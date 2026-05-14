# PurePursuit — Informal Specification

🔬 *Lean Squad automated formal verification.*

**Source**: `src/lib/pure_pursuit/PurePursuit.cpp` — `PurePursuit::calcTargetBearing`
**Reference**: Coulter, R. C. (1992). *Implementation of the Pure Pursuit Path Tracking Algorithm* (CMU-RI-TR-92-01).

---

## Purpose

`calcTargetBearing` implements a **pure pursuit** path-following algorithm for ground vehicles. Given a path segment defined by a previous waypoint and a current waypoint (in NED frame), the current vehicle position, and the vehicle speed, it computes a **target bearing** (heading direction) that the vehicle should steer toward.

The algorithm finds the intersection of a lookahead circle (centred on the vehicle with radius = lookahead distance) with the path segment and steers toward that intersection point.

---

## Inputs

| Parameter | Type | Description |
|-----------|------|-------------|
| `lookahead_gain` | `float` | Proportionality constant: lookahead distance = `gain * |speed|` |
| `lookahead_max` | `float` | Upper bound on lookahead distance (m) |
| `lookahead_min` | `float` | Lower bound on lookahead distance (m) |
| `curr_wp_ned` | `Vector2f` | Current target waypoint in NED frame (m) |
| `prev_wp_ned` | `Vector2f` | Previous waypoint (start of path segment) in NED frame (m) |
| `curr_pos_ned` | `Vector2f` | Current vehicle position in NED frame (m) |
| `vehicle_speed` | `float` | Vehicle ground speed (m/s) |

---

## Output

A **target bearing** in radians, in the range `(−π, π]`, representing the compass direction the vehicle should steer toward.

---

## Preconditions

1. All inputs (`curr_wp_ned`, `prev_wp_ned`, `curr_pos_ned`, `vehicle_speed`) must be finite (not NaN, not ±∞).
2. `lookahead_min ≤ lookahead_max` (not explicitly checked but implied by `math::constrain`).
3. `lookahead_gain ≥ 0` (negative gain produces inverted lookahead; not guarded).

---

## Postconditions

1. **If any input is non-finite**: return `NAN`.
2. **Lookahead distance is constrained**: `lookahead_distance = constrain(gain * |speed|, lookahead_min, lookahead_max)`, so `lookahead_min ≤ lookahead_distance ≤ lookahead_max`.
3. **Target bearing is in `(−π, π]`**: whenever a finite bearing is returned, it is wrapped via `matrix::wrap_pi`.
4. **Waypoints overlap case**: if `|curr_wp − prev_wp| < FLT_EPSILON`, return bearing directly toward `curr_wp`.
5. **Near-waypoint case**: if the vehicle is closer to `curr_wp` than the lookahead distance, return bearing directly toward `curr_wp`.
6. **Off-path case**: if the vehicle's perpendicular cross-track distance from the segment exceeds the lookahead, steer toward the closest on-path point (or the prev/current waypoint if the segment is too short).
7. **Regular case**: steer toward the intersection of the lookahead circle with the path segment.

---

## Invariants

### Lookahead range invariant (safety-critical)
```
lookahead_min ≤ lookahead_distance ≤ lookahead_max
```
This holds unconditionally (from `math::constrain`), regardless of speed. It ensures the vehicle always looks ahead by at least `lookahead_min` metres.

### Bearing range invariant
```
target_bearing ∈ (−π, π]
```
All computed bearings pass through `matrix::wrap_pi`.

---

## Algorithm Summary

### Step 1: Lookahead computation
```
lookahead_distance = constrain(lookahead_gain * |vehicle_speed|, lookahead_min, lookahead_max)
```

### Step 2: Geometry setup
- `d_to_wp = curr_wp − curr_pos` (vector from vehicle to current waypoint)
- `seg = curr_wp − prev_wp` (path segment vector)
- `proj = (prev_wp_to_pos · seg_unit) * seg_unit` (foot of perpendicular on path)
- `d_to_path = proj − (curr_pos − prev_wp)` (shortest vector from vehicle to path line)
- `crosstrack_error = sign(...) * |d_to_path|` (signed lateral deviation)
- `bearing_to_wp = wrap_pi(atan2(d_to_wp.y, d_to_wp.x))`

### Step 3: Target selection (four branches)
| Condition | Target |
|-----------|--------|
| `|d_to_wp| < lookahead` OR waypoints overlap | Current waypoint directly |
| `|crosstrack| > lookahead` AND closest point is "behind" prev_wp | Previous waypoint direction |
| `|crosstrack| > lookahead` AND closest point is "ahead" of curr_wp | Current waypoint directly |
| `|crosstrack| > lookahead` AND closest point is on segment | Closest point on path |
| Normal case: circle intersects path | Intersection point |

### Step 4: Intersection geometry (normal case)
```
line_ext = sqrt(lookahead² - crosstrack²)
intersection = proj_foot + line_ext * seg_unit
target = intersection + prev_wp - curr_pos
bearing = wrap_pi(atan2(target.y, target.x))
```

---

## Edge Cases

| Scenario | Expected behaviour |
|----------|-------------------|
| `vehicle_speed = 0` | `lookahead_distance = lookahead_min` (constrained) |
| Very high speed | `lookahead_distance = lookahead_max` |
| `curr_wp == prev_wp` | Steer directly toward `curr_wp` |
| Vehicle at `curr_wp` | Bearing toward `curr_wp` (distance 0 < lookahead) |
| Vehicle on path, no crosstrack error | Clean intersection geometry |
| Vehicle far off path (`|crosstrack| > lookahead`) | Steer toward closest on-path point |
| Any non-finite input | Return `NAN` |
| `lookahead_gain < 0` | Lookahead = `constrain(gain * |speed|, min, max)` — could equal `lookahead_min` |

---

## Examples

### Example 1: Vehicle on straight path heading North
- `prev_wp = (0, 0)`, `curr_wp = (100, 0)` (100 m North)
- `curr_pos = (20, 0)` (vehicle 20 m along path, no crosstrack)
- `speed = 5 m/s`, `gain = 2`, `min = 1`, `max = 30`
- `lookahead = constrain(10, 1, 30) = 10`
- `d_to_wp = 80 m > lookahead`; `crosstrack = 0 < lookahead`
- Intersection at `(30, 0)` → `target_bearing ≈ 0` (due North)

### Example 2: Vehicle close to waypoint
- `|d_to_wp| = 5 m < lookahead = 10 m`
- → `target_bearing = bearing_to_curr_wp`

### Example 3: Stationary vehicle
- `speed = 0` → `lookahead = lookahead_min`
- Algorithm continues normally using minimum lookahead

---

## Inferred Intent

The primary design properties of this function are:

1. **Safety**: the lookahead distance must always be in `[lookahead_min, lookahead_max]`. This prevents degenerate navigation (zero lookahead would cause oscillation; unbounded lookahead would cut corners aggressively).

2. **Completeness**: a finite bearing is always returned when inputs are finite. The four-branch structure ensures all geometric configurations are covered with no undefined gaps.

3. **Robustness**: degenerate inputs (overlapping waypoints, vehicle at waypoint, very large crosstrack) all have well-defined fallback behaviours.

4. **Signed crosstrack convention**: positive crosstrack = vehicle is to the left of the path (heading from prev to curr wp); negative = to the right.

---

## Open Questions

1. **`lookahead_gain < 0`**: no guard is present. Should negative gain be prohibited or clamped?
2. **`lookahead_min > lookahead_max`**: `math::constrain` with inverted bounds returns `lookahead_min` on all inputs. Is this intentional or a latent bug?
3. **`prev_wp_to_curr_wp_u.unit_or_zero()`**: when waypoints overlap, `unit_or_zero()` returns `(0,0)`. The overlap case is handled separately, but the projection logic would still execute first — is this guaranteed safe?
4. **NED vs ENU frame**: the header comments say NED. Are callers consistent? A frame mismatch would flip North/South and East/West.
5. **`sign(0)`**: when `crosstrack_error = 0`, `sign(0) = 0`, making `crosstrack_error = 0`. Is the signed convention for exactly on-path consistent with expectations in all callsites?

---

## Properties for Formal Verification

The highest-value FV targets for this function:

1. **`lookahead_in_range`** (safety-critical, easy):
   ```lean
   theorem lookahead_in_range (gain speed min max : Float) (h : min ≤ max) :
       min ≤ constrain (gain * |speed|) min max ∧ constrain (gain * |speed|) min max ≤ max
   ```
   This is a direct consequence of `math::constrain` — provable by `omega`/`linarith`.

2. **Bearing range**: `target_bearing ∈ (−π, π]` — requires `wrap_pi` spec.

3. **Finite output**: if all inputs are finite, output is finite — structural case analysis.

4. **Waypoint-overlap determinism**: if `curr_wp == prev_wp`, output is `bearing_to_curr_wp`.
