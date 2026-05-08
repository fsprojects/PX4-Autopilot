# GainCompression::update — Informal Specification

🔬 *Lean Squad automated formal verification.*

- **C++ source**: `src/lib/rate_control/gain_compression.cpp`
- **C++ header**: `src/lib/rate_control/gain_compression.hpp`

## Purpose

`GainCompression` is an adaptive gain-compression filter that detects oscillations in a
control loop and reduces the loop gain when oscillations are detected.  The algorithm is
based on spectral damping (Orr & Van Zwieten 2012, AIAA GNC).

`GainCompression::update(input, dt)` performs one step of the adaptive gain filter and
returns the current compression gain, a multiplicative factor in the range
`[compression_gain_min, 1]` to be applied to the controller output.

## Preconditions

- `input`: any float (rate or acceleration measurement)
- `dt > 0`: timestep in seconds (the implementation constrains dt to [1ms, 100ms])
- `_compression_gain_min ∈ [0, 1]` (default 0.3; must satisfy 0 ≤ min ≤ 1)
- `_compression_gain ∈ [_compression_gain_min, 1]` (invariant maintained across calls)

## Postconditions

- Return value ∈ `[_compression_gain_min, 1]`
  *(guaranteed by the final `math::constrain` call)*
- `_compression_gain` is updated to the return value

## Invariants

- **Range invariant**: `_compression_gain ∈ [_compression_gain_min, 1]` is maintained
  across all calls, regardless of the input signal.  This is the key safety property.

## Internal algorithm

1. **HPF step**: `_hpf = α_hpf * _hpf + α_hpf * (input - input_prev)`
   (high-pass filter to detect oscillations; α_hpf is computed from sample_freq and cutoff)
2. **LPF step**: `_lpf.update(_hpf²)` — low-pass filter of the HPF energy
3. **Spectral damping**: `ka = max(gain - gain_min, 0)`;
   `spectral_damping = -kSpectralDamperGain * ka * lpf_state`
   (drives gain down when oscillation energy is high)
4. **Leakage**: `leakage = kLeakageGain * (1 - gain)`
   (pulls gain toward 1 when oscillation energy is low; ensures gain recovers)
5. **Update**: `gain = constrain(gain + (spectral_damping + leakage) * dt, gain_min, 1)`

## Edge cases

- **No oscillations** (`_lpf.getState() ≈ 0`): `spectral_damping ≈ 0`, leakage > 0
  (when gain < 1), so gain slowly recovers toward 1.
- **Strong oscillations**: `spectral_damping << 0`, gain is driven toward `gain_min`.
- **At gain = gain_min**: `ka = 0`, so `spectral_damping = 0`; gain is held at
  minimum until oscillations subside.
- **At gain = 1**: `leakage = 0`, gain stays at 1 if no oscillations.

## Key formal properties proved

| Property | Description |
|----------|-------------|
| `gainCompressionUpdate_in_range` | output ∈ [gain_min, 1] for ANY ka_dot and dt |
| `gainCompressionIterate_in_range` | after N steps, gain stays in [gain_min, 1] |
| `gainCompression_leakage_positive` | leakage > 0 when gain < 1 and kLeakage > 0 |

## Open questions

- Is the default `_compression_gain_min = 0.3` appropriate for all vehicle types?
- What happens near the boundary when `_compression_gain = _compression_gain_min`
  and oscillations are still present?  The spectral damping term becomes 0 (ka = 0),
  so gain can no longer decrease.
