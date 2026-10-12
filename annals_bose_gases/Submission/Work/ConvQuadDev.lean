import Mathlib.Tactic.Have
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.ChiSmall
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Stage A1 (core) — differentiability of `zeta1d^M` through its face cuts

STATUS: axiom-free, no `sorry`, rc=0 (this session).  `ζ(y) = cos(πy)·1_{|y| ≤ 1/2}`;
`ζ^M` is C^{M−1} on ℝ (an order-`M` zero at the faces y = ±1/2), hence
differentiable at the faces with derivative `0` for `2 ≤ M`.  Proved at
BOTH faces with a global squeeze: at a face point `c` (`c = ±1/2`) the
face-decay bound `|ζ(y)| ≤ π·|y − c|` holds for ALL `y` (interior via
`cos(πy) = −sin(πc)·sin(π(y−c))` — `cos(πy) = −sin(π(y−1/2))` resp.
`= sin(π(y+1/2))`; exterior via `ζ = 0`), and its `M`-th power bounds the
difference quotient by `π^M·|y−c|^{M−1} → 0` (squeeze_zero).

Contents: `cos_pi_mul_eq_neg_sin_pi_sub_half`, `cos_pi_mul_eq_sin_pi_add_half`
(angle-addition identities at ±π/2), `zeta1d_abs_le_pi_sub_half`,
`zeta1d_abs_le_pi_add_half` (the global face-decay bounds),
`zeta1d_pow_slope_bound_face` (difference-quotient bound), the generic
**`zeta1d_pow_hasDerivAt_face`** (given the face bound), and the two face
instantiations **`zeta1d_pow_hasDerivAt_half`** / **`zeta1d_pow_hasDerivAt_neg_half`**
(`HasDerivAt (fun y => zeta1d y ^ M) 0 (±1/2)`, `2 ≤ M`).

Session-264-part-2/3 additions — **pointwise `HasDerivAt` for `zeta1d^M`
CLOSED at every point**: interior `zeta1d_pow_hasDerivAt_of_abs_lt`
(|y| < 1/2, derivative `↑M·cos(πy)^{M−1}·(−sin(πy)·π)`, from the value-level
`hasDerivAt_id_pow_nat` (= Mathlib `hasDerivAt_pow`), `cos_affine_hasDerivAt`
and `cosPow_hasDerivAt` (`fun_pow`)), faces `zeta1d_pow_hasDerivAt_half/_neg_half`
(derivative 0), exterior identically 0.

Session-264-part-4..11 — **STAGE A1 COMPLETE: `zeta1d^M` is `C²` on ℝ
for `3 ≤ M`** (`zeta1d_pow_contDiff_two`).  Full chain (60 decls):
`zeta1d_pow_contDiff_one` (`2 ≤ M`); second-derivative formula
`zeta1dDeriv2F` + face limits `zeta1dDeriv2F_tendsto_half/_neg_half`
(`3 ≤ M`); `zeta1dDerivF_hasDerivAt`; the deriv²-vanishing layer
(`zeta1d_pow_second_deriv_eq_zero_of_one_half_le`,
`zeta1dDerivPiecewise_hasDerivAt_zero_face/_of_one_half_le`);
the piecewise deriv² (`zeta1d_pow_second_deriv`); the piecewise-second def
`zeta1dDeriv2Piecewise`, its face/all-points continuity (`|g₂| ≤ |F₂|`
squeeze + the F₂ face limits; interior/exterior eventual equality), giving
`zeta1d_pow_second_deriv_continuous`; `zeta1dDerivPiecewise_deriv` /
`_differentiable` / `_contDiff_one` (so `ContDiff 1 (deriv ζ^M)`); and
**`zeta1d_pow_contDiff_two`** via `contDiff_succ_iff_deriv`
(`(2 : ℕ∞ω) = (1 : ℕ∞ω) + 1`, Differentiable ζ^M ∧ ContDiff 1 (deriv ζ^M)).

Next: A2 — `chiSmall` (`C_M·Π_j ζ(z_j)^M`, 3D product of `zeta1d`-powers +
scalar normalisation) is `C²_c` via the 1D `zeta1d_pow_contDiff_two`,
`ContDiff.mul`/`.comp` and the constant normaliser; then A3 (convolution
smoothness via `HasCompactSupport.contDiff_convolution_left`), A4 (Taylor
remainder `map_add_eq_sum_add_integral_iteratedFDeriv`), A5 (global
boundedness), A6 (refactor `hdev` off the four Session-263 mass-gap
lemmas).
-/

noncomputable section
open MeasureTheory Metric Filter
open scoped Real Topology ContDiff
namespace Submission
set_option autoImplicit false
set_option linter.unusedVariables false
namespace BoseGases

/-- `cos(πy) = −sin(π(y − 1/2))` (angle addition at `π/2`). -/
lemma cos_pi_mul_eq_neg_sin_pi_sub_half (y : ℝ) :
    Real.cos (Real.pi * y) = -Real.sin (Real.pi * (y - (1 / 2 : ℝ))) := by
  have harg : Real.pi * y = Real.pi / 2 + Real.pi * (y - (1 / 2 : ℝ)) := by ring
  rw [harg, Real.cos_add, Real.cos_pi_div_two, Real.sin_pi_div_two]
  ring

/-- `cos(πy) = sin(π(y + 1/2))` (angle addition at `−π/2`). -/
lemma cos_pi_mul_eq_sin_pi_add_half (y : ℝ) :
    Real.cos (Real.pi * y) = Real.sin (Real.pi * (y + (1 / 2 : ℝ))) := by
  have harg : Real.pi * y = -(Real.pi / 2) + Real.pi * (y + (1 / 2 : ℝ)) := by ring
  rw [harg, Real.cos_add, Real.cos_neg, Real.cos_pi_div_two, Real.sin_neg, Real.sin_pi_div_two]
  ring

/-- **face-decay bound at `1/2`**: `|ζ(y)| ≤ π·|y − 1/2|` for all `y`. -/
lemma zeta1d_abs_le_pi_sub_half (y : ℝ) :
    |zeta1d y| ≤ Real.pi * |y - (1 / 2 : ℝ)| := by
  by_cases hy : |y| ≤ 1 / 2
  · rw [zeta1d_of_abs_le hy]
    calc
      |Real.cos (Real.pi * y)| = |Real.sin (Real.pi * (y - (1 / 2 : ℝ)))| := by
            rw [cos_pi_mul_eq_neg_sin_pi_sub_half y, abs_neg]
      _ ≤ |Real.pi * (y - (1 / 2 : ℝ))| := by
            exact Real.abs_sin_le_abs
      _ = Real.pi * |y - (1 / 2 : ℝ)| := by
            rw [abs_mul, abs_of_nonneg (le_of_lt Real.pi_pos)]
  · have hz : zeta1d y = 0 := zeta1d_of_one_half_lt (lt_of_not_ge hy)
    rw [hz]
    simpa using (mul_nonneg (le_of_lt Real.pi_pos) (abs_nonneg (y - (1 / 2 : ℝ))))

/-- **face-decay bound at `−1/2`**: `|ζ(y)| ≤ π·|y + 1/2|` for all `y`. -/
lemma zeta1d_abs_le_pi_add_half (y : ℝ) :
    |zeta1d y| ≤ Real.pi * |y + (1 / 2 : ℝ)| := by
  by_cases hy : |y| ≤ 1 / 2
  · rw [zeta1d_of_abs_le hy]
    calc
      |Real.cos (Real.pi * y)| = |Real.sin (Real.pi * (y + (1 / 2 : ℝ)))| := by
            rw [cos_pi_mul_eq_sin_pi_add_half y]
      _ ≤ |Real.pi * (y + (1 / 2 : ℝ))| := by
            exact Real.abs_sin_le_abs
      _ = Real.pi * |y + (1 / 2 : ℝ)| := by
            rw [abs_mul, abs_of_nonneg (le_of_lt Real.pi_pos)]
  · have hz : zeta1d y = 0 := zeta1d_of_one_half_lt (lt_of_not_ge hy)
    rw [hz]
    simpa using (mul_nonneg (le_of_lt Real.pi_pos) (abs_nonneg (y + (1 / 2 : ℝ))))

/-- at a face point `c` (where `ζ c = 0`), the difference quotient of
`zeta1d^M` is bounded by `π^M·|y−c|^{M−1}` (all `y`), given the face-decay
bound `hface`. -/
lemma zeta1d_pow_slope_bound_face {M : ℕ} (hM : 2 ≤ M) {c : ℝ}
    (hface : ∀ y : ℝ, |zeta1d y| ≤ Real.pi * |y - c|) (y : ℝ) :
    |(zeta1d y ^ M - zeta1d c ^ M) / (y - c)| ≤ Real.pi ^ M * |y - c| ^ (M - 1) := by
  have hzeta0 : zeta1d c = 0 := by
    have hb : |zeta1d c| ≤ Real.pi * |c - c| := hface c
    have hb' : |zeta1d c| ≤ 0 := by simpa using hb
    exact abs_eq_zero.mp (le_antisymm hb' (abs_nonneg _))
  have hhalf : zeta1d c ^ M = 0 := by
    rw [hzeta0]
    exact zero_pow (ne_of_gt (by omega : 0 < M))
  by_cases hyc : y = c
  · subst y
    have hM1 : 0 < M - 1 := by omega
    simp [zero_pow (ne_of_gt hM1)]
  · have he0 : |y - c| ≠ 0 := by
      exact abs_ne_zero.mpr (sub_ne_zero.mpr hyc)
    have hz' : |zeta1d y| ≤ Real.pi * |y - c| := hface y
    have hpowle : |zeta1d y| ^ M ≤ (Real.pi * |y - c|) ^ M :=
      pow_le_pow_left₀ (abs_nonneg _) hz' M
    have hMrec : M = (M - 1) + 1 := by omega
    have hfac : |y - c| ^ M = |y - c| ^ (M - 1) * |y - c| := by
      conv_lhs => rw [hMrec]
      rw [pow_succ]
    calc
      |(zeta1d y ^ M - zeta1d c ^ M) / (y - c)| = |zeta1d y ^ M| / |y - c| := by
              rw [hhalf]
              simp [abs_div]
      _ = |zeta1d y| ^ M / |y - c| := by rw [abs_pow]
      _ ≤ (Real.pi * |y - c|) ^ M / |y - c| := by
              exact div_le_div_of_nonneg_right hpowle (abs_nonneg _)
      _ = Real.pi ^ M * |y - c| ^ M / |y - c| := by rw [mul_pow]
      _ = Real.pi ^ M * (|y - c| ^ M / |y - c|) := by ring
      _ = Real.pi ^ M * |y - c| ^ (M - 1) := by
              rw [hfac]
              rw [div_eq_mul_inv, mul_assoc]
              rw [mul_inv_cancel₀ he0]
              simp

/-- **`zeta1d^M` is differentiable at a face point `c` with `ζ c = 0`
(derivative `0`, `2 ≤ M`)**, given the face-decay bound `hface`: the
difference quotient is squeezed by `π^M·|y−c|^{M−1} → 0`. -/
lemma zeta1d_pow_hasDerivAt_face {M : ℕ} (hM : 2 ≤ M) {c : ℝ}
    (hface : ∀ y : ℝ, |zeta1d y| ≤ Real.pi * |y - c|) :
    HasDerivAt (fun y : ℝ => zeta1d y ^ M) 0 c := by
  rw [hasDerivAt_iff_tendsto_slope]
  let f : ℝ → ℝ := fun y => zeta1d y ^ M
  have hM1 : 0 < M - 1 := by omega
  have hzfull : Tendsto (fun y : ℝ => |y - c|) (𝓝 c) (𝓝 (0 : ℝ)) := by
    have hcid : Tendsto (fun y : ℝ => y) (𝓝 c) (𝓝 c) := tendsto_id
    have hcst : Tendsto (fun _ : ℝ => c) (𝓝 c) (𝓝 c) := tendsto_const_nhds
    have hc : Tendsto (fun y : ℝ => y - c) (𝓝 c) (𝓝 (0 : ℝ)) := by
      simpa using hcid.sub hcst
    have habs0 : ContinuousAt (fun z : ℝ => |z|) (0 : ℝ) :=
      Continuous.continuousAt continuous_abs (x := (0 : ℝ))
    have htmp : Tendsto (fun y : ℝ => |y - c|) (𝓝 c) (𝓝 (|(0 : ℝ)|)) := by
      refine (habs0.tendsto.comp hc).congr' ?_
      filter_upwards with y
      rfl
    simpa using htmp
  have hznear : Tendsto (fun y : ℝ => |y - c|) (𝓝[≠] c) (𝓝 (0 : ℝ)) := by
    exact hzfull.mono_left (nhdsWithin_le_nhds (a := c) (s := {y : ℝ | y ≠ c}))
  have hg0 : Tendsto (fun y : ℝ => Real.pi ^ M * |y - c| ^ (M - 1)) (𝓝[≠] c) (𝓝 (0 : ℝ)) := by
    have hzpow : Tendsto (fun y : ℝ => |y - c| ^ (M - 1)) (𝓝[≠] c) (𝓝 (0 : ℝ)) := by
      simpa [zero_pow (ne_of_gt hM1)] using (hznear.pow (M - 1))
    simpa [mul_zero] using (tendsto_const_nhds.mul hzpow)
  have hsq : Tendsto (fun y : ℝ => |slope f c y|) (𝓝[≠] c) (𝓝 (0 : ℝ)) := by
    refine squeeze_zero (fun y => abs_nonneg _) (fun y => ?_) hg0
    have hb := zeta1d_pow_slope_bound_face hM hface y
    have hsl : slope f c y = (zeta1d y ^ M - zeta1d c ^ M) / (y - c) := by
      dsimp [slope, f]
      ring
    rw [hsl]
    exact hb
  rw [tendsto_iff_norm_sub_tendsto_zero]
  simpa [f, sub_zero, Real.norm_eq_abs] using hsq

/-- **`zeta1d^M` is differentiable at the right face `1/2` (derivative `0`,
`2 ≤ M`).** -/
lemma zeta1d_pow_hasDerivAt_half {M : ℕ} (hM : 2 ≤ M) :
    HasDerivAt (fun y : ℝ => zeta1d y ^ M) 0 (1 / 2 : ℝ) := by
  exact zeta1d_pow_hasDerivAt_face hM zeta1d_abs_le_pi_sub_half

/-- **`zeta1d^M` is differentiable at the left face `−1/2` (derivative `0`,
`2 ≤ M`).** -/
lemma zeta1d_pow_hasDerivAt_neg_half {M : ℕ} (hM : 2 ≤ M) :
    HasDerivAt (fun y : ℝ => zeta1d y ^ M) 0 (-(1 / 2 : ℝ)) := by
  refine zeta1d_pow_hasDerivAt_face hM ?_
  intro y
  simpa [sub_eq_add_neg] using zeta1d_abs_le_pi_add_half y

/-- **value-level derivative of the monomial** `z ↦ z^M` at `z0` with
value `↑M·z0^(M−1)` — Mathlib's `hasDerivAt_pow` (value-level, no
function-power statements). -/
lemma hasDerivAt_id_pow_nat (z0 : ℝ) (M : ℕ) :
    HasDerivAt (fun z : ℝ => z ^ M) (↑M * z0 ^ (M - 1)) z0 := by
  exact hasDerivAt_pow M z0

/-- **value-level affine cosine chain**: `HasDerivAt (fun w => cos(πw))`
at `y` with value `−sin(πy)·π`, built by `Real.hasDerivAt_cos` + the
`convert`-bridge over the ℝ-instance gap (the comp carries the
division-ring module instance; `convert` closes the instance goals by
`rfl`). -/
lemma cos_affine_hasDerivAt (y : ℝ) :
    HasDerivAt (fun w : ℝ => Real.cos (Real.pi * w)) (-Real.sin (Real.pi * y) * Real.pi) y := by
  have hlin : HasDerivAt (fun w : ℝ => Real.pi * w) Real.pi y := by
    convert (hasDerivAt_id y).const_mul Real.pi using 1 <;> first | rfl | exact (mul_one Real.pi).symm
  convert (Real.hasDerivAt_cos (Real.pi * y)).comp y hlin using 1 <;> rfl

/-- **interior `cos(π·)^M` derivative** (value level, `fun_pow` on the
affine cosine chain): `HasDerivAt (fun w => cos(πw)^M) (↑M·cos(πy)^{M−1}·
(−sin(πy)·π)) y`. -/
lemma cosPow_hasDerivAt (M : ℕ) (y : ℝ) :
    HasDerivAt (fun w : ℝ => Real.cos (Real.pi * w) ^ M)
      (↑M * (Real.cos (Real.pi * y)) ^ (M - 1) * (-Real.sin (Real.pi * y) * Real.pi)) y := by
  simpa [mul_assoc] using ((cos_affine_hasDerivAt y).fun_pow M)

/-- **interior points `|y| < 1/2`: `zeta1d^M` is differentiable at `y`**
with the cosine-power derivative — `ζ^M = cos(π·)^M` on a neighbourhood of
`y` (from `zeta1d_of_abs_le`). -/
lemma zeta1d_pow_hasDerivAt_of_abs_lt {M : ℕ} (y : ℝ) (hy : |y| < 1 / 2) :
    HasDerivAt (fun w : ℝ => zeta1d w ^ M)
      (↑M * (Real.cos (Real.pi * y)) ^ (M - 1) * (-Real.sin (Real.pi * y) * Real.pi)) y := by
  have hg := cosPow_hasDerivAt M y
  refine hg.congr_of_eventuallyEq ?_
  have hset : ({w : ℝ | |w| < 1 / 2}) ∈ 𝓝 y := by
    have hset' : {w : ℝ | |w| < 1 / 2} = Metric.ball (0 : ℝ) (1 / 2) := by
      ext w
      simp [Real.norm_eq_abs, dist_eq_norm]
    rw [hset']
    exact Metric.isOpen_ball.mem_nhds (by simpa [Real.norm_eq_abs, dist_eq_norm] using hy)
  filter_upwards [hset] with w hw
  rw [zeta1d_of_abs_le (le_of_lt hw)]



/-- **cosine face-decay bound at `1/2`**: `|cos(πy)| ≤ π·|y − 1/2|` for
all `y` (from `cos(πy) = −sin(π(y−1/2))`). -/
lemma cos_abs_le_pi_sub_half (y : ℝ) :
    |Real.cos (Real.pi * y)| ≤ Real.pi * |y - (1 / 2 : ℝ)| := by
  calc
    |Real.cos (Real.pi * y)| = |Real.sin (Real.pi * (y - (1 / 2 : ℝ)))| := by
          rw [cos_pi_mul_eq_neg_sin_pi_sub_half y, abs_neg]
    _ ≤ |Real.pi * (y - (1 / 2 : ℝ))| := Real.abs_sin_le_abs
    _ = Real.pi * |y - (1 / 2 : ℝ)| := by
          rw [abs_mul, abs_of_nonneg (le_of_lt Real.pi_pos)]

/-- **cosine face-decay bound at `−1/2`**: `|cos(πy)| ≤ π·|y + 1/2|` for
all `y` (from `cos(πy) = sin(π(y+1/2))`). -/
lemma cos_abs_le_pi_add_half (y : ℝ) :
    |Real.cos (Real.pi * y)| ≤ Real.pi * |y + (1 / 2 : ℝ)| := by
  calc
    |Real.cos (Real.pi * y)| = |Real.sin (Real.pi * (y + (1 / 2 : ℝ)))| := by
          rw [cos_pi_mul_eq_sin_pi_add_half y]
    _ ≤ |Real.pi * (y + (1 / 2 : ℝ))| := Real.abs_sin_le_abs
    _ = Real.pi * |y + (1 / 2 : ℝ)| := by
          rw [abs_mul, abs_of_nonneg (le_of_lt Real.pi_pos)]

/-- pointwise bound of the interior-derivative value at `1/2`:
`|d(y)| ≤ (↑M·(π·|y−1/2|)^{M−1})·π` (`M ≥ 2`). -/
lemma cosPow_deriv_abs_bound_half {M : ℕ} (hM : 2 ≤ M) (y : ℝ) :
    |↑M * (Real.cos (Real.pi * y)) ^ (M - 1) * (-Real.sin (Real.pi * y) * Real.pi)|
      ≤ (↑M * (Real.pi * |y - (1 / 2 : ℝ)|) ^ (M - 1)) * Real.pi := by
  have hc := cos_abs_le_pi_sub_half y
  have hc' : |Real.cos (Real.pi * y)| ^ (M - 1) ≤ (Real.pi * |y - (1 / 2 : ℝ)|) ^ (M - 1) :=
    pow_le_pow_left₀ (abs_nonneg _) hc (M - 1)
  have hsin : |(-Real.sin (Real.pi * y)) * Real.pi| ≤ Real.pi := by
    rw [abs_mul, abs_of_nonneg (le_of_lt Real.pi_pos), abs_neg]
    have h1 : |Real.sin (Real.pi * y)| * Real.pi ≤ (1 : ℝ) * Real.pi :=
      mul_le_mul_of_nonneg_right (Real.abs_sin_le_one (Real.pi * y)) (le_of_lt Real.pi_pos)
    simpa using h1
  have hM0 : 0 ≤ (↑M : ℝ) := by exact_mod_cast (Nat.zero_le M)
  have hstep : |Real.cos (Real.pi * y)| ^ (M - 1) * |(-Real.sin (Real.pi * y)) * Real.pi|
      ≤ (Real.pi * |y - (1 / 2 : ℝ)|) ^ (M - 1) * Real.pi :=
    mul_le_mul hc' hsin (abs_nonneg _) (by positivity : 0 ≤ (Real.pi * |y - (1 / 2 : ℝ)|) ^ (M - 1))
  calc
    |↑M * (Real.cos (Real.pi * y)) ^ (M - 1) * (-Real.sin (Real.pi * y) * Real.pi)|
        = ↑M * (|Real.cos (Real.pi * y)| ^ (M - 1) * |(-Real.sin (Real.pi * y)) * Real.pi|) := by
            rw [abs_mul, abs_mul]
            rw [abs_of_nonneg hM0, abs_pow]
            ring
    _ ≤ ↑M * ((Real.pi * |y - (1 / 2 : ℝ)|) ^ (M - 1) * Real.pi) := by
            exact mul_le_mul_of_nonneg_left hstep hM0
    _ = (↑M * (Real.pi * |y - (1 / 2 : ℝ)|) ^ (M - 1)) * Real.pi := by ring

/-- **face limit of the interior derivative at `1/2`** (`2 ≤ M`): the value
`↑M·cos(πy)^{M−1}·(−sin(πy)·π)` tends to `0` as `y → 1/2` (the vanishing
cosine power kills the bounded sine factor) — keystone for the continuity
of `deriv (ζ^M)` through the right cut. -/
lemma cosPow_deriv_tendsto_half {M : ℕ} (hM : 2 ≤ M) :
    Tendsto (fun y : ℝ => ↑M * (Real.cos (Real.pi * y)) ^ (M - 1)
        * (-Real.sin (Real.pi * y) * Real.pi)) (𝓝 (1 / 2 : ℝ)) (𝓝 (0 : ℝ)) := by
  have hM1 : 0 < M - 1 := by omega
  have hnear : Tendsto (fun y : ℝ => |y - (1 / 2 : ℝ)|) (𝓝 (1 / 2 : ℝ)) (𝓝 (0 : ℝ)) := by
    have hc : ContinuousAt (fun y : ℝ => |y - (1 / 2 : ℝ)|) (1 / 2 : ℝ) :=
      (continuous_abs.comp (continuous_id.sub continuous_const)).continuousAt
    simpa using hc.tendsto
  have hpow0 : Tendsto (fun y : ℝ => |y - (1 / 2 : ℝ)| ^ (M - 1)) (𝓝 (1 / 2 : ℝ)) (𝓝 (0 : ℝ)) := by
    simpa [zero_pow (ne_of_gt hM1)] using (hnear.pow (M - 1))
  have hg0 : Tendsto (fun y : ℝ => (↑M * (Real.pi * |y - (1 / 2 : ℝ)|) ^ (M - 1)) * Real.pi)
      (𝓝 (1 / 2 : ℝ)) (𝓝 (0 : ℝ)) := by
    have h1 : Tendsto (fun y : ℝ => (Real.pi * |y - (1 / 2 : ℝ)|) ^ (M - 1))
        (𝓝 (1 / 2 : ℝ)) (𝓝 (0 : ℝ)) := by
      simpa [mul_pow, mul_zero] using (tendsto_const_nhds.mul hpow0)
    have h2 : Tendsto (fun y : ℝ => ↑M * (Real.pi * |y - (1 / 2 : ℝ)|) ^ (M - 1))
        (𝓝 (1 / 2 : ℝ)) (𝓝 (0 : ℝ)) := by
      simpa [mul_zero] using (tendsto_const_nhds.mul h1)
    simpa [mul_zero] using (h2.mul tendsto_const_nhds)
  have habs : Tendsto (fun y : ℝ =>
      |↑M * (Real.cos (Real.pi * y)) ^ (M - 1) * (-Real.sin (Real.pi * y) * Real.pi)|)
      (𝓝 (1 / 2 : ℝ)) (𝓝 (0 : ℝ)) := by
    refine squeeze_zero (fun y => abs_nonneg _) (fun y => ?_) hg0
    exact cosPow_deriv_abs_bound_half hM y
  rw [tendsto_iff_norm_sub_tendsto_zero]
  simpa [sub_zero, Real.norm_eq_abs] using habs

/-- **face limit of the interior derivative at `−1/2`** (`2 ≤ M`): mirror
of `cosPow_deriv_tendsto_half` (cosine power vanishes there too). -/
lemma cosPow_deriv_tendsto_neg_half {M : ℕ} (hM : 2 ≤ M) :
    Tendsto (fun y : ℝ => ↑M * (Real.cos (Real.pi * y)) ^ (M - 1)
        * (-Real.sin (Real.pi * y) * Real.pi)) (𝓝 (-(1 / 2 : ℝ))) (𝓝 (0 : ℝ)) := by
  have hM1 : 0 < M - 1 := by omega
  have hnear : Tendsto (fun y : ℝ => |y - (-(1 / 2 : ℝ))|) (𝓝 (-(1 / 2 : ℝ))) (𝓝 (0 : ℝ)) := by
    have hc : ContinuousAt (fun y : ℝ => |y - (-(1 / 2 : ℝ))|) (-(1 / 2 : ℝ)) :=
      (continuous_abs.comp (continuous_id.sub continuous_const)).continuousAt
    simpa using hc.tendsto
  have hpow0 : Tendsto (fun y : ℝ => |y - (-(1 / 2 : ℝ))| ^ (M - 1)) (𝓝 (-(1 / 2 : ℝ))) (𝓝 (0 : ℝ)) := by
    simpa [zero_pow (ne_of_gt hM1)] using (hnear.pow (M - 1))
  have hg0 : Tendsto (fun y : ℝ => (↑M * (Real.pi * |y - (-(1 / 2 : ℝ))|) ^ (M - 1)) * Real.pi)
      (𝓝 (-(1 / 2 : ℝ))) (𝓝 (0 : ℝ)) := by
    have h1 : Tendsto (fun y : ℝ => (Real.pi * |y - (-(1 / 2 : ℝ))|) ^ (M - 1))
        (𝓝 (-(1 / 2 : ℝ))) (𝓝 (0 : ℝ)) := by
      simpa [mul_pow, mul_zero] using (tendsto_const_nhds.mul hpow0)
    have h2 : Tendsto (fun y : ℝ => ↑M * (Real.pi * |y - (-(1 / 2 : ℝ))|) ^ (M - 1))
        (𝓝 (-(1 / 2 : ℝ))) (𝓝 (0 : ℝ)) := by
      simpa [mul_zero] using (tendsto_const_nhds.mul h1)
    simpa [mul_zero] using (h2.mul tendsto_const_nhds)
  have hb : ∀ y : ℝ,
      |↑M * (Real.cos (Real.pi * y)) ^ (M - 1) * (-Real.sin (Real.pi * y) * Real.pi)|
        ≤ (↑M * (Real.pi * |y - (-(1 / 2 : ℝ))|) ^ (M - 1)) * Real.pi := by
    intro y
    -- |y - (−1/2)| = |y + 1/2|: re-use the half bound with the + form then convert
    have hb' := cosPow_deriv_abs_bound_half hM y
    -- |y - 1/2| in the RHS of hb' vs |y + 1/2|: NOT equal... redo for neg-half:
    have hc := cos_abs_le_pi_add_half y
    have hc' : |Real.cos (Real.pi * y)| ^ (M - 1) ≤ (Real.pi * |y + (1 / 2 : ℝ)|) ^ (M - 1) :=
      pow_le_pow_left₀ (abs_nonneg _) hc (M - 1)
    have hsin : |(-Real.sin (Real.pi * y)) * Real.pi| ≤ Real.pi := by
      rw [abs_mul, abs_of_nonneg (le_of_lt Real.pi_pos), abs_neg]
      have h1 : |Real.sin (Real.pi * y)| * Real.pi ≤ (1 : ℝ) * Real.pi :=
        mul_le_mul_of_nonneg_right (Real.abs_sin_le_one (Real.pi * y)) (le_of_lt Real.pi_pos)
      simpa using h1
    have hM0 : 0 ≤ (↑M : ℝ) := by exact_mod_cast (Nat.zero_le M)
    have hstep : |Real.cos (Real.pi * y)| ^ (M - 1) * |(-Real.sin (Real.pi * y)) * Real.pi|
        ≤ (Real.pi * |y + (1 / 2 : ℝ)|) ^ (M - 1) * Real.pi :=
      mul_le_mul hc' hsin (abs_nonneg _) (by positivity : 0 ≤ (Real.pi * |y + (1 / 2 : ℝ)|) ^ (M - 1))
    calc
      |↑M * (Real.cos (Real.pi * y)) ^ (M - 1) * (-Real.sin (Real.pi * y) * Real.pi)|
          = ↑M * (|Real.cos (Real.pi * y)| ^ (M - 1) * |(-Real.sin (Real.pi * y)) * Real.pi|) := by
              rw [abs_mul, abs_mul]
              rw [abs_of_nonneg hM0, abs_pow]
              ring
      _ ≤ ↑M * ((Real.pi * |y + (1 / 2 : ℝ)|) ^ (M - 1) * Real.pi) := by
              exact mul_le_mul_of_nonneg_left hstep hM0
      _ ≤ (↑M * (Real.pi * |y - (-(1 / 2 : ℝ))|) ^ (M - 1)) * Real.pi := by
              have harg : |y + (1 / 2 : ℝ)| = |y - (-(1 / 2 : ℝ))| := by
                congr 1
                ring
              rw [harg]
              ring_nf
              exact le_rfl
  have habs : Tendsto (fun y : ℝ =>
      |↑M * (Real.cos (Real.pi * y)) ^ (M - 1) * (-Real.sin (Real.pi * y) * Real.pi)|)
      (𝓝 (-(1 / 2 : ℝ))) (𝓝 (0 : ℝ)) := by
    refine squeeze_zero (fun y => abs_nonneg _) hb hg0
  rw [tendsto_iff_norm_sub_tendsto_zero]
  simpa [sub_zero, Real.norm_eq_abs] using habs



/-- **exterior points `1/2 < |y|`**: `zeta1d^M` is identically `0` on a
neighbourhood of `y`, so it has derivative `0` there. -/
lemma zeta1d_pow_hasDerivAt_zero_of_one_half_lt {M : ℕ} (hM : 1 ≤ M) {y : ℝ}
    (hy : 1 / 2 < |y|) :
    HasDerivAt (fun w : ℝ => zeta1d w ^ M) 0 y := by
  have hzero : ∀ᶠ w : ℝ in 𝓝 y, zeta1d w = 0 := by
    have hset : ({w : ℝ | 1 / 2 < |w|}) ∈ 𝓝 y := by
      have hset' : {w : ℝ | 1 / 2 < |w|} = (Metric.closedBall (0 : ℝ) (1 / 2))ᶜ := by
        ext w
        simp [Real.norm_eq_abs, dist_eq_norm]
      rw [hset']
      have hclosed : IsClosed (Metric.closedBall (0 : ℝ) (1 / 2)) := isClosed_closedBall
      exact hclosed.isOpen_compl.mem_nhds (by
        simpa [Real.norm_eq_abs, dist_eq_norm, Metric.mem_closedBall] using (not_le_of_gt hy))
    filter_upwards [hset] with w hw
    exact zeta1d_of_one_half_lt hw
  have hfun : (fun w : ℝ => zeta1d w ^ M) =ᶠ[𝓝 y] (fun _ : ℝ => (0 : ℝ)) := by
    filter_upwards [hzero] with w hw
    rw [hw, zero_pow (ne_of_gt (by omega : 0 < M))]
  have hconst : HasDerivAt (fun _ : ℝ => (0 : ℝ)) 0 y := by
    simpa using (hasDerivAt_const y (0 : ℝ))
  exact hconst.congr_of_eventuallyEq hfun

/-- **`|y| ≥ 1/2` (exterior + the two faces)**: `zeta1d^M` has derivative
`0` at `y` (`2 ≤ M`) — exterior by the constant-zero neighbourhood, faces
by `zeta1d_pow_hasDerivAt_half`/`_neg_half`. -/
lemma zeta1d_pow_hasDerivAt_zero_of_one_half_le {M : ℕ} (hM : 2 ≤ M) {y : ℝ}
    (hy : 1 / 2 ≤ |y|) :
    HasDerivAt (fun w : ℝ => zeta1d w ^ M) 0 y := by
  rcases lt_or_eq_of_le hy with hy_lt | hy_eq
  · exact zeta1d_pow_hasDerivAt_zero_of_one_half_lt (by omega : 1 ≤ M) hy_lt
  · have hb : |y| = 1 / 2 := hy_eq.symm
    by_cases hy0 : 0 ≤ y
    · have hyeq : y = 1 / 2 := by
        have : |y| = y := abs_of_nonneg hy0
        linarith
      subst y
      exact zeta1d_pow_hasDerivAt_half hM
    · have hyeq : y = -(1 / 2) := by
        have : |y| = -y := abs_of_neg (lt_of_not_ge hy0)
        linarith
      subst y
      exact zeta1d_pow_hasDerivAt_neg_half hM

/-- **the derivative of `zeta1d^M` is the piecewise formula**: interior
(`|y| < 1/2`, the cosine-power derivative), `0` on the exterior and at the
faces (`2 ≤ M`). -/
lemma zeta1d_pow_deriv {M : ℕ} (hM : 2 ≤ M) (y : ℝ) :
    deriv (fun w : ℝ => zeta1d w ^ M) y =
      if |y| < 1 / 2 then ↑M * (Real.cos (Real.pi * y)) ^ (M - 1)
          * (-Real.sin (Real.pi * y) * Real.pi) else 0 := by
  by_cases hy : |y| < 1 / 2
  · rw [if_pos hy]
    exact (zeta1d_pow_hasDerivAt_of_abs_lt y hy).deriv
  · rw [if_neg hy]
    exact (zeta1d_pow_hasDerivAt_zero_of_one_half_le hM (le_of_not_gt hy)).deriv



/-- the interior derivative formula of `zeta1d^M`: `↑M·cos(πy)^{M−1}·(−sin(πy)·π)`. -/
noncomputable def zeta1dDerivF (M : ℕ) (y : ℝ) : ℝ :=
  ↑M * (Real.cos (Real.pi * y)) ^ (M - 1) * (-Real.sin (Real.pi * y) * Real.pi)

/-- the piecewise derivative of `zeta1d^M` (`2 ≤ M`): the interior formula on
`|y| < 1/2`, `0` on the exterior and at the faces. -/
noncomputable def zeta1dDerivPiecewise (M : ℕ) (y : ℝ) : ℝ :=
  if |y| < 1 / 2 then zeta1dDerivF M y else 0

/-- the derivative of `zeta1d^M` is the piecewise formula (`zeta1d_pow_deriv`,
def-level). -/
lemma zeta1dDerivPiecewise_eq_deriv {M : ℕ} (hM : 2 ≤ M) :
    (fun w : ℝ => deriv (fun z : ℝ => zeta1d z ^ M) w) = zeta1dDerivPiecewise M := by
  funext y
  dsimp [zeta1dDerivPiecewise, zeta1dDerivF]
  rw [zeta1d_pow_deriv hM y]

/-- the derivative formula is continuous (smooth in cos/sin). -/
lemma zeta1dDerivF_continuous (M : ℕ) : Continuous (zeta1dDerivF M) := by
  unfold zeta1dDerivF
  fun_prop

/-- the derivative formula vanishes at the right face `1/2` (`M ≥ 2`). -/
lemma zeta1dDerivF_zero_at_half {M : ℕ} (hM : 2 ≤ M) : zeta1dDerivF M (1 / 2 : ℝ) = 0 := by
  unfold zeta1dDerivF
  have hM1 : 0 < M - 1 := by omega
  have hval : Real.cos (Real.pi * (1 / 2 : ℝ)) = 0 := by
    rw [show Real.pi * (1 / 2 : ℝ) = Real.pi / 2 by ring]
    exact Real.cos_pi_div_two
  rw [hval, zero_pow (ne_of_gt hM1)]
  ring

/-- the derivative formula vanishes at the left face `−1/2` (`M ≥ 2`). -/
lemma zeta1dDerivF_zero_at_neg_half {M : ℕ} (hM : 2 ≤ M) : zeta1dDerivF M (-(1 / 2 : ℝ)) = 0 := by
  unfold zeta1dDerivF
  have hM1 : 0 < M - 1 := by omega
  have hval : Real.cos (Real.pi * (-(1 / 2 : ℝ))) = 0 := by
    rw [show Real.pi * (-(1 / 2 : ℝ)) = -(Real.pi / 2) by ring]
    rw [Real.cos_neg, Real.cos_pi_div_two]
  rw [hval, zero_pow (ne_of_gt hM1)]
  ring

/-- the piecewise derivative is continuous at the right face `1/2`: globally
`|g| ≤ |F|` (`g = F` on the interior, `0 ≤ |F|` on the exterior), and the
derivative formula tends to `0` there (`cosPow_deriv_tendsto_half`). -/
lemma zeta1dDerivPiecewise_continuousAt_half {M : ℕ} (hM : 2 ≤ M) :
    ContinuousAt (zeta1dDerivPiecewise M) (1 / 2 : ℝ) := by
  change Tendsto (zeta1dDerivPiecewise M) (𝓝 (1 / 2 : ℝ))
    (𝓝 (zeta1dDerivPiecewise M (1 / 2 : ℝ)))
  have hval : zeta1dDerivPiecewise M (1 / 2 : ℝ) = 0 := by
    unfold zeta1dDerivPiecewise
    rw [if_neg (by norm_num : ¬ |(1 / 2 : ℝ)| < 1 / 2)]
  rw [hval]
  have hF0 : Tendsto (zeta1dDerivF M) (𝓝 (1 / 2 : ℝ)) (𝓝 (0 : ℝ)) := by
    exact cosPow_deriv_tendsto_half hM
  have hFabs : Tendsto (fun y : ℝ => |zeta1dDerivF M y|) (𝓝 (1 / 2 : ℝ)) (𝓝 (0 : ℝ)) := by
    have habs0 : ContinuousAt (fun z : ℝ => |z|) (0 : ℝ) :=
      Continuous.continuousAt continuous_abs (x := (0 : ℝ))
    have htmp : Tendsto (fun y : ℝ => |zeta1dDerivF M y|) (𝓝 (1 / 2 : ℝ)) (𝓝 (|(0 : ℝ)|)) :=
      habs0.tendsto.comp hF0
    simpa using htmp
  have hb : ∀ y : ℝ, |zeta1dDerivPiecewise M y| ≤ |zeta1dDerivF M y| := by
    intro y
    dsimp [zeta1dDerivPiecewise]
    by_cases hy : |y| < 1 / 2
    · rw [if_pos hy]
    · rw [if_neg hy]
      simp
  have habs : Tendsto (fun y : ℝ => |zeta1dDerivPiecewise M y|) (𝓝 (1 / 2 : ℝ)) (𝓝 (0 : ℝ)) := by
    refine squeeze_zero (fun y => abs_nonneg _) hb hFabs
  rw [tendsto_iff_norm_sub_tendsto_zero]
  simpa [Real.norm_eq_abs] using habs

/-- the piecewise derivative is continuous at the left face `−1/2` (mirror:
the formula vanishes there via `cosPow_deriv_tendsto_neg_half`). -/
lemma zeta1dDerivPiecewise_continuousAt_neg_half {M : ℕ} (hM : 2 ≤ M) :
    ContinuousAt (zeta1dDerivPiecewise M) (-(1 / 2 : ℝ)) := by
  change Tendsto (zeta1dDerivPiecewise M) (𝓝 (-(1 / 2 : ℝ)))
    (𝓝 (zeta1dDerivPiecewise M (-(1 / 2 : ℝ))))
  have hval : zeta1dDerivPiecewise M (-(1 / 2 : ℝ)) = 0 := by
    unfold zeta1dDerivPiecewise
    rw [if_neg (by norm_num : ¬ |-(1 / 2 : ℝ)| < 1 / 2)]
  rw [hval]
  have hF0 : Tendsto (zeta1dDerivF M) (𝓝 (-(1 / 2 : ℝ))) (𝓝 (0 : ℝ)) := by
    exact cosPow_deriv_tendsto_neg_half hM
  have hFabs : Tendsto (fun y : ℝ => |zeta1dDerivF M y|) (𝓝 (-(1 / 2 : ℝ))) (𝓝 (0 : ℝ)) := by
    have habs0 : ContinuousAt (fun z : ℝ => |z|) (0 : ℝ) :=
      Continuous.continuousAt continuous_abs (x := (0 : ℝ))
    have htmp : Tendsto (fun y : ℝ => |zeta1dDerivF M y|) (𝓝 (-(1 / 2 : ℝ))) (𝓝 (|(0 : ℝ)|)) :=
      habs0.tendsto.comp hF0
    simpa using htmp
  have hb : ∀ y : ℝ, |zeta1dDerivPiecewise M y| ≤ |zeta1dDerivF M y| := by
    intro y
    dsimp [zeta1dDerivPiecewise]
    by_cases hy : |y| < 1 / 2
    · rw [if_pos hy]
    · rw [if_neg hy]
      simp
  have habs : Tendsto (fun y : ℝ => |zeta1dDerivPiecewise M y|) (𝓝 (-(1 / 2 : ℝ))) (𝓝 (0 : ℝ)) := by
    refine squeeze_zero (fun y => abs_nonneg _) hb hFabs
  rw [tendsto_iff_norm_sub_tendsto_zero]
  simpa [Real.norm_eq_abs] using habs

/-- the piecewise derivative is continuous at every point (`2 ≤ M`):
interior (`|y| < 1/2`, eventually equals the continuous formula), exterior
(`1/2 < |y|`, eventually `0`), faces (`y = ±1/2`, the two face lemmas). -/
lemma zeta1dDerivPiecewise_continuousAt {M : ℕ} (hM : 2 ≤ M) (y : ℝ) :
    ContinuousAt (zeta1dDerivPiecewise M) y := by
  by_cases h1 : |y| < 1 / 2
  · -- interior: eventually |w| < 1/2, so g = F there
    have hset : ({w : ℝ | |w| < 1 / 2}) ∈ 𝓝 y := by
      have hset' : {w : ℝ | |w| < 1 / 2} = Metric.ball (0 : ℝ) (1 / 2) := by
        ext w
        simp [Real.norm_eq_abs, dist_eq_norm]
      rw [hset']
      exact Metric.isOpen_ball.mem_nhds (by simpa [Real.norm_eq_abs, dist_eq_norm] using h1)
    have hev : (fun w : ℝ => zeta1dDerivPiecewise M w) =ᶠ[𝓝 y]
        (fun w : ℝ => zeta1dDerivF M w) := by
      filter_upwards [hset] with w hw
      dsimp [zeta1dDerivPiecewise]
      rw [if_pos hw]
    exact ((zeta1dDerivF_continuous M).continuousAt).congr_of_eventuallyEq hev
  · by_cases h2 : 1 / 2 < |y|
    · -- exterior: eventually 1/2 < |w|, so g = 0 there
      have hev0 : (fun w : ℝ => zeta1dDerivPiecewise M w) =ᶠ[𝓝 y]
          (fun _ : ℝ => (0 : ℝ)) := by
        have hset : ({w : ℝ | 1 / 2 < |w|}) ∈ 𝓝 y := by
          have hset' : {w : ℝ | 1 / 2 < |w|} = (Metric.closedBall (0 : ℝ) (1 / 2))ᶜ := by
            ext w
            simp [Real.norm_eq_abs, dist_eq_norm]
          rw [hset']
          have hclosed : IsClosed (Metric.closedBall (0 : ℝ) (1 / 2)) := isClosed_closedBall
          exact hclosed.isOpen_compl.mem_nhds (by
            simpa [Real.norm_eq_abs, dist_eq_norm, Metric.mem_closedBall] using (not_le_of_gt h2))
        filter_upwards [hset] with w hw
        dsimp [zeta1dDerivPiecewise]
        rw [if_neg (not_lt_of_gt hw)]
      exact ((continuousAt_const : ContinuousAt (fun _ : ℝ => (0 : ℝ)) y).congr_of_eventuallyEq hev0)
    · -- face |y| = 1/2
      have hb : |y| = 1 / 2 := le_antisymm (le_of_not_gt h2) (le_of_not_gt h1)
      by_cases hy0 : 0 ≤ y
      · have hyeq : y = 1 / 2 := by
          have : |y| = y := abs_of_nonneg hy0
          linarith
        subst y
        exact zeta1dDerivPiecewise_continuousAt_half hM
      · have hyeq : y = -(1 / 2) := by
          have : |y| = -y := abs_of_neg (lt_of_not_ge hy0)
          linarith
        subst y
        exact zeta1dDerivPiecewise_continuousAt_neg_half hM

/-- **the derivative of `zeta1d^M` is continuous** (`2 ≤ M`) — the
`ContDiff 1` derivative condition. -/
lemma zeta1d_pow_deriv_continuous {M : ℕ} (hM : 2 ≤ M) :
    Continuous (fun w : ℝ => deriv (fun z : ℝ => zeta1d z ^ M) w) := by
  rw [continuous_iff_continuousAt]
  intro y
  have hcontP := zeta1dDerivPiecewise_continuousAt hM y
  have hEq : (fun w : ℝ => deriv (fun z : ℝ => zeta1d z ^ M) w) = zeta1dDerivPiecewise M :=
    zeta1dDerivPiecewise_eq_deriv hM
  simpa [hEq] using hcontP

/-- `zeta1d^M` is differentiable at every point (`2 ≤ M`). -/
lemma zeta1d_pow_differentiable {M : ℕ} (hM : 2 ≤ M) :
    Differentiable ℝ (fun w : ℝ => zeta1d w ^ M) := by
  intro y
  by_cases h1 : |y| < 1 / 2
  · exact (zeta1d_pow_hasDerivAt_of_abs_lt y h1).differentiableAt
  · by_cases h2 : 1 / 2 < |y|
    · exact (zeta1d_pow_hasDerivAt_zero_of_one_half_lt (by omega : 1 ≤ M) h2).differentiableAt
    · have hb : |y| = 1 / 2 := le_antisymm (le_of_not_gt h2) (le_of_not_gt h1)
      by_cases hy0 : 0 ≤ y
      · have hyeq : y = 1 / 2 := by
          have : |y| = y := abs_of_nonneg hy0
          linarith
        subst y
        exact (zeta1d_pow_hasDerivAt_half hM).differentiableAt
      · have hyeq : y = -(1 / 2) := by
          have : |y| = -y := abs_of_neg (lt_of_not_ge hy0)
          linarith
        subst y
        exact (zeta1d_pow_hasDerivAt_neg_half hM).differentiableAt

/-- **`zeta1d^M` is `C¹` on the whole real line** (`2 ≤ M`): differentiable
everywhere (`zeta1d_pow_differentiable`) with continuous derivative
(`zeta1d_pow_deriv_continuous`) — `contDiff_one_iff_deriv`. -/
lemma zeta1d_pow_contDiff_one {M : ℕ} (hM : 2 ≤ M) :
    ContDiff ℝ 1 (fun w : ℝ => zeta1d w ^ M) := by
  rw [contDiff_one_iff_deriv]
  exact ⟨zeta1d_pow_differentiable hM, zeta1d_pow_deriv_continuous hM⟩



/-- the second-derivative interior formula of `zeta1d^M` (the derivative of
`zeta1dDerivF M` on `|y| < 1/2`):
`↑M·π²·cos(πy)^{M−2}·(↑(M−1)·sin(πy)² − cos(πy)²)`.  For `3 ≤ M` the
`cos^{M−2}`-factor vanishes at the faces. -/
noncomputable def zeta1dDeriv2F (M : ℕ) (y : ℝ) : ℝ :=
  ↑M * Real.pi ^ 2 * (Real.cos (Real.pi * y)) ^ (M - 2)
    * (↑(M - 1) * (Real.sin (Real.pi * y)) ^ 2 - (Real.cos (Real.pi * y)) ^ 2)


/-- the absolute values of the sine/cosine squares are ≤ 1. -/
lemma abs_sq_le_one_of_abs_le_one (x : ℝ) (h : |x| ≤ 1) : |x ^ 2| ≤ 1 := by
  rw [abs_pow, pow_two]
  have hm : |x| * |x| ≤ 1 * 1 := mul_le_mul h h (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)
  simpa using hm

/-- pointwise bound of the second-derivative formula at a face `c`:
`|F2(y)| ≤ ((↑M·(↑(M−1)+1))·π²)·(π·|y−c|)^{M−2}` (`3 ≤ M`), using
`|sin|,|cos| ≤ 1` and the cosine face-decay bound `hface`. -/
lemma zeta1dDeriv2F_abs_bound_face {M : ℕ} (hM : 3 ≤ M) {c : ℝ}
    (hface : ∀ y : ℝ, |Real.cos (Real.pi * y)| ≤ Real.pi * |y - c|) (y : ℝ) :
    |zeta1dDeriv2F M y|
      ≤ ((↑M * (↑(M - 1) + 1)) * Real.pi ^ 2) * (Real.pi * |y - c|) ^ (M - 2) := by
  have hc' : |Real.cos (Real.pi * y)| ^ (M - 2) ≤ (Real.pi * |y - c|) ^ (M - 2) :=
    pow_le_pow_left₀ (abs_nonneg _) (hface y) (M - 2)
  have hM0 : 0 ≤ (M : ℝ) := by exact_mod_cast (Nat.zero_le M)
  have hM10 : 0 ≤ ((M - 1 : ℕ) : ℝ) := by exact_mod_cast (Nat.zero_le (M - 1))
  have hsin : |Real.sin (Real.pi * y)| ≤ 1 := Real.abs_sin_le_one (Real.pi * y)
  have hcos : |Real.cos (Real.pi * y)| ≤ 1 := Real.abs_cos_le_one (Real.pi * y)
  have hs1 : |Real.sin (Real.pi * y) ^ 2| ≤ 1 := abs_sq_le_one_of_abs_le_one _ hsin
  have hc1 : |Real.cos (Real.pi * y) ^ 2| ≤ 1 := abs_sq_le_one_of_abs_le_one _ hcos
  have hterm1 : |((M - 1 : ℕ) : ℝ) * Real.sin (Real.pi * y) ^ 2| ≤ ((M - 1 : ℕ) : ℝ) := by
    calc
      |((M - 1 : ℕ) : ℝ) * Real.sin (Real.pi * y) ^ 2|
          = ((M - 1 : ℕ) : ℝ) * |Real.sin (Real.pi * y) ^ 2| := by
              rw [abs_mul, abs_of_nonneg hM10]
      _ ≤ ((M - 1 : ℕ) : ℝ) * 1 := mul_le_mul_of_nonneg_left hs1 hM10
      _ = ((M - 1 : ℕ) : ℝ) := by simp
  have hq : |((M - 1 : ℕ) : ℝ) * Real.sin (Real.pi * y) ^ 2 - Real.cos (Real.pi * y) ^ 2|
      ≤ ((M - 1 : ℕ) : ℝ) + 1 := by
    have habs : |((M - 1 : ℕ) : ℝ) * Real.sin (Real.pi * y) ^ 2 - Real.cos (Real.pi * y) ^ 2|
        ≤ |((M - 1 : ℕ) : ℝ) * Real.sin (Real.pi * y) ^ 2| + |Real.cos (Real.pi * y) ^ 2| := by
      let a : ℝ := ((M - 1 : ℕ) : ℝ) * Real.sin (Real.pi * y) ^ 2
      let b : ℝ := Real.cos (Real.pi * y) ^ 2
      change |a - b| ≤ |a| + |b|
      have htri : |a - b| ≤ |a - 0| + |0 - b| := abs_sub_le a 0 b
      calc
        |a - b| ≤ |a - 0| + |0 - b| := htri
        _ = |a| + |b| := by simp [abs_neg]
    linarith [hterm1, hc1, habs]
  have hK : 0 ≤ (M : ℝ) * (((M - 1 : ℕ) : ℝ) + 1) := by
    exact mul_nonneg hM0 (by positivity)
  calc
    |zeta1dDeriv2F M y|
        = ↑M * Real.pi ^ 2 * (|Real.cos (Real.pi * y)| ^ (M - 2))
            * |((M - 1 : ℕ) : ℝ) * Real.sin (Real.pi * y) ^ 2 - Real.cos (Real.pi * y) ^ 2| := by
            unfold zeta1dDeriv2F
            rw [abs_mul, abs_mul, abs_mul]
            rw [abs_of_nonneg hM0, abs_of_nonneg (sq_nonneg Real.pi)]
            rw [abs_pow]
    _ ≤ ↑M * Real.pi ^ 2 * (Real.pi * |y - c|) ^ (M - 2)
          * |((M - 1 : ℕ) : ℝ) * Real.sin (Real.pi * y) ^ 2 - Real.cos (Real.pi * y) ^ 2| := by
            have hb1 : ↑M * Real.pi ^ 2 * |Real.cos (Real.pi * y)| ^ (M - 2)
                ≤ ↑M * Real.pi ^ 2 * (Real.pi * |y - c|) ^ (M - 2) := by
              exact mul_le_mul_of_nonneg_left hc' (mul_nonneg hM0 (sq_nonneg Real.pi))
            exact mul_le_mul_of_nonneg_right hb1 (abs_nonneg _)
    _ ≤ (↑M * Real.pi ^ 2 * (Real.pi * |y - c|) ^ (M - 2)) * (((M - 1 : ℕ) : ℝ) + 1) := by
            exact mul_le_mul_of_nonneg_left hq
              (mul_nonneg (mul_nonneg hM0 (sq_nonneg Real.pi))
                (pow_nonneg (mul_nonneg (le_of_lt Real.pi_pos) (abs_nonneg _)) (M - 2)))
    _ = ((↑M * (↑(M - 1) + 1)) * Real.pi ^ 2) * (Real.pi * |y - c|) ^ (M - 2) := by ring

/-- **face limit of the second-derivative formula**: for `3 ≤ M` the value
`zeta1dDeriv2F M y` tends to `0` as `y → c` at a face (`c = ±1/2`; the
`cos^{M−2}`-factor with `M−2 ≥ 1` vanishes against the cosine face-decay
bound).  Keystone for the continuity of `deriv² (ζ^M)` through the cuts
(→ `ContDiff 2`). -/
lemma zeta1dDeriv2F_tendsto_face {M : ℕ} (hM : 3 ≤ M) {c : ℝ}
    (hface : ∀ y : ℝ, |Real.cos (Real.pi * y)| ≤ Real.pi * |y - c|) :
    Tendsto (zeta1dDeriv2F M) (𝓝 c) (𝓝 (0 : ℝ)) := by
  have hM2 : 0 < M - 2 := by omega
  have hnear : Tendsto (fun y : ℝ => |y - c|) (𝓝 c) (𝓝 (0 : ℝ)) := by
    have hc : ContinuousAt (fun y : ℝ => |y - c|) c :=
      (continuous_abs.comp (continuous_id.sub continuous_const)).continuousAt
    simpa using hc.tendsto
  have hpow0 : Tendsto (fun y : ℝ => |y - c| ^ (M - 2)) (𝓝 c) (𝓝 (0 : ℝ)) := by
    simpa [zero_pow (ne_of_gt hM2)] using (hnear.pow (M - 2))
  have h1 : Tendsto (fun y : ℝ => (Real.pi * |y - c|) ^ (M - 2)) (𝓝 c) (𝓝 (0 : ℝ)) := by
    simpa [mul_pow, mul_zero] using (tendsto_const_nhds.mul hpow0)
  let K : ℝ := (↑M * (↑(M - 1) + 1)) * Real.pi ^ 2
  have hK0 : 0 ≤ K := by
    dsimp [K]
    exact mul_nonneg (mul_nonneg (by exact_mod_cast (Nat.zero_le M)) (by positivity)) (sq_nonneg Real.pi)
  have hg0 : Tendsto (fun y : ℝ => K * (Real.pi * |y - c|) ^ (M - 2)) (𝓝 c) (𝓝 (0 : ℝ)) := by
    simpa [mul_zero] using (tendsto_const_nhds.mul h1)
  have hb : ∀ y : ℝ, |zeta1dDeriv2F M y| ≤ K * (Real.pi * |y - c|) ^ (M - 2) := by
    intro y
    simpa [K] using zeta1dDeriv2F_abs_bound_face hM hface y
  have habs : Tendsto (fun y : ℝ => |zeta1dDeriv2F M y|) (𝓝 c) (𝓝 (0 : ℝ)) := by
    refine squeeze_zero (fun y => abs_nonneg _) hb hg0
  rw [tendsto_iff_norm_sub_tendsto_zero]
  simpa [Real.norm_eq_abs] using habs

/-- the second-derivative formula tends to `0` at the right face `1/2`
(`3 ≤ M`). -/
lemma zeta1dDeriv2F_tendsto_half {M : ℕ} (hM : 3 ≤ M) :
    Tendsto (zeta1dDeriv2F M) (𝓝 (1 / 2 : ℝ)) (𝓝 (0 : ℝ)) := by
  exact zeta1dDeriv2F_tendsto_face hM cos_abs_le_pi_sub_half

/-- the second-derivative formula tends to `0` at the left face `−1/2`
(`3 ≤ M`). -/
lemma zeta1dDeriv2F_tendsto_neg_half {M : ℕ} (hM : 3 ≤ M) :
    Tendsto (zeta1dDeriv2F M) (𝓝 (-(1 / 2 : ℝ))) (𝓝 (0 : ℝ)) := by
  refine zeta1dDeriv2F_tendsto_face hM ?_
  intro y
  simpa [sub_eq_add_neg] using cos_abs_le_pi_add_half y



/-- the affine sine chain: `HasDerivAt (fun w => sin(πw)) (cos(πy)·π) y`
(mirror of `cos_affine_hasDerivAt`). -/
lemma sin_affine_hasDerivAt (y : ℝ) :
    HasDerivAt (fun w : ℝ => Real.sin (Real.pi * w)) (Real.cos (Real.pi * y) * Real.pi) y := by
  have hlin : HasDerivAt (fun w : ℝ => Real.pi * w) Real.pi y := by
    convert (hasDerivAt_id y).const_mul Real.pi using 1 <;> first | rfl | exact (mul_one Real.pi).symm
  convert (Real.hasDerivAt_sin (Real.pi * y)).comp y hlin using 1 <;> rfl

/-- **the derivative formula differentiates to the second-derivative
formula**: `HasDerivAt (zeta1dDerivF M) (zeta1dDeriv2F M y) y` for `2 ≤ M`
(value-level chain: `cos_affine_hasDerivAt`.fun_pow for the cosine power,
the affine sine chain for `−sin(π·)π`, product rule, `HasDerivAt.const_mul`). -/
lemma zeta1dDerivF_hasDerivAt {M : ℕ} (hM : 2 ≤ M) (y : ℝ) :
    HasDerivAt (zeta1dDerivF M) (zeta1dDeriv2F M y) y := by
  have hlin : HasDerivAt (fun w : ℝ => Real.pi * w) Real.pi y := by
    convert (hasDerivAt_id y).const_mul Real.pi using 1 <;> first | rfl | exact (mul_one Real.pi).symm
  have hsin' : HasDerivAt (fun w : ℝ => Real.sin (Real.pi * w)) (Real.cos (Real.pi * y) * Real.pi) y := by
    convert (Real.hasDerivAt_sin (Real.pi * y)).comp y hlin using 1 <;> rfl
  have hc : HasDerivAt (fun w : ℝ => Real.cos (Real.pi * w) ^ (M - 1))
      (((M - 1 : ℕ) : ℝ) * (Real.cos (Real.pi * y)) ^ ((M - 1) - 1)
        * (-Real.sin (Real.pi * y) * Real.pi)) y := by
    simpa using ((cos_affine_hasDerivAt y).fun_pow (M - 1))
  have hs : HasDerivAt (fun w : ℝ => -Real.sin (Real.pi * w) * Real.pi)
      (-(Real.cos (Real.pi * y) * Real.pi) * Real.pi) y := by
    have hneg := hsin'.neg
    simpa using (hneg.mul_const Real.pi)
  have hm := hc.mul hs
  have hF := HasDerivAt.const_mul (↑M : ℝ) hm
  convert hF using 1
  all_goals try rfl
  all_goals try (funext w; dsimp [zeta1dDerivF]; ring)
  · have hrec1 : (M - 1) - 1 = M - 2 := by omega
    have hrec2 : M - 1 = (M - 2) + 1 := by omega
    have hcM1 : Real.cos (Real.pi * y) ^ (M - 1)
        = Real.cos (Real.pi * y) ^ (M - 2) * Real.cos (Real.pi * y) := by
      rw [hrec2, pow_succ]
    unfold zeta1dDeriv2F
    rw [hrec1]
    rw [hcM1]
    ring_nf
/-- the second-derivative formula vanishes at the right face `1/2` (`3 ≤ M`:
the `cos^{M−2}`-factor vanishes). -/
lemma zeta1dDeriv2F_zero_at_half {M : ℕ} (hM : 3 ≤ M) : zeta1dDeriv2F M (1 / 2 : ℝ) = 0 := by
  unfold zeta1dDeriv2F
  have hM2 : 0 < M - 2 := by omega
  have hval : Real.cos (Real.pi * (1 / 2 : ℝ)) = 0 := by
    rw [show Real.pi * (1 / 2 : ℝ) = Real.pi / 2 by ring]
    exact Real.cos_pi_div_two
  rw [hval, zero_pow (ne_of_gt hM2)]
  ring

/-- the second-derivative formula vanishes at the left face `−1/2` (`3 ≤ M`). -/
lemma zeta1dDeriv2F_zero_at_neg_half {M : ℕ} (hM : 3 ≤ M) : zeta1dDeriv2F M (-(1 / 2 : ℝ)) = 0 := by
  unfold zeta1dDeriv2F
  have hM2 : 0 < M - 2 := by omega
  have hval : Real.cos (Real.pi * (-(1 / 2 : ℝ))) = 0 := by
    rw [show Real.pi * (-(1 / 2 : ℝ)) = -(Real.pi / 2) by ring]
    rw [Real.cos_neg, Real.cos_pi_div_two]
  rw [hval, zero_pow (ne_of_gt hM2)]
  ring

/-- **the piecewise derivative has derivative `0` at a face point `c`
(`c = ±1/2`, `3 ≤ M`)**: on the interior side (`|w| < 1/2`) it equals the
differentiable `F` with `F(c) = 0` and `F'(c) = 0`
(`zeta1dDerivF_hasDerivAt` + the vanishing of `zeta1dDeriv2F`), on the
exterior side it is `0` — and globally `|g| ≤ |F|`, so the global squeeze
gives the result. -/
lemma zeta1dDerivPiecewise_hasDerivAt_zero_face {M : ℕ} (hM : 3 ≤ M) {c : ℝ}
    (hc : c = (1 / 2 : ℝ) ∨ c = -(1 / 2 : ℝ)) :
    HasDerivAt (zeta1dDerivPiecewise M) 0 c := by
  have hF2c : zeta1dDeriv2F M c = 0 := by
    rcases hc with rfl | rfl
    · exact zeta1dDeriv2F_zero_at_half hM
    · exact zeta1dDeriv2F_zero_at_neg_half hM
  have hd := zeta1dDerivF_hasDerivAt (by omega : 2 ≤ M) c
  have hF0 : HasDerivAt (zeta1dDerivF M) 0 c := hd.congr_deriv hF2c
  have hFc : zeta1dDerivF M c = 0 := by
    rcases hc with rfl | rfl
    · exact zeta1dDerivF_zero_at_half (by omega : 2 ≤ M)
    · exact zeta1dDerivF_zero_at_neg_half (by omega : 2 ≤ M)
  have hgc : zeta1dDerivPiecewise M c = 0 := by
    unfold zeta1dDerivPiecewise
    rcases hc with rfl | rfl
    · rw [if_neg (by norm_num : ¬ |(1 / 2 : ℝ)| < 1 / 2)]
    · rw [if_neg (by norm_num : ¬ |-(1 / 2 : ℝ)| < 1 / 2)]
  -- difference-quotient ratios: |g w| ≤ |F w| globally
  have hle : ∀ w : ℝ, |zeta1dDerivPiecewise M w| ≤ |zeta1dDerivF M w| := by
    intro w
    dsimp [zeta1dDerivPiecewise]
    by_cases hw : |w| < 1 / 2
    · rw [if_pos hw]
    · rw [if_neg hw]
      simp
  -- squeeze the g-ratio by the F-ratio (which → 0 by hF0)
  rw [hasDerivAt_iff_tendsto]
  have hF0t : Tendsto (fun w : ℝ => ‖w - c‖⁻¹ * ‖zeta1dDerivF M w‖)
      (𝓝 c) (𝓝 (0 : ℝ)) := by
    have htmp := hasDerivAt_iff_tendsto.mp hF0
    -- htmp's function: ‖w−c‖⁻¹·‖F w − F c − (w−c)•0‖; simplify with hFc
    simpa [hFc] using htmp
  have hgt : Tendsto (fun w : ℝ => ‖w - c‖⁻¹ * ‖zeta1dDerivPiecewise M w‖)
      (𝓝 c) (𝓝 (0 : ℝ)) := by
    refine squeeze_zero (fun w => ?_) (fun w => ?_) hF0t
    · exact mul_nonneg (inv_nonneg.mpr (norm_nonneg _)) (norm_nonneg _)
    · have hle' := hle w
      have hnorm : ‖zeta1dDerivPiecewise M w‖ ≤ ‖zeta1dDerivF M w‖ := by
        simpa [Real.norm_eq_abs] using hle'
      exact mul_le_mul_of_nonneg_left hnorm (inv_nonneg.mpr (norm_nonneg (w - c)))
  simpa [hgc] using hgt



/-- **exterior points `1/2 < |y|`**: the piecewise derivative `zeta1dDerivPiecewise`
is identically `0` on a neighbourhood of `y`, hence has derivative `0` there. -/
lemma zeta1dDerivPiecewise_hasDerivAt_zero_of_one_half_lt {M : ℕ} {y : ℝ}
    (hy : 1 / 2 < |y|) :
    HasDerivAt (zeta1dDerivPiecewise M) 0 y := by
  have hzero : ∀ᶠ w : ℝ in 𝓝 y, zeta1dDerivPiecewise M w = 0 := by
    have hset : ({w : ℝ | 1 / 2 < |w|}) ∈ 𝓝 y := by
      have hset' : {w : ℝ | 1 / 2 < |w|} = (Metric.closedBall (0 : ℝ) (1 / 2))ᶜ := by
        ext w
        simp [Real.norm_eq_abs, dist_eq_norm]
      rw [hset']
      have hclosed : IsClosed (Metric.closedBall (0 : ℝ) (1 / 2)) := isClosed_closedBall
      exact hclosed.isOpen_compl.mem_nhds (by
        simpa [Real.norm_eq_abs, dist_eq_norm, Metric.mem_closedBall] using (not_le_of_gt hy))
    filter_upwards [hset] with w hw
    dsimp [zeta1dDerivPiecewise]
    rw [if_neg (not_lt_of_gt hw)]
  have hfun : (fun w : ℝ => zeta1dDerivPiecewise M w) =ᶠ[𝓝 y] (fun _ : ℝ => (0 : ℝ)) := by
    filter_upwards [hzero] with w hw
    exact hw
  have hconst : HasDerivAt (fun _ : ℝ => (0 : ℝ)) 0 y := by
    simpa using (hasDerivAt_const y (0 : ℝ))
  exact hconst.congr_of_eventuallyEq hfun

/-- **`|y| ≥ 1/2` (exterior + the two faces)**: the piecewise derivative has
derivative `0` at `y` (`3 ≤ M`) — exterior by the constant-zero
neighbourhood, faces by `zeta1dDerivPiecewise_hasDerivAt_zero_face`. -/
lemma zeta1dDerivPiecewise_hasDerivAt_zero_of_one_half_le {M : ℕ} (hM : 3 ≤ M) {y : ℝ}
    (hy : 1 / 2 ≤ |y|) :
    HasDerivAt (zeta1dDerivPiecewise M) 0 y := by
  rcases lt_or_eq_of_le hy with hy_lt | hy_eq
  · exact zeta1dDerivPiecewise_hasDerivAt_zero_of_one_half_lt hy_lt
  · have hb : |y| = 1 / 2 := hy_eq.symm
    by_cases hy0 : 0 ≤ y
    · have hyeq : y = 1 / 2 := by
        have : |y| = y := abs_of_nonneg hy0
        linarith
      rw [hyeq]
      exact zeta1dDerivPiecewise_hasDerivAt_zero_face (c := (1 / 2 : ℝ)) hM (Or.inl rfl)
    · have hyeq : y = -(1 / 2) := by
        have : |y| = -y := abs_of_neg (lt_of_not_ge hy0)
        linarith
      rw [hyeq]
      exact zeta1dDerivPiecewise_hasDerivAt_zero_face (c := (-(1 / 2 : ℝ))) hM (Or.inr rfl)

/-- **`deriv² (ζ^M)` vanishes on `|y| ≥ 1/2`** (`3 ≤ M`): the second
derivative of `zeta1d^M` is `0` on the exterior and at the two faces
(`deriv (deriv ζ^M) = deriv zeta1dDerivPiecewise`, whose HasDerivAt is `0`
there). -/
lemma zeta1d_pow_second_deriv_eq_zero_of_one_half_le {M : ℕ} (hM : 3 ≤ M) {y : ℝ}
    (hy : 1 / 2 ≤ |y|) :
    deriv (fun w : ℝ => deriv (fun z : ℝ => zeta1d z ^ M) w) y = 0 := by
  have hEq : (fun w : ℝ => deriv (fun z : ℝ => zeta1d z ^ M) w) = zeta1dDerivPiecewise M :=
    zeta1dDerivPiecewise_eq_deriv (by omega : 2 ≤ M)
  rw [hEq]
  exact (zeta1dDerivPiecewise_hasDerivAt_zero_of_one_half_le hM hy).deriv



/-- **interior points `|y| < 1/2`**: the piecewise derivative has derivative
`zeta1dDeriv2F M y` at `y` — it equals the derivative formula `zeta1dDerivF`
on a neighbourhood of `y` (`zeta1dDerivPiecewise`'s `if_pos` branch), and
`zeta1dDerivF_hasDerivAt` differentiates that formula. -/
lemma zeta1dDerivPiecewise_hasDerivAt_of_abs_lt {M : ℕ} (hM : 2 ≤ M) (y : ℝ)
    (hy : |y| < 1 / 2) :
    HasDerivAt (zeta1dDerivPiecewise M) (zeta1dDeriv2F M y) y := by
  have hg := zeta1dDerivF_hasDerivAt hM y
  refine hg.congr_of_eventuallyEq ?_
  have hset : ({w : ℝ | |w| < 1 / 2}) ∈ 𝓝 y := by
    have hset' : {w : ℝ | |w| < 1 / 2} = Metric.ball (0 : ℝ) (1 / 2) := by
      ext w
      simp [Real.norm_eq_abs, dist_eq_norm]
    rw [hset']
    exact Metric.isOpen_ball.mem_nhds (by simpa [Real.norm_eq_abs, dist_eq_norm] using hy)
  filter_upwards [hset] with w hw
  dsimp [zeta1dDerivPiecewise]
  rw [if_pos hw]

/-- **the full piecewise second derivative of `zeta1d^M`** (`3 ≤ M`):
`deriv²(ζ^M) = if |y| < 1/2 then zeta1dDeriv2F M y else 0` — interior by
`zeta1dDerivPiecewise_hasDerivAt_of_abs_lt`, exterior and faces by
`zeta1d_pow_second_deriv_eq_zero_of_one_half_le`. -/
lemma zeta1d_pow_second_deriv {M : ℕ} (hM : 3 ≤ M) (y : ℝ) :
    deriv (fun w : ℝ => deriv (fun z : ℝ => zeta1d z ^ M) w) y =
      if |y| < 1 / 2 then zeta1dDeriv2F M y else 0 := by
  by_cases hy : |y| < 1 / 2
  · rw [if_pos hy]
    rw [zeta1dDerivPiecewise_eq_deriv (by omega : 2 ≤ M)]
    exact (zeta1dDerivPiecewise_hasDerivAt_of_abs_lt (by omega : 2 ≤ M) y hy).deriv
  · rw [if_neg hy]
    exact zeta1d_pow_second_deriv_eq_zero_of_one_half_le hM (le_of_not_gt hy)



/-- the piecewise second derivative of `zeta1d^M`: the interior formula
`zeta1dDeriv2F` on `|y| < 1/2`, `0` on the exterior and at the faces. -/
noncomputable def zeta1dDeriv2Piecewise (M : ℕ) (y : ℝ) : ℝ :=
  if |y| < 1 / 2 then zeta1dDeriv2F M y else 0

/-- the second derivative of `zeta1d^M` is the piecewise second-derivative
formula (`zeta1d_pow_second_deriv`, def-level). -/
lemma zeta1dDeriv2Piecewise_eq_second_deriv {M : ℕ} (hM : 3 ≤ M) :
    (fun y : ℝ => deriv (fun w : ℝ => deriv (fun z : ℝ => zeta1d z ^ M) w) y) =
      zeta1dDeriv2Piecewise M := by
  funext y
  dsimp [zeta1dDeriv2Piecewise]
  rw [zeta1d_pow_second_deriv hM y]

/-- the second-derivative formula is continuous (smooth in cos/sin). -/
lemma zeta1dDeriv2F_continuous (M : ℕ) : Continuous (zeta1dDeriv2F M) := by
  unfold zeta1dDeriv2F
  fun_prop

/-- the piecewise second derivative is continuous at the right face `1/2`:
globally `|g₂| ≤ |F₂|` and `F₂ → 0` there
(`zeta1dDeriv2F_tendsto_half`). -/
lemma zeta1dDeriv2Piecewise_continuousAt_half {M : ℕ} (hM : 3 ≤ M) :
    ContinuousAt (zeta1dDeriv2Piecewise M) (1 / 2 : ℝ) := by
  change Tendsto (zeta1dDeriv2Piecewise M) (𝓝 (1 / 2 : ℝ))
    (𝓝 (zeta1dDeriv2Piecewise M (1 / 2 : ℝ)))
  have hval : zeta1dDeriv2Piecewise M (1 / 2 : ℝ) = 0 := by
    unfold zeta1dDeriv2Piecewise
    rw [if_neg (by norm_num : ¬ |(1 / 2 : ℝ)| < 1 / 2)]
  rw [hval]
  have hF0 : Tendsto (zeta1dDeriv2F M) (𝓝 (1 / 2 : ℝ)) (𝓝 (0 : ℝ)) :=
    zeta1dDeriv2F_tendsto_half hM
  have hFabs : Tendsto (fun y : ℝ => |zeta1dDeriv2F M y|) (𝓝 (1 / 2 : ℝ)) (𝓝 (0 : ℝ)) := by
    have habs0 : ContinuousAt (fun z : ℝ => |z|) (0 : ℝ) :=
      Continuous.continuousAt continuous_abs (x := (0 : ℝ))
    have htmp : Tendsto (fun y : ℝ => |zeta1dDeriv2F M y|) (𝓝 (1 / 2 : ℝ)) (𝓝 (|(0 : ℝ)|)) :=
      habs0.tendsto.comp hF0
    simpa using htmp
  have hb : ∀ y : ℝ, |zeta1dDeriv2Piecewise M y| ≤ |zeta1dDeriv2F M y| := by
    intro y
    dsimp [zeta1dDeriv2Piecewise]
    by_cases hy : |y| < 1 / 2
    · rw [if_pos hy]
    · rw [if_neg hy]
      simp
  have habs : Tendsto (fun y : ℝ => |zeta1dDeriv2Piecewise M y|) (𝓝 (1 / 2 : ℝ)) (𝓝 (0 : ℝ)) := by
    refine squeeze_zero (fun y => abs_nonneg _) hb hFabs
  rw [tendsto_iff_norm_sub_tendsto_zero]
  simpa [Real.norm_eq_abs] using habs

/-- the piecewise second derivative is continuous at the left face `−1/2`
(mirror, `zeta1dDeriv2F_tendsto_neg_half`). -/
lemma zeta1dDeriv2Piecewise_continuousAt_neg_half {M : ℕ} (hM : 3 ≤ M) :
    ContinuousAt (zeta1dDeriv2Piecewise M) (-(1 / 2 : ℝ)) := by
  change Tendsto (zeta1dDeriv2Piecewise M) (𝓝 (-(1 / 2 : ℝ)))
    (𝓝 (zeta1dDeriv2Piecewise M (-(1 / 2 : ℝ))))
  have hval : zeta1dDeriv2Piecewise M (-(1 / 2 : ℝ)) = 0 := by
    unfold zeta1dDeriv2Piecewise
    rw [if_neg (by norm_num : ¬ |-(1 / 2 : ℝ)| < 1 / 2)]
  rw [hval]
  have hF0 : Tendsto (zeta1dDeriv2F M) (𝓝 (-(1 / 2 : ℝ))) (𝓝 (0 : ℝ)) :=
    zeta1dDeriv2F_tendsto_neg_half hM
  have hFabs : Tendsto (fun y : ℝ => |zeta1dDeriv2F M y|) (𝓝 (-(1 / 2 : ℝ))) (𝓝 (0 : ℝ)) := by
    have habs0 : ContinuousAt (fun z : ℝ => |z|) (0 : ℝ) :=
      Continuous.continuousAt continuous_abs (x := (0 : ℝ))
    have htmp : Tendsto (fun y : ℝ => |zeta1dDeriv2F M y|) (𝓝 (-(1 / 2 : ℝ))) (𝓝 (|(0 : ℝ)|)) :=
      habs0.tendsto.comp hF0
    simpa using htmp
  have hb : ∀ y : ℝ, |zeta1dDeriv2Piecewise M y| ≤ |zeta1dDeriv2F M y| := by
    intro y
    dsimp [zeta1dDeriv2Piecewise]
    by_cases hy : |y| < 1 / 2
    · rw [if_pos hy]
    · rw [if_neg hy]
      simp
  have habs : Tendsto (fun y : ℝ => |zeta1dDeriv2Piecewise M y|) (𝓝 (-(1 / 2 : ℝ))) (𝓝 (0 : ℝ)) := by
    refine squeeze_zero (fun y => abs_nonneg _) hb hFabs
  rw [tendsto_iff_norm_sub_tendsto_zero]
  simpa [Real.norm_eq_abs] using habs



/-- the piecewise second derivative is continuous at every point (`3 ≤ M`):
interior (eventually equals the smooth `zeta1dDeriv2F`), exterior
(eventually `0`), faces (the two face lemmas). -/
lemma zeta1dDeriv2Piecewise_continuousAt {M : ℕ} (hM : 3 ≤ M) (y : ℝ) :
    ContinuousAt (zeta1dDeriv2Piecewise M) y := by
  by_cases h1 : |y| < 1 / 2
  · have hset : ({w : ℝ | |w| < 1 / 2}) ∈ 𝓝 y := by
      have hset' : {w : ℝ | |w| < 1 / 2} = Metric.ball (0 : ℝ) (1 / 2) := by
        ext w
        simp [Real.norm_eq_abs, dist_eq_norm]
      rw [hset']
      exact Metric.isOpen_ball.mem_nhds (by simpa [Real.norm_eq_abs, dist_eq_norm] using h1)
    have hev : (fun w : ℝ => zeta1dDeriv2Piecewise M w) =ᶠ[𝓝 y]
        (fun w : ℝ => zeta1dDeriv2F M w) := by
      filter_upwards [hset] with w hw
      dsimp [zeta1dDeriv2Piecewise]
      rw [if_pos hw]
    exact ((zeta1dDeriv2F_continuous M).continuousAt).congr_of_eventuallyEq hev
  · by_cases h2 : 1 / 2 < |y|
    · have hset : ({w : ℝ | 1 / 2 < |w|}) ∈ 𝓝 y := by
        have hset' : {w : ℝ | 1 / 2 < |w|} = (Metric.closedBall (0 : ℝ) (1 / 2))ᶜ := by
          ext w
          simp [Real.norm_eq_abs, dist_eq_norm]
        rw [hset']
        have hclosed : IsClosed (Metric.closedBall (0 : ℝ) (1 / 2)) := isClosed_closedBall
        exact hclosed.isOpen_compl.mem_nhds (by
          simpa [Real.norm_eq_abs, dist_eq_norm, Metric.mem_closedBall] using (not_le_of_gt h2))
      have hev0 : (fun w : ℝ => zeta1dDeriv2Piecewise M w) =ᶠ[𝓝 y]
          (fun _ : ℝ => (0 : ℝ)) := by
        filter_upwards [hset] with w hw
        dsimp [zeta1dDeriv2Piecewise]
        rw [if_neg (not_lt_of_gt hw)]
      exact ((continuousAt_const : ContinuousAt (fun _ : ℝ => (0 : ℝ)) y).congr_of_eventuallyEq hev0)
    · have hb : |y| = 1 / 2 := le_antisymm (le_of_not_gt h2) (le_of_not_gt h1)
      by_cases hy0 : 0 ≤ y
      · have hyeq : y = 1 / 2 := by
          have : |y| = y := abs_of_nonneg hy0
          linarith
        rw [hyeq]
        exact zeta1dDeriv2Piecewise_continuousAt_half hM
      · have hyeq : y = -(1 / 2) := by
          have : |y| = -y := abs_of_neg (lt_of_not_ge hy0)
          linarith
        rw [hyeq]
        exact zeta1dDeriv2Piecewise_continuousAt_neg_half hM

/-- the piecewise second derivative is continuous (`3 ≤ M`). -/
lemma zeta1dDeriv2Piecewise_continuous {M : ℕ} (hM : 3 ≤ M) :
    Continuous (zeta1dDeriv2Piecewise M) := by
  rw [continuous_iff_continuousAt]
  exact fun y => zeta1dDeriv2Piecewise_continuousAt hM y

/-- **`deriv² (ζ^M)` is continuous** (`3 ≤ M`) — the `ContDiff 2` second
derivative condition. -/
lemma zeta1d_pow_second_deriv_continuous {M : ℕ} (hM : 3 ≤ M) :
    Continuous (fun y : ℝ => deriv (fun w : ℝ => deriv (fun z : ℝ => zeta1d z ^ M) w) y) := by
  have hEq := zeta1dDeriv2Piecewise_eq_second_deriv hM
  simpa [hEq] using zeta1dDeriv2Piecewise_continuous hM

/-- the derivative of the piecewise first derivative is the piecewise second
derivative (`3 ≤ M`). -/
lemma zeta1dDerivPiecewise_deriv {M : ℕ} (hM : 3 ≤ M) (y : ℝ) :
    deriv (zeta1dDerivPiecewise M) y = zeta1dDeriv2Piecewise M y := by
  by_cases hy : |y| < 1 / 2
  · dsimp [zeta1dDeriv2Piecewise]
    rw [if_pos hy]
    exact (zeta1dDerivPiecewise_hasDerivAt_of_abs_lt (by omega : 2 ≤ M) y hy).deriv
  · dsimp [zeta1dDeriv2Piecewise]
    rw [if_neg hy]
    exact (zeta1dDerivPiecewise_hasDerivAt_zero_of_one_half_le hM (le_of_not_gt hy)).deriv

/-- the piecewise first derivative is differentiable everywhere (`3 ≤ M`). -/
lemma zeta1dDerivPiecewise_differentiable {M : ℕ} (hM : 3 ≤ M) :
    Differentiable ℝ (zeta1dDerivPiecewise M) := by
  intro y
  by_cases h1 : |y| < 1 / 2
  · exact (zeta1dDerivPiecewise_hasDerivAt_of_abs_lt (by omega : 2 ≤ M) y h1).differentiableAt
  · by_cases h2 : 1 / 2 < |y|
    · exact (zeta1dDerivPiecewise_hasDerivAt_zero_of_one_half_lt h2).differentiableAt
    · have hb : |y| = 1 / 2 := le_antisymm (le_of_not_gt h2) (le_of_not_gt h1)
      by_cases hy0 : 0 ≤ y
      · have hyeq : y = 1 / 2 := by
          have : |y| = y := abs_of_nonneg hy0
          linarith
        rw [hyeq]
        exact (zeta1dDerivPiecewise_hasDerivAt_zero_face hM (Or.inl rfl)).differentiableAt
      · have hyeq : y = -(1 / 2) := by
          have : |y| = -y := abs_of_neg (lt_of_not_ge hy0)
          linarith
        rw [hyeq]
        exact (zeta1dDerivPiecewise_hasDerivAt_zero_face hM (Or.inr rfl)).differentiableAt

/-- **the piecewise first derivative is `C¹`** (`3 ≤ M`): differentiable
everywhere with continuous derivative (the piecewise second derivative). -/
lemma zeta1dDerivPiecewise_contDiff_one {M : ℕ} (hM : 3 ≤ M) :
    ContDiff ℝ 1 (zeta1dDerivPiecewise M) := by
  rw [contDiff_one_iff_deriv]
  constructor
  · exact zeta1dDerivPiecewise_differentiable hM
  · have hEq : (fun y : ℝ => deriv (zeta1dDerivPiecewise M) y) = zeta1dDeriv2Piecewise M := by
      funext y
      exact zeta1dDerivPiecewise_deriv hM y
    simpa [hEq] using zeta1dDeriv2Piecewise_continuous hM

/-- **`zeta1d^M` is `C²` on the whole real line** (`3 ≤ M`): from
`contDiff_succ_iff_deriv` with the differentiability of `ζ^M` and the
`C¹`-ness of its derivative (the piecewise first derivative). -/
lemma zeta1d_pow_contDiff_two {M : ℕ} (hM : 3 ≤ M) :
    ContDiff ℝ 2 (fun w : ℝ => zeta1d w ^ M) := by
  rw [show (2 : ℕ∞ω) = (1 : ℕ∞ω) + 1 by norm_num]
  rw [contDiff_succ_iff_deriv]
  constructor
  · exact zeta1d_pow_differentiable (by omega : 2 ≤ M)
  · constructor
    · intro h
      norm_num at h
    · have hEq : (fun w : ℝ => deriv (fun z : ℝ => zeta1d z ^ M) w) = zeta1dDerivPiecewise M :=
        zeta1dDerivPiecewise_eq_deriv (by omega : 2 ≤ M)
      have hEq' : (deriv (fun w : ℝ => zeta1d w ^ M)) = zeta1dDerivPiecewise M := by
        simpa using hEq
      rw [hEq']
      exact zeta1dDerivPiecewise_contDiff_one hM



end BoseGases
end Submission
