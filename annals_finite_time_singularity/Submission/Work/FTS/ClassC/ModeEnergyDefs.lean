/-
Copyright: work module for the Elgindi finite-time singularity project.

# `FTS/ClassC/ModeEnergyDefs` — the vocabulary of the per-mode weighted energy identity

The elliptic existence node (`Work.FTS.PhiStar.bslOp_sol_exists`) needs, at level `0` of the
`ℋ`-tower, the *finiteness* of the `w²`-weighted quantities of the modal solution
`Ψ = Σ_m a_m e_m`, `a_m = radGreen α m (cmode m F)`.  The route is *per mode*: the mode-`m`
radial problem

  `-α²z²a'' - α(5+α)za' + λ_m a = c_m`,   `λ_m = 2m(2m+5) ≥ 14` (`m ≥ 1`),

multiplied by `a·w²` and integrated by parts (the paper's Step 1 of the proof of `prop:H2`,
specialised to a single mode and with the *exact* radial weight, no Fourier step needed because
the angular factor is an eigenfunction) gives

  `α²∫(za')²w² + (λ_m - 3α² - 3α(5+α)/2)∫a²w² ≤ ∫c_m a w²`.

The gain `λ_m - O(α) ≥ 14 - O(α)` is what makes the per-mode bounds *summable* over `m` (a
`λ_m⁻¹` decay of the `z`-norms), with constants that are uniform in `m`.

This file fixes the vocabulary of the identity (all of it `sorry`-free):

* `rw z = (1+z)^4/z^2 = (z·w(z))²` — the radial weight with the `1/z^4` split off (so that
  `rw z · (a' z)² = (z a' z)² · w(z)²`);
* `rwb`, `rwbb`, `rwc` — the explicit derivative formulas `(rw)'`, `(rw)''`, `(rw/z)'`;
* `flux α a` — the antiderivative (in `z`) of the integrand of the identity: the boundary term
  of the integration by parts, which the hypotheses of `modeWeightedEnergy` send to `0` at both
  ends of `(0,∞)`;
* the elementary lemmas about them: `rw_eq_w`, `hasDerivAt_rw`, `hasDerivAt_rwb`,
  `hasDerivAt_rwDiv`, `flux_zero`, and the two *bounds* `|(rw)''| ≤ 6w²`, `|(rw/z)'| ≤ 3w²`
  which are what turn the identity into the coercive inequality (these are exactly the paper's
  "`|∂_R²(R²w²)| ≤ 6w²`, `|∂_R(Rw²)| ≤ 3w²`").
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.Spaces.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.ClassC

set_option autoImplicit false

/-! ## The radial weight and its derivative formulas -/

/-- `rw z = (1+z)^4/z^2`.  This is `(z·w(z))²`, with the singular factor `1/z^4` of `w²` split
off so that `rw z · (deriv a z)² = (z ∂_z a)² · w(z)²`. -/
def rw (z : ℝ) : ℝ := (1 + z) ^ 4 / z ^ 2

/-- The explicit formula for `d/dz rw` (with the junk value `0` at `z = 0`). -/
def rwb (z : ℝ) : ℝ := (1 + z) ^ 3 * (2 * z - 2) / z ^ 3

/-- The explicit formula for `d²/dz² rw`. -/
def rwbb (z : ℝ) : ℝ := (1 + z) ^ 2 * (2 * z ^ 2 - 4 * z + 6) / z ^ 4

/-- The explicit formula for `d/dz (rw z / z)`, i.e. for `d/dz (z w(z)²)`. -/
def rwc (z : ℝ) : ℝ := (1 + z) ^ 3 * (z - 3) / z ^ 4

/-- The boundary term of the integration by parts:
`flux α a z = α² rw z (∂_z a) a - (α²/2) rwb z a² + (α(5+α)/2) (rw z / z) a²`. -/
def flux (α : ℝ) (a : ℝ → ℝ) : ℝ → ℝ :=
  fun z => α ^ 2 * (rw z * (deriv a z * a z)) - (α ^ 2 / 2) * (rwb z * (a z) ^ 2)
    + ((α * (5 + α)) / 2) * (rw z / z) * (a z) ^ 2

lemma rw_eq_w (z : ℝ) : rw z = (z * Work.Spaces.w z) ^ 2 := by
  rw [Work.Spaces.w, rw]
  field_simp

lemma rw_nonneg (z : ℝ) : 0 ≤ rw z := by
  rw [rw_eq_w]; exact sq_nonneg _

/-- `flux` vanishes at `z = 0` (all three coefficients are multiples of `z`-powers). -/
lemma flux_zero (α : ℝ) (a : ℝ → ℝ) : flux α a 0 = 0 := by
  simp [flux, rw, rwb]

/-! ## The derivative of the weight -/

lemma hasDerivAt_rw {z : ℝ} (hz : z ≠ 0) : HasDerivAt rw (rwb z) z := by
  have h12 := (hasDerivAt_id z).add_const (1:ℝ)
  have h34 := h12.pow 4
  have h := h34.div (hasDerivAt_pow 2 z) (pow_ne_zero 2 hz)
  convert h using 1
  · -- the function
    funext t
    simp only [Pi.div_apply, Pi.pow_apply, Pi.add_apply, id_eq]
    rw [show rw t = (1 + t) ^ 4 / t ^ 2 from rfl]
    ring_nf
  · -- the derivative value
    simp only [Pi.pow_apply, Pi.add_apply, Pi.mul_apply, id_eq]
    rw [show rwb z = (1 + z) ^ 3 * (2 * z - 2) / z ^ 3 from rfl]
    field_simp
    ring_nf

lemma hasDerivAt_rwb {z : ℝ} (hz : z ≠ 0) : HasDerivAt rwb (rwbb z) z := by
  have h12 : HasDerivAt (fun t : ℝ => t + 1) 1 z := (hasDerivAt_id z).add_const 1
  have h2 : HasDerivAt (fun t : ℝ => 2 * t - 2) 2 z := by
    have h := ((hasDerivAt_id z).const_mul (2:ℝ)).sub_const 2
    convert h using 1
    · funext x; simp
    · ring
  have hnum := (h12.pow 3).mul h2
  have h := hnum.div (hasDerivAt_pow 3 z) (pow_ne_zero 3 hz)
  convert h using 1
  · -- the function
    funext t
    simp only [Pi.div_apply, Pi.pow_apply, Pi.add_apply, Pi.mul_apply, Pi.sub_apply, id_eq]
    rw [show rwb t = (1 + t) ^ 3 * (2 * t - 2) / t ^ 3 from rfl]
    ring_nf
  · -- the derivative value
    simp only [Pi.pow_apply, Pi.mul_apply, Pi.sub_apply, Pi.add_apply, id_eq]
    rw [show rwbb z = (1 + z) ^ 2 * (2 * z ^ 2 - 4 * z + 6) / z ^ 4 from rfl]
    field_simp
    ring_nf

lemma hasDerivAt_rwDiv {z : ℝ} (hz : z ≠ 0) :
    HasDerivAt (fun t : ℝ => rw t / t) (rwc z) z := by
  have h := (hasDerivAt_rw hz).div (hasDerivAt_id z) hz
  convert h using 1
  · -- the function
    funext t
    simp only [Pi.div_apply, id_eq]
  · -- the derivative value
    simp only [Pi.div_apply, id_eq]
    rw [show rwc z = (1 + z) ^ 3 * (z - 3) / z ^ 4 from rfl,
      show rwb z = (1 + z) ^ 3 * (2 * z - 2) / z ^ 3 from rfl,
      show rw z = (1 + z) ^ 4 / z ^ 2 from rfl]
    field_simp
    ring_nf

/-! ## The two bounds that make the identity coercive -/

lemma abs_rwbb_le {z : ℝ} (hz : 0 < z) : |rwbb z| ≤ 6 * (Work.Spaces.w z) ^ 2 := by
  have hz4 : (0:ℝ) < z ^ 4 := by positivity
  have hpos : 0 ≤ (1 + z) ^ 2 * (2 * z ^ 2 - 4 * z + 6) :=
    mul_nonneg (sq_nonneg _) (by nlinarith [sq_nonneg (z - 1)])
  have hnum : (1 + z) ^ 2 * (2 * z ^ 2 - 4 * z + 6) ≤ 6 * (1 + z) ^ 4 := by
    have h1 : (0:ℝ) < 4 * z * (1 + z) ^ 2 * (z + 4) :=
      mul_pos (mul_pos (mul_pos (by norm_num) hz) (pow_pos (by linarith) 2)) (by linarith)
    nlinarith [h1]
  calc |rwbb z| = ((1 + z) ^ 2 * (2 * z ^ 2 - 4 * z + 6)) / z ^ 4 := by
        rw [rwbb, abs_div, abs_of_pos hz4, abs_of_nonneg hpos]
    _ ≤ 6 * (1 + z) ^ 4 / z ^ 4 := by gcongr
    _ = 6 * (Work.Spaces.w z) ^ 2 := by rw [Work.Spaces.w]; ring

lemma abs_rwc_le {z : ℝ} (hz : 0 < z) : |rwc z| ≤ 3 * (Work.Spaces.w z) ^ 2 := by
  have hz4 : (0:ℝ) < z ^ 4 := by positivity
  have h3 : |z - 3| ≤ 3 * (1 + z) := by
    rw [abs_le]
    constructor <;> linarith
  have hnum : |(1 + z) ^ 3 * (z - 3)| ≤ 3 * (1 + z) ^ 4 := by
    calc |(1 + z) ^ 3 * (z - 3)| = (1 + z) ^ 3 * |z - 3| := by
          rw [abs_mul, abs_of_nonneg (by positivity)]
      _ ≤ (1 + z) ^ 3 * (3 * (1 + z)) := by gcongr
      _ = 3 * (1 + z) ^ 4 := by ring
  calc |rwc z| = |(1 + z) ^ 3 * (z - 3)| / z ^ 4 := by
        rw [rwc, abs_div, abs_of_pos hz4]
    _ ≤ 3 * (1 + z) ^ 4 / z ^ 4 := by gcongr
    _ = 3 * (Work.Spaces.w z) ^ 2 := by rw [Work.Spaces.w]; ring

end Work.FTS.ClassC
