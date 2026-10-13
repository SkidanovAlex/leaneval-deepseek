/-
Copyright: work module for the Elgindi finite-time singularity project.

# Vocabulary for the radial AM–GM estimate `HkNorm_Dz_amgm`

The target of this little chapter is

`Work.FTS.EllipticEst.HkNorm_Dz_amgm`:

there is a universal `C` such that for every `0 < α ≤ 1`, every `f` smooth on the open
quadrant and in `ℋ^k` whose second radial derivative `z²∂_z²f` is also in `ℋ^k`,

`α · |D_z f|_{H^k} ≤ C (|f|_{H^k} + α² |z²∂_z²f|_{H^k})`   and   `D_z f ∈ ℋ^k`.

The proof is a *sliced* one-dimensional Agmon–Nirenberg interpolation: at every frozen angle
`θ` one applies the weighted `L²` interpolation for `D_z = z∂_z` (the analytic core
`Work.FTS.EllipticEst.DzAmgm.rDz_amgm_lintegral`) to the `z`-slice `z ↦ D_z^m D_θ^i f (z,θ)`,
using that `z²∂_z²` commutes with `D_z` and with `D_θ` (`.../DzAmgm/ZsqComm.lean`), and then
integrates over `θ`.  This module collects the bookkeeping vocabulary of that reduction, so
that the analytic lemmas can be stated without reference to the sum decomposition of
`HkIntegrand`.

* `angZ θ = sin(2θ)^{-η/2}` is the angular factor of the *pure* (`D_z`-) summands of
  `HkIntegrand α k f`, so that `(D_z^m f · w/sin(2θ)^{η/2})² = (D_z^m f · w · angZ θ)²`
  on `Iθ`;
* `zsqPz2 f = z² ∂_z² f` is the second radial derivative appearing in the hypotheses;
* `TZ f m` is the honest (iterated `lintegral`) `L²·L²` size of the `m`-th pure summand;
* `TM α f i j` is the honest size of the mixed summand `D_z^j D_θ^i f · Wt`;
* `LkSq α k f` is the honest (`lintegral`) version of `HkSq α k f`, i.e. the nested
  `lintegral` of `ENNReal.ofReal (HkIntegrand α k f ·)`.

Everything here is `sorry`-free and rests on `[propext, Classical.choice, Quot.sound]`.
-/
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.EllipticEst.OpenQDefs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology ENNReal
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.DzAmgm

set_option autoImplicit false

/-! ## The angular weights -/

/-- The angular weight `sin(2θ)^{-η/2}` of the *pure* (`D_z`-) summands of `HkIntegrand`:
`(w z / sin(2θ)^{η/2}) = w z · angZ θ` on the quadrant. -/
def angZ (θ : ℝ) : ℝ := (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta / 2))

/-- The angular weight `sin(2θ)^{-γ/2}` of the *mixed* summands: `Wt α z θ = w z · angM α θ`. -/
def angM (α θ : ℝ) : ℝ := (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α / 2))

/-- The second radial derivative `z² ∂_z² f` appearing in the hypotheses of `HkNorm_Dz_amgm`. -/
def zsqPz2 (f : ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ := fun z θ => z ^ 2 * Work.Spaces.pzIter 2 f z θ

/-! ## The term functionals -/

/-- The honest `L²·L²` size of the `m`-th pure summand `D_z^m f · w · angZ` of `HkIntegrand`.
Written as a nested `lintegral` over `Iθ × Iz`, angular variable first (the order in which the
sliced interpolation is applied). -/
def TZ (f : ℝ → ℝ → ℝ) (m : ℕ) : ℝ≥0∞ :=
  ∫⁻ θ in Work.Spaces.Iθ, ∫⁻ z in Work.Spaces.Iz,
    ENNReal.ofReal ((Work.Spaces.DzIter m f z θ * Work.Spaces.w z * angZ θ) ^ 2)

/-- The honest `L²·L²` size of the mixed summand `D_z^j D_θ^i f · Wt α`. -/
def TM (α : ℝ) (f : ℝ → ℝ → ℝ) (i j : ℕ) : ℝ≥0∞ :=
  ∫⁻ θ in Work.Spaces.Iθ, ∫⁻ z in Work.Spaces.Iz,
    ENNReal.ofReal ((Work.Spaces.mixed j i f z θ * Work.Spaces.Wt α z θ) ^ 2)

/-- The honest (`lintegral`) version of `HkSq α k f`: the nested `lintegral` of
`ENNReal.ofReal (HkIntegrand α k f ·)`, angular variable first. -/
def LkSq (α : ℝ) (k : ℕ) (f : ℝ → ℝ → ℝ) : ℝ≥0∞ :=
  ∫⁻ θ in Work.Spaces.Iθ, ∫⁻ z in Work.Spaces.Iz,
    ENNReal.ofReal (Work.Spaces.HkIntegrand α k f z θ)

/-! ## Elementary properties -/

/-- On the angular interval the pure angular weight is nonnegative. -/
theorem angZ_nonneg_of_mem {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) : 0 ≤ angZ θ := by
  rw [Work.Spaces.Iθ, Set.mem_Icc] at hθ
  exact Real.rpow_nonneg
    (Real.sin_nonneg_of_mem_Icc ⟨by linarith [hθ.1], by linarith [hθ.2, Real.pi_pos]⟩) _

/-- On the angular interval the mixed angular weight is nonnegative. -/
theorem angM_nonneg_of_mem {α θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) : 0 ≤ angM α θ := by
  rw [Work.Spaces.Iθ, Set.mem_Icc] at hθ
  exact Real.rpow_nonneg
    (Real.sin_nonneg_of_mem_Icc ⟨by linarith [hθ.1], by linarith [hθ.2, Real.pi_pos]⟩) _

/-- On the angular interval the product `w z · angZ θ` is nonnegative. -/
theorem w_mul_angZ_nonneg_of_mem {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) (z : ℝ) :
    0 ≤ Work.Spaces.w z * angZ θ :=
  mul_nonneg (by rw [Work.Spaces.w]; positivity) (angZ_nonneg_of_mem hθ)

/-- `TM` is monotone in the size of the mixed summand (a.e. version used by the assembly). -/
theorem TM_ofReal_sq_le {α : ℝ} {f : ℝ → ℝ → ℝ} {i j : ℕ} {θ z : ℝ}
    {c : ℝ} (hc : 0 ≤ c) (h : |Work.Spaces.mixed j i f z θ * Work.Spaces.Wt α z θ| ≤ c) :
    ENNReal.ofReal ((Work.Spaces.mixed j i f z θ * Work.Spaces.Wt α z θ) ^ 2)
      ≤ ENNReal.ofReal (c ^ 2) :=
  ENNReal.ofReal_le_ofReal (by
    set x := Work.Spaces.mixed j i f z θ * Work.Spaces.Wt α z θ with hx
    obtain ⟨h1, h2⟩ := abs_le.mp h
    nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ c - x) (by linarith : (0 : ℝ) ≤ c + x)])

end Work.FTS.EllipticEst.DzAmgm
