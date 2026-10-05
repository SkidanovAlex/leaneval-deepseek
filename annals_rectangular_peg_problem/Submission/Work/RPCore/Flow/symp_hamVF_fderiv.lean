import Mathlib
import Submission.Work.RPCore.Defs

/-!
# The linearisation of the Hamiltonian vector field is skew with respect to `ω`

For a Hamiltonian `H : PS → ℝ` of class `C²` we show that the Fréchet derivative of the
Hamiltonian vector field `hamVF H` at any point `y` is *skew-adjoint* for the symplectic form
`symp = dp₁∧dq₁ + dp₂∧dq₂`, namely

`symp (fderiv ℝ (hamVF H) y u) w + symp u (fderiv ℝ (hamVF H) y w) = 0`.

The proof is coordinate-free and rests on two facts:

* `hamVF H = Jf ∘ fderiv ℝ H`, where `Jf` is the fixed linear "musical" map sending a
  covector `φ` to the vector `((φ e₃, φ e₄), (-φ e₁, -φ e₂))`; and
* `symp (Jf φ) w = - φ w` for every covector `φ` and vector `w`.

Hence `fderiv ℝ (hamVF H) y = Jf ∘ S` with `S = fderiv ℝ (fderiv ℝ H) y` the (bilinear)
second derivative of `H`, which is symmetric by `ContDiffAt.isSymmSndFDerivAt`.  Expanding
`symp (Jf (S u)) w = -(S u) w` and `symp u (Jf (S w)) = (S w) u` (the second via
antisymmetry of `symp`) the claim becomes `-(S u w) + (S w u) = 0`, which is exactly the
symmetry of `S`.
-/

namespace Work.RPCore.Flow

open Work.RPV

set_option autoImplicit false

noncomputable section

/-- First coordinate direction `∂/∂q₁` of `PS = T^*ℝ²`. -/
def sympE1 : PS := ((1, 0), (0, 0))

/-- Second coordinate direction `∂/∂q₂` of `PS = T^*ℝ²`. -/
def sympE2 : PS := ((0, 1), (0, 0))

/-- Third coordinate direction `∂/∂p₁` of `PS = T^*ℝ²`. -/
def sympE3 : PS := ((0, 0), (1, 0))

/-- Fourth coordinate direction `∂/∂p₂` of `PS = T^*ℝ²`. -/
def sympE4 : PS := ((0, 0), (0, 1))

/-- The "musical" linear map `Jf` turning a covector `φ` into the vector
`((φ e₃, φ e₄), (-φ e₁, -φ e₂))`.  It is designed so that `hamVF H x = Jf (fderiv ℝ H x)`. -/
def sympJ : (PS →L[ℝ] ℝ) →L[ℝ] PS :=
  ((ContinuousLinearMap.apply ℝ ℝ sympE3).prod (ContinuousLinearMap.apply ℝ ℝ sympE4)).prod
    ((-(ContinuousLinearMap.apply ℝ ℝ sympE1)).prod
      (-(ContinuousLinearMap.apply ℝ ℝ sympE2)))

/-- `hamVF` is `sympJ` composed with the derivative of `H`. -/
theorem hamVF_eq_sympJ (H : PS → ℝ) : hamVF H = fun x => sympJ (fderiv ℝ H x) := by
  funext x
  simp only [sympJ, hamVF, ContinuousLinearMap.prod_apply, neg_apply,
    ContinuousLinearMap.apply_apply, sympE1, sympE2, sympE3, sympE4]

/-- Decomposition of a point of `PS` in the coordinate basis. -/
theorem PS_decomp (w : PS) :
    w = w.1.1 • sympE1 + w.1.2 • sympE2 + w.2.1 • sympE3 + w.2.2 • sympE4 := by
  simp only [sympE1, sympE2, sympE3, sympE4]
  ext <;> simp

/-- Evaluation of an element of the dual of `PS` in coordinates. -/
theorem clm_apply_decomp (φ : PS →L[ℝ] ℝ) (w : PS) :
    φ w = w.1.1 * φ sympE1 + w.1.2 * φ sympE2 + w.2.1 * φ sympE3 + w.2.2 * φ sympE4 := by
  conv_lhs => rw [PS_decomp w]
  simp [map_add, map_smul]

/-- The defining identity of the musical map: `symp (Jf φ) w = - φ w`. -/
theorem symp_sympJ (φ : PS →L[ℝ] ℝ) (w : PS) : symp (sympJ φ) w = - φ w := by
  rw [clm_apply_decomp φ w]
  simp only [sympJ, symp, ContinuousLinearMap.prod_apply, neg_apply,
    ContinuousLinearMap.apply_apply, sympE1, sympE2, sympE3, sympE4]
  ring

/-- `symp` is antisymmetric. -/
theorem symp_antisym (a b : PS) : symp a b = - symp b a := by
  simp only [symp]; ring

theorem symp_hamVF_fderiv (H : Work.RPV.PS → ℝ) (hH : ContDiff ℝ 2 H) (y : Work.RPV.PS)
    (u w : Work.RPV.PS) :
    Work.RPV.symp (fderiv ℝ (Work.RPV.hamVF H) y u) w
      + Work.RPV.symp u (fderiv ℝ (Work.RPV.hamVF H) y w) = 0 := by
  -- The second derivative of `H` at `y`.
  set S : PS →L[ℝ] (PS →L[ℝ] ℝ) := fderiv ℝ (fderiv ℝ H) y with hS
  -- Its derivative is `sympJ ∘ S`.
  have hderiv : fderiv ℝ (hamVF H) y = sympJ.comp S := by
    rw [hamVF_eq_sympJ H]
    have hA : HasFDerivAt (fderiv ℝ H) S y := by
      have hd : DifferentiableAt ℝ (fderiv ℝ H) y :=
        (hH.contDiffAt.fderiv_right (m := 1) (by norm_num)).differentiableAt (by simp)
      simpa [hS] using hd.hasFDerivAt
    exact (sympJ.hasFDerivAt.comp y hA).fderiv
  -- `S` is symmetric (Clairaut/Schwarz).
  have hsymm : ∀ v w : PS, (S v) w = (S w) v := by
    intro v w
    exact (hH.contDiffAt.isSymmSndFDerivAt (by simp)).eq v w
  have h1 : fderiv ℝ (hamVF H) y u = sympJ (S u) := by
    rw [hderiv]; rfl
  have h2 : fderiv ℝ (hamVF H) y w = sympJ (S w) := by
    rw [hderiv]; rfl
  rw [h1, h2, symp_sympJ (S u) w]
  have h3 : symp u (sympJ (S w)) = (S w) u := by
    rw [symp_antisym u (sympJ (S w)), symp_sympJ (S w) u]
    ring
  rw [h3, hsymm w u]
  ring

end

end Work.RPCore.Flow
