import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Submission.Work.BoseBox.Fock
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBox.pairBogolubov_identity` — the Bogoliubov operator identity on one
mode pair (FS `eq:BogIdentity`, `κ = 0`)

This module proves `PairBogIdentity m` (`Submission/Work/BoseBox/Fock.lean`):

for `A > 0`, `|B| ≤ A` and two *distinct* modes `i ≠ j`,

  `A(aᵢ†aᵢ + aⱼ†aⱼ) + B(aᵢ†aⱼ† + aᵢaⱼ) = D(b₊†b₊ + b₋†b₋) − (A−s)·1`,

with `s = √(A²−B²)`, `D = (A+s)/2`, `α = B/(A+s)`, `b₊ = aᵢ + α aⱼ†`,
`b₋ = aⱼ + α aᵢ†`.  This is the algebraic heart of FS `thm:BogHamDiag`.

The proof has two independent halves.

* **The operator algebra** (Bargmann–Segal model `aᵢ = ∂/∂xᵢ`, `aᵢ† = xᵢ`): the
  canonical commutation relation `aᵢaᵢ† = aᵢ†aᵢ + 1` (`ann_cre_self`), the
  commutativity of the derivatives `aᵢaⱼ = aⱼaᵢ` (`ann_ann_comm`) and of the
  multiplications `aᵢ†aⱼ† = aⱼ†aᵢ†` (`cre_cre_comm`).  Expanding the two
  squeezed products with these gives
  `b₊†b₊ + b₋†b₋ = (1+α²)(nᵢ+nⱼ) + 2α(aᵢ†aⱼ† + aᵢaⱼ) + 2α²·1`.
* **The scalar diagonalisation arithmetic** (from `Submission/Bog2Mode.lean`):
  `D(1+α²) = A`, `2Dα = B` and `2Dα² = A − s`.

The only point that is not pure `ring`/`module` bookkeeping is `ann_ann_comm`:
Mathlib has no commutation of iterated `MvPolynomial.pderiv`s, so it is proved
here by induction on the polynomial (`pderiv` of a variable is constant).
-/

noncomputable section

open scoped BigOperators

namespace Work.BoseBox

open _root_.BoseGases
open Submission.BoseGases

set_option autoImplicit false

/-! ## 1. The model-level commutation relations -/

/-- `aᵢ aⱼ = aⱼ aᵢ`: formal partial derivatives commute.  Mathlib does not have
commutation of iterated `MvPolynomial.pderiv`s, so this is proved by induction
on the polynomial; the only non-formal input is `pderiv` of a variable, which is
a constant. -/
private lemma pderiv_pderiv_comm {m : ℕ} (i j : Fin m) (p : Fock m) :
    MvPolynomial.pderiv i (MvPolynomial.pderiv j p) =
      MvPolynomial.pderiv j (MvPolynomial.pderiv i p) := by
  induction p using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p n hp =>
      have h2 : MvPolynomial.pderiv i
          (MvPolynomial.pderiv j (MvPolynomial.X n : Fock m)) = 0 := by
        rcases eq_or_ne n j with h | h
        · subst h; simp
        · rw [MvPolynomial.pderiv_X_of_ne h]; simp
      have h3 : MvPolynomial.pderiv j
          (MvPolynomial.pderiv i (MvPolynomial.X n : Fock m)) = 0 := by
        rcases eq_or_ne n i with h | h
        · subst h; simp
        · rw [MvPolynomial.pderiv_X_of_ne h]; simp
      simp only [MvPolynomial.pderiv_mul, map_add, hp, h2, h3]
      ring

/-- Annihilation operators of different modes commute: `aᵢ aⱼ = aⱼ aᵢ`. -/
private lemma ann_ann_comm {m : ℕ} (i j : Fin m) : ann i ∘ₗ ann j = ann j ∘ₗ ann i := by
  refine LinearMap.ext fun p => ?_
  simpa only [LinearMap.comp_apply, ann_apply] using pderiv_pderiv_comm i j p

/-- Creation operators of different modes commute: `aᵢ† aⱼ† = aⱼ† aᵢ†`. -/
private lemma cre_cre_comm {m : ℕ} (i j : Fin m) : cre i ∘ₗ cre j = cre j ∘ₗ cre i := by
  refine LinearMap.ext fun p => ?_
  simp only [LinearMap.comp_apply, cre_apply]
  ring

/-- The canonical commutation relation `aᵢ aᵢ† = aᵢ† aᵢ + 1`. -/
private lemma ann_cre_self {m : ℕ} (i : Fin m) : ann i ∘ₗ cre i = cre i ∘ₗ ann i + 1 := by
  refine LinearMap.ext fun p => ?_
  simp only [LinearMap.comp_apply, LinearMap.add_apply, ann_apply, cre_apply]
  rw [MvPolynomial.pderiv_mul, MvPolynomial.pderiv_X_self, one_mul]
  simp [add_comm]

/-! ## 2. The two squeezed products -/

/-- `b₊†b₊ = nᵢ + α(aᵢ†aⱼ† + aᵢaⱼ) + α²(nⱼ + 1)`. -/
private lemma bPlus_comp {m : ℕ} (i j : Fin m) (α : ℝ) :
    bPlusDag i j α ∘ₗ bPlus i j α
      = numOp i + α • (cre i ∘ₗ cre j + ann i ∘ₗ ann j) + α ^ 2 • (numOp j + 1) := by
  simp only [bPlusDag, bPlus, numOp, LinearMap.add_comp, LinearMap.comp_add,
    LinearMap.smul_comp, LinearMap.comp_smul]
  rw [ann_ann_comm j i, ann_cre_self j]
  module

/-- `b₋†b₋ = nⱼ + α(aᵢ†aⱼ† + aᵢaⱼ) + α²(nᵢ + 1)`. -/
private lemma bMinus_comp {m : ℕ} (i j : Fin m) (α : ℝ) :
    bMinusDag i j α ∘ₗ bMinus i j α
      = numOp j + α • (cre i ∘ₗ cre j + ann i ∘ₗ ann j) + α ^ 2 • (numOp i + 1) := by
  simp only [bMinusDag, bMinus, numOp, LinearMap.add_comp, LinearMap.comp_add,
    LinearMap.smul_comp, LinearMap.comp_smul]
  rw [cre_cre_comm j i, ann_cre_self i]
  module

/-- The sum of the two squeezed products is the quadratic operator whose
diagonalisation is the content of the identity. -/
private lemma pairBog_squeeze_sum {m : ℕ} (i j : Fin m) (α : ℝ) :
    bPlusDag i j α ∘ₗ bPlus i j α + bMinusDag i j α ∘ₗ bMinus i j α
      = (1 + α ^ 2) • (numOp i + numOp j)
        + (2 * α) • (cre i ∘ₗ cre j + ann i ∘ₗ ann j)
        + (2 * α ^ 2) • (1 : Fock m →ₗ[ℝ] Fock m) := by
  rw [bPlus_comp i j α, bMinus_comp i j α]
  module

/-! ## 3. The scalar diagonalisation coefficients -/

/-- `2Dα = B`. -/
private lemma two_bogD_mul_bogAlpha {A B : ℝ} (hA : 0 < A) (hB : |B| ≤ A) :
    bogD A B * (2 * bogAlpha A B) = B := by
  nlinarith [bog_alpha_mul_D hA hB]

/-- `2Dα² = A − s`, the cancellation of the constant term. -/
private lemma two_bogD_mul_bogAlpha_sq {A B : ℝ} (hA : 0 < A) (hB : |B| ≤ A) :
    bogD A B * (2 * bogAlpha A B ^ 2) = A - bogS A B := by
  have hαD : bogAlpha A B * bogD A B = B / 2 := bog_alpha_mul_D hA hB
  have key : bogD A B * (2 * bogAlpha A B ^ 2) = bogAlpha A B * B := by
    linear_combination (2 * bogAlpha A B) * hαD
  rw [key, bog_A_sub_s_eq hA hB, bogAlpha, div_mul_eq_mul_div, pow_two]

/-! ## 4. The identity -/

/-- **The Bogoliubov operator identity on one mode pair** (FS `eq:BogIdentity`
with `κ = 0`), see `Work.BoseBox.PairBogIdentity`. -/
theorem pairBogolubov_identity (m : ℕ) : Work.BoseBox.PairBogIdentity m := by
  intro i j _hij A B hA hB
  unfold pairBogForm pairBogDiag
  have h1 : bogD A B * (1 + bogAlpha A B ^ 2) = A := bog_D_mul_one_add_alpha_sq hA hB
  have h2 : bogD A B * (2 * bogAlpha A B) = B := two_bogD_mul_bogAlpha hA hB
  have h3 : bogD A B * (2 * bogAlpha A B ^ 2) = A - bogS A B :=
    two_bogD_mul_bogAlpha_sq hA hB
  rw [pairBog_squeeze_sum]
  simp only [smul_add, smul_smul]
  rw [h1, h2, h3]
  module

end Work.BoseBox
