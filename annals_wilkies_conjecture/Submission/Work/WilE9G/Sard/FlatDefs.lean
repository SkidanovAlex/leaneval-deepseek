import Mathlib
import Submission.Work.WilE9G.Sard.Basic

/-!
# Vocabulary for the analytic Sard theorem

`Work.WilE9G.Sard.sardAnalyticGeneral` : for a map `f : ℝⁿ → ℝᵐ` which is real analytic on an open
set `U`, the image of the critical set `{x | fderiv ℝ f x not surjective} ∩ U` is Lebesgue-null.

The proof runs by a double induction (on the target dimension `m`, and inside that on a measure
built from the source dimension `d` and a "flatness level" `j`).  The relevant objects are

* `flatSetV F j` — the points where all iterated derivatives of `F` of orders `1, …, j` vanish;
* `critSet F` — the points where the Fréchet derivative of `F` is not surjective;
* `flatCrit F j = flatSetV F (j-1) ∩ critSet F` — the set to which the recursion at level `j`
  applies.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace Work.WilE9G.Sard

open MeasureTheory

/-- The set of points at which all iterated derivatives of `F` of orders `1, …, j` vanish. -/
def flatSetV {d m : ℕ} (F : (Fin d → ℝ) → (Fin m → ℝ)) (j : ℕ) : Set (Fin d → ℝ) :=
  {x | ∀ i, 1 ≤ i → i ≤ j → iteratedFDeriv ℝ i F x = 0}

/-- The points of `flatSetV F (j-1)` at which `F` is critical. -/
def flatCrit {d m : ℕ} (F : (Fin d → ℝ) → (Fin m → ℝ)) (j : ℕ) : Set (Fin d → ℝ) :=
  flatSetV F (j - 1) ∩ critSet F

lemma mem_flatSetV {d m : ℕ} {F : (Fin d → ℝ) → (Fin m → ℝ)} {j : ℕ} {x : Fin d → ℝ} :
    x ∈ flatSetV F j ↔ ∀ i, 1 ≤ i → i ≤ j → iteratedFDeriv ℝ i F x = 0 := Iff.rfl

lemma mem_flatCrit {d m : ℕ} {F : (Fin d → ℝ) → (Fin m → ℝ)} {j : ℕ} {x : Fin d → ℝ} :
    x ∈ flatCrit F j ↔
      (∀ i, 1 ≤ i → i ≤ j - 1 → iteratedFDeriv ℝ i F x = 0) ∧
        ¬ Function.Surjective (fderiv ℝ F x) := Iff.rfl

/-- `flatSetV F 0` is everything. -/
lemma flatSetV_zero {d m : ℕ} (F : (Fin d → ℝ) → (Fin m → ℝ)) : flatSetV F 0 = Set.univ := by
  ext x
  simp only [mem_flatSetV, Set.mem_univ, iff_true]
  intro i hi hi'
  exact absurd (le_trans hi hi') (Nat.not_succ_le_zero 0)

lemma flatSetV_antitone {d m : ℕ} (F : (Fin d → ℝ) → (Fin m → ℝ)) :
    Antitone (flatSetV F) := fun _a _b hab x hx i hi hib => hx i hi (le_trans hib hab)

lemma flatCrit_subset_critSet {d m : ℕ} (F : (Fin d → ℝ) → (Fin m → ℝ)) (j : ℕ) :
    flatCrit F j ⊆ critSet F := Set.inter_subset_right

lemma flatCrit_subset_flatSetV {d m : ℕ} (F : (Fin d → ℝ) → (Fin m → ℝ)) (j : ℕ) :
    flatCrit F j ⊆ flatSetV F (j - 1) := Set.inter_subset_left

/-- If the Fréchet derivative vanishes then so does the first iterated derivative. -/
lemma iteratedFDeriv_one_eq_zero_of_fderiv_eq_zero {d m : ℕ} {F : (Fin d → ℝ) → (Fin m → ℝ)}
    {x : Fin d → ℝ} (h : fderiv ℝ F x = 0) : iteratedFDeriv ℝ 1 F x = 0 := by
  ext mm
  rw [iteratedFDeriv_one_apply]
  simp [h]

/-- For a continuous linear endomorphism of `ℝⁿ`, non-surjectivity forces the determinant to
vanish. -/
theorem det_eq_zero_of_not_surjective {n : ℕ} (A : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ))
    (hA : ¬ Function.Surjective A) : A.det = 0 := by
  by_contra h
  have hker : LinearMap.ker A.toLinearMap = ⊥ := by
    by_contra hk
    exact h ((LinearMap.det_eq_zero_iff_ker_ne_bot (f := A.toLinearMap)).mpr hk)
  have hinj : Function.Injective A.toLinearMap := LinearMap.ker_eq_bot.mp hker
  have hsurj : Function.Surjective A.toLinearMap :=
    LinearMap.injective_iff_surjective.mp hinj
  exact hA fun y => hsurj y

end Work.WilE9G.Sard
