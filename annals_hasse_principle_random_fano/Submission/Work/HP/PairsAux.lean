import Mathlib
import Submission.Work.HP.Defs
import Submission.Work.HP.rk_le_card

/-!
# Auxiliary definitions and lemmas for N05 `pair_counts`

This file holds the definitions shared with the delegated lemmas of N05
(`pair_counts`), plus a few elementary facts.  It is imported by
`Submission.Work.HP.pair_counts` and by the child lemmas.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

namespace Work.HP

open Filter

variable {ι : Type*} [Fintype ι]

/-- An integral lattice `L ⊆ ℤ^ι` is *primitive* (= saturated, pure) if it is not
properly contained in another integral lattice of the same rank, equivalently if
`ℤ^ι / L` is torsion free, equivalently `ℤ^ι ∩ span_ℝ(L) = L`.  We use the purity
formulation: `m • v ∈ L` with `m ≠ 0` forces `v ∈ L`. -/
def IsPrimLat (L : Submodule ℤ (ι → ℤ)) : Prop :=
  ∀ (v : ι → ℤ) (m : ℤ), m ≠ 0 → m • v ∈ L → v ∈ L

lemma isPrimLat_top : IsPrimLat (⊤ : Submodule ℤ (ι → ℤ)) := fun _ _ _ _ => trivial

lemma isPrimLat_bot : IsPrimLat (⊥ : Submodule ℤ (ι → ℤ)) := by
  intro v m hm hv
  rw [Submodule.mem_bot] at hv ⊢
  funext i
  have h : m * v i = 0 := by simpa using congrFun hv i
  exact (mul_eq_zero.mp h).resolve_left hm

/-- A nonzero vector of `ℤ^ι` has Euclidean norm at least `1`. -/
lemma one_le_eNorm_of_ne_zero {v : ι → ℤ} (hv : v ≠ 0) : 1 ≤ eNorm v := by
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hv
  have hiz : v i ≠ 0 := by simpa using hi
  have hge : (1 : ℤ) ≤ |v i| := by
    have := abs_pos.mpr hiz; omega
  have hge' : (1 : ℝ) ≤ |((v i : ℤ) : ℝ)| := by exact_mod_cast hge
  have hsq : (1 : ℝ) ≤ ((v i : ℝ)) ^ 2 := by
    rw [← sq_abs]; nlinarith [abs_nonneg ((v i : ℤ) : ℝ)]
  have h2 : ((v i : ℝ)) ^ 2 ≤ ∑ j, ((v j : ℝ)) ^ 2 :=
    Finset.single_le_sum (fun j _ => sq_nonneg (v j : ℝ)) (Finset.mem_univ i)
  have := Real.one_le_sqrt.mpr (le_trans hsq h2)
  simpa [eNorm] using this


/-- The dyadic window exponent of the `(j+1)`-st successive minimum of `L`: the least
integer `k` with `λ_{j+1}(L) ≤ 2^k`, rendered as `⌈log₂ λ_{j+1}(L)⌉`.  Used to group
lattices into dyadic windows. -/
def kwin (r : ℕ) (L : Submodule ℤ (ι → ℤ)) (j : Fin r) : ℕ :=
  ⌈Real.logb 2 (lam L (j.1 + 1))⌉₊

end Work.HP
