import Mathlib
import Submission.Work.BW.aligned_defs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BW

/-- Lower bound for the product of modified heights over the complement of `J`: since every
factor `hmod (α i) (ℓ i)` is at least `1 / [K : ℚ]`, the product over the `m - J.card` indices
outside `J` dominates `(1 / [K : ℚ]) ^ (m - J.card)`. -/
lemma F_bound_Q_lower {K : Type*} [Field K] [NumberField K] {m : ℕ}
    (α : Fin m → K) (ℓ : Fin m → ℂ) (J : Finset (Fin m)) :
    (1 / (Module.finrank ℚ K : ℝ)) ^ (m - J.card) ≤
      ∏ i ∈ Finset.univ \ J, hmod (α i) (ℓ i) := by
  have hle : ∀ i, (1 : ℝ) / (Module.finrank ℚ K : ℝ) ≤ hmod (α i) (ℓ i) :=
    fun i => le_trans (le_max_right _ _) (le_max_right _ _)
  have hnn : (0 : ℝ) ≤ 1 / (Module.finrank ℚ K : ℝ) := by positivity
  calc (1 / (Module.finrank ℚ K : ℝ)) ^ (m - J.card)
      = (1 / (Module.finrank ℚ K : ℝ)) ^ ((Finset.univ \ J).card) := by
        congr 1
        rw [Finset.card_sdiff, Finset.card_univ, Fintype.card_fin,
          Finset.inter_eq_left.2 (Finset.subset_univ J)]
    _ = ∏ _i ∈ Finset.univ \ J, (1 / (Module.finrank ℚ K : ℝ)) := by
        rw [Finset.prod_const]
    _ ≤ ∏ i ∈ Finset.univ \ J, hmod (α i) (ℓ i) :=
        Finset.prod_le_prod₀ (fun i _ => hnn) (fun i _ => hle i)

end Work.BW
