import Mathlib.Analysis.InnerProductSpace.PiL2
import Submission.Work.SmallBoxSliding.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SmallBoxSliding

/-- The complement of the good set is covered by the bad band and the far
set: if some coordinate of `w = (ℓd)•u` exceeds `A − μ^{-1/3}`
(`A = ½ℓ(1+d)`), then either it exceeds `A` itself (so `u ∈ farSet`), or all
coordinates stay `≤ A` and that coordinate exceeds `A − 2μ^{-1/3}`
(`u ∈ bandSet`, using `μ^{-1/3} ≥ 0`). -/
lemma goodSet_compl_subset {ℓ d μ : ℝ} (hμ : 0 < μ) :
    (Work.SmallBoxSliding.goodSet ℓ d μ)ᶜ ⊆
      Work.SmallBoxSliding.bandSet ℓ d μ ∪ Work.SmallBoxSliding.farSet ℓ d μ := by
  intro u hu
  rw [Set.mem_compl_iff] at hu
  rw [goodSet] at hu
  rw [Set.mem_ofPred_eq] at hu
  push Not at hu
  rw [Set.mem_union]
  simp only [bandSet, farSet, Set.mem_ofPred_eq]
  by_cases hfar : ∃ j : Fin 3, (1 / 2) * ℓ * (1 + d) < |((ℓ * d) • u).ofLp j|
  · exact Or.inr hfar
  · push Not at hfar
    obtain ⟨j, hj⟩ := hu
    refine Or.inl ⟨⟨j, ?_⟩, hfar⟩
    have hδ : 0 < μ ^ (-1 / 3 : ℝ) := Real.rpow_pos_of_pos hμ _
    linarith

end Work.SmallBoxSliding
