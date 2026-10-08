import Mathlib
import Submission.Work.ThmG.Defs
import Submission.Work.CohApps.sum_irr_deg_sq_le_ker

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.ThmG

theorem sum_deg_sq_excludingKernel {G : Type} [Group G] [Fintype G] {H : Subgroup G}
    (Q₁ : Subgroup G) (hQ₁ : Q₁ ≤ H) (hN : (Q₁.subgroupOf H).Normal) :
    ∑ χ ∈ Submission.Blueprint.excludingKernel H Q₁, ((Work.CharCore.irrDeg χ : ℝ)) ^ 2
      = (Nat.card H : ℝ) - ((Q₁.subgroupOf H).index : ℝ) := by
  classical
  -- `Q₁ ≤ H` is part of the paper's setting; note that membership in `Q₁.subgroupOf H`
  -- below is literally membership in `Q₁`, so no further use of it is needed.
  have hQ₁' : ∀ x ∈ Q₁, x ∈ H := fun x hx => hQ₁ hx
  -- `𝒮 = excludingKernel H Q₁` is a filter of `Irr H` by the "non-trivial on `Q₁`" predicate.
  have hexcl : Submission.Blueprint.excludingKernel H Q₁
      = (Work.CharCore.Irr H).filter
          (fun χ => ∃ x : H, (x : G) ∈ Q₁ ∧ χ x ≠ χ 1) := rfl
  -- Its complement in `Irr H` is the set of characters whose kernel contains `Q₁`.
  have hcompl : (Work.CharCore.Irr H).filter
        (fun χ => ¬ ∃ x : H, (x : G) ∈ Q₁ ∧ χ x ≠ χ 1)
      = (Work.CharCore.Irr H).filter
          (fun χ => (Q₁.subgroupOf H : Set H) ⊆ Work.CharCore.charKernel χ) := by
    apply Finset.filter_congr
    intro χ _
    constructor
    · intro h x hx
      by_contra hne
      exact h ⟨x, (Subgroup.mem_subgroupOf.mp hx), hne⟩
    · rintro h ⟨x, hx, hne⟩
      exact hne (h (Subgroup.mem_subgroupOf.mpr hx))
  -- Split the sum over `Irr H` into the two complementary pieces.
  have hsplit := Finset.sum_filter_add_sum_filter_not (Work.CharCore.Irr H)
      (fun χ : H → ℂ => ∃ x : H, (x : G) ∈ Q₁ ∧ χ x ≠ χ 1)
      (fun χ => ((Work.CharCore.irrDeg χ : ℝ)) ^ 2)
  rw [hcompl] at hsplit
  -- The trivial-on-`Q₁` piece is `[H : Q₁]`, and the whole of `Irr H` sums to `|H|`.
  have hker := @Work.CohApps.sum_irr_deg_sq_le_ker H _ _ (Q₁.subgroupOf H) hN
  have hirr := Work.CohApps.real_sum_irr_deg_sq H
  rw [hker, hirr] at hsplit
  rw [hexcl, eq_sub_iff_add_eq]
  exact hsplit

end Work.ThmG
