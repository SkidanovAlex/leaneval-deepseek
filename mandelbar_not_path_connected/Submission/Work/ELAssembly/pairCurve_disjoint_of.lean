import Mathlib
import Submission.Work.ELTop.Defs
import Submission.Work.ELTop.paramRay_disjoint
import Submission.Work.ELTop.landsN_mem_K
import Submission.Work.ELAssembly.pairCurve_disjoint_alpha

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.ELAssembly

/-- **Two co-landing pairs whose angular data differ by no integer and whose landing points
differ have disjoint curves.**  A common point `z` of the two curves either lies in `K c` — but
the rays lie in `K cᶜ`, so then `z = P.y = Q.y`, against `hy` — or lies outside `K c`, so it is a
common point of a ray of `P` and a ray of `Q`; then the two angles differ by an integer
(`exists_int_angle_eq_of_mem_paramRay_inter`), contradicting `haa`, `hab`, `hba`, `hbb`. -/
theorem pairCurve_disjoint_of {c : ℂ} {φ : ℂ → ℂ} (hN : Work.EL.DynB c φ)
    (P Q : Work.EL.CoPair hN)
    (haa : ∀ k : ℤ, Q.a ≠ P.a + k) (hab : ∀ k : ℤ, Q.b ≠ P.a + k)
    (hba : ∀ k : ℤ, Q.a ≠ P.b + k) (hbb : ∀ k : ℤ, Q.b ≠ P.b + k)
    (hy : P.y ≠ Q.y) :
    Disjoint (Work.EL.pairCurve P) (Work.EL.pairCurve Q) := by
  rw [Set.disjoint_iff]
  rintro z ⟨hz1, hz2⟩
  rw [Work.EL.mem_pairCurve_iff] at hz1 hz2
  have hPyK : P.y ∈ Work.EL.K c := Work.ELTop.landsN_mem_K hN P.lands_a
  have hQyK : Q.y ∈ Work.EL.K c := Work.ELTop.landsN_mem_K hN Q.lands_a
  by_cases hK : z ∈ Work.EL.K c
  · -- a common point inside `K c` is the landing point of each pair
    have hzP : z = P.y := by
      rcases hz1 with h | h | h
      · exact absurd hK ((Work.EL.paramRay_subset_compl hN P.a) h)
      · exact h
      · exact absurd hK ((Work.EL.paramRay_subset_compl hN P.b) h)
    have hzQ : z = Q.y := by
      rcases hz2 with h | h | h
      · exact absurd hK ((Work.EL.paramRay_subset_compl hN Q.a) h)
      · exact h
      · exact absurd hK ((Work.EL.paramRay_subset_compl hN Q.b) h)
    exact hy (hzP.symm.trans hzQ)
  · -- a common point outside `K c` is a common point of a ray of `P` and a ray of `Q`
    have hzPr : z ∈ Work.EL.paramRay hN P.a ∨ z ∈ Work.EL.paramRay hN P.b := by
      rcases hz1 with h | h | h
      · exact Or.inl h
      · exact absurd (h ▸ hPyK) hK
      · exact Or.inr h
    have hzQr : z ∈ Work.EL.paramRay hN Q.a ∨ z ∈ Work.EL.paramRay hN Q.b := by
      rcases hz2 with h | h | h
      · exact Or.inl h
      · exact absurd (h ▸ hQyK) hK
      · exact Or.inr h
    rcases hzPr with hPa | hPb <;> rcases hzQr with hQa | hQb
    · obtain ⟨k, hk⟩ := exists_int_angle_eq_of_mem_paramRay_inter hN hPa hQa
      exact haa k hk
    · obtain ⟨k, hk⟩ := exists_int_angle_eq_of_mem_paramRay_inter hN hPa hQb
      exact hab k hk
    · obtain ⟨k, hk⟩ := exists_int_angle_eq_of_mem_paramRay_inter hN hPb hQa
      exact hba k hk
    · obtain ⟨k, hk⟩ := exists_int_angle_eq_of_mem_paramRay_inter hN hPb hQb
      exact hbb k hk

end Work.ELAssembly
