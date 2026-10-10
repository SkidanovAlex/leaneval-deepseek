import Mathlib.FieldTheory.Normal.Defs
import Submission.Work.CohomologicalShrinking.Semidirect
import Submission.Work.ProP.API
import Submission.Work.ProP.exists_freePQuotientAction
import Submission.Work.ProP.exists_surjective_freePQuotient_equivariant
import Submission.Work.Shrinking.finite_freeGroup_quotient_pCentralSeries
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.CohomologicalShrinking.flow

/-! ## Finiteness of the refined graded pieces

The graded piece `P_{(i,j)}/P_{(i,j)+1}` of Schmidt–Wingberg's refinement of the descending
`p`-central series (`refinedQuotient`) is finite whenever `P` is a finitely generated free
group.  We prove this for the discrete model `Work.Shrinking.freeOperatorGroup G m` of the
free `G`-operator group of rank `m` (`G` finite), so that the `𝔽_p`-vector spaces `E p G m i j`
of the chapter are finite-dimensional.

The argument is a subquotient argument.  Writing `A = P_{(i,j)}` and
`B = P_{(i,j)+1}`, both `A` and `B` lie between `P_{i+1}` and `P_i`; the piece `A/B` is a
quotient of `A/(A ∩ P_{i+1})`, which is a subgroup of the finite quotient `P_i/P_{i+1}`.
Since `P = FreeGroup (Fin m × G)` is free on a finite generating set, the quotients
`P/P_k` are finite (`Work.Shrinking.finite_freeGroup_quotient_pCentralSeries`). -/

/-- Auxiliary subquotient lemma: if `N ≤ B` are subgroups of a group `P` with `N` and `B`
normal in `P`, and the quotient `P ⧸ N` is finite, then the subquotient `A ⧸ (B ∩ A)` is
finite for every subgroup `A ≤ P` containing `B`.

Indeed `A ⧸ (N ∩ A)` is a subgroup of `P ⧸ N` (it embeds as the range of the composite
`A ↪ P → P ⧸ N`, whose kernel is `N ∩ A`), hence finite, and `A ⧸ (B ∩ A)` is a quotient of
`A ⧸ (N ∩ A)` because `N ≤ B`. -/
theorem finite_quotient_subgroupOf_of_finite_quotient {P : Type*} [Group P]
    {N B A : Subgroup P} [N.Normal] [B.Normal] (hNB : N ≤ B)
    [Finite (P ⧸ N)] : Finite (A ⧸ B.subgroupOf A) := by
  -- `A ⧸ (N ∩ A)` embeds into `P ⧸ N` via the first isomorphism theorem
  have hfin : Finite (A ⧸ N.subgroupOf A) := by
    have hker : ((QuotientGroup.mk' N).comp A.subtype).ker = N.subgroupOf A := by
      ext x : 1
      simp only [MonoidHom.mem_ker, MonoidHom.comp_apply, Subgroup.mem_subgroupOf,
        QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
      exact Iff.rfl
    rw [← hker]
    exact Finite.of_injective (QuotientGroup.quotientKerEquivRange _).toFun
      (QuotientGroup.quotientKerEquivRange _).injective
  haveI := hfin
  -- `A ⧸ (B ∩ A)` is a quotient of `A ⧸ (N ∩ A)`
  exact Finite.of_surjective
    (QuotientGroup.lift (N.subgroupOf A) (QuotientGroup.mk' (B.subgroupOf A))
      (by rw [QuotientGroup.ker_mk']; exact Subgroup.subgroupOf_mono A hNB))
    (by
      intro y
      obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (B.subgroupOf A) y
      exact ⟨QuotientGroup.mk' (N.subgroupOf A) x, by
        simp only [QuotientGroup.mk'_apply, QuotientGroup.lift_mk']⟩)

/-- Every term `P_{(i,j)}` of the refinement is a normal subgroup (it is built from the
`p`-central series and the descending central series, both of which are normal). -/
instance refinedTerm_instNormal (p : ℕ) (P : Type*) [Group P] (i j : ℕ) :
    (refinedTerm p P i j).Normal := by
  unfold refinedTerm
  infer_instance

/-- The next term of the refinement always contains `P_{i+1}`, i.e.
`P_{i+1} ≤ P_{(i,j)+1}` for all `i, j`. -/
theorem pSeries_succ_le_refinedTerm_tauSucc (p : ℕ) (P : Type*) [Group P] (i j : ℕ) :
    pSeries p P (i + 1) ≤ refinedTerm p P (tauSucc i j).1 (tauSucc i j).2 := by
  by_cases hji : j < i
  · rw [tauSucc_of_lt hji]
    exact le_sup_right
  · rw [tauSucc_of_le (Nat.le_of_not_lt hji), refinedTerm_one]

/-- The graded piece `P_{(i,j)}/P_{(i,j)+1}` of the refined `p`-central filtration of a free
`G`-operator group of finite rank is finite. -/
theorem finite_refinedQuotient (p : ℕ) [Fact p.Prime] (G : Type*) [Group G] [Fintype G]
    (m i j : ℕ) : Finite (refinedQuotient p (Work.Shrinking.freeOperatorGroup G m) i j) := by
  have hNB := pSeries_succ_le_refinedTerm_tauSucc p (Work.Shrinking.freeOperatorGroup G m) i j
  haveI hfin : Finite (Work.Shrinking.freeOperatorGroup G m ⧸
      pSeries p (Work.Shrinking.freeOperatorGroup G m) (i + 1)) :=
    Work.Shrinking.finite_freeGroup_quotient_pCentralSeries p (Fin m × G) i
  exact finite_quotient_subgroupOf_of_finite_quotient
    (N := pSeries p (Work.Shrinking.freeOperatorGroup G m) (i + 1)) hNB

end Work.CohomologicalShrinking.flow
