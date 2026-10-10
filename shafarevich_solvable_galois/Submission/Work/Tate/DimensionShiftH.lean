import Mathlib.Order.CompletePartialOrder
import Mathlib.Data.Fintype.Defs
import Mathlib.GroupTheory.QuotientGroup.Defs
import Mathlib.Algebra.Group.Subgroup.Basic
import Mathlib.Algebra.GroupWithZero.Action.Defs
import Submission.Work.Tate.CoindUp
import Submission.Work.Tate.ker_delta0_eq_range_H0g
import Submission.Work.Tate.ker_deltaH1_eq_range_mapH1
import Submission.Work.Tate.range_delta0_eq_ker_mapH1
import Submission.Work.Tate.range_deltaH1_eq_ker_mapH2
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

universe u v

namespace Work.Tate

/-- The `2 → 1` connecting map `H¹(G, A^*) →+ H²(G, A)` of the shift sequence. -/
noncomputable abbrev coindSESdeltaH1 (G : Type u) (A : Type v) [Group G] [AddCommGroup A]
    [DistribMulAction G A] [Fintype G] :
    GroupCohomology.H1 G (coindShift G A) →+ GroupCohomology.H2 G A :=
  (coindSES G A).toShortExactSeq.deltaH1

/-- **Dimension shifting `2 → 1`.**  The connecting map of the shift sequence is an isomorphism
`H¹(G, A^*) ≃+ H²(G, A)` because `Coind(A)` is acyclic. -/
noncomputable def dimensionShiftH2H1Symm (G : Type u) (A : Type v) [Group G] [AddCommGroup A]
    [DistribMulAction G A] [Fintype G] :
    GroupCohomology.H1 G (coindShift G A) ≃+ GroupCohomology.H2 G A :=
  AddEquiv.ofBijective _ (by
    have h1 : Subsingleton (GroupCohomology.H1 G (G → A)) :=
      (Submission.subsingleton_H1_H2_coind G A).1
    have h2 : Subsingleton (GroupCohomology.H2 G (G → A)) :=
      (Submission.subsingleton_H1_H2_coind G A).2
    have hf : (GroupCohomology.mapH1 G (coindSES G A).toShortExactSeq.pi
        (coindSES G A).toShortExactSeq.pi_equivariant).range = ⊥ := by
      refine le_antisymm ?_ bot_le
      rintro y ⟨x, rfl⟩
      have hx : x = 0 := h1.elim x 0
      rw [hx, map_zero]
      exact AddSubgroup.zero_mem _
    have hg : (GroupCohomology.mapH2 G (coindSES G A).toShortExactSeq.iota
        (coindSES G A).toShortExactSeq.iota_equivariant).ker = ⊤ := by
      refine le_antisymm le_top ?_
      intro y _
      rw [AddMonoidHom.mem_ker]
      exact h2.elim _ 0
    have hker : (coindSES G A).toShortExactSeq.deltaH1.ker = ⊥ := by
      rw [ker_deltaH1_eq_range_mapH1, hf]
    have hrange : (coindSES G A).toShortExactSeq.deltaH1.range = ⊤ := by
      rw [range_deltaH1_eq_ker_mapH2, hg]
    refine ⟨?_, ?_⟩
    · intro x y hxy
      have hmem : x - y ∈ (coindSES G A).toShortExactSeq.deltaH1.ker := by
        rw [AddMonoidHom.mem_ker, map_sub, hxy, sub_self]
      rw [hker] at hmem
      exact sub_eq_zero.mp (by simpa using hmem)
    · intro y
      have hmem : y ∈ (coindSES G A).toShortExactSeq.deltaH1.range := by
        rw [hrange]; exact AddSubgroup.mem_top y
      exact AddMonoidHom.mem_range.mp hmem)

/-- **Dimension shifting `2 → 1`**: `H²(G, A) ≃+ H¹(G, A^*)`. -/
noncomputable def dimensionShiftH2H1 (G : Type u) (A : Type v) [Group G] [AddCommGroup A]
    [DistribMulAction G A] [Fintype G] :
    GroupCohomology.H2 G A ≃+ GroupCohomology.H1 G (coindShift G A) :=
  (dimensionShiftH2H1Symm G A).symm

/-- The `1 → 0` connecting map `Ĥ⁰(G, A^*) →+ H¹(G, A)` of the shift sequence. -/
noncomputable abbrev coindSESdelta0 (G : Type u) (A : Type v) [Group G] [AddCommGroup A]
    [DistribMulAction G A] [Fintype G] :
    H0 G (coindShift G A) →+ GroupCohomology.H1 G A :=
  (coindSES G A).delta0

/-- **Dimension shifting `1 → 0`.**  The connecting map of the shift sequence is an isomorphism
`Ĥ⁰(G, A^*) ≃+ H¹(G, A)` because `Coind(A)` is acyclic. -/
noncomputable def dimensionShiftH1H0Symm (G : Type u) (A : Type v) [Group G] [AddCommGroup A]
    [DistribMulAction G A] [Fintype G] :
    H0 G (coindShift G A) ≃+ GroupCohomology.H1 G A :=
  AddEquiv.ofBijective _ (by
    have h0 : Subsingleton (H0 G (G → A)) := coind_H0_subsingleton (G := G) (R := A)
    have h1 : Subsingleton (GroupCohomology.H1 G (G → A)) :=
      (Submission.subsingleton_H1_H2_coind G A).1
    have hg : (coindSES G A).H0g.range = ⊥ := by
      refine le_antisymm ?_ bot_le
      rintro y ⟨x, rfl⟩
      have hx : x = 0 := h0.elim x 0
      rw [hx, map_zero]
      exact AddSubgroup.zero_mem _
    have hf : (GroupCohomology.mapH1 G (coindSES G A).f (coindSES G A).f_equiv).ker = ⊤ := by
      refine le_antisymm le_top ?_
      intro y _
      rw [AddMonoidHom.mem_ker]
      exact h1.elim _ 0
    have hker : (coindSES G A).delta0.ker = ⊥ := by
      rw [ker_delta0_eq_range_H0g, hg]
    have hrange : (coindSES G A).delta0.range = ⊤ := by
      rw [range_delta0_eq_ker_mapH1, hf]
    refine ⟨?_, ?_⟩
    · intro x y hxy
      have hmem : x - y ∈ (coindSES G A).delta0.ker := by
        rw [AddMonoidHom.mem_ker, map_sub, hxy, sub_self]
      rw [hker] at hmem
      exact sub_eq_zero.mp (by simpa using hmem)
    · intro y
      have hmem : y ∈ (coindSES G A).delta0.range := by
        rw [hrange]; exact AddSubgroup.mem_top y
      exact AddMonoidHom.mem_range.mp hmem)

/-- **Dimension shifting `1 → 0`**: `H¹(G, A) ≃+ Ĥ⁰(G, A^*)`. -/
noncomputable def dimensionShiftH1H0 (G : Type u) (A : Type v) [Group G] [AddCommGroup A]
    [DistribMulAction G A] [Fintype G] :
    GroupCohomology.H1 G A ≃+ H0 G (coindShift G A) :=
  (dimensionShiftH1H0Symm G A).symm

/-- **Dimension shifting `2 → 0`**: `Ĥ²(G, A) ≃+ Ĥ⁰(G, A^{**})`.  This form mentions only
double twists, so it can be *used* without any instance-search depth workaround. -/
noncomputable def dimensionShiftH2H0 (G : Type u) (A : Type v) [Group G] [AddCommGroup A]
    [DistribMulAction G A] [Fintype G] :
    GroupCohomology.H2 G A ≃+ H0 G (coindShift G (coindShift G A)) :=
  (dimensionShiftH2H1 G A).trans (dimensionShiftH1H0 G (coindShift G A))

/-- **Dimension shifting `Ĥ¹(G, A) ≃+ Ĥ⁻¹(G, A^{**})`** (`k = 1` of the paper's relation, with
`A_1 = I_G^{-2}`): two applications of the shift `A ↦ A^* = Coind(A)/A`. -/
noncomputable def dimensionShiftH1 (G : Type u) (A : Type v) [Group G] [AddCommGroup A]
    [DistribMulAction G A] [Fintype G] :=
  letI : AddCommGroup (coindShift G A) := inferInstance
  letI : DistribMulAction G (coindShift G A) := inferInstance
  (dimensionShiftH1H0 G A).trans (dimensionShiftCoind G (coindShift G A)).symm

/-- **Dimension shifting `Ĥ²(G, A) ≃+ Ĥ⁻¹(G, A^{***})`** (`k = 2` of the paper's relation, with
`A_2 = I_G^{-3}`): three applications of the shift `A ↦ A^* = Coind(A)/A`. -/
noncomputable def dimensionShiftH2 (G : Type u) (A : Type v) [Group G] [AddCommGroup A]
    [DistribMulAction G A] [Fintype G] :=
  letI : AddCommGroup (coindShift G (coindShift G A)) := inferInstance
  letI : DistribMulAction G (coindShift G (coindShift G A)) := inferInstance
  (dimensionShiftH2H1 G A).trans
    ((dimensionShiftH1H0 G (coindShift G A)).trans
      (dimensionShiftCoind G (coindShift G (coindShift G A))).symm)

end Work.Tate
