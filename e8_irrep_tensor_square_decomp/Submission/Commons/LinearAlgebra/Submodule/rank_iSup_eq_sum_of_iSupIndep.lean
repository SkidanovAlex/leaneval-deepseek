import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.HopkinsLevitzki

namespace Commons.LinearAlgebra.Submodule

open Module

/-- The rank of the supremum of two disjoint submodules is the sum of their ranks.
(Over a division ring every submodule is a free module.) -/
theorem rank_sup_of_disjoint {K M : Type*} [DivisionRing K] [AddCommGroup M] [Module K M]
    {p q : Submodule K M} (h : Disjoint p q) :
    Module.rank K ↥(p ⊔ q) = Module.rank K ↥p + Module.rank K ↥q := by
  have e : (↥p × ↥q) ≃ₗ[K] ↥(p ⊔ q) := by
    refine LinearEquiv.ofBijective ?_ ⟨?_, ?_⟩
    · refine
      { toFun := fun x => ⟨↑x.1 + ↑x.2, ?_⟩
        map_add' := ?_
        map_smul' := ?_ }
      · exact add_mem (Submodule.mem_sup_left x.1.2) (Submodule.mem_sup_right x.2.2)
      · intro a b
        ext
        simp only [Prod.fst_add, Prod.snd_add, Submodule.coe_add]
        abel
      · intro c a
        ext
        simp only [Prod.smul_fst, Prod.smul_snd, Submodule.coe_smul, smul_add,
          RingHom.id_apply]
    · intro x y hxy
      have h1 : (↑x.1 : M) + ↑x.2 = ↑y.1 + ↑y.2 := congrArg Subtype.val hxy
      have hx : (↑x.1 : M) - ↑y.1 = ↑y.2 - ↑x.2 := by
        rw [sub_eq_sub_iff_add_eq_add]
        exact h1.trans (add_comm (↑y.1 : M) (↑y.2 : M))
      have hmem : (↑x.1 : M) - ↑y.1 ∈ p ⊓ q := by
        refine ⟨?_, ?_⟩
        · exact Submodule.sub_mem p x.1.2 y.1.2
        · rw [hx]
          exact Submodule.sub_mem q y.2.2 x.2.2
      rw [disjoint_iff.mp h] at hmem
      simp only [Submodule.mem_bot] at hmem
      have h1' : (↑x.1 : M) = ↑y.1 := sub_eq_zero.mp hmem
      have h2' : (↑x.2 : M) = ↑y.2 := by
        have hh := h1
        rw [h1'] at hh
        exact add_left_cancel hh
      exact Prod.ext (Subtype.ext h1') (Subtype.ext h2')
    · intro y
      obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.mp y.2
      refine ⟨(⟨a, ha⟩, ⟨b, hb⟩), Subtype.ext ?_⟩
      change a + b = ↑y
      exact hab
  rw [← e.rank_eq, rank_prod']

/-- The rank of the supremum of a finite supremum-independent family of submodules is the sum
of the ranks of the members. -/
theorem rank_biSup_finset_eq_sum {K M ι : Type*} [DivisionRing K] [AddCommGroup M]
    [Module K M] (f : ι → Submodule K M) (h : iSupIndep f) (s : Finset ι) :
    Module.rank K ↥(⨆ i ∈ (s : Set ι), f i) = ∑ i ∈ s, Module.rank K ↥(f i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      rw [Finset.sum_empty, Finset.coe_empty]
      have hb : (⨆ i ∈ (∅ : Set ι), f i) = ⊥ := by simp
      rw [hb, rank_zero_iff]
      infer_instance
  | insert a t ha ih =>
      rw [Finset.coe_insert, iSup_insert, Finset.sum_insert ha]
      rw [rank_sup_of_disjoint (h.disjoint_biSup (by simpa using ha)), ih]

theorem rank_iSup_eq_sum_of_iSupIndep {K M ι : Type*} [DivisionRing K] [AddCommGroup M]
    [Module K M] [Fintype ι] (f : ι → Submodule K M) (h : iSupIndep f) :
    Module.rank K ↥(⨆ i, f i) = ∑ i, Module.rank K ↥(f i) := by
  have key : (⨆ i ∈ ((Finset.univ : Finset ι) : Set ι), f i) = ⨆ i, f i := by simp
  rw [← key]
  exact rank_biSup_finset_eq_sum f h Finset.univ

end Commons.LinearAlgebra.Submodule