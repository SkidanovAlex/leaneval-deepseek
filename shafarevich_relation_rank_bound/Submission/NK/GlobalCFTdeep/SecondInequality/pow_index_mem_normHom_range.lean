import Mathlib
import Submission.NK.GlobalCFTdeep.AbstractH0

namespace NK.GlobalCFTdeep.SecondInequality

/-- If `y = N_H x` is a norm from the subgroup `H` and is moreover fixed by all of `G`, then
`y ^ [G : H]` is a norm from `G`: writing `G = ⊔_{s ∈ S} s H` for a left transversal `S`,
`y ^ |S| = ∏_{s : ↥S} s • y = ∏_{s : ↥S} ∏_{h : ↥H} (s * h) • x = ∏_{g : G} g • x`, using
`Nat.card ↥S = H.index`. -/
theorem pow_index_mem_normHom_range {G M : Type*} [Group G] [Fintype G] [CommGroup M]
    [MulDistribMulAction G M] (H : Subgroup G) [Fintype ↥H] {y : M}
    (hy : y ∈ (NK.GlobalCFTdeep.normHom H M).range)
    (hyA : y ∈ NK.GlobalCFTdeep.fixedSubgroup G M) :
    y ^ H.index ∈ (NK.GlobalCFTdeep.normHom G M).range := by
  classical
  -- Write `y = N_H x` and produce the norm of `x` over `G` as the witness.
  obtain ⟨x, rfl⟩ := hy
  refine ⟨x, ?_⟩
  rw [NK.GlobalCFTdeep.normHom_apply]
  -- `S` is a left transversal of `H` in `G`, of cardinality `H.index`.
  let S : Set G := Set.range (Quotient.out : G ⧸ H → G)
  have hcomp : Subgroup.IsComplement S (H : Set G) :=
    Subgroup.isComplement_range_left (f := fun q : G ⧸ H => Quotient.out q)
      (fun q => Quotient.out_eq' q)
  have hcard : Fintype.card ↥S = H.index := by
    rw [← Nat.card_eq_fintype_card, hcomp.card_left]
  -- Each `s ∈ S` contributes `N_H x`, which is fixed by `G`.
  have hinner : ∀ s : ↥S,
      ∏ h : ↥(H : Set G), ((s : G) * (h : G)) • x = NK.GlobalCFTdeep.normHom H M x := by
    intro s
    rw [NK.GlobalCFTdeep.normHom_apply]
    have step1 : (∏ h : ↥(H : Set G), ((s : G) * (h : G)) • x)
        = (MulDistribMulAction.toMulAut G M (s : G)) (∏ h : ↥(H : Set G), (h : G) • x) := by
      rw [map_prod]
      exact Finset.prod_congr rfl (fun h _ => (mul_smul (s : G) (h : G) x).trans rfl)
    have hprod : (∏ h : ↥(H : Set G), (h : G) • x) = NK.GlobalCFTdeep.normHom H M x := by
      rw [NK.GlobalCFTdeep.normHom_apply]
      exact Finset.prod_congr rfl (fun h _ => (Subgroup.smul_def h x).symm)
    rw [step1, hprod]
    exact hyA (s : G)
  -- Reindex `G` by `↥S × ↥H` and evaluate.
  calc ∏ g : G, g • x
      = ∏ p : ↥S × ↥(H : Set G), ((p.1 : G) * (p.2 : G)) • x :=
        (Fintype.prod_equiv hcomp.equiv.symm _ _ (fun p => by
          show ((p.1 : G) * (p.2 : G)) • x = (hcomp.equiv.symm p : G) • x
          rw [Subgroup.IsComplement.equiv_symm_apply])).symm
    _ = ∏ s : ↥S, ∏ h : ↥(H : Set G), ((s : G) * (h : G)) • x :=
        Fintype.prod_prod_type _
    _ = ∏ _s : ↥S, NK.GlobalCFTdeep.normHom H M x :=
        Finset.prod_congr rfl (fun s _ => hinner s)
    _ = (NK.GlobalCFTdeep.normHom H M x) ^ H.index := by
        rw [Finset.prod_const, Finset.card_univ, hcard]

end NK.GlobalCFTdeep.SecondInequality
