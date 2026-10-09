import Mathlib
import Submission.NK.GlobalCFTdeep.SecondInequality.pow_index_mem_normHom_range
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace NK.NUV2.ArtinBridge

/-- Additive (`ℤ`-module) analogue of `pow_index_mem_normHom_range`: if `x` is fixed by all of
`G` and is a `P`-norm, then `[G : P] • x` is a `G`-norm.  Writing `G = ⊔_{s ∈ S} sP` for a left
transversal `S` of `P` in `G`, each coset block `∑_{p : P} ρ (s * p)` sends the witness `y` to
`ρ s x = x`, so the full `G`-norm of `y` is `|S| • x = P.index • x`. -/
theorem nsmul_index_mem_norm_range {G V : Type} [Group G] [Fintype G] [AddCommGroup V] [Module ℤ V]
    (ρ : Representation ℤ G V) (P : Subgroup G) [Fintype ↥P] {x : V}
    (hx : ∀ g : G, ρ g x = x)
    (hy : x ∈ LinearMap.range (∑ p : ↥P, ρ p.1)) :
    P.index • x ∈ LinearMap.range (∑ g : G, ρ g) := by
  classical
  -- Write `x = N_P y` and exhibit `y` as a witness for the `G`-norm of `[G : P] • x`.
  obtain ⟨y, hy⟩ := hy
  refine ⟨y, ?_⟩
  simp only [LinearMap.sum_apply]
  -- `S` is a left transversal of `P` in `G`, of cardinality `P.index`.
  let S : Set G := Set.range (Quotient.out : G ⧸ P → G)
  have hcomp : Subgroup.IsComplement S (P : Set G) :=
    Subgroup.isComplement_range_left (f := fun q : G ⧸ P => Quotient.out q)
      (fun q => Quotient.out_eq' q)
  have hcard : Fintype.card ↥S = P.index := by
    rw [← Nat.card_eq_fintype_card, hcomp.card_left]
  -- Each coset `s P` contributes the fixed element `x`.
  have hinner : ∀ s : ↥S,
      (∑ p : ↥P, ρ ((s : G) * (p : G))) y = x := by
    intro s
    have hstep : (∑ p : ↥P, ρ ((s : G) * (p : G))) y
        = ρ (s : G) ((∑ p : ↥P, ρ (p : G)) y) := by
      simp only [LinearMap.sum_apply, map_sum]
      apply Finset.sum_congr rfl
      intro p _
      rw [map_mul]
      rfl
    rw [hstep, hy, hx]
  -- Reindex `G` by the complement `↥S × ↥P` and evaluate coset by coset.
  calc ∑ g : G, ρ g y
      = ∑ p : ↥S × ↥P, ρ ((p.1 : G) * (p.2 : G)) y :=
        (Fintype.sum_equiv hcomp.equiv.symm
          (fun p : ↥S × ↥P => ρ ((p.1 : G) * (p.2 : G)) y)
          (fun g : G => ρ g y) (fun p => by
            show ρ ((p.1 : G) * (p.2 : G)) y = ρ (hcomp.equiv.symm p : G) y
            rw [Subgroup.IsComplement.equiv_symm_apply])).symm
    _ = ∑ s : ↥S, ∑ p : ↥P, ρ ((s : G) * (p : G)) y := Fintype.sum_prod_type _
    _ = ∑ _s : ↥S, x := Finset.sum_congr rfl (fun s _ => by
          rw [← hinner s]; simp only [LinearMap.sum_apply])
    _ = P.index • x := by rw [Finset.sum_const, Finset.card_univ, hcard]

end NK.NUV2.ArtinBridge
