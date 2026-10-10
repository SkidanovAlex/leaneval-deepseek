import Mathlib.GroupTheory.Nilpotent
import Mathlib.Algebra.Field.ZMod
import Submission.Work.SSGRoute.TateDual.dual_coindUp_coindShift
import Submission.Work.SSGRoute.TateDual.tateDuality_degree_zero
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `tateDuality_hm2_dual`

Finite-group Tate duality in degree `-2`, in the models of `Submission/Work/Tate`:

  `Ĥ⁻²(G, M^*) ≅ H¹(G, M)^∨`,  `M^* = Hom(M, 𝔽_p)`,

where `Ĥ⁻²(G, M^*)` is `Work.Tate.Hm2 G (DualMod p M) = Ĥ⁻¹(G, M^*^♯)` with `M^*^♯` the
`I_G`-twist `Work.Tate.coindUp G (DualMod p M)` (the workspace's model of `Ĥ⁻²`).

Assembly of the two classical ingredients proved in `SSGRoute/TateDual/`:

* `tateDuality_degree_zero` — the perfect evaluation pairing
  `Ĥ⁻¹(G, A) × Ĥ⁰(G, A^∨) → 𝔽_p` (Tate duality in degree `0`), applied to
  `A = ↥(coindUp G (DualMod p M))`;
* `dual_coindUp_coindShift` — the dual of the shift sequence, identifying
  `DualMod p ↥(coindUp G (M^∨))` with `coindShift G M = Coind(M)/M` `G`-equivariantly;

together with the dimension shift `Work.Tate.dimensionShiftH1H0 : H¹(G, M) ≃+ Ĥ⁰(G, coindShift G M)`
(`H¹ ≅ Ĥ⁰` of the shift) — `Ĥ⁻²(G, M^∨) ≅ Ĥ⁻¹(G, M^∨^♯) ≅ (Ĥ⁰(G, Dual(coindUp)))^∨ ≅ (Ĥ⁰(G, M♭))^∨
≅ (H¹(G,M))^∨`.
-/

namespace Work.SSGRoute

/-- Transport of additive homomorphisms out of an additively equivalent domain:
`(B →+ D) ≃+ (C →+ D)` from `e : B ≃+ C`, by precomposition with `e.symm`. -/
def addHomCongrRight {D B C : Type} [AddCommGroup D] [AddCommGroup B] [AddCommGroup C]
    (e : B ≃+ C) : (B →+ D) ≃+ (C →+ D) where
  toFun φ := φ.comp e.symm.toAddMonoidHom
  invFun ψ := ψ.comp e.toAddMonoidHom
  left_inv φ := by ext x; simp
  right_inv ψ := by ext x; simp
  map_add' φ ψ := by ext x; simp

theorem tateDuality_hm2_dual (p : ℕ) [Fact p.Prime] (G : Type) [Group G] [Fintype G]
    (M : Type) [AddCommGroup M] [Module (ZMod p) M] [DistribMulAction G M]
    [SMulCommClass G (ZMod p) M] [Finite M] :
    Nonempty (Work.Tate.Hm2 G (Work.SSGRoute.DualMod p M) ≃+
      (Work.GroupCohomology.H1 G M →+ ZMod p)) := by
  -- The dual of the `I_G`-twist is the shift `Coind(M)/M`.
  obtain ⟨eB, hB⟩ := Work.SSGRoute.TateDual.dual_coindUp_coindShift (p := p) (G := G) (M := M)
  -- Tate duality in degree `0`, applied to the `I_G`-twist of `M^∨`.
  obtain ⟨eA⟩ := Work.SSGRoute.TateDual.tateDuality_degree_zero (p := p) (G := G)
    (A := ↥(Work.Tate.coindUp G (Work.SSGRoute.DualMod p M)))
  -- Transport along the duality of the shift, then along the dimension shift `H¹ ≅ Ĥ⁰`.
  have h0 := Work.Tate.H0Equiv eB.toAddMonoidHom hB eB.bijective
  have h1 := Work.Tate.dimensionShiftH1H0 G M
  exact ⟨eA.trans ((addHomCongrRight h0).trans (addHomCongrRight h1).symm)⟩

end Work.SSGRoute
