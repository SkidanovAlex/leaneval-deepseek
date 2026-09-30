import Mathlib

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# Kernel of a surjection `ℤ^5 → ℤ^4` is `ℤ`

A surjective `ℤ`-linear map from a free `ℤ`-module of rank `5` onto one of rank `4`
has a kernel isomorphic to `ℤ`.

The mathematical content is the rank–nullity theorem for the PID `ℤ`
(`LinearMap.rank_eq_of_surjective`) together with the structure theorem for
submodules of finite free modules over a PID (`Submodule.basisOfPid`): the kernel
is free, its rank is `5 - 4 = 1`, and a free module of rank `1` over `ℤ` is `ℤ`.

The general statement is reduced to the concrete Type-0 case `ℤ^5 → ℤ^4` by
conjugating with the given linear equivalences; the resulting isomorphism is
transported back along the (additive) restriction of `eM` to the kernels, and
converted to a `ℤ`-linear equivalence via `AddEquiv.toIntLinearEquiv`.
-/

namespace Work.BridgeSquare

/-- A surjective `ℤ`-linear map `(Fin 5 → ℤ) →ₗ (Fin 4 → ℤ)` has kernel isomorphic to `ℤ`. -/
theorem ker_finFive_finFour_equiv_int (g : (Fin 5 → ℤ) →ₗ[ℤ] (Fin 4 → ℤ))
    (hg : Function.Surjective g) : Nonempty (g.ker ≃ₗ[ℤ] ℤ) := by
  have bM : Module.Basis (Fin 5) ℤ (Fin 5 → ℤ) := Pi.basisFun ℤ (Fin 5)
  -- The kernel of `g` is a free `ℤ`-module of some finite rank `n`.
  obtain ⟨n, bK⟩ := Submodule.basisOfPid bM g.ker
  have hM : Module.rank ℤ (Fin 5 → ℤ) = (5 : Cardinal) := by
    rw [rank_eq_card_basis bM]; simp
  have hN : Module.rank ℤ (Fin 4 → ℤ) = (4 : Cardinal) := by
    rw [rank_eq_card_basis (Pi.basisFun ℤ (Fin 4))]; simp
  have hker : Module.rank ℤ (g.ker) = (n : Cardinal) := by
    rw [rank_eq_card_basis bK]; simp
  -- Rank–nullity: `5 = 4 + n`, hence `n = 1`.
  have hsurj := LinearMap.rank_eq_of_surjective hg
  rw [hM, hN, hker] at hsurj
  have hn : n = 1 := by
    have h : (5 : ℕ) = 4 + n := by
      apply Nat.cast_injective (R := Cardinal)
      rw [Nat.cast_add]
      exact hsurj
    omega
  subst hn
  -- A basis of the kernel indexed by `Fin 1` exhibits it as `ℤ`.
  exact ⟨bK.repr.trans ((Finsupp.linearEquivFunOnFinite ℤ ℤ (Fin 1)).trans
    (LinearEquiv.funUnique (Fin 1) ℤ ℤ))⟩

theorem ker_equiv_int_of_surjective {M N : Type*} [AddCommGroup M] [Module ℤ M]
    [AddCommGroup N] [Module ℤ N] (eM : M ≃ₗ[ℤ] (Fin 5 → ℤ)) (eN : N ≃ₗ[ℤ] (Fin 4 → ℤ))
    (f : M →ₗ[ℤ] N) (hf : Function.Surjective f) : Nonempty (f.ker ≃ₗ[ℤ] ℤ) := by
  -- Conjugate `f` to a map of concrete free modules.
  let g : (Fin 5 → ℤ) →ₗ[ℤ] (Fin 4 → ℤ) := eN.toLinearMap.comp (f.comp eM.symm.toLinearMap)
  have hg : Function.Surjective g := eN.surjective.comp (hf.comp eM.symm.surjective)
  obtain ⟨φ⟩ := ker_finFive_finFour_equiv_int g hg
  -- `eM` restricts to an additive isomorphism `ker f ≃ ker g`.
  have hfwd : ∀ x : ↥f.ker, eM x.1 ∈ g.ker := fun x => by
    have hx : f x.1 = 0 := LinearMap.mem_ker.mp x.2
    change eN (f (eM.symm (eM x.1))) = 0
    rw [eM.symm_apply_apply, hx, map_zero]
  let fwd : ↥f.ker →+ ↥g.ker :=
    { toFun := fun x => ⟨eM x.1, hfwd x⟩
      map_zero' := by ext; simp
      map_add' := fun x y => by ext; simp [map_add] }
  have hbij : Function.Bijective fwd := by
    constructor
    · intro x y hxy
      exact Subtype.ext (eM.injective (congrArg Subtype.val hxy))
    · intro y
      have hy : eN (f (eM.symm y.1)) = 0 := LinearMap.mem_ker.mp y.2
      refine ⟨⟨eM.symm y.1, ?_⟩, ?_⟩
      · show f (eM.symm y.1) = 0
        exact eN.injective (by rw [hy, map_zero])
      · apply Subtype.ext
        simp [fwd, eM.apply_symm_apply]
  have β : ↥f.ker ≃+ ↥g.ker := AddEquiv.ofBijective fwd hbij
  exact ⟨(β.trans φ.toAddEquiv).toIntLinearEquiv⟩

end Work.BridgeSquare
