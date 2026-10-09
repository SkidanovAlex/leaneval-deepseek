/-
# Non-degeneracy of the canonical Tate pairing `H₁(G, A) × H¹(G, A^∨) → k`

`Work.SSGRoute.H1Pair.tatePairLin A : H₁(G, A) →ₗ (H¹(G, A^∨))^∨` is the explicit evaluation
pairing of the bar complex, with computation rule `tatePairLin A (H1π c) (H1π θ) = ∑_g θ g (c g)`.

This file proves that the pairing is non-degenerate:
* `tatePairLin_injective`: an element of `H₁(G, A)` pairing to zero against everything is zero;
* `tatePairLin_bijective`: over `𝔽_p`, for finite `G` and finite `A`, it is an isomorphism
  (Tate duality `H₁ ≅ H¹(A^∨)^∨`).

The injectivity argument is the concrete universal-coefficient computation.  Writing
`V = G →₀ A` for the 1-chains and `Ξ = Finsupp.lsum k : (G → A^∨) ≅ V^∨` for the curried pairing,
the identity `pairFun_d₂₁` says `Ξ ∘ d₁₂ = (d₂₁)^∨ ∘ Ξ`; hence `Ξ(ker d₁₂) = (im d₂₁)^⊥`.  If
`[c] ∈ H₁` pairs to zero against every cocycle, then `Dual.eval c` kills `(im d₂₁)^⊥`, so
`c ∈ (im d₂₁)^{⊥⊥} = im d₂₁ = B₁`, i.e. `[c] = 0`.  (`Subspace.dualAnnihilator_dualAnnihilator_eq`,
`Module.mapEvalEquiv_apply`, `Module.evalEquiv`.)
-/
import Submission.Work.SSGRoute.H1Pair.Pairing
import Submission.Work.SSGRoute.H1_tateDual_clean
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

noncomputable section

open CategoryTheory

namespace Work.SSGRoute.H1Pair

universe u

variable {k : Type u} [Field k] {G : Type u} [Group G] [Fintype G] (A : Rep k G)
  [FiniteDimensional k A.V]

/-- **Non-degeneracy of the canonical Tate pairing in the second argument**: an element of
`H₁(G, A)` whose pairing with every class of `H¹(G, A^∨)` vanishes is zero. -/
theorem tatePairLin_injective :
    Function.Injective (tatePairLin A) := by
  have key : ∀ z : groupHomology.H1 A, tatePairLin A z = 0 → z = 0 := by
    intro z
    refine groupHomology.H1_induction_on z fun c => ?_
    intro hz
    rw [groupHomology.H1π_eq_zero_iff]
    -- `(c : G →₀ A) ∈ boundaries₁ A`
    set W : Submodule k (G →₀ A.V) := groupHomology.boundaries₁ A with hW
    have hkill : ∀ θ : G → Module.Dual k A.V,
        (groupCohomology.d₁₂ (contra A)).hom θ = 0 → pairFun c.1 θ = 0 := by
      intro θ hθ
      have h1 : tatePairLin A ((groupHomology.H1π A) c)
          ((groupCohomology.H1π (contra A)) ⟨θ, hθ⟩) = pairFun c.1 θ :=
        tatePairLin_apply_mk A c ⟨θ, hθ⟩
      rw [← h1, hz]
      exact LinearMap.zero_apply _
    have hmem : Module.Dual.eval k (G →₀ A.V) c.1 ∈ W.dualAnnihilator.dualAnnihilator := by
      rw [Submodule.mem_dualAnnihilator]
      intro φ hφ
      rw [Module.Dual.eval_apply]
      obtain ⟨θ, rfl⟩ := (Finsupp.lsum k).surjective φ
      have hθ : (groupCohomology.d₁₂ (contra A)).hom θ = 0 := by
        funext p
        refine LinearMap.ext fun a => ?_
        have hx : (Finsupp.lsum k θ) ((groupHomology.d₂₁ A).hom (Finsupp.single p a)) = 0 :=
          (Submodule.mem_dualAnnihilator (Finsupp.lsum k θ)).1 hφ _
            ⟨Finsupp.single p a, rfl⟩
        rw [← pairFun_eq] at hx
        rw [pairFun_d₂₁ A (Finsupp.single p a) θ, pairFun_single] at hx
        exact hx
      rw [← pairFun_eq]
      exact hkill θ hθ
    rw [Subspace.dualAnnihilator_dualAnnihilator_eq, Module.mapEvalEquiv_apply] at hmem
    obtain ⟨w, hw, hwe⟩ := hmem
    have hwc : w = c.1 := (Module.evalEquiv k (G →₀ A.V)).injective (by
      rw [Module.evalEquiv_apply, Module.evalEquiv_apply]
      exact hwe)
    rw [← hwc]
    exact hw
  intro x y hxy
  have h : x - y = 0 := key (x - y) (by rw [map_sub, hxy, sub_self])
  exact sub_eq_zero.mp h

/-- **Tate duality as an isomorphism from the explicit pairing**: over `𝔽_p`, for a finite group
`G` and a finite `𝔽_p[G]`-module `M`, the explicit evaluation pairing
`tatePairLin M : H₁(G, M) →ₗ (H¹(G, M^∨))^∨` is bijective. -/
theorem tatePairLin_bijective (p : ℕ) [Fact p.Prime] {G : Type} [Group G] [Fintype G]
    (M : Rep (ZMod p) G) [Finite M.V] :
    Function.Bijective (tatePairLin M) := by
  haveI : FiniteDimensional (ZMod p) M.V := Module.Finite.of_finite
  have hinj : Function.Injective (tatePairLin M) := tatePairLin_injective M
  refine ⟨hinj, ?_⟩
  haveI hfin : Module.Finite (ZMod p) (groupHomology.H1 M) :=
    Module.Finite.of_surjective (groupHomology.H1π M).hom
      ((ModuleCat.epi_iff_surjective (groupHomology.H1π M)).1 inferInstance)
  obtain ⟨e⟩ := H1_tateDual_clean p M
  haveI hfin' : Module.Finite (ZMod p)
      (Module.Dual (ZMod p) (groupCohomology.H1 (Rep.of M.ρ.dual))) :=
    Module.Finite.of_surjective (e : groupHomology.H1 M →ₗ[ZMod p] _) e.surjective
  have hfr : Module.finrank (ZMod p) (groupHomology.H1 M)
      = Module.finrank (ZMod p)
          (Module.Dual (ZMod p) (groupCohomology.H1 (Rep.of M.ρ.dual))) :=
    LinearEquiv.finrank_eq e
  exact (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hfr).1 hinj

end Work.SSGRoute.H1Pair
