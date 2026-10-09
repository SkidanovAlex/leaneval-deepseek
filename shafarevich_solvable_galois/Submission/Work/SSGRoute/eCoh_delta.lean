import Mathlib
import Submission.Work.SSGRoute.E0bDefs
import Submission.Work.SSGRoute.PTDefs
import Submission.Work.SSGRoute.eCoh_delta_aux
import Submission.Work.SSGRoute.extMk_comp_extClass
import Submission.Work.SSGRoute.exists_lift_and_factor
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The connecting map of the `Hⁿ(G, -)`/`Extⁿ_G(ℤ, -)` comparison (`eCoh_delta`)

We prove that the isomorphism `SSGRoute.PTExt.eCoh n G A : Hⁿ(G, A) ≃+ Extⁿ_G(ℤ, A)` commutes,
up to sign, with the connecting maps of a short exact sequence `S` of `Rep Coeff G`
(`Work.SSGRoute.eCoh_delta`).

The argument: write `y = π z` for an inhomogeneous cocycle `z`; lift `z` to a cochain `y₂` for
`S.X₂` and take `x` with `S.f ∘ x = d y₂` (`exists_lift_and_factor`).  Both sides of the
assertion are then computed by `extMk` of the associated `cochainsToHom`s (`eCoh_cocycle`,
`eCoh_delta_cocycle`), and the remaining statement is the computation of the Yoneda product with
`hS.extClass` by lifting in a projective resolution (`extMk_comp_extClass`).
-/

namespace Work.SSGRoute

open CategoryTheory Limits SSGRoute.PTExt

noncomputable section

open CategoryTheory Limits in
theorem eCoh_delta (n : ℕ) (G : Type) [Group G] (S : ShortComplex (Rep SSGRoute.PTExt.Coeff G))
    (hS : S.ShortExact) (y : groupCohomology S.X₃ n) :
    SSGRoute.PTExt.eCoh (n + 1) G S.X₁ ((groupCohomology.δ hS n (n + 1) rfl).hom y) =
        (SSGRoute.PTExt.eCoh n G S.X₃ y).comp hS.extClass rfl ∨
      SSGRoute.PTExt.eCoh (n + 1) G S.X₁ ((groupCohomology.δ hS n (n + 1) rfl).hom y) =
        -((SSGRoute.PTExt.eCoh n G S.X₃ y).comp hS.extClass rfl) := by
  induction y using groupCohomology_induction_on with
  | h zcyc =>
    obtain ⟨hz, hzc⟩ := cocyclesMk_iCocycles n G S.X₃ zcyc
    rw [← hzc]
    let z : (Fin n → G) → S.X₃ := ⇑(groupCohomology.iCocycles S.X₃ n) zcyc
    obtain ⟨y₂, x, hy₂, hx, hxc⟩ := exists_lift_and_factor n G S hS z hz
    have hL : eCoh (n + 1) G S.X₁
        (groupCohomology.δ hS n (n + 1) rfl
          (groupCohomology.π S.X₃ n (groupCohomology.cocyclesMk z hz))) =
        (Rep.barResolution Coeff G).extMk (cochainToHom (n + 1) G S.X₁ x) (n + 2) rfl
          (cochainToHom_cocycle (n + 1) G S.X₁ x hxc) :=
      eCoh_delta_cocycle n G S hS z hz y₂ hy₂ x hx hxc
    have hR : eCoh n G S.X₃ (groupCohomology.π S.X₃ n (groupCohomology.cocyclesMk z hz)) =
        (Rep.barResolution Coeff G).extMk (cochainToHom n G S.X₃ z) (n + 1) rfl
          (cochainToHom_cocycle n G S.X₃ z hz) :=
      eCoh_cocycle n G S.X₃ z hz
    have hy₂' : (fun g : Fin n → G => S.g (y₂ g)) = z := by
      rw [← hy₂]
      rfl
    have hw₂ : cochainToHom n G S.X₂ y₂ ≫ S.g = cochainToHom n G S.X₃ z := by
      rw [cochainToHom_naturality n G S.g y₂, hy₂']
    have hw₁ : cochainToHom (n + 1) G S.X₁ x ≫ S.f =
        (Rep.barResolution Coeff G).complex.d (n + 1) n ≫ cochainToHom n G S.X₂ y₂ := by
      have hx' : (fun g : Fin (n + 1) → G => S.f (x g)) =
          ConcreteCategory.hom ((groupCohomology.inhomogeneousCochains S.X₂).d n (n + 1)) y₂ := hx
      rw [cochainToHom_naturality (n + 1) G S.f x, hx']
      exact (cochainToHom_d n G S.X₂ y₂).symm
    have hkey := extMk_comp_extClass (Rep.barResolution Coeff G) hS
      (cochainToHom n G S.X₃ z) (cochainToHom_cocycle n G S.X₃ z hz)
      (cochainToHom n G S.X₂ y₂) hw₂
      (cochainToHom (n + 1) G S.X₁ x) hw₁
      (cochainToHom_cocycle (n + 1) G S.X₁ x hxc)
    rw [← hL, ← hR] at hkey
    rcases hkey with h | h
    · exact Or.inl h.symm
    · refine Or.inr ?_
      simpa using congrArg Neg.neg h.symm

end

end Work.SSGRoute
