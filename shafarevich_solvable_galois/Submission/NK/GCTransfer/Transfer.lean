/-
The transfer (corestriction) identity at the level of cochains and of `H²`.

Given a subgroup `S ≤ Γ` of finite index and a `2`-cocycle `z` of a representation `A : Rep k Γ`
whose restriction to `S` is a coboundary, the cochain `[Γ : S] • z` is a coboundary on `Γ`
(`exists_coboundary_index_nsmul`).  Consequently, restriction to `S` is injective on the
`p`-torsion of `H²` whenever the index of `S` is prime to `p`.

This uses the two cochain identities `NK.GCTransfer.cor1_d12` and
`NK.GCTransfer.cor2_cocycles`.
-/
import Submission.NK.GCTransfer.cor1_d12
import Submission.NK.GCTransfer.cor2_cocycles
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

open CategoryTheory Representation Rep

set_option autoImplicit false
set_option maxHeartbeats 1600000

universe u

namespace NK.GCTransfer

variable {Γ : Type u} [Group Γ] [Fintype Γ] (S : Subgroup Γ)
variable {k : Type u} [CommRing k] (A : Rep.{u,u,u} k Γ)

omit [Fintype Γ] in
/-- The restriction map on `2`-cocycles along the inclusion of a subgroup, evaluated at a pair in
the subgroup: it is the evident restriction of the cocycle. -/
lemma mapCocycles₂_subtype_apply (w : groupCohomology.cocycles₂ A) (s t : S) :
    ((groupCohomology.mapCocycles₂ S.subtype (𝟙 (Rep.res S.subtype A))) w) (s, t) =
      w ((s : Γ), (t : Γ)) := by
  rw [groupCohomology.coe_mapCocycles₂]
  have h : (groupCohomology.cochainsMap₂ S.subtype (𝟙 (Rep.res S.subtype A))) ⇑w
      = fun q : S × S => w ((q.1 : Γ), (q.2 : Γ)) := by
    funext q
    obtain ⟨a, b⟩ := q
    simp only [groupCohomology.cochainsMap₂, LinearMap.comp_apply, LinearMap.compLeft_apply,
      LinearMap.funLeft_apply, Prod.map_apply, Function.comp_apply, ModuleCat.hom_ofHom]
    rfl
  rw [h]

/-- **The cochain-level transfer identity.**  If a `2`-cocycle `z` of `A` restricts to the
coboundary of the `1`-cochain `b` on `S`, then `[Γ : S] • z` is a coboundary on `Γ`. -/
theorem exists_coboundary_index_nsmul (z : groupCohomology.cocycles₂ A) (b : S → A)
    (hb : ∀ s t : S,
      z ((s : Γ), (t : Γ)) = (groupCohomology.d₁₂ (Rep.res S.subtype A)).hom b (s, t)) :
    ∃ B : Γ → A, ∀ σ τ : Γ,
      (groupCohomology.d₁₂ A).hom B (σ, τ) = (Subgroup.index S) • (z (σ, τ)) := by
  refine ⟨fun γ => cor1 S A b γ - Xi S A (⇑z) γ + Pb S A (⇑z) γ, fun σ τ => ?_⟩
  have hcor2 : cor2 S A (fun s t => (groupCohomology.d₁₂ (Rep.res S.subtype A)).hom b (s, t)) σ τ
      = cor2 S A (fun s t => z ((s : Γ), (t : Γ))) σ τ := by
    refine Finset.sum_congr rfl (fun c _ => ?_)
    dsimp only
    rw [hb (sXS S (Quotient.out c) σ) (sXS S (sRep S (Quotient.out c * σ)) τ)]
  have hfun : (fun γ => cor1 S A b γ - Xi S A (⇑z) γ + Pb S A (⇑z) γ)
      = cor1 S A b - (fun γ => Xi S A (⇑z) γ - Pb S A (⇑z) γ) := by
    funext γ
    simp only [Pi.sub_apply]
    abel
  have hlin : (groupCohomology.d₁₂ A).hom
        (fun γ => cor1 S A b γ - Xi S A (⇑z) γ + Pb S A (⇑z) γ)
      = (groupCohomology.d₁₂ A).hom (cor1 S A b)
        - (groupCohomology.d₁₂ A).hom (fun γ => Xi S A (⇑z) γ - Pb S A (⇑z) γ) := by
    rw [hfun, map_sub]
  rw [hlin, Pi.sub_apply, cor1_d12 S A b σ τ, hcor2, cor2_cocycles S A z σ τ]
  abel

end NK.GCTransfer
