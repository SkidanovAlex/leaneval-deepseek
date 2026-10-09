import Mathlib
import Submission.Work.SSGRoute.Interfaces
import Submission.Work.SSGRoute.LTDDefs.Basic
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Coefficient transport for the local `H²` of the model

Milne's proof of the local Euler characteristic (and every step of the local-duality dimension
count) identifies the Euler characteristic of coefficient modules that are related by
`Gal(K/k)`-equivariant linear isomorphisms: `𝔽_p ⊗ T ≅ T`, `DualMod p (M ⊗ T) ≅ …`, and so on.
For the model of `LTDDefs/Basic.lean` this invariance is available for `H1loc`
(`Work.SSGRoute.PTembedding.finrank_H1loc_eq_of_equiv`) and for `H0loc`
(`…finrank_H0loc_eq_of_equiv`); here is the missing degree-`2` half: pushing a locally constant
`2`-cocycle on `H` forward along an equivariant `𝔽_p`-linear map preserves the `2`-cocycle
condition, the local-constancy condition and the coboundaries, so an equivariant *isomorphism*
induces a bijection — hence equality of cardinalities — on `H2loc`.
-/

open scoped Pointwise
open Classical

namespace Work.SSGRoute

noncomputable section

variable {p : ℕ} [Fact p.Prime] {k Ω : Type} [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
  [IsAlgClosure k Ω] {K : IntermediateField k Ω} [FiniteDimensional k K] [IsGalois k K]
  {H : Subgroup (Ω ≃ₐ[k] Ω)}
  {M M' : Type} [AddCommGroup M] [Module (ZMod p) M]
  [DistribMulAction (K ≃ₐ[k] K) M] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M]
  [AddCommGroup M'] [Module (ZMod p) M']
  [DistribMulAction (K ≃ₐ[k] K) M'] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M']

/-- Push-forward of a `2`-cochain along a linear map of coefficients. -/
def pushFun2 (e : M →ₗ[ZMod p] M') (c : (Ω ≃ₐ[k] Ω) → (Ω ≃ₐ[k] Ω) → M) :
    (Ω ≃ₐ[k] Ω) → (Ω ≃ₐ[k] Ω) → M' := fun g h => e (c g h)

@[simp] lemma pushFun2_apply (e : M →ₗ[ZMod p] M') (c : (Ω ≃ₐ[k] Ω) → (Ω ≃ₐ[k] Ω) → M)
    (g h : Ω ≃ₐ[k] Ω) : pushFun2 e c g h = e (c g h) := rfl

/-- Push-forward preserves the `2`-cocycle condition. -/
lemma isCocycle2On_pushFun2 (e : M →ₗ[ZMod p] M')
    (he : ∀ (g : K ≃ₐ[k] K) (m : M), e (g • m) = g • e m)
    {c : (Ω ≃ₐ[k] Ω) → (Ω ≃ₐ[k] Ω) → M} (hc : IsCocycle2On p k Ω K M H c) :
    IsCocycle2On p k Ω K M' H (pushFun2 e c) := by
  intro g hg h hh l hl
  have h1 := hc g hg h hh l hl
  have key : SSGRoute.res k K g • pushFun2 e c h l - pushFun2 e c (g * h) l
        + pushFun2 e c g (h * l) - pushFun2 e c g h
      = e (SSGRoute.res k K g • c h l - c (g * h) l + c g (h * l) - c g h) := by
    simp only [pushFun2_apply, map_sub, map_add, he]
  rw [key, h1, map_zero]

/-- Push-forward preserves local constancy of `2`-cochains. -/
lemma isLocConst2On_pushFun2 (e : M →ₗ[ZMod p] M')
    {c : (Ω ≃ₐ[k] Ω) → (Ω ≃ₐ[k] Ω) → M} (hc : IsLocConst2On p k Ω K M H c) :
    IsLocConst2On p k Ω K M' H (pushFun2 e c) := by
  obtain ⟨U, hUo, hU⟩ := hc
  refine ⟨U, hUo, fun g hg h hh u hu v hv huH hvH => ?_⟩
  simp only [pushFun2_apply, hU g hg h hh u hu v hv huH hvH]

/-- Push-forward of locally constant `2`-cocycles. -/
def pushCocycles2 (e : M →ₗ[ZMod p] M')
    (he : ∀ (g : K ≃ₐ[k] K) (m : M), e (g • m) = g • e m) :
    ↥(lcCocycles2 p k Ω K M H) →ₗ[ZMod p] ↥(lcCocycles2 p k Ω K M' H) where
  toFun c := ⟨pushFun2 e c.1, isCocycle2On_pushFun2 e he c.2.1, isLocConst2On_pushFun2 e c.2.2⟩
  map_add' c d := Subtype.ext (funext fun g => funext fun h => map_add e (c.1 g h) (d.1 g h))
  map_smul' a c := Subtype.ext (funext fun g => funext fun h => map_smul e a (c.1 g h))

@[simp] lemma pushCocycles2_apply (e : M →ₗ[ZMod p] M')
    (he : ∀ (g : K ≃ₐ[k] K) (m : M), e (g • m) = g • e m)
    (c : ↥(lcCocycles2 p k Ω K M H)) (g h : Ω ≃ₐ[k] Ω) :
    (pushCocycles2 e he c).1 g h = e (c.1 g h) := rfl

/-- Push-forward sends `2`-coboundaries to `2`-coboundaries. -/
lemma isCoboundary2On_pushFun2 (e : M →ₗ[ZMod p] M')
    (he : ∀ (g : K ≃ₐ[k] K) (m : M), e (g • m) = g • e m)
    {c : (Ω ≃ₐ[k] Ω) → (Ω ≃ₐ[k] Ω) → M} (hc : SSGRoute.IsCoboundary2On (SSGRoute.res k K) H c) :
    SSGRoute.IsCoboundary2On (SSGRoute.res k K) H (pushFun2 e c) := by
  obtain ⟨b, hb, hbc⟩ := hc
  obtain ⟨U, hUo, hU⟩ := hb
  refine ⟨fun g => e (b g), ⟨U, hUo, fun g hg u hu huH => ?_⟩, fun g hg h hh => ?_⟩
  · simp only [hU g hg u hu huH]
  · have key : pushFun2 e c g h
        = SSGRoute.res k K g • e (b h) - e (b (g * h)) + e (b g) := by
      simp only [pushFun2_apply, hbc g hg h hh, map_sub, map_add, he]
    exact key

/-- **Transport of the local `H²` along an equivariant linear map.** -/
def H2locPush (e : M →ₗ[ZMod p] M')
    (he : ∀ (g : K ≃ₐ[k] K) (m : M), e (g • m) = g • e m) :
    H2loc p k Ω K M H →ₗ[ZMod p] H2loc p k Ω K M' H :=
  Submodule.mapQ (Submodule.comap (lcCocycles2 p k Ω K M H).subtype (coboundaries2 p k Ω K M H))
    (Submodule.comap (lcCocycles2 p k Ω K M' H).subtype (coboundaries2 p k Ω K M' H))
    (pushCocycles2 e he)
    (by
      intro x hx
      rw [Submodule.mem_comap] at hx ⊢
      exact isCoboundary2On_pushFun2 e he hx)

/-- The class computation rule for `H2locPush`. -/
lemma H2locPush_mk (e : M →ₗ[ZMod p] M')
    (he : ∀ (g : K ≃ₐ[k] K) (m : M), e (g • m) = g • e m)
    (c : ↥(lcCocycles2 p k Ω K M H)) :
    H2locPush e he (Submodule.Quotient.mk c)
      = Submodule.Quotient.mk (pushCocycles2 e he c) :=
  Submodule.mapQ_apply _ _ _ c

/-- The inverse of an equivariant linear isomorphism is equivariant (in the same direction). -/
lemma linearEquiv_symm_equivariant2 (e : M ≃ₗ[ZMod p] M')
    (he : ∀ (g : K ≃ₐ[k] K) (m : M), e (g • m) = g • e m) :
    ∀ (g : K ≃ₐ[k] K) (m' : M'), e.symm (g • m') = g • e.symm m' := by
  intro g m'
  apply e.injective
  rw [he g (e.symm m'), LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]

/-- **The local `H²` is invariant under equivariant coefficient isomorphisms**: the push-forward is
a bijection, with inverse the push-forward along the inverse isomorphism. -/
theorem H2loc_card_eq_of_equiv (e : M ≃ₗ[ZMod p] M')
    (he : ∀ (g : K ≃ₐ[k] K) (m : M), e (g • m) = g • e m) :
    Nat.card (H2loc p k Ω K M H) = Nat.card (H2loc p k Ω K M' H) := by
  have hs := linearEquiv_symm_equivariant2 e he
  have key : ∀ y : H2loc p k Ω K M H,
      H2locPush e.symm.toLinearMap hs (H2locPush e.toLinearMap he y) = y := by
    intro y
    refine Submodule.Quotient.induction_on _ y (fun c => ?_)
    rw [H2locPush_mk, H2locPush_mk, Submodule.Quotient.eq]
    have h0 : pushCocycles2 e.symm.toLinearMap hs (pushCocycles2 e.toLinearMap he c) = c := by
      apply Subtype.ext
      ext g h
      simp
    rw [h0, sub_self]
    exact Submodule.zero_mem _
  have key' : ∀ y : H2loc p k Ω K M' H,
      H2locPush e.toLinearMap he (H2locPush e.symm.toLinearMap hs y) = y := by
    intro y
    refine Submodule.Quotient.induction_on _ y (fun c => ?_)
    rw [H2locPush_mk, H2locPush_mk, Submodule.Quotient.eq]
    have h0 : pushCocycles2 e.toLinearMap he (pushCocycles2 e.symm.toLinearMap hs c) = c := by
      apply Subtype.ext
      ext g h
      simp
    rw [h0, sub_self]
    exact Submodule.zero_mem _
  have hinj : Function.Injective (H2locPush (K := K) (H := H) (M := M) (M' := M')
      e.toLinearMap he) := by
    intro a b hab
    have h := key (a - b)
    simp only [map_sub, hab, sub_self, map_zero] at h
    exact sub_eq_zero.mp h.symm
  have hsurj : Function.Surjective (H2locPush (K := K) (H := H) (M := M) (M' := M')
      e.toLinearMap he) := fun b =>
    ⟨H2locPush (K := K) (H := H) (M := M') (M' := M) e.symm.toLinearMap hs b, key' b⟩
  exact Nat.card_congr (Equiv.ofBijective _ ⟨hinj, hsurj⟩)

end

end Work.SSGRoute
