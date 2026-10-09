import Mathlib
import Submission.Work.SSGRoute.PTDefs
import Submission.Work.SSGRoute.homRep
import Submission.Work.SSGRoute.ExtOnePre
import Submission.Work.SSGRoute.ExtOneSES
import Submission.Work.SSGRoute.ExtOneDefs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The dual short complex `Hom_ℤ(-, N)` is short exact for injective `N`

For a short exact short complex `S : 0 → X₁ → X₂ → X₃ → 0` in `Rep Coeff G` (`Coeff = ULift ℤ`)
and a representation `N` whose underlying `Coeff`-module is injective (equivalently divisible, over
the PID `ULift ℤ`), the contravariantly induced complex

`0 → Hom_ℤ(X₃, N) → Hom_ℤ(X₂, N) → Hom_ℤ(X₁, N) → 0`

(whose differentials are precomposition, `Work.SSGRoute.homRepPre`) is again short exact.

The mathematical content is the standard one: `Hom_ℤ(-, N)` is exact on `ℤ`-modules when `N` is
injective, and exactness in `Rep Coeff G` is detected on underlying `Coeff`-modules by the exact
faithful forgetful functor `Rep Coeff G ⥤ ModuleCat Coeff`.

## A note on the `ULift ℤ` instance diamond

The carrier of `homRep X N` is the `Coeff`-linear map type `X.V →ₗ[Coeff] N.V`, where the
`Module Coeff` instance arguments stored inside `homRep` are the canonical ones produced by type
class search for a bare type (`ULift.module` over the `ℤ`-action).  On the other hand the
`IntertwiningMap` underlying a `Rep.Hom` is typed with the *structure* instances `X.hV2`, `N.hV2`.
Both are the same `ℤ`-module structure on the same abelian group -- there is at most one, cf.
`Work.SSGRoute.subsingleton_moduleCoeff` -- but they are not syntactically equal.  Two small
bridges are used below:

* `hrscFunLike`, a `FunLike` instance for `IntertwiningMap`s pinned to the structure instances
  (needed because `ConcreteCategory (Rep Coeff G)` cannot otherwise be synthesized, which in turn
  makes `HasForget₂ (Rep Coeff G) (ModuleCat Coeff)` -- hence the forgetful functor -- available);
* `hrscCanon` / `hrscSmul_congr` / `hrscLmChange`, reinterpreting a `Coeff`-linear map in the other
  instance family without changing its underlying function (the same remedy as in
  `Submission.Work.SSGRoute.unitHomEquiv_exists`).
-/

open CategoryTheory SSGRoute.PTExt

namespace Work.SSGRoute

noncomputable section

variable {G : Type} [Group G]

/-- `FunLike` for the `IntertwiningMap`s of `Rep Coeff G`, with the module structures pinned to the
structure instances `X.hV2`.  Without this, `ConcreteCategory (Rep Coeff G) _` (and hence
`HasForget₂ (Rep Coeff G) (ModuleCat Coeff)`) cannot be synthesized for `Coeff = ULift ℤ`, because
type class search then produces the (equal but not syntactically identical) `ULift.module`
instance. -/
local instance hrscFunLike (X Y : Rep.{0} Coeff G) :
    @FunLike (@Representation.IntertwiningMap Coeff G X.V Y.V _ _ _ _ X.hV2 Y.hV2 X.ρ Y.ρ) X.V Y.V :=
  @Representation.IntertwiningMap.instFunLike Coeff G X.V Y.V _ _ _ _ X.hV2 Y.hV2 X.ρ Y.ρ

/-- The canonical `Coeff`-module structure on an additive commutative group: the one induced by the
`ℤ`-action through `ULift.module`.  This is what type class search produces for a type which is not
already known to be the carrier of a representation, and it is the structure stored inside
`homRep`. -/
@[instance_reducible] noncomputable def hrscCanon (M : Type) [AddCommGroup M] : Module Coeff M :=
  @ULift.module.{0,0,0} Int M Int.instSemiring _ _

/-- The scalar actions of two `Coeff`-module structures on the same additive commutative group
agree. -/
lemma hrscSmul_congr (M : Type) [AddCommGroup M] (P Q : Module Coeff M) (c : Coeff) (x : M) :
    @SMul.smul Coeff M P.toDistribMulAction.toSMul c x =
      @SMul.smul Coeff M Q.toDistribMulAction.toSMul c x := by
  haveI := subsingleton_moduleCoeff M
  rw [Subsingleton.elim P Q]

/-- The canonical family of `Coeff`-linear maps `M →ₗ N` (the one stored in `homRep X N` when
`M = X.V` and `N` is the coefficient module). -/
abbrev hrscCanLM (M N : Type) [AddCommGroup M] [AddCommGroup N] : Type :=
  @LinearMap.{0,0,0,0} Coeff Coeff _ _ (RingHom.id Coeff) M N _ _ (hrscCanon M) (hrscCanon N)

/-- The underlying additive homomorphism of a `Coeff`-linear map, with the module instances left
implicit. -/
abbrev hrscToAHom (M N : Type) [AddCommGroup M] [AddCommGroup N]
    (P : Module Coeff M) (Q : Module Coeff N)
    (f : @LinearMap.{0,0,0,0} Coeff Coeff _ _ (RingHom.id Coeff) M N _ _ P Q) : M →ₙ+ N :=
  @LinearMap.toAddHom Coeff Coeff _ _ (RingHom.id Coeff) M N _ _ P Q f

/-- Reinterpret a `Coeff`-linear map in a different pair of `Coeff`-module structures.  The
underlying function is unchanged; only the `map_smul'` field has to be redone, which is possible
because the scalar actions agree (`hrscSmul_congr`). -/
noncomputable def hrscLmChange {M N : Type} [AddCommGroup M] [AddCommGroup N]
    {P : Module Coeff M} {Q : Module Coeff N}
    (f : @LinearMap.{0,0,0,0} Coeff Coeff _ _ (RingHom.id Coeff) M N _ _ P Q)
    (P' : Module Coeff M) (Q' : Module Coeff N) :
    @LinearMap.{0,0,0,0} Coeff Coeff _ _ (RingHom.id Coeff) M N _ _ P' Q' :=
  @LinearMap.mk Coeff Coeff _ _ (RingHom.id Coeff) M N _ _ P' Q'
    (hrscToAHom M N P Q f)
    (fun c x => by
      have h1 : @AddHom.toFun M N _ _ (hrscToAHom M N P Q f)
            (@SMul.smul Coeff M P'.toDistribMulAction.toSMul c x) =
          @AddHom.toFun M N _ _ (hrscToAHom M N P Q f)
            (@SMul.smul Coeff M P.toDistribMulAction.toSMul c x) :=
        congrArg (@AddHom.toFun M N _ _ (hrscToAHom M N P Q f)) (hrscSmul_congr M P' P c x)
      have h2 := @LinearMap.map_smul' Coeff Coeff _ _ (RingHom.id Coeff) M N _ _ P Q f c x
      have h3 : @SMul.smul Coeff N Q.toDistribMulAction.toSMul ((RingHom.id Coeff) c)
            (@AddHom.toFun M N _ _ (hrscToAHom M N P Q f) x) =
          @SMul.smul Coeff N Q'.toDistribMulAction.toSMul ((RingHom.id Coeff) c)
            (@AddHom.toFun M N _ _ (hrscToAHom M N P Q f) x) :=
        hrscSmul_congr N Q Q' ((RingHom.id Coeff) c)
          (@AddHom.toFun M N _ _ (hrscToAHom M N P Q f) x)
      exact h1.trans (h2.trans h3))

@[simp] lemma hrscLmChange_apply {M N : Type} [AddCommGroup M] [AddCommGroup N]
    {P : Module Coeff M} {Q : Module Coeff N}
    (f : @LinearMap.{0,0,0,0} Coeff Coeff _ _ (RingHom.id Coeff) M N _ _ P Q)
    (P' : Module Coeff M) (Q' : Module Coeff N) (x : M) :
    hrscLmChange f P' Q' x = f x := rfl

/-- An element of `(homRep X N).V` (the canonical instance family) read as a `Coeff`-linear map in
the canonical family. -/
abbrev hrscHM (X N : Rep.{0} Coeff G) (w : (homRep X N).V) : hrscCanLM X.V N.V :=
  show hrscCanLM X.V N.V from w

/-- A `Coeff`-linear map in the canonical family, read as an element of `(homRep X N).V`. -/
abbrev hrscMH (X N : Rep.{0} Coeff G) (v : hrscCanLM X.V N.V) : (homRep X N).V :=
  show (homRep X N).V from v

/-- `hrscHM` is injective (it is essentially the identity). -/
lemma hrscHM_injective (X N : Rep.{0} Coeff G) : Function.Injective (hrscHM X N) := fun _ _ h => h

/-- The forgetful functor `Rep Coeff G ⥤ ModuleCat Coeff` (forgetting the `G`-action). -/
abbrev repForget : Rep.{0} Coeff G ⥤ ModuleCat Coeff := forget₂ _ _

/-- **The dual short complex of a short exact complex is short exact for injective coefficients.**
For `S : 0 → X₁ → X₂ → X₃ → 0` short exact in `Rep Coeff G` and `N.V` an injective
(= divisible) `Coeff`-module, the precomposition complex
`0 → Hom(X₃,N) → Hom(X₂,N) → Hom(X₁,N) → 0` is short exact. -/
theorem homRepShortComplex_shortExact (G : Type) [Group G]
    (S : CategoryTheory.ShortComplex (Rep.{0} SSGRoute.PTExt.Coeff G))
    (hS : CategoryTheory.ShortComplex.ShortExact S)
    (N : Rep.{0} SSGRoute.PTExt.Coeff G)
    (hInj : Module.Injective SSGRoute.PTExt.Coeff N.V) :
    CategoryTheory.ShortComplex.ShortExact (Work.SSGRoute.homRepShortComplex S N) := by
  have hSmap : (S.map repForget).ShortExact := hS.map_of_exact repForget
  -- the two differentials of `S`, and the elementwise facts about them
  have hsurjV : Function.Surjective ⇑(S.map repForget).g :=
    (ModuleCat.epi_iff_surjective ((S.map repForget).g)).1 hSmap.epi_g
  have hinjV : Function.Injective ⇑(S.map repForget).f :=
    (ModuleCat.mono_iff_injective ((S.map repForget).f)).1 hSmap.mono_f
  have hexV : ∀ y : S.X₂.V, (⇑(S.map repForget).g) y = 0 →
      ∃ x : S.X₁.V, (⇑(S.map repForget).f) x = y :=
    (ShortComplex.moduleCat_exact_iff (S.map repForget)).1 hSmap.exact
  have sf_apply : ∀ x : S.X₁.V, ⇑(S.map repForget).f x = ⇑(Rep.Hom.hom S.f) x := fun x => rfl
  have sg_apply : ∀ x : S.X₂.V, ⇑(S.map repForget).g x = ⇑(Rep.Hom.hom S.g) x := fun x => rfl
  -- the same maps, transported to the canonical family (the one stored in `homRep`)
  let fC : hrscCanLM S.X₁.V S.X₂.V :=
    hrscLmChange (S.map repForget).f.hom (hrscCanon S.X₁.V) (hrscCanon S.X₂.V)
  let gC : hrscCanLM S.X₂.V S.X₃.V :=
    hrscLmChange (S.map repForget).g.hom (hrscCanon S.X₂.V) (hrscCanon S.X₃.V)
  have fC_apply : ∀ x : S.X₁.V, fC x = (⇑(S.map repForget).f) x := fun x => rfl
  have gC_apply : ∀ x : S.X₂.V, gC x = (⇑(S.map repForget).g) x := fun x => rfl
  have sfC : ∀ x : S.X₁.V, ⇑(Rep.Hom.hom S.f) x = fC x := fun x => rfl
  have sgC : ∀ x : S.X₂.V, ⇑(Rep.Hom.hom S.g) x = gC x := fun x => rfl
  have hinjC : Function.Injective fC := fun a b h => hinjV (by rw [← fC_apply a, ← fC_apply b, h])
  have hsurjC : Function.Surjective gC := fun y => by
    obtain ⟨x, hx⟩ := hsurjV y
    refine ⟨(show S.X₂.V from x), ?_⟩
    rw [gC_apply]
    exact hx
  have hexC : ∀ y : S.X₂.V, gC y = 0 → ∃ x : S.X₁.V, fC x = y := by
    intro y hy
    rw [gC_apply] at hy
    obtain ⟨x, hx⟩ := hexV y hy
    exact ⟨(show S.X₁.V from x), by rw [fC_apply]; exact hx⟩
  refine { exact := ?_, mono_f := ?_, epi_g := ?_ }
  · -- exactness at the middle term of the dual complex
    refine (forget₂ (Rep.{0} Coeff G) (ModuleCat Coeff)).reflects_exact_of_faithful _ ?_
    rw [ShortComplex.moduleCat_exact_iff]
    intro (ψ : (homRep S.X₂ N).V) hψ
    have hψ0 : (Rep.Hom.hom (homRepPre S.X₂ S.X₁ N S.f)) ψ = 0 := hψ
    have hkill : ∀ x : S.X₁.V, (hrscHM S.X₂ N ψ) (fC x) = 0 := by
      intro x
      have h1 : (hrscHM S.X₁ N ((Rep.Hom.hom (homRepPre S.X₂ S.X₁ N S.f)) ψ)) x = 0 := by
        rw [hψ0]
        show (0 : hrscCanLM S.X₁.V N.V) x = 0
        simp
      have hCB : (hrscHM S.X₂ N ψ) (fC x) = (hrscHM S.X₂ N ψ) (⇑(Rep.Hom.hom S.f) x) := by
        rw [← sfC x]
      exact hCB.trans ((homRepPre_apply S.X₂ S.X₁ N S.f ψ x).symm.trans h1)
    have hle : LinearMap.ker gC ≤ LinearMap.ker (hrscHM S.X₂ N ψ) := by
      intro y hy
      obtain ⟨x, rfl⟩ := hexC y hy
      exact hkill x
    let ψ' : hrscCanLM S.X₃.V N.V := ((LinearMap.ker gC).liftQ (hrscHM S.X₂ N ψ) hle).comp
      (gC.quotKerEquivOfSurjective hsurjC).symm.toLinearMap
    refine ⟨hrscMH S.X₃ N ψ', ?_⟩
    rw [show ((homRepShortComplex S N).map repForget).f (hrscMH S.X₃ N ψ')
        = (Rep.Hom.hom (homRepPre S.X₃ S.X₂ N S.g)) (hrscMH S.X₃ N ψ') from rfl]
    apply hrscHM_injective S.X₂ N
    apply LinearMap.ext
    intro x
    have h3 : (hrscHM S.X₂ N ((Rep.Hom.hom (homRepPre S.X₃ S.X₂ N S.g))
          (hrscMH S.X₃ N ψ'))) x
        = (hrscHM S.X₃ N (hrscMH S.X₃ N ψ')) (⇑(Rep.Hom.hom S.g) x) :=
      homRepPre_apply S.X₃ S.X₂ N S.g (hrscMH S.X₃ N ψ') x
    have hCB : (hrscHM S.X₃ N (hrscMH S.X₃ N ψ')) (⇑(Rep.Hom.hom S.g) x)
        = (hrscHM S.X₃ N (hrscMH S.X₃ N ψ')) (gC x) := by rw [sgC x]
    have h4 : (hrscHM S.X₃ N (hrscMH S.X₃ N ψ')) (gC x) = ψ' (gC x) := rfl
    have h5 : ψ' (gC x) = (hrscHM S.X₂ N ψ) x := by
      show (LinearMap.ker gC).liftQ (hrscHM S.X₂ N ψ) hle
        ((gC.quotKerEquivOfSurjective hsurjC).symm (gC x)) = (hrscHM S.X₂ N ψ) x
      rw [LinearMap.quotKerEquivOfSurjective_symm_apply]
      exact Submodule.liftQ_apply (LinearMap.ker gC) (hrscHM S.X₂ N ψ) x
    exact h3.trans (hCB.trans (h4.trans h5))
  · -- precomposition with the epimorphism `S.g` is injective
    rw [homRepShortComplex_f]
    refine (Rep.mono_iff_injective _).2 ?_
    intro ψ₁ ψ₂ h
    apply hrscHM_injective S.X₃ N
    apply LinearMap.ext
    intro y
    obtain ⟨x, rfl⟩ := hsurjV y
    rw [sg_apply x]
    have hpt : (hrscHM S.X₂ N ((Rep.Hom.hom (homRepPre S.X₃ S.X₂ N S.g)) ψ₁)) x
        = (hrscHM S.X₂ N ((Rep.Hom.hom (homRepPre S.X₃ S.X₂ N S.g)) ψ₂)) x :=
      congrArg (fun ξ => (hrscHM S.X₂ N ξ) x) h
    exact (homRepPre_apply S.X₃ S.X₂ N S.g ψ₁ x).symm.trans (hpt.trans
      (homRepPre_apply S.X₃ S.X₂ N S.g ψ₂ x))
  · -- precomposition with the monomorphism `S.f` is surjective, `N` being injective
    rw [homRepShortComplex_g]
    refine (Rep.epi_iff_surjective _).2 ?_
    intro φ
    obtain ⟨ψ, hψ⟩ := hInj.out fC hinjC (hrscHM S.X₁ N φ)
    refine ⟨hrscMH S.X₂ N ψ, ?_⟩
    apply hrscHM_injective S.X₁ N
    apply LinearMap.ext
    intro x
    have h3 : (hrscHM S.X₁ N ((Rep.Hom.hom (homRepPre S.X₂ S.X₁ N S.f))
          (hrscMH S.X₂ N ψ))) x
        = (hrscHM S.X₂ N (hrscMH S.X₂ N ψ)) (⇑(Rep.Hom.hom S.f) x) :=
      homRepPre_apply S.X₂ S.X₁ N S.f (hrscMH S.X₂ N ψ) x
    have hCB : (hrscHM S.X₂ N (hrscMH S.X₂ N ψ)) (⇑(Rep.Hom.hom S.f) x)
        = (hrscHM S.X₂ N (hrscMH S.X₂ N ψ)) (fC x) := by rw [← sfC x]
    have h4 : (hrscHM S.X₂ N (hrscMH S.X₂ N ψ)) (fC x) = ψ (fC x) := rfl
    exact h3.trans (hCB.trans (h4.trans (hψ x)))

end

end Work.SSGRoute
