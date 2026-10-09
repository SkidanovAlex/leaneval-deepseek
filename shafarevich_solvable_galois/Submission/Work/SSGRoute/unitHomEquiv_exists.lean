import Mathlib
import Submission.Work.SSGRoute.PTDefs
import Submission.Work.SSGRoute.homRep
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Hom_G(ℤ, Hom_ℤ(X, N)) ≅ Hom_G(X, N)` — evaluation at `1`

For `X N : Rep Coeff G` (`Coeff = ULift ℤ`) there is an additive equivalence

`(unitRep G ⟶ homRep X N) ≃+ (X ⟶ N)`

whose forward map is *evaluation at `1`*: a `ℤ[G]`-linear map `ℤ → Hom_ℤ(X,N)` is the same thing
as a `G`-invariant `ℤ`-linear map `X → N`, i.e. a morphism `X ⟶ N`.

## Formalisation note (the `Coe` coercion used by the statement)

The statement writes the coercion `(e φ).hom` to a `LinearMap` as
`show X.V →ₗ[Coeff] N.V from (e φ).hom`.  `Rep.Hom.hom` is an
`Representation.IntertwiningMap`, a `FunLike`/`LinearMapClass` element which Mathlib does **not**
register as a `Coe` coercion to `LinearMap`; *locally* (at the end of this file, just before the
theorem) the missing coercion is registered as `coeIntertwiningMapToLinearMapCoeff`.  It sends an
intertwining map to its underlying `Coeff`-linear map, reinterpreted in the instance family of the
target type by `uhLmChangeGen`, which leaves the underlying *function* unchanged (lemma
`coeIntertwiningMapToLinearMapCoeff_apply`).  Thus both `show`s in the statement mean exactly "the
underlying function of the given morphism / element", evaluated at the given point, and the theorem
proves the formula for the equivalence `evalOneEquiv` built below.

## Formalisation note (the `ULift ℤ` instance diamond)

The carrier of `homRep X N` is the `LinearMap` type `X.V →ₗ[Coeff] N.V` whose `Module Coeff`
instance arguments, as stored inside `homRep`, are the canonical ones produced by type class search
for a bare type (`ULift.module` over the `ℤ`-action), while the `IntertwiningMap` underlying a
`Rep.Hom X N` is typed with the *structure* instances `X.hV2`, `N.hV2`.  These are the same
`ℤ`-module structure on the same abelian group -- all `Coeff`-module structures on an abelian group
coincide -- but they are not definitionally equal.  The little bridge below (`uhCanon`,
`uhModuleCoeff_subsingleton`, `uhLmChange`) reinterprets a `Coeff`-linear map in the other instance
family without changing its underlying additive homomorphism; it is the standard remedy used
elsewhere in this workspace.
-/

namespace Work.SSGRoute

open SSGRoute.PTExt

noncomputable section

variable {G : Type} [Group G]

/-! ## The `Coeff = ULift ℤ` instance bridge -/

/-- The canonical `Coeff = ULift ℤ`-module structure on an additive commutative group, i.e. the one
obtained from the `ℤ`-action via `ULift.module`.  This is the `Module` instance that type class
search produces for a type which is not already a `Rep`'s carrier. -/
noncomputable def uhCanon (M : Type) [AddCommGroup M] : Module SSGRoute.PTExt.Coeff M :=
  @ULift.module.{0,0,0} Int M Int.instSemiring _ _

/-- All `Coeff = ULift ℤ`-module structures on an additive commutative group coincide. -/
lemma uhModuleCoeff_subsingleton (M : Type) [AddCommGroup M] :
    Subsingleton (Module SSGRoute.PTExt.Coeff M) := by
  constructor
  intro P Q
  apply Module.ext
  funext r m
  obtain ⟨k⟩ := r
  have hP : P.smul (ULift.up k) m = k • m := by
    letI := P
    rw [← Int.cast_smul_eq_zsmul (R := ULift ℤ) k m]
    rfl
  have hQ : Q.smul (ULift.up k) m = k • m := by
    letI := Q
    rw [← Int.cast_smul_eq_zsmul (R := ULift ℤ) k m]
    rfl
  exact hP.trans hQ.symm

/-- The scalar actions of two `Coeff`-module structures on the same additive commutative group
agree. -/
lemma uhSmul_congr (M : Type) [AddCommGroup M]
    (P Q : Module SSGRoute.PTExt.Coeff M) (c : SSGRoute.PTExt.Coeff) (x : M) :
    @SMul.smul SSGRoute.PTExt.Coeff M P.toDistribMulAction.toSMul c x =
      @SMul.smul SSGRoute.PTExt.Coeff M Q.toDistribMulAction.toSMul c x := by
  haveI := uhModuleCoeff_subsingleton M
  rw [Subsingleton.elim P Q]

/-- The underlying additive homomorphism of a `Coeff`-linear map, with the module instances of the
`LinearMap` type left implicit. -/
abbrev uhToAHom (X N : Rep.{0} SSGRoute.PTExt.Coeff G)
    (P : Module SSGRoute.PTExt.Coeff X.V) (Q : Module SSGRoute.PTExt.Coeff N.V)
    (f : @LinearMap.{0,0,0,0} SSGRoute.PTExt.Coeff SSGRoute.PTExt.Coeff _ _
            (RingHom.id SSGRoute.PTExt.Coeff) X.V N.V _ _ P Q) : X.V →ₙ+ N.V :=
  @LinearMap.toAddHom SSGRoute.PTExt.Coeff SSGRoute.PTExt.Coeff _ _
    (RingHom.id SSGRoute.PTExt.Coeff) X.V N.V _ _ P Q f

/-- Reinterpret a `Coeff`-linear map `X.V →ₗ N.V` in a different pair of `Coeff`-module
structures.  The underlying function is unchanged; only the `map_smul'` field has to be redone,
which is possible because the scalar actions agree (`uhSmul_congr`). -/
noncomputable def uhLmChange (X N : Rep.{0} SSGRoute.PTExt.Coeff G)
    (P : Module SSGRoute.PTExt.Coeff X.V) (Q : Module SSGRoute.PTExt.Coeff N.V)
    (P' : Module SSGRoute.PTExt.Coeff X.V) (Q' : Module SSGRoute.PTExt.Coeff N.V)
    (f : @LinearMap.{0,0,0,0} SSGRoute.PTExt.Coeff SSGRoute.PTExt.Coeff _ _
            (RingHom.id SSGRoute.PTExt.Coeff) X.V N.V _ _ P Q) :
    @LinearMap.{0,0,0,0} SSGRoute.PTExt.Coeff SSGRoute.PTExt.Coeff _ _
            (RingHom.id SSGRoute.PTExt.Coeff) X.V N.V _ _ P' Q' :=
  @LinearMap.mk SSGRoute.PTExt.Coeff SSGRoute.PTExt.Coeff _ _
    (RingHom.id SSGRoute.PTExt.Coeff) X.V N.V _ _ P' Q'
    (uhToAHom X N P Q f)
    (fun c x => by
      have h1 : @AddHom.toFun X.V N.V _ _ (uhToAHom X N P Q f)
            (@SMul.smul SSGRoute.PTExt.Coeff X.V P'.toDistribMulAction.toSMul c x) =
          @AddHom.toFun X.V N.V _ _ (uhToAHom X N P Q f)
            (@SMul.smul SSGRoute.PTExt.Coeff X.V P.toDistribMulAction.toSMul c x) :=
        congrArg (@AddHom.toFun X.V N.V _ _ (uhToAHom X N P Q f))
          (uhSmul_congr X.V P' P c x)
      have h2 := @LinearMap.map_smul' SSGRoute.PTExt.Coeff SSGRoute.PTExt.Coeff _ _
        (RingHom.id SSGRoute.PTExt.Coeff) X.V N.V _ _ P Q f c x
      have h3 : @SMul.smul SSGRoute.PTExt.Coeff N.V Q.toDistribMulAction.toSMul
            ((RingHom.id SSGRoute.PTExt.Coeff) c)
            (@AddHom.toFun X.V N.V _ _ (uhToAHom X N P Q f) x) =
          @SMul.smul SSGRoute.PTExt.Coeff N.V Q'.toDistribMulAction.toSMul
            ((RingHom.id SSGRoute.PTExt.Coeff) c)
            (@AddHom.toFun X.V N.V _ _ (uhToAHom X N P Q f) x) :=
        uhSmul_congr N.V Q Q' ((RingHom.id SSGRoute.PTExt.Coeff) c)
          (@AddHom.toFun X.V N.V _ _ (uhToAHom X N P Q f) x)
      exact h1.trans (h2.trans h3))

/-- Two `Coeff`-linear maps with the same underlying additive homomorphism are equal. -/
lemma uhLmExt (X N : Rep.{0} SSGRoute.PTExt.Coeff G)
    (P : Module SSGRoute.PTExt.Coeff X.V) (Q : Module SSGRoute.PTExt.Coeff N.V)
    {f g : @LinearMap.{0,0,0,0} SSGRoute.PTExt.Coeff SSGRoute.PTExt.Coeff _ _
            (RingHom.id SSGRoute.PTExt.Coeff) X.V N.V _ _ P Q}
    (h : uhToAHom X N P Q f = uhToAHom X N P Q g) : f = g := by
  cases f; cases g
  simp only [uhToAHom] at h
  subst h
  rfl

/-! ## Reading the carrier of `homRep` in the two instance families -/

/-- An element of `(homRep X N).V` (the canonical instance family) read as a `Coeff`-linear map in
the canonical family `X.V →ₗ[Coeff] N.V`. -/
abbrev hmLM (X N : Rep.{0} SSGRoute.PTExt.Coeff G) (w : (homRep X N).V) :
    X.V →ₗ[SSGRoute.PTExt.Coeff] N.V :=
  show X.V →ₗ[SSGRoute.PTExt.Coeff] N.V from w

/-- A `Coeff`-linear map in the canonical family, read as an element of `(homRep X N).V`. -/
abbrev lmHM (X N : Rep.{0} SSGRoute.PTExt.Coeff G) (v : X.V →ₗ[SSGRoute.PTExt.Coeff] N.V) :
    (homRep X N).V :=
  show (homRep X N).V from v

/-- The `hV2`-instance family of `Coeff`-linear maps `X.V → N.V`: the family in which
`Rep.Hom X N` and Mathlib's internal hom `(Rep.ihom X).obj N` live. -/
abbrev hV2LM (X N : Rep.{0} SSGRoute.PTExt.Coeff G) : Type :=
  @LinearMap.{0,0,0,0} SSGRoute.PTExt.Coeff SSGRoute.PTExt.Coeff _ _
    (RingHom.id SSGRoute.PTExt.Coeff) X.V N.V _ _
    X.hV2 N.hV2

/-- The canonical family is the one stored in `homRep`, so `hmLM` is the identity on elements. -/
lemma hmLM_injective (X N : Rep.{0} SSGRoute.PTExt.Coeff G) :
    Function.Injective (hmLM X N) := by
  intro u v h
  exact h

/-- Canonical family ⟶ `hV2` family (the family of `Rep.Hom`). -/
noncomputable def toHV2 (X N : Rep.{0} SSGRoute.PTExt.Coeff G) (w : (homRep X N).V) :
    hV2LM X N :=
  uhLmChange X N (uhCanon X.V) (uhCanon N.V) X.hV2 N.hV2 w

/-- `hV2` family ⟶ canonical family. -/
noncomputable def toCanon (X N : Rep.{0} SSGRoute.PTExt.Coeff G) (v : hV2LM X N) :
    (homRep X N).V :=
  uhLmChange X N X.hV2 N.hV2 (uhCanon X.V) (uhCanon N.V) v

lemma toHV2_apply (X N : Rep.{0} SSGRoute.PTExt.Coeff G) (w : (homRep X N).V) (x : X.V) :
    (toHV2 X N w) x = (hmLM X N w) x := rfl

lemma toCanon_apply (X N : Rep.{0} SSGRoute.PTExt.Coeff G) (v : hV2LM X N) (x : X.V) :
    (hmLM X N (toCanon X N v)) x = v x := rfl

/-- The round trip `hV2 → canonical → hV2` is the identity. -/
lemma toHV2_toCanon (X N : Rep.{0} SSGRoute.PTExt.Coeff G) (v : hV2LM X N) :
    toHV2 X N (toCanon X N v) = v := by
  apply uhLmExt X N X.hV2 N.hV2
  rfl

/-- The round trip `canonical → hV2 → canonical` is the identity. -/
lemma toCanon_toHV2 (X N : Rep.{0} SSGRoute.PTExt.Coeff G) (w : (homRep X N).V) :
    toCanon X N (toHV2 X N w) = w := by
  apply hmLM_injective X N
  apply uhLmExt X N (uhCanon X.V) (uhCanon N.V)
  rfl

/-! ## Evaluation at `1` -/

/-- `φ.hom (1 : Coeff) ∈ (homRep X N).V`. -/
def evalOne (X N : Rep.{0} SSGRoute.PTExt.Coeff G)
    (φ : SSGRoute.PTExt.unitRep G ⟶ homRep X N) : (homRep X N).V :=
  φ.hom (1 : SSGRoute.PTExt.Coeff)

/-- The evaluation of a morphism `unitRep G ⟶ homRep X N` at `1` is `G`-invariant. -/
lemma evalOne_invariant (X N : Rep.{0} SSGRoute.PTExt.Coeff G)
    (φ : SSGRoute.PTExt.unitRep G ⟶ homRep X N) (g : G) :
    (homRep X N).ρ g (evalOne X N φ) = evalOne X N φ := by
  show (homRep X N).ρ g (φ.hom (1 : SSGRoute.PTExt.Coeff)) = φ.hom (1 : SSGRoute.PTExt.Coeff)
  rw [← Rep.hom_comm_apply φ g (1 : SSGRoute.PTExt.Coeff)]
  rfl

/-- Value-level description of the action on `homRep X N`. -/
lemma hmLM_rho (X N : Rep.{0} SSGRoute.PTExt.Coeff G) (g : G) (w : (homRep X N).V) (x : X.V) :
    (hmLM X N ((homRep X N).ρ g w)) x = N.ρ g ((hmLM X N w) (X.ρ g⁻¹ x)) := rfl

/-- The evaluation at `1` of `φ` intertwines. -/
lemma evalOne_step (X N : Rep.{0} SSGRoute.PTExt.Coeff G)
    (φ : SSGRoute.PTExt.unitRep G ⟶ homRep X N) (g : G) (x : X.V) :
    (hmLM X N (evalOne X N φ)) (X.ρ g x) = N.ρ g ((hmLM X N (evalOne X N φ)) x) := by
  have h := LinearMap.congr_fun (congrArg (hmLM X N) (evalOne_invariant X N φ g)) (X.ρ g x)
  rw [hmLM_rho] at h
  rw [show X.ρ g⁻¹ (X.ρ g x) = x from by simp] at h
  exact h.symm
/-- Additivity of `toHV2`. -/
lemma toHV2_add (X N : Rep.{0} SSGRoute.PTExt.Coeff G) (u v : (homRep X N).V) :
    toHV2 X N (u + v) = toHV2 X N u + toHV2 X N v := by
  apply uhLmExt X N X.hV2 N.hV2
  rfl

/-- Additivity of `toCanon`. -/
lemma toCanon_add (X N : Rep.{0} SSGRoute.PTExt.Coeff G) (u v : hV2LM X N) :
    toCanon X N (u + v) = toCanon X N u + toCanon X N v := by
  apply hmLM_injective X N
  apply uhLmExt X N (uhCanon X.V) (uhCanon N.V)
  rfl

/-! ## The two directions -/

/-- `X.ρ` with the module instance of the `Rep` structure made explicit. -/
abbrev rhoHV2 (A : Rep.{0} SSGRoute.PTExt.Coeff G) :
    @Representation SSGRoute.PTExt.Coeff G A.V _ _ _ A.hV2 := A.ρ

/-- The `hV2`-instance family of intertwining maps `X → N`. -/
abbrev IMapHV2 (X N : Rep.{0} SSGRoute.PTExt.Coeff G) : Type :=
  @Representation.IntertwiningMap SSGRoute.PTExt.Coeff G X.V N.V _ _ _ _
    X.hV2 N.hV2 (rhoHV2 X) (rhoHV2 N)

/-- The canonical-instance family of `Coeff`-linear maps `↑(unitRep G) → ↑(homRep X N)`. -/
abbrev spanFamily (X N : Rep.{0} SSGRoute.PTExt.Coeff G) : Type :=
  @LinearMap.{0,0,0,0} SSGRoute.PTExt.Coeff SSGRoute.PTExt.Coeff _ _ (RingHom.id _)
    (↑(SSGRoute.PTExt.unitRep G)) (↑(homRep X N)) _ _
    (SSGRoute.PTExt.unitRep G).hV2 (homRep X N).hV2

/-- The canonical-instance family of intertwining maps `unitRep G → homRep X N`. -/
abbrev IMapUnit (X N : Rep.{0} SSGRoute.PTExt.Coeff G) : Type :=
  @Representation.IntertwiningMap SSGRoute.PTExt.Coeff G (↑(SSGRoute.PTExt.unitRep G))
    (↑(homRep X N)) _ _ _ _ (SSGRoute.PTExt.unitRep G).hV2 (homRep X N).hV2
    (rhoHV2 (SSGRoute.PTExt.unitRep G)) (rhoHV2 (homRep X N))

/-- The `hV2`-linear map underlying `f : X ⟶ N`, read off the intertwining map carried by
`f` with the module instances of the `Rep` structures made explicit. -/
noncomputable def homHV2 (X N : Rep.{0} SSGRoute.PTExt.Coeff G) (f : X ⟶ N) :
    hV2LM X N :=
  @Representation.IntertwiningMap.toLinearMap SSGRoute.PTExt.Coeff G X.V N.V _ _ _ _
    X.hV2 N.hV2 (rhoHV2 X) (rhoHV2 N) (Rep.Hom.hom f)

/-- The underlying function of `homHV2 X N f` is that of `f`. -/
lemma homHV2_apply (X N : Rep.{0} SSGRoute.PTExt.Coeff G) (f : X ⟶ N) (x : X.V) :
    homHV2 X N f x = f.hom x := rfl

/-- The canonically-instanced version of `f : X ⟶ N` (an element of `homRep X N`). -/
noncomputable def homCanon (X N : Rep.{0} SSGRoute.PTExt.Coeff G) (f : X ⟶ N) :
    (homRep X N).V :=
  toCanon X N (homHV2 X N f)

/-- `f : X ⟶ N` is invariant under the conjugation action of `homRep X N`. -/
lemma rho_toCanon (X N : Rep.{0} SSGRoute.PTExt.Coeff G) (f : X ⟶ N) (g : G) :
    (homRep X N).ρ g (homCanon X N f) = homCanon X N f := by
  apply hmLM_injective X N
  apply LinearMap.ext
  intro x
  rw [hmLM_rho]
  show N.ρ g (homHV2 X N f (X.ρ g⁻¹ x)) = homHV2 X N f x
  have key : homHV2 X N f (X.ρ g (X.ρ g⁻¹ x))
      = N.ρ g (homHV2 X N f (X.ρ g⁻¹ x)) := Rep.hom_comm_apply f g (X.ρ g⁻¹ x)
  rw [show X.ρ g (X.ρ g⁻¹ x) = x from by simp] at key
  exact key.symm

/-- The `hV2`-intertwining map underlying the forward direction. -/
noncomputable def toIMap (X N : Rep.{0} SSGRoute.PTExt.Coeff G)
    (φ : SSGRoute.PTExt.unitRep G ⟶ homRep X N) : IMapHV2 X N :=
  @LinearMap.intertwiningMap_of_isIntertwiningMap SSGRoute.PTExt.Coeff G X.V N.V _ _ _ _
    X.hV2 N.hV2 (rhoHV2 X) (rhoHV2 N) (toHV2 X N (evalOne X N φ))
    (fun g x => by
      show toHV2 X N (evalOne X N φ) (rhoHV2 X g x)
        = rhoHV2 N g (toHV2 X N (evalOne X N φ) x)
      exact evalOne_step X N φ g x)

/-- The forward direction: a morphism `unitRep G ⟶ homRep X N` is an invariant element, i.e. a
morphism `X ⟶ N`. -/
noncomputable def toHom (X N : Rep.{0} SSGRoute.PTExt.Coeff G)
    (φ : SSGRoute.PTExt.unitRep G ⟶ homRep X N) : X ⟶ N :=
  @Rep.ofHom SSGRoute.PTExt.Coeff G _ _ X.V N.V X.hV1 N.hV1 X.hV2 N.hV2
    (rhoHV2 X) (rhoHV2 N) (toIMap X N φ)

lemma toHom_hom_apply (X N : Rep.{0} SSGRoute.PTExt.Coeff G)
    (φ : SSGRoute.PTExt.unitRep G ⟶ homRep X N) (x : X.V) :
    (Rep.Hom.hom (toHom X N φ)) x = toHV2 X N (evalOne X N φ) x := rfl

lemma homHV2_toHom (X N : Rep.{0} SSGRoute.PTExt.Coeff G)
    (φ : SSGRoute.PTExt.unitRep G ⟶ homRep X N) :
    homHV2 X N (toHom X N φ) = toHV2 X N (evalOne X N φ) := by
  apply uhLmExt X N X.hV2 N.hV2
  rfl

lemma homCanon_toHom (X N : Rep.{0} SSGRoute.PTExt.Coeff G)
    (φ : SSGRoute.PTExt.unitRep G ⟶ homRep X N) :
    homCanon X N (toHom X N φ) = evalOne X N φ := by
  show toCanon X N (homHV2 X N (toHom X N φ)) = evalOne X N φ
  rw [homHV2_toHom, toCanon_toHV2]

/-- `c ↦ c • w` on `↑(unitRep G) → ↑(homRep X N)`, in the canonical family. -/
noncomputable def spanHV2 (X N : Rep.{0} SSGRoute.PTExt.Coeff G) (w : (homRep X N).V) :
    spanFamily X N :=
  uhLmChange (SSGRoute.PTExt.unitRep G) (homRep X N) Semiring.toModule ULift.module
    (SSGRoute.PTExt.unitRep G).hV2 (homRep X N).hV2
    (LinearMap.toSpanSingleton SSGRoute.PTExt.Coeff (↑(homRep X N)) w)

lemma spanHV2_apply (X N : Rep.{0} SSGRoute.PTExt.Coeff G) (w : (homRep X N).V)
    (c : ↑(SSGRoute.PTExt.unitRep G)) :
    spanHV2 X N w c = c • w := by
  show (LinearMap.toSpanSingleton SSGRoute.PTExt.Coeff (↑(homRep X N)) w) c = c • w
  rw [LinearMap.toSpanSingleton_apply]

/-- The action of `homRep X N` is `Coeff`-linear. -/
lemma rho_smul (X N : Rep.{0} SSGRoute.PTExt.Coeff G) (g : G) (c : SSGRoute.PTExt.Coeff)
    (w : (homRep X N).V) :
    (homRep X N).ρ g (c • w) = c • ((homRep X N).ρ g w) :=
  LinearMap.map_smul ((homRep X N).ρ g) c w

/-- The intertwining map underlying the backward direction. -/
noncomputable def ofIMap (X N : Rep.{0} SSGRoute.PTExt.Coeff G) (f : X ⟶ N) : IMapUnit X N :=
  @LinearMap.intertwiningMap_of_isIntertwiningMap SSGRoute.PTExt.Coeff G
    (↑(SSGRoute.PTExt.unitRep G)) (↑(homRep X N)) _ _ _ _
    (SSGRoute.PTExt.unitRep G).hV2 (homRep X N).hV2
    (rhoHV2 (SSGRoute.PTExt.unitRep G)) (rhoHV2 (homRep X N))
    (spanHV2 X N (homCanon X N f))
    (fun g c => by
      have h1 : rhoHV2 (SSGRoute.PTExt.unitRep G) g c = c := rfl
      have h2 : spanHV2 X N (homCanon X N f) c = c • homCanon X N f :=
        spanHV2_apply X N (homCanon X N f) c
      have h3 : rhoHV2 (homRep X N) g (c • homCanon X N f)
          = c • rhoHV2 (homRep X N) g (homCanon X N f) :=
        rho_smul X N g c (homCanon X N f)
      have h4 : rhoHV2 (homRep X N) g (homCanon X N f) = homCanon X N f :=
        rho_toCanon X N f g
      show spanHV2 X N (homCanon X N f) (rhoHV2 (SSGRoute.PTExt.unitRep G) g c)
        = rhoHV2 (homRep X N) g (spanHV2 X N (homCanon X N f) c)
      rw [h1, h2, h3, h4])

/-- The backward direction: a morphism `X ⟶ N` gives the morphism
`unitRep G ⟶ homRep X N`, `c ↦ c • f`. -/
noncomputable def ofHom' (X N : Rep.{0} SSGRoute.PTExt.Coeff G) (f : X ⟶ N) :
    SSGRoute.PTExt.unitRep G ⟶ homRep X N :=
  Rep.ofHom (ofIMap X N f)

lemma ofHom'_hom_apply (X N : Rep.{0} SSGRoute.PTExt.Coeff G) (f : X ⟶ N)
    (c : ↑(SSGRoute.PTExt.unitRep G)) :
    (Rep.Hom.hom (ofHom' X N f)) c = spanHV2 X N (homCanon X N f) c := rfl

/-! ## The two inverse laws and additivity -/

lemma toHom_ofHom' (X N : Rep.{0} SSGRoute.PTExt.Coeff G) (f : X ⟶ N) :
    toHom X N (ofHom' X N f) = f := by
  have h1 : evalOne X N (ofHom' X N f) = homCanon X N f := by
    show (ofHom' X N f).hom (1 : SSGRoute.PTExt.Coeff) = homCanon X N f
    rw [ofHom'_hom_apply, spanHV2_apply, one_smul]
  have h2 : toHV2 X N (evalOne X N (ofHom' X N f)) = homHV2 X N f := by
    rw [h1]
    exact toHV2_toCanon X N (homHV2 X N f)
  apply Rep.hom_ext
  apply DFunLike.coe_injective
  funext x
  rw [toHom_hom_apply, h2, homHV2_apply]

lemma ofHom'_toHom (X N : Rep.{0} SSGRoute.PTExt.Coeff G)
    (φ : SSGRoute.PTExt.unitRep G ⟶ homRep X N) : ofHom' X N (toHom X N φ) = φ := by
  apply Rep.hom_ext
  apply Representation.IntertwiningMap.ext
  apply LinearMap.ext_ring
  rw [show (Rep.Hom.hom (ofHom' X N (toHom X N φ))).toLinearMap
        (1 : ↑(SSGRoute.PTExt.unitRep G))
      = spanHV2 X N (homCanon X N (toHom X N φ)) (1 : ↑(SSGRoute.PTExt.unitRep G)) from rfl,
    show (Rep.Hom.hom φ).toLinearMap (1 : ↑(SSGRoute.PTExt.unitRep G))
      = evalOne X N φ from rfl,
    homCanon_toHom, spanHV2_apply, one_smul]

lemma toHom_add (X N : Rep.{0} SSGRoute.PTExt.Coeff G)
    (φ ψ : SSGRoute.PTExt.unitRep G ⟶ homRep X N) :
    toHom X N (φ + ψ) = toHom X N φ + toHom X N ψ := by
  have h1 : evalOne X N (φ + ψ) = evalOne X N φ + evalOne X N ψ := by
    show (φ + ψ).hom (1 : SSGRoute.PTExt.Coeff)
      = φ.hom (1 : SSGRoute.PTExt.Coeff) + ψ.hom (1 : SSGRoute.PTExt.Coeff)
    rw [show (φ + ψ).hom = φ.hom + ψ.hom from rfl]
    rfl
  apply Rep.hom_ext
  apply DFunLike.coe_injective
  funext x
  show (Rep.Hom.hom (toHom X N (φ + ψ))) x
    = (Rep.Hom.hom (toHom X N φ + toHom X N ψ)) x
  rw [toHom_hom_apply]
  show toHV2 X N (evalOne X N (φ + ψ)) x
    = (Rep.Hom.hom (toHom X N φ)) x + (Rep.Hom.hom (toHom X N ψ)) x
  rw [toHom_hom_apply, toHom_hom_apply, h1, toHV2_add]
  rfl

/-- The evaluation-at-`1` additive equivalence. -/
noncomputable def evalOneEquiv (X N : Rep.{0} SSGRoute.PTExt.Coeff G) :
    (SSGRoute.PTExt.unitRep G ⟶ homRep X N) ≃+ (X ⟶ N) where
  toFun := toHom X N
  invFun := ofHom' X N
  left_inv := ofHom'_toHom X N
  right_inv := toHom_ofHom' X N
  map_add' := toHom_add X N

/-! ## The generic instance-family reinterpretation

`uhLmChange` above only reinterprets `Coeff`-linear maps between the carriers of two `Rep`s.  For the
statement below we need the same reinterpretation for arbitrary abelian groups `M`, `N` carrying two
`Coeff`-module structures. -/

/-- The underlying additive homomorphism of a `Coeff`-linear map, with the module instances left
implicit. -/
abbrev uhToAHomGen {M N : Type} [AddCommGroup M] [AddCommGroup N]
    (P : Module SSGRoute.PTExt.Coeff M) (Q : Module SSGRoute.PTExt.Coeff N)
    (f : @LinearMap.{0,0,0,0} SSGRoute.PTExt.Coeff SSGRoute.PTExt.Coeff _ _
            (RingHom.id SSGRoute.PTExt.Coeff) M N _ _ P Q) : M →ₙ+ N :=
  @LinearMap.toAddHom SSGRoute.PTExt.Coeff SSGRoute.PTExt.Coeff _ _
    (RingHom.id SSGRoute.PTExt.Coeff) M N _ _ P Q f

/-- Reinterpret a `Coeff`-linear map `M →ₗ N` in a different pair of `Coeff`-module structures
(arbitrary abelian groups `M`, `N`).  The underlying function is unchanged. -/
noncomputable def uhLmChangeGen {M N : Type} [AddCommGroup M] [AddCommGroup N]
    (P : Module SSGRoute.PTExt.Coeff M) (Q : Module SSGRoute.PTExt.Coeff N)
    (P' : Module SSGRoute.PTExt.Coeff M) (Q' : Module SSGRoute.PTExt.Coeff N)
    (f : @LinearMap.{0,0,0,0} SSGRoute.PTExt.Coeff SSGRoute.PTExt.Coeff _ _
            (RingHom.id SSGRoute.PTExt.Coeff) M N _ _ P Q) :
    @LinearMap.{0,0,0,0} SSGRoute.PTExt.Coeff SSGRoute.PTExt.Coeff _ _
            (RingHom.id SSGRoute.PTExt.Coeff) M N _ _ P' Q' :=
  @LinearMap.mk SSGRoute.PTExt.Coeff SSGRoute.PTExt.Coeff _ _
    (RingHom.id SSGRoute.PTExt.Coeff) M N _ _ P' Q'
    (uhToAHomGen P Q f)
    (fun c x => by
      have h1 : @AddHom.toFun M N _ _ (uhToAHomGen P Q f)
            (@SMul.smul SSGRoute.PTExt.Coeff M P'.toDistribMulAction.toSMul c x) =
          @AddHom.toFun M N _ _ (uhToAHomGen P Q f)
            (@SMul.smul SSGRoute.PTExt.Coeff M P.toDistribMulAction.toSMul c x) :=
        congrArg (@AddHom.toFun M N _ _ (uhToAHomGen P Q f)) (uhSmul_congr M P' P c x)
      have h2 := @LinearMap.map_smul' SSGRoute.PTExt.Coeff SSGRoute.PTExt.Coeff _ _
        (RingHom.id SSGRoute.PTExt.Coeff) M N _ _ P Q f c x
      have h3 : @SMul.smul SSGRoute.PTExt.Coeff N Q.toDistribMulAction.toSMul
            ((RingHom.id SSGRoute.PTExt.Coeff) c)
            (@AddHom.toFun M N _ _ (uhToAHomGen P Q f) x) =
          @SMul.smul SSGRoute.PTExt.Coeff N Q'.toDistribMulAction.toSMul
            ((RingHom.id SSGRoute.PTExt.Coeff) c)
            (@AddHom.toFun M N _ _ (uhToAHomGen P Q f) x) :=
        uhSmul_congr N Q Q' ((RingHom.id SSGRoute.PTExt.Coeff) c)
          (@AddHom.toFun M N _ _ (uhToAHomGen P Q f) x)
      exact h1.trans (h2.trans h3))

lemma uhLmChangeGen_apply {M N : Type} [AddCommGroup M] [AddCommGroup N]
    (P : Module SSGRoute.PTExt.Coeff M) (Q : Module SSGRoute.PTExt.Coeff N)
    (P' : Module SSGRoute.PTExt.Coeff M) (Q' : Module SSGRoute.PTExt.Coeff N)
    (f : @LinearMap.{0,0,0,0} SSGRoute.PTExt.Coeff SSGRoute.PTExt.Coeff _ _
            (RingHom.id SSGRoute.PTExt.Coeff) M N _ _ P Q) (x : M) :
    uhLmChangeGen P Q P' Q' f x = f x := rfl

/-! ## The statement

The requested statement coerces `Rep.Hom.hom (e φ)` (an
`Representation.IntertwiningMap`, i.e. a `FunLike`/`LinearMapClass` element) to the underlying
`LinearMap` via `show X.V →ₗ[Coeff] N.V from (e φ).hom`.  Mathlib registers no `Coe` coercion for
that (only the `LinearMapClass` instance), so we register it locally here: it sends an intertwining
map to its underlying `Coeff`-linear map, reinterpreted in the instance family of the target type
(`uhLmChangeGen`, which leaves the underlying function unchanged).  This is the coercion the
statement's `show` needs, and it makes the left-hand side mean exactly "the underlying function of
`e φ` applied to `x`", as intended. -/

set_option synthInstance.checkSynthOrder false in
/-- The missing coercion `IntertwiningMap → LinearMap` (with an arbitrary pair of target instances);
it is the underlying linear map, reinterpreted in the target instance family. -/
local instance coeIntertwiningMapToLinearMapCoeff {G : Type*} {V W : Type} [Group G] [AddCommGroup V]
    [AddCommGroup W] (P : Module SSGRoute.PTExt.Coeff V) (Q : Module SSGRoute.PTExt.Coeff W)
    (P' : Module SSGRoute.PTExt.Coeff V) (Q' : Module SSGRoute.PTExt.Coeff W)
    (ρ : @Representation SSGRoute.PTExt.Coeff G V _ _ _ P)
    (σ : @Representation SSGRoute.PTExt.Coeff G W _ _ _ Q) :
    Coe (@Representation.IntertwiningMap SSGRoute.PTExt.Coeff G V W _ _ _ _ P Q ρ σ)
      (@LinearMap.{0,0,0,0} SSGRoute.PTExt.Coeff SSGRoute.PTExt.Coeff _ _
        (RingHom.id SSGRoute.PTExt.Coeff) V W _ _ P' Q') :=
  ⟨fun f => uhLmChangeGen P Q P' Q'
    (@Representation.IntertwiningMap.toLinearMap SSGRoute.PTExt.Coeff G V W _ _ _ _ P Q ρ σ f)⟩

lemma coeIntertwiningMapToLinearMapCoeff_apply {G : Type*} {V W : Type} [Group G] [AddCommGroup V]
    [AddCommGroup W] (P : Module SSGRoute.PTExt.Coeff V) (Q : Module SSGRoute.PTExt.Coeff W)
    (P' : Module SSGRoute.PTExt.Coeff V) (Q' : Module SSGRoute.PTExt.Coeff W)
    (ρ : @Representation SSGRoute.PTExt.Coeff G V _ _ _ P)
    (σ : @Representation SSGRoute.PTExt.Coeff G W _ _ _ Q)
    (f : @Representation.IntertwiningMap SSGRoute.PTExt.Coeff G V W _ _ _ _ P Q ρ σ) (x : V) :
    ((f : @LinearMap.{0,0,0,0} SSGRoute.PTExt.Coeff SSGRoute.PTExt.Coeff _ _
        (RingHom.id SSGRoute.PTExt.Coeff) V W _ _ P' Q') x) = f x := rfl

theorem unitHomEquiv_exists (G : Type) [Group G] (X N : Rep.{0} SSGRoute.PTExt.Coeff G) :
    ∃ e : (SSGRoute.PTExt.unitRep G ⟶ Work.SSGRoute.homRep X N) ≃+ (X ⟶ N),
      ∀ (φ : SSGRoute.PTExt.unitRep G ⟶ Work.SSGRoute.homRep X N) (x : X.V),
        (show X.V →ₗ[SSGRoute.PTExt.Coeff] N.V from (e φ).hom) x =
          (show X.V →ₗ[SSGRoute.PTExt.Coeff] N.V from φ.hom (1 : SSGRoute.PTExt.Coeff)) x := by
  refine ⟨evalOneEquiv X N, ?_⟩
  intro φ x
  rw [show (show X.V →ₗ[SSGRoute.PTExt.Coeff] N.V from (evalOneEquiv X N φ).hom) x
      = (Rep.Hom.hom (toHom X N φ)) x from
      coeIntertwiningMapToLinearMapCoeff_apply _ _ _ _ (rhoHV2 X) (rhoHV2 N) _ x,
    toHom_hom_apply, toHV2_apply]
  rfl

end

end Work.SSGRoute
