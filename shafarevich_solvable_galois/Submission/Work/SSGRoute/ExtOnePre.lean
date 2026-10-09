import Mathlib
import Submission.Work.SSGRoute.PTDefs
import Submission.Work.SSGRoute.homRep
import Submission.Work.SSGRoute.ExtOneDefs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Precomposition on the internal hom `Hom_ℤ(X,N)`

`Work.SSGRoute.homRepPre u : homRep X N ⟶ homRep X' N` for `u : X' ⟶ X` is precomposition of the
underlying `Coeff`-linear map with `u`.  Its existence is the contravariant functoriality of the
internal hom in its first variable; it is what allows the long exact sequence of
`0 → homRep M N → homRep F N → homRep R N → 0` to be formed.
-/

open CategoryTheory SSGRoute.PTExt

namespace Work.SSGRoute

noncomputable section

variable {G : Type} [Group G]

/-- The action of a `Rep`-morphism on the underlying abelian groups is additive. -/
lemma inter_add (X X' : Rep.{0} Coeff G) (u : X' ⟶ X) (a b : X'.V) :
    u.hom (a + b) = u.hom a + u.hom b := by
  letI : Module Coeff X'.V := X'.hV2
  letI : Module Coeff X.V := X.hV2
  exact map_add (Rep.Hom.hom u).toLinearMap a b

/-- The action of a `Rep`-morphism on the underlying abelian groups is `ℤ`-linear. -/
lemma inter_zsmul (X X' : Rep.{0} Coeff G) (u : X' ⟶ X) (k : ℤ) (a : X'.V) :
    u.hom (k • a) = k • u.hom a := by
  letI : Module Coeff X'.V := X'.hV2
  letI : Module Coeff X.V := X.hV2
  exact map_zsmul (Rep.Hom.hom u).toLinearMap.toAddMonoidHom k a

/-- **Precomposition on the internal hom.** -/
theorem homRepPre_exists (X X' N : Rep.{0} Coeff G) (u : X' ⟶ X) :
    ∃ φ : homRep X N ⟶ homRep X' N,
      ∀ (ψ : (homRep X N).V) (x : X'.V),
        (show X'.V →ₗ[Coeff] N.V from φ.hom ψ) x =
          (show X.V →ₗ[Coeff] N.V from ψ) (u.hom x) := by
  let v : (X.V →ₗ[Coeff] N.V) → (X'.V →ₗ[Coeff] N.V) := fun ψ =>
    { toFun := fun x => ψ (u.hom x)
      map_add' := fun a b => by
        show ψ (u.hom (a + b)) = ψ (u.hom a) + ψ (u.hom b)
        rw [inter_add X X' u a b]
        exact map_add ψ (u.hom a) (u.hom b)
      map_smul' := fun c a => by
        show ψ (u.hom (c • a)) = c • ψ (u.hom a)
        obtain ⟨k⟩ := c
        rw [ulift_up_int_smul_eq k a, inter_zsmul X X' u k a]
        exact map_zsmul ψ.toAddMonoidHom k (u.hom a) }
  have hvadd : ∀ a b, v (a + b) = v a + v b := by
    intro a b
    apply LinearMap.ext; intro x
    show (a + b) (u.hom x) = a (u.hom x) + b (u.hom x)
    exact LinearMap.add_apply a b (u.hom x)
  have hvsmul : ∀ (c : Coeff) a, v (c • a) = c • v a := by
    intro c a
    apply LinearMap.ext; intro x
    show (c • a) (u.hom x) = c • (a (u.hom x))
    exact LinearMap.smul_apply c a (u.hom x)
  let Lin : (X.V →ₗ[Coeff] N.V) →ₗ[Coeff] (X'.V →ₗ[Coeff] N.V) :=
    { toFun := v, map_add' := hvadd, map_smul' := hvsmul }
  have hLin : ∀ (ψ : X.V →ₗ[Coeff] N.V), Lin ψ = v ψ := fun _ => rfl
  refine ⟨Rep.ofHom (Representation.IntertwiningMap.mk Lin ?_), ?_⟩
  · intro g
    apply LinearMap.ext; intro ψ
    apply LinearMap.ext; intro x
    show (show X.V →ₗ[Coeff] N.V from (homRep X N).ρ g ψ) (u.hom x) =
      (show X'.V →ₗ[Coeff] N.V from (homRep X' N).ρ g (Lin ψ)) x
    rw [homRep_rho_apply X' N g (Lin ψ) x, homRep_rho_apply X N g ψ (u.hom x)]
    show (N.ρ g) (ψ ((X.ρ g⁻¹) ((Rep.Hom.hom u) x))) =
      (N.ρ g) (ψ ((Rep.Hom.hom u) ((X'.ρ g⁻¹) x)))
    rw [Rep.hom_comm_apply u g⁻¹ x]
  · intro ψ x
    change (v ψ) x = (show X.V →ₗ[Coeff] N.V from ψ) (u.hom x)
    rfl

/-- Precomposition on the internal hom, as a morphism. -/
noncomputable def homRepPre (X X' N : Rep.{0} Coeff G) (u : X' ⟶ X) :
    homRep X N ⟶ homRep X' N :=
  Classical.choose (homRepPre_exists X X' N u)

/-- Computation rule for `homRepPre`. -/
lemma homRepPre_apply (X X' N : Rep.{0} Coeff G) (u : X' ⟶ X)
    (ψ : (homRep X N).V) (x : X'.V) :
    (show X'.V →ₗ[Coeff] N.V from (homRepPre X X' N u).hom ψ) x =
      (show X.V →ₗ[Coeff] N.V from ψ) (u.hom x) :=
  Classical.choose_spec (homRepPre_exists X X' N u) ψ x

/-- Precomposition on the internal hom is contravariantly functorial. -/
lemma homRepPre_comp (X X' X'' N : Rep.{0} Coeff G) (u : X' ⟶ X) (v : X'' ⟶ X') :
    homRepPre X X' N u ≫ homRepPre X' X'' N v = homRepPre X X'' N (v ≫ u) := by
  apply Rep.hom_ext
  apply Representation.IntertwiningMap.ext
  apply LinearMap.ext
  intro ψ
  apply LinearMap.ext
  intro x
  show (show X''.V →ₗ[Coeff] N.V from
      (homRepPre X X' N u ≫ homRepPre X' X'' N v).hom ψ) x =
    (show X''.V →ₗ[Coeff] N.V from (homRepPre X X'' N (v ≫ u)).hom ψ) x
  rw [ConcreteCategory.comp_apply (homRepPre X X' N u) (homRepPre X' X'' N v) ψ]
  rw [homRepPre_apply X' X'' N v ((homRepPre X X' N u).hom ψ) x,
      homRepPre_apply X X' N u ψ (v.hom x),
      homRepPre_apply X X'' N (v ≫ u) ψ x,
      ConcreteCategory.comp_apply v u x]

/-- Precomposition with the zero morphism is zero. -/
lemma homRepPre_zero (X X' N : Rep.{0} Coeff G) :
    homRepPre X X' N (0 : X' ⟶ X) = 0 := by
  apply Rep.hom_ext
  apply Representation.IntertwiningMap.ext
  apply LinearMap.ext
  intro ψ
  apply LinearMap.ext
  intro x
  show (show X'.V →ₗ[Coeff] N.V from (homRepPre X X' N (0 : X' ⟶ X)).hom ψ) x = 0
  rw [homRepPre_apply X X' N (0 : X' ⟶ X) ψ x, Rep.zero_hom]
  exact map_zero (show X.V →ₗ[Coeff] N.V from ψ)

end

end Work.SSGRoute
