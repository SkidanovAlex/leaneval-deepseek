import Mathlib
import Submission.Work.CharCore.Basic

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# Simplicity of an `FDRep` object vs irreducibility of its representation

For `V : FDRep ℂ G`, an object of the category of finite dimensional complex
representations of `G`, we show that `V` is a simple object of the category
(any monomorphism into `V` is zero or an isomorphism) if and only if the
underlying representation `V.ρ` is irreducible, i.e. its lattice of
subrepresentations is `{⊥, ⊤}` (`Representation.IsIrreducible`).

The proof passes through the subobject lattice: we show that a subrepresentation
of `V.ρ` gives a monomorphism into `V` (the inclusion of the subrepresentation)
and, conversely, that a monomorphism into `V` has an image which is a
subrepresentation, so that the two lattices are order isomorphic.

## Main result

* `Work.CharCore.fdRep_simple_iff`
-/

noncomputable section

open CategoryTheory

namespace Work.CharCore

variable {G : Type*} [Group G]

/-! ### The inclusion of a subrepresentation -/

/-- A subrepresentation `S ≤ V.ρ` of a finite dimensional representation `V` is again a
finite dimensional representation, and the inclusion of `S` into `V` is a morphism of
`FDRep`s. -/
def subrepIncl (V : FDRep ℂ G) (S : Subrepresentation V.ρ) :
    FDRep.of S.toRepresentation ⟶ V :=
  Action.Hom.mk (hom := FGModuleCat.ofHom S.toSubmodule.subtype) (comm := by
    intro g
    have key : (Action.ρ (FDRep.of S.toRepresentation) g).hom.hom =
        (S.toRepresentation g : ↥S.toSubmodule →ₗ[ℂ] ↥S.toSubmodule) := by
      rw [FDRep.hom_hom_action_ρ, FDRep.of_ρ']
    apply FGModuleCat.hom_ext
    rw [FGModuleCat.hom_hom_comp, FGModuleCat.hom_hom_comp, key, FDRep.hom_hom_action_ρ]
    rfl)

lemma subrepIncl_apply (V : FDRep ℂ G) (S : Subrepresentation V.ρ) (x : ↥S.toSubmodule) :
    subrepIncl V S x = (x : ↥V) := rfl

lemma subrepIncl_injective (V : FDRep ℂ G) (S : Subrepresentation V.ρ) :
    Function.Injective (subrepIncl V S) := fun _ _ h => Subtype.ext h

lemma subrepIncl_mono (V : FDRep ℂ G) (S : Subrepresentation V.ρ) : Mono (subrepIncl V S) :=
  ConcreteCategory.mono_of_injective _ (subrepIncl_injective V S)

/-! ### Basic API for morphisms of `FDRep`s -/

/-- A monomorphism of finite dimensional representations is injective on the underlying
vector spaces. -/
lemma fdRep_injective_of_mono {V W : FDRep ℂ G} (f : V ⟶ W) [Mono f] :
    Function.Injective f := by
  have h1 : Mono (f.hom) := Functor.map_mono (Action.forget (FGModuleCat ℂ) G) f
  have h2 : Mono ((forget₂ (FGModuleCat ℂ) (ModuleCat ℂ)).map f.hom) :=
    Functor.map_mono ((forget₂ (FGModuleCat ℂ) (ModuleCat ℂ))) f.hom
  rw [ModuleCat.mono_iff_injective] at h2
  exact h2

/-- Equivariance of a morphism of finite dimensional representations, stated for the
underlying linear maps. -/
lemma fdRep_comm_apply {V W : FDRep ℂ G} (f : W ⟶ V) (g : G) (x : ↥W) :
    (f.hom.hom.hom) ((FDRep.ρ W) g x) = (FDRep.ρ V) g (f.hom.hom.hom x) := by
  have key : (f.hom.hom.hom : ↥W →ₗ[ℂ] ↥V).comp ((Action.ρ W g).hom.hom) =
      ((Action.ρ V g).hom.hom).comp (f.hom.hom.hom : ↥W →ₗ[ℂ] ↥V) := by
    have h := congrArg (fun (t : W.V ⟶ V.V) => t.hom.hom) (f.comm g)
    simp only [FGModuleCat.hom_hom_comp] at h
    exact h
  have h2 := congrArg (fun (t : ↥W →ₗ[ℂ] ↥V) => t x) key
  simp only [LinearMap.comp_apply] at h2
  rw [FDRep.hom_hom_action_ρ, FDRep.hom_hom_action_ρ] at h2
  exact h2

/-- A finite dimensional representation whose underlying space is trivial is a zero
object, so its identity is zero. -/
lemma fdRep_id_eq_zero_of_subsingleton (V : FDRep ℂ G) [Subsingleton ↥V] :
    (𝟙 V : V ⟶ V) = 0 := by
  apply Action.hom_ext
  apply FGModuleCat.hom_ext
  ext x
  rw [Subsingleton.elim x 0]
  simp

/-- A finite dimensional representation is nonzero (as a module) if and only if it has a
nontrivial lattice of subrepresentations. -/
lemma fdRep_nontrivial_iff (V : FDRep ℂ G) :
    Nontrivial ↥V ↔ Nontrivial (Subrepresentation V.ρ) := by
  rw [← not_iff_not, not_nontrivial_iff_subsingleton, not_nontrivial_iff_subsingleton]
  constructor
  · intro h
    haveI : Subsingleton (Submodule ℂ ↥V) := (Submodule.subsingleton_iff ℂ).mpr h
    exact ⟨fun a b =>
      Subrepresentation.toSubmodule_injective (Subsingleton.elim a.toSubmodule b.toSubmodule)⟩
  · intro h
    haveI := h
    have hbt : (⊥ : Subrepresentation V.ρ) = ⊤ := Subsingleton.elim _ _
    have hbt' : (⊥ : Submodule ℂ ↥V) = ⊤ := by
      have h2 := congrArg Subrepresentation.toSubmodule hbt
      change (⊥ : Submodule ℂ ↥V) = (⊤ : Submodule ℂ ↥V) at h2
      exact h2
    refine ⟨fun a b => ?_⟩
    have ha : a = 0 := by
      have hmem : a ∈ (⊤ : Submodule ℂ ↥V) := Submodule.mem_top
      rw [← hbt'] at hmem
      simpa using hmem
    have hb : b = 0 := by
      have hmem : b ∈ (⊤ : Submodule ℂ ↥V) := Submodule.mem_top
      rw [← hbt'] at hmem
      simpa using hmem
    rw [ha, hb]

/-! ### The two implications -/

/-- A simple object of `FDRep ℂ G` has irreducible underlying representation. -/
theorem isIrreducible_of_simple_fdRep (V : FDRep ℂ G) [CategoryTheory.Simple V] :
    Representation.IsIrreducible V.ρ := by
  haveI hnt : Nontrivial ↥V := by
    by_contra h
    rw [not_nontrivial_iff_subsingleton] at h
    haveI := h
    exact CategoryTheory.id_nonzero V (fdRep_id_eq_zero_of_subsingleton V)
  haveI : Nontrivial (Subrepresentation V.ρ) := (fdRep_nontrivial_iff V).mp hnt
  refine ⟨fun S => ?_⟩
  haveI : Mono (subrepIncl V S) := subrepIncl_mono V S
  rcases IsSimpleOrder.eq_bot_or_eq_top (Subobject.mk (subrepIncl V S)) with h | h
  · left
    have hφ0 : subrepIncl V S = 0 := Subobject.mk_eq_bot_iff_zero.mp h
    have hval : ∀ x : ↥S.toSubmodule, (x : ↥V) = 0 := by
      intro x
      have h3 : subrepIncl V S x = 0 := by rw [hφ0]; rfl
      exact h3
    have hsub : S.toSubmodule = ⊥ := by
      rw [Submodule.eq_bot_iff]
      intro x hx
      exact hval ⟨x, hx⟩
    exact Subrepresentation.ext hsub
  · right
    have hiso : IsIso (subrepIncl V S) := (Subobject.isIso_iff_mk_eq_top _).mpr h
    haveI := hiso
    have hsurj : Function.Surjective (subrepIncl V S) :=
      (ConcreteCategory.bijective_of_isIso _).2
    have hsub : S.toSubmodule = ⊤ := by
      rw [Submodule.eq_top_iff']
      intro v
      obtain ⟨x, hx⟩ := hsurj v
      rw [← hx, subrepIncl_apply V S x]
      exact x.property
    exact Subrepresentation.ext hsub

/-- A finite dimensional representation which is irreducible is a simple object of
`FDRep ℂ G`. -/
theorem simple_of_isIrreducible_fdRep (V : FDRep ℂ G) (h : Representation.IsIrreducible V.ρ) :
    CategoryTheory.Simple V where
  mono_isIso_iff_nonzero := by
    intro W f hmono
    haveI := hmono
    haveI : IsSimpleOrder (Subrepresentation V.ρ) := h
    constructor
    · intro _ h0
      have hnt : Nontrivial ↥V := (fdRep_nontrivial_iff V).mpr inferInstance
      refine (not_subsingleton_iff_nontrivial.mpr hnt) ⟨fun a b => ?_⟩
      have hbij := ConcreteCategory.bijective_of_isIso f
      obtain ⟨x, hx⟩ := hbij.2 a
      obtain ⟨y, hy⟩ := hbij.2 b
      rw [← hx, ← hy, h0]
      rfl
    · intro hne
      let S : Subrepresentation V.ρ :=
        { toSubmodule := LinearMap.range (f.hom.hom.hom : ↥W →ₗ[ℂ] ↥V)
          apply_mem_toSubmodule := fun g _ hv => by
            obtain ⟨u, rfl⟩ := hv
            exact ⟨(FDRep.ρ W) g u, fdRep_comm_apply f g u⟩ }
      rcases IsSimpleOrder.eq_bot_or_eq_top S with hS | hS
      · exfalso
        apply hne
        have hbot : (f.hom.hom.hom : ↥W →ₗ[ℂ] ↥V) = 0 := by
          apply LinearMap.range_eq_bot.mp
          have h2 := congrArg Subrepresentation.toSubmodule hS
          change LinearMap.range (f.hom.hom.hom : ↥W →ₗ[ℂ] ↥V) = ⊥ at h2
          exact h2
        apply Action.hom_ext
        apply FGModuleCat.hom_ext
        simpa using hbot
      · have htop : LinearMap.range (f.hom.hom.hom : ↥W →ₗ[ℂ] ↥V) = ⊤ := by
          have h2 := congrArg Subrepresentation.toSubmodule hS
          change LinearMap.range (f.hom.hom.hom : ↥W →ₗ[ℂ] ↥V) = ⊤ at h2
          exact h2
        have hsurj : Function.Surjective (⇑f) := LinearMap.range_eq_top.mp htop
        exact (ConcreteCategory.isIso_iff_bijective f).mpr
          ⟨fdRep_injective_of_mono f, hsurj⟩

theorem fdRep_simple_iff {G : Type*} [Group G] (V : FDRep ℂ G) :
    CategoryTheory.Simple V ↔ Representation.IsIrreducible V.ρ :=
  ⟨fun h => by
    haveI := h
    exact isIrreducible_of_simple_fdRep V, fun h => simple_of_isIrreducible_fdRep V h⟩

end Work.CharCore
