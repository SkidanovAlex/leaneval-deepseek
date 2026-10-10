import Mathlib.Tactic.Group
import Mathlib.Combinatorics.Quiver.ReflQuiver
import Mathlib.RepresentationTheory.Rep.Basic
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

noncomputable section

open CategoryTheory

namespace Work.SSGRoute

universe u

variable (k : Type u) [CommRing k] (G : Type u) [Group G]

/-- The coinduced representation `Coind_1^G V`: functions `G → V` with the action
`(g • φ) x = φ (x * g)`. -/
def coindRepRep (V : Type u) [AddCommGroup V] [Module k V] : Representation k G (G → V) where
  toFun := fun g =>
    LinearMap.pi (fun x : G => LinearMap.proj (R := k) (φ := fun _ : G => V) (x * g))
  map_one' := by ext φ x; simp
  map_mul' := by intro g h; ext φ x; simp [mul_assoc]

@[simp]
theorem coindRepRep_apply (V : Type u) [AddCommGroup V] [Module k V] (g x : G) (φ : G → V) :
    (coindRepRep k G V) g φ x = φ (x * g) := rfl

/-- The coinduced representation `Coind_1^G V` of a `k`-module `V`. -/
def coindRep (V : Type u) [AddCommGroup V] [Module k V] : Rep k G :=
  Rep.of (coindRepRep k G V)

@[simp]
theorem coindRep_ρ_apply (V : Type u) [AddCommGroup V] [Module k V] (g x : G) (φ : G → V) :
    (coindRep k G V).ρ g φ x = φ (x * g) := rfl

variable {k G}

/-- The augmentation `φ ↦ ∑ x, x⁻¹ • φ x` of the coinduced module, as a `k`-linear map. -/
def coindAugFun (M : Rep k G) [Fintype G] : (G → M.V) →ₗ[k] M.V where
  toFun φ := ∑ x : G, M.ρ x⁻¹ (φ x)
  map_add' φ ψ := by
    simp only [Pi.add_apply, map_add, Finset.sum_add_distrib]
  map_smul' c φ := by
    show (∑ x : G, M.ρ x⁻¹ ((c • φ) x)) = c • ∑ x : G, M.ρ x⁻¹ (φ x)
    simp only [Pi.smul_apply, map_smul]
    rw [Finset.smul_sum]

@[simp]
theorem coindAugFun_apply (M : Rep k G) [Fintype G] (φ : G → M.V) :
    coindAugFun M φ = ∑ x : G, M.ρ x⁻¹ (φ x) := rfl

/-- The augmentation is surjective. -/
theorem coindAugFun_surjective (M : Rep k G) [Fintype G] :
    Function.Surjective (coindAugFun M) := by
  classical
  intro m
  refine ⟨fun x => if x = 1 then m else 0, ?_⟩
  rw [coindAugFun_apply, Finset.sum_eq_single 1]
  · simp
  · intro b _ hb; simp [hb]
  · intro h; exact absurd (Finset.mem_univ 1) h

/-- The augmentation map is equivariant, as a morphism `Coind(M) ⟶ M`. -/
def coindAugHom (M : Rep k G) [Fintype G] : coindRep k G M.V ⟶ M :=
  Rep.ofHom
    { toLinearMap := coindAugFun M
      isIntertwining' := by
        intro g
        ext φ
        simp only [LinearMap.comp_apply, coindRepRep_apply, coindAugFun_apply]
        rw [show (∑ x : G, M.ρ x⁻¹ (φ (x * g))) =
            ∑ y : G, M.ρ (g * y⁻¹) (φ y) from
          Fintype.sum_equiv (Equiv.mulRight g) _ _ (fun x => by
            simp only [Equiv.coe_mulRight]
            congr 1
            group)]
        rw [map_sum]
        exact Finset.sum_congr rfl fun y _ => by
          change (M.ρ (g * y⁻¹)) (φ y) = (M.ρ g ∘ₗ M.ρ y⁻¹) (φ y)
          rw [← Rep.ρ_mul] }

@[simp]
theorem coindAugHom_apply (M : Rep k G) [Fintype G] (φ : G → M.V) :
    (coindAugHom M).hom φ = ∑ x : G, M.ρ x⁻¹ (φ x) := rfl

/-- The kernel of a morphism of representations, as a representation: the subrepresentation on
`ker f`. -/
def kerRep {M N : Rep k G} (f : M ⟶ N) : Rep k G :=
  Rep.of (Representation.subrepresentation M.ρ (LinearMap.ker (Rep.Hom.hom f).toLinearMap)
    (fun g x hx => by
      change (Rep.Hom.hom f) ((M.ρ g) x) = 0
      rw [Rep.hom_comm_apply]
      have hx' : (Rep.Hom.hom f) x = 0 := hx
      rw [hx', map_zero]))

/-- The inclusion of the kernel of a morphism of representations. -/
def kerRepSubtype {M N : Rep k G} (f : M ⟶ N) : kerRep f ⟶ M :=
  Rep.ofHom ⟨Submodule.subtype _, fun _ => rfl⟩

@[simp]
theorem kerRepSubtype_apply {M N : Rep k G} (f : M ⟶ N) (v : (kerRep f).V) :
    (kerRepSubtype f).hom v = v.1 := rfl

/-- **The short complex `0 → ker(aug) → Coind(M) → M → 0`.** -/
def coindSES (M : Rep k G) [Fintype G] : ShortComplex (Rep k G) where
  X₁ := kerRep (coindAugHom M)
  X₂ := coindRep k G M.V
  X₃ := M
  f := kerRepSubtype (coindAugHom M)
  g := coindAugHom M
  zero := by
    ext x
    exact LinearMap.mem_ker.mp x.2

/-- **The sequence `0 → ker(aug) → Coind(M) → M → 0` is short exact.** -/
theorem coindSES_shortExact (M : Rep k G) [Fintype G] : (coindSES M).ShortExact where
  exact := (forget₂ (Rep k G) (ModuleCat k)).reflects_exact_of_faithful _ <|
    (ShortComplex.moduleCat_exact_iff _).2 fun x hx => ⟨⟨x, hx⟩, rfl⟩
  mono_f := (Rep.mono_iff_injective _).2 Subtype.coe_injective
  epi_g := (Rep.epi_iff_surjective _).2 (coindAugFun_surjective M)


/-- The contragredient (dual) representation. -/
abbrev dualRep (M : Rep k G) : Rep k G := Rep.of M.ρ.dual

/-- The transpose (dual) of a morphism of representations. -/
def dualHom {M N : Rep k G} (f : M ⟶ N) : dualRep N ⟶ dualRep M :=
  Rep.ofHom
    { toLinearMap := (Rep.Hom.hom f).dualMap
      isIntertwining' := by
        intro g
        ext ψ v
        simp only [LinearMap.comp_apply, LinearMap.dualMap_apply, Representation.dual_apply,
          Module.Dual.transpose_apply]
        congr 1
        simpa using (Rep.hom_comm_apply f g⁻¹ v).symm }

set_option backward.isDefEq.respectTransparency false in
@[simp]
theorem dualHom_apply {M N : Rep k G} (f : M ⟶ N) (ψ : (dualRep N).V) :
    ((dualHom f).hom ψ : M.V →ₗ[k] k) = (ψ : N.V →ₗ[k] k).comp (Rep.Hom.hom f).toLinearMap :=
  rfl

set_option backward.isDefEq.respectTransparency false in
@[simp]
theorem dualHom_apply_apply {M N : Rep k G} (f : M ⟶ N) (ψ : (dualRep N).V) (v : M.V) :
    ((dualHom f).hom ψ : M.V →ₗ[k] k) v = (ψ : N.V →ₗ[k] k) ((Rep.Hom.hom f).toLinearMap v) :=
  rfl

/-- The kernel `M' = ker (coindAugHom M)` of the augmentation. -/
def augKer (M : Rep k G) [Fintype G] : Rep k G := kerRep (coindAugHom M)

/-- The inclusion `M' ⟶ Coind(M)`. -/
def augKerSubtype (M : Rep k G) [Fintype G] : augKer M ⟶ coindRep k G M.V :=
  kerRepSubtype (coindAugHom M)

/-- The dual of the coinduced resolution:
`0 → M^∨ → Coind(M)^∨ → (M')^∨ → 0`. -/
def dualSES (M : Rep k G) [Fintype G] : ShortComplex (Rep k G) where
  X₁ := dualRep M
  X₂ := dualRep (coindRep k G M.V)
  X₃ := dualRep (augKer M)
  f := dualHom (coindAugHom M)
  g := dualHom (augKerSubtype M)
  zero := by
    ext ψ x
    change (LinearMap.dualMap (Rep.Hom.hom (augKerSubtype M)).toLinearMap)
        ((LinearMap.dualMap (Rep.Hom.hom (coindAugHom M)).toLinearMap) ψ) x = 0
    rw [LinearMap.dualMap_apply, LinearMap.dualMap_apply]
    rw [show (Rep.Hom.hom (augKerSubtype M)).toLinearMap x = x.1 from rfl]
    rw [show (Rep.Hom.hom (coindAugHom M)).toLinearMap (x.1) = 0 from x.2]
    exact map_zero ((ψ : (dualRep M).V) : M.V →ₗ[k] k)

end Work.SSGRoute
