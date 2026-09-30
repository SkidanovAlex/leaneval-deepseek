import Mathlib
import Submission.Work.SymQuot.Invariants.tensor_fixedPoints

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


set_option autoImplicit false

open scoped TensorProduct

namespace Work.SymQuot.Invariants

section Helpers

variable {K B R G : Type*} [Field K] [CommRing B] [Algebra K B] [Group G] [Fintype G]
  [DecidableEq G] [MulSemiringAction G B] [SMulCommClass G K B] [CommRing R] [Algebra K R] [Module.Flat K R]

/-- The `K`-linear difference map `B →ₗ[K] (G → B)`, `b ↦ (g • b - b)_g`.  Its kernel is the
subalgebra `B^G` of `G`-fixed points. -/
noncomputable def tensor_fixedPoints_of_flat_dmap : B →ₗ[K] (G → B) :=
  LinearMap.pi fun g => ((MulSemiringAction.toAlgHom K B g).toLinearMap : B →ₗ[K] B) - LinearMap.id

/-- The `K`-algebra automorphism of `B ⊗[K] R` acting by `g` on the first factor and trivially
on `R`. -/
noncomputable def tensor_fixedPoints_of_flat_sact (g : G) : B ⊗[K] R →ₐ[K] B ⊗[K] R :=
  Algebra.TensorProduct.map (MulSemiringAction.toAlgHom K B g) (AlgHom.id K R)

local notation "dmap" => tensor_fixedPoints_of_flat_dmap (K := K) (B := B) (G := G)

local notation "sact" => tensor_fixedPoints_of_flat_sact (K := K) (B := B) (R := R) (G := G)

lemma tensor_fixedPoints_of_flat_dmap_apply (g : G) (b : B) : dmap b g = g • b - b := by
  simp [tensor_fixedPoints_of_flat_dmap, LinearMap.pi_apply, LinearMap.sub_apply, LinearMap.id_apply,
    AlgHom.toLinearMap_apply]

lemma tensor_fixedPoints_of_flat_mem_ker_dmap {b : B} :
    b ∈ LinearMap.ker dmap ↔ ∀ g : G, g • b = b := by
  rw [LinearMap.mem_ker]
  constructor
  · intro h g
    have hg := congrFun h g
    rw [tensor_fixedPoints_of_flat_dmap_apply] at hg
    exact sub_eq_zero.mp hg
  · intro h
    funext g
    rw [tensor_fixedPoints_of_flat_dmap_apply, h g, sub_self]
    rfl

lemma tensor_fixedPoints_of_flat_ker_dmap :
    LinearMap.ker dmap = (FixedPoints.subalgebra K B G).toSubmodule := by
  ext b
  rw [tensor_fixedPoints_of_flat_mem_ker_dmap, Subalgebra.mem_toSubmodule,
    show b ∈ FixedPoints.subalgebra K B G ↔ b ∈ FixedPoints.submonoid G B from Iff.rfl,
    FixedPoints.mem_submonoid]

lemma tensor_fixedPoints_of_flat_range_rTensor_dmap :
    LinearMap.range ((LinearMap.ker dmap).subtype.rTensor R)
      = LinearMap.ker (LinearMap.rTensor R dmap) := by
  have hex : Function.Exact (⇑(LinearMap.ker dmap).subtype) ⇑(dmap) := by
    rw [LinearMap.exact_iff, Submodule.range_subtype]
  have h := Module.Flat.rTensor_exact (M := R) (f := (LinearMap.ker dmap).subtype) (g := dmap) hex
  rw [LinearMap.exact_iff] at h
  exact h.symm

lemma tensor_fixedPoints_of_flat_sact_tmul (g : G) (b : B) (f : R) :
    sact g (b ⊗ₜ[K] f) = (g • b) ⊗ₜ[K] f := by
  simp [tensor_fixedPoints_of_flat_sact]

lemma tensor_fixedPoints_of_flat_sact_sub_id_rTensor (g : G) :
    (((MulSemiringAction.toAlgHom K B g).toLinearMap : B →ₗ[K] B) - LinearMap.id).rTensor R
      = AlgHom.toLinearMap (sact g) - LinearMap.id := by
  rw [LinearMap.rTensor_sub, LinearMap.rTensor_id]
  rfl

lemma tensor_fixedPoints_of_flat_phi_rTensor_apply_eq_zero_iff (g : G) (x : B ⊗[K] R) :
    ((((MulSemiringAction.toAlgHom K B g).toLinearMap : B →ₗ[K] B) - LinearMap.id).rTensor R) x = 0
      ↔ sact g x = x := by
  rw [tensor_fixedPoints_of_flat_sact_sub_id_rTensor, LinearMap.sub_apply, LinearMap.id_apply, sub_eq_zero,
    AlgHom.toLinearMap_apply]

lemma tensor_fixedPoints_of_flat_piLeft_tmul_apply (u : G → B) (f : R) (g : G) :
    TensorProduct.piLeft K R (fun _ : G => B) (u ⊗ₜ[K] f) g = u g ⊗ₜ[K] f := by
  simp

lemma tensor_fixedPoints_of_flat_piLeft_rTensor_dmap_tmul (b : B) (f : R) :
    TensorProduct.piLeft K R (fun _ : G => B) (LinearMap.rTensor R dmap (b ⊗ₜ[K] f))
      = fun g : G =>
          ((((MulSemiringAction.toAlgHom K B g).toLinearMap : B →ₗ[K] B) - LinearMap.id).rTensor R)
            (b ⊗ₜ[K] f) := by
  funext g
  rw [LinearMap.rTensor_tmul, tensor_fixedPoints_of_flat_piLeft_tmul_apply, LinearMap.rTensor_tmul,
    LinearMap.sub_apply, LinearMap.id_apply, AlgHom.toLinearMap_apply,
    MulSemiringAction.toAlgHom_apply, tensor_fixedPoints_of_flat_dmap_apply]

lemma tensor_fixedPoints_of_flat_piLeft_rTensor_dmap :
    (TensorProduct.piLeft K R (fun _ : G => B)).toLinearMap.comp (LinearMap.rTensor R dmap)
      = LinearMap.pi (fun g : G =>
          (((MulSemiringAction.toAlgHom K B g).toLinearMap : B →ₗ[K] B) - LinearMap.id).rTensor R) := by
  apply TensorProduct.ext'
  intro b f
  exact tensor_fixedPoints_of_flat_piLeft_rTensor_dmap_tmul b f

lemma tensor_fixedPoints_of_flat_mem_ker_rTensor_dmap {x : B ⊗[K] R} :
    x ∈ LinearMap.ker (LinearMap.rTensor R dmap) ↔ ∀ g : G, sact g x = x := by
  have key := tensor_fixedPoints_of_flat_piLeft_rTensor_dmap (K := K) (B := B) (R := R) (G := G)
  have happ : (TensorProduct.piLeft K R (fun _ : G => B)) (LinearMap.rTensor R dmap x)
      = fun g : G =>
          ((((MulSemiringAction.toAlgHom K B g).toLinearMap : B →ₗ[K] B) - LinearMap.id).rTensor R) x := by
    have h := congrArg (fun l => l x) key
    funext g
    simpa [LinearMap.pi_apply] using congrFun h g
  have hzero : LinearMap.rTensor R dmap x = 0
      ↔ (TensorProduct.piLeft K R (fun _ : G => B)) (LinearMap.rTensor R dmap x) = 0 :=
    (LinearEquiv.map_eq_zero_iff (TensorProduct.piLeft K R (fun _ : G => B))).symm
  rw [LinearMap.mem_ker, hzero, happ, funext_iff]
  simp only [Pi.zero_apply]
  exact forall_congr' (fun g => tensor_fixedPoints_of_flat_phi_rTensor_apply_eq_zero_iff g x)

lemma tensor_fixedPoints_of_flat_sact_comp_map (g : G) (y : FixedPoints.subalgebra K B G ⊗[K] R) :
    sact g
        (Algebra.TensorProduct.map (Subalgebra.val (FixedPoints.subalgebra K B G)) (AlgHom.id K R) y)
      = Algebra.TensorProduct.map (Subalgebra.val (FixedPoints.subalgebra K B G)) (AlgHom.id K R) y := by
  refine TensorProduct.inductionOn y ?_ ?_
  · intro a f
    have ha : g • (a : B) = (a : B) := by
      have h := a.2
      rw [show (a : B) ∈ FixedPoints.subalgebra K B G ↔ (a : B) ∈ FixedPoints.submonoid G B
        from Iff.rfl, FixedPoints.mem_submonoid] at h
      exact h g
    simp only [Algebra.TensorProduct.map_tmul, tensor_fixedPoints_of_flat_sact_tmul, AlgHom.id_apply]
    exact congrArg (fun z : B => z ⊗ₜ[K] f) ha
  · intro y₁ y₂ h₁ h₂
    simp only [map_add, h₁, h₂]

/-- **Base change of invariants.**  The fixed points of the standard action of `G` on `B ⊗[K] R`
are exactly the image of `B^G ⊗[K] R`. -/
theorem tensor_fixedPoints_of_flat_range_map_eq_fixedPoints :
    Set.range (Algebra.TensorProduct.map (Subalgebra.val (FixedPoints.subalgebra K B G)) (AlgHom.id K R))
      = {x : B ⊗[K] R | ∀ g : G, sact g x = x} := by
  apply Set.Subset.antisymm
  · rintro x ⟨y, rfl⟩ g
    exact tensor_fixedPoints_of_flat_sact_comp_map g y
  · intro x hx
    have hd : x ∈ LinearMap.ker (LinearMap.rTensor R dmap) :=
      tensor_fixedPoints_of_flat_mem_ker_rTensor_dmap.mpr hx
    have h1 : x ∈ LinearMap.range ((LinearMap.ker dmap).subtype.rTensor R) := by
      rw [tensor_fixedPoints_of_flat_range_rTensor_dmap]
      exact hd
    have hval : ((FixedPoints.subalgebra K B G).toSubmodule.subtype :
          (FixedPoints.subalgebra K B G).toSubmodule →ₗ[K] B)
        = (Subalgebra.val (FixedPoints.subalgebra K B G)).toLinearMap := by
      ext y; rfl
    have h2 : x ∈ LinearMap.range ((FixedPoints.subalgebra K B G).toSubmodule.subtype.rTensor R) := by
      rwa [tensor_fixedPoints_of_flat_ker_dmap] at h1
    have h3 : x ∈ LinearMap.range
        ((Subalgebra.val (FixedPoints.subalgebra K B G)).toLinearMap.rTensor R) := by
      rwa [hval] at h2
    obtain ⟨y, hy⟩ := LinearMap.mem_range.mp h3
    exact ⟨y, hy⟩

end Helpers

theorem tensor_fixedPoints_of_flat {K B R G : Type*} [Field K] [CommRing B] [Algebra K B]
    [Group G] [Fintype G] [DecidableEq G] [MulSemiringAction G B] [SMulCommClass G K B]
    [CommRing R] [Algebra K R] [Module.Flat K R] :
    Set.range (Algebra.TensorProduct.map (Subalgebra.val (FixedPoints.subalgebra K B G))
        (AlgHom.id K R)) =
      {x : TensorProduct K B R | ∀ g : G,
        Algebra.TensorProduct.map (MulSemiringAction.toAlgHom K B g) (AlgHom.id K R) x = x} := by
  exact tensor_fixedPoints_of_flat_range_map_eq_fixedPoints

end Work.SymQuot.Invariants
