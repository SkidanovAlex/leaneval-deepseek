import Mathlib.Combinatorics.Quiver.ReflQuiver
import Mathlib.RepresentationTheory.Rep.Iso
import Mathlib.Algebra.Homology.DerivedCategory.Ext.EnoughProjectives
import Submission.Work.SSGRoute.ExtH1
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `H¹(G, M) ≅ Ext¹_G(ℤ, M)` in the `Ext` core

For a group `G` and a `G`-module `M`, the augmentation resolution `0 → I → k[G] → k → 0` of
`Submission/Work/SSGRoute/ExtH1.lean` computes

  `Ext¹_G(ℤ, M) ≅ Hom_{k[G]}(I, M) / im(Hom_{k[G]}(k[G], M) → Hom_{k[G]}(I, M))`,

and the derivation bridge `cocycleHom` identifies `Hom_{k[G]}(I, M)` with the group of crossed
homomorphisms `G → M` while the image of the restriction map is the group of coboundaries.  Hence

  `gammaHom : H¹(G, M) →+ extH (modRep G M) 1`

is an isomorphism, computed on the class of a cocycle `ψ` by `Φ(cocycleHom ψ)`, the connecting map
of the augmentation sequence.  This is the degree-one case of node `E0b` of `DESIGN_EXT.md`.

Everything is stated for a fixed proof `hS : (augSES G).ShortExact` of the short exactness of the
augmentation sequence.
-/

set_option maxHeartbeats 1000000
set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits
open SSGRoute.PTExt

namespace Work.SSGRoute
namespace ExtH1

variable (G : Type) [Group G]

/-! ## The connecting map of the augmentation sequence -/

section Phi

variable (M : Type) [AddCommGroup M] [DistribMulAction G M] [SMulCommClass G Coeff M]

/-- **The connecting map** `Φ : Hom_{k[G]}(I, M) →+ Ext¹_G(ℤ, M)` of the augmentation sequence:
Yoneda composition with the class of `0 → I → k[G] → k → 0`. -/
noncomputable def phiMap (hS : (augSES G).ShortExact) : (augI G ⟶ modRep G M) →+
    extH (modRep G M) 1 where
  toFun f := hS.extClass.comp (Abelian.Ext.mk₀ f) (by norm_num : 1 + 0 = 1)
  map_zero' := by
    show hS.extClass.comp (Abelian.Ext.mk₀ (0 : augI G ⟶ modRep G M)) (by norm_num) = 0
    rw [Abelian.Ext.mk₀_zero, Abelian.Ext.comp_zero]
  map_add' f g := by
    show hS.extClass.comp (Abelian.Ext.mk₀ (f + g)) (by norm_num) =
      hS.extClass.comp (Abelian.Ext.mk₀ f) (by norm_num) +
        hS.extClass.comp (Abelian.Ext.mk₀ g) (by norm_num)
    rw [Abelian.Ext.mk₀_add, Abelian.Ext.comp_add]

/-- **`Φ` is surjective**, because `k[G]` is projective. -/
theorem phiMap_surjective (hS : (augSES G).ShortExact) :
    Function.Surjective (phiMap G M hS) := by
  intro y
  haveI : Subsingleton (Abelian.Ext (regRep G) (modRep G M) (0 + 1)) :=
    Abelian.Ext.subsingleton_of_projective (regRep G) (modRep G M) 0
  have hzero : (Abelian.Ext.mk₀ (augHom G)).comp y (zero_add 1) = 0 := Subsingleton.elim _ _
  obtain ⟨x₁, hx₁⟩ := Abelian.Ext.contravariant_sequence_exact₃ hS (modRep G M) y hzero
    (n₀ := 0) (by norm_num : 1 + 0 = 1)
  refine ⟨Abelian.Ext.addEquiv₀ x₁, ?_⟩
  show hS.extClass.comp (Abelian.Ext.mk₀ (Abelian.Ext.addEquiv₀ x₁)) (by norm_num) = y
  rw [Abelian.Ext.mk₀_addEquiv₀_apply]
  exact hx₁

/-- **The kernel of `Φ`** is the image of the restriction map along `augIncl`: a class dies under
`Φ` exactly when it extends to `k[G]`. -/
theorem phiMap_eq_zero_iff (hS : (augSES G).ShortExact) (f : augI G ⟶ modRep G M) :
    phiMap G M hS f = 0 ↔ ∃ k : regRep G ⟶ modRep G M, f = augIncl G ≫ k := by
  constructor
  · intro hf
    have hf' : hS.extClass.comp (Abelian.Ext.mk₀ f) (by norm_num : 1 + 0 = 1) = 0 := hf
    obtain ⟨x₂, hx₂⟩ := Abelian.Ext.contravariant_sequence_exact₁ hS (modRep G M)
      (Abelian.Ext.mk₀ f) (by norm_num : 1 + 0 = 1) hf'
    refine ⟨Abelian.Ext.addEquiv₀ x₂, ?_⟩
    have h1 : Abelian.Ext.mk₀ f
        = Abelian.Ext.mk₀ (augIncl G ≫ Abelian.Ext.addEquiv₀ x₂) := by
      rw [← Abelian.Ext.mk₀_comp_mk₀, Abelian.Ext.mk₀_addEquiv₀_apply]
      exact hx₂.symm
    exact (Abelian.Ext.mk₀_bijective (X := augI G) (Y := modRep G M)).1 h1
  · rintro ⟨k, rfl⟩
    show hS.extClass.comp (Abelian.Ext.mk₀ (augIncl G ≫ k)) (by norm_num : 1 + 0 = 1) = 0
    rw [← Abelian.Ext.mk₀_comp_mk₀,
      ← Abelian.Ext.comp_assoc_of_second_deg_zero (α := hS.extClass)
        (β := Abelian.Ext.mk₀ (augIncl G)) (γ := Abelian.Ext.mk₀ k) (h₁₃ := by norm_num)]
    rw [ShortComplex.ShortExact.extClass_comp, Abelian.Ext.zero_comp]

end Phi

/-! ## Additivity of the derivation bridge -/

section Add

variable (M : Type) [AddCommGroup M] [DistribMulAction G M] [SMulCommClass G Coeff M]

/-- The crossed-homogeneity conditions of `ExtH1` and of `Work.GroupCohomology` agree. -/
theorem crossedHom_iff (φ : G → M) :
    Work.GroupCohomology.IsCrossedHom G M φ ↔ IsCrossedHom (G := G) (M := M) φ := by
  constructor
  · intro h g h'
    rw [h g h']
    exact add_comm _ _
  · intro h g h'
    rw [h g h']
    exact add_comm _ _

/-- Crossed homomorphisms are closed under addition. -/
theorem isCrossedHom_add (φ ψ : G → M) (hφ : IsCrossedHom (G := G) (M := M) φ)
    (hψ : IsCrossedHom (G := G) (M := M) ψ) :
    IsCrossedHom (G := G) (M := M) (φ + ψ) := by
  intro g h
  show (φ + ψ) (g * h) = (φ + ψ) g + g • (φ + ψ) h
  simp only [Pi.add_apply, smul_add]
  rw [hφ g h, hψ g h]
  abel

/-- `cocycleHom` does not depend on the chosen proof of the crossed-homomorphism condition. -/
theorem cocycleHom_proof_irrel (φ : G → M)
    (h h' : IsCrossedHom (G := G) (M := M) φ) :
    cocycleHom (G := G) (M := M) φ h = cocycleHom (G := G) (M := M) φ h' := by
  apply Rep.hom_ext
  rfl

/-- **The derivation bridge is additive** in the crossed homomorphism. -/
theorem cocycleHom_add (φ ψ : G → M) (hφ : IsCrossedHom (G := G) (M := M) φ)
    (hψ : IsCrossedHom (G := G) (M := M) ψ) :
    cocycleHom (G := G) (M := M) (φ + ψ) (isCrossedHom_add G M φ ψ hφ hψ) =
      cocycleHom (G := G) (M := M) φ hφ + cocycleHom (G := G) (M := M) ψ hψ := by
  apply hom_ext_augDiff G M
  intro γ
  rw [cocycleHom_augDiff]
  have hsum : (cocycleHom (G := G) (M := M) φ hφ
        + cocycleHom (G := G) (M := M) ψ hψ).hom (augDiff G γ)
      = (cocycleHom (G := G) (M := M) φ hφ).hom (augDiff G γ)
        + (cocycleHom (G := G) (M := M) ψ hψ).hom (augDiff G γ) := by
    rw [Rep.add_hom, Representation.IntertwiningMap.coe_add, Pi.add_apply]
  rw [hsum, cocycleHom_augDiff, cocycleHom_augDiff]
  rfl

/-- The crossed-homomorphism condition for the coboundary `d⁰ m`. -/
theorem isCrossedHom_d0 (m : M) :
    IsCrossedHom (G := G) (M := M) (fun γ => γ • m - m) := by
  intro g h
  show (g * h) • m - m = (g • m - m) + g • (h • m - m)
  rw [mul_smul, smul_sub]
  abel

/-- **The coboundary `γ ↦ γ • m - m` extends to `k[G]`.** -/
theorem cocycleHom_d0 (m : M) :
    cocycleHom (G := G) (M := M) (fun γ => γ • m - m) (isCrossedHom_d0 G M m) =
      augIncl G ≫ Rep.leftRegularHom (modRep G M) m := by
  apply hom_ext_augDiff G M
  intro γ
  have h1 : (cocycleHom (G := G) (M := M) (fun γ => γ • m - m) (isCrossedHom_d0 G M m)).hom
      (augDiff G γ) = γ • m - m :=
    cocycleHom_augDiff (G := G) (M := M) _ _ γ
  have h2 : (augIncl G ≫ Rep.leftRegularHom (modRep G M) m).hom (augDiff G γ)
      = (Rep.leftRegularHom (modRep G M) m).hom (ebas G γ - ebas G 1) := by
    rw [Rep.hom_comp, Representation.IntertwiningMap.comp_apply, augIncl_augDiff]
  have h3 : (Rep.leftRegularHom (modRep G M) m).hom (ebas G γ - ebas G 1) = γ • m - m := by
    rw [map_sub, Rep.leftRegularHom_hom_single, Rep.leftRegularHom_hom_single,
      one_smul, one_smul,
      Rep.ofDistribMulAction_ρ_apply_apply (k := Coeff) (G := G) (A := M) γ m,
      Rep.ofDistribMulAction_ρ_apply_apply (k := Coeff) (G := G) (A := M) (1 : G) m,
      one_smul]
  rw [h1, h2, h3]

end Add

/-! ## The map `H¹(G, M) →+ Ext¹_G(ℤ, M)` -/

section Gamma

variable (M : Type) [AddCommGroup M] [DistribMulAction G M] [SMulCommClass G Coeff M]

/-- `↥(modRep G M)` regarded as the type `M` it is definitionally. -/
abbrev modRepToM : ↥(modRep G M) → M := fun x => x

/-- The action of `G` on `modRep G M`, read in `M`. -/
theorem modRepToM_rho (γ : G) (x : ↥(modRep G M)) :
    modRepToM G M ((modRep G M).ρ γ x) = γ • modRepToM G M x :=
  Rep.ofDistribMulAction_ρ_apply_apply (k := Coeff) (G := G) (A := M) γ (modRepToM G M x)

/-- **The kernel of the composite of `cocycleHom` and `Φ`** on a crossed homomorphism: it vanishes
exactly when the crossed homomorphism is a coboundary. -/
theorem phiMap_cocycleHom_eq_zero_iff (hS : (augSES G).ShortExact) (φ : G → M)
    (hφ : IsCrossedHom (G := G) (M := M) φ) :
    phiMap G M hS (cocycleHom (G := G) (M := M) φ hφ) = 0 ↔
      ∃ m : M, ∀ γ : G, φ γ = γ • m - m := by
  constructor
  · intro h
    obtain ⟨k, hk⟩ := (phiMap_eq_zero_iff G M hS _).mp h
    refine ⟨k.hom (ebas G 1), fun γ => ?_⟩
    have h2 : φ γ = modRepToM G M (k.hom (ebas G γ)) - modRepToM G M (k.hom (ebas G 1)) := by
      rw [← cocycleHom_augDiff (G := G) (M := M) φ hφ γ, hk, Rep.hom_comp,
        Representation.IntertwiningMap.comp_apply, augIncl_augDiff, map_sub]
    have h3 : modRepToM G M (k.hom (ebas G γ))
        = γ • modRepToM G M (k.hom (ebas G 1)) := by
      rw [show ebas G γ = (regRep G).ρ γ (ebas G 1) from by rw [regRep_ρ_ebas, mul_one],
        Rep.hom_comm_apply]
      exact modRepToM_rho G M γ (k.hom (ebas G 1))
    rw [h2, h3]
  · rintro ⟨m, hm⟩
    have hcoe : cocycleHom (G := G) (M := M) φ hφ =
        cocycleHom (G := G) (M := M) (fun γ => γ • m - m) (isCrossedHom_d0 G M m) := by
      apply hom_ext_augDiff G M
      intro γ
      rw [cocycleHom_augDiff, cocycleHom_augDiff]
      exact hm γ
    rw [hcoe, cocycleHom_d0]
    exact (phiMap_eq_zero_iff G M hS _).mpr ⟨Rep.leftRegularHom (modRep G M) m, rfl⟩

/-- Additivity of the composite of `cocycleHom` and `Φ` on crossed homomorphisms. -/
theorem phiMap_cocycleHom_add (hS : (augSES G).ShortExact) (φ ψ : G → M)
    (hφ : IsCrossedHom (G := G) (M := M) φ) (hψ : IsCrossedHom (G := G) (M := M) ψ)
    (h : IsCrossedHom (G := G) (M := M) (φ + ψ)) :
    phiMap G M hS (cocycleHom (G := G) (M := M) (φ + ψ) h) =
      phiMap G M hS (cocycleHom (G := G) (M := M) φ hφ) +
        phiMap G M hS (cocycleHom (G := G) (M := M) ψ hψ) := by
  rw [show cocycleHom (G := G) (M := M) (φ + ψ) h
      = cocycleHom (G := G) (M := M) (φ + ψ) (isCrossedHom_add G M φ ψ hφ hψ) from
    cocycleHom_proof_irrel (G := G) (M := M) (φ + ψ) h _,
    cocycleHom_add G M φ ψ hφ hψ, map_add]

/-- The map on the `1`-cocycles `Z¹(G, M) →+ Ext¹_G(ℤ, M)`. -/
noncomputable def gammaZ1 (hS : (augSES G).ShortExact) :
    ↥(Work.GroupCohomology.Z1 G M) →+ extH (modRep G M) 1 :=
  AddMonoidHom.mk' (fun ψ => phiMap G M hS (cocycleHom (G := G) (M := M) ψ.1
      ((crossedHom_iff (G := G) (M := M) ψ.1).mp ψ.2))) (by
    intro ψ ψ'
    exact phiMap_cocycleHom_add G M hS ψ.1 ψ'.1 _ _ _)

/-- The computation rule for `gammaZ1`. -/
theorem gammaZ1_apply (hS : (augSES G).ShortExact) (ψ : ↥(Work.GroupCohomology.Z1 G M)) :
    gammaZ1 G M hS ψ = phiMap G M hS (cocycleHom (G := G) (M := M) ψ.1
      ((crossedHom_iff (G := G) (M := M) ψ.1).mp ψ.2)) := rfl

/-- **The kernel of `gammaZ1`**: a cocycle maps to `0` exactly when it is a coboundary. -/
theorem gammaZ1_eq_zero_iff (hS : (augSES G).ShortExact)
    (ψ : ↥(Work.GroupCohomology.Z1 G M)) :
    gammaZ1 G M hS ψ = 0 ↔ ψ.1 ∈ Work.GroupCohomology.B1 G M := by
  rw [gammaZ1_apply,
    phiMap_cocycleHom_eq_zero_iff G M hS ψ.1 ((crossedHom_iff (G := G) (M := M) ψ.1).mp ψ.2),
    Work.GroupCohomology.mem_B1_iff]
  constructor
  · rintro ⟨m, hm⟩
    refine ⟨m, funext fun γ => ?_⟩
    rw [Work.GroupCohomology.d0_apply]
    exact (hm γ).symm
  · rintro ⟨m, hm⟩
    refine ⟨m, fun γ => ?_⟩
    rw [show (↑ψ : G → M) γ = (Work.GroupCohomology.d0 G M m) γ from (congrFun hm γ).symm,
      Work.GroupCohomology.d0_apply]

/-- `H1π ψ = 0` exactly for the coboundaries. -/
theorem H1π_eq_zero_iff (ψ : ↥(Work.GroupCohomology.Z1 G M)) :
    Work.GroupCohomology.H1π G M ψ = 0 ↔ ψ.1 ∈ Work.GroupCohomology.B1 G M := by
  rw [← AddMonoidHom.mem_ker, Work.GroupCohomology.H1π, QuotientAddGroup.ker_mk',
    AddSubgroup.mem_comap]
  exact Iff.rfl

/-- **The degree-one bridge** `H¹(G, M) →+ Ext¹_G(ℤ, M)`, induced by `gammaZ1` on the
`1`-cocycles. -/
noncomputable def gammaHom (hS : (augSES G).ShortExact) :
    Work.GroupCohomology.H1 G M →+ extH (modRep G M) 1 :=
  QuotientAddGroup.lift
    ((Work.GroupCohomology.B1 G M).comap (Work.GroupCohomology.Z1 G M).subtype)
    (gammaZ1 G M hS)
    (fun ψ hψ => (gammaZ1_eq_zero_iff G M hS ψ).mpr (AddSubgroup.mem_comap.mp hψ))

/-- The computation rule for `gammaHom` on the class of a cocycle. -/
theorem gammaHom_H1π (hS : (augSES G).ShortExact) (ψ : ↥(Work.GroupCohomology.Z1 G M)) :
    gammaHom G M hS (Work.GroupCohomology.H1π G M ψ) = gammaZ1 G M hS ψ :=
  QuotientAddGroup.lift_mk' _ _ _

/-- **`gammaHom` is injective**: its kernel is the group of coboundaries. -/
theorem gammaHom_injective (hS : (augSES G).ShortExact) :
    Function.Injective (gammaHom G M hS) := by
  rw [← AddMonoidHom.ker_eq_bot_iff, AddSubgroup.eq_bot_iff_forall]
  intro x hx
  rw [AddMonoidHom.mem_ker] at hx
  obtain ⟨ψ, rfl⟩ := QuotientAddGroup.mk'_surjective
    ((Work.GroupCohomology.B1 G M).comap (Work.GroupCohomology.Z1 G M).subtype) x
  rw [show gammaHom G M hS
      (QuotientAddGroup.mk' ((Work.GroupCohomology.B1 G M).comap
        (Work.GroupCohomology.Z1 G M).subtype) ψ) = gammaZ1 G M hS ψ from
    gammaHom_H1π G M hS ψ] at hx
  exact (H1π_eq_zero_iff G M ψ).mpr ((gammaZ1_eq_zero_iff G M hS ψ).mp hx)

/-- **`gammaHom` is surjective**: every `Ext¹` class comes from a `1`-cocycle. -/
theorem gammaHom_surjective (hS : (augSES G).ShortExact) :
    Function.Surjective (gammaHom G M hS) := by
  intro y
  obtain ⟨f, hf⟩ := phiMap_surjective G M hS y
  refine ⟨Work.GroupCohomology.H1π G M ⟨derivCochain (G := G) (M := M) f, ?_⟩, ?_⟩
  · rw [Work.GroupCohomology.mem_Z1_iff]
    exact (crossedHom_iff (G := G) (M := M) _).mpr
      (derivCochain_isCrossedHom (G := G) (M := M) f)
  · rw [gammaHom_H1π, gammaZ1_apply,
      show cocycleHom (G := G) (M := M) (derivCochain (G := G) (M := M) f) _
        = f from cocycleHom_derivCochain (G := G) (M := M) f]
    exact hf

end Gamma

end ExtH1
end Work.SSGRoute
