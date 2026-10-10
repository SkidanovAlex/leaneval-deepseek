import Mathlib.GroupTheory.Nilpotent
import Mathlib.Order.CompletePartialOrder
import Mathlib.Algebra.Field.ZMod
import Mathlib.Combinatorics.Quiver.ReflQuiver
import Mathlib.FieldTheory.Galois.Abelian
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Mathlib.RepresentationTheory.Homological.GroupCohomology.LongExactSequence
import Mathlib.Algebra.Homology.DerivedCategory.Ext.Basic
import Submission.Work.SSGRoute.CFTSide.cyclicNormCriterion_classesK
import Submission.Work.SSGRoute.CFTSide.exists_cyclic_prime_notMem_normClassSubgroup
import Submission.Work.SSGRoute.PT.e3_exists_level_of_cyclic
import Submission.Work.SSGRoute.PT.e3_level_comparison
import Submission.Work.SSGRoute.Sha2Lib.classGroupRep_norm_eq_classIncl
import Submission.Work.SSGRoute.Sha2Lib.classIncl_hom_fixed
import Submission.Work.SSGRoute.Sha2Lib.exists_addHom_ker_fixingSubgroup
import Submission.Work.SSGRoute.Sha2Lib.mem_normClassSubgroup_iff_of_algEquiv
import Submission.Work.SSGRoute.classIncl_mem_invariants_range
import Submission.Work.SSGRoute.e3_ext_spine
import Submission.Work.SSGRoute.phi1_classIncl_compat

/-!
# `E3Ω` from its three named inputs (node `E3In`)

Assembles `Work.SSGRoute.E3In.phi1_trivial_mono_in_of_inputs` from
* the `Ext`/group-cohomology bridge `b` (node `E0b`),
* the `p`-power criterion `hPTW` for `C_k`,
* the general-level cyclic norm criterion `hGen`,

using the reusable lemmas produced by the `Sha2Lib` and `PT` lanes.
-/

set_option backward.isDefEq.respectTransparency false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

open CategoryTheory SSGRoute.PTExt

namespace Work.SSGRoute.E3In

theorem classIncl_injective (k K L : Type) [Field k] [NumberField k] [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra k K] [Algebra K L] [Algebra k L] [IsScalarTower k K L]
    [FiniteDimensional k K] [IsGalois k K] [FiniteDimensional k L] [IsGalois k L] :
    Function.Injective (Rep.Hom.hom (classIncl k K L)) := by
  obtain ⟨u, hu, φ, hφ, hι⟩ := classIncl_isCanonical k K L
  obtain ⟨ψ, hψ⟩ := NK.GlobalCFT.Inclusion.globalCFT_ideleClassGroup_inclusion_exists u hu φ hφ
  have hclass' : ∀ q : NK.GlobalCFT.IdeleClassGroup K,
      (Rep.Hom.hom (classIncl k K L)) (Additive.ofMul q) = Additive.ofMul (ψ q) := by
    intro q
    obtain ⟨x, rfl⟩ := NK.GlobalCFT.IdeleClassGroup.mk_surjective K q
    exact (hι x).trans (congrArg Additive.ofMul (hψ x).symm)
  have hψinj := NK.GlobalCFT.Inclusion.globalCFT_ideleClassGroup_inclusion_injective u hu φ hφ ψ hψ
  intro a1 a2 h
  have h1 : Additive.ofMul (ψ (Additive.toMul a1)) = Additive.ofMul (ψ (Additive.toMul a2)) :=
    (hclass' (Additive.toMul a1)).symm.trans (h.trans (hclass' (Additive.toMul a2)))
  have h2 : Additive.toMul a1 = Additive.toMul a2 := hψinj (Additive.ofMul.injective h1)
  exact congrArg Additive.ofMul h2

theorem exists_level_data (p : ℕ) [Fact p.Prime] (k K Ω : Type) [Field k] [NumberField k]
    [Field K] [NumberField K] [Algebra k K] [FiniteDimensional k K] [IsGalois k K] [Field Ω]
    [IsAlgClosed Ω] [Algebra K Ω] [Algebra k Ω] [IsScalarTower k K Ω]
    (F₀ : IntermediateField k Ω) [NumberField ↥F₀] [FiniteDimensional k ↥F₀] [IsGalois k ↥F₀]
    (hF : Module.finrank k ↥F₀ = p) :
    ∃ (L : IntermediateField K Ω) (F : IntermediateField k ↥L),
      Nonempty (NumberField ↥L) ∧ Nonempty (FiniteDimensional k ↥L) ∧ Nonempty (IsGalois k ↥L) ∧
      Nonempty (FiniteDimensional k ↥F) ∧ Nonempty (IsGalois k ↥F) ∧ Nonempty (NumberField ↥F) ∧
      Module.finrank k ↥F = p ∧ Nonempty (↥F ≃ₐ[k] ↥F₀) := by
  let Kimg : IntermediateField k Ω := IntermediateField.restrictScalars k (⊥ : IntermediateField K Ω)
  haveI hKimg_fd : FiniteDimensional k ↥Kimg :=
    LinearEquiv.finiteDimensional
      (((IntermediateField.botEquiv K Ω).toLinearEquiv).restrictScalars k).symm
  haveI hKimg_gal : IsGalois k ↥Kimg :=
    IsGalois.of_algEquiv (((IntermediateField.botEquiv K Ω).restrictScalars k).symm)
  let L₀ : IntermediateField k Ω := F₀ ⊔ Kimg
  haveI hL₀_fd : FiniteDimensional k ↥L₀ := IntermediateField.finiteDimensional_sup F₀ Kimg
  haveI hL₀_gal : IsGalois k ↥L₀ :=
    isGalois_iff.mpr ⟨IntermediateField.isSeparable_sup k Ω F₀ Kimg,
      IntermediateField.normal_sup k Ω F₀ Kimg⟩
  let L : IntermediateField K Ω := (L₀.toSubfield).toIntermediateField (fun x => by
    have hx : algebraMap K Ω x ∈ (⊥ : IntermediateField K Ω) :=
      (IntermediateField.mem_bot).mpr ⟨x, rfl⟩
    have hx' : algebraMap K Ω x ∈ Kimg := by
      rw [IntermediateField.mem_restrictScalars]; exact hx
    exact (le_sup_right : Kimg ≤ F₀ ⊔ Kimg) hx')
  have hLcoe : (L : Set Ω) = (L₀ : Set Ω) := Subfield.coe_toIntermediateField _ _
  haveI hL_fd : FiniteDimensional k ↥L := hL₀_fd
  haveI hL_gal : IsGalois k ↥L := hL₀_gal
  haveI hL_nf : NumberField ↥L := NumberField.of_module_finite k ↥L
  let F : IntermediateField k ↥L :=
    IntermediateField.comap ((IntermediateField.val L).restrictScalars k) F₀
  have hF₀le : (F₀ : Set Ω) ⊆ (L : Set Ω) := by
    intro x hx
    rw [hLcoe]
    exact (le_sup_left : F₀ ≤ F₀ ⊔ Kimg) hx
  let e : ↥F ≃ₐ[k] ↥F₀ :=
    { toFun := fun x => ⟨(x : ↥L), x.2⟩
      invFun := fun y => ⟨⟨(y : Ω), hF₀le y.2⟩, y.2⟩
      left_inv := fun x => Subtype.ext rfl
      right_inv := fun y => Subtype.ext rfl
      map_mul' := fun x y => Subtype.ext rfl
      map_add' := fun x y => Subtype.ext rfl
      commutes' := fun c => Subtype.ext rfl }
  haveI hF_fd : FiniteDimensional k ↥F := LinearEquiv.finiteDimensional e.toLinearEquiv.symm
  haveI hF_gal : IsGalois k ↥F := IsGalois.of_algEquiv e.symm
  haveI hF_nf : NumberField ↥F := NumberField.of_module_finite k ↥F
  refine ⟨L, F, ⟨hL_nf⟩, ⟨hL_fd⟩, ⟨hL_gal⟩, ⟨hF_fd⟩, ⟨hF_gal⟩, ⟨hF_nf⟩, ?_, ⟨e⟩⟩
  exact (LinearEquiv.finrank_eq e.toLinearEquiv).trans hF

end Work.SSGRoute.E3In

namespace Work.SSGRoute.E3In

open Work.SSGRoute

theorem exists_pushClass_powHomCls (p : ℕ) [Fact p.Prime] (k K : Type) [Field k] [NumberField k]
    [Field K] [NumberField K] [Algebra k K] [FiniteDimensional k K] [IsGalois k K]
    (x : Abelian.Ext (Rep.trivial Coeff (K ≃ₐ[k] K) (ZMod p)) (classesK k K) 1) :
    ∃ (a : classesK k K) (ha : ∀ σ : K ≃ₐ[k] K, (classesK k K).ρ σ a = a),
      x = E3Ext.pushClass p (K ≃ₐ[k] K) (classesK k K) (Phi1.powHomCls k K a ha) := by
  obtain ⟨φ, hφ⟩ := E3Ext.exists_pushClass (G := K ≃ₐ[k] K) p (classesK k K)
    (E3Ext.subsingleton_extH_classesK k K) x
  have hafix : ∀ σ : K ≃ₐ[k] K, (classesK k K).ρ σ (φ.hom 1) = φ.hom 1 := by
    intro σ
    have h := Rep.hom_comm_apply (A := unitRep (K ≃ₐ[k] K)) (B := classesK k K) φ σ (1 : Coeff)
    simp only [unitRep] at h
    exact h.symm
  have hφeq : φ = Phi1.powHomCls k K (φ.hom 1) hafix := by
    apply Rep.hom_ext
    apply Representation.IntertwiningMap.ext
    apply LinearMap.ext
    intro n
    show (Rep.Hom.hom φ) n = (Rep.Hom.hom (Phi1.powHomCls k K (φ.hom 1) hafix)) n
    rw [Phi1.powHomCls_apply]
    have hn : n • (1 : Coeff) = n := by simp
    have key2 : (Rep.Hom.hom φ) n = (Rep.Hom.hom φ) (n • (1 : Coeff)) := by rw [hn]
    exact key2.trans (LinearMap.map_smul (Rep.Hom.hom φ).toLinearMap n (1 : Coeff))
  exact ⟨φ.hom 1, hafix, by
    rw [hφ]
    exact congrArg (fun ψ => E3Ext.pushClass p (K ≃ₐ[k] K) (classesK k K) ψ) hφeq⟩

end Work.SSGRoute.E3In

namespace Work.SSGRoute.E3In

open Work.SSGRoute

theorem norm_mem_of_vanishing (p : ℕ) [Fact p.Prime] (k K Ω : Type) [Field k] [NumberField k]
    [Field K] [NumberField K] [Algebra k K] [FiniteDimensional k K] [IsGalois k K] [Field Ω]
    [IsAlgClosed Ω] [Algebra K Ω] [Algebra k Ω] [IsScalarTower k K Ω]
    (b : Phi1.ExtGroupCohomologyBridge)
    (hGen : ∀ (L : IntermediateField K Ω) [NumberField ↥L] [FiniteDimensional k ↥L]
        [IsGalois k ↥L]
        (F : IntermediateField k ↥L) [FiniteDimensional k ↥F] [IsGalois k ↥F] [NumberField ↥F],
        Module.finrank k ↥F = p →
        ∀ (a : classesK k ↥L) (hafix : ∀ σ : ↥L ≃ₐ[k] ↥L, (classesK k ↥L).ρ σ a = a)
          (g : Additive (↥L ≃ₐ[k] ↥L) →+ ZMod p), g ≠ 0 →
          (∀ σ : ↥L ≃ₐ[k] ↥L, g (Additive.ofMul σ) = 0 ↔ σ ∈ F.fixingSubgroup) →
          groupCohomology.map (MonoidHom.id (↥L ≃ₐ[k] ↥L)) (Phi1.powHomCls k ↥L a hafix) 2
            ((groupCohomology.δ (Phi1.coeffSES_shortExact (↥L ≃ₐ[k] ↥L) p) 1 2 rfl).hom
              (groupCohomology.H1π (Rep.trivial Coeff (↥L ≃ₐ[k] ↥L) (ZMod p))
                ⟨g ∘ Additive.ofMul, groupCohomology.mem_cocycles₁_of_addMonoidHom
                  (A := Rep.trivial Coeff (↥L ≃ₐ[k] ↥L) (ZMod p)) g⟩)) = 0 →
          ∃ b : classesK k ↥F, classIncl k ↥F ↥L ((classesK k ↥F).norm.hom b) = a)
    (a₀ : classesK k k) (φ : unitRep (K ≃ₐ[k] K) ⟶ classesK k K)
    (ha₀ : (classIncl k k K).hom a₀ = φ.hom 1)
    (hx : PhiOneVanishesIn (k := k) (K := K) (Ω := Ω)
      (E3Ext.pushClass p (K ≃ₐ[k] K) (classesK k K) φ))
    (F₀ : IntermediateField k Ω) [NumberField ↥F₀] [FiniteDimensional k ↥F₀] [IsGalois k ↥F₀]
    (hF₀ : Module.finrank k ↥F₀ = p) :
    Additive.toMul a₀ ∈ NK.GlobalCFT.Idele.normClassSubgroup k ↥F₀ := by
  obtain ⟨L, F, hLnf, hLfd, hLgal, hFfd, hFgal, hFnf, hFdeg, ⟨e⟩⟩ :=
    exists_level_data p k K Ω F₀ hF₀
  letI : NumberField ↥L := hLnf.some
  letI : FiniteDimensional k ↥L := hLfd.some
  letI : IsGalois k ↥L := hLgal.some
  letI : FiniteDimensional k ↥F := hFfd.some
  letI : IsGalois k ↥F := hFgal.some
  letI : NumberField ↥F := hFnf.some
  have hfixφ : ∀ σ : K ≃ₐ[k] K, (classesK k K).ρ σ (φ.hom 1) = φ.hom 1 := by
    intro σ
    have h := Rep.hom_comm_apply (A := unitRep (K ≃ₐ[k] K)) (B := classesK k K) φ σ (1 : Coeff)
    simp only [unitRep] at h
    exact h.symm
  have hafix' : ∀ σ : ↥L ≃ₐ[k] ↥L,
      (classesK k ↥L).ρ σ ((classIncl k K ↥L).hom (φ.hom 1))
        = (classIncl k K ↥L).hom (φ.hom 1) :=
    Sha2Lib.classIncl_hom_fixed k K ↥L (φ.hom 1) hfixφ
  obtain ⟨g, hgne, hgker⟩ := Sha2Lib.exists_addHom_ker_fixingSubgroup k ↥L p F hFdeg
  have hvan : groupCohomology.map (MonoidHom.id (↥L ≃ₐ[k] ↥L))
        (Phi1.powHomCls k ↥L ((classIncl k K ↥L).hom (φ.hom 1)) hafix') 2
        ((groupCohomology.δ (Phi1.coeffSES_shortExact (↥L ≃ₐ[k] ↥L) p) 1 2 rfl).hom
          (groupCohomology.H1π (Rep.trivial Coeff (↥L ≃ₐ[k] ↥L) (ZMod p))
            ⟨g ∘ Additive.ofMul, groupCohomology.mem_cocycles₁_of_addMonoidHom
              (A := Rep.trivial Coeff (↥L ≃ₐ[k] ↥L) (ZMod p)) g⟩)) = 0 := by
    let h1 : groupCohomology (Rep.trivial Coeff (↥L ≃ₐ[k] ↥L) (ZMod p)) 1 :=
      groupCohomology.H1π (Rep.trivial Coeff (↥L ≃ₐ[k] ↥L) (ZMod p))
        ⟨g ∘ Additive.ofMul, groupCohomology.mem_cocycles₁_of_addMonoidHom
          (A := Rep.trivial Coeff (↥L ≃ₐ[k] ↥L) (ZMod p)) g⟩
    let hh : extH (Rep.res (galRes k K ↥L) (Rep.trivial Coeff (K ≃ₐ[k] K) (ZMod p))) 1 :=
      (b.e 1 (↥L ≃ₐ[k] ↥L) (Rep.trivial Coeff (↥L ≃ₐ[k] ↥L) (ZMod p))) h1
    have hsymm : (b.e 1 (↥L ≃ₐ[k] ↥L) (Rep.trivial Coeff (↥L ≃ₐ[k] ↥L) (ZMod p))).symm hh = h1 :=
      AddEquiv.symm_apply_apply _ _
    have hxL := hx L hh
    have key := (E3Ext.bridge_pairing_eq_zero_iff b p ↥L φ hh).mp hxL
    rw [hsymm] at key
    rw [Work.SSGRoute.PT.e3_level_comparison k K ↥L φ hafix'] at key
    exact key
  obtain ⟨bb, hbb⟩ := hGen L F hFdeg ((classIncl k K ↥L).hom (φ.hom 1)) hafix' g hgne hgker hvan
  haveI : FiniteDimensional K ↥L := FiniteDimensional.right k K ↥L
  haveI : IsGalois K ↥L := IsGalois.tower_top_of_isGalois k K ↥L
  haveI : FiniteDimensional ↥F ↥L := FiniteDimensional.right k ↥F ↥L
  haveI : IsGalois ↥F ↥L := IsGalois.tower_top_of_isGalois k ↥F ↥L
  have htrans1 : (classIncl k K ↥L).hom (φ.hom 1) = (classIncl k k ↥L).hom a₀ := by
    rw [← ha₀]
    exact Work.SSGRoute.classIncl_compat_apply (k := k) (K := k) (L := K) (L₂ := ↥L) a₀
  have htrans2 : (classIncl k k ↥L).hom a₀
      = (classIncl k ↥F ↥L).hom ((classIncl k k ↥F).hom a₀) :=
    (Work.SSGRoute.classIncl_compat_apply (k := k) (K := k) (L := ↥F) (L₂ := ↥L) a₀).symm
  have hnorm_eq : (classesK k ↥F).norm.hom bb = (classIncl k k ↥F).hom a₀ := by
    apply classIncl_injective k ↥F ↥L
    rw [hbb, htrans1, htrans2]
  have hkey : (classIncl k k ↥F).hom a₀ = (classIncl k k ↥F).hom
      (Additive.ofMul (NK.GlobalCFT.IdeleClassGroup.normClassHom k ↥F (Additive.toMul bb))) := by
    rw [← hnorm_eq]
    exact Sha2Lib.classGroupRep_norm_eq_classIncl k ↥F (Additive.toMul bb)
  have hfinal : a₀ = Additive.ofMul
      (NK.GlobalCFT.IdeleClassGroup.normClassHom k ↥F (Additive.toMul bb)) :=
    classIncl_injective k k ↥F hkey
  have hmemF : Additive.toMul a₀ ∈ NK.GlobalCFT.Idele.normClassSubgroup k ↥F := by
    refine NK.GlobalCFT.Idele.mem_normClassSubgroup.mpr ⟨Additive.toMul bb, ?_⟩
    show NK.GlobalCFT.IdeleClassGroup.normClassHom k ↥F (Additive.toMul bb) = Additive.toMul a₀
    rw [hfinal]
    exact (toMul_ofMul _).symm
  exact (Sha2Lib.mem_normClassSubgroup_iff_of_algEquiv e (Additive.toMul a₀)).mp hmemF

end Work.SSGRoute.E3In

namespace Work.SSGRoute.E3In

open Work.SSGRoute

theorem phi1_trivial_mono_in_of_inputs (p : ℕ) [Fact p.Prime] (k K Ω : Type) [Field k] [NumberField k] [Field K] [NumberField K] [Algebra k K] [FiniteDimensional k K] [IsGalois k K] [Field Ω] [IsAlgClosed Ω] [Algebra K Ω] [Algebra k Ω] [IsScalarTower k K Ω] (ζ : k) (hζ : IsPrimitiveRoot ζ p) (b : SSGRoute.Phi1.ExtGroupCohomologyBridge) (hPTW : ∀ x : NK.GlobalCFT.IdeleClassGroup k, (∀ V : Subgroup (NK.GlobalCFT.IdeleClassGroup k), V.FiniteIndex → IsOpen (V : Set (NK.GlobalCFT.IdeleClassGroup k)) → V.index = p → x ∈ V) → ∃ y : NK.GlobalCFT.IdeleClassGroup k, y ^ p = x) (hGen : ∀ (L : IntermediateField K Ω) [NumberField L] [FiniteDimensional k L] [IsGalois k L] (F : IntermediateField k L) [FiniteDimensional k F] [IsGalois k F] [NumberField F], Module.finrank k F = p → ∀ (a : SSGRoute.PTExt.classesK k L) (hafix : ∀ σ : L ≃ₐ[k] L, (SSGRoute.PTExt.classesK k L).ρ σ a = a) (g : Additive (L ≃ₐ[k] L) →+ ZMod p), g ≠ 0 → (∀ σ : L ≃ₐ[k] L, g (Additive.ofMul σ) = 0 ↔ σ ∈ F.fixingSubgroup) → groupCohomology.map (MonoidHom.id (L ≃ₐ[k] L)) (SSGRoute.Phi1.powHomCls k L a hafix) 2 ((groupCohomology.δ (SSGRoute.Phi1.coeffSES_shortExact (L ≃ₐ[k] L) p) 1 2 rfl).hom (groupCohomology.H1π (Rep.trivial SSGRoute.PTExt.Coeff (L ≃ₐ[k] L) (ZMod p)) ⟨g ∘ Additive.ofMul, groupCohomology.mem_cocycles₁_of_addMonoidHom (A := Rep.trivial SSGRoute.PTExt.Coeff (L ≃ₐ[k] L) (ZMod p)) g⟩)) = 0 → ∃ b : SSGRoute.PTExt.classesK k F, SSGRoute.PTExt.classIncl k F L ((SSGRoute.PTExt.classesK k F).norm.hom b) = a) (x : CategoryTheory.Abelian.Ext.{0} (Rep.trivial SSGRoute.PTExt.Coeff (K ≃ₐ[k] K) (ZMod p)) (SSGRoute.PTExt.classesK k K) 1) (hx : SSGRoute.PTExt.PhiOneVanishesIn (k := k) (K := K) (Ω := Ω) x) : x = 0 := by
  obtain ⟨a_K, haK, hxφ⟩ := exists_pushClass_powHomCls p k K x
  rw [hxφ] at hx ⊢
  obtain ⟨a₀, ha₀⟩ := classIncl_mem_invariants_range k K a_K haK
  suffices hpow : ∃ y : NK.GlobalCFT.IdeleClassGroup k, y ^ p = Additive.toMul a₀ by
    obtain ⟨y, hy⟩ := hpow
    have hfixy : ∀ σ : k ≃ₐ[k] k, (classesK k k).ρ σ (Additive.ofMul y) = Additive.ofMul y := by
      intro σ
      rw [Subsingleton.elim σ 1]
      simp
      rfl
    have hb := Sha2Lib.classIncl_hom_fixed k k K (Additive.ofMul y) hfixy
    have ha0' : a₀ = Additive.ofMul (y ^ p) := by rw [hy]; rfl
    have hA : a_K = p • ((classIncl k k K).hom (Additive.ofMul y)) := by
      rw [← ha₀, ha0', ofMul_pow, map_nsmul]
      rfl
    refine E3Ext.pushClass_powHomCls_eq_zero_of_eq_smul p k K a_K
      ((classIncl k k K).hom (Additive.ofMul y)) haK hb ?_
    rw [show (p : SSGRoute.PTExt.Coeff) •
        ((classIncl k k K).hom (Additive.ofMul y))
        = p • ((classIncl k k K).hom (Additive.ofMul y)) from by simp]
    exact hA
  by_contra hnot
  obtain ⟨E, hFE, hNE, hAE, hfdE, hgalE, hdegE, hnotnorm⟩ :=
    exists_cyclic_prime_notMem_normClassSubgroup k p (Additive.toMul a₀) hPTW hnot
  letI : Algebra k E := hAE
  letI : FiniteDimensional k E := hfdE
  haveI : IsGalois k E := hgalE
  obtain ⟨F₀, ⟨eiso⟩, hF₀deg⟩ :=
    Work.SSGRoute.PT.e3_exists_level_of_cyclic p k Ω (⊥ : IntermediateField k Ω) E hdegE
  haveI : FiniteDimensional k ↥F₀ :=
    FiniteDimensional.of_finrank_pos (by rw [hF₀deg]; exact (Fact.out : p.Prime).pos)
  haveI : IsGalois k ↥F₀ := IsGalois.of_algEquiv eiso
  haveI : NumberField ↥F₀ := NumberField.of_module_finite k ↥F₀
  have ha₀' : (classIncl k k K).hom a₀ = (Phi1.powHomCls k K a_K haK).hom 1 := by
    rw [ha₀, Phi1.powHomCls_apply]
    simp
  have hmem := norm_mem_of_vanishing p k K Ω b hGen a₀ (Phi1.powHomCls k K a_K haK) ha₀' hx F₀ hF₀deg
  exact hnotnorm ((Sha2Lib.mem_normClassSubgroup_iff_of_algEquiv eiso (Additive.toMul a₀)).mpr hmem)

end Work.SSGRoute.E3In
