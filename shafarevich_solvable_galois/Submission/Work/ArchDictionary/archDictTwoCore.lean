import Mathlib.FieldTheory.KrullTopology
import Mathlib.GroupTheory.Nilpotent
import Mathlib.RingTheory.Henselian
import Mathlib.Algebra.Field.ZMod
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Combinatorics.Quiver.ReflQuiver
import Mathlib.RepresentationTheory.Rep.Res
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.NumberTheory.NumberField.Completion.InfinitePlace
import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
import Mathlib.Algebra.Homology.DerivedCategory.Ext.Basic
import Submission.Work.SSGRoute.ArchDictionary.coeff_two_coboundary_iff
import Submission.Work.SSGRoute.ArchDictionary.placeLocalFieldComplex
import Submission.Work.SSGRoute.ArchDictionary_aux.psiEMap_sub_betaRaw_mem_range
import Submission.Work.SSGRoute.E1aClean.ArchCompare
import Submission.Work.SSGRoute.ExtChain.exists_lift_of_extRes_comp_eq_zero
import Submission.Work.SSGRoute.PT.decompK_linked
import Submission.Work.SSGRoute.PT.freeCoverCompatKernel
import Submission.Work.SSGRoute.PTdualControl.archimedeanLocalPush
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.ArchDictionary

open CategoryTheory SSGRoute.PTExt
open scoped TensorProduct

set_option maxHeartbeats 8000000
set_option synthInstance.maxHeartbeats 4000000
set_option linter.unusedSectionVars false

noncomputable section

attribute [local instance 10000] Rep.hV2 Rep.hV1

/-! ## Elementary helpers -/

/-- In an abelian group, two `2`-torsion elements satisfy `a - b = b - a`. -/
theorem sub_eq_swap_of_two_nsmul_eq_zero {A : Type*} [AddCommGroup A] {a b : A}
    (ha : (2 : ℕ) • a = 0) (hb : (2 : ℕ) • b = 0) : a - b = b - a := by
  have hx : a - b = -(a - b) := by
    have h : (a - b) + (a - b) = 0 := by
      rw [← two_nsmul, smul_sub, ha, hb, sub_zero]
    exact eq_neg_of_add_eq_zero_left h
  rw [hx, neg_sub]

/-- **Lifting `2`-torsion `ℂˣ`-valued additive maps to `Ωˣ`.** -/
theorem exists_unitsLift_of_two_nsmul_eq_zero {V : Type*} [AddCommGroup V]
    (Ω : Type) [Field Ω] (φ : Ω →+* ℂ) (z : V →+ Additive ℂˣ)
    (hz : ∀ m : V, (2 : ℕ) • z m = 0) :
    ∃ z' : V →+ Additive Ωˣ, (∀ m : V, (2 : ℕ) • z' m = 0) ∧
      ∀ m : V, Units.map φ.toMonoidHom (Additive.toMul (z' m)) = Additive.toMul (z m) := by
  classical
  have hφinj : Function.Injective (Units.map φ.toMonoidHom) := by
    intro a b hab
    apply Units.ext
    exact RingHom.injective φ (congrArg (fun u : ℂˣ => (u : ℂ)) hab)
  have hz1 : ∀ m : V, Additive.toMul (z m) = 1 ∨ Additive.toMul (z m) = -1 := by
    intro m
    have h2 : ((Additive.toMul (z m) : ℂˣ) : ℂ) ^ 2 = 1 := by
      have h : (Additive.toMul (z m)) ^ 2 = 1 := by
        simpa [pow_two] using congrArg Additive.toMul (hz m)
      simpa [pow_two] using congrArg (fun u : ℂˣ => (u : ℂ)) h
    rcases sq_eq_one_iff.mp h2 with h | h
    · exact Or.inl (Units.ext h)
    · exact Or.inr (Units.ext h)
  have key : ∀ m : V, ∃ w : Ωˣ, (2 : ℕ) • (Additive.ofMul w) = (0 : Additive Ωˣ) ∧
      Units.map φ.toMonoidHom w = Additive.toMul (z m) := by
    intro m
    rcases hz1 m with h | h
    · refine ⟨1, ?_, ?_⟩
      · rw [two_nsmul]
        show Additive.ofMul ((1:Ωˣ) * 1) = (0 : Additive Ωˣ)
        rw [one_mul, ofMul_one]
      · rw [h]; simp
    · refine ⟨-1, ?_, ?_⟩
      · rw [two_nsmul]
        show Additive.ofMul ((-1:Ωˣ) * (-1)) = (0 : Additive Ωˣ)
        rw [neg_mul_neg, one_mul, ofMul_one]
      · rw [h]; simp
  have hz'2 : ∀ m : V, (2 : ℕ) • (Additive.ofMul (Classical.choose (key m))) = 0 :=
    fun m => (Classical.choose_spec (key m)).1
  have hfac : ∀ m : V, Units.map φ.toMonoidHom (Classical.choose (key m)) = Additive.toMul (z m) :=
    fun m => (Classical.choose_spec (key m)).2
  refine ⟨AddMonoidHom.mk' (fun m => Additive.ofMul (Classical.choose (key m))) ?_, hz'2, hfac⟩
  intro m n
  apply Additive.toMul.injective
  apply hφinj
  show Units.map φ.toMonoidHom (Additive.toMul (Additive.ofMul (Classical.choose (key (m+n)))))
      = Units.map φ.toMonoidHom (Additive.toMul (Additive.ofMul (Classical.choose (key m))
          + Additive.ofMul (Classical.choose (key n))))
  rw [toMul_ofMul, toMul_add, toMul_ofMul, toMul_ofMul, map_mul, hfac m, hfac n, hfac (m + n)]
  exact congrArg Additive.toMul (map_add z m n)

/-- **Factoring a `ℂˣ`-valued map through the canonical cover.** -/
theorem factor_coverMap_of_kappa_eq_zero {k : Type} [Field k] [CharZero k] {Ω : Type} [Field Ω]
    [Algebra k Ω] [IsAlgClosure k Ω] {K : IntermediateField k Ω}
    [FiniteDimensional k K] [IsGalois k K]
    (M : Rep.{0} SSGRoute.PTExt.Coeff (K ≃ₐ[k] K))
    (B : (Work.SSGRoute.ExtChain.E1cGeneric.E1cF (k := k) (Ω := Ω) (K := K) M).V →+ Additive ℂˣ)
    (hB : ∀ r : (Work.SSGRoute.ExtChain.E1cGeneric.E1cR1 (k := k) (Ω := Ω) (K := K) M).V,
      B (Work.SSGRoute.ExtChain.E1cGeneric.kappa (k := k) (Ω := Ω) (K := K) M r) = 0) :
    ∃ z : M.V →+ Additive ℂˣ,
      B = z.comp (Work.SSGRoute.ExtChain.E1cGeneric.coverMap (k := k) (Ω := Ω) (K := K) M) := by
  classical
  haveI : Fintype (K ≃ₐ[k] K) := inferInstance
  have hker : (Work.SSGRoute.ExtChain.E1cGeneric.coverMap (k := k) (Ω := Ω) (K := K) M).ker
      = (Work.SSGRoute.ExtChain.E1cGeneric.kappa (k := k) (Ω := Ω) (K := K) M).range := by
    simpa [Work.SSGRoute.ExtChain.E1cGeneric.coverMap, Work.SSGRoute.ExtChain.E1cGeneric.kappa,
      Rep.free] using
      (Work.SSGRoute.ker_hom_eq_range_kernel_iota (K := K) (Work.SSGRoute.freeCover M))
  have hle : (Work.SSGRoute.ExtChain.E1cGeneric.coverMap (k := k) (Ω := Ω) (K := K) M).ker
      ≤ B.ker := by
    intro x hx
    rw [hker] at hx
    obtain ⟨r, rfl⟩ := hx
    exact hB r
  refine ⟨(AddMonoidHom.liftOfSurjective
      (Work.SSGRoute.ExtChain.E1cGeneric.coverMap (k := k) (Ω := Ω) (K := K) M)
      (Work.SSGRoute.freeCover_surjective M)) ⟨B, hle⟩, ?_⟩
  apply AddMonoidHom.ext
  intro x
  exact (AddMonoidHom.liftOfRightInverse_comp_apply
    (Work.SSGRoute.ExtChain.E1cGeneric.coverMap (k := k) (Ω := Ω) (K := K) M)
    (Function.surjInv (Work.SSGRoute.freeCover_surjective M))
    (Function.rightInverse_surjInv (Work.SSGRoute.freeCover_surjective M)) ⟨B, hle⟩ x).symm

/-! ## The canonical conjugation actions, pinned as named definitions -/

section Actions

variable {k : Type} [Field k] [CharZero k] {Ω : Type} [Field Ω] [Algebra k Ω]
  [IsAlgClosure k Ω] {K : IntermediateField k Ω} [FiniteDimensional k K] [IsGalois k K]

/-- The canonical action on `E1cN M = Hom_ℤ(F_M,Ωˣ)`. -/
def actE1cN (M : Rep.{0} SSGRoute.PTExt.Coeff (K ≃ₐ[k] K)) :
    DistribMulAction (Ω ≃ₐ[k] Ω)
      (Work.SSGRoute.ExtChain.E1cGeneric.E1cN (k := k) (Ω := Ω) (K := K) M) :=
  Work.SSGRoute.homCoind.instDistribMulActionAlgEquiv (k := k) (Ω := Ω) (K := K)
    (Work.SSGRoute.ExtChain.E1cGeneric.E1cF (k := k) (Ω := Ω) (K := K) M)

/-- The canonical action on `homCoind M = Hom_ℤ(M.V,Ωˣ)`. -/
def actCoind (M : Rep.{0} SSGRoute.PTExt.Coeff (K ≃ₐ[k] K)) :
    DistribMulAction (Ω ≃ₐ[k] Ω) (Work.SSGRoute.homCoind k Ω K M) :=
  Work.SSGRoute.homCoind.instDistribMulActionAlgEquiv (k := k) (Ω := Ω) (K := K) M

theorem actE1cN_smul_apply (M : Rep.{0} SSGRoute.PTExt.Coeff (K ≃ₐ[k] K)) (σ : Ω ≃ₐ[k] Ω)
    (m : Work.SSGRoute.ExtChain.E1cGeneric.E1cN (k := k) (Ω := Ω) (K := K) M)
    (v : (Work.SSGRoute.ExtChain.E1cGeneric.E1cF (k := k) (Ω := Ω) (K := K) M).V) :
    (actE1cN (k := k) (Ω := Ω) (K := K) M).smul σ m v
      = σ • (m (((Work.SSGRoute.ExtChain.E1cGeneric.E1cF (k := k) (Ω := Ω) (K := K) M).ρ
          (SSGRoute.res k K σ)⁻¹) v)) :=
  Work.SSGRoute.homCoind.smul_apply σ m v

theorem actCoind_smul_apply (M : Rep.{0} SSGRoute.PTExt.Coeff (K ≃ₐ[k] K)) (σ : Ω ≃ₐ[k] Ω)
    (m : Work.SSGRoute.homCoind k Ω K M) (v : M.V) :
    (actCoind (k := k) (Ω := Ω) (K := K) M).smul σ m v
      = σ • (m ((M.ρ (SSGRoute.res k K σ)⁻¹) v)) :=
  Work.SSGRoute.homCoind.smul_apply σ m v

theorem actE1cN_smul_add (M : Rep.{0} SSGRoute.PTExt.Coeff (K ≃ₐ[k] K)) (σ : Ω ≃ₐ[k] Ω)
    (a b : Work.SSGRoute.ExtChain.E1cGeneric.E1cN (k := k) (Ω := Ω) (K := K) M) :
    (actE1cN (k := k) (Ω := Ω) (K := K) M).smul σ (a + b)
      = (actE1cN (k := k) (Ω := Ω) (K := K) M).smul σ a
        + (actE1cN (k := k) (Ω := Ω) (K := K) M).smul σ b := by
  apply AddMonoidHom.ext
  intro v
  rw [show ((actE1cN (k := k) (Ω := Ω) (K := K) M).smul σ a
        + (actE1cN (k := k) (Ω := Ω) (K := K) M).smul σ b) v
      = (actE1cN (k := k) (Ω := Ω) (K := K) M).smul σ a v
        + (actE1cN (k := k) (Ω := Ω) (K := K) M).smul σ b v from rfl]
  rw [actE1cN_smul_apply, actE1cN_smul_apply, actE1cN_smul_apply]
  rw [show (a + b) (((Work.SSGRoute.ExtChain.E1cGeneric.E1cF (k := k) (Ω := Ω) (K := K) M).ρ
        (SSGRoute.res k K σ)⁻¹) v)
      = a (((Work.SSGRoute.ExtChain.E1cGeneric.E1cF (k := k) (Ω := Ω) (K := K) M).ρ
            (SSGRoute.res k K σ)⁻¹) v)
        + b (((Work.SSGRoute.ExtChain.E1cGeneric.E1cF (k := k) (Ω := Ω) (K := K) M).ρ
            (SSGRoute.res k K σ)⁻¹) v) from rfl]
  rw [smul_add]

theorem actE1cN_smul_sub (M : Rep.{0} SSGRoute.PTExt.Coeff (K ≃ₐ[k] K)) (σ : Ω ≃ₐ[k] Ω)
    (a b : Work.SSGRoute.ExtChain.E1cGeneric.E1cN (k := k) (Ω := Ω) (K := K) M) :
    (actE1cN (k := k) (Ω := Ω) (K := K) M).smul σ (a - b)
      = (actE1cN (k := k) (Ω := Ω) (K := K) M).smul σ a
        - (actE1cN (k := k) (Ω := Ω) (K := K) M).smul σ b := by
  apply AddMonoidHom.ext
  intro v
  rw [show ((actE1cN (k := k) (Ω := Ω) (K := K) M).smul σ a
        - (actE1cN (k := k) (Ω := Ω) (K := K) M).smul σ b) v
      = (actE1cN (k := k) (Ω := Ω) (K := K) M).smul σ a v
        - (actE1cN (k := k) (Ω := Ω) (K := K) M).smul σ b v from rfl]
  rw [actE1cN_smul_apply, actE1cN_smul_apply, actE1cN_smul_apply]
  rw [show (a - b) (((Work.SSGRoute.ExtChain.E1cGeneric.E1cF (k := k) (Ω := Ω) (K := K) M).ρ
        (SSGRoute.res k K σ)⁻¹) v)
      = a (((Work.SSGRoute.ExtChain.E1cGeneric.E1cF (k := k) (Ω := Ω) (K := K) M).ρ
            (SSGRoute.res k K σ)⁻¹) v)
        - b (((Work.SSGRoute.ExtChain.E1cGeneric.E1cF (k := k) (Ω := Ω) (K := K) M).ρ
            (SSGRoute.res k K σ)⁻¹) v) from rfl]
  rw [smul_sub]

theorem actE1cN_iotaH (M : Rep.{0} SSGRoute.PTExt.Coeff (K ≃ₐ[k] K)) (σ : Ω ≃ₐ[k] Ω)
    (x : Work.SSGRoute.homCoind k Ω K M) :
    (actE1cN (k := k) (Ω := Ω) (K := K) M).smul σ
        (Work.SSGRoute.ExtChain.E1cGeneric.iotaH (k := k) (Ω := Ω) (K := K) M x)
      = Work.SSGRoute.ExtChain.E1cGeneric.iotaH (k := k) (Ω := Ω) (K := K) M
          ((actCoind (k := k) (Ω := Ω) (K := K) M).smul σ x) :=
  (Work.SSGRoute.ExtChain.E1cGeneric.iotaH_equivariant (k := k) (Ω := Ω) (K := K) M σ x).symm

end Actions

/-- **The complex-place spelling of the local action.** -/
theorem localActionConjOfLinkedComplex
    (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω]
    (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K] [NumberField ↥K]
    (c : Ω ≃ₐ[k] Ω) (hc2 : c ^ 2 = 1) (hc1 : c ≠ 1) (φ : Ω →+* ℂ)
    (hlink : ∀ x : Ω, φ (c x) = starRingEnd ℂ (φ x))
    (w : NK.GlobalCFT.Place ↥K)
    (hw : w = NK.GlobalCFT.Place.ofInfinite
      (NumberField.InfinitePlace.mk (φ.comp (algebraMap ↥K Ω))))
    (hne : SSGRoute.PTExt.decompK (k := k) w ≠ ⊥) :
    ∃ e : NK.GlobalCFT.Place.localField ↥K w ≃+* ℂ,
      (∀ x : (↥K)ˣ, e (Units.val (NK.HassePrinciple.unitsToLocalUnitsHom w x))
          = φ (algebraMap ↥K Ω (Units.val x))) ∧
      (∀ (γ : ↥(SSGRoute.PTExt.decompK (k := k) w))
         (u : (SSGRoute.PTExt.localUnitsK (k := k) w).V),
          (γ : ↥K ≃ₐ[k] ↥K) = SSGRoute.res k K c →
          e (Units.val (Additive.toMul ((SSGRoute.PTExt.localUnitsK (k := k) w).ρ γ u)))
            = starRingEnd ℂ (e (Units.val (Additive.toMul u)))) := by
  classical
  set ψ : ↥K →+* ℂ := φ.comp (algebraMap ↥K Ω) with hψ
  set v : NumberField.InfinitePlace ↥K := NumberField.InfinitePlace.mk ψ with hv
  have hwv : w = NK.GlobalCFT.Place.ofInfinite v := by rw [hw, hv]
  have hvC : v.IsComplex := by
    refine Work.SSGRoute.PTdualControl.isComplex_of_decompK_ofInfinite_ne_bot_aux
      (k := k) (K := K) v ?_
    rw [← hwv]; exact hne
  -- the level link
  have hconj : ∀ x : ↥K,
      v.embedding ((SSGRoute.res k K c) x) = starRingEnd ℂ (v.embedding x) := by
    intro x
    have hcx : ((SSGRoute.res k K c) x : Ω) = c (x : Ω) :=
      AlgEquiv.restrictNormalHom_apply K c x
    have hmain : ψ ((SSGRoute.res k K c) x) = starRingEnd ℂ (ψ x) := by
      rw [hψ]
      show φ ((algebraMap ↥K Ω) ((SSGRoute.res k K c) x))
        = starRingEnd ℂ (φ ((algebraMap ↥K Ω) x))
      rw [IntermediateField.algebraMap_apply, IntermediateField.algebraMap_apply, hcx, hlink]
    rcases hcase : NumberField.InfinitePlace.embedding_mk_eq ψ with h | h
    · rw [hv, h]; exact hmain
    · rw [hv, h]
      simp only [NumberField.ComplexEmbedding.conjugate_coe_eq]
      rw [hmain]
  -- the value formula of the completion iso on `K`
  have hcoe : ∀ x : ↥K,
      NumberField.InfinitePlace.Completion.extensionEmbedding v
        (algebraMap ↥K v.Completion x) = v.embedding x := by
    intro x
    simp [NumberField.InfinitePlace.Completion.algebraMap_apply,
      NumberField.InfinitePlace.Completion.extensionEmbedding_coe]
  have he₀ : ∀ x : ↥K,
      NumberField.InfinitePlace.Completion.ringEquivComplexOfIsComplex hvC
        (algebraMap ↥K v.Completion x) = v.embedding x := by
    intro x
    rw [NumberField.InfinitePlace.Completion.ringEquivComplexOfIsComplex_apply]
    exact hcoe x
  have hunit : ∀ x : (↥K)ˣ,
      NumberField.InfinitePlace.Completion.ringEquivComplexOfIsComplex hvC
        (Units.val (NK.HassePrinciple.unitsToLocalUnitsHom (NK.GlobalCFT.Place.ofInfinite v) x))
        = v.embedding (Units.val x) := by
    intro x
    show NumberField.InfinitePlace.Completion.ringEquivComplexOfIsComplex hvC
        (Units.val (Units.map (algebraMap ↥K v.Completion).toMonoidHom x)) = v.embedding ↑x
    rw [Units.coe_map]
    exact he₀ ↑x
  have hact : ∀ (γ : ↥(SSGRoute.PTExt.decompK (k := k) (NK.GlobalCFT.Place.ofInfinite v)))
      (u : (SSGRoute.PTExt.localUnitsK (k := k) (NK.GlobalCFT.Place.ofInfinite v)).V),
      (γ : ↥K ≃ₐ[k] ↥K) = SSGRoute.res k K c →
      NumberField.InfinitePlace.Completion.ringEquivComplexOfIsComplex hvC
          (Units.val (Additive.toMul ((SSGRoute.PTExt.localUnitsK (k := k)
            (NK.GlobalCFT.Place.ofInfinite v)).ρ γ u)))
        = starRingEnd ℂ (NumberField.InfinitePlace.Completion.ringEquivComplexOfIsComplex hvC
            (Units.val (Additive.toMul u))) := by
    intro γ u hγ
    have hlac : Work.SSGRoute.E1aClean.localActionC K v hvC γ = starRingEnd ℂ :=
      Work.SSGRoute.E1aClean.localActionC_eq_conj K v hvC γ (fun x => by rw [hγ]; exact hconj x)
    have h4 : ((SSGRoute.PTExt.localUnitsK (k := k) (NK.GlobalCFT.Place.ofInfinite v)).ρ γ u)
        = Additive.ofMul ((NK.HassePrinciple.localUnitsEquiv (K := k) (L := ↥K)
            (NK.GlobalCFT.Place.ofInfinite v) γ) (Additive.toMul u)) := rfl
    rw [h4, toMul_ofMul]
    change Units.val (Units.mapEquiv
        (NumberField.InfinitePlace.Completion.ringEquivComplexOfIsComplex hvC).toMulEquiv
        ((NK.HassePrinciple.localUnitsEquiv (K := k) (L := ↥K)
          (NK.GlobalCFT.Place.ofInfinite v) γ) (Additive.toMul u)))
      = starRingEnd ℂ (Units.val (Units.mapEquiv
        (NumberField.InfinitePlace.Completion.ringEquivComplexOfIsComplex hvC).toMulEquiv
        (Additive.toMul u)))
    rw [Work.SSGRoute.PTdualControl.localUnitsEquiv_transport (k := k) (K := K) v hvC γ
      (Additive.toMul u)]
    rw [Units.coe_map]
    exact RingHom.congr_fun hlac _
  have hAe : ∀ z : ℂ, Complex.conjAe.toRingEquiv z = starRingEnd ℂ z := fun z => rfl
  rw [hwv]
  rcases hcase : NumberField.InfinitePlace.embedding_mk_eq ψ with hA | hB
  · refine ⟨NumberField.InfinitePlace.Completion.ringEquivComplexOfIsComplex hvC, ?_, ?_⟩
    · intro x
      rw [hunit x, hA, hψ]
      rfl
    · intro γ u hγ
      exact hact γ u hγ
  · refine ⟨(NumberField.InfinitePlace.Completion.ringEquivComplexOfIsComplex hvC).trans
        Complex.conjAe, ?_, ?_⟩
    · intro x
      rw [RingEquiv.trans_apply, hunit x, hB, hψ]
      rw [NumberField.ComplexEmbedding.conjugate_coe_eq]
      simp only [hAe, starRingEnd_apply, star_star]
      rfl
    · intro γ u hγ
      rw [RingEquiv.trans_apply, RingEquiv.trans_apply]
      simp only [hAe]
      rw [hact γ u hγ]


/-! ## The main theorem -/

theorem archDictTwoCore (p : ℕ) [Fact p.Prime] (hp : p = 2) (k Ω : Type) [Field k] [NumberField k]
    [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω] (K : IntermediateField k Ω)
    [FiniteDimensional k K] [IsGalois k K] [NumberField ↥K] (ζ : Ω) (hζ : IsPrimitiveRoot ζ p)
    (hζK : ζ ∈ K)
    (T : Type) [AddCommGroup T] [Module (ZMod p) T] [DistribMulAction (K ≃ₐ[k] K) T]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) T]
    (hT : SSGRoute.IsCyclotomicDual p (T := T) (SSGRoute.res k K) ζ)
    (E : Type) [AddCommGroup E] [Module (ZMod p) E] [DistribMulAction (K ≃ₐ[k] K) E]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) E] [Finite E]
    [hMfinZ : Module.Finite ℤ ↑(Work.SSGRoute.ArchDictionary.Eprime p k Ω K T E)]
    (c : Ω ≃ₐ[k] Ω) (hc2 : c ^ 2 = 1) (hc1 : c ≠ 1)
    (w : NK.GlobalCFT.Place ↥K) (φ : Ω →+* ℂ)
    (hwinf : ∀ q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ↥K),
      w ≠ NK.GlobalCFT.Place.ofFinite q)
    (hw : w = NK.GlobalCFT.Place.ofInfinite
      (NumberField.InfinitePlace.mk (φ.comp (algebraMap ↥K Ω))))
    (hlink : ∀ x : Ω, φ (c x) = starRingEnd ℂ (φ x))
    (hne : SSGRoute.PTExt.decompK (k := k) w ≠ ⊥)
    (b : (Ω ≃ₐ[k] Ω) → E)
    (hb : SSGRoute.IsCocycleOn (SSGRoute.res k K) ⊤ b) (hl : SSGRoute.IsLocConstOn ⊤ b)
    (hγ : SSGRoute.PTExt.extLoc (k := k) w
      (SSGRoute.PTExt.extToIdeles (k := k)
        (Work.SSGRoute.E1aClean.globalDictionaryCanon p k Ω K ζ hζ hζK T hT E b)) = 0) :
    Work.SSGRoute.PT.H2Fin.resH1 (Subgroup.zpowers c)
      (Work.SSGRoute.homCoind k Ω K (Work.SSGRoute.ArchDictionary.Eprime p k Ω K T E))
      (Work.SSGRoute.ExtChain.E1cGeneric.e1cMap (k := k) (Ω := Ω) (K := K)
        (Work.SSGRoute.ArchDictionary.Eprime p k Ω K T E)
        (Work.SSGRoute.E1aClean.globalDictionaryCanon p k Ω K ζ hζ hζK T hT E b)) = 0 := by
  classical
  letI : DistribMulAction (Ω ≃ₐ[k] Ω) E := DistribMulAction.compHom E (SSGRoute.res k K)
  haveI hTfin : Finite T := Work.SSGRoute.ExtChain.e1aFiniteT p k Ω K ζ T hT
  let 𝓔 : Rep.{0} SSGRoute.PTExt.Coeff (K ≃ₐ[k] K) :=
    Work.SSGRoute.ArchDictionary.Eprime p k Ω K T E
  haveI h𝓔fin : Finite (𝓔 : Type) := by
    change Finite (Work.SSGRoute.DualMod p (TensorProduct (ZMod p) E T))
    exact Work.SSGRoute.PT.finite_dualMod_tensor p E T
  haveI h𝓔mod : Module.Finite ℤ ((𝓔 : Type)) := hMfinZ
  haveI h𝓔zp : Module (ZMod p) ((𝓔 : Type)) := by
    change Module (ZMod p) (Work.SSGRoute.DualMod p (TensorProduct (ZMod p) E T))
    infer_instance
  let 𝓕 : Rep.{0} SSGRoute.PTExt.Coeff (K ≃ₐ[k] K) :=
    Work.SSGRoute.ExtChain.E1cGeneric.E1cF (k := k) (Ω := Ω) (K := K) 𝓔
  let 𝓡 : Rep.{0} SSGRoute.PTExt.Coeff (K ≃ₐ[k] K) :=
    Work.SSGRoute.ExtChain.E1cGeneric.E1cR1 (k := k) (Ω := Ω) (K := K) 𝓔
  let zz : CategoryTheory.Abelian.Ext 𝓔 (SSGRoute.PTExt.unitsK k (↥K)) 1 :=
    Work.SSGRoute.E1aClean.globalDictionaryCanon p k Ω K ζ hζ hζK T hT E b
  have hzz : zz = Work.SSGRoute.E1aClean.globalDictionaryCanon p k Ω K ζ hζ hζK T hT E b := rfl
  let Φd := Work.SSGRoute.ExtChain.e1aCoeffNat p k Ω K ζ hζ hζK T hT E
  have hΦd : Work.GroupCohomology.IsEquivariant (Ω ≃ₐ[k] Ω) Φd.toAddMonoidHom :=
    fun σ e => Work.SSGRoute.ExtChain.e1aCoeffNat_equivariant p k Ω K ζ hζ hζK T hT E σ e
  have hΦd' : Work.GroupCohomology.IsEquivariant (Ω ≃ₐ[k] Ω) Φd.symm.toAddMonoidHom :=
    fun σ n => Work.SSGRoute.ExtChain.e1aCoeffNat_symm_equivariant p k Ω K ζ hζ hζK T hT E σ n
  have hbZ : b ∈ Work.AbsoluteKummer.Z1 (Ω ≃ₐ[k] Ω) E :=
    Work.SSGRoute.mem_absZ1_of_isCocycleOn_isLocConstOn (SSGRoute.res k K) hb hl
  let cfZ : ↥(Work.AbsoluteKummer.Z1 (Ω ≃ₐ[k] Ω) (Work.SSGRoute.homCoind k Ω K 𝓔)) :=
    Work.AbsoluteKummer.mapZ1 Φd.toAddMonoidHom hΦd ⟨b, hbZ⟩
  let cfFun : (Ω ≃ₐ[k] Ω) → Work.SSGRoute.homCoind k Ω K 𝓔 :=
    fun σ => (cfZ : (Ω ≃ₐ[k] Ω) → Work.SSGRoute.homCoind k Ω K 𝓔) σ
  have hcfFun_eq : ∀ σ : Ω ≃ₐ[k] Ω, cfFun σ = Φd (b σ) := by
    intro σ
    exact Work.AbsoluteKummer.mapZ1_apply Φd.toAddMonoidHom hΦd ⟨b, hbZ⟩ σ
  have hcls : Work.SSGRoute.ExtChain.E1cGeneric.e1cMap (k := k) (Ω := Ω) (K := K) 𝓔 zz
      = Work.AbsoluteKummer.H1π (Ω ≃ₐ[k] Ω) (Work.SSGRoute.homCoind k Ω K 𝓔) cfZ := by
    have h1 : zz = (Work.SSGRoute.ExtChain.E1cGeneric.e1cEquiv (k := k) (Ω := Ω) (K := K) 𝓔).symm
        ((Work.SSGRoute.H1Equiv.h1AddEquiv Φd hΦd hΦd')
          (Work.AbsoluteKummer.H1π (Ω ≃ₐ[k] Ω) E ⟨b, hbZ⟩)) := by
      rw [hzz]
      dsimp only [Work.SSGRoute.E1aClean.globalDictionaryCanon]
      rw [dif_pos hbZ]
      rfl
    have h2 : Work.SSGRoute.ExtChain.E1cGeneric.e1cMap (k := k) (Ω := Ω) (K := K) 𝓔
        ((Work.SSGRoute.ExtChain.E1cGeneric.e1cEquiv (k := k) (Ω := Ω) (K := K) 𝓔).symm
          ((Work.SSGRoute.H1Equiv.h1AddEquiv Φd hΦd hΦd')
            (Work.AbsoluteKummer.H1π (Ω ≃ₐ[k] Ω) E ⟨b, hbZ⟩)))
        = (Work.SSGRoute.H1Equiv.h1AddEquiv Φd hΦd hΦd')
            (Work.AbsoluteKummer.H1π (Ω ≃ₐ[k] Ω) E ⟨b, hbZ⟩) := by
      have h2' : (Work.SSGRoute.ExtChain.E1cGeneric.e1cEquiv (k := k) (Ω := Ω) (K := K) 𝓔)
          ((Work.SSGRoute.ExtChain.E1cGeneric.e1cEquiv (k := k) (Ω := Ω) (K := K) 𝓔).symm
            ((Work.SSGRoute.H1Equiv.h1AddEquiv Φd hΦd hΦd')
              (Work.AbsoluteKummer.H1π (Ω ≃ₐ[k] Ω) E ⟨b, hbZ⟩)))
          = (Work.SSGRoute.H1Equiv.h1AddEquiv Φd hΦd hΦd')
              (Work.AbsoluteKummer.H1π (Ω ≃ₐ[k] Ω) E ⟨b, hbZ⟩) :=
        AddEquiv.apply_symm_apply _ _
      exact h2'
    rw [h1, h2]
    rw [show ⇑(Work.SSGRoute.H1Equiv.h1AddEquiv Φd hΦd hΦd')
        = ⇑(Work.AbsoluteKummer.mapH1 Φd.toAddMonoidHom hΦd) from rfl]
    rw [Work.AbsoluteKummer.mapH1_H1π]
  obtain ⟨y, hy⟩ :=
    Work.SSGRoute.ExtChain.E1cGeneric.PhiE_surjective (k := k) (Ω := Ω) (K := K) 𝓔 zz
  have hloc : (SSGRoute.PTExt.extRes (SSGRoute.PTExt.decompK (k := k) w).subtype
        (Work.SSGRoute.ExtChain.E1cGeneric.PhiE (k := k) (Ω := Ω) (K := K) 𝓔 y)).comp
      (CategoryTheory.Abelian.Ext.mk₀ (NK.HassePrinciple.unitsToLocalUnits k (↥K) w))
      (add_zero 1) = 0 := by
    rw [← Work.SSGRoute.SSGStage.extLoc_extToIdeles_eq (k := k) (K := ↥K) (M := 𝓔) w
      (Work.SSGRoute.ExtChain.E1cGeneric.PhiE (k := k) (Ω := Ω) (K := K) 𝓔 y)]
    rw [hy]
    exact hγ
  obtain ⟨Ψ₁, hΨ₁⟩ := Work.SSGRoute.ExtChain.exists_lift_of_extRes_comp_eq_zero
    (k := k) (Ω := Ω) (K := K) 𝓔 (SSGRoute.PTExt.decompK (k := k) w)
    (SSGRoute.PTExt.localUnitsK (k := k) w) (NK.HassePrinciple.unitsToLocalUnits k (↥K) w) y hloc
  obtain ⟨e, he1, he2⟩ := localActionConjOfLinkedComplex k Ω K c hc2 hc1 φ hlink w hw hne
  have hdecomp : SSGRoute.PTExt.decompK (k := k) w
      = (Subgroup.zpowers c).map (SSGRoute.res k K) := by
    rw [hw]; exact Work.SSGRoute.PT.decompK_linked k Ω K c hc2 hc1 φ hlink
  have hmem : SSGRoute.res k K c ∈ SSGRoute.PTExt.decompK (k := k) w := by
    rw [hdecomp]
    exact Subgroup.mem_map_of_mem _ (Subgroup.mem_zpowers c)
  let γc : ↥(SSGRoute.PTExt.decompK (k := k) w) := ⟨SSGRoute.res k K c, hmem⟩
  have hγc : (γc : ↥K ≃ₐ[k] ↥K) = SSGRoute.res k K c := rfl
  have he1map : ∀ u : (↥K)ˣ,
      Units.map e.toMonoidHom ((NK.HassePrinciple.unitsToLocalUnitsHom w) u)
        = Units.map φ.toMonoidHom (Units.map (algebraMap ↥K Ω).toMonoidWithZeroHom u) := by
    intro u
    apply Units.ext
    rw [Units.coe_map, Units.coe_map, Units.coe_map]
    show e ↑((NK.HassePrinciple.unitsToLocalUnitsHom w) u) = φ ((algebraMap ↥K Ω) ↑u)
    exact he1 u
  -- the Γ-invariant element lifting `ΨE y` modulo the `betaRaw` class
  have hsub := Work.SSGRoute.ArchDictionary_aux.psiEMap_sub_betaRaw_mem_range
    (k := k) (Ω := Ω) (K := K) 𝓔 zz y hy cfZ hcls.symm
  obtain ⟨Φg, hΦg⟩ := AddMonoidHom.mem_range.mp hsub
  let w₀ : Work.SSGRoute.ExtChain.E1cGeneric.E1cN (k := k) (Ω := Ω) (K := K) 𝓔 :=
    Work.SSGRoute.ExtChain.E1cGeneric.liftOf (k := k) (Ω := Ω) (K := K) 𝓔 cfZ
  let A : Work.SSGRoute.ExtChain.E1cGeneric.E1cN (k := k) (Ω := Ω) (K := K) 𝓔 := w₀ + Φg.1
  have hpiΦg : (Work.SSGRoute.ExtChain.E1cGeneric.piH (k := k) (Ω := Ω) (K := K) 𝓔) Φg.1
      = (Work.SSGRoute.ExtChain.E1cGeneric.PsiEMap (k := k) (Ω := Ω) (K := K) 𝓡 y).1
        - (Work.SSGRoute.ExtChain.E1cGeneric.piH (k := k) (Ω := Ω) (K := K) 𝓔) w₀ := by
    have h := congrArg Subtype.val hΦg
    simpa [Work.SSGRoute.ExtChain.E1cGeneric.piH0, Work.GroupCohomology.mapH0,
      Work.SSGRoute.ExtChain.E1cGeneric.betaRaw, w₀] using h
  have hpiA : (Work.SSGRoute.ExtChain.E1cGeneric.piH (k := k) (Ω := Ω) (K := K) 𝓔) A
      = (Work.SSGRoute.ExtChain.E1cGeneric.PsiEMap (k := k) (Ω := Ω) (K := K) 𝓡 y).1 := by
    show (Work.SSGRoute.ExtChain.E1cGeneric.piH (k := k) (Ω := Ω) (K := K) 𝓔) (w₀ + Φg.1) = _
    rw [map_add, hpiΦg]
    abel
  -- the defect equations
  have hw₀d : (actE1cN (k := k) (Ω := Ω) (K := K) 𝓔).smul c w₀ - w₀
      = Work.SSGRoute.ExtChain.E1cGeneric.iotaH (k := k) (Ω := Ω) (K := K) 𝓔 (cfFun c) := by
    have h := Work.SSGRoute.ExtChain.E1cGeneric.liftOf_spec (k := k) (Ω := Ω) (K := K) 𝓔 cfZ
    change (Work.GroupCohomology.d0 (Ω ≃ₐ[k] Ω)
        (Work.SSGRoute.ExtChain.E1cGeneric.E1cN (k := k) (Ω := Ω) (K := K) 𝓔) w₀) c
      = Work.SSGRoute.ExtChain.E1cGeneric.iotaH (k := k) (Ω := Ω) (K := K) 𝓔 (cfFun c)
    rw [h, Work.AbsoluteKummer.mapZ1_apply]
  have hΦg_inv : (actE1cN (k := k) (Ω := Ω) (K := K) 𝓔).smul c Φg.1 = Φg.1 := by
    have h := (Work.GroupCohomology.mem_invariants (Ω ≃ₐ[k] Ω)
      (Work.SSGRoute.ExtChain.E1cGeneric.E1cN (k := k) (Ω := Ω) (K := K) 𝓔) Φg.1).mp Φg.2 c
    change (actE1cN (k := k) (Ω := Ω) (K := K) 𝓔).smul c Φg.1 = Φg.1 at h
    exact h
  have hAdef : (actE1cN (k := k) (Ω := Ω) (K := K) 𝓔).smul c A - A
      = Work.SSGRoute.ExtChain.E1cGeneric.iotaH (k := k) (Ω := Ω) (K := K) 𝓔 (cfFun c) := by
    show (actE1cN (k := k) (Ω := Ω) (K := K) 𝓔).smul c (w₀ + Φg.1) - (w₀ + Φg.1) = _
    rw [actE1cN_smul_add]
    rw [show (actE1cN (k := k) (Ω := Ω) (K := K) 𝓔).smul c w₀
          + (actE1cN (k := k) (Ω := Ω) (K := K) 𝓔).smul c Φg.1 - (w₀ + Φg.1)
        = ((actE1cN (k := k) (Ω := Ω) (K := K) 𝓔).smul c w₀ - w₀)
          + ((actE1cN (k := k) (Ω := Ω) (K := K) 𝓔).smul c Φg.1 - Φg.1) from by abel]
    rw [hw₀d, hΦg_inv, sub_self, add_zero]
  -- the pointwise defect for `A`
  have hA : ∀ v : 𝓕.V, A (𝓕.ρ (SSGRoute.res k K c) v)
      = c • (A v) - (Work.SSGRoute.ExtChain.E1cGeneric.iotaH (k := k) (Ω := Ω) (K := K) 𝓔)
          (cfFun c) (𝓕.ρ (SSGRoute.res k K c) v) := by
    intro v
    have h := congrArg (fun f : Work.SSGRoute.ExtChain.E1cGeneric.E1cN (k := k) (Ω := Ω) (K := K) 𝓔 =>
      f (𝓕.ρ (SSGRoute.res k K c) v)) hAdef
    rw [show ((actE1cN (k := k) (Ω := Ω) (K := K) 𝓔).smul c A - A)
          (𝓕.ρ (SSGRoute.res k K c) v)
        = (actE1cN (k := k) (Ω := Ω) (K := K) 𝓔).smul c A (𝓕.ρ (SSGRoute.res k K c) v)
          - A (𝓕.ρ (SSGRoute.res k K c) v) from rfl] at h
    rw [actE1cN_smul_apply] at h
    rw [show 𝓕.ρ (SSGRoute.res k K c)⁻¹ (𝓕.ρ (SSGRoute.res k K c) v) = v from by
      rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]] at h
    rw [eq_sub_iff_add_eq, ← h]
    abel
  -- the `ℂˣ`-valued side
  let phiStar : Additive Ωˣ →+ Additive ℂˣ := (Units.map φ.toMonoidHom).toAdditive
  let conjAdd : Additive ℂˣ →+ Additive ℂˣ := (Units.map (starRingEnd ℂ).toMonoidHom).toAdditive
  let Ψ₁' : 𝓕.V →+ Additive ℂˣ :=
    (Units.map e.toMonoidHom).toAdditive.comp
      ((Rep.Hom.hom Ψ₁).toLinearMap.toAddMonoidHom)
  let A' : 𝓕.V →+ Additive ℂˣ := phiStar.comp A
  let B : 𝓕.V →+ Additive ℂˣ := Ψ₁' - A'
  have hΨ₁'_apply : ∀ v : 𝓕.V, Ψ₁' v
      = Additive.ofMul (Units.map e.toMonoidHom (Additive.toMul (Rep.Hom.hom Ψ₁ v))) :=
    fun v => rfl
  have hφUnits_inj : Function.Injective (Units.map φ.toMonoidHom) := by
    intro a b hab
    apply Units.ext
    exact RingHom.injective φ (congrArg (fun u : ℂˣ => (u : ℂ)) hab)
  have hphiStar_inj : Function.Injective phiStar := by
    intro a b hab
    have h := congrArg Additive.toMul hab
    rw [show phiStar a = Additive.ofMul (Units.map φ.toMonoidHom (Additive.toMul a)) from rfl,
      show phiStar b = Additive.ofMul (Units.map φ.toMonoidHom (Additive.toMul b)) from rfl,
      toMul_ofMul, toMul_ofMul] at h
    exact congrArg Additive.ofMul (hφUnits_inj h)
  -- the κ-compatibility of `Ψ₁'`
  have hΨ₁E : ∀ r : 𝓡.V,
      Rep.Hom.hom Ψ₁ (Work.SSGRoute.ExtChain.E1cGeneric.kappa (k := k) (Ω := Ω) (K := K) 𝓔 r)
        = Rep.Hom.hom (NK.HassePrinciple.unitsToLocalUnits k (↥K) w)
            (Rep.Hom.hom (CategoryTheory.Abelian.Ext.addEquiv₀ y) r) :=
    fun r => hΨ₁ r
  have hΨ₁'κ : ∀ r : 𝓡.V, Ψ₁' (Work.SSGRoute.ExtChain.E1cGeneric.kappa (k := k) (Ω := Ω) (K := K) 𝓔 r)
      = Additive.ofMul (Units.map φ.toMonoidHom (Units.map (algebraMap ↥K Ω).toMonoidWithZeroHom
          (Additive.toMul (Rep.Hom.hom (CategoryTheory.Abelian.Ext.addEquiv₀ y) r)))) := by
    intro r
    rw [hΨ₁'_apply, hΨ₁E r]
    rw [show Rep.Hom.hom (NK.HassePrinciple.unitsToLocalUnits k (↥K) w)
          (Rep.Hom.hom (CategoryTheory.Abelian.Ext.addEquiv₀ y) r)
        = Additive.ofMul ((NK.HassePrinciple.unitsToLocalUnitsHom w)
            (Additive.toMul (Rep.Hom.hom (CategoryTheory.Abelian.Ext.addEquiv₀ y) r))) from rfl]
    rw [toMul_ofMul]
    congr 1
    exact he1map _
  have hA'κ : ∀ r : 𝓡.V, A' (Work.SSGRoute.ExtChain.E1cGeneric.kappa (k := k) (Ω := Ω) (K := K) 𝓔 r)
      = Additive.ofMul (Units.map φ.toMonoidHom (Units.map (algebraMap ↥K Ω).toMonoidWithZeroHom
          (Additive.toMul (Rep.Hom.hom (CategoryTheory.Abelian.Ext.addEquiv₀ y) r)))) := by
    intro r
    show phiStar (A (Work.SSGRoute.ExtChain.E1cGeneric.kappa (k := k) (Ω := Ω) (K := K) 𝓔 r)) = _
    have hAκ : A (Work.SSGRoute.ExtChain.E1cGeneric.kappa (k := k) (Ω := Ω) (K := K) 𝓔 r)
        = Additive.ofMul (Units.map (algebraMap ↥K Ω).toMonoidWithZeroHom
            (Additive.toMul (Rep.Hom.hom (CategoryTheory.Abelian.Ext.addEquiv₀ y) r))) := by
      have h := congrArg (fun f : Work.SSGRoute.homCoind k Ω K 𝓡 => f r) hpiA
      rw [show (Work.SSGRoute.ExtChain.E1cGeneric.piH (k := k) (Ω := Ω) (K := K) 𝓔) A
          = A.comp (Work.SSGRoute.ExtChain.E1cGeneric.kappa (k := k) (Ω := Ω) (K := K) 𝓔) from rfl,
        AddMonoidHom.comp_apply] at h
      rw [h]
      have hp : ((Work.SSGRoute.ExtChain.E1cGeneric.PsiEMap (k := k) (Ω := Ω) (K := K) 𝓡 y).1)
          = (Work.SSGRoute.toCoindH0 (k := k) (Ω := Ω) (K := K) 𝓡
              (CategoryTheory.Abelian.Ext.addEquiv₀ y)).1 :=
        congrArg Subtype.val
          (Work.SSGRoute.ExtChain.E1cGeneric.PsiEMap_apply_toCoindH0 (k := k) (Ω := Ω) (K := K) 𝓡 y)
      rw [hp]
      exact Work.SSGRoute.toCoindH0_apply (k := k) (Ω := Ω) (K := K) 𝓡
        (CategoryTheory.Abelian.Ext.addEquiv₀ y) r
    rw [hAκ]
    rfl
  have hBκ : ∀ r : 𝓡.V, B (Work.SSGRoute.ExtChain.E1cGeneric.kappa (k := k) (Ω := Ω) (K := K) 𝓔 r) = 0 := by
    intro r
    show Ψ₁' (Work.SSGRoute.ExtChain.E1cGeneric.kappa (k := k) (Ω := Ω) (K := K) 𝓔 r)
      - A' (Work.SSGRoute.ExtChain.E1cGeneric.kappa (k := k) (Ω := Ω) (K := K) 𝓔 r) = 0
    rw [hΨ₁'κ r, hA'κ r, sub_self]
  obtain ⟨z₀, hz₀⟩ := factor_coverMap_of_kappa_eq_zero (k := k) (Ω := Ω) (K := K) 𝓔 B hBκ
  let cm : 𝓕.V →+ 𝓔.V :=
    Work.SSGRoute.ExtChain.E1cGeneric.coverMap (k := k) (Ω := Ω) (K := K) 𝓔
  have hcm_comm : ∀ v : 𝓕.V, cm (𝓕.ρ (SSGRoute.res k K c) v)
      = 𝓔.ρ (SSGRoute.res k K c) (cm v) :=
    fun v => Work.SSGRoute.ExtChain.E1cGeneric.coverMap_comm (k := k) (Ω := Ω) (K := K) 𝓔
      (SSGRoute.res k K c) v
  have hz₀_apply : ∀ v : 𝓕.V, B v = z₀ (cm v) := by
    intro v
    rw [hz₀]
    rfl
  -- `z₀` takes `2`-torsion values
  have hm_two : ∀ m : 𝓔.V, (2 : ℕ) • m = 0 := by
    intro m
    change (2 : ℕ) • (m : Work.SSGRoute.DualMod p (TensorProduct (ZMod p) E T)) = 0
    rw [← hp, ← Nat.cast_smul_eq_nsmul (ZMod p) p m, ZMod.natCast_self, zero_smul]
  have hz₀_two : ∀ m : 𝓔.V, (2 : ℕ) • z₀ m = 0 := by
    intro m
    rw [← map_nsmul z₀ 2 m, hm_two m, map_zero]
  have hconjAdd_two : ∀ y : Additive ℂˣ, (2 : ℕ) • y = 0 → conjAdd y = y := by
    intro y hy
    show Additive.ofMul (Units.map (starRingEnd ℂ).toMonoidHom (Additive.toMul y)) = y
    apply Additive.toMul.injective
    rw [toMul_ofMul]
    have h2 : ((Additive.toMul y : ℂˣ) : ℂ) ^ 2 = 1 := by
      have h1 : (Additive.toMul y) ^ 2 = 1 := by simpa [pow_two] using congrArg Additive.toMul hy
      simpa [pow_two] using congrArg (fun u : ℂˣ => (u : ℂ)) h1
    rcases sq_eq_one_iff.mp h2 with h | h
    · rw [show Additive.toMul y = 1 from Units.ext h]
      congr 1
      apply Units.ext
      simp
    · rw [show Additive.toMul y = -1 from Units.ext h]
      congr 1
      apply Units.ext
      simp
  -- the `c`-equivariance of `Ψ₁'`
  have hΨ₁'_c : ∀ v : 𝓕.V, Ψ₁' (𝓕.ρ (SSGRoute.res k K c) v) = conjAdd (Ψ₁' v) := by
    intro v
    have hcom : Rep.Hom.hom Ψ₁ (𝓕.ρ (SSGRoute.res k K c) v)
        = (SSGRoute.PTExt.localUnitsK (k := k) w).ρ γc (Rep.Hom.hom Ψ₁ v) :=
      Rep.hom_comm_apply Ψ₁ γc v
    rw [hΨ₁'_apply, hΨ₁'_apply, hcom]
    show Additive.ofMul (Units.map e.toMonoidHom (Additive.toMul
        ((SSGRoute.PTExt.localUnitsK (k := k) w).ρ γc (Rep.Hom.hom Ψ₁ v))))
      = Additive.ofMul (Units.map (starRingEnd ℂ).toMonoidHom
          (Units.map e.toMonoidHom (Additive.toMul (Rep.Hom.hom Ψ₁ v))))
    congr 1
    apply Units.ext
    rw [Units.coe_map, Units.coe_map, Units.coe_map]
    exact he2 γc (Rep.Hom.hom Ψ₁ v) hγc
  have hphiStar_conj : ∀ x : Additive Ωˣ, phiStar (c • x) = conjAdd (phiStar x) := by
    intro x
    show Additive.ofMul (Units.map φ.toMonoidHom (Additive.toMul (c • x)))
      = Additive.ofMul (Units.map (starRingEnd ℂ).toMonoidHom
          (Units.map φ.toMonoidHom (Additive.toMul x)))
    congr 1
    apply Units.ext
    rw [Units.coe_map, Units.coe_map, Units.coe_map,
      Work.SSGRoute.addUnits_smul_toMulΩ]
    rw [Work.SSGRoute.algEquivUnitsMapΩ_coe]
    exact hlink ((Additive.toMul x : Ωˣ) : Ω)
  have hA'_c : ∀ v : 𝓕.V, A' (𝓕.ρ (SSGRoute.res k K c) v)
      = conjAdd (A' v) - phiStar ((Work.SSGRoute.ExtChain.E1cGeneric.iotaH (k := k) (Ω := Ω) (K := K) 𝓔)
          (cfFun c) (𝓕.ρ (SSGRoute.res k K c) v)) := by
    intro v
    show phiStar (A (𝓕.ρ (SSGRoute.res k K c) v)) = conjAdd (A' v) - phiStar _
    rw [hA v, map_sub, hphiStar_conj]
    rfl
  have hBdef : ∀ v : 𝓕.V, B (𝓕.ρ (SSGRoute.res k K c) v)
      = conjAdd (B v) + (phiStar.comp (cfFun c)) (𝓔.ρ (SSGRoute.res k K c) (cm v)) := by
    intro v
    show Ψ₁' (𝓕.ρ (SSGRoute.res k K c) v) - A' (𝓕.ρ (SSGRoute.res k K c) v)
      = conjAdd (B v) + (phiStar.comp (cfFun c)) (𝓔.ρ (SSGRoute.res k K c) (cm v))
    rw [hΨ₁'_c v, hA'_c v, show B v = Ψ₁' v - A' v from rfl, map_sub]
    rw [show (Work.SSGRoute.ExtChain.E1cGeneric.iotaH (k := k) (Ω := Ω) (K := K) 𝓔) (cfFun c)
          (𝓕.ρ (SSGRoute.res k K c) v) = (cfFun c) (cm (𝓕.ρ (SSGRoute.res k K c) v)) from rfl]
    rw [hcm_comm]
    abel
  have hcfℂ : ∀ m : 𝓔.V, (phiStar.comp (cfFun c)) (𝓔.ρ (SSGRoute.res k K c) m)
      = z₀ (𝓔.ρ (SSGRoute.res k K c) m) - z₀ m := by
    intro m
    obtain ⟨v, hv⟩ := Work.SSGRoute.freeCover_surjective 𝓔 m
    have hv' : cm v = m := hv
    have h := hBdef v
    rw [hz₀_apply (𝓕.ρ (SSGRoute.res k K c) v), hz₀_apply v, hcm_comm v,
      show conjAdd (z₀ (cm v)) = z₀ (cm v) from hconjAdd_two _ (hz₀_two _)] at h
    have h2 : (phiStar.comp (cfFun c)) (𝓔.ρ (SSGRoute.res k K c) (cm v))
        = z₀ (𝓔.ρ (SSGRoute.res k K c) (cm v)) - z₀ (cm v) := by
      rw [h]
      abel
    rw [hv'] at h2
    exact h2
  -- the `Ωˣ`-valued lift of `z₀`
  obtain ⟨z₀', hz₀'tor, hz₀'φ⟩ := exists_unitsLift_of_two_nsmul_eq_zero Ω φ z₀ hz₀_two
  have hphiStar_z : ∀ m : 𝓔.V, phiStar (z₀' m) = z₀ m :=
    fun m => congrArg Additive.ofMul (hz₀'φ m)
  have hcfΩ : ∀ m : 𝓔.V, (cfFun c) (𝓔.ρ (SSGRoute.res k K c) m)
      = z₀' (𝓔.ρ (SSGRoute.res k K c) m) - z₀' m := by
    intro m
    apply hphiStar_inj
    rw [map_sub, hphiStar_z, hphiStar_z]
    exact hcfℂ m
  have hcn₂ : (actCoind (k := k) (Ω := Ω) (K := K) 𝓔).smul c z₀' - z₀' = cfFun c := by
    apply AddMonoidHom.ext
    intro m
    show (actCoind (k := k) (Ω := Ω) (K := K) 𝓔).smul c z₀' m - z₀' m = cfFun c m
    rw [actCoind_smul_apply]
    rw [show c • (z₀' (𝓔.ρ (SSGRoute.res k K c)⁻¹ m)) = z₀' (𝓔.ρ (SSGRoute.res k K c)⁻¹ m) from
      Work.SSGRoute.ArchDictionary.smul_addUnits_eq_self_of_two_nsmul_eq_zero k Ω c _
        (hz₀'tor _)]
    have h2 : cfFun c m = z₀' m - z₀' (𝓔.ρ (SSGRoute.res k K c)⁻¹ m) := by
      have h := hcfΩ (𝓔.ρ (SSGRoute.res k K c)⁻¹ m)
      rwa [show 𝓔.ρ (SSGRoute.res k K c) (𝓔.ρ ((SSGRoute.res k K c)⁻¹) m) = m from by
        rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]] at h
    rw [h2]
    exact sub_eq_swap_of_two_nsmul_eq_zero (hz₀'tor _) (hz₀'tor _)
  -- the `⟨c⟩`-invariant lift
  have hiota_sub : (actE1cN (k := k) (Ω := Ω) (K := K) 𝓔).smul c
        (A - (Work.SSGRoute.ExtChain.E1cGeneric.iotaH (k := k) (Ω := Ω) (K := K) 𝓔) z₀')
      = A - (Work.SSGRoute.ExtChain.E1cGeneric.iotaH (k := k) (Ω := Ω) (K := K) 𝓔) z₀' := by
    have hX : (actE1cN (k := k) (Ω := Ω) (K := K) 𝓔).smul c A
        = A + (Work.SSGRoute.ExtChain.E1cGeneric.iotaH (k := k) (Ω := Ω) (K := K) 𝓔) (cfFun c) := by
      rw [← hAdef]; abel
    have hY : (actE1cN (k := k) (Ω := Ω) (K := K) 𝓔).smul c
          ((Work.SSGRoute.ExtChain.E1cGeneric.iotaH (k := k) (Ω := Ω) (K := K) 𝓔) z₀')
        = (Work.SSGRoute.ExtChain.E1cGeneric.iotaH (k := k) (Ω := Ω) (K := K) 𝓔)
            (cfFun c + z₀') := by
      rw [actE1cN_iotaH]
      congr 1
      rw [← hcn₂]; abel
    rw [actE1cN_smul_sub, hX, hY, map_add]
    abel
  have hΦmem : (A - (Work.SSGRoute.ExtChain.E1cGeneric.iotaH (k := k) (Ω := Ω) (K := K) 𝓔) z₀')
      ∈ Work.AbsoluteKummer.H0 (Subgroup.zpowers c)
          (Work.SSGRoute.ExtChain.E1cGeneric.E1cN (k := k) (Ω := Ω) (K := K) 𝓔) := by
    rw [Work.GroupCohomology.mem_invariants]
    intro g
    rw [Subgroup.smul_def]
    rcases Work.SSGRoute.PTdualControl.zpowers_involution_eq c hc2 g.2 with h1 | hc
    · rw [h1, one_smul]
    · rw [hc]
      change (actE1cN (k := k) (Ω := Ω) (K := K) 𝓔).smul c
          (A - (Work.SSGRoute.ExtChain.E1cGeneric.iotaH (k := k) (Ω := Ω) (K := K) 𝓔) z₀')
        = A - (Work.SSGRoute.ExtChain.E1cGeneric.iotaH (k := k) (Ω := Ω) (K := K) 𝓔) z₀'
      exact hiota_sub
  have hΦpi : (Work.SSGRoute.ExtChain.E1cGeneric.piH (k := k) (Ω := Ω) (K := K) 𝓔)
        (A - (Work.SSGRoute.ExtChain.E1cGeneric.iotaH (k := k) (Ω := Ω) (K := K) 𝓔) z₀')
      = (Work.SSGRoute.ExtChain.E1cGeneric.PsiEMap (k := k) (Ω := Ω) (K := K) 𝓡 y).1 := by
    rw [map_sub, hpiA, Work.SSGRoute.ExtChain.E1cGeneric.piH_iotaH, sub_zero]
  rw [← hzz, ← hy]
  exact Work.SSGRoute.ExtChain.resH1_e1cMap_eq_zero_of_extension (k := k) (Ω := Ω) (K := K) 𝓔 y
    (Subgroup.zpowers c)
    (A - (Work.SSGRoute.ExtChain.E1cGeneric.iotaH (k := k) (Ω := Ω) (K := K) 𝓔) z₀')
    hΦmem hΦpi

end

end Work.ArchDictionary
