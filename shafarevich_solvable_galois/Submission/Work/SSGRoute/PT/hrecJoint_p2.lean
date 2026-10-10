import Mathlib.FieldTheory.KrullTopology
import Mathlib.RingTheory.Henselian
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.RepresentationTheory.Rep.Res
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.Valuation.ValuationSubring
import Mathlib.NumberTheory.NumberField.InfinitePlace.Ramification
import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
import Mathlib.Algebra.Homology.DerivedCategory.Ext.Basic
import Submission.Work.PT.hrecArchFamily_seamValue
import Submission.Work.PT.seamPlace_orbit_theory
import Submission.Work.SSGRoute.E9Nodes.e9_unramified_all_but_finite
import Submission.Work.SSGRoute.PT.G1plusOwn.clause7Core
import Submission.Work.SSGRoute.PT.G1plusOwn.g1FinHalf_reciprocity_v2
import Submission.Work.SSGRoute.PT.G1plusOwn.g1FinHalf_unramified
import Submission.Work.SSGRoute.PT.archPairLocal_hpairArch
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGRoute.PT

open scoped TensorProduct
open CategoryTheory

set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option maxHeartbeats 40000000
set_option synthInstance.maxHeartbeats 8000000
set_option backward.isDefEq.respectTransparency false

/-! Clause (7) of the hub at `p = 2`: the body of the `p = 2` branch of
`Work.SSGRoute.PT.hrecJoint_archFamily`, extracted here so that it can be proved and filed
independently. -/

theorem hrecJoint_archFamily_p2
    (p : ℕ) [Fact p.Prime] (hp2 : p = 2) (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
    [IsAlgClosure k Ω] (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    (ζ : Ω) (hζ : IsPrimitiveRoot ζ p) (hζK : ζ ∈ K)
    (T : Type) [AddCommGroup T] [Module (ZMod p) T] [DistribMulAction (K ≃ₐ[k] K) T]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) T] [Finite T]
    (hT : SSGRoute.IsCyclotomicDual p (T := T) (SSGRoute.res k K) ζ)
    (χ : G1pOwn.ChiK p k Ω K T)
    (hχadd : ∀ (L : IntermediateField k Ω) [NumberField L] [FiniteDimensional k L]
      [IsGalois k L] (hKL : K ≤ L) (u v : SSGRoute.PTExt.extH (SSGRoute.PTExt.classesK k L) 2),
      p • u = 0 → p • v = 0 → χ L hKL (u + v) = χ L hKL u + χ L hKL v)
    (hχcompat : ∀ (L : IntermediateField k Ω) [NumberField L] [FiniteDimensional k L]
      [IsGalois k L] (hKL : K ≤ L) (L' : IntermediateField k Ω) [NumberField L']
      [FiniteDimensional k L'] [IsGalois k L'] (hKL' : K ≤ L') (hLL : L ≤ L')
      (u : SSGRoute.PTExt.extH (SSGRoute.PTExt.classesK k L) 2),
      p • u = 0 → χ L' hKL' (Work.SSGRoute.PT.inflLevel L L' hLL u) = χ L hKL u)
    (φc : (c : Ω ≃ₐ[k] Ω) → c ^ 2 = 1 → c ≠ 1 → Ω →+* ℂ)
    (hφc : ∀ (c : Ω ≃ₐ[k] Ω) (hc2 : c ^ 2 = 1) (hc1 : c ≠ 1) (x : Ω),
      φc c hc2 hc1 (c x) = starRingEnd ℂ (φc c hc2 hc1 x))
    (M : Type) [AddCommGroup M] [Module (ZMod p) M] [DistribMulAction (K ≃ₐ[k] K) M]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M] [Finite M]
    (a : (Ω ≃ₐ[k] Ω) → M) (b : (Ω ≃ₐ[k] Ω) → Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T)) :
    SSGRoute.IsCocycleOn (SSGRoute.res k K) ⊤ a → SSGRoute.IsLocConstOn ⊤ a →
    SSGRoute.IsCocycleOn (SSGRoute.res k K) ⊤ b → SSGRoute.IsLocConstOn ⊤ b →
    ∀ (S' : Finset (ValuationSubring Ω)), (∀ A ∈ S', SSGRoute.IsFinPlace k A) →
    (∀ A ∈ S', ∀ B ∈ S', SSGRoute.IsConjPlace k A B → A = B) →
    (∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
      (∀ A ∈ S', ¬ SSGRoute.IsConjPlace k A B) →
      ¬ B.valuation (p : Ω) < 1 ∧ ¬ SSGRoute.IsRamifiedIn k K B ∧
        ∀ σ : Ω ≃ₐ[k] Ω, SSGRoute.IsInertia k B σ → a σ = 0 ∧ b σ = 0) →
    ∀ (C' : Finset (Ω ≃ₐ[k] Ω)), (∀ c ∈ C', c ^ 2 = 1) →
    (∀ c : Ω ≃ₐ[k] Ω, c ^ 2 = 1 → c ≠ 1 → ∃ c₀ ∈ C', ∃ σ : Ω ≃ₐ[k] Ω, c = σ * c₀ * σ⁻¹) →
    (∀ c ∈ C', ∀ c' ∈ C', (∃ σ : Ω ≃ₐ[k] Ω, c' = σ * c * σ⁻¹) → c = c') →
    ∑ A ∈ S', G1pOwn.g1FinHalf p k Ω K ζ hζ hζK T hT χ M (SSGRoute.decomp k A) a b +
      ∑ c ∈ C', archFamily p k Ω K ζ hζ hζK T hT χ φc hφc M (Subgroup.zpowers c) a b = 0 := by
  classical
  intro ha1 ha2 hb1 hb2 S' hS'fin hS'disj hgood C' hC'inv hC'rep hC'disj
-- ## the joint statement, by the class formation at one level (see the route above).
  haveI hKnum : NumberField ↥K := NumberField.of_module_finite k ↥K
  -- ### the common level `L`: `b` factors through it and it is unramified outside the classes
  -- of `S'`
  obtain ⟨L, hLfin, hLnorm, hKL, ⟨b₀, hb₀⟩, hInertia⟩ :=
    G1plusOwn.exists_level_factors_unramified_v2 (p := p) (K := K)
      (M := Work.SSGRoute.PT.VFcoef p M T) b hb1 hb2 S' hS'fin
      (fun B hB hBnot =>
        ⟨(hgood B hB hBnot).2.1, fun σ hσ => ((hgood B hB hBnot).2.2 σ hσ).2⟩)
  haveI : FiniteDimensional k L := hLfin
  haveI : Normal k L := hLnorm
  haveI hLnum : NumberField ↥L := NumberField.of_module_finite k ↥L
  haveI hLgal : IsGalois k ↥L :=
    isGalois_iff.mpr ⟨Algebra.IsSeparable.of_integral k ↥L, hLnorm⟩
  letI : Algebra ↥K ↥L := (IntermediateField.inclusion hKL).toAlgebra
  haveI : IsScalarTower k ↥K ↥L := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  haveI : IsScalarTower ↥K ↥L Ω := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  -- ### the crossed-homomorphism property and the global level class
  have hψ : ∀ g hh : ↥L ≃ₐ[k] ↥L,
      b₀ (g * hh) = SSGRoute.PTExt.galRes k (↥K) (↥L) g • b₀ hh + b₀ g :=
    G1plusOwn.crossedHom_of_factorises p k Ω K T M b hb1 b₀ hb₀
  set h_L : SSGRoute.PTExt.extH (Rep.res (SSGRoute.PTExt.galRes k (↥K) (↥L))
      (SSGRoute.PTExt.modRep (↥K ≃ₐ[k] ↥K) (Work.SSGRoute.PT.VFcoef p M T))) 1 :=
    Work.SSGRoute.PT.levelClassOf p k Ω K T M L b₀ hψ with hh_L
  -- ### the global idèle class and its restriction to `L`
  set Z : CategoryTheory.Abelian.Ext
      (SSGRoute.PTExt.modRep (↥K ≃ₐ[k] ↥K) (Work.SSGRoute.PT.VFcoef p M T))
      (SSGRoute.PTExt.idelesK k ↥K) 1 :=
    SSGRoute.PTExt.extToIdeles (k := k) (finZBg p K ζ hζ hζK T hT M a) with hh_Z
  set Z' : CategoryTheory.Abelian.Ext
      (Rep.res (SSGRoute.PTExt.galRes k (↥K) (↥L))
        (SSGRoute.PTExt.modRep (↥K ≃ₐ[k] ↥K) (Work.SSGRoute.PT.VFcoef p M T)))
      (SSGRoute.PTExt.idelesK k ↥L) 1 :=
    (SSGRoute.PTExt.extRes (SSGRoute.PTExt.galRes k (↥K) (↥L)) Z).comp
      (CategoryTheory.Abelian.Ext.mk₀ (Work.SSGRoute.idleRepMap k (↥K) (↥L))) (add_zero 1)
    with hh_Z'
  -- ### `extToClasses Z' = 0`
  have hZgen : ∀ {M0 : Rep.{0} SSGRoute.PTExt.Coeff (↥K ≃ₐ[k] ↥K)}
      (x : CategoryTheory.Abelian.Ext M0 (SSGRoute.PTExt.idelesK k ↥K) 1),
      SSGRoute.PTExt.extToClasses (k := k) (K := ↥L)
          ((SSGRoute.PTExt.extRes (SSGRoute.PTExt.galRes k (↥K) (↥L)) x).comp
            (CategoryTheory.Abelian.Ext.mk₀ (Work.SSGRoute.idleRepMap k (↥K) (↥L)))
            (add_zero 1))
        = (SSGRoute.PTExt.extRes (SSGRoute.PTExt.galRes k (↥K) (↥L))
              (SSGRoute.PTExt.extToClasses (k := k) (K := ↥K) x)).comp
            (CategoryTheory.Abelian.Ext.mk₀ (SSGRoute.PTExt.classIncl k (↥K) (↥L)))
            (add_zero 1) := by
    intro M0 x
    simp only [SSGRoute.PTExt.extToClasses]
    rw [CategoryTheory.Abelian.Ext.comp_assoc_of_second_deg_zero,
      CategoryTheory.Abelian.Ext.mk₀_comp_mk₀,
      ← Work.SSGRoute.resMap_classGroupMap_comp_classIncl k (↥K) (↥L),
      ← CategoryTheory.Abelian.Ext.mk₀_comp_mk₀,
      ← CategoryTheory.Abelian.Ext.comp_assoc_of_third_deg_zero,
      ← Work.SSGRoute.extRes_comp_mk₀]
  have hZ : SSGRoute.PTExt.extToClasses (k := k) (K := ↥L) Z' = 0 := by
    rw [hh_Z', hZgen (M0 := SSGRoute.PTExt.modRep (↥K ≃ₐ[k] ↥K)
          (Work.SSGRoute.PT.VFcoef p M T)) Z,
      show SSGRoute.PTExt.extToClasses (k := k) (K := ↥K) Z = 0 from
        SSGRoute.PTExt.extToClasses_extToIdeles (k := k) (K := ↥K)
          (finZBg p K ζ hζ hζK T hT M a),
      show SSGRoute.PTExt.extRes (SSGRoute.PTExt.galRes k (↥K) (↥L))
          (0 : CategoryTheory.Abelian.Ext (SSGRoute.PTExt.modRep (↥K ≃ₐ[k] ↥K)
              (Work.SSGRoute.PT.VFcoef p M T))
            (SSGRoute.PTExt.classesK k ↥K) 1) = 0 from
        Work.SSGRoute.E6Util.extRes_zero _]
    simp
  -- ### the finite value formula at the level `L`
  have hfinval : ∀ (A : ValuationSubring Ω) (hA : SSGRoute.IsFinPlace k A) (hmem : A ∈ S'),
      G1pOwn.g1FinHalf p k Ω K ζ hζ hζK T hT χ M (SSGRoute.decomp k A) a b =
        χ L hKL (Work.SSGRoute.PT.iota (k := k) (L := ↥L)
          (NK.GlobalCFT.Place.ofFinite (Work.SSGRoute.PT.finQW L A hA))
          (SSGRoute.PTExt.yonedaPair
            (SSGRoute.PTExt.extLoc (k := k) (K := ↥L)
              (NK.GlobalCFT.Place.ofFinite (Work.SSGRoute.PT.finQW L A hA)) Z')
            (SSGRoute.PTExt.extHRestrict (SSGRoute.PTExt.decompK (k := k)
              (NK.GlobalCFT.Place.ofFinite (Work.SSGRoute.PT.finQW L A hA))) h_L))) := by
    intro A hA hmem
    have hbA : SSGRoute.IsCocycleOn (SSGRoute.res k K) (SSGRoute.decomp k A) b :=
      G1plusOwn.isCocycleOn_of_le (SSGRoute.res k K) le_top (f := b) hb1
    have ha2' : SSGRoute.IsLocConstOn (SSGRoute.decomp k A) a :=
      G1plusOwn.isLocConstOn_of_le (Γ := Ω ≃ₐ[k] Ω) (G := ↥K ≃ₐ[k] ↥K) (M' := M)
        (H := SSGRoute.decomp k A) (H' := ⊤) le_top (f := a) ha2
    have hb2' : SSGRoute.IsLocConstOn (SSGRoute.decomp k A) b :=
      G1plusOwn.isLocConstOn_of_le (Γ := Ω ≃ₐ[k] Ω) (G := ↥K ≃ₐ[k] ↥K)
        (M' := Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T))
        (H := SSGRoute.decomp k A) (H' := ⊤) le_top (f := b) hb2
    rw [G1plusOwn.g1FinHalf_hpair p k Ω K ζ hζ hζK T hT χ hχcompat M A hA a b ha2' hb2' hbA
        L hKL b₀ (fun σ _ => hb₀ σ),
      ← finZB_square p k Ω K ζ hζ hζK T hT M A hA a ha1 ha2]
    refine congrArg (fun v => χ L hKL (Work.SSGRoute.PT.iota (k := k) (L := ↥L)
      (NK.GlobalCFT.Place.ofFinite (Work.SSGRoute.PT.finQW L A hA)) v)) ?_
    rw [hh_Z', ← hh_Z]
    exact (Work.SSGRoute.PT.vf_local_compare p k Ω K T M L hKL A hA Z
      (SSGRoute.PTExt.extLoc (k := k) (K := ↥K)
        (NK.GlobalCFT.Place.ofFinite (Work.SSGRoute.PT.finQ K A hA)) Z)
      rfl h_L b₀ hψ (by rw [hh_L]) b (fun σ => hb₀ σ) hbA (fun σ _ => hb₀ σ)).symm
  -- ### the archimedean value formula at the level `L` (from `hrecArchFamily_seamValue`)
  have harchval : ∀ (c : Ω ≃ₐ[k] Ω) (hc2 : c ^ 2 = 1) (hc1 : c ≠ 1),
      archFamily p k Ω K ζ hζ hζK T hT χ φc hφc M (Subgroup.zpowers c) a b =
        χ L hKL (Work.SSGRoute.PT.iota (k := k) (L := ↥L)
          (NK.GlobalCFT.Place.ofInfinite (NumberField.InfinitePlace.mk
            ((φc c hc2 hc1).comp (algebraMap ↥L Ω))))
          (SSGRoute.PTExt.yonedaPair
            (SSGRoute.PTExt.extLoc (k := k) (K := ↥L)
              (NK.GlobalCFT.Place.ofInfinite (NumberField.InfinitePlace.mk
                ((φc c hc2 hc1).comp (algebraMap ↥L Ω)))) Z')
            (SSGRoute.PTExt.extHRestrict (SSGRoute.PTExt.decompK (k := k)
              (NK.GlobalCFT.Place.ofInfinite (NumberField.InfinitePlace.mk
                ((φc c hc2 hc1).comp (algebraMap ↥L Ω))))) h_L))) := by
    intro c hc2 hc1
    have hb' : SSGRoute.IsCocycleOn (SSGRoute.res k K) (Subgroup.zpowers c) b :=
      G1plusOwn.isCocycleOn_of_le (SSGRoute.res k K) le_top (f := b) hb1
    rw [Work.PT.hrecArchFamily_seamValue p k Ω K ζ hζ hζK T hT χ hχadd hχcompat φc hφc
      M c hc2 hc1 a b ha1 ha2 hb' L hKL b₀ (fun σ => hb₀ σ) hψ]
    refine congrArg (fun v => χ L hKL (Work.SSGRoute.PT.iota (k := k) (L := ↥L)
      (NK.GlobalCFT.Place.ofInfinite (NumberField.InfinitePlace.mk
        ((φc c hc2 hc1).comp (algebraMap ↥L Ω)))) v)) ?_
    rw [← hh_Z, ← hh_L, hh_Z']
    exact Work.SSGRoute.extLoc_levelPair_idleRepMap_eq k (↥K) (↥L)
      (SSGRoute.PTExt.modRep (↥K ≃ₐ[k] ↥K) (Work.SSGRoute.PT.VFcoef p M T)) Z
      (Work.SSGRoute.PT.levelClassOf p k Ω K T M L b₀ hψ)
      (NK.GlobalCFT.Place.ofInfinite (NumberField.InfinitePlace.mk
        ((φc c hc2 hc1).comp (algebraMap ↥L Ω))))
  -- ### the supporting Finset `W`
  let wfin : {A : ValuationSubring Ω // A ∈ S'} → NK.GlobalCFT.Place ↥L :=
    fun A => NK.GlobalCFT.Place.ofFinite (Work.SSGRoute.PT.finQW L A.1 (hS'fin A.1 A.2))
  let C'' : Finset (Ω ≃ₐ[k] Ω) := C'.filter (fun c => SSGRoute.res k L c ≠ 1)
  let warch : {c : Ω ≃ₐ[k] Ω // c ∈ C''} → NK.GlobalCFT.Place ↥L :=
    fun c => NK.GlobalCFT.Place.ofInfinite (NumberField.InfinitePlace.mk
      ((φc c.1 (hC'inv c.1 (Finset.mem_of_mem_filter c.1 c.2))
        (fun hc1 => (Finset.mem_filter.mp c.2).2 (by rw [hc1]; exact map_one _))).comp
        (algebraMap ↥L Ω)))
  let W : Finset (NK.GlobalCFT.Place ↥L) :=
    S'.attach.image wfin ∪ C''.attach.image warch
  have hseam_congr : ∀ (c : {c : Ω ≃ₐ[k] Ω // c ∈ C''}) (hc2 : c.1 ^ 2 = 1) (hc1 : c.1 ≠ 1),
      NK.GlobalCFT.Place.ofInfinite (NumberField.InfinitePlace.mk
          ((φc c.1 hc2 hc1).comp (algebraMap ↥L Ω)))
        = warch c := by
    intro c hc2 hc1
    have hφ : (φc c.1 hc2 hc1)
        = (φc c.1 (hC'inv c.1 (Finset.mem_of_mem_filter c.1 c.2))
            (fun hc1' => (Finset.mem_filter.mp c.2).2 (by rw [hc1']; exact map_one _))) := by
      simp only [Subsingleton.elim hc2 (hC'inv c.1 (Finset.mem_of_mem_filter c.1 c.2)),
        Subsingleton.elim hc1
          (fun hc1' => (Finset.mem_filter.mp c.2).2 (by rw [hc1']; exact map_one _))]
    rw [hφ]
  have hWmem : ∀ (c : {c : Ω ≃ₐ[k] Ω // c ∈ C''}), warch c ∈ W := fun c =>
    Finset.mem_union_right _ (Finset.mem_image.mpr ⟨c, Finset.mem_attach C'' c, rfl⟩)
  -- ### pairwise non-conjugacy of `W`
  have hW : ∀ w ∈ W, ∀ w' ∈ W, (∃ σ : ↥L ≃ₐ[k] ↥L, σ • w = w') → w = w' := by
    intro w hw w' hw' hconj
    rw [Finset.mem_union] at hw hw'
    rcases hw with hw | hw <;> rcases hw' with hw' | hw'
    · obtain ⟨A, -, hA⟩ := Finset.mem_image.mp hw
      obtain ⟨B, -, hB⟩ := Finset.mem_image.mp hw'
      obtain ⟨σ, hσ⟩ := hconj
      rw [← hA, ← hB] at hσ
      rw [← hA, ← hB]
      exact congrArg wfin (Subtype.ext
        (G1plusOwn.isConjPlace_of_finQW_conj L S' hS'fin hS'disj σ (A := A.1) (B := B.1)
          A.2 B.2 hσ))
    · obtain ⟨A, -, hA⟩ := Finset.mem_image.mp hw
      obtain ⟨c, -, hc⟩ := Finset.mem_image.mp hw'
      obtain ⟨σ, hσ⟩ := hconj
      rw [← hA, ← hc] at hσ
      rw [NK.GlobalCFT.Place.smul_ofFinite] at hσ
      exact absurd hσ.symm (NK.GlobalCFT.Place.ofInfinite_ne_ofFinite _ _)
    · obtain ⟨c, -, hc⟩ := Finset.mem_image.mp hw
      obtain ⟨A, -, hA⟩ := Finset.mem_image.mp hw'
      obtain ⟨σ, hσ⟩ := hconj
      rw [← hc, ← hA] at hσ
      rw [NK.GlobalCFT.Place.smul_ofInfinite] at hσ
      exact absurd hσ (NK.GlobalCFT.Place.ofInfinite_ne_ofFinite _ _)
    · obtain ⟨c, -, hc⟩ := Finset.mem_image.mp hw
      obtain ⟨c', -, hc'⟩ := Finset.mem_image.mp hw'
      obtain ⟨σ, hσ⟩ := hconj
      rw [← hc, ← hc'] at hσ
      have hcC' : c.1 ∈ C' := Finset.mem_of_mem_filter c.1 c.2
      have hc1 : c.1 ≠ 1 := fun h1 => (Finset.mem_filter.mp c.2).2 (by rw [h1]; exact map_one _)
      have hc'C' : c'.1 ∈ C' := Finset.mem_of_mem_filter c'.1 c'.2
      have hc1' : c'.1 ≠ 1 := fun h1 => (Finset.mem_filter.mp c'.2).2 (by rw [h1]; exact map_one _)
      have hconj' : ∃ γ : ↥L ≃ₐ[k] ↥L,
          γ • NK.GlobalCFT.Place.ofInfinite (NumberField.InfinitePlace.mk
            ((φc c.1 (hC'inv c.1 hcC') hc1).comp (algebraMap ↥L Ω)))
            = NK.GlobalCFT.Place.ofInfinite (NumberField.InfinitePlace.mk
              ((φc c'.1 (hC'inv c'.1 hc'C') hc1').comp (algebraMap ↥L Ω))) := by
        refine ⟨σ, ?_⟩
        rw [← hseam_congr c (hC'inv c.1 hcC') hc1,
          ← hseam_congr c' (hC'inv c'.1 hc'C') hc1'] at hσ
        exact hσ
      have hcc : c.1 = c'.1 :=
        (Work.PT.seamPlace_orbit_theory p k Ω K φc hφc C' hC'inv hC'rep hC'disj L hKL).2
          c.1 (hC'inv c.1 hcC') hc1 hcC' (Finset.mem_filter.mp c.2).2
          c'.1 (hC'inv c'.1 hc'C') hc1' hc'C' (Finset.mem_filter.mp c'.2).2 hconj'
      rw [← hc, ← hc']
      exact congrArg warch (Subtype.ext hcc)
  -- ### the vanishing of the local values off the classes of `W`
  have hoff : ∀ w : NK.GlobalCFT.Place ↥L,
      (∀ w' ∈ W, ∀ σ : ↥L ≃ₐ[k] ↥L, σ • w' ≠ w) →
      SSGRoute.PTExt.yonedaPair (SSGRoute.PTExt.extLoc (k := k) (K := ↥L) w Z')
        (SSGRoute.PTExt.extHRestrict (SSGRoute.PTExt.decompK (k := k) w) h_L) = 0 := by
    intro w hw
    rcases w with v | q'
    · -- an infinite place
      by_cases hD : SSGRoute.PTExt.decompK (k := k)
          (NK.GlobalCFT.Place.ofInfinite v) = ⊥
      · have hz : SSGRoute.PTExt.extHRestrict (SSGRoute.PTExt.decompK (k := k)
            (NK.GlobalCFT.Place.ofInfinite v)) h_L = 0 :=
          hD ▸ Work.SSGRoute.E9Nodes.extHRestrict_bot_eq_zero (le_refl 1) h_L
        rw [hz]
        simp only [SSGRoute.PTExt.yonedaPair_zero_left, SSGRoute.PTExt.yonedaPair_zero_right]
      · obtain ⟨c, hc2, hc1, hcC', hne, γ, hγ⟩ :=
          (Work.PT.seamPlace_orbit_theory p k Ω K φc hφc C' hC'inv hC'rep hC'disj L hKL).1
            (NK.GlobalCFT.Place.ofInfinite v) ⟨v, rfl⟩ hD
        have hcC'' : c ∈ C'' := Finset.mem_filter.mpr ⟨hcC', hne⟩
        refine absurd (hw (warch ⟨c, hcC''⟩) (hWmem ⟨c, hcC''⟩) γ⁻¹) ?_
        rw [← hseam_congr ⟨c, hcC''⟩ hc2 hc1, ← hγ, smul_smul]
        simp
    · -- a finite place
      obtain ⟨B, hB, hBq, hBnot⟩ :=
        G1plusOwn.goodPlaceUnder_finQW L S' hS'fin q' (fun A hA σ hc => hw
          (wfin ⟨A, hA⟩) (Finset.mem_union_left _ (Finset.mem_image.mpr
            ⟨⟨A, hA⟩, Finset.mem_attach S' _, rfl⟩)) σ hc)
      have hunr : ∀ σ : ↥L ≃ₐ[k] ↥L,
          SSGRoute.PTExt.IsInertiaAt (Work.SSGRoute.PT.finQW L B hB) σ → σ = 1 :=
        fun σ hσ => G1plusOwn.isInertiaAt_eq_one_of_inertiaSub_le k Ω B hB L
          (hInertia B hB hBnot) σ hσ
      have hgoodB := hgood B hB hBnot
      let u : NK.GlobalCFT.Place ↥K := NK.GlobalCFT.Place.ofFinite (Work.SSGRoute.PT.finQ K B hB)
      let wB : NK.GlobalCFT.Place ↥L := NK.GlobalCFT.Place.ofFinite (Work.SSGRoute.PT.finQW L B hB)
      let hwB : NK.GlobalCFT.Place.LiesOver wB u :=
        (Work.SSGRoute.PT.place_glue_level k Ω K L hKL B hB (Work.SSGRoute.PT.finQ K B hB)
          (fun x => Work.SSGRoute.PT.finQ_spec K B hB x) (Work.SSGRoute.PT.finQW L B hB)
          (fun y => Work.SSGRoute.PT.finQW_spec L B hB y)).1
      have h1 : SSGRoute.PTExt.extLoc (k := k) (K := ↥L) wB
          (SSGRoute.PTExt.levelPair (SSGRoute.PTExt.galRes k (↥K) (↥L))
            (Work.SSGRoute.idleRepMap k (↥K) (↥L)) Z h_L)
          = SSGRoute.PTExt.levelPair
              (Work.SSGRoute.decompKRestrict k ↥K ↥L u wB hwB)
              (Work.SSGRoute.localUnitsMap k ↥K ↥L u wB hwB)
              (SSGRoute.PTExt.extLoc (k := k) (K := ↥K) u Z)
              (SSGRoute.PTExt.extHRestrict (SSGRoute.PTExt.decompK (k := k) (K := ↥L) wB)
                h_L) := by
        rw [Work.SSGRoute.extLoc_levelPair_idleRepMap_eq (k := k) (K := ↥K) (L := ↥L)
          (SSGRoute.PTExt.modRep (↥K ≃ₐ[k] ↥K) (Work.SSGRoute.PT.VFcoef p M T)) Z h_L wB]
        rw [Work.SSGRoute.E7cOmega.extLoc_push_ideleMap (k := k) (K := ↥K) (L := ↥L) (z := Z)
          (u := u) (w := wB) (hw := hwB)
          (ι := Work.SSGRoute.localUnitsMap k ↥K ↥L u wB hwB)
          (hι := Work.SSGRoute.localUnitsMap_spec k ↥K ↥L u wB hwB)]
        rfl
      have hgoal : SSGRoute.PTExt.yonedaPair (SSGRoute.PTExt.extLoc (k := k) (K := ↥L) wB Z')
          (SSGRoute.PTExt.extHRestrict (SSGRoute.PTExt.decompK (k := k) (K := ↥L) wB) h_L)
          = SSGRoute.PTExt.extLoc (k := k) (K := ↥L) wB
              (SSGRoute.PTExt.levelPair (SSGRoute.PTExt.galRes k (↥K) (↥L))
                (Work.SSGRoute.idleRepMap k (↥K) (↥L)) Z h_L) := by
        rw [hh_Z']
        exact (Work.SSGRoute.extLoc_levelPair_idleRepMap_eq (k := k) (K := ↥K) (L := ↥L)
          (SSGRoute.PTExt.modRep (↥K ≃ₐ[k] ↥K)
            (Work.SSGRoute.PT.VFcoef p M T)) Z h_L wB).symm
      have hfin : SSGRoute.PTExt.yonedaPair (SSGRoute.PTExt.extLoc (k := k) (K := ↥L) wB Z')
          (SSGRoute.PTExt.extHRestrict (SSGRoute.PTExt.decompK (k := k) (K := ↥L) wB) h_L)
          = 0 := by
        rw [hgoal, h1]
        rw [show SSGRoute.PTExt.extLoc (k := k) (K := ↥K) u Z
            = finZB p K ζ hζ hζK T hT M B hB a from by
          rw [hh_Z]
          exact finZB_square p k Ω K ζ hζ hζK T hT M B hB a ha1 ha2]
        refine Work.SSGRoute.PT.levelPair_unramified_eq_zero k ↥K
          (SSGRoute.PTExt.modRep (↥K ≃ₐ[k] ↥K)
            (Work.SSGRoute.PT.VFcoef p M T))
          u ↥L (Work.SSGRoute.PT.finQW L B hB) hwB hunr
          (Work.SSGRoute.decompKRestrict k ↥K ↥L u wB hwB)
          (Work.SSGRoute.decompKRestrict_coe k ↥K ↥L u wB hwB)
          (Work.SSGRoute.localUnitsMap k ↥K ↥L u wB hwB)
          (Work.SSGRoute.localUnitsMap_spec k ↥K ↥L u wB hwB)
          (finZB p K ζ hζ hζK T hT M B hB a)
          (finZB_unramified p k Ω K ζ hζ hζK T hT M B hB hgoodB.1 hgoodB.2.1 a
            (G1plusOwn.isCocycleOn_of_le (SSGRoute.res k K) le_top (f := a) ha1)
            (G1plusOwn.isLocConstOn_of_le (Γ := Ω ≃ₐ[k] Ω) (G := ↥K ≃ₐ[k] ↥K)
              (M' := M) (H := SSGRoute.decomp k B) (H' := ⊤) le_top (f := a) ha2)
            (fun σ hσ => (hgoodB.2.2 σ hσ).1))
          (SSGRoute.PTExt.extHRestrict (SSGRoute.PTExt.decompK (k := k) (K := ↥L) wB) h_L)
      rw [show q' = Work.SSGRoute.PT.finQW L B hB from hBq.symm]
      exact hfin
  -- ### the `p`-torsion of the local values
  have iota_nsmul : ∀ (w : NK.GlobalCFT.Place ↥L)
      (z : SSGRoute.PTExt.extH (SSGRoute.PTExt.localUnitsK (k := k) (K := ↥L) w) 2) (n : ℕ),
      n • Work.SSGRoute.PT.iota (k := k) (L := ↥L) w z
        = Work.SSGRoute.PT.iota (k := k) (L := ↥L) w (n • z) := by
    intro w z n
    induction n with
    | zero => rw [zero_smul, zero_smul, Work.SSGRoute.PT.iota_zero]
    | succ n ih => rw [add_nsmul, one_smul, ih, ← Work.SSGRoute.PT.iota_add, add_nsmul, one_smul]
  have hp' : ∀ w ∈ W, p • Work.SSGRoute.PT.iota (k := k) (L := ↥L) w
      (SSGRoute.PTExt.yonedaPair (SSGRoute.PTExt.extLoc (k := k) (K := ↥L) w Z')
        (SSGRoute.PTExt.extHRestrict (SSGRoute.PTExt.decompK (k := k) (K := ↥L) w) h_L)) = 0 := by
    intro w hw
    have hX : ∀ x : Work.SSGRoute.PT.VFcoef p M T, p • x = 0 :=
      fun x => Work.SSGRoute.PT.nsmul_eq_zero_of_zmod' p x
    have hxl : p • SSGRoute.PTExt.extLoc (k := k) (K := ↥L) w Z' = 0 :=
      Work.SSGRoute.E6Util.ext_nsmul_p_torsion_left p hX _
    have hy : p • SSGRoute.PTExt.yonedaPair (SSGRoute.PTExt.extLoc (k := k) (K := ↥L) w Z')
        (SSGRoute.PTExt.extHRestrict (SSGRoute.PTExt.decompK (k := k) (K := ↥L) w) h_L) = 0 := by
      rw [show p • SSGRoute.PTExt.yonedaPair (SSGRoute.PTExt.extLoc (k := k) (K := ↥L) w Z')
            (SSGRoute.PTExt.extHRestrict (SSGRoute.PTExt.decompK (k := k) (K := ↥L) w) h_L)
          = SSGRoute.PTExt.yonedaPair
              (p • SSGRoute.PTExt.extLoc (k := k) (K := ↥L) w Z')
              (SSGRoute.PTExt.extHRestrict (SSGRoute.PTExt.decompK (k := k) (K := ↥L) w)
                h_L) from
        (AddMonoidHom.map_nsmul
          { toFun := fun x : CategoryTheory.Abelian.Ext
                (Rep.res (SSGRoute.PTExt.decompK (k := k) (K := ↥L) w).subtype
                  (Rep.res (SSGRoute.PTExt.galRes k (↥K) (↥L))
                    (SSGRoute.PTExt.modRep (↥K ≃ₐ[k] ↥K)
                      (Work.SSGRoute.PT.VFcoef p M T))))
                (SSGRoute.PTExt.localUnitsK (k := k) (K := ↥L) w) 1 =>
              SSGRoute.PTExt.yonedaPair x
                (SSGRoute.PTExt.extHRestrict (SSGRoute.PTExt.decompK (k := k) (K := ↥L) w) h_L)
            map_zero' := SSGRoute.PTExt.yonedaPair_zero_right _
            map_add' := fun x x' => SSGRoute.PTExt.yonedaPair_add_right x x' _ } p _).symm,
        hxl]
      simp only [SSGRoute.PTExt.yonedaPair_zero_left, SSGRoute.PTExt.yonedaPair_zero_right]
    rw [iota_nsmul, hy, Work.SSGRoute.PT.iota_zero]
  -- ### the class-formation reciprocity sum
  have hchild := Work.SSGRoute.PT.G1plusOwn.sum_iota_eq_zero_of_extToClasses_zero p
    (fun u : SSGRoute.PTExt.extH (SSGRoute.PTExt.classesK k ↥L) 2 => χ L hKL u)
    (fun u v hu hv => hχadd L hKL u v hu hv) Z' hZ h_L W hW hoff hp'
  -- ### splitting the sum into its finite and archimedean parts
  have hdisj : Disjoint (S'.attach.image wfin) (C''.attach.image warch) := by
    refine Finset.disjoint_left.mpr fun w hw1 hw2 => ?_
    obtain ⟨A, -, hA⟩ := Finset.mem_image.mp hw1
    obtain ⟨c, -, hc⟩ := Finset.mem_image.mp hw2
    exact (NK.GlobalCFT.Place.ofInfinite_ne_ofFinite _ _) (hc.trans hA.symm)
  have hinjfin : Set.InjOn wfin ↑S'.attach := by
    intro A _ B _ h
    exact Subtype.ext (G1plusOwn.isConjPlace_of_finQW_conj L S' hS'fin hS'disj 1
      (A := A.1) (B := B.1) A.2 B.2 (by simpa only [wfin, one_smul] using h))
  have hinjarch : Set.InjOn warch ↑C''.attach := by
    intro c _ c' _ h
    have hcC' : c.1 ∈ C' := Finset.mem_of_mem_filter c.1 c.2
    have hc1 : c.1 ≠ 1 := fun h1 => (Finset.mem_filter.mp c.2).2 (by rw [h1]; exact map_one _)
    have hc'C' : c'.1 ∈ C' := Finset.mem_of_mem_filter c'.1 c'.2
    have hc1' : c'.1 ≠ 1 := fun h1 => (Finset.mem_filter.mp c'.2).2 (by rw [h1]; exact map_one _)
    have hconj' : ∃ γ : ↥L ≃ₐ[k] ↥L,
        γ • NK.GlobalCFT.Place.ofInfinite (NumberField.InfinitePlace.mk
          ((φc c.1 (hC'inv c.1 hcC') hc1).comp (algebraMap ↥L Ω)))
          = NK.GlobalCFT.Place.ofInfinite (NumberField.InfinitePlace.mk
            ((φc c'.1 (hC'inv c'.1 hc'C') hc1').comp (algebraMap ↥L Ω))) := by
      refine ⟨1, ?_⟩
      rw [← hseam_congr c (hC'inv c.1 hcC') hc1,
        ← hseam_congr c' (hC'inv c'.1 hc'C') hc1'] at h
      simpa using h
    exact Subtype.ext
      ((Work.PT.seamPlace_orbit_theory p k Ω K φc hφc C' hC'inv hC'rep hC'disj L hKL).2
        c.1 (hC'inv c.1 hcC') hc1 hcC' (Finset.mem_filter.mp c.2).2
        c'.1 (hC'inv c'.1 hc'C') hc1' hc'C' (Finset.mem_filter.mp c'.2).2 hconj')
  have hsplit : ∑ w ∈ W, χ L hKL (Work.SSGRoute.PT.iota (k := k) (L := ↥L) w
        (SSGRoute.PTExt.yonedaPair (SSGRoute.PTExt.extLoc (k := k) (K := ↥L) w Z')
          (SSGRoute.PTExt.extHRestrict (SSGRoute.PTExt.decompK (k := k) (K := ↥L) w) h_L)))
      = ∑ A ∈ S'.attach, G1pOwn.g1FinHalf p k Ω K ζ hζ hζK T hT χ M
          (SSGRoute.decomp k (A : ValuationSubring Ω)) a b
        + ∑ c ∈ C''.attach, archFamily p k Ω K ζ hζ hζK T hT χ φc hφc M
            (Subgroup.zpowers c.1) a b := by
    rw [show W = S'.attach.image wfin ∪ C''.attach.image warch from rfl,
      Finset.sum_union hdisj, Finset.sum_image hinjfin, Finset.sum_image hinjarch]
    congr 1
    · refine Finset.sum_congr rfl fun A _ => ?_
      exact (hfinval (A : ValuationSubring Ω) (hS'fin A.1 A.2) A.2).symm
    · refine Finset.sum_congr rfl fun c _ => ?_
      have hcC' : c.1 ∈ C' := Finset.mem_of_mem_filter c.1 c.2
      have hne : SSGRoute.res k L c.1 ≠ 1 := (Finset.mem_filter.mp c.2).2
      have hc1 : c.1 ≠ 1 := fun h1 => hne (by rw [h1]; exact map_one _)
      exact (harchval c.1 (hC'inv c.1 hcC') hc1).symm
  -- ### the archimedean terms of `C'` acting trivially on `L` vanish
  have htriv : ∀ c ∈ C', SSGRoute.res k L c = 1 →
      archFamily p k Ω K ζ hζ hζK T hT χ φc hφc M (Subgroup.zpowers c) a b = 0 := by
    intro c hc hres1
    by_cases hc1 : c = 1
    · subst hc1
      rw [Subgroup.zpowers_one_eq_bot]
      exact archFamily_bot p k Ω K ζ hζ hζK T hT χ φc hφc M a b
    · rw [harchval c (hC'inv c hc) hc1]
      have hbot : SSGRoute.PTExt.decompK (k := k)
          (NK.GlobalCFT.Place.ofInfinite (NumberField.InfinitePlace.mk
            ((φc c (hC'inv c hc) hc1).comp (algebraMap ↥L Ω)))) = ⊥ := by
        rw [Work.SSGRoute.PT.decompK_linked k Ω L c (hC'inv c hc) hc1
          (φc c (hC'inv c hc) hc1) (hφc c (hC'inv c hc) hc1), Subgroup.eq_bot_iff_forall]
        intro x hx
        rw [Subgroup.mem_map] at hx
        obtain ⟨y, hy, rfl⟩ := hx
        rw [Subgroup.mem_zpowers_iff] at hy
        obtain ⟨n, rfl⟩ := hy
        rw [map_zpow, hres1, one_zpow]
      have hzero : SSGRoute.PTExt.yonedaPair
          (SSGRoute.PTExt.extLoc (k := k) (K := ↥L)
            (NK.GlobalCFT.Place.ofInfinite (NumberField.InfinitePlace.mk
              ((φc c (hC'inv c hc) hc1).comp (algebraMap ↥L Ω)))) Z')
          (SSGRoute.PTExt.extHRestrict (SSGRoute.PTExt.decompK (k := k)
            (NK.GlobalCFT.Place.ofInfinite (NumberField.InfinitePlace.mk
              ((φc c (hC'inv c hc) hc1).comp (algebraMap ↥L Ω))))) h_L) = 0 := by
        have hz : SSGRoute.PTExt.extHRestrict (SSGRoute.PTExt.decompK (k := k)
            (NK.GlobalCFT.Place.ofInfinite (NumberField.InfinitePlace.mk
              ((φc c (hC'inv c hc) hc1).comp (algebraMap ↥L Ω))))) h_L = 0 :=
          hbot ▸ Work.SSGRoute.E9Nodes.extHRestrict_bot_eq_zero (le_refl 1) h_L
        rw [hz]
        simp only [SSGRoute.PTExt.yonedaPair_zero_left, SSGRoute.PTExt.yonedaPair_zero_right]
      rw [hzero, Work.SSGRoute.PT.iota_zero]
      exact Work.SSGRoute.PT.chi_zero_of_additive (k := k) (K := L) p (χ L hKL)
        (fun u v hu hv => hχadd L hKL u v hu hv)
  -- ### reindexing the archimedean sum over all of `C'`
  have harchsplit : ∑ c ∈ C', archFamily p k Ω K ζ hζ hζK T hT χ φc hφc M
        (Subgroup.zpowers c) a b
      = ∑ c ∈ C''.attach, archFamily p k Ω K ζ hζ hζK T hT χ φc hφc M
          (Subgroup.zpowers c.1) a b := by
    rw [Finset.sum_attach C'' (fun c => archFamily p k Ω K ζ hζ hζK T hT χ φc hφc M
      (Subgroup.zpowers c) a b)]
    refine (Finset.sum_subset ?_ ?_).symm
    · intro x hx
      exact Finset.mem_of_mem_filter x hx
    · intro x hx hxnot
      exact htriv x hx (by
        by_contra hne
        exact hxnot (Finset.mem_filter.mpr ⟨hx, hne⟩))
  -- ### conclusion
  rw [← Finset.sum_attach S' (fun A => G1pOwn.g1FinHalf p k Ω K ζ hζ hζK T hT χ M
    (SSGRoute.decomp k A) a b), harchsplit, ← hsplit]
  exact hchild



end Work.SSGRoute.PT
