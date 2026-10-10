import Mathlib.RingTheory.Henselian
import Mathlib.Algebra.Field.ZMod
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.NumberTheory.NumberField.InfinitePlace.Ramification
import Submission.Work.SSGRoute.ArchPlace.linkedPlaceOfInvolution
import Submission.Work.SSGRoute.HRec.exists_conjInv_kummerChar_eq_zero_iff
import Submission.Work.SSGRoute.HRec.realPlace_eq_of_isNegAt_iff
import Submission.Work.SSGRoute.PT.archFamilyLocal
import Submission.Work.SSGRoute.PT.wc_orbit_injective
import Submission.Work.SSGRoute.ZDataTwo.ArchDictionary
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.PT

open NumberField

/-! ## The sign at the seam place of an involution -/

/-- For a seam embedding `φ` of `d` (`φ ∘ d = conj ∘ φ`), the sign of `a ∈ kˣ` at the infinite
place `mk (φ|_k)` of `k` is given by the norm-set predicate of `d`. -/
theorem isNegAt_mk_seamComp_iff (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
    [IsAlgClosure k Ω] (d : Ω ≃ₐ[k] Ω) (φ : Ω →+* ℂ)
    (hφ : ∀ x : Ω, φ (d x) = starRingEnd ℂ (φ x)) (a : kˣ) :
    Work.SSGRoute.ZDataTwo.IsNegAt (NumberField.InfinitePlace.mk (φ.comp (algebraMap k Ω))) a ↔
      algebraMap k Ω (a : k) ∉ Work.SSGRoute.TwoTorsion.normSet d.toRingEquiv := by
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed k
  have hreal : NumberField.ComplexEmbedding.IsReal (φ.comp (algebraMap k Ω)) := by
    rw [NumberField.ComplexEmbedding.isReal_iff]
    ext x
    show starRingEnd ℂ (φ (algebraMap k Ω x)) = φ (algebraMap k Ω x)
    rw [← hφ (algebraMap k Ω x), d.commutes x]
  have hw : (NumberField.InfinitePlace.mk (φ.comp (algebraMap k Ω))).IsReal :=
    NumberField.InfinitePlace.isReal_mk_iff.mpr hreal
  have hΨ : ∀ b : k, φ (algebraMap k Ω b) =
      (((NumberField.InfinitePlace.embedding_of_isReal hw) b : ℝ) : ℂ) := by
    intro b
    rw [NumberField.InfinitePlace.embedding_of_isReal_apply hw b,
      NumberField.InfinitePlace.embedding_mk_eq_of_isReal hreal]
    rfl
  constructor
  · intro hneg hmem
    exact (Work.SSGRoute.HRec.not_isNegAt_of_mem_normSet
      (NumberField.InfinitePlace.mk (φ.comp (algebraMap k Ω))) hw hΨ hφ a hmem) hneg
  · intro hmem
    by_contra hneg
    exact hmem (Work.SSGRoute.HRec.mem_normSet_of_not_isNegAt
      (NumberField.InfinitePlace.mk (φ.comp (algebraMap k Ω))) hw hΨ hφ a hneg)

/-- If `res_L c = 1` then the seam embedding of `c` is real valued on `L`, so its place is real;
contrapositively, a complex seam place forces `res_L c ≠ 1`. -/
theorem res_ne_one_of_seamComp_isComplex (k Ω : Type) [Field k] [NumberField k] [Field Ω]
    [Algebra k Ω] [IsAlgClosure k Ω]
    (L : IntermediateField k Ω) [FiniteDimensional k L] [IsGalois k L] [NumberField ↥L]
    (c : Ω ≃ₐ[k] Ω) (φ : Ω →+* ℂ)
    (hφ : ∀ x : Ω, φ (c x) = starRingEnd ℂ (φ x))
    (hcomplex : (NumberField.InfinitePlace.mk (φ.comp (algebraMap ↥L Ω))).IsComplex) :
    SSGRoute.res k L c ≠ 1 := by
  intro hres
  have hcx : ∀ x : ↥L, c ((x : ↥L) : Ω) = ((x : ↥L) : Ω) := by
    intro x
    have hx : (SSGRoute.res k L c) x = x :=
      congrArg (fun (e : ↥L ≃ₐ[k] ↥L) => e x) hres
    have h := AlgEquiv.restrictNormalHom_apply L c x
    show c ((x : ↥L) : Ω) = ((x : ↥L) : Ω)
    rw [← h, hx]
  have hreal : NumberField.ComplexEmbedding.IsReal (φ.comp (algebraMap ↥L Ω)) := by
    rw [NumberField.ComplexEmbedding.isReal_iff]
    ext x
    show starRingEnd ℂ (φ ((x : ↥L) : Ω)) = φ ((x : ↥L) : Ω)
    rw [← hφ ((x : ↥L) : Ω), hcx x]
  exact (NumberField.InfinitePlace.not_isReal_iff_isComplex.mpr hcomplex)
    (NumberField.InfinitePlace.isReal_mk_iff.mpr hreal)

/-! ## The base place of a seam embedding only depends on the conjugacy class -/

/-- Two seam embeddings of the *same* involution give the same place of `k`. -/
theorem mk_seamComp_eq_of_same (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
    [IsAlgClosure k Ω]
    (c : Ω ≃ₐ[k] Ω) (hc2 : c ^ 2 = 1) (hc1 : c ≠ 1) (φ φ' : Ω →+* ℂ)
    (hφ : ∀ x : Ω, φ (c x) = starRingEnd ℂ (φ x))
    (hφ' : ∀ x : Ω, φ' (c x) = starRingEnd ℂ (φ' x)) :
    NumberField.InfinitePlace.mk (φ.comp (algebraMap k Ω)) =
      NumberField.InfinitePlace.mk (φ'.comp (algebraMap k Ω)) := by
  have hw : (NumberField.InfinitePlace.mk (φ.comp (algebraMap k Ω))).IsReal := by
    rw [NumberField.InfinitePlace.isReal_mk_iff, NumberField.ComplexEmbedding.isReal_iff]
    ext x
    show starRingEnd ℂ (φ (algebraMap k Ω x)) = φ (algebraMap k Ω x)
    rw [← hφ (algebraMap k Ω x), c.commutes x]
  refine (Work.SSGRoute.HRec.realPlace_eq_of_isNegAt_iff (w :=
      NumberField.InfinitePlace.mk (φ.comp (algebraMap k Ω))) (w' :=
      NumberField.InfinitePlace.mk (φ'.comp (algebraMap k Ω))) hw ?_)
  intro a
  exact (isNegAt_mk_seamComp_iff k Ω c φ hφ a).trans
    (isNegAt_mk_seamComp_iff k Ω c φ' hφ' a).symm

/-- Conjugate involutions have their seam places at the same place of `k`. -/
theorem mk_seamComp_eq_of_conj (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
    [IsAlgClosure k Ω]
    (c c' : Ω ≃ₐ[k] Ω) (hc2 : c ^ 2 = 1) (hc1 : c ≠ 1) (hc2' : c' ^ 2 = 1) (hc1' : c' ≠ 1)
    (σ : Ω ≃ₐ[k] Ω) (hσ : c' = σ * c * σ⁻¹) (φ φ' : Ω →+* ℂ)
    (hφ : ∀ x : Ω, φ (c x) = starRingEnd ℂ (φ x))
    (hφ' : ∀ x : Ω, φ' (c' x) = starRingEnd ℂ (φ' x)) :
    NumberField.InfinitePlace.mk (φ.comp (algebraMap k Ω)) =
      NumberField.InfinitePlace.mk (φ'.comp (algebraMap k Ω)) := by
  have hseam : ∀ x : Ω, (φ'.comp (σ : Ω →+* Ω)) (c x) =
      starRingEnd ℂ ((φ'.comp (σ : Ω →+* Ω)) x) := by
    intro x
    have h1 : σ * c = c' * σ := by
      rw [hσ]
      group
    have h2 := congrArg (fun (e : Ω ≃ₐ[k] Ω) => (e : Ω → Ω) x) h1
    simp only [AlgEquiv.mul_apply] at h2
    show φ' (σ (c x)) = starRingEnd ℂ (φ' (σ x))
    rw [h2]
    exact hφ' (σ x)
  have hsame := mk_seamComp_eq_of_same k Ω c hc2 hc1 φ (φ'.comp (σ : Ω →+* Ω)) hφ hseam
  rw [hsame]
  have hcomp : ((φ'.comp (σ : Ω →+* Ω)).comp (algebraMap k Ω)) = φ'.comp (algebraMap k Ω) := by
    ext x
    exact congrArg φ' (σ.commutes x)
  rw [hcomp]

/-! ## Every real place of `k` is the seam place of a non-trivial involution -/

/-- For every real place `v` of `k` there is a non-trivial involution `c` of `G_k` whose seam
place `mk (φc c|_k)` is `v`. -/
theorem seamComp_exists_of_isReal (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
    [IsAlgClosure k Ω]
    (φc : (c : Ω ≃ₐ[k] Ω) → c ^ 2 = 1 → c ≠ 1 → Ω →+* ℂ)
    (hφc : ∀ (c : Ω ≃ₐ[k] Ω) (hc2 : c ^ 2 = 1) (hc1 : c ≠ 1) (x : Ω),
      φc c hc2 hc1 (c x) = starRingEnd ℂ (φc c hc2 hc1 x))
    (v : NumberField.InfinitePlace k) (hv : v.IsReal) :
    ∃ (c : Ω ≃ₐ[k] Ω) (hc2 : c ^ 2 = 1) (hc1 : c ≠ 1),
      NumberField.InfinitePlace.mk ((φc c hc2 hc1).comp (algebraMap k Ω)) = v := by
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed k
  have hζ : IsPrimitiveRoot (-1 : k) 2 := IsPrimitiveRoot.neg_one 0 (by norm_num)
  obtain ⟨c, hc2, hc1, hkum⟩ :=
    Work.SSGRoute.HRec.exists_conjInv_kummerChar_eq_zero_iff (Ω := Ω) (-1 : k) hζ v hv
  refine ⟨c, hc2, hc1, ?_⟩
  refine (Work.SSGRoute.HRec.realPlace_eq_of_isNegAt_iff (w := v) (w' :=
    NumberField.InfinitePlace.mk ((φc c hc2 hc1).comp (algebraMap k Ω))) hv ?_).symm
  intro a
  have hAC : Work.SSGRoute.ZDataTwo.IsNegAt
        (NumberField.InfinitePlace.mk ((φc c hc2 hc1).comp (algebraMap k Ω))) a ↔
      Work.SSGRoute.kummerChar (K := k) (Ω := Ω) (-1 : k) hζ a c ≠ 0 :=
    (isNegAt_mk_seamComp_iff k Ω c (φc c hc2 hc1) (hφc c hc2 hc1) a).trans
      ((Work.SSGRoute.ZDataTwo.kummerChar_eq_one_iff_not_mem_normSet (-1 : k) hζ c hc2 a).symm.trans
        (Work.SSGRoute.ZDataTwo.zmodTwo_eq_one_iff_ne_zero _))
  have hCD : Work.SSGRoute.kummerChar (K := k) (Ω := Ω) (-1 : k) hζ a c ≠ 0 ↔
      Work.SSGRoute.ZDataTwo.IsNegAt v a :=
    (hkum a).not.trans not_not
  exact hCD.symm.trans hAC.symm

/-! ## The orbit theory of the seam places -/

theorem seamPlace_orbit_theory
    (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
    [IsAlgClosure k Ω] (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    (φc : (c : Ω ≃ₐ[k] Ω) → c ^ 2 = 1 → c ≠ 1 → Ω →+* ℂ)
    (hφc : ∀ (c : Ω ≃ₐ[k] Ω) (hc2 : c ^ 2 = 1) (hc1 : c ≠ 1) (x : Ω),
      φc c hc2 hc1 (c x) = starRingEnd ℂ (φc c hc2 hc1 x))
    (C' : Finset (Ω ≃ₐ[k] Ω)) (hC'inv : ∀ c ∈ C', c ^ 2 = 1)
    (hC'rep : ∀ c : Ω ≃ₐ[k] Ω, c ^ 2 = 1 → c ≠ 1 →
      ∃ c₀ ∈ C', ∃ σ : Ω ≃ₐ[k] Ω, c = σ * c₀ * σ⁻¹)
    (hC'disj : ∀ c ∈ C', ∀ c' ∈ C', (∃ σ : Ω ≃ₐ[k] Ω, c' = σ * c * σ⁻¹) → c = c')
    (L : IntermediateField k Ω) [NumberField ↥L] [FiniteDimensional k ↥L] [IsGalois k ↥L]
    (hKL : K ≤ L) :
    (∀ (u : NK.GlobalCFT.Place ↥L), (∃ v : NumberField.InfinitePlace ↥L,
        u = NK.GlobalCFT.Place.ofInfinite v) →
      SSGRoute.PTExt.decompK (k := k) u ≠ ⊥ →
      ∃ (c : Ω ≃ₐ[k] Ω) (hc2 : c ^ 2 = 1) (hc1 : c ≠ 1), c ∈ C' ∧
        SSGRoute.res k L c ≠ 1 ∧
        ∃ γ : ↥L ≃ₐ[k] ↥L, γ • u = NK.GlobalCFT.Place.ofInfinite
          (NumberField.InfinitePlace.mk ((φc c hc2 hc1).comp (algebraMap ↥L Ω)))) ∧
    (∀ (c : Ω ≃ₐ[k] Ω) (hc2 : c ^ 2 = 1) (hc1 : c ≠ 1), c ∈ C' →
      SSGRoute.res k L c ≠ 1 →
      ∀ (c' : Ω ≃ₐ[k] Ω) (hc2' : c' ^ 2 = 1) (hc1' : c' ≠ 1), c' ∈ C' →
      SSGRoute.res k L c' ≠ 1 →
      (∃ γ : ↥L ≃ₐ[k] ↥L,
        γ • NK.GlobalCFT.Place.ofInfinite (NumberField.InfinitePlace.mk
            ((φc c hc2 hc1).comp (algebraMap ↥L Ω)))
          = NK.GlobalCFT.Place.ofInfinite (NumberField.InfinitePlace.mk
            ((φc c' hc2' hc1').comp (algebraMap ↥L Ω)))) → c = c') := by
  constructor
  · rintro u ⟨v, rfl⟩ hD
    -- `decompK` of an infinite place is its stabiliser; it is non-trivial, so `u` is ramified.
    have hstab : MulAction.stabilizer (↥L ≃ₐ[k] ↥L) v ≠ ⊥ := by
      rw [← Work.SSGRoute.PT.decompK_ofInfinite_eq (k := k) (K := ↥L) v]
      exact hD
    have hnotunr : ¬ NumberField.InfinitePlace.IsUnramified k v := by
      rw [NumberField.InfinitePlace.isUnramified_iff_stabilizer_eq_bot]
      exact hstab
    obtain ⟨hvcomplex, hvreal⟩ := NumberField.InfinitePlace.not_isUnramified_iff.mp hnotunr
    -- The base place `v₀` of `u` is real; take the involution `c₀` whose seam place is `v₀`.
    obtain ⟨c₀, hc0_2, hc0_1, hc0_eq⟩ :=
      seamComp_exists_of_isReal k Ω φc hφc (v.comap (algebraMap k ↥L)) hvreal
    -- Replace `c₀` by its representative `c₁ ∈ C'`.
    obtain ⟨c₁, hc₁mem, σ, hσ⟩ := hC'rep c₀ hc0_2 hc0_1
    have hc₁2 : c₁ ^ 2 = 1 := hC'inv c₁ hc₁mem
    have hc₁1 : c₁ ≠ 1 := by
      intro h1
      apply hc0_1
      rw [hσ, h1, mul_one, mul_inv_cancel]
    -- The seam place of `c₁` restricts to the same real place of `k` as `u`.
    have hc₁K : NumberField.InfinitePlace.mk ((φc c₁ hc₁2 hc₁1).comp (algebraMap k Ω)) =
        v.comap (algebraMap k ↥L) :=
      (mk_seamComp_eq_of_conj k Ω c₁ c₀ hc₁2 hc₁1 hc0_2 hc0_1 σ hσ
        (φc c₁ hc₁2 hc₁1) (φc c₀ hc0_2 hc0_1)
        (hφc c₁ hc₁2 hc₁1) (hφc c₀ hc0_2 hc0_1)).trans hc0_eq
    -- Hence the seam place of `c₁` at level `L` is a Galois conjugate of `u`.
    have hcomap : (NumberField.InfinitePlace.mk
          ((φc c₁ hc₁2 hc₁1).comp (algebraMap ↥L Ω))).comap (algebraMap k ↥L) =
        v.comap (algebraMap k ↥L) := by
      have hcomp : (((φc c₁ hc₁2 hc₁1).comp (algebraMap ↥L Ω)).comp (algebraMap k ↥L)) =
          (φc c₁ hc₁2 hc₁1).comp (algebraMap k Ω) := by
        ext x
        exact congrArg (φc c₁ hc₁2 hc₁1) (IsScalarTower.algebraMap_apply k ↥L Ω x)
      rw [NumberField.InfinitePlace.comap_mk, hcomp, hc₁K]
    obtain ⟨γ, hγ⟩ := NumberField.InfinitePlace.exists_smul_eq_of_comap_eq (k := k) (K := ↥L)
      (w := v) (w' := NumberField.InfinitePlace.mk
        ((φc c₁ hc₁2 hc₁1).comp (algebraMap ↥L Ω))) hcomap.symm
    have hvLcomplex : (NumberField.InfinitePlace.mk
        ((φc c₁ hc₁2 hc₁1).comp (algebraMap ↥L Ω))).IsComplex := by
      have h := (NumberField.InfinitePlace.isComplex_smul_iff (σ := γ) (w := v)).mpr hvcomplex
      rwa [hγ] at h
    refine ⟨c₁, hc₁2, hc₁1, hc₁mem, ?_, γ, ?_⟩
    · exact res_ne_one_of_seamComp_isComplex k Ω L c₁ (φc c₁ hc₁2 hc₁1)
        (hφc c₁ hc₁2 hc₁1) hvLcomplex
    · rw [NK.GlobalCFT.Place.smul_ofInfinite, hγ]
  · rintro c hc2 hc1 hcmem _ c' hc2' hc1' hc'mem _ ⟨γ, hγ⟩
    exact hC'disj c hcmem c' hc'mem
      (Work.SSGRoute.PT.wc_orbit_injective k Ω L c c' hc2 hc1 hc2' hc1'
        (φc c hc2 hc1) (φc c' hc2' hc1') (hφc c hc2 hc1) (hφc c' hc2' hc1') γ hγ)

end Work.PT
