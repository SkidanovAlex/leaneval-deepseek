import Mathlib.GroupTheory.Nilpotent
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.PicardGroup
import Mathlib.FieldTheory.Galois.Abelian
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.Polynomial.Cyclotomic.Roots
import Submission.NK.GlobalCFT.Inclusion.globalCFT_localAction
import Submission.Work.HRec.exists_inflated_of_invariant
import Submission.Work.HRec.grunwald_surjective_odd_over_same
import Submission.Work.SSGRoute.E7cOmega.card_stab_eq_of_liesOver
import Submission.Work.SSGRoute.LevelInertiaProEll.stabilizerValuationSubringAtPrime
import Submission.Work.SSGRoute.ZConstruction.exists_KConj_reps
import Submission.Work.SSGRoute.grunwald_surjective_odd
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

open NumberField
open scoped Pointwise

namespace Work.SSGRoute.Sha2Lib

set_option maxHeartbeats 40000000

theorem exists_heightOneSpectrum (k : Type) [Field k] [NumberField k] :
    Nonempty (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers k)) :=
  let ⟨M, hM⟩ := Ideal.exists_maximal (NumberField.RingOfIntegers k)
  ⟨⟨M, hM.isPrime,
    Ring.ne_bot_of_isMaximal_of_not_isField hM (NumberField.RingOfIntegers.not_isField k)⟩⟩

/-- **The cyclotomic base `K = k(ζ_q)`.**  There is a primitive `q`-th root of unity `ζ` in `Ω`,
and `k⟮ζ⟯` is a finite Galois number field over `k` whose Galois group is coprime to `q`. -/

theorem cycloSetup (q : ℕ) (hq : q.Prime) (k Ω : Type) [Field k] [NumberField k] [Field Ω]
    [Algebra k Ω] [IsAlgClosure k Ω] :
    ∃ ζ : Ω, IsPrimitiveRoot ζ q ∧
      (∃ (_ : FiniteDimensional k ↥(IntermediateField.adjoin k {ζ}))
         (_ : NumberField ↥(IntermediateField.adjoin k {ζ}))
         (_ : IsGalois k ↥(IntermediateField.adjoin k {ζ})),
        Nat.Coprime (Nat.card (↥(IntermediateField.adjoin k {ζ}) ≃ₐ[k]
          ↥(IntermediateField.adjoin k {ζ}))) q) := by
  classical
  haveI hNZq : NeZero q := ⟨hq.ne_zero⟩
  haveI hSepClosure : IsSepClosure k Ω := IsSepClosure.of_isAlgClosure_of_perfectField k Ω
  haveI hSepClosed : IsSepClosed Ω := IsSepClosure.sep_closed k
  haveI hAlg : Algebra.IsAlgebraic k Ω := IsAlgClosure.isAlgebraic
  haveI hcharΩ : CharZero Ω :=
    charZero_of_injective_algebraMap (RingHom.injective (algebraMap k Ω))
  haveI hqcast : NeZero ((q : ℕ) : Ω) := ⟨Nat.cast_ne_zero.mpr hq.ne_zero⟩
  obtain ⟨ζ, hζ⟩ := NK.LocalAnabelian.exists_isPrimitiveRoot_of_isSepClosed (K := Ω) (n := q)
  refine ⟨ζ, hζ, ?_⟩
  have hInt : IsIntegral k ζ := isAlgebraic_iff_isIntegral.mp (Algebra.IsAlgebraic.isAlgebraic ζ)
  haveI hfd : FiniteDimensional k ↥(IntermediateField.adjoin k {ζ}) :=
    IntermediateField.adjoin.finiteDimensional hInt
  haveI hnf : NumberField ↥(IntermediateField.adjoin k {ζ}) := NumberField.of_module_finite k _
  have hrootSet : IntermediateField.adjoin k ({ζ} : Set Ω) =
      IntermediateField.adjoin k ((Polynomial.X ^ q - 1 : Polynomial k).rootSet Ω) := by
    have hpne : (Polynomial.X ^ q - 1 : Polynomial k) ≠ 0 := by
      simpa using (Polynomial.monic_X_pow_sub_C (1 : k) hq.ne_zero).ne_zero
    refine le_antisymm ?_ ?_
    · refine IntermediateField.adjoin_le_iff.mpr ?_
      intro y hy
      rw [Set.mem_singleton_iff] at hy
      subst hy
      refine IntermediateField.subset_adjoin k _ (Polynomial.mem_rootSet.mpr ⟨hpne, ?_⟩)
      rw [Polynomial.aeval_sub, Polynomial.aeval_one, map_pow, Polynomial.aeval_X,
        hζ.pow_eq_one, sub_self]
    · refine IntermediateField.adjoin_le_iff.mpr ?_
      intro y hy
      obtain ⟨-, hzero⟩ := Polynomial.mem_rootSet.mp hy
      have hyq : y ^ q = 1 := by
        rw [Polynomial.aeval_sub, Polynomial.aeval_one, map_pow, Polynomial.aeval_X] at hzero
        exact sub_eq_zero.mp hzero
      obtain ⟨i, -, hi⟩ := hζ.eq_pow_of_pow_eq_one hyq
      rw [← hi]
      exact pow_mem (IntermediateField.subset_adjoin k ({ζ} : Set Ω) (Set.mem_singleton ζ)) i
  haveI hgal : IsGalois k ↥(IntermediateField.adjoin k {ζ}) := by
    have hsep : (Polynomial.X ^ q - 1 : Polynomial k).Separable :=
      Polynomial.X_pow_sub_one_separable_iff.mpr (Nat.cast_ne_zero.mpr hq.ne_zero)
    have hsp : (Polynomial.X ^ q - 1 : Polynomial Ω).Splits := Polynomial.X_pow_sub_one_splits hζ
    have hsplit : ((Polynomial.X ^ q - 1 : Polynomial k).map (algebraMap k Ω)).Splits := by
      simpa only [Polynomial.map_sub, Polynomial.map_pow, Polynomial.map_X, Polynomial.map_one]
        using hsp
    haveI : Polynomial.IsSplittingField k
        ↥(IntermediateField.adjoin k ((Polynomial.X ^ q - 1 : Polynomial k).rootSet Ω))
        (Polynomial.X ^ q - 1) :=
      IntermediateField.adjoin_rootSet_isSplittingField hsplit
    haveI hgal' : IsGalois k
        ↥(IntermediateField.adjoin k ((Polynomial.X ^ q - 1 : Polynomial k).rootSet Ω)) :=
      IsGalois.of_separable_splitting_field hsep
    exact IsGalois.of_algEquiv (IntermediateField.equivOfEq hrootSet.symm)
  refine ⟨hfd, hnf, hgal, ?_⟩
  have hcard : Nat.card (↥(IntermediateField.adjoin k {ζ}) ≃ₐ[k]
      ↥(IntermediateField.adjoin k {ζ})) = (minpoly k ζ).natDegree := by
    rw [IsGalois.card_aut_eq_finrank k ↥(IntermediateField.adjoin k {ζ}),
      IntermediateField.adjoin.finrank hInt]
  rw [hcard]
  refine (hq.coprime_iff_not_dvd.mpr (fun hdvd => ?_)).symm
  have hroot : (Polynomial.aeval ζ) (Polynomial.cyclotomic q k) = 0 := by
    have h : (Polynomial.aeval ζ) (Polynomial.cyclotomic q Ω) = 0 := hζ.isRoot_cyclotomic hq.pos
    rw [← Polynomial.map_cyclotomic q (algebraMap k Ω)] at h
    rw [Polynomial.aeval_map_algebraMap Ω ζ (Polynomial.cyclotomic q k)] at h
    exact h
  have hdvd' : minpoly k ζ ∣ Polynomial.cyclotomic q k := minpoly.dvd k ζ hroot
  have hle : (minpoly k ζ).natDegree ≤ q - 1 := by
    calc (minpoly k ζ).natDegree ≤ (Polynomial.cyclotomic q k).natDegree :=
          Polynomial.natDegree_le_of_dvd hdvd' (Polynomial.cyclotomic_ne_zero q k)
      _ = q - 1 := by rw [Polynomial.natDegree_cyclotomic, Nat.totient_prime hq]
  have hpos : 0 < (minpoly k ζ).natDegree := minpoly.natDegree_pos hInt
  have h1 : q ≤ (minpoly k ζ).natDegree := Nat.le_of_dvd hpos hdvd
  omega


def conjN {G : Type*} [Group G] (N : Subgroup G) [N.Normal] (g : G) (n : N) : N :=
  ⟨g * (n : G) * g⁻¹, Subgroup.Normal.conj_mem (inferInstance : N.Normal) (n : G) n.2 g⟩

@[simp] lemma conjN_coe {G : Type*} [Group G] (N : Subgroup G) [N.Normal] (g : G) (n : N) :
    ((conjN N g n : N) : G) = g * (n : G) * g⁻¹ := rfl

lemma conjN_mul {G : Type*} [Group G] (N : Subgroup G) [N.Normal] (g : G) (a b : N) :
    conjN N g (a * b) = conjN N g a * conjN N g b :=
  Subtype.ext (by simp [conjN, mul_assoc])

lemma conjN_conj {G : Type*} [Group G] (N : Subgroup G) [N.Normal] (g h : G) (n : N) :
    conjN N g (conjN N h n) = conjN N (g * h) n :=
  Subtype.ext (by simp [conjN, mul_assoc])

lemma conjN_conjN {G : Type*} [Group G] (N : Subgroup G) [N.Normal] (a : G) (m n : N) :
    conjN N a (conjN N m n) = conjN N (conjN N a m) (conjN N a n) :=
  Subtype.ext (by simp [conjN, mul_assoc])

/-- **The conjugation average of an additive map is additive and invariant.** -/
theorem conjAvg_aux (q : ℕ) (G : Type) [Group G] (N : Subgroup G) [N.Normal]
    [Fintype (G ⧸ N)] (z : N → ZMod q) (hzadd : ∀ a b : N, z (a * b) = z a + z b)
    (sec : G ⧸ N → G) (hsec : ∀ x, QuotientGroup.mk (sec x) = x) :
    (∀ a b : N, (∑ x : G ⧸ N, z (conjN N (sec x) (a * b)))
        = (∑ x : G ⧸ N, z (conjN N (sec x) a))
          + (∑ x : G ⧸ N, z (conjN N (sec x) b))) ∧
    (∀ (σ : G) (δ : N),
        (∑ x : G ⧸ N, z (conjN N (sec x) (conjN N σ δ)))
          = (∑ x : G ⧸ N, z (conjN N (sec x) δ))) := by
  classical
  have hz1 : z 1 = 0 := by
    have h := hzadd 1 1
    rw [mul_one] at h
    exact add_left_cancel (h.symm.trans (add_zero (z 1)).symm)
  have hzinv : ∀ a : N, z a⁻¹ = - z a := by
    intro a
    have h := hzadd a a⁻¹
    rw [mul_inv_cancel, hz1] at h
    exact eq_neg_iff_add_eq_zero.mpr (by rw [add_comm]; exact h.symm)
  have hconjN : ∀ (n δ : N), z (conjN N n δ) = z δ := by
    intro n δ
    have h1 : conjN N n δ = n * δ * n⁻¹ := Subtype.ext (by simp [conjN])
    rw [h1, hzadd, hzadd, hzinv]
    abel
  constructor
  · intro a b
    rw [Finset.sum_congr rfl (fun x _ => by rw [conjN_mul, hzadd]), Finset.sum_add_distrib]
  · intro σ δ
    have hkey : ∀ x : G ⧸ N, z (conjN N (sec x) (conjN N σ δ))
        = z (conjN N (sec (QuotientGroup.mk (sec x * σ))) δ) := by
      intro x
      have hmem : (sec (QuotientGroup.mk (sec x * σ)))⁻¹ * (sec x * σ) ∈ N := by
        rw [← QuotientGroup.eq_one_iff]
        change (QuotientGroup.mk ((sec (QuotientGroup.mk (sec x * σ)))⁻¹ * (sec x * σ)) :
          G ⧸ N) = 1
        rw [QuotientGroup.mk_mul, QuotientGroup.mk_inv, QuotientGroup.mk_mul, hsec, hsec,
          inv_mul_cancel]
      let n : N := ⟨(sec (QuotientGroup.mk (sec x * σ)))⁻¹ * (sec x * σ), hmem⟩
      have hn : (n : G) = (sec (QuotientGroup.mk (sec x * σ)))⁻¹ * (sec x * σ) := rfl
      have hstep : conjN N (sec x * σ) δ
          = conjN N (sec (QuotientGroup.mk (sec x * σ))) (conjN N n δ) := by
        refine Subtype.ext ?_
        simp only [conjN_coe, hn]
        group
      calc z (conjN N (sec x) (conjN N σ δ))
          = z (conjN N (sec x * σ) δ) := by rw [conjN_conj]
        _ = z (conjN N (sec (QuotientGroup.mk (sec x * σ))) (conjN N n δ)) := by rw [hstep]
        _ = z (conjN N (conjN N (sec (QuotientGroup.mk (sec x * σ))) n)
                (conjN N (sec (QuotientGroup.mk (sec x * σ))) δ)) := by rw [conjN_conjN]
        _ = z (conjN N (sec (QuotientGroup.mk (sec x * σ))) δ) := by rw [hconjN]
    rw [Finset.sum_congr rfl (fun x _ => hkey x)]
    refine Fintype.sum_equiv
      { toFun := fun x : G ⧸ N => x * QuotientGroup.mk σ
        invFun := fun x : G ⧸ N => x * (QuotientGroup.mk σ)⁻¹
        left_inv := fun x => by simp
        right_inv := fun x => by simp }
      (fun x : G ⧸ N => z (conjN N (sec (QuotientGroup.mk (sec x * σ))) δ))
      (fun y : G ⧸ N => z (conjN N (sec y) δ)) (fun x => ?_)
    show z (conjN N (sec (QuotientGroup.mk (sec x * σ))) δ)
        = z (conjN N (sec (x * QuotientGroup.mk σ)) δ)
    congr 2
    rw [QuotientGroup.mk_mul, hsec]


structure PlaceData (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
    (K : IntermediateField k Ω)
    (S : Finset (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers k))) where
  T : Finset (ValuationSubring Ω)
  base : {v // v ∈ S} → ValuationSubring Ω
  vOf : {P // P ∈ T} → {v // v ∈ S}
  u : {P // P ∈ T} → Ω ≃ₐ[k] Ω
  hTfin : ∀ P ∈ T, SSGRoute.IsFinPlace k P
  hTinj : ∀ P Q : {P // P ∈ T}, (P : ValuationSubring Ω).comap (algebraMap ↥K Ω) =
    (Q : ValuationSubring Ω).comap (algebraMap ↥K Ω) → P = Q
  hbase_mem : ∀ v : {v // v ∈ S}, base v ∈ T
  hbase_comap : ∀ v : {v // v ∈ S}, (base v).comap (algebraMap k Ω) =
    IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime k
      (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers k))
  hu : ∀ P : {P // P ∈ T}, u P • (P : ValuationSubring Ω) = base (vOf P)
  hcover : ∀ v : {v // v ∈ S}, ∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
    B.comap (algebraMap k Ω) = (base v).comap (algebraMap k Ω) →
      ∃ P ∈ T, Work.SSGRoute.KConj K P B

/-- The local datum at a finite place. -/
structure LocalChar (q : ℕ) (k Ω : Type) [Field k] [Field Ω] [Algebra k Ω]
    (K : IntermediateField k Ω) (P : ValuationSubring Ω) where
  f : (Ω ≃ₐ[k] Ω) → ZMod q
  hadd : ∀ g ∈ SSGRoute.decomp k P ⊓ K.fixingSubgroup,
    ∀ h ∈ SSGRoute.decomp k P ⊓ K.fixingSubgroup, f (g * h) = f g + f h
  hcont : ∃ U : Subgroup (Ω ≃ₐ[k] Ω), IsOpen (U : Set (Ω ≃ₐ[k] Ω)) ∧
    ∀ x ∈ U, x ∈ SSGRoute.decomp k P ⊓ K.fixingSubgroup → f x = 0
  hne : ∃ δ ∈ SSGRoute.decomp k P ⊓ K.fixingSubgroup, f δ ≠ 0
  hinv : ∀ (σ : Ω ≃ₐ[k] Ω), σ ∈ SSGRoute.decomp k P →
    ∀ δ ∈ SSGRoute.decomp k P ⊓ K.fixingSubgroup, f (σ * δ * σ⁻¹) = f δ

/-- **The place bookkeeping** (delegated node). -/
theorem placeData_nonempty (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
    [IsAlgClosure k Ω] (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    (S : Finset (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers k))) :
    Nonempty (PlaceData k Ω K S) := by
  classical
  haveI hgalΩ : IsGalois k Ω := inferInstance
  haveI hgalKΩ : IsGalois ↥K Ω := by
    haveI : IsAlgClosure ↥K Ω := ⟨IsAlgClosure.isAlgClosed k, inferInstance⟩
    exact IsAlgClosure.isGalois ↥K Ω
  -- a chosen place of `Ω` above each `v ∈ S`
  have hplace : ∀ v : {v // v ∈ S}, ∃ A : ValuationSubring Ω,
      SSGRoute.IsFinPlace k A ∧ A.comap (algebraMap k Ω) =
        IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime k
          (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers k)) := by
    intro v
    obtain ⟨A, hA⟩ := Commons.RingTheory.Valuation.exists_valuationSubring_comap_eq
      (K := k) (L := Ω)
      (IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime k
        (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers k)))
    refine ⟨A, ?_, hA⟩
    rw [SSGRoute.IsFinPlace, hA]
    exact Commons.RingTheory.Valuation.valuationSubringAtPrime_ne_top
      (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers k))
  choose A0 hA0fin hA0comap using hplace
  let SΩ : Finset (ValuationSubring Ω) := Finset.univ.image A0
  have hSΩfin : ∀ A ∈ SΩ, SSGRoute.IsFinPlace k A := by
    intro A hA
    obtain ⟨v, -, rfl⟩ := Finset.mem_image.mp hA
    exact hA0fin v
  -- one representative per level-`K` class
  obtain ⟨T, hTfin, hTdisj, hTconj, hTcov⟩ :=
    Work.SSGRoute.ZConstruction.exists_KConj_reps K SΩ hSΩfin
  have hA0mem : ∀ v : {v // v ∈ S}, A0 v ∈ SΩ := fun v =>
    Finset.mem_image.mpr ⟨v, Finset.mem_univ _, rfl⟩
  -- for each `v` a representative above `A0 v`
  have hbase : ∀ v : {v // v ∈ S}, ∃ P : ValuationSubring Ω,
      P ∈ T ∧ Work.SSGRoute.KConj K P (A0 v) := fun v =>
    hTcov (A0 v) ⟨A0 v, hA0mem v, SSGRoute.isConjPlace_refl (k := k) (A0 v)⟩
  choose base hbasemem hbaseconj using hbase
  have hbasecomap : ∀ v : {v // v ∈ S},
      (base v).comap (algebraMap k Ω) = (A0 v).comap (algebraMap k Ω) := by
    intro v
    obtain ⟨τ, -, hτP⟩ := hbaseconj v
    rw [← hτP, SSGRoute.comap_algebraMap_smul]
  -- the transport elements
  have hu : ∀ P : {P // P ∈ T}, ∃ v : {v // v ∈ S}, ∃ uu : Ω ≃ₐ[k] Ω,
      uu • (P : ValuationSubring Ω) = base v := by
    intro P
    obtain ⟨A, hAΩ, hconj⟩ := hTconj P P.2
    obtain ⟨v, -, rfl⟩ := Finset.mem_image.mp hAΩ
    obtain ⟨uu, huu⟩ := SSGRoute.isConjPlace_symm hconj
    obtain ⟨τ, -, hτb⟩ := hbaseconj v
    exact ⟨v, τ⁻¹ * uu, by rw [mul_smul, huu, ← hτb, inv_smul_smul]⟩
  choose vOf u hu_eq using hu
  refine ⟨⟨T, base, vOf, u, hTfin, ?_, hbasemem, ?_, hu_eq, ?_⟩⟩
  · -- injectivity of the restriction to `K`
    intro P Q hPQ
    have hconj : Work.SSGRoute.KConj K (P : ValuationSubring Ω) (Q : ValuationSubring Ω) := by
      obtain ⟨σ, hσ⟩ := Commons.RingTheory.Valuation.exists_smul_eq_of_comap_eq
        (F := ↥K) (E := Ω) (A := (P : ValuationSubring Ω)) (B := (Q : ValuationSubring Ω)) hPQ
      refine ⟨AlgEquiv.restrictScalars k σ, ?_, ?_⟩
      · rw [IntermediateField.mem_fixingSubgroup_iff]
        intro x hx
        exact σ.commutes ⟨x, hx⟩
      · exact hσ
    have := hTdisj P P.2 Q Q.2 hconj
    exact Subtype.ext this
  · -- the base places lie over the given primes
    intro v
    rw [hbasecomap v]
    exact hA0comap v
  · -- the cover clause
    intro v B hBfin hBcomap
    have hconj : SSGRoute.IsConjPlace k (A0 v) B := by
      obtain ⟨σ, hσ⟩ := Commons.RingTheory.Valuation.exists_smul_eq_of_comap_eq
        (F := k) (E := Ω) (A := A0 v) (B := B) ((hBcomap.trans (hbasecomap v)).symm)
      exact ⟨σ, hσ⟩
    exact hTcov B ⟨A0 v, hA0mem v, hconj⟩

/-- The place bookkeeping data (chosen representative of the existential). -/
noncomputable def placeData_aux (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
    [IsAlgClosure k Ω] (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    (S : Finset (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers k))) :
    PlaceData k Ω K S :=
  Classical.choice (placeData_nonempty k Ω K S)


theorem packageLevel_aux (q : ℕ) (hq : q.Prime)
    (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω]
    (S : Finset (ValuationSubring Ω))
    (χ : (Ω ≃ₐ[k] Ω) → ZMod q)
    (hadd : ∀ a b : Ω ≃ₐ[k] Ω, χ (a * b) = χ a + χ b)
    (hcont : ∃ U : Subgroup (Ω ≃ₐ[k] Ω), IsOpen (U : Set (Ω ≃ₐ[k] Ω)) ∧ ∀ x ∈ U, χ x = 0)
    (hne : ∃ x : Ω ≃ₐ[k] Ω, χ x ≠ 0)
    (hnon : ∀ A ∈ S, ∃ δ : Ω ≃ₐ[k] Ω, δ ∈ SSGRoute.decomp k A ∧ χ δ ≠ 0) :
    ∃ M : IntermediateField k Ω, ∃ (_ : FiniteDimensional k ↥M) (_ : NumberField ↥M)
      (_ : IsGalois k ↥M),
      IsCyclic (↥M ≃ₐ[k] ↥M) ∧ Nat.card (↥M ≃ₐ[k] ↥M) = q ∧
      (∀ A ∈ S, ∃ δ : Ω ≃ₐ[k] Ω, δ ∈ SSGRoute.decomp k A ∧ δ ∉ M.fixingSubgroup) := by
  classical
  haveI hFact : Fact q.Prime := ⟨hq⟩
  haveI hNZ : NeZero q := ⟨hq.ne_zero⟩
  haveI hgalΩ : IsGalois k Ω := inferInstance
  -- elementary facts about the additive character
  have hχ1 : χ 1 = 0 := by
    have h := hadd 1 1
    rw [mul_one] at h
    exact add_left_cancel (h.symm.trans (add_zero (χ 1)).symm)
  have hχinv : ∀ a : Ω ≃ₐ[k] Ω, χ a⁻¹ = - χ a := by
    intro a
    have h := hadd a a⁻¹
    rw [mul_inv_cancel, hχ1] at h
    exact eq_neg_iff_add_eq_zero.mpr (by rw [add_comm]; exact h.symm)
  have hχpow : ∀ (x : Ω ≃ₐ[k] Ω) (m : ℕ), χ (x ^ m) = (m : ZMod q) * χ x := by
    intro x m
    induction m with
    | zero => rw [pow_zero, hχ1, Nat.cast_zero, zero_mul]
    | succ k ih => rw [pow_succ, hadd, ih, Nat.cast_succ, add_mul, one_mul]
  have hχsurj : Function.Surjective χ := by
    obtain ⟨x, hx⟩ := hne
    intro t
    refine ⟨x ^ (t * (χ x)⁻¹).val, ?_⟩
    rw [hχpow, ZMod.natCast_zmod_val, mul_assoc, inv_mul_cancel₀ hx, mul_one]
  -- the character as a multiplicative homomorphism
  let ψ : (Ω ≃ₐ[k] Ω) →* Multiplicative (ZMod q) :=
    { toFun := fun σ => Multiplicative.ofAdd (χ σ)
      map_one' := by rw [hχ1]; rfl
      map_mul' := fun a b => by rw [hadd]; rfl }
  have hψ : ∀ σ, ψ σ = Multiplicative.ofAdd (χ σ) := fun σ => rfl
  have hofAdd1 : ∀ a : ZMod q, Multiplicative.ofAdd a = 1 ↔ a = 0 := by
    intro a
    constructor
    · intro h
      have h2 := congrArg (⇑Multiplicative.toAdd) h
      simpa using h2
    · intro h
      rw [h]
      rfl
  have hker_mem : ∀ σ : Ω ≃ₐ[k] Ω, σ ∈ ψ.ker ↔ χ σ = 0 := by
    intro σ
    change ψ σ = 1 ↔ χ σ = 0
    rw [hψ, hofAdd1]
  have hsurjψ : Function.Surjective ψ := by
    intro y
    obtain ⟨g, hg⟩ := hχsurj (Multiplicative.toAdd y)
    refine ⟨g, ?_⟩
    rw [hψ, hg]
    exact Multiplicative.ofAdd.apply_symm_apply y
  have hopen : IsOpen (ψ.ker : Set (Ω ≃ₐ[k] Ω)) := by
    obtain ⟨U, hUo, hU⟩ := hcont
    refine Subgroup.isOpen_mono (fun x hx => ?_) hUo
    exact (hker_mem x).mpr (hU x hx)
  have hclosed : IsClosed (ψ.ker : Set (Ω ≃ₐ[k] Ω)) := Subgroup.isClosed_of_isOpen ψ.ker hopen
  -- the level
  let M : IntermediateField k Ω := IntermediateField.fixedField ψ.ker
  have hfix : M.fixingSubgroup = ψ.ker :=
    @InfiniteGalois.fixingSubgroup_fixedField k Ω _ _ _ (⟨ψ.ker, hclosed⟩ : ClosedSubgroup _) hgalΩ
  have hfd : FiniteDimensional k M :=
    (@InfiniteGalois.isOpen_iff_finite k Ω _ _ _ M hgalΩ).mp (by rw [hfix]; exact hopen)
  haveI hgalM : IsGalois k M :=
    @IsGalois.of_fixedField_normal_subgroup k Ω _ _ _ _ ψ.ker (MonoidHom.normal_ker ψ)
  haveI hnfM : NumberField ↥M := NumberField.of_module_finite k ↥M
  -- `Gal(M/k) ≃ G ⧸ ker ψ ≃ ψ.range`
  haveI hnH : (⟨ψ.ker, hclosed⟩ : ClosedSubgroup (Ω ≃ₐ[k] Ω)).Normal := MonoidHom.normal_ker ψ
  let na := @InfiniteGalois.normalAutEquivQuotient k Ω _ _ _ hgalΩ ⟨ψ.ker, hclosed⟩ hnH
  let e : (ψ.range) ≃* (↥M ≃ₐ[k] ↥M) :=
    (QuotientGroup.quotientKerEquivRange ψ).symm.trans na
  -- `Multiplicative (ZMod q)` is cyclic
  haveI hcycZ : IsCyclic (Multiplicative (ZMod q)) := by
    refine ⟨Multiplicative.ofAdd 1, ?_⟩
    intro y
    refine ⟨((Multiplicative.toAdd y).val : ℤ), ?_⟩
    change (Multiplicative.ofAdd 1 : Multiplicative (ZMod q)) ^
      (((Multiplicative.toAdd y).val : ℕ) : ℤ) = y
    have hnat : (Multiplicative.ofAdd 1 : Multiplicative (ZMod q)) ^ (Multiplicative.toAdd y).val
        = Multiplicative.ofAdd (((Multiplicative.toAdd y).val : ℕ) • (1 : ZMod q)) := by
      induction (Multiplicative.toAdd y).val with
      | zero => rw [pow_zero, zero_nsmul]; rfl
      | succ k ih => rw [pow_succ, ih, succ_nsmul]; rfl
    rw [zpow_natCast, hnat, nsmul_eq_mul, mul_one, ZMod.natCast_zmod_val]
    exact Multiplicative.ofAdd.apply_symm_apply y
  haveI hcycRange : IsCyclic ψ.range := Subgroup.isCyclic ψ.range
  haveI hcycM : IsCyclic (↥M ≃ₐ[k] ↥M) := by
    obtain ⟨g, hg⟩ := hcycRange
    refine ⟨e g, ?_⟩
    intro x
    obtain ⟨n, hn⟩ := hg (e.symm x)
    have hn' : g ^ n = e.symm x := hn
    refine ⟨n, ?_⟩
    show (e g) ^ n = x
    have h2 : (e g) ^ n = e (g ^ n) := (map_zpow (e : (ψ.range) →* (↥M ≃ₐ[k] ↥M)) g n).symm
    rw [h2, hn', MulEquiv.apply_symm_apply]
  have hrange_card : Nat.card (ψ.range) = q := by
    have hdvd : Nat.card (ψ.range) ∣ q := by
      have h1 : Nat.card (ψ.range) ∣ Nat.card (Multiplicative (ZMod q)) :=
        Subgroup.card_subgroup_dvd_card ψ.range
      have h2 : Nat.card (Multiplicative (ZMod q)) = q := by
        rw [Nat.card_eq_fintype_card,
          ← Fintype.card_congr (Multiplicative.ofAdd : ZMod q ≃ Multiplicative (ZMod q)),
          ZMod.card]
      rwa [h2] at h1
    have hne1 : Nat.card (ψ.range) ≠ 1 := by
      obtain ⟨x, hx⟩ := hne
      intro h1
      have hbot : ψ.range = ⊥ := Subgroup.card_eq_one.mp h1
      have hxmem : ψ x ∈ ψ.range := MonoidHom.mem_range.mpr ⟨x, rfl⟩
      rw [hbot] at hxmem
      have h2 : ψ x = 1 := by simpa using hxmem
      exact hx ((hker_mem x).mp h2)
    rcases hq.eq_one_or_self_of_dvd _ hdvd with h | h
    · exact absurd h hne1
    · exact h
  have hcard : Nat.card (↥M ≃ₐ[k] ↥M) = q := by
    rw [← hrange_card]
    exact (Nat.card_congr e.toEquiv).symm
  refine ⟨M, hfd, hnfM, hgalM, hcycM, hcard, ?_⟩
  intro A hA
  obtain ⟨δ, hδmem, hδne⟩ := hnon A hA
  refine ⟨δ, hδmem, fun hcon => hδne ?_⟩
  exact (hker_mem δ).mp (by rw [← hfix]; exact hcon)

/-- **Prime degree level: one non-split place forces `q ∣ |Stab|` at every place above it.** -/
theorem dvd_card_stabilizer_of_nontrivial (q : ℕ) (hq : q.Prime)
    (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω]
    (M : IntermediateField k Ω) [FiniteDimensional k ↥M] [NumberField ↥M] [IsGalois k ↥M]
    (hcard : Nat.card (↥M ≃ₐ[k] ↥M) = q)
    (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers k))
    (hnontriv : ∃ w : NK.GlobalCFT.Place ↥M,
      NK.GlobalCFT.Place.LiesOver w (NK.GlobalCFT.Place.ofFinite v) ∧
        MulAction.stabilizer (↥M ≃ₐ[k] ↥M) w ≠ ⊥) :
    ∀ w : NK.GlobalCFT.Place ↥M,
      NK.GlobalCFT.Place.LiesOver w (NK.GlobalCFT.Place.ofFinite v) →
        q ∣ Nat.card (MulAction.stabilizer (↥M ≃ₐ[k] ↥M) w) := by
  intro w hw
  obtain ⟨w₀, hw₀, hne⟩ := hnontriv
  haveI : Finite (↥M ≃ₐ[k] ↥M) :=
    Nat.finite_of_card_ne_zero (by rw [hcard]; exact hq.ne_zero)
  have heq : Nat.card (MulAction.stabilizer (↥M ≃ₐ[k] ↥M) w)
      = Nat.card (MulAction.stabilizer (↥M ≃ₐ[k] ↥M) w₀) :=
    Work.SSGRoute.E7cOmega.card_stab_eq_of_liesOver (k := k) (K := k) ↥M
      (NK.GlobalCFT.Place.ofFinite v) w w₀ hw hw₀
  have hdvd : Nat.card (MulAction.stabilizer (↥M ≃ₐ[k] ↥M) w₀) ∣ q := by
    rw [← hcard]
    exact Subgroup.card_subgroup_dvd_card _
  have hne1 : Nat.card (MulAction.stabilizer (↥M ≃ₐ[k] ↥M) w₀) ≠ 1 := fun h1 =>
    hne (Subgroup.card_eq_one.mp h1)
  rcases hq.eq_one_or_self_of_dvd _ hdvd with h | h
  · exact absurd h hne1
  · rw [heq, h]

/-- **The stabiliser bridge** (delegated node). -/
theorem stabBridge_aux (q : ℕ) (hq : q.Prime) (k Ω : Type) [Field k] [NumberField k] [Field Ω]
    [Algebra k Ω] [IsAlgClosure k Ω]
    (M : IntermediateField k Ω) [FiniteDimensional k ↥M] [NumberField ↥M] [IsGalois k ↥M]
    (hcard : Nat.card (↥M ≃ₐ[k] ↥M) = q)
    (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers k))
    (A : ValuationSubring Ω) (hAfin : SSGRoute.IsFinPlace k A)
    (hAover : A.comap (algebraMap k Ω) =
      IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime k v)
    (hnonsplit : ∃ δ : Ω ≃ₐ[k] Ω, δ ∈ SSGRoute.decomp k A ∧ δ ∉ M.fixingSubgroup) :
    ∀ w : NK.GlobalCFT.Place ↥M, NK.GlobalCFT.Place.LiesOver w
      (NK.GlobalCFT.Place.ofFinite v) →
      q ∣ Nat.card (MulAction.stabilizer (↥M ≃ₐ[k] ↥M) w) := by
  classical
  -- the place of `M` induced by `A`
  have hBne : A.comap (algebraMap ↥M Ω) ≠ ⊤ := by
    intro h
    have h2 : (A.comap (algebraMap ↥M Ω)).comap (algebraMap k ↥M) = ⊤ := by
      rw [h]; ext x; simp [ValuationSubring.mem_comap]
    rw [ValuationSubring.comap_comap, ← IsScalarTower.algebraMap_eq k ↥M Ω, hAover] at h2
    exact Commons.RingTheory.Valuation.valuationSubringAtPrime_ne_top v h2
  obtain ⟨P, hP⟩ := Commons.RingTheory.Valuation.exists_heightOneSpectrum_eq_valuationSubringAtPrime
      (L := ↥M) (A.comap (algebraMap ↥M Ω)) hBne
      (Commons.NumberTheory.NumberField.ringOfIntegers_le_of_valuationSubring _)
  have hunder : P.asIdeal.under (NumberField.RingOfIntegers k) = v.asIdeal := by
    let Q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers k) :=
      ⟨P.asIdeal.under (NumberField.RingOfIntegers k), inferInstance,
        Ideal.under_ne_bot _ P.ne_bot⟩
    have h1 : (IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime ↥M P).comap
        (algebraMap k ↥M) = IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime k Q :=
      Commons.RingTheory.Valuation.comap_valuationSubringAtPrime Q P (Ideal.over_under P.asIdeal)
    have h2 : (IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime ↥M P).comap
        (algebraMap k ↥M) = IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime k v := by
      rw [← hP, ValuationSubring.comap_comap, ← IsScalarTower.algebraMap_eq k ↥M Ω, hAover]
    have hQv : Q = v :=
      Commons.RingTheory.Valuation.valuationSubringAtPrime_injective (h1.symm.trans h2)
    show P.asIdeal.under (NumberField.RingOfIntegers k) = v.asIdeal
    rw [← show Q.asIdeal = P.asIdeal.under (NumberField.RingOfIntegers k) from rfl, ← hQv]
  have hlies : NK.GlobalCFT.Place.LiesOver (NK.GlobalCFT.Place.ofFinite P)
      (NK.GlobalCFT.Place.ofFinite v) :=
    NK.GlobalCFT.Place.liesOver_ofFinite (hunder ▸ Ideal.over_under P.asIdeal)
  -- the restriction of `δ` to `M`
  obtain ⟨δ, hδmem, hδne⟩ := hnonsplit
  haveI hnorm : Normal k ↥M := (isGalois_iff.mp (inferInstance : IsGalois k ↥M)).2
  let δM : ↥M ≃ₐ[k] ↥M := AlgEquiv.restrictNormalHom ↥M δ
  have hδM_ne : δM ≠ 1 := by
    intro h1
    refine hδne ?_
    rw [← IntermediateField.restrictNormalHom_ker M]
    exact MonoidHom.mem_ker.mpr h1
  have hδA : δ • A = A := MulAction.mem_stabilizer_iff.mp hδmem
  have hδM_comap : (δ • A).comap (algebraMap ↥M Ω) =
      δM • (A.comap (algebraMap ↥M Ω)) :=
    Commons.FieldTheory.Galois.comap_smul_eq_restrictNormalHom_smul A δ M
  have hfixV : δM • (IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime ↥M P) =
      IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime ↥M P := by
    rw [← hP, ← hδM_comap, hδA]
  have hstabV : δM ∈ MulAction.stabilizer (↥M ≃ₐ[k] ↥M)
      (IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime ↥M P) :=
    MulAction.mem_stabilizer_iff.mpr hfixV
  have hstabI : δM ∈ MulAction.stabilizer (↥M ≃ₐ[k] ↥M) P.asIdeal := by
    rw [← Work.SSGRoute.LevelInertiaProEll.stabilizerValuationSubringAtPrime (K := k) P]
    exact hstabV
  have hstabP : δM ∈ MulAction.stabilizer (↥M ≃ₐ[k] ↥M) (NK.GlobalCFT.Place.ofFinite P) := by
    have hstab_eq : MulAction.stabilizer (↥M ≃ₐ[k] ↥M) (NK.GlobalCFT.Place.ofFinite P)
        = MulAction.stabilizer (↥M ≃ₐ[k] ↥M) P.asIdeal := by
      ext σ
      rw [MulAction.mem_stabilizer_iff, MulAction.mem_stabilizer_iff,
        NK.GlobalCFT.Place.smul_ofFinite, NK.GlobalCFT.Place.ofFinite_inj,
        IsDedekindDomain.HeightOneSpectrum.ext_iff,
        NK.GlobalCFT.Place.smulHeightOneSpectrum_asIdeal]
      rw [Ideal.pointwise_smul_def]
      exact Iff.rfl
    rw [hstab_eq]
    exact hstabI
  refine dvd_card_stabilizer_of_nontrivial q hq k Ω M hcard v ?_
  refine ⟨NK.GlobalCFT.Place.ofFinite P, hlies, fun hbot => hδM_ne ?_⟩
  rw [hbot] at hstabP
  simpa using hstabP


end Work.SSGRoute.Sha2Lib
