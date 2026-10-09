import Mathlib
import Submission.NK.CFTLib.Arl.Defs
import Submission.NK.CFTLib.Arl.prod_frobAtPrime_ramificationIdx_eq_one
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

set_option linter.style.haveILetI false
set_option warn.classDefReducibility false

open scoped NumberField
open NumberField IsDedekindDomain

namespace NK.CFTLib.Existence

/-- A commutative group structure on `Gal(L/K)` from the commutativity hypothesis. -/
noncomputable def galCommGroup {K L : Type*} [Field K] [Field L] [Algebra K L]
    (hcomm : ∀ a b : Gal(L/K), a * b = b * a) : CommGroup Gal(L/K) :=
  { (inferInstance : Group Gal(L/K)) with mul_comm := hcomm }

theorem artinSym_map_eq_one_of_unramified {K E : Type} [Field K] [NumberField K] [Field E] [NumberField E]
    [Algebra K E] [FiniteDimensional K E] [IsGalois K E]
    (L' M' : IntermediateField K E) [IsGalois K ↥M'] [IsMulCommutative Gal(↥M'/K)]
    (hdisj : L' ⊓ M' = ⊥) (hsup : L' ⊔ M' = ⊤)
    (hexp : ∀ σ : Gal(↥M'/K), σ ^ Module.finrank K ↥L' = 1)
    (hcomm : ∀ a b : Gal(E/↥L'), a * b = b * a)
    (A : FractionalIdeal (nonZeroDivisors (NumberField.RingOfIntegers K)) K)
    (B : FractionalIdeal (nonZeroDivisors (NumberField.RingOfIntegers ↥L')) ↥L')
    (hB : ∀ (𝔮 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ↥L'))
          (𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)),
        𝔮.asIdeal.LiesOver 𝔭.asIdeal →
        FractionalIdeal.count ↥L' 𝔮 B
          = (𝔮.asIdeal.ramificationIdx (NumberField.RingOfIntegers K) : ℤ)
            * FractionalIdeal.count K 𝔭 A)
    (hunrM : ∀ 𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K),
      FractionalIdeal.count K 𝔭 A ≠ 0 →
      ∀ 𝔔 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ↥M'),
        𝔔.asIdeal.LiesOver 𝔭.asIdeal →
          𝔔.asIdeal.ramificationIdx (NumberField.RingOfIntegers K) = 1)
    (hunrE : ∀ 𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K),
      FractionalIdeal.count K 𝔭 A ≠ 0 →
      ∀ 𝔮 ∈ NK.GlobalCFT.Place.primesOverFinite (K := K) (L := ↥L') 𝔭,
      ∀ 𝔔 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers E),
        𝔔.asIdeal.LiesOver 𝔮.asIdeal →
          𝔔.asIdeal.ramificationIdx (NumberField.RingOfIntegers ↥L') = 1) :
    NK.CFTLib.Arl.artinSym (K := ↥L') (L := E) hcomm B = 1 := by
  classical
  letI : CommGroup Gal(E/↥L') := galCommGroup hcomm
  -- ### The transfer lemma at a single prime, with `ℤ`-exponents
  have htransfer : ∀ 𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K),
      FractionalIdeal.count K 𝔭 A ≠ 0 →
      (∏ 𝔮 ∈ NK.GlobalCFT.Place.primesOverFinite (K := K) (L := ↥L') 𝔭,
        (NK.Chebotarev.frobAtPrime (K := ↥L') (L := E) 𝔮)
          ^ ((𝔮.asIdeal.ramificationIdx (NumberField.RingOfIntegers K) : ℕ) : ℤ)) = 1 := by
    intro 𝔭 h𝔭
    have h := NK.CFTLib.Arl.prod_frobAtPrime_ramificationIdx_eq_one (K := K) (E := E)
      L' M' hdisj hsup hexp 𝔭 (fun Q hQ => hunrM 𝔭 h𝔭 Q hQ)
      (fun 𝔮 h𝔮 => hunrE 𝔭 h𝔭 𝔮 h𝔮)
    have h' : (∏ 𝔮 ∈ NK.GlobalCFT.Place.primesOverFinite (K := K) (L := ↥L') 𝔭,
        (NK.Chebotarev.frobAtPrime (K := ↥L') (L := E) 𝔮)
          ^ (𝔮.asIdeal.ramificationIdx (NumberField.RingOfIntegers K))) = 1 := by
      rw [← Finset.prod_map_toList]
      exact h
    simpa only [zpow_natCast] using h'
  -- ### The support of `B` is contained in the fibres over the primes dividing `A`
  let T : Finset (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)) :=
    (NK.CFTLib.Arl.exps A).support
  have hT : ∀ 𝔭, 𝔭 ∈ T ↔ (NK.CFTLib.Arl.exps A) 𝔭 ≠ 0 := by
    intro 𝔭; simp only [T, Finsupp.mem_support_iff]
  have hsupport : (NK.CFTLib.Arl.exps B).support ⊆
      T.biUnion (fun 𝔭 => NK.GlobalCFT.Place.primesOverFinite (K := K) (L := ↥L') 𝔭) := by
    intro 𝔮 h𝔮
    rw [Finsupp.mem_support_iff] at h𝔮
    set 𝔭 := 𝔮.under (NumberField.RingOfIntegers K) with h𝔭def
    have hover : 𝔮.asIdeal.LiesOver 𝔭.asIdeal := Ideal.LiesOver.mk rfl
    have hcount : (NK.CFTLib.Arl.exps B) 𝔮
        = (𝔮.asIdeal.ramificationIdx (NumberField.RingOfIntegers K) : ℤ)
          * (NK.CFTLib.Arl.exps A) 𝔭 := by
      simpa only [NK.CFTLib.Arl.exps_apply] using hB 𝔮 𝔭 hover
    have hAne : (NK.CFTLib.Arl.exps A) 𝔭 ≠ 0 := by
      intro h0
      exact h𝔮 (by rw [hcount, h0, mul_zero])
    refine Finset.mem_biUnion.mpr ⟨𝔭, ?_, ?_⟩
    · exact (hT 𝔭).mpr hAne
    · exact (NK.GlobalCFT.Place.mem_primesOverFinite).mpr hover
  -- ### The fibres are pairwise disjoint
  have hpair : (↑T : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))).PairwiseDisjoint
      (fun 𝔭 => NK.GlobalCFT.Place.primesOverFinite (K := K) (L := ↥L') 𝔭) := by
    intro 𝔭 _ 𝔭' _ hne
    change Disjoint (NK.GlobalCFT.Place.primesOverFinite (K := K) (L := ↥L') 𝔭)
      (NK.GlobalCFT.Place.primesOverFinite (K := K) (L := ↥L') 𝔭')
    rw [Finset.disjoint_left]
    intro 𝔮 h𝔮 h𝔮'
    exact hne (HeightOneSpectrum.ext
      ((NK.GlobalCFT.Place.mem_primesOverFinite.mp h𝔮).over.trans
        ((NK.GlobalCFT.Place.mem_primesOverFinite.mp h𝔮').over.symm)))
  -- ### Conclusion: expand the Artin symbol as a product over the fibres
  change (NK.CFTLib.Arl.exps B).prod
      (fun 𝔮 e => (NK.Chebotarev.frobAtPrime (K := ↥L') (L := E) 𝔮) ^ e) = 1
  rw [Finsupp.prod_of_support_subset (NK.CFTLib.Arl.exps B) hsupport
      (fun 𝔮 e => (NK.Chebotarev.frobAtPrime (K := ↥L') (L := E) 𝔮) ^ e)
      (fun i _ => zpow_zero _)]
  rw [Finset.prod_biUnion hpair]
  refine Finset.prod_eq_one (fun 𝔭 h𝔭 => ?_)
  have hAne : (NK.CFTLib.Arl.exps A) 𝔭 ≠ 0 := (hT 𝔭).mp h𝔭
  have hfib : ∀ 𝔮 ∈ NK.GlobalCFT.Place.primesOverFinite (K := K) (L := ↥L') 𝔭,
      (NK.CFTLib.Arl.exps B) 𝔮
        = ((𝔮.asIdeal.ramificationIdx (NumberField.RingOfIntegers K) : ℕ) : ℤ)
          * (NK.CFTLib.Arl.exps A) 𝔭 := by
    intro 𝔮 h𝔮
    simpa only [NK.CFTLib.Arl.exps_apply] using
      hB 𝔮 𝔭 ((NK.GlobalCFT.Place.mem_primesOverFinite).mp h𝔮)
  calc (∏ 𝔮 ∈ NK.GlobalCFT.Place.primesOverFinite (K := K) (L := ↥L') 𝔭,
          (NK.Chebotarev.frobAtPrime (K := ↥L') (L := E) 𝔮) ^ ((NK.CFTLib.Arl.exps B) 𝔮))
      = ∏ 𝔮 ∈ NK.GlobalCFT.Place.primesOverFinite (K := K) (L := ↥L') 𝔭,
          (NK.Chebotarev.frobAtPrime (K := ↥L') (L := E) 𝔮)
            ^ (((𝔮.asIdeal.ramificationIdx (NumberField.RingOfIntegers K) : ℕ) : ℤ)
                * (NK.CFTLib.Arl.exps A) 𝔭) :=
        Finset.prod_congr rfl (fun 𝔮 h𝔮 => by rw [hfib 𝔮 h𝔮])
    _ = ∏ 𝔮 ∈ NK.GlobalCFT.Place.primesOverFinite (K := K) (L := ↥L') 𝔭,
          ((NK.Chebotarev.frobAtPrime (K := ↥L') (L := E) 𝔮)
            ^ ((𝔮.asIdeal.ramificationIdx (NumberField.RingOfIntegers K) : ℕ) : ℤ))
            ^ ((NK.CFTLib.Arl.exps A) 𝔭) :=
        Finset.prod_congr rfl (fun 𝔮 _ => zpow_mul _ _ _)
    _ = (∏ 𝔮 ∈ NK.GlobalCFT.Place.primesOverFinite (K := K) (L := ↥L') 𝔭,
          (NK.Chebotarev.frobAtPrime (K := ↥L') (L := E) 𝔮)
            ^ ((𝔮.asIdeal.ramificationIdx (NumberField.RingOfIntegers K) : ℕ) : ℤ))
          ^ ((NK.CFTLib.Arl.exps A) 𝔭) :=
        Finset.prod_zpow _ _ _
    _ = 1 := by rw [htransfer 𝔭 hAne]; exact one_zpow _

end NK.CFTLib.Existence


