import Mathlib
import Submission.NK.GlobalCFT.Place
import Submission.NK.GlobalCFT.Norm
import Submission.Commons.NumberTheory.NumberField.Completion.norm_units_surjective_of_ramificationIdx_eq_one
import Submission.Commons.NumberTheory.NumberField.Completion.val_norm_adicCompletion_eq_pow
import Submission.Commons.NumberTheory.NumberField.Completion.val_norm_units_adicCompletion_eq_pow_inertiaDeg
import Submission.Commons.NumberTheory.NumberField.Completion.val_adicCompletionMap_eq_pow
import Submission.Commons.NumberTheory.NumberField.Completion.finrank_adicCompletion_eq_ramificationIdx_mul_inertiaDeg
import Submission.Commons.NumberTheory.NumberField.Completion.module_finite_adicCompletion
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

open scoped NumberField WithZero

set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 4000000

namespace NK.CFTLib.Existence

open NK.GlobalCFT

/-- **The ramification index is one as soon as the prime is not the only prime over the base
prime**, in a Galois extension of prime degree.

If `L / K` is a Galois extension of number fields of prime degree `p`, `Q` is a nonzero prime of
`𝓞 K` and `q ≠ q₁` are two primes of `𝓞 L` over `Q`, then `e(q|Q) = 1`.

Indeed, the fundamental identity `g · e · f = [L : K] = p` for the number `g` of primes of `𝓞 L`
over `Q` (`Ideal.ncard_primesOver_mul_ramificationIdxIn_mul_inertiaDegIn`) together with `g ≥ 2`
and the primality of `p` forces `g = p` and `e · f = 1`. -/
private theorem ramificationIdx_eq_one_of_exists_ne {K L : Type*} [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    {p : ℕ} (hp : p.Prime) (hdeg : Module.finrank K L = p)
    (Q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (q q₁ : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L))
    (hq : q.asIdeal.LiesOver Q.asIdeal) (hq₁ : q₁.asIdeal.LiesOver Q.asIdeal) (hne : q₁ ≠ q) :
    q.asIdeal.ramificationIdx (NumberField.RingOfIntegers K) = 1 := by
  letI : MulSemiringAction Gal(L/K) (NumberField.RingOfIntegers L) :=
    IsIntegralClosure.MulSemiringAction (NumberField.RingOfIntegers K) K L
      (NumberField.RingOfIntegers L)
  haveI hGal : IsGaloisGroup Gal(L/K) (NumberField.RingOfIntegers K)
      (NumberField.RingOfIntegers L) :=
    IsGaloisGroup.of_isFractionRing Gal(L/K) (NumberField.RingOfIntegers K)
      (NumberField.RingOfIntegers L) K L
  haveI := hq
  have hcardG : Nat.card Gal(L/K) = p := by
    rw [IsGalois.card_aut_eq_finrank K L, hdeg]
  have hfund := Ideal.ncard_primesOver_mul_ramificationIdxIn_mul_inertiaDegIn
    (A := NumberField.RingOfIntegers K) Q.asIdeal (NumberField.RingOfIntegers L) Gal(L/K)
  rw [hcardG] at hfund
  have hqmem : q.asIdeal ∈ Q.asIdeal.primesOver (NumberField.RingOfIntegers L) :=
    ⟨q.isPrime, hq⟩
  have hq₁mem : q₁.asIdeal ∈ Q.asIdeal.primesOver (NumberField.RingOfIntegers L) :=
    ⟨q₁.isPrime, hq₁⟩
  have hneq : q.asIdeal ≠ q₁.asIdeal := fun h =>
    hne (IsDedekindDomain.HeightOneSpectrum.ext h).symm
  have hsub : ({q.asIdeal, q₁.asIdeal} : Set (Ideal (NumberField.RingOfIntegers L))) ⊆
      Q.asIdeal.primesOver (NumberField.RingOfIntegers L) := by
    intro P hP
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hP
    rcases hP with rfl | rfl
    · exact hqmem
    · exact hq₁mem
  have hg2 : 2 ≤ (Q.asIdeal.primesOver (NumberField.RingOfIntegers L)).ncard := by
    have h := Set.ncard_le_ncard hsub
    rw [Set.ncard_pair hneq] at h
    exact h
  have hdvd : (Q.asIdeal.primesOver (NumberField.RingOfIntegers L)).ncard ∣ p :=
    ⟨_, hfund.symm⟩
  have hsplit : Q.asIdeal.ramificationIdxIn (NumberField.RingOfIntegers L) *
      Q.asIdeal.inertiaDegIn (NumberField.RingOfIntegers L) = 1 := by
    rcases hp.eq_one_or_self_of_dvd _ hdvd with h1 | h1
    · omega
    · refine Nat.mul_left_cancel hp.pos ?_
      rw [h1] at hfund
      rw [mul_one]
      exact hfund
  have heIn : Q.asIdeal.ramificationIdxIn (NumberField.RingOfIntegers L) = 1 :=
    Nat.dvd_one.mp ⟨Q.asIdeal.inertiaDegIn (NumberField.RingOfIntegers L), hsplit.symm⟩
  rw [← Ideal.ramificationIdxIn_eq_ramificationIdx (A := NumberField.RingOfIntegers K)
    (B := NumberField.RingOfIntegers L) Q.asIdeal q.asIdeal Gal(L/K)]
  exact heIn


/-- **Surjectivity of the local norm on local units at an unramified place**, in the form needed
here (all local fields written as `Q.adicCompletion`/`q.adicCompletion`).

If `e(q|Q) = 1` then every local unit at `Q` is the norm of a local unit at `q`.  This is the
classical statement that an unramified extension has norm-surjective unit groups; the proof is the
elementary valuation argument: for `u ∈ 𝒪_{K_Q}ˣ` the commons lemma
`norm_units_surjective_of_ramificationIdx_eq_one` produces `x ∈ L_q` with `N x = u`, and the norm
identity `v (Φ (N x)) = v x ^ [L_q : K_Q]` together with `e = 1` forces `v x = 1`. -/
private theorem exists_localUnit_localNormFinite_eq_of_ramificationIdx_eq_one
    {K : Type} [Field K] [NumberField K] {L : Type} [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    (Q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L))
    (hq : q.asIdeal.LiesOver Q.asIdeal)
    (hunr : q.asIdeal.ramificationIdx (NumberField.RingOfIntegers K) = 1)
    (u : (Q.adicCompletion K)ˣ)
    (hu : u ∈ NK.GlobalCFT.Place.localUnits K (NK.GlobalCFT.Place.ofFinite Q)) :
    ∃ u' : (q.adicCompletion L)ˣ,
      u' ∈ NK.GlobalCFT.Place.localUnits L (NK.GlobalCFT.Place.ofFinite q) ∧
        NK.GlobalCFT.Place.localNormFinite q Q hq u' = u := by
  letI : Algebra (Q.adicCompletion K) (q.adicCompletion L) :=
    RingHom.toAlgebra (Commons.RingTheory.Henselian.adicCompletionMap Q q hq)
  haveI hfd : Module.Finite (Q.adicCompletion K) (q.adicCompletion L) :=
    Commons.NumberTheory.NumberField.Completion.module_finite_adicCompletion Q q hq
  have hval : Valued.v (R := Q.adicCompletion K) (Γ₀ := WithZero (Multiplicative ℤ))
      (u : Q.adicCompletion K) = 1 :=
    (NK.GlobalCFT.Place.mem_localUnits_ofFinite_iff_valued_eq_one (K := K) (q := Q)).mp hu
  obtain ⟨x, hx⟩ :=
    Commons.NumberTheory.NumberField.Completion.norm_units_surjective_of_ramificationIdx_eq_one
      Q q hq hunr (u : Q.adicCompletion K) hval
  have hxne : x ≠ 0 := by
    intro h0
    have h1 : Algebra.norm (Q.adicCompletion K) x = (0 : Q.adicCompletion K) := by
      rw [h0, Algebra.norm_zero]
    rw [h1] at hx
    exact Units.ne_zero u hx.symm
  have hvx : Valued.v (R := q.adicCompletion L) (Γ₀ := WithZero (Multiplicative ℤ)) x = 1 := by
    have h1 := Commons.NumberTheory.NumberField.Completion.val_norm_adicCompletion_eq_pow Q q hq x
    have h2 := Commons.NumberTheory.NumberField.Completion.val_adicCompletionMap_eq_pow Q q hq
      (Algebra.norm (Q.adicCompletion K) x)
    have halg : (algebraMap (Q.adicCompletion K) (q.adicCompletion L)
        (Algebra.norm (Q.adicCompletion K) x)) =
        (Commons.RingTheory.Henselian.adicCompletionMap Q q hq)
          (Algebra.norm (Q.adicCompletion K) x) := rfl
    have hfin : Module.finrank (Q.adicCompletion K) (q.adicCompletion L) =
        q.asIdeal.inertiaDeg (NumberField.RingOfIntegers K) := by
      have h :=
        Commons.NumberTheory.NumberField.Completion.finrank_adicCompletion_eq_ramificationIdx_mul_inertiaDeg
          (K := K) (L := L) Q q hq
      rw [hunr, one_mul] at h
      exact h.symm
    have hvpow : Valued.v (R := q.adicCompletion L) (Γ₀ := WithZero (Multiplicative ℤ)) x ^
        (q.asIdeal.inertiaDeg (NumberField.RingOfIntegers K)) = 1 := by
      rw [← hfin, ← h1, halg, h2, hx, hval, hunr]
      simp
    have hvne : Valued.v (R := q.adicCompletion L) (Γ₀ := WithZero (Multiplicative ℤ)) x ≠ 0 :=
      (Valuation.ne_zero_iff _).mpr hxne
    have hlog : (q.asIdeal.inertiaDeg (NumberField.RingOfIntegers K) : ℤ) *
        WithZero.log (Valued.v (R := q.adicCompletion L)
          (Γ₀ := WithZero (Multiplicative ℤ)) x) = 0 := by
      have h := WithZero.log_pow (Valued.v (R := q.adicCompletion L)
        (Γ₀ := WithZero (Multiplicative ℤ)) x)
        (q.asIdeal.inertiaDeg (NumberField.RingOfIntegers K))
      rw [hvpow, WithZero.log_one] at h
      simpa [nsmul_eq_mul] using h.symm
    have hfne : (q.asIdeal.inertiaDeg (NumberField.RingOfIntegers K) : ℤ) ≠ 0 := by
      exact_mod_cast (Ideal.inertiaDeg_pos q.asIdeal (NumberField.RingOfIntegers K)).ne'
    have hlog0 : WithZero.log (Valued.v (R := q.adicCompletion L)
        (Γ₀ := WithZero (Multiplicative ℤ)) x) = 0 :=
      (mul_eq_zero.mp hlog).resolve_left hfne
    rw [← WithZero.exp_log hvne, hlog0, WithZero.exp_zero]
  refine ⟨Units.mk0 x hxne, ?_, ?_⟩
  · rw [NK.GlobalCFT.Place.mem_localUnits_ofFinite_iff_valued_eq_one]
    exact hvx
  · rw [NK.GlobalCFT.Place.localNormFinite]
    refine Units.ext ?_
    rw [Units.coe_map, Units.val_mk0]
    exact hx

theorem localNormUnits_of_fiber_prod
    {K : Type} [Field K] [NumberField K] {L : Type} [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L] {p : ℕ} (hp : p.Prime) (hdeg : Module.finrank K L = p)
    (Q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L))
    (hq : q.asIdeal.LiesOver Q.asIdeal)
    (u : (Q.adicCompletion K)ˣ)
    (hu : u ∈ NK.GlobalCFT.Place.localUnits K (NK.GlobalCFT.Place.ofFinite Q))
    (x : NK.GlobalCFT.Idele L)
    (hprod : u = ∏ q' ∈ (NK.GlobalCFT.Place.primesOverFinite Q).attach,
        (NK.GlobalCFT.Place.localNormFinite
          (q' : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L)) Q
          ((NK.GlobalCFT.Place.mem_primesOverFinite (K := K) (L := L) (Q := Q) (q := q')).mp q'.2))
          (x (NK.GlobalCFT.Place.ofFinite q'.1))) :
    ∃ u' : (q.adicCompletion L)ˣ,
      u' ∈ NK.GlobalCFT.Place.localUnits L (NK.GlobalCFT.Place.ofFinite q) ∧
        NK.GlobalCFT.Place.localNormFinite q Q hq u' = u := by
  classical
  by_cases huniq : ∀ q' ∈ NK.GlobalCFT.Place.primesOverFinite (K := K) (L := L) Q, q' = q
  · -- The fibre over `Q` is a single prime: the product is the term at `q`.
    have hqmem : q ∈ NK.GlobalCFT.Place.primesOverFinite (K := K) (L := L) Q :=
      (NK.GlobalCFT.Place.mem_primesOverFinite).mpr hq
    set F : {q' // q' ∈ NK.GlobalCFT.Place.primesOverFinite (K := K) (L := L) Q} →
        (Q.adicCompletion K)ˣ := fun q' =>
      NK.GlobalCFT.Place.localNormFinite q'.1 Q
        ((NK.GlobalCFT.Place.mem_primesOverFinite (K := K) (L := L) (Q := Q)
          (q := q'.1)).mp q'.2)
        (x (NK.GlobalCFT.Place.ofFinite q'.1)) with hF
    have hprodF : u = ∏ q' ∈ (NK.GlobalCFT.Place.primesOverFinite (K := K) (L := L) Q).attach,
        F q' := hprod
    have hkey : (∏ q' ∈ (NK.GlobalCFT.Place.primesOverFinite (K := K) (L := L) Q).attach,
        F q') = F ⟨q, hqmem⟩ := by
      refine Finset.prod_eq_single (⟨q, hqmem⟩ :
        {q' // q' ∈ NK.GlobalCFT.Place.primesOverFinite (K := K) (L := L) Q}) ?_ ?_
      · intro b _ hb
        exact absurd (Subtype.ext (huniq b.1 b.2)) hb
      · intro h
        exact absurd (Finset.mem_attach _ _) h
    -- The single factor of the product is the term at `q`; the two proofs of
    -- `q.asIdeal.LiesOver Q.asIdeal` occurring are identified by proof irrelevance.
    have hprod' : NK.GlobalCFT.Place.localNormFinite q Q hq
        (x (NK.GlobalCFT.Place.ofFinite q)) = u := by
      rw [hprodF, hkey]
    have hxunit : x (NK.GlobalCFT.Place.ofFinite q) ∈
        NK.GlobalCFT.Place.localUnits L (NK.GlobalCFT.Place.ofFinite q) := by
      letI : Algebra (Q.adicCompletion K) (q.adicCompletion L) :=
        RingHom.toAlgebra (Commons.RingTheory.Henselian.adicCompletionMap Q q hq)
      rw [NK.GlobalCFT.Place.mem_localUnits_ofFinite_iff_valued_eq_one]
      have huval : Valued.v (R := Q.adicCompletion K) (Γ₀ := WithZero (Multiplicative ℤ))
          (u : Q.adicCompletion K) = 1 :=
        (NK.GlobalCFT.Place.mem_localUnits_ofFinite_iff_valued_eq_one (K := K) (q := Q)).mp hu
      have hnorm :=
        Commons.NumberTheory.NumberField.Completion.val_norm_units_adicCompletion_eq_pow_inertiaDeg
          Q q hq (x (NK.GlobalCFT.Place.ofFinite q))
      have hcoe : ((NK.GlobalCFT.Place.localNormFinite q Q hq
            (x (NK.GlobalCFT.Place.ofFinite q)) : (Q.adicCompletion K)ˣ) :
              Q.adicCompletion K) =
          Algebra.norm (Q.adicCompletion K)
            ((x (NK.GlobalCFT.Place.ofFinite q)) : q.adicCompletion L) := by
        rw [NK.GlobalCFT.Place.localNormFinite, Units.coe_map]
      have h1 : (Valued.v (R := q.adicCompletion L) (Γ₀ := WithZero (Multiplicative ℤ))
          ((x (NK.GlobalCFT.Place.ofFinite q)) : q.adicCompletion L)) ^
            (q.asIdeal.inertiaDeg (NumberField.RingOfIntegers K)) = 1 := by
        rw [← hnorm, ← hcoe, hprod', huval]
      have hf : q.asIdeal.inertiaDeg (NumberField.RingOfIntegers K) ≠ 0 :=
        (Ideal.inertiaDeg_pos q.asIdeal (NumberField.RingOfIntegers K)).ne'
      have hvne : Valued.v (R := q.adicCompletion L) (Γ₀ := WithZero (Multiplicative ℤ))
          ((x (NK.GlobalCFT.Place.ofFinite q)) : q.adicCompletion L) ≠ 0 :=
        (Valuation.ne_zero_iff _).mpr (Units.ne_zero _)
      have hlog : (q.asIdeal.inertiaDeg (NumberField.RingOfIntegers K) : ℤ) *
          WithZero.log (Valued.v (R := q.adicCompletion L) (Γ₀ := WithZero (Multiplicative ℤ))
            ((x (NK.GlobalCFT.Place.ofFinite q)) : q.adicCompletion L)) = 0 := by
        have h := WithZero.log_pow (Valued.v (R := q.adicCompletion L)
          (Γ₀ := WithZero (Multiplicative ℤ))
          ((x (NK.GlobalCFT.Place.ofFinite q)) : q.adicCompletion L))
          (q.asIdeal.inertiaDeg (NumberField.RingOfIntegers K))
        rw [h1, WithZero.log_one] at h
        simpa [nsmul_eq_mul] using h.symm
      have hlog0 : WithZero.log (Valued.v (R := q.adicCompletion L)
          (Γ₀ := WithZero (Multiplicative ℤ))
          ((x (NK.GlobalCFT.Place.ofFinite q)) : q.adicCompletion L)) = 0 :=
        (mul_eq_zero.mp hlog).resolve_left (by exact_mod_cast hf)
      rw [← WithZero.exp_log hvne, hlog0, WithZero.exp_zero]
    exact ⟨x (NK.GlobalCFT.Place.ofFinite q), hxunit, hprod'⟩
  · -- Two distinct primes over `Q`: the place `q` is unramified.
    push Not at huniq
    obtain ⟨q₁, hq₁mem, hq₁ne⟩ := huniq
    have hq₁ : q₁.asIdeal.LiesOver Q.asIdeal :=
      (NK.GlobalCFT.Place.mem_primesOverFinite).mp hq₁mem
    have hram : q.asIdeal.ramificationIdx (NumberField.RingOfIntegers K) = 1 :=
      ramificationIdx_eq_one_of_exists_ne hp hdeg Q q q₁ hq hq₁ hq₁ne
    exact exists_localUnit_localNormFinite_eq_of_ramificationIdx_eq_one Q q hq hram u hu

end NK.CFTLib.Existence
