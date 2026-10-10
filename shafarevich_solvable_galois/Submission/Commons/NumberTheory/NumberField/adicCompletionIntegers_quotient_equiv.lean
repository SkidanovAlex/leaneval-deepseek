import Mathlib.RingTheory.DedekindDomain.AdicValuation
import Submission.Commons.NumberTheory.NumberField.Completion.ringOfIntegers_dense_in_adicIntegers
import Submission.Commons.RingTheory.Henselian.uniformizer_valuation_eq_exp_neg_one
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

open scoped NumberField WithZero
open IsDedekindDomain Filter
open scoped Topology

namespace Commons.NumberTheory.NumberField

noncomputable section

set_option autoImplicit false
set_option linter.style.haveILetI false
set_option maxHeartbeats 1000000

/-- In the discrete value group `ℤᵐ⁰`, an element strictly below `exp k` is at most `exp (k - 1)`. -/
lemma lt_exp_le_exp_sub_one {y : Zstar0} {k : ℤ} (hy : y < WithZero.exp k) :
    y ≤ WithZero.exp (k - 1) := by
  by_cases hy0 : y = 0
  · simp [hy0]
  · rw [← WithZero.exp_log hy0]
    apply WithZero.exp_le_exp.2
    have hlog : WithZero.log y < k := by
      rw [← WithZero.exp_log hy0] at hy
      exact WithZero.exp_lt_exp.mp hy
    omega

/-- The value on `𝓞 K`, seen in the completion, of an element is its `v`-adic valuation. -/
lemma adicCompletion_valued_algebraMap {K : Type*} [Field K] [NumberField K]
    (V : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (r : NumberField.RingOfIntegers K) :
    Valued.v ((algebraMap (NumberField.RingOfIntegers K) (V.adicCompletionIntegers K) r :
        V.adicCompletionIntegers K) : V.adicCompletion K) = V.intValuation r :=
  (IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_eq_valuation
      (R := NumberField.RingOfIntegers K) (K := K) V r).trans
    (IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap
      (R := NumberField.RingOfIntegers K) (K := K) V r)

/-- Membership in the `n`-th power of the maximal ideal of the ring of integers of a completion,
in terms of the valuation. -/
lemma mem_maximalIdeal_pow_iff_valued_le {K : Type*} [Field K] [NumberField K]
    (V : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)) (n : ℕ)
    (y : V.adicCompletionIntegers K) :
    y ∈ IsLocalRing.maximalIdeal (V.adicCompletionIntegers K) ^ n ↔
      Valued.v (y : V.adicCompletion K) ≤ WithZero.exp (-(n : ℤ)) := by
  have hpow : (WithZero.exp (-1 : ℤ)) ^ n = WithZero.exp (-(n : ℤ)) := by
    rw [← WithZero.exp_nsmul]
    congr 1
    simp
  have hunif : Valued.v (algebraMap (V.adicCompletionIntegers K) (V.adicCompletion K)
        (Commons.RingTheory.Henselian.uniformizer (R := NumberField.RingOfIntegers K)
          (K := K) V)) = WithZero.exp (-1 : ℤ) := by
    simpa using Commons.RingTheory.Henselian.uniformizer_valuation_eq_exp_neg_one (K := K) V
  rw [Commons.RingTheory.Henselian.mem_pow_maximalIdeal_iff
      (R := NumberField.RingOfIntegers K) (K := K) V n y]
  rw [hunif, hpow]
  simp

/-- Every element of the ring of integers of the completion is congruent modulo the `n`-th power
of the maximal ideal to the image of an element of `𝓞 K`. -/
lemma exists_sub_algebraMap_mem_maximalIdeal_pow {K : Type*} [Field K] [NumberField K]
    (V : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (n : ℕ) (x : V.adicCompletionIntegers K) :
    ∃ r : NumberField.RingOfIntegers K,
      x - algebraMap (NumberField.RingOfIntegers K) (V.adicCompletionIntegers K) r ∈
        IsLocalRing.maximalIdeal (V.adicCompletionIntegers K) ^ n := by
  classical
  let R := NumberField.RingOfIntegers K
  let A := V.adicCompletionIntegers K
  let L := V.adicCompletion K
  let φ : R →+* A := algebraMap R A
  -- density: for every `k` we can approximate `x` by an element of the image of `R`
  have hdense : ∀ k : ℤ, ∃ r : R,
      Valued.v (((φ r : A) : L) - (x : L)) < WithZero.exp k := by
    intro k
    have hcl :=
      Commons.NumberTheory.NumberField.Completion.ringOfIntegers_dense_in_adicIntegers K V x
    have hball : {y : L | Valued.v (y - (x : L)) < WithZero.exp k} ∈ 𝓝 (x : L) :=
      Commons.NumberTheory.NumberField.Completion.exp_ball_nhds V (x : L) k
    obtain ⟨y, hyball, hyS⟩ := (mem_closure_iff_nhds.mp hcl) _ hball
    obtain ⟨r, rfl⟩ := hyS
    have hcoe : ((φ r : A) : L) = algebraMap K L (r : K) := by
      rw [show ((φ r : A) : L) = algebraMap R L r from rfl]
      exact IsScalarTower.algebraMap_apply R K L r
    exact ⟨r, by rw [hcoe]; exact hyball⟩
  rcases n with _ | n
  · refine ⟨0, ?_⟩
    rw [pow_zero, Ideal.one_eq_top]
    simp
  · obtain ⟨r, hr⟩ := hdense (1 - ((n + 1 : ℕ) : ℤ))
    refine ⟨r, ?_⟩
    have hneg : ((x - φ r : A) : L) = -(((φ r : A) : L) - (x : L)) := by
      simp [neg_sub]
    rw [show IsLocalRing.maximalIdeal (V.adicCompletionIntegers K) ^ (n + 1) =
        IsLocalRing.maximalIdeal A ^ (n + 1) from rfl]
    rw [mem_maximalIdeal_pow_iff_valued_le V (n + 1) (x - φ r)]
    rw [hneg, Valuation.map_neg]
    have hstep := lt_exp_le_exp_sub_one hr
    have hk : (1 - ((n + 1 : ℕ) : ℤ)) - 1 = -((n + 1 : ℕ) : ℤ) := by ring
    rwa [hk] at hstep

/-- The natural map `𝓞 K ⧸ Q ^ n → (Q.adicCompletionIntegers K) ⧸ 𝔪 ^ n` is a ring isomorphism,
compatible with the canonical projections. -/
theorem adicCompletionIntegers_quotient_equiv {K : Type*} [Field K] [NumberField K]
    (Q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)) (n : ℕ) :
    ∃ e : (NumberField.RingOfIntegers K ⧸ Q.asIdeal ^ n) ≃+*
        (Q.adicCompletionIntegers K ⧸ (IsLocalRing.maximalIdeal (Q.adicCompletionIntegers K)) ^ n),
      ∀ x : NumberField.RingOfIntegers K,
        e (Ideal.Quotient.mk _ x) =
          Ideal.Quotient.mk _ (algebraMap (NumberField.RingOfIntegers K)
            (Q.adicCompletionIntegers K) x) := by
  classical
  let R := NumberField.RingOfIntegers K
  let A := Q.adicCompletionIntegers K
  let φ : R →+* A := algebraMap R A
  let m : Ideal A := IsLocalRing.maximalIdeal A
  have hm : m = Q.asIdeal.map φ := by
    simpa [m, φ, A] using
      (Commons.NumberTheory.NumberField.adicCompletionIntegers_maximalIdeal_eq_map (K := K) Q)
  have hmn : m ^ n = (Q.asIdeal ^ n).map φ := by
    rw [hm, ← Ideal.map_pow]
  have hle : Q.asIdeal ^ n ≤ (m ^ n).comap φ := by
    rw [hmn]
    exact Ideal.le_comap_map
  let ψ : R ⧸ Q.asIdeal ^ n →+* A ⧸ m ^ n :=
    Ideal.quotientMap (I := Q.asIdeal ^ n) (m ^ n) φ hle
  have hψ : ∀ x : R,
      ψ (Ideal.Quotient.mk (Q.asIdeal ^ n) x) = Ideal.Quotient.mk (m ^ n) (φ x) :=
    fun x => Ideal.quotientMap_mk
  have hinj : Function.Injective ψ := by
    rw [injective_iff_map_eq_zero]
    intro a ha
    obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective a
    have h1 : Ideal.Quotient.mk (m ^ n) (φ r) = 0 := by
      rw [← hψ r]
      exact ha
    rw [Ideal.Quotient.eq_zero_iff_mem] at h1
    rw [Ideal.Quotient.eq_zero_iff_mem]
    have hv : Q.intValuation r ≤ WithZero.exp (-(n : ℤ)) := by
      have := (mem_maximalIdeal_pow_iff_valued_le Q n (φ r)).mp h1
      rwa [adicCompletion_valued_algebraMap Q r] at this
    exact (Q.intValuation_le_pow_iff_mem r n).mp hv
  have hsurj : Function.Surjective ψ := by
    intro y
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective y
    obtain ⟨r, hr⟩ := exists_sub_algebraMap_mem_maximalIdeal_pow Q n x
    refine ⟨Ideal.Quotient.mk (Q.asIdeal ^ n) r, ?_⟩
    rw [hψ r, Ideal.Quotient.eq]
    have hneg : -(x - φ r) ∈ m ^ n :=
      (Ideal.neg_mem_iff (I := m ^ n)).mpr (by simpa [φ] using hr)
    simpa [neg_sub] using hneg
  have hbij : Function.Bijective ψ := ⟨hinj, hsurj⟩
  refine ⟨RingEquiv.ofBijective ψ hbij, ?_⟩
  intro x
  change (RingEquiv.ofBijective ψ hbij) (Ideal.Quotient.mk (Q.asIdeal ^ n) x) =
    Ideal.Quotient.mk (m ^ n) (φ x)
  rw [RingEquiv.ofBijective_apply]
  exact hψ x

end

end Commons.NumberTheory.NumberField
