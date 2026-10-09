import Mathlib
import Submission.NK.CFTLib.Arl.Defs
import Submission.Commons.NumberTheory.NumberField.Completion.ringOfIntegers_dense_in_adicIntegers
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 800000

open scoped NumberField nonZeroDivisors WithZero
open NumberField IsDedekindDomain

noncomputable section

namespace NK.CFTLib.Arl

/-! ## A local-to-global congruence lemma -/

/-- **A local-to-global lemma for principal ideals of a Dedekind domain.**  If for every height-one
prime `v` the `v`-adic valuation of `y` is at least that of `m`, then `m` divides `y`.

The point is that the hypothesis is a *local* statement, while the conclusion is global; the
dividing element is produced as `y / m` and shown to be integral by
`HeightOneSpectrum.mem_integers_of_valuation_le_one`. -/
lemma mem_span_of_intValuation_le {R : Type*} [CommRing R] [IsDedekindDomain R]
    {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]
    (m : R) (hm : m ≠ 0) {y : R}
    (h : ∀ v : HeightOneSpectrum R, v.intValuation y ≤ v.intValuation m) :
    y ∈ Ideal.span {m} := by
  obtain ⟨z, hz⟩ := HeightOneSpectrum.mem_integers_of_valuation_le_one K
    ((algebraMap R K y) / (algebraMap R K m)) (fun v => by
      rw [Valuation.map_div, HeightOneSpectrum.valuation_of_algebraMap,
        HeightOneSpectrum.valuation_of_algebraMap]
      exact (div_le_one₀ (zero_lt_iff.mpr (HeightOneSpectrum.intValuation_ne_zero v m hm))).mpr
        (h v))
  rw [Ideal.mem_span_singleton]
  refine ⟨z, ?_⟩
  have hmK : (algebraMap R K m) ≠ 0 :=
    fun h0 => hm (IsFractionRing.injective R K (by simpa using h0))
  apply IsFractionRing.injective R K
  rw [map_mul, hz]
  field_simp


/-- The local congruence hypothesis, transported from the completion to the global `𝔭`-adic
valuation. -/
lemma valuation_sub_one_le_of_hcong {K : Type*} [Field K] [NumberField K] (m : ℕ) (b : Kˣ)
    (hcong : ∀ 𝔭 : HeightOneSpectrum (𝓞 K), (m : 𝓞 K) ∈ 𝔭.asIdeal →
      Valued.v (algebraMap K (𝔭.adicCompletion K) (b : K) - 1)
        ≤ Valued.v ((m : ℕ) : 𝔭.adicCompletion K)) :
    ∀ 𝔭 : HeightOneSpectrum (𝓞 K), (m : 𝓞 K) ∈ 𝔭.asIdeal →
      𝔭.valuation K ((b : K) - 1) ≤ 𝔭.intValuation (m : 𝓞 K) := by
  intro 𝔭 h𝔭
  have h1 := hcong 𝔭 h𝔭
  rw [← show algebraMap K (𝔭.adicCompletion K) ((b : K) - 1)
      = algebraMap K (𝔭.adicCompletion K) (b : K) - 1 by rw [map_sub, map_one]] at h1
  rw [Commons.NumberTheory.NumberField.Completion.valued_alg_eq 𝔭 ((b : K) - 1)] at h1
  rw [show ((m : ℕ) : 𝔭.adicCompletion K) = algebraMap K (𝔭.adicCompletion K) ((m : ℕ) : K)
      from (map_natCast _ m).symm,
    Commons.NumberTheory.NumberField.Completion.valued_alg_eq 𝔭 ((m : ℕ) : K),
    show ((m : ℕ) : K) = algebraMap (𝓞 K) K ((m : ℕ) : 𝓞 K) from (map_natCast _ m).symm,
    HeightOneSpectrum.valuation_of_algebraMap] at h1
  exact h1

/-- At a prime `𝔭` containing `m`, the element `b ≡ 1 mod m` (in the `𝔭`-adic sense) is a
`𝔭`-adic unit. -/
lemma valuation_eq_one_of_hcong {K : Type*} [Field K] [NumberField K] (m : ℕ) (b : Kˣ)
    (hcongK : ∀ 𝔭 : HeightOneSpectrum (𝓞 K), (m : 𝓞 K) ∈ 𝔭.asIdeal →
      𝔭.valuation K ((b : K) - 1) ≤ 𝔭.intValuation (m : 𝓞 K))
    (𝔭 : HeightOneSpectrum (𝓞 K)) (h𝔭 : (m : 𝓞 K) ∈ 𝔭.asIdeal) :
    𝔭.valuation K (b : K) = 1 := by
  have hlt : 𝔭.valuation K ((b : K) - 1) < 𝔭.valuation K (1 : K) := by
    rw [map_one]
    exact lt_of_le_of_lt (hcongK 𝔭 h𝔭)
      ((HeightOneSpectrum.intValuation_lt_one_iff_mem 𝔭 (m : 𝓞 K)).mpr h𝔭)
  have h := Valuation.map_add_eq_of_lt_left (v := 𝔭.valuation K) (x := (1 : K))
    (y := (b : K) - 1) hlt
  rwa [map_one, show (1 : K) + ((b : K) - 1) = (b : K) by ring] at h

/-- **The congruence step.**  If `b · s = r` for `r, s ∈ 𝓞 K` and `b ≡ 1 mod m` at all primes over
`m`, then `r - s ≡ 0 mod m`. -/
lemma sub_mem_span_of_mul_eq {K : Type*} [Field K] [NumberField K] (m : ℕ) (hm : m ≠ 0) (b : Kˣ)
    (hcongK : ∀ 𝔭 : HeightOneSpectrum (𝓞 K), (m : 𝓞 K) ∈ 𝔭.asIdeal →
      𝔭.valuation K ((b : K) - 1) ≤ 𝔭.intValuation (m : 𝓞 K))
    {r s : 𝓞 K} (h : (b : K) * (s : K) = (r : K)) :
    r - s ∈ Ideal.span {(m : 𝓞 K)} := by
  have harg : NumberField.RingOfIntegers.val (r - s)
      = ((b : K) - 1) * (NumberField.RingOfIntegers.val s) := by
    rw [show NumberField.RingOfIntegers.val (r - s)
        = NumberField.RingOfIntegers.val r - NumberField.RingOfIntegers.val s from by simp]
    rw [← h]
    ring
  refine mem_span_of_intValuation_le (R := 𝓞 K) (K := K) (m := (m : 𝓞 K))
    (show (m : 𝓞 K) ≠ 0 from Nat.cast_ne_zero.mpr hm) (y := r - s) (fun 𝔮 => ?_)
  have key : 𝔮.intValuation (r - s) = 𝔮.valuation K ((b : K) - 1) * 𝔮.intValuation s := by
    rw [← HeightOneSpectrum.valuation_of_algebraMap (K := K) 𝔮 (r - s)]
    change (HeightOneSpectrum.valuation K 𝔮) (NumberField.RingOfIntegers.val (r - s)) = _
    rw [harg]
    rw [map_mul, HeightOneSpectrum.valuation_of_algebraMap (K := K) 𝔮 s]
  by_cases hmem : (m : 𝓞 K) ∈ 𝔮.asIdeal
  · rw [key]
    calc 𝔮.valuation K ((b : K) - 1) * 𝔮.intValuation s
        ≤ 𝔮.intValuation (m : 𝓞 K) * 1 :=
          mul_le_mul' (hcongK 𝔮 hmem) (HeightOneSpectrum.intValuation_le_one 𝔮 s)
      _ = 𝔮.intValuation (m : 𝓞 K) := mul_one _
  · have hm1 : 𝔮.intValuation (m : 𝓞 K) = 1 :=
      le_antisymm (HeightOneSpectrum.intValuation_le_one 𝔮 (m : 𝓞 K))
        (le_of_not_gt (fun hlt =>
          hmem ((HeightOneSpectrum.intValuation_lt_one_iff_mem 𝔮 (m : 𝓞 K)).mp hlt)))
    rw [hm1]
    exact HeightOneSpectrum.intValuation_le_one 𝔮 (r - s)


theorem exists_denominator_ideal {K : Type*} [Field K] [NumberField K] (m : ℕ) (hm : 0 < m)
    (b : Kˣ)
    (hcong : ∀ 𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K),
      (m : NumberField.RingOfIntegers K) ∈ 𝔭.asIdeal →
        Valued.v (algebraMap K (𝔭.adicCompletion K) (b : K) - 1)
          ≤ Valued.v ((m : ℕ) : 𝔭.adicCompletion K)) :
    ∃ B : Ideal (NumberField.RingOfIntegers K),
      (∃ a : NumberField.RingOfIntegers K, a ∈ B ∧
        a - 1 ∈ Ideal.span {(m : NumberField.RingOfIntegers K)}) ∧
      (∃ y : NumberField.RingOfIntegers K, y ∈ B ∧ y ≠ 0) ∧
      (∀ x : NumberField.RingOfIntegers K, x ∈ B →
        ∃ p : NumberField.RingOfIntegers K,
          (p : K) = (b : K) * (x : K) ∧
          p - x ∈ Ideal.span {(m : NumberField.RingOfIntegers K)}) := by
  classical
  have hmvanish : (m : 𝓞 K) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.pos_iff_ne_zero.mp hm)
  have hmne : m ≠ 0 := Nat.pos_iff_ne_zero.mp hm
  have hcongK := valuation_sub_one_le_of_hcong (K := K) m b hcong
  -- a common denominator of `b`
  obtain ⟨p, q, hq, hpq⟩ := IsFractionRing.div_surjective (𝓞 K) (b : K)
  have hq0 : q ≠ 0 := mem_nonZeroDivisors_iff_ne_zero.mp hq
  have hqK : (q : K) ≠ 0 :=
    fun h0 => hq0 (IsFractionRing.injective (𝓞 K) K (by simpa using h0))
  have hqp : (b : K) * (q : K) = (p : K) := by
    rw [← hpq, div_mul_cancel₀ _ hqK]
  have hpq_mem : p - q ∈ Ideal.span {(m : 𝓞 K)} :=
    sub_mem_span_of_mul_eq (K := K) m hmne b hcongK (r := p) (s := q) hqp
  -- at each prime above `m`, a denominator of `b` which is a unit at that prime
  have hch : ∀ 𝔭 : {𝔭 : HeightOneSpectrum (𝓞 K) // (m : 𝓞 K) ∈ 𝔭.asIdeal},
      ∃ (n : 𝓞 K) (d : 𝔭.1.asIdeal.primeCompl), (b : K) * (d : 𝓞 K) = (n : K) := by
    intro 𝔭
    exact HeightOneSpectrum.exists_primeCompl_mul_eq_of_integer 𝔭.1 (b : K)
      (le_of_eq (valuation_eq_one_of_hcong (K := K) m b hcongK 𝔭.1 𝔭.2))
  choose n d hnd using hch
  -- the ideal generated by `q` and the local denominators
  let T : Set (𝓞 K) := {q} ∪ Set.range (fun 𝔭 : {𝔭 : HeightOneSpectrum (𝓞 K) //
      (m : 𝓞 K) ∈ 𝔭.asIdeal} => (d 𝔭 : 𝓞 K))
  let B : Ideal (𝓞 K) := Ideal.span T
  -- the ideal of all `x` with `b x ≡ x mod m`
  let Good : Ideal (𝓞 K) :=
    { carrier := {x : 𝓞 K | ∃ p : 𝓞 K,
        (p : K) = (b : K) * (x : K) ∧ p - x ∈ Ideal.span {(m : 𝓞 K)}}
      zero_mem' := ⟨0, by simp, by simp⟩
      add_mem' := by
        rintro x y ⟨p, hp, hpx⟩ ⟨p', hp', hp'x⟩
        refine ⟨p + p', ?_, ?_⟩
        · simp only [RingOfIntegers.val] at hp hp' ⊢
          rw [map_add, map_add, hp, hp']
          ring
        · rw [show (p + p') - (x + y) = (p - x) + (p' - y) by ring]
          exact Ideal.add_mem _ hpx hp'x
      smul_mem' := by
        rintro a x ⟨p, hp, hpx⟩
        refine ⟨a * p, ?_, ?_⟩
        · simp only [RingOfIntegers.val] at hp ⊢
          rw [map_mul, smul_eq_mul, map_mul, hp]
          ring
        · rw [show (a * p) - a • x = a * (p - x) by rw [smul_eq_mul]; ring]
          exact Ideal.mul_mem_left _ _ hpx }
  have hB_le : B ≤ Good := by
    change Ideal.span T ≤ Good
    rw [Ideal.span_le]
    intro x hx
    rcases hx with hx | ⟨𝔭, rfl⟩
    · rw [Set.mem_singleton_iff] at hx
      subst hx
      exact ⟨p, hqp.symm, hpq_mem⟩
    · exact ⟨n 𝔭, (hnd 𝔭).symm,
        sub_mem_span_of_mul_eq (K := K) m hmne b hcongK (r := n 𝔭) (s := (d 𝔭 : 𝓞 K)) (hnd 𝔭)⟩
  -- `B` is coprime to `(m)`
  have hsup : B ⊔ Ideal.span {(m : 𝓞 K)} = ⊤ := by
    by_contra hne
    obtain ⟨M, hmax, hle⟩ := Ideal.exists_le_maximal _ hne
    have hmM : (m : 𝓞 K) ∈ M :=
      hle (Submodule.mem_sup.mpr
        ⟨0, Submodule.zero_mem _, (m : 𝓞 K), Ideal.subset_span (Set.mem_singleton _), by simp⟩)
    have hMne : M ≠ ⊥ := fun h0 => hmvanish (by simpa [h0] using hmM)
    let 𝔭 : HeightOneSpectrum (𝓞 K) := ⟨M, hmax.isPrime, hMne⟩
    let 𝔭' : {𝔭 : HeightOneSpectrum (𝓞 K) // (m : 𝓞 K) ∈ 𝔭.asIdeal} := ⟨𝔭, hmM⟩
    have hdB : (d 𝔭' : 𝓞 K) ∈ B := Ideal.subset_span (Set.mem_union_right _ ⟨𝔭', rfl⟩)
    have hdM : (d 𝔭' : 𝓞 K) ∈ M :=
      hle (Submodule.mem_sup.mpr ⟨_, hdB, 0, Submodule.zero_mem _, by simp⟩)
    exact (d 𝔭').2 hdM
  obtain ⟨u, huB, v, hv, huv⟩ := Submodule.mem_sup.mp
    (show (1 : 𝓞 K) ∈ B ⊔ Ideal.span {(m : 𝓞 K)} from hsup.symm ▸ Submodule.mem_top)
  refine ⟨B, ⟨u, huB, ?_⟩, ⟨q, ?_, hq0⟩, fun x hx => hB_le hx⟩
  · rw [show u - 1 = -v by rw [← huv]; ring]
    exact (Ideal.neg_mem_iff _).mpr hv
  · exact Ideal.subset_span (Set.mem_union_left _ rfl)

/-! ## The converse direction, and the resulting characterisation -/

/-- The converse of `mem_span_of_intValuation_le`: membership in the principal ideal `(m)` implies
the local conditions. -/
lemma intValuation_le_of_mem_span {R : Type*} [CommRing R] [IsDedekindDomain R]
    {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K] {m y : R}
    (h : y ∈ Ideal.span {m}) (v : HeightOneSpectrum R) :
    v.intValuation y ≤ v.intValuation m := by
  rw [Ideal.mem_span_singleton] at h
  obtain ⟨z, rfl⟩ := h
  rw [map_mul]
  calc v.intValuation m * v.intValuation z ≤ v.intValuation m * 1 :=
        mul_le_mul_of_nonneg_left (HeightOneSpectrum.intValuation_le_one v z) zero_le
    _ = v.intValuation m := mul_one _

/-- **The local characterisation of a principal ideal of a Dedekind domain:** `m ∣ y` if and only
if at every height-one prime the `v`-adic valuation of `y` is at least that of `m`. -/
lemma mem_span_iff_intValuation_le {R : Type*} [CommRing R] [IsDedekindDomain R]
    {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K] {m y : R} (hm : m ≠ 0) :
    y ∈ Ideal.span {m} ↔ ∀ v : HeightOneSpectrum R, v.intValuation y ≤ v.intValuation m :=
  ⟨fun h v => intValuation_le_of_mem_span (K := K) h v,
    fun h => mem_span_of_intValuation_le (K := K) (m := m) hm h⟩


end NK.CFTLib.Arl
