import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.PicardGroup
import Mathlib.Tactic.Have
import Mathlib.RingTheory.AdicCompletion.Noetherian
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.NumberTheory.NumberField.Completion.FinitePlace
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

open scoped WithZero NNReal Topology
open IsDedekindDomain Valuation MonoidWithZeroHom Filter
noncomputable section
set_option autoImplicit false

namespace Commons.RingTheory.Henselian

-- value-group helpers ----------------------------------------------------

/-- Powers of an element of `ℤᵐ⁰` which is positive and below `1` are eventually below any
positive element. -/
lemma exists_forall_pow_lt_of_lt_one {q c : ℤᵐ⁰} (hq1 : q < 1) (hc0 : c ≠ 0) :
    ∃ N : ℕ, ∀ n ≥ N, q ^ n < c := by
  let abv : ℤᵐ⁰ →*₀ ℝ≥0 := WithZeroMulInt.toNNReal (by norm_num : (2 : ℝ≥0) ≠ 0)
  have habv_sm : StrictMono abv := WithZeroMulInt.toNNReal_strictMono (by norm_num : 1 < (2 : ℝ≥0))
  have hcq_ne : abv c ≠ 0 := by
    intro h
    exact hc0 ((MonoidWithZeroHom.map_eq_zero_iff (f := abv)).mp h)
  have hcq_pos : 0 < abv c := pos_iff_ne_zero.mpr hcq_ne
  have hr_lt1 : abv q < 1 := by
    simpa using (habv_sm.lt_iff_lt (f := abv) (a := q) (b := 1)).2 hq1
  obtain ⟨N, hN⟩ := exists_pow_lt_of_lt_one hcq_pos hr_lt1
  refine ⟨N, fun n hn => ?_⟩
  rw [← (habv_sm.lt_iff_lt (f := abv) (a := q ^ n) (b := c))]
  rw [map_pow]
  exact lt_of_le_of_lt
    (pow_le_pow_of_le_one (a := abv q) bot_le (le_of_lt hr_lt1) hn) hN

-- local ring data --------------------------------------------------------

noncomputable def uniformizer {R K : Type*} [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K]
    [IsFractionRing R K] (v : IsDedekindDomain.HeightOneSpectrum R) : v.adicCompletionIntegers K :=
  Classical.choose (IsDiscreteValuationRing.exists_irreducible (v.adicCompletionIntegers K))

lemma uniformizer_irreducible {R K : Type*} [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K]
    [IsFractionRing R K] (v : IsDedekindDomain.HeightOneSpectrum R) :
    Irreducible (uniformizer (R := R) (K := K) v) := by
  dsimp [uniformizer]
  exact Classical.choose_spec (IsDiscreteValuationRing.exists_irreducible (v.adicCompletionIntegers K))

lemma maximalIdeal_eq_span_uniformizer {R K : Type*} [CommRing R] [IsDedekindDomain R] [Field K]
    [Algebra R K] [IsFractionRing R K] (v : IsDedekindDomain.HeightOneSpectrum R) :
    IsLocalRing.maximalIdeal (v.adicCompletionIntegers K) = Ideal.span {uniformizer (R := R) (K := K) v} :=
  (uniformizer_irreducible (R := R) (K := K) v).maximalIdeal_eq

lemma mem_pow_maximalIdeal_iff {R K : Type*} [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K]
    [IsFractionRing R K] (v : IsDedekindDomain.HeightOneSpectrum R) (n : ℕ)
    (y : v.adicCompletionIntegers K) :
    y ∈ (IsLocalRing.maximalIdeal (v.adicCompletionIntegers K) ^ n : Ideal (v.adicCompletionIntegers K)) ↔
      Valued.v (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) y) ≤
        (Valued.v (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K)
          (uniformizer (R := R) (K := K) v))) ^ n := by
  rw [maximalIdeal_eq_span_uniformizer (R := R) (K := K) v, Ideal.span_singleton_pow]
  rw [Ideal.mem_span_singleton]
  rw [Valuation.Integers.dvd_iff_le (IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers.integers K v)
    (x := uniformizer (R := R) (K := K) v ^ n) (y := y)]
  simp [map_pow]

lemma uniformizer_val_ne_zero {R K : Type*} [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K]
    [IsFractionRing R K] (v : IsDedekindDomain.HeightOneSpectrum R) :
    Valued.v (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K)
      (uniformizer (R := R) (K := K) v)) ≠ 0 := by
  intro h
  apply (uniformizer_irreducible (R := R) (K := K) v).ne_zero
  apply (IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers.integers K v).hom_inj
  simpa using ((Valuation.zero_iff (v := Valued.v)).mp h)

lemma uniformizer_val_lt_one {R K : Type*} [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K]
    [IsFractionRing R K] (v : IsDedekindDomain.HeightOneSpectrum R) :
    Valued.v (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K)
      (uniformizer (R := R) (K := K) v)) < 1 := by
  let ϖ := uniformizer (R := R) (K := K) v
  have hle : Valued.v (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) ϖ) ≤ 1 :=
    Valuation.Integers.map_le_one (IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers.integers K v) ϖ
  have hne : Valued.v (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) ϖ) ≠ 1 := by
    intro h
    exact (uniformizer_irreducible (R := R) (K := K) v).not_isUnit
      ((Valuation.Integers.isUnit_iff_valuation_eq_one
        (IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers.integers K v)).2 h)
  exact lt_of_le_of_ne hle hne

theorem cong_value_bound {R K : Type*} [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K]
    [IsFractionRing R K] (v : IsDedekindDomain.HeightOneSpectrum R)
    (x : ℕ → v.adicCompletionIntegers K)
    (hx : ∀ {m n : ℕ}, m ≤ n →
      x m ≡ x n [SMOD ((IsLocalRing.maximalIdeal (v.adicCompletionIntegers K)) ^ m • ⊤ :
        Submodule (v.adicCompletionIntegers K) (v.adicCompletionIntegers K))]) :
    ∀ {m n : ℕ}, m ≤ n →
      Valued.v ((x m : v.adicCompletion K) - (x n : v.adicCompletion K)) ≤
        (Valued.v (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K)
          (uniformizer (R := R) (K := K) v))) ^ m := by
  intro m n hmn
  have hmem : x m - x n ∈ (IsLocalRing.maximalIdeal (v.adicCompletionIntegers K) ^ m :
      Ideal (v.adicCompletionIntegers K)) := by
    have h := hx hmn
    rw [SModEq.sub_mem] at h
    simpa [← Ideal.one_eq_top, Ideal.smul_eq_mul] using h
  rw [mem_pow_maximalIdeal_iff (R := R) (K := K) v m (x m - x n)] at hmem
  simpa using hmem



theorem isPrecomplete_adicCompletionIntegers {R K : Type*} [CommRing R] [IsDedekindDomain R]
    [Field K] [Algebra R K] [IsFractionRing R K] (v : IsDedekindDomain.HeightOneSpectrum R) :
    IsPrecomplete (IsLocalRing.maximalIdeal (v.adicCompletionIntegers K)) (v.adicCompletionIntegers K) := by
  refine ⟨fun x hx => ?_⟩
  let q : ℤᵐ⁰ := Valued.v (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K)
      (uniformizer (R := R) (K := K) v))
  have hq1 : q < 1 := uniformizer_val_lt_one (R := R) (K := K) v
  have hCauchy : Cauchy (atTop.map fun n : ℕ => (x n : v.adicCompletion K)) := by
    rw [Valued.cauchy_iff]
    refine ⟨?_, ?_⟩
    · exact Filter.NeBot.map (inferInstance : NeBot atTop) (fun n : ℕ => (x n : v.adicCompletion K))
    · intro γ
      let VG : Type := ((Valued.v : Valuation (v.adicCompletion K) ℤᵐ⁰) : v.adicCompletion K →*₀ ℤᵐ⁰).ValueGroup₀
      let emb : VG →*₀ ℤᵐ⁰ := MonoidWithZeroHom.ValueGroup₀.embedding
      have hγ0 : emb (γ : VG) ≠ 0 := by
        intro h
        exact (Units.ne_zero γ) ((MonoidWithZeroHom.map_eq_zero_iff (f := emb)).mp h)
      obtain ⟨N, hN⟩ := exists_forall_pow_lt_of_lt_one hq1 hγ0
      refine ⟨{a : v.adicCompletion K | ∃ n : ℕ, N ≤ n ∧ (x n : v.adicCompletion K) = a}, ?_, ?_⟩
      · rw [Filter.mem_map]
        exact eventually_atTop.2 ⟨N, fun n hn => ⟨n, hn, rfl⟩⟩
      · intro a ha b hb
        rcases ha with ⟨m, hmN, rfl⟩
        rcases hb with ⟨n, hnN, rfl⟩
        have prove : ∀ {m n : ℕ}, N ≤ m → N ≤ n → m ≤ n →
            Valued.v.restrict ((x n : v.adicCompletion K) - (x m : v.adicCompletion K)) < (γ : VG) := by
          intro m n hmN' hnN' hmn
          have hb : Valued.v ((x m : v.adicCompletion K) - (x n : v.adicCompletion K)) ≤ q ^ m :=
            cong_value_bound (R := R) (K := K) v x hx hmn
          have hq : q ^ m < emb (γ : VG) := hN m hmN'
          have hlt : Valued.v ((x m : v.adicCompletion K) - (x n : v.adicCompletion K)) <
              emb (γ : VG) := lt_of_le_of_lt hb hq
          rw [Valuation.restrict_lt_iff_lt_embedding]
          rw [← Valuation.map_sub_swap (v := (Valued.v : Valuation (v.adicCompletion K) ℤᵐ⁰))
            (x := (x m : v.adicCompletion K)) (y := (x n : v.adicCompletion K))]
          simpa [emb] using hlt
        by_cases h : m ≤ n
        · exact prove hmN hnN h
        · have hnm : n ≤ m := by omega
          have h' : Valued.v.restrict ((x m : v.adicCompletion K) - (x n : v.adicCompletion K)) < (γ : VG) :=
            prove hnN hmN hnm
          rw [Valuation.map_sub_swap (Valued.v.restrict) (x := (x n : v.adicCompletion K))
            (y := (x m : v.adicCompletion K))]
          exact h'
  obtain ⟨L, hL⟩ := CompleteSpace.complete hCauchy
  have hclosedA : IsClosed ((v.adicCompletionIntegers K : Set (v.adicCompletion K))) := by
    exact Valued.isClosed_valuationSubring (v.adicCompletion K)
  have hLA : L ∈ (v.adicCompletionIntegers K : Set (v.adicCompletion K)) := by
    have hL' : Tendsto (fun n : ℕ => (x n : v.adicCompletion K)) atTop (𝓝 L) := hL
    exact hclosedA.mem_of_tendsto hL' (Filter.Eventually.of_forall (by intro n; exact (x n).2))
  let LA : v.adicCompletionIntegers K := ⟨L, hLA⟩
  refine ⟨LA, ?_⟩
  intro n
  let ϖ : v.adicCompletionIntegers K := uniformizer (R := R) (K := K) v
  have hball : IsClosed {z : v.adicCompletion K |
      Valued.v.restrict z ≤ Valued.v.restrict ((algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) ϖ) ^ n)} := by
    exact Valued.isClosed_closedBall (v.adicCompletion K)
      (Valued.v.restrict ((algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) ϖ) ^ n))
  have htend : Tendsto (fun N : ℕ => (x n : v.adicCompletion K) - (x N : v.adicCompletion K)) atTop
      (𝓝 ((x n : v.adicCompletion K) - L)) := by
    have hcst : Tendsto (fun _ : ℕ => (x n : v.adicCompletion K)) atTop (𝓝 ((x n : v.adicCompletion K))) := tendsto_const_nhds
    exact hcst.sub hL
  have hev : ∀ᶠ N : ℕ in atTop, (x n : v.adicCompletion K) - (x N : v.adicCompletion K) ∈
      {z : v.adicCompletion K | Valued.v.restrict z ≤
        Valued.v.restrict ((algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) ϖ) ^ n)} := by
    refine eventually_atTop.2 ⟨n, fun N hN => ?_⟩
    have hb := cong_value_bound (R := R) (K := K) v x hx hN
    rw [Set.mem_ofPred_eq, Valuation.restrict_le_iff (Valued.v : Valuation (v.adicCompletion K) ℤᵐ⁰)]
    simpa [q, map_pow] using hb
  have hmemBall : (x n : v.adicCompletion K) - L ∈
      {z : v.adicCompletion K | Valued.v.restrict z ≤
        Valued.v.restrict ((algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) ϖ) ^ n)} :=
    IsClosed.mem_of_tendsto hball htend hev
  have hval : Valued.v ((x n : v.adicCompletion K) - L) ≤ q ^ n := by
    have hmono : Monotone (MonoidWithZeroHom.ValueGroup₀.embedding
        (f := ((Valued.v : Valuation (v.adicCompletion K) ℤᵐ⁰) : v.adicCompletion K →*₀ ℤᵐ⁰))) :=
      (MonoidWithZeroHom.ValueGroup₀.embedding_strictMono
        (f := ((Valued.v : Valuation (v.adicCompletion K) ℤᵐ⁰) : v.adicCompletion K →*₀ ℤᵐ⁰))).monotone
    simpa [q, map_pow, Valuation.embedding_restrict] using hmono hmemBall
  have hmem : (x n - LA : v.adicCompletionIntegers K) ∈
      (IsLocalRing.maximalIdeal (v.adicCompletionIntegers K) ^ n : Ideal (v.adicCompletionIntegers K)) := by
    rw [mem_pow_maximalIdeal_iff (R := R) (K := K) v n (x n - LA)]
    simpa [sub_eq_add_neg, q, LA] using hval
  rw [SModEq.sub_mem]
  simpa [← Ideal.one_eq_top, Ideal.smul_eq_mul, LA] using hmem



/-- The ring of integers of the `v`-adic completion of `K` (a complete discrete valuation ring)
is a Henselian local ring. -/
theorem adicCompletionIntegers_henselianLocalRing
    {R K : Type*} [CommRing R] [Field K] [Algebra R K] [IsDedekindDomain R]
    [IsFractionRing R K]
    (v : IsDedekindDomain.HeightOneSpectrum R) :
    HenselianLocalRing (v.adicCompletionIntegers K) := by
  letI : IsAdicComplete (IsLocalRing.maximalIdeal (v.adicCompletionIntegers K)) (v.adicCompletionIntegers K) :=
    { toIsHausdorff := (inferInstance : IsHausdorff (IsLocalRing.maximalIdeal (v.adicCompletionIntegers K))
        (v.adicCompletionIntegers K))
      toIsPrecomplete := isPrecomplete_adicCompletionIntegers (R := R) (K := K) v }
  letI : HenselianRing (v.adicCompletionIntegers K) (IsLocalRing.maximalIdeal (v.adicCompletionIntegers K)) :=
    IsAdicComplete.henselianRing (v.adicCompletionIntegers K)
      (IsLocalRing.maximalIdeal (v.adicCompletionIntegers K))
  refine { toIsLocalRing := inferInstance, is_henselian := ?_ }
  intro f hf a₀ h₁ h₂
  have h₂' : IsUnit ((Ideal.Quotient.mk (IsLocalRing.maximalIdeal (v.adicCompletionIntegers K)))
      (f.derivative.eval a₀)) := by
    simpa using (Ideal.Quotient.mk (IsLocalRing.maximalIdeal (v.adicCompletionIntegers K))).isUnit_map h₂
  exact (HenselianRing.is_henselian (R := v.adicCompletionIntegers K)
    (I := IsLocalRing.maximalIdeal (v.adicCompletionIntegers K)) f hf a₀ h₁ h₂')

end Commons.RingTheory.Henselian