import Mathlib
import Submission.NK.GlobalCFT.IdeleClassGroup
import Submission.NK.Reconstruct.GammaDual
import Submission.NK.RankTheoryDeep.IdeleRankDefs
import Submission.NK.NUV2.LocalUnitsAux
import Submission.NK.NUV2.PrincipalUnitBall
import Submission.NK.LocalInputs.Defs
import Submission.NK.LocalInputs.Inputs
import Submission.NK.LocalInputs.Degree.localDegree_eq_ramificationIdx_mul_inertiaDeg
import Submission.NK.LocalInputs.ResidueChar.primesEquiv_primeBelow
import Submission.NK.ReconstructField.finrank_eq_of_localCorrespondence
import Submission.Commons.Analysis.Nonarchimedean.exists_exp_log_adicCompletion_log_val_eq
import Submission.Commons.NumberTheory.NumberField.Completion.module_finite_adicCompletionIntegers
import Submission.Commons.NumberTheory.NumberField.Completion.module_free_adicCompletionIntegers
import Submission.Commons.NumberTheory.NumberField.Completion.trace_adicCompletionIntegers_mem
import Submission.Commons.NumberTheory.NumberField.Completion.exists_trace_eq_one_adicCompletion
import Submission.Commons.NumberTheory.NumberField.Completion.finrank_adicCompletion_eq_ramificationIdx_mul_inertiaDeg
import Submission.NK.NUV2.natCard_quotient_maximalIdeal_pow
import Submission.NK.NUV2.two_span_eq_maximalIdeal_pow
import Submission.NK.NUV2.localUnitLogStructure

set_option maxHeartbeats 4000000

namespace NK.NUV2

/-! ## Part 1: the transfer lemma

A finite-index subgroup `H ≤ A` has dual of *no larger* rank: the transfer (here the explicit
power map `a ↦ a ^ [A : H]`) exhibits `Dual H` as a submodule of `Dual A`. -/

/-- **A finite-index subgroup has dual rank at most that of the ambient group.**  Precomposition
with the `[A : H]`-th power map `A →* H` (defined because `a ^ [A : H] ∈ H`) makes the dual of `H`
a submodule of the dual of `A`; on `H` this map is multiplication by the (nonzero) index, so it is
injective. -/
theorem rank_dual_le_rank_dual_of_finiteIndex {A : Type*} [CommGroup A] [TopologicalSpace A]
    [ContinuousMul A] {ℓ : ℕ} [Fact ℓ.Prime] (H : Subgroup A) [H.FiniteIndex] :
    Module.rank (PadicInt ℓ) (NK.Reconstruct.Dual ↥H ℓ) ≤
      Module.rank (PadicInt ℓ) (NK.Reconstruct.Dual A ℓ) := by
  classical
  haveI : H.Normal := Subgroup.normal_of_isMulCommutative H
  let ψ : A →* ↥H :=
    { toFun := fun a => ⟨a ^ H.index, Subgroup.pow_index_mem H a⟩
      map_one' := by ext; exact one_pow _
      map_mul' := by intro a b; ext; exact mul_pow a b _ }
  have hψ_cont : Continuous ⇑ψ :=
    Continuous.subtype_mk (continuous_pow (M := A) H.index) _
  let Φ : NK.Reconstruct.Dual ↥H ℓ →ₗ[PadicInt ℓ] NK.Reconstruct.Dual A ℓ :=
    { toFun := fun f => ⟨f.1.comp (MonoidHom.toAdditive ψ), by
        show Continuous ((f.1 : Additive ↥H →+ PadicInt ℓ) ∘ ⇑(MonoidHom.toAdditive ψ))
        exact f.2.comp hψ_cont⟩
      map_add' := by intro x y; rfl
      map_smul' := by intro a x; rfl }
  have hψ_eq : ∀ h : ↥H, ψ (h : A) = h ^ H.index := fun h => Subtype.ext rfl
  have hinj : Function.Injective Φ := by
    intro f g hfg
    apply Subtype.ext
    refine AddMonoidHom.ext fun x => ?_
    set h : ↥H := Additive.toMul x with hh
    have h1 : Φ f (Additive.ofMul (h : A)) = Φ g (Additive.ofMul (h : A)) := by rw [hfg]
    have h2 : ∀ k : NK.Reconstruct.Dual ↥H ℓ,
        Φ k (Additive.ofMul (h : A)) = H.index • k (Additive.ofMul h) := by
      intro k
      change k.1 (MonoidHom.toAdditive ψ (Additive.ofMul (h : A))) = _
      have hstep : MonoidHom.toAdditive ψ (Additive.ofMul (h : A)) =
          Additive.ofMul (h ^ H.index) := by
        rw [← hψ_eq h]
        rfl
      rw [hstep, LocalUnitsAux.additive_ofMul_pow, map_nsmul]
    rw [h2 f, h2 g] at h1
    have hne : (H.index : PadicInt ℓ) ≠ 0 := by
      exact_mod_cast (Subgroup.FiniteIndex.index_ne_zero (H := H))
    have h3 : f (Additive.ofMul h) = g (Additive.ofMul h) := by
      refine mul_left_cancel₀ hne ?_
      simpa [nsmul_eq_mul] using h1
    have hx : x = Additive.ofMul h := by rw [hh]; exact (ofMul_toMul x).symm
    rw [hx]
    exact h3
  exact Cardinal.lift_le.mp (Φ.lift_rank_le_of_injective hinj)

/-! ## Part 2: a continuity criterion

A homomorphism into a *discrete* topological group is continuous as soon as its kernel is open
(equivalently: as soon as it kills an open subgroup). -/

/-- **A homomorphism with open kernel into a discrete group is continuous.** -/
theorem continuous_of_isOpen_ker {A : Type*} [AddCommGroup A] [UniformSpace A]
    [IsUniformAddGroup A] {B : Type*} [AddCommGroup B] [UniformSpace B] [DiscreteTopology B]
    [IsUniformAddGroup B] (f : A →+ B) (h : IsOpen (f.ker : Set A)) : Continuous f :=
  ((IsUniformAddGroup.uniformContinuous_iff_isOpen_ker (f := f)).mpr h).continuous

/-! ## Part 3: the rational prime `2` as a prime of `𝓞 ℚ` -/

/-- The rational prime `2`, as a height-one prime of `𝓞 ℚ`. -/
noncomputable def basePrime : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ℚ) :=
  Rat.HeightOneSpectrum.primesEquiv.symm ⟨2, Nat.prime_two⟩

theorem primesEquiv_basePrime :
    Rat.HeightOneSpectrum.primesEquiv basePrime = ⟨2, Nat.prime_two⟩ :=
  Equiv.apply_symm_apply _ _

/-- **A finite prime lying over `(2)` also lies over `basePrime`.** -/
theorem liesOver_basePrime {K : Type*} [Field K] [NumberField K]
    (q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (hq : q.asIdeal.LiesOver (Ideal.span {(2 : ℤ)})) :
    q.asIdeal.LiesOver (basePrime).asIdeal := by
  have h2mem : (2 : NumberField.RingOfIntegers K) ∈ q.asIdeal := by
    have h := (Ideal.mem_of_liesOver (P := q.asIdeal) (p := (Ideal.span {(2 : ℤ)}))
      (A := ℤ) (B := NumberField.RingOfIntegers K) (2 : ℤ)).mp
      (Ideal.mem_span_singleton_self (2 : ℤ))
    simpa using h
  have hgen : Rat.HeightOneSpectrum.natGenerator (NK.LocalInputs.primeBelow K q) = 2 := by
    have hdvd := NK.LocalInputs.ResidueChar.natGenerator_primeBelow_dvd (K := K) q h2mem
    have hne : Rat.HeightOneSpectrum.natGenerator (NK.LocalInputs.primeBelow K q) ≠ 1 :=
      (Rat.HeightOneSpectrum.prime_natGenerator _).ne_one
    exact ((Nat.Prime.dvd_iff_eq Nat.prime_two hne).mp hdvd).symm
  have hEq : NK.LocalInputs.primeBelow K q = basePrime := by
    apply Rat.HeightOneSpectrum.primesEquiv.injective
    apply Subtype.ext
    rw [primesEquiv_basePrime]
    exact hgen
  rw [← hEq]
  exact NK.LocalInputs.primeBelow_liesOver K q

theorem localUnitDualRank_lowerBound (K : Type) [Field K] [NumberField K]
    (q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (hq : q.asIdeal.LiesOver (Ideal.span {(2 : ℤ)})) :
    (((q.asIdeal.ramificationIdx ℤ * q.asIdeal.inertiaDeg ℤ : ℕ)) : Cardinal) ≤
      Module.rank (PadicInt 2)
        (NK.Reconstruct.Dual
          (↥(NK.GlobalCFT.Place.localUnits K (NK.GlobalCFT.Place.ofFinite q))) 2) := by
  classical
  -- ## Setup: the base field `ℚ_2`, the local field `F = K_q`, and the two rings of integers
  have hQ : q.asIdeal.LiesOver (basePrime).asIdeal := liesOver_basePrime q hq
  letI : Algebra (basePrime.adicCompletion ℚ) (q.adicCompletion K) :=
    RingHom.toAlgebra (Commons.RingTheory.Henselian.adicCompletionMap basePrime q hQ)
  letI : Algebra (basePrime.adicCompletionIntegers ℚ) (q.adicCompletion K) :=
    RingHom.toAlgebra ((Commons.RingTheory.Henselian.adicCompletionMap basePrime q hQ).comp
      (basePrime.adicCompletionIntegers ℚ).subtype)
  letI : Algebra (basePrime.adicCompletionIntegers ℚ) (q.adicCompletionIntegers K) :=
    RingHom.toAlgebra (((Commons.RingTheory.Henselian.adicCompletionMap basePrime q hQ).comp
      (basePrime.adicCompletionIntegers ℚ).subtype).codRestrict (q.adicCompletionIntegers K)
      (fun x => Commons.RingTheory.Henselian.adicCompletionMap_mem_integers basePrime q hQ x.2))
  haveI hTowerL : IsScalarTower (basePrime.adicCompletionIntegers ℚ) (basePrime.adicCompletion ℚ)
      (q.adicCompletion K) := IsScalarTower.of_algebraMap_eq fun _ => rfl
  haveI hTowerO : IsScalarTower (basePrime.adicCompletionIntegers ℚ) (q.adicCompletionIntegers K)
      (q.adicCompletion K) := IsScalarTower.of_algebraMap_eq fun _ => rfl
  haveI hFin : FiniteDimensional (basePrime.adicCompletion ℚ) (q.adicCompletion K) :=
    Commons.NumberTheory.NumberField.Completion.module_finite_adicCompletion basePrime q hQ
  haveI hIntClos : IsIntegralClosure (q.adicCompletionIntegers K)
      (basePrime.adicCompletionIntegers ℚ) (q.adicCompletion K) :=
    Commons.NumberTheory.NumberField.Completion.isIntegralClosure_adicCompletionIntegers_extension
      basePrime q hQ
  haveI : IsFractionRing (basePrime.adicCompletionIntegers ℚ) (basePrime.adicCompletion ℚ) :=
    inferInstance
  haveI : CharZero (basePrime.adicCompletion ℚ) :=
    charZero_of_injective_algebraMap (algebraMap ℚ (basePrime.adicCompletion ℚ)).injective
  haveI : Algebra.IsSeparable (basePrime.adicCompletion ℚ) (q.adicCompletion K) := inferInstance
  -- ## the local degree is `e · f`
  set n : ℕ := q.asIdeal.ramificationIdx ℤ * q.asIdeal.inertiaDeg ℤ with hn
  have hdeg : Module.finrank (basePrime.adicCompletion ℚ) (q.adicCompletion K) = n := by
    rw [← Commons.NumberTheory.NumberField.Completion.finrank_adicCompletion_eq_ramificationIdx_mul_inertiaDeg
      (K := ℚ) (L := K) basePrime q hQ,
      NK.LocalInputs.Degree.ramificationIdx_rat_eq q.asIdeal q.ne_bot,
      NK.LocalInputs.Degree.inertiaDeg_rat_eq q.asIdeal q.ne_bot, hn]
  -- ## `2 ∈ 𝔪`, hence `v 2 < 1`
  have he_ne : q.asIdeal.ramificationIdx ℤ ≠ 0 := by
    haveI : q.asIdeal.IsPrime := q.isPrime
    exact (q.asIdeal.ramificationIdx_pos ℤ).ne'
  have h2mem : (2 : q.adicCompletionIntegers K) ∈
      IsLocalRing.maximalIdeal (q.adicCompletionIntegers K) :=
    (Ideal.pow_le_self he_ne) (by
      rw [← NK.NUV2.two_span_eq_maximalIdeal_pow K q hq]
      exact Ideal.mem_span_singleton_self 2)
  have h2v_le : Valued.v (R := q.adicCompletion K) (Γ₀ := WithZero (Multiplicative ℤ))
      (2 : q.adicCompletion K) ≤ WithZero.exp (-(1 : ℤ)) := by
    have h := (Commons.NumberTheory.NumberField.Completion.val_le_exp_neg_iff_mem_maximalIdeal_pow
      q (2 : q.adicCompletionIntegers K) 1).mpr (by simpa using h2mem)
    rwa [show ((2 : q.adicCompletionIntegers K) : q.adicCompletion K) = (2 : q.adicCompletion K)
      from rfl] at h
  have h2v_lt : Valued.v (R := q.adicCompletion K) (Γ₀ := WithZero (Multiplicative ℤ))
      (2 : q.adicCompletion K) < 1 := by
    refine lt_of_le_of_lt h2v_le ?_
    rw [show (1 : WithZero (Multiplicative ℤ)) = WithZero.exp (0 : ℤ) from (WithZero.exp_zero).symm,
      WithZero.exp_lt_exp]
    omega
  -- ## the covering statement `F = L · 𝒪`
  have hcover : ∀ y : q.adicCompletion K, ∃ k : ℕ,
      (2 : q.adicCompletion K) ^ k * y ∈ q.adicCompletionIntegers K := by
    intro y
    rcases eq_or_ne y 0 with rfl | hy
    · refine ⟨0, ?_⟩
      rw [pow_zero, one_mul]
      exact (q.adicCompletionIntegers K).zero_mem
    · set n : ℤ := (Valued.v (R := q.adicCompletion K)
        (Γ₀ := WithZero (Multiplicative ℤ)) y).log with hn
      set m : ℤ := (Valued.v (R := q.adicCompletion K)
        (Γ₀ := WithZero (Multiplicative ℤ)) (2 : q.adicCompletion K)).log with hm
      have hvy : Valued.v (R := q.adicCompletion K) (Γ₀ := WithZero (Multiplicative ℤ)) y =
          WithZero.exp n := by
        rw [hn, WithZero.exp_log]
        exact (Valuation.ne_zero_iff _).mpr hy
      have hv2 : Valued.v (R := q.adicCompletion K) (Γ₀ := WithZero (Multiplicative ℤ))
          (2 : q.adicCompletion K) = WithZero.exp m := by
        rw [hm, WithZero.exp_log]
        exact (Valuation.ne_zero_iff _).mpr (by
          haveI : CharZero (q.adicCompletion K) :=
            Commons.NumberTheory.NumberField.charZero_adicCompletion q
          norm_num)
      have hm_le : m ≤ -1 := by
        have h : WithZero.exp m < WithZero.exp (0 : ℤ) := by
          rw [← hv2, WithZero.exp_zero]
          exact h2v_lt
        have h' := WithZero.exp_lt_exp.mp h
        omega
      refine ⟨(max 0 n).toNat, ?_⟩
      rw [IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers]
      have hk : n ≤ (((max 0 n).toNat : ℕ) : ℤ) := by
        rw [Int.toNat_of_nonneg (le_max_left (0 : ℤ) n)]
        exact le_max_right 0 n
      rw [map_mul, map_pow, hv2, hvy, ← WithZero.exp_nsmul, ← WithZero.exp_add,
        show (1 : WithZero (Multiplicative ℤ)) = WithZero.exp (0 : ℤ) from (WithZero.exp_zero).symm,
        WithZero.exp_le_exp]
      rw [nsmul_eq_mul]
      have hk0 : (0 : ℤ) ≤ (((max 0 n).toNat : ℕ) : ℤ) := Int.natCast_nonneg _
      nlinarith [hk, hm_le, hk0]
  -- the same covering statement, with the base-field scalar
  have hcoverL : ∀ y : q.adicCompletion K, ∃ k : ℕ,
      (2 : basePrime.adicCompletion ℚ) ^ k • y ∈ q.adicCompletionIntegers K := by
    intro y
    obtain ⟨k, hk⟩ := hcover y
    refine ⟨k, ?_⟩
    have hpow : (2 : basePrime.adicCompletion ℚ) ^ k • y = (2 : q.adicCompletion K) ^ k * y := by
      rw [Algebra.smul_def, map_pow, map_ofNat]
    rwa [hpow]
  -- ## a basis of `F` over `L` and the integral elements `u i`
  let b₀ : Module.Basis (Fin (Module.finrank (basePrime.adicCompletion ℚ) (q.adicCompletion K)))
      (basePrime.adicCompletion ℚ) (q.adicCompletion K) := Module.finBasis _ _
  let b : Module.Basis (Fin n) (basePrime.adicCompletion ℚ) (q.adicCompletion K) :=
    b₀.reindex (finCongr hdeg)
  choose k hk using fun i : Fin n => hcoverL (b i)
  let u : Fin n → q.adicCompletionIntegers K := fun i =>
    ⟨(2 : basePrime.adicCompletion ℚ) ^ k i • (b i), hk i⟩
  have hu : ∀ i, (u i : q.adicCompletion K) = (2 : basePrime.adicCompletion ℚ) ^ k i • (b i) :=
    fun i => rfl
  have huLI : LinearIndependent (basePrime.adicCompletion ℚ)
      (fun i => (u i : q.adicCompletion K)) := by
    rw [linearIndependent_iff']
    intro s g hsum i hi
    have hb := Module.Basis.linearIndependent b
    rw [linearIndependent_iff'] at hb
    have h1 : ∑ j ∈ s, (g j * (2 : basePrime.adicCompletion ℚ) ^ k j) • (b j) = 0 := by
      rw [← hsum]
      refine Finset.sum_congr rfl fun j hj => ?_
      rw [hu j, mul_smul]
    have h2 := hb s (fun j => g j * (2 : basePrime.adicCompletion ℚ) ^ (k j)) h1 i hi
    rcases mul_eq_zero.mp h2 with h | h
    · exact h
    · exact absurd h (pow_ne_zero _ (by
        haveI : CharZero (basePrime.adicCompletion ℚ) :=
          Commons.NumberTheory.NumberField.charZero_adicCompletion basePrime
        norm_num))
  -- ## integrality of the trace, and the trace functionals `Lam i`
  have hInt : ∀ y : q.adicCompletionIntegers K,
      Algebra.trace (basePrime.adicCompletion ℚ) (q.adicCompletion K) (y : q.adicCompletion K) ∈
        (basePrime.adicCompletionIntegers ℚ : Set (basePrime.adicCompletion ℚ)) := by
    intro y
    have hy : IsIntegral (basePrime.adicCompletionIntegers ℚ) (y : q.adicCompletion K) :=
      IsIntegralClosure.isIntegral_iff.mpr ⟨y, rfl⟩
    have htr := Algebra.isIntegral_trace (R := basePrime.adicCompletionIntegers ℚ)
      (L := basePrime.adicCompletion ℚ) (F := q.adicCompletion K) hy
    obtain ⟨a, ha⟩ := IsIntegrallyClosed.isIntegral_iff.mp htr
    rw [← ha]
    exact a.2
  let Lam : Fin n → (q.adicCompletionIntegers K) → (basePrime.adicCompletionIntegers ℚ) :=
    fun i y => ⟨Algebra.trace (basePrime.adicCompletion ℚ) (q.adicCompletion K)
        ((u i : q.adicCompletion K) * (y : q.adicCompletion K)), by
      have h := hInt (u i * y)
      rw [show ((u i * y : q.adicCompletionIntegers K) : q.adicCompletion K) =
        (u i : q.adicCompletion K) * (y : q.adicCompletion K) from
        Subring.coe_mul (q.adicCompletionIntegers K).toSubring (u i) y] at h
      exact h⟩
  have Lam_add : ∀ (i : Fin n) (y z : q.adicCompletionIntegers K),
      (Lam i (y + z) : basePrime.adicCompletion ℚ) =
        (Lam i y : basePrime.adicCompletion ℚ) + (Lam i z : basePrime.adicCompletion ℚ) := by
    intro i y z
    show Algebra.trace (basePrime.adicCompletion ℚ) (q.adicCompletion K)
        ((u i : q.adicCompletion K) * ((y : q.adicCompletionIntegers K) + 
          (z : q.adicCompletionIntegers K)) : q.adicCompletion K) =
      Algebra.trace (basePrime.adicCompletion ℚ) (q.adicCompletion K)
        ((u i : q.adicCompletion K) * (y : q.adicCompletion K)) +
      Algebra.trace (basePrime.adicCompletion ℚ) (q.adicCompletion K)
        ((u i : q.adicCompletion K) * (z : q.adicCompletion K))
    rw [mul_add, map_add]
  have Lam_smul : ∀ (i : Fin n) (a : basePrime.adicCompletionIntegers ℚ)
      (y : q.adicCompletionIntegers K),
      (Lam i (a • y) : basePrime.adicCompletion ℚ) =
        (a : basePrime.adicCompletion ℚ) * (Lam i y : basePrime.adicCompletion ℚ) := by
    intro i a y
    show Algebra.trace (basePrime.adicCompletion ℚ) (q.adicCompletion K)
        ((u i : q.adicCompletion K) * (a • (y : q.adicCompletion K))) =
      (a : basePrime.adicCompletion ℚ) * Algebra.trace (basePrime.adicCompletion ℚ)
        (q.adicCompletion K) ((u i : q.adicCompletion K) * (y : q.adicCompletion K))
    rw [← IsScalarTower.algebraMap_smul (R := basePrime.adicCompletionIntegers ℚ)
      (A := basePrime.adicCompletion ℚ) (M := q.adicCompletion K) a (y : q.adicCompletion K)]
    have hmul : (u i : q.adicCompletion K) *
        ((algebraMap (basePrime.adicCompletionIntegers ℚ) (basePrime.adicCompletion ℚ) a) •
          (y : q.adicCompletion K)) =
        (algebraMap (basePrime.adicCompletionIntegers ℚ) (basePrime.adicCompletion ℚ) a) •
        ((u i : q.adicCompletion K) * (y : q.adicCompletion K)) := by
      rw [Algebra.smul_def, Algebra.smul_def]
      ring
    rw [hmul, map_smul, Algebra.smul_def]
    rfl
  -- ## vanishing of the trace pairing on the base lattice implies vanishing of the element
  have trace_vanishing : ∀ b : q.adicCompletion K,
      (∀ x : q.adicCompletionIntegers K,
        Algebra.trace (basePrime.adicCompletion ℚ) (q.adicCompletion K)
          (b * (x : q.adicCompletion K)) = 0) → b = 0 := by
    intro b hb
    refine (traceForm_nondegenerate (basePrime.adicCompletion ℚ) (q.adicCompletion K)).1 b ?_
    intro y
    obtain ⟨k, hk⟩ := hcover y
    have h2k : (2 : basePrime.adicCompletion ℚ) ^ k ≠ 0 := by
      haveI : CharZero (basePrime.adicCompletion ℚ) :=
        Commons.NumberTheory.NumberField.charZero_adicCompletion basePrime
      exact pow_ne_zero _ (by norm_num)
    have h2map : (2 : q.adicCompletion K) ^ k =
        algebraMap (basePrime.adicCompletion ℚ) (q.adicCompletion K)
          ((2 : basePrime.adicCompletion ℚ) ^ k) := by
      rw [map_pow, map_ofNat]
    have hzero := hb ⟨(2 : q.adicCompletion K) ^ k * y, hk⟩
    rw [Subtype.coe_mk, h2map] at hzero
    rw [Algebra.traceForm_apply]
    have hsplit : b * (algebraMap (basePrime.adicCompletion ℚ) (q.adicCompletion K)
        ((2 : basePrime.adicCompletion ℚ) ^ k) * y) =
        algebraMap (basePrime.adicCompletion ℚ) (q.adicCompletion K)
          ((2 : basePrime.adicCompletion ℚ) ^ k) * (b * y) := by ring
    rw [hsplit, ← Algebra.smul_def, map_smul, Algebra.smul_def] at hzero
    exact (mul_eq_zero.mp hzero).resolve_left h2k
  -- ## the `p`-adic exponential/logarithm and the group of principal units
  obtain ⟨M, hM1, exp, log, hlogval, hlogadd, hlogone, hlogexp, hvalexp, hexplog⟩ :=
    NK.NUV2.localUnitLogStructure K q
  set δ : WithZero (Multiplicative ℤ) := WithZero.exp (-(M : ℤ)) with hδ
  have hδ1 : δ ≤ 1 := by
    rw [hδ, show (1 : WithZero (Multiplicative ℤ)) = WithZero.exp (0 : ℤ) from
      (WithZero.exp_zero).symm, WithZero.exp_le_exp]
    omega
  -- the subgroup of the local units given by the `M`-th principal unit ball
  let U := NK.GlobalCFT.Place.localUnits K (NK.GlobalCFT.Place.ofFinite q)
  let eu : ↥U ≃* (q.adicCompletionIntegers K)ˣ :=
    Submonoid.unitsEquivUnitsType (q.adicCompletionIntegers K).toSubmonoid
  let H : Subgroup ↥U := (NK.NUV2.principalUnitBall K q M).comap eu.toMonoidHom
  have hHfin : H.FiniteIndex := by
    haveI := NK.NUV2.principalUnitBall_finiteIndex K q M
    refine Subgroup.FiniteIndex.mk ?_
    rw [Subgroup.index_comap_of_surjective _ eu.surjective]
    exact Subgroup.FiniteIndex.index_ne_zero
  -- the field avatar of an element of `↥U`
  let feF : ↥U → q.adicCompletion K :=
    fun u => ((u : (q.adicCompletion K)ˣ) : q.adicCompletion K)
  have heu_val : ∀ u : ↥U,
      ((eu u : (q.adicCompletionIntegers K)ˣ) : q.adicCompletion K) = feF u := by
    intro u
    exact Submonoid.val_unitsEquivUnitsType_apply_coe (q.adicCompletionIntegers K).toSubmonoid u
  have hHmemF : ∀ u : ↥H,
      Valued.v (R := q.adicCompletion K) (Γ₀ := WithZero (Multiplicative ℤ)) (feF (u : ↥U) - 1) ≤ δ := by
    intro u
    have h1 : eu (u : ↥U) ∈ NK.NUV2.principalUnitBall K q M := u.2
    have h2 := (NK.NUV2.mem_principalUnitBall_iff_val q M (eu (u : ↥U))).mp h1
    rw [hδ, ← heu_val (u : ↥U)]
    exact h2
  have hmemlogF : ∀ u : ↥H, log (feF (u : ↥U)) ∈ q.adicCompletionIntegers K := by
    intro u
    rw [IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers, hlogval _ (hHmemF u)]
    exact le_trans (hHmemF u) hδ1
  -- the ring isomorphism `𝒪_{ℚ_2} ≅ ℤ_2`
  let eb : (basePrime.adicCompletionIntegers ℚ) ≃+* PadicInt 2 :=
    (PadicInt.adicCompletionIntegersEquiv (R := NumberField.RingOfIntegers ℚ)
      ⟨2, Nat.prime_two⟩).symm.toRingEquiv
  -- the characters
  let chiMon : Fin n → (↥H →* Multiplicative (PadicInt 2)) := fun i =>
    { toFun := fun u => Multiplicative.ofAdd
        (eb (Lam i (⟨log (feF (u : ↥U)), hmemlogF u⟩ : q.adicCompletionIntegers K)))
      map_one' := by
        show eb (Lam i (⟨log (feF ((1 : ↥H) : ↥U)), hmemlogF (1 : ↥H)⟩ :
          q.adicCompletionIntegers K)) = 0
        have hfe1 : feF ((1 : ↥H) : ↥U) = 1 := by
          simp [feF]
        have hz : (Lam i (⟨log (feF ((1 : ↥H) : ↥U)), hmemlogF (1 : ↥H)⟩ :
            q.adicCompletionIntegers K)) = 0 := by
          apply Subtype.ext
          show Algebra.trace (basePrime.adicCompletion ℚ) (q.adicCompletion K)
            ((u i : q.adicCompletion K) *
              ((⟨log (feF ((1 : ↥H) : ↥U)), hmemlogF (1 : ↥H)⟩ :
                q.adicCompletionIntegers K) : q.adicCompletion K)) = (0 : basePrime.adicCompletion ℚ)
          rw [show ((⟨log (feF ((1 : ↥H) : ↥U)), hmemlogF (1 : ↥H)⟩ :
              q.adicCompletionIntegers K) : q.adicCompletion K) =
              log (feF ((1 : ↥H) : ↥U)) from rfl]
          rw [hfe1, show log (1 : q.adicCompletion K) = (0 : q.adicCompletion K) from hlogone,
            mul_zero, map_zero]
        rw [hz, map_zero]
      map_mul' := by
        intro u v
        show eb (Lam i (⟨log (feF ((u * v : ↥H) : ↥U)), hmemlogF (u * v)⟩ :
          q.adicCompletionIntegers K)) =
          eb (Lam i (⟨log (feF (u : ↥U)), hmemlogF u⟩ : q.adicCompletionIntegers K)) +
          eb (Lam i (⟨log (feF (v : ↥U)), hmemlogF v⟩ : q.adicCompletionIntegers K))
        have hfe : feF ((u * v : ↥H) : ↥U) = feF (u : ↥U) * feF (v : ↥U) := by
          simp [feF]
        have hy : (⟨log (feF ((u * v : ↥H) : ↥U)), hmemlogF (u * v)⟩ :
            q.adicCompletionIntegers K) =
            (⟨log (feF (u : ↥U)), hmemlogF u⟩ : q.adicCompletionIntegers K) +
            (⟨log (feF (v : ↥U)), hmemlogF v⟩ : q.adicCompletionIntegers K) := by
          apply Subtype.ext
          rw [Subring.coe_add (q.adicCompletionIntegers K).toSubring]
          show log (feF ((u * v : ↥H) : ↥U)) =
            log (feF (u : ↥U)) + log (feF (v : ↥U))
          rw [hfe, hlogadd _ _ (hHmemF u) (hHmemF v)]
        rw [hy, ← map_add]
        congr 1
        exact Subtype.ext (Lam_add i _ _) }
  -- ## the strict balls are open
  have hopen : ∀ N : ℕ, IsOpen {y : q.adicCompletion K |
      Valued.v (R := q.adicCompletion K) (Γ₀ := WithZero (Multiplicative ℤ)) y <
        Valued.v (R := q.adicCompletion K) (Γ₀ := WithZero (Multiplicative ℤ))
          ((2 : q.adicCompletion K)^N)} := by
    intro N
    let vv : q.adicCompletion K →*₀ WithZero (Multiplicative ℤ) :=
      MonoidWithZeroHom.ofClass (Valued.v (R := q.adicCompletion K)
        (Γ₀ := WithZero (Multiplicative ℤ)))
    have h := Valued.isOpen_ball (q.adicCompletion K)
      (MonoidWithZeroHom.ValueGroup₀.restrict₀ vv ((2 : q.adicCompletion K)^N))
    have hset : {x : q.adicCompletion K |
        Valued.v.restrict x < MonoidWithZeroHom.ValueGroup₀.restrict₀ vv
          ((2 : q.adicCompletion K)^N)} =
        {x : q.adicCompletion K | Valued.v (R := q.adicCompletion K)
          (Γ₀ := WithZero (Multiplicative ℤ)) x <
            Valued.v (R := q.adicCompletion K) (Γ₀ := WithZero (Multiplicative ℤ))
              ((2 : q.adicCompletion K)^N)} := by
      ext x
      simp only [Set.mem_ofPred_eq]
      rw [show Valued.v.restrict x = MonoidWithZeroHom.ValueGroup₀.restrict₀ vv x from rfl,
        ← (MonoidWithZeroHom.ValueGroup₀.embedding_strictMono (f := vv)).lt_iff_lt]
      simp only [MonoidWithZeroHom.ValueGroup₀.embedding_restrict₀,
        MonoidWithZeroHom.coe_ofClass, vv]
    rwa [hset] at h
  have hfeF_cont : Continuous (fun u : ↥U => feF u) := by
    have h := Continuous.comp Units.continuous_val (continuous_subtype_val : Continuous
      (fun u : ↥U => (u : (q.adicCompletion K)ˣ)))
    exact h
  have hdeepOpen : ∀ N : ℕ, IsOpen {u : ↥U |
      Valued.v (R := q.adicCompletion K) (Γ₀ := WithZero (Multiplicative ℤ)) (feF u - 1) <
        Valued.v (R := q.adicCompletion K) (Γ₀ := WithZero (Multiplicative ℤ))
          ((2 : q.adicCompletion K)^N)} := by
    intro N
    have h1 : IsOpen {y : q.adicCompletion K |
        Valued.v (R := q.adicCompletion K) (Γ₀ := WithZero (Multiplicative ℤ)) (y - 1) <
          Valued.v (R := q.adicCompletion K) (Γ₀ := WithZero (Multiplicative ℤ))
            ((2 : q.adicCompletion K)^N)} := by
      have hc : Continuous (fun y : q.adicCompletion K => y - 1) :=
        continuous_id.sub continuous_const
      have h2 := (hopen N).preimage hc
      convert h2 using 2
      ext y
      rfl
    exact h1.preimage hfeF_cont
  -- ## the estimate: the deep principal units are killed by the reduction
  have hest : ∀ (N : ℕ) (i : Fin n) (u : ↥H),
      Valued.v (R := q.adicCompletion K) (Γ₀ := WithZero (Multiplicative ℤ))
        (feF (u : ↥U) - 1) <
        Valued.v (R := q.adicCompletion K) (Γ₀ := WithZero (Multiplicative ℤ))
          ((2 : q.adicCompletion K)^N) →
      eb (Lam i (⟨log (feF (u : ↥U)), hmemlogF u⟩ : q.adicCompletionIntegers K)) ∈
        Ideal.span {((2 : PadicInt 2)^N)} := by
    intro N i u hu
    have hlogv : Valued.v (R := q.adicCompletion K) (Γ₀ := WithZero (Multiplicative ℤ))
        (log (feF (u : ↥U))) <
        Valued.v (R := q.adicCompletion K) (Γ₀ := WithZero (Multiplicative ℤ))
          ((2 : q.adicCompletion K)^N) := by
      rw [hlogval _ (hHmemF u)]
      exact hu
    have hzmem : log (feF (u : ↥U)) / (2 : q.adicCompletion K)^N ∈ q.adicCompletionIntegers K := by
      rw [IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers, Valuation.map_div]
      have hpos : 0 < Valued.v (R := q.adicCompletion K) (Γ₀ := WithZero (Multiplicative ℤ))
          ((2 : q.adicCompletion K)^N) := by
        rw [Valuation.map_pow]
        exact pow_pos (WithZero.pos_iff_ne_zero.mpr
          ((Valuation.ne_zero_iff _).mpr (by
            haveI : CharZero (q.adicCompletion K) :=
              Commons.NumberTheory.NumberField.charZero_adicCompletion q
            norm_num))) N
      rw [div_le_one₀ hpos]
      exact hlogv.le
    let z : q.adicCompletionIntegers K := ⟨_, hzmem⟩
    have hzlog : log (feF (u : ↥U)) = (2 : q.adicCompletion K)^N * (z : q.adicCompletion K) := by
      show log (feF (u : ↥U)) = (2 : q.adicCompletion K)^N *
        (log (feF (u : ↥U)) / (2 : q.adicCompletion K)^N)
      rw [mul_div_cancel₀]
      haveI : CharZero (q.adicCompletion K) :=
        Commons.NumberTheory.NumberField.charZero_adicCompletion q
      exact pow_ne_zero _ (by norm_num)
    have h2pow : (2 : q.adicCompletion K)^N =
        algebraMap (basePrime.adicCompletion ℚ) (q.adicCompletion K)
          ((2 : basePrime.adicCompletion ℚ)^N) := by
      rw [map_pow, map_ofNat]
    have hzeq : (⟨log (feF (u : ↥U)), hmemlogF u⟩ : q.adicCompletionIntegers K) =
        (2 : basePrime.adicCompletionIntegers ℚ)^N • z := by
      have hval : (((2 : basePrime.adicCompletionIntegers ℚ)^N • z :
          q.adicCompletionIntegers K) : q.adicCompletion K) =
          (2 : q.adicCompletion K)^N * (z : q.adicCompletion K) := by
        rw [Algebra.smul_def, Subring.coe_mul (q.adicCompletionIntegers K).toSubring, h2pow]
        rfl
      refine Subtype.ext ?_
      show ((⟨log (feF (u : ↥U)), hmemlogF u⟩ : q.adicCompletionIntegers K) :
        q.adicCompletion K) = (((2 : basePrime.adicCompletionIntegers ℚ)^N • z :
        q.adicCompletionIntegers K) : q.adicCompletion K)
      rw [show ((⟨log (feF (u : ↥U)), hmemlogF u⟩ : q.adicCompletionIntegers K) :
        q.adicCompletion K) = log (feF (u : ↥U)) from rfl, hval]
      exact hzlog
    have hL : (Lam i ((2 : basePrime.adicCompletionIntegers ℚ)^N • z)) =
        (2 : basePrime.adicCompletionIntegers ℚ)^N * Lam i z :=
      Subtype.ext (Lam_smul i _ z)
    rw [hzeq, hL, map_mul, map_pow, map_ofNat]
    exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)
  -- ## continuity of the characters
  have hcont : ∀ i : Fin n, Continuous ⇑((chiMon i).toAdditive) := by
    intro i
    rw [continuous_iff_continuousAt]
    intro x₀
    rw [ContinuousAt, Metric.tendsto_nhds]
    intro ε hε
    obtain ⟨N, hN⟩ := PadicInt.exists_pow_neg_lt 2 hε
    have hc : Continuous (fun z : Additive ↥H =>
        (((Additive.toMul (z - x₀) : ↥H)) : ↥U)) :=
      continuous_subtype_val.comp (continuous_id.sub continuous_const)
    have hop : IsOpen {z : Additive ↥H |
        Valued.v (R := q.adicCompletion K) (Γ₀ := WithZero (Multiplicative ℤ))
          (feF (((Additive.toMul (z - x₀) : ↥H) : ↥U)) - 1) <
          Valued.v (R := q.adicCompletion K) (Γ₀ := WithZero (Multiplicative ℤ))
            ((2 : q.adicCompletion K)^N)} :=
      (hdeepOpen N).preimage hc
    have hmem : x₀ ∈ {z : Additive ↥H |
        Valued.v (R := q.adicCompletion K) (Γ₀ := WithZero (Multiplicative ℤ))
          (feF (((Additive.toMul (z - x₀) : ↥H) : ↥U)) - 1) <
          Valued.v (R := q.adicCompletion K) (Γ₀ := WithZero (Multiplicative ℤ))
            ((2 : q.adicCompletion K)^N)} := by
      show Valued.v (R := q.adicCompletion K) (Γ₀ := WithZero (Multiplicative ℤ))
        (feF (((Additive.toMul (x₀ - x₀) : ↥H) : ↥U)) - 1) < _
      rw [sub_self,
        show (((Additive.toMul (0 : Additive ↥H) : ↥H)) : ↥U) = (1 : ↥U) from rfl,
        show feF (1 : ↥U) = 1 from by simp [feF]]
      have h2ne : Valued.v (R := q.adicCompletion K) (Γ₀ := WithZero (Multiplicative ℤ))
          (2 : q.adicCompletion K) ≠ 0 := by
        rw [Valuation.ne_zero_iff]
        haveI : CharZero (q.adicCompletion K) :=
          Commons.NumberTheory.NumberField.charZero_adicCompletion q
        norm_num
      rw [sub_self, map_zero, Valuation.map_pow, ← WithZero.exp_log h2ne,
        ← WithZero.exp_nsmul]
      exact WithZero.exp_pos
    refine Filter.mem_of_superset (hop.mem_nhds hmem) ?_
    intro z hz
    show dist (((chiMon i).toAdditive) z) (((chiMon i).toAdditive) x₀) < ε
    have hgz : ((chiMon i).toAdditive) z - ((chiMon i).toAdditive) x₀ =
        ((chiMon i).toAdditive) (z - x₀) := by
      rw [map_sub]
    rw [dist_eq_norm, hgz]
    have hmem2 := hest N i (Additive.toMul (z - x₀)) hz
    have hnorm : ‖((chiMon i).toAdditive) (z - x₀)‖ ≤ ((2 : ℕ) : ℝ) ^ (-(N : ℤ)) :=
      (PadicInt.norm_le_pow_iff_mem_span_pow _ N).mpr hmem2
    exact lt_of_le_of_lt hnorm hN
  -- ## the dual elements
  let chi : Fin n → NK.Reconstruct.Dual ↥H 2 := fun i => ⟨(chiMon i).toAdditive, hcont i⟩
  -- ## the logarithm is surjective onto the ball
  have hδ_lt1 : δ < 1 := by
    rw [hδ, show (1 : WithZero (Multiplicative ℤ)) = WithZero.exp (0 : ℤ) from
      (WithZero.exp_zero).symm, WithZero.exp_lt_exp]
    omega
  have hsurj : ∀ w : q.adicCompletionIntegers K,
      Valued.v (R := q.adicCompletion K) (Γ₀ := WithZero (Multiplicative ℤ))
        (w : q.adicCompletion K) ≤ δ →
      ∃ u : ↥H, log (feF (u : ↥U)) = (w : q.adicCompletion K) := by
    intro w hw
    have hle : Valued.v (R := q.adicCompletion K) (Γ₀ := WithZero (Multiplicative ℤ))
        (exp (w : q.adicCompletion K) - 1) ≤ δ := by
      rw [hvalexp _ hw]
      exact hw
    have hyv : Valued.v (R := q.adicCompletion K) (Γ₀ := WithZero (Multiplicative ℤ))
        (exp (w : q.adicCompletion K)) = 1 := by
      have hltv : Valued.v (R := q.adicCompletion K) (Γ₀ := WithZero (Multiplicative ℤ))
          (exp (w : q.adicCompletion K) - 1) <
          Valued.v (R := q.adicCompletion K) (Γ₀ := WithZero (Multiplicative ℤ))
            (1 : q.adicCompletion K) := by
        rw [Valuation.map_one]
        exact lt_of_le_of_lt hle hδ_lt1
      rw [show exp (w : q.adicCompletion K) = (1 : q.adicCompletion K) +
          (exp (w : q.adicCompletion K) - 1) from by ring,
        Valuation.map_add_eq_of_lt_left _ hltv, Valuation.map_one]
    have hne : exp (w : q.adicCompletion K) ≠ 0 := by
      intro h
      rw [h, Valuation.map_zero] at hyv
      exact zero_ne_one hyv
    let y : (q.adicCompletion K)ˣ := Units.mk0 _ hne
    have hymem : y ∈ U := by
      rw [show U = NK.GlobalCFT.Place.localUnits K
        (NK.GlobalCFT.Place.ofFinite q) from rfl]
      exact (NK.GlobalCFT.Place.mem_localUnits_ofFinite_iff_valued_eq_one (q := q)).mpr hyv
    let u : ↥U := ⟨y, hymem⟩
    have huy : feF u = exp (w : q.adicCompletion K) := rfl
    have hlog : log (feF u) = (w : q.adicCompletion K) := by
      rw [huy]
      exact hlogexp _ hw
    have hHu : u ∈ H := by
      show eu.toMonoidHom u ∈ NK.NUV2.principalUnitBall K q M
      rw [NK.NUV2.mem_principalUnitBall_iff_val, ← hδ]
      show Valued.v (R := q.adicCompletion K) (Γ₀ := WithZero (Multiplicative ℤ))
        (((eu u : (q.adicCompletionIntegers K)ˣ) : q.adicCompletion K) - 1) ≤ δ
      rw [show (((eu u : (q.adicCompletionIntegers K)ˣ) : q.adicCompletion K)) =
        exp (w : q.adicCompletion K) from by rw [heu_val u]; rfl]
      exact hle
    exact ⟨⟨u, hHu⟩, hlog⟩
  -- ## the `Lam i` depend on `z` only through its value, and the characters are independent
  have hLam_congr : ∀ (j : Fin n) {z z' : q.adicCompletionIntegers K},
      (z : q.adicCompletion K) = (z' : q.adicCompletion K) → Lam j z = Lam j z' := by
    intro j z z' h
    apply Subtype.ext
    show Algebra.trace (basePrime.adicCompletion ℚ) (q.adicCompletion K)
      ((u j : q.adicCompletion K) * (z : q.adicCompletion K)) =
      Algebra.trace (basePrime.adicCompletion ℚ) (q.adicCompletion K)
      ((u j : q.adicCompletion K) * (z' : q.adicCompletion K))
    rw [h]
  -- ## the scalar `2^M` behaves as expected
  have hsmulval : ∀ (a : basePrime.adicCompletionIntegers ℚ) (y : q.adicCompletionIntegers K),
      ((a • y : q.adicCompletionIntegers K) : q.adicCompletion K) =
        algebraMap (basePrime.adicCompletionIntegers ℚ) (q.adicCompletion K) a *
          (y : q.adicCompletion K) := by
    intro a y
    rw [Algebra.smul_def, Subring.coe_mul (q.adicCompletionIntegers K).toSubring]
    congr 1
  have h2Mval : algebraMap (basePrime.adicCompletionIntegers ℚ) (q.adicCompletion K)
      ((2 : basePrime.adicCompletionIntegers ℚ)^M) = (2 : q.adicCompletion K)^M := by
    rw [map_pow, map_ofNat]
  have h2powval : (((2 : basePrime.adicCompletionIntegers ℚ)^M :
      basePrime.adicCompletionIntegers ℚ) : basePrime.adicCompletion ℚ) =
      (2 : basePrime.adicCompletion ℚ)^M := by
    change algebraMap (basePrime.adicCompletionIntegers ℚ) (basePrime.adicCompletion ℚ)
      ((2 : basePrime.adicCompletionIntegers ℚ)^M) = (2 : basePrime.adicCompletion ℚ)^M
    rw [map_pow, map_ofNat]
  have h2M_ne : (2 : basePrime.adicCompletion ℚ)^M ≠ 0 := by
    haveI : CharZero (basePrime.adicCompletion ℚ) :=
      Commons.NumberTheory.NumberField.charZero_adicCompletion basePrime
    exact pow_ne_zero _ (by norm_num)
  have hδpow : (Valued.v (R := q.adicCompletion K) (Γ₀ := WithZero (Multiplicative ℤ))
      (2 : q.adicCompletion K))^M ≤ δ := by
    rw [hδ]
    calc (Valued.v (R := q.adicCompletion K) (Γ₀ := WithZero (Multiplicative ℤ))
          (2 : q.adicCompletion K))^M
        ≤ (WithZero.exp (-(1 : ℤ)))^M := pow_le_pow_left' h2v_le M
      _ = WithZero.exp (M • (-(1 : ℤ))) := (WithZero.exp_nsmul M (-(1 : ℤ))).symm
      _ = WithZero.exp (-(M : ℤ)) := by
            congr 1
            rw [nsmul_eq_mul]
            ring
  have hindep : LinearIndependent (PadicInt 2) (fun i : Fin n => chi i) := by
    rw [linearIndependent_iff']
    intro s g hsum i hi
    let c : Fin n → basePrime.adicCompletionIntegers ℚ := fun j => eb.symm (g j)
    have hc : ∀ j, eb (c j) = g j := fun j => eb.apply_symm_apply (g j)
    -- ## the sum vanishes on the ball
    have hball : ∀ w : q.adicCompletionIntegers K,
        Valued.v (R := q.adicCompletion K) (Γ₀ := WithZero (Multiplicative ℤ))
          (w : q.adicCompletion K) ≤ δ → ∑ j ∈ s, c j * Lam j w = 0 := by
      intro w hw
      obtain ⟨u', hu'⟩ := hsurj w hw
      let ev : NK.Reconstruct.Dual ↥H 2 →+ PadicInt 2 :=
        { toFun := fun x => x (Additive.ofMul u')
          map_zero' := rfl
          map_add' := fun x y => rfl }
      have h1 : (∑ j ∈ s, g j • chi j) (Additive.ofMul u') =
          ∑ j ∈ s, g j * eb (Lam j w) := by
        rw [show (∑ j ∈ s, g j • chi j) (Additive.ofMul u')
          = ev (∑ j ∈ s, g j • chi j) from rfl, map_sum]
        refine Finset.sum_congr rfl fun j hj => ?_
        show (g j • chi j) (Additive.ofMul u') = g j * eb (Lam j w)
        rw [NK.RankTheoryDeep.smul_dual_apply]
        congr 1
        show eb (Lam j (⟨log (feF (u' : ↥U)), hmemlogF u'⟩ :
          q.adicCompletionIntegers K)) = eb (Lam j w)
        rw [hLam_congr j (by
          show ((⟨log (feF (u' : ↥U)), hmemlogF u'⟩ : q.adicCompletionIntegers K) :
            q.adicCompletion K) = (w : q.adicCompletion K)
          exact hu')]
      have hzero : (∑ j ∈ s, g j • chi j) (Additive.ofMul u') = 0 := by
        have h := congrArg (fun (x : NK.Reconstruct.Dual ↥H 2) =>
          x (Additive.ofMul u')) hsum
        simpa using h
      have h2 : (∑ j ∈ s, eb (c j * Lam j w)) = 0 := by
        rw [show (∑ j ∈ s, eb (c j * Lam j w)) = ∑ j ∈ s, g j * eb (Lam j w) from
          Finset.sum_congr rfl (fun j hj => by rw [map_mul, hc j])]
        rw [← h1, hzero]
      have h3 : (∑ j ∈ s, c j * Lam j w) = 0 := by
        apply eb.injective
        simpa only [map_sum, map_mul, map_zero] using h2
      exact h3
    -- ## extend the vanishing from the ball to all of `𝒪`
    have hball_all : ∀ z : q.adicCompletionIntegers K,
        ∑ j ∈ s, (c j : basePrime.adicCompletion ℚ) *
          (Lam j z : basePrime.adicCompletion ℚ) = 0 := by
      intro z
      have hzle : Valued.v (R := q.adicCompletion K) (Γ₀ := WithZero (Multiplicative ℤ))
          (z : q.adicCompletion K) ≤ 1 :=
        (IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers
          (NumberField.RingOfIntegers K) K q).mp z.2
      have hzball : Valued.v (R := q.adicCompletion K) (Γ₀ := WithZero (Multiplicative ℤ))
          ((((2 : basePrime.adicCompletionIntegers ℚ)^M) • z : q.adicCompletionIntegers K) :
            q.adicCompletion K) ≤ δ := by
        rw [hsmulval, Valuation.map_mul]
        calc Valued.v (R := q.adicCompletion K) (Γ₀ := WithZero (Multiplicative ℤ))
              (algebraMap (basePrime.adicCompletionIntegers ℚ) (q.adicCompletion K)
                ((2 : basePrime.adicCompletionIntegers ℚ)^M)) *
                Valued.v (R := q.adicCompletion K) (Γ₀ := WithZero (Multiplicative ℤ))
                  (z : q.adicCompletion K)
            ≤ Valued.v (R := q.adicCompletion K) (Γ₀ := WithZero (Multiplicative ℤ))
              (algebraMap (basePrime.adicCompletionIntegers ℚ) (q.adicCompletion K)
                ((2 : basePrime.adicCompletionIntegers ℚ)^M)) * 1 := by
                gcongr
          _ = Valued.v (R := q.adicCompletion K) (Γ₀ := WithZero (Multiplicative ℤ))
              (algebraMap (basePrime.adicCompletionIntegers ℚ) (q.adicCompletion K)
                ((2 : basePrime.adicCompletionIntegers ℚ)^M)) := mul_one _
          _ = (Valued.v (R := q.adicCompletion K) (Γ₀ := WithZero (Multiplicative ℤ))
              (2 : q.adicCompletion K))^M := by rw [h2Mval, Valuation.map_pow]
          _ ≤ δ := hδpow
      have hw := hball _ hzball
      have hwL : (∑ j ∈ s, (c j : basePrime.adicCompletion ℚ) *
          (Lam j (((2 : basePrime.adicCompletionIntegers ℚ)^M) • z) :
            basePrime.adicCompletion ℚ)) = 0 := by
        have h := congrArg (fun x : basePrime.adicCompletionIntegers ℚ =>
          algebraMap (basePrime.adicCompletionIntegers ℚ) (basePrime.adicCompletion ℚ) x) hw
        push_cast at h
        simpa using h
      have hterms : (∑ j ∈ s, (c j : basePrime.adicCompletion ℚ) *
            ((2 : basePrime.adicCompletion ℚ)^M *
              (Lam j z : basePrime.adicCompletion ℚ))) =
          ∑ j ∈ s, (c j : basePrime.adicCompletion ℚ) *
            (Lam j (((2 : basePrime.adicCompletionIntegers ℚ)^M) • z) :
              basePrime.adicCompletion ℚ) := by
        refine Finset.sum_congr rfl fun j hj => ?_
        rw [Lam_smul j ((2 : basePrime.adicCompletionIntegers ℚ)^M) z, ← h2powval]
      have hwL' : (∑ j ∈ s, (c j : basePrime.adicCompletion ℚ) *
            ((2 : basePrime.adicCompletion ℚ)^M *
              (Lam j z : basePrime.adicCompletion ℚ))) = 0 := by
        rw [hterms, hwL]
      have hfac : (2 : basePrime.adicCompletion ℚ)^M *
          (∑ j ∈ s, (c j : basePrime.adicCompletion ℚ) *
            (Lam j z : basePrime.adicCompletion ℚ)) = 0 := by
        rw [Finset.mul_sum]
        trans ∑ j ∈ s, (c j : basePrime.adicCompletion ℚ) *
            ((2 : basePrime.adicCompletion ℚ)^M *
              (Lam j z : basePrime.adicCompletion ℚ))
        · exact Finset.sum_congr rfl fun j hj => by ring
        · exact hwL'
      exact (mul_eq_zero.mp hfac).resolve_left h2M_ne
    -- ## the element `b` and the trace pairing
    let cf : Fin n → q.adicCompletion K := fun j =>
      algebraMap (basePrime.adicCompletion ℚ) (q.adicCompletion K)
        (c j : basePrime.adicCompletion ℚ)
    let bb : q.adicCompletion K := ∑ j ∈ s, cf j * (u j : q.adicCompletion K)
    have htr : ∀ x : q.adicCompletionIntegers K,
        Algebra.trace (basePrime.adicCompletion ℚ) (q.adicCompletion K)
          (bb * (x : q.adicCompletion K)) = 0 := by
      intro x
      have hsplit : bb * (x : q.adicCompletion K) =
          ∑ j ∈ s, cf j * ((u j : q.adicCompletion K) * (x : q.adicCompletion K)) := by
        rw [show bb = ∑ j ∈ s, cf j * (u j : q.adicCompletion K) from rfl, Finset.sum_mul]
        exact Finset.sum_congr rfl fun j hj => by ring
      have hterm : ∀ j ∈ s,
          Algebra.trace (basePrime.adicCompletion ℚ) (q.adicCompletion K)
            (cf j * ((u j : q.adicCompletion K) * (x : q.adicCompletion K))) =
          (c j : basePrime.adicCompletion ℚ) * (Lam j x : basePrime.adicCompletion ℚ) := by
        intro j hj
        have hcs : cf j * ((u j : q.adicCompletion K) * (x : q.adicCompletion K)) =
            (c j : basePrime.adicCompletion ℚ) •
              ((u j : q.adicCompletion K) * (x : q.adicCompletion K)) := by
          change algebraMap (basePrime.adicCompletion ℚ) (q.adicCompletion K)
              (c j : basePrime.adicCompletion ℚ) *
              ((u j : q.adicCompletion K) * (x : q.adicCompletion K)) =
            (c j : basePrime.adicCompletion ℚ) •
              ((u j : q.adicCompletion K) * (x : q.adicCompletion K))
          exact (Algebra.smul_def (c j : basePrime.adicCompletion ℚ)
            ((u j : q.adicCompletion K) * (x : q.adicCompletion K))).symm
        rw [hcs, map_smul, smul_eq_mul]
      rw [hsplit, map_sum, Finset.sum_congr rfl hterm, hball_all x]
    have hbzero : bb = 0 := trace_vanishing bb htr
    have hcoeff : ∀ j ∈ s, (c j : basePrime.adicCompletion ℚ) = 0 := by
      intro j hj
      have hsum0 : ∑ j' ∈ s, (c j' : basePrime.adicCompletion ℚ) •
          (u j' : q.adicCompletion K) = 0 := by
        have h2 : (∑ j' ∈ s, algebraMap (basePrime.adicCompletion ℚ) (q.adicCompletion K)
            (c j' : basePrime.adicCompletion ℚ) * (u j' : q.adicCompletion K)) = 0 := hbzero
        simpa only [Algebra.smul_def] using h2
      exact (linearIndependent_iff'.mp huLI) s
        (fun j' => (c j' : basePrime.adicCompletion ℚ)) hsum0 j hj
    have hci : c i = 0 := Subtype.ext (by simpa using hcoeff i hi)
    rw [← hc i, hci, map_zero]
  -- ## assembly
  haveI : H.FiniteIndex := hHfin
  have hkey : (n : Cardinal) ≤
      Module.rank (PadicInt 2) (NK.Reconstruct.Dual ↥H 2) :=
    (Module.le_rank_iff (R := PadicInt 2) (M := NK.Reconstruct.Dual ↥H 2)
      (n := n)).mpr ⟨chi, hindep⟩
  exact le_trans hkey (rank_dual_le_rank_dual_of_finiteIndex (A := ↥U) (ℓ := 2) H)
