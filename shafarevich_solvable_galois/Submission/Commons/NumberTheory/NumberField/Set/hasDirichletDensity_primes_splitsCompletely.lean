import Mathlib.RingTheory.Henselian
import Mathlib.NumberTheory.NumberField.DirichletDensity
import Mathlib.NumberTheory.RamificationInertia.Galois
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Topology.GDelta.MetrizableSpace
import Mathlib.Topology.Separation.CompletelyRegular
import Mathlib.Algebra.Order.Star.Real
import Submission.Commons.NumberTheory.NumberField.Set.isBigO_primeIdealZetaSum_sub_log
import Submission.Commons.NumberTheory.NumberField.Set.tendsto_primeIdealZetaSum_univ_nhdsGT
import Submission.Commons.NumberTheory.NumberField.finite_setOf_ramificationIdx_ne_one
import Submission.Commons.NumberTheory.NumberField.ncard_primesOver_eq_finrank_iff_splitCompletely
import Submission.Commons.NumberTheory.NumberField.ncard_primesOver_le_finrank
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

set_option maxHeartbeats 1000000
set_option linter.unusedSectionVars false
set_option linter.ambiguousOpen false
set_option linter.style.haveILetI false
set_option linter.style.setOption false

open Filter IsDedekindDomain Topology Set Asymptotics
open scoped BigOperators

namespace Commons.NumberTheory.NumberField.Set

/-! ## Auxiliary definitions -/

/-- The nonzero prime ideal of `𝓞 K` below a nonzero prime ideal of `𝓞 L`. -/
private noncomputable def underPrime (K L : Type*) [Field K] [NumberField K] [Field L]
    [NumberField L] [Algebra K L] [FiniteDimensional K L]
    (𝔮 : HeightOneSpectrum (NumberField.RingOfIntegers L)) :
    HeightOneSpectrum (NumberField.RingOfIntegers K) :=
  HeightOneSpectrum.under (NumberField.RingOfIntegers K) 𝔮

private lemma underPrime_asIdeal (K L : Type*) [Field K] [NumberField K] [Field L]
    [NumberField L] [Algebra K L] [FiniteDimensional K L]
    (𝔮 : HeightOneSpectrum (NumberField.RingOfIntegers L)) :
    (underPrime K L 𝔮).asIdeal = 𝔮.asIdeal.under (NumberField.RingOfIntegers K) :=
  HeightOneSpectrum.under_asIdeal _ 𝔮

private lemma liesOver_iff_underPrime_eq (K L : Type*) [Field K] [NumberField K] [Field L]
    [NumberField L] [Algebra K L] [FiniteDimensional K L]
    (𝔭 : HeightOneSpectrum (NumberField.RingOfIntegers K))
    (𝔮 : HeightOneSpectrum (NumberField.RingOfIntegers L)) :
    𝔮.asIdeal.LiesOver 𝔭.asIdeal ↔ underPrime K L 𝔮 = 𝔭 := by
  constructor
  · intro h
    exact HeightOneSpectrum.ext h.over.symm
  · intro h
    rw [← h, underPrime_asIdeal]
    exact ⟨rfl⟩

/-- The fibre of `underPrime` over `𝔭` is the set of primes of `𝓞 L` lying over `𝔭`. -/
private noncomputable def fiberEquivPrimesOver (K L : Type*) [Field K] [NumberField K] [Field L]
    [NumberField L] [Algebra K L] [FiniteDimensional K L]
    (𝔭 : HeightOneSpectrum (NumberField.RingOfIntegers K)) :
    {𝔮 : HeightOneSpectrum (NumberField.RingOfIntegers L) // underPrime K L 𝔮 = 𝔭} ≃
      (𝔭.asIdeal.primesOver (NumberField.RingOfIntegers L)) where
  toFun 𝔮 := ⟨𝔮.1.asIdeal, 𝔮.1.isPrime,
    (liesOver_iff_underPrime_eq K L 𝔭 𝔮.1).mpr 𝔮.2⟩
  invFun P := ⟨⟨P.1, P.2.1,
      Ideal.ne_bot_of_mem_primesOver 𝔭.ne_bot P.2⟩,
    (liesOver_iff_underPrime_eq K L 𝔭 _).mp P.2.2⟩
  left_inv 𝔮 := by rfl
  right_inv P := by rfl

private lemma natCard_fiber_eq_ncard_primesOver (K L : Type*) [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L] [FiniteDimensional K L]
    (𝔭 : HeightOneSpectrum (NumberField.RingOfIntegers K)) :
    Nat.card {𝔮 : HeightOneSpectrum (NumberField.RingOfIntegers L) //
        underPrime K L 𝔮 = 𝔭}
      = (𝔭.asIdeal.primesOver (NumberField.RingOfIntegers L)).ncard := by
  rw [Nat.card_congr (fiberEquivPrimesOver K L 𝔭), Nat.card_eq_fintype_card,
    Set.fintypeCard_eq_ncard]

/-- The fibre sum over a prime `𝔭` of `𝓞 K`: the sum of `(N 𝔮)^{-s}` over the primes `𝔮` of
`𝓞 L` above `𝔭`. -/
private noncomputable def fiberSum (K L : Type*) [Field K] [NumberField K] [Field L]
    [NumberField L] [Algebra K L] [FiniteDimensional K L]
    (s : ℝ) (𝔭 : HeightOneSpectrum (NumberField.RingOfIntegers K)) : ℝ :=
  ∑' 𝔮 : {𝔮 : HeightOneSpectrum (NumberField.RingOfIntegers L) // underPrime K L 𝔮 = 𝔭},
    (Ideal.absNorm 𝔮.1.asIdeal : ℝ) ^ (-s)

/-- The set of primes of `𝓞 K` that split completely in `L`. -/
private def splitSet (K L : Type*) [Field K] [NumberField K] [Field L]
    [NumberField L] [Algebra K L] [FiniteDimensional K L] :
    Set (HeightOneSpectrum (NumberField.RingOfIntegers K)) :=
  {𝔭 | (𝔭.asIdeal.primesOver (NumberField.RingOfIntegers L)).ncard = Module.finrank K L}

/-! ## Fibrewise decomposition -/

private lemma tsum_fiberwise_underPrime (K L : Type*) [Field K] [NumberField K] [Field L]
    [NumberField L] [Algebra K L] [FiniteDimensional K L] {s : ℝ}
    (hf : Summable (fun 𝔮 : HeightOneSpectrum (NumberField.RingOfIntegers L) =>
        (Ideal.absNorm 𝔮.asIdeal : ℝ) ^ (-s))) :
    (∑' 𝔮 : HeightOneSpectrum (NumberField.RingOfIntegers L),
        (Ideal.absNorm 𝔮.asIdeal : ℝ) ^ (-s)) =
      ∑' 𝔭 : HeightOneSpectrum (NumberField.RingOfIntegers K), fiberSum K L s 𝔭 := by
  classical
  let f : HeightOneSpectrum (NumberField.RingOfIntegers L) → ℝ :=
    fun 𝔮 => (Ideal.absNorm 𝔮.asIdeal : ℝ) ^ (-s)
  let e : ((𝔭 : HeightOneSpectrum (NumberField.RingOfIntegers K)) ×
      {𝔮 : HeightOneSpectrum (NumberField.RingOfIntegers L) // underPrime K L 𝔮 = 𝔭}) ≃
      HeightOneSpectrum (NumberField.RingOfIntegers L) := Equiv.sigmaFiberEquiv (underPrime K L)
  have hsum : Summable (f ∘ e) := (e.summable_iff).mpr hf
  calc ∑' 𝔮, f 𝔮 = ∑' x, f (e x) := (e.tsum_eq f).symm
    _ = ∑' 𝔭, ∑' c, f (e ⟨𝔭, c⟩) := hsum.tsum_sigma
    _ = ∑' 𝔭 : HeightOneSpectrum (NumberField.RingOfIntegers K), fiberSum K L s 𝔭 := by
        refine tsum_congr fun 𝔭 => ?_
        rw [fiberSum]
        refine tsum_congr fun c => ?_
        rfl

private lemma summable_fiberSum (K L : Type*) [Field K] [NumberField K] [Field L]
    [NumberField L] [Algebra K L] [FiniteDimensional K L] {s : ℝ}
    (hf : Summable (fun 𝔮 : HeightOneSpectrum (NumberField.RingOfIntegers L) =>
        (Ideal.absNorm 𝔮.asIdeal : ℝ) ^ (-s))) :
    Summable (fun 𝔭 : HeightOneSpectrum (NumberField.RingOfIntegers K) => fiberSum K L s 𝔭) := by
  classical
  let f : HeightOneSpectrum (NumberField.RingOfIntegers L) → ℝ :=
    fun 𝔮 => (Ideal.absNorm 𝔮.asIdeal : ℝ) ^ (-s)
  let e : ((𝔭 : HeightOneSpectrum (NumberField.RingOfIntegers K)) ×
      {𝔮 : HeightOneSpectrum (NumberField.RingOfIntegers L) // underPrime K L 𝔮 = 𝔭}) ≃
      HeightOneSpectrum (NumberField.RingOfIntegers L) := Equiv.sigmaFiberEquiv (underPrime K L)
  have hsum : Summable (f ∘ e) := (e.summable_iff).mpr hf
  have h2 := hsum.sigma
  have h3 : (fun 𝔭 : HeightOneSpectrum (NumberField.RingOfIntegers K) =>
      ∑' c, (f ∘ e) ⟨𝔭, c⟩) =
      fun 𝔭 : HeightOneSpectrum (NumberField.RingOfIntegers K) => fiberSum K L s 𝔭 := by
    funext 𝔭
    rw [fiberSum]
    refine tsum_congr fun c => ?_
    rfl
  rwa [h3] at h2

/-! ## The fibrewise value and bounds -/

private lemma fiberSum_eq_of_split (K L : Type*) [Field K] [NumberField K] [Field L]
    [NumberField L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    (𝔭 : HeightOneSpectrum (NumberField.RingOfIntegers K))
    (h𝔭 : (𝔭.asIdeal.primesOver (NumberField.RingOfIntegers L)).ncard = Module.finrank K L)
    (s : ℝ) :
    fiberSum K L s 𝔭 = (Module.finrank K L : ℝ) *
      (Ideal.absNorm 𝔭.asIdeal : ℝ) ^ (-s) := by
  classical
  haveI : Fintype {𝔮 : HeightOneSpectrum (NumberField.RingOfIntegers L) //
      underPrime K L 𝔮 = 𝔭} :=
    Fintype.ofEquiv (𝔭.asIdeal.primesOver (NumberField.RingOfIntegers L))
      (fiberEquivPrimesOver K L 𝔭).symm
  have htermp : ∀ 𝔮 : {𝔮 : HeightOneSpectrum (NumberField.RingOfIntegers L) //
      underPrime K L 𝔮 = 𝔭},
      (Ideal.absNorm 𝔮.1.asIdeal : ℝ) ^ (-s) =
        (Ideal.absNorm 𝔭.asIdeal : ℝ) ^ (-s) := by
    intro 𝔮
    have hlies : 𝔮.1.asIdeal.LiesOver 𝔭.asIdeal :=
      (liesOver_iff_underPrime_eq K L 𝔭 𝔮.1).mpr 𝔮.2
    haveI := hlies
    have hf : 𝔮.1.asIdeal.inertiaDeg (NumberField.RingOfIntegers K) = 1 := by
      have h1 := (ncard_primesOver_eq_finrank_iff_splitCompletely 𝔭).mp h𝔭
      rw [← Ideal.inertiaDegIn_eq_inertiaDeg 𝔭.asIdeal 𝔮.1.asIdeal (Gal(L/K))]
      exact h1.2
    have hnorm := Ideal.absNorm_pow_inertiaDeg (R := NumberField.RingOfIntegers K)
      (S := NumberField.RingOfIntegers L) 𝔭.asIdeal 𝔮.1.asIdeal
    rw [hf, pow_one] at hnorm
    rw [← hnorm]
  rw [fiberSum, tsum_fintype]
  rw [Finset.sum_congr rfl (fun 𝔮 _ => htermp 𝔮)]
  rw [Finset.sum_const, Finset.card_univ, ← Nat.card_eq_fintype_card,
    natCard_fiber_eq_ncard_primesOver, h𝔭, nsmul_eq_mul]

private lemma fiberSum_le_of_two_le_inertiaDegIn (K L : Type*) [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    (𝔭 : HeightOneSpectrum (NumberField.RingOfIntegers K))
    (h : 2 ≤ 𝔭.asIdeal.inertiaDegIn (NumberField.RingOfIntegers L))
    {s : ℝ} (hs : 1 ≤ s) :
    fiberSum K L s 𝔭 ≤ (Module.finrank K L : ℝ) *
      (Ideal.absNorm 𝔭.asIdeal : ℝ) ^ (-2 : ℝ) := by
  classical
  haveI : Fintype {𝔮 : HeightOneSpectrum (NumberField.RingOfIntegers L) //
      underPrime K L 𝔮 = 𝔭} :=
    Fintype.ofEquiv (𝔭.asIdeal.primesOver (NumberField.RingOfIntegers L))
      (fiberEquivPrimesOver K L 𝔭).symm
  have hterm : ∀ 𝔮 : {𝔮 : HeightOneSpectrum (NumberField.RingOfIntegers L) //
      underPrime K L 𝔮 = 𝔭},
      (Ideal.absNorm 𝔮.1.asIdeal : ℝ) ^ (-s) ≤
        (Ideal.absNorm 𝔭.asIdeal : ℝ) ^ (-2 : ℝ) := by
    intro 𝔮
    have hlies : 𝔮.1.asIdeal.LiesOver 𝔭.asIdeal :=
      (liesOver_iff_underPrime_eq K L 𝔭 𝔮.1).mpr 𝔮.2
    haveI := hlies
    have hf2 : 2 ≤ 𝔮.1.asIdeal.inertiaDeg (NumberField.RingOfIntegers K) := by
      rw [← Ideal.inertiaDegIn_eq_inertiaDeg 𝔭.asIdeal 𝔮.1.asIdeal (Gal(L/K))]
      exact h
    set N : ℝ := (Ideal.absNorm 𝔭.asIdeal : ℝ) with hN
    have hN0 : 0 ≤ N := by rw [hN]; exact Nat.cast_nonneg _
    have hN1 : 1 ≤ N := by
      rw [hN]
      have h2 : (2 : ℝ) ≤ (Ideal.absNorm 𝔭.asIdeal : ℝ) :=
        DedekindZeta.two_le_absNorm_primeIdeal 𝔭
      linarith
    have hexp : ((𝔮.1.asIdeal.inertiaDeg (NumberField.RingOfIntegers K) : ℕ) : ℝ) * (-s) ≤ (-2 : ℝ) := by
      have hf2' : (2 : ℝ) ≤ ((𝔮.1.asIdeal.inertiaDeg (NumberField.RingOfIntegers K) : ℕ) : ℝ) := by
        exact_mod_cast hf2
      nlinarith [hs, hf2']
    have hnorm : (Ideal.absNorm 𝔮.1.asIdeal : ℝ) = N ^
        (((𝔮.1.asIdeal.inertiaDeg (NumberField.RingOfIntegers K) : ℕ) : ℝ)) := by
      have hnat : Ideal.absNorm 𝔮.1.asIdeal = Ideal.absNorm 𝔭.asIdeal ^
          𝔮.1.asIdeal.inertiaDeg (NumberField.RingOfIntegers K) :=
        (Ideal.absNorm_pow_inertiaDeg (R := NumberField.RingOfIntegers K)
          (S := NumberField.RingOfIntegers L) 𝔭.asIdeal 𝔮.1.asIdeal).symm
      rw [hnat, Nat.cast_pow, Real.rpow_natCast, hN]
    rw [hnorm, ← Real.rpow_mul hN0]
    exact Real.rpow_le_rpow_of_exponent_le hN1 hexp
  rw [fiberSum, tsum_fintype]
  have hsum_le : (∑ 𝔮 : {𝔮 : HeightOneSpectrum (NumberField.RingOfIntegers L) //
        underPrime K L 𝔮 = 𝔭}, (Ideal.absNorm 𝔮.1.asIdeal : ℝ) ^ (-s))
      ≤ ∑ _𝔮 : {𝔮 : HeightOneSpectrum (NumberField.RingOfIntegers L) //
        underPrime K L 𝔮 = 𝔭}, (Ideal.absNorm 𝔭.asIdeal : ℝ) ^ (-2 : ℝ) :=
    Finset.sum_le_sum fun 𝔮 _ => hterm 𝔮
  refine le_trans hsum_le ?_
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg (Nat.cast_nonneg _) _)
  rw [Nat.cast_le, ← Nat.card_eq_fintype_card, natCard_fiber_eq_ncard_primesOver]
  exact ncard_primesOver_le_finrank 𝔭

private lemma fiberSum_le_mul_absNorm_rpow_neg_one (K L : Type*) [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    (𝔭 : HeightOneSpectrum (NumberField.RingOfIntegers K)) {s : ℝ} (hs : 1 ≤ s) :
    fiberSum K L s 𝔭 ≤ (Module.finrank K L : ℝ) *
      (Ideal.absNorm 𝔭.asIdeal : ℝ) ^ (-1 : ℝ) := by
  classical
  haveI : Fintype {𝔮 : HeightOneSpectrum (NumberField.RingOfIntegers L) //
      underPrime K L 𝔮 = 𝔭} :=
    Fintype.ofEquiv (𝔭.asIdeal.primesOver (NumberField.RingOfIntegers L))
      (fiberEquivPrimesOver K L 𝔭).symm
  have hterm : ∀ 𝔮 : {𝔮 : HeightOneSpectrum (NumberField.RingOfIntegers L) //
      underPrime K L 𝔮 = 𝔭},
      (Ideal.absNorm 𝔮.1.asIdeal : ℝ) ^ (-s) ≤
        (Ideal.absNorm 𝔭.asIdeal : ℝ) ^ (-1 : ℝ) := by
    intro 𝔮
    have hlies : 𝔮.1.asIdeal.LiesOver 𝔭.asIdeal :=
      (liesOver_iff_underPrime_eq K L 𝔭 𝔮.1).mpr 𝔮.2
    haveI := hlies
    have hf1 : 1 ≤ 𝔮.1.asIdeal.inertiaDeg (NumberField.RingOfIntegers K) := by
      have hpos := Ideal.inertiaDeg_pos 𝔮.1.asIdeal (NumberField.RingOfIntegers K)
      omega
    set N : ℝ := (Ideal.absNorm 𝔭.asIdeal : ℝ) with hN
    have hN0 : 0 ≤ N := by rw [hN]; exact Nat.cast_nonneg _
    have hN1 : 1 ≤ N := by
      rw [hN]
      have h2 : (2 : ℝ) ≤ (Ideal.absNorm 𝔭.asIdeal : ℝ) :=
        DedekindZeta.two_le_absNorm_primeIdeal 𝔭
      linarith
    have hexp : ((𝔮.1.asIdeal.inertiaDeg (NumberField.RingOfIntegers K) : ℕ) : ℝ) * (-s)
        ≤ (-1 : ℝ) := by
      have hf1' : (1 : ℝ) ≤ ((𝔮.1.asIdeal.inertiaDeg (NumberField.RingOfIntegers K) : ℕ) : ℝ) := by
        exact_mod_cast hf1
      nlinarith [hs, hf1']
    have hnorm : (Ideal.absNorm 𝔮.1.asIdeal : ℝ) = N ^
        (((𝔮.1.asIdeal.inertiaDeg (NumberField.RingOfIntegers K) : ℕ) : ℝ)) := by
      have hnat : Ideal.absNorm 𝔮.1.asIdeal = Ideal.absNorm 𝔭.asIdeal ^
          𝔮.1.asIdeal.inertiaDeg (NumberField.RingOfIntegers K) :=
        (Ideal.absNorm_pow_inertiaDeg (R := NumberField.RingOfIntegers K)
          (S := NumberField.RingOfIntegers L) 𝔭.asIdeal 𝔮.1.asIdeal).symm
      rw [hnat, Nat.cast_pow, Real.rpow_natCast, hN]
    rw [hnorm, ← Real.rpow_mul hN0]
    exact Real.rpow_le_rpow_of_exponent_le hN1 hexp
  rw [fiberSum, tsum_fintype]
  have hsum_le : (∑ 𝔮 : {𝔮 : HeightOneSpectrum (NumberField.RingOfIntegers L) //
        underPrime K L 𝔮 = 𝔭}, (Ideal.absNorm 𝔮.1.asIdeal : ℝ) ^ (-s))
      ≤ ∑ _𝔮 : {𝔮 : HeightOneSpectrum (NumberField.RingOfIntegers L) //
        underPrime K L 𝔮 = 𝔭}, (Ideal.absNorm 𝔭.asIdeal : ℝ) ^ (-1 : ℝ) :=
    Finset.sum_le_sum fun 𝔮 _ => hterm 𝔮
  refine le_trans hsum_le ?_
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg (Nat.cast_nonneg _) _)
  rw [Nat.cast_le, ← Nat.card_eq_fintype_card, natCard_fiber_eq_ncard_primesOver]
  exact ncard_primesOver_le_finrank 𝔭

/-! ## Finiteness of the ramified primes below -/

private lemma finite_setOf_ramificationIdxIn_ne_one (K L : Type*) [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L] :
    {𝔭 : HeightOneSpectrum (NumberField.RingOfIntegers K) |
      𝔭.asIdeal.ramificationIdxIn (NumberField.RingOfIntegers L) ≠ 1}.Finite := by
  classical
  have hA : {𝔮 : HeightOneSpectrum (NumberField.RingOfIntegers L) |
      𝔮.asIdeal.ramificationIdx (NumberField.RingOfIntegers K) ≠ 1}.Finite :=
    Commons.NumberTheory.NumberField.finite_setOf_ramificationIdx_ne_one
  refine (hA.image (fun 𝔮 : HeightOneSpectrum (NumberField.RingOfIntegers L) =>
    underPrime K L 𝔮)).subset ?_
  intro 𝔭 h𝔭
  simp only [Set.mem_ofPred_eq] at h𝔭
  obtain ⟨P⟩ := (inferInstance : Nonempty (𝔭.asIdeal.primesOver (NumberField.RingOfIntegers L)))
  refine ⟨⟨P.1, P.2.1, Ideal.ne_bot_of_mem_primesOver 𝔭.ne_bot P.2⟩, ?_, ?_⟩
  · simp only [Set.mem_ofPred_eq]
    rw [← Ideal.ramificationIdxIn_eq_ramificationIdx 𝔭.asIdeal P.1 (Gal(L/K))]
    exact h𝔭
  · exact HeightOneSpectrum.ext (by rw [underPrime_asIdeal]; exact P.2.2.over.symm)

/-! ## A uniform bound for the tail -/

private lemma exists_bound_fiberSum_compl (K L : Type*) [Field K] [NumberField K] [Field L]
    [NumberField L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L] :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ s : ℝ, 1 < s →
      (∑' 𝔭 : ((splitSet K L)ᶜ : Set (HeightOneSpectrum (NumberField.RingOfIntegers K))),
        fiberSum K L s 𝔭) ≤ M := by
  classical
  let Bad : Set (HeightOneSpectrum (NumberField.RingOfIntegers K)) :=
    {𝔭 | 𝔭.asIdeal.ramificationIdxIn (NumberField.RingOfIntegers L) ≠ 1}
  have hBadFin : Bad.Finite := by
    simpa only [Bad] using finite_setOf_ramificationIdxIn_ne_one K L
  let badPart : HeightOneSpectrum (NumberField.RingOfIntegers K) → ℝ := fun 𝔭 =>
    (Module.finrank K L : ℝ) * (Ideal.absNorm 𝔭.asIdeal : ℝ) ^ (-1 : ℝ)
  let maj : HeightOneSpectrum (NumberField.RingOfIntegers K) → ℝ := fun 𝔭 =>
    Set.indicator Bad badPart 𝔭
      + (Module.finrank K L : ℝ) * (Ideal.absNorm 𝔭.asIdeal : ℝ) ^ (-2 : ℝ)
  have hmaj_nonneg : ∀ 𝔭, 0 ≤ maj 𝔭 := by
    intro 𝔭
    have h1 : 0 ≤ Set.indicator Bad badPart 𝔭 :=
      Set.indicator_nonneg (fun 𝔮 _ => mul_nonneg (Nat.cast_nonneg _)
        (Real.rpow_nonneg (Nat.cast_nonneg _) _)) 𝔭
    have h2 : 0 ≤ (Module.finrank K L : ℝ) * (Ideal.absNorm 𝔭.asIdeal : ℝ) ^ (-2 : ℝ) :=
      mul_nonneg (Nat.cast_nonneg _) (Real.rpow_nonneg (Nat.cast_nonneg _) _)
    dsimp only [maj]
    linarith
  refine ⟨∑' 𝔭, maj 𝔭, tsum_nonneg hmaj_nonneg, fun s hs => ?_⟩
  have hmaj_sum : Summable maj := by
    have h1 : Summable (Set.indicator Bad badPart) := by
      haveI : Fintype Bad := hBadFin.fintype
      have hf : Summable (fun 𝔭 : Bad => badPart 𝔭.1) := Summable.of_finite
      have h2 : Summable (badPart ∘ Subtype.val) := hf
      exact (summable_subtype_iff_indicator (s := Bad) (f := badPart)).mp h2
    have h2 : Summable (fun 𝔭 : HeightOneSpectrum (NumberField.RingOfIntegers K) =>
        (Module.finrank K L : ℝ) * (Ideal.absNorm 𝔭.asIdeal : ℝ) ^ (-2 : ℝ)) :=
      (summable_primeIdealZetaSum (K := K) (by norm_num : (1 : ℝ) < 2)).mul_left _
    have h3 := h1.add h2
    simpa only [maj] using h3
  have hsummF : Summable (fun 𝔭 : HeightOneSpectrum (NumberField.RingOfIntegers K) =>
      fiberSum K L s 𝔭) :=
    summable_fiberSum K L (summable_primeIdealZetaSum (K := L) hs)
  have hind : Summable (fun 𝔭 : HeightOneSpectrum (NumberField.RingOfIntegers K) =>
      Set.indicator ((splitSet K L)ᶜ) (fun 𝔭 => fiberSum K L s 𝔭) 𝔭) :=
    (summable_subtype_iff_indicator (s := (splitSet K L)ᶜ)
      (f := fun 𝔭 => fiberSum K L s 𝔭)).mp (hsummF.subtype _)
  rw [tsum_subtype]
  refine Summable.tsum_le_tsum (fun 𝔭 => ?_) hind hmaj_sum
  by_cases h𝔭 : 𝔭 ∈ (splitSet K L)ᶜ
  · rw [Set.indicator_of_mem h𝔭]
    have h𝔭notS : 𝔭 ∉ splitSet K L := by simpa using h𝔭
    by_cases hf2 : 2 ≤ 𝔭.asIdeal.inertiaDegIn (NumberField.RingOfIntegers L)
    · have h1 := fiberSum_le_of_two_le_inertiaDegIn K L 𝔭 hf2 (le_of_lt hs)
      have h2 : 0 ≤ Set.indicator Bad badPart 𝔭 :=
        Set.indicator_nonneg (fun 𝔮 _ => mul_nonneg (Nat.cast_nonneg _)
          (Real.rpow_nonneg (Nat.cast_nonneg _) _)) 𝔭
      dsimp only [maj]
      linarith
    · have hf1 : 𝔭.asIdeal.inertiaDegIn (NumberField.RingOfIntegers L) = 1 := by
        have hpos : 𝔭.asIdeal.inertiaDegIn (NumberField.RingOfIntegers L) ≠ 0 :=
          Ideal.inertiaDegIn_ne_zero (A := NumberField.RingOfIntegers K)
            (B := NumberField.RingOfIntegers L) (G := Gal(L/K)) (p := 𝔭.asIdeal)
        omega
      have h𝔭Bad : 𝔭 ∈ Bad := by
        simp only [Bad, Set.mem_ofPred_eq]
        intro he1
        exact h𝔭notS (by
          rw [splitSet, Set.mem_ofPred_eq]
          exact (ncard_primesOver_eq_finrank_iff_splitCompletely 𝔭).mpr ⟨he1, hf1⟩)
      have h1 := fiberSum_le_mul_absNorm_rpow_neg_one K L 𝔭 (le_of_lt hs)
      have h2 : Set.indicator Bad badPart 𝔭 = badPart 𝔭 := Set.indicator_of_mem h𝔭Bad badPart
      have h3 : 0 ≤ (Module.finrank K L : ℝ) * (Ideal.absNorm 𝔭.asIdeal : ℝ) ^ (-2 : ℝ) :=
        mul_nonneg (Nat.cast_nonneg _) (Real.rpow_nonneg (Nat.cast_nonneg _) _)
      dsimp only [maj, badPart] at *
      rw [h2] at *
      linarith
  · rw [Set.indicator_of_notMem h𝔭]
    exact hmaj_nonneg 𝔭

/-! ## The main theorem -/

theorem hasDirichletDensity_primes_splitsCompletely {K L : Type*} [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L] :
    NumberField.Set.HasDirichletDensity
      {𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K) |
        (𝔭.asIdeal.primesOver (NumberField.RingOfIntegers L)).ncard = Module.finrank K L}
      (1 / (Module.finrank K L : ℝ)) := by
  classical
  change NumberField.Set.HasDirichletDensity (splitSet K L) (1 / (Module.finrank K L : ℝ))
  obtain ⟨M, hM0, hMb⟩ := exists_bound_fiberSum_compl (K := K) (L := L)
  have hnpos : (0 : ℝ) < (Module.finrank K L : ℝ) := by
    exact_mod_cast (Module.finrank_pos (R := K) (M := L) : 0 < Module.finrank K L)
  have hℓ : (Module.finrank K L : ℝ) ≠ 0 := ne_of_gt hnpos
  rw [NumberField.Set.HasDirichletDensity]
  let partS : ℝ → ℝ := fun s => NumberField.Set.primeIdealZetaSum (splitSet K L) s
  let fullK : ℝ → ℝ := fun s =>
    NumberField.Set.primeIdealZetaSum (Set.univ :
      Set (HeightOneSpectrum (NumberField.RingOfIntegers K))) s
  let fullL : ℝ → ℝ := fun s =>
    NumberField.Set.primeIdealZetaSum (Set.univ :
      Set (HeightOneSpectrum (NumberField.RingOfIntegers L))) s
  let tail : ℝ → ℝ := fun s =>
    ∑' 𝔭 : ((splitSet K L)ᶜ : Set (HeightOneSpectrum (NumberField.RingOfIntegers K))),
      fiberSum K L s 𝔭
  change Tendsto (fun s : ℝ => partS s / fullK s) (𝓝[>] 1) (𝓝 (1 / (Module.finrank K L : ℝ)))
  have hBA : (fun s : ℝ => fullL s - fullK s) =O[𝓝[>] 1] (fun _ => (1 : ℝ)) := by
    have h1 : (fun s : ℝ => fullL s - Real.log (1 / (s - 1))) =O[𝓝[>] 1] (fun _ => (1 : ℝ)) := by
      simpa only [fullL] using isBigO_primeIdealZetaSum_sub_log L
    have h2 : (fun s : ℝ => fullK s - Real.log (1 / (s - 1))) =O[𝓝[>] 1] (fun _ => (1 : ℝ)) := by
      simpa only [fullK] using isBigO_primeIdealZetaSum_sub_log K
    simpa only [sub_sub_sub_cancel_right] using h1.sub h2
  have htail_nonneg : ∀ s : ℝ, 0 ≤ tail s := by
    intro s
    dsimp only [tail]
    refine tsum_nonneg fun 𝔭 => ?_
    rw [fiberSum]
    exact tsum_nonneg fun 𝔮 => Real.rpow_nonneg (Nat.cast_nonneg _) _
  have htail : (fun s : ℝ => tail s) =O[𝓝[>] 1] (fun _ => (1 : ℝ)) := by
    refine IsBigO.of_bound M ?_
    filter_upwards [self_mem_nhdsWithin] with s hs
    have hs1 : 1 < s := Set.mem_Ioi.mp hs
    rw [Real.norm_eq_abs, abs_of_nonneg (htail_nonneg s), norm_one, mul_one]
    exact hMb s hs1
  have hident : ∀ᶠ s in 𝓝[>] (1 : ℝ),
      fullL s = (Module.finrank K L : ℝ) * partS s + tail s := by
    filter_upwards [self_mem_nhdsWithin] with s hs
    have hs1 : 1 < s := Set.mem_Ioi.mp hs
    have hfL : Summable (fun 𝔮 : HeightOneSpectrum (NumberField.RingOfIntegers L) =>
        (Ideal.absNorm 𝔮.asIdeal : ℝ) ^ (-s)) := summable_primeIdealZetaSum hs1
    have hsum : Summable (fun 𝔭 : HeightOneSpectrum (NumberField.RingOfIntegers K) =>
        fiberSum K L s 𝔭) := summable_fiberSum K L hfL
    have hsplit := Summable.tsum_subtype_add_tsum_subtype_compl hsum (splitSet K L)
    have hfib := tsum_fiberwise_underPrime K L hfL
    have hSpart : (∑' 𝔭 : splitSet K L, fiberSum K L s 𝔭) =
        (Module.finrank K L : ℝ) * partS s := by
      dsimp only [partS]
      rw [NumberField.Set.primeIdealZetaSum_def, ← tsum_mul_left]
      refine tsum_congr fun 𝔭 => ?_
      refine fiberSum_eq_of_split K L 𝔭.1 ?_ s
      have h2 := 𝔭.2
      simpa only [splitSet, Set.mem_ofPred_eq] using h2
    have htail_eq : (∑' 𝔭 : ((splitSet K L)ᶜ :
        Set (HeightOneSpectrum (NumberField.RingOfIntegers K))), fiberSum K L s 𝔭) = tail s := rfl
    rw [show fullL s = ∑' 𝔮 : HeightOneSpectrum (NumberField.RingOfIntegers L),
        (Ideal.absNorm 𝔮.asIdeal : ℝ) ^ (-s) from by
      dsimp only [fullL]
      rw [NumberField.Set.primeIdealZetaSum_def]
      exact tsum_univ (fun 𝔮 : HeightOneSpectrum (NumberField.RingOfIntegers L) =>
        (Ideal.absNorm 𝔮.asIdeal : ℝ) ^ (-s))]
    rw [hfib, ← hsplit, hSpart, htail_eq]
  have hD : (fun s : ℝ => partS s - (1 / (Module.finrank K L : ℝ)) * fullK s)
      =O[𝓝[>] 1] (fun _ => (1 : ℝ)) := by
    have hcore : (fun s : ℝ => (fullL s - fullK s) - tail s) =O[𝓝[>] 1] (fun _ => (1 : ℝ)) :=
      hBA.sub htail
    have hscaled : (fun s : ℝ => (1 / (Module.finrank K L : ℝ)) *
        ((fullL s - fullK s) - tail s)) =O[𝓝[>] 1] (fun _ => (1 : ℝ)) :=
      hcore.const_mul_left _
    have hEq : (fun s : ℝ => (1 / (Module.finrank K L : ℝ)) *
        ((fullL s - fullK s) - tail s))
        =ᶠ[𝓝[>] 1] (fun s : ℝ => partS s - (1 / (Module.finrank K L : ℝ)) * fullK s) := by
      filter_upwards [hident] with s hs
      have h1 : partS s = (fullL s - tail s) / (Module.finrank K L : ℝ) := by
        rw [eq_div_iff hℓ]
        rw [hs]
        ring
      rw [h1]
      field_simp
      ring
    exact hscaled.congr' hEq (EventuallyEq.refl _ _)
  have hKtop : Tendsto fullK (𝓝[>] 1) atTop := by
    simpa only [fullK] using tendsto_primeIdealZetaSum_univ_nhdsGT K
  have hstep : Tendsto (fun s : ℝ =>
      (partS s - (1 / (Module.finrank K L : ℝ)) * fullK s) / fullK s) (𝓝[>] 1) (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    obtain ⟨c, hc⟩ := hD.bound
    have hcb : ∀ᶠ s in 𝓝[>] 1,
        ‖partS s - (1 / (Module.finrank K L : ℝ)) * fullK s‖ ≤ max c 0 := by
      filter_upwards [hc] with s hs
      exact le_trans (by simpa using hs) (le_max_left c 0)
    have hg : Tendsto (fun s : ℝ => max c 0 * (fullK s)⁻¹) (𝓝[>] 1) (𝓝 0) := by
      have h0 := hKtop.inv_tendsto_atTop.const_mul (max c 0)
      simpa using h0
    refine squeeze_zero' ?_ ?_ hg
    · filter_upwards with s
      exact norm_nonneg _
    · filter_upwards [hcb, hKtop.eventually (eventually_gt_atTop (0 : ℝ))] with s hbs hpos
      have hbs' : |partS s - (1 / (Module.finrank K L : ℝ)) * fullK s| ≤ max c 0 := by
        rwa [Real.norm_eq_abs] at hbs
      rw [norm_div, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos hpos]
      exact le_trans (div_le_div_of_nonneg_right hbs' (le_of_lt hpos))
        (le_of_eq (div_eq_mul_inv _ _))
  have hfinal : Tendsto (fun s : ℝ =>
      (partS s - (1 / (Module.finrank K L : ℝ)) * fullK s) / fullK s +
        1 / (Module.finrank K L : ℝ)) (𝓝[>] 1) (𝓝 (1 / (Module.finrank K L : ℝ))) := by
    have h0 := hstep.add (tendsto_const_nhds (x := 1 / (Module.finrank K L : ℝ))
      (f := 𝓝[>] (1 : ℝ)))
    simpa using h0
  refine Tendsto.congr' ?_ hfinal
  filter_upwards [hKtop.eventually (eventually_gt_atTop (0 : ℝ))] with s hpos
  have hne : fullK s ≠ 0 := ne_of_gt hpos
  field_simp
  ring

end Commons.NumberTheory.NumberField.Set
