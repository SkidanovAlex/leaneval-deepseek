import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.PicardGroup
import Mathlib.Algebra.AffineMonoid.Basic
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.Data.Int.Star
import Mathlib.NumberTheory.Cyclotomic.Basic
import Mathlib.RingTheory.DedekindDomain.Different
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.Valuation.LocalSubring
import Mathlib.Topology.Connected.Separation
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.NumberTheory.NumberField.Completion.FinitePlace
import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.Topology.MetricSpace.Ultra.TotallySeparated
import Submission.Commons.NumberTheory.NumberField.finite_primesOver
import Submission.Work.SSGRoute.TatePoitouRoute.FinitenessHM.adicExp_le_iff_trace_mem
import Submission.Work.SSGRoute.TatePoitouRoute.FinitenessHM.adicLocExpBoundByRamification
import Submission.Work.SSGRoute.TatePoitouRoute.FinitenessHM.exists_cyclotomic_completion_finrank
import Submission.Work.SSGRoute.TatePoitouRoute.FinitenessHM.exists_mem_adicExp_eq_fractionalIdeal_count
import Submission.Work.SSGRoute.TatePoitouRoute.FinitenessHM.ramificationIdx_under_ringOfIntegers_rat
import Submission.Work.SSGRoute.TatePoitouRoute.FinitenessHM.residueField_pow_generated_by_residue
import Submission.Work.SSGRoute.TatePoitouRoute.FinitenessHM.sum_trace_adicCompletion_eq_trace

/-!
# The exponent of a rational prime in the different of a number field

For a number field `K`, a rational prime `p` and a prime `P | (p)` of `𝓞 K`, the exponent of `P`
in the different `𝔡_{K/ℤ}` is at most `e · (1 + e · v_p(e))`, `e = P.ramificationIdx ℤ`.

The proof goes through the `P`-adic completion `L := Q.adicCompletion K` and splits into

* **the local bound** (`adicLocExpBoundByRamification`, proved): the exponent `adicLocExp Q₀ Q` of
  the maximal ideal in the local different `𝔡_{𝒪_L/ℤ_p}` is at most `e(1+e·v_p(e))`;
* **the base-change glue** (`ramificationIdx_under_ringOfIntegers_rat`, proved): the ramification
  index over `ℤ` equals the one over `𝓞 ℚ`;
* **the completion bridge** (`count_le_adicLocExp_clean`, proved here): the *global* exponent
  `count_P(𝔡_{K/ℤ})` is at most the local exponent `adicLocExp Q₀ Q`.

The bridge is proved with the trace criterion for the different.  Suppose
`𝔡_{K/ℤ} ≤ Q^m` with `m = adicLocExp + 1`.  Take `x ∈ (Q^m)^{-1}` with `adicExp_Q x = -m`
(`exists_mem_adicExp_eq_fractionalIdeal_count`); then `x` is integral at every prime other than
`Q`, and by the trace criterion `Tr_{K/ℚ}(x·b) ∈ ℤ` for every `b ∈ 𝓞 K`.  The local–global trace
identity `∑_{Q' | (p)} Tr_{K_{Q'}}(x·b) = Tr_{K/ℚ}(x·b)` then shows that the `Q`-component
`Tr_{K_Q}(x·b)` is `p`-adically integral for every `b ∈ 𝓞 K`; since the trace pairing
`z ↦ Tr_{K_Q}(x·z)` is continuous and the ring of integers of `K_Q` is the closure of `𝓞 K`
(`ringOfIntegers_dense_in_adicIntegers`), this holds for all `z ∈ 𝒪_{K_Q}`.  The local trace
criterion `adicExp_le_iff_trace_mem` then gives `v_{K_Q}(x) ≥ -adicLocExp`, contradicting
`v_{K_Q}(x) = -m = -(adicLocExp+1)`.
-/

namespace Work.SSGRoute.TatePoitouRoute.FinitenessHM

open IsDedekindDomain
open scoped NumberField nonZeroDivisors WithZero Valued
set_option linter.style.haveILetI false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

noncomputable section

/-- Continuity of the local trace pairing against a fixed element. -/
private theorem trace_mul_continuous {K : Type*} [Field K] [NumberField K]
    (Q0 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ℚ))
    (Q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (hQ : Q.asIdeal.LiesOver Q0.asIdeal) (x : Q.adicCompletion K) :
    letI : Algebra (Q0.adicCompletion ℚ) (Q.adicCompletion K) :=
      RingHom.toAlgebra (Commons.RingTheory.Henselian.adicCompletionMap Q0 Q hQ)
    Continuous (fun z : Q.adicCompletion K =>
      Algebra.trace (Q0.adicCompletion ℚ) (Q.adicCompletion K) (x * z)) := by
  letI : Algebra (Q0.adicCompletion ℚ) (Q.adicCompletion K) :=
    RingHom.toAlgebra (Commons.RingTheory.Henselian.adicCompletionMap Q0 Q hQ)
  have hcont : Continuous (algebraMap (Q0.adicCompletion ℚ) (Q.adicCompletion K)) := by
    change Continuous (Commons.RingTheory.Henselian.adicCompletionMap Q0 Q hQ :
      Q0.adicCompletion ℚ → Q.adicCompletion K)
    exact Commons.RingTheory.Henselian.adicCompletionMap_continuous Q0 Q hQ
  haveI : ContinuousSMul (Q0.adicCompletion ℚ) (Q.adicCompletion K) :=
    continuousSMul_of_algebraMap (Q0.adicCompletion ℚ) (Q.adicCompletion K) hcont
  haveI hFD : FiniteDimensional (Q0.adicCompletion ℚ) (Q.adicCompletion K) :=
    Commons.NumberTheory.NumberField.Completion.module_finite_adicCompletion Q0 Q hQ
  have h1 : Continuous (fun z : Q.adicCompletion K => x * z) :=
    continuous_const.mul continuous_id
  have h2 : Continuous (Algebra.trace (Q0.adicCompletion ℚ) (Q.adicCompletion K)) :=
    LinearMap.continuous_of_finiteDimensional _
  exact h2.comp h1

/-- The trace of an integral element of the local completion is integral. -/
private theorem trace_mem_integers_of_mem {K : Type*} [Field K] [NumberField K]
    (Q0 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ℚ))
    (Q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (hQ : Q.asIdeal.LiesOver Q0.asIdeal)
    (z : Q.adicCompletion K) (hz : z ∈ (Q.adicCompletionIntegers K : Set (Q.adicCompletion K))) :
    letI : Algebra (Q0.adicCompletionIntegers ℚ) (Q.adicCompletionIntegers K) :=
      RingHom.toAlgebra
        (Commons.NumberTheory.NumberField.Completion.adicCompletionMapIntegers Q0 Q hQ)
    letI : Algebra (Q0.adicCompletion ℚ) (Q.adicCompletion K) :=
      RingHom.toAlgebra (Commons.RingTheory.Henselian.adicCompletionMap Q0 Q hQ)
    Algebra.trace (Q0.adicCompletion ℚ) (Q.adicCompletion K) z ∈
      (Q0.adicCompletionIntegers ℚ : Set (Q0.adicCompletion ℚ)) := by
  letI : Algebra (Q0.adicCompletionIntegers ℚ) (Q.adicCompletionIntegers K) :=
    RingHom.toAlgebra
      (Commons.NumberTheory.NumberField.Completion.adicCompletionMapIntegers Q0 Q hQ)
  letI : Algebra (Q0.adicCompletion ℚ) (Q.adicCompletion K) :=
    RingHom.toAlgebra (Commons.RingTheory.Henselian.adicCompletionMap Q0 Q hQ)
  haveI hIC : IsIntegralClosure (Q.adicCompletionIntegers K) (Q0.adicCompletionIntegers ℚ)
      (Q.adicCompletion K) :=
    Commons.NumberTheory.NumberField.Completion.isIntegralClosure_adicCompletionIntegers_extension
      Q0 Q hQ
  haveI hFD : FiniteDimensional (Q0.adicCompletion ℚ) (Q.adicCompletion K) :=
    Commons.NumberTheory.NumberField.Completion.module_finite_adicCompletion Q0 Q hQ
  have hz' : IsIntegral (Q0.adicCompletionIntegers ℚ) z :=
    (IsIntegralClosure.isIntegral_iff (A := Q.adicCompletionIntegers K)).mpr ⟨⟨z, hz⟩, rfl⟩
  have htr : IsIntegral (Q0.adicCompletionIntegers ℚ)
      (Algebra.trace (Q0.adicCompletion ℚ) (Q.adicCompletion K) z) :=
    Algebra.isIntegral_trace hz'
  obtain ⟨y, hy⟩ := (IsIntegrallyClosed.isIntegral_iff).mp htr
  exact hy ▸ y.2


/-- An element of `(Q^m)^{-1}` is integral at every other prime. -/
private theorem adicExp_nonneg_of_mem_inv {K : Type*} [Field K] [NumberField K]
    (Q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)) (m : ℕ) {x : K}
    (hx : x ∈ (((Q.asIdeal ^ m : Ideal (NumberField.RingOfIntegers K)) :
      FractionalIdeal (nonZeroDivisors (NumberField.RingOfIntegers K)) K)⁻¹))
    (Q' : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (hne : Q' ≠ Q) :
    (0 : ℤ) ≤ adicExp Q' x := by
  classical
  by_cases hx0 : x = 0
  · rw [hx0, adicExp_zero]
  have hnotle : ¬ (Q.asIdeal ≤ Q'.asIdeal) := by
    intro h
    have heq : Q.asIdeal = Q'.asIdeal :=
      Ideal.IsMaximal.eq_of_le Q.isMaximal Q'.isPrime.ne_top h
    exact hne (HeightOneSpectrum.ext heq.symm)
  obtain ⟨a, haQ, haQ'⟩ : ∃ a : NumberField.RingOfIntegers K, a ∈ Q.asIdeal ∧ a ∉ Q'.asIdeal := by
    by_contra h
    exact hnotle fun b hb => by
      by_contra hb'
      exact h ⟨b, hb, hb'⟩
  have ha0 : a ≠ 0 := fun h0 => haQ' (h0 ▸ Q'.asIdeal.zero_mem)
  have hpa : a ^ m ∈ Q.asIdeal ^ m := Ideal.pow_mem_pow haQ m
  have hI0 : (((Q.asIdeal ^ m : Ideal (NumberField.RingOfIntegers K)) :
      FractionalIdeal (nonZeroDivisors (NumberField.RingOfIntegers K)) K)) ≠ 0 :=
    FractionalIdeal.coeIdeal_ne_zero.mpr (pow_ne_zero m Q.ne_bot)
  have hy : algebraMap (NumberField.RingOfIntegers K) K (a ^ m) ∈
      (((Q.asIdeal ^ m : Ideal (NumberField.RingOfIntegers K)) :
        FractionalIdeal (nonZeroDivisors (NumberField.RingOfIntegers K)) K)) :=
    FractionalIdeal.mem_coeIdeal _ |>.mpr ⟨a ^ m, hpa, rfl⟩
  have hmem1 : x * algebraMap (NumberField.RingOfIntegers K) K (a ^ m) ∈
      (1 : FractionalIdeal (nonZeroDivisors (NumberField.RingOfIntegers K)) K) :=
    (FractionalIdeal.mem_inv_iff hI0).mp hx _ hy
  obtain ⟨c, hc⟩ := (FractionalIdeal.mem_one_iff _).mp hmem1
  have ha0' : algebraMap (NumberField.RingOfIntegers K) K a ≠ 0 :=
    fun h => ha0 (FaithfulSMul.algebraMap_injective _ _ h)
  have hmapne : algebraMap (NumberField.RingOfIntegers K) K (a ^ m) ≠ 0 :=
    fun h => pow_ne_zero m ha0 (FaithfulSMul.algebraMap_injective _ _ h)
  have h1 : (0 : ℤ) ≤ adicExp Q' (x * algebraMap (NumberField.RingOfIntegers K) K (a ^ m)) := by
    rw [← hc]
    exact (adicExp_nonneg_iff Q' _).mpr (by
      rw [HeightOneSpectrum.valuation_of_algebraMap]
      exact HeightOneSpectrum.intValuation_le_one Q' c)
  have h3 : adicExp Q' (algebraMap (NumberField.RingOfIntegers K) K (a ^ m)) = 0 := by
    rw [map_pow, adicExp_pow Q' ha0' m,
      adicExp_eq_zero_iff Q' ha0' |>.mpr (by
        rw [HeightOneSpectrum.valuation_of_algebraMap, HeightOneSpectrum.intValuation_eq_one_iff]
        exact haQ'),
      mul_zero]
  have h2 : adicExp Q' (x * algebraMap (NumberField.RingOfIntegers K) K (a ^ m)) =
      adicExp Q' x + adicExp Q' (algebraMap (NumberField.RingOfIntegers K) K (a ^ m)) :=
    adicExp_mul Q' hx0 hmapne
  linarith [h1, h2, h3]


/-- **The local trace of `x · b` at `Q` is integral**, for `x` in the global trace dual which is
integral away from `Q`. -/
private theorem trace_mem_of_forall_ringOfIntegers {K : Type*} [Field K] [NumberField K]
    (Q0 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ℚ))
    (Q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (hQ : Q.asIdeal.LiesOver Q0.asIdeal) (x : K)
    (hx : x ∈ FractionalIdeal.dual ℤ ℚ
      (1 : FractionalIdeal (nonZeroDivisors (NumberField.RingOfIntegers K)) K))
    (hxint : ∀ Q' : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K),
        Q'.asIdeal.LiesOver Q0.asIdeal → Q' ≠ Q → 0 ≤ adicExp Q' x) :
    letI : Algebra (Q0.adicCompletion ℚ) (Q.adicCompletion K) :=
      RingHom.toAlgebra (Commons.RingTheory.Henselian.adicCompletionMap Q0 Q hQ)
    ∀ b : NumberField.RingOfIntegers K,
      Algebra.trace (Q0.adicCompletion ℚ) (Q.adicCompletion K)
        (algebraMap K (Q.adicCompletion K) (x * algebraMap (NumberField.RingOfIntegers K) K b)) ∈
      (Q0.adicCompletionIntegers ℚ : Set (Q0.adicCompletion ℚ)) := by
  classical
  letI hAlgQ : Algebra (Q0.adicCompletion ℚ) (Q.adicCompletion K) :=
    RingHom.toAlgebra (Commons.RingTheory.Henselian.adicCompletionMap Q0 Q hQ)
  letI hQ0alg : Algebra ℚ (Q0.adicCompletion ℚ) :=
    HeightOneSpectrum.instAlgebraAdicCompletion (R := NumberField.RingOfIntegers ℚ) (K := ℚ) (S := ℚ) Q0
  intro b
  let ι := {Q' : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K) //
    Q'.asIdeal.LiesOver Q0.asIdeal}
  haveI : Fintype ι :=
    Fintype.ofEquiv _ (Commons.NumberTheory.NumberField.Completion.primesOverEquiv Q0).symm
  let Qι : ι := ⟨Q, hQ⟩
  letI : ∀ Q' : ι, Algebra (Q0.adicCompletion ℚ) (Q'.1.adicCompletion K) :=
    fun Q' => RingHom.toAlgebra (Commons.RingTheory.Henselian.adicCompletionMap Q0 Q'.1 Q'.2)
  have htrace : Algebra.trace ℚ K (x * algebraMap (NumberField.RingOfIntegers K) K b) ∈
      Set.range (algebraMap ℤ ℚ) := by
    have hb1 : algebraMap (NumberField.RingOfIntegers K) K b ∈
        (1 : FractionalIdeal (nonZeroDivisors (NumberField.RingOfIntegers K)) K) :=
      (mem_one_fractionalIdeal_iff (B := NumberField.RingOfIntegers K) (L := K)
        (algebraMap (NumberField.RingOfIntegers K) K b)).mpr ⟨b, rfl⟩
    have h1 := (FractionalIdeal.mem_dual (A := ℤ) (K := ℚ)
      (B := NumberField.RingOfIntegers K) (L := K) one_ne_zero).mp hx
      (algebraMap (NumberField.RingOfIntegers K) K b) hb1
    rwa [Algebra.traceForm_apply] at h1
  let f : ι → Q0.adicCompletion ℚ := fun Q' =>
    Algebra.trace (Q0.adicCompletion ℚ) (Q'.1.adicCompletion K)
      (algebraMap K (Q'.1.adicCompletion K)
        (x * algebraMap (NumberField.RingOfIntegers K) K b))
  have hsum_int : (∑ Q' : ι, f Q') ∈
      (Q0.adicCompletionIntegers ℚ : Set (Q0.adicCompletion ℚ)) := by
    have hgl := sum_trace_adicCompletion_eq_trace (K := K) Q0
      (x * algebraMap (NumberField.RingOfIntegers K) K b)
    obtain ⟨k, hk⟩ := htrace
    rw [hgl, ← hk]
    have heq : algebraMap ℚ (Q0.adicCompletion ℚ) (algebraMap ℤ ℚ k) =
        ((k : ℤ) : Q0.adicCompletion ℚ) := by
      change ((algebraMap ℚ (Q0.adicCompletion ℚ)).comp (algebraMap ℤ ℚ)) k =
        ((k : ℤ) : Q0.adicCompletion ℚ)
      exact map_intCast _ k
    rw [heq]
    exact intCast_mem (Q0.adicCompletionIntegers ℚ) k
  have herase_int : (∑ Q' ∈ Finset.univ.erase Qι, f Q') ∈
      (Q0.adicCompletionIntegers ℚ : Set (Q0.adicCompletion ℚ)) := by
    refine Subring.sum_mem _ (fun Q' hQ' => ?_)
    have hQ'ne : Q' ≠ Qι := by
      rintro rfl
      exact Finset.notMem_erase Qι Finset.univ hQ'
    have hQ'ne' : Q'.1 ≠ Q := fun h => hQ'ne (Subtype.ext h)
    have hxQ' : (0 : ℤ) ≤ adicExp Q'.1 x := hxint Q'.1 Q'.2 hQ'ne'
    have hxq_int : algebraMap K (Q'.1.adicCompletion K) x ∈
        (Q'.1.adicCompletionIntegers K : Set (Q'.1.adicCompletion K)) := by
      refine (HeightOneSpectrum.mem_adicCompletionIntegers
        (NumberField.RingOfIntegers K) K Q'.1).mpr ?_
      rw [Commons.NumberTheory.NumberField.Completion.valued_alg_eq]
      exact (adicExp_nonneg_iff Q'.1 x).mp hxQ'
    have hbq_int : algebraMap K (Q'.1.adicCompletion K)
        (algebraMap (NumberField.RingOfIntegers K) K b) ∈
        (Q'.1.adicCompletionIntegers K : Set (Q'.1.adicCompletion K)) := by
      refine (HeightOneSpectrum.mem_adicCompletionIntegers
        (NumberField.RingOfIntegers K) K Q'.1).mpr ?_
      rw [Commons.NumberTheory.NumberField.Completion.valued_alg_eq]
      rw [show (HeightOneSpectrum.valuation K Q'.1) ((algebraMap (NumberField.RingOfIntegers K) K) b)
        = Q'.1.intValuation b from HeightOneSpectrum.valuation_of_algebraMap Q'.1 b]
      exact HeightOneSpectrum.intValuation_le_one Q'.1 b
    have hprod : algebraMap K (Q'.1.adicCompletion K)
        (x * algebraMap (NumberField.RingOfIntegers K) K b) ∈
        (Q'.1.adicCompletionIntegers K : Set (Q'.1.adicCompletion K)) := by
      rw [map_mul]; exact mul_mem hxq_int hbq_int
    exact trace_mem_integers_of_mem Q0 Q'.1 Q'.2 _ hprod
  have hfQι : f Qι = (∑ Q' : ι, f Q') - (∑ Q' ∈ Finset.univ.erase Qι, f Q') := by
    rw [← Finset.add_sum_erase Finset.univ f (Finset.mem_univ Qι)]
    abel
  show f Qι ∈ (Q0.adicCompletionIntegers ℚ : Set (Q0.adicCompletion ℚ))
  rw [hfQι]
  exact Subring.sub_mem _ hsum_int herase_int

/-- Upgrading from the ring of integers to the local ring of integers, by density. -/
private theorem trace_mem_of_dense {K : Type*} [Field K] [NumberField K]
    (Q0 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ℚ))
    (Q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (hQ : Q.asIdeal.LiesOver Q0.asIdeal) (x : K) :
    letI : Algebra (Q0.adicCompletion ℚ) (Q.adicCompletion K) :=
      RingHom.toAlgebra (Commons.RingTheory.Henselian.adicCompletionMap Q0 Q hQ)
    (∀ b : NumberField.RingOfIntegers K,
      Algebra.trace (Q0.adicCompletion ℚ) (Q.adicCompletion K)
        (algebraMap K (Q.adicCompletion K) (x * algebraMap (NumberField.RingOfIntegers K) K b)) ∈
      (Q0.adicCompletionIntegers ℚ : Set (Q0.adicCompletion ℚ))) →
    ∀ c : Q.adicCompletionIntegers K,
      Algebra.trace (Q0.adicCompletion ℚ) (Q.adicCompletion K)
        (algebraMap K (Q.adicCompletion K) x * (c : Q.adicCompletion K)) ∈
      (Q0.adicCompletionIntegers ℚ : Set (Q0.adicCompletion ℚ)) := by
  letI : Algebra (Q0.adicCompletion ℚ) (Q.adicCompletion K) :=
    RingHom.toAlgebra (Commons.RingTheory.Henselian.adicCompletionMap Q0 Q hQ)
  intro hx c
  have hcl : IsClosed (Q0.adicCompletionIntegers ℚ : Set (Q0.adicCompletion ℚ)) :=
    Valued.isClosed_valuationSubring _
  have hcl2 : IsClosed {z : Q.adicCompletion K | Algebra.trace (Q0.adicCompletion ℚ)
      (Q.adicCompletion K) (algebraMap K (Q.adicCompletion K) x * z) ∈
      (Q0.adicCompletionIntegers ℚ : Set (Q0.adicCompletion ℚ))} :=
    hcl.preimage (trace_mul_continuous Q0 Q hQ (algebraMap K (Q.adicCompletion K) x))
  have hsub : closure (Set.range fun r : NumberField.RingOfIntegers K =>
      algebraMap K (Q.adicCompletion K) (r : K)) ⊆
      {z : Q.adicCompletion K | Algebra.trace (Q0.adicCompletion ℚ) (Q.adicCompletion K)
        (algebraMap K (Q.adicCompletion K) x * z) ∈
        (Q0.adicCompletionIntegers ℚ : Set (Q0.adicCompletion ℚ))} := by
    rw [hcl2.closure_subset_iff]
    rintro z ⟨b, rfl⟩
    simpa [map_mul] using hx b
  exact hsub (Commons.NumberTheory.NumberField.Completion.ringOfIntegers_dense_in_adicIntegers K Q c)

/-- **The completion bridge** (form without the rational prime). -/
private theorem count_le_adicLocExp_aux {K : Type*} [Field K] [NumberField K]
    (Q0 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ℚ))
    (Q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (hQ : Q.asIdeal.LiesOver Q0.asIdeal) :
    (UniqueFactorizationMonoid.normalizedFactors
      (differentIdeal ℤ (NumberField.RingOfIntegers K))).count Q.asIdeal ≤
      Work.SSGRoute.TatePoitouRoute.FinitenessHM.adicLocExp Q0 Q hQ := by
  classical
  letI : Algebra (Q0.adicCompletion ℚ) (Q.adicCompletion K) :=
    RingHom.toAlgebra (Commons.RingTheory.Henselian.adicCompletionMap Q0 Q hQ)
  set n₀ : ℕ := Work.SSGRoute.TatePoitouRoute.FinitenessHM.adicLocExp Q0 Q hQ with hn₀
  set m : ℕ := n₀ + 1 with hm
  by_contra hcount
  have hmle : m ≤ (UniqueFactorizationMonoid.normalizedFactors
      (differentIdeal ℤ (NumberField.RingOfIntegers K))).count Q.asIdeal := by omega
  have hd0 : differentIdeal ℤ (NumberField.RingOfIntegers K) ≠ ⊥ := differentIdeal_ne_bot
  have hdvd : Q.asIdeal ^ m ∣ differentIdeal ℤ (NumberField.RingOfIntegers K) :=
    dvd_trans (pow_dvd_pow Q.asIdeal hmle)
      (pow_count_dvd (I := differentIdeal ℤ (NumberField.RingOfIntegers K))
        Q.isPrime Q.ne_bot hd0)
  have hle : differentIdeal ℤ (NumberField.RingOfIntegers K) ≤ Q.asIdeal ^ m :=
    Ideal.dvd_iff_le.mp hdvd
  have hle' : ((differentIdeal ℤ (NumberField.RingOfIntegers K) : Ideal _) :
      FractionalIdeal (nonZeroDivisors (NumberField.RingOfIntegers K)) K) ≤
      (((Q.asIdeal ^ m : Ideal (NumberField.RingOfIntegers K))) :
        FractionalIdeal (nonZeroDivisors (NumberField.RingOfIntegers K)) K) :=
    (FractionalIdeal.coeIdeal_le_coeIdeal K).mpr hle
  have hQm0 : ((Q.asIdeal ^ m : Ideal (NumberField.RingOfIntegers K))) ≠ 0 :=
    pow_ne_zero m Q.ne_bot
  have hQmf0 : (((Q.asIdeal ^ m : Ideal (NumberField.RingOfIntegers K))) :
      FractionalIdeal (nonZeroDivisors (NumberField.RingOfIntegers K)) K) ≠ 0 :=
    FractionalIdeal.coeIdeal_ne_zero.mpr hQm0
  have hdf0 : ((differentIdeal ℤ (NumberField.RingOfIntegers K) : Ideal _) :
      FractionalIdeal (nonZeroDivisors (NumberField.RingOfIntegers K)) K) ≠ 0 :=
    FractionalIdeal.coeIdeal_ne_zero.mpr hd0
  have hinv : ((((Q.asIdeal ^ m : Ideal (NumberField.RingOfIntegers K))) :
      FractionalIdeal (nonZeroDivisors (NumberField.RingOfIntegers K)) K))⁻¹ ≤
      (((differentIdeal ℤ (NumberField.RingOfIntegers K) : Ideal _) :
      FractionalIdeal (nonZeroDivisors (NumberField.RingOfIntegers K)) K))⁻¹ :=
    (FractionalIdeal.inv_le_inv_iff hQmf0 hdf0).mpr hle'
  have hdual : (((differentIdeal ℤ (NumberField.RingOfIntegers K) : Ideal _) :
      FractionalIdeal (nonZeroDivisors (NumberField.RingOfIntegers K)) K))⁻¹ =
      FractionalIdeal.dual ℤ ℚ
        (1 : FractionalIdeal (nonZeroDivisors (NumberField.RingOfIntegers K)) K) := by
    rw [coeIdeal_differentIdeal ℤ ℚ K (NumberField.RingOfIntegers K), inv_inv]
  rw [hdual] at hinv
  have hcountQm : FractionalIdeal.count K Q
      (((Q.asIdeal ^ m : Ideal (NumberField.RingOfIntegers K))) :
        FractionalIdeal (nonZeroDivisors (NumberField.RingOfIntegers K)) K) = (m : ℤ) := by
    rw [FractionalIdeal.count_coe K Q hQm0,
      Ideal.count_associates_factors_eq hQm0 Q.isPrime Q.ne_bot]
    exact_mod_cast Ideal.count_normalizedFactors_eq (p := Q.asIdeal) (x := Q.asIdeal ^ m)
      (n := m) (hp := Q.isPrime) le_rfl
      (not_le_of_gt ((Ideal.pow_right_strictAnti Q.asIdeal Q.ne_bot Q.isPrime.ne_top)
        (Nat.lt_succ_self m)))
  have hcountI : FractionalIdeal.count K Q
      ((((Q.asIdeal ^ m : Ideal (NumberField.RingOfIntegers K))) :
        FractionalIdeal (nonZeroDivisors (NumberField.RingOfIntegers K)) K))⁻¹ = -((m : ℕ) : ℤ) := by
    rw [FractionalIdeal.count_inv, hcountQm]
  obtain ⟨x, hxmem, hxexp⟩ := exists_mem_adicExp_eq_fractionalIdeal_count Q
    (I := (((Q.asIdeal ^ m : Ideal (NumberField.RingOfIntegers K))) :
      FractionalIdeal (nonZeroDivisors (NumberField.RingOfIntegers K)) K)⁻¹)
    (inv_ne_zero hQmf0)
  have hxexp' : adicExp Q x = -((m : ℕ) : ℤ) := by rw [hxexp, hcountI]
  have hxdual : x ∈ FractionalIdeal.dual ℤ ℚ
      (1 : FractionalIdeal (nonZeroDivisors (NumberField.RingOfIntegers K)) K) := hinv hxmem
  have hx0 : x ≠ 0 := by
    intro h
    rw [h, adicExp_zero] at hxexp'
    omega
  have hxint : ∀ Q' : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K),
      Q'.asIdeal.LiesOver Q0.asIdeal → Q' ≠ Q → 0 ≤ adicExp Q' x :=
    fun Q' _ hne => adicExp_nonneg_of_mem_inv Q m hxmem Q' hne
  have hb_int := trace_mem_of_forall_ringOfIntegers Q0 Q hQ x hxdual hxint
  have hc_int := (trace_mem_of_dense Q0 Q hQ x) hb_int
  have hval : Valued.v (R := Q.adicCompletion K) (Γ₀ := WithZero (Multiplicative ℤ))
      (algebraMap K (Q.adicCompletion K) x) = WithZero.exp ((m : ℕ) : ℤ) := by
    rw [Commons.NumberTheory.NumberField.Completion.valued_alg_eq,
      ← exp_neg_adicExp Q hx0, hxexp', neg_neg]
  have hne_le : ¬ (Valued.v (R := Q.adicCompletion K) (Γ₀ := WithZero (Multiplicative ℤ))
      (algebraMap K (Q.adicCompletion K) x) ≤ WithZero.exp ((n₀ : ℕ) : ℤ)) := by
    rw [hval, WithZero.exp_le_exp]
    omega
  refine hne_le ?_
  exact (adicExp_le_iff_trace_mem Q0 Q hQ (algebraMap K (Q.adicCompletion K) x)).mp hc_int


/-- **The completion bridge.**  The exponent of a prime `Q | (p)` of `𝓞 K` in the global different
`𝔡_{K/ℤ}` is at most the exponent of the maximal ideal in the different of the `p`-adic
completion.  (In fact the two are equal: the different commutes with completion.) -/
theorem count_le_adicLocExp_clean {K : Type*} [Field K] [NumberField K] (p : ℕ) [Fact p.Prime]
    (Q0 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ℚ))
    (hQ0 : Q0.asIdeal = Ideal.span
      ({(p : NumberField.RingOfIntegers ℚ)} : Set (NumberField.RingOfIntegers ℚ)))
    (Q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (hQ : Q.asIdeal.LiesOver Q0.asIdeal) :
    (UniqueFactorizationMonoid.normalizedFactors
      (differentIdeal ℤ (NumberField.RingOfIntegers K))).count Q.asIdeal ≤
      Work.SSGRoute.TatePoitouRoute.FinitenessHM.adicLocExp Q0 Q hQ :=
  count_le_adicLocExp_aux Q0 Q hQ


open scoped IntermediateField

private theorem finrank_eq_of_isCyclotomicExtension_clean {K L L' : Type*} [Field K] [Field L] [Field L']
    [Algebra K L] [Algebra K L'] {m : ℕ} [NeZero m]
    [IsCyclotomicExtension {m} K L] [IsCyclotomicExtension {m} K L'] :
    Module.finrank K L = Module.finrank K L' :=
  (IsCyclotomicExtension.algEquiv {m} K L L').toLinearEquiv.finrank_eq


private theorem inertiaField_finrank_clean {K : Type*} [Field K] [NumberField K] (p : ℕ) [Fact p.Prime]
    (Q0 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ℚ))
    (hQ0 : Q0.asIdeal = Ideal.span
      ({(p : NumberField.RingOfIntegers ℚ)} : Set (NumberField.RingOfIntegers ℚ)))
    (Q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    [hQ : Q.asIdeal.LiesOver Q0.asIdeal]
    (ζ : Q.adicCompletionIntegers K)
    (hζ : IsPrimitiveRoot (ζ : Q.adicCompletion K)
      (Nat.card (IsLocalRing.ResidueField (Q.adicCompletionIntegers K)) - 1)) :
    Module.finrank (Q0.adicCompletion ℚ) ↥(inertiaField Q0 Q ζ) =
      Q.asIdeal.inertiaDeg (NumberField.RingOfIntegers ℚ) := by
  classical
  have hp : p.Prime := Fact.out
  set f := Q.asIdeal.inertiaDeg (NumberField.RingOfIntegers ℚ) with hf
  have hmem : (p : NumberField.RingOfIntegers ℚ) ∈ Q0.asIdeal := by
    rw [hQ0]; exact Ideal.mem_span_singleton_self _
  have hcard : Nat.card (IsLocalRing.ResidueField (Q.adicCompletionIntegers K)) = p ^ f := by
    simpa [hf] using
      (Commons.NumberTheory.NumberField.Completion.card_residueField_adicCompletionIntegers_eq_pow_inertiaDeg
        Q0 p hp hmem K Q hQ)
  haveI : Finite (IsLocalRing.ResidueField (Q.adicCompletionIntegers K)) :=
    Commons.NumberTheory.NumberField.Completion.finite_residueField_adicCompletion K Q
  have hcard2 : 2 ≤ p ^ f := by
    rw [← hcard]; exact Finite.one_lt_card
  have hm : 0 < p ^ f - 1 := by omega
  have hfpos : 0 < f := by
    rcases Nat.eq_zero_or_pos f with h0 | h0
    · rw [h0, pow_zero] at hcard2; omega
    · exact h0
  haveI : NeZero (p ^ f - 1) := ⟨hm.ne'⟩
  have hζm : IsPrimitiveRoot (ζ : Q.adicCompletion K) (p ^ f - 1) := by
    rw [← hcard]; exact hζ
  -- ## The upper bound `[ℚ_p(ζ) : ℚ_p] ≤ f`
  obtain ⟨M, hMf, hMA, hMfin, w, hwprim, hwfin⟩ :=
    exists_cyclotomic_completion_finrank p f hfpos Q0 hQ0
  letI : Algebra (Q0.adicCompletion ℚ) M := hMA
  haveI : Module.Finite (Q0.adicCompletion ℚ) M := hMfin
  haveI : Algebra.IsIntegral (Q0.adicCompletion ℚ) M :=
    Algebra.IsIntegral.of_finite (Q0.adicCompletion ℚ) M
  let A : IntermediateField (Q0.adicCompletion ℚ) M :=
    IntermediateField.adjoin (Q0.adicCompletion ℚ) {w}
  haveI hEcyc : IsCyclotomicExtension {p ^ f - 1} (Q0.adicCompletion ℚ)
      ↥(inertiaField Q0 Q ζ) :=
    IsPrimitiveRoot.intermediateField_adjoin_isCyclotomicExtension
      (K := Q0.adicCompletion ℚ) (n := p ^ f - 1) hζm
  haveI hAcyc : IsCyclotomicExtension {p ^ f - 1} (Q0.adicCompletion ℚ) ↥A :=
    IsPrimitiveRoot.intermediateField_adjoin_isCyclotomicExtension
      (K := Q0.adicCompletion ℚ) (n := p ^ f - 1) hwprim
  have hcmp : Module.finrank (Q0.adicCompletion ℚ) ↥(inertiaField Q0 Q ζ) =
      Module.finrank (Q0.adicCompletion ℚ) ↥A :=
    finrank_eq_of_isCyclotomicExtension_clean (K := Q0.adicCompletion ℚ)
      (L := ↥(inertiaField Q0 Q ζ)) (L' := ↥A) (m := p ^ f - 1)
  have hAle : Module.finrank (Q0.adicCompletion ℚ) ↥A ≤ Module.finrank (Q0.adicCompletion ℚ) M :=
    Submodule.finrank_le A.toSubmodule
  have hupper : Module.finrank (Q0.adicCompletion ℚ) ↥(inertiaField Q0 Q ζ) ≤ f := by
    rw [hcmp]
    exact hAle.trans_eq hwfin
  -- ## The lower bound `f ≤ [ℚ_p(ζ) : ℚ_p]`
  have hlower : f ≤ Module.finrank (Q0.adicCompletion ℚ) ↥(inertiaField Q0 Q ζ) := by
    -- the residue fields carry the canonical algebra structure of Mathlib
    haveI hlies : Ideal.LiesOver (IsLocalRing.maximalIdeal (Q.adicCompletionIntegers K))
        (IsLocalRing.maximalIdeal (Q0.adicCompletionIntegers ℚ)) :=
      Commons.NumberTheory.NumberField.Completion.liesOver_maximalIdeal_adicCompletionIntegers
        Q0 Q hQ
    haveI hloc : IsLocalHom
        (algebraMap (Q0.adicCompletionIntegers ℚ) (Q.adicCompletionIntegers K)) := inferInstance
    set Fp := IsLocalRing.ResidueField (Q0.adicCompletionIntegers ℚ) with hFp
    set kw := IsLocalRing.ResidueField (Q.adicCompletionIntegers K) with hkw
    set ζbar : kw := IsLocalRing.residue (Q.adicCompletionIntegers K) ζ with hζbar
    -- `kw` is generated over `Fp` by `ζbar`
    have hgen : Algebra.adjoin Fp ({ζbar} : Set kw) = ⊤ := by
      refine eq_top_iff.mpr fun y _ => ?_
      rcases eq_or_ne y 0 with rfl | hy
      · exact Subalgebra.zero_mem _
      · obtain ⟨j, hj⟩ := residueField_pow_generated_by_residue Q0 Q ζ hζ y hy
        rw [hj]
        exact Subalgebra.pow_mem _ (Algebra.subset_adjoin (Set.mem_singleton ζbar)) j
    -- the minimal polynomial of `ζ` over `ℤ_p`
    set g : Polynomial (Q0.adicCompletionIntegers ℚ) :=
      minpoly (Q0.adicCompletionIntegers ℚ) ζ with hg
    have hint : IsIntegral (Q0.adicCompletionIntegers ℚ) ζ :=
      IsIntegralClosure.isIntegral (Q0.adicCompletionIntegers ℚ) (Q.adicCompletion K) ζ
    have hgmonic : g.Monic := minpoly.monic hint
    have hcompat : (algebraMap Fp kw).comp
          (IsLocalRing.residue (Q0.adicCompletionIntegers ℚ)) =
        (IsLocalRing.residue (Q.adicCompletionIntegers K)).comp
          (algebraMap (Q0.adicCompletionIntegers ℚ) (Q.adicCompletionIntegers K)) :=
      RingHom.ext fun r => IsLocalRing.ResidueField.algebraMap_residue r
    have haeval : Polynomial.aeval ζbar
        (g.map (IsLocalRing.residue (Q0.adicCompletionIntegers ℚ))) = 0 := by
      have hkey := Polynomial.map_aeval_eq_aeval_map (R := Q0.adicCompletionIntegers ℚ)
        (S := Q.adicCompletionIntegers K) (T := Fp) (U := kw)
        (φ := IsLocalRing.residue (Q0.adicCompletionIntegers ℚ))
        (ψ := IsLocalRing.residue (Q.adicCompletionIntegers K)) hcompat g ζ
      rw [hg] at hkey
      rw [show (Polynomial.aeval ζ) (minpoly (Q0.adicCompletionIntegers ℚ) ζ) = 0 from
        minpoly.aeval _ _, map_zero] at hkey
      exact hkey.symm
    have hdim := finrank_le_natDegree_of_aeval_eq_zero
      (x := ζbar) (g := g.map (IsLocalRing.residue (Q0.adicCompletionIntegers ℚ)))
      (hgmonic.map _) haeval hgen
    have hdeg : (g.map (IsLocalRing.residue (Q0.adicCompletionIntegers ℚ))).natDegree =
        g.natDegree := by
      refine Polynomial.natDegree_map_of_leadingCoeff_ne_zero _ ?_
      rw [hgmonic.leadingCoeff, map_one]; exact one_ne_zero
    have hdeg2 : g.natDegree = Module.finrank (Q0.adicCompletion ℚ) ↥(inertiaField Q0 Q ζ) := by
      have hrel : minpoly (Q0.adicCompletion ℚ) (ζ : Q.adicCompletion K) =
          g.map (algebraMap (Q0.adicCompletionIntegers ℚ) (Q0.adicCompletion ℚ)) := by
        rw [hg]
        exact minpoly.isIntegrallyClosed_eq_field_fractions (Q0.adicCompletion ℚ)
          (Q.adicCompletion K) hint
      have hmap : (g.map (algebraMap (Q0.adicCompletionIntegers ℚ)
          (Q0.adicCompletion ℚ))).natDegree = g.natDegree := by
        refine Polynomial.natDegree_map_of_leadingCoeff_ne_zero _ ?_
        rw [hgmonic.leadingCoeff, map_one]; exact one_ne_zero
      have hadj : Module.finrank (Q0.adicCompletion ℚ)
            ↥(IntermediateField.adjoin (Q0.adicCompletion ℚ) {(ζ : Q.adicCompletion K)}) =
          (minpoly (Q0.adicCompletion ℚ) (ζ : Q.adicCompletion K)).natDegree :=
        IntermediateField.adjoin.finrank (liftElem_isIntegral Q0 Q ζ)
      have heq : inertiaField Q0 Q ζ =
          IntermediateField.adjoin (Q0.adicCompletion ℚ) {(ζ : Q.adicCompletion K)} := rfl
      calc g.natDegree = (g.map (algebraMap (Q0.adicCompletionIntegers ℚ)
              (Q0.adicCompletion ℚ))).natDegree := hmap.symm
        _ = (minpoly (Q0.adicCompletion ℚ) (ζ : Q.adicCompletion K)).natDegree :=
            (congrArg Polynomial.natDegree hrel).symm
        _ = Module.finrank (Q0.adicCompletion ℚ)
              ↥(IntermediateField.adjoin (Q0.adicCompletion ℚ) {(ζ : Q.adicCompletion K)}) :=
            hadj.symm
        _ = Module.finrank (Q0.adicCompletion ℚ) ↥(inertiaField Q0 Q ζ) := by rw [heq]
    have hcardFp : Nat.card Fp = p :=
      Commons.NumberTheory.NumberField.Completion.residueCard_adicCompletionIntegers_rat
        Q0 p hp hmem
    haveI : Module.Finite Fp kw := Module.Finite.of_finite
    have hnat := Module.natCard_eq_pow_finrank (K := Fp) (V := kw)
    have hfrank : Module.finrank Fp kw = f := by
      have h3 : p ^ f = p ^ Module.finrank Fp kw := by
        rw [← hcard, hnat, hcardFp]
      exact Nat.pow_right_injective hp.two_le h3.symm
    calc f = Module.finrank Fp kw := hfrank.symm
      _ ≤ (g.map (IsLocalRing.residue (Q0.adicCompletionIntegers ℚ))).natDegree := hdim
      _ = g.natDegree := hdeg
      _ = Module.finrank (Q0.adicCompletion ℚ) ↥(inertiaField Q0 Q ζ) := hdeg2
  exact (le_antisymm hupper hlower).trans hf


private theorem adicLocExpBoundByRamification_clean {K : Type*} [Field K] [NumberField K] (p : ℕ) [Fact p.Prime]
    (Q0 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ℚ))
    (hQ0 : Q0.asIdeal = Ideal.span ({(p : NumberField.RingOfIntegers ℚ)} : Set (NumberField.RingOfIntegers ℚ)))
    (Q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (hQ : Q.asIdeal.LiesOver Q0.asIdeal) :
    Work.SSGRoute.TatePoitouRoute.FinitenessHM.adicLocExp Q0 Q hQ ≤
      Q.asIdeal.ramificationIdx (NumberField.RingOfIntegers ℚ) *
        (1 + Q.asIdeal.ramificationIdx (NumberField.RingOfIntegers ℚ) *
          padicValNat p (Q.asIdeal.ramificationIdx (NumberField.RingOfIntegers ℚ))) := by
  classical
  haveI hQinst : Q.asIdeal.LiesOver Q0.asIdeal := hQ
  haveI hcharZero : CharZero (Q.adicCompletion K) :=
    Commons.NumberTheory.NumberField.charZero_adicCompletion (K := K) Q
  -- ## the Teichmüller lift of a generator of the residue field
  obtain ⟨ζ, hζ, -⟩ :=
    Commons.NumberTheory.NumberField.Completion.exists_isPrimitiveRoot_lift_adicCompletionB
      Q0 Q hQ
  -- ## the four interface facts about the inertia field
  have hfin := inertiaField_finrank_clean (K := K) p Q0 hQ0 Q ζ hζ
  have hD := differentIdeal_inertiaRing_eq_top (K := K) p Q0 hQ0 Q ζ hζ
  obtain ⟨hmax, -⟩ := inertiaRing_span_p_isMaximal (K := K) p Q0 hQ0 Q ζ hζ hfin
  have hordn := inertia_ordAt_natCast (K := K) p Q0 hQ0 Q ζ hζ hD hmax
  have hunder : Ideal.span ({(p : ↥(inertiaRing Q0 Q ζ))} : Set ↥(inertiaRing Q0 Q ζ)) =
      (IsLocalRing.maximalIdeal (Q.adicCompletionIntegers K)).comap
        (algebraMap ↥(inertiaRing Q0 Q ζ) (Q.adicCompletionIntegers K)) := by
    have hpne : ((p : ℕ) : Q.adicCompletion K) ≠ 0 :=
      Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero
    have hpmem : (p : Q.adicCompletionIntegers K) ∈
        IsLocalRing.maximalIdeal (Q.adicCompletionIntegers K) := by
      rw [← pow_one (IsLocalRing.maximalIdeal (Q.adicCompletionIntegers K)),
        mem_maximalIdeal_pow_iff_le_adicValExp Q hpne 1]
      rw [show ((p : Q.adicCompletionIntegers K) : Q.adicCompletion K) =
        ((p : ℕ) : Q.adicCompletion K) from map_natCast
          (algebraMap (Q.adicCompletionIntegers K) (Q.adicCompletion K)) p]
      rw [adicValExp_natCast (K := K) (p := p) (Q := Q) Q0 hQ0 hQ p
        (Fact.out : p.Prime).ne_zero]
      simp only [padicValNat_self, mul_one]
      exact_mod_cast (Ideal.ramificationIdx_pos (R := NumberField.RingOfIntegers ℚ) (q := Q.asIdeal))
    have hle : Ideal.span ({(p : ↥(inertiaRing Q0 Q ζ))} : Set ↥(inertiaRing Q0 Q ζ)) ≤
        (IsLocalRing.maximalIdeal (Q.adicCompletionIntegers K)).comap
          (algebraMap ↥(inertiaRing Q0 Q ζ) (Q.adicCompletionIntegers K)) := by
      rw [Ideal.span_le, Set.singleton_subset_iff]
      refine Ideal.mem_comap.mpr ?_
      rw [map_natCast]
      exact hpmem
    have hprime : ((IsLocalRing.maximalIdeal (Q.adicCompletionIntegers K)).comap
        (algebraMap ↥(inertiaRing Q0 Q ζ) (Q.adicCompletionIntegers K))).IsPrime :=
      inferInstance
    exact hmax.eq_of_le hprime.ne_top hle
  have hordc := inertia_ordAt_algebraMap (K := K) p Q0 hQ0 Q ζ hζ hfin hmax hunder
  -- ## a uniformiser
  obtain ⟨π, hπ, -⟩ :=
    Commons.NumberTheory.NumberField.Completion.exists_uniformizer_val_eq_exp_neg_one Q
  -- ## the congruence bound for the derivative of the minimal polynomial of `π` over `𝒪_E`
  obtain ⟨hdegπ, hbound⟩ := inertia_derivative_bound (K := K) p Q0 hQ0 Q ζ hζ hfin hmax hunder
    hordc hordn π hπ
  -- ## `E(π) = L`, so that Mathlib's derivative lemma applies
  have hcoee : (π : Q.adicCompletion K) =
      algebraMap (Q.adicCompletionIntegers K) (Q.adicCompletion K) π := rfl
  have hCint : IsIntegral ↥(inertiaRing Q0 Q ζ) π :=
    IsIntegralClosure.isIntegral ↥(inertiaRing Q0 Q ζ) (Q.adicCompletion K) π
  have hmin : (minpoly ↥(inertiaField Q0 Q ζ) (π : Q.adicCompletion K)).natDegree =
      (minpoly ↥(inertiaRing Q0 Q ζ) π).natDegree := by
    have hmap := minpoly.isIntegrallyClosed_eq_field_fractions ↥(inertiaField Q0 Q ζ)
      (Q.adicCompletion K) hCint
    have hinj : Function.Injective
        (algebraMap ↥(inertiaRing Q0 Q ζ) ↥(inertiaField Q0 Q ζ)) := fun a b hab => Subtype.ext hab
    rw [hcoee, hmap, Polynomial.natDegree_map_eq_of_injective hinj]
  have hfpos : 0 < Q.asIdeal.inertiaDeg (NumberField.RingOfIntegers ℚ) :=
    Ideal.inertiaDeg_pos (R := NumberField.RingOfIntegers ℚ) (q := Q.asIdeal)
  have hLE : Module.finrank ↥(inertiaField Q0 Q ζ) (Q.adicCompletion K) =
      Q.asIdeal.ramificationIdx (NumberField.RingOfIntegers ℚ) := by
    have hL := Commons.NumberTheory.NumberField.Completion.finrank_adicCompletion_eq_ramificationIdx_mul_inertiaDeg
      (K := ℚ) (L := K) Q0 Q hQ
    have hmul := Module.finrank_mul_finrank (Q0.adicCompletion ℚ) ↥(inertiaField Q0 Q ζ)
      (Q.adicCompletion K)
    rw [← hL, hfin] at hmul
    have h2 : Q.asIdeal.inertiaDeg (NumberField.RingOfIntegers ℚ) *
        Q.asIdeal.ramificationIdx (NumberField.RingOfIntegers ℚ) =
        Q.asIdeal.inertiaDeg (NumberField.RingOfIntegers ℚ) *
          Module.finrank ↥(inertiaField Q0 Q ζ) (Q.adicCompletion K) := by
      rw [mul_comm]
      exact hmul.symm
    exact (Nat.mul_left_cancel hfpos h2).symm
  have hgen : Algebra.adjoin ↥(inertiaField Q0 Q ζ)
      {algebraMap (Q.adicCompletionIntegers K) (Q.adicCompletion K) π} = ⊤ := by
    rw [← hcoee, ← IntermediateField.adjoin_eq_top_iff]
    rw [Field.primitive_element_iff_minpoly_natDegree_eq]
    rw [hmin, hdegπ]
    exact hLE.symm
  -- ## the element `f'(π) ∈ 𝔇_{𝒪_L/ℤ_p}`
  have hcompat : ∀ q : Polynomial ↥(inertiaRing Q0 Q ζ),
      algebraMap (Q.adicCompletionIntegers K) (Q.adicCompletion K) (Polynomial.aeval π q) =
        Polynomial.aeval ((algebraMap (Q.adicCompletionIntegers K) (Q.adicCompletion K)) π)
          (q.map (algebraMap ↥(inertiaRing Q0 Q ζ) ↥(inertiaField Q0 Q ζ))) := by
    intro q
    have hhom : (algebraMap (Q.adicCompletionIntegers K) (Q.adicCompletion K)).comp
        (algebraMap ↥(inertiaRing Q0 Q ζ) (Q.adicCompletionIntegers K)) =
        (algebraMap ↥(inertiaField Q0 Q ζ) (Q.adicCompletion K)).comp
          (algebraMap ↥(inertiaRing Q0 Q ζ) ↥(inertiaField Q0 Q ζ)) := by
      refine RingHom.ext fun c => ?_
      show (algebraMap (Q.adicCompletionIntegers K) (Q.adicCompletion K))
          ((algebraMap ↥(inertiaRing Q0 Q ζ) (Q.adicCompletionIntegers K)) c) =
        (algebraMap ↥(inertiaField Q0 Q ζ) (Q.adicCompletion K))
          ((algebraMap ↥(inertiaRing Q0 Q ζ) ↥(inertiaField Q0 Q ζ)) c)
      rw [← IsScalarTower.algebraMap_apply ↥(inertiaRing Q0 Q ζ) (Q.adicCompletionIntegers K)
        (Q.adicCompletion K)]
      rw [← IsScalarTower.algebraMap_apply ↥(inertiaRing Q0 Q ζ) ↥(inertiaField Q0 Q ζ)
        (Q.adicCompletion K)]
    rw [Polynomial.aeval_def, Polynomial.hom_eval₂, Polynomial.aeval_def, Polynomial.eval₂_map,
      hhom]
  have hpoly : Polynomial.derivative
      (minpoly ↥(inertiaField Q0 Q ζ) (π : Q.adicCompletion K)) =
      (Polynomial.derivative (minpoly ↥(inertiaRing Q0 Q ζ) π)).map
        (algebraMap ↥(inertiaRing Q0 Q ζ) ↥(inertiaField Q0 Q ζ)) := by
    rw [hcoee, minpoly.isIntegrallyClosed_eq_field_fractions ↥(inertiaField Q0 Q ζ)
      (Q.adicCompletion K) hCint, Polynomial.derivative_map]
  have hgmem : Polynomial.aeval π
      (Polynomial.derivative (minpoly ↥(inertiaRing Q0 Q ζ) π)) ∈
      differentIdeal (Q0.adicCompletionIntegers ℚ) (Q.adicCompletionIntegers K) := by
    have h1 : Polynomial.aeval π (Polynomial.derivative (minpoly ↥(inertiaRing Q0 Q ζ) π)) ∈
        differentIdeal ↥(inertiaRing Q0 Q ζ) (Q.adicCompletionIntegers K) :=
      aeval_derivative_mem_differentIdeal (A := ↥(inertiaRing Q0 Q ζ))
        (K := ↥(inertiaField Q0 Q ζ)) (B := Q.adicCompletionIntegers K)
        (L := Q.adicCompletion K) π hgen
    have htow := differentIdeal_eq_differentIdeal_mul_differentIdeal
      (Q0.adicCompletionIntegers ℚ) ↥(inertiaRing Q0 Q ζ) (Q.adicCompletionIntegers K)
    rw [htow, hD, Ideal.map_top, Ideal.mul_top]
    exact h1
  have hgne : Polynomial.aeval π
      (Polynomial.derivative (minpoly ↥(inertiaRing Q0 Q ζ) π)) ≠ 0 := by
    intro h0
    have hne := (Algebra.IsSeparable.isSeparable ↥(inertiaField Q0 Q ζ)
      (π : Q.adicCompletion K)).aeval_derivative_ne_zero
      (minpoly.aeval ↥(inertiaField Q0 Q ζ) (π : Q.adicCompletion K))
    rw [hpoly, hcoee] at hne
    rw [← hcompat (Polynomial.derivative (minpoly ↥(inertiaRing Q0 Q ζ) π))] at hne
    exact hne (by rw [h0, map_zero])
  -- ## the count bound
  have h1 : adicLocExp Q0 Q hQ ≤ ordAt (IsLocalRing.maximalIdeal (Q.adicCompletionIntegers K))
      (Polynomial.aeval π (Polynomial.derivative (minpoly ↥(inertiaRing Q0 Q ζ) π))) := by
    rw [adicLocExp]
    letI : Algebra (Q0.adicCompletionIntegers ℚ) (Q.adicCompletionIntegers K) :=
      RingHom.toAlgebra
        (Commons.NumberTheory.NumberField.Completion.adicCompletionMapIntegers Q0 Q hQ)
    haveI : Module.IsTorsionFree (Q0.adicCompletionIntegers ℚ) (Q.adicCompletionIntegers K) :=
      adicLocExpIsTorsionFreeIntegers Q0 Q
    have hspan : Ideal.span (singleton (Polynomial.aeval π
        (Polynomial.derivative (minpoly ↥(inertiaRing Q0 Q ζ) π)))) ≠ ⊥ := by
      simpa [Ideal.span_singleton_eq_bot] using hgne
    have hle : Ideal.span (singleton (Polynomial.aeval π
        (Polynomial.derivative (minpoly ↥(inertiaRing Q0 Q ζ) π)))) ≤
        differentIdeal (Q0.adicCompletionIntegers ℚ) (Q.adicCompletionIntegers K) :=
      Ideal.span_le.mpr (Set.singleton_subset_iff.mpr hgmem)
    have hprime : (IsLocalRing.maximalIdeal (Q.adicCompletionIntegers K)).IsPrime :=
      (IsLocalRing.maximalIdeal.isMaximal _).isPrime
    have hbot : IsLocalRing.maximalIdeal (Q.adicCompletionIntegers K) ≠ ⊥ := by
      intro h
      exact IsDiscreteValuationRing.not_isField (Q.adicCompletionIntegers K)
        ((IsLocalRing.isField_iff_maximalIdeal_eq (R := Q.adicCompletionIntegers K)).mpr h)
    have := count_normalizedFactors_le_of_le (R := Q.adicCompletionIntegers K) hprime hbot
      hspan hle
    simpa [ordAt] using this
  -- ## conclusion
  refine le_trans h1 (le_trans hbound ?_)
  exact adicLocExp_arith _ _




/-- **The exponent of a rational prime in the different of a number field.** -/
theorem differentIdeal_count_le_clean_bound {K : Type*} [Field K] [NumberField K] (p : ℕ) [Fact p.Prime]
    (P : Ideal (NumberField.RingOfIntegers K)) (hP : P.IsPrime)
    (hlies : P.LiesOver (Ideal.span ({(p : ℤ)} : Set ℤ))) :
    (UniqueFactorizationMonoid.normalizedFactors
        (differentIdeal ℤ (NumberField.RingOfIntegers K))).count P ≤
      P.ramificationIdx ℤ * (1 + P.ramificationIdx ℤ * padicValNat p (P.ramificationIdx ℤ)) := by
  classical
  have hp : p.Prime := Fact.out
  have hp0 : Ideal.span ({(p : ℤ)} : Set ℤ) ≠ ⊥ := by
    rw [Ne, Ideal.span_singleton_eq_bot]
    exact_mod_cast hp.ne_zero
  have hPbot : P ≠ ⊥ := Ideal.ne_bot_of_liesOver_of_ne_bot hp0 P
  -- the prime `(p)` of `𝓞 ℚ`
  have hQ0 : (ratPrime p hp).asIdeal =
      Ideal.span ({(p : NumberField.RingOfIntegers ℚ)} : Set (NumberField.RingOfIntegers ℚ)) :=
    ratPrime_asIdeal p hp
  -- the prime `Q` of `𝓞 K` attached to `P`
  let Q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K) :=
    spectrumOf hP hPbot
  have hQlies : Q.asIdeal.LiesOver (ratPrime p hp).asIdeal := by
    have h := liesOver_ratPrime p hp P hP hPbot hlies
    simpa [Q, spectrumOf_asIdeal] using h
  have hQasIdeal : Q.asIdeal = P := rfl
  -- the two halves and the glue
  have hbridge := count_le_adicLocExp_clean p (ratPrime p hp) hQ0 Q hQlies
  have hlocal := adicLocExpBoundByRamification_clean p (ratPrime p hp) hQ0 Q hQlies
  rw [hQasIdeal] at hlocal
  have hglue := ramificationIdx_under_ringOfIntegers_rat p hp P hP hPbot hlies
  rw [← hglue] at hlocal
  have hbridge' : (UniqueFactorizationMonoid.normalizedFactors
      (differentIdeal ℤ (NumberField.RingOfIntegers K))).count P ≤
      adicLocExp (ratPrime p hp) Q hQlies := by
    simpa [Q, spectrumOf_asIdeal] using hbridge
  exact hbridge'.trans hlocal

end

end Work.SSGRoute.TatePoitouRoute.FinitenessHM
