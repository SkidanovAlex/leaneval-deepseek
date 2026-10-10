import Mathlib.NumberTheory.NumberField.Completion.FinitePlace
import Submission.NK.LocalInputs.PowerQuotient.localFieldInputs_of_prime
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The `𝔮`-adic absolute value of the rational prime below `𝔮`

For a number field `K`, a finite prime `𝔮` of `K` and the rational prime `p` below it
(so `(p) ⊆ 𝔮`), the `𝔮`-adic absolute value of `p` is

  `|p|_𝔮 = p ^ (-[K_𝔮 : ℚ_p])`.

This is the standard normalisation of the `𝔮`-adic place: the normalised absolute value attached
to `𝔮` is `x ↦ N(𝔮) ^ (-v_𝔮 x)`, where `N(𝔮) = p ^ f` is the absolute norm of `𝔮` and
`f = inertiaDeg(𝔮/p)`, so for `x = p` one gets `N(𝔮) ^ (-e) = p ^ (-(e·f))` with `e` the
ramification index of `𝔮` over `p`.  Since `e·f = [K_𝔮 : ℚ_p] = localDegree K 𝔮`, this is the
stated identity.

The file records the computation in three steps:

* `under_eq_span_of_mem` — `(p)` is the rational prime below `𝔮`, i.e. `𝔮 ∩ ℤ = (p)`;
* `ramificationIdx_eq_multiplicity_span` — the multiplicity of `𝔮` in `(p) ⊆ 𝓞 K` is the
  ramification index of `𝔮` over `ℤ`;
* `valuation_eq_exp_neg_ramificationIdx` — the `𝔮`-adic valuation of `p ∈ K` is
  `exp (-e)`, which, together with `absNorm 𝔮 = p ^ f`, gives the statement.
-/

open scoped Classical

namespace NK.GlobalCFTdeep.SecondInequality

open IsDedekindDomain.HeightOneSpectrum

variable {K : Type} [Field K] [NumberField K]

/-- **The rational prime below `𝔮`.**  If `p` is a prime and `(p) ⊆ 𝔮` for a finite prime `𝔮` of
the number field `K`, then `(p)` is exactly the prime of `ℤ` cut out by `𝔮`. -/
theorem under_eq_span_of_mem (𝔮 : IsDedekindDomain.HeightOneSpectrum
      (NumberField.RingOfIntegers K)) {p : ℕ} (hp : p.Prime)
    (hmem : (p : NumberField.RingOfIntegers K) ∈ 𝔮.asIdeal) :
    𝔮.asIdeal.under ℤ = Ideal.span {(p : ℤ)} := by
  have hmemZ : (p : ℤ) ∈ 𝔮.asIdeal.under ℤ := by
    rw [Ideal.mem_under]
    show algebraMap ℤ (NumberField.RingOfIntegers K) (p : ℤ) ∈ 𝔮.asIdeal
    rw [map_natCast]
    exact hmem
  have hle : Ideal.span {(p : ℤ)} ≤ 𝔮.asIdeal.under ℤ :=
    Ideal.span_le.mpr (Set.singleton_subset_iff.mpr hmemZ)
  have hpr : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
  have hmax : (Ideal.span {(p : ℤ)}).IsMaximal :=
    Ideal.IsPrime.isMaximal ((Ideal.span_singleton_prime hpr.ne_zero).mpr hpr)
      (by rw [Ne, Ideal.span_singleton_eq_bot]; exact hpr.ne_zero)
  have hne : 𝔮.asIdeal.under ℤ ≠ ⊤ := (Ideal.IsPrime.under ℤ 𝔮.asIdeal).ne_top
  exact (Ideal.IsMaximal.eq_of_le hmax hne hle).symm

/-- **The multiplicity of `𝔮` in `(p)` is the ramification index of `𝔮` over `ℤ`.** -/
theorem ramificationIdx_eq_multiplicity_span (𝔮 : IsDedekindDomain.HeightOneSpectrum
      (NumberField.RingOfIntegers K)) {p : ℕ} (hp : p.Prime)
    (hmem : (p : NumberField.RingOfIntegers K) ∈ 𝔮.asIdeal) :
    𝔮.asIdeal.ramificationIdx ℤ =
      multiplicity 𝔮.asIdeal (Ideal.span {(p : NumberField.RingOfIntegers K)}) := by
  have hlies : 𝔮.asIdeal.LiesOver (Ideal.span {(p : ℤ)}) :=
    Ideal.LiesOver.mk (under_eq_span_of_mem 𝔮 hp hmem).symm
  have hmap : (Ideal.span {(p : ℤ)}).map (algebraMap ℤ (NumberField.RingOfIntegers K)) =
      Ideal.span {(p : NumberField.RingOfIntegers K)} := by
    rw [Ideal.map_span, Set.image_singleton, map_natCast]
  have hmapne : (Ideal.span {(p : ℤ)}).map (algebraMap ℤ (NumberField.RingOfIntegers K)) ≠ ⊥ := by
    rw [hmap, Ne, Ideal.span_singleton_eq_bot]
    exact_mod_cast hp.ne_zero
  have h := Ideal.IsDedekindDomain.ramificationIdx_eq_multiplicity
    (p := Ideal.span {(p : ℤ)}) (q := 𝔮.asIdeal) hmapne
  rwa [hmap] at h

/-- **The `𝔮`-adic valuation of the rational prime `p ∈ K`** is `exp (-e)`, where `e` is the
ramification index of `𝔮` over `ℤ`. -/
theorem valuation_eq_exp_neg_ramificationIdx (𝔮 : IsDedekindDomain.HeightOneSpectrum
      (NumberField.RingOfIntegers K)) {p : ℕ} (hp : p.Prime)
    (hmem : (p : NumberField.RingOfIntegers K) ∈ 𝔮.asIdeal) :
    IsDedekindDomain.HeightOneSpectrum.valuation K 𝔮 ((p : ℕ) : K) =
      WithZero.exp (-(𝔮.asIdeal.ramificationIdx ℤ : ℤ)) := by
  rw [show ((p : ℕ) : K) = algebraMap (NumberField.RingOfIntegers K) K
      ((p : ℕ) : NumberField.RingOfIntegers K) from (map_natCast _ p).symm,
    IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap]
  rw [IsDedekindDomain.HeightOneSpectrum.intValuation_eq_exp_neg_multiplicity _
      (by exact_mod_cast hp.ne_zero),
    ← ramificationIdx_eq_multiplicity_span 𝔮 hp hmem]

/-- **`N(𝔮) = p ^ f`**: the absolute norm of `𝔮` is the inertia degree `f` of `𝔮` over `ℤ`
power of the rational prime below `𝔮`. -/
theorem absNorm_eq_pow_inertiaDeg (𝔮 : IsDedekindDomain.HeightOneSpectrum
      (NumberField.RingOfIntegers K)) {p : ℕ} (hp : p.Prime)
    (hmem : (p : NumberField.RingOfIntegers K) ∈ 𝔮.asIdeal) :
    (Ideal.absNorm 𝔮.asIdeal : NNReal) = (p : NNReal) ^ (𝔮.asIdeal.inertiaDeg ℤ) := by
  have hlies : 𝔮.asIdeal.LiesOver (Ideal.span {(p : ℤ)}) :=
    Ideal.LiesOver.mk (under_eq_span_of_mem 𝔮 hp hmem).symm
  have h := Ideal.pow_inertiaDeg (R := NumberField.RingOfIntegers K) p 𝔮.asIdeal
  rw [← h]
  push_cast
  rfl

/-- `toNNReal` at the base `e` sends `exp n` to `e ^ n`. -/
theorem toNNReal_exp {e : NNReal} (he : e ≠ 0) (n : ℤ) :
    WithZeroMulInt.toNNReal he (WithZero.exp n) = e ^ n := by
  rw [WithZeroMulInt.toNNReal_neg_apply he (WithZero.exp_ne_zero)]
  congr 1

/-- **The `𝔮`-adic absolute value of the rational prime below `𝔮`.**

`|p|_𝔮 = N(𝔮) ^ (-e)`, with `N(𝔮)` the absolute norm and `e` the ramification index of `𝔮`
over `ℤ`. -/
theorem adicAbv_eq_absNorm_zpow_ramificationIdx (𝔮 : IsDedekindDomain.HeightOneSpectrum
      (NumberField.RingOfIntegers K)) {p : ℕ} (hp : p.Prime)
    (hmem : (p : NumberField.RingOfIntegers K) ∈ 𝔮.asIdeal) :
    NumberField.HeightOneSpectrum.adicAbv K 𝔮 (p : K) =
      ((Ideal.absNorm 𝔮.asIdeal : NNReal) : ℝ) ^ (-(𝔮.asIdeal.ramificationIdx ℤ : ℤ)) := by
  rw [NumberField.HeightOneSpectrum.adicAbv_def,
    valuation_eq_exp_neg_ramificationIdx 𝔮 hp hmem,
    toNNReal_exp (NumberField.HeightOneSpectrum.absNorm_ne_zero 𝔮),
    NNReal.coe_zpow]

theorem adicAbv_prime_eq_zpow_localDegree {K : Type} [Field K] [NumberField K]
    (𝔮 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)) {p : ℕ} (hp : p.Prime)
    (hmem : (p : NumberField.RingOfIntegers K) ∈ 𝔮.asIdeal) :
    NumberField.HeightOneSpectrum.adicAbv K 𝔮 (p : K) =
      (p : ℝ) ^ (-(NK.LocalInputs.localDegree K 𝔮 : ℤ)) := by
  rw [adicAbv_eq_absNorm_zpow_ramificationIdx 𝔮 hp hmem]
  have hbase : ((Ideal.absNorm 𝔮.asIdeal : NNReal) : ℝ) =
      (p : ℝ) ^ (𝔮.asIdeal.inertiaDeg ℤ : ℕ) := by
    rw [absNorm_eq_pow_inertiaDeg 𝔮 hp hmem, NNReal.coe_pow, NNReal.coe_natCast]
  have hdeg : NK.LocalInputs.localDegree K 𝔮 =
      𝔮.asIdeal.ramificationIdx ℤ * 𝔮.asIdeal.inertiaDeg ℤ :=
    NK.LocalInputs.Degree.localDegree_eq_ramificationIdx_mul_inertiaDeg 𝔮
  rw [hbase, ← zpow_natCast (p : ℝ) (𝔮.asIdeal.inertiaDeg ℤ), ← zpow_mul]
  congr 1
  rw [hdeg]
  push_cast
  ring

end NK.GlobalCFTdeep.SecondInequality
