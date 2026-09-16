import Submission.ZagierHoffmanProof.GenOmega

/-!
# The Anderson–Thakur period datum over an arbitrary value group

The generic version (arbitrary value group `Γ₀`, fixed small `γ`) of `PeriodDatum.lean`: the
period datum is `Ω = C μ · Ω̃` where `Ω̃ = atOmegaGen q θ` and `μ ∈ K` is a "period constant" with
`v μ ≤ γ`.  We prove the three properties that the specialisation step of the paper needs:

* `GIsSmall γ Ω` (`gIsSmall_C_mul_atOmegaGen`),
* `GSuperEntire γ Ω` (`gSuperEntire_C_mul_atOmegaGen`),
* `Ω(θ ^ (q^k)) = 0` for `k ≥ 1` (`evalSeriesGen_C_mul_atOmegaGen_frobenius_orbit`) — the
  paper's "`Ω` has a simple zero at `t = θ^{q^k}`".

The generic Step 2 of the paper for this datum is `step2_specialisation_gen_period`.

## Main results

* `gIsSmall_C_mul_atOmegaGen`, `gSuperEntire_C_mul_atOmegaGen`.
* ★★★ `evalSeriesGen_atOmegaGen_frobenius_orbit`, `evalSeriesGen_C_mul_atOmegaGen_frobenius_orbit`.
* ★★★ `step2_specialisation_gen_period`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
open Filter Polynomial RatFunc
open scoped WithZero Topology

namespace ZagierHoffmanPositiveChar

variable {K : Type*} [Field K] {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀] [Valued K Γ₀]
variable [CompleteSpace K] [NonarchimedeanAddGroup K]

section small

variable {γ : Γ₀}

/-- The period datum `C μ · Ω̃` is small as soon as `v μ ≤ γ` and `γ < 1`. -/
lemma gIsSmall_C_mul_atOmegaGen (q : ℕ) (θ : K) {μ : K} (hγ0 : 0 < γ)
    (hγθ : (Valued.v θ)⁻¹ ≤ γ) (hγ1 : γ < 1) (harch : GammaArchimedean Γ₀) (hq : 2 ≤ q)
    (hμ : Valued.v μ ≤ γ) : GIsSmall γ (PowerSeries.C μ * atOmegaGen q θ) := by
  intro n
  rw [PowerSeries.coeff_C_mul, map_mul]
  calc Valued.v μ * Valued.v (PowerSeries.coeff n (atOmegaGen q θ))
      ≤ γ * γ ^ n := mul_le_mul' hμ (v_coeff_atOmegaGen_le q θ hγ0 hγθ hγ1 harch hq n)
    _ = γ * γ ^ n := rfl
    _ ≤ γ * 1 := mul_le_mul_right (pow_le_one₀ hγ0.le hγ1.le) γ
    _ = γ := mul_one γ

/-- The period datum `C μ · Ω̃` is super-entire. -/
lemma gSuperEntire_C_mul_atOmegaGen (q : ℕ) (θ : K) {μ : K} (hγ0 : 0 < γ)
    (hγθ : (Valued.v θ)⁻¹ ≤ γ) (hγ1 : γ < 1) (harch : GammaArchimedean Γ₀) (hq : 2 ≤ q) :
    GSuperEntire γ (PowerSeries.C μ * atOmegaGen q θ) :=
  (GSuperEntire.C γ μ).mul hγ1.le (gSuperEntire_atOmegaGen q θ hγ0 hγθ hγ1 harch hq)

end small

section vanishing

variable (q : ℕ) [FrobPow K q] (θ : K) {γ : Γ₀}

/-- **The period function vanishes at the Frobenius orbit of `θ`**: `Ω(θ^{q^k}) = 0` for `k ≥ 1`.
This is the formal version of the paper's "the function `Ω` has a simple zero at `t = θ^{q^k}`". -/
theorem evalSeriesGen_atOmegaGen_frobenius_orbit (hθ0 : θ ≠ 0) (hγ0 : 0 < γ)
    (hγθ : (Valued.v θ)⁻¹ ≤ γ) (hγ1 : γ < 1) (harch : GammaArchimedean Γ₀) (hq : 2 ≤ q)
    {k : ℕ} (hk : 1 ≤ k) :
    evalSeriesGen (atOmegaGen q θ) (θ ^ (q ^ k)) = 0 := by
  have hse : GSuperEntire γ (atOmegaGen q θ) :=
    gSuperEntire_atOmegaGen q θ hγ0 hγθ hγ1 harch hq
  have hfac : ∀ i ∈ Finset.range k, GSuperEntire γ
      (1 - PowerSeries.C (omX q θ (i + 1)) * PowerSeries.X) :=
    fun i _ => (GSuperEntire.one γ).sub
      ((GSuperEntire.C γ _).mul hγ1.le (GSuperEntire.X hγ0))
  have hpart : GSuperEntire γ (omPartial q θ k) := by
    rw [omPartial]
    exact GSuperEntire.prod hγ1.le _ _ hfac
  have htw : GSuperEntire γ (frobTwist (R := K) (p := q) k (atOmegaGen q θ)) :=
    hse.frobTwist hγ1.le k
  have hzero : evalSeriesGen (omPartial q θ k) (θ ^ (q ^ k)) = 0 := by
    rw [omPartial]
    rw [evalSeriesGen_prod hγ1 harch _ _ hfac (θ ^ (q ^ k))]
    have hmem : k - 1 ∈ Finset.range k := Finset.mem_range.mpr (by omega)
    refine Finset.prod_eq_zero hmem ?_
    rw [evalSeriesGen_one_sub_C_mul_X hγ0 hγ1 harch, omX]
    have hk1 : k - 1 + 1 = k := by omega
    rw [hk1, inv_mul_cancel₀ (pow_ne_zero _ hθ0), sub_self]
  rw [atOmegaGen_eq_omPartial_mul_frobTwist q θ hγ0 hγθ hγ1 harch hq k,
    evalSeriesGen_mul hγ1 harch hpart htw, hzero, zero_mul]

/-- **The normalised period datum `μ·Ω̃` vanishes at the Frobenius orbit of `θ`.** -/
theorem evalSeriesGen_C_mul_atOmegaGen_frobenius_orbit (hθ0 : θ ≠ 0) (hγ0 : 0 < γ)
    (hγθ : (Valued.v θ)⁻¹ ≤ γ) (hγ1 : γ < 1) (harch : GammaArchimedean Γ₀) (hq : 2 ≤ q)
    (μ : K) {k : ℕ} (hk : 1 ≤ k) :
    evalSeriesGen (PowerSeries.C μ * atOmegaGen q θ) (θ ^ (q ^ k)) = 0 := by
  rw [evalSeriesGen_C_mul,
    evalSeriesGen_atOmegaGen_frobenius_orbit q θ hθ0 hγ0 hγθ hγ1 harch hq hk, mul_zero]

end vanishing

section step2

variable (q : ℕ) [FrobPow K q] (θ : K) {γ : Γ₀}

/-- **Step 2 of the paper for the Anderson–Thakur period datum** (generic value group): the
relation between `L`-series of the dual `t`-motive, specialised at `θ^{q^j}`, becomes a relation
between the `q^j`-th powers of the values of the maximal-weight `L`-series. -/
theorem step2_specialisation_gen_period (hθ0 : θ ≠ 0) (hγ0 : 0 < γ)
    (hγθ : (Valued.v θ)⁻¹ ≤ γ) (hγ1 : γ < 1) (harch : GammaArchimedean Γ₀) (hq : 2 ≤ q)
    {μ : K} (hμ : Valued.v μ ≤ γ)
    {ι : Type*} [DecidableEq ι] (s : Finset ι) (L : ι → List (ℕ × PowerSeries K))
    (hne : ∀ k ∈ s, L k ≠ [])
    (hL : ∀ k ∈ s, ∀ x ∈ L k,
      GIsSmall γ ((PowerSeries.C μ * atOmegaGen q θ) ^ x.1 * x.2))
    (hLse : ∀ k ∈ s, ∀ x ∈ L k, GSuperEntire γ x.2)
    (hs : ∀ k ∈ s, ∀ x ∈ L k, 1 ≤ x.1)
    (P Q : ι → Polynomial K) (W : ℕ) (hW : ∀ k ∈ s, lseriesWeightGen (L k) ≤ W)
    {j : ℕ} (hj : 1 ≤ j) (hQc : ∀ k ∈ s, (Q k).eval (θ ^ (q ^ j)) ≠ 0)
    (h : ∑ k ∈ s, ((P k * ∏ l ∈ s.erase k, Q l : Polynomial K) : PowerSeries K)
          * (atLrPaperGen q (PowerSeries.C μ * atOmegaGen q θ) (L k)
              * (PowerSeries.C μ * atOmegaGen q θ) ^ (W - lseriesWeightGen (L k))) = 0) :
    ∑ k ∈ s.filter (fun k => lseriesWeightGen (L k) = W),
        ((P k).eval (θ ^ (q ^ j)) / (Q k).eval (θ ^ (q ^ j)))
          * (evalSeriesGen (atLrPaperGen q (PowerSeries.C μ * atOmegaGen q θ) (L k)) θ)
              ^ (q ^ j) = 0 :=
  step2_specialisation_gen hγ0 hγ1 harch q hq
    (gIsSmall_C_mul_atOmegaGen q θ hγ0 hγθ hγ1 harch hq hμ)
    (gSuperEntire_C_mul_atOmegaGen q θ hγ0 hγθ hγ1 harch hq)
    (fun _ hk => evalSeriesGen_C_mul_atOmegaGen_frobenius_orbit q θ hθ0 hγ0 hγθ hγ1 harch hq μ hk)
    s L hne hL hLse hs P Q W hW hj hQc h

end step2

end ZagierHoffmanPositiveChar
