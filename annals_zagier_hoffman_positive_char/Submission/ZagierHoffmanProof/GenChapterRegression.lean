import Submission.ZagierHoffmanProof.GenPeriodDatum
import Submission.ZagierHoffmanProof.GenEntireRegression
import Submission.ZagierHoffmanProof.GenLSeriesRegression
import Submission.ZagierHoffmanProof.MZProperty
import Submission.ZagierHoffmanProof.Specialisation
import Submission.ZagierHoffmanProof.SuperOmega

/-!
# Regression tests for the generic `ε`-chapter (depth `r`, `Ω`, MZ property, specialisation)

Over a `ℤᵐ⁰`-valued field the generic objects of this chapter are *the same* as the
`ℤᵐ⁰`-specific ones (`atLrGen = atLr`, `atLrPaperGen = atLrPaper`, `atOmegaGen = atOmega`,
`lseriesWeightGen = lseriesWeight`, `evalSeriesGen = evalSeries`), and `GammaArchimedean ℤᵐ⁰`
holds; consequently the generic theorems (`gSuperEntire_atOmegaGen`, the MZ property, the
specialisation step) instantiate back to the `ℤᵐ⁰`-specific statements of
`SuperOmega.lean`/`MZProperty.lean`/`Specialisation.lean`.
-/

set_option autoImplicit false
open Filter Polynomial RatFunc
open scoped WithZero Topology

namespace ZagierHoffmanPositiveChar

/-- The value group `ℤᵐ⁰` is archimedean: `a ^ n → 0` for every `a < 1`. -/
theorem gammaArchimedean_zm : GammaArchimedean ℤᵐ⁰ := by
  intro a ha ε hε
  obtain ⟨k, rfl⟩ := exists_exp_eq_of_ne_zero' hε
  rcases eq_or_ne a 0 with h0 | h0
  · refine ⟨1, ?_⟩
    rw [h0, pow_one]
    exact zero_lt_of_ne_zero hε
  · obtain ⟨j, rfl⟩ := exists_exp_eq_of_ne_zero' h0
    have hj : 1 ≤ -j := by
      have h1 : (1 : ℤᵐ⁰) = WithZero.exp 0 := WithZero.exp_zero.symm
      rw [h1] at ha
      have h2 := WithZero.exp_lt_exp.mp ha
      omega
    refine ⟨(-k).natAbs + 1, ?_⟩
    rw [expmul, WithZero.exp_lt_exp]
    have h1 : -k ≤ (((-k).natAbs : ℤ)) := Int.le_natAbs
    have h2 : j ≤ -1 := by omega
    have h3 : (0 : ℤ) ≤ (((-k).natAbs + 1 : ℕ) : ℤ) := by positivity
    have hjn : j * (((-k).natAbs + 1 : ℕ) : ℤ) ≤ -((((-k).natAbs + 1 : ℕ) : ℤ)) := by
      have hh := mul_le_mul_of_nonneg_right h2 h3
      simpa using hh
    have h4 : -((((-k).natAbs + 1 : ℕ) : ℤ)) ≤ (k : ℤ) - 1 := by
      have h5 : (((-k).natAbs + 1 : ℕ) : ℤ) = ((-k).natAbs : ℤ) + 1 := by push_cast; ring
      rw [h5]; linarith
    linarith

variable {K : Type*} [Field K] [Valued K ℤᵐ⁰] [CompleteSpace K] [NonarchimedeanAddGroup K]

/-- The generic cutoff `L`-series is the `ℤᵐ⁰`-specific one. -/
lemma atLrFoldGen_eq_atLrFold (q : ℕ) [FrobPow K q] (ω : PowerSeries K)
    (g : ℕ → PowerSeries K) :
    ∀ (L : List (ℕ × PowerSeries K)) (N : ℕ),
      atLrFoldGen (K := K) q ω g L N = atLrFold (K := K) q ω g L N := by
  intro L
  induction L with
  | nil => intro N; rfl
  | cons a rest ih =>
      obtain ⟨s, Q⟩ := a
      intro N
      ext n
      rw [atLrFoldGen_cons, atLrFold_cons, PowerSeries.coeff_mk, PowerSeries.coeff_mk]
      refine tsum_congr (fun i => ?_)
      rw [ih]

lemma atLrcutGen_eq_atLrcut (q : ℕ) [FrobPow K q] (ω : PowerSeries K)
    (L : List (ℕ × PowerSeries K)) (N : ℕ) :
    atLrcutGen (K := K) q ω L N = atLrcut (K := K) q ω L N :=
  atLrFoldGen_eq_atLrFold q ω (fun _ => (1 : PowerSeries K)) L N

/-- The generic `L`-series is the `ℤᵐ⁰`-specific one. -/
lemma atLrGen_eq_atLr (q : ℕ) [FrobPow K q] (ω : PowerSeries K)
    (L : List (ℕ × PowerSeries K)) :
    atLrGen (K := K) q ω L = atLr (K := K) q ω L :=
  atLrcutGen_eq_atLrcut q ω L 0

/-- The generic `L`-series in the paper's convention is the `ℤᵐ⁰`-specific one. -/
lemma atLrPaperGen_eq_atLrPaper (q : ℕ) [FrobPow K q] (ω : PowerSeries K)
    (L : List (ℕ × PowerSeries K)) :
    atLrPaperGen (K := K) q ω L = atLrPaper (K := K) q ω L :=
  atLrGen_eq_atLr q ω L.reverse

/-- The generic weight of an `L`-series tuple is the `ℤᵐ⁰`-specific one. -/
lemma lseriesWeightGen_eq_lseriesWeight (L : List (ℕ × PowerSeries K)) :
    lseriesWeightGen L = lseriesWeight L := rfl

/-- The generic period function is the `ℤᵐ⁰`-specific one. -/
lemma atOmegaGen_eq_atOmega (q : ℕ) (θ : K) [CompleteSpace K] [NonarchimedeanAddGroup K] :
    atOmegaGen (K := K) q θ = atOmega (K := K) q θ := rfl

/-- **`Ω ∈ ε` recovered from the generic theorem**: the generic sharp bound
(`gSuperEntire_atOmegaGen`) instantiates back to `superEntire_atOmega`. -/
theorem superEntire_atOmega_of_generic (q : ℕ) (θ : K) (d : ℤ) (hd : 1 ≤ d)
    (hθ : Valued.v θ = WithZero.exp d) (hq : 2 ≤ q) [CompleteSpace K]
    [NonarchimedeanAddGroup K] : SuperEntire (atOmega q θ) := by
  have hγ0 : (0 : ℤᵐ⁰) < WithZero.exp (-1) := WithZero.exp_pos
  have hγθ : (Valued.v θ)⁻¹ ≤ WithZero.exp (-1) := by
    rw [hθ, ← WithZero.exp_neg, WithZero.exp_le_exp]
    omega
  have hγ1 : (WithZero.exp (-1) : ℤᵐ⁰) < 1 := by
    rw [show (1 : ℤᵐ⁰) = WithZero.exp 0 from WithZero.exp_zero.symm, WithZero.exp_lt_exp]
    omega
  have h := gSuperEntire_atOmegaGen (K := K) (Γ₀ := ℤᵐ⁰) q θ hγ0 hγθ hγ1
    gammaArchimedean_zm hq
  rw [atOmegaGen_eq_atOmega] at h
  exact (gSuperEntire_iff_superEntire _).mp h

/-- **The period-datum vanishing recovered from the generic theorem.** -/
theorem evalSeries_atOmega_frobenius_orbit_of_generic (q : ℕ) [FrobPow K q] (θ : K) (d : ℤ)
    (hd : 1 ≤ d)
    (hθ : Valued.v θ = WithZero.exp d) (hq : 2 ≤ q) [CompleteSpace K]
    [NonarchimedeanAddGroup K] {k : ℕ} (hk : 1 ≤ k) :
    evalSeries (atOmega q θ) (θ ^ (q ^ k)) = 0 := by
  have hθ0 : θ ≠ 0 := by
    intro h; rw [h, map_zero] at hθ
    exact absurd hθ.symm (WithZero.exp_ne_zero)
  have hγ0 : (0 : ℤᵐ⁰) < WithZero.exp (-1) := WithZero.exp_pos
  have hγθ : (Valued.v θ)⁻¹ ≤ WithZero.exp (-1) := by
    rw [hθ, ← WithZero.exp_neg, WithZero.exp_le_exp]
    omega
  have hγ1 : (WithZero.exp (-1) : ℤᵐ⁰) < 1 := by
    rw [show (1 : ℤᵐ⁰) = WithZero.exp 0 from WithZero.exp_zero.symm, WithZero.exp_lt_exp]
    omega
  have h := evalSeriesGen_atOmegaGen_frobenius_orbit (K := K) q θ hθ0 hγ0 hγθ hγ1
    gammaArchimedean_zm hq hk
  rwa [atOmegaGen_eq_atOmega] at h

end ZagierHoffmanPositiveChar
