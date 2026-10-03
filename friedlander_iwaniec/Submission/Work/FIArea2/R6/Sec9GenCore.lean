/-
# The §9 frequency tail with a general majorant and a general derivative constant

`Work.FIArea2.sec9_frequency_summable` / `sec9_frequency_sum_bound` are the two analytic facts
behind *FI* (9.1): the frequency series (6.9) is absolutely convergent, and its `h ≠ (0,0)` tail is
bounded by the paper's weight `H(z₁,z₂)` of (9.2).  Both were proved with Lemma 7.1 for the
**specific** majorant (support `[M/4,4M]`, `|f^{(j)}| ≤ M^{-j}`).

Round 6 needs them for the **general** majorant of `IsMajorant6`: support in `[A,B]` with
`M/64 ≤ A`, `B ≤ 64 M`, and `|F^{(j)}| ≤ Cder·M^{-j}` with `Cder ≥ 1`.  The only place the specific
majorant entered was the bound on the Fourier integral `Fint`, so both lemmas are restated here
with that bound as an *explicit hypothesis* `h71` (of the shape produced by
`Work.FIArea2.R6.lemma_7_1_gen`), with a general `Cder ≥ 1` factor and a general frequency
`γ` (so that the two statements are independent of the analytic input and can be instantiated at
`γ = gamOf z₁ z₂` afterwards).

The weight of the tail is `HaverG Pa γ z₁ z₂`, the (9.2) sum at frequency `γ`; at `γ = gamOf z₁ z₂`
it is definitionally `Work.FIArea2.Haver Pa z₁ z₂`.
-/
import Mathlib
import Submission.Work.FIArea2.sec9_frequency_sum_bound
import Submission.Work.FIArea2.sec9_error_Hweight
import Submission.Work.FIArea2.Haver_le_uniform

set_option autoImplicit false

namespace Work.FIArea2.R6

open MeasureTheory
open scoped BigOperators
open scoped Topology

noncomputable section

/-- `gnorm z > 0` for `z ≠ 0` (a local copy, to avoid the name clash between the two
`Work.FIArea2.gnorm_pos_of_ne_zero`s). -/
lemma gnorm_pos_z (z : GaussianInt) (hz : z ≠ 0) : 0 < Work.FIPlan.gnorm z := by
  rw [Work.FIPlan.gnorm, Int.natAbs_pos]
  exact fun h => hz ((Zsqrtd.norm_eq_zero (d := -1) (by intro n; nlinarith [sq_nonneg n]) z).mp h)

/-- The summand of the (9.2) weight of the tail, at a general frequency `γ`: this is literally
the summand of `Work.FIArea2.Haver`, so that `HaverG` is *definitionally* `Haver` at
`γ = gamOf z₁ z₂`, and the §9 bounds below match `Haver` syntactically. -/
def HaverTerm (Pa : Work.FITop.Params) (γ : ℝ) (z1 z2 : GaussianInt) (h : ℤ × ℤ) : ℝ :=
  if h = (0, 0) then 0 else
    (Work.FIArea2.gcdDelta z1 z2 h.1 h.2 : ℝ)
      * (1 + (Work.FIArea2.secFreq₁ z1 z2 h.1) ^ 2 * Real.sqrt (1 - γ ^ 2) * Real.sqrt Pa.M)⁻¹
      * (1 + (Work.FIArea2.secFreq₂ z1 z2 h.2) ^ 2 * Real.sqrt (1 - γ ^ 2) * Real.sqrt Pa.M)⁻¹

/-- The (9.2) weight of the tail, at a general frequency `γ` (so that the two §9 facts below are
independent of `γ = gamOf z₁ z₂`). -/
def HaverG (Pa : Work.FITop.Params) (γ : ℝ) (z1 z2 : GaussianInt) : ℝ :=
  ∑' h : ℤ × ℤ, HaverTerm Pa γ z1 z2 h

/-- At `γ = gamOf z₁ z₂` the general weight is the paper's `Haver` of (9.2). -/
lemma HaverG_gamOf (Pa : Work.FITop.Params) (z1 z2 : GaussianInt) :
    HaverG Pa (Work.FIArea2.gamOf z1 z2) z1 z2 = Work.FIArea2.Haver Pa z1 z2 := rfl

/-- The weight (9.2) is non-negative (each term is non-negative: `√x = 0` when `x < 0`, so the
`(1 + h²√(1−γ²)√M)^{−1}` factors are non-negative regardless of the sign of `1 − γ²`). -/
lemma HaverTerm_nonneg (Pa : Work.FITop.Params) (γ : ℝ) (z1 z2 : GaussianInt)
    (h : ℤ × ℤ) : 0 ≤ HaverTerm Pa γ z1 z2 h := by
  rw [HaverTerm]
  by_cases hh : h = (0, 0)
  · simp [hh]
  · rw [if_neg hh]
    have h1 : 0 ≤ Real.sqrt (1 - γ ^ 2) := Real.sqrt_nonneg _
    have h2 : 0 ≤ Real.sqrt Pa.M := Real.sqrt_nonneg _
    refine mul_nonneg (mul_nonneg (Nat.cast_nonneg _) ?_) ?_
    · refine inv_nonneg.mpr ?_
      linarith [mul_nonneg (mul_nonneg (sq_nonneg (Work.FIArea2.secFreq₁ z1 z2 h.1)) h1) h2]
    · refine inv_nonneg.mpr ?_
      linarith [mul_nonneg (mul_nonneg (sq_nonneg (Work.FIArea2.secFreq₂ z1 z2 h.2)) h1) h2]

lemma HaverG_nonneg (Pa : Work.FITop.Params) (γ : ℝ) (z1 z2 : GaussianInt) :
    0 ≤ HaverG Pa γ z1 z2 := by
  rw [HaverG]
  exact tsum_nonneg fun h => HaverTerm_nonneg Pa γ z1 z2 h

/-- **Absolute convergence of the frequency series (6.9)** for a general majorant: the `h ≠ (0,0)`
tail is dominated by `K71·Cder·(τ(Δ))³|Δ|^{-1}√M·log(2+δ^{-2})·H(z₁,z₂)`. -/
lemma sec9_frequency_summable_gen (Pa : Work.FITop.Params) (F : ℝ → ℝ) (z1 z2 : GaussianInt)
    (γ K71 Cder : ℝ) (hK71 : 0 ≤ K71) (hCder : 0 ≤ Cder) (hM : 1 ≤ Pa.M)
    (hγ0 : 0 ≤ γ) (hγ1 : γ < 1)
    (hΔ : Work.FIPlan.Delta z1 z2 ≠ 0)
    (hG : ∀ h1 h2 : ℤ, ‖Work.FIArea2.Gsum z1 z2 h1 h2‖
        ≤ 4 * (((Work.FIPlan.absDelta z1 z2).divisors.card : ℝ) ^ 3)
            * (Work.FIArea2.gcdDelta z1 z2 h1 h2 : ℝ) / ((Work.FIPlan.absDelta z1 z2 : ℕ) : ℝ))
    (h71 : ∀ u₁ u₂ : ℝ, ‖Work.FIArea2.Fint F γ u₁ u₂‖ ≤ K71 * Cder
      * (1 + u₁ ^ 2 * Real.sqrt (1 - γ ^ 2) * Real.sqrt Pa.M)⁻¹
      * (1 + u₂ ^ 2 * Real.sqrt (1 - γ ^ 2) * Real.sqrt Pa.M)⁻¹
      * Real.sqrt Pa.M * Real.log (2 + 1 / (1 - γ ^ 2))) :
    Summable (fun h : ℤ × ℤ => Work.FIArea2.Fint F γ
        (-(Work.FIArea2.secFreq₁ z1 z2 h.1)) (-(Work.FIArea2.secFreq₂ z1 z2 h.2))
        * Work.FIArea2.Gsum z1 z2 h.1 h.2) := by
  have h1γ : 0 < 1 - γ ^ 2 := by nlinarith [sq_nonneg γ]
  have hδpos : 0 < Real.sqrt (1 - γ ^ 2) := Real.sqrt_pos.mpr h1γ
  have hSpos : 0 < Real.sqrt Pa.M := Real.sqrt_pos.mpr (lt_of_lt_of_le one_pos hM)
  have hApos : 0 < ((Work.FIPlan.absDelta z1 z2 : ℕ) : ℝ) := by
    exact_mod_cast Work.FIArea2.absDelta_pos z1 z2 hΔ
  have hz1 : z1 ≠ 0 := fun h => hΔ (Work.FIArea2.delta_eq_zero_of_fst_eq_zero z1 z2 h)
  have hz2 : z2 ≠ 0 := fun h => hΔ (Work.FIArea2.delta_eq_zero_of_snd_eq_zero z1 z2 h)
  have hg1pos : (0 : ℝ) < ((Work.FIPlan.gnorm z1 : ℕ) : ℝ) := by
    exact_mod_cast gnorm_pos_z z1 hz1
  have hg2pos : (0 : ℝ) < ((Work.FIPlan.gnorm z2 : ℕ) : ℝ) := by
    exact_mod_cast gnorm_pos_z z2 hz2
  have hlogpos : 0 < Real.log (2 + 1 / (1 - γ ^ 2)) := by
    apply Real.log_pos
    have h1 : 0 < 1 / (1 - γ ^ 2) := by positivity
    linarith
  have hwnn1 : ∀ t : ℤ, 0 ≤ (1 + Work.FIArea2.secFreq₁ z1 z2 t ^ 2 * Real.sqrt (1 - γ ^ 2)
      * Real.sqrt Pa.M)⁻¹ := by
    intro t
    exact inv_nonneg.mpr (by
      have h1 : 0 ≤ Work.FIArea2.secFreq₁ z1 z2 t ^ 2 * Real.sqrt (1 - γ ^ 2) * Real.sqrt Pa.M :=
        mul_nonneg (mul_nonneg (sq_nonneg _) hδpos.le) hSpos.le
      linarith)
  have hwnn2 : ∀ t : ℤ, 0 ≤ (1 + Work.FIArea2.secFreq₂ z1 z2 t ^ 2 * Real.sqrt (1 - γ ^ 2)
      * Real.sqrt Pa.M)⁻¹ := by
    intro t
    exact inv_nonneg.mpr (by
      have h1 : 0 ≤ Work.FIArea2.secFreq₂ z1 z2 t ^ 2 * Real.sqrt (1 - γ ^ 2) * Real.sqrt Pa.M :=
        mul_nonneg (mul_nonneg (sq_nonneg _) hδpos.le) hSpos.le
      linarith)
  have hsum1 : Summable (fun t : ℤ =>
      (1 + Work.FIArea2.secFreq₁ z1 z2 t ^ 2 * Real.sqrt (1 - γ ^ 2) * Real.sqrt Pa.M)⁻¹) := by
    have hc : 0 < Real.sqrt (1 - γ ^ 2) * Real.sqrt Pa.M
        / (((Work.FIPlan.absDelta z1 z2 : ℕ) : ℝ)
            * Real.sqrt (((Work.FIPlan.gnorm z2 : ℕ) : ℝ))) :=
      div_pos (mul_pos hδpos hSpos) (mul_pos hApos (Real.sqrt_pos.mpr hg2pos))
    refine (Work.FIArea2.summable_inv_one_add_mul_sq _ hc).congr (fun t => ?_)
    exact (Work.FIArea2.secFreq₁_weight_eq z1 z2 t _ _ hApos hg2pos).symm
  have hsum2 : Summable (fun t : ℤ =>
      (1 + Work.FIArea2.secFreq₂ z1 z2 t ^ 2 * Real.sqrt (1 - γ ^ 2) * Real.sqrt Pa.M)⁻¹) := by
    have hc : 0 < Real.sqrt (1 - γ ^ 2) * Real.sqrt Pa.M
        / (((Work.FIPlan.absDelta z1 z2 : ℕ) : ℝ)
            * Real.sqrt (((Work.FIPlan.gnorm z1 : ℕ) : ℝ))) :=
      div_pos (mul_pos hδpos hSpos) (mul_pos hApos (Real.sqrt_pos.mpr hg1pos))
    refine (Work.FIArea2.summable_inv_one_add_mul_sq _ hc).congr (fun t => ?_)
    exact (Work.FIArea2.secFreq₂_weight_eq z1 z2 t _ _ hApos hg1pos).symm
  have hsumprod : Summable (fun p : ℤ × ℤ =>
      (1 + Work.FIArea2.secFreq₁ z1 z2 p.1 ^ 2 * Real.sqrt (1 - γ ^ 2) * Real.sqrt Pa.M)⁻¹
        * (1 + Work.FIArea2.secFreq₂ z1 z2 p.2 ^ 2 * Real.sqrt (1 - γ ^ 2) * Real.sqrt Pa.M)⁻¹) := by
    refine Summable.mul_of_nonneg hsum1 hsum2 ?_ ?_
    · intro t; exact hwnn1 t
    · intro t; exact hwnn2 t
  have hg : Summable (fun p : ℤ × ℤ => (Work.FIArea2.gcdDelta z1 z2 p.1 p.2 : ℝ)
      * (1 + Work.FIArea2.secFreq₁ z1 z2 p.1 ^ 2 * Real.sqrt (1 - γ ^ 2) * Real.sqrt Pa.M)⁻¹
      * (1 + Work.FIArea2.secFreq₂ z1 z2 p.2 ^ 2 * Real.sqrt (1 - γ ^ 2) * Real.sqrt Pa.M)⁻¹) := by
    have hsumMaj : Summable (fun p : ℤ × ℤ => ((Work.FIPlan.absDelta z1 z2 : ℕ) : ℝ) *
        ((1 + Work.FIArea2.secFreq₁ z1 z2 p.1 ^ 2 * Real.sqrt (1 - γ ^ 2) * Real.sqrt Pa.M)⁻¹
          * (1 + Work.FIArea2.secFreq₂ z1 z2 p.2 ^ 2 * Real.sqrt (1 - γ ^ 2) * Real.sqrt Pa.M)⁻¹)) :=
      hsumprod.mul_left _
    refine Summable.of_nonneg_of_le (f := fun p : ℤ × ℤ => ((Work.FIPlan.absDelta z1 z2 : ℕ) : ℝ) *
        ((1 + Work.FIArea2.secFreq₁ z1 z2 p.1 ^ 2 * Real.sqrt (1 - γ ^ 2) * Real.sqrt Pa.M)⁻¹
          * (1 + Work.FIArea2.secFreq₂ z1 z2 p.2 ^ 2 * Real.sqrt (1 - γ ^ 2) * Real.sqrt Pa.M)⁻¹)) ?_ ?_ hsumMaj
    · intro p
      exact mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (hwnn1 p.1)) (hwnn2 p.2)
    · intro p
      calc (Work.FIArea2.gcdDelta z1 z2 p.1 p.2 : ℝ)
            * (1 + Work.FIArea2.secFreq₁ z1 z2 p.1 ^ 2 * Real.sqrt (1 - γ ^ 2) * Real.sqrt Pa.M)⁻¹
            * (1 + Work.FIArea2.secFreq₂ z1 z2 p.2 ^ 2 * Real.sqrt (1 - γ ^ 2) * Real.sqrt Pa.M)⁻¹
          = (Work.FIArea2.gcdDelta z1 z2 p.1 p.2 : ℝ) *
              ((1 + Work.FIArea2.secFreq₁ z1 z2 p.1 ^ 2 * Real.sqrt (1 - γ ^ 2) * Real.sqrt Pa.M)⁻¹
              * (1 + Work.FIArea2.secFreq₂ z1 z2 p.2 ^ 2 * Real.sqrt (1 - γ ^ 2) * Real.sqrt Pa.M)⁻¹) := by ring
        _ ≤ ((Work.FIPlan.absDelta z1 z2 : ℕ) : ℝ) *
              ((1 + Work.FIArea2.secFreq₁ z1 z2 p.1 ^ 2 * Real.sqrt (1 - γ ^ 2) * Real.sqrt Pa.M)⁻¹
              * (1 + Work.FIArea2.secFreq₂ z1 z2 p.2 ^ 2 * Real.sqrt (1 - γ ^ 2) * Real.sqrt Pa.M)⁻¹) :=
            mul_le_mul_of_nonneg_right (Work.FIArea2.gcdDelta_cast_le_absDelta z1 z2 hΔ p.1 p.2)
              (mul_nonneg (hwnn1 p.1) (hwnn2 p.2))
  refine Summable.of_norm_bounded (g := fun p : ℤ × ℤ =>
      (4 * (((Work.FIPlan.absDelta z1 z2).divisors.card : ℝ) ^ 3) * (K71 * Cder) * Real.sqrt Pa.M
          * Real.log (2 + 1 / (1 - γ ^ 2)) / ((Work.FIPlan.absDelta z1 z2 : ℕ) : ℝ))
        * ((Work.FIArea2.gcdDelta z1 z2 p.1 p.2 : ℝ)
          * (1 + Work.FIArea2.secFreq₁ z1 z2 p.1 ^ 2 * Real.sqrt (1 - γ ^ 2) * Real.sqrt Pa.M)⁻¹
          * (1 + Work.FIArea2.secFreq₂ z1 z2 p.2 ^ 2 * Real.sqrt (1 - γ ^ 2) * Real.sqrt Pa.M)⁻¹)) ?_ ?_
  · exact hg.mul_left _
  · intro p
    have hsq1 : (-(Work.FIArea2.secFreq₁ z1 z2 p.1)) ^ 2 = (Work.FIArea2.secFreq₁ z1 z2 p.1) ^ 2 := by ring
    have hsq2 : (-(Work.FIArea2.secFreq₂ z1 z2 p.2)) ^ 2 = (Work.FIArea2.secFreq₂ z1 z2 p.2) ^ 2 := by ring
    have hf := h71 (-(Work.FIArea2.secFreq₁ z1 z2 p.1)) (-(Work.FIArea2.secFreq₂ z1 z2 p.2))
    rw [hsq1, hsq2] at hf
    have hgg := hG p.1 p.2
    have hbpos : 0 ≤ K71 * Cder
        * (1 + Work.FIArea2.secFreq₁ z1 z2 p.1 ^ 2 * Real.sqrt (1 - γ ^ 2) * Real.sqrt Pa.M)⁻¹
        * (1 + Work.FIArea2.secFreq₂ z1 z2 p.2 ^ 2 * Real.sqrt (1 - γ ^ 2) * Real.sqrt Pa.M)⁻¹
        * Real.sqrt Pa.M * Real.log (2 + 1 / (1 - γ ^ 2)) :=
      mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hK71 hCder) (hwnn1 p.1))
        (hwnn2 p.2)) hSpos.le) hlogpos.le
    rw [norm_mul]
    calc ‖Work.FIArea2.Fint F γ (-(Work.FIArea2.secFreq₁ z1 z2 p.1)) (-(Work.FIArea2.secFreq₂ z1 z2 p.2))‖
              * ‖Work.FIArea2.Gsum z1 z2 p.1 p.2‖
        ≤ (K71 * Cder
              * (1 + Work.FIArea2.secFreq₁ z1 z2 p.1 ^ 2 * Real.sqrt (1 - γ ^ 2) * Real.sqrt Pa.M)⁻¹
              * (1 + Work.FIArea2.secFreq₂ z1 z2 p.2 ^ 2 * Real.sqrt (1 - γ ^ 2) * Real.sqrt Pa.M)⁻¹
              * Real.sqrt Pa.M * Real.log (2 + 1 / (1 - γ ^ 2)))
            * (4 * (((Work.FIPlan.absDelta z1 z2).divisors.card : ℝ) ^ 3)
                * (Work.FIArea2.gcdDelta z1 z2 p.1 p.2 : ℝ) / ((Work.FIPlan.absDelta z1 z2 : ℕ) : ℝ)) :=
          mul_le_mul hf hgg (norm_nonneg _) hbpos
      _ = (4 * (((Work.FIPlan.absDelta z1 z2).divisors.card : ℝ) ^ 3) * (K71 * Cder)
              * Real.sqrt Pa.M * Real.log (2 + 1 / (1 - γ ^ 2))
              / ((Work.FIPlan.absDelta z1 z2 : ℕ) : ℝ))
            * ((Work.FIArea2.gcdDelta z1 z2 p.1 p.2 : ℝ)
              * (1 + Work.FIArea2.secFreq₁ z1 z2 p.1 ^ 2 * Real.sqrt (1 - γ ^ 2) * Real.sqrt Pa.M)⁻¹
              * (1 + Work.FIArea2.secFreq₂ z1 z2 p.2 ^ 2 * Real.sqrt (1 - γ ^ 2) * Real.sqrt Pa.M)⁻¹) := by
          ring

/-- **(9.1)'s analytic core, general majorant**: the `h ≠ (0,0)` tail of the Poisson series (6.9)
is bounded by the (9.2) weight `HaverG Pa γ z₁ z₂`, with the frequency bound `h71` in place of
Lemma 7.1 and a general derivative constant `Cder`. -/
theorem sec9_frequency_sum_bound_gen (Pa : Work.FITop.Params) (F : ℝ → ℝ) (z1 z2 : GaussianInt)
    (γ K71 Cder : ℝ) (hK71 : 0 ≤ K71) (hCder : 0 ≤ Cder) (hM : 1 ≤ Pa.M)
    (hγ0 : 0 ≤ γ) (hγ1 : γ < 1)
    (hΔ : Work.FIPlan.Delta z1 z2 ≠ 0)
    (hG : ∀ h1 h2 : ℤ, ‖Work.FIArea2.Gsum z1 z2 h1 h2‖
        ≤ 4 * (((Work.FIPlan.absDelta z1 z2).divisors.card : ℝ) ^ 3)
            * (Work.FIArea2.gcdDelta z1 z2 h1 h2 : ℝ) / ((Work.FIPlan.absDelta z1 z2 : ℕ) : ℝ))
    (h71 : ∀ u₁ u₂ : ℝ, ‖Work.FIArea2.Fint F γ u₁ u₂‖ ≤ K71 * Cder
      * (1 + u₁ ^ 2 * Real.sqrt (1 - γ ^ 2) * Real.sqrt Pa.M)⁻¹
      * (1 + u₂ ^ 2 * Real.sqrt (1 - γ ^ 2) * Real.sqrt Pa.M)⁻¹
      * Real.sqrt Pa.M * Real.log (2 + 1 / (1 - γ ^ 2))) :
    ‖∑' h : ℤ × ℤ, (if h = (0, 0) then 0 else
        Work.FIArea2.Fint F γ (-(Work.FIArea2.secFreq₁ z1 z2 h.1))
          (-(Work.FIArea2.secFreq₂ z1 z2 h.2))
        * Work.FIArea2.Gsum z1 z2 h.1 h.2)‖
      ≤ K71 * Cder * 4 * (((Work.FIPlan.absDelta z1 z2).divisors.card : ℝ) ^ 3)
          / ((Work.FIPlan.absDelta z1 z2 : ℕ) : ℝ) * Real.sqrt Pa.M
          * Real.log (2 + 1 / (1 - γ ^ 2))
          * HaverG Pa γ z1 z2 := by
  have h1γ : 0 < 1 - γ ^ 2 := by nlinarith [sq_nonneg γ]
  have hδpos : 0 < Real.sqrt (1 - γ ^ 2) := Real.sqrt_pos.mpr h1γ
  have hSpos : 0 < Real.sqrt Pa.M := Real.sqrt_pos.mpr (lt_of_lt_of_le one_pos hM)
  have hApos : 0 < ((Work.FIPlan.absDelta z1 z2 : ℕ) : ℝ) := by
    exact_mod_cast Work.FIArea2.absDelta_pos z1 z2 hΔ
  have hz1 : z1 ≠ 0 := fun h => hΔ (Work.FIArea2.delta_eq_zero_of_fst_eq_zero z1 z2 h)
  have hz2 : z2 ≠ 0 := fun h => hΔ (Work.FIArea2.delta_eq_zero_of_snd_eq_zero z1 z2 h)
  have hg1pos : (0 : ℝ) < ((Work.FIPlan.gnorm z1 : ℕ) : ℝ) := by
    exact_mod_cast gnorm_pos_z z1 hz1
  have hg2pos : (0 : ℝ) < ((Work.FIPlan.gnorm z2 : ℕ) : ℝ) := by
    exact_mod_cast gnorm_pos_z z2 hz2
  have hlogpos : 0 < Real.log (2 + 1 / (1 - γ ^ 2)) := by
    apply Real.log_pos
    have h1 : 0 < 1 / (1 - γ ^ 2) := by positivity
    linarith
  have hwnn1 : ∀ t : ℤ, 0 ≤ (1 + Work.FIArea2.secFreq₁ z1 z2 t ^ 2 * Real.sqrt (1 - γ ^ 2)
      * Real.sqrt Pa.M)⁻¹ := by
    intro t
    exact inv_nonneg.mpr (by
      have h1 : 0 ≤ Work.FIArea2.secFreq₁ z1 z2 t ^ 2 * Real.sqrt (1 - γ ^ 2) * Real.sqrt Pa.M :=
        mul_nonneg (mul_nonneg (sq_nonneg _) hδpos.le) hSpos.le
      linarith)
  have hwnn2 : ∀ t : ℤ, 0 ≤ (1 + Work.FIArea2.secFreq₂ z1 z2 t ^ 2 * Real.sqrt (1 - γ ^ 2)
      * Real.sqrt Pa.M)⁻¹ := by
    intro t
    exact inv_nonneg.mpr (by
      have h1 : 0 ≤ Work.FIArea2.secFreq₂ z1 z2 t ^ 2 * Real.sqrt (1 - γ ^ 2) * Real.sqrt Pa.M :=
        mul_nonneg (mul_nonneg (sq_nonneg _) hδpos.le) hSpos.le
      linarith)
  have hsum1 : Summable (fun t : ℤ =>
      (1 + Work.FIArea2.secFreq₁ z1 z2 t ^ 2 * Real.sqrt (1 - γ ^ 2) * Real.sqrt Pa.M)⁻¹) := by
    have hc : 0 < Real.sqrt (1 - γ ^ 2) * Real.sqrt Pa.M
        / (((Work.FIPlan.absDelta z1 z2 : ℕ) : ℝ)
            * Real.sqrt (((Work.FIPlan.gnorm z2 : ℕ) : ℝ))) :=
      div_pos (mul_pos hδpos hSpos) (mul_pos hApos (Real.sqrt_pos.mpr hg2pos))
    refine (Work.FIArea2.summable_inv_one_add_mul_sq _ hc).congr (fun t => ?_)
    exact (Work.FIArea2.secFreq₁_weight_eq z1 z2 t _ _ hApos hg2pos).symm
  have hsum2 : Summable (fun t : ℤ =>
      (1 + Work.FIArea2.secFreq₂ z1 z2 t ^ 2 * Real.sqrt (1 - γ ^ 2) * Real.sqrt Pa.M)⁻¹) := by
    have hc : 0 < Real.sqrt (1 - γ ^ 2) * Real.sqrt Pa.M
        / (((Work.FIPlan.absDelta z1 z2 : ℕ) : ℝ)
            * Real.sqrt (((Work.FIPlan.gnorm z1 : ℕ) : ℝ))) :=
      div_pos (mul_pos hδpos hSpos) (mul_pos hApos (Real.sqrt_pos.mpr hg1pos))
    refine (Work.FIArea2.summable_inv_one_add_mul_sq _ hc).congr (fun t => ?_)
    exact (Work.FIArea2.secFreq₂_weight_eq z1 z2 t _ _ hApos hg1pos).symm
  have hsumprod : Summable (fun p : ℤ × ℤ =>
      (1 + Work.FIArea2.secFreq₁ z1 z2 p.1 ^ 2 * Real.sqrt (1 - γ ^ 2) * Real.sqrt Pa.M)⁻¹
        * (1 + Work.FIArea2.secFreq₂ z1 z2 p.2 ^ 2 * Real.sqrt (1 - γ ^ 2) * Real.sqrt Pa.M)⁻¹) := by
    refine Summable.mul_of_nonneg hsum1 hsum2 ?_ ?_
    · intro t; exact hwnn1 t
    · intro t; exact hwnn2 t
  have hg : Summable (fun p : ℤ × ℤ => (if p = (0, 0) then 0 else
      (Work.FIArea2.gcdDelta z1 z2 p.1 p.2 : ℝ)
        * (1 + Work.FIArea2.secFreq₁ z1 z2 p.1 ^ 2 * Real.sqrt (1 - γ ^ 2) * Real.sqrt Pa.M)⁻¹
        * (1 + Work.FIArea2.secFreq₂ z1 z2 p.2 ^ 2 * Real.sqrt (1 - γ ^ 2) * Real.sqrt Pa.M)⁻¹)) := by
    have hsumMaj : Summable (fun p : ℤ × ℤ => ((Work.FIPlan.absDelta z1 z2 : ℕ) : ℝ) *
        ((1 + Work.FIArea2.secFreq₁ z1 z2 p.1 ^ 2 * Real.sqrt (1 - γ ^ 2) * Real.sqrt Pa.M)⁻¹
          * (1 + Work.FIArea2.secFreq₂ z1 z2 p.2 ^ 2 * Real.sqrt (1 - γ ^ 2) * Real.sqrt Pa.M)⁻¹)) :=
      hsumprod.mul_left _
    refine Summable.of_nonneg_of_le (f := fun p : ℤ × ℤ => ((Work.FIPlan.absDelta z1 z2 : ℕ) : ℝ) *
        ((1 + Work.FIArea2.secFreq₁ z1 z2 p.1 ^ 2 * Real.sqrt (1 - γ ^ 2) * Real.sqrt Pa.M)⁻¹
          * (1 + Work.FIArea2.secFreq₂ z1 z2 p.2 ^ 2 * Real.sqrt (1 - γ ^ 2) * Real.sqrt Pa.M)⁻¹)) ?_ ?_ hsumMaj
    · intro p
      by_cases hp : p = (0, 0)
      · simp [hp]
      · rw [if_neg hp]
        exact mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (hwnn1 p.1)) (hwnn2 p.2)
    · intro p
      by_cases hp : p = (0, 0)
      · rw [if_pos hp]
        exact mul_nonneg (Nat.cast_nonneg _) (mul_nonneg (hwnn1 p.1) (hwnn2 p.2))
      · rw [if_neg hp]
        calc (Work.FIArea2.gcdDelta z1 z2 p.1 p.2 : ℝ)
              * (1 + Work.FIArea2.secFreq₁ z1 z2 p.1 ^ 2 * Real.sqrt (1 - γ ^ 2) * Real.sqrt Pa.M)⁻¹
              * (1 + Work.FIArea2.secFreq₂ z1 z2 p.2 ^ 2 * Real.sqrt (1 - γ ^ 2) * Real.sqrt Pa.M)⁻¹
            = (Work.FIArea2.gcdDelta z1 z2 p.1 p.2 : ℝ)
              * ((1 + Work.FIArea2.secFreq₁ z1 z2 p.1 ^ 2 * Real.sqrt (1 - γ ^ 2) * Real.sqrt Pa.M)⁻¹
              * (1 + Work.FIArea2.secFreq₂ z1 z2 p.2 ^ 2 * Real.sqrt (1 - γ ^ 2) * Real.sqrt Pa.M)⁻¹) := by ring
          _ ≤ ((Work.FIPlan.absDelta z1 z2 : ℕ) : ℝ)
              * ((1 + Work.FIArea2.secFreq₁ z1 z2 p.1 ^ 2 * Real.sqrt (1 - γ ^ 2) * Real.sqrt Pa.M)⁻¹
              * (1 + Work.FIArea2.secFreq₂ z1 z2 p.2 ^ 2 * Real.sqrt (1 - γ ^ 2) * Real.sqrt Pa.M)⁻¹) :=
              mul_le_mul_of_nonneg_right (Work.FIArea2.gcdDelta_cast_le_absDelta z1 z2 hΔ p.1 p.2)
                (mul_nonneg (hwnn1 p.1) (hwnn2 p.2))
  have hT : ∀ p : ℤ × ℤ, ‖(if p = (0, 0) then 0 else
      Work.FIArea2.Fint F γ (-(Work.FIArea2.secFreq₁ z1 z2 p.1)) (-(Work.FIArea2.secFreq₂ z1 z2 p.2))
        * Work.FIArea2.Gsum z1 z2 p.1 p.2)‖
      ≤ (4 * (K71 * Cder) * (((Work.FIPlan.absDelta z1 z2).divisors.card : ℝ) ^ 3)
          / ((Work.FIPlan.absDelta z1 z2 : ℕ) : ℝ) * Real.sqrt Pa.M
          * Real.log (2 + 1 / (1 - γ ^ 2)))
        * (if p = (0, 0) then 0 else
            (Work.FIArea2.gcdDelta z1 z2 p.1 p.2 : ℝ)
              * (1 + Work.FIArea2.secFreq₁ z1 z2 p.1 ^ 2 * Real.sqrt (1 - γ ^ 2) * Real.sqrt Pa.M)⁻¹
              * (1 + Work.FIArea2.secFreq₂ z1 z2 p.2 ^ 2 * Real.sqrt (1 - γ ^ 2) * Real.sqrt Pa.M)⁻¹) := by
    intro p
    by_cases hp : p = (0, 0)
    · simp [hp]
    · rw [if_neg hp, if_neg hp]
      have hsq1 : (-(Work.FIArea2.secFreq₁ z1 z2 p.1)) ^ 2 = (Work.FIArea2.secFreq₁ z1 z2 p.1) ^ 2 := by ring
      have hsq2 : (-(Work.FIArea2.secFreq₂ z1 z2 p.2)) ^ 2 = (Work.FIArea2.secFreq₂ z1 z2 p.2) ^ 2 := by ring
      have hf := h71 (-(Work.FIArea2.secFreq₁ z1 z2 p.1)) (-(Work.FIArea2.secFreq₂ z1 z2 p.2))
      rw [hsq1, hsq2] at hf
      have hgg := hG p.1 p.2
      have hbpos : 0 ≤ K71 * Cder
          * (1 + Work.FIArea2.secFreq₁ z1 z2 p.1 ^ 2 * Real.sqrt (1 - γ ^ 2) * Real.sqrt Pa.M)⁻¹
          * (1 + Work.FIArea2.secFreq₂ z1 z2 p.2 ^ 2 * Real.sqrt (1 - γ ^ 2) * Real.sqrt Pa.M)⁻¹
          * Real.sqrt Pa.M * Real.log (2 + 1 / (1 - γ ^ 2)) :=
        mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hK71 hCder) (hwnn1 p.1))
          (hwnn2 p.2)) hSpos.le) hlogpos.le
      calc ‖Work.FIArea2.Fint F γ (-(Work.FIArea2.secFreq₁ z1 z2 p.1))
              (-(Work.FIArea2.secFreq₂ z1 z2 p.2)) * Work.FIArea2.Gsum z1 z2 p.1 p.2‖
          = ‖Work.FIArea2.Fint F γ (-(Work.FIArea2.secFreq₁ z1 z2 p.1))
              (-(Work.FIArea2.secFreq₂ z1 z2 p.2))‖ * ‖Work.FIArea2.Gsum z1 z2 p.1 p.2‖ := norm_mul _ _
        _ ≤ (K71 * Cder
              * (1 + Work.FIArea2.secFreq₁ z1 z2 p.1 ^ 2 * Real.sqrt (1 - γ ^ 2) * Real.sqrt Pa.M)⁻¹
              * (1 + Work.FIArea2.secFreq₂ z1 z2 p.2 ^ 2 * Real.sqrt (1 - γ ^ 2) * Real.sqrt Pa.M)⁻¹
              * Real.sqrt Pa.M * Real.log (2 + 1 / (1 - γ ^ 2)))
            * (4 * (((Work.FIPlan.absDelta z1 z2).divisors.card : ℝ) ^ 3)
                * (Work.FIArea2.gcdDelta z1 z2 p.1 p.2 : ℝ) / ((Work.FIPlan.absDelta z1 z2 : ℕ) : ℝ)) :=
            mul_le_mul hf hgg (norm_nonneg _) hbpos
        _ = (4 * (K71 * Cder) * (((Work.FIPlan.absDelta z1 z2).divisors.card : ℝ) ^ 3)
              / ((Work.FIPlan.absDelta z1 z2 : ℕ) : ℝ) * Real.sqrt Pa.M
              * Real.log (2 + 1 / (1 - γ ^ 2)))
            * ((Work.FIArea2.gcdDelta z1 z2 p.1 p.2 : ℝ)
              * (1 + Work.FIArea2.secFreq₁ z1 z2 p.1 ^ 2 * Real.sqrt (1 - γ ^ 2) * Real.sqrt Pa.M)⁻¹
              * (1 + Work.FIArea2.secFreq₂ z1 z2 p.2 ^ 2 * Real.sqrt (1 - γ ^ 2) * Real.sqrt Pa.M)⁻¹) := by
            ring
  have hmain := Work.FIArea2.norm_tsum_pair_le (4 * (K71 * Cder)
      * (((Work.FIPlan.absDelta z1 z2).divisors.card : ℝ) ^ 3)
      / ((Work.FIPlan.absDelta z1 z2 : ℕ) : ℝ) * Real.sqrt Pa.M
      * Real.log (2 + 1 / (1 - γ ^ 2)))
      (fun p : ℤ × ℤ => (if p = (0, 0) then 0 else
        (Work.FIArea2.gcdDelta z1 z2 p.1 p.2 : ℝ)
          * (1 + Work.FIArea2.secFreq₁ z1 z2 p.1 ^ 2 * Real.sqrt (1 - γ ^ 2) * Real.sqrt Pa.M)⁻¹
          * (1 + Work.FIArea2.secFreq₂ z1 z2 p.2 ^ 2 * Real.sqrt (1 - γ ^ 2) * Real.sqrt Pa.M)⁻¹))
      (fun p : ℤ × ℤ => (if p = (0, 0) then 0 else
        Work.FIArea2.Fint F γ (-(Work.FIArea2.secFreq₁ z1 z2 p.1))
          (-(Work.FIArea2.secFreq₂ z1 z2 p.2))
        * Work.FIArea2.Gsum z1 z2 p.1 p.2)) hg hT
  have hconv : (∑' p : ℤ × ℤ, (if p = (0, 0) then 0 else
      (Work.FIArea2.gcdDelta z1 z2 p.1 p.2 : ℝ)
        * (1 + Work.FIArea2.secFreq₁ z1 z2 p.1 ^ 2 * Real.sqrt (1 - γ ^ 2) * Real.sqrt Pa.M)⁻¹
        * (1 + Work.FIArea2.secFreq₂ z1 z2 p.2 ^ 2 * Real.sqrt (1 - γ ^ 2) * Real.sqrt Pa.M)⁻¹))
      = HaverG Pa γ z1 z2 := by
    rw [HaverG]
    exact tsum_congr fun p => (by rw [HaverTerm])
  rw [hconv] at hmain
  refine le_trans hmain (le_of_eq ?_)
  ring

end

end Work.FIArea2.R6
