import Mathlib
import Submission.Work.OddVolterra.Defs
import Submission.Work.OddVolterra.Ball
import Submission.Work.OddVolterra.Existence.data_close_of_small
import Submission.Work.OddExistence.Estimates.rpow_lipschitz_Icc
import Submission.Work.OddExistence.Estimates.diagPhi_abs_bound

/-!
# Closeness of `Godd` in the perturbation

`Work.OddExistence.Estimates.godd_close`: the odd transition-slope data `Godd n h s z`
depends on the perturbation `h` in a `C^{n+2}`-smallness-linear way, uniformly over a compact
slope interval `[a,b] ⊂ (0,1]` and over a ball of radius `ρ ≤ 1/2` around the base state.

The proof reduces `Godd` to the *diagonal* Abel kernels (`G2_diag`, `K1_diag_eq`, `K2_diag_eq`):
at `σ = s` the averaged kernel `G₂` collapses to the `τ`-weight mass times
`Kvec n h s s z`, and the difference of the diagonal kernels is the difference of the
explicit functions `diagPhi1`, `diagPhi2` of the pair `(L, ∂_s L)`.  Those are Lipschitz on
the region `L · ∂_sL ≥ c₀ > 0` (`diagPhi1_diff_le`, `diagPhi2_diff_le`) and globally bounded
(`diagPhi_abs_bound`); the two regimes are combined in `diag_kernel_diff_bound`.
-/

open MeasureTheory Set Filter
open scoped Topology ContDiff Interval

namespace Work.OddExistence.Estimates

open Work.OddVolterra (line lineSlope K1 K2 Kvec G2 Godd St baseState)
open Work.OddVolterra.Existence (diagPhi1 diagPhi2 K1_diag_eq K2_diag_eq G2_diag
  exists_baseState_bound Kvec_diag_sub_apply_zero Kvec_diag_sub_apply_one)

noncomputable section

set_option maxHeartbeats 1200000

/-- `profileX s = 1/√(1+s²)` exceeds `7/10` for `0 ≤ s ≤ 1`; this is the quantitative form of
`1/√2 - 1/2 ≥ 1/5` used to keep the section endpoints away from `0`. -/
lemma seven_tenths_le_profileX {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    (7 : ℝ) / 10 ≤ Commons.Geometry.Ulam.profileX s := by
  have hs2 : s ^ 2 ≤ 1 := by nlinarith
  have hsqrt2 : Real.sqrt 2 ≤ 10 / 7 := by
    have h := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
    nlinarith [Real.sqrt_nonneg 2]
  have hsqrt : Real.sqrt (1 + s ^ 2) ≤ Real.sqrt 2 := Real.sqrt_le_sqrt (by linarith)
  have hpos : 0 < Real.sqrt (1 + s ^ 2) := Real.sqrt_pos.mpr (by positivity)
  have hpos2 : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have h2 : (7 : ℝ) / 10 ≤ 1 / Real.sqrt 2 := by
    rw [le_div_iff₀ hpos2]
    nlinarith
  have h3 : 1 / Real.sqrt 2 ≤ 1 / Real.sqrt (1 + s ^ 2) := one_div_le_one_div_of_le hpos hsqrt
  have hprof : Commons.Geometry.Ulam.profileX s = 1 / Real.sqrt (1 + s ^ 2) := rfl
  rw [hprof]
  linarith

/-- The diagonal first kernel as a real power of the product `L · ∂_sL`. -/
lemma diagPhi1_eq_rpow (n : ℕ) {u v : ℝ} (hW : 0 < u * v) :
    diagPhi1 n (u, v) =
      (-1 : ℝ) ^ (n + 1) * (Nat.doubleFactorial (2 * n + 1) : ℝ) / Real.sqrt 2 *
        (u * v) ^ ((n : ℝ) + 1 / 2) := by
  have hsplit : (u * v) ^ ((n : ℝ) + 1 / 2) = (u * v) ^ n * Real.sqrt (u * v) := by
    rw [Real.rpow_add hW, Real.rpow_natCast, ← Real.sqrt_eq_rpow]
  rw [hsplit]
  unfold diagPhi1
  ring

/-- The diagonal second kernel as a real power of the product `L · ∂_sL`. -/
lemma diagPhi2_eq_rpow (n : ℕ) (hn : 1 ≤ n) {u v : ℝ} (hW : 0 < u * v) :
    diagPhi2 n (u, v) =
      (-1 : ℝ) ^ n * (Nat.doubleFactorial (2 * n - 1) : ℝ) / Real.sqrt 2 *
        ((u * v) ^ ((n : ℝ) - 1 / 2) * v) := by
  have hsplit : (u * v) ^ ((n : ℝ) - 1 / 2) = (u * v) ^ (n - 1) * Real.sqrt (u * v) := by
    rw [show (n : ℝ) - 1 / 2 = ((n - 1 : ℕ) : ℝ) + 1 / 2 by rw [Nat.cast_sub hn]; ring]
    rw [Real.rpow_add hW, Real.rpow_natCast, ← Real.sqrt_eq_rpow]
  rw [hsplit]
  unfold diagPhi2
  ring

/-- Membership of a product in `[c₀, B²]` from component bounds and a lower bound on the product. -/
lemma mul_mem_Icc_of_abs_le {c0 Bq u v : ℝ} (hc0 : 0 < c0) (hBq : 0 ≤ Bq)
    (hu : |u| ≤ Bq) (hv : |v| ≤ Bq) (hW : c0 ≤ u * v) : u * v ∈ Set.Icc c0 (Bq ^ 2) := by
  refine ⟨hW, ?_⟩
  have h2 : |u| * |v| ≤ Bq * Bq := mul_le_mul hu hv (abs_nonneg v) hBq
  have h3 : |u * v| = |u| * |v| := abs_mul u v
  have h4 : |u * v| ≤ Bq ^ 2 := by
    rw [h3]
    exact le_trans h2 (le_of_eq (by ring : Bq * Bq = Bq ^ 2))
  exact le_trans (le_abs_self _) h4

/-- The constant prefactor of `diagPhi1` has absolute value `(2n+1)!!/√2`. -/
lemma abs_const1 (n : ℕ) :
    |((-1 : ℝ) ^ (n + 1) * (Nat.doubleFactorial (2 * n + 1) : ℝ) / Real.sqrt 2)| =
      (Nat.doubleFactorial (2 * n + 1) : ℝ) / Real.sqrt 2 := by
  rw [abs_div, abs_mul]
  have h1 : |((-1 : ℝ)) ^ (n + 1)| = 1 := by simp
  rw [h1, one_mul, abs_of_nonneg (by positivity), abs_of_nonneg (by positivity)]

/-- The constant prefactor of `diagPhi2` has absolute value `(2n-1)!!/√2`. -/
lemma abs_const2 (n : ℕ) :
    |((-1 : ℝ) ^ n * (Nat.doubleFactorial (2 * n - 1) : ℝ) / Real.sqrt 2)| =
      (Nat.doubleFactorial (2 * n - 1) : ℝ) / Real.sqrt 2 := by
  rw [abs_div, abs_mul]
  have h1 : |((-1 : ℝ)) ^ n| = 1 := by simp
  rw [h1, one_mul, abs_of_nonneg (by positivity), abs_of_nonneg (by positivity)]

/-- `diagPhi1` is Lipschitz on the region `L · ∂_sL ≥ c₀` of the box `[-Bq,Bq]²`. -/
lemma diagPhi1_diff_le (n : ℕ) {c0 Bq L : ℝ} (hc0 : 0 < c0) (hBq : 0 ≤ Bq) (hLnn : 0 ≤ L)
    (hL : ∀ x ∈ Set.Icc c0 (Bq ^ 2), ∀ y ∈ Set.Icc c0 (Bq ^ 2),
        |x ^ ((n : ℝ) + 1 / 2) - y ^ ((n : ℝ) + 1 / 2)| ≤ L * |x - y|)
    {u v u' v' : ℝ} (hu : |u| ≤ Bq) (hv : |v| ≤ Bq) (hu' : |u'| ≤ Bq) (hv' : |v'| ≤ Bq)
    (hW : c0 ≤ u * v) (hW' : c0 ≤ u' * v') :
    |diagPhi1 n (u, v) - diagPhi1 n (u', v')| ≤
      (Nat.doubleFactorial (2 * n + 1) : ℝ) / Real.sqrt 2 * (L * Bq * (|u - u'| + |v - v'|)) := by
  have hWpos : 0 < u * v := lt_of_lt_of_le hc0 hW
  have hW'pos : 0 < u' * v' := lt_of_lt_of_le hc0 hW'
  have hmain : |diagPhi1 n (u, v) - diagPhi1 n (u', v')| =
      (Nat.doubleFactorial (2 * n + 1) : ℝ) / Real.sqrt 2 *
        |(u * v) ^ ((n : ℝ) + 1 / 2) - (u' * v') ^ ((n : ℝ) + 1 / 2)| := by
    rw [diagPhi1_eq_rpow n hWpos, diagPhi1_eq_rpow n hW'pos]
    have hfac : (-1 : ℝ) ^ (n + 1) * (Nat.doubleFactorial (2 * n + 1) : ℝ) / Real.sqrt 2 *
          (u * v) ^ ((n : ℝ) + 1 / 2) -
        (-1 : ℝ) ^ (n + 1) * (Nat.doubleFactorial (2 * n + 1) : ℝ) / Real.sqrt 2 *
          (u' * v') ^ ((n : ℝ) + 1 / 2)
        = (-1 : ℝ) ^ (n + 1) * (Nat.doubleFactorial (2 * n + 1) : ℝ) / Real.sqrt 2 *
          ((u * v) ^ ((n : ℝ) + 1 / 2) - (u' * v') ^ ((n : ℝ) + 1 / 2)) := by ring
    rw [hfac, abs_mul, abs_const1]
  rw [hmain]
  have h1 := hL (u * v) (mul_mem_Icc_of_abs_le hc0 hBq hu hv hW)
    (u' * v') (mul_mem_Icc_of_abs_le hc0 hBq hu' hv' hW')
  have h2 : |u * v - u' * v'| ≤ Bq * (|u - u'| + |v - v'|) := by
    have h3 : u * v - u' * v' = (u - u') * v + u' * (v - v') := by ring
    rw [h3]
    calc |(u - u') * v + u' * (v - v')| ≤ |(u - u') * v| + |u' * (v - v')| := abs_add_le _ _
      _ = |u - u'| * |v| + |u'| * |v - v'| := by rw [abs_mul, abs_mul]
      _ ≤ |u - u'| * Bq + Bq * |v - v'| :=
          add_le_add (mul_le_mul_of_nonneg_left hv (abs_nonneg _))
            (mul_le_mul_of_nonneg_right hu' (abs_nonneg _))
      _ = Bq * (|u - u'| + |v - v'|) := by ring
  have h4 : |(u * v) ^ ((n : ℝ) + 1 / 2) - (u' * v') ^ ((n : ℝ) + 1 / 2)|
      ≤ L * Bq * (|u - u'| + |v - v'|) := by
    have h5 := le_trans h1 (mul_le_mul_of_nonneg_left h2 hLnn)
    rwa [← mul_assoc] at h5
  exact mul_le_mul_of_nonneg_left h4 (by positivity)

/-- `diagPhi2` is Lipschitz on the region `L · ∂_sL ≥ c₀` of the box `[-Bq,Bq]²`. -/
lemma diagPhi2_diff_le (n : ℕ) (hn : 1 ≤ n) {c0 Bq L : ℝ} (hc0 : 0 < c0) (hBq : 0 ≤ Bq)
    (hLnn : 0 ≤ L)
    (hL : ∀ x ∈ Set.Icc c0 (Bq ^ 2), ∀ y ∈ Set.Icc c0 (Bq ^ 2),
        |x ^ ((n : ℝ) - 1 / 2) - y ^ ((n : ℝ) - 1 / 2)| ≤ L * |x - y|)
    {u v u' v' : ℝ} (hu : |u| ≤ Bq) (hv : |v| ≤ Bq) (hu' : |u'| ≤ Bq) (hv' : |v'| ≤ Bq)
    (hW : c0 ≤ u * v) (hW' : c0 ≤ u' * v') :
    |diagPhi2 n (u, v) - diagPhi2 n (u', v')| ≤
      (Nat.doubleFactorial (2 * n - 1) : ℝ) / Real.sqrt 2 *
        ((L * Bq * Bq + (Bq ^ 2) ^ ((n : ℝ) - 1 / 2)) * (|u - u'| + |v - v'|)) := by
  have hWpos : 0 < u * v := lt_of_lt_of_le hc0 hW
  have hW'pos : 0 < u' * v' := lt_of_lt_of_le hc0 hW'
  have hW'le : u' * v' ≤ Bq ^ 2 := (mul_mem_Icc_of_abs_le hc0 hBq hu' hv' hW').2
  have hexp : (0 : ℝ) ≤ (n : ℝ) - 1 / 2 := by
    have h : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    linarith
  have h5 : (u' * v') ^ ((n : ℝ) - 1 / 2) ≤ (Bq ^ 2) ^ ((n : ℝ) - 1 / 2) :=
    Real.rpow_le_rpow (le_of_lt hW'pos) hW'le hexp
  have hΔ : 0 ≤ |u - u'| + |v - v'| := by positivity
  have hmain : |diagPhi2 n (u, v) - diagPhi2 n (u', v')| =
      (Nat.doubleFactorial (2 * n - 1) : ℝ) / Real.sqrt 2 *
        |(u * v) ^ ((n : ℝ) - 1 / 2) * v - (u' * v') ^ ((n : ℝ) - 1 / 2) * v'| := by
    rw [diagPhi2_eq_rpow n hn hWpos, diagPhi2_eq_rpow n hn hW'pos]
    have hfac : (-1 : ℝ) ^ n * (Nat.doubleFactorial (2 * n - 1) : ℝ) / Real.sqrt 2 *
          ((u * v) ^ ((n : ℝ) - 1 / 2) * v) -
        (-1 : ℝ) ^ n * (Nat.doubleFactorial (2 * n - 1) : ℝ) / Real.sqrt 2 *
          ((u' * v') ^ ((n : ℝ) - 1 / 2) * v')
        = (-1 : ℝ) ^ n * (Nat.doubleFactorial (2 * n - 1) : ℝ) / Real.sqrt 2 *
          ((u * v) ^ ((n : ℝ) - 1 / 2) * v - (u' * v') ^ ((n : ℝ) - 1 / 2) * v') := by ring
    rw [hfac, abs_mul, abs_const2]
  rw [hmain]
  have h1 := hL (u * v) (mul_mem_Icc_of_abs_le hc0 hBq hu hv hW)
    (u' * v') (mul_mem_Icc_of_abs_le hc0 hBq hu' hv' hW')
  have h2 : |u * v - u' * v'| ≤ Bq * (|u - u'| + |v - v'|) := by
    have h3 : u * v - u' * v' = (u - u') * v + u' * (v - v') := by ring
    rw [h3]
    calc |(u - u') * v + u' * (v - v')| ≤ |(u - u') * v| + |u' * (v - v')| := abs_add_le _ _
      _ = |u - u'| * |v| + |u'| * |v - v'| := by rw [abs_mul, abs_mul]
      _ ≤ |u - u'| * Bq + Bq * |v - v'| :=
          add_le_add (mul_le_mul_of_nonneg_left hv (abs_nonneg _))
            (mul_le_mul_of_nonneg_right hu' (abs_nonneg _))
      _ = Bq * (|u - u'| + |v - v'|) := by ring
  have h7 : |(u * v) ^ ((n : ℝ) - 1 / 2) - (u' * v') ^ ((n : ℝ) - 1 / 2)|
      ≤ L * (Bq * (|u - u'| + |v - v'|)) :=
    le_trans h1 (mul_le_mul_of_nonneg_left h2 hLnn)
  have h8 : |(u' * v') ^ ((n : ℝ) - 1 / 2)| ≤ (Bq ^ 2) ^ ((n : ℝ) - 1 / 2) := by
    rw [abs_of_nonneg (Real.rpow_nonneg (le_of_lt hW'pos) _)]
    exact h5
  have h9 : |(u * v) ^ ((n : ℝ) - 1 / 2) * v - (u' * v') ^ ((n : ℝ) - 1 / 2) * v'|
      ≤ (L * Bq * Bq + (Bq ^ 2) ^ ((n : ℝ) - 1 / 2)) * (|u - u'| + |v - v'|) := by
    have h6 : (u * v) ^ ((n : ℝ) - 1 / 2) * v - (u' * v') ^ ((n : ℝ) - 1 / 2) * v'
        = ((u * v) ^ ((n : ℝ) - 1 / 2) - (u' * v') ^ ((n : ℝ) - 1 / 2)) * v
          + (u' * v') ^ ((n : ℝ) - 1 / 2) * (v - v') := by ring
    rw [h6]
    calc |((u * v) ^ ((n : ℝ) - 1 / 2) - (u' * v') ^ ((n : ℝ) - 1 / 2)) * v
            + (u' * v') ^ ((n : ℝ) - 1 / 2) * (v - v')|
        ≤ |((u * v) ^ ((n : ℝ) - 1 / 2) - (u' * v') ^ ((n : ℝ) - 1 / 2)) * v|
            + |(u' * v') ^ ((n : ℝ) - 1 / 2) * (v - v')| := abs_add_le _ _
      _ = |(u * v) ^ ((n : ℝ) - 1 / 2) - (u' * v') ^ ((n : ℝ) - 1 / 2)| * |v|
            + |(u' * v') ^ ((n : ℝ) - 1 / 2)| * |v - v'| := by rw [abs_mul, abs_mul]
      _ ≤ (L * (Bq * (|u - u'| + |v - v'|))) * Bq
            + (Bq ^ 2) ^ ((n : ℝ) - 1 / 2) * (|u - u'| + |v - v'|) := by
          refine add_le_add ?_ ?_
          · exact mul_le_mul h7 hv (abs_nonneg v) (mul_nonneg hLnn (mul_nonneg hBq hΔ))
          · refine mul_le_mul h8 ?_ (abs_nonneg _) (Real.rpow_nonneg (by positivity) _)
            exact le_add_of_nonneg_left (abs_nonneg _)
      _ = (L * Bq * Bq + (Bq ^ 2) ^ ((n : ℝ) - 1 / 2)) * (|u - u'| + |v - v'|) := by ring
  exact mul_le_mul_of_nonneg_left h9 (by positivity)

/-- Difference bounds for the diagonal Abel kernels `K₁`, `K₂` between a perturbation `h` with
`C⁰`/`C¹`-norms at most `δ ≤ 1/100` and the unperturbed `h = 0`, uniformly in `s ∈ [a,1]` and in
`t` with `1/5 ≤ |t| ≤ Bt`. -/
theorem diag_kernel_diff_bound (n : ℕ) (hn : 1 ≤ n) (a Bt : ℝ) (ha : 0 < a) (ha1 : a ≤ 1)
    (hBt : 2 ≤ Bt) :
    ∃ D : ℝ, 0 < D ∧ ∀ {h : ℝ → ℝ} {δ s t : ℝ},
      (∀ x : ℝ, |h x| ≤ δ) → (∀ x : ℝ, |deriv h x| ≤ δ) →
      0 < δ → δ ≤ 1 / 100 → a ≤ s → s ≤ 1 → 1 / 5 ≤ |t| → |t| ≤ Bt →
      |K1 n h s s t - K1 n 0 s s t| ≤ D * δ ∧
      |K2 n h s s t - K2 n 0 s s t| ≤ D * δ := by
  set Bq : ℝ := Bt + 1 with hBq
  have hBqpos : 0 < Bq := by rw [hBq]; linarith
  have hBqnn : (0 : ℝ) ≤ Bq := le_of_lt hBqpos
  have hBtp : 0 < Bt := by linarith
  set c0 : ℝ := a / 100 with hc0def
  have hc0pos : 0 < c0 := by rw [hc0def]; linarith
  have hc0Bq : c0 ≤ Bq ^ 2 := by rw [hc0def]; nlinarith
  obtain ⟨L1, hL1nn, hL1⟩ :=
    rpow_lipschitz_Icc (r := (n : ℝ) + 1 / 2) (c := c0) (M := Bq ^ 2) hc0pos hc0Bq
  obtain ⟨L2, hL2nn, hL2⟩ :=
    rpow_lipschitz_Icc (r := (n : ℝ) - 1 / 2) (c := c0) (M := Bq ^ 2) hc0pos hc0Bq
  set K1b : ℝ := (Nat.doubleFactorial (2 * n + 1) : ℝ) * Bq ^ (2 * n + 1) / Real.sqrt 2 with hK1b
  set K2b : ℝ := (Nat.doubleFactorial (2 * n - 1) : ℝ) * Bq ^ (2 * n) / Real.sqrt 2 with hK2b
  set A1 : ℝ := (Nat.doubleFactorial (2 * n + 1) : ℝ) / Real.sqrt 2 * (L1 * Bq * 2) with hA1
  set A2 : ℝ := (Nat.doubleFactorial (2 * n - 1) : ℝ) / Real.sqrt 2 *
    ((L2 * Bq * Bq + (Bq ^ 2) ^ ((n : ℝ) - 1 / 2)) * 2) with hA2
  set U1 : ℝ := 2 * K1b * (100 * Bt) / a with hU1
  set U2 : ℝ := 2 * K2b * (100 * Bt) / a with hU2
  have hK1bnn : 0 ≤ K1b := by rw [hK1b]; positivity
  have hK2bnn : 0 ≤ K2b := by rw [hK2b]; positivity
  have hA1nn : 0 ≤ A1 := by rw [hA1]; positivity
  have hA2nn : 0 ≤ A2 := by rw [hA2]; positivity
  have hU1nn : 0 ≤ U1 := by rw [hU1]; positivity
  have hU2nn : 0 ≤ U2 := by rw [hU2]; positivity
  set D : ℝ := 1 + A1 + A2 + U1 + U2 with hD
  have hDpos : 0 < D := by rw [hD]; linarith
  refine ⟨D, hDpos, ?_⟩
  intro h δ s t hh hdh hδ0 hδ100 hs0 hs1 ht1 ht2
  have hsa : |s| ≤ 1 := by
    rw [abs_of_pos (lt_of_lt_of_le ha hs0)]; exact hs1
  have e0 : line 0 s t = s * t := by simp [line]
  have f0 : lineSlope 0 s t = t := by simp [lineSlope]
  have e1 : line h s t = line 0 s t + h s := by simp [line]
  have e2 : lineSlope h s t = lineSlope 0 s t + deriv h s := by simp [lineSlope]
  have hu0 : |line 0 s t| ≤ Bt := by
    rw [e0, abs_mul]; nlinarith [abs_nonneg t]
  have hv0 : |lineSlope 0 s t| ≤ Bt := by rw [f0]; exact ht2
  have hu0Bq : |line 0 s t| ≤ Bq := by rw [hBq]; linarith
  have hv0Bq : |lineSlope 0 s t| ≤ Bq := by rw [hBq]; linarith
  have hu : |line h s t| ≤ Bq := by
    rw [e1, hBq]
    calc |line 0 s t + h s| ≤ |line 0 s t| + |h s| := abs_add_le _ _
      _ ≤ Bt + δ := add_le_add hu0 (hh s)
      _ ≤ Bt + 1 := by linarith
  have hv : |lineSlope h s t| ≤ Bq := by
    rw [e2, hBq]
    calc |lineSlope 0 s t + deriv h s| ≤ |lineSlope 0 s t| + |deriv h s| := abs_add_le _ _
      _ ≤ Bt + δ := add_le_add hv0 (hdh s)
      _ ≤ Bt + 1 := by linarith
  have hdu : |line h s t - line 0 s t| ≤ δ := by
    have h : line h s t - line 0 s t = h s := by rw [e1]; ring
    rw [h]; exact hh s
  have hdv : |lineSlope h s t - lineSlope 0 s t| ≤ δ := by
    have h : lineSlope h s t - lineSlope 0 s t = deriv h s := by rw [e2]; ring
    rw [h]; exact hdh s
  have ht2' : ((1 : ℝ) / 5) ^ 2 ≤ t ^ 2 := by
    have h := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1 / 5) ht1 2
    rwa [sq_abs] at h
  have hW0 : c0 ≤ line 0 s t * lineSlope 0 s t := by
    rw [e0, f0, hc0def]
    nlinarith [ht2', hs0]
  have hΔ2 : |line h s t - line 0 s t| + |lineSlope h s t - lineSlope 0 s t| ≤ 2 * δ := by
    linarith
  by_cases hcase : δ ≤ a / (100 * Bt)
  · -- the safe regime: the product `L · ∂_sL` stays in the region of Lipschitz-continuity
    have h25 : a / 25 ≤ line 0 s t * lineSlope 0 s t := by
      rw [e0, f0]
      nlinarith [ht2', hs0]
    have hW : c0 ≤ line h s t * lineSlope h s t := by
      have hlow : line 0 s t * lineSlope 0 s t - Bt * δ - δ * Bt - δ * δ
          ≤ line h s t * lineSlope h s t := by
        rw [e1, e2]
        have hb1 : -(line 0 s t * deriv h s) ≤ Bt * δ := by
          have h := neg_le_abs (line 0 s t * deriv h s)
          rw [abs_mul] at h
          exact le_trans h (mul_le_mul hu0 (hdh s) (abs_nonneg _) (le_of_lt hBtp))
        have hb2 : -(h s * lineSlope 0 s t) ≤ δ * Bt := by
          have h := neg_le_abs (h s * lineSlope 0 s t)
          rw [abs_mul] at h
          exact le_trans h (mul_le_mul (hh s) hv0 (abs_nonneg _) (le_of_lt hδ0))
        have hb3 : -(h s * deriv h s) ≤ δ * δ := by
          have h := neg_le_abs (h s * deriv h s)
          rw [abs_mul] at h
          exact le_trans h (mul_le_mul (hh s) (hdh s) (abs_nonneg _) (le_of_lt hδ0))
        nlinarith [hb1, hb2, hb3]
      have hcc100 : a / (100 * Bt) ≤ a / 100 := by
        have heq : a / 100 / Bt = a / (100 * Bt) := by rw [div_div]
        rw [← heq]
        exact div_le_self (by positivity) (by linarith : (1 : ℝ) ≤ Bt)
      have hδa : δ ≤ a / 100 := le_trans hcase hcc100
      have hBtD : 2 * Bt * δ ≤ a / 50 := by
        have h1 : δ * (100 * Bt) ≤ a := by
          have h := mul_le_mul_of_nonneg_right hcase
            (show (0 : ℝ) ≤ 100 * Bt by positivity)
          rwa [div_mul_cancel₀ a (by positivity : (100 : ℝ) * Bt ≠ 0)] at h
        nlinarith [h1]
      have hd2 : δ * δ ≤ a / 100 := by
        have h2 : δ * δ ≤ δ * (1 / 100) := mul_le_mul_of_nonneg_left hδ100 (le_of_lt hδ0)
        have h3 : δ * (1 / 100) ≤ (a / 100) * (1 / 100) :=
          mul_le_mul_of_nonneg_right hδa (by norm_num)
        have h4 : (a / 100) * (1 / 100) ≤ a / 100 := by nlinarith [ha]
        linarith
      rw [hc0def]
      linarith
    have hK1 : |K1 n h s s t - K1 n 0 s s t| ≤ A1 * δ := by
      have hd := diagPhi1_diff_le (n := n) (c0 := c0) (Bq := Bq) (L := L1) hc0pos hBqnn hL1nn hL1
        (u := line h s t) (v := lineSlope h s t) (u' := line 0 s t) (v' := lineSlope 0 s t)
        hu hv hu0Bq hv0Bq hW hW0
      rw [K1_diag_eq n h s t, K1_diag_eq n (0 : ℝ → ℝ) s t]
      refine le_trans hd ?_
      rw [hA1]
      have h1 : L1 * Bq * (|line h s t - line 0 s t| + |lineSlope h s t - lineSlope 0 s t|)
          ≤ L1 * Bq * (2 * δ) := mul_le_mul_of_nonneg_left hΔ2 (mul_nonneg hL1nn hBqnn)
      calc (Nat.doubleFactorial (2 * n + 1) : ℝ) / Real.sqrt 2 *
            (L1 * Bq * (|line h s t - line 0 s t| + |lineSlope h s t - lineSlope 0 s t|))
          ≤ (Nat.doubleFactorial (2 * n + 1) : ℝ) / Real.sqrt 2 * (L1 * Bq * (2 * δ)) :=
            mul_le_mul_of_nonneg_left h1 (by positivity)
        _ = (Nat.doubleFactorial (2 * n + 1) : ℝ) / Real.sqrt 2 * (L1 * Bq * 2) * δ := by ring
    have hK2 : |K2 n h s s t - K2 n 0 s s t| ≤ A2 * δ := by
      have hd := diagPhi2_diff_le (n := n) (hn := hn) (c0 := c0) (Bq := Bq) (L := L2)
        hc0pos hBqnn hL2nn hL2
        (u := line h s t) (v := lineSlope h s t) (u' := line 0 s t) (v' := lineSlope 0 s t)
        hu hv hu0Bq hv0Bq hW hW0
      rw [K2_diag_eq n hn h s t, K2_diag_eq n hn (0 : ℝ → ℝ) s t]
      refine le_trans hd ?_
      rw [hA2]
      have h1 : (L2 * Bq * Bq + (Bq ^ 2) ^ ((n : ℝ) - 1 / 2)) *
            (|line h s t - line 0 s t| + |lineSlope h s t - lineSlope 0 s t|)
          ≤ (L2 * Bq * Bq + (Bq ^ 2) ^ ((n : ℝ) - 1 / 2)) * (2 * δ) :=
        mul_le_mul_of_nonneg_left hΔ2 (by positivity)
      calc (Nat.doubleFactorial (2 * n - 1) : ℝ) / Real.sqrt 2 *
            ((L2 * Bq * Bq + (Bq ^ 2) ^ ((n : ℝ) - 1 / 2)) *
              (|line h s t - line 0 s t| + |lineSlope h s t - lineSlope 0 s t|))
          ≤ (Nat.doubleFactorial (2 * n - 1) : ℝ) / Real.sqrt 2 *
              ((L2 * Bq * Bq + (Bq ^ 2) ^ ((n : ℝ) - 1 / 2)) * (2 * δ)) :=
            mul_le_mul_of_nonneg_left h1 (by positivity)
        _ = (Nat.doubleFactorial (2 * n - 1) : ℝ) / Real.sqrt 2 *
              ((L2 * Bq * Bq + (Bq ^ 2) ^ ((n : ℝ) - 1 / 2)) * 2) * δ := by ring
    exact ⟨le_trans hK1 (mul_le_mul_of_nonneg_right (by rw [hD]; linarith) (le_of_lt hδ0)),
      le_trans hK2 (mul_le_mul_of_nonneg_right (by rw [hD]; linarith) (le_of_lt hδ0))⟩
  · -- the unsafe regime: the difference is honestly bounded, and `δ` is comparable to `a / Bt`
    have hcc : a / (100 * Bt) ≤ δ := le_of_lt (lt_of_not_ge hcase)
    have hle1 : 1 ≤ (100 * Bt) * δ / a := by
      rw [le_div_iff₀ ha]
      rw [div_le_iff₀ (by positivity : (0 : ℝ) < 100 * Bt)] at hcc
      rw [mul_comm δ] at hcc
      linarith [hcc]
    have hK1t : |K1 n h s s t| ≤ K1b := by
      rw [K1_diag_eq n h s t, hK1b]
      exact (diagPhi_abs_bound n hn hBqnn hu hv).1
    have hK1z : |K1 n 0 s s t| ≤ K1b := by
      rw [K1_diag_eq n (0 : ℝ → ℝ) s t, hK1b]
      exact (diagPhi_abs_bound n hn hBqnn hu0Bq hv0Bq).1
    have hK2t : |K2 n h s s t| ≤ K2b := by
      rw [K2_diag_eq n hn h s t, hK2b]
      exact (diagPhi_abs_bound n hn hBqnn hu hv).2
    have hK2z : |K2 n 0 s s t| ≤ K2b := by
      rw [K2_diag_eq n hn (0 : ℝ → ℝ) s t, hK2b]
      exact (diagPhi_abs_bound n hn hBqnn hu0Bq hv0Bq).2
    have hsub1 : |K1 n h s s t - K1 n 0 s s t| ≤ 2 * K1b := by
      have h := abs_sub_le (K1 n h s s t) 0 (K1 n 0 s s t)
      rw [sub_zero, zero_sub, abs_neg] at h
      linarith
    have hsub2 : |K2 n h s s t - K2 n 0 s s t| ≤ 2 * K2b := by
      have h := abs_sub_le (K2 n h s s t) 0 (K2 n 0 s s t)
      rw [sub_zero, zero_sub, abs_neg] at h
      linarith
    have hm1 : 2 * K1b ≤ U1 * δ := by
      rw [hU1]
      have hA : 2 * K1b * (100 * Bt) / a * δ = (2 * K1b) * ((100 * Bt) * δ / a) := by ring
      rw [hA]
      exact le_mul_of_one_le_right (by linarith : (0:ℝ) ≤ 2 * K1b) hle1
    have hm2 : 2 * K2b ≤ U2 * δ := by
      rw [hU2]
      have hA : 2 * K2b * (100 * Bt) / a * δ = (2 * K2b) * ((100 * Bt) * δ / a) := by ring
      rw [hA]
      exact le_mul_of_one_le_right (by linarith : (0:ℝ) ≤ 2 * K2b) hle1
    exact ⟨le_trans hsub1 (le_trans hm1
        (mul_le_mul_of_nonneg_right (by rw [hD]; linarith) (le_of_lt hδ0))),
      le_trans hsub2 (le_trans hm2
        (mul_le_mul_of_nonneg_right (by rw [hD]; linarith) (le_of_lt hδ0)))⟩

/-- **Closeness of `Godd` in the perturbation.**  On a compact slope interval
`[a,b] ⊆ (0,1]` and in a ball of radius `ρ ≤ 1/2` around the base state, the odd transition-slope
map `Godd n h s z` differs from the unperturbed `Godd n 0 s z` by at most `C · δ` whenever the
`C^{n+2}`-norm of `h` is at most `δ ≤ 1/100`. -/
theorem godd_close (n : ℕ) (hn : 1 ≤ n) {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) (hb : b ≤ 1)
    {ρ : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ ≤ 1 / 2) :
    ∃ C : ℝ, 0 < C ∧ ∀ h : ℝ → ℝ, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) h →
      ∀ δ : ℝ, 0 < δ → δ ≤ 1 / 100 →
      (∀ k : ℕ, k ≤ n + 2 → ∀ s : ℝ, |iteratedDeriv k h s| ≤ δ) →
      ∀ s ∈ Set.Icc a b, ∀ z : Work.OddVolterra.St, ‖z - Work.OddVolterra.baseState s‖ ≤ ρ →
        ‖Work.OddVolterra.Godd n h s z - Work.OddVolterra.Godd n 0 s z‖ ≤ C * δ := by
  have ha1 : a ≤ 1 := le_trans hab hb
  obtain ⟨B, hB1, hB⟩ := exists_baseState_bound (a := a) ha1
  obtain ⟨D, hD0, hD⟩ := diag_kernel_diff_bound n hn a (B + 1) ha ha1 (by linarith)
  set Cw : ℝ := ∫ τ in (0 : ℝ)..1, (Real.sqrt (τ * (1 - τ)))⁻¹ with hCw
  refine ⟨|Cw| * (2 * (B + 2) * D) + 1, by positivity, ?_⟩
  intro h hh δ hδ0 hδ100 hjet s hs z hz
  have hs0 : a ≤ s := hs.1
  have hs1 : s ≤ 1 := le_trans hs.2 hb
  have hhδ : ∀ x : ℝ, |h x| ≤ δ := fun x => by
    simpa using hjet 0 (Nat.zero_le _) x
  have hdhδ : ∀ x : ℝ, |deriv h x| ≤ δ := fun x => by
    have h1 := hjet 1 (by omega) x
    rwa [iteratedDeriv_one] at h1
  -- component bounds for the state
  have hzbd : ∀ i : Fin 4, |z i - baseState s i| ≤ ρ := by
    intro i
    have h1 : ‖(z - baseState s) i‖ ≤ ‖z - baseState s‖ := norm_le_pi_norm _ i
    rw [Pi.sub_apply, Real.norm_eq_abs] at h1
    linarith
  have hcomp : ∀ i : Fin 4, |z i| ≤ B + 1 := by
    intro i
    have h1 := hzbd i
    have h2 : |baseState s i| ≤ B := by
      obtain ⟨h0', h1', h2', h3'⟩ := hB s ⟨hs0, hs1⟩
      fin_cases i
      · exact h0'
      · exact h1'
      · exact h2'
      · exact h3'
    calc |z i| = |(z i - baseState s i) + baseState s i| := by ring_nf
      _ ≤ |z i - baseState s i| + |baseState s i| := abs_add_le _ _
      _ ≤ B + 1 := by linarith
  -- the two endpoints are bounded below by `1/5`
  have hz0ge : (1 : ℝ) / 5 ≤ z 0 := by
    have h1 : |z 0 - Commons.Geometry.Ulam.profileX s| ≤ ρ := by
      have := hzbd 0
      rwa [show baseState s 0 = Commons.Geometry.Ulam.profileX s from rfl] at this
    have h2 : (7 : ℝ) / 10 ≤ Commons.Geometry.Ulam.profileX s :=
      seven_tenths_le_profileX (le_of_lt (lt_of_lt_of_le ha hs0)) hs1
    have := (abs_le.mp h1).1
    linarith
  have hz1ge : (1 : ℝ) / 5 ≤ z 1 := by
    have h1 : |z 1 - Commons.Geometry.Ulam.profileX s| ≤ ρ := by
      have := hzbd 1
      rwa [show baseState s 1 = Commons.Geometry.Ulam.profileX s from rfl] at this
    have h2 : (7 : ℝ) / 10 ≤ Commons.Geometry.Ulam.profileX s :=
      seven_tenths_le_profileX (le_of_lt (lt_of_lt_of_le ha hs0)) hs1
    have := (abs_le.mp h1).1
    linarith
  have ht1a : (1 : ℝ) / 5 ≤ |-(z 0)| := by rw [abs_neg, abs_of_pos (by linarith)]; exact hz0ge
  have ht2a : |-(z 0)| ≤ B + 1 := by rw [abs_neg]; exact hcomp 0
  have ht1b : (1 : ℝ) / 5 ≤ |z 1| := by rw [abs_of_pos (by linarith)]; exact hz1ge
  have ht2b : |z 1| ≤ B + 1 := hcomp 1
  have hKa := hD (h := h) (δ := δ) (s := s) (t := -(z 0)) hhδ hdhδ hδ0 hδ100 hs0 hs1 ht1a ht2a
  have hKb := hD (h := h) (δ := δ) (s := s) (t := z 1) hhδ hdhδ hδ0 hδ100 hs0 hs1 ht1b ht2b
  -- the difference of the two `Godd`'s
  have hvec : Godd n h s z - Godd n 0 s z =
      ![0, 0,
        -((G2 n h s s (z 0) (z 1) (z 2) (z 3)) 0 - (G2 n 0 s s (z 0) (z 1) (z 2) (z 3)) 0),
        -((G2 n h s s (z 0) (z 1) (z 2) (z 3)) 1 - (G2 n 0 s s (z 0) (z 1) (z 2) (z 3)) 1)] := by
    funext i
    fin_cases i <;> simp [Godd, Pi.sub_apply] <;> ring
  have hG2eq0 : (G2 n h s s (z 0) (z 1) (z 2) (z 3)) 0 -
      (G2 n 0 s s (z 0) (z 1) (z 2) (z 3)) 0 =
      ((Kvec n h s s (z 0) (z 1) (z 2) (z 3)) 0 -
        (Kvec n 0 s s (z 0) (z 1) (z 2) (z 3)) 0) * Cw := by
    rw [G2_diag, G2_diag, ← hCw]
    ring
  have hG2eq1 : (G2 n h s s (z 0) (z 1) (z 2) (z 3)) 1 -
      (G2 n 0 s s (z 0) (z 1) (z 2) (z 3)) 1 =
      ((Kvec n h s s (z 0) (z 1) (z 2) (z 3)) 1 -
        (Kvec n 0 s s (z 0) (z 1) (z 2) (z 3)) 1) * Cw := by
    rw [G2_diag, G2_diag, ← hCw]
    ring
  have hDnn : 0 ≤ D * δ := by positivity
  have hterm1 : |(K1 n h s s (-(z 0)) - K1 n 0 s s (-(z 0))) * (z 2) +
        (K1 n h s s (z 1) - K1 n 0 s s (z 1)) * (z 3)|
      ≤ 2 * (B + 1) * (D * δ) := by
    calc _ ≤ |(K1 n h s s (-(z 0)) - K1 n 0 s s (-(z 0))) * (z 2)|
            + |(K1 n h s s (z 1) - K1 n 0 s s (z 1)) * (z 3)| := abs_add_le _ _
      _ = |K1 n h s s (-(z 0)) - K1 n 0 s s (-(z 0))| * |z 2|
            + |K1 n h s s (z 1) - K1 n 0 s s (z 1)| * |z 3| := by rw [abs_mul, abs_mul]
      _ ≤ (D * δ) * (B + 1) + (D * δ) * (B + 1) :=
          add_le_add (mul_le_mul hKa.1 (hcomp 2) (abs_nonneg _) hDnn)
            (mul_le_mul hKb.1 (hcomp 3) (abs_nonneg _) hDnn)
      _ = 2 * (B + 1) * (D * δ) := by ring
  have hterm2 : |(K2 n h s s (-(z 0)) - K2 n 0 s s (-(z 0))) * (z 2) +
        (K2 n h s s (z 1) - K2 n 0 s s (z 1)) * (z 3)|
      ≤ 2 * (B + 1) * (D * δ) := by
    calc _ ≤ |(K2 n h s s (-(z 0)) - K2 n 0 s s (-(z 0))) * (z 2)|
            + |(K2 n h s s (z 1) - K2 n 0 s s (z 1)) * (z 3)| := abs_add_le _ _
      _ = |K2 n h s s (-(z 0)) - K2 n 0 s s (-(z 0))| * |z 2|
            + |K2 n h s s (z 1) - K2 n 0 s s (z 1)| * |z 3| := by rw [abs_mul, abs_mul]
      _ ≤ (D * δ) * (B + 1) + (D * δ) * (B + 1) :=
          add_le_add (mul_le_mul hKa.2 (hcomp 2) (abs_nonneg _) hDnn)
            (mul_le_mul hKb.2 (hcomp 3) (abs_nonneg _) hDnn)
      _ = 2 * (B + 1) * (D * δ) := by ring
  have hG20 : |(G2 n h s s (z 0) (z 1) (z 2) (z 3)) 0 -
      (G2 n 0 s s (z 0) (z 1) (z 2) (z 3)) 0| ≤ |Cw| * (2 * (B + 1) * (D * δ)) := by
    rw [hG2eq0, abs_mul, Kvec_diag_sub_apply_zero n h 0 s z, abs_neg]
    exact le_trans (mul_le_mul_of_nonneg_right hterm1 (abs_nonneg Cw)) (le_of_eq (by ring))
  have hG21 : |(G2 n h s s (z 0) (z 1) (z 2) (z 3)) 1 -
      (G2 n 0 s s (z 0) (z 1) (z 2) (z 3)) 1| ≤ |Cw| * (2 * (B + 1) * (D * δ)) := by
    rw [hG2eq1, abs_mul, Kvec_diag_sub_apply_one n h 0 s z, abs_neg]
    exact le_trans (mul_le_mul_of_nonneg_right hterm2 (abs_nonneg Cw)) (le_of_eq (by ring))
  have hbound : 0 ≤ |Cw| * (2 * (B + 1) * (D * δ)) := by positivity
  rw [hvec]
  refine le_trans ((pi_norm_le_iff_of_nonneg hbound).mpr fun i => ?_) ?_
  · fin_cases i
    · simpa using hbound
    · simpa using hbound
    · simpa [abs_sub_comm] using hG20
    · simpa [abs_sub_comm] using hG21
  · have hA : 2 * (B + 1) * (D * δ) ≤ 2 * (B + 2) * (D * δ) :=
      mul_le_mul_of_nonneg_right (by linarith) (by positivity)
    calc |Cw| * (2 * (B + 1) * (D * δ)) ≤ |Cw| * (2 * (B + 2) * (D * δ)) :=
          mul_le_mul_of_nonneg_left hA (abs_nonneg Cw)
      _ = (|Cw| * (2 * (B + 2) * D)) * δ := by ring
      _ ≤ (|Cw| * (2 * (B + 2) * D) + 1) * δ :=
          mul_le_mul_of_nonneg_right (by linarith) (le_of_lt hδ0)

end

end Work.OddExistence.Estimates
