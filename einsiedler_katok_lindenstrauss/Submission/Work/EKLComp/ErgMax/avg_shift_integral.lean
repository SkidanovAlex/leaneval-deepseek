import Mathlib
import Submission.Work.EKLComp.ErgMax.ShiftDefs
import Submission.Work.EKLComp.ErgMax.oscillation_eventually_small
import Submission.Work.EKLComp.ErgMax.integral_avg_sum
import Submission.Work.EKLComp.ErgMax.integral_avg_map_sum
import Submission.Work.EKLComp.ErgMax.psi_step_le
import Submission.Work.EKLComp.ErgMax.psi_abs_le
import Submission.Work.EKLComp.ErgMax.shift_double_sum_le

/-!
# `avg_shift_integral` — the shift-invariance estimate for the `A⁺`-average

This is step 4 of the `ErgMax` plan: for `ν` a probability measure concentrated on the compact
forward-invariant set `Drho ρ` and `f : X₃ →ᵇ ℝ`, the integrals of `f` against `avg ν N` and
against its pushforward under `act (aPlus r s)` (`r, s ≥ 0`) differ by `o(1)`.

Both integrals expand as normalised double sums of `psi ν f u v = ∫ y, f (aPlus u v • y) ∂ν`:

  `∫ f ∂(avg ν N) = (n N · n N)⁻¹ · Σ_{i,j} psi ν f (i/N) (j/N)`
  `∫ f ∂((avg ν N).map (act (aPlus r s))) = (n N · n N)⁻¹ · Σ_{i,j} psi ν f (i/N + r) (j/N + s)`

(`integral_avg_sum`, `integral_avg_map_sum`; `n N = N²`).  The shift by `(r,s)` in the *argument*
of `psi` is a shift by `(⌊rN⌋, ⌊sN⌋)` grid steps of size `1/N`, so the two double sums differ by
at most `2 (n N)² · osc + 2 ‖f‖ (⌊rN⌋ + ⌊sN⌋) (n N)` (`shift_double_sum_le`), where `osc` is the
oscillation of `z ↦ f (aPlus a b • z)` on `Drho ρ` for `0 ≤ a, b ≤ 1/N`
(`psi_step_le`, `psi_abs_le`).  Since `⌊rN⌋ + ⌊sN⌋ ≤ (r+s) N` and `n N = N²`, dividing by
`(n N)² = N⁴` leaves `2 osc + 2 ‖f‖ (r+s)/N → 0`.
-/

open MeasureTheory Filter Topology
open scoped ENNReal

namespace Work.EKLComp.ErgMax

open Work.EKLContract

/-! ## Arithmetic glue -/

private lemma arith_key {N M K r s b : ℝ} (hN : 1 ≤ N) (hb : 0 < b) (hM : 0 ≤ M)
    (hK : K ≤ (r + s) * N) (hlin : 2 * M * (r + s) < (b / 2) * N) :
    ((N ^ 2 * N ^ 2)⁻¹) * (2 * (N ^ 2) ^ 2 * (b / 4) + 2 * M * K * N ^ 2) < b := by
  have hNpos : 0 < N := lt_of_lt_of_le zero_lt_one hN
  have h1 : 2 * M * K ≤ 2 * M * ((r + s) * N) := by nlinarith [hK, hM]
  have h2 : 2 * M * ((r + s) * N) < (b / 2) * (N ^ 2) := by nlinarith [hlin, hNpos]
  have hN2 : 0 < N ^ 2 := by positivity
  have h1' : 2 * M * K * N ^ 2 ≤ 2 * M * ((r + s) * N) * N ^ 2 :=
    mul_le_mul_of_nonneg_right h1 hN2.le
  have h2' : 2 * M * ((r + s) * N) * N ^ 2 < (b / 2) * (N ^ 2 * N ^ 2) := by
    have := mul_lt_mul_of_pos_right h2 hN2
    nlinarith [this]
  rw [inv_mul_eq_div, div_lt_iff₀ (by positivity : (0:ℝ) < N ^ 2 * N ^ 2)]
  nlinarith [h1', h2']

private lemma eventually_mul_lt_atTop {C b : ℝ} (hb : 0 < b) :
    ∀ᶠ N : ℕ in Filter.atTop, C < (b / 2) * (N : ℝ) := by
  have h : Filter.Tendsto (fun N : ℕ => (b / 2) * (N : ℝ)) Filter.atTop Filter.atTop :=
    Filter.Tendsto.const_mul_atTop (by linarith) tendsto_natCast_atTop_atTop
  exact h.eventually (Filter.eventually_gt_atTop C)

private lemma one_le_eventually : ∀ᶠ N : ℕ in Filter.atTop, (1 : ℕ) ≤ N :=
  Filter.eventually_atTop.2 ⟨1, fun N hN => hN⟩

/-! ## The shift-invariance estimate -/

theorem avg_shift_integral (ν : MeasureTheory.Measure Work.EKLContract.X3)
    [MeasureTheory.IsProbabilityMeasure ν] {ρ : ℝ} (hν : ν (Work.EKLContract.Drho ρ) = 1)
    (hK : IsCompact (Work.EKLContract.Drho ρ)) (f : BoundedContinuousFunction Work.EKLContract.X3 ℝ)
    {r s : ℝ} (hr : 0 ≤ r) (hs : 0 ≤ s) :
    Filter.Tendsto (fun N : ℕ =>
        |(∫ x, f x ∂((Work.EKLComp.ErgMax.avg ν N).map
            (Work.EKLComp.ErgMax.act (Work.EKLContract.aPlus r s))))
          - (∫ x, f x ∂(Work.EKLComp.ErgMax.avg ν N))|)
      Filter.atTop (nhds 0) := by
  have hMnn : 0 ≤ ‖f‖ := norm_nonneg f
  refine tendsto_order.2 ⟨?_, ?_⟩
  · -- the lower bound is trivial: the sequence is nonnegative
    intro ε hε
    filter_upwards with N
    exact lt_of_lt_of_le hε (abs_nonneg _)
  · -- the upper bound: given `ε > 0`, eventually the difference is `< ε`
    intro ε hε
    have hε2 : 0 < ε / 2 := by linarith
    have hε4 : 0 < ε / 4 := by linarith
    -- the oscillation of `f` under an `(1/N)`-step on `Drho ρ` is eventually `< ε/4`
    have hosc : ∀ᶠ N : ℕ in atTop, ∀ z ∈ Drho ρ, ∀ a b : ℝ, 0 ≤ a → a ≤ 1 / (N : ℝ) →
        0 ≤ b → b ≤ 1 / (N : ℝ) → |f (aPlus a b • z) - f z| < ε / 4 :=
      oscillation_eventually_small (Drho ρ) hK f (ε / 4) hε4
    -- and `N` eventually dominates the fixed constant `2 ‖f‖ (r+s) / (ε/2)`
    have hlin : ∀ᶠ N : ℕ in atTop, (2 * ‖f‖ * (r + s)) < (ε / 2) * (N : ℝ) :=
      eventually_mul_lt_atTop (C := 2 * ‖f‖ * (r + s)) hε
    filter_upwards [hosc, one_le_eventually, hlin] with N hoscN hN1 hlinN
    have hNle : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN1
    have hncast : ((n N : ℕ) : ℝ) = (N : ℝ) ^ 2 := by simp [n, pow_two]
    have hccast : (((n N * n N : ℕ) : ℝ)) = (N : ℝ) ^ 2 * (N : ℝ) ^ 2 := by
      rw [Nat.cast_mul, hncast]
    have hc_nn : 0 ≤ (((n N * n N : ℕ) : ℝ))⁻¹ := inv_nonneg.mpr (by positivity)
    -- the `psi`-step bounds in the two variables, with the common constant `ε/4`
    have hstep1 : ∀ u v t : ℝ, 0 ≤ u → 0 ≤ v → 0 ≤ t → t ≤ 1 / (N : ℝ) →
        |psi ν f (u + t) v - psi ν f u v| ≤ ε / 4 := by
      intro u v t hu hv ht htu
      have h := psi_step_le (ν := ν) (ρ := ρ) (f := f) (u := u) (v := v) (a := t) (b := 0)
        (e := ε / 4) hν hK hu hv ht (le_refl 0)
        (fun z hz => le_of_lt (hoscN z hz t 0 ht htu (le_refl 0) (by positivity)))
      simpa using h
    have hstep2 : ∀ u v t : ℝ, 0 ≤ u → 0 ≤ v → 0 ≤ t → t ≤ 1 / (N : ℝ) →
        |psi ν f u (v + t) - psi ν f u v| ≤ ε / 4 := by
      intro u v t hu hv ht htu
      have h := psi_step_le (ν := ν) (ρ := ρ) (f := f) (u := u) (v := v) (a := 0) (b := t)
        (e := ε / 4) hν hK hu hv (le_refl 0) ht
        (fun z hz => le_of_lt (hoscN z hz 0 t (le_refl 0) (by positivity) ht htu))
      simpa using h
    have hMb : ∀ u v : ℝ, |psi ν f u v| ≤ ‖f‖ := fun u v => psi_abs_le ν f u v
    -- the two double sums differ by at most `2 (n N)² (ε/4) + 2 ‖f‖ K (n N)`
    have hS := shift_double_sum_le (N := N) (m := n N) (G := psi ν f) (e := ε / 4)
      (M := ‖f‖) (r := r) (s := s) hN1 hr hs hstep1 hstep2 hMb
    have hKle : (((⌊r * (N : ℝ)⌋ : ℤ) : ℝ) + ((⌊s * (N : ℝ)⌋ : ℤ) : ℝ)) ≤ (r + s) * (N : ℝ) := by
      have h1 : ((⌊r * (N : ℝ)⌋ : ℤ) : ℝ) ≤ r * (N : ℝ) := Int.floor_le _
      have h2 : ((⌊s * (N : ℝ)⌋ : ℤ) : ℝ) ≤ s * (N : ℝ) := Int.floor_le _
      linarith
    have harith := arith_key (N := (N : ℝ)) (M := ‖f‖)
      (K := ((⌊r * (N : ℝ)⌋ : ℤ) : ℝ) + ((⌊s * (N : ℝ)⌋ : ℤ) : ℝ))
      (r := r) (s := s) (b := ε) hNle hε hMnn hKle hlinN
    have hfin : (((n N * n N : ℕ) : ℝ))⁻¹ *
        (2 * ((n N : ℕ) : ℝ) ^ 2 * (ε / 4) + 2 * ‖f‖ *
          (((⌊r * (N : ℝ)⌋ : ℤ) : ℝ) + ((⌊s * (N : ℝ)⌋ : ℤ) : ℝ)) * ((n N : ℕ) : ℝ)) < ε := by
      rw [hncast, hccast]
      exact harith
    -- expand both integrals and conclude
    rw [integral_avg_map_sum, integral_avg_sum, ← mul_sub, abs_mul, abs_of_nonneg hc_nn]
    exact lt_of_le_of_lt (mul_le_mul_of_nonneg_left hS hc_nn) hfin

end Work.EKLComp.ErgMax
