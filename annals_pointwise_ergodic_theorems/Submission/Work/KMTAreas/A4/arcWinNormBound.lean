/-
# Norm summability and a uniform bound for the single-arc window kernel

`arcWin ψ N s m = N⁻¹ ψ(m/N) e(m s)` has norm `‖arcWin ψ N s m‖ = N⁻¹ ‖ψ(m/N)‖`,
independent of the frequency `s`.  Hence:

* summability of `m ↦ ‖arcWin ψ N s m‖` for every `N` and `s`
  (`Work.KMTAreas.A4.schwartzSamplingSummable` for `N ≥ 1`, the kernel vanishing identically
  for `N = 0`);
* a bound `∑_m ‖arcWin ψ N s m‖ ≤ K`, uniform in `N ≥ 1` and `s`.

For the second point, the two-regime estimate (`Work.KMTAreas.A4.winPointwiseLe`)

  `N⁻¹ ‖ψ(m/N)‖ ≤ (4D + 4C) N / (N + |m|)²`

(with `D` a global bound for `‖ψ‖` and `C` the constant of the `|y|⁻²` decay) reduces the claim to
the elementary lattice estimate `∑_{m : ℤ} N / (N + |m|)² ≤ 5` for `N ≥ 1`, supplied by `Work.KMTAreas.A4.winFracSumBound`.
-/
import Mathlib
import Submission.Work.KMTAreas.A4.lip2ArcDefs
import Submission.Work.KMTAreas.A4.schwartzSamplingSummable
import Submission.Work.KMTAreas.A4.winPointwiseLe
import Submission.Work.KMTAreas.A4.winFracSumBound

set_option autoImplicit false
set_option maxHeartbeats 1000000

open scoped BigOperators

namespace Work.KMTAreas.A4

open Work.Analysis.InverseTheory

/-! ## Preparatory lemmas -/

lemma norm_arcWin (ψ : SchwartzR) (N : ℕ) (s : ℝ) (m : ℤ) :
    ‖arcWin ψ N s m‖ = (N : ℝ)⁻¹ * ‖ψ ((m : ℝ)/(N : ℝ))‖ := by
  simp only [arcWin, norm_mul]
  rw [fourier_apply, Circle.norm_coe, mul_one, norm_inv, Complex.norm_natCast]

/-- The two regimes of Schwartz decay: a global bound `D`, and the `|y|⁻²` decay away from `0`. -/
lemma schwartzTwoRegime (ψ : SchwartzR) :
    ∃ D C : ℝ, 0 ≤ D ∧ 0 ≤ C ∧ (∀ y : ℝ, ‖ψ y‖ ≤ D) ∧
      (∀ y : ℝ, 1 ≤ |y| → ‖ψ y‖ ≤ C / |y| ^ 2) := by
  obtain ⟨C, hCpos, hCdecay⟩ := schwartz_decay_inv_sq ψ
  refine ⟨max (SchwartzMap.seminorm ℝ 0 0 ψ) 0, C, le_max_right _ _, hCpos.le, ?_, ?_⟩
  · intro y
    exact (SchwartzMap.norm_le_seminorm ℝ ψ y).trans (le_max_left _ _)
  · intro y hy
    have h := hCdecay y hy
    rw [mul_one_div, Real.rpow_two] at h
    exact h

/-- Summability of the lattice sampling of a Schwartz function at scale `N ≥ 1`. -/
lemma summable_norm_schwartz_div (ψ : SchwartzR) {N : ℕ} (hN : 1 ≤ N) :
    Summable (fun m : ℤ => ‖ψ ((m : ℝ)/(N : ℝ))‖) := by
  have hNne : (N : ℝ) ≠ 0 := by positivity
  have hc : ((N : ℝ))⁻¹ ≠ 0 := inv_ne_zero hNne
  have h := schwartzSamplingSummable ψ (a := 0) (c := ((N : ℝ))⁻¹) hc
  refine h.congr (fun m => ?_)
  congr 1
  field_simp
  ring


/-! ## The target -/

theorem arcWinNormBound (ψ : Work.Analysis.InverseTheory.SchwartzR) : (∀ (N : ℕ) (s : ℝ), Summable fun m : ℤ => ‖Work.KMTAreas.A4.arcWin ψ N s m‖) ∧ (∃ K : ℝ, 0 < K ∧ ∀ (N : ℕ), 1 ≤ N → ∀ s : ℝ, (∑' m : ℤ, ‖Work.KMTAreas.A4.arcWin ψ N s m‖) ≤ K) := by

  obtain ⟨D, C, hD, hC, hDb, hCb⟩ := schwartzTwoRegime ψ
  have hA : 0 ≤ 4 * D + 4 * C := by linarith
  have hkey : ∀ (N : ℕ), 1 ≤ N → ∀ s : ℝ,
      (∑' m : ℤ, ‖arcWin ψ N s m‖) ≤ (4 * D + 4 * C) * 5 + 1 := by
    intro N hN s
    have hN1 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
    have hsumL : Summable (fun m : ℤ => (N : ℝ)⁻¹ * ‖ψ ((m : ℝ)/(N : ℝ))‖) :=
      (summable_norm_schwartz_div ψ hN).mul_left _
    have hfrac := winFracSumBound (N : ℝ) hN1
    have hsumR : Summable (fun m : ℤ =>
        (4 * D + 4 * C) * ((N : ℝ)/((N : ℝ) + |(m : ℝ)|)^2)) := hfrac.1.mul_left _
    calc (∑' m : ℤ, ‖arcWin ψ N s m‖)
        = ∑' m : ℤ, (N : ℝ)⁻¹ * ‖ψ ((m : ℝ)/(N : ℝ))‖ :=
          tsum_congr (fun m => norm_arcWin ψ N s m)
      _ ≤ ∑' m : ℤ, (4 * D + 4 * C) * ((N : ℝ)/((N : ℝ) + |(m : ℝ)|)^2) := by
          refine Summable.tsum_le_tsum (fun m => ?_) hsumL hsumR
          have h := winPointwiseLe (φ := (ψ : SchwartzMap ℝ ℂ)) hD hC hDb hCb hN1 m
          simpa only [mul_div_assoc] using h
      _ = (4 * D + 4 * C) * (∑' m : ℤ, (N : ℝ)/((N : ℝ) + |(m : ℝ)|)^2) := tsum_mul_left
      _ ≤ (4 * D + 4 * C) * 5 := by
          have := hfrac.2
          exact mul_le_mul_of_nonneg_left this hA
      _ ≤ (4 * D + 4 * C) * 5 + 1 := by linarith
  refine ⟨?_, ⟨(4 * D + 4 * C) * 5 + 1, by linarith, hkey⟩⟩
  intro N s
  rcases Nat.eq_zero_or_pos N with hN | hN
  · subst hN
    have hzero : (fun m : ℤ => ‖arcWin ψ 0 s m‖) = fun _ => 0 := by
      funext m
      rw [norm_arcWin]
      simp
    rw [hzero]
    exact summable_zero
  · exact ((summable_norm_schwartz_div ψ hN).mul_left _).congr
      (fun m => (norm_arcWin ψ N s m).symm)

end Work.KMTAreas.A4
