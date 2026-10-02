import Mathlib
import Submission.Work.MRMT.Found.Defs
import Submission.Work.MRMT.Found.dzbar_symm_le
import Submission.Work.MRMT.Found.courantLebesgue_uniform
import Submission.Work.MRMT.Found.norm_symm_sub_le
import Submission.Work.MRMT.Found.exists_tendstoLocallyUniformly_of_l2_of_modulus
import Submission.Work.MRMT.Found.exists_delta_div_log_lt

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# Uniform equicontinuity of the inverses of the `F n`

Let `Fn n : ℂ ≃ₜ ℂ` be a `C¹` homeomorphism of the plane (with `C¹` inverse) whose complex
dilatation is bounded by `k < 1` and whose displacement decays like `O(1/‖z‖)` at infinity:
`‖Fn n z - z‖ ≤ Cd / ‖z‖` for `‖z‖ ≥ Rd`.

We prove that the inverses `(Fn n)⁻¹` are *uniformly* (in `n`) equicontinuous on every ball:
for every `N` and `ε > 0` there is `δ > 0`, `δ ≤ 1/4`, such that `‖v‖ ≤ N` and `‖u - v‖ < δ`
imply `‖(Fn n)⁻¹ u - (Fn n)⁻¹ v‖ < ε` for every `n`.

The proof has three ingredients.

* The *uniform Courant–Lebesgue estimate* (`courantLebesgue_uniform`): for every injective
  `C¹` map `F` with `‖∂̄F‖ ≤ k ‖∂F‖` pointwise and `‖z - z₀‖ ≤ 1/4`,
  `‖F z - F z₀‖² ≤ c · volume (F '' ball z₀ 1) / log (1/‖z - z₀‖)`.
  The inverse `G n := (Fn n)⁻¹` satisfies the hypotheses, with the same constant `k`
  (the inverse-matrix relation `dzbar_symm_le`).
* A *uniform bound on the images of unit balls*: the decay of `Fn n` at infinity bounds the
  preimage of a bounded ball, uniformly in `n`: if `‖w‖ ≤ M` and `z = (Fn n)⁻¹ w` then either
  `‖z‖ ≤ Rd` or `‖z‖² ≤ M ‖z‖ + Cd`, so `‖z‖ ≤ max Rd ((M + √(M² + 4 Cd))/2)`.
  Hence `volume ((Fn n)⁻¹ '' ball v 1)` is bounded by a constant depending only on
  `Cd, Rd, N` for `‖v‖ ≤ N`.
* The *elementary inversion of the logarithmic bound*: for `c, A ≥ 0` and `ε > 0` there is
  `δ ≤ 1/4` with `c A / log (1/t) < ε²` for all `0 < t < δ`; take
  `δ = min (1/4) (exp (-(c A / ε²)))`, so that `t < δ` forces `log (1/t) > c A / ε²`.

Combining the Courant–Lebesgue estimate for `G n` with the uniform volume bound and the
elementary choice of `δ` gives the modulus of continuity, uniformly in `n`.
-/

noncomputable section

open MeasureTheory Metric Filter Topology Complex

namespace Work.MRMT.Found

/-! ## Three auxiliary estimates -/

/-- **Preimage of a bounded ball.**  If the homeomorphism `F` satisfies
`‖F z - z‖ ≤ C / ‖z‖` for `‖z‖ ≥ R` with `R ≥ 0`, then every point of norm at most `M` has
preimage of norm at most `max R ((M + √(M² + 4C))/2)`. -/
private lemma symm_norm_le_of_decay_aux {F : ℂ ≃ₜ ℂ} {C R M : ℝ}
    (hdec : ∀ z : ℂ, R ≤ ‖z‖ → ‖F z - z‖ ≤ C / ‖z‖) (hR : 0 ≤ R)
    {w : ℂ} (hw : ‖w‖ ≤ M) :
    ‖(F.symm : ℂ → ℂ) w‖ ≤ max R ((M + Real.sqrt (M ^ 2 + 4 * C)) / 2) := by
  set z : ℂ := (F.symm : ℂ → ℂ) w with hzdef
  have hFz : F z = w := by rw [hzdef]; exact F.apply_symm_apply w
  by_cases hRz : R ≤ ‖z‖
  · have h1 : ‖w - z‖ ≤ C / ‖z‖ := by
      have h := hdec z hRz
      rwa [hFz] at h
    by_cases hz0 : ‖z‖ = 0
    · rw [hz0]; exact le_trans hR (le_max_left _ _)
    · have hzpos : 0 < ‖z‖ := lt_of_le_of_ne (norm_nonneg z) (Ne.symm hz0)
      have h2 : ‖z‖ ≤ ‖w‖ + C / ‖z‖ := by
        have h3 : ‖z‖ ≤ ‖z - w‖ + ‖w‖ := by
          have := norm_add_le (z - w) w
          rwa [sub_add_cancel] at this
        rw [norm_sub_rev] at h3
        linarith
      have h4 : ‖z‖ * ‖z‖ ≤ M * ‖z‖ + C := by
        have h5 : ‖z‖ * ‖z‖ ≤ (‖w‖ + C / ‖z‖) * ‖z‖ :=
          mul_le_mul_of_nonneg_right h2 (norm_nonneg z)
        have h6 : (‖w‖ + C / ‖z‖) * ‖z‖ = ‖w‖ * ‖z‖ + C := by
          rw [add_mul, div_mul_cancel₀ C hz0]
        rw [h6] at h5
        have h7 : ‖w‖ * ‖z‖ ≤ M * ‖z‖ := mul_le_mul_of_nonneg_right hw (norm_nonneg z)
        linarith
      have h8 : (2 * ‖z‖ - M) ^ 2 ≤ M ^ 2 + 4 * C := by nlinarith
      have h9 : 2 * ‖z‖ - M ≤ Real.sqrt (M ^ 2 + 4 * C) := by
        have h10 := Real.sqrt_le_sqrt h8
        rw [Real.sqrt_sq_eq_abs] at h10
        linarith [le_abs_self (2 * ‖z‖ - M)]
      have h11 : ‖z‖ ≤ (M + Real.sqrt (M ^ 2 + 4 * C)) / 2 := by linarith
      exact le_trans h11 (le_max_right _ _)
  · rw [not_le] at hRz
    exact le_trans hRz.le (le_max_left _ _)

/-- **Uniform volume bound.**  Under the uniform decay hypothesis the volume of the image of
any unit ball under any of the inverses `(Fn n)⁻¹` is bounded by a constant independent of `n`
(and of the centre `v`, as long as `‖v‖ ≤ N`). -/
private lemma symm_ball_volume_bound_aux {Cd Rd N : ℝ} {Fn : ℕ → ℂ ≃ₜ ℂ}
    (hRd : 0 ≤ Rd)
    (hdec : ∀ n : ℕ, ∀ z : ℂ, Rd ≤ ‖z‖ → ‖Fn n z - z‖ ≤ Cd / ‖z‖) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ n : ℕ, ∀ v : ℂ, ‖v‖ ≤ N →
      ((MeasureTheory.volume : MeasureTheory.Measure ℂ)
        (((Fn n).symm : ℂ → ℂ) '' Metric.ball v (1 : ℝ))).toReal ≤ A := by
  set M : ℝ := max N 0 + 1 with hMdef
  set B : ℝ := max Rd ((M + Real.sqrt (M ^ 2 + 4 * Cd)) / 2) with hBdef
  refine ⟨((MeasureTheory.volume : MeasureTheory.Measure ℂ) (Metric.closedBall 0 B)).toReal,
    ENNReal.toReal_nonneg, ?_⟩
  intro n v hv
  have hfin : (MeasureTheory.volume : MeasureTheory.Measure ℂ)
      (Metric.closedBall (0:ℂ) B) ≠ ⊤ := (isCompact_closedBall (0:ℂ) B).measure_lt_top.ne
  refine ENNReal.toReal_mono hfin (MeasureTheory.measure_mono ?_)
  rintro _ ⟨w, hw, rfl⟩
  rw [Metric.mem_ball] at hw
  have hwn : ‖w‖ ≤ M := by
    have h1 : ‖w - v‖ < 1 := by rwa [dist_eq_norm] at hw
    have h2 : ‖w‖ ≤ ‖w - v‖ + ‖v‖ := by
      have := norm_add_le (w - v) v
      rwa [sub_add_cancel] at this
    have h3 : ‖v‖ ≤ max N 0 := le_trans hv (le_max_left N 0)
    rw [hMdef]
    linarith
  have hF := symm_norm_le_of_decay_aux (F := Fn n) (C := Cd) (R := Rd) (M := M)
    (hdec n) hRd hwn
  rw [Metric.mem_closedBall, dist_zero_right]
  exact hF

/-! ## The main statement -/

theorem equicontinuous_symm_of_beltrami {μn : ℕ → ℂ → ℂ} {k Cd Rd : ℝ} {Fn : ℕ → ℂ ≃ₜ ℂ}
    (hk0 : 0 ≤ k) (hk1 : k < 1) (hCd : 0 ≤ Cd) (hRd : 1 ≤ Rd)
    (hμnB : ∀ n z, ‖μn n z‖ ≤ k)
    (hFC : ∀ n, ContDiff ℝ 1 (Fn n : ℂ → ℂ))
    (hFCS : ∀ n, ContDiff ℝ 1 ((Fn n).symm : ℂ → ℂ))
    (hFB : ∀ n z, Work.MRMT.dzbar (Fn n : ℂ → ℂ) z = μn n z * Work.MRMT.dz (Fn n : ℂ → ℂ) z)
    (hdec : ∀ n : ℕ, ∀ z : ℂ, Rd ≤ ‖z‖ → ‖Fn n z - z‖ ≤ Cd / ‖z‖) :
    ∀ N : ℝ, ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 / 4 ∧
      ∀ n : ℕ, ∀ u v : ℂ, ‖v‖ ≤ N → ‖u - v‖ < δ →
        ‖((Fn n).symm : ℂ → ℂ) u - ((Fn n).symm : ℂ → ℂ) v‖ < ε := by
  -- The uniform Courant–Lebesgue constant.
  obtain ⟨c, hcpos, hc⟩ := courantLebesgue_uniform k hk0 hk1
  intro N ε hε
  -- The uniform bound on the volume of the images of unit balls under the inverses.
  obtain ⟨A, hA0, hA⟩ := symm_ball_volume_bound_aux (Fn := Fn) (Cd := Cd) (Rd := Rd) (N := N)
    (le_trans zero_le_one hRd) hdec
  -- The logarithmic threshold.
  obtain ⟨δ, hδpos, hδle, hδ⟩ := exists_delta_div_log_lt hcpos hA0 hε
  refine ⟨δ, hδpos, hδle, ?_⟩
  intro n u v hv huv
  by_cases huv_eq : u = v
  · subst huv_eq
    simpa using hε
  · have htpos : 0 < ‖u - v‖ := norm_pos_iff.mpr (sub_ne_zero.mpr huv_eq)
    have hquarter : ‖u - v‖ ≤ 1 / 4 := le_of_lt (lt_of_lt_of_le huv hδle)
    -- The inverse `G n` satisfies the hypotheses of Courant–Lebesgue.
    have hdil : ∀ w : ℂ, ‖Work.MRMT.dzbar ((Fn n).symm : ℂ → ℂ) w‖
        ≤ k * ‖Work.MRMT.dz ((Fn n).symm : ℂ → ℂ) w‖ :=
      (dzbar_symm_le (Fn n) (μn n) k (hFC n) (hFCS n) (hFB n) (hμnB n)).1
    have hinj : Function.Injective ((Fn n).symm : ℂ → ℂ) := (Fn n).symm.injective
    have hCL := hc (hFCS n) hinj hdil v u hquarter
    -- The volume of `(Fn n)⁻¹ '' ball v 1` is at most `A`.
    have hvol := hA n v hv
    have hlogpos : 0 < Real.log (1 / ‖u - v‖) := by
      apply Real.log_pos
      rw [one_lt_div htpos]
      linarith
    have hstep : c * ((MeasureTheory.volume : MeasureTheory.Measure ℂ)
          (((Fn n).symm : ℂ → ℂ) '' Metric.ball v (1 : ℝ))).toReal / Real.log (1 / ‖u - v‖)
        ≤ c * A / Real.log (1 / ‖u - v‖) :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hvol hcpos.le) hlogpos.le
    have hfin := hδ ‖u - v‖ htpos huv
    have hsq : ‖((Fn n).symm : ℂ → ℂ) u - ((Fn n).symm : ℂ → ℂ) v‖ ^ 2 < ε ^ 2 :=
      lt_of_le_of_lt (le_trans hCL hstep) hfin
    have h' : |‖((Fn n).symm : ℂ → ℂ) u - ((Fn n).symm : ℂ → ℂ) v‖| < |ε| := sq_lt_sq.mp hsq
    rwa [abs_of_nonneg (norm_nonneg _), abs_of_pos hε] at h'

end Work.MRMT.Found
