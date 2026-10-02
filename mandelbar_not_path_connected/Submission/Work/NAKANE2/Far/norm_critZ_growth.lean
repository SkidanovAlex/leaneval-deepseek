import Mathlib
import Submission.Work.NAKANE2.Defs

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.NAKANE2.Far

open Work.NAKANE2

/-! ## Auxiliary facts for the growth of the critical orbit

The critical orbit of the tricorn family is the `pMap c = T_c ∘ T_c`-orbit of the
critical point `c`.  In the far region `‖z‖ ≥ 2 + ‖c‖` one step of `pMap c` at least
doubles the norm (`Work.Bottcher.Core.pMap_norm_step` and `‖z‖ ≥ 2`), hence the
orbits grow at least geometrically with ratio `2`; this is the whole content of the
file, together with the continuity of `c ↦ critZ c N` (a polynomial in `c` and
`conj c`) which turns the pointwise statement at `c₀` into a uniform one on a ball.
-/

/-- `farRadius C ≥ C + 2` for `C ≥ 0`. -/
lemma critZGrowth_farRadius_ge (C : ℝ) (hC : 0 ≤ C) : C + 2 ≤ Work.NAKANE.farRadius C := by
  unfold Work.NAKANE.farRadius
  have h1 : (1 + C) ≤ max 2 (1 + C) := le_max_right _ _
  have h2 : (0 : ℝ) ≤ (1 + C) ^ 2 := sq_nonneg _
  nlinarith [h1, hC, h2, sq_nonneg (max 2 (1 + C))]

/-- The `N`-th critical-orbit point depends continuously on the parameter: `critZ c N` is a
polynomial in `c` and `conj c`. -/
lemma critZGrowth_continuous (N : ℕ) : Continuous fun c : ℂ => critZ c N := by
  induction N with
  | zero =>
      rw [show (fun c : ℂ => critZ c 0) = id from funext (fun _ => rfl)]
      exact continuous_id
  | succ N ih =>
      have h : (fun c : ℂ => critZ c (N + 1))
          = fun c => ((critZ c N) ^ 2 + (starRingEnd ℂ) c) ^ 2 + c := by
        funext c
        rw [critZ_succ, Work.Bottcher.pMap_apply]
      rw [h]
      fun_prop

/-- In the far region one application of `pMap c` at least doubles the norm. -/
lemma critZGrowth_two_mul_le_norm_pMap (c u : ℂ) (hu : 2 + ‖c‖ ≤ ‖u‖) :
    2 * ‖u‖ ≤ ‖Work.Bottcher.pMap c u‖ := by
  have hu0 : (0 : ℝ) ≤ ‖u‖ := norm_nonneg u
  have hu2 : (2 : ℝ) ≤ ‖u‖ := by linarith [norm_nonneg c, hu]
  have hstep : ‖u‖ ^ 4 / 2 ≤ ‖Work.Bottcher.pMap c u‖ :=
    (Work.Bottcher.Core.pMap_norm_step c u hu).2.1
  have h3 : (8 : ℝ) ≤ ‖u‖ ^ 3 := by
    have := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2) hu2 3
    norm_num at this
    exact this
  have h4 : 8 * ‖u‖ ≤ ‖u‖ ^ 4 := by
    have := mul_le_mul_of_nonneg_right h3 hu0
    nlinarith [this]
  linarith

/-- One step of the critical orbit at least doubles the norm, as long as the orbit is far. -/
lemma critZGrowth_two_mul_le_norm_critZ_succ (c : ℂ) (k : ℕ) (h : 2 + ‖c‖ ≤ ‖critZ c k‖) :
    2 * ‖critZ c k‖ ≤ ‖critZ c (k + 1)‖ := by
  rw [critZ_succ]
  exact critZGrowth_two_mul_le_norm_pMap c _ h

/-- The far region `2 + ‖c‖ ≤ ‖·‖` is forward invariant for `pMap c`. -/
lemma critZGrowth_two_add_le (c : ℂ) (k : ℕ) (h : 2 + ‖c‖ ≤ ‖critZ c k‖) (n : ℕ) :
    2 + ‖c‖ ≤ ‖critZ c (k + n)‖ := by
  have hw := Work.Bottcher.Core.pMap_norm_iterate_ge c (critZ c k) h n
  rwa [pMap_iterate_critZ] at hw

/-- Geometric growth of the far critical orbit: `‖critZ c (k+n)‖ ≥ 2 ^ n ‖critZ c k‖`. -/
lemma critZGrowth_pow_two_mul_le (c : ℂ) (k : ℕ) (h : 2 + ‖c‖ ≤ ‖critZ c k‖) :
    ∀ n : ℕ, (2 : ℝ) ^ n * ‖critZ c k‖ ≤ ‖critZ c (k + n)‖ := by
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
      have hfar : 2 + ‖c‖ ≤ ‖critZ c (k + n)‖ := critZGrowth_two_add_le c k h n
      have hstep : 2 * ‖critZ c (k + n)‖ ≤ ‖critZ c ((k + n) + 1)‖ :=
        critZGrowth_two_mul_le_norm_critZ_succ c (k + n) hfar
      have h1 : (2 : ℝ) ^ (n + 1) * ‖critZ c k‖ = 2 * ((2 : ℝ) ^ n * ‖critZ c k‖) := by
        rw [pow_succ]; ring
      rw [h1, show k + (n + 1) = (k + n) + 1 by omega]
      linarith

/-- Consequence of the geometric growth: `1 / ‖critZ c (k+n)‖²` decays like `4^{-n}`. -/
lemma critZGrowth_inv_sq_le (c : ℂ) {k : ℕ} {R : ℝ} (hRpos : 0 < R)
    (hk : R ≤ ‖critZ c k‖) (h : 2 + ‖c‖ ≤ ‖critZ c k‖) (n : ℕ) :
    1 / ‖critZ c (k + n)‖ ^ 2 ≤ (1 / R ^ 2) * (1 / 4 : ℝ) ^ n := by
  have hZkpos : 0 < ‖critZ c k‖ := lt_of_lt_of_le hRpos hk
  have hpow := critZGrowth_pow_two_mul_le c k h n
  have hApos : 0 < (2 : ℝ) ^ n * ‖critZ c k‖ := by positivity
  have hsq : ((2 : ℝ) ^ n * ‖critZ c k‖) ^ 2 ≤ ‖critZ c (k + n)‖ ^ 2 :=
    pow_le_pow_left₀ (le_of_lt hApos) hpow 2
  have hinv : 1 / ‖critZ c (k + n)‖ ^ 2 ≤ 1 / ((2 : ℝ) ^ n * ‖critZ c k‖) ^ 2 :=
    one_div_le_one_div_of_le (by positivity) hsq
  have hid : 1 / ((2 : ℝ) ^ n * ‖critZ c k‖) ^ 2
      = (1 / 4 : ℝ) ^ n * (1 / ‖critZ c k‖ ^ 2) := by
    have h2n : ((2 : ℝ) ^ n) ^ 2 = (4 : ℝ) ^ n := by
      rw [← pow_mul, mul_comm, pow_mul]; norm_num
    rw [mul_pow, h2n, one_div, one_div, mul_inv, inv_pow]
    norm_num
  have hR2 : 1 / ‖critZ c k‖ ^ 2 ≤ 1 / R ^ 2 :=
    one_div_le_one_div_of_le (by positivity) (pow_le_pow_left₀ (le_of_lt hRpos) hk 2)
  calc 1 / ‖critZ c (k + n)‖ ^ 2 ≤ 1 / ((2 : ℝ) ^ n * ‖critZ c k‖) ^ 2 := hinv
    _ = (1 / 4 : ℝ) ^ n * (1 / ‖critZ c k‖ ^ 2) := hid
    _ ≤ (1 / 4 : ℝ) ^ n * (1 / R ^ 2) :=
        mul_le_mul_of_nonneg_left hR2 (by positivity)
    _ = (1 / R ^ 2) * (1 / 4 : ℝ) ^ n := by ring

/-- Route: `‖critZ c (k+1)‖ ≥ ‖critZ c k‖^4 / 2` (`Work.Bottcher.Core.pMap_norm_step`) while
`2 + ‖c‖ ≤ ‖critZ c k‖`.  With `v k = 1 / ‖critZ c k‖^2` one has `v (k+1) ≤ 4 * v k^4`, so
`v (N+n) ≤ 4^{-n} * v N`; the value at `N` is bounded on a small ball around `c₀` by continuity of
`critZ · N`. -/
theorem norm_critZ_growth {N : ℕ} {c₀ : ℂ}
    (hfar : Work.NAKANE.farRadius (‖c₀‖ + 1) < ‖Work.NAKANE2.critZ c₀ N‖) :
    ∃ δ > 0, ∃ M : ℝ, 0 < M ∧ ∀ c : ℂ, ‖c - c₀‖ < δ → ∀ n : ℕ,
      1 / ‖Work.NAKANE2.critZ c (N + n)‖ ^ 2 ≤ M * (1 / 4 : ℝ) ^ n := by
  set R : ℝ := Work.NAKANE.farRadius (‖c₀‖ + 1) with hRdef
  have hRpos : 0 < R := Work.NAKANE.pos_farRadius _
  have hR3 : ‖c₀‖ + 3 ≤ R := by
    have h := critZGrowth_farRadius_ge (‖c₀‖ + 1) (by positivity)
    rw [hRdef]
    linarith
  have hε : 0 < ‖critZ c₀ N‖ - R := by linarith
  obtain ⟨δ₁, hδ₁pos, hδ₁⟩ := Metric.continuousAt_iff.mp (critZGrowth_continuous N).continuousAt
    (‖critZ c₀ N‖ - R) hε
  refine ⟨min δ₁ 1, lt_min hδ₁pos one_pos, 1 / R ^ 2, by positivity, ?_⟩
  intro c hc n
  have hc₁ : dist c c₀ < δ₁ := by
    rw [dist_eq_norm]
    exact lt_of_lt_of_le hc (min_le_left _ _)
  have hc₂ : ‖c - c₀‖ < 1 := lt_of_lt_of_le hc (min_le_right _ _)
  have hZc₀' := hδ₁ hc₁
  rw [Complex.dist_eq] at hZc₀'
  have hZc : R ≤ ‖critZ c N‖ := by
    have hrt : ‖critZ c₀ N‖ ≤ ‖critZ c N - critZ c₀ N‖ + ‖critZ c N‖ := by
      have h := norm_add_le (critZ c₀ N - critZ c N) (critZ c N)
      rw [sub_add_cancel] at h
      rwa [norm_sub_rev] at h
    linarith
  have hcnorm : ‖c‖ ≤ ‖c₀‖ + 1 := by
    have h1 : ‖c‖ ≤ ‖c - c₀‖ + ‖c₀‖ := by
      have h := norm_add_le (c - c₀) c₀
      rwa [sub_add_cancel] at h
    linarith
  have hk : 2 + ‖c‖ ≤ ‖critZ c N‖ := by linarith
  exact critZGrowth_inv_sq_le c hRpos hZc hk n

end Work.NAKANE2.Far
