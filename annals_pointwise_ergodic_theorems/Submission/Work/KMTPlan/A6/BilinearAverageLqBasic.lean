/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import Submission.Commons.Analysis.Moment.rpow_ave_mono
import Submission.Work.Analysis.Concentration.Corollary1Weak
import Submission.Work.Analysis.Paraproduct.ArithBilinearMain

-- v4.35 port: restore the v4.34 instance-unification behaviour (respectTransparency) in this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Elementary bounds for the bilinear arithmetic average on `ℤ/Qℤ`

This file collects the *unconditional, elementary* part of the `L² × L² → L^q` theory of the
bilinear arithmetic average `A(f,g)(x) = Q⁻¹ ∑_y f (x - y) g (x - P y)`
(`Work.Analysis.Concentration.polyBilinearAverageZMod X P Q`), for use by the assembly of
`Work.KMTPlan.A6.BilinearAverageLqUniform`:

* `LpNormZMod_le_two` : the normalized `L^p` norms on `ℤ/Qℤ` are **decreasing in `p` on
  `[1,2]`** (`‖f‖_{L^q} ≤ ‖f‖_{L²}` for `1 ≤ q ≤ 2`), by Hölder's inequality;
* `bilinearAverageL2_le` : the **`L²` bound** `‖A(f,g)‖_{L²} ≤ ‖f‖_{L²}‖g‖_{L²}`, valid for
  *every* `Q` and every polynomial `P`, with constant `1`.  This is the paper's estimate
  (avg-1) at `s = 1`, i.e. `bilinAverage_lq_fiber` applied to the trivial fibre bound
  `FiberLpBound P Q 1 1` (which is `∑_y h(y) = Q`);
* `bilinearAverageLq_of_le_two` : consequently the target estimate
  `‖A(f,g)‖_{L^q} ≤ ‖f‖_{L²}‖g‖_{L²}` holds with constant `1` for every `q ≤ 2`,
  uniformly in `Q`.
-/

set_option autoImplicit false

namespace Work.KMTPlan.A6

open Work.Analysis.Concentration

noncomputable section

/-- The normalized `L^p` norm on `ℤ/Qℤ` as a power mean of the pointwise norms. -/
theorem LpNormZMod_eq_ave (Q : ℕ) [NeZero Q] (p : ℝ) (u : ZMod Q → ℂ) :
    LpNormZMod Q p u = ((∑ x : ZMod Q, ‖u x‖ ^ p) / (Q : ℝ)) ^ (1 / p) := by
  rw [LpNormZMod,
    show (Q : ℝ)⁻¹ * ∑ x : ZMod Q, ‖u x‖ ^ p
        = (∑ x : ZMod Q, ‖u x‖ ^ p) / (Q : ℝ) from by rw [div_eq_mul_inv, mul_comm]]

/-- **The normalized `L^p` norms on `ℤ/Qℤ` increase with the exponent** (`0 < q ≤ p`):
`‖f‖_{L^q(ℤ/Qℤ)} ≤ ‖f‖_{L^p(ℤ/Qℤ)}`.  This is the power-mean inequality for the normalized
counting measure (`Commons.Analysis.Moment.rpow_ave_mono`). -/
theorem LpNormZMod_le_of_le {Q : ℕ} [NeZero Q] {q p : ℝ} (hq : 0 < q) (hqp : q ≤ p)
    (u : ZMod Q → ℂ) : LpNormZMod Q q u ≤ LpNormZMod Q p u := by
  have hcard : 0 < Fintype.card (ZMod Q) := by
    rw [ZMod.card]; exact Nat.pos_of_ne_zero (NeZero.ne Q)
  have h := Commons.Analysis.Moment.rpow_ave_mono (ι := ZMod Q) (Y := fun x => ‖u x‖)
    hcard (fun x => norm_nonneg _) hq hqp
  have hcard' : ((Fintype.card (ZMod Q) : ℕ) : ℝ) = (Q : ℝ) := by rw [ZMod.card]
  rw [hcard'] at h
  rwa [LpNormZMod_eq_ave, LpNormZMod_eq_ave]

/-- The normalized `L^p` norms on `ℤ/Qℤ` are **decreasing on `[1,2]`**: for `1 ≤ q ≤ 2`,
`‖f‖_{L^q(ℤ/Qℤ)} ≤ ‖f‖_{L²(ℤ/Qℤ)}`. -/
theorem LpNormZMod_le_two {Q : ℕ} [NeZero Q] {q : ℝ} (hq1 : 1 ≤ q) (hq2 : q ≤ 2)
    (u : ZMod Q → ℂ) : LpNormZMod Q q u ≤ LpNormZMod Q 2 u :=
  LpNormZMod_le_of_le (lt_of_lt_of_le zero_lt_one hq1) hq2 u

/-- **The `L²` bilinear bound**: for every modulus `Q` and every polynomial `P`,
`‖A(f,g)‖_{L²(ℤ/Qℤ)} ≤ ‖f‖_{L²} ‖g‖_{L²}` with constant `1`.

This is the paper's (avg-1) at `s = 1`: the fibre counting function satisfies the trivial
concentration bound `FiberLpBound P Q 1 1` (its `L¹` norm is `1`, since `∑_y h(y) = Q`), and
`bilinAverage_lq_fiber` converts it into the `L² × L² → L²` estimate. -/
theorem bilinearAverageL2_le (P : Polynomial ℤ) (Q : ℕ) [NeZero Q] (f g : ZMod Q → ℂ) :
    LpNormZMod Q 2 (polyBilinearAverageZMod Polynomial.X P Q f g)
      ≤ LpNormZMod Q 2 f * LpNormZMod Q 2 g := by
  have hQ : (0 : ℝ) < Q := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne Q)
  have hfib : LpNormZMod Q 1 (fun m => (polyFiberCard P Q m : ℂ)) ≤ 1 := by
    rw [LpNormZMod_one_eq]
    simp only [Complex.norm_natCast]
    rw [← Nat.cast_sum, fiber_card_sum, inv_mul_cancel₀ (ne_of_gt hQ)]
  have h := Work.Analysis.Paraproduct.bilinAverage_lq_fiber P Q (s := 1) le_rfl hfib f g
  rw [show (2 : ℝ) * 1 = 2 by norm_num, Real.sqrt_one, one_mul] at h
  exact h

/-- **The target estimate in the range `q ≤ 2`**: for `1 ≤ q ≤ 2` the bilinear arithmetic
average satisfies `‖A(f,g)‖_{L^q(ℤ/Qℤ)} ≤ ‖f‖_{L²}‖g‖_{L²}` for *every* `Q`, with constant
`1` (so a fortiori for every `P`). -/
theorem bilinearAverageLq_le_two (P : Polynomial ℤ) {q : ℝ} (hq1 : 1 ≤ q) (hq2 : q ≤ 2) :
    ∀ (Q : ℕ) [NeZero Q] (f g : ZMod Q → ℂ),
      LpNormZMod Q q (polyBilinearAverageZMod Polynomial.X P Q f g)
        ≤ 1 * LpNormZMod Q 2 f * LpNormZMod Q 2 g := by
  intro Q _ f g
  refine (LpNormZMod_le_two hq1 hq2 _).trans ?_
  rw [one_mul]
  exact bilinearAverageL2_le P Q f g


/-- The trivial maximal-fibre bound: every fibre of `P` modulo `Q` has at most `Q` elements. -/
theorem fiberMaxBound_self (P : Polynomial ℤ) (Q : ℕ) [NeZero Q] : FiberMaxBound P Q Q := by
  intro y
  have h : polyFiberCard P Q y ≤ Q := by
    unfold polyFiberCard
    calc (Finset.univ.filter (fun x : ZMod Q => polyEvalZMod P Q x = y)).card
        ≤ (Finset.univ : Finset (ZMod Q)).card :=
          Finset.card_le_card (Finset.filter_subset _ _)
      _ = Q := by simp [ZMod.card]
  exact_mod_cast h

/-- **The modulus-dependent bilinear bound**: for every *fixed* modulus `Q` and every `q ≥ 1`
the bilinear average is bounded `L² × L² → L^q` with a constant depending on `Q`
(namely `max 1 (Q^{1 - 1/(q/2)})^{1/2}`); no hypothesis on `P` beyond non-vanishing of the
modulus is needed.

This is the form in which the paper's applications use the arithmetic bilinear estimate (only a
single large but fixed `Q` is ever needed; see the footnote in §4 of the paper); the *uniform in
`Q`* form is `Work.KMTPlan.A6.BilinearAverageLqUniform`, which requires the deep inputs of §10. -/
theorem bilinearAverageLq_fixed (P : Polynomial ℤ) (Q : ℕ) [NeZero Q] {q : ℝ} (hq : 1 ≤ q) :
    ∃ C : ℝ, 0 < C ∧ BilinearAverageLq P Q q C := by
  by_cases hq2 : q ≤ 2
  · exact ⟨1, one_pos, fun f g => bilinearAverageLq_le_two P hq hq2 Q f g⟩
  · have hq2' : 2 < q := lt_of_not_ge hq2
    have hQpos : (0 : ℝ) < Q := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne Q)
    have hs1 : 1 ≤ q / 2 := by
      rw [one_le_div (by norm_num : (0 : ℝ) < 2)]
      linarith
    have hCpos : (0 : ℝ) < Q ^ (1 - 1 / (q / 2)) := Real.rpow_pos_of_pos hQpos _
    refine ⟨Real.sqrt (Q ^ (1 - 1 / (q / 2))), Real.sqrt_pos.mpr hCpos, fun f g => ?_⟩
    have hfb : FiberLpBound P Q (q / 2) (Q ^ (1 - 1 / (q / 2))) :=
      fiberLpBound_of_fiberMaxBound (fiberMaxBound_self P Q) hs1
    have hLp : LpNormZMod Q (q / 2) (fun m => (polyFiberCard P Q m : ℂ))
        ≤ Q ^ (1 - 1 / (q / 2)) :=
      LpNormZMod_fiberFun_le (r := q / 2) (C := Q ^ (1 - 1 / (q / 2)))
        (by linarith) hCpos.le hfb
    have h := Work.Analysis.Paraproduct.bilinearAverageLq_of_fiber P Q (s := q / 2) hs1 hLp
    have h' : BilinearAverageLq P Q q (Real.sqrt (Q ^ (1 - 1 / (q / 2)))) := by
      simpa [show 2 * (q / 2) = q by ring] using h
    exact h' f g

end

end Work.KMTPlan.A6
