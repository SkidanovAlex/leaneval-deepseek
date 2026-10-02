/-
Copyright: subproject `Submission/Work/PARIMPL2/` of `mandelbar_not_path_connected`.

# `Work.PARIMPL2.Lavaurs.deep_level_bound` — the deep level bound with bounded height

This is the *restricted* uniform transient bound requested by `Work.PARIMPL2.Lavaurs.hLB_H`
(item (1) of the lead's directive): on the *deep* part of the petal, i.e. for `z ∈ fl.Pa` with

  `A.N < Re (w0 P z) ≤ M`   and   `|Im (φa z)| ≤ H`,

the attracting level `Re (φa z)` is bounded above by a constant `M'` depending only on
`(P, fl, A, M, H)`.

Note the depth hypothesis `A.N < Re (w0 P z)`: unlike the *unrestricted* transient bound it places
`z` on the region where the asymptotic `AttrCompare.asymp` is available, and there it is exactly
what rules out the counterexample discussed in `hLB_H` (a point at bounded distance from a
preimage `z_* ≠ z₁` of `z₁`, whose `F`-image is very deep): at depth `> A.N` the asymptotic
`φa z = w0 z − κ₀ log (w0 z) + sa + O(1/Re w0 z)` forces `Re (φa z)` to be bounded whenever
`|Im (φa z)|` is.

## Proof route

From `AttrCompare.asymp` with `w := w0 P z`, `h := φa z`, the error term `E := h − (w − κ₀ log w + sa)`
satisfies `‖E‖ ≤ K / Re w ≤ K / A.N` (as `Re w > A.N > 0`).  Write `γ := max 0 (−log A.N)`, so that
`−log ‖w‖ ≤ γ` because `‖w‖ ≥ Re w > A.N`.  Then

* `|Re (log w)| ≤ γ + log (2 + ‖w‖)` and `|Im (log w)| ≤ π`   (`dlb_log_re_abs_le`, `dlb_abs_im_log_le_pi`);
* hence the *height* of `w` obeys a self-referential *logarithmic* bound
  `|Im w| ≤ H + ‖sa‖ + K/A.N + ‖κ₀‖(γ + log (2+‖w‖) + π)`   (`dlb_abs_im_le_of_asymp`);
* with `Re w ≤ M` this bounds `‖w‖ ≤ Y + ‖κ₀‖ log (2+‖w‖)`, and a `log x ≤ 2√x` bootstrap
  (`Work.FlowerGlue2.bdtb_max_log_le_of_self_bound`) turns it into a genuine constant bound
  `‖w‖ ≤ C`   (`dlb_norm_le_of_self_log`);
* finally `Re h = Re (w − κ₀ log w + sa) + Re E ≤ Re w + ‖κ₀‖(γ + log (2+C) + π) + ‖sa‖ + K/A.N`
  (`dlb_re_le_of_asymp`).

The `M'` produced is `M + ‖sa‖ + K/A.N + ‖κ₀‖(γ + log (2+C) + π) + 1`, an explicit constant.
-/
import Mathlib
import Submission.Work.PARIMPL2.Lavaurs.Defs
import Submission.Work.FlowerGlue2.Defs
import Submission.Work.FlowerGlue2.AttrNorm
import Submission.Work.FlowerGlue2.box_deep_of_transient_bound

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

open scoped Topology

namespace Work.PARIMPL2.Lavaurs

/-! ## 1. The elementary bounds on `log` and on `κ log w` -/

/-- The `ℓ¹`-bound for four real summands. -/
theorem dlb_abs_add_four_le (a b c d : ℝ) : |a + b + c + d| ≤ |a| + |b| + |c| + |d| := by
  have h1 := abs_add_le (a + b + c) d
  have h2 := abs_add_le (a + b) c
  have h3 := abs_add_le a b
  linarith

/-- For `Re w > N₀ > 0`, the real part `log ‖w‖` of `log w` is bounded by
`max 0 (−log N₀) + log (2 + ‖w‖)`: above by monotonicity of `log` (and `2 + ‖w‖ ≥ ‖w‖`), below
because `‖w‖ ≥ Re w > N₀`.  (Note that `log (2 + ‖w‖)` alone does **not** bound `−log ‖w‖` from
below; this is why the `max 0 (−log N₀)` term is present.) -/
theorem dlb_log_re_abs_le {N₀ : ℝ} (hN₀ : 0 < N₀) {w : ℂ} (hw : N₀ < w.re) :
    |(Complex.log w).re| ≤ max 0 (-(Real.log N₀)) + Real.log (2 + ‖w‖) := by
  have hwnorm : N₀ ≤ ‖w‖ := le_trans hw.le (Complex.re_le_norm w)
  have hwnormpos : 0 < ‖w‖ := lt_of_lt_of_le hN₀ hwnorm
  have h2 : -(Real.log N₀) ≤ max 0 (-(Real.log N₀)) := le_max_right _ _
  have h4 : 0 ≤ max 0 (-(Real.log N₀)) := le_max_left _ _
  have h5 : 0 ≤ Real.log (2 + ‖w‖) := Real.log_nonneg (by linarith [norm_nonneg w])
  rw [Complex.log_re]
  rcases lt_or_ge 0 (Real.log ‖w‖) with h | h
  · rw [abs_of_nonneg h.le]
    have h3 : Real.log ‖w‖ ≤ Real.log (2 + ‖w‖) := Real.log_le_log hwnormpos (by linarith)
    linarith
  · rw [abs_of_nonpos h]
    have h3 : Real.log N₀ ≤ Real.log ‖w‖ := Real.log_le_log hN₀ hwnorm
    linarith

/-- The imaginary part of `log w` is the argument of `w`, hence at most `π` in modulus. -/
theorem dlb_abs_im_log_le_pi (w : ℂ) : |(Complex.log w).im| ≤ Real.pi := by
  rw [Complex.log_im]
  exact Complex.abs_arg_le_pi w

/-! ## 2. The height bound for `w0`

From the asymptotic `h = w − κ log w + sa + O(1/Re w)` and a bounded `|Im h|`, the height `|Im w|`
obeys a logarithmic self-bound: the `Im` of `w` is `Im h − Im sa − Im E + Im (κ log w)`, and
`log w` has real part at most `γ + log (2+‖w‖)` in modulus and imaginary part at most `π`. -/

theorem dlb_abs_im_le_of_asymp {κ sa : ℂ} {K N₀ H : ℝ} (hN₀ : 0 < N₀) (hK : 0 ≤ K)
    {w h : ℂ} (hw : N₀ < w.re) (him : |h.im| ≤ H)
    (happrox : ‖h - ((w - κ * Complex.log w) + sa)‖ ≤ K / w.re) :
    |w.im| ≤ H + ‖sa‖ + K / N₀
      + ‖κ‖ * (max 0 (-(Real.log N₀)) + Real.log (2 + ‖w‖) + Real.pi) := by
  have hwr : 0 < w.re := lt_trans hN₀ hw
  set E : ℂ := h - ((w - κ * Complex.log w) + sa) with hE
  have hEim : |E.im| ≤ K / w.re := le_trans (Complex.abs_im_le_norm E) happrox
  have hKdiv : K / w.re ≤ K / N₀ := div_le_div_of_nonneg_left hK hN₀ hw.le
  have hlogre := dlb_log_re_abs_le hN₀ hw
  have hlogim := dlb_abs_im_log_le_pi w
  have hlogsum : |(Complex.log w).re| + |(Complex.log w).im| ≤
      max 0 (-(Real.log N₀)) + Real.log (2 + ‖w‖) + Real.pi := by linarith
  have hkim : |(κ * Complex.log w).im| ≤
      ‖κ‖ * (max 0 (-(Real.log N₀)) + Real.log (2 + ‖w‖) + Real.pi) :=
    le_trans (Work.FlowerGlue2.bdtb_abs_im_mul_le κ (Complex.log w))
      (mul_le_mul_of_nonneg_left hlogsum (norm_nonneg κ))
  have hwim : w.im = h.im + (-(sa.im)) + (-(E.im)) + (κ * Complex.log w).im := by
    have hh : h = ((w - κ * Complex.log w) + sa) + E := by rw [hE]; ring
    rw [hh]
    simp only [Complex.add_im, Complex.sub_im]
    ring
  have h4 := dlb_abs_add_four_le h.im (-(sa.im)) (-(E.im)) ((κ * Complex.log w).im)
  have hsa_im : |sa.im| ≤ ‖sa‖ := Complex.abs_im_le_norm sa
  calc |w.im| = |h.im + (-(sa.im)) + (-(E.im)) + (κ * Complex.log w).im| := by rw [hwim]
    _ ≤ |h.im| + |sa.im| + |E.im| + |(κ * Complex.log w).im| := by
          simpa only [abs_neg] using h4
    _ ≤ H + ‖sa‖ + K / w.re
          + ‖κ‖ * (max 0 (-(Real.log N₀)) + Real.log (2 + ‖w‖) + Real.pi) := by
          linarith [him, hsa_im, hEim, hkim]
    _ ≤ H + ‖sa‖ + K / N₀
          + ‖κ‖ * (max 0 (-(Real.log N₀)) + Real.log (2 + ‖w‖) + Real.pi) := by linarith

/-! ## 3. The bootstrap `‖w‖ ≤ Y + ‖κ‖ log (2 + ‖w‖) ⟹ ‖w‖ ≤ C` -/

theorem dlb_norm_le_of_self_log {κ : ℂ} {X : ℝ} {w : ℂ}
    (h : ‖w‖ ≤ X + ‖κ‖ * Real.log (2 + ‖w‖)) :
    ‖w‖ ≤ max 1 (max 0 X + ‖κ‖ * Real.log 3
      + ‖κ‖ * Real.log (2 * (max 0 X + ‖κ‖ * Real.log 3 + 2 * ‖κ‖ ^ 2 + 1))) := by
  by_cases h1 : ‖w‖ < 1
  · exact le_trans h1.le (le_max_left _ _)
  · push Not at h1
    have hwpos : 0 < ‖w‖ := lt_of_lt_of_le zero_lt_one h1
    have hlog3 : Real.log (2 + ‖w‖) ≤ Real.log ‖w‖ + Real.log 3 := by
      have h2 : 2 + ‖w‖ ≤ 3 * ‖w‖ := by linarith
      have h3 : 0 < 2 + ‖w‖ := by linarith
      calc Real.log (2 + ‖w‖) ≤ Real.log (3 * ‖w‖) := Real.log_le_log h3 h2
        _ = Real.log 3 + Real.log ‖w‖ := Real.log_mul (by norm_num) (ne_of_gt hwpos)
        _ = Real.log ‖w‖ + Real.log 3 := by ring
    have hlogw0 : 0 ≤ Real.log ‖w‖ := Real.log_nonneg h1
    have hXle : X ≤ max 0 X := le_max_right _ _
    have hself : ‖w‖ ≤ (max 0 X + ‖κ‖ * Real.log 3) + ‖κ‖ * max 0 (Real.log ‖w‖) := by
      have h2 : ‖w‖ ≤ X + ‖κ‖ * (Real.log ‖w‖ + Real.log 3) := by
        have := mul_le_mul_of_nonneg_left hlog3 (norm_nonneg κ)
        linarith
      have h3 : X + ‖κ‖ * (Real.log ‖w‖ + Real.log 3)
          ≤ (max 0 X + ‖κ‖ * Real.log 3) + ‖κ‖ * max 0 (Real.log ‖w‖) := by
        rw [max_eq_right hlogw0]
        nlinarith [mul_le_mul_of_nonneg_left hXle (norm_nonneg κ)]
      linarith
    have hA0 : 0 ≤ max 0 X + ‖κ‖ * Real.log 3 := by
      have h2 : 0 ≤ max 0 X := le_max_left _ _
      have h3 : 0 ≤ Real.log 3 := Real.log_nonneg (by norm_num)
      nlinarith [norm_nonneg κ]
    have hb := Work.FlowerGlue2.bdtb_max_log_le_of_self_bound (T := ‖w‖)
      (A := max 0 X + ‖κ‖ * Real.log 3) (b := ‖κ‖) (norm_nonneg w) hA0 (norm_nonneg κ) hself
    have hfin : ‖w‖ ≤ max 0 X + ‖κ‖ * Real.log 3
        + ‖κ‖ * Real.log (2 * (max 0 X + ‖κ‖ * Real.log 3 + 2 * ‖κ‖ ^ 2 + 1)) := by
      have h2 := mul_le_mul_of_nonneg_left hb (norm_nonneg κ)
      linarith [hself, h2]
    exact le_trans hfin (le_max_right _ _)

/-! ## 4. The level bound from a constant bound on `‖w‖` -/

theorem dlb_re_le_of_asymp {κ sa : ℂ} {K M H N₀ C : ℝ} (hN₀ : 0 < N₀) (hK : 0 ≤ K)
    {w h : ℂ} (hw : N₀ < w.re) (hwM : w.re ≤ M) (him : |h.im| ≤ H)
    (happrox : ‖h - ((w - κ * Complex.log w) + sa)‖ ≤ K / w.re) (hC : ‖w‖ ≤ C) :
    h.re ≤ M + ‖sa‖ + K / N₀
      + ‖κ‖ * (max 0 (-(Real.log N₀)) + Real.log (2 + C) + Real.pi) + 1 := by
  set E : ℂ := h - ((w - κ * Complex.log w) + sa) with hE
  have hEre : |E.re| ≤ K / w.re := le_trans (Complex.abs_re_le_norm E) happrox
  have hKdiv : K / w.re ≤ K / N₀ := div_le_div_of_nonneg_left hK hN₀ hw.le
  have hlogre := dlb_log_re_abs_le hN₀ hw
  have hlogim := dlb_abs_im_log_le_pi w
  have hlogC : Real.log (2 + ‖w‖) ≤ Real.log (2 + C) :=
    Real.log_le_log (by positivity) (by linarith)
  have hsum : |(Complex.log w).re| + |(Complex.log w).im| ≤
      max 0 (-(Real.log N₀)) + Real.log (2 + C) + Real.pi := by linarith
  have hkim : |(κ * Complex.log w).re| ≤
      ‖κ‖ * (max 0 (-(Real.log N₀)) + Real.log (2 + C) + Real.pi) :=
    le_trans (Work.FlowerGlue2.bdtb_abs_re_mul_le κ (Complex.log w))
      (mul_le_mul_of_nonneg_left hsum (norm_nonneg κ))
  have hre_eq : h.re = (w - κ * Complex.log w + sa).re + E.re := by
    have hh : h = ((w - κ * Complex.log w) + sa) + E := by rw [hE]; ring
    rw [hh, Complex.add_re]
  have hmain : (w - κ * Complex.log w + sa).re ≤
      M + ‖κ‖ * (max 0 (-(Real.log N₀)) + Real.log (2 + C) + Real.pi) + ‖sa‖ := by
    have hsub : (w - κ * Complex.log w + sa).re = w.re - (κ * Complex.log w).re + sa.re := by
      simp only [Complex.add_re, Complex.sub_re]
    have h2 : -(κ * Complex.log w).re ≤
        ‖κ‖ * (max 0 (-(Real.log N₀)) + Real.log (2 + C) + Real.pi) :=
      le_trans (neg_le_abs _) hkim
    have h3 : sa.re ≤ ‖sa‖ := Complex.re_le_norm sa
    linarith
  have hEre' : E.re ≤ K / N₀ := by linarith [hEre, hKdiv, le_abs_self E.re]
  linarith [hre_eq, hmain, hEre']

/-! ## 5. The theorem -/

theorem deep_level_bound {c₀ : ℂ} {d : Work.EL.RootParabolic c₀} (P : Work.PARIMPL.ParNormal d)
    (fl : Work.FatouCoordFix.ParabolicFlowerFix (Work.PARIMPL.Ft c₀) (Work.PARIMPL.gtc c₀) d.z₁)
    (A : Work.FlowerGlue2.AttrCompare P fl.Pa fl.φa) (M H : ℝ) :
    ∃ M' : ℝ, ∀ z ∈ fl.Pa, A.N < (Work.PARIMPL2.w0 P z).re → (Work.PARIMPL2.w0 P z).re ≤ M →
      |(fl.φa z).im| ≤ H → (fl.φa z).re ≤ M' := by
  have hN₀ : 0 < A.N := A.N_pos
  have hK : 0 ≤ A.K := A.K_nonneg
  have hb0 : 0 ≤ ‖P.κ c₀‖ := norm_nonneg _
  have hlog3 : 0 ≤ Real.log 3 := Real.log_nonneg (by norm_num)
  let γ : ℝ := max 0 (-(Real.log A.N))
  let Y : ℝ := M + H + ‖A.sa‖ + A.K / A.N + ‖P.κ c₀‖ * (γ + Real.pi + Real.log 3)
  let C : ℝ := max 1 (max 0 Y + ‖P.κ c₀‖ * Real.log 3
    + ‖P.κ c₀‖ * Real.log (2 * (max 0 Y + ‖P.κ c₀‖ * Real.log 3 + 2 * ‖P.κ c₀‖ ^ 2 + 1)))
  refine ⟨M + ‖A.sa‖ + A.K / A.N + ‖P.κ c₀‖ * (γ + Real.log (2 + C) + Real.pi) + 1, ?_⟩
  intro z hz hdeep hle hH
  rw [show Work.PARIMPL2.w0 P z = Work.FlowerGlue2.w0 P z from rfl] at hdeep hle
  have hzne : z ≠ d.z₁ := by
    intro hz₁
    rw [hz₁] at hdeep
    simp only [Work.FlowerGlue2.w0_apply, sub_self, div_zero, Complex.zero_re] at hdeep
    linarith
  have hasymp : ‖fl.φa z
      - ((Work.FlowerGlue2.w0 P z - P.κ c₀ * Complex.log (Work.FlowerGlue2.w0 P z)) + A.sa)‖
      ≤ A.K / (Work.FlowerGlue2.w0 P z).re := by
    have h := A.asymp z hz hzne hdeep
    simpa only [Work.FatouCoord.approxCoord] using h
  have himb := dlb_abs_im_le_of_asymp hN₀ hK hdeep hH hasymp
  have hnorm_self : ‖Work.FlowerGlue2.w0 P z‖
      ≤ Y + ‖P.κ c₀‖ * Real.log (2 + ‖Work.FlowerGlue2.w0 P z‖) := by
    have h1 : ‖Work.FlowerGlue2.w0 P z‖
        ≤ |(Work.FlowerGlue2.w0 P z).re| + |(Work.FlowerGlue2.w0 P z).im| :=
      Complex.norm_le_abs_re_add_abs_im _
    have hrepos : 0 < (Work.FlowerGlue2.w0 P z).re := lt_trans hN₀ hdeep
    have h2 : |(Work.FlowerGlue2.w0 P z).re| = (Work.FlowerGlue2.w0 P z).re := abs_of_pos hrepos
    have h4 : ‖Work.FlowerGlue2.w0 P z‖ ≤ M + H + ‖A.sa‖ + A.K / A.N
        + ‖P.κ c₀‖ * (γ + Real.log (2 + ‖Work.FlowerGlue2.w0 P z‖) + Real.pi) := by
      linarith [h1, h2, himb, hle]
    have h5 : ‖P.κ c₀‖ * (γ + Real.log (2 + ‖Work.FlowerGlue2.w0 P z‖) + Real.pi)
        ≤ ‖P.κ c₀‖ * (γ + Real.pi + Real.log 3)
          + ‖P.κ c₀‖ * Real.log (2 + ‖Work.FlowerGlue2.w0 P z‖) := by
      have h6 : γ + Real.log (2 + ‖Work.FlowerGlue2.w0 P z‖) + Real.pi
          ≤ (γ + Real.pi + Real.log 3) + Real.log (2 + ‖Work.FlowerGlue2.w0 P z‖) := by linarith
      calc ‖P.κ c₀‖ * (γ + Real.log (2 + ‖Work.FlowerGlue2.w0 P z‖) + Real.pi)
          ≤ ‖P.κ c₀‖ * ((γ + Real.pi + Real.log 3)
              + Real.log (2 + ‖Work.FlowerGlue2.w0 P z‖)) :=
            mul_le_mul_of_nonneg_left h6 hb0
        _ = ‖P.κ c₀‖ * (γ + Real.pi + Real.log 3)
              + ‖P.κ c₀‖ * Real.log (2 + ‖Work.FlowerGlue2.w0 P z‖) := by ring
    have hY : Y = M + H + ‖A.sa‖ + A.K / A.N
        + ‖P.κ c₀‖ * (γ + Real.pi + Real.log 3) := rfl
    linarith [h4, h5, hY]
  have hnormC : ‖Work.FlowerGlue2.w0 P z‖ ≤ C :=
    dlb_norm_le_of_self_log (κ := P.κ c₀) (X := Y) hnorm_self
  exact dlb_re_le_of_asymp (κ := P.κ c₀) (sa := A.sa) (K := A.K) (M := M) (H := H)
    (N₀ := A.N) (C := C) hN₀ hK hdeep hle hH hasymp hnormC

end Work.PARIMPL2.Lavaurs
