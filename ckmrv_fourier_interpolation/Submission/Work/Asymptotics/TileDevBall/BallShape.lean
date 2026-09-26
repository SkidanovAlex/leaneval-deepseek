/-
# The "ball shape" `BBdd` and its calculus

For the tile deviation bound on the cusp-`0` tile `E = KEpsilon` one needs bounds for
two-variable expressions `F w ζ`, where `w ∈ E` and `ζ` ranges over the ball of radius `29/20`
about `σ = S • w` with `3 ≤ Im ζ` (the hypotheses of the tile analysis).

`BBdd c d F` records the bound

  `‖F w ζ‖ ≤ C (scale w)^N exp (c · Im (S • w)) exp (d · Im ζ)`

for such pairs `(w, ζ)`, with `C, N` existential.  The calculus is closed under products
(additive exponents), sums (max of exponents), scalar multiples and weakening of the exponents.

The point of the two exponents is that the `ζ`-atoms in the region carry a factor
`e^{-2π Im ζ}` while the `τ`-atoms at `τ = n +ᵥ w` carry a factor `e^{2π Im (S • w)}`; a product
of the two has `c + d = 0`.  Since the ball constraint gives `Im ζ ≥ Im (S • w) - 29/20`, such a
product is uniformly bounded (`BBdd.reduce`).
-/
import Mathlib
import Submission.Work.Asymptotics.KEpsilon
import Submission.Work.Asymptotics.EBase
import Submission.Work.Asymptotics.KPlusXiDefs
import Submission.Work.Asymptotics.EtailE.Atoms

noncomputable section

open UpperHalfPlane ModularGroup
open scoped MatrixGroups UpperHalfPlane

namespace Work.Asymptotics.TileDevBall

open Work.Kernels

/-- The hypotheses of the ball estimate: `w ∈ E = KEpsilon` and `ζ` in the closed ball of
radius `29/20` about `S • w`, with `3 ≤ Im ζ`. -/
structure Ball (w ζ : ℍ) : Prop where
  hw : w ∈ KEpsilon
  hball : ‖(ζ : ℂ) - ((ModularGroup.S • w : ℍ) : ℂ)‖ ≤ 29 / 20
  him : 3 ≤ ζ.im

namespace Ball

variable {w ζ : ℍ}

lemma S_im_ge_two (h : Ball w ζ) : 2 ≤ (ModularGroup.S • w).im := h.hw.2

lemma S_im_nonneg (h : Ball w ζ) : 0 ≤ (ModularGroup.S • w).im :=
  le_trans (by norm_num) (S_im_ge_two h)

lemma im_pos (h : Ball w ζ) : 0 < ζ.im := lt_of_lt_of_le (by norm_num) h.him

lemma im_ge (h : Ball w ζ) : (ModularGroup.S • w).im - 29 / 20 ≤ ζ.im := by
  have h1 : |ζ.im - (ModularGroup.S • w).im|
      ≤ ‖(ζ : ℂ) - ((ModularGroup.S • w : ℍ) : ℂ)‖ := by
    have h2 := Complex.abs_im_le_norm ((ζ : ℂ) - ((ModularGroup.S • w : ℍ) : ℂ))
    rwa [Complex.sub_im, UpperHalfPlane.coe_im, UpperHalfPlane.coe_im] at h2
  have h2 : |ζ.im - (ModularGroup.S • w).im| ≤ 29 / 20 := le_trans h1 h.hball
  linarith [(abs_le.mp h2).1]

lemma im_le (h : Ball w ζ) : ζ.im ≤ (ModularGroup.S • w).im + 29 / 20 := by
  have h1 : |ζ.im - (ModularGroup.S • w).im|
      ≤ ‖(ζ : ℂ) - ((ModularGroup.S • w : ℍ) : ℂ)‖ := by
    have h2 := Complex.abs_im_le_norm ((ζ : ℂ) - ((ModularGroup.S • w : ℍ) : ℂ))
    rwa [Complex.sub_im, UpperHalfPlane.coe_im, UpperHalfPlane.coe_im] at h2
  have h2 : |ζ.im - (ModularGroup.S • w).im| ≤ 29 / 20 := le_trans h1 h.hball
  linarith [(abs_le.mp h2).2]

lemma one_le_scale (h : Ball w ζ) : 1 ≤ scale w := Work.Kernels.one_le_scale w

lemma scale_pos (h : Ball w ζ) : 0 < scale w := Work.Kernels.scale_pos w

lemma norm_le (h : Ball w ζ) : ‖(ζ : ℂ)‖ ≤ scale w + 29 / 20 := by
  have h1 : ‖(ζ : ℂ)‖ ≤ ‖((ModularGroup.S • w : ℍ) : ℂ)‖
      + ‖(ζ : ℂ) - ((ModularGroup.S • w : ℍ) : ℂ)‖ := by
    have h2 := norm_add_le ((ζ : ℂ) - ((ModularGroup.S • w : ℍ) : ℂ))
      ((ModularGroup.S • w : ℍ) : ℂ)
    have h3 : (ζ : ℂ) - ((ModularGroup.S • w : ℍ) : ℂ) + ((ModularGroup.S • w : ℍ) : ℂ)
        = (ζ : ℂ) := by ring
    rw [h3] at h2
    linarith [h2]
  linarith [h1, EtailE.E_norm_S_le_scale w, h.hball]

/-- `‖ζ‖ ≤ 49/20 · scale w`. -/
lemma norm_le_scaled (h : Ball w ζ) : ‖(ζ : ℂ)‖ ≤ (49 / 20) * scale w := by
  have h1 := h.norm_le
  have h2 := h.one_le_scale
  nlinarith [h1, h2, norm_nonneg (ζ : ℂ)]

lemma exp_le_const_im {c d : ℝ} (h : Ball w ζ) (hd : d ≤ 0) (hcd : c + d ≤ 0) :
    Real.exp (c * (ModularGroup.S • w).im) * Real.exp (d * ζ.im)
      ≤ Real.exp (-(d * (29 / 20))) := by
  have hx : 0 ≤ (ModularGroup.S • w).im := h.S_im_nonneg
  have hy : (ModularGroup.S • w).im - 29 / 20 ≤ ζ.im := h.im_ge
  rw [← Real.exp_add]
  refine Real.exp_le_exp.mpr ?_
  have h1 : d * ζ.im ≤ d * ((ModularGroup.S • w).im - 29 / 20) :=
    mul_le_mul_of_nonpos_left hy hd
  have h2 : (c + d) * (ModularGroup.S • w).im ≤ 0 :=
    mul_nonpos_of_nonpos_of_nonneg (by linarith) hx
  nlinarith [h1, h2]

end Ball

/-! ## The shape -/

/-- `BBdd c d F`: the bound `‖F w ζ‖ ≤ C (scale w)^N e^{c Im (S • w)} e^{d Im ζ}` on the ball. -/
def BBdd (c d : ℝ) (F : ℍ → ℍ → ℂ) : Prop :=
  ∃ C N : ℝ, 0 < C ∧ 0 ≤ N ∧ ∀ (w ζ : ℍ), Ball w ζ →
    ‖F w ζ‖ ≤ C * (scale w) ^ N * Real.exp (c * (ModularGroup.S • w).im)
      * Real.exp (d * ζ.im)

namespace BBdd

variable {c d c1 c2 d1 d2 : ℝ} {F G : ℍ → ℍ → ℂ}

lemma congr {F G : ℍ → ℍ → ℂ} (h : F = G) (hF : BBdd c d F) : BBdd c d G := h ▸ hF

lemma mono {c d c' d' : ℝ} (hc : c ≤ c') (hd : d ≤ d') (h : BBdd c d F) : BBdd c' d' F := by
  obtain ⟨C, N, hC, hN, hb⟩ := h
  refine ⟨C, N, hC, hN, fun w ζ hw => ?_⟩
  refine le_trans (hb w ζ hw) ?_
  have hx : 0 ≤ (ModularGroup.S • w).im := hw.S_im_nonneg
  have hy : 0 ≤ ζ.im := le_of_lt hw.im_pos
  have e1 : Real.exp (c * (ModularGroup.S • w).im) ≤ Real.exp (c' * (ModularGroup.S • w).im) :=
    Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hc hx)
  have e2 : Real.exp (d * ζ.im) ≤ Real.exp (d' * ζ.im) :=
    Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hd hy)
  have h0 : 0 ≤ C * (scale w) ^ N :=
    mul_nonneg hC.le (Real.rpow_nonneg (hw.scale_pos).le N)
  calc C * (scale w) ^ N * Real.exp (c * (ModularGroup.S • w).im) * Real.exp (d * ζ.im)
      ≤ C * (scale w) ^ N * Real.exp (c' * (ModularGroup.S • w).im)
          * Real.exp (d * ζ.im) := by
        refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left e1 h0) (Real.exp_pos _).le
    _ ≤ C * (scale w) ^ N * Real.exp (c' * (ModularGroup.S • w).im)
          * Real.exp (d' * ζ.im) := by
        refine mul_le_mul_of_nonneg_left e2 ?_
        exact mul_nonneg h0 (Real.exp_pos _).le

lemma mul (hF : BBdd c1 d1 F) (hG : BBdd c2 d2 G) :
    BBdd (c1 + c2) (d1 + d2) (fun w ζ => F w ζ * G w ζ) := by
  obtain ⟨C1, N1, hC1, hN1, hb1⟩ := hF
  obtain ⟨C2, N2, hC2, hN2, hb2⟩ := hG
  refine ⟨C1 * C2, N1 + N2, by positivity, by positivity, fun w ζ hw => ?_⟩
  have e1 := hb1 w ζ hw
  have e2 := hb2 w ζ hw
  have hX : (0:ℝ) < scale w := hw.scale_pos
  have hkey1 : (scale w) ^ N1 * (scale w) ^ N2 = (scale w) ^ (N1 + N2) :=
    (Real.rpow_add hX N1 N2).symm
  have hkey2 : Real.exp (c1 * (ModularGroup.S • w).im) * Real.exp (c2 * (ModularGroup.S • w).im)
      = Real.exp ((c1 + c2) * (ModularGroup.S • w).im) := by
    rw [← Real.exp_add]; congr 1; ring
  have hkey3 : Real.exp (d1 * ζ.im) * Real.exp (d2 * ζ.im)
      = Real.exp ((d1 + d2) * ζ.im) := by
    rw [← Real.exp_add]; congr 1; ring
  have hnorm := norm_mul (F w ζ) (G w ζ)
  rw [hnorm]
  calc ‖F w ζ‖ * ‖G w ζ‖
      ≤ (C1 * (scale w) ^ N1 * Real.exp (c1 * (ModularGroup.S • w).im)
            * Real.exp (d1 * ζ.im))
        * (C2 * (scale w) ^ N2 * Real.exp (c2 * (ModularGroup.S • w).im)
            * Real.exp (d2 * ζ.im)) :=
        mul_le_mul e1 e2 (norm_nonneg _)
          (by positivity)
    _ = C1 * C2 * (scale w) ^ (N1 + N2) * Real.exp ((c1 + c2) * (ModularGroup.S • w).im)
          * Real.exp ((d1 + d2) * ζ.im) := by
        rw [show (C1 * (scale w) ^ N1 * Real.exp (c1 * (ModularGroup.S • w).im)
              * Real.exp (d1 * ζ.im))
            * (C2 * (scale w) ^ N2 * Real.exp (c2 * (ModularGroup.S • w).im)
              * Real.exp (d2 * ζ.im))
          = C1 * C2 * ((scale w) ^ N1 * (scale w) ^ N2)
            * (Real.exp (c1 * (ModularGroup.S • w).im)
                * Real.exp (c2 * (ModularGroup.S • w).im))
            * (Real.exp (d1 * ζ.im) * Real.exp (d2 * ζ.im)) from by ring,
          hkey1, hkey2, hkey3]

lemma add (hF : BBdd c1 d1 F) (hG : BBdd c2 d2 G) :
    BBdd (max c1 c2) (max d1 d2) (fun w ζ => F w ζ + G w ζ) := by
  obtain ⟨C1, N1, hC1, hN1, hb1⟩ := hF
  obtain ⟨C2, N2, hC2, hN2, hb2⟩ := hG
  refine ⟨C1 + C2, max N1 N2, by positivity, le_max_of_le_left hN1, fun w ζ hw => ?_⟩
  refine le_trans (norm_add_le _ _) ?_
  have hX : (1:ℝ) ≤ scale w := hw.one_le_scale
  have hN1' : (scale w) ^ N1 ≤ (scale w) ^ (max N1 N2) :=
    Real.rpow_le_rpow_of_exponent_le hX (le_max_left _ _)
  have hN2' : (scale w) ^ N2 ≤ (scale w) ^ (max N1 N2) :=
    Real.rpow_le_rpow_of_exponent_le hX (le_max_right _ _)
  have hc1 : Real.exp (c1 * (ModularGroup.S • w).im) ≤ Real.exp (max c1 c2 * (ModularGroup.S • w).im) :=
    Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right (le_max_left _ _) hw.S_im_nonneg)
  have hc2 : Real.exp (c2 * (ModularGroup.S • w).im) ≤ Real.exp (max c1 c2 * (ModularGroup.S • w).im) :=
    Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right (le_max_right _ _) hw.S_im_nonneg)
  have hd1 : Real.exp (d1 * ζ.im) ≤ Real.exp (max d1 d2 * ζ.im) :=
    Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right (le_max_left _ _) (le_of_lt hw.im_pos))
  have hd2 : Real.exp (d2 * ζ.im) ≤ Real.exp (max d1 d2 * ζ.im) :=
    Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right (le_max_right _ _) (le_of_lt hw.im_pos))
  have h1 : C1 * (scale w) ^ N1 * Real.exp (c1 * (ModularGroup.S • w).im)
        * Real.exp (d1 * ζ.im)
      ≤ C1 * (scale w) ^ (max N1 N2) * Real.exp (max c1 c2 * (ModularGroup.S • w).im)
        * Real.exp (max d1 d2 * ζ.im) := by
    have a : C1 * (scale w) ^ N1 ≤ C1 * (scale w) ^ (max N1 N2) :=
      mul_le_mul_of_nonneg_left hN1' hC1.le
    have b : C1 * (scale w) ^ N1 * Real.exp (c1 * (ModularGroup.S • w).im)
        ≤ C1 * (scale w) ^ (max N1 N2) * Real.exp (max c1 c2 * (ModularGroup.S • w).im) :=
      mul_le_mul a hc1 (Real.exp_pos _).le (by positivity)
    exact mul_le_mul b hd1 (Real.exp_pos _).le (by positivity)
  have h2 : C2 * (scale w) ^ N2 * Real.exp (c2 * (ModularGroup.S • w).im)
        * Real.exp (d2 * ζ.im)
      ≤ C2 * (scale w) ^ (max N1 N2) * Real.exp (max c1 c2 * (ModularGroup.S • w).im)
        * Real.exp (max d1 d2 * ζ.im) := by
    have a : C2 * (scale w) ^ N2 ≤ C2 * (scale w) ^ (max N1 N2) :=
      mul_le_mul_of_nonneg_left hN2' hC2.le
    have b : C2 * (scale w) ^ N2 * Real.exp (c2 * (ModularGroup.S • w).im)
        ≤ C2 * (scale w) ^ (max N1 N2) * Real.exp (max c1 c2 * (ModularGroup.S • w).im) :=
      mul_le_mul a hc2 (Real.exp_pos _).le (by positivity)
    exact mul_le_mul b hd2 (Real.exp_pos _).le (by positivity)
  have hgoal : C1 * (scale w) ^ (max N1 N2) * Real.exp (max c1 c2 * (ModularGroup.S • w).im)
        * Real.exp (max d1 d2 * ζ.im)
      + C2 * (scale w) ^ (max N1 N2) * Real.exp (max c1 c2 * (ModularGroup.S • w).im)
        * Real.exp (max d1 d2 * ζ.im)
      = (C1 + C2) * (scale w) ^ (max N1 N2) * Real.exp (max c1 c2 * (ModularGroup.S • w).im)
        * Real.exp (max d1 d2 * ζ.im) := by ring
  linarith [le_trans (add_le_add (le_trans (hb1 w ζ hw) h1) (le_trans (hb2 w ζ hw) h2)) le_rfl,
    hgoal]

lemma neg (h : BBdd c d F) : BBdd c d (fun w ζ => -F w ζ) := by
  obtain ⟨C, N, hC, hN, hb⟩ := h
  exact ⟨C, N, hC, hN, fun w ζ hw => by rw [norm_neg]; exact hb w ζ hw⟩

lemma sub (hF : BBdd c1 d1 F) (hG : BBdd c2 d2 G) :
    BBdd (max c1 c2) (max d1 d2) (fun w ζ => F w ζ - G w ζ) := by
  simpa only [sub_eq_add_neg] using hF.add hG.neg

lemma const (k : ℂ) : BBdd 0 0 (fun _ _ => k) := by
  refine ⟨max ‖k‖ 1, 0, lt_of_lt_of_le zero_lt_one (le_max_right _ _), le_rfl, fun w ζ hw => ?_⟩
  simp only [Real.rpow_zero, mul_one, zero_mul, Real.exp_zero]
  exact le_max_left _ _

lemma const_mul (k : ℂ) (h : BBdd c d F) : BBdd c d (fun w ζ => k * F w ζ) := by
  have h1 := (const k).mul h
  simpa using h1

/-- A `Bdd c` bound on `E` (one variable) gives a `BBdd c 0` bound on the ball. -/
lemma of_bdd {c : ℝ} {F : ℍ → ℂ} (h : EtailE.Bdd c F) : BBdd c 0 (fun w _ => F w) := by
  obtain ⟨C, N, hC, hN, hb⟩ := h
  refine ⟨C, N, hC, hN, fun w ζ hw => ?_⟩
  have h1 := hb w hw.hw
  simpa only [zero_mul, Real.exp_zero, mul_one] using h1

/-- **The reduction of the exponential exponents.**  On the ball, `Im ζ ≥ Im (S • w) - 29/20`;
hence if `d ≤ 0` and `c + d ≤ 0` the product `e^{c Im (S • w)} e^{d Im ζ}` is bounded by the
constant `e^{-29 d/20}`. -/
lemma reduce {c d : ℝ} {F : ℍ → ℍ → ℂ} (h : BBdd c d F) (hd : d ≤ 0) (hcd : c + d ≤ 0) :
    BBdd 0 0 F := by
  obtain ⟨C, N, hC, hN, hb⟩ := h
  set E : ℝ := Real.exp (-(d * (29 / 20))) with hE
  have hEpos : 0 < E := Real.exp_pos _
  refine ⟨C * E + 1, N, by positivity, hN, fun w ζ hw => ?_⟩
  have h1 := hb w ζ hw
  have h2 : Real.exp (c * (ModularGroup.S • w).im) * Real.exp (d * ζ.im) ≤ E := by
    rw [hE]; exact hw.exp_le_const_im hd hcd
  have hX1 : (1:ℝ) ≤ (scale w) ^ N := Real.one_le_rpow hw.one_le_scale hN
  have hX0 : (0:ℝ) ≤ (scale w) ^ N := le_trans zero_le_one hX1
  have hC0 : 0 ≤ C := hC.le
  calc ‖F w ζ‖
      ≤ C * (scale w) ^ N * Real.exp (c * (ModularGroup.S • w).im)
          * Real.exp (d * ζ.im) := h1
    _ = C * (scale w) ^ N
          * (Real.exp (c * (ModularGroup.S • w).im) * Real.exp (d * ζ.im)) := by ring
    _ ≤ C * (scale w) ^ N * E := mul_le_mul_of_nonneg_left h2 (by positivity)
    _ = C * E * (scale w) ^ N := by ring
    _ ≤ (C * E + 1) * (scale w) ^ N := by nlinarith [hX1, hEpos, hC.le]
    _ = (C * E + 1) * (scale w) ^ N * Real.exp (0 * (ModularGroup.S • w).im)
          * Real.exp (0 * ζ.im) := by
        rw [zero_mul, Real.exp_zero, zero_mul, Real.exp_zero]; ring

/-- A `BBdd 0 0` bound is a plain `C (scale w)^N` bound on the ball. -/
lemma exists_bound_zero {F : ℍ → ℍ → ℂ} (h : BBdd 0 0 F) :
    ∃ C N : ℝ, 0 < C ∧ 0 ≤ N ∧
      ∀ (w ζ : ℍ), Ball w ζ → ‖F w ζ‖ ≤ C * (scale w) ^ N := by
  obtain ⟨C, N, hC, hN, hb⟩ := h
  refine ⟨C, N, hC, hN, fun w ζ hw => ?_⟩
  have h1 := hb w ζ hw
  simpa only [zero_mul, Real.exp_zero, mul_one] using h1

end BBdd

end Work.Asymptotics.TileDevBall
