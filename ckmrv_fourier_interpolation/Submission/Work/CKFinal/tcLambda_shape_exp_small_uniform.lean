/-
# Uniform shape bound for the closed form `tcLambda` of the CKMRV tail

`Work.Asymptotics.tcLambda G B w` is the `λ`-closed form of
`sinSq r · ∫_{Ici B} Aexp G w t · e^{-πr²t} dt` (with `λ` the argument of `tcLambda`).  This file
proves that its `l`-th iterated derivative is bounded, uniformly over the point `w` and the
contour height `B ∈ [1, scale w]`, by `scale w ^ N · (1 + |x|) e^{-x}` whenever the two rows of
`G` obey the paper's growth bounds: the `(0,j)`-row grows at most like a power of `scale w`, while
the `(1,j)`-row is `e^{-2πB}`-small.

## The route

`tcLambda` splits as the four-term sum
`E_sh1 B · G 0 0 w + E_sh2 B · G 0 1 w + E_sh3 B · G 1 0 w + E_sh4 B · G 1 1 w`
(`Work.CKFinal.E_tcLambda_iteratedDeriv_le_sum`), so the iterated derivative is controlled by the
four shape bounds

* `Work.Asymptotics.E_sh1_bound`, `E_sh2_bound` (`x ≥ 0`, already in `E_TailClosed`),
* `Work.CKFinal.E_sh3_bound_global`, `E_sh4_bound_nonneg` (the two `(1,j)`-corners, which carry
  the extra factor `e^{2πB}` because the shifted exponential `e^{-(x-2π)B}` *grows* on `0 ≤ x ≤ 2π`).

The shift factor `e^{2πB}` is then cancelled against the `e^{-2πB}`-smallness of the `(1,j)`-row,
using `B ≤ scale w` to absorb everything into a power of `scale w`.
-/
import Mathlib
import Submission.Work.Asymptotics.E_TailClosed
import Submission.Work.Asymptotics.psi1_iteratedDeriv_bound
import Submission.Work.Asymptotics.highPartDefs
import Submission.Work.CKFinal.E_sh3_bound_global
import Submission.Work.CKFinal.E_tcLambda_iteratedDeriv_le_sum

noncomputable section
open MeasureTheory Filter Topology UpperHalfPlane
open scoped Topology ContDiff

namespace Work.CKFinal

open Work.Asymptotics

/-- **Global bound for the `(1,1)` corner of the tail.**  The `l`-th derivative of `E_sh4 B` is
bounded for every `x ≥ 0` by the Leibniz sum for `tcF4 B` times the shift factor `exp (2π B)`.
This is the companion of `Work.CKFinal.E_sh3_bound_global`; it is an immediate corollary of
`Work.CKFinal.E_shape_bound_exp_shift` applied to `tcF4 B`. -/
lemma E_sh4_bound_nonneg (B : ℝ) (hB0 : 0 ≤ B) (hB1 : 1 ≤ B) (l : ℕ) (x : ℝ) (hx : 0 ≤ x) :
    ‖iteratedDeriv l (Work.Asymptotics.E_sh4 B) x‖
      ≤ 2 * (B + 1) * (1 + 2 * Real.pi) * (2 + B) ^ l * Real.exp (2 * Real.pi * B)
          * ((1 + |x|) * Real.exp (-x)) := by
  rw [show Work.Asymptotics.E_sh4 B
      = fun y : ℝ => Work.Asymptotics.tcF4 B y
          * Complex.exp (-(((y - 2 * Real.pi : ℝ) : ℂ) * (B : ℂ))) from rfl]
  have h := E_shape_bound_exp_shift (tcF4 B) (contDiff_tcF4 B)
    (fun p => 2 ^ (p + 1) * (B + 1) * (1 + 2 * Real.pi))
    (fun m y => E_tcF4_bound B hB0 m y) (2 * Real.pi) B hB1 l x hx
  refine le_trans h ?_
  have hsum : (∑ p ∈ Finset.range (l + 1),
      (l.choose p : ℝ) * (2 ^ (p + 1) * (B + 1) * (1 + 2 * Real.pi)) * B ^ (l - p))
      = 2 * (B + 1) * (1 + 2 * Real.pi) * (2 + B) ^ l := by
    rw [show (∑ p ∈ Finset.range (l + 1),
        (l.choose p : ℝ) * (2 ^ (p + 1) * (B + 1) * (1 + 2 * Real.pi)) * B ^ (l - p))
      = (1 + 2 * Real.pi) * (∑ p ∈ Finset.range (l + 1),
          (l.choose p : ℝ) * (2 ^ (p + 1) * (B + 1)) * B ^ (l - p)) from by
        rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro p hp; ring]
    rw [E_sum_choose_succ' l B]
    ring
  rw [hsum]

/-- **Collapsed global bound for the `(1,0)` corner.**  The `(1+2π)`-weighted Leibniz sum of
`E_sh3_bound_global` is `2 (1+2π) (2+B)^l`, giving the same clean shape as `E_sh4_bound_nonneg`. -/
lemma E_sh3_collapsed (B : ℝ) (hB1 : 1 ≤ B) (l : ℕ) (x : ℝ) (hx : 0 ≤ x) :
    ‖iteratedDeriv l (Work.Asymptotics.E_sh3 B) x‖
      ≤ 2 * (1 + 2 * Real.pi) * (2 + B) ^ l * Real.exp (2 * Real.pi * B)
          * ((1 + |x|) * Real.exp (-x)) := by
  refine le_trans (E_sh3_bound_global B hB1 l x hx) ?_
  have hsum : (∑ p ∈ Finset.range (l + 1),
      (l.choose p : ℝ) * (2 ^ (p + 1) * (1 + 2 * Real.pi)) * B ^ (l - p))
      = 2 * (1 + 2 * Real.pi) * (2 + B) ^ l := by
    rw [show (∑ p ∈ Finset.range (l + 1),
        (l.choose p : ℝ) * (2 ^ (p + 1) * (1 + 2 * Real.pi)) * B ^ (l - p))
      = (1 + 2 * Real.pi) * (∑ p ∈ Finset.range (l + 1),
          (l.choose p : ℝ) * (2 ^ (p + 1)) * B ^ (l - p)) from by
        rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro p hp; ring]
    rw [E_sum_choose_succ l B]; ring
  rw [hsum]

theorem tcLambda_shape_exp_small_uniform (C0 N0 C1 N1 : ℝ)
    (hC0 : 0 ≤ C0) (hN0 : 0 ≤ N0) (hC1 : 0 ≤ C1) (hN1 : 0 ≤ N1) (l : ℕ) :
    ∃ C N : ℝ, 0 ≤ C ∧ 0 ≤ N ∧
      ∀ (G : Fin 2 → Fin 2 → UpperHalfPlane → ℂ) (w : UpperHalfPlane) (B : ℝ),
        1 ≤ B → B ≤ Work.Kernels.scale w →
        (∀ j : Fin 2, ‖G 0 j w‖ ≤ C0 * (Work.Kernels.scale w) ^ N0) →
        (∀ j : Fin 2, ‖G 1 j w‖ ≤ C1 * (Work.Kernels.scale w) ^ N1 * Real.exp (-(2 * Real.pi * B))) →
        ∀ x : ℝ, 0 ≤ x →
          ‖iteratedDeriv l (Work.Asymptotics.tcLambda G B w) x‖
            ≤ C * (Work.Kernels.scale w) ^ N * (1 + |x|) * Real.exp (-x) := by
  refine ⟨8 * (3 : ℝ) ^ l * (1 + 2 * Real.pi) * (C0 + C1), (l : ℝ) + 1 + max N0 N1, ?_, ?_, ?_⟩
  · exact mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) (pow_nonneg (by norm_num) l))
      (by linarith [Real.pi_pos])) (add_nonneg hC0 hC1)
  · have h1 : (0 : ℝ) ≤ (l : ℝ) := Nat.cast_nonneg l
    have h2 : (0 : ℝ) ≤ max N0 N1 := le_trans hN0 (le_max_left _ _)
    linarith
  · intro G w B hB1 hBle hG0 hG1 x hx
    have hB0 : (0 : ℝ) ≤ B := le_trans zero_le_one hB1
    have hSW1 : (1 : ℝ) ≤ Work.Kernels.scale w := Work.Kernels.one_le_scale w
    have hSW0 : (0 : ℝ) < Work.Kernels.scale w := Work.Kernels.scale_pos w
    have hSWnn : (0 : ℝ) ≤ Work.Kernels.scale w := hSW0.le
    have hRnn : (0 : ℝ) ≤ (1 + |x|) * Real.exp (-x) := by positivity
    have hEnn : (0 : ℝ) ≤ Real.exp (2 * Real.pi * B) := Real.exp_nonneg _
    have hb1 := Work.Asymptotics.E_sh1_bound B hB0 hB1 l x hx
    have hb2 := Work.Asymptotics.E_sh2_bound B hB0 hB1 l x hx
    have hb3 := E_sh3_collapsed B hB1 l x hx
    have hb4 := E_sh4_bound_nonneg B hB0 hB1 l x hx
    have hD1 : 2 * (2 + B) ^ l ≤ 2 * (B + 1) * (1 + 2 * Real.pi) * (2 + B) ^ l := by
      have hP : (1 : ℝ) ≤ (B + 1) * (1 + 2 * Real.pi) := by
        have a : (1 : ℝ) ≤ B + 1 := by linarith
        have b : (1 : ℝ) ≤ 1 + 2 * Real.pi := by linarith [Real.pi_pos]
        calc (1 : ℝ) = 1 * 1 := by ring
          _ ≤ (B + 1) * (1 + 2 * Real.pi) := mul_le_mul a b (by norm_num) (by linarith)
      have hp : (0 : ℝ) ≤ 2 * (2 + B) ^ l :=
        mul_nonneg (by norm_num) (pow_nonneg (by linarith) l)
      calc 2 * (2 + B) ^ l = 2 * (2 + B) ^ l * 1 := by ring
        _ ≤ 2 * (2 + B) ^ l * ((B + 1) * (1 + 2 * Real.pi)) := mul_le_mul_of_nonneg_left hP hp
        _ = 2 * (B + 1) * (1 + 2 * Real.pi) * (2 + B) ^ l := by ring
    have hD2 : 2 * (B + 1) * (2 + B) ^ l ≤ 2 * (B + 1) * (1 + 2 * Real.pi) * (2 + B) ^ l := by
      have hP : (1 : ℝ) ≤ 1 + 2 * Real.pi := by linarith [Real.pi_pos]
      have hp : (0 : ℝ) ≤ 2 * (B + 1) * (2 + B) ^ l :=
        mul_nonneg (mul_nonneg (by norm_num) (by linarith)) (pow_nonneg (by linarith) l)
      calc 2 * (B + 1) * (2 + B) ^ l = 2 * (B + 1) * (2 + B) ^ l * 1 := by ring
        _ ≤ 2 * (B + 1) * (2 + B) ^ l * (1 + 2 * Real.pi) := mul_le_mul_of_nonneg_left hP hp
        _ = 2 * (B + 1) * (1 + 2 * Real.pi) * (2 + B) ^ l := by ring
    have hD3 : 2 * (1 + 2 * Real.pi) * (2 + B) ^ l
        ≤ 2 * (B + 1) * (1 + 2 * Real.pi) * (2 + B) ^ l := by
      have hb1p : (1 : ℝ) ≤ B + 1 := by linarith
      have hp : (0 : ℝ) ≤ (1 + 2 * Real.pi) * (2 + B) ^ l :=
        mul_nonneg (by linarith [Real.pi_pos]) (pow_nonneg (by linarith) l)
      calc 2 * (1 + 2 * Real.pi) * (2 + B) ^ l = 2 * ((1 + 2 * Real.pi) * (2 + B) ^ l) := by ring
        _ ≤ 2 * ((B + 1) * ((1 + 2 * Real.pi) * (2 + B) ^ l)) := by
            refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
            calc (1 + 2 * Real.pi) * (2 + B) ^ l
                = 1 * ((1 + 2 * Real.pi) * (2 + B) ^ l) := by ring
              _ ≤ (B + 1) * ((1 + 2 * Real.pi) * (2 + B) ^ l) :=
                  mul_le_mul_of_nonneg_right hb1p hp
        _ = 2 * (B + 1) * (1 + 2 * Real.pi) * (2 + B) ^ l := by ring
    have hb1' : ‖iteratedDeriv l (Work.Asymptotics.E_sh1 B) x‖
        ≤ 2 * (B + 1) * (1 + 2 * Real.pi) * (2 + B) ^ l * ((1 + |x|) * Real.exp (-x)) :=
      le_trans hb1 (mul_le_mul_of_nonneg_right hD1 hRnn)
    have hb2' : ‖iteratedDeriv l (Work.Asymptotics.E_sh2 B) x‖
        ≤ 2 * (B + 1) * (1 + 2 * Real.pi) * (2 + B) ^ l * ((1 + |x|) * Real.exp (-x)) :=
      le_trans hb2 (mul_le_mul_of_nonneg_right hD2 hRnn)
    have hb3' : ‖iteratedDeriv l (Work.Asymptotics.E_sh3 B) x‖
        ≤ 2 * (B + 1) * (1 + 2 * Real.pi) * (2 + B) ^ l * Real.exp (2 * Real.pi * B)
            * ((1 + |x|) * Real.exp (-x)) := by
      refine le_trans hb3 ?_
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hD3 hEnn) hRnn
    have hb4' : ‖iteratedDeriv l (Work.Asymptotics.E_sh4 B) x‖
        ≤ 2 * (B + 1) * (1 + 2 * Real.pi) * (2 + B) ^ l * Real.exp (2 * Real.pi * B)
            * ((1 + |x|) * Real.exp (-x)) := hb4
    have hDRnn : (0 : ℝ) ≤ 2 * (B + 1) * (1 + 2 * Real.pi) * (2 + B) ^ l
        * ((1 + |x|) * Real.exp (-x)) :=
      mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) (by linarith))
        (by linarith [Real.pi_pos])) (pow_nonneg (by linarith) l)) hRnn
    have hSig : (‖G 0 0 w‖ + ‖G 0 1 w‖)
        + Real.exp (2 * Real.pi * B) * (‖G 1 0 w‖ + ‖G 1 1 w‖)
        ≤ 2 * C0 * (Work.Kernels.scale w) ^ (max N0 N1)
          + 2 * C1 * (Work.Kernels.scale w) ^ (max N0 N1) := by
      have h0 : ‖G 0 0 w‖ + ‖G 0 1 w‖
          ≤ 2 * C0 * (Work.Kernels.scale w) ^ (max N0 N1) := by
        have hle : (Work.Kernels.scale w) ^ N0 ≤ (Work.Kernels.scale w) ^ (max N0 N1) :=
          Real.rpow_le_rpow_of_exponent_le hSW1 (le_max_left N0 N1)
        calc ‖G 0 0 w‖ + ‖G 0 1 w‖
            ≤ C0 * (Work.Kernels.scale w) ^ N0 + C0 * (Work.Kernels.scale w) ^ N0 :=
              add_le_add (hG0 0) (hG0 1)
          _ = 2 * (C0 * (Work.Kernels.scale w) ^ N0) := by ring
          _ ≤ 2 * (C0 * (Work.Kernels.scale w) ^ (max N0 N1)) :=
              mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hle hC0) (by norm_num)
          _ = 2 * C0 * (Work.Kernels.scale w) ^ (max N0 N1) := by ring
      have h1 : Real.exp (2 * Real.pi * B) * (‖G 1 0 w‖ + ‖G 1 1 w‖)
          ≤ 2 * C1 * (Work.Kernels.scale w) ^ (max N0 N1) := by
        have hle : (Work.Kernels.scale w) ^ N1 ≤ (Work.Kernels.scale w) ^ (max N0 N1) :=
          Real.rpow_le_rpow_of_exponent_le hSW1 (le_max_right N0 N1)
        have hexp1 : Real.exp (2 * Real.pi * B) * Real.exp (-(2 * Real.pi * B)) = 1 := by
          rw [← Real.exp_add, show 2 * Real.pi * B + -(2 * Real.pi * B) = 0 by ring, Real.exp_zero]
        calc Real.exp (2 * Real.pi * B) * (‖G 1 0 w‖ + ‖G 1 1 w‖)
            ≤ Real.exp (2 * Real.pi * B) * (C1 * (Work.Kernels.scale w) ^ N1
                * Real.exp (-(2 * Real.pi * B))
              + C1 * (Work.Kernels.scale w) ^ N1 * Real.exp (-(2 * Real.pi * B))) :=
              mul_le_mul_of_nonneg_left (add_le_add (hG1 0) (hG1 1)) hEnn
          _ = 2 * (Real.exp (2 * Real.pi * B)
                * (C1 * (Work.Kernels.scale w) ^ N1 * Real.exp (-(2 * Real.pi * B)))) := by ring
          _ = 2 * (C1 * (Work.Kernels.scale w) ^ N1
                * (Real.exp (2 * Real.pi * B) * Real.exp (-(2 * Real.pi * B)))) := by ring
          _ = 2 * (C1 * (Work.Kernels.scale w) ^ N1) := by rw [hexp1]; ring
          _ ≤ 2 * (C1 * (Work.Kernels.scale w) ^ (max N0 N1)) :=
              mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hle hC1) (by norm_num)
          _ = 2 * C1 * (Work.Kernels.scale w) ^ (max N0 N1) := by ring
      linarith [h0, h1]
    have hDbound : 2 * (B + 1) * (1 + 2 * Real.pi) * (2 + B) ^ l
        ≤ 4 * (3 : ℝ) ^ l * (1 + 2 * Real.pi) * (Work.Kernels.scale w) ^ (l + 1) := by
      have hBp : B + 1 ≤ 2 * Work.Kernels.scale w := by linarith
      have h2B : 2 + B ≤ 3 * Work.Kernels.scale w := by linarith
      have hp : (2 + B) ^ l ≤ (3 * Work.Kernels.scale w) ^ l :=
        pow_le_pow_left₀ (by linarith) h2B l
      have hone : (0 : ℝ) ≤ 1 + 2 * Real.pi := by linarith [Real.pi_pos]
      have hstep : 2 * (B + 1) * (1 + 2 * Real.pi) * (2 + B) ^ l
          ≤ 2 * (2 * Work.Kernels.scale w) * (1 + 2 * Real.pi)
              * (3 * Work.Kernels.scale w) ^ l := by
        have h1 : 2 * (B + 1) ≤ 2 * (2 * Work.Kernels.scale w) := by linarith
        calc 2 * (B + 1) * (1 + 2 * Real.pi) * (2 + B) ^ l
            = (2 * (B + 1)) * ((1 + 2 * Real.pi) * (2 + B) ^ l) := by ring
          _ ≤ (2 * (2 * Work.Kernels.scale w))
                * ((1 + 2 * Real.pi) * (3 * Work.Kernels.scale w) ^ l) := by
              refine mul_le_mul h1 ?_ (mul_nonneg hone (pow_nonneg (by linarith) l)) (by linarith)
              exact mul_le_mul_of_nonneg_left hp hone
          _ = 2 * (2 * Work.Kernels.scale w) * (1 + 2 * Real.pi)
              * (3 * Work.Kernels.scale w) ^ l := by ring
      calc 2 * (B + 1) * (1 + 2 * Real.pi) * (2 + B) ^ l
          ≤ 2 * (2 * Work.Kernels.scale w) * (1 + 2 * Real.pi)
              * (3 * Work.Kernels.scale w) ^ l := hstep
        _ = 4 * (3 : ℝ) ^ l * (1 + 2 * Real.pi)
              * (Work.Kernels.scale w * Work.Kernels.scale w ^ l) := by rw [mul_pow]; ring
        _ = 4 * (3 : ℝ) ^ l * (1 + 2 * Real.pi)
              * (Work.Kernels.scale w) ^ (l + 1) := by
            rw [show Work.Kernels.scale w * Work.Kernels.scale w ^ l
                = (Work.Kernels.scale w) ^ (l + 1) by rw [pow_succ]; ring]
    have hZnn : (0 : ℝ) ≤ 2 * (C0 + C1) * (Work.Kernels.scale w) ^ (max N0 N1) :=
      mul_nonneg (mul_nonneg (by norm_num) (add_nonneg hC0 hC1)) (Real.rpow_nonneg hSWnn _)
    have hSwmer : (Work.Kernels.scale w) ^ (l + 1) * (Work.Kernels.scale w) ^ (max N0 N1)
        = (Work.Kernels.scale w) ^ ((l : ℝ) + 1 + max N0 N1) := by
      have h1 : (Work.Kernels.scale w) ^ (l + 1)
          = (Work.Kernels.scale w) ^ (((l + 1 : ℕ)) : ℝ) :=
        (Real.rpow_natCast (Work.Kernels.scale w) (l + 1)).symm
      rw [h1, ← Real.rpow_add hSW0]
      congr 1
      push_cast
      ring
    have hdec := E_tcLambda_iteratedDeriv_le_sum G B w l x
    calc ‖iteratedDeriv l (Work.Asymptotics.tcLambda G B w) x‖
        ≤ ‖iteratedDeriv l (Work.Asymptotics.E_sh1 B) x‖ * ‖G 0 0 w‖
          + ‖iteratedDeriv l (Work.Asymptotics.E_sh2 B) x‖ * ‖G 0 1 w‖
          + ‖iteratedDeriv l (Work.Asymptotics.E_sh3 B) x‖ * ‖G 1 0 w‖
          + ‖iteratedDeriv l (Work.Asymptotics.E_sh4 B) x‖ * ‖G 1 1 w‖ := hdec
      _ ≤ 2 * (B + 1) * (1 + 2 * Real.pi) * (2 + B) ^ l * ((1 + |x|) * Real.exp (-x)) * ‖G 0 0 w‖
          + 2 * (B + 1) * (1 + 2 * Real.pi) * (2 + B) ^ l * ((1 + |x|) * Real.exp (-x)) * ‖G 0 1 w‖
          + 2 * (B + 1) * (1 + 2 * Real.pi) * (2 + B) ^ l * Real.exp (2 * Real.pi * B)
              * ((1 + |x|) * Real.exp (-x)) * ‖G 1 0 w‖
          + 2 * (B + 1) * (1 + 2 * Real.pi) * (2 + B) ^ l * Real.exp (2 * Real.pi * B)
              * ((1 + |x|) * Real.exp (-x)) * ‖G 1 1 w‖ := by
            have t1 := mul_le_mul_of_nonneg_right hb1' (norm_nonneg (G 0 0 w))
            have t2 := mul_le_mul_of_nonneg_right hb2' (norm_nonneg (G 0 1 w))
            have t3 := mul_le_mul_of_nonneg_right hb3' (norm_nonneg (G 1 0 w))
            have t4 := mul_le_mul_of_nonneg_right hb4' (norm_nonneg (G 1 1 w))
            linarith [t1, t2, t3, t4]
      _ = 2 * (B + 1) * (1 + 2 * Real.pi) * (2 + B) ^ l * ((1 + |x|) * Real.exp (-x))
            * ((‖G 0 0 w‖ + ‖G 0 1 w‖)
              + Real.exp (2 * Real.pi * B) * (‖G 1 0 w‖ + ‖G 1 1 w‖)) := by ring
      _ ≤ 2 * (B + 1) * (1 + 2 * Real.pi) * (2 + B) ^ l * ((1 + |x|) * Real.exp (-x))
            * (2 * C0 * (Work.Kernels.scale w) ^ (max N0 N1)
              + 2 * C1 * (Work.Kernels.scale w) ^ (max N0 N1)) :=
            mul_le_mul_of_nonneg_left hSig hDRnn
      _ = 2 * (B + 1) * (1 + 2 * Real.pi) * (2 + B) ^ l * ((1 + |x|) * Real.exp (-x))
            * (2 * (C0 + C1) * (Work.Kernels.scale w) ^ (max N0 N1)) := by ring
      _ ≤ 4 * (3 : ℝ) ^ l * (1 + 2 * Real.pi) * (Work.Kernels.scale w) ^ (l + 1)
            * ((1 + |x|) * Real.exp (-x))
            * (2 * (C0 + C1) * (Work.Kernels.scale w) ^ (max N0 N1)) :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hDbound hRnn) hZnn
      _ = 8 * (3 : ℝ) ^ l * (1 + 2 * Real.pi) * (C0 + C1)
            * ((Work.Kernels.scale w) ^ (l + 1) * (Work.Kernels.scale w) ^ (max N0 N1))
            * ((1 + |x|) * Real.exp (-x)) := by ring
      _ = 8 * (3 : ℝ) ^ l * (1 + 2 * Real.pi) * (C0 + C1)
            * (Work.Kernels.scale w) ^ ((l : ℝ) + 1 + max N0 N1)
            * ((1 + |x|) * Real.exp (-x)) := by rw [hSwmer]
      _ = 8 * (3 : ℝ) ^ l * (1 + 2 * Real.pi) * (C0 + C1)
            * (Work.Kernels.scale w) ^ ((l : ℝ) + 1 + max N0 N1)
            * (1 + |x|) * Real.exp (-x) := by ring

end Work.CKFinal
