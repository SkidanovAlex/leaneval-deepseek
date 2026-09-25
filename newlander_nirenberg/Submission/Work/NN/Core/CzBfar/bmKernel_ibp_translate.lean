import Mathlib
import Submission.Work.CR.Flat.Cauchy.bmCZDefs
import Submission.Work.CR.Flat.Cauchy.bmCz.dCoord_bmKernel
import Submission.Work.CR.Flat.Polydisc
import Submission.Work.CR.Flat.Cauchy.bmSetup
import Submission.Work.CR.Flat.Cauchy.bmCz.integral_bmKernel_mul_dCoord
import Submission.Work.CR.Flat.Cauchy.bmDzKernel_ibp
import Submission.Work.CR.Flat.Cauchy.bmIbp.Defs

namespace Work.NN.Core.CzBfar

open MeasureTheory Set

/-- The Euclidean norm on `ℂⁿ` is controlled by the ambient (sup) norm:
`eucNorm x ≤ √n · ‖x‖`. -/
private lemma eucNorm_le_sqrt_mul_norm_aux {n : ℕ} (x : Fin n → ℂ) :
    Work.CR.Flat.Cauchy.eucNorm x ≤ Real.sqrt n * ‖x‖ := by
  have h1 : Work.CR.Flat.Cauchy.eucNorm x ^ 2 ≤ (Real.sqrt n * ‖x‖) ^ 2 := by
    rw [mul_pow, Real.sq_sqrt (Nat.cast_nonneg n), ← Work.CR.Flat.Cauchy.nrmSq_eq_eucNorm_sq]
    exact Work.CR.Flat.Cauchy.nrmSq_le_card_mul x
  have h2 := sq_le_sq.mp h1
  rwa [abs_of_nonneg (Work.CR.Flat.Cauchy.eucNorm_nonneg x),
      abs_of_nonneg (mul_nonneg (Real.sqrt_nonneg n) (norm_nonneg x))] at h2

/-- **Integration by parts against the Bochner–Martinelli kernel, in translated form.**

For a `C¹` function `F` supported in the (sup-norm) ball of radius `r`, and a point `z` with
`r < ‖z‖`, the singularity of the kernel `bmKernel l` at the origin lies strictly outside the
support of `F(z + ·)`.  Hence the singular subtraction of the classical identity is unnecessary
and one gets the clean full-space integration-by-parts identity

`∫ x, bmKernel l x · ∂_i (F(z + ·)) x = - ∫ x, ∂_{z_i}(bmKernel l) x · F(z + x)`.

The proof applies `bmDzKernel_ibp` to the translate `g = F(z + ·)` (whose support is contained in
the Euclidean ball of radius `R`), observes that `g 0 = 0` (since `r < ‖z‖`), and removes the
restriction to `eucBall (4R)` because `g` vanishes outside it. -/
theorem bmKernel_ibp_translate {n : ℕ} (l i : Fin n) {r : ℝ}
    {F : (Fin n → ℂ) → ℂ} (hF : ContDiff ℝ 1 F)
    (hsupp : ∀ x : Fin n → ℂ, r ≤ ‖x‖ → F x = 0) {z : Fin n → ℂ} (hz : r < ‖z‖) :
    ∫ x : Fin n → ℂ, Work.CR.Flat.Cauchy.bmKernel l x *
        Work.CR.Flat.dCoord i (fun x => F (z + x)) x
      = -∫ x : Fin n → ℂ, Work.CR.Flat.Cauchy.bmDzKernel i l x * F (z + x) := by
  have hn : 0 < n := l.pos
  let g : (Fin n → ℂ) → ℂ := fun x => F (z + x)
  have hg : ContDiff ℝ 1 g := hF.comp (contDiff_const.add contDiff_id)
  let R : ℝ := Real.sqrt n * (|r| + ‖z‖) + 1
  have hsqrtpos : 0 < Real.sqrt n := by
    rw [Real.sqrt_pos]; exact_mod_cast hn
  have hRpos : 0 < R := by
    rw [show R = Real.sqrt n * (|r| + ‖z‖) + 1 from rfl]; positivity
  -- `g` is supported in the Euclidean ball of radius `R`
  have hgsupp : ∀ x : Fin n → ℂ, R ≤ Work.CR.Flat.Cauchy.eucNorm x → g x = 0 := by
    intro x hx
    have hx' : Real.sqrt n * (|r| + ‖z‖) ≤ Work.CR.Flat.Cauchy.eucNorm x := by
      rw [show R = Real.sqrt n * (|r| + ‖z‖) + 1 from rfl] at hx; linarith
    have hxn : Real.sqrt n * (|r| + ‖z‖) ≤ Real.sqrt n * ‖x‖ :=
      le_trans hx' (eucNorm_le_sqrt_mul_norm_aux x)
    have hxnorm : |r| + ‖z‖ ≤ ‖x‖ := le_of_mul_le_mul_left hxn hsqrtpos
    have hzx : r ≤ ‖z + x‖ := by
      have htri : ‖x‖ ≤ ‖z + x‖ + ‖z‖ := by
        calc ‖x‖ = ‖(z + x) + (-z)‖ := by ring_nf
          _ ≤ ‖z + x‖ + ‖-z‖ := norm_add_le _ _
          _ = ‖z + x‖ + ‖z‖ := by rw [norm_neg]
      linarith [le_abs_self r]
    show F (z + x) = 0
    exact hsupp (z + x) hzx
  -- the classical identity for the translate
  have hb := Work.CR.Flat.Cauchy.bmDzKernel_ibp hn i l hRpos hg hgsupp
  -- `g` vanishes at the origin, since `r < ‖z‖`
  have hg0 : g 0 = 0 := by
    show F (z + 0) = 0
    rw [add_zero]
    exact hsupp z (le_of_lt hz)
  -- remove the restriction to `eucBall (4R)`: `g` vanishes off it
  have hres : ∫ x in Work.CR.Flat.Cauchy.eucBall (n := n) (4 * R),
        Work.CR.Flat.Cauchy.bmDzKernel i l x * (g x - g 0)
      = ∫ x, Work.CR.Flat.Cauchy.bmDzKernel i l x * g x := by
    rw [show (∫ x in Work.CR.Flat.Cauchy.eucBall (n := n) (4 * R),
          Work.CR.Flat.Cauchy.bmDzKernel i l x * (g x - g 0))
        = ∫ x in Work.CR.Flat.Cauchy.eucBall (n := n) (4 * R),
          Work.CR.Flat.Cauchy.bmDzKernel i l x * g x from ?_]
    · exact setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx => by
        have h4 : 4 * R ≤ Work.CR.Flat.Cauchy.eucNorm x :=
          not_lt.mp (fun hlt => hx (by simpa [Work.CR.Flat.Cauchy.mem_eucBall] using hlt))
        have hxR : R ≤ Work.CR.Flat.Cauchy.eucNorm x := by linarith
        rw [hgsupp x hxR, mul_zero])
    · apply setIntegral_congr_fun (Work.CR.Flat.Cauchy.measurableSet_eucBall (4 * R))
      intro x hx
      simp only [hg0, sub_zero]
  rw [hb, hres]

end Work.NN.Core.CzBfar
