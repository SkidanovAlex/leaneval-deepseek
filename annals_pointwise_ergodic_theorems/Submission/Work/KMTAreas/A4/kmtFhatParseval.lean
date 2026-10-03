import Mathlib
import Submission.Work.A3.parseval_finsupp

/-!
# Bilinear Parseval identity for `Work.A3.kmtFhat`

`Work.A3.kmtFhat f θ = ∑'_x f x * e(-xθ)` is the (1-periodic) Fourier transform, as a function of
the frequency `θ`, of a function `f : ℤ → ℂ`.  Here we prove the **bilinear Parseval identity**

`∑'_x a x * star (b x) = ∫_0^1 kmtFhat a t * star (kmtFhat b t) dt`

for two absolutely summable sequences `a, b`.

The proof is the direct one.  Since `a, b` are absolutely summable, the pointwise product of the
transforms is the absolutely convergent double series

`kmtFhat a t * star (kmtFhat b t)
   = ∑' p : ℤ × ℤ, (a p.1 * star (b p.2)) * (parsevalE p.1 t * star (parsevalE p.2 t))`,

whose terms are dominated by the summable family `‖a p.1‖ * ‖b p.2‖`.  Fubini for the Bochner
integral (`MeasureTheory.integral_tsum_of_summable_integral_norm`) therefore exchanges the sum and
the integral, and the orthogonality `∫_0^1 parsevalE x t * star (parsevalE y t) dt = δ_{x,y}`
collapses the double sum onto the diagonal, which is exactly `∑'_x a x * star (b x)`.

The finitely supported analogue of the orthogonality is `Work.A3.parseval_integral_char_pair`
(and the `L²` Plancherel identity in that setting is `Work.A3.parseval_finsupp`).
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

open scoped BigOperators
open MeasureTheory

namespace Work.KMTAreas.A4

noncomputable section

private lemma norm_parsevalE (x : ℤ) (t : ℝ) : ‖Work.A3.parsevalE x t‖ = 1 := by
  rw [Work.A3.parsevalE, Complex.norm_exp]
  simp

private lemma continuous_parsevalE (x : ℤ) : Continuous fun t : ℝ => Work.A3.parsevalE x t := by
  unfold Work.A3.parsevalE
  fun_prop

private lemma parsevalE_pair_integral (x y : ℤ) :
    ∫ t : ℝ, Work.A3.parsevalE x t * star (Work.A3.parsevalE y t)
      ∂(MeasureTheory.volume.restrict (Set.Ioc (0:ℝ) 1)) = if x = y then (1:ℂ) else 0 := by
  rw [← MeasureTheory.integral_Icc_eq_integral_Ioc]
  have h : (fun t : ℝ => Work.A3.parsevalE x t * star (Work.A3.parsevalE y t))
      = fun t : ℝ => star (Work.A3.parsevalE y t) * Work.A3.parsevalE x t := by
    funext t; ring
  rw [h, Work.A3.parseval_integral_char_pair y x]
  rcases eq_or_ne x y with hxy | hxy
  · subst hxy; simp
  · simp [hxy, Ne.symm hxy]

theorem kmtFhatParseval (a b : ℤ → ℂ) (ha : Summable fun x : ℤ => ‖a x‖) (hb : Summable fun x : ℤ => ‖b x‖) :
    (∑' x : ℤ, a x * star (b x)) = ∫ t in (0 : ℝ)..1, Work.A3.kmtFhat a t * star (Work.A3.kmtFhat b t) := by
  have hprod : ∀ t : ℝ, Work.A3.kmtFhat a t * star (Work.A3.kmtFhat b t)
      = ∑' p : ℤ × ℤ, (a p.1 * star (b p.2)) * (Work.A3.parsevalE p.1 t * star (Work.A3.parsevalE p.2 t)) := by
    intro t
    have hb_star : star (Work.A3.kmtFhat b t)
        = ∑' y : ℤ, star (b y) * star (Work.A3.parsevalE y t) := by
      rw [show Work.A3.kmtFhat b t = ∑' y : ℤ, b y * Work.A3.parsevalE y t from rfl, tsum_star]
      exact tsum_congr (fun y => by rw [star_mul, mul_comm])
    rw [show Work.A3.kmtFhat a t = ∑' x : ℤ, a x * Work.A3.parsevalE x t from rfl, hb_star,
      tsum_mul_tsum_of_summable_norm (f := fun x : ℤ => a x * Work.A3.parsevalE x t)
        (g := fun y : ℤ => star (b y) * star (Work.A3.parsevalE y t)) ?_ ?_]
    · exact tsum_congr (fun p => by ring)
    · rw [show (fun x : ℤ => ‖a x * Work.A3.parsevalE x t‖) = fun x => ‖a x‖ from
        funext (fun x => by rw [norm_mul, norm_parsevalE x t, mul_one])]
      exact ha
    · rw [show (fun y : ℤ => ‖star (b y) * star (Work.A3.parsevalE y t)‖) = fun y => ‖b y‖ from
        funext (fun y => by rw [norm_mul, norm_star, norm_star, norm_parsevalE y t, mul_one])]
      exact hb
  have int_norm : ∀ p : ℤ × ℤ, ∫ t : ℝ, ‖(a p.1 * star (b p.2)) * (Work.A3.parsevalE p.1 t * star (Work.A3.parsevalE p.2 t))‖
      ∂(MeasureTheory.volume.restrict (Set.Ioc (0:ℝ) 1)) = ‖a p.1‖ * ‖b p.2‖ := by
    intro p
    have hc : ∀ t : ℝ, ‖(a p.1 * star (b p.2)) * (Work.A3.parsevalE p.1 t * star (Work.A3.parsevalE p.2 t))‖ = ‖a p.1‖ * ‖b p.2‖ := by
      intro t
      simp only [norm_mul, norm_star, norm_parsevalE, norm_one, mul_one]
    rw [show (fun t : ℝ => ‖(a p.1 * star (b p.2)) * (Work.A3.parsevalE p.1 t * star (Work.A3.parsevalE p.2 t))‖) = fun t : ℝ => ‖a p.1‖ * ‖b p.2‖ from funext hc]
    rw [MeasureTheory.integral_const]
    simp
  have hpt : ∀ p : ℤ × ℤ, ∫ t : ℝ, (a p.1 * star (b p.2)) * (Work.A3.parsevalE p.1 t * star (Work.A3.parsevalE p.2 t))
      ∂(MeasureTheory.volume.restrict (Set.Ioc (0:ℝ) 1)) = (a p.1 * star (b p.2)) * (if p.1 = p.2 then (1:ℂ) else 0) := by
    intro p
    rw [MeasureTheory.integral_const_mul, parsevalE_pair_integral p.1 p.2]
  have hFint : ∀ p : ℤ × ℤ, Integrable (fun t : ℝ => (a p.1 * star (b p.2)) * (Work.A3.parsevalE p.1 t * star (Work.A3.parsevalE p.2 t)))
      (MeasureTheory.volume.restrict (Set.Ioc (0:ℝ) 1)) := by
    intro p
    refine MeasureTheory.Integrable.mono' (MeasureTheory.integrable_const (‖a p.1‖ * ‖b p.2‖)) ?_ ?_
    · exact ((continuous_const.mul ((continuous_parsevalE p.1).mul (continuous_star.comp (continuous_parsevalE p.2)))).aestronglyMeasurable)
    · filter_upwards with t
      simp only [norm_mul, norm_star, norm_parsevalE, norm_one, mul_one]
      exact le_of_eq (by ring)
  have hFs : Summable (fun p : ℤ × ℤ => ∫ t : ℝ, ‖(a p.1 * star (b p.2)) * (Work.A3.parsevalE p.1 t * star (Work.A3.parsevalE p.2 t))‖
      ∂(MeasureTheory.volume.restrict (Set.Ioc (0:ℝ) 1))) := by
    rw [show (fun p : ℤ × ℤ => ∫ t : ℝ, ‖(a p.1 * star (b p.2)) * (Work.A3.parsevalE p.1 t * star (Work.A3.parsevalE p.2 t))‖
        ∂(MeasureTheory.volume.restrict (Set.Ioc (0:ℝ) 1))) = fun p : ℤ × ℤ => ‖a p.1‖ * ‖b p.2‖ from funext int_norm]
    exact (Summable.mul_norm ha hb).congr (fun p => by rw [norm_mul])
  have hfub := MeasureTheory.integral_tsum_of_summable_integral_norm
    (F := fun (p : ℤ × ℤ) (t : ℝ) => (a p.1 * star (b p.2)) * (Work.A3.parsevalE p.1 t * star (Work.A3.parsevalE p.2 t)))
    hFint hFs
  have hdiag : (∑' p : ℤ × ℤ, (a p.1 * star (b p.2)) * (if p.1 = p.2 then (1:ℂ) else 0)) = ∑' x : ℤ, a x * star (b x) := by
    have hsum : Summable (fun p : ℤ × ℤ => (a p.1 * star (b p.2)) * (if p.1 = p.2 then (1:ℂ) else 0)) := by
      refine Summable.of_norm_bounded ((Summable.mul_norm ha hb).congr (fun p => by rw [norm_mul])) (fun p => ?_)
      simp only [norm_mul, norm_star]
      have hnn : (0:ℝ) ≤ ‖a p.1‖ * ‖b p.2‖ := mul_nonneg (norm_nonneg _) (norm_nonneg _)
      split_ifs with h
      · simp only [norm_one, mul_one]; exact le_rfl
      · simp only [norm_zero, mul_zero]; exact hnn
    rw [hsum.tsum_prod]
    refine tsum_congr (fun x => ?_)
    rw [tsum_eq_single x (fun y hy => by simp [Ne.symm hy])]
    simp
  rw [intervalIntegral.integral_of_le (by norm_num : (0:ℝ) ≤ 1)]
  rw [show (∫ t : ℝ, Work.A3.kmtFhat a t * star (Work.A3.kmtFhat b t) ∂(MeasureTheory.volume.restrict (Set.Ioc (0:ℝ) 1)))
      = ∫ t : ℝ, (∑' p : ℤ × ℤ, (a p.1 * star (b p.2)) * (Work.A3.parsevalE p.1 t * star (Work.A3.parsevalE p.2 t)))
          ∂(MeasureTheory.volume.restrict (Set.Ioc (0:ℝ) 1)) from by
        rw [show (fun t : ℝ => Work.A3.kmtFhat a t * star (Work.A3.kmtFhat b t))
            = fun t : ℝ => ∑' p : ℤ × ℤ, (a p.1 * star (b p.2)) * (Work.A3.parsevalE p.1 t * star (Work.A3.parsevalE p.2 t)) from funext hprod]]
  rw [← hfub]
  rw [show (∑' p : ℤ × ℤ, ∫ t : ℝ, (a p.1 * star (b p.2)) * (Work.A3.parsevalE p.1 t * star (Work.A3.parsevalE p.2 t))
        ∂(MeasureTheory.volume.restrict (Set.Ioc (0:ℝ) 1)))
      = ∑' p : ℤ × ℤ, (a p.1 * star (b p.2)) * (if p.1 = p.2 then (1:ℂ) else 0) from tsum_congr hpt]
  exact hdiag.symm

end

end Work.KMTAreas.A4
