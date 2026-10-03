import Mathlib
import Submission.Work.Pert.pert2v2.steps

namespace Work.Pert.pert2v2

theorem step_bounds {Ξ : ℝ} {ρ : ℂ} {F : ℂ → ℂ} {a : ℂ}
    (hρre : |ρ.re - 1| ≤ 1 / 32) (hρim : |ρ.im| ≤ 1 / 32)
    (hd : ‖F a - (a + ρ)‖ ≤ 1 / 64) :
    a.re + 15 / 16 ≤ (F a).re ∧ (F a).re ≤ a.re + 9 / 8 ∧
      (F a).im ≤ a.im + 3 / 64 ∧
      (a.im ≤ 0 → (F a).im ≤ 0 →
        Work.Pert.margB_g Ξ a - 35 / 32 ≤ Work.Pert.margB_g Ξ (F a)) := by
  -- componentwise bounds on the error `F a - (a + ρ)`
  have hre : |(F a).re - (a.re + ρ.re)| ≤ 1 / 64 := by
    have h : (F a).re - (a.re + ρ.re) = (F a - (a + ρ)).re := by simp [Complex.sub_re]
    rw [h]
    exact le_trans (Complex.abs_re_le_norm _) hd
  have him : |(F a).im - (a.im + ρ.im)| ≤ 1 / 64 := by
    have h : (F a).im - (a.im + ρ.im) = (F a - (a + ρ)).im := by simp [Complex.sub_im]
    rw [h]
    exact le_trans (Complex.abs_im_le_norm _) hd
  have hρrel : (31 : ℝ) / 32 ≤ ρ.re := by have := (abs_le.mp hρre).1; linarith
  have hρreu : ρ.re ≤ (33 : ℝ) / 32 := by have := (abs_le.mp hρre).2; linarith
  have hρimu : ρ.im ≤ (1 : ℝ) / 32 := by have := (abs_le.mp hρim).2; linarith
  have hrelo : -((1 : ℝ) / 64) ≤ (F a).re - (a.re + ρ.re) := (abs_le.mp hre).1
  have hrehi : (F a).re - (a.re + ρ.re) ≤ (1 : ℝ) / 64 := (abs_le.mp hre).2
  have himhi : (F a).im - (a.im + ρ.im) ≤ (1 : ℝ) / 64 := (abs_le.mp him).2
  have hFre_lo : a.re + 15 / 16 ≤ (F a).re := by linarith
  have hFre_hi : (F a).re ≤ a.re + 9 / 8 := by linarith
  have hFre_hi' : (F a).re ≤ a.re + 67 / 64 := by linarith
  have hFim_hi : (F a).im ≤ a.im + 3 / 64 := by linarith
  refine ⟨hFre_lo, hFre_hi, hFim_hi, ?_⟩
  intro hai hFi
  rw [Work.Pert.margB_g, Work.Pert.margB_g, abs_of_nonpos hai, abs_of_nonpos hFi]
  linarith

end Work.Pert.pert2v2
