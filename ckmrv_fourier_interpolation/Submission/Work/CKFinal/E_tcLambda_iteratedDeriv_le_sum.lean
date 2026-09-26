import Mathlib
import Submission.Work.Asymptotics.E_TailClosed

noncomputable section

open scoped Topology ContDiff

namespace Work.CKFinal

open Work.Asymptotics

/-- Triangle inequality for the `l`-th iterated derivative of a sum of four smooth functions:
`‖dˡ(f₀+f₁+f₂+f₃)‖ ≤ ‖dˡf₀‖ + ‖dˡf₁‖ + ‖dˡf₂‖ + ‖dˡf₃‖`. -/
lemma E_norm_iteratedDeriv_four_le {f0 f1 f2 f3 : ℝ → ℂ} {l : ℕ} {x : ℝ}
    (h0 : ContDiffAt ℝ (l : ℕ∞) f0 x) (h1 : ContDiffAt ℝ (l : ℕ∞) f1 x)
    (h2 : ContDiffAt ℝ (l : ℕ∞) f2 x) (h3 : ContDiffAt ℝ (l : ℕ∞) f3 x) :
    ‖iteratedDeriv l (f0 + f1 + f2 + f3) x‖
      ≤ ‖iteratedDeriv l f0 x‖ + ‖iteratedDeriv l f1 x‖ + ‖iteratedDeriv l f2 x‖
        + ‖iteratedDeriv l f3 x‖ := by
  have h01 : ContDiffAt ℝ (l : ℕ∞) (f0 + f1) x := h0.add h1
  have h012 : ContDiffAt ℝ (l : ℕ∞) ((f0 + f1) + f2) x := h01.add h2
  have hkey : iteratedDeriv l (f0 + f1 + f2 + f3) x
      = iteratedDeriv l f0 x + iteratedDeriv l f1 x + iteratedDeriv l f2 x
        + iteratedDeriv l f3 x := by
    rw [iteratedDeriv_add h012 h3, iteratedDeriv_add h01 h2, iteratedDeriv_add h0 h1]
  rw [hkey]
  have hd := norm_add_le (iteratedDeriv l f0 x + iteratedDeriv l f1 x + iteratedDeriv l f2 x)
    (iteratedDeriv l f3 x)
  have hd2 := norm_add_le (iteratedDeriv l f0 x + iteratedDeriv l f1 x) (iteratedDeriv l f2 x)
  have hd3 := norm_add_le (iteratedDeriv l f0 x) (iteratedDeriv l f1 x)
  linarith [hd, hd2, hd3, norm_nonneg (iteratedDeriv l f0 x), norm_nonneg (iteratedDeriv l f1 x),
    norm_nonneg (iteratedDeriv l f2 x), norm_nonneg (iteratedDeriv l f3 x)]

theorem E_tcLambda_iteratedDeriv_le_sum (G : Fin 2 → Fin 2 → UpperHalfPlane → ℂ) (B : ℝ) (w : UpperHalfPlane) (l : ℕ) (x : ℝ) :
    ‖iteratedDeriv l (Work.Asymptotics.tcLambda G B w) x‖
      ≤ ‖iteratedDeriv l (Work.Asymptotics.E_sh1 B) x‖ * ‖G 0 0 w‖
        + ‖iteratedDeriv l (Work.Asymptotics.E_sh2 B) x‖ * ‖G 0 1 w‖
        + ‖iteratedDeriv l (Work.Asymptotics.E_sh3 B) x‖ * ‖G 1 0 w‖
        + ‖iteratedDeriv l (Work.Asymptotics.E_sh4 B) x‖ * ‖G 1 1 w‖ := by
  have hF : tcLambda G B w = fun y : ℝ => (E_sh1 B y * G 0 0 w) + (E_sh2 B y * G 0 1 w)
      + (E_sh3 B y * G 1 0 w) + (E_sh4 B y * G 1 1 w) := by
    funext y
    unfold tcLambda E_sh1 E_sh2 E_sh3 E_sh4 tcF1 tcF2 tcF3 tcF4
    ring_nf
  have c3 : ContDiff ℝ ω (E_sh3 B) :=
    contDiff_tcF3.mul (contDiff_exp_negB B |>.comp (contDiff_id.sub contDiff_const))
  have c4 : ContDiff ℝ ω (E_sh4 B) :=
    contDiff_tcF4 B |>.mul (contDiff_exp_negB B |>.comp (contDiff_id.sub contDiff_const))
  have hd0 : ContDiffAt ℝ (l : ℕ∞) (fun y : ℝ => E_sh1 B y * G 0 0 w) x :=
    ((contDiff_E_sh1 B).mul contDiff_const).contDiffAt.of_le le_top
  have hd1 : ContDiffAt ℝ (l : ℕ∞) (fun y : ℝ => E_sh2 B y * G 0 1 w) x :=
    ((contDiff_E_sh2 B).mul contDiff_const).contDiffAt.of_le le_top
  have hd2 : ContDiffAt ℝ (l : ℕ∞) (fun y : ℝ => E_sh3 B y * G 1 0 w) x :=
    (c3.mul contDiff_const).contDiffAt.of_le le_top
  have hd3 : ContDiffAt ℝ (l : ℕ∞) (fun y : ℝ => E_sh4 B y * G 1 1 w) x :=
    (c4.mul contDiff_const).contDiffAt.of_le le_top
  rw [hF]
  rw [show (fun y : ℝ => (E_sh1 B y * G 0 0 w) + (E_sh2 B y * G 0 1 w)
        + (E_sh3 B y * G 1 0 w) + (E_sh4 B y * G 1 1 w))
      = (fun y : ℝ => E_sh1 B y * G 0 0 w) + (fun y : ℝ => E_sh2 B y * G 0 1 w)
        + (fun y : ℝ => E_sh3 B y * G 1 0 w) + (fun y : ℝ => E_sh4 B y * G 1 1 w) from rfl]
  refine le_trans (E_norm_iteratedDeriv_four_le hd0 hd1 hd2 hd3) ?_
  rw [iteratedDeriv_mul_const_field (n := l) (E_sh1 B) (G 0 0 w), norm_mul,
    iteratedDeriv_mul_const_field (n := l) (E_sh2 B) (G 0 1 w), norm_mul,
    iteratedDeriv_mul_const_field (n := l) (E_sh3 B) (G 1 0 w), norm_mul,
    iteratedDeriv_mul_const_field (n := l) (E_sh4 B) (G 1 1 w), norm_mul]

end Work.CKFinal
