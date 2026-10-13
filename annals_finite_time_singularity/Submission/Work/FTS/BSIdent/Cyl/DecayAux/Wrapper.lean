import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.FTS.BSIdent.Defs
import Submission.Work.FTS.BSIdent.Cyl.DecayAux.Basic
import Submission.Work.FTS.BSIdent.Cyl.DecayAux.Quadrant

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The pointwise bounds for `∂_z psiCore` and `∂_r psiCore` on the open quadrant
-/

noncomputable section

open scoped Topology

namespace Work.FTS.BSIdent.Cyl

set_option autoImplicit false
set_option maxHeartbeats 1000000

/-- **The bound on `∂_z ψ` on the open quadrant.** -/
theorem abs_pdZ_psiCore_le {G : ℝ → ℝ → ℝ} {p c b C₀ q lam r z : ℝ}
    (hC₀ : 0 ≤ C₀) (hq : 2 < q) (hlam : 0 < lam) (hp : 0 < p) (hb : 0 < b)
    (hr : 0 < r) (hz : 0 < z) (hpl : 3 ≤ p * lam)
    (hG : Work.Cyl.DiffAt2 G (Work.Cyl.rhoP r z ^ p / b) (Work.Cyl.thetaP r z))
    (hval : |G (Work.Cyl.rhoP r z ^ p / b) (Work.Cyl.thetaP r z)|
      ≤ C₀ * (Real.pi / 2 - Work.Cyl.thetaP r z) ^ q * (1 + Work.Cyl.rhoP r z ^ p / b) ^ (-lam))
    (hwd : |Work.Cyl.pdR G (Work.Cyl.rhoP r z ^ p / b) (Work.Cyl.thetaP r z)|
      ≤ C₀ * (Real.pi / 2 - Work.Cyl.thetaP r z) ^ q
        * (1 + Work.Cyl.rhoP r z ^ p / b) ^ (-lam - 1))
    (hth : |Work.Cyl.pdZ G (Work.Cyl.rhoP r z ^ p / b) (Work.Cyl.thetaP r z)|
      ≤ C₀ * (Real.pi / 2 - Work.Cyl.thetaP r z) ^ (q - 1)
        * (1 + Work.Cyl.rhoP r z ^ p / b) ^ (-lam)) :
    |Work.Cyl.pdZ (psiCore p c b G) r z|
      ≤ decayKzr p c C₀ q lam b / (1 + Work.Cyl.rhoP r z) := by
  rw [pdZ_psiCore_eq hG hr]
  refine abs_combination_bound (X := p * z * (Work.Cyl.rhoP r z ^ p / b)) (Y := r) (zc := z)
    hC₀ hq hlam hp hb hr hz hpl ?_ ?_ ?_ hval hwd hth
  · exact abs_snd_le_rhoP r z
  · rw [abs_mul, abs_mul, abs_of_nonneg hp.le,
      abs_of_nonneg (div_nonneg (Real.rpow_nonneg (Work.Cyl.rhoP_nonneg r z) p) hb.le)]
    have h1 : (0 : ℝ) ≤ Work.Cyl.rhoP r z ^ p / b :=
      div_nonneg (Real.rpow_nonneg (Work.Cyl.rhoP_nonneg r z) p) hb.le
    have h2 : p * |z| ≤ p * Work.Cyl.rhoP r z :=
      mul_le_mul_of_nonneg_left (abs_snd_le_rhoP r z) hp.le
    exact mul_le_mul_of_nonneg_right h2 h1
  · rw [abs_of_nonneg hr.le]; exact le_rhoP r z hr.le

/-- **The bound on `∂_r ψ` on the open quadrant.** -/
theorem abs_pdR_psiCore_le {G : ℝ → ℝ → ℝ} {p c b C₀ q lam r z : ℝ}
    (hC₀ : 0 ≤ C₀) (hq : 2 < q) (hlam : 0 < lam) (hp : 0 < p) (hb : 0 < b)
    (hr : 0 < r) (hz : 0 < z) (hpl : 3 ≤ p * lam)
    (hG : Work.Cyl.DiffAt2 G (Work.Cyl.rhoP r z ^ p / b) (Work.Cyl.thetaP r z))
    (hval : |G (Work.Cyl.rhoP r z ^ p / b) (Work.Cyl.thetaP r z)|
      ≤ C₀ * (Real.pi / 2 - Work.Cyl.thetaP r z) ^ q * (1 + Work.Cyl.rhoP r z ^ p / b) ^ (-lam))
    (hwd : |Work.Cyl.pdR G (Work.Cyl.rhoP r z ^ p / b) (Work.Cyl.thetaP r z)|
      ≤ C₀ * (Real.pi / 2 - Work.Cyl.thetaP r z) ^ q
        * (1 + Work.Cyl.rhoP r z ^ p / b) ^ (-lam - 1))
    (hth : |Work.Cyl.pdZ G (Work.Cyl.rhoP r z ^ p / b) (Work.Cyl.thetaP r z)|
      ≤ C₀ * (Real.pi / 2 - Work.Cyl.thetaP r z) ^ (q - 1)
        * (1 + Work.Cyl.rhoP r z ^ p / b) ^ (-lam)) :
    |Work.Cyl.pdR (psiCore p c b G) r z|
      ≤ decayKzr p c C₀ q lam b / (1 + Work.Cyl.rhoP r z) := by
  rw [pdR_psiCore_eq hG hr]
  refine abs_combination_bound (X := p * r * (Work.Cyl.rhoP r z ^ p / b)) (Y := -z) (zc := r)
    hC₀ hq hlam hp hb hr hz hpl ?_ ?_ ?_ hval hwd hth
  · rw [abs_of_nonneg hr.le]; exact le_rhoP r z hr.le
  · rw [abs_mul, abs_mul, abs_of_nonneg hp.le, abs_of_nonneg hr.le,
      abs_of_nonneg (div_nonneg (Real.rpow_nonneg (Work.Cyl.rhoP_nonneg r z) p) hb.le)]
    have h1 : (0 : ℝ) ≤ Work.Cyl.rhoP r z ^ p / b :=
      div_nonneg (Real.rpow_nonneg (Work.Cyl.rhoP_nonneg r z) p) hb.le
    have h2 : p * r ≤ p * Work.Cyl.rhoP r z :=
      mul_le_mul_of_nonneg_left (le_rhoP r z hr.le) hp.le
    exact mul_le_mul_of_nonneg_right h2 h1
  · rw [abs_neg]; exact abs_snd_le_rhoP r z

end Work.FTS.BSIdent.Cyl
