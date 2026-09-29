import Mathlib
import Submission.Work.Cert.Spec
import Submission.Work.APsi.psiA_facts
import Submission.Work.Haupt.haupt_facts

namespace Work.Cert.ACore

open Submission.CDTPlan Metric

/-! ## Continuity of `T ↦ log ‖φ_A(rot t)‖`

The three maps `phiAfam k` (`k : Fin 3`) are the rescalings `z ↦ φ_A(c_k · z)` of `φ_A = h ∘ ψ_A`
by the constants `c = (1/10⁴, 283/500, 1)`.  Since `ψ_A` maps the closed unit disc into the open
unit disc, `φ_A` is continuous on the closed unit disc (`hM.1.continuousOn` composed with `hP.1`),
and `φ_A` vanishes there only at `0` (`hP.2.2.2.1`, `hM.2.2.1`, `hP.2.2.2.2`).  Composing with
the parametrisation `t ↦ rot t = e^{2πit}` of the unit circle (of norm `1` and never `0`) and with
`Real.log` on `{0}ᶜ` gives the result. -/

/-- `φ_A = h ∘ ψ_A` is continuous on the closed unit disc: `ψ_A` maps it into the open unit disc
on which `h` is holomorphic. -/
theorem phiA_continuousOn_closedBall :
    ContinuousOn phiA (closedBall (0 : ℂ) 1) := by
  have hP := Work.APsi.psiA_facts
  have hM := Work.Haupt.haupt_facts
  have hmaps : Set.MapsTo psiA (closedBall (0 : ℂ) 1) (ball (0 : ℂ) 1) := by
    intro z hz
    simpa only [mem_ball, dist_zero_right] using hP.2.2.2.1 z hz
  change ContinuousOn (fun z : ℂ => hauptH (psiA z)) (closedBall (0 : ℂ) 1)
  exact (hM.1.continuousOn).comp hP.1 hmaps

/-- `φ_A` vanishes on the closed unit disc only at the origin. -/
theorem phiA_ne_zero_of_ne_zero {z : ℂ} (hz : z ∈ closedBall (0 : ℂ) 1) (hz0 : z ≠ 0) :
    phiA z ≠ 0 := by
  intro hzphi
  have hP := Work.APsi.psiA_facts
  have hM := Work.Haupt.haupt_facts
  have hψmem : psiA z ∈ ball (0 : ℂ) 1 := by
    simpa only [mem_ball, dist_zero_right] using hP.2.2.2.1 z hz
  have hψ0 : psiA z = 0 := hM.2.2.1 (psiA z) hψmem (by simpa only [phiA] using hzphi)
  exact hz0 (hP.2.2.2.2 z hz hψ0)

/-- `t ↦ log ‖φ_A(c · rot t)‖` is continuous on `[0,1]` for every rescaling constant `c ≠ 0`
of modulus `≤ 1`. -/
theorem continuousOn_circleLog_const_mul (c : ℂ) (hc : ‖c‖ ≤ 1) (hc0 : c ≠ 0) :
    ContinuousOn (circleLog (fun z : ℂ => phiA (c * z))) (Set.Icc (0 : ℝ) 1) := by
  have hcont : ContinuousOn (fun z : ℂ => phiA (c * z)) (closedBall (0 : ℂ) 1) := by
    refine phiA_continuousOn_closedBall.comp ?_ ?_
    · exact (continuous_const.mul continuous_id).continuousOn
    · intro z hz
      simp only [mem_closedBall, dist_zero_right] at hz ⊢
      rw [norm_mul]
      calc ‖c‖ * ‖z‖ ≤ 1 * 1 := mul_le_mul hc hz (norm_nonneg _) zero_le_one
        _ = 1 := by norm_num
  have hparam : Continuous (fun t : ℝ => rot t) := by
    change Continuous (fun t : ℝ => Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (t : ℂ)))
    fun_prop
  have hmaps : Set.MapsTo (fun t : ℝ => rot t) (Set.Icc (0 : ℝ) 1) (closedBall (0 : ℂ) 1) := by
    intro t _
    simp only [mem_closedBall, dist_zero_right]
    rw [Work.APsi.norm_rot]
  have hcomp : ContinuousOn (fun t : ℝ => phiA (c * rot t)) (Set.Icc (0 : ℝ) 1) :=
    hcont.comp hparam.continuousOn hmaps
  have hne : ∀ t ∈ Set.Icc (0 : ℝ) 1, ‖phiA (c * rot t)‖ ≠ 0 := by
    intro t _
    rw [norm_ne_zero_iff]
    refine phiA_ne_zero_of_ne_zero ?_ ?_
    · simp only [mem_closedBall, dist_zero_right]
      rw [norm_mul, Work.APsi.norm_rot, mul_one]
      exact hc
    · exact mul_ne_zero hc0 (Work.APsi.rot_ne_zero t)
  have hfun : circleLog (fun z : ℂ => phiA (c * z)) =
      fun t : ℝ => Real.log ‖phiA (c * rot t)‖ := by
    funext t
    simp only [circleLog, rot]
  rw [hfun]
  exact hcomp.norm.log hne

open Submission.CDTPlan in
/-- Continuity of the three functions `t ↦ log ‖φ_A(c_k · e^{2πit})‖` (`k : Fin 3`) on `[0,1]`,
one of the hypotheses of `Work.ArcCert.rearrInt_arc_bound`.  `ψ_A` is continuous on the closed unit
disc and maps it into the open disc (`PsiAFacts`), `h` is holomorphic on the open disc
(`HauptFacts`), and `φ_A = h ∘ ψ_A` does not vanish on the closed disc except at `0`, while
`c_k · e^{2πit} ≠ 0`.

HINT: `Work.APsi.psiA_facts : PsiAFacts` and `Work.Haupt.haupt_facts : HauptFacts` are both
sorry-free theorems in the workspace (import the modules, do not reprove them).  Useful route:
(i) `ContinuousOn phiA (closedBall 0 1)` from `hP.1` (`ContinuousOn psiA _`) composed with
`hM.1.continuousOn` (`DifferentiableOn hauptH (ball 0 1)`), the `MapsTo` being
`hP.2.2.1 : ∀ z ∈ closedBall 0 1, ‖psiA z‖ < 1`;
(ii) `phiA z ≠ 0` for `‖z‖ ≤ 1`, `z ≠ 0`: if `phiA z = 0`, then `psiA z ∈ ball 0 1` and
`hM.2.2.1 : ∀ q ∈ ball 0 1, hauptH q = 0 → q = 0` give `psiA z = 0`, and
`hP.2.2.2 : ∀ z ∈ closedBall 0 1, psiA z = 0 → z = 0` contradicts `z ≠ 0`;
(iii) `t ↦ c_k * exp (2πit)` is continuous, lands in `closedBall 0 1`, and never vanishes;
(iv) `Real.continuousOn_log` (domain `{0}ᶜ`) composed with `t ↦ ‖phiA (c_k * exp (2πit))‖`.
Note `circleLog φ t = Real.log ‖φ (rot t)‖` and `rot t = Complex.exp (2*π*I*t)`. -/
theorem continuousOn_circleLog_phiAfam (k : Fin 3) :
    ContinuousOn (circleLog (phiAfam k)) (Set.Icc (0 : ℝ) 1) := by
  have hk : k = 0 ∨ k = 1 ∨ k = 2 := by fin_cases k <;> simp
  rcases hk with rfl | rfl | rfl
  · rw [show phiAfam 0 = (fun z : ℂ => phiA ((1 / 10000 : ℂ) * z)) from by
      funext z; simp [phiAfam]; congr 1; ring]
    exact continuousOn_circleLog_const_mul (1 / 10000 : ℂ) (by norm_num) (by norm_num)
  · rw [show phiAfam 1 = (fun z : ℂ => phiA ((283 / 500 : ℂ) * z)) from by
      funext z; simp [phiAfam]; congr 1; ring]
    exact continuousOn_circleLog_const_mul (283 / 500 : ℂ) (by norm_num) (by norm_num)
  · rw [show phiAfam 2 = (fun z : ℂ => phiA ((1 : ℂ) * z)) from by
      funext z; simp [phiAfam]]
    simpa using continuousOn_circleLog_const_mul (1 : ℂ) (by norm_num) (by norm_num)

end Work.Cert.ACore
