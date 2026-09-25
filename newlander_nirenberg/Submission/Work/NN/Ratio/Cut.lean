/-
# The flexible cutoff with a tight plateau

`rCut a b ζ = σ((b² - ‖ζ‖²)/(b² - a²))` where `σ = Real.smoothTransition`; it is `1` for
`‖ζ‖ ≤ a`, `0` for `b ≤ ‖ζ‖`, smooth, bounded by `1`, with `∂̄χ = 0` on both regions.  Its
`∂̄`-derivative is bounded and Lipschitz (by compactness).

The plateau/support ratio `a/b` can be taken arbitrarily close to `1`, which is what makes
the telescoping construction solve `∂̄u = f` on a polydisc arbitrarily close to the polydisc
where the data are controlled.
-/
import Mathlib
import Submission.Work.NN.Ratio.Defs
import Submission.Work.CR.Flat.Cauchy.openCutAux

noncomputable section

open scoped NNReal ENNReal ContDiff
open Set MeasureTheory

namespace Work.NN.Ratio

/-- The radial profile of the cutoff: `rCut a b ζ = (rCutR a b (‖ζ‖²) : ℂ)`. -/
def rCutR (a b : ℝ) (s : ℝ) : ℝ :=
  Real.smoothTransition ((b ^ 2 - s) / (b ^ 2 - a ^ 2))

/-- The flexible cutoff. -/
def rCut (a b : ℝ) (ζ : ℂ) : ℂ :=
  (rCutR a b (Complex.normSq ζ) : ℂ)

lemma rCut_eq_fun (a b : ℝ) : rCut a b = fun w : ℂ => (rCutR a b (Complex.normSq w) : ℂ) :=
  funext fun w => rfl

lemma rCutR_nonneg (a b : ℝ) (s : ℝ) : 0 ≤ rCutR a b s := Real.smoothTransition.nonneg _

lemma rCutR_le_one (a b : ℝ) (s : ℝ) : rCutR a b s ≤ 1 := Real.smoothTransition.le_one _

lemma sq_lt_sq_of_pos {a b : ℝ} (ha : 0 ≤ a) (hab : a < b) : a ^ 2 < b ^ 2 := by
  nlinarith

lemma rCutR_eq_one_of_le {a b s : ℝ} (ha : 0 ≤ a) (hab : a < b) (hs : s ≤ a ^ 2) :
    rCutR a b s = 1 := by
  rw [rCutR, Real.smoothTransition.one_of_one_le]
  rw [le_div_iff₀ (by nlinarith [sq_lt_sq_of_pos ha hab])]
  linarith

lemma rCutR_eq_zero_of_le {a b s : ℝ} (ha : 0 ≤ a) (hab : a < b) (hs : b ^ 2 ≤ s) :
    rCutR a b s = 0 := by
  rw [rCutR, Real.smoothTransition.zero_of_nonpos]
  apply div_nonpos_of_nonpos_of_nonneg _ (le_of_lt (by nlinarith [sq_lt_sq_of_pos ha hab]))
  linarith

lemma contDiff_rCutR (a b : ℝ) : ContDiff ℝ ∞ (rCutR a b) := by
  have h : ContDiff ℝ ∞ (fun s : ℝ => (b ^ 2 - s) / (b ^ 2 - a ^ 2)) := by
    have h' : (fun s : ℝ => (b ^ 2 - s) / (b ^ 2 - a ^ 2))
        = fun s : ℝ => (b ^ 2 - s) * (b ^ 2 - a ^ 2)⁻¹ := by
      funext s; rw [div_eq_mul_inv]
    rw [h']; fun_prop
  exact (Real.smoothTransition.contDiff (n := ⊤)).comp h

lemma contDiff_normSq_aux : ContDiff ℝ ∞ (fun ζ : ℂ => Complex.normSq ζ) := by
  have h : (fun ζ : ℂ => Complex.normSq ζ)
      = fun ζ : ℂ => Complex.reCLM ζ * Complex.reCLM ζ + Complex.imCLM ζ * Complex.imCLM ζ := by
    funext ζ; rw [Complex.normSq_apply]; rfl
  rw [h]; fun_prop

lemma contDiff_rCut (a b : ℝ) : ContDiff ℝ ∞ (rCut a b) := by
  rw [rCut_eq_fun]
  exact (Complex.ofRealCLM.contDiff).comp ((contDiff_rCutR a b).comp contDiff_normSq_aux)

lemma rCut_eq_one_of_norm_le {a b : ℝ} (ha : 0 ≤ a) (hab : a < b) {ζ : ℂ} (h : ‖ζ‖ ≤ a) :
    rCut a b ζ = 1 := by
  have hs : Complex.normSq ζ ≤ a ^ 2 := by
    rw [Complex.normSq_eq_norm_sq]
    exact pow_le_pow_left₀ (norm_nonneg ζ) h 2
  rw [rCut, rCutR_eq_one_of_le ha hab hs]
  norm_num

lemma rCut_eq_zero_of_le_norm {a b : ℝ} (ha : 0 ≤ a) (hab : a < b) {ζ : ℂ} (h : b ≤ ‖ζ‖) :
    rCut a b ζ = 0 := by
  have hb : (0 : ℝ) ≤ b := le_trans ha (le_of_lt hab)
  have hs : b ^ 2 ≤ Complex.normSq ζ := by
    rw [Complex.normSq_eq_norm_sq]
    exact pow_le_pow_left₀ hb h 2
  rw [rCut, rCutR_eq_zero_of_le ha hab hs]
  norm_num

lemma norm_rCut_le_one (a b : ℝ) (ζ : ℂ) : ‖rCut a b ζ‖ ≤ 1 := by
  rw [rCut]
  have h1 : 0 ≤ rCutR a b (Complex.normSq ζ) := rCutR_nonneg a b _
  have h2 : rCutR a b (Complex.normSq ζ) ≤ 1 := rCutR_le_one a b _
  have h3 : ‖((rCutR a b (Complex.normSq ζ)) : ℂ)‖ = |rCutR a b (Complex.normSq ζ)| := by simp
  rw [h3, abs_of_nonneg h1]; exact h2

lemma deriv_rCutR_eq_zero_of_le {a b s : ℝ} (ha : 0 ≤ a) (hab : a < b) (hs : s ≤ a ^ 2) :
    deriv (rCutR a b) s = 0 := by
  have hdiff : DifferentiableAt ℝ (rCutR a b) s := (contDiff_rCutR a b).differentiable (by simp) s
  have hu : UniqueDiffWithinAt ℝ (Iic s) s := uniqueDiffWithinAt_Iic s
  have h1 : HasDerivWithinAt (rCutR a b) 0 (Iic s) s :=
    (hasDerivWithinAt_const s (Iic s) (1 : ℝ)).congr
      (fun x hx => rCutR_eq_one_of_le ha hab (le_trans hx hs)) (rCutR_eq_one_of_le ha hab hs)
  have h2 : HasDerivWithinAt (rCutR a b) (deriv (rCutR a b) s) (Iic s) s :=
    hdiff.hasDerivAt.hasDerivWithinAt
  rw [← h2.derivWithin hu, h1.derivWithin hu]

lemma deriv_rCutR_eq_zero_of_le' {a b s : ℝ} (ha : 0 ≤ a) (hab : a < b) (hs : b ^ 2 ≤ s) :
    deriv (rCutR a b) s = 0 := by
  have hdiff : DifferentiableAt ℝ (rCutR a b) s := (contDiff_rCutR a b).differentiable (by simp) s
  have hu : UniqueDiffWithinAt ℝ (Ici s) s := uniqueDiffWithinAt_Ici s
  have h1 : HasDerivWithinAt (rCutR a b) 0 (Ici s) s :=
    (hasDerivWithinAt_const s (Ici s) (0 : ℝ)).congr
      (fun x hx => rCutR_eq_zero_of_le ha hab (le_trans hs hx)) (rCutR_eq_zero_of_le ha hab hs)
  have h2 : HasDerivWithinAt (rCutR a b) (deriv (rCutR a b) s) (Ici s) s :=
    hdiff.hasDerivAt.hasDerivWithinAt
  rw [← h2.derivWithin hu, h1.derivWithin hu]

lemma dbarC_rCut_eq (a b : ℝ) (ζ : ℂ) :
    Work.CR.Flat.dbarC (rCut a b) ζ
      = ((deriv (rCutR a b) (Complex.normSq ζ) : ℝ) : ℂ) * ζ := by
  rw [rCut_eq_fun,
    Work.CR.Flat.dbarC_comp_normSq_aux (rCutR a b) ((contDiff_rCutR a b).differentiable (by simp)) ζ]

lemma dbarC_rCut_eq_zero_of_norm_le {a b : ℝ} (ha : 0 ≤ a) (hab : a < b) {ζ : ℂ}
    (h : ‖ζ‖ ≤ a) : Work.CR.Flat.dbarC (rCut a b) ζ = 0 := by
  rw [dbarC_rCut_eq, deriv_rCutR_eq_zero_of_le ha hab ?_, Complex.ofReal_zero, zero_mul]
  rw [Complex.normSq_eq_norm_sq]
  exact pow_le_pow_left₀ (norm_nonneg ζ) h 2

lemma dbarC_rCut_eq_zero_of_le_norm {a b : ℝ} (ha : 0 ≤ a) (hab : a < b) {ζ : ℂ}
    (h : b ≤ ‖ζ‖) : Work.CR.Flat.dbarC (rCut a b) ζ = 0 := by
  rw [dbarC_rCut_eq, deriv_rCutR_eq_zero_of_le' ha hab ?_, Complex.ofReal_zero, zero_mul]
  rw [Complex.normSq_eq_norm_sq]
  have hb : (0 : ℝ) ≤ b := le_trans ha (le_of_lt hab)
  exact pow_le_pow_left₀ hb h 2

lemma hasCompactSupport_rCut {a b : ℝ} (ha : 0 ≤ a) (hab : a < b) :
    HasCompactSupport (rCut a b) := by
  refine HasCompactSupport.intro (K := Metric.closedBall (0 : ℂ) b) (isCompact_closedBall (0 : ℂ) b) ?_
  intro x hx
  have hx' : b ≤ ‖x‖ := by
    by_contra h
    exact hx (by rw [Metric.mem_closedBall, dist_zero_right]; exact le_of_lt (not_le.mp h))
  exact rCut_eq_zero_of_le_norm ha hab hx'

lemma contDiff_dbarC_rCut (a b : ℝ) : ContDiff ℝ ∞ (fun ζ : ℂ => Work.CR.Flat.dbarC (rCut a b) ζ) := by
  have hfd : ContDiff ℝ ∞ (fderiv ℝ (rCut a b)) := (contDiff_rCut a b).fderiv_right (m := ∞) le_rfl
  have h1 : ContDiff ℝ ∞ (fun z : ℂ => fderiv ℝ (rCut a b) z 1) := hfd.clm_apply contDiff_const
  have hI : ContDiff ℝ ∞ (fun z : ℂ => fderiv ℝ (rCut a b) z Complex.I) :=
    hfd.clm_apply contDiff_const
  rw [show Work.CR.Flat.dbarC (rCut a b) = fun z => (1 / 2 : ℂ) *
      ((fderiv ℝ (rCut a b) z) 1 + Complex.I * (fderiv ℝ (rCut a b) z) Complex.I) from rfl]
  exact contDiff_const.mul (h1.add (contDiff_const.mul hI))

lemma hasCompactSupport_dbarC_rCut {a b : ℝ} (ha : 0 ≤ a) (hab : a < b) :
    HasCompactSupport (fun ζ : ℂ => Work.CR.Flat.dbarC (rCut a b) ζ) := by
  refine HasCompactSupport.intro (K := Metric.closedBall (0 : ℂ) b) (isCompact_closedBall (0 : ℂ) b) ?_
  intro x hx
  have hx' : b ≤ ‖x‖ := by
    by_contra h
    exact hx (by rw [Metric.mem_closedBall, dist_zero_right]; exact le_of_lt (not_le.mp h))
  exact dbarC_rCut_eq_zero_of_le_norm ha hab hx'

lemma dbarC_rCut_bounded {a b : ℝ} (ha : 0 ≤ a) (hab : a < b) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ζ : ℂ, ‖Work.CR.Flat.dbarC (rCut a b) ζ‖ ≤ C := by
  obtain ⟨C, hC⟩ := (hasCompactSupport_dbarC_rCut ha hab).exists_bound_of_continuous
    (contDiff_dbarC_rCut a b).continuous
  exact ⟨max C 0, le_max_right _ _, fun ζ => (hC ζ).trans (le_max_left _ _)⟩

lemma dbarC_rCut_lipschitz {a b : ℝ} (ha : 0 ≤ a) (hab : a < b) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ζ ζ' : ℂ,
      ‖Work.CR.Flat.dbarC (rCut a b) ζ - Work.CR.Flat.dbarC (rCut a b) ζ'‖ ≤ C * ‖ζ - ζ'‖ := by
  obtain ⟨C, hC⟩ := ContDiff.lipschitzWith_of_hasCompactSupport (hasCompactSupport_dbarC_rCut ha hab)
    (contDiff_dbarC_rCut a b) (by simp)
  refine ⟨(C : ℝ), C.coe_nonneg, fun ζ ζ' => ?_⟩
  simpa only [dist_eq_norm] using hC.dist_le_mul ζ ζ'

lemma rCut_lipschitz {a b : ℝ} (ha : 0 ≤ a) (hab : a < b) :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ ζ ζ' : ℂ, ‖rCut a b ζ - rCut a b ζ'‖ ≤ L * ‖ζ - ζ'‖ := by
  obtain ⟨C, hC⟩ := ContDiff.lipschitzWith_of_hasCompactSupport (hasCompactSupport_rCut ha hab)
    (contDiff_rCut a b) (by simp)
  refine ⟨(C : ℝ), C.coe_nonneg, fun ζ ζ' => ?_⟩
  simpa only [dist_eq_norm] using hC.dist_le_mul ζ ζ'

/-- The flexible cutoff provides the geometric data of the telescoping construction. -/
theorem exists_geom {n : ℕ} {a b T r e : ℝ} (ha : 0 < a) (hab : a < b) (hbT : b < T)
    (hea : e < a) (hr : 2 * b ≤ r) (hr0 : 0 < r) : Nonempty (Geom n) := by
  obtain ⟨cχ, hcχ0, hcχ⟩ := dbarC_rCut_bounded (le_of_lt ha) hab
  obtain ⟨cχ', hcχ'0, hcχ'⟩ := dbarC_rCut_lipschitz (le_of_lt ha) hab
  obtain ⟨L, hL0, hL⟩ := rCut_lipschitz (le_of_lt ha) hab
  exact ⟨Geom.mk a b T r e ha hab hbT hea hr hr0 (rCut a b)
    (contDiff_rCut a b)
    (fun ζ h => rCut_eq_one_of_norm_le (le_of_lt ha) hab h)
    (fun ζ h => rCut_eq_zero_of_le_norm (le_of_lt ha) hab h)
    (norm_rCut_le_one a b)
    (fun ζ h => dbarC_rCut_eq_zero_of_norm_le (le_of_lt ha) hab h)
    (fun ζ h => dbarC_rCut_eq_zero_of_le_norm (le_of_lt ha) hab h)
    cχ hcχ0 hcχ cχ' hcχ'0 hcχ' L hL0 hL⟩

end Work.NN.Ratio
