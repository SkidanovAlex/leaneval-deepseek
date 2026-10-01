import Mathlib
import Submission.Work.LinnikAreas.Density4.TestFun
import Submission.Work.LinnikAreas.Density4.testfun_basic
import Submission.Work.LinnikAreas.Density4.testfun_lapl_pos
import Submission.Work.LinnikAreas.Density4.fTregular

namespace Work.LinnikAreas.Density4

/-- The norm of a real number viewed in `ℂ` is the norm of the real number. -/
lemma fT_norm_ofReal_complex (a : ℝ) : ‖((a : ℝ) : ℂ)‖ = ‖a‖ := by simp

/-- Complexifying a real function commutes with taking the `n`-th iterated derivative:
`(ℝ ∋ t ↦ (f t : ℂ))^{(n)}(x) = (f^{(n)}(x) : ℂ)`, since `ℂ` sits in `ℝ` as a linear
isometry. -/
lemma fT_iteratedDeriv_ofReal_comp {f : ℝ → ℝ} {x : ℝ} {n : ℕ} (h : ContDiffAt ℝ n f x) :
    iteratedDeriv n (fun t : ℝ => ((f t : ℝ) : ℂ)) x = ((iteratedDeriv n f x : ℝ) : ℂ) := by
  show iteratedDeriv n (Complex.ofRealCLM ∘ f) x = _
  unfold iteratedDeriv
  rw [Complex.ofRealCLM.iteratedFDeriv_comp_left (n := (n : WithTop ℕ∞)) h le_rfl]
  simp only [ContinuousLinearMap.compContinuousMultilinearMap_coe, Function.comp_apply,
    Complex.ofRealCLM_apply]

/-- **HB §12**: the complexified §7 test function `t ↦ (f(t) : ℂ)` is continuous on `[0,2γ]`,
`C²` on `(0,2γ)`, and has a bounded second derivative there.  This is the form in which the
Laplace-transform manipulations of HB §5/§12 (`∫ e^{-zt} f(t) dt`, integration by parts, and
the resulting bound `|F(z)| ≤ …`) consume the regularity of `f`. -/
theorem fT_laplace_regularity {θ lam : ℝ} (hθ1 : Real.pi / 2 < θ) (hθ2 : θ < Real.pi)
    (hlam : 0 < lam) :
    ContinuousOn (fun t : ℝ => ((fT θ lam t : ℝ) : ℂ)) (Set.Icc 0 (2 * gammaT θ lam)) ∧
    ContDiffOn ℝ 2 (fun t : ℝ => ((fT θ lam t : ℝ) : ℂ)) (Set.Ioo 0 (2 * gammaT θ lam)) ∧
    (∃ B : ℝ, 0 ≤ B ∧ ∀ t ∈ Set.Ioo (0:ℝ) (2 * gammaT θ lam),
        ‖iteratedDeriv 2 (fun t : ℝ => ((fT θ lam t : ℝ) : ℂ)) t‖ ≤ B) := by
  obtain ⟨hcont, -, hcd, B, hB0, hB⟩ := fTregular hθ1 hθ2 hlam
  refine ⟨?_, ?_, B, hB0, ?_⟩
  · -- continuity on `[0,2γ]` from continuity on `[0,∞)`
    exact (Complex.continuous_ofReal.comp_continuousOn hcont).mono Set.Icc_subset_Ici_self
  · -- `C²` on `(0,2γ)`: compose the `C²` real function with the linear isometry `ℝ ↪ ℂ`
    exact ContDiffOn.comp (t := Set.univ) Complex.ofRealCLM.contDiff.contDiffOn hcd
      (fun x _ => trivial)
  · -- the second derivative of the complexification has the same norm as the real one
    intro t ht
    rw [fT_iteratedDeriv_ofReal_comp (hcd.contDiffAt (isOpen_Ioo.mem_nhds ht)),
      fT_norm_ofReal_complex]
    exact hB t ht

end Work.LinnikAreas.Density4
