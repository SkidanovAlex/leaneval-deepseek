import Mathlib
import Submission.Lib.Unif2.Commons.Analysis.Complex.Analytic.exists_analyticAt_log_of_ne_zero

/-!
# Auxiliary analytic facts for the one-critical-point Riemann–Hurwitz step

* `Work.BasinSC.StepOneCrit.eventuallyEq_const_of_pow_eq_one` : a function which is continuous at a
  point, and whose `d`-th power is `1` near that point, is eventually constant there (the `d`-th
  roots of unity are a finite set).
* `Work.BasinSC.StepOneCrit.analyticAt_of_pow_eq_of_continuousAt` : if a function continuous at a
  point has a `d`-th power which is analytic and non-zero there, then it is analytic there.  (The
  local logarithm of the `d`-th power makes the ratio a locally constant `d`-th root of unity.)
-/

set_option linter.style.haveILetI false

open scoped Topology
open Filter

namespace Work.BasinSC.StepOneCrit

theorem eventuallyEq_const_of_pow_eq_one {u : ℂ → ℂ} {z₀ : ℂ} {d : ℕ} (hd : 0 < d)
    (hu : ContinuousAt u z₀) (hpow : ∀ᶠ z in 𝓝 z₀, u z ^ d = 1) :
    u =ᶠ[𝓝 z₀] (fun _ => u z₀) := by
  have hμfin : ({ζ : ℂ | ζ ^ d = 1} : Set ℂ).Finite :=
    Set.Finite.subset (Polynomial.finite_setOfPred_isRoot
      (Polynomial.X_pow_sub_C_ne_zero hd (1 : ℂ))) (by
        intro ζ hζ
        simp only [Set.mem_ofPred_eq, Polynomial.IsRoot.def, Polynomial.eval_sub,
          Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_C, sub_eq_zero] at hζ ⊢
        exact hζ)
  have hcl : IsClosed (({ζ : ℂ | ζ ^ d = 1} : Set ℂ) \ {u z₀}) :=
    (hμfin.subset Set.sdiff_subset).isClosed
  have hmem : u z₀ ∈ (({ζ : ℂ | ζ ^ d = 1} : Set ℂ) \ {u z₀})ᶜ := by
    simp only [Set.mem_compl_iff, Set.mem_sdiff, Set.mem_ofPred_eq, Set.mem_singleton_iff,
      not_and, not_not, implies_true]
  obtain ⟨δ, hδ, hδ'⟩ := Metric.isOpen_iff.mp hcl.isOpen_compl _ hmem
  obtain ⟨ε₁, hε₁, h₁⟩ :=
    Metric.eventually_nhds_iff.mp (hu.eventually (Metric.ball_mem_nhds _ hδ))
  obtain ⟨ε₂, hε₂, h₂⟩ := Metric.eventually_nhds_iff.mp hpow
  refine Metric.eventually_nhds_iff.mpr ⟨min ε₁ ε₂, lt_min hε₁ hε₂, fun z hz => ?_⟩
  have hz₁ : dist z z₀ < ε₁ := lt_of_lt_of_le hz (min_le_left _ _)
  have hz₂ : dist z z₀ < ε₂ := lt_of_lt_of_le hz (min_le_right _ _)
  have hzμ : u z ∈ ({ζ : ℂ | ζ ^ d = 1} : Set ℂ) := h₂ hz₂
  by_contra hne
  exact hδ' (h₁ hz₁) ⟨hzμ, by simpa using hne⟩

/-- If `f` is continuous at `z₀` and `f ^ d` is analytic and non-zero at `z₀`, then `f` is
analytic at `z₀`. -/
theorem analyticAt_of_pow_eq_of_continuousAt {q f : ℂ → ℂ} {z₀ : ℂ} {d : ℕ} (hd : 0 < d)
    (hq : AnalyticAt ℂ q z₀) (hqz : q z₀ ≠ 0) (hf : ContinuousAt f z₀)
    (hpow : ∀ᶠ z in 𝓝 z₀, f z ^ d = q z) : AnalyticAt ℂ f z₀ := by
  obtain ⟨G, hGan, hGexp⟩ :=
    Commons.Analysis.Complex.Analytic.exists_analyticAt_log_of_ne_zero hq hqz
  have hdc : (d : ℂ) ≠ 0 := by exact_mod_cast hd.ne'
  set H : ℂ → ℂ := fun w => Complex.exp (G w / (d : ℂ)) with hH
  have hHan : AnalyticAt ℂ H z₀ := (hGan.div_const (c := (d : ℂ))).cexp
  have hHne : ∀ w, H w ≠ 0 := fun w => Complex.exp_ne_zero _
  have hHpow : ∀ w, H w ^ d = Complex.exp (G w) := by
    intro w
    rw [hH]
    simp only
    rw [← Complex.exp_nat_mul]
    congr 1
    field_simp
  have hucont : ContinuousAt (fun w => f w / H w) z₀ :=
    hf.div hHan.continuousAt (hHne z₀)
  have hupow : ∀ᶠ z in 𝓝 z₀, (f z / H z) ^ d = 1 := by
    filter_upwards [hGexp, hpow] with z h1 h2
    rw [div_pow, hHpow z, h2, h1, div_self (Complex.exp_ne_zero (G z))]
  have huev := eventuallyEq_const_of_pow_eq_one hd hucont hupow
  have heq : (fun w => (f z₀ / H z₀) * H w) =ᶠ[𝓝 z₀] f := by
    filter_upwards [huev] with w hw
    rw [← hw, div_mul_cancel₀ _ (hHne w)]
  exact ((analyticAt_const (v := f z₀ / H z₀)).mul hHan).congr heq

end Work.BasinSC.StepOneCrit
