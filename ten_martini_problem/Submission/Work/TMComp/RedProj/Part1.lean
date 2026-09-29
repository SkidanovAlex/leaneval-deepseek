import Mathlib
import Submission.Work.TMContract.Components
import Submission.Work.TMComp.RedProj.Basic
import Submission.Work.TMComp.RedProj.FourierAux
import Submission.Work.TMComp.RedProj.ClaimB
import Submission.Work.TMComp.RedProj.ClaimA
import Submission.Work.TMComp.RedProj.Extract
import Submission.Work.TMComp.RedProj.exp_lower_of_diophBelow
import Submission.Work.TMComp.RedProj.complexify_analyticOn
import Submission.Work.TMComp.RedProj.fourierCoeff_decay_of_strip
import Submission.Work.TMComp.RedProj.analytic_coboundary_of_decay

/-!
# C11 (`P_Reducibility`), part 1: the case `β = 0`

If `DiophBelow α b` holds for every `b > 0` and `0 < λ ≤ 1`, then every point of an interval
contained in the spectrum is reducible (AJ Thm 4.2(1), page 973):

* on the interval, component C9 gives the analytic conjugacy of the cocycle to rotations;
* the analyticity gives exponential decay of the Fourier coefficients `φ̂ k` of the rotation
  angle, while the Diophantine condition gives a lower bound `|exp (2πi k α) - 1| ≥ C e^{-ε|k|}`;
* the quotient `ψ̂ k = φ̂ k / (exp (2πi k α) - 1)` therefore decays exponentially, so the
  coboundary `ψ` is analytic (AJ (4.18)) and `rot (-ψ) * C` is a reducible gauge (Claim B).
-/

open MeasureTheory intervalIntegral

set_option autoImplicit false

noncomputable section

namespace Work.TMComp.RedProj

open Work.TMContract

/-- From a complex-valued analytic 1-periodic coboundary, extract a real-valued one. -/
theorem exists_real_coboundary (α : ℝ) (θ : ℝ) {φ : ℝ → ℝ} {ψC : ℝ → ℂ}
    (hψp : ∀ x, ψC (x + 1) = ψC x) (hψan : AnalyticOnNhd ℝ ψC Set.univ)
    (heq : ∀ x, ((φ x : ℝ) : ℂ) - ((θ : ℝ) : ℂ) = ψC (x + α) - ψC x) :
    ∃ ψ : ℝ → ℝ, (∀ x, ψ (x + 1) = ψ x) ∧ AnalyticOnNhd ℝ ψ Set.univ ∧
      ∀ x, φ x - θ = ψ (x + α) - ψ x := by
  refine ⟨fun x => (ψC x).re, fun x => ?_, ?_, fun x => ?_⟩
  · show (ψC (x + 1)).re = (ψC x).re
    rw [hψp x]
  · exact (Complex.reCLM.analyticOnNhd (s := Set.univ)).comp hψan (fun x _ => trivial)
  · have h := congrArg Complex.re (heq x)
    simpa using h

/-- **Part 1 of C11** (AJ Thm 4.2(1)). -/
theorem reducible_of_dioph_all (h9 : P_mAnalytic) (α : ℝ) (hα : Irrational α)
    (hD : ∀ b : ℝ, 0 < b → DiophBelow α b) :
    ∀ lam : ℝ, 0 < lam → lam ≤ 1 → ∀ a b : ℝ, a < b → Set.Ioo a b ⊆ amoSpec α lam →
      Set.Ioo a b ⊆ RedSet α lam := by
  intro lam h0 h1 a b hab hspec E hE
  obtain ⟨Cj, φj, hCjan, hφjan, hCjp, hφjp, hCjdet, hCjdeg, hCjconj⟩ :=
    joint_analytic_of_mAnalytic h9 α lam a b hα h0 h1 hab hspec
  -- single-energy data extracted from the joint family
  have hfE : AnalyticOnNhd ℝ (fun x : ℝ => (E, x)) Set.univ :=
    analyticOnNhd_const.prod analyticOnNhd_id
  have hEim : Set.MapsTo (fun x : ℝ => (E, x)) Set.univ (Set.Ioo a b ×ˢ Set.univ) :=
    fun x _ => ⟨hE, trivial⟩
  set C : ℝ → Matrix (Fin 2) (Fin 2) ℝ := fun x => Cj E x with hCdef
  set φ : ℝ → ℝ := fun x => φj E x with hφdef
  have hCan : ∀ i j, AnalyticOnNhd ℝ (fun x => C x i j) Set.univ :=
    fun i j => (hCjan i j).comp hfE hEim
  have hCp : ∀ x, C (x + 1) = C x := fun x => hCjp E x
  have hCdet : ∀ x, (C x).det = 1 := fun x => hCjdet E hE x
  have hCdeg : HasDegree C 0 := hCjdeg E hE
  have hconj : ∀ x, C (x + α) * tmR lam E x = rot (φ x) * C x := fun x => hCjconj E hE x
  have hφan : AnalyticOnNhd ℝ φ Set.univ := hφjan.comp hfE hEim
  have hφp : ∀ x, φ (x + 1) = φ x := fun x => hφjp E x
  -- complexify in `x` and read off exponential Fourier decay
  have hjoint : AnalyticOnNhd ℝ (fun p : ℝ × ℝ => ((φj p.1 p.2 : ℝ) : ℂ))
      (Set.Ioo a b ×ˢ Set.univ) :=
    (Complex.ofRealCLM.analyticOnNhd (s := Set.univ)).comp hφjan (fun p _ => trivial)
  have hab' : ∀ E' x, (fun p : ℝ × ℝ => ((φj p.1 p.2 : ℝ) : ℂ)) (E', x + 1)
      = (fun p : ℝ × ℝ => ((φj p.1 p.2 : ℝ) : ℂ)) (E', x) :=
    fun E' x => by
      show ((φj E' (x + 1) : ℝ) : ℂ) = ((φj E' x : ℝ) : ℂ)
      rw [hφjp E' x]
  obtain ⟨Δ, ρ, F, _hΔopen, hΔmem, hρ, hFdiff, hFagree, hFper⟩ :=
    complexify_analyticOn (fun p : ℝ × ℝ => ((φj p.1 p.2 : ℝ) : ℂ)) a b E E hE.1 le_rfl hE.2
      hjoint hab'
  have hEΔ : (E : ℂ) ∈ Δ := hΔmem (Set.mem_Icc.mpr ⟨le_rfl, le_rfl⟩)
  have hΦdiff : DifferentiableOn ℂ (fun w : ℂ => F ((E : ℂ), w)) {w : ℂ | |w.im| < ρ} := by
    have hg : DifferentiableOn ℂ (fun w : ℂ => ((E : ℂ), w)) {w : ℂ | |w.im| < ρ} :=
      DifferentiableOn.prodMk (differentiableOn_const (c := (E : ℂ))) differentiableOn_id
    exact DifferentiableOn.comp hFdiff hg (fun w hw => ⟨hEΔ, hw⟩)
  have hΦper : ∀ w : ℂ, |w.im| < ρ → F ((E : ℂ), w + 1) = F ((E : ℂ), w) := by
    intro w hw
    exact hFper ((E : ℂ), w) ⟨hEΔ, hw⟩
  have hΦagree : ∀ x : ℝ, F ((E : ℂ), (x : ℂ)) = ((φ x : ℝ) : ℂ) := by
    intro x
    have h := hFagree E (Set.mem_Icc.mpr ⟨le_rfl, le_rfl⟩) x
    simpa using h
  obtain ⟨C₁, η₁, hη₁, hbound⟩ :=
    fourierCoeff_decay_of_strip (fun x => ((φ x : ℝ) : ℂ)) (fun w => F ((E : ℂ), w)) ρ hρ
      hΦdiff hΦper hΦagree
  -- the Diophantine lower bound
  obtain ⟨C₂, hC₂, hbound₂⟩ := exp_lower_of_diophBelow α (η₁ / 4) hα (by positivity)
    (hD (η₁ / 4) (by positivity)) (η₁ / 2) (by linarith)
  set C₁' : ℝ := max C₁ 0 + 1 with hC₁'def
  have hC₁'pos : 0 < C₁' := by
    have := le_max_right C₁ 0
    simp only [hC₁'def]
    linarith
  have hC₁'le : C₁ ≤ C₁' := by
    simp only [hC₁'def]
    linarith [le_max_left C₁ 0]
  have hbound' : ∀ k : ℤ, k ≠ 0 →
      ‖fourierCoeffOn (show (0 : ℝ) < 1 by norm_num) (fun x => ((φ x : ℝ) : ℂ)) k‖
        ≤ (C₁' / C₂) * ‖Complex.exp (2 * Real.pi * (k : ℝ) * α * Complex.I) - 1‖
            * Real.exp (-((η₁ / 2) * |(k : ℝ)|)) := by
    intro k hk
    have h2 : C₂ * Real.exp (-((η₁ / 2) * |(k : ℝ)|))
        ≤ ‖Complex.exp (2 * Real.pi * (k : ℝ) * α * Complex.I) - 1‖ := hbound₂ k hk
    have he2 : 0 < Real.exp (-((η₁ / 2) * |(k : ℝ)|)) := Real.exp_pos _
    have hsplit : Real.exp (-(η₁ * |(k : ℝ)|))
        = Real.exp (-((η₁ / 2) * |(k : ℝ)|)) * Real.exp (-((η₁ / 2) * |(k : ℝ)|)) := by
      rw [← Real.exp_add]
      congr 1
      ring
    have h4 : Real.exp (-((η₁ / 2) * |(k : ℝ)|))
        ≤ ‖Complex.exp (2 * Real.pi * (k : ℝ) * α * Complex.I) - 1‖ / C₂ := by
      rw [le_div_iff₀ hC₂]
      linarith [h2]
    have hC₁'eq : (C₁' / C₂) * C₂ = C₁' := div_mul_cancel₀ _ hC₂.ne'
    calc ‖fourierCoeffOn (show (0 : ℝ) < 1 by norm_num) (fun x => ((φ x : ℝ) : ℂ)) k‖
        ≤ C₁ * Real.exp (-(η₁ * |(k : ℝ)|)) := hbound k
      _ ≤ C₁' * Real.exp (-(η₁ * |(k : ℝ)|)) := by
          nlinarith [hC₁'le, Real.exp_pos (-(η₁ * |(k : ℝ)|))]
      _ = C₁' * (Real.exp (-((η₁ / 2) * |(k : ℝ)|)) * Real.exp (-((η₁ / 2) * |(k : ℝ)|))) := by
          rw [hsplit]
      _ ≤ C₁' * ((‖Complex.exp (2 * Real.pi * (k : ℝ) * α * Complex.I) - 1‖ / C₂)
            * Real.exp (-((η₁ / 2) * |(k : ℝ)|))) := by
          apply mul_le_mul_of_nonneg_left _ hC₁'pos.le
          nlinarith [h4, he2]
      _ = (C₁' / C₂) * ‖Complex.exp (2 * Real.pi * (k : ℝ) * α * Complex.I) - 1‖
            * Real.exp (-((η₁ / 2) * |(k : ℝ)|)) := by ring

  -- solve the cohomological equation by its Fourier series
  have hcont : Continuous fun x => ((φ x : ℝ) : ℂ) := Complex.continuous_ofReal.comp hφan.continuous
  have hper2 : ∀ x, (fun x => ((φ x : ℝ) : ℂ)) (x + 1) = (fun x => ((φ x : ℝ) : ℂ)) x := by
    intro x
    show ((φ (x + 1) : ℝ) : ℂ) = ((φ x : ℝ) : ℂ)
    rw [hφp x]
  obtain ⟨ψC, hψCp, hψCan, hψCeq⟩ :=
    analytic_coboundary_of_decay α hα (fun x => ((φ x : ℝ) : ℂ)) hcont hper2 (η₁ / 2)
      (by positivity) (C₁' / C₂) (by positivity) hbound'
  have hint : ((∫ t in (0 : ℝ)..1, φ t : ℝ) : ℂ) = ∫ t in (0 : ℝ)..1, ((φ t : ℝ) : ℂ) :=
    (ContinuousLinearMap.intervalIntegral_comp_comm Complex.ofRealCLM
      (hφan.continuous.intervalIntegrable _ _)).symm
  obtain ⟨ψ, hψp, hψan, hψeq⟩ :=
    exists_real_coboundary α (∫ t in (0 : ℝ)..1, φ t) (φ := φ) hψCp hψCan
      (fun x => by
        have h := hψCeq x
        rw [← hint] at h
        exact h)
  exact mem_RedSet_of_coboundary α lam E C φ ψ hCan hCp hCdet hCdeg hconj hψan hψp hψeq

end Work.TMComp.RedProj
