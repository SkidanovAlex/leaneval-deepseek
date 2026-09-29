import Mathlib
import Submission.Work.TMContract.Components
import Submission.Work.TMComp.RedProj.Basic
import Submission.Work.TMComp.RedProj.ClaimB
import Submission.Work.TMComp.RedProj.FourierAux
import Submission.Work.TMComp.RedProj.complexify_analyticOn
import Submission.Work.TMComp.RedProj.fourierCoeff_decay_of_strip

/-!
# C11 (`P_Reducibility`), Claim A: reducibility forces Fourier decay

This is the converse of `ClaimB`: if `E` is reducible (`E ∈ RedSet α lam`) and, in addition,
the almost Mathieu cocycle at `E` is analytically conjugate to rotations with angle `φ`
(component C9), then the Fourier coefficients of `x ↦ φ (E,x)` satisfy the small-divisor
bound `|φ̂ k| ≤ C * |exp (2πi k α) - 1| * exp (-η|k|)` (AJ (4.22)–(4.23)).

The proof is AJ's: the two conjugacies (the reducible one and C9's) differ by an analytic
1-periodic gauge `O`, so `O (x+α) rot (φ x) = rot c * O x`; the cohomological equation for
`φ` follows from `coboundary_of_conjugacy`, its solution `ψ` is analytic and 1-periodic, and
the Fourier coefficients of `φ` and `ψ` are related by
`φ̂ k = (exp (2πi k α) - 1) * ψ̂ k`, while `ψ̂` decays exponentially.
-/

open MeasureTheory intervalIntegral

set_option autoImplicit false

noncomputable section

namespace Work.TMComp.RedProj

open Work.TMContract

theorem continuous_ek (k : ℤ) : Continuous (ek k) := by
  unfold ek
  fun_prop

/-- **Fourier coefficients of a coboundary** (AJ (4.18)): if `φ x - ∫φ = ψ (x+α) - ψ x` with
`ψ` 1-periodic, then for `k ≠ 0` the `k`-th Fourier coefficient of `φ` is
`(exp (2πi k α) - 1)` times that of `ψ`. -/
theorem fcoef_coboundary (α : ℝ) (φ ψ : ℝ → ℝ) (hψp : ∀ x, ψ (x + 1) = ψ x)
    (hcontψ : Continuous ψ)
    (heq : ∀ x, φ x - (∫ t in (0 : ℝ)..1, φ t) = ψ (x + α) - ψ x)
    (k : ℤ) (hk : k ≠ 0) :
    fourierCoeffOn (show (0 : ℝ) < 1 by norm_num) (fun x => ((φ x : ℝ) : ℂ)) k
      = (Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (k : ℂ) * (α : ℂ)) - 1)
        * fourierCoeffOn (show (0 : ℝ) < 1 by norm_num) (fun x => ((ψ x : ℝ) : ℂ)) k := by
  have hf : ∀ x, (fun x => ((ψ x : ℝ) : ℂ)) (x + 1) = (fun x => ((ψ x : ℝ) : ℂ)) x :=
    fun x => by show ((ψ (x + 1) : ℝ) : ℂ) = ((ψ x : ℝ) : ℂ); rw [hψp x]
  have hpt : ∀ x : ℝ, ((φ x : ℝ) : ℂ) * ek k x
      = (((∫ t in (0 : ℝ)..1, φ t) : ℝ) : ℂ) * ek k x
        + ((ψ (x + α) : ℝ) : ℂ) * ek k x - ((ψ x : ℝ) : ℂ) * ek k x := by
    intro x
    have h := heq x
    have hx : φ x = (∫ t in (0 : ℝ)..1, φ t) + ψ (x + α) - ψ x := by linarith
    rw [hx]
    push_cast
    ring
  have hint : ∀ c : ℂ, IntervalIntegrable (fun x : ℝ => c * ek k x) volume (0 : ℝ) 1 :=
    fun c => (continuous_const.mul (continuous_ek k)).intervalIntegrable _ _
  have hint2 : IntervalIntegrable (fun x : ℝ => ((ψ (x + α) : ℝ) : ℂ) * ek k x) volume (0 : ℝ) 1 :=
    ((Complex.continuous_ofReal.comp
      (hcontψ.comp (continuous_id.add continuous_const))).mul (continuous_ek k)).intervalIntegrable _ _
  have hint3 : IntervalIntegrable (fun x : ℝ => ((ψ x : ℝ) : ℂ) * ek k x) volume (0 : ℝ) 1 :=
    ((Complex.continuous_ofReal.comp hcontψ).mul (continuous_ek k)).intervalIntegrable _ _
  calc fourierCoeffOn (show (0 : ℝ) < 1 by norm_num) (fun x => ((φ x : ℝ) : ℂ)) k
      = (∫ x in (0 : ℝ)..1, ((φ x : ℝ) : ℂ) * ek k x) := fcoef_eq_int _ k
    _
      = ∫ x in (0 : ℝ)..1, ((((∫ t in (0 : ℝ)..1, φ t) : ℝ) : ℂ) * ek k x
          + ((ψ (x + α) : ℝ) : ℂ) * ek k x - ((ψ x : ℝ) : ℂ) * ek k x) :=
        intervalIntegral.integral_congr fun x _ => hpt x
    _ = (∫ x in (0 : ℝ)..1, (((∫ t in (0 : ℝ)..1, φ t) : ℝ) : ℂ) * ek k x)
          + (∫ x in (0 : ℝ)..1, ((ψ (x + α) : ℝ) : ℂ) * ek k x)
          - (∫ x in (0 : ℝ)..1, ((ψ x : ℝ) : ℂ) * ek k x) := by
        rw [intervalIntegral.integral_sub (hint _ |>.add hint2) hint3,
          intervalIntegral.integral_add (hint _) hint2]
    _ = (((∫ t in (0 : ℝ)..1, φ t) : ℝ) : ℂ) * (∫ x in (0 : ℝ)..1, ek k x)
          + (∫ x in (0 : ℝ)..1, ((ψ (x + α) : ℝ) : ℂ) * ek k x)
          - (∫ x in (0 : ℝ)..1, ((ψ x : ℝ) : ℂ) * ek k x) := by
        rw [intervalIntegral.integral_const_mul]
    _ = 0 + (Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (k : ℂ) * (α : ℂ))
            * ∫ x in (0 : ℝ)..1, ((ψ x : ℝ) : ℂ) * ek k x)
          - (∫ x in (0 : ℝ)..1, ((ψ x : ℝ) : ℂ) * ek k x) := by
        have hshift : (∫ x in (0 : ℝ)..1, ((ψ (x + α) : ℝ) : ℂ) * ek k x)
            = Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (k : ℂ) * (α : ℂ))
              * ∫ x in (0 : ℝ)..1, ((ψ x : ℝ) : ℂ) * ek k x := by
          rw [← fcoef_eq_int (fun x => ((ψ (x + α) : ℝ) : ℂ)) k,
            ← fcoef_eq_int (fun x => ((ψ x : ℝ) : ℂ)) k,
            fcoef_shift (fun x => ((ψ x : ℝ) : ℂ)) hf α k]
        rw [hshift, integral_ek_zero k hk, mul_zero, zero_add]
    _ = (Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (k : ℂ) * (α : ℂ)) - 1)
          * fourierCoeffOn (show (0 : ℝ) < 1 by norm_num) (fun x => ((ψ x : ℝ) : ℂ)) k := by
        rw [fcoef_eq_int (fun x => ((ψ x : ℝ) : ℂ)) k]
        ring

/-- **Claim A** (AJ (4.22)–(4.23)).  If `E` is in the reducible set and the cocycle at `E` is
analytically conjugate to rotations with angle `φ`, then the Fourier coefficients of `φ`
satisfy the small-divisor bound. -/
theorem fourier_bound_of_mem_RedSet
    (hcob : ∀ (α : ℝ), Irrational α → ∀ (φ : ℝ → ℝ), Continuous φ →
      (∀ x, φ (x + 1) = φ x) → ∀ (O : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (c : ℝ),
      (∀ i j, AnalyticOnNhd ℝ (fun x => O x i j) Set.univ) →
      (∀ x, O (x + 1) = O x) → (∀ x, (O x).det = 1) →
      (∀ x, O (x + α) * rot (φ x) = rot c * O x) →
      ∃ ψ : ℝ → ℝ, (∀ x, ψ (x + 1) = ψ x) ∧ AnalyticOnNhd ℝ ψ Set.univ ∧
        ∀ x, φ x - (∫ t in (0 : ℝ)..1, φ t) = ψ (x + α) - ψ x)
    (α lam E a b : ℝ) (hα : Irrational α)
    (hE : E ∈ Set.Ioo a b)
    (C : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (φ : ℝ → ℝ)
    (hCan : ∀ i j, AnalyticOnNhd ℝ (fun x => C x i j) Set.univ)
    (hCp : ∀ x, C (x + 1) = C x) (hCdet : ∀ x, (C x).det = 1)
    (hconj : ∀ x, C (x + α) * tmR lam E x = rot (φ x) * C x)
    (hφan : AnalyticOnNhd ℝ φ Set.univ) (hφp : ∀ x, φ (x + 1) = φ x)
    (hred : E ∈ RedSet α lam) :
    ∃ C₀ η : ℝ, 0 < η ∧ ∀ k : ℤ, k ≠ 0 →
      ‖fourierCoeffOn (show (0 : ℝ) < 1 by norm_num) (fun x => ((φ x : ℝ) : ℂ)) k‖
        ≤ C₀ * ‖Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (k : ℂ) * (α : ℂ)) - 1‖
            * Real.exp (-(η * |(k : ℝ)|)) := by
  obtain ⟨B, c, hBan, hBp, hBdet, _hBdeg, hBconj⟩ := hred
  have hCadj : ∀ x, C x * Matrix.adjugate (C x) = 1 := by
    intro x
    rw [Matrix.mul_adjugate, hCdet x, one_smul]
  have hAdjC : ∀ x, Matrix.adjugate (C x) * C x = 1 := by
    intro x
    rw [Matrix.adjugate_mul, hCdet x, one_smul]
  have hAan : ∀ i j, AnalyticOnNhd ℝ (fun x => Matrix.adjugate (C x) i j) Set.univ := by
    intro i j
    have hrep : (fun x => Matrix.adjugate (C x) i j)
        = fun x => (!![C x 1 1, -C x 0 1; -C x 1 0, C x 0 0] :
            Matrix (Fin 2) (Fin 2) ℝ) i j := by
      funext x
      rw [Matrix.adjugate_fin_two]
    rw [hrep]
    fin_cases i <;> fin_cases j <;>
      first
        | exact hCan 1 1
        | exact (hCan 0 1).neg
        | exact (hCan 1 0).neg
        | exact hCan 0 0
  set O : ℝ → Matrix (Fin 2) (Fin 2) ℝ := fun x => B x * Matrix.adjugate (C x) with hOdef
  have hOan : ∀ i j, AnalyticOnNhd ℝ (fun x => O x i j) Set.univ :=
    analyticOnNhd_matrix_mul hBan hAan
  have hOp : ∀ x, O (x + 1) = O x := by
    intro x
    simp only [O]
    rw [hBp x, hCp x]
  have hOdet : ∀ x, (O x).det = 1 := by
    intro x
    simp only [O]
    rw [Matrix.det_mul, hBdet x, Matrix.det_adjugate]
    simp [hCdet x]
  have hOconj : ∀ x, O (x + α) * rot (φ x) = rot c * O x := by
    intro x
    have h2 : Matrix.adjugate (C (x + α)) * rot (φ x)
        = tmR lam E x * Matrix.adjugate (C x) := by
      calc Matrix.adjugate (C (x + α)) * rot (φ x)
          = Matrix.adjugate (C (x + α)) * rot (φ x) * (C x * Matrix.adjugate (C x)) := by
              rw [hCadj x, mul_one]
        _ = Matrix.adjugate (C (x + α)) * (rot (φ x) * C x) * Matrix.adjugate (C x) := by
              noncomm_ring
        _ = Matrix.adjugate (C (x + α)) * (C (x + α) * tmR lam E x) * Matrix.adjugate (C x) := by
              rw [hconj x]
        _ = (Matrix.adjugate (C (x + α)) * C (x + α)) * tmR lam E x * Matrix.adjugate (C x) := by
              noncomm_ring
        _ = tmR lam E x * Matrix.adjugate (C x) := by rw [hAdjC (x + α), one_mul]
    simp only [O]
    rw [mul_assoc, h2, ← mul_assoc, hBconj x, mul_assoc]
  obtain ⟨ψ, hψp, hψan, hψeq⟩ :=
    hcob α hα φ hφan.continuous hφp O c hOan hOp hOdet hOconj
  have hψjoint : AnalyticOnNhd ℝ (fun p : ℝ × ℝ => ((ψ p.2 : ℝ) : ℂ))
      (Set.Ioo a b ×ˢ Set.univ) :=
    (Complex.ofRealCLM.analyticOnNhd (s := Set.univ)).comp
      (hψan.comp analyticOnNhd_snd (fun p _ => trivial)) (fun p _ => trivial)
  have hψ2p : ∀ E' x, (fun p : ℝ × ℝ => ((ψ p.2 : ℝ) : ℂ)) (E', x + 1)
      = (fun p : ℝ × ℝ => ((ψ p.2 : ℝ) : ℂ)) (E', x) :=
    fun E' x => by
      show ((ψ (x + 1) : ℝ) : ℂ) = ((ψ x : ℝ) : ℂ)
      rw [hψp x]
  obtain ⟨Δ, ρ, F, hΔopen, hΔmem, hρ, hFdiff, hFagree, hFper⟩ :=
    complexify_analyticOn (fun p : ℝ × ℝ => ((ψ p.2 : ℝ) : ℂ)) a b E E hE.1 le_rfl hE.2
      hψjoint hψ2p
  have hEΔ : (E : ℂ) ∈ Δ := hΔmem (Set.mem_Icc.mpr ⟨le_rfl, le_rfl⟩)
  have hΦdiff : DifferentiableOn ℂ (fun w : ℂ => F ((E : ℂ), w)) {w : ℂ | |w.im| < ρ} := by
    have hg : DifferentiableOn ℂ (fun w : ℂ => ((E : ℂ), w)) {w : ℂ | |w.im| < ρ} :=
      DifferentiableOn.prodMk (differentiableOn_const (c := (E : ℂ))) differentiableOn_id
    exact DifferentiableOn.comp hFdiff hg (fun w hw => ⟨hEΔ, hw⟩)
  have hΦper : ∀ w : ℂ, |w.im| < ρ → F ((E : ℂ), w + 1) = F ((E : ℂ), w) := by
    intro w hw
    have h := hFper ((E : ℂ), w) ⟨hEΔ, hw⟩
    simpa using h
  have hΦagree : ∀ x : ℝ, F ((E : ℂ), (x : ℂ)) = ((ψ x : ℝ) : ℂ) := by
    intro x
    have h := hFagree E (Set.mem_Icc.mpr ⟨le_rfl, le_rfl⟩) x
    simpa using h
  obtain ⟨C₁, η₁, hη₁, hbound⟩ :=
    fourierCoeff_decay_of_strip (fun x => ((ψ x : ℝ) : ℂ)) (fun w => F ((E : ℂ), w)) ρ hρ
      hΦdiff hΦper hΦagree
  refine ⟨C₁, η₁, hη₁, fun k hk => ?_⟩
  have hkey := fcoef_coboundary α φ ψ hψp hψan.continuous hψeq k hk
  have h1 := hbound k
  rw [hkey, norm_mul]
  calc ‖Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (k : ℂ) * (α : ℂ)) - 1‖
        * ‖fourierCoeffOn (show (0 : ℝ) < 1 by norm_num) (fun x => ((ψ x : ℝ) : ℂ)) k‖
      ≤ ‖Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (k : ℂ) * (α : ℂ)) - 1‖
        * (C₁ * Real.exp (-(η₁ * |(k : ℝ)|))) :=
        mul_le_mul_of_nonneg_left h1 (norm_nonneg _)
    _ = C₁ * ‖Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (k : ℂ) * (α : ℂ)) - 1‖
        * Real.exp (-(η₁ * |(k : ℝ)|)) := by ring

end Work.TMComp.RedProj
