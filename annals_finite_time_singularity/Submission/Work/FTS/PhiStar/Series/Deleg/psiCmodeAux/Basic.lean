import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Order.CompletePartialOrder
import Submission.Work.FTS.EllipticEst.OpenFTC.absFtcLeIntegralAbsDeriv
import Submission.Work.FTS.EllipticEst.integrableOn_HkIntegrand_terms
import Submission.Work.FTS.PhiStar.Gegenbauer.FamNormValue
import Submission.Work.FTS.PhiStar.Series.Weil.integrableOn_prod_mul
import Submission.Work.FTS.StrongEps.SupPort.HardyThetaOpen
import Submission.Work.H2.T1Q.IbpCutoff
import Submission.Work.Spaces.factor_bound
import Submission.Work.Spaces.sin_two_rpow
import Submission.Work.Spaces.sq_mul_div_rpow

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.PhiStar.Series.Deleg

/-!
# Decay of the angular mode coefficients `cmode m ψ 0`

With `ψ` a solution of the angular model `L₀ψ = Γ̄` (`Work.FTS.PhiStar.AngModel α ψ`,
`0 < α ≤ 1/5`), the `m`-th coefficient `∫₀^{π/2} ψ e_m cos θ` of `ψ` in the Dirichlet
eigenbasis `e_m` of `L₀` (`Work.FTS.PhiStar.Gegenbauer.eFam`) obeys

  `|cmode m (fun _ θ => ψ θ) 0| ≤ C / (lam m · sqrt (2m+1))`.

**The route.**  `L₀` is self-adjoint for the pairing `⟨f,g⟩ = ∫₀^{π/2} f g cos θ dθ` on the
Dirichlet space, so with `λ_m = lam m` and `Γ̄ = GamBar α` the *Wronskian identity*

  `d/dθ [cos θ · (ψ' e_m - ψ e_m')] = cos θ · (λ_m ψ - Γ̄) e_m`   on `(0, π/2)`

(proved pointwise in `hasDerivAt_lzero_wronskian`) and the fact that the antiderivative
`Ξ θ = cos θ (ψ' e_m - ψ e_m')` tends to `0` at both endpoints (from the integrated form of the
model equation, `psi_deriv_tan_form`, and the continuity of `ψ` at the endpoints) give

  `λ_m ∫₀^{π/2} ψ e_m cos θ = ∫₀^{π/2} Γ̄ e_m cos θ`.

Cauchy–Schwarz in `L²(Ioc 0 (π/2), cos θ dθ)` then bounds the right hand side by
`sqrt (∫₀^{π/2} Γ̄² cos θ) · sqrt (∫₀^{π/2} e_m² cos θ)`, and
`∫₀^{π/2} e_m² cos θ = (2m+2)(2m+3)/(4m+5) ≥ (2m+1)/4` (`FamNormValue`) while
`∫₀^{π/2} Γ̄² cos θ` is bounded by an absolute constant because `|Γ̄| ≤ 45/4` on `[0, π/2]`.
-/

/-! ## Elementary facts about the eigenfunctions `eFam m` -/

theorem contDiff_eFam (m : ℕ) : ContDiff ℝ 3 (Work.FTS.PhiStar.Gegenbauer.eFam m) := by
  have h1 : ContDiff ℝ 3 (Work.FTS.PhiStar.Gegenbauer.gC (2 * m + 1)) :=
    Work.FTS.PhiStar.Gegenbauer.contDiff_gC _
  have h2 : ContDiff ℝ 3
      (fun θ : ℝ => Work.FTS.PhiStar.Gegenbauer.gC (2 * m + 1) (Real.sin θ)) :=
    h1.comp Real.contDiff_sin
  exact Real.contDiff_cos.mul h2

theorem eFam_zero (m : ℕ) : Work.FTS.PhiStar.Gegenbauer.eFam m 0 = 0 := by
  simp [Work.FTS.PhiStar.Gegenbauer.eFam, Work.FTS.PhiStar.Gegenbauer.gC_odd_zero]

theorem eFam_pi_div_two (m : ℕ) : Work.FTS.PhiStar.Gegenbauer.eFam m (Real.pi / 2) = 0 := by
  simp [Work.FTS.PhiStar.Gegenbauer.eFam]


/-- `eFam m` is bounded on the closed angular interval. -/
theorem eFam_abs_bound (m : ℕ) :
    ∃ Q : ℝ, 0 ≤ Q ∧ ∀ θ ∈ Set.Icc (0 : ℝ) (Real.pi / 2),
      |Work.FTS.PhiStar.Gegenbauer.eFam m θ| ≤ Q := by
  obtain ⟨C, hC⟩ := IsCompact.exists_bound_of_continuousOn
    (isCompact_Icc : IsCompact (Set.Icc (0 : ℝ) (Real.pi / 2)))
    ((contDiff_eFam m).continuous.continuousOn)
  refine ⟨C, le_trans (norm_nonneg _) (hC 0 ⟨le_refl 0, by linarith [Real.pi_pos]⟩), ?_⟩
  intro θ hθ
  simpa [Real.norm_eq_abs] using hC θ hθ

/-- `deriv (eFam m)` is bounded on the closed angular interval. -/
theorem eFam_deriv_abs_bound (m : ℕ) :
    ∃ Q : ℝ, 0 ≤ Q ∧ ∀ θ ∈ Set.Icc (0 : ℝ) (Real.pi / 2),
      |deriv (Work.FTS.PhiStar.Gegenbauer.eFam m) θ| ≤ Q := by
  have hcont : Continuous (deriv (Work.FTS.PhiStar.Gegenbauer.eFam m)) := by
    have h : ContDiffOn ℝ 2 (deriv (Work.FTS.PhiStar.Gegenbauer.eFam m)) Set.univ :=
      (contDiff_eFam m).contDiffOn.deriv_of_isOpen isOpen_univ
        (by norm_num : ((2:ℕ∞) : WithTop ℕ∞) + 1 ≤ ((3:ℕ∞) : WithTop ℕ∞))
    exact continuousOn_univ.mp h.continuousOn
  obtain ⟨C, hC⟩ := IsCompact.exists_bound_of_continuousOn
    (isCompact_Icc : IsCompact (Set.Icc (0 : ℝ) (Real.pi / 2))) hcont.continuousOn
  refine ⟨C, le_trans (norm_nonneg _) (hC 0 ⟨le_refl 0, by linarith [Real.pi_pos]⟩), ?_⟩
  intro θ hθ
  simpa [Real.norm_eq_abs] using hC θ hθ



/-- `eFam m` is a Dirichlet eigenfunction of `Lzero1` with eigenvalue `lam m`. -/
theorem eFam_Lzero1 (m : ℕ) {θ : ℝ} (hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)) :
    Work.FTS.EllipticEst.Lzero1 (Work.FTS.PhiStar.Gegenbauer.eFam m) θ
      = Work.FTS.PhiStar.Gegenbauer.lam m * Work.FTS.PhiStar.Gegenbauer.eFam m θ := by
  have hcos : Real.cos θ ≠ 0 :=
    ne_of_gt (Real.cos_pos_of_mem_Ioo ⟨by linarith [hθ.1, Real.pi_pos], hθ.2⟩)
  rw [Work.FTS.EllipticEst.Lzero1_eq_Lzero]
  exact Work.FTS.PhiStar.Gegenbauer.eFam_Lzero m hcos 0

/-! ## The Wronskian identity -/

/-- **The pointwise Wronskian identity.**  For `f`, `g` twice differentiable at `θ` with
`cos θ ≠ 0`, the derivative of `θ' ↦ cos θ' (f' g - f g')(θ')` is
`cos θ·(f L₀g - (L₀f) g)`.  This is the differential form of the self-adjointness of `L₀`. -/
theorem hasDerivAt_lzero_wronskian {f g : ℝ → ℝ} {θ : ℝ} (hcos : Real.cos θ ≠ 0)
    (hf1 : HasDerivAt f (deriv f θ) θ) (hf2 : HasDerivAt (deriv f) (deriv (deriv f) θ) θ)
    (hg1 : HasDerivAt g (deriv g θ) θ) (hg2 : HasDerivAt (deriv g) (deriv (deriv g) θ) θ) :
    HasDerivAt (fun θ' => Real.cos θ' * (deriv f θ' * g θ' - f θ' * deriv g θ'))
      (Real.cos θ * (f θ * Work.FTS.EllipticEst.Lzero1 g θ
        - Work.FTS.EllipticEst.Lzero1 f θ * g θ)) θ := by
  have hW : HasDerivAt (fun θ' => deriv f θ' * g θ' - f θ' * deriv g θ')
      (deriv (deriv f) θ * g θ - f θ * deriv (deriv g) θ) θ := by
    have h := (hf2.mul hg1).sub (hf1.mul hg2)
    convert h using 1
    ring
  have htanf : deriv (fun t : ℝ => Real.tan t * f t) θ
      = (1 / Real.cos θ ^ 2) * f θ + Real.tan θ * deriv f θ :=
    ((Real.hasDerivAt_tan hcos).mul hf1).deriv
  have htang : deriv (fun t : ℝ => Real.tan t * g t) θ
      = (1 / Real.cos θ ^ 2) * g θ + Real.tan θ * deriv g θ :=
    ((Real.hasDerivAt_tan hcos).mul hg1).deriv
  have key : f θ * Work.FTS.EllipticEst.Lzero1 g θ - Work.FTS.EllipticEst.Lzero1 f θ * g θ
      = (deriv (deriv f) θ * g θ - f θ * deriv (deriv g) θ)
        - Real.tan θ * (deriv f θ * g θ - f θ * deriv g θ) := by
    simp only [Work.FTS.EllipticEst.Lzero1]
    rw [htanf, htang]
    field_simp
    ring
  have h := (Real.hasDerivAt_cos θ).mul hW
  refine h.congr_deriv ?_
  rw [key, Real.tan_eq_sin_div_cos]
  field_simp
  ring

/-! ## The integrated form of the model equation -/




end Work.FTS.PhiStar.Series.Deleg
