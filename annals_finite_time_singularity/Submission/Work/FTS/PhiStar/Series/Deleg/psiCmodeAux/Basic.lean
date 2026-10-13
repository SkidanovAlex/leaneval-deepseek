import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Order.CompletePartialOrder
import Submission.Work.FTS.PhiStar.Series.Defs
import Submission.Work.FTS.PhiStar.Defs
import Submission.Work.FTS.PhiStar.Gegenbauer.eFam_Lzero
import Submission.Work.FTS.PhiStar.Gegenbauer.FamNormValue
import Submission.Work.Elliptic.Defs
import Submission.Work.Spaces.c_bounds
import Submission.Work.Spaces.cs_integral
import Submission.Work.FTS.EllipticEst.StraightDefs
import Submission.Work.Elliptic.intervalIntegrable_of_continuousOn_Ioo_of_bound
import Submission.Work.Elliptic.contDiffOn_one_bounds

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

/-- `|eFam m θ| ≤ K θ` on the closed angular interval. -/
theorem eFam_theta_bound (m : ℕ) :
    ∃ K : ℝ, 0 ≤ K ∧
      ∀ θ ∈ Set.Icc (0 : ℝ) (Real.pi / 2),
        |Work.FTS.PhiStar.Gegenbauer.eFam m θ| ≤ K * θ := by
  obtain ⟨C, hCnn, hCmin, _⟩ := Work.Elliptic.contDiffOn_one_bounds
    ((contDiff_eFam m).contDiffOn.of_le (by norm_num)) (eFam_zero m) (eFam_pi_div_two m)
  exact ⟨C, hCnn, fun θ hθ => le_trans (hCmin θ hθ)
    (mul_le_mul_of_nonneg_left (min_le_left _ _) hCnn)⟩

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

/-- The Gegenbauer polynomials are bounded on `[0,1]`.

**Name.**  This is the *existential* bound on the closed unit interval; the same namespace
(`Work.FTS.PhiStar.Series.Deleg`) also carries the sharp pointwise bound
`gC_abs_bound m hθ : |gC (2m+1) (sin θ)| ≤ √(Npsi m)/cos θ` of `Deleg/psiAngDefs.lean`, so the two
cannot share a name (a file importing both would fail at the import line).  This one is called
`gC_abs_bound_on_Icc`; renaming it was necessary to make the `CptQ`/honesty chain importable
together with the star-package chain. -/
theorem gC_abs_bound_on_Icc (m : ℕ) :
    ∃ Q : ℝ, 0 ≤ Q ∧ ∀ u ∈ Set.Icc (0 : ℝ) 1,
      |Work.FTS.PhiStar.Gegenbauer.gC (2 * m + 1) u| ≤ Q := by
  obtain ⟨C, hC⟩ := IsCompact.exists_bound_of_continuousOn
    (isCompact_Icc : IsCompact (Set.Icc (0 : ℝ) 1))
    ((Work.FTS.PhiStar.Gegenbauer.contDiff_gC (2 * m + 1)).continuous.continuousOn)
  refine ⟨C, le_trans (norm_nonneg _) (hC 0 ⟨le_refl 0, by norm_num⟩), ?_⟩
  intro u hu
  simpa [Real.norm_eq_abs] using hC u hu

/-- The derivatives of the Gegenbauer polynomials are bounded on `[0,1]`. -/
theorem gC_deriv_abs_bound (m : ℕ) :
    ∃ Q : ℝ, 0 ≤ Q ∧ ∀ u ∈ Set.Icc (0 : ℝ) 1,
      |deriv (Work.FTS.PhiStar.Gegenbauer.gC (2 * m + 1)) u| ≤ Q := by
  have hcont : Continuous (deriv (Work.FTS.PhiStar.Gegenbauer.gC (2 * m + 1))) := by
    have h : ContDiffOn ℝ 2 (deriv (Work.FTS.PhiStar.Gegenbauer.gC (2 * m + 1))) Set.univ :=
      (Work.FTS.PhiStar.Gegenbauer.contDiff_gC (2 * m + 1)).contDiffOn.deriv_of_isOpen
        isOpen_univ (by norm_num : ((2:ℕ∞) : WithTop ℕ∞) + 1 ≤ ((3:ℕ∞) : WithTop ℕ∞))
    exact continuousOn_univ.mp h.continuousOn
  obtain ⟨C, hC⟩ := IsCompact.exists_bound_of_continuousOn
    (isCompact_Icc : IsCompact (Set.Icc (0 : ℝ) 1)) hcont.continuousOn
  refine ⟨C, le_trans (norm_nonneg _) (hC 0 ⟨le_refl 0, by norm_num⟩), ?_⟩
  intro u hu
  simpa [Real.norm_eq_abs] using hC u hu

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

/-- **The integrated form of `L₀ψ = Γ̄`.**  For `0 < a ≤ b < π/2`,

  `ψ'(a) - tan a·ψ(a) = ψ'(b) - tan b·ψ(b) + 6 ∫_a^b ψ + ∫_a^b Γ̄`.

This is the fundamental-theorem-of-calculus integrated form of the ODE: the antiderivative
`-ψ' + tan·ψ` of the first two terms of `L₀ψ` is evaluated at the two endpoints. -/
theorem psi_deriv_tan_form_le {α : ℝ} {ψ : ℝ → ℝ} (hψ : Work.FTS.PhiStar.AngModel α ψ)
    {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) (hb : b < Real.pi / 2) :
    deriv ψ a - Real.tan a * ψ a
      = deriv ψ b - Real.tan b * ψ b + 6 * (∫ s in a..b, ψ s)
        + ∫ s in a..b, Work.FTS.VocabO.GamBar α s := by
  have hsub : Set.Icc a b ⊆ Set.Ioo (0 : ℝ) (Real.pi / 2) := by
    intro x hx
    exact ⟨lt_of_lt_of_le ha hx.1, lt_of_le_of_lt hx.2 hb⟩
  have hsm : ContDiffOn ℝ 3 ψ (Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
    hψ.smooth.of_le (by simp [Work.Stability.smoothOrder])
  have hd1' : ContDiffOn ℝ 2 (deriv ψ) (Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
    hsm.deriv_of_isOpen isOpen_Ioo (by norm_num : ((2:ℕ∞) : WithTop ℕ∞) + 1 ≤ ((3:ℕ∞) : WithTop ℕ∞))
  have hd2 : ContDiffOn ℝ 1 (deriv (deriv ψ)) (Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
    hd1'.deriv_of_isOpen isOpen_Ioo (by norm_num : ((1:ℕ∞) : WithTop ℕ∞) + 1 ≤ ((2:ℕ∞) : WithTop ℕ∞))
  have hcont2 : ContinuousOn (deriv (deriv ψ)) (Set.Icc a b) := hd2.continuousOn.mono hsub
  have hcont0 : ContinuousOn ψ (Set.Icc a b) := (hsm.continuousOn).mono hsub
  have htan : ContDiffOn ℝ 3 Real.tan (Set.Ioo (0 : ℝ) (Real.pi / 2)) := by
    rw [show Real.tan = fun x : ℝ => Real.sin x / Real.cos x from
      funext Real.tan_eq_sin_div_cos]
    exact (Real.contDiff_sin.contDiffOn).div (Real.contDiff_cos.contDiffOn)
      (fun x hx => ne_of_gt (Real.cos_pos_of_mem_Ioo ⟨by linarith [hx.1], hx.2⟩))
  have hprod : ContDiffOn ℝ 3 (fun t : ℝ => Real.tan t * ψ t)
      (Set.Ioo (0 : ℝ) (Real.pi / 2)) := htan.mul hsm
  have hd1 : ContDiffOn ℝ 2 (deriv (fun t : ℝ => Real.tan t * ψ t))
      (Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
    hprod.deriv_of_isOpen isOpen_Ioo (by norm_num : ((2:ℕ∞) : WithTop ℕ∞) + 1 ≤ ((3:ℕ∞) : WithTop ℕ∞))
  have hcont1 : ContinuousOn (deriv (fun t : ℝ => Real.tan t * ψ t)) (Set.Icc a b) :=
    hd1.continuousOn.mono hsub
  have hA : IntervalIntegrable (fun s => deriv (deriv ψ) s) volume a b :=
    ContinuousOn.intervalIntegrable_of_Icc hab hcont2
  have hB : IntervalIntegrable (fun s => deriv (fun t : ℝ => Real.tan t * ψ t) s) volume a b :=
    ContinuousOn.intervalIntegrable_of_Icc hab hcont1
  have hC : IntervalIntegrable (fun s => ψ s) volume a b :=
    ContinuousOn.intervalIntegrable_of_Icc hab hcont0
  have hEqOn : Set.EqOn (Work.FTS.EllipticEst.Lzero1 ψ) (Work.FTS.VocabO.GamBar α)
      (Set.uIcc a b) := by
    intro x hx
    rw [Set.uIcc_of_le hab] at hx
    exact hψ.eq x (hsub hx)
  have hint_eq : (∫ s in a..b, Work.FTS.EllipticEst.Lzero1 ψ s)
      = ∫ s in a..b, Work.FTS.VocabO.GamBar α s :=
    intervalIntegral.integral_congr hEqOn
  have hfun2 : (∫ s in a..b, Work.FTS.EllipticEst.Lzero1 ψ s)
      = ∫ s in a..b,
          (-(deriv (deriv ψ) s) + deriv (fun t : ℝ => Real.tan t * ψ t) s - 6 * ψ s) := by
    apply intervalIntegral.integral_congr
    intro x hx
    simp only [Work.FTS.EllipticEst.Lzero1]
  have hsum : (∫ s in a..b, (-(deriv (deriv ψ) s) + deriv (fun t : ℝ => Real.tan t * ψ t) s))
      = (∫ s in a..b, -(deriv (deriv ψ) s))
        + (∫ s in a..b, deriv (fun t : ℝ => Real.tan t * ψ t) s) :=
    intervalIntegral.integral_add (f := fun s => -(deriv (deriv ψ) s))
      (g := fun s => deriv (fun t : ℝ => Real.tan t * ψ t) s) hA.neg hB
  have hC6 : (∫ s in a..b, 6 * ψ s) = 6 * (∫ s in a..b, ψ s) :=
    intervalIntegral.integral_const_mul 6 ψ
  have hsub2 :
      (∫ s in a..b, (-(deriv (deriv ψ) s) + deriv (fun t : ℝ => Real.tan t * ψ t) s) - 6 * ψ s)
      = (∫ s in a..b, (-(deriv (deriv ψ) s) + deriv (fun t : ℝ => Real.tan t * ψ t) s))
        - (∫ s in a..b, 6 * ψ s) :=
    intervalIntegral.integral_sub
      (f := fun s => -(deriv (deriv ψ) s) + deriv (fun t : ℝ => Real.tan t * ψ t) s)
      (g := fun s => 6 * ψ s) (hA.neg.add hB) (hC.const_mul 6)
  have hneg : (∫ s in a..b, -(deriv (deriv ψ) s)) = -(∫ s in a..b, deriv (deriv ψ) s) :=
    intervalIntegral.integral_neg (f := fun s => deriv (deriv ψ) s)
  have hmem : ∀ x ∈ Set.uIcc a b, x ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) := by
    intro x hx
    rw [Set.uIcc_of_le hab] at hx
    exact hsub hx
  have hAval : (∫ s in a..b, deriv (deriv ψ) s) = deriv ψ b - deriv ψ a :=
    intervalIntegral.integral_deriv_eq_sub
      (fun x hx => (hd1'.contDiffAt ((isOpen_Ioo.mem_nhds (hmem x hx)))).differentiableAt
        (by norm_num)) hA
  have hBval : (∫ s in a..b, deriv (fun t : ℝ => Real.tan t * ψ t) s)
      = Real.tan b * ψ b - Real.tan a * ψ a :=
    intervalIntegral.integral_deriv_eq_sub
      (fun x hx => (hprod.contDiffAt ((isOpen_Ioo.mem_nhds (hmem x hx)))).differentiableAt
        (by norm_num)) hB
  rw [← hint_eq, hfun2, hsub2, hsum, hneg, hC6, hAval, hBval]
  ring

/-- The integrated form of the model equation for an arbitrary pair of points of `(0, π/2)`. -/
theorem psi_deriv_tan_form {α : ℝ} {ψ : ℝ → ℝ} (hψ : Work.FTS.PhiStar.AngModel α ψ)
    {a b : ℝ} (ha : 0 < a) (ha2 : a < Real.pi / 2) (hb : 0 < b) (hb2 : b < Real.pi / 2) :
    deriv ψ a - Real.tan a * ψ a
      = deriv ψ b - Real.tan b * ψ b + 6 * (∫ s in a..b, ψ s)
        + ∫ s in a..b, Work.FTS.VocabO.GamBar α s := by
  rcases le_total a b with hab | hba
  · exact psi_deriv_tan_form_le hψ ha hab hb2
  · have h := psi_deriv_tan_form_le (ψ := ψ) hψ hb hba ha2
    rw [intervalIntegral.integral_symm a b, intervalIntegral.integral_symm a b] at h
    linarith [h]


end Work.FTS.PhiStar.Series.Deleg
