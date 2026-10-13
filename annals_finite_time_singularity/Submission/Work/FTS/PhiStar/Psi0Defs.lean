/-
# `Work.FTS.PhiStar.Psi0Defs` — the explicit angular model `ψ` solving `L₀ψ = Γ̄`

This file constructs the *explicit* solution of the angular model of `PhiStar.Defs`:

  `Lzero1 ψ = Γ̄`,  `ψ(0) = ψ(π/2) = 0`,  `∫ ψ sinθcos²θ = 0`,

with the source `Γ̄ = Γ/c − (5/4) sin 2θ` (`Work.FTS.VocabO.GamBar`), `Γ = (sinθcos²θ)^{α/3}`,
`c = ∫ Γ K`.  Writing `S = sin θ`, `C = cos θ`, the substitution `ψ = 2 S C · w = sin 2θ · w`
turns `L₀` into the divergence form `L₀(sin θ cos θ · w) = −(sin θ cos θ / μ) (μ w')'` with
`μ = S²C³`, so `L₀ ψ = g` is equivalent to

  `w'(θ) = P(θ)/S²`,   `P = G₀/(2C³)`,   `G₀(θ) = ∫_θ^{π/2} S C² g`.

The endpoint conditions `ψ(0) = ψ(π/2) = 0` are automatic (the prefactor `sin 2θ` vanishes), and
the single remaining free constant `K` is fixed by the moment condition `∫ ψ sinθcos²θ = 0`.
Using `Γ̄ = Γ/c − (5/4) sin 2θ` one has the *exact* decomposition

  `G₀ = (1/c) Ψ_Γ − (5/2) Ψ_S`,   `Ψ_Γ = ∫_θ^{π/2} S C² Γ`,   `Ψ_S = ∫_θ^{π/2} S² C³`,

with `Ψ_S` the *elementary* polynomial `2/15 − S³/3 + S⁵/5` (`PsiS`) and `Ψ_Γ` monotone with the
explicit slope `Ψ_Γ' = −S C² Γ` (`hasDerivAt_PsiG`).
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Submission.Work.FTS.PhiStar.Defs
import Submission.Work.FTS.PhiStar.Basic
import Submission.Work.Spaces.Gamma_WlInf

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology ContDiff
open MeasureTheory Set Filter

namespace Work.FTS.PhiStar

set_option autoImplicit false
set_option maxHeartbeats 1600000

/-! ## The elementary `Ψ_S` -/

/-- `Ψ_S(θ) = ∫_θ^{π/2} sin²t cos³t dt = 2/15 − sin³θ/3 + sin⁵θ/5`. -/
def PsiS (θ : ℝ) : ℝ := 2 / 15 - Real.sin θ ^ 3 / 3 + Real.sin θ ^ 5 / 5

lemma PsiS_zero : PsiS 0 = 2 / 15 := by simp [PsiS]

lemma PsiS_pi_div_two : PsiS (π / 2) = 0 := by
  simp only [PsiS, Real.sin_pi_div_two]
  norm_num

lemma hasDerivAt_PsiS (θ : ℝ) :
    HasDerivAt PsiS (-(Real.sin θ ^ 2 * Real.cos θ ^ 3)) θ := by
  have h3 : HasDerivAt (fun t : ℝ => Real.sin t ^ 3) (3 * Real.sin θ ^ 2 * Real.cos θ) θ := by
    have h := (Real.hasDerivAt_sin θ).pow 3
    rw [show ((fun t : ℝ => Real.sin t) ^ 3) = fun t : ℝ => Real.sin t ^ 3 from by
      funext t; rw [Pi.pow_apply]] at h
    simpa using h
  have h5 : HasDerivAt (fun t : ℝ => Real.sin t ^ 5) (5 * Real.sin θ ^ 4 * Real.cos θ) θ := by
    have h := (Real.hasDerivAt_sin θ).pow 5
    rw [show ((fun t : ℝ => Real.sin t) ^ 5) = fun t : ℝ => Real.sin t ^ 5 from by
      funext t; rw [Pi.pow_apply]] at h
    simpa using h
  have h3' : HasDerivAt (fun t : ℝ => Real.sin t ^ 3 / 3) (Real.sin θ ^ 2 * Real.cos θ) θ := by
    have hh := h3.div_const 3
    convert hh using 1
    ring
  have h5' : HasDerivAt (fun t : ℝ => Real.sin t ^ 5 / 5) (Real.sin θ ^ 4 * Real.cos θ) θ := by
    have hh := h5.div_const 5
    convert hh using 1
    ring
  have h := (h5'.sub h3').const_add (2 / 15)
  convert h using 1
  · funext t; simp only [PsiS, Pi.sub_apply]; ring
  · have hc : Real.cos θ ^ 2 = 1 - Real.sin θ ^ 2 := by
      linarith [Real.sin_sq_add_cos_sq θ]
    rw [show Real.cos θ ^ 3 = Real.cos θ * Real.cos θ ^ 2 from by ring, hc]
    ring

/-- **The fundamental integral of `Ψ_S`**: `∫_a^b sin²t cos³t dt = Ψ_S(a) − Ψ_S(b)`. -/
theorem integral_sin_sq_cos_cu (a b : ℝ) (hab : a ≤ b) :
    ∫ t in a..b, Real.sin t ^ 2 * Real.cos t ^ 3 = PsiS a - PsiS b := by
  have hcont : ContinuousOn PsiS (Set.Icc a b) := by
    change ContinuousOn (fun θ : ℝ => 2 / 15 - Real.sin θ ^ 3 / 3 + Real.sin θ ^ 5 / 5)
      (Set.Icc a b)
    fun_prop
  have hint : IntervalIntegrable (fun t : ℝ => -(Real.sin t ^ 2 * Real.cos t ^ 3))
      volume a b := (by fun_prop : Continuous fun t : ℝ =>
        -(Real.sin t ^ 2 * Real.cos t ^ 3)).intervalIntegrable _ _
  have hderiv : ∀ x ∈ Set.Ioo a b, HasDerivAt PsiS (-(Real.sin x ^ 2 * Real.cos x ^ 3)) x :=
    fun x _ => hasDerivAt_PsiS x
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hab hcont hderiv hint
  rw [intervalIntegral.integral_neg] at h
  linarith

/-- `Ψ_S(θ) = ∫_θ^{π/2} sin²t cos³t dt`. -/
theorem PsiS_eq_integral (θ : ℝ) (hθ : θ ≤ π / 2) :
    PsiS θ = ∫ t in θ..(π / 2), Real.sin t ^ 2 * Real.cos t ^ 3 := by
  rw [integral_sin_sq_cos_cu θ (π / 2) hθ, PsiS_pi_div_two, sub_zero]

/-- **The factorisation of `Ψ_S`**: `Ψ_S(θ) = (1−S)²(3S³+6S²+4S+2)/15`. -/
theorem PsiS_factor (θ : ℝ) :
    PsiS θ = (1 - Real.sin θ) ^ 2 *
      (3 * Real.sin θ ^ 3 + 6 * Real.sin θ ^ 2 + 4 * Real.sin θ + 2) / 15 := by
  have h : Real.sin θ ^ 2 + Real.cos θ ^ 2 = 1 := Real.sin_sq_add_cos_sq θ
  simp only [PsiS]
  nlinarith [h]

/-! ## Smoothness of `Γ`, and the `L∞` bound for `Γ̄` -/

/-- `Γ(θ) = (sinθ cos²θ)^{α/3}` is `C^∞` on `(0,π/2)`. -/
lemma contDiffOn_Gam (α : ℝ) :
    ContDiffOn ℝ (∞ : ℕ∞ω) (fun θ => Work.Spaces.Gam α θ) (Set.Ioo 0 (π / 2)) := by
  have hpos : ∀ θ ∈ Set.Ioo (0:ℝ) (π/2), 0 < Real.sin θ * Real.cos θ ^ 2 := by
    intro θ hθ
    have h1 : 0 < Real.sin θ := Real.sin_pos_of_pos_of_lt_pi hθ.1 (by linarith [hθ.2, Real.pi_pos])
    have h2 : 0 < Real.cos θ := Real.cos_pos_of_mem_Ioo ⟨by linarith [hθ.1, Real.pi_pos], hθ.2⟩
    positivity
  have hsm : ContDiffOn ℝ (∞ : ℕ∞ω) (fun θ : ℝ => Real.sin θ * Real.cos θ ^ 2)
      (Set.Ioo 0 (π / 2)) := by fun_prop
  have hlog : ContDiffOn ℝ (∞ : ℕ∞ω)
      (fun θ : ℝ => Real.log (Real.sin θ * Real.cos θ ^ 2)) (Set.Ioo 0 (π / 2)) :=
    hsm.log (fun θ hθ => ne_of_gt (hpos θ hθ))
  have hexp : ContDiffOn ℝ (∞ : ℕ∞ω)
      (fun θ : ℝ => Real.exp ((α / 3) * Real.log (Real.sin θ * Real.cos θ ^ 2)))
      (Set.Ioo 0 (π / 2)) := (((contDiffOn_const (c := α / 3) (s := Set.Ioo 0 (π / 2)))).mul hlog).exp
  refine hexp.congr (fun θ hθ => ?_)
  rw [Work.Spaces.Gam, Real.rpow_def_of_pos (hpos θ hθ), mul_comm]

/-- `Γ̄` is bounded on `[0,π/2]` by `1/c + 5/4`. -/
lemma abs_GamBar_le (α θ : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) (hθ : θ ∈ Set.Icc 0 (π / 2)) :
    |Work.FTS.VocabO.GamBar α θ| ≤ 1 / Work.Spaces.c α + 5 / 4 := by
  have hc := (Work.Spaces.c_bounds α hα hα1).1
  have hcpos : 0 < Work.Spaces.c α := by linarith
  have hG1 := (Work.Spaces.Gam_bounds α θ hα hθ).2
  have hG0 := (Work.Spaces.Gam_bounds α θ hα hθ).1
  rw [Work.FTS.VocabO.GamBar]
  have hsplit : |Work.Spaces.Gam α θ / Work.Spaces.c α - 5 / 4 * Real.sin (2 * θ)|
      ≤ |Work.Spaces.Gam α θ / Work.Spaces.c α| + |(5:ℝ) / 4 * Real.sin (2 * θ)| := by
    simpa only [sub_eq_add_neg, abs_neg] using
      abs_add_le (Work.Spaces.Gam α θ / Work.Spaces.c α) (-((5:ℝ) / 4 * Real.sin (2 * θ)))
  have h1 : |Work.Spaces.Gam α θ / Work.Spaces.c α| ≤ 1 / Work.Spaces.c α := by
    rw [abs_div, abs_of_pos hcpos, div_le_div_iff_of_pos_right hcpos, abs_of_nonneg hG0]
    exact hG1
  have h2 : |(5:ℝ) / 4 * Real.sin (2 * θ)| ≤ 5 / 4 := by
    rw [abs_mul, abs_of_pos (by norm_num : (0:ℝ) < 5 / 4)]
    have := Real.abs_sin_le_one (2 * θ)
    linarith
  linarith

/-! ## Continuity of the source integrands on the angular interval -/

/-- Pointwise `rpow` identity for the `Γ`-integrand on the angular interval. -/
lemma sin_cos_sq_Gam_eq (α t : ℝ) (hα : 0 ≤ α) (h0 : 0 ≤ Real.sin t * Real.cos t ^ 2) :
    Real.sin t * Real.cos t ^ 2 * Work.Spaces.Gam α t
      = (Real.sin t * Real.cos t ^ 2) ^ (1 + α / 3) := by
  rcases eq_or_lt_of_le h0 with h | h
  · rw [← h, Work.Spaces.Gam, Real.zero_rpow (by linarith : (1:ℝ) + α/3 ≠ 0), zero_mul]
  · rw [Work.Spaces.Gam]
    conv_rhs => rw [Real.rpow_add h 1 (α / 3)]
    rw [Real.rpow_one]

/-- On the closed angular interval the integrand `S C² Γ` is continuous (for `α ≥ 0`). -/
lemma continuousOn_sin_cos_sq_Gam (α : ℝ) (hα : 0 ≤ α) :
    ContinuousOn (fun t : ℝ => Real.sin t * Real.cos t ^ 2 * Work.Spaces.Gam α t)
      (Set.Icc 0 (π / 2)) := by
  have hbase : ContinuousOn (fun t : ℝ => (Real.sin t * Real.cos t ^ 2) ^ (1 + α / 3))
      (Set.Icc 0 (π / 2)) :=
    ((Real.continuous_sin.mul (Real.continuous_cos.pow 2)).continuousOn).rpow_const
      (fun t _ => Or.inr (by positivity))
  refine hbase.congr (fun t ht => ?_)
  have h1 : 0 ≤ Real.sin t :=
    Real.sin_nonneg_of_mem_Icc ⟨ht.1, by linarith [ht.2, Real.pi_pos]⟩
  have h2 : 0 ≤ Real.cos t :=
    Real.cos_nonneg_of_mem_Icc ⟨by linarith [ht.1, Real.pi_pos], ht.2⟩
  exact sin_cos_sq_Gam_eq α t hα (mul_nonneg h1 (by positivity))

/-- On the closed angular interval the source integrand `S C² Γ̄` is continuous (for `α ≥ 0`). -/
lemma continuousOn_sin_cos_sq_GamBar (α : ℝ) (hα : 0 ≤ α) :
    ContinuousOn (fun t : ℝ => Real.sin t * Real.cos t ^ 2 * Work.FTS.VocabO.GamBar α t)
      (Set.Icc 0 (π / 2)) := by
  have h1 := continuousOn_sin_cos_sq_Gam α hα
  have h2 : ContinuousOn (fun t : ℝ =>
      (5 / 2) * (Real.sin t ^ 2 * Real.cos t ^ 3)) (Set.Icc 0 (π / 2)) := by fun_prop
  refine ((h1.div_const (Work.Spaces.c α)).sub h2).congr (fun t _ => ?_)
  simp only [Work.FTS.VocabO.GamBar, Real.sin_two_mul, Pi.sub_apply]
  ring

/-- Interval-integrability of the source integrand on any subinterval of `[0,π/2]`. -/
lemma intervalIntegrable_GamBar (α : ℝ) (hα : 0 ≤ α) {a b : ℝ} (ha : 0 ≤ a)
    (hb : b ≤ π / 2) (hab : a ≤ b) :
    IntervalIntegrable (fun t : ℝ => Real.sin t * Real.cos t ^ 2 * Work.FTS.VocabO.GamBar α t)
      volume a b := by
  have hsub : Set.uIcc a b ⊆ Set.Icc 0 (π / 2) := by
    intro t ht
    rw [Set.uIcc_of_le hab] at ht
    exact ⟨le_trans ha ht.1, le_trans ht.2 hb⟩
  exact ((continuousOn_sin_cos_sq_GamBar α hα).mono hsub).intervalIntegrable

/-! ## The `Γ`-part `Ψ_Γ` of the source integral -/

/-- `Ψ_Γ(α,θ) = ∫_θ^{π/2} sin t cos²t Γ(α,t) dt`. -/
def PsiG (α θ : ℝ) : ℝ := ∫ t in θ..(π / 2), Real.sin t * Real.cos t ^ 2 * Work.Spaces.Gam α t

lemma PsiG_pi_div_two (α : ℝ) : PsiG α (π / 2) = 0 := by
  simp [PsiG]

/-- **The derivative of `Ψ_Γ`**: `Ψ_Γ' = − sin θ cos²θ Γ`. -/
theorem hasDerivAt_PsiG (α : ℝ) (hα : 0 ≤ α) {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (π / 2)) :
    HasDerivAt (PsiG α) (-(Real.sin θ * Real.cos θ ^ 2 * Work.Spaces.Gam α θ)) θ := by
  have hcontIcc := continuousOn_sin_cos_sq_Gam α hα
  have hsub : Set.uIcc θ (π / 2) ⊆ Set.Icc 0 (π / 2) := by
    intro t ht
    rw [Set.uIcc_of_le (le_of_lt hθ.2)] at ht
    exact ⟨le_trans (le_of_lt hθ.1) ht.1, ht.2⟩
  have hint : IntervalIntegrable (fun t : ℝ =>
      Real.sin t * Real.cos t ^ 2 * Work.Spaces.Gam α t) volume θ (π / 2) :=
    (hcontIcc.mono hsub).intervalIntegrable
  have hcat : ContinuousAt (fun t : ℝ =>
      Real.sin t * Real.cos t ^ 2 * Work.Spaces.Gam α t) θ :=
    hcontIcc.continuousAt (Icc_mem_nhds hθ.1 hθ.2)
  have hmeas : StronglyMeasurableAtFilter (fun t : ℝ =>
      Real.sin t * Real.cos t ^ 2 * Work.Spaces.Gam α t) (𝓝 θ) volume :=
    ContinuousOn.stronglyMeasurableAtFilter isOpen_Ioo
      (hcontIcc.mono (fun t ht => ⟨le_of_lt ht.1, le_of_lt ht.2⟩)) θ hθ
  exact intervalIntegral.integral_hasDerivAt_left hint hmeas hcat

/-- `Ψ_Γ` is `C^∞` on `(0,π/2)`. -/
lemma contDiffOn_PsiG (α : ℝ) (hα : 0 ≤ α) :
    ContDiffOn ℝ (∞ : ℕ∞ω) (PsiG α) (Set.Ioo 0 (π / 2)) := by
  have hSC : ContDiffOn ℝ (∞ : ℕ∞ω) (fun θ : ℝ => Real.sin θ * Real.cos θ ^ 2)
      (Set.Ioo 0 (π / 2)) := by fun_prop
  have hsm : ContDiffOn ℝ (∞ : ℕ∞ω)
      (fun θ : ℝ => -(Real.sin θ * Real.cos θ ^ 2 * Work.Spaces.Gam α θ))
      (Set.Ioo 0 (π / 2)) := (hSC.mul (contDiffOn_Gam α)).neg
  rw [contDiffOn_infty_iff_deriv_of_isOpen isOpen_Ioo]
  exact ⟨fun θ hθ => (hasDerivAt_PsiG α hα hθ).differentiableAt.differentiableWithinAt,
    hsm.congr (fun θ hθ => (hasDerivAt_PsiG α hα hθ).deriv)⟩

/-! ## The source integral `G₀` and its decomposition -/

/-- `G₀(α,θ) = ∫_θ^{π/2} sin t cos²t Γ̄(α,t) dt`. -/
def Gzero (α θ : ℝ) : ℝ := ∫ t in θ..(π / 2),
  Real.sin t * Real.cos t ^ 2 * Work.FTS.VocabO.GamBar α t

lemma Gzero_pi_div_two (α : ℝ) : Gzero α (π / 2) = 0 := by simp [Gzero]

/-- `G₀(0) = 0`, the solvability (moment) condition of the angular model. -/
theorem Gzero_zero (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1 / 4) : Gzero α 0 = 0 := by
  have hmom := GamBar_moment (α := α) hα (by linarith)
  simp only [Work.Spaces.Iθ, Work.Elliptic.sinCos2] at hmom
  rw [Gzero, intervalIntegral.integral_of_le (by linarith [Real.pi_pos] : (0:ℝ) ≤ π / 2),
    ← MeasureTheory.integral_Icc_eq_integral_Ioc]
  simpa only [mul_comm] using hmom

/-- **The decomposition of the source integral**: `G₀ = (1/c) Ψ_Γ − (5/2) Ψ_S`. -/
theorem Gzero_eq (α θ : ℝ) (hα : 0 ≤ α) (hθ0 : 0 ≤ θ) (hθ : θ ≤ π / 2) :
    Gzero α θ = (1 / Work.Spaces.c α) * PsiG α θ - (5 / 2) * PsiS θ := by
  have h1 : IntervalIntegrable (fun t : ℝ =>
      (1 / Work.Spaces.c α) * (Real.sin t * Real.cos t ^ 2 * Work.Spaces.Gam α t))
      volume θ (π / 2) :=
    (((continuousOn_sin_cos_sq_Gam α hα).const_mul _).mono (by
      intro t ht
      rw [Set.uIcc_of_le hθ] at ht
      exact ⟨le_trans hθ0 ht.1, ht.2⟩)).intervalIntegrable
  have h2 : IntervalIntegrable (fun t : ℝ =>
      (5 / 2) * (Real.sin t ^ 2 * Real.cos t ^ 3)) volume θ (π / 2) :=
    (by fun_prop : Continuous fun t : ℝ =>
      (5 / 2 : ℝ) * (Real.sin t ^ 2 * Real.cos t ^ 3)).intervalIntegrable _ _
  have hpt : ∀ t : ℝ, Real.sin t * Real.cos t ^ 2 * Work.FTS.VocabO.GamBar α t
      = (1 / Work.Spaces.c α) * (Real.sin t * Real.cos t ^ 2 * Work.Spaces.Gam α t)
        - (5 / 2) * (Real.sin t ^ 2 * Real.cos t ^ 3) := by
    intro t
    rw [Work.FTS.VocabO.GamBar, Real.sin_two_mul]
    ring
  rw [Gzero, intervalIntegral.integral_congr (fun t _ => hpt t),
    intervalIntegral.integral_sub h1 h2, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul, PsiG, ← PsiS_eq_integral θ hθ]

/-- **The derivative of `G₀`**: `G₀' = − sin θ cos²θ Γ̄`. -/
theorem hasDerivAt_Gzero (α : ℝ) (hα : 0 ≤ α) {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (π / 2)) :
    HasDerivAt (Gzero α) (-(Real.sin θ * Real.cos θ ^ 2 * Work.FTS.VocabO.GamBar α θ)) θ := by
  have hIcc := continuousOn_sin_cos_sq_GamBar α hα
  have hIoo : ContinuousOn (fun t : ℝ =>
      Real.sin t * Real.cos t ^ 2 * Work.FTS.VocabO.GamBar α t) (Set.Ioo 0 (π / 2)) :=
    hIcc.mono (fun t ht => ⟨le_of_lt ht.1, le_of_lt ht.2⟩)
  have hsub : Set.uIcc θ (π / 2) ⊆ Set.Icc 0 (π / 2) := by
    intro t ht
    rw [Set.uIcc_of_le (le_of_lt hθ.2)] at ht
    exact ⟨le_trans (le_of_lt hθ.1) ht.1, ht.2⟩
  have hint : IntervalIntegrable (fun t : ℝ =>
      Real.sin t * Real.cos t ^ 2 * Work.FTS.VocabO.GamBar α t) volume θ (π / 2) :=
    (hIcc.mono hsub).intervalIntegrable
  have hmeas : StronglyMeasurableAtFilter (fun t : ℝ =>
      Real.sin t * Real.cos t ^ 2 * Work.FTS.VocabO.GamBar α t) (𝓝 θ) volume :=
    ContinuousOn.stronglyMeasurableAtFilter isOpen_Ioo hIoo θ hθ
  have hcat : ContinuousAt (fun t : ℝ =>
      Real.sin t * Real.cos t ^ 2 * Work.FTS.VocabO.GamBar α t) θ :=
    hIcc.continuousAt (Icc_mem_nhds hθ.1 hθ.2)
  exact intervalIntegral.integral_hasDerivAt_left hint hmeas hcat

/-- `G₀` is `C^∞` on `(0,π/2)`. -/
lemma contDiffOn_Gzero (α : ℝ) (hα : 0 ≤ α) :
    ContDiffOn ℝ (∞ : ℕ∞ω) (Gzero α) (Set.Ioo 0 (π / 2)) := by
  have hSC : ContDiffOn ℝ (∞ : ℕ∞ω) (fun θ : ℝ => Real.sin θ * Real.cos θ ^ 2)
      (Set.Ioo 0 (π / 2)) := by fun_prop
  have hsm : ContDiffOn ℝ (∞ : ℕ∞ω)
      (fun θ : ℝ => -(Real.sin θ * Real.cos θ ^ 2 * Work.FTS.VocabO.GamBar α θ))
      (Set.Ioo 0 (π / 2)) := by
    have hG : ContDiffOn ℝ (∞ : ℕ∞ω) (fun θ : ℝ => Work.FTS.VocabO.GamBar α θ)
        (Set.Ioo 0 (π / 2)) :=
      ((contDiffOn_Gam α).div_const (Work.Spaces.c α)).sub (by fun_prop)
    exact (hSC.mul hG).neg
  rw [contDiffOn_infty_iff_deriv_of_isOpen isOpen_Ioo]
  exact ⟨fun θ hθ => (hasDerivAt_Gzero α hα hθ).differentiableAt.differentiableWithinAt,
    hsm.congr (fun θ hθ => (hasDerivAt_Gzero α hα hθ).deriv)⟩

/-- `G₀(θ) = −∫_0^θ sin t cos²t Γ̄`, using the vanishing `G₀(0) = 0`. -/
theorem Gzero_eq_neg (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1 / 4) (θ : ℝ)
    (hθ : θ ∈ Set.Icc 0 (π / 2)) :
    Gzero α θ = -∫ t in 0..θ, Real.sin t * Real.cos t ^ 2 * Work.FTS.VocabO.GamBar α t := by
  have hint1 : IntervalIntegrable (fun t : ℝ =>
      Real.sin t * Real.cos t ^ 2 * Work.FTS.VocabO.GamBar α t) volume 0 θ :=
    intervalIntegrable_GamBar α (le_of_lt hα) le_rfl hθ.2 hθ.1
  have hint2 : IntervalIntegrable (fun t : ℝ =>
      Real.sin t * Real.cos t ^ 2 * Work.FTS.VocabO.GamBar α t) volume θ (π / 2) :=
    intervalIntegrable_GamBar α (le_of_lt hα) hθ.1 le_rfl hθ.2
  have hadd := intervalIntegral.integral_add_adjacent_intervals hint1 hint2
  have h0 := Gzero_zero α hα hα1
  simp only [Gzero] at h0 ⊢
  linarith [hadd]

/-- The pointwise bound `|S C² Γ̄| ≤ 13t` on `[0,1]`. -/
lemma abs_sin_cos_sq_GamBar_le (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) {t : ℝ} (ht0 : 0 ≤ t)
    (ht1 : t ≤ 1) :
    |Real.sin t * Real.cos t ^ 2 * Work.FTS.VocabO.GamBar α t| ≤ 13 * t := by
  have htπ : t ≤ π / 2 := by have := Real.pi_gt_three; linarith
  have hmem : t ∈ Set.Icc (0:ℝ) (π / 2) := ⟨ht0, htπ⟩
  have hc := (Work.Spaces.c_bounds α hα hα1).1
  have hcpos : 0 < Work.Spaces.c α := by linarith
  have hc10 : 1 / Work.Spaces.c α ≤ 10 := by
    rw [div_le_iff₀ hcpos]; linarith
  have hsin : 0 ≤ Real.sin t := Real.sin_nonneg_of_mem_Icc ⟨ht0, by linarith [Real.pi_pos]⟩
  have hcos : 0 ≤ Real.cos t :=
    Real.cos_nonneg_of_mem_Icc ⟨by linarith [ht0, Real.pi_pos], htπ⟩
  have hG1 := (Work.Spaces.Gam_bounds α t hα hmem).2
  have hG0 := (Work.Spaces.Gam_bounds α t hα hmem).1
  have hsinle : Real.sin t ≤ t := Real.sin_le ht0
  have hsin2b : |Real.sin (2 * t)| ≤ 2 * t := by
    have h := Real.abs_sin_le_abs (x := 2 * t)
    rwa [abs_of_nonneg (by linarith : (0:ℝ) ≤ 2 * t)] at h
  have hcos2 : Real.cos t ^ 2 ≤ 1 := by nlinarith [Real.cos_sq_le_one t]
  have hSC1 : Real.sin t * Real.cos t ^ 2 ≤ t := by nlinarith [hsinle, hcos2, hsin]
  have hSC0 : 0 ≤ Real.sin t * Real.cos t ^ 2 := mul_nonneg hsin (by positivity)
  have hGb : |Work.FTS.VocabO.GamBar α t| ≤ 10 + (5 / 2) * t := by
    rw [Work.FTS.VocabO.GamBar]
    have hsplit : |Work.Spaces.Gam α t / Work.Spaces.c α - 5 / 4 * Real.sin (2 * t)|
        ≤ |Work.Spaces.Gam α t / Work.Spaces.c α| + |(5:ℝ) / 4 * Real.sin (2 * t)| := by
      simpa only [sub_eq_add_neg, abs_neg] using
        abs_add_le (Work.Spaces.Gam α t / Work.Spaces.c α) (-((5:ℝ) / 4 * Real.sin (2 * t)))
    have h1 : |Work.Spaces.Gam α t / Work.Spaces.c α| ≤ 10 := by
      rw [abs_of_nonneg (div_nonneg hG0 (le_of_lt hcpos))]
      calc Work.Spaces.Gam α t / Work.Spaces.c α ≤ 1 / Work.Spaces.c α :=
            div_le_div_of_nonneg_right hG1 (le_of_lt hcpos)
        _ ≤ 10 := hc10
    have h2 : |(5:ℝ) / 4 * Real.sin (2 * t)| ≤ (5 / 2) * t := by
      rw [abs_mul, abs_of_pos (by norm_num : (0:ℝ) < 5 / 4)]
      linarith [hsin2b]
    linarith
  rw [abs_mul, abs_of_nonneg hSC0]
  have hfin : Real.sin t * Real.cos t ^ 2 * |Work.FTS.VocabO.GamBar α t|
      ≤ t * (10 + (5 / 2) * t) := mul_le_mul hSC1 hGb (abs_nonneg _) ht0
  nlinarith [hfin, ht0, ht1]

/-- Near `0`: `|G₀(θ)| ≤ 7θ²` for `θ ∈ [0,1]`. -/
theorem Gzero_abs_le_sq (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1 / 4) {θ : ℝ}
    (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) : |Gzero α θ| ≤ 7 * θ ^ 2 := by
  have hθπ : θ ≤ π / 2 := by have := Real.pi_gt_three; linarith
  have hmem : θ ∈ Set.Icc (0:ℝ) (π / 2) := ⟨hθ0, hθπ⟩
  rw [Gzero_eq_neg α hα hα1 θ hmem, abs_neg]
  refine le_trans (intervalIntegral.abs_integral_le_integral_abs (f := fun t : ℝ =>
    Real.sin t * Real.cos t ^ 2 * Work.FTS.VocabO.GamBar α t) hθ0) ?_
  have hsub : Set.uIcc (0:ℝ) θ ⊆ Set.Icc 0 (π / 2) := by
    intro t ht
    rw [Set.uIcc_of_le hθ0] at ht
    exact ⟨ht.1, le_trans ht.2 hθπ⟩
  have hint : IntervalIntegrable (fun t : ℝ =>
      |Real.sin t * Real.cos t ^ 2 * Work.FTS.VocabO.GamBar α t|) volume 0 θ :=
    (((continuousOn_sin_cos_sq_GamBar α (le_of_lt hα)).mono hsub).abs).intervalIntegrable
  have hint2 : IntervalIntegrable (fun t : ℝ => 13 * t) volume 0 θ :=
    (continuous_const.mul continuous_id).intervalIntegrable _ _
  have hmono : (∫ t in 0..θ, |Real.sin t * Real.cos t ^ 2 * Work.FTS.VocabO.GamBar α t|)
      ≤ ∫ t in 0..θ, (13 * t) :=
    intervalIntegral.integral_mono_on hθ0 hint hint2 (fun t ht =>
      abs_sin_cos_sq_GamBar_le α hα (by linarith) ht.1 (le_trans ht.2 hθ1))
  have hval : (∫ t in 0..θ, (13 * t)) = 13 * θ ^ 2 / 2 := by
    rw [intervalIntegral.integral_const_mul, integral_id]
    ring
  linarith [hmono, hval, sq_nonneg θ]

/-- The elementary `L∞` bound for `G₀`: `|G₀(θ)| ≤ (1/c + 5/4)(π/2−θ) cos²θ`. -/
theorem Gzero_abs_le (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) {θ : ℝ}
    (hθ : θ ∈ Set.Icc 0 (π / 2)) :
    |Gzero α θ| ≤ (1 / Work.Spaces.c α + 5 / 4) * (π / 2 - θ) * Real.cos θ ^ 2 := by
  have hδ0 : 0 ≤ π / 2 - θ := by linarith [hθ.2]
  have hCpos : 0 ≤ Real.cos θ :=
    Real.cos_nonneg_of_mem_Icc ⟨by linarith [hθ.1, Real.pi_pos], hθ.2⟩
  rw [Gzero]
  refine le_trans (intervalIntegral.abs_integral_le_integral_abs hθ.2) ?_
  have hsub : Set.uIcc θ (π / 2) ⊆ Set.Icc 0 (π / 2) := by
    intro t ht
    rw [Set.uIcc_of_le hθ.2] at ht
    exact ⟨le_trans hθ.1 ht.1, ht.2⟩
  have hint : IntervalIntegrable (fun t : ℝ =>
      |Real.sin t * Real.cos t ^ 2 * Work.FTS.VocabO.GamBar α t|) volume θ (π / 2) :=
    (((continuousOn_sin_cos_sq_GamBar α (le_of_lt hα)).mono hsub).abs).intervalIntegrable
  have hint2 : IntervalIntegrable (fun _ : ℝ => Real.cos θ ^ 2 *
      (1 / Work.Spaces.c α + 5 / 4)) volume θ (π / 2) := continuous_const.intervalIntegrable _ _
  have hm : (∫ t in θ..(π / 2), |Real.sin t * Real.cos t ^ 2 *
      Work.FTS.VocabO.GamBar α t|)
      ≤ ∫ t in θ..(π / 2), Real.cos θ ^ 2 * (1 / Work.Spaces.c α + 5 / 4) := by
    refine intervalIntegral.integral_mono_on hθ.2 hint hint2 ?_
    intro t ht
    have htmem : t ∈ Set.Icc (0:ℝ) (π / 2) := ⟨le_trans hθ.1 ht.1, ht.2⟩
    have h1 : 0 ≤ Real.sin t := by
      have h0t : 0 ≤ t := le_trans hθ.1 ht.1
      have htπ' : t ≤ π := by linarith [ht.2, Real.pi_gt_three]
      exact Real.sin_nonneg_of_mem_Icc ⟨h0t, htπ'⟩
    have hcos : 0 ≤ Real.cos t :=
      Real.cos_nonneg_of_mem_Icc ⟨by linarith [hθ.1, ht.1, Real.pi_pos], ht.2⟩
    have h2 : Real.cos t ^ 2 ≤ Real.cos θ ^ 2 := by
      have hle := Real.cos_le_cos_of_nonneg_of_le_pi hθ.1
        (by linarith [ht.2, Real.pi_gt_three]) ht.1
      nlinarith [hcos, hCpos]
    have h3 : |Work.FTS.VocabO.GamBar α t| ≤ 1 / Work.Spaces.c α + 5 / 4 :=
      abs_GamBar_le α t hα hα1 htmem
    have h4 : Real.sin t * Real.cos t ^ 2 ≤ Real.cos θ ^ 2 := by
      nlinarith [Real.sin_le_one t, hcos]
    rw [abs_mul, abs_of_nonneg (mul_nonneg h1 (by positivity))]
    exact mul_le_mul h4 h3 (abs_nonneg _) (sq_nonneg _)
  have hval : (∫ t in θ..(π / 2), Real.cos θ ^ 2 * (1 / Work.Spaces.c α + 5 / 4))
      = (1 / Work.Spaces.c α + 5 / 4) * (π / 2 - θ) * Real.cos θ ^ 2 := by
    rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_const]
    ring
  linarith [hm, hval]

/-! ## `P = G₀/(2C³)`, its derivative and its elementary bounds -/

/-- `P(α,θ) = G₀(α,θ)/(2 cos³θ)`, the profile of `w' = P/sin²θ`. -/
def Pfun (α θ : ℝ) : ℝ := Gzero α θ / (2 * Real.cos θ ^ 3)

/-- **The derivative of `P`**: `P' = − S Γ̄/(2C) + 3 S P/C`. -/
theorem hasDerivAt_Pfun (α : ℝ) (hα : 0 ≤ α) {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (π / 2)) :
    HasDerivAt (Pfun α)
      (-(Real.sin θ * Work.FTS.VocabO.GamBar α θ / (2 * Real.cos θ))
        + 3 * Real.sin θ * Pfun α θ / Real.cos θ) θ := by
  have hCpos : 0 < Real.cos θ := Real.cos_pos_of_mem_Ioo ⟨by linarith [hθ.1, Real.pi_pos], hθ.2⟩
  have hden : HasDerivAt (fun t : ℝ => 2 * Real.cos t ^ 3)
      (-(6 * Real.sin θ * Real.cos θ ^ 2)) θ := by
    have h3 : HasDerivAt (fun t : ℝ => Real.cos t ^ 3)
        (3 * Real.cos θ ^ 2 * (-Real.sin θ)) θ := by
      have h := (Real.hasDerivAt_cos θ).pow 3
      rw [show ((fun t : ℝ => Real.cos t) ^ 3) = fun t : ℝ => Real.cos t ^ 3 from by
        funext t; rw [Pi.pow_apply]] at h
      simpa using h
    have hh := h3.const_mul (2 : ℝ)
    convert hh using 1
    ring
  have hnum : HasDerivAt (Gzero α)
      (-(Real.sin θ * Real.cos θ ^ 2 * Work.FTS.VocabO.GamBar α θ)) θ :=
    hasDerivAt_Gzero α hα hθ
  have hquot := hnum.div hden (by positivity)
  have hgoal : HasDerivAt (fun t : ℝ => Pfun α t)
      ((-(Real.sin θ * Real.cos θ ^ 2 * Work.FTS.VocabO.GamBar α θ) * (2 * Real.cos θ ^ 3)
        - Gzero α θ * -(6 * Real.sin θ * Real.cos θ ^ 2)) / (2 * Real.cos θ ^ 3) ^ 2) θ := hquot
  convert hgoal using 1
  rw [Pfun]
  field_simp
  ring

lemma contDiffOn_Pfun (α : ℝ) (hα : 0 ≤ α) :
    ContDiffOn ℝ (∞ : ℕ∞ω) (Pfun α) (Set.Ioo 0 (π / 2)) := by
  have hcos : ContDiffOn ℝ (∞ : ℕ∞ω) (fun θ : ℝ => 2 * Real.cos θ ^ 3) (Set.Ioo 0 (π/2)) := by
    fun_prop
  exact (contDiffOn_Gzero α hα).div hcos (fun θ hθ => by
    have hCpos : 0 < Real.cos θ := Real.cos_pos_of_mem_Ioo ⟨by linarith [hθ.1, Real.pi_pos], hθ.2⟩
    positivity)

/-- `|P(θ)| ≤ 20` on `[0,π/2]`. -/
theorem Pfun_abs_le (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1 / 4) {θ : ℝ}
    (hθ : θ ∈ Set.Icc 0 (π / 2)) : |Pfun α θ| ≤ 20 := by
  rcases eq_or_lt_of_le hθ.2 with hπ | hπ
  · rw [hπ, Pfun, Gzero_pi_div_two]
    simp [Real.cos_pi_div_two]
  · have hCpos : 0 < Real.cos θ :=
      Real.cos_pos_of_mem_Ioo ⟨by linarith [hθ.1, Real.pi_pos], hπ⟩
    have hδ0 : 0 ≤ π / 2 - θ := by linarith
    have hG := Gzero_abs_le α hα (by linarith) hθ
    have hcp : 1 / Work.Spaces.c α + 5 / 4 ≤ 12 := by
      have hc := (Work.Spaces.c_bounds α hα (by linarith)).1
      have h10 : 1 / Work.Spaces.c α ≤ 10 := by
        have h := one_div_le_one_div_of_le (by norm_num : (0:ℝ) < 1 / 10) hc
        have h2 : (1:ℝ) / (1 / 10) = 10 := by norm_num
        rwa [h2] at h
      linarith
    have hδ : π / 2 - θ ≤ (π / 2) * Real.cos θ := by
      have hsin : Real.cos θ = Real.sin (π / 2 - θ) := (Real.sin_pi_div_two_sub θ).symm
      have hh : (2 / π) * (π / 2 - θ) ≤ Real.sin (π / 2 - θ) :=
        Real.mul_le_sin hδ0 (by linarith [hθ.1, hπ, Real.pi_pos])
      rw [hsin]
      have hπ2 : (0:ℝ) < π / 2 := by positivity
      have h3 : (π / 2) * ((2 / π) * (π / 2 - θ)) ≤ (π / 2) * Real.sin (π / 2 - θ) :=
        mul_le_mul_of_nonneg_left hh (le_of_lt hπ2)
      have h4 : (π / 2) * ((2 / π) * (π / 2 - θ)) = π / 2 - θ := by
        field_simp
      linarith [h3, h4]
    rw [Pfun, abs_div, abs_of_pos (by positivity : (0:ℝ) < 2 * Real.cos θ ^ 3),
      div_le_iff₀ (by positivity : (0:ℝ) < 2 * Real.cos θ ^ 3)]
    have hC2 : (0:ℝ) ≤ Real.cos θ ^ 2 := sq_nonneg _
    calc |Gzero α θ| ≤ (1 / Work.Spaces.c α + 5 / 4) * (π / 2 - θ) * Real.cos θ ^ 2 := hG
      _ ≤ 12 * ((π / 2) * Real.cos θ) * Real.cos θ ^ 2 := by
          have h1 : (1 / Work.Spaces.c α + 5 / 4) * (π / 2 - θ)
              ≤ 12 * ((π / 2) * Real.cos θ) :=
            mul_le_mul hcp hδ hδ0 (by positivity)
          exact mul_le_mul_of_nonneg_right h1 hC2
      _ = 6 * π * Real.cos θ ^ 3 := by ring
      _ ≤ 20 * (2 * Real.cos θ ^ 3) := by nlinarith [hCpos, Real.pi_lt_four, pow_pos hCpos 3]

/-- Near `0`: `|P(θ)| ≤ 30θ²` for `θ ∈ [0,1/2]`. -/
theorem Pfun_abs_le_sq (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1 / 4) {θ : ℝ}
    (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1 / 2) : |Pfun α θ| ≤ 30 * θ ^ 2 := by
  have hC : (1 / 2 : ℝ) ≤ Real.cos θ := by
    have hπ : θ ≤ π / 3 := by have := Real.pi_gt_three; linarith
    have h1 : Real.cos (π / 3) ≤ Real.cos θ :=
      Real.cos_le_cos_of_nonneg_of_le_pi hθ0 (by linarith [Real.pi_pos]) hπ
    rwa [Real.cos_pi_div_three] at h1
  have hC3 : (1 / 8 : ℝ) ≤ Real.cos θ ^ 3 := by
    have h := pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 1 / 2) hC 3
    norm_num at h
    exact h
  rw [Pfun, abs_div, abs_of_pos (by positivity : (0:ℝ) < 2 * Real.cos θ ^ 3),
    div_le_iff₀ (by positivity : (0:ℝ) < 2 * Real.cos θ ^ 3)]
  have hG := Gzero_abs_le_sq α hα hα1 hθ0 (by linarith)
  nlinarith [hG, hC3, sq_nonneg θ]

/-- `|P(θ)/sin²θ| ≤ 500` on `[0,π/2]`. -/
theorem Pfun_div_sin_sq_le (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1 / 4) {θ : ℝ}
    (hθ : θ ∈ Set.Icc 0 (π / 2)) : |Pfun α θ / Real.sin θ ^ 2| ≤ 500 := by
  rw [abs_div, abs_of_nonneg (sq_nonneg (Real.sin θ))]
  have hbase : (0:ℝ) < 2 / π := by positivity
  rcases eq_or_lt_of_le hθ.1 with h0 | h0
  · rw [← h0]; simp [Pfun]
  · have hsin0 : 0 < Real.sin θ :=
      Real.sin_pos_of_pos_of_lt_pi h0 (by linarith [hθ.2, Real.pi_pos])
    rcases le_or_gt θ (1 / 2) with h | h
    · have hsin : (2 / π) * θ ≤ Real.sin θ := Real.mul_le_sin hθ.1 hθ.2
      have hsinB0 : 0 ≤ (2 / π) * θ := mul_nonneg (le_of_lt hbase) hθ.1
      have hsq : ((2 / π) * θ) ^ 2 ≤ Real.sin θ ^ 2 :=
        pow_le_pow_left₀ hsinB0 hsin 2
      have hP := Pfun_abs_le_sq α hα hα1 hθ.1 h
      have h2 : 0 < ((2 / π) * θ) ^ 2 := by positivity
      have hkey : |Pfun α θ| / Real.sin θ ^ 2 ≤ 30 * θ ^ 2 / ((2 / π) * θ) ^ 2 :=
        div_le_div₀ (by positivity) hP h2 hsq
      have hv : 30 * θ ^ 2 / ((2 / π) * θ) ^ 2 = 30 / (2 / π) ^ 2 := by
        rw [mul_pow]
        field_simp
      rw [hv] at hkey
      have hge : (1 / 4 : ℝ) ≤ (2 / π) ^ 2 := by
        have h1 : (1 / 2 : ℝ) ≤ 2 / π := by
          rw [le_div_iff₀ (by positivity : (0:ℝ) < π)]
          linarith [Real.pi_lt_four]
        nlinarith [h1]
      have hb : 30 / (2 / π) ^ 2 ≤ 500 := by
        rw [div_le_iff₀ (by positivity : (0:ℝ) < (2 / π) ^ 2)]
        nlinarith [hge]
      linarith
    · have hsin : (2 / π) * (1 / 2 : ℝ) ≤ Real.sin θ := by
        have h1 : (2 / π) * (1 / 2 : ℝ) ≤ (2 / π) * θ := mul_le_mul_of_nonneg_left h.le
          (le_of_lt hbase)
        linarith [Real.mul_le_sin hθ.1 hθ.2]
      have hbase2 : (0:ℝ) ≤ (2 / π) * (1 / 2 : ℝ) :=
        mul_nonneg (le_of_lt hbase) (by norm_num)
      have hsq : ((2 / π) * (1 / 2 : ℝ)) ^ 2 ≤ Real.sin θ ^ 2 :=
        pow_le_pow_left₀ hbase2 hsin 2
      have hP := Pfun_abs_le α hα hα1 hθ
      have h2 : 0 < ((2 / π) * (1 / 2 : ℝ)) ^ 2 := by positivity
      have hkey : |Pfun α θ| / Real.sin θ ^ 2 ≤ 20 / ((2 / π) * (1 / 2 : ℝ)) ^ 2 :=
        div_le_div₀ (by positivity) hP h2 hsq
      have hge : (1 / 4 : ℝ) ≤ (2 / π) * (1 / 2 : ℝ) := by
        have h1 : (1 / 2 : ℝ) ≤ 2 / π := by
          rw [le_div_iff₀ (by positivity : (0:ℝ) < π)]
          linarith [Real.pi_lt_four]
        linarith
      have hb : 20 / ((2 / π) * (1 / 2 : ℝ)) ^ 2 ≤ 500 := by
        rw [div_le_iff₀ h2]
        nlinarith [hge]
      linarith

end Work.FTS.PhiStar
