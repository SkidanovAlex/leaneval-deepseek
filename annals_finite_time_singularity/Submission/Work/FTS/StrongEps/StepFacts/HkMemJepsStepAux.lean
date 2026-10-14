import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.MeasureTheory.Function.JacobianOneDim
import Submission.Work.FTS.StrongEps.SmoothOpen_Jeps
import Submission.Work.FTS.StrongEps.StepFacts.StepPointwise
import Submission.Work.FTS.StrongPersist.H6Rows.Npair6SupAux.StarSlotPcs.DzdIterBound
import Submission.Work.FTS.StrongPersist.SupOpenH2
import Submission.Work.FTS_EllLimOK.IsBslSolPos_add
import Submission.Work.FTS_RegExport.RXT.Slots.JetCalc.Expand
import Submission.Work.FTS_RegExport.RXT.starVop
import Submission.Work.FTS_RegExport.RXT.velVanish2Star
import Submission.Work.FTS_StreamBdry.Inputs.theta_part_theta
import Submission.Work.Spaces.sin_two_rpow

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Submission/Work/FTS/StrongEps/StepFacts/HkMemJepsStepAux.lean`

The auxiliary lemmas of the one-order smoothing statement `HkMem_Jeps_step` (the membership
`HkMem α (m-1) u ⟹ HkMem α m (J_ε u)` for the log-coordinate mollifier `J_ε = Jeps ρ ε`), put in
a separate module so that each file stays inside the harness size limit.

The two shorthands `Kd`/`Fd` assemble the `p`-integrand of the pointwise step `step_pointwise`,
and the four lemmas give, for the density `Ψ = Psi ρ ε = ε⁻¹ · Jker (ρ + |∂₁ρ| + |∂₂ρ|) ε`:

* `hjstep_Psi_support`: the support of `Ψ` is contained in the ball of radius `ε`;
* `hjstep_Psi_mul_exp_bound`: `Ψ p · e^{γ|p|}` is bounded;
* `hjstep_Psi_comp_zShift_lt_top`: `∫⁻ p, Ψ p e^{γ|p|} G (z e^{-p₁}) < ⊤` for every `G` with
  finite mass on `(0,∞)` (the substitute for `Jker_comp_zShift_lt_top`, whose kernel is `Ψ`);
* `hjstep_aemeasurable_pair_slice_Psi`: the pair measurability of `Ψ` against a shifted slot.
-/

noncomputable section

namespace Work.FTS.StrongEps.StepFacts

open scoped Real Topology ENNReal
open MeasureTheory Set Filter

set_option autoImplicit false
set_option maxHeartbeats 2000000

/-! ## Two shorthands -/

/-- The `p`-only part of the density of the pointwise step. -/
def Kd (ρ : ℝ × ℝ → ℝ) (ε c : ℝ) : ℝ × ℝ → ℝ≥0∞ :=
  fun p => ENNReal.ofReal (Psi ρ ε p) * ENNReal.ofReal (Real.exp (2 * c * (|p.1| + |p.2|)))

/-- The shifted level-`m-1` integrand of `u`, as a function of the shift `p`. -/
def Fd (α : ℝ) (m : ℕ) (u : ℝ → ℝ → ℝ) (z θ : ℝ) : ℝ × ℝ → ℝ≥0∞ :=
  fun p => ENNReal.ofReal (Work.Spaces.HkIntegrand α (m - 1) u
    (Work.FTS.StrongEps.zShift z p.1) (Work.FTS.StrongEps.thShift θ p.2))

/-! ## The one-dimensional substitution `u = z e^{-x}`

The private lemma of `JepsHkMem/Jker_comp_zShift_lt_top.lean`, restated (and renamed) so that it
can be used for the density `Ψ` as well. -/

lemma hjstep_lintegral_Icc_expNeg_le {G : ℝ → ℝ≥0∞} {ε z : ℝ} (hε : 0 < ε) (hz : 0 < z) :
    (∫⁻ x in Set.Icc (-ε) ε, G (z * Real.exp (-x)))
      ≤ ENNReal.ofReal (Real.exp ε / z) * ∫⁻ u in Set.Ioi 0, G u := by
  have hzε : 0 < z * Real.exp (-ε) := mul_pos hz (Real.exp_pos _)
  have hderiv : ∀ x ∈ Set.Icc (-ε) ε,
      HasDerivWithinAt (fun x : ℝ => z * Real.exp (-x)) (-(z * Real.exp (-x)))
        (Set.Icc (-ε) ε) x := by
    intro x _
    have h' : HasDerivAt (fun x : ℝ => Real.exp (-x)) (-Real.exp (-x)) x := by
      have h1 : HasDerivAt (fun x : ℝ => Real.exp (-x)) (Real.exp (-x) * (-1)) x :=
        (Real.hasDerivAt_exp (-x)).comp x (hasDerivAt_neg x)
      simpa using h1
    have h2 : HasDerivAt (fun x : ℝ => z * Real.exp (-x)) (-(z * Real.exp (-x))) x := by
      have h3 := h'.const_mul z
      simpa using h3
    exact h2.hasDerivWithinAt
  have hinj : Set.InjOn (fun x : ℝ => z * Real.exp (-x)) (Set.Icc (-ε) ε) := by
    intro x _ y _ hxy
    have hexp : Real.exp (-x) = Real.exp (-y) := mul_left_cancel₀ hz.ne' hxy
    have h2 : -x = -y := Real.exp_injective hexp
    linarith
  have hkey := MeasureTheory.lintegral_image_eq_lintegral_abs_deriv_mul
    (s := Set.Icc (-ε) ε) (f := fun x : ℝ => z * Real.exp (-x))
    (f' := fun x : ℝ => -(z * Real.exp (-x))) measurableSet_Icc hderiv hinj G
  have himage_sub : (fun x : ℝ => z * Real.exp (-x)) '' Set.Icc (-ε) ε ⊆ Set.Ioi 0 := by
    rintro u ⟨x, _, rfl⟩
    exact mul_pos hz (Real.exp_pos _)
  have hpt : ∀ x : ℝ, ENNReal.ofReal |(-(z * Real.exp (-x)))| * G (z * Real.exp (-x))
      = ENNReal.ofReal (z * Real.exp (-x)) * G (z * Real.exp (-x)) := by
    intro x
    rw [abs_neg, abs_of_pos (mul_pos hz (Real.exp_pos _))]
  have h1 : ENNReal.ofReal (z * Real.exp (-ε))
        * (∫⁻ x in Set.Icc (-ε) ε, G (z * Real.exp (-x)))
      ≤ ∫⁻ x in Set.Icc (-ε) ε,
          ENNReal.ofReal |(-(z * Real.exp (-x)))| * G (z * Real.exp (-x)) := by
    rw [← lintegral_const_mul' (ENNReal.ofReal (z * Real.exp (-ε)))
      (fun x => G (z * Real.exp (-x))) ENNReal.ofReal_ne_top]
    refine setLIntegral_mono' measurableSet_Icc ?_
    intro x hx
    rw [hpt x]
    refine mul_le_mul_of_nonneg_right ?_ zero_le
    exact ENNReal.ofReal_le_ofReal
      (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by linarith [hx.2])) hz.le)
  have h2 : (∫⁻ x in Set.Icc (-ε) ε,
        ENNReal.ofReal |(-(z * Real.exp (-x)))| * G (z * Real.exp (-x)))
      ≤ ∫⁻ u in Set.Ioi 0, G u := by
    rw [← hkey]
    exact lintegral_mono_set himage_sub
  have hfin' : ENNReal.ofReal (z * Real.exp (-ε))
        * (∫⁻ x in Set.Icc (-ε) ε, G (z * Real.exp (-x)))
      ≤ ∫⁻ u in Set.Ioi 0, G u := le_trans h1 h2
  have hne0 : ENNReal.ofReal (z * Real.exp (-ε)) ≠ 0 := by
    rw [ENNReal.ofReal_ne_zero_iff]; exact hzε
  have hneTop : ENNReal.ofReal (z * Real.exp (-ε)) ≠ ⊤ := ENNReal.ofReal_ne_top
  have hstep : (∫⁻ x in Set.Icc (-ε) ε, G (z * Real.exp (-x)))
      ≤ (ENNReal.ofReal (z * Real.exp (-ε)))⁻¹ * ∫⁻ u in Set.Ioi 0, G u := by
    calc (∫⁻ x in Set.Icc (-ε) ε, G (z * Real.exp (-x)))
        = 1 * (∫⁻ x in Set.Icc (-ε) ε, G (z * Real.exp (-x))) := (one_mul _).symm
      _ = (ENNReal.ofReal (z * Real.exp (-ε)))⁻¹ * ENNReal.ofReal (z * Real.exp (-ε))
            * (∫⁻ x in Set.Icc (-ε) ε, G (z * Real.exp (-x))) := by
          rw [ENNReal.inv_mul_cancel hne0 hneTop]
      _ = (ENNReal.ofReal (z * Real.exp (-ε)))⁻¹ *
            (ENNReal.ofReal (z * Real.exp (-ε))
              * (∫⁻ x in Set.Icc (-ε) ε, G (z * Real.exp (-x)))) := by
          rw [mul_assoc]
      _ ≤ (ENNReal.ofReal (z * Real.exp (-ε)))⁻¹ * ∫⁻ u in Set.Ioi 0, G u :=
          mul_le_mul_of_nonneg_left hfin' zero_le
  have hreal : (z * Real.exp (-ε))⁻¹ = Real.exp ε / z := by
    rw [Real.exp_neg, mul_inv, inv_inv, div_eq_mul_inv, mul_comm]
  have hconst_eq : (ENNReal.ofReal (z * Real.exp (-ε)))⁻¹ = ENNReal.ofReal (Real.exp ε / z) := by
    rw [← ENNReal.ofReal_inv_of_pos hzε, hreal]
  rwa [hconst_eq] at hstep

/-! ## Support and pointwise bound of the density `Ψ = ε⁻¹ Jker ρ̃ ε` -/

lemma hjstep_Psi_support (ρ : ℝ × ℝ → ℝ) (hρ : Work.FTS.StrongEps.IsSmoothKernel ρ)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ p : ℝ × ℝ, Psi ρ ε p ≠ 0 → p.1 ^ 2 + p.2 ^ 2 ≤ ε ^ 2 := by
  intro p hp
  have h1 : Work.FTS.StrongEps.Jker (rhoTilde ρ) ε p ≠ 0 := by
    intro h
    exact hp (by simp only [Psi, h, mul_zero])
  have h2 : rhoTilde ρ (ε⁻¹ • p) ≠ 0 := by
    intro h
    exact h1 (by simp only [Work.FTS.StrongEps.Jker, h, mul_zero])
  have h3 := rhoTilde_support ρ hρ h2
  simp only [Prod.smul_fst, Prod.smul_snd, smul_eq_mul] at h3
  have hp1 : (ε⁻¹ * p.1) ^ 2 = ε⁻¹ ^ 2 * p.1 ^ 2 := by ring
  have hp2 : (ε⁻¹ * p.2) ^ 2 = ε⁻¹ ^ 2 * p.2 ^ 2 := by ring
  rw [hp1, hp2] at h3
  have hεi : ε ^ 2 * ε⁻¹ ^ 2 = 1 := by field_simp
  have hmul := mul_le_mul_of_nonneg_left h3 (sq_nonneg ε)
  have h1' : ε ^ 2 * (ε⁻¹ ^ 2 * p.1 ^ 2) = p.1 ^ 2 := by rw [← mul_assoc, hεi, one_mul]
  have h2' : ε ^ 2 * (ε⁻¹ ^ 2 * p.2 ^ 2) = p.2 ^ 2 := by rw [← mul_assoc, hεi, one_mul]
  rw [mul_add, h1', h2', mul_one] at hmul
  exact hmul

lemma hjstep_Psi_mul_exp_bound (ρ : ℝ × ℝ → ℝ)
    (hρ : Work.FTS.StrongEps.IsSmoothKernel ρ)
    {ε γ : ℝ} (hε : 0 < ε) (hγ : 0 ≤ γ) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ p : ℝ × ℝ, Psi ρ ε p * Real.exp (γ * (|p.1| + |p.2|)) ≤ D := by
  obtain ⟨B, hB⟩ := (isCompact_closedBall (0 : ℝ × ℝ) 1).exists_bound_of_continuousOn
    (rhoTilde_continuous ρ hρ).continuousOn
  refine ⟨max (ε⁻¹ * (ε⁻¹ ^ 2 * max B 0) * Real.exp (γ * (2 * ε))) 0,
    le_max_right _ _, fun p => ?_⟩
  have hB0 : 0 ≤ max B 0 := le_max_right _ _
  have hbound : rhoTilde ρ (ε⁻¹ • p) ≤ max B 0 := by
    by_cases hp : (ε⁻¹ • p) ∈ Metric.closedBall (0 : ℝ × ℝ) 1
    · have h := hB _ hp
      rw [Real.norm_eq_abs] at h
      exact le_trans (le_abs_self _) (le_trans h (le_max_left _ _))
    · have hz : rhoTilde ρ (ε⁻¹ • p) = 0 := by
        by_contra h
        have hsupp := rhoTilde_support ρ hρ h
        have hlt : 1 < max |(ε⁻¹ • p).1| |(ε⁻¹ • p).2| := by
          rw [Metric.mem_closedBall, dist_zero_right, Prod.norm_def] at hp
          rw [Real.norm_eq_abs, Real.norm_eq_abs] at hp
          exact not_le.mp hp
        rcases lt_max_iff.mp hlt with hlt1 | hlt2
        · have h2 : 1 < (ε⁻¹ • p).1 ^ 2 := by
            rw [← sq_abs]
            nlinarith [hlt1, abs_nonneg ((ε⁻¹ • p).1)]
          have h3 : 1 < (ε⁻¹ • p).1 ^ 2 + (ε⁻¹ • p).2 ^ 2 := by
            nlinarith [sq_nonneg ((ε⁻¹ • p).2)]
          exact absurd hsupp (not_le.mpr h3)
        · have h2 : 1 < (ε⁻¹ • p).2 ^ 2 := by
            rw [← sq_abs]
            nlinarith [hlt2, abs_nonneg ((ε⁻¹ • p).2)]
          have h3 : 1 < (ε⁻¹ • p).1 ^ 2 + (ε⁻¹ • p).2 ^ 2 := by
            nlinarith [sq_nonneg ((ε⁻¹ • p).1)]
          exact absurd hsupp (not_le.mpr h3)
      rw [hz]; exact hB0
  have hPsi : Psi ρ ε p ≤ ε⁻¹ * (ε⁻¹ ^ 2 * max B 0) := by
    rw [Psi, Work.FTS.StrongEps.Jker]
    exact mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_left hbound (sq_nonneg _)) (by positivity)
  by_cases hp : Psi ρ ε p = 0
  · rw [hp, zero_mul]
    exact le_max_right _ _
  · have hb : |p.1| + |p.2| ≤ 2 * ε := by
      have hsupp := hjstep_Psi_support ρ hρ hε p hp
      have h1 : p.1 ^ 2 ≤ ε ^ 2 := by nlinarith [sq_nonneg p.2]
      have h2 : p.2 ^ 2 ≤ ε ^ 2 := by nlinarith [sq_nonneg p.1]
      have ha : |p.1| ≤ ε := by
        rw [sq_le_sq] at h1
        rwa [abs_of_nonneg hε.le] at h1
      have hb' : |p.2| ≤ ε := by
        rw [sq_le_sq] at h2
        rwa [abs_of_nonneg hε.le] at h2
      linarith
    have hexp : Real.exp (γ * (|p.1| + |p.2|)) ≤ Real.exp (γ * (2 * ε)) := by
      rw [Real.exp_le_exp]
      exact mul_le_mul_of_nonneg_left hb hγ
    have hle : Psi ρ ε p * Real.exp (γ * (|p.1| + |p.2|))
        ≤ (ε⁻¹ * (ε⁻¹ ^ 2 * max B 0)) * Real.exp (γ * (2 * ε)) :=
      mul_le_mul hPsi hexp (Real.exp_pos _).le (by positivity)
    exact hle.trans (le_max_left _ _)

/-! ## Finiteness of the `Ψ`-weighted shifted integral -/

/-- **Finiteness of the `Ψ`-weighted shifted integral.**  For any `ℝ≥0∞`-valued `G` with finite
mass on `(0,∞)`, `∫⁻ p, Ψ p e^{γ|p|} G (z e^{-p₁})` is finite: `Ψ` is compactly supported in the
ball of radius `ε`, so the `p`-integral is a bounded multiple of the integral of `G` over the
image of `[-ε,ε]` under `x ↦ z e^{-x}`, which the substitution `u = z e^{-x}` controls by the
mass of `G` with the factor `e^ε / z`. -/
theorem hjstep_Psi_comp_zShift_lt_top (ρ : ℝ × ℝ → ℝ)
    (hρ : Work.FTS.StrongEps.IsSmoothKernel ρ)
    {ε z γ : ℝ} (hε : 0 < ε) (hz : 0 < z) (hγ : 0 ≤ γ) {G : ℝ → ℝ≥0∞}
    (hfin : (∫⁻ u in Set.Ioi 0, G u) < ⊤) :
    (∫⁻ p : ℝ × ℝ, ENNReal.ofReal (Psi ρ ε p)
      * ENNReal.ofReal (Real.exp (γ * (|p.1| + |p.2|)))
      * G (z * Real.exp (-(p.1)))) < ⊤ := by
  obtain ⟨D, hD0, hD⟩ := hjstep_Psi_mul_exp_bound ρ hρ hε hγ
  set s : Set ℝ := Set.Icc (-ε) ε with hs
  set Φ : ℝ × ℝ → ℝ≥0∞ := fun p => G (z * Real.exp (-(p.1))) with hΦdef
  have hΦa : ∀ p : ℝ × ℝ, Φ p = G (z * Real.exp (-(p.1))) := fun p => by simp only [hΦdef]
  have hpt : ∀ p : ℝ × ℝ,
      ENNReal.ofReal (Psi ρ ε p) * ENNReal.ofReal (Real.exp (γ * (|p.1| + |p.2|))) * Φ p
        ≤ ENNReal.ofReal D * (Metric.closedBall (0 : ℝ × ℝ) ε).indicator Φ p := by
    intro p
    by_cases hp : p ∈ Metric.closedBall (0 : ℝ × ℝ) ε
    · rw [indicator_of_mem hp]
      rw [← ENNReal.ofReal_mul (Psi_nonneg ρ hρ hε p)]
      refine mul_le_mul_of_nonneg_right (ENNReal.ofReal_le_ofReal (hD p)) zero_le
    · have hz0 : Psi ρ ε p = 0 := by
        by_contra h
        have hsupp := hjstep_Psi_support ρ hρ hε p h
        have h1 : p.1 ^ 2 ≤ ε ^ 2 := by nlinarith [sq_nonneg p.2]
        have h2 : p.2 ^ 2 ≤ ε ^ 2 := by nlinarith [sq_nonneg p.1]
        have ha : |p.1| ≤ ε := by
          rw [sq_le_sq] at h1
          rwa [abs_of_nonneg hε.le] at h1
        have hb : |p.2| ≤ ε := by
          rw [sq_le_sq] at h2
          rwa [abs_of_nonneg hε.le] at h2
        refine hp ?_
        rw [Metric.mem_closedBall, dist_zero_right, Prod.norm_def]
        exact max_le ha hb
      rw [indicator_of_notMem hp, mul_zero, hz0, ENNReal.ofReal_zero, zero_mul, zero_mul]
  have h1 : (∫⁻ p : ℝ × ℝ, ENNReal.ofReal (Psi ρ ε p)
        * ENNReal.ofReal (Real.exp (γ * (|p.1| + |p.2|))) * Φ p)
      ≤ ENNReal.ofReal D * ∫⁻ p in Metric.closedBall (0 : ℝ × ℝ) ε, Φ p := by
    calc (∫⁻ p : ℝ × ℝ, ENNReal.ofReal (Psi ρ ε p)
          * ENNReal.ofReal (Real.exp (γ * (|p.1| + |p.2|))) * Φ p)
        ≤ ∫⁻ p : ℝ × ℝ,
            ENNReal.ofReal D * (Metric.closedBall (0 : ℝ × ℝ) ε).indicator Φ p :=
          lintegral_mono hpt
      _ = ENNReal.ofReal D
            * ∫⁻ p : ℝ × ℝ, (Metric.closedBall (0 : ℝ × ℝ) ε).indicator Φ p :=
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
      _ = ENNReal.ofReal D * ∫⁻ p in Metric.closedBall (0 : ℝ × ℝ) ε, Φ p := by
          rw [lintegral_indicator (Metric.isClosed_closedBall.measurableSet) Φ]
  have hball_sub : Metric.closedBall (0 : ℝ × ℝ) ε ⊆ s ×ˢ s := by
    intro p hp
    rw [Metric.mem_closedBall, dist_zero_right, Prod.norm_def] at hp
    have hp' : max |p.1| |p.2| ≤ ε := by simpa only [Real.norm_eq_abs] using hp
    have h1 : |p.1| ≤ ε := le_trans (le_max_left _ _) hp'
    have h2 : |p.2| ≤ ε := le_trans (le_max_right _ _) hp'
    rw [hs]
    exact ⟨abs_le.mp h1, abs_le.mp h2⟩
  have h2 : (∫⁻ p in Metric.closedBall (0 : ℝ × ℝ) ε, Φ p) ≤ ∫⁻ p in s ×ˢ s, Φ p :=
    lintegral_mono_set hball_sub
  have h3 : (∫⁻ p in s ×ˢ s, Φ p)
      = ∫⁻ p, Φ p ∂((MeasureTheory.volume.restrict s).prod (MeasureTheory.volume.restrict s)) := by
    rw [Measure.volume_eq_prod ℝ ℝ, Measure.prod_restrict]
  have h4 : (∫⁻ p, Φ p ∂((MeasureTheory.volume.restrict s).prod
        (MeasureTheory.volume.restrict s)))
      ≤ ∫⁻ x in s, ∫⁻ y in s, Φ (x, y) := lintegral_prod_le Φ
  have hinner : ∀ x : ℝ, (∫⁻ y in s, Φ (x, y))
      = ENNReal.ofReal (2 * ε) * G (z * Real.exp (-x)) := by
    intro x
    have hc : ∀ y : ℝ, Φ (x, y) = G (z * Real.exp (-x)) := fun y => by rw [hΦa]
    rw [show (∫⁻ y in s, Φ (x, y)) = ∫⁻ y in s, G (z * Real.exp (-x)) from
      lintegral_congr fun y => hc y]
    rw [setLIntegral_const, hs, Real.volume_Icc]
    have : (ε : ℝ) - -ε = 2 * ε := by ring
    rw [this]
    exact mul_comm _ _
  have h5 : (∫⁻ x in s, ∫⁻ y in s, Φ (x, y))
      = ENNReal.ofReal (2 * ε) * ∫⁻ x in s, G (z * Real.exp (-x)) := by
    rw [show (∫⁻ x in s, ∫⁻ y in s, Φ (x, y))
        = ∫⁻ x in s, ENNReal.ofReal (2 * ε) * G (z * Real.exp (-x)) from
      lintegral_congr fun x => hinner x]
    exact lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
  have h6 : (∫⁻ x in s, G (z * Real.exp (-x)))
      ≤ ENNReal.ofReal (Real.exp ε / z) * ∫⁻ u in Set.Ioi 0, G u := by
    simpa only [hs] using hjstep_lintegral_Icc_expNeg_le (G := G) hε hz
  have hstart : (∫⁻ p : ℝ × ℝ, ENNReal.ofReal (Psi ρ ε p)
        * ENNReal.ofReal (Real.exp (γ * (|p.1| + |p.2|))) * Φ p)
      = (∫⁻ p : ℝ × ℝ, ENNReal.ofReal (Psi ρ ε p)
          * ENNReal.ofReal (Real.exp (γ * (|p.1| + |p.2|)))
          * G (z * Real.exp (-(p.1)))) :=
    lintegral_congr fun p => by rw [hΦa p]
  have hK : ENNReal.ofReal D * (ENNReal.ofReal (2 * ε)
      * (ENNReal.ofReal (Real.exp ε / z) * ∫⁻ u in Set.Ioi 0, G u)) < ⊤ := by
    refine ENNReal.mul_lt_top ENNReal.ofReal_lt_top ?_
    refine ENNReal.mul_lt_top ENNReal.ofReal_lt_top ?_
    exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top hfin
  rw [← hstart]
  refine lt_of_le_of_lt ?_ hK
  calc (∫⁻ p : ℝ × ℝ, ENNReal.ofReal (Psi ρ ε p)
        * ENNReal.ofReal (Real.exp (γ * (|p.1| + |p.2|))) * Φ p)
      ≤ ENNReal.ofReal D * ∫⁻ p in Metric.closedBall (0 : ℝ × ℝ) ε, Φ p := h1
    _ ≤ ENNReal.ofReal D * ∫⁻ p in s ×ˢ s, Φ p :=
        mul_le_mul_of_nonneg_left h2 zero_le
    _ = ENNReal.ofReal D * ∫⁻ p, Φ p ∂((MeasureTheory.volume.restrict s).prod
          (MeasureTheory.volume.restrict s)) := by rw [h3]
    _ ≤ ENNReal.ofReal D * ∫⁻ x in s, ∫⁻ y in s, Φ (x, y) :=
        mul_le_mul_of_nonneg_left h4 zero_le
    _ = ENNReal.ofReal D
          * (ENNReal.ofReal (2 * ε) * ∫⁻ x in s, G (z * Real.exp (-x))) := by rw [h5]
    _ ≤ ENNReal.ofReal D * (ENNReal.ofReal (2 * ε)
          * (ENNReal.ofReal (Real.exp ε / z) * ∫⁻ u in Set.Ioi 0, G u)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h6 zero_le) zero_le

/-! ## Pair measurability of the density against the shifted slot -/

lemma hjstep_aemeasurable_pair_slice_Psi (ρ : ℝ × ℝ → ℝ)
    (hρ : Work.FTS.StrongEps.IsSmoothKernel ρ)
    {ε c z : ℝ} (hz : 0 < z) {H : ℝ → ℝ → ℝ}
    (hH : ContinuousOn (fun q : ℝ × ℝ => H q.1 q.2) Work.FTS.StrongEps.Quad) :
    AEMeasurable (fun q : ℝ × (ℝ × ℝ) =>
        ENNReal.ofReal (Psi ρ ε q.2) * ENNReal.ofReal (Real.exp (2 * c * (|q.2.1| + |q.2.2|)))
          * ENNReal.ofReal (H (Work.FTS.StrongEps.zShift z q.2.1)
              (Work.FTS.StrongEps.thShift q.1 q.2.2)))
      ((MeasureTheory.volume.restrict Work.Spaces.Iθ).prod MeasureTheory.volume) := by
  have hc : Continuous (fun q : ℝ × ℝ => ε⁻¹ * rhoTilde ρ q) :=
    (rhoTilde_continuous ρ hρ).const_mul _
  have hbase := JepsHkMem.aemeasurable_pair_slice (H := H) hH hc (ε := ε) (c := c) (z := z) hz
  refine hbase.congr (Eventually.of_forall fun q => ?_)
  simp only [Psi_eq_Jker]

end Work.FTS.StrongEps.StepFacts
