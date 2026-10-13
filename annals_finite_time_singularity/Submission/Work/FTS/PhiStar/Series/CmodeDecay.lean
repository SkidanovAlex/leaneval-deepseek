/-
Copyright: work module for the Elgindi finite-time singularity project.

# `Work.FTS.PhiStar.Series.CmodeDecay`

The mode coefficients `cmode m (fun _ θ => ψ θ) 0` of the angular model decay like
`1/(lam m · √(2m+1))`, uniformly in `α ∈ (0, 1/5]` and in the model `ψ`.

**Route.**  `cmode m F z` is the `e_m`-coefficient of the slice `F z ·` in the self-adjoint
weight `cos θ dθ`, so `cmode m F z · cmdD m = ∫_{Iθ} F z θ · e_m θ · cos θ`
(`cmode_mul_cmdD`, `cmdD m = ∫_{Iθ} e_m² cos`).  Since `ψ` solves `Lzero1 ψ = Γ̄`
(`AngModel.eq`) and `Lzero1 e_m = lam m · e_m` (`eFam_Lzero`), the self-adjointness of
`Lzero1` in the weight `cos θ` (`pairing_core`) turns the moment of `ψ` into the moment of the
*source*:

  `lam m · ∫_{Iθ} ψ e_m cos = ∫_{Iθ} Γ̄ e_m cos`.

The right-hand side is bounded by `(1/c + 5/4)·∫_{Iθ} |e_m| cos ≤ (23/2)·√(cmdD m)` by
Cauchy–Schwarz (proved here with the optimal AM–GM parameter, `l1_eFam_le_sqrt`), and
`cmdD m = (2m+2)(2m+3)/(4m+5)` (`eFam_norm_fts`) is `≥ (2m+1)/4` for `m ≥ 1`.  Assembling
gives the statement with the universal constant `C = 23`.

The self-adjointness computation integrates the pointwise identity

  `(d/dθ)(-(ψ e_m' - ψ' e_m) cos θ) = (ψ · Lzero1 e_m - (Lzero1 ψ) · e_m) · cos θ`

over `Iθ`; the boundary terms vanish because `ψ` and `e_m` both vanish at `θ = 0, π/2` and `ψ'`
is bounded on `(0, π/2)`, so `ψ' e_m cos → 0` at both ends.
-/
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Order.CompletePartialOrder
import Submission.Work.FTS.PhiStar.Defs
import Submission.Work.FTS.PhiStar.Series.Defs
import Submission.Work.FTS.PhiStar.Gegenbauer.eFam_Lzero
import Submission.Work.FTS.PhiStar.Gegenbauer.FamNormValue
import Submission.Work.FTS.PhiStar.Psi0_exists

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.PhiStar.Series

set_option autoImplicit false
set_option maxHeartbeats 1000000

local notation "Iθ" => Work.Spaces.Iθ
private abbrev eF (m : ℕ) : ℝ → ℝ := Work.FTS.PhiStar.Gegenbauer.eFam m
private abbrev lamF (m : ℕ) : ℝ := Work.FTS.PhiStar.Gegenbauer.lam m
private abbrev gamBar (p q : ℝ) : ℝ := Work.FTS.VocabO.GamBar p q

/-! ## Elementary facts about the modes, the weight and the source -/

/-- The set integral over `Iθ = [0, π/2]` is the interval integral over `0..π/2`. -/
theorem setIntegral_Iθ_eq_intervalIntegral' (g : ℝ → ℝ) :
    (∫ θ in Iθ, g θ) = ∫ θ in (0 : ℝ)..(Real.pi / 2), g θ := by
  rw [Work.Spaces.Iθ, MeasureTheory.integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (by linarith [Real.pi_pos] : (0 : ℝ) ≤ Real.pi / 2)]

/-- The squared `L²(Iθ, cos θ dθ)`-norm of the `m`-th Gegenbauer mode. -/
private def cmdD (m : ℕ) : ℝ := ∫ θ in Iθ, eF m θ ^ 2 * Real.cos θ

private theorem cmdD_eq (m : ℕ) : cmdD m
    = ((2 * (m : ℝ) + 2) * (2 * (m : ℝ) + 3)) / (4 * (m : ℝ) + 5) :=
  Work.FTS.PhiStar.Gegenbauer.eFam_norm_fts m

private theorem cmdD_pos (m : ℕ) : 0 < cmdD m := by
  rw [cmdD_eq]; positivity

/-- `cmdD m ≥ (2m+1)/4` for `m ≥ 1`. -/
private theorem cmdD_ge (m : ℕ) (hm : 1 ≤ m) : (2 * (m : ℝ) + 1) / 4 ≤ cmdD m := by
  rw [cmdD_eq]
  have hm' : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have h4 : (0 : ℝ) < 4 * (m : ℝ) + 5 := by linarith
  rw [le_div_iff₀ h4]
  nlinarith

/-- `∫_{Iθ} cos θ = 1`. -/
private theorem integral_cos_Iθ : (∫ θ in Iθ, Real.cos θ) = 1 := by
  rw [setIntegral_Iθ_eq_intervalIntegral', integral_cos, Real.sin_pi_div_two,
    Real.sin_zero, sub_zero]

private theorem cos_nonneg_Iθ : ∀ θ ∈ Iθ, (0 : ℝ) ≤ Real.cos θ := fun θ hθ =>
  Real.cos_nonneg_of_mem_Icc ⟨by linarith [hθ.1, Real.pi_pos], hθ.2⟩

private theorem zero_mem_Icc_pi : (0 : ℝ) ∈ Set.Icc (0 : ℝ) (Real.pi / 2) :=
  ⟨le_refl 0, by positivity⟩

private theorem pi_half_mem_Icc_pi : (Real.pi / 2) ∈ Set.Icc (0 : ℝ) (Real.pi / 2) :=
  ⟨by positivity, le_refl _⟩

private theorem integrableOn_Iθ_of_continuousOn {f : ℝ → ℝ}
    (hf : ContinuousOn f (Set.Icc (0 : ℝ) (Real.pi / 2))) : IntegrableOn f Iθ := by
  simpa only [Work.Spaces.Iθ] using hf.integrableOn_Icc

/-- `cmode m F z · cmdD m` is the `m`-th moment of the slice `F z ·`. -/
private theorem cmode_mul_cmdD (m : ℕ) (F : ℝ → ℝ → ℝ) (z : ℝ) :
    cmode m F z * cmdD m = ∫ θ in Iθ, F z θ * eF m θ * Real.cos θ := by
  have hD : cmdD m = ∫ θ in (0 : ℝ)..(Real.pi / 2), eF m θ ^ 2 * Real.cos θ :=
    setIntegral_Iθ_eq_intervalIntegral' _
  have hN : (∫ θ in Iθ, F z θ * eF m θ * Real.cos θ)
      = ∫ θ in (0 : ℝ)..(Real.pi / 2), F z θ * eF m θ * Real.cos θ :=
    setIntegral_Iθ_eq_intervalIntegral' _
  have hDne : (∫ θ in (0 : ℝ)..(Real.pi / 2), eF m θ ^ 2 * Real.cos θ) ≠ 0 := by
    rw [← hD]; exact ne_of_gt (cmdD_pos m)
  rw [cmode, hD, hN]
  field_simp

/-! ## Pointwise facts about the modes -/

/-- `gC (2m+1) 0 = 0` (the odd Gegenbauer polynomials vanish at the origin). -/
private theorem gC_odd_zero (m : ℕ) : Work.FTS.PhiStar.Gegenbauer.gC (2 * m + 1) 0 = 0 := by
  induction m with
  | zero =>
      rw [show Work.FTS.PhiStar.Gegenbauer.gC 1 = (fun x : ℝ => 3 * x) from rfl]
      norm_num
  | succ m ih =>
      have h := Work.FTS.PhiStar.Gegenbauer.gC_rec (2 * m + 1) 0
      have h1 : (2 * m + 1) + 2 = 2 * (m + 1) + 1 := by omega
      rw [h1] at h
      have h3 : (((2 * m + 1 : ℕ) : ℝ) + 3)
          * Work.FTS.PhiStar.Gegenbauer.gC (2 * m + 1) 0 = 0 := by
        rw [ih]; ring
      simp only [mul_zero, zero_mul] at h
      rw [h3, sub_zero] at h
      have hne : (((2 * m + 1 : ℕ) : ℝ) + 2) ≠ 0 := by positivity
      exact (mul_eq_zero.mp h).resolve_left hne

private theorem eF_zero (m : ℕ) : eF m 0 = 0 := by
  change Work.FTS.PhiStar.Gegenbauer.eFam m 0 = 0
  rw [Work.FTS.PhiStar.Gegenbauer.eFam]
  simp only [Real.cos_zero, Real.sin_zero, one_mul]
  exact gC_odd_zero m

private theorem eF_pi_half (m : ℕ) : eF m (Real.pi / 2) = 0 := by
  change Work.FTS.PhiStar.Gegenbauer.eFam m (Real.pi / 2) = 0
  rw [Work.FTS.PhiStar.Gegenbauer.eFam, Real.cos_pi_div_two, zero_mul]

private theorem continuous_eFam (m : ℕ) : Continuous (eF m) :=
  Real.continuous_cos.mul
    (((Work.FTS.PhiStar.Gegenbauer.contDiff_gC (2 * m + 1)).continuous).comp Real.continuous_sin)

private theorem continuous_deriv_eFam (m : ℕ) : Continuous (deriv (eF m)) := by
  have h : deriv (eF m) = fun θ : ℝ =>
      -Real.sin θ * Work.FTS.PhiStar.Gegenbauer.gC (2 * m + 1) (Real.sin θ)
        + Real.cos θ ^ 2 * deriv (Work.FTS.PhiStar.Gegenbauer.gC (2 * m + 1))
            (Real.sin θ) :=
    Work.FTS.PhiStar.Gegenbauer.deriv_cos_comp_sin _
      (Work.FTS.PhiStar.Gegenbauer.contDiff_gC _)
  rw [h]
  refine ((Real.continuous_sin.neg.mul ?_).add ((Real.continuous_cos.pow 2).mul ?_))
  · exact ((Work.FTS.PhiStar.Gegenbauer.contDiff_gC (2 * m + 1)).continuous).comp
      Real.continuous_sin
  · exact (((Work.FTS.PhiStar.Gegenbauer.contDiff_gC (2 * m + 1)).continuous_deriv
      (by norm_num)).comp Real.continuous_sin)

/-! ## The source `Γ̄` is bounded and continuous on `Iθ` -/

private theorem abs_gamBar_le_Iθ {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) {θ : ℝ} (hθ : θ ∈ Iθ) :
    |gamBar α θ| ≤ 23 / 2 := by
  have h1 : |gamBar α θ| ≤ 1 / Work.Spaces.c α + 5 / 4 :=
    Work.FTS.PhiStar.abs_GamBar_le α θ hα hα1 hθ
  have hc : (1 : ℝ) / 10 ≤ Work.Spaces.c α := (Work.Spaces.c_bounds α hα hα1).1
  have hcpos : 0 < Work.Spaces.c α := by linarith
  have h10 : 1 / Work.Spaces.c α ≤ 10 := by
    rw [div_le_iff₀ hcpos]; linarith
  linarith

private theorem continuousOn_gamBar {α : ℝ} (hα : 0 ≤ α) :
    ContinuousOn (fun θ => gamBar α θ) Iθ := by
  have hbase : ContinuousOn (fun θ : ℝ => (Real.sin θ * Real.cos θ ^ 2) ^ (α / 3)) Iθ :=
    ((Real.continuous_sin.mul (Real.continuous_cos.pow 2)).continuousOn).rpow_const
      (fun θ _ => Or.inr (div_nonneg hα (by norm_num)))
  have h1 : ContinuousOn (fun θ : ℝ => Work.Spaces.Gam α θ) Iθ :=
    hbase.congr (fun θ _ => by simp only [Work.Spaces.Gam])
  have h2 : ContinuousOn (fun θ : ℝ => (5 / 4 : ℝ) * Real.sin (2 * θ)) Iθ := by fun_prop
  refine ((h1.div_const (Work.Spaces.c α)).sub h2).congr (fun θ _ => ?_)
  simp only [gamBar, Work.FTS.VocabO.GamBar, Pi.sub_apply, Pi.div_apply]

/-! ## The Cauchy–Schwarz bound `∫ |e_m| cos ≤ √(cmdD m)` -/

/-- `2XY ≤ X²/A + A·Y²` for `A > 0` (the AM–GM inequality with the optimal parameter). -/
private theorem two_mul_le_div_add (X Y A : ℝ) (hA : 0 < A) :
    2 * X * Y ≤ X ^ 2 / A + A * Y ^ 2 := by
  have h : 0 ≤ (X - A * Y) ^ 2 / A := div_nonneg (sq_nonneg _) (le_of_lt hA)
  have hexpand : (X - A * Y) ^ 2 / A = X ^ 2 / A - 2 * X * Y + A * Y ^ 2 := by
    field_simp
    ring
  linarith [h, hexpand]

private theorem l1_eFam_le_sqrt (m : ℕ) :
    (∫ θ in Iθ, |eF m θ| * Real.cos θ) ≤ Real.sqrt (cmdD m) := by
  set sA : ℝ := Real.sqrt (cmdD m) with hsA
  have hA : 0 < cmdD m := cmdD_pos m
  have hsApos : 0 < sA := by rw [hsA]; exact Real.sqrt_pos_of_pos hA
  have hsA_sq : sA ^ 2 = cmdD m := by rw [hsA]; exact Real.sq_sqrt (le_of_lt hA)
  have hsA_ne : sA ≠ 0 := ne_of_gt hsApos
  -- the pointwise AM–GM bound on `Iθ`
  have hamgm : ∀ θ ∈ Iθ, |eF m θ| * Real.cos θ
      ≤ (1 / (2 * sA)) * (eF m θ ^ 2 * Real.cos θ) + (sA / 2) * Real.cos θ := by
    intro θ hθ
    have hc : 0 ≤ Real.cos θ := cos_nonneg_Iθ θ hθ
    have hs2 : Real.sqrt (Real.cos θ) * Real.sqrt (Real.cos θ) = Real.cos θ := by
      rw [← sq, Real.sq_sqrt hc]
    have hXY := two_mul_le_div_add (X := |eF m θ| * Real.sqrt (Real.cos θ))
      (Y := Real.sqrt (Real.cos θ)) (A := sA) hsApos
    have hX2 : (|eF m θ| * Real.sqrt (Real.cos θ)) ^ 2 = eF m θ ^ 2 * Real.cos θ := by
      rw [mul_pow, sq_abs, Real.sq_sqrt hc]
    have hY2 : (Real.sqrt (Real.cos θ)) ^ 2 = Real.cos θ := Real.sq_sqrt hc
    rw [hX2, hY2] at hXY
    have hL : 2 * (|eF m θ| * Real.sqrt (Real.cos θ)) * Real.sqrt (Real.cos θ)
        = 2 * (|eF m θ| * Real.cos θ) := by
      rw [mul_assoc, mul_assoc, hs2]
    rw [hL] at hXY
    have htarget : (eF m θ ^ 2 * Real.cos θ) / sA + sA * Real.cos θ
        = 2 * ((1 / (2 * sA)) * (eF m θ ^ 2 * Real.cos θ) + (sA / 2) * Real.cos θ) := by
      field_simp
    linarith [hXY, htarget]
  -- integrate
  have hint1 : IntegrableOn (fun θ => |eF m θ| * Real.cos θ) Iθ :=
    integrableOn_Iθ_of_continuousOn
      (((continuous_eFam m).continuousOn.abs).mul Real.continuous_cos.continuousOn)
  have hcont2 : ContinuousOn (fun θ => (1 / (2 * sA)) * (eF m θ ^ 2 * Real.cos θ)
      + (sA / 2) * Real.cos θ) (Set.Icc (0 : ℝ) (Real.pi / 2)) := by
    refine ((continuousOn_const.mul ?_).add (continuousOn_const.mul
      Real.continuous_cos.continuousOn))
    exact ((continuous_eFam m).continuousOn.pow 2).mul Real.continuous_cos.continuousOn
  have hint2 : IntegrableOn (fun θ => (1 / (2 * sA)) * (eF m θ ^ 2 * Real.cos θ)
      + (sA / 2) * Real.cos θ) Iθ := integrableOn_Iθ_of_continuousOn hcont2
  have hmono : (∫ θ in Iθ, |eF m θ| * Real.cos θ)
      ≤ ∫ θ in Iθ, (1 / (2 * sA)) * (eF m θ ^ 2 * Real.cos θ)
          + (sA / 2) * Real.cos θ := by
    refine MeasureTheory.integral_mono_ae hint1 hint2 ?_
    filter_upwards [MeasureTheory.ae_restrict_mem (μ := volume) (s := Iθ) measurableSet_Icc]
      with θ hθ
    exact hamgm θ hθ
  have hval : (∫ θ in Iθ, (1 / (2 * sA)) * (eF m θ ^ 2 * Real.cos θ)
        + (sA / 2) * Real.cos θ)
      = (1 / (2 * sA)) * cmdD m + (sA / 2) * 1 := by
    have hintA : Integrable (fun θ => (1 / (2 * sA)) * (eF m θ ^ 2 * Real.cos θ))
        (volume.restrict Iθ) :=
      (integrableOn_Iθ_of_continuousOn
        (((continuous_eFam m).continuousOn.pow 2).mul
          Real.continuous_cos.continuousOn)).const_mul _
    have hintB : Integrable (fun θ => (sA / 2) * Real.cos θ) (volume.restrict Iθ) :=
      (integrableOn_Iθ_of_continuousOn Real.continuous_cos.continuousOn).const_mul _
    have hadd : (∫ θ in Iθ, (1 / (2 * sA)) * (eF m θ ^ 2 * Real.cos θ)
          + (sA / 2) * Real.cos θ)
        = (∫ θ in Iθ, (1 / (2 * sA)) * (eF m θ ^ 2 * Real.cos θ))
          + (∫ θ in Iθ, (sA / 2) * Real.cos θ) :=
      MeasureTheory.integral_add hintA hintB
    have hAval : (∫ θ in Iθ, (1 / (2 * sA)) * (eF m θ ^ 2 * Real.cos θ))
        = (1 / (2 * sA)) * cmdD m := by
      rw [MeasureTheory.integral_const_mul]
      rfl
    have hBval : (∫ θ in Iθ, (sA / 2) * Real.cos θ) = (sA / 2) * 1 := by
      rw [MeasureTheory.integral_const_mul, integral_cos_Iθ]
    rw [hadd, hAval, hBval]
  -- conclude
  have hfin : (1 / (2 * sA)) * cmdD m + (sA / 2) * 1 = sA := by
    rw [← hsA_sq]
    field_simp
    ring
  linarith [hmono, hval, hfin]

/-! ## The mode coefficients of a solution of `Lzero1 ψ = Γ̄` -/

/-- The primitive of the pairing identity: `P θ = -(ψ θ · e_m'(θ) - ψ'(θ) · e_m(θ)) cos θ`. -/
private def cmdPrim (ψ : ℝ → ℝ) (m : ℕ) : ℝ → ℝ :=
  fun θ => -((ψ θ * deriv (eF m) θ - deriv ψ θ * eF m θ) * Real.cos θ)

/-- The integrand of the pairing identity: `(lam m · ψ - Γ̄) · e_m · cos θ`. -/
private def cmdInt (α : ℝ) (ψ : ℝ → ℝ) (m : ℕ) : ℝ → ℝ :=
  fun θ => (lamF m * ψ θ - gamBar α θ) * eF m θ * Real.cos θ

/-- **The pointwise self-adjointness identity of `Lzero1`.**  The derivative of
`-(u v' - u' v)·cos θ` is `(u · Lzero1 v - Lzero1 u · v)·cos θ`; here we need the instance
`u = ψ`, `v = e_m`, whose derivative is `cmdInt α ψ m` by the eigenvalue relation
`Lzero1 e_m = lam m · e_m` and the model equation `Lzero1 ψ = Γ̄`. -/
private theorem hasDerivAt_cmdPrim {α : ℝ} {ψ : ℝ → ℝ}
    (hψ : Work.FTS.PhiStar.AngModel α ψ) (m : ℕ) {θ : ℝ}
    (hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)) :
    HasDerivAt (cmdPrim ψ m) (cmdInt α ψ m θ) θ := by
  have hI : Set.Ioo (0 : ℝ) (Real.pi / 2) ∈ 𝓝 θ := isOpen_Ioo.mem_nhds hθ
  have hcos : Real.cos θ ≠ 0 := ne_of_gt (Real.cos_pos_of_mem_Ioo
    ⟨by linarith [hθ.1, Real.pi_pos], hθ.2⟩)
  have hψ2 : ContDiffOn ℝ 2 ψ (Set.Ioo 0 (Real.pi / 2)) := hψ.smooth.of_le (by norm_num)
  have he2 : ContDiffOn ℝ 2 (eF m) (Set.Ioo 0 (Real.pi / 2)) := by
    have h : ContDiff ℝ 3 (fun t : ℝ => Real.cos t
        * Work.FTS.PhiStar.Gegenbauer.gC (2 * m + 1) (Real.sin t)) :=
      Real.contDiff_cos.mul
        ((Work.FTS.PhiStar.Gegenbauer.contDiff_gC (2 * m + 1)).comp Real.contDiff_sin)
    exact (h.contDiffOn).of_le (by norm_num)
  have hu1 : HasDerivAt ψ (deriv ψ θ) θ :=
    ((hψ2.contDiffAt hI).differentiableAt (by norm_num)).hasDerivAt
  have hu2 : HasDerivAt (deriv ψ) (deriv (deriv ψ) θ) θ :=
    (((hψ2.deriv_of_isOpen (m := 1) isOpen_Ioo (by norm_num)).contDiffAt hI).differentiableAt
      (by norm_num)).hasDerivAt
  have hv1 : HasDerivAt (eF m) (deriv (eF m) θ) θ :=
    ((he2.contDiffAt hI).differentiableAt (by norm_num)).hasDerivAt
  have hv2 : HasDerivAt (deriv (eF m)) (deriv (deriv (eF m)) θ) θ :=
    (((he2.deriv_of_isOpen (m := 1) isOpen_Ioo (by norm_num)).contDiffAt hI).differentiableAt
      (by norm_num)).hasDerivAt
  have hW : HasDerivAt (fun t : ℝ => deriv ψ t * eF m t - ψ t * deriv (eF m) t)
      (deriv (deriv ψ) θ * eF m θ - ψ θ * deriv (deriv (eF m)) θ) θ := by
    have h := (hu2.mul hv1).sub (hu1.mul hv2)
    convert h using 1
    ring
  have htanψ : deriv (fun t : ℝ => Real.tan t * ψ t) θ
      = (1 / Real.cos θ ^ 2) * ψ θ + Real.tan θ * deriv ψ θ :=
    ((Real.hasDerivAt_tan hcos).mul hu1).deriv
  have htane : deriv (fun t : ℝ => Real.tan t * (eF m) t) θ
      = (1 / Real.cos θ ^ 2) * eF m θ + Real.tan θ * deriv (eF m) θ :=
    ((Real.hasDerivAt_tan hcos).mul hv1).deriv
  have hkey : ψ θ * Work.FTS.EllipticEst.Lzero1 (eF m) θ
        - Work.FTS.EllipticEst.Lzero1 ψ θ * eF m θ
      = (deriv (deriv ψ) θ * eF m θ - ψ θ * deriv (deriv (eF m)) θ)
        - Real.tan θ * (deriv ψ θ * eF m θ - ψ θ * deriv (eF m) θ) := by
    simp only [Work.FTS.EllipticEst.Lzero1]
    rw [htanψ, htane]
    field_simp
    ring
  have hmain : HasDerivAt (fun θ' : ℝ => Real.cos θ'
        * (deriv ψ θ' * eF m θ' - ψ θ' * deriv (eF m) θ'))
      (Real.cos θ * (ψ θ * Work.FTS.EllipticEst.Lzero1 (eF m) θ
        - Work.FTS.EllipticEst.Lzero1 ψ θ * eF m θ)) θ := by
    have h := (Real.hasDerivAt_cos θ).mul hW
    refine h.congr_deriv ?_
    rw [hkey, Real.tan_eq_sin_div_cos]
    field_simp
    ring
  have hfun : cmdPrim ψ m = fun θ' : ℝ => Real.cos θ'
      * (deriv ψ θ' * eF m θ' - ψ θ' * deriv (eF m) θ') := by
    funext θ'
    simp only [cmdPrim]
    ring
  rw [hfun]
  refine hmain.congr_deriv ?_
  have hLzero_eF : Work.FTS.EllipticEst.Lzero1 (eF m) θ = lamF m * eF m θ := by
    rw [Work.FTS.EllipticEst.Lzero1_eq_Lzero]
    exact Work.FTS.PhiStar.Gegenbauer.eFam_Lzero m hcos 0
  rw [hLzero_eF, hψ.eq θ hθ]
  simp only [cmdInt]
  ring

/-- Comparison of a function with an integral bound on its derivative on a closed interval. -/
private theorem abs_sub_le_of_deriv_bound {F f' : ℝ → ℝ} {a b C : ℝ} (hab : a ≤ b) (hC : 0 ≤ C)
    (hderiv : ∀ x ∈ Set.Icc a b, HasDerivAt F (f' x) x)
    (hint : IntervalIntegrable f' volume a b) (hbound : ∀ x ∈ Set.Icc a b, |f' x| ≤ C) :
    |F b - F a| ≤ C * (b - a) := by
  have h1 : (∫ x in a..b, f' x) = F b - F a := by
    refine intervalIntegral.integral_eq_sub_of_hasDerivAt ?_ hint
    rw [Set.uIcc_of_le hab]
    exact hderiv
  rw [← h1]
  calc |∫ x in a..b, f' x| ≤ ∫ x in a..b, |f' x| :=
        intervalIntegral.abs_integral_le_integral_abs hab
    _ ≤ ∫ x in a..b, C :=
        intervalIntegral.integral_mono_on hab hint.abs intervalIntegrable_const
          (fun x hx => hbound x hx)
    _ = C * (b - a) := by rw [intervalIntegral.integral_const, smul_eq_mul, mul_comm]

/-- The first-order form of the angular equation: `W θ = tan θ · ψ θ - ψ' θ` satisfies
`W' = Γ̄ + 6ψ`. -/
private theorem hasDerivAt_tan_psi_sub {α : ℝ} {ψ : ℝ → ℝ}
    (hψ : Work.FTS.PhiStar.AngModel α ψ) {θ : ℝ} (hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)) :
    HasDerivAt (fun t : ℝ => Real.tan t * ψ t - deriv ψ t) (gamBar α θ + 6 * ψ θ) θ := by
  have hI : Set.Ioo (0 : ℝ) (Real.pi / 2) ∈ 𝓝 θ := isOpen_Ioo.mem_nhds hθ
  have hcos : Real.cos θ ≠ 0 := ne_of_gt (Real.cos_pos_of_mem_Ioo
    ⟨by linarith [hθ.1, Real.pi_pos], hθ.2⟩)
  have hψ2 : ContDiffOn ℝ 2 ψ (Set.Ioo 0 (Real.pi / 2)) := hψ.smooth.of_le (by norm_num)
  have h1 : HasDerivAt ψ (deriv ψ θ) θ :=
    ((hψ2.contDiffAt hI).differentiableAt (by norm_num)).hasDerivAt
  have h2 : HasDerivAt (deriv ψ) (deriv (deriv ψ) θ) θ :=
    (((hψ2.deriv_of_isOpen (m := 1) isOpen_Ioo (by norm_num)).contDiffAt hI).differentiableAt
      (by norm_num)).hasDerivAt
  have hode : -deriv (deriv ψ) θ + deriv (fun t : ℝ => Real.tan t * ψ t) θ - 6 * ψ θ
      = gamBar α θ := by
    have h := hψ.eq θ hθ
    simpa only [Work.FTS.EllipticEst.Lzero1] using h
  have htan : deriv (fun t : ℝ => Real.tan t * ψ t) θ
      = (1 / Real.cos θ ^ 2) * ψ θ + Real.tan θ * deriv ψ θ :=
    ((Real.hasDerivAt_tan hcos).mul h1).deriv
  rw [htan] at hode
  have h := ((Real.hasDerivAt_tan hcos).mul h1).sub h2
  refine h.congr_deriv ?_
  linarith [hode]

/-- `W θ = tan θ · ψ θ - ψ' θ` is bounded on `(0, π/2)`: its derivative is `Γ̄ + 6ψ`, which is
bounded by `1/c + 5/4 + 6‖ψ‖_∞`. -/
private theorem exists_tanPsi_sub_deriv_bound {α : ℝ} {ψ : ℝ → ℝ} (hα : 0 < α) (hα1 : α ≤ 1)
    (hψ : Work.FTS.PhiStar.AngModel α ψ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      |Real.tan θ * ψ θ - deriv ψ θ| ≤ C := by
  obtain ⟨M, hMraw⟩ := isCompact_Icc.exists_bound_of_continuousOn hψ.cont
  have hM : ∀ x ∈ Set.Icc (0 : ℝ) (Real.pi / 2), |ψ x| ≤ M := fun x hx => by
    simpa only [Real.norm_eq_abs] using hMraw x hx
  have hΓ : ∀ θ ∈ Set.Icc (0 : ℝ) (Real.pi / 2), |gamBar α θ| ≤ 23 / 2 :=
    fun θ hθ => abs_gamBar_le_Iθ hα hα1 hθ
  have hC0 : (0 : ℝ) ≤ 23 / 2 + 6 * M := by
    have := le_trans (abs_nonneg _) (hM 0 zero_mem_Icc_pi); linarith
  have hW' : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      HasDerivAt (fun t : ℝ => Real.tan t * ψ t - deriv ψ t) (gamBar α θ + 6 * ψ θ) θ :=
    fun θ hθ => hasDerivAt_tan_psi_sub hψ hθ
  have hW'c : ∀ θ ∈ Set.Icc (0 : ℝ) (Real.pi / 2),
      |gamBar α θ + 6 * ψ θ| ≤ 23 / 2 + 6 * M := by
    intro θ hθ
    have h1 : |gamBar α θ| ≤ 23 / 2 := hΓ θ hθ
    have h2 : |ψ θ| ≤ M := hM θ hθ
    calc |gamBar α θ + 6 * ψ θ| ≤ |gamBar α θ| + |6 * ψ θ| := abs_add_le _ _
      _ ≤ 23 / 2 + 6 * M := by
          refine add_le_add h1 ?_
          rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 6)]
          exact mul_le_mul_of_nonneg_left h2 (by norm_num)
  have hπ4 : (Real.pi / 4) ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) :=
    ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩
  have hcontW : ContinuousOn (fun t : ℝ => gamBar α t + 6 * ψ t)
      (Set.Icc (0 : ℝ) (Real.pi / 2)) :=
    (continuousOn_gamBar (le_of_lt hα)).add (hψ.cont.const_mul (6 : ℝ))
  have hint : ∀ a b : ℝ, a ≤ b → a ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) →
      b ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) →
      IntervalIntegrable (fun t : ℝ => gamBar α t + 6 * ψ t) volume a b := by
    intro a b hab ha hb
    refine ContinuousOn.intervalIntegrable ?_
    rw [Set.uIcc_of_le hab]
    exact hcontW.mono (fun x hx => ⟨le_of_lt (lt_of_lt_of_le ha.1 hx.1),
      le_of_lt (lt_of_le_of_lt hx.2 hb.2)⟩)
  have hM0 : 0 ≤ M := le_trans (abs_nonneg _) (hM 0 zero_mem_Icc_pi)
  refine ⟨|Real.tan (Real.pi / 4) * ψ (Real.pi / 4) - deriv ψ (Real.pi / 4)|
    + (23 / 2 + 6 * M) * (Real.pi / 2), by positivity, fun θ hθ => ?_⟩
  have hkey : |(Real.tan θ * ψ θ - deriv ψ θ)
        - (Real.tan (Real.pi / 4) * ψ (Real.pi / 4) - deriv ψ (Real.pi / 4))|
      ≤ (23 / 2 + 6 * M) * (Real.pi / 2) := by
    rcases lt_trichotomy θ (Real.pi / 4) with hlt | heqθ | hgt
    · have hd : ∀ x ∈ Set.Icc θ (Real.pi / 4), HasDerivAt
          (fun t : ℝ => Real.tan t * ψ t - deriv ψ t) (gamBar α x + 6 * ψ x) x :=
        fun x hx => hW' x ⟨lt_of_lt_of_le hθ.1 hx.1, lt_of_le_of_lt hx.2 hπ4.2⟩
      have hb : ∀ x ∈ Set.Icc θ (Real.pi / 4), |gamBar α x + 6 * ψ x| ≤ 23 / 2 + 6 * M :=
        fun x hx => hW'c x ⟨le_trans (le_of_lt hθ.1) hx.1, le_trans hx.2 (le_of_lt hπ4.2)⟩
      have h := abs_sub_le_of_deriv_bound (le_of_lt hlt) hC0 hd
        (hint θ (Real.pi / 4) (le_of_lt hlt) hθ hπ4) hb
      calc |(Real.tan θ * ψ θ - deriv ψ θ)
            - (Real.tan (Real.pi / 4) * ψ (Real.pi / 4) - deriv ψ (Real.pi / 4))|
          = |(Real.tan (Real.pi / 4) * ψ (Real.pi / 4) - deriv ψ (Real.pi / 4))
              - (Real.tan θ * ψ θ - deriv ψ θ)| := abs_sub_comm _ _
        _ ≤ (23 / 2 + 6 * M) * (Real.pi / 4 - θ) := h
        _ ≤ (23 / 2 + 6 * M) * (Real.pi / 2) := by nlinarith [hC0, hθ.1]
    · rw [heqθ, sub_self, abs_zero]
      nlinarith [hC0, Real.pi_pos]
    · have hd : ∀ x ∈ Set.Icc (Real.pi / 4) θ, HasDerivAt
          (fun t : ℝ => Real.tan t * ψ t - deriv ψ t) (gamBar α x + 6 * ψ x) x :=
        fun x hx => hW' x ⟨lt_of_lt_of_le hπ4.1 hx.1, lt_of_le_of_lt hx.2 hθ.2⟩
      have hb : ∀ x ∈ Set.Icc (Real.pi / 4) θ, |gamBar α x + 6 * ψ x| ≤ 23 / 2 + 6 * M :=
        fun x hx => hW'c x ⟨le_trans (le_of_lt hπ4.1) hx.1, le_trans hx.2 (le_of_lt hθ.2)⟩
      have h := abs_sub_le_of_deriv_bound (le_of_lt hgt) hC0 hd
        (hint (Real.pi / 4) θ (le_of_lt hgt) hπ4 hθ) hb
      calc |(Real.tan θ * ψ θ - deriv ψ θ)
            - (Real.tan (Real.pi / 4) * ψ (Real.pi / 4) - deriv ψ (Real.pi / 4))|
          ≤ (23 / 2 + 6 * M) * (θ - Real.pi / 4) := h
        _ ≤ (23 / 2 + 6 * M) * (Real.pi / 2) := by nlinarith [hC0, hθ.2]
  have hdecomp : Real.tan θ * ψ θ - deriv ψ θ
      = ((Real.tan θ * ψ θ - deriv ψ θ)
          - (Real.tan (Real.pi / 4) * ψ (Real.pi / 4) - deriv ψ (Real.pi / 4)))
        + (Real.tan (Real.pi / 4) * ψ (Real.pi / 4) - deriv ψ (Real.pi / 4)) := by ring
  have hmain : |Real.tan θ * ψ θ - deriv ψ θ| ≤ (23 / 2 + 6 * M) * (Real.pi / 2)
      + |Real.tan (Real.pi / 4) * ψ (Real.pi / 4) - deriv ψ (Real.pi / 4)| := by
    rw [hdecomp]
    calc |(Real.tan θ * ψ θ - deriv ψ θ
          - (Real.tan (Real.pi / 4) * ψ (Real.pi / 4) - deriv ψ (Real.pi / 4)))
        + (Real.tan (Real.pi / 4) * ψ (Real.pi / 4) - deriv ψ (Real.pi / 4))|
        ≤ |Real.tan θ * ψ θ - deriv ψ θ
            - (Real.tan (Real.pi / 4) * ψ (Real.pi / 4) - deriv ψ (Real.pi / 4))|
          + |Real.tan (Real.pi / 4) * ψ (Real.pi / 4) - deriv ψ (Real.pi / 4)| :=
          abs_add_le _ _
      _ ≤ (23 / 2 + 6 * M) * (Real.pi / 2)
          + |Real.tan (Real.pi / 4) * ψ (Real.pi / 4) - deriv ψ (Real.pi / 4)| :=
          add_le_add hkey (le_refl _)
  calc |Real.tan θ * ψ θ - deriv ψ θ|
      ≤ (23 / 2 + 6 * M) * (Real.pi / 2)
        + |Real.tan (Real.pi / 4) * ψ (Real.pi / 4) - deriv ψ (Real.pi / 4)| := hmain
    _ = |Real.tan (Real.pi / 4) * ψ (Real.pi / 4) - deriv ψ (Real.pi / 4)|
        + (23 / 2 + 6 * M) * (Real.pi / 2) := by ring
/-- Near `0` the derivative of the angular model is bounded (`ψ' = tan θ · ψ - W` with `W`
bounded and `tan` bounded on `(0,1)`). -/
private theorem exists_deriv_bound_left {α : ℝ} {ψ : ℝ → ℝ} (hα : 0 < α) (hα1 : α ≤ 1)
    (hψ : Work.FTS.PhiStar.AngModel α ψ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ θ ∈ Set.Ioo (0 : ℝ) 1, |deriv ψ θ| ≤ C := by
  obtain ⟨CW, hCW0, hCW⟩ := exists_tanPsi_sub_deriv_bound hα hα1 hψ
  obtain ⟨M, hMraw⟩ := isCompact_Icc.exists_bound_of_continuousOn hψ.cont
  have hM : ∀ x ∈ Set.Icc (0 : ℝ) (Real.pi / 2), |ψ x| ≤ M := fun x hx => by
    simpa only [Real.norm_eq_abs] using hMraw x hx
  have hM0 : 0 ≤ M := le_trans (abs_nonneg _) (hM 0 zero_mem_Icc_pi)
  refine ⟨2 * M + CW, by linarith, fun θ hθ => ?_⟩
  have hθmem : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) := ⟨hθ.1, by linarith [hθ.2, Real.pi_gt_three]⟩
  have hθIcc : θ ∈ Set.Icc (0 : ℝ) (Real.pi / 2) := ⟨le_of_lt hθ.1, le_of_lt hθmem.2⟩
  have hcos1 : (1 / 2 : ℝ) ≤ Real.cos 1 := by
    have h3 := Real.cos_le_cos_of_nonneg_of_le_pi (by norm_num : (0 : ℝ) ≤ 1)
      (by linarith [Real.pi_pos] : Real.pi / 3 ≤ Real.pi)
      (by linarith [Real.pi_gt_three] : (1 : ℝ) ≤ Real.pi / 3)
    rw [Real.cos_pi_div_three] at h3
    linarith
  have hcos : (1 / 2 : ℝ) ≤ Real.cos θ :=
    le_trans hcos1
      (Real.cos_le_cos_of_nonneg_of_le_pi (le_of_lt hθ.1) (by linarith [Real.pi_gt_three])
        (le_of_lt hθ.2))
  have hcpos : 0 < Real.cos θ := by linarith
  have htan : |Real.tan θ| ≤ 2 := by
    rw [Real.tan_eq_sin_div_cos, abs_div, abs_of_pos hcpos, div_le_iff₀ hcpos]
    nlinarith [Real.abs_sin_le_one θ, hcos]
  have hkey : deriv ψ θ = Real.tan θ * ψ θ - (Real.tan θ * ψ θ - deriv ψ θ) := by ring
  rw [hkey]
  calc |Real.tan θ * ψ θ - (Real.tan θ * ψ θ - deriv ψ θ)|
      ≤ |Real.tan θ * ψ θ| + |Real.tan θ * ψ θ - deriv ψ θ| := abs_sub _ _
    _ ≤ 2 * M + CW := by
        refine add_le_add ?_ (hCW θ hθmem)
        rw [abs_mul]
        exact mul_le_mul htan (hM θ hθIcc) (abs_nonneg _) (by norm_num)

/-- `cos²θ · ψ'(θ) → 0` at `π/2⁻`: the first-order form gives
`cos²θ ψ' = cos θ (sin θ · ψ - cos θ · W)` with `W` bounded and `ψ`, `cos` vanishing. -/
private theorem tendsto_cosSq_deriv {α : ℝ} {ψ : ℝ → ℝ} (hα : 0 < α) (hα1 : α ≤ 1)
    (hψ : Work.FTS.PhiStar.AngModel α ψ) :
    Tendsto (fun θ : ℝ => Real.cos θ ^ 2 * deriv ψ θ)
      (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds 0) := by
  obtain ⟨CW, hCW0, hCW⟩ := exists_tanPsi_sub_deriv_bound hα hα1 hψ
  obtain ⟨M, hMraw⟩ := isCompact_Icc.exists_bound_of_continuousOn hψ.cont
  have hM : ∀ x ∈ Set.Icc (0 : ℝ) (Real.pi / 2), |ψ x| ≤ M := fun x hx => by
    simpa only [Real.norm_eq_abs] using hMraw x hx
  have hlepi : nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))
      ≤ nhdsWithin (Real.pi / 2) (Set.Icc (0 : ℝ) (Real.pi / 2)) := by
    rw [nhdsWithin_le_iff, mem_nhdsWithin_iff_exists_mem_nhds_inter]
    exact ⟨Set.Ioi 0, isOpen_Ioi.mem_nhds (by simp only [Set.mem_Ioi]; linarith [Real.pi_pos]),
      fun x hx => ⟨le_of_lt hx.1, le_of_lt hx.2⟩⟩
  have hψlim : Tendsto ψ (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds 0) := by
    have h : Tendsto ψ (nhdsWithin (Real.pi / 2) (Set.Icc (0 : ℝ) (Real.pi / 2)))
        (nhds (ψ (Real.pi / 2))) := hψ.cont.continuousWithinAt pi_half_mem_Icc_pi
    rw [hψ.bdry1] at h
    exact h.mono_left hlepi
  have hcoslim : Tendsto (fun θ : ℝ => Real.cos θ * (M + CW))
      (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds 0) := by
    have h1 : Tendsto Real.cos (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds 0) := by
      have h : Tendsto Real.cos (nhds (Real.pi / 2)) (nhds (Real.cos (Real.pi / 2))) :=
        Real.continuous_cos.continuousAt
      rw [Real.cos_pi_div_two] at h
      exact h.mono_left nhdsWithin_le_nhds
    simpa using h1.mul_const (M + CW)
  have hmem : Set.Ioo (0 : ℝ) (Real.pi / 2)
      ∈ nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2)) := by
    rw [mem_nhdsWithin_iff_exists_mem_nhds_inter]
    exact ⟨Set.Ioi 0, isOpen_Ioi.mem_nhds (by simp only [Set.mem_Ioi]; linarith [Real.pi_pos]),
      fun x hx => ⟨hx.1, hx.2⟩⟩
  refine squeeze_zero_norm' ?_ hcoslim
  filter_upwards [hmem] with θ hθ
  rw [Real.norm_eq_abs]
  have hc : 0 ≤ Real.cos θ := cos_nonneg_Iθ θ ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩
  have hcp : Real.cos θ ≠ 0 := ne_of_gt (Real.cos_pos_of_mem_Ioo
    ⟨by linarith [hθ.1, Real.pi_pos], hθ.2⟩)
  have hZ : Real.cos θ ^ 2 * deriv ψ θ
      = Real.cos θ * (Real.sin θ * ψ θ - Real.cos θ * (Real.tan θ * ψ θ - deriv ψ θ)) := by
    rw [Real.tan_eq_sin_div_cos]
    field_simp
    ring
  rw [hZ, abs_mul, abs_of_nonneg hc]
  have hinner : |Real.sin θ * ψ θ - Real.cos θ * (Real.tan θ * ψ θ - deriv ψ θ)| ≤ M + CW := by
    have hM' : |ψ θ| ≤ M := hM θ ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩
    calc |Real.sin θ * ψ θ - Real.cos θ * (Real.tan θ * ψ θ - deriv ψ θ)|
        ≤ |Real.sin θ * ψ θ| + |Real.cos θ * (Real.tan θ * ψ θ - deriv ψ θ)| := abs_sub _ _
      _ ≤ M + CW := by
          refine add_le_add ?_ ?_
          · calc |Real.sin θ * ψ θ| = |Real.sin θ| * |ψ θ| := by rw [abs_mul]
              _ ≤ 1 * M :=
                mul_le_mul (Real.abs_sin_le_one θ) hM' (abs_nonneg _) (by norm_num)
              _ = M := one_mul M
          · calc |Real.cos θ * (Real.tan θ * ψ θ - deriv ψ θ)|
                = |Real.cos θ| * |Real.tan θ * ψ θ - deriv ψ θ| := by rw [abs_mul]
              _ ≤ 1 * CW :=
                mul_le_mul (Real.abs_cos_le_one θ) (hCW θ hθ) (abs_nonneg _) (by norm_num)
              _ = CW := one_mul CW
  exact mul_le_mul_of_nonneg_left hinner hc

/-- **Left endpoint.**  If `ψ → 0` and `e_m → 0` at `0⁺`, `ψ'` is bounded near `0` and `e_m'` is
bounded on `[0,π/2]`, then the primitive `cmdPrim ψ m` tends to `0` at `0⁺`. -/
private theorem tendsto_cmdPrim_left {ψ : ℝ → ℝ} {m : ℕ} {Cψ' K : ℝ}
    (hCψ'0 : 0 ≤ Cψ') (hK0 : 0 ≤ K)
    (hψ' : ∀ θ ∈ Set.Ioo (0 : ℝ) 1, |deriv ψ θ| ≤ Cψ')
    (hK : ∀ θ ∈ Set.Icc (0 : ℝ) (Real.pi / 2), |deriv (eF m) θ| ≤ K)
    (hψl : Tendsto ψ (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0))
    (heFl : Tendsto (eF m) (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0)) :
    Tendsto (cmdPrim ψ m) (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) := by
  have hmem : Set.Ioo (0 : ℝ) 1 ∈ nhdsWithin (0 : ℝ) (Set.Ioi 0) := by
    rw [mem_nhdsWithin_iff_exists_mem_nhds_inter]
    exact ⟨Set.Iio 1, isOpen_Iio.mem_nhds (by simp only [Set.mem_Iio]; norm_num),
      fun x hx => ⟨hx.2, hx.1⟩⟩
  have hψnorm : Tendsto (fun θ : ℝ => |ψ θ|) (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) := by
    have h := hψl.norm
    simpa only [Real.norm_eq_abs, norm_zero] using h
  have heFnorm : Tendsto (fun θ : ℝ => |eF m θ|) (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) := by
    have h := heFl.norm
    simpa only [Real.norm_eq_abs, norm_zero] using h
  have hhlim : Tendsto (fun θ : ℝ => |ψ θ| * K + Cψ' * |eF m θ|)
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) := by
    have h1 : Tendsto (fun θ : ℝ => |ψ θ| * K) (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) := by
      simpa using hψnorm.mul_const K
    have h2 : Tendsto (fun θ : ℝ => Cψ' * |eF m θ|)
        (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) := by
      simpa using heFnorm.const_mul Cψ'
    simpa using h1.add h2
  refine squeeze_zero_norm' ?_ hhlim
  filter_upwards [hmem] with θ hθ
  rw [Real.norm_eq_abs]
  have hθ' : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) := ⟨hθ.1, by linarith [hθ.2, Real.pi_gt_three]⟩
  have hd : |deriv (eF m) θ| ≤ K := hK θ ⟨le_of_lt hθ.1, le_of_lt hθ'.2⟩
  have hdψ : |deriv ψ θ| ≤ Cψ' := hψ' θ hθ
  have hc : |Real.cos θ| ≤ 1 := Real.abs_cos_le_one θ
  have h1 : |ψ θ * deriv (eF m) θ * Real.cos θ| ≤ |ψ θ| * K := by
    have hstep : |ψ θ| * |deriv (eF m) θ| ≤ |ψ θ| * K :=
      mul_le_mul_of_nonneg_left hd (abs_nonneg _)
    calc |ψ θ * deriv (eF m) θ * Real.cos θ|
        = |ψ θ| * |deriv (eF m) θ| * |Real.cos θ| := by rw [abs_mul, abs_mul]
      _ ≤ |ψ θ| * K * |Real.cos θ| := mul_le_mul_of_nonneg_right hstep (abs_nonneg _)
      _ ≤ |ψ θ| * K * 1 := mul_le_mul_of_nonneg_left hc (mul_nonneg (abs_nonneg _) hK0)
      _ = |ψ θ| * K := by ring
  have h2 : |deriv ψ θ * eF m θ * Real.cos θ| ≤ Cψ' * |eF m θ| := by
    have hstep : |deriv ψ θ| * |eF m θ| ≤ Cψ' * |eF m θ| :=
      mul_le_mul_of_nonneg_right hdψ (abs_nonneg _)
    calc |deriv ψ θ * eF m θ * Real.cos θ|
        = |deriv ψ θ| * |eF m θ| * |Real.cos θ| := by rw [abs_mul, abs_mul]
      _ ≤ Cψ' * |eF m θ| * |Real.cos θ| := mul_le_mul_of_nonneg_right hstep (abs_nonneg _)
      _ ≤ Cψ' * |eF m θ| * 1 :=
          mul_le_mul_of_nonneg_left hc (mul_nonneg hCψ'0 (abs_nonneg _))
      _ = Cψ' * |eF m θ| := by ring
  have hsplit : |cmdPrim ψ m θ|
      = |ψ θ * deriv (eF m) θ * Real.cos θ - deriv ψ θ * eF m θ * Real.cos θ| := by
    rw [cmdPrim, abs_neg]
    congr 1
    ring
  rw [hsplit]
  calc |ψ θ * deriv (eF m) θ * Real.cos θ - deriv ψ θ * eF m θ * Real.cos θ|
      ≤ |ψ θ * deriv (eF m) θ * Real.cos θ| + |deriv ψ θ * eF m θ * Real.cos θ| :=
        abs_sub _ _
    _ ≤ |ψ θ| * K + Cψ' * |eF m θ| := add_le_add h1 h2

/-- **Right endpoint.**  If `ψ → 0` and `cos²θ ψ'(θ) → 0` at `π/2⁻` and `e_m'` is bounded on
`[0,π/2]`, then `cmdPrim ψ m → 0` at `π/2⁻`. -/
private theorem tendsto_cmdPrim_right {ψ : ℝ → ℝ} {m : ℕ} {K : ℝ} (hK0 : 0 ≤ K)
    (hK : ∀ θ ∈ Set.Icc (0 : ℝ) (Real.pi / 2), |deriv (eF m) θ| ≤ K)
    (hψl : Tendsto ψ (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds 0))
    (hcos : Tendsto (fun θ : ℝ => Real.cos θ ^ 2 * deriv ψ θ)
      (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds 0)) :
    Tendsto (cmdPrim ψ m) (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds 0) := by
  obtain ⟨K', hK'raw⟩ := isCompact_Icc.exists_bound_of_continuousOn
    ((Work.FTS.PhiStar.Gegenbauer.contDiff_gC (2 * m + 1)).continuous.continuousOn)
  have hK' : ∀ x ∈ Set.Icc (-1 : ℝ) 1,
      |Work.FTS.PhiStar.Gegenbauer.gC (2 * m + 1) x| ≤ K' := fun x hx => by
    simpa only [Real.norm_eq_abs] using hK'raw x hx
  have hK'0 : 0 ≤ K' := le_trans (abs_nonneg _) (hK' 0 ⟨by norm_num, by norm_num⟩)
  have hψnorm : Tendsto (fun θ : ℝ => |ψ θ|)
      (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds 0) := by
    have h := hψl.norm
    simpa only [Real.norm_eq_abs, norm_zero] using h
  have hcosnorm : Tendsto (fun θ : ℝ => |Real.cos θ ^ 2 * deriv ψ θ|)
      (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds 0) := by
    have h := hcos.norm
    simpa only [Real.norm_eq_abs, norm_zero] using h
  have hhlim : Tendsto (fun θ : ℝ => |ψ θ| * K + K' * |Real.cos θ ^ 2 * deriv ψ θ|)
      (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds 0) := by
    have h1 : Tendsto (fun θ : ℝ => |ψ θ| * K)
        (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds 0) := by
      simpa using hψnorm.mul_const K
    have h2 : Tendsto (fun θ : ℝ => K' * |Real.cos θ ^ 2 * deriv ψ θ|)
        (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds 0) := by
      simpa using hcosnorm.const_mul K'
    simpa using h1.add h2
  have hmem : Set.Ioo (0 : ℝ) (Real.pi / 2)
      ∈ nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2)) := by
    rw [mem_nhdsWithin_iff_exists_mem_nhds_inter]
    exact ⟨Set.Ioi 0, isOpen_Ioi.mem_nhds (by simp only [Set.mem_Ioi]; linarith [Real.pi_pos]),
      fun x hx => ⟨hx.1, hx.2⟩⟩
  refine squeeze_zero_norm' ?_ hhlim
  filter_upwards [hmem] with θ hθ
  rw [Real.norm_eq_abs]
  have hd : |deriv (eF m) θ| ≤ K := hK θ ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩
  have hc : |Real.cos θ| ≤ 1 := Real.abs_cos_le_one θ
  have hq : |Work.FTS.PhiStar.Gegenbauer.gC (2 * m + 1) (Real.sin θ)| ≤ K' :=
    hK' _ ⟨Real.neg_one_le_sin θ, Real.sin_le_one θ⟩
  have h1 : |ψ θ * deriv (eF m) θ * Real.cos θ| ≤ |ψ θ| * K := by
    have hstep : |ψ θ| * |deriv (eF m) θ| ≤ |ψ θ| * K :=
      mul_le_mul_of_nonneg_left hd (abs_nonneg _)
    calc |ψ θ * deriv (eF m) θ * Real.cos θ|
        = |ψ θ| * |deriv (eF m) θ| * |Real.cos θ| := by rw [abs_mul, abs_mul]
      _ ≤ |ψ θ| * K * |Real.cos θ| := mul_le_mul_of_nonneg_right hstep (abs_nonneg _)
      _ ≤ |ψ θ| * K * 1 := mul_le_mul_of_nonneg_left hc (mul_nonneg (abs_nonneg _) hK0)
      _ = |ψ θ| * K := by ring
  have h2 : |deriv ψ θ * eF m θ * Real.cos θ| ≤ K' * |Real.cos θ ^ 2 * deriv ψ θ| := by
    have heF : eF m θ = Real.cos θ
        * Work.FTS.PhiStar.Gegenbauer.gC (2 * m + 1) (Real.sin θ) := rfl
    have hrewrite : deriv ψ θ * eF m θ * Real.cos θ
        = (Real.cos θ ^ 2 * deriv ψ θ)
          * Work.FTS.PhiStar.Gegenbauer.gC (2 * m + 1) (Real.sin θ) := by
      rw [heF]; ring
    rw [hrewrite, abs_mul]
    calc |Real.cos θ ^ 2 * deriv ψ θ|
          * |Work.FTS.PhiStar.Gegenbauer.gC (2 * m + 1) (Real.sin θ)|
        ≤ |Real.cos θ ^ 2 * deriv ψ θ| * K' := mul_le_mul_of_nonneg_left hq (abs_nonneg _)
      _ = K' * |Real.cos θ ^ 2 * deriv ψ θ| := by ring
  have hsplit : |cmdPrim ψ m θ|
      = |ψ θ * deriv (eF m) θ * Real.cos θ - deriv ψ θ * eF m θ * Real.cos θ| := by
    rw [cmdPrim, abs_neg]
    congr 1
    ring
  rw [hsplit]
  calc |ψ θ * deriv (eF m) θ * Real.cos θ - deriv ψ θ * eF m θ * Real.cos θ|
      ≤ |ψ θ * deriv (eF m) θ * Real.cos θ| + |deriv ψ θ * eF m θ * Real.cos θ| :=
        abs_sub _ _
    _ ≤ |ψ θ| * K + K' * |Real.cos θ ^ 2 * deriv ψ θ| := add_le_add h1 h2

/-- **The eigenrelation.**  For an angular model `ψ` (`Lzero1 ψ = Γ̄`) the `m`-th mode
coefficient of `Lzero1 ψ` is `lam m` times that of `ψ` — the self-adjointness of `Lzero1` in
the weight `cos θ dθ`. -/
private theorem pairing_core {α : ℝ} {ψ : ℝ → ℝ} {Cψ' : ℝ} (hα : 0 < α) (hα1 : α ≤ 1)
    (hψ : Work.FTS.PhiStar.AngModel α ψ) (hCψ'0 : 0 ≤ Cψ')
    (hCψ' : ∀ θ ∈ Set.Ioo (0 : ℝ) 1, |deriv ψ θ| ≤ Cψ') (m : ℕ) :
    (∫ θ in Iθ, gamBar α θ * eF m θ * Real.cos θ)
      = lamF m * (∫ θ in Iθ, ψ θ * eF m θ * Real.cos θ) := by
  -- smoothness inputs for the integration by parts
  have hψ2 : ContDiffOn ℝ 2 ψ (Set.Ioo 0 (Real.pi / 2)) := hψ.smooth.of_le (by norm_num)
  have heF2 : ContDiffOn ℝ 2 (eF m) (Set.Ioo (0 : ℝ) (Real.pi / 2)) := by
    have h : ContDiff ℝ 3 (fun θ : ℝ => Real.cos θ
        * Work.FTS.PhiStar.Gegenbauer.gC (2 * m + 1) (Real.sin θ)) :=
      Real.contDiff_cos.mul
        ((Work.FTS.PhiStar.Gegenbauer.contDiff_gC (2 * m + 1)).comp Real.contDiff_sin)
    exact (h.contDiffOn).of_le (by norm_num)
  -- the mode solves the eigenvalue equation
  have hLzero_eF : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      Work.FTS.EllipticEst.Lzero1 (eF m) θ = lamF m * eF m θ := by
    intro θ hθ
    have hcos : Real.cos θ ≠ 0 := ne_of_gt (Real.cos_pos_of_mem_Ioo
      ⟨by linarith [hθ.1, Real.pi_pos], hθ.2⟩)
    rw [Work.FTS.EllipticEst.Lzero1_eq_Lzero]
    exact Work.FTS.PhiStar.Gegenbauer.eFam_Lzero m hcos 0
  -- the derivative identity
  have hderiv : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      HasDerivAt (cmdPrim ψ m) (cmdInt α ψ m θ) θ :=
    fun θ hθ => hasDerivAt_cmdPrim hψ m hθ
  -- integrability of the integrand
  have hcont_g : ContinuousOn (cmdInt α ψ m) Iθ := by
    have hGB : ContinuousOn (fun θ => gamBar α θ) Iθ := continuousOn_gamBar (le_of_lt hα)
    have h : ContinuousOn (fun θ => (lamF m * ψ θ - gamBar α θ) * eF m θ * Real.cos θ) Iθ :=
      (((continuousOn_const.mul hψ.cont).sub hGB).mul (continuous_eFam m).continuousOn).mul
        Real.continuous_cos.continuousOn
    exact h
  have hint : IntervalIntegrable (cmdInt α ψ m) volume (0 : ℝ) (Real.pi / 2) := by
    refine ContinuousOn.intervalIntegrable ?_
    rw [Set.uIcc_of_le (by positivity : (0 : ℝ) ≤ Real.pi / 2)]
    exact hcont_g
  -- bounds for the endpoint squeeze
  obtain ⟨Kb, hKbraw⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (continuous_deriv_eFam m).continuousOn
  have hKb : ∀ θ ∈ Set.Icc (0 : ℝ) (Real.pi / 2), |deriv (eF m) θ| ≤ Kb := fun θ hθ => by
    simpa only [Real.norm_eq_abs] using hKbraw θ hθ
  have hKb0 : 0 ≤ Kb := le_trans (abs_nonneg _) (hKb 0 zero_mem_Icc_pi)
  -- the one-sided filters sit above the closed-interval filter
  have hle0 : nhdsWithin (0 : ℝ) (Set.Ioi 0)
      ≤ nhdsWithin (0 : ℝ) (Set.Icc (0 : ℝ) (Real.pi / 2)) := by
    rw [nhdsWithin_le_iff, mem_nhdsWithin_iff_exists_mem_nhds_inter]
    exact ⟨Set.Iio (Real.pi / 2), isOpen_Iio.mem_nhds (by simp only [Set.mem_Iio]; linarith [Real.pi_pos]),
      fun x hx => ⟨le_of_lt hx.2, le_of_lt hx.1⟩⟩
  have hlepi : nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))
      ≤ nhdsWithin (Real.pi / 2) (Set.Icc (0 : ℝ) (Real.pi / 2)) := by
    rw [nhdsWithin_le_iff, mem_nhdsWithin_iff_exists_mem_nhds_inter]
    exact ⟨Set.Ioi 0, isOpen_Ioi.mem_nhds (by simp only [Set.mem_Ioi]; linarith [Real.pi_pos]),
      fun x hx => ⟨le_of_lt hx.1, le_of_lt hx.2⟩⟩
  -- the limiting values of `ψ` and `e_m` at the endpoints
  have hψlim0 : Tendsto ψ (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) := by
    have h : Tendsto ψ (nhdsWithin (0 : ℝ) (Set.Icc (0 : ℝ) (Real.pi / 2))) (nhds (ψ 0)) :=
      hψ.cont.continuousWithinAt zero_mem_Icc_pi
    rw [hψ.bdry0] at h
    exact h.mono_left hle0
  have hψlimpi : Tendsto ψ (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds 0) := by
    have h : Tendsto ψ (nhdsWithin (Real.pi / 2) (Set.Icc (0 : ℝ) (Real.pi / 2)))
        (nhds (ψ (Real.pi / 2))) := hψ.cont.continuousWithinAt pi_half_mem_Icc_pi
    rw [hψ.bdry1] at h
    exact h.mono_left hlepi
  have heFlim0 : Tendsto (eF m) (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) := by
    have h : Tendsto (eF m) (nhds 0) (nhds (eF m 0)) := (continuous_eFam m).continuousAt
    rw [eF_zero m] at h
    exact h.mono_left nhdsWithin_le_nhds
  have heFlimpi : Tendsto (eF m) (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds 0) := by
    have h : Tendsto (eF m) (nhds (Real.pi / 2)) (nhds (eF m (Real.pi / 2))) :=
      (continuous_eFam m).continuousAt
    rw [eF_pi_half m] at h
    exact h.mono_left nhdsWithin_le_nhds
  have hcos2 : Tendsto (fun θ : ℝ => Real.cos θ ^ 2 * deriv ψ θ)
      (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds 0) :=
    tendsto_cosSq_deriv hα hα1 hψ
  have hP0 : Tendsto (cmdPrim ψ m) (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) :=
    tendsto_cmdPrim_left hCψ'0 hKb0 hCψ' hKb hψlim0 heFlim0
  have hPpi : Tendsto (cmdPrim ψ m) (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds 0) :=
    tendsto_cmdPrim_right hKb0 hKb hψlimpi hcos2
  -- the fundamental theorem of calculus
  have hFTC : (∫ θ in (0 : ℝ)..(Real.pi / 2), cmdInt α ψ m θ) = 0 := by
    have hmain := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_tendsto
      (by linarith [Real.pi_pos] : (0 : ℝ) < Real.pi / 2) hderiv hint hP0 hPpi
    simpa using hmain
  -- split the integral into the two pieces and conclude
  have hpt : ∀ θ : ℝ, cmdInt α ψ m θ
      = lamF m * (ψ θ * eF m θ * Real.cos θ) - gamBar α θ * eF m θ * Real.cos θ := by
    intro θ; simp only [cmdInt]; ring
  have hint1 : IntervalIntegrable (fun θ : ℝ => lamF m * (ψ θ * eF m θ * Real.cos θ))
      volume (0 : ℝ) (Real.pi / 2) := by
    refine ContinuousOn.intervalIntegrable ?_
    rw [Set.uIcc_of_le (by positivity : (0 : ℝ) ≤ Real.pi / 2)]
    exact continuousOn_const.mul ((hψ.cont.mul (continuous_eFam m).continuousOn).mul
      Real.continuous_cos.continuousOn)
  have hint2 : IntervalIntegrable (fun θ : ℝ => gamBar α θ * eF m θ * Real.cos θ)
      volume (0 : ℝ) (Real.pi / 2) := by
    refine ContinuousOn.intervalIntegrable ?_
    rw [Set.uIcc_of_le (by positivity : (0 : ℝ) ≤ Real.pi / 2)]
    exact ((continuousOn_gamBar (le_of_lt hα)).mul (continuous_eFam m).continuousOn).mul
      Real.continuous_cos.continuousOn
  have hAB : (∫ θ in (0 : ℝ)..(Real.pi / 2), (lamF m * (ψ θ * eF m θ * Real.cos θ)
        - gamBar α θ * eF m θ * Real.cos θ))
      = (∫ θ in (0 : ℝ)..(Real.pi / 2), lamF m * (ψ θ * eF m θ * Real.cos θ))
        - ∫ θ in (0 : ℝ)..(Real.pi / 2), gamBar α θ * eF m θ * Real.cos θ :=
    intervalIntegral.integral_sub hint1 hint2
  have hgval : (∫ θ in (0 : ℝ)..(Real.pi / 2), lamF m * (ψ θ * eF m θ * Real.cos θ))
      = lamF m * (∫ θ in (0 : ℝ)..(Real.pi / 2), ψ θ * eF m θ * Real.cos θ) :=
    intervalIntegral.integral_const_mul _ _
  have hsplit : (∫ θ in (0 : ℝ)..(Real.pi / 2), cmdInt α ψ m θ)
      = lamF m * (∫ θ in (0 : ℝ)..(Real.pi / 2), ψ θ * eF m θ * Real.cos θ)
        - ∫ θ in (0 : ℝ)..(Real.pi / 2), gamBar α θ * eF m θ * Real.cos θ := by
    rw [show (∫ θ in (0 : ℝ)..(Real.pi / 2), cmdInt α ψ m θ)
        = ∫ θ in (0 : ℝ)..(Real.pi / 2), (lamF m * (ψ θ * eF m θ * Real.cos θ)
            - gamBar α θ * eF m θ * Real.cos θ) from
      intervalIntegral.integral_congr (fun θ _ => hpt θ), hAB, hgval]
  have hconv1 : (∫ θ in (0 : ℝ)..(Real.pi / 2), ψ θ * eF m θ * Real.cos θ)
      = ∫ θ in Iθ, ψ θ * eF m θ * Real.cos θ :=
    (setIntegral_Iθ_eq_intervalIntegral' _).symm
  have hconv2 : (∫ θ in (0 : ℝ)..(Real.pi / 2), gamBar α θ * eF m θ * Real.cos θ)
      = ∫ θ in Iθ, gamBar α θ * eF m θ * Real.cos θ :=
    (setIntegral_Iθ_eq_intervalIntegral' _).symm
  rw [hconv1, hconv2] at hsplit
  linarith [hsplit, hFTC]

/-! ## The decay of the mode coefficients -/

theorem CmodeDecay : ∃ C : ℝ, 0 < C ∧ ∀ (α : ℝ) (ψ : ℝ → ℝ), 0 < α → α ≤ 1 / 5 → Work.FTS.PhiStar.AngModel α ψ → ∀ m : ℕ, 1 ≤ m → |Work.FTS.PhiStar.Series.cmode m (fun _ θ => ψ θ) 0| ≤ C / (Work.FTS.PhiStar.Gegenbauer.lam m * Real.sqrt (2 * (m : ℝ) + 1)) := by
  refine ⟨23, by norm_num, ?_⟩
  intro α ψ hα hα5 hψ m hm
  have hα1 : α ≤ 1 := by linarith
  -- the bound on `ψ'` near `0` and the eigenrelation
  obtain ⟨Cψ', hCψ'0, hCψ'⟩ := exists_deriv_bound_left hα hα1 hψ
  have hpair := pairing_core hα hα1 hψ hCψ'0 hCψ' m
  -- the mode moment
  have hcm := cmode_mul_cmdD m (fun _ θ => ψ θ) 0
  -- express the coefficient in terms of the moments
  have hm1 : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have hlam_pos : 0 < lamF m := by
    simp only [Work.FTS.PhiStar.Gegenbauer.lam]
    positivity
  have hlam : lamF m ≠ 0 := ne_of_gt hlam_pos
  have hA : 0 < cmdD m := cmdD_pos m
  have hDne : cmdD m ≠ 0 := ne_of_gt hA
  have hc_eq : cmode m (fun _ θ => ψ θ) 0
      = (∫ θ in Iθ, gamBar α θ * eF m θ * Real.cos θ) / (lamF m * cmdD m) := by
    have hkey : cmode m (fun _ θ => ψ θ) 0 * (lamF m * cmdD m)
        = ∫ θ in Iθ, gamBar α θ * eF m θ * Real.cos θ := by
      calc cmode m (fun _ θ => ψ θ) 0 * (lamF m * cmdD m)
          = lamF m * (cmode m (fun _ θ => ψ θ) 0 * cmdD m) := by ring
        _ = lamF m * (∫ θ in Iθ, ψ θ * eF m θ * Real.cos θ) := by rw [hcm]
        _ = ∫ θ in Iθ, gamBar α θ * eF m θ * Real.cos θ := hpair.symm
    rw [← hkey, mul_div_cancel_right₀ _ (mul_ne_zero hlam hDne)]
  -- the numerator is bounded by Cauchy–Schwarz
  have hnum : |∫ θ in Iθ, gamBar α θ * eF m θ * Real.cos θ|
      ≤ (23 / 2) * Real.sqrt (cmdD m) := by
    have h1 : |∫ θ in Iθ, gamBar α θ * eF m θ * Real.cos θ|
        ≤ ∫ θ in Iθ, |gamBar α θ * eF m θ * Real.cos θ| := by
      simpa only [Real.norm_eq_abs] using (norm_integral_le_integral_norm
        (μ := volume.restrict Iθ)
        (f := fun θ : ℝ => gamBar α θ * eF m θ * Real.cos θ))
    have h2 : (∫ θ in Iθ, |gamBar α θ * eF m θ * Real.cos θ|)
        ≤ (23 / 2) * (∫ θ in Iθ, |eF m θ| * Real.cos θ) := by
      rw [← MeasureTheory.integral_const_mul]
      have hint1 : IntegrableOn (fun θ => |gamBar α θ * eF m θ * Real.cos θ|) Iθ :=
        integrableOn_Iθ_of_continuousOn (((continuousOn_gamBar (le_of_lt hα)).mul
          (continuous_eFam m).continuousOn).mul Real.continuous_cos.continuousOn).abs
      have hint2 : IntegrableOn (fun θ => (23 / 2) * (|eF m θ| * Real.cos θ)) Iθ :=
        (integrableOn_Iθ_of_continuousOn (((continuous_eFam m).continuousOn.abs).mul
          Real.continuous_cos.continuousOn)).const_mul _
      refine MeasureTheory.integral_mono_ae hint1 hint2 ?_
      filter_upwards [MeasureTheory.ae_restrict_mem (μ := volume) (s := Iθ) measurableSet_Icc]
        with θ hθ
      have hc : 0 ≤ Real.cos θ := cos_nonneg_Iθ θ hθ
      have hgb : |gamBar α θ| ≤ 23 / 2 := abs_gamBar_le_Iθ hα hα1 hθ
      rw [abs_mul, abs_mul, abs_of_nonneg hc]
      calc |gamBar α θ| * |eF m θ| * Real.cos θ
          ≤ (23 / 2) * |eF m θ| * Real.cos θ := by
            refine mul_le_mul_of_nonneg_right ?_ hc
            exact mul_le_mul_of_nonneg_right hgb (abs_nonneg _)
        _ = (23 / 2) * (|eF m θ| * Real.cos θ) := by ring
    have h3 : (23 / 2) * (∫ θ in Iθ, |eF m θ| * Real.cos θ)
        ≤ (23 / 2) * Real.sqrt (cmdD m) :=
      mul_le_mul_of_nonneg_left (l1_eFam_le_sqrt m) (by norm_num)
    linarith
  -- the final arithmetic
  have habs : |cmode m (fun _ θ => ψ θ) 0|
      ≤ (23 / 2) * Real.sqrt (cmdD m) / (lamF m * cmdD m) := by
    rw [hc_eq, abs_div, abs_of_pos (mul_pos hlam_pos hA)]
    exact div_le_div_of_nonneg_right hnum (le_of_lt (mul_pos hlam_pos hA))
  have hfin : (23 / 2) * Real.sqrt (cmdD m) / (lamF m * cmdD m)
      ≤ 23 / (lamF m * Real.sqrt (2 * (m : ℝ) + 1)) := by
    have hsA : 0 < Real.sqrt (cmdD m) := Real.sqrt_pos_of_pos hA
    have hsA_ne : Real.sqrt (cmdD m) ≠ 0 := ne_of_gt hsA
    have hsq : Real.sqrt (cmdD m) * Real.sqrt (cmdD m) = cmdD m := by
      rw [← sq, Real.sq_sqrt (le_of_lt hA)]
    have hs2m : (0 : ℝ) < 2 * (m : ℝ) + 1 := by linarith
    have hs2 : Real.sqrt (2 * (m : ℝ) + 1) ≤ 2 * Real.sqrt (cmdD m) := by
      rw [← Real.sqrt_sq (by positivity : (0 : ℝ) ≤ 2 * Real.sqrt (cmdD m))]
      refine Real.sqrt_le_sqrt ?_
      rw [mul_pow, Real.sq_sqrt (le_of_lt hA)]
      have := cmdD_ge m hm
      linarith
    have hkey : (23 / 2) * Real.sqrt (cmdD m) / (lamF m * cmdD m)
        = (23 / 2) / (lamF m * Real.sqrt (cmdD m)) := by
      rw [div_eq_div_iff (mul_ne_zero hlam hDne) (mul_ne_zero hlam hsA_ne)]
      nlinarith [hsq]
    rw [hkey, div_le_div_iff₀ (mul_pos hlam_pos hsA)
      (mul_pos hlam_pos (Real.sqrt_pos_of_pos hs2m))]
    nlinarith [hs2, hlam_pos, Real.sqrt_nonneg (cmdD m), Real.sqrt_nonneg (2 * (m : ℝ) + 1)]
  exact habs.trans hfin

end Work.FTS.PhiStar.Series
