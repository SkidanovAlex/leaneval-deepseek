import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS_RegExport.RXT.Slots.v2_hkMem_pointwise_min
import Submission.Work.FTS.StrongEps.Jker_integral_eq_one
import Submission.Work.FTS.StrongEps.Kernel
import Submission.Work.FTS.OpenPkg.l12zero_field
import Submission.Work.FTS.StrongEps.HkSq_Jeps_le
import Submission.Work.FTS.StrongEps.HkMem_Jeps
import Submission.Work.FTS.StrongEps.JepsSmoothOpen
import Submission.Work.FTS.StrongEps.PZeroAux.pzNorm_pos
import Submission.Work.FTS.StrongEps.PZero
import Submission.Work.FTS.StrongEps.EpsSqTools.BumpEpsSqBound

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.E5G

open Work.FTS.Galerkin (Fn Fam slice)

open scoped Real Topology
open MeasureTheory Set Filter

set_option maxHeartbeats 1000000

/-- **A pointwise bound for the projected, mollified profile** in terms of the honest `ℋ⁴`-norm of
its argument, uniformly in the mollification scale `ε ∈ (0,1]`: the mollified profile is an average
of the shifted values (bounded by the `ℋ⁴ → L^∞` trade-off `v2_hkMem_pointwise_min`, which needs no
trace hypothesis) weighted by the mass-one kernel `Jker ρ ε`, and the `P₀`-correction is controlled
by the zero-mode bound `l12zero_field`. -/
theorem PzJeps_abs_le_unif {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) {ρ : ℝ × ℝ → ℝ}
    (hρ : Work.FTS.StrongEps.IsSmoothKernel ρ) :
    ∃ C : ℝ, 0 < C ∧ ∀ ε ∈ Set.Ioc (0 : ℝ) 1, ∀ Z : Fn,
      Work.FTS.EllipticEst.SmoothOpen Z → Work.Spaces.HkMem α 4 Z →
        ∀ z θ : ℝ, 0 < z → θ ∈ Set.Ioo 0 (π / 2) →
          |Work.FTS.StrongEps.Pz (Work.FTS.StrongEps.Jeps ρ ε Z) z θ|
            ≤ C * Work.Spaces.HkNorm α 4 Z := by
  obtain ⟨Cv2, hCv2nn, hv2⟩ := Work.FTS_RegExport.RXT.v2_hkMem_pointwise_min hα hα1
  obtain ⟨CJ, hCJpos, hCJ⟩ := Work.FTS.StrongEps.HkSq_Jeps_le ρ hρ.moll
  obtain ⟨C1, hC1pos, hC1⟩ := Work.FTS.OpenPkg.l12zero_field
  have hpzpos : 0 < Work.FTS.StrongEps.pzNorm := Work.FTS.StrongEps.PZeroAux.pzNorm_pos
  refine ⟨Cv2 + C1 * Real.exp (CJ / 2) / Work.FTS.StrongEps.pzNorm, by positivity, ?_⟩
  intro ε hε Z hsm hmem z θ hz hθ
  have hN0 : 0 ≤ Work.Spaces.HkNorm α 4 Z := Work.Spaces.HkNorm_nonneg α 4 Z
  have hquad : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry Z) Work.FTS.StrongEps.Quad :=
    (Work.FTS.EllipticEst.smoothOpen_iff_forall Z).mp hsm
  -- ## the pointwise bound of the shifted integrand
  have hstep : ∀ x : ℝ, Cv2 * min x 1 * Work.Spaces.HkNorm α 4 Z
      ≤ Cv2 * Work.Spaces.HkNorm α 4 Z := by
    intro x
    calc Cv2 * min x 1 * Work.Spaces.HkNorm α 4 Z
        = (Cv2 * min x 1) * Work.Spaces.HkNorm α 4 Z := rfl
      _ ≤ (Cv2 * 1) * Work.Spaces.HkNorm α 4 Z :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left (min_le_right x 1) hCv2nn) hN0
      _ = Cv2 * Work.Spaces.HkNorm α 4 Z := by ring
  have hpw : ∀ p : ℝ × ℝ,
      |Z (Work.FTS.StrongEps.zShift z p.1) (Work.FTS.StrongEps.thShift θ p.2)|
        ≤ Cv2 * Work.Spaces.HkNorm α 4 Z := by
    intro p
    have hθ' := Work.FTS.StrongEps.thShift_mem (p := p.2) hθ
    have h := hv2 Z (hquad 4) hmem 0 0 (by norm_num)
      (Work.FTS.StrongEps.zShift z p.1) (Work.FTS.StrongEps.thShift θ p.2)
      (Work.FTS.StrongEps.zShift_pos (p := p.1) hz) hθ'.1 hθ'.2
    simp only [Work.Spaces.mixed_zero_right] at h
    exact le_trans h (hstep (Work.FTS.StrongEps.zShift z p.1))
  -- ## the mollifier part
  have hJnn : ∀ p : ℝ × ℝ, 0 ≤ Work.FTS.StrongEps.Jker ρ ε p := by
    intro p
    simp only [Work.FTS.StrongEps.Jker]
    exact mul_nonneg (by positivity) (hρ.moll.nonneg _)
  have hJbound : |Work.FTS.StrongEps.Jeps ρ ε Z z θ| ≤ Cv2 * Work.Spaces.HkNorm α 4 Z := by
    rw [Work.FTS.StrongEps.Jeps_eq_integral ρ ε Z hz hθ]
    have hJint : Integrable (Work.FTS.StrongEps.Jker ρ ε) :=
      Work.FTS.StrongEps.Jker_integrable hρ.moll hε.1
    have hJmass : ∫ p : ℝ × ℝ, Work.FTS.StrongEps.Jker ρ ε p = 1 :=
      Work.FTS.StrongEps.Jker_integral_eq_one ρ hρ.moll hε.1
    have h1 : |∫ p : ℝ × ℝ, Work.FTS.StrongEps.Jker ρ ε p *
        Z (Work.FTS.StrongEps.zShift z p.1) (Work.FTS.StrongEps.thShift θ p.2)|
        ≤ ∫ p : ℝ × ℝ, |Work.FTS.StrongEps.Jker ρ ε p *
            Z (Work.FTS.StrongEps.zShift z p.1) (Work.FTS.StrongEps.thShift θ p.2)| := by
      simpa only [Real.norm_eq_abs] using
        (MeasureTheory.norm_integral_le_integral_norm
          (f := fun p : ℝ × ℝ => Work.FTS.StrongEps.Jker ρ ε p *
            Z (Work.FTS.StrongEps.zShift z p.1) (Work.FTS.StrongEps.thShift θ p.2)))
    refine le_trans h1 ?_
    rw [show (fun p : ℝ × ℝ => |Work.FTS.StrongEps.Jker ρ ε p *
          Z (Work.FTS.StrongEps.zShift z p.1) (Work.FTS.StrongEps.thShift θ p.2)|)
        = (fun p : ℝ × ℝ => Work.FTS.StrongEps.Jker ρ ε p *
            |Z (Work.FTS.StrongEps.zShift z p.1) (Work.FTS.StrongEps.thShift θ p.2)|) from by
      funext p
      rw [abs_mul, abs_of_nonneg (hJnn p)]]
    have hle : (fun p : ℝ × ℝ => Work.FTS.StrongEps.Jker ρ ε p *
          |Z (Work.FTS.StrongEps.zShift z p.1) (Work.FTS.StrongEps.thShift θ p.2)|)
        ≤ᵐ[MeasureTheory.volume]
        (fun p : ℝ × ℝ => Work.FTS.StrongEps.Jker ρ ε p
          * (Cv2 * Work.Spaces.HkNorm α 4 Z)) :=
      Filter.Eventually.of_forall (fun p => mul_le_mul_of_nonneg_left (hpw p) (hJnn p))
    have hIntG : Integrable (fun p : ℝ × ℝ => Work.FTS.StrongEps.Jker ρ ε p
        * (Cv2 * Work.Spaces.HkNorm α 4 Z)) := hJint.mul_const _
    refine le_trans (MeasureTheory.integral_mono_of_nonneg
      (f := fun p : ℝ × ℝ => Work.FTS.StrongEps.Jker ρ ε p *
        |Z (Work.FTS.StrongEps.zShift z p.1) (Work.FTS.StrongEps.thShift θ p.2)|)
      (g := fun p : ℝ × ℝ => Work.FTS.StrongEps.Jker ρ ε p
        * (Cv2 * Work.Spaces.HkNorm α 4 Z))
      (Filter.Eventually.of_forall (fun p => mul_nonneg (hJnn p) (abs_nonneg _))) hIntG hle) ?_
    rw [MeasureTheory.integral_mul_const, hJmass, one_mul]
  -- ## the correction part
  have hJsm : Work.FTS.EllipticEst.SmoothOpen (Work.FTS.StrongEps.Jeps ρ ε Z) :=
    Work.FTS.StrongEps.smoothOpen_Jeps ρ hρ hε.1 hquad
  have hJmem : Work.Spaces.HkMem α 4 (Work.FTS.StrongEps.Jeps ρ ε Z) :=
    Work.FTS.StrongEps.HkMem_Jeps hρ.moll ⟨hα, hα1⟩ hε.1 hquad hmem
  have hnormJ : Work.Spaces.HkNorm α 4 (Work.FTS.StrongEps.Jeps ρ ε Z)
      ≤ Real.exp (CJ / 2) * Work.Spaces.HkNorm α 4 Z := by
    have hsq := hCJ α ⟨hα, hα1⟩ 4 ε hε.1 hε.2 Z hquad hmem hJmem
    rw [Work.Spaces.HkNorm, Work.Spaces.HkNorm]
    calc Real.sqrt (Work.Spaces.HkSq α 4 (Work.FTS.StrongEps.Jeps ρ ε Z))
        ≤ Real.sqrt (Real.exp (CJ * ε) * Work.Spaces.HkSq α 4 Z) := Real.sqrt_le_sqrt hsq
      _ = Real.sqrt (Real.exp (CJ * ε)) * Real.sqrt (Work.Spaces.HkSq α 4 Z) :=
          Real.sqrt_mul (Real.exp_pos _).le _
      _ = Real.exp (CJ * ε / 2) * Work.Spaces.HkNorm α 4 Z := by
          rw [Real.exp_half, Work.Spaces.HkNorm]
      _ ≤ Real.exp (CJ / 2) * Work.Spaces.HkNorm α 4 Z := by
          refine mul_le_mul_of_nonneg_right ?_ (Work.Spaces.HkNorm_nonneg _ _ _)
          exact Real.exp_le_exp.mpr (by nlinarith [hε.2, hCJpos])
  have hL12 : |Work.Construction.L12 (Work.FTS.StrongEps.Jeps ρ ε Z) 0|
      ≤ C1 * (Real.exp (CJ / 2) * Work.Spaces.HkNorm α 4 Z) := by
    refine le_trans (hC1 α hα hα1 (Work.FTS.StrongEps.Jeps ρ ε Z) ⟨hJsm, hJmem⟩) ?_
    exact mul_le_mul_of_nonneg_left hnormJ hC1pos.le
  have hbump : |Work.FTS.StrongEps.bump z θ| ≤ 1 := by
    rw [abs_le]
    exact ⟨by linarith [Work.FTS.StrongEps.bump_nonneg z θ],
      Work.FTS.StrongEps.EpsSqTools.bump_le_one z θ⟩
  have hc : |Work.Construction.L12 (Work.FTS.StrongEps.Jeps ρ ε Z) 0
        / Work.FTS.StrongEps.pzNorm| * |Work.FTS.StrongEps.bump z θ|
      ≤ (C1 * Real.exp (CJ / 2) / Work.FTS.StrongEps.pzNorm) * Work.Spaces.HkNorm α 4 Z := by
    rw [abs_div, abs_of_pos hpzpos]
    calc |Work.Construction.L12 (Work.FTS.StrongEps.Jeps ρ ε Z) 0| / Work.FTS.StrongEps.pzNorm
          * |Work.FTS.StrongEps.bump z θ|
        ≤ (C1 * (Real.exp (CJ / 2) * Work.Spaces.HkNorm α 4 Z)) / Work.FTS.StrongEps.pzNorm
            * 1 := by
          refine mul_le_mul (div_le_div_of_nonneg_right hL12 hpzpos.le) hbump (abs_nonneg _)
            (div_nonneg (mul_nonneg hC1pos.le (mul_nonneg (Real.exp_pos _).le hN0)) hpzpos.le)
      _ = (C1 * Real.exp (CJ / 2) / Work.FTS.StrongEps.pzNorm) * Work.Spaces.HkNorm α 4 Z := by
          ring
  -- ## assembly
  rw [Work.FTS.StrongEps.Pz_apply]
  have hsplit : |Work.FTS.StrongEps.Jeps ρ ε Z z θ
        - Work.Construction.L12 (Work.FTS.StrongEps.Jeps ρ ε Z) 0 / Work.FTS.StrongEps.pzNorm
          * Work.FTS.StrongEps.bump z θ|
      ≤ |Work.FTS.StrongEps.Jeps ρ ε Z z θ|
        + |Work.Construction.L12 (Work.FTS.StrongEps.Jeps ρ ε Z) 0 / Work.FTS.StrongEps.pzNorm
          * Work.FTS.StrongEps.bump z θ| := by
    have h := abs_add_le (Work.FTS.StrongEps.Jeps ρ ε Z z θ)
      (-(Work.Construction.L12 (Work.FTS.StrongEps.Jeps ρ ε Z) 0 / Work.FTS.StrongEps.pzNorm
        * Work.FTS.StrongEps.bump z θ))
    simpa only [sub_eq_add_neg, abs_neg] using h
  refine le_trans hsplit ?_
  have h2 : |Work.Construction.L12 (Work.FTS.StrongEps.Jeps ρ ε Z) 0 / Work.FTS.StrongEps.pzNorm
        * Work.FTS.StrongEps.bump z θ|
      ≤ (C1 * Real.exp (CJ / 2) / Work.FTS.StrongEps.pzNorm) * Work.Spaces.HkNorm α 4 Z := by
    rw [abs_mul]
    exact hc
  refine le_trans (add_le_add hJbound h2) (le_of_eq ?_)
  ring


end Work.FTS.StrongEps.E5G
