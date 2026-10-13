import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Submission.Work.FTS.Nonlinear.Pieces.rl1Tools.starPt
import Submission.Work.FTS.Nonlinear.Pieces.rl1Tools.gPt
import Submission.Work.FTS.Nonlinear.Pieces.rl1Tools.FzFacts
import Submission.Work.FTS.Nonlinear.Pieces.rl1Tools.gSlots
import Submission.Work.FTS.Nonlinear.Pieces.rl1Tools.FKgFacts
import Submission.Work.FTS.H2.InvOneAddSq
import Submission.Work.FTS.Nonlinear.Pieces.rl1Tools.LintEngine
import Submission.Work.FTS.Nonlinear.Pieces.rl1Tools.FKradialL1
import Submission.Work.FTS.Nonlinear.Pieces.rl1Tools.Row45gs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.Nonlinear.Pieces.rl1Pieces

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

open Work.FTS.Nonlin (Xn N4Norm GalClass StarPkg EllPkgG N1gs N2gs N3gs N4gs N5gs)
open Work.Construction (Rop Uop Vop Fstar FK s2)
open Work.Spaces (Iθ pth Dz HkNorm HkNorm_nonneg)
open Work.FTS.Nonlinear.Pieces.rl1Tools (inner_le_const outer_le outer_le_radial FstarPt
  abs_K_le_three abs_sin_two_mul_deriv_Gam_le abs_K_mul_deriv_Gam_le)

set_option maxHeartbeats 1200000

/-- An almost-everywhere statement on the angular interval `Iθ = [0,π/2]` follows from the
corresponding statement on the open interval `(0,π/2)`. -/
theorem ae_Iθ_of_forall_Ioo {p : ℝ → Prop} (h : ∀ θ ∈ Set.Ioo (0 : ℝ) (π / 2), p θ) :
    ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ), p θ := by
  have hmeas : MeasureTheory.volume.restrict Work.Spaces.Iθ
      = MeasureTheory.volume.restrict (Set.Ioo (0 : ℝ) (π / 2)) := by
    rw [Work.Spaces.Iθ]
    exact MeasureTheory.Measure.restrict_congr_set
      (MeasureTheory.Ioo_ae_eq_Icc (μ := volume) (a := (0 : ℝ)) (b := π / 2)).symm
  rw [hmeas]
  exact MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioo h

/-- `√(10/α)·α = √(10α)` for `α > 0`. -/
theorem sqrt_div_mul_eq {α : ℝ} (hα : 0 < α) :
    Real.sqrt (10 / α) * α = Real.sqrt (10 * α) := by
  have h10 : (0 : ℝ) ≤ 10 / α := div_nonneg (by norm_num) hα.le
  calc Real.sqrt (10 / α) * α
      = Real.sqrt (10 / α) * Real.sqrt (α ^ 2) := by rw [Real.sqrt_sq hα.le]
    _ = Real.sqrt (10 / α * α ^ 2) := (Real.sqrt_mul h10 (α ^ 2)).symm
    _ = Real.sqrt (10 * α) := by rw [show 10 / α * α ^ 2 = 10 * α from by field_simp]

/-- `√(10/α)·α ≤ √10·α^{1/2}` for `α > 0`. -/
theorem sqrt_div_mul_le {α : ℝ} (hα : 0 < α) :
    Real.sqrt (10 / α) * α ≤ Real.sqrt 10 * α ^ (1 / 2 : ℝ) := by
  rw [sqrt_div_mul_eq hα, Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 10)]
  simp only [Real.sqrt_eq_rpow]
  exact le_refl _

/-- `√(10/α)·α² ≤ √10·α^{3/2}` for `α > 0`. -/
theorem sqrt_div_mul_sq_le {α : ℝ} (hα : 0 < α) :
    Real.sqrt (10 / α) * α ^ 2 ≤ Real.sqrt 10 * α ^ (3 / 2 : ℝ) := by
  have h3 := sqrt_div_mul_le hα
  calc Real.sqrt (10 / α) * α ^ 2 = (Real.sqrt (10 / α) * α) * α := by ring
    _ ≤ (Real.sqrt 10 * α ^ (1 / 2 : ℝ)) * α := mul_le_mul_of_nonneg_right h3 hα.le
    _ = Real.sqrt 10 * α ^ (3 / 2 : ℝ) := by
        rw [show (3 / 2 : ℝ) = (1 / 2 : ℝ) + 1 by norm_num, Real.rpow_add hα,
          Real.rpow_one]
        ring

/-- `α^{3/2} ≤ α^{1/2}` for `0 < α ≤ 1`. -/
theorem rpow_three_halves_le {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) :
    α ^ (3 / 2 : ℝ) ≤ α ^ (1 / 2 : ℝ) := by
  rw [show (3 / 2 : ℝ) = (1 / 2 : ℝ) + 1 by norm_num, Real.rpow_add hα, Real.rpow_one]
  have h1 : 0 < α ^ (1 / 2 : ℝ) := Real.rpow_pos_of_pos hα _
  nlinarith [hα1, h1]

/-- The elliptic coefficient `𝒰(Φ̃_g)/sin(2θ)` of `gPt`, read as a bound on `𝒰` itself
(the missing `sin(2θ)` is at most `1`). -/
theorem abs_Uop_le {α Ce : ℝ} {g Φg : Work.FTS.Galerkin.Fn} (hα : 0 < α) (hα1 : α ≤ 1)
    (hell : EllPkgG α Ce g Φg) :
    ∀ r, 0 < r → ∀ θ, 0 < θ → θ < π / 2 →
      |Uop α (Work.FTS.Nonlin.PhiTg α g Φg) r θ|
        ≤ 10 * Real.sqrt (10 / α) * max Ce 0 * Xn α g := by
  have hU := (Work.FTS.Nonlinear.Pieces.rl1Tools.gPt hα hα1 hell).2.1
  have hX0 : 0 ≤ Xn α g := HkNorm_nonneg α 4 g
  have hB0 : 0 ≤ 10 * Real.sqrt (10 / α) * max Ce 0 * Xn α g :=
    mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) (Real.sqrt_nonneg _))
      (le_max_right _ _)) hX0
  intro r hr θ hθ0 hθ1
  have h := hU r hr θ hθ0 hθ1
  have hs2 : 0 < Real.sin (2 * θ) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith)
  have hsa : Real.sin (2 * θ) ≤ 1 := Real.sin_le_one _
  have h' : |Uop α (Work.FTS.Nonlin.PhiTg α g Φg) r θ| / Real.sin (2 * θ)
      ≤ 10 * Real.sqrt (10 / α) * max Ce 0 * Xn α g := by
    simpa only [Work.Construction.s2, abs_div, abs_of_pos hs2] using h
  calc |Uop α (Work.FTS.Nonlin.PhiTg α g Φg) r θ|
      = |Uop α (Work.FTS.Nonlin.PhiTg α g Φg) r θ| / Real.sin (2 * θ) * Real.sin (2 * θ) :=
        (div_mul_cancel₀ _ (ne_of_gt hs2)).symm
    _ ≤ (10 * Real.sqrt (10 / α) * max Ce 0 * Xn α g) * 1 :=
        mul_le_mul h' hsa (by linarith [hs2]) hB0
    _ = 10 * Real.sqrt (10 / α) * max Ce 0 * Xn α g := by ring

/-- The pointwise size of `K θ · ∂_θF_*(r,θ)`: the profile factor `2r/(1+r)²` times the
*angular* combination `K θ Γ'(θ)`, which is bounded by `2α` because `K θ = (3/2)cos θ·sin 2θ`
and `sin(2θ)Γ'(θ) = α q(θ)Γ(θ)`. -/
theorem abs_K_pth_Fstar_le {α r θ : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) (hr : 0 < r)
    (hθ0 : 0 < θ) (hθ1 : θ < π / 2) :
    |Work.Spaces.K θ * pth (Fstar α) r θ| ≤ 80 * α ^ 2 * (r / (1 + r) ^ 2) := by
  have hc : (1 : ℝ) / 10 ≤ Work.Spaces.c α := (Work.Spaces.c_bounds α hα hα1).1
  have hc0 : 0 < Work.Spaces.c α := by linarith
  have hshape := (Work.FTS.Nonlinear.Pieces.rl1Tools.FzShape α hα).1 r θ hθ0 hθ1
  have hθI : θ ∈ Work.Spaces.Iθ := ⟨hθ0.le, hθ1.le⟩
  have hsc : |Work.Spaces.K θ| * |deriv (fun t => Work.Spaces.Gam α t) θ| ≤ 2 * α := by
    rw [← abs_mul]
    exact abs_K_mul_deriv_Gam_le hα hθI
  have hF : |Work.FM.Fstar r| = 2 * r / (1 + r) ^ 2 := by
    rw [Work.FM.Fstar, abs_of_nonneg (by positivity)]
  have hFnn : 0 ≤ |Work.FM.Fstar r| := abs_nonneg _
  have hΓnn : 0 ≤ |deriv (fun t => Work.Spaces.Gam α t) θ| := abs_nonneg _
  have hKn : 0 ≤ |Work.Spaces.K θ| := abs_nonneg _
  have hinv : |deriv (fun t => Work.Spaces.Gam α t) θ| / Work.Spaces.c α
      ≤ 10 * |deriv (fun t => Work.Spaces.Gam α t) θ| := by
    rw [div_le_iff₀ hc0]
    nlinarith [hΓnn, hc]
  have hval : |pth (Fstar α) r θ|
      = α * (|deriv (fun t => Work.Spaces.Gam α t) θ| / Work.Spaces.c α)
          * |Work.FM.Fstar r| := by
    calc |pth (Fstar α) r θ|
        = |α * (deriv (fun t => Work.Spaces.Gam α t) θ / Work.Spaces.c α)
            * Work.FM.Fstar r| := by rw [hshape]
      _ = |α| * |deriv (fun t => Work.Spaces.Gam α t) θ / Work.Spaces.c α|
            * |Work.FM.Fstar r| := by rw [abs_mul, abs_mul]
      _ = α * (|deriv (fun t => Work.Spaces.Gam α t) θ| / Work.Spaces.c α)
            * |Work.FM.Fstar r| := by rw [abs_div, abs_of_pos hα, abs_of_pos hc0]
  calc |Work.Spaces.K θ * pth (Fstar α) r θ|
      = |Work.Spaces.K θ| * |pth (Fstar α) r θ| := by rw [abs_mul]
    _ = |Work.Spaces.K θ| * (α * (|deriv (fun t => Work.Spaces.Gam α t) θ|
            / Work.Spaces.c α)) * |Work.FM.Fstar r| := by
        rw [hval]; ring
    _ ≤ |Work.Spaces.K θ| * (α * (10 * |deriv (fun t => Work.Spaces.Gam α t) θ|))
          * |Work.FM.Fstar r| := by
        refine mul_le_mul_of_nonneg_right ?_ hFnn
        refine mul_le_mul_of_nonneg_left ?_ hKn
        exact mul_le_mul_of_nonneg_left hinv hα.le
    _ = 10 * α * (|Work.Spaces.K θ| * |deriv (fun t => Work.Spaces.Gam α t) θ|)
          * |Work.FM.Fstar r| := by ring
    _ ≤ 10 * α * (2 * α) * |Work.FM.Fstar r| := by
        refine mul_le_mul_of_nonneg_right ?_ hFnn
        exact mul_le_mul_of_nonneg_left hsc (by positivity)
    _ = 20 * α ^ 2 * |Work.FM.Fstar r| := by ring
    _ ≤ 80 * α ^ 2 * (r / (1 + r) ^ 2) := by
        rw [hF]
        have h1 : 0 ≤ α ^ 2 * (r / (1 + r) ^ 2) :=
          mul_nonneg (sq_nonneg _) (div_nonneg hr.le (by positivity))
        calc 20 * α ^ 2 * (2 * r / (1 + r) ^ 2)
            = 40 * (α ^ 2 * (r / (1 + r) ^ 2)) := by ring
          _ ≤ 80 * (α ^ 2 * (r / (1 + r) ^ 2)) := by linarith
          _ = 80 * α ^ 2 * (r / (1 + r) ^ 2) := by ring

/-- **The `rl1`-reduction.**  If `|K θ · N r θ|` is bounded, uniformly in `θ`, by
`C r/(1+r)²`, then the `rl1`-norm of `N` is at most `ofReal (4C)`. -/
theorem rowStep {N : ℝ → ℝ → ℝ} {C : ℝ} (hC : 0 ≤ C)
    (h : ∀ r : ℝ, 0 < r → ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ),
        |Work.Spaces.K θ * N r θ| ≤ C * r / (1 + r) ^ 2) :
    (∫⁻ r in Set.Ioi (0 : ℝ), ENNReal.ofReal r⁻¹ * (∫⁻ θ in Work.Spaces.Iθ,
        ENNReal.ofReal |Work.Spaces.K θ * N r θ|)) ≤ ENNReal.ofReal (4 * C) := by
  have hinner : ∀ r ∈ Set.Ioi (0 : ℝ),
      (∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal |Work.Spaces.K θ * N r θ|)
        ≤ ENNReal.ofReal (2 * C * r / (1 + r) ^ 2) := by
    intro r hr
    have hr0 : 0 < r := hr
    have hD : 0 ≤ C * r / (1 + r) ^ 2 :=
      div_nonneg (mul_nonneg hC hr0.le) (by positivity)
    have h2 := inner_le_const (g := fun θ => |Work.Spaces.K θ * N r θ|) hD (h r hr0)
    rwa [show 2 * (C * r / (1 + r) ^ 2) = 2 * C * r / (1 + r) ^ 2 from by ring] at h2
  have hmono : (∫⁻ r in Set.Ioi (0 : ℝ), ENNReal.ofReal r⁻¹ * (∫⁻ θ in Work.Spaces.Iθ,
        ENNReal.ofReal |Work.Spaces.K θ * N r θ|))
      ≤ ∫⁻ r in Set.Ioi (0 : ℝ),
          ENNReal.ofReal r⁻¹ * ENNReal.ofReal (2 * C * r / (1 + r) ^ 2) := by
    refine MeasureTheory.lintegral_mono_ae ?_
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with r hr
    exact mul_le_mul_of_nonneg_left (hinner r hr)
      (show (0 : ENNReal) ≤ ENNReal.ofReal r⁻¹ from bot_le)
  refine hmono.trans ?_
  have hout := outer_le (C := 2 * C) (by positivity)
  rwa [show 2 * (2 * C) = 4 * C from by ring] at hout

/-- Row `N₁^{gs}`: `2ℛ(Φ̃_g)·F_*` is `α^{1/2}`-small in the `rl1`-norm. -/
theorem row1gs {α Ce : ℝ} {g Φg : Work.FTS.Galerkin.Fn} (hα : 0 < α) (hα1 : α ≤ 1)
    (hell : EllPkgG α Ce g Φg) :
    (∫⁻ r in Set.Ioi (0 : ℝ), ENNReal.ofReal r⁻¹ * (∫⁻ θ in Work.Spaces.Iθ,
        ENNReal.ofReal |Work.Spaces.K θ * N1gs α g Φg r θ|))
      ≤ ENNReal.ofReal (4800 * Real.sqrt 10 * max Ce 0 * Xn α g * α ^ (1 / 2 : ℝ)) := by
  have hR := (Work.FTS.Nonlinear.Pieces.rl1Tools.gPt hα hα1 hell).1
  have hX0 : 0 ≤ Xn α g := HkNorm_nonneg α 4 g
  have hCa0 : 0 ≤ max Ce 0 := le_max_right _ _
  have hs10 : 0 ≤ Real.sqrt 10 := Real.sqrt_nonneg 10
  have hsp : 0 ≤ α ^ (1 / 2 : ℝ) := Real.rpow_nonneg hα.le _
  have hB0 : 0 ≤ 10 * Real.sqrt (10 / α) * max Ce 0 * Xn α g :=
    mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) (Real.sqrt_nonneg _)) hCa0) hX0
  have hnn : 0 ≤ 1200 * Real.sqrt 10 * max Ce 0 * Xn α g * α ^ (1 / 2 : ℝ) :=
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hs10) hCa0) hX0) hsp
  have hsq := sqrt_div_mul_le hα
  refine (rowStep (C := 1200 * Real.sqrt 10 * max Ce 0 * Xn α g * α ^ (1 / 2 : ℝ))
    hnn ?_).trans ?_
  · intro r hr
    refine ae_Iθ_of_forall_Ioo ?_
    intro θ hθ
    obtain ⟨hθ0, hθ1⟩ := hθ
    have hθI : θ ∈ Work.Spaces.Iθ := ⟨hθ0.le, hθ1.le⟩
    have hb1 : |Work.Spaces.K θ| ≤ 3 := abs_K_le_three θ
    have hb2 : |Rop α (Work.FTS.Nonlin.PhiTg α g Φg) r θ|
        ≤ 10 * Real.sqrt (10 / α) * max Ce 0 * Xn α g := hR r hr θ hθ0 hθ1
    have hb3 : |Fstar α r θ| ≤ 20 * α * (r / (1 + r) ^ 2) :=
      (FstarPt hα hα1 hr.le hθI).1
    have habs : |Work.Spaces.K θ * N1gs α g Φg r θ|
        = 2 * |Work.Spaces.K θ| * |Rop α (Work.FTS.Nonlin.PhiTg α g Φg) r θ|
          * |Fstar α r θ| := by
      simp only [N1gs, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
      ring
    rw [habs]
    have hstep : 2 * |Work.Spaces.K θ| * |Rop α (Work.FTS.Nonlin.PhiTg α g Φg) r θ|
          * |Fstar α r θ|
        ≤ 2 * 3 * (10 * Real.sqrt (10 / α) * max Ce 0 * Xn α g)
          * (20 * α * (r / (1 + r) ^ 2)) := by
      have h1 : 2 * |Work.Spaces.K θ| ≤ 2 * 3 :=
        mul_le_mul_of_nonneg_left hb1 (by norm_num)
      have h2 : 2 * |Work.Spaces.K θ| * |Rop α (Work.FTS.Nonlin.PhiTg α g Φg) r θ|
          ≤ 2 * 3 * (10 * Real.sqrt (10 / α) * max Ce 0 * Xn α g) :=
        mul_le_mul h1 hb2 (abs_nonneg _) (by norm_num)
      exact mul_le_mul h2 hb3 (abs_nonneg _) (mul_nonneg (by norm_num) hB0)
    calc 2 * |Work.Spaces.K θ| * |Rop α (Work.FTS.Nonlin.PhiTg α g Φg) r θ|
          * |Fstar α r θ|
        ≤ 2 * 3 * (10 * Real.sqrt (10 / α) * max Ce 0 * Xn α g)
            * (20 * α * (r / (1 + r) ^ 2)) := hstep
      _ = 1200 * (Real.sqrt (10 / α) * α) * max Ce 0 * Xn α g
            * (r / (1 + r) ^ 2) := by ring
      _ ≤ 1200 * (Real.sqrt 10 * α ^ (1 / 2 : ℝ)) * max Ce 0 * Xn α g
            * (r / (1 + r) ^ 2) := by
          refine mul_le_mul_of_nonneg_right ?_ (div_nonneg hr.le (by positivity))
          refine mul_le_mul_of_nonneg_right ?_ hX0
          refine mul_le_mul_of_nonneg_right ?_ hCa0
          exact mul_le_mul_of_nonneg_left hsq (by norm_num)
      _ = 1200 * Real.sqrt 10 * max Ce 0 * Xn α g * α ^ (1 / 2 : ℝ) * r
            / (1 + r) ^ 2 := by ring
  · refine ENNReal.ofReal_le_ofReal (le_of_eq ?_)
    ring

/-- Row `N₂^{gs}`: `-2𝒰(Φ̃_g)·∂_θF_*`. -/
theorem row2gs {α Ce : ℝ} {g Φg : Work.FTS.Galerkin.Fn} (hα : 0 < α) (hα1 : α ≤ 1)
    (hell : EllPkgG α Ce g Φg) :
    (∫⁻ r in Set.Ioi (0 : ℝ), ENNReal.ofReal r⁻¹ * (∫⁻ θ in Work.Spaces.Iθ,
        ENNReal.ofReal |Work.Spaces.K θ * N2gs α g Φg r θ|))
      ≤ ENNReal.ofReal (6400 * Real.sqrt 10 * max Ce 0 * Xn α g * α ^ (1 / 2 : ℝ)) := by
  have hU := abs_Uop_le hα hα1 hell
  have hX0 : 0 ≤ Xn α g := HkNorm_nonneg α 4 g
  have hCa0 : 0 ≤ max Ce 0 := le_max_right _ _
  have hs10 : 0 ≤ Real.sqrt 10 := Real.sqrt_nonneg 10
  have hrpow := rpow_three_halves_le hα hα1
  have hnn : 0 ≤ 1600 * Real.sqrt 10 * max Ce 0 * Xn α g * α ^ (3 / 2 : ℝ) :=
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hs10) hCa0) hX0)
      (Real.rpow_nonneg hα.le _)
  have hsq := sqrt_div_mul_sq_le hα
  refine (rowStep (C := 1600 * Real.sqrt 10 * max Ce 0 * Xn α g * α ^ (3 / 2 : ℝ))
    hnn ?_).trans ?_
  · intro r hr
    refine ae_Iθ_of_forall_Ioo ?_
    intro θ hθ
    obtain ⟨hθ0, hθ1⟩ := hθ
    have hbU : |Uop α (Work.FTS.Nonlin.PhiTg α g Φg) r θ|
        ≤ 10 * Real.sqrt (10 / α) * max Ce 0 * Xn α g := hU r hr θ hθ0 hθ1
    have hb3 : |Work.Spaces.K θ| * |pth (Fstar α) r θ| ≤ 80 * α ^ 2 * (r / (1 + r) ^ 2) := by
      rw [← abs_mul]
      exact abs_K_pth_Fstar_le hα hα1 hr hθ0 hθ1
    have hB0 : 0 ≤ 10 * Real.sqrt (10 / α) * max Ce 0 * Xn α g :=
      mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) (Real.sqrt_nonneg _)) hCa0) hX0
    have habs : |Work.Spaces.K θ * N2gs α g Φg r θ|
        = 2 * |Uop α (Work.FTS.Nonlin.PhiTg α g Φg) r θ|
          * (|Work.Spaces.K θ| * |pth (Fstar α) r θ|) := by
      simp only [N2gs, abs_mul, abs_neg, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
      ring
    rw [habs]
    have hstep : 2 * |Uop α (Work.FTS.Nonlin.PhiTg α g Φg) r θ|
          * (|Work.Spaces.K θ| * |pth (Fstar α) r θ|)
        ≤ 2 * (10 * Real.sqrt (10 / α) * max Ce 0 * Xn α g)
          * (80 * α ^ 2 * (r / (1 + r) ^ 2)) := by
      have h1 : 2 * |Uop α (Work.FTS.Nonlin.PhiTg α g Φg) r θ|
          ≤ 2 * (10 * Real.sqrt (10 / α) * max Ce 0 * Xn α g) :=
        mul_le_mul_of_nonneg_left hbU (by norm_num)
      exact mul_le_mul h1 hb3 (mul_nonneg (abs_nonneg _) (abs_nonneg _))
        (mul_nonneg (by norm_num) hB0)
    calc 2 * |Uop α (Work.FTS.Nonlin.PhiTg α g Φg) r θ|
          * (|Work.Spaces.K θ| * |pth (Fstar α) r θ|)
        ≤ 2 * (10 * Real.sqrt (10 / α) * max Ce 0 * Xn α g)
            * (80 * α ^ 2 * (r / (1 + r) ^ 2)) := hstep
      _ = 1600 * (Real.sqrt (10 / α) * α ^ 2) * max Ce 0 * Xn α g
            * (r / (1 + r) ^ 2) := by ring
      _ ≤ 1600 * (Real.sqrt 10 * α ^ (3 / 2 : ℝ)) * max Ce 0 * Xn α g
            * (r / (1 + r) ^ 2) := by
          refine mul_le_mul_of_nonneg_right ?_ (div_nonneg hr.le (by positivity))
          refine mul_le_mul_of_nonneg_right ?_ hX0
          refine mul_le_mul_of_nonneg_right ?_ hCa0
          exact mul_le_mul_of_nonneg_left hsq (by norm_num)
      _ = 1600 * Real.sqrt 10 * max Ce 0 * Xn α g * α ^ (3 / 2 : ℝ) * r
            / (1 + r) ^ 2 := by ring
  · refine ENNReal.ofReal_le_ofReal ?_
    have hA : 0 ≤ 1600 * Real.sqrt 10 * max Ce 0 * Xn α g :=
      mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hs10) hCa0) hX0
    calc 4 * (1600 * Real.sqrt 10 * max Ce 0 * Xn α g * α ^ (3 / 2 : ℝ))
        = (1600 * Real.sqrt 10 * max Ce 0 * Xn α g) * (4 * α ^ (3 / 2 : ℝ)) := by ring
      _ ≤ (1600 * Real.sqrt 10 * max Ce 0 * Xn α g) * (4 * α ^ (1 / 2 : ℝ)) :=
          mul_le_mul_of_nonneg_left (by linarith [hrpow]) hA
      _ = 6400 * Real.sqrt 10 * max Ce 0 * Xn α g * α ^ (1 / 2 : ℝ) := by ring

/-- Row `N₃^{gs}`: `-2α𝒱(Φ̃_g)·D_zF_*`. -/
theorem row3gs {α Ce : ℝ} {g Φg : Work.FTS.Galerkin.Fn} (hα : 0 < α) (hα1 : α ≤ 1)
    (hell : EllPkgG α Ce g Φg) :
    (∫⁻ r in Set.Ioi (0 : ℝ), ENNReal.ofReal r⁻¹ * (∫⁻ θ in Work.Spaces.Iθ,
        ENNReal.ofReal |Work.Spaces.K θ * N3gs α g Φg r θ|))
      ≤ ENNReal.ofReal (9600 * Real.sqrt 10 * max Ce 0 * Xn α g * α ^ (1 / 2 : ℝ)) := by
  have hV := (Work.FTS.Nonlinear.Pieces.rl1Tools.gPt hα hα1 hell).2.2
  have hX0 : 0 ≤ Xn α g := HkNorm_nonneg α 4 g
  have hCa0 : 0 ≤ max Ce 0 := le_max_right _ _
  have hs10 : 0 ≤ Real.sqrt 10 := Real.sqrt_nonneg 10
  have hrpow := rpow_three_halves_le hα hα1
  have hnn : 0 ≤ 2400 * Real.sqrt 10 * max Ce 0 * Xn α g * α ^ (3 / 2 : ℝ) :=
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hs10) hCa0) hX0)
      (Real.rpow_nonneg hα.le _)
  have hsq := sqrt_div_mul_sq_le hα
  refine (rowStep (C := 2400 * Real.sqrt 10 * max Ce 0 * Xn α g * α ^ (3 / 2 : ℝ))
    hnn ?_).trans ?_
  · intro r hr
    refine ae_Iθ_of_forall_Ioo ?_
    intro θ hθ
    obtain ⟨hθ0, hθ1⟩ := hθ
    have hθI : θ ∈ Work.Spaces.Iθ := ⟨hθ0.le, hθ1.le⟩
    have hbV : |Vop (Work.FTS.Nonlin.PhiTg α g Φg) r θ|
        ≤ 10 * Real.sqrt (10 / α) * max Ce 0 * Xn α g := hV r hr θ hθ0 hθ1
    have hb3 : |Dz (Fstar α) r θ| ≤ 40 * α * (r / (1 + r) ^ 2) :=
      (FstarPt hα hα1 hr.le hθI).2
    have hB0 : 0 ≤ 10 * Real.sqrt (10 / α) * max Ce 0 * Xn α g :=
      mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) (Real.sqrt_nonneg _)) hCa0) hX0
    have habs : |Work.Spaces.K θ * N3gs α g Φg r θ|
        = 2 * α * |Work.Spaces.K θ| * |Vop (Work.FTS.Nonlin.PhiTg α g Φg) r θ|
          * |Dz (Fstar α) r θ| := by
      simp only [N3gs, abs_mul, abs_neg, abs_of_pos hα,
        abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
      ring
    rw [habs]
    have hstep : 2 * α * |Work.Spaces.K θ| * |Vop (Work.FTS.Nonlin.PhiTg α g Φg) r θ|
          * |Dz (Fstar α) r θ|
        ≤ 2 * α * 3 * (10 * Real.sqrt (10 / α) * max Ce 0 * Xn α g)
          * (40 * α * (r / (1 + r) ^ 2)) := by
      have h1 : 2 * α * |Work.Spaces.K θ| ≤ 2 * α * 3 :=
        mul_le_mul_of_nonneg_left (abs_K_le_three θ) (mul_nonneg (by norm_num) hα.le)
      have h2 : 2 * α * |Work.Spaces.K θ| * |Vop (Work.FTS.Nonlin.PhiTg α g Φg) r θ|
          ≤ 2 * α * 3 * (10 * Real.sqrt (10 / α) * max Ce 0 * Xn α g) :=
        mul_le_mul h1 hbV (abs_nonneg _)
          (mul_nonneg (mul_nonneg (by norm_num) hα.le) (by norm_num))
      exact mul_le_mul h2 hb3 (abs_nonneg _)
        (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hα.le) (by norm_num)) hB0)
    calc 2 * α * |Work.Spaces.K θ| * |Vop (Work.FTS.Nonlin.PhiTg α g Φg) r θ|
          * |Dz (Fstar α) r θ|
        ≤ 2 * α * 3 * (10 * Real.sqrt (10 / α) * max Ce 0 * Xn α g)
            * (40 * α * (r / (1 + r) ^ 2)) := hstep
      _ = 2400 * (Real.sqrt (10 / α) * α ^ 2) * max Ce 0 * Xn α g
            * (r / (1 + r) ^ 2) := by ring
      _ ≤ 2400 * (Real.sqrt 10 * α ^ (3 / 2 : ℝ)) * max Ce 0 * Xn α g
            * (r / (1 + r) ^ 2) := by
          refine mul_le_mul_of_nonneg_right ?_ (div_nonneg hr.le (by positivity))
          refine mul_le_mul_of_nonneg_right ?_ hX0
          refine mul_le_mul_of_nonneg_right ?_ hCa0
          exact mul_le_mul_of_nonneg_left hsq (by norm_num)
      _ = 2400 * Real.sqrt 10 * max Ce 0 * Xn α g * α ^ (3 / 2 : ℝ) * r
            / (1 + r) ^ 2 := by ring
  · refine ENNReal.ofReal_le_ofReal ?_
    have hA : 0 ≤ 2400 * Real.sqrt 10 * max Ce 0 * Xn α g :=
      mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hs10) hCa0) hX0
    calc 4 * (2400 * Real.sqrt 10 * max Ce 0 * Xn α g * α ^ (3 / 2 : ℝ))
        = (2400 * Real.sqrt 10 * max Ce 0 * Xn α g) * (4 * α ^ (3 / 2 : ℝ)) := by ring
      _ ≤ (2400 * Real.sqrt 10 * max Ce 0 * Xn α g) * (4 * α ^ (1 / 2 : ℝ)) :=
          mul_le_mul_of_nonneg_left (by linarith [hrpow]) hA
      _ = 9600 * Real.sqrt 10 * max Ce 0 * Xn α g * α ^ (1 / 2 : ℝ) := by ring

theorem Pgs {α₂ Ci Ce Cs : ℝ} :
    ∃ K : ℝ, 0 < K ∧ ∀ {α : ℝ} {g Φs Φg : Work.FTS.Galerkin.Fn},
      0 < α → α ≤ 1 → α ≤ α₂ → Work.FTS.Nonlin.N4Norm Ci α₂ →
      Work.FTS.Nonlin.GalClass α g → Work.FTS.Nonlin.StarPkg α Cs Φs →
      Work.FTS.Nonlin.EllPkgG α Ce g Φg →
      (∫⁻ r in Set.Ioi (0 : ℝ), ENNReal.ofReal r⁻¹ * (∫⁻ θ in Work.Spaces.Iθ,
          ENNReal.ofReal |Work.Spaces.K θ * Work.FTS.Nonlin.N1gs α g Φg r θ|))
        ≤ ENNReal.ofReal (K * α ^ (1 / 2 : ℝ) * Work.FTS.Nonlin.Xn α g) ∧
      (∫⁻ r in Set.Ioi (0 : ℝ), ENNReal.ofReal r⁻¹ * (∫⁻ θ in Work.Spaces.Iθ,
          ENNReal.ofReal |Work.Spaces.K θ * Work.FTS.Nonlin.N2gs α g Φg r θ|))
        ≤ ENNReal.ofReal (K * α ^ (1 / 2 : ℝ) * Work.FTS.Nonlin.Xn α g) ∧
      (∫⁻ r in Set.Ioi (0 : ℝ), ENNReal.ofReal r⁻¹ * (∫⁻ θ in Work.Spaces.Iθ,
          ENNReal.ofReal |Work.Spaces.K θ * Work.FTS.Nonlin.N3gs α g Φg r θ|))
        ≤ ENNReal.ofReal (K * α ^ (1 / 2 : ℝ) * Work.FTS.Nonlin.Xn α g) ∧
      (∫⁻ r in Set.Ioi (0 : ℝ), ENNReal.ofReal r⁻¹ * (∫⁻ θ in Work.Spaces.Iθ,
          ENNReal.ofReal |Work.Spaces.K θ * Work.FTS.Nonlin.N4gs α g r θ|))
        ≤ ENNReal.ofReal (K * α ^ (1 / 2 : ℝ) * Work.FTS.Nonlin.Xn α g) ∧
      (∫⁻ r in Set.Ioi (0 : ℝ), ENNReal.ofReal r⁻¹ * (∫⁻ θ in Work.Spaces.Iθ,
          ENNReal.ofReal |Work.Spaces.K θ * Work.FTS.Nonlin.N5gs α g r θ|))
        ≤ ENNReal.ofReal (K * α ^ (1 / 2 : ℝ) * Work.FTS.Nonlin.Xn α g) := by
  obtain ⟨K45, hK45pos, hrow45⟩ := Work.FTS.Nonlinear.Pieces.rl1Tools.Row45gs
  refine ⟨1 + 100000 * max Ce 0 + K45 * max Ci 0, ?_, ?_⟩
  · have h2 : 0 ≤ 100000 * max Ce 0 := mul_nonneg (by norm_num) (le_max_right _ _)
    have h3 : 0 ≤ K45 * max Ci 0 := mul_nonneg hK45pos.le (le_max_right _ _)
    linarith
  intro α g Φs Φg hα hα1 hαα₂ hN hgal hstar hell
  have hCa0 : 0 ≤ max Ce 0 := le_max_right _ _
  have hCi0 : 0 ≤ max Ci 0 := le_max_right _ _
  have hX0 : 0 ≤ Xn α g := HkNorm_nonneg α 4 g
  have hsp : 0 ≤ α ^ (1 / 2 : ℝ) := Real.rpow_nonneg hα.le _
  have hs10le : Real.sqrt 10 ≤ 4 := by
    have h := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 10)
    nlinarith [Real.sqrt_nonneg 10]
  have key : ∀ c : ℝ, 0 ≤ c → c ≤ 100000 →
      c * max Ce 0 * Xn α g * α ^ (1 / 2 : ℝ)
        ≤ (1 + 100000 * max Ce 0 + K45 * max Ci 0) * α ^ (1 / 2 : ℝ) * Xn α g := by
    intro c hc hcle
    have h1 : c * max Ce 0 ≤ 100000 * max Ce 0 := mul_le_mul_of_nonneg_right hcle hCa0
    have h2 : 100000 * max Ce 0 ≤ 1 + 100000 * max Ce 0 + K45 * max Ci 0 := by
      have h4 := mul_nonneg hK45pos.le hCi0
      linarith
    calc c * max Ce 0 * Xn α g * α ^ (1 / 2 : ℝ)
        = (c * max Ce 0) * (Xn α g * α ^ (1 / 2 : ℝ)) := by ring
      _ ≤ (100000 * max Ce 0) * (Xn α g * α ^ (1 / 2 : ℝ)) :=
            mul_le_mul_of_nonneg_right h1 (mul_nonneg hX0 hsp)
      _ ≤ (1 + 100000 * max Ce 0 + K45 * max Ci 0) * (Xn α g * α ^ (1 / 2 : ℝ)) :=
            mul_le_mul_of_nonneg_right h2 (mul_nonneg hX0 hsp)
      _ = (1 + 100000 * max Ce 0 + K45 * max Ci 0) * α ^ (1 / 2 : ℝ) * Xn α g := by ring
  have hc1 : 4800 * Real.sqrt 10 ≤ 100000 := by linarith
  have hc2 : 6400 * Real.sqrt 10 ≤ 100000 := by linarith
  have hc3 : 9600 * Real.sqrt 10 ≤ 100000 := by linarith
  obtain ⟨hFKint, hFKle⟩ :=
    Work.FTS.Nonlinear.Pieces.rl1Tools.FKradialL1 hN (α := α) (g := g) hα hαα₂ hgal
  have hFKle' : (∫ z in Set.Ioi (0 : ℝ), |FK g z| / (1 + z) ^ 2) ≤ 2 * (Ci * Xn α g) := by
    rw [show 2 * (Ci * Xn α g) = 2 * Ci * Xn α g from by ring]
    exact hFKle
  have hB0 : 0 ≤ Ci * Xn α g := mul_nonneg hN.pos.1.le hX0
  obtain ⟨hrow4, hrow5⟩ :=
    hrow45 (α := α) (B := Ci * Xn α g) (g := g) hα hα1 hB0 hgal hFKint hFKle'
  have hKCi : K45 * Ci ≤ 1 + 100000 * max Ce 0 + K45 * max Ci 0 := by
    have h1 : Ci ≤ max Ci 0 := le_max_left _ _
    have h2 : K45 * Ci ≤ K45 * max Ci 0 := mul_le_mul_of_nonneg_left h1 hK45pos.le
    have h3 : 0 ≤ 100000 * max Ce 0 := mul_nonneg (by norm_num) hCa0
    linarith
  have hcmp : K45 * (Ci * Xn α g) * α ^ (1 / 2 : ℝ)
      ≤ (1 + 100000 * max Ce 0 + K45 * max Ci 0) * α ^ (1 / 2 : ℝ) * Xn α g := by
    calc K45 * (Ci * Xn α g) * α ^ (1 / 2 : ℝ)
        = (K45 * Ci) * (Xn α g * α ^ (1 / 2 : ℝ)) := by ring
      _ ≤ (1 + 100000 * max Ce 0 + K45 * max Ci 0) * (Xn α g * α ^ (1 / 2 : ℝ)) :=
            mul_le_mul_of_nonneg_right hKCi (mul_nonneg hX0 hsp)
      _ = (1 + 100000 * max Ce 0 + K45 * max Ci 0) * α ^ (1 / 2 : ℝ) * Xn α g := by ring
  exact ⟨(row1gs hα hα1 hell).trans
      (ENNReal.ofReal_le_ofReal (key (4800 * Real.sqrt 10)
        (mul_nonneg (by norm_num) (Real.sqrt_nonneg 10)) hc1)),
    (row2gs hα hα1 hell).trans
      (ENNReal.ofReal_le_ofReal (key (6400 * Real.sqrt 10)
        (mul_nonneg (by norm_num) (Real.sqrt_nonneg 10)) hc2)),
    (row3gs hα hα1 hell).trans
      (ENNReal.ofReal_le_ofReal (key (9600 * Real.sqrt 10)
        (mul_nonneg (by norm_num) (Real.sqrt_nonneg 10)) hc3)),
    hrow4.trans (ENNReal.ofReal_le_ofReal hcmp),
    hrow5.trans (ENNReal.ofReal_le_ofReal hcmp)⟩

end

end Work.FTS.Nonlinear.Pieces.rl1Pieces
