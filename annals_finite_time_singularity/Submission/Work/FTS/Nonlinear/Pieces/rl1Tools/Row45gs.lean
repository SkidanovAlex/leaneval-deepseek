import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Submission.Work.FTS.Nonlinear.Pieces.rl1Tools.LintEngine
import Submission.Work.FTS.Nonlinear.Pieces.rl1Tools.FzFacts

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.Nonlinear.Pieces.rl1Tools

set_option maxHeartbeats 800000

/-!
# `Row45gs` — the `rl¹`-estimates of the `N₄^{gs}` and `N₅^{gs}` rows

The two degrees of freedom of `gRHS` that are `g`-linear and carry the *stationary* profile
`F_*` are

  `N₄^{gs}(z,θ) = -(1/2) sin(2θ) FK(g)(z) ∂_θF_*(z,θ)`,
  `N₅^{gs}(z,θ) = -sin²θ FK(g)(z) F_*(z,θ)`

(`Work.FTS.Nonlin.N4gs`, `Work.FTS.Nonlin.N5gs`), and the `rl¹`-norm of the row is

  `‖N‖_{rl¹} = ∫⁻_{r>0} r⁻¹ (∫⁻_{θ∈Iθ} |K θ · N(r,θ)|)`.

Both pieces are *radially factorised*: `F_*(z,θ) = α(Γ(θ)/c) F_*(z)` with `F_*(z) = 2z/(1+z)²`
and `∂_θF_* = α(Γ'(θ)/c) F_*(z)`, so every `θ`-integral is a numerical multiple of
`|FK(g)(r)| r/(1+r)²`, with the numerical factor bounded uniformly in `α ≤ 1` by
`Work.Spaces.Gam_bounds` (`Γ ≤ 1`), `Work.FTS.LocData.c_ge_three_fifths` (`c ≥ 3/5`) and
`abs_K_mul_deriv_Gam_le` (`|K·Γ'| ≤ 2α`).

The two measure-theoretic engines of `LintEngine` then finish: `inner_le_const` turns the
pointwise angular bound into the `θ`-lintegral, and `outer_le_radial` — with the row
hypothesis `∫ |FK(g)|/(1+z)² ≤ 2B` as its `L¹`-input — turns the radial profile
`C|FK(g)(r)|r/(1+r)²` against the weight `r⁻¹` into `ofReal (4CX)`.

The overall constant `K = 100` is generous: the sharp constants produced here are `80/3`
(for `N₄^{gs}`) and `80` (for `N₅^{gs}`), and the passage from `α` (resp. `α²`) to `α^{1/2}`
uses `α ≤ 1`.
-/

/-- **Pointwise angular bound for `N₅^{gs}`.**  For `θ ∈ Iθ`,
`|K θ · N₅^{gs}(α,g)(r,θ)| ≤ 10 α |FK(g)(r)| r/(1+r)²`, uniformly in `θ`:
`|K θ| sin²θ ≤ 3`, `Γ(θ)/c ≤ 5/3` and `F_*(r) = 2r/(1+r)²`. -/
lemma N5gs_ptwise_le {α : ℝ} {g : Work.FTS.Galerkin.Fn} (hα : 0 < α) (hα1 : α ≤ 1)
    {r : ℝ} (hr : 0 < r) {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) :
    |Work.Spaces.K θ * Work.FTS.Nonlin.N5gs α g r θ|
      ≤ 10 * α * |Work.Construction.FK g r| * r / (1 + r) ^ 2 := by
  have hc : (0:ℝ) < Work.Spaces.c α := by
    have := Work.FTS.LocData.c_ge_three_fifths α hα hα1
    linarith
  obtain ⟨hG0, hG1⟩ := Work.Spaces.Gam_bounds α θ hα hθ
  have hGc : Work.Spaces.Gam α θ / Work.Spaces.c α ≤ 5/3 := by
    rw [div_le_iff₀ hc]
    have := Work.FTS.LocData.c_ge_three_fifths α hα hα1
    linarith
  have hGcnn : 0 ≤ Work.Spaces.Gam α θ / Work.Spaces.c α := div_nonneg hG0 hc.le
  have hR : (0:ℝ) ≤ 2 * r / (1 + r) ^ 2 := by positivity
  have hK3 := abs_K_le_three θ
  have hsin : (Real.sin θ)^2 ≤ 1 := by
    nlinarith [Real.sin_le_one θ, Real.neg_one_le_sin θ]
  have hsin0 : (0:ℝ) ≤ (Real.sin θ)^2 := sq_nonneg _
  have hKsin : |Work.Spaces.K θ| * (Real.sin θ)^2 ≤ 3 := by
    nlinarith [abs_nonneg (Work.Spaces.K θ)]
  have hkey : |Work.Spaces.K θ * Work.FTS.Nonlin.N5gs α g r θ|
      = |Work.Spaces.K θ| * (Real.sin θ)^2 * |Work.Construction.FK g r|
          * (α * (Work.Spaces.Gam α θ / Work.Spaces.c α)) * (2 * r / (1 + r)^2) := by
    rw [Work.FTS.Nonlin.N5gs, Work.Construction.Fstar, Work.FM.Fstar]
    rw [show Work.Spaces.K θ * (-(Real.sin θ)^2 * Work.Construction.FK g r
          * (α * (Work.Spaces.Gam α θ / Work.Spaces.c α) * (2 * r / (1 + r)^2)))
        = -(Work.Spaces.K θ * (Real.sin θ)^2 * Work.Construction.FK g r
            * (α * (Work.Spaces.Gam α θ / Work.Spaces.c α)) * (2 * r / (1 + r)^2)) from by ring]
    rw [abs_neg, abs_mul, abs_mul, abs_mul, abs_mul,
      abs_of_nonneg hsin0, abs_of_nonneg (mul_nonneg hα.le hGcnn), abs_of_nonneg hR]
  rw [hkey]
  have h1 : |Work.Spaces.K θ| * (Real.sin θ)^2 * |Work.Construction.FK g r|
      * (α * (Work.Spaces.Gam α θ / Work.Spaces.c α)) * (2 * r / (1 + r)^2)
      ≤ 3 * |Work.Construction.FK g r| * (α * (5/3)) * (2 * r / (1 + r)^2) := by
    have hV : (0:ℝ) ≤ |Work.Construction.FK g r| := abs_nonneg _
    have h2 : |Work.Spaces.K θ| * (Real.sin θ)^2 * |Work.Construction.FK g r|
        ≤ 3 * |Work.Construction.FK g r| := by
      have := mul_le_mul_of_nonneg_right hKsin hV
      linarith [this]
    have h3 : α * (Work.Spaces.Gam α θ / Work.Spaces.c α) ≤ α * (5/3) :=
      mul_le_mul_of_nonneg_left hGc hα.le
    have h4 : 0 ≤ α * (Work.Spaces.Gam α θ / Work.Spaces.c α) := mul_nonneg hα.le hGcnn
    have h5 : 0 ≤ 3 * |Work.Construction.FK g r| := by positivity
    have h6 : |Work.Spaces.K θ| * (Real.sin θ)^2 * |Work.Construction.FK g r|
          * (α * (Work.Spaces.Gam α θ / Work.Spaces.c α))
        ≤ 3 * |Work.Construction.FK g r| * (α * (5/3)) :=
      mul_le_mul h2 h3 h4 h5
    exact mul_le_mul_of_nonneg_right h6 hR
  have h7 : 3 * |Work.Construction.FK g r| * (α * (5/3)) * (2 * r / (1 + r)^2)
      = 10 * α * |Work.Construction.FK g r| * r / (1 + r)^2 := by ring
  linarith [h7]

/-- **The `θ`-lintegral of `N₅^{gs}`**: the pointwise bound of `N5gs_ptwise_le` integrated
over `Iθ` (of measure `π/2 ≤ 2`) gives `ofReal (2·10 α |FK(g)(r)| r/(1+r)²)`. -/
lemma N5gs_angInt_le {α : ℝ} {g : Work.FTS.Galerkin.Fn} (hα : 0 < α) (hα1 : α ≤ 1)
    {r : ℝ} (hr : 0 < r) :
    (∫⁻ θ in Work.Spaces.Iθ,
        ENNReal.ofReal |Work.Spaces.K θ * Work.FTS.Nonlin.N5gs α g r θ|)
      ≤ ENNReal.ofReal (20 * α * |Work.Construction.FK g r| * r / (1 + r) ^ 2) := by
  have hD : (0:ℝ) ≤ 10 * α * |Work.Construction.FK g r| * r / (1 + r) ^ 2 := by positivity
  have h := inner_le_const hD (MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc
    (fun θ hθ => N5gs_ptwise_le hα hα1 hr hθ))
  rwa [show 2 * (10 * α * |Work.Construction.FK g r| * r / (1 + r) ^ 2)
      = 20 * α * |Work.Construction.FK g r| * r / (1 + r) ^ 2 from by ring] at h

/-- **Pointwise angular bound for `N₄^{gs}`**, a.e. on `Iθ`.  On the open interval
`∂_θF_* = α(Γ'/c)F_*` (`FzShape`), and `|K θ Γ'(θ)| sin(2θ) ≤ 2α` by
`abs_K_mul_deriv_Gam_le`; the endpoints are null. -/
lemma N4gs_ptwise_le {α : ℝ} {g : Work.FTS.Galerkin.Fn} (hα : 0 < α) (hα1 : α ≤ 1)
    {r : ℝ} (hr : 0 < r) :
    ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ),
      |Work.Spaces.K θ * Work.FTS.Nonlin.N4gs α g r θ|
        ≤ (10 / 3) * α ^ 2 * |Work.Construction.FK g r| * r / (1 + r) ^ 2 := by
  have hc : (0:ℝ) < Work.Spaces.c α := by
    have := Work.FTS.LocData.c_ge_three_fifths α hα hα1
    linarith
  have hR : (0:ℝ) ≤ Work.FM.Fstar r := by rw [Work.FM.Fstar]; positivity
  have hc5 : 1 / Work.Spaces.c α ≤ 5/3 := by
    rw [div_le_iff₀ hc]
    have := Work.FTS.LocData.c_ge_three_fifths α hα hα1
    linarith
  have hct0 : (0:ℝ) ≤ 1 / Work.Spaces.c α := by positivity
  rw [show MeasureTheory.volume.restrict Work.Spaces.Iθ
      = MeasureTheory.volume.restrict (Set.Ioo (0:ℝ) (Real.pi/2)) from by
    rw [Work.Spaces.Iθ]
    exact MeasureTheory.Measure.restrict_congr_set MeasureTheory.Ioo_ae_eq_Icc.symm]
  refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioo (fun θ hθ => ?_)
  have hθI : θ ∈ Work.Spaces.Iθ := ⟨hθ.1.le, hθ.2.le⟩
  have hshape := (FzShape α hα).1 r θ hθ.1 hθ.2
  have hKG : |Work.Spaces.K θ| * |Real.sin (2 * θ)|
      * |deriv (fun t => Work.Spaces.Gam α t) θ| ≤ 2 * α := by
    have h := abs_K_mul_deriv_Gam_le hα hθI
    rw [abs_mul] at h
    have hsin : |Real.sin (2 * θ)| ≤ 1 :=
      abs_le.mpr ⟨Real.neg_one_le_sin _, Real.sin_le_one _⟩
    calc |Work.Spaces.K θ| * |Real.sin (2 * θ)| * |deriv (fun t => Work.Spaces.Gam α t) θ|
        = |Work.Spaces.K θ| * |deriv (fun t => Work.Spaces.Gam α t) θ|
            * |Real.sin (2 * θ)| := by ring
      _ ≤ (2 * α) * 1 := mul_le_mul h hsin (abs_nonneg _) (by positivity)
      _ = 2 * α := by ring
  have hkey : |Work.Spaces.K θ * Work.FTS.Nonlin.N4gs α g r θ|
      = (1/2) * (|Work.Spaces.K θ| * |Real.sin (2 * θ)|
            * |deriv (fun t => Work.Spaces.Gam α t) θ|)
          * |Work.Construction.FK g r| * (α * (1 / Work.Spaces.c α)) * Work.FM.Fstar r := by
    rw [Work.FTS.Nonlin.N4gs, Work.Construction.s2, hshape]
    rw [show Work.Spaces.K θ * (-(1/2) * Real.sin (2 * θ) * Work.Construction.FK g r
          * (α * (deriv (fun t => Work.Spaces.Gam α t) θ / Work.Spaces.c α)
              * Work.FM.Fstar r))
        = -((1/2) * Work.Spaces.K θ * Real.sin (2 * θ)
            * deriv (fun t => Work.Spaces.Gam α t) θ * Work.Construction.FK g r
            * α * (1 / Work.Spaces.c α) * Work.FM.Fstar r) from by
      rw [div_eq_mul_inv]; ring]
    rw [abs_neg]
    simp only [abs_mul]
    rw [abs_of_nonneg (by norm_num : (0:ℝ) ≤ (1:ℝ)/2), abs_of_pos hα,
      abs_of_pos (one_div_pos.mpr hc), abs_of_nonneg hR]
    ring
  rw [hkey]
  have hstep : (1/2) * (|Work.Spaces.K θ| * |Real.sin (2 * θ)|
        * |deriv (fun t => Work.Spaces.Gam α t) θ|)
      * |Work.Construction.FK g r| * (α * (1 / Work.Spaces.c α)) * Work.FM.Fstar r
      ≤ (1/2) * (2 * α) * |Work.Construction.FK g r|
          * (α * (1 / Work.Spaces.c α)) * Work.FM.Fstar r := by
    have h0 : (0:ℝ) ≤ |Work.Construction.FK g r| * (α * (1 / Work.Spaces.c α))
        * Work.FM.Fstar r := by
      have h1 : (0:ℝ) ≤ 1 / Work.Spaces.c α := hct0
      positivity
    have h2 := mul_le_mul_of_nonneg_right hKG h0
    have h3 : (0:ℝ) ≤ (1/2 : ℝ) := by norm_num
    have h4 := mul_le_mul_of_nonneg_left h2 h3
    linarith [h4]
  have h5 : (1/2) * (2 * α) * |Work.Construction.FK g r|
      * (α * (1 / Work.Spaces.c α)) * Work.FM.Fstar r
      = α ^ 2 * |Work.Construction.FK g r| * (1 / Work.Spaces.c α) * Work.FM.Fstar r := by ring
  have hXR : (0:ℝ) ≤ α ^ 2 * |Work.Construction.FK g r| * Work.FM.Fstar r := by positivity
  have h6 : α ^ 2 * |Work.Construction.FK g r| * (1 / Work.Spaces.c α) * Work.FM.Fstar r
      ≤ α ^ 2 * |Work.Construction.FK g r| * (5/3) * Work.FM.Fstar r := by
    have := mul_nonpos_of_nonneg_of_nonpos hXR (by linarith : 1 / Work.Spaces.c α - 5/3 ≤ 0)
    linarith [this]
  have h7 : α ^ 2 * |Work.Construction.FK g r| * (5/3) * Work.FM.Fstar r
      = (10 / 3) * α ^ 2 * |Work.Construction.FK g r| * r / (1 + r) ^ 2 := by
    rw [Work.FM.Fstar]; ring
  linarith [hstep, h5, h6, h7]

/-- **The `θ`-lintegral of `N₄^{gs}`**, from the a.e. pointwise bound of `N4gs_ptwise_le`. -/
lemma N4gs_angInt_le {α : ℝ} {g : Work.FTS.Galerkin.Fn} (hα : 0 < α) (hα1 : α ≤ 1)
    {r : ℝ} (hr : 0 < r) :
    (∫⁻ θ in Work.Spaces.Iθ,
        ENNReal.ofReal |Work.Spaces.K θ * Work.FTS.Nonlin.N4gs α g r θ|)
      ≤ ENNReal.ofReal ((20 / 3) * α ^ 2 * |Work.Construction.FK g r| * r / (1 + r) ^ 2) := by
  have hD : (0:ℝ) ≤ (10/3) * α ^ 2 * |Work.Construction.FK g r| * r / (1 + r) ^ 2 := by positivity
  have h := inner_le_const hD (N4gs_ptwise_le hα hα1 hr)
  rwa [show 2 * ((10/3) * α ^ 2 * |Work.Construction.FK g r| * r / (1 + r) ^ 2)
      = (20/3) * α ^ 2 * |Work.Construction.FK g r| * r / (1 + r) ^ 2 from by ring] at h

theorem Row45gs :
    ∃ K : ℝ, 0 < K ∧ ∀ {α B : ℝ} {g : Work.FTS.Galerkin.Fn},
      0 < α → α ≤ 1 → 0 ≤ B → Work.FTS.Nonlin.GalClass α g →
      MeasureTheory.IntegrableOn (fun z => |Work.Construction.FK g z| / (1 + z) ^ 2)
        (Set.Ioi (0 : ℝ)) →
      (∫ z in Set.Ioi (0 : ℝ), |Work.Construction.FK g z| / (1 + z) ^ 2) ≤ 2 * B →
      (∫⁻ r in Set.Ioi (0 : ℝ), ENNReal.ofReal r⁻¹ * (∫⁻ θ in Work.Spaces.Iθ,
          ENNReal.ofReal |Work.Spaces.K θ * Work.FTS.Nonlin.N4gs α g r θ|))
        ≤ ENNReal.ofReal (K * B * α ^ (1 / 2 : ℝ)) ∧
      (∫⁻ r in Set.Ioi (0 : ℝ), ENNReal.ofReal r⁻¹ * (∫⁻ θ in Work.Spaces.Iθ,
          ENNReal.ofReal |Work.Spaces.K θ * Work.FTS.Nonlin.N5gs α g r θ|))
        ≤ ENNReal.ofReal (K * B * α ^ (1 / 2 : ℝ)) := by
  refine ⟨100, by norm_num, ?_⟩
  intro α B g hα hα1 hB hgal hint hle
  have hsnn : (0:ℝ) ≤ α ^ (1/2:ℝ) := Real.rpow_nonneg hα.le _
  have hα_le_sqrt : α ≤ α ^ (1/2:ℝ) := by
    have h1 : α ^ ((1:ℝ)/2 + 1/2) = α ^ (1/2:ℝ) * α ^ (1/2:ℝ) := Real.rpow_add hα _ _
    rw [show (1:ℝ)/2 + 1/2 = 1 by norm_num, Real.rpow_one] at h1
    have h2 : α ^ (1/2:ℝ) ≤ 1 := Real.rpow_le_one hα.le hα1 (by norm_num)
    nlinarith [h1, h2, hsnn]
  have hα2_le_sqrt : α ^ 2 ≤ α ^ (1/2:ℝ) := by
    have h1 : α ^ ((3:ℝ)/2 + 1/2) = α ^ ((3:ℝ)/2) * α ^ (1/2:ℝ) := Real.rpow_add hα _ _
    rw [show (3:ℝ)/2 + 1/2 = 2 by norm_num, Real.rpow_two] at h1
    have h2 : α ^ ((3:ℝ)/2) ≤ 1 := Real.rpow_le_one hα.le hα1 (by norm_num)
    nlinarith [h1, h2, hsnn]
  have hsB : (0:ℝ) ≤ α ^ (1/2:ℝ) * B := mul_nonneg hsnn hB
  constructor
  · have hmono : (∫⁻ r in Set.Ioi (0:ℝ), ENNReal.ofReal r⁻¹ *
        (∫⁻ θ in Work.Spaces.Iθ,
          ENNReal.ofReal |Work.Spaces.K θ * Work.FTS.Nonlin.N4gs α g r θ|))
        ≤ (∫⁻ r in Set.Ioi (0:ℝ), ENNReal.ofReal r⁻¹ *
            ENNReal.ofReal ((20/3) * α^2 * |Work.Construction.FK g r| * r/(1+r)^2)) := by
      refine MeasureTheory.lintegral_mono_ae ?_
      filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with r hr
      exact mul_le_mul' le_rfl (N4gs_angInt_le hα hα1 hr)
    have hout := outer_le_radial (ρ := Work.Construction.FK g) (X := B) (C := (20/3)*α^2)
      (by positivity) hB hint hle
    have hfin : ENNReal.ofReal (4 * ((20/3) * α^2) * B)
        ≤ ENNReal.ofReal (100 * B * α ^ (1/2:ℝ)) := by
      refine ENNReal.ofReal_le_ofReal ?_
      have hα2B : α^2 * B ≤ α ^ (1/2:ℝ) * B := mul_le_mul_of_nonneg_right hα2_le_sqrt hB
      nlinarith [hα2B, hsB]
    exact le_trans (le_trans hmono hout) hfin
  · have hmono : (∫⁻ r in Set.Ioi (0:ℝ), ENNReal.ofReal r⁻¹ *
        (∫⁻ θ in Work.Spaces.Iθ,
          ENNReal.ofReal |Work.Spaces.K θ * Work.FTS.Nonlin.N5gs α g r θ|))
        ≤ (∫⁻ r in Set.Ioi (0:ℝ), ENNReal.ofReal r⁻¹ *
            ENNReal.ofReal (20 * α * |Work.Construction.FK g r| * r/(1+r)^2)) := by
      refine MeasureTheory.lintegral_mono_ae ?_
      filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with r hr
      exact mul_le_mul' le_rfl (N5gs_angInt_le hα hα1 hr)
    have hout := outer_le_radial (ρ := Work.Construction.FK g) (X := B) (C := 20*α)
      (by positivity) hB hint hle
    have hfin : ENNReal.ofReal (4 * (20 * α) * B)
        ≤ ENNReal.ofReal (100 * B * α ^ (1/2:ℝ)) := by
      refine ENNReal.ofReal_le_ofReal ?_
      have hαB : α * B ≤ α ^ (1/2:ℝ) * B := mul_le_mul_of_nonneg_right hα_le_sqrt hB
      nlinarith [hαB, hsB]
    exact le_trans (le_trans hmono hout) hfin

end Work.FTS.Nonlinear.Pieces.rl1Tools
