import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Submission.Work.FTS.MeridianDyn.Defs
import Submission.Work.FTS_BSIdentP.Slim.Dev9
import Submission.Work.FTS_BSIdentP.Slim.MerPsiOriginAux
import Submission.Work.FTS_BSIdentP.Slim.PsiFieldCorrCocompact
import Submission.Work.FTS_FinalLeaves.Min.SliceTheta

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.BSIdentP.Levels

open Work.FTS.BSIdent

open Filter Set
open scoped Topology

/-! ## Elementary facts about the axis point `z₀ • e₂` and the cylindrical frame -/

/-- The axis point `z • e₂` has vanishing cylindrical radius. -/
theorem radial_smul_e_two (z : ℝ) : Work.Cyl.radial (z • FiniteTimeSingularity.e 2) = 0 := by
  rw [Work.Cyl.radial, Work.Cyl.radSq]
  simp [FiniteTimeSingularity.e]

/-- The axis point `z • e₂` has axial coordinate `z`. -/
theorem axial_smul_e_two (z : ℝ) : Work.Cyl.axial (z • FiniteTimeSingularity.e 2) = z := by
  rw [Work.Cyl.axial]
  simp [FiniteTimeSingularity.e]

/-- The cylindrical radius is continuous on `ℝ³`. -/
theorem continuous_radial : Continuous (fun x : Work.FTS.BSIdent.R3 => Work.Cyl.radial x) := by
  have h : (fun x : Work.FTS.BSIdent.R3 => Work.Cyl.radial x)
      = fun x => Real.sqrt (x 0 ^ 2 + x 1 ^ 2) := by funext x; rfl
  rw [h]; fun_prop

/-- The axial coordinate is continuous on `ℝ³`. -/
theorem continuous_axial : Continuous (fun x : Work.FTS.BSIdent.R3 => Work.Cyl.axial x) := by
  have h : (fun x : Work.FTS.BSIdent.R3 => Work.Cyl.axial x) = fun x => x 2 := by
    funext x; rfl
  rw [h]; fun_prop

/-- The radial component `(a / r) • radialVec x` of `psiField` has norm exactly `|a|` off the
axis (and norm `0 ≤ |a|` on it), because `‖radialVec x‖ = radial x`. -/
theorem norm_div_smul_radialVec_le (a : ℝ) (x : Work.FTS.BSIdent.R3) :
    ‖(a / Work.Cyl.radial x) • Work.Cyl.radialVec x‖ ≤ |a| := by
  rw [norm_smul, Work.FTS.BSIdent.Cyl.norm_radialVec_eq, Real.norm_eq_abs, abs_div,
    abs_of_nonneg (Work.Cyl.radial_nonneg x)]
  rcases eq_or_lt_of_le (Work.Cyl.radial_nonneg x) with h | h
  · rw [← h]; simp
  · exact le_of_eq (div_mul_cancel₀ _ (ne_of_gt h))

/-- The `(e_r, e_z)` decomposition of `psiField ψ` in the cylindrical frame. -/
theorem psiField_eq_axis_decomp (ψ : ℝ → ℝ → ℝ) (x : Work.FTS.BSIdent.R3) :
    Work.Cyl.psiField ψ x
      = (Work.Cyl.pdZ ψ (Work.Cyl.radial x) (Work.Cyl.axial x) / Work.Cyl.radial x)
          • Work.Cyl.radialVec x
        + (-(ψ (Work.Cyl.radial x) (Work.Cyl.axial x) / Work.Cyl.radial x)
            - Work.Cyl.pdR ψ (Work.Cyl.radial x) (Work.Cyl.axial x)) • Work.Cyl.eZ := rfl

/-- **The axis limit, abstractly.**  If the three meridian limits `ψ/r → L`, `∂_rψ → L`,
`∂_zψ → 0` hold along the axis, then `psiField ψ` tends to `−2L • e_z`.  The radial component
`(∂_zψ/r) • radialVec` tends to `0` because its *norm* is `|∂_zψ|`, whatever the direction of
`radialVec` does. -/
theorem tendsto_psiField_of_axis_limits (ψ : ℝ → ℝ → ℝ) (L z₀ : ℝ)
    (H : Tendsto (fun x : Work.FTS.BSIdent.R3 => (Work.Cyl.radial x, Work.Cyl.axial x))
      (𝓝[{x : Work.FTS.BSIdent.R3 | Work.Cyl.radial x ≠ 0}]
        (z₀ • FiniteTimeSingularity.e 2))
      (𝓝[{p : ℝ × ℝ | 0 < p.1}] (0, z₀)))
    (h1 : Tendsto (fun p : ℝ × ℝ => ψ p.1 p.2 / p.1)
      (𝓝[{p : ℝ × ℝ | 0 < p.1}] (0, z₀)) (𝓝 L))
    (h2 : Tendsto (fun p : ℝ × ℝ => Work.Cyl.pdR ψ p.1 p.2)
      (𝓝[{p : ℝ × ℝ | 0 < p.1}] (0, z₀)) (𝓝 L))
    (h3 : Tendsto (fun p : ℝ × ℝ => Work.Cyl.pdZ ψ p.1 p.2)
      (𝓝[{p : ℝ × ℝ | 0 < p.1}] (0, z₀)) (𝓝 0)) :
    Tendsto (fun x : Work.FTS.BSIdent.R3 => Work.Cyl.psiField ψ x)
      (𝓝[{x : Work.FTS.BSIdent.R3 | Work.Cyl.radial x ≠ 0}]
        (z₀ • FiniteTimeSingularity.e 2))
      (𝓝 ((-(2 * L)) • Work.Cyl.eZ)) := by
  have H1 : Tendsto (fun x : Work.FTS.BSIdent.R3 =>
      ψ (Work.Cyl.radial x) (Work.Cyl.axial x) / Work.Cyl.radial x) _ (𝓝 L) := h1.comp H
  have H2 : Tendsto (fun x : Work.FTS.BSIdent.R3 =>
      Work.Cyl.pdR ψ (Work.Cyl.radial x) (Work.Cyl.axial x)) _ (𝓝 L) := h2.comp H
  have H3 : Tendsto (fun x : Work.FTS.BSIdent.R3 =>
      Work.Cyl.pdZ ψ (Work.Cyl.radial x) (Work.Cyl.axial x)) _ (𝓝 0) := h3.comp H
  -- the radial part, dominated by `|∂_zψ|`
  have hz1 : Tendsto (fun x : Work.FTS.BSIdent.R3 =>
      (Work.Cyl.pdZ ψ (Work.Cyl.radial x) (Work.Cyl.axial x) / Work.Cyl.radial x)
        • Work.Cyl.radialVec x)
      (𝓝[{x : Work.FTS.BSIdent.R3 | Work.Cyl.radial x ≠ 0}]
        (z₀ • FiniteTimeSingularity.e 2)) (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le (g := fun _ => (0 : ℝ))
      (h := fun x : Work.FTS.BSIdent.R3 =>
        |Work.Cyl.pdZ ψ (Work.Cyl.radial x) (Work.Cyl.axial x)|)
      tendsto_const_nhds ?_ ?_ ?_
    · have h := H3.abs
      rwa [abs_zero] at h
    · exact fun x => norm_nonneg _
    · exact fun x => norm_div_smul_radialVec_le _ x
  -- the axial part
  have hz2 : Tendsto (fun x : Work.FTS.BSIdent.R3 =>
      (-(ψ (Work.Cyl.radial x) (Work.Cyl.axial x) / Work.Cyl.radial x)
        - Work.Cyl.pdR ψ (Work.Cyl.radial x) (Work.Cyl.axial x)) • Work.Cyl.eZ)
      (𝓝[{x : Work.FTS.BSIdent.R3 | Work.Cyl.radial x ≠ 0}]
        (z₀ • FiniteTimeSingularity.e 2)) (𝓝 ((-(2 * L)) • Work.Cyl.eZ)) := by
    have h := (H1.neg.sub H2).smul_const (Work.Cyl.eZ)
    have hL : (-L - L : ℝ) = -(2 * L) := by ring
    rwa [hL] at h
  have hsum := hz1.add hz2
  rw [zero_add] at hsum
  refine hsum.congr' ?_
  filter_upwards with x
  exact (psiField_eq_axis_decomp ψ x).symm

theorem tendsto_psiField_axis {α : ℝ} {A B : ℝ → ℝ} {Φ : Work.FTS.BSIdent.Fam}
    {C : Physical.PhysClock} {t : ℝ} {τ z₀ : ℝ}
    (h1 : Filter.Tendsto (fun p : ℝ × ℝ =>
        Work.FTS.BSIdent.Cyl.merPsiT α A B Φ C t p.1 p.2 / p.1)
      (𝓝[{p : ℝ × ℝ | 0 < p.1}] ((0:ℝ), z₀))
      (𝓝 (Work.FTS.BSIdentP.Dev12.axisLevel α A B Φ τ z₀)))
    (h2 : Filter.Tendsto (fun p : ℝ × ℝ =>
        Work.Cyl.pdR (Work.FTS.BSIdent.Cyl.merPsiT α A B Φ C t) p.1 p.2)
      (𝓝[{p : ℝ × ℝ | 0 < p.1}] ((0:ℝ), z₀))
      (𝓝 (Work.FTS.BSIdentP.Dev12.axisLevel α A B Φ τ z₀)))
    (h3 : Filter.Tendsto (fun p : ℝ × ℝ =>
        Work.Cyl.pdZ (Work.FTS.BSIdent.Cyl.merPsiT α A B Φ C t) p.1 p.2)
      (𝓝[{p : ℝ × ℝ | 0 < p.1}] ((0:ℝ), z₀)) (𝓝 0)) :
    Filter.Tendsto (fun x : Work.FTS.BSIdent.R3 =>
        Work.Cyl.psiField (Work.FTS.BSIdent.Cyl.merPsiT α A B Φ C t) x)
      (𝓝[{x : Work.FTS.BSIdent.R3 | Work.Cyl.radial x ≠ 0}]
        (z₀ • FiniteTimeSingularity.e 2))
      (𝓝 ((-(2 * Work.FTS.BSIdentP.Dev12.axisLevel α A B Φ τ z₀)) • Work.Cyl.eZ)) := by
  -- transport the three meridian limits to `ℝ³` along the cylindrical map
  have hmap : Tendsto (fun x : Work.FTS.BSIdent.R3 => (Work.Cyl.radial x, Work.Cyl.axial x))
      (𝓝[{x : Work.FTS.BSIdent.R3 | Work.Cyl.radial x ≠ 0}]
        (z₀ • FiniteTimeSingularity.e 2))
      (𝓝[{p : ℝ × ℝ | 0 < p.1}] (0, z₀)) := by
    rw [tendsto_nhdsWithin_iff]
    refine ⟨?_, ?_⟩
    · have hcont : ContinuousAt (fun x : Work.FTS.BSIdent.R3 =>
          (Work.Cyl.radial x, Work.Cyl.axial x)) (z₀ • FiniteTimeSingularity.e 2) :=
        continuous_radial.continuousAt.prodMk continuous_axial.continuousAt
      have h := hcont.tendsto
      rw [radial_smul_e_two, axial_smul_e_two] at h
      exact h.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with x hx
      exact lt_of_le_of_ne (Work.Cyl.radial_nonneg x) (Ne.symm hx)
  exact tendsto_psiField_of_axis_limits _ _ _ hmap h1 h2 h3

end Work.FTS.BSIdentP.Levels
