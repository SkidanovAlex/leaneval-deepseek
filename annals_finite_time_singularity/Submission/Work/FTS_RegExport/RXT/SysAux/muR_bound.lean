import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Submission.Work.FTS.RegExportIface.RXT.Leaves

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS_RegExport.RXT.SysAux

/-- `|a - b - c| ≤ |a| + |b| + |c|` (elementary, used to split the defining identity of `Vz7`). -/
private lemma abs_sub_sub_le (a b c : ℝ) : |a - b - c| ≤ |a| + |b| + |c| := by
  have h1 : |a - b - c| ≤ |a - b| + |c| := by
    have := abs_add_le (a - b) (-c)
    simpa [sub_eq_add_neg] using this
  have h2 : |a - b| ≤ |a| + |b| := by
    have := abs_add_le a (-b)
    simpa [sub_eq_add_neg] using this
  linarith [abs_nonneg c]

/-- `Vz7` is affine in the clock `μ`:  `Vz7 α μ G Φ z θ τ = (1 - μ τ) + L12(τ) z * c2m θ
+ 2α * Vop(Φ̃(τ)) z θ`.  Hence a uniform sup bound on `Vz7` together with the uniform bound on
`L12` and the `O(z)`-vanishing bound on `Vop` bounds `μ` on `[0, S]`: evaluate at `z = 1`,
`θ = π/4`, where every term other than `μ` is controlled by a constant that does not depend
on `τ`. -/
theorem muR_bound {α S : ℝ} (hα : 0 < α) (hα13 : α ≤ 1 / 3) (hS : 0 < S)
    {Φs : Work.FTS.Galerkin.Fn} {E : Work.FTS.Galerkin.Fn →ₗ[ℝ] Work.FTS.Galerkin.Fn}
    {g : Work.FTS.Galerkin.Fam}
    (hVz : ∃ M : ℝ, ∀ σ ∈ Set.Icc (0:ℝ) S, ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      |Work.FTS.RegExportIface.Vz7 (Work.FTS.Regularity.pExp α)
        (Work.FTS.RegExportIface.RXT.μR α Φs E g)
        (Work.FTS.RegExportIface.RXT.GR α g) (Work.FTS.RegExportIface.RXT.ΦR α Φs E g)
        z θ σ| ≤ M)
    (hVop : ∃ M : ℝ, ∀ σ ∈ Set.Icc (0:ℝ) S, ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      |Work.Construction.Vop (Work.FTS.RegExportIface.phiTil (Work.FTS.Regularity.pExp α)
        (Work.FTS.RegExportIface.RXT.GR α g) (Work.FTS.RegExportIface.RXT.ΦR α Φs E g) σ)
        z θ| ≤ M * min z 1)
    (hL12b : ∃ C : ℝ, ∀ σ ∈ Set.Icc (0:ℝ) S, ∀ z : ℝ, 0 < z →
      |Work.Construction.L12 (Work.Construction.Ftau (Work.FTS.Regularity.pExp α)
        (Work.FTS.RegExportIface.RXT.GR α g) σ) z| ≤ C) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ σ ∈ Set.Icc (0:ℝ) S,
      |Work.FTS.RegExportIface.RXT.μR α Φs E g σ| ≤ C := by
  obtain ⟨M, hM⟩ := hVz
  obtain ⟨M₂, hM₂⟩ := hVop
  obtain ⟨C₁, hC₁⟩ := hL12b
  refine ⟨|M| + |C₁| * |Work.Construction.c2m (Real.pi / 4)|
    + 2 * |Work.FTS.Regularity.pExp α| * |M₂| + 1, by positivity, ?_⟩
  intro σ hσ
  have hpi : 0 < Real.pi := Real.pi_pos
  have hz : (0 : ℝ) < 1 := one_pos
  have hθ0 : (0 : ℝ) < Real.pi / 4 := by linarith
  have hθ1 : Real.pi / 4 < Real.pi / 2 := by linarith
  have h1 := hM σ hσ 1 (Real.pi / 4) hz hθ0 hθ1
  have h2 := hM₂ σ hσ 1 (Real.pi / 4) hz hθ0 hθ1
  have h3 := hC₁ σ hσ 1 hz
  simp only [min_self, mul_one] at h2
  -- the defining identity of `Vz7` at `(z, θ) = (1, π/4)`
  have hdec : (1 : ℝ) - Work.FTS.RegExportIface.RXT.μR α Φs E g σ
      = Work.FTS.RegExportIface.Vz7 (Work.FTS.Regularity.pExp α)
          (Work.FTS.RegExportIface.RXT.μR α Φs E g)
          (Work.FTS.RegExportIface.RXT.GR α g) (Work.FTS.RegExportIface.RXT.ΦR α Φs E g)
          1 (Real.pi / 4) σ
        - (Work.Construction.L12 (Work.Construction.Ftau (Work.FTS.Regularity.pExp α)
            (Work.FTS.RegExportIface.RXT.GR α g) σ) 1 * Work.Construction.c2m (Real.pi / 4))
        - (2 * Work.FTS.Regularity.pExp α
            * Work.Construction.Vop (Work.FTS.RegExportIface.phiTil (Work.FTS.Regularity.pExp α)
              (Work.FTS.RegExportIface.RXT.GR α g) (Work.FTS.RegExportIface.RXT.ΦR α Φs E g) σ)
              1 (Real.pi / 4)) := by
    unfold Work.FTS.RegExportIface.Vz7
    ring
  have hmain : |1 - Work.FTS.RegExportIface.RXT.μR α Φs E g σ|
      ≤ |M| + |C₁| * |Work.Construction.c2m (Real.pi / 4)|
        + 2 * |Work.FTS.Regularity.pExp α| * |M₂| := by
    have hT : |Work.FTS.RegExportIface.Vz7 (Work.FTS.Regularity.pExp α)
        (Work.FTS.RegExportIface.RXT.μR α Φs E g)
        (Work.FTS.RegExportIface.RXT.GR α g) (Work.FTS.RegExportIface.RXT.ΦR α Φs E g)
        1 (Real.pi / 4) σ| ≤ |M| := le_trans h1 (le_abs_self M)
    have hL : |Work.Construction.L12 (Work.Construction.Ftau (Work.FTS.Regularity.pExp α)
        (Work.FTS.RegExportIface.RXT.GR α g) σ) 1 * Work.Construction.c2m (Real.pi / 4)|
        ≤ |C₁| * |Work.Construction.c2m (Real.pi / 4)| := by
      rw [abs_mul]
      exact le_trans (mul_le_mul_of_nonneg_right h3 (abs_nonneg _))
        (mul_le_mul_of_nonneg_right (le_abs_self C₁) (abs_nonneg _))
    have hV : |2 * Work.FTS.Regularity.pExp α
        * Work.Construction.Vop (Work.FTS.RegExportIface.phiTil (Work.FTS.Regularity.pExp α)
          (Work.FTS.RegExportIface.RXT.GR α g) (Work.FTS.RegExportIface.RXT.ΦR α Φs E g) σ)
          1 (Real.pi / 4)| ≤ 2 * |Work.FTS.Regularity.pExp α| * |M₂| := by
      rw [abs_mul, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
      exact mul_le_mul_of_nonneg_left (le_trans h2 (le_abs_self M₂)) (by positivity)
    rw [hdec]
    refine le_trans (abs_sub_sub_le _ _ _) ?_
    linarith
  have habs : |Work.FTS.RegExportIface.RXT.μR α Φs E g σ|
      ≤ |1 - Work.FTS.RegExportIface.RXT.μR α Φs E g σ| + 1 := by
    have hsplit : Work.FTS.RegExportIface.RXT.μR α Φs E g σ
        = (Work.FTS.RegExportIface.RXT.μR α Φs E g σ - 1) + 1 := by ring
    calc |Work.FTS.RegExportIface.RXT.μR α Φs E g σ|
        = |(Work.FTS.RegExportIface.RXT.μR α Φs E g σ - 1) + 1| :=
            congrArg (fun x : ℝ => |x|) hsplit
      _ ≤ |Work.FTS.RegExportIface.RXT.μR α Φs E g σ - 1| + |(1 : ℝ)| := abs_add_le _ _
      _ = |1 - Work.FTS.RegExportIface.RXT.μR α Φs E g σ| + 1 := by
            rw [abs_sub_comm, abs_one]
  linarith

end Work.FTS_RegExport.RXT.SysAux
