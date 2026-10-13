import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.EllipticEst.LevelOneAsm.EigParsevalDefs
import Submission.Work.FTS.EllipticEst.LevelOneAsm.eigFun_span_dense

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology ENNReal
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.LevelOneAsm

local notation "Iθ" => Work.Spaces.Iθ

/-- **The inner product of `Θ_m` with an arbitrary `L²(angMeasure)`-class is the weighted
integral**

  `inner ℝ (eigLp m) y = ∫ θ in Iθ, Θ_m(θ)·y(θ)·cos θ`.

This is `inner_toLp_toLp` with the second argument an arbitrary class, using
`MeasureTheory.Lp.toLp_coeFn` implicitly through `L2.inner_def`, `eigLp_coe` and
`integral_angMeasure`. -/
lemma inner_eigLp_any (m : ℕ) (y : Lp ℝ 2 angMeasure) :
    inner ℝ (eigLp m) y = ∫ θ in Iθ, eigFun m θ * (y : ℝ → ℝ) θ * Real.cos θ := by
  rw [MeasureTheory.L2.inner_def]
  have h1 : (fun a => inner ℝ ((eigLp m : ℝ → ℝ) a) ((y : ℝ → ℝ) a))
      =ᵐ[angMeasure] fun a => eigFun m a * (y : ℝ → ℝ) a := by
    filter_upwards [eigLp_coe m] with a ha
    rw [ha, Real.inner_apply]
  rw [integral_congr_ae h1, integral_angMeasure]
  exact MeasureTheory.setIntegral_congr_fun measurableSet_Icc (fun θ _ => by ring)

/-- **Totality of the normalised angular eigenfamily `eigE` in `L²(Iθ, cos θ dθ)`**: the
orthogonal complement of the span of `eigE` is `⊥`.
Elaborate this file with `open scoped Real Topology ENNReal; open MeasureTheory Set Filter`.

Definitions used (all in `Submission/Work/FTS/EllipticEst/LevelOneAsm/EigParsevalDefs.lean`):
`angMeasure` with `∫ F ∂angMeasure = ∫ θ in Iθ, cos θ * F θ` (`integral_angMeasure`),
`eigLp n = MemLp.toLp (eigFun n) (memLp_eigFun n) : Lp ℝ 2 angMeasure` (`eigLp_coe`,
`inner_eigLp`, `inner_toLp_toLp`), `eigDn n = ∫ θ in Iθ, (eigFun (n+1) θ)^2 * cos θ`
(`eigDn_pos`) and `eigE n = (Real.sqrt (eigDn n))⁻¹ • eigLp (n+1)`, plus the measure facts
`angMeasure_absolutelyContinuous : angMeasure ≪ volume.restrict Iθ` and
`restrict_absolutelyContinuous_angMeasure : volume.restrict Iθ ≪ angMeasure`, and
`ae_mem_Iθ_angMeasure`.

Route. By `Submodule.eq_bot_iff` + `MeasureTheory.Lp.eq_zero_iff_ae_eq_zero` it suffices to show,
for `y : Lp ℝ 2 angMeasure` with `inner ℝ (eigE n) y = 0` for all `n`, that
`(y : ℝ → ℝ) =ᵐ[angMeasure] 0`.
* `inner ℝ (eigE n) y = 0` gives `inner ℝ (eigLp (n+1)) y = 0` (the scalar `(Real.sqrt (eigDn n))⁻¹`
  is nonzero by `eigDn_pos`), hence `∫ θ in Iθ, eigFun (n+1) θ * (y : ℝ → ℝ) θ * Real.cos θ = 0`
  (compute the inner product with `MeasureTheory.L2.inner_def`, `eigLp_coe` and
  `integral_angMeasure`).
* `MeasureTheory.Lp.memLp y : MemLp (y : ℝ → ℝ) 2 angMeasure` yields, via `integral_angMeasure` and
  `MeasureTheory.memLp_two_iff_integrable_sq`,
  `IntegrableOn (fun θ => ((y : ℝ → ℝ) θ)^2 * Real.cos θ) Iθ`, and its
  `AEStronglyMeasurable … angMeasure` transfers to `AEMeasurable … (volume.restrict Iθ)` along
  `restrict_absolutelyContinuous_angMeasure` (`AEStronglyMeasurable.mono_ac`).
* Apply `eigFun_span_dense` (from `Submission.Work.FTS.EllipticEst.LevelOneAsm.eigFun_span_dense`)
  to `f := (y : ℝ → ℝ)`, giving `(y : ℝ → ℝ) =ᵐ[volume.restrict Iθ] 0`; transfer back to
  `=ᵐ[angMeasure] 0` with `angMeasure_absolutelyContinuous` (`Measure.AbsolutelyContinuous.ae_eq`). -/
theorem eigE_span_orthogonal_eq_bot :
    (Submodule.span ℝ (Set.range eigE))ᗮ = ⊥ := by
  rw [Submodule.eq_bot_iff]
  intro y hy
  -- `y` is orthogonal to every `eigE n`
  have hmem : ∀ n : ℕ, inner ℝ (eigE n) y = 0 := fun n =>
    (Submodule.mem_orthogonal _ y).mp hy (eigE n) (Submodule.subset_span (Set.mem_range_self n))
  -- hence `y ⊥ Θ_{n+1}` (the normalising scalar `(√(eigDn n))⁻¹` does not vanish)
  have hLp : ∀ n : ℕ, inner ℝ (eigLp (n+1)) y = 0 := by
    intro n
    have h := hmem n
    simp only [eigE, real_inner_smul_left] at h
    rcases mul_eq_zero.mp h with h' | h'
    · exact absurd h' (inv_ne_zero (ne_of_gt (Real.sqrt_pos.mpr (eigDn_pos n))))
    · exact h'
  -- the orthogonality integrals
  have hint : ∀ n : ℕ, (∫ θ in Iθ, eigFun (n+1) θ * (y : ℝ → ℝ) θ * Real.cos θ) = 0 := by
    intro n
    rw [← inner_eigLp_any (n+1) y]
    exact hLp n
  -- a.e. strong measurability of `y` for the unweighted measure
  have hy_aesm_L : AEStronglyMeasurable (y : ℝ → ℝ) (volume.restrict Iθ) :=
    MeasureTheory.AEStronglyMeasurable.mono_ac restrict_absolutelyContinuous_angMeasure
      (MeasureTheory.Lp.memLp y).aestronglyMeasurable
  have hy_meas : AEMeasurable (y : ℝ → ℝ) (volume.restrict Iθ) := hy_aesm_L.aemeasurable
  -- square-integrability for `angMeasure` from `Lp.memLp`
  have hy_int_sq : Integrable (fun a => ((y : ℝ → ℝ) a)^2) angMeasure :=
    (MeasureTheory.memLp_two_iff_integrable_sq
      (MeasureTheory.Lp.memLp y).aestronglyMeasurable).mp (MeasureTheory.Lp.memLp y)
  -- transported to the unweighted measure: `(y)^2·cos θ` is integrable on `Iθ`
  have hy_int : IntegrableOn (fun θ => ((y : ℝ → ℝ) θ)^2 * Real.cos θ) Iθ := by
    show Integrable (fun θ => ((y : ℝ → ℝ) θ)^2 * Real.cos θ) (volume.restrict Iθ)
    have h := (MeasureTheory.integrable_withDensity_iff_integrable_smul'
      (μ := volume.restrict Iθ)
      (f := fun θ => ENNReal.ofReal (Real.cos θ))
      (Real.measurable_cos.ennreal_ofReal)
      (Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))
      (g := fun a => ((y : ℝ → ℝ) a)^2)).mp hy_int_sq
    refine h.congr ?_
    filter_upwards [ae_restrict_mem (s := Iθ) measurableSet_Icc] with θ hθ
    simp only [smul_eq_mul]
    rw [ENNReal.toReal_ofReal (cos_nonneg_of_mem_Iθ hθ)]
    ring
  -- the orthogonality hypothesis of `eigFun_span_dense` (ordered as requested)
  have horth : ∀ m : ℕ, 1 ≤ m →
      (∫ θ in Iθ, (y : ℝ → ℝ) θ * eigFun m θ * Real.cos θ) = 0 := by
    intro m hm
    obtain ⟨n, rfl⟩ : ∃ n, m = n + 1 := ⟨m - 1, by omega⟩
    rw [← hint n]
    exact MeasureTheory.setIntegral_congr_fun measurableSet_Icc (fun θ _ => by ring)
  have hae := eigFun_span_dense hy_meas hy_int horth
  have hae2 : (y : ℝ → ℝ) =ᵐ[angMeasure] 0 := angMeasure_absolutelyContinuous.ae_eq hae
  exact (MeasureTheory.Lp.eq_zero_iff_ae_eq_zero).mpr hae2

end Work.FTS.EllipticEst.LevelOneAsm
