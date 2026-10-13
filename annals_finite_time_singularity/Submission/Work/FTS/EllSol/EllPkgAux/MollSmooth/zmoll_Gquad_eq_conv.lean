/-
# `Work.FTS.EllSol.EllPkgAux.MollSmooth.zmoll_Gquad_eq_conv`

The double mollification `zmoll G δ ε z θ = ∫ t, sKer δ (log z - t) * thMoll G ε (e^t) θ` as
defined in `PkgK5/K5c/MollDefs` is the *iterated* integral of the two-dimensional kernel
`Kd δ ε` against the uncurried integrand `Hxy G (t,s) = Qext G (e^t) s`:

  `zmoll G δ ε z θ = ((Hxy G) ⋆[mul] (Kd δ ε)) (log z, θ)`.

This is the bridge that lets the smoothness theory of the two-dimensional convolution be used
for `zmoll`.  The proof is Fubini plus commutativity of the product: both sides are integrals of
the same function
`(t,s) ↦ Qext G (e^t) s * (sKer δ (log z - t) * sKer ε (θ - s))`,
the left one iterated, the right one against the product measure.  Integrability comes from
local integrability of `Hxy G` together with the fact that the (two-dimensional) kernel
`Kd δ ε` is continuous with compact support, so that its translate is again continuous with
compact support (`LocallyIntegrable.integrable_smul_left_of_hasCompactSupport`).
-/
import Mathlib.Analysis.Convolution
import Mathlib.Topology.UniformSpace.Uniformizable
import Submission.Work.FTS.EllSol.EllPkgAux.MollConvDefs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllSol.EllPkgAux.MollSmooth

set_option linter.unusedVariables false

/-- `sKer δ` is continuous. -/
private lemma sKer_continuous_moll (δ : ℝ) :
    Continuous (Work.FTS.EllSol.PkgK5.K5c.sKer δ) := by
  have h : Work.FTS.EllSol.PkgK5.K5c.sKer δ = fun t : ℝ =>
      (δ * Work.FTS.EllSol.PkgK5.K5c.sMass)⁻¹ *
        Work.FTS.EllSol.PkgK5.K5c.sBump (t / δ) := by
    funext t
    rw [Work.FTS.EllSol.PkgK5.K5c.sKer]
  rw [h]
  exact continuous_const.mul
    (Work.FTS.EllSol.PkgK5.K5c.sBump_continuous.comp (continuous_id.div_const δ))

/-- `Kd δ ε` is continuous. -/
private lemma Kd_continuous_moll (δ ε : ℝ) :
    Continuous (Work.FTS.EllSol.EllPkgAux.Kd δ ε) := by
  change Continuous (fun p : ℝ × ℝ => Work.FTS.EllSol.PkgK5.K5c.sKer δ p.1
    * Work.FTS.EllSol.PkgK5.K5c.sKer ε p.2)
  exact ((sKer_continuous_moll δ).comp continuous_fst).mul
    ((sKer_continuous_moll ε).comp continuous_snd)

/-- The `(t,s) ↦ Kd δ ε ((log z, θ) - (t,s))` translate of the two-dimensional kernel is
continuous. -/
private lemma Kd_shift_continuous_moll (δ ε z θ : ℝ) :
    Continuous (fun p : ℝ × ℝ => Work.FTS.EllSol.EllPkgAux.Kd δ ε ((Real.log z, θ) - p)) :=
  (Kd_continuous_moll δ ε).comp (continuous_const.sub continuous_id)

/-- It also has compact support: its support is contained in the box
`[log z - δ, log z + δ] × [θ - ε, θ + ε]`. -/
private lemma Kd_shift_hasCompactSupport_moll (δ ε z θ : ℝ) (hδ : 0 < δ) (hε : 0 < ε) :
    HasCompactSupport (fun p : ℝ × ℝ => Work.FTS.EllSol.EllPkgAux.Kd δ ε
      ((Real.log z, θ) - p)) := by
  refine HasCompactSupport.intro
    (K := Set.Icc (Real.log z - δ) (Real.log z + δ) ×ˢ Set.Icc (θ - ε) (θ + ε))
    (isCompact_Icc.prod isCompact_Icc) ?_
  intro p hp
  by_contra h0
  apply hp
  have hne : Work.FTS.EllSol.PkgK5.K5c.sKer δ (Real.log z - p.1) *
      Work.FTS.EllSol.PkgK5.K5c.sKer ε (θ - p.2) ≠ 0 := by
    intro h
    exact h0 (by simpa only [Work.FTS.EllSol.EllPkgAux.Kd, Prod.fst_sub, Prod.snd_sub] using h)
  have h1 : |Real.log z - p.1| < δ := by
    by_contra hle
    exact (mul_ne_zero_iff.mp hne).1
      (Work.FTS.EllSol.PkgK5.K5c.sKer_eq_zero_of_le_abs hδ (not_lt.mp hle))
  have h2 : |θ - p.2| < ε := by
    by_contra hle
    exact (mul_ne_zero_iff.mp hne).2
      (Work.FTS.EllSol.PkgK5.K5c.sKer_eq_zero_of_le_abs hε (not_lt.mp hle))
  rw [abs_lt] at h1 h2
  rw [Set.mem_prod]
  exact ⟨⟨by linarith [h1.1], by linarith [h1.2]⟩, ⟨by linarith [h2.1], by linarith [h2.2]⟩⟩

theorem zmoll_Gquad_eq_conv (G : ℝ → ℝ → ℝ)
    (hloc : MeasureTheory.LocallyIntegrable
      (Work.FTS.EllSol.EllPkgAux.Hxy (Work.FTS.EllSol.EllPkgAux.Gquad G)) MeasureTheory.volume)
    (δ ε : ℝ) (hδ : 0 < δ) (hε : 0 < ε) (z θ : ℝ) (hz : 0 < z) :
    Work.FTS.EllSol.PkgK5.K5c.zmoll (Work.FTS.EllSol.EllPkgAux.Gquad G) δ ε z θ
      = MeasureTheory.convolution (Work.FTS.EllSol.EllPkgAux.Hxy (Work.FTS.EllSol.EllPkgAux.Gquad G))
          (Work.FTS.EllSol.EllPkgAux.Kd δ ε) (ContinuousLinearMap.mul ℝ ℝ)
          MeasureTheory.volume (Real.log z, θ) := by
  have hInt : MeasureTheory.Integrable (fun p : ℝ × ℝ =>
      Work.FTS.EllSol.EllPkgAux.Hxy (Work.FTS.EllSol.EllPkgAux.Gquad G) p
        * Work.FTS.EllSol.EllPkgAux.Kd δ ε ((Real.log z, θ) - p)) MeasureTheory.volume := by
    refine (hloc.integrable_smul_left_of_hasCompactSupport
      (g := fun p : ℝ × ℝ => Work.FTS.EllSol.EllPkgAux.Kd δ ε ((Real.log z, θ) - p))
      (Kd_shift_continuous_moll δ ε z θ)
      (Kd_shift_hasCompactSupport_moll δ ε z θ hδ hε)).congr ?_
    filter_upwards with p
    simp only [smul_eq_mul]
    ring
  have hvol : (MeasureTheory.volume : MeasureTheory.Measure (ℝ × ℝ))
      = MeasureTheory.volume.prod MeasureTheory.volume := rfl
  have hL : Work.FTS.EllSol.PkgK5.K5c.zmoll (Work.FTS.EllSol.EllPkgAux.Gquad G) δ ε z θ
      = ∫ t : ℝ, Work.FTS.EllSol.PkgK5.K5c.sKer δ (Real.log z - t)
          * (∫ s : ℝ, Work.FTS.EllSol.PkgK5.K5c.sKer ε (θ - s)
              * Work.FTS.EllSol.PkgK5.K5c.Qext (Work.FTS.EllSol.EllPkgAux.Gquad G)
                  (Real.exp t) s) := rfl
  rw [hL, MeasureTheory.convolution_mul, hvol,
    MeasureTheory.integral_prod (fun p : ℝ × ℝ =>
      Work.FTS.EllSol.EllPkgAux.Hxy (Work.FTS.EllSol.EllPkgAux.Gquad G) p
        * Work.FTS.EllSol.EllPkgAux.Kd δ ε ((Real.log z, θ) - p)) hInt]
  refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
  refine (MeasureTheory.integral_const_mul (Work.FTS.EllSol.PkgK5.K5c.sKer δ (Real.log z - t))
    (fun s : ℝ => Work.FTS.EllSol.PkgK5.K5c.sKer ε (θ - s)
      * Work.FTS.EllSol.PkgK5.K5c.Qext (Work.FTS.EllSol.EllPkgAux.Gquad G)
          (Real.exp t) s)).symm.trans ?_
  refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun s => ?_)
  simp only [Work.FTS.EllSol.EllPkgAux.Hxy, Work.FTS.EllSol.EllPkgAux.Kd, Prod.fst_sub,
    Prod.snd_sub]
  ring

end Work.FTS.EllSol.EllPkgAux.MollSmooth
