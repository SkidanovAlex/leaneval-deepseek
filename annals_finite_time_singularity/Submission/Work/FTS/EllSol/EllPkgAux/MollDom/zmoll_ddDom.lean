import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.EllSol.EllPkgAux.MollBase
import Submission.Work.FTS.EllSol.EllPkgAux.KernelDefs
import Submission.Work.FTS.EllSol.PkgK5.K5c.MollDefs
import Submission.Work.FTS.EllSol.EllPkgAux.kernelJensen
import Submission.Work.FTS.EllSol.EllPkgAux.MollFatouAux
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.FTS.EllSol.EllPkgAux.MollDom.slice_data
import Submission.Work.FTS.EllSol.EllPkgAux.MollDom.ddG_sliceL1_bound
import Submission.Work.FTS.EllSol.EllPkgAux.MollDom.KJDdG
import Submission.Work.FTS.EllSol.EllPkgAux.MollDom.zmollDz2Eq

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllSol.EllPkgAux.MollDom

open scoped Real Topology
open MeasureTheory Set Filter
open Work.FTS.EllSol.PkgK5.K5c
open Work.Spaces (Dz pz)

local notation "Iθ" => Work.Spaces.Iθ

set_option maxHeartbeats 4000000

/-- The three-image kernel of the doubly odd extension is dominated by the all-plus kernel. -/
theorem Kern_le_KJ {ε θ s : ℝ} (hε : 0 < ε) :
    ‖Work.FTS.EllSol.EllPkgAux.Kern (sKer ε) θ s‖ ≤ Work.FTS.EllSol.EllPkgAux.KJ ε θ s := by
  have h1 : (0 : ℝ) ≤ sKer ε (θ - s) := sKer_nonneg hε _
  have h2 : (0 : ℝ) ≤ sKer ε (θ + s) := sKer_nonneg hε _
  have h3 : (0 : ℝ) ≤ sKer ε (θ + s - Real.pi) := sKer_nonneg hε _
  have h4 : ‖sKer ε (θ - s) - sKer ε (θ + s) - sKer ε (θ + s - Real.pi)‖
      ≤ ‖sKer ε (θ - s) - sKer ε (θ + s)‖ + ‖sKer ε (θ + s - Real.pi)‖ :=
    norm_sub_le _ _
  have h5 : ‖sKer ε (θ - s) - sKer ε (θ + s)‖ ≤ sKer ε (θ - s) + sKer ε (θ + s) := by
    have h := norm_sub_le (sKer ε (θ - s)) (sKer ε (θ + s))
    simpa only [Real.norm_of_nonneg h1, Real.norm_of_nonneg h2] using h
  have h6 : ‖sKer ε (θ + s - Real.pi)‖ = sKer ε (θ + s - Real.pi) :=
    Real.norm_of_nonneg h3
  have hKJ : Work.FTS.EllSol.EllPkgAux.KJ ε θ s
      = sKer ε (θ - s) + sKer ε (θ + s) + sKer ε (θ + s - Real.pi) := rfl
  have hKn : Work.FTS.EllSol.EllPkgAux.Kern (sKer ε) θ s
      = sKer ε (θ - s) - sKer ε (θ + s) - sKer ε (θ + s - Real.pi) := rfl
  rw [hKJ, hKn]
  linarith [h4, h5, h6]

/-- The `Kern`-integral of a fixed slice is dominated by the `KJ`-kernel against its modulus. -/
theorem Kern_integral_le {X : ℝ → ℝ} {ε θ : ℝ} (hε : 0 < ε) (hX : IntegrableOn X Iθ) :
    ‖∫ s in Iθ, Work.FTS.EllSol.EllPkgAux.Kern (sKer ε) θ s * X s‖
      ≤ ∫ s in Iθ, Work.FTS.EllSol.EllPkgAux.KJ ε θ s * ‖X s‖ := by
  have hKJcont : Continuous (fun s : ℝ => Work.FTS.EllSol.EllPkgAux.KJ ε θ s) := by
    have hker : Continuous (sKer ε) :=
      (Work.FTS.EllSol.EllPkgAux.contDiff_sKer ε (n := 1)).continuous
    have h1 : Continuous (fun s : ℝ => sKer ε (θ - s)) :=
      hker.comp (continuous_const.sub continuous_id)
    have h2 : Continuous (fun s : ℝ => sKer ε (θ + s)) :=
      hker.comp (continuous_const.add continuous_id)
    have h3 : Continuous (fun s : ℝ => sKer ε (θ + s - Real.pi)) :=
      hker.comp ((continuous_const.add continuous_id).sub continuous_const)
    have hsum : Continuous (fun s : ℝ =>
        sKer ε (θ - s) + sKer ε (θ + s) + sKer ε (θ + s - Real.pi)) := (h1.add h2).add h3
    simpa only [Work.FTS.EllSol.EllPkgAux.KJ] using hsum
  have hXint : IntegrableOn (fun s : ℝ => Work.FTS.EllSol.EllPkgAux.KJ ε θ s * ‖X s‖) Iθ :=
    IntegrableOn.continuousOn_mul hKJcont.continuousOn hX.norm isCompact_Icc
  have hKcont : Continuous (fun s : ℝ => Work.FTS.EllSol.EllPkgAux.Kern (sKer ε) θ s) := by
    have hker : Continuous (sKer ε) :=
      (Work.FTS.EllSol.EllPkgAux.contDiff_sKer ε (n := 1)).continuous
    exact ((hker.comp (continuous_const.sub continuous_id)).sub
      (hker.comp (continuous_const.add continuous_id))).sub
      (hker.comp ((continuous_const.add continuous_id).sub continuous_const))
  have hKint : IntegrableOn (fun s : ℝ => ‖Work.FTS.EllSol.EllPkgAux.Kern (sKer ε) θ s
      * X s‖) Iθ := by
    refine (IntegrableOn.continuousOn_mul hKcont.norm.continuousOn hX.norm
      isCompact_Icc).congr_fun ?_ measurableSet_Icc
    intro s _
    exact (norm_mul _ _).symm
  refine (MeasureTheory.norm_integral_le_integral_norm _).trans ?_
  refine setIntegral_mono_on hKint hXint measurableSet_Icc (fun s _ => ?_)
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_right (Kern_le_KJ hε) (norm_nonneg _)

/-- The log-convolution of a function dominated by `Φ` is dominated by the log-convolution
of `Φ`. -/
theorem znorm_le {Ψ Φ : ℝ → ℝ} {δ z : ℝ} (hδ : 0 < δ)
    (hΨ : ∀ t : ℝ, ‖Ψ t‖ ≤ Φ t)
    (hΦ : Integrable (fun t : ℝ => sKer δ (Real.log z - t) * Φ t) volume) :
    ‖∫ t : ℝ, sKer δ (Real.log z - t) * Ψ t‖
      ≤ ∫ t : ℝ, sKer δ (Real.log z - t) * Φ t := by
  calc ‖∫ t : ℝ, sKer δ (Real.log z - t) * Ψ t‖
      ≤ ∫ t : ℝ, ‖sKer δ (Real.log z - t) * Ψ t‖ :=
        MeasureTheory.norm_integral_le_integral_norm _
    _ = ∫ t : ℝ, sKer δ (Real.log z - t) * ‖Ψ t‖ := by
        refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
        beta_reduce
        rw [norm_mul, Real.norm_of_nonneg (sKer_nonneg hδ _)]
    _ ≤ ∫ t : ℝ, sKer δ (Real.log z - t) * Φ t := by
        refine MeasureTheory.integral_mono_of_nonneg
          (Filter.Eventually.of_forall fun t =>
            mul_nonneg (sKer_nonneg hδ _) (norm_nonneg _)) hΦ
          (Filter.Eventually.of_forall fun t =>
            mul_le_mul_of_nonneg_left (hΨ t) (sKer_nonneg hδ _))

/-- **Pointwise domination of the `D_z²`-slot of the log-mollified datum.**

For `G` in the trace class (`TraceClass`) with honest functionals (`FourInts`), `δ, ε ∈ (0,1/2]`,
put `Φ := zmoll G δ ε`.  Then for a.e. `z > 0` and every `θ ∈ Iθ` the second `D_z`-derivative of
`Φ` is dominated by the doubly-odd-mollified `D_z²G`:

  `|D_z²Φ(z,θ)| ≤ ∫_t sKer δ (log z - t) (∫_s KJ ε θ s |D_z²G (e^t) s| ds) dt`,

where `KJ ε θ s = sKer ε (θ-s) + sKer ε (θ+s) + sKer ε (θ+s-π)`.

Intended route.  (i) *θ-fold*, a.e. in `w`:
`D_z^j (thMoll G ε) w θ = ∫_{Iθ} km ε θ s · D_z^j G w s ds` for `j ≤ 2`, where
`km ε θ s = sKer ε (θ-s) - sKer ε (θ+s) - sKer ε (θ+s-π)` (this is `D_z^j` of the folded
representation `thMoll G ε w θ = ∫_{Iθ} km ε θ s G w s ds`; the joint integrability needed for
the Fubini argument, `∫_{a}^{b}∫_{Iθ}|D_z^j G| < ∞` for `0 < a ≤ b`, follows from `SliceHonestOpen G`
and `FourInts G` by Cauchy–Schwarz in `θ` against `σ^{-1} = sin(2·)^{2η} ∈ L¹(Iθ)`).
(ii) *log-mollification commutation*, a.e. in `z`:
`D_z^j (zmoll G δ ε) z θ = ∫_t sKer δ (log z - t) · D_z^j (thMoll G ε) (e^t) θ dt` for `j ≤ 2`
(substitute `t = log z - u` and integrate by parts in `u`; all boundary terms vanish because
`sKer δ` has compact support).
(iii) *glue*: the failure set of (i) is null, and the `t`-kernel has compact support, so the two
`t`-integrals agree for a.e. `z`; `|km| ≤ KJ` gives the stated bound.  Every `t`- and
`s`-integral is finite for every `z > 0` because the window `[z e^{-δ}, z e^{δ}]` is compact in
`(0,∞)` and the box integrability of (i) applies there.

Sources to reuse: `Work.FTS.EllSol.EllPkgAux.thMoll_abs_le` (the `j = 0` fold), `KJ`,
`KJ_nonneg`, `KJ_le`, `KJ_mass`, `integrableOn_sq_of_integrableOn`. -/
theorem zmoll_ddDom (G : ℝ → ℝ → ℝ) (hT : Work.FTS.EllSol.EllPkgAux.TraceClass G)
    (hF : Work.FTS.EllSol.EllPkgAux.FourInts G) (δ ε : ℝ)
    (hP : Work.FTS.EllSol.EllPkgAux.Params δ ε) :
    ∀ᵐ z ∂(MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))),
      ∀ θ ∈ Work.Spaces.Iθ,
        |Work.Spaces.Dz (Work.Spaces.Dz (Work.FTS.EllSol.PkgK5.K5c.zmoll G δ ε)) z θ|
          ≤ ∫ t : ℝ, Work.FTS.EllSol.PkgK5.K5c.sKer δ (Real.log z - t) *
              (∫ s in Work.Spaces.Iθ,
                Work.FTS.EllSol.EllPkgAux.KJ ε θ s *
                |Work.Spaces.Dz (Work.Spaces.Dz G) (Real.exp t) s|) := by
  have hε0 : (0 : ℝ) < ε := hP.1
  have hδ0 : (0 : ℝ) < δ := hP.2.2.1
  obtain ⟨-, -, -, -, -, -, hsd7⟩ := slice_data hT
  rw [MeasureTheory.ae_restrict_iff' measurableSet_Ioi]
  refine Filter.Eventually.of_forall fun z hz => ?_
  intro θ hθ
  have hid := zmoll_dz2_eq G hT hF δ ε hP z hz θ hθ
  have hmain := znorm_le (Ψ := fun t : ℝ => ∫ s in Iθ,
        Work.FTS.EllSol.EllPkgAux.Kern (sKer ε) θ s * Dz (Dz G) (Real.exp t) s)
    (Φ := fun t : ℝ => ∫ s in Iθ,
        Work.FTS.EllSol.EllPkgAux.KJ ε θ s * ‖Dz (Dz G) (Real.exp t) s‖) hδ0
    (fun t => Kern_integral_le hε0 (hsd7 (Real.exp t) (Real.exp_pos t)))
    (KJ_ddG_integrable_mine hT hF hδ0 hP.2.2.2 hε0 hP.2.1 hz)
  rw [hid]
  exact hmain

end Work.FTS.EllSol.EllPkgAux.MollDom
