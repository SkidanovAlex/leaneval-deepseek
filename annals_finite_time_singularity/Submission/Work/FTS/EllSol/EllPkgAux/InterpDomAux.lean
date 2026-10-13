/-
# `Work.FTS.EllSol.EllPkgAux.InterpDomAux` — infrastructure for the domination of the
doubly-mollified approximant

The target `Work.FTS.EllSol.EllPkgAux.interpOpenTrace` is proved through the approximant
`Φ := zmoll G δ ε`, whose four weighted functionals must be dominated by those of `G` (the
statement `Work.FTS.EllSol.EllPkgAux.mollDom`).

The route implemented here is:

* **the folded form of the angular mollification.**  For `0 < ε ≤ 1/2` the doubly odd extension
  of a slice is seen by the whole-line convolution only through the three-image kernel
  `Kern (sKer ε) θ s` (`ThMollDefs`), and the *positive* comparison kernel `KJ ε θ s` dominates
  it pointwise (`Kern_abs_le_KJ`).

* **the angular Jensen step** (`kernSlot_jensen`): the *slice* bound

    `∫_{Iθ} σθ(θ) · (∫_{Iθ} Kern (sKer ε) θ s · h s ds)² ≤ K · ∫_{Iθ} h s² σθ s ds`

  with a constant `K` independent of `ε`, mirroring the proof of `thMollSliceL2`.

Nothing here is a statement of the target.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.Topology.Order.ExtendFrom
import Mathlib.Topology.UniformSpace.Uniformizable
import Submission.Work.FTS.EllSol.EllPkgAux.MollBase
import Submission.Work.FTS.EllSol.EllPkgAux.MollFatouAux
import Submission.Work.FTS.EllSol.EllPkgAux.ThMollDefs
import Submission.Work.FTS.EllSol.EllPkgAux.thMollTransfer2
import Submission.Work.FTS.EllSol.EllPkgAux.kernelJensen
import Submission.Work.FTS.EllSol.EllPkgAux.kernelSwap
import Submission.Work.FTS.EllSol.EllPkgAux.logJensen
import Submission.Work.FTS.EllSol.EllPkgAux.MollDzAux.zmollKernel_hasDerivAt

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllSol.EllPkgAux

set_option autoImplicit false
set_option maxHeartbeats 4000000

open Work.FTS.EllSol.PkgK5.K5c

local notation "Iθ" => Work.Spaces.Iθ
local notation "σθ" => Work.FTS.EllipticEst.thEta

/-! ## The folded kernel is dominated by the positive three-image kernel -/

/-- Each of the three summands of the folded kernel `Kern (sKer ε) θ s` is nonnegative, so the
folded kernel is dominated in absolute value by the positive three-image kernel
`KJ ε θ s = sKer ε (θ-s) + sKer ε (θ+s) + sKer ε (θ+s-π)`. -/
theorem Kern_abs_le_KJ {ε : ℝ} (hε : 0 < ε) (θ s : ℝ) :
    |Kern (sKer ε) θ s| ≤ KJ ε θ s := by
  have h1 : 0 ≤ sKer ε (θ - s) := sKer_nonneg hε _
  have h2 : 0 ≤ sKer ε (θ + s) := sKer_nonneg hε _
  have h3 : 0 ≤ sKer ε (θ + s - Real.pi) := sKer_nonneg hε _
  rw [Kern, KJ]
  exact abs_le.mpr ⟨by linarith, by linarith⟩

/-- The folded kernel is bounded on `Iθ × Iθ`. -/
theorem Kern_le_inv {ε : ℝ} (hε : 0 < ε) (θ s : ℝ) :
    |Kern (sKer ε) θ s| ≤ 3 * (ε * sMass)⁻¹ :=
  le_trans (Kern_abs_le_KJ hε θ s) (KJ_le hε θ s)

/-- Joint continuity of the folded kernel. -/
theorem continuous_Kern (ε : ℝ) : Continuous (fun p : ℝ × ℝ => Kern (sKer ε) p.1 p.2) := by
  have hc : Continuous (fun t : ℝ => sKer ε t) := Work.FTS.EllSol.K5cAux.continuous_sKer ε
  have h : (fun p : ℝ × ℝ => Kern (sKer ε) p.1 p.2)
      = fun p : ℝ × ℝ =>
          sKer ε (p.1 - p.2) - sKer ε (p.1 + p.2) - sKer ε (p.1 + p.2 - Real.pi) := by
    funext p
    rw [Kern]
  rw [h]
  exact ((hc.comp (continuous_fst.sub continuous_snd)).sub
    (hc.comp (continuous_fst.add continuous_snd))).sub
    (hc.comp ((continuous_fst.add continuous_snd).sub continuous_const))

/-- Continuity of the folded kernel in the angular variable. -/
theorem continuous_Kern_slice (ε θ : ℝ) : Continuous (fun s : ℝ => Kern (sKer ε) θ s) := by
  have hc : Continuous (fun t : ℝ => sKer ε t) := Work.FTS.EllSol.K5cAux.continuous_sKer ε
  have hfun : (fun s : ℝ => Kern (sKer ε) θ s)
      = fun s : ℝ => sKer ε (θ - s) - sKer ε (θ + s) - sKer ε (θ + s - Real.pi) := by
    funext s
    rw [Kern]
  rw [hfun]
  exact ((hc.comp (continuous_const.sub continuous_id)).sub
    (hc.comp (continuous_const.add continuous_id))).sub
    (hc.comp ((continuous_const.add continuous_id).sub continuous_const))

/-- Continuity of the positive kernel in the angular variable. -/
theorem continuous_KJ_slice (ε θ : ℝ) : Continuous (fun s : ℝ => KJ ε θ s) := by
  have hc : Continuous (fun t : ℝ => sKer ε t) := Work.FTS.EllSol.K5cAux.continuous_sKer ε
  have hfun : (fun s : ℝ => KJ ε θ s)
      = fun s : ℝ => sKer ε (θ - s) + sKer ε (θ + s) + sKer ε (θ + s - Real.pi) := by
    funext s
    rw [KJ]
  rw [hfun]
  exact ((hc.comp (continuous_const.sub continuous_id)).add
    (hc.comp (continuous_const.add continuous_id))).add
    (hc.comp ((continuous_const.add continuous_id).sub continuous_const))

/-- **The folded kernel against a function is dominated by the positive kernel against its
modulus.** -/
theorem abs_kernSlot_le_kjSlot {ε θ : ℝ} (hε : 0 < ε) (h : ℝ → ℝ)
    (hh : MeasureTheory.IntegrableOn h Work.Spaces.Iθ) :
    |∫ s in Work.Spaces.Iθ, Kern (sKer ε) θ s * h s|
      ≤ ∫ s in Work.Spaces.Iθ, KJ ε θ s * |h s| := by
  have hint1 : MeasureTheory.IntegrableOn
      (fun s : ℝ => Kern (sKer ε) θ s * h s) Work.Spaces.Iθ :=
    (MeasureTheory.IntegrableOn.mul_continuousOn hh (continuous_Kern_slice ε θ).continuousOn
      isCompact_Icc).congr_fun (fun s _ => by ring) measurableSet_Icc
  have hint2 : MeasureTheory.IntegrableOn (fun s : ℝ => KJ ε θ s * |h s|) Work.Spaces.Iθ :=
    (MeasureTheory.IntegrableOn.mul_continuousOn hh.abs (continuous_KJ_slice ε θ).continuousOn
      isCompact_Icc).congr_fun (fun s _ => by ring) measurableSet_Icc
  refine le_trans MeasureTheory.abs_integral_le_integral_abs ?_
  refine MeasureTheory.integral_mono_ae hint1.abs hint2 ?_
  filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Icc] with s hs
  rw [abs_mul]
  exact mul_le_mul_of_nonneg_right (Kern_abs_le_KJ hε θ s) (abs_nonneg _)

/-! ## The angular Jensen step for the folded kernel -/

/-- **Angular Jensen step for the folded kernel.**  For every `0 < ε ≤ 1/2` and every function
`h` with `h` and `h² σθ` integrable on `Iθ`,

  `∫_{Iθ} σθ(θ) · (∫_{Iθ} Kern (sKer ε) θ s · h s ds)² ≤ K · ∫_{Iθ} h s² σθ s ds`

with a constant `K` independent of `ε`.  The proof mirrors the one of `thMollSliceL2`: the
folded kernel is dominated by `KJ`, the pointwise Cauchy–Schwarz `KJ_pointwise` together with the
Fubini identity `kernelSwap` handles the double integral, and the Schur bound `KJ_schur_ae` of
`thWeightCmp` finishes. -/
theorem kernSlot_jensen : ∃ K : ℝ, 0 < K ∧ ∀ (h : ℝ → ℝ),
    MeasureTheory.IntegrableOn h Iθ →
    MeasureTheory.IntegrableOn (fun s : ℝ => h s ^ 2 * σθ s) Iθ →
    ∀ ε : ℝ, 0 < ε → ε ≤ 1 / 2 →
    (∫ θ in Iθ, σθ θ * (∫ s in Iθ, Kern (sKer ε) θ s * h s) ^ 2)
      ≤ K * ∫ s in Iθ, h s ^ 2 * σθ s := by
  obtain ⟨K₁, hK₁pos, hK₁⟩ := Work.FTS.EllSol.K5cAux.thWeightCmp
  refine ⟨3 * K₁, by positivity, ?_⟩
  intro h hh hh2 ε hε hε2
  set g : ℝ → ℝ := fun s => |h s| with hgdef
  have hgint : MeasureTheory.IntegrableOn (fun s : ℝ => g s ^ 2 * σθ s) Iθ := by
    rw [hgdef]
    refine hh2.congr_fun (fun s _ => ?_) measurableSet_Icc
    show (h s) ^ 2 * σθ s = |h s| ^ 2 * σθ s
    rw [sq_abs]
  have hg2int : MeasureTheory.IntegrableOn (fun s : ℝ => g s ^ 2) Iθ :=
    integrableOn_sq_of_integrableOn hgint
  obtain ⟨hswap_eq, hswap_i1, hswap_i2⟩ := kernelSwap (g := g) hε hg2int
  have hgint' : MeasureTheory.IntegrableOn g Iθ := by
    rw [hgdef]
    exact hh.abs
  have hA : MeasureTheory.IntegrableOn
      (fun θ : ℝ => 3 * (σθ θ * ∫ s in Iθ, KJ ε θ s * g s ^ 2)) Iθ :=
    hswap_i1.const_mul 3
  have hmono : (∫ θ in Iθ, σθ θ * (∫ s in Iθ, Kern (sKer ε) θ s * h s) ^ 2)
      ≤ ∫ θ in Iθ, 3 * (σθ θ * ∫ s in Iθ, KJ ε θ s * g s ^ 2) := by
    refine MeasureTheory.integral_mono_of_nonneg
      (f := fun θ : ℝ => σθ θ * (∫ s in Iθ, Kern (sKer ε) θ s * h s) ^ 2)
      (g := fun θ : ℝ => 3 * (σθ θ * ∫ s in Iθ, KJ ε θ s * g s ^ 2)) ?_ hA ?_
    · exact MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc
        (fun θ hθ => mul_nonneg (Work.FTS.EllipticEst.thEta_nonneg hθ) (sq_nonneg _))
    · exact MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc (fun θ hθ => by
        have hpt : |∫ s in Iθ, Kern (sKer ε) θ s * h s| ≤ ∫ s in Iθ, KJ ε θ s * g s :=
          abs_kernSlot_le_kjSlot (θ := θ) hε h hh
        have hKg : (∫ s in Iθ, KJ ε θ s * g s) ^ 2 ≤ 3 * ∫ s in Iθ, KJ ε θ s * g s ^ 2 :=
          KJ_pointwise hε hgint hθ
        have habs := abs_le.mp hpt
        have h2 : (∫ s in Iθ, Kern (sKer ε) θ s * h s) ^ 2
            ≤ (∫ s in Iθ, KJ ε θ s * g s) ^ 2 :=
          sq_le_sq' habs.1 habs.2
        have hσ : 0 ≤ σθ θ := Work.FTS.EllipticEst.thEta_nonneg hθ
        calc σθ θ * (∫ s in Iθ, Kern (sKer ε) θ s * h s) ^ 2
            ≤ σθ θ * (∫ s in Iθ, KJ ε θ s * g s) ^ 2 := mul_le_mul_of_nonneg_left h2 hσ
          _ ≤ σθ θ * (3 * ∫ s in Iθ, KJ ε θ s * g s ^ 2) :=
              mul_le_mul_of_nonneg_left hKg hσ
          _ = 3 * (σθ θ * ∫ s in Iθ, KJ ε θ s * g s ^ 2) := by ring)
  have hc1 : (∫ θ in Iθ, 3 * (σθ θ * ∫ s in Iθ, KJ ε θ s * g s ^ 2))
      = 3 * ∫ θ in Iθ, σθ θ * ∫ s in Iθ, KJ ε θ s * g s ^ 2 :=
    MeasureTheory.integral_const_mul 3 _
  have hschur : ∀ᵐ s ∂(volume.restrict Iθ), (∫ θ in Iθ, σθ θ * KJ ε θ s) ≤ K₁ * σθ s :=
    KJ_schur_ae (K₁ := K₁) (ε := ε) (fun u' hu' => hK₁ ε u' hε hε2 hu')
  have hKσ_int : MeasureTheory.IntegrableOn (fun s : ℝ => g s ^ 2 * (K₁ * σθ s)) Iθ :=
    MeasureTheory.Integrable.congr (hgint.const_mul K₁)
      (Filter.Eventually.of_forall (fun s => by
        show K₁ * (g s ^ 2 * σθ s) = g s ^ 2 * (K₁ * σθ s)
        ring))
  have hmono2 : (∫ s in Iθ, g s ^ 2 * (∫ θ in Iθ, σθ θ * KJ ε θ s))
      ≤ ∫ s in Iθ, g s ^ 2 * (K₁ * σθ s) := by
    refine MeasureTheory.integral_mono_ae hswap_i2 hKσ_int ?_
    filter_upwards [hschur] with s hs
    exact mul_le_mul_of_nonneg_left hs (sq_nonneg (g s))
  have hKσ_eq : (∫ s in Iθ, g s ^ 2 * (K₁ * σθ s)) = K₁ * ∫ s in Iθ, g s ^ 2 * σθ s := by
    have he : (fun s : ℝ => g s ^ 2 * (K₁ * σθ s)) = fun s : ℝ => K₁ * (g s ^ 2 * σθ s) := by
      funext s
      ring
    rw [he, MeasureTheory.integral_const_mul]
  calc (∫ θ in Iθ, σθ θ * (∫ s in Iθ, Kern (sKer ε) θ s * h s) ^ 2)
      ≤ ∫ θ in Iθ, 3 * (σθ θ * ∫ s in Iθ, KJ ε θ s * g s ^ 2) := hmono
    _ = 3 * ∫ θ in Iθ, σθ θ * ∫ s in Iθ, KJ ε θ s * g s ^ 2 := hc1
    _ = 3 * ∫ s in Iθ, g s ^ 2 * (∫ θ in Iθ, σθ θ * KJ ε θ s) := by rw [hswap_eq]
    _ ≤ 3 * ∫ s in Iθ, g s ^ 2 * (K₁ * σθ s) :=
          mul_le_mul_of_nonneg_left hmono2 (by norm_num)
    _ = 3 * (K₁ * ∫ s in Iθ, g s ^ 2 * σθ s) := by rw [hKσ_eq]
    _ = (3 * K₁) * ∫ s in Iθ, g s ^ 2 * σθ s := by ring
    _ = (3 * K₁) * ∫ s in Iθ, h s ^ 2 * σθ s := by
        congr 1
        refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun s => ?_))
        simp only [hgdef, sq_abs]

/-! ## Continuity of the angular slice of the datum -/

/-- **The angular slice of a trace-class datum is continuous on the closed interval `Iθ`.**

The interior continuity comes from `SmoothOpen.curry_θ`; the endpoint continuity is the vanishing
of the one-sided *limits* (the trace hypotheses), matched with the endpoint *values*
`G z 0 = 0 = G z (π/2)`.  This is what allows the fold `thMoll_fold` to be applied to the datum. -/
theorem continuousOn_slice_Iθ {G : ℝ → ℝ → ℝ} (hS : Work.FTS.EllipticEst.SmoothOpen G)
    (h0 : ∀ z : ℝ, G z 0 = 0) (hp : ∀ z : ℝ, G z (Real.pi / 2) = 0)
    (ht0 : ∀ z : ℝ, 0 < z → Filter.Tendsto (fun θ : ℝ => G z θ)
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0))
    (ht1 : ∀ z : ℝ, 0 < z → Filter.Tendsto (fun θ : ℝ => G z θ)
      (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds 0)) :
    ∀ z : ℝ, 0 < z → ContinuousOn (fun θ : ℝ => G z θ) Work.Spaces.Iθ := by
  intro z hz
  have hInt : ContinuousOn (fun θ : ℝ => G z θ) (Set.Ioo 0 (Real.pi / 2)) :=
    (hS.curry_θ hz).continuousOn
  have ha : Filter.Tendsto (fun θ : ℝ => G z θ) (𝓝[>] (0 : ℝ)) (𝓝 0) := ht0 z hz
  have hb : Filter.Tendsto (fun θ : ℝ => G z θ) (𝓝[<] (Real.pi / 2)) (𝓝 0) := ht1 z hz
  have hne : (Set.Ioo (0 : ℝ) (Real.pi / 2)).Nonempty :=
    Set.nonempty_Ioo.mpr (by linarith [Real.pi_pos])
  have hExt : ContinuousOn (extendFrom (Set.Ioo (0 : ℝ) (Real.pi / 2)) (fun θ : ℝ => G z θ))
      (Set.Icc (0 : ℝ) (Real.pi / 2)) :=
    continuousOn_Icc_extendFrom_Ioo hInt ha hb
  have hpi2 : (0 : ℝ) < Real.pi / 2 := by linarith [Real.pi_pos]
  have hcl0 : (0 : ℝ) ∈ closure (Set.Ioo (0 : ℝ) (Real.pi / 2)) := by
    rw [closure_Ioo hpi2.ne]
    exact ⟨le_refl 0, le_of_lt hpi2⟩
  have hclπ : (Real.pi / 2) ∈ closure (Set.Ioo (0 : ℝ) (Real.pi / 2)) := by
    rw [closure_Ioo hpi2.ne]
    exact ⟨le_of_lt hpi2, le_refl _⟩
  have ha' : Filter.Tendsto (fun θ : ℝ => G z θ)
      (𝓝[Set.Ioo (0 : ℝ) (Real.pi / 2)] 0) (𝓝 0) := by
    rw [nhdsWithin_Ioo_eq_nhdsGT hpi2]
    exact ha
  have hb' : Filter.Tendsto (fun θ : ℝ => G z θ)
      (𝓝[Set.Ioo (0 : ℝ) (Real.pi / 2)] (Real.pi / 2)) (𝓝 0) := by
    rw [nhdsWithin_Ioo_eq_nhdsLT hpi2]
    exact hb
  rw [Work.Spaces.Iθ]
  refine hExt.congr ?_
  intro θ hθ
  rcases eq_endpoints_or_mem_Ioo_of_mem_Icc hθ with h | h | h
  · subst h
    show G z 0 = extendFrom (Set.Ioo (0 : ℝ) (Real.pi / 2)) (fun θ : ℝ => G z θ) 0
    rw [h0 z]
    exact (extendFrom_eq hcl0 ha').symm
  · subst h
    show G z (Real.pi / 2)
      = extendFrom (Set.Ioo (0 : ℝ) (Real.pi / 2)) (fun θ : ℝ => G z θ) (Real.pi / 2)
    rw [hp z]
    exact (extendFrom_eq hclπ hb').symm
  · exact (extendFrom_extends hInt θ h).symm

/-- The unfolding of `TraceClass` into the hypotheses of `continuousOn_slice_Iθ`. -/
theorem continuousOn_slice_Iθ_of_traceClass {G : ℝ → ℝ → ℝ}
    (hT : Work.FTS.EllSol.EllPkgAux.TraceClass G) :
    ∀ z : ℝ, 0 < z → ContinuousOn (fun θ : ℝ => G z θ) Work.Spaces.Iθ := by
  obtain ⟨hS, h0, hp, ht0, ht1, -, -, -⟩ := hT
  exact continuousOn_slice_Iθ hS h0 hp ht0 ht1

end Work.FTS.EllSol.EllPkgAux
