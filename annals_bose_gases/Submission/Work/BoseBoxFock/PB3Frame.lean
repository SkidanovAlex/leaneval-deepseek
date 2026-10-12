import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseBoxFock.chiMf_contDiff
import Submission.Work.BoseBoxFock.chiMf_memLp
import Submission.Work.BoseBoxFock.chiMf_tsupport_subset
import Submission.Work.BoseBoxFock.qVec_overlap_eq_kinFT_L2
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.PB3Frame` — the frame of the localised `pinQInf` modes

The localised modes `pinQInf ℓ k = (√ℓ³)⁻¹ Q(χ_ℓ e^{i⟪κ_k,·⟫})` (`κ_k = kappaL ℓ k`) are the
frame of the mean-free part of `L²(boxL ℓ)`.  This file proves the three facts the block-III
(`pairRowB3`) comparison uses:

* `pinQInf_inner_eq` — the pairing of `pinQInf ℓ k` against `f ∈ L²` is the `p`-convention
  Fourier transform of the windowed mean-free part `χ_ℓ · mf ℓ f`, sampled at `κ_k`
  (up to the normalisation `(√ℓ³)⁻¹`);
* the **Parseval identity** `HasSum (k ↦ ‖⟪pinQInf k, f⟫‖²) (∫ χ_ℓ²‖mf ℓ f‖²)` (the frame is
  tight; this is the `L²` aliasing identity `hasSum_kinFT_lattice_L2` at scale `ℓ` read through
  the dictionary above);
* the **high-mode tail bound**: restricting to the lattice momenta of norm `≥ Λ` costs `Λ⁻²`
  (`L1Tails.highModeTail` read through the same dictionary).

The only new ingredient is `qVec_overlap_eq_kinFT_L2` (`Work.BoseBoxFock`), the `L²` version of the
`qVec`-overlap identity, together with the bookkeeping lemmas about `χ_ℓ · mf ℓ f`
(`chiMf_memLp`, `chiMf_tsupport_subset`, `chiMf_contDiff`).
-/

namespace Work.BoseBoxFock

noncomputable section

open scoped BigOperators
open MeasureTheory

local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "boxL" => Work.BoseK15.corpusBox.boxL

/-- `χ_Λ · (Q u) = χ_Λ · (mf u)`: the two spellings of the windowed mean-free part agree
(the box projection of `qVecFrameWeighted.cboxQ` and the mean-free part `PB3Defs.mf`).
Off the box both sides vanish because `χ_Λ` does. -/
theorem chiScale_mul_cboxQ_eq_mf {ℓ : ℝ} (hℓ : 0 < ℓ) (u : E3 → ℂ) (x : E3) :
    ((Submission.BoseGases.chiScale ℓ x : ℝ) : ℂ) * cboxQ ℓ u x
      = ((Submission.BoseGases.chiScale ℓ x : ℝ) : ℂ) * mf ℓ u x := by
  by_cases hx : x ∈ boxL ℓ
  · have hc : ((ℓ : ℂ) ^ 3)⁻¹ * (∫ y in boxL ℓ, u y)
        = (((ℓ ^ 3)⁻¹ : ℝ) : ℂ) * (∫ y in boxL ℓ, u y) := by
      rw [Complex.ofReal_inv, Complex.ofReal_pow]
    simp only [cboxQ, mf, Set.indicator_of_mem hx, mul_one]
    rw [hc]
  · rw [chiScale_eq_zero_of_notMem hℓ hx, Complex.ofReal_zero, zero_mul, zero_mul]

/-- **The `pinQInf`-`kinFT` dictionary**: the pairing of the localised mode `pinQInf ℓ k` against
`f ∈ L²` is `(√ℓ³)⁻¹` times the Fourier sample of the windowed mean-free part. -/
theorem pinQInf_inner_eq {ℓ : ℝ} (hℓ : 0 < ℓ) {f : E3 → ℂ}
    (hf : MemLp f 2 (volume : Measure E3)) (k : Fin 3 → ℤ) :
    (∫ x : E3, (starRingEnd ℂ) (pinQInf ℓ k x) * f x)
      = ((Real.sqrt (ℓ ^ 3))⁻¹ : ℝ)
          * Submission.BoseGases.kinFT (fun x => ((Submission.BoseGases.chiScale ℓ x : ℝ) : ℂ)
              * mf ℓ f x) (kappaL ℓ k) := by
  have hA := qVec_overlap_eq_kinFT_L2 (ℓ := ℓ) hℓ (k := kappaL ℓ k) hf
  have hL : (∫ x : E3, (starRingEnd ℂ) (pinQInf ℓ k x) * f x)
      = (((Real.sqrt (ℓ ^ 3))⁻¹ : ℝ) : ℂ)
          * (∫ x : E3,
              (starRingEnd ℂ) (Work.BoseK15.corpusBox.qVec ℓ (kappaL ℓ k) x) * f x) := by
    rw [show (∫ x : E3, (starRingEnd ℂ) (pinQInf ℓ k x) * f x)
        = ∫ x : E3, (((Real.sqrt (ℓ ^ 3))⁻¹ : ℝ) : ℂ)
            * ((starRingEnd ℂ) (Work.BoseK15.corpusBox.qVec ℓ (kappaL ℓ k) x) * f x) from
      integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)]
    · rw [integral_const_mul]
    · simp only [pinQInf, map_mul, Complex.conj_ofReal]
      ring
  rw [hL, hA]
  have hfun : (fun z : E3 => ((Submission.BoseGases.chiScale ℓ z : ℝ) : ℂ) * cboxQ ℓ f z)
      = (fun z : E3 => ((Submission.BoseGases.chiScale ℓ z : ℝ) : ℂ) * mf ℓ f z) :=
    funext fun z => chiScale_mul_cboxQ_eq_mf hℓ f z
  rw [hfun]

/-- The **squared** form of the dictionary: `‖⟪pinQInf ℓ k, f⟫‖² = ℓ⁻³‖ĝ(κ_k)‖²` for the
windowed mean-free transform `ĝ` of `f`. -/
theorem norm_pinQInf_inner {ℓ : ℝ} (hℓ : 0 < ℓ) {f : E3 → ℂ}
    (hf : MemLp f 2 (volume : Measure E3)) (k : Fin 3 → ℤ) :
    ‖∫ x : E3, (starRingEnd ℂ) (pinQInf ℓ k x) * f x‖ ^ 2
      = (ℓ ^ 3)⁻¹ * ‖Submission.BoseGases.kinFT
          (fun x : E3 => ((Submission.BoseGases.chiScale ℓ x : ℝ) : ℂ) * mf ℓ f x)
          (kappaL ℓ k)‖ ^ 2 := by
  rw [pinQInf_inner_eq (ℓ := ℓ) hℓ (f := f) hf k, norm_mul, mul_pow]
  have hsc : ‖(((Real.sqrt (ℓ ^ 3))⁻¹ : ℝ) : ℂ)‖ ^ 2 = (ℓ ^ 3)⁻¹ := by
    rw [Complex.sq_norm, Complex.normSq_ofReal, ← sq, inv_pow, Real.sq_sqrt (by positivity)]
  rw [hsc]

theorem PB3Frame {ℓ : ℝ} (hℓ : 0 < ℓ) {f : EuclideanSpace ℝ (Fin 3) → ℂ}
    (hf : MeasureTheory.MemLp f 2 (MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin 3))))
    (k : Fin 3 → ℤ) :
    (∫ x : EuclideanSpace ℝ (Fin 3), (starRingEnd ℂ) (Work.BoseBoxFock.pinQInf ℓ k x) * f x)
      = ((Real.sqrt (ℓ ^ 3))⁻¹ : ℝ)
          * Submission.BoseGases.kinFT (fun x => ((Submission.BoseGases.chiScale ℓ x : ℝ) : ℂ)
              * Work.BoseBoxFock.mf ℓ f x) (Work.BoseBoxFock.kappaL ℓ k)
    ∧ (HasSum (fun k : Fin 3 → ℤ => ‖∫ x : EuclideanSpace ℝ (Fin 3), (starRingEnd ℂ) (Work.BoseBoxFock.pinQInf ℓ k x) * f x‖ ^ 2)
        (∫ x : EuclideanSpace ℝ (Fin 3), (Submission.BoseGases.chiScale ℓ x) ^ 2 * ‖Work.BoseBoxFock.mf ℓ f x‖ ^ 2))
    ∧ (∀ {Λ : ℝ}, 0 < Λ → ∀ (g : EuclideanSpace ℝ (Fin 3) → ℂ), ContDiff ℝ 1 g →
        tsupport g ⊆ Work.BoseK15.corpusBox.boxL ℓ → ∀ (S : Finset (Fin 3 → ℤ)),
        (∀ k ∈ S, Λ ≤ ‖Work.BoseBoxFock.kappaL ℓ k‖) →
        ∑ k ∈ S, ‖∫ x : EuclideanSpace ℝ (Fin 3), (starRingEnd ℂ) (Work.BoseBoxFock.pinQInf ℓ k x) * g x‖ ^ 2
          ≤ Λ⁻¹ ^ 2 * (((2 * Real.pi) ^ 3)⁻¹ * ∫ p : EuclideanSpace ℝ (Fin 3), ‖p‖ ^ 2 *
              ‖Submission.BoseGases.kinFT (fun x => ((Submission.BoseGases.chiScale ℓ x : ℝ) : ℂ)
                  * Work.BoseBoxFock.mf ℓ g x) p‖ ^ 2)) := by
  refine ⟨pinQInf_inner_eq (ℓ := ℓ) hℓ (f := f) hf k, ?_, ?_⟩
  · -- the tight-frame (Parseval) identity
    set g : E3 → ℂ := fun x => ((Submission.BoseGases.chiScale ℓ x : ℝ) : ℂ) * mf ℓ f x with hgdef
    have hmem : MeasureTheory.MemLp g 2 (MeasureTheory.volume : MeasureTheory.Measure E3) :=
      chiMf_memLp (ℓ := ℓ) hℓ (f := f) hf
    have hts : tsupport g ⊆ boxL ℓ := chiMf_tsupport_subset (ℓ := ℓ) hℓ f
    have hbase : HasSum (fun n : Fin 3 → ℤ => ‖Submission.BoseGases.kinFT g (kmomInt ℓ n)‖ ^ 2)
        (ℓ ^ 3 * ∫ x : E3, ‖g x‖ ^ 2) := hasSum_kinFT_lattice_L2 (μ := ℓ) hℓ hmem hts
    have hmain := hbase.mul_left ((ℓ ^ 3)⁻¹)
    have hpt : ∀ x : E3, ‖g x‖ ^ 2
        = (Submission.BoseGases.chiScale ℓ x) ^ 2 * ‖mf ℓ f x‖ ^ 2 := by
      intro x
      simp only [hgdef]
      rw [norm_mul, mul_pow, Complex.sq_norm, Complex.normSq_ofReal]
      ring
    have hsum : (ℓ ^ 3)⁻¹ * (ℓ ^ 3 * ∫ x : E3, ‖g x‖ ^ 2)
        = ∫ x : E3, (Submission.BoseGases.chiScale ℓ x) ^ 2 * ‖mf ℓ f x‖ ^ 2 := by
      rw [← mul_assoc, inv_mul_cancel₀ (pow_ne_zero 3 (ne_of_gt hℓ)), one_mul]
      exact integral_congr_ae (Filter.Eventually.of_forall hpt)
    rw [← hsum]
    exact hmain.congr_fun (fun k => by
      simpa only [hgdef] using norm_pinQInf_inner (ℓ := ℓ) hℓ (f := f) hf k)
  · -- the high-mode tail bound
    intro Λ hΛ g hgc hgsupp S hS
    have hcs : HasCompactSupport g :=
      IsCompact.of_isClosed_subset (Work.BoseB4.BoxData.boxL_compact Work.BoseK15.corpusBox ℓ)
        (isClosed_tsupport g) hgsupp
    have hmemg : MeasureTheory.MemLp g 2 (MeasureTheory.volume : MeasureTheory.Measure E3) :=
      hgc.continuous.memLp_of_hasCompactSupport hcs
    set gg : E3 → ℂ := fun x => ((Submission.BoseGases.chiScale ℓ x : ℝ) : ℂ) * mf ℓ g x with hggdef
    have hmemgg : MeasureTheory.MemLp gg 2 (MeasureTheory.volume : MeasureTheory.Measure E3) :=
      chiMf_memLp (ℓ := ℓ) hℓ (f := g) hmemg
    have htsgg : tsupport gg ⊆ boxL ℓ := chiMf_tsupport_subset (ℓ := ℓ) hℓ g
    have hcdgg : ContDiff ℝ 1 gg := chiMf_contDiff (ℓ := ℓ) hℓ (g := g) hgc
    have htail := L1Tails.highModeTail (ℓ := ℓ) (Λ := Λ) hℓ hΛ hcdgg htsgg S hS
    have hpt : ∀ k : Fin 3 → ℤ,
        ‖∫ x : E3, (starRingEnd ℂ) (pinQInf ℓ k x) * g x‖ ^ 2
          = (ℓ ^ 3)⁻¹ * ‖Submission.BoseGases.kinFT gg (kappaL ℓ k)‖ ^ 2 :=
      fun k => norm_pinQInf_inner (ℓ := ℓ) hℓ (f := g) hmemg k
    calc ∑ k ∈ S, ‖∫ x : E3, (starRingEnd ℂ) (pinQInf ℓ k x) * g x‖ ^ 2
        = ∑ k ∈ S, (ℓ ^ 3)⁻¹ * ‖Submission.BoseGases.kinFT gg (kappaL ℓ k)‖ ^ 2 :=
          Finset.sum_congr rfl (fun k _ => hpt k)
      _ = (ℓ ^ 3)⁻¹ * ∑ k ∈ S, ‖Submission.BoseGases.kinFT gg (kappaL ℓ k)‖ ^ 2 :=
          (Finset.mul_sum S (fun k => ‖Submission.BoseGases.kinFT gg (kappaL ℓ k)‖ ^ 2)
            ((ℓ ^ 3)⁻¹)).symm
      _ ≤ (ℓ ^ 3)⁻¹ * (ℓ ^ 3 / Λ ^ 2 * (((2 * Real.pi) ^ 3)⁻¹
            * ∫ p : E3, ‖p‖ ^ 2 * ‖Submission.BoseGases.kinFT gg p‖ ^ 2)) :=
          mul_le_mul_of_nonneg_left htail (by positivity)
      _ = Λ⁻¹ ^ 2 * (((2 * Real.pi) ^ 3)⁻¹
            * ∫ p : E3, ‖p‖ ^ 2 * ‖Submission.BoseGases.kinFT gg p‖ ^ 2) := by
          have hℓ0 : ℓ ≠ 0 := ne_of_gt hℓ
          have hΛ0 : Λ ≠ 0 := ne_of_gt hΛ
          field_simp

end

end Work.BoseBoxFock
