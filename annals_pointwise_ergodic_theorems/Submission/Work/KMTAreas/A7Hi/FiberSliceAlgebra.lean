import Mathlib
import Submission.Work.KMTAreas.A7.fiberVarSamplingLargeLossAuxBdd
import Submission.Work.KMTAreas.A7.fourier_cwR_band
import Submission.Work.KMTAreas.A7.sublatticeCosetCompareBdd

/-!
# The slice algebra of the `g`-side fibre with the concrete wide bump `mStargF d U`

Steps (1), (2) and (4) of the fibre-variational-sampling route
(`Submission/Work/KMTAreas/A7Hi/FiberVarSamplingGLargeFinite.lean`), specialised to the concrete
wide bump `mStargF d U` and an arbitrary **bounded** family `u`:

* step (1): on the residue class `r` mod `q` (with `q • α = 0` for every exact-height frequency
  `α ∈ iwArithFreqsNew ρ l₂`), the fibre `fiberOp ρ l₂ (mStargF d U) M` is the carrier-free slice
  `sliceSumm` of index `M - r` (untwisted form, and the target's twisted form with `M = P.eval n₀`);
* step (2): the slice is the convolution of the bounded family `sliceInput A u y` with the
  near-`0`-band kernel `cw (mStargF d U)`;
* step (4): on the matching coset `qℤ + (r - M)` the slice of index `M - r` is the *cut*
  `fiberOp ρ l₂ (mStargF d U) 0`.

The boundedness hypothesis is exactly what the target's finiteness hypothesis
`eLpNorm (Vʳ (Gcl …)) p count < ⊤` supplies (see the docstring of the target file): it is what
makes the defining `tsum`s junk-free although the input `g` of `Tex` need not be bounded.
-/

namespace Work.KMTAreas.A7Hi

open MeasureTheory
open scoped FourierTransform

noncomputable section

/-! ## Steps (1), (2), (4) of the route: the slice algebra of the concrete family

These are the mechanical specialisations of the proved lemmas `A7.fiberOp_residue_eq_slice` and
`A7.sliceSumm_eq_conv` (module `Submission.Work.KMTAreas.A7.fiberVarSamplingLargeLossAuxBdd`) to
this target's data: the *twisted* fibre `fiberOpP` with the concrete wide bump `mStargF d U` and an
arbitrary **bounded** family `u` (the boundedness is what the target's finiteness hypothesis
supplies, see the note above). -/

open MeasureTheory in
/-- The `cw`-coefficients of the wide fibre bump `mStargF d U` are summable: it is the `C²`
compactly supported cutoff `etaCut kmtEta (-(2dU))`, whose Fourier coefficients decay quadratically
(`A7.cw_etaCut_decay`). -/
theorem summable_cw_mStargF_fin (d U : ℕ) :
    Summable (fun j : ℤ => ‖Work.KMTAreas.A7.cw (Work.KMTAreas.A7.mStargF d U) j‖) := by
  obtain ⟨C, _hC, hC⟩ := Work.KMTAreas.A7.cw_etaCut_decay (-((d : ℤ) * 2 * (U : ℤ)))
  refine Work.KMTContract.kernel_l1_of_decay (C := C) (fun j => ?_)
  simpa only [Work.KMTAreas.A7.mStargF] using hC j

/-- **Step (1) (untwisted form, arbitrary shift).**  On the residue class `r` modulo `q` (with
`q • α = 0` for every exact-height frequency `α`), the fibre with the wide bump `mStargF d U` at
shift `M` is the carrier-free slice of index `M - r`. -/
theorem fiberOp_mStargF_residue_eq_slice (ρ : ℝ) (l₂ d U q : ℕ) (u : ℤ → ℂ) (B : ℝ)
    (hB : ∀ x : ℤ, ‖u x‖ ≤ B)
    (hq : ∀ α ∈ Work.Analysis.IonescuWainger.iwArithFreqsNew ρ l₂, q • α = 0)
    (M r z : ℤ) :
    Work.KMTAreas.A7.fiberOp ρ l₂ (Work.KMTAreas.A7.mStargF d U) M u (q * z + r)
      = Work.KMTAreas.A7.sliceSumm (Work.Analysis.IonescuWainger.iwArithFreqsNew ρ l₂)
          (Work.KMTAreas.A7.mStargF d U) u (M - r) (q * z + r) :=
  Work.KMTAreas.A7.fiberOp_residue_eq_slice ρ l₂ (Work.KMTAreas.A7.mStargF d U) q
    (summable_cw_mStargF_fin d U) u B hB hq M r z

/-- **Step (1), the target's form.**  `fiberOpP ρ P l₂ (mStargF d U) n₀ = fiberOp ρ l₂ (mStargF d U)
(P.eval n₀)` is definitional, so the twisted fibre is the slice of index `P.eval n₀ - r`. -/
theorem fiberOpP_mStargF_residue_eq_slice (ρ : ℝ) (P : Polynomial ℤ) (l₂ d U q : ℕ)
    (u : ℤ → ℂ) (B : ℝ) (hB : ∀ x : ℤ, ‖u x‖ ≤ B)
    (hq : ∀ α ∈ Work.Analysis.IonescuWainger.iwArithFreqsNew ρ l₂, q • α = 0)
    (n₀ r z : ℤ) :
    Work.KMTAreas.A7.fiberOpP ρ P l₂ (Work.KMTAreas.A7.mStargF d U) n₀ u (q * z + r)
      = Work.KMTAreas.A7.sliceSumm (Work.Analysis.IonescuWainger.iwArithFreqsNew ρ l₂)
          (Work.KMTAreas.A7.mStargF d U) u (P.eval n₀ - r) (q * z + r) :=
  fiberOp_mStargF_residue_eq_slice ρ l₂ d U q u B hB hq (P.eval n₀) r z

/-- **Step (2).**  The slice is a convolution of the *bounded* family `sliceInput A u y` with the
near-`0`-band kernel `cw (mStargF d U)` — the form in which the decimation engine
(`A7.convSublatticeCosetCompareBdd`) consumes it. -/
theorem sliceSumm_mStargF_eq_conv (ρ : ℝ) (l₂ d U : ℕ) (u : ℤ → ℂ) (B : ℝ)
    (hB : ∀ x : ℤ, ‖u x‖ ≤ B) (y z : ℤ) :
    Work.KMTAreas.A7.sliceSumm (Work.Analysis.IonescuWainger.iwArithFreqsNew ρ l₂)
        (Work.KMTAreas.A7.mStargF d U) u y z
      = ∑' j : ℤ, Work.KMTAreas.A7.cw (Work.KMTAreas.A7.mStargF d U) j *
          Work.KMTAreas.A7.sliceInput (Work.Analysis.IonescuWainger.iwArithFreqsNew ρ l₂)
            u y (z - j) :=
  Work.KMTAreas.A7.sliceSumm_eq_conv _ (Work.KMTAreas.A7.mStargF d U)
    (summable_cw_mStargF_fin d U) u B hB y z

/-- **Step (4).**  The *matching coset* `qz + (r - M)`: the slice of index `M - r` there is the
*cut* `fiberOp ρ l₂ (mStargF d U) 0` (the `n₀ = 0` instance of step (1), since
`0 - (r - M) = M - r`).  This is the endpoint that step (5) — the range identity
`fiberOp ρ l₂ (mStargF d U) 0 (u n) = u n` — turns into the input family itself. -/
theorem sliceSumm_mStargF_matching_coset (ρ : ℝ) (l₂ d U q : ℕ) (u : ℤ → ℂ) (B : ℝ)
    (hB : ∀ x : ℤ, ‖u x‖ ≤ B)
    (hq : ∀ α ∈ Work.Analysis.IonescuWainger.iwArithFreqsNew ρ l₂, q • α = 0)
    (M r z : ℤ) :
    Work.KMTAreas.A7.sliceSumm (Work.Analysis.IonescuWainger.iwArithFreqsNew ρ l₂)
        (Work.KMTAreas.A7.mStargF d U) u (M - r) (q * z + (r - M))
      = Work.KMTAreas.A7.fiberOp ρ l₂ (Work.KMTAreas.A7.mStargF d U) 0 u
          (q * z + (r - M)) := by
  rw [fiberOp_mStargF_residue_eq_slice ρ l₂ d U q u B hB hq (0 : ℤ) (r - M) z]
  congr 1
  ring

/-- **Steps (1)+(2) combined**: on the residue class `r` mod `q`, the target's twisted fibre is the
convolution of the bounded family `sliceInput A u (P.eval n₀ - r)` with the near-`0`-band kernel
`cw (mStargF d U)`.  This is the exact form consumed by the decimation engine
`A7.convSublatticeCosetCompareBdd`. -/
theorem fiberOpP_mStargF_eq_sliceConv (ρ : ℝ) (P : Polynomial ℤ) (l₂ d U q : ℕ)
    (u : ℤ → ℂ) (B : ℝ) (hB : ∀ x : ℤ, ‖u x‖ ≤ B)
    (hq : ∀ α ∈ Work.Analysis.IonescuWainger.iwArithFreqsNew ρ l₂, q • α = 0)
    (n₀ r z : ℤ) :
    Work.KMTAreas.A7.fiberOpP ρ P l₂ (Work.KMTAreas.A7.mStargF d U) n₀ u (q * z + r)
      = ∑' j : ℤ, Work.KMTAreas.A7.cw (Work.KMTAreas.A7.mStargF d U) j *
          Work.KMTAreas.A7.sliceInput (Work.Analysis.IonescuWainger.iwArithFreqsNew ρ l₂)
            u (P.eval n₀ - r) (q * z + r - j) := by
  rw [fiberOpP_mStargF_residue_eq_slice ρ P l₂ d U q u B hB hq n₀ r z,
    sliceSumm_mStargF_eq_conv ρ l₂ d U u B hB (P.eval n₀ - r) (q * z + r)]


/-- **The band-`2^{-2dU}` continuous extension of the wide-bump kernel `cw (mStargF d U)`.**

This is the `kext` datum required by the decimation engine `A7.convSublatticeCosetCompareBdd`: an
integrable continuous function whose samples at the integers are the convolution kernel
`j ↦ cw (mStargF d U) j`, and whose Fourier transform is supported in the arc of radius `2^{-2dU}`
(the support of the bump `mStargF d U = etaCut kmtEta (-(2dU))`).  It is
`𝓕 (etaCutSchwartz (-(2dU)))`: the Schwartz model of the bump (`A7.etaCutSchwartz`) makes
integrability and continuity automatic, `cwR_eq_fourier` identifies its samples with `cw`, and
Fourier inversion (`fourier_fourier_eq_neg`) puts the band at the support of the bump. -/
theorem exists_kext_cw_mStargF (d U : ℕ) :
    ∃ kext : ℝ → ℂ, MeasureTheory.Integrable kext ∧ Continuous kext ∧
      (∀ m : ℤ, kext (m : ℝ) = Work.KMTAreas.A7.cw (Work.KMTAreas.A7.mStargF d U) m) ∧
      (∀ ξ : ℝ, ξ ∉ Set.Icc (-((2 : ℝ) ^ (-((d : ℤ) * 2 * (U : ℤ)))))
        ((2 : ℝ) ^ (-((d : ℤ) * 2 * (U : ℤ)))) →
        FourierTransform.fourier kext ξ = 0) := by
  set k : ℤ := -((d : ℤ) * 2 * (U : ℤ)) with hk
  refine ⟨⇑(𝓕 (Work.KMTAreas.A7.etaCutSchwartz k) : SchwartzMap ℝ ℂ), ?_, ?_, ?_, ?_⟩
  · exact (𝓕 (Work.KMTAreas.A7.etaCutSchwartz k)).integrable
  · exact (𝓕 (Work.KMTAreas.A7.etaCutSchwartz k)).continuous
  · intro m
    rw [SchwartzMap.fourier_coe,
      ← Work.KMTAreas.A7.cwR_eq_fourier (Work.KMTAreas.A7.etaCutSchwartz k) (m : ℝ)]
    rw [Work.KMTAreas.A7.etaCutSchwartz_coe]
    simp only [Work.KMTAreas.A7.cw, Work.KMTAreas.A7.mStargF, hk, neg_mul]
  · intro ξ hξ
    rw [SchwartzMap.fourier_coe, Work.KMTAreas.A7.fourier_fourier_eq_neg]
    rw [Work.KMTAreas.A7.etaCutSchwartz_coe]
    refine Work.KMTAreas.A7.etaCut_eq_zero_of_le ?_
    by_contra hcon
    rw [not_le, abs_neg] at hcon
    exact hξ (Set.mem_Icc.mpr ⟨by linarith [neg_abs_le ξ, hcon.le],
      by linarith [le_abs_self ξ, hcon.le]⟩)


/-- The pointwise bound on the carrier-free slice input: `‖sliceInput A u y z‖ ≤ B · #A`. -/
theorem norm_sliceInput_le (A : Finset Work.Analysis.IonescuWainger.Circle) (u : ℤ → ℂ) (B : ℝ)
    (hB : ∀ x : ℤ, ‖u x‖ ≤ B) (y z : ℤ) :
    ‖Work.KMTAreas.A7.sliceInput A u y z‖ ≤ B * (A.card : ℝ) := by
  have hB0 : (0 : ℝ) ≤ B := le_trans (norm_nonneg _) (hB 0)
  rw [Work.KMTAreas.A7.sliceInput, norm_mul]
  refine mul_le_mul (hB z) ?_ (by positivity) hB0
  calc ‖∑ α ∈ A, fourier (T := 1) (y + z) α‖
      ≤ ∑ α ∈ A, ‖fourier (T := 1) (y + z) α‖ := norm_sum_le _ _
    _ = ∑ _α ∈ A, (1 : ℝ) := by
        refine Finset.sum_congr rfl (fun α _ => ?_)
        rw [fourier_apply]
        exact _root_.Circle.norm_coe _
    _ = (A.card : ℝ) := by simp

/-- **Step (3)+(4)+(5) of the route, per coset.**  The decimation engine
`A7.convSublatticeCosetCompareBdd` compares the two cosets `qℤ + r₀` and `qℤ + (r₀ - P.eval n₀)`
of the fibre family: the `ℓ^p(Vʳ)`-norm of the target's twisted fibre at residue `n₀` is bounded by
the same norm of the *cut* `fiberOp ρ l₂ (mStargF d U) 0`, which the range hypothesis
`hrange` identifies with the input family `u`.

All the hypotheses consumed by the engine are supplied by `FiberSliceAlgebra` itself:
`exists_kext_cw_mStargF` (the band-`2^{-2dU}` integrable continuous extension of the kernel
`cw (mStargF d U)`), `summable_cw_mStargF_fin`, the slice identities and the pointwise bound
`norm_sliceInput_le`. -/
theorem exists_coset_compare_fibre (ρ : ℝ) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (P : Polynomial ℤ)
    (r : NNReal) (hr : 2 < r) (p : ℝ) (hp : 1 < p)
    (d l₂ U q : ℕ) (hd : 1 ≤ d) (hU : 1 ≤ U) (hq : 0 < q)
    (hband : (2 : ℝ) ^ (-((d : ℤ) * 2 * (U : ℤ))) * (q : ℝ) ≤ 1 / 4)
    (u : ℕ → ℤ → ℂ) (B : ℝ) (hB : ∀ n x, ‖u n x‖ ≤ B)
    (hrange : ∀ n, Work.KMTAreas.A7.fiberOp ρ l₂ (Work.KMTAreas.A7.mStargF d U) 0 (u n) = u n)
    (hqtor : ∀ α ∈ Work.Analysis.IonescuWainger.iwArithFreqsNew ρ l₂, q • α = 0) :
    ∃ C : ℝ, 0 < C ∧ ∀ n₀ r₀ : ℤ,
      (∑' z : ℤ, (PointwiseErgodicTheorems.variationalNorm r (fun n : ℕ =>
          Work.KMTAreas.A7.fiberOpP ρ P l₂ (Work.KMTAreas.A7.mStargF d U) n₀ (u n)
            ((q : ℤ) * z + r₀)))^p)
        ≤ ENNReal.ofReal C *
          (∑' z : ℤ, (PointwiseErgodicTheorems.variationalNorm r (fun n : ℕ =>
            u n ((q : ℤ) * z + (r₀ - P.eval n₀))))^p) := by
  have hr1 : (1 : NNReal) ≤ r := le_of_lt (lt_trans (by norm_num : (1 : NNReal) < 2) hr)
  obtain ⟨Ceng, hCengpos, heng⟩ := Work.KMTAreas.A7.convSublatticeCosetCompareBdd p hp r hr1
  obtain ⟨kext, hkextint, hkextcont, hkextsamp, hkextband⟩ := exists_kext_cw_mStargF d U
  refine ⟨Ceng, hCengpos, ?_⟩
  intro n₀ r₀
  have hβpos : (0 : ℝ) < (2 : ℝ) ^ (-((d : ℤ) * 2 * (U : ℤ))) := by positivity
  have hβq : (2 : ℝ) ^ (-((d : ℤ) * 2 * (U : ℤ))) * (q : ℝ) ≤ 1 / 4 := hband
  set A : Finset Work.Analysis.IonescuWainger.Circle :=
    Work.Analysis.IonescuWainger.iwArithFreqsNew ρ l₂ with hA
  have hbnd : ∀ (n : ℕ) (y z : ℤ), ‖Work.KMTAreas.A7.sliceInput A (u n) y z‖
      ≤ B * (A.card : ℝ) + 1 := fun n y z =>
    le_trans (norm_sliceInput_le A (u n) B (hB n) y z) (le_add_of_nonneg_right zero_le_one)
  have hcomp := heng ((2 : ℝ) ^ (-((d : ℤ) * 2 * (U : ℤ)))) hβpos q hq hβq
      (fun _ : ℕ => fun j : ℤ => Work.KMTAreas.A7.cw (Work.KMTAreas.A7.mStargF d U) j)
      (fun _ : ℕ => kext)
      (fun _ => ⟨hkextint, hkextcont, fun m => hkextsamp m, fun ξ hξ => hkextband ξ hξ⟩)
      (fun _ => summable_cw_mStargF_fin d U)
      (fun n y z => Work.KMTAreas.A7.sliceInput A (u n) y z)
      (B * (A.card : ℝ) + 1) hbnd (P.eval n₀ - r₀) r₀ (r₀ - P.eval n₀)
  have hL : ∀ z : ℤ, PointwiseErgodicTheorems.variationalNorm r (fun n : ℕ =>
        Work.KMTAreas.A7.fiberOpP ρ P l₂ (Work.KMTAreas.A7.mStargF d U) n₀ (u n)
          ((q : ℤ) * z + r₀))
      = PointwiseErgodicTheorems.variationalNorm r (fun n : ℕ => ∑' j : ℤ,
          Work.KMTAreas.A7.cw (Work.KMTAreas.A7.mStargF d U) j *
            Work.KMTAreas.A7.sliceInput A (u n) (P.eval n₀ - r₀) ((q : ℤ) * z + r₀ - j)) := by
    intro z
    refine congrArg (fun v => PointwiseErgodicTheorems.variationalNorm r v) (funext fun n => ?_)
    exact fiberOpP_mStargF_eq_sliceConv ρ P l₂ d U q (u n) B (hB n) hqtor n₀ r₀ z
  have hR : ∀ z : ℤ, PointwiseErgodicTheorems.variationalNorm r (fun n : ℕ => ∑' j : ℤ,
        Work.KMTAreas.A7.cw (Work.KMTAreas.A7.mStargF d U) j *
          Work.KMTAreas.A7.sliceInput A (u n) (P.eval n₀ - r₀)
            ((q : ℤ) * z + (r₀ - P.eval n₀) - j))
      = PointwiseErgodicTheorems.variationalNorm r (fun n : ℕ =>
          u n ((q : ℤ) * z + (r₀ - P.eval n₀))) := by
    intro z
    refine congrArg (fun v => PointwiseErgodicTheorems.variationalNorm r v) (funext fun n => ?_)
    have h1 : P.eval n₀ - r₀ = (0 : ℤ) - (r₀ - P.eval n₀) := by ring
    rw [← sliceSumm_mStargF_eq_conv ρ l₂ d U (u n) B (hB n) (P.eval n₀ - r₀)
      ((q : ℤ) * z + (r₀ - P.eval n₀))]
    rw [h1, show (q : ℤ) * z + (r₀ - P.eval n₀)
        = (q : ℤ) * z + ((r₀ - P.eval n₀) - 0) from by ring,
      sliceSumm_mStargF_matching_coset ρ l₂ d U q (u n) B (hB n) hqtor (0 : ℤ)
        (r₀ - P.eval n₀) z]
    simpa using congrFun (hrange n) ((q : ℤ) * z + (r₀ - P.eval n₀))
  calc (∑' z : ℤ, (PointwiseErgodicTheorems.variationalNorm r (fun n : ℕ =>
          Work.KMTAreas.A7.fiberOpP ρ P l₂ (Work.KMTAreas.A7.mStargF d U) n₀ (u n)
            ((q : ℤ) * z + r₀)))^p)
      = ∑' z : ℤ, (PointwiseErgodicTheorems.variationalNorm r (fun n : ℕ => ∑' j : ℤ,
          Work.KMTAreas.A7.cw (Work.KMTAreas.A7.mStargF d U) j *
            Work.KMTAreas.A7.sliceInput A (u n) (P.eval n₀ - r₀)
              ((q : ℤ) * z + r₀ - j)))^p :=
        tsum_congr (fun z => congrArg (fun v : ENNReal => v ^ p) (hL z))
    _ ≤ ENNReal.ofReal Ceng * ∑' z : ℤ, (PointwiseErgodicTheorems.variationalNorm r
          (fun n : ℕ => ∑' j : ℤ, Work.KMTAreas.A7.cw (Work.KMTAreas.A7.mStargF d U) j *
            Work.KMTAreas.A7.sliceInput A (u n) (P.eval n₀ - r₀)
              ((q : ℤ) * z + (r₀ - P.eval n₀) - j)))^p := hcomp
    _ = ENNReal.ofReal Ceng * ∑' z : ℤ, (PointwiseErgodicTheorems.variationalNorm r
          (fun n : ℕ => u n ((q : ℤ) * z + (r₀ - P.eval n₀))))^p := by
        rw [tsum_congr (fun z => congrArg (fun v : ENNReal => v ^ p) (hR z))]

end

end Work.KMTAreas.A7Hi
