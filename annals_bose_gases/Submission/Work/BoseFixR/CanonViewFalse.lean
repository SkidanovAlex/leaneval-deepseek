import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseFixR.Canon
import Submission.Work.BoseFixR.FamForm.sideAt_d_powers
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission/Work/BoseFixR/CanonViewFalse.lean` — record of the `χ̂`-normalisation obstruction (**repaired**)

This module was created by the `RB5Canon` child as the refutation of the first
version of the canonical view `RView`; that obstruction has since been **repaired
by the lead** in `Defs.lean` (19:41) and `Canon.lean` (19:48), both citing it, so
only the reusable evaluations and the record are kept here.  Everything in this
file is sorry-free and axiom-clean.

## The obstruction that was found (now repaired)

The first `RView` pinned the mode-indexed `χ̂`-kernels to the Fourier transforms of
the **`ℓ`-scaled** localisation,

```
E.hatChi   k = chat (chiFun ℓ) (F.kmom k),
E.hatChiSq k = chat (chiFun ℓ ^ 2) (F.kmom k)      (chiFun ℓ = chiScale ℓ)
```

whose value at the condensate mode `k = 0` (`kmom_zero` below; `F.kmom 0 = 0` is
forced by `kmom_neg`) is `∫χ_ℓ² = ℓ³` (`integral_chiScale_sq`, `chat_chiSq_zero`).
Since the same view carries the kernel interface's field

```
hatChiSq_le : ∀ s, |E.hatChiSq s| ≤ 1        (no guard: s = 0 included)
```

the view *forced* `ℓ(μ)³ ≤ 1`, i.e. `(sideAt μ (a v))³ ≤ 1`, which contradicts
`ℓ(μ) = a·(μa³)^{-163/323} > 1` in the whole diluteness regime
`t = μa³ < a^{323/163}` (`one_lt_sideAt_of_dil_le`).  So the view was empty in
exactly FS's regime, which made the canonical residuals vacuous (`RB5Canon`,
`RB67Canon`) or false (`RB4box`, whose view conjunct is demanded for every
admissible `μ`, hence `RB4boxExistsV2`).  The identification of the pins as `ℓ³`
times the **unit-cell** kernels — the ones `KzKernels`, `Work.BoseK15.K15Input`
(`hatChi_eq`, `hatChiSq_eq`, `ccrX_eq`), the *proved* `Work.BoseK15.hatChi_le_one`
and the honest B4 instance (`Work.BoseB4.ccrKernel`) all use, cf. the corpus's own
`Work.BoseB4.BoxData.integral_chiLam_sq_mul_cos`
(`∫ (chiLam ℓ)² cos⟨p,·⟩ = ℓ³ · corpusBox.hatChiSq (ℓ • p)`) — was reported in
`FINDING_canon_view_uninhabited.md`.

**Fix applied by the lead:** both `RView` and `KzEnvFs` now pin the *normalised*
kernels

```
E.hatChiSq k = chat (χ_ℓ²) (F.kmom k) / chat (χ_ℓ²) 0        (and the same for χ̂),
```

whose condensate-mode value is `1`.  With that, the view is no longer refuted by
the argument above, and `RB5` at the canonical family (`RB5Canon`) is a **genuine**
obligation — FS §9 `lem:Roughbounds`/`prop:FarAway` on FS's data, see
`Submission/Work/BoseFixR/RB5Canon_DESIGN.md`.

## Contents (reusable)

* `kmom_zero` — the condensate momentum is `0`;
* `integral_chiScale_sq` — `∫ χ_ℓ² = ℓ³`;
* `chat_chiSq_zero` — `chat (χ_ℓ²) 0 = ℓ³`;
* `one_lt_sideAt_of_dil_le` — `μa³ ≤ a^{323/163}/2 ⟹ 1 < ℓ(μ)`.
-/

namespace Work.BoseFixR

open MeasureTheory Filter Metric
open scoped Real Topology BigOperators

open _root_.BoseGases Submission.BoseGases Work.UBB Work.BoseBox Work.BoseBoxFix

set_option autoImplicit false

/-- The momentum label of the condensate mode is `0` (`kmom_neg` at `i = 0`). -/
lemma kmom_zero {Mode : Type*} [AddCommGroup Mode] [Fintype Mode] [DecidableEq Mode]
    (F : Work.BoseB7.FockData Mode) : F.kmom (0 : Mode) = 0 := by
  have h0 := F.kmom_neg 0
  simp only [neg_zero] at h0
  have h2 : (2 : ℝ) • F.kmom 0 = 0 := by
    rw [two_smul]
    nth_rewrite 2 [h0]
    rw [add_neg_cancel]
  simpa using h2

/-- `∫ χ_ℓ² = ℓ³` (the `ℓ`-scaled localisation; `∫χ² = 1`, `CubicChi.chi_L2`).
This is also `Work.BoseB4.BoxData.integral_chiLam_sq` for `corpusBox`. -/
lemma integral_chiScale_sq {ℓ : ℝ} (hℓ : 0 < ℓ) :
    (∫ x : EuclideanSpace ℝ (Fin 3), (chiScale ℓ x) ^ 2) = ℓ ^ 3 := by
  have hh := Submission.BoseGases.integral_pair_scale (ℓ := ℓ) hℓ 0
  simp only [sub_zero] at hh
  have hcv : convScale ℓ (0 : EuclideanSpace ℝ (Fin 3)) = 1 := by
    simp [convScale, Submission.BoseGases.conv3_at_zero]
  rw [hcv, mul_one] at hh
  rw [← hh]
  refine integral_congr_ae (Filter.Eventually.of_forall (fun x => ?_))
  ring

/-- **`chat (χ_ℓ²) 0 = ℓ³`**: the unnormalised `χ̂²` at the condensate mode.  This is
the value whose collision with the interface field
`hatChiSq_le : ∀ s, |E.hatChiSq s| ≤ 1` forced the normalisation of the pins. -/
lemma chat_chiSq_zero {ℓ : ℝ} (hℓ : 0 < ℓ) :
    chat (fun z : EuclideanSpace ℝ (Fin 3) => chiFun ℓ z ^ 2) 0 = ℓ ^ 3 := by
  have hint := integral_chiScale_sq hℓ
  simp only [chat, kinFT, inner_zero_left, Complex.ofReal_zero, mul_zero, neg_zero,
    Complex.exp_zero, one_mul, chiFun]
  have h1 : (∫ y : EuclideanSpace ℝ (Fin 3), ((chiScale ℓ y ^ 2 : ℝ) : ℂ))
      = ((∫ y : EuclideanSpace ℝ (Fin 3), chiScale ℓ y ^ 2 : ℝ) : ℂ) := integral_ofReal
  rw [h1, Complex.ofReal_re, hint]

/-- `ℓ(μ) = a·(μa³)^{-163/323}` (`FamForm.sideAt_eq`), so `ℓ(μ) > 1` as soon as
the diluteness `t = μa³` is below `a^{323/163}`. -/
lemma one_lt_sideAt_of_dil_le {μ a : ℝ} (hμ : 0 < μ) (ha : 0 < a)
    (h : μ * a ^ 3 ≤ a ^ (323 / 163 : ℝ) / 2) : 1 < sideAt μ a := by
  have ht : 0 < μ * a ^ 3 := by positivity
  have hlt : μ * a ^ 3 < a ^ (323 / 163 : ℝ) := by
    have hp : 0 < a ^ (323 / 163 : ℝ) := Real.rpow_pos_of_pos ha _
    linarith
  have key : (μ * a ^ 3) ^ (163 / 323 : ℝ) < a := by
    have h1 := Real.rpow_lt_rpow ht.le hlt (by norm_num : (0 : ℝ) < 163 / 323)
    have h2 : (a ^ (323 / 163 : ℝ)) ^ (163 / 323 : ℝ) = a := by
      rw [← Real.rpow_mul ha.le]
      rw [show (323 / 163 : ℝ) * (163 / 323) = 1 by norm_num, Real.rpow_one]
    rwa [h2] at h1
  have hpos : 0 < (μ * a ^ 3) ^ (163 / 323 : ℝ) := Real.rpow_pos_of_pos ht _
  have hdiv : 1 < a / (μ * a ^ 3) ^ (163 / 323 : ℝ) := by
    rw [one_lt_div hpos]
    exact key
  calc (1 : ℝ) < a / (μ * a ^ 3) ^ (163 / 323 : ℝ) := hdiv
    _ = sideAt μ a := by
        rw [Work.BoseFixR.FamForm.sideAt_eq hμ ha, Real.rpow_neg ht.le, ← div_eq_mul_inv]

end Work.BoseFixR
