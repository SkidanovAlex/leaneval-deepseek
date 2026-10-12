import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Data.ZMod.ValMinAbs
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseBoxFock.PB3Frame
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.pinQFinite_bessel` — the truncated Bessel (frame) bound

The finite Bessel inequality for the *truncated* frame of the localised pinned modes
`pinQ v μ N k`, `k : Lab N`:

    Σ_{k : Lab N} ‖⟪pinQ v μ N k, f⟫‖²  ≤  ∫ χ_ℓ² ‖mf ℓ f‖² ,   ℓ = ellH v μ ,

for `f` measurable, bounded and supported in the box `boxL ℓ`.

This is the truncation (`Lab N`, the label cube of the periodic box lattice) of the **tight-frame
(Parseval) identity** `Work.BoseBoxFock.PB3Frame`:  the full lattice series
`Σ'_{k : ℤ³} ‖⟪pinQInf ℓ k, f⟫‖²` *equals* `∫ χ_ℓ²‖mf ℓ f‖²`, so every finite sub-sum is below it.
The three steps are

* `f ∈ L²`: `f` is measurable, bounded and supported in the compact box `boxL ℓ`
  (`HasCompactSupport.memLp_of_bound` with the compactness of `tsupport f`);
* `pinQ v μ N k = pinQInf ℓ (labVec N k)` (`pinQ_eq_pinQInf`), and `labVec N` injects
  `Lab N = (ℤ/(2N+1))³` into `ℤ³` (`ZMod.valMinAbs_inj`), so the `Lab N`-sum is the sub-sum of the
  full series over the image `Finset.univ.image (labVec N)` (`Finset.sum_image`);
* a nonnegative sub-sum of a summable series is `≤` its `tsum` (`Summable.sum_le_tsum`).
-/

namespace Work.BoseBoxFock

open MeasureTheory Filter

theorem pinQFinite_bessel {v : EuclideanSpace ℝ (Fin 3) → ℝ} {μ : ℝ} (N : ℕ)
    {f : EuclideanSpace ℝ (Fin 3) → ℂ} (hm : Measurable f)
    (hb : ∃ C : ℝ, ∀ x, ‖f x‖ ≤ C)
    (hs : Function.support f ⊆ Work.BoseK15.corpusBox.boxL (Work.BoseBoxFock.ellH v μ)) :
    ∑ k : Work.BoseBoxFock.Lab N,
        ‖∫ y : EuclideanSpace ℝ (Fin 3),
            (starRingEnd ℂ) (Work.BoseBoxFock.pinQ v μ N k y) * f y‖ ^ 2
      ≤ ∫ y : EuclideanSpace ℝ (Fin 3),
          (Submission.BoseGases.chiScale (Work.BoseBoxFock.ellH v μ) y) ^ 2
            * ‖Work.BoseBoxFock.mf (Work.BoseBoxFock.ellH v μ) f y‖ ^ 2 := by
  classical
  have hℓ : 0 < Work.BoseBoxFock.ellH v μ := Work.BoseBoxFock.ellH_pos v μ
  -- `f` is `L²`: measurable, bounded, and supported in the compact box
  have hmem : MemLp f 2 (volume : Measure (EuclideanSpace ℝ (Fin 3))) := by
    rcases hb with ⟨C, hC⟩
    refine HasCompactSupport.memLp_of_bound ?_ hm.aestronglyMeasurable C
      (Eventually.of_forall hC)
    rw [HasCompactSupport]
    refine IsCompact.of_isClosed_subset
      (Work.BoseB4.BoxData.boxL_compact Work.BoseK15.corpusBox (Work.BoseBoxFock.ellH v μ))
      (isClosed_tsupport f) ?_
    rw [tsupport]
    calc closure (Function.support f)
        ⊆ closure (Work.BoseK15.corpusBox.boxL (Work.BoseBoxFock.ellH v μ)) := closure_mono hs
      _ = Work.BoseK15.corpusBox.boxL (Work.BoseBoxFock.ellH v μ) :=
          (Work.BoseB4.BoxData.boxL_compact Work.BoseK15.corpusBox
            (Work.BoseBoxFock.ellH v μ)).isClosed.closure_eq
  -- the tight-frame (Parseval) identity of `PB3Frame` over the full lattice
  have hbessel := (Work.BoseBoxFock.PB3Frame hℓ hmem (0 : Fin 3 → ℤ)).2.1
  set F : (Fin 3 → ℤ) → ℝ := fun n => ‖∫ y : EuclideanSpace ℝ (Fin 3),
      (starRingEnd ℂ) (Work.BoseBoxFock.pinQInf (Work.BoseBoxFock.ellH v μ) n y) * f y‖ ^ 2
    with hF
  -- `labVec N` injects the label cube into `ℤ³`
  have hinj : Set.InjOn (Work.BoseBoxFock.labVec N)
      ↑(Finset.univ : Finset (Work.BoseBoxFock.Lab N)) :=
    fun a _ b _ hab => funext fun i => ZMod.valMinAbs_inj.mp (congrFun hab i)
  have hsum_img := Finset.sum_image (s := (Finset.univ : Finset (Work.BoseBoxFock.Lab N)))
    (g := Work.BoseBoxFock.labVec N) (f := F) hinj
  -- the `Lab N`-sum is the sub-sum over the image of `labVec N`
  have hLHS : (∑ k : Work.BoseBoxFock.Lab N, ‖∫ y : EuclideanSpace ℝ (Fin 3),
        (starRingEnd ℂ) (Work.BoseBoxFock.pinQ v μ N k y) * f y‖ ^ 2)
      = ∑ n ∈ (Finset.univ.image (Work.BoseBoxFock.labVec N)), F n := by
    rw [hsum_img]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [hF]
    simp only [Work.BoseBoxFock.pinQ_eq_pinQInf]
  rw [hLHS]
  calc ∑ n ∈ (Finset.univ.image (Work.BoseBoxFock.labVec N)), F n
      ≤ ∑' n : Fin 3 → ℤ, F n :=
        hbessel.summable.sum_le_tsum _ (fun n _ => by positivity)
    _ = ∫ y : EuclideanSpace ℝ (Fin 3),
          (Submission.BoseGases.chiScale (Work.BoseBoxFock.ellH v μ) y) ^ 2
            * ‖Work.BoseBoxFock.mf (Work.BoseBoxFock.ellH v μ) f y‖ ^ 2 := hbessel.tsum_eq

end Work.BoseBoxFock
