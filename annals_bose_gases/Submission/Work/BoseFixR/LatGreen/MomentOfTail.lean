import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseFixR.LatGreen.IntegrableOfSqWeight
import Submission.Work.BoseFixR.LatGreen.LintegralTailLimit
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

open MeasureTheory Set

namespace Work.BoseFixR.LatGreen

/-! ## The proof of `MomentOfTail`

The mathematics: since `G ≥ 0` a.e. on `(0,∞)`, the hypothesis `hInt2` (`s²|G s| ∈ L¹`)
shows that `s ↦ s·G s` is integrable on every tail `(r,∞)` with `r > 0`
(`Work.BoseFixR.LatGreen.IntegrableOfSqWeight`), so the pointwise tail bound `hTail` is a
genuine statement about Bochner integrals.  Monotone convergence along `r ↓ 0`
(`Work.BoseFixR.LatGreen.LintegralTailLimit`) then yields
`∫⁻_{s>0} ofReal (s·|G s|) ≤ ofReal 2`, which is converted back into the Bochner statement
by `lintegral_to_integral`.

Helpers proved here: `tail_lintegral_le` (the tail bound in `ℝ≥0∞` form) and
`lintegral_to_integral` (the final `∫⁻ → ∫` conversion). -/

/-- A bound `∫⁻_{s>0} ofReal (f s) ≤ ofReal C` for a nonnegative a.e.-strongly-measurable `f`
gives integrability of `f` on `(0,∞)` and `∫_{s>0} f s ≤ C`. -/
private lemma lintegral_to_integral {f : ℝ → ℝ} {C : ℝ} (hC : 0 ≤ C)
    (hf : AEStronglyMeasurable f (volume.restrict (Set.Ioi (0 : ℝ))))
    (hnn : ∀ᵐ s ∂(volume.restrict (Set.Ioi (0 : ℝ))), 0 ≤ f s)
    (hb : (∫⁻ s in Set.Ioi (0 : ℝ), ENNReal.ofReal (f s)) ≤ ENNReal.ofReal C) :
    IntegrableOn f (Set.Ioi (0 : ℝ)) ∧ (∫ s in Set.Ioi (0 : ℝ), f s) ≤ C := by
  have hfin : HasFiniteIntegral f (volume.restrict (Set.Ioi (0 : ℝ))) :=
    (hasFiniteIntegral_iff_ofReal hnn).2 (lt_of_le_of_lt hb ENNReal.ofReal_lt_top)
  have hint : Integrable f (volume.restrict (Set.Ioi (0 : ℝ))) := ⟨hf, hfin⟩
  refine ⟨hint, ?_⟩
  rw [integral_eq_lintegral_of_nonneg_ae hnn hf]
  exact le_trans (ENNReal.toReal_mono ENNReal.ofReal_ne_top hb)
    (le_of_eq (ENNReal.toReal_ofReal hC))

/-- The tail bound `∫_{s>r} s·G s ≤ 2` turns into a bound on the `ℝ≥0∞`-integral of the
nonnegative function `ofReal (s·|G s|)` over the tail `(r,∞)`.  Here the integrability of
`s·G s` on `(r,∞)` (from `s²|G s| ∈ L¹` and `r > 0`) is what makes the hypothesis
`hTail` a genuine statement about the Bochner integral. -/
private lemma tail_lintegral_le {G : ℝ → ℝ} {R r : ℝ} (hr : 0 < r) (hrR : r < R)
    (hGmeas : AEStronglyMeasurable G (volume.restrict (Set.Ioi (0 : ℝ))))
    (hInt2 : IntegrableOn (fun s : ℝ => s ^ 2 * |G s|) (Set.Ioi (0 : ℝ)))
    (hnn : ∀ᵐ s ∂(volume.restrict (Set.Ioi (0 : ℝ))), 0 ≤ G s)
    (hTail : ∀ r : ℝ, 0 < r → r < R → (∫ s in Set.Ioi r, s * G s) ≤ 2) :
    (∫⁻ s in Set.Ioi r, ENNReal.ofReal (s * |G s|)) ≤ ENNReal.ofReal 2 := by
  have hInt : IntegrableOn (fun s : ℝ => s * G s) (Set.Ioi r) :=
    IntegrableOfSqWeight hr hGmeas hInt2
  have hnnr : ∀ᵐ s ∂(volume.restrict (Set.Ioi r)), 0 ≤ G s :=
    Filter.Eventually.filter_mono
      (ae_mono (Measure.restrict_mono (Ioi_subset_Ioi (le_of_lt hr)) le_rfl)) hnn
  have hnn2 : ∀ᵐ s ∂(volume.restrict (Set.Ioi r)), 0 ≤ s * G s := by
    filter_upwards [hnnr, ae_restrict_mem measurableSet_Ioi] with s hs hs'
    exact mul_nonneg (le_of_lt (lt_trans hr hs')) hs
  have heq : (fun s => ENNReal.ofReal (s * |G s|)) =ᵐ[volume.restrict (Set.Ioi r)]
      (fun s => ENNReal.ofReal (s * G s)) := by
    filter_upwards [hnnr] with s hs
    rw [abs_of_nonneg hs]
  calc (∫⁻ s in Set.Ioi r, ENNReal.ofReal (s * |G s|))
      = ∫⁻ s in Set.Ioi r, ENNReal.ofReal (s * G s) := lintegral_congr_ae heq
    _ = ENNReal.ofReal (∫ s in Set.Ioi r, s * G s) :=
        (ofReal_integral_eq_lintegral_ofReal hInt hnn2).symm
    _ ≤ ENNReal.ofReal 2 := (ENNReal.ofReal_le_ofReal_iff (by norm_num)).2 (hTail r hr hrR)

/-- **Weighted moment bound from a tail bound.** Let `G : ℝ → ℝ` with
`G ∈ L¹(s²ds)` on `(0,∞)`, `G ≥ 0` a.e. on `(0,∞)`, a.e. strongly measurable, and
`∫_{s>r} s G s ds ≤ 2` for every `0 < r < R` (`R > 0`). Then `s ↦ s·|G s|` is
integrable on `(0,∞)` with integral at most `2`. Namespace
`Work.BoseFixR.LatGreen`. -/
theorem MomentOfTail {G : ℝ → ℝ} {R : ℝ} (hR : 0 < R)
    (hGmeas : MeasureTheory.AEStronglyMeasurable G (MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))))
    (hInt2 : MeasureTheory.IntegrableOn (fun s : ℝ => s ^ 2 * |G s|) (Set.Ioi (0 : ℝ)))
    (hnn : ∀ᵐ s ∂(MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))), 0 ≤ G s)
    (hTail : ∀ r : ℝ, 0 < r → r < R → (∫ s in Set.Ioi r, s * G s) ≤ 2) :
    MeasureTheory.IntegrableOn (fun s : ℝ => s * |G s|) (Set.Ioi (0 : ℝ)) ∧
      (∫ s in Set.Ioi (0 : ℝ), s * |G s|) ≤ 2 := by
  have h1 : AEStronglyMeasurable (fun s : ℝ => s * |G s|) (volume.restrict (Set.Ioi (0 : ℝ))) := by
    have habs : AEStronglyMeasurable (fun s : ℝ => |G s|) (volume.restrict (Set.Ioi (0 : ℝ))) := by
      simpa only [Real.norm_eq_abs] using hGmeas.norm
    exact (continuous_id.aestronglyMeasurable).mul habs
  have hg : AEStronglyMeasurable (fun s : ℝ => ENNReal.ofReal (s * |G s|))
      (volume.restrict (Set.Ioi (0 : ℝ))) :=
    ENNReal.continuous_ofReal.comp_aestronglyMeasurable h1
  have hbound : (∫⁻ s in Set.Ioi (0 : ℝ), ENNReal.ofReal (s * |G s|)) ≤ ENNReal.ofReal 2 :=
    LintegralTailLimit hR hg (fun r hr hrR => tail_lintegral_le hr hrR hGmeas hInt2 hnn hTail)
  have hnn' : ∀ᵐ s ∂(volume.restrict (Set.Ioi (0 : ℝ))), 0 ≤ s * |G s| := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
    exact mul_nonneg (le_of_lt hs) (abs_nonneg _)
  exact lintegral_to_integral (by norm_num) h1 hnn' hbound

end Work.BoseFixR.LatGreen
