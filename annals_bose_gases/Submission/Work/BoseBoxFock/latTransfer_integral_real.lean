import Mathlib.Order.CompletePartialOrder
import Mathlib.MeasureTheory.Group.FundamentalDomain
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseBoxFock.latTransfer_integral
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.latTransfer_integral_real`

The **real-valued** twin of `Work.BoseBoxFock.latTransfer_integral`: the Lebesgue integral of an
`ℓℤ³`-periodic *real* function over the two fundamental domains of the lattice `ℓℤ³` is the same,
namely over the closed centred cube `boxL ℓ = [-ℓ/2,ℓ/2]³ = ℓ • unitCell` of the corpus
(`Work.BoseK15.corpusBox.boxL`) and over the closed corner cube `LatFourier.latBox ℓ = [0,ℓ]³`.

The proof is a verbatim transcription of the complex-valued proof, which needs no integrability
hypotheses: `MeasureTheory.IsAddFundamentalDomain.setIntegral_eq` is stated for functions with
values in any normed `ℝ`-vector space, so it applies to `E = ℝ` as well, and the two transfers
between the closed cubes and the corresponding half-open fundamental domains
(`Work.BoseBoxFock.boxL_ae_eq_latChl`, `Work.BoseBoxFock.LatFourier.latBox_ae_eq_latCell`) are
`MeasureTheory.setIntegral_congr_set`, also valid for real-valued functions.  Consequently the
integrability hypotheses `hB`, `hL` of the complex version are not needed here (they were kept
there only because the filing had them; both statements hold unconditionally, the non-integrable
case being handled by `integral_undef`).

The two auxiliary facts that were `private` in the complex file (`latVec_neg`, `latTile_zero`) are
re-proved here under local names.
-/

noncomputable section

open MeasureTheory
open scoped Pointwise

namespace Work.BoseBoxFock

/-! ## Two elementary lattice lemmas (private in the complex file) -/

private lemma latVec_neg_local (m : Fin 3 → ℤ) : latVec (-m) = -latVec m := by
  ext i
  rw [latVec_apply, Pi.neg_apply, Int.cast_neg]
  rfl

/-- The tile of the zero lattice vector is the half-open cell itself. -/
private lemma latTile_zero_local (ℓ : ℝ) : latTile ℓ (0 : Fin 3 → ℤ) = LatFourier.latCell ℓ := by
  ext x
  rw [latTile_mem, LatFourier.mem_latCell, LatFourier.mem_latCell, LatFourier.latVec_zero,
    smul_zero, sub_zero]

/-! ## The target -/

theorem latTransfer_integral_real {ℓ : ℝ} (hℓ : 0 < ℓ) {f : EuclideanSpace ℝ (Fin 3) → ℝ}
    (hper : ∀ (m : Fin 3 → ℤ) (z : EuclideanSpace ℝ (Fin 3)),
      f (z + ℓ • Work.BoseBoxFock.latVec m) = f z) :
    (∫ z in Work.BoseK15.corpusBox.boxL ℓ, f z)
      = ∫ z in Work.BoseBoxFock.LatFourier.latBox ℓ, f z := by
  -- the action of `ℤ³` on `E3` by the translations `x ↦ x + ℓ • latVec m`
  let act : AddAction (Fin 3 → ℤ) (EuclideanSpace ℝ (Fin 3)) :=
    { vadd := fun m x => x + ℓ • latVec m
      zero_vadd := fun x => by
        show x + ℓ • latVec (0 : Fin 3 → ℤ) = x
        rw [LatFourier.latVec_zero, smul_zero, add_zero]
      add_vadd := fun m m' x => by
        show x + ℓ • latVec (m + m') = (x + ℓ • latVec m') + ℓ • latVec m
        rw [LatFourier.latVec_add, smul_add]; abel }
  letI := act
  haveI : MeasurableConstVAdd (Fin 3 → ℤ) (EuclideanSpace ℝ (Fin 3)) :=
    ⟨fun c => by
      show Measurable fun x : EuclideanSpace ℝ (Fin 3) => x + ℓ • latVec c
      fun_prop⟩
  haveI : VAddInvariantMeasure (Fin 3 → ℤ) (EuclideanSpace ℝ (Fin 3))
      (volume : Measure (EuclideanSpace ℝ (Fin 3))) :=
    ⟨fun c s hs => by
      show volume ((fun x : EuclideanSpace ℝ (Fin 3) => x + ℓ • latVec c) ⁻¹' s) = volume s
      exact MeasurePreserving.measure_preimage (measurePreserving_add_right volume (ℓ • latVec c))
        hs.nullMeasurableSet⟩
  -- the half-open cell is a fundamental domain: the tiling `latTile_cover`/`latTile_disjoint`
  have hfdC : IsAddFundamentalDomain (Fin 3 → ℤ) (LatFourier.latCell ℓ) volume := by
    refine IsAddFundamentalDomain.mk'' (LatFourier.measurableSet_latCell ℓ).nullMeasurableSet
      (Filter.Eventually.of_forall fun x => ?_) ?_ ?_
    · have hx : x ∈ ⋃ m : Fin 3 → ℤ, latTile ℓ m := by rw [latTile_cover ℓ hℓ]; trivial
      obtain ⟨m, hm⟩ := Set.mem_iUnion.mp hx
      refine ⟨-m, ?_⟩
      have hm' : x - ℓ • latVec m ∈ LatFourier.latCell ℓ := (latTile_mem ℓ m x).mp hm
      show x + ℓ • latVec (-m) ∈ LatFourier.latCell ℓ
      rw [latVec_neg_local, smul_neg]
      exact hm'
    · intro g hg
      have hd : Disjoint (g +ᵥ LatFourier.latCell ℓ) (LatFourier.latCell ℓ) := by
        have h : Disjoint (latTile ℓ g) (latTile ℓ (0 : Fin 3 → ℤ)) := latTile_disjoint ℓ hℓ hg
        rw [latTile_zero_local ℓ] at h
        exact h
      exact Disjoint.aedisjoint hd
    · intro g
      show Measure.QuasiMeasurePreserving (fun x : EuclideanSpace ℝ (Fin 3) => x + ℓ • latVec g)
        volume volume
      exact (measurePreserving_add_right volume (ℓ • latVec g)).quasiMeasurePreserving
  -- the centred half-open cube is the translate of the cell by `-latChlCtr ℓ`
  have hfdChl : IsAddFundamentalDomain (Fin 3 → ℤ) (latChl ℓ) volume := by
    have h := hfdC.preimage_of_equiv (s := LatFourier.latCell ℓ)
        (f := fun z : EuclideanSpace ℝ (Fin 3) => z + latChlCtr ℓ)
        (measurePreserving_add_right volume (latChlCtr ℓ)).quasiMeasurePreserving
        (e := id) Function.bijective_id (fun g x => by
          show (x + ℓ • latVec g) + latChlCtr ℓ = (x + latChlCtr ℓ) + ℓ • latVec g
          abel)
    rwa [← latChl_eq_preimage ℓ] at h
  -- transfer between the two half-open fundamental domains, then to the closed cubes
  have h1 : (∫ z in latChl ℓ, f z) = ∫ z in LatFourier.latCell ℓ, f z :=
    IsAddFundamentalDomain.setIntegral_eq hfdChl hfdC (fun m z => hper m z)
  have h2 : (∫ z in Work.BoseK15.corpusBox.boxL ℓ, f z) = ∫ z in latChl ℓ, f z :=
    setIntegral_congr_set (boxL_ae_eq_latChl hℓ)
  have h3 : (∫ z in LatFourier.latCell ℓ, f z) = ∫ z in LatFourier.latBox ℓ, f z :=
    (setIntegral_congr_set (latBox_ae_eq_latCell hℓ.le)).symm
  exact h2.trans (h1.trans h3)

end Work.BoseBoxFock
