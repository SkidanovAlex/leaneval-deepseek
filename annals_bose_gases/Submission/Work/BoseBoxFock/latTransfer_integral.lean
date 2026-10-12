import Mathlib.Order.CompletePartialOrder
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.MeasureTheory.Group.FundamentalDomain
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseBoxFock.latBox_ae_eq_latCell
import Submission.Work.BoseBoxFock.latTiling_integral
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.latTransfer_integral`

The Lebesgue integral of an `ℓℤ³`-periodic function over the two *fundamental domains* of the
lattice `ℓℤ³` used in this chapter is the same: the closed centred cube
`boxL ℓ = [-ℓ/2,ℓ/2]³ = ℓ • unitCell` of the corpus (`Work.BoseK15.corpusBox.boxL`) and the closed
corner cube `LatFourier.latBox ℓ = [0,ℓ]³`.

The proof is the standard comparison of fundamental domains, for which Mathlib has the required
machinery, `MeasureTheory.IsAddFundamentalDomain.setIntegral_eq`: the integral of an invariant
function is the same over any two fundamental domains of a countable, measure-preserving additive
action.  Concretely:

* the action is `ℤ³ ∋ m ↦ (x ↦ x + ℓ • latVec m)` (the instance `AddAction (Fin 3 → ℤ) E3` set up
  locally in the proof of the theorem, together with `MeasurableConstVAdd` and
  `VAddInvariantMeasure`, both from the translation invariance of Lebesgue measure);
* the two *half-open* cubes `latCell ℓ = [0,ℓ)³` and `latChl ℓ = [-ℓ/2,ℓ/2)³` are fundamental
  domains: `isAddFundamentalDomain_latCell` is the tiling proved in
  `Work.BoseBoxFock.latTiling_integral` (`latTile_cover`, `latTile_disjoint`), and
  `isAddFundamentalDomain_latChl` is its translate by `-ctr ℓ`, which is
  `MeasureTheory.IsAddFundamentalDomain.preimage_of_equiv` applied to the measure-preserving
  translation `z ↦ z + ctr ℓ` and the identification `latChl ℓ = (z ↦ z + ctr ℓ) ⁻¹' latCell ℓ`
  (`latChl_eq_preimage`);
* the closed cubes are a.e. equal to the corresponding half-open ones, so
  `MeasureTheory.setIntegral_congr_set` transfers the integrals: `latBox_ae_eq_latCell` is already
  proved in `Work.BoseBoxFock.latBox_ae_eq_latCell`, and `boxL_ae_eq_latChl` is the standard
  "equal finite volumes" argument (`latChl_subset_boxL`, `volume_latChl`, the corpus's
  `Work.BoseB4.BoxData.volume_boxL`, `MeasureTheory.measure_sdiff`).

Because `IsAddFundamentalDomain.setIntegral_eq` also treats the non-integrable case (through
`integral_undef`), the integrability hypotheses `hB` and `hL` of the statement are not needed; they
are kept because the target is stated with them.
-/

noncomputable section

open MeasureTheory
open scoped Pointwise

namespace Work.BoseBoxFock

local notation "E3" => EuclideanSpace ℝ (Fin 3)

set_option linter.unusedVariables false

/-! ## 1. The centred half-open cube `[-ℓ/2,ℓ/2)³` -/

/-- The centre `(ℓ/2, ℓ/2, ℓ/2)` of the centred cube of side `ℓ`. -/
def latChlCtr (ℓ : ℝ) : E3 := WithLp.toLp 2 (fun _ : Fin 3 => ℓ / 2)

@[simp] lemma latChlCtr_apply (ℓ : ℝ) (i : Fin 3) : latChlCtr ℓ i = ℓ / 2 := rfl

/-- The **half-open centred cube** `latChl ℓ = [-ℓ/2, ℓ/2)³`, the fundamental domain of `ℓℤ³`
that is a.e. equal to the closed centred cube `boxL ℓ = [-ℓ/2,ℓ/2]³` of the corpus.  It is the
translate of the half-open cell `latCell ℓ = [0,ℓ)³` by `-latChlCtr ℓ`. -/
def latChl (ℓ : ℝ) : Set E3 := {x : E3 | ∀ i, x i ∈ Set.Ico (-(ℓ/2)) (ℓ/2)}

/-- Characterisation of `latChl ℓ`: it is the translate of the half-open cell `latCell ℓ` of
`Work.BoseBoxFock.LatFourier` by `-latChlCtr ℓ`. -/
lemma mem_latChl {ℓ : ℝ} {x : E3} :
    x ∈ latChl ℓ ↔ x + latChlCtr ℓ ∈ LatFourier.latCell ℓ := by
  rw [latChl, LatFourier.mem_latCell]
  constructor
  · intro h i
    have hi := h i
    rw [Set.mem_Ico] at hi ⊢
    have h2 : (x + latChlCtr ℓ) i = x i + ℓ / 2 := by rw [PiLp.add_apply]; rfl
    rw [h2]
    exact ⟨by linarith [hi.1], by linarith [hi.2]⟩
  · intro h i
    have hi := h i
    rw [Set.mem_Ico] at hi ⊢
    have h2 : (x + latChlCtr ℓ) i = x i + ℓ / 2 := by rw [PiLp.add_apply]; rfl
    rw [h2] at hi
    exact ⟨by linarith [hi.1], by linarith [hi.2]⟩

/-- `latChl ℓ` is the preimage of the half-open cell under the translation `z ↦ z + latChlCtr ℓ`. -/
lemma latChl_eq_preimage (ℓ : ℝ) :
    latChl ℓ = (fun z : E3 => z + latChlCtr ℓ) ⁻¹' LatFourier.latCell ℓ := by
  ext x; rw [Set.mem_preimage, mem_latChl]

lemma measurableSet_latChl (ℓ : ℝ) : MeasurableSet (latChl ℓ) := by
  have h : latChl ℓ = ⋂ i : Fin 3, {x : E3 | x i ∈ Set.Ico (-(ℓ/2)) (ℓ/2)} := by
    ext x; simp [latChl]
  rw [h]
  exact MeasurableSet.iInter fun i =>
    measurableSet_Ico.preimage (by fun_prop : Measurable fun x : E3 => x i)

/-- `latChl ℓ` has the volume of the cell, `ℓ³`. -/
lemma volume_latChl (ℓ : ℝ) : volume (latChl ℓ) = volume (LatFourier.latCell ℓ) := by
  rw [latChl_eq_preimage]
  exact MeasurePreserving.measure_preimage (measurePreserving_add_right volume (latChlCtr ℓ))
    (LatFourier.measurableSet_latCell ℓ).nullMeasurableSet

/-- The half-open centred cube sits inside the corpus's centred cube `boxL ℓ = [-ℓ/2,ℓ/2]³`. -/
lemma latChl_subset_boxL {ℓ : ℝ} (hℓ : 0 < ℓ) : latChl ℓ ⊆ Work.BoseK15.corpusBox.boxL ℓ := by
  intro x hx
  rw [Work.BoseB4.BoxData.boxL, Set.mem_smul_set_iff_inv_smul_mem₀ (ne_of_gt hℓ)]
  intro i
  have hi := hx i
  rw [Set.mem_Ico] at hi
  have h2 : (ℓ⁻¹ • x) i = ℓ⁻¹ * x i := by rw [PiLp.smul_apply]; rfl
  rw [h2, abs_mul, abs_of_pos (inv_pos.mpr hℓ)]
  have habs : |x i| ≤ ℓ / 2 := by
    rw [abs_le]; exact ⟨by linarith [hi.1], le_of_lt (by linarith [hi.2])⟩
  calc ℓ⁻¹ * |x i| ≤ ℓ⁻¹ * (ℓ / 2) :=
        mul_le_mul_of_nonneg_left habs (le_of_lt (inv_pos.mpr hℓ))
    _ = 1 / 2 := by field_simp

/-- The closed centred cube `boxL ℓ` is a.e. equal to the half-open centred cube `latChl ℓ`: they
differ only by the boundary faces, which are null, and they have the same finite volume. -/
lemma boxL_ae_eq_latChl {ℓ : ℝ} (hℓ : 0 < ℓ) :
    Work.BoseK15.corpusBox.boxL ℓ =ᵐ[volume] latChl ℓ := by
  rw [MeasureTheory.ae_eq_set]
  refine ⟨?_, ?_⟩
  · rw [MeasureTheory.measure_sdiff (latChl_subset_boxL hℓ) (measurableSet_latChl ℓ).nullMeasurableSet
        (by rw [volume_latChl ℓ, LatFourier.volume_latCell hℓ.le]; exact ENNReal.ofReal_ne_top),
      Work.BoseB4.BoxData.volume_boxL Work.BoseK15.corpusBox hℓ, volume_latChl ℓ,
      LatFourier.volume_latCell hℓ.le, tsub_self]
  · rw [Set.sdiff_eq_empty.mpr (latChl_subset_boxL hℓ), measure_empty]

/-! ## 2. Two elementary lattice lemmas -/

private lemma latVec_neg (m : Fin 3 → ℤ) : latVec (-m) = -latVec m := by
  ext i
  rw [latVec_apply, Pi.neg_apply, Int.cast_neg]
  rfl

/-- The tile of the zero lattice vector is the cell itself. -/
private lemma latTile_zero (ℓ : ℝ) : latTile ℓ (0 : Fin 3 → ℤ) = LatFourier.latCell ℓ := by
  ext x
  rw [latTile_mem, LatFourier.mem_latCell, LatFourier.mem_latCell, LatFourier.latVec_zero,
    smul_zero, sub_zero]

/-! ## 3. The target -/

theorem latTransfer_integral {ℓ : ℝ} (hℓ : 0 < ℓ) {f : EuclideanSpace ℝ (Fin 3) → ℂ}
    (hper : ∀ (m : Fin 3 → ℤ) (z : EuclideanSpace ℝ (Fin 3)),
      f (z + ℓ • Work.BoseBoxFock.latVec m) = f z)
    (hB : MeasureTheory.IntegrableOn f (Work.BoseK15.corpusBox.boxL ℓ) MeasureTheory.volume)
    (hL : MeasureTheory.IntegrableOn f (Work.BoseBoxFock.LatFourier.latBox ℓ) MeasureTheory.volume) :
    (∫ z in Work.BoseK15.corpusBox.boxL ℓ, f z)
      = ∫ z in Work.BoseBoxFock.LatFourier.latBox ℓ, f z := by
  -- the action of `ℤ³` on `E3` by the translations `x ↦ x + ℓ • latVec m`
  let act : AddAction (Fin 3 → ℤ) E3 :=
    { vadd := fun m x => x + ℓ • latVec m
      zero_vadd := fun x => by
        show x + ℓ • latVec (0 : Fin 3 → ℤ) = x
        rw [LatFourier.latVec_zero, smul_zero, add_zero]
      add_vadd := fun m m' x => by
        show x + ℓ • latVec (m + m') = (x + ℓ • latVec m') + ℓ • latVec m
        rw [LatFourier.latVec_add, smul_add]; abel }
  letI := act
  haveI : MeasurableConstVAdd (Fin 3 → ℤ) E3 :=
    ⟨fun c => by show Measurable fun x : E3 => x + ℓ • latVec c; fun_prop⟩
  haveI : VAddInvariantMeasure (Fin 3 → ℤ) E3 (volume : Measure E3) :=
    ⟨fun c s hs => by
      show volume ((fun x : E3 => x + ℓ • latVec c) ⁻¹' s) = volume s
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
      rw [latVec_neg, smul_neg]
      exact hm'
    · intro g hg
      have hd : Disjoint (g +ᵥ LatFourier.latCell ℓ) (LatFourier.latCell ℓ) := by
        have h : Disjoint (latTile ℓ g) (latTile ℓ (0 : Fin 3 → ℤ)) := latTile_disjoint ℓ hℓ hg
        rw [latTile_zero ℓ] at h
        exact h
      exact Disjoint.aedisjoint hd
    · intro g
      show Measure.QuasiMeasurePreserving (fun x : E3 => x + ℓ • latVec g) volume volume
      exact (measurePreserving_add_right volume (ℓ • latVec g)).quasiMeasurePreserving
  -- the centred half-open cube is the translate of the cell by `-latChlCtr ℓ`
  have hfdChl : IsAddFundamentalDomain (Fin 3 → ℤ) (latChl ℓ) volume := by
    have h := hfdC.preimage_of_equiv (s := LatFourier.latCell ℓ)
        (f := fun z : E3 => z + latChlCtr ℓ)
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
