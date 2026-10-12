import Mathlib.Order.CompletePartialOrder
import Mathlib.MeasureTheory.Group.FundamentalDomain
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Submission.Work.BoseBoxFock.latTransfer_integral
import Submission.Work.BoseFixR.SamplingSqSumLeChiR0
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.periodic_double_fold`

The **double fold** of an `ℓℤ³`-periodic function over the box `cell ℓ = [-ℓ/2,ℓ/2]³`:

    ∫_{cell} ∫_{cell} h (w - y) = ℓ³ ∫_{cell} h .

The content is the standard comparison of fundamental domains of the lattice `ℓℤ³`.  Both `cell`
and the half-open cube `cellI ℓ = [-ℓ/2,ℓ/2)³` are fundamental domains of the translation action
`ℤ³ ∋ m ↦ (x ↦ x + ℓ • latVec m)`, and `MeasureTheory.IsAddFundamentalDomain.setIntegral_eq`
compares the integrals of an invariant function between any two fundamental domains (this also
covers the non-integrable case, via `integral_undef`, so no regularity of `h` is needed).

The route is:

* `cell` and `cellI` are a.e. equal, so their integrals agree for an arbitrary integrand
  (`Work.BoseFixR.cellI_ae_eq_cell`, `Work.BoseFixR.setIntegral_cellI_eq_cell`);
* the half-open cube `cellI ℓ = latChl ℓ` is a fundamental domain: `latCell ℓ = [0,ℓ)³` is one
  (`latTile_cover`/`latTile_disjoint` with `MeasureTheory.IsAddFundamentalDomain.mk''`, exactly as
  in `Work.BoseBoxFock.latTransfer_integral`), and `cellI ℓ` is its translate by `latChlCtr ℓ`
  (`MeasureTheory.IsAddFundamentalDomain.preimage_of_equiv`);
* translation invariance: for a function invariant under the action and any `a`, the integral over
  `cellI` of `f (· + a)` equals the integral of `f` (both `cellI` and its translate are fundamental
  domains);
* finally `h (w - y) = H (y + (-w))` for `H z = h (-z)`, so for every `w` the `y`-integral of
  `h (w - ·)` is the constant `∫_{cell} H = ∫_{cell} h` (the last identity uses `Neg.neg '' cell =
  cell`, the closed cube being symmetric), and the outer integral over the box of side `ℓ` of a
  constant is `ℓ³` times that constant.
-/

noncomputable section

open MeasureTheory MeasureTheory.Measure
open scoped Pointwise

namespace Work.BoseBoxFock

local notation "E3" => EuclideanSpace ℝ (Fin 3)

set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option maxHeartbeats 800000

/-! ## 1. Elementary lemmas -/

private lemma latVec_neg' (m : Fin 3 → ℤ) : latVec (-m) = -latVec m := by
  ext i
  simp [latVec]

private lemma latTile_zero (ℓ : ℝ) : latTile ℓ (0 : Fin 3 → ℤ) = LatFourier.latCell ℓ := by
  ext x
  rw [latTile_mem, LatFourier.mem_latCell, LatFourier.mem_latCell, LatFourier.latVec_zero,
    smul_zero, sub_zero]

/-- The closed cube is symmetric under negation. -/
lemma neg_image_cellR (ℓ : ℝ) : Neg.neg '' (Work.BoseFixR.cell ℓ) = Work.BoseFixR.cell ℓ := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    rw [Work.BoseFixR.mem_cell] at hy ⊢
    intro i
    simpa using hy i
  · intro hx
    refine ⟨-x, ?_, by simp⟩
    rw [Work.BoseFixR.mem_cell] at hx ⊢
    intro i
    simpa using hx i

/-! ## 2. The target -/

theorem periodic_double_fold {ℓ : ℝ} (hℓ : 0 < ℓ) {h : EuclideanSpace ℝ (Fin 3) → ℝ}
    (hper : ∀ (m : Fin 3 → ℤ) (z : EuclideanSpace ℝ (Fin 3)),
      h (z + ℓ • Work.BoseBoxFock.latVec m) = h z) :
    ∫ w in Work.BoseFixR.cell ℓ, ∫ y in Work.BoseFixR.cell ℓ, h (w - y)
      = ℓ ^ 3 * ∫ z in Work.BoseFixR.cell ℓ, h z := by
  classical
  -- ## The lattice action `ℤ³ ∋ m ↦ (x ↦ x + ℓ • latVec m)` and its instances
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
  -- ## `latCell ℓ = [0,ℓ)³` is a fundamental domain
  have hfdC : IsAddFundamentalDomain (Fin 3 → ℤ) (LatFourier.latCell ℓ) volume := by
    refine IsAddFundamentalDomain.mk'' (LatFourier.measurableSet_latCell ℓ).nullMeasurableSet
      (Filter.Eventually.of_forall fun x => ?_) ?_ ?_
    · have hx : x ∈ ⋃ m : Fin 3 → ℤ, latTile ℓ m := by rw [latTile_cover ℓ hℓ]; trivial
      obtain ⟨m, hm⟩ := Set.mem_iUnion.mp hx
      refine ⟨-m, ?_⟩
      have hm' : x - ℓ • latVec m ∈ LatFourier.latCell ℓ := (latTile_mem ℓ m x).mp hm
      show x + ℓ • latVec (-m) ∈ LatFourier.latCell ℓ
      rw [latVec_neg', smul_neg]
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
  -- ## `cellI ℓ = latChl ℓ` is a fundamental domain (the translate of `latCell ℓ`)
  have hfdI : IsAddFundamentalDomain (Fin 3 → ℤ) (Work.BoseFixR.cellI ℓ) volume := by
    have h := hfdC.preimage_of_equiv (s := LatFourier.latCell ℓ)
        (f := fun z : E3 => z + latChlCtr ℓ)
        (measurePreserving_add_right volume (latChlCtr ℓ)).quasiMeasurePreserving
        (e := id) Function.bijective_id fun g x => by
          show (x + ℓ • latVec g) + latChlCtr ℓ = (x + latChlCtr ℓ) + ℓ • latVec g
          abel
    rw [← latChl_eq_preimage ℓ] at h
    exact h
  -- ## invariance of `h` under the action
  have hinv : ∀ (g : Fin 3 → ℤ) (x : E3), h (g +ᵥ x) = h x := fun g x => hper g x
  -- ## translation invariance of the integral over `cellI` for invariant functions
  have htrans : ∀ (f : E3 → ℝ), (∀ (g : Fin 3 → ℤ) (x : E3), f (g +ᵥ x) = f x) →
      ∀ a : E3, (∫ z in Work.BoseFixR.cellI ℓ, f (z + a))
        = ∫ z in Work.BoseFixR.cellI ℓ, f z := by
    intro f hf a
    have hPre : IsAddFundamentalDomain (Fin 3 → ℤ)
        ((fun z : E3 => z + (-a)) ⁻¹' Work.BoseFixR.cellI ℓ) volume :=
      hfdI.preimage_of_equiv (f := fun z : E3 => z + (-a))
        (measurePreserving_add_right volume (-a)).quasiMeasurePreserving
        (e := id) Function.bijective_id fun g x => by
          show (x + ℓ • latVec g) + (-a) = (x + (-a)) + ℓ • latVec g
          abel
    have hset : (fun y : E3 => y + a) '' Work.BoseFixR.cellI ℓ
        = (fun z : E3 => z + (-a)) ⁻¹' Work.BoseFixR.cellI ℓ := by
      ext z
      constructor
      · rintro ⟨y, hy, rfl⟩
        show (y + a) + (-a) ∈ Work.BoseFixR.cellI ℓ
        rw [add_assoc, add_neg_cancel, add_zero]
        exact hy
      · intro hz
        exact ⟨z + (-a), hz, by abel⟩
    rw [setIntegral_comp_add_right f (Work.BoseFixR.cellI ℓ) a, hset]
    exact IsAddFundamentalDomain.setIntegral_eq hPre hfdI hf
  -- ## the key pointwise identity
  set H : E3 → ℝ := fun z => h (-z) with hH
  have hHinv : ∀ (g : Fin 3 → ℤ) (x : E3), H (g +ᵥ x) = H x := by
    intro g x
    change h (-(x + ℓ • latVec g)) = h (-x)
    have h1 : -(x + ℓ • latVec g) = (-x) + ℓ • latVec (-g) := by
      rw [latVec_neg', smul_neg]; abel
    rw [h1, hper (-g) (-x)]
  have key : ∀ w : E3, (∫ y in Work.BoseFixR.cell ℓ, h (w - y))
      = ∫ z in Work.BoseFixR.cell ℓ, h z := by
    intro w
    have h1 : (∫ y in Work.BoseFixR.cell ℓ, h (w - y))
        = ∫ y in Work.BoseFixR.cell ℓ, H (y + (-w)) := by
      refine setIntegral_congr_fun (Work.BoseFixR.measurableSet_boxL ℓ) fun y _ => ?_
      change h (w - y) = h (-(y + (-w)))
      rw [show w - y = -(y + (-w)) from by abel]
    have h2 : (∫ y in Work.BoseFixR.cell ℓ, H (y + (-w)))
        = ∫ y in Work.BoseFixR.cellI ℓ, H (y + (-w)) :=
      (Work.BoseFixR.setIntegral_cellI_eq_cell ℓ (fun y => H (y + (-w)))).symm
    have h3 : (∫ y in Work.BoseFixR.cellI ℓ, H (y + (-w)))
        = ∫ y in Work.BoseFixR.cellI ℓ, H y := htrans H hHinv (-w)
    have h4 : (∫ y in Work.BoseFixR.cellI ℓ, H y) = ∫ y in Work.BoseFixR.cell ℓ, H y :=
      Work.BoseFixR.setIntegral_cellI_eq_cell ℓ H
    have h5 : (∫ y in Work.BoseFixR.cell ℓ, H y)
        = ∫ y in Work.BoseFixR.cell ℓ, h (-y) := by
      simp only [hH]
    have h6 : (∫ y in Work.BoseFixR.cell ℓ, h (-y))
        = ∫ x in Neg.neg '' (Work.BoseFixR.cell ℓ), h x :=
      (MeasurePreserving.setIntegral_image_emb
        (Measure.measurePreserving_neg (volume : Measure E3)) measurableEmbedding_neg
        h (Work.BoseFixR.cell ℓ)).symm
    have h7 : (∫ x in Neg.neg '' (Work.BoseFixR.cell ℓ), h x)
        = ∫ x in Work.BoseFixR.cell ℓ, h x := by rw [neg_image_cellR ℓ]
    rw [h1, h2, h3, h4, h5, h6, h7]
  -- ## the volume of the box
  have hvolreal : volume.real (Work.BoseFixR.cell ℓ) = ℓ ^ 3 := by
    have h : volume (Work.BoseFixR.cell ℓ) = ENNReal.ofReal (ℓ ^ 3) :=
      Work.BoseFixR.volume_boxL ℓ
    show (volume (Work.BoseFixR.cell ℓ)).toReal = ℓ ^ 3
    rw [h, ENNReal.toReal_ofReal (by positivity)]
  calc ∫ w in Work.BoseFixR.cell ℓ, ∫ y in Work.BoseFixR.cell ℓ, h (w - y)
      = ∫ w in Work.BoseFixR.cell ℓ, (∫ z in Work.BoseFixR.cell ℓ, h z) := by
        refine setIntegral_congr_fun (Work.BoseFixR.measurableSet_boxL ℓ) fun w _ => key w
    _ = volume.real (Work.BoseFixR.cell ℓ) • (∫ z in Work.BoseFixR.cell ℓ, h z) :=
        setIntegral_const _
    _ = ℓ ^ 3 * ∫ z in Work.BoseFixR.cell ℓ, h z := by rw [hvolreal, smul_eq_mul]

end Work.BoseBoxFock
