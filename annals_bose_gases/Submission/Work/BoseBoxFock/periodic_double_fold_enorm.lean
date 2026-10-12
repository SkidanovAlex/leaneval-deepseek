import Mathlib.Order.CompletePartialOrder
import Mathlib.MeasureTheory.Group.FundamentalDomain
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Submission.Work.BoseBoxFock.periodic_double_integral_le
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

noncomputable section

open MeasureTheory MeasureTheory.Measure
open scoped Pointwise

namespace Work.BoseBoxFock

local notation "E3" => EuclideanSpace ℝ (Fin 3)

set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option maxHeartbeats 1600000

/-! ## 1. Elementary lemmas -/

/-- `∫⁻` over two a.e. equal sets agree.  This is the `lintegral` twin of
`MeasureTheory.setIntegral_congr_set`; no measurability of the integrand is needed, since the
`lintegral` only sees the restricted measure. -/
lemma setLIntegral_congr_set_ae {α : Type*} [MeasurableSpace α] {μ : Measure α} {s t : Set α}
    (hst : s =ᵐ[μ] t) (f : α → ENNReal) :
    ∫⁻ x in s, f x ∂μ = ∫⁻ x in t, f x ∂μ := by
  rw [Measure.restrict_congr_set hst]

private lemma latVec_neg_enf (m : Fin 3 → ℤ) : latVec (-m) = -latVec m := by
  ext i
  simp [latVec]

private lemma latTile_zero_enf (ℓ : ℝ) : latTile ℓ (0 : Fin 3 → ℤ) = LatFourier.latCell ℓ := by
  ext x
  rw [latTile_mem, LatFourier.mem_latCell, LatFourier.mem_latCell, LatFourier.latVec_zero,
    smul_zero, sub_zero]

/-! ## 2. The target -/

-- The `ENNReal`-valued twin of the PROVED `Work.BoseBoxFock.periodic_double_fold`
-- (`Submission/Work/BoseBoxFock/periodic_double_fold.lean`), which is the `ℝ`-valued statement
-- `∫ w in cell ℓ, ∫ y in cell ℓ, h (w - y) = ℓ^3 * ∫ z in cell ℓ, h z` for `ℤ³`-periodic `h`.
-- Here `boxL ℓ = ℓ • unitCell = [-ℓ/2,ℓ/2]³` equals `Work.BoseFixR.cell ℓ`
-- (`corpusBox_boxL_eq_cell`), so the same proof (fundamental domains `latCell ℓ = [0,ℓ)³` and
-- `latChl ℓ = [-ℓ/2,ℓ/2)³`, `IsAddFundamentalDomain.setLIntegral_eq`,
-- `MeasurePreserving.setLIntegral_comp_emb`, `setLIntegral_const`, `volume_boxL`) carries over
-- with `setIntegral ↦ setLIntegral`; compare `Work.BoseBoxFock.periodic_double_fold`.
theorem periodic_double_fold_enorm {ℓ : ℝ} (hℓ : 0 < ℓ)
    {h : EuclideanSpace ℝ (Fin 3) → ENNReal}
    (hper : ∀ (m : Fin 3 → ℤ) (z : EuclideanSpace ℝ (Fin 3)),
      h (z + ℓ • Work.BoseBoxFock.latVec m) = h z) :
    (∫⁻ w in Work.BoseK15.corpusBox.boxL ℓ,
        (∫⁻ y in Work.BoseK15.corpusBox.boxL ℓ, h (w - y)))
      = ENNReal.ofReal (ℓ ^ 3) * (∫⁻ z in Work.BoseK15.corpusBox.boxL ℓ, h z) := by
  classical
  -- the corpus box `ℓ • [-1/2,1/2]³` is the closed cube `cell ℓ = [-ℓ/2,ℓ/2]³`
  rw [corpusBox_boxL_eq_cell hℓ]
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
      rw [latVec_neg_enf, smul_neg]
      exact hm'
    · intro g hg
      have hd : Disjoint (g +ᵥ LatFourier.latCell ℓ) (LatFourier.latCell ℓ) := by
        have h : Disjoint (latTile ℓ g) (latTile ℓ (0 : Fin 3 → ℤ)) := latTile_disjoint ℓ hℓ hg
        rw [latTile_zero_enf ℓ] at h
        exact h
      exact Disjoint.aedisjoint hd
    · intro g
      show Measure.QuasiMeasurePreserving (fun x : E3 => x + ℓ • latVec g) volume volume
      exact (measurePreserving_add_right volume (ℓ • latVec g)).quasiMeasurePreserving
  -- ## `cellI ℓ = [-ℓ/2,ℓ/2)³` is a fundamental domain (the translate of `latCell ℓ`)
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
  have htrans : ∀ (f : E3 → ENNReal), (∀ (g : Fin 3 → ℤ) (x : E3), f (g +ᵥ x) = f x) →
      ∀ a : E3, (∫⁻ z in Work.BoseFixR.cellI ℓ, f (a + z))
        = ∫⁻ z in Work.BoseFixR.cellI ℓ, f z := by
    intro f hf a
    have hPre : IsAddFundamentalDomain (Fin 3 → ℤ)
        ((fun z : E3 => (-a) + z) ⁻¹' Work.BoseFixR.cellI ℓ) volume :=
      hfdI.preimage_of_equiv (f := fun z : E3 => (-a) + z)
        (measurePreserving_add_left volume (-a)).quasiMeasurePreserving
        (e := id) Function.bijective_id fun g x => by
          show (-a) + (x + ℓ • latVec g) = ((-a) + x) + ℓ • latVec g
          abel
    have hset : (fun y : E3 => a + y) '' Work.BoseFixR.cellI ℓ
        = (fun z : E3 => (-a) + z) ⁻¹' Work.BoseFixR.cellI ℓ := by
      ext z
      constructor
      · rintro ⟨y, hy, rfl⟩
        show (-a) + (a + y) ∈ Work.BoseFixR.cellI ℓ
        rw [show (-a) + (a + y) = y from by abel]
        exact hy
      · intro hz
        exact ⟨(-a) + z, hz, by abel⟩
    rw [MeasurePreserving.setLIntegral_comp_emb (measurePreserving_add_left volume a)
      (measurableEmbedding_const_vadd a) f (Work.BoseFixR.cellI ℓ), hset]
    exact IsAddFundamentalDomain.setLIntegral_eq hPre hfdI f hf
  -- ## the key pointwise identity
  have key : ∀ w : E3, (∫⁻ y in Work.BoseFixR.cell ℓ, h (w - y))
      = ∫⁻ z in Work.BoseFixR.cell ℓ, h z := by
    intro w
    set H : E3 → ENNReal := fun z => h (-z) with hH
    have hHinv : ∀ (g : Fin 3 → ℤ) (x : E3), H (g +ᵥ x) = H x := by
      intro g x
      have h1 : -(x + ℓ • latVec g) = (-x) + ℓ • latVec (-g) := by
        rw [latVec_neg_enf, smul_neg]; abel
      show h (-(x + ℓ • latVec g)) = h (-x)
      rw [h1, hper (-g) (-x)]
    have e1 : (fun y : E3 => h (w - y)) = fun y : E3 => H ((-w) + y) := by
      funext y
      simp only [hH]
      rw [show -((-w) + y) = w - y from by abel]
    calc ∫⁻ y in Work.BoseFixR.cell ℓ, h (w - y)
        = ∫⁻ y in Work.BoseFixR.cell ℓ, H ((-w) + y) := by rw [e1]
      _ = ∫⁻ y in Work.BoseFixR.cellI ℓ, H ((-w) + y) :=
          (setLIntegral_congr_set_ae (Work.BoseFixR.cellI_ae_eq_cell ℓ) _).symm
      _ = ∫⁻ y in Work.BoseFixR.cellI ℓ, H y := htrans H hHinv (-w)
      _ = ∫⁻ y in Work.BoseFixR.cell ℓ, H y :=
          setLIntegral_congr_set_ae (Work.BoseFixR.cellI_ae_eq_cell ℓ) H
      _ = ∫⁻ y in Work.BoseFixR.cell ℓ, h (-y) := by simp only [hH]
      _ = ∫⁻ y in Work.BoseFixR.cell ℓ, h y := by
          rw [MeasurePreserving.setLIntegral_comp_emb
            (Measure.measurePreserving_neg (volume : Measure E3)) measurableEmbedding_neg h
            (Work.BoseFixR.cell ℓ), neg_image_cellR ℓ]
  -- ## the volume of the box
  have hvol : volume (Work.BoseFixR.cell ℓ) = ENNReal.ofReal (ℓ ^ 3) := by
    rw [Work.BoseFixR.cell_eq_boxL ℓ, Work.BoseFixR.volume_boxL ℓ]
  calc ∫⁻ w in Work.BoseFixR.cell ℓ, ∫⁻ y in Work.BoseFixR.cell ℓ, h (w - y)
      = ∫⁻ w in Work.BoseFixR.cell ℓ, (∫⁻ z in Work.BoseFixR.cell ℓ, h z) :=
        lintegral_congr key
    _ = (∫⁻ z in Work.BoseFixR.cell ℓ, h z) * volume (Work.BoseFixR.cell ℓ) :=
        setLIntegral_const _ _
    _ = (∫⁻ z in Work.BoseFixR.cell ℓ, h z) * ENNReal.ofReal (ℓ ^ 3) := by rw [hvol]
    _ = ENNReal.ofReal (ℓ ^ 3) * (∫⁻ z in Work.BoseFixR.cell ℓ, h z) := mul_comm _ _

end Work.BoseBoxFock
