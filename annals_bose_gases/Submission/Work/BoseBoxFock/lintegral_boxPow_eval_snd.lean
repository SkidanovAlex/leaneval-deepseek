import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseBoxFock.LatFourierDefs
import Submission.Work.MB.SlotWeakBase
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.lintegral_boxPow_eval_snd` — the fibre evaluation of the box product

The target states the elementary Fubini fact behind the box ↔ model dictionary: integrating
over the `(d+1)`-particle box `Work.MB.boxPow (d+1) l = (boxL l)^{d+1}` *and* the extra
one-particle box `boxL l` a function which only sees the `p`-th coordinate `z.1 p` of `z.1` and
the second factor `z.2` produces the free-particle integral over `boxL l × boxL l`, with the
volume of the `d`-particle box `Work.MB.boxPow d l` as the *fibre* volume (the remaining `d`
coordinates run freely over `boxL l`).

The proof is the corresponding instance of Tonelli's theorem for the measure-preserving
splitting of a `Fin (d+1)`-fold product off a coordinate, `lintegral_pi_succ_split`, which is
proved from `volume_preserving_piFinSuccAbove` (Mathlib's `Fin.insertNth` splitting of the
product measure) and `MeasureTheory.lintegral_prod_mul`.

* `prod_indicators` — the indicator of a product of sets is the product of the indicators
  (used both for the box and for its `d`-fold part).
* `lintegral_pi_succ_split` — the splitting lemma: for a set `L` in the one-particle space and
  a measurable `g : E3 → ℝ≥0∞`,
  `∫⁻ x : Fin (n+1) → E3, 1_{L^{n+1}}(x) * g (x i)
     = volume (L^n) * ∫⁻ a, 1_L a * g a`.
-/

noncomputable section

open MeasureTheory

namespace Work.BoseBoxFock

local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-- The indicator of a product of sets is the product of the indicators. -/
private lemma prod_indicators (L : Set E3) (n : ℕ) (y : Fin n → E3) :
    (Set.univ.pi (fun _ : Fin n => L)).indicator (fun _ => (1 : ENNReal)) y
      = ∏ i, L.indicator (fun _ => (1 : ENNReal)) (y i) := by
  by_cases h : y ∈ Set.univ.pi (fun _ : Fin n => L)
  · rw [Set.indicator_of_mem h]
    rw [Finset.prod_eq_one (fun i _ => Set.indicator_of_mem (Set.mem_univ_pi.mp h i) _)]
  · rw [Set.indicator_of_notMem h]
    obtain ⟨i, hi⟩ := not_forall.mp (fun hall => h (Set.mem_univ_pi.mpr hall))
    exact (Finset.prod_eq_zero (Finset.mem_univ i) (Set.indicator_of_notMem hi _)).symm

/-- **The splitting identity.**  Integrating the `(n+1)`-fold product box against a function of
the single coordinate `i` produces the volume of the remaining `n`-fold box times the integral
over one box.  Proved by the measure-preserving `Fin.insertNth` splitting of the product
measure (`volume_preserving_piFinSuccAbove`) and Tonelli. -/
private lemma lintegral_pi_succ_split (n : ℕ) (i : Fin (n + 1)) (L : Set E3)
    (hL : MeasurableSet L) (g : E3 → ENNReal) (hg : Measurable g) :
    ∫⁻ x : Fin (n + 1) → E3,
        (Set.univ.pi (fun _ : Fin (n + 1) => L)).indicator (fun _ => (1 : ENNReal)) x * g (x i)
      = (volume (Set.univ.pi (fun _ : Fin n => L)))
        * ∫⁻ a, L.indicator (fun _ => (1 : ENNReal)) a * g a := by
  have hmp : MeasurePreserving (⇑(MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n+1) => E3) i))
      (volume : Measure (Fin (n+1) → E3)) (volume : Measure (E3 × (Fin n → E3))) :=
    volume_preserving_piFinSuccAbove (fun _ : Fin (n+1) => E3) i
  have hQ : Measurable (L.indicator (fun _ : E3 => (1 : ENNReal))) :=
    Measurable.indicator measurable_const hL
  have hmeas : Measurable (fun x : Fin (n + 1) → E3 =>
      (Set.univ.pi (fun _ : Fin (n + 1) => L)).indicator (fun _ => (1 : ENNReal)) x * g (x i)) :=
    (Measurable.indicator measurable_const (MeasurableSet.univ_pi (fun _ => hL))).mul
      (hg.comp (measurable_pi_apply i))
  rw [← (hmp.symm.lintegral_comp hmeas)]
  have hpt : ∀ z : E3 × (Fin n → E3),
      (Set.univ.pi (fun _ : Fin (n + 1) => L)).indicator (fun _ => (1 : ENNReal))
          ((MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n+1) => E3) i).symm z)
        * g (((MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n+1) => E3) i).symm z) i)
      = (L.indicator (fun _ => (1 : ENNReal)) z.1 * g z.1)
        * ∏ j, L.indicator (fun _ => (1 : ENNReal)) (z.2 j) := by
    rintro ⟨a, r⟩
    rw [prod_indicators, Fin.prod_univ_succAbove _ i]
    simp only [MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv_apply,
      Fin.insertNth_apply_same, Fin.insertNth_apply_succAbove]
    exact mul_right_comm (L.indicator (fun _ => (1 : ENNReal)) a)
      (∏ j, L.indicator (fun _ => (1 : ENNReal)) (r j)) (g a)
  rw [MeasureTheory.lintegral_congr hpt]
  have hh : Measurable (fun r : Fin n → E3 =>
      ∏ j, L.indicator (fun _ : E3 => (1 : ENNReal)) (r j)) :=
    Finset.measurable_prod Finset.univ (fun j _ => hQ.comp (measurable_pi_apply j))
  rw [MeasureTheory.Measure.volume_eq_prod E3 (Fin n → E3)]
  rw [show (∫⁻ a : E3 × (Fin n → E3),
        L.indicator (fun _ => (1 : ENNReal)) a.1 * g a.1
          * ∏ j, L.indicator (fun _ => (1 : ENNReal)) (a.2 j) ∂volume.prod volume)
      = ∫⁻ z : E3 × (Fin n → E3),
          ((L.indicator (fun _ => (1 : ENNReal))) * g) z.1
            * (fun r : Fin n → E3 => ∏ j, L.indicator (fun _ => (1 : ENNReal)) (r j)) z.2
          ∂volume.prod volume from rfl]
  rw [MeasureTheory.lintegral_prod_mul (μ := (volume : Measure E3))
    (ν := (volume : Measure (Fin n → E3))) (hQ.mul hg).aemeasurable hh.aemeasurable]
  have hrest : (∫⁻ (r : Fin n → E3), ∏ j, L.indicator (fun _ => (1 : ENNReal)) (r j))
      = volume (Set.univ.pi (fun _ : Fin n => L)) := by
    rw [show (∫⁻ (r : Fin n → E3), ∏ j, L.indicator (fun _ => (1 : ENNReal)) (r j))
        = ∫⁻ (r : Fin n → E3),
            (Set.univ.pi (fun _ : Fin n => L)).indicator (fun _ => (1 : ENNReal)) r from
      MeasureTheory.lintegral_congr (fun r => (prod_indicators L n r).symm)]
    exact MeasureTheory.lintegral_indicator_one (MeasurableSet.univ_pi (fun _ => hL))
  rw [hrest, mul_comm]
  rfl

theorem lintegral_boxPow_eval_snd {d : ℕ} (p : Fin (d + 1)) {l : ℝ}
    {F : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3) → ENNReal}
    (hF : Measurable (Function.uncurry F)) :
    ∫⁻ z : Work.BoseDict.Xn (d + 1) × EuclideanSpace ℝ (Fin 3),
        (Work.MB.boxPow (d + 1) l).indicator (fun _ => 1) z.1
          * (Work.BoseK15.corpusBox.boxL l).indicator (fun _ => 1) z.2
          * F (z.1 p) z.2
      = (MeasureTheory.volume (Work.MB.boxPow d l))
          * ∫⁻ q : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3),
              (Work.BoseK15.corpusBox.boxL l).indicator (fun _ => 1) q.1
                * (Work.BoseK15.corpusBox.boxL l).indicator (fun _ => 1) q.2 * F q.1 q.2 := by
  have hL : MeasurableSet (Work.BoseK15.corpusBox.boxL l) :=
    Work.BoseB4.BoxData.boxL_measurableSet _ l
  have hQ : Measurable ((Work.BoseK15.corpusBox.boxL l).indicator (fun _ : E3 => (1 : ENNReal))) :=
    Measurable.indicator measurable_const hL
  have hPset : MeasurableSet (Work.MB.boxPow (d + 1) l) :=
    MeasurableSet.univ_pi (fun _ : Fin (d + 1) => hL)
  have hP : Measurable ((Work.MB.boxPow (d + 1) l).indicator
      (fun _ : Work.BoseDict.Xn (d + 1) => (1 : ENNReal))) :=
    Measurable.indicator measurable_const hPset
  have hFfix : ∀ a : E3, Measurable (fun y : E3 => F a y) := fun a =>
    hF.comp (by fun_prop : Measurable (fun y : E3 => (a, y)))
  have hF2 : Measurable (fun z : Work.BoseDict.Xn (d + 1) × E3 => F (z.1 p) z.2) :=
    hF.comp (by fun_prop : Measurable (fun z : Work.BoseDict.Xn (d + 1) × E3 => (z.1 p, z.2)))
  have hmeas : AEMeasurable (fun z : Work.BoseDict.Xn (d + 1) × E3 =>
      (Work.MB.boxPow (d + 1) l).indicator (fun _ => (1 : ENNReal)) z.1
        * (Work.BoseK15.corpusBox.boxL l).indicator (fun _ => (1 : ENNReal)) z.2
        * F (z.1 p) z.2)
      (((volume : Measure (Work.BoseDict.Xn (d + 1)))).prod (volume : Measure E3)) :=
    (((hP.comp measurable_fst).mul (hQ.comp measurable_snd)).mul hF2).aemeasurable
  rw [MeasureTheory.Measure.volume_eq_prod (Work.BoseDict.Xn (d + 1)) E3]
  rw [MeasureTheory.lintegral_prod _ hmeas]
  let g : E3 → ENNReal := fun a => ∫⁻ y : E3, (Work.BoseK15.corpusBox.boxL l).indicator
      (fun _ => (1 : ENNReal)) y * F a y
  have hg : Measurable g := by
    show Measurable (fun a : E3 => ∫⁻ y : E3, (Work.BoseK15.corpusBox.boxL l).indicator
      (fun _ => (1 : ENNReal)) y * F a y)
    exact Measurable.lintegral_prod_right (by
      show Measurable (fun z : E3 × E3 => (Work.BoseK15.corpusBox.boxL l).indicator
        (fun _ => (1 : ENNReal)) z.2 * F z.1 z.2)
      exact (hQ.comp measurable_snd).mul hF)
  have hstep : ∀ x : Work.BoseDict.Xn (d + 1),
      (∫⁻ y : E3, (Work.MB.boxPow (d + 1) l).indicator (fun _ => (1 : ENNReal)) x
          * (Work.BoseK15.corpusBox.boxL l).indicator (fun _ => (1 : ENNReal)) y * F (x p) y)
        = (Work.MB.boxPow (d + 1) l).indicator (fun _ => (1 : ENNReal)) x * g (x p) := by
    intro x
    rw [show (∫⁻ y : E3, (Work.MB.boxPow (d + 1) l).indicator (fun _ => (1 : ENNReal)) x
          * (Work.BoseK15.corpusBox.boxL l).indicator (fun _ => (1 : ENNReal)) y * F (x p) y)
        = ∫⁻ y : E3, (Work.MB.boxPow (d + 1) l).indicator (fun _ => (1 : ENNReal)) x
          * (fun y' : E3 => (Work.BoseK15.corpusBox.boxL l).indicator (fun _ => (1 : ENNReal)) y'
              * F (x p) y') y from
      MeasureTheory.lintegral_congr (fun y => mul_assoc _ _ _)]
    exact MeasureTheory.lintegral_const_mul (μ := (volume : Measure E3))
      (r := (Work.MB.boxPow (d + 1) l).indicator (fun _ => (1 : ENNReal)) x)
      (f := fun y' : E3 => (Work.BoseK15.corpusBox.boxL l).indicator (fun _ => (1 : ENNReal)) y'
        * F (x p) y') (hQ.mul (hFfix (x p)))
  rw [MeasureTheory.lintegral_congr hstep]
  simp only [Work.MB.boxPow]
  rw [lintegral_pi_succ_split d p (Work.BoseK15.corpusBox.boxL l) hL g hg]
  have hfinal : (∫⁻ a : E3, (Work.BoseK15.corpusBox.boxL l).indicator (fun _ => (1 : ENNReal)) a
        * g a) = ∫⁻ q : E3 × E3,
        (Work.BoseK15.corpusBox.boxL l).indicator (fun _ => (1 : ENNReal)) q.1
          * (Work.BoseK15.corpusBox.boxL l).indicator (fun _ => (1 : ENNReal)) q.2 * F q.1 q.2 := by
    have h1 : (∫⁻ a : E3, (Work.BoseK15.corpusBox.boxL l).indicator (fun _ => (1 : ENNReal)) a
        * g a) = ∫⁻ a : E3, ∫⁻ y : E3,
          (Work.BoseK15.corpusBox.boxL l).indicator (fun _ => (1 : ENNReal)) a
            * ((Work.BoseK15.corpusBox.boxL l).indicator (fun _ => (1 : ENNReal)) y * F a y) := by
      refine MeasureTheory.lintegral_congr (fun a => ?_)
      show (Work.BoseK15.corpusBox.boxL l).indicator (fun _ => (1 : ENNReal)) a
          * (fun a' : E3 => ∫⁻ y : E3, (Work.BoseK15.corpusBox.boxL l).indicator
              (fun _ => (1 : ENNReal)) y * F a' y) a
        = ∫⁻ y : E3, (Work.BoseK15.corpusBox.boxL l).indicator (fun _ => (1 : ENNReal)) a
            * (fun y' : E3 => (Work.BoseK15.corpusBox.boxL l).indicator (fun _ => (1 : ENNReal)) y'
                * F a y') y
      exact (MeasureTheory.lintegral_const_mul (μ := (volume : Measure E3))
        (r := (Work.BoseK15.corpusBox.boxL l).indicator (fun _ => (1 : ENNReal)) a)
        (f := fun y' : E3 => (Work.BoseK15.corpusBox.boxL l).indicator (fun _ => (1 : ENNReal)) y'
          * F a y') (hQ.mul (hFfix a))).symm
    have h2 : (∫⁻ a : E3, ∫⁻ y : E3,
          (Work.BoseK15.corpusBox.boxL l).indicator (fun _ => (1 : ENNReal)) a
            * ((Work.BoseK15.corpusBox.boxL l).indicator (fun _ => (1 : ENNReal)) y * F a y))
        = ∫⁻ a : E3, ∫⁻ y : E3,
          (Work.BoseK15.corpusBox.boxL l).indicator (fun _ => (1 : ENNReal)) a
            * (Work.BoseK15.corpusBox.boxL l).indicator (fun _ => (1 : ENNReal)) y * F a y := by
      refine MeasureTheory.lintegral_congr (fun a => ?_)
      exact MeasureTheory.lintegral_congr (fun y => (mul_assoc _ _ _).symm)
    rw [h1, h2, MeasureTheory.Measure.volume_eq_prod E3 E3]
    rw [MeasureTheory.lintegral_prod (fun z : E3 × E3 =>
        (Work.BoseK15.corpusBox.boxL l).indicator (fun _ => (1 : ENNReal)) z.1
          * (Work.BoseK15.corpusBox.boxL l).indicator (fun _ => (1 : ENNReal)) z.2 * F z.1 z.2)
      (((hQ.comp measurable_fst).mul (hQ.comp measurable_snd)).mul hF).aemeasurable]
  rw [hfinal]

end Work.BoseBoxFock
