import Mathlib
import Submission.Work.EKLC6Route.Defs
import Submission.Work.EKLC6Route.chartSet_measurable
import Submission.Work.EKLC6Core.firstReturn_partition

namespace Work.EKLC6Route

open MeasureTheory Filter Topology
open Work.EKLContract Work.EKLC6Core

/-- `dev` is continuous: it is the finite supremum of the absolute values of the entries of
`g - 1`, and each entry map `g ↦ g i j` is continuous. -/
private lemma continuous_dev : Continuous (dev : SL3 → ℝ) := by
  unfold dev
  refine Continuous.finset_sup'_apply Finset.univ_nonempty (fun p _ => ?_)
  fun_prop

/-- The `dev`-defect of the chart coordinate, `z ↦ dev (uc z)`, is measurable. -/
private lemma measurable_dev_comp {μ : MeasureTheory.Measure Work.EKLContract.X3}
    {t : Fin 3 → ℝ} (w : Window μ t) : Measurable (fun z : X3 => dev (w.uc z)) :=
  continuous_dev.measurable.comp w.huc

/-- Each entry `k ↦ gridIdx ρ L k a b` of the grid index map is measurable: `⌊·⌋` of a measurable
real function. -/
private lemma measurable_gridIdx_apply (ρ : ℝ) (L : ℕ) (a b : Fin 3) :
    Measurable (fun k : SL3 => gridIdx ρ L k a b) := by
  have hc : Continuous (fun k : SL3 => (k : Matrix (Fin 3) (Fin 3) ℝ) a b) := by fun_prop
  have h1 : Measurable (fun k : SL3 => (k : Matrix (Fin 3) (Fin 3) ℝ) a b) := hc.measurable
  have h2 : Measurable (fun k : SL3 =>
      ((k : Matrix (Fin 3) (Fin 3) ℝ) a b - (1 : Matrix (Fin 3) (Fin 3) ℝ) a b) * 2 ^ L / ρ) :=
    Measurable.div_const (Measurable.mul_const (h1.sub measurable_const) _) ρ
  simpa only [gridIdx] using (Measurable.floor h2)

/-- The grid index map `k ↦ gridIdx ρ L k` into `Fin 3 → Fin 3 → ℤ` is measurable. -/
private lemma measurable_gridIdx (ρ : ℝ) (L : ℕ) :
    Measurable (fun k : SL3 => gridIdx ρ L k) :=
  measurable_pi_iff.mpr fun a => measurable_pi_iff.mpr fun b => measurable_gridIdx_apply ρ L a b

/-- All the sets attached to a window are Borel, and `w.dU` is a measurable function.
* `w.W = chartSet t z0 uc θ r ρ` is Borel by `Work.EKLC6Route.chartSet_measurable` (`w.huc`, `w.hθ`);
* `w.dU = if z ∈ chartSet t z0 uc θ (2 * r) ρ then |dev (uc z) - r| else r` is measurable because the
  chart set `(2 * r)` is Borel (`chartSet_measurable`) and `dev ∘ w.uc : X₃ → ℝ` is measurable
  (`dev` is a finite supremum of absolute values of matrix entries, hence continuous);
* `w.N0 = neverReturnSet t w.W ∪ {z | w.dU z = 0}` is Borel by
  `Work.EKLC6Core.firstReturn_partition` (its `neverReturnSet` clause) and `Measurable w.dU`;
* `w.piece p` is Borel in each of the three cases: `(w.W ∪ w.N0)ᶜ`, `w.N0`, and
  `w.D i J c = (firstReturnSet t w.W i ∩ w.Jset J ∩ {x | gridIdx ρ (gridLev t i) (θ x) = c}) \ N0`
  (`firstReturn_partition` for `firstReturnSet`, `w.hCmeas`/`w.hθ` for `Jset`, `⌊·⌋` of a measurable
  real function for the grid class). -/
theorem piece_measurable {μ : MeasureTheory.Measure Work.EKLContract.X3}
    [MeasureTheory.IsProbabilityMeasure μ] {t : Fin 3 → ℝ} (w : Work.EKLC6Route.Window μ t) :
    (MeasurableSet w.W) ∧ (Measurable w.dU) ∧ (MeasurableSet w.N0) ∧
    (∀ p : Work.EKLC6Route.Window.PIdx, MeasurableSet (w.piece p)) := by
  classical
  have hdevuc : Measurable (fun z : X3 => dev (w.uc z)) := measurable_dev_comp w
  -- `w.W` is the chart set.
  have hW : MeasurableSet w.W := by
    show MeasurableSet (chartSet t w.z0 w.uc w.θ w.r w.ρ)
    exact chartSet_measurable w.huc w.hθ w.r w.ρ
  -- `w.dU` is a two-branch measurable function across the Borel chart set at radius `2 * w.r`.
  have hdU : Measurable w.dU := by
    show Measurable (fun z : X3 =>
      if z ∈ chartSet t w.z0 w.uc w.θ (2 * w.r) w.ρ then |dev (w.uc z) - w.r| else w.r)
    exact Measurable.ite (chartSet_measurable w.huc w.hθ (2 * w.r) w.ρ)
      (hdevuc.sub measurable_const).abs measurable_const
  -- The first-return partition of the window set.
  have hpart := firstReturn_partition (t := t) hW
  have hnr : MeasurableSet (neverReturnSet t w.W) := hpart.2.1
  have hN0 : MeasurableSet w.N0 := by
    show MeasurableSet (neverReturnSet t w.W ∪ {z : X3 | w.dU z = 0})
    exact hnr.union (hdU (measurableSet_singleton 0))
  -- `w.Jset J` is Borel: it is `w.W` cut by the `θ`-preimage of a Borel subset of `SL₃`.
  have hJset : ∀ J : Option ℕ, MeasurableSet (w.Jset J) := by
    intro J
    cases J with
    | none =>
      show MeasurableSet (w.W ∩ w.θ ⁻¹' (⋂ i, w.C i))
      exact hW.inter (w.hθ (MeasurableSet.iInter fun i => w.hCmeas i))
    | some j =>
      show MeasurableSet (w.W ∩ w.θ ⁻¹' (w.C j \ w.C (j + 1)))
      exact hW.inter (w.hθ ((w.hCmeas j).diff (w.hCmeas (j + 1))))
  -- The pieces `w.D i J c`.
  have hD : ∀ (i : ℕ) (J : Option ℕ) (c : Fin 3 → Fin 3 → ℤ), MeasurableSet (w.D i J c) := by
    intro i J c
    show MeasurableSet (if i = 0 then (∅ : Set X3) else
      (firstReturnSet t w.W i ∩ w.Jset J ∩
        {x : X3 | gridIdx w.ρ (gridLev t i) (w.θ x) = c}) \ w.N0)
    by_cases hi : i = 0
    · rw [if_pos hi]
      exact MeasurableSet.empty
    · rw [if_neg hi]
      exact (((hpart.1 i).inter (hJset J)).inter
        ((measurable_gridIdx w.ρ (gridLev t i)).comp w.hθ
          (measurableSet_singleton c))).diff hN0
  refine ⟨hW, hdU, hN0, fun p => ?_⟩
  cases p with
  | none =>
    show MeasurableSet (w.W ∪ w.N0)ᶜ
    exact (hW.union hN0).compl
  | some p =>
    cases p with
    | none =>
      show MeasurableSet w.N0
      exact hN0
    | some q =>
      show MeasurableSet (w.D q.1 q.2.1 q.2.2)
      exact hD q.1 q.2.1 q.2.2

end Work.EKLC6Route
