import Mathlib
import Submission.Work.EKLContract.Defs
import Submission.Work.EKLProd.sl3EntryBox_compact
import Submission.Work.MeasureTheory.ext_of_ratBox_ratio
import Submission.Work.EKLRelCross.Instances

/-!
# The countable ("Bad") set of the C5b globalisation, and its measurability

The last step of the C5b derivation (`EKLComp/ProductPlan.md` §11.3) needs a *Borel* set `Bad`
which contains every point at which the frozen conclusion

`νH z = c • (mul_*)(νT z ⊗ νU z)`  (`c > 0`)

fails, so that `μ Bad = 0` (proved by the `condexp` argument,
`Work.EKLGlobal.measure_zero_of_ae_leafwise_null_cover`) upgrades to the conclusion `μ`-a.e.

Here we provide the *countable* definition of that set: instead of the uncountable quantifiers of
the frozen statement we test the proportionality of the two measures on the countably many boxes
`ratBox(a,b) ∩ {|g| ≤ N}` (`a,b` rational, `N ∈ ℕ`).  By
`Work.MeasureTheory.ext_of_ratBox_ratio` the countable condition implies the proportionality of
the measures, hence the frozen conclusion; and the countable condition is measurable as soon as
the two measure-valued maps are.

Note the use of the *measurable surrogate* of a leafwise system
(`Work.EKLGlobal.exists_measurable_ae_eq_of_isLeafwise`): it differs from `ν` only on a `μ`-null
set, so the resulting `Bad` is still `μ`-null.
-/

open MeasureTheory
open scoped ENNReal

set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option maxHeartbeats 800000

noncomputable section

namespace Work.EKLGlobal

open Work.EKLContract

/-- The boxes on which the proportionality is tested. -/
def ratioBox (a b : Matrix (Fin 3) (Fin 3) ℚ) (N : ℕ) : Set SL3 :=
  {g : SL3 | (∀ i j, (a i j : ℝ) ≤ g i j ∧ g i j ≤ (b i j : ℝ)) ∧ ∀ i j, |g i j| ≤ (N : ℝ)}

theorem measurableSet_ratioBox (a b : Matrix (Fin 3) (Fin 3) ℚ) (N : ℕ) :
    MeasurableSet (ratioBox a b N) := by
  have h1 : IsCompact {g : SL3 | ∀ i j, (a i j : ℝ) ≤ g i j ∧ g i j ≤ (b i j : ℝ)} :=
    Work.EKLProd.sl3EntryBox_compact (fun i j => (a i j : ℝ)) (fun i j => (b i j : ℝ))
  have h2 : IsCompact {g : SL3 | ∀ i j, -(N : ℝ) ≤ g i j ∧ g i j ≤ (N : ℝ)} :=
    Work.EKLProd.sl3EntryBox_compact (fun _ _ => -(N : ℝ)) (fun _ _ => (N : ℝ))
  have h3 : ratioBox a b N = {g : SL3 | ∀ i j, (a i j : ℝ) ≤ g i j ∧ g i j ≤ (b i j : ℝ)} ∩
      {g : SL3 | ∀ i j, -(N : ℝ) ≤ g i j ∧ g i j ≤ (N : ℝ)} := by
    ext g
    simp only [ratioBox, Set.mem_setOf_eq, Set.mem_inter_iff, abs_le]
  rw [h3]
  exact (h1.inter h2).isClosed.measurableSet

/-- **The countable goodness predicate.**  The two measures are proportional on every rational box,
with a rational proportionality constant. -/
def goodRatio (νH P : X3 → Measure SL3) : Set X3 :=
  {z | ∃ c : ℚ, 0 < c ∧ ∀ (a b : Matrix (Fin 3) (Fin 3) ℚ) (N : ℕ),
    (νH z) (ratioBox a b N) = ENNReal.ofReal (c : ℝ) * (P z) (ratioBox a b N)}

/-- **Measurability of the countable goodness predicate.** -/
theorem measurableSet_goodRatio {νH P : X3 → Measure SL3} (hH : Measurable νH) (hP : Measurable P) :
    MeasurableSet (goodRatio νH P) := by
  haveI : Countable (Matrix (Fin 3) (Fin 3) ℚ) := by unfold Matrix; infer_instance
  haveI : Countable (Matrix (Fin 3) (Fin 3) ℚ × Matrix (Fin 3) (Fin 3) ℚ × ℕ) := inferInstance
  have hsingle : ∀ c : ℚ, MeasurableSet {z : X3 | 0 < c ∧ ∀ (a b : Matrix (Fin 3) (Fin 3) ℚ)
      (N : ℕ), (νH z) (ratioBox a b N) = ENNReal.ofReal (c : ℝ) * (P z) (ratioBox a b N)} := by
    intro c
    by_cases hc : 0 < c
    · have : {z : X3 | 0 < c ∧ ∀ (a b : Matrix (Fin 3) (Fin 3) ℚ) (N : ℕ),
          (νH z) (ratioBox a b N) = ENNReal.ofReal (c : ℝ) * (P z) (ratioBox a b N)}
          = ⋂ (p : Matrix (Fin 3) (Fin 3) ℚ × Matrix (Fin 3) (Fin 3) ℚ × ℕ),
            {z : X3 | (νH z) (ratioBox p.1 p.2.1 p.2.2)
              = ENNReal.ofReal (c : ℝ) * (P z) (ratioBox p.1 p.2.1 p.2.2)} := by
        ext z
        simp only [Set.mem_setOf_eq, Set.mem_iInter, hc, true_and]
        exact ⟨fun h p => h p.1 p.2.1 p.2.2, fun h a b N => h (a, b, N)⟩
      rw [this]
      refine MeasurableSet.iInter fun p => ?_
      exact measurableSet_eq_fun
        ((Measure.measurable_coe (measurableSet_ratioBox p.1 p.2.1 p.2.2)).comp hH)
        (((Measure.measurable_coe (measurableSet_ratioBox p.1 p.2.1 p.2.2)).comp hP).const_mul _)
    · have : {z : X3 | 0 < c ∧ ∀ (a b : Matrix (Fin 3) (Fin 3) ℚ) (N : ℕ),
          (νH z) (ratioBox a b N) = ENNReal.ofReal (c : ℝ) * (P z) (ratioBox a b N)} = ∅ := by
        ext z
        simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_and]
        exact fun h => absurd h hc
      rw [this]
      exact MeasurableSet.empty
  rw [show goodRatio νH P = ⋃ c : ℚ, {z : X3 | 0 < c ∧ ∀ (a b : Matrix (Fin 3) (Fin 3) ℚ)
      (N : ℕ), (νH z) (ratioBox a b N) = ENNReal.ofReal (c : ℝ) * (P z) (ratioBox a b N)} from by
    simp only [goodRatio, Set.setOf_exists]]
  exact MeasurableSet.iUnion hsingle

/-- The convolution measure of the pair `(νT, νU)`. -/
def conv (νT νU : Measure SL3) : Measure SL3 :=
  (νT.prod νU).map (fun p : SL3 × SL3 => p.1 * p.2)

/-- **The countable goodness predicate implies the proportionality of the measures**, by the
π-system argument of `Work.MeasureTheory.ext_of_ratBox_ratio` (the test boxes `ratioBox a b N`
are exactly the rational boxes intersected with the compact exhaustion). -/
theorem proportional_of_goodRatio {νH P : X3 → Measure SL3} {z : X3}
    (hH : ∀ K : Set SL3, IsCompact K → (νH z) K < ⊤)
    (hP : ∀ K : Set SL3, IsCompact K → (P z) K < ⊤)
    (hz : z ∈ goodRatio νH P) :
    ∃ c : ℝ, 0 < c ∧ νH z = ENNReal.ofReal c • P z := by
  obtain ⟨c, hc, hbox⟩ := hz
  exact ⟨(c : ℝ), by exact_mod_cast hc,
    Work.MeasureTheory.ext_of_ratBox_ratio hH hP (c : ℝ) (by exact_mod_cast hc) hbox⟩

/-- **Fubini for the convolution**: the integral against `conv` is the iterated integral appearing
in the frozen statement of `P_Product`.  The integrality hypothesis is automatic in the leafwise
setting (the convolution of two Radon measures, tested against a compactly supported function);
where it fails both sides are `0` by `integral_undef`. -/
theorem integral_conv {νT νU : Measure SL3} [SFinite νT] [SFinite νU] (f : CompactlySupportedContinuousMap SL3 ℝ)
    (hint : Integrable (fun p : SL3 × SL3 => f (p.1 * p.2)) (νT.prod νU)) :
    ∫ g, f g ∂(conv νT νU) = ∫ t, (∫ u, f (t * u) ∂νU) ∂νT := by
  rw [conv, MeasureTheory.integral_map (φ := fun p : SL3 × SL3 => p.1 * p.2)
    (f := fun g : SL3 => f g) (measurable_fst.mul measurable_snd).aemeasurable f.continuous.aestronglyMeasurable]
  exact MeasureTheory.integral_prod (fun p : SL3 × SL3 => f (p.1 * p.2)) hint

end Work.EKLGlobal
