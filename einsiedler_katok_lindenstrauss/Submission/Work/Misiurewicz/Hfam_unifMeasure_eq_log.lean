import Mathlib
import Submission.Work.EKLContract.Defs
import Submission.Work.EKLComp.Misiurewicz.Defs
import Submission.Work.Misiurewicz.card_atoms_eq_card
import Submission.Work.Misiurewicz.sum_negMulLog_div_eq_log

/-!
# `Hfam (unifMeasure E) A = log |E|` for a partition `A` separating `E`

`Work.EKLComp.unifMeasure E` is the uniform probability measure on a finite set `E ⊆ X₃`, and
`Work.EKLContract.Hfam μ A = ∑ i, Real.negMulLog (μ (A i)).toReal` is the Shannon entropy of a
finite family `A` of measurable sets.  The lemma below computes the entropy of the uniform
measure with respect to a countable partition `A` of `X₃` which is *separating on `E`*: the
membership pattern `i ↦ [x ∈ A i]` determines a point of `E` (`hinj`).  Under that hypothesis
every atom `A i` carries at most one point of `E`, so `μ (A i)` is either `0` or `1/|E|`, and
exactly `|E|` atoms have mass `1/|E|`:

`H_μ(A) = |E| · negMulLog (1/|E|) = |E| · (log |E|)/|E| = log |E|`.

This is the "base case" estimate of the Misiurewicz construction (`P_Misiurewicz`): the uniform
measure on a maximal separated set has entropy `log` of its cardinality.

The proof is split into three independent ingredients:

* `unifMeasure_apply_toReal` — the mass of a measurable set under `unifMeasure E`, computed by
  expanding the defining finite sum of Dirac masses;
* `Work.Misiurewicz.card_atoms_eq_card` — the combinatorics: with `A` a partition and `hinj`,
  each atom meets `E` in at most one point, and exactly `|E|` atoms meet `E`;
* `Work.Misiurewicz.sum_negMulLog_div_eq_log` — the numerical identity
  `∑ i, negMulLog (m i / n) = log n` for `m i ∈ {0,1}` with exactly `n` indices equal to `1`.
-/

open Classical
open MeasureTheory
open scoped ENNReal

namespace Work.Misiurewicz

open Work.EKLContract Work.EKLComp

/-- The mass of an arbitrary set under the uniform measure on `E`: expanding the defining finite
combination of Dirac masses, `(unifMeasure E) S` is `|E ∩ S| / |E|`, counted as an `ℝ≥0∞`
element.  (No measurability is needed here since the summands are Dirac measures.) -/
lemma unifMeasure_apply (E : Finset X3) (S : Set X3) (hS : MeasurableSet S) :
    (unifMeasure E) S = (E.card : ℝ≥0∞)⁻¹ * (↑(E.filter (fun x => x ∈ S)).card : ℝ≥0∞) := by
  rw [unifMeasure, Measure.smul_apply, Measure.finsetSum_apply]
  congr 1
  rw [← Finset.sum_boole (fun x => x ∈ S) E]
  refine Finset.sum_congr rfl (fun x hx => ?_)
  rw [Measure.dirac_apply' _ hS]
  rfl

/-- The real-valued mass of a measurable set under `unifMeasure E`: `.toReal` of
`unifMeasure_apply`. -/
lemma unifMeasure_apply_toReal (E : Finset X3) (S : Set X3) (hS : MeasurableSet S) :
    ((unifMeasure E) S).toReal = ((E.filter (fun x => x ∈ S)).card : ℝ) / (E.card : ℝ) := by
  rw [unifMeasure_apply E S hS, ENNReal.toReal_mul, ENNReal.toReal_inv, ENNReal.toReal_natCast,
    ENNReal.toReal_natCast]
  ring

/-- Bridge between the two ways of counting the points of a finite set `E` lying in a set `S`:
`Set.ncard` of the intersection and the cardinality of the filtered finset.  The `Set.ncard`
version is the one used in `Work.Misiurewicz.card_atoms_eq_card`, since it does not require a
decidability instance on `S`. -/
lemma ncard_inter_coe_finset (E : Finset X3) (S : Set X3) :
    (S ∩ (E : Set X3)).ncard = (E.filter (fun x => x ∈ S)).card := by
  rw [← Set.ncard_coe_finset (E.filter (fun x => x ∈ S))]
  congr 1
  ext x
  simp [Set.mem_inter_iff, and_comm]

theorem Hfam_unifMeasure_eq_log (E : Finset Work.EKLContract.X3) {ι : Type*} [Fintype ι]
    (A : ι → Set Work.EKLContract.X3) (hdisj : Pairwise (fun i j => Disjoint (A i) (A j)))
    (hcov : ⋃ i, A i = Set.univ) (hmeas : ∀ i, MeasurableSet (A i))
    (hinj : ∀ x ∈ E, ∀ y ∈ E, (∀ i, x ∈ A i ↔ y ∈ A i) → x = y) :
    Work.EKLContract.Hfam (Work.EKLComp.unifMeasure E) A = Real.log (E.card : ℝ) := by
  classical
  -- `|A i ∩ E|` : `0` or `1` by `hinj`, and `1` for exactly `|E|` indices.
  obtain ⟨hle, hcard⟩ := card_atoms_eq_card E A hdisj hcov hinj
  -- The measure of an atom, in terms of `|A i ∩ E|`.
  have hstep : ∀ i, ((unifMeasure E) (A i)).toReal
      = (((A i ∩ (E : Set X3)).ncard : ℝ)) / (E.card : ℝ) := by
    intro i
    rw [unifMeasure_apply_toReal E (A i) (hmeas i), ← ncard_inter_coe_finset E (A i)]
  simp only [Work.EKLContract.Hfam, hstep]
  exact sum_negMulLog_div_eq_log (fun i => (A i ∩ (E : Set X3)).ncard) E.card hle hcard

end Work.Misiurewicz
