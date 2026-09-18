/-
# The mass transference principle in `ℝ`, `k = 1`, `f(r) = r ^ d`, `0 < d < 1`

This file assembles the proof of `massTransferencePrincipleOne`, the Beresnevich–Velani
mass transference principle in `ℝ` for the power dimension function `f(r) = r ^ d`
(`0 < d < 1`), for an arbitrary countable index type.  The statement is definitionally the
same as `Submission.Main.MTPStatement`.

Structure of the proof:

* `full_measure_pos` (`Basic.lean`) transfers the full measure hypothesis from the enlarged
  intervals over all radii to those over positive radii;
* `existsTreeData` (`Tree/Exists.lean`), using the local level construction
  (`Tree/existsLocal1.lean`) and the fold over the parents, produces the Cantor tree
  `TreeData d c ρ η` for every `η > 0`;
* `cantorSubset` identifies the Cantor set of the tree as a subset of the small limsup set
  intersected with `[0,1]`;
* `cantorHausdorff` shows that the Cantor set has `d`-dimensional Hausdorff measure at least
  `η / 400`; since `η` is arbitrary, the measure is `⊤`;
* finally `Work.BV.MTPStatement_of_SeqMTP` ([`Submission/Work/BV/MTPStatement_of_SeqMTP.lean`])
  turns the `ℕ`-indexed statement into the general countable one.
-/
import Submission.Work.MassTransferenceAlt.Tree.Exists
import Submission.Work.MassTransferenceAlt.Tree.existsLocal1
import Submission.Work.MassTransferenceAlt.Tree.cantorSubset
import Submission.Work.MassTransferenceAlt.Tree.cantorHausdorff
import Submission.Work.BV.MTPStatement_of_SeqMTP

open MeasureTheory Set Metric
open scoped ENNReal NNReal

namespace Work.MassTransferenceAlt

/-- **The mass transference principle, `ℕ`-indexed form.** -/
theorem massTransferencePrincipleSeq (d : ℝ) (hd0 : 0 < d) (hd1 : d < 1) (c ρ : ℕ → ℝ)
    (hρ : ∀ i, 0 ≤ ρ i)
    (hρfin : ∀ ε : ℝ, 0 < ε → {i : ℕ | ε ≤ ρ i}.Finite)
    (hfull : ∀ x y : ℝ, 0 ≤ x → y ≤ 1 →
      MeasureTheory.Measure.hausdorffMeasure 1
        (Set.Icc x y ∩ {z : ℝ | {n : ℕ | |z - c n| ≤ (ρ n) ^ d}.Infinite})
        = MeasureTheory.Measure.hausdorffMeasure 1 (Set.Icc x y)) :
    MeasureTheory.Measure.hausdorffMeasure d
      (Set.Icc (0 : ℝ) 1 ∩ {z : ℝ | {n : ℕ | |z - c n| ≤ ρ n}.Infinite}) = ⊤ := by
  classical
  -- the full measure hypothesis for the positive radii
  have hfull' : ∀ a b : ℝ, 0 ≤ a → b ≤ 1 →
      MeasureTheory.Measure.hausdorffMeasure 1 (Set.Icc a b ∩ LSenl d c ρ)
        = MeasureTheory.Measure.hausdorffMeasure 1 (Set.Icc a b) :=
    full_measure_pos c ρ hd0 hρ hfull
  -- the local level construction
  have hlocal : ∀ (B R : ℝ), 0 < R → R ≤ 1 → 0 ≤ B - R → B + R ≤ 1 →
      ∀ (T : Finset ℕ) (L : ℕ), 1 ≤ L → ∃ (F : Finset ℕ) (sub : ℕ → ℕ),
        (∀ i ∈ F, i ∉ T) ∧ IsLoc d c ρ B R F sub L :=
    fun B R hR0 hR1 hB0 hB1 T L hL =>
      Tree.existsLocal1 d hd0 hd1 c ρ hρ hρfin hfull' B R hR0 hR1 hB0 hB1 T L hL
  -- the Cantor set has arbitrarily large `d`-dimensional measure
  have hkey : ∀ η : ℝ, 0 < η → ENNReal.ofReal (η / 400) ≤
      MeasureTheory.Measure.hausdorffMeasure d
        (Set.Icc (0 : ℝ) 1 ∩ {z : ℝ | {n : ℕ | 0 < ρ n ∧ |z - c n| ≤ ρ n}.Infinite}) := by
    intro η hη
    obtain ⟨T⟩ := existsTreeData d hd0 hd1 c ρ hlocal η hη
    refine le_trans (Tree.cantorHausdorff d hd0 hd1 c ρ η hη T) (measure_mono ?_)
    exact Tree.cantorSubset d hd0 hd1 c ρ η T
  -- hence the measure of the small limsup set is `⊤`
  have hbound : ∀ C : ℝ≥0, (C : ℝ≥0∞) ≤ MeasureTheory.Measure.hausdorffMeasure d
      (Set.Icc (0 : ℝ) 1 ∩ {z : ℝ | {n : ℕ | 0 < ρ n ∧ |z - c n| ≤ ρ n}.Infinite}) := by
    intro C
    have hpos : (0:ℝ) < 400 * ((C : ℝ) + 1) := by positivity
    have h1 := hkey (400 * ((C : ℝ) + 1)) hpos
    have h2 : 400 * ((C : ℝ) + 1) / 400 = (C : ℝ) + 1 := by
      rw [mul_comm, div_eq_mul_inv, mul_assoc, mul_inv_cancel₀ (by norm_num), mul_one]
    rw [h2] at h1
    refine le_trans ?_ h1
    rw [← ENNReal.ofReal_coe_nnreal]
    refine ENNReal.ofReal_le_ofReal ?_
    push_cast
    linarith
  have htop : MeasureTheory.Measure.hausdorffMeasure d
      (Set.Icc (0 : ℝ) 1 ∩ {z : ℝ | {n : ℕ | 0 < ρ n ∧ |z - c n| ≤ ρ n}.Infinite}) = ⊤ := by
    have hsup : (⨆ n : ℕ, (((n : NNReal)) : ℝ≥0∞)) ≤ MeasureTheory.Measure.hausdorffMeasure d
        (Set.Icc (0 : ℝ) 1 ∩ {z : ℝ | {n : ℕ | 0 < ρ n ∧ |z - c n| ≤ ρ n}.Infinite}) :=
      iSup_le fun n => hbound (n : NNReal)
    have htop' : (⨆ n : ℕ, (((n : NNReal)) : ℝ≥0∞)) = ⊤ := by
      rw [ENNReal.iSup_coe_eq_top]
      rintro ⟨B, hB⟩
      have h := hB ⟨Nat.ceil B + 1, rfl⟩
      have hlt : B < ((Nat.ceil B + 1 : ℕ) : NNReal) := by
        have := Nat.le_ceil B
        push_cast
        linarith
      exact absurd h (not_le.mpr hlt)
    rw [htop'] at hsup
    exact top_unique hsup
  -- pass to the limsup over all radii
  rw [eq_top_iff, ← htop]
  refine measure_mono ?_
  intro z hz
  exact ⟨hz.1, hz.2.mono (fun n hn => hn.2)⟩

/-- **The Beresnevich–Velani mass transference principle in `ℝ` for `f(r) = r ^ d`**
(ambient dimension `k = 1`), for an arbitrary countable index type.  This is definitionally
the statement `Submission.Main.MTPStatement`. -/
theorem massTransferencePrincipleOne (d : ℝ) (hd0 : 0 < d) (hd1 : d < 1)
    (ι : Type) [Countable ι] (c : ι → ℝ) (ρ : ι → ℝ)
    (hρ : ∀ i, 0 ≤ ρ i)
    (hρfin : ∀ ε : ℝ, 0 < ε → {i | ε ≤ ρ i}.Finite)
    (hfull : ∀ x y : ℝ, 0 ≤ x → y ≤ 1 →
      MeasureTheory.Measure.hausdorffMeasure 1
        (Set.Icc x y ∩ {z : ℝ | {i | |z - c i| ≤ (ρ i) ^ d}.Infinite})
        = MeasureTheory.Measure.hausdorffMeasure 1 (Set.Icc x y)) :
    MeasureTheory.Measure.hausdorffMeasure d
      (Set.Icc (0 : ℝ) 1 ∩ {z : ℝ | {i | |z - c i| ≤ ρ i}.Infinite}) = ⊤ :=
  Work.BV.MTPStatement_of_SeqMTP massTransferencePrincipleSeq d hd0 hd1 ι c ρ hρ hρfin hfull

end Work.MassTransferenceAlt
