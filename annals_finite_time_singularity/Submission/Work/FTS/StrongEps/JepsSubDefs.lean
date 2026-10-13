/-
Copyright: work module for the Elgindi finite-time singularity project.

# `JepsSubDefs` — the slot-wise `ℋ^k`-integrand of a *difference*

`Work.Spaces.HkIntegrand α k f` is a finite sum of squares of weighted derivatives of `f`
(`D_z^i f · w/ sin(2θ)^{η/2}` and `D_z^j D_θ^i f · W`).  It is *not* subadditive in `f` for a
pointwise reason alone: the derivatives `D_z^i`, `D_z^j D_θ^i` are linear only where the data are
smooth, and the algebraic identity `(a - b)² ≤ 2a² + 2b²` then compares the integrand of the
difference with the two integrands.

This module records that comparison *slot by slot*: `HkIntDiff α k A B` is the sum of squares of
the *differences of the slots* of `A` and `B`, i.e. the expression obtained from `HkIntegrand` by
replacing `D_z^i f` with `D_z^i A - D_z^i B` (and similarly for the mixed slots).  Its two
properties, both proved below, are

* `HkIntDiff_nonneg` — it is a sum of squares;
* `HkIntDiff_le` — it is dominated by `2 · HkIntegrand α k A + 2 · HkIntegrand α k B`, purely
  algebraically (no smoothness, no identities: only `(a - b)² ≤ 2a² + 2b²`).

The point of the definition is the *identification* on the open quadrant: for the log-coordinate
mollifier `J_ε` one has `mixed j i (J_ε f - f) = J_ε (mixed j i f) - mixed j i f` on `Quad`
(the hypothesis `hlin` of `HkMem_JepsSub`), so `HkIntegrand α k (J_ε f - f)` agrees with
`HkIntDiff α k (J_ε f) f` there — an expression in the *slots of `J_ε f` and `f`*, which are
continuous on the open quadrant.  That is what makes the integrand of the difference continuous
on `Quad` (whence measurable) even though `J_ε f` itself is only known to be smooth when the
kernel is smooth.

Everything here rests on `[propext, Classical.choice, Quot.sound]`.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.FTS.StrongEps.Basic
import Submission.Work.Spaces.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps

set_option autoImplicit false

/-- The `ℋ^k`-integrand of a difference, computed slot by slot: the expression obtained from
`Work.Spaces.HkIntegrand α k ·` by replacing every derivative `D_z^i`, `D_z^j D_θ^i` with the
corresponding *difference of the slots of `A` and `B`*. -/
def HkIntDiff (α : ℝ) (k : ℕ) (A B : ℝ → ℝ → ℝ) (z θ : ℝ) : ℝ :=
  (∑ i ∈ Finset.range (k + 1),
      ((Work.Spaces.DzIter i A z θ - Work.Spaces.DzIter i B z θ)
        * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2)
    + ∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1),
        (if 1 ≤ i ∧ i + j ≤ k then
          ((Work.Spaces.mixed j i A z θ - Work.Spaces.mixed j i B z θ)
            * Work.Spaces.Wt α z θ) ^ 2
        else 0)

/-- `HkIntDiff` is a sum of squares, hence nonnegative. -/
theorem HkIntDiff_nonneg (α : ℝ) (k : ℕ) (A B : ℝ → ℝ → ℝ) (z θ : ℝ) :
    0 ≤ HkIntDiff α k A B z θ := by
  rw [HkIntDiff]
  refine add_nonneg (Finset.sum_nonneg fun i _ => sq_nonneg _) ?_
  refine Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => ?_
  split_ifs with h
  · exact sq_nonneg _
  · exact le_refl 0

/-- `(x - y)² ≤ 2x² + 2y²`, summed over a finite set. -/
private lemma sum_sq_sub_le {ι : Type*} (s : Finset ι) (x y : ι → ℝ) :
    (∑ i ∈ s, (x i - y i) ^ 2) ≤ 2 * (∑ i ∈ s, x i ^ 2) + 2 * (∑ i ∈ s, y i ^ 2) := by
  calc (∑ i ∈ s, (x i - y i) ^ 2) ≤ ∑ i ∈ s, (2 * x i ^ 2 + 2 * y i ^ 2) :=
        Finset.sum_le_sum fun i _ => by nlinarith [sq_nonneg (x i + y i)]
    _ = 2 * (∑ i ∈ s, x i ^ 2) + 2 * (∑ i ∈ s, y i ^ 2) := by
        rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]

/-- The double-sum version, with a *carried weight* `W` and a *decidable predicate* `c` on the
indices: the `if c then · else 0` shape of the mixed slots is handled by replacing the two slot
functions with their `c`-conditional versions. -/
private lemma two_slot_sum_le {ι : Type*} (s : Finset ι) (c : ι → ι → Prop) [DecidableRel c]
    (p q : ι → ι → ℝ) (W : ℝ) :
    (∑ i ∈ s, ∑ j ∈ s, (if c i j then ((p i j - q i j) * W) ^ 2 else 0))
      ≤ 2 * (∑ i ∈ s, ∑ j ∈ s, (if c i j then (p i j * W) ^ 2 else 0))
        + 2 * (∑ i ∈ s, ∑ j ∈ s, (if c i j then (q i j * W) ^ 2 else 0)) := by
  set X : ι → ι → ℝ := fun i j => if c i j then p i j * W else 0 with hX
  set Y : ι → ι → ℝ := fun i j => if c i j then q i j * W else 0 with hY
  have h1 : (∑ i ∈ s, ∑ j ∈ s, (if c i j then ((p i j - q i j) * W) ^ 2 else 0))
      = ∑ i ∈ s, ∑ j ∈ s, (X i j - Y i j) ^ 2 := by
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    simp only [hX, hY]
    by_cases h : c i j <;> simp only [h, ite_true, ite_false] <;> ring
  have h2 : (∑ i ∈ s, ∑ j ∈ s, (if c i j then (p i j * W) ^ 2 else 0))
      = ∑ i ∈ s, ∑ j ∈ s, (X i j) ^ 2 := by
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    simp only [hX]
    by_cases h : c i j <;> simp [h]
  have h3 : (∑ i ∈ s, ∑ j ∈ s, (if c i j then (q i j * W) ^ 2 else 0))
      = ∑ i ∈ s, ∑ j ∈ s, (Y i j) ^ 2 := by
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    simp only [hY]
    by_cases h : c i j <;> simp [h]
  rw [h1, h2, h3]
  calc (∑ i ∈ s, ∑ j ∈ s, (X i j - Y i j) ^ 2)
      ≤ ∑ i ∈ s, (2 * (∑ j ∈ s, (X i j) ^ 2) + 2 * (∑ j ∈ s, (Y i j) ^ 2)) :=
        Finset.sum_le_sum fun i _ => sum_sq_sub_le s (X i) (Y i)
    _ = 2 * (∑ i ∈ s, ∑ j ∈ s, (X i j) ^ 2) + 2 * (∑ i ∈ s, ∑ j ∈ s, (Y i j) ^ 2) := by
        rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]

/-- **The slot-wise integrand of a difference is dominated by the two integrands.**  Purely
algebraic: `(a - b)² ≤ 2a² + 2b²` applied to every slot. -/
theorem HkIntDiff_le (α : ℝ) (k : ℕ) (A B : ℝ → ℝ → ℝ) (z θ : ℝ) :
    HkIntDiff α k A B z θ ≤ 2 * Work.Spaces.HkIntegrand α k A z θ
      + 2 * Work.Spaces.HkIntegrand α k B z θ := by
  have hS1 : (∑ i ∈ Finset.range (k + 1),
        ((Work.Spaces.DzIter i A z θ - Work.Spaces.DzIter i B z θ)
          * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2)
      ≤ 2 * (∑ i ∈ Finset.range (k + 1),
            (Work.Spaces.DzIter i A z θ
              * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2)
        + 2 * (∑ i ∈ Finset.range (k + 1),
            (Work.Spaces.DzIter i B z θ
              * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2) := by
    have h := sum_sq_sub_le (Finset.range (k + 1))
      (fun i => Work.Spaces.DzIter i A z θ
        * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2)))
      (fun i => Work.Spaces.DzIter i B z θ
        * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2)))
    have heq : (∑ i ∈ Finset.range (k + 1),
        ((Work.Spaces.DzIter i A z θ - Work.Spaces.DzIter i B z θ)
          * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2)
        = ∑ i ∈ Finset.range (k + 1),
            (Work.Spaces.DzIter i A z θ
                * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))
              - Work.Spaces.DzIter i B z θ
                * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2 := by
      refine Finset.sum_congr rfl fun i _ => ?_
      ring
    rw [heq]; exact h
  have hS2 := two_slot_sum_le (Finset.range (k + 1))
    (fun i j => 1 ≤ i ∧ i + j ≤ k)
    (fun i j => Work.Spaces.mixed j i A z θ) (fun i j => Work.Spaces.mixed j i B z θ)
    (Work.Spaces.Wt α z θ)
  simp only [HkIntDiff, Work.Spaces.HkIntegrand]
  linarith [hS1, hS2]

end Work.FTS.StrongEps
