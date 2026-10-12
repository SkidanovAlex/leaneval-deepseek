import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseFixB1S.HopDefs
import Submission.Work.BoseFixB1S.hopEdgeCS
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission.Work.BoseFixB1S.boxCrossHoppingSharpLowAux`

Auxiliary lemmas for the sharp (constant `1`) hopping bound
`Work.BoseFixB1S.boxCrossHoppingSharpLow`.

Two ingredients, both pure bookkeeping:

* `hopCollapseGen` — the `Q`-sum collapse of `Work.BoseFixB1S.hopCollapse` with the
  measurability/boundedness hypotheses on the slot weight `g` **removed** (the proof of
  `hopCollapse` never uses them: it is `Finset.sum_eq_single` at the child, the off-child terms
  being killed by the orthogonality hypothesis `horth`).  The weight of the hopping layer is only
  a.e. strongly measurable on `acube ℓ` — this is the form the sharp bound is applied with.

* `edgeCS_guard`, `sum_sqrt_mul_le_sqrt_sum_mul_sum` — the two Cauchy–Schwarz steps of the
  assembly:
  * `edgeCS_guard`: over the *realised* edges only (`0 < a`, `0 < b`), the Cauchy–Schwarz bound
    of `hopEdgeCS`; outside the realised set every summand is already `0` because the masses are
    non-negative (`a e = 0` or `b e = 0`).
  * `sum_sqrt_mul_le_sqrt_sum_mul_sum`: `Σᵢ√(Wᵢ Pᵢ) ≤ √((ΣᵢWᵢ)(ΣᵢPᵢ))` — the slot-level
    Cauchy–Schwarz, the `hopEdgeCS` at the constant weight `1`.
-/

noncomputable section

open MeasureTheory
open scoped BigOperators

namespace Work.BoseFixB1S

open Submission.BoseGases

local notation "E3" => EuclideanSpace ℝ (Fin 3)

set_option autoImplicit false
set_option linter.unusedVariables false

/-- **The `Q`-sum collapses onto the child** (measurability-free form of
`Work.BoseFixB1S.hopCollapse`).  For a `P`-pair `p` with `i ∈ p.1` and a slot-`i` weight `g`, the
sum over all `Q`-components `ψ_q` with `i ∈ q.2` of the pairing `∫_{abox} ψ_q·g(x i)·ψ_p`
reduces to the single term of the **child** `(p.1.erase i, insert i p.2)`, given the
weighted-orthogonality hypothesis `horth` at every slot `j ≠ i`. -/
theorem hopCollapseGen {N : ℕ} {ℓ volA : ℝ} {A : Set E3}
    {g : E3 → ℝ} {Φ : X N → ℝ}
    {i : Fin N} {p : Finset (Fin N) × Finset (Fin N)}
    (hp : p ∈ Work.BoseFixB1.disjPairs N) (hpi : i ∈ p.1)
    (horth : ∀ (S T S' T' : Finset (Fin N)), Disjoint S T → Disjoint S' T' → ∀ j : Fin N,
      j ≠ i → orthSlotType S T j ≠ orthSlotType S' T' j →
      (∫ x in Submission.BoseGases.abox N ℓ,
        boxCompT volA A S T Φ x * g (x i) * boxCompT volA A S' T' Φ x) = 0) :
    (∑ q ∈ (Work.BoseFixB1.disjPairs N).filter (fun q => i ∈ q.2),
        ∫ x in Submission.BoseGases.abox N ℓ,
          boxCompT volA A q.1 q.2 Φ x * g (x i)
            * boxCompT volA A p.1 p.2 Φ x)
      = ∫ x in Submission.BoseGases.abox N ℓ,
          boxCompT volA A (hopChild i p).1 (hopChild i p).2 Φ x * g (x i)
            * boxCompT volA A p.1 p.2 Φ x := by
  classical
  have hpdd : Disjoint p.1 p.2 := Work.BoseFixB1.mem_disjPairs.mp hp
  have hchild : hopChild i p ∈ (Work.BoseFixB1.disjPairs N).filter (fun q => i ∈ q.2) := by
    rw [Finset.mem_filter]
    exact ⟨hopChild_mem_disjPairs hp hpi, mem_hopChild_snd i p⟩
  refine Finset.sum_eq_single (hopChild i p) ?_ (fun h => absurd hchild h)
  intro q hq hne
  rw [Finset.mem_filter] at hq
  obtain ⟨hqd, hqi⟩ := hq
  have hqdd : Disjoint q.1 q.2 := Work.BoseFixB1.mem_disjPairs.mp hqd
  obtain ⟨j, hji, hdif⟩ := exists_type_mismatch_of_ne_hopChild hpdd hqdd hpi hqi hne
  exact horth q.1 q.2 p.1 p.2 hqdd hpdd j hji hdif

/-- **Cauchy–Schwarz over the realised edges.**  For non-negative masses `a`, `b` on the finset
`s`, the weighted Cauchy–Schwarz sum is bounded by the geometric mean of the *guarded* weight
sums, where the guard `0 < a ∧ 0 < b` selects the realised edges: outside it each summand is
already `0`, because a non-negative mass which is not positive is `0`. -/
theorem edgeCS_guard {ι : Type*} (s : Finset ι) (a b w : ι → ℝ)
    (ha : ∀ e ∈ s, 0 ≤ a e) (hb : ∀ e ∈ s, 0 ≤ b e) :
    (∑ e ∈ s, |w e| * Real.sqrt (a e * b e))
      ≤ Real.sqrt ((∑ e ∈ s.filter (fun e => 0 < a e ∧ 0 < b e), (w e) ^ 2 * a e)
          * (∑ e ∈ s.filter (fun e => 0 < a e ∧ 0 < b e), b e)) := by
  have hdrop : (∑ e ∈ s, |w e| * Real.sqrt (a e * b e))
      = ∑ e ∈ s.filter (fun e => 0 < a e ∧ 0 < b e), |w e| * Real.sqrt (a e * b e) := by
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl fun e he => ?_
    by_cases h : 0 < a e ∧ 0 < b e
    · rw [if_pos h]
    · rw [if_neg h]
      have hz : a e = 0 ∨ b e = 0 := by
        rcases lt_or_eq_of_le (ha e he) with h1 | h1
        · rcases lt_or_eq_of_le (hb e he) with h2 | h2
          · exact absurd ⟨h1, h2⟩ h
          · exact Or.inr h2.symm
        · exact Or.inl h1.symm
      rcases hz with h1 | h2
      · rw [h1, zero_mul, Real.sqrt_zero, mul_zero]
      · rw [h2, mul_zero, Real.sqrt_zero, mul_zero]
  rw [hdrop]
  exact hopEdgeCS _ a b w
    (fun e he => ha e (Finset.mem_of_mem_filter e he))
    (fun e he => hb e (Finset.mem_of_mem_filter e he))

/-- **Slot-level Cauchy–Schwarz**: `Σᵢ√(Wᵢ Pᵢ) ≤ √((ΣᵢWᵢ)(ΣᵢPᵢ))` for non-negative `W`, `P`
(this is `hopEdgeCS` at the constant weight `1`). -/
theorem sum_sqrt_mul_le_sqrt_sum_mul_sum {ι : Type*} (s : Finset ι) (W P : ι → ℝ)
    (hW : ∀ i ∈ s, 0 ≤ W i) (hP : ∀ i ∈ s, 0 ≤ P i) :
    (∑ i ∈ s, Real.sqrt (W i * P i))
      ≤ Real.sqrt ((∑ i ∈ s, W i) * (∑ i ∈ s, P i)) := by
  set f : ι → ℝ := fun i => Real.sqrt (W i) with hf
  set g : ι → ℝ := fun i => Real.sqrt (P i) with hg
  have h1 : (∑ i ∈ s, Real.sqrt (W i * P i)) = ∑ i ∈ s, f i * g i := by
    refine Finset.sum_congr rfl fun i hi => ?_
    simp only [hf, hg]
    rw [Real.sqrt_mul (hW i hi)]
  have h2 : (∑ i ∈ s, (f i) ^ 2) = ∑ i ∈ s, W i := by
    refine Finset.sum_congr rfl fun i hi => ?_
    simp only [hf]
    rw [Real.sq_sqrt (hW i hi)]
  have h3 : (∑ i ∈ s, (g i) ^ 2) = ∑ i ∈ s, P i := by
    refine Finset.sum_congr rfl fun i hi => ?_
    simp only [hg]
    rw [Real.sq_sqrt (hP i hi)]
  rw [h1, ← h2, ← h3, Real.le_sqrt (by positivity) (by positivity)]
  exact Finset.sum_mul_sq_le_sq_mul_sq s f g

/-- **The abstract Cauchy–Schwarz assembly of the hopping bound.** -/
theorem hoppingCS_sum {N : ℕ} {F2 : ℝ} (hF2 : 0 ≤ F2)
    (mc mp w : (i : Fin N) → Finset (Fin N) × Finset (Fin N) → ℝ)
    (I : (i : Fin N) → Finset (Fin N) × Finset (Fin N) → ℝ)
    (hI : ∀ (i : Fin N) (p : Finset (Fin N) × Finset (Fin N)), p ∈ hopPairSet i →
      |I i p| ≤ F2 * Real.sqrt (mc i p * mp i p))
    (hmc : ∀ i p, 0 ≤ mc i p) (hmp : ∀ i p, 0 ≤ mp i p) :
    |∑ i : Fin N, ∑ p ∈ hopPairSet i, w i p * I i p|
      ≤ F2 * Real.sqrt
          ((∑ i : Fin N, ∑ p ∈ hopPairSet i,
              (if 0 < mp i p ∧ 0 < mc i p then mp i p else 0))
            * (∑ i : Fin N, ∑ p ∈ hopPairSet i,
                (if 0 < mp i p ∧ 0 < mc i p then mc i p * (w i p) ^ 2 else 0))) := by
  classical
  -- abbreviations
  have hmc' : ∀ (i : Fin N) (p : Finset (Fin N) × Finset (Fin N)), 0 ≤ mc i p := hmc
  have hmp' : ∀ (i : Fin N) (p : Finset (Fin N) × Finset (Fin N)), 0 ≤ mp i p := hmp
  -- 1. triangle inequality
  have h1 : |∑ i : Fin N, ∑ p ∈ hopPairSet i, w i p * I i p|
      ≤ ∑ i : Fin N, ∑ p ∈ hopPairSet i, |w i p| * |I i p| := by
    refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
    refine Finset.sum_le_sum (fun i _ => ?_)
    refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
    exact Finset.sum_le_sum (fun p _ => by rw [abs_mul])
  -- 2. the per-edge bound
  have h2 : (∑ i : Fin N, ∑ p ∈ hopPairSet i, |w i p| * |I i p|)
      ≤ ∑ i : Fin N, ∑ p ∈ hopPairSet i,
          |w i p| * (F2 * Real.sqrt (mc i p * mp i p)) :=
    Finset.sum_le_sum (fun i _ => Finset.sum_le_sum (fun p hp =>
      mul_le_mul_of_nonneg_left (hI i p hp) (abs_nonneg _)))
  -- 3. pull `F2` out of the double sum
  have h3 : (∑ i : Fin N, ∑ p ∈ hopPairSet i, |w i p| * (F2 * Real.sqrt (mc i p * mp i p)))
      = F2 * ∑ i : Fin N, ∑ p ∈ hopPairSet i, |w i p| * Real.sqrt (mc i p * mp i p) := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun i _ => by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl (fun p _ => by ring))
  -- 4. the per-slot Cauchy–Schwarz (guarded)
  have h4 : ∀ i : Fin N,
      (∑ p ∈ hopPairSet i, |w i p| * Real.sqrt (mc i p * mp i p))
        ≤ Real.sqrt
            ((∑ p ∈ hopPairSet i,
                (if 0 < mp i p ∧ 0 < mc i p then mc i p * (w i p) ^ 2 else 0))
              * (∑ p ∈ hopPairSet i,
                  (if 0 < mp i p ∧ 0 < mc i p then mp i p else 0))) := by
    intro i
    have hg := edgeCS_guard (hopPairSet i) (mc i) (mp i) (w i)
      (fun p _ => hmc' i p) (fun p _ => hmp' i p)
    have hfil : (hopPairSet i).filter (fun p => 0 < mc i p ∧ 0 < mp i p)
        = (hopPairSet i).filter (fun p => 0 < mp i p ∧ 0 < mc i p) :=
      Finset.filter_congr (fun p _ => ⟨fun h => ⟨h.2, h.1⟩, fun h => ⟨h.2, h.1⟩⟩)
    rw [hfil] at hg
    have hsum1 : (∑ p ∈ (hopPairSet i).filter (fun p => 0 < mp i p ∧ 0 < mc i p),
          (w i p) ^ 2 * mc i p)
        = ∑ p ∈ hopPairSet i, (if 0 < mp i p ∧ 0 < mc i p then mc i p * (w i p) ^ 2 else 0) := by
      rw [Finset.sum_filter]
      exact Finset.sum_congr rfl (fun p _ => by
        by_cases h : 0 < mp i p ∧ 0 < mc i p
        · rw [if_pos h, if_pos h]; ring
        · rw [if_neg h, if_neg h])
    have hsum2 : (∑ p ∈ (hopPairSet i).filter (fun p => 0 < mp i p ∧ 0 < mc i p), mp i p)
        = ∑ p ∈ hopPairSet i, (if 0 < mp i p ∧ 0 < mc i p then mp i p else 0) := by
      rw [Finset.sum_filter]
    rw [hsum1, hsum2] at hg
    exact hg
  -- 5. the slot-level Cauchy–Schwarz
  have h5 : (∑ i : Fin N, Real.sqrt
        ((∑ p ∈ hopPairSet i,
            (if 0 < mp i p ∧ 0 < mc i p then mc i p * (w i p) ^ 2 else 0))
          * (∑ p ∈ hopPairSet i, (if 0 < mp i p ∧ 0 < mc i p then mp i p else 0))))
      ≤ Real.sqrt
          ((∑ i : Fin N, ∑ p ∈ hopPairSet i,
              (if 0 < mp i p ∧ 0 < mc i p then mc i p * (w i p) ^ 2 else 0))
            * (∑ i : Fin N, ∑ p ∈ hopPairSet i,
                (if 0 < mp i p ∧ 0 < mc i p then mp i p else 0))) := by
    refine sum_sqrt_mul_le_sqrt_sum_mul_sum Finset.univ
      (fun i => ∑ p ∈ hopPairSet i,
        (if 0 < mp i p ∧ 0 < mc i p then mc i p * (w i p) ^ 2 else 0))
      (fun i => ∑ p ∈ hopPairSet i, (if 0 < mp i p ∧ 0 < mc i p then mp i p else 0))
      (fun i _ => Finset.sum_nonneg (fun p _ => by
        by_cases h : 0 < mp i p ∧ 0 < mc i p
        · rw [if_pos h]; exact mul_nonneg (hmc' i p) (sq_nonneg _)
        · rw [if_neg h]))
      (fun i _ => Finset.sum_nonneg (fun p _ => by
        by_cases h : 0 < mp i p ∧ 0 < mc i p
        · rw [if_pos h]; exact le_of_lt h.1
        · rw [if_neg h]))
  calc |∑ i : Fin N, ∑ p ∈ hopPairSet i, w i p * I i p|
      ≤ ∑ i : Fin N, ∑ p ∈ hopPairSet i, |w i p| * |I i p| := h1
    _ ≤ ∑ i : Fin N, ∑ p ∈ hopPairSet i,
          |w i p| * (F2 * Real.sqrt (mc i p * mp i p)) := h2
    _ = F2 * ∑ i : Fin N, ∑ p ∈ hopPairSet i,
          |w i p| * Real.sqrt (mc i p * mp i p) := h3
    _ ≤ F2 * ∑ i : Fin N, Real.sqrt
          ((∑ p ∈ hopPairSet i,
              (if 0 < mp i p ∧ 0 < mc i p then mc i p * (w i p) ^ 2 else 0))
            * (∑ p ∈ hopPairSet i, (if 0 < mp i p ∧ 0 < mc i p then mp i p else 0))) :=
        mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun i _ => h4 i)) hF2
    _ ≤ F2 * Real.sqrt
          ((∑ i : Fin N, ∑ p ∈ hopPairSet i,
              (if 0 < mp i p ∧ 0 < mc i p then mc i p * (w i p) ^ 2 else 0))
            * (∑ i : Fin N, ∑ p ∈ hopPairSet i,
                (if 0 < mp i p ∧ 0 < mc i p then mp i p else 0))) :=
        mul_le_mul_of_nonneg_left h5 hF2
    _ = F2 * Real.sqrt
          ((∑ i : Fin N, ∑ p ∈ hopPairSet i,
              (if 0 < mp i p ∧ 0 < mc i p then mp i p else 0))
            * (∑ i : Fin N, ∑ p ∈ hopPairSet i,
                (if 0 < mp i p ∧ 0 < mc i p then mc i p * (w i p) ^ 2 else 0))) := by
        exact congrArg (fun t => F2 * Real.sqrt t) (mul_comm _ _)


/-- A function that is a.e. strongly measurable and bounded on the analysis box is integrable
there (the box has finite measure).  The a.e.-strongly-measurable form is what the localised
fibre `w1Fibre ℓ (wSmall1Pair h M ℓ d u)` provides. -/
theorem integrableOn_abox_of_bound_aesm {N : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) {f : X N → ℝ}
    (hm : MeasureTheory.AEStronglyMeasurable f
      ((MeasureTheory.volume : MeasureTheory.Measure (X N)).restrict
        (Submission.BoseGases.abox N ℓ)))
    {C : ℝ} (hb : ∀ x ∈ Submission.BoseGases.abox N ℓ, |f x| ≤ C) :
    MeasureTheory.IntegrableOn f (Submission.BoseGases.abox N ℓ) MeasureTheory.volume := by
  refine MeasureTheory.IntegrableOn.of_bound
    (Submission.BoseGases.abox_lt_top N ℓ hℓ.le) hm C ?_
  rw [MeasureTheory.ae_restrict_iff' (Submission.BoseGases.abox_measurable N ℓ)]
  exact Filter.Eventually.of_forall (fun x hx => by
    rw [Real.norm_eq_abs]; exact hb x hx)

/-- Linearity of the `abox` integral in a finite sum: `∫ (Σᵢ fᵢ)·g = Σᵢ ∫ fᵢ·g`. -/
theorem abox_integral_sum_mul {N : ℕ} {ℓ : ℝ} {ι : Type*} (s : Finset ι)
    (f : ι → Submission.BoseGases.X N → ℝ) (g : Submission.BoseGases.X N → ℝ)
    (hint : ∀ i ∈ s, MeasureTheory.IntegrableOn (fun x => f i x * g x)
      (Submission.BoseGases.abox N ℓ) MeasureTheory.volume) :
    (∫ x in Submission.BoseGases.abox N ℓ, (∑ i ∈ s, f i x) * g x)
      = ∑ i ∈ s, ∫ x in Submission.BoseGases.abox N ℓ, f i x * g x := by
  simp only [Finset.sum_mul]
  rw [MeasureTheory.integral_finsetSum]
  intro i hi
  exact hint i hi

end Work.BoseFixB1S
