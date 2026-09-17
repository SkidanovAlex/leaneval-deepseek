import Mathlib
import Submission.MatSpace
import Submission.Commons.Probability.Gaussian.map_triangular_eq_stdGaussian_fin_measurable
import Submission.Commons.Probability.Reflection.fin_maximal_tail_of_map_pi
import Submission.Commons.Probability.Gaussian.stdGaussian_map_neg
import Submission.Commons.Probability.Gaussian.prod_stdGaussian_map_neg_snd

set_option synthInstance.maxHeartbeats 1000000

/-!
# The generic exploration process `A_{k+1} = A_k + ε · π(A_k) ξ_k`

This file contains the probabilistic core of Klartag's construction in the form actually used
by the final argument.  The state of the process is a single element `A : MatV d` of the
Euclidean space of `d × d` matrices, and the update is

    A_{k+1} = A_k + ε • (π(A_k) ξ_k),

where `ξ_k` is a fresh standard Gaussian on `MatV d` and `π : MatV d → (MatV d →L[ℝ] MatV d)`
is a fixed Borel map whose values are orthogonal projections onto subspaces of the symmetric
matrices (the current "constraint space", a function of `A_k` alone).

Because the constraint projection is a function of the current state, the whole process is a
measurable function of the Gaussian sample, and the triangular-independence lemma applies.

The material here is the generic part: it is stated for an arbitrary such `π`.  The concrete
instantiation (the projection onto the space of symmetric matrices whose quadratic form
vanishes on all violated lattice vectors) is in `Submission/Contact.lean`.
-/

namespace Submission.GenProc

open Matrix MeasureTheory ProbabilityTheory
open Submission.MatSpace

noncomputable section

variable {d : ℕ}

/-- The identity matrix, as an element of `MatV d`. -/
def oneV (d : ℕ) : MatV d := (matOf d).symm 1

lemma matOf_oneV (d : ℕ) : matOf d (oneV d) = 1 := (matOf d).apply_symm_apply 1

lemma oneV_mem_symV (d : ℕ) : oneV d ∈ symV d := by
  show (matOf d (oneV d)).IsSymm
  rw [matOf_oneV]
  exact Matrix.isSymm_one

/-- A matrix-space operator is *admissible* if it is the orthogonal projection onto a subspace
of the symmetric matrices. -/
structure Good (P : MatV d →L[ℝ] MatV d) : Prop where
  idem : P.comp P = P
  adj : ∀ x y : MatV d, inner ℝ (P x) y = inner ℝ x (P y)
  maps : ∀ x : MatV d, P x ∈ symV d

/-- Applying a measurable family of operators to a measurable vector is measurable. -/
lemma measurable_clm_apply {α : Type*} [MeasurableSpace α]
    {F : α → MatV d →L[ℝ] MatV d} {g : α → MatV d}
    (hF : Measurable F) (hg : Measurable g) : Measurable fun a => F a (g a) := by
  have h : Measurable fun q : (MatV d →L[ℝ] MatV d) × MatV d => q.1 q.2 := by fun_prop
  have h2 : Measurable fun a => (F a, g a) := Measurable.prodMk hF hg
  exact h.comp h2

variable (pl : MatV d → MatV d →L[ℝ] MatV d) (a₀ ε : ℝ) (K : ℕ)

/-- One step of the exploration process. -/
def step (A ξ : MatV d) : MatV d := A + ε • (pl A ξ)

lemma measurable_step (hpl : Measurable pl) :
    Measurable fun p : MatV d × MatV d => step pl ε p.1 p.2 := by
  have h : Measurable fun p : MatV d × MatV d => pl p.1 p.2 :=
    measurable_clm_apply (hpl.comp measurable_fst) measurable_snd
  have h2 : Measurable fun p : MatV d × MatV d => ε • (pl p.1 p.2) := h.const_smul ε
  exact measurable_fst.add h2

/-- The exploration process: `A_0 = a₀ · Id` and the `k`-th step uses the first coordinate of
the `k`-th sample. -/
def proc (ω : Fin K → MatV d × MatV d) : ℕ → MatV d
  | 0 => a₀ • oneV d
  | (k + 1) =>
      if h : k < K then step pl ε (proc ω k) (ω ⟨k, h⟩).1
      else proc ω k

lemma proc_succ (k : ℕ) (ω : Fin K → MatV d × MatV d) :
    proc pl a₀ ε K ω (k + 1)
      = if h : k < K then step pl ε (proc pl a₀ ε K ω k) (ω ⟨k, h⟩).1
        else proc pl a₀ ε K ω k := rfl

lemma measurable_proc (hpl : Measurable pl) (k : ℕ) :
    Measurable fun ω : Fin K → MatV d × MatV d => proc pl a₀ ε K ω k := by
  induction k with
  | zero => exact measurable_const
  | succ k ih =>
      have hfun : (fun ω : Fin K → MatV d × MatV d => proc pl a₀ ε K ω (k + 1))
          = fun ω => if h : k < K then step pl ε (proc pl a₀ ε K ω k) (ω ⟨k, h⟩).1
                     else proc pl a₀ ε K ω k := funext (proc_succ pl a₀ ε K k)
      rw [hfun]
      by_cases h : k < K
      · simp only [h, dif_pos]
        have hξ : Measurable fun ω : Fin K → MatV d × MatV d => (ω ⟨k, h⟩).1 :=
          (measurable_pi_apply (⟨k, h⟩ : Fin K)).fst
        exact (measurable_step (pl := pl) (ε := ε) hpl).comp (Measurable.prodMk ih hξ)
      · simp only [h, dif_neg, not_false_iff]
        exact ih

/-- The state at time `k` depends only on the first `k` Gaussian samples. -/
lemma proc_congr {ω ω' : Fin K → MatV d × MatV d} (k : ℕ)
    (h : ∀ i : Fin K, (i : ℕ) < k → ω i = ω' i) :
    proc pl a₀ ε K ω k = proc pl a₀ ε K ω' k := by
  induction k with
  | zero => rfl
  | succ k ih =>
      rw [proc_succ, proc_succ]
      by_cases hk : k < K
      · simp only [hk, dif_pos]
        rw [ih (fun i hi => h i (Nat.lt_trans hi (Nat.lt_succ_self k))),
          h ⟨k, hk⟩ (Nat.lt_succ_self k)]
      · simp only [hk, dif_neg, not_false_iff]
        exact ih (fun i hi => h i (Nat.lt_trans hi (Nat.lt_succ_self k)))

/-- The state is always a symmetric matrix. -/
lemma proc_mem_symV (hG : ∀ A : MatV d, Good (pl A)) (k : ℕ)
    (ω : Fin K → MatV d × MatV d) : proc pl a₀ ε K ω k ∈ symV d := by
  induction k with
  | zero => exact (symV d).smul_mem a₀ (oneV_mem_symV d)
  | succ k ih =>
      rw [proc_succ]
      by_cases h : k < K
      · simp only [h, dif_pos, step]
        exact (symV d).add_mem ih ((symV d).smul_mem ε ((hG _).maps _))
      · simp only [h, dif_neg, not_false_iff]
        exact ih

/-- The law of the Gaussian sample driving the process. -/
def sampleLaw (d K : ℕ) : MeasureTheory.Measure (Fin K → MatV d × MatV d) :=
  MeasureTheory.Measure.pi
    (fun _ : Fin K => (ProbabilityTheory.stdGaussian (MatV d)).prod
      (ProbabilityTheory.stdGaussian (MatV d)))

instance (d K : ℕ) : MeasureTheory.IsProbabilityMeasure (sampleLaw d K) :=
  MeasureTheory.Measure.pi.instIsProbabilityMeasure _

/-- The projection used at step `j`. -/
def projAt (ω : Fin K → MatV d × MatV d) (j : Fin K) : MatV d →L[ℝ] MatV d :=
  pl (proc pl a₀ ε K ω (j : ℕ))

lemma projAt_idem (hG : ∀ A : MatV d, Good (pl A)) (ω : Fin K → MatV d × MatV d)
    (j : Fin K) :
    (projAt pl a₀ ε K ω j).comp (projAt pl a₀ ε K ω j) = projAt pl a₀ ε K ω j :=
  (hG _).idem

lemma projAt_adj (hG : ∀ A : MatV d, Good (pl A)) (ω : Fin K → MatV d × MatV d) (j : Fin K)
    (x y : MatV d) :
    inner ℝ (projAt pl a₀ ε K ω j x) y = inner ℝ x (projAt pl a₀ ε K ω j y) :=
  (hG _).adj x y

lemma projAt_congr {ω ω' : Fin K → MatV d × MatV d} (j : Fin K)
    (h : ∀ i : Fin K, (i : ℕ) < (j : ℕ) → ω i = ω' i) :
    projAt pl a₀ ε K ω j = projAt pl a₀ ε K ω' j := by
  show pl (proc pl a₀ ε K ω (j : ℕ)) = pl (proc pl a₀ ε K ω' (j : ℕ))
  rw [proc_congr (pl := pl) (a₀ := a₀) (ε := ε) (K := K) (j : ℕ) h]

lemma measurable_projAt (hpl : Measurable pl) (j : Fin K) :
    Measurable fun p : (Fin K → MatV d × MatV d) × MatV d => projAt pl a₀ ε K p.1 j p.2 := by
  have h0 : Measurable fun p : (Fin K → MatV d × MatV d) × MatV d =>
      pl (proc pl a₀ ε K p.1 (j : ℕ)) :=
    hpl.comp ((measurable_proc (pl := pl) (a₀ := a₀) (ε := ε) (K := K) hpl (j : ℕ)).comp
      measurable_fst)
  exact measurable_clm_apply h0 measurable_snd

lemma measurable_projAt_ω (hpl : Measurable pl) (j : Fin K) :
    Measurable fun ω : Fin K → MatV d × MatV d => projAt pl a₀ ε K ω j :=
  hpl.comp (measurable_proc (pl := pl) (a₀ := a₀) (ε := ε) (K := K) hpl (j : ℕ))

/-- The `η`-increment of step `j`. -/
def etaAt (ω : Fin K → MatV d × MatV d) (j : Fin K) : MatV d :=
  projAt pl a₀ ε K ω j (ω j).1
    + (ContinuousLinearMap.id ℝ (MatV d) - projAt pl a₀ ε K ω j) (ω j).2

lemma measurable_etaAt (hpl : Measurable pl) (j : Fin K) :
    Measurable fun ω : Fin K → MatV d × MatV d => etaAt pl a₀ ε K ω j := by
  have hp : Measurable fun ω : Fin K → MatV d × MatV d =>
      (projAt pl a₀ ε K ω j, (ω j).1, (ω j).2) :=
    Measurable.prodMk (measurable_projAt_ω (pl := pl) (a₀ := a₀) (ε := ε) (K := K) hpl j)
      (Measurable.prodMk (measurable_pi_apply j).fst (measurable_pi_apply j).snd)
  have hcont : Measurable fun q : (MatV d →L[ℝ] MatV d) × (MatV d × MatV d) =>
      q.1 q.2.1 + (ContinuousLinearMap.id ℝ (MatV d) - q.1) q.2.2 := by fun_prop
  exact hcont.comp hp

/-- `η_j = π_j ω_j⁽¹⁾ + (1 - π_j) ω_j⁽²⁾` has the joint law of `K` independent standard
Gaussians (triangular independence). -/
theorem law_eta (hpl : Measurable pl) (hG : ∀ A : MatV d, Good (pl A)) :
    (sampleLaw d K).map (fun ω : Fin K → MatV d × MatV d => fun j : Fin K => etaAt pl a₀ ε K ω j)
      = MeasureTheory.Measure.pi (fun _ : Fin K => ProbabilityTheory.stdGaussian (MatV d)) :=
  Commons.Probability.Gaussian.map_triangular_eq_stdGaussian_fin_measurable K
    (fun ω j => projAt pl a₀ ε K ω j)
    (fun ω j => projAt_idem (pl := pl) (a₀ := a₀) (ε := ε) (K := K) hG ω j)
    (fun ω j x y => projAt_adj (pl := pl) (a₀ := a₀) (ε := ε) (K := K) hG ω j x y)
    (fun ω ω' j h => projAt_congr (pl := pl) (a₀ := a₀) (ε := ε) (K := K) j (fun i hi => h i hi))
    (fun j => measurable_projAt (pl := pl) (a₀ := a₀) (ε := ε) (K := K) hpl j)

/-- **Scalar maximal tail along the `η` walk.** -/
theorem maximal_tail_eta (hpl : Measurable pl) (hG : ∀ A : MatV d, Good (pl A)) (W : MatV d)
    (hW : ‖W‖ ≤ 1) {r : ℝ} (hε : 0 ≤ ε) (hr : 0 ≤ r) :
    (sampleLaw d K).real {ω | ∃ k ≤ K, r ≤ |∑ j ∈ Finset.univ.filter
        (fun j : Fin K => (j : ℕ) < k), ε * inner ℝ (etaAt pl a₀ ε K ω j) W|}
      ≤ 4 * Real.exp (-r ^ 2 / (2 * (K : ℝ) * ε ^ 2)) :=
  Commons.Probability.Reflection.fin_maximal_tail_of_map_pi
    (fun j (ω : Fin K → MatV d × MatV d) => etaAt pl a₀ ε K ω j)
    (fun j => measurable_etaAt (pl := pl) (a₀ := a₀) (ε := ε) (K := K) hpl j)
    (law_eta (pl := pl) (a₀ := a₀) (ε := ε) (K := K) hpl hG) W hW hε hr

/-! ## The `ζ` walk and the two-sided tail -/

/-- Negate the second coordinate of every sample. -/
def negSec {d K : ℕ} (ω : Fin K → MatV d × MatV d) : Fin K → MatV d × MatV d :=
  fun j => ((ω j).1, -(ω j).2)

lemma measurable_negSec {d K : ℕ} : Measurable (negSec (d := d) (K := K)) := by
  have h : negSec (d := d) (K := K) = fun ω j => ((ω j).1, -(ω j).2) := rfl
  rw [h]
  refine Measurable.of_eval fun j => ?_
  fun_prop

lemma proc_negSec (k : ℕ) (ω : Fin K → MatV d × MatV d) :
    proc pl a₀ ε K (negSec ω) k = proc pl a₀ ε K ω k := by
  induction k with
  | zero => rfl
  | succ k ih =>
      rw [proc_succ, proc_succ]
      by_cases h : k < K
      · simp only [h, dif_pos, negSec, ih]
      · simp only [h, dif_neg, not_false_iff]
        exact ih

/-- The actual increment `π_j ξ_j` of step `j`. -/
def incrAt (ω : Fin K → MatV d × MatV d) (j : Fin K) : MatV d :=
  projAt pl a₀ ε K ω j (ω j).1

/-- The `ζ`-increment of step `j`. -/
def zetaAt (ω : Fin K → MatV d × MatV d) (j : Fin K) : MatV d :=
  projAt pl a₀ ε K ω j (ω j).1
    - (ContinuousLinearMap.id ℝ (MatV d) - projAt pl a₀ ε K ω j) (ω j).2

lemma projAt_negSec (j : Fin K) (ω : Fin K → MatV d × MatV d) :
    projAt pl a₀ ε K (negSec ω) j = projAt pl a₀ ε K ω j := by
  show pl (proc pl a₀ ε K (negSec ω) (j : ℕ)) = pl (proc pl a₀ ε K ω (j : ℕ))
  rw [proc_negSec]

lemma sampleLaw_map_negSec : (sampleLaw d K).map (negSec (d := d) (K := K)) = sampleLaw d K := by
  have h : negSec (d := d) (K := K)
      = fun ω j => (fun p : MatV d × MatV d => (p.1, -p.2)) (ω j) := rfl
  have key := MeasureTheory.Measure.pi_map_pi
    (μ := fun _ : Fin K => (ProbabilityTheory.stdGaussian (MatV d)).prod
      (ProbabilityTheory.stdGaussian (MatV d)))
    (f := fun _ : Fin K => fun p : MatV d × MatV d => (p.1, -p.2))
    (fun _ => (by fun_prop : Measurable fun p : MatV d × MatV d => (p.1, -p.2)).aemeasurable)
  rw [h, show sampleLaw d K = MeasureTheory.Measure.pi (fun _ : Fin K =>
      (ProbabilityTheory.stdGaussian (MatV d)).prod (ProbabilityTheory.stdGaussian (MatV d)))
      from rfl]
  rw [key]
  congr 1
  funext j
  exact Commons.Probability.Gaussian.prod_stdGaussian_map_neg_snd

lemma zetaAt_eq_etaAt_negSec (ω : Fin K → MatV d × MatV d) (j : Fin K) :
    zetaAt pl a₀ ε K ω j = etaAt pl a₀ ε K (negSec ω) j := by
  simp only [zetaAt, etaAt, negSec, map_neg, projAt_negSec pl a₀ ε K j ω]
  abel

/-- The `ζ` family also has the joint law of `K` independent standard Gaussians. -/
theorem law_zeta (hpl : Measurable pl) (hG : ∀ A : MatV d, Good (pl A)) :
    (sampleLaw d K).map (fun ω : Fin K → MatV d × MatV d => fun j : Fin K =>
        zetaAt pl a₀ ε K ω j)
      = MeasureTheory.Measure.pi (fun _ : Fin K => ProbabilityTheory.stdGaussian (MatV d)) := by
  have h1 : (fun ω : Fin K → MatV d × MatV d => fun j : Fin K => zetaAt pl a₀ ε K ω j)
      = (fun ω : Fin K → MatV d × MatV d => fun j : Fin K => etaAt pl a₀ ε K ω j)
        ∘ (negSec (d := d) (K := K)) := by
    funext ω j
    exact zetaAt_eq_etaAt_negSec pl a₀ ε K ω j
  rw [h1, ← MeasureTheory.Measure.map_map
      (Measurable.of_eval (fun j => measurable_etaAt (pl := pl) (a₀ := a₀) (ε := ε) (K := K) hpl j))
      (measurable_negSec (d := d) (K := K)), sampleLaw_map_negSec,
    law_eta (pl := pl) (a₀ := a₀) (ε := ε) (K := K) hpl hG]

/-- **Scalar maximal tail along the `ζ` walk.** -/
theorem maximal_tail_zeta (hpl : Measurable pl) (hG : ∀ A : MatV d, Good (pl A)) (W : MatV d)
    (hW : ‖W‖ ≤ 1) {r : ℝ} (hε : 0 ≤ ε) (hr : 0 ≤ r) :
    (sampleLaw d K).real {ω | ∃ k ≤ K, r ≤ |∑ j ∈ Finset.univ.filter
        (fun j : Fin K => (j : ℕ) < k), ε * inner ℝ (zetaAt pl a₀ ε K ω j) W|}
      ≤ 4 * Real.exp (-r ^ 2 / (2 * (K : ℝ) * ε ^ 2)) :=
  Commons.Probability.Reflection.fin_maximal_tail_of_map_pi
    (fun j (ω : Fin K → MatV d × MatV d) => zetaAt pl a₀ ε K ω j)
    (fun j => by
      have hp : Measurable fun ω : Fin K → MatV d × MatV d =>
          (projAt pl a₀ ε K ω j, (ω j).1, (ω j).2) :=
        Measurable.prodMk (measurable_projAt_ω (pl := pl) (a₀ := a₀) (ε := ε) (K := K) hpl j)
          (Measurable.prodMk (measurable_pi_apply j).fst (measurable_pi_apply j).snd)
      have hcont : Measurable fun q : (MatV d →L[ℝ] MatV d) × (MatV d × MatV d) =>
          q.1 q.2.1 - (ContinuousLinearMap.id ℝ (MatV d) - q.1) q.2.2 := by fun_prop
      exact hcont.comp hp)
    (law_zeta (pl := pl) (a₀ := a₀) (ε := ε) (K := K) hpl hG) W hW hε hr

lemma measurable_incrAt (hpl : Measurable pl) (j : Fin K) :
    Measurable fun ω : Fin K → MatV d × MatV d => incrAt pl a₀ ε K ω j :=
  measurable_clm_apply (measurable_projAt_ω (pl := pl) (a₀ := a₀) (ε := ε) (K := K) hpl j)
    (measurable_pi_apply j).fst

/-- The increment is half the sum of the two Gaussian walks. -/
lemma incrAt_eq_half (ω : Fin K → MatV d × MatV d) (j : Fin K) :
    incrAt pl a₀ ε K ω j
      = (2 : ℝ)⁻¹ • (etaAt pl a₀ ε K ω j + zetaAt pl a₀ ε K ω j) := by
  simp only [incrAt, etaAt, zetaAt, map_add, map_sub]
  module

lemma sum_filter_lt_succ (k : ℕ) (hk : k < K) (f : Fin K → MatV d) :
    (∑ j ∈ Finset.univ.filter (fun j : Fin K => (j : ℕ) < k + 1), f j)
      = f ⟨k, hk⟩ + ∑ j ∈ Finset.univ.filter (fun j : Fin K => (j : ℕ) < k), f j := by
  have hset : (Finset.univ.filter (fun j : Fin K => (j : ℕ) < k + 1))
      = insert ⟨k, hk⟩ (Finset.univ.filter (fun j : Fin K => (j : ℕ) < k)) := by
    ext j
    simp only [Finset.mem_insert, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · intro h
      rcases Nat.lt_succ_iff_lt_or_eq.mp h with h' | h'
      · exact Or.inr h'
      · exact Or.inl (Fin.ext h')
    · rintro (rfl | h)
      · exact Nat.lt_succ_self k
      · exact Nat.lt_succ_of_lt h
  rw [hset, Finset.sum_insert (by simp)]

/-- The state at time `k` is the sum of the increments. -/
theorem proc_eq_sum {k : ℕ} (hk : k ≤ K) (ω : Fin K → MatV d × MatV d) :
    proc pl a₀ ε K ω k
      = a₀ • oneV d + ∑ j ∈ Finset.univ.filter (fun j : Fin K => (j : ℕ) < k),
          ε • incrAt pl a₀ ε K ω j := by
  induction k with
  | zero =>
      rw [show (Finset.univ.filter (fun j : Fin K => (j : ℕ) < 0)) = ∅ from by
        ext j; simp]
      simp [proc]
  | succ k ih =>
      have hklt : k < K := by omega
      have hprev : k ≤ K := by omega
      rw [proc_succ]
      simp only [hklt, dif_pos]
      rw [show step pl ε (proc pl a₀ ε K ω k) (ω ⟨k, hklt⟩).1
          = (proc pl a₀ ε K ω k) + ε • incrAt pl a₀ ε K ω ⟨k, hklt⟩ from rfl]
      rw [ih hprev, sum_filter_lt_succ (d := d) (K := K) k hklt
        (fun j => ε • incrAt pl a₀ ε K ω j)]
      abel

/-- **Two-sided maximal tail for a linear functional.** -/
theorem maximal_tail_incr (hpl : Measurable pl) (hG : ∀ A : MatV d, Good (pl A)) (W : MatV d)
    (hW : ‖W‖ ≤ 1) {r : ℝ} (hε : 0 ≤ ε) (hr : 0 ≤ r) :
    (sampleLaw d K).real {ω | ∃ k ≤ K, r ≤ |∑ j ∈ Finset.univ.filter
        (fun j : Fin K => (j : ℕ) < k), ε * inner ℝ (incrAt pl a₀ ε K ω j) W|}
      ≤ 8 * Real.exp (-r ^ 2 / (2 * (K : ℝ) * ε ^ 2)) := by
  classical
  set A : Set (Fin K → MatV d × MatV d) := {ω | ∃ k ≤ K, r ≤ |∑ j ∈ Finset.univ.filter
      (fun j : Fin K => (j : ℕ) < k), ε * inner ℝ (etaAt pl a₀ ε K ω j) W|} with hA
  set B : Set (Fin K → MatV d × MatV d) := {ω | ∃ k ≤ K, r ≤ |∑ j ∈ Finset.univ.filter
      (fun j : Fin K => (j : ℕ) < k), ε * inner ℝ (zetaAt pl a₀ ε K ω j) W|} with hB
  have hkey : ∀ (k : ℕ) (ω : Fin K → MatV d × MatV d),
      (∑ j ∈ Finset.univ.filter (fun j : Fin K => (j : ℕ) < k),
          ε * inner ℝ (incrAt pl a₀ ε K ω j) W)
        = (2 : ℝ)⁻¹ * ((∑ j ∈ Finset.univ.filter (fun j : Fin K => (j : ℕ) < k),
              ε * inner ℝ (etaAt pl a₀ ε K ω j) W)
            + (∑ j ∈ Finset.univ.filter (fun j : Fin K => (j : ℕ) < k),
              ε * inner ℝ (zetaAt pl a₀ ε K ω j) W)) := by
    intro k ω
    rw [mul_add, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [incrAt_eq_half (pl := pl) (a₀ := a₀) (ε := ε) (K := K) ω j, inner_smul_left,
      inner_add_left]
    simp only [conj_trivial]
    ring
  have hsub : {ω | ∃ k ≤ K, r ≤ |∑ j ∈ Finset.univ.filter
        (fun j : Fin K => (j : ℕ) < k), ε * inner ℝ (incrAt pl a₀ ε K ω j) W|} ⊆ A ∪ B := by
    rintro ω ⟨k, hk, hle⟩
    let S₁ : ℝ := ∑ j ∈ Finset.univ.filter (fun j : Fin K => (j : ℕ) < k),
      ε * inner ℝ (etaAt pl a₀ ε K ω j) W
    let S₂ : ℝ := ∑ j ∈ Finset.univ.filter (fun j : Fin K => (j : ℕ) < k),
      ε * inner ℝ (zetaAt pl a₀ ε K ω j) W
    have hX : (∑ j ∈ Finset.univ.filter (fun j : Fin K => (j : ℕ) < k),
        ε * inner ℝ (incrAt pl a₀ ε K ω j) W) = (2 : ℝ)⁻¹ * (S₁ + S₂) := hkey k ω
    have hle' : r ≤ |(2 : ℝ)⁻¹ * (S₁ + S₂)| := by rw [← hX]; exact hle
    have hmax : r ≤ max |S₁| |S₂| := by
      have hb : |(2 : ℝ)⁻¹ * (S₁ + S₂)| ≤ max |S₁| |S₂| := by
        rw [abs_mul, abs_inv, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
        have h1 : |S₁ + S₂| ≤ |S₁| + |S₂| := abs_add_le _ _
        have h2 : |S₁| + |S₂| ≤ 2 * max |S₁| |S₂| := by
          linarith [le_max_left |S₁| |S₂|, le_max_right |S₁| |S₂|]
        have h3 : (2 : ℝ)⁻¹ * |S₁ + S₂| = |S₁ + S₂| / 2 := by ring
        linarith
      linarith
    rcases le_max_iff.mp hmax with h | h
    · exact Or.inl ⟨k, hk, h⟩
    · exact Or.inr ⟨k, hk, h⟩
  calc (sampleLaw d K).real _
      ≤ (sampleLaw d K).real (A ∪ B) :=
        MeasureTheory.measureReal_mono hsub (MeasureTheory.measure_ne_top _ _)
    _ ≤ (sampleLaw d K).real A + (sampleLaw d K).real B :=
        MeasureTheory.measureReal_union_le _ _
    _ ≤ 4 * Real.exp (-r ^ 2 / (2 * (K : ℝ) * ε ^ 2))
          + 4 * Real.exp (-r ^ 2 / (2 * (K : ℝ) * ε ^ 2)) :=
        add_le_add (hA ▸ maximal_tail_eta (pl := pl) (a₀ := a₀) (ε := ε) (K := K) hpl hG W hW hε hr)
          (hB ▸ maximal_tail_zeta (pl := pl) (a₀ := a₀) (ε := ε) (K := K) hpl hG W hW hε hr)
    _ = 8 * Real.exp (-r ^ 2 / (2 * (K : ℝ) * ε ^ 2)) := by ring

end

end Submission.GenProc
