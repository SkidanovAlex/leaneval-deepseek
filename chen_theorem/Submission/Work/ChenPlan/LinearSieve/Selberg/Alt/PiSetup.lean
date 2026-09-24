import Mathlib
import Submission.Work.ChenPlan.LinearSieve.Selberg.Alt.ExpLaw

/-!
# Splitting the product measure on `ℝ^ℕ`

Definitions of the "cons" and "join" maps used to split `Measure.infinitePi (fun _ : ℕ => μ)`
into a finite prefix and an infinite tail, together with their basic properties.
-/

open MeasureTheory
open scoped ENNReal

namespace Work.ChenPlan.LinearSieve.Selberg.Alt

/-- `Tf k x = x 0 + x 1 + ... + x (k-1)`; it is `partialSum x k`. -/
def Tf (k : ℕ) (x : ℕ → ℝ) : ℝ := ∑ i ∈ Finset.range k, x i

@[simp] lemma Tf_zero (x : ℕ → ℝ) : Tf 0 x = 0 := by simp [Tf]

lemma Tf_succ (k : ℕ) (x : ℕ → ℝ) : Tf (k+1) x = Tf k x + x k := by
  simp only [Tf, Finset.sum_range_succ]

/-- `mkSeq (u, z)` is the sequence with head `u` and tail `z`. -/
def mkSeq (p : ℝ × (ℕ → ℝ)) : ℕ → ℝ := fun n => if n = 0 then p.1 else p.2 (n - 1)

@[simp] lemma mkSeq_zero (p : ℝ × (ℕ → ℝ)) : mkSeq p 0 = p.1 := by simp [mkSeq]

@[simp] lemma mkSeq_succ (p : ℝ × (ℕ → ℝ)) (n : ℕ) : mkSeq p (n+1) = p.2 n := by
  simp [mkSeq]

@[simp] lemma measurable_mkSeq : Measurable mkSeq := by
  rw [measurable_pi_iff]
  intro n
  cases n with
  | zero => simp only [mkSeq_zero]; exact measurable_fst
  | succ m => simp only [mkSeq_succ]; exact (measurable_pi_apply m).comp measurable_snd

lemma mkSeq_injective : Function.Injective mkSeq := by
  intro p q h
  ext n
  · have := congrFun h 0; simpa using this
  · have := congrFun h (n+1); simpa using this

/-- Head and tail of a sequence; inverse of `mkSeq`. -/
def unSeq (x : ℕ → ℝ) : ℝ × (ℕ → ℝ) := (x 0, fun n => x (n+1))

@[simp] lemma measurable_unSeq : Measurable unSeq := by
  refine Measurable.prodMk ?_ ?_
  · exact measurable_pi_apply 0
  · rw [measurable_pi_iff]; intro n
    exact measurable_pi_apply (n+1)

@[simp] lemma unSeq_mkSeq (p : ℝ × (ℕ → ℝ)) : unSeq (mkSeq p) = p := by
  ext n <;> simp [unSeq]

@[simp] lemma mkSeq_unSeq (x : ℕ → ℝ) : mkSeq (unSeq x) = x := by
  funext n; cases n <;> simp [unSeq, mkSeq]

lemma Tf_mkSeq (k : ℕ) (p : ℝ × (ℕ → ℝ)) :
    Tf (k+1) (mkSeq p) = Tf k p.2 + p.1 := by
  induction k with
  | zero => simp [Tf]
  | succ k ih => rw [Tf_succ, ih, Tf_succ, mkSeq_succ]; ring

/-- Split a sequence into its first `k` terms and its tail. -/
def splitSeq (k : ℕ) (p : (Fin k → ℝ) × (ℕ → ℝ)) : ℕ → ℝ :=
  fun n => if h : n < k then p.1 ⟨n, h⟩ else p.2 (n - k)

lemma splitSeq_apply_lt {k : ℕ} {p : (Fin k → ℝ) × (ℕ → ℝ)} {n : ℕ} (h : n < k) :
    splitSeq k p n = p.1 ⟨n, h⟩ := by simp [splitSeq, h]

lemma splitSeq_apply_ge {k : ℕ} {p : (Fin k → ℝ) × (ℕ → ℝ)} {n : ℕ} (h : ¬ n < k) :
    splitSeq k p n = p.2 (n - k) := by simp [splitSeq, h]

@[simp] lemma measurable_splitSeq (k : ℕ) : Measurable (splitSeq k) := by
  rw [measurable_pi_iff]
  intro n
  by_cases h : n < k
  · have hh : (fun p : (Fin k → ℝ) × (ℕ → ℝ) => splitSeq k p n) = fun p => p.1 ⟨n, h⟩ := by
      funext p; exact splitSeq_apply_lt h
    rw [hh]
    exact (measurable_pi_apply (⟨n,h⟩ : Fin k)).comp measurable_fst
  · have hh : (fun p : (Fin k → ℝ) × (ℕ → ℝ) => splitSeq k p n) = fun p => p.2 (n - k) := by
      funext p; exact splitSeq_apply_ge h
    rw [hh]
    exact (measurable_pi_apply (n-k)).comp measurable_snd

lemma Tf_splitSeq (k : ℕ) (p : (Fin k → ℝ) × (ℕ → ℝ)) :
    Tf k (splitSeq k p) = ∑ i : Fin k, p.1 i := by
  rw [Tf, Finset.sum_range]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [splitSeq_apply_lt i.isLt]

/-- Three-way decomposition of a sequence into a prefix of length `k`, its `k`-th term,
and the remaining tail. -/
def splitSeq3 (k : ℕ) (q : ((Fin k → ℝ) × ℝ) × (ℕ → ℝ)) : ℕ → ℝ :=
  fun n => if h : n < k then q.1.1 ⟨n, h⟩ else if n = k then q.1.2 else q.2 (n - k - 1)

lemma splitSeq3_apply_lt {k : ℕ} {q : ((Fin k → ℝ) × ℝ) × (ℕ → ℝ)} {n : ℕ} (h : n < k) :
    splitSeq3 k q n = q.1.1 ⟨n, h⟩ := by simp [splitSeq3, h]

lemma splitSeq3_apply_eq {k : ℕ} (q : ((Fin k → ℝ) × ℝ) × (ℕ → ℝ)) : splitSeq3 k q k = q.1.2 := by
  simp [splitSeq3]

lemma splitSeq3_apply_gt {k : ℕ} {q : ((Fin k → ℝ) × ℝ) × (ℕ → ℝ)} {n : ℕ} (h : k < n) :
    splitSeq3 k q n = q.2 (n - k - 1) := by
  simp [splitSeq3, Nat.not_lt.mpr (le_of_lt h), Nat.ne_of_gt h]

@[simp] lemma measurable_splitSeq3 (k : ℕ) : Measurable (splitSeq3 k) := by
  rw [measurable_pi_iff]
  intro n
  by_cases h : n < k
  · have hh : (fun q : ((Fin k → ℝ) × ℝ) × (ℕ → ℝ) => splitSeq3 k q n) =
        fun q => q.1.1 ⟨n, h⟩ := by funext q; exact splitSeq3_apply_lt h
    rw [hh]
    exact (measurable_pi_apply (⟨n,h⟩ : Fin k)).comp (measurable_fst.comp measurable_fst)
  · by_cases h2 : n = k
    · have hh : (fun q : ((Fin k → ℝ) × ℝ) × (ℕ → ℝ) => splitSeq3 k q n) = fun q => q.1.2 := by
        funext q; rw [h2]; exact splitSeq3_apply_eq q
      rw [hh]
      exact measurable_snd.comp measurable_fst
    · have hk : k < n := lt_of_le_of_ne (not_lt.mp h) (Ne.symm h2)
      have hh : (fun q : ((Fin k → ℝ) × ℝ) × (ℕ → ℝ) => splitSeq3 k q n) =
          fun q => q.2 (n - k - 1) := by funext q; exact splitSeq3_apply_gt hk
      rw [hh]
      exact (measurable_pi_apply (n-k-1)).comp measurable_snd

lemma Tf_splitSeq3 (k : ℕ) (q : ((Fin k → ℝ) × ℝ) × (ℕ → ℝ)) :
    Tf k (splitSeq3 k q) = ∑ i : Fin k, q.1.1 i := by
  rw [Tf, Finset.sum_range]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [splitSeq3_apply_lt i.isLt]

end Work.ChenPlan.LinearSieve.Selberg.Alt
