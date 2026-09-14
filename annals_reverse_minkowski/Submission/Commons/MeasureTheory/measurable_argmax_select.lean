import Mathlib.Analysis.InnerProductSpace.Defs
import Mathlib.Analysis.Normed.Order.Lattice
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order

namespace Commons.MeasureTheory

/-- `boundMax f k a` is the maximum of `f 0 a, f 1 a, …, f k a`. -/
private def boundMax {α : Type*} (f : ℕ → α → ℝ) : ℕ → α → ℝ
  | 0 => f 0
  | (k + 1) => fun a => max (f (k + 1) a) (boundMax f k a)

/-- `boundIdx f k a` is the *least* index `m ≤ k` at which `f · a` attains its maximum
over `{0, …, k}`. -/
private noncomputable def boundIdx {α : Type*} (f : ℕ → α → ℝ) : ℕ → α → ℕ
  | 0 => fun _ => 0
  | (k + 1) => fun a => if boundMax f k a < f (k + 1) a then k + 1 else boundIdx f k a

private lemma measurable_boundMax {α : Type*} [MeasurableSpace α] (f : ℕ → α → ℝ)
    (hf : ∀ m, Measurable (f m)) : ∀ k, Measurable (boundMax f k) := by
  intro k
  induction k with
  | zero => simpa [boundMax] using hf 0
  | succ k ih =>
    rw [show boundMax f (k + 1) = fun a => max (f (k + 1) a) (boundMax f k a) from rfl]
    exact (hf (k + 1)).max ih

private lemma measurable_boundIdx {α : Type*} [MeasurableSpace α] (f : ℕ → α → ℝ)
    (hf : ∀ m, Measurable (f m)) : ∀ k, Measurable (boundIdx f k) := by
  intro k
  induction k with
  | zero => exact measurable_const
  | succ k ih =>
    have hset : MeasurableSet {a | boundMax f k a < f (k + 1) a} :=
      measurableSet_lt (measurable_boundMax f hf k) (hf (k + 1))
    rw [show boundIdx f (k + 1) =
        fun a => if boundMax f k a < f (k + 1) a then k + 1 else boundIdx f k a from rfl]
    exact Measurable.ite hset measurable_const ih

private lemma boundIdx_le {α : Type*} (f : ℕ → α → ℝ) : ∀ k a, boundIdx f k a ≤ k := by
  intro k
  induction k with
  | zero => intro a; simp [boundIdx]
  | succ k ih =>
    intro a
    rw [show boundIdx f (k + 1) a =
        if boundMax f k a < f (k + 1) a then k + 1 else boundIdx f k a from rfl]
    split_ifs with hp
    · exact le_refl _
    · exact le_trans (ih a) (Nat.le_succ k)

private lemma boundMax_eq {α : Type*} (f : ℕ → α → ℝ) :
    ∀ k a, boundMax f k a = f (boundIdx f k a) a := by
  intro k
  induction k with
  | zero => intro a; rfl
  | succ k ih =>
    intro a
    rw [show boundMax f (k + 1) a = max (f (k + 1) a) (boundMax f k a) from rfl]
    rw [show boundIdx f (k + 1) a =
        if boundMax f k a < f (k + 1) a then k + 1 else boundIdx f k a from rfl]
    split_ifs with hp
    · rw [max_eq_left (le_of_lt hp)]
    · rw [max_eq_right (le_of_not_gt hp), ih a]

private lemma le_boundMax {α : Type*} (f : ℕ → α → ℝ) :
    ∀ k a m, m ≤ k → f m a ≤ boundMax f k a := by
  intro k
  induction k with
  | zero =>
    intro a m hm
    rw [show m = 0 from Nat.eq_zero_of_le_zero hm, show boundMax f 0 a = f 0 a from rfl]
  | succ k ih =>
    intro a m hm
    rw [show boundMax f (k + 1) a = max (f (k + 1) a) (boundMax f k a) from rfl]
    rcases Nat.lt_or_eq_of_le hm with hm' | rfl
    · exact le_trans (ih a m (Nat.lt_succ_iff.mp hm')) (le_max_right _ _)
    · exact le_max_left _ _

private lemma boundIdx_argmax {α : Type*} (f : ℕ → α → ℝ) :
    ∀ k a m, m ≤ k → f m a ≤ f (boundIdx f k a) a := by
  intro k a m hm
  rw [← boundMax_eq f k a]
  exact le_boundMax f k a m hm

/-- Given measurable functions `f m : α → ℝ` for `m : ℕ`, there is a measurable
selection `n : α → ℕ` of a maximizer of `f 0, …, f M`, i.e. `n a ≤ M` and
`f m a ≤ f (n a) a` for all `m ≤ M`. -/
private lemma exists_measurable_argmax {α : Type*} [MeasurableSpace α] (f : ℕ → α → ℝ)
    (hf : ∀ m, Measurable (f m)) (M : ℕ) :
    ∃ n : α → ℕ, Measurable n ∧ (∀ a, n a ≤ M) ∧ (∀ a m, m ≤ M → f m a ≤ f (n a) a) :=
  ⟨boundIdx f M, measurable_boundIdx f hf M, fun a => boundIdx_le f M a,
    fun a m hm => boundIdx_argmax f M a m hm⟩

theorem measurable_argmax_select {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [MeasurableSpace E] [BorelSpace E] {α : Type*} [MeasurableSpace α] (ψ : ℕ → E) (φ : α → E) (hφ : ∀ m, Measurable fun a => inner ℝ (ψ m) (φ a)) (M : ℕ) : ∃ g : α → E, Measurable g ∧ (∀ a, ∃ m, m ≤ M ∧ g a = ψ m) ∧ (∀ a, ∀ m, m ≤ M → inner ℝ (ψ m) (φ a) ≤ inner ℝ (g a) (φ a)) := by
  obtain ⟨n, hn_meas, hn_le, hn_arg⟩ :=
    exists_measurable_argmax (fun m a => inner ℝ (ψ m) (φ a)) hφ M
  refine ⟨fun a => ψ (n a), ?_, ?_, ?_⟩
  · exact (measurable_of_countable ψ).comp hn_meas
  · intro a; exact ⟨n a, hn_le a, rfl⟩
  · intro a m hm
    exact hn_arg a m hm

end Commons.MeasureTheory