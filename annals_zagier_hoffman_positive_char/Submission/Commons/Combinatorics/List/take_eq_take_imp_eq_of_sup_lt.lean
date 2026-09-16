import Mathlib.Data.List.TakeWhile
import Mathlib.Order.Lattice.Nat

namespace Commons.Combinatorics.List

/-- `take` distributes over `zip`. -/
private lemma take_zip {α β : Type*} :
    ∀ (l₁ : List α) (l₂ : List β) (n : ℕ),
      (l₁.zip l₂).take n = (l₁.take n).zip (l₂.take n)
  | [], l₂, n => by simp
  | a :: as, l₂, n => by
      cases l₂ with
      | nil => simp
      | cons b bs =>
        cases n with
        | zero => simp
        | succ m => simp [take_zip as bs m]

/-- Zipping a list with itself is the diagonal map. -/
private lemma zip_self {α : Type*} (l : List α) :
    l.zip l = l.map (fun x => (x, x)) := by
  induction l with
  | nil => simp
  | cons a as ih => simp [ih]

/-- Taking the `takeWhile` of a diagonal zip leaves it unchanged. -/
private lemma takeWhile_zip_self {α : Type*} [DecidableEq α] (l : List α) :
    (l.zip l).takeWhile (fun p : α × α => p.1 = p.2) = l.zip l := by
  rw [zip_self, List.takeWhile_map]
  have h : List.takeWhile ((fun p : α × α => p.1 = p.2) ∘ fun x => (x, x)) l = l := by
    rw [List.takeWhile_eq_self_iff]
    intro x _
    simp
  rw [h]

/-- The common-prefix length is at least `k` when the two lists agree on their first `k`
entries and the first list is at least `k` long. -/
private lemma le_length_takeWhile_zip {α : Type*} [DecidableEq α] {a b : List α} {k : ℕ}
    (h : a.take k = b.take k) (ha : k ≤ a.length) :
    k ≤ ((a.zip b).takeWhile (fun p : α × α => p.1 = p.2)).length := by
  have key : (a.zip b).take k = (a.take k).zip (a.take k) := by
    rw [take_zip, h]
  have htw : ((a.zip b).takeWhile (fun p : α × α => p.1 = p.2)).take k
      = (a.take k).zip (a.take k) := by
    rw [List.take_takeWhile, key, takeWhile_zip_self]
  have hlen := congrArg List.length htw
  simp only [List.length_take, List.length_zip, min_self] at hlen
  rw [Nat.min_eq_left ha] at hlen
  exact (min_eq_left_iff).mp hlen

/-- If two distinct lists agree on their first `k` entries then their common prefix has
length at least `k`. -/
private lemma le_length_takeWhile_zip_of_take_eq_of_ne {α : Type*} [DecidableEq α]
    {a b : List α} {k : ℕ} (h : a.take k = b.take k) (hne : a ≠ b) :
    k ≤ ((a.zip b).takeWhile (fun p : α × α => p.1 = p.2)).length := by
  by_cases ha : k ≤ a.length
  · exact le_length_takeWhile_zip h ha
  · exfalso
    simp only [not_le] at ha
    have h1 : a = b.take k := by
      rw [← List.take_of_length_le (le_of_lt ha)]
      exact h
    have hlenb : (b.take k).length = a.length := by rw [← h1]
    rw [List.length_take] at hlenb
    have hble : b.length ≤ k := by
      by_contra hb
      simp only [not_le] at hb
      rw [Nat.min_eq_left (le_of_lt hb)] at hlenb
      omega
    have hb' : b.take k = b := List.take_of_length_le hble
    exact hne (h1.trans hb')

theorem take_eq_take_imp_eq_of_sup_lt {α : Type*} [DecidableEq α] (S : Finset (List α))
    (s₀ : List α) {k : ℕ}
    (hk : (S.filter (fun s => s ≠ s₀)).sup
      (fun s => ((s.zip s₀).takeWhile (fun p => p.1 = p.2)).length) < k)
    {s : List α} (hs : s ∈ S) (h : s.take k = s₀.take k) : s = s₀ := by
  by_contra hne
  have hmem : s ∈ S.filter (fun s => s ≠ s₀) := Finset.mem_filter.mpr ⟨hs, hne⟩
  have hle : ((s.zip s₀).takeWhile (fun p => p.1 = p.2)).length ≤
      (S.filter (fun s => s ≠ s₀)).sup
        (fun s => ((s.zip s₀).takeWhile (fun p => p.1 = p.2)).length) :=
    Finset.le_sup (f := fun s => ((s.zip s₀).takeWhile (fun p => p.1 = p.2)).length) hmem
  have hlt : ((s.zip s₀).takeWhile (fun p => p.1 = p.2)).length < k :=
    lt_of_le_of_lt hle hk
  have hge : k ≤ ((s.zip s₀).takeWhile (fun p => p.1 = p.2)).length :=
    le_length_takeWhile_zip_of_take_eq_of_ne h hne
  omega

end Commons.Combinatorics.List