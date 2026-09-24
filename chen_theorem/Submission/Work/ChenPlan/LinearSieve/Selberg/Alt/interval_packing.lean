import Mathlib
import Submission.Work.ChenPlan.LinearSieve.Selberg.Alt.vocab

/-!
# Interval packing (Earliest-Deadline-First scheduling)

This file proves the combinatorial "packing" lemma used to build the `K`-tuple of intervals
`(a j, b j]` on which the events `IntervalHit` in `interval_events` are mounted: one has to
realise prescribed lengths `m j` without overlapping, inside the individual "deadlines"
`log (1 / t j)`.

The content is the classical single–machine scheduling criterion.  Jobs `j` have a positive
processing time `f j` and a deadline `d j`; all are available at time `0`.  A feasible
non-preemptive schedule *back to back* exists if and only if, for every `s`, the total
processing time of the jobs with deadline `≤ s` does not exceed `s`.  The schedule is
Earliest-Deadline-First, i.e. the jobs are ordered by the pair `(d j, index)`.

The order is encoded abstractly by a strict total order relation `r` on the (finite) index
type, required to be refined by the deadlines (`r i j → d i ≤ d j`); this keeps the
combinatorial core independent of the concrete `Fin n` situation.
-/

namespace Work.ChenPlan.LinearSieve.Selberg.Alt

/-- **Scheduling lemma.**
Let `r` be a strict total order on a finite type `ι`, refined by a "deadline" function `d`
(`r i j → d i ≤ d j`), and let `f > 0` satisfy the feasibility condition
`∑_{k : d k ≤ s} f k ≤ s` for every `s ≥ 0`.  Then there are non-negative starting times `a`
and finishing times `b` with `b i - a i = f i`, `b i ≤ d i`, and the intervals `(a i, b i]`
pairwise disjoint. -/
theorem exists_packing_of_strictTotalOrder {ι : Type*} [Fintype ι]
    (r : ι → ι → Prop) (hirr : ∀ i, ¬ r i i)
    (htrans : ∀ i j k, r i j → r j k → r i k)
    (htotal : ∀ i j, i ≠ j → r i j ∨ r j i)
    (f d : ι → ℝ) (hf : ∀ i, 0 < f i)
    (hle : ∀ i j, r i j → d i ≤ d j)
    (hmeas : ∀ s : ℝ, 0 ≤ s → ∑ k ∈ Finset.univ.filter (fun k => d k ≤ s), f k ≤ s) :
    ∃ a b : ι → ℝ, (∀ i, 0 ≤ a i) ∧ (∀ i, b i - a i = f i) ∧ (∀ i, b i ≤ d i) ∧
      (∀ i i', i ≠ i' → Disjoint (Set.Ioc (a i) (b i)) (Set.Ioc (a i') (b i'))) := by
  classical
  -- the feasibility condition forces the deadlines to be positive
  have hdpos : ∀ i, 0 < d i := by
    intro i
    by_contra h
    have h' : d i ≤ 0 := not_lt.mp h
    have hmem : i ∈ Finset.univ.filter (fun k => d k ≤ 0) :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ i, h'⟩
    have hle1 := Finset.single_le_sum (fun k _ => le_of_lt (hf k)) hmem
    have h0 := hmeas 0 le_rfl
    linarith [hf i]
  -- Earliest-deadline-first: the predecessors of `j`
  let S : ι → Finset ι := fun j => Finset.univ.filter (fun k => r k j)
  -- starting time of the job `j`
  let a : ι → ℝ := fun j => ∑ k ∈ S j, f k
  have hSkeep : ∀ j, j ∉ S j := by
    intro j
    simp only [S, Finset.mem_filter, Finset.mem_univ, true_and]
    exact hirr j
  have hsum : ∀ j, a j + f j = ∑ k ∈ insert j (S j), f k := by
    intro j
    rw [Finset.sum_insert (hSkeep j)]
    simp only [a]
    ring
  -- the predecessors of `k` are predecessors of `j` whenever `r k j`
  have hpk : ∀ k j, r k j → a k + f k ≤ a j := by
    intro k j hkj
    have hsub : insert k (S k) ⊆ S j := by
      intro i hi
      simp only [Finset.mem_insert, S, Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
      rcases hi with rfl | hi
      · exact hkj
      · exact htrans i k j hi hkj
    calc a k + f k = ∑ i ∈ insert k (S k), f i := hsum k
      _ ≤ ∑ i ∈ S j, f i :=
          Finset.sum_le_sum_of_subset_of_nonneg hsub (fun i _ _ => le_of_lt (hf i))
      _ = a j := rfl
  refine ⟨a, fun j => a j + f j, ?_, ?_, ?_, ?_⟩
  · intro j
    simp only [a]
    exact Finset.sum_nonneg (fun k _ => le_of_lt (hf k))
  · intro j
    ring
  · -- the job `j` finishes before its deadline
    intro j
    have hsub : insert j (S j) ⊆ Finset.univ.filter (fun k => d k ≤ d j) := by
      intro k hk
      simp only [Finset.mem_insert, S, Finset.mem_filter, Finset.mem_univ, true_and] at hk ⊢
      rcases hk with rfl | hk
      · exact le_rfl
      · exact hle k j hk
    change a j + f j ≤ d j
    rw [hsum j]
    exact le_trans (Finset.sum_le_sum_of_subset_of_nonneg hsub (fun i _ _ => le_of_lt (hf i)))
      (hmeas (d j) (le_of_lt (hdpos j)))
  · -- disjointness of the intervals
    intro i i' hne
    rcases htotal i i' hne with h | h
    · have hb := hpk i i' h
      apply Set.disjoint_left.mpr
      intro x hx hx'
      exact absurd (le_trans hx.2 hb) (not_le.mpr hx'.1)
    · have hb := hpk i' i h
      apply Set.disjoint_left.mpr
      intro x hx hx'
      exact absurd (le_trans hx'.2 hb) (not_le.mpr hx.1)

/-- **Interval packing.**  Given positive "scales" `t j` and positive lengths `m j` such that,
for every `u ∈ (0,1]`, the total length of the jobs with `t j ≥ u` is at most `log (1/u)`,
there are intervals `(a j, b j]` (with `a j ≥ 0`), of the prescribed lengths `m j`, sitting
below the individual deadlines `log (1 / t j)` and pairwise disjoint.

This is the Earliest-Deadline-First schedule for the jobs `j` with processing time `m j` and
deadline `log (1 / t j)`: substituting `u = exp (-s)` turns the hypothesis into the feasibility
condition `∑_{j : log (1/t j) ≤ s} m j ≤ s`, and ordering the jobs lexicographically by
`(log (1 / t j), j)` produces the schedule. -/
theorem interval_packing {n : ℕ} (t m : Fin n → ℝ) (ht : ∀ j, 0 < t j) (hm : ∀ j, 0 < m j)
    (hcon : ∀ u : ℝ, 0 < u → u ≤ 1 →
      ∑ j ∈ Finset.univ.filter (fun j : Fin n => u ≤ t j), m j ≤ Real.log (1 / u)) :
    ∃ a b : Fin n → ℝ, (∀ j, 0 ≤ a j) ∧ (∀ j, b j - a j = m j)
      ∧ (∀ j, b j ≤ Real.log (1 / t j))
      ∧ Work.ChenPlan.LinearSieve.Selberg.Alt.PairwiseDisjointIoc a b := by
  classical
  -- `u = 1` shows that every `t j` is `< 1`, hence every deadline `log (1/t j)` is positive
  have hlt1 : ∀ j : Fin n, t j < 1 := by
    intro j
    by_contra h
    have h' : (1 : ℝ) ≤ t j := not_lt.mp h
    have hmem : j ∈ Finset.univ.filter (fun k : Fin n => (1 : ℝ) ≤ t k) :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ j, h'⟩
    have hsingle : m j ≤ ∑ k ∈ Finset.univ.filter (fun k : Fin n => (1 : ℝ) ≤ t k), m k :=
      Finset.single_le_sum (fun i _ => le_of_lt (hm i)) hmem
    have h1 := hcon 1 zero_lt_one le_rfl
    simp only [Real.log_one, one_div_one] at h1
    linarith [hm j]
  -- the hypothesis of the scheduling lemma
  have hmeas : ∀ s : ℝ, 0 ≤ s →
      ∑ k ∈ Finset.univ.filter (fun k : Fin n => Real.log (1 / t k) ≤ s), m k ≤ s := by
    intro s hs
    have hu0 : 0 < Real.exp (-s) := Real.exp_pos _
    have hu1 : Real.exp (-s) ≤ 1 := by
      have h : Real.exp (-s) ≤ Real.exp 0 := Real.exp_le_exp.mpr (by linarith)
      simpa using h
    have h := hcon (Real.exp (-s)) hu0 hu1
    have hlog : Real.log (1 / Real.exp (-s)) = s := by
      rw [one_div, Real.exp_neg, inv_inv, Real.log_exp]
    rw [hlog] at h
    -- `exp (-s) ≤ t k ↔ log (1 / t k) ≤ s`
    have hfilter : Finset.univ.filter (fun k : Fin n => Real.log (1 / t k) ≤ s)
        = Finset.univ.filter (fun k : Fin n => Real.exp (-s) ≤ t k) := by
      apply Finset.filter_congr
      intro k _
      constructor
      · intro hk
        have hk' : -Real.log (t k) ≤ s := by
          simpa [one_div, Real.log_inv] using hk
        have h2 : -s ≤ Real.log (t k) := by linarith
        calc Real.exp (-s) ≤ Real.exp (Real.log (t k)) := Real.exp_le_exp.mpr h2
          _ = t k := Real.exp_log (ht k)
      · intro hk
        have h1 : Real.log (Real.exp (-s)) ≤ Real.log (t k) :=
          Real.log_le_log (Real.exp_pos _) hk
        rw [Real.log_exp] at h1
        rw [one_div, Real.log_inv]
        linarith
    rw [hfilter]
    exact h
  -- apply the scheduling lemma to the lexicographic order on `(log (1 / t j), j)`
  obtain ⟨a, b, ha, hab, hb, hdisj⟩ :=
    exists_packing_of_strictTotalOrder (ι := Fin n)
      (r := fun k j : Fin n => Real.log (1 / t k) < Real.log (1 / t j)
        ∨ (Real.log (1 / t k) = Real.log (1 / t j) ∧ k < j))
      (by intro i; simp)
      (by
        intro i j k hij hjk
        rcases hij with h1 | ⟨h1, h1'⟩ <;> rcases hjk with h2 | ⟨h2, h2'⟩
        · left; linarith
        · left; linarith
        · left; linarith
        · right; exact ⟨by linarith, lt_trans h1' h2'⟩)
      (by
        intro i j hij
        rcases lt_trichotomy (Real.log (1 / t i)) (Real.log (1 / t j)) with h | h | h
        · left; left; exact h
        · rcases lt_or_gt_of_ne hij with hlt | hgt
          · left; right; exact ⟨h, hlt⟩
          · right; right; exact ⟨h.symm, hgt⟩
        · right; left; exact h)
      m (fun j => Real.log (1 / t j)) hm
      (by intro i j h; rcases h with h | ⟨h, _⟩ <;> linarith)
      hmeas
  exact ⟨a, b, ha, hab, hb, hdisj⟩

end Work.ChenPlan.LinearSieve.Selberg.Alt
