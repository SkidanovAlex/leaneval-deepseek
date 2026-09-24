import Mathlib
import Submission.Work.ChenPlan.LinearSieve.Selberg.Alt.vocab

namespace Work.ChenPlan.LinearSieve.Selberg

/-- **Deterministic packing bound for the reference sum.**

Let `E : ℕ → Ω → ℝ` be a sequence of increments, `S k = E 0 + ⋯ + E (k-1)` its partial sums (so
`S 0 = 0`).  Suppose the intervals `(a j, b j]` are pairwise disjoint, `a j ≥ 0` and the weights
`t j > 0` satisfy `b j ≤ log (1 / t j)`.  Then, whenever `Σ_{k ≥ 1} e^{-S_k}` converges,

  `Σ_j t_j · 1{some partial sum lies in (a j, b j]} ≤ Σ_{k ≥ 1} e^{-S_k}`.

Indeed `a j ≥ 0` rules out the witness `k = 0`, and a partial sum falling in `(a j, b j]` is at
most `b j`, whence `t j ≤ e^{-b j} ≤ e^{-S_k}`; distinct intervals are hit by distinct partial
sums because they are disjoint. -/
theorem sum_levels_mul_hitIndicator_le_refSum {Ω : Type*} {n : ℕ} (E : ℕ → Ω → ℝ)
    (t : Fin n → ℝ) (a b : Fin n → ℝ) (ht : ∀ j, 0 < t j) (ha : ∀ j, 0 ≤ a j)
    (hb : ∀ j, b j ≤ Real.log (1 / t j))
    (hdisj : Work.ChenPlan.LinearSieve.Selberg.Alt.PairwiseDisjointIoc a b) (ω : Ω)
    (hsum : Summable fun k : ℕ =>
      Real.exp (- Work.ChenPlan.LinearSieve.Selberg.Alt.partialSum (fun i => E i ω) (k + 1))) :
    (∑ j, t j * (Work.ChenPlan.LinearSieve.Selberg.Alt.IntervalHit E (a j) (b j)).indicator
        (fun _ => (1 : ℝ)) ω)
      ≤ Work.ChenPlan.LinearSieve.Selberg.Alt.refSum (fun i => E i ω) := by
  classical
  set S : ℕ → ℝ := fun k =>
    Work.ChenPlan.LinearSieve.Selberg.Alt.partialSum (fun i => E i ω) k with hS
  set f : ℕ → ℝ := fun k => Real.exp (- S (k + 1)) with hf
  have hfpos : ∀ k, 0 ≤ f k := fun k => le_of_lt (Real.exp_pos _)
  have hsumf : Summable f := by
    simpa only [hf, hS] using hsum
  -- a hit can only be witnessed by an index `k ≥ 1`, since `S 0 = 0` and `a j ≥ 0`
  have hmem : ∀ j, ω ∈ Work.ChenPlan.LinearSieve.Selberg.Alt.IntervalHit E (a j) (b j) ↔
      ∃ k, 1 ≤ k ∧ S k ∈ Set.Ioc (a j) (b j) := by
    intro j
    constructor
    · rintro ⟨k, hk⟩
      rcases Nat.eq_zero_or_pos k with rfl | hkpos
      · simp only [Work.ChenPlan.LinearSieve.Selberg.Alt.partialSum,
          Finset.sum_range_zero] at hk
        exact absurd hk.1 (not_lt.mpr (ha j))
      · exact ⟨k, hkpos, hk⟩
    · rintro ⟨k, _, hk⟩
      exact ⟨k, hk⟩
  -- choose a witness `kk j` for every hit interval
  let kk : Fin n → ℕ := fun j =>
    if h : ω ∈ Work.ChenPlan.LinearSieve.Selberg.Alt.IntervalHit E (a j) (b j) then
      Nat.find ((hmem j).mp h) else 0
  have hkk : ∀ j (h : ω ∈ Work.ChenPlan.LinearSieve.Selberg.Alt.IntervalHit E (a j) (b j)),
      1 ≤ kk j ∧ S (kk j) ∈ Set.Ioc (a j) (b j) := by
    intro j h
    have h' : kk j = Nat.find ((hmem j).mp h) := by simp only [kk, dif_pos h]
    rw [h']
    exact Nat.find_spec ((hmem j).mp h)
  set I : Finset (Fin n) :=
    Finset.univ.filter (fun j => ω ∈ Work.ChenPlan.LinearSieve.Selberg.Alt.IntervalHit E (a j) (b j))
    with hI
  -- distinct hit intervals have distinct witnesses, by disjointness
  have hkk_inj : Set.InjOn kk ↑I := by
    intro j hj j' hj' hEq
    by_contra hne
    have h1 := (hkk j (Finset.mem_filter.mp hj).2).2
    have h2 := (hkk j' (Finset.mem_filter.mp hj').2).2
    rw [hEq] at h1
    exact (Set.disjoint_left.mp (hdisj j j' hne)) h1 h2
  have hLHS : ∑ j : Fin n, t j * (Work.ChenPlan.LinearSieve.Selberg.Alt.IntervalHit E (a j) (b j)).indicator
        (fun _ => (1 : ℝ)) ω = ∑ j ∈ I, t j := by
    have h1 : ∀ j : Fin n, t j *
        (Work.ChenPlan.LinearSieve.Selberg.Alt.IntervalHit E (a j) (b j)).indicator
          (fun _ => (1 : ℝ)) ω
        = if ω ∈ Work.ChenPlan.LinearSieve.Selberg.Alt.IntervalHit E (a j) (b j) then t j else 0 := by
      intro j
      rw [Set.indicator_apply]
      by_cases h : ω ∈ Work.ChenPlan.LinearSieve.Selberg.Alt.IntervalHit E (a j) (b j) <;> simp [h]
    simp only [h1, hI]
    rw [Finset.sum_filter]
  -- each weight is dominated by the exponential of the corresponding partial sum
  have hbase : ∑ j ∈ I, t j ≤ ∑ j ∈ I, f (kk j - 1) := by
    apply Finset.sum_le_sum
    intro j hj
    obtain ⟨hk1, hk2⟩ := hkk j (Finset.mem_filter.mp hj).2
    have hkey : f (kk j - 1) = Real.exp (- S (kk j)) := by
      simp only [hf, Nat.sub_add_cancel hk1]
    rw [hkey]
    have hlog : Real.log (1 / t j) = - Real.log (t j) := by
      rw [one_div, Real.log_inv]
    have hb' : Real.log (t j) ≤ - S (kk j) := by
      have := hb j
      rw [hlog] at this
      linarith [hk2.2]
    calc t j = Real.exp (Real.log (t j)) := (Real.exp_log (ht j)).symm
      _ ≤ Real.exp (- S (kk j)) := Real.exp_le_exp.mpr hb'
  have hinj_sub : Set.InjOn (fun j => kk j - 1) ↑I := by
    intro j hj j' hj' hEq
    change kk j - 1 = kk j' - 1 at hEq
    have h1 := (hkk j (Finset.mem_filter.mp hj).2).1
    have h2 := (hkk j' (Finset.mem_filter.mp hj').2).1
    have h3 : kk j = kk j' := by omega
    exact hkk_inj hj hj' h3
  have hsum_img : ∑ j ∈ I, f (kk j - 1) = ∑ k ∈ I.image (fun j => kk j - 1), f k :=
    (Finset.sum_image hinj_sub).symm
  calc ∑ j, t j * (Work.ChenPlan.LinearSieve.Selberg.Alt.IntervalHit E (a j) (b j)).indicator
        (fun _ => (1 : ℝ)) ω
      = ∑ j ∈ I, t j := hLHS
    _ ≤ ∑ j ∈ I, f (kk j - 1) := hbase
    _ = ∑ k ∈ I.image (fun j => kk j - 1), f k := hsum_img
    _ ≤ ∑' k, f k := Summable.sum_le_tsum _ (fun k _ => hfpos k) hsumf
    _ = Work.ChenPlan.LinearSieve.Selberg.Alt.refSum (fun i => E i ω) := by
        simp only [hf, hS, Work.ChenPlan.LinearSieve.Selberg.Alt.refSum]

end Work.ChenPlan.LinearSieve.Selberg
