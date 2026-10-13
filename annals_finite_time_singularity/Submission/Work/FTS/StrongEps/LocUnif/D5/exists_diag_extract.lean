import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
import Mathlib.Order.CompletePartialOrder

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# Abstract diagonal extraction along a.e.-convergent subsequences

`Work.FTS.StrongEps.LocUnif.D5.exists_diag_extract`: given a doubly-indexed family
`F : ℕ → ℕ → α → ℝ`, targets `G : ℕ → α → ℝ` and the hypothesis

* for every `k` and every strictly increasing `σ : ℕ → ℕ` there is a strictly increasing
  `ν : ℕ → ℕ` with `F k (σ (ν n)) p → G k p` for almost every `p`,

produce a **single** strictly increasing `Φ` with `F k (Φ n) p → G k p` for a.e. `p`, for every `k`.

The proof is the classical diagonal extraction.  Build the nested sequences
`S 0 = id`, `S (k+1) = S k ∘ ν k`, where `ν k` is the sequence supplied by the hypothesis at index
`k` for the sequence `S k`.  Each `S j` is strictly increasing, `range (S j) ⊆ range (S i)` for
`i ≤ j`, and for every `k` one has `F k (S (k+1) n) p → G k p` for a.e. `p`.  Then set
`Φ n := S n (m n)`, with `m n` chosen recursively so that `Φ` is strictly increasing — this makes
the tail `{n : n ≥ k+1}` of `Φ` a strictly increasing subsequence of `S (k+1)`, so it inherits the
a.e. convergence for the index `k`, and the countably many exceptional null sets are collected into
a single one.
-/

open Filter MeasureTheory

namespace Work.FTS.StrongEps.LocUnif.D5

/-- A strictly increasing sequence `ℕ → ℕ` is unbounded. -/
theorem strictMono_exists_gt (f : ℕ → ℕ) (hf : StrictMono f) (b : ℕ) : ∃ j, f j > b := by
  refine ⟨b + 1, ?_⟩
  have h1 : b + 1 ≤ f (b + 1) := hf.id_le (b + 1)
  omega

/-- If `u` and `σ` are strictly increasing and every value of `u` lies in the range of `σ`, then
`u` is a subsequence of `σ`; in particular a limit along `σ` is also a limit along `u`. -/
theorem tendsto_of_strictMono_range {β : Type*} [TopologicalSpace β] {a : ℕ → β} {L : β}
    {u σ : ℕ → ℕ} (hu : StrictMono u) (hσ : StrictMono σ)
    (hrange : ∀ n, u n ∈ Set.range σ)
    (ha : Tendsto (fun m => a (σ m)) atTop (nhds L)) :
    Tendsto (fun n => a (u n)) atTop (nhds L) := by
  classical
  have hr_spec : ∀ n, σ (Nat.find (hrange n)) = u n := fun n => Nat.find_spec (hrange n)
  have hr_mono : StrictMono (fun n => Nat.find (hrange n)) := by
    intro m n hmn
    by_contra hle
    have hle' : Nat.find (hrange n) ≤ Nat.find (hrange m) := le_of_not_gt hle
    have h1 : σ (Nat.find (hrange n)) ≤ σ (Nat.find (hrange m)) := hσ.monotone hle'
    rw [hr_spec n, hr_spec m] at h1
    exact absurd (hu hmn) (not_lt.mpr h1)
  have heq : (fun n => a (u n)) = (fun m => a (σ m)) ∘ (fun n => Nat.find (hrange n)) := by
    funext n
    rw [Function.comp_apply, hr_spec n]
  rw [heq]
  exact ha.comp hr_mono.tendsto_atTop

/-- Tail version of `tendsto_of_strictMono_range`: the range condition is needed only from `N` on. -/
theorem tendsto_of_strictMono_range' {β : Type*} [TopologicalSpace β] {a : ℕ → β} {L : β}
    {u σ : ℕ → ℕ} (hu : StrictMono u) (hσ : StrictMono σ) (N : ℕ)
    (hrange : ∀ n, N ≤ n → u n ∈ Set.range σ)
    (ha : Tendsto (fun m => a (σ m)) atTop (nhds L)) :
    Tendsto (fun n => a (u n)) atTop (nhds L) := by
  rw [← tendsto_add_atTop_iff_nat (f := fun n => a (u n)) N]
  refine tendsto_of_strictMono_range (hu.comp (fun a b h => Nat.add_lt_add_right h N)) hσ ?_ ha
  intro n
  exact hrange (n + N) (by omega)

/-- The nested strictly increasing sequences `S k` of the diagonal extraction, defined by
`S 0 = id` and `S (k+1) = S k ∘ ν k`, where `ν k` is the sequence furnished by the hypothesis at
index `k` applied to `S k`. -/
noncomputable def diagNestedSeq {α : Type*} [MeasurableSpace α] {μ : MeasureTheory.Measure α}
    {F : ℕ → ℕ → α → ℝ} {G : ℕ → α → ℝ}
    (h : ∀ k : ℕ, ∀ σ : ℕ → ℕ, StrictMono σ → ∃ ν : ℕ → ℕ, StrictMono ν ∧
      ∀ᵐ p ∂μ, Filter.Tendsto (fun n => F k (σ (ν n)) p) Filter.atTop (nhds (G k p))) :
    ℕ → {f : ℕ → ℕ // StrictMono f} :=
  Nat.rec ⟨id, strictMono_id⟩
    (fun k prev => ⟨prev.1 ∘ (h k prev.1 prev.2).choose,
      prev.2.comp ((h k prev.1 prev.2).choose_spec).1⟩)

/-- **Diagonal extraction.**  If for every `k` and every strictly increasing `σ` the sequence
`F k (σ (ν n))` converges to `G k` a.e. along some further strictly increasing `ν`, then a single
strictly increasing `Φ` converges a.e. for *all* `k` at once. -/
theorem exists_diag_extract {α : Type*} [MeasurableSpace α] {μ : MeasureTheory.Measure α}
    {F : ℕ → ℕ → α → ℝ} {G : ℕ → α → ℝ}
    (h : ∀ k : ℕ, ∀ σ : ℕ → ℕ, StrictMono σ → ∃ ν : ℕ → ℕ, StrictMono ν ∧
      ∀ᵐ p ∂μ, Filter.Tendsto (fun n => F k (σ (ν n)) p) Filter.atTop (nhds (G k p))) :
    ∃ Φ : ℕ → ℕ, StrictMono Φ ∧ ∀ k : ℕ,
      ∀ᵐ p ∂μ, Filter.Tendsto (fun n => F k (Φ n) p) Filter.atTop (nhds (G k p)) := by
  classical
  set S : ℕ → {f : ℕ → ℕ // StrictMono f} := diagNestedSeq h with hS
  -- unfolding lemma for the recursion
  have S_succ : ∀ k, (S (k+1)).1 = (S k).1 ∘ (h k (S k).1 (S k).2).choose := by
    intro k
    rw [hS]
    rfl
  have S_zero : (S 0).1 = id := by rw [hS]; rfl
  -- the a.e. convergence along `S (k+1)` for the index `k`
  have hconv : ∀ k : ℕ,
      ∀ᵐ p ∂μ, Filter.Tendsto (fun n => F k ((S (k+1)).1 n) p) Filter.atTop (nhds (G k p)) := by
    intro k
    have hk := (h k (S k).1 (S k).2).choose_spec.2
    rw [S_succ k]
    simpa only [Function.comp_apply] using hk
  -- the ranges are nested
  have hrange_step : ∀ k, Set.range (S (k+1)).1 ⊆ Set.range (S k).1 := by
    intro k x hx
    obtain ⟨j, hj⟩ := hx
    refine ⟨(h k (S k).1 (S k).2).choose j, ?_⟩
    rw [← hj, S_succ k]
    rfl
  have hrange_le : ∀ k n, k ≤ n → Set.range (S n).1 ⊆ Set.range (S k).1 := by
    intro k n hkn
    induction n, hkn using Nat.le_induction with
    | base => exact subset_rfl
    | succ m hm ih => exact (hrange_step m).trans ih
  -- the diagonal: `Φ n = S n (m n)` with `m` chosen so that `Φ` is strictly increasing
  set Φ : ℕ → ℕ := Nat.rec 0 (fun n prev =>
    (S (n+1)).1 (Nat.find (strictMono_exists_gt (S (n+1)).1 (S (n+1)).2 prev))) with hΦ
  have Φ_succ : ∀ n, Φ (n+1)
      = (S (n+1)).1 (Nat.find (strictMono_exists_gt (S (n+1)).1 (S (n+1)).2 (Φ n))) := by
    intro n
    rw [hΦ]
  have Φ_lt_succ : ∀ n, Φ n < Φ (n+1) := by
    intro n
    rw [Φ_succ n]
    exact Nat.find_spec (strictMono_exists_gt (S (n+1)).1 (S (n+1)).2 (Φ n))
  have Φ_mono : StrictMono Φ := strictMono_nat_of_lt_succ Φ_lt_succ
  -- `Φ n` lies in the range of `S n`
  have Φ_mem : ∀ n, Φ n ∈ Set.range (S n).1 := by
    intro n
    cases n with
    | zero =>
      refine ⟨0, ?_⟩
      rw [hΦ]
      rfl
    | succ n =>
      refine ⟨Nat.find (strictMono_exists_gt (S (n+1)).1 (S (n+1)).2 (Φ n)), ?_⟩
      rw [Φ_succ n]
  refine ⟨Φ, Φ_mono, fun k => ?_⟩
  refine (hconv k).mono (fun p hp => ?_)
  exact tendsto_of_strictMono_range' (a := fun m => F k m p) (L := G k p)
    Φ_mono (S (k+1)).2 (k+1) (fun n hn => hrange_le (k+1) n hn (Φ_mem n)) hp

end Work.FTS.StrongEps.LocUnif.D5
