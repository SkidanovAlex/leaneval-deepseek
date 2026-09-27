import Mathlib
import Submission.Work.Whitney.ArcFraming

/-!
# Chains of charts along an arc, on an arbitrary parameter interval

`Work.Whitney.IsArcChain` (in `Submission/Work/Whitney/ArcFraming.lean`) packages a chain of charts
following a continuous arc `γ : ℝ → M` from the parameter `0` to the parameter `1`.  For the
transport argument along a chain we need the same notion on an arbitrary parameter interval
`[a, b]`, together with two elementary "surgery" operations: dropping the first chart (the *tail*
of a chain) and moving the starting parameter of a chain forward.

* `ChainData γ a b c d N dd t` : the raw data of such a chain (charts `dd`, junction parameters
  `t`), so that induction on `N` is possible;
* `IsArcChainOn γ a b c d` : the existential version; by construction
  `IsArcChain γ c d ↔ IsArcChainOn γ 0 1 c d`;
* `chainData_tail` : the tail of a chain, starting at the second chart;
* `chainData_restrictStart` : a chain whose starting parameter has been moved forward, keeping the
  same charts.
-/

namespace Work.Whitney

open scoped Manifold ContDiff
open Topology Filter

set_option linter.unusedSectionVars false

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) ((⊤ : ℕ∞) : WithTop ℕ∞) M]

/-- The raw data of a chain of charts along `γ` on the parameter interval `[a, b]`:
charts `dd 0, …, dd N` and junction parameters `a = t 0 ≤ ⋯ ≤ t N = b`, with every sub-arc
`γ '' [t i, t i+1]` inside the source of `dd i`, positive transitions at the junctions, and the
endpoint conditions. -/
def ChainData (γ : ℝ → M) (a b : ℝ)
    (c d : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n)))
    (N : ℕ) (dd : Fin (N + 1) → OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n)))
    (t : Fin (N + 1) → ℝ) : Prop :=
  t 0 = a ∧ t (Fin.last N) = b ∧ Monotone t ∧ dd 0 = c ∧ dd (Fin.last N) = d ∧
  γ a ∈ c.source ∧ γ b ∈ d.source ∧
  (∀ i : Fin (N + 1), IsSmoothChart (dd i)) ∧
  (∀ i : Fin N, γ '' Set.Icc (t i.castSucc) (t i.succ) ⊆ (dd i.castSucc).source) ∧
  (∀ i : Fin N, γ (t i.succ) ∈ (dd i.succ).source ∧
    PosTransitionAt (dd i.castSucc) (dd i.succ) (γ (t i.succ)))

/-- A chain of charts along `γ` from `γ a` (chart `c`) to `γ b` (chart `d`).  For `a = 0`, `b = 1`
this is `Work.Whitney.IsArcChain`. -/
def IsArcChainOn (γ : ℝ → M) (a b : ℝ)
    (c d : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n))) : Prop :=
  ∃ (N : ℕ) (_ : 0 < N)
    (dd : Fin (N + 1) → OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n))) (t : Fin (N + 1) → ℝ),
    ChainData γ a b c d N dd t

/-- `IsArcChain` is the special case `a = 0`, `b = 1` of `IsArcChainOn`. -/
theorem isArcChain_iff_isArcChainOn (γ : ℝ → M)
    (c d : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n))) :
    IsArcChain γ c d ↔ IsArcChainOn γ 0 1 c d := Iff.rfl

/-- **Tail of a chain.**  Dropping the first chart of a chain of length `k + 1` gives a chain of
length `k` starting at the second chart, on the parameter interval `[t 1, b]`. -/
theorem chainData_tail {k : ℕ} {γ : ℝ → M} {a b : ℝ}
    {c d : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n))}
    {dd : Fin (k + 1 + 1) → OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n))}
    {t : Fin (k + 1 + 1) → ℝ}
    (h : ChainData γ a b c d (k + 1) dd t) :
    ChainData γ (t (Fin.succ 0)) b (dd (Fin.succ 0)) d k
      (fun j : Fin (k + 1) => dd (Fin.succ j)) (fun j : Fin (k + 1) => t (Fin.succ j)) := by
  obtain ⟨ht0, htb, htmono, hdd0, hddN, hγa, hγb, hsm, hcov, hjunc⟩ := h
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [Fin.succ_zero_eq_one]
  · simpa only [Fin.succ_last] using htb
  · intro i j hij
    exact htmono (Fin.succ_le_succ_iff.mpr hij)
  · rfl
  · simpa only [Fin.succ_last] using hddN
  · simpa [Fin.succ_zero_eq_one] using (hjunc (0 : Fin (k+1))).1
  · exact hγb
  · intro i; exact hsm _
  · intro i
    simpa only [Fin.succ_castSucc] using hcov (Fin.succ i)
  · intro i
    simpa only [Fin.succ_castSucc] using hjunc (Fin.succ i)

/-- **Restricting the start of a chain.**  If `a ≤ u ≤ t 1`, then replacing the first junction
parameter `a` by `u` gives again a chain, now starting at `γ u`; the charts are unchanged. -/
theorem chainData_restrictStart {k : ℕ} {γ : ℝ → M} {a b u : ℝ}
    {c' d' : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n))}
    {ff : Fin (k + 1 + 1) → OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n))}
    {s : Fin (k + 1 + 1) → ℝ}
    (h : ChainData γ a b c' d' (k + 1) ff s) (hau : a ≤ u) (hle : u ≤ s (Fin.succ 0)) :
    ChainData γ u b c' d' (k + 1) ff (Function.update s 0 u) := by
  obtain ⟨hs0, hsb, hsmono, hff0, hffM, hγa, hγb, hsm, hcov, hjunc⟩ := h
  have hlast_ne : (Fin.last (k+1) : Fin (k+1+1)) ≠ 0 := by
    intro hc
    have h := congrArg Fin.val hc
    simp [Fin.val_last] at h
  have h0u : (Function.update s 0 u) (0 : Fin (k+1+1)) = u := Function.update_self 0 u s
  have hsucc : (Function.update s 0 u) (Fin.succ 0) = s (Fin.succ 0) :=
    Function.update_of_ne (Fin.succ_ne_zero 0) u s
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [h0u]
  · rw [Function.update_of_ne hlast_ne, hsb]
  · intro i j hij
    by_cases hi : i = 0
    · subst hi
      rw [h0u]
      by_cases hj : j = 0
      · subst hj; rw [h0u]
      · rw [Function.update_of_ne hj]
        obtain ⟨l, hl⟩ := (Fin.eq_zero_or_eq_succ j).resolve_left hj
        subst hl
        exact le_trans hle (hsmono (Fin.succ_le_succ_iff.mpr (Fin.zero_le l)))
    · rw [Function.update_of_ne hi]
      by_cases hj : j = 0
      · subst hj
        exact absurd (le_antisymm hij (Fin.zero_le i)) hi
      · rw [Function.update_of_ne hj]
        exact hsmono hij
  · exact hff0
  · exact hffM
  · have hmem : u ∈ Set.Icc (s (Fin.castSucc 0)) (s (Fin.succ 0)) :=
      ⟨by simpa [Fin.castSucc_zero, hs0] using hau, hle⟩
    have := (hcov (0 : Fin (k+1))) ⟨u, hmem, rfl⟩
    simpa [Fin.castSucc_zero, hff0] using this
  · exact hγb
  · intro i; exact hsm i
  · intro i
    by_cases hi : i = 0
    · subst hi
      rw [show (Fin.castSucc (0 : Fin (k+1)) : Fin (k+1+1)) = 0 from Fin.castSucc_zero,
        h0u, hsucc]
      refine subset_trans (Set.image_mono ?_) (hcov (0 : Fin (k+1)))
      intro x hx
      exact ⟨le_trans (by simpa [Fin.castSucc_zero, hs0] using hau) hx.1, hx.2⟩
    · have hci : i.castSucc ≠ (0 : Fin (k+1+1)) :=
        fun hc => hi (Fin.castSucc_injective _ (hc.trans Fin.castSucc_zero.symm))
      have hsi : i.succ ≠ (0 : Fin (k+1+1)) := Fin.succ_ne_zero i
      rw [Function.update_of_ne hci, Function.update_of_ne hsi]
      exact hcov i
  · intro i
    by_cases hi : i = 0
    · subst hi
      rw [hsucc]
      exact hjunc (0 : Fin (k+1))
    · have hsi : i.succ ≠ (0 : Fin (k+1+1)) := Fin.succ_ne_zero i
      rw [Function.update_of_ne hsi]
      exact hjunc i

end Work.Whitney
