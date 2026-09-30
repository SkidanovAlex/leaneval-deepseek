import Mathlib
import Submission.Work.N8.step6v2_defs
import Submission.Work.N8.step6_defs
import Submission.Work.N8.closed_walk_lower_v2
import Submission.Work.BMF.Defs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.N8

open Finset

/-- Arithmetic core of the Step-6 walk lower bound: under the size hypotheses on `T` and the
edge lower bound, the average internal degree `E/n` dominates `(c_E/c₂)·(P/log P)²`. -/
theorem walk_arith_lower (c_E c₂ P N E n : ℝ) (m : ℕ)
    (hcE : 0 < c_E) (hc2 : 0 < c₂) (hP : 1 ≤ P) (hN : 0 < N)
    (hTlow : c_E * N ≤ n) (hThigh : n ≤ c₂ * N)
    (hedges : c_E * (P / Real.log P) ^ 2 * N ≤ E) :
    ((c_E / c₂) * (P / Real.log P) ^ 2) ^ (2 * m) ≤ (E / n) ^ (2 * m) := by
  have hnpos : 0 < n := lt_of_lt_of_le (mul_pos hcE hN) hTlow
  have hBnn : 0 ≤ (c_E / c₂) * (P / Real.log P) ^ 2 := by positivity
  have hBn : (c_E / c₂) * (P / Real.log P) ^ 2 * n ≤ E := by
    have h1 : (c_E / c₂) * (P / Real.log P) ^ 2 * n
        ≤ (c_E / c₂) * (P / Real.log P) ^ 2 * (c₂ * N) :=
      mul_le_mul_of_nonneg_left hThigh hBnn
    have h2 : (c_E / c₂) * (P / Real.log P) ^ 2 * (c₂ * N)
        = c_E * (P / Real.log P) ^ 2 * N := by
      have hc := div_mul_cancel₀ c_E (ne_of_gt hc2)
      calc (c_E / c₂) * (P / Real.log P) ^ 2 * (c₂ * N)
          = ((c_E / c₂) * c₂) * ((P / Real.log P) ^ 2 * N) := by ring
        _ = c_E * ((P / Real.log P) ^ 2 * N) := by rw [hc]
        _ = c_E * (P / Real.log P) ^ 2 * N := by ring
    rw [h2] at h1
    linarith [h1, hedges]
  have hbase : (c_E / c₂) * (P / Real.log P) ^ 2 ≤ E / n := (le_div_iff₀ hnpos).mpr hBn
  exact pow_le_pow_left₀ hBnn hbase (2 * m)

/-- **Lower bound for the number of closed walks in an induced subgraph.**

For a symmetric graph on `V` and a finite vertex set `T`, the number of closed walks of even
length `2m` staying in `T` dominates the `(2m)`-th power of the average degree of the induced
graph, i.e. of `(number of ordered adjacent pairs inside T) / |T|`.  This is
`closed_walk_lower_v2` applied to the induced subgraph on `T`. -/
theorem closed_walk_lower_subgraph {V : Type} [Fintype V] [DecidableEq V]
    (Adj : V → V → Prop) [DecidableRel Adj] (hsym : ∀ a b, Adj a b ↔ Adj b a)
    (T : Finset V) (m : ℕ) (hm : 1 ≤ m) :
    (((Finset.univ.filter (fun p : V × V ↦ p.1 ∈ T ∧ p.2 ∈ T ∧ Adj p.1 p.2)).card : ℝ)
        / (T.card : ℝ)) ^ (2 * m)
      ≤ ((step6Walks Adj T (2 * m)).card : ℝ) := by
  classical
  have hcard : Fintype.card ↥T = T.card := Fintype.card_coe T
  have hE : (Finset.univ.filter (fun p : ↥T × ↥T => Adj p.1 p.2)).card
      = (Finset.univ.filter (fun p : V × V => p.1 ∈ T ∧ p.2 ∈ T ∧ Adj p.1 p.2)).card := by
    apply Finset.card_bij (fun p _ => ((p.1 : V), (p.2 : V)))
    · intro p hp
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp ⊢
      exact ⟨p.1.2, p.2.2, hp⟩
    · intro p₁ _ p₂ _ heq
      simp only [Prod.mk.injEq] at heq
      exact Prod.ext (Subtype.ext heq.1) (Subtype.ext heq.2)
    · intro q hq
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hq
      refine ⟨(⟨q.1, hq.1⟩, ⟨q.2, hq.2.1⟩), ?_, ?_⟩
      · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        exact hq.2.2
      · rfl
  have hW : (Finset.univ.filter (fun v : Fin (2 * m) → ↥T =>
        ∀ j : Fin (2 * m),
          Adj (v j) (v ⟨((j : ℕ) + 1) % (2 * m), Nat.mod_lt _ (by omega)⟩))).card
      = (step6Walks Adj T (2 * m)).card := by
    apply Finset.card_bij (fun v _ => fun j => (v j : V))
    · intro v hv
      rw [mem_step6Walks]
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hv
      refine ⟨fun j => (v j).2, fun j => ?_⟩
      have hidx : (⟨((j : ℕ) + 1) % (2 * m), Nat.mod_lt _ (by omega)⟩ : Fin (2 * m))
          = step6next (2 * m) j := Fin.ext rfl
      have h := hv j
      rw [hidx] at h
      simpa using h
    · intro v₁ _ v₂ _ heq
      funext j
      exact Subtype.ext (congrFun heq j)
    · intro w hw
      rw [mem_step6Walks] at hw
      refine ⟨(fun j => (⟨w j, hw.1 j⟩ : ↥T)), ?_, ?_⟩
      · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        intro j
        have hidx : (⟨((j : ℕ) + 1) % (2 * m), Nat.mod_lt _ (by omega)⟩ : Fin (2 * m))
            = step6next (2 * m) j := Fin.ext rfl
        rw [hidx]
        simpa using hw.2 j
      · funext j
        rfl
  have hcl := closed_walk_lower_v2 (V := ↥T) (fun a b : ↥T => Adj (a : V) (b : V))
    (fun a b => hsym (a : V) (b : V)) m hm
  rw [hcard, hE, hW] at hcl
  exact hcl

theorem step6v2_walk_lower {V : Type} [Fintype V] [DecidableEq V]
    (Adj : V → V → Prop) [DecidableRel Adj] (hsym : ∀ a b, Adj a b ↔ Adj b a)
    (T : Finset V) (ℓ : ℕ) (hℓ2 : 2 ≤ ℓ) (hℓeven : ∃ m : ℕ, ℓ = 2 * m)
    (c_E c₂ P N : ℝ) (hcE : 0 < c_E) (hc2 : 0 < c₂) (hP : 1 ≤ P) (hN : 0 < N)
    (hTlow : c_E * N ≤ (T.card : ℝ)) (hThigh : (T.card : ℝ) ≤ c₂ * N)
    (hedges : c_E * (P / Real.log P) ^ 2 * N ≤
      ((Finset.univ.filter (fun p : V × V ↦ p.1 ∈ T ∧ p.2 ∈ T ∧ Adj p.1 p.2)).card : ℝ)) :
    ((c_E / c₂) * (P / Real.log P) ^ 2) ^ ℓ ≤ ((Work.N8.step6Walks Adj T ℓ).card : ℝ) := by
  obtain ⟨m, hm_eq⟩ := hℓeven
  rw [hm_eq] at hℓ2 ⊢
  have hm : 1 ≤ m := by omega
  exact le_trans
    (walk_arith_lower c_E c₂ P N
      ((Finset.univ.filter (fun p : V × V => p.1 ∈ T ∧ p.2 ∈ T ∧ Adj p.1 p.2)).card : ℝ)
      (T.card : ℝ) m hcE hc2 hP hN hTlow hThigh hedges)
    (closed_walk_lower_subgraph Adj hsym T m hm)

end Work.N8
