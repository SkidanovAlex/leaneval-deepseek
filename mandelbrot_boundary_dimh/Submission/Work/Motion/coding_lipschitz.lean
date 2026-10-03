import Mathlib
import Submission.Work.Motion.Basic
import Submission.Work.Motion.Coding
import Submission.Work.Motion.coding_piece_dist
import Submission.Work.Motion.tail_limit

namespace Work.Motion

open Metric Set Filter
open MandelDim
open LeanEval.Dynamics.MandelbrotBoundary

noncomputable section

variable {c₀ : ℂ} {N : ℕ} {τ : Fin N → ℂ → ℂ} {n : Fin N → ℕ} {p : ℂ} {r K : ℝ}

namespace PertData

variable (D : PertData c₀ N τ n p r K)
include D

/-- Any composite of `k` branches maps the core `closedBall p (r/2)` into itself (for `k = 0` it is
the identity, and for `k ≥ 1` the image lands in the smaller ball `closedBall p s`). -/
lemma pComp_mem_core (c : ℂ) (hc : c ∈ ball c₀ D.ρ) (ω : ℕ → Fin N) (k : ℕ) :
    ∀ x ∈ closedBall p (r / 2), pComp (D.τc c) ω k x ∈ closedBall p (r / 2) := by
  intro x hx
  rcases Nat.eq_zero_or_pos k with hk | hk
  · subst hk
    simpa using hx
  · have h := pComp_mem D c hc ω (k - 1) x hx
    have hk' : k - 1 + 1 = k := by omega
    rw [hk'] at h
    exact closedBall_s_subset D h

/-- Arithmetic identity behind the contraction constant `Lc / (1 - θ)` for the parameter
dependence: `Lc + θ · (Lc / (1 - θ)) = Lc / (1 - θ)`. -/
lemma add_mul_div_self (hθ : D.θ < 1) :
    D.Lc + D.θ * (D.Lc / (1 - D.θ)) = D.Lc / (1 - D.θ) := by
  have hden : (1 : ℝ) - D.θ ≠ 0 := by linarith
  field_simp
  ring

/-- **The `k`-fold composite depends Lipschitz-continuously on the parameter**, with the
`θ`-independent constant `Lc / (1 - θ)`: each level pays `Lc ‖c - c'‖` for the branch and the
previously built error is contracted by `θ`. -/
lemma pComp_lips_c (ω : ℕ → Fin N) :
    ∀ k, ∀ c ∈ ball c₀ D.ρ, ∀ c' ∈ ball c₀ D.ρ,
      ‖pComp (D.τc c) ω k p - pComp (D.τc c') ω k p‖ ≤ (D.Lc / (1 - D.θ)) * ‖c - c'‖ := by
  intro k
  induction k generalizing ω with
  | zero =>
    intro c hc c' hc'
    simp only [pComp_zero, id_eq, sub_self, norm_zero]
    exact mul_nonneg (div_nonneg D.hLc (by linarith [D.hθ1])) (norm_nonneg _)
  | succ k ih =>
    intro c hc c' hc'
    have hz : pComp (D.τc c) (fun j => ω (j + 1)) k p ∈ closedBall p (r / 2) :=
      pComp_mem_core D c hc _ k p (half_mem D c)
    have hz' : pComp (D.τc c') (fun j => ω (j + 1)) k p ∈ closedBall p (r / 2) :=
      pComp_mem_core D c' hc' _ k p (half_mem D c')
    simp only [pComp_succ, Function.comp_apply]
    have h1 : ‖D.τc c (ω 0) (pComp (D.τc c) (fun j => ω (j + 1)) k p)
        - D.τc c' (ω 0) (pComp (D.τc c) (fun j => ω (j + 1)) k p)‖
        ≤ D.Lc * ‖c - c'‖ :=
      D.lips_c (ω 0) _ hz c hc c' hc'
    have h2 : ‖D.τc c' (ω 0) (pComp (D.τc c) (fun j => ω (j + 1)) k p)
        - D.τc c' (ω 0) (pComp (D.τc c') (fun j => ω (j + 1)) k p)‖
        ≤ D.θ * ((D.Lc / (1 - D.θ)) * ‖c - c'‖) := by
      refine le_trans (D.lips_z (ω 0) hc' _ hz' _ hz) ?_
      exact mul_le_mul_of_nonneg_left (ih (fun j => ω (j + 1)) c hc c' hc') D.hθ0
    have htri : ‖D.τc c (ω 0) (pComp (D.τc c) (fun j => ω (j + 1)) k p)
        - D.τc c' (ω 0) (pComp (D.τc c') (fun j => ω (j + 1)) k p)‖
        ≤ D.Lc * ‖c - c'‖ + D.θ * ((D.Lc / (1 - D.θ)) * ‖c - c'‖) := by
      have hsplit : D.τc c (ω 0) (pComp (D.τc c) (fun j => ω (j + 1)) k p)
            - D.τc c' (ω 0) (pComp (D.τc c') (fun j => ω (j + 1)) k p)
          = (D.τc c (ω 0) (pComp (D.τc c) (fun j => ω (j + 1)) k p)
              - D.τc c' (ω 0) (pComp (D.τc c) (fun j => ω (j + 1)) k p))
            + (D.τc c' (ω 0) (pComp (D.τc c) (fun j => ω (j + 1)) k p)
              - D.τc c' (ω 0) (pComp (D.τc c') (fun j => ω (j + 1)) k p)) := by ring
      rw [hsplit]
      exact le_trans (norm_add_le _ _) (add_le_add h1 h2)
    refine le_trans htri ?_
    have harith : D.Lc * ‖c - c'‖ + D.θ * ((D.Lc / (1 - D.θ)) * ‖c - c'‖)
        = (D.Lc / (1 - D.θ)) * ‖c - c'‖ := by
      calc D.Lc * ‖c - c'‖ + D.θ * ((D.Lc / (1 - D.θ)) * ‖c - c'‖)
          = (D.Lc + D.θ * (D.Lc / (1 - D.θ))) * ‖c - c'‖ := by ring
        _ = (D.Lc / (1 - D.θ)) * ‖c - c'‖ := by rw [add_mul_div_self D D.hθ1]
    exact le_of_eq harith

end PertData

/-- **Lipschitz dependence of the coding map on the parameter.** For `c, c'` in the parameter disc
of a `PertData`, the coding points of a common code differ by at most `(Lc / (1 - θ)) ‖c - c'‖`:
the level-`k` pieces of the two IFS have diameter `2 s θ^(k-1)`, the level-`k` composites at `p`
differ by at most `(Lc / (1 - θ)) ‖c - c'‖` (each of the `k` branches costs `Lc`, the previous
error being contracted by `θ`), and `k → ∞` kills the first contribution. -/
theorem coding_lipschitz {c₀ : ℂ} {N : ℕ} {τ : Fin N → ℂ → ℂ} {n : Fin N → ℕ} {p : ℂ} {r K : ℝ}
    (D : PertData c₀ N τ n p r K) :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ c ∈ ball c₀ D.ρ, ∀ c' ∈ ball c₀ D.ρ, ∀ ω : ℕ → Fin N,
      ‖D.coding c ω - D.coding c' ω‖ ≤ L * ‖c - c'‖ := by
  refine ⟨D.Lc / (1 - D.θ), div_nonneg D.hLc (by linarith [D.hθ1]), ?_⟩
  intro c hc c' hc' ω
  have hbound : ∀ k : ℕ, 1 ≤ k →
      ‖D.coding c ω - D.coding c' ω‖
        ≤ (D.Lc / (1 - D.θ)) * ‖c - c'‖ + 4 * D.s * D.θ ^ (k - 1) := by
    intro k hk
    obtain ⟨m, hm⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
    subst hm
    show ‖D.coding c ω - D.coding c' ω‖
        ≤ (D.Lc / (1 - D.θ)) * ‖c - c'‖ + 4 * D.s * D.θ ^ m
    have ha : ‖D.coding c ω - pComp (D.τc c) ω (m + 1) p‖ ≤ 2 * D.s * D.θ ^ m :=
      coding_piece_dist D c hc ω (k := m + 1) (by omega)
    have hb : ‖D.coding c' ω - pComp (D.τc c') ω (m + 1) p‖ ≤ 2 * D.s * D.θ ^ m :=
      coding_piece_dist D c' hc' ω (k := m + 1) (by omega)
    have hcc := D.pComp_lips_c ω (m + 1) c hc c' hc'
    have htri : ‖D.coding c ω - D.coding c' ω‖
        ≤ ‖D.coding c ω - pComp (D.τc c) ω (m + 1) p‖
          + ‖pComp (D.τc c) ω (m + 1) p - pComp (D.τc c') ω (m + 1) p‖
          + ‖pComp (D.τc c') ω (m + 1) p - D.coding c' ω‖ := by
      have hsplit : D.coding c ω - D.coding c' ω
          = (D.coding c ω - pComp (D.τc c) ω (m + 1) p)
            + ((pComp (D.τc c) ω (m + 1) p - pComp (D.τc c') ω (m + 1) p)
            + (pComp (D.τc c') ω (m + 1) p - D.coding c' ω)) := by ring
      rw [hsplit]
      calc ‖(D.coding c ω - pComp (D.τc c) ω (m + 1) p)
              + ((pComp (D.τc c) ω (m + 1) p - pComp (D.τc c') ω (m + 1) p)
              + (pComp (D.τc c') ω (m + 1) p - D.coding c' ω))‖
            ≤ ‖D.coding c ω - pComp (D.τc c) ω (m + 1) p‖
              + ‖(pComp (D.τc c) ω (m + 1) p - pComp (D.τc c') ω (m + 1) p)
              + (pComp (D.τc c') ω (m + 1) p - D.coding c' ω)‖ := norm_add_le _ _
        _ ≤ ‖D.coding c ω - pComp (D.τc c) ω (m + 1) p‖
              + (‖pComp (D.τc c) ω (m + 1) p - pComp (D.τc c') ω (m + 1) p‖
              + ‖pComp (D.τc c') ω (m + 1) p - D.coding c' ω‖) :=
            add_le_add le_rfl (norm_add_le _ _)
        _ = ‖D.coding c ω - pComp (D.τc c) ω (m + 1) p‖
              + ‖pComp (D.τc c) ω (m + 1) p - pComp (D.τc c') ω (m + 1) p‖
              + ‖pComp (D.τc c') ω (m + 1) p - D.coding c' ω‖ := by ring
    have hsym : ‖pComp (D.τc c') ω (m + 1) p - D.coding c' ω‖
        = ‖D.coding c' ω - pComp (D.τc c') ω (m + 1) p‖ := norm_sub_rev _ _
    rw [hsym] at htri
    have hkey : ‖D.coding c ω - D.coding c' ω‖
        ≤ (D.Lc / (1 - D.θ)) * ‖c - c'‖ + (2 * D.s * D.θ ^ m + 2 * D.s * D.θ ^ m) := by
      linarith [htri, ha, hb, hcc]
    calc ‖D.coding c ω - D.coding c' ω‖
        ≤ (D.Lc / (1 - D.θ)) * ‖c - c'‖ + (2 * D.s * D.θ ^ m + 2 * D.s * D.θ ^ m) := hkey
      _ = (D.Lc / (1 - D.θ)) * ‖c - c'‖ + 4 * D.s * D.θ ^ m := by ring
  exact tail_limit (C := 4 * D.s) (t := D.θ) D.hθ0 D.hθ1 (by linarith [D.hs0]) hbound

end

end Work.Motion
