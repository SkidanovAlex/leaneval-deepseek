import Mathlib
import Submission.Work.Motion.Basic
import Submission.Work.Motion.Coding
import Submission.Work.Motion.coding_lipschitz

namespace Work.Motion

open Metric Set Filter
open MandelDim
open LeanEval.Dynamics.MandelbrotBoundary

noncomputable section

variable {c₀ : ℂ} {N : ℕ} {τ : Fin N → ℂ → ℂ} {n : Fin N → ℕ} {p : ℂ} {r K : ℝ}

/-! Auxiliary lemmas for `Work.Motion.deriv_ratio_and_lips`: differentiability of the finite
composites at the base point `p`, the chain rule there, and the elementary real-arithmetic step
turning a one-letter comparison of derivative moduli into an exponential bound. -/

namespace DRL

variable (D : PertData c₀ N τ n p r K)
include D

/-- `0 < r₁`. -/
lemma r₁_pos : 0 < D.r₁ := by linarith [D.r_pos, D.hr₁]

/-- Every finite composite of the perturbed branches, evaluated at `p`, stays in the core. -/
lemma pComp_p_mem_core (c : ℂ) (hc : c ∈ ball c₀ D.ρ) (ω : ℕ → Fin N) (k : ℕ) :
    pComp (D.τc c) ω k p ∈ closedBall p (r / 2) := by
  rcases Nat.eq_zero_or_pos k with hk | hk
  · subst hk
    rw [pComp_zero]
    exact D.half_mem p
  · obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
    exact D.closedBall_s_subset (D.pComp_mem c hc ω m p (D.half_mem p))

/-- Every finite composite of the perturbed branches, evaluated at `p`, stays in `ball p r₁`,
where the branches are holomorphic. -/
lemma pComp_p_mem_ball (c : ℂ) (hc : c ∈ ball c₀ D.ρ) (ω : ℕ → Fin N) (k : ℕ) :
    pComp (D.τc c) ω k p ∈ ball p D.r₁ := by
  rcases Nat.eq_zero_or_pos k with hk | hk
  · subst hk
    rw [pComp_zero, mem_ball]
    simpa using r₁_pos D
  · obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
    exact D.closedBall_s_subset' (D.pComp_mem c hc ω m p (D.half_mem p))

/-- Every finite composite of the perturbed branches is holomorphic at `p`. -/
lemma differentiableAt_pComp (c : ℂ) (hc : c ∈ ball c₀ D.ρ) (ω : ℕ → Fin N) (k : ℕ) :
    DifferentiableAt ℂ (pComp (D.τc c) ω k) p := by
  induction k generalizing ω with
  | zero => rw [pComp_zero]; exact differentiableAt_id
  | succ k ih =>
    rw [pComp_succ]
    exact DifferentiableAt.comp (x := p)
      ((D.diffOn_z (ω 0) hc).differentiableAt
        (IsOpen.mem_nhds isOpen_ball (pComp_p_mem_ball D c hc (fun j => ω (j + 1)) k)))
      (ih (fun j => ω (j + 1)))

/-- Chain rule for `pComp` at the base point `p`: the derivative of the `(k+1)`-fold composite
splits off the first letter. -/
lemma deriv_pComp_succ_p (c : ℂ) (hc : c ∈ ball c₀ D.ρ) (ω : ℕ → Fin N) (k : ℕ) :
    deriv (pComp (D.τc c) ω (k + 1)) p =
      deriv (D.τc c (ω 0)) (pComp (D.τc c) (fun j => ω (j + 1)) k p) *
        deriv (pComp (D.τc c) (fun j => ω (j + 1)) k) p := by
  rw [pComp_succ]
  refine deriv_comp (x := p) (h := pComp (D.τc c) (fun j => ω (j + 1)) k)
    (h₂ := D.τc c (ω 0)) ?_ (differentiableAt_pComp D c hc (fun j => ω (j + 1)) k)
  exact (D.diffOn_z (ω 0) hc).differentiableAt
    (IsOpen.mem_nhds isOpen_ball (pComp_p_mem_ball D c hc (fun j => ω (j + 1)) k))

omit D in
/-- Elementary real step: if `β ≤ b` and `a ≤ b + G(1+Λ)δ` with all constants nonnegative, then
`a ≤ exp(G(1+Λ)/β · δ) · b`.  This is `1 + x ≤ exp x` after removing `β` from the last term. -/
lemma exp_ratio_step {β G Λ δ a b : ℝ} (hβ : 0 < β) (hG : 0 ≤ G) (hΛ : 0 ≤ Λ) (hδ : 0 ≤ δ)
    (hb : β ≤ b) (ha : a ≤ b + G * (1 + Λ) * δ) :
    a ≤ Real.exp (G * (1 + Λ) / β * δ) * b := by
  have hM : 0 ≤ G * (1 + Λ) / β := div_nonneg (mul_nonneg hG (by linarith)) (le_of_lt hβ)
  have hb0 : 0 ≤ b := le_trans (le_of_lt hβ) hb
  have hkey : G * (1 + Λ) * δ ≤ G * (1 + Λ) / β * δ * b := by
    have h1 : G * (1 + Λ) * δ = G * (1 + Λ) / β * δ * β := by field_simp
    rw [h1]
    exact mul_le_mul_of_nonneg_left hb (mul_nonneg hM hδ)
  have hexp : 1 + G * (1 + Λ) / β * δ ≤ Real.exp (G * (1 + Λ) / β * δ) := by
    have := Real.add_one_le_exp (G * (1 + Λ) / β * δ)
    linarith
  have h2 : (1 + G * (1 + Λ) / β * δ) * b ≤ Real.exp (G * (1 + Λ) / β * δ) * b :=
    mul_le_mul_of_nonneg_right hexp hb0
  have h3 : b + G * (1 + Λ) * δ ≤ (1 + G * (1 + Λ) / β * δ) * b := by
    have heq : (1 + G * (1 + Λ) / β * δ) * b = b + G * (1 + Λ) / β * δ * b := by ring
    rw [heq]
    linarith
  linarith

/-- **Single-letter factor comparison.**  The modulus of the derivative of the branch `τc c i` at
`u` is at most `exp(G(1+Lc/(1-θ))/β · ‖c-c'‖)` times that of the branch `τc c' i` at `u'`, provided
the two points are within `(Lc/(1-θ))·‖c-c'‖` of each other (the shadowing bound). -/
lemma deriv_factor_step {c c' : ℂ} (hc : c ∈ ball c₀ D.ρ) (hc' : c' ∈ ball c₀ D.ρ)
    (i : Fin N) {u u' : ℂ} (hu : u ∈ closedBall p (r / 2)) (hu' : u' ∈ closedBall p (r / 2))
    (h : ‖u - u'‖ ≤ (D.Lc / (1 - D.θ)) * ‖c - c'‖) :
    ‖deriv (D.τc c i) u‖ ≤
      Real.exp (D.G * (1 + D.Lc / (1 - D.θ)) / D.β * ‖c - c'‖) *
        ‖deriv (D.τc c' i) u'‖ := by
  set Λ : ℝ := D.Lc / (1 - D.θ) with hΛ
  have hΛ0 : 0 ≤ Λ := by rw [hΛ]; exact div_nonneg D.hLc (by linarith [D.hθ1])
  have hδ : 0 ≤ ‖c - c'‖ := norm_nonneg _
  have hb : D.β ≤ ‖deriv (D.τc c' i) u'‖ := D.deriv_ge c' hc' i u' hu'
  have htri : ‖deriv (D.τc c i) u‖ ≤
      ‖deriv (D.τc c' i) u'‖ + ‖deriv (D.τc c i) u - deriv (D.τc c' i) u'‖ := by
    have h2 := norm_add_le (deriv (D.τc c i) u - deriv (D.τc c' i) u') (deriv (D.τc c' i) u')
    rwa [sub_add_cancel, add_comm] at h2
  have hAB : ‖deriv (D.τc c i) u - deriv (D.τc c' i) u'‖ ≤
      D.G * (‖c - c'‖ + ‖u - u'‖) := D.deriv_lips i u hu u' hu' c hc c' hc'
  have hsum : ‖c - c'‖ + ‖u - u'‖ ≤ (1 + Λ) * ‖c - c'‖ := by
    rw [add_mul, one_mul]
    linarith [h]
  have hGsum : D.G * (‖c - c'‖ + ‖u - u'‖) ≤ D.G * (1 + Λ) * ‖c - c'‖ := by
    have h2 := mul_le_mul_of_nonneg_left hsum D.hG
    rwa [← mul_assoc] at h2
  have ha : ‖deriv (D.τc c i) u‖ ≤ ‖deriv (D.τc c' i) u'‖ + D.G * (1 + Λ) * ‖c - c'‖ := by
    linarith
  exact exp_ratio_step D.hβ D.hG hΛ0 hδ hb ha

end DRL

/-- **Uniform Lipschitz dependence on `c` of the finite composite `pComp`, and the two-sided
comparison of its derivative at `p`.**  The second component is the key estimate for the Hölder
bound: `‖(pComp (τc c) ω k)' p‖ ≤ exp(k·L·‖c-c'‖)·‖(pComp (τc c') ω k)' p‖`. -/
theorem deriv_ratio_and_lips {c₀ : ℂ} {N : ℕ} {τ : Fin N → ℂ → ℂ} {n : Fin N → ℕ} {p : ℂ} {r K : ℝ}
    (D : PertData c₀ N τ n p r K) :
    ∃ (L Λ : ℝ), 0 ≤ L ∧ 0 ≤ Λ ∧
      (∀ (k : ℕ) (ω : ℕ → Fin N) (c : ℂ), c ∈ ball c₀ D.ρ → ∀ c' ∈ ball c₀ D.ρ,
        ‖pComp (D.τc c) ω k p - pComp (D.τc c') ω k p‖ ≤ Λ * ‖c - c'‖) ∧
      (∀ (k : ℕ) (ω : ℕ → Fin N) (c : ℂ), c ∈ ball c₀ D.ρ → ∀ c' ∈ ball c₀ D.ρ,
        ‖deriv (pComp (D.τc c) ω k) p‖ ≤
          Real.exp ((k : ℝ) * L * ‖c - c'‖) * ‖deriv (pComp (D.τc c') ω k) p‖) := by
  set Λ : ℝ := D.Lc / (1 - D.θ) with hΛ
  set L : ℝ := D.G * (1 + Λ) / D.β with hL
  have hΛ0 : 0 ≤ Λ := by rw [hΛ]; exact div_nonneg D.hLc (by linarith [D.hθ1])
  have hL0 : 0 ≤ L := by
    rw [hL]
    exact div_nonneg (mul_nonneg D.hG (by linarith)) (le_of_lt D.hβ)
  refine ⟨L, Λ, hL0, hΛ0, ?_, ?_⟩
  · intro k ω c hc c' hc'
    exact D.pComp_lips_c ω k c hc c' hc'
  · have key : ∀ (ω : ℕ → Fin N) (k : ℕ) (c : ℂ), c ∈ ball c₀ D.ρ → ∀ c' ∈ ball c₀ D.ρ,
        ‖deriv (pComp (D.τc c) ω k) p‖ ≤ Real.exp ((k : ℝ) * L * ‖c - c'‖) *
          ‖deriv (pComp (D.τc c') ω k) p‖ := by
      intro ω k
      induction k generalizing ω with
      | zero =>
        intro c hc c' hc'
        simp [pComp_zero, deriv_id]
      | succ j ih =>
        intro c hc c' hc'
        have hu : pComp (D.τc c) (fun l => ω (l + 1)) j p ∈ closedBall p (r / 2) :=
          DRL.pComp_p_mem_core D c hc (fun l => ω (l + 1)) j
        have hu' : pComp (D.τc c') (fun l => ω (l + 1)) j p ∈ closedBall p (r / 2) :=
          DRL.pComp_p_mem_core D c' hc' (fun l => ω (l + 1)) j
        have hsh : ‖pComp (D.τc c) (fun l => ω (l + 1)) j p
            - pComp (D.τc c') (fun l => ω (l + 1)) j p‖ ≤ Λ * ‖c - c'‖ :=
          D.pComp_lips_c (fun l => ω (l + 1)) j c hc c' hc'
        rw [DRL.deriv_pComp_succ_p D c hc ω j, DRL.deriv_pComp_succ_p D c' hc' ω j]
        set A := deriv (D.τc c (ω 0)) (pComp (D.τc c) (fun l => ω (l + 1)) j p) with hA
        set B := deriv (pComp (D.τc c) (fun l => ω (l + 1)) j) p with hB
        set A' := deriv (D.τc c' (ω 0)) (pComp (D.τc c') (fun l => ω (l + 1)) j p) with hA'
        set B' := deriv (pComp (D.τc c') (fun l => ω (l + 1)) j) p with hB'
        rw [norm_mul, norm_mul]
        have hfac : ‖A‖ ≤ Real.exp (L * ‖c - c'‖) * ‖A'‖ :=
          DRL.deriv_factor_step D hc hc' (ω 0) hu hu' hsh
        have hih : ‖B‖ ≤ Real.exp ((j : ℝ) * L * ‖c - c'‖) * ‖B'‖ :=
          ih (fun l => ω (l + 1)) c hc c' hc'
        have h1 : ‖A‖ * ‖B‖ ≤ (Real.exp (L * ‖c - c'‖) * ‖A'‖) *
            (Real.exp ((j : ℝ) * L * ‖c - c'‖) * ‖B'‖) :=
          mul_le_mul hfac hih (norm_nonneg _) (by positivity)
        have h2 : (Real.exp (L * ‖c - c'‖) * ‖A'‖) *
            (Real.exp ((j : ℝ) * L * ‖c - c'‖) * ‖B'‖)
            = Real.exp (((Nat.succ j : ℕ) : ℝ) * L * ‖c - c'‖) * (‖A'‖ * ‖B'‖) := by
          have hexp : Real.exp (L * ‖c - c'‖) * Real.exp ((j : ℝ) * L * ‖c - c'‖)
              = Real.exp (((Nat.succ j : ℕ) : ℝ) * L * ‖c - c'‖) := by
            rw [← Real.exp_add]
            congr 1
            rw [Nat.cast_succ]
            ring
          rw [mul_mul_mul_comm, hexp]
        exact le_trans h1 (le_of_eq h2)
    intro k ω c hc c' hc'
    exact key ω k c hc c' hc'

end

end Work.Motion
