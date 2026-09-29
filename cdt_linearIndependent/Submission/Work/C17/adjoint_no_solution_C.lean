import Mathlib
import Submission.Work.C17.adjoint_C_defs
import Submission.Work.C17adj.adjoint_divisor_boundC
import Submission.Work.C17adj2.adjoint_clearingL
import Submission.Work.C17z.adjoint_no_solution_C

/-!
# `Work.C17.adjoint_no_solution_C`

The formal adjoint `M* = d²P₂ − dP₁ + P₀` of the order-two operator
`M = P₂∂² + P₁∂ + P₀` of Calegari--Dimitrov--Tang (arXiv:2408.15403) has no rational solution
with right hand side in the span of `y^{i−4}y'` (`y = x²/(x−1)`, `i < 6`).

## The proof, and where each ingredient comes from

Let `D = x⁶(x−1)²(x+1)²` (`= Work.C17C.DadjL`) and `M*β = Σᵢ cᵢ y^{i−4}y'`.

1. **The right hand side.** `rnC i / rdC i = y^{i−4}·y'` as rational functions
   (`Work.C17z.rnC_div_rdC`), and `P2C/P1C/P0C` are definitionally the `ℂ`-images `Pac/Pbc/Pcc`
   of the `ℚ`-coefficients (`Work.C17z.Pac_eq`, `Pbc_eq`, `Pcc_eq`).
2. **Divisor bound** (`Work.C17adj.adjoint_divisor_boundC`, proved by the local/indicial analysis
   of the adjoint operator: exponents `−N²` at `0`, `N(N+2)` at `±1`, `N²` at the roots of `Q₄`,
   `N(N−1)` at the regular points, and degree `d + 5` at `∞`).  It gives
   `β·D = NpolyL n` with a polynomial of degree `≤ 6`, i.e. `β = NpolyL n / D`.
3. **Clearing denominators** (`Work.C17adj2.adjoint_clearingL`): multiplying the equation by `D³`
   and using the quotient rule turns it into the polynomial identity
   `EpolyL a b n c = 0` (the `ℂ`-copy of the machine-generated certificate).
4. **Certificate.** `EpolyL = GpolyL` is a finite polynomial identity
   (`Work.C17z.GpolyL_eq_EpolyL`), whose `X^d`-coefficients are the explicit linear forms
   `LformL d`; the linear algebra (`Work.C17z.linear_coreL`) then reads off `n = 0`, `c = 0`
   from the non-vanishing of the order-13 minor `Pdet4L = Ψ₈·(a²−b²)²/240 ≠ 0`
   (`Work.C17adj.Psi8_ne_zero`).
5. Hence `β·D = NpolyL 0 = 0`, and `D ≠ 0` gives `β = 0`.
-/

namespace Work.C17

open Polynomial

theorem adjoint_no_solution_C (a b : ℚ) (hA : Work.C17.AdmQ a b)
    (β : RatFunc ℂ) (c : Fin 6 → ℂ)
    (h : Submission.CDT.dRat
            (Submission.CDT.dRat (algebraMap (Polynomial ℂ) (RatFunc ℂ) (Work.C17.P2C a b) * β))
          - Submission.CDT.dRat (algebraMap (Polynomial ℂ) (RatFunc ℂ) (Work.C17.P1C a b) * β)
          + algebraMap (Polynomial ℂ) (RatFunc ℂ) (Work.C17.P0C a b) * β
        = ∑ i : Fin 6, (algebraMap ℂ (RatFunc ℂ) (c i)) *
            (algebraMap (Polynomial ℂ) (RatFunc ℂ) (Work.C17.rnC i)
              / algebraMap (Polynomial ℂ) (RatFunc ℂ) (Work.C17.rdC i))) :
    β = 0 ∧ c = 0 := by
  -- ## 1. the right hand side, in the `y^{i-4} y'` form used by the divisor bound
  have hRhs : (∑ i : Fin 6, (algebraMap ℂ (RatFunc ℂ) (c i)) *
            (algebraMap (Polynomial ℂ) (RatFunc ℂ) (Work.C17.rnC i)
              / algebraMap (Polynomial ℂ) (RatFunc ℂ) (Work.C17.rdC i)))
        = ∑ i : Fin 6, algebraMap ℂ (RatFunc ℂ) (c i)
            * Work.C17.yQc ^ ((i : ℤ) - 4) * Work.C17.dyQc := by
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Work.C17z.rnC_div_rdC i, ← mul_assoc]
  -- ## 1'. the operator, in the `Pac/Pbc/Pcc` normal form
  have h' : Submission.CDT.dRat (Submission.CDT.dRat (Work.C17.Pac a b * β))
        - Submission.CDT.dRat (Work.C17.Pbc a b * β) + Work.C17.Pcc a b * β
      = ∑ i : Fin 6, algebraMap ℂ (RatFunc ℂ) (c i)
          * Work.C17.yQc ^ ((i : ℤ) - 4) * Work.C17.dyQc := by
    have h2 := h
    rw [← Work.C17z.Pac_eq a b, ← Work.C17z.Pbc_eq a b, ← Work.C17z.Pcc_eq a b, hRhs] at h2
    exact h2
  -- ## 2. the divisor bound over `ℂ`: `β·D = NpolyL n`, `deg ≤ 6`
  obtain ⟨n, hn⟩ := Work.C17adj.adjoint_divisor_boundC a b hA β c h'
  -- ## 3. `β = NpolyL n / D`
  have hDneL : (algebraMap (Polynomial ℂ) (RatFunc ℂ) (Work.C17C.DadjL)) ≠ 0 :=
    RatFunc.algebraMap_ne_zero Work.C17C.DadjL_ne_zero
  have hNpoly : algebraMap (Polynomial ℂ) (RatFunc ℂ) (Work.C17C.NpolyL n)
      = ∑ k : Fin 7, algebraMap (Polynomial ℂ) (RatFunc ℂ)
          (Polynomial.C (n k) * Polynomial.X ^ (k : ℕ)) := by
    rw [Work.C17C.NpolyL, map_sum]
  have hβ : β = algebraMap (Polynomial ℂ) (RatFunc ℂ) (Work.C17C.NpolyL n)
        / algebraMap (Polynomial ℂ) (RatFunc ℂ) (Work.C17C.DadjL) := by
    rw [eq_div_iff hDneL, hNpoly, ← hn, ← Work.C17C.DadjC_eq]
  -- ## 4. the same equation, with the operator written through `P2xL/P1xL/P0xL`
  have hh : Work.C17C.AdjOpL ((a : ℚ) : ℂ) ((b : ℚ) : ℂ) β = Work.C17C.RhsYc c := by
    rw [Work.C17C.AdjOpL, Work.C17C.RhsYc, ← Work.C17C.WorkC_P2C_eq a b,
      ← Work.C17C.WorkC_P1C_eq a b, ← Work.C17C.WorkC_P0C_eq a b]
    have h2 := h
    rw [hRhs] at h2
    exact h2
  -- ## 5. clearing denominators: `EpolyL a b n c = 0`, hence `GpolyL a b n c = 0`
  have hE : Work.C17C.EpolyL ((a : ℚ) : ℂ) ((b : ℚ) : ℂ) n c = 0 :=
    Work.C17adj2.adjoint_clearingL a b n c β hβ hh
  have hG : Work.C17C.GpolyL ((a : ℚ) : ℂ) ((b : ℚ) : ℂ) n c = 0 := by
    rw [Work.C17z.GpolyL_eq_EpolyL]
    exact hE
  -- ## 6. non-degeneracy of the certificate at an admissible pair:
  --        `Pdet4L = (1/240)·(a²−b²)²·Ψ₈ ≠ 0`
  have hPsi : Work.C17C.PsibL ((a : ℚ) : ℂ) ((b : ℚ) : ℂ) ≠ 0 := by
    rw [Work.C17C.PsibL_eq_map]
    exact_mod_cast Work.C17adj.Psi8_ne_zero a b hA.1 hA.2.1 hA.2.2.1
  have hP4 : Work.C17C.Pdet4L ((a : ℚ) : ℂ) ((b : ℚ) : ℂ) ≠ 0 := by
    rw [Work.C17C.PdetL_eq]
    have hab : ((a : ℂ) ^ 2 - (b : ℂ) ^ 2) ≠ 0 := by
      have hq : (a : ℚ) ^ 2 - b ^ 2 ≠ 0 := by
        have ha0 : (0 : ℚ) < a := lt_of_lt_of_le (by norm_num) hA.1
        have hb0 : (0 : ℚ) < b := lt_trans ha0 hA.2.1
        have h1 : (a + b) ≠ 0 := ne_of_gt (add_pos ha0 hb0)
        have h2 : a - b ≠ 0 := sub_ne_zero.mpr (ne_of_lt hA.2.1)
        have h3 : (a - b) * (a + b) ≠ 0 := mul_ne_zero h2 h1
        intro hh0
        have h4 : (a - b) * (a + b) = 0 := by
          rw [show (a - b) * (a + b) = a ^ 2 - b ^ 2 by ring, hh0]
        exact h3 h4
      intro hh0
      exact hq (by exact_mod_cast hh0)
    exact mul_ne_zero (by norm_num) (mul_ne_zero (pow_ne_zero 2 hab) hPsi)
  -- ## 7. the linear algebra certificate over `ℂ`
  obtain ⟨hn0, hc0⟩ := Work.C17z.linear_coreL ((a : ℚ) : ℂ) ((b : ℚ) : ℂ) hP4 n c hG
  -- ## 8. conclusion
  have hDne : Work.C17.DadjC ≠ 0 := by
    rw [Work.C17C.DadjC_eq]
    exact hDneL
  refine ⟨?_, ?_⟩
  · have hz : β * Work.C17.DadjC = 0 := by
      rw [hn]
      simp [hn0]
    exact (mul_eq_zero.mp hz).resolve_right hDne
  · funext i
    exact hc0 i

end Work.C17
