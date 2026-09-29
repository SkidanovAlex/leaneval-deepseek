import Mathlib
import Submission.Work.C17.riccati_no_rational_C
import Submission.Work.C17y.adjoint_no_solution_rat
import Submission.Work.C17.adjoint_C_defs
import Submission.Work.C17z.adj_certificate
import Submission.Work.C17adj2.adjoint_clearingL
import Submission.Work.C17adj.adjoint_divisor_boundC
import Submission.Work.C17adj.adjoint_base_change

/-!
# The adjoint equation over `ℂ(x)` has only the trivial solution

`Work.C17z.adjoint_no_solution_C` is the `ℂ`-version of `Work.C17.adjoint_no_solution`
(`Submission/Work/C17/adjoint_no_solution.lean`): for an admissible pair `(a,b) : ℚ²` the
inhomogeneous adjoint equation

  `(P₂β)'' − (P₁β)' + P₀β = Σ_{i<6} cᵢ · y^{i−4}·y'`,   `y = x²/(x−1)`,

with `β ∈ ℂ(x)`, `cᵢ ∈ ℂ` has no nontrivial solution.

The proof follows the same route as the `ℚ`-statement:

* the divisor bound over `ℂ` (`Work.C17adj.adjoint_divisor_boundC`): a solution has
  `β·x⁶(x−1)²(x+1)² = NpolyL n` with `n : Fin 7 → ℂ`;
* the denominator-cleared certificate over `ℂ` (`Work.C17adj2.adjoint_clearingL`):
  if `β = NpolyL n / DadjL` then `EpolyL a b n c = 0`, and `EpolyL = GpolyL` as explicit
  polynomials (`GpolyL_eq_EpolyL` below);
* the linear algebra certificate over `ℂ` (`Work.C17z.linear_coreL`, in
  `Submission/Work/C17z/adj_certificate.lean`, the literal `ℂ`-copy of the machine generated
  certificate `Work.C17.linear_core`): `GpolyL a b n c = 0 ⟹ n = 0 ∧ c = 0`.

The only genuinely `ℂ`-specific inputs are the two bridges proved here: the `ℂ`-copy of the
`Gpoly = Epoly` computation, and the identification of the right hand side `Σᵢ cᵢ·rnᵢ/rdᵢ` with
`Σᵢ cᵢ·y^{i−4}·y'` through the base change `Work.C17adj.T : ℚ(x) → ℂ(x)`.
-/

namespace Work.C17z

open Polynomial

set_option maxHeartbeats 4000000000 in
set_option maxRecDepth 1000000 in
/-- `GpolyL = EpolyL`: the `ℂ`-copy of `Work.C17adj.Gpoly_eq_Epoly`. -/
theorem GpolyL_eq_EpolyL (a b : ℂ) (n : Fin 7 → ℂ) (c : Fin 6 → ℂ) :
    Work.C17C.GpolyL a b n c = Work.C17C.EpolyL a b n c := by
  unfold Work.C17C.GpolyL Work.C17C.EpolyL Work.C17C.LeftPolyL Work.C17C.RightPolyL
  -- expand the range of degrees `11, …, 31` of `GpolyL`
  rw [show (Finset.Icc 11 31 : Finset ℕ) =
      ({11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27,28,29,30,31} : Finset ℕ)
      from by decide]
  repeat rw [Finset.sum_insert (by decide)]
  rw [Finset.sum_singleton]
  simp only [Work.C17C.P2xL, Work.C17C.Q4xL, Work.C17C.BadjL, Work.C17C.CadjL,
    Work.C17C.DadjL, Work.C17C.Dadj1L, Work.C17C.Dadj2L, Work.C17C.NpolyL, Work.C17C.NpolyDL,
    Work.C17C.NpolyDDL, Work.C17C.LformL, Work.C17C.gD3L, Work.C17C.gD3L_0,
    Work.C17C.gD3L_1, Work.C17C.gD3L_2, Work.C17C.gD3L_3, Work.C17C.gD3L_4, Work.C17C.gD3L_5,
    Fin.isValue, Matrix.cons_val, Fin.coe_ofNat_eq_mod, Nat.reduceMod, Nat.reduceSub,
    Fin.sum_univ_seven, Fin.sum_univ_six]
  simp only [map_mul, map_add, map_sub, map_pow, map_neg, map_natCast, map_ofNat, map_one,
    Fin.isValue, Nat.cast_ofNat, pow_zero, mul_one, one_mul]
  ring

/-- The right hand side of the target statement is the `ℂ`-image of the `ℚ`-right hand side:
`rnᵢ/rdᵢ = y^{i−4}·y'` (`y = x²/(x−1)`). -/
theorem rnC_div_rdC (i : Fin 6) :
    algebraMap (Polynomial ℂ) (RatFunc ℂ) (Work.C17.rnC i)
        / algebraMap (Polynomial ℂ) (RatFunc ℂ) (Work.C17.rdC i)
      = Work.C17.yQc ^ ((i : ℤ) - 4) * Work.C17.dyQc := by
  have key : (algebraMap (Polynomial ℂ) (RatFunc ℂ) (Work.C17.rnC i)
        / algebraMap (Polynomial ℂ) (RatFunc ℂ) (Work.C17.rdC i))
      = Work.C17adj.T (Work.C17.yQ ^ ((i : ℤ) - 4) * Work.C17.dyQ) := by
    show algebraMap (Polynomial ℂ) (RatFunc ℂ)
          (((Work.C17.yQ ^ ((i : ℤ) - 4)) * Work.C17.dyQ).num.map (algebraMap ℚ ℂ))
        / algebraMap (Polynomial ℂ) (RatFunc ℂ)
          (((Work.C17.yQ ^ ((i : ℤ) - 4)) * Work.C17.dyQ).denom.map (algebraMap ℚ ℂ))
      = Work.C17adj.T (Work.C17.yQ ^ ((i : ℤ) - 4) * Work.C17.dyQ)
    rw [← Work.C17adj.T_algebraMap (((Work.C17.yQ ^ ((i : ℤ) - 4)) * Work.C17.dyQ).num),
      ← Work.C17adj.T_algebraMap (((Work.C17.yQ ^ ((i : ℤ) - 4)) * Work.C17.dyQ).denom),
      ← map_div₀, ← Submission.CDT.num_denom_eq (Work.C17.yQ ^ ((i : ℤ) - 4) * Work.C17.dyQ)]
  rw [key, map_mul, map_zpow₀, Work.C17adj.T_yQ, Work.C17adj.T_dyQ]

/-- The `ℂ`-images of the coefficient polynomials of `M`. -/
theorem Pac_eq (a b : ℚ) :
    Work.C17.Pac a b = algebraMap (Polynomial ℂ) (RatFunc ℂ) (Work.C17.P2C a b) := rfl

theorem Pbc_eq (a b : ℚ) :
    Work.C17.Pbc a b = algebraMap (Polynomial ℂ) (RatFunc ℂ) (Work.C17.P1C a b) := rfl

theorem Pcc_eq (a b : ℚ) :
    Work.C17.Pcc a b = algebraMap (Polynomial ℂ) (RatFunc ℂ) (Work.C17.P0C a b) := rfl

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
  -- ## 1. the hypothesis, in the `Pac/Pbc/Pcc` + `yQc/dyQc` normal form used by the divisor bound
  have hRhs : (∑ i : Fin 6, (algebraMap ℂ (RatFunc ℂ) (c i)) *
            (algebraMap (Polynomial ℂ) (RatFunc ℂ) (Work.C17.rnC i)
              / algebraMap (Polynomial ℂ) (RatFunc ℂ) (Work.C17.rdC i)))
        = ∑ i : Fin 6, algebraMap ℂ (RatFunc ℂ) (c i)
            * Work.C17.yQc ^ ((i : ℤ) - 4) * Work.C17.dyQc := by
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [rnC_div_rdC i, ← mul_assoc]
  have h' : Submission.CDT.dRat (Submission.CDT.dRat (Work.C17.Pac a b * β))
        - Submission.CDT.dRat (Work.C17.Pbc a b * β) + Work.C17.Pcc a b * β
      = ∑ i : Fin 6, algebraMap ℂ (RatFunc ℂ) (c i)
          * Work.C17.yQc ^ ((i : ℤ) - 4) * Work.C17.dyQc := by
    have h2 := h
    rw [← Pac_eq a b, ← Pbc_eq a b, ← Pcc_eq a b, hRhs] at h2
    exact h2
  -- ## 2. the divisor bound over `ℂ`
  obtain ⟨n, hn⟩ := Work.C17adj.adjoint_divisor_boundC a b hA β c h'
  -- ## 3. clearing denominators
  have hDneL : (algebraMap (Polynomial ℂ) (RatFunc ℂ) (Work.C17C.DadjL)) ≠ 0 :=
    RatFunc.algebraMap_ne_zero Work.C17C.DadjL_ne_zero
  have hDne : Work.C17.DadjC ≠ 0 := by
    rw [Work.C17C.DadjC_eq]
    exact hDneL
  have hNpoly : algebraMap (Polynomial ℂ) (RatFunc ℂ) (Work.C17C.NpolyL n)
      = ∑ k : Fin 7, algebraMap (Polynomial ℂ) (RatFunc ℂ)
          (Polynomial.C (n k) * Polynomial.X ^ (k : ℕ)) := by
    rw [Work.C17C.NpolyL, map_sum]
  have hβ : β = algebraMap (Polynomial ℂ) (RatFunc ℂ) (Work.C17C.NpolyL n)
        / algebraMap (Polynomial ℂ) (RatFunc ℂ) (Work.C17C.DadjL) := by
    rw [eq_div_iff hDneL, hNpoly, ← hn, ← Work.C17C.DadjC_eq]
  -- ## 4. the adjoint operator identity in the `P2xL/P1xL/P0xL` normal form
  have hh : Work.C17C.AdjOpL ((a : ℚ) : ℂ) ((b : ℚ) : ℂ) β = Work.C17C.RhsYc c := by
    rw [Work.C17C.AdjOpL, Work.C17C.RhsYc, ← Work.C17C.WorkC_P2C_eq a b,
      ← Work.C17C.WorkC_P1C_eq a b, ← Work.C17C.WorkC_P0C_eq a b]
    have h2 := h
    rw [hRhs] at h2
    exact h2
  -- ## 5. the cleared polynomial identity `EpolyL = 0`, hence `GpolyL = 0`
  have hE : Work.C17C.EpolyL ((a : ℚ) : ℂ) ((b : ℚ) : ℂ) n c = 0 :=
    Work.C17adj2.adjoint_clearingL a b n c β hβ hh
  have hG : Work.C17C.GpolyL ((a : ℚ) : ℂ) ((b : ℚ) : ℂ) n c = 0 := by
    rw [GpolyL_eq_EpolyL]; exact hE
  -- ## 6. non-degeneracy of the certificate at an admissible pair
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
  obtain ⟨hn0, hc0⟩ := linear_coreL ((a : ℚ) : ℂ) ((b : ℚ) : ℂ) hP4 n c hG
  -- ## 8. conclusion
  constructor
  · have hz : β * Work.C17.DadjC = 0 := by
      rw [hn]
      simp [hn0]
    exact (mul_eq_zero.mp hz).resolve_right hDne
  · funext i
    exact hc0 i

end Work.C17z
