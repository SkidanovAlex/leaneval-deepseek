import Mathlib
import Submission.Work.A14.defs
import Submission.Work.A14D.riccatiZ_helpers
import Submission.Work.A14D.riccatiZ_degree
import Submission.Work.A14D.riccatiZ_residue
import Submission.Work.C17.riccati_denom_squarefree
import Submission.Work.C17.roots_sum_div_derivative

/-!
# `Work.A14D.riccatiZ_no_rational`

The Riccati equation of `L_Z` (`P·(u' + u²) + P'·u + R = 0`, `P = X − 10X² + 9X³`,
`P' = 1 − 20X + 27X²`, `R = −3 + 9X`) has no solution `u ∈ ℂ(X)`.

Writing `u = A/B` in lowest terms (`B` monic) and clearing denominators produces the polynomial
identity `Q2Z·(A'B − AB') + Q2Z·A² + Q1Z·A·B + Q0Z·B² = 0`.

* `riccatiZ_degree` gives `deg A = deg B − 1` and `lc A = −1`, so `A` has degree one less than `B`;
* `riccatiZ_residue` + `Work.C17.riccati_denom_squarefree` show that every root `β` of `B` is
  simple and satisfies `A(β)/B'(β) = 1`;
* hence the sum of residues `∑_{β ∈ B.roots} A(β)/B'(β)` equals `deg B ≥ 1`
  (each term is `1`), while `Work.C17.roots_sum_div_derivative` computes it as
  `A.coeff (deg B − 1) = −1` — a contradiction.
-/

namespace Work.A14D

open Polynomial

noncomputable section

theorem riccatiZ_no_rational (u : RatFunc ℂ) :
    (algebraMap (Polynomial ℂ) (RatFunc ℂ) (X - 10 * X ^ 2 + 9 * X ^ 3)) * (Submission.CDT.dRat u + u ^ 2)
      + (algebraMap (Polynomial ℂ) (RatFunc ℂ) (1 - 20 * X + 27 * X ^ 2)) * u
      + algebraMap (Polynomial ℂ) (RatFunc ℂ) (-3 + 9 * X) ≠ 0 := by
  intro hEq
  -- ## 1. Clear denominators: the polynomial identity.
  have hpoly : Q2Z * (u.num.derivative * u.denom - u.num * u.denom.derivative) + Q2Z * u.num ^ 2
      + Q1Z * u.num * u.denom + Q0Z * u.denom ^ 2 = 0 := by
    have hden : u.denom ≠ 0 := RatFunc.denom_ne_zero u
    have hAmap : (algebraMap (Polynomial ℂ) (RatFunc ℂ) u.denom) ≠ 0 := by simpa using hden
    have hnum : u = algebraMap (Polynomial ℂ) (RatFunc ℂ) u.num
        / algebraMap (Polynomial ℂ) (RatFunc ℂ) u.denom := (RatFunc.num_div_denom u).symm
    have key : (algebraMap (Polynomial ℂ) (RatFunc ℂ))
        ((X - 10 * X ^ 2 + 9 * X ^ 3 : Polynomial ℂ)
            * (u.num.derivative * u.denom - u.num * u.denom.derivative)
          + (X - 10 * X ^ 2 + 9 * X ^ 3 : Polynomial ℂ) * u.num ^ 2
          + (1 - 20 * X + 27 * X ^ 2 : Polynomial ℂ) * u.num * u.denom
          + (-3 + 9 * X : Polynomial ℂ) * u.denom ^ 2) = 0 := by
      rw [hnum, Submission.CDT.dRat_div] at hEq
      simp only [map_add, map_mul, map_sub, map_pow] at hEq ⊢
      field_simp at hEq ⊢
      ring_nf at hEq ⊢
      linear_combination hEq
    exact RatFunc.algebraMap_injective ℂ (by simpa [Q2Z, Q1Z, Q0Z] using key)
  have hBmonic : u.denom.Monic := RatFunc.monic_denom u
  have hcop : IsCoprime u.num u.denom := RatFunc.isCoprime_num_denom u
  have hAne : u.num ≠ 0 := by
    intro h0
    rw [h0] at hpoly
    have hz : Q0Z * u.denom ^ 2 = 0 := by simpa using hpoly
    rcases mul_eq_zero.mp hz with h | h
    · exact Q0Z_ne_zero h
    · exact pow_ne_zero 2 (RatFunc.denom_ne_zero u) h
  -- ## 2. Degree of `A` and `B`.
  obtain ⟨hdegA, hleadA⟩ := riccatiZ_degree u.num u.denom hBmonic hAne hpoly
  have hBdeg : 1 ≤ u.denom.natDegree := by
    by_contra hcon
    have hBnat : u.denom.natDegree = 0 := by omega
    have hAnat : u.num.natDegree = 0 := by omega
    have hAcoeff : u.num.coeff 0 = -1 := by
      rw [← hAnat, Polynomial.coeff_natDegree]
      exact hleadA
    have hAeq : u.num = Polynomial.C (-1) := by
      rw [Polynomial.eq_C_of_natDegree_eq_zero hAnat, hAcoeff]
    have hBeq : u.denom = 1 := by
      have hc : u.denom.coeff 0 = 1 := by
        rw [← hBnat, Polynomial.coeff_natDegree]
        exact hBmonic
      rw [Polynomial.eq_C_of_natDegree_eq_zero hBnat, hc, Polynomial.C_1]
    rw [hAeq, hBeq] at hpoly
    have h3 := congrArg (Polynomial.eval (3 : ℂ)) hpoly
    simp [Q2Z, Q1Z, Q0Z, Polynomial.derivative_C, Polynomial.derivative_one,
      Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_sub, Polynomial.eval_pow,
      Polynomial.eval_C, Polynomial.eval_one, Polynomial.eval_X] at h3
    norm_num at h3
  -- ## 3. `B` is squarefree.
  have hrootP2 : ∀ α : ℂ, Q2Z.rootMultiplicity α ≤ 1 := Q2Z_rootMultiplicity_le_one
  have hsf : ∀ α : ℂ, u.denom.rootMultiplicity α ≤ 1 :=
    Work.C17.riccati_denom_squarefree Q2Z Q1Z Q0Z u.num u.denom hBmonic Q2Z_ne_zero hcop hrootP2 hpoly
  have hnodup : u.denom.roots.Nodup := by
    rw [Multiset.nodup_iff_count_le_one]
    intro β
    rw [Polynomial.count_roots]
    exact hsf β
  -- ## 4. The sum of residues, computed two ways.
  have hdeg_lt : u.num.natDegree < u.denom.natDegree := by omega
  have hsum := Work.C17.roots_sum_div_derivative u.num u.denom hBmonic hnodup hdeg_lt
  have hcoeff : u.num.coeff (u.denom.natDegree - 1) = -1 := by
    rw [← hdegA, Polynomial.coeff_natDegree]
    exact hleadA
  have hsumval : (u.denom.roots.map (fun β => u.num.eval β / u.denom.derivative.eval β)).sum = -1 := by
    rw [hsum]; exact hcoeff
  have hres : (u.denom.roots.map (fun β => u.num.eval β / u.denom.derivative.eval β)).sum
      = (u.denom.roots.card : ℂ) := by
    rw [show (u.denom.roots.map (fun β => u.num.eval β / u.denom.derivative.eval β))
        = u.denom.roots.map (fun _ => (1 : ℂ)) from
          Multiset.map_congr rfl (fun β hβ => riccatiZ_residue u.num u.denom hBmonic hcop hpoly hβ)]
    simp
  have hcard : u.denom.roots.card = u.denom.natDegree :=
    ((IsAlgClosed.splits u.denom).natDegree_eq_card_roots).symm
  -- ## 5. Contradiction: a natural number cannot be `−1`.
  have hbig : ((u.denom.natDegree : ℂ)) = -1 := by
    rw [← hcard]
    exact hres.symm.trans hsumval
  have hre := congrArg Complex.re hbig
  simp at hre
  have hnonneg : (0 : ℝ) ≤ (u.denom.natDegree : ℝ) := Nat.cast_nonneg _
  linarith

end

end Work.A14D
