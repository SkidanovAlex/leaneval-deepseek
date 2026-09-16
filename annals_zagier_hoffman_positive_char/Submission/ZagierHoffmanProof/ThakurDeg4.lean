import Submission.ZagierHoffmanProof.ThakurDeg3

set_option autoImplicit false
set_option maxHeartbeats 4000000

open Polynomial RatFunc
open scoped BigOperators WithZero
open WithZero

/-!
# Step M4: Thakur's bound `s_d(k) ≥ d · s_1(k)` and the non-vanishing of depth-two MZVs

Thakur (2.2.5) observes that `S_d(k)` is the sum of the values of `S_1(k)` at the monic
polynomials of degree `d` with zero constant term: writing every monic `a` of degree `d`
as `a = X·n + c` with `n` monic of degree `d − 1` and `c ∈ F` gives

  `P_d(k) = ∑_{n ∈ A_{d-1}^+} ∑_{c : F} (X n + c)^{-k} = ∑_{n} zetaSum(k)(X·n)`,

and each inner sum, by Step M3, has valuation `exp (−d·(k + j_min(k)))`.  Hence

  `v (P_d(k)) ≤ exp (−d·(k + j_min(k))) = (v (P_1(k)))^d`.

This is the input for the non-vanishing of the depth-two MZV `ζ_A(a, b)`.
-/

namespace ZagierHoffmanPositiveChar

variable (F : Type*) [Field F] [Finite F] [DecidableEq (RatFunc F)]

section Decomp

/-- Dividing a monic polynomial of degree `d ≥ 1` by `X` gives a monic polynomial of
degree `d − 1`. -/
lemma divX_monic_deg (d : ℕ) (hd : 1 ≤ d) (p : F[X]) (hp : p.Monic) (hdeg : p.natDegree = d) :
    (p.divX).Monic ∧ (p.divX).natDegree = d - 1 := by
  have hle : (p.divX).natDegree ≤ d - 1 := by
    rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
    intro n hn
    rw [Polynomial.coeff_divX]
    exact Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)
  have hcoeff : (p.divX).coeff (d - 1) = 1 := by
    rw [Polynomial.coeff_divX]
    have : d - 1 + 1 = d := by omega
    rw [this]
    simpa [hdeg] using hp.coeff_natDegree
  have hnd := Polynomial.natDegree_eq_of_le_of_coeff_ne_zero hle (by rw [hcoeff]; exact one_ne_zero)
  refine ⟨?_, hnd⟩
  show (p.divX).leadingCoeff = 1
  rw [Polynomial.leadingCoeff, hnd, hcoeff]

/-- `X · n + C c` is monic of degree `d` when `n` is monic of degree `d − 1`. -/
lemma X_mul_monic_deg (d : ℕ) (hd : 1 ≤ d) (n : F[X]) (hn : n.Monic) (hdeg : n.natDegree = d - 1)
    (c : F) :
    (Polynomial.X * n + Polynomial.C c).Monic ∧
      (Polynomial.X * n + Polynomial.C c).natDegree = d := by
  have hXn : (Polynomial.X * n).Monic := Polynomial.monic_X.mul hn
  have hXnd : (Polynomial.X * n).natDegree = d := by
    rw [Polynomial.natDegree_mul Polynomial.X_ne_zero (Polynomial.Monic.ne_zero hn), hdeg,
      Polynomial.natDegree_X]
    omega
  have hlt : (Polynomial.C c : F[X]).natDegree < (Polynomial.X * n).natDegree := by
    rw [hXnd]
    by_cases hc : c = 0
    · rw [hc, Polynomial.C_0, Polynomial.natDegree_zero]; omega
    · rw [Polynomial.natDegree_C]; omega
  have hnd : (Polynomial.X * n + Polynomial.C c).natDegree = d := by
    rw [Polynomial.natDegree_add_eq_left_of_natDegree_lt hlt, hXnd]
  refine ⟨?_, hnd⟩
  show (Polynomial.X * n + Polynomial.C c).leadingCoeff = 1
  rw [Polynomial.leadingCoeff, hnd]
  have h1 : (Polynomial.X * n).coeff d = 1 := by
    rw [← hXnd]
    exact hXn.coeff_natDegree
  rw [Polynomial.coeff_add, h1, Polynomial.coeff_C, if_neg (by omega)]
  ring

/-- The constant term of `X · n + C c`. -/
lemma coeff_zero_X_mul_add (n : F[X]) (c : F) :
    (Polynomial.X * n + Polynomial.C c).coeff 0 = c := by
  rw [Polynomial.coeff_add, Polynomial.coeff_C_zero]
  have h : (Polynomial.X * n).coeff 0 = 0 := Polynomial.X_dvd_iff.mp ⟨n, by ring⟩
  rw [h, zero_add]

/-- `divX (X · n + C c) = n`. -/
lemma divX_X_mul_add_C (n : F[X]) (c : F) : (Polynomial.X * n + Polynomial.C c).divX = n := by
  have h := Polynomial.X_mul_divX_add (Polynomial.X * n + Polynomial.C c)
  rw [coeff_zero_X_mul_add F n c] at h
  exact mul_left_cancel₀ Polynomial.X_ne_zero (add_right_cancel h)

/-- The monic degree-`d` polynomials are the pairs (monic of degree `d-1`, constant). -/
noncomputable def headDEquiv (d : ℕ) (hd : 1 ≤ d) : HeadD F d ≃ HeadD F (d - 1) × F where
  toFun p := (⟨p.1.divX, divX_monic_deg F d hd p.1 p.2.1 p.2.2⟩, p.1.coeff 0)
  invFun q := ⟨Polynomial.X * q.1.1 + Polynomial.C q.2,
    X_mul_monic_deg F d hd q.1.1 q.1.2.1 q.1.2.2 q.2⟩
  left_inv p := by
    apply Subtype.ext
    show Polynomial.X * p.1.divX + Polynomial.C (p.1.coeff 0) = p.1
    rw [Polynomial.X_mul_divX_add]
  right_inv q := by
    apply Prod.ext
    · apply Subtype.ext
      exact divX_X_mul_add_C F q.1.1 q.2
    · exact coeff_zero_X_mul_add F q.1.1 q.2

end Decomp

section Sums

/-- The constant polynomial as an element of the completion. -/
lemma coe_poly_C (c : F) : (((Polynomial.C c : F[X]) : RatFunc F) : RatFunc.CompletionAtInfty F)
    = cst F c := by
  rw [cst, cstHom, RingHom.comp_apply]
  rfl

/-- Splitting `X · n + C c` into its two summands inside the completion. -/
lemma coe_X_mul_add_C (n : F[X]) (c : F) :
    (((Polynomial.X * n + Polynomial.C c : F[X]) : RatFunc F) : RatFunc.CompletionAtInfty F)
      = (((Polynomial.X * n : F[X]) : RatFunc F) : RatFunc.CompletionAtInfty F) + cst F c := by
  rw [show (((Polynomial.X * n + Polynomial.C c : F[X]) : RatFunc F)
        : RatFunc.CompletionAtInfty F)
      = (((Polynomial.X * n : F[X]) : RatFunc F) : RatFunc.CompletionAtInfty F)
        + (((Polynomial.C c : F[X]) : RatFunc F) : RatFunc.CompletionAtInfty F) from by
    change algebraMap (RatFunc F) (RatFunc.CompletionAtInfty F)
        (((Polynomial.X * n + Polynomial.C c : F[X]) : RatFunc F))
      = algebraMap (RatFunc F) (RatFunc.CompletionAtInfty F)
          (((Polynomial.X * n : F[X]) : RatFunc F))
        + algebraMap (RatFunc F) (RatFunc.CompletionAtInfty F)
          (((Polynomial.C c : F[X]) : RatFunc F))
    rw [← map_add]
    congr 1
    simp]
  rw [coe_poly_C F c]

/-- The degree-`d` power sum, split by the constant term of the monic polynomials. -/
lemma P_eq_sum_prod (d : ℕ) (hd : 1 ≤ d) (k : ℕ+) :
    letI : Fintype F := Fintype.ofFinite F
    P F d k = ∑ q : HeadD F (d - 1) × F,
      ((((Polynomial.X * q.1.1 + Polynomial.C q.2 : F[X]) : RatFunc F)
        : RatFunc.CompletionAtInfty F) ^ (k : ℕ))⁻¹ := by
  classical
  letI : Fintype F := Fintype.ofFinite F
  rw [P_eq_sum F d k]
  refine Fintype.sum_equiv (headDEquiv F d hd) _ _ ?_
  intro p
  show (((((p.1 : F[X]) : RatFunc F) : RatFunc.CompletionAtInfty F) ^ (k : ℕ))⁻¹)
      = (((((Polynomial.X * p.1.divX + Polynomial.C (p.1.coeff 0) : F[X]) : RatFunc F)
          : RatFunc.CompletionAtInfty F) ^ (k : ℕ))⁻¹)
  conv_lhs => rw [← Polynomial.X_mul_divX_add p.1]

/-- The sum over the constant term at fixed `n` is `zetaSum`. -/
lemma sum_translate_eq_zetaSum (k : ℕ+) (n : F[X]) :
    letI : Fintype F := Fintype.ofFinite F
    (∑ c : F, ((((Polynomial.X * n + Polynomial.C c : F[X]) : RatFunc F)
        : RatFunc.CompletionAtInfty F) ^ (k : ℕ))⁻¹)
      = zetaSum F (k : ℕ) (((Polynomial.X * n : F[X]) : RatFunc F)
          : RatFunc.CompletionAtInfty F) := by
  classical
  letI : Fintype F := Fintype.ofFinite F
  rw [zetaSum]
  apply Finset.sum_congr rfl
  intro c _
  rw [coe_X_mul_add_C F n c]

end Sums

section Bound

/-- `X · n` is monic of degree `d` when `n` is monic of degree `d − 1`, `d ≥ 1`. -/
lemma X_mul_monic (d : ℕ) (hd : 1 ≤ d) (n : F[X]) (hn : n.Monic) (hdeg : n.natDegree = d - 1) :
    (Polynomial.X * n).Monic ∧ (Polynomial.X * n).natDegree = d := by
  refine ⟨Polynomial.monic_X.mul hn, ?_⟩
  rw [Polynomial.natDegree_mul Polynomial.X_ne_zero hn.ne_zero, hdeg, Polynomial.natDegree_X]
  omega

/-- ★★ **Thakur 2.2.5**: `s_d(k) ≥ d · s_1(k)`, in valuation form
`v (P_d(k)) ≤ exp (−d (k + j_min(k))) = (v (P_1(k)))^d`. -/
theorem v_P_le (d : ℕ) (hd : 1 ≤ d) (k : ℕ+) :
    Valued.v (P F d k) ≤ WithZero.exp (-((d : ℤ) * ((k : ℤ) + jMin F k))) := by
  classical
  letI : Fintype F := Fintype.ofFinite F
  rw [P_eq_sum_prod F d hd k, Fintype.sum_prod_type]
  refine le_trans (Valuation.map_sum_le
    (v := (Valued.v : Valuation (RatFunc.CompletionAtInfty F) ℤᵐ⁰))
    (g := WithZero.exp (-((d : ℤ) * ((k : ℤ) + jMin F k)))) ?_) le_rfl
  intro n _
  rw [sum_translate_eq_zetaSum F k n.1]
  have hXn := X_mul_monic F d hd n.1 n.2.1 n.2.2
  have hne : Polynomial.X * n.1 ≠ 0 := hXn.1.ne_zero
  refine le_of_eq (v_zetaSum F k (((Polynomial.X * n.1 : F[X]) : RatFunc F)
      : RatFunc.CompletionAtInfty F) (d : ℤ) ?_ ?_ ?_ ?_)
  · intro hcon
    have := inftyValued_v_polynomial F (Polynomial.X * n.1) hne
    rw [hcon, map_zero] at this
    exact WithZero.exp_ne_zero this.symm
  · rw [inftyValued_v_polynomial F _ hne, hXn.2]
  · exact_mod_cast hd
  · intro c
    have hc := X_mul_monic_deg F d hd n.1 n.2.1 n.2.2 c
    have hne' : Polynomial.X * n.1 + Polynomial.C c ≠ 0 := hc.1.ne_zero
    rw [← coe_X_mul_add_C F n.1 c, inftyValued_v_polynomial F _ hne', hc.2,
      inftyValued_v_polynomial F _ hne, hXn.2]

end Bound

end ZagierHoffmanPositiveChar
