import Mathlib
import Submission.Work.LinnikBurgess.burgess_lead_defs

/-!
# Nondegeneracy of the critical polynomial `critN` for a singleton pair

`critN a b = f_a' f_b - f_a f_b'` is the Wronskian of the two cubics
`f_a = ∏_l (X + a_l)`, `f_b = ∏_l (X + b_l)`.  We show that whenever the shift
vector `shift a b = ![a 0, a 1, a 2, b 0, b 1, b 2]` has a *unique* entry (some
index `i` whose value differs from the five others), the two cubics are distinct,
and then:

* the Wronskian of two distinct monic cubics has degree at least `2`, and
* the content `contAB a b = gcd_k |e_k(a) - e_k(b)|` of the pair is nonzero.

The proof is the one indicated in `BURGESS_ROUTE_LEAD.md` (U4):
writing `g = f_a - f_b ≠ 0` (of degree `d ≤ 2`, leading coefficient `λ`) and
`h = f_b`, one has `critN a b = W(g,h) = g'h - gh'`, both terms have degree
`d + 2` and `X^{d+2}`-coefficients `λ d` and `3λ`, so the `X^{d+2}` coefficient
of `critN` is `λ(d-3) ≠ 0`.

The uniqueness hypothesis enters only through `f_a ≠ f_b`: if `f_a = f_b` then
every root `-a_l` of `f_a` is a root of `f_b`, so `a_l ∈ {b_0,b_1,b_2}` (and
symmetrically); consequently the value `shift a b i` occurs at least twice among
the six shifts, contradicting uniqueness.
-/

namespace Work.LinnikBurgess

open Polynomial

/-- The first three entries of `shift a b` are the `a l`. -/
lemma shift_castAdd (a b : Fin 3 → ℕ) (k : Fin 3) : shift a b (Fin.castAdd 3 k) = a k := by
  fin_cases k <;> rfl

/-- The last three entries of `shift a b` are the `b l`. -/
lemma shift_natAdd (a b : Fin 3 → ℕ) (k : Fin 3) : shift a b (Fin.natAdd 3 k) = b k := by
  fin_cases k <;> rfl

/-- Expansion of the cubic `∏_l (X + a_l)` in the elementary symmetric functions. -/
lemma cubicZ_expand (a : Fin 3 → ℕ) :
    cubicZ a = X ^ 3 + C (esymm3 a 0) * X ^ 2 + C (esymm3 a 1) * X + C (esymm3 a 2) := by
  rw [cubicZ, Fin.prod_univ_three]
  simp only [esymm3, Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
  simp only [C_add, C_mul]
  ring

/-- `cubicZ a` is monic of degree three. -/
lemma cubicZ_isMonicOfDegree (a : Fin 3 → ℕ) : (cubicZ a).IsMonicOfDegree 3 := by
  rw [cubicZ, Fin.prod_univ_three]
  have h := ((isMonicOfDegree_X_add_one ((a 0 : ℕ) : ℤ)).mul
      (isMonicOfDegree_X_add_one ((a 1 : ℕ) : ℤ))).mul
      (isMonicOfDegree_X_add_one ((a 2 : ℕ) : ℤ))
  simpa using h

/-- `critN` is the Wronskian of `g = f_a - f_b` with `h = f_b`. -/
lemma critN_eq_wronskian (a b : Fin 3 → ℕ) :
    critN a b = derivative (cubicZ a - cubicZ b) * cubicZ b
      - (cubicZ a - cubicZ b) * derivative (cubicZ b) := by
  have h : cubicZ a = (cubicZ a - cubicZ b) + cubicZ b := by ring
  rw [critN]
  conv_lhs => rw [h]
  rw [derivative_add]
  ring

/-- Wronskian degree lower bound: for `g ≠ 0` of degree `≤ 2` and monic `h` of degree `3`,
the Wronskian `g'h - gh'` has degree at least `2`.

Indeed with `d = g.natDegree ≤ 2` and `λ = g.leadingCoeff ≠ 0` the coefficient of
`X^{d+2}` in the Wronskian is `λ d - 3λ = λ (d - 3) ≠ 0`. -/
lemma natDegree_wronskian_ge_two (g h : ℤ[X]) (hg : g ≠ 0) (hgd : g.natDegree ≤ 2)
    (hh : h.IsMonicOfDegree 3) :
    2 ≤ (derivative g * h - g * derivative h).natDegree := by
  set d := g.natDegree with hd_def
  set c := g.leadingCoeff with hc_def
  have hc : c ≠ 0 := by rw [hc_def, leadingCoeff_ne_zero]; exact hg
  rcases Nat.eq_zero_or_pos d with hd0 | hdpos
  · -- `g` is constant: `g' = 0` and the Wronskian is `-g h'`, of degree `2`.
    have hgn0 : g.natDegree = 0 := by rw [← hd_def]; exact hd0
    have hgC : g = C c := by
      rw [eq_C_of_natDegree_eq_zero hgn0]
      congr 1
      show g.coeff 0 = c
      rw [hc_def, Polynomial.leadingCoeff, hgn0]
    have hexpr : derivative g * h - g * derivative h = -(C c * derivative h) := by
      rw [hgC, derivative_C]; ring
    have hcoeff : (derivative h).coeff 2 = 3 := by
      have h1 : (derivative h).coeff 2 = (derivative h).leadingCoeff := by
        rw [← coeff_natDegree, natDegree_derivative, hh.natDegree_eq]
      rw [h1, leadingCoeff_derivative, hh.leadingCoeff_eq, hh.natDegree_eq]
      norm_num
    refine le_natDegree_of_ne_zero ?_
    rw [hexpr, coeff_neg, coeff_C_mul, hcoeff]
    simp [hc]
  · -- `g` has degree `d ≥ 1`: compare the `X^{d+2}` coefficients.
    have hgd_ne : derivative g ≠ 0 := by rw [derivative_ne_zero]; omega
    have hh_ne : h ≠ 0 := hh.ne_zero
    have hdh_ne : derivative h ≠ 0 := by rw [derivative_ne_zero, hh.natDegree_eq]; norm_num
    have hnd1 : (derivative g * h).natDegree = d + 2 := by
      rw [natDegree_mul hgd_ne hh_ne, natDegree_derivative, hh.natDegree_eq, ← hd_def]
      omega
    have hlc1 : (derivative g * h).leadingCoeff = c * (d : ℤ) := by
      rw [leadingCoeff_mul, leadingCoeff_derivative, hh.leadingCoeff_eq, mul_one, ← hc_def,
        ← hd_def]
    have hc1 : (derivative g * h).coeff (d + 2) = c * (d : ℤ) := by
      rw [← hnd1, coeff_natDegree, hlc1]
    have hnd2 : (g * derivative h).natDegree = d + 2 := by
      rw [natDegree_mul hg hdh_ne, natDegree_derivative, hh.natDegree_eq, ← hd_def]
    have hlc2 : (g * derivative h).leadingCoeff = c * 3 := by
      rw [leadingCoeff_mul, leadingCoeff_derivative, hh.leadingCoeff_eq, hh.natDegree_eq,
        ← hc_def]
      norm_num
    have hc2 : (g * derivative h).coeff (d + 2) = c * 3 := by
      rw [← hnd2, coeff_natDegree, hlc2]
    have hcoeff : (derivative g * h - g * derivative h).coeff (d + 2) ≠ 0 := by
      rw [coeff_sub, hc1, hc2]
      have : c * (d : ℤ) - c * 3 = c * ((d : ℤ) - 3) := by ring
      rw [this]
      refine mul_ne_zero hc ?_
      omega
    exact le_trans (by omega) (le_natDegree_of_ne_zero hcoeff)

/-- If the two cubics `f_a` and `f_b` agree, then every value `a l` occurs among
`b 0, b 1, b 2` (evaluation at the root `-a l`). -/
lemma exists_eq_of_cubicZ_eq (a b : Fin 3 → ℕ) (h : cubicZ a = cubicZ b) (l : Fin 3) :
    ∃ l' : Fin 3, b l' = a l := by
  have h0 : (cubicZ b).eval (-((a l : ℕ) : ℤ)) = 0 := by
    rw [← h]
    rw [cubicZ, eval_prod]
    exact Finset.prod_eq_zero (Finset.mem_univ l) (by simp)
  rw [cubicZ, eval_prod] at h0
  obtain ⟨l', _, hl'⟩ := Finset.prod_eq_zero_iff.mp h0
  simp only [eval_add, eval_X, eval_C] at hl'
  refine ⟨l', ?_⟩
  have : ((b l' : ℕ) : ℤ) = ((a l : ℕ) : ℤ) := by omega
  exact_mod_cast this

theorem critN_ne_zero_of_unique (a b : Fin 3 → ℕ) (i : Fin 6)
    (hi : ∀ j : Fin 6, j ≠ i → shift a b i ≠ shift a b j) :
    2 ≤ (critN a b).natDegree ∧ contAB a b ≠ 0 := by
  -- The uniqueness hypothesis forces the two cubics to differ.
  have hne : cubicZ a ≠ cubicZ b := by
    intro h
    have ha_sub : ∀ l : Fin 3, ∃ l' : Fin 3, b l' = a l := fun l => exists_eq_of_cubicZ_eq a b h l
    have hb_sub : ∀ l' : Fin 3, ∃ l : Fin 3, a l = b l' :=
      fun l' => exists_eq_of_cubicZ_eq b a h.symm l'
    rcases i with ⟨n, hn6⟩
    rcases lt_or_ge n 3 with hn3 | hn3
    · -- `shift i = a⟨n⟩` also occurs as `b l' = shift (3 + l')`.
      obtain ⟨l', hl'⟩ := ha_sub ⟨n, hn3⟩
      exact hi (Fin.natAdd 3 l') (by
        intro hji
        have hval : (Fin.natAdd 3 l').val = n := by rw [hji]
        simp [Fin.natAdd] at hval
        omega) (by
        have h2 : shift a b ⟨n, hn6⟩ = a ⟨n, hn3⟩ := by
          rw [← shift_castAdd a b (⟨n, hn3⟩ : Fin 3)]
          exact congrArg (shift a b) (Fin.ext rfl)
        rw [h2, shift_natAdd]
        exact hl'.symm)
    · -- `shift i = b⟨n-3⟩` also occurs as `a l' = shift l'`.
      obtain ⟨l', hl'⟩ := hb_sub ⟨n - 3, by omega⟩
      exact hi (Fin.castAdd 3 l') (by
        intro hji
        have hval : (Fin.castAdd 3 l').val = n := by rw [hji]
        simp [Fin.castAdd] at hval
        omega) (by
        have h2 : shift a b ⟨n, hn6⟩ = b ⟨n - 3, by omega⟩ := by
          rw [← shift_natAdd a b (⟨n - 3, by omega⟩ : Fin 3)]
          exact congrArg (shift a b) (Fin.ext (by simp [Fin.natAdd]; omega))
        rw [h2, shift_castAdd]
        exact hl'.symm)
  refine ⟨?_, ?_⟩
  · rw [critN_eq_wronskian]
    exact natDegree_wronskian_ge_two _ _ (sub_ne_zero.mpr hne) (by
      have := (cubicZ_isMonicOfDegree a).natDegree_sub_lt (by norm_num : (3 : ℕ) ≠ 0)
        (cubicZ_isMonicOfDegree b)
      omega) (cubicZ_isMonicOfDegree b)
  · -- `contAB a b = 0` would force all three elementary symmetric functions to agree,
    -- hence `f_a = f_b`, contradicting `hne`.
    intro h0
    apply hne
    rw [contAB] at h0
    have hxA : (esymm3 a 0 - esymm3 b 0).natAbs = 0 := (Nat.gcd_eq_zero_iff.mp h0).1
    have hyz : Nat.gcd (esymm3 a 1 - esymm3 b 1).natAbs (esymm3 a 2 - esymm3 b 2).natAbs = 0 :=
      (Nat.gcd_eq_zero_iff.mp h0).2
    have hyA : (esymm3 a 1 - esymm3 b 1).natAbs = 0 := (Nat.gcd_eq_zero_iff.mp hyz).1
    have hzA : (esymm3 a 2 - esymm3 b 2).natAbs = 0 := (Nat.gcd_eq_zero_iff.mp hyz).2
    have hx : esymm3 a 0 = esymm3 b 0 := by
      have := Int.natAbs_eq_zero.mp hxA; omega
    have hy : esymm3 a 1 = esymm3 b 1 := by
      have := Int.natAbs_eq_zero.mp hyA; omega
    have hz : esymm3 a 2 = esymm3 b 2 := by
      have := Int.natAbs_eq_zero.mp hzA; omega
    rw [cubicZ_expand a, cubicZ_expand b, hx, hy, hz]

end Work.LinnikBurgess
