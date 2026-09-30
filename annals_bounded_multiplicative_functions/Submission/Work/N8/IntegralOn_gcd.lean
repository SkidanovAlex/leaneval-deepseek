import Mathlib
import Submission.Work.BMF.Defs
import Submission.Work.BMF.newton_series
import Submission.Work.BMF.lattice_top_coeff
import Submission.Work.BMF.adi_basic
import Submission.Work.BMF.adi_defs
import Submission.Work.BMF.intval_basis
import Submission.Work.BMF.binP_intValued
import Submission.Work.N8.ExistsIntCoprimeMul

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Bézout/gcd closure for lattice-integral polynomials (MRTTZ Appendix B)

If `γ` has degree `≤ k` and maps both `aℤ` and `bℤ` into `ℤ`, then it maps `gcd a b ℤ` into `ℤ`.

The proof follows the sketch in the docstring of `IntegralOn_gcd`: reduce to the case of coprime
`a, b` by substituting `t ↦ g t` (`g = gcd a b`), then induct on the degree bound, peeling off the
top term `M · binP d` where `M = d! · γ.coeff d` is forced to be an integer by `lattice_top_coeff`
and coprimality of `a^d` and `b^d`.
-/

namespace Work.N8

open Polynomial

/-- `(dil c P).eval x = P.eval (c * x)`. -/
private theorem dil_eval_apply (c x : ℝ) (P : ℝ[X]) :
    (Work.BMF.dil c P).eval x = P.eval (c * x) := by
  unfold Work.BMF.dil
  rw [Polynomial.eval_comp, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X]

/-- Integrality on `ℤ` gives integrality on `nℤ` for every natural `n`. -/
private theorem integralOn_of_one {γ : ℝ[X]} (h : Work.BMF.IntegralOn 1 γ) (n : ℕ) :
    Work.BMF.IntegralOn (n : ℝ) γ := by
  intro m
  obtain ⟨z, hz⟩ := h ((n : ℤ) * m)
  refine ⟨z, ?_⟩
  rw [show (n : ℝ) * (m : ℝ) = 1 * (((n : ℤ) * m : ℤ) : ℝ) by push_cast; ring]
  exact hz

/-- `binP d` is integer-valued on all of `ℤ`. -/
private theorem integralOn_one_binP (d : ℕ) : Work.BMF.IntegralOn 1 (Work.BMF.binP d) := by
  intro n
  obtain ⟨z, hz⟩ := Work.BMF.binP_intValued d n
  exact ⟨z, by simpa using hz⟩

/-- The leading coefficient of `binP d` is `1/d!`, in the multiplicative form. -/
private theorem binP_coeff_mul_factorial (d : ℕ) :
    (d.factorial : ℝ) * (Work.BMF.binP d).coeff d = 1 := by
  rw [Work.BMF.binP, Polynomial.coeff_C_mul]
  have h : (descPochhammer ℝ d).coeff d = 1 := by
    simpa [Polynomial.Monic, Polynomial.leadingCoeff, descPochhammer_natDegree ℝ d]
      using monic_descPochhammer ℝ d
  rw [h, mul_one]
  exact mul_inv_cancel₀ (by exact_mod_cast Nat.factorial_ne_zero d)

/-- **Coprime case.**  If `γ` is integral on `aℤ` and on `bℤ` for coprime `a, b` and has degree
`≤ k`, then `γ` is integral on `ℤ`. -/
private theorem coprime_integral (a b : ℕ) (hab : Nat.Coprime a b) :
    ∀ k (γ : ℝ[X]), γ.natDegree ≤ k → Work.BMF.IntegralOn (a : ℝ) γ →
      Work.BMF.IntegralOn (b : ℝ) γ → Work.BMF.IntegralOn 1 γ := by
  intro k
  induction k with
  | zero =>
      intro γ hdeg haγ _hbγ n
      have hγc : γ = Polynomial.C (γ.coeff 0) := Polynomial.eq_C_of_natDegree_le_zero hdeg
      obtain ⟨m, hm⟩ := haγ 0
      simp only [Int.cast_zero, mul_zero] at hm
      refine ⟨m, ?_⟩
      rw [one_mul, hγc, Polynomial.eval_C, Polynomial.coeff_zero_eq_eval_zero]
      exact hm
  | succ k ih =>
      intro γ hdeg haγ hbγ
      by_cases hle : γ.natDegree ≤ k
      · exact ih γ hle haγ hbγ
      · have hnd : γ.natDegree = k + 1 := by omega
        -- the top coefficient, rescaled by `a^{natDegree}` and `natDegree!`, is an integer
        have hA : ∃ m : ℤ,
            (a : ℝ) ^ γ.natDegree * ((γ.natDegree).factorial : ℝ) * γ.coeff γ.natDegree
              = (m : ℝ) := by
          have hint : ∀ n : ℤ, ∃ m : ℤ,
              (((1 : ℕ)) : ℝ) * (Work.BMF.dil (a : ℝ) γ).eval
                ((1 / (((1 : ℕ)) : ℝ)) * (n : ℝ)) = (m : ℝ) := by
            intro n
            obtain ⟨z, hz⟩ := haγ n
            exact ⟨z, by simpa [dil_eval_apply] using hz⟩
          obtain ⟨m, hm⟩ := Work.BMF.lattice_top_coeff (j := γ.natDegree) (D := 1) (Qm := 1)
            (G := Work.BMF.dil (a : ℝ) γ) le_rfl le_rfl
            (Work.BMF.natDegree_dil_le (a : ℝ) γ) hint
          refine ⟨m, ?_⟩
          simp only [Nat.cast_one, one_mul, one_pow, div_one] at hm
          rw [Work.BMF.coeff_dil] at hm
          linear_combination hm
        have hB : ∃ m : ℤ,
            (b : ℝ) ^ γ.natDegree * ((γ.natDegree).factorial : ℝ) * γ.coeff γ.natDegree
              = (m : ℝ) := by
          have hint : ∀ n : ℤ, ∃ m : ℤ,
              (((1 : ℕ)) : ℝ) * (Work.BMF.dil (b : ℝ) γ).eval
                ((1 / (((1 : ℕ)) : ℝ)) * (n : ℝ)) = (m : ℝ) := by
            intro n
            obtain ⟨z, hz⟩ := hbγ n
            exact ⟨z, by simpa [dil_eval_apply] using hz⟩
          obtain ⟨m, hm⟩ := Work.BMF.lattice_top_coeff (j := γ.natDegree) (D := 1) (Qm := 1)
            (G := Work.BMF.dil (b : ℝ) γ) le_rfl le_rfl
            (Work.BMF.natDegree_dil_le (b : ℝ) γ) hint
          refine ⟨m, ?_⟩
          simp only [Nat.cast_one, one_mul, one_pow, div_one] at hm
          rw [Work.BMF.coeff_dil] at hm
          linear_combination hm
        -- coprimality of `a^d` and `b^d` leaves `d! * γ.coeff d ∈ ℤ`
        have hC : ∃ M : ℤ, ((γ.natDegree).factorial : ℝ) * γ.coeff γ.natDegree = (M : ℝ) := by
          have hcop : Nat.Coprime (a ^ γ.natDegree) (b ^ γ.natDegree) := hab.pow γ.natDegree γ.natDegree
          refine Work.N8.ExistsIntCoprimeMul (X := ((γ.natDegree).factorial : ℝ) * γ.coeff γ.natDegree) hcop ?_ ?_
          · obtain ⟨m, hm⟩ := hA
            exact ⟨m, by rw [Nat.cast_pow]; linear_combination hm⟩
          · obtain ⟨m, hm⟩ := hB
            exact ⟨m, by rw [Nat.cast_pow]; linear_combination hm⟩
        obtain ⟨M, hM⟩ := hC
        set γ' : ℝ[X] := γ - Polynomial.C (M : ℝ) * Work.BMF.binP γ.natDegree with hγ'def
        have hγ'deg : γ'.natDegree ≤ k := by
          have h1 : γ'.natDegree ≤ γ.natDegree := by
            rw [hγ'def]
            refine le_trans (Polynomial.natDegree_sub_le _ _) (max_le le_rfl ?_)
            exact le_trans (Polynomial.natDegree_C_mul_le _ _)
              (le_of_eq (Work.BMF.binP_natDegree _))
          have h2 : γ'.coeff γ.natDegree = 0 := by
            rw [hγ'def, Polynomial.coeff_sub, Polynomial.coeff_C_mul]
            have hB' := binP_coeff_mul_factorial γ.natDegree
            calc γ.coeff γ.natDegree - M * (Work.BMF.binP γ.natDegree).coeff γ.natDegree
                = γ.coeff γ.natDegree -
                    ((γ.natDegree).factorial * γ.coeff γ.natDegree) *
                      (Work.BMF.binP γ.natDegree).coeff γ.natDegree := by rw [← hM]
              _ = γ.coeff γ.natDegree - γ.coeff γ.natDegree *
                    ((γ.natDegree).factorial *
                      (Work.BMF.binP γ.natDegree).coeff γ.natDegree) := by ring
              _ = 0 := by rw [hB', mul_one, sub_self]
          have h3 := Work.BMF.natDegree_le_sub_one_of h1 h2
          have hk : γ.natDegree - 1 = k := by omega
          rw [hk] at h3
          exact h3
        have hγ'a : Work.BMF.IntegralOn (a : ℝ) γ' := by
          rw [hγ'def]
          exact haγ.sub ((integralOn_of_one (integralOn_one_binP γ.natDegree) a).const_mul M)
        have hγ'b : Work.BMF.IntegralOn (b : ℝ) γ' := by
          rw [hγ'def]
          exact hbγ.sub ((integralOn_of_one (integralOn_one_binP γ.natDegree) b).const_mul M)
        have hres : Work.BMF.IntegralOn 1 γ' := ih γ' hγ'deg hγ'a hγ'b
        have hpeel : Work.BMF.IntegralOn 1
            (Polynomial.C (M : ℝ) * Work.BMF.binP γ.natDegree) :=
          (integralOn_one_binP γ.natDegree).const_mul M
        have hsum : γ = γ' + Polynomial.C (M : ℝ) * Work.BMF.binP γ.natDegree := by
          rw [hγ'def]; ring
        rw [hsum]
        exact hres.add hpeel

/-- **Bezout/gcd closure for lattice-integral polynomials** (MRTTZ Appendix B).
If `γ` has degree `≤ k` and maps both `aℤ` and `bℤ` into `ℤ`, then it maps `gcd a b ℤ` into `ℤ`.

Suggested route: it suffices to treat the case `Nat.Coprime a b` after substituting `t ↦ g t`
(`g = gcd a b`): if `a = g a'`, `b = g b'` and `γ̃(t) = γ(g t)`, then `IntegralOn a γ ↔ IntegralOn a' γ̃`.
For coprime `a b`, induct on `k`: by `Work.BMF.newton_series` applied to `X ↦ γ(a X)` (which is
integer-valued on `ℤ`, degree `≤ k`) one knows `k!·a^k·(γ.coeff k) ∈ ℤ` (for `k = γ.natDegree`; this
also follows from `Work.BMF.lattice_top_coeff` applied to `γ.comp (C a * X)` with `Qm = 1`, `D = 1`),
and likewise `k!·b^k·(γ.coeff k) ∈ ℤ`; coprimality of `a^k` and `b^k` gives `k!·γ.coeff k ∈ ℤ`, so
`γ - C (k!·γ.coeff k) * binP k` has smaller degree, still satisfies both lattice conditions
(`binP k` is integer-valued, so it is integral on `aℤ` and on `bℤ`), and induction applies. -/
theorem IntegralOn_gcd {a b : ℕ} (ha : 0 < a) (hb : 0 < b) {k : ℕ} {γ : Polynomial ℝ}
    (hdeg : γ.natDegree ≤ k) (haγ : Work.BMF.IntegralOn (a : ℝ) γ)
    (hbγ : Work.BMF.IntegralOn (b : ℝ) γ) :
    Work.BMF.IntegralOn ((a.gcd b : ℕ) : ℝ) γ := by
  set g : ℕ := a.gcd b with hg
  have hbpos : 0 < b := hb
  have hgpos : 0 < g := Nat.gcd_pos_of_pos_left b ha
  have hdvdA : g ∣ a := by rw [hg]; exact Nat.gcd_dvd_left a b
  have hdvdB : g ∣ b := by rw [hg]; exact Nat.gcd_dvd_right a b
  have hmulA : g * (a / g) = a := Nat.mul_div_cancel' hdvdA
  have hmulB : g * (b / g) = b := Nat.mul_div_cancel' hdvdB
  have hcop : Nat.Coprime (a / g) (b / g) := by
    rw [hg]
    exact Nat.coprime_div_gcd_div_gcd (Nat.gcd_pos_of_pos_left b ha)
  set γt : ℝ[X] := Work.BMF.dil (g : ℝ) γ with hγt
  have hdegγt : γt.natDegree ≤ k := le_trans (Work.BMF.natDegree_dil_le (g : ℝ) γ) hdeg
  have ht_a : Work.BMF.IntegralOn ((a / g : ℕ) : ℝ) γt := by
    intro n
    obtain ⟨z, hz⟩ := haγ n
    refine ⟨z, ?_⟩
    rw [hγt, dil_eval_apply]
    have hcast : (g : ℝ) * ((a / g : ℕ) : ℝ) = (a : ℝ) := by
      rw [← Nat.cast_mul, hmulA]
    rw [show (g : ℝ) * (((a / g : ℕ) : ℝ) * (n : ℝ)) = (a : ℝ) * (n : ℝ) by
      rw [← mul_assoc, hcast]]
    exact hz
  have ht_b : Work.BMF.IntegralOn ((b / g : ℕ) : ℝ) γt := by
    intro n
    obtain ⟨z, hz⟩ := hbγ n
    refine ⟨z, ?_⟩
    rw [hγt, dil_eval_apply]
    have hcast : (g : ℝ) * ((b / g : ℕ) : ℝ) = (b : ℝ) := by
      rw [← Nat.cast_mul, hmulB]
    rw [show (g : ℝ) * (((b / g : ℕ) : ℝ) * (n : ℝ)) = (b : ℝ) * (n : ℝ) by
      rw [← mul_assoc, hcast]]
    exact hz
  have hres : Work.BMF.IntegralOn 1 γt :=
    coprime_integral (a / g) (b / g) hcop k γt hdegγt ht_a ht_b
  intro n
  obtain ⟨z, hz⟩ := hres n
  refine ⟨z, ?_⟩
  rw [hγt, dil_eval_apply] at hz
  rw [one_mul] at hz
  exact hz

end Work.N8
