import Mathlib
import Submission.Work.BMF.intval_basis

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Newton series for integer-valued polynomials

Every polynomial `γ : ℝ[X]` that is integral on `ℤ` and has degree `≤ k` is a `ℤ`-linear
combination of the binomial-coefficient polynomials `binP i = C(X, i)`, `i = 0, …, k`.

The proof is the classical descending-difference argument: the forward difference
`ΔP = P(X+1) - P` preserves integrality and lowers the degree by one, and a polynomial with
`ΔP = 0` is constant.
-/

namespace Work.BMF

open Polynomial Finset

/-- The forward-difference operator `ΔP = P(X+1) - P`, as a linear map. -/
noncomputable def fwdDiff : ℝ[X] →ₗ[ℝ] ℝ[X] where
  toFun P := P.comp (X + C 1) - P
  map_add' P Q := by
    simp only [add_comp]
    ring
  map_smul' a P := by
    simp only [smul_eq_C_mul, mul_comp, C_comp, RingHom.id_apply]
    ring

/-- `Δ` lowers the binomial polynomial index: `Δ binP (j+1) = binP j`. -/
theorem fwdDiff_binP (j : ℕ) : fwdDiff (binP (j+1)) = binP j := by
  show (binP (j + 1)).comp (X + C 1) - binP (j + 1) = binP j
  rw [binP_comp_succ j]; ring

/-- A polynomial fixed by the translation `X ↦ X+1` is constant. -/
theorem fwdDiff_eq_zero {P : ℝ[X]} (h : fwdDiff P = 0) : P = C (P.eval 0) := by
  have hshift : ∀ x : ℝ, P.eval (x + 1) = P.eval x := by
    intro x
    have := congrArg (Polynomial.eval x) h
    simp only [fwdDiff, LinearMap.coe_mk, AddHom.coe_mk, Polynomial.eval_sub, Polynomial.eval_comp,
      Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_C, Polynomial.eval_zero] at this
    exact sub_eq_zero.mp this
  have hconst : ∀ n : ℕ, P.eval (n : ℝ) = P.eval 0 := by
    intro n
    induction n with
    | zero => norm_num
    | succ n ih => rw [Nat.cast_succ, hshift, ih]
  have hroot : ∀ n : ℕ, (P - C (P.eval 0)).IsRoot (n : ℝ) := by
    intro n
    rw [Polynomial.IsRoot, Polynomial.eval_sub, Polynomial.eval_C, hconst n, sub_self]
  have hQ : P - C (P.eval 0) = 0 := by
    apply eq_zero_of_infinite_isRoot
    apply (Set.infinite_range_of_injective (Nat.cast_injective)).mono
    rintro x ⟨n, rfl⟩
    exact hroot n
  exact sub_eq_zero.mp hQ

/-- The forward difference of an integer-valued polynomial is integer-valued. -/
theorem IntegralOn.fwdDiff {γ : ℝ[X]} (h : IntegralOn 1 γ) : IntegralOn 1 (fwdDiff γ) := by
  intro n
  obtain ⟨m1, hm1⟩ := h (n + 1)
  obtain ⟨m2, hm2⟩ := h n
  refine ⟨m1 - m2, ?_⟩
  show (γ.comp (X + C 1) - γ).eval (1 * (n:ℝ)) = ((m1 - m2 : ℤ) : ℝ)
  simp only [Polynomial.eval_sub, Polynomial.eval_comp, Polynomial.eval_add, Polynomial.eval_X,
    Polynomial.eval_C]
  rw [show (1:ℝ) * (n:ℝ) + 1 = 1 * ((n + 1 : ℤ) : ℝ) by push_cast; ring]
  rw [hm1, hm2]
  push_cast
  ring

/-- **Newton series.** An integer-valued polynomial `γ` of degree `≤ k` is a `ℤ`-linear
combination of `binP 0, …, binP k`. -/
theorem newton_series (k : ℕ) (γ : Polynomial ℝ) (hint : Work.BMF.IntegralOn 1 γ) (hdeg : γ.natDegree ≤ k) :
    ∃ c : ℕ → ℤ, γ = ∑ i ∈ Finset.range (k + 1), Polynomial.C ((c i : ℝ)) * Work.BMF.binP i := by
  induction k generalizing γ with
  | zero =>
      obtain ⟨m, hm⟩ := hint 0
      simp only [Int.cast_zero, mul_zero] at hm
      refine ⟨fun _ => m, ?_⟩
      rw [Finset.sum_range_one, binP_zero, mul_one]
      rw [eq_C_of_natDegree_le_zero hdeg, coeff_zero_eq_eval_zero, hm]
  | succ k ih =>
      have hΔint : IntegralOn 1 (fwdDiff γ) := hint.fwdDiff
      have hΔdeg : (fwdDiff γ).natDegree ≤ k := by
        show (γ.comp (X + C 1) - γ).natDegree ≤ k
        exact natDegree_comp_X_add_one_sub_le hdeg
      obtain ⟨dc, hdc⟩ := ih (fwdDiff γ) hΔint hΔdeg
      obtain ⟨m, hm⟩ := hint 0
      simp only [Int.cast_zero, mul_zero] at hm
      set S : ℝ[X] := ∑ i ∈ range (k+1), C ((dc i : ℝ)) * binP (i+1) with hSdef
      have hS : fwdDiff S = ∑ i ∈ range (k+1), C ((dc i : ℝ)) * binP i := by
        rw [hSdef, map_sum]
        refine Finset.sum_congr rfl fun i hi => ?_
        rw [show C ((dc i : ℝ)) * binP (i+1) = (dc i : ℝ) • binP (i+1) by rw [smul_eq_C_mul]]
        rw [map_smul, fwdDiff_binP, smul_eq_C_mul]
      have hΓ : fwdDiff (γ - S) = 0 := by
        rw [map_sub, hS, hdc, sub_self]
      have hΓc : γ - S = C ((γ - S).eval 0) := fwdDiff_eq_zero hΓ
      have hSev : S.eval 0 = 0 := by
        rw [hSdef, Polynomial.eval_finsetSum]
        refine Finset.sum_eq_zero fun i hi => ?_
        rw [Polynomial.eval_mul, Polynomial.eval_C]
        have hb : Polynomial.eval 0 (binP (i+1)) = 0 := by
          rw [show (0:ℝ) = ((0:ℕ):ℝ) by norm_num, binP_eval_nat,
            Nat.choose_eq_zero_of_lt (Nat.succ_pos i)]
        rw [hb, mul_zero]
      have hΓev : (γ - S).eval 0 = ((m:ℤ):ℝ) := by
        rw [Polynomial.eval_sub, hSev, hm, sub_zero]
      have hg : γ = S + C ((m:ℤ):ℝ) := by
        have h1 : γ - S = C ((m:ℤ):ℝ) := by rw [hΓc, hΓev]
        calc γ = (γ - S) + S := by ring
          _ = C ((m:ℤ):ℝ) + S := by rw [h1]
          _ = S + C ((m:ℤ):ℝ) := by ring
      refine ⟨fun i => Nat.rec m (fun j _ => dc j) i, ?_⟩
      have hsum2 : (∑ i ∈ range (k+2),
            C ((((fun i => Nat.rec m (fun j _ => dc j) i) i : ℤ) : ℝ)) * binP i)
          = S + C ((m:ℤ):ℝ) := by
        rw [Finset.sum_range_succ', hSdef]
        simp only [Nat.rec_zero, binP_zero, mul_one]
      rw [hsum2, hg]

end Work.BMF
