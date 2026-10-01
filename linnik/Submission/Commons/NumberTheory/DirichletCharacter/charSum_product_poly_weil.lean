import Mathlib
import Submission.Commons.NumberTheory.DirichletCharacter.LFunction_conj
import Submission.Commons.NumberTheory.DirichletCharacter.weil_bound_poly

/-!
# Weil's bound for `∑_x χ (f x) * conj (χ (g x))`

The main result of this file,

`Commons.NumberTheory.DirichletCharacter.charSum_product_poly_weil`,

bounds the "correlation" `∑_x χ (f x) * conj (χ (g x))` of two polynomial arguments of a
non-trivial Dirichlet character modulo a prime `p` by `(deg f + deg g) * √p`, for `f, g`
squarefree, coprime and non-constant.

The proof reduces the correlation to a *single* polynomial character sum: since
`χ (b) ^ orderOf χ = 1` for every unit `b`, one has

`χ (f x) * conj (χ (g x)) = χ ((f * g ^ (orderOf χ - 1)) (x))`

pointwise, so the correlation equals `∑_x χ (F x)` with `F = f * g ^ (orderOf χ - 1)`.
Weil's bound for one-variable multiplicative character sums (the Bombieri–Stepanov
theorem, available in the shared commons as
`Commons.NumberTheory.DirichletCharacter.weil_bound_poly`) bounds such a sum by the number
of *distinct* roots of `F` times `√p`; the roots of `F = f * g ^ (orderOf χ - 1)` are the
union of the roots of `f` and of `g`, so there are at most `deg f + deg g` of them.
The hypothesis that `F` is not a constant multiple of an `(orderOf χ)`-th power is checked
separately (`not_const_mul_pow_mul`), using that `f` is squarefree and coprime to `g`.
-/

open Polynomial
open scoped BigOperators

namespace Commons.NumberTheory.DirichletCharacter

/-- For a unit value `b`, the complex conjugate of `χ b` is the inverse of the complex
number `χ b` (both are roots of unity). The value `0` is handled as well, since `0⁻¹ = 0`. -/
private lemma star_char_eq_inv' (p : ℕ) [Fact p.Prime] (χ : DirichletCharacter ℂ p)
    (b : ZMod p) : (starRingEnd ℂ) (χ b) = (χ b)⁻¹ := by
  rcases eq_or_ne b 0 with rfl | hb
  · rw [MulChar.map_zero]; simp
  · obtain ⟨u, rfl⟩ := isUnit_iff_ne_zero.mpr hb
    have hmul : χ ((u : ZMod p)) * (starRingEnd ℂ) (χ ((u : ZMod p))) = 1 := by
      rw [star_apply_char, ← MulChar.mul_apply, mul_inv_cancel, MulChar.one_apply_coe]
    exact eq_inv_of_mul_eq_one_right hmul

/-- Pointwise reduction of the correlation to a single polynomial character sum. -/
private lemma charSum_product_poly_weil_term (p : ℕ) [Fact p.Prime]
    (χ : DirichletCharacter ℂ p) (hχ : χ ≠ 1) (f g : Polynomial (ZMod p)) (x : ZMod p) :
    χ (f.eval x) * (starRingEnd ℂ) (χ (g.eval x))
      = χ ((f * g ^ (orderOf χ - 1)).eval x) := by
  have hm2 : 2 ≤ orderOf χ := by
    have h1 : orderOf χ ≠ 1 := fun h => hχ (orderOf_eq_one_iff.mp h)
    have h2 : 1 ≤ orderOf χ := orderOf_pos χ
    omega
  rw [eval_mul, eval_pow]
  rcases eq_or_ne (g.eval x) 0 with hg0 | hg0
  · rw [hg0]
    simp [MulChar.map_zero, zero_pow (by omega : orderOf χ - 1 ≠ 0)]
  · have hunit : IsUnit (g.eval x) := isUnit_iff_ne_zero.mpr hg0
    rw [map_mul χ (f.eval x) ((g.eval x) ^ (orderOf χ - 1)), map_pow]
    have hpow : (χ (g.eval x)) ^ (orderOf χ - 1) = (χ (g.eval x))⁻¹ := by
      have h1 : (χ (g.eval x)) ^ orderOf χ = 1 := by
        have hp : (χ ^ orderOf χ) = (1 : DirichletCharacter ℂ p) := pow_orderOf_eq_one χ
        have h2 : (χ ^ orderOf χ) (g.eval x) = 1 := by rw [hp, MulChar.one_apply hunit]
        rwa [MulChar.pow_apply' χ (by omega : orderOf χ ≠ 0) (g.eval x)] at h2
      have h2 : (χ (g.eval x)) ^ orderOf χ
          = (χ (g.eval x)) ^ (orderOf χ - 1) * χ (g.eval x) := by
        conv_lhs => rw [show orderOf χ = (orderOf χ - 1) + 1 by omega]
        rw [pow_succ]
      rw [h2] at h1
      exact eq_inv_of_mul_eq_one_left h1
    rw [star_char_eq_inv' p χ (g.eval x), ← hpow]

/-- The distinct roots of `f * g ^ n` are the distinct roots of `f` together with those of
`g`, so there are at most `f.natDegree + g.natDegree` of them. -/
lemma ncard_rootSet_mul_pow_le (p : ℕ) [Fact p.Prime] (f g : Polynomial (ZMod p)) (n : ℕ)
    (hn : 1 ≤ n) :
    ((f * g ^ n).rootSet (AlgebraicClosure (ZMod p))).ncard ≤ f.natDegree + g.natDegree := by
  classical
  set S := AlgebraicClosure (ZMod p) with hS
  by_cases hfg : f * g ^ n = 0
  · rw [hfg, rootSet_zero]; simp
  · have hf0 : f ≠ 0 := fun h => hfg (by rw [h, zero_mul])
    have hgn : g ^ n ≠ 0 := fun h => hfg (by rw [h, mul_zero])
    have hg0 : g ≠ 0 := fun h => hgn (by rw [h, zero_pow (by omega : n ≠ 0)])
    have hsub : (f * g ^ n).rootSet S ⊆ f.rootSet S ∪ g.rootSet S := by
      intro a ha
      rw [mem_rootSet'] at ha
      obtain ⟨_, haev⟩ := ha
      rw [aeval_mul, map_pow (Polynomial.aeval a) g n] at haev
      rcases mul_eq_zero.mp haev with h | h
      · left; rw [mem_rootSet']
        exact ⟨(Polynomial.map_ne_zero_iff
          (FaithfulSMul.algebraMap_injective (ZMod p) S)).mpr hf0, h⟩
      · right; rw [mem_rootSet']
        refine ⟨(Polynomial.map_ne_zero_iff
          (FaithfulSMul.algebraMap_injective (ZMod p) S)).mpr hg0, ?_⟩
        exact (pow_eq_zero_iff (by omega : n ≠ 0)).mp h
    calc ((f * g ^ n).rootSet S).ncard
        ≤ (f.rootSet S ∪ g.rootSet S).ncard :=
          Set.ncard_le_ncard hsub (Set.Finite.union (rootSet_finite f S) (rootSet_finite g S))
      _ ≤ (f.rootSet S).ncard + (g.rootSet S).ncard := Set.ncard_union_le _ _
      _ ≤ f.natDegree + g.natDegree :=
          Nat.add_le_add (ncard_rootSet_le f S) (ncard_rootSet_le g S)

/-- `f * g ^ (m - 1)` is never a constant multiple of an `m`-th power when `m ≥ 2`, `f` is
squarefree of positive degree and `f` is coprime to `g` (with `g` squarefree so that
`g ≠ 0`). -/
lemma not_const_mul_pow_mul (p : ℕ) [Fact p.Prime] (m : ℕ) (hm : 2 ≤ m)
    (f g : Polynomial (ZMod p)) (hf : Squarefree f) (hg : Squarefree g) (hcop : IsCoprime f g)
    (hdf : 1 ≤ f.natDegree) :
    ∀ (c : ZMod p) (H : Polynomial (ZMod p)), f * g ^ (m - 1) ≠ Polynomial.C c * H ^ m := by
  intro c H hcon
  have hf0 : f ≠ 0 := hf.ne_zero
  have hg0 : g ≠ 0 := hg.ne_zero
  have hm1 : m - 1 ≠ 0 := by omega
  have hm0 : m ≠ 0 := by omega
  have hL : f * g ^ (m - 1) ≠ 0 := mul_ne_zero hf0 (pow_ne_zero _ hg0)
  have hc : c ≠ 0 := by
    intro hc; rw [hc, Polynomial.C_0, zero_mul] at hcon; exact hL hcon
  have hHdiv : f ∣ H ^ m := by
    refine ⟨Polynomial.C c⁻¹ * g ^ (m - 1), ?_⟩
    have hcc : H ^ m = Polynomial.C c⁻¹ * (Polynomial.C c * H ^ m) := by
      rw [← mul_assoc, ← Polynomial.C_mul, inv_mul_cancel₀ hc, Polynomial.C_1, one_mul]
    rw [hcc, ← hcon]
    ring
  have hfH : f ∣ H := (hf.dvd_pow_iff_dvd hm0).mp hHdiv
  obtain ⟨K, hK⟩ := hfH
  have h2 : Polynomial.C c * (f * K) ^ m = f * g ^ (m - 1) := by
    conv_lhs => rw [← hK]
    rw [← hcon]
  rw [mul_pow] at h2
  have h3 : f * (Polynomial.C c * f ^ (m - 1) * K ^ m) = f * g ^ (m - 1) := by
    rw [← h2]
    have hfm : (f : Polynomial (ZMod p)) ^ m = f * f ^ (m - 1) := by
      conv_lhs => rw [show m = (m - 1) + 1 by omega]
      rw [pow_succ]; ring
    rw [hfm]; ring
  have hg_eq : g ^ (m - 1) = Polynomial.C c * f ^ (m - 1) * K ^ m :=
    (mul_left_cancel₀ hf0 h3).symm
  have hfdvd : f ^ (m - 1) ∣ g ^ (m - 1) := ⟨Polynomial.C c * K ^ m, by rw [hg_eq]; ring⟩
  have hfdvd' : f ∣ g ^ (m - 1) := dvd_trans (dvd_pow_self f hm1) hfdvd
  have hfg_dvd : f ∣ g := (hf.dvd_pow_iff_dvd hm1).mp hfdvd'
  have hunit : IsUnit f := hcop.isUnit_of_dvd hfg_dvd
  have hle : f.natDegree ≤ 0 := by
    have h1 : f ∣ (1 : Polynomial (ZMod p)) := hunit.dvd
    have h2 := Polynomial.natDegree_le_of_dvd h1 one_ne_zero
    simpa using h2
  omega

theorem charSum_product_poly_weil (p : ℕ) [Fact p.Prime] (χ : DirichletCharacter ℂ p) (hχ : χ ≠ 1)
    (f g : Polynomial (ZMod p)) (hf : Squarefree f) (hg : Squarefree g) (hcop : IsCoprime f g)
    (hd : 1 ≤ f.natDegree) (hg' : 1 ≤ g.natDegree) :
    ‖∑ x : ZMod p, χ (f.eval x) * (starRingEnd ℂ) (χ (g.eval x))‖
      ≤ ((f.natDegree : ℝ) + (g.natDegree : ℝ)) * Real.sqrt (p : ℝ) := by
  have hm2 : 2 ≤ orderOf χ := by
    have h1 : orderOf χ ≠ 1 := fun h => hχ (orderOf_eq_one_iff.mp h)
    have h2 : 1 ≤ orderOf χ := orderOf_pos χ
    omega
  set F := f * g ^ (orderOf χ - 1) with hFdef
  have hf0 : f ≠ 0 := hf.ne_zero
  have hg0 : g ≠ 0 := hg.ne_zero
  have hgn : g ^ (orderOf χ - 1) ≠ 0 := pow_ne_zero _ hg0
  have hF0 : F ≠ 0 := mul_ne_zero hf0 hgn
  have hdegF : 1 ≤ F.natDegree := by
    rw [hFdef, natDegree_mul hf0 hgn, natDegree_pow]
    have h1 : 1 ≤ orderOf χ - 1 := by omega
    nlinarith [hd, hg']
  have hndF : ∀ (c : ZMod p) (H : Polynomial (ZMod p)), F ≠ Polynomial.C c * H ^ orderOf χ := by
    intro c H
    exact not_const_mul_pow_mul p (orderOf χ) hm2 f g hf hg hcop hd c H
  have hb := weil_bound_poly p χ hχ F hF0 hdegF hndF
  have hcard : ((F.rootSet (AlgebraicClosure (ZMod p))).ncard : ℝ)
      ≤ (f.natDegree : ℝ) + (g.natDegree : ℝ) := by
    have h := ncard_rootSet_mul_pow_le p f g (orderOf χ - 1) (by omega)
    have hcast : (((f * g ^ (orderOf χ - 1)).rootSet (AlgebraicClosure (ZMod p))).ncard : ℝ)
        ≤ (f.natDegree : ℝ) + (g.natDegree : ℝ) := by exact_mod_cast h
    exact hcast
  have hcongr : (∑ x : ZMod p, χ (f.eval x) * (starRingEnd ℂ) (χ (g.eval x)))
      = ∑ x : ZMod p, χ (F.eval x) := by
    rw [hFdef]
    exact Finset.sum_congr rfl (fun x _ => charSum_product_poly_weil_term p χ hχ f g x)
  rw [hcongr]
  calc ‖∑ x : ZMod p, χ (F.eval x)‖
      ≤ ((F.rootSet (AlgebraicClosure (ZMod p))).ncard : ℝ) * Real.sqrt (p : ℝ) := hb
    _ ≤ ((f.natDegree : ℝ) + (g.natDegree : ℝ)) * Real.sqrt (p : ℝ) :=
        mul_le_mul_of_nonneg_right hcard (Real.sqrt_nonneg _)

end Commons.NumberTheory.DirichletCharacter
