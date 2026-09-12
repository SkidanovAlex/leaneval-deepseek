import Mathlib
import Submission.Commons.LorentzianPolynomials.S_closed
import Submission.Commons.LorentzianPolynomials.hessian_aeval_eq
import Submission.Commons.LorentzianPolynomials.strict_lorentzian_quadratic_stable
import Submission.Commons.LorentzianPolynomials.strict_subset_L
import Submission.Commons.LorentzianPolynomials.rayleigh_of_hessian_roots_le_one
import Submission.Commons.LorentzianPolynomials.closure_strict_eq_L_of_degree_le_two
import Submission.Commons.LorentzianPolynomials.stable_hessian_posRoots_le_one
import Submission.Commons.LorentzianPolynomials.smul_mem_strict
import Submission.Commons.LinearAlgebra.Matrix.quadReal_hyperplane_negDef
import Submission.Commons.LinearAlgebra.Matrix.quadratic_stable_iff_roots_card_le_one
import Submission.Commons.LorentzianPolynomials.closure_P_eq_S_of_degree_le_one
import Submission.Commons.LorentzianPolynomials.strictLorentzian_preconnected
import Submission.Commons.LinearAlgebra.Matrix.rankOne_sub_posDef_strict
import Submission.Commons.LinearAlgebra.Matrix.negDef_ker_pos_implies_strict
import Submission.Commons.LinearAlgebra.Matrix.strictQuad_preconnected
import Submission.Commons.LinearAlgebra.Matrix.posRoots_card_locallyConstant
import Submission.Commons.LinearAlgebra.Matrix.quadratic_stable_iff_roots_card_le_one

open Finsupp Matrix MvPolynomial UpperHalfPlane Topology Set Filter
open scoped BigOperators
set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option linter.unusedTactic false
set_option maxHeartbeats 400000

namespace Commons.LorentzianPolynomials
namespace WitEx

noncomputable section

/-! # `exists_strict_stable_in_intersection`

For every `n ≥ 1` and degree `d` we exhibit a polynomial which is *strictly
Lorentzian* (`∈ Ŀ n d`) and *stable with nonnegative coefficients* (`∈ S n d`).

Strategy.  Degree `d = 0, 1` are covered by powers of `Σ Xᵢ`.  In degree `2` we take
the quadratic whose Hessian is `3J − I` (a strictly Lorentzian matrix); by
`strict_lorentzian_quadratic_stable` every strict quadratic is stable.

For `d ≥ 2` the witness is `q₂ · (ΣX)^(d−2)` where `q₂` is the strict quadratic
above.  This polynomial has all coefficients positive; stability is inherited from
its factors.  The strict-Lorentzian membership is verified by computing every
`(d−2)`-fold partial derivative: differentiating `q₂ · e^s` (`e = ΣXᵢ`, `s = d−2`)
`d−2` times leaves a quadratic whose Hessian is `m J − I − a⊗1 − 1⊗a` for the
count vector `a` of the differentiation directions and `m = 3 + 6s + 2ΣC(aᵢ,2)
+ 3Σ_{i<j}aᵢaⱼ`, which is a strictly Lorentzian matrix by `jRankTwo_strictQuad`.
-/

/-! ## The vector `(1,…,1)`, powers of `Σ Xᵢ`, and their basic properties -/

/-- the all-ones vector in `Fin n → ℝ` -/
def ones (n : ℕ) : Fin n → ℝ := fun _ => 1

/-- `Σᵢ Xᵢ` in `n` variables. -/
def eSum (n : ℕ) : MvPolynomial (Fin n) ℝ := ∑ i : Fin n, MvPolynomial.X i

lemma eSum_isWeightedHomogeneous_one (n : ℕ) :
    MvPolynomial.IsWeightedHomogeneous (1 : Fin n → ℕ) (eSum n) 1 := by
  unfold eSum
  refine MvPolynomial.IsWeightedHomogeneous.sum Finset.univ
    (fun i : Fin n => MvPolynomial.X i) 1 ?_
  intro i hi
  simpa using (MvPolynomial.isWeightedHomogeneous_X (R := ℝ) (1 : Fin n → ℕ) i)

lemma eSum_isHomogeneous (n d : ℕ) : MvPolynomial.IsHomogeneous ((eSum n) ^ d) d := by
  simpa [MvPolynomial.IsHomogeneous] using
    (MvPolynomial.IsWeightedHomogeneous.pow (w := (1 : Fin n → ℕ))
      (eSum_isWeightedHomogeneous_one n) d)

lemma eSum_aeval (n : ℕ) (z : Fin n → ℂ) :
    MvPolynomial.aeval (R := ℝ) z (eSum n) = ∑ i : Fin n, z i := by
  unfold eSum
  simp

lemma eSum_aeval_upper (n : ℕ) (z : Fin n → ℍ) :
    MvPolynomial.aeval (R := ℝ) (((↑) : ℍ → ℂ) ∘ z) (eSum n) =
      ∑ i : Fin n, ((z i : ℍ) : ℂ) := by
  unfold eSum
  simp

lemma eSum_aeval_pow (n d : ℕ) (z : Fin n → ℂ) :
    MvPolynomial.aeval (R := ℝ) z ((eSum n) ^ d) = (∑ i : Fin n, z i) ^ d := by
  rw [map_pow]
  rw [eSum_aeval]

lemma eSum_aeval_pow_upper (n d : ℕ) (z : Fin n → ℍ) :
    MvPolynomial.aeval (R := ℝ) (((↑) : ℍ → ℂ) ∘ z) ((eSum n) ^ d) =
      (∑ i : Fin n, ((z i : ℍ) : ℂ)) ^ d := by
  rw [map_pow]
  rw [eSum_aeval_upper]

lemma sum_eval_ne_zero_of_pos (n : ℕ) (hn : 0 < n) (z : Fin n → ℍ) :
    (∑ i : Fin n, ((z i : ℍ) : ℂ)) ≠ 0 := by
  haveI : Nonempty (Fin n) := Fin.pos_iff_nonempty.mp hn
  have him : 0 < (∑ i : Fin n, (((z i : ℍ) : ℂ))).im := by
    rw [Complex.im_sum Finset.univ (fun i : Fin n => (((z i : ℍ) : ℂ)))]
    exact Finset.sum_pos (s := Finset.univ) (f := fun i : Fin n => (((z i : ℍ) : ℂ)).im)
      (fun i hi => by simpa using UpperHalfPlane.im_pos (z i)) Finset.univ_nonempty
  intro hzero
  rw [hzero] at him
  norm_num at him

/-- powers of `Σ Xᵢ` are stable (nonvanishing on the upper half plane), for `n ≥ 1`. -/
lemma eSum_pow_stable (n d : ℕ) (hn : 0 < n) :
    IsStable ((eSum n) ^ d) := by
  right
  intro z
  rw [eSum_aeval_pow_upper n d z]
  have hsum : (∑ i : Fin n, (((z i : ℍ) : ℂ))) ≠ 0 := sum_eval_ne_zero_of_pos n hn z
  by_cases hd : d = 0
  · subst d
    simp
  · exact pow_ne_zero d hsum

/-- `pderiv` of a power of `Σ Xᵢ`. -/
lemma eSum_pderiv_pow (n d : ℕ) (i : Fin n) :
    pderiv i ((eSum n) ^ d) = (d : ℝ) • (eSum n) ^ (d - 1) := by
  have hsum_deriv : pderiv i (eSum n) = 1 := by
    unfold eSum
    rw [map_sum]
    simp
  rw [pderiv_pow, hsum_deriv, mul_one]
  rw [← (C_eq_coe_nat (σ := Fin n) (R := ℝ) d), smul_eq_C_mul]
/-- `m.sum (fun _ x => x) = weight 1 m`. -/
private lemma sum_eq_weight_one (n : ℕ) (m : Fin n →₀ ℕ) :
    m.sum (fun _ x => x) = Finsupp.weight (1 : Fin n → ℕ) m := by
  rw [Finsupp.weight_eq_sum]
  rw [Finsupp.sum]
  simp
  exact Finset.sum_subset (Finset.subset_univ m.support) (by
    intro x hx hxnot
    exact Finsupp.notMem_support_iff.mp hxnot)

private lemma multinomial_pos_real (n : ℕ) (m : Fin n →₀ ℕ) : 0 < (m.multinomial : ℝ) := by
  have hpos : 0 < m.multinomial := by
    rw [Finsupp.multinomial_eq]
    exact Nat.multinomial_pos (s := m.support) (f := m)
  exact_mod_cast hpos

/-- coefficients of `(Σ Xᵢ)^d` are positive on every monomial of weight `d`. -/
lemma eSum_pow_mem_P (n d : ℕ) : (⟨(eSum n) ^ d, eSum_isHomogeneous n d⟩ : H n d) ∈ P n d := by
  intro m hm
  have hcoeff := MvPolynomial.coeff_sum_X_pow_of_fintype (R := ℝ) (σ := Fin n) m d
  change 0 < MvPolynomial.coeff m ((eSum n) ^ d)
  unfold eSum
  rw [hcoeff]
  rw [if_pos (by rw [sum_eq_weight_one n m]; simpa using hm)]
  exact multinomial_pos_real n m



namespace esiMath



def ones (n : ℕ) : Fin n → ℝ := fun _ => 1

def countJMat (n : ℕ) (m : ℝ) (a : Fin n → ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  fun i j => m - (if i = j then (1 : ℝ) else 0) - a i - a j

lemma countJMat_symm (n : ℕ) (m : ℝ) (a : Fin n → ℝ) : (countJMat n m a).IsSymm := by
  refine Matrix.IsSymm.ext ?_
  intro i j
  by_cases h : i = j
  · subst j
    simp [countJMat]
  · have hji : j ≠ i := Ne.symm h
    simp [countJMat, h, hji]
    ring

lemma vecMul_countJMat (n : ℕ) (m : ℝ) (a x : Fin n → ℝ) :
    (countJMat n m a) *ᵥ x =
      (fun _ : Fin n => m * (∑ i : Fin n, x i) - (∑ i : Fin n, a i * x i)) - x -
        (∑ i : Fin n, x i) • a := by
  classical
  funext i
  rw [Matrix.mulVec]
  calc
    (∑ j : Fin n, (m - (if i = j then (1 : ℝ) else 0) - a i - a j) * x j)
        = ∑ j : Fin n, ((m - a i) * x j - (if i = j then (1 : ℝ) else 0) * x j - a j * x j) := by
          apply Finset.sum_congr rfl
          intro j hj
          ring
    _ = (∑ j : Fin n, (m - a i) * x j) - (∑ j : Fin n, (if i = j then (1 : ℝ) else 0) * x j)
            - (∑ j : Fin n, a j * x j) := by
          rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib]
    _ = (m - a i) * (∑ j : Fin n, x j) - x i - (∑ j : Fin n, a j * x j) := by
          rw [← Finset.mul_sum]
          simp [Finset.sum_ite_eq']
    _ = (m * (∑ j : Fin n, x j) - (∑ j : Fin n, a j * x j)) - x i - (∑ j : Fin n, x j) * a i := by
          ring

/-- quadReal M x x formula -/
lemma quadReal_countJMat_vv (n : ℕ) (m : ℝ) (a x : Fin n → ℝ) :
    Commons.LinearAlgebra.Matrix.quadReal (countJMat n m a) x x =
      m * (∑ i : Fin n, x i) ^ 2 - (∑ i : Fin n, x i * x i) -
        2 * (∑ i : Fin n, x i) * (∑ i : Fin n, a i * x i) := by
  classical
  rw [Commons.LinearAlgebra.Matrix.quadReal_mulVec]
  rw [vecMul_countJMat]
  dsimp [dotProduct]
  let C : ℝ := m * (∑ j : Fin n, x j) - (∑ j : Fin n, a j * x j)
  have h1 : (∑ i : Fin n, x i * (C - x i - (∑ j : Fin n, x j) * a i))
      = (∑ i : Fin n, (x i * C - x i * x i - x i * ((∑ j : Fin n, x j) * a i))) := by
        apply Finset.sum_congr rfl
        intro i hi
        ring
  have hA' : (∑ i : Fin n, x i * C) = C * (∑ i : Fin n, x i) := by
    rw [← Finset.sum_mul, mul_comm]
  have hC : (∑ i : Fin n, x i * ((∑ j : Fin n, x j) * a i)) =
      (∑ j : Fin n, x j) * (∑ i : Fin n, a i * x i) := by
    calc
      (∑ i : Fin n, x i * ((∑ j : Fin n, x j) * a i))
          = ∑ i : Fin n, (∑ j : Fin n, x j) * (a i * x i) := by
            apply Finset.sum_congr rfl
            intro i hi
            ring
      _ = (∑ j : Fin n, x j) * (∑ i : Fin n, a i * x i) := by
            rw [← Finset.mul_sum]
  have hmain : (∑ i : Fin n, x i * (C - x i - (∑ j : Fin n, x j) * a i))
      = C * (∑ i : Fin n, x i) - (∑ i : Fin n, x i * x i) - (∑ j : Fin n, x j) * (∑ i : Fin n, a i * x i) := by
        rw [h1]
        rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib]
        rw [hA', hC]
  have h2 : C * (∑ i : Fin n, x i) - (∑ i : Fin n, x i * x i) - (∑ j : Fin n, x j) * (∑ i : Fin n, a i * x i)
      = m * (∑ i : Fin n, x i) ^ 2 - (∑ i : Fin n, x i * x i) - 2 * (∑ i : Fin n, x i) * (∑ i : Fin n, a i * x i) := by
        dsimp [C]
        rw [sub_mul, pow_two]
        ring
  change (∑ i : Fin n, x i * (C - x i - (∑ j : Fin n, x j) * a i)) =
      m * (∑ i : Fin n, x i) ^ 2 - (∑ i : Fin n, x i * x i) - 2 * (∑ i : Fin n, x i) * (∑ i : Fin n, a i * x i)
  rw [hmain, h2]

/-- on the hyperplane Σx = 0 the form equals −‖x‖² -/
lemma quadReal_countJMat_zeroSum (n : ℕ) (m : ℝ) (a x : Fin n → ℝ)
    (hx : (∑ i : Fin n, x i) = 0) :
    Commons.LinearAlgebra.Matrix.quadReal (countJMat n m a) x x =
      - (∑ i : Fin n, x i * x i) := by
  rw [quadReal_countJMat_vv]
  rw [hx]
  ring

/-- quadReal A e v formula -/
lemma quadReal_countJMat_ones_v (n : ℕ) (m : ℝ) (a v : Fin n → ℝ) (s : ℝ)
    (hs : (∑ i : Fin n, a i) = s) :
    Commons.LinearAlgebra.Matrix.quadReal (countJMat n m a) (ones n) v =
      ((n : ℝ) * m - s - 1) * (∑ i : Fin n, v i) - (n : ℝ) * (∑ i : Fin n, a i * v i) := by
  classical
  let T : ℝ := ∑ i : Fin n, v i
  let U : ℝ := ∑ i : Fin n, a i * v i
  let C : ℝ := m * T - U
  rw [Commons.LinearAlgebra.Matrix.quadReal_mulVec]
  rw [vecMul_countJMat]
  dsimp [dotProduct, ones]
  simp only [one_mul]
  calc
    (∑ i : Fin n, (m * T - U - v i - T * a i))
        = (∑ i : Fin n, (C - v i - T * a i)) := by
          apply Finset.sum_congr rfl
          intro i hi
          dsimp [C]
    _ = (n : ℝ) * C - (∑ i : Fin n, v i) - T * s := by
          dsimp [T]
          rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib]
          have hC : (∑ i : Fin n, C) = (n : ℝ) * C := by
            simp [Finset.sum_const, Finset.card_univ]
          have hT : (∑ i : Fin n, T * a i) = T * s := by
            rw [← Finset.mul_sum]
            rw [hs]
          rw [hC, hT]
    _ = ((n : ℝ) * m - s - 1) * T - (n : ℝ) * U := by
          dsimp [C, U]
          ring
    _ = ((n : ℝ) * m - s - 1) * (∑ i : Fin n, v i) - (n : ℝ) * (∑ i : Fin n, a i * v i) := by
          rfl

/-- quadReal of the all-ones vector is positive -/
lemma quadReal_countJMat_ones_pos (n : ℕ) (hn : 0 < n) (m : ℝ) (a : Fin n → ℝ) (s : ℝ)
    (hs : (∑ i : Fin n, a i) = s) (hm : 0 < (n : ℝ) * m - 2 * s - 1) :
    0 < Commons.LinearAlgebra.Matrix.quadReal (countJMat n m a) (ones n) (ones n) := by
  rw [quadReal_countJMat_vv]
  simp [ones]
  rw [hs]
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  have h3 : 0 < (↑n : ℝ) * ((↑n : ℝ) * m - 2 * s - 1) := mul_pos hnR hm
  nlinarith

/-- entries of `countJMat` with natural `m, a` are positive -/
lemma countJMat_pos_entries (n m s : ℕ) (a : Fin n → ℕ)
    (hsum : (∑ i : Fin n, a i) = s) (hm : 3 + 6 * s ≤ m) :
    ∀ i j : Fin n, 0 < countJMat n (m : ℝ) (fun i => (a i : ℝ)) i j := by
  intro i j
  have hai : a i ≤ s := by
    rw [← hsum]
    exact Finset.single_le_sum (fun x hx => Nat.zero_le (a x)) (Finset.mem_univ i)
  have haj : a j ≤ s := by
    rw [← hsum]
    exact Finset.single_le_sum (fun x hx => Nat.zero_le (a x)) (Finset.mem_univ j)
  have hm' : (3 : ℝ) + 6 * (s : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have haiR : (a i : ℝ) ≤ (s : ℝ) := by exact_mod_cast hai
  have hajR : (a j : ℝ) ≤ (s : ℝ) := by exact_mod_cast haj
  have hsR0 : 0 ≤ (s : ℝ) := by exact_mod_cast (Nat.zero_le s)
  by_cases h : i = j
  · subst j
    change 0 < (m : ℝ) - (if i = i then (1 : ℝ) else 0) - (a i : ℝ) - (a i : ℝ)
    simp only [if_true]
    nlinarith
  · have hji : j ≠ i := Ne.symm h
    change 0 < (m : ℝ) - (if i = j then (1 : ℝ) else 0) - (a i : ℝ) - (a j : ℝ)
    simp only [h, if_false]
    nlinarith

/-- strictness of `m•J − I − a⊗1 − 1⊗a` for natural `a` with total `s` and `m ≥ 3 + 6s` -/
theorem countJMat_strictQuad (n m s : ℕ) (hn : 0 < n) (a : Fin n → ℕ)
    (hsum : (∑ i : Fin n, a i) = s) (hm : 3 + 6 * s ≤ m) :
    countJMat n (m : ℝ) (fun i => (a i : ℝ)) ∈ Commons.LinearAlgebra.Matrix.strictQuadSet n := by
  classical
  let mR : ℝ := m
  let aR : Fin n → ℝ := fun i => (a i : ℝ)
  let sR : ℝ := s
  let e : Fin n → ℝ := ones n
  let A := countJMat n mR aR
  have hsymm : A.IsSymm := by
    dsimp [A]
    exact countJMat_symm n mR aR
  have hpos : ∀ i j : Fin n, 0 < A i j := by
    dsimp [A, aR, mR]
    exact countJMat_pos_entries n m s a hsum hm
  have hAsumR : (∑ i : Fin n, aR i) = sR := by
    dsimp [aR, sR]
    exact_mod_cast hsum
  have hmR : (3 : ℝ) + 6 * sR ≤ mR := by
    dsimp [mR, sR]
    exact_mod_cast hm
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  have hsR0 : 0 ≤ sR := by
    dsimp [sR]
    exact_mod_cast (Nat.zero_le s)
  have hmBig : 0 ≤ (n : ℝ) * mR - 2 * sR - 2 := by
    have hmposR : 0 ≤ mR := by nlinarith
    have hn1nat : 1 ≤ n := by omega
    have hnm : 0 ≤ (n : ℝ) * mR - mR := by
      have hn1c : (1 : ℝ) ≤ (n : ℝ) := by
        exact_mod_cast (show (1 : ℕ) ≤ n by omega)
      have hn1 : 0 ≤ (n : ℝ) - 1 := by nlinarith
      nlinarith [mul_nonneg hn1 hmposR]
    nlinarith [hmR, hnm]
  -- quadReal A e e > 0
  have hQee : 0 < Commons.LinearAlgebra.Matrix.quadReal A e e := by
    dsimp [A, e, mR, sR]
    apply quadReal_countJMat_ones_pos n hn (m : ℝ) (fun i => (a i : ℝ)) (s : ℝ)
    · exact_mod_cast hsum
    · have hnat1 : (1 : ℕ) ≤ n := by omega
      have hn1c : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hnat1
      have hmR' : (3 : ℝ) + 6 * (s : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
      have hs0 : 0 ≤ (s : ℝ) := by exact_mod_cast (Nat.zero_le s)
      nlinarith
  -- hker
  have hker : ∀ v : Fin n → ℝ, Commons.LinearAlgebra.Matrix.quadReal A e v = 0 →
      v = 0 ∨ Commons.LinearAlgebra.Matrix.quadReal A v v < 0 := by
    intro v hv0
    let T : ℝ := ∑ i : Fin n, v i
    let U : ℝ := ∑ i : Fin n, aR i * v i
    let W : ℝ := ∑ i : Fin n, v i * v i
    have hvv : Commons.LinearAlgebra.Matrix.quadReal A v v = mR * T ^ 2 - W - 2 * T * U := by
      dsimp [A, mR, aR, T, U, W]
      rw [quadReal_countJMat_vv]
    have hev : Commons.LinearAlgebra.Matrix.quadReal A e v =
        ((n : ℝ) * mR - sR - 1) * T - (n : ℝ) * U := by
      dsimp [A, e, T, U, mR, sR]
      exact quadReal_countJMat_ones_v n mR aR v sR hAsumR
    have hrel : T * ((n : ℝ) * mR - 1 - sR) = (n : ℝ) * U := by
      have htmp := hv0
      rw [hev] at htmp
      linarith
    by_cases hvz : v = 0
    · left
      exact hvz
    · right
      have hWpos : 0 < W := by
        dsimp [W]
        have hne : ∃ i : Fin n, v i ≠ 0 := by
          by_contra h
          apply hvz
          funext i
          by_contra hvi
          exact h ⟨i, hvi⟩
        rcases hne with ⟨i, hvi⟩
        exact Finset.sum_pos' (fun j hj => by exact mul_self_nonneg (v j))
          ⟨i, Finset.mem_univ i, by simpa [pow_two] using sq_pos_of_ne_zero hvi⟩
      have hident : (n : ℝ) * Commons.LinearAlgebra.Matrix.quadReal A v v =
          - (T * T) * ((n : ℝ) * mR - 2 * sR - 2) - W * (n : ℝ) := by
        rw [hvv]
        calc
          (n : ℝ) * (mR * T ^ 2 - W - 2 * T * U)
              = (n : ℝ) * mR * T ^ 2 - (n : ℝ) * W - 2 * T * ((n : ℝ) * U) := by ring
          _ = (n : ℝ) * mR * T ^ 2 - (n : ℝ) * W - 2 * T * (T * ((n : ℝ) * mR - 1 - sR)) := by
                rw [hrel]
          _ = - (T * T) * ((n : ℝ) * mR - 2 * sR - 2) - W * (n : ℝ) := by ring
      have hle : Commons.LinearAlgebra.Matrix.quadReal A v v ≤ - W := by
        have hB2 : 0 ≤ (T * T) * ((n : ℝ) * mR - 2 * sR - 2) :=
          mul_nonneg (mul_self_nonneg T) hmBig
        have hq : (n : ℝ) * Commons.LinearAlgebra.Matrix.quadReal A v v ≤ (n : ℝ) * (-W) := by
          rw [hident]
          nlinarith
        exact le_of_mul_le_mul_left hq hnR
      have hneg : - W < 0 := by linarith
      exact lt_of_le_of_lt hle hneg
  have hND := Commons.LinearAlgebra.Matrix.negDef_ker_pos_implies_strict n A hsymm e hQee hker
  -- assemble strictQuadSet
  rw [Commons.LinearAlgebra.Matrix.in_strictQuadSet_iff_sigPos]
  exact ⟨hsymm, hpos, hND.1, by
    rw [Commons.LinearAlgebra.Matrix.sigPos_toQuadraticForm_eq_card_pos_roots A hsymm]
    exact hND.2⟩


end esiMath

/-! ## The candidate family (developed incrementally) -/

/-- iterated partial derivative over a list of indices -/
def pderivL {n : ℕ} : List (Fin n) → MvPolynomial (Fin n) ℝ → MvPolynomial (Fin n) ℝ
| [], p => p
| i :: l, p => pderivL l (pderiv i p)

/-- the count of an index in a list -/
def cnt (n : ℕ) (l : List (Fin n)) (i : Fin n) : ℕ := l.count i

lemma cnt_cons (n : ℕ) (i j : Fin n) (l : List (Fin n)) :
    cnt n (i :: l) j = (if j = i then 1 else 0) + cnt n l j := by
  classical
  by_cases hji : j = i
  · subst j
    simp [cnt]
    omega
  · have hij : i ≠ j := by exact Ne.symm hji
    simp [cnt, hji, hij]

lemma sum_cnt_eq_length (n : ℕ) (l : List (Fin n)) :
    (∑ i : Fin n, cnt n l i) = l.length := by
  classical
  induction l with
  | nil => simp [cnt]
  | cons a l ih =>
      rw [List.length_cons]
      simp only [cnt_cons]
      rw [Finset.sum_add_distrib]
      have h1 : (∑ j : Fin n, (if j = a then 1 else 0)) = 1 := by
        simp [Finset.sum_ite_eq']
      rw [h1]
      omega

/-- the quadratic base: the quadric of the strictly Lorentzian matrix `3J − I`,
as an element of `H n 2`.  Its hessian is `3J − I`. -/
def cand_q2 (n : ℕ) : H n 2 :=
  quadricOfMatrix n (esiMath.countJMat n 3 (fun _ : Fin n => 0))

/-- the base matrix is strictly Lorentzian -/
lemma cand_q2_strictQuad (n : ℕ) (hn : 0 < n) :
    esiMath.countJMat n 3 (fun _ : Fin n => 0) ∈
      Commons.LinearAlgebra.Matrix.strictQuadSet n := by
  simpa using esiMath.countJMat_strictQuad n 3 0 hn (fun _ : Fin n => 0) (by simp) (by norm_num)

/-- hessian of `q₂` is `3J − I`. -/
lemma cand_q2_hessian (n : ℕ) : (cand_q2 n).hessian = esiMath.countJMat n 3 (fun _ : Fin n => 0) := by
  unfold cand_q2
  exact hessian_quadricOfMatrix_symm n (esiMath.countJMat n 3 (fun _ : Fin n => 0))
    (esiMath.countJMat_symm n 3 (fun _ : Fin n => 0))

/-- `q₂` is strictly Lorentzian in degree two. -/
lemma cand_q2_mem_Ŀ (n : ℕ) (hn : 0 < n) : cand_q2 n ∈ Ŀ n 2 := by
  rcases cand_q2_strictQuad n hn with ⟨hsymm, hpos, hunit, hcard⟩
  exact quadricOfMatrix_mem_Ŀ_of_strict n hsymm hpos hunit hcard

/-- `q₂` is stable with nonnegative coefficients. -/
lemma cand_q2_mem_S (n : ℕ) (hn : 0 < n) : cand_q2 n ∈ S n 2 := by
  exact strict_lorentzian_quadratic_subset_S n (cand_q2_mem_Ŀ n hn)

/-- derivative of `q₂` equals the matrix row applied to the variables. -/
lemma cand_pderiv_q2 (n : ℕ) (i : Fin n) :
    pderiv i (cand_q2 n).1 = (3 : ℝ) • (eSum n) - MvPolynomial.X i := by
  classical
  rw [hessian_aeval_eq_pderiv_eq_sum_hessian n (cand_q2 n) i]
  rw [cand_q2_hessian]
  -- now ∑ j, C (countJMat i j) * X j where countJMat entries are 3 − δᵢⱼ
  have hB (j : Fin n) : esiMath.countJMat n 3 (fun _ : Fin n => 0) i j =
      (3 : ℝ) - (if i = j then 1 else 0) := by
    simp [esiMath.countJMat]
  calc
    (∑ j : Fin n, MvPolynomial.C (esiMath.countJMat n 3 (fun _ : Fin n => 0) i j) * MvPolynomial.X j)
        = ∑ j : Fin n, (3 - (if i = j then (1 : ℝ) else 0)) • MvPolynomial.X j := by
          apply Finset.sum_congr rfl
          intro j hj
          rw [hB j]
          rw [smul_eq_C_mul]
    _ = (3 : ℝ) • (∑ j : Fin n, MvPolynomial.X j) - MvPolynomial.X i := by
          calc
            (∑ j : Fin n, (3 - (if i = j then (1 : ℝ) else 0)) • MvPolynomial.X j)
                = ∑ j : Fin n, ((3 : ℝ) • MvPolynomial.X j -
                    (if i = j then (1 : ℝ) else 0) • MvPolynomial.X j) := by
                  apply Finset.sum_congr rfl
                  intro j hj
                  rw [sub_smul]
            _ = (∑ j : Fin n, (3 : ℝ) • MvPolynomial.X j) -
                  (∑ j : Fin n, (if i = j then (1 : ℝ) else 0) • MvPolynomial.X j) := by
                  rw [Finset.sum_sub_distrib]
            _ = (3 : ℝ) • (∑ j : Fin n, MvPolynomial.X j) - MvPolynomial.X i := by
                  rw [Finset.smul_sum]
                  rw [show (∑ j : Fin n, (if i = j then (1 : ℝ) else 0) • MvPolynomial.X j) =
                      MvPolynomial.X i by
                    calc
                      (∑ j : Fin n, (if i = j then (1 : ℝ) else 0) • MvPolynomial.X j)
                          = ∑ j : Fin n, (if i = j then MvPolynomial.X j else 0) := by
                            apply Finset.sum_congr rfl
                            intro j hj
                            by_cases hij : i = j
                            · subst j
                              simp
                            · simp [hij]
                      _ = MvPolynomial.X i := by
                            simp]
    _ = (3 : ℝ) • (eSum n) - MvPolynomial.X i := by rfl

/-- second partial derivatives of a degree-two homogeneous polynomial equal its Hessian
entries, as constants. -/
lemma second_pderiv_eq_C_hessian (n : ℕ) (f : H n 2) (i j : Fin n) :
    pderiv j (pderiv i f.1) = MvPolynomial.C (f.hessian i j) := by
  classical
  rw [hessian_aeval_eq_pderiv_eq_sum_hessian n f i]
  have hsum : (∑ k : Fin n, pderiv j (MvPolynomial.C (f.hessian i k) * MvPolynomial.X k)) =
      MvPolynomial.C (f.hessian i j) := by
    calc
      (∑ k : Fin n, pderiv j (MvPolynomial.C (f.hessian i k) * MvPolynomial.X k))
          = ∑ k : Fin n, (if k = j then MvPolynomial.C (f.hessian i k) else 0) := by
            apply Finset.sum_congr rfl
            intro k hk
            by_cases hkj : k = j
            · subst j
              rw [pderiv_mul, pderiv_C, pderiv_X]
              simp
            · have hj : j ≠ k := Ne.symm hkj
              rw [pderiv_mul, pderiv_C, pderiv_X]
              simp [hkj]
      _ = MvPolynomial.C (f.hessian i j) := by
            simp
  rw [show pderiv j (∑ k : Fin n, MvPolynomial.C (f.hessian i k) * MvPolynomial.X k) =
      ∑ k : Fin n, pderiv j (MvPolynomial.C (f.hessian i k) * MvPolynomial.X k) by
        simp only [map_sum]]
  exact hsum

/-- second-order derivatives of `q₂` are the constants `2` (on the diagonal) and `3`
(off the diagonal). -/
lemma cand_q2_second (n : ℕ) (i j : Fin n) :
    pderiv j (pderiv i (cand_q2 n).1) = MvPolynomial.C (if i = j then (2 : ℝ) else 3) := by
  classical
  rw [second_pderiv_eq_C_hessian n (cand_q2 n) i j]
  rw [cand_q2_hessian]
  congr 1
  by_cases hij : i = j
  · subst i
    simp [esiMath.countJMat]
    ring
  · have hji : j ≠ i := Ne.symm hij
    simp [esiMath.countJMat, hij, hji]

/-- pointwise subtraction lemma for `weight`: `weight (a − b) = weight a − weight b` when `b ≤ a`. -/
lemma weight_sub_eq_sub (n : ℕ) (a b : Fin n →₀ ℕ) (hb : b ≤ a) :
    Finsupp.weight (1 : Fin n → ℕ) (a - b) =
      Finsupp.weight (1 : Fin n → ℕ) a - Finsupp.weight (1 : Fin n → ℕ) b := by
  classical
  have hpoint : ∀ i, b i + (a i - b i) = a i := fun i => by
    rw [Nat.add_comm]
    exact Nat.sub_add_cancel (hb i)
  have hbm : b + (a - b) = a := by
    ext i
    change b i + (a i - b i) = a i
    exact hpoint i
  have hw : Finsupp.weight (1 : Fin n → ℕ) b + Finsupp.weight (1 : Fin n → ℕ) (a - b) =
      Finsupp.weight (1 : Fin n → ℕ) a := by
    have hmap := map_add (Finsupp.weight (1 : Fin n → ℕ)) b (a - b)
    rw [hbm] at hmap
    omega
  omega

/-- a sub-monomial of weight `d` of any monomial of weight at least `d` exists. -/
lemma exists_sub_monomial_weight (n : ℕ) (m : Fin n →₀ ℕ) (d : ℕ)
    (hm : d ≤ Finsupp.weight (1 : Fin n → ℕ) m) :
    ∃ m₁ : Fin n →₀ ℕ, Finsupp.weight (1 : Fin n → ℕ) m₁ = d ∧ m₁ ≤ m := by
  classical
  induction d generalizing m with
  | zero =>
      refine ⟨0, ?_, ?_⟩
      · simp [Finsupp.weight]
      · simp
  | succ d ih =>
      have hD : 1 ≤ Finsupp.weight (1 : Fin n → ℕ) m := by omega
      have hpos : ∃ i : Fin n, 0 < m i := by
        by_contra h
        have hall : ∀ i : Fin n, m i = 0 := by
          intro i
          by_contra hmi
          have : 0 < m i := Nat.pos_of_ne_zero hmi
          exact h ⟨i, this⟩
        have hm0 : m = 0 := by
          ext i
          simp [hall i]
        have hw0 : Finsupp.weight (1 : Fin n → ℕ) m = 0 := by
          rw [hm0]
          simp [Finsupp.weight]
        omega
      rcases hpos with ⟨i, hi⟩
      let m' : Fin n →₀ ℕ := m - Finsupp.single i 1
      have hle' : Finsupp.single i 1 ≤ m := by
        intro x
        by_cases hxi : x = i
        · subst i
          simp
          exact hi
        · simp [hxi]
      have hw' : Finsupp.weight (1 : Fin n → ℕ) m' = Finsupp.weight (1 : Fin n → ℕ) m - 1 := by
        dsimp [m']
        rw [weight_sub_eq_sub n m (Finsupp.single i 1) hle']
        simp [Finsupp.weight_single]
      have hw'2 : d ≤ Finsupp.weight (1 : Fin n → ℕ) m' := by omega
      rcases ih m' hw'2 with ⟨m₁, hw1, hle1⟩
      refine ⟨m₁ + Finsupp.single i 1, ?_, ?_⟩
      · rw [map_add (Finsupp.weight (1 : Fin n → ℕ)), hw1]
        simp [Finsupp.weight_single]
      · intro x
        by_cases hxi : x = i
        · subst i
          rw [Finsupp.add_apply, Finsupp.single_eq_same]
          have h1 : m₁ x ≤ m x - 1 := by
            have hh := hle1 x
            dsimp [m'] at hh
            simpa using hh
          omega
        · rw [Finsupp.add_apply, Finsupp.single_eq_of_ne hxi]
          have h1 : m₁ x ≤ m x := by
            have hh := hle1 x
            dsimp [m'] at hh
            simpa [hxi] using hh
          omega

/-- product of polynomials in `P` stays in `P` -/
lemma mul_mem_P (n d e : ℕ) (f : H n d) (g : H n e)
    (hf : f ∈ P n d) (hg : g ∈ P n e) :
    (⟨f.1 * g.1, by
      have hfdeg : (f.1).IsHomogeneous d := by simpa [MvPolynomial.IsHomogeneous] using f.2
      have hgdeg : (g.1).IsHomogeneous e := by simpa [MvPolynomial.IsHomogeneous] using g.2
      exact (hfdeg.mul hgdeg)⟩ : H n (d + e)) ∈ P n (d + e) := by
  classical
  intro m hm
  -- pick a sub-monomial of `m` of weight `d`
  obtain ⟨m1, hw1, hle1⟩ := exists_sub_monomial_weight n m d (by omega)
  have hw2 : Finsupp.weight (1 : Fin n → ℕ) (m - m1) = e := by
    rw [weight_sub_eq_sub n m m1 hle1, hw1]
    have hm' : Finsupp.weight (1 : Fin n → ℕ) m = d + e := by simpa using hm
    omega
  have hsum_m : m1 + (m - m1) = m := by
    ext i
    rw [Finsupp.add_apply]
    change m1 i + (m i - m1 i) = m i
    rw [Nat.add_comm]
    exact Nat.sub_add_cancel (hle1 i)
  have hpos1 : 0 < MvPolynomial.coeff m1 f.1 := hf m1 hw1
  have hpos2 : 0 < MvPolynomial.coeff (m - m1) g.1 := hg (m - m1) hw2
  -- coefficient of the product as a sum over the antidiagonal
  rw [MvPolynomial.coeff_mul]
  let t : (Fin n →₀ ℕ) × (Fin n →₀ ℕ) → ℝ := fun x =>
    MvPolynomial.coeff x.1 f.1 * MvPolynomial.coeff x.2 g.1
  have hx0 : (m1, m - m1) ∈ Finset.HasAntidiagonal.antidiagonal m := by
    rw [Finset.HasAntidiagonal.mem_antidiagonal]
    exact hsum_m
  have hnonneg : ∀ x ∈ Finset.HasAntidiagonal.antidiagonal m, 0 ≤ t x := by
    intro x hx
    have hxsum : x.1 + x.2 = m := (Finset.HasAntidiagonal.mem_antidiagonal).mp hx
    -- coefficients are nonnegative
    by_cases hxw : Finsupp.weight (1 : Fin n → ℕ) x.1 = d
    · have hposx1 : 0 < MvPolynomial.coeff x.1 f.1 := hf x.1 hxw
      -- weight x.2 = e automatically
      have hxw2 : Finsupp.weight (1 : Fin n → ℕ) x.2 = e := by
        have hm' : Finsupp.weight (1 : Fin n → ℕ) m = d + e := by simpa using hm
        have hwsum : Finsupp.weight (1 : Fin n → ℕ) x.1 + Finsupp.weight (1 : Fin n → ℕ) x.2 =
            Finsupp.weight (1 : Fin n → ℕ) m := by
          rw [← map_add (Finsupp.weight (1 : Fin n → ℕ)) x.1 x.2]
          rw [hxsum]
        omega
      have hposx2 : 0 < MvPolynomial.coeff x.2 g.1 := hg x.2 hxw2
      dsimp [t]
      exact le_of_lt (mul_pos hposx1 hposx2)
    · have hzero1 : MvPolynomial.coeff x.1 f.1 = 0 := by
        exact MvPolynomial.IsWeightedHomogeneous.coeff_eq_zero
          (w := (1 : Fin n → ℕ)) (n := d)
          (by simpa [MvPolynomial.IsHomogeneous] using (f.2)) x.1 hxw
      dsimp [t]
      rw [hzero1]
      simp
  have hterm : t (m1, m - m1) ≤
      ∑ x ∈ Finset.HasAntidiagonal.antidiagonal m, t x := by
    exact Finset.single_le_sum hnonneg hx0
  have hposterm : 0 < t (m1, m - m1) := by
    dsimp [t]
    exact mul_pos hpos1 hpos2
  exact lt_of_lt_of_le hposterm hterm


/-- the candidate `q₂ · (ΣX)^s`, homogeneous of degree `s + 2` -/
def candS (n : ℕ) (s : ℕ) : H n (s + 2) := ⟨(cand_q2 n).1 * (eSum n) ^ s, by
  have hq : ((cand_q2 n).1).IsHomogeneous 2 := by simpa [MvPolynomial.IsHomogeneous] using (cand_q2 n).2
  have he : ((eSum n) ^ s).IsHomogeneous s := by simpa [MvPolynomial.IsHomogeneous] using eSum_isHomogeneous n s
  rw [mem_homogeneousSubmodule]
  have hdeg : 2 + s = s + 2 := by omega
  simpa [hdeg] using hq.mul he⟩

/-- the power `(ΣX)^s` as an element of `H n s` -/
def candPow (n : ℕ) (s : ℕ) : H n s := ⟨(eSum n) ^ s, by
  simpa [MvPolynomial.IsHomogeneous] using eSum_isHomogeneous n s⟩

/-- product of two stable polynomials is stable. -/
lemma mul_stable {n : ℕ} (p q : MvPolynomial (Fin n) ℝ) (hp : IsStable p) (hq : IsStable q) :
    IsStable (p * q) := by
  classical
  rcases hp with hpz | hpst
  · left
    rw [hpz]
    simp
  · rcases hq with hqz | hqst
    · left
      rw [hqz]
      simp
    · right
      intro z
      rw [map_mul]
      exact mul_ne_zero (hpst z) (hqst z)

/-- the candidate lies in `P n (s+2)`. -/
lemma candS_mem_P (n s : ℕ) : candS n s ∈ P n (s + 2) := by
  classical
  have hq : cand_q2 n ∈ P n 2 := by
    unfold cand_q2
    apply quadricOfMatrix_mem_P_of_pos
    intro i j
    by_cases hij : i = j
    · subst j
      simp [esiMath.countJMat]
    · have hji : j ≠ i := Ne.symm hij
      simp [esiMath.countJMat, hij, hji]
  have hp : candPow n s ∈ P n s := eSum_pow_mem_P n s
  have hprod := mul_mem_P n 2 s (cand_q2 n) (candPow n s) hq hp
  intro m hm
  have hm' : Finsupp.weight (1 : Fin n → ℕ) m = 2 + s := by omega
  have hpos : 0 < MvPolynomial.coeff m ((cand_q2 n).1 * (eSum n) ^ s) := by
    simpa [candPow] using hprod m hm'
  simpa [candS] using hpos

/-- the candidate is stable with nonnegative coefficients. -/
lemma candS_mem_S (n s : ℕ) (hn : 0 < n) : candS n s ∈ S n (s + 2) := by
  classical
  constructor
  · change IsStable (candS n s).1
    simp only [candS]
    exact mul_stable (cand_q2 n).1 ((eSum n) ^ s) (cand_q2_mem_S n hn).1 (eSum_pow_stable n s hn)
  · intro m
    by_cases hmw : Finsupp.weight (1 : Fin n → ℕ) m = s + 2
    · exact le_of_lt (candS_mem_P n s m hmw)
    · have hzero : MvPolynomial.coeff m (candS n s).1 = 0 := by
        exact MvPolynomial.IsWeightedHomogeneous.coeff_eq_zero
          (w := (1 : Fin n → ℕ)) (n := s + 2)
          (by simpa [MvPolynomial.IsHomogeneous] using (candS n s).2) m hmw
      rw [hzero]


/-! ## Iterated partial derivatives of the candidate -/

/-- `pderivL` distributes over real scalar multiplication. -/
lemma pderivL_smul {n : ℕ} (l : List (Fin n)) (r : ℝ) (p : MvPolynomial (Fin n) ℝ) :
    pderivL l (r • p) = r • pderivL l p := by
  induction l generalizing r p with
  | nil => simp [pderivL]
  | cons a l ih =>
      simp only [pderivL]
      rw [show pderiv a (r • p) = r • pderiv a p by rw [(pderiv a).map_smul]]
      exact ih r (pderiv a p)

/-- `pderivL` distributes over addition. -/
lemma pderivL_add {n : ℕ} (l : List (Fin n)) (p q : MvPolynomial (Fin n) ℝ) :
    pderivL l (p + q) = pderivL l p + pderivL l q := by
  induction l generalizing p q with
  | nil => simp [pderivL]
  | cons a l ih =>
      simp only [pderivL]
      rw [show pderiv a (p + q) = pderiv a p + pderiv a q by rw [(pderiv a).map_add]]
      exact ih (pderiv a p) (pderiv a q)

/-- the falling product `m·(m−1)⋯(m−t+1)` -/
def fallingProd (m t : ℕ) : ℕ := ∏ r ∈ Finset.range t, (m - r)

lemma fallingProd_zero (m : ℕ) : fallingProd m 0 = 1 := by
  simp [fallingProd]

lemma fallingProd_succ (m t : ℕ) (hm : t < m) :
    fallingProd m (t + 1) = (m - t) * fallingProd m t := by
  simp [fallingProd, Finset.prod_range_succ]
  rw [Nat.mul_comm]

/-- `m!/(m−t)!` as a real number -/
noncomputable def fallReal (m t : ℕ) : ℝ := (Nat.factorial m : ℝ) / (Nat.factorial (m - t) : ℝ)

/-- `pderivL` of a power of `ΣXᵢ` -/
lemma pderivL_eSum_pow (n : ℕ) (l : List (Fin n)) (m : ℕ) (hm : l.length ≤ m) :
    pderivL l ((eSum n) ^ m) = fallReal m l.length • (eSum n) ^ (m - l.length) := by
  classical
  induction l generalizing m with
  | nil =>
      have hf : (Nat.factorial m : ℝ) ≠ 0 := by positivity
      simp [pderivL, fallReal, div_self hf]
  | cons a l ih =>
      simp only [pderivL, List.length_cons]
      have hm' : l.length + 1 ≤ m := by simpa using hm
      have hm1 : 1 ≤ m := by omega
      rw [eSum_pderiv_pow]
      rw [pderivL_smul]
      have hml : l.length ≤ m - 1 := by omega
      have hrec := ih (m - 1) hml
      rw [hrec]
      have hexp : (m - 1) - l.length = m - (l.length + 1) := by omega
      rw [hexp]
      have hscalar : (m : ℝ) * fallReal (m - 1) l.length = fallReal m (l.length + 1) := by
        dsimp [fallReal]
        have hfac : (Nat.factorial m : ℝ) = (m : ℝ) * (Nat.factorial (m - 1) : ℝ) := by
          have hmm : m = (m - 1) + 1 := by omega
          rw [hmm]
          simp only [Nat.factorial_succ]
          norm_num
        have hden : (m - 1) - l.length = m - (l.length + 1) := by omega
        rw [hden]
        have hne : (Nat.factorial (m - 1 - l.length) : ℝ) ≠ 0 := by positivity
        rw [hfac]
        field_simp [hne]
      have hstep : (m : ℝ) • (fallReal (m - 1) l.length • (eSum n) ^ (m - (l.length + 1))) =
          fallReal m (l.length + 1) • (eSum n) ^ (m - (l.length + 1)) := by
        rw [smul_smul, hscalar]
      simpa using hstep


/-! ## `Ŀ`-membership via all top partials -/

/-- the partial derivative as a map between the graded pieces. -/
def pderivH {n : ℕ} {d : ℕ} (i : Fin n) (f : H n (d + 1)) : H n d := ⟨pderiv i f.1, by
  have hf : f.1.IsHomogeneous (d + 1) := by simpa [MvPolynomial.IsHomogeneous] using f.2
  have hd : (d + 1) - 1 = d := by omega
  simpa [hd] using (hf.pderiv (i := i))⟩

/-- iterated partials preserve homogeneity: `pderivL l p` is homogeneous of degree
`m − l.length` when `p` is homogeneous of degree `m`. -/
lemma pderivL_IsHomogeneous {n : ℕ} (l : List (Fin n)) (p : MvPolynomial (Fin n) ℝ) (m : ℕ)
    (hp : p.IsHomogeneous m) (hl : l.length ≤ m) :
    (pderivL l p).IsHomogeneous (m - l.length) := by
  classical
  induction l generalizing p m with
  | nil =>
      simpa [pderivL] using hp
  | cons a l ih =>
      simp only [pderivL, List.length_cons]
      have hl' : l.length + 1 ≤ m := by simpa using hl
      have hm1 : 1 ≤ m := by omega
      have hdp : (pderiv a p).IsHomogeneous (m - 1) := by
        simpa using (hp.pderiv (i := a))
      have hle' : l.length ≤ m - 1 := by omega
      have hres := ih (pderiv a p) (m - 1) hdp hle'
      have hdeg : (m - 1) - l.length = m - (l.length + 1) := by omega
      simpa [hdeg] using hres

/-- the order-`s` partial of `f` (degree `s + 2`) as an element of degree `2`. -/
def partialElem {n : ℕ} (s : ℕ) (l : List (Fin n)) (f : H n (s + 2)) (hl : l.length = s) : H n 2 :=
  ⟨pderivL l f.1, by
    have hf : f.1.IsHomogeneous (s + 2) := by simpa [MvPolynomial.IsHomogeneous] using f.2
    have hdeg := pderivL_IsHomogeneous l f.1 (s + 2) hf (by omega)
    have hfin : (s + 2) - s = 2 := by omega
    simpa [hl, hfin] using hdeg⟩

/-- partial derivatives preserve `P`. -/
lemma pderivH_mem_P (n k : ℕ) (f : H n (k + 1)) (hf : f ∈ P n (k + 1)) (i : Fin n) :
    pderivH (d := k) i f ∈ P n k := by
  classical
  intro m hm
  have hc := MvPolynomial.coeff_pderiv (p := f.1) (i := i) (m := m)
  have hmw : Finsupp.weight (1 : Fin n → ℕ) (m + Finsupp.single i 1) = k + 1 := by
    rw [map_add (Finsupp.weight (1 : Fin n → ℕ)) m (Finsupp.single i 1)]
    rw [Finsupp.weight_single]
    simp [hm]
  have hpos : 0 < MvPolynomial.coeff (m + Finsupp.single i 1) f.1 := hf (m + Finsupp.single i 1) hmw
  change 0 < (pderivH (d := k) i f).1.coeff m
  simp only [pderivH]
  rw [hc]
  positivity

/-- a `P`-element whose every order-`s` partial is strictly Lorentzian is strictly
Lorentzian of degree `s + 2`. -/
lemma Ŀ_of_partials (n s : ℕ) (f : H n (s + 2)) (hP : f ∈ P n (s + 2))
    (hparts : ∀ (l : List (Fin n)) (hl : l.length = s), partialElem s l f hl ∈ Ŀ n 2) :
    f ∈ Ŀ n (s + 2) := by
  classical
  induction s with
  | zero =>
      have hf' : partialElem 0 [] f (by simp) = f := by
        apply Subtype.ext
        simp [partialElem, pderivL]
      rw [← hf']
      exact hparts [] (by simp)
  | succ s ih =>
      -- f : H n ((s+1)+2); want f ∈ Ŀ n ((s+1)+2)
      have hmem : ∀ i : Fin n, (⟨f.1.pderiv i, f.2.pderiv⟩ : H n (s + 2)) ∈ Ŀ n (s + 2) := by
        intro i
        let g : H n (s + 2) := ⟨f.1.pderiv i, f.2.pderiv⟩
        have hgP : g ∈ P n (s + 2) := by
          intro m hm
          have hc := MvPolynomial.coeff_pderiv (p := f.1) (i := i) (m := m)
          have hmw : Finsupp.weight (1 : Fin n → ℕ) (m + Finsupp.single i 1) = (s + 1) + 2 := by
            rw [map_add (Finsupp.weight (1 : Fin n → ℕ)) m (Finsupp.single i 1)]
            rw [Finsupp.weight_single]
            simp [hm]
          have hpos : 0 < MvPolynomial.coeff (m + Finsupp.single i 1) f.1 := hP (m + Finsupp.single i 1) hmw
          change 0 < g.1.coeff m
          dsimp [g]
          rw [hc]
          positivity
        apply ih g hgP
        intro l hl
        have hrel : partialElem s l g hl = partialElem (s + 1) (i :: l) f (by simp [hl]) := by
          apply Subtype.ext
          simp [partialElem, g, pderivL]
        rw [hrel]
        exact hparts (i :: l) (by simp [hl])
      rw [Ŀ]
      exact ⟨hP, hmem⟩



/-! ## The closed forms for iterated partials of `q₂·(ΣX)^s` (×2 form) -/

/-- `Σ` over unordered pairs `i < j` of `aᵢaⱼ` -/
def pairSum {n : ℕ} (a : Fin n → ℕ) : ℕ :=
  ∑ i : Fin n, ∑ j : Fin n, (if i < j then a i * a j else 0)

/-- `2·Σᵢ C(aᵢ,2) + 3·Σ_{i<j} aᵢaⱼ` -/
def candC2 {n : ℕ} (a : Fin n → ℕ) : ℕ :=
  2 * (∑ i : Fin n, Nat.choose (a i) 2) + 3 * pairSum a

/-- the coefficient of the `e²` term in the closed form is a natural number -/
def candM {n : ℕ} (a : Fin n → ℕ) (s : ℕ) : ℕ := 3 + 6 * s + candC2 a

/-- the matrix of the closed form: `candM(a)J − I − a⊗1 − 1⊗a` -/
def candMat {n : ℕ} (a : Fin n → ℕ) (s : ℕ) : Matrix (Fin n) (Fin n) ℝ :=
  fun p q => (candM a s : ℝ) - (if p = q then (1 : ℝ) else 0) - (a p : ℝ) - (a q : ℝ)

/-- the linear form `6e − 2Xᵢ` -/
noncomputable def F (n : ℕ) (i : Fin n) : MvPolynomial (Fin n) ℝ :=
  (6 : ℝ) • (eSum n) - (2 : ℝ) • (MvPolynomial.X i : MvPolynomial (Fin n) ℝ)

/-- `2q₂ + (Σᵢ aᵢ(6e − 2Xᵢ))·e + candC2(a)·e²` -/
noncomputable def candB2 (n : ℕ) (a : Fin n → ℕ) : MvPolynomial (Fin n) ℝ :=
  (2 : ℝ) • (cand_q2 n).1 +
    ((∑ i : Fin n, ((a i : ℕ) : ℝ) • F n i) * (eSum n)) +
    (((candC2 a : ℕ) : ℝ) • ((eSum n) ^ 2))

/-- count increment: `(b + e_a)` as a function -/
def cntInc {n : ℕ} (b : Fin n → ℕ) (a : Fin n) : Fin n → ℕ := fun i => if i = a then b i + 1 else b i

/-- counts of `a :: l` are `cntInc (cnt l) a` -/
lemma cnt_cons_eq_cntInc (n : ℕ) (a : Fin n) (l : List (Fin n)) :
    cnt n (a :: l) = cntInc (cnt n l) a := by
  funext i
  dsimp [cntInc]
  by_cases hia : i = a
  · subst i
    simp [cnt_cons]
    omega
  · simp [cnt_cons, hia]


/-! ## Count arithmetic for the closed form -/

lemma choose_two_succ (k : ℕ) : Nat.choose (k + 1) 2 = Nat.choose k 2 + k := by
  rw [Nat.choose_succ_succ]
  norm_num
  rw [Nat.add_comm]

/-- trichotomy split of a sum at an index -/
private lemma triple_split (n : ℕ) (b : Fin n → ℕ) (a0 : Fin n) :
    (∑ i : Fin n, b i) =
      (∑ i : Fin n, (if i < a0 then b i else 0)) + b a0 +
        (∑ i : Fin n, (if a0 < i then b i else 0)) := by
  classical
  have hsplit : ∀ i : Fin n, b i =
      (if i < a0 then b i else 0) + (if i = a0 then b i else 0) + (if a0 < i then b i else 0) := by
    intro i
    rcases lt_trichotomy i a0 with hi | hi | hi
    · have hia : i ≠ a0 := ne_of_lt hi
      have ha0i : ¬ a0 < i := not_lt_of_gt hi
      simp [hi, hia, ha0i]
    · subst i
      simp
    · have hia : ¬ i < a0 := not_lt_of_ge (le_of_lt hi)
      have hia0 : i ≠ a0 := ne_of_gt hi
      simp [hia, hia0, hi]
  calc
    (∑ i, b i) = ∑ i, ((if i < a0 then b i else 0) + (if i = a0 then b i else 0) + (if a0 < i then b i else 0)) := by
      apply Finset.sum_congr rfl
      intro i hi
      exact hsplit i
    _ = (∑ i, (if i < a0 then b i else 0)) + (∑ i, (if i = a0 then b i else 0)) + (∑ i, (if a0 < i then b i else 0)) := by
      rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
    _ = (∑ i, (if i < a0 then b i else 0)) + b a0 + (∑ i, (if a0 < i then b i else 0)) := by
      have h1 : (∑ i, (if i = a0 then b i else 0)) = b a0 := by simp
      rw [h1]

/-- inner collapse: `Σ_i [i<j ∧ i=a0]·b j = if a0<j then b j else 0` -/
private lemma inner_collapse_1 (n : ℕ) (b : Fin n → ℕ) (a0 j : Fin n) :
    (∑ i : Fin n, (if i < j ∧ i = a0 then b j else 0)) = (if a0 < j then b j else 0) := by
  classical
  calc
    (∑ i : Fin n, (if i < j ∧ i = a0 then b j else 0))
        = ∑ i : Fin n, (if i = a0 then (if a0 < j then b j else 0) else 0) := by
          apply Finset.sum_congr rfl
          intro i hi
          by_cases hia : i = a0
          · subst i
            simp
          · simp [hia]
    _ = (if a0 < j then b j else 0) := by simp

/-- inner collapse: `Σ_j [i<j ∧ j=a0]·b i = if i<a0 then b i else 0` -/
private lemma inner_collapse_2 (n : ℕ) (b : Fin n → ℕ) (a0 i : Fin n) :
    (∑ j : Fin n, (if i < j ∧ j = a0 then b i else 0)) = (if i < a0 then b i else 0) := by
  classical
  calc
    (∑ j : Fin n, (if i < j ∧ j = a0 then b i else 0))
        = ∑ j : Fin n, (if j = a0 then (if i < a0 then b i else 0) else 0) := by
          apply Finset.sum_congr rfl
          intro j hj
          by_cases hja : j = a0
          · subst j
            simp
          · simp [hja]
    _ = (if i < a0 then b i else 0) := by simp

/-- pair sum changes by `t − b a` when `a` is incremented (with total `t`). -/
lemma pairSum_cntInc {n : ℕ} (b : Fin n → ℕ) (a0 : Fin n) (t : ℕ)
    (ht : (∑ i : Fin n, b i) = t) :
    pairSum (cntInc b a0) = pairSum b + (t - b a0) := by
  classical
  calc
    pairSum (cntInc b a0)
        = ∑ i : Fin n, ∑ j : Fin n, (if i < j then (cntInc b a0 i) * (cntInc b a0 j) else 0) := by rfl
    _ = ∑ i : Fin n, ∑ j : Fin n, ((if i < j then b i * b j else 0)
              + (if i < j ∧ i = a0 then b j else 0)
              + (if i < j ∧ j = a0 then b i else 0)) := by
          apply Finset.sum_congr rfl
          intro i hi
          apply Finset.sum_congr rfl
          intro j hj
          by_cases hij : i < j
          · simp only [hij, if_true]
            by_cases h1 : i = a0
            · by_cases h2 : j = a0
              · exfalso
                have : i = j := by rw [h1, h2]
                exact not_lt_of_ge (le_of_eq this.symm) hij
              · subst i
                simp [cntInc, h2]
                ring
            · by_cases h2 : j = a0
              · subst j
                simp [cntInc, h1]
                ring
              · simp [cntInc, h1, h2]
          · simp [hij]
    _ = (∑ i : Fin n, ∑ j : Fin n, (if i < j then b i * b j else 0))
          + (∑ j : Fin n, (if a0 < j then b j else 0))
          + (∑ i : Fin n, (if i < a0 then b i else 0)) := by
          simp_rw [Finset.sum_add_distrib]
          have hT1 : (∑ i : Fin n, ∑ j : Fin n, (if i < j ∧ i = a0 then b j else 0)) =
              ∑ j : Fin n, (if a0 < j then b j else 0) := by
            calc
              (∑ i : Fin n, ∑ j : Fin n, (if i < j ∧ i = a0 then b j else 0))
                  = ∑ j : Fin n, ∑ i : Fin n, (if i < j ∧ i = a0 then b j else 0) := by
                    rw [Finset.sum_comm]
              _ = ∑ j : Fin n, (if a0 < j then b j else 0) := by
                    apply Finset.sum_congr rfl
                    intro j hj
                    exact inner_collapse_1 n b a0 j
          have hT2 : (∑ i : Fin n, ∑ j : Fin n, (if i < j ∧ j = a0 then b i else 0)) =
              ∑ i : Fin n, (if i < a0 then b i else 0) := by
            apply Finset.sum_congr rfl
            intro i hi
            exact inner_collapse_2 n b a0 i
          rw [hT1, hT2]
    _ = pairSum b + (t - b a0) := by
          have htriple := triple_split n b a0
          have htriple' : t = (∑ i, (if i < a0 then b i else 0)) + b a0 + (∑ i, (if a0 < i then b i else 0)) := by
            rw [← ht]
            exact htriple
          have hsub : t - b a0 = (∑ i, (if i < a0 then b i else 0)) + (∑ i, (if a0 < i then b i else 0)) := by omega
          rw [hsub]
          simp only [pairSum]
          omega

/-- `candC2` changes by `3t − b a` when `a` is incremented. -/
lemma candC2_cntInc {n : ℕ} (b : Fin n → ℕ) (a0 : Fin n) (t : ℕ)
    (ht : (∑ i : Fin n, b i) = t) :
    candC2 (cntInc b a0) = candC2 b + (3 * t - b a0) := by
  classical
  have hchoose : (∑ i : Fin n, Nat.choose (cntInc b a0 i) 2) =
      (∑ i : Fin n, Nat.choose (b i) 2) + b a0 := by
    calc
      (∑ i : Fin n, Nat.choose (cntInc b a0 i) 2)
          = ∑ i : Fin n, (Nat.choose (b i) 2 + (if i = a0 then b a0 else 0)) := by
            apply Finset.sum_congr rfl
            intro i hi
            by_cases hia : i = a0
            · subst i
              simp [cntInc, choose_two_succ]
            · simp [cntInc, hia]
      _ = (∑ i : Fin n, Nat.choose (b i) 2) + (∑ i : Fin n, (if i = a0 then b a0 else 0)) := by
            rw [Finset.sum_add_distrib]
      _ = (∑ i : Fin n, Nat.choose (b i) 2) + b a0 := by
            have h1 : (∑ i : Fin n, (if i = a0 then b a0 else 0)) = b a0 := by simp
            rw [h1]
  have hle : b a0 ≤ t := by
    have hs := Finset.single_le_sum (fun x hx => Nat.zero_le (b x)) (Finset.mem_univ a0)
    rw [ht] at hs
    exact hs
  dsimp [candC2]
  rw [hchoose]
  rw [pairSum_cntInc b a0 t ht]
  omega

/-- total count increments by one -/
lemma sum_cntInc {n : ℕ} (b : Fin n → ℕ) (a : Fin n) :
    (∑ i : Fin n, cntInc b a i) = (∑ i : Fin n, b i) + 1 := by
  classical
  calc
    (∑ i : Fin n, cntInc b a i)
        = ∑ i : Fin n, (b i + (if i = a then 1 else 0)) := by
          apply Finset.sum_congr rfl
          intro i hi
          by_cases hia : i = a
          · subst i
            simp [cntInc]
          · simp [cntInc, hia]
    _ = (∑ i : Fin n, b i) + (∑ i : Fin n, (if i = a then 1 else 0)) := by
          rw [Finset.sum_add_distrib]
    _ = (∑ i : Fin n, b i) + 1 := by
          have h1 : (∑ i : Fin n, (if i = a then 1 else 0)) = 1 := by simp
          rw [h1]

/-! ## Increment laws for the ×2 closed form -/

lemma sumF_cntInc {n : ℕ} (b : Fin n → ℕ) (a0 : Fin n) :
    (∑ i : Fin n, (((cntInc b a0 i : ℕ) : ℝ) • F n i)) =
      (∑ i : Fin n, (((b i : ℕ) : ℝ) • F n i)) + F n a0 := by
  classical
  calc
    (∑ i : Fin n, (((cntInc b a0 i : ℕ) : ℝ) • F n i))
        = ∑ i : Fin n, (((b i : ℕ) : ℝ) • F n i + (if i = a0 then (1 : ℝ) else 0) • F n i) := by
          apply Finset.sum_congr rfl
          intro i hi
          by_cases hia : i = a0
          · subst i
            simp [cntInc]
            rw [add_smul]
            rw [one_smul]
          · simp [cntInc, hia]
    _ = (∑ i : Fin n, (((b i : ℕ) : ℝ) • F n i)) + (∑ i : Fin n, ((if i = a0 then (1 : ℝ) else 0) • F n i)) := by
          rw [Finset.sum_add_distrib]
    _ = (∑ i : Fin n, (((b i : ℕ) : ℝ) • F n i)) + F n a0 := by
          have h1 : (∑ i : Fin n, ((if i = a0 then (1 : ℝ) else 0) • F n i)) = F n a0 := by
            calc
              (∑ i : Fin n, ((if i = a0 then (1 : ℝ) else 0) • F n i))
                  = ∑ i : Fin n, (if i = a0 then F n a0 else 0) := by
                    apply Finset.sum_congr rfl
                    intro i hi
                    by_cases hia : i = a0
                    · subst i
                      simp
                    · simp [hia]
              _ = F n a0 := by simp
          simpa using h1

lemma candB2_cntInc {n : ℕ} (b : Fin n → ℕ) (a0 : Fin n) (t : ℕ)
    (ht : (∑ i : Fin n, b i) = t) :
    candB2 n (cntInc b a0) =
      candB2 n b + (F n a0 * eSum n) + (((3 * t - b a0 : ℕ) : ℕ) : ℝ) • ((eSum n) ^ 2) := by
  classical
  unfold candB2
  have hm : (∑ i : Fin n, (((cntInc b a0 i : ℕ) : ℝ) • F n i)) * eSum n =
      (∑ i : Fin n, (((b i : ℕ) : ℝ) • F n i)) * eSum n + F n a0 * eSum n := by
    rw [sumF_cntInc b a0]
    rw [add_mul]
  have hc2 : (candC2 (cntInc b a0) : ℝ) • ((eSum n) ^ 2) =
      (candC2 b : ℝ) • ((eSum n) ^ 2) + (((3 * t - b a0 : ℕ) : ℕ) : ℝ) • ((eSum n) ^ 2) := by
    rw [candC2_cntInc b a0 t ht]
    rw [Nat.cast_add]
    rw [add_smul]
  rw [hm, hc2]
  abel

/-- `pderiv` of `X a0 · e^m`: expanding the product rule. -/
private lemma pderiv_F_mul_pow (n : ℕ) (a a0 : Fin n) (m : ℕ) :
    pderiv a (MvPolynomial.X a0 * (eSum n) ^ m) =
      (if a0 = a then (1 : ℝ) else 0) • (eSum n) ^ m +
        (m : ℝ) • (MvPolynomial.X a0 * (eSum n) ^ (m - 1)) := by
  classical
  rw [pderiv_mul]
  rw [eSum_pderiv_pow n m a]
  by_cases ha : a0 = a
  · subst a0
    simp [one_smul]
  · have hd : pderiv a (MvPolynomial.X a0 : MvPolynomial (Fin n) ℝ) = 0 := by
      simpa using (pderiv_X_of_ne (σ := Fin n) (R := ℝ) (i := a) (j := a0) ha)
    rw [hd]
    simp only [ha, zero_mul, zero_add, ite_false, zero_smul]
    rw [mul_comm (MvPolynomial.X a0), smul_mul_assoc]
    rw [mul_comm (eSum n ^ (m - 1))]

/-- `pderivL l` of `X a0 · e^m`: exactly one derivative of index `a0` can hit the linear
factor, contributing `cnt n l a0` times the derivative of the power only. -/
lemma pderivL_X_mul_pow (n : ℕ) (l : List (Fin n)) (a0 : Fin n) (m : ℕ) (hm : l.length ≤ m) :
    pderivL l (MvPolynomial.X a0 * (eSum n) ^ m) =
      fallReal m l.length • (MvPolynomial.X a0 * (eSum n) ^ (m - l.length)) +
        ((cnt n l a0 : ℕ) : ℝ) • (fallReal m (l.length - 1) • (eSum n) ^ (m + 1 - l.length)) := by
  classical
  induction l generalizing m with
  | nil =>
      simp [pderivL, cnt]
      have hf : fallReal m 0 = 1 := by
        dsimp [fallReal]
        have hne : (Nat.factorial m : ℝ) ≠ 0 := by positivity
        field_simp [hne]
      simp [hf]
  | cons a l ih =>
      simp only [pderivL, List.length_cons]
      have hm' : l.length + 1 ≤ m := by simpa using hm
      have hm1 : 1 ≤ m := by omega
      have hml : l.length ≤ m - 1 := by omega
      have hmlm : l.length ≤ m := by omega
      rw [pderiv_F_mul_pow n a a0 m]
      rw [pderivL_add]
      rw [pderivL_smul]
      rw [pderivL_eSum_pow n l m hmlm]
      rw [pderivL_smul]
      have hrec := ih (m - 1) hml
      rw [hrec]
      have hexp1 : (m - 1) - l.length = m - (l.length + 1) := by omega
      have hexp2 : (m - 1) + 1 - l.length = m - l.length := by omega
      rw [hexp1, hexp2]
      rw [smul_add]
      simp only [smul_smul]
      have hL1 : (l.length + 1) - 1 = l.length := by omega
      have hL2 : m + 1 - (l.length + 1) = m - l.length := by omega
      rw [hL1, hL2]
      have hcntN : cnt n (a :: l) a0 = (if a0 = a then 1 else 0) + cnt n l a0 := by
        rw [cnt_cons n a a0 l]
      have hcnt : (cnt n (a :: l) a0 : ℝ) =
          ((if a0 = a then (1 : ℕ) else 0) : ℝ) + (cnt n l a0 : ℝ) := by
        exact_mod_cast hcntN
      have hscalarX : (m : ℝ) * fallReal (m - 1) l.length = fallReal m (l.length + 1) := by
        dsimp [fallReal]
        have hfac : (Nat.factorial m : ℝ) = (m : ℝ) * (Nat.factorial (m - 1) : ℝ) := by
          have hmm : m = (m - 1) + 1 := by omega
          rw [hmm]
          simp only [Nat.factorial_succ]
          norm_num
        have hden : (m - 1) - l.length = m - (l.length + 1) := by omega
        rw [hden]
        have hne : (Nat.factorial (m - (l.length + 1)) : ℝ) ≠ 0 := by positivity
        rw [hfac]
        field_simp [hne]
      have hscalarE : (m : ℝ) * ((cnt n l a0 : ℝ) * fallReal (m - 1) (l.length - 1)) =
          (cnt n l a0 : ℝ) * fallReal m l.length := by
        by_cases hlen0 : l.length = 0
        · have hl0 : l = [] := List.length_eq_zero_iff.mp hlen0
          rw [hl0]
          simp [cnt]
        · have hlen1 : 1 ≤ l.length := by omega
          have hfacm : (Nat.factorial m : ℝ) = (m : ℝ) * (Nat.factorial (m - 1) : ℝ) := by
            have hmm : m = (m - 1) + 1 := by omega
            rw [hmm]
            simp only [Nat.factorial_succ]
            norm_num
          have hsc : (m : ℝ) * fallReal (m - 1) (l.length - 1) = fallReal m l.length := by
            dsimp [fallReal]
            have hden : (m - 1) - (l.length - 1) = m - l.length := by omega
            rw [hden]
            have hne : (Nat.factorial (m - l.length) : ℝ) ≠ 0 := by positivity
            rw [hfacm]
            field_simp [hne]
          rw [show (m : ℝ) * ((cnt n l a0 : ℝ) * fallReal (m - 1) (l.length - 1)) =
              (cnt n l a0 : ℝ) * ((m : ℝ) * fallReal (m - 1) (l.length - 1)) by ring]
          rw [hsc]
      have hdelta : ((if a0 = a then (1 : ℕ) else 0) : ℝ) = (if a0 = a then (1 : ℝ) else 0) := by
        by_cases ha : a0 = a
        · subst a0; norm_num
        · simp [ha]
      conv_lhs =>
        rw [hscalarX]
        rw [hscalarE]
      rw [← hdelta]
      rw [hcnt]
      conv_rhs =>
        rw [add_mul]
        rw [add_smul]
      abel

private lemma smul_mul_out {n : ℕ} (x y : MvPolynomial (Fin n) ℝ) (r : ℝ) :
    x * (r • y) = r • (x * y) := by
  rw [mul_comm x, smul_mul_assoc, mul_comm y x]

lemma test_q2der (n : ℕ) (i : Fin n) (s : ℕ) :
    pderiv i ((cand_q2 n).1 * (eSum n) ^ (s + 1)) =
      (3 : ℝ) • (eSum n) ^ (s + 2) - (MvPolynomial.X i * (eSum n) ^ (s + 1)) +
        ((s + 1 : ℕ) : ℝ) • ((cand_q2 n).1 * (eSum n) ^ s) := by
  rw [pderiv_mul]
  rw [cand_pderiv_q2]
  rw [eSum_pderiv_pow n (s + 1) i]
  have hexp : (s + 1) - 1 = s := by omega
  rw [hexp]
  rw [smul_mul_out (cand_q2 n).1 (eSum n ^ s) ((s + 1 : ℕ) : ℝ)]
  rw [sub_mul]
  rw [smul_mul_assoc]
  rw [mul_comm (eSum n) (eSum n ^ (s + 1))]
  rw [← pow_succ]

-- base case check
example (n : ℕ) :
    (2 : ℝ) • pderivL ([] : List (Fin n)) ((cand_q2 n).1 * (eSum n) ^ ([] : List (Fin n)).length) =
      (Nat.factorial ([] : List (Fin n)).length : ℝ) • candB2 n (cnt n ([] : List (Fin n))) := by
  simp [pderivL, cnt]
  unfold candB2
  simp [F, cnt, candC2, pairSum]

private lemma pderivL_sub {n : ℕ} (l : List (Fin n)) (p q : MvPolynomial (Fin n) ℝ) :
    pderivL l (p - q) = pderivL l p - pderivL l q := by
  induction l generalizing p q with
  | nil => simp [pderivL]
  | cons a l ih =>
      simp only [pderivL]
      rw [show pderiv a (p - q) = pderiv a p - pderiv a q by rw [(pderiv a).map_sub]]
      exact ih (pderiv a p) (pderiv a q)

lemma closedFormA (n : ℕ) (l : List (Fin n)) :
    (2 : ℝ) • pderivL l ((cand_q2 n).1 * (eSum n) ^ l.length) =
      (Nat.factorial l.length : ℝ) • candB2 n (cnt n l) := by
  classical
  induction l with
  | nil =>
      simp [pderivL, cnt]
      unfold candB2
      simp [F, cnt, candC2, pairSum]
  | cons i l' ih =>
      -- LHS: unfold pderivL (i::l') and the length
      simp only [pderivL, List.length_cons]
      -- expand the inner single derivative of q₂·e^{s+1}
      rw [test_q2der n i l'.length]
      rw [pderivL_add]
      rw [pderivL_sub]
      -- pull the scalar smuls out of pderivL
      rw [pderivL_smul]
      rw [pderivL_smul]
      -- expand e-power and X·e-power derivatives (M3b, L2)
      rw [pderivL_X_mul_pow n l' i (l'.length + 1) (by omega)]
      rw [pderivL_eSum_pow n l' (l'.length + 2) (by omega)]
      -- apply IH to the q₂·e^s term
      have hE1 : l'.length + 2 - l'.length = 2 := by omega
      have hE2 : l'.length + 1 - l'.length = 1 := by omega
      have hE3 : l'.length + 1 + 1 - l'.length = 2 := by omega
      rw [hE1, hE2]
      simp only [smul_smul]
      -- now handle the (s+1)•C piece: bring factor 2 next to C via IH
      have hsc_comm : (2 : ℝ) • (((l'.length + 1 : ℕ) : ℝ) • pderivL l' ((cand_q2 n).1 * (eSum n) ^ l'.length)) =
          ((l'.length + 1 : ℕ) : ℝ) • ((2 : ℝ) • pderivL l' ((cand_q2 n).1 * (eSum n) ^ l'.length)) := by
        rw [smul_smul, smul_smul]
        ring
      -- distribute the outer scalar 2 through the sum
      rw [smul_add]
      rw [hsc_comm]
      rw [ih]
      rw [smul_smul]
      -- now expand the remaining first summand 2•(A − (B1+B2))
      rw [smul_sub]
      rw [smul_add]
      rw [smul_smul]
      rw [smul_smul]
      rw [smul_smul]
      rw [pow_one]
      -- ---- scalar facts ----
      have hfr1 : fallReal (l'.length + 1) l'.length = (Nat.factorial (l'.length + 1) : ℝ) := by
        dsimp [fallReal]
        have hsub : (l'.length + 1) - l'.length = 1 := by omega
        rw [hsub]
        norm_num
      have hfacS : ((Nat.factorial (l'.length + 1) : ℕ) : ℝ) =
          ((l'.length + 1 : ℕ) : ℝ) * (Nat.factorial l'.length : ℝ) := by
        rw [Nat.factorial_succ]
        norm_num
      have hfacS2 : ((l'.length + 1 : ℕ) : ℝ) * (Nat.factorial l'.length : ℝ) =
          (Nat.factorial (l'.length + 1) : ℝ) := by
        rw [Nat.factorial_succ]
        norm_num
      have hfr2 : 6 * fallReal (l'.length + 2) l'.length =
          (3 * (l'.length + 2 : ℕ) : ℝ) * (Nat.factorial (l'.length + 1) : ℝ) := by
        dsimp [fallReal]
        have hfac : (Nat.factorial (l'.length + 2) : ℝ) =
            ((l'.length + 2 : ℕ) : ℝ) * (Nat.factorial (l'.length + 1) : ℝ) := by
          have hmm : l'.length + 2 = (l'.length + 1) + 1 := by omega
          rw [hmm]
          rw [Nat.factorial_succ]
          norm_num
        have hden : (l'.length + 2) - l'.length = 2 := by omega
        rw [hden]
        have hne : (Nat.factorial 2 : ℝ) ≠ 0 := by norm_num
        rw [hfac]
        field_simp [hne]
        ring
      have hfr2c : 2 * (3 * fallReal (l'.length + 2) l'.length) =
          (3 * (l'.length + 2 : ℕ) : ℝ) * (Nat.factorial (l'.length + 1) : ℝ) := by
        nlinarith [hfr2]
      have hcntl : cnt n (i :: l') = cntInc (cnt n l') i := cnt_cons_eq_cntInc n i l'
      have hsuml : (∑ k : Fin n, cnt n l' k) = l'.length := sum_cnt_eq_length n l'
      have hB2inc := candB2_cntInc (cnt n l') i l'.length hsuml
      have hFexp : F n i * eSum n = (6 : ℝ) • ((eSum n) ^ 2) - (2 : ℝ) • (MvPolynomial.X i * eSum n) := by
        unfold F
        rw [sub_mul]
        rw [smul_mul_assoc]
        rw [← pow_two]
        rw [mul_comm (MvPolynomial.X i) (eSum n), smul_mul_assoc]
        rw [mul_comm (eSum n) (MvPolynomial.X i)]
      -- expand RHS
      conv_rhs =>
        rw [hcntl]
        rw [hB2inc]
        rw [smul_add]
        rw [smul_add]
        rw [hFexp]
        rw [smul_sub]
        rw [smul_smul]
        rw [smul_smul]
        rw [smul_smul]
      -- normalize LHS coefficient products
      conv_lhs =>
        rw [show 2 * (3 * fallReal (l'.length + 2) l'.length) =
            6 * fallReal (l'.length + 2) l'.length by ring]
        rw [show 2 * (↑(cnt n l' i) * fallReal (l'.length + 1) (l'.length - 1)) =
            (↑(cnt n l' i) : ℝ) * (2 * fallReal (l'.length + 1) (l'.length - 1)) by ring]
        rw [show 2 * fallReal (l'.length + 1) l'.length =
            2 * (Nat.factorial (l'.length + 1) : ℝ) by rw [hfr1]]
        rw [show ((l'.length + 1 : ℕ) : ℝ) * (Nat.factorial l'.length : ℝ) =
            (Nat.factorial (l'.length + 1) : ℝ) by exact hfacS2]
      -- e² coefficient scalar equality (LHS vs RHS), the only remaining nontrivial part
      have he2scalar : 6 * fallReal (l'.length + 2) l'.length
          - (↑(cnt n l' i) * (2 * fallReal (l'.length + 1) (l'.length - 1))) =
          (Nat.factorial (l'.length + 1) : ℝ) * 6
            + (Nat.factorial (l'.length + 1) : ℝ) * (↑(3 * l'.length - cnt n l' i) : ℝ) := by
        by_cases hs0 : l'.length = 0
        · have hl0 : l' = [] := List.length_eq_zero_iff.mp hs0
          subst l'
          simp [cnt]
          dsimp [fallReal]
          norm_num
        · have hs1 : 1 ≤ l'.length := by omega
          have hcntle : cnt n l' i ≤ 3 * l'.length := by
            have hle : cnt n l' i ≤ l'.length := by
              have hs2 := Finset.single_le_sum (fun x hx => Nat.zero_le (cnt n l' x)) (Finset.mem_univ i)
              rw [hsuml] at hs2
              exact hs2
            omega
          have hΔ : (↑(3 * l'.length - cnt n l' i) : ℝ) =
              3 * (l'.length : ℝ) - (cnt n l' i : ℝ) := by
            rw [Nat.cast_sub hcntle]
            norm_num
          have hfr0 : 2 * fallReal (l'.length + 1) (l'.length - 1) =
              (Nat.factorial (l'.length + 1) : ℝ) := by
            dsimp [fallReal]
            have hden : (l'.length + 1) - (l'.length - 1) = 2 := by omega
            rw [hden]
            have hne : (Nat.factorial (l'.length + 1) : ℝ) ≠ 0 := by positivity
            field_simp [hne]
            norm_num
          have hcast : (3 * (l'.length + 2 : ℕ) : ℝ) = 3 * (l'.length : ℝ) + 6 := by
            norm_num
            ring
          rw [hfr2, hfr0, hΔ]
          rw [hcast]
          ring
      set E2 : MvPolynomial (Fin n) ℝ := eSum n ^ 2
      set XE : MvPolynomial (Fin n) ℝ := MvPolynomial.X i * eSum n
      set CB : MvPolynomial (Fin n) ℝ := candB2 n (cnt n l')
      -- LHS: regroup so the two e² terms are adjacent, then combine them
      have hL : (6 * fallReal (l'.length + 2) l'.length) • E2 -
            (((2 * (Nat.factorial (l'.length + 1) : ℝ)) • XE) +
              ((↑(cnt n l' i) * (2 * fallReal (l'.length + 1) (l'.length - 1))) • E2)) +
              ((Nat.factorial (l'.length + 1) : ℝ) • CB) =
          ((6 * fallReal (l'.length + 2) l'.length) • E2 -
            ((↑(cnt n l' i) * (2 * fallReal (l'.length + 1) (l'.length - 1))) • E2)) -
              ((2 * (Nat.factorial (l'.length + 1) : ℝ)) • XE) +
              ((Nat.factorial (l'.length + 1) : ℝ) • CB) := by abel
      conv_lhs => rw [hL]
      conv_lhs =>
        rw [show ((6 * fallReal (l'.length + 2) l'.length) • E2 -
            ((↑(cnt n l' i) * (2 * fallReal (l'.length + 1) (l'.length - 1))) • E2)) =
          ((6 * fallReal (l'.length + 2) l'.length -
            (↑(cnt n l' i) * (2 * fallReal (l'.length + 1) (l'.length - 1)))) • E2) by
          rw [← sub_smul]]
      -- RHS: fix X-scalar to `2·f`, regroup so the two e² terms are adjacent, combine, and
      -- rewrite the combined scalar to the LHS form via he2scalar
      conv_rhs =>
        rw [show (Nat.factorial (l'.length + 1) : ℝ) * 2 = 2 * (Nat.factorial (l'.length + 1) : ℝ) by ring]
      have hR : (Nat.factorial (l'.length + 1) : ℝ) • CB +
            ((((Nat.factorial (l'.length + 1) : ℝ) * 6) • E2) -
              ((2 * (Nat.factorial (l'.length + 1) : ℝ)) • XE)) +
              (((Nat.factorial (l'.length + 1) : ℝ) * (↑(3 * l'.length - cnt n l' i) : ℝ)) • E2) =
          (Nat.factorial (l'.length + 1) : ℝ) • CB +
            ((((Nat.factorial (l'.length + 1) : ℝ) * 6) • E2) +
              (((Nat.factorial (l'.length + 1) : ℝ) * (↑(3 * l'.length - cnt n l' i) : ℝ)) • E2)) -
              ((2 * (Nat.factorial (l'.length + 1) : ℝ)) • XE) := by abel
      conv_rhs => rw [hR]
      conv_rhs => rw [← add_smul]
      conv_lhs => rw [he2scalar]
      abel

private lemma IsHomogeneous_smul {n : ℕ} (a : ℝ) {p : MvPolynomial (Fin n) ℝ} {m : ℕ}
    (hp : p.IsHomogeneous m) : (a • p).IsHomogeneous m := by
  rw [MvPolynomial.smul_eq_C_mul p a]
  exact hp.C_mul a

lemma eSum_hom_one (n : ℕ) : ((eSum n : MvPolynomial (Fin n) ℝ).IsHomogeneous 1) := by
  simpa [MvPolynomial.IsHomogeneous] using (eSum_isWeightedHomogeneous_one n)

lemma F_hom_one (n : ℕ) (i : Fin n) : (F n i).IsHomogeneous 1 := by
  unfold F
  exact MvPolynomial.IsHomogeneous.sub
    (IsHomogeneous_smul (6 : ℝ) (eSum_hom_one n))
    (IsHomogeneous_smul (2 : ℝ) (isHomogeneous_X (σ := Fin n) (R := ℝ) i))

def E2el (n : ℕ) : H n 2 := ⟨(eSum n) ^ 2, by
  simpa [MvPolynomial.IsHomogeneous] using eSum_isHomogeneous n 2⟩

def XiEel (n : ℕ) (i : Fin n) : H n 2 := ⟨MvPolynomial.X i * eSum n, by
  rw [mem_homogeneousSubmodule]
  exact (isHomogeneous_X (σ := Fin n) (R := ℝ) i).mul (eSum_hom_one n)⟩

def FiEel (n : ℕ) (i : Fin n) : H n 2 := ⟨F n i * eSum n, by
  rw [mem_homogeneousSubmodule]
  exact (F_hom_one n i).mul (eSum_hom_one n)⟩

def hB2 (n : ℕ) (a : Fin n → ℕ) : H n 2 := ⟨candB2 n a, by
  rw [mem_homogeneousSubmodule]
  dsimp [candB2]
  have hq : ((cand_q2 n).1).IsHomogeneous 2 := by
    simpa [MvPolynomial.IsHomogeneous] using (cand_q2 n).2
  have hL : (∑ i : Fin n, (((a i : ℕ) : ℝ) • F n i)).IsHomogeneous 1 := by
    refine MvPolynomial.IsHomogeneous.sum Finset.univ
      (fun i : Fin n => (((a i : ℕ) : ℝ) • F n i)) 1 ?_
    intro i hi
    exact IsHomogeneous_smul ((a i : ℕ) : ℝ) (F_hom_one n i)
  have hLe : (((∑ i : Fin n, (((a i : ℕ) : ℝ) • F n i)) * (eSum n)).IsHomogeneous 2) :=
    hL.mul (eSum_hom_one n)
  have he2 : ((eSum n) ^ 2).IsHomogeneous 2 := by
    simpa [MvPolynomial.IsHomogeneous] using eSum_isHomogeneous n 2
  have hCe : (((candC2 a : ℕ) : ℝ) • ((eSum n) ^ 2)).IsHomogeneous 2 :=
    IsHomogeneous_smul ((candC2 a : ℕ) : ℝ) he2
  have h2q : ((2 : ℝ) • (cand_q2 n).1).IsHomogeneous 2 := IsHomogeneous_smul (2 : ℝ) hq
  have hall := MvPolynomial.IsHomogeneous.add (MvPolynomial.IsHomogeneous.add h2q hLe) hCe
  simpa [candB2] using hall
⟩

lemma hessian_add (n : ℕ) (f g : H n 2) : (f + g).hessian = f.hessian + g.hessian := by
  classical
  ext i j
  by_cases h : i = j
  · subst j
    rw [hessian_apply_sq n (f + g) i]
    rw [Matrix.add_apply, hessian_apply_sq n f i, hessian_apply_sq n g i]
    change 2 * MvPolynomial.coeff (Finsupp.single i 2) (f.1 + g.1) =
      2 * MvPolynomial.coeff (Finsupp.single i 2) f.1 + 2 * MvPolynomial.coeff (Finsupp.single i 2) g.1
    rw [MvPolynomial.coeff_add]
    ring
  · rw [hessian_apply_cross n (f + g) h]
    rw [Matrix.add_apply, hessian_apply_cross n f h, hessian_apply_cross n g h]
    change MvPolynomial.coeff (Finsupp.single i 1 + Finsupp.single j 1) (f.1 + g.1) =
      MvPolynomial.coeff (Finsupp.single i 1 + Finsupp.single j 1) f.1 +
        MvPolynomial.coeff (Finsupp.single i 1 + Finsupp.single j 1) g.1
    rw [MvPolynomial.coeff_add]

lemma hessian_smul (n : ℕ) (c : ℝ) (f : H n 2) : (c • f).hessian = c • f.hessian := by
  classical
  ext i j
  by_cases h : i = j
  · subst j
    rw [hessian_apply_sq n (c • f) i]
    rw [Matrix.smul_apply, hessian_apply_sq n f i]
    change 2 * MvPolynomial.coeff (Finsupp.single i 2) (c • f.1) =
      c * (2 * MvPolynomial.coeff (Finsupp.single i 2) f.1)
    rw [MvPolynomial.coeff_smul]
    simp [smul_eq_mul]
    ring
  · rw [hessian_apply_cross n (c • f) h]
    rw [Matrix.smul_apply, hessian_apply_cross n f h]
    change MvPolynomial.coeff (Finsupp.single i 1 + Finsupp.single j 1) (c • f.1) =
      c * MvPolynomial.coeff (Finsupp.single i 1 + Finsupp.single j 1) f.1
    rw [MvPolynomial.coeff_smul]
    simp [smul_eq_mul]

-- coefficient of `X a * eSum` at degree-two monomials
lemma coeff_XaE_diag (n : ℕ) (a p : Fin n) :
    MvPolynomial.coeff (Finsupp.single p 2) (MvPolynomial.X a * eSum n) =
      (if a = p then (1 : ℝ) else 0) := by
  classical
  have hsum : MvPolynomial.X a * eSum n = ∑ i : Fin n, (MvPolynomial.X a * MvPolynomial.X i) := by
    unfold eSum
    rw [Finset.mul_sum]
  rw [hsum]
  rw [MvPolynomial.coeff_sum]
  simp only [coeff_X_mul_X]
  by_cases ha : a = p
  · subst a
    have h1 : (∑ i : Fin n, (if Finsupp.single p 2 = Finsupp.single p 1 + Finsupp.single i 1 then (1 : ℝ) else 0)) = 1 := by
      rw [Finset.sum_eq_single p]
      · simp [single_one_add_single_one]
      · intro b hb hbp
        have hne : ¬ (Finsupp.single p 2 = Finsupp.single p 1 + Finsupp.single b 1) := by
          intro hh
          exact hbp ((single_add_single_eq_single_two_iff p b p).mp hh.symm).2
        simp [hne]
      · intro hp
        exact False.elim (hp (Finset.mem_univ p))
    simpa using h1
  · have hzero : ∀ i : Fin n,
        (if Finsupp.single p 2 = Finsupp.single a 1 + Finsupp.single i 1 then (1 : ℝ) else 0) = 0 := by
      intro i
      have hne : ¬ (Finsupp.single p 2 = Finsupp.single a 1 + Finsupp.single i 1) := by
        intro hh
        rcases (single_add_single_eq_single_two_iff a i p).mp hh.symm with ⟨ha1, hi1⟩
        exact ha ha1
      simp [hne]
    simp [hzero, ha]

lemma coeff_XaE_cross (n : ℕ) (a p q : Fin n) (h : p ≠ q) :
    MvPolynomial.coeff (Finsupp.single p 1 + Finsupp.single q 1) (MvPolynomial.X a * eSum n) =
      (if p = a then (1 : ℝ) else 0) + (if q = a then (1 : ℝ) else 0) := by
  classical
  have hsum : MvPolynomial.X a * eSum n = ∑ i : Fin n, (MvPolynomial.X a * MvPolynomial.X i) := by
    unfold eSum
    rw [Finset.mul_sum]
  rw [hsum]
  rw [MvPolynomial.coeff_sum]
  simp only [coeff_X_mul_X]
  by_cases hpa : p = a
  · subst p
    have hqa' : q ≠ a := by
      intro hqa
      exact h (Eq.symm hqa)
    have h1 : (∑ i : Fin n, (if Finsupp.single a 1 + Finsupp.single q 1 = Finsupp.single a 1 + Finsupp.single i 1 then (1 : ℝ) else 0)) = 1 := by
      rw [Finset.sum_eq_single q]
      · simp
      · intro b hb hbq
        have hne : ¬ (Finsupp.single a 1 + Finsupp.single q 1 = Finsupp.single a 1 + Finsupp.single b 1) := by
          intro hh
          apply hbq
          have hq : Finsupp.single q 1 = Finsupp.single b 1 := add_left_cancel hh
          rw [Finsupp.single_eq_single_iff] at hq
          rcases hq with hq | hq
          · exact hq.1.symm
          · norm_num at hq
        simp [hne]
      · intro hq'
        exact False.elim (hq' (Finset.mem_univ q))
    rw [h1]
    simp [hqa']
  · by_cases hqa : q = a
    · subst q
      have h1 : (∑ i : Fin n, (if Finsupp.single p 1 + Finsupp.single a 1 = Finsupp.single a 1 + Finsupp.single i 1 then (1 : ℝ) else 0)) = 1 := by
        rw [Finset.sum_eq_single p]
        · rw [add_comm (Finsupp.single a 1) (Finsupp.single p 1)]
          simp
        · intro b hb hbp
          have hne : ¬ (Finsupp.single p 1 + Finsupp.single a 1 = Finsupp.single a 1 + Finsupp.single b 1) := by
            intro hh
            apply hbp
            rw [add_comm (Finsupp.single a 1) (Finsupp.single b 1)] at hh
            have hp : Finsupp.single p 1 = Finsupp.single b 1 := add_right_cancel hh
            rw [Finsupp.single_eq_single_iff] at hp
            rcases hp with hp | hp
            · exact hp.1.symm
            · norm_num at hp
          simp [hne]
        · intro hp'
          exact False.elim (hp' (Finset.mem_univ p))
      rw [h1]
      simp [hpa]
    · have h1 : (∑ i : Fin n, (if Finsupp.single p 1 + Finsupp.single q 1 = Finsupp.single a 1 + Finsupp.single i 1 then (1 : ℝ) else 0)) = 0 := by
        apply Finset.sum_eq_zero
        intro i hi
        have hne : ¬ (Finsupp.single p 1 + Finsupp.single q 1 = Finsupp.single a 1 + Finsupp.single i 1) := by
          intro hh
          rcases (single_add_single_eq_iff p q a i h).mp hh with ⟨ha, hi'⟩ | ⟨ha, hi'⟩
          · exact hpa ha.symm
          · exact hqa ha.symm
        simp [hne]
      rw [h1]
      simp [hpa, hqa]

lemma coeff_e2_diag (n : ℕ) (p : Fin n) :
    MvPolynomial.coeff (Finsupp.single p 2) ((eSum n) ^ 2) = 1 := by
  classical
  rw [pow_two]
  have hsum : eSum n * eSum n = ∑ i : Fin n, (MvPolynomial.X i * eSum n) := by
    unfold eSum
    rw [Finset.sum_mul]
  rw [hsum]
  rw [MvPolynomial.coeff_sum]
  simp [coeff_XaE_diag]

lemma coeff_e2_cross (n : ℕ) (p q : Fin n) (h : p ≠ q) :
    MvPolynomial.coeff (Finsupp.single p 1 + Finsupp.single q 1) ((eSum n) ^ 2) = 2 := by
  classical
  rw [pow_two]
  have hsum : eSum n * eSum n = ∑ i : Fin n, (MvPolynomial.X i * eSum n) := by
    unfold eSum
    rw [Finset.sum_mul]
  rw [hsum]
  rw [MvPolynomial.coeff_sum]
  simp [coeff_XaE_cross n, h]
  rw [Finset.sum_add_distrib]
  have hs1 : (∑ x : Fin n, (if p = x then (1 : ℝ) else 0)) = 1 := by simp
  have hs2 : (∑ x : Fin n, (if q = x then (1 : ℝ) else 0)) = 1 := by simp
  rw [hs1, hs2]
  norm_num

/-- hessian of `X a * e` -/
lemma hessian_XiEel (n : ℕ) (a : Fin n) :
    (XiEel n a).hessian = fun p q => (if p = a then (1 : ℝ) else 0) + (if q = a then (1 : ℝ) else 0) := by
  classical
  ext p q
  by_cases hpq : p = q
  · subst q
    rw [hessian_apply_sq n (XiEel n a) p]
    change 2 * MvPolynomial.coeff (Finsupp.single p 2) (MvPolynomial.X a * eSum n) =
      (if p = a then (1 : ℝ) else 0) + (if p = a then (1 : ℝ) else 0)
    rw [coeff_XaE_diag n a p]
    by_cases hpa : p = a
    · subst p
      norm_num
    · have hap : a ≠ p := Ne.symm hpa
      simp [hpa, hap]
  · rw [hessian_apply_cross n (XiEel n a) hpq]
    change MvPolynomial.coeff (Finsupp.single p 1 + Finsupp.single q 1) (MvPolynomial.X a * eSum n) =
      (if p = a then (1 : ℝ) else 0) + (if q = a then (1 : ℝ) else 0)
    rw [coeff_XaE_cross n a p q hpq]

/-- hessian of `e²` is the all-two matrix -/
lemma hessian_E2el (n : ℕ) : (E2el n).hessian = fun _ _ => (2 : ℝ) := by
  classical
  ext p q
  by_cases h : p = q
  · subst q
    rw [hessian_apply_sq n (E2el n) p]
    change 2 * MvPolynomial.coeff (Finsupp.single p 2) ((eSum n) ^ 2) = 2
    rw [coeff_e2_diag n p]
    norm_num
  · rw [hessian_apply_cross n (E2el n) h]
    change MvPolynomial.coeff (Finsupp.single p 1 + Finsupp.single q 1) ((eSum n) ^ 2) = 2
    rw [coeff_e2_cross n p q h]
lemma hessian_zero (n : ℕ) : (0 : H n 2).hessian = 0 := by
  rw [show (0 : H n 2) = (0 : ℝ) • E2el n by simp]
  rw [hessian_smul]
  simp

lemma hessian_finset_sum (n : ℕ) {ι : Type*} (s : Finset ι) (f : ι → H n 2) :
    (∑ i ∈ s, f i).hessian = ∑ i ∈ s, (f i).hessian := by
  classical
  refine Finset.induction_on s ?_ ?_
  · simp [hessian_zero]
  · intro a s has ih
    simp [has, hessian_add, ih]

lemma hessian_neg (n : ℕ) (f : H n 2) : (-f).hessian = -f.hessian := by
  have h := hessian_smul n (-1 : ℝ) f
  simpa using h

lemma hessian_sub (n : ℕ) (f g : H n 2) : (f - g).hessian = f.hessian - g.hessian := by
  rw [sub_eq_add_neg, hessian_add, hessian_neg]
  rfl

lemma FiEel_decomp (n : ℕ) (i : Fin n) :
    FiEel n i = (6 : ℝ) • E2el n - (2 : ℝ) • XiEel n i := by
  apply Subtype.ext
  change F n i * eSum n = (6 : ℝ) • ((eSum n) ^ 2) - (2 : ℝ) • (MvPolynomial.X i * eSum n)
  unfold F
  rw [sub_mul]
  rw [smul_mul_assoc]
  rw [smul_mul_assoc]
  rw [← pow_two]

lemma hessian_FiEel (n : ℕ) (i p q : Fin n) :
    (FiEel n i).hessian p q =
      12 - 2 * ((if p = i then (1 : ℝ) else 0) + (if q = i then (1 : ℝ) else 0)) := by
  rw [FiEel_decomp]
  rw [hessian_sub]
  rw [hessian_smul]
  rw [hessian_smul]
  rw [Matrix.sub_apply]
  rw [Matrix.smul_apply]
  rw [Matrix.smul_apply]
  rw [hessian_E2el]
  rw [hessian_XiEel]
  by_cases hpi : p = i <;> by_cases hqi : q = i <;> simp [hpi, hqi] <;> norm_num

lemma coe_val_add (n : ℕ) (x y : H n 2) : (x + y).1 = x.1 + y.1 := by rfl
lemma coe_val_zero (n : ℕ) : (0 : H n 2).1 = 0 := by rfl
lemma coe_val_smul (n : ℕ) (c : ℝ) (x : H n 2) : (c • x).1 = c • x.1 := by rfl

lemma val_finset_sum (n : ℕ) {ι : Type*} (s : Finset ι) (f : ι → H n 2) :
    (∑ i ∈ s, f i).1 = ∑ i ∈ s, (f i).1 := by
  classical
  refine Finset.induction_on s ?_ ?_
  · rw [Finset.sum_empty, Finset.sum_empty]
    exact coe_val_zero n
  · intro a s has ih
    rw [Finset.sum_insert has, Finset.sum_insert has]
    rw [coe_val_add, ih]

lemma hB2_decomp (n : ℕ) (a : Fin n → ℕ) :
    hB2 n a = (2 : ℝ) • (cand_q2 n) + (∑ i : Fin n, (((a i : ℕ) : ℝ) • FiEel n i)) +
      ((candC2 a : ℕ) : ℝ) • E2el n := by
  classical
  apply Subtype.ext
  change candB2 n a = ((2 : ℝ) • (cand_q2 n) + (∑ i : Fin n, (((a i : ℕ) : ℝ) • FiEel n i)) +
      ((candC2 a : ℕ) : ℝ) • E2el n).1
  change candB2 n a =
      (2 : ℝ) • (cand_q2 n).1 + (∑ i : Fin n, (((a i : ℕ) : ℝ) • FiEel n i)).1 +
        ((candC2 a : ℕ) : ℝ) • (E2el n).1
  rw [val_finset_sum n Finset.univ]
  simp only [coe_val_smul]
  simp only [FiEel]
  change candB2 n a =
      (2 : ℝ) • (cand_q2 n).1 +
        (∑ i : Fin n, (((a i : ℕ) : ℝ) • (F n i * eSum n))) +
          ((candC2 a : ℕ) : ℝ) • ((eSum n) ^ 2)
  unfold candB2
  rw [Finset.sum_mul]
  have hm : (∑ i : Fin n, (((a i : ℕ) : ℝ) • F n i) * (eSum n)) =
      (∑ i : Fin n, (((a i : ℕ) : ℝ) • (F n i * eSum n))) := by
    apply Finset.sum_congr rfl
    intro i hi
    rw [smul_mul_assoc]
  rw [hm]


lemma sum_cast (n : ℕ) (a : Fin n → ℕ) : (∑ i : Fin n, ((a i : ℕ) : ℝ)) = ((∑ i : Fin n, a i : ℕ) : ℝ) := by
  classical
  induction (Finset.univ : Finset (Fin n)) using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha]
      rw [ih]
      norm_num

lemma sum_delta_term (n : ℕ) (a : Fin n → ℕ) (p q : Fin n) :
    (∑ i : Fin n, (((a i : ℕ) : ℝ) *
        ((if p = i then (1 : ℝ) else 0) + (if q = i then (1 : ℝ) else 0)))) =
      ((a p : ℕ) : ℝ) + ((a q : ℕ) : ℝ) := by
  classical
  have h1 : (∑ i : Fin n, (((a i : ℕ) : ℝ) * (if p = i then (1 : ℝ) else 0))) = ((a p : ℕ) : ℝ) := by
    calc
      (∑ i : Fin n, (((a i : ℕ) : ℝ) * (if p = i then (1 : ℝ) else 0)))
          = ∑ i : Fin n, (if p = i then ((a i : ℕ) : ℝ) else 0) := by
            apply Finset.sum_congr rfl
            intro i hi
            by_cases hpi : p = i
            · subst i; simp
            · simp [hpi]
      _ = ((a p : ℕ) : ℝ) := by simp
  have h2 : (∑ i : Fin n, (((a i : ℕ) : ℝ) * (if q = i then (1 : ℝ) else 0))) = ((a q : ℕ) : ℝ) := by
    calc
      (∑ i : Fin n, (((a i : ℕ) : ℝ) * (if q = i then (1 : ℝ) else 0)))
          = ∑ i : Fin n, (if q = i then ((a i : ℕ) : ℝ) else 0) := by
            apply Finset.sum_congr rfl
            intro i hi
            by_cases hqi : q = i
            · subst i; simp
            · simp [hqi]
      _ = ((a q : ℕ) : ℝ) := by simp
  calc
    (∑ i : Fin n, (((a i : ℕ) : ℝ) * ((if p = i then (1 : ℝ) else 0) + (if q = i then (1 : ℝ) else 0))))
        = ∑ i : Fin n, ((((a i : ℕ) : ℝ) * (if p = i then (1 : ℝ) else 0)) +
            (((a i : ℕ) : ℝ) * (if q = i then (1 : ℝ) else 0))) := by
          apply Finset.sum_congr rfl
          intro i hi
          rw [mul_add]
    _ = (∑ i : Fin n, (((a i : ℕ) : ℝ) * (if p = i then (1 : ℝ) else 0))) +
          (∑ i : Fin n, (((a i : ℕ) : ℝ) * (if q = i then (1 : ℝ) else 0))) := by
          rw [Finset.sum_add_distrib]
    _ = ((a p : ℕ) : ℝ) + ((a q : ℕ) : ℝ) := by rw [h1, h2]


lemma matrix_sum_apply {n : ℕ} {ι : Type*} [Fintype ι]
    (A : ι → Matrix (Fin n) (Fin n) ℝ) (p q : Fin n) :
    ((∑ x, A x) p q) = ∑ x, A x p q := by
  classical
  let ev : Matrix (Fin n) (Fin n) ℝ →ₗ[ℝ] ℝ := { toFun := fun M => M p q, map_add' := by intro M N; rfl, map_smul' := by intro c M; rfl }
  change ev (∑ x, A x) = ∑ x, A x p q
  exact map_sum (M := Matrix (Fin n) (Fin n) ℝ) (N := ℝ)
    (g := (show Matrix (Fin n) (Fin n) ℝ →+ ℝ from ev)) (f := A) (s := Finset.univ)

lemma matrix_sum_smul_apply (n : ℕ) (c : Fin n → ℝ) (M : Fin n → Matrix (Fin n) (Fin n) ℝ) (p q : Fin n) :
    ((∑ x : Fin n, (c x) • (M x)) p q) = ∑ x : Fin n, (c x) • (M x p q) := by
  classical
  rw [matrix_sum_apply]
  apply Finset.sum_congr rfl
  intro x hx
  simp [Matrix.smul_apply]


lemma hessian_hB2 (n : ℕ) (a : Fin n → ℕ) :
    (hB2 n a).hessian = (2 : ℝ) • candMat a (∑ i : Fin n, a i) := by
  classical
  rw [hB2_decomp]
  rw [hessian_add, hessian_add]
  rw [hessian_smul, hessian_smul]
  rw [hessian_finset_sum n Finset.univ]
  simp only [hessian_smul]
  ext p q
  rw [Matrix.add_apply, Matrix.add_apply, Matrix.smul_apply, Matrix.smul_apply]
  rw [matrix_sum_smul_apply]
  rw [cand_q2_hessian]
  simp only [hessian_FiEel, hessian_E2el, esiMath.countJMat]
  rw [Matrix.smul_apply]
  simp only [smul_eq_mul, sub_zero]
  change 2 * (3 - (if p = q then (1 : ℝ) else 0)) +
      (∑ i : Fin n, (((a i : ℕ) : ℝ) *
        (12 - 2 * ((if p = i then (1 : ℝ) else 0) + (if q = i then (1 : ℝ) else 0))))) +
      ((candC2 a : ℕ) : ℝ) * 2 =
    2 * (((candM a (∑ i : Fin n, a i) : ℕ) : ℝ) - (if p = q then (1 : ℝ) else 0) -
        ((a p : ℕ) : ℝ) - ((a q : ℕ) : ℝ))
  have hm : (∑ i : Fin n, (((a i : ℕ) : ℝ) *
        (12 - 2 * ((if p = i then (1 : ℝ) else 0) + (if q = i then (1 : ℝ) else 0))))) =
      12 * ((∑ i : Fin n, a i : ℕ) : ℝ) - 2 * (((a p : ℕ) : ℝ) + ((a q : ℕ) : ℝ)) := by
    calc
      (∑ i : Fin n, (((a i : ℕ) : ℝ) * (12 - 2 * ((if p = i then (1 : ℝ) else 0) + (if q = i then (1 : ℝ) else 0)))))
          = ∑ i : Fin n, ((((a i : ℕ) : ℝ) * 12) - 2 * (((a i : ℕ) : ℝ) * ((if p = i then (1 : ℝ) else 0) + (if q = i then (1 : ℝ) else 0)))) := by
            apply Finset.sum_congr rfl
            intro i hi
            ring
      _ = ((∑ i : Fin n, ((a i : ℕ) : ℝ)) * 12) -
            2 * (∑ i : Fin n, (((a i : ℕ) : ℝ) * ((if p = i then (1 : ℝ) else 0) + (if q = i then (1 : ℝ) else 0)))) := by
            rw [Finset.sum_sub_distrib]
            rw [Finset.sum_mul]
            congr 1
            rw [Finset.mul_sum]
      _ = 12 * ((∑ i : Fin n, a i : ℕ) : ℝ) - 2 * (((a p : ℕ) : ℝ) + ((a q : ℕ) : ℝ)) := by
            rw [sum_cast]
            rw [sum_delta_term]
            nlinarith
  rw [hm]
  simp only [candM]
  norm_num
  ring


lemma partialElem_two_smul (n : ℕ) (l : List (Fin n)) :
    (2 : ℝ) • partialElem l.length l (candS n l.length) rfl =
      (Nat.factorial l.length : ℝ) • hB2 n (cnt n l) := by
  apply Subtype.ext
  change (2 : ℝ) • pderivL l ((candS n l.length).1) =
    (Nat.factorial l.length : ℝ) • candB2 n (cnt n l)
  exact closedFormA n l

lemma hessian_partialElem_candS (n : ℕ) (l : List (Fin n)) :
    (partialElem l.length l (candS n l.length) rfl).hessian =
      (Nat.factorial l.length : ℝ) • candMat (cnt n l) l.length := by
  classical
  let pe : H n 2 := partialElem l.length l (candS n l.length) rfl
  change pe.hessian = (Nat.factorial l.length : ℝ) • candMat (cnt n l) l.length
  have hscal : (2 : ℝ) • pe.hessian =
      ((2 * Nat.factorial l.length : ℕ) : ℝ) • candMat (cnt n l) (∑ i : Fin n, cnt n l i) := by
    calc
      (2 : ℝ) • pe.hessian = ((2 : ℝ) • pe).hessian := by rw [← hessian_smul]
      _ = ((Nat.factorial l.length : ℝ) • hB2 n (cnt n l)).hessian := by rw [partialElem_two_smul]
      _ = (Nat.factorial l.length : ℝ) • (hB2 n (cnt n l)).hessian := by rw [hessian_smul]
      _ = (Nat.factorial l.length : ℝ) • ((2 : ℝ) • candMat (cnt n l) (∑ i : Fin n, cnt n l i)) := by rw [hessian_hB2]
      _ = ((Nat.factorial l.length : ℝ) * 2) • candMat (cnt n l) (∑ i : Fin n, cnt n l i) := by rw [smul_smul]
      _ = ((2 * Nat.factorial l.length : ℕ) : ℝ) • candMat (cnt n l) (∑ i : Fin n, cnt n l i) := by
            norm_num [Nat.cast_mul]
            ring
  have hhalf : pe.hessian = (1 / 2 : ℝ) • ((2 : ℝ) • pe.hessian) := by
    rw [smul_smul]
    norm_num
  rw [hhalf, hscal]
  rw [smul_smul]
  rw [sum_cnt_eq_length n l]
  congr 1
  norm_num [Nat.cast_mul]
  ring


private lemma charpoly_smul_scaleRoots (n : ℕ) {c : ℝ} (hc : c ≠ 0)
    (A : Matrix (Fin n) (Fin n) ℝ) :
    (c • A).charpoly = A.charpoly.scaleRoots c := by
  classical
  apply Polynomial.funext
  intro x
  let y : ℝ := c⁻¹ * x
  have hcy : c * y = x := by
    dsimp [y]
    field_simp [hc]
  have hsmul_scalar : c • Matrix.scalar (Fin n) y = Matrix.scalar (Fin n) (c * y) := by
    ext i j
    by_cases hij : i = j
    · subst j
      simp [Matrix.scalar_apply, Matrix.smul_apply, smul_eq_mul]
    · simp [Matrix.scalar_apply, Matrix.smul_apply, smul_eq_mul, hij]
  have hscalar : Matrix.scalar (Fin n) (c * y) - c • A = c • (Matrix.scalar (Fin n) y - A) := by
    rw [hsmul_scalar.symm]
    rw [smul_sub]
  have hL : Polynomial.eval (c * y) (charpoly (c • A)) =
      c ^ n * Polynomial.eval y (charpoly A) := by
    rw [Matrix.eval_charpoly, Matrix.eval_charpoly, hscalar, Matrix.det_smul]
    simp
  have hnd : (A.charpoly).natDegree = n := by simp
  have hR : Polynomial.eval (c * y) (A.charpoly.scaleRoots c) =
      c ^ n * Polynomial.eval y (charpoly A) := by
    rw [Polynomial.scaleRoots_eval_mul]
    rw [hnd]
  have hmain : Polynomial.eval x (charpoly (c • A)) = Polynomial.eval x (A.charpoly.scaleRoots c) := by
    calc
      Polynomial.eval x (charpoly (c • A)) = Polynomial.eval (c * y) (charpoly (c • A)) := by rw [← hcy]
      _ = c ^ n * Polynomial.eval y (charpoly A) := hL
      _ = Polynomial.eval (c * y) (A.charpoly.scaleRoots c) := hR.symm
      _ = Polynomial.eval x (A.charpoly.scaleRoots c) := by rw [hcy]
  exact hmain

private lemma card_filter_pos_map_mul (c : ℝ) (hc : 0 < c) (s : Multiset ℝ) :
    ((s.map (fun r : ℝ => c * r)).filter (0 < ·)).card =
      (s.filter (0 < ·)).card := by
  classical
  have hf := Multiset.filter_map (p := fun r : ℝ => 0 < r) (f := fun r : ℝ => c * r) s
  rw [hf]
  rw [Multiset.card_map]
  congr 1
  apply Multiset.filter_congr
  intro r hr
  constructor
  · intro hpos
    dsimp at hpos
    exact (mul_pos_iff_of_pos_left hc).mp hpos
  · intro hpos
    exact mul_pos hc hpos

private lemma charpoly_smul_pos_roots_card (n : ℕ) {c : ℝ} (hc : 0 < c)
    (A : Matrix (Fin n) (Fin n) ℝ) :
    ((c • A).charpoly.roots.filter (0 < ·)).card = (A.charpoly.roots.filter (0 < ·)).card := by
  classical
  have hc0 : c ≠ 0 := ne_of_gt hc
  rw [charpoly_smul_scaleRoots n hc0 A]
  have hIsUnit : IsUnit c := isUnit_iff_ne_zero.mpr hc0
  rw [Polynomial.roots_scaleRoots (A.charpoly) hIsUnit]
  exact card_filter_pos_map_mul c hc A.charpoly.roots

private lemma isUnit_smul_matrix (n : ℕ) {c : ℝ} (hc : c ≠ 0)
    {A : Matrix (Fin n) (Fin n) ℝ} (hA : IsUnit A) : IsUnit (c • A) := by
  classical
  rw [Matrix.isUnit_iff_isUnit_det] at hA
  rw [Matrix.isUnit_iff_isUnit_det]
  rw [Matrix.det_smul]
  rw [isUnit_iff_ne_zero] at hA ⊢
  exact mul_ne_zero (pow_ne_zero (Fintype.card (Fin n)) hc) hA

lemma smul_mem_strictQuadSet (n : ℕ) {c : ℝ} (hc : 0 < c)
    {A : Matrix (Fin n) (Fin n) ℝ}
    (hA : A ∈ Commons.LinearAlgebra.Matrix.strictQuadSet n) :
    (c • A) ∈ Commons.LinearAlgebra.Matrix.strictQuadSet n := by
  classical
  rcases hA with ⟨hsymm, hpos, hunit, hcard⟩
  constructor
  · refine Matrix.IsSymm.ext ?_
    intro i j
    rw [Matrix.smul_apply, Matrix.smul_apply]
    apply congrArg (fun x : ℝ => c • x)
    exact (Matrix.IsSymm.ext_iff.mp hsymm) i j
  · constructor
    · intro i j
      rw [Matrix.smul_apply]
      exact mul_pos hc (hpos i j)
    · constructor
      · exact isUnit_smul_matrix n (ne_of_gt hc) hunit
      · rw [charpoly_smul_pos_roots_card n hc A]
        exact hcard


lemma partialElem_mem_Ŀ_two (n : ℕ) (hn : 0 < n) (l : List (Fin n)) :
    partialElem l.length l (candS n l.length) rfl ∈ Ŀ n 2 := by
  classical
  let pe : H n 2 := partialElem l.length l (candS n l.length) rfl
  change pe ∈ Ŀ n 2
  have hfac : 0 < (Nat.factorial l.length : ℝ) := by
    exact_mod_cast (Nat.factorial_pos l.length)
  have heq : candMat (cnt n l) l.length =
      esiMath.countJMat n ((candM (cnt n l) l.length : ℕ) : ℝ) (fun i => ((cnt n l i : ℕ) : ℝ)) := by
    ext p q
    rfl
  have hcand : candMat (cnt n l) l.length ∈ Commons.LinearAlgebra.Matrix.strictQuadSet n := by
    rw [heq]
    apply esiMath.countJMat_strictQuad n (candM (cnt n l) l.length) l.length hn (cnt n l)
    · exact sum_cnt_eq_length n l
    · dsimp [candM]
      omega
  have hstrict : ((Nat.factorial l.length : ℝ) • candMat (cnt n l) l.length) ∈
      Commons.LinearAlgebra.Matrix.strictQuadSet n :=
    smul_mem_strictQuadSet n hfac hcand
  have hh : pe.hessian = (Nat.factorial l.length : ℝ) • candMat (cnt n l) l.length := by
    dsimp [pe]
    exact hessian_partialElem_candS n l
  have hpe : pe.hessian ∈ Commons.LinearAlgebra.Matrix.strictQuadSet n := by
    rw [hh]
    exact hstrict
  rcases hpe with ⟨hsymm, hpos, hunit, hcard⟩
  rw [← quadricOfMatrix_hessian n pe]
  exact quadricOfMatrix_mem_Ŀ_of_strict n hsymm hpos hunit hcard

lemma partialElem_length (n : ℕ) (s : ℕ) (l : List (Fin n)) (hl : l.length = s) :
    partialElem s l (candS n s) hl = partialElem l.length l (candS n l.length) rfl := by
  classical
  apply Subtype.ext
  change pderivL l ((candS n s).1) = pderivL l ((candS n l.length).1)
  congr 1
  change (cand_q2 n).1 * (eSum n) ^ s = (cand_q2 n).1 * (eSum n) ^ l.length
  congr 1
  rw [← hl]

lemma partialElem_mem_Ŀ (n : ℕ) (hn : 0 < n) (s : ℕ) (l : List (Fin n)) (hl : l.length = s) :
    partialElem s l (candS n s) hl ∈ Ŀ n 2 := by
  classical
  rw [partialElem_length n s l hl]
  exact partialElem_mem_Ŀ_two n hn l

lemma candS_mem_Ŀ (n : ℕ) (hn : 0 < n) (s : ℕ) : candS n s ∈ Ŀ n (s + 2) := by
  classical
  exact Ŀ_of_partials n s (candS n s) (candS_mem_P n s) (fun l hl => partialElem_mem_Ŀ n hn s l hl)


lemma candPow_mem_S (n d : ℕ) (hn : 0 < n) : candPow n d ∈ S n d := by
  classical
  constructor
  · change IsStable (candPow n d).1
    simp [candPow]
    exact eSum_pow_stable n d hn
  · intro m
    change 0 ≤ MvPolynomial.coeff m (candPow n d).1
    simp only [candPow]
    change 0 ≤ MvPolynomial.coeff m ((eSum n) ^ d)
    change 0 ≤ MvPolynomial.coeff m ((∑ i : Fin n, MvPolynomial.X i) ^ d)
    rw [MvPolynomial.coeff_sum_X_pow_of_fintype (R := ℝ) (σ := Fin n) m d]
    by_cases h : m.sum (fun _ x => x) = d
    · rw [if_pos h]
      exact_mod_cast (Nat.zero_le (m.multinomial))
    · rw [if_neg h]
      norm_num


theorem exists_strict_stable_in_intersection (n d : ℕ) (hn : 0 < n) :
    ∃ f : H n d, f ∈ Ŀ n d ∧ f ∈ S n d := by
  classical
  by_cases hd2 : d ≤ 2
  · have hcases : d = 0 ∨ d = 1 ∨ d = 2 := by omega
    rcases hcases with hd | hd | hd
    · subst d
      refine ⟨candPow n 0, ?_, ?_⟩
      · have hP : candPow n 0 ∈ P n 0 := by
          dsimp [candPow]
          exact eSum_pow_mem_P n 0
        simpa [Ŀ] using hP
      · exact candPow_mem_S n 0 hn
    · subst d
      refine ⟨candPow n 1, ?_, ?_⟩
      · have hP : candPow n 1 ∈ P n 1 := by
          dsimp [candPow]
          exact eSum_pow_mem_P n 1
        simpa [Ŀ] using hP
      · exact candPow_mem_S n 1 hn
    · subst d
      refine ⟨cand_q2 n, ?_, ?_⟩
      · exact cand_q2_mem_Ŀ n hn
      · exact cand_q2_mem_S n hn
  · rcases (⟨d - 2, by omega⟩ : ∃ k : ℕ, d = k + 2) with ⟨k, hk⟩
    rw [hk]
    exact ⟨candS n k, candS_mem_Ŀ n hn k, candS_mem_S n k hn⟩

end

end WitEx


noncomputable section

/-- pderiv of an element of `H n d` as an element of `H n (d-1)`. -/
def pderivS {n d : ℕ} (i : Fin n) (g : H n d) : H n (d - 1) :=
  ⟨g.1.pderiv i, g.2.pderiv⟩

lemma pderivS_apply {n d : ℕ} (i : Fin n) (g : H n d) : (pderivS i g).1 = g.1.pderiv i := rfl

/-- the Hessian matrix of g at w -/
def hessAt {n d : ℕ} (w : Fin n → ℝ) (g : H n d) : Matrix (Fin n) (Fin n) ℝ :=
  Matrix.of (fun a b : Fin n => MvPolynomial.eval w (MvPolynomial.pderiv a (MvPolynomial.pderiv b g.1)))

/-- the number of positive real roots of the characteristic polynomial -/
def posRoots {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) : ℕ :=
  (A.charpoly.roots.filter (fun r : ℝ => 0 < r)).card

lemma hessAt_apply {n d : ℕ} (w : Fin n → ℝ) (g : H n d) (a b : Fin n) :
    hessAt w g a b = MvPolynomial.eval w (MvPolynomial.pderiv a (MvPolynomial.pderiv b g.1)) := rfl

lemma hessAt_symm (n d : ℕ) (w : Fin n → ℝ) (g : H n d) : (hessAt w g).IsSymm := by
  unfold hessAt
  exact rayleigh_pre.hess_symm g.1 w

/-- Ŀ ⊆ P (all degrees). -/
lemma Ŀ_subset_P (n d : ℕ) : Ŀ n d ⊆ P n d := by
  intro f hf
  cases d with
  | zero => simpa [Ŀ] using hf
  | succ d =>
      cases d with
      | zero => simpa [Ŀ] using hf
      | succ d =>
          cases d with
          | zero => simpa [Ŀ] using hf.1
          | succ k => simpa [Ŀ] using hf.1

/-- partial derivative of a strict element (degree ≥ 3) is strict. -/
lemma Ŀ_pderiv_mem {n d : ℕ} (hd : 3 ≤ d) (g : H n d) (hg : g ∈ Ŀ n d) (i : Fin n) :
    pderivS i g ∈ Ŀ n (d - 1) := by
  classical
  rcases d with _ | d1
  · omega
  rcases d1 with _ | d2
  · omega
  rcases d2 with _ | e
  · omega
  · change pderivS i g ∈ Ŀ n (e + 2)
    have hgmem : g ∈ {f : H n (e + 3) | f ∈ P n (e + 3) ∧
        ∀ j : Fin n, (⟨f.1.pderiv j, f.2.pderiv⟩ : H n (e + 2)) ∈ Ŀ n (e + 2)} := by
      change g ∈ Ŀ n (e + 3)
      simpa [Ŀ] using hg
    have hpart : (⟨g.1.pderiv i, g.2.pderiv⟩ : H n (e + 2)) ∈ Ŀ n (e + 2) := hgmem.2 i
    change (⟨g.1.pderiv i, g.2.pderiv⟩ : H n (e + 2)) ∈ Ŀ n (e + 2)
    exact hpart

/-- pderiv of a P element (degree ≥ 1) is in P. -/
lemma pderivS_mem_P {n d : ℕ} (hd : 1 ≤ d) (g : H n d) (hg : g ∈ P n d) (i : Fin n) :
    pderivS i g ∈ P n (d - 1) := by
  classical
  intro m hm
  dsimp [pderivS]
  rw [MvPolynomial.coeff_pderiv]
  have hw : Finsupp.weight (1 : Fin n → ℕ) (m + Finsupp.single i 1) = d := by
    rw [map_add (Finsupp.weight (1 : Fin n → ℕ)), Finsupp.weight_single]
    rw [hm]
    simp
    omega
  have hc : 0 < g.1.coeff (m + Finsupp.single i 1) := hg (m + Finsupp.single i 1) hw
  have hm0 : 0 ≤ (m i : ℝ) + 1 := by positivity
  positivity

/-- A P polynomial has positive evaluation at positive w (n ≥ 1). -/
lemma eval_pos_of_P {n d : ℕ} (hn : 0 < n) (g : H n d) (hg : g ∈ P n d)
    {w : Fin n → ℝ} (hw : ∀ k : Fin n, 0 < w k) : 0 < MvPolynomial.eval w g.1 := by
  classical
  haveI : Nonempty (Fin n) := Fin.pos_iff_nonempty.mp hn
  let i0 : Fin n := ⟨0, hn⟩
  let m : Fin n →₀ ℕ := Finsupp.single i0 d
  have hm : Finsupp.weight (1 : Fin n → ℕ) m = d := by
    simp [m, Finsupp.weight_single]
  have hcoeff : 0 < g.1.coeff m := hg m hm
  have hne : g.1 ≠ 0 := by
    intro h0
    have : g.1.coeff m = 0 := by rw [h0]; simp
    linarith
  exact rayleigh_pre.eval_pos_of_ne_zero g.1 (fun m' => by
    by_cases hm' : Finsupp.weight (1 : Fin n → ℕ) m' = d
    · exact le_of_lt (hg m' hm')
    · have hc : g.1.coeff m' = 0 := by
        exact MvPolynomial.IsWeightedHomogeneous.coeff_eq_zero (w := (1 : Fin n → ℕ))
          (by simpa [MvPolynomial.IsHomogeneous] using g.2) m' hm'
      exact le_of_eq hc.symm) hw hne

/-- eval of pderiv of strict element at positive w is positive -/
lemma Ŀ_pderiv_eval_pos {n d : ℕ} (hn : 0 < n) (hd : 2 ≤ d) (g : H n d) (hg : g ∈ Ŀ n d)
    (i : Fin n) {w : Fin n → ℝ} (hw : ∀ k : Fin n, 0 < w k) :
    0 < MvPolynomial.eval w (MvPolynomial.pderiv i g.1) := by
  have hp : pderivS i g ∈ P n (d - 1) := pderivS_mem_P (by omega : 1 ≤ d) g (Ŀ_subset_P n d hg) i
  have he := eval_pos_of_P hn (pderivS i g) hp hw
  simpa [pderivS] using he

-- ============================ degree 2 base ============================

/-- the Hessian matrix at w equals the definitional Hessian for degree 2 -/
lemma hessAt_eq_hessian_two (n : ℕ) (w : Fin n → ℝ) (f : H n 2) :
    (hessAt w f) = f.hessian := by
  classical
  ext a b
  change MvPolynomial.eval w (MvPolynomial.pderiv a (MvPolynomial.pderiv b f.1)) = f.hessian a b
  have h1 := hessian_aeval_eq_pderiv_eq_sum_hessian n f b
  have hpd : MvPolynomial.pderiv a (MvPolynomial.pderiv b f.1) = MvPolynomial.C (f.hessian b a) := by
    rw [h1]
    rw [map_sum]
    have hpdterm : ∀ j : Fin n,
        MvPolynomial.pderiv a (MvPolynomial.C (f.hessian b j) * MvPolynomial.X j) =
          if j = a then MvPolynomial.C (f.hessian b a) else 0 := by
      intro j
      by_cases h : j = a
      · subst j
        rw [pderiv_mul, pderiv_C, pderiv_X_self a]
        simp
      · rw [pderiv_mul, pderiv_C, pderiv_X_of_ne h]
        simp [h]
    calc
      (∑ x : Fin n, MvPolynomial.pderiv a (MvPolynomial.C (f.hessian b x) * MvPolynomial.X x))
          = ∑ x : Fin n, (if x = a then MvPolynomial.C (f.hessian b a) else 0) := by
            apply Finset.sum_congr rfl
            intro x _
            rw [hpdterm x]
      _ = MvPolynomial.C (f.hessian b a) := by simp
  rw [hpd]
  simp
  have hsymm : f.hessian.IsSymm := hessian_symm n f
  exact Matrix.IsSymm.ext_iff.mp hsymm a b

lemma hessian_two_units (n : ℕ) (f : H n 2) (hf : f ∈ Ŀ n 2) : IsUnit f.hessian := by
  have : f ∈ P n 2 ∧ IsUnit f.hessian ∧
      (f.hessian.charpoly.roots.filter (fun r : ℝ => 0 < r)).card = 1 := by simpa [Ŀ] using hf
  exact this.2.1

lemma hessian_two_index_card (n : ℕ) (f : H n 2) (hf : f ∈ Ŀ n 2) :
    (f.hessian.charpoly.roots.filter (fun r : ℝ => 0 < r)).card = 1 := by
  have : f ∈ P n 2 ∧ IsUnit f.hessian ∧
      (f.hessian.charpoly.roots.filter (fun r : ℝ => 0 < r)).card = 1 := by simpa [Ŀ] using hf
  exact this.2.2

/-- degree 2 nonsingularity -/
lemma strict_two_nonsing (n : ℕ) (f : H n 2) (hf : f ∈ Ŀ n 2) (w : Fin n → ℝ) :
    (hessAt w f).det ≠ 0 := by
  have hIsUnit : IsUnit f.hessian := hessian_two_units n f hf
  have hdet_unit : IsUnit f.hessian.det := by
    rw [Matrix.isUnit_iff_isUnit_det] at hIsUnit
    exact hIsUnit
  have hdet_ne : f.hessian.det ≠ 0 := isUnit_iff_ne_zero.mp hdet_unit
  rwa [hessAt_eq_hessian_two n w f]

/-- degree 2 index -/
lemma strict_two_index {n : ℕ} (f : H n 2) (hf : f ∈ Ŀ n 2) (w : Fin n → ℝ) :
    posRoots (hessAt w f) ≤ 1 := by
  change ((hessAt w f).charpoly.roots.filter (fun r : ℝ => 0 < r)).card ≤ 1
  rw [hessAt_eq_hessian_two n w f]
  rw [hessian_two_index_card n f hf]

-- ============================ Euler identities ============================

/-- three partial derivatives commute -/
lemma pderiv3_comm {n : ℕ} (a b c : Fin n) (p : MvPolynomial (Fin n) ℝ) :
    pderiv a (pderiv b (pderiv c p)) = pderiv c (pderiv a (pderiv b p)) := by
  rw [rayleigh_pre.pderiv_comm a b (pderiv c p)]
  rw [rayleigh_pre.pderiv_comm a c p]
  rw [rayleigh_pre.pderiv_comm b c (pderiv a p)]
  rw [rayleigh_pre.pderiv_comm a b p]

/-- Euler on the entry of the Hessian: (d-2) ∂a∂b g(w) = Σ_i w_i ∂a∂b∂i g(w) -/
lemma hessAt_entry_euler {n d : ℕ} (hd : 3 ≤ d) (g : H n d) (w : Fin n → ℝ) (a b : Fin n) :
    (∑ i : Fin n, w i * MvPolynomial.eval w (MvPolynomial.pderiv a (MvPolynomial.pderiv b (MvPolynomial.pderiv i g.1)))) =
      ((d - 2 : ℕ) : ℝ) * MvPolynomial.eval w (MvPolynomial.pderiv a (MvPolynomial.pderiv b g.1)) := by
  classical
  have hg' : g.1.IsHomogeneous d := by simpa [MvPolynomial.IsHomogeneous] using g.2
  have hqi : (MvPolynomial.pderiv b g.1).IsHomogeneous (d - 1) := by
    simpa using (hg'.pderiv (i := b))
  have hq : (MvPolynomial.pderiv a (MvPolynomial.pderiv b g.1)).IsHomogeneous (d - 2) := by
    have h1 : (MvPolynomial.pderiv a (MvPolynomial.pderiv b g.1)).IsHomogeneous ((d - 1) - 1) := by
      simpa using (hqi.pderiv (i := a))
    have hsub : (d - 1) - 1 = d - 2 := by omega
    simpa [hsub] using h1
  have heu := rayleigh_pre.euler_eval w (MvPolynomial.pderiv a (MvPolynomial.pderiv b g.1)) (d - 2) hq
  calc
    (∑ i : Fin n, w i * MvPolynomial.eval w
        (MvPolynomial.pderiv a (MvPolynomial.pderiv b (MvPolynomial.pderiv i g.1))))
        = ∑ i : Fin n, w i * MvPolynomial.eval w (MvPolynomial.pderiv i (MvPolynomial.pderiv a (MvPolynomial.pderiv b g.1))) := by
          apply Finset.sum_congr rfl
          intro i _
          congr 1
          congr 1
          exact pderiv3_comm a b i g.1
    _ = ((d - 2 : ℕ) : ℝ) * MvPolynomial.eval w (MvPolynomial.pderiv a (MvPolynomial.pderiv b g.1)) := by
          simpa using heu

/-- Euler with the partial-`H` element: Σ_i w_i eval(∂a∂b (∂ᵢg)) = (d-2) eval(∂a∂b g) -/
lemma hessAt_entry_euler_pderivS {n d : ℕ} (hd : 3 ≤ d) (g : H n d) (w : Fin n → ℝ) (a b : Fin n) :
    (∑ i : Fin n, w i * MvPolynomial.eval w (MvPolynomial.pderiv a (MvPolynomial.pderiv b (pderivS i g).1))) =
      ((d - 2 : ℕ) : ℝ) * MvPolynomial.eval w (MvPolynomial.pderiv a (MvPolynomial.pderiv b g.1)) := by
  classical
  calc
    (∑ i : Fin n, w i * MvPolynomial.eval w (MvPolynomial.pderiv a (MvPolynomial.pderiv b (pderivS i g).1)))
        = ∑ i : Fin n, w i * MvPolynomial.eval w (MvPolynomial.pderiv a (MvPolynomial.pderiv b (MvPolynomial.pderiv i g.1))) := by
          apply Finset.sum_congr rfl
          intro i _
          rw [pderivS_apply]
    _ = ((d - 2 : ℕ) : ℝ) * MvPolynomial.eval w (MvPolynomial.pderiv a (MvPolynomial.pderiv b g.1)) := by
          exact hessAt_entry_euler hd g w a b

/-- second Euler identity (row form): (d-2) e_aᵀ H_g(w) = wᵀ H_{∂a g}(w), entrywise -/
lemma hessAt_row_euler {n d : ℕ} (hd : 3 ≤ d) (g : H n d) (w : Fin n → ℝ) (a b : Fin n) :
    (∑ i : Fin n, w i * MvPolynomial.eval w
        (MvPolynomial.pderiv i (MvPolynomial.pderiv b (MvPolynomial.pderiv a g.1)))) =
      ((d - 2 : ℕ) : ℝ) * MvPolynomial.eval w (MvPolynomial.pderiv a (MvPolynomial.pderiv b g.1)) := by
  classical
  have hg' : g.1.IsHomogeneous d := by simpa [MvPolynomial.IsHomogeneous] using g.2
  have hqi : (MvPolynomial.pderiv b g.1).IsHomogeneous (d - 1) := by
    simpa using (hg'.pderiv (i := b))
  have hq : (MvPolynomial.pderiv a (MvPolynomial.pderiv b g.1)).IsHomogeneous (d - 2) := by
    have h1 : (MvPolynomial.pderiv a (MvPolynomial.pderiv b g.1)).IsHomogeneous ((d - 1) - 1) := by
      simpa using (hqi.pderiv (i := a))
    have hsub : (d - 1) - 1 = d - 2 := by omega
    simpa [hsub] using h1
  have heu := rayleigh_pre.euler_eval w (MvPolynomial.pderiv a (MvPolynomial.pderiv b g.1)) (d - 2) hq
  calc
    (∑ i : Fin n, w i * MvPolynomial.eval w
        (MvPolynomial.pderiv i (MvPolynomial.pderiv b (MvPolynomial.pderiv a g.1))))
        = ∑ i : Fin n, w i * MvPolynomial.eval w (MvPolynomial.pderiv i (MvPolynomial.pderiv a (MvPolynomial.pderiv b g.1))) := by
          apply Finset.sum_congr rfl
          intro i _
          congr 2
          rw [rayleigh_pre.pderiv_comm b a g.1]
    _ = ((d - 2 : ℕ) : ℝ) * MvPolynomial.eval w (MvPolynomial.pderiv a (MvPolynomial.pderiv b g.1)) := by
          simpa using heu

/-- row-euler with partial element: Σ_i w_i eval(∂i∂j(∂a g)(w)) = (d-2) eval(∂a∂j g)(w) -/
lemma hessAt_row_euler_pderivS {n d : ℕ} (hd : 3 ≤ d) (g : H n d) (w : Fin n → ℝ) (a j : Fin n) :
    (∑ i : Fin n, w i * MvPolynomial.eval w
        (MvPolynomial.pderiv i (MvPolynomial.pderiv j (pderivS a g).1))) =
      ((d - 2 : ℕ) : ℝ) * MvPolynomial.eval w (MvPolynomial.pderiv a (MvPolynomial.pderiv j g.1)) := by
  classical
  calc
    (∑ i : Fin n, w i * MvPolynomial.eval w
        (MvPolynomial.pderiv i (MvPolynomial.pderiv j (pderivS a g).1)))
        = ∑ i : Fin n, w i * MvPolynomial.eval w (MvPolynomial.pderiv i (MvPolynomial.pderiv j (MvPolynomial.pderiv a g.1))) := by
          apply Finset.sum_congr rfl
          intro i _
          rw [pderivS_apply]
    _ = ((d - 2 : ℕ) : ℝ) * MvPolynomial.eval w (MvPolynomial.pderiv a (MvPolynomial.pderiv j g.1)) := by
          exact hessAt_row_euler hd g w a j

-- ============================ Lefschetz / nonsingularity ============================

/-- Σ_a w_a (H_{∂a g}(w))_{ij} = (d-2) (H_g(w))_{ij} -/
lemma hessAt_wsum_entry {n d : ℕ} (hd : 3 ≤ d) (g : H n d) (w : Fin n → ℝ) (i j : Fin n) :
    (∑ a : Fin n, w a * hessAt w (pderivS a g) i j) =
      ((d - 2 : ℕ) : ℝ) * hessAt w g i j := by
  classical
  calc
    (∑ a : Fin n, w a * hessAt w (pderivS a g) i j)
        = ∑ a : Fin n, w a * MvPolynomial.eval w (MvPolynomial.pderiv i (MvPolynomial.pderiv j (pderivS a g).1)) := by
          apply Finset.sum_congr rfl
          intro a _
          congr 1
    _ = ((d - 2 : ℕ) : ℝ) * MvPolynomial.eval w (MvPolynomial.pderiv i (MvPolynomial.pderiv j g.1)) := by
          exact hessAt_entry_euler_pderivS hd g w i j
    _ = ((d - 2 : ℕ) : ℝ) * hessAt w g i j := by
          congr 1

/-- wᵀ H_{∂a g}(w) e_j = (d-2) (row a of H_g(w))_j -/
lemma hessAt_wwsum_entry {n d : ℕ} (hd : 3 ≤ d) (g : H n d) (w : Fin n → ℝ) (a j : Fin n) :
    (∑ i : Fin n, w i * hessAt w (pderivS a g) i j) =
      ((d - 2 : ℕ) : ℝ) * hessAt w g a j := by
  classical
  calc
    (∑ i : Fin n, w i * hessAt w (pderivS a g) i j)
        = ∑ i : Fin n, w i * MvPolynomial.eval w (MvPolynomial.pderiv i (MvPolynomial.pderiv j (pderivS a g).1)) := by
          apply Finset.sum_congr rfl
          intro i _
          congr 1
    _ = ((d - 2 : ℕ) : ℝ) * MvPolynomial.eval w (MvPolynomial.pderiv a (MvPolynomial.pderiv j g.1)) := by
          exact hessAt_row_euler_pderivS hd g w a j
    _ = ((d - 2 : ℕ) : ℝ) * hessAt w g a j := by
          congr 1

/-- the matrix identity `(d-2) • H_g(w) = Σ_i w_i • H_{∂i g}(w)` for d ≥ 3 -/
lemma hessAt_comb {n d : ℕ} (hd : 3 ≤ d) (g : H n d) (w : Fin n → ℝ) :
    (((d - 2 : ℕ) : ℝ) • hessAt w g) = ∑ i : Fin n, w i • hessAt w (pderivS i g) := by
  classical
  ext a b
  rw [WitEx.matrix_sum_smul_apply n w (fun a : Fin n => hessAt w (pderivS a g)) a b]
  rw [Matrix.smul_apply]
  simp only [smul_eq_mul]
  rw [hessAt_wsum_entry hd g w a b]

/-- quadReal is linear in the first (matrix) argument: addition -/
lemma shn_quadReal_add_left (n : ℕ) (A B : Matrix (Fin n) (Fin n) ℝ) (x y : Fin n → ℝ) :
    Commons.LinearAlgebra.Matrix.quadReal (A + B) x y =
      Commons.LinearAlgebra.Matrix.quadReal A x y + Commons.LinearAlgebra.Matrix.quadReal B x y := by
  classical
  calc
    Commons.LinearAlgebra.Matrix.quadReal (A + B) x y
        = x ⬝ᵥ ((A + B) *ᵥ y) := by
            rw [Commons.LinearAlgebra.Matrix.quadReal_mulVec]
    _ = x ⬝ᵥ (A *ᵥ y + B *ᵥ y) := by
            rw [add_mulVec]
    _ = x ⬝ᵥ (A *ᵥ y) + x ⬝ᵥ (B *ᵥ y) := by
            rw [dotProduct_add]
    _ = Commons.LinearAlgebra.Matrix.quadReal A x y + Commons.LinearAlgebra.Matrix.quadReal B x y := by
            rw [Commons.LinearAlgebra.Matrix.quadReal_mulVec]
            rw [Commons.LinearAlgebra.Matrix.quadReal_mulVec]

/-- quadReal is linear in the first (matrix) argument: scalar -/
lemma shn_quadReal_smul_left (n : ℕ) (c : ℝ) (A : Matrix (Fin n) (Fin n) ℝ) (x y : Fin n → ℝ) :
    Commons.LinearAlgebra.Matrix.quadReal (c • A) x y =
      c * Commons.LinearAlgebra.Matrix.quadReal A x y := by
  classical
  calc
    Commons.LinearAlgebra.Matrix.quadReal (c • A) x y
        = x ⬝ᵥ ((c • A) *ᵥ y) := by
            rw [Commons.LinearAlgebra.Matrix.quadReal_mulVec]
    _ = x ⬝ᵥ (c • (A *ᵥ y)) := by
            rw [smul_mulVec]
    _ = c • (x ⬝ᵥ (A *ᵥ y)) := by
            rw [dotProduct_smul]
    _ = c * Commons.LinearAlgebra.Matrix.quadReal A x y := by
            rw [Commons.LinearAlgebra.Matrix.quadReal_mulVec]
            rw [smul_eq_mul]

/-- the quadratic form of the first argument is linear -/
def shn_quadRealLin (n : ℕ) (x : Fin n → ℝ) : Matrix (Fin n) (Fin n) ℝ →ₗ[ℝ] ℝ where
  toFun := fun A => Commons.LinearAlgebra.Matrix.quadReal A x x
  map_add' := by intro A B; exact shn_quadReal_add_left n A B x x
  map_smul' := by intro c A; exact shn_quadReal_smul_left n c A x x

/-- quadReal distributes over a weighted sum of matrices -/
lemma shn_quadReal_smul_sum (n : ℕ) (c : Fin n → ℝ) (A : Fin n → Matrix (Fin n) (Fin n) ℝ)
    (x : Fin n → ℝ) :
    (∑ i : Fin n, c i * Commons.LinearAlgebra.Matrix.quadReal (A i) x x) =
      Commons.LinearAlgebra.Matrix.quadReal (∑ i : Fin n, c i • A i) x x := by
  classical
  let L : Matrix (Fin n) (Fin n) ℝ →ₗ[ℝ] ℝ := shn_quadRealLin n x
  change (∑ i : Fin n, c i * L (A i)) = L (∑ i : Fin n, c i • A i)
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [map_smul]
  change c i • L (A i) = c i * L (A i)
  rw [smul_eq_mul]

/-- Σ_a w_a xᵀH_{∂a g}(w)x = (d-2) xᵀH_g(w)x -/
lemma quadReal_sum_hessAt {n d : ℕ} (hd : 3 ≤ d) (g : H n d) (w x : Fin n → ℝ) :
    (∑ a : Fin n, w a * Commons.LinearAlgebra.Matrix.quadReal (hessAt w (pderivS a g)) x x) =
      ((d - 2 : ℕ) : ℝ) * Commons.LinearAlgebra.Matrix.quadReal (hessAt w g) x x := by
  classical
  calc
    (∑ a : Fin n, w a * Commons.LinearAlgebra.Matrix.quadReal (hessAt w (pderivS a g)) x x)
        = Commons.LinearAlgebra.Matrix.quadReal (∑ a : Fin n, w a • hessAt w (pderivS a g)) x x := by
          rw [shn_quadReal_smul_sum]
    _ = Commons.LinearAlgebra.Matrix.quadReal ((((d - 2 : ℕ) : ℝ) • hessAt w g)) x x := by
          rw [hessAt_comb hd g w]
    _ = ((d - 2 : ℕ) : ℝ) * Commons.LinearAlgebra.Matrix.quadReal (hessAt w g) x x := by
          rw [shn_quadReal_smul_left]

/-- for x: wᵀH_{∂a g}(w) x = (d-2) (H_g(w)x)_a -/
lemma quadReal_hessAt_wx {n d : ℕ} (hd : 3 ≤ d) (g : H n d) (w x : Fin n → ℝ) (a : Fin n) :
    Commons.LinearAlgebra.Matrix.quadReal (hessAt w (pderivS a g)) w x =
      ((d - 2 : ℕ) : ℝ) * (hessAt w g *ᵥ x) a := by
  classical
  calc
    Commons.LinearAlgebra.Matrix.quadReal (hessAt w (pderivS a g)) w x
        = Commons.LinearAlgebra.Matrix.quadReal (hessAt w (pderivS a g)) x w := by
            exact Commons.LinearAlgebra.Matrix.quadReal_symm (hessAt w (pderivS a g))
              (hessAt_symm n (d - 1) w (pderivS a g)) w x
    _ = x ⬝ᵥ (hessAt w (pderivS a g) *ᵥ w) := by
            rw [Commons.LinearAlgebra.Matrix.quadReal_mulVec]
    _ = ∑ j : Fin n, x j * (∑ i : Fin n, hessAt w (pderivS a g) j i * w i) := by
            apply Finset.sum_congr rfl
            intro j _
            simp [Matrix.mulVec, dotProduct]
    _ = ∑ j : Fin n, x j * (((d - 2 : ℕ) : ℝ) * hessAt w g a j) := by
            apply Finset.sum_congr rfl
            intro j _
            congr 1
            calc
              (∑ i : Fin n, hessAt w (pderivS a g) j i * w i)
                  = ∑ i : Fin n, w i * hessAt w (pderivS a g) i j := by
                    apply Finset.sum_congr rfl
                    intro i _
                    rw [Matrix.IsSymm.ext_iff.mp (hessAt_symm n (d - 1) w (pderivS a g)) j i]
                    ring
              _ = ((d - 2 : ℕ) : ℝ) * hessAt w g a j := by
                    exact hessAt_wwsum_entry hd g w a j
    _ = ((d - 2 : ℕ) : ℝ) * (∑ j : Fin n, hessAt w g a j * x j) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro j _
          ring
    _ = ((d - 2 : ℕ) : ℝ) * (hessAt w g *ᵥ x) a := by
          rw [show (hessAt w g *ᵥ x) a = (∑ j : Fin n, hessAt w g a j * x j) by
            simp [Matrix.mulVec, dotProduct]]

/-- quadReal A w w > 0 for the Hessian of a partial of a strict polynomial -/
lemma hessAt_quadReal_ww_pos {n d : ℕ} (hn : 0 < n) (hd : 3 ≤ d) (g : H n d) (hg : g ∈ Ŀ n d)
    (w : Fin n → ℝ) (hw : ∀ k : Fin n, 0 < w k) (a : Fin n) :
    0 < Commons.LinearAlgebra.Matrix.quadReal (hessAt w (pderivS a g)) w w := by
  classical
  have hpos : 0 < MvPolynomial.eval w (MvPolynomial.pderiv a g.1) :=
    Ŀ_pderiv_eval_pos hn (by omega : 2 ≤ d) g hg a hw
  let p : MvPolynomial (Fin n) ℝ := MvPolynomial.pderiv a g.1
  have hp_hom : p.IsHomogeneous (d - 1) := by
    have hg' : g.1.IsHomogeneous d := by simpa [MvPolynomial.IsHomogeneous] using g.2
    simpa using (hg'.pderiv (i := a))
  have hhd : 1 ≤ d - 1 := by omega
  have hcast : (d - 1) - 1 = d - 2 := by omega
  have heu := rayleigh_pre.quadReal_hess_w p w w hhd hp_hom
  have heuler := rayleigh_pre.euler_eval w p (d - 1) hp_hom
  have hmain : Commons.LinearAlgebra.Matrix.quadReal (hessAt w (pderivS a g)) w w =
      ((d - 2 : ℕ) : ℝ) * ((d - 1 : ℕ) : ℝ) * MvPolynomial.eval w p := by
    calc
      Commons.LinearAlgebra.Matrix.quadReal (hessAt w (pderivS a g)) w w
          = Commons.LinearAlgebra.Matrix.quadReal (rayleigh_pre.hess p w) w w := by
            unfold hessAt
            rfl
      _ = ((d - 2 : ℕ) : ℝ) * (∑ b : Fin n, w b * MvPolynomial.eval w (MvPolynomial.pderiv b p)) := by
            simpa [hcast] using heu
      _ = ((d - 2 : ℕ) : ℝ) * ((d - 1 : ℕ) : ℝ) * MvPolynomial.eval w p := by
            rw [heuler]
            ring
  rw [hmain]
  have hd2pos : 0 < (d - 2 : ℕ) := by omega
  have hd1pos : 0 < (d - 1 : ℕ) := by omega
  exact mul_pos (mul_pos (by exact_mod_cast hd2pos) (by exact_mod_cast hd1pos)) hpos

/-- linear algebra: `∑_i w_i q_i = 0` with `q_i ≤ 0` and `w_i > 0` forces `q_i = 0` -/
lemma sum_zero_of_nonpos_terms {n : ℕ} (w : Fin n → ℝ) (hw : ∀ i : Fin n, 0 < w i)
    (q : Fin n → ℝ) (hqle : ∀ i : Fin n, q i ≤ 0) (hsum : (∑ i : Fin n, w i * q i) = 0) :
    ∀ i : Fin n, q i = 0 := by
  classical
  intro i
  by_contra hne
  have hlt : w i * q i < 0 := by
    have hq : q i < 0 := lt_of_le_of_ne (hqle i) hne
    exact mul_neg_of_pos_of_neg (hw i) hq
  have hsum_erase_le : (∑ j ∈ (Finset.univ.erase i), w j * q j) ≤ 0 := by
    apply Finset.sum_nonpos
    intro j hj
    exact mul_nonpos_of_nonneg_of_nonpos (le_of_lt (hw j)) (hqle j)
  have hreassoc : (∑ j : Fin n, w j * q j) = (∑ j ∈ (Finset.univ.erase i), w j * q j) + w i * q i := by
    rw [← Finset.sum_erase_add (Finset.univ) (fun j : Fin n => w j * q j) (a := i) (by simp)]
  have hsum_lt : (∑ j : Fin n, w j * q j) < 0 := by
    rw [hreassoc]
    exact add_neg_of_nonpos_of_neg hsum_erase_le hlt
  linarith

/-- nonsingularity at degree d from the (nonsingular, index) properties at degree d-1 -/
lemma strict_nonsing_step {n d : ℕ} (hn : 0 < n) (hd : 3 ≤ d)
    (g : H n d) (hg : g ∈ Ŀ n d) (w : Fin n → ℝ) (hw : ∀ k : Fin n, 0 < w k)
    (hprev : ∀ i : Fin n, (hessAt w (pderivS i g)).det ≠ 0 ∧ posRoots (hessAt w (pderivS i g)) ≤ 1) :
    (hessAt w g).det ≠ 0 := by
  classical
  let A : Matrix (Fin n) (Fin n) ℝ := hessAt w g
  let Aa : Fin n → Matrix (Fin n) (Fin n) ℝ := fun a => hessAt w (pderivS a g)
  have hAa_symm : ∀ a : Fin n, (Aa a).IsSymm := fun a => hessAt_symm n (d - 1) w (pderivS a g)
  have hAa_nonsing : ∀ a : Fin n, (Aa a).det ≠ 0 := fun a => (hprev a).1
  have hAa_index : ∀ a : Fin n, posRoots (Aa a) ≤ 1 := fun a => (hprev a).2
  have hAa_pos : ∀ a : Fin n, 0 < Commons.LinearAlgebra.Matrix.quadReal (Aa a) w w := fun a =>
    hessAt_quadReal_ww_pos hn hd g hg w hw a
  have hker_triv : ∀ x : Fin n → ℝ, A *ᵥ x = 0 → x = 0 := by
    intro x hx
    have hqa0 : ∀ a : Fin n, Commons.LinearAlgebra.Matrix.quadReal (Aa a) w x = 0 := by
      intro a
      have hstep : Commons.LinearAlgebra.Matrix.quadReal (Aa a) w x =
          ((d - 2 : ℕ) : ℝ) * (A *ᵥ x) a := by
        simpa [Aa, A] using (quadReal_hessAt_wx hd g w x a)
      have hAa0 : (A *ᵥ x) a = 0 := by
        rw [hx]
        simp
      rw [hstep, hAa0]
      simp
    have hxxA : Commons.LinearAlgebra.Matrix.quadReal A x x = 0 := by
      rw [Commons.LinearAlgebra.Matrix.quadReal_mulVec A x x]
      rw [hx]
      simp
    have hsum0 : (∑ a : Fin n, w a * Commons.LinearAlgebra.Matrix.quadReal (Aa a) x x) = 0 := by
      calc
        (∑ a : Fin n, w a * Commons.LinearAlgebra.Matrix.quadReal (Aa a) x x)
            = ((d - 2 : ℕ) : ℝ) * Commons.LinearAlgebra.Matrix.quadReal A x x := by
              simpa [Aa, A] using (quadReal_sum_hessAt hd g w x)
        _ = 0 := by simp [hxxA]
    have hqa_le0 : ∀ a : Fin n, Commons.LinearAlgebra.Matrix.quadReal (Aa a) x x ≤ 0 := by
      intro a
      exact (Commons.LinearAlgebra.Matrix.quadReal_hyperplane_negDef (Aa a) (hAa_symm a) (hAa_nonsing a)
        (hAa_index a) w (hAa_pos a) x (hqa0 a)).1
    have hq0 : ∀ a : Fin n, Commons.LinearAlgebra.Matrix.quadReal (Aa a) x x = 0 := by
      intro a
      exact sum_zero_of_nonpos_terms w hw (fun i => Commons.LinearAlgebra.Matrix.quadReal (Aa i) x x) hqa_le0 hsum0 a
    have hAa_x0 : ∀ a : Fin n, (Aa a) *ᵥ x = 0 := by
      intro a
      exact (Commons.LinearAlgebra.Matrix.quadReal_hyperplane_negDef (Aa a) (hAa_symm a) (hAa_nonsing a)
        (hAa_index a) w (hAa_pos a) x (hqa0 a)).2 (hq0 a)
    haveI : Nonempty (Fin n) := Fin.pos_iff_nonempty.mp hn
    let a0 : Fin n := ⟨0, hn⟩
    have hx0' : (Aa a0) *ᵥ x = 0 := hAa_x0 a0
    have hunit_a0 : IsUnit (Aa a0) := by
      exact (Matrix.isUnit_iff_isUnit_det (Aa a0)).mpr (isUnit_iff_ne_zero.mpr (hAa_nonsing a0))
    have hinj : Function.Injective ((Aa a0).mulVec) :=
      (Matrix.mulVec_injective_iff_isUnit).mpr hunit_a0
    exact hinj (by simpa using hx0')
  have hinjA : Function.Injective (A.mulVec) := by
    intro x y hxy
    have hdiff : A *ᵥ (x - y) = 0 := by
      rw [Matrix.mulVec_sub, hxy]
      simp
    have hxy0 : x - y = 0 := hker_triv (x - y) hdiff
    funext k
    exact sub_eq_zero.mp (congrFun hxy0 k)
  have hunitA : IsUnit A := (Matrix.mulVec_injective_iff_isUnit).mp hinjA
  have hdet : A.det ≠ 0 := by
    have hu : IsUnit A.det := (Matrix.isUnit_iff_isUnit_det A).mp hunitA
    exact isUnit_iff_ne_zero.mp hu
  simpa [A] using hdet

-- ============================ index via connectivity ============================

/-- hessAt is linear in the polynomial -/
def hessAtLin (n d : ℕ) (w : Fin n → ℝ) : H n d →ₗ[ℝ] Matrix (Fin n) (Fin n) ℝ where
  toFun := hessAt w
  map_add' := by
    intro f g
    ext a b
    change MvPolynomial.eval w (MvPolynomial.pderiv a (MvPolynomial.pderiv b ((f + g : H n d).1))) =
      MvPolynomial.eval w (MvPolynomial.pderiv a (MvPolynomial.pderiv b f.1)) +
        MvPolynomial.eval w (MvPolynomial.pderiv a (MvPolynomial.pderiv b g.1))
    rw [show ((f + g : H n d).1) = f.1 + g.1 by rfl]
    rw [(MvPolynomial.pderiv b).map_add]
    rw [(MvPolynomial.pderiv a).map_add]
    rw [(MvPolynomial.eval w).map_add]
  map_smul' := by
    intro r f
    ext a b
    change MvPolynomial.eval w (MvPolynomial.pderiv a (MvPolynomial.pderiv b ((r • f : H n d).1))) =
      r * MvPolynomial.eval w (MvPolynomial.pderiv a (MvPolynomial.pderiv b f.1))
    rw [show ((r • f : H n d).1) = r • f.1 by rfl]
    rw [(MvPolynomial.pderiv b).map_smul]
    rw [(MvPolynomial.pderiv a).map_smul]
    rw [Algebra.smul_def]
    rw [map_mul]
    simp

/-- hessAt at fixed w is continuous -/
lemma hessAt_continuous (n d : ℕ) (w : Fin n → ℝ) : Continuous (hessAt (n := n) (d := d) w) := by
  have hcont : Continuous (hessAtLin n d w) := IsModuleTopology.continuous_of_linearMap (hessAtLin n d w)
  simpa [hessAtLin] using hcont

/-- an element of `P n d` (n ≥ 1) is nonzero -/
lemma mem_P_ne_zero {n d : ℕ} (hn : 0 < n) (g : H n d) (hg : g ∈ P n d) : g.1 ≠ 0 := by
  classical
  let i0 : Fin n := ⟨0, hn⟩
  let m : Fin n →₀ ℕ := Finsupp.single i0 d
  have hm : Finsupp.weight (1 : Fin n → ℕ) m = d := by
    simp [m, Finsupp.weight_single]
  intro h0
  have hcoeff : 0 < g.1.coeff m := hg m hm
  have : g.1.coeff m = 0 := by rw [h0]; simp
  linarith

/-- at most one positive eigenvalue for the Hessian of strict polynomials, obtained from
preconnectedness of `Ŀ` and the stable elements inside it -/
lemma strict_index_of_connectivity (n d : ℕ) (hn : 0 < n) (hd : 2 ≤ d)
    (hconn : IsPreconnected (Ŀ n d))
    (hloc : ∀ A : Matrix (Fin n) (Fin n) ℝ, A.IsSymm → A.det ≠ 0 →
      ∃ U : Set (Matrix (Fin n) (Fin n) ℝ), U ∈ nhds A ∧
        ∀ B : Matrix (Fin n) (Fin n) ℝ, B ∈ U → B.IsSymm →
          (B.charpoly.roots.filter (fun r : ℝ => 0 < r)).card =
            (A.charpoly.roots.filter (fun r : ℝ => 0 < r)).card)
    (hnonsing : ∀ g : H n d, g ∈ Ŀ n d → ∀ w : Fin n → ℝ, (∀ k : Fin n, 0 < w k) →
      (hessAt w g).det ≠ 0) :
    ∀ g : H n d, g ∈ Ŀ n d → ∀ w : Fin n → ℝ, (∀ k : Fin n, 0 < w k) →
      posRoots (hessAt w g) ≤ 1 := by
  classical
  intro g hg w hw
  let X : Type := ↥(Ŀ n d)
  let F : X → ℕ := fun u => posRoots (hessAt w u.1)
  haveI : PreconnectedSpace X := Subtype.preconnectedSpace hconn
  have hF_loc : IsLocallyConstant F := by
    rw [IsLocallyConstant.iff_eventually_eq]
    intro x
    let A0 : Matrix (Fin n) (Fin n) ℝ := hessAt w x.1
    have hA0_nonsing : A0.det ≠ 0 := hnonsing x.1 x.2 w hw
    rcases hloc A0 (hessAt_symm n d w x.1) hA0_nonsing with ⟨U0, hU0nhds, hU0⟩
    have hcontX : Continuous (fun y : X => hessAt w y.1) :=
      (hessAt_continuous n d w).comp continuous_subtype_val
    have ht : Filter.Tendsto (fun y : X => hessAt w y.1) (𝓝 x) (𝓝 A0) :=
      hcontX.continuousAt.tendsto
    rw [Filter.eventually_iff_exists_mem]
    refine ⟨{y : X | hessAt w y.1 ∈ U0}, ht hU0nhds, ?_⟩
    intro y hy
    change posRoots (hessAt w y.1) = posRoots (hessAt w x.1)
    change ((hessAt w y.1).charpoly.roots.filter (fun r : ℝ => 0 < r)).card =
      ((hessAt w x.1).charpoly.roots.filter (fun r : ℝ => 0 < r)).card
    exact hU0 (hessAt w y.1) hy (hessAt_symm n d w y.1)
  have hF_eq : ∀ y : X, F y = F ⟨g, hg⟩ := fun y =>
    hF_loc.apply_eq_of_preconnectedSpace y ⟨g, hg⟩
  rcases WitEx.exists_strict_stable_in_intersection n d hn with ⟨g0, hg0Ŀ, hg0S⟩
  have hg0ne : g0.1 ≠ 0 := mem_P_ne_zero hn g0 (Ŀ_subset_P n d hg0Ŀ)
  have hbound : posRoots (hessAt w g0) ≤ 1 := by
    have hb := stable_hessian_posRoots_le_one n d hd g0 hg0S hg0ne w hw
    simpa [posRoots, hessAt] using hb
  calc
    posRoots (hessAt w g) = posRoots (hessAt w g0) := by
      exact (hF_eq ⟨g0, hg0Ŀ⟩).symm
    _ ≤ 1 := hbound

-- ============================ main induction ============================

/-- joint induction: nonsingularity and index for strict polynomials of every degree -/
lemma strict_props_by_induction (n : ℕ) (hn : 0 < n)
    (hconn : ∀ d : ℕ, IsPreconnected (Ŀ n d))
    (hloc : ∀ d : ℕ, ∀ A : Matrix (Fin n) (Fin n) ℝ, A.IsSymm → A.det ≠ 0 →
      ∃ U : Set (Matrix (Fin n) (Fin n) ℝ), U ∈ nhds A ∧
        ∀ B : Matrix (Fin n) (Fin n) ℝ, B ∈ U → B.IsSymm →
          (B.charpoly.roots.filter (fun r : ℝ => 0 < r)).card =
            (A.charpoly.roots.filter (fun r : ℝ => 0 < r)).card) :
    ∀ d : ℕ, 2 ≤ d →
      (∀ (g : H n d), g ∈ Ŀ n d → ∀ (w : Fin n → ℝ), (∀ k : Fin n, 0 < w k) →
        (hessAt w g).det ≠ 0) ∧
      (∀ (g : H n d), g ∈ Ŀ n d → ∀ (w : Fin n → ℝ), (∀ k : Fin n, 0 < w k) →
        posRoots (hessAt w g) ≤ 1) := by
  classical
  intro d
  refine Nat.le_induction ?base ?step d
  · constructor
    · intro g hg w hw
      exact strict_two_nonsing n g hg w
    · intro g hg w hw
      exact strict_two_index g hg w
  · intro d hd ih
    have hAnext : ∀ (g : H n (d + 1)), g ∈ Ŀ n (d + 1) → ∀ (w : Fin n → ℝ),
        (∀ k : Fin n, 0 < w k) → (hessAt w g).det ≠ 0 := by
      intro g hg w hw
      have hprev : ∀ i : Fin n,
          (hessAt w (pderivS i g)).det ≠ 0 ∧ posRoots (hessAt w (pderivS i g)) ≤ 1 := by
        intro i
        have hp : pderivS i g ∈ Ŀ n d := by
          have hm : pderivS i g ∈ Ŀ n ((d + 1) - 1) :=
            Ŀ_pderiv_mem (n := n) (d := d + 1) (by omega : 3 ≤ d + 1) g hg i
          simpa using hm
        exact ⟨ih.1 (pderivS i g) hp w hw, ih.2 (pderivS i g) hp w hw⟩
      exact strict_nonsing_step hn (by omega : 3 ≤ d + 1) g hg w hw hprev
    constructor
    · exact hAnext
    · apply strict_index_of_connectivity n (d + 1) hn (by omega : 2 ≤ d + 1)
        (hconn (d + 1)) (hloc (d + 1)) hAnext

/-- Theorem 2.16 (HR) for strictly Lorentzian polynomials: the Hessian at any positive point
is nonsingular, and its characteristic polynomial has at most one positive root. -/
theorem strict_hessian_nonsing_and_index (n d : ℕ) (hn : 0 < n) (hd : 2 ≤ d) :
    (∀ (g : H n d), g ∈ Ŀ n d → ∀ (w : Fin n → ℝ), (∀ k : Fin n, 0 < w k) →
      (Matrix.of (fun a b : Fin n => MvPolynomial.eval w
        (MvPolynomial.pderiv a (MvPolynomial.pderiv b g.1)))).det ≠ 0) ∧
    (∀ (g : H n d), g ∈ Ŀ n d → ∀ (w : Fin n → ℝ), (∀ k : Fin n, 0 < w k) →
      ((Matrix.of (fun a b : Fin n => MvPolynomial.eval w
        (MvPolynomial.pderiv a (MvPolynomial.pderiv b g.1)))).charpoly.roots.filter
          (fun r : ℝ => 0 < r)).card ≤ 1) := by
  rcases strict_props_by_induction n hn
    (fun e : ℕ => strictLorentzian_preconnected n e hn)
    (fun e : ℕ => fun A hA hreg =>
      Commons.LinearAlgebra.Matrix.posRoots_card_locallyConstant (n := n) A hA hreg)
    d hd with ⟨hns, hidx⟩
  constructor
  · intro g hg w hw
    change (hessAt w g).det ≠ 0
    exact hns g hg w hw
  · intro g hg w hw
    change posRoots (hessAt w g) ≤ 1
    exact hidx g hg w hw
