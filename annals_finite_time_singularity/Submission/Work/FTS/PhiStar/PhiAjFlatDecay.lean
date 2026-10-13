/-
# `Work.FTS.PhiStar.PhiAjFlatDecay` — flat decay of the `𝒜`-iterates of the radial profile

For `𝒜 = α z²∂_zz + (5+α) z∂_z` and `φ(z) = 2z/(1+z)² = VocabO.phiR` the file
`StarDefs.lean` defines `phiAj j α = 𝒜^j φ`.  The consumer
`PhiStar/RadialWAux/RadGreenDivFlat` (radial Green function estimate) needs the two-sided
*flat* bounds

* `|∂_t^k (phiAj j α) t| ≤ A/(1+t^{k+1})`,
* `|∂_t^k (phiAj j α · / ·) t| ≤ A/(1+t^{k+2})`

for `j ≤ 6`, `k ≤ 14`, `t > 0`.

## The mathematics

`𝒜` preserves the class of *rational functions with all poles at `z = -1`*:

  `f(z) = P(z)/(1+z)^n  ⟹  f'(z) = (numStep n P)(z)/(1+z)^{n+1}`,
  `numStep n P = P'·(1+X) - n·P`,   `deg (numStep n P) ≤ deg P`,

and applying `𝒜` once more with the `z², z` prefactors raises the degree bound by `2` while
the denominator exponent grows by `2`.  Starting from `P₀ = 2X`, `n₀ = 2`, the iterates keep
`deg P_j ≤ n_j - 1 = 2j+1` **and** are divisible by `X` (because the `𝒜`-step has the form
`X²·(…) + X(1+X)·(…)`).  Consequently

* `phiAj j α = P_j(z)/(1+z)^{2j+2}` with `deg P_j ≤ 2j+1`, and
* `phiAj j α / z = (P_j.divX)(z)/(1+z)^{2j+2}` with `deg (P_j.divX) ≤ 2j`.

Since the `k`-th derivative of `P(z)/(1+z)^{d+s}` has numerator `numIter (d+s) P k` of degree
`≤ d` and denominator `(1+z)^{d+s+k}`, each such derivative is `O((1+t)^{-(s+k)})` — which is
exactly the two bounds above with `(d,s) = (2j+1,1)` resp. `(2j,2)`.

## What is in this file

* the derivative/degree calculus of `numStep`/`numIter` (`deriv_rat`, `iteratedDeriv_rat`,
  `poly_eval_bound`, `rat_iteratedDeriv_bound`);
* the two numerators `phiAjNum` (numerator of `phiAj j α`) and `phiAjNumDiv` (its `divX`),
  their degree bounds and the two representation lemmas `phiAj_eqOn_num`, `phiAj_div_eqOn_num`;
* the assembly `PhiAjFlatDecay` with a completely explicit constant.
-/
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Polynomial.Div
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.FTS.PhiStar.StarDefs
import Submission.Work.FTS.PhiStar.Defs
import Submission.Work.FTS.PhiStar.Basic

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open scoped Real Topology
open Set Filter Polynomial

namespace Work.FTS.PhiStar

set_option autoImplicit false

/-! ## 1. The derivative numerator of `z ↦ P(z)/(1+z)^n` -/

/-- The numerator of the derivative of `P(z)/(1+z)^n`: `P'(X)·(1+X) − n·P(X)`. -/
noncomputable def numStep (n : ℕ) (P : Polynomial ℝ) : Polynomial ℝ :=
  Polynomial.derivative P * (1 + Polynomial.X) - Polynomial.C (n : ℝ) * P

/-- The `k`-fold iterate of `numStep` (the numerator of the `k`-th derivative of
`P(z)/(1+z)^n`). -/
noncomputable def numIter (n : ℕ) (P : Polynomial ℝ) : ℕ → Polynomial ℝ
  | 0 => P
  | (k + 1) => numStep (n + k) (numIter n P k)

lemma numIter_zero (n : ℕ) (P : Polynomial ℝ) : numIter n P 0 = P := rfl

lemma numIter_succ (n : ℕ) (P : Polynomial ℝ) (k : ℕ) :
    numIter n P (k + 1) = numStep (n + k) (numIter n P k) := rfl

lemma numStep_eval (n : ℕ) (P : Polynomial ℝ) (z : ℝ) :
    (numStep n P).eval z = P.derivative.eval z * (1 + z) - (n : ℝ) * P.eval z := by
  simp only [numStep, Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_add,
    Polynomial.eval_one, Polynomial.eval_X, Polynomial.eval_C]

lemma natDegree_one_add_X_le : (1 + Polynomial.X : Polynomial ℝ).natDegree ≤ 1 := by
  have h1 : (1 : Polynomial ℝ).natDegree = 0 := Polynomial.natDegree_one
  have h2 : (Polynomial.X : Polynomial ℝ).natDegree ≤ 1 := Polynomial.natDegree_X_le
  have h3 := Polynomial.natDegree_add_le (1 : Polynomial ℝ) Polynomial.X
  omega

lemma numStep_natDegree_le {n d : ℕ} (hd : 1 ≤ d) {P : Polynomial ℝ} (hP : P.natDegree ≤ d) :
    (numStep n P).natDegree ≤ d := by
  have hder : (Polynomial.derivative P).natDegree ≤ d - 1 :=
    (Polynomial.natDegree_derivative_le P).trans (by omega)
  have hmul : (Polynomial.derivative P * (1 + Polynomial.X)).natDegree ≤ d := by
    have h := Polynomial.natDegree_mul_le (p := Polynomial.derivative P)
      (q := 1 + Polynomial.X)
    have hX := natDegree_one_add_X_le
    omega
  have hC : (Polynomial.C (n : ℝ) * P).natDegree ≤ d :=
    (Polynomial.natDegree_C_mul_le _ _).trans hP
  rw [numStep]
  exact (Polynomial.natDegree_sub_le _ _).trans (max_le hmul hC)

/-- `numStep` never increases the degree (also when the degree is `0`). -/
lemma numStep_natDegree_le_self (m : ℕ) (Q : Polynomial ℝ) :
    (numStep m Q).natDegree ≤ Q.natDegree := by
  rcases Nat.eq_zero_or_pos Q.natDegree with h0 | hpos
  · rw [numStep, Polynomial.derivative_of_natDegree_zero h0, zero_mul, zero_sub,
      Polynomial.natDegree_neg]
    exact Polynomial.natDegree_C_mul_le _ _
  · exact numStep_natDegree_le hpos le_rfl

lemma numIter_natDegree_le (n : ℕ) (P : Polynomial ℝ) (k : ℕ) :
    (numIter n P k).natDegree ≤ P.natDegree := by
  induction k with
  | zero => rw [numIter_zero]
  | succ k ih => rw [numIter_succ]; exact (numStep_natDegree_le_self _ _).trans ih

/-- `z ↦ (1+z)^p` has the expected derivative. -/
lemma hasDerivAt_one_add_pow (p : ℕ) (z : ℝ) :
    HasDerivAt (fun w : ℝ => (1 + w) ^ p) ((p : ℝ) * (1 + z) ^ (p - 1)) z := by
  have hpoly : (fun w : ℝ => (1 + w) ^ p)
      = fun w : ℝ => ((1 + Polynomial.X : Polynomial ℝ) ^ p).eval w := by
    funext w
    simp [Polynomial.eval_pow, Polynomial.eval_add, Polynomial.eval_one, Polynomial.eval_X]
  rw [hpoly]
  have hder := Polynomial.hasDerivAt ((1 + Polynomial.X : Polynomial ℝ) ^ p) z
  convert hder using 1
  rw [Polynomial.derivative_pow]
  simp [Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_C, Polynomial.eval_one,
    Polynomial.eval_add, Polynomial.eval_X, Polynomial.derivative_add,
    Polynomial.derivative_one, Polynomial.derivative_X]

/-- **The derivative of a rational function with a single pole at `-1`.** -/
lemma deriv_rat (P : Polynomial ℝ) (n : ℕ) (hn : 1 ≤ n) {z : ℝ} (hz : z ≠ -1) :
    deriv (fun w : ℝ => P.eval w / (1 + w) ^ n) z
      = (numStep n P).eval z / (1 + z) ^ (n + 1) := by
  have ha : (1 : ℝ) + z ≠ 0 := by intro h; exact hz (by linarith)
  have h1 : HasDerivAt (fun w : ℝ => P.eval w) (P.derivative.eval z) z :=
    Polynomial.hasDerivAt P z
  have h2 : HasDerivAt (fun w : ℝ => (1 + w) ^ n) ((n : ℝ) * (1 + z) ^ (n - 1)) z :=
    hasDerivAt_one_add_pow n z
  have hdiv : HasDerivAt (fun w : ℝ => P.eval w / (1 + w) ^ n)
      ((P.derivative.eval z * (1 + z) ^ n - P.eval z * ((n : ℝ) * (1 + z) ^ (n - 1)))
        / ((1 + z) ^ n) ^ 2) z := h1.div h2 (pow_ne_zero n ha)
  rw [hdiv.deriv, numStep_eval]
  rw [div_eq_div_iff (pow_ne_zero 2 (pow_ne_zero n ha)) (pow_ne_zero (n + 1) ha)]
  have e1 : (1 + z) ^ n * (1 + z) ^ (n + 1) = (1 + z) ^ (2 * n + 1) := by
    rw [← pow_add]; congr 1; omega
  have e2 : (1 + z) ^ (n - 1) * (1 + z) ^ (n + 1) = (1 + z) ^ (2 * n) := by
    rw [← pow_add]; congr 1; omega
  have e3 : (1 + z) * (1 + z) ^ (2 * n) = (1 + z) ^ (2 * n + 1) :=
    (pow_succ' (1 + z) (2 * n)).symm
  have e4 : ((1 + z) ^ n) ^ 2 = (1 + z) ^ (2 * n) := by
    rw [← pow_mul]; congr 1; ring
  calc (P.derivative.eval z * (1 + z) ^ n - P.eval z * ((n : ℝ) * (1 + z) ^ (n - 1)))
        * (1 + z) ^ (n + 1)
      = P.derivative.eval z * ((1 + z) ^ n * (1 + z) ^ (n + 1))
        - (n : ℝ) * P.eval z * ((1 + z) ^ (n - 1) * (1 + z) ^ (n + 1)) := by ring
    _ = P.derivative.eval z * (1 + z) ^ (2 * n + 1)
        - (n : ℝ) * P.eval z * (1 + z) ^ (2 * n) := by rw [e1, e2]
    _ = (P.derivative.eval z * (1 + z) - (n : ℝ) * P.eval z) * ((1 + z) ^ n) ^ 2 := by
        rw [e4, sub_mul, mul_assoc, mul_assoc, e3]

/-- `iteratedDeriv 2 f = deriv (deriv f)`. -/
lemma iteratedDeriv_two_eq (f : ℝ → ℝ) : iteratedDeriv 2 f = deriv (deriv f) := by
  rw [show (2 : ℕ) = 1 + 1 from rfl, iteratedDeriv_succ, iteratedDeriv_succ,
    iteratedDeriv_zero]

/-- **The iterated derivative of a rational function with a single pole at `-1`.** -/
lemma iteratedDeriv_rat (P : Polynomial ℝ) (n : ℕ) (hn : 1 ≤ n) (k : ℕ) :
    Set.EqOn (iteratedDeriv k (fun w : ℝ => P.eval w / (1 + w) ^ n))
      (fun w : ℝ => (numIter n P k).eval w / (1 + w) ^ (n + k)) (Set.Ioi (-1)) := by
  induction k with
  | zero =>
      intro z _
      simp [numIter]
  | succ k ih =>
      intro z hz
      have hz' : (-1 : ℝ) < z := hz
      have hzne : z ≠ -1 := ne_of_gt hz'
      have hev : iteratedDeriv k (fun w : ℝ => P.eval w / (1 + w) ^ n)
          =ᶠ[𝓝 z] fun w : ℝ => (numIter n P k).eval w / (1 + w) ^ (n + k) :=
        ih.eventuallyEq_of_mem (isOpen_Ioi.mem_nhds hz)
      rw [iteratedDeriv_succ, hev.deriv_eq,
        deriv_rat (numIter n P k) (n + k) (by omega) hzne, numIter_succ]
      rw [Nat.add_assoc]

/-! ## 2. The polynomial bound and the master decay estimate -/

/-- On the nonnegative half-line a polynomial of degree `≤ d` is bounded by the sum of the
absolute values of its coefficients times `(1+t)^d`. -/
lemma poly_eval_bound (P : Polynomial ℝ) {d : ℕ} (hd : P.natDegree ≤ d) {t : ℝ}
    (ht : 0 ≤ t) :
    |P.eval t| ≤ (∑ i ∈ Finset.range (d + 1), |P.coeff i|) * (1 + t) ^ d := by
  rw [Polynomial.eval_eq_sum_range]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  calc ∑ i ∈ Finset.range (P.natDegree + 1), |P.coeff i * t ^ i|
      = ∑ i ∈ Finset.range (P.natDegree + 1), |P.coeff i| * t ^ i := by
        refine Finset.sum_congr rfl fun i _ => by rw [abs_mul, abs_pow, abs_of_nonneg ht]
    _ ≤ ∑ i ∈ Finset.range (P.natDegree + 1), |P.coeff i| * (1 + t) ^ d := by
        refine Finset.sum_le_sum fun i hi => ?_
        have hi' : i ≤ P.natDegree := by
          have := Finset.mem_range.mp hi
          omega
        refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
        calc t ^ i ≤ (1 + t) ^ i := pow_le_pow_left₀ ht (by linarith) i
          _ ≤ (1 + t) ^ d := pow_le_pow_right₀ (by linarith) (by omega)
    _ = (∑ i ∈ Finset.range (P.natDegree + 1), |P.coeff i|) * (1 + t) ^ d := by
        rw [Finset.sum_mul]
    _ ≤ (∑ i ∈ Finset.range (d + 1), |P.coeff i|) * (1 + t) ^ d := by
        refine mul_le_mul_of_nonneg_right ?_ (by positivity)
        refine Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_
        · intro i hi
          simp only [Finset.mem_range] at hi ⊢
          omega
        · intro i _ _; exact abs_nonneg _

/-- **The master estimate.**  For a polynomial `P` with `natDegree P ≤ d` and `1 ≤ s`, every
`k`-th derivative of `z ↦ P(z)/(1+z)^{d+s}` decays at least like `(1+t)^{-(s+k)}` on
`(0,∞)`, with the completely explicit constant given by the coefficients of the numerator
polynomial `numIter (d+s) P k`. -/
theorem rat_iteratedDeriv_bound (P : Polynomial ℝ) (d s k : ℕ) (hs : 1 ≤ s)
    (hPd : P.natDegree ≤ d) :
    ∀ t : ℝ, 0 < t →
      |iteratedDeriv k (fun z : ℝ => P.eval z / (1 + z) ^ (d + s)) t|
        ≤ (∑ i ∈ Finset.range (d + 1), |(numIter (d + s) P k).coeff i|)
            / (1 + t) ^ (s + k) := by
  intro t ht
  have hds : 1 ≤ d + s := by omega
  have ht1 : (-1 : ℝ) < t := by linarith
  have hiter : iteratedDeriv k (fun z : ℝ => P.eval z / (1 + z) ^ (d + s)) t
      = (numIter (d + s) P k).eval t / (1 + t) ^ (d + s + k) :=
    iteratedDeriv_rat P (d + s) hds k ht1
  have hdeg : (numIter (d + s) P k).natDegree ≤ d :=
    (numIter_natDegree_le (d + s) P k).trans hPd
  have hpb := poly_eval_bound (numIter (d + s) P k) hdeg ht.le
  have hden : (0 : ℝ) < (1 + t) ^ (d + s + k) := pow_pos (by linarith) _
  have habs : |(1 + t) ^ (d + s + k)| = (1 + t) ^ (d + s + k) := abs_of_pos hden
  rw [hiter, abs_div, habs]
  refine (div_le_div_of_nonneg_right hpb hden.le).trans ?_
  have heq : (∑ i ∈ Finset.range (d + 1), |(numIter (d + s) P k).coeff i|) * (1 + t) ^ d
        / (1 + t) ^ (d + s + k)
      = (∑ i ∈ Finset.range (d + 1), |(numIter (d + s) P k).coeff i|)
        / (1 + t) ^ (s + k) := by
    rw [show d + s + k = d + (s + k) from by omega, pow_add]
    rw [div_eq_div_iff (by positivity) (by positivity)]
    ring
  rw [heq]

/-- Equality on an open set passes to iterated derivatives. -/
lemma iteratedDeriv_congr_of_eqOn_isOpen {s : Set ℝ} (hs : IsOpen s) {f g : ℝ → ℝ}
    (h : Set.EqOn f g s) (k : ℕ) : Set.EqOn (iteratedDeriv k f) (iteratedDeriv k g) s := by
  induction k with
  | zero => simpa using h
  | succ k ih =>
      intro x hx
      rw [iteratedDeriv_succ, iteratedDeriv_succ]
      exact EventuallyEq.deriv_eq (ih.eventuallyEq_of_mem (hs.mem_nhds hx))

/-! ## 3. The numerator polynomial of `phiAj j α` -/

/-- `phiAjNum α j` is the numerator of `phiAj j α` over the common denominator
`(1+z)^(2j+2)`:  `phiAj j α z = (phiAjNum α j).eval z / (1+z)^(2j+2)`. -/
noncomputable def phiAjNum (α : ℝ) : ℕ → Polynomial ℝ
  | 0 => Polynomial.C 2 * Polynomial.X
  | (j + 1) =>
      Polynomial.C α * Polynomial.X ^ 2
          * numStep (2 * j + 3) (numStep (2 * j + 2) (phiAjNum α j))
        + Polynomial.C (5 + α) * Polynomial.X * (1 + Polynomial.X)
          * numStep (2 * j + 2) (phiAjNum α j)

lemma phiAjNum_natDegree_le (α : ℝ) (j : ℕ) : (phiAjNum α j).natDegree ≤ 2 * j + 1 := by
  induction j with
  | zero =>
      have h := Polynomial.natDegree_C_mul_le (2 : ℝ) (Polynomial.X : Polynomial ℝ)
      have hX := Polynomial.natDegree_X_le (R := ℝ)
      simp only [phiAjNum]
      omega
  | succ j ih =>
      have hQ1 : (numStep (2 * j + 2) (phiAjNum α j)).natDegree ≤ 2 * j + 1 :=
        numStep_natDegree_le (by omega) ih
      have hQ2 : (numStep (2 * j + 3)
          (numStep (2 * j + 2) (phiAjNum α j))).natDegree ≤ 2 * j + 1 :=
        numStep_natDegree_le (by omega) hQ1
      have hX2 : (Polynomial.X ^ 2 : Polynomial ℝ).natDegree ≤ 2 := by
        have h := Polynomial.natDegree_pow_le (p := (Polynomial.X : Polynomial ℝ)) (n := 2)
        have hX := Polynomial.natDegree_X_le (R := ℝ)
        omega
      have h1X := natDegree_one_add_X_le
      rw [phiAjNum]
      refine (Polynomial.natDegree_add_le _ _).trans (max_le ?_ ?_)
      · have hc : (Polynomial.C α * Polynomial.X ^ 2).natDegree ≤ 2 :=
          (Polynomial.natDegree_C_mul_le _ _).trans hX2
        have h := Polynomial.natDegree_mul_le (p := Polynomial.C α * Polynomial.X ^ 2)
          (q := numStep (2 * j + 3) (numStep (2 * j + 2) (phiAjNum α j)))
        omega
      · have hc : (Polynomial.C (5 + α) * Polynomial.X
            * (1 + Polynomial.X)).natDegree ≤ 2 := by
          refine (Polynomial.natDegree_mul_le.trans ?_)
          have hcx : (Polynomial.C (5 + α) * Polynomial.X).natDegree ≤ 1 :=
            (Polynomial.natDegree_C_mul_le _ _).trans Polynomial.natDegree_X_le
          omega
        have h := Polynomial.natDegree_mul_le
          (p := Polynomial.C (5 + α) * Polynomial.X * (1 + Polynomial.X))
          (q := numStep (2 * j + 2) (phiAjNum α j))
        omega

lemma phiAjNum_dvd_X (α : ℝ) (j : ℕ) : Polynomial.X ∣ phiAjNum α j := by
  induction j with
  | zero => exact ⟨Polynomial.C 2, by rw [phiAjNum]; ring⟩
  | succ j _ =>
      refine ⟨Polynomial.C α * Polynomial.X
          * numStep (2 * j + 3) (numStep (2 * j + 2) (phiAjNum α j))
        + Polynomial.C (5 + α) * (1 + Polynomial.X)
          * numStep (2 * j + 2) (phiAjNum α j), ?_⟩
      rw [phiAjNum]
      ring

lemma phiAjNum_coeff_zero (α : ℝ) (j : ℕ) : (phiAjNum α j).coeff 0 = 0 :=
  Polynomial.X_dvd_iff.mp (phiAjNum_dvd_X α j)

/-- The elementary algebra of one `𝒜`-step on the rational representation. -/
lemma rat_step_algebra (α z a₁ a₂ : ℝ) (e : ℕ) (ha : (1 : ℝ) + z ≠ 0) :
    α * z ^ 2 * (a₂ / (1 + z) ^ (e + 2)) + (5 + α) * z * (a₁ / (1 + z) ^ (e + 1))
      = (α * z ^ 2 * a₂ + (5 + α) * z * (1 + z) * a₁) / (1 + z) ^ (e + 2) := by
  have h0 : α * z ^ 2 * (a₂ / (1 + z) ^ (e + 2)) = α * z ^ 2 * a₂ / (1 + z) ^ (e + 2) :=
    (mul_div_assoc _ _ _).symm
  have h1 : (5 + α) * z * (a₁ / (1 + z) ^ (e + 1))
      = ((5 + α) * z * a₁ * (1 + z)) / (1 + z) ^ (e + 2) := by
    rw [← mul_div_assoc]
    rw [div_eq_div_iff (pow_ne_zero (e + 1) ha) (pow_ne_zero (e + 2) ha)]
    have hA : (1 + z) ^ (e + 2) = (1 + z) ^ (e + 1) * (1 + z) := by
      rw [show e + 2 = (e + 1) + 1 from by omega, pow_succ]
    have hB : (1 + z) ^ (e + 1) = (1 + z) ^ e * (1 + z) := pow_succ _ _
    rw [hA, hB]
    ring
  rw [h0, h1, ← add_div]
  ring

/-- **The rational representation of `phiAj j α`.** -/
theorem phiAj_eqOn_num (α : ℝ) (j : ℕ) :
    Set.EqOn (phiAj j α)
      (fun z : ℝ => (phiAjNum α j).eval z / (1 + z) ^ (2 * j + 2)) (Set.Ioi (-1)) := by
  induction j with
  | zero =>
      intro z _
      show Work.FTS.VocabO.phiR z = (phiAjNum α 0).eval z / (1 + z) ^ (2 * 0 + 2)
      rw [Work.FTS.VocabO.phiR]
      simp only [phiAjNum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X]
  | succ j ih =>
      intro z hz
      have hz' : (-1 : ℝ) < z := hz
      have hzne : z ≠ -1 := ne_of_gt hz'
      have ha : (1 : ℝ) + z ≠ 0 := by intro h; exact hzne (by linarith)
      show phiAj (j + 1) α z
        = (phiAjNum α (j + 1)).eval z / (1 + z) ^ (2 * (j + 1) + 2)
      have hder1 : deriv (phiAj j α) z
          = (numStep (2 * j + 2) (phiAjNum α j)).eval z / (1 + z) ^ (2 * j + 3) := by
        rw [(ih.eventuallyEq_of_mem (isOpen_Ioi.mem_nhds hz)).deriv_eq]
        have h := deriv_rat (phiAjNum α j) (2 * j + 2) (by omega) hzne
        rw [show (2 * j + 2 + 1 : ℕ) = 2 * j + 3 from by omega] at h
        exact h
      have hder2 : iteratedDeriv 2 (phiAj j α) z
          = (numStep (2 * j + 3) (numStep (2 * j + 2) (phiAjNum α j))).eval z
              / (1 + z) ^ (2 * j + 4) := by
        have hev' : deriv (phiAj j α) =ᶠ[𝓝 z]
            (fun w : ℝ => (numStep (2 * j + 2) (phiAjNum α j)).eval w
              / (1 + w) ^ (2 * j + 3)) := by
          filter_upwards [isOpen_Ioi.mem_nhds hz] with y hy
          have hy' : (-1 : ℝ) < y := hy
          rw [(ih.eventuallyEq_of_mem (isOpen_Ioi.mem_nhds hy)).deriv_eq]
          have h := deriv_rat (phiAjNum α j) (2 * j + 2) (by omega) (ne_of_gt hy')
          rw [show (2 * j + 2 + 1 : ℕ) = 2 * j + 3 from by omega] at h
          exact h
        rw [iteratedDeriv_two_eq, hev'.deriv_eq]
        have h := deriv_rat (numStep (2 * j + 2) (phiAjNum α j)) (2 * j + 3) (by omega) hzne
        rw [show (2 * j + 3 + 1 : ℕ) = 2 * j + 4 from by omega] at h
        exact h
      have hphi : phiAj (j + 1) α z
          = α * z ^ 2 * iteratedDeriv 2 (phiAj j α) z
            + (5 + α) * z * deriv (phiAj j α) z := rfl
      have hnum : (phiAjNum α (j + 1)).eval z
          = α * z ^ 2 * (numStep (2 * j + 3) (numStep (2 * j + 2) (phiAjNum α j))).eval z
            + (5 + α) * z * (1 + z)
              * (numStep (2 * j + 2) (phiAjNum α j)).eval z := by
        simp only [phiAjNum, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow,
          Polynomial.eval_C, Polynomial.eval_X, Polynomial.eval_one]
      rw [hphi, hder1, hder2, hnum]
      rw [show (2 * j + 4 : ℕ) = (2 * j + 2) + 2 from by omega,
        show (2 * j + 3 : ℕ) = (2 * j + 2) + 1 from by omega,
        show (2 * (j + 1) + 2 : ℕ) = (2 * j + 2) + 2 from by omega]
      exact rat_step_algebra α z ((numStep (2 * j + 2) (phiAjNum α j)).eval z)
        ((numStep (2 * j + 3) (numStep (2 * j + 2) (phiAjNum α j))).eval z) (2 * j + 2) ha

/-! ## 4. The divided function `phiAj j α / z` -/

/-- The numerator of `phiAj j α / z` over the denominator `(1+z)^(2j+2)`:
`(phiAjNum α j).divX`. -/
noncomputable def phiAjNumDiv (α : ℝ) (j : ℕ) : Polynomial ℝ := (phiAjNum α j).divX

lemma phiAjNumDiv_natDegree_le (α : ℝ) (j : ℕ) : (phiAjNumDiv α j).natDegree ≤ 2 * j := by
  rw [phiAjNumDiv, Polynomial.natDegree_divX_eq_natDegree_tsub_one]
  have h := phiAjNum_natDegree_le α j
  omega

/-- `(phiAjNum α j).eval z = z · (phiAjNumDiv α j).eval z`. -/
lemma phiAjNum_eval_divX (α : ℝ) (j : ℕ) (z : ℝ) :
    (phiAjNum α j).eval z = z * (phiAjNumDiv α j).eval z := by
  have h := congrArg (fun p : Polynomial ℝ => p.eval z)
    (Polynomial.divX_mul_X_add (phiAjNum α j))
  simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_X, Polynomial.eval_C]
    at h
  rw [phiAjNum_coeff_zero α j, add_zero, mul_comm] at h
  exact h.symm

/-- **The rational representation of `phiAj j α / z`.** -/
theorem phiAj_div_eqOn_num (α : ℝ) (j : ℕ) :
    Set.EqOn (fun z : ℝ => phiAj j α z / z)
      (fun z : ℝ => (phiAjNumDiv α j).eval z / (1 + z) ^ (2 * j + 2)) (Set.Ioi 0) := by
  intro z hz
  have hzpos : (0 : ℝ) < z := hz
  have hz0 : z ≠ 0 := ne_of_gt hzpos
  have hz1 : (-1 : ℝ) < z := by linarith
  show phiAj j α z / z = (phiAjNumDiv α j).eval z / (1 + z) ^ (2 * j + 2)
  rw [phiAj_eqOn_num α j hz1]
  dsimp only
  have ha : (1 + z) ^ (2 * j + 2) ≠ 0 := pow_ne_zero _ (by linarith)
  rw [phiAjNum_eval_divX α j z]
  field_simp

/-! ## 5. Auxiliary inequalities for the assembly -/

lemma div_pow_le_shift (C t : ℝ) (m : ℕ) (hC : 0 ≤ C) (ht : 0 < t) :
    C / (1 + t) ^ m ≤ (2 * C) / (1 + t ^ m) := by
  have h2 : (0 : ℝ) < (1 + t) ^ m := pow_pos (by linarith) m
  have h3 : 1 + t ^ m ≤ 2 * (1 + t) ^ m := by
    have a : t ^ m ≤ (1 + t) ^ m := pow_le_pow_left₀ (le_of_lt ht) (by linarith) m
    have b : (1 : ℝ) ≤ (1 + t) ^ m := by
      simpa using pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1) (by linarith : (1 : ℝ) ≤ 1 + t) m
    linarith
  have hgoal : C * (1 + t ^ m) ≤ 2 * C * (1 + t) ^ m := by nlinarith [h3, hC]
  have htnn : (0 : ℝ) ≤ 1 + t ^ m := by positivity
  have hleft : C / (1 + t) ^ m = C * (1 + t ^ m) / ((1 + t ^ m) * (1 + t) ^ m) := by
    rw [div_eq_div_iff (ne_of_gt h2) (by positivity)]
    ring
  have hright : (2 * C) / (1 + t ^ m) = 2 * C * (1 + t) ^ m / ((1 + t ^ m) * (1 + t) ^ m) := by
    rw [div_eq_div_iff (by positivity) (by positivity)]
    ring
  rw [hleft, hright]
  exact div_le_div_of_nonneg_right hgoal (by positivity)

lemma bound_of_le {X C A t : ℝ} (m : ℕ) (hC : 0 ≤ C) (hA : 2 * C ≤ A) (ht : 0 < t)
    (hX : X ≤ C / (1 + t) ^ m) : X ≤ A / (1 + t ^ m) :=
  hX.trans ((div_pow_le_shift C t m hC ht).trans
    (div_le_div_of_nonneg_right hA (by positivity)))

/-- The constant of the `k`-th derivative bound for the `j`-th `𝒜`-iterate. -/
noncomputable def slotC1 (α : ℝ) (j k : ℕ) : ℝ :=
  ∑ i ∈ Finset.range (2 * j + 2), |(numIter (2 * j + 2) (phiAjNum α j) k).coeff i|

/-- The constant of the `k`-th derivative bound for the divided `j`-th `𝒜`-iterate. -/
noncomputable def slotC2 (α : ℝ) (j k : ℕ) : ℝ :=
  ∑ i ∈ Finset.range (2 * j + 1), |(numIter (2 * j + 2) (phiAjNumDiv α j) k).coeff i|

lemma slotC1_nonneg (α : ℝ) (j k : ℕ) : 0 ≤ slotC1 α j k := by
  rw [slotC1]; exact Finset.sum_nonneg fun i _ => abs_nonneg _

lemma slotC2_nonneg (α : ℝ) (j k : ℕ) : 0 ≤ slotC2 α j k := by
  rw [slotC2]; exact Finset.sum_nonneg fun i _ => abs_nonneg _

/-- The assembled constant. -/
noncomputable def boundA (α : ℝ) : ℝ :=
  1 + ∑ j ∈ Finset.range 7, ∑ k ∈ Finset.range 15, (2 * slotC1 α j k + 2 * slotC2 α j k)

lemma boundA_pos (α : ℝ) : 0 < boundA α := by
  rw [boundA]
  have h : (0 : ℝ) ≤ ∑ j ∈ Finset.range 7, ∑ k ∈ Finset.range 15,
      (2 * slotC1 α j k + 2 * slotC2 α j k) :=
    Finset.sum_nonneg fun j _ => Finset.sum_nonneg fun k _ => by
      have := slotC1_nonneg α j k
      have := slotC2_nonneg α j k
      linarith
  linarith

lemma slotC_le_boundA (α : ℝ) {j k : ℕ} (hj : j ∈ Finset.range 7)
    (hk : k ∈ Finset.range 15) :
    2 * slotC1 α j k ≤ boundA α ∧ 2 * slotC2 α j k ≤ boundA α := by
  have hinner : ∀ j' ∈ Finset.range 7, 0 ≤ ∑ k' ∈ Finset.range 15,
      (2 * slotC1 α j' k' + 2 * slotC2 α j' k') := fun j' _ =>
    Finset.sum_nonneg fun k' _ => by
      have := slotC1_nonneg α j' k'
      have := slotC2_nonneg α j' k'
      linarith
  have h1 : 2 * slotC1 α j k + 2 * slotC2 α j k
      ≤ ∑ j' ∈ Finset.range 7, ∑ k' ∈ Finset.range 15,
          (2 * slotC1 α j' k' + 2 * slotC2 α j' k') :=
    (Finset.single_le_sum (fun k' _ => by
        have := slotC1_nonneg α j k'
        have := slotC2_nonneg α j k'
        linarith) hk).trans (Finset.single_le_sum hinner hj)
  rw [boundA]
  have ha := slotC1_nonneg α j k
  have hb := slotC2_nonneg α j k
  constructor <;> linarith

/-! ## 6. The target -/

theorem PhiAjFlatDecay (α : ℝ) (hα : 0 < α) (hα5 : α ≤ 1 / 5) : ∃ A : ℝ, 0 < A ∧ ∀ j : ℕ, j ≤ 6 → (∀ k : ℕ, k ≤ 14 → ∀ t : ℝ, 0 < t → |iteratedDeriv k (Work.FTS.PhiStar.phiAj j α) t| ≤ A / (1 + t ^ (k + 1))) ∧ (∀ k : ℕ, k ≤ 14 → ∀ t : ℝ, 0 < t → |iteratedDeriv k (fun t => Work.FTS.PhiStar.phiAj j α t / t) t| ≤ A / (1 + t ^ (k + 2))) := by
  refine ⟨boundA α, boundA_pos α, ?_⟩
  intro j hj
  have hj7 : j ∈ Finset.range 7 := Finset.mem_range.mpr (by omega)
  constructor
  · intro k hk t ht
    have hk15 : k ∈ Finset.range 15 := Finset.mem_range.mpr (by omega)
    obtain ⟨hC1, -⟩ := slotC_le_boundA α hj7 hk15
    have hC1nn := slotC1_nonneg α j k
    have ht1 : (-1 : ℝ) < t := by linarith
    have heq : iteratedDeriv k (Work.FTS.PhiStar.phiAj j α) t
        = iteratedDeriv k (fun z : ℝ => (phiAjNum α j).eval z / (1 + z) ^ (2 * j + 2)) t :=
      iteratedDeriv_congr_of_eqOn_isOpen isOpen_Ioi (phiAj_eqOn_num α j) k ht1
    have hb : |iteratedDeriv k (fun z : ℝ => (phiAjNum α j).eval z / (1 + z) ^ (2 * j + 2)) t|
        ≤ slotC1 α j k / (1 + t) ^ (k + 1) := by
      have h := rat_iteratedDeriv_bound (phiAjNum α j) (2 * j + 1) 1 k (by norm_num)
        (phiAjNum_natDegree_le α j) t ht
      rw [show (2 * j + 1 + 1 : ℕ) = 2 * j + 2 from by omega,
        show (1 + k : ℕ) = k + 1 from by omega] at h
      exact h
    rw [heq]
    exact bound_of_le (k + 1) hC1nn hC1 ht hb
  · intro k hk t ht
    have hk15 : k ∈ Finset.range 15 := Finset.mem_range.mpr (by omega)
    obtain ⟨-, hC2⟩ := slotC_le_boundA α hj7 hk15
    have hC2nn := slotC2_nonneg α j k
    have heq : iteratedDeriv k (fun t : ℝ => Work.FTS.PhiStar.phiAj j α t / t) t
        = iteratedDeriv k (fun z : ℝ => (phiAjNumDiv α j).eval z / (1 + z) ^ (2 * j + 2)) t :=
      iteratedDeriv_congr_of_eqOn_isOpen isOpen_Ioi (phiAj_div_eqOn_num α j) k ht
    have hb : |iteratedDeriv k (fun z : ℝ => (phiAjNumDiv α j).eval z / (1 + z) ^ (2 * j + 2)) t|
        ≤ slotC2 α j k / (1 + t) ^ (k + 2) := by
      have h := rat_iteratedDeriv_bound (phiAjNumDiv α j) (2 * j) 2 k (by norm_num)
        (phiAjNumDiv_natDegree_le α j) t ht
      rw [show (2 + k : ℕ) = k + 2 from by omega] at h
      exact h
    rw [heq]
    exact bound_of_le (k + 2) hC2nn hC2 ht hb

end Work.FTS.PhiStar
