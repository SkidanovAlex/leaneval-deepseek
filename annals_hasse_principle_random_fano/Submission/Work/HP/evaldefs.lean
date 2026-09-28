import Mathlib
import Submission.Work.HP.Defs
import Submission.Work.HP.ArchDefs
import Submission.Work.HP.tau_basic

/-!
# Helper definitions and elementary lemmas for `Work.HP.eval_bounds`

This file owns the auxiliary definitions used by `Work.HP.eval_bounds` (the eight-part
lemma collecting the elementary analytic facts about the forms `f_a`, their gradients and
their Taylor expansion used in the Archimedean part of Browning--Le Boudec--Sawin).

Conventions (see `Submission/Work/HP/Defs.lean`):
* a degree-`d` form in `n+1` variables has coefficient vector `a : Mon d n → ℝ`;
* `veronese d n x m = ∏ i, x i ^ (m.1 i : ℕ)` is the monomial function;
* `formEvalR d n a x = ∑ m, a m * veronese d n x m`;
* `rNorm` is the **Euclidean** norm (Lean's `‖·‖` on `Fin (n+1) → ℝ` is the sup norm);
* `gradF d n a x j` is the `j`-th partial derivative of `x ↦ formEvalR d n a x`.

Everything here is meant to be imported by the delegated lemmas
`Work.HP.veronese_first`, `Work.HP.veronese_taylor2`, `Work.HP.realSol_IPt`.

## Outline of the intended use (hints for collaborators)

* `prod_pow_diff_le` : a pure product-difference (telescoping) bound for monomials.  It is the
  engine for the first-order (Lipschitz) bounds on the monomial maps, and also for the
  first-order piece of the second-order Taylor bound.
* `abs_pow_sub_pow_le` : the one-variable version, via `geom_sum_mul`.
* `formEvalR_homogeneous` : `f_a(t • x) = t ^ d * f_a x`, used both for the homogeneity part of
  `eval_bounds` and for `realSol_IPt`.
-/

set_option autoImplicit false

noncomputable section

open Classical Finset MvPolynomial MeasureTheory
open scoped BigOperators

namespace Work.HP

/-! ## Partial derivatives of the monomials -/

/-- `∂(x^m)/∂x_j`: the `j`-th summand of `gradF`.  Note `dm d n m x j = 0` when `m j = 0`,
which matches the true partial derivative of `x ^ m` at `x`. -/
def dm (d n : ℕ) (m : Mon d n) (x : Fin (n + 1) → ℝ) (j : Fin (n + 1)) : ℝ :=
  ((m.1 j : ℕ) : ℝ) * x j ^ ((m.1 j : ℕ) - 1) * ∏ l ∈ Finset.univ.erase j, x l ^ ((m.1 l : ℕ))

lemma gradF_eq_sum_dm (d n : ℕ) (a : Mon d n → ℝ) (x : Fin (n + 1) → ℝ) (j : Fin (n + 1)) :
    gradF d n a x j = ∑ m : Mon d n, a m * dm d n m x j := by
  simp only [gradF, dm]
  exact Finset.sum_congr rfl (fun m _ => by ring)

lemma gradVec_eq_sum_dm (d n : ℕ) (a : Mon d n → ℝ) (x : Fin (n + 1) → ℝ) :
    gradVec d n a x = fun j => ∑ m : Mon d n, a m * dm d n m x j := by
  funext j
  exact gradF_eq_sum_dm d n a x j

/-! ## Elementary facts about `rNorm` -/

lemma abs_coord_le_rNorm {ι : Type*} [Fintype ι] (v : ι → ℝ) (i : ι) : |v i| ≤ rNorm v := by
  rw [← Real.sqrt_sq_eq_abs, rNorm]
  apply Real.sqrt_le_sqrt
  have h : (v i) ^ 2 ≤ ∑ j, (v j) ^ 2 :=
    Finset.single_le_sum (fun j _ => sq_nonneg _) (Finset.mem_univ i)
  linarith [h]

lemma abs_coeff_le_rNorm {ι : Type*} [Fintype ι] (a : ι → ℝ) (m : ι) : |a m| ≤ rNorm a :=
  abs_coord_le_rNorm a m

lemma rNorm_le_sum_abs {ι : Type*} [Fintype ι] (v : ι → ℝ) : rNorm v ≤ ∑ i, |v i| := by
  rw [rNorm, Real.sqrt_le_iff]
  refine ⟨Finset.sum_nonneg (fun i _ => abs_nonneg _), ?_⟩
  refine (Finset.sum_le_sum (fun i _ => ?_)).trans
    (Finset.sum_sq_le_sq_sum_of_nonneg (s := Finset.univ) (f := fun i => |v i|)
      (fun i _ => abs_nonneg _))
  rw [← sq_abs]

lemma rNorm_le_card_mul {ι : Type*} [Fintype ι] (v : ι → ℝ) {δ : ℝ} (h : ∀ i, |v i| ≤ δ) :
    rNorm v ≤ (Fintype.card ι : ℝ) * δ := by
  calc rNorm v ≤ ∑ i, |v i| := rNorm_le_sum_abs v
    _ ≤ ∑ _i : ι, δ := Finset.sum_le_sum (fun i _ => h i)
    _ = (Fintype.card ι : ℝ) * δ := by simp [Finset.sum_const, nsmul_eq_mul]

/-- The index type of monomials is always nonempty. -/
lemma nonempty_mon (d n : ℕ) : Nonempty (Mon d n) := by
  classical
  refine ⟨⟨fun i => if i = 0 then ⟨d, Nat.lt_succ_self d⟩ else ⟨0, Nat.succ_pos d⟩, ?_⟩⟩
  simp [Fin.sum_univ_succ]

lemma one_le_NN (d n : ℕ) : 1 ≤ NN d n := by
  have h : 0 < NN d n := by
    simpa [NN] using Fintype.card_pos_iff.mpr (nonempty_mon d n)
  omega

/-! ## Bounds for products of powers -/

lemma abs_prod_pow_le {ι : Type*} [Fintype ι] (m : ι → ℕ) (x : ι → ℝ) {M : ℝ}
    (hx : ∀ i, |x i| ≤ M) : |∏ i, x i ^ m i| ≤ M ^ (∑ i, m i) := by
  rw [Finset.abs_prod]
  calc ∏ i, |x i ^ m i| = ∏ i, |x i| ^ m i := Finset.prod_congr rfl (fun i _ => abs_pow _ _)
    _ ≤ ∏ i, M ^ m i := by
        refine Finset.prod_le_prod₀ (fun i _ => by positivity) (fun i _ => ?_)
        exact pow_le_pow_left₀ (abs_nonneg _) (hx i) _
    _ = M ^ (∑ i, m i) := Finset.prod_pow_eq_pow_sum _ _ _

/-- One-variable Lipschitz bound for powers: `|t^m - s^m| ≤ m M^m |t - s|` when
`|s|, |t| ≤ M` and `1 ≤ M`. -/
lemma abs_pow_sub_pow_le (m : ℕ) {s t M ε : ℝ} (hM : 1 ≤ M) (hε : 0 ≤ ε)
    (hs : |s| ≤ M) (ht : |t| ≤ M) (h : |t - s| ≤ ε) :
    |t ^ m - s ^ m| ≤ (m : ℝ) * M ^ m * ε := by
  have hM0 : 0 ≤ M := le_trans zero_le_one hM
  induction m with
  | zero => simp
  | succ k ih =>
    have hkey : t ^ (k + 1) - s ^ (k + 1) = t * (t ^ k - s ^ k) + (t - s) * s ^ k := by ring
    have hMk : (0 : ℝ) ≤ M ^ k := pow_nonneg hM0 k
    have h1 : |t * (t ^ k - s ^ k)| ≤ M * ((k : ℝ) * M ^ k * ε) := by
      rw [abs_mul]
      exact mul_le_mul ht ih (abs_nonneg _) hM0
    have h2 : |(t - s) * s ^ k| ≤ ε * M ^ k := by
      rw [abs_mul, abs_pow]
      have hsk : |s| ^ k ≤ M ^ k := pow_le_pow_left₀ (abs_nonneg _) hs k
      exact mul_le_mul h hsk (by positivity) hε
    calc |t ^ (k + 1) - s ^ (k + 1)| = |t * (t ^ k - s ^ k) + (t - s) * s ^ k| := by rw [hkey]
      _ ≤ M * ((k : ℝ) * M ^ k * ε) + ε * M ^ k := (abs_add_le _ _).trans (add_le_add h1 h2)
      _ ≤ ((k + 1 : ℕ) : ℝ) * M ^ (k + 1) * ε := by
            have heq : ((k + 1 : ℕ) : ℝ) * M ^ (k + 1) * ε
                - (M * ((k : ℝ) * M ^ k * ε) + ε * M ^ k) = M ^ k * ε * (M - 1) := by
              rw [pow_succ]; push_cast; ring
            have hnn : 0 ≤ M ^ k * ε * (M - 1) :=
              mul_nonneg (mul_nonneg (pow_nonneg hM0 k) hε) (by linarith)
            linarith

/-- **Product-difference (telescoping) bound.** If `|x i|, |y i| ≤ M` and `|y i - x i| ≤ ε`
on `s`, with `1 ≤ M`, `0 ≤ ε`, then the monomials differ by at most
`(∑ m i) M ^ (∑ m i) ε`. -/
lemma prod_pow_diff_le {ι : Type*} [Fintype ι] [DecidableEq ι] (s : Finset ι) (m : ι → ℕ)
    (x y : ι → ℝ) (M ε : ℝ) (hM : 1 ≤ M) (hε : 0 ≤ ε)
    (hx : ∀ i ∈ s, |x i| ≤ M) (hy : ∀ i ∈ s, |y i| ≤ M) (hxy : ∀ i ∈ s, |y i - x i| ≤ ε) :
    |∏ i ∈ s, y i ^ m i - ∏ i ∈ s, x i ^ m i|
      ≤ ((∑ i ∈ s, m i : ℕ) : ℝ) * M ^ (∑ i ∈ s, m i) * ε := by
  revert hx hy hxy
  induction s using Finset.induction_on with
  | empty => intro _ _ _; simp
  | insert i s hi ih =>
      intro hx hy hxy
      have hi' : i ∈ insert i s := Finset.mem_insert_self i s
      have hx' : ∀ j ∈ s, |x j| ≤ M := fun j hj => hx j (Finset.mem_insert_of_mem hj)
      have hy' : ∀ j ∈ s, |y j| ≤ M := fun j hj => hy j (Finset.mem_insert_of_mem hj)
      have hxy' : ∀ j ∈ s, |y j - x j| ≤ ε := fun j hj => hxy j (Finset.mem_insert_of_mem hj)
      have ihb := ih hx' hy' hxy'
      have hM0 : 0 ≤ M := le_trans zero_le_one hM
      have hAx : |∏ j ∈ s, x j ^ m j| ≤ M ^ (∑ j ∈ s, m j) := by
        rw [Finset.abs_prod]
        calc ∏ j ∈ s, |x j ^ m j| = ∏ j ∈ s, |x j| ^ m j := by
              exact Finset.prod_congr rfl (fun j _ => abs_pow _ _)
          _ ≤ ∏ j ∈ s, M ^ m j := by
              refine Finset.prod_le_prod₀ (fun j _ => by positivity) (fun j _ => ?_)
              exact pow_le_pow_left₀ (abs_nonneg _) (hx' j ‹j ∈ s›) _
          _ = M ^ (∑ j ∈ s, m j) := Finset.prod_pow_eq_pow_sum _ _ _
      have hyi : |y i| ^ m i ≤ M ^ m i := pow_le_pow_left₀ (abs_nonneg _) (hy i hi') _
      have hdiff : |y i ^ m i - x i ^ m i| ≤ (m i : ℝ) * M ^ m i * ε :=
        abs_pow_sub_pow_le (m i) hM hε (hx i hi') (hy i hi') (hxy i hi')
      rw [Finset.prod_insert hi, Finset.prod_insert hi, Finset.sum_insert hi]
      have hsplit : y i ^ m i * (∏ j ∈ s, y j ^ m j) - x i ^ m i * (∏ j ∈ s, x j ^ m j)
          = y i ^ m i * ((∏ j ∈ s, y j ^ m j) - (∏ j ∈ s, x j ^ m j))
            + (y i ^ m i - x i ^ m i) * (∏ j ∈ s, x j ^ m j) := by ring
      rw [hsplit]
      have key1 : ((m i + ∑ j ∈ s, m j : ℕ) : ℝ) = (m i : ℝ) + ((∑ j ∈ s, m j : ℕ) : ℝ) := by
        push_cast; ring
      have key2 : M ^ (m i + ∑ j ∈ s, m j) = M ^ m i * M ^ (∑ j ∈ s, m j) := pow_add M _ _
      rw [key1, key2]
      have h1 : |y i ^ m i * ((∏ j ∈ s, y j ^ m j) - (∏ j ∈ s, x j ^ m j))|
          ≤ M ^ m i * (((∑ j ∈ s, m j : ℕ) : ℝ) * M ^ (∑ j ∈ s, m j) * ε) := by
        rw [abs_mul]
        exact mul_le_mul (by simpa [abs_pow] using hyi) ihb (abs_nonneg _) (by positivity)
      have h2 : |(y i ^ m i - x i ^ m i) * (∏ j ∈ s, x j ^ m j)|
          ≤ ((m i : ℝ) * M ^ m i * ε) * M ^ (∑ j ∈ s, m j) := by
        rw [abs_mul]
        exact mul_le_mul hdiff hAx (abs_nonneg _) (by positivity)
      calc |y i ^ m i * ((∏ j ∈ s, y j ^ m j) - (∏ j ∈ s, x j ^ m j))
            + (y i ^ m i - x i ^ m i) * (∏ j ∈ s, x j ^ m j)|
          ≤ _ + _ := abs_add_le _ _
        _ ≤ M ^ m i * (((∑ j ∈ s, m j : ℕ) : ℝ) * M ^ (∑ j ∈ s, m j) * ε)
              + ((m i : ℝ) * M ^ m i * ε) * M ^ (∑ j ∈ s, m j) := add_le_add h1 h2
        _ = ((m i : ℝ) + ((∑ j ∈ s, m j : ℕ) : ℝ)) * (M ^ m i * M ^ (∑ j ∈ s, m j)) * ε := by
              ring

/-! ## Homogeneity of the forms -/

lemma formEvalR_homogeneous (d n : ℕ) (a : Mon d n → ℝ) (x : Fin (n + 1) → ℝ) (t : ℝ) :
    formEvalR d n a (t • x) = t ^ d * formEvalR d n a x := by
  simp only [formEvalR, veronese, Pi.smul_apply, smul_eq_mul, mul_pow, Finset.prod_mul_distrib,
    Finset.prod_pow_eq_pow_sum, ← Finset.mul_sum]
  have key : ∀ m : Mon d n, a m * ((t ^ (∑ i, (m.1 i : ℕ))) * ∏ i, x i ^ (m.1 i : ℕ))
      = t ^ d * (a m * ∏ i, x i ^ (m.1 i : ℕ)) := by
    intro m; rw [m.2]; ring
  rw [Finset.sum_congr rfl (fun m _ => key m), Finset.mul_sum]

/-- The integer form `formEval` is `formEvalR` of the coerced coefficients. -/
lemma formEval_eq_formEvalR (d n : ℕ) (a : Mon d n → ℤ) (x : Fin (n + 1) → ℝ) :
    formEval d n a x = formEvalR d n (toR a) x := by
  simp only [formEval, formEvalR, toR]


end Work.HP
