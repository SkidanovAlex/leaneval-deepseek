import Mathlib.Topology.Algebra.Polynomial
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Complex.Order
import Mathlib.Analysis.Complex.Basic
import Mathlib.RingTheory.Coprime.Lemmas
import Submission.SerreExample

/-!
# Sign-change / IVT / root-location bundle for the final assembly

Smith, adjust.tex, proof of Theorem main (ssec:main).  Given a real monic
polynomial `F = ∏_i (X − α_i)` (roots strictly increasing `α_1 < … < α_n`) with
bracketing points `x_i < α_i < y_i`, `y_i < x_{i+1}`, `[x_i,y_i] ⊆ [aSerre,bSerre]`,
and a real monic degree-`n` polynomial `G` that is *close* to `F` at the bracket
endpoints (`|F(x_i) − G(x_i)| < |F(x_i)|`, same at `y_i`), we conclude:

1. `G` has a root in every open bracket `(x_i, y_i)`;
2. every complex root of `G` lies in the OPEN Serre interval
   `(aSerre, bSerre)` (so any root is a totally positive algebraic integer).

Step 1 = sign change of `F` across each bracket (product formula, exactly one
root inside) + IVT transfer of the sign to `G`.  Step 2 = `G` monic of degree
`n` with `n` distinct real roots found in disjoint intervals forces
`G = ∏_i (X − r_i)`, so the complex roots are exactly these reals.
-/

noncomputable section

open ComplexOrder
open scoped Real BigOperators
open Polynomial

namespace Submission.IvtRoots

open Submission.SerreExample

/-- A real `b` that is strictly closer to `a` than `a` is to zero has the sign of `a`. -/
lemma sign_same_of_abs_sub_lt {a b : ℝ} (h : |a - b| < |a|) :
    (a < 0 → b < 0) ∧ (0 < a → 0 < b) := by
  have hs := abs_lt.mp h
  constructor
  · intro ha
    have habs : |a| = -a := abs_of_neg ha
    have hb : a < a - b := by simpa [habs] using hs.1
    nlinarith
  · intro ha
    have habs : |a| = a := abs_of_pos ha
    have hb : a - b < a := by simpa [habs] using hs.2
    nlinarith

/-- A product over a finite set with exactly one strictly negative factor (all other
factors strictly positive) is strictly negative. -/
lemma prod_neg_of_single_neg {ι : Type*} [DecidableEq ι] (s : Finset ι) {f : ι → ℝ}
    (i : ι) (hi : i ∈ s) (hi_neg : f i < 0) (hpos : ∀ j ∈ s, j ≠ i → 0 < f j) :
    (∏ j ∈ s, f j) < 0 := by
  rw [← Finset.mul_prod_erase s f hi]
  exact mul_neg_of_neg_of_pos hi_neg
    (Finset.prod_pos (by
      intro j hj
      exact hpos j (Finset.mem_of_mem_erase hj) (Finset.ne_of_mem_erase hj)))

/-- Intermediate value theorem: a real polynomial whose values at the two endpoints of an
interval have opposite signs has a root strictly between them. -/
lemma exists_root_of_mul_neg {p : Polynomial ℝ} {a b : ℝ} (hab : a < b)
    (h : p.eval a * p.eval b < 0) : ∃ r : ℝ, a < r ∧ r < b ∧ p.eval r = 0 := by
  rcases (mul_neg_iff.mp h) with hlt | hlt
  · -- `0 < p a` and `p b < 0`
    have hpa_pos : 0 < p.eval a := hlt.1
    have hpb_neg : p.eval b < 0 := hlt.2
    have hIcc : (0 : ℝ) ∈ Set.Icc (p.eval b) (p.eval a) :=
      ⟨le_of_lt hpb_neg, le_of_lt hpa_pos⟩
    have hset : Set.Icc (p.eval b) (p.eval a) ⊆ (fun x => p.eval x) '' Set.Icc a b :=
      intermediate_value_Icc' (le_of_lt hab) p.continuous.continuousOn
    rcases hset hIcc with ⟨c, hcIcc, hc0⟩
    refine ⟨c, ?_, ?_, hc0⟩
    · have hc_ne : c ≠ a := by
        intro hca
        subst c
        linarith
      exact lt_of_le_of_ne hcIcc.1 (Ne.symm hc_ne)
    · have hc_ne : c ≠ b := by
        intro hcb
        subst c
        linarith
      exact lt_of_le_of_ne hcIcc.2 hc_ne
  · -- `p a < 0` and `0 < p b`
    have hpa_neg : p.eval a < 0 := hlt.1
    have hpb_pos : 0 < p.eval b := hlt.2
    have hIcc : (0 : ℝ) ∈ Set.Icc (p.eval a) (p.eval b) :=
      ⟨le_of_lt hpa_neg, le_of_lt hpb_pos⟩
    have hset : Set.Icc (p.eval a) (p.eval b) ⊆ (fun x => p.eval x) '' Set.Icc a b :=
      intermediate_value_Icc (le_of_lt hab) p.continuous.continuousOn
    rcases hset hIcc with ⟨c, hcIcc, hc0⟩
    refine ⟨c, ?_, ?_, hc0⟩
    · have hc_ne : c ≠ a := by
        intro hca
        subst c
        linarith
      exact lt_of_le_of_ne hcIcc.1 (Ne.symm hc_ne)
    · have hc_ne : c ≠ b := by
        intro hcb
        subst c
        linarith
      exact lt_of_le_of_ne hcIcc.2 hc_ne

/-- Sign-change identity: the values of `∏_j (X - α_j)` at the two bracket endpoints
`x i` and `y i` (with `x i < α i < y i` and disjoint ordered brackets) multiply to a
strictly negative number. -/
lemma F_sign_change_product {n : ℕ} (α x y : Fin n → ℝ)
    (hxαy : ∀ i : Fin n, x i < α i ∧ α i < y i)
    (hsep : ∀ i j : Fin n, i.val < j.val → y i < x j)
    (i : Fin n) : (∏ j : Fin n, (x i - α j) * (y i - α j)) < 0 := by
  classical
  rw [show (∏ j : Fin n, (x i - α j) * (y i - α j)) =
      ∏ j ∈ (Finset.univ : Finset (Fin n)), (x i - α j) * (y i - α j) by rfl]
  refine prod_neg_of_single_neg (Finset.univ : Finset (Fin n)) i (Finset.mem_univ i) ?_ ?_
  · exact mul_neg_of_neg_of_pos (sub_neg.mpr (hxαy i).1) (sub_pos.mpr (hxαy i).2)
  · intro j hj hji
    have hji' : j.val ≠ i.val := by
      intro h
      exact hji (Fin.ext h)
    rcases lt_or_gt_of_ne hji' with hjl | hjg
    · -- j is left of i: `α j < x i < y i`, both factors positive
      have hαx : α j < x i := lt_trans (hxαy j).2 (hsep j i hjl)
      have hxy : x i < y i := lt_trans (hxαy i).1 (hxαy i).2
      have hαy : α j < y i := lt_trans hαx hxy
      exact mul_pos (sub_pos.mpr hαx) (sub_pos.mpr hαy)
    · -- j is right of i: `x i < y i < x j < α j`, both factors negative
      have hαj : y i < α j := lt_trans (hsep i j hjg) (hxαy j).1
      have hx_neg : x i - α j < 0 :=
        sub_neg.mpr (lt_trans (lt_trans (hxαy i).1 (hxαy i).2) hαj)
      have hy_neg : y i - α j < 0 := sub_neg.mpr hαj
      exact mul_pos_of_neg_of_neg hx_neg hy_neg

/-- Evaluation of the factored product at `t`. -/
lemma eval_product_eq {n : ℕ} (α : Fin n → ℝ) (F : Polynomial ℝ)
    (hfac : F = ∏ i : Fin n, (Polynomial.X - Polynomial.C (α i))) (t : ℝ) :
    F.eval t = ∏ i : Fin n, (t - α i) := by
  rw [hfac]
  simp [Polynomial.eval_prod]

/-- Sign-change / IVT / root-location bundle. -/
theorem roots_of_close {n : ℕ} (α x y : Fin n → ℝ) (F G : Polynomial ℝ)
    (hFmon : F.Monic) (hGmon : G.Monic) (hdegF : F.natDegree = n) (hdegG : G.natDegree = n)
    (hfac : F = ∏ i : Fin n, (Polynomial.X - Polynomial.C (α i)))
    (hαmono : ∀ i j : Fin n, i.val < j.val → α i < α j)
    (hxαy : ∀ i : Fin n, x i < α i ∧ α i < y i)
    (hsep : ∀ i j : Fin n, i.val < j.val → y i < x j)
    (hab : ∀ i : Fin n, aSerre ≤ x i ∧ y i ≤ bSerre)
    (hclose : ∀ i : Fin n, |F.eval (x i) - G.eval (x i)| < |F.eval (x i)| ∧
                             |F.eval (y i) - G.eval (y i)| < |F.eval (y i)|) :
    (∀ i : Fin n, ∃ r : ℝ, x i < r ∧ r < y i ∧ G.eval r = 0) ∧
    (∀ z : ℂ, Polynomial.aeval z G = 0 → (aSerre : ℂ) < z ∧ z < (bSerre : ℂ)) := by
  classical
  -- sign change of F across each bracket
  have hsign : ∀ i : Fin n, F.eval (x i) * F.eval (y i) < 0 := by
    intro i
    rw [eval_product_eq α F hfac (x i), eval_product_eq α F hfac (y i)]
    calc
      (∏ j : Fin n, (x i - α j)) * (∏ j : Fin n, (y i - α j))
          = ∏ j : Fin n, (x i - α j) * (y i - α j) := by
            rw [show (∏ j : Fin n, (x i - α j)) =
                ∏ j ∈ (Finset.univ : Finset (Fin n)), (x i - α j) by rfl,
              show (∏ j : Fin n, (y i - α j)) =
                ∏ j ∈ (Finset.univ : Finset (Fin n)), (y i - α j) by rfl]
            rw [Finset.prod_mul_distrib]
      _ < 0 := F_sign_change_product α x y hxαy hsep i
  -- closeness transfers the sign change to G
  have hGsign : ∀ i : Fin n, G.eval (x i) * G.eval (y i) < 0 := by
    intro i
    rcases (mul_neg_iff.mp (hsign i)) with hlt | hlt
    · -- F x > 0, F y < 0
      have hGx_pos : 0 < G.eval (x i) := (sign_same_of_abs_sub_lt (hclose i).1).2 hlt.1
      have hGy_neg : G.eval (y i) < 0 := (sign_same_of_abs_sub_lt (hclose i).2).1 hlt.2
      exact mul_neg_of_pos_of_neg hGx_pos hGy_neg
    · -- F x < 0, F y > 0
      have hGx_neg : G.eval (x i) < 0 := (sign_same_of_abs_sub_lt (hclose i).1).1 hlt.1
      have hGy_pos : 0 < G.eval (y i) := (sign_same_of_abs_sub_lt (hclose i).2).2 hlt.2
      exact mul_neg_of_neg_of_pos hGx_neg hGy_pos
  -- Part 1: a root of G in every bracket
  have hroot : ∀ i : Fin n, ∃ r : ℝ, x i < r ∧ r < y i ∧ G.eval r = 0 := by
    intro i
    exact exists_root_of_mul_neg (lt_trans (hxαy i).1 (hxαy i).2) (hGsign i)
  let r : Fin n → ℝ := fun i => Classical.choose (hroot i)
  have hr_gt : ∀ i : Fin n, x i < r i := fun i => (Classical.choose_spec (hroot i)).1
  have hr_lt : ∀ i : Fin n, r i < y i := fun i => (Classical.choose_spec (hroot i)).2.1
  have hr_root : ∀ i : Fin n, G.eval (r i) = 0 := fun i => (Classical.choose_spec (hroot i)).2.2
  -- distinctness of these roots
  have hrinj : Function.Injective r := by
    intro i j hij
    by_contra hne
    have hne' : i.val ≠ j.val := by
      intro h
      exact hne (Fin.ext h)
    rcases lt_or_gt_of_ne hne' with hlt | hlt
    · have hlt1 : r i < r j := lt_trans (hr_lt i) (lt_trans (hsep i j hlt) (hr_gt j))
      exact (ne_of_lt hlt1) hij
    · have hlt1 : r j < r i := lt_trans (hr_lt j) (lt_trans (hsep j i hlt) (hr_gt i))
      exact (ne_of_lt hlt1) hij.symm
  -- G equals the product of the linear factors over the roots r i
  have hAmon : (∏ i : Fin n, (Polynomial.X - Polynomial.C (r i))).Monic := by
    rw [show (∏ i : Fin n, (Polynomial.X - Polynomial.C (r i))) =
        ∏ i ∈ (Finset.univ : Finset (Fin n)), (Polynomial.X - Polynomial.C (r i)) by rfl]
    exact monic_prod_of_monic (Finset.univ : Finset (Fin n))
      (fun i => Polynomial.X - Polynomial.C (r i))
      (by intro i hi; exact Polynomial.monic_X_sub_C (r i))
  have hAdeg : (∏ i : Fin n, (Polynomial.X - Polynomial.C (r i))).natDegree = n := by
    rw [show (∏ i : Fin n, (Polynomial.X - Polynomial.C (r i))) =
        ∏ i ∈ (Finset.univ : Finset (Fin n)), (Polynomial.X - Polynomial.C (r i)) by rfl]
    rw [Polynomial.natDegree_prod]
    · simp [Fintype.card_fin]
    · intro i hi
      exact Polynomial.X_sub_C_ne_zero (r i)
  have hdiv : (∏ i : Fin n, (Polynomial.X - Polynomial.C (r i))) ∣ G := by
    refine Fintype.prod_dvd_of_coprime ?_ ?_
    · exact Polynomial.pairwise_coprime_X_sub_C hrinj
    · intro i
      rw [Polynomial.dvd_iff_isRoot]
      exact hr_root i
  have hGA : G = ∏ i : Fin n, (Polynomial.X - Polynomial.C (r i)) :=
    Polynomial.eq_of_monic_of_dvd_of_natDegree_le hAmon hGmon hdiv (by omega)
  constructor
  · intro i
    exact hroot i
  · intro z hz
    -- complex root: since G equals the product of the real linear factors,
    -- z must equal one of the real roots r i
    have hzA : (Polynomial.aeval z) (∏ i : Fin n, (Polynomial.X - Polynomial.C (r i))) = 0 := by
      simpa [hGA] using hz
    have hprod : (∏ i : Fin n, (z - (r i : ℂ))) = 0 := by
      simpa using hzA
    rw [show (∏ i : Fin n, (z - (r i : ℂ))) =
        ∏ i ∈ (Finset.univ : Finset (Fin n)), (z - (r i : ℂ)) by rfl] at hprod
    rcases (Finset.prod_eq_zero_iff.mp hprod) with ⟨i, hi, hzi⟩
    have hz_eq : z = (r i : ℂ) := sub_eq_zero.mp hzi
    constructor
    · rw [hz_eq]
      exact Complex.real_lt_real.mpr (lt_of_le_of_lt (hab i).1 (hr_gt i))
    · rw [hz_eq]
      exact Complex.real_lt_real.mpr (lt_of_lt_of_le (hr_lt i) (hab i).2)

end Submission.IvtRoots
