import Mathlib
import Submission.Commons.Algebra.BigOperators.sum_Icc_split_add
import Submission.Commons.Data.Finset.card_Icc_nat
import Submission.Commons.NumberTheory.DiophantineApproximation.BoundedDegree.height_ge_one
import Submission.Commons.NumberTheory.DiophantineApproximation.BoundedDegree.minpoly_leading_coeff_eq_one
import Submission.Commons.NumberTheory.DiophantineApproximation.BoundedDegree.root_close_deriv_bound
import Submission.Commons.NumberTheory.DiophantineApproximation.BoundedDegree.finite_algebraic_bounded_deg_height
import Submission.Commons.NumberTheory.DiophantineApproximation.Dirichlet.poly_small_value
import Submission.Commons.NumberTheory.DiophantineApproximation.BoundedDegree.finite_int_polys_bounded_supNorm
import Submission.Commons.NumberTheory.DiophantineApproximation.BoundedDegree.int_poly_supNorm_one_le
import Submission.Commons.NumberTheory.DiophantineApproximation.BoundedDegree.int_poly_eval_ne_zero_of_transcendental
import Submission.Commons.NumberTheory.DiophantineApproximation.BoundedDegree.root_transfer_all_heights
import Submission.Commons.NumberTheory.DiophantineApproximation.BoundedDegree.weak_lemma41
import Submission.Commons.NumberTheory.DiophantineApproximation.BoundedDegree.poels_prop51_real
import Submission.Commons.NumberTheory.DiophantineApproximation.BoundedDegree.wirsing_irreducible_solutions

/-!
# poels_dio_main

This file formalizes the core constructive part of A. Poëls,
*On approximation to a real number by algebraic numbers of bounded degree*,
Annals of Math, 201 (1) 2025 — specifically the "A step toward Wirsing's
conjecture" section (Theorem `ω*_n(ξ) ≥ min F`, without the minimization step).

The statement below says: for every transcendental ξ, every n ≥ 2 and every
ε > 0 there is a constant C ≥ 1 such that for every h0 there exist
  • x ≥ n and an admissible weight sequence (a_i)_{2≤i≤n+1}
    (a₂ = 1, non-decreasing, all ≥ 1, summing to x),
  • an algebraic α of degree ≤ n with height ≥ h0,
satisfying 0 < ‖ξ − α‖ and ‖ξ − α‖ ≤ C · H(α)^{−Λ(x,a) − 1 + 2ε} where
Λ(x,a) = sup_{2≤k≤n+1} (2x − 2(n−k+1) − Σ_{i=2}^{k} a_i)/a_k.

This corresponds to the combination of Sections 3–6 of the paper:
parametric geometry of numbers, the construction of the polynomial family
(Lemma "estimations de base pour Wirsing"), the generalized-resultant
transfer (Proposition "première estimation brute" + its corollary), and the
final combination, together with the classical transference inequality
(ω*_n(ξ) ≥ ω_n(ξ) − n + 1, Bugeaud) for the case ω_n(ξ) = ∞.

Plan of the development (bottom-up):
 1. elementary real/`Finset` facts about the exponent functional Λ;
 2. height of algebraic numbers (defeq with the inline expression);
 3. polynomial lattice setup: ℝ[X]_{≤n}, sup-norm, evaluation at ξ;
 4. Section 3 (successive minima, Minkowski, base construction lemma);
 5. Section 4 (families of polynomials, Lemma 4.1);
 6. Section 5 (generalized resultants, Prop 5.1, Cor 5.2);
 7. combination (Section 6) and the ω_n = ∞ case;
 8. the final theorem.
-/

open Commons.Algebra.BigOperators
open Commons.Data.Finset
open Commons.NumberTheory.DiophantineApproximation.BoundedDegree

namespace Commons.NumberTheory.DiophantineApproximation.BoundedDegree

open scoped BigOperators Topology
open Filter
open Finset

set_option maxHeartbeats 5000000


/-! ### Verified foundational lemmas (batch 1) -/

open scoped BigOperators
open Finset

/-- The exponent functional Λ(x,a) of the main statement. -/
noncomputable def Lambda (n : ℕ) (x : ℝ) (a : ℕ → ℝ) : ℝ :=
  if h : (Finset.Icc 2 (n + 1)).Nonempty then
    (Finset.Icc 2 (n + 1)).sup' h (fun k =>
      (2 * x - 2 * (n - k + 1) - (∑ i ∈ Finset.Icc 2 k, a i)) / a k)
  else 0

/-- A_{n+1}(x,a) = x under the sum constraint (the term `(n - (n+1) + 1 : ℝ)` is zero). -/
lemma A_at_top (n : ℕ) (x : ℝ) (a : ℕ → ℝ)
    (hsum : (∑ i ∈ Finset.Icc 2 (n + 1), a i) = x) :
    2 * x - 2 * ((n : ℝ) - ((n + 1 : ℕ) : ℝ) + 1) - (∑ i ∈ Finset.Icc 2 (n + 1), a i) = x := by
  simp [hsum]; ring



/-- A_k(x,a) ≥ 1 for every k ∈ Icc 2 (n+1) under admissibility (real arithmetic, matching the paper). -/
lemma A_lower (n k : ℕ) (x : ℝ) (a : ℕ → ℝ) (hk : k ∈ Finset.Icc 2 (n + 1))
    (hsum : (∑ i ∈ Finset.Icc 2 (n + 1), a i) = x)
    (ha1 : ∀ i ∈ Finset.Icc 2 (n + 1), 1 ≤ a i) :
    1 ≤ 2 * x - 2 * ((n : ℝ) - (k : ℝ) + 1) - (∑ i ∈ Finset.Icc 2 k, a i) := by
  have hk2 : 2 ≤ k := (Finset.mem_Icc.mp hk).1
  have hkn : k ≤ n + 1 := (Finset.mem_Icc.mp hk).2
  let S : ℝ := ∑ i ∈ Finset.Icc 2 k, a i
  let T : ℝ := ∑ i ∈ Finset.Icc (k+1) (n+1), a i
  have hsplit : (∑ i ∈ Finset.Icc 2 (n + 1), a i) = S + T := by
    dsimp [S, T]
    rw [sum_Icc_split_add 2 k (n+1) (by omega : 2 ≤ k) (by omega : k ≤ n + 1)]
  have hxT : x = S + T := by rw [← hsplit, hsum]
  have hT : ((n : ℝ) - (k : ℝ) + 1) ≤ T := by
    dsimp [T]
    have hcard : (Finset.Icc (k+1) (n+1)).card = n + 1 - k := by
      rw [card_Icc_nat]; omega
    calc
      ((n : ℝ) - (k : ℝ) + 1) = ((n + 1 - k : ℕ) : ℝ) := by
        rw [Nat.cast_sub (by omega : k ≤ n + 1)]
        simp only [Nat.cast_add, Nat.cast_one]
        ring
      _ = ∑ _ ∈ Finset.Icc (k+1) (n+1), (1 : ℝ) := by
        rw [← hcard]; rw [Finset.sum_const]; simp
      _ ≤ ∑ i ∈ Finset.Icc (k+1) (n+1), a i := by
        apply Finset.sum_le_sum
        intro i hi
        have hi2 : 2 ≤ i := by
          have : k + 1 ≤ i := (Finset.mem_Icc.mp hi).1
          omega
        exact ha1 i (Finset.mem_Icc.mpr ⟨hi2, (Finset.mem_Icc.mp hi).2⟩)
  have hS : 1 ≤ S := by
    dsimp [S]
    have hc : 1 ≤ (Finset.Icc 2 k).card := by
      have hmem2 : 2 ∈ Finset.Icc 2 k := Finset.mem_Icc.mpr ⟨le_rfl, hk2⟩
      exact Finset.card_pos.mpr ⟨2, hmem2⟩
    calc
      (1 : ℝ) ≤ ((Finset.Icc 2 k).card : ℝ) := by exact_mod_cast hc
      _ = ∑ _ ∈ Finset.Icc 2 k, (1 : ℝ) := by rw [Finset.sum_const]; simp
      _ ≤ S := by
        apply Finset.sum_le_sum
        intro i hi
        exact ha1 i (Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp hi).1, le_trans (Finset.mem_Icc.mp hi).2 hkn⟩)
  have hA : S ≤ 2 * x - 2 * ((n : ℝ) - (k : ℝ) + 1) - S := by
    rw [hxT]
    nlinarith [hT]
  exact le_trans hS hA




/-! ### Batch 3: height-to-exponent interface (verified)

Turning the product identity `H₂⋯H_{n+1} = H₂ˣ` (with monotone heights
`H₂ ≤ H₃ ≤ ⋯ ≤ H_{n+1}`) into the admissible weight sequence
`aᵢ = log Hᵢ / log H₂` of the statement (a₂ = 1, nondecreasing, Σ aᵢ = x,
all ≥ 1). This is the pure-analysis part of Section 6's `α = (a₂,…,a_{n+1}) ∈ A(x)`
step. -/

lemma log_div_mono {H₂ : ℝ} (hH2 : 1 < H₂) {u v : ℝ} (hu : 0 < u) (huv : u ≤ v) :
    Real.log u / Real.log H₂ ≤ Real.log v / Real.log H₂ := by
  have hlog : Real.log u ≤ Real.log v := Real.log_le_log hu huv
  have hH2log : 0 < Real.log H₂ := Real.log_pos hH2
  exact (div_le_div_iff_of_pos_right hH2log).2 hlog

lemma log_div_self {H₂ : ℝ} (hH2 : 1 < H₂) : Real.log H₂ / Real.log H₂ = 1 := by
  have h : Real.log H₂ ≠ 0 := ne_of_gt (Real.log_pos hH2)
  exact div_self h

lemma log_div_ge_one {H₂ : ℝ} (hH2 : 1 < H₂) {u : ℝ} (hu0 : 0 < u) (hhu : H₂ ≤ u) :
    1 ≤ Real.log u / Real.log H₂ := by
  have hH2log : 0 < Real.log H₂ := Real.log_pos hH2
  have hl : Real.log H₂ ≤ Real.log u := Real.log_le_log (by linarith) hhu
  rw [← log_div_self hH2]
  exact (div_le_div_iff_of_pos_right hH2log).2 hl

lemma log_prod_div_eq_sum_div {n : ℕ} {H₂ : ℝ} (hH2 : 1 < H₂) (H : ℕ → ℝ)
    (hh : ∀ i ∈ Finset.Icc 2 (n + 1), H i ≠ 0) :
    Real.log (∏ i ∈ Finset.Icc 2 (n + 1), H i) / Real.log H₂ =
      (∑ i ∈ Finset.Icc 2 (n + 1), Real.log (H i) / Real.log H₂) := by
  rw [Real.log_prod hh, Finset.sum_div]

/-- Given heights `H_i ≥ H₂ > 1` with `H 2 = H₂`, forming a chain and satisfying
`Π_{i=2}^{n+1} Hᵢ = H₂ˣ`, the logarithms `aᵢ = log Hᵢ / log H₂` form an admissible
weight sequence (a₂ = 1, nondecreasing on [2,n], sum = x, all ≥ 1). -/
lemma admissible_from_heights (n : ℕ) (hn : 2 ≤ n) (x : ℝ) (H₂ : ℝ) (H : ℕ → ℝ)
    (hH2 : 1 < H₂)
    (hH2eq : H 2 = H₂)
    (hchain : ∀ i ∈ Finset.Icc 2 n, H i ≤ H (i + 1))
    (hHge : ∀ i ∈ Finset.Icc 2 (n + 1), H₂ ≤ H i)
    (hprod : (∏ i ∈ Finset.Icc 2 (n + 1), H i) = H₂ ^ x) :
    (fun i => Real.log (H i) / Real.log H₂) 2 = 1 ∧
    (∀ i : ℕ, i ∈ Finset.Icc 2 n → (fun i => Real.log (H i) / Real.log H₂) i ≤
        (fun i => Real.log (H i) / Real.log H₂) (i + 1)) ∧
    ((∑ i ∈ Finset.Icc 2 (n + 1), (fun i => Real.log (H i) / Real.log H₂) i) = x) ∧
    (∀ i : ℕ, i ∈ Finset.Icc 2 (n + 1) → 1 ≤ (fun i => Real.log (H i) / Real.log H₂) i) := by
  let a : ℕ → ℝ := fun i => Real.log (H i) / Real.log H₂
  have hH2log : 0 < Real.log H₂ := Real.log_pos hH2
  have hH2log_ne : Real.log H₂ ≠ 0 := ne_of_gt hH2log
  have hpos : ∀ i ∈ Finset.Icc 2 (n + 1), 0 < H i := by
    intro i hi
    exact lt_trans zero_lt_one (lt_of_lt_of_le hH2 (hHge i hi))
  have hH2pos : 0 < H₂ := lt_trans zero_lt_one hH2
  refine ⟨?_, ?_, ?_, ?_⟩
  · dsimp [a]
    rw [hH2eq]
    exact log_div_self hH2
  · intro i hi
    have hi2 : 2 ≤ i := (Finset.mem_Icc.mp hi).1
    have hin : i ≤ n := (Finset.mem_Icc.mp hi).2
    have hi' : i ∈ Finset.Icc 2 (n + 1) := Finset.mem_Icc.mpr ⟨hi2, by omega⟩
    have hip : 0 < H i := hpos i hi'
    have hip1 : 0 < H (i + 1) := by
      have hi1 : i + 1 ∈ Finset.Icc 2 (n + 1) := Finset.mem_Icc.mpr ⟨by omega, by omega⟩
      exact hpos (i + 1) hi1
    dsimp [a]
    exact log_div_mono hH2 hip (hchain i hi)
  · dsimp [a]
    calc
      (∑ i ∈ Finset.Icc 2 (n + 1), Real.log (H i) / Real.log H₂)
          = Real.log (∏ i ∈ Finset.Icc 2 (n + 1), H i) / Real.log H₂ := by
            rw [← log_prod_div_eq_sum_div hH2 H (by intro i hi; exact ne_of_gt (hpos i hi))]
      _ = Real.log (H₂ ^ x) / Real.log H₂ := by rw [hprod]
      _ = x * Real.log H₂ / Real.log H₂ := by rw [Real.log_rpow hH2pos]
      _ = x := by field_simp [hH2log_ne]
  · intro i hi
    dsimp [a]
    exact log_div_ge_one hH2 (hpos i hi) (hHge i hi)

/-! ### Batch 2: interface analysis (verified)

Pure analysis layer used by the final assembly: finiteness/sup properties of the
exponent functional, ε-reduction to small ε, and the algebraic/transcendental
bridge (0 < ‖ξ − α‖). -/

/-- The inline height of the statement, factored out. -/
noncomputable def Hgt (α : ℂ) : ℝ :=
  (((let p := minpoly ℚ α;
      let D := Multiset.lcm (Multiset.map (fun i ↦ (p.coeff i).den) p.support.val);
      Finset.sup p.support (fun i ↦ (D * p.coeff i).num.natAbs) : ℕ) : ℝ))

/-- The inline height as a natural number (before the real cast). -/
noncomputable def HgtNat (α : ℂ) : ℕ :=
  let p := minpoly ℚ α
  let D := Multiset.lcm (Multiset.map (fun i ↦ (p.coeff i).den) p.support.val)
  Finset.sup p.support (fun i ↦ (D * p.coeff i).num.natAbs)

/-- The inline supremum functional of the statement (equals `Lambda` when `2 ≤ n`). -/
noncomputable def LamInline (n : ℕ) (x : ℝ) (a : ℕ → ℝ) : ℝ :=
  (if h : (Finset.Icc 2 (n + 1)).Nonempty then
     (Finset.Icc 2 (n + 1)).sup' h (fun k =>
       (2 * x - 2 * (n - k + 1) - (∑ i ∈ Finset.Icc 2 k, a i)) / a k)
   else 0)

/-- Full inner body of the main statement (after `∃ C, 1 ≤ C ∧`). -/
def GoodBody (n : ℕ) (ξ : ℝ) (ε C : ℝ) : Prop :=
  ∀ h0 : ℕ, ∃ x : ℝ, ∃ a : ℕ → ℝ, ∃ α : ℂ,
    n ≤ x ∧
    (a 2 = 1 ∧
     (∀ i : ℕ, i ∈ Finset.Icc 2 n → a i ≤ a (i + 1)) ∧
     ((∑ i ∈ Finset.Icc 2 (n + 1), a i) = x) ∧
     (∀ i : ℕ, i ∈ Finset.Icc 2 (n + 1) → 1 ≤ a i)) ∧
    IsAlgebraic ℚ α ∧ Polynomial.natDegree (minpoly ℚ α) ≤ n ∧
    0 < ‖(ξ : ℂ) - α‖ ∧
    (h0 : ℝ) ≤ Hgt α ∧
    ‖(ξ : ℂ) - α‖ ≤ C * (Hgt α) ^ (-LamInline n x a - 1 + 2 * ε)

/-- `sup'` value does not depend on the nonemptiness proof. -/
lemma sup'_independent {β : Type*} (s : Finset β) (H1 H2 : s.Nonempty) (f : β → ℝ) :
    s.sup' H1 f = s.sup' H2 f := by
  exact WithBot.coe_eq_coe.mp (by rw [Finset.coe_sup'])

/-- A finite supremum over a nonempty set is attained. -/
lemma exists_mem_eq_sup' {β : Type*} [DecidableEq β] (s : Finset β) (hs : s.Nonempty)
    (f : β → ℝ) : ∃ b ∈ s, f b = s.sup' hs f := by
  classical
  revert hs
  refine Finset.induction_on s ?empty ?insert
  · intro hs
    simp at hs
  · intro b t hbt ih hs
    by_cases ht : t.Nonempty
    · have hsi : (insert b t).sup' hs f = f b ⊔ t.sup' ht f := by
        have h := Finset.sup'_insert (s := t) (H := ht) (b := b) (f := f)
        exact (sup'_independent (insert b t) hs (insert_nonempty b t) f).trans h
      rcases ih ht with ⟨c, hc, hfc⟩
      rcases le_total (t.sup' ht f) (f b) with hle | hge
      · refine ⟨b, by simp, ?_⟩
        rw [hsi, max_eq_left hle]
      · refine ⟨c, by simp [hc], ?_⟩
        rw [hsi, max_eq_right hge, hfc]
    · refine ⟨b, by simp, ?_⟩
      have ht_empty : t = ∅ := Finset.not_nonempty_iff_eq_empty.mp ht
      subst ht_empty
      simpa using (Finset.sup'_singleton (b := b) (f := f) : ({b} : Finset β).sup' _ f = f b)

/-- The interval `Icc 2 (n+1)` is nonempty for `2 ≤ n`. -/
lemma Icc_nonempty_2_n1 (n : ℕ) (hn : 2 ≤ n) : (Finset.Icc 2 (n + 1)).Nonempty := by
  exact ⟨2, by simp; omega⟩

/-- For `2 ≤ n`, `Λ` is the `sup'` over the whole interval. -/
lemma Lambda_eq_sup' (n : ℕ) (hn : 2 ≤ n) (x : ℝ) (a : ℕ → ℝ) :
    Lambda n x a = (Finset.Icc 2 (n + 1)).sup' (Icc_nonempty_2_n1 n hn) (fun k =>
      (2 * x - 2 * (n - k + 1) - (∑ i ∈ Finset.Icc 2 k, a i)) / a k) := by
  unfold Lambda
  rw [dif_pos (Icc_nonempty_2_n1 n hn)]

/-- The inline functional of the statement is exactly `Lambda` (given `2 ≤ n`). -/
lemma LamInline_eq_Lambda (n : ℕ) (hn : 2 ≤ n) (x : ℝ) (a : ℕ → ℝ) :
    LamInline n x a = Lambda n x a := by
  rfl

/-- The supremum defining Λ is attained at some k ∈ [2, n+1]. -/
lemma Lambda_mem (n : ℕ) (hn : 2 ≤ n) (x : ℝ) (a : ℕ → ℝ) :
    ∃ k ∈ Finset.Icc 2 (n + 1),
      Lambda n x a = (2 * x - 2 * ((n : ℝ) - (k : ℝ) + 1) - (∑ i ∈ Finset.Icc 2 k, a i)) / a k := by
  rw [Lambda_eq_sup' n hn x a]
  rcases exists_mem_eq_sup' (Finset.Icc 2 (n + 1)) (Icc_nonempty_2_n1 n hn)
    (fun k => (2 * x - 2 * ((n : ℝ) - (k : ℝ) + 1) - (∑ i ∈ Finset.Icc 2 k, a i)) / a k) with ⟨k, hk, hkf⟩
  refine ⟨k, hk, ?_⟩
  exact hkf.symm

/-- From the admissibility constraints, n ≤ x. -/
lemma x_ge_n (n : ℕ) (x : ℝ) (a : ℕ → ℝ)
    (hsum : (∑ i ∈ Finset.Icc 2 (n + 1), a i) = x)
    (ha : ∀ i ∈ Finset.Icc 2 (n + 1), 1 ≤ a i) : (n : ℝ) ≤ x := by
  have hcard : (Finset.Icc 2 (n + 1)).card = n := by
    rw [card_Icc_nat]; omega
  calc
    (n : ℝ) = ((Finset.Icc 2 (n + 1)).card : ℝ) := by rw [hcard]
    _ = ∑ _ ∈ Finset.Icc 2 (n + 1), (1 : ℝ) := by rw [Finset.sum_const]; simp
    _ ≤ ∑ i ∈ Finset.Icc 2 (n + 1), a i := by
      apply Finset.sum_le_sum
      intro i hi
      exact ha i hi
    _ = x := hsum

/-- Exponent slack: replacing `2ε/a` by `2ε` increases the exponent. -/
lemma exponent_slack_le (H A a ε : ℝ) (hH : 1 ≤ H) (ha : 1 ≤ a) (hε : 0 < ε) :
    H ^ (-(A / a) - 1 + 2 * ε / a) ≤ H ^ (-(A / a) - 1 + 2 * ε) := by
  apply rpow_mono_exp hH
  have ha0 : 0 < a := lt_of_lt_of_le zero_lt_one ha
  have hε0 : 0 < 2 * ε := by positivity
  have h1 : 2 * ε ≤ 2 * ε * a := by
    have hm := mul_le_mul_of_nonneg_left ha (le_of_lt hε0)
    simpa [mul_comm, mul_left_comm, mul_assoc] using hm
  have hdiv : 2 * ε / a ≤ 2 * ε := (div_le_iff₀ ha0).mpr (by simpa [mul_comm] using h1)
  linarith

/-- Bound transfer: from the exponent at the level of the maximizing index `A/a = L`
to the final form with `2ε` slack (uses `a ≥ 1`). -/
lemma bound_transfer (H A a ε L : ℝ) (hH : 1 ≤ H) (ha : 1 ≤ a) (hε : 0 < ε)
    (hL : A / a = L) : H ^ (-(A / a) - 1 + 2 * ε / a) ≤ H ^ (-L - 1 + 2 * ε) := by
  apply rpow_mono_exp hH
  rw [← hL]
  have ha0 : 0 < a := lt_of_lt_of_le zero_lt_one ha
  have hε0 : 0 < 2 * ε := by positivity
  have h1 : 2 * ε ≤ 2 * ε * a := by
    have hm := mul_le_mul_of_nonneg_left ha (le_of_lt hε0)
    simpa [mul_comm, mul_left_comm, mul_assoc] using hm
  have hdiv : 2 * ε / a ≤ 2 * ε := (div_le_iff₀ ha0).mpr (by simpa [mul_comm] using h1)
  linarith

/-- Increasing ε only increases the right-hand side (for base ≥ 1). -/
lemma rpow_exp_le_of_eps_le {H T ε₁ ε₂ : ℝ} (hH : 1 ≤ H) (h : ε₁ ≤ ε₂) :
    H ^ (-T - 1 + 2 * ε₁) ≤ H ^ (-T - 1 + 2 * ε₂) := by
  apply rpow_mono_exp hH
  linarith

/-- An element of `ℝ` is algebraic over `ℚ` iff its image in `ℂ` is. -/
lemma isAlgebraic_complex_iff_real (x : ℝ) : IsAlgebraic ℚ (x : ℂ) ↔ IsAlgebraic ℚ x := by
  let f : ℝ →ₐ[ℚ] ℂ := IsScalarTower.toAlgHom ℚ ℝ ℂ
  have hf : Function.Injective f := by
    dsimp [f]
    intro a b hab
    exact Complex.ofReal_injective hab
  constructor
  · intro h
    exact (isAlgebraic_algHom_iff f hf).mp h
  · intro h
    exact IsAlgebraic.algHom f h

/-- An algebraic number cannot equal a transcendental real number. -/
lemma algebraic_ne_transcendental (ξ : ℝ) (hξ : Transcendental ℚ ξ) (α : ℂ)
    (hα : IsAlgebraic ℚ α) : α ≠ (ξ : ℂ) := by
  intro h
  apply hξ
  rw [h] at hα
  exact (isAlgebraic_complex_iff_real ξ).mp hα

/-- Distance from a transcendental real number to an algebraic number is positive. -/
lemma dist_pos_of_algebraic (ξ : ℝ) (hξ : Transcendental ℚ ξ) (α : ℂ)
    (hα : IsAlgebraic ℚ α) : 0 < ‖(ξ : ℂ) - α‖ := by
  rw [norm_pos_iff]
  intro hz
  apply algebraic_ne_transcendental ξ hξ α hα
  exact (sub_eq_zero.mp hz).symm

/-- ε-reduction: it suffices to prove the statement for small ε (0 < ε < 1/2). -/
lemma poels_dio_main_of_small (n : ℕ) (hn : 2 ≤ n) (ξ : ℝ) (hξ : Transcendental ℚ ξ)
    (hsmall : ∀ ε : ℝ, 0 < ε → ε < 1 / 2 → ∃ C : ℝ, 1 ≤ C ∧ GoodBody n ξ ε C) :
    ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 1 ≤ C ∧ GoodBody n ξ ε C := by
  intro ε hε
  let δ : ℝ := min ε (1 / 4)
  have hδ0 : 0 < δ := lt_min hε (by norm_num)
  have hδlt : δ < 1 / 2 := by
    dsimp [δ]
    have : min ε (1 / 4) ≤ 1 / 4 := min_le_right ε (1 / 4)
    linarith
  have hδε : δ ≤ ε := min_le_left ε (1 / 4)
  rcases hsmall δ hδ0 hδlt with ⟨C, hC1, hCbody⟩
  refine ⟨C, hC1, ?_⟩
  intro h0
  rcases hCbody h0 with ⟨x, a, α, hx, hb⟩
  rcases hb with ⟨hadm, hα, hdeg, hpos, hh0, hle⟩
  refine ⟨x, a, α, hx, hadm, hα, hdeg, hpos, hh0, ?_⟩
  have hH1 : 1 ≤ Hgt α := height_ge_one α hα
  have hr := rpow_exp_le_of_eps_le (H := Hgt α) (T := LamInline n x a) hH1 hδε
  have hC0 : 0 ≤ C := by linarith
  calc
    ‖(ξ : ℂ) - α‖ ≤ C * (Hgt α) ^ (-LamInline n x a - 1 + 2 * δ) := hle
    _ ≤ C * (Hgt α) ^ (-LamInline n x a - 1 + 2 * ε) := mul_le_mul_of_nonneg_left hr hC0

lemma heights_unbounded_of_tendsto {n : ℕ} {ξ : ℝ} (hξ : Transcendental ℚ ξ)
    (α : ℕ → ℂ) (hαalg : ∀ j : ℕ, IsAlgebraic ℚ (α j))
    (hdeg : ∀ j : ℕ, Polynomial.natDegree (minpoly ℚ (α j)) ≤ n)
    (htend : Tendsto (fun j : ℕ => ‖(ξ : ℂ) - α j‖) atTop (𝓝 0)) :
    ∀ H0 : ℕ, ∃ j : ℕ, (H0 : ℝ) ≤ Hgt (α j) := by
  intro H0
  by_cases hH0 : H0 = 0
  · refine ⟨0, ?_⟩
    have hge : 1 ≤ Hgt (α 0) := by
      dsimp [Hgt, HgtNat]
      exact height_ge_one (α 0) (hαalg 0)
    rw [hH0, Nat.cast_zero]
    exact le_trans (by positivity : (0 : ℝ) ≤ 1) hge
  · have hH0pos : 0 < H0 := Nat.pos_of_ne_zero hH0
    by_contra hnot
    push_neg at hnot
    have hlt : ∀ j : ℕ, HgtNat (α j) < H0 := by
      intro j
      have hle : ¬ (H0 : ℝ) ≤ (HgtNat (α j) : ℝ) := by simpa [Hgt, HgtNat] using hnot j
      have h' : (HgtNat (α j) : ℝ) < (H0 : ℝ) := lt_of_not_ge hle
      exact_mod_cast h'
    let F : Set ℂ := {γ : ℂ | IsAlgebraic ℚ γ ∧ Polynomial.natDegree (minpoly ℚ γ) ≤ n ∧ HgtNat γ ≤ H0}
    have hFin : F.Finite := by
      dsimp [F]
      exact finite_algebraic_bounded_deg_height n H0
    have hmem : ∀ j : ℕ, α j ∈ F := by
      intro j
      exact ⟨hαalg j, hdeg j, Nat.le_of_lt (hlt j)⟩
    have hξnot : (ξ : ℂ) ∉ F := by
      intro hξF
      exact hξ ((isAlgebraic_complex_iff_real ξ).mp hξF.1)
    let s : Finset ℂ := hFin.toFinset
    have hs_all : ∀ γ ∈ F, γ ∈ s := by intro γ hγ; exact hFin.mem_toFinset.mpr hγ
    have hs_sub : ∀ γ ∈ s, γ ∈ F := by intro γ hγ; exact hFin.mem_toFinset.mp hγ
    have hne_s : s.Nonempty := ⟨α 0, hs_all (α 0) (hmem 0)⟩
    let im : Finset ℝ := s.image (fun γ : ℂ => ‖(ξ : ℂ) - γ‖)
    have hne_im : im.Nonempty := by
      refine ⟨‖(ξ : ℂ) - α 0‖, ?_⟩
      exact Finset.mem_image.mpr ⟨α 0, hs_all (α 0) (hmem 0), rfl⟩
    let δ : ℝ := im.min' hne_im
    have hδmem : δ ∈ im := by
      dsimp [δ]
      exact Finset.min'_mem im hne_im
    have hδpos : 0 < δ := by
      rcases Finset.mem_image.mp hδmem with ⟨γ, hγs, hγeq⟩
      rw [← hγeq]
      rcases hs_sub γ hγs with ⟨hAlg, hDeg, hH⟩
      exact dist_pos_of_algebraic ξ hξ γ hAlg
    have hδle : ∀ γ ∈ s, δ ≤ ‖(ξ : ℂ) - γ‖ := by
      intro γ hγ
      have hl : δ ∈ lowerBounds (↑im) := (Finset.isLeast_min' im hne_im).2
      exact hl (Finset.mem_image.mpr ⟨γ, hγ, rfl⟩)
    have hδneigh : Set.Iio δ ∈ 𝓝 0 := Iio_mem_nhds hδpos
    have hev : ∀ᶠ j in atTop, ‖(ξ : ℂ) - α j‖ ∈ Set.Iio δ := htend.eventually hδneigh
    rcases (Filter.eventually_atTop.1 hev) with ⟨N, hN⟩
    have h1 : ‖(ξ : ℂ) - α N‖ < δ := by
      simpa using (hN N le_rfl)
    have h2 : δ ≤ ‖(ξ : ℂ) - α N‖ := hδle (α N) (hs_all (α N) (hmem N))
    linarith


/-! ### Batch 5: polynomial lattice layer (verified)

Definitions and facts about the sup-norm ‖P‖ of an integer polynomial
(`intNorm`, i.e. the ℂ-map sup-norm = max |coefficient|), the evaluation bound
at a complex point, and Gelfond's divisor lemma (via Mahler measure, Mathlib).
These mirror the paper's Notation section and are the foundation on which the
Sections 3–6 constructions (successive minima on ℤ[X]_{≤n}, Lemma 4.1,
generalized resultants) will be formalized. -/

/-- Sup-norm over the coefficients of an integer polynomial (viewed in ℂ):
‖P‖ = max_i |coeff_i|. -/
noncomputable def intNorm (P : Polynomial ℤ) : ℝ :=
  (P.map (Int.castRingHom ℂ)).supNorm

lemma intNorm_nonneg (P : Polynomial ℤ) : 0 ≤ intNorm P := by
  dsimp [intNorm]
  exact Polynomial.supNorm_nonneg _

lemma coeff_abs_le_intNorm (P : Polynomial ℤ) (i : ℕ) :
    ‖((P.coeff i : ℤ) : ℂ)‖ ≤ intNorm P := by
  dsimp [intNorm]
  have h := Polynomial.le_supNorm (p := P.map (Int.castRingHom ℂ)) i
  rw [Polynomial.coeff_map] at h
  exact h

lemma intNorm_le_of_forall_coeff_le {P : Polynomial ℤ} {B : ℝ}
    (h : ∀ i : ℕ, ‖((P.coeff i : ℤ) : ℂ)‖ ≤ B) : intNorm P ≤ B := by
  dsimp [intNorm]
  rcases Polynomial.exists_eq_supNorm (p := P.map (Int.castRingHom ℂ)) with ⟨i, hi⟩
  rw [hi]
  rw [Polynomial.coeff_map]
  exact h i

lemma intNorm_eq_zero_iff (P : Polynomial ℤ) : intNorm P = 0 ↔ P = 0 := by
  dsimp [intNorm]
  rw [Polynomial.supNorm_eq_zero_iff]
  constructor
  · intro h
    apply Polynomial.map_injective (Int.castRingHom ℂ) Int.cast_injective
    simpa using h
  · intro h
    simp [h]

lemma intNorm_ne_zero_of_ne_zero {P : Polynomial ℤ} (h : P ≠ 0) : intNorm P ≠ 0 := by
  intro hz
  exact h ((intNorm_eq_zero_iff P).mp hz)

lemma norm_intCast_eq_natAbs (z : ℤ) : ‖(z : ℂ)‖ = (z.natAbs : ℝ) := by
  rcases (Int.natAbs_eq_iff (a := z) (n := z.natAbs)).mp rfl with hz | hz
  · rw [hz]
    exact norm_natCast z.natAbs
  · rw [hz, Int.natAbs_neg, Int.cast_neg, norm_neg]
    exact norm_natCast z.natAbs

lemma intNorm_one_le {P : Polynomial ℤ} (h : P ≠ 0) : 1 ≤ intNorm P := by
  rcases (Polynomial.support_nonempty.mpr h) with ⟨i, hi⟩
  have hc : P.coeff i ≠ 0 := (Polynomial.mem_support_iff).mp hi
  have hge : 1 ≤ ‖((P.coeff i : ℤ) : ℂ)‖ := by
    rw [norm_intCast_eq_natAbs]
    exact_mod_cast (Int.natAbs_pos.mpr hc)
  exact le_trans hge (coeff_abs_le_intNorm P i)

lemma intNorm_pos_of_ne_zero {P : Polynomial ℤ} (h : P ≠ 0) : 0 < intNorm P :=
  lt_of_lt_of_le zero_lt_one (intNorm_one_le h)

/-- Triangle inequality for the sup-norm of integer polynomials. -/
lemma intNorm_add_le (P Q : Polynomial ℤ) : intNorm (P + Q) ≤ intNorm P + intNorm Q := by
  apply intNorm_le_of_forall_coeff_le
  intro i
  rw [Polynomial.coeff_add]
  rw [Int.cast_add]
  exact le_trans (norm_add_le _ _) (add_le_add (coeff_abs_le_intNorm P i) (coeff_abs_le_intNorm Q i))

/-- Bounding ‖ξ^i‖ by max(1,‖ξ‖)^n for i ≤ n. -/
lemma norm_pow_le_max_pow {ξ : ℂ} {i n : ℕ} (hin : i ≤ n) :
    ‖ξ ^ i‖ ≤ (max 1 ‖ξ‖) ^ n := by
  have h1 : ‖ξ ^ i‖ ≤ (max 1 ‖ξ‖) ^ i := by
    rw [norm_pow]
    exact pow_le_pow_left₀ (norm_nonneg ξ) (le_max_right 1 ‖ξ‖) i
  exact le_trans h1 (pow_le_pow_right₀ (le_max_left 1 ‖ξ‖) hin)

/-- Evaluation bound: |P(ξ)| ≤ (n+1)·‖P‖·max(1,‖ξ‖)^n for deg P ≤ n. -/
lemma eval_intNorm_le {n : ℕ} (P : Polynomial ℤ) (hdeg : P.natDegree ≤ n) (ξ : ℂ) :
    ‖Polynomial.eval ξ (P.map (Int.castRingHom ℂ))‖ ≤
      (n + 1 : ℝ) * intNorm P * (max 1 ‖ξ‖) ^ n := by
  rw [Polynomial.eval_map]
  have hdeg' : P.natDegree < n + 1 := Nat.lt_succ_of_le hdeg
  rw [Polynomial.eval₂_eq_sum_range' (Int.castRingHom ℂ) hdeg' ξ]
  calc
    ‖∑ i ∈ Finset.range (n + 1), ((P.coeff i : ℤ) : ℂ) * ξ ^ i‖
        ≤ ∑ i ∈ Finset.range (n + 1), ‖((P.coeff i : ℤ) : ℂ) * ξ ^ i‖ := by
          exact norm_sum_le _ _
    _ ≤ ∑ i ∈ Finset.range (n + 1), intNorm P * (max 1 ‖ξ‖) ^ n := by
          apply Finset.sum_le_sum
          intro i hi
          have hin : i ≤ n := by simpa using (Finset.mem_range.mp hi)
          rw [norm_mul]
          have hc : ‖((P.coeff i : ℤ) : ℂ)‖ ≤ intNorm P := coeff_abs_le_intNorm P i
          have hpow : ‖ξ ^ i‖ ≤ (max 1 ‖ξ‖) ^ n := norm_pow_le_max_pow hin
          calc
            ‖((P.coeff i : ℤ) : ℂ)‖ * ‖ξ ^ i‖ ≤ intNorm P * ‖ξ ^ i‖ := by
              exact mul_le_mul_of_nonneg_right hc (norm_nonneg _)
            _ ≤ intNorm P * (max 1 ‖ξ‖) ^ n := by
              exact mul_le_mul_of_nonneg_left hpow (intNorm_nonneg P)
    _ = (n + 1 : ℝ) * intNorm P * (max 1 ‖ξ‖) ^ n := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
          rw [Nat.cast_add, Nat.cast_one]
          ring

/-- Mapping to ℂ does not increase the natDegree (given an upper bound). -/
lemma map_natDegree_le {n : ℕ} (P : Polynomial ℤ) (hdeg : P.natDegree ≤ n) :
    (P.map (Int.castRingHom ℂ)).natDegree ≤ n := by
  rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
  intro j hj
  have hPj : P.coeff j = 0 := Polynomial.coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt hdeg hj)
  rw [Polynomial.coeff_map, hPj]
  simp

/-- Every binomial coefficient n.choose k is ≤ 2^n. -/
lemma choose_le_two_pow (n k : ℕ) : n.choose k ≤ 2 ^ n := by
  by_cases hk : k ≤ n
  · have hk' : k ∈ Finset.range (n + 1) := by simp [hk]
    calc
      n.choose k ≤ ∑ m ∈ Finset.range (n + 1), n.choose m :=
        Finset.single_le_sum (s := Finset.range (n + 1)) (f := fun m => n.choose m)
          (by intro b hb; exact Nat.zero_le _) hk'
      _ = 2 ^ n := by rw [Nat.sum_range_choose]
  · have : n.choose k = 0 := Nat.choose_eq_zero_of_lt (Nat.lt_of_not_ge hk)
    simp [this]

/-- **Gelfond's lemma** (sup-norm version): if P divides Q in ℤ[X], P,Q ≠ 0, both of
degree ≤ n, then ‖P‖ ≤ 2^n·√(n+1)·‖Q‖. In particular a large-norm factor cannot be
absorbed by a much smaller multiple. -/
lemma gelfond_factor {n : ℕ} {P Q : Polynomial ℤ} (hP : P ≠ 0) (hQ : Q ≠ 0)
    (hdegP : P.natDegree ≤ n) (hdegQ : Q.natDegree ≤ n) (hdiv : P ∣ Q) :
    intNorm P ≤ (2 : ℝ) ^ n * Real.sqrt (n + 1 : ℝ) * intNorm Q := by
  let p : Polynomial ℂ := P.map (Int.castRingHom ℂ)
  let q : Polynomial ℂ := Q.map (Int.castRingHom ℂ)
  rcases hdiv with ⟨S, hQS⟩
  let s : Polynomial ℂ := S.map (Int.castRingHom ℂ)
  have hSne : S ≠ 0 := by
    intro hS0
    exact hQ (by rw [hQS, hS0, mul_zero])
  have hpq : q = p * s := by
    dsimp [q, p, s]
    rw [hQS, Polynomial.map_mul]
  have hpne0 : p ≠ 0 := by
    intro hp0
    apply hP
    have hp0' : P.map (Int.castRingHom ℂ) = (0 : Polynomial ℤ).map (Int.castRingHom ℂ) := by simpa [p] using hp0
    exact (Polynomial.map_injective (Int.castRingHom ℂ) Int.cast_injective) hp0'
  have hMs : 1 ≤ s.mahlerMeasure := by
    dsimp [s]
    exact Polynomial.one_le_mahlerMeasure_of_ne_zero hSne
  have hMle : p.mahlerMeasure ≤ q.mahlerMeasure := by
    rw [hpq, Polynomial.mahlerMeasure_mul]
    exact le_mul_of_one_le_right (Polynomial.mahlerMeasure_nonneg p) hMs
  have hpsup : p.supNorm ≤ (2 : ℝ) ^ p.natDegree * p.mahlerMeasure := by
    calc
      p.supNorm ≤ (p.natDegree.choose (p.natDegree / 2) : ℝ) * p.mahlerMeasure := by
        exact Polynomial.supNorm_le_choose_natDegree_div_two_mul_mahlerMeasure p
      _ ≤ (2 : ℝ) ^ p.natDegree * p.mahlerMeasure := by
        exact mul_le_mul_of_nonneg_right
          (by exact_mod_cast choose_le_two_pow p.natDegree (p.natDegree / 2))
          (Polynomial.mahlerMeasure_nonneg p)
  have hpd : p.natDegree ≤ n := map_natDegree_le P hdegP
  have hqd : q.natDegree ≤ n := map_natDegree_le Q hdegQ
  have hMq : q.mahlerMeasure ≤ Real.sqrt (n + 1 : ℝ) * q.supNorm := by
    calc
      q.mahlerMeasure ≤ Real.sqrt (q.natDegree + 1 : ℝ) * q.supNorm := by
        exact Polynomial.mahlerMeasure_le_sqrt_natDegree_add_one_mul_supNorm q
      _ ≤ Real.sqrt (n + 1 : ℝ) * q.supNorm := by
        have hsqrt : Real.sqrt (q.natDegree + 1 : ℝ) ≤ Real.sqrt (n + 1 : ℝ) := by
          exact Real.sqrt_le_sqrt (by exact_mod_cast (Nat.add_le_add_right hqd 1))
        exact mul_le_mul_of_nonneg_right hsqrt (Polynomial.supNorm_nonneg q)
  calc
    intNorm P = p.supNorm := by simp [intNorm, p]
    _ ≤ (2 : ℝ) ^ p.natDegree * p.mahlerMeasure := hpsup
    _ ≤ (2 : ℝ) ^ n * p.mahlerMeasure := by
      exact mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num) hpd)
        (Polynomial.mahlerMeasure_nonneg p)
    _ ≤ (2 : ℝ) ^ n * q.mahlerMeasure := by
      exact mul_le_mul_of_nonneg_left hMle (pow_nonneg (by norm_num) n)
    _ ≤ (2 : ℝ) ^ n * (Real.sqrt (n + 1 : ℝ) * q.supNorm) := by
      exact mul_le_mul_of_nonneg_left hMq (pow_nonneg (by norm_num) n)
    _ = (2 : ℝ) ^ n * Real.sqrt (n + 1 : ℝ) * q.supNorm := by ring
    _ = (2 : ℝ) ^ n * Real.sqrt (n + 1 : ℝ) * intNorm Q := by simp [intNorm, q]




/-! ### Batch 6: ω_n(ξ) sup-exponent infrastructure (verified)

The exponent ω_n(ξ) := sup of the workable exponents (system ‖Q‖ ≤ H,
|Q(ξ)| ≤ H^{-ω} solvable for arbitrarily large H).  We formalise only the
quantitative facts the main proof needs: Dirichlet's lower bound (every
exponent n−δ is workable for every large H), the eventual lower bound
|Q(ξ)| ≥ ‖Q‖^{-w2} for large ‖Q‖ when w2 exceeds the sup, solutions at
exponent just below the sup, and large-norm solutions at any workable
exponent. -/

noncomputable section

def omegaSol (n : ℕ) (ξ : ℝ) (ω : ℝ) : Prop :=
  ∀ H0 : ℝ, 0 < H0 → ∃ H : ℝ, H0 ≤ H ∧ ∃ Q : Polynomial ℤ, Q ≠ 0 ∧
    Q.natDegree ≤ n ∧ (Q.map (Int.castRingHom ℝ)).supNorm ≤ H ∧
    ‖Polynomial.eval ξ (Q.map (Int.castRingHom ℝ))‖ ≤ H ^ (-ω)

def omegaSolBar (n : ℕ) (ξ : ℝ) (ω : ℝ) : Prop :=
  ∃ H0 : ℝ, 1 ≤ H0 ∧ ∀ H : ℝ, H0 ≤ H → ∃ Q : Polynomial ℤ, Q ≠ 0 ∧
    Q.natDegree ≤ n ∧ (Q.map (Int.castRingHom ℝ)).supNorm ≤ H ∧
    ‖Polynomial.eval ξ (Q.map (Int.castRingHom ℝ))‖ ≤ H ^ (-ω)

def SolSet (n : ℕ) (ξ : ℝ) : Set ℝ := {ω | 0 < ω ∧ omegaSol n ξ ω}

lemma norm_int_real_natAbs (z : ℤ) : ‖(z : ℝ)‖ = (z.natAbs : ℝ) := by
  rw [Real.norm_eq_abs]
  rcases Int.natAbs_eq_iff.mp (rfl : z.natAbs = z.natAbs) with hz | hz
  · rw [hz]; norm_num
  · rw [hz]; norm_num

lemma supNorm_le_of_forall_coeff_le {P : Polynomial ℤ} {B : ℝ}
    (h : ∀ i : ℕ, ‖((P.coeff i : ℤ) : ℝ)‖ ≤ B) : (P.map (Int.castRingHom ℝ)).supNorm ≤ B := by
  rcases (P.map (Int.castRingHom ℝ)).exists_eq_supNorm with ⟨i, hi⟩
  rw [hi, Polynomial.coeff_map]
  exact h i

lemma supNorm_le_of_coeffs {P : Polynomial ℤ} {n Q : ℕ} (hdeg : P.natDegree ≤ n)
    (h : ∀ i : ℕ, i ≤ n → (P.coeff i).natAbs ≤ Q) :
    (P.map (Int.castRingHom ℝ)).supNorm ≤ (Q : ℝ) := by
  apply supNorm_le_of_forall_coeff_le
  intro i
  by_cases hin : i ≤ n
  · rw [norm_int_real_natAbs]
    exact_mod_cast h i hin
  · have hc : P.coeff i = 0 := by
      have hni : n < i := lt_of_not_ge hin
      have hdi : P.natDegree < i := lt_of_le_of_lt hdeg hni
      exact Polynomial.coeff_eq_zero_of_natDegree_lt hdi
    rw [hc]
    norm_num

lemma omegaSol_of_le {n : ℕ} {ξ : ℝ} {ω' ω : ℝ} (_hω' : 0 < ω') (hle : ω' ≤ ω)
    (hsol : omegaSol n ξ ω) : omegaSol n ξ ω' := by
  intro H0 hH0
  rcases hsol (max H0 1) (lt_of_lt_of_le hH0 (le_max_left H0 1)) with ⟨H, hH0H, Q, hQ⟩
  refine ⟨H, le_trans (le_max_left H0 1) hH0H, Q, hQ.1, hQ.2.1, hQ.2.2.1, ?_⟩
  have hH1 : 1 ≤ H := le_trans (le_max_right H0 1) hH0H
  have he : -ω ≤ -ω' := by linarith
  calc
    ‖Polynomial.eval ξ (Q.map (Int.castRingHom ℝ))‖ ≤ H ^ (-ω) := hQ.2.2.2
    _ ≤ H ^ (-ω') := Real.rpow_le_rpow_of_exponent_le hH1 he

lemma omegaSol_of_bar {n : ℕ} {ξ : ℝ} {ω : ℝ} (hsol : omegaSolBar n ξ ω) :
    omegaSol n ξ ω := by
  intro H0 hH0
  rcases hsol with ⟨H1, hH1, hmain⟩
  refine ⟨max H0 H1, le_max_left H0 H1, ?_⟩
  exact hmain (max H0 H1) (le_max_right H0 H1)

lemma rpow_neg_natCast {a : ℝ} (ha : 0 ≤ a) (n : ℕ) : a ^ (-(n : ℝ)) = (a ^ n)⁻¹ := by
  rw [Real.rpow_neg ha, Real.rpow_natCast a n]

lemma rpow_neg_natCast_antitone {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (n : ℕ)
    (hab : b ≤ a) : a ^ (-(n : ℝ)) ≤ b ^ (-(n : ℝ)) := by
  rw [rpow_neg_natCast ha.le, rpow_neg_natCast hb.le]
  have hpow : b ^ n ≤ a ^ n := pow_le_pow_left₀ hb.le hab n
  exact (inv_le_inv₀ (pow_pos ha n) (pow_pos hb n)).mpr hpow

lemma rpow_half_neg_natCast (H : ℝ) (hH : 0 < H) (n : ℕ) :
    (H / 2) ^ (-(n : ℝ)) = H ^ (-(n : ℝ)) * (2 : ℝ) ^ n := by
  rw [rpow_neg_natCast (by positivity : 0 ≤ H / 2) n, rpow_neg_natCast hH.le n]
  have hdiv : (H / 2) ^ n = H ^ n / (2 : ℝ) ^ n := by rw [div_pow]
  rw [hdiv]
  field_simp [pow_pos hH n, pow_pos (by norm_num : 0 < (2 : ℝ)) n]

lemma dirichlet_real (n : ℕ) (ξ : ℝ) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ H : ℝ, 1 ≤ H → ∃ P : Polynomial ℤ, P ≠ 0 ∧
      P.natDegree ≤ n ∧ (P.map (Int.castRingHom ℝ)).supNorm ≤ H ∧
      ‖Polynomial.eval ξ (P.map (Int.castRingHom ℝ))‖ ≤ C * H ^ (-(n : ℝ)) := by
  rcases Commons.NumberTheory.DiophantineApproximation.Dirichlet.poly_small_value n ξ with ⟨c, hc0, hmain⟩
  let C : ℝ := (max c 1) * (2 : ℝ) ^ n
  have hC1 : 1 ≤ C := by
    dsimp [C]
    have hm : 1 ≤ max c 1 := le_max_right c 1
    have hpow : 1 ≤ (2 : ℝ) ^ n := by exact one_le_pow₀ (by norm_num : (1 : ℝ) ≤ (2 : ℝ))
    nlinarith
  have hC0 : 0 < C := lt_of_lt_of_le zero_lt_one hC1
  have hcC : c ≤ C := by
    dsimp [C]
    have hm : c ≤ max c 1 := le_max_left c 1
    have hpow1 : 1 ≤ (2 : ℝ) ^ n := by exact one_le_pow₀ (by norm_num : (1 : ℝ) ≤ (2 : ℝ))
    have hmm : c ≤ (max c 1) * (2 : ℝ) ^ n := by
      calc
        c ≤ max c 1 := hm
        _ ≤ (max c 1) * (2 : ℝ) ^ n := by
          exact le_mul_of_one_le_right (by positivity) hpow1
    exact hmm
  refine ⟨C, hC1, ?_⟩
  intro H hH1
  let Q : ℕ := Nat.floor H
  have hH0 : 0 ≤ H := le_trans zero_le_one hH1
  have hQle : (Q : ℝ) ≤ H := Nat.floor_le hH0
  have hQgeH : H ≤ (Q : ℝ) + 1 := le_of_lt (Nat.lt_floor_add_one (a := H))
  have hQ1c : ((1 : ℕ) : ℝ) ≤ H := by simpa using hH1
  have hQ1 : (1 : ℕ) ≤ Q := Nat.le_floor hQ1c
  have hQn : 0 < Q := lt_of_lt_of_le zero_lt_one hQ1
  have hQhalf : H / 2 ≤ (Q : ℝ) := by
    by_cases hH2 : 2 ≤ H
    · have h1 : H / 2 ≤ H - 1 := by nlinarith
      have h2 : H - 1 ≤ (Q : ℝ) := by linarith
      exact le_trans h1 h2
    · have hHle2 : H ≤ 2 := le_of_not_ge hH2
      have h1 : H / 2 ≤ 1 := by nlinarith
      have h2 : (1 : ℝ) ≤ (Q : ℝ) := by exact_mod_cast hQ1
      exact le_trans h1 h2
  rcases hmain Q hQn with ⟨P, hPne, hdeg, hcoeff, hval⟩
  refine ⟨P, hPne, hdeg, ?_, ?_⟩
  · exact le_trans (supNorm_le_of_coeffs hdeg hcoeff) hQle
  · have hval' : ‖Polynomial.eval ξ (P.map (Int.castRingHom ℝ))‖ ≤ c * ((Q : ℝ) ^ (-(n : ℝ))) := by
      simpa using hval
    have hQpos : 0 < (Q : ℝ) := by exact_mod_cast hQn
    have hHhalf : 0 < H / 2 := by positivity
    have hHpos : 0 < H := lt_of_lt_of_le zero_lt_one hH1
    calc
      ‖Polynomial.eval ξ (P.map (Int.castRingHom ℝ))‖
          ≤ c * (Q : ℝ) ^ (-(n : ℝ)) := hval'
      _ ≤ (max c 1) * (Q : ℝ) ^ (-(n : ℝ)) := by
        exact mul_le_mul_of_nonneg_right (le_max_left c 1)
          (Real.rpow_nonneg (by positivity : 0 ≤ (Q : ℝ)) _)
      _ ≤ (max c 1) * (H / 2) ^ (-(n : ℝ)) := by
        exact mul_le_mul_of_nonneg_left (rpow_neg_natCast_antitone hQpos hHhalf n hQhalf)
          (by positivity)
      _ = (max c 1) * (H ^ (-(n : ℝ)) * (2 : ℝ) ^ n) := by rw [rpow_half_neg_natCast H hHpos n]
      _ = ((max c 1) * (2 : ℝ) ^ n) * H ^ (-(n : ℝ)) := by ring
      _ = C * H ^ (-(n : ℝ)) := by rfl

/-- Dirichlet: for every δ > 0 the exponent n−δ is "every-large-H achievable". -/
lemma dirichlet_omegaSolBar (n : ℕ) (ξ : ℝ) (δ : ℝ) (hδ : 0 < δ) :
    omegaSolBar n ξ ((n : ℝ) - δ) := by
  rcases dirichlet_real n ξ with ⟨C, hC1, hmain⟩
  have hC0 : 0 < C := lt_of_lt_of_le zero_lt_one hC1
  let H0 : ℝ := (C * (2 : ℝ) ^ n) ^ (1 / δ) + 2
  have hbase0 : 0 ≤ C * (2 : ℝ) ^ n := by positivity
  have hH01 : 1 ≤ H0 := by
    dsimp [H0]
    have h1 : 0 ≤ (C * (2 : ℝ) ^ n) ^ (1 / δ) := Real.rpow_nonneg hbase0 (1 / δ)
    nlinarith
  refine ⟨H0, hH01, ?_⟩
  intro H hH
  have hH1' : 1 ≤ H := le_trans hH01 hH
  rcases hmain H hH1' with ⟨P, hPne, hdeg, hsup, hval⟩
  refine ⟨P, hPne, hdeg, hsup, ?_⟩
  have hHpos : 0 < H := lt_of_lt_of_le zero_lt_one hH1'
  have hCpow : C * (2 : ℝ) ^ n ≤ H ^ δ := by
    have hsub : (C * (2 : ℝ) ^ n) ^ (1 / δ) ≤ H := by
      have h0 : (C * (2 : ℝ) ^ n) ^ (1 / δ) ≤ H0 := by dsimp [H0]; nlinarith
      exact le_trans h0 hH
    have hr : ((C * (2 : ℝ) ^ n) ^ (1 / δ)) ^ δ ≤ H ^ δ := by
      exact Real.rpow_le_rpow (Real.rpow_nonneg hbase0 (1 / δ)) hsub hδ.le
    have hrm : ((C * (2 : ℝ) ^ n) ^ (1 / δ)) ^ δ = C * (2 : ℝ) ^ n := by
      rw [← Real.rpow_mul hbase0]
      have hpow : (1 / δ) * δ = 1 := by field_simp [ne_of_gt hδ]
      rw [hpow, Real.rpow_one]
    rwa [hrm] at hr
  calc
    ‖Polynomial.eval ξ (P.map (Int.castRingHom ℝ))‖ ≤ C * H ^ (-(n : ℝ)) := hval
    _ ≤ H ^ (-((n : ℝ) - δ)) := by
      have hEq : -((n : ℝ) - δ) = -(n : ℝ) + δ := by ring
      rw [hEq]
      rw [Real.rpow_add hHpos]
      have hC2 : C ≤ H ^ δ := by
        calc
          C ≤ C * (2 : ℝ) ^ n := by
            exact le_mul_of_one_le_right hC0.le (by exact one_le_pow₀ (by norm_num : (1 : ℝ) ≤ (2 : ℝ)))
          _ ≤ H ^ δ := hCpow
      have hHn : 0 ≤ H ^ (-(n : ℝ)) := by positivity
      calc
        C * H ^ (-(n : ℝ)) ≤ (H ^ δ) * H ^ (-(n : ℝ)) := by
          exact mul_le_mul_of_nonneg_right hC2 hHn
        _ = H ^ (-(n : ℝ)) * H ^ δ := by ring
        _ ≤ H ^ (-(n : ℝ)) * H ^ δ := by rfl

/-- a^{-e} is antitone in the base (a ≥ b ⟹ a^{-e} ≤ b^{-e}) for e > 0. -/
lemma rpow_neg_antitone_le {a b e : ℝ} (ha : 0 < a) (hb : 0 < b) (he : 0 < e) (hab : b ≤ a) :
    a ^ (-e) ≤ b ^ (-e) := by
  rw [Real.rpow_neg ha.le, Real.rpow_neg hb.le]
  have hpow : b ^ e ≤ a ^ e := Real.rpow_le_rpow hb.le hab he.le
  exact (inv_le_inv₀ (Real.rpow_pos_of_pos ha e) (Real.rpow_pos_of_pos hb e)).mpr hpow

/-- Strict version of the antitone bound. -/
lemma rpow_neg_strict_antitone {a b e : ℝ} (ha : 0 < a) (hb : 0 < b) (he : 0 < e) (hab : b < a) :
    a ^ (-e) < b ^ (-e) := by
  rw [Real.rpow_neg ha.le, Real.rpow_neg hb.le]
  have hpow : b ^ e < a ^ e := Real.rpow_lt_rpow hb.le hab he
  exact (inv_lt_inv₀ (Real.rpow_pos_of_pos ha e) (Real.rpow_pos_of_pos hb e)).mpr hpow

/-- If the system is solvable at positive exponent e for arbitrarily large H, it has
solutions of arbitrarily large sup-norm with |P(ξ)| ≤ ‖P‖^{-e}. -/lemma exists_largeNorm_sol {n : ℕ} {ξ : ℝ} {e : ℝ} (he : 0 < e) (hξ : Transcendental ℚ ξ)
    (hsol : omegaSol n ξ e) (N : ℝ) (hN : 0 < N) :
    ∃ P : Polynomial ℤ, P ≠ 0 ∧ P.natDegree ≤ n ∧ N ≤ (P.map (Int.castRingHom ℝ)).supNorm ∧
      ‖Polynomial.eval ξ (P.map (Int.castRingHom ℝ))‖ ≤
        ((P.map (Int.castRingHom ℝ)).supNorm) ^ (-e) := by
  by_contra hnot
  have hnot' : ∀ P : Polynomial ℤ, P ≠ 0 → P.natDegree ≤ n →
      N ≤ (P.map (Int.castRingHom ℝ)).supNorm →
      ‖Polynomial.eval ξ (P.map (Int.castRingHom ℝ))‖ ≤
        ((P.map (Int.castRingHom ℝ)).supNorm) ^ (-e) → False := by
    intro P hPne hdeg hN hval
    exact hnot ⟨P, hPne, hdeg, hN, hval⟩
  have hFin : {P : Polynomial ℤ | P ≠ 0 ∧ P.natDegree ≤ n ∧
      (P.map (Int.castRingHom ℝ)).supNorm ≤ N}.Finite := by
    simpa using finite_int_polys_bounded_supNorm n N
  let F : Finset (Polynomial ℤ) := hFin.toFinset
  have hF_all : ∀ P ∈ F, P ≠ 0 ∧ P.natDegree ≤ n ∧ (P.map (Int.castRingHom ℝ)).supNorm ≤ N := by
    intro P hP
    exact hFin.mem_toFinset.mp hP
  have hnorm_pos : ∀ P : Polynomial ℤ, P ≠ 0 → 0 < (P.map (Int.castRingHom ℝ)).supNorm := by
    intro P hP
    exact lt_of_lt_of_le zero_lt_one (int_poly_supNorm_one_le P hP)
  have hbig_contra : ∀ (H : ℝ), 0 < H → ∀ Q : Polynomial ℤ, Q ≠ 0 → Q.natDegree ≤ n →
      (Q.map (Int.castRingHom ℝ)).supNorm ≤ H →
      ‖Polynomial.eval ξ (Q.map (Int.castRingHom ℝ))‖ ≤ H ^ (-e) →
      N ≤ (Q.map (Int.castRingHom ℝ)).supNorm → False := by
    intro H hH Q hQne hdeg hsup hval hbig
    have hvalQ : ‖Polynomial.eval ξ (Q.map (Int.castRingHom ℝ))‖ ≤
        ((Q.map (Int.castRingHom ℝ)).supNorm) ^ (-e) := by
      exact le_trans hval (rpow_neg_antitone_le hH (hnorm_pos Q hQne) he hsup)
    exact hnot' Q hQne hdeg hbig hvalQ
  rcases hsol (max 2 (N + 2)) (by positivity) with ⟨H1, hH1ge, Q1, hQ1ne, hdeg1, hsup1, hval1⟩
  have hH1pos : 0 < H1 := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 2)
    (le_trans (le_max_left 2 (N + 2)) hH1ge)
  by_cases hbig1 : N ≤ (Q1.map (Int.castRingHom ℝ)).supNorm
  · exact hbig_contra H1 hH1pos Q1 hQ1ne hdeg1 hsup1 hval1 hbig1
  · have hsmall1 : (Q1.map (Int.castRingHom ℝ)).supNorm < N := lt_of_not_ge hbig1
    have hQ1F : Q1 ∈ F := hFin.mem_toFinset.mpr ⟨hQ1ne, hdeg1, le_of_lt hsmall1⟩
    let vals : Finset ℝ := F.image (fun P : Polynomial ℤ =>
      ‖Polynomial.eval ξ (P.map (Int.castRingHom ℝ))‖)
    have hvalsne : vals.Nonempty := by
      refine ⟨‖Polynomial.eval ξ (Q1.map (Int.castRingHom ℝ))‖, ?_⟩
      exact Finset.mem_image.mpr ⟨Q1, hQ1F, rfl⟩
    let m : ℝ := vals.min' hvalsne
    have hmpos : 0 < m := by
      rcases Finset.mem_image.mp (Finset.min'_mem vals hvalsne) with ⟨P, hPF, hEq⟩
      have hpos : 0 < ‖Polynomial.eval ξ (P.map (Int.castRingHom ℝ))‖ :=
        norm_pos_iff.mpr (int_poly_eval_ne_zero_of_transcendental ξ hξ P (hF_all P hPF).1)
      change 0 < vals.min' hvalsne
      rw [← hEq]
      exact hpos
    have hmle : ∀ P ∈ F, m ≤ ‖Polynomial.eval ξ (P.map (Int.castRingHom ℝ))‖ := by
      intro P hP
      exact Finset.min'_le vals (‖Polynomial.eval ξ (P.map (Int.castRingHom ℝ))‖)
        (Finset.mem_image.mpr ⟨P, hP, rfl⟩)
    let H20 : ℝ := max (max 2 (N + 2)) (m ^ (-1 / e) + 2)
    have hH20pos : 0 < H20 := by positivity
    rcases hsol H20 hH20pos with ⟨H2, hH2ge, Q2, hQ2ne, hdeg2, hsup2, hval2⟩
    have hH2pos : 0 < H2 := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 2)
      (le_trans (le_trans (le_max_left 2 (N + 2)) (le_max_left _ _)) hH2ge)
    by_cases hbig2 : N ≤ (Q2.map (Int.castRingHom ℝ)).supNorm
    · exact hbig_contra H2 hH2pos Q2 hQ2ne hdeg2 hsup2 hval2 hbig2
    · have hsmall2 : (Q2.map (Int.castRingHom ℝ)).supNorm < N := lt_of_not_ge hbig2
      have hQ2F : Q2 ∈ F := hFin.mem_toFinset.mpr ⟨hQ2ne, hdeg2, le_of_lt hsmall2⟩
      have hmleQ2 : m ≤ ‖Polynomial.eval ξ (Q2.map (Int.castRingHom ℝ))‖ := hmle Q2 hQ2F
      have hbigm : m ^ (-1 / e) < H2 := by
        have h1 : m ^ (-1 / e) + 2 ≤ H20 := by dsimp [H20]; exact le_max_right _ _
        have h2 : m ^ (-1 / e) + 2 ≤ H2 := le_trans h1 hH2ge
        nlinarith
      have hmmpos : 0 < m ^ (-1 / e) := Real.rpow_pos_of_pos hmpos (-1 / e)
      have hpowid : (m ^ (-1 / e)) ^ (-e) = m := by
        rw [← Real.rpow_mul (le_of_lt hmpos)]
        have hmul : (-1 / e) * (-e) = 1 := by field_simp [ne_of_gt he]
        rw [hmul, Real.rpow_one]
      have hstrict := rpow_neg_strict_antitone hH2pos hmmpos he hbigm
      have hH2small : H2 ^ (-e) < m := by
        rwa [hpowid] at hstrict
      have hval2lt : ‖Polynomial.eval ξ (Q2.map (Int.castRingHom ℝ))‖ < m :=
        lt_of_le_of_lt hval2 hH2small
      linarith


/-- Dirichlet: exponents just below n belong to SolSet. -/
lemma SolSet_mem_of_dirichlet {n : ℕ} {ξ : ℝ} {δ : ℝ} (hδ : 0 < δ) (hδlt : δ < (n : ℝ)) :
    ((n : ℝ) - δ) ∈ SolSet n ξ := by
  refine ⟨by linarith, omegaSol_of_bar (dirichlet_omegaSolBar n ξ δ hδ)⟩

lemma SolSet_nonempty (n : ℕ) (hn : 2 ≤ n) (ξ : ℝ) : (SolSet n ξ).Nonempty := by
  refine ⟨(n : ℝ) - 1 / 2, ?_⟩
  apply SolSet_mem_of_dirichlet (n := n) (ξ := ξ) (δ := 1 / 2)
  · norm_num
  · have hn2 : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    linarith

/-- If not every positive exponent is workable, the working exponents are bounded
above (by the least failing one). -/
lemma SolSet_bddAbove_of_not_all {n : ℕ} {ξ : ℝ}
    (hnot : ¬ ∀ ω : ℝ, 0 < ω → omegaSol n ξ ω) : BddAbove (SolSet n ξ) := by
  rw [Classical.not_forall] at hnot
  rcases hnot with ⟨ω₀, h₁⟩
  rcases (Classical.not_imp.mp h₁) with ⟨hω₀, hnotω₀⟩
  refine ⟨ω₀, ?_⟩
  intro ω hω
  by_contra hle
  have hgt : ω₀ < ω := lt_of_not_ge hle
  have hsol : omegaSol n ξ ω₀ := omegaSol_of_le hω₀ (le_of_lt hgt) hω.2
  exact hnotω₀ hsol

/-- In the bounded case, the supremum of the working exponents is a real ωN ≥ n with
(1) no workable exponent exceeds ωN; (2) every positive exponent below ωN is workable. -/
lemma exists_omegaN (n : ℕ) (hn : 2 ≤ n) (ξ : ℝ) (hbd : BddAbove (SolSet n ξ)) :
    ∃ ωN : ℝ, (n : ℝ) ≤ ωN ∧
      (∀ ω : ℝ, omegaSol n ξ ω → ω ≤ ωN) ∧
      (∀ ω' : ℝ, 0 < ω' → ω' < ωN → omegaSol n ξ ω') := by
  let S : Set ℝ := SolSet n ξ
  let ωN : ℝ := sSup S
  have hSne : S.Nonempty := SolSet_nonempty n hn ξ
  have hnpos : 0 < (n : ℝ) := by
    have h : (0 : ℕ) < n := lt_of_lt_of_le (by norm_num) hn
    exact_mod_cast h
  have h1 : (n : ℝ) ≤ ωN := by
    apply le_of_not_gt
    intro hgt
    have hsub : 0 < (n : ℝ) - ωN := sub_pos.mpr hgt
    let δ : ℝ := min ((n : ℝ)) ((n : ℝ) - ωN) / 2
    have hmin : 0 < min ((n : ℝ)) ((n : ℝ) - ωN) := lt_min_iff.mpr ⟨hnpos, hsub⟩
    have hδ0 : 0 < δ := by dsimp [δ]; exact half_pos hmin
    have hδltn : δ < (n : ℝ) := by
      dsimp [δ]
      have hminle : min ((n : ℝ)) ((n : ℝ) - ωN) ≤ (n : ℝ) := min_le_left _ _
      have hδlt : δ < min ((n : ℝ)) ((n : ℝ) - ωN) := by
        dsimp [δ]
        exact half_lt_self hmin
      exact lt_of_lt_of_le hδlt hminle
    have hmem : ((n : ℝ) - δ) ∈ S := SolSet_mem_of_dirichlet (n := n) (ξ := ξ) (δ := δ) hδ0 hδltn
    have hle : (n : ℝ) - δ ≤ ωN := le_csSup hbd hmem
    have hδlt : δ < (n : ℝ) - ωN := by
      dsimp [δ]
      have hminle : min ((n : ℝ)) ((n : ℝ) - ωN) ≤ (n : ℝ) - ωN := min_le_right _ _
      exact lt_of_lt_of_le (half_lt_self hmin) hminle
    have hcontra : ωN < (n : ℝ) - δ := by linarith
    exact (not_le_of_gt hcontra) hle
  refine ⟨ωN, h1, ?_, ?_⟩
  · intro ω hω
    by_cases h0 : 0 < ω
    · exact le_csSup hbd ⟨h0, hω⟩
    · have hle0 : ω ≤ 0 := le_of_not_gt h0
      have hn2 : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
      nlinarith [h1]
  · intro ω' hω' hlt
    rcases exists_lt_of_lt_csSup (s := S) hSne hlt with ⟨ω'', hS'', hlt''⟩
    have hω'' : omegaSol n ξ ω'' := hS''.2
    exact omegaSol_of_le hω' (le_of_lt hlt'') hω''


end

/-! ### Batch 7: the ω_n(ξ) = ∞ case

If every positive exponent is workable (ω_n(ξ) = ∞), the commons result
`root_transfer_all_heights` provides algebraic approximations of degree ≤ n at any
prescribed exponent and with unbounded heights.  Choosing the all-ones admissible
pair (x = n, aᵢ = 1) gives Λ = n, and the main statement follows with C = 1. -/

/-- For the all-ones weight (a ≡ 1, x = n) the exponent functional is Λ = n. -/
lemma Lambda_all_ones (n : ℕ) (hn : 2 ≤ n) :
    Lambda n (n : ℝ) (fun _ : ℕ => (1 : ℝ)) = (n : ℝ) := by
  let s : Finset ℕ := Finset.Icc 2 (n + 1)
  let f : ℕ → ℝ := fun k => (2 * (n : ℝ) - 2 * (((n : ℝ) - (k : ℝ)) + 1) -
      (∑ i ∈ Finset.Icc 2 k, (1 : ℝ))) / (1 : ℝ)
  have hf : ∀ k : ℕ, 2 ≤ k → f k = (k : ℝ) - 1 := by
    intro k hk2
    dsimp [f]
    have hcard : (Finset.Icc 2 k).card = k - 1 := by
      rw [card_Icc_nat]
      omega
    have hsum : (∑ i ∈ Finset.Icc 2 k, (1 : ℝ)) = ((k - 1 : ℕ) : ℝ) := by
      rw [Finset.sum_const, nsmul_eq_mul, hcard]
      simp
    have hcast : ((k - 1 : ℕ) : ℝ) = (k : ℝ) - 1 := by
      rw [Nat.cast_sub (by omega : 1 ≤ k)]
      norm_num
    rw [hsum, hcast]
    ring
  rw [Lambda_eq_sup' n hn (n : ℝ) (fun _ : ℕ => (1 : ℝ))]
  change s.sup' (Icc_nonempty_2_n1 n hn) f = (n : ℝ)
  apply le_antisymm
  · rw [Finset.sup'_le_iff]
    intro k hk
    have hk2 : 2 ≤ k := (Finset.mem_Icc.mp hk).1
    have hkn : k ≤ n + 1 := (Finset.mem_Icc.mp hk).2
    rw [hf k hk2]
    have hkn' : (k : ℝ) ≤ (n : ℝ) + 1 := by exact_mod_cast hkn
    nlinarith
  · have hk1 : n + 1 ∈ s := by
      dsimp [s]
      rw [Finset.mem_Icc]
      omega
    calc
      (n : ℝ) = f (n + 1) := by
        rw [hf (n + 1) (by omega : 2 ≤ n + 1)]
        norm_num
      _ ≤ s.sup' (Icc_nonempty_2_n1 n hn) f := Finset.le_sup' (s := s) f hk1

/-- From unbounded algebraic approximations at exponent −(n) − 1 + 2ε (all heights),
the all-ones pair satisfies the main statement with C = 1. -/
lemma goodbody_allones_approx (n : ℕ) (hn : 2 ≤ n) (ξ : ℝ) (ε : ℝ)
    (hε0 : 0 < ε) (_hε1 : ε < 1 / 2)
    (happrox : ∀ h0 : ℕ, ∃ α : ℂ, IsAlgebraic ℚ α ∧
      Polynomial.natDegree (minpoly ℚ α) ≤ n ∧ 0 < ‖(ξ : ℂ) - α‖ ∧
      (h0 : ℝ) ≤ Hgt α ∧ ‖(ξ : ℂ) - α‖ ≤ (Hgt α) ^ (-(n : ℝ) - 1 + 2 * ε)) :
    ∃ C : ℝ, 1 ≤ C ∧ GoodBody n ξ ε C := by
  refine ⟨1, by norm_num, ?_⟩
  intro h0
  rcases happrox h0 with ⟨α, hAlg, hdeg, hpos, hh0, hle⟩
  let x : ℝ := (n : ℝ)
  let a : ℕ → ℝ := fun _ => 1
  refine ⟨x, a, α, ?hx, ⟨?hA1, ?hA2, ?hA3, ?hA4⟩, hAlg, hdeg, hpos, hh0, ?hle⟩
  · dsimp [x]
    exact le_rfl
  · rfl
  · intro i hi
    dsimp [a]
    norm_num
  · have hcard : (Finset.Icc 2 (n + 1)).card = n := by
      rw [card_Icc_nat]
      omega
    dsimp [x, a]
    rw [Finset.sum_const, nsmul_eq_mul, hcard]
    simp
  · intro i hi
    dsimp [a]
    norm_num
  · have hLam : LamInline n x a = (n : ℝ) := by
      dsimp [x, a]
      exact (LamInline_eq_Lambda n hn (n : ℝ) (fun _ => (1 : ℝ))).trans (Lambda_all_ones n hn)
    rw [hLam]
    simpa using hle

/-- Case ω_n(ξ) = ∞ (every positive exponent workable): main statement with C = 1. -/
lemma poels_dio_infty_case (n : ℕ) (hn : 2 ≤ n) (ξ : ℝ) (hξ : Transcendental ℚ ξ)
    (hWinfty : ∀ ω : ℝ, 0 < ω → omegaSol n ξ ω) :
    ∀ ε : ℝ, 0 < ε → ε < 1 / 2 → ∃ C : ℝ, 1 ≤ C ∧ GoodBody n ξ ε C := by
  intro ε hε0 hε1
  apply goodbody_allones_approx n hn ξ ε hε0 hε1
  intro h0
  let w : ℝ := (n : ℝ) - 2 * ε
  have hw : 0 < w := by
    have hn2 : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    dsimp [w]
    nlinarith
  have hWoo : ∀ E : ℝ, 0 < E → ∀ N : ℝ, 0 < N → ∃ S : Polynomial ℤ, S ≠ 0 ∧
      S.natDegree ≤ n ∧ N ≤ (S.map (Int.castRingHom ℝ)).supNorm ∧
      ‖Polynomial.eval ξ (S.map (Int.castRingHom ℝ))‖ ≤
        ((S.map (Int.castRingHom ℝ)).supNorm) ^ (-E) := by
    intro E hE N hN
    exact exists_largeNorm_sol (e := E) (he := hE) hξ (hWinfty E hE) N hN
  rcases root_transfer_all_heights n hn ξ hξ hWoo w hw h0 with
    ⟨α, hAlg, hdeg, hpos, hh0, hle⟩
  refine ⟨α, hAlg, hdeg, hpos, hh0, ?_⟩
  have hE : -(n : ℝ) - 1 + 2 * ε = -w - 1 := by
    dsimp [w]
    ring
  rw [hE]
  exact hle



/-! ### Batch 9: glue for the finite-ω_n case (Section 3–6 assembly)

Helpers connecting the `ω_n(ξ)`-sup infrastructure (Batch 6), the Sections 3–4
engine `weak_lemma41` and the Section 5 transfer `poels_prop51_real`, plus the
real-exponent algebra needed for the per-P conversion. -/

/-- No positive slack above the sup of workable exponents is workable. -/
lemma omegaN_plus_not_sol {n : ℕ} {ξ : ℝ} {ωN : ℝ}
    (hle : ∀ ω : ℝ, omegaSol n ξ ω → ω ≤ ωN) {δ : ℝ} (hδ : 0 < δ) :
    ¬ omegaSol n ξ (ωN + δ) := by
  intro hsol
  have h : ωN + δ ≤ ωN := hle (ωN + δ) hsol
  linarith

/-- From `¬omegaSol n ξ w2` (w2 above the sup of workable exponents) extract the
eventual lower bound (B): every degree-≤n `Q0` with `supN Q0 ≥ HE` satisfies
`(supN Q0)^(-w2) ≤ |Q0(ξ)|`. -/
lemma hB_of_not_sol {n : ℕ} {ξ : ℝ} {w2 : ℝ} (hnot : ¬ omegaSol n ξ w2) :
    ∃ HE : ℝ, 1 ≤ HE ∧ ∀ Q0 : Polynomial ℤ, Q0 ≠ 0 → Q0.natDegree ≤ n →
      HE ≤ (Q0.map (Int.castRingHom ℝ)).supNorm →
      ((Q0.map (Int.castRingHom ℝ)).supNorm) ^ (-w2) ≤
        ‖Polynomial.eval ξ (Q0.map (Int.castRingHom ℝ))‖ := by
  classical
  unfold omegaSol at hnot
  rcases (Classical.not_forall.mp hnot) with ⟨H0, hH0imp⟩
  rcases (Classical.not_imp.mp hH0imp) with ⟨hH0pos, hrest⟩
  refine ⟨max H0 1, le_max_right H0 1, ?_⟩
  intro Q0 hQ0ne hdeg hHE
  have hH0le : H0 ≤ (Q0.map (Int.castRingHom ℝ)).supNorm :=
    le_trans (le_max_left H0 1) hHE
  by_contra hnotge
  have hsmall : ‖Polynomial.eval ξ (Q0.map (Int.castRingHom ℝ))‖ ≤
      ((Q0.map (Int.castRingHom ℝ)).supNorm) ^ (-w2) := le_of_not_ge hnotge
  exact hrest ⟨(Q0.map (Int.castRingHom ℝ)).supNorm, hH0le,
    ⟨Q0, hQ0ne, hdeg, le_rfl, hsmall⟩⟩

/-- Coprimality over ℚ of the integer-mapped polynomials transfers to ℝ. -/
lemma qcop_map_real (P Q : Polynomial ℤ)
    (h : IsCoprime ((P.map (algebraMap ℤ ℚ)) : Polynomial ℚ)
        ((Q.map (algebraMap ℤ ℚ)) : Polynomial ℚ)) :
    IsCoprime ((P.map (algebraMap ℤ ℝ)) : Polynomial ℝ)
        ((Q.map (algebraMap ℤ ℝ)) : Polynomial ℝ) := by
  have hcast : ∀ z : ℤ, (algebraMap ℚ ℝ) (algebraMap ℤ ℚ z) = algebraMap ℤ ℝ z := by
    intro z
    norm_num
  have h' : IsCoprime (((P.map (algebraMap ℤ ℚ)).map (algebraMap ℚ ℝ)) : Polynomial ℝ)
      (((Q.map (algebraMap ℤ ℚ)).map (algebraMap ℚ ℝ)) : Polynomial ℝ) :=
    h.map (Polynomial.mapRingHom (algebraMap ℚ ℝ))
  have hP : (P.map (algebraMap ℤ ℚ)).map (algebraMap ℚ ℝ) = P.map (algebraMap ℤ ℝ) := by
    ext i
    simp only [Polynomial.coeff_map]
    exact hcast (P.coeff i)
  have hQ : (Q.map (algebraMap ℤ ℚ)).map (algebraMap ℚ ℝ) = Q.map (algebraMap ℤ ℝ) := by
    ext i
    simp only [Polynomial.coeff_map]
    exact hcast (Q.coeff i)
  rw [hP, hQ] at h'
  exact h'

/-- From the step-chain on `Icc 1 n`, the family `H(i.val + 1)` is monotone on
`Fin k` whenever `k ≤ n+1`. -/
lemma monotone_fin_of_chain {n k : ℕ} (hk : k ≤ n + 1) {H : ℕ → ℝ}
    (hchain : ∀ i ∈ Finset.Icc 1 n, H i ≤ H (i + 1)) :
    Monotone (fun i : Fin k => H (i.val + 1)) := by
  classical
  intro a b hab
  have hle : a.val ≤ b.val := hab
  have hb_le_n : b.val ≤ n := by
    exact Nat.le_of_lt_succ (lt_of_lt_of_le b.isLt hk)
  suffices ∀ j : ℕ, j < k → a.val ≤ j → H (a.val + 1) ≤ H (j + 1) by
    exact this b.val b.isLt hle
  intro j
  induction j with
  | zero =>
      intro _ h0
      have : a.val = 0 := by omega
      rw [this]
  | succ m ih =>
      intro hsk hle'
      by_cases hjm : a.val ≤ m
      · have hmk : m < k := Nat.lt_of_succ_lt hsk
        have hIH : H (a.val + 1) ≤ H (m + 1) := ih hmk hjm
        have hm1n : m + 1 ≤ n := Nat.le_of_lt_succ (lt_of_lt_of_le hsk hk)
        have hc : H (m + 1) ≤ H (m + 2) := hchain (m + 1) (by
          rw [Finset.mem_Icc]
          omega)
        exact le_trans hIH hc
      · have : a.val = m + 1 := by omega
        rw [this]

/-- A linearly independent family has no zero member. -/
lemma linearIndependent_apply_ne_zero {ι : Type*} {M : Type*} [AddCommGroup M] [Module ℝ M]
    {v : ι → M} (hv : LinearIndependent ℝ v) (i : ι) : v i ≠ 0 := by
  intro hvi
  have hrel : (Finsupp.linearCombination ℝ v) (Finsupp.single i (1 : ℝ)) =
      (Finsupp.linearCombination ℝ v) 0 := by
    simp [hvi]
  have hz : Finsupp.single i (1 : ℝ) = 0 := hv hrel
  have hone : (1 : ℝ) = 0 := by
    have := congrArg (fun f : ι →₀ ℝ => f i) hz
    simpa using this
  exact one_ne_zero hone

/-- Members `Q i` of the weak-4.1 family (linear independent) are nonzero. -/
lemma qi_ne_zero_of_li {Q : ℕ → Polynomial ℤ} {n i : ℕ}
    (hi : i ∈ Finset.Icc 1 (n + 1))
    (hLI : LinearIndependent ℝ (fun j : Fin (n + 1) =>
      (Q (j.val + 1)).map (Int.castRingHom ℝ))) :
    Q i ≠ 0 := by
  intro hQi
  have hi1 : 1 ≤ i := (Finset.mem_Icc.mp hi).1
  have hin : i ≤ n + 1 := (Finset.mem_Icc.mp hi).2
  have hlt : i - 1 < n + 1 := by omega
  have hv : (fun j : Fin (n + 1) => (Q (j.val + 1)).map (Int.castRingHom ℝ))
      ⟨i - 1, hlt⟩ ≠ 0 :=
    linearIndependent_apply_ne_zero hLI ⟨i - 1, hlt⟩
  apply hv
  have hsub : i - 1 + 1 = i := by omega
  simp [hsub, hQi]

/-- Linear independence of a `Fin (n+1)`-indexed family of polynomials (index
`Q (i.val + 1)`) restricts to the `Fin k` subfamily for `k ≤ n+1`. -/
lemma fin_linIndep_sub {n k : ℕ} (hk : k ≤ n + 1) (Q : ℕ → Polynomial ℤ)
    (hLI : LinearIndependent ℝ (fun i : Fin (n + 1) =>
      (Q (i.val + 1)).map (Int.castRingHom ℝ))) :
    LinearIndependent ℝ (fun i : Fin k =>
      (Q (i.val + 1)).map (Int.castRingHom ℝ)) := by
  let f : Fin k → Fin (n + 1) := fun i => ⟨i.val, lt_of_lt_of_le i.isLt hk⟩
  have hf : Function.Injective f := by
    intro a b hab
    apply Fin.ext
    dsimp [f] at hab
    simpa using congrArg Fin.val hab
  have hLI' : LinearIndependent ℝ ((fun i : Fin (n + 1) =>
      (Q (i.val + 1)).map (Int.castRingHom ℝ)) ∘ f) :=
    LinearIndependent.comp hLI f hf
  convert hLI' using 1
  funext i
  rfl


/-- `∏ H^a_i = H^(∑ a_i)` over a finite set (H positive). -/
lemma rpow_sum {H : ℝ} (hH : 0 < H) (s : Finset ℕ) (a : ℕ → ℝ) :
    (∏ i ∈ s, H ^ a i) = H ^ (∑ i ∈ s, a i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert b t hbt ih =>
      simp [hbt, ih, Finset.sum_insert hbt, Real.rpow_add hH]

/-- Base-swap for a negative power: `B ≤ c·H` gives `H^(-e) ≤ c^e · B^(-e)`. -/
lemma pow_neg_base_transfer {H B c e : ℝ} (hH : 0 < H) (hB : 0 < B) (hc : 1 ≤ c)
    (he : 0 < e) (hBle : B ≤ c * H) : H ^ (-e) ≤ c ^ e * B ^ (-e) := by
  have hBc : 0 < B / c := div_pos hB (lt_of_lt_of_le zero_lt_one hc)
  have hHle : B / c ≤ H := by
    rw [div_le_iff₀ (lt_of_lt_of_le zero_lt_one hc)]
    simpa [mul_comm] using hBle
  have hneg := rpow_neg_antitone_le (a := H) (b := B / c) (e := e) hH hBc he hHle
  calc
    H ^ (-e) ≤ (B / c) ^ (-e) := hneg
    _ = c ^ e * B ^ (-e) := by
      rw [Real.div_rpow (le_of_lt hB) (le_trans zero_le_one hc) (-e)]
      have hcne : c ≠ 0 := ne_of_gt (lt_of_lt_of_le zero_lt_one hc)
      have hce : (c : ℝ) ^ (-e) = (c ^ e)⁻¹ := by
        rw [Real.rpow_neg (le_of_lt (lt_of_lt_of_le zero_lt_one hc)) e]
      rw [hce]
      field_simp [hcne, Real.rpow_pos_of_pos hB (-e), Real.rpow_pos_of_pos (lt_of_lt_of_le zero_lt_one hc) e]

/-- A chain `a_i ≤ a_{i+1}` on `Icc 2 n` makes `a` nondecreasing on `Icc 2 (n+1)`. -/
lemma a_le_of_chain {a : ℕ → ℝ} {n u v : ℕ} (hu2 : 2 ≤ u) (hvn : v ≤ n + 1) (huv : u ≤ v)
    (hchain : ∀ i ∈ Finset.Icc 2 n, a i ≤ a (i + 1)) : a u ≤ a v := by
  have hclaim : ∀ d : ℕ, u + d ≤ v → a u ≤ a (u + d) := by
    intro d
    induction d with
    | zero =>
        intro _
        exact le_rfl
    | succ d ih =>
        intro hd
        have hd' : u + d ≤ v := by omega
        have hIH : a u ≤ a (u + d) := ih hd'
        have hmem : u + d ∈ Finset.Icc 2 n := by
          rw [Finset.mem_Icc]
          omega
        have hc := hchain (u + d) hmem
        have hstep : a (u + d) ≤ a (u + (d + 1)) := by
          simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hc
        exact le_trans hIH hstep
  have huv' : u + (v - u) ≤ v := by omega
  have hres := hclaim (v - u) huv'
  have hvv : u + (v - u) = v := by omega
  simpa [hvv] using hres


/-- Products over the `Fin k` subfamily (indices with value ≥ 2) equal products
over `Icc 3 k` in the natural indices. -/
lemma prod_fin_filter_Icc (k : ℕ) (f : ℕ → ℝ) :
    (∏ j ∈ (Finset.univ.filter (fun j : Fin k => 2 ≤ j.val)), f (j.val + 1)) =
      (∏ i ∈ Finset.Icc 3 k, f i) := by
  classical
  by_cases hk : 3 ≤ k
  · let s : Finset (Fin k) := Finset.univ.filter (fun j : Fin k => 2 ≤ j.val)
    let φ : Fin k → ℕ := fun j => j.val + 1
    have him : s.image φ = Finset.Icc 3 k := by
      ext i
      rw [mem_image]
      constructor
      · rintro ⟨j, hj, rfl⟩
        rw [mem_filter] at hj
        rw [mem_Icc]
        simp [φ]
        omega
      · intro hi
        rw [mem_Icc] at hi
        have hjv : 2 ≤ i - 1 := by omega
        have hjk : i - 1 < k := by omega
        refine ⟨⟨i - 1, hjk⟩, ?_, ?_⟩
        · rw [mem_filter]
          constructor
          · exact mem_univ _
          · simpa using hjv
        · simp [φ]
          omega
    have hinj : Set.InjOn φ (↑s : Set (Fin k)) := by
      intro a ha b hb hab
      dsimp [φ] at hab
      apply Fin.ext
      omega
    have himage : (∏ j ∈ s.image φ, f j) = ∏ j ∈ s, f (j.val + 1) := by
      rw [Finset.prod_image hinj]
    calc
      (∏ j ∈ s, f (j.val + 1)) = ∏ j ∈ s.image φ, f j := himage.symm
      _ = ∏ i ∈ Finset.Icc 3 k, f i := by rw [him]
  · have hs_empty : (Finset.univ.filter (fun j : Fin k => 2 ≤ j.val)) = ∅ := by
      ext j
      simp
      omega
    have hi_empty : Finset.Icc 3 k = ∅ := by
      ext i
      simp
      omega
    rw [hs_empty, hi_empty]
    simp

/-- `(H^t)^2 = H^(2t)` for `0 ≤ H`. -/
lemma rpow_sq {H t : ℝ} (hH : 0 ≤ H) : (H ^ t) ^ 2 = H ^ (2 * t) := by
  calc
    (H ^ t) ^ 2 = (H ^ t) ^ (2 : ℝ) := (Real.rpow_natCast (H ^ t) 2).symm
    _ = H ^ (t * 2) := (Real.rpow_mul hH t (2 : ℝ)).symm
    _ = H ^ (2 * t) := by congr 1; ring

/-- Final transfer chain (all left-associated): from `D ≤ cb·c0²·Hbase^{−E}` with
`T ≤ E`, `Hgt ≤ cb·Hbase`, deduce `D ≤ cb·c0²·cb^{2X+1}·Hgt^{−T}`. -/
lemma rpow_chain_final {D cb c0 Hbase Hgt E T X : ℝ}
    (hD : D ≤ cb * c0 ^ 2 * Hbase ^ (-E))
    (hcb : 1 ≤ cb) (hHbase1 : 1 ≤ Hbase) (hHgt1 : 1 ≤ Hgt)
    (hTpos : 0 < T) (hET : T ≤ E) (hHgtle : Hgt ≤ cb * Hbase)
    (hTX : T ≤ 2 * X + 1) :
    D ≤ cb * c0 ^ 2 * cb ^ (2 * X + 1) * Hgt ^ (-T) := by
  have hc0 : 0 ≤ cb * c0 ^ 2 := by positivity
  have hmono1 : Hbase ^ (-E) ≤ Hbase ^ (-T) := by
    apply rpow_mono_exp hHbase1
    linarith
  have hbasepos : 0 < Hbase := lt_of_lt_of_le zero_lt_one hHbase1
  have hgtpos : 0 < Hgt := lt_of_lt_of_le zero_lt_one hHgt1
  have htr := pow_neg_base_transfer (H := Hbase) (B := Hgt) (c := cb) (e := T)
    hbasepos hgtpos hcb hTpos hHgtle
  have hcbT : cb ^ T ≤ cb ^ (2 * X + 1) := by
    exact Real.rpow_le_rpow_of_exponent_le hcb hTX
  calc
    D ≤ cb * c0 ^ 2 * Hbase ^ (-E) := hD
    _ ≤ cb * c0 ^ 2 * Hbase ^ (-T) := by
      exact mul_le_mul_of_nonneg_left hmono1 hc0
    _ ≤ cb * c0 ^ 2 * (cb ^ T * Hgt ^ (-T)) := by
      exact mul_le_mul_of_nonneg_left htr hc0
    _ = cb * c0 ^ 2 * cb ^ T * Hgt ^ (-T) := by ring
    _ ≤ cb * c0 ^ 2 * cb ^ (2 * X + 1) * Hgt ^ (-T) := by
      have h1 : cb * c0 ^ 2 * cb ^ T ≤ cb * c0 ^ 2 * cb ^ (2 * X + 1) := by
        exact mul_le_mul_of_nonneg_left hcbT hc0
      have h2 : 0 ≤ Hgt ^ (-T) := by positivity
      exact mul_le_mul_of_nonneg_right h1 h2

/-- rpow exponent upper bound `c1 ^ E ≤ c1 ^ B` for `1 ≤ c1` and `E ≤ B`. -/
lemma rpow_pow_le {c1 E B : ℝ} (hc1 : 1 ≤ c1) (hEB : E ≤ B) :
    c1 ^ E ≤ c1 ^ B := by
  exact Real.rpow_le_rpow_of_exponent_le hc1 hEB


/-! ### Batch 10: the per-P conversion (Section 5/6 transfer + exponent algebra)

`perP_data` takes one member `P` of the Wirsing family together with its
`weak_lemma41` output (the polynomial family `Q` and exponent `x`) and produces
the admissible weight sequence `aᵢ = log Hᵢ/log H₂` together with an algebraic
`α` of degree ≤ n satisfying the two final bounds with the uniform constants
`PBound`/`P0Bound` (which depend only on `n, ξ, c0, X`). -/

/-- The normalized Prop-5.1 constant (≥ 1). -/
noncomputable def Cb (n : ℕ) (hn : 2 ≤ n) (ξ : ℝ) : ℝ :=
  max (Classical.choose (poels_prop51_real n hn ξ)) 1

/-- The uniform constant in the main per-P bound. -/
noncomputable def PBound (n : ℕ) (hn : 2 ≤ n) (ξ : ℝ) (c0 X : ℝ) : ℝ :=
  Cb n hn ξ * c0 ^ 2 * Cb n hn ξ ^ (2 * X + 1)

/-- The uniform constant in the per-P `‖P‖ → 0` bound. -/
noncomputable def P0Bound (n : ℕ) (hn : 2 ≤ n) (ξ : ℝ) (c0 : ℝ) : ℝ :=
  Cb n hn ξ * c0 ^ 2

/-- Per-P conversion: from the weak-4.1 family `Q` and exponent `x` attached to
`P = Q 2`, produce the admissible log-weights `a` (with `Σ aᵢ = x`) and an
algebraic `α` of degree ≤ n with `0 < ‖ξ−α‖`, the main bound
`‖ξ−α‖ ≤ PBound·Hgt(α)^{−Λ−1+2ε}` and the decay bound
`‖ξ−α‖ ≤ P0Bound·‖P‖^{−(2−2ε)}`. -/
lemma perP_data (n : ℕ) (hn : 2 ≤ n) (ξ : ℝ) (hξ : Transcendental ℚ ξ)
    (eps : ℝ) (heps0 : 0 < eps) (heps1 : eps < 1 / 2)
    (X : ℝ) (hX0 : 0 ≤ X)
    (c0 : ℝ) (hc01 : 1 ≤ c0)
    (Q : ℕ → Polynomial ℤ) (x : ℝ) (P : Polynomial ℤ)
    (hQ2 : Q 2 = P)
    (hxn : (n : ℝ) ≤ x) (hxX : x ≤ X)
    (hdegQ : ∀ i ∈ Finset.Icc 1 (n + 1), (Q i).natDegree ≤ n)
    (hLI : LinearIndependent ℝ (fun i : Fin (n + 1) =>
      (Q (i.val + 1)).map (Int.castRingHom ℝ)))
    (hqcop : IsCoprime ((Q 1).map (algebraMap ℤ ℚ)) ((Q 2).map (algebraMap ℤ ℚ)))
    (hchain : ∀ i ∈ Finset.Icc 1 n, supN (Q i) ≤ supN (Q (i + 1)))
    (hH2le : ∀ i ∈ Finset.Icc 2 (n + 1), supN (Q 2) ≤ supN (Q i))
    (hprod : (∏ i ∈ Finset.Icc 2 (n + 1), supN (Q i)) = supN (Q 2) ^ x)
    (heval : ∀ i ∈ Finset.Icc 1 (n + 1),
      ‖Polynomial.eval ξ ((Q i).map (Int.castRingHom ℝ))‖ ≤
        c0 * supN (Q 2) ^ (-x + eps))
    (hP2 : 2 ≤ supN P) :
    ∃ a : ℕ → ℝ, ∃ α : ℂ,
      a 2 = 1 ∧
      (∀ i : ℕ, i ∈ Finset.Icc 2 n → a i ≤ a (i + 1)) ∧
      ((∑ i ∈ Finset.Icc 2 (n + 1), a i) = x) ∧
      (∀ i : ℕ, i ∈ Finset.Icc 2 (n + 1) → 1 ≤ a i) ∧
      IsAlgebraic ℚ α ∧ Polynomial.natDegree (minpoly ℚ α) ≤ n ∧
      0 < ‖(ξ : ℂ) - α‖ ∧
      ‖(ξ : ℂ) - α‖ ≤ PBound n hn ξ c0 X * (Hgt α) ^ (-LamInline n x a - 1 + 2 * eps) ∧
      ‖(ξ : ℂ) - α‖ ≤ P0Bound n hn ξ c0 * supN P ^ (-(2 - 2 * eps)) := by
  classical
  let H : ℕ → ℝ := fun i => supN (Q i)
  let H2 : ℝ := supN (Q 2)
  let a : ℕ → ℝ := fun i => Real.log (H i) / Real.log H2
  have hQ2P : Q 2 = P := hQ2
  have hH2P : H2 = supN P := by dsimp [H2]; rw [hQ2P]
  have hH2gt1 : 1 < H2 := by
    rw [hH2P]
    linarith
  have hH2pos : 0 < H2 := lt_trans zero_lt_one hH2gt1
  have hchain2 : ∀ i ∈ Finset.Icc 2 n, H i ≤ H (i + 1) := by
    intro i hi
    dsimp [H]
    exact hchain i (by rw [Finset.mem_Icc] at hi ⊢; omega)
  have hprodH : (∏ i ∈ Finset.Icc 2 (n + 1), H i) = H2 ^ x := by
    dsimp [H, H2]
    exact hprod
  have hadm := admissible_from_heights n hn x H2 H hH2gt1 (by rfl) hchain2 hH2le hprodH
  have ha2 : a 2 = 1 := by simpa [a, H, H2] using hadm.1
  have hachain : ∀ i ∈ Finset.Icc 2 n, a i ≤ a (i + 1) := by
    simpa [a, H, H2] using hadm.2.1
  have hasum : (∑ i ∈ Finset.Icc 2 (n + 1), a i) = x := by
    simpa [a, H, H2] using hadm.2.2.1
  have ha1 : ∀ i ∈ Finset.Icc 2 (n + 1), 1 ≤ a i := by
    simpa [a, H, H2] using hadm.2.2.2
  have hHpos_range : ∀ i ∈ Finset.Icc 2 (n + 1), 0 < H i := by
    intro i hi
    exact lt_of_lt_of_le hH2pos (hH2le i hi)
  have hHi_a : ∀ i ∈ Finset.Icc 2 (n + 1), H2 ^ a i = H i := by
    intro i hi
    have hlog := rpow_log_div_log (H := H2) (x := H i) hH2gt1 (hHpos_range i hi)
    simpa [a] using hlog
  have hH1mem : 1 ∈ Finset.Icc 1 (n + 1) := by rw [Finset.mem_Icc]; omega
  have hQ1ne : Q 1 ≠ 0 := qi_ne_zero_of_li hH1mem hLI
  have hH1ge1 : 1 ≤ H 1 := by
    dsimp [H]
    exact supN_one_le hQ1ne
  have hH1leH2 : H 1 ≤ H2 := by
    dsimp [H, H2]
    exact hchain 1 (by rw [Finset.mem_Icc]; omega)
  have hH1pos : 0 < H 1 := lt_of_lt_of_le zero_lt_one hH1ge1
  have hH1ge0 : 0 ≤ H 1 := le_of_lt hH1pos
  let Λ : ℝ := Lambda n x a
  have hLam_mem := Lambda_mem n hn x a
  rcases hLam_mem with ⟨k, hk_mem, hLamk⟩
  have hk2 : 2 ≤ k := (Finset.mem_Icc.mp hk_mem).1
  have hkn : k ≤ n + 1 := (Finset.mem_Icc.mp hk_mem).2
  let A : ℝ := 2 * x - 2 * (((n : ℝ) - (k : ℝ)) + 1) - (∑ i ∈ Finset.Icc 2 k, a i)
  have hΛA : Λ = A / a k := by
    dsimp [Λ, A]
    simpa using hLamk
  have hak1 : 1 ≤ a k := ha1 k hk_mem
  have hakpos : 0 < a k := lt_of_lt_of_le zero_lt_one hak1
  have hAge1 : 1 ≤ A := by
    dsimp [A]
    exact A_lower n k x a hk_mem hasum ha1
  have hAge0 : 0 ≤ A := le_trans zero_le_one hAge1
  have hΛge0 : 0 ≤ Λ := by
    rw [hΛA]
    exact div_nonneg hAge0 (le_of_lt hakpos)
  have hΛleA : Λ ≤ A := by
    rw [hΛA]
    exact (div_le_iff₀ hakpos).mpr (by nlinarith)
  have hA2x : A ≤ 2 * x := by
    dsimp [A]
    have h1 : 0 ≤ 2 * (((n : ℝ) - (k : ℝ)) + 1) := by
      have hkn' : (k : ℝ) ≤ (n : ℝ) + 1 := by exact_mod_cast hkn
      nlinarith
    have h2 : 0 ≤ (∑ i ∈ Finset.Icc 2 k, a i) := by
      apply Finset.sum_nonneg
      intro i hi
      have hmem' : i ∈ Finset.Icc 2 (n + 1) := by
        rw [Finset.mem_Icc] at hi ⊢
        omega
      exact le_trans zero_le_one (ha1 i hmem')
    linarith
  have hΛ2x : Λ ≤ 2 * x := le_trans hΛleA hA2x
  let T : ℝ := Λ + 1 - 2 * eps
  have hTpos : 0 < T := by
    dsimp [T]
    have h12 : 0 < 1 - 2 * eps := by linarith
    linarith
  have hT2X : T ≤ 2 * X + 1 := by
    dsimp [T]
    have hxX' : 2 * x ≤ 2 * X := mul_le_mul_of_nonneg_left hxX (by norm_num)
    linarith
  let c1 : ℝ := Classical.choose (poels_prop51_real n hn ξ)
  have hc1spec := Classical.choose_spec (poels_prop51_real n hn ξ)
  let cb : ℝ := max c1 1
  have hcb1 : 1 ≤ cb := by dsimp [cb]; exact le_max_right c1 1
  have hc1cb : c1 ≤ cb := by dsimp [cb]; exact le_max_left c1 1
  let δ : ℝ := c0 * H2 ^ (-x + eps)
  have hδpos : 0 < δ := by
    dsimp [δ]
    exact mul_pos (lt_of_lt_of_le zero_lt_one hc01) (Real.rpow_pos_of_pos hH2pos _)
  let Psub : Fin k → Polynomial ℤ := fun i => Q (i.val + 1)
  have hdegsub : ∀ i : Fin k, (Psub i).natDegree ≤ n := by
    intro i
    dsimp [Psub]
    apply hdegQ
    rw [Finset.mem_Icc]
    omega
  have hLIsub : LinearIndependent ℝ (fun i : Fin k =>
      (Psub i).map (Int.castRingHom ℝ)) := by
    have hLI' : LinearIndependent ℝ (fun i : Fin k =>
        (Q (i.val + 1)).map (Int.castRingHom ℝ)) := fin_linIndep_sub hkn Q hLI
    simpa [Psub] using hLI'
  have hcopsub : IsCoprime ((Psub ⟨0, by omega⟩).map (Int.castRingHom ℝ))
      ((Psub ⟨1, by omega⟩).map (Int.castRingHom ℝ)) := by
    simpa [Psub] using qcop_map_real (Q 1) (Q 2) hqcop
  have hmonosub : Monotone (fun i : Fin k =>
      ((Psub i).map (Int.castRingHom ℝ)).supNorm) := by
    have hm : Monotone (fun i : Fin k => H (i.val + 1)) := by
      apply monotone_fin_of_chain hkn (H := H)
      intro i hi
      exact hchain i (by rw [Finset.mem_Icc] at hi ⊢; omega)
    simpa [Psub, H, supN] using hm
  have hevalsub : ∀ i : Fin k, ‖Polynomial.eval ξ ((Psub i).map (Int.castRingHom ℝ))‖ ≤ δ := by
    intro i
    dsimp [Psub]
    have hmem : i.val + 1 ∈ Finset.Icc 1 (n + 1) := by
      rw [Finset.mem_Icc]
      omega
    have hb := heval (i.val + 1) hmem
    simpa [δ, H2] using hb
  rcases (hc1spec.2 k hk2 hkn Psub δ hδpos hdegsub hLIsub hcopsub hmonosub hevalsub) with
    ⟨m, α, hAlg, hdegα, hHgt51, hdist51⟩
  let Hm : ℝ := H (m.val + 1)
  have hHm1 : 1 ≤ Hm := by
    dsimp [Hm]
    have hmem : m.val + 1 ∈ Finset.Icc 1 (n + 1) := by
      rw [Finset.mem_Icc]
      omega
    exact supN_one_le (qi_ne_zero_of_li hmem hLI)
  have hHm_pos : 0 < Hm := lt_of_lt_of_le zero_lt_one hHm1
  have hHgt2 : Hgt α ≤ cb * Hm := by
    have h1 : Hgt α ≤ c1 * Hm := by
      dsimp [Hm]
      have hs := hHgt51
      simpa [Psub, H, Hgt, supN] using hs
    have h2 : c1 * Hm ≤ cb * Hm := mul_le_mul_of_nonneg_right hc1cb hHm_pos.le
    exact le_trans h1 h2
  have hHgtge1 : 1 ≤ Hgt α := height_ge_one α hAlg
  -- F0 := the (cb-free) right-hand side of the Prop 5.1 bound with δ expanded
  let F0 : ℝ := c0 ^ 2 * H2 ^ (-2 * x + 2 * eps) * (H 1) ^ (n + 1 - k) *
      (H 2) ^ (n + 2 - k) * (∏ i ∈ Finset.Icc 3 k, H i) * (Hm)⁻¹
  have hdsq : δ ^ 2 = c0 ^ 2 * H2 ^ (-2 * x + 2 * eps) := by
    dsimp [δ]
    rw [mul_pow]
    rw [rpow_sq (le_of_lt hH2pos)]
    congr 1
    ring
  have hfilter : (∏ j ∈ (Finset.univ.filter (fun j : Fin k => 2 ≤ j.val)),
        ((Psub j).map (Int.castRingHom ℝ)).supNorm) = ∏ i ∈ Finset.Icc 3 k, H i := by
    have hp := prod_fin_filter_Icc k (fun i : ℕ => H i)
    simpa [Psub, H, supN] using hp
  have hHi_nonneg : ∀ i : ℕ, 0 ≤ H i := by
    intro i
    dsimp [H]
    exact supN_nonneg (Q i)
  have hF0ge0 : 0 ≤ F0 := by
    dsimp [F0]
    have h1 : 0 ≤ c0 ^ 2 := by positivity
    have h2 : 0 ≤ H2 ^ (-2 * x + 2 * eps) := Real.rpow_nonneg (le_of_lt hH2pos) _
    have h3 : 0 ≤ (H 1) ^ (n + 1 - k) := pow_nonneg (hHi_nonneg 1) _
    have h4 : 0 ≤ (H 2) ^ (n + 2 - k) := pow_nonneg (hHi_nonneg 2) _
    have h5 : 0 ≤ ∏ i ∈ Finset.Icc 3 k, H i := Finset.prod_nonneg (by intro i hi; exact hHi_nonneg i)
    have h12 : 0 ≤ c0 ^ 2 * H2 ^ (-2 * x + 2 * eps) := mul_nonneg h1 h2
    have h123 : 0 ≤ c0 ^ 2 * H2 ^ (-2 * x + 2 * eps) * (H 1) ^ (n + 1 - k) := mul_nonneg h12 h3
    have h1234 : 0 ≤ c0 ^ 2 * H2 ^ (-2 * x + 2 * eps) * (H 1) ^ (n + 1 - k) *
        (H 2) ^ (n + 2 - k) := mul_nonneg h123 h4
    have hA : 0 ≤ c0 ^ 2 * H2 ^ (-2 * x + 2 * eps) * (H 1) ^ (n + 1 - k) *
        (H 2) ^ (n + 2 - k) * (∏ i ∈ Finset.Icc 3 k, H i) := mul_nonneg h1234 h5
    exact mul_nonneg hA (inv_nonneg.mpr hHm_pos.le)
  have hF0eq : F0 = δ ^ 2 * (H 1) ^ (n + 1 - k) * (H 2) ^ (n + 2 - k) *
      (∏ j ∈ (Finset.univ.filter (fun j : Fin k => 2 ≤ j.val)),
        ((Psub j).map (Int.castRingHom ℝ)).supNorm) * (Hm)⁻¹ := by
    dsimp [F0]
    rw [hdsq, hfilter]
  have hF0ge0 : 0 ≤ F0 := by
    dsimp [F0]
    have h1 : 0 ≤ c0 ^ 2 := by positivity
    have h2 : 0 ≤ H2 ^ (-2 * x + 2 * eps) := Real.rpow_nonneg (le_of_lt hH2pos) _
    have h3 : 0 ≤ (H 1) ^ (n + 1 - k) := pow_nonneg (hHi_nonneg 1) _
    have h4 : 0 ≤ (H 2) ^ (n + 2 - k) := pow_nonneg (hHi_nonneg 2) _
    have h5 : 0 ≤ ∏ i ∈ Finset.Icc 3 k, H i := Finset.prod_nonneg (by intro i hi; exact hHi_nonneg i)
    have h12 : 0 ≤ c0 ^ 2 * H2 ^ (-2 * x + 2 * eps) := mul_nonneg h1 h2
    have h123 : 0 ≤ c0 ^ 2 * H2 ^ (-2 * x + 2 * eps) * (H 1) ^ (n + 1 - k) := mul_nonneg h12 h3
    have h1234 : 0 ≤ c0 ^ 2 * H2 ^ (-2 * x + 2 * eps) * (H 1) ^ (n + 1 - k) *
        (H 2) ^ (n + 2 - k) := mul_nonneg h123 h4
    have hA : 0 ≤ c0 ^ 2 * H2 ^ (-2 * x + 2 * eps) * (H 1) ^ (n + 1 - k) *
        (H 2) ^ (n + 2 - k) * (∏ i ∈ Finset.Icc 3 k, H i) := mul_nonneg h1234 h5
    exact mul_nonneg hA (inv_nonneg.mpr hHm_pos.le)
  have hdistF : ‖(ξ : ℂ) - α‖ ≤ cb * F0 := by
    have hGge0 : 0 ≤ δ ^ 2 * (H 1) ^ (n + 1 - k) * (H 2) ^ (n + 2 - k) *
        (∏ j ∈ (Finset.univ.filter (fun j : Fin k => 2 ≤ j.val)),
          ((Psub j).map (Int.castRingHom ℝ)).supNorm) * (Hm)⁻¹ := by
      rw [← hF0eq]
      exact hF0ge0
    have h1c : ‖(ξ : ℂ) - α‖ ≤
        c1 * (δ ^ 2 * (H 1) ^ (n + 1 - k) * (H 2) ^ (n + 2 - k) *
          (∏ j ∈ (Finset.univ.filter (fun j : Fin k => 2 ≤ j.val)),
            ((Psub j).map (Int.castRingHom ℝ)).supNorm) * (Hm)⁻¹) := by
      calc
        ‖(ξ : ℂ) - α‖ ≤ (c1 * δ ^ 2 * (H 1) ^ (n + 1 - k) * (H 2) ^ (n + 2 - k) *
              (∏ j ∈ (Finset.univ.filter (fun j : Fin k => 2 ≤ j.val)),
                ((Psub j).map (Int.castRingHom ℝ)).supNorm)) * (Hm)⁻¹ := by
          simpa [Psub, Hm, H, supN] using hdist51
        _ = c1 * (δ ^ 2 * (H 1) ^ (n + 1 - k) * (H 2) ^ (n + 2 - k) *
              (∏ j ∈ (Finset.univ.filter (fun j : Fin k => 2 ≤ j.val)),
                ((Psub j).map (Int.castRingHom ℝ)).supNorm) * (Hm)⁻¹) := by ring
    calc
      ‖(ξ : ℂ) - α‖ ≤ cb * (δ ^ 2 * (H 1) ^ (n + 1 - k) * (H 2) ^ (n + 2 - k) *
          (∏ j ∈ (Finset.univ.filter (fun j : Fin k => 2 ≤ j.val)),
            ((Psub j).map (Int.castRingHom ℝ)).supNorm) * (Hm)⁻¹) := by
        exact le_trans h1c (mul_le_mul_of_nonneg_right hc1cb hGge0)
      _ = cb * F0 := by
        congr 1
        exact hF0eq.symm

  -- final exponent identity
  have hLamEq' : LamInline n x a = Λ := by
    dsimp [Λ]
    exact LamInline_eq_Lambda n hn x a
  have hTexp : -LamInline n x a - 1 + 2 * eps = -T := by
    dsimp [T]
    rw [hLamEq']
    ring
  -- α ≠ ξ and 0 < dist
  refine ⟨a, α, ha2, hachain, hasum, ha1, hAlg, hdegα, ?hpos, ?hbd1, ?hbd2⟩
  · exact dist_pos_of_algebraic ξ hξ α hAlg
  · -- main bound; case analysis on the index m
    rw [hTexp]
    by_cases hm0 : m.val = 0
    · -- m = 1 (index 1); subcase on k
      by_cases hklt : k ≤ n
      · -- case: m = 1 and k ≤ n
        have hHm1' : Hm = H 1 := by
          dsimp [Hm]
          simp [hm0]
        have hH1ne : H 1 ≠ 0 := ne_of_gt hH1pos
        have hHgt2' : Hgt α ≤ cb * H2 := by
          calc
            Hgt α ≤ cb * Hm := hHgt2
            _ = cb * H 1 := by rw [hHm1']
            _ ≤ cb * H2 := by
              exact mul_le_mul_of_nonneg_left hH1leH2 (le_trans zero_le_one hcb1)
        let S3 : ℝ := ∑ i ∈ Finset.Icc 3 k, a i
        have hS2eq : (∑ i ∈ Finset.Icc 2 k, a i) = 1 + S3 := by
          dsimp [S3]
          have hsplit := sum_Icc_split_add 2 2 k (by omega) hk2 a
          calc
            (∑ i ∈ Finset.Icc 2 k, a i) = (∑ i ∈ Finset.Icc 2 2, a i) + (∑ i ∈ Finset.Icc 3 k, a i) := hsplit
            _ = 1 + (∑ i ∈ Finset.Icc 3 k, a i) := by simp [ha2]
        have hprod3 : (∏ i ∈ Finset.Icc 3 k, H i) = H2 ^ S3 := by
          dsimp [S3]
          calc
            (∏ i ∈ Finset.Icc 3 k, H i) = (∏ i ∈ Finset.Icc 3 k, H2 ^ a i) := by
              apply Finset.prod_congr rfl
              intro i hi
              have hmem' : i ∈ Finset.Icc 2 (n + 1) := by
                rw [Finset.mem_Icc] at hi ⊢
                omega
              exact (hHi_a i hmem').symm
            _ = H2 ^ (∑ i ∈ Finset.Icc 3 k, a i) := rpow_sum hH2pos (Finset.Icc 3 k) a
        have hsplitn : n + 1 - k = (n - k) + 1 := by omega
        have hH1split : (H 1) ^ (n + 1 - k) * (H 1)⁻¹ = (H 1) ^ (n - k) := by
          rw [hsplitn, pow_succ]
          field_simp [hH1ne]
        have hH1pow2 : (H 1) ^ (n - k) ≤ (H 2) ^ (n - k) := by
          exact pow_le_pow_left₀ hH1ge0 hH1leH2 (n - k)
        have hPosRestB : 0 ≤ H2 ^ (-2 * x + 2 * eps) * (H 2) ^ (n + 2 - k) *
              (∏ i ∈ Finset.Icc 3 k, H i) := by
          have h2a : 0 ≤ H2 ^ (-2 * x + 2 * eps) := Real.rpow_nonneg (le_of_lt hH2pos) _
          have h2b : 0 ≤ (H 2) ^ (n + 2 - k) := pow_nonneg (hHi_nonneg 2) _
          have h2c : 0 ≤ ∏ i ∈ Finset.Icc 3 k, H i := Finset.prod_nonneg (by intro i hi; exact hHi_nonneg i)
          have hab : 0 ≤ H2 ^ (-2 * x + 2 * eps) * (H 2) ^ (n + 2 - k) := mul_nonneg h2a h2b
          exact mul_nonneg hab h2c
        have hcastB1 : ((n - k : ℕ) : ℝ) = (n : ℝ) - (k : ℝ) := by
          rw [Nat.cast_sub (by omega : k ≤ n)]
        have hcastB2 : ((n + 2 - k : ℕ) : ℝ) = (n : ℝ) + 2 - (k : ℝ) := by
          rw [Nat.cast_sub (by omega : k ≤ n + 2)]
          simp
        have hEeqB : -2 * x + 2 * eps + ((n - k : ℕ) : ℝ) + ((n + 2 - k : ℕ) : ℝ) + S3
            = -A - 1 + 2 * eps := by
          dsimp [A]
          rw [hS2eq, hcastB1, hcastB2]
          ring
        let EB : ℝ := A + 1 - 2 * eps
        have hExpB : -A - 1 + 2 * eps = -(A + 1 - 2 * eps) := by ring
        have hETB : T ≤ EB := by
          dsimp [T, EB]
          nlinarith [hΛleA]
        have hF0leB : F0 ≤ c0 ^ 2 * H2 ^ (-(A + 1 - 2 * eps)) := by
          calc
            F0 = c0 ^ 2 * (H2 ^ (-2 * x + 2 * eps) * (H 1) ^ (n + 1 - k) * (H 2) ^ (n + 2 - k) *
                  (∏ i ∈ Finset.Icc 3 k, H i) * (Hm)⁻¹) := by
              dsimp [F0]
              ring
            _ ≤ c0 ^ 2 * H2 ^ (-(A + 1 - 2 * eps)) := by
              apply mul_le_mul_of_nonneg_left _ (by positivity : 0 ≤ c0 ^ 2)
              calc
                (H2 ^ (-2 * x + 2 * eps) * (H 1) ^ (n + 1 - k) * (H 2) ^ (n + 2 - k) *
                    (∏ i ∈ Finset.Icc 3 k, H i) * (Hm)⁻¹)
                    = (H 1) ^ (n + 1 - k) * (H 1)⁻¹ * (H2 ^ (-2 * x + 2 * eps) * (H 2) ^ (n + 2 - k) *
                        (∏ i ∈ Finset.Icc 3 k, H i)) := by
                      rw [hHm1']
                      ring
                _ = (H 1) ^ (n - k) * (H2 ^ (-2 * x + 2 * eps) * (H 2) ^ (n + 2 - k) *
                        (∏ i ∈ Finset.Icc 3 k, H i)) := by
                      rw [hH1split]
                _ ≤ (H 2) ^ (n - k) * (H2 ^ (-2 * x + 2 * eps) * (H 2) ^ (n + 2 - k) *
                        (∏ i ∈ Finset.Icc 3 k, H i)) := by
                      exact mul_le_mul_of_nonneg_right hH1pow2 hPosRestB
                _ = H2 ^ (-2 * x + 2 * eps) * (H 2) ^ (n - k) * (H 2) ^ (n + 2 - k) *
                        (∏ i ∈ Finset.Icc 3 k, H i) := by ring
                _ = H2 ^ (-2 * x + 2 * eps) * (H 2) ^ (n - k) * (H 2) ^ (n + 2 - k) * H2 ^ S3 := by
                      rw [hprod3]
                _ = H2 ^ (-2 * x + 2 * eps + ((n - k : ℕ) : ℝ) + ((n + 2 - k : ℕ) : ℝ) + S3) := by
                      rw [← Real.rpow_natCast (H 2) (n - k)]
                      rw [← Real.rpow_natCast (H 2) (n + 2 - k)]
                      rw [← Real.rpow_add hH2pos]
                      rw [← Real.rpow_add hH2pos]
                      rw [← Real.rpow_add hH2pos]
                _ = H2 ^ (-A - 1 + 2 * eps) := by rw [hEeqB]
                _ = H2 ^ (-(A + 1 - 2 * eps)) := by rw [hExpB]
        have hcb0B : 0 ≤ cb := le_trans zero_le_one hcb1
        have hcollB : ‖(ξ : ℂ) - α‖ ≤ cb * c0 ^ 2 * H2 ^ (-EB) := by
          calc
            ‖(ξ : ℂ) - α‖ ≤ cb * F0 := hdistF
            _ ≤ cb * (c0 ^ 2 * H2 ^ (-(A + 1 - 2 * eps))) := by
              exact mul_le_mul_of_nonneg_left hF0leB hcb0B
            _ = cb * c0 ^ 2 * H2 ^ (-(A + 1 - 2 * eps)) := by ring
            _ = cb * c0 ^ 2 * H2 ^ (-EB) := by rfl
        have hfinB := rpow_chain_final (D := ‖(ξ : ℂ) - α‖) (cb := cb) (c0 := c0)
          (Hbase := H2) (Hgt := Hgt α) (E := EB) (T := T) (X := X) hcollB hcb1 hH2gt1.le
          hHgtge1 hTpos hETB hHgt2' hT2X
        simpa [PBound, Cb, cb] using hfinB
      · -- case: m = 1 and k = n+1
        have hkeq : k = n + 1 := by omega
        have hHm1' : Hm = H 1 := by
          dsimp [Hm]
          simp [hm0]
        have hHgtc1 : Hgt α ≤ cb * H 1 := by
          calc
            Hgt α ≤ cb * Hm := hHgt2
            _ = cb * H 1 := by rw [hHm1']
        have hcb0C : 0 ≤ cb := le_trans zero_le_one hcb1
        have hcbposC : 0 < cb := lt_of_lt_of_le zero_lt_one hcb1
        have hHgtc2 : Hgt α ≤ cb * H2 := by
          calc
            Hgt α ≤ cb * H 1 := hHgtc1
            _ ≤ cb * H2 := by exact mul_le_mul_of_nonneg_left hH1leH2 hcb0C
        have hpeel : (∏ i ∈ Finset.Icc 2 (n + 1), H i) = H 2 * (∏ i ∈ Finset.Icc 3 (n + 1), H i) := by
          have hset : Finset.Icc 2 (n + 1) = insert 2 (Finset.Icc 3 (n + 1)) := by
            ext i
            simp
            omega
          rw [hset]
          exact Finset.prod_insert (by simp : 2 ∉ Finset.Icc 3 (n + 1))
        have hH2P : H2 * (∏ i ∈ Finset.Icc 3 (n + 1), H i) = H2 ^ x := by
          have hh := hprodH
          rw [hpeel] at hh
          simpa using hh
        have hk1 : n + 1 - k = 0 := by omega
        have hk2C : n + 2 - k = 1 := by omega
        have hF0eqC : F0 = c0 ^ 2 * (H 1)⁻¹ * H2 ^ (-x + 2 * eps) := by
          have hstep1 : F0 = c0 ^ 2 * (H2 ^ (-2 * x + 2 * eps) * (H 1) ^ (n + 1 - k) * (H 2) ^ (n + 2 - k) *
                (∏ i ∈ Finset.Icc 3 k, H i) * (Hm)⁻¹) := by
            dsimp [F0]
            ring
          have hstep2 : c0 ^ 2 * (H2 ^ (-2 * x + 2 * eps) * (H 1) ^ (n + 1 - k) * (H 2) ^ (n + 2 - k) *
                (∏ i ∈ Finset.Icc 3 k, H i) * (Hm)⁻¹)
              = c0 ^ 2 * ((H2 ^ (-2 * x + 2 * eps) * (H 1) ^ 0 * (H 2) ^ 1 *
                  (∏ i ∈ Finset.Icc 3 (n + 1), H i)) * (H 1)⁻¹) := by
            congr 1
            rw [hk1, hk2C, hHm1']
            rw [hkeq]
          have hPcomb : H2 ^ (-2 * x + 2 * eps) * (H 1) ^ 0 * (H 2) ^ 1 *
                  (∏ i ∈ Finset.Icc 3 (n + 1), H i) = H2 ^ (-x + 2 * eps) := by
            calc
              H2 ^ (-2 * x + 2 * eps) * (H 1) ^ 0 * (H 2) ^ 1 * (∏ i ∈ Finset.Icc 3 (n + 1), H i)
                  = H2 ^ (-2 * x + 2 * eps) * 1 * (H 2) ^ 1 * (∏ i ∈ Finset.Icc 3 (n + 1), H i) := by
                    rw [pow_zero]
              _ = H2 ^ (-2 * x + 2 * eps) * (H 2) ^ 1 * (∏ i ∈ Finset.Icc 3 (n + 1), H i) := by ring
              _ = H2 ^ (-2 * x + 2 * eps) * H2 * (∏ i ∈ Finset.Icc 3 (n + 1), H i) := by rw [pow_one]
              _ = H2 ^ (-2 * x + 2 * eps) * (H2 * (∏ i ∈ Finset.Icc 3 (n + 1), H i)) := by rw [← mul_assoc]
              _ = H2 ^ (-2 * x + 2 * eps) * H2 ^ x := by rw [hH2P]
              _ = H2 ^ ((-2 * x + 2 * eps) + x) := by rw [← Real.rpow_add hH2pos]
              _ = H2 ^ (-x + 2 * eps) := by congr 1; ring
          have hstep3 : c0 ^ 2 * ((H2 ^ (-2 * x + 2 * eps) * (H 1) ^ 0 * (H 2) ^ 1 *
                  (∏ i ∈ Finset.Icc 3 (n + 1), H i)) * (H 1)⁻¹)
              = c0 ^ 2 * (H 1)⁻¹ * H2 ^ (-x + 2 * eps) := by
            rw [hPcomb]
            ring
          exact hstep1.trans (hstep2.trans hstep3)

        have hcollC : ‖(ξ : ℂ) - α‖ ≤ cb * c0 ^ 2 * (H 1)⁻¹ * H2 ^ (-x + 2 * eps) := by
          calc
            ‖(ξ : ℂ) - α‖ ≤ cb * F0 := hdistF
            _ = cb * (c0 ^ 2 * (H 1)⁻¹ * H2 ^ (-x + 2 * eps)) := by rw [hF0eqC]
            _ = cb * c0 ^ 2 * (H 1)⁻¹ * H2 ^ (-x + 2 * eps) := by
              rw [← mul_assoc, ← mul_assoc]
        have heposC : 0 < x - 2 * eps := by
          have hn2C : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
          have hx2C : 2 ≤ x := by linarith
          nlinarith
        have hHgtge1pos : 0 < Hgt α := lt_of_lt_of_le zero_lt_one hHgtge1
        have hgtnonneg : 0 ≤ (Hgt α) ^ (-x - 1 + 2 * eps) := by positivity
        have hA1C : (H 1)⁻¹ ≤ cb * (Hgt α)⁻¹ := by
          have hp := pow_neg_base_transfer (H := H 1) (B := Hgt α) (c := cb) (e := 1)
            hH1pos hHgtge1pos hcb1 (by norm_num) hHgtc1
          simpa [Real.rpow_neg_one] using hp
        have hA2C : H2 ^ (-x + 2 * eps) ≤ cb ^ (x - 2 * eps) * (Hgt α) ^ (-(x - 2 * eps)) := by
          have hp := pow_neg_base_transfer (H := H2) (B := Hgt α) (c := cb) (e := x - 2 * eps)
            hH2pos hHgtge1pos hcb1 heposC hHgtc2
          have hExpEqC : -x + 2 * eps = -(x - 2 * eps) := by ring
          rw [hExpEqC]
          exact hp
        let e : ℝ := x - 2 * eps
        have hcbcombE : cb * cb ^ e = cb ^ (e + 1) := by
          calc
            cb * cb ^ e = cb ^ 1 * cb ^ e := by rw [Real.rpow_one cb]
            _ = cb ^ (1 + e) := (Real.rpow_add hcbposC (1 : ℝ) e).symm
            _ = cb ^ (e + 1) := by congr 1; ring
        have hgtcombE : (Hgt α) ^ (-1 : ℝ) * (Hgt α) ^ (-e) = (Hgt α) ^ (-(e + 1)) := by
          rw [← Real.rpow_add hHgtge1pos]
          congr 1
          ring
        have hEqR : cb * c0 ^ 2 * ((cb * (Hgt α) ^ (-1 : ℝ)) * (cb ^ e * (Hgt α) ^ (-e)))
            = cb * c0 ^ 2 * cb ^ (e + 1) * (Hgt α) ^ (-(e + 1)) := by
          rw [show cb * c0 ^ 2 * ((cb * (Hgt α) ^ (-1 : ℝ)) * (cb ^ e * (Hgt α) ^ (-e)))
                = cb * c0 ^ 2 * (cb * cb ^ e) * ((Hgt α) ^ (-1 : ℝ) * (Hgt α) ^ (-e)) by ring]
          rw [hcbcombE, hgtcombE]
        have hmidC : cb * c0 ^ 2 * (H 1)⁻¹ * H2 ^ (-x + 2 * eps)
            ≤ cb * c0 ^ 2 * cb ^ (e + 1) * (Hgt α) ^ (-(e + 1)) := by
          have h00 : 0 ≤ cb * c0 ^ 2 := by positivity
          calc
            cb * c0 ^ 2 * (H 1)⁻¹ * H2 ^ (-x + 2 * eps)
                = cb * c0 ^ 2 * ((H 1)⁻¹ * H2 ^ (-x + 2 * eps)) := by ring
            _ ≤ cb * c0 ^ 2 * ((cb * (Hgt α)⁻¹) * H2 ^ (-x + 2 * eps)) := by
              apply mul_le_mul_of_nonneg_left _ h00
              exact mul_le_mul_of_nonneg_right hA1C
                (Real.rpow_nonneg (le_of_lt hH2pos) _)
            _ ≤ cb * c0 ^ 2 * ((cb * (Hgt α)⁻¹) * (cb ^ e * (Hgt α) ^ (-e))) := by
              apply mul_le_mul_of_nonneg_left _ h00
              exact mul_le_mul_of_nonneg_left hA2C (by positivity : 0 ≤ cb * (Hgt α)⁻¹)
            _ = cb * c0 ^ 2 * cb ^ (e + 1) * (Hgt α) ^ (-(e + 1)) := by
              have hg : (Hgt α)⁻¹ = (Hgt α) ^ (-1 : ℝ) := (Real.rpow_neg_one (Hgt α)).symm
              rw [hg]
              exact hEqR
        have hAvalC : A = x := by
          dsimp [A]
          rw [hkeq]
          exact A_at_top n x a hasum
        have hΛx : Λ ≤ x := by
          rw [hΛA, hAvalC]
          rw [div_le_iff₀ hakpos]
          have hx0 : 0 ≤ x := by linarith
          calc
            x ≤ x * 1 := by simp
            _ ≤ x * a k := mul_le_mul_of_nonneg_left hak1 hx0
        have hegate1 : T ≤ e + 1 := by
          dsimp [T, e]
          nlinarith
        have hegate2 : e + 1 ≤ 2 * X + 1 := by
          dsimp [e]
          nlinarith [hX0]
        have hfinC : ‖(ξ : ℂ) - α‖ ≤
            cb * c0 ^ 2 * cb ^ (2 * X + 1) * (Hgt α) ^ (-T) := by
          have hpowb : cb ^ (e + 1) ≤ cb ^ (2 * X + 1) :=
            Real.rpow_le_rpow_of_exponent_le hcb1 hegate2
          have hgate : (Hgt α) ^ (-(e + 1)) ≤ (Hgt α) ^ (-T) := by
            apply rpow_mono_exp hHgtge1
            linarith
          calc
            ‖(ξ : ℂ) - α‖ ≤ cb * c0 ^ 2 * (H 1)⁻¹ * H2 ^ (-x + 2 * eps) := hcollC
            _ ≤ cb * c0 ^ 2 * cb ^ (e + 1) * (Hgt α) ^ (-(e + 1)) := hmidC
            _ ≤ cb * c0 ^ 2 * cb ^ (2 * X + 1) * (Hgt α) ^ (-(e + 1)) := by
              have hm1 : cb * c0 ^ 2 * cb ^ (e + 1) ≤ cb * c0 ^ 2 * cb ^ (2 * X + 1) :=
                mul_le_mul_of_nonneg_left hpowb (by positivity : 0 ≤ cb * c0 ^ 2)
              exact mul_le_mul_of_nonneg_right hm1 (by positivity : 0 ≤ (Hgt α) ^ (-(e + 1)))
            _ ≤ cb * c0 ^ 2 * cb ^ (2 * X + 1) * (Hgt α) ^ (-T) := by
              exact mul_le_mul_of_nonneg_left hgate (by positivity : 0 ≤ cb * c0 ^ 2 * cb ^ (2 * X + 1))
        simpa [PBound, Cb, cb] using hfinC

    · -- case: m ≥ 2
      have hmu1 : 1 ≤ m.val := by omega
      have hmem_u : m.val + 1 ∈ Finset.Icc 2 (n + 1) := by
        rw [Finset.mem_Icc]
        omega
      have hamu1 : 1 ≤ a (m.val + 1) := ha1 (m.val + 1) hmem_u
      have hamu_pos : 0 < a (m.val + 1) := lt_of_lt_of_le zero_lt_one hamu1
      have hHm_eq : H2 ^ a (m.val + 1) = Hm := by
        have := hHi_a (m.val + 1) hmem_u
        simpa [Hm] using this
      have haukle : a (m.val + 1) ≤ a k := by
        apply a_le_of_chain (n := n) (u := m.val + 1) (v := k)
        · omega
        · exact hkn
        · omega
        · exact hachain
      have hAaLam : Λ ≤ A / a (m.val + 1) := by
        rw [hΛA]
        rw [div_le_div_iff₀ hakpos hamu_pos]
        exact mul_le_mul_of_nonneg_left haukle hAge0
      have hslack : 0 ≤ 2 * eps - 2 * eps / a (m.val + 1) := by
        have hdiv : 2 * eps / a (m.val + 1) ≤ 2 * eps :=
          (div_le_iff₀ hamu_pos).mpr (by nlinarith)
        linarith
      let E : ℝ := A / a (m.val + 1) + 1 - 2 * eps / a (m.val + 1)
      have hET : T ≤ E := by
        dsimp [T, E]
        nlinarith [hAaLam, hslack]
      let S3 : ℝ := ∑ i ∈ Finset.Icc 3 k, a i
      have hS2eq : (∑ i ∈ Finset.Icc 2 k, a i) = 1 + S3 := by
        dsimp [S3]
        have hsplit := sum_Icc_split_add 2 2 k (by omega) hk2 a
        calc
          (∑ i ∈ Finset.Icc 2 k, a i) = (∑ i ∈ Finset.Icc 2 2, a i) + (∑ i ∈ Finset.Icc 3 k, a i) := hsplit
          _ = 1 + (∑ i ∈ Finset.Icc 3 k, a i) := by simp [ha2]
      have hprod3 : (∏ i ∈ Finset.Icc 3 k, H i) = H2 ^ S3 := by
        dsimp [S3]
        calc
          (∏ i ∈ Finset.Icc 3 k, H i) = (∏ i ∈ Finset.Icc 3 k, H2 ^ a i) := by
            apply Finset.prod_congr rfl
            intro i hi
            have hmem' : i ∈ Finset.Icc 2 (n + 1) := by
              rw [Finset.mem_Icc] at hi ⊢
              omega
            exact (hHi_a i hmem').symm
          _ = H2 ^ (∑ i ∈ Finset.Icc 3 k, a i) := rpow_sum hH2pos (Finset.Icc 3 k) a
      have hHm_inv : (Hm)⁻¹ = H2 ^ (-a (m.val + 1)) := by
        have hneg := Real.rpow_neg (le_of_lt hH2pos) (a (m.val + 1))
        rw [hHm_eq] at hneg
        exact hneg.symm
      have hH1pow : (H 1) ^ (n + 1 - k) ≤ (H 2) ^ (n + 1 - k) := by
        exact pow_le_pow_left₀ hH1ge0 hH1leH2 (n + 1 - k)
      have hPosRest : 0 ≤ H2 ^ (-2 * x + 2 * eps) * (H 2) ^ (n + 2 - k) *
            (∏ i ∈ Finset.Icc 3 k, H i) * (Hm)⁻¹ := by
        have h2a : 0 ≤ H2 ^ (-2 * x + 2 * eps) := Real.rpow_nonneg (le_of_lt hH2pos) _
        have h2b : 0 ≤ (H 2) ^ (n + 2 - k) := pow_nonneg (hHi_nonneg 2) _
        have h2c : 0 ≤ ∏ i ∈ Finset.Icc 3 k, H i := Finset.prod_nonneg (by intro i hi; exact hHi_nonneg i)
        have hab : 0 ≤ H2 ^ (-2 * x + 2 * eps) * (H 2) ^ (n + 2 - k) := mul_nonneg h2a h2b
        have habc : 0 ≤ H2 ^ (-2 * x + 2 * eps) * (H 2) ^ (n + 2 - k) * (∏ i ∈ Finset.Icc 3 k, H i) :=
          mul_nonneg hab h2c
        exact mul_nonneg habc (inv_nonneg.mpr hHm_pos.le)
      have hcast1 : ((n + 1 - k : ℕ) : ℝ) = (n : ℝ) + 1 - (k : ℝ) := by
        rw [Nat.cast_sub (by omega : k ≤ n + 1)]
        simp
      have hcast2 : ((n + 2 - k : ℕ) : ℝ) = (n : ℝ) + 2 - (k : ℝ) := by
        rw [Nat.cast_sub (by omega : k ≤ n + 2)]
        simp
      have hEeq : -2 * x + 2 * eps + ((n + 1 - k : ℕ) : ℝ) + ((n + 2 - k : ℕ) : ℝ) + S3 + (-a (m.val + 1))
          = -A - a (m.val + 1) + 2 * eps := by
        dsimp [A]
        rw [hS2eq, hcast1, hcast2]
        ring
      have hExpMul : -A - a (m.val + 1) + 2 * eps = a (m.val + 1) * (-E) := by
        dsimp [E]
        field_simp [ne_of_gt hamu_pos]
        ring
      have hF0le : F0 ≤ c0 ^ 2 * Hm ^ (-E) := by
        calc
          F0 = c0 ^ 2 * (H2 ^ (-2 * x + 2 * eps) * (H 1) ^ (n + 1 - k) * (H 2) ^ (n + 2 - k) *
                (∏ i ∈ Finset.Icc 3 k, H i) * (Hm)⁻¹) := by
            dsimp [F0]
            ring
          _ ≤ c0 ^ 2 * Hm ^ (-E) := by
            apply mul_le_mul_of_nonneg_left _ (by positivity : 0 ≤ c0 ^ 2)
            calc
              (H2 ^ (-2 * x + 2 * eps) * (H 1) ^ (n + 1 - k) * (H 2) ^ (n + 2 - k) *
                  (∏ i ∈ Finset.Icc 3 k, H i) * (Hm)⁻¹)
                  = (H 1) ^ (n + 1 - k) * (H2 ^ (-2 * x + 2 * eps) * (H 2) ^ (n + 2 - k) *
                      (∏ i ∈ Finset.Icc 3 k, H i) * (Hm)⁻¹) := by ring
              _ ≤ (H 2) ^ (n + 1 - k) * (H2 ^ (-2 * x + 2 * eps) * (H 2) ^ (n + 2 - k) *
                      (∏ i ∈ Finset.Icc 3 k, H i) * (Hm)⁻¹) := by
                exact mul_le_mul_of_nonneg_right hH1pow hPosRest
              _ = H2 ^ (-2 * x + 2 * eps) * (H 2) ^ (n + 1 - k) * (H 2) ^ (n + 2 - k) *
                  (∏ i ∈ Finset.Icc 3 k, H i) * (Hm)⁻¹ := by ring
              _ = H2 ^ (-2 * x + 2 * eps) * (H 2) ^ (n + 1 - k) * (H 2) ^ (n + 2 - k) *
                  H2 ^ S3 * H2 ^ (-a (m.val + 1)) := by
                rw [hprod3, hHm_inv]
              _ = H2 ^ (-2 * x + 2 * eps + ((n + 1 - k : ℕ) : ℝ) + ((n + 2 - k : ℕ) : ℝ) + S3 + (-a (m.val + 1))) := by
                rw [← Real.rpow_natCast (H 2) (n + 1 - k)]
                rw [← Real.rpow_natCast (H 2) (n + 2 - k)]
                rw [← Real.rpow_add hH2pos]
                rw [← Real.rpow_add hH2pos]
                rw [← Real.rpow_add hH2pos]
                rw [← Real.rpow_add hH2pos]
              _ = H2 ^ (-A - a (m.val + 1) + 2 * eps) := by rw [hEeq]
              _ = Hm ^ (-E) := by
                rw [hExpMul]
                rw [Real.rpow_mul (le_of_lt hH2pos) (a (m.val + 1)) (-E)]
                rw [hHm_eq]
      have hcb0 : 0 ≤ cb := le_trans zero_le_one hcb1
      have hcollA : ‖(ξ : ℂ) - α‖ ≤ cb * c0 ^ 2 * Hm ^ (-E) := by
        calc
          ‖(ξ : ℂ) - α‖ ≤ cb * F0 := hdistF
          _ ≤ cb * (c0 ^ 2 * Hm ^ (-E)) := by
            exact mul_le_mul_of_nonneg_left hF0le hcb0
          _ = cb * c0 ^ 2 * Hm ^ (-E) := by ring
      have hfin := rpow_chain_final (D := ‖(ξ : ℂ) - α‖) (cb := cb) (c0 := c0)
        (Hbase := Hm) (Hgt := Hgt α) (E := E) (T := T) (X := X) hcollA hcb1 hHm1 hHgtge1
        hTpos hET hHgt2 hT2X
      simpa [PBound, Cb, cb] using hfin
  · -- decay bound ‖ξ−α‖ ≤ P0Bound·supN P^{−(2−2ε)}
    have hγ : 2 - 2 * eps = -( - (2 - 2 * eps)) := by ring
    have hγ2 : (2 - 2 * eps) = -(2 - 2 * eps) + 2 * (2 - 2 * eps) := by ring
    have hgoal : ‖(ξ : ℂ) - α‖ ≤ cb * c0 ^ 2 * H2 ^ (-2 + 2 * eps) := by
      by_cases hm0 : m.val = 0
      · by_cases hklt : k ≤ n
        · -- decay: m = 1, k ≤ n
          have hHm1' : Hm = H 1 := by
            dsimp [Hm]
            simp [hm0]
          let S3 : ℝ := ∑ i ∈ Finset.Icc 3 k, a i
          have hS2eq : (∑ i ∈ Finset.Icc 2 k, a i) = 1 + S3 := by
            dsimp [S3]
            have hsplit := sum_Icc_split_add 2 2 k (by omega) hk2 a
            calc
              (∑ i ∈ Finset.Icc 2 k, a i) = (∑ i ∈ Finset.Icc 2 2, a i) + (∑ i ∈ Finset.Icc 3 k, a i) := hsplit
              _ = 1 + (∑ i ∈ Finset.Icc 3 k, a i) := by simp [ha2]
          have hprod3 : (∏ i ∈ Finset.Icc 3 k, H i) = H2 ^ S3 := by
            dsimp [S3]
            calc
              (∏ i ∈ Finset.Icc 3 k, H i) = (∏ i ∈ Finset.Icc 3 k, H2 ^ a i) := by
                apply Finset.prod_congr rfl
                intro i hi
                have hmem' : i ∈ Finset.Icc 2 (n + 1) := by
                  rw [Finset.mem_Icc] at hi ⊢
                  omega
                exact (hHi_a i hmem').symm
              _ = H2 ^ (∑ i ∈ Finset.Icc 3 k, a i) := rpow_sum hH2pos (Finset.Icc 3 k) a
          have hsplitn : n + 1 - k = (n - k) + 1 := by omega
          have hH1ne : H 1 ≠ 0 := ne_of_gt hH1pos
          have hH1split : (H 1) ^ (n + 1 - k) * (H 1)⁻¹ = (H 1) ^ (n - k) := by
            rw [hsplitn, pow_succ]
            field_simp [hH1ne]
          have hH1pow2 : (H 1) ^ (n - k) ≤ (H 2) ^ (n - k) := by
            exact pow_le_pow_left₀ hH1ge0 hH1leH2 (n - k)
          have hPosRestB : 0 ≤ H2 ^ (-2 * x + 2 * eps) * (H 2) ^ (n + 2 - k) *
                (∏ i ∈ Finset.Icc 3 k, H i) := by
            have h2a : 0 ≤ H2 ^ (-2 * x + 2 * eps) := Real.rpow_nonneg (le_of_lt hH2pos) _
            have h2b : 0 ≤ (H 2) ^ (n + 2 - k) := pow_nonneg (hHi_nonneg 2) _
            have h2c : 0 ≤ ∏ i ∈ Finset.Icc 3 k, H i := Finset.prod_nonneg (by intro i hi; exact hHi_nonneg i)
            have hab : 0 ≤ H2 ^ (-2 * x + 2 * eps) * (H 2) ^ (n + 2 - k) := mul_nonneg h2a h2b
            exact mul_nonneg hab h2c
          have hcastB1 : ((n - k : ℕ) : ℝ) = (n : ℝ) - (k : ℝ) := by
            rw [Nat.cast_sub (by omega : k ≤ n)]
          have hcastB2 : ((n + 2 - k : ℕ) : ℝ) = (n : ℝ) + 2 - (k : ℝ) := by
            rw [Nat.cast_sub (by omega : k ≤ n + 2)]
            simp
          have hEeqB : -2 * x + 2 * eps + ((n - k : ℕ) : ℝ) + ((n + 2 - k : ℕ) : ℝ) + S3
              = -A - 1 + 2 * eps := by
            dsimp [A]
            rw [hS2eq, hcastB1, hcastB2]
            ring
          have hF0leB2 : F0 ≤ c0 ^ 2 * H2 ^ (-A - 1 + 2 * eps) := by
            calc
              F0 = c0 ^ 2 * (H2 ^ (-2 * x + 2 * eps) * (H 1) ^ (n + 1 - k) * (H 2) ^ (n + 2 - k) *
                    (∏ i ∈ Finset.Icc 3 k, H i) * (Hm)⁻¹) := by
                dsimp [F0]
                ring
              _ ≤ c0 ^ 2 * H2 ^ (-A - 1 + 2 * eps) := by
                apply mul_le_mul_of_nonneg_left _ (by positivity : 0 ≤ c0 ^ 2)
                calc
                  (H2 ^ (-2 * x + 2 * eps) * (H 1) ^ (n + 1 - k) * (H 2) ^ (n + 2 - k) *
                      (∏ i ∈ Finset.Icc 3 k, H i) * (Hm)⁻¹)
                      = (H 1) ^ (n + 1 - k) * (H 1)⁻¹ * (H2 ^ (-2 * x + 2 * eps) * (H 2) ^ (n + 2 - k) *
                          (∏ i ∈ Finset.Icc 3 k, H i)) := by
                        rw [hHm1']
                        ring
                  _ = (H 1) ^ (n - k) * (H2 ^ (-2 * x + 2 * eps) * (H 2) ^ (n + 2 - k) *
                          (∏ i ∈ Finset.Icc 3 k, H i)) := by
                        rw [hH1split]
                  _ ≤ (H 2) ^ (n - k) * (H2 ^ (-2 * x + 2 * eps) * (H 2) ^ (n + 2 - k) *
                          (∏ i ∈ Finset.Icc 3 k, H i)) := by
                        exact mul_le_mul_of_nonneg_right hH1pow2 hPosRestB
                  _ = H2 ^ (-2 * x + 2 * eps) * (H 2) ^ (n - k) * (H 2) ^ (n + 2 - k) *
                          (∏ i ∈ Finset.Icc 3 k, H i) := by ring
                  _ = H2 ^ (-2 * x + 2 * eps) * (H 2) ^ (n - k) * (H 2) ^ (n + 2 - k) * H2 ^ S3 := by
                        rw [hprod3]
                  _ = H2 ^ (-2 * x + 2 * eps + ((n - k : ℕ) : ℝ) + ((n + 2 - k : ℕ) : ℝ) + S3) := by
                        rw [← Real.rpow_natCast (H 2) (n - k)]
                        rw [← Real.rpow_natCast (H 2) (n + 2 - k)]
                        rw [← Real.rpow_add hH2pos]
                        rw [← Real.rpow_add hH2pos]
                        rw [← Real.rpow_add hH2pos]
                  _ = H2 ^ (-A - 1 + 2 * eps) := by rw [hEeqB]
          have hcb0B2 : 0 ≤ cb := le_trans zero_le_one hcb1
          calc
            ‖(ξ : ℂ) - α‖ ≤ cb * F0 := hdistF
            _ ≤ cb * (c0 ^ 2 * H2 ^ (-A - 1 + 2 * eps)) := by
              exact mul_le_mul_of_nonneg_left hF0leB2 hcb0B2
            _ = cb * c0 ^ 2 * H2 ^ (-A - 1 + 2 * eps) := by ring
            _ ≤ cb * c0 ^ 2 * H2 ^ (-2 + 2 * eps) := by
              have hmon : H2 ^ (-A - 1 + 2 * eps) ≤ H2 ^ (-2 + 2 * eps) := by
                apply rpow_mono_exp hH2gt1.le
                nlinarith
              exact mul_le_mul_of_nonneg_left hmon (by positivity : 0 ≤ cb * c0 ^ 2)
        · -- decay: m = 1, k = n+1
          have hkeq : k = n + 1 := by omega
          have hHm1' : Hm = H 1 := by
            dsimp [Hm]
            simp [hm0]
          have hpeel : (∏ i ∈ Finset.Icc 2 (n + 1), H i) = H 2 * (∏ i ∈ Finset.Icc 3 (n + 1), H i) := by
            have hset : Finset.Icc 2 (n + 1) = insert 2 (Finset.Icc 3 (n + 1)) := by
              ext i
              simp
              omega
            rw [hset]
            exact Finset.prod_insert (by simp : 2 ∉ Finset.Icc 3 (n + 1))
          have hH2P : H2 * (∏ i ∈ Finset.Icc 3 (n + 1), H i) = H2 ^ x := by
            have hh := hprodH
            rw [hpeel] at hh
            simpa using hh
          have hk1 : n + 1 - k = 0 := by omega
          have hk2C : n + 2 - k = 1 := by omega
          have hF0eqC2 : F0 = c0 ^ 2 * (H 1)⁻¹ * H2 ^ (-x + 2 * eps) := by
            have hstep1 : F0 = c0 ^ 2 * (H2 ^ (-2 * x + 2 * eps) * (H 1) ^ (n + 1 - k) * (H 2) ^ (n + 2 - k) *
                  (∏ i ∈ Finset.Icc 3 k, H i) * (Hm)⁻¹) := by
              dsimp [F0]
              ring
            have hstep2 : c0 ^ 2 * (H2 ^ (-2 * x + 2 * eps) * (H 1) ^ (n + 1 - k) * (H 2) ^ (n + 2 - k) *
                  (∏ i ∈ Finset.Icc 3 k, H i) * (Hm)⁻¹)
                = c0 ^ 2 * ((H2 ^ (-2 * x + 2 * eps) * (H 1) ^ 0 * (H 2) ^ 1 *
                    (∏ i ∈ Finset.Icc 3 (n + 1), H i)) * (H 1)⁻¹) := by
              congr 1
              rw [hk1, hk2C, hHm1']
              rw [hkeq]
            have hPcomb : H2 ^ (-2 * x + 2 * eps) * (H 1) ^ 0 * (H 2) ^ 1 *
                    (∏ i ∈ Finset.Icc 3 (n + 1), H i) = H2 ^ (-x + 2 * eps) := by
              calc
                H2 ^ (-2 * x + 2 * eps) * (H 1) ^ 0 * (H 2) ^ 1 * (∏ i ∈ Finset.Icc 3 (n + 1), H i)
                    = H2 ^ (-2 * x + 2 * eps) * 1 * (H 2) ^ 1 * (∏ i ∈ Finset.Icc 3 (n + 1), H i) := by
                      rw [pow_zero]
                _ = H2 ^ (-2 * x + 2 * eps) * (H 2) ^ 1 * (∏ i ∈ Finset.Icc 3 (n + 1), H i) := by ring
                _ = H2 ^ (-2 * x + 2 * eps) * H2 * (∏ i ∈ Finset.Icc 3 (n + 1), H i) := by rw [pow_one]
                _ = H2 ^ (-2 * x + 2 * eps) * (H2 * (∏ i ∈ Finset.Icc 3 (n + 1), H i)) := by rw [← mul_assoc]
                _ = H2 ^ (-2 * x + 2 * eps) * H2 ^ x := by rw [hH2P]
                _ = H2 ^ ((-2 * x + 2 * eps) + x) := by rw [← Real.rpow_add hH2pos]
                _ = H2 ^ (-x + 2 * eps) := by congr 1; ring
            have hstep3 : c0 ^ 2 * ((H2 ^ (-2 * x + 2 * eps) * (H 1) ^ 0 * (H 2) ^ 1 *
                    (∏ i ∈ Finset.Icc 3 (n + 1), H i)) * (H 1)⁻¹)
                = c0 ^ 2 * (H 1)⁻¹ * H2 ^ (-x + 2 * eps) := by
              rw [hPcomb]
              ring
            exact hstep1.trans (hstep2.trans hstep3)
          have hcb0C2 : 0 ≤ cb := le_trans zero_le_one hcb1
          calc
            ‖(ξ : ℂ) - α‖ ≤ cb * F0 := hdistF
            _ = cb * (c0 ^ 2 * (H 1)⁻¹ * H2 ^ (-x + 2 * eps)) := by rw [hF0eqC2]
            _ = cb * c0 ^ 2 * (H 1)⁻¹ * H2 ^ (-x + 2 * eps) := by ring
            _ ≤ cb * c0 ^ 2 * H2 ^ (-x + 2 * eps) := by
              -- H1⁻¹ ≤ 1 since H1 ≥ 1
              have h1inv : (H 1)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hH1ge1
              have h00 : 0 ≤ cb * c0 ^ 2 := by positivity
              have h2p : 0 ≤ H2 ^ (-x + 2 * eps) := Real.rpow_nonneg (le_of_lt hH2pos) _
              calc
                cb * c0 ^ 2 * (H 1)⁻¹ * H2 ^ (-x + 2 * eps)
                    = (cb * c0 ^ 2 * (H 1)⁻¹) * H2 ^ (-x + 2 * eps) := by ring
                _ ≤ (cb * c0 ^ 2 * 1) * H2 ^ (-x + 2 * eps) := by
                  have hm : cb * c0 ^ 2 * (H 1)⁻¹ ≤ cb * c0 ^ 2 * 1 :=
                    mul_le_mul_of_nonneg_left h1inv h00
                  exact mul_le_mul_of_nonneg_right hm h2p
                _ = cb * c0 ^ 2 * H2 ^ (-x + 2 * eps) := by ring
            _ ≤ cb * c0 ^ 2 * H2 ^ (-2 + 2 * eps) := by
              have hmon : H2 ^ (-x + 2 * eps) ≤ H2 ^ (-2 + 2 * eps) := by
                apply rpow_mono_exp hH2gt1.le
                have hn2C : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
                have hx2C : 2 ≤ x := by linarith
                linarith
              exact mul_le_mul_of_nonneg_left hmon (by positivity : 0 ≤ cb * c0 ^ 2)
      · -- decay: m ≥ 2
        have hmu1 : 1 ≤ m.val := by omega
        have hmem_u : m.val + 1 ∈ Finset.Icc 2 (n + 1) := by
          rw [Finset.mem_Icc]
          omega
        have hamu1 : 1 ≤ a (m.val + 1) := ha1 (m.val + 1) hmem_u
        have hamu_pos : 0 < a (m.val + 1) := lt_of_lt_of_le zero_lt_one hamu1
        have hHm_eq : H2 ^ a (m.val + 1) = Hm := by
          have := hHi_a (m.val + 1) hmem_u
          simpa [Hm] using this
        let S3 : ℝ := ∑ i ∈ Finset.Icc 3 k, a i
        have hS2eq : (∑ i ∈ Finset.Icc 2 k, a i) = 1 + S3 := by
          dsimp [S3]
          have hsplit := sum_Icc_split_add 2 2 k (by omega) hk2 a
          calc
            (∑ i ∈ Finset.Icc 2 k, a i) = (∑ i ∈ Finset.Icc 2 2, a i) + (∑ i ∈ Finset.Icc 3 k, a i) := hsplit
            _ = 1 + (∑ i ∈ Finset.Icc 3 k, a i) := by simp [ha2]
        have hprod3 : (∏ i ∈ Finset.Icc 3 k, H i) = H2 ^ S3 := by
          dsimp [S3]
          calc
            (∏ i ∈ Finset.Icc 3 k, H i) = (∏ i ∈ Finset.Icc 3 k, H2 ^ a i) := by
              apply Finset.prod_congr rfl
              intro i hi
              have hmem' : i ∈ Finset.Icc 2 (n + 1) := by
                rw [Finset.mem_Icc] at hi ⊢
                omega
              exact (hHi_a i hmem').symm
            _ = H2 ^ (∑ i ∈ Finset.Icc 3 k, a i) := rpow_sum hH2pos (Finset.Icc 3 k) a
        have hHm_inv : (Hm)⁻¹ = H2 ^ (-a (m.val + 1)) := by
          have hneg := Real.rpow_neg (le_of_lt hH2pos) (a (m.val + 1))
          rw [hHm_eq] at hneg
          exact hneg.symm
        have hH1pow : (H 1) ^ (n + 1 - k) ≤ (H 2) ^ (n + 1 - k) := by
          exact pow_le_pow_left₀ hH1ge0 hH1leH2 (n + 1 - k)
        have hPosRestA : 0 ≤ H2 ^ (-2 * x + 2 * eps) * (H 2) ^ (n + 2 - k) *
              (∏ i ∈ Finset.Icc 3 k, H i) := by
          have h2a : 0 ≤ H2 ^ (-2 * x + 2 * eps) := Real.rpow_nonneg (le_of_lt hH2pos) _
          have h2b : 0 ≤ (H 2) ^ (n + 2 - k) := pow_nonneg (hHi_nonneg 2) _
          have h2c : 0 ≤ ∏ i ∈ Finset.Icc 3 k, H i := Finset.prod_nonneg (by intro i hi; exact hHi_nonneg i)
          have hab : 0 ≤ H2 ^ (-2 * x + 2 * eps) * (H 2) ^ (n + 2 - k) := mul_nonneg h2a h2b
          exact mul_nonneg hab h2c
        have hcast1 : ((n + 1 - k : ℕ) : ℝ) = (n : ℝ) + 1 - (k : ℝ) := by
          rw [Nat.cast_sub (by omega : k ≤ n + 1)]
          simp
        have hcast2 : ((n + 2 - k : ℕ) : ℝ) = (n : ℝ) + 2 - (k : ℝ) := by
          rw [Nat.cast_sub (by omega : k ≤ n + 2)]
          simp
        have hEeqA2 : -2 * x + 2 * eps + ((n + 1 - k : ℕ) : ℝ) + ((n + 2 - k : ℕ) : ℝ) + S3
            + (-a (m.val + 1)) = -A - a (m.val + 1) + 2 * eps := by
          dsimp [A]
          rw [hS2eq, hcast1, hcast2]
          ring
        have hF0leA2 : F0 ≤ c0 ^ 2 * H2 ^ (-A - a (m.val + 1) + 2 * eps) := by
          calc
            F0 = c0 ^ 2 * (H2 ^ (-2 * x + 2 * eps) * (H 1) ^ (n + 1 - k) * (H 2) ^ (n + 2 - k) *
                  (∏ i ∈ Finset.Icc 3 k, H i) * (Hm)⁻¹) := by
              dsimp [F0]
              ring
            _ ≤ c0 ^ 2 * H2 ^ (-A - a (m.val + 1) + 2 * eps) := by
              apply mul_le_mul_of_nonneg_left _ (by positivity : 0 ≤ c0 ^ 2)
              calc
                (H2 ^ (-2 * x + 2 * eps) * (H 1) ^ (n + 1 - k) * (H 2) ^ (n + 2 - k) *
                    (∏ i ∈ Finset.Icc 3 k, H i) * (Hm)⁻¹)
                    = (H 1) ^ (n + 1 - k) * (H2 ^ (-2 * x + 2 * eps) * (H 2) ^ (n + 2 - k) *
                        (∏ i ∈ Finset.Icc 3 k, H i) * (Hm)⁻¹) := by ring
                _ ≤ (H 2) ^ (n + 1 - k) * (H2 ^ (-2 * x + 2 * eps) * (H 2) ^ (n + 2 - k) *
                        (∏ i ∈ Finset.Icc 3 k, H i) * (Hm)⁻¹) := by
                  exact mul_le_mul_of_nonneg_right hH1pow (by positivity : 0 ≤ H2 ^ (-2 * x + 2 * eps) * (H 2) ^ (n + 2 - k) * (∏ i ∈ Finset.Icc 3 k, H i) * (Hm)⁻¹)
                _ = H2 ^ (-2 * x + 2 * eps) * (H 2) ^ (n + 1 - k) * (H 2) ^ (n + 2 - k) *
                    (∏ i ∈ Finset.Icc 3 k, H i) * (Hm)⁻¹ := by ring
                _ = H2 ^ (-2 * x + 2 * eps) * (H 2) ^ (n + 1 - k) * (H 2) ^ (n + 2 - k) *
                    H2 ^ S3 * H2 ^ (-a (m.val + 1)) := by
                  rw [hprod3, hHm_inv]
                _ = H2 ^ (-2 * x + 2 * eps + ((n + 1 - k : ℕ) : ℝ) + ((n + 2 - k : ℕ) : ℝ) + S3 + (-a (m.val + 1))) := by
                  rw [← Real.rpow_natCast (H 2) (n + 1 - k)]
                  rw [← Real.rpow_natCast (H 2) (n + 2 - k)]
                  rw [← Real.rpow_add hH2pos]
                  rw [← Real.rpow_add hH2pos]
                  rw [← Real.rpow_add hH2pos]
                  rw [← Real.rpow_add hH2pos]
                _ = H2 ^ (-A - a (m.val + 1) + 2 * eps) := by rw [hEeqA2]
        have hcb0A2 : 0 ≤ cb := le_trans zero_le_one hcb1
        calc
          ‖(ξ : ℂ) - α‖ ≤ cb * F0 := hdistF
          _ ≤ cb * (c0 ^ 2 * H2 ^ (-A - a (m.val + 1) + 2 * eps)) := by
            exact mul_le_mul_of_nonneg_left hF0leA2 hcb0A2
          _ = cb * c0 ^ 2 * H2 ^ (-A - a (m.val + 1) + 2 * eps) := by ring
          _ ≤ cb * c0 ^ 2 * H2 ^ (-2 + 2 * eps) := by
            have hmon : H2 ^ (-A - a (m.val + 1) + 2 * eps) ≤ H2 ^ (-2 + 2 * eps) := by
              apply rpow_mono_exp hH2gt1.le
              nlinarith
            exact mul_le_mul_of_nonneg_left hmon (by positivity : 0 ≤ cb * c0 ^ 2)
    -- assemble: ‖ξ−α‖ ≤ P0Bound·supN P^{−(2−2ε)}
    have hExpEq0 : -2 + 2 * eps = -(2 - 2 * eps) := by ring
    simpa [P0Bound, Cb, cb, hExpEq0, hH2P] using hgoal

/-- Finite-ω_n(ξ) case of the small-ε statement: the paper's Sections 3–6
construction.  From `hfinite` (not every positive exponent workable) we get a
bounded set of workable exponents; `exists_omegaN` gives ωN ≥ n with every
positive exponent below ωN workable and none above workable.  Set
w2 := ωN + eps/2 (the eventual lower bound (B)), wbar := n − eps/4 (the
every-large-H solutions (A), by Dirichlet), e1 := ωN − eps/4 and
e2 := ωN − eps/2 = w2 − eps (both workable).  The Wirsing child turns e1-solutions
into irreducible polynomials P at exponent e2 with unbounded norms; the
Section 3–4 engine `weak_lemma41` turns each such P into the family Q with the
weak-4.1 properties; then the per-P conversion (Section 5 via
`poels_prop51_real` + the exponent algebra recorded in the roadmap) produces the
algebraic α with |ξ−α| ≤ C·(Hgt α)^{−Λ−1+2ε} and |ξ−α| → 0 along ‖P‖ → ∞;
the uniformity/h0 step outputs (x, a, α) per h0. -/
lemma poels_dio_finite_case (n : ℕ) (hn : 2 ≤ n) (ξ : ℝ) (hξ : Transcendental ℚ ξ)
    (hfinite : ¬ ∀ ω : ℝ, 0 < ω → omegaSol n ξ ω) :
    ∀ ε : ℝ, 0 < ε → ε < 1 / 2 → ∃ C : ℝ, 1 ≤ C ∧ GoodBody n ξ ε C := by
  intro eps hε0 hε1
  classical
  have hn2r : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hbd := SolSet_bddAbove_of_not_all hfinite
  rcases exists_omegaN n hn ξ hbd with ⟨ωN, hωNge, hωNle, hωNlt⟩
  let w2 : ℝ := ωN + eps / 2
  let wbar : ℝ := (n : ℝ) - eps / 4
  have hwbar0 : 0 < wbar := by dsimp [wbar]; nlinarith [hn2r, hε1]
  have hw2eps : eps < w2 := by dsimp [w2]; nlinarith [hn2r]
  have hε4 : 0 < eps / 4 := by positivity
  have hA : omegaSolBar n ξ wbar := by
    dsimp [wbar]
    exact dirichlet_omegaSolBar n ξ (eps / 4) hε4
  have hnotw2 : ¬ omegaSol n ξ w2 := by
    dsimp [w2]
    have hnp := omegaN_plus_not_sol (n := n) (ξ := ξ) (ωN := ωN) hωNle (half_pos hε0)
    simpa using hnp
  have hB := hB_of_not_sol (n := n) (ξ := ξ) (w2 := w2) hnotw2
  rcases weak_lemma41 n hn ξ hξ eps hε0 hε1 wbar hwbar0 w2 hw2eps hA hB with ⟨c0w, hc0wpos, hWLmain⟩
  let c0 : ℝ := max c0w 1
  have hc01 : 1 ≤ c0 := by dsimp [c0]; exact le_max_right c0w 1
  have hc0w_le_c0 : c0w ≤ c0 := by dsimp [c0]; exact le_max_left c0w 1
  let e1 : ℝ := ωN - eps / 4
  let e2 : ℝ := ωN - eps / 2
  have he1pos : 0 < e1 := by dsimp [e1]; nlinarith [hn2r, hε1]
  have he2lt : e2 < e1 := by dsimp [e1, e2]; linarith
  have he1ltN : e1 < ωN := by dsimp [e1]; linarith
  have hωNlt_e1 : omegaSol n ξ e1 := hωNlt e1 he1pos he1ltN
  have hsol_e1 : ∀ H : ℝ, 0 < H → ∃ P : Polynomial ℤ, P ≠ 0 ∧ P.natDegree ≤ n ∧
      H ≤ supN P ∧ ‖Polynomial.eval ξ (P.map (Int.castRingHom ℝ))‖ ≤ supN P ^ (-e1) := by
    intro H hH
    exact exists_largeNorm_sol (e := e1) (he := he1pos) hξ hωNlt_e1 H hH
  have hwirs : ∀ H : ℝ, 0 < H → ∃ P : Polynomial ℤ, P ≠ 0 ∧ Irreducible P ∧ P.natDegree ≤ n ∧
      H ≤ supN P ∧ ‖Polynomial.eval ξ (P.map (Int.castRingHom ℝ))‖ ≤ supN P ^ (-e2) := by
    intro H hH
    exact wirsing_irreducible_solutions n hn ξ hξ e1 he1pos hsol_e1 e2 he2lt H hH
  have he2w : e2 = w2 - eps := by dsimp [e2, w2]; ring
  let Pfun : ℕ → Polynomial ℤ := fun j =>
    Classical.choose (hwirs (max (max c0w 2) (j + 2 : ℝ)) (by positivity : 0 < max (max c0w 2) (j + 2 : ℝ)))
  have hPfun : ∀ j : ℕ, Pfun j ≠ 0 ∧ Irreducible (Pfun j) ∧ (Pfun j).natDegree ≤ n ∧
      (max (max c0w 2) (j + 2 : ℝ)) ≤ supN (Pfun j) ∧
      ‖Polynomial.eval ξ ((Pfun j).map (Int.castRingHom ℝ))‖ ≤ supN (Pfun j) ^ (-e2) := by
    intro j
    dsimp [Pfun]
    exact Classical.choose_spec (hwirs (max (max c0w 2) (j + 2 : ℝ)) (by positivity : 0 < max (max c0w 2) (j + 2 : ℝ)))
  have hPfun_ge_c0 : ∀ j : ℕ, c0 ≤ supN (Pfun j) := by
    intro j
    have hm : c0 ≤ max c0w 2 := by
      dsimp [c0]
      exact max_le_max le_rfl (by norm_num)
    have hm2 : c0 ≤ max (max c0w 2) (j + 2 : ℝ) := le_trans hm (le_max_left (max c0w 2) (j + 2 : ℝ))
    exact le_trans hm2 (hPfun j).2.2.2.1
  have hPfun_ge_2 : ∀ j : ℕ, 2 ≤ supN (Pfun j) := by
    intro j
    have hm : (2 : ℝ) ≤ max (max c0w 2) (j + 2 : ℝ) :=
      le_trans (le_max_right c0w 2) (le_max_left (max c0w 2) (j + 2 : ℝ))
    exact le_trans hm (hPfun j).2.2.2.1
  have hPfun_ge_j : ∀ j : ℕ, (j + 2 : ℝ) ≤ supN (Pfun j) := by
    intro j
    exact le_trans (le_max_right (max c0w 2) (j + 2 : ℝ)) (hPfun j).2.2.2.1
  have hPfun_ge_c0w : ∀ j : ℕ, c0w ≤ supN (Pfun j) := by
    intro j
    exact le_trans hc0w_le_c0 (hPfun_ge_c0 j)
  have hPfun_small : ∀ j : ℕ,
      ‖Polynomial.eval ξ ((Pfun j).map (Int.castRingHom ℝ))‖ ≤ supN (Pfun j) ^ (-(w2 - eps)) := by
    intro j
    rw [← he2w]
    exact (hPfun j).2.2.2.2
  let X : ℝ := w2 + eps
  have hX0 : 0 ≤ X := by dsimp [X]; nlinarith
  have hQdata : ∀ j : ℕ, ∃ Q : ℕ → Polynomial ℤ, ∃ x : ℝ,
      (n : ℝ) ≤ x ∧ x ≤ X ∧ Q 2 = Pfun j ∧
      (∀ i ∈ Finset.Icc 1 (n + 1), (Q i).natDegree ≤ n) ∧
      LinearIndependent ℝ (fun i : Fin (n + 1) => (Q (i.val + 1)).map (Int.castRingHom ℝ)) ∧
      IsCoprime ((Q 1).map (algebraMap ℤ ℚ)) ((Q 2).map (algebraMap ℤ ℚ)) ∧
      (∀ i ∈ Finset.Icc 1 n, supN (Q i) ≤ supN (Q (i + 1))) ∧
      (∀ i ∈ Finset.Icc 2 (n + 1), supN (Q 2) ≤ supN (Q i)) ∧
      (∏ i ∈ Finset.Icc 2 (n + 1), supN (Q i)) = supN (Q 2) ^ x ∧
      (∀ i ∈ Finset.Icc 1 (n + 1),
        ‖Polynomial.eval ξ ((Q i).map (Int.castRingHom ℝ))‖ ≤ c0 * supN (Q 2) ^ (-x + eps)) := by
    intro j
    rcases hWLmain (Pfun j) (hPfun j).1 (hPfun j).2.1 (hPfun j).2.2.1 (hPfun_small j) (hPfun_ge_c0w j) with
      ⟨Q, x, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩
    refine ⟨Q, x, h1, ?_, h3, h4, h5, h6, h7, h8, h9, ?_⟩
    · dsimp [X]
      exact h2
    · intro i hi
      have hb := h10 i hi
      have hle : c0w * supN (Q 2) ^ (-x + eps) ≤ c0 * supN (Q 2) ^ (-x + eps) := by
        exact mul_le_mul_of_nonneg_right hc0w_le_c0 (Real.rpow_nonneg (supN_nonneg (Q 2)) _)
      exact le_trans hb hle
  have hPdata : ∀ j : ℕ, ∃ x : ℝ, ∃ a : ℕ → ℝ, ∃ α : ℂ,
      (n : ℝ) ≤ x ∧
      (a 2 = 1 ∧ (∀ i ∈ Finset.Icc 2 n, a i ≤ a (i + 1)) ∧
        ((∑ i ∈ Finset.Icc 2 (n + 1), a i) = x) ∧
        (∀ i ∈ Finset.Icc 2 (n + 1), 1 ≤ a i)) ∧
      IsAlgebraic ℚ α ∧ Polynomial.natDegree (minpoly ℚ α) ≤ n ∧
      0 < ‖(ξ : ℂ) - α‖ ∧
      ‖(ξ : ℂ) - α‖ ≤ PBound n hn ξ c0 X * (Hgt α) ^ (-LamInline n x a - 1 + 2 * eps) ∧
      ‖(ξ : ℂ) - α‖ ≤ P0Bound n hn ξ c0 * supN (Pfun j) ^ (-(2 - 2 * eps)) := by
    intro j
    rcases hQdata j with ⟨Qj, xj, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩
    rcases perP_data n hn ξ hξ eps hε0 hε1 X hX0 c0 hc01 Qj xj (Pfun j) h3 h1 h2 h4 h5 h6 h7 h8 h9 h10
      (hPfun_ge_2 j) with ⟨a, α, hc⟩
    refine ⟨xj, a, α, h1, ⟨hc.1, ⟨hc.2.1, ⟨hc.2.2.1, hc.2.2.2.1⟩⟩⟩, hc.2.2.2.2.1, hc.2.2.2.2.2.1,
      hc.2.2.2.2.2.2.1, hc.2.2.2.2.2.2.2.1, hc.2.2.2.2.2.2.2.2⟩
  -- the concrete sequences (choice)
  let xf : ℕ → ℝ := fun j => Classical.choose (hPdata j)
  have xfspec : ∀ j : ℕ, ∃ a : ℕ → ℝ, ∃ α : ℂ,
      ((n : ℝ) ≤ xf j ∧
      (a 2 = 1 ∧ (∀ i ∈ Finset.Icc 2 n, a i ≤ a (i + 1)) ∧
        ((∑ i ∈ Finset.Icc 2 (n + 1), a i) = xf j) ∧
        (∀ i ∈ Finset.Icc 2 (n + 1), 1 ≤ a i)) ∧
      IsAlgebraic ℚ α ∧ Polynomial.natDegree (minpoly ℚ α) ≤ n ∧
      0 < ‖(ξ : ℂ) - α‖ ∧
      ‖(ξ : ℂ) - α‖ ≤ PBound n hn ξ c0 X * (Hgt α) ^ (-LamInline n (xf j) a - 1 + 2 * eps) ∧
      ‖(ξ : ℂ) - α‖ ≤ P0Bound n hn ξ c0 * supN (Pfun j) ^ (-(2 - 2 * eps))) := by
    intro j
    dsimp [xf]
    exact Classical.choose_spec (hPdata j)
  let af : ℕ → ℕ → ℝ := fun j => Classical.choose (xfspec j)
  have afspec : ∀ j : ℕ, ∃ α : ℂ,
      ((n : ℝ) ≤ xf j ∧
      (af j 2 = 1 ∧ (∀ i ∈ Finset.Icc 2 n, af j i ≤ af j (i + 1)) ∧
        ((∑ i ∈ Finset.Icc 2 (n + 1), af j i) = xf j) ∧
        (∀ i ∈ Finset.Icc 2 (n + 1), 1 ≤ af j i)) ∧
      IsAlgebraic ℚ α ∧ Polynomial.natDegree (minpoly ℚ α) ≤ n ∧
      0 < ‖(ξ : ℂ) - α‖ ∧
      ‖(ξ : ℂ) - α‖ ≤ PBound n hn ξ c0 X * (Hgt α) ^ (-LamInline n (xf j) (af j) - 1 + 2 * eps) ∧
      ‖(ξ : ℂ) - α‖ ≤ P0Bound n hn ξ c0 * supN (Pfun j) ^ (-(2 - 2 * eps))) := by
    intro j
    dsimp [af]
    exact Classical.choose_spec (xfspec j)
  let αf : ℕ → ℂ := fun j => Classical.choose (afspec j)
  have αfspec : ∀ j : ℕ,
      ((n : ℝ) ≤ xf j ∧
      (af j 2 = 1 ∧ (∀ i ∈ Finset.Icc 2 n, af j i ≤ af j (i + 1)) ∧
        ((∑ i ∈ Finset.Icc 2 (n + 1), af j i) = xf j) ∧
        (∀ i ∈ Finset.Icc 2 (n + 1), 1 ≤ af j i)) ∧
      IsAlgebraic ℚ (αf j) ∧ Polynomial.natDegree (minpoly ℚ (αf j)) ≤ n ∧
      0 < ‖(ξ : ℂ) - (αf j)‖ ∧
      ‖(ξ : ℂ) - (αf j)‖ ≤ PBound n hn ξ c0 X * (Hgt (αf j)) ^ (-LamInline n (xf j) (af j) - 1 + 2 * eps) ∧
      ‖(ξ : ℂ) - (αf j)‖ ≤ P0Bound n hn ξ c0 * supN (Pfun j) ^ (-(2 - 2 * eps))) := by
    intro j
    dsimp [αf]
    exact Classical.choose_spec (afspec j)
  have hα_alg : ∀ j : ℕ, IsAlgebraic ℚ (αf j) := fun j => (αfspec j).2.2.1
  have hα_deg : ∀ j : ℕ, Polynomial.natDegree (minpoly ℚ (αf j)) ≤ n := fun j => (αfspec j).2.2.2.1
  have hα_decay : ∀ j : ℕ,
      ‖(ξ : ℂ) - αf j‖ ≤ P0Bound n hn ξ c0 * supN (Pfun j) ^ (-(2 - 2 * eps)) := fun j =>
        (αfspec j).2.2.2.2.2.2
  -- unbounded heights of (αf j): direct argument (avoiding Tendsto machinery)
  have hunbounded : ∀ h0 : ℕ, ∃ j : ℕ, (h0 : ℝ) ≤ Hgt (αf j) := by
    intro h0
    by_cases hh0 : h0 = 0
    · refine ⟨0, ?_⟩
      have hge : 1 ≤ Hgt (αf 0) := height_ge_one (αf 0) (hα_alg 0)
      rw [hh0, Nat.cast_zero]
      exact le_trans (by norm_num : (0 : ℝ) ≤ 1) hge
    · have hh0pos : 0 < h0 := Nat.pos_of_ne_zero hh0
      by_contra hnot
      push_neg at hnot
      have hlt : ∀ j : ℕ, HgtNat (αf j) < h0 := by
        intro j
        have hle : ¬ (h0 : ℝ) ≤ (HgtNat (αf j) : ℝ) := by simpa [Hgt, HgtNat] using hnot j
        have h' : (HgtNat (αf j) : ℝ) < (h0 : ℝ) := lt_of_not_ge hle
        exact_mod_cast h'
      let F : Set ℂ := {γ : ℂ | IsAlgebraic ℚ γ ∧ Polynomial.natDegree (minpoly ℚ γ) ≤ n ∧ HgtNat γ ≤ h0}
      have hFin : F.Finite := by
        dsimp [F]
        exact finite_algebraic_bounded_deg_height n h0
      have hmemF : ∀ j : ℕ, αf j ∈ F := by
        intro j
        exact ⟨hα_alg j, hα_deg j, Nat.le_of_lt (hlt j)⟩
      have hξnotF : (ξ : ℂ) ∉ F := by
        intro hξF
        exact hξ ((isAlgebraic_complex_iff_real ξ).mp hξF.1)
      let s : Finset ℂ := hFin.toFinset
      have hs_all : ∀ γ ∈ F, γ ∈ s := by intro γ hγ; exact hFin.mem_toFinset.mpr hγ
      have hs_sub : ∀ γ ∈ s, γ ∈ F := by intro γ hγ; exact hFin.mem_toFinset.mp hγ
      have hne_s : s.Nonempty := ⟨αf 0, hs_all (αf 0) (hmemF 0)⟩
      let im : Finset ℝ := s.image (fun γ : ℂ => ‖(ξ : ℂ) - γ‖)
      have hne_im : im.Nonempty := by
        refine ⟨‖(ξ : ℂ) - αf 0‖, ?_⟩
        exact Finset.mem_image.mpr ⟨αf 0, hs_all (αf 0) (hmemF 0), rfl⟩
      let δ : ℝ := im.min' hne_im
      have hδmem : δ ∈ im := by
        dsimp [δ]
        exact Finset.min'_mem im hne_im
      have hδpos : 0 < δ := by
        rcases Finset.mem_image.mp hδmem with ⟨γ, hγs, hγeq⟩
        rw [← hγeq]
        rcases hs_sub γ hγs with ⟨hAlg, hDeg, hH⟩
        exact dist_pos_of_algebraic ξ hξ γ hAlg
      have hδle : ∀ γ ∈ s, δ ≤ ‖(ξ : ℂ) - γ‖ := by
        intro γ hγ
        have hl : δ ∈ lowerBounds (↑im) := (Finset.isLeast_min' im hne_im).2
        exact hl (Finset.mem_image.mpr ⟨γ, hγ, rfl⟩)
      have hP0ge1 : 1 ≤ P0Bound n hn ξ c0 := by
        have hCb1 : 1 ≤ Cb n hn ξ := by dsimp [Cb]; exact le_max_right _ _
        have hc0sq : 1 ≤ c0 ^ 2 := by exact one_le_pow₀ hc01
        dsimp [P0Bound]
        nlinarith
      have hP0pos : 0 < P0Bound n hn ξ c0 := lt_of_lt_of_le zero_lt_one hP0ge1
      have hγpos : 0 < 2 - 2 * eps := by nlinarith
      have hx0 : 0 ≤ P0Bound n hn ξ c0 / δ := le_of_lt (div_pos hP0pos hδpos)
      let M : ℝ := (P0Bound n hn ξ c0 / δ) ^ (1 / (2 - 2 * eps))
      have hMge0 : 0 ≤ M := by dsimp [M]; exact Real.rpow_nonneg hx0 _
      rcases exists_nat_gt M with ⟨J, hJ⟩
      have hMJ : M < (J : ℝ) + 2 := by
        have hJ' : M < (J : ℝ) := hJ
        nlinarith
      have hSgtM : M < supN (Pfun J) := lt_of_lt_of_le hMJ (hPfun_ge_j J)
      have hSpos : 0 < supN (Pfun J) := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 2) (hPfun_ge_2 J)
      have hMγ : M ^ (2 - 2 * eps) = P0Bound n hn ξ c0 / δ := by
        calc
          M ^ (2 - 2 * eps)
              = (P0Bound n hn ξ c0 / δ) ^ ((1 / (2 - 2 * eps)) * (2 - 2 * eps)) := by
                  dsimp [M]
                  exact (Real.rpow_mul hx0 (1 / (2 - 2 * eps)) (2 - 2 * eps)).symm
          _ = (P0Bound n hn ξ c0 / δ) ^ (1 : ℝ) := by
                  congr 1
                  rw [one_div, inv_mul_cancel₀ (ne_of_gt hγpos)]
          _ = P0Bound n hn ξ c0 / δ := Real.rpow_one _
      have hdecJ : P0Bound n hn ξ c0 * supN (Pfun J) ^ (-(2 - 2 * eps)) < δ := by
        have hpow := Real.rpow_lt_rpow hMge0 hSgtM hγpos
        have hmain1 : P0Bound n hn ξ c0 / δ < supN (Pfun J) ^ (2 - 2 * eps) := by
          rwa [hMγ] at hpow
        have hP0lt : P0Bound n hn ξ c0 < δ * supN (Pfun J) ^ (2 - 2 * eps) := by
          have hh := (div_lt_iff₀ hδpos).mp hmain1
          simpa [mul_comm] using hh
        have hSγpos : 0 < supN (Pfun J) ^ (2 - 2 * eps) := Real.rpow_pos_of_pos hSpos _
        have hdiv : P0Bound n hn ξ c0 / supN (Pfun J) ^ (2 - 2 * eps) < δ :=
          (div_lt_iff₀ hSγpos).mpr hP0lt
        calc
          P0Bound n hn ξ c0 * supN (Pfun J) ^ (-(2 - 2 * eps))
              = P0Bound n hn ξ c0 * (supN (Pfun J) ^ (2 - 2 * eps))⁻¹ := by
                  rw [Real.rpow_neg (le_of_lt hSpos) (2 - 2 * eps)]
          _ = P0Bound n hn ξ c0 / supN (Pfun J) ^ (2 - 2 * eps) := by rw [div_eq_mul_inv]
          _ < δ := hdiv
      have hdJ : ‖(ξ : ℂ) - αf J‖ < δ := lt_of_le_of_lt (hα_decay J) hdecJ
      have hmemJ : αf J ∈ s := hs_all (αf J) (hmemF J)
      have hδleJ : δ ≤ ‖(ξ : ℂ) - αf J‖ := hδle (αf J) hmemJ
      linarith
  -- choose the constant C
  refine ⟨PBound n hn ξ c0 X, ?hC, ?hGB⟩
  · have hCb1 : 1 ≤ Cb n hn ξ := by dsimp [Cb]; exact le_max_right _ _
    have hc0sq : 1 ≤ c0 ^ 2 := by exact one_le_pow₀ hc01
    have hCb0 : 0 ≤ Cb n hn ξ := le_trans zero_le_one hCb1
    have hprod0 : 0 ≤ Cb n hn ξ * c0 ^ 2 := mul_nonneg hCb0 (by positivity : 0 ≤ c0 ^ 2)
    have h1 : 1 ≤ Cb n hn ξ * c0 ^ 2 := by
      calc
        1 ≤ Cb n hn ξ := hCb1
        _ ≤ Cb n hn ξ * c0 ^ 2 := le_mul_of_one_le_right hCb0 hc0sq
    have hcbpow : 1 ≤ (Cb n hn ξ) ^ (2 * X + 1) := by
      have hle := Real.rpow_le_rpow_of_exponent_le hCb1 (by nlinarith : 0 ≤ 2 * X + 1)
      simpa using hle
    dsimp [PBound]
    calc
      1 ≤ Cb n hn ξ * c0 ^ 2 := h1
      _ ≤ Cb n hn ξ * c0 ^ 2 * (Cb n hn ξ) ^ (2 * X + 1) := le_mul_of_one_le_right hprod0 hcbpow
  · intro h0
    rcases hunbounded h0 with ⟨J, hJ⟩
    refine ⟨xf J, af J, αf J, (αfspec J).1, ⟨(αfspec J).2.1.1, ⟨(αfspec J).2.1.2.1,
      ⟨(αfspec J).2.1.2.2.1, (αfspec J).2.1.2.2.2⟩⟩⟩, (αfspec J).2.2.1, (αfspec J).2.2.2.1,
      (αfspec J).2.2.2.2.1, hJ, (αfspec J).2.2.2.2.2.1⟩

/-- The small-ε version of the statement (0 < ε < 1/2); the ONLY remaining `TODO`
is `poels_dio_finite_case`.  Case split: ω_n(ξ) = ∞ (every positive exponent
workable → all-ones pair via `poels_dio_infty_case`); else finite case via
`poels_dio_finite_case`. -/
lemma poels_dio_main_small (n : ℕ) (hn : 2 ≤ n) (ξ : ℝ) (hξ : Transcendental ℚ ξ) :
    ∀ ε : ℝ, 0 < ε → ε < 1 / 2 → ∃ C : ℝ, 1 ≤ C ∧ GoodBody n ξ ε C := by
  by_cases hinf : ∀ ω : ℝ, 0 < ω → omegaSol n ξ ω
  · exact poels_dio_infty_case n hn ξ hξ hinf
  · exact poels_dio_finite_case n hn ξ hξ hinf

theorem poels_dio_main (n : ℕ) (hn : 2 ≤ n) (ξ : ℝ) (hξ : Transcendental ℚ ξ) :
    ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 1 ≤ C ∧ ∀ h0 : ℕ,
      ∃ x : ℝ, ∃ a : ℕ → ℝ, ∃ α : ℂ,
        n ≤ x ∧
        (a 2 = 1 ∧
         (∀ i : ℕ, i ∈ Finset.Icc 2 n → a i ≤ a (i + 1)) ∧
         ((∑ i ∈ Finset.Icc 2 (n + 1), a i) = x) ∧
         (∀ i : ℕ, i ∈ Finset.Icc 2 (n + 1) → 1 ≤ a i)) ∧
        IsAlgebraic ℚ α ∧ Polynomial.natDegree (minpoly ℚ α) ≤ n ∧
        0 < ‖(ξ : ℂ) - α‖ ∧
        (h0 : ℝ) ≤ (((let p := minpoly ℚ α;
          let D := Multiset.lcm (Multiset.map (fun i ↦ (p.coeff i).den) p.support.val);
          Finset.sup p.support (fun i ↦ (D * p.coeff i).num.natAbs) : ℕ) : ℝ)) ∧
        ‖(ξ : ℂ) - α‖ ≤
          C * ((((let p := minpoly ℚ α;
            let D := Multiset.lcm (Multiset.map (fun i ↦ (p.coeff i).den) p.support.val);
            Finset.sup p.support (fun i ↦ (D * p.coeff i).num.natAbs) : ℕ) : ℝ)) ^
            (-(if h : (Finset.Icc 2 (n + 1)).Nonempty then
                 (Finset.Icc 2 (n + 1)).sup' h (fun k =>
                   (2 * x - 2 * (n - k + 1) - (∑ i ∈ Finset.Icc 2 k, a i)) / a k)
               else 0) - 1 + 2 * ε)) := by
  intro ε hε
  change ∃ C : ℝ, 1 ≤ C ∧ GoodBody n ξ ε C
  exact poels_dio_main_of_small n hn ξ hξ (poels_dio_main_small n hn ξ hξ) ε hε

end Commons.NumberTheory.DiophantineApproximation.BoundedDegree

/-! ## Detailed roadmap and STATUS

The statement is the content of Poëls, Annals of Math 201 (2025),
*On approximation to a real number by algebraic numbers of bounded degree*,
Sections 3–6 ("A step toward Wirsing's conjecture").  With
    A_k(x,a) := 2x − 2(n−k+1) − Σ_{2≤i≤k} a_i   and   Λ := max_{2≤k≤n+1} A_k/a_k
the conclusion asks: ∀ε>0 ∃C≥1 ∀h0 ∃x≥n, admissible a, algebraic α
(deg ≤ n, height ≥ h0, α ≠ ξ) with ‖ξ−α‖ ≤ C·H(α)^{−Λ−1+2ε}.

CURRENT STATE OF THE FILE (compiles cleanly; the two `TODO`s are the finite-ω_n
case `poels_dio_finite_case` and `poels_dio_main_small` itself, which is the
by_cases split of the ∞/finite cases):

VERIFIED CONTENT (no TODO), in this file:
 • Batch 1: `Lambda`, `rpow_mono_exp`, `A_at_top`, `A_lower` (A_k ≥ 1 under
   admissibility).
 • Batch 2 (interface): `Hgt`, `HgtNat`, `LamInline`, `GoodBody`, `sup'_independent`,
   `exists_mem_eq_sup'`, `Icc_nonempty_2_n1`, `Lambda_eq_sup'`, `LamInline_eq_Lambda`,
   `Lambda_mem`, `x_ge_n`, `exponent_slack_le`, `bound_transfer`,
   `rpow_exp_le_of_eps_le`, `isAlgebraic_complex_iff_real`,
   `algebraic_ne_transcendental`, `dist_pos_of_algebraic`, `poels_dio_main_of_small`
   (ε-reduction: 0 < ε < 1/2 suffices — poels_dio_main is fully proven from
   poels_dio_main_small).
 • Batch 3 (heights → weights): `log_div_mono`, `log_div_self`, `log_div_ge_one`,
   `log_prod_div_eq_sum_div`, `admissible_from_heights`.
 • Batch 4: `heights_unbounded_of_tendsto` (algebraic deg-≤n sequence → ξ ⇒ heights
   unbounded; uses commons finite_algebraic_bounded_deg_height).
 • Batch 5 (polynomial lattice): `intNorm` + norm basics, `eval_intNorm_le`,
   `gelfond_factor` (Mahler-measure proof).
 • Batch 6 (ω_n(ξ) sup-exponent infrastructure, NEW this session): `omegaSol`,
   `omegaSolBar`, `SolSet`, downward-closedness `omegaSol_of_le`, bar→sol,
   real-parameter Dirichlet `dirichlet_real`, `dirichlet_omegaSolBar` (exponent n−δ
   workable for every large H), `exists_largeNorm_sol` (workable exponent ⇒
   large-norm solutions |P(ξ)| ≤ ‖P‖^{−e}), `SolSet_mem_of_dirichlet`,
   `SolSet_nonempty`, `SolSet_bddAbove_of_not_all`, `exists_omegaN` (ωN = sSup S with
   (n) ≤ ωN, ∀ω workable ω ≤ ωN, every 0 < ω' < ωN workable), `omegaN_plus_not_sol`.
 • Batch 7 (ω_n(ξ) = ∞ case, NEW this session, fully proven): `Lambda_all_ones`
   (Λ(n, all-ones) = n), `goodbody_allones_approx`, `poels_dio_infty_case` — from
   `hWinfty : ∀ ω > 0, omegaSol n ξ ω` derive the GoodBody instance with C = 1,
   x = n, a ≡ 1, α from the commons `root_transfer_all_heights`.

COMMONS (importable) used: height_ge_one, minpoly_leading_coeff_eq_one,
sum_Icc_split_add, card_Icc_nat, root_close_deriv_bound,
finite_algebraic_bounded_deg_height, dirichlet poly_small_value,
finite_int_polys_bounded_supNorm, int_poly_supNorm_one_le,
int_poly_eval_ne_zero_of_transcendental, root_transfer_all_heights (PROVEN this
session, child L56), poly_det_facile, wirsing_irreducible_solutions,
poels_prop51 (NOTE: its coprimality hypothesis is ZZ[X]-Bezout — TOO STRONG for
us; see poels_prop51_real below), poels_opt_lower, p51_* helpers,
int_poly_factor_supNorm_le, exists_pos_small_eval_of_transcendental, ...

CHILDREN IN FLIGHT (dispatched this session):
 • weak_lemma41 (child L76): the Sections 3–4 engine, RE-DISPATCHED after L55
   correctly declared the first version FALSE.  FLAW FOUND AND FIXED: the output
   clause `IsCoprime (Q 1) (Q 2)` over ZZ[X] (Bezout) is NOT derivable — ZZ[X] is
   not Bezout and gcd-1 over QQ (all the source guarantees, via P irreducible over
   QQ and ‖Q_1‖ ≤ e^{-n}‖P‖ so P ∤ Q_1) does not imply a ZZ-Bezout identity.  The
   re-dispatched statement requires instead
   `IsCoprime ((Q 1).map (algebraMap ZZ QQ)) ((Q 2).map (algebraMap ZZ QQ))`
   (coprime over QQ[X]).  Everything else unchanged (output: Q-family with Q 2 = P,
   QQ-coprime Q 1, monotone sup-norms, product identity H_2⋯H_{n+1} = H_2^x with
   n ≤ x ≤ w2 + eps, |Q_i(ξ)| ≤ c·H_2^{−x+eps}; inputs: (A) = every-large-H
   solutions at exponent wbar, (B) = eventual lower bound at exponent w2; uniform
   in irreducible P with ‖P‖ ≥ c and |P(ξ)| ≤ ‖P‖^{−(w2−eps)}).
 • poels_prop51_real (child L77): Prop 5.1 re-issued with the coprimality
   hypothesis on the REAL maps, `IsCoprime ((P 0).map RR) ((P 1).map RR)` (the
   p51 machinery's deep helpers already take RR-IsCoprime; only the outer layer
   needs replaying).  Use THIS (not poels_prop51) in the finite-case assembly;
   QQ-coprime from weak_lemma41 maps to RR-coprime by mapping the QQ-Bezout
   identity to RR (Q.map QQ .map RR = Q.map RR).

REMAINING WORK to finish poels_dio_main_small (the finite-ω_n case =
Sections 3–6 assembly):
 1. In `poels_dio_finite_case` (TODO): from hfinite (∃ a positive exponent not
    workable): SolSet_bddAbove_of_not_all → exists_omegaN gives ωN ≥ n; set
    w2 := ωN + eps/2 ((B) via omegaN_plus_not_sol), wbar := n − eps/4 (hA via
    dirichlet_omegaSolBar), omega := w2 − eps = ωN − eps/2 and e1 := ωN − eps/4
    (both workable via the `< ωN` clause); exists_largeNorm_sol at e1 →
    wirsing_irreducible_solutions at e2 := omega gives irreducible P at exponent
    omega for every height; apply weak_lemma41 (hWL41 hypothesis; replace by the
    commons import once published) to each large P.
 2. Per-P conversion (the core assembly, to be written in-file once weak_lemma41
    lands): family Q, x ↦ admissible a_i = log H_i/log H_2 (admissible_from_heights;
    needs H 2 = ‖P‖ > 1 and H_i ≥ H_2 ≥ 1), x' = Σ a_i = x; k* = argmax of
    A_k/a_k (Lambda_mem); apply poels_prop51_real to the Fin k* subfamily
    (Q 1..Q k*) with δ := c0·H_2^{−x+eps}; convert to |ξ−α| ≤ C·(Hgt α)^{−Λ−1+2eps}
    with C built from c0, the prop51 constant (take ≥ 1), and c^E bounds
    (E = Λ+1−2ε ≤ 2x+1 bounded by x ≤ w2+eps), C uniform over the family; also
    the →0 bound |ξ−α| ≤ C'·H_2^{−(1−2ε)} (A_k(x,a) ≥ 1 via A_lower) for the
    height unboundedness step.

    EXPONENT ALGEBRA (checked by hand; the resolution for the Lean proof): with
    H_j = H_2^{a_j} (a_1 := log H_1/log H_2 ∈ [0,1], a_2 = 1, a_j ≥ 1 for j ≥ 2,
    Σ_{2..n+1} a_j = x), A := A_{k*}(x,a) = 2x − 2(n+1−k*) − Σ_{2..k*}a_j ≥ 1
    (A_lower), and Λ = A/a_{k*} (k* the argmax, Lambda_mem), prop51_real with
    δ = c0·H_2^{−x+eps} gives (c1 ≥ 1 the prop51 constant, absorbed)
      |ξ−α| ≤ c1·c0²·H_2^{−2x+2eps}·H_1^{n+1−k*}·H_2^{n+2−k*}·(Π_{3≤j≤k*}H_j)·H_m^{−1}.
    CASE m ≥ 2 (paper index ≥ 2, a_m ≥ 1): H_1^{n+1−k*} ≤ H_2^{n+1−k*}, the
    exponent of H_2 is −2x+2eps+(n+1−k*)+(n+2−k*)+Σ_{3..k*}a_j − a_m =
    −A − a_m + 2eps, so |ξ−α| ≤ c1c0²·H_m^{−(A/a_m+1−2eps/a_m)}; A/a_m ≥
    A/a_{k*} = Λ (a_m ≤ a_{k*}), H(α) ≤ c1·H_m, E := Λ+1−2eps ≥ 0: gives
    |ξ−α| ≤ c1c0²·c1^{E}·H(α)^{−E} with c1^{E} ≤ c1^{2x+1} uniform (x ≤ X).
    CASE m = 1 (paper index 1, H_m = H_1): |ξ−α| ≤ c1c0²·H_2^{−2x+2eps}·
      H_1^{n−k*}·H_2^{n+2−k*}·(Π_{3≤j≤k*}H_j).  If k* ≤ n bound H_1^{n−k*} ≤
      H_2^{n−k*}: exponent −A − 1 + 2eps; A ≥ Λ (a_{k*} ≥ 1) gives
      |ξ−α| ≤ c1c0²·c1^{A+1}·H(α)^{−Λ−1+2eps} via H_2 ≥ H(α)/c1.  If
      k* = n+1: A = x and the bound is |ξ−α| ≤ c1c0²·H_1^{−1}·H_2^{−x+2eps};
      DO NOT drop H_1^{−1}: use H_1 ≥ H(α)/c1 and H_2 ≥ H(α)/c1 to get
      |ξ−α| ≤ c1c0²·c1^{x−2eps+1}·H(α)^{−x−1+2eps} ≤ c1c0²·c1^{x+1}·H(α)^{−Λ−1+2eps}
      (Λ = x/a_{n+1} ≤ x, so −x−1+2eps ≤ −Λ−1+2eps).  All constants ≤
      c1·c0²·c1^{2X+1} with X a bound on x (X := w2 + eps): UNIFORM over the
      family in every case.
    →0 BOUND (for the height-unboundedness step): m ≥ 2: −A−a_m+2eps ≤
      −2+2eps < 0; m = 1: −A−1+2eps ≤ −2+2eps (k* ≤ n) and −x−a_1+2eps ≤
      −n+2eps (k* = n+1), so always |ξ−α| ≤ C0·H_2^{−(2−2eps)} with
      C0 := c1c0²·max(1, H_1-based factors ≤ 1)-style; since H_2 = ‖P‖ → ∞
      along the family, |ξ−α| → 0.
 3. Uniformity/h0 step: pick a sequence P_j of irreducible members with
    ‖P_j‖ → ∞ (exists since the Wirsing family is unbounded); per j produce α_j;
    |ξ−α_j| → 0 ⇒ heights unbounded (heights_unbounded_of_tendsto); given h0 pick
    j with h0 ≤ Hgt(α_j) and output (x_j, a_j, α_j) — the per-P bound holds with
    the SAME C because x_j ≤ w2 + eps is uniform (ωN fixed) and all per-P
    constants are uniform.
 4. Assemble poels_dio_main_small := by_cases on hinf : ∀ω>0, omegaSol:
    ∞ branch: poels_dio_infty_case n hn ξ hξ hinf; finite branch:
    poels_dio_finite_case n hn ξ hξ hinf weak_lemma41 (import from commons).

SESSION 5 STATUS (most recent work; supersedes the older paragraph above):
The file now contains a complete *interface and scaffolding* for the finite-ω_n case:
 • Batch 9/9b/10 infrastructure (all full proofs, no TODO): `omegaN_plus_not_sol`,
   `hB_of_not_sol`, `qcop_map_real` (ℚ[X]-IsCoprime ⇒ ℝ[X]-IsCoprime),
   `monotone_fin_of_chain`, `fin_linIndep_sub`, `linearIndependent_apply_ne_zero`,
   `qi_ne_zero_of_li`, `prod_fin_filter_Icc`, `rpow_sum`, `rpow_sq`,
   `pow_neg_base_transfer` (H^{-e} ≤ c^e·B^{-e} from B ≤ c·H), `a_le_of_chain`,
   `rpow_chain_final` (all-left-assoc final transfer: D ≤ cb·c0²·Hbase^{−E}, T ≤ E,
   Hgt ≤ cb·Hbase ⇒ D ≤ cb·c0²·cb^{2X+1}·Hgt^{−T}).
 • Constants `Cb`/`PBound`/`P0Bound` (= cb·c0²·cb^{2X+1} / cb·c0² with
   cb = max (Prop51 c) 1).
 • The per-P conversion lemma `perP_data` (statement EXACTLY as needed by
   `poels_dio_finite_case`) whose body is FULLY proved EXCEPT three remaining
   `TODO`s: the m=1 & k=n+1 sub-branch of the main bound (branch C, line ~1813),
   the decay bound ‖ξ−α‖ ≤ P0Bound·supN P^{−(2−2ε)} (hbd2, line ~1936), and the
   `poels_dio_finite_case` assembly itself (line ~1954).  In `perP_data`, the
   setup through `hdistF` (D ≤ cb·F0, F0 the collapsed Prop-5.1 bound), the
   admissible log-weights, `hHi_a` (H_i = H2^{a_i}), the Λ/k*/T machinery, the
   prop51 application, and the hbd1 branches "m ≥ 2" (branch A) and
   "m = 1 & k ≤ n" (branch B) are all fully proven and compile.
TECHNICAL LESSONS for finishing branch C and hbd2 (all learned the hard way):
 • The m=1 & k=n+1 collapse must use the product identity
   `H2·(∏ Icc 3 (n+1) H) = H2^x` (peel `2` off `hprodH` via `Finset.prod_insert`
   after `Icc 2 (n+1) = insert 2 (Icc 3 (n+1))`); the exponent of H2 collapses to
   −x+2ε and the bound ends as `cb·c0²·(H1)⁻¹·H2^{−(x−2ε)}`, then two
   `pow_neg_base_transfer` steps (e=1 with H=H1; e=x−2ε with H=H2), recombine
   `cb·cb^e = cb^(e+1)` and `Hgt⁻¹·Hgt^{−e} = Hgt^{−(1+e)}` (rpow_add), lower the
   exponent via Λ ≤ x (from Λ = A/a_k, k = n+1 ⇒ A = x by `A_at_top`+`hasum`,
   a_k ≥ 1) and bound cb-power by 2X+1.
 • `ring` on expressions containing `x⁻¹` generates "denominator nonzero"
   side-goals (disjunction goals like `H 1 = 0 ∨ c0 = 0 ∨ ⋯`) — avoid `ring`
   over subterms with `⁻¹`; prefer `congr`/`rw`/`mul_assoc`/`rpow`-only steps, or
   convert `(H1)⁻¹` ↔ `(H1)^(-1)` with `Real.rpow_neg_one` and work in rpow.
 • `rw [hH2P]` cannot match `H2·∏` inside `(H2^{t0}·H2)·∏`; regroup with
   `← mul_assoc` first.
 • `mul_le_mul` takes `(a≤b)(c≤d)(0≤c)(0≤b)` (4 args, the last is 0 ≤ b!).
 • `rw [hExpEqC]` where hExpEqC : -(x-2ε) = -x+2ε rewrites BOTH rpow-exponent
   occurrences in the goal/hypothesis; to change only the H2-factor exponent
   rewrite the GOAL with the opposite-direction equality then `exact hp`.
 • rpow combination of ≤ 5 powers of one base: use separate
   `rw [← Real.rpow_natCast base n]` (for nat-power factors) then repeated
   `rw [← Real.rpow_add hpos]`; final `+ -a` vs `- a` mismatches are avoided by
   writing the target exponent in `+ (-a)` form.
 • heartbeat budget: perP_data is one large declaration; keep maxHeartbeats high
   (set_option at top of file is 800000) but expect slowness; if a ring/whnf
   timeout persists, split the remaining branch analyses into separate top-level
   lemmas with explicit parameters.
REMAINING WORK (in order): (1) finish branch C inside perP_data; (2) fill hbd2
(decay bound): same three cases, each ends with D ≤ cb·c0²·H2^{−(2−2ε)} using
A ≥ 1, a_u ≥ 1 (m≥2: exponent −A−a_u+2ε ≤ −2+2ε), A ≥ 1 (m=1,k≤n: −A−1+2ε),
H1⁻¹ ≤ 1 and −x+2ε ≤ −2+2ε (m=1,k=n+1); then `simpa [P0Bound, Cb, cb]`;
(3) write `poels_dio_finite_case` (assembly): ωN via exists_omegaN from hfinite;
w2 = ωN+ε/2, hB = hB_of_not_sol (omegaN_plus_not_sol), wbar = n−ε/4,
hA = dirichlet_omegaSolBar; weak_lemma41 → c0; e1/e2 workable exponents →
wirsing_irreducible_solutions → irreducible P_j with ‖P_j‖ → ∞; perP_data per j;
|ξ−α_j| → 0 via the decay bound ⇒ heights_unbounded_of_tendsto gives ∀h0 ∃j with
h0 ≤ Hgt α_j; output (x_j, a_j, α_j) with C := PBound n hn ξ c0 X (needs 1 ≤ C,
from c0 ≥ 1, cb ≥ 1, X ≥ 0).

CONVENTIONS (unchanged): powers are Real.rpow; ‖P‖ = (P.map (Int.castRingHom RR)).supNorm
for P : Polynomial ZZ, evaluation Polynomial.eval xi (P.map ... RR); naive height =
inline (let p := minpoly QQ α; D := lcm of denominators of p.coeff; sup over
p.support of (D·p.coeff i).num.natAbs : NN) as ℝ; IsCoprime is over QQ[X]
(resp. RR[X]) of the mapped polynomials wherever coprimality of constructed
families is asserted.  The final theorem text is unchanged. -/

