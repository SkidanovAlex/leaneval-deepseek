import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Normed.Field.Basic
import Mathlib.Data.Finset.Functor
import Mathlib.RingTheory.MvPolynomial.Homogeneous

open MvPolynomial
open scoped BigOperators

namespace Commons.Algebra.MvPolynomial

noncomputable section
open Classical

-- =====================================================================
-- Exponents of a given total weight and their basic arithmetic.
-- =====================================================================

/-- total weight of an exponent (sum of coordinates) -/
private def wt (n : ℕ) (a : Fin n →₀ ℕ) : ℕ := Finsupp.weight (1 : Fin n → ℕ) a

private noncomputable instance expFintype (n d : ℕ) :
    Fintype {m : Fin n →₀ ℕ // wt n m = d} := by
  classical
  exact (Finsupp.finite_of_nat_weight_eq (1 : Fin n → ℕ) (by intro x; simp) d).fintype

/-- the finite set of exponents of total weight exactly `d` -/
private noncomputable def wtExps (n d : ℕ) : Finset (Fin n →₀ ℕ) :=
  (Finset.univ : Finset {m : Fin n →₀ ℕ // wt n m = d}).image (fun s => (s : Fin n →₀ ℕ))

private lemma mem_wtExps {n d : ℕ} (m : Fin n →₀ ℕ) : m ∈ wtExps n d ↔ wt n m = d := by
  classical
  simp [wtExps, Finset.mem_image]

private lemma wt_single_two {n : ℕ} (j : Fin n) : wt n (Finsupp.single j 2) = 2 := by
  dsimp [wt]
  rw [Finsupp.weight_single]
  norm_num

private lemma wt_add_two {n : ℕ} (j : Fin n) (b : Fin n →₀ ℕ) :
    wt n (b + Finsupp.single j 2) = wt n b + 2 := by
  dsimp [wt]
  rw [map_add]
  rw [Finsupp.weight_single]
  norm_num

private lemma sub_add_single_two {n : ℕ} (j : Fin n) {a : Fin n →₀ ℕ} (h : 2 ≤ a j) :
    (a - Finsupp.single j 2) + Finsupp.single j 2 = a := by
  ext i
  by_cases hji : i = j
  · subst i
    simp
    omega
  · simp [hji]

private lemma add_sub_single_two {n : ℕ} (j : Fin n) (b : Fin n →₀ ℕ) :
    (b + Finsupp.single j 2) - Finsupp.single j 2 = b := by
  ext i
  by_cases hji : i = j
  · subst i
    simp
  · simp

private lemma wt_sub_two {n : ℕ} (j : Fin n) {a : Fin n →₀ ℕ} (h : 2 ≤ a j) :
    wt n (a - Finsupp.single j 2) = wt n a - 2 := by
  have hwa : wt n a = wt n (a - Finsupp.single j 2) + 2 := by
    rw [← sub_add_single_two j h]
    dsimp [wt]
    rw [map_add]
    rw [Finsupp.weight_single]
    norm_num
  omega

private lemma add_two_apply_same {n : ℕ} (j : Fin n) (b : Fin n →₀ ℕ) :
    ((b + Finsupp.single j 2) : Fin n →₀ ℕ) j = b j + 2 := by
  simp [Finsupp.add_apply]

/-- reindexing: replacing `a` by `a - 2 e_j` turns a sum over weight-`k` exponents
    (restricted to `2 ≤ a j`) into a sum over weight-`m` exponents. -/
private lemma reindex_sum {n : ℕ} {k m : ℕ} (j : Fin n) (hmk : m + 2 = k)
    (F : (Fin n →₀ ℕ) → ℝ) :
    (∑ a ∈ wtExps n k, if 2 ≤ a j then F (a - Finsupp.single j 2) else 0)
      = (∑ b ∈ wtExps n m, F b) := by
  classical
  let s : Finset (Fin n →₀ ℕ) := (wtExps n k).filter (fun a => 2 ≤ a j)
  have hL : (∑ a ∈ wtExps n k, if 2 ≤ a j then F (a - Finsupp.single j 2) else 0)
      = ∑ a ∈ s, F (a - Finsupp.single j 2) := by
    dsimp [s]
    rw [← Finset.sum_filter]
  rw [hL]
  rw [Finset.sum_bij' (s := s) (t := wtExps n m)
        (i := fun a _ => a - Finsupp.single j 2)
        (j := fun b _ => b + Finsupp.single j 2)]
  · -- hi : i a ∈ t
    intro a ha
    have ha1 : a ∈ wtExps n k := (Finset.mem_filter.mp ha).1
    have ha2 : 2 ≤ a j := (Finset.mem_filter.mp ha).2
    rw [mem_wtExps]
    have hw : wt n a = k := (mem_wtExps a).mp ha1
    rw [wt_sub_two j ha2, hw]
    omega
  · -- hj : j b ∈ s
    intro b hb
    have hw : wt n b = m := (mem_wtExps b).mp hb
    rw [Finset.mem_filter]
    constructor
    · rw [mem_wtExps]
      rw [wt_add_two, hw]
      omega
    · rw [add_two_apply_same]
      omega
  · -- left_neg
    intro a ha
    have ha2 : 2 ≤ a j := (Finset.mem_filter.mp ha).2
    exact sub_add_single_two j ha2
  · -- right_neg
    intro b hb
    exact add_sub_single_two j b
  · -- congr
    intro a ha
    rfl

private lemma reindex_sum_shift {n : ℕ} {k m : ℕ} (j : Fin n) (hmk : m + 2 = k)
    (G : (Fin n →₀ ℕ) → ℝ) :
    (∑ a ∈ wtExps n k, if 2 ≤ a j then G a else 0)
      = (∑ b ∈ wtExps n m, G (b + Finsupp.single j 2)) := by
  classical
  let s : Finset (Fin n →₀ ℕ) := (wtExps n k).filter (fun a => 2 ≤ a j)
  have hL : (∑ a ∈ wtExps n k, if 2 ≤ a j then G a else 0)
      = ∑ a ∈ s, G a := by
    dsimp [s]
    rw [← Finset.sum_filter]
  rw [hL]
  rw [Finset.sum_bij' (s := s) (t := wtExps n m)
        (i := fun a _ => a - Finsupp.single j 2)
        (j := fun b _ => b + Finsupp.single j 2)]
  · -- hi : i a ∈ t
    intro a ha
    have ha1 : a ∈ wtExps n k := (Finset.mem_filter.mp ha).1
    have ha2 : 2 ≤ a j := (Finset.mem_filter.mp ha).2
    rw [mem_wtExps]
    have hw : wt n a = k := (mem_wtExps a).mp ha1
    rw [wt_sub_two j ha2, hw]
    omega
  · -- hj : j b ∈ s
    intro b hb
    have hw : wt n b = m := (mem_wtExps b).mp hb
    rw [Finset.mem_filter]
    constructor
    · rw [mem_wtExps]
      rw [wt_add_two, hw]
      omega
    · rw [add_two_apply_same]
      omega
  · -- left_neg
    intro a ha
    have ha2 : 2 ≤ a j := (Finset.mem_filter.mp ha).2
    exact sub_add_single_two j ha2
  · -- right_neg
    intro b hb
    exact add_sub_single_two j b
  · -- congr
    intro a ha
    have ha2 : 2 ≤ a j := (Finset.mem_filter.mp ha).2
    rw [sub_add_single_two j ha2]

-- =====================================================================
-- The factorial weight function.
-- =====================================================================

/-- `∏_i (a i)!` — the monomial weight for the Fischer-type inner product. -/
private def factW {n : ℕ} (a : Fin n →₀ ℕ) : ℝ :=
  ((∏ i : Fin n, (a i).factorial : ℕ) : ℝ)

private lemma factW_pos {n : ℕ} (a : Fin n →₀ ℕ) : 0 < factW a := by
  dsimp [factW]
  positivity

private lemma shift_eq_update {n : ℕ} (j : Fin n) (b : Fin n →₀ ℕ) :
    (fun i : Fin n => ((b + Finsupp.single j 2) : Fin n →₀ ℕ) i)
      = Function.update (fun i : Fin n => b i) j (b j + 2) := by
  funext i
  by_cases h : i = j
  · subst i
    simp [Finsupp.add_apply]
  · simp [Finsupp.add_apply, h]

private lemma prod_update_coord {n : ℕ} (j : Fin n) (c : Fin n → ℕ) (r : ℕ) :
    (∏ i : Fin n, ((Function.update c j r) i).factorial : ℕ) =
      r.factorial * (∏ i ∈ (Finset.univ : Finset (Fin n)).erase j, (c i).factorial) := by
  have hs := Finset.mul_prod_erase (s := (Finset.univ : Finset (Fin n)))
      (f := fun i : Fin n => ((Function.update c j r) i).factorial) (a := j) (Finset.mem_univ j)
  rw [← hs]
  congr 1
  · simp
  · apply Finset.prod_congr rfl
    intro i hi
    have hne : i ≠ j := (Finset.mem_erase.mp hi).1
    simp [hne]

private lemma cast_factorial_add_two (r : ℕ) :
    (((r + 2).factorial : ℕ) : ℝ) = ((r + 2 : ℕ) : ℝ) * ((r + 1 : ℕ) : ℝ) * (r.factorial : ℝ) := by
  rw [show (r + 2).factorial = (r + 2) * (r + 1) * r.factorial by
        rw [show r + 2 = (r + 1) + 1 by omega]
        rw [Nat.factorial_succ]
        rw [Nat.factorial_succ]
        rw [← Nat.mul_assoc]]
  norm_num

/-- factorial weights shift by the two factors that appear when differentiating twice -/
private lemma factW_add_two_single {n : ℕ} (j : Fin n) (b : Fin n →₀ ℕ) :
    factW (b + Finsupp.single j 2) =
      factW b * (((b j + 1 : ℕ) : ℝ)) * (((b j + 2 : ℕ) : ℝ)) := by
  let P : ℕ := ∏ i ∈ (Finset.univ : Finset (Fin n)).erase j, (b i).factorial
  have hfull : (∏ i : Fin n, (((b + Finsupp.single j 2) : Fin n →₀ ℕ) i).factorial)
      = (b j + 2).factorial * P := by
    have hprod : (∏ i : Fin n, (((b + Finsupp.single j 2) : Fin n →₀ ℕ) i).factorial)
        = (∏ i : Fin n, ((Function.update (fun i : Fin n => b i) j (b j + 2)) i).factorial) := by
      apply Finset.prod_congr rfl
      intro i hi
      congr 1
      exact congrFun (shift_eq_update j b) i
    rw [hprod]
    dsimp [P]
    rw [prod_update_coord j (fun i : Fin n => b i) (b j + 2)]
  have hfullb : (∏ i : Fin n, (b i).factorial) = (b j).factorial * P := by
    dsimp [P]
    rw [← Finset.mul_prod_erase (s := (Finset.univ : Finset (Fin n)))
        (f := fun i : Fin n => (b i).factorial) (a := j) (Finset.mem_univ j)]
  calc
    factW (b + Finsupp.single j 2)
        = (((b j + 2).factorial * P : ℕ) : ℝ) := by
            rw [factW]
            exact_mod_cast hfull
    _ = (((b j + 2).factorial : ℕ) : ℝ) * (P : ℝ) := by norm_num
    _ = (((b j + 2 : ℕ) : ℝ) * ((b j + 1 : ℕ) : ℝ) * ((b j).factorial : ℝ)) * (P : ℝ) := by
            rw [cast_factorial_add_two (b j)]
    _ = factW b * (((b j + 1 : ℕ) : ℝ)) * (((b j + 2 : ℕ) : ℝ)) := by
            dsimp [factW]
            rw [hfullb]
            push_cast
            ring

-- =====================================================================
-- Coefficient identities for `X_j^2 * g` and for two partial derivatives.
-- =====================================================================

private lemma coeff_X2_mul {n : ℕ} (j : Fin n) (g : MvPolynomial (Fin n) ℝ)
    (a : Fin n →₀ ℕ) :
    coeff a ((X j)^2 * g) = if 2 ≤ a j then coeff (a - Finsupp.single j 2) g else 0 := by
  classical
  rw [pow_two, mul_assoc]
  rw [coeff_X_mul']
  by_cases h2 : 2 ≤ a j
  · -- a j ≥ 2 : both branches present
    have hpos : j ∈ a.support := by
      rw [Finsupp.mem_support_iff]
      omega
    rw [if_pos hpos]
    rw [coeff_X_mul']
    have hpos2 : j ∈ (a - Finsupp.single j 1).support := by
      rw [Finsupp.mem_support_iff]
      simp [Finsupp.tsub_apply]
      omega
    rw [if_pos hpos2]
    have hsub : (a - Finsupp.single j 1) - Finsupp.single j 1 = a - Finsupp.single j 2 := by
      ext i
      by_cases hji : i = j
      · subst i
        simp [Finsupp.tsub_apply]
        omega
      · simp [Finsupp.tsub_apply, hji]
    rw [hsub]
    rw [if_pos h2]
  · -- a j ≤ 1 : the coefficient is zero
    have hsub : a j ≤ 1 := by omega
    by_cases hpos : j ∈ a.support
    · rw [if_pos hpos]
      rw [coeff_X_mul']
      have hnot : j ∉ (a - Finsupp.single j 1).support := by
        rw [Finsupp.mem_support_iff]
        simp [Finsupp.tsub_apply]
        omega
      rw [if_neg hnot]
      rw [if_neg h2]
    · rw [if_neg hpos]
      rw [if_neg h2]

private lemma coeff_pderiv2 {n : ℕ} (j : Fin n) (f : MvPolynomial (Fin n) ℝ)
    (b : Fin n →₀ ℕ) :
    coeff b (pderiv j (pderiv j f)) =
      ((((b j + 1 : ℕ) : ℝ)) * (((b j + 2 : ℕ) : ℝ))) * coeff (b + Finsupp.single j 2) f := by
  rw [coeff_pderiv (i := j) (p := pderiv j f) (m := b)]
  rw [coeff_pderiv (i := j) (p := f) (m := b + Finsupp.single j 1)]
  have hsum : b + Finsupp.single j 1 + Finsupp.single j 1 = b + Finsupp.single j 2 := by
    ext i
    by_cases hji : i = j
    · subst i
      simp [Finsupp.add_apply]
    · simp [Finsupp.add_apply, hji]
  rw [hsum]
  have hfac1 : (↑(b j) + 1) = (((b j + 1 : ℕ) : ℝ)) := by norm_num
  have hfac2 : (↑(((b + Finsupp.single j 1) : Fin n →₀ ℕ) j) + 1) = (((b j + 2 : ℕ) : ℝ)) := by
    simp [Finsupp.add_apply]
    ring
  rw [hfac1, hfac2]
  ring

-- =====================================================================
-- The self-adjointness of the Laplacian with respect to the factorial pairing.
-- =====================================================================

private lemma term_shift {n : ℕ} (j : Fin n) (b : Fin n →₀ ℕ)
    (f g : MvPolynomial (Fin n) ℝ) :
    factW (b + Finsupp.single j 2) * coeff (b + Finsupp.single j 2) f * coeff b g
      = factW b * coeff b (pderiv j (pderiv j f)) * coeff b g := by
  rw [factW_add_two_single j b, coeff_pderiv2 j f b]
  ring

private lemma pair_shift_j {n : ℕ} {k m : ℕ} (j : Fin n) (hmk : m + 2 = k)
    (f g : MvPolynomial (Fin n) ℝ) :
    (∑ a ∈ wtExps n k, factW a * coeff a f * coeff a ((X j)^2 * g))
      = (∑ b ∈ wtExps n m, factW b * coeff b (pderiv j (pderiv j f)) * coeff b g) := by
  classical
  calc
    (∑ a ∈ wtExps n k, factW a * coeff a f * coeff a ((X j)^2 * g))
        = (∑ a ∈ wtExps n k, factW a * coeff a f *
              (if 2 ≤ a j then coeff (a - Finsupp.single j 2) g else 0)) := by
            apply Finset.sum_congr rfl
            intro a ha
            rw [coeff_X2_mul j g a]
    _ = (∑ a ∈ wtExps n k,
          if 2 ≤ a j then factW a * coeff a f * coeff (a - Finsupp.single j 2) g else 0) := by
            apply Finset.sum_congr rfl
            intro a ha
            by_cases h : 2 ≤ a j
            · simp [h]
            · simp [h]
    _ = (∑ b ∈ wtExps n m, factW (b + Finsupp.single j 2) * coeff (b + Finsupp.single j 2) f *
              coeff ((b + Finsupp.single j 2) - Finsupp.single j 2) g) := by
            rw [reindex_sum_shift (k := k) (m := m) j hmk
                (fun a => factW a * coeff a f * coeff (a - Finsupp.single j 2) g)]
    _ = (∑ b ∈ wtExps n m, factW (b + Finsupp.single j 2) * coeff (b + Finsupp.single j 2) f * coeff b g) := by
            apply Finset.sum_congr rfl
            intro b hb
            rw [add_sub_single_two j b]
    _ = (∑ b ∈ wtExps n m, factW b * coeff b (pderiv j (pderiv j f)) * coeff b g) := by
            apply Finset.sum_congr rfl
            intro b hb
            exact term_shift j b f g

-- =====================================================================
-- Positivity of the pairing and consequences for `H`.
-- =====================================================================

private lemma coeff_X2_sum_mul {n : ℕ} (g : MvPolynomial (Fin n) ℝ) (a : Fin n →₀ ℕ) :
    coeff a ((∑ j : Fin n, (X j)^2) * g) = ∑ j : Fin n, coeff a ((X j)^2 * g) := by
  rw [Finset.sum_mul]
  rw [coeff_sum]

private lemma pair_X2_sum_eq_lap {n : ℕ} {k m : ℕ} (hmk : m + 2 = k)
    (f g : MvPolynomial (Fin n) ℝ) :
    (∑ a ∈ wtExps n k, factW a * coeff a f * coeff a ((∑ j : Fin n, (X j)^2) * g))
      = (∑ b ∈ wtExps n m, factW b * coeff b (∑ j : Fin n, pderiv j (pderiv j f)) * coeff b g) := by
  classical
  calc
    (∑ a ∈ wtExps n k, factW a * coeff a f * coeff a ((∑ j : Fin n, (X j)^2) * g))
        = (∑ a ∈ wtExps n k, factW a * coeff a f * (∑ j : Fin n, coeff a ((X j)^2 * g))) := by
            apply Finset.sum_congr rfl
            intro a ha
            rw [coeff_X2_sum_mul g a]
    _ = (∑ a ∈ wtExps n k, ∑ j : Fin n, factW a * coeff a f * coeff a ((X j)^2 * g)) := by
            apply Finset.sum_congr rfl
            intro a ha
            rw [Finset.mul_sum]
    _ = (∑ j : Fin n, ∑ a ∈ wtExps n k, factW a * coeff a f * coeff a ((X j)^2 * g)) := by
            rw [Finset.sum_comm]
    _ = (∑ j : Fin n, ∑ b ∈ wtExps n m, factW b * coeff b (pderiv j (pderiv j f)) * coeff b g) := by
            apply Finset.sum_congr rfl
            intro j hj
            exact pair_shift_j j hmk f g
    _ = (∑ b ∈ wtExps n m, ∑ j : Fin n, factW b * coeff b (pderiv j (pderiv j f)) * coeff b g) := by
            rw [Finset.sum_comm]
    _ = (∑ b ∈ wtExps n m, factW b * coeff b (∑ j : Fin n, pderiv j (pderiv j f)) * coeff b g) := by
            apply Finset.sum_congr rfl
            intro b hb
            calc
              (∑ j : Fin n, factW b * coeff b (pderiv j (pderiv j f)) * coeff b g)
                  = (∑ j : Fin n, (factW b * coeff b g) * coeff b (pderiv j (pderiv j f))) := by
                      apply Finset.sum_congr rfl
                      intro j hj
                      ring
              _ = (factW b * coeff b g) * (∑ j : Fin n, coeff b (pderiv j (pderiv j f))) := by
                      rw [Finset.mul_sum]
              _ = factW b * coeff b (∑ j : Fin n, pderiv j (pderiv j f)) * coeff b g := by
                      rw [coeff_sum]
                      ring

private lemma pair_sq_eq_zero {n : ℕ} {k : ℕ} (H : MvPolynomial (Fin n) ℝ)
    (hsum : (∑ a ∈ wtExps n k, factW a * (coeff a H)^2) = 0) :
    ∀ a ∈ wtExps n k, coeff a H = 0 := by
  intro a ha
  have hnonneg : ∀ x ∈ wtExps n k, 0 ≤ factW x * (coeff x H)^2 := by
    intro x hx
    exact mul_nonneg (le_of_lt (factW_pos x)) (sq_nonneg (coeff x H))
  have hz : ∀ x ∈ wtExps n k, factW x * (coeff x H)^2 = 0 := by
    exact (Finset.sum_eq_zero_iff_of_nonneg (s := wtExps n k)
      (f := fun x => factW x * (coeff x H)^2) hnonneg).mp hsum
  have hterm := hz a ha
  have hf : factW a ≠ 0 := ne_of_gt (factW_pos a)
  have hsq0 : (coeff a H)^2 = 0 := by
    rcases mul_eq_zero.mp hterm with h1 | h2
    · exact False.elim (hf h1)
    · exact h2
  exact sq_eq_zero_iff.mp hsq0

private lemma coeff_eq_zero_of_weight_ne {n k : ℕ} (H : MvPolynomial (Fin n) ℝ)
    (hH : H ∈ homogeneousSubmodule (Fin n) ℝ k) {a : Fin n →₀ ℕ}
    (hw : wt n a ≠ k) : coeff a H = 0 := by
  have hIso : H.IsHomogeneous k :=
    (MvPolynomial.mem_homogeneousSubmodule (n := k) (p := H)).mp hH
  have hIso' : MvPolynomial.IsWeightedHomogeneous (1 : Fin n → ℕ) H k := by
    simpa [MvPolynomial.IsHomogeneous] using hIso
  exact MvPolynomial.IsWeightedHomogeneous.coeff_eq_zero hIso' a (by simpa [wt] using hw)

private lemma coord_le_wt {n : ℕ} (a : Fin n →₀ ℕ) (j : Fin n) : a j ≤ wt n a := by
  dsimp [wt]
  rw [Finsupp.weight_eq_sum]
  have h := Finset.single_le_sum (s := (Finset.univ : Finset (Fin n)))
      (f := fun i : Fin n => a i • (1 : ℕ))
      (by intro i hi; exact Nat.zero_le _) (a := j) (Finset.mem_univ j)
  simpa using h

theorem harmonic_X2_intersection {n : ℕ} {k : ℕ}
    (H : MvPolynomial (Fin n) ℝ) (Q : MvPolynomial (Fin n) ℝ)
    (hH : H ∈ MvPolynomial.homogeneousSubmodule (Fin n) ℝ k)
    (hQ : Q ∈ MvPolynomial.homogeneousSubmodule (Fin n) ℝ (k - 2))
    (hlap : (∑ i : Fin n, MvPolynomial.pderiv i (MvPolynomial.pderiv i H)) = 0)
    (h : H = (∑ j : Fin n, (MvPolynomial.X j)^2) * Q) :
    H = 0 := by
  classical
  by_cases hn0 : n = 0
  · -- no variables: the sum of squares is 0, hence H = 0
    subst n
    simp [h]
  · by_cases hk2 : 2 ≤ k
    · -- main case : positivity of the Fischer-type pairing
      let m : ℕ := k - 2
      have hmk : m + 2 = k := by omega
      let E : MvPolynomial (Fin n) ℝ := (∑ j : Fin n, (X j)^2) * Q
      have hE : H = E := h
      have hlapE : (∑ i : Fin n, pderiv i (pderiv i E)) = 0 := by
        rw [hE] at hlap
        exact hlap
      have hpairE : (∑ x ∈ wtExps n k, factW x * (coeff x E)^2) = 0 := by
        calc
          (∑ x ∈ wtExps n k, factW x * (coeff x E)^2)
              = (∑ x ∈ wtExps n k, factW x * coeff x E * coeff x E) := by
                  apply Finset.sum_congr rfl
                  intro x hx
                  ring
          _ = (∑ x ∈ wtExps n k, factW x * coeff x E * coeff x ((∑ j : Fin n, (X j)^2) * Q)) := by
                  rfl
          _ = (∑ b ∈ wtExps n m, factW b * coeff b (∑ j : Fin n, pderiv j (pderiv j E)) * coeff b Q) := by
                  exact pair_X2_sum_eq_lap hmk E Q
          _ = 0 := by
                  rw [hlapE]
                  simp
      have hpair : (∑ x ∈ wtExps n k, factW x * (coeff x H)^2) = 0 := by
        calc
          (∑ x ∈ wtExps n k, factW x * (coeff x H)^2)
              = (∑ x ∈ wtExps n k, factW x * (coeff x E)^2) := by
                  apply Finset.sum_congr rfl
                  intro x hx
                  rw [hE]
          _ = 0 := hpairE
      have hzero_coeff : ∀ a : Fin n →₀ ℕ, coeff a H = 0 := by
        intro a
        by_cases hw : wt n a = k
        · exact pair_sq_eq_zero H hpair a ((mem_wtExps a).mpr hw)
        · exact coeff_eq_zero_of_weight_ne H hH hw
      ext a
      exact hzero_coeff a
    · -- k ≤ 1 : H = r2 * Q is homogeneous of degree k ≤ 1, and every monomial
      -- of weight k appears in r2 * Q with coefficient 0 (each summand needs
      -- exponent ≥ 2 in some variable).
      have hk1 : k ≤ 1 := by omega
      have hzero_coeff : ∀ a : Fin n →₀ ℕ, coeff a H = 0 := by
        intro a
        by_cases hw : wt n a = k
        · rw [h]
          rw [coeff_X2_sum_mul Q a]
          apply Finset.sum_eq_zero
          intro j hj
          rw [coeff_X2_mul j Q a]
          have ha2 : ¬ 2 ≤ a j := by
            have hle : a j ≤ wt n a := coord_le_wt a j
            omega
          simp [ha2]
        · exact coeff_eq_zero_of_weight_ne H hH hw
      ext a
      exact hzero_coeff a

end

end Commons.Algebra.MvPolynomial