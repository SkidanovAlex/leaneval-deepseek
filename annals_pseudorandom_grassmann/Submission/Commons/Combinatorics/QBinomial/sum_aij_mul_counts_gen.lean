import Mathlib
import Submission.Commons.Combinatorics.QBinomial.sum_aij_mul_counts

namespace Commons.Combinatorics.QBinomial

open Module

noncomputable section

/-- The coefficient `c(i,j)` appearing in the statement below. -/
private def coef (a : ℕ → ℤ) (i j : ℕ) : ℤ :=
  if i = 0 then (if j = 0 then 0 else a j) else (if j = 0 then a i else -(a i * a j))

/-- `xfun a i = a i` for `i ≠ 0`, and `xfun a 0 = 0`. -/
private def xfun (a : ℕ → ℤ) (i : ℕ) : ℤ := if i = 0 then 0 else a i

/-- The Kronecker delta, as an integer. -/
private def indfun (i : ℕ) : ℤ := if i = 0 then 1 else 0

private lemma coef_eq (a : ℕ → ℤ) (i j : ℕ) :
    coef a i j = xfun a i * (indfun j - xfun a j) + indfun i * xfun a j := by
  by_cases hi : i = 0 <;> by_cases hj : j = 0 <;>
    simp [coef, xfun, indfun, hi, hj]

/-- The abstract combinatorial identity: a doubly-indexed sum whose coefficient is `coef a`
factors into the "row" and "column" sums.  Unlike the version in
`sum_aij_mul_counts`, the two index ranges are independent. -/
private lemma sum_coef_mul_gen (n m : ℕ) (a : ℕ → ℤ) (A B : ℕ → ℤ)
    (hA0 : A 0 = 1) (hB0 : B 0 = 1) :
    (∑ i ∈ Finset.range (n + 1), ∑ j ∈ Finset.range (m + 1), coef a i j * (A i * B j))
      = (∑ i ∈ Finset.Icc 1 n, a i * A i) + (∑ j ∈ Finset.Icc 1 m, a j * B j)
        - (∑ i ∈ Finset.Icc 1 n, a i * A i) * (∑ j ∈ Finset.Icc 1 m, a j * B j) := by
  have hR : Finset.range (n + 1) = insert 0 (Finset.Icc 1 n) := by
    ext k
    simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Icc]
    omega
  have hSm : Finset.range (m + 1) = insert 0 (Finset.Icc 1 m) := by
    ext k
    simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Icc]
    omega
  have h0In : (0 : ℕ) ∉ Finset.Icc 1 n := by simp [Finset.mem_Icc]
  have h0Im : (0 : ℕ) ∉ Finset.Icc 1 m := by simp [Finset.mem_Icc]
  have hstep :
      (∑ i ∈ Finset.range (n + 1), ∑ j ∈ Finset.range (m + 1), coef a i j * (A i * B j))
        = (∑ i ∈ Finset.range (n + 1), ∑ j ∈ Finset.range (m + 1),
              (xfun a i * A i) * ((indfun j - xfun a j) * B j))
          + (∑ i ∈ Finset.range (n + 1), ∑ j ∈ Finset.range (m + 1),
              (indfun i * A i) * (xfun a j * B j)) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j _
    rw [coef_eq a i j]
    ring
  have h1 :
      (∑ i ∈ Finset.range (n + 1), ∑ j ∈ Finset.range (m + 1),
          (xfun a i * A i) * ((indfun j - xfun a j) * B j))
        = (∑ i ∈ Finset.range (n + 1), xfun a i * A i)
          * (∑ j ∈ Finset.range (m + 1), (indfun j - xfun a j) * B j) :=
    (Finset.sum_mul_sum (Finset.range (n + 1)) (Finset.range (m + 1))
      (fun i => xfun a i * A i) (fun j => (indfun j - xfun a j) * B j)).symm
  have h2 :
      (∑ i ∈ Finset.range (n + 1), ∑ j ∈ Finset.range (m + 1),
          (indfun i * A i) * (xfun a j * B j))
        = (∑ i ∈ Finset.range (n + 1), indfun i * A i)
          * (∑ j ∈ Finset.range (m + 1), xfun a j * B j) :=
    (Finset.sum_mul_sum (Finset.range (n + 1)) (Finset.range (m + 1))
      (fun i => indfun i * A i) (fun j => xfun a j * B j)).symm
  have hxA : (∑ i ∈ Finset.range (n + 1), xfun a i * A i)
      = ∑ i ∈ Finset.Icc 1 n, a i * A i := by
    rw [hR, Finset.sum_insert h0In]
    rw [show xfun a 0 * A 0 = 0 by simp [xfun], zero_add]
    apply Finset.sum_congr rfl
    intro i hi
    have hi0 : i ≠ 0 := by
      have := (Finset.mem_Icc.mp hi).1
      omega
    rw [show xfun a i = a i by simp [xfun, hi0]]
  have hxB : (∑ j ∈ Finset.range (m + 1), xfun a j * B j)
      = ∑ j ∈ Finset.Icc 1 m, a j * B j := by
    rw [hSm, Finset.sum_insert h0Im]
    rw [show xfun a 0 * B 0 = 0 by simp [xfun], zero_add]
    apply Finset.sum_congr rfl
    intro j hj
    have hj0 : j ≠ 0 := by
      have := (Finset.mem_Icc.mp hj).1
      omega
    rw [show xfun a j = a j by simp [xfun, hj0]]
  have hindA : (∑ i ∈ Finset.range (n + 1), indfun i * A i) = 1 := by
    rw [hR, Finset.sum_insert h0In]
    rw [show indfun 0 * A 0 = 1 by simp [indfun, hA0]]
    have hz : ∀ i ∈ Finset.Icc 1 n, indfun i * A i = 0 := by
      intro i hi
      have hi0 : i ≠ 0 := by
        have := (Finset.mem_Icc.mp hi).1
        omega
      rw [show indfun i = 0 by simp [indfun, hi0], zero_mul]
    rw [Finset.sum_eq_zero hz, add_zero]
  have hindB : (∑ j ∈ Finset.range (m + 1), indfun j * B j) = 1 := by
    rw [hSm, Finset.sum_insert h0Im]
    rw [show indfun 0 * B 0 = 1 by simp [indfun, hB0]]
    have hz : ∀ j ∈ Finset.Icc 1 m, indfun j * B j = 0 := by
      intro j hj
      have hj0 : j ≠ 0 := by
        have := (Finset.mem_Icc.mp hj).1
        omega
      rw [show indfun j = 0 by simp [indfun, hj0], zero_mul]
    rw [Finset.sum_eq_zero hz, add_zero]
  have hfac : (∑ j ∈ Finset.range (m + 1), (indfun j - xfun a j) * B j)
      = 1 - ∑ j ∈ Finset.Icc 1 m, a j * B j := by
    have hsplit : (∑ j ∈ Finset.range (m + 1), (indfun j - xfun a j) * B j)
        = (∑ j ∈ Finset.range (m + 1), indfun j * B j)
          - (∑ j ∈ Finset.range (m + 1), xfun a j * B j) := by
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro j _
      rw [sub_mul]
    rw [hsplit, hindB, hxB]
  rw [hstep, h1, h2, hfac, hxA, hindA, hxB]
  ring

/-- Auxiliary: `∑_{i=1}^{N} a i · gb d i` is the indicator of `d ≠ 0`, when `d ≤ N`. -/
private lemma sum_Icc_range_mul_gb (N d : ℕ) (a : ℕ → ℤ)
    (ha : ∀ t : ℕ, 1 ≤ t → ∑ i ∈ Finset.Icc 1 t, a i * (gb t i : ℤ) = 1)
    (hd : d ≤ N) :
    ∑ i ∈ Finset.Icc 1 N, a i * (gb d i : ℤ) = if d = 0 then 0 else 1 := by
  rcases Nat.eq_zero_or_pos d with hd0 | hdpos
  · subst hd0
    rw [if_pos rfl]
    apply Finset.sum_eq_zero
    intro i hi
    have hi1 : 1 ≤ i := (Finset.mem_Icc.mp hi).1
    rw [gb_eq_zero_of_lt 0 i (by omega), Nat.cast_zero, mul_zero]
  · rw [if_neg (Nat.pos_iff_ne_zero.mp hdpos)]
    have hsub : Finset.Icc 1 d ⊆ Finset.Icc 1 N := Finset.Icc_subset_Icc_right hd
    have hzero : ∀ i ∈ Finset.Icc 1 N, i ∉ Finset.Icc 1 d → a i * (gb d i : ℤ) = 0 := by
      intro i hi hin
      have hdlt : d < i := by
        simp only [Finset.mem_Icc] at hi hin
        omega
      rw [gb_eq_zero_of_lt d i hdlt, Nat.cast_zero, mul_zero]
    rw [← Finset.sum_subset hsub hzero]
    exact ha d hdpos

theorem sum_aij_mul_counts_gen (n m : ℕ) (a : ℕ → ℤ)
    (ha : ∀ t : ℕ, 1 ≤ t →
      ∑ i ∈ Finset.Icc 1 t, a i * (Commons.Combinatorics.QBinomial.gb t i : ℤ) = 1)
    (V' : Submodule (ZMod 2) (Fin n → ZMod 2))
    (W' : Submodule (ZMod 2) (Fin m → ZMod 2)) :
    (∑ i ∈ Finset.range (n + 1), ∑ j ∈ Finset.range (m + 1),
      (if i = 0 then (if j = 0 then 0 else a j) else (if j = 0 then a i else -(a i * a j))) *
        ((Nat.card {V₁ : Submodule (ZMod 2) (Fin n → ZMod 2) //
            V₁ ≤ V' ∧ Module.finrank (ZMod 2) V₁ = i} : ℤ) *
         (Nat.card {W₁ : Submodule (ZMod 2) (Fin m → ZMod 2) //
            W' ≤ W₁ ∧ Module.finrank (ZMod 2) W₁ = m - j} : ℤ)))
      = if V' = ⊥ ∧ W' = ⊤ then 0 else 1 := by
  classical
  let d : ℕ := Module.finrank (ZMod 2) V'
  let e : ℕ := m - Module.finrank (ZMod 2) W'
  have hd : d = Module.finrank (ZMod 2) V' := rfl
  have he : e = m - Module.finrank (ZMod 2) W' := rfl
  -- Step 1: rewrite the two `Nat.card`s as Gaussian binomials.
  have hgb : (∑ i ∈ Finset.range (n + 1), ∑ j ∈ Finset.range (m + 1),
        (if i = 0 then (if j = 0 then 0 else a j) else (if j = 0 then a i else -(a i * a j))) *
          ((Nat.card {V₁ : Submodule (ZMod 2) (Fin n → ZMod 2) //
              V₁ ≤ V' ∧ Module.finrank (ZMod 2) V₁ = i} : ℤ) *
           (Nat.card {W₁ : Submodule (ZMod 2) (Fin m → ZMod 2) //
              W' ≤ W₁ ∧ Module.finrank (ZMod 2) W₁ = m - j} : ℤ)))
      = (∑ i ∈ Finset.range (n + 1), ∑ j ∈ Finset.range (m + 1),
          coef a i j * ((gb d i : ℤ) * (gb e j : ℤ))) := by
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j hj
    have hjle : j ≤ m := by
      simp only [Finset.mem_range] at hj
      omega
    have h1 : (Nat.card {V₁ : Submodule (ZMod 2) (Fin n → ZMod 2) //
          V₁ ≤ V' ∧ Module.finrank (ZMod 2) V₁ = i} : ℤ) = (gb d i : ℤ) := by
      rw [Commons.LinearAlgebra.Submodule.card_submodule_le_finrank_eq_gb n V' i, hd]
    have h2 : (Nat.card {W₁ : Submodule (ZMod 2) (Fin m → ZMod 2) //
          W' ≤ W₁ ∧ Module.finrank (ZMod 2) W₁ = m - j} : ℤ) = (gb e j : ℤ) := by
      rw [Commons.LinearAlgebra.Submodule.card_superspace_codim_eq_gb_of_le m W' j hjle, he]
    rw [h1, h2]
    rfl
  -- Step 2: the abstract identity.
  have hA0 : (fun i => (gb d i : ℤ)) 0 = 1 := by simp [gb_zero]
  have hB0 : (fun j => (gb e j : ℤ)) 0 = 1 := by simp [gb_zero]
  have hS : (∑ i ∈ Finset.range (n + 1), ∑ j ∈ Finset.range (m + 1),
        coef a i j * ((gb d i : ℤ) * (gb e j : ℤ)))
      = (∑ i ∈ Finset.Icc 1 n, a i * (gb d i : ℤ)) + (∑ j ∈ Finset.Icc 1 m, a j * (gb e j : ℤ))
        - (∑ i ∈ Finset.Icc 1 n, a i * (gb d i : ℤ))
          * (∑ j ∈ Finset.Icc 1 m, a j * (gb e j : ℤ)) :=
    sum_coef_mul_gen n m a (fun i => (gb d i : ℤ)) (fun j => (gb e j : ℤ)) hA0 hB0
  -- Step 3: the indicator values of the two one-dimensional sums.
  have hdle : d ≤ n := by
    rw [hd]
    have htop : Module.finrank (ZMod 2) (⊤ : Submodule (ZMod 2) (Fin n → ZMod 2)) = n := by
      rw [finrank_top, Module.finrank_pi, Fintype.card_fin]
    exact (Submodule.finrank_mono (R := ZMod 2) le_top).trans (le_of_eq htop)
  have hele : e ≤ m := by
    rw [he]
    exact Nat.sub_le m _
  have hS1 : (∑ i ∈ Finset.Icc 1 n, a i * (gb d i : ℤ)) = if V' = ⊥ then 0 else 1 := by
    rw [sum_Icc_range_mul_gb n d a ha hdle]
    have hd0 : d = 0 ↔ V' = ⊥ := by
      rw [hd]
      exact Submodule.finrank_eq_zero
    by_cases h : V' = ⊥
    · rw [if_pos h, if_pos (hd0.mpr h)]
    · rw [if_neg h, if_neg (fun hh => h (hd0.mp hh))]
  have hS2 : (∑ j ∈ Finset.Icc 1 m, a j * (gb e j : ℤ)) = if W' = ⊤ then 0 else 1 := by
    rw [sum_Icc_range_mul_gb m e a ha hele]
    have he0 : e = 0 ↔ W' = ⊤ := by
      rw [he]
      constructor
      · intro h
        have hmle : Module.finrank (ZMod 2) W' ≤ m :=
          (Submodule.finrank_mono (R := ZMod 2) le_top).trans
            (le_of_eq (by rw [finrank_top, Module.finrank_pi, Fintype.card_fin]))
        have hm : m ≤ Module.finrank (ZMod 2) W' := Nat.sub_eq_zero_iff_le.mp h
        have hfin : Module.finrank (ZMod 2) W' = Module.finrank (ZMod 2) (Fin m → ZMod 2) := by
          rw [Module.finrank_pi, Fintype.card_fin]
          omega
        exact Submodule.eq_top_of_finrank_eq hfin
      · intro h
        rw [h, finrank_top, Module.finrank_pi, Fintype.card_fin, Nat.sub_self]
    by_cases h : W' = ⊤
    · rw [if_pos h, if_pos (he0.mpr h)]
    · rw [if_neg h, if_neg (fun hh => h (he0.mp hh))]
  rw [hgb, hS, hS1, hS2]
  by_cases hV : V' = ⊥ <;> by_cases hW : W' = ⊤ <;> simp [hV, hW]

end

end Commons.Combinatorics.QBinomial
