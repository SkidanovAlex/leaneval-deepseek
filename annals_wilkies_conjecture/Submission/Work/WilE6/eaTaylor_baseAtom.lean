/-
  WilE6: the base atom of the Taylor expansion.

  `eaTaylor_baseAtom`: for the affine EA function `Q = x_i - a` (the "base-fixing atom"
  `baseAtom` of the E6 development), the order-`N` Taylor polynomial is exact for `N ≥ 1`:
  `eaTaylor c (X (inl i) - C a) N y x = x i - a`.

  The only nonvanishing multi-indices in the defining sum are `m = 0` (contributing
  `eaEval c Q y = y i - a`) and `m = e_i` (contributing `1 · (x i - y i)`); every other `m`
  has `eaDmulti c m Q = 0`.  The proof of that vanishing reduces, via the composition law
  `eaDmulti_comp`, to the two elementary facts that `eaD` of a constant vanishes and that
  `eaD` of `x_i - a` is a constant (`1` at `i`, `0` elsewhere).

  Reuses the E3 API: `miFinset`, `mem_miFinset`, `eMI`, `eaDmulti_zero`, `eaDmulti_eMI`,
  `miS`, `miS_add_eMI`, `sum_eMI`, `eaTaylor_eq_sum`, `eaDmulti_comp`.
-/
import Mathlib
import Submission.Work.Wilkies.E.Spec
import Submission.Work.WilE3.API.RemDefs
import Submission.Work.WilE3.API.Rem.eaDmulti_comp

namespace Work.WilE6

open WilkiesDesign.E

/-! ## The elementary values of `eaD` on the affine atom -/

/-- `eaD c j` kills constants. -/
private theorem eaD_C_zero {k r : ℕ} (c : EAChain k r) (j : Fin k) (b : ℝ) :
    eaD c j (MvPolynomial.C b) = 0 := by
  simp [eaD]

/-- `eaD c j (x_i - a)` is `1` when `j = i` and `0` otherwise: the atom is linear in `x_i`
and involves no chain variable. -/
private theorem eaD_atom {k r : ℕ} (c : EAChain k r) (i : Fin k) (a : ℝ) (j : Fin k) :
    eaD c j (MvPolynomial.X (Sum.inl i) - MvPolynomial.C a) = if j = i then 1 else 0 := by
  have h1 : (MvPolynomial.pderiv (Sum.inl j)) (MvPolynomial.X (Sum.inl i) - MvPolynomial.C a)
      = (if j = i then 1 else 0 : EAPoly k r) := by
    rw [map_sub, MvPolynomial.pderiv_X, MvPolynomial.pderiv_C, sub_zero]
    rw [Pi.single_apply]
    by_cases h : j = i
    · subst h; simp
    · have h' : i ≠ j := fun hh => h hh.symm
      simp [h, h']
  have h2 : ∀ j' : Fin r,
      (MvPolynomial.pderiv (Sum.inr j')) (MvPolynomial.X (Sum.inl i) - MvPolynomial.C a) = 0 := by
    intro j'
    rw [map_sub, MvPolynomial.pderiv_C, sub_zero]
    rw [MvPolynomial.pderiv_X_of_ne (fun (h : Sum.inl i = Sum.inr j') => Sum.inl_ne_inr h)]
  rw [eaD, h1]
  simp only [h2, mul_zero, Finset.sum_const_zero, add_zero]

/-- The `j = i` case of `eaD_atom`, in the form needed for the `m = e_i` term. -/
private theorem eaD_atom_self {k r : ℕ} (c : EAChain k r) (i : Fin k) (a : ℝ) :
    eaD c i (MvPolynomial.X (Sum.inl i) - MvPolynomial.C a) = 1 := by
  rw [eaD_atom c i a i, if_pos rfl]

/-! ## Evaluating the atom at a point, and the two Taylor coefficients -/

private theorem eaEval_atom {k r : ℕ} (c : EAChain k r) (i : Fin k) (a : ℝ) (y : Fin k → ℝ) :
    eaEval c (MvPolynomial.X (Sum.inl i) - MvPolynomial.C a) y = y i - a := by
  simp [eaEval]

private theorem eaEval_one {k r : ℕ} (c : EAChain k r) (y : Fin k → ℝ) :
    eaEval c (1 : EAPoly k r) y = 1 := by
  simp [eaEval]

/-- The coefficient monomial of the `m = 0` term is `1`. -/
private theorem prod_zero_idx {k : ℕ} (x y : Fin k → ℝ) :
    (∏ j : Fin k, (x j - y j) ^ ((0 : Fin k → ℕ) j) /
      (((0 : Fin k → ℕ) j).factorial : ℝ)) = 1 := by
  simp

/-- The coefficient monomial of the `m = e_i` term is `x i - y i`. -/
private theorem prod_eMI_idx {k : ℕ} (i : Fin k) (x y : Fin k → ℝ) :
    (∏ j : Fin k, (x j - y j) ^ (Work.WilE3.API.eMI i j) /
      ((Work.WilE3.API.eMI i j).factorial : ℝ)) = x i - y i := by
  rw [Finset.prod_eq_single i]
  · rw [Work.WilE3.API.eMI_apply, if_pos rfl]
    simp
  · intro b _ hb
    rw [Work.WilE3.API.eMI_apply, if_neg hb]
    simp
  · intro hmem; exact absurd (Finset.mem_univ i) hmem

/-! ## Vanishing of `eaDmulti` on the atom -/

private theorem iterate_eaD_zero {k r : ℕ} (c : EAChain k r) (j : Fin k) (n : ℕ) :
    (eaD c j)^[n] (0 : EAPoly k r) = 0 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply', ih]
    simp [eaD]

/-- Every symbolic derivative of `0` is `0`. -/
private theorem eaDmulti_zeroP {k r : ℕ} (c : EAChain k r) (m : Fin k → ℕ) :
    eaDmulti c m (0 : EAPoly k r) = 0 := by
  rw [eaDmulti]
  have h : ∀ L : List (Fin k), L.foldr (fun j g => (eaD c j)^[m j] g) (0 : EAPoly k r) = 0 := by
    intro L
    induction L with
    | nil => rfl
    | cons a t ih => rw [List.foldr_cons, ih]; exact iterate_eaD_zero c a (m a)
  exact h (List.finRange k)

/-- For a nonzero multi-index `m`, every symbolic derivative of a constant vanishes.
Peel one unit off any occupied index with the composition law `eaDmulti_comp`. -/
private theorem eaDmulti_C_vanish {k r : ℕ} (c : EAChain k r) (m : Fin k → ℕ) (b : ℝ)
    (hm : m ≠ 0) : eaDmulti c m (MvPolynomial.C b) = 0 := by
  obtain ⟨j, hj⟩ := Function.ne_iff.mp hm
  have hjpos : 0 < m j := Nat.pos_of_ne_zero hj
  have key : eaDmulti c (Work.WilE3.API.miS m j)
        (eaDmulti c (Work.WilE3.API.eMI j) (MvPolynomial.C b)) =
      eaDmulti c m (MvPolynomial.C b) := by
    rw [Work.WilE3.API.Rem.eaDmulti_comp, Work.WilE3.API.miS_add_eMI hjpos]
  rw [← key, Work.WilE3.API.eaDmulti_eMI, eaD_C_zero]
  exact eaDmulti_zeroP c (Work.WilE3.API.miS m j)

/-- For `m ∉ {0, e_i}`, every symbolic derivative of the atom `x_i - a` vanishes. -/
private theorem eaDmulti_atom_vanishes {k r : ℕ} (c : EAChain k r) (i : Fin k) (a : ℝ)
    (m : Fin k → ℕ) (hm0 : m ≠ 0) (hm1 : m ≠ Work.WilE3.API.eMI i) :
    eaDmulti c m (MvPolynomial.X (Sum.inl i) - MvPolynomial.C a) = 0 := by
  obtain ⟨j, hj⟩ := Function.ne_iff.mp hm0
  have hjpos : 0 < m j := Nat.pos_of_ne_zero hj
  have key : eaDmulti c (Work.WilE3.API.miS m j)
        (eaDmulti c (Work.WilE3.API.eMI j)
          (MvPolynomial.X (Sum.inl i) - MvPolynomial.C a)) =
      eaDmulti c m (MvPolynomial.X (Sum.inl i) - MvPolynomial.C a) := by
    rw [Work.WilE3.API.Rem.eaDmulti_comp, Work.WilE3.API.miS_add_eMI hjpos]
  rw [← key, Work.WilE3.API.eaDmulti_eMI, eaD_atom]
  by_cases hji : j = i
  · rw [hji, if_pos rfl, ← MvPolynomial.C_1]
    refine eaDmulti_C_vanish c (Work.WilE3.API.miS m i) 1 ?_
    intro h
    have hjpos' : 0 < m i := by rw [← hji]; exact hjpos
    exact hm1 (by
      calc m = Work.WilE3.API.miS m i + Work.WilE3.API.eMI i :=
            (Work.WilE3.API.miS_add_eMI hjpos').symm
        _ = 0 + Work.WilE3.API.eMI i := by rw [h]
        _ = Work.WilE3.API.eMI i := zero_add _)
  · rw [if_neg hji]
    exact eaDmulti_zeroP c (Work.WilE3.API.miS m j)

/-! ## The base atom -/

theorem eaTaylor_baseAtom {k r : ℕ} (c : WilkiesDesign.E.EAChain k r) (i : Fin k) (a : ℝ)
    {N : ℕ} (hN : 1 ≤ N) (y x : Fin k → ℝ) :
    WilkiesDesign.E.eaTaylor c (MvPolynomial.X (Sum.inl i) - MvPolynomial.C a) N y x =
      x i - a := by
  rw [Work.WilE3.API.eaTaylor_eq_sum]
  have hne : (0 : Fin k → ℕ) ≠ Work.WilE3.API.eMI i := by
    intro h
    have h2 : (0 : ℕ) = 1 := by simpa [Work.WilE3.API.eMI_apply] using congrFun h i
    omega
  have hsub : ({0, Work.WilE3.API.eMI i} : Finset (Fin k → ℕ)) ⊆ Work.WilE3.API.miFinset k N := by
    intro m hm
    rw [Finset.mem_insert, Finset.mem_singleton] at hm
    rcases hm with rfl | rfl
    · exact Work.WilE3.API.mem_miFinset.mpr (by simp)
    · exact Work.WilE3.API.mem_miFinset.mpr (by rw [Work.WilE3.API.sum_eMI i]; exact hN)
  have hvan : ∀ m ∈ Work.WilE3.API.miFinset k N,
      m ∉ ({0, Work.WilE3.API.eMI i} : Finset (Fin k → ℕ)) →
      eaEval c (eaDmulti c m (MvPolynomial.X (Sum.inl i) - MvPolynomial.C a)) y *
        ∏ j, (x j - y j) ^ m j / ((m j).factorial : ℝ) = 0 := by
    intro m _ hnot
    have hm0 : m ≠ 0 := by intro h; exact hnot (by rw [h]; simp)
    have hm1 : m ≠ Work.WilE3.API.eMI i := by intro h; exact hnot (by rw [h]; simp)
    rw [eaDmulti_atom_vanishes c i a m hm0 hm1]
    simp [eaEval]
  rw [(Finset.sum_subset hsub hvan).symm, Finset.sum_pair hne]
  simp only [Work.WilE3.API.eaDmulti_zero, Work.WilE3.API.eaDmulti_eMI, eaD_atom_self,
    eaEval_atom, eaEval_one, prod_zero_idx, prod_eMI_idx]
  ring

end Work.WilE6
