/-
  WilE4 / CAD — total-degree bookkeeping for the projection data.

  The estimates collected here bound the total degree of the objects the projection data is made of:
  coefficients of a member (`finSuccEquiv`), products, the Sylvester matrix and the resultant, and
  the determinant of a small matrix.  They are what turns `projData` into a family whose total
  degrees — and hence whose size `famDeg` — is bounded by a fixed polynomial in the size of the
  input family.

  (Split out of `Proj.lean`, which `import`s this module.)
-/
import Mathlib

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
open Classical
namespace Work.WilE4.CAD

open MvPolynomial Polynomial

/-! ## Total-degree bookkeeping -/

/-- `rename` along an equivalence preserves the total degree. -/
theorem rename_totalDegree {σ τ : Type*} (e : σ ≃ τ) (p : MvPolynomial σ ℝ) :
    (MvPolynomial.rename e p).totalDegree = p.totalDegree := by
  refine le_antisymm (MvPolynomial.totalDegree_rename_le e p) ?_
  have h := MvPolynomial.totalDegree_rename_le (R := ℝ) (e.symm) (MvPolynomial.rename e p)
  have h2 : MvPolynomial.rename (e.symm) (MvPolynomial.rename e p) = p := by
    rw [MvPolynomial.rename_rename]
    have h3 : (⇑e.symm ∘ ⇑e : σ → σ) = id := funext fun a => e.symm_apply_apply a
    rw [h3, MvPolynomial.rename_id]
    rfl
  rwa [h2] at h

/-- `D ≤ 2 * D * D` for every natural number. -/
theorem le_two_mul_sq (D : ℕ) : D ≤ 2 * D * D := by
  rcases D with _ | e
  · simp
  · have h1 : 1 ≤ 2 * (e + 1) := by omega
    calc e + 1 = (e + 1) * 1 := by ring
      _ ≤ (e + 1) * (2 * (e + 1)) := Nat.mul_le_mul_left _ h1
      _ = 2 * (e + 1) * (e + 1) := by ring

/-- The coefficients of `finSuccEquiv P` do not raise the total degree. -/
theorem totalDegree_coeff_finSucc_le {d : ℕ} (P : MvPolynomial (Fin (d + 1)) ℝ) (j : ℕ) :
    (((MvPolynomial.finSuccEquiv ℝ d) P).coeff j).totalDegree ≤ P.totalDegree := by
  show (((MvPolynomial.finSuccEquiv ℝ d) P).coeff j).support.sup
      (fun s => s.sum fun _ e => e) ≤ P.totalDegree
  refine Finset.sup_le fun s hs => ?_
  rw [MvPolynomial.mem_support_iff] at hs
  have hs' : P.coeff (Finsupp.cons j s) ≠ 0 := by
    rw [← MvPolynomial.finSuccEquiv_coeff_coeff s P j]
    exact hs
  have hmem : Finsupp.cons j s ∈ P.support := by
    rwa [MvPolynomial.mem_support_iff]
  have h := MvPolynomial.le_totalDegree hmem
  rw [Finsupp.sum_cons] at h
  omega

/-- Removing `1` from one exponent does not increase the degree sum of an exponent vector. -/
theorem finsupp_tsub_sum_le {d : ℕ} (s : Fin d →₀ ℕ) (i : Fin d) :
    ((s - Finsupp.single i 1).sum fun _ e => e) ≤ s.sum fun _ e => e := by
  set t : Fin d →₀ ℕ := s - Finsupp.single i 1 with ht
  show (t.sum fun _ e => e) ≤ s.sum fun _ e => e
  rw [Finsupp.sum, Finsupp.sum]
  calc ∑ j ∈ t.support, (t j)
      ≤ ∑ j ∈ t.support, (s j) :=
        Finset.sum_le_sum fun j _ => by rw [ht, Finsupp.tsub_apply]; exact Nat.sub_le _ _
    _ ≤ ∑ j ∈ s.support, (s j) := by
        refine Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_
        · intro j hj
          rw [Finsupp.mem_support_iff] at hj ⊢
          intro h0
          exact hj (by rw [ht, Finsupp.tsub_apply, h0]; simp)
        · intro j _ _; exact Nat.zero_le _

/-- The `pderiv` of a polynomial does not raise the total degree. -/
theorem totalDegree_pderiv_le {d : ℕ} (P : MvPolynomial (Fin d) ℝ) (i : Fin d) :
    (MvPolynomial.pderiv i P).totalDegree ≤ P.totalDegree := by
  conv_lhs => rw [MvPolynomial.as_sum P]
  rw [map_sum]
  refine (MvPolynomial.totalDegree_finsetSum _ _).trans ?_
  refine Finset.sup_le fun s hs => ?_
  rw [MvPolynomial.pderiv_monomial]
  exact (MvPolynomial.totalDegree_monomial_le _ _).trans
    ((finsupp_tsub_sum_le s i).trans (MvPolynomial.le_totalDegree hs))

/-- Iterated `pderiv` does not raise the total degree. -/
theorem totalDegree_iterate_pderiv_le {d : ℕ} (P : MvPolynomial (Fin d) ℝ) (i : Fin d) (k : ℕ) :
    (((MvPolynomial.pderiv i)^[k]) P).totalDegree ≤ P.totalDegree := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ_apply']
    exact (totalDegree_pderiv_le _ i).trans ih

/-! ## The degree of a product and of a resultant -/

/-- The total degree of a product is at most the sum of the total degrees. -/
theorem totalDegree_prod_le {d : ℕ} {σ : Type*} [Fintype σ]
    (f : σ → MvPolynomial (Fin d) ℝ) :
    (∏ i, f i).totalDegree ≤ ∑ i, (f i).totalDegree := by
  have key : ∀ s : Finset σ, (∏ i ∈ s, f i).totalDegree ≤ ∑ i ∈ s, (f i).totalDegree := by
    intro s
    induction s using Finset.induction with
    | empty => simp
    | insert a s ha ih =>
      rw [Finset.prod_insert ha, Finset.sum_insert ha]
      exact (MvPolynomial.totalDegree_mul _ _).trans (Nat.add_le_add_left ih _)
  calc (∏ i, f i).totalDegree ≤ ∑ i, (f i).totalDegree := key Finset.univ

/-- Every entry of the Sylvester matrix is a coefficient of `f` or of `g`. -/
theorem totalDegree_sylvester_entry_le {d : ℕ} (f g : Polynomial (MvPolynomial (Fin d) ℝ))
    (D m n : ℕ) (hf : ∀ j, (f.coeff j).totalDegree ≤ D) (hg : ∀ j, (g.coeff j).totalDegree ≤ D)
    (i j : Fin (m + n)) : (((Polynomial.sylvester f g m n) i j)).totalDegree ≤ D := by
  rw [Polynomial.sylvester, Matrix.of_apply]
  simp only [Fin.addCases]
  split_ifs <;> first
    | exact hf _
    | exact hg _
    | (simp; try (exact hf _); try (exact hg _))

/-- The action of a unit of `ℤ` (i.e. `±1`) does not raise the total degree. -/
theorem totalDegree_units_smul_le {d : ℕ} (u : ℤˣ) (p : MvPolynomial (Fin d) ℝ) :
    (u • p).totalDegree ≤ p.totalDegree := by
  rw [Units.smul_def]
  rcases Int.units_eq_one_or u with h | h
  · rw [h, Units.val_one, one_zsmul]
  · rw [h, Units.val_neg, Units.val_one, neg_one_zsmul, MvPolynomial.totalDegree_neg]

/-- The resultant does not raise the total degree beyond `(m + n) * D`. -/
theorem totalDegree_resultant_le {d : ℕ} (f g : Polynomial (MvPolynomial (Fin d) ℝ))
    (m n D : ℕ) (hf : ∀ j, (f.coeff j).totalDegree ≤ D)
    (hg : ∀ j, (g.coeff j).totalDegree ≤ D) :
    (f.resultant g m n).totalDegree ≤ (m + n) * D := by
  rw [Polynomial.resultant, Matrix.det_apply]
  refine (MvPolynomial.totalDegree_finsetSum _ _).trans ?_
  refine Finset.sup_le fun σ _ => ?_
  refine (totalDegree_units_smul_le (Equiv.Perm.sign σ)
    (∏ i, Polynomial.sylvester f g m n (σ i) i)).trans ?_
  calc (∏ i, Polynomial.sylvester f g m n (σ i) i).totalDegree
      ≤ ∑ i, (Polynomial.sylvester f g m n (σ i) i).totalDegree := totalDegree_prod_le _
    _ ≤ ∑ _i : Fin (m + n), D :=
        Finset.sum_le_sum fun i _ => totalDegree_sylvester_entry_le f g D m n hf hg (σ i) i
    _ = (m + n) * D := by simp [Finset.sum_const, Finset.card_univ, smul_eq_mul]

/-! ## The determinant of a small matrix -/

/-- The determinant of an `l × l` matrix whose entries have total degree at most `D` has total
degree at most `l * D`. -/
theorem totalDegree_det_le {d : ℕ} {l : ℕ} (M : Matrix (Fin l) (Fin l) (MvPolynomial (Fin d) ℝ))
    {D : ℕ} (hM : ∀ i j, (M i j).totalDegree ≤ D) : M.det.totalDegree ≤ l * D := by
  rw [Matrix.det_apply]
  refine (MvPolynomial.totalDegree_finsetSum _ _).trans ?_
  refine Finset.sup_le fun σ _ => ?_
  refine (totalDegree_units_smul_le (Equiv.Perm.sign σ) (∏ i, M (σ i) i)).trans ?_
  calc (∏ i, M (σ i) i).totalDegree
      ≤ ∑ i, (M (σ i) i).totalDegree := totalDegree_prod_le _
    _ ≤ ∑ _i : Fin l, D := Finset.sum_le_sum fun i _ => hM _ _
    _ = l * D := by simp [Finset.sum_const, Finset.card_univ, smul_eq_mul]

end Work.WilE4.CAD
