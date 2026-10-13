import Mathlib
import Submission.Work.WilE3.Realify.Defs

namespace Work.WilE3.Realify

set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section
open Classical

open MvPolynomial

variable {k r : ℕ}

/-! ## Degree of the elementary factors of `monoNum`

`monoNum N e m` is a product of three families of factors:
* `∏ i, (cU i + cI * cV i) ^ (m (inl i))`, each base of total degree `≤ 1`;
* `∏ j, (C (e j) * cY j * cZ j) ^ (m (inr j))`, each base of total degree `≤ 3`;
* `∏ j, (cW j) ^ (N - m (inr j))`, each base of total degree `≤ 2`.

We bound the total degree of each family separately. -/

lemma totalDegree_cI : (cI (k := k) (r := r)).totalDegree = 0 := by
  rw [cI, totalDegree_C]

lemma totalDegree_two : (2 : MvPolynomial (Sig k r) ℂ).totalDegree = 0 := by
  rw [show (2 : MvPolynomial (Sig k r) ℂ) = C (2 : ℂ) from by
    rw [show (2 : MvPolynomial (Sig k r) ℂ) = algebraMap ℂ (MvPolynomial (Sig k r) ℂ) (2 : ℂ)
          from (map_natCast _ 2).symm]
    rfl, totalDegree_C]

lemma totalDegree_cT (j : Fin r) : (cT (k := k) j).totalDegree = 1 := by
  rw [cT, totalDegree_X]

lemma totalDegree_cY (j : Fin r) : (cY (k := k) j).totalDegree = 1 := by
  rw [cY, totalDegree_X]

lemma totalDegree_two_mul_cI : (2 * cI : MvPolynomial (Sig k r) ℂ).totalDegree ≤ 0 := by
  calc (2 * cI : MvPolynomial (Sig k r) ℂ).totalDegree
      ≤ (2 : MvPolynomial (Sig k r) ℂ).totalDegree + cI.totalDegree := totalDegree_mul _ _
    _ ≤ 0 + 0 := add_le_add (le_of_eq totalDegree_two) (le_of_eq totalDegree_cI)
    _ = 0 := by norm_num

/-- `cU i + cI * cV i` has total degree `≤ 1`. -/
lemma totalDegree_cU_add_cI_cV (i : Fin k) :
    (cU (k := k) (r := r) i + cI * cV i).totalDegree ≤ 1 := by
  rw [cU, cV]
  calc (X (Sum.inl (Fin.castAdd k i)) + cI * X (Sum.inl (Fin.natAdd k i))).totalDegree
      ≤ max (X (Sum.inl (Fin.castAdd k i)) : MvPolynomial (Sig k r) ℂ).totalDegree
            (cI * X (Sum.inl (Fin.natAdd k i))).totalDegree := totalDegree_add _ _
    _ ≤ max 1 1 := max_le_max (le_of_eq (totalDegree_X _))
          (by calc (cI * X (Sum.inl (Fin.natAdd k i))).totalDegree
                    ≤ cI.totalDegree
                      + (X (Sum.inl (Fin.natAdd k i)) : MvPolynomial (Sig k r) ℂ).totalDegree :=
                  totalDegree_mul _ _
                _ ≤ 0 + 1 := add_le_add (le_of_eq totalDegree_cI) (le_of_eq (totalDegree_X _))
                _ = 1 := by norm_num)
    _ = 1 := max_self 1

/-- `cZ j = 1 + 2 i t_j - t_j²` has total degree `≤ 2`. -/
lemma totalDegree_cZ (j : Fin r) : (cZ (k := k) j).totalDegree ≤ 2 := by
  have h1 : (1 + 2 * cI * cT j : MvPolynomial (Sig k r) ℂ).totalDegree ≤ 1 := by
    calc (1 + 2 * cI * cT j : MvPolynomial (Sig k r) ℂ).totalDegree
        ≤ max (1 : MvPolynomial (Sig k r) ℂ).totalDegree
            (2 * cI * cT j).totalDegree := totalDegree_add _ _
      _ ≤ max 0 1 := max_le_max (le_of_eq totalDegree_one) (by
            calc (2 * cI * cT j : MvPolynomial (Sig k r) ℂ).totalDegree
                ≤ (2 * cI : MvPolynomial (Sig k r) ℂ).totalDegree
                  + (cT j).totalDegree := totalDegree_mul _ _
              _ ≤ 0 + 1 := add_le_add totalDegree_two_mul_cI (le_of_eq (totalDegree_cT j))
              _ = 1 := by norm_num)
      _ = 1 := max_eq_right (by norm_num)
  rw [cZ]
  calc (1 + 2 * cI * cT j - cT j ^ 2 : MvPolynomial (Sig k r) ℂ).totalDegree
      ≤ max (1 + 2 * cI * cT j : MvPolynomial (Sig k r) ℂ).totalDegree
          (cT j ^ 2).totalDegree := totalDegree_sub _ _
    _ ≤ max 1 2 := max_le_max h1 (by
          calc (cT j ^ 2 : MvPolynomial (Sig k r) ℂ).totalDegree
              ≤ 2 * (cT j).totalDegree := totalDegree_pow _ _
            _ ≤ 2 * 1 := Nat.mul_le_mul_left 2 (le_of_eq (totalDegree_cT j))
            _ = 2 := by norm_num)
    _ = 2 := max_eq_right (by norm_num)

/-- `cW j = 1 + t_j²` has total degree `≤ 2`. -/
lemma totalDegree_cW (j : Fin r) : (cW (k := k) j).totalDegree ≤ 2 := by
  rw [cW]
  calc (1 + cT j ^ 2 : MvPolynomial (Sig k r) ℂ).totalDegree
      ≤ max (1 : MvPolynomial (Sig k r) ℂ).totalDegree (cT j ^ 2).totalDegree :=
        totalDegree_add _ _
    _ ≤ max 0 2 := max_le_max (le_of_eq totalDegree_one) (by
          calc (cT j ^ 2 : MvPolynomial (Sig k r) ℂ).totalDegree
              ≤ 2 * (cT j).totalDegree := totalDegree_pow _ _
            _ ≤ 2 * 1 := Nat.mul_le_mul_left 2 (le_of_eq (totalDegree_cT j))
            _ = 2 := by norm_num)
    _ = 2 := max_eq_right (by norm_num)

/-- `C (e j) * cY j * cZ j` has total degree `≤ 3`. -/
lemma totalDegree_C_mul_cY_mul_cZ (e : Fin r → ℝ) (j : Fin r) :
    ((C (e j : ℂ) : MvPolynomial (Sig k r) ℂ) * cY j * cZ j).totalDegree ≤ 3 := by
  calc ((C (e j : ℂ) : MvPolynomial (Sig k r) ℂ) * cY j * cZ j).totalDegree
      ≤ ((C (e j : ℂ) : MvPolynomial (Sig k r) ℂ) * cY j).totalDegree + (cZ j).totalDegree :=
        totalDegree_mul _ _
    _ ≤ ((C (e j : ℂ) : MvPolynomial (Sig k r) ℂ).totalDegree + (cY j).totalDegree)
          + (cZ j).totalDegree := add_le_add (totalDegree_mul _ _) le_rfl
    _ ≤ (0 + 1) + 2 := add_le_add
        (add_le_add (le_of_eq (totalDegree_C _)) (le_of_eq (totalDegree_cY j)))
        (totalDegree_cZ j)
    _ = 3 := by norm_num

/-! ## Degree of the three product families -/

/-- The `u/v` family of `monoNum` has total degree `≤ ∑ᵢ m (inl i)`. -/
lemma totalDegree_monoNum_prodUV (m : (Fin k ⊕ Fin r) →₀ ℕ) :
    (∏ i : Fin k, (cU (k := k) (r := r) i + cI * cV i) ^ (m (Sum.inl i))).totalDegree
      ≤ ∑ i : Fin k, m (Sum.inl i) := by
  calc (∏ i : Fin k, (cU i + cI * cV i) ^ (m (Sum.inl i))).totalDegree
      ≤ ∑ i : Fin k, ((cU i + cI * cV i) ^ (m (Sum.inl i)) :
          MvPolynomial (Sig k r) ℂ).totalDegree := totalDegree_finsetProd _ _
    _ ≤ ∑ i : Fin k, m (Sum.inl i) := Finset.sum_le_sum fun i _ =>
        calc ((cU i + cI * cV i) ^ (m (Sum.inl i)) : MvPolynomial (Sig k r) ℂ).totalDegree
            ≤ (m (Sum.inl i)) * (cU i + cI * cV i).totalDegree := totalDegree_pow _ _
          _ ≤ (m (Sum.inl i)) * 1 := Nat.mul_le_mul_left _ (totalDegree_cU_add_cI_cV i)
          _ = m (Sum.inl i) := Nat.mul_one _

/-- A generic bound on the total degree of a product of powers: if every factor `f i` has total
degree `≤ d`, then `∏ i ∈ s, f i ^ (n i)` has total degree `≤ ∑ i ∈ s, n i * d`. -/
lemma totalDegree_finsetProd_pow_le {ι : Type*} {σ : Type*} [DecidableEq σ]
    (s : Finset ι) (f : ι → MvPolynomial σ ℂ) (n : ι → ℕ) (d : ℕ)
    (hf : ∀ i ∈ s, (f i).totalDegree ≤ d) :
    (s.prod fun i => (f i) ^ (n i)).totalDegree ≤ ∑ i ∈ s, n i * d := by
  calc (s.prod fun i => (f i) ^ (n i)).totalDegree
      ≤ ∑ i ∈ s, ((f i) ^ (n i)).totalDegree := totalDegree_finsetProd _ _
    _ ≤ ∑ i ∈ s, n i * d := Finset.sum_le_sum fun i hi =>
        (totalDegree_pow (f i) (n i)).trans (Nat.mul_le_mul_left _ (hf i hi))

/-- The `y/t` family of `monoNum` has total degree `≤ ∑ⱼ 3 * m (inr j)`. -/
lemma totalDegree_monoNum_prodYT (e : Fin r → ℝ) (m : (Fin k ⊕ Fin r) →₀ ℕ) :
    (∏ j : Fin r, ((C (e j : ℂ) : MvPolynomial (Sig k r) ℂ) * cY j * cZ j) ^
        (m (Sum.inr j))).totalDegree
      ≤ ∑ j : Fin r, m (Sum.inr j) * 3 :=
  totalDegree_finsetProd_pow_le Finset.univ
    (fun j : Fin r => (C (e j : ℂ) : MvPolynomial (Sig k r) ℂ) * cY j * cZ j)
    (fun j : Fin r => m (Sum.inr j)) 3
    (fun j _ => totalDegree_C_mul_cY_mul_cZ e j)

/-- The clearing family of `monoNum` has total degree `≤ ∑ⱼ 2 * (N - m (inr j))`. -/
lemma totalDegree_monoNum_prodW (N : ℕ) (m : (Fin k ⊕ Fin r) →₀ ℕ) :
    (∏ j : Fin r, (cW (k := k) (r := r) j) ^ (N - m (Sum.inr j))).totalDegree
      ≤ ∑ j : Fin r, (N - m (Sum.inr j)) * 2 := by
  calc (∏ j : Fin r, (cW j) ^ (N - m (Sum.inr j))).totalDegree
      ≤ ∑ j : Fin r, ((cW j) ^ (N - m (Sum.inr j)) : MvPolynomial (Sig k r) ℂ).totalDegree :=
        totalDegree_finsetProd _ _
    _ ≤ ∑ j : Fin r, (N - m (Sum.inr j)) * 2 := Finset.sum_le_sum fun j _ =>
        calc ((cW j) ^ (N - m (Sum.inr j)) : MvPolynomial (Sig k r) ℂ).totalDegree
            ≤ (N - m (Sum.inr j)) * (cW j).totalDegree := totalDegree_pow _ _
          _ ≤ (N - m (Sum.inr j)) * 2 := Nat.mul_le_mul_left _ (totalDegree_cW j)
          _ = (N - m (Sum.inr j)) * 2 := rfl

/-! ## The numerical inequality -/

/-- The arithmetic inequality behind the bound: the sum of the three degree bounds is at most
`∑ m + 2 ∑_{inr} m + 2 r N`. -/
lemma monoNum_arith (N : ℕ) (m : (Fin k ⊕ Fin r) →₀ ℕ) :
    (∑ i : Fin k, m (Sum.inl i)) + (∑ j : Fin r, m (Sum.inr j) * 3)
      + (∑ j : Fin r, (N - m (Sum.inr j)) * 2)
    ≤ (m.sum fun _ e => e) + 2 * (∑ j : Fin r, m (Sum.inr j)) + 2 * r * N := by
  have hsum : (m.sum fun _ e => e)
      = (∑ i : Fin k, m (Sum.inl i)) + ∑ j : Fin r, m (Sum.inr j) := by
    rw [Finsupp.sum_fintype _ _ (fun a => rfl)]
    exact Fintype.sum_sum_type fun a => m a
  have h3 : (∑ j : Fin r, m (Sum.inr j) * 3) = (∑ j : Fin r, m (Sum.inr j)) * 3 :=
    (Finset.sum_mul _ _ _).symm
  have hC : (∑ j : Fin r, (N - m (Sum.inr j)) * 2) ≤ 2 * r * N := by
    calc (∑ j : Fin r, (N - m (Sum.inr j)) * 2) ≤ ∑ j : Fin r, N * 2 :=
          Finset.sum_le_sum fun j _ => Nat.mul_le_mul_right 2 (Nat.sub_le N (m (Sum.inr j)))
      _ = r * (N * 2) := by simp [Finset.sum_const, Finset.card_univ]
      _ = 2 * r * N := by ring
  rw [hsum, h3]
  omega

/-! ## The main bound -/

theorem monoNum_totalDegree_le {k r : ℕ} (N : ℕ) (e : Fin r → ℝ) (m : (Fin k ⊕ Fin r) →₀ ℕ) :
    (monoNum (k := k) (r := r) N e m).totalDegree ≤
      (m.sum fun _ e => e) + 2 * (∑ j : Fin r, m (Sum.inr j)) + 2 * r * N := by
  have key : (monoNum (k := k) (r := r) N e m).totalDegree
      ≤ (∑ i : Fin k, m (Sum.inl i)) + (∑ j : Fin r, m (Sum.inr j) * 3)
        + (∑ j : Fin r, (N - m (Sum.inr j)) * 2) := by
    rw [monoNum]
    calc ((∏ i : Fin k, (cU i + cI * cV i) ^ (m (Sum.inl i)))
            * (∏ j : Fin r, ((C (e j : ℂ) : MvPolynomial (Sig k r) ℂ) * cY j * cZ j) ^
                (m (Sum.inr j)))
            * (∏ j : Fin r, (cW j) ^ (N - m (Sum.inr j)))).totalDegree
        ≤ ((∏ i : Fin k, (cU i + cI * cV i) ^ (m (Sum.inl i)))
            * (∏ j : Fin r, ((C (e j : ℂ) : MvPolynomial (Sig k r) ℂ) * cY j * cZ j) ^
                (m (Sum.inr j)))).totalDegree
          + (∏ j : Fin r, (cW j) ^ (N - m (Sum.inr j))).totalDegree := totalDegree_mul _ _
      _ ≤ ((∏ i : Fin k, (cU i + cI * cV i) ^ (m (Sum.inl i))).totalDegree
            + (∏ j : Fin r, ((C (e j : ℂ) : MvPolynomial (Sig k r) ℂ) * cY j * cZ j) ^
                (m (Sum.inr j))).totalDegree)
          + (∏ j : Fin r, (cW j) ^ (N - m (Sum.inr j))).totalDegree :=
            add_le_add (totalDegree_mul _ _) le_rfl
      _ ≤ (∑ i : Fin k, m (Sum.inl i)) + (∑ j : Fin r, m (Sum.inr j) * 3)
            + (∑ j : Fin r, (N - m (Sum.inr j)) * 2) :=
            add_le_add (add_le_add (totalDegree_monoNum_prodUV m)
              (totalDegree_monoNum_prodYT e m)) (totalDegree_monoNum_prodW N m)
  exact le_trans key (monoNum_arith N m)

end

end Work.WilE3.Realify
