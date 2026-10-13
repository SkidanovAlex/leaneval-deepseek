/-
  annals_wilkies_conjecture, AREA E3, `Realify` (`ET`): the total-degree estimate for the
  realified system.

  `Work.WilE3.Realify.realifyRe N e Q` and `Work.WilE3.Realify.realifyIm N e Q` are the real and
  imaginary parts of `(Π_j (1 + t_j²))^N` times the complexified polynomial `Q` under the
  half-angle substitution `z_i ↦ u_i + i v_i`, `e^{ℓ_j} ↦ e_j y_j (1 + 2 i t_j - t_j²)/(1 + t_j²)`
  (`Realify/Defs.lean`).  They are support sums of the coefficientwise real/imaginary parts of
  `monoNum N e m`, and

  `deg (monoNum N e m) ≤ 3 ∑_i m_i + 3 ∑_j m_j + 2 ∑_j (N - m_j) ≤ 3 (∑ m) + 2 r N`,

  because the three factors of `monoNum` contribute respectively `≤ 1`, `≤ 3` and `≤ 2` per
  variable.  Since `∑ m ≤ deg Q` on the support of `Q`, this gives the degree bound
  `O (deg Q + r N)` used by the separable-chain Khovanskii bound.
-/
import Mathlib
import Submission.Work.WilE3.Realify.Defs
import Submission.Work.WilE3.Realify.rePoly_imPoly_totalDegree_le
import Submission.Work.WilE3.Realify.EvalMain

namespace Work.WilE3.Realify.ET

set_option autoImplicit false
noncomputable section

/-! ## §1. Degree bounds for the individual factors of `monoNum` -/

/-- The constant `i` has degree `0`. -/
theorem totalDegree_cI_le {k r : ℕ} : (cI (k := k) (r := r)).totalDegree = 0 := by
  simp only [cI]
  exact MvPolynomial.totalDegree_C _

/-- The variable `u_i` has degree `1`. -/
theorem totalDegree_cU_le {k r : ℕ} (i : Fin k) : (cU (k := k) (r := r) i).totalDegree = 1 := by
  simp only [cU]
  exact MvPolynomial.totalDegree_X _

/-- The variable `v_i` has degree `1`. -/
theorem totalDegree_cV_le {k r : ℕ} (i : Fin k) : (cV (k := k) (r := r) i).totalDegree = 1 := by
  simp only [cV]
  exact MvPolynomial.totalDegree_X _

/-- The variable `y_j` has degree `1`. -/
theorem totalDegree_cY_le {k r : ℕ} (j : Fin r) : (cY (k := k) (r := r) j).totalDegree = 1 := by
  simp only [cY]
  exact MvPolynomial.totalDegree_X _

/-- The variable `t_j` has degree `1`. -/
theorem totalDegree_cT_le {k r : ℕ} (j : Fin r) : (cT (k := k) (r := r) j).totalDegree = 1 := by
  simp only [cT]
  exact MvPolynomial.totalDegree_X _

/-- The complexified coordinate `u_i + i v_i` has degree `1`. -/
theorem totalDegree_cU_add_cI_mul_cV_le {k r : ℕ} (i : Fin k) :
    (cU (k := k) (r := r) i + cI * cV (k := k) (r := r) i).totalDegree ≤ 1 := by
  have hcV : (cI (k := k) (r := r) * cV (k := k) (r := r) i).totalDegree ≤ 1 := by
    refine le_trans (MvPolynomial.totalDegree_mul _ _) ?_
    simp [totalDegree_cI_le, totalDegree_cV_le]
  exact le_trans (MvPolynomial.totalDegree_add _ _)
    (max_le (le_of_eq (totalDegree_cU_le i)) hcV)

/-- The factor `1 + 2 i t_j - t_j² = (1 + i t_j)²` has degree `≤ 2`. -/
theorem totalDegree_cZ_le {k r : ℕ} (j : Fin r) : (cZ (k := k) (r := r) j).totalDegree ≤ 2 := by
  have hlin : (cI (k := k) (r := r) * cT (k := k) (r := r) j).totalDegree ≤ 1 := by
    refine le_trans (MvPolynomial.totalDegree_mul _ _) ?_
    simp [totalDegree_cI_le, totalDegree_cT_le]
  have hnum : ((2 : MvPolynomial (Sig k r) ℂ) * cI (k := k) (r := r)
      * cT (k := k) (r := r) j).totalDegree ≤ 2 := by
    have hsplit : (2 : MvPolynomial (Sig k r) ℂ) * cI (k := k) (r := r)
        * cT (k := k) (r := r) j
        = (cI (k := k) (r := r) * cT (k := k) (r := r) j)
          + (cI (k := k) (r := r) * cT (k := k) (r := r) j) := by ring
    rw [hsplit]
    exact le_trans (MvPolynomial.totalDegree_add _ _)
      (max_le (le_trans hlin (by norm_num)) (le_trans hlin (by norm_num)))
  have hsq : ((cT (k := k) (r := r) j) ^ 2).totalDegree ≤ 2 := by
    refine le_trans (MvPolynomial.totalDegree_pow _ _) ?_
    simp [totalDegree_cT_le]
  simp only [cZ]
  refine le_trans (MvPolynomial.totalDegree_sub _ _) (max_le ?_ hsq)
  exact le_trans (MvPolynomial.totalDegree_add _ _)
    (max_le (le_trans (le_of_eq MvPolynomial.totalDegree_one) (Nat.zero_le 2)) hnum)

/-- The clearing factor `1 + t_j²` has degree `≤ 2`. -/
theorem totalDegree_cW_le {k r : ℕ} (j : Fin r) : (cW (k := k) (r := r) j).totalDegree ≤ 2 := by
  have hsq : ((cT (k := k) (r := r) j) ^ 2).totalDegree ≤ 2 := by
    refine le_trans (MvPolynomial.totalDegree_pow _ _) ?_
    simp [totalDegree_cT_le]
  simp only [cW]
  exact le_trans (MvPolynomial.totalDegree_add _ _)
    (max_le (le_trans (le_of_eq MvPolynomial.totalDegree_one) (Nat.zero_le 2)) hsq)

/-- The numerator `e_j y_j (1 + 2 i t_j - t_j²)` has degree `≤ 3`. -/
theorem totalDegree_C_mul_cY_mul_cZ_le {k r : ℕ} (e : Fin r → ℝ) (j : Fin r) :
    (MvPolynomial.C (e j : ℂ) * cY (k := k) (r := r) j * cZ (k := k) (r := r) j).totalDegree
      ≤ 3 := by
  have hCY : (MvPolynomial.C (e j : ℂ) * cY (k := k) (r := r) j).totalDegree ≤ 1 := by
    refine le_trans (MvPolynomial.totalDegree_mul _ _) ?_
    simp [totalDegree_cY_le]
  calc (MvPolynomial.C (e j : ℂ) * cY (k := k) (r := r) j * cZ (k := k) (r := r) j).totalDegree
      ≤ (MvPolynomial.C (e j : ℂ) * cY (k := k) (r := r) j).totalDegree
          + (cZ (k := k) (r := r) j).totalDegree := MvPolynomial.totalDegree_mul _ _
    _ ≤ 1 + 2 := add_le_add hCY (totalDegree_cZ_le j)
    _ = 3 := by norm_num

/-! ## §2. Degree bounds for the three products in `monoNum` -/

/-- The `u`-part `Π_i (u_i + i v_i)^{m_i}` has degree at most `∑_i m_i`. -/
theorem totalDegree_prod_U_le {k r : ℕ} (m : (Fin k ⊕ Fin r) →₀ ℕ) :
    (∏ i : Fin k, (cU (k := k) (r := r) i + cI * cV (k := k) (r := r) i)
        ^ (m (Sum.inl i))).totalDegree ≤ ∑ i : Fin k, m (Sum.inl i) := by
  have hper : ∀ i : Fin k,
      ((cU (k := k) (r := r) i + cI * cV (k := k) (r := r) i) ^ (m (Sum.inl i))).totalDegree
        ≤ m (Sum.inl i) := by
    intro i
    refine le_trans (MvPolynomial.totalDegree_pow _ _) ?_
    exact le_trans (Nat.mul_le_mul_left (m (Sum.inl i)) (totalDegree_cU_add_cI_mul_cV_le i))
      (le_of_eq (Nat.mul_one _))
  refine le_trans (MvPolynomial.totalDegree_finsetProd (Finset.univ : Finset (Fin k))
    (fun i : Fin k => (cU (k := k) (r := r) i + cI * cV (k := k) (r := r) i)
      ^ (m (Sum.inl i)))) ?_
  apply Finset.sum_le_sum
  intro i _
  exact hper i

/-- The `t`-part `Π_j (e_j y_j (1 + 2 i t_j - t_j²))^{m_j}` has degree at most `3 ∑_j m_j`. -/
theorem totalDegree_prod_B_le {k r : ℕ} (e : Fin r → ℝ) (m : (Fin k ⊕ Fin r) →₀ ℕ) :
    (∏ j : Fin r, (MvPolynomial.C (e j : ℂ) * cY (k := k) (r := r) j
        * cZ (k := k) (r := r) j) ^ (m (Sum.inr j))).totalDegree
      ≤ 3 * ∑ j : Fin r, m (Sum.inr j) := by
  have hper : ∀ j : Fin r,
      ((MvPolynomial.C (e j : ℂ) * cY (k := k) (r := r) j * cZ (k := k) (r := r) j)
          ^ (m (Sum.inr j))).totalDegree ≤ 3 * m (Sum.inr j) := by
    intro j
    refine le_trans (MvPolynomial.totalDegree_pow _ _) ?_
    calc m (Sum.inr j) * (MvPolynomial.C (e j : ℂ) * cY (k := k) (r := r) j
            * cZ (k := k) (r := r) j).totalDegree
        ≤ m (Sum.inr j) * 3 := Nat.mul_le_mul_left _ (totalDegree_C_mul_cY_mul_cZ_le e j)
      _ = 3 * m (Sum.inr j) := by ring
  have hsum : (∑ j : Fin r, ((MvPolynomial.C (e j : ℂ) * cY (k := k) (r := r) j
      * cZ (k := k) (r := r) j) ^ (m (Sum.inr j))).totalDegree)
      ≤ ∑ j : Fin r, 3 * m (Sum.inr j) := by
    apply Finset.sum_le_sum
    intro j _
    exact hper j
  refine le_trans (MvPolynomial.totalDegree_finsetProd (Finset.univ : Finset (Fin r))
    (fun j : Fin r => (MvPolynomial.C (e j : ℂ) * cY (k := k) (r := r) j
      * cZ (k := k) (r := r) j) ^ (m (Sum.inr j)))) ?_
  exact le_trans hsum (le_of_eq (Finset.mul_sum Finset.univ
    (fun j : Fin r => m (Sum.inr j)) 3).symm)

/-- The clearing part `Π_j (1 + t_j²)^{N - m_j}` has degree at most `2 r N`. -/
theorem totalDegree_prod_W_le {k r : ℕ} (N : ℕ) (m : (Fin k ⊕ Fin r) →₀ ℕ) :
    (∏ j : Fin r, cW (k := k) (r := r) j ^ (N - m (Sum.inr j))).totalDegree ≤ 2 * r * N := by
  have hper : ∀ j : Fin r,
      (cW (k := k) (r := r) j ^ (N - m (Sum.inr j))).totalDegree ≤ 2 * N := by
    intro j
    refine le_trans (MvPolynomial.totalDegree_pow _ _) ?_
    exact le_trans
      (le_trans (Nat.mul_le_mul_left (N - m (Sum.inr j)) (totalDegree_cW_le j))
        (Nat.mul_le_mul_right 2 (Nat.sub_le N (m (Sum.inr j)))))
      (le_of_eq (by ring))
  have hsum : (∑ j : Fin r, (cW (k := k) (r := r) j ^ (N - m (Sum.inr j))).totalDegree)
      ≤ ∑ _j : Fin r, 2 * N := by
    apply Finset.sum_le_sum
    intro j _
    exact hper j
  have hcard : (∑ _j : Fin r, 2 * N) = r * (2 * N) := by simp
  refine le_trans (MvPolynomial.totalDegree_finsetProd (Finset.univ : Finset (Fin r))
    (fun j : Fin r => cW (k := k) (r := r) j ^ (N - m (Sum.inr j)))) ?_
  exact le_trans hsum (le_trans (le_of_eq hcard) (le_of_eq (by ring)))

/-! ## §3. The degree of `monoNum` -/

/-- The total exponent sum of `m` splits over the two summands of `Fin k ⊕ Fin r`. -/
theorem sum_split {k r : ℕ} (m : (Fin k ⊕ Fin r) →₀ ℕ) :
    (m.sum fun _ x => x)
      = (∑ i : Fin k, m (Sum.inl i)) + ∑ j : Fin r, m (Sum.inr j) := by
  rw [Finsupp.sum_fintype m (fun _ x => x) (fun i => rfl), Fintype.sum_sum_type]

/-- **Degree of the realification numerator**: the product `monoNum N e m` has total degree at
most `3 · (total exponent of m) + 2 r N`. -/
theorem monoNum_totalDegree_le_aux {k r : ℕ} (N : ℕ) (e : Fin r → ℝ)
    (m : (Fin k ⊕ Fin r) →₀ ℕ) :
    (monoNum (k := k) (r := r) N e m).totalDegree ≤ 3 * (m.sum fun _ x => x) + 2 * r * N := by
  have hm : (m.sum fun _ x => x)
      = (∑ i : Fin k, m (Sum.inl i)) + ∑ j : Fin r, m (Sum.inr j) := sum_split m
  have hA := totalDegree_prod_U_le m
  have hB := totalDegree_prod_B_le e m
  have hC := totalDegree_prod_W_le N m
  have hmain : (monoNum (k := k) (r := r) N e m).totalDegree
      ≤ (∏ i : Fin k, (cU (k := k) (r := r) i + cI * cV (k := k) (r := r) i)
            ^ (m (Sum.inl i))).totalDegree
        + (∏ j : Fin r, (MvPolynomial.C (e j : ℂ) * cY (k := k) (r := r) j
            * cZ (k := k) (r := r) j) ^ (m (Sum.inr j))).totalDegree
        + (∏ j : Fin r, cW (k := k) (r := r) j ^ (N - m (Sum.inr j))).totalDegree := by
    rw [monoNum]
    exact le_trans (MvPolynomial.totalDegree_mul _ _)
      (add_le_add (MvPolynomial.totalDegree_mul _ _) le_rfl)
  have h1 := le_trans hmain (Nat.add_le_add (Nat.add_le_add hA hB) hC)
  have h2 : (∑ i : Fin k, m (Sum.inl i)) + 3 * (∑ j : Fin r, m (Sum.inr j))
      ≤ 3 * ((∑ i : Fin k, m (Sum.inl i)) + ∑ j : Fin r, m (Sum.inr j)) := by
    have hS : (∑ i : Fin k, m (Sum.inl i)) ≤ 3 * ∑ i : Fin k, m (Sum.inl i) := by
      have h : (∑ i : Fin k, m (Sum.inl i)) * 3 = 3 * ∑ i : Fin k, m (Sum.inl i) := by ring
      have h1' : (∑ i : Fin k, m (Sum.inl i)) * 1 ≤ (∑ i : Fin k, m (Sum.inl i)) * 3 :=
        Nat.mul_le_mul_left _ (by norm_num)
      simpa [h] using h1'
    calc (∑ i : Fin k, m (Sum.inl i)) + 3 * (∑ j : Fin r, m (Sum.inr j))
        ≤ 3 * (∑ i : Fin k, m (Sum.inl i)) + 3 * (∑ j : Fin r, m (Sum.inr j)) :=
          Nat.add_le_add_right hS _
      _ = 3 * ((∑ i : Fin k, m (Sum.inl i)) + ∑ j : Fin r, m (Sum.inr j)) := by ring
  rw [hm]
  exact le_trans h1 (Nat.add_le_add_right h2 (2 * r * N))

/-! ## §4. Support sums and the main estimate -/

/-- If every term of a support sum of a polynomial has total degree at most `D`, so has the sum. -/
theorem totalDegree_supportSum_le {k r : ℕ} (Q : WilkiesDesign.E.EAPoly k r)
    (F : ((Fin k ⊕ Fin r) →₀ ℕ) → RPoly k r) (D : ℕ)
    (hD : ∀ m ∈ Q.support, (F m).totalDegree ≤ D) :
    (∑ m ∈ Q.support, Q.coeff m • F m).totalDegree ≤ D := by
  refine MvPolynomial.totalDegree_finsetSum_le (fun m hm => ?_)
  exact le_trans (MvPolynomial.totalDegree_smul_le (Q.coeff m) (F m)) (hD m hm)

/-- The degree of the real part of `monoNum N e m`, in terms of the exponent sum of `m`. -/
theorem totalDegree_rePoly_monoNum_le {k r : ℕ} (N : ℕ) (e : Fin r → ℝ)
    (m : (Fin k ⊕ Fin r) →₀ ℕ) (D : ℕ) (hm : (m.sum fun _ x => x) ≤ D) :
    (rePoly (monoNum (k := k) (r := r) N e m)).totalDegree ≤ 3 * D + 2 * r * N :=
  le_trans (rePoly_imPoly_totalDegree_le (monoNum (k := k) (r := r) N e m)).1
    (le_trans (monoNum_totalDegree_le_aux N e m)
      (Nat.add_le_add_right (Nat.mul_le_mul_left 3 hm) (2 * r * N)))

/-- The degree of the imaginary part of `monoNum N e m`, in terms of the exponent sum of `m`. -/
theorem totalDegree_imPoly_monoNum_le {k r : ℕ} (N : ℕ) (e : Fin r → ℝ)
    (m : (Fin k ⊕ Fin r) →₀ ℕ) (D : ℕ) (hm : (m.sum fun _ x => x) ≤ D) :
    (imPoly (monoNum (k := k) (r := r) N e m)).totalDegree ≤ 3 * D + 2 * r * N :=
  le_trans (rePoly_imPoly_totalDegree_le (monoNum (k := k) (r := r) N e m)).2
    (le_trans (monoNum_totalDegree_le_aux N e m)
      (Nat.add_le_add_right (Nat.mul_le_mul_left 3 hm) (2 * r * N)))

/-- Arithmetic: the clearing contribution `2 r N` is dominated by `3 r (N + 1)`. -/
theorem two_mul_mul_le_three_mul_mul_succ (r N : ℕ) : 2 * r * N ≤ 3 * r * (N + 1) := by
  calc 2 * r * N = 2 * (r * N) := by ring
    _ ≤ 3 * (r * N) := Nat.mul_le_mul_right (r * N) (by norm_num)
    _ ≤ 3 * (r * (N + 1)) := Nat.mul_le_mul_left 3 (Nat.mul_le_mul_left r (Nat.le_succ N))
    _ = 3 * r * (N + 1) := by ring

theorem totalDegree_realify_le {k r : ℕ} (N : ℕ) (e : Fin r → ℝ)
    (Q : WilkiesDesign.E.EAPoly k r) :
    (Work.WilE3.Realify.realifyRe N e Q).totalDegree ≤ 3 * Q.totalDegree + 3 * r * (N + 1) ∧
    (Work.WilE3.Realify.realifyIm N e Q).totalDegree ≤ 3 * Q.totalDegree + 3 * r * (N + 1) := by
  have harith : ∀ m ∈ Q.support,
      3 * Q.totalDegree + 2 * r * N ≤ 3 * Q.totalDegree + 3 * r * (N + 1) :=
    fun _ _ => Nat.add_le_add_left (two_mul_mul_le_three_mul_mul_succ r N) (3 * Q.totalDegree)
  constructor
  · rw [realifyRe_sum]
    refine totalDegree_supportSum_le Q
      (fun m => rePoly (monoNum (k := k) (r := r) N e m)) _ (fun m hm => ?_)
    exact le_trans (totalDegree_rePoly_monoNum_le N e m Q.totalDegree
      (MvPolynomial.le_totalDegree hm)) (harith m hm)
  · rw [realifyIm_sum]
    refine totalDegree_supportSum_le Q
      (fun m => imPoly (monoNum (k := k) (r := r) N e m)) _ (fun m hm => ?_)
    exact le_trans (totalDegree_imPoly_monoNum_le N e m Q.totalDegree
      (MvPolynomial.le_totalDegree hm)) (harith m hm)

end

end Work.WilE3.Realify.ET
