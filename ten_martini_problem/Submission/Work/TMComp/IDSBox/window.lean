import Mathlib
import Submission.Work.TMComp.IDSDefs

/-!
# The finite-volume eigenvalue count in a window

If `m` orthonormal vectors `ψ i` have residual `‖(A - E)ψ i‖₂ ≤ ε` for a Hermitian
matrix `A` and a number `E`, then at least `m (1 - (ε/ε')²)` eigenvalues of `A` lie
in `[E - ε', E + ε']` (with `ε' > 0`).

The proof expands `ψ i` in the orthonormal eigenbasis `hA.eigenvectorBasis`: writing
`c i j = ⟨b_j, ψ_i⟩`,

* Parseval gives `∑_j ‖c i j‖² = ‖ψ i‖² = 1`,
* the residual identity gives `∑_j ‖c i j‖² (λ_j - E)² = ‖(A - E)ψ i‖² ≤ ε²`,
* Bessel gives `∑_i ‖c i j‖² ≤ 1`.

Dropping the terms with `|λ_j - E| > ε'` from the second identity forces
`∑_{j ∈ window} ‖c i j‖² ≥ 1 - (ε/ε')²`; summing over `i` and using the third
inequality turns this into the desired count of eigenvalues in the window.  The two
spectral identities (the `L²` form of the spectral theorem) are proved here from
Mathlib's `eigenvectorBasis`.
-/

namespace Work.TMComp.IDSBox

open scoped BigOperators

/-- The norm of a linear combination in an orthonormal basis is the `ℓ²`-norm of its
coefficients: `∑ i, ‖a i‖ ^ 2 = ‖∑ i, a i • b i‖ ^ 2`. -/
lemma norm_sum_smul_orthonormal {ι : Type*} [Fintype ι] {V : Type*} [NormedAddCommGroup V]
    [InnerProductSpace ℂ V] (b : OrthonormalBasis ι ℂ V) (a : ι → ℂ) :
    ‖∑ i, a i • b i‖ ^ 2 = ∑ i, ‖a i‖ ^ 2 := by
  rw [← b.sum_sq_norm_inner_right (∑ i, a i • b i)]
  refine Finset.sum_congr rfl fun k _ => ?_
  have h : inner ℂ (b k) (∑ i, a i • b i) = a k := by
    rw [inner_sum, Finset.sum_eq_single k]
    · rw [inner_smul_right, b.inner_eq_one, mul_one]
    · intro i _ hi
      rw [inner_smul_right, b.inner_eq_zero (Ne.symm hi), mul_zero]
    · intro hk; exact absurd (Finset.mem_univ k) hk
  rw [h]

/-- `‖z * (r : ℂ)‖ ^ 2 = ‖z‖ ^ 2 * r ^ 2` for a complex number `z` and a real `r`. -/
lemma eigNormSq_mul_ofReal (z : ℂ) (r : ℝ) : ‖z * (r : ℂ)‖ ^ 2 = ‖z‖ ^ 2 * r ^ 2 := by
  rw [Complex.sq_norm, Complex.normSq_mul, Complex.normSq_ofReal, ← Complex.sq_norm z]
  ring

/-- Expansion of a vector in the orthonormal eigenbasis of a Hermitian matrix, together
with Parseval's identity for the coefficients. -/
lemma eigExpansion {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) (hA : A.IsHermitian)
    (ψ : Fin n → ℂ) :
    (∀ l : Fin n, ψ l = ∑ j : Fin n,
        inner ℂ (hA.eigenvectorBasis j) (WithLp.toLp 2 ψ) * (hA.eigenvectorBasis j).ofLp l) ∧
    (∑ j : Fin n, ‖inner ℂ (hA.eigenvectorBasis j) (WithLp.toLp 2 ψ)‖ ^ 2
      = ∑ l : Fin n, ‖ψ l‖ ^ 2) := by
  constructor
  · intro l
    have h := congrArg (fun (x : EuclideanSpace ℂ (Fin n)) => x.ofLp l)
      (hA.eigenvectorBasis.sum_repr' (WithLp.toLp 2 ψ))
    simpa using h.symm
  · rw [hA.eigenvectorBasis.sum_sq_norm_inner_right, EuclideanSpace.norm_sq_eq]

/-- The residual identity: the squared `ℓ²`-norm of `(A - E)ψ` equals the sum of
`‖⟨b_j, ψ⟩‖²` weighted by `(λ_j - E)²`, `λ_j` running over the eigenvalues of the
Hermitian matrix `A`. -/
lemma eigResidual {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) (hA : A.IsHermitian)
    {E : ℝ} (ψ : Fin n → ℂ) :
    (∑ l : Fin n, ‖(Matrix.mulVec A ψ) l - (E : ℂ) * ψ l‖ ^ 2)
      = ∑ j : Fin n, ‖inner ℂ (hA.eigenvectorBasis j) (WithLp.toLp 2 ψ)‖ ^ 2
          * (hA.eigenvalues j - E) ^ 2 := by
  classical
  set c : Fin n → ℂ := fun j => inner ℂ (hA.eigenvectorBasis j) (WithLp.toLp 2 ψ) with hc
  have hψ : ψ = ∑ j : Fin n, c j • (hA.eigenvectorBasis j).ofLp := by
    funext l
    rw [Finset.sum_apply]
    simp only [Pi.smul_apply, smul_eq_mul]
    exact (eigExpansion A hA ψ).1 l
  have hone : ∀ l : Fin n, (Matrix.mulVec A ψ) l
      = ∑ j : Fin n, (c j * ((hA.eigenvalues j : ℝ) : ℂ))
          * (hA.eigenvectorBasis j).ofLp l := by
    intro l
    conv_lhs => rw [hψ]
    rw [Matrix.mulVec_sum]
    simp only [Finset.sum_apply]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [Matrix.mulVec_smul, Pi.smul_apply, smul_eq_mul,
      hA.mulVec_eigenvectorBasis j, Complex.real_smul]
    ring
  have hpt : ∀ l : Fin n, (Matrix.mulVec A ψ) l - (E : ℂ) * ψ l
      = ∑ j : Fin n, (c j * (((hA.eigenvalues j : ℝ) : ℂ) - (E : ℂ)))
          * (hA.eigenvectorBasis j).ofLp l := by
    intro l
    rw [hone l, hψ]
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  have htoLp : WithLp.toLp 2 (fun l => (Matrix.mulVec A ψ) l - (E : ℂ) * ψ l)
      = ∑ j : Fin n, (c j * (((hA.eigenvalues j : ℝ) : ℂ) - (E : ℂ)))
          • hA.eigenvectorBasis j := by
    apply WithLp.ofLp_injective
    simp only [WithLp.ofLp_sum, WithLp.ofLp_smul]
    funext l
    rw [Finset.sum_apply]
    simp only [Pi.smul_apply, smul_eq_mul]
    exact hpt l
  calc ∑ l : Fin n, ‖(Matrix.mulVec A ψ) l - (E : ℂ) * ψ l‖ ^ 2
      = ‖WithLp.toLp 2 (fun l => (Matrix.mulVec A ψ) l - (E : ℂ) * ψ l)‖ ^ 2 := by
        simp [EuclideanSpace.norm_sq_eq]
    _ = ‖∑ j : Fin n, (c j * (((hA.eigenvalues j : ℝ) : ℂ) - (E : ℂ)))
          • hA.eigenvectorBasis j‖ ^ 2 := by rw [htoLp]
    _ = ∑ j : Fin n, ‖c j * (((hA.eigenvalues j : ℝ) : ℂ) - (E : ℂ))‖ ^ 2 :=
        norm_sum_smul_orthonormal (hA.eigenvectorBasis)
          (fun j => c j * (((hA.eigenvalues j : ℝ) : ℂ) - (E : ℂ)))
    _ = ∑ j : Fin n, ‖inner ℂ (hA.eigenvectorBasis j) (WithLp.toLp 2 ψ)‖ ^ 2
          * (hA.eigenvalues j - E) ^ 2 := by
        refine Finset.sum_congr rfl fun j _ => ?_
        have hcast : (((hA.eigenvalues j : ℝ) : ℂ) - (E : ℂ))
            = ((hA.eigenvalues j - E : ℝ) : ℂ) := by push_cast; ring
        rw [hcast, eigNormSq_mul_ofReal]

/-- Bessel's inequality for the coefficients of the eigenbasis along an orthonormal
family `ψ i`. -/
lemma eigBessel {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) (hA : A.IsHermitian)
    {m : ℕ} (ψ : Fin m → Fin n → ℂ)
    (horth : ∀ i j : Fin m,
      (∑ k : Fin n, ψ i k * (starRingEnd ℂ) (ψ j k)) = if i = j then 1 else 0)
    (j : Fin n) :
    ∑ i : Fin m, ‖inner ℂ (hA.eigenvectorBasis j) (WithLp.toLp 2 (ψ i))‖ ^ 2 ≤ 1 := by
  have horth' : Orthonormal ℂ (fun i : Fin m => WithLp.toLp 2 (ψ i)) := by
    rw [orthonormal_iff_ite]
    intro i j
    simp only [PiLp.inner_apply, RCLike.inner_apply]
    simpa [eq_comm] using horth j i
  have hb := Orthonormal.sum_inner_products_le (x := hA.eigenvectorBasis j) horth'
    (s := Finset.univ)
  rw [hA.eigenvectorBasis.norm_eq_one j, one_pow] at hb
  convert hb using 2 with i
  rw [← inner_conj_symm, RCLike.norm_conj]

theorem window {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) (hA : A.IsHermitian)
    {E ε ε' : ℝ} (hε : 0 ≤ ε) (hε' : 0 < ε') {m : ℕ} (ψ : Fin m → Fin n → ℂ)
    (horth : ∀ i j : Fin m,
      (∑ k : Fin n, ψ i k * (starRingEnd ℂ) (ψ j k)) = if i = j then 1 else 0)
    (hres : ∀ i : Fin m,
      (∑ k : Fin n, ‖(Matrix.mulVec A (ψ i)) k - E * ψ i k‖ ^ 2) ≤ ε ^ 2) :
    ((Finset.univ.filter (fun k : Fin n => |hA.eigenvalues k - E| ≤ ε')).card : ℝ)
      ≥ (m : ℝ) * (1 - (ε / ε') ^ 2) := by
  classical
  set S : Finset (Fin n) := Finset.univ.filter (fun k => |hA.eigenvalues k - E| ≤ ε') with hS
  set T : Finset (Fin n) :=
    Finset.univ.filter (fun k => ¬ |hA.eigenvalues k - E| ≤ ε') with hT
  set c : Fin m → Fin n → ℝ :=
    fun i j => ‖inner ℂ (hA.eigenvectorBasis j) (WithLp.toLp 2 (ψ i))‖ ^ 2 with hc
  have hc0 : ∀ i j, 0 ≤ c i j := by
    intro i j
    exact sq_nonneg (‖inner ℂ (hA.eigenvectorBasis j) (WithLp.toLp 2 (ψ i))‖ : ℝ)
  -- the `ψ i` are unit vectors
  have hpsi : ∀ i : Fin m, ∑ l : Fin n, ‖ψ i l‖ ^ 2 = 1 := by
    intro i
    have h : (∑ l : Fin n, ψ i l * (starRingEnd ℂ) (ψ i l)) = 1 := by
      simpa using horth i i
    apply Complex.ofReal_injective
    push_cast
    rw [← h]
    exact Finset.sum_congr rfl fun l _ => (RCLike.mul_conj (ψ i l)).symm
  -- Parseval: the rows of the coefficient matrix have squared norm `1`
  have hrow : ∀ i : Fin m, ∑ j : Fin n, c i j = 1 := by
    intro i
    have h1 := (eigExpansion A hA (ψ i)).2
    rw [show (∑ j : Fin n, c i j)
        = ∑ j : Fin n, ‖inner ℂ (hA.eigenvectorBasis j) (WithLp.toLp 2 (ψ i))‖ ^ 2
        from Finset.sum_congr rfl fun j _ => rfl, h1, hpsi i]
  -- the residual identity, transferred to `c`
  have hresid : ∀ i : Fin m, ∑ j : Fin n, c i j * (hA.eigenvalues j - E) ^ 2 ≤ ε ^ 2 := by
    intro i
    have h1 := eigResidual A hA (E := E) (ψ i)
    rw [show (∑ j : Fin n, c i j * (hA.eigenvalues j - E) ^ 2)
        = ∑ l : Fin n, ‖(Matrix.mulVec A (ψ i)) l - (E : ℂ) * ψ i l‖ ^ 2 from by
      rw [h1]]
    exact hres i
  -- Bessel: the columns of the coefficient matrix have squared norm at most `1`
  have hcol : ∀ j : Fin n, ∑ i : Fin m, c i j ≤ 1 := by
    intro j
    exact eigBessel A hA ψ horth j
  have hmemT : ∀ j : Fin n, j ∈ T ↔ ¬ (|hA.eigenvalues j - E| ≤ ε') := by
    intro j
    rw [hT]
    simp
  -- each row has mass at least `1 - (ε/ε')²` inside the window
  have hkey : ∀ i : Fin m, 1 - (ε / ε') ^ 2 ≤ ∑ j ∈ S, c i j := by
    intro i
    have hsplit : (∑ j ∈ S, c i j) + (∑ j ∈ T, c i j) = ∑ j : Fin n, c i j := by
      have h := Finset.sum_filter_add_sum_filter_not (Finset.univ : Finset (Fin n))
        (fun k => |hA.eigenvalues k - E| ≤ ε') (fun k => c i k)
      simpa [hS, hT] using h
    have hbnd : ∑ j ∈ T, c i j ≤ (ε / ε') ^ 2 := by
      have hsq : ∀ j ∈ T, ε' ^ 2 ≤ (hA.eigenvalues j - E) ^ 2 := by
        intro j hj
        have hp : ¬ (|hA.eigenvalues j - E| ≤ ε') := (hmemT j).mp hj
        have hlt : ε' < |hA.eigenvalues j - E| := lt_of_not_ge hp
        have h2 := sq_lt_sq.mpr (show |ε'| < |hA.eigenvalues j - E| by
          rwa [abs_of_pos hε'])
        linarith
      have hstep : ∀ j ∈ T, c i j ≤ c i j * (hA.eigenvalues j - E) ^ 2 / ε' ^ 2 := by
        intro j hj
        have h2 := hsq j hj
        have hpos : (0 : ℝ) < ε' ^ 2 := by positivity
        have hle1 : (1 : ℝ) ≤ (hA.eigenvalues j - E) ^ 2 / ε' ^ 2 :=
          (one_le_div hpos).mpr h2
        calc c i j = c i j * 1 := by ring
          _ ≤ c i j * ((hA.eigenvalues j - E) ^ 2 / ε' ^ 2) :=
              mul_le_mul_of_nonneg_left hle1 (hc0 i j)
          _ = c i j * (hA.eigenvalues j - E) ^ 2 / ε' ^ 2 := by ring
      calc ∑ j ∈ T, c i j
          ≤ ∑ j ∈ T, c i j * (hA.eigenvalues j - E) ^ 2 / ε' ^ 2 :=
            Finset.sum_le_sum hstep
        _ = (∑ j ∈ T, c i j * (hA.eigenvalues j - E) ^ 2) / ε' ^ 2 := by
            rw [Finset.sum_div]
        _ ≤ (∑ j : Fin n, c i j * (hA.eigenvalues j - E) ^ 2) / ε' ^ 2 := by
            apply div_le_div_of_nonneg_right _ (by positivity)
            exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ T)
              (fun j _ _ => mul_nonneg (hc0 i j) (sq_nonneg _))
        _ ≤ ε ^ 2 / ε' ^ 2 :=
            div_le_div_of_nonneg_right (hresid i) (by positivity)
        _ = (ε / ε') ^ 2 := by rw [div_pow]
    have h := hrow i
    linarith
  have hlow : (m : ℝ) * (1 - (ε / ε') ^ 2) ≤ ∑ i : Fin m, ∑ j ∈ S, c i j := by
    have h := Finset.sum_le_sum (s := Finset.univ) (fun i _ => hkey i)
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at h
    exact h
  have hhigh : ∑ i : Fin m, ∑ j ∈ S, c i j ≤ (S.card : ℝ) := by
    rw [Finset.sum_comm]
    calc ∑ j ∈ S, ∑ i : Fin m, c i j ≤ ∑ j ∈ S, (1 : ℝ) :=
          Finset.sum_le_sum (fun j _ => hcol j)
      _ = (S.card : ℝ) := by simp [Finset.sum_const, nsmul_eq_mul]
  have := le_trans hlow hhigh
  simpa [hS] using this

end Work.TMComp.IDSBox
