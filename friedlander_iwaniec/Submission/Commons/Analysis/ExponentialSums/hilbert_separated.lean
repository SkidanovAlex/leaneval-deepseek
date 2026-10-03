import Mathlib
import Submission.Commons.Analysis.ExponentialSums.selberg_hilbert_quad
import Submission.Commons.Analysis.ExponentialSums.sum_inv_sq_le_separated

namespace Commons.Analysis.ExponentialSums

open scoped BigOperators

noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def hilbU (lam : ι → ℝ) (i j : ι) : ℂ :=
  if i = j then 0 else ((lam i - lam j : ℝ) : ℂ)⁻¹

lemma hilbU_self (lam : ι → ℝ) (i : ι) : hilbU lam i i = 0 := by simp [hilbU]

lemma hilbU_of_ne (lam : ι → ℝ) {i j : ι} (h : i ≠ j) :
    hilbU lam i j = ((lam i - lam j : ℝ) : ℂ)⁻¹ := by simp [hilbU, h]

lemma hilbU_star (lam : ι → ℝ) (i j : ι) : star (hilbU lam i j) = hilbU lam i j := by
  by_cases h : i = j
  · subst h; simp [hilbU]
  · rw [hilbU_of_ne lam h]; simp

lemma hilbU_antisym (lam : ι → ℝ) (i j : ι) : hilbU lam i j = - hilbU lam j i := by
  by_cases h : i = j
  · subst h; simp [hilbU]
  · rw [hilbU_of_ne lam h, hilbU_of_ne lam (Ne.symm h)]
    have : ((lam i - lam j : ℝ) : ℂ) = - ((lam j - lam i : ℝ) : ℂ) := by push_cast; ring
    rw [this, inv_neg]

def L (lam : ι → ℝ) : EuclideanSpace ℂ ι →ₗ[ℂ] EuclideanSpace ℂ ι :=
  Matrix.toEuclideanLin (fun i j => hilbU lam i j)

lemma L_apply (lam : ι → ℝ) (z : EuclideanSpace ℂ ι) (i : ι) :
    (L lam z) i = ∑ j, hilbU lam i j * z j := rfl

lemma inner_L (lam : ι → ℝ) (x y : EuclideanSpace ℂ ι) :
    inner ℂ (L lam x) y = ∑ p : ι × ι, y p.1 * hilbU lam p.1 p.2 * star (x p.2) := by
  rw [show inner ℂ (L lam x) y = ∑ i, y i * star ((L lam x) i) from by rw [PiLp.inner_apply]; simp]
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl; intro i _
  rw [L_apply]
  rw [star_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl; intro j _
  rw [star_mul, hilbU_star]; ring

lemma inner_L' (lam : ι → ℝ) (x y : EuclideanSpace ℂ ι) :
    inner ℂ x (L lam y) = ∑ p : ι × ι, hilbU lam p.1 p.2 * y p.2 * star (x p.1) := by
  rw [show inner ℂ x (L lam y) = ∑ i, (L lam y) i * star (x i) from by rw [PiLp.inner_apply]; simp]
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl; intro i _
  rw [L_apply, Finset.sum_mul]

lemma L_skew (lam : ι → ℝ) (x y : EuclideanSpace ℂ ι) :
    inner ℂ (L lam x) y = - inner ℂ x (L lam y) := by
  rw [inner_L, inner_L', ← Finset.sum_neg_distrib]
  exact Fintype.sum_equiv (Equiv.prodComm ι ι) _ _
    (fun p => by
      rcases p with ⟨i, j⟩
      simp only [Equiv.prodComm_apply, Prod.swap_prod_mk]
      rw [hilbU_antisym lam j i]; ring)

def T (lam : ι → ℝ) : EuclideanSpace ℂ ι →ₗ[ℂ] EuclideanSpace ℂ ι := Complex.I • L lam

lemma T_apply (lam : ι → ℝ) (z : EuclideanSpace ℂ ι) :
    T lam z = Complex.I • (L lam z) := rfl

lemma T_symm (lam : ι → ℝ) : (T lam).IsSymmetric := by
  intro x y
  rw [T_apply, T_apply, inner_smul_left, inner_smul_right, L_skew lam x y]
  simp [Complex.conj_I]

theorem norm_apply_le_of_eigen_bound {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E]
    [InnerProductSpace 𝕜 E] [FiniteDimensional 𝕜 E] (S : E →ₗ[𝕜] E) (hS : S.IsSymmetric)
    {c : ℝ} (hc : 0 ≤ c)
    (heig : ∀ i : Fin (Module.finrank 𝕜 E), |hS.eigenvalues rfl i| ≤ c) (v : E) :
    ‖S v‖ ≤ c * ‖v‖ := by
  have hn : Module.finrank 𝕜 E = Module.finrank 𝕜 E := rfl
  have hv : ‖S v‖ = ‖(hS.eigenvectorBasis hn).repr (S v)‖ :=
    ((hS.eigenvectorBasis hn).repr.norm_map (S v)).symm
  rw [hv]
  have hsq : ‖(hS.eigenvectorBasis hn).repr (S v)‖ ^ 2 ≤ c ^ 2 * ‖v‖ ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq]
    calc ∑ i, ‖(hS.eigenvectorBasis hn).repr (S v) i‖ ^ 2
        = ∑ i, ‖((hS.eigenvalues hn i : ℝ) : 𝕜) * (hS.eigenvectorBasis hn).repr v i‖ ^ 2 := by
            refine Finset.sum_congr rfl fun i _ => ?_
            rw [hS.eigenvectorBasis_apply_self_apply hn v i]
      _ = ∑ i, (hS.eigenvalues hn i) ^ 2 * ‖(hS.eigenvectorBasis hn).repr v i‖ ^ 2 := by
            refine Finset.sum_congr rfl fun i _ => ?_
            rw [norm_mul, RCLike.norm_ofReal, mul_pow, sq_abs]
      _ ≤ ∑ i, c ^ 2 * ‖(hS.eigenvectorBasis hn).repr v i‖ ^ 2 := by
            refine Finset.sum_le_sum fun i _ => ?_
            have h2 : (hS.eigenvalues hn i) ^ 2 ≤ c ^ 2 := by
              rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) (heig i) 2
            exact mul_le_mul_of_nonneg_right h2 (by positivity)
      _ = c ^ 2 * ∑ i, ‖(hS.eigenvectorBasis hn).repr v i‖ ^ 2 := by rw [Finset.mul_sum]
      _ = c ^ 2 * ‖(hS.eigenvectorBasis hn).repr v‖ ^ 2 := by rw [EuclideanSpace.norm_sq_eq]
      _ = c ^ 2 * ‖v‖ ^ 2 := by rw [(hS.eigenvectorBasis hn).repr.norm_map]
  have hmul : (c * ‖v‖) ^ 2 = c ^ 2 * ‖v‖ ^ 2 := by ring
  rw [← hmul] at hsq
  have := sq_le_sq.mp hsq
  rwa [abs_of_nonneg (norm_nonneg _), abs_of_nonneg (mul_nonneg hc (norm_nonneg _))] at this

/-- Every eigenvalue of the self-adjoint operator `T` is bounded by `π/δ`. -/
lemma eigen_bound (lam : ι → ℝ) {δ : ℝ} (hδ : 0 < δ) (hinj : Function.Injective lam)
    (hsep : ∀ i j : ι, i ≠ j → δ ≤ |lam i - lam j|)
    (i : Fin (Module.finrank ℂ (EuclideanSpace ℂ ι))) :
    |((T_symm lam).eigenvalues rfl i)| ≤ Real.pi / δ := by
  set w : EuclideanSpace ℂ ι := (T_symm lam).eigenvectorBasis rfl i with hw
  set a : ℝ := (T_symm lam).eigenvalues rfl i with ha
  have hw1 : ‖w‖ = 1 := by rw [hw]; exact (T_symm lam).eigenvectorBasis rfl |>.norm_eq_one i
  have heigen : T lam w = ((a : ℝ) : ℂ) • w := by
    rw [hw, ha]; exact (T_symm lam).apply_eigenvectorBasis rfl i
  have hLw : L lam w = (-(Complex.I * ((a : ℝ) : ℂ))) • w := by
    have h1 : Complex.I • (L lam w) = ((a : ℝ) : ℂ) • w := by
      rw [← T_apply]; exact heigen
    have h2 : L lam w = (Complex.I⁻¹ * ((a : ℝ) : ℂ)) • w := by
      have := congrArg (fun u => (Complex.I)⁻¹ • u) h1
      simpa only [smul_smul, inv_mul_cancel₀ Complex.I_ne_zero, one_smul] using this
    rw [h2, Complex.inv_I]
    congr 1
    ring
  have hrel : ∀ k, ∑ j, hilbU lam k j * w j = -(Complex.I * ((a : ℝ) : ℂ)) * w k := by
    intro k
    have hcoord := congrArg (fun v : EuclideanSpace ℂ ι => v k) hLw
    rw [L_apply] at hcoord
    simpa using hcoord
  have hsel : ∑ k, ‖∑ j, hilbU lam k j * w j‖ ^ 2 ≤ (Real.pi ^ 2 / δ ^ 2) * ∑ k, ‖w k‖ ^ 2 := by
    have h := selberg_hilbert_quad lam hδ hinj hsep (fun k => w k) hrel
    simpa [hilbU] using h
  have hLnorm : ∑ k, ‖∑ j, hilbU lam k j * w j‖ ^ 2 = ‖L lam w‖ ^ 2 := by
    have : ∀ k, ‖∑ j, hilbU lam k j * w j‖ ^ 2 = ‖(L lam w) k‖ ^ 2 := by
      intro k; rw [L_apply]
    rw [Finset.sum_congr rfl (fun k _ => this k), ← EuclideanSpace.norm_sq_eq]
  have hwn : ∑ k, ‖w k‖ ^ 2 = ‖w‖ ^ 2 := (EuclideanSpace.norm_sq_eq w).symm
  have hnn : ‖L lam w‖ ^ 2 = a ^ 2 * ‖w‖ ^ 2 := by
    rw [hLw, norm_smul]
    have hc : ‖(-(Complex.I * ((a : ℝ) : ℂ)))‖ = |a| := by
      rw [norm_neg, norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs]
    rw [hc, mul_pow, sq_abs]
  rw [hLnorm, hwn, hnn, hw1] at hsel
  simp only [one_pow, mul_one] at hsel
  have h2 : a ^ 2 ≤ (Real.pi / δ) ^ 2 := by
    rw [div_pow]; exact hsel
  have h3 : |a| ≤ Real.pi / δ := by
    have := sq_le_sq.mp h2
    rwa [abs_of_pos (div_pos Real.pi_pos hδ)] at this
  exact h3

/-- **Hilbert's inequality for separated points** (Montgomery–Vaughan).  For real numbers
`λ i` that are pairwise `δ`-separated and complex numbers `z i`,
`‖∑ i, ∑_{j≠i} z i * conj (z j) / (λ i - λ j)‖ ≤ (π / δ) * ∑ i, ‖z i‖ ^ 2`. -/
theorem hilbert_separated {ι : Type*} [Fintype ι] [DecidableEq ι] (lam : ι → ℝ) {δ : ℝ}
    (hδ : 0 < δ)
    (hsep : ∀ i j : ι, i ≠ j → δ ≤ |lam i - lam j|) (z : ι → ℂ) :
    ‖∑ i, ∑ j ∈ Finset.univ.erase i, z i * star (z j) / ((lam i - lam j : ℝ) : ℂ)‖
      ≤ Real.pi / δ * ∑ i, ‖z i‖ ^ 2 := by
  have hinj : Function.Injective lam := by
    intro a b hab
    by_contra hne
    have h := hsep a b hne
    rw [hab, sub_self, abs_zero] at h
    linarith
  set w : EuclideanSpace ℂ ι := WithLp.toLp 2 z with hw
  have hwval : ∀ i, w i = z i := by
    intro i; simp [hw, WithLp.ofLp_toLp]
  have hwn2 : ‖w‖ ^ 2 = ∑ i, ‖z i‖ ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq]
  have hT : ‖(T lam) w‖ ≤ Real.pi / δ * ‖w‖ :=
    norm_apply_le_of_eigen_bound (T lam) (T_symm lam) (by positivity)
      (eigen_bound lam hδ hinj hsep) w
  have hquad : ‖inner ℂ ((T lam) w) w‖ ≤ Real.pi / δ * ∑ i, ‖z i‖ ^ 2 := by
    calc ‖inner ℂ ((T lam) w) w‖ ≤ ‖(T lam) w‖ * ‖w‖ := norm_inner_le_norm _ _
      _ ≤ (Real.pi / δ * ‖w‖) * ‖w‖ := mul_le_mul_of_nonneg_right hT (norm_nonneg _)
      _ = Real.pi / δ * ‖w‖ ^ 2 := by ring
      _ = Real.pi / δ * ∑ i, ‖z i‖ ^ 2 := by rw [hwn2]
  have hSp : (∑ p : ι × ι, w p.1 * hilbU lam p.1 p.2 * star (w p.2))
      = ∑ i, ∑ j ∈ Finset.univ.erase i, z i * star (z j) / ((lam i - lam j : ℝ) : ℂ) := by
    rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Finset.sum_erase_add (Finset.univ) (fun j => w i * hilbU lam i j * star (w j))
          (Finset.mem_univ i)]
    rw [show w i * hilbU lam i i * star (w i) = 0 by simp [hilbU_self], add_zero]
    refine Finset.sum_congr rfl fun j hj => ?_
    rw [Finset.mem_erase] at hj
    have hij : i ≠ j := fun h => hj.1 h.symm
    rw [hwval i, hwval j, hilbU_of_ne lam hij, div_eq_mul_inv]
    ring
  have hkey : inner ℂ ((T lam) w) w
      = -(Complex.I) * (∑ i, ∑ j ∈ Finset.univ.erase i,
          z i * star (z j) / ((lam i - lam j : ℝ) : ℂ)) := by
    rw [T_apply, inner_smul_left, inner_L, hSp]
    simp [Complex.conj_I]
  rw [show ‖∑ i, ∑ j ∈ Finset.univ.erase i, z i * star (z j) / ((lam i - lam j : ℝ) : ℂ)‖
        = ‖inner ℂ ((T lam) w) w‖ by
      rw [hkey, norm_mul, norm_neg, Complex.norm_I, one_mul]]
  exact hquad

end

end Commons.Analysis.ExponentialSums
