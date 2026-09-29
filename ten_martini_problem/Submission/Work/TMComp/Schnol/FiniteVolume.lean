import Mathlib
import Submission.Work.TMComp.Schnol.Defs
import Submission.Work.TMComp.Schnol.Basic

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Component C15 (`P_Schnol`): the finite-volume (Dirichlet truncation) facts

The truncated matrix `winMat M α lam θ` is Hermitian, its eigenvectors give solutions of the
almost Mathieu equation on the window `[-M, M]` (after zero extension), and the spectral
energy identity that turns a small residual in the window into a large set of eigenvalues
near `E₀`.
-/

open scoped ENNReal
open Matrix LeanEval.Analysis.TenMartini

noncomputable section

namespace Work.TMComp.Schnol

/-! ## 1. The truncation is Hermitian -/

theorem winMatHermitian (M : ℕ) (α lam θ : ℝ) : (winMat M α lam θ).IsHermitian := by
  ext i j
  simp only [winMat, Work.TMC16Core.dirMat, Matrix.conjTranspose_apply, Complex.star_def,
    Complex.conj_ofReal, map_add, map_sub, map_zero, map_one]
  by_cases hij : i = j
  · subst hij
    simp
  · have hji : ¬ (j = i) := fun h => hij h.symm
    rw [if_neg hij, if_neg hji]
    simp only [map_zero, map_one, star_zero, star_one, zero_add]
    split_ifs <;> simp

/-! ## 2. Eigenvectors of the truncation solve the equation on the window -/

theorem extRecur (M : ℕ) (α lam θ : ℝ) (w : Fin (2 * M + 1) → ℂ) {E : ℝ}
    (heig : (winMat M α lam θ).mulVec w = (E : ℂ) • w) :
    ∀ m : ℤ, -(M : ℤ) ≤ m → m ≤ (M : ℤ) →
      Work.TMContract.amoAct α lam θ (ext M w) m = (E : ℂ) * ext M w m := by
  intro m hm₁ hm₂
  let i : Fin (2 * M + 1) := ⟨(m + (M : ℤ)).toNat,
    by rw [Int.toNat_lt (by omega)]; omega⟩
  have hsite : (i : ℤ) - (M : ℤ) = m := by
    show (((m + (M : ℤ)).toNat : ℕ) : ℤ) - (M : ℤ) = m
    rw [Int.toNat_of_nonneg (by omega)]
    ring
  have hmat : ((Work.TMC16Core.dirMat α lam (θ - (M : ℝ) * α) 0 (2 * M + 1)).mulVec w) i
      = (E : ℂ) * w i := by
    have h := congrArg (fun f : Fin (2 * M + 1) → ℂ => f i) heig
    simpa [winMat, Pi.smul_apply, smul_eq_mul] using h
  have hkey := Work.TMC16Core.Basic.dirMat_mulVec_entry (α := α) (lam := lam)
    (φ := θ - (M : ℝ) * α) (E := 0) (n := 2 * M + 1) w i
  have h1 : ext M w (m + 1) = (if h : (i : ℕ) + 1 < 2 * M + 1 then w ⟨(i : ℕ) + 1, h⟩ else 0) := by
    have h := ext_succ M w i
    rw [hsite] at h
    exact h
  have h2 : ext M w (m - 1) = (if h : 0 < (i : ℕ) then w ⟨(i : ℕ) - 1, by omega⟩ else 0) := by
    have h := ext_pred M w i
    rw [hsite] at h
    exact h
  have h3 : ext M w m = w i := by
    have h := ext_eq M w i
    rw [hsite] at h
    exact h
  have h4 : ((Work.TMContract.amoPot α lam θ m : ℝ) : ℂ)
      = ((Work.TMC16Core.amoPot α lam (θ - (M : ℝ) * α) ((i : ℕ) : ℤ) : ℝ) : ℂ) := by
    have harg : θ + (m : ℝ) * α = (θ - (M : ℝ) * α) + (((i : ℕ) : ℤ) : ℝ) * α := by
      rw [← hsite]; push_cast; ring
    simp only [Work.TMContract.amoPot, Work.TMC16Core.amoPot, harg, sub_zero]
  rw [Work.TMContract.amoAct, h1, h2, h3, h4, ← hmat, hkey]
  ring

/-! ## 3. The window norm identity and the truncation of `H - E₀` -/

theorem norm_eq_of_sq_eq {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (h : a ^ 2 = b ^ 2) : a = b := by
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp h with h | h
  · exact h
  · have hb0 : b = 0 := by linarith
    rw [h, hb0]
    ring

/-- The squared norm of a vector supported in the window `[-M, M]` as a sum over the
`2*M+1` sites of the window. -/
theorem norm_sq_eq_window_sum (M : ℕ) (w : EllTwo)
    (hwin : ∀ n : ℤ, (n < -(M : ℤ) ∨ (M : ℤ) < n) → w n = 0) :
    ‖w‖ ^ 2 = ∑ i : Fin (2 * M + 1), ‖w ((i : ℤ) - (M : ℤ))‖ ^ 2 := by
  have hmem : ∀ n : ℤ,
      n ∉ Finset.univ.image (fun i : Fin (2 * M + 1) => (i : ℤ) - (M : ℤ)) → w n = 0 := by
    intro n hn
    by_contra hw
    apply hn
    have h1 : ¬ (n < -(M : ℤ) ∨ (M : ℤ) < n) := fun h => hw (hwin n h)
    rw [not_or, not_lt, not_lt] at h1
    refine Finset.mem_image.mpr ⟨⟨(n + (M : ℤ)).toNat, ?_⟩, Finset.mem_univ _, ?_⟩
    · rw [Int.toNat_lt (by omega)]; omega
    · show ((((n + (M : ℤ)).toNat : ℕ)) : ℤ) - (M : ℤ) = n
      rw [Int.toNat_of_nonneg (by omega)]
      ring
  have htsum : ‖w‖ ^ 2 = ∑' n : ℤ, ‖w n‖ ^ 2 := by
    have h := lp.norm_rpow_eq_tsum (p := 2) (E := fun _ : ℤ => ℂ) (by norm_num) w
    simpa using h
  have hmem2 : ∀ n : ℤ,
      n ∉ Finset.univ.image (fun i : Fin (2 * M + 1) => (i : ℤ) - (M : ℤ)) → ‖w n‖ ^ 2 = 0 := by
    intro n hn
    rw [hmem n hn, norm_zero]
    norm_num
  rw [htsum]
  rw [tsum_eq_sum (f := fun n : ℤ => ‖w n‖ ^ 2)
    (s := Finset.univ.image (fun i : Fin (2 * M + 1) => (i : ℤ) - (M : ℤ))) hmem2]
  have hinj : Set.InjOn (fun i : Fin (2 * M + 1) => (i : ℤ) - (M : ℤ))
      ((Finset.univ : Finset (Fin (2 * M + 1))) : Set (Fin (2 * M + 1))) := by
    intro x _ y _ hxy
    have h : ((x : ℕ) : ℤ) = ((y : ℕ) : ℤ) := by linarith [hxy]
    exact Fin.ext (by exact_mod_cast h)
  rw [Finset.sum_image hinj]

/-- The coordinate formula for the truncation `winMat M α lam θ`, at index `i` (site
`i - M`), with Dirichlet boundary terms. -/
theorem winMat_mulVec_apply (M : ℕ) (α lam θ : ℝ) (w : Fin (2 * M + 1) → ℂ)
    (i : Fin (2 * M + 1)) :
    ((winMat M α lam θ).mulVec w) i
      = ((Work.TMContract.amoPot α lam θ ((i : ℤ) - (M : ℤ)) : ℝ) : ℂ) * w i
        + (if h : (i : ℕ) + 1 < 2 * M + 1 then w ⟨(i : ℕ) + 1, h⟩ else 0)
        + (if h : 0 < (i : ℕ) then w ⟨(i : ℕ) - 1, by omega⟩ else 0) := by
  have hk := Work.TMC16Core.Basic.dirMat_mulVec_entry (α := α) (lam := lam)
    (φ := θ - (M : ℝ) * α) (E := 0) (n := 2 * M + 1) w i
  have hw : ((winMat M α lam θ).mulVec w) i
      = ((Work.TMC16Core.dirMat α lam (θ - (M : ℝ) * α) 0 (2 * M + 1)).mulVec w) i := rfl
  rw [hw, hk]
  have harg : (θ - (M : ℝ) * α) + (((i : ℕ) : ℤ) : ℝ) * α
      = θ + (((i : ℤ) - (M : ℤ) : ℤ) : ℝ) * α := by
    push_cast
    ring
  simp only [Work.TMContract.amoPot, Work.TMC16Core.amoPot, harg, sub_zero]

/-- The coordinate formula for the truncation applied to a window-restricted vector. -/
theorem winMat_mulVec_winVec_apply (M : ℕ) (α lam θ : ℝ) (φ : EllTwo) (i : Fin (2 * M + 1)) :
    ((winMat M α lam θ).mulVec (winVec M φ).ofLp) i
      = ((Work.TMContract.amoPot α lam θ ((i : ℤ) - (M : ℤ)) : ℝ) : ℂ) * φ ((i : ℤ) - (M : ℤ))
        + (if h : (i : ℕ) + 1 < 2 * M + 1 then
            φ (((⟨(i : ℕ) + 1, h⟩ : Fin (2 * M + 1)) : ℤ) - (M : ℤ)) else 0)
        + (if h : 0 < (i : ℕ) then
            φ (((⟨(i : ℕ) - 1, by omega⟩ : Fin (2 * M + 1)) : ℤ) - (M : ℤ)) else 0) :=
  winMat_mulVec_apply M α lam θ ((winVec M φ).ofLp) i

/-! ## 4. The spectral energy identity -/

theorem norm_sum_smul_orthonormal {n : ℕ}
    (b : OrthonormalBasis (Fin n) ℂ (EuclideanSpace ℂ (Fin n))) (cc : Fin n → ℂ) :
    ‖∑ j, cc j • b j‖ ^ 2 = ∑ j, ‖cc j‖ ^ 2 := by
  have hone : ∀ i j : Fin n, inner ℂ (b i) (b j) = if i = j then 1 else 0 :=
    orthonormal_iff_ite.mp b.orthonormal
  have hcoe : ∀ j, inner ℂ (b j) (∑ i, cc i • b i) = cc j := by
    intro j
    rw [inner_sum]
    rw [Finset.sum_eq_single j]
    · rw [inner_smul_right, hone j j, if_pos rfl, mul_one]
    · intro i _ hij
      rw [inner_smul_right, hone j i, if_neg (Ne.symm hij), mul_zero]
    · intro hj
      exact absurd (Finset.mem_univ j) hj
  have h1 := (onbFacts b (∑ i, cc i • b i)).1
  rw [← h1]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [hcoe j]

theorem energyIdentity {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) (hA : A.IsHermitian)
    (x : EuclideanSpace ℂ (Fin n)) (μ : ℝ) :
    ‖A.toEuclideanLin x - (μ : ℂ) • x‖ ^ 2
      = ∑ j, (hA.eigenvalues j - μ) ^ 2 * ‖inner ℂ (hA.eigenvectorBasis j) x‖ ^ 2 := by
  set b := hA.eigenvectorBasis with hb
  have heig : ∀ j, A.toEuclideanLin (b j) = ((hA.eigenvalues j : ℝ) : ℂ) • b j := by
    intro j
    rw [Matrix.toLpLin_apply, hA.mulVec_eigenvectorBasis j]
    apply WithLp.ofLp_injective
    show hA.eigenvalues j • (b j).ofLp = ((hA.eigenvalues j : ℝ) : ℂ) • (b j).ofLp
    exact RCLike.real_smul_eq_coe_smul _ _
  have key : A.toEuclideanLin x - (μ : ℂ) • x
      = ∑ j, (((hA.eigenvalues j - μ : ℝ) : ℂ) * inner ℂ (b j) x) • b j := by
    conv_lhs => rw [show x = ∑ j, inner ℂ (b j) x • b j from (b.sum_repr' x).symm]
    rw [map_sum, Finset.smul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_smul, heig j, smul_smul, smul_smul, ← sub_smul]
    congr 1
    rw [Complex.ofReal_sub]
    ring
  rw [key, norm_sum_smul_orthonormal b
    (fun j => ((hA.eigenvalues j - μ : ℝ) : ℂ) * inner ℂ (b j) x)]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, mul_pow, sq_abs]


/-! ## 5. The truncation does not change the norms -/

theorem truncNormEq (M : ℕ) (Y : ℤ) (hY : Y + 1 ≤ (M : ℤ)) (α lam θ : ℝ)
    {H : EllTwo →L[ℂ] EllTwo}
    (hH : IsAlmostMathieuOperator α lam θ H) (φ : EllTwo) (E₀ : ℝ)
    (hsupp : ∀ n : ℤ, (n < -Y ∨ Y < n) → φ n = 0) :
    ‖winVec M φ‖ = ‖φ‖ ∧
      ‖(winMat M α lam θ).toEuclideanLin (winVec M φ) - (E₀ : ℂ) • (winVec M φ)‖ =
        ‖H φ - (E₀ : ℂ) • φ‖ := by
  have hsuppM : ∀ n : ℤ, (n < -(M : ℤ) ∨ (M : ℤ) < n) → φ n = 0 := by
    intro n hn
    apply hsupp n
    rcases hn with h | h
    · left; linarith
    · right; linarith
  have hHsupp : ∀ n : ℤ, (n < -(M : ℤ) ∨ (M : ℤ) < n) → (H φ - (E₀ : ℂ) • φ) n = 0 := by
    intro n hn
    rw [lp.coeFn_sub, Pi.sub_apply, hH φ n, lp.coeFn_smul, Pi.smul_apply, smul_eq_mul]
    have h0 : φ n = 0 := hsuppM n hn
    have h1 : φ (n + 1) = 0 := by
      apply hsupp
      rcases hn with h | h
      · left; linarith
      · right; linarith
    have h2 : φ (n - 1) = 0 := by
      apply hsupp
      rcases hn with h | h
      · left; linarith
      · right; linarith
    rw [h0, h1, h2]
    ring
  constructor
  · have ha : ‖winVec M φ‖ ^ 2 = ∑ i : Fin (2 * M + 1), ‖φ ((i : ℤ) - (M : ℤ))‖ ^ 2 := by
      rw [winVec, PiLp.norm_sq_eq_of_L2]
    have hb : ‖φ‖ ^ 2 = ∑ i : Fin (2 * M + 1), ‖φ ((i : ℤ) - (M : ℤ))‖ ^ 2 :=
      norm_sq_eq_window_sum M φ hsuppM
    exact norm_eq_of_sq_eq (norm_nonneg _) (norm_nonneg _) (ha.trans hb.symm)
  · have hpt : ∀ i : Fin (2 * M + 1),
        ((winMat M α lam θ).toEuclideanLin (winVec M φ) - (E₀ : ℂ) • (winVec M φ)).ofLp i
          = (H φ - (E₀ : ℂ) • φ) ((i : ℤ) - (M : ℤ)) := by
      intro i
      have hmat := winMat_mulVec_winVec_apply M α lam θ φ i
      have hs1 : (if h : (i : ℕ) + 1 < 2 * M + 1 then
            φ (((⟨(i : ℕ) + 1, h⟩ : Fin (2 * M + 1)) : ℤ) - (M : ℤ)) else 0)
          = φ (((i : ℤ) - (M : ℤ)) + 1) := by
        by_cases h : (i : ℕ) + 1 < 2 * M + 1
        · rw [dif_pos h]
          have hidx : (((⟨(i : ℕ) + 1, h⟩ : Fin (2 * M + 1)) : ℤ) - (M : ℤ))
              = ((i : ℤ) - (M : ℤ)) + 1 := by push_cast; ring
          rw [hidx]
        · rw [dif_neg h]
          have hi : (i : ℕ) = 2 * M := by omega
          have hsite : ((i : ℤ) - (M : ℤ)) + 1 = (M : ℤ) + 1 := by push_cast [hi]; ring
          rw [hsite]
          exact (hsupp ((M : ℤ) + 1) (Or.inr (by linarith))).symm
      have hs2 : (if h : 0 < (i : ℕ) then
            φ (((⟨(i : ℕ) - 1, by omega⟩ : Fin (2 * M + 1)) : ℤ) - (M : ℤ)) else 0)
          = φ (((i : ℤ) - (M : ℤ)) - 1) := by
        by_cases h : 0 < (i : ℕ)
        · rw [dif_pos h]
          have hidx : (((⟨(i : ℕ) - 1, by omega⟩ : Fin (2 * M + 1)) : ℤ) - (M : ℤ))
              = ((i : ℤ) - (M : ℤ)) - 1 := by
            push_cast
            omega
          rw [hidx]
        · rw [dif_neg h]
          have hi : (i : ℕ) = 0 := by omega
          have hsite : ((i : ℤ) - (M : ℤ)) - 1 = -(M : ℤ) - 1 := by push_cast [hi]; ring
          rw [hsite]
          exact (hsupp (-(M : ℤ) - 1) (Or.inl (by linarith))).symm
      rw [show ((winMat M α lam θ).toEuclideanLin (winVec M φ) - (E₀ : ℂ) • (winVec M φ)).ofLp i
            = ((winMat M α lam θ).mulVec (winVec M φ).ofLp) i - (E₀ : ℂ) * φ ((i : ℤ) - (M : ℤ))
            from rfl]
      rw [hmat, hs1, hs2, lp.coeFn_sub, Pi.sub_apply, hH φ ((i : ℤ) - (M : ℤ)),
        lp.coeFn_smul, Pi.smul_apply, smul_eq_mul]
      simp only [Work.TMContract.amoPot]
      push_cast
      ring
    have hvec : winVec M (H φ - (E₀ : ℂ) • φ)
        = (winMat M α lam θ).toEuclideanLin (winVec M φ) - (E₀ : ℂ) • (winVec M φ) := by
      apply PiLp.ext
      intro i
      rw [hpt i]
      rfl
    have ha : ‖(winMat M α lam θ).toEuclideanLin (winVec M φ) - (E₀ : ℂ) • (winVec M φ)‖ ^ 2
        = ∑ i : Fin (2 * M + 1), ‖(H φ - (E₀ : ℂ) • φ) ((i : ℤ) - (M : ℤ))‖ ^ 2 := by
      rw [← hvec, winVec, PiLp.norm_sq_eq_of_L2]
    have hb : ‖H φ - (E₀ : ℂ) • φ‖ ^ 2
        = ∑ i : Fin (2 * M + 1), ‖(H φ - (E₀ : ℂ) • φ) ((i : ℤ) - (M : ℤ))‖ ^ 2 :=
      norm_sq_eq_window_sum M _ hHsupp
    exact norm_eq_of_sq_eq (norm_nonneg _) (norm_nonneg _) (ha.trans hb.symm)


end Work.TMComp.Schnol
