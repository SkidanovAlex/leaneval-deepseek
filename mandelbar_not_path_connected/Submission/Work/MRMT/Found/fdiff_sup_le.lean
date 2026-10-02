import Mathlib
import Submission.Work.MRMT.Found.FdiffDef

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


noncomputable section

open scoped ContDiff

namespace Work.MRMT.Found

/-! ## Combinatorics of the finite-difference coefficients -/

private lemma fdCoeff_zero_right (n : ℕ) : fdCoeff n (n+1) = 0 := by
  rw [fdCoeff, Nat.choose_succ_self]
  ring

private lemma fdCoeff_succ_zero (n : ℕ) : fdCoeff (n+1) 0 = -fdCoeff n 0 := by
  rw [fdCoeff, fdCoeff, Nat.sub_zero, Nat.sub_zero, Nat.choose_zero_right, Nat.choose_zero_right]
  push_cast
  rw [pow_succ]
  ring

private lemma fdCoeff_succ_succ (n i : ℕ) :
    fdCoeff (n+1) (i+1) = fdCoeff n i - fdCoeff n (i+1) := by
  rw [fdCoeff, fdCoeff, fdCoeff, Nat.succ_sub_succ, Nat.choose_succ_succ']
  push_cast
  by_cases h : i + 1 ≤ n
  · have h1 : n - (i+1) = n - i - 1 := (Nat.sub_sub n i 1).symm
    obtain ⟨k, hk⟩ : ∃ k, n - i = k + 1 := ⟨n - i - 1, by omega⟩
    have hk' : n - i - 1 = k := by omega
    have hpow : (-1:ℝ)^(n-i) = -(-1:ℝ)^(n-(i+1)) := by
      rw [h1, hk', hk, pow_succ]
      ring
    rw [hpow]; ring
  · have hb : n.choose (i+1) = 0 := Nat.choose_eq_zero_of_lt (by omega)
    have h1 : n - (i+1) = 0 := by omega
    have h2 : n - i = 0 := by omega
    rw [hb, h1, h2]; ring

/-- The pure summation identity underlying the Pascal recurrence for finite differences:
shifting a `c_n`-weighted sum of a sequence and subtracting the unshifted sum produces the
`c_{n+1}`-weighted sum. -/
private lemma fdiff_sum_shift {E : Type*} [AddCommGroup E] [Module ℝ E] (A : ℕ → E) (n : ℕ) :
    (∑ j ∈ Finset.range (n+1), fdCoeff n j • A (j+1))
      - (∑ j ∈ Finset.range (n+1), fdCoeff n j • A j)
      = ∑ m ∈ Finset.range (n+2), fdCoeff (n+1) m • A m := by
  have h1 : (∑ j ∈ Finset.range (n+1), fdCoeff n j • A (j+1))
      = (∑ m ∈ Finset.range (n+2), (if m = 0 then 0 else fdCoeff n (m-1)) • A m) := by
    conv_rhs => rw [Finset.sum_range_succ']
    simp
  have h2 : (∑ j ∈ Finset.range (n+1), fdCoeff n j • A j)
      = (∑ m ∈ Finset.range (n+2), fdCoeff n m • A m) := by
    conv_rhs => rw [Finset.sum_range_succ]
    rw [fdCoeff_zero_right]
    simp
  rw [h1, h2, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl (fun m hm => ?_)
  rcases Nat.eq_zero_or_pos m with hm0 | hmpos
  · subst hm0
    rw [ite_eq_left (show (0:ℕ) = 0 from rfl), fdCoeff_succ_zero]
    simp [neg_smul, zero_sub]
  · obtain ⟨i, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.pos_iff_ne_zero.mp hmpos)
    rw [ite_eq_right (Nat.succ_ne_zero i), Nat.succ_sub_one, fdCoeff_succ_succ, sub_smul]

/-- Pascal recurrence for the finite-difference sums. -/
private theorem fdiff_succ_aux {E : Type*} [AddCommGroup E] [Module ℝ E] (n : ℕ) (f : ℂ → E)
    (h z : ℂ) : fdiff (n+1) f h z = fdiff n f h (z - h) - fdiff n f h z := by
  have hA : ∀ i : ℕ, f ((z - h) - (i:ℂ)*h) = f (z - ((i+1 : ℕ):ℂ)*h) := by
    intro i; congr 1; push_cast; ring
  simp only [fdiff, hA]
  exact (fdiff_sum_shift (E := E) (fun i => f (z - (i:ℂ)*h)) n).symm

/-! ## The Fréchet derivative of a finite difference -/

/-- The Fréchet derivative of the `n`-th finite difference is the `n`-th finite difference of
the derivative. -/
lemma hasFDerivAt_fdiff {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (n : ℕ) {f : ℂ → E} (hf : Differentiable ℝ f) (h z : ℂ) :
    HasFDerivAt (fun w : ℂ => fdiff n f h w) (fdiff n (fun w : ℂ => fderiv ℝ f w) h z) z := by
  have key : ∀ j ∈ Finset.range (n + 1),
      HasFDerivAt (fun w : ℂ => fdCoeff n j • f (w - (j : ℂ) * h))
        (fdCoeff n j • fderiv ℝ f (z - (j : ℂ) * h)) z := by
    intro j hj
    have h1 : HasFDerivAt (fun w : ℂ => w - (j : ℂ) * h) (ContinuousLinearMap.id ℝ ℂ) z :=
      hasFDerivAt_sub_const _
    have h2 : HasFDerivAt f (fderiv ℝ f (z - (j : ℂ) * h)) ((fun w : ℂ => w - (j : ℂ) * h) z) := by
      simpa using (hf (z - (j : ℂ) * h)).hasFDerivAt
    have h3 := h2.comp z h1
    simp only [ContinuousLinearMap.comp_id] at h3
    exact h3.const_smul (fdCoeff n j)
  have hsum0 := HasFDerivAt.sum key
  have hfun : (∑ i ∈ Finset.range (n+1), (fun w : ℂ => fdCoeff n i • f (w - (i:ℂ)*h)))
      = (fun w : ℂ => fdiff n f h w) := by
    ext w
    simp only [fdiff, Finset.sum_apply]
  have hder' : (∑ i ∈ Finset.range (n+1), (fdCoeff n i • fderiv ℝ f (z - (i:ℂ)*h)))
      = fdiff n (fun w : ℂ => fderiv ℝ f w) h z := by
    simp only [fdiff]
  rw [hfun, hder'] at hsum0
  exact hsum0

/-! ## The uniform bound -/

/-- The `n`-th finite difference of a smooth compactly supported family is `O(‖h‖^n)`,
uniformly in the point and the step. -/
theorem fdiff_bound (n : ℕ) :
    ∀ (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] (f : ℂ → E),
      ContDiff ℝ ∞ f → HasCompactSupport f →
      ∃ K : ℝ, 0 ≤ K ∧ ∀ h z : ℂ, ‖fdiff n f h z‖ ≤ K * ‖h‖ ^ n := by
  induction n with
  | zero =>
      intro E _ _ f hf hs
      obtain ⟨C, hC⟩ := hf.continuous.bounded_above_of_compact_support hs
      refine ⟨max C 0, le_max_right _ _, fun h z => ?_⟩
      rw [fdiff_zero, pow_zero, mul_one]
      exact le_trans (hC z) (le_max_left _ _)
  | succ n ih =>
      intro E _ _ f hf hs
      have hdiff : Differentiable ℝ f := hf.differentiable (by simp)
      have hg_cd : ContDiff ℝ ∞ (fun w : ℂ => fderiv ℝ f w) := by
        have hOn := ((contDiffOn_infty_iff_fderiv_of_isOpen (s := Set.univ) isOpen_univ).1
          (contDiffOn_univ.2 hf)).2
        exact contDiffOn_univ.1 hOn
      have hg_cs : HasCompactSupport (fun w : ℂ => fderiv ℝ f w) := hs.fderiv ℝ
      obtain ⟨K', hK'0, hK'⟩ := ih (ℂ →L[ℝ] E) (fun w : ℂ => fderiv ℝ f w) hg_cd hg_cs
      refine ⟨K', hK'0, fun h z => ?_⟩
      have hder : ∀ w : ℂ,
          fderiv ℝ (fun w : ℂ => fdiff n f h w) w = fdiff n (fun w : ℂ => fderiv ℝ f w) h w :=
        fun w => (hasFDerivAt_fdiff n hdiff h w).fderiv
      have hbound : ∀ w ∈ segment ℝ z (z - h),
          ‖fderiv ℝ (fun w : ℂ => fdiff n f h w) w‖ ≤ K' * ‖h‖ ^ n := by
        intro w hw
        rw [hder w]
        exact hK' h w
      have hdiffat : ∀ w ∈ segment ℝ z (z - h),
          DifferentiableAt ℝ (fun w : ℂ => fdiff n f h w) w :=
        fun w hw => (hasFDerivAt_fdiff n hdiff h w).differentiableAt
      have hmvt := Convex.norm_image_sub_le_of_norm_fderiv_le hdiffat hbound
        (convex_segment z (z - h)) (left_mem_segment ℝ z (z - h)) (right_mem_segment ℝ z (z - h))
      have hmvt' : ‖fdiff n f h (z - h) - fdiff n f h z‖ ≤ (K' * ‖h‖ ^ n) * ‖h‖ := by
        have hd : (z - h) - z = -h := by ring
        simpa [hd] using hmvt
      rw [fdiff_succ_aux]
      calc ‖fdiff n f h (z - h) - fdiff n f h z‖ ≤ (K' * ‖h‖ ^ n) * ‖h‖ := hmvt'
        _ = K' * ‖h‖ ^ (n+1) := by rw [pow_succ]; ring

/-! ## The requested statement -/

theorem fdiff_sup_le {g : ℂ → ℂ} (hg : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) g) (hs : HasCompactSupport g)
    (N : ℕ) : ∃ C : ℝ, 0 ≤ C ∧ ∀ t z : ℂ,
      ‖∑ j ∈ Finset.range (N+1), (-1 : ℂ) ^ (N - j) * (N.choose j : ℂ) * g (z - (j : ℂ) * t)‖ ≤ C * ‖t‖ ^ N := by
  obtain ⟨K, hK0, hK⟩ := fdiff_bound N ℂ g hg hs
  refine ⟨K, hK0, fun t z => ?_⟩
  have hsum : (∑ j ∈ Finset.range (N+1), (-1 : ℂ) ^ (N - j) * (N.choose j : ℂ) * g (z - (j : ℂ) * t))
      = fdiff N g t z := by
    rw [fdiff]
    refine Finset.sum_congr rfl (fun j hj => ?_)
    simp only [fdCoeff]
    rw [Algebra.smul_def, map_mul, map_pow, map_neg, map_one, map_natCast]
  rw [hsum]
  exact hK t z

end Work.MRMT.Found
