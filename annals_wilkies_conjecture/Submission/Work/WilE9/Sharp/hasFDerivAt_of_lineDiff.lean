import Mathlib

set_option maxHeartbeats 4000000

open scoped Topology BigOperators
open Filter Asymptotics Set

namespace Work.WilE9.Sharp

/-! ### Auxiliary lemmas for `hasFDerivAt_of_lineDiff`

These are the two ingredients of the proof: a one-dimensional mean-value estimate along an
axis-parallel segment (`lineDeriv_bound`) and the coordinate-by-coordinate telescoping of
`F x - F y` into line steps (`lineDecomp'`). -/

namespace LineDiffAux


/-- Interpolating point between `y` (k = 0) and `x` (k = n). -/
def interp {n : ℕ} (x y : Fin n → ℝ) (k : ℕ) : Fin n → ℝ :=
  fun j => if (j : ℕ) < k then x j else y j

lemma abs_le_abs_of_mem_uIcc {s t : ℝ} (h : s ∈ Set.uIcc (0:ℝ) t) : |s| ≤ |t| := by
  rcases Set.mem_uIcc.mp h with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · rw [abs_of_nonneg h1]
    exact le_trans h2 (le_abs_self t)
  · rw [abs_of_nonpos h2]
    exact le_trans (by linarith only [h1]) (neg_le_abs t)

lemma hasDerivAt_of_shift {F : ℝ → ℝ} {c u : ℝ}
    (h : HasDerivAt (fun s : ℝ => F (u + s)) c 0) : HasDerivAt F c u := by
  rw [hasDerivAt_iff_isLittleO_nhds_zero] at h ⊢
  simpa only [zero_add, add_zero] using h

lemma norm_pi_single_one {n : ℕ} (k : Fin n) :
    ‖(Pi.single k (1:ℝ) : Fin n → ℝ)‖ = 1 := by
  rw [Pi.norm_single]
  norm_num

lemma lineDeriv_bound {n : ℕ} {f : (Fin n → ℝ) → ℝ} {U : Set (Fin n → ℝ)}
    {g : Fin n → (Fin n → ℝ) → ℝ}
    (hl : ∀ i, ∀ p ∈ U, ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
        ∀ t : ℝ, 0 < |t| → |t| < δ →
          |f (p + t • Pi.single i (1 : ℝ)) - f p - t * g i p| ≤ ε * |t|)
    {i : Fin n} {a y : Fin n → ℝ} {t ε : ℝ}
    (hseg : ∀ s ∈ Set.uIcc (0:ℝ) t, a + s • Pi.single i (1 : ℝ) ∈ U)
    (hbound : ∀ s ∈ Set.uIcc (0:ℝ) t, ‖g i (a + s • Pi.single i (1 : ℝ)) - g i y‖ ≤ ε) :
    |f (a + t • Pi.single i (1 : ℝ)) - f a - t * g i y| ≤ ε * |t| := by
  have hline_at : ∀ u ∈ Set.uIcc (0:ℝ) t,
      HasDerivAt (fun z : ℝ => f (a + z • Pi.single i (1:ℝ)))
        (g i (a + u • Pi.single i (1:ℝ))) u := by
    intro u hu
    have hp : a + u • Pi.single i (1:ℝ) ∈ U := hseg u hu
    have hline0 : HasDerivAt (fun s : ℝ => f ((a + u • Pi.single i (1:ℝ)) + s • Pi.single i (1:ℝ)))
        (g i (a + u • Pi.single i (1:ℝ))) 0 := by
      rw [hasDerivAt_iff_isLittleO_nhds_zero, Asymptotics.isLittleO_iff]
      intro c hc
      obtain ⟨δ, hδ, hδ'⟩ := hl i (a + u • Pi.single i (1:ℝ)) hp c hc
      refine Metric.mem_nhds_iff.mpr ⟨δ, hδ, fun s hs => ?_⟩
      simp only [Set.mem_setOf_eq]
      rw [Metric.mem_ball, dist_eq_norm, sub_zero, Real.norm_eq_abs] at hs
      by_cases hs0 : s = 0
      · subst hs0
        simp only [zero_add, zero_smul, add_zero, sub_self, sub_zero, norm_zero, mul_zero]
        norm_num
      · have hb := hδ' s (abs_pos.mpr hs0) hs
        simpa only [zero_smul, zero_add, add_zero, smul_eq_mul, Real.norm_eq_abs] using hb
    have hfun : (fun s : ℝ => f (a + (u + s) • Pi.single i (1:ℝ)))
        = (fun s : ℝ => f ((a + u • Pi.single i (1:ℝ)) + s • Pi.single i (1:ℝ))) := by
      funext s
      rw [add_smul, add_assoc]
    rw [← hfun] at hline0
    exact hasDerivAt_of_shift hline0
  have hderiv : ∀ u ∈ Set.uIcc (0:ℝ) t,
      HasDerivAt (fun z : ℝ => f (a + z • Pi.single i (1:ℝ)) - z * g i y)
        (g i (a + u • Pi.single i (1:ℝ)) - g i y) u := by
    intro u hu
    have h1 := hline_at u hu
    have h2 : HasDerivAt (fun z : ℝ => z * g i y) (g i y) u := by
      have h := (hasDerivAt_id u).mul_const (g i y)
      rw [one_mul] at h
      exact h
    exact HasDerivAt.sub h1 h2
  have hmvt : ‖(f (a + t • Pi.single i (1:ℝ)) - t * g i y)
        - (f (a + (0:ℝ) • Pi.single i (1:ℝ)) - (0:ℝ) * g i y)‖ ≤ ε * ‖t - 0‖ :=
    Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
      (f := fun z : ℝ => f (a + z • Pi.single i (1:ℝ)) - z * g i y)
      (f' := fun u : ℝ => g i (a + u • Pi.single i (1:ℝ)) - g i y)
      (s := Set.uIcc (0:ℝ) t) (x := (0:ℝ)) (y := t) (C := ε)
      (fun u hu => (hderiv u hu).hasDerivWithinAt) hbound (convex_uIcc 0 t)
      left_mem_uIcc right_mem_uIcc
  have hψeq : (f (a + t • Pi.single i (1:ℝ)) - t * g i y)
        - (f (a + (0:ℝ) • Pi.single i (1:ℝ)) - (0:ℝ) * g i y)
      = f (a + t • Pi.single i (1:ℝ)) - f a - t * g i y := by
    simp only [zero_smul, add_zero, zero_mul, sub_zero]
    abel
  rw [hψeq] at hmvt
  simpa only [Real.norm_eq_abs, sub_zero] using hmvt

lemma lineDecomp' {n : ℕ} (F : (Fin n → ℝ) → ℝ) (x y : Fin n → ℝ) (G : Fin n → ℝ) :
    F x - F y - ∑ i : Fin n, (x i - y i) * G i =
      ∑ k : Fin n,
        ((F (interp x y k + (x k - y k) • Pi.single k (1 : ℝ)) - F (interp x y k))
          - (x k - y k) * G k) := by
  have hx : interp x y n = x := by
    funext j
    simp only [interp]
    rw [if_pos j.isLt]
  have hy : interp x y 0 = y := by
    funext j
    simp only [interp]
    rw [if_neg (Nat.not_lt_zero _)]
  have hsucc : ∀ k : Fin n,
      interp x y ((k:ℕ)+1) = interp x y k + (x k - y k) • Pi.single k (1:ℝ) := by
    intro k
    funext j
    by_cases hjk : j = k
    · subst hjk
      simp only [interp, Pi.add_apply, Pi.smul_apply, Pi.single_eq_same, smul_eq_mul]
      rw [if_pos (Nat.lt_succ_self _), if_neg (Nat.lt_irrefl _)]
      ring
    · have hne : (j:ℕ) ≠ (k:ℕ) := fun h => hjk (Fin.ext h)
      simp only [interp, Pi.add_apply, Pi.smul_apply, Pi.single_eq_of_ne hjk, smul_zero, add_zero]
      by_cases h2 : (j:ℕ) < (k:ℕ)
      · rw [if_pos (by omega : (j:ℕ) < (k:ℕ)+1), if_pos h2]
      · rw [if_neg (by omega : ¬ ((j:ℕ) < (k:ℕ)+1)), if_neg h2]
  have htel : (∑ k : Fin n, (F (interp x y ((k:ℕ)+1)) - F (interp x y (k:ℕ)))) = F x - F y := by
    rw [Fin.sum_univ_eq_sum_range (fun m => F (interp x y (m+1)) - F (interp x y m)) n]
    rw [Finset.sum_range_sub (fun m => F (interp x y m)) n]
    rw [hx, hy]
  rw [Finset.sum_sub_distrib]
  have hA : (∑ k : Fin n, (F (interp x y k + (x k - y k) • Pi.single k (1:ℝ)) - F (interp x y k)))
      = F x - F y := by
    rw [show (∑ k : Fin n, (F (interp x y k + (x k - y k) • Pi.single k (1:ℝ)) - F (interp x y k)))
          = ∑ k : Fin n, (F (interp x y ((k:ℕ)+1)) - F (interp x y (k:ℕ))) from
        Finset.sum_congr rfl (fun k _ => by rw [hsucc k])]
    exact htel
  rw [hA]

end LineDiffAux

open LineDiffAux

theorem hasFDerivAt_of_lineDiff {n : ℕ} {f : (Fin n → ℝ) → ℝ} {U : Set (Fin n → ℝ)}
    (hU : IsOpen U) (hfc : ContinuousOn f U) (g : Fin n → (Fin n → ℝ) → ℝ)
    (hg : ∀ i, ContinuousOn (g i) U)
    (hl : ∀ i, ∀ p ∈ U, ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
        ∀ t : ℝ, 0 < |t| → |t| < δ →
          |f (p + t • Pi.single i (1 : ℝ)) - f p - t * g i p| ≤ ε * |t|) :
    ∀ y ∈ U, HasFDerivAt f
      (∑ i : Fin n, (g i y) • (ContinuousLinearMap.proj i : (Fin n → ℝ) →L[ℝ] ℝ)) y := by
  intro y hy
  obtain ⟨ρ, hρ, hρU⟩ := Metric.isOpen_iff.mp hU y hy
  have hρU' : ∀ {z : Fin n → ℝ}, ‖z - y‖ < ρ → z ∈ U := by
    intro z hz
    exact hρU (by simpa only [Metric.mem_ball, dist_eq_norm] using hz)
  rw [hasFDerivAt_iff_isLittleO, Asymptotics.isLittleO_iff]
  intro ε hε
  set C : ℝ := ε / ((n : ℝ) + 1) with hC
  have hCpos : 0 < C := by rw [hC]; positivity
  have hCne : ((n : ℝ) + 1) ≠ 0 := by positivity
  have hCmul : C * ((n : ℝ) + 1) = ε := by rw [hC]; exact div_mul_cancel₀ ε hCne
  have hGcont : ContinuousOn (fun z : Fin n → ℝ => fun i => g i z) U := continuousOn_pi.mpr hg
  have hGci : ContinuousWithinAt (fun z : Fin n → ℝ => fun i => g i z) U y :=
    hGcont.continuousWithinAt hy
  rw [Metric.continuousWithinAt_iff] at hGci
  obtain ⟨δg, hδgpos, hδg⟩ := hGci C hCpos
  refine Metric.mem_nhds_iff.mpr ⟨min ρ δg / 2, div_pos (lt_min hρ hδgpos) two_pos, fun x hx => ?_⟩
  simp only [Set.mem_setOf_eq]
  rw [Metric.mem_ball, dist_eq_norm] at hx
  have hr2 : 2 * ‖x - y‖ < min ρ δg := by linarith only [hx]
  have hkabs : ∀ k : Fin n, |x k - y k| ≤ ‖x - y‖ := by
    intro k
    have h1 := norm_le_pi_norm (x - y) k
    rwa [Pi.sub_apply, Real.norm_eq_abs] at h1
  have hLapp : (∑ i : Fin n, (g i y) • (ContinuousLinearMap.proj i : (Fin n → ℝ) →L[ℝ] ℝ)) (x - y)
      = ∑ i : Fin n, (x i - y i) * g i y := by
    rw [sum_apply]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [smul_apply, ContinuousLinearMap.proj_apply, Pi.sub_apply, smul_eq_mul, mul_comm]
  have hterm : ∀ k : Fin n,
      |(f (interp x y k + (x k - y k) • Pi.single k (1:ℝ)) - f (interp x y k))
        - (x k - y k) * g k y| ≤ C * |x k - y k| := by
    intro k
    have hA : ‖interp x y k - y‖ ≤ ‖x - y‖ := by
      rw [pi_norm_le_iff_of_nonneg (norm_nonneg _)]
      intro j
      by_cases hj : (j : ℕ) < k
      · have he : (interp x y k - y) j = (x - y) j := by
          simp only [Pi.sub_apply, interp]
          rw [if_pos hj]
        rw [he]; exact norm_le_pi_norm (x - y) j
      · have he : (interp x y k - y) j = 0 := by
          simp only [Pi.sub_apply, interp]
          rw [if_neg hj, sub_self]
        rw [he]; simp
    have hclose : ∀ s : ℝ, |s| ≤ |x k - y k| →
        ‖interp x y k + s • Pi.single k (1:ℝ) - y‖ < min ρ δg := by
      intro s hs
      have hdist : ‖interp x y k + s • Pi.single k (1:ℝ) - y‖
          ≤ ‖interp x y k - y‖ + |s| := by
        have he : (interp x y k + s • Pi.single k (1:ℝ)) - y
            = (interp x y k - y) + (s • Pi.single k (1:ℝ)) := by abel
        rw [he]
        calc ‖(interp x y k - y) + s • Pi.single k (1:ℝ)‖
            ≤ ‖interp x y k - y‖ + ‖s • Pi.single k (1:ℝ)‖ := norm_add_le _ _
          _ = ‖interp x y k - y‖ + |s| := by
                rw [norm_smul, Real.norm_eq_abs, norm_pi_single_one, mul_one]
      calc ‖interp x y k + s • Pi.single k (1:ℝ) - y‖
          ≤ ‖interp x y k - y‖ + |s| := hdist
        _ ≤ ‖x - y‖ + ‖x - y‖ := add_le_add hA (le_trans hs (hkabs k))
        _ = 2 * ‖x - y‖ := by rw [two_mul]
        _ < min ρ δg := hr2
    apply lineDeriv_bound hl
    · intro s hs
      exact hρU' (lt_of_lt_of_le (hclose s (abs_le_abs_of_mem_uIcc hs)) (min_le_left _ _))
    · intro s hs
      have hz := hclose s (abs_le_abs_of_mem_uIcc hs)
      have hzU : interp x y k + s • Pi.single k (1:ℝ) ∈ U :=
        hρU' (lt_of_lt_of_le hz (min_le_left _ _))
      have hgd := hδg hzU (by simpa only [dist_eq_norm] using lt_of_lt_of_le hz (min_le_right _ _))
      have hgd' : ‖(fun i => g i (interp x y k + s • Pi.single k (1:ℝ))) - (fun i => g i y)‖ < C := by
        simpa only [dist_eq_norm] using hgd
      have h1 := norm_le_pi_norm
        ((fun i => g i (interp x y k + s • Pi.single k (1:ℝ))) - (fun i => g i y)) k
      have h1' : ‖g k (interp x y k + s • Pi.single k (1:ℝ)) - g k y‖
          ≤ ‖(fun i => g i (interp x y k + s • Pi.single k (1:ℝ))) - (fun i => g i y)‖ := by
        simpa only [Pi.sub_apply] using h1
      exact le_of_lt (lt_of_le_of_lt h1' hgd')
  have hdec := lineDecomp' f x y (fun i => g i y)
  rw [hLapp, hdec, Real.norm_eq_abs]
  calc |∑ k : Fin n, ((f (interp x y k + (x k - y k) • Pi.single k (1:ℝ)) - f (interp x y k))
          - (x k - y k) * g k y)|
      ≤ ∑ k : Fin n, |(f (interp x y k + (x k - y k) • Pi.single k (1:ℝ)) - f (interp x y k))
          - (x k - y k) * g k y| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ k : Fin n, C * |x k - y k| := Finset.sum_le_sum (fun k _ => hterm k)
    _ = C * ∑ k : Fin n, |x k - y k| := by rw [Finset.mul_sum]
    _ ≤ C * (((n : ℝ) + 1) * ‖x - y‖) := by
          refine mul_le_mul_of_nonneg_left ?_ (le_of_lt hCpos)
          calc ∑ k : Fin n, |x k - y k| ≤ ∑ k : Fin n, ‖x - y‖ :=
                Finset.sum_le_sum (fun k _ => hkabs k)
            _ = (n : ℝ) * ‖x - y‖ := by
                  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
            _ ≤ ((n : ℝ) + 1) * ‖x - y‖ :=
                  mul_le_mul_of_nonneg_right (le_add_of_nonneg_right zero_le_one) (norm_nonneg _)
    _ = ε * ‖x - y‖ := by rw [← mul_assoc, hCmul]


end Work.WilE9.Sharp
