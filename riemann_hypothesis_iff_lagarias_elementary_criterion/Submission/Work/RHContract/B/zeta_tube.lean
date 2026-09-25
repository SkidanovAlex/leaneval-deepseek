import Mathlib
import Submission.Work.RHContract.B.zeta_neg_of_mem_Ioo

namespace Work.RHContract.B

/-!
# The Riemann zeta function is zero-free in a thin tube around the real axis

For `c ∈ (-1/2, 0)` the segment `[c+1, 1] ⊂ ℝ` of the real axis contains no zero of `ζ`:
for `c + 1 ≤ t < 1` we have `0 < t < 1` and `ζ t < 0` (`zeta_neg_of_mem_Ioo`), while at `t = 1`
the (junk) value `ζ 1` is non-zero.  Since the zeros of `ζ` form a discrete subset which is
finite in any compact set, the whole rectangle `[c+1,1] × [-1,1]` contains only finitely many
zeros, none of which lie on the real axis; hence there is a positive lower bound `ν` for the
imaginary parts of these zeros and `min ν 1` is the required tube radius.
-/

theorem zeta_tube (c : ℝ) (hc1 : -(1 / 2 : ℝ) < c) (hc2 : c < 0) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ w : ℂ, c + 1 ≤ w.re → w.re ≤ 1 → w ≠ 1 →
      |w.im| < δ → riemannZeta w ≠ 0 := by
  -- the compact rectangle `K = [c+1,1] × [-1,1]`
  let K : Set ℂ := {w : ℂ | c + 1 ≤ w.re ∧ w.re ≤ 1 ∧ |w.im| ≤ 1}
  have hKcpt : IsCompact K := by
    rw [Metric.isCompact_iff_isClosed_bounded]
    refine ⟨?_, ?_⟩
    · have h1 : IsClosed {w : ℂ | c + 1 ≤ w.re} := isClosed_Ici.preimage Complex.continuous_re
      have h2 : IsClosed {w : ℂ | w.re ≤ 1} := isClosed_Iic.preimage Complex.continuous_re
      have h3 : IsClosed {w : ℂ | |w.im| ≤ 1} :=
        isClosed_Iic.preimage (continuous_abs.comp Complex.continuous_im)
      have hKeq : K = {w : ℂ | c + 1 ≤ w.re} ∩ {w : ℂ | w.re ≤ 1} ∩ {w : ℂ | |w.im| ≤ 1} := by
        ext w; simp [K, and_assoc]
      rw [hKeq]
      exact (h1.inter h2).inter h3
    · rw [Metric.isBounded_iff_subset_closedBall (0 : ℂ)]
      refine ⟨Real.sqrt 2, fun w hw => ?_⟩
      rw [Metric.mem_closedBall, dist_zero_right]
      have hc1' : (0 : ℝ) < c + 1 := by linarith
      have hre0 : 0 ≤ w.re := le_trans (le_of_lt hc1') hw.1
      have hre2 : w.re ^ 2 ≤ 1 :=
        (sq_le_one_iff_abs_le_one w.re).mpr (by rw [abs_of_nonneg hre0]; exact hw.2.1)
      have him2 : w.im ^ 2 ≤ 1 := (sq_le_one_iff_abs_le_one w.im).mpr hw.2.2
      have hnorm : ‖w‖ ^ 2 ≤ 2 := by
        rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
        nlinarith
      have hle : ‖w‖ ≤ Real.sqrt 2 := by
        have h := Real.sqrt_le_sqrt hnorm
        rwa [Real.sqrt_sq (norm_nonneg w)] at h
      exact hle
  -- only finitely many zeros lie in `K`
  have hfin : (K ∩ riemannZetaZeros).Finite := hKcpt.inter_riemannZetaZeros_finite
  -- none of them lies on the real axis
  have himne : ∀ z ∈ K ∩ riemannZetaZeros, z.im ≠ 0 := by
    intro z hz him
    have hzK : z ∈ K := hz.1
    have hzZ : riemannZeta z = 0 := mem_riemannZetaZeros.mp hz.2
    have hzre : z = (z.re : ℂ) := Complex.ext (by simp) (by simpa using him)
    rw [hzre] at hzZ
    have h0 : (0 : ℝ) < z.re := by
      have : (0 : ℝ) < c + 1 := by linarith
      exact lt_of_lt_of_le this hzK.1
    rcases lt_or_eq_of_le hzK.2.1 with hlt | heq
    · have hneg := (zeta_neg_of_mem_Ioo z.re h0 hlt).1
      rw [hzZ] at hneg
      simp at hneg
    · rw [heq] at hzZ
      simp only [Complex.ofReal_one] at hzZ
      exact riemannZeta_one_ne_zero hzZ
  -- hence a positive uniform lower bound for `|im|` over these zeros
  obtain ⟨ν, hνpos, hν⟩ : ∃ ν > 0, ∀ z ∈ K ∩ riemannZetaZeros, ν ≤ |z.im| := by
    rcases (K ∩ riemannZetaZeros).eq_empty_or_nonempty with hemp | hne
    · refine ⟨1, one_pos, ?_⟩
      intro z hz
      rw [hemp] at hz
      exact absurd hz (by simp)
    · obtain ⟨z0, hz0, hmin⟩ := Set.exists_min_image _ (fun z => |z.im|) hfin hne
      exact ⟨|z0.im|, abs_pos.mpr (himne z0 hz0), hmin⟩
  refine ⟨min ν 1, lt_min hνpos one_pos, fun w hw1 hw2 _ himδ => ?_⟩
  have hwK : w ∈ K := ⟨hw1, hw2, le_of_lt (lt_of_lt_of_le himδ (min_le_right _ _))⟩
  intro hzero
  have hwZ : w ∈ riemannZetaZeros := mem_riemannZetaZeros.mpr hzero
  have hge := hν w ⟨hwK, hwZ⟩
  have himlt : |w.im| < ν := lt_of_lt_of_le himδ (min_le_left _ _)
  linarith

end Work.RHContract.B
