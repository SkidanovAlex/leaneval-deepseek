/-
# The support of the modulated Ionescu--Wainger bump `φ_{N,t}`

The KMT bumps `φ_N` (and their modulations `φ_{N,t} = φ_N · e(Nt·)`) are supported in the
frequency window `ℝ_{≤ -Log N + k₁}`: `φ_N(ξ) = η(2^{Log N - k₁} ξ) - η(2^{Log N - k₁ + 1} ξ)`
is a *difference* of two rescalings of the fixed cutoff `η`, which vanishes for `|x| ≥ 1`, so
`φ_{N,t}(ξ) ≠ 0` forces `|ξ| < 2^{k₁ - Log N}`.  This is the support statement that lets the
Ionescu--Wainger multiplier `T^{≤l}_{φ_{N,t}}` be treated as a Fourier multiplier living on the
band `2^{k₁}/N`.

The modulation `φ_{N,t} = φ_N · e(Nt·)` never changes the support, because `e` is nowhere zero
(`e(x) = exp(2πix)` and `Complex.exp` has no zeros).
-/
import Mathlib
import Submission.Work.Analysis.CzShift.Main
import Submission.Work.Analysis.CzShift.exists_isCZSeed_of_fourierInv
import Submission.Work.BourgainPlan.Maximal.main_narrow_taoSetS
import Submission.Work.BourgainPlan.Maximal.mikhlinConvolutionLp
import Submission.Work.KMTAreas.A7.LargeInterface

namespace Work.KMTAreas.A7

/-- Elementary arithmetic of the support bound: if `2^{L-k} |ξ| < 1` then `|ξ| ≤ 2^{k-L}`. -/
private lemma abs_le_of_rpow_mul_lt_one {L : ℝ} {k : ℕ} {ξ : ℝ}
    (h : (2 : ℝ) ^ (L - (k : ℝ)) * |ξ| < 1) : |ξ| ≤ (2 : ℝ) ^ ((k : ℝ) - L) := by
  have hp : (0 : ℝ) < (2 : ℝ) ^ (L - (k : ℝ)) := Real.rpow_pos_of_pos (by norm_num) _
  have h4 : (2 : ℝ) ^ (L - (k : ℝ)) * |ξ| <
      (2 : ℝ) ^ (L - (k : ℝ)) * ((2 : ℝ) ^ (L - (k : ℝ)))⁻¹ := by
    rwa [mul_inv_cancel₀ (ne_of_gt hp)]
  have h5 : |ξ| < ((2 : ℝ) ^ (L - (k : ℝ)))⁻¹ :=
    lt_of_mul_lt_mul_left h4 (le_of_lt hp)
  have h6 : ((2 : ℝ) ^ (L - (k : ℝ)))⁻¹ = (2 : ℝ) ^ ((k : ℝ) - L) := by
    rw [← Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2)]
    congr 1
    ring
  rw [h6] at h5
  exact le_of_lt h5

theorem varphiNt_support_le (k₁ : ℕ) (hk₁ : 1 ≤ k₁) (N : ℕ) (t : ℝ) :
    ∀ ξ : ℝ, Work.KMTAreas.A7.varphiNt N k₁ t ξ ≠ 0 →
      |ξ| ≤ (2 : ℝ) ^ ((k₁ : ℝ) - (Work.Analysis.EndVar.logN N : ℝ)) := by
  intro ξ hξ
  have hk1ne : k₁ ≠ 0 := by omega
  simp only [Work.KMTAreas.A7.varphiNt, Work.KMTAreas.A7.varphiN,
    if_neg hk1ne] at hξ
  obtain ⟨hmain, -⟩ := mul_ne_zero_iff.mp hξ
  have hbor :
      Work.KMTContract.kmtEta ((2 : ℝ) ^ ((Work.Analysis.EndVar.logN N : ℝ) - (k₁ : ℝ)) * ξ) ≠ 0 ∨
        Work.KMTContract.kmtEta
          ((2 : ℝ) ^ ((Work.Analysis.EndVar.logN N : ℝ) - (k₁ : ℝ) + 1) * ξ) ≠ 0 := by
    by_contra h
    push Not at h
    exact hmain (by rw [h.1, h.2, sub_zero])
  rcases hbor with h | h
  · -- the coarse term of the difference is nonzero
    have hlt1 : ¬ (1 ≤ |(2 : ℝ) ^ ((Work.Analysis.EndVar.logN N : ℝ) - (k₁ : ℝ)) * ξ|) :=
      fun hc => h (Work.KMTContract.kmtEta_zero hc)
    have h3 : |(2 : ℝ) ^ ((Work.Analysis.EndVar.logN N : ℝ) - (k₁ : ℝ)) * ξ| < 1 :=
      lt_of_not_ge hlt1
    have hp : (0 : ℝ) < (2 : ℝ) ^ ((Work.Analysis.EndVar.logN N : ℝ) - (k₁ : ℝ)) :=
      Real.rpow_pos_of_pos (by norm_num) _
    rw [abs_mul, abs_of_pos hp] at h3
    exact abs_le_of_rpow_mul_lt_one h3
  · -- the fine term of the difference is nonzero; `2^{L-k₁} ≤ 2^{L-k₁+1}` gives the same bound
    have hlt1 :
        ¬ (1 ≤ |(2 : ℝ) ^ ((Work.Analysis.EndVar.logN N : ℝ) - (k₁ : ℝ) + 1) * ξ|) :=
      fun hc => h (Work.KMTContract.kmtEta_zero hc)
    have h3 : |(2 : ℝ) ^ ((Work.Analysis.EndVar.logN N : ℝ) - (k₁ : ℝ) + 1) * ξ| < 1 :=
      lt_of_not_ge hlt1
    have hp : (0 : ℝ) < (2 : ℝ) ^ ((Work.Analysis.EndVar.logN N : ℝ) - (k₁ : ℝ) + 1) :=
      Real.rpow_pos_of_pos (by norm_num) _
    rw [abs_mul, abs_of_pos hp] at h3
    have hbase : (2 : ℝ) ^ ((Work.Analysis.EndVar.logN N : ℝ) - (k₁ : ℝ)) ≤
        (2 : ℝ) ^ ((Work.Analysis.EndVar.logN N : ℝ) - (k₁ : ℝ) + 1) :=
      (Real.rpow_le_rpow_left_iff (by norm_num : (1 : ℝ) < 2)).mpr (by linarith)
    have h2 : (2 : ℝ) ^ ((Work.Analysis.EndVar.logN N : ℝ) - (k₁ : ℝ)) * |ξ| < 1 :=
      lt_of_le_of_lt (mul_le_mul_of_nonneg_right hbase (abs_nonneg ξ)) h3
    exact abs_le_of_rpow_mul_lt_one h2

end Work.KMTAreas.A7
