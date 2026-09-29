import Mathlib
import Submission.Work.Resample.auDefs
import Submission.Work.Resample.auMLe
import Submission.Work.Resample.sumWtComplex
import Submission.Work.Resample.normSumWtLe
import Submission.Work.Resample.auLTwoMulAddLe
import Submission.Work.Resample.tdivDiscStep

namespace Work.Resample

/-- `auWi` is nonnegative (it is `(1/2α)·e^{−…}`). -/
theorem auWi_nonneg (p α s t k i : ℕ) : 0 ≤ auWi p α s t k i := by
  rw [auWi]
  exact mul_nonneg (div_nonneg zero_le_one (by positivity)) (Real.exp_pos _).le

/-- An element of the fixed-point disc has complex modulus at most `2^p`. -/
theorem normCplxOfInDisc (p : ℕ) (z : ℤ × ℤ) (hz : HvdH.inDisc p z) :
    ‖((z.1 : ℂ) + (z.2 : ℂ) * Complex.I)‖ ≤ (2 : ℝ) ^ p := by
  have hsq : ‖((z.1 : ℂ) + (z.2 : ℂ) * Complex.I)‖ ^ 2
      = (z.1 : ℝ) ^ 2 + (z.2 : ℝ) ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    simp
    ring
  have hzR : (z.1 : ℝ) ^ 2 + (z.2 : ℝ) ^ 2 ≤ ((2 : ℝ) ^ p) ^ 2 := by
    have h : ((z.1 ^ 2 + z.2 ^ 2 : ℤ) : ℝ) ≤ ((4 : ℤ) ^ p : ℝ) := by exact_mod_cast hz
    push_cast at h
    rw [show (4 : ℝ) = (2 : ℝ) ^ 2 by norm_num, ← pow_mul] at h
    calc (z.1 : ℝ) ^ 2 + (z.2 : ℝ) ^ 2 ≤ (2 : ℝ) ^ (2 * p) := h
      _ = ((2 : ℝ) ^ p) ^ 2 := by rw [pow_two, ← pow_add, show p + p = 2 * p by omega]
  have h2 : ‖((z.1 : ℂ) + (z.2 : ℂ) * Complex.I)‖ ^ 2 ≤ ((2 : ℝ) ^ p) ^ 2 := by
    rw [hsq]; exact hzR
  have h3 : |‖((z.1 : ℂ) + (z.2 : ℂ) * Complex.I)‖| ≤ |(2 : ℝ) ^ p| := sq_le_sq.mp h2
  rwa [abs_of_nonneg (norm_nonneg _), abs_of_nonneg (by positivity)] at h3

/-- From `|x - c| ≤ 2` and `0 ≤ c`: `|x| ≤ c + 2`. -/
theorem abs_le_abs_sub_add {x c : ℝ} (hc : 0 ≤ c) (h : |x - c| ≤ 2) : |x| ≤ c + 2 := by
  have h1 := abs_add_le (x - c) c
  rw [sub_add_cancel, abs_of_nonneg hc] at h1
  linarith

-- The output values of auPhi lie in the fixed-point disc.  Given the per-weight accuracy
-- |auWt - 2^p auWi| ≤ 2 (a hypothesis here; it is Work.Resample.auWtErr_asm in
-- Submission/Work/Resample/zz_auwt_asm.lean) and the sharp window row-sum bound Σ_i auWi ≤ 3/4
-- (a hypothesis here; it is Resample/auWiRow):
-- write X + iY = auPhi p α s t w k, so X = tdiv A 2^p, Y = tdiv B 2^p with A + iB = Σ_i W_i z_i,
-- W_i = the computed weight, z_i = w (auJ k i).  Then |W_i| ≤ 2^p auWi + 2, |z_i| ≤ 2^p, hence
-- |X + iY| ≤ |A + iB|/2^p + 2 ≤ Σ_i |W_i| + 2 ≤ (3/4) 2^p + 2 auL p α + 4 < 2^p
-- (use α^2 < p to get auL p α ≤ 2p+2, so 2 auL p α + 4 ≤ 2^p / 4 for p ≥ 100), hence
-- X^2 + Y^2 ≤ 4^p.
theorem auPhiDisc (p α s t : ℕ) (hs : 2 ≤ s) (hst : s < t) (hα : 2 ≤ α) (hp : 100 ≤ p) (hαp : α ^ 2 < p)
    (hwt : ∀ (k i : ℕ), |(Work.Resample.auWt p α t (Work.Resample.auNsq p α s t k i) : ℝ) -
      (2 : ℝ) ^ p * Work.Resample.auWi p α s t k i| ≤ 2)
    (hrow : ∀ k : Fin t, ∑ i ∈ Finset.range (Work.Resample.auL p α), Work.Resample.auWi p α s t (k : ℕ) i ≤ 3 / 4)
    (w : Fin s → ℤ × ℤ) (hw : ∀ j, HvdH.inDisc p (w j)) (k : Fin t) :
    HvdH.inDisc p (Work.Resample.auPhi p α s t w k) := by
  -- resolve the `if auJ … < s` in the definition of `auPhi` (always the `then` branch)
  have hsumA : (∑ i ∈ Finset.range (auL p α),
        auWt p α t (auNsq p α s t (k : ℕ) i) *
          (if h : auJ p α s t (k : ℕ) i < s then w ⟨auJ p α s t (k : ℕ) i, h⟩ else 0).1)
      = ∑ i ∈ Finset.range (auL p α),
        auWt p α t (auNsq p α s t (k : ℕ) i) *
          (w ⟨auJ p α s t (k : ℕ) i, auJ_lt p α s t (k : ℕ) i hs⟩).1 := by
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [dif_pos (auJ_lt p α s t (k : ℕ) i hs)]
  have hsumB : (∑ i ∈ Finset.range (auL p α),
        auWt p α t (auNsq p α s t (k : ℕ) i) *
          (if h : auJ p α s t (k : ℕ) i < s then w ⟨auJ p α s t (k : ℕ) i, h⟩ else 0).2)
      = ∑ i ∈ Finset.range (auL p α),
        auWt p α t (auNsq p α s t (k : ℕ) i) *
          (w ⟨auJ p α s t (k : ℕ) i, auJ_lt p α s t (k : ℕ) i hs⟩).2 := by
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [dif_pos (auJ_lt p α s t (k : ℕ) i hs)]
  have hphi : auPhi p α s t w k =
      (Int.tdiv (∑ i ∈ Finset.range (auL p α), auWt p α t (auNsq p α s t (k : ℕ) i) *
          (w ⟨auJ p α s t (k : ℕ) i, auJ_lt p α s t (k : ℕ) i hs⟩).1) ((2 : ℤ) ^ p),
       Int.tdiv (∑ i ∈ Finset.range (auL p α), auWt p α t (auNsq p α s t (k : ℕ) i) *
          (w ⟨auJ p α s t (k : ℕ) i, auJ_lt p α s t (k : ℕ) i hs⟩).2) ((2 : ℤ) ^ p)) := by
    simp only [auPhi]
    rw [hsumA, hsumB]
  rw [hphi]
  -- the two integer coordinate sums
  set A : ℤ := ∑ i ∈ Finset.range (auL p α), auWt p α t (auNsq p α s t (k : ℕ) i) *
          (w ⟨auJ p α s t (k : ℕ) i, auJ_lt p α s t (k : ℕ) i hs⟩).1 with hA
  set B : ℤ := ∑ i ∈ Finset.range (auL p α), auWt p α t (auNsq p α s t (k : ℕ) i) *
          (w ⟨auJ p α s t (k : ℕ) i, auJ_lt p α s t (k : ℕ) i hs⟩).2 with hB
  -- the abstract data fed to the estimates
  set W : ℕ → ℤ := fun i => auWt p α t (auNsq p α s t (k : ℕ) i) with hWdef
  set β : ℕ → ℝ := fun i => auWi p α s t (k : ℕ) i with hβdef
  set zz : ℕ → ℤ × ℤ := fun i => w ⟨auJ p α s t (k : ℕ) i, auJ_lt p α s t (k : ℕ) i hs⟩ with hzzdef
  set ζ : ℕ → ℂ := fun i => ((zz i).1 : ℂ) + ((zz i).2 : ℂ) * Complex.I with hζdef
  have hAexp : A = ∑ i ∈ Finset.range (auL p α), W i * (zz i).1 := by rw [hA]
  have hBexp : B = ∑ i ∈ Finset.range (auL p α), W i * (zz i).2 := by rw [hB]
  -- the three estimates on the abstract data
  have hβnn : ∀ i ∈ Finset.range (auL p α), 0 ≤ β i := by
    intro i _
    rw [hβdef]
    exact auWi_nonneg p α s t (k : ℕ) i
  have hWle : ∀ i ∈ Finset.range (auL p α), |(W i : ℝ)| ≤ (2 : ℝ)^p * β i + 2 := by
    intro i hi
    have h := hwt (k : ℕ) i
    have hc : (0 : ℝ) ≤ (2 : ℝ)^p * β i := mul_nonneg (by positivity) (hβnn i hi)
    simp only [hWdef, hβdef]
    exact abs_le_abs_sub_add hc h
  have hζle : ∀ i ∈ Finset.range (auL p α), ‖ζ i‖ ≤ (2 : ℝ)^p := by
    intro i _
    have hz : HvdH.inDisc p (zz i) := by rw [hzzdef]; exact hw _
    simpa only [hζdef] using normCplxOfInDisc p (zz i) hz
  have hrowβ : ∑ i ∈ Finset.range (auL p α), β i ≤ 3 / 4 := by
    simpa only [hβdef] using hrow k
  -- triangle inequality: ‖A + iB‖ ≤ 2^p (3/4 · 2^p + 2 auL)
  have h1 : ‖(A : ℂ) + (B : ℂ) * Complex.I‖ ≤
      (2 : ℝ)^p * ((3 / 4) * (2 : ℝ)^p + 2 * ((auL p α : ℕ) : ℝ)) := by
    have hh := normSumWtLe (auL p α) p W ζ β hβnn hWle hζle hrowβ
    have hsum_eq : (∑ i ∈ Finset.range (auL p α), (W i : ℂ) * ζ i) =
        (A : ℂ) + (B : ℂ) * Complex.I := by
      rw [← sumWtComplex (auL p α) W zz, ← hAexp, ← hBexp]
    rwa [hsum_eq] at hh
  have h2p : (0 : ℝ) < (2 : ℝ)^p := by positivity
  -- crude division by 2^p: at most `2` of loss
  have hU : (2 : ℝ)^p * ((3 / 4) * (2 : ℝ)^p + 2 * ((auL p α : ℕ) : ℝ)) / (2 : ℝ)^p + 2
      ≤ (2 : ℝ)^p := by
    have hL := auLTwoMulAddLe p α hp hα hαp
    rw [mul_div_cancel_left₀ _ (ne_of_gt h2p)]
    nlinarith [hL]
  have hXY : ‖((Int.tdiv A ((2:ℤ)^p) : ℤ) : ℂ) + ((Int.tdiv B ((2:ℤ)^p) : ℤ) : ℂ) * Complex.I‖
      ≤ (2 : ℝ)^p :=
    le_trans (tdivDiscStep p A B _ h1) hU
  set X : ℤ := Int.tdiv A ((2:ℤ)^p) with hX
  set Y : ℤ := Int.tdiv B ((2:ℤ)^p) with hY
  -- squaring: X^2 + Y^2 ≤ (2^p)^2 = 4^p
  have hXY' : ‖((X : ℂ) + (Y : ℂ) * Complex.I)‖ ≤ (2 : ℝ)^p := hXY
  have hfin : X ^ 2 + Y ^ 2 ≤ 4 ^ p := by
    have h3 : ‖((X : ℂ) + (Y : ℂ) * Complex.I)‖ ^ 2 = (X : ℝ)^2 + (Y : ℝ)^2 := by
      rw [Complex.sq_norm, Complex.normSq_apply]
      simp
      ring
    have h5 : ‖((X : ℂ) + (Y : ℂ) * Complex.I)‖ ^ 2 ≤ (2 : ℝ)^p * (2 : ℝ)^p := by
      rw [pow_two]
      exact mul_le_mul hXY' hXY' (norm_nonneg _) (by positivity)
    have h6 : (2 : ℝ)^p * (2 : ℝ)^p = (4 : ℝ)^p := by rw [← mul_pow]; norm_num
    have h4 : (X : ℝ)^2 + (Y : ℝ)^2 ≤ (4 : ℝ)^p := by
      rw [h3, h6] at h5
      exact h5
    have hR' : (((X : ℤ)^2 + (Y : ℤ)^2 : ℤ) : ℝ) ≤ (((4 : ℤ)^p : ℤ) : ℝ) := by
      push_cast
      exact h4
    exact_mod_cast hR'
  exact hfin

end Work.Resample
