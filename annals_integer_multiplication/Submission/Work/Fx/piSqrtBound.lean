import Mathlib
import Submission.Work.Fx.piDefs
import Submission.Work.Fx.AseqSqrtLower
import Submission.Work.Fx.piAseqSqrtBound
import Submission.Work.Fx.sqrtSubSqrtLe

/-!
# `2^p·π` from the fixed-point nested square-root iteration, to within `1/4`

`Work.Fx.piSqrtBound` compares the fixed-point quantity
`2^(2p+1)·√(2 − aval p p / 2^(2·qq p))` with `2^p·π`.  The estimate is split into

* `Work.Fx.piAseqSqrtBound`: the real model sequence (`√(2 - Aseq p) = 2 sin (π/2^(p+2))`)
  matches `π` to `2^(-p)` after scaling;
* `Work.Fx.piSqrtGap`: the integer iterate `aval p p` moves the radicand by at most
  `4/2^(4p)` (hypothesis `herr`), which — against the lower bound
  `Work.Fx.AseqSqrtLower` (`√(2 - Aseq p) ≥ 1/2^p`) and the Lipschitz estimate
  `Work.Fx.sqrtSubSqrtLe` for `Real.sqrt` — perturbs the answer by at most `1/8`.
-/

set_option autoImplicit false

namespace Work.Fx

/-- Fixed-point deviation, in the division form needed below: the hypothesis `herr`
controls `|2^(2·qq p)·Aseq p - aval p p|` by `4·2^(qq p)`, hence
`|Aseq p - aval p p / 2^(2·qq p)| ≤ 4/2^(4p)`. -/
theorem piSqrtAvalRatio (p : ℕ)
    (herr : |(2 : ℝ) ^ (2 * qq p) * Aseq p - (aval p p : ℝ)| ≤ 4 * (2 : ℝ) ^ qq p) :
    |Aseq p - (aval p p : ℝ) / (2 : ℝ) ^ (2 * qq p)| ≤ 4 / (2 : ℝ) ^ (4 * p) := by
  set Q : ℝ := (2 : ℝ) ^ (2 * qq p) with hQ
  have hQpos : 0 < Q := by rw [hQ]; positivity
  have hdiff : Aseq p - (aval p p : ℝ) / Q = (Q * Aseq p - (aval p p : ℝ)) / Q := by
    rw [sub_div, mul_div_cancel_left₀ _ (ne_of_gt hQpos)]
  rw [hdiff, abs_div, abs_of_pos hQpos]
  refine (div_le_div_of_nonneg_right herr hQpos.le).trans (le_of_eq ?_)
  rw [hQ, show (2 : ℝ) ^ (2 * qq p) = (2 : ℝ) ^ (qq p) * (2 : ℝ) ^ (qq p) by
        rw [← pow_add]; ring]
  rw [mul_div_mul_right 4 ((2 : ℝ) ^ (qq p)) (by positivity : (2 : ℝ) ^ (qq p) ≠ 0)]
  rfl

/-- The square root of the fixed-point radicand is `1/8`-close to the square root of the
real model radicand, after scaling by `2^(2p+1)`. -/
theorem piSqrtGap (p : ℕ) (h100 : 100 ≤ p)
    (herr : |(2 : ℝ) ^ (2 * qq p) * Aseq p - (aval p p : ℝ)| ≤ 4 * (2 : ℝ) ^ qq p) :
    |(2 : ℝ) ^ (2 * p + 1) *
        (Real.sqrt (2 - (aval p p : ℝ) / (2 : ℝ) ^ (2 * qq p)) - Real.sqrt (2 - Aseq p))| ≤ 1 / 8 := by
  set a : ℝ := (aval p p : ℝ) with ha
  set Q : ℝ := (2 : ℝ) ^ (2 * qq p) with hQ
  set δ : ℝ := 1 / (2 : ℝ) ^ p with hδ
  have hδpos : 0 < δ := by rw [hδ]; positivity
  have hdev : |Aseq p - a / Q| ≤ 4 / (2 : ℝ) ^ (4 * p) := piSqrtAvalRatio p herr
  have hxpos : 0 < 2 - Aseq p := two_sub_Aseq_pos p
  have hlow : δ ≤ Real.sqrt (2 - Aseq p) := by
    rw [hδ]
    simpa only [div_pow, one_pow] using AseqSqrtLower p
  have hdx : δ ^ 2 ≤ 2 - Aseq p := by
    have h := mul_le_mul hlow hlow hδpos.le (Real.sqrt_nonneg (2 - Aseq p))
    rwa [← sq, ← sq, Real.sq_sqrt hxpos.le] at h
  have h3 : 4 / (2 : ℝ) ^ (4 * p) ≤ δ ^ 2 := by
    rw [hδ]
    rw [show ((1 : ℝ) / (2 : ℝ) ^ p) ^ 2 = 1 / (2 : ℝ) ^ (2 * p) by
          rw [div_pow, one_pow, ← pow_mul]; congr 1; ring]
    rw [div_le_div_iff₀ (by positivity) (by positivity), one_mul]
    have h4 : (4 : ℝ) ≤ (2 : ℝ) ^ (2 * p) := by
      have h2 : (2 : ℕ) ≤ 2 * p := by omega
      have h := pow_le_pow_right₀ (show (1 : ℝ) ≤ 2 by norm_num) h2
      norm_num at h; exact h
    calc (4 : ℝ) * (2 : ℝ) ^ (2 * p) ≤ (2 : ℝ) ^ (2 * p) * (2 : ℝ) ^ (2 * p) :=
          mul_le_mul_of_nonneg_right h4 (by positivity)
      _ = (2 : ℝ) ^ (4 * p) := by rw [← pow_add]; ring_nf
  have hy0 : 0 ≤ 2 - a / Q := by
    have h1 : a / Q ≤ Aseq p + 4 / (2 : ℝ) ^ (4 * p) := by
      have h2 := (abs_le.mp hdev).1
      linarith
    have h2 : Aseq p ≤ 2 - δ ^ 2 := by linarith
    linarith
  have hxy : |(2 - Aseq p) - (2 - a / Q)| ≤ 4 / (2 : ℝ) ^ (4 * p) := by
    have he : (2 - Aseq p) - (2 - a / Q) = a / Q - Aseq p := by ring
    rw [he, abs_sub_comm]
    exact hdev
  have hstep : |Real.sqrt (2 - Aseq p) - Real.sqrt (2 - a / Q)| ≤ 4 / (2 : ℝ) ^ (3 * p) := by
    refine (sqrtSubSqrtLe (x := 2 - Aseq p) (y := 2 - a / Q) (δ := δ) hδpos hlow hy0).trans ?_
    rw [div_le_iff₀ hδpos]
    refine hxy.trans (le_of_eq ?_)
    rw [hδ, mul_one_div, div_div, ← pow_add, show 3 * p + p = 4 * p by ring]
  have hscale : (2 : ℝ) ^ (2 * p + 1) * (4 / (2 : ℝ) ^ (3 * p)) = 8 / (2 : ℝ) ^ p := by
    rw [← mul_div_assoc, show (4 : ℝ) = 2 ^ 2 by norm_num, ← pow_add,
        show 2 * p + 1 + 2 = 2 * p + 3 by ring, show (8 : ℝ) = 2 ^ 3 by norm_num]
    rw [div_eq_div_iff (by positivity) (by positivity), ← pow_add, ← pow_add]
    congr 1; ring
  have hfin : 8 / (2 : ℝ) ^ p ≤ 1 / 8 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    have h : (2 : ℝ) ^ 6 ≤ (2 : ℝ) ^ p := pow_le_pow_right₀ (by norm_num) (by omega)
    norm_num at h ⊢
    linarith
  calc |(2 : ℝ) ^ (2 * p + 1) * (Real.sqrt (2 - a / Q) - Real.sqrt (2 - Aseq p))|
      = (2 : ℝ) ^ (2 * p + 1) * |Real.sqrt (2 - a / Q) - Real.sqrt (2 - Aseq p)| := by
        rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < (2 : ℝ) ^ (2 * p + 1))]
    _ = (2 : ℝ) ^ (2 * p + 1) * |Real.sqrt (2 - Aseq p) - Real.sqrt (2 - a / Q)| := by
        rw [abs_sub_comm]
    _ ≤ (2 : ℝ) ^ (2 * p + 1) * (4 / (2 : ℝ) ^ (3 * p)) :=
        mul_le_mul_of_nonneg_left hstep (by positivity)
    _ = 8 / (2 : ℝ) ^ p := hscale
    _ ≤ 1 / 8 := hfin

theorem piSqrtBound (p : ℕ) (h100 : 100 ≤ p)
    (herr : |(2 : ℝ) ^ (2 * Work.Fx.qq p) * Work.Fx.Aseq p - (Work.Fx.aval p p : ℝ)|
        ≤ 4 * (2 : ℝ) ^ Work.Fx.qq p) :
    |(2 : ℝ) ^ (2 * p + 1) * Real.sqrt (2 - (Work.Fx.aval p p : ℝ) / (2 : ℝ) ^ (2 * Work.Fx.qq p))
        - (2 : ℝ) ^ p * Real.pi| ≤ 1 / 4 := by
  have hgap := piSqrtGap p h100 herr
  have htrig := piAseqSqrtBound p
  have hab : |(2 : ℝ) ^ (2 * p + 1) * Real.sqrt (2 - (aval p p : ℝ) / (2 : ℝ) ^ (2 * qq p))
      - (2 : ℝ) ^ (2 * p + 1) * Real.sqrt (2 - Aseq p)| ≤ 1 / 8 := by
    rw [← mul_sub]
    exact hgap
  have htri := abs_sub_le ((2 : ℝ) ^ (2 * p + 1) * Real.sqrt (2 - (aval p p : ℝ) / (2 : ℝ) ^ (2 * qq p)))
      ((2 : ℝ) ^ (2 * p + 1) * Real.sqrt (2 - Aseq p)) ((2 : ℝ) ^ p * Real.pi)
  have hsmall : (1 / 2 : ℝ) ^ p ≤ 1 / 8 := by
    have h := pow_le_pow_of_le_one (show (0 : ℝ) ≤ 1 / 2 by norm_num) (by norm_num) (by omega : 3 ≤ p)
    norm_num at h
    exact h
  linarith

end Work.Fx
