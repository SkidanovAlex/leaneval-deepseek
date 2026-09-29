import Mathlib
import Submission.Work.CNum.Fx
import Submission.Work.CNum.MemIvS
import Submission.Work.CNum.IsqrtSpec

/-!
# `Work.CNum.ExpAux.qcos_qsin_mem`

Soundness of the table entries `qcos q`, `qsin q` of `Work.CNum.Fx` for `q ≤ 4`:

`qcos q` encloses `cos (q·π/4)` and `qsin q` encloses `sin (q·π/4)`.

The only non-trivial entries are `q = 1` and `q = 3`, where the interval is `rt2 = IvS (ratIv 1 2)`
(up to sign), i.e. the mantissa-level square root of `1/2`; soundness there is `MemIvS`, the
specification of the binary-search integer square root.  All other entries are exact rational
point intervals.
-/

namespace Work.CNum.ExpAux

open Work.ANum

/-- `√(1/2) = √2/2`. -/
lemma sqrt_half : Real.sqrt (1 / 2) = Real.sqrt 2 / 2 := by
  rw [Real.sqrt_div (by norm_num : (0:ℝ) ≤ 1), Real.sqrt_one]
  rw [div_eq_div_iff (by positivity) (by norm_num : (2:ℝ) ≠ 0)]
  rw [one_mul, ← pow_two, Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)]

/-- `ratIv 1 2` is the point interval at the mantissa `SC / 2`. -/
lemma ratIv_one_two : ratIv 1 2 = Iv.pt (SC / 2) := by
  norm_num [ratIv, Iv.pt, SC]

/-- The mantissa-level `√(1/2)` interval `rt2 = IvS (ratIv 1 2)` encloses `√2/2`. -/
lemma rt2_mem : Iv.Mem rt2 (Real.sqrt 2 / 2) := by
  have hmem := MemIvS (I := ratIv 1 2) (x := (1:ℝ)/2)
    (by rw [ratIv_one_two]; simpa [Iv.m2r_SC_half] using Iv.mem_pt (SC / 2))
    (by rw [ratIv_one_two]; norm_num [Iv.pt, Iv.m2r_SC_half])
    (by rw [ratIv_one_two]; norm_num [Iv.pt, SC]; try decide)
  rw [sqrt_half] at hmem
  exact hmem

/-- `ratIv p 1` is the point interval at the integer `p`. -/
lemma mem_ratIv_one (p : ℤ) : (ratIv p 1).Mem (p : ℝ) := by
  constructor
  · show m2r (ratIv p 1).lo ≤ (p : ℝ)
    have h : (ratIv p 1).lo = p * SC := by
      show Int.ediv (p * SC) ((1:ℕ):ℤ) = p * SC
      exact Int.ediv_one (p * SC)
    rw [h, m2r_mul, m2r_SC, mul_one, mul_comm, Iv.m2r_mul_SC]
  · show (p : ℝ) ≤ m2r (ratIv p 1).hi
    have h : (ratIv p 1).hi = p * SC := by
      show -Int.ediv (-(p * SC)) ((1:ℕ):ℤ) = p * SC
      have h1 : Int.ediv (-(p * SC)) ((1:ℕ):ℤ) = -(p * SC) := Int.ediv_one (-(p * SC))
      rw [h1, neg_neg]
    rw [h, m2r_mul, m2r_SC, mul_one, mul_comm, Iv.m2r_mul_SC]

theorem qcos_qsin_mem (q : ℕ) (hq : q ≤ 4) : Work.ANum.Iv.Mem (Work.CNum.qcos q) (Real.cos ((q : ℝ) * Real.pi / 4)) ∧ Work.ANum.Iv.Mem (Work.CNum.qsin q) (Real.sin ((q : ℝ) * Real.pi / 4)) := by
  interval_cases q
  · simp only [Work.CNum.qcos, Work.CNum.qsin]
    refine ⟨?_, ?_⟩
    · rw [show ((0:ℕ):ℝ) * Real.pi / 4 = 0 by ring, Real.cos_zero]
      simpa using mem_ratIv_one 1
    · rw [show ((0:ℕ):ℝ) * Real.pi / 4 = 0 by ring, Real.sin_zero]
      simpa using mem_ratIv_one 0
  · simp only [Work.CNum.qcos, Work.CNum.qsin]
    refine ⟨?_, ?_⟩
    · rw [show ((1:ℕ):ℝ) * Real.pi / 4 = Real.pi / 4 by ring, Real.cos_pi_div_four]
      exact rt2_mem
    · rw [show ((1:ℕ):ℝ) * Real.pi / 4 = Real.pi / 4 by ring, Real.sin_pi_div_four]
      exact rt2_mem
  · simp only [Work.CNum.qcos, Work.CNum.qsin]
    refine ⟨?_, ?_⟩
    · rw [show ((2:ℕ):ℝ) * Real.pi / 4 = Real.pi / 2 by ring, Real.cos_pi_div_two]
      simpa using mem_ratIv_one 0
    · rw [show ((2:ℕ):ℝ) * Real.pi / 4 = Real.pi / 2 by ring, Real.sin_pi_div_two]
      simpa using mem_ratIv_one 1
  · simp only [Work.CNum.qcos, Work.CNum.qsin]
    refine ⟨?_, ?_⟩
    · rw [show ((3:ℕ):ℝ) * Real.pi / 4 = Real.pi - Real.pi / 4 by ring, Real.cos_pi_sub,
        Real.cos_pi_div_four]
      exact Iv.mem_neg rt2_mem
    · rw [show ((3:ℕ):ℝ) * Real.pi / 4 = Real.pi - Real.pi / 4 by ring, Real.sin_pi_sub,
        Real.sin_pi_div_four]
      exact rt2_mem
  · simp only [Work.CNum.qcos, Work.CNum.qsin]
    refine ⟨?_, ?_⟩
    · rw [show ((4:ℕ):ℝ) * Real.pi / 4 = Real.pi by ring, Real.cos_pi]
      simpa using mem_ratIv_one (-1)
    · rw [show ((4:ℕ):ℝ) * Real.pi / 4 = Real.pi by ring, Real.sin_pi]
      simpa using mem_ratIv_one 0

end Work.CNum.ExpAux
