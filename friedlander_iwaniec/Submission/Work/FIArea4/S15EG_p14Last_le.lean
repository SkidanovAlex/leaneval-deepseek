import Mathlib
import Submission.Work.FIArea4.S15EGDefs
import Submission.Work.FIArea4.A4varbounds

namespace Work.FIArea4

noncomputable section

/-!
# The last term of the FI §14 bracket at the §15 support box

`p14Last R S ε = (R+S)^{1/12}(RS)^{11/12+ε}` is evaluated at the support box
`R = S15EG_Re Pa e`, `S = S15EG_Se Pa` of the §15 stratum arrays, which is bounded by
`(5/2)√N` in each variable.  Hence
`p14Last R S ε ≤ 5^{1/12}(25/4)^{11/12+ε} · N^{23/24+ε}`, and the numerical constant
`5^{1/12}(25/4)^{11/12+1/4000} ≤ (32/25)(25/4) = 8` gives the stated bound.
-/

/-- The numerical constant: `5^{1/12}(25/4)^{11/12+1/4000} ≤ 8`.  It follows from
`5^{1/12} ≤ 32/25` (i.e. `5 ≤ (32/25)^{12}`) and `(25/4)^{11/12+1/4000} ≤ 25/4`
(the exponent is `≤ 1` and the base is `≥ 1`). -/
lemma S15EG_p14const :
    (5 : ℝ) ^ ((1 : ℝ) / 12) * ((25 : ℝ) / 4) ^ ((11 : ℝ) / 12 + (1 : ℝ) / 4000) ≤ 8 := by
  have h1 : (5 : ℝ) ≤ ((32 : ℝ) / 25) ^ (12 : ℕ) := by norm_num
  have hA : (5 : ℝ) ^ ((1 : ℝ) / 12) ≤ (32 : ℝ) / 25 := by
    calc (5 : ℝ) ^ ((1 : ℝ) / 12)
        ≤ (((32 : ℝ) / 25) ^ (12 : ℕ)) ^ ((1 : ℝ) / 12) :=
          Real.rpow_le_rpow (by norm_num) h1 (by norm_num)
      _ = ((32 : ℝ) / 25) ^ (((12 : ℕ) : ℝ) * ((1 : ℝ) / 12)) := by
          rw [← Real.rpow_natCast (x := (32:ℝ)/25) (n := 12)]
          exact (Real.rpow_mul (by norm_num) ((12:ℕ):ℝ) ((1:ℝ)/12)).symm
      _ = ((32 : ℝ) / 25) ^ (1 : ℝ) := by norm_num
      _ = (32 : ℝ) / 25 := Real.rpow_one _
  have hB : ((25 : ℝ) / 4) ^ ((11 : ℝ) / 12 + (1 : ℝ) / 4000) ≤ (25 : ℝ) / 4 := by
    calc ((25 : ℝ) / 4) ^ ((11 : ℝ) / 12 + (1 : ℝ) / 4000)
        ≤ ((25 : ℝ) / 4) ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
      _ = (25 : ℝ) / 4 := Real.rpow_one _
  calc (5 : ℝ) ^ ((1 : ℝ) / 12) * ((25 : ℝ) / 4) ^ ((11 : ℝ) / 12 + (1 : ℝ) / 4000)
      ≤ ((32 : ℝ) / 25) * ((25 : ℝ) / 4) :=
        mul_le_mul hA hB (Real.rpow_nonneg (by norm_num) _) (by norm_num)
    _ = 8 := by norm_num

/-- The §15 support box is dominated by `(5/2)√N` in each variable: in particular
`S15EG_Re Pa e + S15EG_Se Pa ≤ 5√N` and `S15EG_Re Pa e * S15EG_Se Pa ≤ (25/4)N`. -/
lemma S15EG_p14Last_box (Pa : Work.FITop.Params) (e : ℕ) :
    (S15EG_Re Pa e : ℝ) + (S15EG_Se Pa : ℝ) ≤ 5 * Real.sqrt Pa.N
      ∧ (S15EG_Re Pa e : ℝ) * (S15EG_Se Pa : ℝ) ≤ ((25 : ℝ) / 4) * Pa.N := by
  have hN1 : (1 : ℝ) ≤ Pa.N := Pa.hN1
  have ht1 : (1 : ℝ) ≤ Real.sqrt Pa.N := Real.one_le_sqrt.mpr hN1
  have hK : (S15EG_K Pa : ℝ) ≤ 2 * Real.sqrt Pa.N + 1 := S15EG_K_le_two_sqrt_add Pa
  have hSe : (S15EG_Se Pa : ℝ) ≤ (5 : ℝ) / 2 * Real.sqrt Pa.N := by
    rw [S15EG_Se]
    push_cast
    have hcast : ((S15EG_K Pa / 2 : ℕ) : ℝ) ≤ (S15EG_K Pa : ℝ) / 2 := Nat.cast_div_le
    linarith
  have hRe : (S15EG_Re Pa e : ℝ) ≤ (5 : ℝ) / 2 * Real.sqrt Pa.N := by
    have hle : S15EG_Re Pa e ≤ S15EG_Se Pa := by
      rw [S15EG_Re, S15EG_Se]
      have hdiv : S15EG_K Pa / (2 * e) ≤ S15EG_K Pa / 2 := by
        rcases Nat.eq_zero_or_pos e with h | h
        · subst h; simp
        · exact Nat.div_le_div_left (by omega) (by norm_num)
      omega
    exact le_trans (by exact_mod_cast hle) hSe
  have hS0 : (0 : ℝ) ≤ (S15EG_Se Pa : ℝ) := Nat.cast_nonneg _
  have ht0 : (0 : ℝ) ≤ Real.sqrt Pa.N := Real.sqrt_nonneg _
  have htsq : Real.sqrt Pa.N * Real.sqrt Pa.N = Pa.N := by
    rw [← sq]
    exact Real.sq_sqrt (le_trans zero_le_one hN1)
  constructor
  · linarith
  · have hm := mul_le_mul hRe hSe hS0 (by positivity)
    nlinarith [hm, htsq]

/-- The assembly: if the support box satisfies the two bounds of `S15EG_p14Last_box`, then the
last term of the §14 bracket at that box is at most `8·N^{23/24+1/4000}`. -/
theorem S15EG_p14Last_le (Pa : Work.FITop.Params) (e : ℕ) :
    Work.FIArea4.p14Last (Work.FIArea4.S15EG_Re Pa e) (Work.FIArea4.S15EG_Se Pa) ((1 : ℝ) / 4000)
      ≤ 8 * Pa.N ^ ((23 : ℝ) / 24 + (1 : ℝ) / 4000) := by
  obtain ⟨hsum, hprod⟩ := S15EG_p14Last_box Pa e
  have hN1 : (1 : ℝ) ≤ Pa.N := Pa.hN1
  have hNpos : (0 : ℝ) < Pa.N := by linarith
  have hN0 : (0 : ℝ) ≤ Pa.N := le_of_lt hNpos
  have ht0 : (0 : ℝ) ≤ Real.sqrt Pa.N := Real.sqrt_nonneg _
  have h1 : (((S15EG_Re Pa e : ℝ) + (S15EG_Se Pa : ℝ)) ^ ((1 : ℝ) / 12))
      ≤ (5 * Real.sqrt Pa.N) ^ ((1 : ℝ) / 12) :=
    Real.rpow_le_rpow (by positivity) hsum (by norm_num)
  have h2 : (((S15EG_Re Pa e : ℝ) * (S15EG_Se Pa : ℝ)) ^ ((11 : ℝ) / 12 + (1 : ℝ) / 4000))
      ≤ (((25 : ℝ) / 4) * Pa.N) ^ ((11 : ℝ) / 12 + (1 : ℝ) / 4000) :=
    Real.rpow_le_rpow (by positivity) hprod (by positivity)
  have h5 : (5 * Real.sqrt Pa.N) ^ ((1 : ℝ) / 12)
      = (5 : ℝ) ^ ((1 : ℝ) / 12) * Pa.N ^ ((1 : ℝ) / 24) := by
    rw [Real.mul_rpow (by norm_num) ht0]
    congr 1
    rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hN0]
    norm_num
  have h6 : (((25 : ℝ) / 4) * Pa.N) ^ ((11 : ℝ) / 12 + (1 : ℝ) / 4000)
      = ((25 : ℝ) / 4) ^ ((11 : ℝ) / 12 + (1 : ℝ) / 4000)
        * Pa.N ^ ((11 : ℝ) / 12 + (1 : ℝ) / 4000) :=
    Real.mul_rpow (by norm_num) hN0
  have h7 : Pa.N ^ ((1 : ℝ) / 24) * Pa.N ^ ((11 : ℝ) / 12 + (1 : ℝ) / 4000)
      = Pa.N ^ ((23 : ℝ) / 24 + (1 : ℝ) / 4000) := by
    rw [← Real.rpow_add hNpos]
    congr 1
    norm_num
  rw [p14Last]
  calc ((S15EG_Re Pa e : ℝ) + (S15EG_Se Pa : ℝ)) ^ ((1 : ℝ) / 12)
        * ((S15EG_Re Pa e : ℝ) * (S15EG_Se Pa : ℝ)) ^ ((11 : ℝ) / 12 + (1 : ℝ) / 4000)
      ≤ (5 * Real.sqrt Pa.N) ^ ((1 : ℝ) / 12)
        * (((25 : ℝ) / 4) * Pa.N) ^ ((11 : ℝ) / 12 + (1 : ℝ) / 4000) :=
        mul_le_mul h1 h2 (by positivity) (by positivity)
    _ = ((5 : ℝ) ^ ((1 : ℝ) / 12) * ((25 : ℝ) / 4) ^ ((11 : ℝ) / 12 + (1 : ℝ) / 4000))
          * (Pa.N ^ ((1 : ℝ) / 24) * Pa.N ^ ((11 : ℝ) / 12 + (1 : ℝ) / 4000)) := by
        rw [h5, h6]; ring
    _ = ((5 : ℝ) ^ ((1 : ℝ) / 12) * ((25 : ℝ) / 4) ^ ((11 : ℝ) / 12 + (1 : ℝ) / 4000))
          * Pa.N ^ ((23 : ℝ) / 24 + (1 : ℝ) / 4000) := by rw [h7]
    _ ≤ 8 * Pa.N ^ ((23 : ℝ) / 24 + (1 : ℝ) / 4000) :=
        mul_le_mul_of_nonneg_right S15EG_p14const (Real.rpow_nonneg hN0 _)

end

end Work.FIArea4
