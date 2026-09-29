import Mathlib
import Submission.Work.Cert.ThetaDefs

/-! # One step of the `B` accumulator: the `Br/Bi` partial-sum invariant

`Bsum q (k+1) = Bsum q k + 2·(-1)^(k+1)·q^((k+1)^2)`, and `bStep` updates the partial-sum
mantissa pair by `(Br,Bi) ↦ (Br,Bi) + 2·sg·(psr,psi)` with `sg = if n % 2 = 1 then -1 else 1`.
So if the current pair encloses `Bsum q k` to within `Bd2 k/S` and the step pair `(a,b)`
(`psr,psi`) encloses `q^((k+1)^2)` to within `8(k+1)^2/S`, the updated pair encloses `Bsum q (k+1)`
to within

  `Bd2 k/S + 2·(8(k+1)^2/S) = (Bd2 k + 16(k+1)^2)/S ≤ (Bd2 k + 16(k+1)^2 + 1)/S = Bd2 (k+1)/S`,

the slack `+1` being the per-step rounding allowance of `bStep`. -/

namespace Work.Cert

open Complex Finset

noncomputable section

/-- The `B` partial sum satisfies the recursion `Bsum q (k+1) = Bsum q k + 2·(-1)^(k+1)·q^((k+1)^2)`. -/
lemma bstep_Br_Bsum_succ (q : ℂ) (k : ℕ) :
    Bsum q (k+1) = Bsum q k + 2 * (-1:ℂ)^(k+1) * q^((k+1)^2) := by
  simp only [Bsum, Finset.sum_range_succ]
  ring

/-- The rounding budget of the `B` loop accumulates the per-step allowance `16(j+1)^2+1`. -/
lemma bstep_Br_Bd2_succ (k : ℕ) :
    Bd2 (k+1) = Bd2 k + (((16 * (k+1)^2 + 1 : ℕ)) : ℝ) := by
  simp only [Bd2, Finset.sum_range_succ]

/-- `cx` is `ℤ`-homogeneous in the mantissa pair: `cx (m·x) (m·y) = m·cx x y`. -/
lemma bstep_Br_cx_int_smul (m : ℤ) (x y : ℤ) : cx (m * x) (m * y) = (m : ℂ) * cx x y := by
  simp only [cx]; push_cast; ring

/-- The step sign `if n % 2 = 1 then -1 else 1` is `(-1)^n`, in the sense needed for `Bsum`. -/
lemma bstep_Br_sign_cast (k : ℕ) :
    (((2 * (if (k+1) % 2 = 1 then (-1:ℤ) else 1) : ℤ)) : ℂ) = 2 * (-1:ℂ)^(k+1) := by
  rcases Nat.mod_two_eq_zero_or_one (k+1) with h | h
  · have hev : Even (k+1) := Nat.even_iff.mpr h
    rw [h, if_neg (by decide), Even.neg_one_pow hev]
    norm_num
  · have hod : Odd (k+1) := Nat.odd_iff.mpr h
    rw [h, if_pos rfl, Odd.neg_one_pow hod]
    norm_num

theorem bstep_Br_le (qr qi : ℤ) {c d a b : ℤ} {k : ℕ}
    (h6 : ‖cx c d - Bsum (qc qr qi) k‖ ≤ Bd2 k / ((S:ℝ)))
    (hp : ‖cx a b - (qc qr qi) ^ ((k+1)*(k+1))‖ ≤ 8 * ((((k+1)*(k+1) : ℕ)) : ℝ) / ((S:ℝ))) :
    ‖cx (c + 2 * (if (k+1) % 2 = 1 then (-1:ℤ) else 1) * a)
          (d + 2 * (if (k+1) % 2 = 1 then (-1:ℤ) else 1) * b) - Bsum (qc qr qi) (k+1)‖
      ≤ Bd2 (k+1) / ((S:ℝ)) := by
  set e : ℤ := (if (k+1) % 2 = 1 then (-1:ℤ) else 1) with he
  have hSp : (0:ℝ) < (S:ℝ) := thS_pos
  have hB := bstep_Br_Bsum_succ (qc qr qi) k
  have he' : ((2 * e : ℤ) : ℂ) = 2 * (-1:ℂ)^(k+1) := by rw [he]; exact bstep_Br_sign_cast k
  have hn2 : ‖((2 * e : ℤ) : ℂ)‖ = 2 := by rw [he']; simp
  have hcx : cx (c + 2 * e * a) (d + 2 * e * b) = cx c d + ((2 * e : ℤ) : ℂ) * cx a b := by
    rw [cx_add c d ((2*e)*a) ((2*e)*b), bstep_Br_cx_int_smul (2*e) a b]
  have hdecomp : cx (c + 2 * e * a) (d + 2 * e * b) - Bsum (qc qr qi) (k+1)
      = (cx c d - Bsum (qc qr qi) k)
        + ((2 * e : ℤ) : ℂ) * (cx a b - (qc qr qi) ^ ((k+1)*(k+1))) := by
    rw [hB, hcx, he']; ring
  have h2 : ‖((2 * e:ℤ):ℂ) * (cx a b - (qc qr qi)^((k+1)*(k+1)))‖
      ≤ 2 * (8 * ((((k+1)*(k+1):ℕ)):ℝ) / (S:ℝ)) := by
    rw [norm_mul, hn2]
    exact mul_le_mul_of_nonneg_left hp (by norm_num)
  have hcast : (((16 * (k+1)^2 + 1 : ℕ)) : ℝ) = 16 * ((((k+1)*(k+1) : ℕ)) : ℝ) + 1 := by
    push_cast; ring
  have hmono : Bd2 k / (S:ℝ) + 2 * (8 * ((((k+1)*(k+1):ℕ)):ℝ) / (S:ℝ)) ≤ Bd2 (k+1) / (S:ℝ) := by
    set X : ℝ := ((((k+1)*(k+1) : ℕ)) : ℝ) with hX
    have hXeq : 2 * (8 * X / (S:ℝ)) = 16 * X / (S:ℝ) := by ring
    rw [hXeq, bstep_Br_Bd2_succ k, hcast]
    rw [show Bd2 k + (16 * X + 1) = (Bd2 k + 16 * X) + 1 by ring]
    rw [add_div, ← add_div]
    exact le_add_of_nonneg_right (div_nonneg zero_le_one (le_of_lt hSp))
  calc ‖cx (c + 2 * e * a) (d + 2 * e * b) - Bsum (qc qr qi) (k+1)‖
      = ‖(cx c d - Bsum (qc qr qi) k)
          + ((2 * e:ℤ):ℂ) * (cx a b - (qc qr qi)^((k+1)*(k+1)))‖ := by rw [hdecomp]
    _ ≤ ‖cx c d - Bsum (qc qr qi) k‖
          + ‖((2 * e:ℤ):ℂ) * (cx a b - (qc qr qi)^((k+1)*(k+1)))‖ := norm_add_le _ _
    _ ≤ Bd2 k / (S:ℝ) + 2 * (8 * ((((k+1)*(k+1):ℕ)):ℝ) / (S:ℝ)) := add_le_add h6 h2
    _ ≤ Bd2 (k+1) / (S:ℝ) := hmono

end

end Work.Cert
