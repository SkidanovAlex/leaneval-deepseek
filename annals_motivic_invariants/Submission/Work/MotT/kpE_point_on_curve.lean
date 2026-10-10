import Mathlib
import Submission.Work.MotT.KleinParamData
import Submission.Work.MotC2.Translation
import Submission.Work.Reflect.PolyId
set_option maxRecDepth 100000

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.MotT

theorem kpE_point_on_curve (L : Type) [Field L] (u w d ζ : L) (hu : u ≠ 0) (hw : w ≠ 0)
    (h5 : (5 : L) ≠ 0) (hwd : w = 2 * u ^(5:ℕ) - 1) (hd : d = u ^(10:ℕ) - 11 * u ^(5:ℕ) - 1)
    (hζ : ζ ^(4:ℕ) + ζ ^(3:ℕ) + ζ ^(2:ℕ) + ζ + 1 = 0) :
    (let xq : L := -d * ((3 * u ^(5:ℕ) + 1) + w * (ζ ^(2:ℕ) + ζ ^(3:ℕ))) / (125 * u ^(4:ℕ) * w)
     let yq : L := -d * ((3 * u ^(5:ℕ) + 1) * (1 + ζ ^(3:ℕ)) + (u ^(5:ℕ) + 2) * (ζ + ζ ^(2:ℕ))) / (625 * u ^(6:ℕ))
     let a1 : L := -(3 * u ^(5:ℕ) + 1) / (5 * u ^(2:ℕ))
     let a2 : L := -(29 * u ^(15:ℕ) + 59 * u ^(10:ℕ) + 63 * u ^(5:ℕ) - 3) / (125 * u ^(4:ℕ) * w)
     let a3 : L := d ^(2:ℕ) / (625 * u ^(6:ℕ) * w)
     let a4 : L := d ^(2:ℕ) * (27 * u ^(10:ℕ) + 28 * u ^(5:ℕ) - 2) / (15625 * u ^(8:ℕ) * w ^(2:ℕ))
     let a6 : L := -(7 * u ^(5:ℕ) - 1) * d ^(4:ℕ) / (1953125 * u ^(12:ℕ) * w ^(3:ℕ))
     yq ^(2:ℕ) + a1 * xq * yq + a3 * yq = xq ^(3:ℕ) + a2 * xq ^(2:ℕ) + a4 * xq + a6) := by
  dsimp only
  set X : L := -d * ((3 * u ^(5:ℕ) + 1) + w * (ζ ^(2:ℕ) + ζ ^(3:ℕ))) with hX
  set Y : L := -d * ((3 * u ^(5:ℕ) + 1) * (1 + ζ ^(3:ℕ)) + (u ^(5:ℕ) + 2) * (ζ + ζ ^(2:ℕ))) with hY
  have hζ4 : ζ ^(4:ℕ) = -(1 + ζ + ζ ^(2:ℕ) + ζ ^(3:ℕ)) := by linear_combination hζ
  have hζ5 : ζ ^(5:ℕ) = 1 := by linear_combination (ζ - 1) * hζ
  have hζ6 : ζ ^(6:ℕ) = ζ := by rw [show ζ ^(6:ℕ) = ζ ^(5:ℕ) * ζ by ring, hζ5, one_mul]
  have hζ7 : ζ ^(7:ℕ) = ζ ^(2:ℕ) := by rw [show ζ ^(7:ℕ) = ζ ^(5:ℕ) * ζ ^(2:ℕ) by ring, hζ5, one_mul]
  have hζ8 : ζ ^(8:ℕ) = ζ ^(3:ℕ) := by rw [show ζ ^(8:ℕ) = ζ ^(5:ℕ) * ζ ^(3:ℕ) by ring, hζ5, one_mul]
  have hζ9 : ζ ^(9:ℕ) = ζ ^(4:ℕ) := by rw [show ζ ^(9:ℕ) = ζ ^(5:ℕ) * ζ ^(4:ℕ) by ring, hζ5, one_mul]
  have hclear : 5 * w ^(3:ℕ) * Y ^(2:ℕ) + 5 * w ^(2:ℕ) * (-(3 * u ^(5:ℕ) + 1)) * X * Y + 5 * w ^(2:ℕ) * d ^(2:ℕ) * Y
      = X ^(3:ℕ) + (-(29 * u ^(15:ℕ) + 59 * u ^(10:ℕ) + 63 * u ^(5:ℕ) - 3)) * X ^(2:ℕ)
        + (d ^(2:ℕ) * (27 * u ^(10:ℕ) + 28 * u ^(5:ℕ) - 2)) * X + (-(7 * u ^(5:ℕ) - 1) * d ^(4:ℕ)) := by
    rw [hX, hY, hwd, hd]
    ring_nf
    rw [hζ9, hζ8, hζ7, hζ6, hζ5, hζ4]
    ring_nf
  have h5ne : (5 : L) ≠ 0 := h5
  have h125ne : (125 : L) ≠ 0 := by rw [show (125 : L) = 5 ^(3:ℕ) by norm_num]; exact pow_ne_zero 3 h5ne
  have h625ne : (625 : L) ≠ 0 := by rw [show (625 : L) = 5 ^(4:ℕ) by norm_num]; exact pow_ne_zero 4 h5ne
  have h15625ne : (15625 : L) ≠ 0 := by
    rw [show (15625 : L) = 5 ^(6:ℕ) by norm_num]; exact pow_ne_zero 6 h5ne
  have h1953125ne : (1953125 : L) ≠ 0 := by
    rw [show (1953125 : L) = 5 ^(9:ℕ) by norm_num]; exact pow_ne_zero 9 h5ne
  have hU1 : (125 * u ^(4:ℕ) * w : L) ≠ 0 := mul_ne_zero (mul_ne_zero h125ne (pow_ne_zero 4 hu)) hw
  have hU2 : (625 * u ^(6:ℕ) : L) ≠ 0 := mul_ne_zero h625ne (pow_ne_zero 6 hu)
  have hU3 : (5 * u ^(2:ℕ) : L) ≠ 0 := mul_ne_zero h5ne (pow_ne_zero 2 hu)
  have hU5 : (625 * u ^(6:ℕ) * w : L) ≠ 0 := mul_ne_zero hU2 hw
  have hU6 : (15625 * u ^(8:ℕ) * w ^(2:ℕ) : L) ≠ 0 :=
    mul_ne_zero (mul_ne_zero h15625ne (pow_ne_zero 8 hu)) (pow_ne_zero 2 hw)
  have hU7 : (1953125 * u ^(12:ℕ) * w ^(3:ℕ) : L) ≠ 0 :=
    mul_ne_zero (mul_ne_zero h1953125ne (pow_ne_zero 12 hu)) (pow_ne_zero 3 hw)
  have h1 : (1953125 : L) * u ^(12:ℕ) * w ^(3:ℕ) * (Y / (625 * u ^(6:ℕ))) ^(2:ℕ) = 5 * w ^(3:ℕ) * Y ^(2:ℕ) := by
    rw [div_pow, ← mul_div_assoc, div_eq_iff (pow_ne_zero 2 hU2)]
    first | refl_ring1 | ring
  have h2 : (1953125 : L) * u ^(12:ℕ) * w ^(3:ℕ) *
        ((-(3 * u ^(5:ℕ) + 1) / (5 * u ^(2:ℕ))) * (X / (125 * u ^(4:ℕ) * w)) * (Y / (625 * u ^(6:ℕ))))
      = 5 * w ^(2:ℕ) * (-(3 * u ^(5:ℕ) + 1)) * X * Y := by
    rw [div_mul_div_comm, div_mul_div_comm, ← mul_div_assoc,
      div_eq_iff (mul_ne_zero (mul_ne_zero hU3 hU1) hU2)]
    first | refl_ring1 | ring
  have h3 : (1953125 : L) * u ^(12:ℕ) * w ^(3:ℕ) * ((d ^(2:ℕ) / (625 * u ^(6:ℕ) * w)) * (Y / (625 * u ^(6:ℕ))))
      = 5 * w ^(2:ℕ) * d ^(2:ℕ) * Y := by
    rw [div_mul_div_comm, ← mul_div_assoc, div_eq_iff (mul_ne_zero hU5 hU2)]
    first | refl_ring1 | ring
  have h4 : (1953125 : L) * u ^(12:ℕ) * w ^(3:ℕ) * (X / (125 * u ^(4:ℕ) * w)) ^(3:ℕ) = X ^(3:ℕ) := by
    rw [div_pow, ← mul_div_assoc, div_eq_iff (pow_ne_zero 3 hU1)]
    first | refl_ring1 | ring
  have h5' : (1953125 : L) * u ^(12:ℕ) * w ^(3:ℕ) *
        ((-(29 * u ^(15:ℕ) + 59 * u ^(10:ℕ) + 63 * u ^(5:ℕ) - 3) / (125 * u ^(4:ℕ) * w)) *
          (X / (125 * u ^(4:ℕ) * w)) ^(2:ℕ))
      = (-(29 * u ^(15:ℕ) + 59 * u ^(10:ℕ) + 63 * u ^(5:ℕ) - 3)) * X ^(2:ℕ) := by
    rw [div_pow, div_mul_div_comm, ← mul_div_assoc, div_eq_iff (mul_ne_zero hU1 (pow_ne_zero 2 hU1))]
    first | refl_ring1 | ring
  have h6 : (1953125 : L) * u ^(12:ℕ) * w ^(3:ℕ) *
        ((d ^(2:ℕ) * (27 * u ^(10:ℕ) + 28 * u ^(5:ℕ) - 2) / (15625 * u ^(8:ℕ) * w ^(2:ℕ))) * (X / (125 * u ^(4:ℕ) * w)))
      = (d ^(2:ℕ) * (27 * u ^(10:ℕ) + 28 * u ^(5:ℕ) - 2)) * X := by
    rw [div_mul_div_comm, ← mul_div_assoc, div_eq_iff (mul_ne_zero hU6 hU1)]
    first | refl_ring1 | ring
  have h7 : (1953125 : L) * u ^(12:ℕ) * w ^(3:ℕ) * (-(7 * u ^(5:ℕ) - 1) * d ^(4:ℕ) / (1953125 * u ^(12:ℕ) * w ^(3:ℕ)))
      = -(7 * u ^(5:ℕ) - 1) * d ^(4:ℕ) := by
    rw [← mul_div_assoc, div_eq_iff hU7]
    first | refl_ring1 | ring
  have hL : (1953125 : L) * u ^(12:ℕ) * w ^(3:ℕ) *
        ((Y / (625 * u ^(6:ℕ))) ^(2:ℕ) + ((-(3 * u ^(5:ℕ) + 1) / (5 * u ^(2:ℕ))) * (X / (125 * u ^(4:ℕ) * w)) *
            (Y / (625 * u ^(6:ℕ)))) + (d ^(2:ℕ) / (625 * u ^(6:ℕ) * w) * (Y / (625 * u ^(6:ℕ)))))
      = 5 * w ^(3:ℕ) * Y ^(2:ℕ) + 5 * w ^(2:ℕ) * (-(3 * u ^(5:ℕ) + 1)) * X * Y + 5 * w ^(2:ℕ) * d ^(2:ℕ) * Y := by
    rw [show (1953125 : L) * u ^(12:ℕ) * w ^(3:ℕ) *
          ((Y / (625 * u ^(6:ℕ))) ^(2:ℕ) + ((-(3 * u ^(5:ℕ) + 1) / (5 * u ^(2:ℕ))) * (X / (125 * u ^(4:ℕ) * w)) *
              (Y / (625 * u ^(6:ℕ)))) + (d ^(2:ℕ) / (625 * u ^(6:ℕ) * w) * (Y / (625 * u ^(6:ℕ)))))
        = (1953125 : L) * u ^(12:ℕ) * w ^(3:ℕ) * (Y / (625 * u ^(6:ℕ))) ^(2:ℕ)
          + (1953125 : L) * u ^(12:ℕ) * w ^(3:ℕ) *
              ((-(3 * u ^(5:ℕ) + 1) / (5 * u ^(2:ℕ))) * (X / (125 * u ^(4:ℕ) * w)) * (Y / (625 * u ^(6:ℕ))))
          + (1953125 : L) * u ^(12:ℕ) * w ^(3:ℕ) * (d ^(2:ℕ) / (625 * u ^(6:ℕ) * w) * (Y / (625 * u ^(6:ℕ)))) from by
      ring]
    rw [h1, h2, h3]
  have hR : (1953125 : L) * u ^(12:ℕ) * w ^(3:ℕ) *
        ((X / (125 * u ^(4:ℕ) * w)) ^(3:ℕ) +
          (-(29 * u ^(15:ℕ) + 59 * u ^(10:ℕ) + 63 * u ^(5:ℕ) - 3) / (125 * u ^(4:ℕ) * w)) *
            (X / (125 * u ^(4:ℕ) * w)) ^(2:ℕ) +
          d ^(2:ℕ) * (27 * u ^(10:ℕ) + 28 * u ^(5:ℕ) - 2) / (15625 * u ^(8:ℕ) * w ^(2:ℕ)) * (X / (125 * u ^(4:ℕ) * w)) +
          -(7 * u ^(5:ℕ) - 1) * d ^(4:ℕ) / (1953125 * u ^(12:ℕ) * w ^(3:ℕ)))
      = X ^(3:ℕ) + (-(29 * u ^(15:ℕ) + 59 * u ^(10:ℕ) + 63 * u ^(5:ℕ) - 3)) * X ^(2:ℕ) +
          (d ^(2:ℕ) * (27 * u ^(10:ℕ) + 28 * u ^(5:ℕ) - 2)) * X + (-(7 * u ^(5:ℕ) - 1) * d ^(4:ℕ)) := by
    rw [show (1953125 : L) * u ^(12:ℕ) * w ^(3:ℕ) *
          ((X / (125 * u ^(4:ℕ) * w)) ^(3:ℕ) +
            (-(29 * u ^(15:ℕ) + 59 * u ^(10:ℕ) + 63 * u ^(5:ℕ) - 3) / (125 * u ^(4:ℕ) * w)) *
              (X / (125 * u ^(4:ℕ) * w)) ^(2:ℕ) +
            d ^(2:ℕ) * (27 * u ^(10:ℕ) + 28 * u ^(5:ℕ) - 2) / (15625 * u ^(8:ℕ) * w ^(2:ℕ)) * (X / (125 * u ^(4:ℕ) * w)) +
            -(7 * u ^(5:ℕ) - 1) * d ^(4:ℕ) / (1953125 * u ^(12:ℕ) * w ^(3:ℕ)))
        = (1953125 : L) * u ^(12:ℕ) * w ^(3:ℕ) * (X / (125 * u ^(4:ℕ) * w)) ^(3:ℕ)
          + (1953125 : L) * u ^(12:ℕ) * w ^(3:ℕ) *
              ((-(29 * u ^(15:ℕ) + 59 * u ^(10:ℕ) + 63 * u ^(5:ℕ) - 3) / (125 * u ^(4:ℕ) * w)) *
                (X / (125 * u ^(4:ℕ) * w)) ^(2:ℕ))
          + (1953125 : L) * u ^(12:ℕ) * w ^(3:ℕ) *
              (d ^(2:ℕ) * (27 * u ^(10:ℕ) + 28 * u ^(5:ℕ) - 2) / (15625 * u ^(8:ℕ) * w ^(2:ℕ)) * (X / (125 * u ^(4:ℕ) * w)))
          + (1953125 : L) * u ^(12:ℕ) * w ^(3:ℕ) * (-(7 * u ^(5:ℕ) - 1) * d ^(4:ℕ) / (1953125 * u ^(12:ℕ) * w ^(3:ℕ))) from by
      ring]
    rw [h4, h5', h6, h7]
  exact mul_left_cancel₀ hU7 (hL.trans (hclear.trans hR.symm))

end Work.MotT
