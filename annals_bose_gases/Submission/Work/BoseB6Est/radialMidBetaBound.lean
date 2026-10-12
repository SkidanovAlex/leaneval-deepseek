import Mathlib.Algebra.Order.Star.Real
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

set_option maxHeartbeats 2000000

namespace Work.BoseB6Est

/-- Exact rewrite of the "core" expression in terms of `w = sqrt(y^2+2yt) - y`. -/
lemma radialMid_core_eq (y t : ℝ) (hy : 0 < y) (ht : 0 ≤ t) :
    (y + t) - Real.sqrt (y^2 + 2*y*t) - t^2/(2*y)
      = -((Real.sqrt (y^2 + 2*y*t) - y)^3 * (4*y + (Real.sqrt (y^2+2*y*t) - y))) / (8*y^3) := by
  have hs2 : Real.sqrt (y^2 + 2*y*t)^2 = y^2 + 2*y*t := Real.sq_sqrt (by nlinarith [hy, ht])
  set s := Real.sqrt (y^2 + 2*y*t) with hsd
  field_simp
  nlinarith [hs2, sq_nonneg (s - y), sq_nonneg s]

theorem radialMidBetaBound {y β c : ℝ} (hy : 0 < y) (hβ : 0 ≤ β) (hβc : β ≤ c) :
    ((y + β) - Real.sqrt (y ^ 2 + 2 * y * β) - β ^ 2 / (2 * y))
      - ((y + c) - Real.sqrt (y ^ 2 + 2 * y * c) - c ^ 2 / (2 * y))
      ≤ (3 / 2) * c ^ 2 * |β - c| / y ^ 2 := by
  have hβ2 : 0 ≤ y^2 + 2*y*β := by nlinarith [hy, hβ]
  have hc2 : 0 ≤ y^2 + 2*y*c := by nlinarith [hy, hβ, hβc]
  set u := Real.sqrt (y^2 + 2*y*β) - y with hud
  set v := Real.sqrt (y^2 + 2*y*c) - y with hvd
  have hu2 : u^2 + 2*y*u = 2*y*β := by rw [hud]; nlinarith [Real.sq_sqrt hβ2]
  have hv2 : v^2 + 2*y*v = 2*y*c := by rw [hvd]; nlinarith [Real.sq_sqrt hc2]
  have hun : 0 ≤ u := by
    rw [hud, sub_nonneg]
    rw [Real.le_sqrt hy.le hβ2]
    nlinarith [hy, hβ]
  have hvn : 0 ≤ v := by
    rw [hvd, sub_nonneg]
    rw [Real.le_sqrt hy.le hc2]
    nlinarith [hy, hβ, hβc]
  have huv : u ≤ v := by
    rw [hud, hvd]
    have h : y^2 + 2*y*β ≤ y^2 + 2*y*c := by nlinarith [hy, hβc]
    linarith [Real.sqrt_le_sqrt h]
  have hβeq : β = u*(1+u/(2*y)) := by
    have h := hu2
    field_simp
    linarith [h]
  have hceq : c = v*(1+v/(2*y)) := by
    have h := hv2
    field_simp
    linarith [h]
  have hcβ : c - β = (v-u)*(1+(u+v)/(2*y)) := by
    rw [hβeq, hceq]
    field_simp
    ring_nf
  set M := 4*y*(v^2+u*v+u^2) + (v+u)*(v^2+u^2) with hMd
  have hdiff : ((y + β) - Real.sqrt (y ^ 2 + 2 * y * β) - β ^ 2 / (2 * y))
      - ((y + c) - Real.sqrt (y ^ 2 + 2 * y * c) - c ^ 2 / (2 * y))
      = (v-u)*M/(8*y^3) := by
    have h1 := radialMid_core_eq y β hy hβ
    have h2 := radialMid_core_eq y c hy (le_trans hβ hβc)
    rw [h1, h2]
    rw [← hud, ← hvd]
    have key : v^3*(4*y+v) - u^3*(4*y+u) = (v-u)*M := by rw [hMd]; ring
    field_simp
    linarith [key]
  have hMle : M ≤ 4*v^2*(3*y+v) := by
    have hA : v^2 + u*v + u^2 ≤ 3*v^2 := by
      have h : (u-v)*(u+2*v) ≤ 0 := mul_nonpos_of_nonpos_of_nonneg (by linarith) (by linarith)
      nlinarith [h]
    have hB : (v+u)*(v^2+u^2) ≤ 4*v^3 := by
      have h1 : u^3 ≤ v^3 := pow_le_pow_left₀ hun huv 3
      have h2 : u^2 ≤ v^2 := pow_le_pow_left₀ hun huv 2
      have h3 : v^2*u ≤ v^2*v := mul_le_mul_of_nonneg_left huv (sq_nonneg v)
      have h4 : v*u^2 ≤ v*v^2 := mul_le_mul_of_nonneg_left h2 hvn
      nlinarith [h1, h3, h4]
    have hAy : 4*y*(v^2+u*v+u^2) ≤ 4*y*(3*v^2) := mul_le_mul_of_nonneg_left hA (by linarith [hy])
    rw [hMd]
    nlinarith [hAy, hB]
  have hMn : 0 ≤ v - u := by linarith
  have hstep2 : 4*v^2*(3*y+v) ≤ 12*y*v^2*(1+v/(2*y))^3 := by
    have hq : 0 ≤ 28*y^2+18*y*v+3*v^2 := by
      nlinarith [sq_nonneg y, mul_nonneg hy.le hvn, sq_nonneg v]
    have hid : 8*y^3*(3*y*(1+v/(2*y))^3 - (3*y+v)) = y*v*(28*y^2+18*y*v+3*v^2) := by
      field_simp
      ring_nf
    have hbase : 3*y+v ≤ 3*y*(1+v/(2*y))^3 := by
      have hP : 0 ≤ 8*y^3*(3*y*(1+v/(2*y))^3 - (3*y+v)) := by
        rw [hid]; exact mul_nonneg (mul_nonneg hy.le hvn) hq
      have hX : 0 ≤ 3*y*(1+v/(2*y))^3 - (3*y+v) :=
        (mul_nonneg_iff_of_pos_left (by positivity : (0:ℝ) < 8*y^3)).mp hP
      linarith
    calc 4*v^2*(3*y+v) ≤ 4*v^2*(3*y*(1+v/(2*y))^3) := mul_le_mul_of_nonneg_left hbase (by positivity)
      _ = 12*y*v^2*(1+v/(2*y))^3 := by ring
  have hstep3 : 12*y*v^2*(1+v/(2*y))^3 ≤ 12*y*v^2*(1+v/(2*y))^2*(1+(u+v)/(2*y)) := by
    have h1 : (1+v/(2*y)) ≤ (1+(u+v)/(2*y)) := by
      have hd : (1+(u+v)/(2*y)) - (1+v/(2*y)) = u/(2*y) := by field_simp; ring
      have h2 : 0 ≤ u/(2*y) := by positivity
      linarith
    have h2 : 0 ≤ 12*y*v^2*(1+v/(2*y))^2 := by positivity
    calc 12*y*v^2*(1+v/(2*y))^3 = 12*y*v^2*(1+v/(2*y))^2*(1+v/(2*y)) := by ring
      _ ≤ 12*y*v^2*(1+v/(2*y))^2*(1+(u+v)/(2*y)) := mul_le_mul_of_nonneg_left h1 h2
  have hstep2b : (v-u)*(4*v^2*(3*y+v)) ≤ (v-u)*(12*y*v^2*(1+v/(2*y))^3) :=
    mul_le_mul_of_nonneg_left hstep2 hMn
  have hstep23 : (v-u)*(12*y*v^2*(1+v/(2*y))^3)
      ≤ (v-u)*(12*y*v^2*(1+v/(2*y))^2*(1+(u+v)/(2*y))) :=
    mul_le_mul_of_nonneg_left hstep3 hMn
  have hstep4 : (v-u)*(12*y*v^2*(1+v/(2*y))^2*(1+(u+v)/(2*y))) = 12*y*c^2*(c-β) := by
    rw [hcβ, hceq]
    field_simp
  have hbound : (v-u)*M ≤ 12*y*c^2*(c-β) := by
    have hM1 : (v-u)*M ≤ (v-u)*(4*v^2*(3*y+v)) := mul_le_mul_of_nonneg_left hMle hMn
    linarith [hM1, hstep2b, hstep23, hstep4]
  have habs : |β - c| = c - β := by
    have hle : β - c ≤ 0 := by linarith
    rw [abs_of_nonpos hle]; ring
  rw [habs, hdiff]
  have hpos : (0:ℝ) < 8*y^3 := by positivity
  rw [div_le_iff₀ hpos]
  have heq : (3/2)*c^2*(c-β)/y^2 * (8*y^3) = 12*y*c^2*(c-β) := by field_simp; ring_nf
  rw [heq]
  exact hbound

end Work.BoseB6Est
