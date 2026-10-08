import Mathlib
import Submission.Work.PGroup.Cyc2Defs
import Submission.Work.PGroup.geom_sum_sq_not_dvd

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.PGroup

theorem not_sq_dvd_PhiZ {q D j : ℕ} (hq : q.Prime) (hq2 : q ≠ 2)
    (hD : D = orderOf (2 : ZMod q)) (hj : 1 ≤ j) (hdvd : (q : ℤ) ∣ PhiZ (D * q ^ j)) :
    ¬ ((q : ℤ) ^ 2 ∣ PhiZ (D * q ^ j)) := by
  have hqpos : 0 < q := hq.pos
  -- `q ^ j = q ^ (j-1) * q` since `j ≥ 1`
  have hpowj : q ^ j = q ^ (j - 1) * q := by
    rw [← pow_succ]
    congr 1
    omega
  -- hence `(D * q^j) / q = D * q^(j-1)`
  have hdiv : D * q ^ j / q = D * q ^ (j - 1) := by
    rw [hpowj, ← mul_assoc, Nat.mul_div_cancel _ hqpos]
  -- `2 ^ (D * q^(j-1)) = 1` in `ZMod q`, since `orderOf 2 = D ∣ D * q^(j-1)`
  have hpow : (2 : ZMod q) ^ (D * q ^ (j - 1)) = 1 :=
    (orderOf_dvd_iff_pow_eq_one).1 (by rw [← hD]; exact dvd_mul_right D _)
  -- hence `q ∣ 2 ^ (D * q^(j-1)) - 1`
  have hdiv2 : (q : ℤ) ∣ (2 : ℤ) ^ (D * q ^ (j - 1)) - 1 := by
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd ((2 : ℤ) ^ (D * q ^ (j - 1)) - 1) q]
    push_cast
    rw [hpow]
    ring
  intro h
  -- `Φ_{D q^j}(2)` divides the geometric sum
  have hgeom : PhiZ (D * q ^ j) ∣ ∑ i ∈ Finset.range q, ((2 : ℤ) ^ (D * q ^ (j - 1))) ^ i := by
    have hqdvd : q ∣ D * q ^ j := ⟨D * q ^ (j - 1), by rw [hpowj]; ring⟩
    have := PhiZ_dvd_geom (n := D * q ^ j) (ℓ := q) hq hqdvd
    rwa [hdiv] at this
  exact geom_sum_sq_not_dvd hq hq2 hdiv2 (h.trans hgeom)

end Work.PGroup
