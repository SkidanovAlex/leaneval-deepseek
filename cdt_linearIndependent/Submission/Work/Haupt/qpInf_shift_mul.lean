import Mathlib
import Submission.Work.Haupt.qp_defs
import Submission.Work.Haupt.sf_aux
import Submission.Work.Haupt.semifinite_rhs_limit

/-!
# Shifting the infinite `q`-Pochhammer symbol

The main result `Work.Haupt.qpInf_shift_mul` is the elementary product identity

`(q; q)_m · q^{m(m+1)/2} z^{-m} · (z q^{-m}; q)_∞ = (-q/z; q)_m · (-z; q)_∞`,

i.e. the "`m`-fold shift/renormalisation" of the infinite product `(-z; q)_∞` that is used in
the semi-finite proof of the Jacobi triple product.

It is a consequence of
* the tail splitting `(a;q)_∞ = (a;q)_m (a q^m; q)_∞` (`qpInf_eq_qpNat_mul_tail_aux`), and
* the finite product identity `qhalf q (m+1) z^{-m} ∏_{j<m}(1 + z q^{j-m}) = (-q/z; q)_m`
  (`qhalf_zpow_shift_prod_aux`).
-/

open scoped BigOperators
open Filter Topology

namespace Work.Haupt

/-- Splitting the infinite `q`-Pochhammer product at the index `m`:
`(a;q)_∞ = (a;q)_m (a q^m; q)_∞`. -/
lemma qpInf_eq_qpNat_mul_tail_aux {a q : ℂ} (hq : ‖q‖ < 1) (m : ℕ) :
    qpInf a q = qpNat a q m * qpInf (a * q^m) q := by
  have hcomp : Tendsto (fun k : ℕ => m + k) atTop atTop := by
    have h0 : Tendsto (fun k : ℕ => k + m) atTop atTop :=
      (tendsto_add_atTop_iff_nat m).mpr tendsto_id
    simpa [Nat.add_comm] using h0
  have h1 : Tendsto (fun k : ℕ => qpNat a q (m + k)) atTop (nhds (qpInf a q)) :=
    (qpNat_tendsto_qpInf a q hq).comp hcomp
  have h2 : Tendsto (fun k : ℕ => qpNat a q m * qpNat (a * q^m) q k) atTop
      (nhds (qpNat a q m * qpInf (a * q^m) q)) :=
    tendsto_const_nhds.mul (qpNat_tendsto_qpInf (a * q^m) q hq)
  have h3 : Tendsto (fun k : ℕ => qpNat a q m * qpNat (a * q^m) q k) atTop
      (nhds (qpInf a q)) :=
    h1.congr' (Eventually.of_forall (fun k => (qpNat_mul_qpNat a q m k).symm))
  exact tendsto_nhds_unique h3 h2

/-- The finite product identity behind the shift formula:
`qhalf q (m+1) z^{-m} ∏_{j<m} (1 + z q^{j-m}) = (-q/z; q)_m`. -/
lemma qhalf_zpow_shift_prod_aux {q z : ℂ} (hq : q ≠ 0) (hz : z ≠ 0) (m : ℕ) :
    qhalf q (m+1) * z^(-(m:ℤ)) * (∏ j ∈ Finset.range m, (1 + z * q^((j:ℤ) - (m:ℤ))))
      = qpNat (-q/z) q m := by
  have hzpow : z ^ (-(m:ℤ)) = ∏ j ∈ Finset.range m, z⁻¹ := by
    rw [zpow_neg, zpow_natCast, Finset.prod_const, Finset.card_range, ← inv_pow]
  have hqh : qhalf q (m+1) = ∏ j ∈ Finset.range m, q^(j+1) := by
    rw [qhalf, Finset.prod_range_succ']
    simp
  have hrefl : (∏ j ∈ Finset.range m, (1 + z * q^((j:ℤ) - (m:ℤ))))
      = ∏ j ∈ Finset.range m, (1 + z * q^(-((j:ℤ) + 1))) := by
    rw [← Finset.prod_range_reflect (fun i : ℕ => 1 + z * q^((i:ℤ) - (m:ℤ))) m]
    refine Finset.prod_congr rfl (fun j hj => ?_)
    have hj' : j < m := Finset.mem_range.mp hj
    have hexp : (((m - 1 - j : ℕ)) : ℤ) - (m:ℤ) = -((j:ℤ) + 1) := by
      rw [show (((m - 1 - j : ℕ)) : ℤ) = (m:ℤ) - 1 - (j:ℤ) by omega]
      ring
    rw [hexp]
  rw [hqh, hzpow, hrefl]
  rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
  rw [qpNat]
  refine Finset.prod_congr rfl (fun j _ => ?_)
  have hpow : q ^ (-((j:ℤ) + 1)) = (q^(j+1))⁻¹ := by
    rw [show -((j:ℤ)+1) = -((j+1 : ℕ) : ℤ) from by push_cast; ring, zpow_neg, zpow_natCast]
  rw [hpow]
  have hqne : q ^ (j+1) ≠ 0 := pow_ne_zero _ hq
  field_simp
  ring

theorem qpInf_shift_mul {q z : ℂ} (hq : q ≠ 0) (hqn : ‖q‖ < 1) (hz : z ≠ 0) (m : ℕ) :
    qhalf q (m+1) * z^(-(m:ℤ)) * qpInf (-(q^(-(m:ℤ)) * z)) q
      = qpNat (-q/z) q m * qpInf (-z) q := by
  have hsplit := qpInf_eq_qpNat_mul_tail_aux (a := -(q^(-(m:ℤ)) * z)) hqn m
  have htail : (-(q^(-(m:ℤ)) * z)) * q^m = -z := by
    have h1 : q^(-(m:ℤ)) * z * q^m = z := by
      rw [mul_assoc, mul_comm z (q^m), ← mul_assoc, ← zpow_natCast q m,
        zpow_neg_mul_self q hq (m:ℤ), one_mul]
    rw [neg_mul, h1]
  have hpn : qpNat (-(q^(-(m:ℤ)) * z)) q m
      = ∏ j ∈ Finset.range m, (1 + z * q^((j:ℤ) - (m:ℤ))) := by
    rw [qpNat]
    refine Finset.prod_congr rfl (fun j _ => ?_)
    have h2 : q^(-(m:ℤ)) * (q:ℂ)^j = q^((j:ℤ) - (m:ℤ)) := by
      rw [← zpow_natCast q j, mul_comm, ← zpow_add₀ hq,
        show (j:ℤ) + -(m:ℤ) = (j:ℤ) - (m:ℤ) by ring]
    have h3 : (q^(-(m:ℤ)) * z) * (q:ℂ)^j = z * q^((j:ℤ) - (m:ℤ)) := by
      rw [mul_assoc, mul_comm z (q^j), ← mul_assoc, h2, mul_comm]
    rw [neg_mul, h3, sub_neg_eq_add]
  rw [hsplit, htail, hpn]
  rw [← mul_assoc]
  rw [qhalf_zpow_shift_prod_aux hq hz m]

end Work.Haupt
