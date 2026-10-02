import Mathlib
import Submission.Work.FatouDeg.Petal.DefsAux
import Submission.Work.FatouDeg.Petal.orbitBoundsAux
import Submission.Work.FatouDeg.Petal.rpowSumBound
import Submission.Work.FatouDeg.Petal.rfunSummableUniform

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.FatouDeg.Petal

open scoped Topology

/-! ## Elementary real-power bookkeeping -/

/-- `(x ^ (m-1)) ^ t = x ^ ((m-1) * t)` for `x ≥ 0` and a real exponent `t`. -/
private lemma rpow_pow_sub_one_mul (x : ℝ) (hx : 0 ≤ x) (m : ℕ) (t : ℝ) :
    (x ^ (m - 1)) ^ t = x ^ (((m - 1 : ℕ) : ℝ) * t) := by
  rw [← Real.rpow_natCast x (m - 1), ← Real.rpow_mul hx ((m - 1 : ℕ) : ℝ) t]

/-- `((m-1 : ℕ) : ℝ) + 1 = m` for `1 ≤ m`. -/
private lemma cast_sub_one_add_one {m : ℕ} (hm : 1 ≤ m) :
    ((m - 1 : ℕ) : ℝ) + 1 = (m : ℝ) := by
  have h1 : m - 1 + 1 = m := Nat.sub_add_cancel hm
  have h2 := congrArg (fun n : ℕ => (n : ℝ)) h1
  push_cast at h2
  exact h2

/-- `(m-1) * q = 1` for `q = 1 / (m-1)`. -/
private lemma cast_N_mul_q (q : ℝ) {m : ℕ} (hm : 2 ≤ m)
    (hq : q = 1 / ((m - 1 : ℕ) : ℝ)) : ((m - 1 : ℕ) : ℝ) * q = 1 := by
  have hNpos : (0 : ℝ) < ((m - 1 : ℕ) : ℝ) := by
    have h : 0 < m - 1 := by omega
    exact_mod_cast h
  rw [hq, mul_one_div, div_self (ne_of_gt hNpos)]

/-- `(m-1) * (q + 1) = m` for `q = 1 / (m-1)`. -/
private lemma cast_N_mul_q_plus_one (q : ℝ) {m : ℕ} (hm : 2 ≤ m)
    (hq : q = 1 / ((m - 1 : ℕ) : ℝ)) : ((m - 1 : ℕ) : ℝ) * (q + 1) = (m : ℝ) := by
  calc ((m - 1 : ℕ) : ℝ) * (q + 1)
      = ((m - 1 : ℕ) : ℝ) * q + ((m - 1 : ℕ) : ℝ) := by ring
    _ = 1 + ((m - 1 : ℕ) : ℝ) := by rw [cast_N_mul_q q hm hq]
    _ = (m : ℝ) := by linarith [cast_sub_one_add_one (by omega : 1 ≤ m)]

/-- `(x ^ (m-1)) ^ (q+1) = x ^ m` for `q = 1/(m-1)`, `x ≥ 0`. -/
private lemma pow_sub_one_rpow (x q : ℝ) (hx : 0 ≤ x) {m : ℕ} (hm : 2 ≤ m)
    (hq : q = 1 / ((m - 1 : ℕ) : ℝ)) : (x ^ (m - 1)) ^ (q + 1) = x ^ m := by
  rw [rpow_pow_sub_one_mul x hx m (q + 1), cast_N_mul_q_plus_one q hm hq, Real.rpow_natCast]

/-- `(((x ^ (m-1))⁻¹)) ^ (-(q+1)) = x ^ m` for `q = 1/(m-1)`, `x ≥ 0`. -/
private lemma invpow_sub_one_rpow_neg (x q : ℝ) (hx : 0 ≤ x) {m : ℕ} (hm : 2 ≤ m)
    (hq : q = 1 / ((m - 1 : ℕ) : ℝ)) : ((x ^ (m - 1))⁻¹) ^ (-(q + 1)) = x ^ m := by
  have hbase : (0 : ℝ) ≤ x ^ (m - 1) := pow_nonneg hx _
  rw [Real.inv_rpow hbase, Real.rpow_neg hbase (q + 1), inv_inv]
  exact pow_sub_one_rpow x q hx hm hq

/-- `(((x ^ (m-1))⁻¹)) ^ (-q) = x` for `q = 1/(m-1)`, `x ≥ 0`. -/
private lemma invpow_sub_one_rpow_neg_q (x q : ℝ) (hx : 0 ≤ x) {m : ℕ} (hm : 2 ≤ m)
    (hq : q = 1 / ((m - 1 : ℕ) : ℝ)) : ((x ^ (m - 1))⁻¹) ^ (-q) = x := by
  have hbase : (0 : ℝ) ≤ x ^ (m - 1) := pow_nonneg hx _
  rw [Real.inv_rpow hbase, Real.rpow_neg hbase q, inv_inv,
    rpow_pow_sub_one_mul x hx m q, cast_N_mul_q q hm hq, Real.rpow_one]

/-- `1 / (q * c) = (m-1) / c` for `q = 1/(m-1)`. -/
private lemma one_div_q_mul (q c : ℝ) {m : ℕ} (hq : q = 1 / ((m - 1 : ℕ) : ℝ)) :
    1 / (q * c) = ((m - 1 : ℕ) : ℝ) / c := by
  rw [hq]
  have h1 : (1 : ℝ) / ((m - 1 : ℕ) : ℝ) * c = c / ((m - 1 : ℕ) : ℝ) := by ring
  rw [h1, one_div_div]

/-! ## The main bound -/

/-- **The defect series grows at most linearly in `‖z‖` on the working domain.**

Under the standing hypotheses, for every `z ∈ Dom m ρ` (so `‖z‖ < 2ρ`),
`‖∑'_k Rfun m G (P^[k] z)‖ ≤ C * ((2ρ)^(m-1) + (m-1)/c) * ‖z‖`.

Proof idea: with `a = (‖z‖^(m-1))⁻¹`, `p = m/(m-1)`, each term is
`≤ C (a + c*k)^{-p}`; summing and applying `rpowSumBound` with `q = 1/(m-1) ≤ 1` gives
`≤ C (a^{-p} + a^{-q}/(q c)) = C (‖z‖^m + (m-1)‖z‖/c)`, and `‖z‖^m ≤ (2ρ)^(m-1) * ‖z‖`. -/
theorem rfunGrowthBound (m : ℕ) (hm : 3 ≤ m) (G : Polynomial ℂ) {ρ c C : ℝ}
    (hρ : 0 < ρ) (hc : 0 < c) (hC : 0 ≤ C)
    (hmap : Set.MapsTo (Pfun m G) (Dom m ρ) (Dom m ρ))
    (hnorm : ∀ z ∈ Dom m ρ, ‖Pfun m G z‖ ≤ ‖z‖)
    (hcontract : ∀ z ∈ Dom m ρ, (‖z‖ ^ (m - 1))⁻¹ + c ≤ (‖Pfun m G z‖ ^ (m - 1))⁻¹)
    (hdefect : ∀ z ∈ Dom m ρ, ‖Rfun m G z‖ ≤ C * ‖z‖ ^ m) :
    ∀ z ∈ Dom m ρ, ‖∑' k : ℕ, Rfun m G ((Pfun m G)^[k] z)‖
      ≤ C * ((2 * ρ) ^ (m - 1) + (m - 1) / c) * ‖z‖ := by
  intro z hz
  obtain ⟨hzball, hzsect⟩ := (mem_Dom (m := m) (ρ := ρ)).mp hz
  have hm1 : 1 ≤ m := by omega
  have hm2 : 2 ≤ m := by omega
  have hzre : 0 < z.re := lt_of_le_of_lt (mul_nonneg (by positivity) (abs_nonneg z.im)) hzsect
  have hz0 : z ≠ 0 := by intro h; rw [h] at hzre; simp at hzre
  have hx0 : 0 < ‖z‖ := norm_pos_iff.mpr hz0
  -- summability of the defect series along the orbit
  obtain ⟨hsumm, -⟩ := rfunSummableUniform m hm G hρ hc hC hmap hnorm hcontract hdefect
  have hsummz : Summable (fun k : ℕ => Rfun m G ((Pfun m G)^[k] z)) := hsumm z hz
  have hnormsumm : Summable (fun k : ℕ => ‖Rfun m G ((Pfun m G)^[k] z)‖) := hsummz.norm
  -- orbit bounds
  obtain ⟨-, horbit, -⟩ := orbitBoundsAux m hm G hc hmap hnorm hcontract
  have hmem : ∀ k : ℕ, (Pfun m G)^[k] z ∈ Dom m ρ := by
    intro k
    induction k with
    | zero => simpa using hz
    | succ k ih => rw [Function.iterate_succ_apply']; exact hmap ih
  -- parameters
  set a : ℝ := (‖z‖ ^ (m - 1))⁻¹ with ha
  have hapos : 0 < a := by rw [ha]; exact inv_pos.mpr (pow_pos hx0 _)
  set q : ℝ := 1 / ((m - 1 : ℕ) : ℝ) with hq
  have hNpos : (0 : ℝ) < ((m - 1 : ℕ) : ℝ) := by
    have h : 0 < m - 1 := by omega
    exact_mod_cast h
  have hq0 : 0 < q := by rw [hq]; exact div_pos one_pos hNpos
  have hq1 : q ≤ 1 := by
    rw [hq, div_le_one hNpos]
    have h : 1 ≤ m - 1 := by omega
    exact_mod_cast h
  -- the pointwise bound `‖Rfun … ‖ ≤ C * (a + c k)^{-(q+1)}`
  have hpoint : ∀ k : ℕ, ‖Rfun m G ((Pfun m G)^[k] z)‖ ≤ C * (a + c * (k:ℝ)) ^ (-(q + 1)) := by
    intro k
    have h2 := horbit z hz k
    have hbase : 0 < a + c * (k : ℝ) := by
      have : 0 ≤ c * (k : ℝ) := mul_nonneg hc.le (Nat.cast_nonneg k)
      linarith
    have hstep : (‖(Pfun m G)^[k] z‖ ^ (m - 1)) ^ (q + 1)
        ≤ ((a + c * (k:ℝ))⁻¹) ^ (q + 1) :=
      Real.rpow_le_rpow (by positivity) h2 (by linarith : (0:ℝ) ≤ q + 1)
    have hL : (‖(Pfun m G)^[k] z‖ ^ (m - 1)) ^ (q + 1) = ‖(Pfun m G)^[k] z‖ ^ m :=
      pow_sub_one_rpow ‖(Pfun m G)^[k] z‖ q (norm_nonneg _) hm2 hq
    have hR : ((a + c * (k:ℝ))⁻¹) ^ (q + 1) = (a + c * (k:ℝ)) ^ (-(q + 1)) := by
      rw [Real.inv_rpow hbase.le, Real.rpow_neg hbase.le]
    calc ‖Rfun m G ((Pfun m G)^[k] z)‖
        ≤ C * ‖(Pfun m G)^[k] z‖ ^ m := hdefect _ (hmem k)
      _ ≤ C * (a + c * (k:ℝ)) ^ (-(q + 1)) := by
          rw [← hL, ← hR]
          exact mul_le_mul_of_nonneg_left hstep hC
  -- summation of the geometric majorant
  obtain ⟨hgeomsumm, hgeombound⟩ := rpowSumBound a c q hapos hc hq0 hq1
  have hgeomC : Summable (fun k : ℕ => C * (a + c * (k:ℝ)) ^ (-(q + 1))) :=
    hgeomsumm.mul_left C
  have hsum_bound : ∑' k : ℕ, ‖Rfun m G ((Pfun m G)^[k] z)‖
      ≤ C * (a ^ (-(q + 1)) + a ^ (-q) / (q * c)) := by
    calc ∑' k : ℕ, ‖Rfun m G ((Pfun m G)^[k] z)‖
        ≤ ∑' k : ℕ, C * (a + c * (k:ℝ)) ^ (-(q + 1)) :=
          Summable.tsum_le_tsum hpoint hnormsumm hgeomC
      _ = C * ∑' k : ℕ, (a + c * (k:ℝ)) ^ (-(q + 1)) := by rw [tsum_mul_left]
      _ ≤ C * (a ^ (-(q + 1)) + a ^ (-q) / (q * c)) :=
          mul_le_mul_of_nonneg_left hgeombound hC
  -- evaluation of the closed form
  have hfin1 : a ^ (-(q + 1)) + a ^ (-q) / (q * c)
      = ‖z‖ ^ m + ((m - 1 : ℕ) : ℝ) / c * ‖z‖ := by
    rw [ha, invpow_sub_one_rpow_neg ‖z‖ q (norm_nonneg z) hm2 hq,
      invpow_sub_one_rpow_neg_q ‖z‖ q (norm_nonneg z) hm2 hq,
      div_eq_mul_one_div, one_div_q_mul q c hq]
    ring
  have hpow : ‖z‖ ^ m ≤ (2 * ρ) ^ (m - 1) * ‖z‖ := by
    have hm_eq : m = (m - 1) + 1 := (Nat.sub_add_cancel hm1).symm
    calc ‖z‖ ^ m = ‖z‖ ^ (m - 1) * ‖z‖ := by conv_lhs => rw [hm_eq, pow_succ]
      _ ≤ (2 * ρ) ^ (m - 1) * ‖z‖ :=
          mul_le_mul_of_nonneg_right
            (pow_le_pow_left₀ (norm_nonneg z) hzball.le (m - 1)) (norm_nonneg z)
  calc ‖∑' k : ℕ, Rfun m G ((Pfun m G)^[k] z)‖
      ≤ ∑' k : ℕ, ‖Rfun m G ((Pfun m G)^[k] z)‖ := norm_tsum_le_tsum_norm hnormsumm
    _ ≤ C * (a ^ (-(q + 1)) + a ^ (-q) / (q * c)) := hsum_bound
    _ = C * (‖z‖ ^ m + ((m - 1 : ℕ) : ℝ) / c * ‖z‖) := by rw [hfin1]
    _ ≤ C * (((2 * ρ) ^ (m - 1) + ((m - 1 : ℕ) : ℝ) / c) * ‖z‖) := by
        apply mul_le_mul_of_nonneg_left _ hC
        have heq : ((2 * ρ) ^ (m - 1) + ((m - 1 : ℕ) : ℝ) / c) * ‖z‖
            = (2 * ρ) ^ (m - 1) * ‖z‖ + ((m - 1 : ℕ) : ℝ) / c * ‖z‖ := by ring
        rw [heq]
        linarith
    _ = C * ((2 * ρ) ^ (m - 1) + (m - 1) / c) * ‖z‖ := by
        have hcast : ((m : ℝ) - 1) = ((m - 1 : ℕ) : ℝ) := by
          have h := cast_sub_one_add_one hm1
          linarith
        rw [hcast]
        ring

end Work.FatouDeg.Petal
