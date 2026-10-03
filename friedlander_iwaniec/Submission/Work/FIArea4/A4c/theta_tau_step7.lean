import Mathlib
import Submission.Work.FIArea4.A4c.Defs
import Submission.Work.FITop4.Defs4

namespace Work.FIArea4.A4c

noncomputable section

set_option maxHeartbeats 1000000

/-!
# The `θτ`-bookkeeping of the pinned parameters (`theta_tau_step7`)

At the pins `θ = thetaOf x Asave = (log x)^{-A'}`, `τ = tauOf x Asave = (log x)^{A'}`
(`A' = Aprime Asave = 2·10^8 + 2^20`), step 7 of the area-4 chain needs three arithmetic facts,
all of which are pure log-arithmetic:

* `θ·τ = 1`;
* `θ (log N + 1)^{2^20-20} ≤ 1`, because `log N + 1 ≤ log x` (from `N < x^{1/2}(log x)^{-B}`,
  `B > 0`, `x ≥ 3`) and `2^20 - 20 ≤ A'`;
* `θ^{-1}(log N + 1)^{2^20-20} ≤ N^{1/6}`, because the left side is at most
  `(log x)^{A' + (2^20-20)} ≤ (log x)^{3·10^8} ≤ x^{1/24} < N^{1/6}` (the last inequality from
  `N > x^{1/4+η} > x^{1/4}`); here `A' + (2^20-20) = 202097132 ≤ 3·10^8` binds against the
  hypothesis `hxpow` supplied by the caller.
-/

/-- `θ = (log x)^{-A'}` at the pin: the definition, unfolded. -/
lemma thetaOf_apply (x : ℕ) (A : ℝ) :
    Work.FITop4.thetaOf x A = (Real.log (x : ℝ)) ^ (-(Work.FITop4.Aprime A)) := rfl

/-- `τ = (log x)^{A'}` at the pin: unfolding `tauOf` and `Aprime`, the two exponents coincide. -/
lemma tauOf_eq_rpow_Aprime (x : ℕ) (A : ℝ) :
    Work.FITop4.tauOf x A = (Real.log (x : ℝ)) ^ (Work.FITop4.Aprime A) := rfl

/-- At the pin, `θ·τ = 1`. -/
lemma thetaOf_mul_tauOf {x : ℕ} (hx : 0 < Real.log (x : ℝ)) (A : ℝ) :
    Work.FITop4.thetaOf x A * Work.FITop4.tauOf x A = 1 := by
  rw [thetaOf_apply, tauOf_eq_rpow_Aprime]
  rw [← Real.rpow_add hx]
  have h : -(Work.FITop4.Aprime A) + Work.FITop4.Aprime A = (0 : ℝ) := by ring
  rw [h, Real.rpow_zero]

/-- At the pin, `θ^{-1} = (log x)^{A'}`. -/
lemma inv_thetaOf {x : ℕ} (hx : 0 < Real.log (x : ℝ)) (A : ℝ) :
    (Work.FITop4.thetaOf x A)⁻¹ = (Real.log (x : ℝ)) ^ (Work.FITop4.Aprime A) := by
  rw [thetaOf_apply, Real.rpow_neg hx.le]
  exact inv_inv _

/-- **`log N + 1 ≤ log x`.**  From (4.6) `N < x^{1/2}(log x)^{-B}`, `B > 0`, `x ≥ 3`:
`N ≤ x^{1/2}`, hence `log N ≤ (1/2)log x`, hence `log N + 1 ≤ log x` as soon as `2 ≤ log x`. -/
lemma logN_add_one_le_logx (Pa : Work.FITop.Params) (hlog2 : 2 ≤ Real.log (Pa.x : ℝ)) :
    Real.log Pa.N + 1 ≤ Real.log (Pa.x : ℝ) := by
  have hx1 : (1 : ℝ) ≤ (Pa.x : ℝ) := by
    have h : (1 : ℕ) ≤ Pa.x := by have := Pa.hx; omega
    exact_mod_cast h
  have hx0 : (0 : ℝ) < (Pa.x : ℝ) := by linarith
  have hL1 : (1 : ℝ) ≤ Real.log (Pa.x : ℝ) := by linarith
  have hpowle : (Real.log (Pa.x : ℝ)) ^ (-Pa.B) ≤ 1 := by
    have h := Real.rpow_le_rpow_of_exponent_le hL1 (show -Pa.B ≤ (0 : ℝ) by linarith [Pa.hB])
    rwa [Real.rpow_zero] at h
  have hNpos : 0 < Pa.N := by linarith [Pa.hN1]
  have hNle : Pa.N ≤ (Pa.x : ℝ) ^ ((1 : ℝ) / 2) := by
    have h3 : 0 < (Pa.x : ℝ) ^ ((1 : ℝ) / 2) := Real.rpow_pos_of_pos hx0 _
    nlinarith [Pa.hNhi, hpowle, h3]
  have hlogN : Real.log Pa.N ≤ (1 / 2) * Real.log (Pa.x : ℝ) := by
    have h := Real.log_le_log hNpos hNle
    rw [Real.log_rpow hx0] at h
    linarith
  linarith

theorem theta_tau_step7 (Pa : Work.FITop.Params)
    (hθ : Pa.θ = Work.FITop4.thetaOf Pa.x Work.FITop4.Asave)
    (hτ : Pa.τ = Work.FITop4.tauOf Pa.x Work.FITop4.Asave)
    (hlog2 : 2 ≤ Real.log (Pa.x : ℝ))
    (hxpow : (Real.log (Pa.x : ℝ)) ^ (300000000 : ℕ) ≤ (Pa.x : ℝ) ^ ((1 : ℝ) / 24)) :
    Pa.θ * Pa.τ = 1 ∧
    Pa.θ * (Real.log Pa.N + 1) ^ (10 + (((2 : ℕ) ^ 20) - 30)) ≤ 1 ∧
    (Pa.θ)⁻¹ * (Real.log Pa.N + 1) ^ (10 + (((2 : ℕ) ^ 20) - 30)) ≤ Pa.N ^ ((1 : ℝ) / 6) ∧
    (Pa.θ)⁻¹ * (Real.log Pa.N + 1) ^ (10 + (((2 : ℕ) ^ 20) - 30)) ≤ Pa.N := by
  set k : ℕ := 10 + (((2 : ℕ) ^ 20) - 30) with hkdef
  set L : ℝ := Real.log (Pa.x : ℝ) with hLdef
  have hLpos : 0 < L := by linarith
  have hL0 : (0 : ℝ) ≤ L := by linarith
  have hL1 : (1 : ℝ) ≤ L := by linarith
  have hlogxpos : 0 < Real.log (Pa.x : ℝ) := by rw [← hLdef]; exact hLpos
  have hx1 : (1 : ℝ) ≤ (Pa.x : ℝ) := by
    have h : (1 : ℕ) ≤ Pa.x := by have := Pa.hx; omega
    exact_mod_cast h
  have hx0 : (0 : ℝ) < (Pa.x : ℝ) := by linarith
  -- the numeric content of the exponent `k = 2^20 - 20`
  have hkA : (k : ℝ) ≤ Work.FITop4.Aprime Work.FITop4.Asave := by
    rw [hkdef]; unfold Work.FITop4.Aprime Work.FITop4.Asave; norm_num
  have hksum : Work.FITop4.Aprime Work.FITop4.Asave + (k : ℝ) ≤ 300000000 := by
    rw [hkdef]; unfold Work.FITop4.Aprime Work.FITop4.Asave; norm_num
  -- `log N + 1 ≤ log x`
  have hlogN : Real.log Pa.N + 1 ≤ L := by
    rw [hLdef]
    exact logN_add_one_le_logx Pa (by rw [← hLdef]; exact hlog2)
  have hLNnn : (0 : ℝ) ≤ Real.log Pa.N + 1 := by
    have h := Real.log_nonneg (show (1 : ℝ) ≤ Pa.N by exact_mod_cast Pa.hN1)
    linarith
  -- `(log N + 1)^k ≤ L^{↑k}`
  have hpowL : (Real.log Pa.N + 1) ^ k ≤ L ^ ((k : ℕ) : ℝ) := by
    have h1 : (Real.log Pa.N + 1) ^ k ≤ L ^ k := pow_le_pow_left₀ hLNnn hlogN k
    rw [← Real.rpow_natCast L k] at h1
    exact h1
  -- `(log N + 1)^k ≤ L^{A'}`
  have hpowA' : (Real.log Pa.N + 1) ^ k ≤ L ^ (Work.FITop4.Aprime Work.FITop4.Asave) :=
    hpowL.trans (Real.rpow_le_rpow_of_exponent_le hL1 hkA)
  -- `L^{-A'}·L^{A'} = 1`
  have hone : L ^ (-(Work.FITop4.Aprime Work.FITop4.Asave))
      * L ^ (Work.FITop4.Aprime Work.FITop4.Asave) = 1 := by
    rw [← Real.rpow_add hLpos]
    have h : -(Work.FITop4.Aprime Work.FITop4.Asave) + Work.FITop4.Aprime Work.FITop4.Asave
        = (0 : ℝ) := by ring
    rw [h, Real.rpow_zero]
  have hθ' : Pa.θ = L ^ (-(Work.FITop4.Aprime Work.FITop4.Asave)) := by
    rw [hθ, thetaOf_apply]
  have hθinv : (Pa.θ)⁻¹ = L ^ (Work.FITop4.Aprime Work.FITop4.Asave) := by
    rw [hθ, inv_thetaOf hlogxpos Work.FITop4.Asave]
  -- `x^{1/24} < N^{1/6}`
  have hx4 : (Pa.x : ℝ) ^ ((1 : ℝ) / 4) ≤ (Pa.x : ℝ) ^ ((1 : ℝ) / 4 + Pa.η) :=
    Real.rpow_le_rpow_of_exponent_le hx1 (by linarith [Pa.hη])
  have hlt : (Pa.x : ℝ) ^ ((1 : ℝ) / 4) < Pa.N := lt_of_le_of_lt hx4 Pa.hNlo
  have h24 : (Pa.x : ℝ) ^ ((1 : ℝ) / 24) = ((Pa.x : ℝ) ^ ((1 : ℝ) / 4)) ^ ((1 : ℝ) / 6) := by
    rw [← Real.rpow_mul hx0.le]
    norm_num
  have hN16 : (Pa.x : ℝ) ^ ((1 : ℝ) / 24) < Pa.N ^ ((1 : ℝ) / 6) := by
    rw [h24]
    exact Real.rpow_lt_rpow (Real.rpow_nonneg hx0.le _) hlt (by norm_num)
  have hN1 : (1 : ℝ) ≤ Pa.N := by exact_mod_cast Pa.hN1
  have hN16le : Pa.N ^ ((1 : ℝ) / 6) ≤ Pa.N := by
    have h := Real.rpow_le_rpow_of_exponent_le hN1 (show (1 : ℝ) / 6 ≤ 1 by norm_num)
    rwa [Real.rpow_one] at h
  -- the key estimate `θ^{-1}(log N + 1)^k ≤ N^{1/6}`
  have hkey : (Pa.θ)⁻¹ * (Real.log Pa.N + 1) ^ k ≤ Pa.N ^ ((1 : ℝ) / 6) := by
    rw [hθinv]
    have h250 : L ^ (Work.FITop4.Aprime Work.FITop4.Asave) * L ^ ((k : ℕ) : ℝ)
        ≤ L ^ (300000000 : ℝ) := by
      rw [← Real.rpow_add hLpos]
      exact Real.rpow_le_rpow_of_exponent_le hL1 hksum
    calc L ^ (Work.FITop4.Aprime Work.FITop4.Asave) * (Real.log Pa.N + 1) ^ k
        ≤ L ^ (Work.FITop4.Aprime Work.FITop4.Asave) * L ^ ((k : ℕ) : ℝ) :=
          mul_le_mul_of_nonneg_left hpowL (Real.rpow_nonneg hL0 _)
      _ ≤ L ^ (300000000 : ℝ) := h250
      _ = L ^ (300000000 : ℕ) := Real.rpow_natCast L 300000000
      _ ≤ (Pa.x : ℝ) ^ ((1 : ℝ) / 24) := hxpow
      _ ≤ Pa.N ^ ((1 : ℝ) / 6) := hN16.le
  refine ⟨?_, ?_, hkey, ?_⟩
  · rw [hθ, hτ]
    exact thetaOf_mul_tauOf hlogxpos Work.FITop4.Asave
  · rw [hθ']
    calc L ^ (-(Work.FITop4.Aprime Work.FITop4.Asave)) * (Real.log Pa.N + 1) ^ k
        ≤ L ^ (-(Work.FITop4.Aprime Work.FITop4.Asave))
            * L ^ (Work.FITop4.Aprime Work.FITop4.Asave) :=
          mul_le_mul_of_nonneg_left hpowA' (Real.rpow_nonneg hL0 _)
      _ = 1 := hone
  · exact le_trans hkey hN16le

end

end Work.FIArea4.A4c
