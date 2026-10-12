import ChallengeDeps
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Submission.Work.BoseBoxFock.pcfFrameDefs
import Submission.Work.BoseGateFS.LabAdd
import Submission.Work.BoseRowQ2.vec_labVec_sub_eq
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.kmomLab_sub_of_support`

The **guarded label arithmetic** of the `§10` kernel gate `Q3KernelFS`: on the pairs
`(s,k)` that the `Q₃` sums actually visit — `s` in the support of the low-momentum cut-off
`f_L` and `k` in the support of the UV-cut `Ŵ₁` — the cube momentum map
`kmomLab ℓ N : Lab N → ℝ³` is additive,

`kmomLab ℓ N (s − k) = kmomLab ℓ N s − kmomLab ℓ N k`.

The mechanism is the one recorded in `Work.BoseGateFS.LabAdd`: the two supports confine the
labels to `‖kmomLab ℓ N s‖ ≤ 2(d²ℓ)⁻¹` and `‖kmomLab ℓ N k‖ ≤ 2·uvRad ℓ N`, and the
numerical hypothesis `hN` of the statement is *exactly* the box-size condition
`ℓ(2(d²ℓ)⁻¹ + 2·uvRad ℓ N)/(2π) ≤ N` needed by `LabAdd.kmomLab_sub_of_norm_le`.  The two
support bounds are the `LowCut` axioms (`f = 0` on `[2,∞)`); the only care needed is the
positivity of the cut-off radius `(d²ℓ)⁻¹`, i.e. `d ≠ 0`, which is extracted from the
hypothesis `0 < sideAt μ (a v)`: `d = (μ(a v)³)^{6/323}` can only vanish when `μ(a v)³ = 0`,
but `0 < sideAt μ (a v)` forces `0 < μ·a v` (the half-integer power `(μ·a v)^{-1/2}`
vanishes on the nonpositive half-line), hence `μ(a v)³ > 0`.
-/

namespace Work.BoseBoxFock

open Work.BoseBox

set_option linter.unusedVariables false

/-! ## 0. `Real.rpow` on the nonpositive half-line -/

/-- `x ^ (−1/2) = 0` for `x ≤ 0` (for `x < 0` by the definition of `Real.rpow` at a negative
base, `cos(−π/2) = 0`; for `x = 0` by `Real.zero_rpow`). -/
theorem rpow_neg_half_eq_zero_of_nonpos {x : ℝ} (hx : x ≤ 0) :
    x ^ (-(1 / 2 : ℝ)) = 0 := by
  rcases lt_or_eq_of_le hx with h | h
  · have hcos : Real.cos ((-(1 / 2 : ℝ)) * Real.pi) = 0 := by
      rw [show (-(1 / 2 : ℝ)) * Real.pi = -(Real.pi / 2) by ring, Real.cos_neg,
        Real.cos_pi_div_two]
    rw [Real.rpow_def_of_neg h, hcos, mul_zero]
  · rw [h, Real.zero_rpow (by norm_num : (-(1 / 2 : ℝ)) ≠ 0)]

/-- **The positivity of the box side forces `μ·a > 0`.**  `sideAt μ a = K_ℓ (μa)^{-1/2}` and
the half-integer power vanishes on the nonpositive half-line. -/
theorem mu_mul_side_pos_of_sideAt_pos {μ a : ℝ} (h : 0 < Work.BoseBox.sideAt μ a) :
    0 < μ * a := by
  have hside : Work.BoseBox.sideAt μ a
      = (Work.BoseBox.paramsAt μ a).Kl * (μ * a) ^ (-(1 / 2 : ℝ)) := rfl
  by_contra hcon
  have hle : μ * a ≤ 0 := not_lt.mp hcon
  rw [hside, rpow_neg_half_eq_zero_of_nonpos hle, mul_zero] at h
  exact lt_irrefl 0 h

/-- `d > 0` as soon as the box side is positive (`d = (μa³)^{6/323}`). -/
theorem paramsAt_d_pos_of_sideAt_pos {μ a : ℝ} (h : 0 < Work.BoseBox.sideAt μ a) :
    0 < (Work.BoseBox.paramsAt μ a).d := by
  have hy : 0 < μ * a := mu_mul_side_pos_of_sideAt_pos h
  have hane : a ≠ 0 := by
    intro h0
    rw [h0, mul_zero] at hy
    exact lt_irrefl 0 hy
  rw [show (Work.BoseBox.paramsAt μ a).d
      = Work.BoseBox.fsXp (μ * a ^ 3) (6 : ℝ) from rfl]
  refine Real.rpow_pos_of_pos ?_ _
  rw [show μ * a ^ 3 = (μ * a) * a ^ 2 by ring]
  exact mul_pos hy (sq_pos_of_ne_zero hane)

/-! ## 1. The two support bounds -/

/-- **The `f_L` support bound**: `f_L s ≠ 0` forces `‖kmomLab ℓ N s‖ ≤ 2(d²ℓ)⁻¹`, because
`f_c = 0` on `[2,∞)`. -/
theorem fLh_norm_le {v : EuclideanSpace ℝ (Fin 3) → ℝ} {fc : Work.BoseBoxFix.LowCut}
    {μ : ℝ} {N : ℕ} {s : Work.BoseBoxFock.Lab N}
    (hD : 0 < ((Work.BoseBox.paramsAt μ (BoseGases.a v)).d ^ 2
        * Work.BoseBox.sideAt μ (BoseGases.a v))⁻¹)
    (hs : Work.BoseBoxFock.fLh v fc μ N s ≠ 0) :
    ‖Work.BoseBoxFock.kmomLab (Work.BoseBoxFock.ellH v μ) N s‖
      ≤ 2 * ((Work.BoseBox.paramsAt μ (BoseGases.a v)).d ^ 2
          * Work.BoseBox.sideAt μ (BoseGases.a v))⁻¹ := by
  rw [Work.BoseBoxFock.fLh] at hs
  by_contra hcon
  have hcon' : 2 * ((Work.BoseBox.paramsAt μ (BoseGases.a v)).d ^ 2
      * Work.BoseBox.sideAt μ (BoseGases.a v))⁻¹
      < ‖Work.BoseBoxFock.kmomLab (Work.BoseBoxFock.ellH v μ) N s‖ := not_le.mp hcon
  have h2 : 2 ≤ ‖Work.BoseBoxFock.kmomLab (Work.BoseBoxFock.ellH v μ) N s‖
      / ((Work.BoseBox.paramsAt μ (BoseGases.a v)).d ^ 2
          * Work.BoseBox.sideAt μ (BoseGases.a v))⁻¹ := by
    rw [le_div_iff₀ hD]
    linarith
  exact hs (fc.zero _ h2)

/-- **The `Ŵ₁` support bound**: the UV cut vanishes off `2·uvRad ℓ N`. -/
theorem W1h_norm_le {v : EuclideanSpace ℝ (Fin 3) → ℝ} {h : Work.UBB.ScatSol v}
    {fu : Work.BoseBoxFix.LowCut} {μ : ℝ} {N : ℕ} {k : Work.BoseBoxFock.Lab N}
    (hΛ : 0 < Work.BoseBoxFock.uvRad (Work.BoseBox.sideAt μ (BoseGases.a v)) N)
    (hk : Work.BoseBoxFock.W1h v h μ fu N k ≠ 0) :
    ‖Work.BoseBoxFock.kmomLab (Work.BoseBoxFock.ellH v μ) N k‖
      ≤ 2 * Work.BoseBoxFock.uvRad (Work.BoseBox.sideAt μ (BoseGases.a v)) N := by
  have hk' : Work.BoseBoxFock.uvCut fu
        (Work.BoseBoxFock.uvRad (Work.BoseBox.sideAt μ (BoseGases.a v)) N)
        (Work.BoseBoxFock.kmomLab (Work.BoseBoxFock.ellH v μ) N k)
      * Work.BoseFixR.chat (Work.BoseFixR.W1fun v h (Work.BoseBox.sideAt μ (BoseGases.a v)))
        (Work.BoseBoxFock.kmomLab (Work.BoseBoxFock.ellH v μ) N k) ≠ 0 := by
    simpa only [Work.BoseBoxFock.W1h] using hk
  rw [mul_ne_zero_iff] at hk'
  have hζ : fu.f (‖Work.BoseBoxFock.kmomLab (Work.BoseBoxFock.ellH v μ) N k‖
      / Work.BoseBoxFock.uvRad (Work.BoseBox.sideAt μ (BoseGases.a v)) N) ≠ 0 := by
    simpa only [Work.BoseBoxFock.uvCut] using hk'.1
  by_contra hcon
  have hcon' : 2 * Work.BoseBoxFock.uvRad (Work.BoseBox.sideAt μ (BoseGases.a v)) N
      < ‖Work.BoseBoxFock.kmomLab (Work.BoseBoxFock.ellH v μ) N k‖ := not_le.mp hcon
  have h2 : 2 ≤ ‖Work.BoseBoxFock.kmomLab (Work.BoseBoxFock.ellH v μ) N k‖
      / Work.BoseBoxFock.uvRad (Work.BoseBox.sideAt μ (BoseGases.a v)) N := by
    rw [le_div_iff₀ hΛ]
    linarith
  exact hζ (fu.zero _ h2)

/-! ## 2. The arithmetic: `hN` is the box-size condition of `LabAdd` -/

/-- The numerical hypothesis of the statement, in the exact shape consumed by
`Work.BoseGateFS.kmomLab_sub_of_norm_le`. -/
theorem arith_XY (v : EuclideanSpace ℝ (Fin 3) → ℝ) (μ : ℝ) (N : ℕ)
    (hℓ0 : 0 < Work.BoseBox.sideAt μ (BoseGases.a v))
    (hN : 2 * ((Work.BoseBox.paramsAt μ (BoseGases.a v)).d ^ 2
        * Work.BoseBoxFock.ellH v μ)⁻¹
        * Work.BoseBoxFock.ellH v μ / (2 * Real.pi) ≤ (N : ℝ) / 2)
    (hN1 : 1 ≤ N) :
    Work.BoseBoxFock.ellH v μ
      * (2 * ((Work.BoseBox.paramsAt μ (BoseGases.a v)).d ^ 2
            * Work.BoseBox.sideAt μ (BoseGases.a v))⁻¹
        + 2 * Work.BoseBoxFock.uvRad (Work.BoseBox.sideAt μ (BoseGases.a v)) N)
      / (2 * Real.pi) ≤ (N : ℝ) := by
  have hℓ : Work.BoseBoxFock.ellH v μ = Work.BoseBox.sideAt μ (BoseGases.a v) := by
    rw [Work.BoseBoxFock.ellH, if_pos hℓ0]
  have hA : Work.BoseBox.sideAt μ (BoseGases.a v)
      * (2 * ((Work.BoseBox.paramsAt μ (BoseGases.a v)).d ^ 2
            * Work.BoseBox.sideAt μ (BoseGases.a v))⁻¹) / (2 * Real.pi)
      ≤ (N : ℝ) / 2 := by
    rw [hℓ] at hN
    have heq : Work.BoseBox.sideAt μ (BoseGases.a v)
        * (2 * ((Work.BoseBox.paramsAt μ (BoseGases.a v)).d ^ 2
              * Work.BoseBox.sideAt μ (BoseGases.a v))⁻¹) / (2 * Real.pi)
        = 2 * ((Work.BoseBox.paramsAt μ (BoseGases.a v)).d ^ 2
              * Work.BoseBox.sideAt μ (BoseGases.a v))⁻¹
          * Work.BoseBox.sideAt μ (BoseGases.a v) / (2 * Real.pi) := by ring
    rw [heq]
    exact hN
  have hB : Work.BoseBox.sideAt μ (BoseGases.a v)
      * (2 * Work.BoseBoxFock.uvRad (Work.BoseBox.sideAt μ (BoseGases.a v)) N)
      / (2 * Real.pi) = (N : ℝ) / 2 := by
    rw [Work.BoseBoxFock.uvRad]
    have hne : Work.BoseBox.sideAt μ (BoseGases.a v) ≠ 0 := ne_of_gt hℓ0
    field_simp
    ring
  rw [hℓ,
    show Work.BoseBox.sideAt μ (BoseGases.a v)
        * (2 * ((Work.BoseBox.paramsAt μ (BoseGases.a v)).d ^ 2
              * Work.BoseBox.sideAt μ (BoseGases.a v))⁻¹
          + 2 * Work.BoseBoxFock.uvRad (Work.BoseBox.sideAt μ (BoseGases.a v)) N)
        / (2 * Real.pi)
        = Work.BoseBox.sideAt μ (BoseGases.a v)
            * (2 * ((Work.BoseBox.paramsAt μ (BoseGases.a v)).d ^ 2
                * Work.BoseBox.sideAt μ (BoseGases.a v))⁻¹) / (2 * Real.pi)
          + Work.BoseBox.sideAt μ (BoseGases.a v)
            * (2 * Work.BoseBoxFock.uvRad (Work.BoseBox.sideAt μ (BoseGases.a v)) N)
            / (2 * Real.pi) by ring]
  linarith [hA, hB]

/-! ## 3. The guarded label arithmetic -/

theorem kmomLab_sub_of_support (v : EuclideanSpace ℝ (Fin 3) → ℝ) (h : Work.UBB.ScatSol v)
    (fc fu : Work.BoseBoxFix.LowCut) (μ : ℝ) (N : ℕ)
    (hℓ0 : 0 < Work.BoseBox.sideAt μ (BoseGases.a v))
    (hN : 2 * ((Work.BoseBox.paramsAt μ (BoseGases.a v)).d ^ 2 * Work.BoseBoxFock.ellH v μ)⁻¹
        * Work.BoseBoxFock.ellH v μ / (2 * Real.pi) ≤ (N : ℝ) / 2)
    (hN1 : 1 ≤ N)
    {s k : Work.BoseBoxFock.Lab N}
    (hs : Work.BoseBoxFock.fLh v fc μ N s ≠ 0)
    (hk : Work.BoseBoxFock.W1h v h μ fu N k ≠ 0) :
    Work.BoseBoxFock.kmomLab (Work.BoseBoxFock.ellH v μ) N (s - k)
      = Work.BoseBoxFock.kmomLab (Work.BoseBoxFock.ellH v μ) N s
        - Work.BoseBoxFock.kmomLab (Work.BoseBoxFock.ellH v μ) N k := by
  have hd : 0 < (Work.BoseBox.paramsAt μ (BoseGases.a v)).d :=
    paramsAt_d_pos_of_sideAt_pos hℓ0
  have hD : 0 < ((Work.BoseBox.paramsAt μ (BoseGases.a v)).d ^ 2
      * Work.BoseBox.sideAt μ (BoseGases.a v))⁻¹ :=
    inv_pos.mpr (mul_pos (pow_pos hd 2) hℓ0)
  have hΛ : 0 < Work.BoseBoxFock.uvRad (Work.BoseBox.sideAt μ (BoseGases.a v)) N := by
    rw [Work.BoseBoxFock.uvRad]
    have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN1
    exact div_pos (mul_pos (div_pos (by positivity) hℓ0) hNpos) (by norm_num)
  exact Work.BoseGateFS.kmomLab_sub_of_norm_le (Work.BoseBoxFock.ellH v μ)
    (Work.BoseBoxFock.ellH_pos v μ) N hN1 s k _
    (2 * Work.BoseBoxFock.uvRad (Work.BoseBox.sideAt μ (BoseGases.a v)) N)
    (fLh_norm_le hD hs) (W1h_norm_le hΛ hk) (arith_XY v μ N hℓ0 hN hN1)

end Work.BoseBoxFock
