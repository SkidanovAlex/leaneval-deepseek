/-
# The `K_+^{(24)}` tail on the cusp-`±1` tiles

For `w ∈ E = KEpsilon`, `n = ±1` and `z = i t` with `t ≥ 2 Im (S • w) + 1`, the kernel
`K_+^{(24)}(n+w, z)` differs from its cusp-`i∞` model `𝒢_+^{(24)}(n+w, z)` by
`O((scale w)^N (1+t)^M e^{π Im(Sw) - πt})`, i.e. `TB π 1` of `tileTB`.

On the tiles `t ≥ 2 Im(S•w) + 1 ≥ 5`, so the `z`-atoms are controlled for `t ≥ 5`; this is the
threshold `ZC5`/`ZCg5` calculus below (the tile analogue of `ZC`/`ZCg`, whose threshold is `1`).
The `z`-deviations are the ones of `Work.Asymptotics.K24Fsm.zdev` (`Im z ≥ 3`), the `τ`-atoms are
the `TB` atoms of `tileTB`.
-/
import Mathlib
import Submission.Work.Asymptotics.Tile.tileTB
import Submission.Work.Asymptotics.Tile.KPlus8TileTail
import Submission.Work.Asymptotics.K24FDefs
import Submission.Work.Asymptotics.K24FBase
import Submission.Work.Asymptotics.K24F_sm_sum_bound
import Submission.Work.Asymptotics.funnel_divisor_lower

set_option maxHeartbeats 1000000

namespace Work.Asymptotics.Tile

open UpperHalfPlane ModularGroup
open scoped MatrixGroups UpperHalfPlane Manifold
open Work.Kernels Work.Asymptotics

noncomputable section

/-! ## The `z`-atom calculus at the threshold `t ≥ 5` -/

/-- `ZC5 m n f`: `‖f z‖ ≤ C (1+t)^m e^{-nπt}` on the contour `z = i t`, for `t ≥ 5`. -/
def ZC5 (m n : ℝ) (f : ℍ → ℂ) : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ (z : ℍ) (t : ℝ), 5 ≤ t → (z : ℂ) = (t : ℂ) * Complex.I →
    ‖f z‖ ≤ C * (1 + t) ^ m * Real.exp (-(n * Real.pi * t))

/-- `ZCg5 m n f`: `‖f z‖ ≤ C (1+t)^m e^{nπt}` on the contour `z = i t`, for `t ≥ 5`. -/
def ZCg5 (m n : ℝ) (f : ℍ → ℂ) : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ (z : ℍ) (t : ℝ), 5 ≤ t → (z : ℂ) = (t : ℂ) * Complex.I →
    ‖f z‖ ≤ C * (1 + t) ^ m * Real.exp (n * Real.pi * t)

namespace ZC5

variable {m n m' n' : ℝ} {f g : ℍ → ℂ}

lemma mono (h : ZC5 m n f) (hm : m ≤ m') (hn : n' ≤ n) : ZC5 m' n' f := by
  obtain ⟨C, hC, hb⟩ := h
  refine ⟨C, hC, fun z t ht hz => ?_⟩
  refine le_trans (hb z t ht hz) ?_
  have h1 : (1 + t) ^ m ≤ (1 + t) ^ m' := Real.rpow_le_rpow_of_exponent_le (by linarith) hm
  have h2 : Real.exp (-(n * Real.pi * t)) ≤ Real.exp (-(n' * Real.pi * t)) := by
    rw [Real.exp_le_exp]
    have hmul : n' * (Real.pi * t) ≤ n * (Real.pi * t) :=
      mul_le_mul_of_nonneg_right hn (mul_nonneg Real.pi_pos.le (by linarith))
    nlinarith [hmul]
  exact mul_le_mul (mul_le_mul_of_nonneg_left h1 hC.le) h2 (Real.exp_pos _).le
    (mul_nonneg hC.le (Real.rpow_nonneg (by linarith) _))

lemma add (hf : ZC5 m n f) (hg : ZC5 m' n' g) : ZC5 (max m m') (min n n') (fun z => f z + g z) := by
  obtain ⟨C1, hC1, hb1⟩ := hf
  obtain ⟨C2, hC2, hb2⟩ := hg
  refine ⟨C1 + C2, by positivity, fun z t ht hz => ?_⟩
  have h1 : (1 + t) ^ m ≤ (1 + t) ^ (max m m') :=
    Real.rpow_le_rpow_of_exponent_le (by linarith) (le_max_left _ _)
  have h2 : (1 + t) ^ m' ≤ (1 + t) ^ (max m m') :=
    Real.rpow_le_rpow_of_exponent_le (by linarith) (le_max_right _ _)
  have hm1 : (0:ℝ) ≤ (1 + t) ^ (max m m') := Real.rpow_nonneg (by linarith) _
  have h3 : Real.exp (-(n * Real.pi * t)) ≤ Real.exp (-(min n n' * Real.pi * t)) := by
    rw [Real.exp_le_exp]
    have hmul : min n n' * (Real.pi * t) ≤ n * (Real.pi * t) :=
      mul_le_mul_of_nonneg_right (min_le_left n n') (mul_nonneg Real.pi_pos.le (by linarith))
    nlinarith [hmul]
  have h4 : Real.exp (-(n' * Real.pi * t)) ≤ Real.exp (-(min n n' * Real.pi * t)) := by
    rw [Real.exp_le_exp]
    have hmul : min n n' * (Real.pi * t) ≤ n' * (Real.pi * t) :=
      mul_le_mul_of_nonneg_right (min_le_right n n') (mul_nonneg Real.pi_pos.le (by linarith))
    nlinarith [hmul]
  have hb1' : ‖f z‖ ≤ C1 * (1 + t) ^ (max m m') * Real.exp (-(min n n' * Real.pi * t)) :=
    le_trans (hb1 z t ht hz) (mul_le_mul (mul_le_mul_of_nonneg_left h1 hC1.le) h3
      (Real.exp_pos _).le (mul_nonneg hC1.le hm1))
  have hb2' : ‖g z‖ ≤ C2 * (1 + t) ^ (max m m') * Real.exp (-(min n n' * Real.pi * t)) :=
    le_trans (hb2 z t ht hz) (mul_le_mul (mul_le_mul_of_nonneg_left h2 hC2.le) h4
      (Real.exp_pos _).le (mul_nonneg hC2.le hm1))
  refine le_trans (norm_add_le _ _) ?_
  rw [show (C1 + C2) * (1 + t) ^ (max m m') * Real.exp (-(min n n' * Real.pi * t))
      = C1 * (1 + t) ^ (max m m') * Real.exp (-(min n n' * Real.pi * t))
        + C2 * (1 + t) ^ (max m m') * Real.exp (-(min n n' * Real.pi * t)) from by ring]
  exact add_le_add hb1' hb2'

lemma mul (hf : ZC5 m n f) (hg : ZC5 m' n' g) : ZC5 (m + m') (n + n') (fun z => f z * g z) := by
  obtain ⟨C1, hC1, hb1⟩ := hf
  obtain ⟨C2, hC2, hb2⟩ := hg
  refine ⟨C1 * C2, by positivity, fun z t ht hz => ?_⟩
  rw [norm_mul]
  have h1 := hb1 z t ht hz
  have h2 := hb2 z t ht hz
  have hr : (1 + t) ^ m * (1 + t) ^ m' = (1 + t) ^ (m + m') :=
    (Real.rpow_add (by linarith : (0:ℝ) < 1 + t) m m').symm
  have hexp : Real.exp (-(n * Real.pi * t)) * Real.exp (-(n' * Real.pi * t))
      = Real.exp (-((n + n') * Real.pi * t)) := by
    rw [← Real.exp_add]; congr 1; ring
  have h3 : (0:ℝ) ≤ C1 * (1 + t) ^ m * Real.exp (-(n * Real.pi * t)) :=
    mul_nonneg (mul_nonneg hC1.le (Real.rpow_nonneg (by linarith) _)) (Real.exp_pos _).le
  calc ‖f z‖ * ‖g z‖
      ≤ (C1 * (1 + t) ^ m * Real.exp (-(n * Real.pi * t)))
        * (C2 * (1 + t) ^ m' * Real.exp (-(n' * Real.pi * t))) :=
        mul_le_mul h1 h2 (norm_nonneg _) h3
    _ = C1 * C2 * (1 + t) ^ (m + m') * Real.exp (-((n + n') * Real.pi * t)) := by
        rw [← hr, ← hexp]; ring

lemma neg (hf : ZC5 m n f) : ZC5 m n (fun z => -f z) := by
  obtain ⟨C, hC, hb⟩ := hf
  exact ⟨C, hC, fun z t ht hz => by rw [norm_neg]; exact hb z t ht hz⟩

lemma sub (hf : ZC5 m n f) (hg : ZC5 m' n' g) : ZC5 (max m m') (min n n') (fun z => f z - g z) := by
  simpa only [sub_eq_add_neg] using hf.add hg.neg

lemma congr (h : ZC5 m n f) (hfg : ∀ z, f z = g z) : ZC5 m n g := by
  obtain ⟨C, hC, hb⟩ := h
  exact ⟨C, hC, fun z t ht hz => by rw [← hfg]; exact hb z t ht hz⟩

lemma const (m : ℝ) (hm : 0 ≤ m) (c : ℂ) : ZC5 m 0 (fun _ => c) := by
  refine ⟨‖c‖ + 1, by positivity, fun z t ht hz => ?_⟩
  rw [show -(0 * Real.pi * t) = 0 from by ring, Real.exp_zero, mul_one]
  have h1 : (1:ℝ) ≤ (1 + t) ^ m := Real.one_le_rpow (by linarith) hm
  have h0 : (0:ℝ) ≤ (1 + t) ^ m := Real.rpow_nonneg (by linarith) m
  nlinarith [norm_nonneg c, h1, h0]

lemma cmul (c : ℂ) (h : ZC5 m n f) : ZC5 m n (fun z => c * f z) :=
  ((const 0 le_rfl c).mul h).mono (m' := m) (n' := n) (by linarith) (by linarith)

end ZC5

namespace ZCg5

variable {m n m' n' : ℝ} {f g : ℍ → ℂ}

lemma mono (h : ZCg5 m n f) (hm : m ≤ m') (hn : n ≤ n') : ZCg5 m' n' f := by
  obtain ⟨C, hC, hb⟩ := h
  refine ⟨C, hC, fun z t ht hz => ?_⟩
  refine le_trans (hb z t ht hz) ?_
  have h1 : (1 + t) ^ m ≤ (1 + t) ^ m' := Real.rpow_le_rpow_of_exponent_le (by linarith) hm
  have h2 : Real.exp (n * Real.pi * t) ≤ Real.exp (n' * Real.pi * t) := by
    rw [Real.exp_le_exp]
    have hmul : n * (Real.pi * t) ≤ n' * (Real.pi * t) :=
      mul_le_mul_of_nonneg_right hn (mul_nonneg Real.pi_pos.le (by linarith))
    nlinarith [hmul]
  exact mul_le_mul (mul_le_mul_of_nonneg_left h1 hC.le) h2 (Real.exp_pos _).le
    (mul_nonneg hC.le (Real.rpow_nonneg (by linarith) _))

lemma congr (h : ZCg5 m n f) (hfg : ∀ z, f z = g z) : ZCg5 m n g := by
  obtain ⟨C, hC, hb⟩ := h
  exact ⟨C, hC, fun z t ht hz => by rw [← hfg]; exact hb z t ht hz⟩

lemma of_ZC (h : ZC5 m n f) (hn : 0 ≤ n) : ZCg5 m n f := by
  obtain ⟨C, hC, hb⟩ := h
  refine ⟨C, hC, fun z t ht hz => ?_⟩
  refine le_trans (hb z t ht hz) ?_
  have h1 : Real.exp (-(n * Real.pi * t)) ≤ Real.exp (n * Real.pi * t) := by
    rw [Real.exp_le_exp]
    have hnt : 0 ≤ n * (Real.pi * t) := mul_nonneg hn (mul_nonneg Real.pi_pos.le (by linarith))
    linarith
  exact mul_le_mul_of_nonneg_left h1 (mul_nonneg hC.le (Real.rpow_nonneg (by linarith) _))

end ZCg5

/-- Glue a decaying `z`-atom to a `TB` bound (threshold `5`). -/
lemma TB.mul_ZC5 {m n : ℝ} (hm : 0 ≤ m) {f : ℍ → ℂ} {G : ℍ → ℤ → ℍ → ℂ} {a b : ℝ}
    (hf : ZC5 m n f) (hG : TB a b G) : TB a (b + n) (fun w k z => f z * G w k z) := by
  obtain ⟨C1, hC1, hb1⟩ := hf
  obtain ⟨C2, N2, M2, hC2, hN2, hM2, hb2⟩ := hG
  refine ⟨C1 * C2, N2, M2 + m, by positivity, hN2, by linarith,
    fun w k z t hk hw hz ht => ?_⟩
  have ht5 : (5:ℝ) ≤ t := by have h := hw.2; linarith
  rw [norm_mul]
  have hfz := hb1 z t ht5 hz
  have hS := hb2 w k z t hk hw hz ht
  refine le_trans (mul_le_mul hfz hS (norm_nonneg _)
    (mul_nonneg (mul_nonneg hC1.le (Real.rpow_nonneg (by linarith) _)) (Real.exp_pos _).le)) ?_
  have hr : (1 + t) ^ m * (1 + t) ^ M2 = (1 + t) ^ (M2 + m) := by
    rw [mul_comm, ← Real.rpow_add (by linarith : (0:ℝ) < 1 + t) M2 m]
  have hexp : Real.exp (-(n * Real.pi * t))
      * Real.exp (a * (ModularGroup.S • w).im - b * Real.pi * t)
      = Real.exp (a * (ModularGroup.S • w).im - (b + n) * Real.pi * t) := by
    rw [← Real.exp_add]; congr 1; ring
  rw [show (C1 * (1 + t) ^ m * Real.exp (-(n * Real.pi * t)))
        * (C2 * (Work.Kernels.scale w) ^ N2 * (1 + t) ^ M2
          * Real.exp (a * (ModularGroup.S • w).im - b * Real.pi * t))
      = C1 * C2 * (Work.Kernels.scale w) ^ N2 * ((1 + t) ^ m * (1 + t) ^ M2)
        * (Real.exp (-(n * Real.pi * t))
          * Real.exp (a * (ModularGroup.S • w).im - b * Real.pi * t)) from by ring,
    hr, hexp]

/-- Glue a growing `z`-atom to a `TB` bound (threshold `5`). -/
lemma TB.mul_ZCg5 {m n : ℝ} (hm : 0 ≤ m) {f : ℍ → ℂ} {G : ℍ → ℤ → ℍ → ℂ} {a b : ℝ}
    (hf : ZCg5 m n f) (hG : TB a b G) : TB a (b - n) (fun w k z => f z * G w k z) := by
  obtain ⟨C1, hC1, hb1⟩ := hf
  obtain ⟨C2, N2, M2, hC2, hN2, hM2, hb2⟩ := hG
  refine ⟨C1 * C2, N2, M2 + m, by positivity, hN2, by linarith,
    fun w k z t hk hw hz ht => ?_⟩
  have ht5 : (5:ℝ) ≤ t := by have h := hw.2; linarith
  rw [norm_mul]
  have hfz := hb1 z t ht5 hz
  have hS := hb2 w k z t hk hw hz ht
  refine le_trans (mul_le_mul hfz hS (norm_nonneg _)
    (mul_nonneg (mul_nonneg hC1.le (Real.rpow_nonneg (by linarith) _)) (Real.exp_pos _).le)) ?_
  have hr : (1 + t) ^ m * (1 + t) ^ M2 = (1 + t) ^ (M2 + m) := by
    rw [mul_comm, ← Real.rpow_add (by linarith : (0:ℝ) < 1 + t) M2 m]
  have hexp : Real.exp (n * Real.pi * t)
      * Real.exp (a * (ModularGroup.S • w).im - b * Real.pi * t)
      = Real.exp (a * (ModularGroup.S • w).im - (b - n) * Real.pi * t) := by
    rw [← Real.exp_add]; congr 1; ring
  rw [show (C1 * (1 + t) ^ m * Real.exp (n * Real.pi * t))
        * (C2 * (Work.Kernels.scale w) ^ N2 * (1 + t) ^ M2
          * Real.exp (a * (ModularGroup.S • w).im - b * Real.pi * t))
      = C1 * C2 * (Work.Kernels.scale w) ^ N2 * ((1 + t) ^ m * (1 + t) ^ M2)
        * (Real.exp (n * Real.pi * t)
          * Real.exp (a * (ModularGroup.S • w).im - b * Real.pi * t)) from by ring,
    hr, hexp]


/-! ## The `z`-deviations of `zdev` in terms of `K24F.S0` -/

private lemma zdev_K24F : ∃ A : ℝ, 0 < A ∧ ∀ z : ℍ, 3 ≤ z.im →
      ‖E4Fun z - 1‖ ≤ A * ‖qParamFun z‖ ∧
      ‖E4Fun z ^ 3 - 1‖ ≤ A * ‖qParamFun z‖ ∧
      ‖E2S z ^ 2 - K24F.S0 z ^ 2‖ ≤ A * ‖qParamFun z‖ ∧
      ‖E6Fun z * E2S z / E4Fun z - K24F.S0 z‖ ≤ A * ‖qParamFun z‖ ∧
      ‖E6Fun z * E2S z / E4Fun z - K24F.S0 z + 24 * qParamFun z
          + 744 * qParamFun z * K24F.S0 z‖ ≤ A * ‖qParamFun z‖ ^ 2 ∧
      ‖E2S z - K24F.S0 z + 24 * qParamFun z‖ ≤ A * ‖qParamFun z‖ ^ 2 ∧
      ‖E4Fun z - 1 - 240 * qParamFun z‖ ≤ A * ‖qParamFun z‖ ^ 2 ∧
      ‖qParamFun z / DeltaFun z - 1‖ ≤ A * ‖qParamFun z‖ ∧
      ‖(DeltaFun z)⁻¹ - (qParamFun z)⁻¹ - 24‖ ≤ A * ‖qParamFun z‖ ∧
      ‖1 - DeltaFun z / qParamFun z‖ ≤ A * ‖qParamFun z‖ ∧
      (1 / 2) * ‖qParamFun z‖ ≤ ‖DeltaFun z‖ ∧
      ‖(DeltaFun z)⁻¹‖ ≤ A * ‖qParamFun z‖⁻¹ ∧
      ‖(E4Fun z)⁻¹‖ ≤ 2 ∧
      ‖E4Fun z‖ ≤ 3 / 2 ∧
      ‖K24F.S0 z‖ ≤ 3 := by
  obtain ⟨A, hAp, hA⟩ := K24Fsm.zdev
  refine ⟨A, hAp, fun z hz => ?_⟩
  obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15⟩ := hA z hz
  exact ⟨a1, a2, by simpa only [← K24Fsm.S0_eq_S0c] using a3,
    by simpa only [← K24Fsm.S0_eq_S0c] using a4,
    by simpa only [← K24Fsm.S0_eq_S0c] using a5,
    by simpa only [← K24Fsm.S0_eq_S0c] using a6, a7, a8, a9,
    by simpa only [← K24Fsm.S0_eq_S0c] using a10, a11, a12, a13, a14,
    by simpa only [← K24Fsm.S0_eq_S0c] using a15⟩

/-! ## Conversion of the `q`-power bounds to `ZC5`/`ZCg5` -/

lemma ZC5.of_qpow1 {f : ℍ → ℂ}
    (h : ∃ A : ℝ, 0 < A ∧ ∀ z : ℍ, 3 ≤ z.im → ‖f z‖ ≤ A * ‖qParamFun z‖) :
    ZC5 0 2 f := by
  obtain ⟨A, hA, hb⟩ := h
  refine ⟨A, hA, fun z t ht5 hz => ?_⟩
  have hzim : z.im = t := K24F.im_of_coe_eq_axis hz
  have hz3 : (3:ℝ) ≤ z.im := by rw [hzim]; linarith
  have h := hb z hz3
  have hq : ‖qParamFun z‖ = Real.exp (-(2 * Real.pi * t)) := by
    rw [norm_qParamFun, hzim]
  rw [hq] at h
  simpa using h

lemma ZC5.of_qpow2 {f : ℍ → ℂ}
    (h : ∃ A : ℝ, 0 < A ∧ ∀ z : ℍ, 3 ≤ z.im → ‖f z‖ ≤ A * ‖qParamFun z‖ ^ 2) :
    ZC5 0 4 f := by
  obtain ⟨A, hA, hb⟩ := h
  refine ⟨A, hA, fun z t ht5 hz => ?_⟩
  have hzim : z.im = t := K24F.im_of_coe_eq_axis hz
  have hz3 : (3:ℝ) ≤ z.im := by rw [hzim]; linarith
  have h := hb z hz3
  have hq : ‖qParamFun z‖ ^ 2 = Real.exp (-(4 * Real.pi * t)) := by
    rw [norm_qParamFun, hzim, ← Real.exp_nat_mul]
    congr 1
    push_cast
    ring
  rw [hq] at h
  simpa using h

lemma ZC5.of_qbdd {f : ℍ → ℂ}
    (h : ∃ A : ℝ, 0 < A ∧ ∀ z : ℍ, 3 ≤ z.im → ‖f z‖ ≤ A) : ZC5 0 0 f := by
  obtain ⟨A, hA, hb⟩ := h
  refine ⟨A, hA, fun z t ht5 hz => ?_⟩
  have hzim : z.im = t := K24F.im_of_coe_eq_axis hz
  have hz3 : (3:ℝ) ≤ z.im := by rw [hzim]; linarith
  have h := hb z hz3
  rw [show -(0 * Real.pi * t) = 0 from by ring, Real.exp_zero, Real.rpow_zero, mul_one, mul_one]
  exact h

lemma ZCg5.of_qinv {f : ℍ → ℂ}
    (h : ∃ A : ℝ, 0 < A ∧ ∀ z : ℍ, 3 ≤ z.im → ‖f z‖ ≤ A * ‖qParamFun z‖⁻¹) :
    ZCg5 0 2 f := by
  obtain ⟨A, hA, hb⟩ := h
  refine ⟨A, hA, fun z t ht5 hz => ?_⟩
  have hzim : z.im = t := K24F.im_of_coe_eq_axis hz
  have hz3 : (3:ℝ) ≤ z.im := by rw [hzim]; linarith
  have h := hb z hz3
  have hq : ‖qParamFun z‖⁻¹ = Real.exp (2 * Real.pi * t) := by
    rw [norm_qParamFun, hzim, ← Real.exp_neg]
    congr 1
    ring
  rw [hq] at h
  simpa using h

/-! ## The `z`-atoms -/

lemma ZC5.ktl24_q : ZC5 0 2 (fun z : ℍ => qParamFun z) := by
  refine ⟨1, one_pos, fun z t ht5 hz => ?_⟩
  rw [norm_qParamFun, K24F.im_of_coe_eq_axis hz]
  simp

lemma ZC5.ktl24_z : ZC5 1 0 (fun z : ℍ => (z : ℂ)) := by
  refine ⟨1, one_pos, fun z t ht5 hz => ?_⟩
  have hzt : ‖(z : ℂ)‖ = t := ktl_norm_coe (by linarith) hz
  rw [hzt, Real.rpow_one, show -(0 * Real.pi * t) = 0 from by ring, Real.exp_zero]
  simp only [mul_one]
  linarith

lemma ZC5.ktl24_zsq : ZC5 2 0 (fun z : ℍ => (z : ℂ) ^ 2) :=
  ZC5.congr ((ZC5.ktl24_z.mul ZC5.ktl24_z).mono (m' := 2) (n' := 0) (by norm_num) (by norm_num))
    (fun z => by ring)

lemma ZC5.ktl24_E4sub1 : ZC5 0 2 (fun z : ℍ => E4Fun z - 1) := by
  obtain ⟨A, hAp, hA⟩ := zdev_K24F
  exact ZC5.of_qpow1 ⟨A, hAp, fun z hz => (hA z hz).1⟩

lemma ZC5.ktl24_E4cube_sub1 : ZC5 0 2 (fun z : ℍ => E4Fun z ^ 3 - 1) := by
  obtain ⟨A, hAp, hA⟩ := zdev_K24F
  exact ZC5.of_qpow1 ⟨A, hAp, fun z hz => (hA z hz).2.1⟩

lemma ZC5.ktl24_E2Ssq_sub_S0sq :
    ZC5 0 2 (fun z : ℍ => E2S z ^ 2 - K24F.S0 z ^ 2) := by
  obtain ⟨A, hAp, hA⟩ := zdev_K24F
  exact ZC5.of_qpow1 ⟨A, hAp, fun z hz => (hA z hz).2.2.1⟩

lemma ZC5.ktl24_E6E2S_div_E4_sub_S0 :
    ZC5 0 2 (fun z : ℍ => E6Fun z * E2S z / E4Fun z - K24F.S0 z) := by
  obtain ⟨A, hAp, hA⟩ := zdev_K24F
  exact ZC5.of_qpow1 ⟨A, hAp, fun z hz => (hA z hz).2.2.2.1⟩

lemma ZC5.ktl24_X4 : ZC5 0 4 (fun z : ℍ => E6Fun z * E2S z / E4Fun z - K24F.S0 z
      + 24 * qParamFun z + 744 * qParamFun z * K24F.S0 z) := by
  obtain ⟨A, hAp, hA⟩ := zdev_K24F
  exact ZC5.of_qpow2 ⟨A, hAp, fun z hz => (hA z hz).2.2.2.2.1⟩

lemma ZC5.ktl24_E4sub1_sub240q :
    ZC5 0 4 (fun z : ℍ => E4Fun z - 1 - 240 * qParamFun z) := by
  obtain ⟨A, hAp, hA⟩ := zdev_K24F
  exact ZC5.of_qpow2 ⟨A, hAp, fun z hz => (hA z hz).2.2.2.2.2.2.1⟩

lemma ZC5.ktl24_q_div_Delta_sub1 :
    ZC5 0 2 (fun z : ℍ => qParamFun z / DeltaFun z - 1) := by
  obtain ⟨A, hAp, hA⟩ := zdev_K24F
  exact ZC5.of_qpow1 ⟨A, hAp, fun z hz => (hA z hz).2.2.2.2.2.2.2.1⟩

lemma ZC5.ktl24_d1 :
    ZC5 0 2 (fun z : ℍ => (DeltaFun z)⁻¹ - (qParamFun z)⁻¹ - 24) := by
  obtain ⟨A, hAp, hA⟩ := zdev_K24F
  exact ZC5.of_qpow1 ⟨A, hAp, fun z hz => (hA z hz).2.2.2.2.2.2.2.2.1⟩

lemma ZC5.ktl24_one_sub_Delta_div_q :
    ZC5 0 2 (fun z : ℍ => 1 - DeltaFun z / qParamFun z) := by
  obtain ⟨A, hAp, hA⟩ := zdev_K24F
  exact ZC5.of_qpow1 ⟨A, hAp, fun z hz => (hA z hz).2.2.2.2.2.2.2.2.2.1⟩

lemma ZCg5.ktl24_Delta_inv : ZCg5 0 2 (fun z : ℍ => (DeltaFun z)⁻¹) := by
  obtain ⟨A, hAp, hA⟩ := zdev_K24F
  exact ZCg5.of_qinv ⟨A, hAp, fun z hz => (hA z hz).2.2.2.2.2.2.2.2.2.2.2.1⟩

lemma ZC5.ktl24_E4inv : ZC5 0 0 (fun z : ℍ => (E4Fun z)⁻¹) := by
  obtain ⟨A, hAp, hA⟩ := zdev_K24F
  exact ZC5.of_qbdd ⟨2, by norm_num, fun z hz => (hA z hz).2.2.2.2.2.2.2.2.2.2.2.2.1⟩

lemma ZC5.ktl24_E4 : ZC5 0 0 (fun z : ℍ => E4Fun z) := by
  obtain ⟨A, hAp, hA⟩ := zdev_K24F
  exact ZC5.of_qbdd ⟨3 / 2, by norm_num, fun z hz => (hA z hz).2.2.2.2.2.2.2.2.2.2.2.2.2.1⟩

lemma ZC5.ktl24_S0 : ZC5 0 0 (fun z : ℍ => K24F.S0 z) := by
  obtain ⟨A, hAp, hA⟩ := zdev_K24F
  exact ZC5.of_qbdd ⟨3, by norm_num, fun z hz => (hA z hz).2.2.2.2.2.2.2.2.2.2.2.2.2.2⟩

lemma ZC5.ktl24_B2 : ZC5 0 4 (fun z : ℍ => K24F.B2 z) := by
  obtain ⟨C, hC, hb⟩ := b2_le
  exact ZC5.of_qpow2 ⟨C, hC, hb⟩

/-- `Δ(z) = q(z) · (Δ(z)/q(z))`. -/
lemma ZC5.ktl24_Delta : ZC5 0 2 (fun z : ℍ => DeltaFun z) := by
  have h0 : ZC5 0 0 (fun z : ℍ => 1 - (1 - DeltaFun z / qParamFun z)) :=
    ((ZC5.const 0 le_rfl (1 : ℂ)).sub ZC5.ktl24_one_sub_Delta_div_q).mono
      (m' := 0) (n' := 0) (by norm_num) (by norm_num)
  have h1 : ZC5 0 0 (fun z : ℍ => DeltaFun z / qParamFun z) :=
    h0.congr (fun z => by ring)
  refine ((ZC5.ktl24_q.mul h1).mono (m' := 0) (n' := 2) (by norm_num) (by norm_num)).congr
    (fun z => ?_)
  rw [div_eq_mul_inv]
  field_simp

lemma ZC5.ktl24_one_sub_E4cube : ZC5 0 2 (fun z : ℍ => 1 - E4Fun z ^ 3) :=
  ZC5.ktl24_E4cube_sub1.neg.congr (fun z => by ring)

lemma ZC5.ktl24_E4cube : ZC5 0 0 (fun z : ℍ => E4Fun z ^ 3) :=
  (((ZC5.ktl24_E4.mul ZC5.ktl24_E4).mul ZC5.ktl24_E4).mono (m' := 0) (n' := 0)
    (by norm_num) (by norm_num)).congr (fun z => by ring)

lemma ZC5.ktl24_S0sq : ZC5 0 0 (fun z : ℍ => K24F.S0 z ^ 2) :=
  ((ZC5.ktl24_S0.mul ZC5.ktl24_S0).mono (m' := 0) (n' := 0) (by norm_num)
    (by norm_num)).congr (fun z => by ring)

lemma ZC5.ktl24_12_E2Ssq_sub_S0sq :
    ZC5 0 2 (fun z : ℍ => 12 * (E2S z ^ 2 - K24F.S0 z ^ 2)) :=
  ZC5.ktl24_E2Ssq_sub_S0sq.cmul 12

lemma ZC5.ktl24_12_E4sub1 : ZC5 0 2 (fun z : ℍ => 12 * (E4Fun z - 1)) :=
  ZC5.ktl24_E4sub1.cmul 12

lemma ZC5.ktl24_8640_E4sub1 : ZC5 0 2 (fun z : ℍ => 8640 * (E4Fun z - 1)) :=
  ZC5.ktl24_E4sub1.cmul 8640

lemma ZC5.ktl24_12096_E2Ssq_sub_S0sq :
    ZC5 0 2 (fun z : ℍ => 12096 * (E2S z ^ 2 - K24F.S0 z ^ 2)) :=
  ZC5.ktl24_E2Ssq_sub_S0sq.cmul 12096

lemma ZC5.ktl24_E4sub1_sub_E2Ssq :
    ZC5 0 2 (fun z : ℍ => (E4Fun z - 1) - (E2S z ^ 2 - K24F.S0 z ^ 2)) :=
  (ZC5.ktl24_E4sub1.sub ZC5.ktl24_E2Ssq_sub_S0sq).mono (m' := 0) (n' := 2)
    (by norm_num) (by norm_num)

lemma ZC5.ktl24_dev2 : ZC5 0 2 (fun z : ℍ =>
    12 * (E2S z ^ 2 - K24F.S0 z ^ 2) - 12 * (E4Fun z - 1)) :=
  (ZC5.ktl24_12_E2Ssq_sub_S0sq.sub ZC5.ktl24_12_E4sub1).mono (m' := 0) (n' := 2)
    (by norm_num) (by norm_num)

lemma ZC5.ktl24_dev3 : ZC5 0 2 (fun z : ℍ =>
    8640 * (E4Fun z - 1) - 12096 * (E2S z ^ 2 - K24F.S0 z ^ 2)) :=
  (ZC5.ktl24_8640_E4sub1.sub ZC5.ktl24_12096_E2Ssq_sub_S0sq).mono (m' := 0) (n' := 2)
    (by norm_num) (by norm_num)

lemma ZC5.ktl24_12_B2 : ZC5 0 4 (fun z : ℍ => 12 * K24F.B2 z) := ZC5.ktl24_B2.cmul 12

lemma ZC5.ktl24_12_E4sub1_sub240q :
    ZC5 0 4 (fun z : ℍ => 12 * (E4Fun z - 1 - 240 * qParamFun z)) :=
  ZC5.ktl24_E4sub1_sub240q.cmul 12

lemma ZC5.ktl24_8640_E4sub1_sub240q :
    ZC5 0 4 (fun z : ℍ => 8640 * (E4Fun z - 1 - 240 * qParamFun z)) :=
  ZC5.ktl24_E4sub1_sub240q.cmul 8640

lemma ZC5.ktl24_12096_B2 : ZC5 0 4 (fun z : ℍ => 12096 * K24F.B2 z) :=
  ZC5.ktl24_B2.cmul 12096

lemma ZC5.ktl24_devb1 : ZC5 0 4 (fun z : ℍ =>
    (E4Fun z - 1 - 240 * qParamFun z) - K24F.B2 z) :=
  (ZC5.ktl24_E4sub1_sub240q.sub ZC5.ktl24_B2).mono (m' := 0) (n' := 4)
    (by norm_num) (by norm_num)

lemma ZC5.ktl24_devb2 : ZC5 0 4 (fun z : ℍ =>
    12 * K24F.B2 z - 12 * (E4Fun z - 1 - 240 * qParamFun z)) :=
  (ZC5.ktl24_12_B2.sub ZC5.ktl24_12_E4sub1_sub240q).mono (m' := 0) (n' := 4)
    (by norm_num) (by norm_num)

lemma ZC5.ktl24_devb3 : ZC5 0 4 (fun z : ℍ =>
    8640 * (E4Fun z - 1 - 240 * qParamFun z) - 12096 * K24F.B2 z) :=
  (ZC5.ktl24_8640_E4sub1_sub240q.sub ZC5.ktl24_12096_B2).mono (m' := 0) (n' := 4)
    (by norm_num) (by norm_num)

lemma ZC5.ktl24_Sm3bracket : ZC5 0 2 (fun z : ℍ =>
    K24F.S0 z * (E4Fun z ^ 3 - 1) - (E6Fun z * E2S z / E4Fun z - K24F.S0 z)) :=
  ((ZC5.ktl24_S0.mul ZC5.ktl24_E4cube_sub1).sub ZC5.ktl24_E6E2S_div_E4_sub_S0).mono
    (m' := 0) (n' := 2) (by norm_num) (by norm_num)


lemma ZC5.ktl24_one_sub_S0sq : ZC5 0 0 (fun z : ℍ => 1 - K24F.S0 z ^ 2) :=
  ((ZC5.const 0 le_rfl (1 : ℂ)).sub ZC5.ktl24_S0sq).mono (m' := 0) (n' := 0)
    (by norm_num) (by norm_num)

/-! ## The `τ`-atoms on the tiles -/

lemma TB.ktl24_r0 : TB 0 0 (fun w n _ => K24F.r0 ((n : ℝ) +ᵥ w)) :=
  ((TB.mul TB.ktl8_tau TB.E14).mono (by norm_num) (by norm_num)).congr
    (fun w n z => by simp only [K24F.r0])

lemma TB.ktl24_r1 : TB 0 0 (fun w n _ => K24F.r1 ((n : ℝ) +ᵥ w)) := by
  have h : TB 0 0 (fun w n _ => Work.Kernels.phi0 ((n : ℝ) +ᵥ w)
      * DeltaFun ((n : ℝ) +ᵥ w)) :=
    (TB.mul TB.phi0 TB.Delta).mono (by linarith [Real.pi_pos]) (by norm_num)
  exact h.congr (fun w n z => by simp only [K24F.r1, Compact.phi1, Work.Kernels.phi0])

lemma TB.ktl24_E4cube : TB 0 0 (fun w n _ => E4Fun ((n : ℝ) +ᵥ w) ^ 3) :=
  (((TB.mul TB.E4 TB.E4).mul TB.E4).mono (by norm_num) (by norm_num)).congr
    (fun w n z => by ring)

lemma TB.ktl24_r2 : TB 0 0 (fun w n _ => K24F.r2 ((n : ℝ) +ᵥ w)) := by
  have h : TB 0 0 (fun w n _ => Work.Kernels.phi2 ((n : ℝ) +ᵥ w)
      * E10Fun ((n : ℝ) +ᵥ w)) := (TB.mul TB.phi2 TB.E10).mono (by norm_num) (by norm_num)
  exact h.congr (fun w n z => by simp only [K24F.r2, Compact.phi2t, Work.Kernels.phi2])

lemma TB.ktl24_R0 : TB 0 0 (fun w n _ => K24F.R0 ((n : ℝ) +ᵥ w)) := by
  have h : TB 0 0 (fun w n _ => Work.Kernels.phi0 ((n : ℝ) +ᵥ w)
      * E4Fun ((n : ℝ) +ᵥ w) ^ 3) :=
    (TB.mul TB.phi0 TB.ktl24_E4cube).mono (by norm_num) (by norm_num)
  exact h.congr (fun w n z => by simp only [K24F.R0, Compact.phi1, Work.Kernels.phi0])

lemma TB.ktl24_j : TB (2 * Real.pi) 0 (fun w n _ => jInvariantFun ((n : ℝ) +ᵥ w)) := TB.j

/-! ## `Phiref`, `Q1`, `Uref`, `Th0` -/

lemma TB.ktl24_Phiref : TB 0 0 (fun w n z => K24F.Phiref ((n : ℝ) +ᵥ w) z) := by
  have h1 : TB 0 0 (fun w n z => (1 - K24F.S0 z ^ 2)
      * (6 * (K24F.r0 ((n : ℝ) +ᵥ w) + K24F.r2 ((n : ℝ) +ᵥ w)))) :=
    (TB.mul_ZC5 (le_refl 0) ZC5.ktl24_one_sub_S0sq
      (TB.const_mul 6 (TB.add TB.ktl24_r0 TB.ktl24_r2))).mono (le_refl 0) (by norm_num)
  have h2 : TB 0 0 (fun w n z => K24F.S0 z ^ 2
      * (12 * K24F.R0 ((n : ℝ) +ᵥ w) - 12096 * K24F.r1 ((n : ℝ) +ᵥ w))) :=
    (TB.mul_ZC5 (le_refl 0) ZC5.ktl24_S0sq
      (TB.sub (TB.const_mul 12 TB.ktl24_R0) (TB.const_mul 12096 TB.ktl24_r1))).mono
      (le_refl 0) (by norm_num)
  have h3 : TB 0 0 (fun w n z => -12 * K24F.R0 ((n : ℝ) +ᵥ w)
      + 8640 * K24F.r1 ((n : ℝ) +ᵥ w)) :=
    TB.add (TB.const_mul (-12) TB.ktl24_R0) (TB.const_mul 8640 TB.ktl24_r1)
  have h4 : TB 0 0 (fun w n z => K24F.S0 z * (3456 * K24F.r1 ((n : ℝ) +ᵥ w))) :=
    (TB.mul_ZC5 (le_refl 0) ZC5.ktl24_S0 (TB.const_mul 3456 TB.ktl24_r1)).mono
      (le_refl 0) (by norm_num)
  exact (TB.add (TB.add (TB.add h1 h2) h3) h4).congr (fun w n z => by
    rw [K24Fsm.phiref_jfree]; ring)

lemma TB.ktl24_Q1 : TB 0 0 (fun w n z => K24F.Q1 ((n : ℝ) +ᵥ w) z) := by
  have hz : ZC5 0 0 (fun z : ℍ => (1440 : ℂ) + 288 * K24F.S0 z) :=
    ((ZC5.const 0 le_rfl (1440 : ℂ)).add
      ((ZC5.const 0 le_rfl (288 : ℂ)).mul ZC5.ktl24_S0)).mono
      (m' := 0) (n' := 0) (by norm_num) (by norm_num)
  have h1 : TB 0 0 (fun w n z => ((1440 : ℂ) + 288 * K24F.S0 z)
      * (K24F.r0 ((n : ℝ) +ᵥ w) + K24F.r2 ((n : ℝ) +ᵥ w))) :=
    (TB.mul_ZC5 (le_refl 0) hz (TB.add TB.ktl24_r0 TB.ktl24_r2)).mono (le_refl 0) (by norm_num)
  have h2 : TB 0 0 (fun w n z => -2880 * K24F.R0 ((n : ℝ) +ᵥ w)
      + 2073600 * K24F.r1 ((n : ℝ) +ᵥ w)) :=
    TB.add (TB.const_mul (-2880) TB.ktl24_R0) (TB.const_mul 2073600 TB.ktl24_r1)
  have h3 : TB 0 0 (fun w n z => K24F.S0 z * (-576 * K24F.R0 ((n : ℝ) +ᵥ w))) :=
    (TB.mul_ZC5 (le_refl 0) ZC5.ktl24_S0 (TB.const_mul (-576) TB.ktl24_R0)).mono
      (le_refl 0) (by norm_num)
  have h4 : TB 0 0 (fun w n z => K24F.S0 z * (580608 * K24F.r1 ((n : ℝ) +ᵥ w))) :=
    (TB.mul_ZC5 (le_refl 0) ZC5.ktl24_S0 (TB.const_mul 580608 TB.ktl24_r1)).mono
      (le_refl 0) (by norm_num)
  have h5 : TB 0 0 (fun w n z => -82944 * K24F.r1 ((n : ℝ) +ᵥ w)) :=
    TB.const_mul (-82944) TB.ktl24_r1
  have h6 : TB 0 0 (fun w n z => K24F.S0 z * (2571264 * K24F.r1 ((n : ℝ) +ᵥ w))) :=
    (TB.mul_ZC5 (le_refl 0) ZC5.ktl24_S0 (TB.const_mul 2571264 TB.ktl24_r1)).mono
      (le_refl 0) (by norm_num)
  exact (TB.sub (TB.add (TB.add (TB.add (TB.add h1 h2) h3) h4) h5) h6).congr
    (fun w n z => by rw [K24Fsm.q1_jfree]; ring)

lemma TB.ktl24_Uref : TB 0 0 (fun w n z => K24F.Uref ((n : ℝ) +ᵥ w) z) := by
  have h1 : TB 0 0 (fun w n z => K24F.S0 z ^ 2 * (1728 * K24F.r0 ((n : ℝ) +ᵥ w))) :=
    (TB.mul_ZC5 (le_refl 0) ZC5.ktl24_S0sq (TB.const_mul 1728 TB.ktl24_r0)).mono
      (le_refl 0) (by norm_num)
  have h2 : TB 0 0 (fun w n z => 1728 * K24F.r2 ((n : ℝ) +ᵥ w)) :=
    TB.const_mul 1728 TB.ktl24_r2
  exact (TB.add h1 h2).congr (fun w n z => by simp only [K24F.Uref]; ring)

lemma TB.ktl24_Th0 : TB 0 0 (fun w n z => K24F.Th0 ((n : ℝ) +ᵥ w) z) := by
  have h1 : TB 0 0 (fun w n z => K24F.S0 z * (3456 * K24F.R0 ((n : ℝ) +ᵥ w))) :=
    (TB.mul_ZC5 (le_refl 0) ZC5.ktl24_S0 (TB.const_mul 3456 TB.ktl24_R0)).mono
      (le_refl 0) (by norm_num)
  have h2 : TB 0 0 (fun w n z => 24 * K24F.Phiref ((n : ℝ) +ᵥ w) z) :=
    TB.const_mul 24 TB.ktl24_Phiref
  exact (TB.add (TB.sub (TB.add TB.ktl24_Q1 h2) TB.ktl24_Uref) h1).congr
    (fun w n z => by simp only [K24F.Th0]; ring)

/-! ## `Φ - Φref` and `Φ - Φref - q·Q⁽¹⁾` -/

private lemma ktl24_E4ne : ∀ (w : ℍ) (n : ℤ) (z : ℍ) (t : ℝ), (n = 1 ∨ n = -1) →
    w ∈ KEpsilon → (z : ℂ) = (t : ℂ) * Complex.I → 2 * (ModularGroup.S • w).im + 1 ≤ t →
    E4Fun z ≠ 0 := by
  intro w n z t hn hw hz ht
  have hzim : z.im = t := K24F.im_of_coe_eq_axis hz
  exact K24F.E4_ne_zero_three z (by rw [hzim]; have h := hw.2; linarith)

lemma TB.ktl24_Phi_sub_Phiref :
    TB 0 2 (fun w n z => K24F.Phi ((n : ℝ) +ᵥ w) z - K24F.Phiref ((n : ℝ) +ᵥ w) z) := by
  have h1 : TB 0 2 (fun w n z => ((E4Fun z - 1) - (E2S z ^ 2 - K24F.S0 z ^ 2))
      * (6 * (K24F.r0 ((n : ℝ) +ᵥ w) + K24F.r2 ((n : ℝ) +ᵥ w)))) :=
    (TB.mul_ZC5 (le_refl 0) ZC5.ktl24_E4sub1_sub_E2Ssq
      (TB.const_mul 6 (TB.add TB.ktl24_r0 TB.ktl24_r2))).mono (le_refl 0) (by norm_num)
  have h2 : TB 0 2 (fun w n z => (12 * (E2S z ^ 2 - K24F.S0 z ^ 2) - 12 * (E4Fun z - 1))
      * K24F.R0 ((n : ℝ) +ᵥ w)) :=
    (TB.mul_ZC5 (le_refl 0) ZC5.ktl24_dev2 TB.ktl24_R0).mono (le_refl 0) (by norm_num)
  have h3 : TB 0 2 (fun w n z => (8640 * (E4Fun z - 1)
      - 12096 * (E2S z ^ 2 - K24F.S0 z ^ 2)) * K24F.r1 ((n : ℝ) +ᵥ w)) :=
    (TB.mul_ZC5 (le_refl 0) ZC5.ktl24_dev3 TB.ktl24_r1).mono (le_refl 0) (by norm_num)
  have h4 : TB 0 2 (fun w n z => (E6Fun z * E2S z / E4Fun z - K24F.S0 z)
      * (3456 * K24F.r1 ((n : ℝ) +ᵥ w))) :=
    (TB.mul_ZC5 (le_refl 0) ZC5.ktl24_E6E2S_div_E4_sub_S0
      (TB.const_mul 3456 TB.ktl24_r1)).mono (le_refl 0) (by norm_num)
  refine (TB.add (TB.add (TB.add h1 h2) h3) h4).congr_tile (fun w n z t hn hw hz ht => ?_)
  rw [K24F.Phi_sub_Phiref_expanded ((n : ℝ) +ᵥ w) z (ktl24_E4ne w n z t hn hw hz ht)]
  ring

lemma TB.ktl24_Phi_sub_Phiref_sub :
    TB 0 4 (fun w n z => K24F.Phi ((n : ℝ) +ᵥ w) z - K24F.Phiref ((n : ℝ) +ᵥ w) z
      - qParamFun z * K24F.Q1 ((n : ℝ) +ᵥ w) z) := by
  have h1 : TB 0 4 (fun w n z => ((E4Fun z - 1 - 240 * qParamFun z) - K24F.B2 z)
      * (6 * (K24F.r0 ((n : ℝ) +ᵥ w) + K24F.r2 ((n : ℝ) +ᵥ w)))) :=
    (TB.mul_ZC5 (le_refl 0) ZC5.ktl24_devb1
      (TB.const_mul 6 (TB.add TB.ktl24_r0 TB.ktl24_r2))).mono (le_refl 0) (by norm_num)
  have h2 : TB 0 4 (fun w n z => (12 * K24F.B2 z - 12 * (E4Fun z - 1 - 240 * qParamFun z))
      * K24F.R0 ((n : ℝ) +ᵥ w)) :=
    (TB.mul_ZC5 (le_refl 0) ZC5.ktl24_devb2 TB.ktl24_R0).mono (le_refl 0) (by norm_num)
  have h3 : TB 0 4 (fun w n z => (8640 * (E4Fun z - 1 - 240 * qParamFun z) - 12096 * K24F.B2 z)
      * K24F.r1 ((n : ℝ) +ᵥ w)) :=
    (TB.mul_ZC5 (le_refl 0) ZC5.ktl24_devb3 TB.ktl24_r1).mono (le_refl 0) (by norm_num)
  have h4 : TB 0 4 (fun w n z => (E6Fun z * E2S z / E4Fun z - K24F.S0 z
      + 24 * qParamFun z + 744 * qParamFun z * K24F.S0 z)
      * (3456 * K24F.r1 ((n : ℝ) +ᵥ w))) :=
    (TB.mul_ZC5 (le_refl 0) ZC5.ktl24_X4 (TB.const_mul 3456 TB.ktl24_r1)).mono
      (le_refl 0) (by norm_num)
  refine (TB.add (TB.add (TB.add h1 h2) h3) h4).congr_tile (fun w n z t hn hw hz ht => ?_)
  rw [K24F.Phi_sub_Phiref_sub_expanded ((n : ℝ) +ᵥ w) z (ktl24_E4ne w n z t hn hw hz ht)]
  ring

/-! ## The five remainder groups -/

lemma TB.ktl24_Sm1 :
    TB (2 * Real.pi) 2 (fun w n z => K24F.Sm1 ((n : ℝ) +ᵥ w) z) := by
  have hA : TB (2 * Real.pi) 2 (fun w n z => jInvariantFun ((n : ℝ) +ᵥ w)
      * (K24F.Phi ((n : ℝ) +ᵥ w) z - K24F.Phiref ((n : ℝ) +ᵥ w) z)) :=
    (TB.mul TB.ktl24_j TB.ktl24_Phi_sub_Phiref).mono (by linarith [Real.pi_pos]) (by norm_num)
  have hB : TB (2 * Real.pi) 2 (fun w n z => E4Fun z ^ 3
      * K24F.Q1 ((n : ℝ) +ᵥ w) z * (qParamFun z / DeltaFun z - 1)) := by
    have h0 : TB 0 0 (fun w n z => E4Fun z ^ 3 * K24F.Q1 ((n : ℝ) +ᵥ w) z) :=
      (TB.mul_ZC5 (le_refl 0) ZC5.ktl24_E4cube TB.ktl24_Q1).mono (le_refl 0) (by norm_num)
    have h1 : TB 0 2 (fun w n z => (qParamFun z / DeltaFun z - 1)
        * (E4Fun z ^ 3 * K24F.Q1 ((n : ℝ) +ᵥ w) z)) :=
      (TB.mul_ZC5 (le_refl 0) ZC5.ktl24_q_div_Delta_sub1 h0).mono (le_refl 0) (by norm_num)
    exact (h1.mono (by linarith [Real.pi_pos]) (by norm_num)).congr (fun w n z => by ring)
  have hC : TB (2 * Real.pi) 2 (fun w n z => E4Fun z ^ 3
      * (K24F.Phi ((n : ℝ) +ᵥ w) z - K24F.Phiref ((n : ℝ) +ᵥ w) z
          - qParamFun z * K24F.Q1 ((n : ℝ) +ᵥ w) z) * (DeltaFun z)⁻¹) := by
    have h0 : TB 0 2 (fun w n z => (DeltaFun z)⁻¹
        * (K24F.Phi ((n : ℝ) +ᵥ w) z - K24F.Phiref ((n : ℝ) +ᵥ w) z
            - qParamFun z * K24F.Q1 ((n : ℝ) +ᵥ w) z)) :=
      (TB.mul_ZCg5 (le_refl 0) ZCg5.ktl24_Delta_inv TB.ktl24_Phi_sub_Phiref_sub).mono
        (le_refl 0) (by norm_num)
    have h1 : TB 0 2 (fun w n z => E4Fun z ^ 3
        * ((DeltaFun z)⁻¹ * (K24F.Phi ((n : ℝ) +ᵥ w) z - K24F.Phiref ((n : ℝ) +ᵥ w) z
            - qParamFun z * K24F.Q1 ((n : ℝ) +ᵥ w) z))) :=
      (TB.mul_ZC5 (le_refl 0) ZC5.ktl24_E4cube h0).mono (le_refl 0) (by norm_num)
    exact (h1.mono (by linarith [Real.pi_pos]) (by norm_num)).congr (fun w n z => by ring)
  exact (TB.sub (TB.sub hA hB) hC).congr (fun w n z => by simp only [K24F.Sm1]; ring)

lemma TB.ktl24_Sm2 :
    TB (2 * Real.pi) 2 (fun w n z => K24F.Sm2 ((n : ℝ) +ᵥ w) z) := by
  have hA : TB (2 * Real.pi) 2 (fun w n z => jInvariantFun ((n : ℝ) +ᵥ w)
      * K24F.Phiref ((n : ℝ) +ᵥ w) z * (1 - DeltaFun z / qParamFun z)) := by
    have h0 := TB.mul TB.ktl24_j TB.ktl24_Phiref
    exact ((TB.mul_ZC5 (le_refl 0) ZC5.ktl24_one_sub_Delta_div_q h0).mono
      (by linarith [Real.pi_pos]) (by norm_num)).congr (fun w n z => by ring)
  have hB : TB (2 * Real.pi) 2 (fun w n z => E4Fun z ^ 3 * K24F.Phiref ((n : ℝ) +ᵥ w) z
      * ((DeltaFun z)⁻¹ - (qParamFun z)⁻¹ - 24)) := by
    have h0 : TB 0 0 (fun w n z => E4Fun z ^ 3 * K24F.Phiref ((n : ℝ) +ᵥ w) z) :=
      (TB.mul_ZC5 (le_refl 0) ZC5.ktl24_E4cube TB.ktl24_Phiref).mono (le_refl 0) (by norm_num)
    exact ((TB.mul_ZC5 (le_refl 0) ZC5.ktl24_d1 h0).mono (by linarith [Real.pi_pos])
      (by norm_num)).congr (fun w n z => by ring)
  exact (TB.sub hA hB).congr (fun w n z => by simp only [K24F.Sm2, K24F.d1])

lemma TB.ktl24_Sm3 :
    TB (2 * Real.pi) 2 (fun w n z => K24F.Sm3 ((n : ℝ) +ᵥ w) z) := by
  have h : TB 0 2 (fun w n z => (K24F.S0 z * (E4Fun z ^ 3 - 1)
      - (E6Fun z * E2S z / E4Fun z - K24F.S0 z)) * (3456 * K24F.R0 ((n : ℝ) +ᵥ w))) :=
    (TB.mul_ZC5 (le_refl 0) ZC5.ktl24_Sm3bracket (TB.const_mul 3456 TB.ktl24_R0)).mono
      (le_refl 0) (by norm_num)
  exact (h.mono (by linarith [Real.pi_pos]) (by norm_num)).congr (fun w n z => by
    rw [K24F.Sm3_bracket]; ring)

lemma TB.ktl24_Sm4 :
    TB (2 * Real.pi) 2 (fun w n z => K24F.Sm4 ((n : ℝ) +ᵥ w) z) := by
  have h1 : TB 0 2 (fun w n z => (E2S z ^ 2 - K24F.S0 z ^ 2)
      * (1728 * K24F.r0 ((n : ℝ) +ᵥ w))) :=
    (TB.mul_ZC5 (le_refl 0) ZC5.ktl24_E2Ssq_sub_S0sq
      (TB.const_mul 1728 TB.ktl24_r0)).mono (le_refl 0) (by norm_num)
  have h2 : TB 0 2 (fun w n z => (E4Fun z - 1) * (1728 * K24F.r2 ((n : ℝ) +ᵥ w))) :=
    (TB.mul_ZC5 (le_refl 0) ZC5.ktl24_E4sub1 (TB.const_mul 1728 TB.ktl24_r2)).mono
      (le_refl 0) (by norm_num)
  have h3 : TB 0 2 (fun w n z => (1 - E4Fun z ^ 3)
      * (K24F.S0 z ^ 2 * (1728 * K24F.r0 ((n : ℝ) +ᵥ w))
        + 1728 * K24F.r2 ((n : ℝ) +ᵥ w))) := by
    have h0 : TB 0 0 (fun w n z => K24F.S0 z ^ 2 * (1728 * K24F.r0 ((n : ℝ) +ᵥ w))
        + 1728 * K24F.r2 ((n : ℝ) +ᵥ w)) :=
      TB.add ((TB.mul_ZC5 (le_refl 0) ZC5.ktl24_S0sq
        (TB.const_mul 1728 TB.ktl24_r0)).mono (le_refl 0) (by norm_num))
        (TB.const_mul 1728 TB.ktl24_r2)
    exact (TB.mul_ZC5 (le_refl 0) ZC5.ktl24_one_sub_E4cube h0).mono (le_refl 0) (by norm_num)
  exact ((TB.add (TB.add h1 h2) h3).mono (by linarith [Real.pi_pos]) (by norm_num)).congr
    (fun w n z => by rw [K24F.Sm4_split]; ring)

lemma TB.ktl24_Sm5 :
    TB (2 * Real.pi) 2 (fun w n z => K24F.Sm5 ((n : ℝ) +ᵥ w) z) := by
  have h : TB (2 * Real.pi) 2 (fun w n z => DeltaFun z * (-jInvariantFun ((n : ℝ) +ᵥ w))
      * K24F.Th0 ((n : ℝ) +ᵥ w) z) := by
    have h0 : TB (2 * Real.pi) 2 (fun w n z =>
        DeltaFun z * (-jInvariantFun ((n : ℝ) +ᵥ w))) :=
      (TB.mul_ZC5 (le_refl 0) ZC5.ktl24_Delta (TB.neg TB.ktl24_j)).mono
        (le_refl (2 * Real.pi)) (by norm_num)
    exact (TB.mul h0 TB.ktl24_Th0).mono (by linarith [Real.pi_pos]) (by norm_num)
  exact h.congr (fun w n z => by rw [K24F.Sm5_split]; simp only [K24F.Th0]; ring)

/-! ## The main theorem, `d = 24` -/

lemma TB.ktl24_Sm_sum :
    TB (2 * Real.pi) 2 (fun w n z => K24F.Sm1 ((n : ℝ) +ᵥ w) z + K24F.Sm2 ((n : ℝ) +ᵥ w) z
      + K24F.Sm3 ((n : ℝ) +ᵥ w) z + K24F.Sm4 ((n : ℝ) +ᵥ w) z
      + K24F.Sm5 ((n : ℝ) +ᵥ w) z) :=
  (TB.add (TB.add (TB.add (TB.add TB.ktl24_Sm1 TB.ktl24_Sm2) TB.ktl24_Sm3)
    TB.ktl24_Sm4) TB.ktl24_Sm5).congr (fun w n z => by ring)

theorem KPlus24TileTail :
    TB Real.pi 1
      (fun (w : UpperHalfPlane) (n : ℤ) (z : UpperHalfPlane) =>
        Work.Kernels.KPlus 24 ((n : ℝ) +ᵥ w) z
          - Work.Asymptotics.Compact.Gplus 24 ((n : ℝ) +ᵥ w) z) := by
  have hZ : TB (2 * Real.pi) (2 + 0) (fun w n z => (z : ℂ) ^ 2
      * (K24F.Sm1 ((n : ℝ) +ᵥ w) z + K24F.Sm2 ((n : ℝ) +ᵥ w) z
        + K24F.Sm3 ((n : ℝ) +ᵥ w) z + K24F.Sm4 ((n : ℝ) +ᵥ w) z
        + K24F.Sm5 ((n : ℝ) +ᵥ w) z)) :=
    TB.mul_ZC5 (by norm_num) ZC5.ktl24_zsq TB.ktl24_Sm_sum
  have hmain : TB (2 * Real.pi + 0) ((2 + 0) + 0) (fun w n z => K24F.c * (z : ℂ) ^ 2
      * (K24F.Sm1 ((n : ℝ) +ᵥ w) z + K24F.Sm2 ((n : ℝ) +ᵥ w) z
        + K24F.Sm3 ((n : ℝ) +ᵥ w) z + K24F.Sm4 ((n : ℝ) +ᵥ w) z
        + K24F.Sm5 ((n : ℝ) +ᵥ w) z)
      * (DeltaFun z * (jInvariantFun ((n : ℝ) +ᵥ w) - jInvariantFun z))⁻¹) := by
    have hZ' : TB (2 * Real.pi) (2 + 0) (fun w n z => K24F.c * (z : ℂ) ^ 2
        * (K24F.Sm1 ((n : ℝ) +ᵥ w) z + K24F.Sm2 ((n : ℝ) +ᵥ w) z
          + K24F.Sm3 ((n : ℝ) +ᵥ w) z + K24F.Sm4 ((n : ℝ) +ᵥ w) z
          + K24F.Sm5 ((n : ℝ) +ᵥ w) z)) :=
      (TB.const_mul K24F.c hZ).congr (fun w n z => by ring)
    exact TB.mul hZ' TB.ktl8_invdivisor
  refine (hmain.absorb_gen (by norm_num) (by nlinarith [Real.pi_pos])).congr_tile
    (fun w n z t hn hw hz ht => ?_)
  have hzim : z.im = t := K24F.im_of_coe_eq_axis hz
  have hz3 : (3:ℝ) ≤ z.im := by rw [hzim]; have h := hw.2; linarith
  have hE4 : E4Fun z ≠ 0 := K24F.E4_ne_zero_three z hz3
  have hd := ktl8_tile_divisor_lower w hw z t hz ht n hn
  have hJ : jInvariantFun ((n : ℝ) +ᵥ w) - jInvariantFun z ≠ 0 := by
    intro h0
    rw [h0, mul_zero, norm_zero] at hd
    norm_num at hd
  have hΔz : DeltaFun z ≠ 0 := ClassicalFacts.DeltaFun_ne_zero z
  have hne : DeltaFun z * (jInvariantFun ((n : ℝ) +ᵥ w) - jInvariantFun z) ≠ 0 :=
    mul_ne_zero hΔz hJ
  have hdiff := K24F.KPlus24_diff ((n : ℝ) +ᵥ w) z hJ hE4
  rw [show K24F.c * (z : ℂ) ^ 2
        * (K24F.Sm1 ((n : ℝ) +ᵥ w) z + K24F.Sm2 ((n : ℝ) +ᵥ w) z
          + K24F.Sm3 ((n : ℝ) +ᵥ w) z + K24F.Sm4 ((n : ℝ) +ᵥ w) z
          + K24F.Sm5 ((n : ℝ) +ᵥ w) z)
        * (DeltaFun z * (jInvariantFun ((n : ℝ) +ᵥ w) - jInvariantFun z))⁻¹
      = K24F.c * (z : ℂ) ^ 2
          * (K24F.Sm1 ((n : ℝ) +ᵥ w) z + K24F.Sm2 ((n : ℝ) +ᵥ w) z
            + K24F.Sm3 ((n : ℝ) +ᵥ w) z + K24F.Sm4 ((n : ℝ) +ᵥ w) z
            + K24F.Sm5 ((n : ℝ) +ᵥ w) z)
          / (DeltaFun z * (jInvariantFun ((n : ℝ) +ᵥ w) - jInvariantFun z)) from by ring]
  rw [div_eq_iff hne, ← hdiff]
  ring

end

end Work.Asymptotics.Tile
