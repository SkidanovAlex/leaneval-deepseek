/-
# TripodCert — `Re (deriv ((Tsq c)^[3])) > 1` on the uniqueness disc

Area `Submission/Work/TripodCert/`.  The uniqueness certificate of `UniqueDefs.lean` reduces the
tripod statement TRI to the injectivity of `h = (Tsq c)^[3] - id` on the small disc
`UDisc = closedBall z₀ uRUr` (`R = uRUq = 54608039/2^40 ≈ 4.97·10⁻⁵`) about the rational point
`z₀ = uZ0`; by `injOn_closedBall_of_re_deriv_pos` it is enough that `Re (deriv h) = Re (deriv
((Tsq c)^[3])) - 1 > 0` there, which is this module:

  `1 < Re (deriv ((Tsq c)^[3])) z`   for `c` in the parameter box `Xb` and `z ∈ UDisc`.

*The proof.*  By the chain rule (`deriv_tsq_three`) the derivative of the third iterate is the
product `Π(c,z) = D₂ D₁ D₀` of the three derivatives along the orbit of `z`, where
`Dᵢ = deriv (Tsq c) ((Tsq c)^[i] z)`.  At the centre `(c₀, z₀)` of the certificate the product is
computed exactly (`certP0_re`):

  `Re Π(c₀,z₀) ≥ 3/2 + Uδq`,  `Uδq ≥ 1/2`.

The whole point of the certificate is that the *variation* of the product is dominated by `Uδq`:
for `c ∈ Xb` and `z` in the disc, the first three orbit points `z, Tsq c z, (Tsq c)² z` stay in
the disc `E` of radius `UREq = 1/20` about `z₀` (`orbit_disc`), so that

* `‖deriv (Tsq c) w‖ ≤ ULq` on `E`  (`norm_deriv_Tsq_lipschitz_disc`),
* `‖deriv (Tsq c) u - deriv (Tsq c) v‖ ≤ UKq ‖u - v‖`  (`norm_deriv_Tsq_sub_le_disc`),
* `‖deriv (Tsq c) w - deriv (Tsq c') w‖ ≤ Uβq` for `‖c - c'‖ ≤ UDcq`  (`..._param`).

With the orbit distances `‖z - z₀‖ ≤ uRUq`, `‖Tsq c z - Tsq c₀ z₀‖ ≤ Ur1q + Ur0q` and
`‖(Tsq c)² z - (Tsq c₀)² z₀‖ ≤ ULq·(Ur1q + Ur0q) + dcq`, the telescoping
`D₂D₁D₀ - D₂'D₁'D₀' = (D₂-D₂')D₁D₀ + D₂'(D₁-D₁')D₀ + D₂'D₁'(D₀-D₀')`
bounds the deviation of the product by `3/4` (the numerical inequality is checked by `norm_num`),
and `3/2 + 1/2 - 3/4 = 5/4 > 1`.
-/
import Mathlib
import Submission.Work.TripodCert.UniqueDefs
import Submission.Work.TripodCert.norm_Tsq_sub_le
import Submission.Work.TripodCert.norm_deriv_Tsq_sub_le
import Submission.Work.TripodCert.deriv_tsq_three
import Submission.Work.TripodCert.norm_deriv_Tsq_le_disc
import Submission.Work.TripodCert.norm_Tsq_lipschitz_disc
import Submission.Work.TripodCert.orbit_disc

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.TripodCert

open Filter Set Topology Function
open Work.SeedCertRay
open scoped Topology ComplexConjugate

set_option linter.unusedVariables false

/-! ## The error constants of the estimate -/

/-- A bound for the distance between the first orbit points `Tsq c z` and `Tsq c₀ z₀`. -/
def d1q : ℚ := Ur1q + Ur0q

/-- The variation of `Tsq` caused by moving the parameter alone (`‖c - c₀‖ ≤ UDcq`). -/
def dcq : ℚ := (2 * UMq * UMq + 2 * UCmq + 1) * UDcq

/-! ## Elementary numerical facts -/

theorem UREq_nonneg : (0 : ℝ) ≤ (UREq : ℝ) := by norm_num [UREq]

theorem uRUq_nonneg : (0 : ℝ) ≤ (uRUq : ℝ) := by norm_num [uRUq, URmU, Q, MS]

theorem ULq_nonneg : (0 : ℝ) ≤ (ULq : ℝ) := by
  norm_num [ULq, UMq, US0q, UDcq, UREq, UCmq, Q, MS, RADM]

theorem UKq_nonneg : (0 : ℝ) ≤ (UKq : ℝ) := by norm_num [UKq, UMq, UCmq]

theorem dcq_nonneg : (0 : ℝ) ≤ (dcq : ℝ) := by
  have h : (0 : ℚ) ≤ dcq := by norm_num [dcq, UMq, UCmq, UDcq, Q, MS, RADM]
  exact_mod_cast h

/-- The centre `c₀ = c0T` of the parameter box lies in the box. -/
theorem c0T_mem : Xb.mem c0T := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
  · simp only [Xb, c0T, Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
      Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero, mul_one,
      add_zero, sub_zero]
    norm_num [Q, MS, HWM, PXM, PYM]

/-- A point of the disc `E` of radius `UREq` about `z₀` has norm at most `UMq`. -/
theorem norm_le_UMq {w : ℂ} (hw : ‖w - uZ0‖ ≤ (UREq : ℝ)) : ‖w‖ ≤ (UMq : ℝ) := by
  have h1 : ‖w‖ ≤ ‖uZ0‖ + ‖w - uZ0‖ := by
    calc ‖w‖ = ‖uZ0 + (w - uZ0)‖ := by ring_nf
      _ ≤ ‖uZ0‖ + ‖w - uZ0‖ := norm_add_le _ _
  linarith [h1, hw, hUMe]

/-- `Ur1q + dcq ≤ d1q`. -/
theorem d1q_le : (Ur1q : ℝ) + (dcq : ℝ) ≤ (d1q : ℝ) := by
  have h : (d1q : ℝ) = (Ur1q : ℝ) + (Ur0q : ℝ) := by simp only [d1q]; push_cast; ring
  have h2 : (Ur0q : ℝ) = (Ud0q : ℝ) + (dcq : ℝ) := by simp only [Ur0q, dcq]; push_cast; ring
  have h3 : (0 : ℝ) ≤ (Ud0q : ℝ) := by norm_num [Ud0q]
  rw [h]; linarith

/-- `d1q ≤ UREq`. -/
theorem d1q_le_UREq : (d1q : ℝ) ≤ (UREq : ℝ) := by
  have h : (d1q : ℚ) ≤ UREq := by
    norm_num [d1q, Ur1q, Ur0q, UMq, UCmq, UDcq, UREq, UN0q, UN1q, Ud0q, uRUq, URmU, Q, MS, RADM]
  calc (d1q : ℝ) = ((d1q : ℚ) : ℝ) := rfl
    _ ≤ (UREq : ℝ) := by exact_mod_cast h

/-- `d1q + Ud0q ≤ UREq`. -/
theorem d1q_plus_Ud0q_le_UREq : (d1q : ℝ) + (Ud0q : ℝ) ≤ (UREq : ℝ) := by
  have h : (d1q + Ud0q : ℚ) ≤ UREq := by
    norm_num [d1q, Ur1q, Ur0q, Ud0q, UMq, UCmq, UDcq, UREq, UN0q, UN1q, uRUq, URmU, Q, MS, RADM]
  have h2 : ((d1q + Ud0q : ℚ) : ℝ) ≤ (UREq : ℝ) := by exact_mod_cast h
  calc (d1q : ℝ) + (Ud0q : ℝ) = ((d1q + Ud0q : ℚ) : ℝ) := by push_cast; ring
    _ ≤ (UREq : ℝ) := h2

/-! ## The Lipschitz estimates for `Tsq` and its derivative -/

/-- The derivative of `Tsq c` is `UKq`-Lipschitz on the ambient disc `‖w‖ ≤ UMq`. -/
theorem norm_deriv_Tsq_sub_le_disc {c : ℂ} (hc : Xb.mem c) {u v : ℂ}
    (hu : ‖u‖ ≤ (UMq : ℝ)) (hv : ‖v‖ ≤ (UMq : ℝ)) :
    ‖deriv (Work.Landing.Tsq c) u - deriv (Work.Landing.Tsq c) v‖ ≤ (UKq : ℝ) * ‖u - v‖ := by
  have hc' := hUCm hc
  have h1 : ‖u‖ ^ 2 + ‖u‖ * ‖v‖ + ‖v‖ ^ 2 + ‖c‖ ≤ 3 * (UMq : ℝ) ^ 2 + (UCmq : ℝ) := by
    nlinarith [norm_nonneg u, norm_nonneg v, hu, hv, hc']
  have h4 : (0 : ℝ) ≤ 4 * ‖u - v‖ := by positivity
  have h5 := mul_le_mul_of_nonneg_left h1 h4
  have hUK : (UKq : ℝ) = 4 * (3 * (UMq : ℝ) ^ 2 + (UCmq : ℝ)) := by norm_num [UKq, UMq, UCmq]
  calc ‖deriv (Work.Landing.Tsq c) u - deriv (Work.Landing.Tsq c) v‖
      ≤ 4 * ‖u - v‖ * (‖u‖ ^ 2 + ‖u‖ * ‖v‖ + ‖v‖ ^ 2 + ‖c‖) :=
        Work.TripodCert.norm_deriv_Tsq_sub_le c u v
    _ ≤ 4 * ‖u - v‖ * (3 * (UMq : ℝ) ^ 2 + (UCmq : ℝ)) := h5
    _ = (UKq : ℝ) * ‖u - v‖ := by rw [hUK]; ring

/-- The derivative of `Tsq` varies by at most `Uβq` when the parameter moves by `UDcq`. -/
theorem norm_deriv_Tsq_sub_param {c c' : ℂ} (h : ‖c - c'‖ ≤ (UDcq : ℝ)) {w : ℂ}
    (hw : ‖w‖ ≤ (UMq : ℝ)) :
    ‖deriv (Work.Landing.Tsq c) w - deriv (Work.Landing.Tsq c') w‖ ≤ (Uβq : ℝ) := by
  have hkey : deriv (Work.Landing.Tsq c) w - deriv (Work.Landing.Tsq c') w
      = 4 * w * (star c - star c') := by
    rw [Work.SeedDyn.deriv_Tsq_eq, Work.SeedDyn.deriv_Tsq_eq]; ring
  rw [hkey, show star c - star c' = star (c - c') by rw [star_sub]]
  rw [norm_mul, norm_mul, norm_star]
  have h4 : ‖(4 : ℂ)‖ = 4 := by norm_num
  rw [h4]
  have hUβ : (Uβq : ℝ) = 4 * (UMq : ℝ) * (UDcq : ℝ) := by
    norm_num [Uβq, UMq, UDcq, Q, MS, RADM]
  calc 4 * ‖w‖ * ‖c - c'‖ ≤ 4 * (UMq : ℝ) * (UDcq : ℝ) := by
        nlinarith [hw, h, norm_nonneg w, norm_nonneg (c - c')]
    _ = (Uβq : ℝ) := hUβ.symm

/-- The parameter variation of `Tsq` at fixed `z`. -/
theorem norm_Tsq_param_diff {c c' : ℂ} (hc : Xb.mem c) (hc' : Xb.mem c') {w : ℂ}
    (hw : ‖w‖ ≤ (UMq : ℝ)) :
    ‖Work.Landing.Tsq c w - Work.Landing.Tsq c' w‖
      ≤ ‖c - c'‖ * (2 * (UMq : ℝ) * (UMq : ℝ) + 2 * (UCmq : ℝ) + 1) := by
  have h1 := hUCm hc
  have h2 := hUCm hc'
  have hid : Work.Landing.Tsq c w - Work.Landing.Tsq c' w
      = (star c - star c') * (2 * w ^ 2 + star c + star c') + (c - c') := by
    unfold Work.Landing.Tsq; ring
  rw [hid]
  have hnorm : ‖star c - star c'‖ = ‖c - c'‖ := by rw [← star_sub, norm_star]
  have h2w : ‖(2 : ℂ) * w ^ 2‖ = 2 * ‖w‖ ^ 2 := by rw [norm_mul, norm_pow]; norm_num
  have hq : ‖2 * w ^ 2 + star c + star c'‖ ≤ 2 * (UMq : ℝ) ^ 2 + 2 * (UCmq : ℝ) := by
    calc ‖2 * (w ^ 2) + star c + star c'‖ ≤ ‖2 * (w ^ 2) + star c‖ + ‖star c'‖ :=
          norm_add_le _ _
      _ ≤ (‖2 * (w ^ 2)‖ + ‖star c‖) + ‖star c'‖ := by
          have := norm_add_le (2 * (w ^ 2)) (star c); linarith
      _ ≤ 2 * (UMq : ℝ) ^ 2 + 2 * (UCmq : ℝ) := by
          rw [h2w, norm_star, norm_star]
          nlinarith [norm_nonneg w, hw, h1, h2]
  calc ‖(star c - star c') * (2 * w ^ 2 + star c + star c') + (c - c')‖
      ≤ ‖(star c - star c') * (2 * w ^ 2 + star c + star c')‖ + ‖c - c'‖ := norm_add_le _ _
    _ = ‖c - c'‖ * ‖2 * w ^ 2 + star c + star c'‖ + ‖c - c'‖ := by rw [norm_mul, hnorm]
    _ ≤ ‖c - c'‖ * (2 * (UMq : ℝ) ^ 2 + 2 * (UCmq : ℝ)) + ‖c - c'‖ := by
        have h3 : (0 : ℝ) ≤ ‖c - c'‖ := norm_nonneg _
        nlinarith [hq, h3]
    _ = ‖c - c'‖ * (2 * (UMq : ℝ) * (UMq : ℝ) + 2 * (UCmq : ℝ) + 1) := by ring

/-- The `dcq` form of the parameter variation of `Tsq`. -/
theorem norm_Tsq_param_diff_le_dcq {c c' : ℂ} (hc : Xb.mem c) (hc' : Xb.mem c') {w : ℂ}
    (hw : ‖w‖ ≤ (UMq : ℝ)) (hcc : ‖c - c'‖ ≤ (UDcq : ℝ)) :
    ‖Work.Landing.Tsq c w - Work.Landing.Tsq c' w‖ ≤ (dcq : ℝ) := by
  refine (norm_Tsq_param_diff hc hc' hw).trans ?_
  have h1 : (2 * (UMq : ℝ) * (UMq : ℝ) + 2 * (UCmq : ℝ) + 1)
      = ((2 * UMq * UMq + 2 * UCmq + 1 : ℚ) : ℝ) := by push_cast; ring
  rw [h1]
  have h2 : (0 : ℝ) ≤ ((2 * UMq * UMq + 2 * UCmq + 1 : ℚ) : ℝ) := by
    have h : (0 : ℚ) ≤ 2 * UMq * UMq + 2 * UCmq + 1 := by norm_num [UMq, UCmq]
    exact_mod_cast h
  calc ‖c - c'‖ * ((2 * UMq * UMq + 2 * UCmq + 1 : ℚ) : ℝ)
      ≤ (UDcq : ℝ) * ((2 * UMq * UMq + 2 * UCmq + 1 : ℚ) : ℝ) :=
        mul_le_mul_of_nonneg_right hcc h2
    _ = (dcq : ℝ) := by simp only [dcq]; push_cast; ring

/-! ## The orbit distances -/

/-- The first orbit point: `‖Tsq c z - Tsq c₀ z₀‖ ≤ d1q`. -/
theorem norm_Tsq_orbit_one {c : ℂ} (hc : Xb.mem c) {z : ℂ} (hz : ‖z - uZ0‖ ≤ uRUr) :
    ‖Work.Landing.Tsq c z - Work.Landing.Tsq c0T uZ0‖ ≤ (d1q : ℝ) := by
  have hzc := hUCm hc
  have hzE : ‖z - uZ0‖ ≤ (UREq : ℝ) := le_trans hz uRUr_le_UREq
  have hzM : ‖z‖ ≤ (UMq : ℝ) := norm_le_UMq hzE
  have hU0 : ‖uZ0‖ ≤ (UMq : ℝ) := hUMz0
  have hcd : ‖c - c0T‖ ≤ (UDcq : ℝ) := hDc hc
  have step1 : ‖Work.Landing.Tsq c z - Work.Landing.Tsq c uZ0‖
      ≤ (uRUq : ℝ) * (2 * (UMq : ℝ)) * (2 * (UMq : ℝ) ^ 2 + 2 * (UCmq : ℝ)) := by
    refine (Work.TripodCert.norm_Tsq_sub_le c z uZ0).trans ?_
    have e1 : ‖z - uZ0‖ ≤ (uRUq : ℝ) := hz
    have e2 : ‖z‖ + ‖uZ0‖ ≤ 2 * (UMq : ℝ) := by linarith
    have e3 : ‖z‖ ^ 2 + ‖uZ0‖ ^ 2 + 2 * ‖c‖ ≤ 2 * (UMq : ℝ) ^ 2 + 2 * (UCmq : ℝ) := by
      nlinarith [norm_nonneg z, norm_nonneg uZ0, hzM, hU0, hzc]
    have hqz : (0 : ℝ) ≤ ‖z‖ + ‖uZ0‖ := by positivity
    have huR : (0 : ℝ) ≤ (uRUq : ℝ) := uRUq_nonneg
    have hU2 : (0 : ℝ) ≤ 2 * (UMq : ℝ) := by norm_num [UMq]
    have h1 : ‖z - uZ0‖ * (‖z‖ + ‖uZ0‖) ≤ (uRUq : ℝ) * (2 * (UMq : ℝ)) :=
      mul_le_mul e1 e2 hqz huR
    have h1' : (0 : ℝ) ≤ (uRUq : ℝ) * (2 * (UMq : ℝ)) := mul_nonneg huR hU2
    exact mul_le_mul h1 e3 (by positivity) h1'
  have step2 : ‖Work.Landing.Tsq c uZ0 - Work.Landing.Tsq c0T uZ0‖ ≤ (dcq : ℝ) :=
    norm_Tsq_param_diff_le_dcq hc c0T_mem hU0 hcd
  have hstep1eq : (uRUq : ℝ) * (2 * (UMq : ℝ)) * (2 * (UMq : ℝ) ^ 2 + 2 * (UCmq : ℝ))
      = (Ur1q : ℝ) := by
    simp only [Ur1q, UN0q, UN1q, uRUq, UMq, UCmq, Q, MS, URmU]; push_cast; ring
  calc ‖Work.Landing.Tsq c z - Work.Landing.Tsq c0T uZ0‖
      ≤ ‖Work.Landing.Tsq c z - Work.Landing.Tsq c uZ0‖
          + ‖Work.Landing.Tsq c uZ0 - Work.Landing.Tsq c0T uZ0‖ := by
        rw [show Work.Landing.Tsq c z - Work.Landing.Tsq c0T uZ0
            = (Work.Landing.Tsq c z - Work.Landing.Tsq c uZ0)
              + (Work.Landing.Tsq c uZ0 - Work.Landing.Tsq c0T uZ0) by ring]
        exact norm_add_le _ _
    _ ≤ (Ur1q : ℝ) + (dcq : ℝ) := by
        rw [hstep1eq] at step1
        exact add_le_add step1 step2
    _ ≤ (d1q : ℝ) := d1q_le

/-- The second orbit point: `‖(Tsq c)² z - (Tsq c₀)² z₀‖ ≤ ULq·d1q + dcq`. -/
theorem norm_Tsq_orbit_two {c : ℂ} (hc : Xb.mem c) {z : ℂ} (hz : ‖z - uZ0‖ ≤ uRUr) :
    ‖Work.Landing.Tsq c (Work.Landing.Tsq c z)
        - Work.Landing.Tsq c0T (Work.Landing.Tsq c0T uZ0)‖
      ≤ ((ULq * d1q + dcq : ℚ) : ℝ) := by
  have hd1 := norm_Tsq_orbit_one hc hz
  have hf1d : ‖Work.Landing.Tsq c z - uZ0‖ ≤ (UREq : ℝ) := by
    have h := hUd0
    calc ‖Work.Landing.Tsq c z - uZ0‖
        ≤ ‖Work.Landing.Tsq c z - Work.Landing.Tsq c0T uZ0‖
            + ‖Work.Landing.Tsq c0T uZ0 - uZ0‖ := by
          rw [show Work.Landing.Tsq c z - uZ0
              = (Work.Landing.Tsq c z - Work.Landing.Tsq c0T uZ0)
                + (Work.Landing.Tsq c0T uZ0 - uZ0) by ring]
          exact norm_add_le _ _
      _ ≤ (d1q : ℝ) + (Ud0q : ℝ) := add_le_add hd1 hUd0
      _ ≤ (UREq : ℝ) := d1q_plus_Ud0q_le_UREq
  have hg1d : ‖Work.Landing.Tsq c0T uZ0 - uZ0‖ ≤ (UREq : ℝ) := le_trans hUd0 Ud0q_le_UREq
  have hg1M : ‖Work.Landing.Tsq c0T uZ0‖ ≤ (UMq : ℝ) := norm_le_UMq hg1d
  have step1 : ‖Work.Landing.Tsq c (Work.Landing.Tsq c z)
        - Work.Landing.Tsq c (Work.Landing.Tsq c0T uZ0)‖ ≤ (ULq : ℝ) * (d1q : ℝ) :=
    (norm_Tsq_lipschitz_disc hc hf1d hg1d).trans (mul_le_mul_of_nonneg_left hd1 ULq_nonneg)
  have step2 : ‖Work.Landing.Tsq c (Work.Landing.Tsq c0T uZ0)
        - Work.Landing.Tsq c0T (Work.Landing.Tsq c0T uZ0)‖ ≤ (dcq : ℝ) :=
    norm_Tsq_param_diff_le_dcq hc c0T_mem hg1M (hDc hc)
  have hcast : ((ULq * d1q + dcq : ℚ) : ℝ) = (ULq : ℝ) * (d1q : ℝ) + (dcq : ℝ) := by
    push_cast; ring
  calc ‖Work.Landing.Tsq c (Work.Landing.Tsq c z)
        - Work.Landing.Tsq c0T (Work.Landing.Tsq c0T uZ0)‖
      ≤ ‖Work.Landing.Tsq c (Work.Landing.Tsq c z)
            - Work.Landing.Tsq c (Work.Landing.Tsq c0T uZ0)‖
          + ‖Work.Landing.Tsq c (Work.Landing.Tsq c0T uZ0)
            - Work.Landing.Tsq c0T (Work.Landing.Tsq c0T uZ0)‖ := by
        rw [show Work.Landing.Tsq c (Work.Landing.Tsq c z)
              - Work.Landing.Tsq c0T (Work.Landing.Tsq c0T uZ0)
            = (Work.Landing.Tsq c (Work.Landing.Tsq c z)
                - Work.Landing.Tsq c (Work.Landing.Tsq c0T uZ0))
              + (Work.Landing.Tsq c (Work.Landing.Tsq c0T uZ0)
                - Work.Landing.Tsq c0T (Work.Landing.Tsq c0T uZ0)) by ring]
        exact norm_add_le _ _
    _ ≤ (ULq : ℝ) * (d1q : ℝ) + (dcq : ℝ) := add_le_add step1 step2
    _ = ((ULq * d1q + dcq : ℚ) : ℝ) := hcast.symm

/-! ## Perturbation of a product of three numbers -/

/-- If two triples of complex numbers are close, then so are their products. -/
theorem norm_prod_sub_le {A0 A1 A2 B0 B1 B2 : ℂ} {L X0 X1 X2 : ℝ}
    (hA0 : ‖A0‖ ≤ L) (hA1 : ‖A1‖ ≤ L) (hA2 : ‖A2‖ ≤ L)
    (hB0 : ‖B0‖ ≤ L) (hB1 : ‖B1‖ ≤ L) (hB2 : ‖B2‖ ≤ L)
    (hd0 : ‖A0 - B0‖ ≤ X0) (hd1 : ‖A1 - B1‖ ≤ X1) (hd2 : ‖A2 - B2‖ ≤ X2) :
    ‖A2 * A1 * A0 - B2 * B1 * B0‖ ≤ X2 * L * L + L * X1 * L + L * L * X0 := by
  have hL0 : (0 : ℝ) ≤ L := (norm_nonneg A0).trans hA0
  have hX0 : (0 : ℝ) ≤ X0 := (norm_nonneg (A0 - B0)).trans hd0
  have hX1 : (0 : ℝ) ≤ X1 := (norm_nonneg (A1 - B1)).trans hd1
  have hX2 : (0 : ℝ) ≤ X2 := (norm_nonneg (A2 - B2)).trans hd2
  have hdecomp : A2 * A1 * A0 - B2 * B1 * B0
      = (A2 - B2) * A1 * A0 + B2 * (A1 - B1) * A0 + B2 * B1 * (A0 - B0) := by ring
  rw [hdecomp]
  have hmain : ‖(A2 - B2) * A1 * A0 + B2 * (A1 - B1) * A0 + B2 * B1 * (A0 - B0)‖
      ≤ ‖A2 - B2‖ * ‖A1‖ * ‖A0‖ + ‖B2‖ * ‖A1 - B1‖ * ‖A0‖ + ‖B2‖ * ‖B1‖ * ‖A0 - B0‖ := by
    have h2 := norm_add_le ((A2 - B2) * A1 * A0 + B2 * (A1 - B1) * A0) (B2 * B1 * (A0 - B0))
    have h3 := norm_add_le ((A2 - B2) * A1 * A0) (B2 * (A1 - B1) * A0)
    simp only [norm_mul] at h2 h3 ⊢
    linarith
  refine hmain.trans ?_
  gcongr

/-! ## The main theorem -/

/-- **The real part of the derivative of `(Tsq c)^[3]` exceeds `1` on the uniqueness disc.**
This is the estimate that makes `(Tsq c)^[3] - id` injective on `closedBall z₀ uRUr`
(`injOn_closedBall_of_re_deriv_pos`), whence the uniqueness of the fixed point of `(Tsq c)^[3]`
there. -/
theorem deriv_tsq_three_re_pos {c : ℂ} (hc : Work.SeedCertRay.Xb.mem c) {z : ℂ}
    (hz : z ∈ Metric.closedBall Work.TripodCert.uZ0 Work.TripodCert.uRUr) :
    1 < (deriv ((Work.Landing.Tsq c)^[3]) z).re := by
  have hzd : ‖z - uZ0‖ ≤ uRUr := by
    simpa [Metric.mem_closedBall, dist_eq_norm] using hz
  obtain ⟨hz0d, hf1d, hf2d, hg1d, hg2d⟩ := orbit_disc hc hzd
  have hd10 := norm_Tsq_orbit_one hc hzd
  have hd20 := norm_Tsq_orbit_two hc hzd
  -- the six derivative factors along the two orbits
  set A0 : ℂ := deriv (Work.Landing.Tsq c) z with hA0
  set A1 : ℂ := deriv (Work.Landing.Tsq c) (Work.Landing.Tsq c z) with hA1
  set A2 : ℂ := deriv (Work.Landing.Tsq c) (Work.Landing.Tsq c (Work.Landing.Tsq c z)) with hA2
  set B0 : ℂ := deriv (Work.Landing.Tsq c0T) uZ0 with hB0
  set B1 : ℂ := deriv (Work.Landing.Tsq c0T) (Work.Landing.Tsq c0T uZ0) with hB1
  set B2 : ℂ := deriv (Work.Landing.Tsq c0T) (Work.Landing.Tsq c0T (Work.Landing.Tsq c0T uZ0))
    with hB2
  -- norms of the orbit points
  have hzM : ‖z‖ ≤ (UMq : ℝ) := norm_le_UMq hz0d
  have hf1M : ‖Work.Landing.Tsq c z‖ ≤ (UMq : ℝ) := norm_le_UMq hf1d
  have hf2M : ‖Work.Landing.Tsq c (Work.Landing.Tsq c z)‖ ≤ (UMq : ℝ) := norm_le_UMq hf2d
  have hg1M : ‖Work.Landing.Tsq c0T uZ0‖ ≤ (UMq : ℝ) := norm_le_UMq hg1d
  have hg2M : ‖Work.Landing.Tsq c0T (Work.Landing.Tsq c0T uZ0)‖ ≤ (UMq : ℝ) :=
    norm_le_UMq hg2d
  have h00 : ‖uZ0 - uZ0‖ ≤ (UREq : ℝ) := by rw [sub_self, norm_zero]; exact UREq_nonneg
  have hcd : ‖c - c0T‖ ≤ (UDcq : ℝ) := hDc hc
  -- the derivative bounds
  have hLA0 : ‖A0‖ ≤ (ULq : ℝ) := by rw [hA0]; exact norm_deriv_Tsq_le_disc hc hz0d
  have hLA1 : ‖A1‖ ≤ (ULq : ℝ) := by rw [hA1]; exact norm_deriv_Tsq_le_disc hc hf1d
  have hLA2 : ‖A2‖ ≤ (ULq : ℝ) := by rw [hA2]; exact norm_deriv_Tsq_le_disc hc hf2d
  have hLB0 : ‖B0‖ ≤ (ULq : ℝ) := by rw [hB0]; exact norm_deriv_Tsq_le_disc c0T_mem h00
  have hLB1 : ‖B1‖ ≤ (ULq : ℝ) := by rw [hB1]; exact norm_deriv_Tsq_le_disc c0T_mem hg1d
  have hLB2 : ‖B2‖ ≤ (ULq : ℝ) := by rw [hB2]; exact norm_deriv_Tsq_le_disc c0T_mem hg2d
  -- the three derivative differences
  have hD0 : ‖A0 - B0‖ ≤ (UKq : ℝ) * (uRUq : ℝ) + (Uβq : ℝ) := by
    rw [hA0, hB0]
    have h1 := norm_deriv_Tsq_sub_le_disc hc hzM hUMz0
    have h2 := norm_deriv_Tsq_sub_param hcd hUMz0
    have h3 : (UKq : ℝ) * ‖z - uZ0‖ ≤ (UKq : ℝ) * (uRUq : ℝ) :=
      mul_le_mul_of_nonneg_left hzd UKq_nonneg
    calc ‖deriv (Work.Landing.Tsq c) z - deriv (Work.Landing.Tsq c0T) uZ0‖
        ≤ ‖deriv (Work.Landing.Tsq c) z - deriv (Work.Landing.Tsq c) uZ0‖
            + ‖deriv (Work.Landing.Tsq c) uZ0 - deriv (Work.Landing.Tsq c0T) uZ0‖ := by
          rw [show deriv (Work.Landing.Tsq c) z - deriv (Work.Landing.Tsq c0T) uZ0
              = (deriv (Work.Landing.Tsq c) z - deriv (Work.Landing.Tsq c) uZ0)
                + (deriv (Work.Landing.Tsq c) uZ0 - deriv (Work.Landing.Tsq c0T) uZ0)
              by ring]
          exact norm_add_le _ _
      _ ≤ (UKq : ℝ) * (uRUq : ℝ) + (Uβq : ℝ) := by linarith
  have hD1 : ‖A1 - B1‖ ≤ (UKq : ℝ) * (d1q : ℝ) + (Uβq : ℝ) := by
    rw [hA1, hB1]
    have h1 := norm_deriv_Tsq_sub_le_disc hc hf1M hg1M
    have h2 := norm_deriv_Tsq_sub_param hcd hg1M
    have h3 : (UKq : ℝ) * ‖Work.Landing.Tsq c z - Work.Landing.Tsq c0T uZ0‖
        ≤ (UKq : ℝ) * (d1q : ℝ) := mul_le_mul_of_nonneg_left hd10 UKq_nonneg
    calc ‖deriv (Work.Landing.Tsq c) (Work.Landing.Tsq c z)
          - deriv (Work.Landing.Tsq c0T) (Work.Landing.Tsq c0T uZ0)‖
        ≤ ‖deriv (Work.Landing.Tsq c) (Work.Landing.Tsq c z)
            - deriv (Work.Landing.Tsq c) (Work.Landing.Tsq c0T uZ0)‖
          + ‖deriv (Work.Landing.Tsq c) (Work.Landing.Tsq c0T uZ0)
            - deriv (Work.Landing.Tsq c0T) (Work.Landing.Tsq c0T uZ0)‖ := by
          rw [show deriv (Work.Landing.Tsq c) (Work.Landing.Tsq c z)
                - deriv (Work.Landing.Tsq c0T) (Work.Landing.Tsq c0T uZ0)
              = (deriv (Work.Landing.Tsq c) (Work.Landing.Tsq c z)
                  - deriv (Work.Landing.Tsq c) (Work.Landing.Tsq c0T uZ0))
                + (deriv (Work.Landing.Tsq c) (Work.Landing.Tsq c0T uZ0)
                  - deriv (Work.Landing.Tsq c0T) (Work.Landing.Tsq c0T uZ0)) by ring]
          exact norm_add_le _ _
      _ ≤ (UKq : ℝ) * (d1q : ℝ) + (Uβq : ℝ) := by linarith
  have hD2 : ‖A2 - B2‖ ≤ (UKq : ℝ) * ((ULq : ℝ) * (d1q : ℝ) + (dcq : ℝ)) + (Uβq : ℝ) := by
    rw [hA2, hB2]
    have hcast : ((ULq * d1q + dcq : ℚ) : ℝ) = (ULq : ℝ) * (d1q : ℝ) + (dcq : ℝ) := by
      push_cast; ring
    have h1 := norm_deriv_Tsq_sub_le_disc hc hf2M hg2M
    have h2 := norm_deriv_Tsq_sub_param hcd hg2M
    have h3 : (UKq : ℝ) * ‖Work.Landing.Tsq c (Work.Landing.Tsq c z)
          - Work.Landing.Tsq c0T (Work.Landing.Tsq c0T uZ0)‖
        ≤ (UKq : ℝ) * ((ULq : ℝ) * (d1q : ℝ) + (dcq : ℝ)) := by
      rw [← hcast]
      exact mul_le_mul_of_nonneg_left hd20 UKq_nonneg
    calc ‖deriv (Work.Landing.Tsq c) (Work.Landing.Tsq c (Work.Landing.Tsq c z))
          - deriv (Work.Landing.Tsq c0T) (Work.Landing.Tsq c0T (Work.Landing.Tsq c0T uZ0))‖
        ≤ ‖deriv (Work.Landing.Tsq c) (Work.Landing.Tsq c (Work.Landing.Tsq c z))
            - deriv (Work.Landing.Tsq c) (Work.Landing.Tsq c0T (Work.Landing.Tsq c0T uZ0))‖
          + ‖deriv (Work.Landing.Tsq c) (Work.Landing.Tsq c0T (Work.Landing.Tsq c0T uZ0))
            - deriv (Work.Landing.Tsq c0T)
                (Work.Landing.Tsq c0T (Work.Landing.Tsq c0T uZ0))‖ := by
          rw [show deriv (Work.Landing.Tsq c) (Work.Landing.Tsq c (Work.Landing.Tsq c z))
                - deriv (Work.Landing.Tsq c0T)
                    (Work.Landing.Tsq c0T (Work.Landing.Tsq c0T uZ0))
              = (deriv (Work.Landing.Tsq c) (Work.Landing.Tsq c (Work.Landing.Tsq c z))
                  - deriv (Work.Landing.Tsq c) (Work.Landing.Tsq c0T (Work.Landing.Tsq c0T uZ0)))
                + (deriv (Work.Landing.Tsq c) (Work.Landing.Tsq c0T (Work.Landing.Tsq c0T uZ0))
                  - deriv (Work.Landing.Tsq c0T)
                      (Work.Landing.Tsq c0T (Work.Landing.Tsq c0T uZ0))) by ring]
          exact norm_add_le _ _
      _ ≤ (UKq : ℝ) * ((ULq : ℝ) * (d1q : ℝ) + (dcq : ℝ)) + (Uβq : ℝ) := by linarith
  -- the perturbation of the product
  have hprod := norm_prod_sub_le hLA0 hLA1 hLA2 hLB0 hLB1 hLB2 hD0 hD1 hD2
  have hnum : ((UKq : ℝ) * ((ULq : ℝ) * (d1q : ℝ) + (dcq : ℝ)) + (Uβq : ℝ)) * (ULq : ℝ) * (ULq : ℝ)
      + (ULq : ℝ) * ((UKq : ℝ) * (d1q : ℝ) + (Uβq : ℝ)) * (ULq : ℝ)
      + (ULq : ℝ) * (ULq : ℝ) * ((UKq : ℝ) * (uRUq : ℝ) + (Uβq : ℝ)) ≤ (3 / 4 : ℝ) := by
    norm_num [d1q, dcq, UKq, ULq, Uβq, Ur1q, Ur0q, UMq, US0q, UCmq, UDcq, UREq, UN0q, UN1q,
      Ud0q, uRUq, URmU, Q, MS, RADM]
  have hdiff : ‖A2 * A1 * A0 - B2 * B1 * B0‖ ≤ (3 / 4 : ℝ) := hprod.trans hnum
  have hre : |(A2 * A1 * A0).re - (B2 * B1 * B0).re| ≤ (3 / 4 : ℝ) := by
    have h := Complex.abs_re_le_norm (A2 * A1 * A0 - B2 * B1 * B0)
    rw [Complex.sub_re] at h
    exact h.trans hdiff
  -- the value at the centre
  have hP0e : deriv ((Work.Landing.Tsq c0T)^[3]) uZ0 = B2 * B1 * B0 := by
    rw [hB0, hB1, hB2, deriv_tsq_three]
    simp only [show (2 : ℕ) = 1 + 1 from rfl, Function.iterate_succ_apply',
      Function.iterate_zero_apply]
  have hP0 : 3 / 2 + (Uδq : ℝ) ≤ (B2 * B1 * B0).re := by
    have h := certP0_re
    rwa [hP0e] at h
  have hδ : (1 / 2 : ℝ) ≤ (Uδq : ℝ) := by
    norm_num [Uδq, UKq, ULq, Uβq, Ur1q, Ur0q, UMq, US0q, UCmq, UDcq, UREq, UN0q, UN1q, Ud0q,
      uRUq, URmU, Q, MS, RADM]
  -- conclude
  have hPce : deriv ((Work.Landing.Tsq c)^[3]) z = A2 * A1 * A0 := by
    rw [hA0, hA1, hA2, deriv_tsq_three]
    simp only [show (2 : ℕ) = 1 + 1 from rfl, Function.iterate_succ_apply',
      Function.iterate_zero_apply]
  rw [hPce]
  have hlow : (B2 * B1 * B0).re - (3 / 4 : ℝ) ≤ (A2 * A1 * A0).re := by
    rw [abs_le] at hre
    linarith [hre.1]
  linarith

end Work.TripodCert
