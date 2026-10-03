import Mathlib
import Submission.Work.Pert.Phi_dev_geom
import Submission.Work.Pert.Gates
import Submission.Work.Pert.Setup

/-!
# PERT · `Work.Pert.pert2v2.steps`: the two one-step lemmas of the walk in the lower gate

For a near-translation `F` on the lower gate `Qm Ξ α = Qreg (some (Ξ - 1/α)) (some (-Ξ))` we show

* `fwdStep` : if `z` lies in the gate with room `1 + 1/8` on the *right* (`margB_g Ξ z`), then
  `F z` is again in the gate and `Φ (F z) = Φ z + 1`;
* `backStep_exists` : if `z` lies in the gate with room `1 + 1/4` on the *left*
  (`margA_g Ξ α z`), then `F` has a preimage `w` of `z` with `‖w - (z - 1)‖ ≤ 1/32`; moreover
  `w` is again in the gate and `Φ w = Φ z - 1`.

The backward step is a contraction-mapping argument: the map `T w = z - (F w - w)` maps the closed
ball of radius `1/32` around `z - 1` into itself (`‖F w - (w + 1)‖ ≤ 1/32` on the gate) and is
`1/32`-Lipschitz there (`‖deriv F w - 1‖ ≤ 1/32` on the gate, plus the mean value inequality on
the convex ball).  Its fixed point `w` satisfies `F w = z`.

These two steps are the ingredients of the long walks of `Work.Pert.pert2v2.fatou_proper_im`.
-/

namespace Work.Pert.pert2v2

open MandelDim Complex Metric Set
open scoped NNReal

noncomputable section

variable {Ξ : ℝ} {α : ℂ}

/-- Continuity of the lower margin. -/
theorem continuous_margA_g : Continuous (Work.Pert.margA_g Ξ α) := by
  unfold Work.Pert.margA_g
  fun_prop

/-- Continuity of the upper margin. -/
theorem continuous_margB_g : Continuous (Work.Pert.margB_g Ξ) := by
  unfold Work.Pert.margB_g
  fun_prop

/-- The lower gate is open. -/
theorem isOpen_Qm : IsOpen (Work.Pert.Qm Ξ α) := by
  have h : Work.Pert.Qm Ξ α
      = {z | 0 < Work.Pert.margA_g Ξ α z} ∩ {z | 0 < Work.Pert.margB_g Ξ z} := by
    ext z
    rw [Work.Pert.mem_Qm_iff_g]
    simp
  rw [h]
  exact (isOpen_lt continuous_const continuous_margA_g).inter
    (isOpen_lt continuous_const continuous_margB_g)

/-- The left margin of `z - 1` is that of `z`, minus one. -/
theorem margA_g_sub_one (z : ℂ) :
    Work.Pert.margA_g Ξ α (z - 1) = Work.Pert.margA_g Ξ α z - 1 := by
  simp only [Work.Pert.margA_g, Complex.sub_re, Complex.sub_im, Complex.one_re, Complex.one_im,
    sub_zero]
  ring

/-- The right margin of `z - 1` is that of `z`, plus one. -/
theorem margB_g_sub_one (z : ℂ) :
    Work.Pert.margB_g Ξ (z - 1) = Work.Pert.margB_g Ξ z + 1 := by
  simp only [Work.Pert.margB_g, Complex.sub_re, Complex.sub_im, Complex.one_re, Complex.one_im,
    sub_zero]
  ring

/-- **Forward step.**  If `z` is in the gate with room `1 + 1/8` on the right, then `F z` is in
the gate and `Φ (F z) = Φ z + 1`. -/
theorem fwdStep {F Φ : ℂ → ℂ} {z : ℂ}
    (hNT : ∀ w ∈ Work.Pert.Qm Ξ α, ‖F w - (w + 1)‖ ≤ 1 / 32)
    (hz : z ∈ Work.Pert.Qm Ξ α)
    (hroom : 1 + 1 / 8 ≤ Work.Pert.margB_g Ξ z)
    (hΦ : ∀ w ∈ Work.Pert.Qm Ξ α, F w ∈ Work.Pert.Qm Ξ α → Φ (F w) = Φ w + 1) :
    F z ∈ Work.Pert.Qm Ξ α ∧ Φ (F z) = Φ z + 1 := by
  have hroom' : 1 + 1 / 8 ≤ |z.im| - Ξ - z.re := by
    simpa only [Work.Pert.margB_g] using hroom
  have hz' : 0 < z.re - Ξ + (1 / α).re + |z.im + (1 / α).im| ∧
      0 < |z.im| - Ξ - z.re := by
    have h := (Work.Pert.mem_Qm_iff_g z).mp hz
    simpa only [Work.Pert.margA_g, Work.Pert.margB_g] using h
  have hε : ‖F z - (z + 1)‖ ≤ 1 / 32 := hNT z hz
  have hε_im : |(F z - (z + 1)).im| ≤ 1 / 32 :=
    le_trans (Complex.abs_im_le_norm _) hε
  have hε_re : |(F z - (z + 1)).re| ≤ 1 / 32 :=
    le_trans (Complex.abs_re_le_norm _) hε
  have hre : (F z).re = z.re + 1 + (F z - (z + 1)).re := by simp
  have him : (F z).im = z.im + (F z - (z + 1)).im := by simp
  have himsub : |(F z).im - z.im| ≤ 1 / 32 := by
    have he : (F z).im - z.im = (F z - (z + 1)).im := by rw [him]; ring
    rw [he]; exact hε_im
  have hmem : F z ∈ Work.Pert.Qm Ξ α := by
    rw [Work.Pert.mem_Qm_iff_g]
    constructor
    · show 0 < (F z).re - Ξ + (1 / α).re + |(F z).im + (1 / α).im|
      have hre' : z.re + 1 - 1 / 32 ≤ (F z).re := by
        rw [hre]; linarith [neg_abs_le (F z - (z + 1)).re]
      have him' : |z.im + (1 / α).im| - 1 / 32 ≤ |(F z).im + (1 / α).im| := by
        have habs := abs_sub ((F z).im + (1 / α).im) ((F z).im - z.im)
        have heq : ((F z).im + (1 / α).im) - ((F z).im - z.im) = z.im + (1 / α).im := by ring
        rw [heq] at habs
        linarith
      linarith [hz'.1]
    · show 0 < |(F z).im| - Ξ - (F z).re
      have hre' : (F z).re ≤ z.re + 1 + 1 / 32 := by
        rw [hre]; linarith [le_abs_self (F z - (z + 1)).re]
      have him' : |z.im| - 1 / 32 ≤ |(F z).im| := by
        have habs := abs_sub (F z).im ((F z).im - z.im)
        have heq : (F z).im - ((F z).im - z.im) = z.im := by ring
        rw [heq] at habs
        linarith
      linarith [hroom', hre', him']
  exact ⟨hmem, hΦ z hz hmem⟩

/-- **Backward step.**  If `z` is in the gate with room `1 + 1/4` on the left, then there is `w`
with `‖w - (z - 1)‖ ≤ 1/32`, `F w = z`, `w` in the gate and `Φ w = Φ z - 1`. -/
theorem backStep_exists {F Φ : ℂ → ℂ} {z : ℂ}
    (hdiff : DifferentiableOn ℂ F (Work.Pert.Qm Ξ α))
    (hNT : ∀ w ∈ Work.Pert.Qm Ξ α, ‖F w - (w + 1)‖ ≤ 1 / 32 ∧ ‖deriv F w - 1‖ ≤ 1 / 32)
    (hz : z ∈ Work.Pert.Qm Ξ α)
    (hroom : 1 + 1 / 4 ≤ Work.Pert.margA_g Ξ α z)
    (hΦ : ∀ w ∈ Work.Pert.Qm Ξ α, F w ∈ Work.Pert.Qm Ξ α → Φ (F w) = Φ w + 1) :
    ∃ w : ℂ, ‖w - (z - 1)‖ ≤ 1 / 32 ∧ F w = z ∧ w ∈ Work.Pert.Qm Ξ α ∧ Φ w = Φ z - 1 := by
  classical
  have hzA : 0 < Work.Pert.margA_g Ξ α z :=
    ((Work.Pert.mem_Qm_iff_g z).mp hz).1
  have hzB : 0 < Work.Pert.margB_g Ξ z :=
    ((Work.Pert.mem_Qm_iff_g z).mp hz).2
  -- the closed ball is contained in the gate
  have hsub : Metric.closedBall (z - 1) (1 / 32) ⊆ Work.Pert.Qm Ξ α := by
    intro w hw
    rw [Work.Pert.mem_Qm_iff_g]
    have hw32 : ‖w - (z - 1)‖ ≤ 1 / 32 := by
      simpa [dist_eq_norm] using (Metric.mem_closedBall.mp hw)
    have hA : Work.Pert.margA_g Ξ α w ≥ Work.Pert.margA_g Ξ α (z - 1) - 2 * ‖w - (z - 1)‖ := by
      have h := Work.Pert.margA_sub_le Ξ α w (z - 1)
      linarith
    have hB : Work.Pert.margB_g Ξ w ≥ Work.Pert.margB_g Ξ (z - 1) - 2 * ‖w - (z - 1)‖ := by
      have h := Work.Pert.margB_sub_le Ξ w (z - 1)
      linarith
    have hA' : Work.Pert.margA_g Ξ α w
        ≥ Work.Pert.margA_g Ξ α z - 1 - 2 * ‖w - (z - 1)‖ := by
      rw [margA_g_sub_one] at hA; linarith
    have hB' : Work.Pert.margB_g Ξ w
        ≥ Work.Pert.margB_g Ξ z + 1 - 2 * ‖w - (z - 1)‖ := by
      rw [margB_g_sub_one] at hB; linarith
    constructor
    · linarith [hA', hroom, hw32]
    · linarith [hB', hzB, hw32]
  set T : ℂ → ℂ := fun w => z - (F w - w) with hT
  have hTs : MapsTo T (Metric.closedBall (z - 1) (1 / 32))
      (Metric.closedBall (z - 1) (1 / 32)) := by
    intro w hw
    have hwQ : w ∈ Work.Pert.Qm Ξ α := hsub hw
    have h1 : ‖w + 1 - F w‖ ≤ 1 / 32 := by
      have := (hNT w hwQ).1
      simpa [norm_sub_rev] using this
    have he : T w - (z - 1) = w + 1 - F w := by
      simp only [hT]
      ring
    rw [Metric.mem_closedBall, dist_eq_norm, he]
    exact h1
  have hlip : ∀ x ∈ Metric.closedBall (z - 1) (1 / 32),
      ∀ y ∈ Metric.closedBall (z - 1) (1 / 32),
      dist (T x) (T y) ≤ (1 / 32 : ℝ≥0) * dist x y := by
    intro x hx y hy
    have hconv : Convex ℝ (Metric.closedBall (z - 1) (1 / 32)) := convex_closedBall _ _
    have hderiv : ∀ w ∈ Metric.closedBall (z - 1) (1 / 32),
        DifferentiableAt ℂ (fun u => F u - u) w := by
      intro w hw
      have hwQ : w ∈ Work.Pert.Qm Ξ α := hsub hw
      exact (hdiff.differentiableAt (isOpen_Qm.mem_nhds hwQ)).sub differentiableAt_id
    have hbound : ∀ w ∈ Metric.closedBall (z - 1) (1 / 32),
        ‖deriv (fun u => F u - u) w‖ ≤ 1 / 32 := by
      intro w hw
      have hwQ : w ∈ Work.Pert.Qm Ξ α := hsub hw
      have hd : DifferentiableAt ℂ F w :=
        hdiff.differentiableAt (isOpen_Qm.mem_nhds hwQ)
      have hder : deriv (fun u => F u - u) w = deriv F w - 1 := by
        have h1 : deriv (fun u => F u - u) w = deriv F w - deriv (fun u : ℂ => u) w :=
          deriv_sub hd differentiableAt_id
        rw [h1, deriv_id'']
      rw [hder]
      exact (hNT w hwQ).2
    have hmvt := hconv.norm_image_sub_le_of_norm_deriv_le hderiv hbound hx hy
    have hTxy : T x - T y = (F y - y) - (F x - x) := by
      simp only [hT]
      ring
    simp only [dist_eq_norm, hTxy, NNReal.coe_div, NNReal.coe_ofNat, NNReal.coe_one]
    rw [norm_sub_rev x y]
    exact hmvt
  have hK1 : (1 / 32 : ℝ≥0) < 1 := by
    norm_num
  have hcontr : ContractingWith (1 / 32 : ℝ≥0)
      (hTs.restrict T (Metric.closedBall (z - 1) (1 / 32))
        (Metric.closedBall (z - 1) (1 / 32))) := by
    refine ⟨hK1, ?_⟩
    refine LipschitzWith.of_dist_le_mul ?_
    intro x y
    exact hlip x.1 x.2 y.1 y.2
  have hsc : IsComplete (Metric.closedBall (z - 1) (1 / 32)) :=
    Metric.isClosed_closedBall.isComplete
  obtain ⟨w, hws, hfix, -⟩ :=
    hcontr.exists_fixedPoint' hsc hTs (x := z - 1) (by simp) (by simp)
  have hTw : T w = w := hfix
  have hFw : F w = z := by
    have h1 : z - (F w - w) = w := by simpa only [hT] using hTw
    have h2 : z = F w := by
      calc z = z - (F w - w) + (F w - w) := by ring
        _ = w + (F w - w) := by rw [h1]
        _ = F w := by ring
    exact h2.symm
  have hwQ : w ∈ Work.Pert.Qm Ξ α := hsub hws
  have hdist : ‖w - (z - 1)‖ ≤ 1 / 32 := by
    simpa [dist_eq_norm] using (Metric.mem_closedBall.mp hws)
  have hphi : Φ w = Φ z - 1 := by
    have h1 : Φ z = Φ w + 1 := by
      have := hΦ w hwQ (by rw [hFw]; exact hz)
      rwa [hFw] at this
    rw [h1]; ring
  exact ⟨w, hdist, hFw, hwQ, hphi⟩

end

end Work.Pert.pert2v2
