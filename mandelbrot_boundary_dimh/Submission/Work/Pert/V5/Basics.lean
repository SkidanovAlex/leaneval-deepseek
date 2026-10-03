import Mathlib
import Submission.Work.Pert.Setup
import Submission.Work.Pert.Basic
import Submission.Work.Interfaces.Parabolic
import Submission.Work.Interfaces.Fatou
import Submission.Work.Interfaces.FatouNarrow
import Submission.Work.Pert.Qm_slice
import Submission.Work.Pert.band_Qm_margins
import Submission.Work.Pert.dev_vert_le
import Submission.Work.FatouL1.windowDefectBound

/-!
# Auxiliary lemmas for `Work.Pert.Phi_dev_gate_lin_v5`

This file collects the *elementary* (and clash-free) tools used by the assembly of
`Work.Pert.Phi_dev_gate_lin_v5`:

* `mgA`, `mgB`: the two marginals of the gate `Qm Ξ α = Qreg (Ξ - 1/α) (-Ξ)`,
  `mgA z = Re z - Ξ + Re (1/α) + |Im z + Im (1/α)|` (the `b₁`-condition) and
  `mgB z = |Im z| - Ξ - Re z` (the `b₂`-condition), together with `mem_Qm_iff_mg`;
* `band_margins`: every point of the *band* `[-(Ξ+2^10+2M), -(Ξ+2^10)] × ℝ` lies in the gate, with
  explicit margins (this is `Work.Pert.band_Qm_margins`, restated);
* `slice_interval`: the gate slice at a fixed height is an interval, so a horizontal segment
  between two gate points of the same height lies in the gate;
* `ball_in_gate`: the ball of radius `min (mgA z) (mgB z) / √2` around `z ∈ Qm` is contained in
  `Qm` (`Work.Pert.ball_subset_Qm_of_margin_slice`);
* `dev_vert_band`: the vertical transport of the deviation `z ↦ Φm z - z` in the band, with the
  explicit Lipschitz constant `1/150 + 1/31` (a clash-free copy of `Work.Pert.dev_vert_le_gate`,
  with `band_Qm_key_bound` in place of `spine_geometry` for the size of `Re (1/α)`);
* `pin_dev_le`, `dev_step`, `dev_iterate`: the pin bound and the telescoping identity for the
  deviation along an `F`-orbit.
-/

open Set Metric Filter
open scoped Topology

namespace Work.Pert.V5

noncomputable section

/-- The `b₁`-marginal of the gate: `Re z - Ξ + Re (1/α) + |Im z + Im (1/α)|`; its positivity is
the first inequality defining `Qreg (Ξ - 1/α) (-Ξ)`. -/
def mgA (Ξ : ℝ) (α z : ℂ) : ℝ := z.re - Ξ + (1 / α).re + |z.im + (1 / α).im|

/-- The `b₂`-marginal of the gate: `|Im z| - Ξ - Re z`; its positivity is the second inequality
defining `Qreg (Ξ - 1/α) (-Ξ)`. -/
def mgB (Ξ : ℝ) (z : ℂ) : ℝ := |z.im| - Ξ - z.re

theorem mem_Qm_iff_mg {Ξ : ℝ} {α z : ℂ} :
    z ∈ Work.Pert.Qm Ξ α ↔ 0 < mgA Ξ α z ∧ 0 < mgB Ξ z := by
  rw [Qm_mem_iff]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨?_, ?_⟩
    · have h : Ξ - (1/α).re - |z.im + (1/α).im| < z.re := h1
      simp only [mgA]
      linarith
    · have h : z.re < |z.im| - Ξ := h2
      simp only [mgB]
      linarith
  · rintro ⟨h1, h2⟩
    simp only [mgA] at h1
    simp only [mgB] at h2
    exact ⟨by linarith, by linarith⟩

/-- **Every point of the band lies in the gate, with explicit margins.**  For `ξ` in
`[-(Ξ+2^10+2M), -(Ξ+2^10)]` and every height `s`, `ξ + i s ∈ Qm Ξ α`, the `b₂`-margin is at least
`2^10` and the `b₁`-margin at least `16 M`. -/
theorem band_margins {Ξ M : ℝ} {α : ℂ}
    (hΞ : 0 < Ξ) (hM : 2 ^ 10 ≤ M) (hInF1 : MandelDim.InF1 α)
    (hα : ‖α‖ ≤ 1 / (32 * (M + 2 + Ξ)))
    (hQAdm : MandelDim.QAdm (some ((Ξ : ℂ) - 1 / α)) (some (-(Ξ : ℂ)))) :
    ∀ ξ s : ℝ, -(Ξ + 2 ^ 10 + 2 * M) ≤ ξ → ξ ≤ -(Ξ + 2 ^ 10) →
      (ξ + s * Complex.I) ∈ Work.Pert.Qm Ξ α ∧
        2 ^ 10 ≤ mgB Ξ (ξ + s * Complex.I) ∧
        16 * M ≤ mgA Ξ α (ξ + s * Complex.I) := by
  intro ξ s h1 h2
  obtain ⟨hQ, hB, hA, -⟩ := (band_Qm_margins hΞ hM hInF1 hα hQAdm).2 ξ s h1 h2
  have him : (ξ + s * Complex.I : ℂ).im = s := by
    simp [Complex.add_im, Complex.mul_I_im, Complex.ofReal_im]
  have hre : (ξ + s * Complex.I : ℂ).re = ξ := by
    simp [Complex.add_re, Complex.mul_I_re, Complex.ofReal_re]
  refine ⟨hQ, ?_, ?_⟩
  · rw [mgB, him, hre]; exact hB
  · rw [mgA, him, hre]; linarith

/-- **The gate slice at a fixed height is an interval.**  Hence a horizontal segment joining two
points of the gate at the same height stays in the gate. -/
theorem slice_interval {Ξ : ℝ} {α : ℂ} {s a b x : ℝ}
    (ha : (a + s * Complex.I : ℂ) ∈ Work.Pert.Qm Ξ α)
    (hb : (b + s * Complex.I : ℂ) ∈ Work.Pert.Qm Ξ α)
    (hx : x ∈ Set.Icc (min a b) (max a b)) :
    (x + s * Complex.I : ℂ) ∈ Work.Pert.Qm Ξ α := by
  have him : ∀ y : ℝ, ((y + s * Complex.I : ℂ)).im = s := by
    intro y; simp [Complex.add_im, Complex.mul_I_im, Complex.ofReal_im]
  have hre : ∀ y : ℝ, ((y + s * Complex.I : ℂ)).re = y := by
    intro y; simp [Complex.add_re, Complex.mul_I_re, Complex.ofReal_re]
  rw [Qm_mem_iff] at ha hb ⊢
  obtain ⟨ha1, ha2⟩ := ha
  obtain ⟨hb1, hb2⟩ := hb
  rw [him a, hre a] at ha1 ha2
  rw [him b, hre b] at hb1 hb2
  rw [him x, hre x]
  rcases le_total a b with hab | hab
  · rw [min_eq_left hab, max_eq_right hab] at hx
    exact ⟨by linarith [hx.1, ha1], by linarith [hx.2, hb2]⟩
  · rw [min_eq_right hab, max_eq_left hab] at hx
    exact ⟨by linarith [hx.1, hb1], by linarith [hx.2, ha2]⟩

/-- **The ball of radius `min (mgA z) (mgB z) / √2` around `z ∈ Qm` lies in `Qm`.** -/
theorem ball_in_gate {Ξ : ℝ} {α : ℂ} {z : ℂ} (hz : z ∈ Work.Pert.Qm Ξ α) :
    Metric.ball z (min (mgA Ξ α z) (mgB Ξ z) / Real.sqrt 2) ⊆ Work.Pert.Qm Ξ α := by
  set r : ℝ := min (mgA Ξ α z) (mgB Ξ z) / Real.sqrt 2 with hr
  have hmain : Metric.ball ((z.re : ℂ) + z.im * Complex.I) r ⊆ Work.Pert.Qm Ξ α := by
    have hzQ : ((z.re : ℂ) + z.im * Complex.I) ∈ Work.Pert.Qm Ξ α := by
      rw [Complex.re_add_im]; exact hz
    refine ball_subset_Qm_of_margin_slice (ξ := Ξ) (α := α) (x := z.re) (t := z.im)
      (r := r) hzQ ?_
    have hs : (0:ℝ) < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
    have hrg : r * Real.sqrt 2 = min (mgA Ξ α z) (mgB Ξ z) := by
      rw [hr]; exact div_mul_cancel₀ _ (ne_of_gt hs)
    rw [hrg]
    have e1 : z.re - sliceLo Ξ α z.im = mgA Ξ α z := by
      simp only [mgA, sliceLo]; ring
    have e2 : sliceHi Ξ z.im - z.re = mgB Ξ z := by
      simp only [mgB, sliceHi]
    rw [e1, e2]
  rw [Complex.re_add_im] at hmain
  exact hmain

/-- **The deviation at the pinned point.** -/
theorem pin_dev_le {M Kp : ℝ} {Φm : ℂ → ℂ} {z₀ : ℂ}
    (hpin : Φm z₀ = (((-M : ℝ)) : ℂ))
    (hpinbd : ‖z₀ + (((M : ℝ)) : ℂ)‖ ≤ Kp * (1 + Real.log (2 + M))) :
    ‖Φm z₀ - z₀‖ ≤ Kp * (1 + Real.log (2 + M)) := by
  rw [hpin]
  have h : (((-M : ℝ)) : ℂ) - z₀ = -(z₀ + (((M : ℝ)) : ℂ)) := by push_cast; ring
  rw [h, norm_neg]
  exact hpinbd

/-- **Exact per-step recursion** for the deviation `Ψ - id` of a Fatou coordinate. -/
theorem dev_step {F Ψ : ℂ → ℂ} {Q : Set ℂ} (hΨ : MandelDim.IsFatouCoordOn F Ψ Q)
    {w : ℂ} (hw : w ∈ Q) (hFw : F w ∈ Q) :
    (Ψ (F w) - F w) - (Ψ w - w) = -(F w - (w + 1)) := by
  have h := hΨ.2.2 w hw hFw
  rw [h]; ring

/-- **Telescoped recursion** along a legal walk. -/
theorem dev_iterate {F Ψ : ℂ → ℂ} {Q : Set ℂ} (hΨ : MandelDim.IsFatouCoordOn F Ψ Q)
    {z : ℂ} {n : ℕ} (hwalk : ∀ j ≤ n, F^[j] z ∈ Q) :
    (Ψ (F^[n] z) - F^[n] z) - (Ψ z - z) =
      -∑ j ∈ Finset.range n, (F (F^[j] z) - (F^[j] z + 1)) := by
  induction n with
  | zero => simp
  | succ k ih =>
    have h1 : ∀ j ≤ k, F^[j] z ∈ Q := fun j hj => hwalk j (by omega)
    have hk : F^[k] z ∈ Q := hwalk k (by omega)
    have hk1 : F (F^[k] z) ∈ Q := by
      have he : F^[(k + 1)] z = F (F^[k] z) := by rw [Function.iterate_succ_apply']
      rw [← he]; exact hwalk (k + 1) (by omega)
    have hstep := dev_step hΨ hk hk1
    have hiter : F^[k.succ] z = F (F^[k] z) := Function.iterate_succ_apply' F k z
    rw [hiter, Finset.sum_range_succ]
    linear_combination hstep + ih h1

/-- `‖1/v - 1‖ ≤ 1/31` as soon as `‖v - 1‖ ≤ 1/32`. -/
theorem inv_sub_one_le_of_close {v : ℂ} (hv : ‖v - 1‖ ≤ 1 / 32) : ‖1 / v - 1‖ ≤ 1 / 31 := by
  have h1v : ‖1 - v‖ ≤ 1 / 32 := by rw [norm_sub_rev (1 : ℂ) v]; exact hv
  have hvnorm : (31 / 32 : ℝ) ≤ ‖v‖ := by
    have h := norm_add_le v (1 - v)
    have h3 : v + (1 - v) = (1 : ℂ) := by ring
    rw [h3, norm_one, norm_sub_rev (1 : ℂ) v] at h
    linarith
  have hv0 : v ≠ 0 := by
    intro h0; rw [h0, norm_zero] at hvnorm; norm_num at hvnorm
  rw [div_sub_one hv0, norm_div]
  calc ‖1 - v‖ / ‖v‖ ≤ (1 / 32) / (31 / 32) := div_le_div₀ (by norm_num) h1v (by norm_num) hvnorm
    _ = 1 / 31 := by norm_num

/-- **Vertical transport in the band (clash-free copy of `Work.Pert.dev_vert_le_gate`).**

For `ξ` in the band `[-(Ξ+2^10+2M), -(Ξ+2^10)]` the deviation `D z = Φm z - z` is Lipschitz along
the vertical line `Re = ξ` with constant `1/150 + 1/31`:
`‖D (ξ + i s₁) - D (ξ + i s₂)‖ ≤ (1/150 + 1/31) |s₂ - s₁|`.

The constant is the sum of the two inputs of the perturbation layer: the window defect bound
`‖Φ' - 1/(F z - z)‖ ≤ 1/150` of the `L¹` Fatou machinery (transferred to `Φm` by `FatouUnique`),
and `‖1/(F z - z) - 1‖ ≤ 1/31` from the near-translation hypothesis. -/
theorem dev_vert_band {Ξ rr M : ℝ} {α σ : ℂ} {u Φm : ℂ → ℂ}
    (hF : MandelDim.FatouStatement)
    (hΞ : 0 < Ξ) (hrr : 0 < rr) (hM : 2 ^ 10 ≤ M) (hInF1 : MandelDim.InF1 α)
    (hα : ‖α‖ ≤ 1 / (32 * (M + 2 + Ξ)))
    (hQAdm : MandelDim.QAdm (some ((Ξ : ℂ) - 1 / α)) (some (-(Ξ : ℂ))))
    (hσ : σ ≠ 0) (hnorm : 1 - σ * u 0 = Complex.exp (2 * Real.pi * Complex.I * α))
    (hu : DifferentiableOn ℂ u (Metric.ball (0 : ℂ) rr))
    (hu2 : ∀ z ∈ Metric.ball (0 : ℂ) rr, 1 / 2 ≤ ‖u z‖ ∧ ‖u z‖ ≤ 2)
    (hτQ : ∀ z ∈ Work.Pert.Qm Ξ α, Work.Pert.tauC σ α z ∈ Metric.ball (0 : ℂ) rr)
    (hNT : MandelDim.NearTranslationL1 (Work.Pert.liftF u σ α) (Work.Pert.Qm Ξ α))
    (hΦm : MandelDim.IsFatouCoordOn (Work.Pert.liftF u σ α) Φm (Work.Pert.Qm Ξ α)) :
    ∀ ξ s₁ s₂ : ℝ, -(Ξ + 2 ^ 10 + 2 * M) ≤ ξ → ξ ≤ -(Ξ + 2 ^ 10) →
      ‖(Φm ((ξ : ℂ) + s₁ * Complex.I) - ((ξ : ℂ) + s₁ * Complex.I))
        - (Φm ((ξ : ℂ) + s₂ * Complex.I) - ((ξ : ℂ) + s₂ * Complex.I))‖
        ≤ (1 / 150 + 1 / 31) * |s₂ - s₁| := by
  -- ## `Re (1/α)` is large
  have hkey : 18 * M + 2 * Ξ + 2 ^ 10 ≤ (1 / α).re := band_Qm_key_bound hΞ hM hInF1 hα
  have hQopen : IsOpen (Work.Pert.Qm Ξ α) := by
    simpa only [Work.Pert.Qm] using Work.Fatou.Qreg.isOpen_Qreg (some ((Ξ : ℂ) - 1 / α))
      (some (-(Ξ : ℂ)))
  intro ξ s₁ s₂ hξlo hξhi
  have hmem : ∀ t : ℝ, (ξ + t * Complex.I : ℂ) ∈ Work.Pert.Qm Ξ α := fun t =>
    (band_margins hΞ hM hInF1 hα hQAdm ξ t hξlo hξhi).1
  -- ## the room conditions of the window lemma
  have hw1 : ∀ a ∈ (some ((Ξ : ℂ) - 1 / α) : Option ℂ), a.re + 1 < ξ := by
    intro a ha
    rw [Option.mem_some_iff] at ha
    rw [← ha, Complex.sub_re, Complex.ofReal_re]
    linarith
  have hw2 : ∀ b ∈ (some (-(Ξ : ℂ)) : Option ℂ), ξ + 3 < b.re := by
    intro b hb
    rw [Option.mem_some_iff] at hb
    rw [← hb, Complex.neg_re, Complex.ofReal_re]
    have h2p : (3 : ℝ) < 2 ^ 10 := by norm_num
    linarith
  -- ## a Fatou coordinate of `F` with the window defect bound `1/150`
  obtain ⟨Φw, hΦw, hwin⟩ :=
    Work.FatouL1.windowDefectBound (b₁ := some ((Ξ : ℂ) - 1 / α)) (b₂ := some (-(Ξ : ℂ)))
      (F := liftF u σ α) (x₀ := ξ) hQAdm hNT hw1 hw2
  -- ## uniqueness of the Fatou coordinate
  obtain ⟨c, hc⟩ := hF.2.2.1 (some ((Ξ : ℂ) - 1 / α)) (some (-(Ξ : ℂ))) (liftF u σ α) Φw Φm
    hQAdm hNT.1 hΦw hΦm
  have hderiv : ∀ z ∈ Work.Pert.Qm Ξ α, deriv Φm z = deriv Φw z := by
    intro z hz
    have hev : (fun w => Φw w + c) =ᶠ[nhds z] Φm := by
      filter_upwards [hQopen.mem_nhds hz] with w hw
      rw [hc w hw]
    have h1 : deriv (fun w => Φw w + c) z = deriv Φm z := Filter.EventuallyEq.deriv_eq hev
    rw [deriv_add_const] at h1
    exact h1.symm
  -- ## the pointwise derivative bound
  have hpt : ∀ t : ℝ, ‖deriv Φm ((ξ : ℂ) + (t : ℂ) * Complex.I) - 1‖ ≤ 1 / 150 + 1 / 31 := by
    intro t
    have hzQ := hmem t
    have hzin : ((ξ : ℂ) + (t : ℂ) * Complex.I).re = ξ := by simp
    have hwz : ‖deriv Φw ((ξ : ℂ) + (t : ℂ) * Complex.I)
        - 1 / (liftF u σ α ((ξ : ℂ) + (t : ℂ) * Complex.I) - ((ξ : ℂ) + (t : ℂ) * Complex.I))‖
        ≤ 1 / 150 :=
      hwin _ (by rw [hzin]; linarith) (by rw [hzin]; linarith)
    have hv : ‖(liftF u σ α ((ξ : ℂ) + (t : ℂ) * Complex.I) - ((ξ : ℂ) + (t : ℂ) * Complex.I)) - 1‖
        ≤ 1 / 32 := by
      have h := (hNT.1.2 _ hzQ).1
      have he : liftF u σ α ((ξ : ℂ) + (t : ℂ) * Complex.I) - ((ξ : ℂ) + (t : ℂ) * Complex.I) - 1
          = liftF u σ α ((ξ : ℂ) + (t : ℂ) * Complex.I)
              - (((ξ : ℂ) + (t : ℂ) * Complex.I) + 1) := by ring
      rwa [he]
    have hinv := inv_sub_one_le_of_close hv
    have hdz := hderiv _ hzQ
    calc ‖deriv Φm ((ξ : ℂ) + (t : ℂ) * Complex.I) - 1‖
        = ‖(deriv Φm ((ξ : ℂ) + (t : ℂ) * Complex.I)
              - 1 / (liftF u σ α ((ξ : ℂ) + (t : ℂ) * Complex.I)
                  - ((ξ : ℂ) + (t : ℂ) * Complex.I)))
            + (1 / (liftF u σ α ((ξ : ℂ) + (t : ℂ) * Complex.I)
                  - ((ξ : ℂ) + (t : ℂ) * Complex.I)) - 1)‖ := by ring_nf
      _ ≤ ‖deriv Φm ((ξ : ℂ) + (t : ℂ) * Complex.I)
              - 1 / (liftF u σ α ((ξ : ℂ) + (t : ℂ) * Complex.I)
                  - ((ξ : ℂ) + (t : ℂ) * Complex.I))‖
            + ‖1 / (liftF u σ α ((ξ : ℂ) + (t : ℂ) * Complex.I)
                  - ((ξ : ℂ) + (t : ℂ) * Complex.I)) - 1‖ := norm_add_le _ _
      _ ≤ 1 / 150 + 1 / 31 := by rw [hdz]; exact add_le_add hwz hinv
  -- ## integrate along the vertical segment
  rcases le_total s₁ s₂ with hle | hle
  · have hdev := dev_vert_le (Φ := Φm) (Q := Work.Pert.Qm Ξ α) (x := ξ) (y₁ := s₁) (y₂ := s₂)
      (g := fun _ : ℝ => (1 / 150 + 1 / 31 : ℝ)) hQopen hle
      (fun t _ => hmem t) hΦm.1 (fun t _ => hpt t) continuousOn_const
    have hint : (∫ t in s₁..s₂, (1 / 150 + 1 / 31 : ℝ)) = (1 / 150 + 1 / 31) * |s₂ - s₁| := by
      rw [intervalIntegral.integral_const, smul_eq_mul,
        abs_of_nonneg (by linarith : (0 : ℝ) ≤ s₂ - s₁)]
      ring
    rw [hint] at hdev
    rw [norm_sub_rev]
    exact hdev
  · have hdev := dev_vert_le (Φ := Φm) (Q := Work.Pert.Qm Ξ α) (x := ξ) (y₁ := s₂) (y₂ := s₁)
      (g := fun _ : ℝ => (1 / 150 + 1 / 31 : ℝ)) hQopen hle
      (fun t _ => hmem t) hΦm.1 (fun t _ => hpt t) continuousOn_const
    have hint : (∫ t in s₂..s₁, (1 / 150 + 1 / 31 : ℝ)) = (1 / 150 + 1 / 31) * |s₂ - s₁| := by
      rw [intervalIntegral.integral_const, smul_eq_mul,
        abs_of_nonpos (by linarith : s₂ - s₁ ≤ 0)]
      ring
    rw [hint] at hdev
    exact hdev

end

end Work.Pert.V5
