import Mathlib
import Submission.Work.Pert.pert2v2.waist_cover_pinned_im
import Submission.Work.Pert.waist_cover_pinned_v2
import Submission.Work.Pert.Gates
import Submission.Work.Pert.pert2v2.waist_room
import Submission.Work.Pert.RBlock4.gate_walk_Qreg

namespace Work.Pert.pert2v2

/-- The lower gate `Qm ξ α` is open (an intersection of two open half-planes). -/
private lemma isOpen_Qm_seg (ξ : ℝ) (α : ℂ) : IsOpen (Work.Pert.Qm ξ α) := by
  have h1 : IsOpen {z : ℂ | -|((z - ((ξ : ℂ) - 1 / α)).im)| < (z - ((ξ : ℂ) - 1 / α)).re} :=
    isOpen_lt (continuous_abs.comp
        (Complex.continuous_im.comp (continuous_id.sub continuous_const))).neg
      (Complex.continuous_re.comp (continuous_id.sub continuous_const))
  have h2 : IsOpen {z : ℂ | (z - (-(ξ : ℂ))).re < |((z - (-(ξ : ℂ))).im)|} :=
    isOpen_lt (Complex.continuous_re.comp (continuous_id.sub continuous_const))
      (continuous_abs.comp
        (Complex.continuous_im.comp (continuous_id.sub continuous_const)))
  have h3 : Work.Pert.Qm ξ α =
      {z : ℂ | -|((z - ((ξ : ℂ) - 1 / α)).im)| < (z - ((ξ : ℂ) - 1 / α)).re} ∩
        {z : ℂ | (z - (-(ξ : ℂ))).re < |((z - (-(ξ : ℂ))).im)|} := by
    ext z
    simp [Work.Pert.Qm, MandelDim.Qreg]
  rw [h3]
  exact h1.inter h2

/-- **The pinned cover, uniformly along a segment.**  A single integer `n` works for the whole
half-open segment `{x + y₀ i : x ∈ Ico 0 1}`: the translate lies in the gate ∩ waist image and its
`Φ`-preimage has height `≥ Ξ`.  Hypotheses are those of the proved
`Work.Pert.pert2v2.waist_cover_pinned_im` verbatim; only the conclusion is uniform in `x`.  This is
the delegation spec of the 11th `HANDOFF.md` entry (steps 5 + 3 of the low `R_close` row).

**Route — use the covering-ball mechanism, not the window clause** (both reviewers corrected an
earlier sketch on this): in the base lemma's proof the anchor is `z₀ = i·t` with `t = w.im ≥ y₀`, the
covering ball is `Metric.ball (Φ z₀) (r/4) ⊆ Φ '' (Qm Ξ α ∩ Qp Ξ α)` with
`r = (t - Ξ - 2R₂ - 4)/4`, i.e. radius `≈ (y₀ - Ξ)/16`, and `closedBall z₀ r ⊆ Qm Ξ α ∩ Qp Ξ α`.  So
**enlarge `Y`** (freely, it is existential) so that
`1 + (A log (y₀ + 2) + C + y₀/64) < r/4`; then the *whole* unit segment `{x + y₀ i : x ∈ [0,1]}` lies in
that ball, hence in `Φ '' (Qm Ξ α ∩ Qp Ξ α)` — with the constant integer `n = 0`.  Any preimage
`ζ ∈ closedBall z₀ r` has `ζ.im ≥ y₀ - r ≥ Ξ`, which is the second conjunct (use
`Set.InjOn Φ (Qm Ξ α)` — from `IsFatouCoordOn` — to identify it with `invOn`).

Two traps the statement is shaped to avoid, worth preserving: membership must be at **level 0**
(`Φ '' (Qm Ξ α ∩ Qp Ξ α)`, not merely `GoodP` at the minimal level), and the integer must be
**constant in `x`** (a jumping `n(x)` would satisfy every pointwise hypothesis of
`hornmap_segment_close` while breaking holomorphy for `end_const_le_seg` and the periodicity step).
The half-open `Ico 0 1` costs nothing downstream: `end_const_le_seg` needs its `hseg` on the whole
*line* `{Im = y₀}`, obtained via `Work.Pert.pert2v2.norm_le_of_periodic_seg` from the segment, with
`x = 1` recovered by `1`-periodicity of `Ef`. -/
theorem waist_cover_pinned_im_seg {f₀ : ℂ → ℂ} {D₀ : Set ℂ} (d : MandelDim.ParabData f₀ D₀)
    (hF : MandelDim.FatouStatement) (hd : MandelDim.IsParabolicGerm f₀ D₀)
    (Ξ : ℝ) (hΞ : 1 + 64 * Real.pi ≤ Ξ)
    {rr : ℝ} (hrr : 0 < rr) (hrrD : Metric.closedBall (0 : ℂ) rr ⊆ D₀) :
    ∃ Y : ℝ, Ξ < Y ∧
    ∃ Ms : ℝ, 0 < Ms ∧ ∀ M : ℝ, Ms ≤ M →
    ∃ L : Set ℂ, IsCompact L ∧ L ⊆ D₀ ∧ Metric.closedBall (0 : ℂ) rr ⊆ L ∧
      ∃ δ₀ : ℝ, 0 < δ₀ ∧
      ∀ (f : ℂ → ℂ) (Df : Set ℂ) (u : ℂ → ℂ) (σ α : ℂ) (Φ : ℂ → ℂ),
        MandelDim.NearOn f₀ f Df L δ₀ → f 0 = 0 → MandelDim.InF1 (MandelDim.rotOf f) →
        α = MandelDim.rotOf f →
        DifferentiableOn ℂ u (Metric.ball (0 : ℂ) rr) →
        (∀ z ∈ Metric.ball (0 : ℂ) rr, 1 / 2 ≤ ‖u z‖ ∧ ‖u z‖ ≤ 2) →
        (∀ z ∈ Metric.ball (0 : ℂ) rr, f z = z + z * (z - σ) * u z) →
        1 - σ * u 0 = Complex.exp (2 * Real.pi * Complex.I * α) →
        (∀ z ∈ Work.Pert.Qm Ξ α, Work.Pert.tauC σ α z ∈ Metric.ball (0 : ℂ) rr) →
        MandelDim.QAdm (some ((Ξ : ℂ) - 1 / α)) (some (-(Ξ : ℂ))) →
        MandelDim.NearTranslationL1 (Work.Pert.liftF u σ α) (Work.Pert.Qm Ξ α) →
        MandelDim.IsFatouCoordOn (Work.Pert.liftF u σ α) Φ (Work.Pert.Qm Ξ α) →
        Work.Pert.Xc d (((-M : ℝ)) : ℂ) ∈ Work.Pert.Qm Ξ α →
        Φ (Work.Pert.Xc d (((-M : ℝ)) : ℂ)) = (((-M : ℝ)) : ℂ) →
        ∀ y₀ : ℝ, Y ≤ y₀ →
          ∃ n : ℤ, ∀ x ∈ Set.Ico (0 : ℝ) 1,
            (x : ℂ) + (y₀ : ℂ) * Complex.I + (n : ℂ) ∈
              Φ '' (Work.Pert.Qm Ξ α ∩ Work.Pert.Qp Ξ α) ∧
            Ξ ≤ (Work.Pert.invOn Φ (Work.Pert.Qm Ξ α)
              ((x : ℂ) + (y₀ : ℂ) * Complex.I + (n : ℂ))).im := by
  -- ## 1. the datum-level constants
  -- the pinned deviation bound at the two waist anchors
  -- `‖Φ (± i t) ∓ i t‖ ≤ A log(t+2) + C + t/64` (`A, C, Y₀` do not see `M`)
  obtain ⟨A, C, Y₀, hA, hC, hY₀pos, Ms₀, hMs₀, hdev₀⟩ :=
    Work.Pert.PinLogDev.anchor_dev_le d hF hd Ξ hΞ hrr hrrD
  -- the datum-level radius on which `Φ' ≈ 1` on the gate (`FatouDerivEstimate`)
  obtain ⟨R₂, hR₂, hder₀⟩ := Work.Pert.WaistPinned.deriv_close_on_gate_uniform hF.2.2.2.2.1
  -- the height threshold: the linear term beats `log`
  obtain ⟨Yraw, hYraw, hYraw'⟩ := Work.Pert.WaistPinned.exists_Y_log_linear A C 0 R₂ Ξ hA hC
  -- the second threshold: the *linear slack* `t/64` is beaten by the waist room, with the additive
  -- constant enlarged from `12` to `20` because the window is the whole unit segment (`1` instead
  -- of `1/2`): `16 + 32·(deviation) + t/2 < t - Ξ - 2R₂ - 4`
  obtain ⟨Y₁, hY₁pos, hY₁⟩ :=
    Work.Pert.exists_add_mul_log_lt_half A (32 * C + 2 * R₂ + Ξ + 20) hA
  -- the height threshold, enlarged so that it is strictly bigger than `Ξ` and at least `2`
  set Y : ℝ := max Yraw (max Y₁ (max Y₀ (max (Ξ + 1) 2))) with hYdef
  have hYΞ1 : Ξ + 1 ≤ Y := by
    rw [hYdef]
    exact le_trans (le_max_left (Ξ + 1) 2)
      (le_trans (le_max_right Y₀ (max (Ξ + 1) 2))
        (le_trans (le_max_right Y₁ (max Y₀ (max (Ξ + 1) 2)))
          (le_max_right Yraw (max Y₁ (max Y₀ (max (Ξ + 1) 2))))))
  have hY2 : (2 : ℝ) ≤ Y := by
    rw [hYdef]
    exact le_trans (le_max_right (Ξ + 1) 2)
      (le_trans (le_max_right Y₀ (max (Ξ + 1) 2))
        (le_trans (le_max_right Y₁ (max Y₀ (max (Ξ + 1) 2)))
          (le_max_right Yraw (max Y₁ (max Y₀ (max (Ξ + 1) 2))))))
  have hYΞ : Ξ < Y := lt_of_lt_of_le (by linarith) hYΞ1
  have hYYraw : Yraw ≤ Y := by rw [hYdef]; exact le_max_left _ _
  have hYY₁ : Y₁ ≤ Y := by
    rw [hYdef]
    exact le_trans (le_max_left Y₁ (max Y₀ (max (Ξ + 1) 2)))
      (le_max_right Yraw (max Y₁ (max Y₀ (max (Ξ + 1) 2))))
  have hYY₀ : Y₀ ≤ Y := by
    rw [hYdef]
    exact le_trans (le_max_left Y₀ (max (Ξ + 1) 2))
      (le_trans (le_max_right Y₁ (max Y₀ (max (Ξ + 1) 2)))
        (le_max_right Yraw (max Y₁ (max Y₀ (max (Ξ + 1) 2)))))
  refine ⟨Y, hYΞ, max Ms₀ 1, lt_max_iff.mpr (Or.inr one_pos), ?_⟩
  -- ## 2. the datum-level compact set and threshold for this `M`
  intro M hM
  have hMMs : Ms₀ ≤ M := le_trans (le_max_left _ _) hM
  obtain ⟨L, hLc, hLD, hLrr, δ₀, hδ₀, hdev⟩ := hdev₀ M hMMs
  refine ⟨L, hLc, hLD, hLrr, δ₀, hδ₀, ?_⟩
  -- ## 3. the perturbation data
  intro f Df u σ α Φ hNear hf0 hInF1r hα hdu hub hform hexp hτQ hQAdm hNT hΦ hXcQm hpin
  have hInF1 : MandelDim.InF1 α := by rw [hα]; exact hInF1r
  -- ## 4. the height `t := y₀` and the anchor `z₀ = i t`
  intro y₀ hy₀
  have hy₀Ξ1 : Ξ + 1 ≤ y₀ := le_trans hYΞ1 hy₀
  have hy₀2 : (2 : ℝ) ≤ y₀ := le_trans hY2 hy₀
  have hy₀pos : 0 < y₀ := lt_of_lt_of_le (by norm_num) hy₀2
  have hy₀Yraw : Yraw ≤ y₀ := le_trans hYYraw hy₀
  have hy₀Y₁ : Y₁ ≤ y₀ := le_trans hYY₁ hy₀
  have hy₀Y₀ : Y₀ ≤ y₀ := le_trans hYY₀ hy₀
  have hlog0 : 0 ≤ Real.log (y₀ + 2) := Real.log_nonneg (by linarith)
  set z₀ : ℂ := ((y₀ : ℝ) : ℂ) * Complex.I with hz₀
  have hz₀re : z₀.re = 0 := by simp [hz₀]
  have hz₀im : z₀.im = y₀ := by simp [hz₀]
  have hz₀abs : |z₀.im| = y₀ := by rw [hz₀im, abs_of_pos hy₀pos]
  -- ## 5. the radius `ρ` of the waist disc at the anchor, from the threshold
  set ρ : ℝ := (y₀ - (Ξ + 2)) / 2 with hρ
  have hbase : R₂ + 7 + 16 * C + 16 * A * Real.log (y₀ + 2) ≤ ρ := by
    have h := hYraw' y₀ hy₀Yraw
    rw [hρ]
    simpa using h
  have h16 : 0 ≤ 16 * A * Real.log (y₀ + 2) := mul_nonneg (by linarith) hlog0
  have hbase0 : 0 ≤ R₂ + 7 + 16 * C + 16 * A * Real.log (y₀ + 2) := by
    linarith [hR₂, hC, h16]
  have hρnn : 0 ≤ ρ := le_trans hbase0 hbase
  have hρR₂ : R₂ + 1 ≤ ρ := le_trans (by linarith [hC, h16]) hbase
  have hwaist : Ξ + 2 * ρ < y₀ := by rw [hρ]; linarith
  -- ## 6. the waist disc, the deviation bound at the anchor, and the covering radius
  have hdisc : Metric.closedBall z₀ ρ ⊆ Work.Pert.Qm Ξ α ∩ Work.Pert.Qp Ξ α :=
    Work.Pert.WaistPinned.waist_disc_window (ξ := Ξ) (T := y₀) (ρ := ρ) (α := α) (z₀ := z₀)
      hInF1 hρnn hwaist hz₀re hz₀abs
  have hdevz : ‖Φ z₀ - z₀‖ ≤ A * Real.log (y₀ + 2) + C + y₀ / 64 := by
    have hanch := hdev f Df u σ α hNear hf0 hInF1r hα hdu hub hform hexp hτQ hQAdm hNT
      Φ hΦ hXcQm hpin
    have h := (hanch y₀ hy₀Y₀).1
    rw [hz₀]
    simpa using h
  set r : ℝ := (ρ - R₂ - 1) / 2 with hr
  have hrpos : 0 < r := by rw [hr]; linarith
  have hrρ : r ≤ ρ := by rw [hr]; linarith
  have hrR₂ : R₂ ≤ ρ - r := by rw [hr]; linarith
  -- the deviation budget: `1 + 2 (A log(y₀+2) + C + y₀/64) < r/4` (the `1` is the half-width of
  -- the window `Ico 0 1` doubled: `|Re| ≤ 1`)
  have hdev_arith : 1 + 2 * (A * Real.log (y₀ + 2) + C + y₀ / 64) < r / 4 := by
    have hkey := hY₁ y₀ hy₀Y₁
    rw [hr, hρ]
    linarith
  -- ## 7. `Φ` is a near-identity on the disc, so the quarter-ball is covered
  have hsubWaist : Metric.closedBall z₀ r ⊆ Work.Pert.Qm Ξ α ∩ Work.Pert.Qp Ξ α := fun z hz =>
    hdisc (Metric.closedBall_subset_closedBall hrρ hz)
  have hdiff : ∀ ζ ∈ Metric.closedBall z₀ r, DifferentiableAt ℂ Φ ζ := fun ζ hζ =>
    hΦ.1.differentiableAt (isOpen_Qm_seg Ξ α |>.mem_nhds (hsubWaist hζ).1)
  have hder : ∀ ζ ∈ Metric.closedBall z₀ r, ‖deriv Φ ζ - 1‖ ≤ 1 / 2 := by
    intro ζ hζ
    refine hder₀ (Work.Pert.liftF u σ α) Φ α Ξ hNT hΦ ζ (ρ - r) hrR₂ ?_
    intro z hz
    rw [Metric.mem_ball] at hz
    have h1 : dist ζ z₀ ≤ r := by rwa [Metric.mem_closedBall] at hζ
    have h2 : dist z z₀ < ρ := by
      calc dist z z₀ ≤ dist z ζ + dist ζ z₀ := dist_triangle _ _ _
        _ < (ρ - r) + r := by linarith
        _ = ρ := by ring
    exact (hdisc (Metric.mem_closedBall.mpr h2.le)).1
  have hcov : Metric.ball (Φ z₀) (r / 4) ⊆ Φ '' Metric.closedBall z₀ r :=
    Work.Pert.image_cover_centered hrpos hdiff hder
  -- ## 8. the whole segment sits in that ball, with the constant integer translate `n = 0`
  refine ⟨0, ?_⟩
  intro x hx
  obtain ⟨hx0, hx1⟩ := hx
  simp only [Int.cast_zero, add_zero]
  set w : ℂ := (x : ℂ) + (y₀ : ℂ) * Complex.I with hwdef
  have hwre : w.re = x := by rw [hwdef]; simp
  have hwim : w.im = y₀ := by rw [hwdef]; simp
  have hwabsre : |w.re| ≤ 1 := by
    rw [hwre]
    exact abs_le.mpr ⟨by linarith, le_of_lt hx1⟩
  have hsmall : ‖w - Φ z₀‖ < r / 4 := by
    have hre : |(w - Φ z₀).re| ≤ 1 + (A * Real.log (y₀ + 2) + C + y₀ / 64) := by
      have hΦre : (Φ z₀).re = (Φ z₀ - z₀).re := by rw [Complex.sub_re, hz₀re, sub_zero]
      have h1 : |(w - Φ z₀).re| = |w.re - (Φ z₀).re| := by rw [Complex.sub_re]
      rw [h1, hΦre]
      have h2 := Complex.abs_re_le_norm (Φ z₀ - z₀)
      linarith [abs_sub w.re (Φ z₀ - z₀).re, hwabsre]
    have him : |(w - Φ z₀).im| ≤ A * Real.log (y₀ + 2) + C + y₀ / 64 := by
      have h1 : (w - Φ z₀).im = -(Φ z₀ - z₀).im := by
        rw [Complex.sub_im, Complex.sub_im, hwim, hz₀im]; ring
      rw [h1, abs_neg]
      exact le_trans (Complex.abs_im_le_norm _) hdevz
    have h3 : ‖w - Φ z₀‖ ≤ |(w - Φ z₀).re| + |(w - Φ z₀).im| :=
      Complex.norm_le_abs_re_add_abs_im _
    linarith
  have hmemcb : w ∈ Φ '' Metric.closedBall z₀ r :=
    hcov (by rw [Metric.mem_ball, dist_eq_norm]; exact hsmall)
  have hmem : w ∈ Φ '' (Work.Pert.Qm Ξ α ∩ Work.Pert.Qp Ξ α) := Set.image_mono hsubWaist hmemcb
  -- ## 9. the second conjunct: the `Φ`-preimage of the witness lies at height `≥ Ξ`
  obtain ⟨ζ, hζball, hζeq⟩ := hmemcb
  have hζWaist : ζ ∈ Work.Pert.Qm Ξ α ∩ Work.Pert.Qp Ξ α := hsubWaist hζball
  have hζQm : ζ ∈ Work.Pert.Qm Ξ α := hζWaist.1
  -- `InjOn Φ (Qm Ξ α)` pins the *chosen* preimage `invOn Φ (Qm Ξ α) w` to that `ζ`
  have hinv : Work.Pert.invOn Φ (Work.Pert.Qm Ξ α) w = ζ :=
    Work.Pert.invOn_eq hΦ.2.1 ⟨ζ, hζQm, hζeq⟩ hζQm hζeq
  have hζim : Ξ ≤ ζ.im := by
    have hdist : dist ζ z₀ ≤ r := by rwa [Metric.mem_closedBall] at hζball
    have hdist' : ‖ζ - z₀‖ ≤ r := by rwa [dist_eq_norm] at hdist
    have habs : |ζ.im - z₀.im| ≤ r :=
      le_trans (Complex.abs_im_le_norm (ζ - z₀)) hdist'
    have hstep : r ≤ y₀ - Ξ := by
      have h1 : r ≤ ρ / 2 := by rw [hr]; linarith
      have h2 : ρ / 2 ≤ 2 * ρ := by linarith
      have h3 : 2 * ρ = y₀ - Ξ - 2 := by rw [hρ]; ring
      linarith
    have h4 : z₀.im - r ≤ ζ.im := by
      have h := (abs_le.mp habs).1
      rw [hz₀im] at h
      linarith
    linarith
  exact ⟨hmem, by rw [hinv]; exact hζim⟩

end Work.Pert.pert2v2
