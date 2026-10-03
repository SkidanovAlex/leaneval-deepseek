import Mathlib
import Submission.Work.Pert.waist_cover_pinned_v2
import Submission.Work.Pert.CoverHigh.cover_anchor
import Submission.Work.Pert.CoverHigh.waist_disc_pos
import Submission.Work.Pert.Gates

namespace Work.Pert.pert2v2

/-! ## Local helpers (copies of the private helpers of `Work.Pert.waist_cover_pinned_v2`)

The proof below is the construction of `Work.Pert.waist_cover_pinned_v2` read on the *positive*
height branch only (the new hypothesis is `Y ≤ w.im`, not `Y ≤ |w.im|`), with the extra conclusion
that the `Φ`-preimage produced by the covering argument sits at height `≥ Ξ`. -/

/-- The integer `-(⌊w.re + 1/2⌋)` brings the real part of `w` into `[-1/2, 1/2]`. -/
private lemma abs_re_add_neg_floor (w : ℂ) :
    |(w + ((-(⌊w.re + 1 / 2⌋) : ℤ) : ℂ)).re| ≤ 1 / 2 := by
  have hcast : (((-(⌊w.re + 1 / 2⌋) : ℤ)) : ℂ).re = -(((⌊w.re + 1 / 2⌋) : ℤ) : ℝ) := by
    simp
  rw [Complex.add_re, hcast, abs_le]
  have h1 := Int.floor_le (w.re + 1 / 2)
  have h2 := Int.lt_floor_add_one (w.re + 1 / 2)
  constructor <;> linarith

/-- The lower gate `Qm ξ α` is open (an intersection of two open half-planes). -/
private lemma isOpen_Qm' (ξ : ℝ) (α : ℂ) : IsOpen (Work.Pert.Qm ξ α) := by
  have h1 : IsOpen {z : ℂ | -|(z - ((ξ : ℂ) - 1 / α)).im| < (z - ((ξ : ℂ) - 1 / α)).re} :=
    isOpen_lt (continuous_abs.comp
        (Complex.continuous_im.comp (continuous_id.sub continuous_const))).neg
      (Complex.continuous_re.comp (continuous_id.sub continuous_const))
  have h2 : IsOpen {z : ℂ | (z - (-(ξ : ℂ))).re < |(z - (-(ξ : ℂ))).im|} :=
    isOpen_lt (Complex.continuous_re.comp (continuous_id.sub continuous_const))
      (continuous_abs.comp
        (Complex.continuous_im.comp (continuous_id.sub continuous_const)))
  have h3 : Work.Pert.Qm ξ α =
      {z : ℂ | -|(z - ((ξ : ℂ) - 1 / α)).im| < (z - ((ξ : ℂ) - 1 / α)).re} ∩
        {z : ℂ | (z - (-(ξ : ℂ))).re < |(z - (-(ξ : ℂ))).im|} := by
    ext z
    simp [Work.Pert.Qm, MandelDim.Qreg]
  rw [h3]
  exact h1.inter h2

/-- **The pinned cover, with the witness's preimage height above `Ξ`.**  Strengthened form of
`Work.Pert.waist_cover_pinned_v2` (proved, axiom-clean) carrying one extra conclusion on the
**positive** height branch: the witness `w + n` has its `Φ`-preimage at height `≥ Ξ`.  This is the
witness-branch fact the last cell of the low `R_close` row needs (7th `HANDOFF.md` entry): at that
witness, `invOn Φ (Qm Ξ α) (w + n)` lies in the waist, and `Ξ ≤ ς.im` makes the room
`|ς.im - (1/α).im| - ς.re - Ξ + (1/α).re` exceed `(1/α).re - (1/α).im` outright.

**Proof (cheap, and both reviewers verified it):** copy `Work.Pert.waist_cover_pinned_v2`'s proof and
read the extra conclusion off the same construction.  On the positive branch its witness lies in
`closedBall z₀ r` with `z₀ = i t`, `t = w.im ≥ Y`, `ρ = (t - Ξ - 2)/2`, `r = (ρ - R₂ - 1)/2`
(`CoverHigh.cover_anchor`, `CoverHigh.waist_disc_pos`, `Work.Pert.image_cover_centered`), so
`ζ.im ≥ t - r = (3t + Ξ + 2R₂ + 4)/4 ≥ Ξ` once `t ≥ Ξ`; `Ξ ≤ Y` is added to the threshold, and
`Work.Pert.invOn`'s choice is pinned to that `ζ` by `Set.InjOn Φ (Qm Ξ α)` (from `IsFatouCoordOn`).

**Do NOT add `w ∈ Φ '' Qm Ξ α`** — both reviewers flagged that as false (it is the project's own C1:
`Φ '' Qm Ξ α` is bounded on the right by `Re z < Im z - Ξ`, so it contains no tail `{Im > T}`); the
construction produces only the integer translate, which is why the `n : ℤ` is there.

**Declared fallback** (parked so the row is never blocked): the negative-branch smallness bound
`|ς.im| ≤ ((1/α).re - (1/α).im - (17/16) m - 1)/2`, which kills the `2ς.im` penalty directly. -/
theorem waist_cover_pinned_im {f₀ : ℂ → ℂ} {D₀ : Set ℂ} (d : MandelDim.ParabData f₀ D₀)
    (hF : MandelDim.FatouStatement) (hd : MandelDim.IsParabolicGerm f₀ D₀)
    (Ξ : ℝ) (hΞ : 1 + 64 * Real.pi ≤ Ξ)
    {rr : ℝ} (hrr : 0 < rr) (hrrD : Metric.closedBall (0 : ℂ) rr ⊆ D₀) :
    ∃ Y : ℝ, 0 < Y ∧ Ξ ≤ Y ∧
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
        ∀ w : ℂ, Y ≤ w.im →
          ∃ n : ℤ, |(w + (n : ℂ)).re| < 1 ∧
            w + (n : ℂ) ∈ Φ '' (Work.Pert.Qm Ξ α ∩ Work.Pert.Qp Ξ α) ∧
            Ξ ≤ (Work.Pert.invOn Φ (Work.Pert.Qm Ξ α) (w + (n : ℂ))).im := by
  -- ## 1. the datum-level constants
  -- the pinned deviation bound at the two waist anchors
  -- `‖Φ (± i t) ∓ i t‖ ≤ A log(t+2) + C + t/64` (`A, C, Y₀` do not see `M`)
  obtain ⟨A, C, Y₀, hA, hC, hY₀pos, Ms₀, hMs₀, hdev₀⟩ :=
    Work.Pert.PinLogDev.anchor_dev_le d hF hd Ξ hΞ hrr hrrD
  -- the datum-level radius on which `Φ' ≈ 1` on the gate (`FatouDerivEstimate`)
  obtain ⟨R₂, hR₂, hder₀⟩ := Work.Pert.WaistPinned.deriv_close_on_gate_uniform hF.2.2.2.2.1
  -- the height threshold: the linear term beats `log`
  obtain ⟨Yraw, hYraw, hYraw'⟩ := Work.Pert.WaistPinned.exists_Y_log_linear A C 0 R₂ Ξ hA hC
  -- the second threshold: the *linear slack* `t/64` is beaten by the waist room
  -- (`8 · (t/64) = t/8 < t/2`)
  obtain ⟨Y₁, hY₁pos, hY₁⟩ :=
    Work.Pert.exists_add_mul_log_lt_half A (32 * C + 2 * R₂ + Ξ + 12) hA
  -- the height threshold, enlarged so that it also dominates `Ξ` (this is the one added input of
  -- the strengthened statement: only the *positive* branch `Y ≤ w.im` is covered)
  set Y : ℝ := max Yraw (max Y₁ (max Y₀ (max Ξ 2))) with hYdef
  have hYΞ : Ξ ≤ Y := by
    rw [hYdef]
    exact le_trans (le_max_left Ξ 2)
      (le_trans (le_max_right Y₀ (max Ξ 2))
        (le_trans (le_max_right Y₁ (max Y₀ (max Ξ 2)))
          (le_max_right Yraw (max Y₁ (max Y₀ (max Ξ 2))))))
  have hY2 : (2 : ℝ) ≤ Y := by
    rw [hYdef]
    exact le_trans (le_max_right Ξ 2)
      (le_trans (le_max_right Y₀ (max Ξ 2))
        (le_trans (le_max_right Y₁ (max Y₀ (max Ξ 2)))
          (le_max_right Yraw (max Y₁ (max Y₀ (max Ξ 2))))))
  have hΞpos : 0 < Ξ := by linarith [Real.pi_pos, hΞ]
  have hYpos : 0 < Y := lt_of_lt_of_le hΞpos hYΞ
  have hYYraw : Yraw ≤ Y := by rw [hYdef]; exact le_max_left _ _
  have hYY₁ : Y₁ ≤ Y := by
    rw [hYdef]
    exact le_trans (le_max_left Y₁ (max Y₀ (max Ξ 2)))
      (le_max_right Yraw (max Y₁ (max Y₀ (max Ξ 2))))
  have hYY₀ : Y₀ ≤ Y := by
    rw [hYdef]
    exact le_trans (le_max_left Y₀ (max Ξ 2))
      (le_trans (le_max_right Y₁ (max Y₀ (max Ξ 2)))
        (le_max_right Yraw (max Y₁ (max Y₀ (max Ξ 2)))))
  refine ⟨Y, hYpos, hYΞ, max Ms₀ 1, lt_max_iff.mpr (Or.inr one_pos), ?_⟩
  -- ## 2. the datum-level compact set and threshold for this `M`
  intro M hM
  have hMMs : Ms₀ ≤ M := le_trans (le_max_left _ _) hM
  obtain ⟨L, hLc, hLD, hLrr, δ₀, hδ₀, hdev⟩ := hdev₀ M hMMs
  refine ⟨L, hLc, hLD, hLrr, δ₀, hδ₀, ?_⟩
  -- ## 3. the perturbation data
  intro f Df u σ α Φ hNear hf0 hInF1r hα hdu hub hform hexp hτQ hQAdm hNT hΦ hXcQm hpin
  intro w hw
  have hInF1 : MandelDim.InF1 α := by rw [hα]; exact hInF1r
  -- ## 4. the height `t := Im w` (only the positive branch is needed now) and the anchor `i t`
  set t : ℝ := w.im with ht
  have htY : Y ≤ t := by rw [ht]; exact hw
  have ht2 : (2 : ℝ) ≤ t := le_trans hY2 htY
  have htpos : 0 < t := lt_of_lt_of_le (by norm_num) ht2
  have htYraw : Yraw ≤ t := le_trans hYYraw htY
  have htY₁ : Y₁ ≤ t := le_trans hYY₁ htY
  have hlog0 : 0 ≤ Real.log (t + 2) := Real.log_nonneg (by linarith)
  set z₀ : ℂ := ((t : ℝ) : ℂ) * Complex.I with hz₀
  have hz₀re : z₀.re = 0 := by simp [hz₀]
  have hz₀im : z₀.im = t := by simp [hz₀]
  have hz₀w : z₀.im = w.im := by rw [hz₀im, ht]
  have hz₀abs : |z₀.im| = t := by rw [hz₀im, abs_of_pos htpos]
  -- ## 5. the radius `ρ` of the waist disc at the anchor, from the threshold
  set ρ : ℝ := (t - (Ξ + 2)) / 2 with hρ
  have hbase : R₂ + 7 + 16 * C + 16 * A * Real.log (t + 2) ≤ ρ := by
    have h := hYraw' t htYraw
    rw [hρ]
    simpa using h
  have h16 : 0 ≤ 16 * A * Real.log (t + 2) := mul_nonneg (by linarith) hlog0
  have hbase0 : 0 ≤ R₂ + 7 + 16 * C + 16 * A * Real.log (t + 2) := by
    linarith [hR₂, hC, h16]
  have hρnn : 0 ≤ ρ := le_trans hbase0 hbase
  have hρR₂ : R₂ + 1 ≤ ρ := le_trans (by linarith [hC, h16]) hbase
  have hwaist : Ξ + 2 * ρ < t := by rw [hρ]; linarith
  -- ## 6. the waist disc, the deviation bound at the anchor, and the covering radius
  have hdisc : Metric.closedBall z₀ ρ ⊆ Work.Pert.Qm Ξ α ∩ Work.Pert.Qp Ξ α :=
    Work.Pert.WaistPinned.waist_disc_window (ξ := Ξ) (T := t) (ρ := ρ) (α := α) (z₀ := z₀)
      hInF1 hρnn hwaist hz₀re hz₀abs
  have hdevz : ‖Φ z₀ - z₀‖ ≤ A * Real.log (t + 2) + C + t / 64 := by
    have hanch := hdev f Df u σ α hNear hf0 hInF1r hα hdu hub hform hexp hτQ hQAdm hNT
      Φ hΦ hXcQm hpin
    have htY₀ : Y₀ ≤ t := le_trans hYY₀ htY
    have h := (hanch t htY₀).1
    rw [hz₀]
    simpa using h
  set r : ℝ := (ρ - R₂ - 1) / 2 with hr
  have hrpos : 0 < r := by rw [hr]; linarith
  have hrρ : r ≤ ρ := by rw [hr]; linarith
  have hrR₂ : R₂ ≤ ρ - r := by rw [hr]; linarith
  -- the deviation budget: `1/2 + 2 (A log(t+2) + C + t/64) < r/4`
  have hdev_arith : 1 / 2 + 2 * (A * Real.log (t + 2) + C + t / 64) < r / 4 := by
    have hkey := hY₁ t htY₁
    rw [hr, hρ]
    linarith
  -- ## 7. `Φ` is a near-identity on the disc, so the quarter-ball is covered
  have hsubWaist : Metric.closedBall z₀ r ⊆ Work.Pert.Qm Ξ α ∩ Work.Pert.Qp Ξ α := fun z hz =>
    hdisc (Metric.closedBall_subset_closedBall hrρ hz)
  have hdiff : ∀ ζ ∈ Metric.closedBall z₀ r, DifferentiableAt ℂ Φ ζ := fun ζ hζ =>
    hΦ.1.differentiableAt (isOpen_Qm' Ξ α |>.mem_nhds (hsubWaist hζ).1)
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
  -- ## 8. the integer translate `u = w + n` with `|Re u| ≤ 1/2` is covered
  have hre_n : |(w + (((-(⌊w.re + 1 / 2⌋)) : ℤ) : ℂ)).re| < 1 :=
    lt_of_le_of_lt (abs_re_add_neg_floor w) (by norm_num)
  set uu : ℂ := w + (((-(⌊w.re + 1 / 2⌋)) : ℤ) : ℂ) with huu
  have huure : |uu.re| ≤ 1 / 2 := by rw [huu]; exact abs_re_add_neg_floor w
  have huuim : uu.im = w.im := by rw [huu, Complex.add_im]; simp
  have hsmall : ‖uu - Φ z₀‖ < r / 4 := by
    have hre : |(uu - Φ z₀).re| ≤ 1 / 2 + (A * Real.log (t + 2) + C + t / 64) := by
      have hΦre : (Φ z₀).re = (Φ z₀ - z₀).re := by rw [Complex.sub_re, hz₀re, sub_zero]
      have h1 : |(uu - Φ z₀).re| = |uu.re - (Φ z₀).re| := by rw [Complex.sub_re]
      rw [h1, hΦre]
      have h2 := Complex.abs_re_le_norm (Φ z₀ - z₀)
      linarith [abs_sub uu.re (Φ z₀ - z₀).re]
    have him : |(uu - Φ z₀).im| ≤ A * Real.log (t + 2) + C + t / 64 := by
      have h1 : (uu - Φ z₀).im = -(Φ z₀ - z₀).im := by
        rw [Complex.sub_im, Complex.sub_im, huuim, hz₀w]; ring
      rw [h1, abs_neg]
      exact le_trans (Complex.abs_im_le_norm _) hdevz
    have h3 : ‖uu - Φ z₀‖ ≤ |(uu - Φ z₀).re| + |(uu - Φ z₀).im| :=
      Complex.norm_le_abs_re_add_abs_im _
    linarith
  -- the covering argument produces a concrete preimage `ζ ∈ closedBall z₀ r`
  have hcball : uu ∈ Φ '' Metric.closedBall z₀ r :=
    hcov (by rw [Metric.mem_ball, dist_eq_norm]; exact hsmall)
  have hmem_n : w + (((-(⌊w.re + 1 / 2⌋)) : ℤ) : ℂ) ∈
      Φ '' (Work.Pert.Qm Ξ α ∩ Work.Pert.Qp Ξ α) :=
    Set.image_mono hsubWaist hcball
  obtain ⟨ζ, hζball, hζeq⟩ := hcball
  have hζWaist : ζ ∈ Work.Pert.Qm Ξ α ∩ Work.Pert.Qp Ξ α := hsubWaist hζball
  have hζQm : ζ ∈ Work.Pert.Qm Ξ α := hζWaist.1
  -- ## 9. the extra conclusion: the `Φ`-preimage of the witness lies at height `≥ Ξ`
  -- `InjOn Φ (Qm Ξ α)` pins the *chosen* preimage `invOn Φ (Qm Ξ α) (w+n)` to that `ζ`
  have hinv : Work.Pert.invOn Φ (Work.Pert.Qm Ξ α)
      (w + (((-(⌊w.re + 1 / 2⌋)) : ℤ) : ℂ)) = ζ :=
    Work.Pert.invOn_eq hΦ.2.1 ⟨ζ, hζQm, hζeq⟩ hζQm hζeq
  -- and `ζ` is high: `ζ.im ≥ z₀.im - r = t - r`, and `r ≤ 2ρ = t - Ξ - 2 < t - Ξ`
  have hζim : Ξ ≤ ζ.im := by
    have hdist : dist ζ z₀ ≤ r := by rwa [Metric.mem_closedBall] at hζball
    have hdist' : ‖ζ - z₀‖ ≤ r := by rwa [dist_eq_norm] at hdist
    have habs : |ζ.im - z₀.im| ≤ r :=
      le_trans (Complex.abs_im_le_norm (ζ - z₀)) hdist'
    have hstep : r ≤ t - Ξ := by
      have h1 : r ≤ ρ / 2 := by rw [hr]; linarith
      have h2 : ρ / 2 ≤ 2 * ρ := by linarith
      have h3 : 2 * ρ = t - Ξ - 2 := by rw [hρ]; ring
      linarith
    have h4 : z₀.im - r ≤ ζ.im := by
      have h := (abs_le.mp habs).1
      rw [hz₀im] at h
      linarith
    linarith
  exact ⟨_, hre_n, hmem_n, by rw [hinv]; exact hζim⟩

end Work.Pert.pert2v2
