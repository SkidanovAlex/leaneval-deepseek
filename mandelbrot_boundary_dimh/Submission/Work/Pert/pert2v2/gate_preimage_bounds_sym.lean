import Mathlib
import Submission.Work.Pert.Setup
import Submission.Work.Pert.MaxDom
import Submission.Work.Pert.Basic
import Submission.Work.Pert.pert2v2.GatePreimageReBound.gate_preimage_re_bound
import Submission.Work.Pert.pert2v2.gate_preimage_im_bound
import Submission.Work.Pert.pert2v2.walk_to_window

/-!
# `Work.Pert.pert2v2.gate_preimage_bounds_sym`

**The symmetric-window preimage bounds.**  The proved companions
`GatePreimageReBound.gate_preimage_re_bound`, `gate_preimage_im_bound` and `gate_preimage_dev_bound`
control the chosen gate preimage `ς = invOn Φ (Qm Ξ α) w` of a point `w` of the *fundamental window*
`0 ≤ w.re < 1` of the cylinder.  This lemma does the same for the symmetric window
`|w.re| ≤ 1/2` centered at the axis, which is the window in which the glued return map `R` is
described.

The whole content of the extension is a **height gain**: both bounds of the companions are derived
from the upper-end asymptotics `Φ z = z + c + o(1)` applied at a point of the *fixed* real window
`[-2,2]`, which is reached from the preimage by the gate walk; so everything needs the preimage to
be high up, and the cover hypothesis pins the preimage only of the window `[0,1)`.  For a point `w`
with `-1 ≤ w.re < 0` the shifted point `w + 1` lies in the window, so `hcov` pins *its* preimage
`ς = invOn Φ (Qm Ξ α) (w+1)` at height `≥ (3 w.im + Ξ)/4`; the orbit relation `FatouOrbit`
(`hF.2.1`), applied to `Φ ς = w + 1 = Φ ς + 1`, gives `F ς = ς`, and the near-translation defect
`‖F ς - (ς+1)‖ ≤ 1/32` transfers the height bound back to `ς`.  This is the lemma `im_gain_sym`
below; from it the two bounds follow exactly as in the companions.
-/

namespace Work.Pert.pert2v2

noncomputable section

/-- **Height gain for the gate preimage in the symmetric window `|Re w| ≤ 1/2`.**  For every point
`w` of `Φ '' Qm Ξ α` with `|w.re| ≤ 1/2` and large height, the chosen preimage
`invOn Φ (Qm Ξ α) w` is at height `≥ (3 w.im + Ξ)/4 - 1/32`.

(Recall `Qm Ξ α = Qreg (some (Ξ - 1/α)) (some (-Ξ))`, so `MandelDim.FatouOrbit` — a field of
`hF` — applies to the two gate points `ζ` and `ς` below.) -/
theorem im_gain_sym {u : ℂ → ℂ} {σ α : ℂ} {Ξ : ℝ} {Φ : ℂ → ℂ}
    (hF : MandelDim.FatouStatement) (hΞ : 0 < Ξ)
    (hQAdm : MandelDim.QAdm (some ((Ξ : ℂ) - 1 / α)) (some (-(Ξ : ℂ))))
    (hNT : MandelDim.NearTranslationL1 (Work.Pert.liftF u σ α) (Work.Pert.Qm Ξ α))
    (hΦ : MandelDim.IsFatouCoordOn (Work.Pert.liftF u σ α) Φ (Work.Pert.Qm Ξ α))
    (hcover : ∃ Y : ℝ, Ξ < Y ∧ ∀ y₀ : ℝ, Y ≤ y₀ → ∀ x ∈ Set.Ico (0 : ℝ) 1,
      (x : ℂ) + (y₀ : ℂ) * Complex.I ∈ Φ '' (Work.Pert.Qm Ξ α ∩ Work.Pert.Qp Ξ α) ∧
      (3 * y₀ + Ξ) / 4 ≤ (Work.Pert.invOn Φ (Work.Pert.Qm Ξ α)
        ((x : ℂ) + (y₀ : ℂ) * Complex.I)).im) :
    ∃ Yg : ℝ, ∀ w : ℂ, Yg ≤ w.im → |w.re| ≤ 1 / 2 → w ∈ Φ '' (Work.Pert.Qm Ξ α) →
      (3 * w.im + Ξ) / 4 - 1 / 32 ≤ (Work.Pert.invOn Φ (Work.Pert.Qm Ξ α) w).im := by
  obtain ⟨Y, _hΞY, hcov⟩ := hcover
  refine ⟨Y, ?_⟩
  intro w hwY hwre hwmem
  set ζ : ℂ := Work.Pert.invOn Φ (Work.Pert.Qm Ξ α) w with hζdef
  have hζQ : ζ ∈ Work.Pert.Qm Ξ α := Work.Pert.invOn_mem hwmem
  have hζΦ : Φ ζ = w := Work.Pert.invOn_spec hwmem
  by_cases h0 : 0 ≤ w.re
  · -- `w` itself lies in the window covered by `hcov`
    have hx : w.re ∈ Set.Ico (0 : ℝ) 1 := ⟨h0, by linarith [(abs_le.mp hwre).2]⟩
    have hc := hcov w.im hwY w.re hx
    rw [Complex.re_add_im w, ← hζdef] at hc
    linarith [hc.2]
  · -- shift into the window: `w + 1` has real part in `[0,1)`
    push_neg at h0
    have hpt : ((w.re + 1 : ℝ) : ℂ) + ((w.im : ℝ) : ℂ) * Complex.I = w + 1 := by
      have h1 : ((w.re : ℂ) + (w.im : ℂ) * Complex.I) = w := Complex.re_add_im w
      calc ((w.re + 1 : ℝ) : ℂ) + ((w.im : ℝ) : ℂ) * Complex.I
          = ((w.re : ℂ) + (w.im : ℂ) * Complex.I) + 1 := by push_cast; ring
        _ = w + 1 := by rw [h1]
    have hx : w.re + 1 ∈ Set.Ico (0 : ℝ) 1 :=
      ⟨by linarith [(abs_le.mp hwre).1], by linarith⟩
    have hc := hcov w.im hwY (w.re + 1) hx
    rw [hpt] at hc
    obtain ⟨z, hz, hzΦ⟩ := hc.1
    have hςmem : ∃ z ∈ Work.Pert.Qm Ξ α, Φ z = w + 1 := ⟨z, hz.1, hzΦ⟩
    set ς : ℂ := Work.Pert.invOn Φ (Work.Pert.Qm Ξ α) (w + 1) with hςdef
    have hςQ : ς ∈ Work.Pert.Qm Ξ α := Work.Pert.invOn_mem hςmem
    have hςΦ : Φ ς = w + 1 := Work.Pert.invOn_spec hςmem
    have hςim : (3 * w.im + Ξ) / 4 ≤ ς.im := hc.2
    -- the orbit relation `F ζ = ς`, from `Φ ς = Φ ζ + 1` (`FatouOrbit`)
    have hrel : Φ ς = Φ ζ + ((1 : ℕ) : ℂ) := by
      rw [hςΦ, hζΦ]
      push_cast
      ring
    have horb := hF.2.1 (some ((Ξ : ℂ) - 1 / α)) (some (-(Ξ : ℂ)))
      (Work.Pert.liftF u σ α) Φ hQAdm hNT.1 hΦ ζ hζQ ς hςQ 1 hrel
    have hFζ : Work.Pert.liftF u σ α ζ = ς := by
      simpa using horb.2
    have hdef : ‖Work.Pert.liftF u σ α ζ - (ζ + 1)‖ ≤ 1 / 32 := (hNT.1.2 ζ hζQ).1
    have him : |ς.im - ζ.im| ≤ 1 / 32 := by
      have h1 := Complex.abs_im_le_norm (Work.Pert.liftF u σ α ζ - (ζ + 1))
      have h2 : (Work.Pert.liftF u σ α ζ - (ζ + 1)).im = ς.im - ζ.im := by
        simp only [Complex.sub_im, Complex.add_im, Complex.one_im, hFζ]
        ring
      rw [h2] at h1
      exact le_trans h1 hdef
    have him' : ς.im - 1 / 32 ≤ ζ.im := by
      have h := (abs_le.mp him).2
      linarith
    linarith

theorem gate_preimage_bounds_sym {u : ℂ → ℂ} {σ α : ℂ} {Ξ : ℝ} {Φ : ℂ → ℂ}
    (hF : MandelDim.FatouStatement) (hΞ : 0 < Ξ)
    (hQAdm : MandelDim.QAdm (some ((Ξ : ℂ) - 1 / α)) (some (-(Ξ : ℂ))))
    (hNT : MandelDim.NearTranslationL1 (Work.Pert.liftF u σ α) (Work.Pert.Qm Ξ α))
    (hΦ : MandelDim.IsFatouCoordOn (Work.Pert.liftF u σ α) Φ (Work.Pert.Qm Ξ α))
    (hdec : ∃ M κ Y : ℝ, 0 < M ∧ 0 < κ ∧ ∀ z ∈ Work.Pert.Qm Ξ α, Y < z.im →
      ‖Work.Pert.liftF u σ α z - (z + 1)‖ ≤ M * Real.exp (-(κ * z.im)))
    (hcover : ∃ Y : ℝ, Ξ < Y ∧ ∀ y₀ : ℝ, Y ≤ y₀ → ∀ x ∈ Set.Ico (0 : ℝ) 1,
      (x : ℂ) + (y₀ : ℂ) * Complex.I ∈ Φ '' (Work.Pert.Qm Ξ α ∩ Work.Pert.Qp Ξ α) ∧
      (3 * y₀ + Ξ) / 4 ≤ (Work.Pert.invOn Φ (Work.Pert.Qm Ξ α)
        ((x : ℂ) + (y₀ : ℂ) * Complex.I)).im) :
    ∃ B C Yc : ℝ, 0 ≤ B ∧ 0 ≤ C ∧ ∀ w : ℂ, Yc ≤ w.im → |w.re| ≤ 1 / 2 →
      w ∈ Φ '' (Work.Pert.Qm Ξ α) →
      |(Work.Pert.invOn Φ (Work.Pert.Qm Ξ α) w).re| ≤ B ∧
      w.im - C ≤ (Work.Pert.invOn Φ (Work.Pert.Qm Ξ α) w).im := by
  obtain ⟨M, κ, Yd, hM, hκ, hdec'⟩ := hdec
  -- the two walks of the gate, which reach the fixed real window `[-2,2]`
  obtain ⟨K, hK⟩ := walk_to_window (Ξ := Ξ) (α := α) (F := Work.Pert.liftF u σ α) (Φ := Φ)
    hNT.1 hΦ.2.2 hdec' hM hκ
  -- the upper-end asymptotics `Φ z = z + c + o(1)` of the gate coordinate
  obtain ⟨c, hc⟩ :=
    gate_coord_end_asymptotic_Qm hF hΞ hQAdm hNT hΦ ⟨M, κ, Yd, hM, hκ, hdec'⟩
  -- one uniform height threshold for each of the two real windows used below
  obtain ⟨Ye2, hYe2⟩ :=
    exists_threshold_re_bounded (Q := Work.Pert.Qm Ξ α) (Φ := Φ) (c := c) (B := 2) hc
  obtain ⟨YeB, hYeB⟩ :=
    exists_threshold_re_bounded (Q := Work.Pert.Qm Ξ α) (Φ := Φ) (c := c) (B := ‖c‖ + 3) hc
  -- the height gain for the preimage, and the cover threshold
  obtain ⟨Yg, hYg⟩ := im_gain_sym hF hΞ hQAdm hNT hΦ hcover
  obtain ⟨Ycov, _hΞYcov, _hcov'⟩ := hcover
  -- the height the preimage must reach
  set Msum : ℝ := max K (max (Ye2 + 2) (YeB + 1)) with hMsum
  have hKM : K ≤ Msum := by
    rw [hMsum]; exact le_max_left _ _
  have hYe2M : Ye2 + 2 ≤ Msum := by
    rw [hMsum]; exact le_trans (le_max_left _ _) (le_max_right _ _)
  have hYeBM : YeB + 1 ≤ Msum := by
    rw [hMsum]; exact le_trans (le_max_right _ _) (le_max_right _ _)
  -- the height threshold of the statement
  set Yc : ℝ := max Yg (max Ycov ((4 * Msum + 1 - Ξ) / 3)) with hYcdef
  have hYcYg : Yg ≤ Yc := by rw [hYcdef]; exact le_max_left _ _
  have hYcYcov : Ycov ≤ Yc := by
    rw [hYcdef]; exact le_trans (le_max_left _ _) (le_max_right _ _)
  have hYcthr : (4 * Msum + 1 - Ξ) / 3 ≤ Yc := by
    rw [hYcdef]; exact le_trans (le_max_right _ _) (le_max_right _ _)
  refine ⟨‖c‖ + 3, max 0 (c.im + 1), Yc, by positivity, le_max_left 0 _, ?_⟩
  intro w hwy hwre hwmem
  have hYg_le : Yg ≤ w.im := le_trans hYcYg hwy
  have hYcov_le : Ycov ≤ w.im := le_trans hYcYcov hwy
  have hthr : (4 * Msum + 1 - Ξ) / 3 ≤ w.im := le_trans hYcthr hwy
  -- the chosen gate preimage
  set ζ : ℂ := Work.Pert.invOn Φ (Work.Pert.Qm Ξ α) w with hζdef
  have hζQ : ζ ∈ Work.Pert.Qm Ξ α := Work.Pert.invOn_mem hwmem
  have hζΦ : Φ ζ = w := Work.Pert.invOn_spec hwmem
  -- it is high up, by the height gain
  have hζim : Msum ≤ ζ.im := by
    have hg : (3 * w.im + Ξ) / 4 - 1 / 32 ≤ ζ.im := by
      rw [hζdef]
      exact hYg w hYg_le hwre hwmem
    have h4 : Msum + 1 / 4 ≤ (3 * w.im + Ξ) / 4 := by linarith
    linarith
  -- the walk into the fixed real window `[-2,2]`
  obtain ⟨z', hz'Q, hz're, hz'im, hErr⟩ := hK ζ hζQ (le_trans hKM hζim)
  have hz'abs : |z'.re| ≤ 2 := abs_le.mpr hz're
  have hz'Ye : Ye2 < z'.im := by
    have h1 : Ye2 < ζ.im - 1 := by linarith
    linarith
  have hEnd := hYe2 z' hz'Q hz'Ye hz'abs
  -- the asymptotic transfers from the walked point `z'` back to the preimage `ζ`
  have hmain : ‖Φ ζ - ζ - c‖ ≤ 2 := by
    have hErr' : ‖Φ ζ - ζ - (Φ z' - z')‖ ≤ 1 := by rw [norm_sub_rev]; exact hErr
    have hid : Φ ζ - ζ - c = (Φ ζ - ζ - (Φ z' - z')) + (Φ z' - z' - c) := by ring
    rw [hid]
    exact le_trans (norm_add_le _ _) (by linarith [hErr', hEnd])
  have hrec : |(Φ ζ - ζ - c).re| ≤ 2 := le_trans (Complex.abs_re_le_norm _) hmain
  have hζre_eq : ζ.re = w.re - (Φ ζ - ζ - c).re - c.re := by
    have h1 : ζ.re = w.re - (Φ ζ - ζ).re := by
      rw [← hζΦ]; simp only [Complex.sub_re]; ring
    have h2 : (Φ ζ - ζ).re = (Φ ζ - ζ - c).re + c.re := by
      simp only [Complex.sub_re]; ring
    linarith
  -- the `Re`-bound
  have hre : |ζ.re| ≤ ‖c‖ + 3 := by
    calc |ζ.re| = |w.re - (Φ ζ - ζ - c).re - c.re| := by rw [hζre_eq]
      _ ≤ |w.re| + |(Φ ζ - ζ - c).re| + |c.re| := by
          have he : w.re - (Φ ζ - ζ - c).re - c.re
              = w.re + (-((Φ ζ - ζ - c).re)) + (-c.re) := by ring
          rw [he]
          refine le_trans (abs_add_three _ _ _) ?_
          rw [abs_neg, abs_neg]
      _ ≤ ‖c‖ + 3 := by linarith [hrec, Complex.abs_re_le_norm c, hwre]
  -- the second asymptotic, now at the preimage itself
  have hζYe : YeB < ζ.im := lt_of_lt_of_le (by linarith [hYeBM]) hζim
  have hAsym := hYeB ζ hζQ hζYe hre
  have hfin : w.im - (c.im + 1) < ζ.im := by
    have h := Complex.abs_im_le_norm (Φ ζ - ζ - c)
    have h2 : |(Φ ζ - ζ - c).im| < 1 := lt_of_le_of_lt h hAsym
    have h2' : (Φ ζ - ζ - c).im < 1 := (abs_lt.mp h2).2
    have him : (Φ ζ - ζ - c).im = w.im - ζ.im - c.im := by
      simp only [Complex.sub_im, hζΦ]
    rw [him] at h2'
    linarith
  refine ⟨hre, ?_⟩
  have hC : w.im - max 0 (c.im + 1) ≤ w.im - (c.im + 1) :=
    sub_le_sub_left (le_max_right (0 : ℝ) (c.im + 1)) w.im
  linarith

end

end Work.Pert.pert2v2
