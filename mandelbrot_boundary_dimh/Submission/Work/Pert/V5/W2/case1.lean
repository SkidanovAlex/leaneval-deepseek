import Mathlib
import Submission.Work.Pert.V5.W2.Setup
import Submission.Work.Pert.V5.W2.xiB_gt_edge
import Submission.Work.Pert.V5.corridor_piece_bound

/-!
# `Work.Pert.V5.W2.case1` — the *short* right corridor

This is the case `z.re - z₀.re ≤ 16 (M + 2 + Ξ)` of the right corridor (`z₀.re ≤ z.re`) at height
`y₀ = z₀.im`, with `x := z.re` a band abscissa and the pin `z₀` cleared
(`closedBall z₀ (2 Rde + 2) ⊆ Qm Ξ α`).  The conclusion is the certificate

`‖D (x + i y₀) - D z₀‖ ≤ (1/150 + 1/31) √2 Rde + P`, `P := C₂ 2^6 (1+Ξ) L + 2^24 (1+1/rr) Lg`,

i.e. **one** cleared piece (`hshort` is exactly the condition making the ceiling
`⌈ℓ/(16 (M + 2 + Ξ))⌉ = 1`) plus a window piece of length at most `√2 Rde`.

Write `ξ_B := |y₀| - Ξ - √2 Rde`, so that on the horizontal line at height `y₀` the `b₂`-margin is
`mgB = |y₀| - Ξ - ξ`, which is `≥ √2 Rde ⇔ ξ ≤ ξ_B`.

* **Case `z.re ≤ ξ_B`.**  On the whole corridor `[z₀.re, z.re]` both margins are `≥ √2 Rde`
  (`mgA` grows from `mgA z₀ > 2 Rde + 2`, `mgB` decays to `mgB (z.re + i y₀) ≥ √2 Rde`) and `≥ 1`
  (`mgA > 2 Rde + 2`, `mgB (z.re + i y₀) ≥ 2^10`).  The lattice clearance on the corridor follows
  from `hshort` (`|ξ| ≤ 20 (M + 2 + Ξ)`) and `ξ ≤ -(Ξ + 2^10)` via `clear_lattice_gate`.  So
  `corridor_piece_bound` gives `‖D (x + i y₀) - D z₀‖ ≤ P`, and the extra slot `c₀ √2 Rde ≥ 0` is
  free.
* **Case `ξ_B < z.re`.**  Then `ξ_B ∈ (z₀.re, z.re)` (the left inequality from `mgB z₀ > 2 Rde + 2`).
  Split the corridor at `ξ_B`: the left piece `[z₀.re, ξ_B]` again has margins `≥ √2 Rde` and `≥ 1`
  (note `√2 Rde > 2^10`, since `mgB (z.re + i y₀) ≥ 2^10` exceeds `mgB (ξ_B + i y₀) = √2 Rde`),
  so it costs one `P`; the right piece `[ξ_B, z.re]` lies in the window strip
  (`xiB_gt_edge`: `Ξ - (1/α).re + 1 < ξ_B`, and `ξ ≤ z.re ≤ -(Ξ + 2^10) < -Ξ - 3`), so
  `window_horiz_dev_le` prices it at `c₀ (z.re - ξ_B) = c₀ (√2 Rde - mgB (z.re + i y₀)) ≤ c₀ √2 Rde`.
  The triangle inequality through `ξ_B` finishes.
-/

namespace Work.Pert.V5.W2

open Set Metric Filter
open scoped _root_.Topology

noncomputable section

/-! ## Elementary arithmetic and the two structural inputs -/

/-- `√2 Rde ≤ 2 Rde + 2`. -/
private lemma sqrt2_mul_le_two_mul_add {Rde : ℝ} (hRde : 0 < Rde) :
    Real.sqrt 2 * Rde ≤ 2 * Rde + 2 := by
  have hs : Real.sqrt 2 ≤ 2 := by
    nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num), Real.sqrt_nonneg 2]
  nlinarith

/-- **Lattice clearance of a short corridor point.**  For `x` in
`[-(Ξ + 2^10 + 2M + 16 (M+2+Ξ)), -(Ξ + 2^10)]` (which is what `hshort` produces for the corridor
`[z₀.re, z.re]`) and any height `s`, the point `x + i s` is at distance `≥ 2^10` from the lattice
`(1/α)ℤ`, scaled by `‖α‖`.

Immediate from `clear_lattice_gate`: `|x| ≤ 20 (M + 2 + Ξ)` because
`17Ξ + 18M + 2^10 + 32 ≤ 20 (M + 2 + Ξ)`, and `‖x + i s‖ ≥ |x| ≥ Ξ + 2^10 ≥ 2^10`. -/
private lemma case1_clear {Ξ M : ℝ} {α : ℂ} {x s : ℝ}
    (hΞ : 0 < Ξ) (hM : 2 ^ 10 ≤ M) (hInF1 : MandelDim.InF1 α)
    (hα : ‖α‖ ≤ 1 / (32 * (M + 2 + Ξ)))
    (hxl : -(Ξ + 2 ^ 10 + 2 * M + 16 * (M + 2 + Ξ)) ≤ x)
    (hxr : x ≤ -(Ξ + 2 ^ 10)) :
    ∀ k : ℤ, ‖α‖ * 2 ^ 10 ≤ ‖α * ((x : ℂ) + (s : ℂ) * Complex.I) - (k : ℂ)‖ := by
  have hwr : |((x : ℂ) + (s : ℂ) * Complex.I).re| ≤ 20 * (M + 2 + Ξ) := by
    rw [re_of_re_im, abs_of_nonpos (by linarith)]
    nlinarith [hxl, hM, hΞ]
  have hlow : 2 ^ 10 ≤ ‖((x : ℂ) + (s : ℂ) * Complex.I)‖ := by
    have h1 := Complex.abs_re_le_norm ((x : ℂ) + (s : ℂ) * Complex.I)
    rw [re_of_re_im, abs_of_nonpos (by linarith)] at h1
    linarith
  exact clear_lattice_gate hΞ hM hInF1 hα hwr hlow

/-- **Margins on a cleared sub-corridor.**  If `ξ` lies between `z₀.re` and some `b ≤ z.re` with
`b ≤ ξ_B := |z₀.im| - Ξ - √2 Rde` then the point `ξ + i z₀.im` has both margins `≥ √2 Rde` and
`≥ 1`, hence lies in the gate.  (The `≥ 1` part uses `hξb, hbz, hzhi` to get `mgB ≥ 2^10`.) -/
private lemma case1_margins {Ξ Rde : ℝ} {α : ℂ} {z₀ z : ℂ} {b ξ : ℝ}
    (hRde : 0 < Rde)
    (hcl : Metric.closedBall z₀ (2 * Rde + 2) ⊆ Work.Pert.Qm Ξ α)
    (hzhi : z.re ≤ -(Ξ + 2 ^ 10))
    (hbz : b ≤ z.re) (hbξ : b ≤ |z₀.im| - Ξ - Real.sqrt 2 * Rde)
    (hξ₀ : z₀.re ≤ ξ) (hξb : ξ ≤ b) :
    Real.sqrt 2 * Rde ≤ min (Work.Pert.V5.mgA Ξ α ((ξ : ℂ) + (z₀.im : ℂ) * Complex.I))
                            (Work.Pert.V5.mgB Ξ ((ξ : ℂ) + (z₀.im : ℂ) * Complex.I))
      ∧ 1 ≤ min (Work.Pert.V5.mgA Ξ α ((ξ : ℂ) + (z₀.im : ℂ) * Complex.I))
                (Work.Pert.V5.mgB Ξ ((ξ : ℂ) + (z₀.im : ℂ) * Complex.I))
      ∧ ((ξ : ℂ) + (z₀.im : ℂ) * Complex.I) ∈ Work.Pert.Qm Ξ α := by
  have hq₀ : ((z₀.re : ℂ) + (z₀.im : ℂ) * Complex.I) = z₀ := Complex.re_add_im z₀
  have hmA : 2 * Rde + 2 < z₀.re - Ξ + (1 / α).re + |z₀.im + (1 / α).im| := by
    have h := (zo_margins hRde hcl).1
    rw [← hq₀] at h
    rwa [Work.Pert.V5.mgA_re_im] at h
  have hmB : 2 * Rde + 2 < |z₀.im| - Ξ - z₀.re := by
    have h := (zo_margins hRde hcl).2
    rw [← hq₀] at h
    rwa [Work.Pert.V5.mgB_re_im] at h
  have hsq2 : Real.sqrt 2 * Rde ≤ 2 * Rde + 2 := sqrt2_mul_le_two_mul_add hRde
  have hAξ : Work.Pert.V5.mgA Ξ α ((ξ : ℂ) + (z₀.im : ℂ) * Complex.I)
      = ξ - Ξ + (1 / α).re + |z₀.im + (1 / α).im| := Work.Pert.V5.mgA_re_im Ξ α ξ z₀.im
  have hBξ : Work.Pert.V5.mgB Ξ ((ξ : ℂ) + (z₀.im : ℂ) * Complex.I)
      = |z₀.im| - Ξ - ξ := Work.Pert.V5.mgB_re_im Ξ ξ z₀.im
  have hB10 : 2 ^ 10 ≤ |z₀.im| - Ξ - ξ := by
    have h1 : ξ ≤ -(Ξ + 2 ^ 10) := le_trans (le_trans hξb hbz) hzhi
    have h2 : (0 : ℝ) ≤ |z₀.im| := abs_nonneg _
    linarith
  have hBsq : Real.sqrt 2 * Rde ≤ |z₀.im| - Ξ - ξ := by
    have h1 : |z₀.im| - Ξ - b ≤ |z₀.im| - Ξ - ξ := by linarith
    linarith
  refine ⟨?_, ?_, ?_⟩
  · rw [hAξ, hBξ]
    exact le_min (by linarith) hBsq
  · rw [hAξ, hBξ]
    exact le_min (by linarith) (by linarith)
  · rw [Work.Pert.V5.mem_Qm_iff_mg, hAξ, hBξ]
    exact ⟨by linarith, by linarith⟩

/-! ## The theorem -/

theorem case1 {Ξ rr M Kp Rde C₂ : ℝ} {α σ : ℂ} {u Φm : ℂ → ℂ} {z₀ : ℂ}
    (hF : MandelDim.FatouStatement)
    (hΞ : 0 < Ξ) (hrr : 0 < rr) (hM : 2 ^ 10 ≤ M) (hKp : 0 ≤ Kp)
    (hRde : 0 < Rde) (hC₂ : 0 < C₂)
    (hInF1 : MandelDim.InF1 α) (hα : ‖α‖ ≤ 1 / (32 * (M + 2 + Ξ)))
    (hQAdm : MandelDim.QAdm (some ((Ξ : ℂ) - 1 / α)) (some (-(Ξ : ℂ))))
    (hσ : σ ≠ 0) (hnorm : 1 - σ * u 0 = Complex.exp (2 * Real.pi * Complex.I * α))
    (hu : DifferentiableOn ℂ u (Metric.ball (0 : ℂ) rr))
    (hu2 : ∀ z ∈ Metric.ball (0 : ℂ) rr, 1 / 2 ≤ ‖u z‖ ∧ ‖u z‖ ≤ 2)
    (hτQ : ∀ z ∈ Work.Pert.Qm Ξ α, Work.Pert.tauC σ α z ∈ Metric.ball (0 : ℂ) rr)
    (hDE : ∀ (Φ v : ℂ → ℂ) (z : ℂ) (R : ℝ), Rde ≤ R →
      DifferentiableOn ℂ Φ (Metric.ball z R) → Set.InjOn Φ (Metric.ball z R) →
      DifferentiableOn ℂ v (Metric.ball z R) → (∀ w ∈ Metric.ball z R, ‖v w - 1‖ < 1 / 4) →
      (∀ w ∈ Metric.ball z R, w + v w ∈ Metric.ball z R → Φ (w + v w) = Φ w + 1) →
      ‖deriv Φ z - 1 / v z‖ ≤ C₂ / R)
    (hNT : MandelDim.NearTranslationL1 (Work.Pert.liftF u σ α) (Work.Pert.Qm Ξ α))
    (hΦm : MandelDim.IsFatouCoordOn (Work.Pert.liftF u σ α) Φm (Work.Pert.Qm Ξ α))
    (hz₀ : z₀ ∈ Work.Pert.Qm Ξ α)
    (hcl : Metric.closedBall z₀ (2 * Rde + 2) ⊆ Work.Pert.Qm Ξ α)
    (hpinbd : ‖z₀ + (((M : ℝ)) : ℂ)‖ ≤ Kp * (1 + Real.log (2 + M)))
    {z : ℂ} (hz : z ∈ Work.Pert.Qm Ξ α)
    (hzlo : -(Ξ + 2 ^ 10 + 2 * M) ≤ z.re) (hzhi : z.re ≤ -(Ξ + 2 ^ 10))
    (ht : 4 * Rde ≤ |z.im|) (hcase : z₀.re ≤ z.re)
    (hshort : z.re - z₀.re ≤ 16 * (M + 2 + Ξ)) :
    ‖(Φm ((z.re : ℂ) + (z₀.im : ℂ) * Complex.I) - ((z.re : ℂ) + (z₀.im : ℂ) * Complex.I))
        - (Φm z₀ - z₀)‖
      ≤ (1 / 150 + 1 / 31) * Real.sqrt 2 * Rde
        + (C₂ * 2 ^ 6 * (1 + Ξ) * (1 + Real.log (2 + M))
            + 2 ^ 24 * (1 + 1 / rr) * (1 + Real.log (2 + 16 * (M + 2 + Ξ)))) := by
  have hc0nn : (0 : ℝ) ≤ 1 / 150 + 1 / 31 := by norm_num
  have hq₀ : ((z₀.re : ℂ) + (z₀.im : ℂ) * Complex.I) = z₀ := Complex.re_add_im z₀
  -- the `b₂`-margin at the band abscissa exceeds `2^10` (this uses only `hzhi`)
  have hqB : 2 ^ 10 ≤ mgB Ξ ((z.re : ℂ) + (z₀.im : ℂ) * Complex.I) := by
    rw [mgB_re_im]
    have h1 : (0 : ℝ) ≤ |z₀.im| := abs_nonneg _
    linarith
  -- the lattice clearance along the whole corridor
  have hclr : ∀ ξ ∈ Set.Icc z₀.re z.re, ∀ k : ℤ,
      ‖α‖ * 2 ^ 10 ≤ ‖α * ((ξ : ℂ) + (z₀.im : ℂ) * Complex.I) - (k : ℂ)‖ := by
    intro ξ hξ k
    exact case1_clear hΞ hM hInF1 hα (by linarith [hξ.1, hzlo, hshort])
      (by linarith [hξ.2, hzhi]) k
  by_cases hA : z.re ≤ |z₀.im| - Ξ - Real.sqrt 2 * Rde
  · -- ## Case A: the whole corridor is cleared
    have hmarg := fun ξ (hξ : ξ ∈ Set.Icc z₀.re z.re) =>
      case1_margins (z := z) (b := z.re) hRde hcl hzhi le_rfl hA hξ.1 hξ.2
    have hlo : ∀ ξ ∈ Set.Icc z₀.re z.re,
        Real.sqrt 2 * Rde ≤ min (mgA Ξ α ((ξ : ℂ) + (z₀.im : ℂ) * Complex.I))
                                (mgB Ξ ((ξ : ℂ) + (z₀.im : ℂ) * Complex.I)) :=
      fun ξ hξ => (hmarg ξ hξ).1
    have hpos : ∀ ξ ∈ Set.Icc z₀.re z.re,
        1 ≤ min (mgA Ξ α ((ξ : ℂ) + (z₀.im : ℂ) * Complex.I))
                (mgB Ξ ((ξ : ℂ) + (z₀.im : ℂ) * Complex.I)) :=
      fun ξ hξ => (hmarg ξ hξ).2.1
    have hgate : ∀ ξ ∈ Set.Icc z₀.re z.re,
        ((ξ : ℂ) + (z₀.im : ℂ) * Complex.I) ∈ Work.Pert.Qm Ξ α :=
      fun ξ hξ => (hmarg ξ hξ).2.2
    have hpiece := corridor_piece_bound (Ξ := Ξ) (rr := rr) (M := M) (Rde := Rde) (C₂ := C₂)
      (α := α) (σ := σ) (u := u) (Φm := Φm) (s := z₀.im) (x := z₀.re) (y := z.re)
      hΞ hrr hM hRde hC₂ hInF1 hα hσ hnorm hu hu2 hτQ hDE hNT hΦm hcase hshort hgate hclr hlo hpos
    have hfin : ‖(Φm ((z.re : ℂ) + (z₀.im : ℂ) * Complex.I) - ((z.re : ℂ) + (z₀.im : ℂ) * Complex.I))
        - (Φm ((z₀.re : ℂ) + (z₀.im : ℂ) * Complex.I) - ((z₀.re : ℂ) + (z₀.im : ℂ) * Complex.I))‖
        ≤ (1 / 150 + 1 / 31) * Real.sqrt 2 * Rde
          + (C₂ * 2 ^ 6 * (1 + Ξ) * (1 + Real.log (2 + M))
              + 2 ^ 24 * (1 + 1 / rr) * (1 + Real.log (2 + 16 * (M + 2 + Ξ)))) := by
      have hnn : (0 : ℝ) ≤ (1 / 150 + 1 / 31) * Real.sqrt 2 * Rde := by positivity
      linarith [hpiece]
    simpa [hq₀] using hfin
  · -- ## Case B: split the corridor at `ξ_B`
    have hB : |z₀.im| - Ξ - Real.sqrt 2 * Rde < z.re := not_le.mp hA
    have hsq2 : Real.sqrt 2 * Rde ≤ 2 * Rde + 2 := sqrt2_mul_le_two_mul_add hRde
    -- `ξ_B` lies strictly inside the corridor
    have hx₀ξB : z₀.re < |z₀.im| - Ξ - Real.sqrt 2 * Rde := by
      have h := (zo_margins hRde hcl).2
      rw [← hq₀, mgB_re_im] at h
      linarith
    -- `mgB (z.re + i y₀) ≥ 2^10` forces `√2 Rde > 2^10`
    have hbig : 2 ^ 10 < Real.sqrt 2 * Rde := by
      have h : mgB Ξ ((z.re : ℂ) + (z₀.im : ℂ) * Complex.I) < Real.sqrt 2 * Rde := by
        rw [mgB_re_im]
        linarith
      linarith
    -- the cleared piece `[z₀.re, ξ_B]`
    have hmarg1 := fun ξ (hξ : ξ ∈ Set.Icc z₀.re (|z₀.im| - Ξ - Real.sqrt 2 * Rde)) =>
      case1_margins (z := z) (b := |z₀.im| - Ξ - Real.sqrt 2 * Rde) hRde hcl hzhi
        (le_of_lt hB) le_rfl hξ.1 hξ.2
    have hgate1 : ∀ ξ ∈ Set.Icc z₀.re (|z₀.im| - Ξ - Real.sqrt 2 * Rde),
        ((ξ : ℂ) + (z₀.im : ℂ) * Complex.I) ∈ Work.Pert.Qm Ξ α :=
      fun ξ hξ => (hmarg1 ξ hξ).2.2
    have hlo1 : ∀ ξ ∈ Set.Icc z₀.re (|z₀.im| - Ξ - Real.sqrt 2 * Rde),
        Real.sqrt 2 * Rde ≤ min (mgA Ξ α ((ξ : ℂ) + (z₀.im : ℂ) * Complex.I))
                                (mgB Ξ ((ξ : ℂ) + (z₀.im : ℂ) * Complex.I)) :=
      fun ξ hξ => (hmarg1 ξ hξ).1
    have hpos1 : ∀ ξ ∈ Set.Icc z₀.re (|z₀.im| - Ξ - Real.sqrt 2 * Rde),
        1 ≤ min (mgA Ξ α ((ξ : ℂ) + (z₀.im : ℂ) * Complex.I))
                (mgB Ξ ((ξ : ℂ) + (z₀.im : ℂ) * Complex.I)) :=
      fun ξ hξ => (hmarg1 ξ hξ).2.1
    have hclear1 : ∀ ξ ∈ Set.Icc z₀.re (|z₀.im| - Ξ - Real.sqrt 2 * Rde), ∀ k : ℤ,
        ‖α‖ * 2 ^ 10 ≤ ‖α * ((ξ : ℂ) + (z₀.im : ℂ) * Complex.I) - (k : ℂ)‖ :=
      fun ξ hξ k => hclr ξ ⟨hξ.1, le_trans hξ.2 (le_of_lt hB)⟩ k
    have hlen1 : (|z₀.im| - Ξ - Real.sqrt 2 * Rde) - z₀.re ≤ 16 * (M + 2 + Ξ) := by
      linarith [hB, hshort]
    have hpiece1 := corridor_piece_bound (Ξ := Ξ) (rr := rr) (M := M) (Rde := Rde) (C₂ := C₂)
      (α := α) (σ := σ) (u := u) (Φm := Φm) (s := z₀.im) (x := z₀.re)
      (y := |z₀.im| - Ξ - Real.sqrt 2 * Rde)
      hΞ hrr hM hRde hC₂ hInF1 hα hσ hnorm hu hu2 hτQ hDE hNT hΦm (le_of_lt hx₀ξB) hlen1
      hgate1 hclear1 hlo1 hpos1
    -- the window piece `[ξ_B, z.re]`
    have hedge := xiB_gt_edge (Ξ := Ξ) (M := M) (Rde := Rde) (α := α) (z₀ := z₀)
      hΞ hM hInF1 hα hRde hcl
    have hseg2 : ∀ ξ ∈ Set.Icc (|z₀.im| - Ξ - Real.sqrt 2 * Rde) z.re,
        ((ξ : ℂ) + (z₀.im : ℂ) * Complex.I) ∈ Work.Pert.Qm Ξ α := by
      intro ξ hξ
      refine Work.Pert.V5.mem_Qm_iff_mg.mpr ⟨?_, ?_⟩
      · rw [Work.Pert.V5.mgA_re_im]
        have h1 : ((Ξ : ℂ) - 1 / α).re + 1 < ξ := lt_of_lt_of_le hedge hξ.1
        have hre : ((Ξ : ℂ) - 1 / α).re = Ξ - (1 / α).re := by
          rw [Complex.sub_re, Complex.ofReal_re]
        rw [hre] at h1
        have him : (0 : ℝ) ≤ |z₀.im + (1 / α).im| := abs_nonneg _
        linarith
      · rw [Work.Pert.V5.mgB_re_im]
        have him : (0 : ℝ) ≤ |z₀.im| := abs_nonneg _
        linarith [hξ.2, hzhi]
    have hwin2 : ∀ ξ ∈ Set.Icc (|z₀.im| - Ξ - Real.sqrt 2 * Rde) z.re,
        ((Ξ : ℂ) - 1 / α).re + 1 < ξ ∧ ξ < -Ξ - 3 := by
      intro ξ hξ
      refine ⟨lt_of_lt_of_le hedge hξ.1, ?_⟩
      have h210 : (3 : ℝ) < 2 ^ 10 := by norm_num
      linarith [hξ.2, hzhi, h210]
    have hpiece2 := window_horiz_dev_le (Ξ := Ξ) (α := α) (σ := σ) (u := u) (Φm := Φm)
      (s := z₀.im) (a := |z₀.im| - Ξ - Real.sqrt 2 * Rde) (b := z.re)
      hF hQAdm hNT hΦm hseg2 hwin2 (le_of_lt hB)
    -- the window cost and the triangle inequality through `ξ_B`
    have hwcost : (1 / 150 + 1 / 31) * (z.re - (|z₀.im| - Ξ - Real.sqrt 2 * Rde))
        ≤ (1 / 150 + 1 / 31) * Real.sqrt 2 * Rde := by
      have hlenB : z.re - (|z₀.im| - Ξ - Real.sqrt 2 * Rde) ≤ Real.sqrt 2 * Rde := by
        have h := hqB
        rw [mgB_re_im] at h
        linarith
      calc (1 / 150 + 1 / 31) * (z.re - (|z₀.im| - Ξ - Real.sqrt 2 * Rde))
          ≤ (1 / 150 + 1 / 31) * (Real.sqrt 2 * Rde) :=
            mul_le_mul_of_nonneg_left hlenB hc0nn
        _ = (1 / 150 + 1 / 31) * Real.sqrt 2 * Rde := by ring
    have htot : ‖(Φm ((z.re : ℂ) + (z₀.im : ℂ) * Complex.I) - ((z.re : ℂ) + (z₀.im : ℂ) * Complex.I))
        - (Φm ((z₀.re : ℂ) + (z₀.im : ℂ) * Complex.I) - ((z₀.re : ℂ) + (z₀.im : ℂ) * Complex.I))‖
        ≤ (1 / 150 + 1 / 31) * Real.sqrt 2 * Rde
          + (C₂ * 2 ^ 6 * (1 + Ξ) * (1 + Real.log (2 + M))
              + 2 ^ 24 * (1 + 1 / rr) * (1 + Real.log (2 + 16 * (M + 2 + Ξ)))) := by
      have htri := dist_triangle
        (Φm ((z.re : ℂ) + (z₀.im : ℂ) * Complex.I) - ((z.re : ℂ) + (z₀.im : ℂ) * Complex.I))
        (Φm (((|z₀.im| - Ξ - Real.sqrt 2 * Rde : ℝ) : ℂ) + (z₀.im : ℂ) * Complex.I)
          - (((|z₀.im| - Ξ - Real.sqrt 2 * Rde : ℝ) : ℂ) + (z₀.im : ℂ) * Complex.I))
        (Φm ((z₀.re : ℂ) + (z₀.im : ℂ) * Complex.I) - ((z₀.re : ℂ) + (z₀.im : ℂ) * Complex.I))
      rw [dist_eq_norm, dist_eq_norm, dist_eq_norm] at htri
      linarith [htri, hpiece1, hpiece2, hwcost]
    simpa [hq₀] using htot

end

end Work.Pert.V5.W2
