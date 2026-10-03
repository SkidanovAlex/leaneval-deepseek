import Mathlib
import Submission.Work.Pert.Gates

/-!
# PERT · `Work.Pert.waist_low`

The geometry that pins the **domain** of the paper's return map `R̃_f = Φ₋,f ∘ T_f ∘ Φ₋,f⁻¹`
(A.4) — the object that `PertData.R` must be — and the elementary sector fact that decides
**which** points of the `PertData.orbit` quantifier are live.

## 1. The waist is empty below height `Ξ`

`Φ₋,f` is a Fatou coordinate on the gate `Qm Ξ α` only, so the composition
`Φ₋ ∘ Tt α ∘ Φ₋⁻¹` makes sense only on the *waist*
`{z | z ∈ Qm Ξ α ∧ Tt α z ∈ Qm Ξ α} = Qm Ξ α ∩ Qp Ξ α`
(`Tt_mem_Qm_iff`), and `Qm_inter_Qp` says that equals `{z | |z.re| < |z.im| - Ξ}` — i.e. the waist
is confined to heights `> Ξ`.  The gate parameter `Ξ` is *not* free: the pointwise `1/32`
near-translation of `F_f = liftF u σ α` on `Qm Ξ α` requires the gate to stay at distance `≳ 32`
from the lattice `(1/α)ℤ` (`Work.Pert.scale_lattice`: membership gives `dist ≥ Ξ/2`; the defect
`F_f z - (z+1)` is `≈ C / dist (z, (1/α)ℤ)`), so `Ξ ≳ 64` in every application.  Hence the natural
domain of the return map is `{|Im| ≳ Ξ}` with `Ξ ≳ 64`, while `PertData.DR_sub` demands
`{w | y₁ ≤ |w.im|} ⊆ DR` for **every** `y₁ > d.η₀`, and `d.η₀` is a free field of `ParabData`
(`Work.Parab.coordData` produces `η₀ = max ηb 1 ≥ 1`).  The two demands cannot be met
simultaneously by the paper's `R̃_f`; this is the contract discrepancy recorded in
`NOTES_pert2_session18.md`.

## 2. The sector condition

`PertData.orbit` fires only for pairs with `|arg (w' + 1/(2α) - w)| < 2π/3`.  We record that this
condition is *automatically* satisfied by the candidate that the strip produces: the integer `j`
that puts `Re (R w + j)` in the unit window simultaneously puts `R w + j + 1/(2α) - w` into the
half plane `Re > 0`, hence into the sector `|arg| < π/2 < 2π/3`.  So the quantifier of `orbit` is
never vacuous at the heights that `DR_sub` reaches down to.
-/

namespace Work.Pert

open Complex Set

noncomputable section

/-! ## 1. `InF1` inversion and the waist geometry -/

/-- `𝓕₁` is preserved by inversion, **strictly**: `|Im (1/α)| < Re (1/α)`.  (The version on disk,
`Work.Pert.abs_im_one_div_le_re_one_div`, loses strictness; `Qm_inter_Qp` needs the strict form.) -/
theorem abs_im_one_div_lt_re_one_div {α : ℂ} (hα : MandelDim.InF1 α) :
    |(1 / α).im| < (1 / α).re := by
  have hαre : 0 < α.re := lt_of_le_of_lt (abs_nonneg α.im) hα
  have hαne : α ≠ 0 := by intro h; rw [h] at hαre; simp at hαre
  have hnsq : 0 < Complex.normSq α := Complex.normSq_pos.mpr hαne
  have hx : (1 / α).re = α.re / Complex.normSq α := by rw [one_div, Complex.inv_re]
  have hy : (1 / α).im = -α.im / Complex.normSq α := by rw [one_div, Complex.inv_im]
  rw [hy, hx, abs_div, abs_neg, abs_of_pos hnsq]
  exact div_lt_div_of_pos_right hα hnsq

/-- **The waist of the gate is the symmetric window** `{|Re z| < |Im z| - Ξ}`. -/
theorem mem_waist_iff {Ξ : ℝ} {α z : ℂ} (hF1 : |(1 / α).im| < (1 / α).re) :
    (z ∈ Qm Ξ α ∧ Tt α z ∈ Qm Ξ α) ↔ |z.re| < |z.im| - Ξ := by
  rw [Tt_mem_Qm_iff, ← Set.mem_inter_iff, Qm_inter_Qp hF1]
  rfl

/-- **The waist lives above height `Ξ`**: a point `z` with both `z` and `Tt α z` in the gate
satisfies `Ξ < |z.im|`. -/
theorem im_gt_of_mem_waist {Ξ : ℝ} {α z : ℂ} (hF1 : |(1 / α).im| < (1 / α).re)
    (hz : z ∈ Qm Ξ α) (hTz : Tt α z ∈ Qm Ξ α) : Ξ < |z.im| := by
  have h := (mem_waist_iff hF1).mp ⟨hz, hTz⟩
  have := abs_nonneg z.re
  linarith

/-- Contrapositive form: no point of height `≤ Ξ` is in the waist.  In particular the return map
`Φ₋ ∘ Tt α ∘ Φ₋⁻¹` — the only `φ`-invariant candidate for `PertData.R` — has a domain confined to
`{|Im| > Ξ}`. -/
theorem not_mem_waist_of_im_le {Ξ : ℝ} {α z : ℂ} (hF1 : |(1 / α).im| < (1 / α).re)
    (h : |z.im| ≤ Ξ) : ¬ (z ∈ Qm Ξ α ∧ Tt α z ∈ Qm Ξ α) := by
  rintro hz
  have := im_gt_of_mem_waist hF1 hz.1 hz.2
  linarith

/-- At a nonnegative gate parameter the waist avoids the real axis. -/
theorem im_pos_of_mem_waist {Ξ : ℝ} {α z : ℂ} (hΞ : 0 ≤ Ξ)
    (hF1 : |(1 / α).im| < (1 / α).re) (hz : z ∈ Qm Ξ α) (hTz : Tt α z ∈ Qm Ξ α) :
    0 < |z.im| := by
  have := im_gt_of_mem_waist hF1 hz hTz
  linarith

/-! ## 2. The sector condition of `PertData.orbit` -/

/-- If `Re u ≥ 0` then `|arg u| ≤ π/2 < 2π/3`.  This is the sector bound of `PertData.orbit`. -/
theorem arg_lt_two_thirds_of_re_nonneg {u : ℂ} (hu : 0 ≤ u.re) :
    |Complex.arg u| < 2 * Real.pi / 3 := by
  have h : |Complex.arg u| ≤ Real.pi / 2 := Complex.abs_arg_le_pi_div_two_iff.mpr hu
  linarith [Real.pi_pos]

/-- **The strip candidate satisfies the angle condition of `orbit`.**  For any `Rw` (the value of
the return map at `w`) and any `w` in the unit Re-window, provided `Re (1/α) ≥ 4`, some integer
shift `j` simultaneously

* puts `Re (Rw + j)` into the unit window `[-1,1]` (membership of `w'` in the strip that
  `PertData.Dφ_strip` and `PertData.DR_sub` force into the domains), and
* puts `u := Rw + j + 1/(2α) - w` into the sector `|arg u| < 2π/3` of `PertData.orbit`.

Indeed `u.re = (Rw + j).re + Re (1/(2α)) - w.re ≥ -1/2 + Re (1/α)/2 - 1 > 0`.  In particular the
`orbit` quantifier is never vacuous on a point of the band, *irrespective* of the size of `Rw`: the
shift is what saves the sector, and the near-translation threshold of §1 is what kills the domain. -/
theorem exists_int_shift_angle {α Rw w : ℂ} (hA : 4 ≤ (1 / α).re) (hwre : |w.re| ≤ 1) :
    ∃ j : ℤ, |(Rw + (j : ℂ)).re| ≤ 1 ∧
      |Complex.arg (Rw + (j : ℂ) + 1 / (2 * α) - w)| < 2 * Real.pi / 3 := by
  -- the integer nearest `-Re Rw`
  obtain ⟨j, hj⟩ : ∃ j : ℤ, |(j : ℝ) + Rw.re| ≤ 1 / 2 := by
    refine ⟨⌊-Rw.re + 1 / 2⌋, ?_⟩
    have h1 := Int.floor_le (-Rw.re + 1 / 2)
    have h2 := Int.lt_floor_add_one (-Rw.re + 1 / 2)
    rw [abs_le]; constructor <;> linarith
  have hjc : ((j : ℂ)).re = (j : ℝ) := Complex.intCast_re j
  have hstrip : |(Rw + (j : ℂ)).re| ≤ 1 := by
    have hsplit : (Rw + (j : ℂ)).re = Rw.re + (j : ℝ) := by
      simp only [Complex.add_re, hjc]
    rw [hsplit, abs_le]
    have h := abs_le.mp hj
    constructor <;> linarith [h.1, h.2]
  refine ⟨j, hstrip, arg_lt_two_thirds_of_re_nonneg ?_⟩
  -- the half plane `Re > 0`
  have hαne : α ≠ 0 := by
    rintro rfl
    norm_num at hA
  have hhalf : (1 / (2 * α) : ℂ) = ((1 / 2 : ℝ) : ℂ) * (1 / α) := by
    field_simp
    norm_num
  have hhalf_re : (1 / (2 * α) : ℂ).re = (1 / α).re / 2 := by
    rw [hhalf, Complex.re_ofReal_mul]
    ring
  have hsplit : (Rw + (j : ℂ) + 1 / (2 * α) - w).re
      = Rw.re + (j : ℝ) + (1 / α).re / 2 - w.re := by
    simp only [Complex.add_re, Complex.sub_re, hjc, hhalf_re]
  rw [hsplit]
  have h1 : -(1 / 2 : ℝ) ≤ Rw.re + (j : ℝ) := by
    have h := abs_le.mp hj
    linarith [h.1]
  have h2 : w.re ≤ 1 := (abs_le.mp hwre).2
  have hA2 : (2 : ℝ) ≤ (1 / α).re / 2 := by linarith
  linarith only [h1, h2, hA2]

end

end Work.Pert
