import Mathlib
import Submission.Work.Pert.pert2v2.waist_cover_pinned_im_seg_low

/-!
# `Work.Pert.pert2v2.CoverHalf` — coverage of the half plane by the gate saturation

`NOTES_pert2v2_session30.md` §14.1, §16.1.  The `ℤ`-extension `Ef` of the horn map
`Φp ∘ Φm⁻¹` (and `pert2v2.end_const_le_seg`, whose `hper`/`hdiff`/`hlim` are stated on the half
plane) needs the gate image `Φm '' (Qm Ξ α)` to cover the half plane *modulo* `ℤ`:

  `∀ y, ∀ w, y ≤ w.im → ∃ n : ℤ, w - n ∈ Φm '' (Qm Ξ α)`.

The cover lemma `pert2v2.waist_cover_pinned_im_seg_low` gives, for every height `y₀` above its
threshold `Y`, a **fixed** integer `n` and a gate preimage of *every* point `x + i y₀` with
`x ∈ [0,1)`.  Shifting by the integer part of `w.re` turns this into the statement above with
`y := Y`.

The two lemmas below are the `hcov` (on a half plane) and `hcover`/`hcovAll` shapes consumed by
`pert2v2.Ef_add_one`, `pert2v2.Ef_sub_id_differentiableOn` and `pert2v2.Ef_tendsto_upperEnd`.
-/

namespace Work.Pert.pert2v2

open MandelDim Complex Set

noncomputable section

/-- **Coverage of the half plane modulo `ℤ`.**  If the cover lemma produces, at every height
`y₀ ≥ Y`, a *fixed* integer `n` and gate preimages of the whole unit window `x + i y₀`
(`x ∈ [0,1)`), then every point of height `≥ Y` is an integer translate of a gate value. -/
theorem exists_sub_mem_image_of_cover {Φ : ℂ → ℂ} {Q : Set ℂ} {Y : ℝ}
    (hcover : ∀ y₀ : ℝ, Y ≤ y₀ → ∃ n : ℤ, ∀ x ∈ Set.Ico (0 : ℝ) 1,
      (x : ℂ) + (y₀ : ℂ) * Complex.I + (n : ℂ) ∈ Φ '' Q) :
    ∀ y : ℝ, Y ≤ y → ∀ w : ℂ, y ≤ w.im → ∃ m : ℤ, w - (m : ℂ) ∈ Φ '' Q := by
  intro y hy w hw
  have him : Y ≤ w.im := le_trans hy hw
  obtain ⟨n, hn⟩ := hcover w.im him
  set k : ℤ := ⌊w.re⌋ with hk
  set x : ℝ := Int.fract w.re with hx
  have hxmem : x ∈ Set.Ico (0 : ℝ) 1 := ⟨Int.fract_nonneg w.re, Int.fract_lt_one w.re⟩
  have hxw : (x : ℂ) + (w.im : ℂ) * Complex.I + (n : ℂ)
      = w - (((k - n : ℤ)) : ℂ) := by
    have h1 : w.re = x + (k : ℝ) := by
      rw [hx, hk]
      have := Int.floor_add_fract w.re
      linarith
    have h2 : (x : ℂ) + (w.im : ℂ) * Complex.I
        = (((x + (k : ℝ)) : ℝ) : ℂ) + (w.im : ℂ) * Complex.I - ((k : ℤ) : ℂ) := by
      push_cast
      ring
    have h3 : ((w.re : ℝ) : ℂ) + (w.im : ℂ) * Complex.I = w := Complex.re_add_im w
    rw [h2, ← h1, h3]
    push_cast
    ring
  refine ⟨k - n, ?_⟩
  rw [← hxw]
  exact hn x hxmem

/-- **The segment cover in the `hcover` shape of `pert2v2.hseg_of_cover`.**  The cover lemma
`pert2v2.waist_cover_pinned_im_seg_low` produces, at every height `y₀` above its threshold, a
**fixed** integer `n` (in the proof: `n = 0`) and the gate preimages of the whole half-open window
`x + i y₀`, `x ∈ [0,1)`.  Here the input is the `n = 0` form (see `waist_cover_pinned_im_seg_low`,
whose proof ends with `refine ⟨0, ?_⟩`), and the conclusion is the pointwise-`n` form consumed by
`hseg_of_cover`: the endpoint `x = 1` is covered by the point `0 + i y₀` with the shift `-1`. -/
theorem cover_seg_pointwise {Φ : ℂ → ℂ} {Q : Set ℂ} {Y : ℝ}
    (hcover : ∀ y₀ : ℝ, Y ≤ y₀ → ∀ x ∈ Set.Ico (0 : ℝ) 1,
      (x : ℂ) + (y₀ : ℂ) * Complex.I ∈ Φ '' Q) :
    ∀ y₀ : ℝ, Y ≤ y₀ → ∀ x ∈ Set.Icc (0 : ℝ) 1, ∃ n : ℤ, |x + (n : ℝ)| < 1 ∧
      (x : ℂ) + (y₀ : ℂ) * Complex.I + (n : ℂ) ∈ Φ '' Q := by
  intro y₀ hy₀ x hx
  rcases lt_or_eq_of_le hx.2 with hx1 | hx1
  · refine ⟨0, by simpa using abs_lt.mpr ⟨by linarith [hx.1], hx1⟩, ?_⟩
    simpa using hcover y₀ hy₀ x ⟨hx.1, hx1⟩
  · -- `x = 1`: use the point `0 + i y₀` and the shift `-1`
    subst hx1
    refine ⟨-1, by norm_num, ?_⟩
    have h := hcover y₀ hy₀ 0 ⟨le_rfl, zero_lt_one⟩
    simpa using h

end

end Work.Pert.pert2v2
