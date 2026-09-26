import Mathlib
import Submission.Work.Drive.Mono.Residual

namespace Work.Drive.Mono

open LeanEval.KnotTheory.PardonDistortion

/-- At every crux configuration of the tilted sweep there are tilt data — a unit direction `v`, half-widths `h`, a radius bound `R`, a wall functional `ℓ` with `ℓ ≠ 0` and `ℓ v = 0`, window ends `lam0 < lam1` and a finite exceptional set `exc` — satisfying `Work.Drive.Mono.TiltData`: the genericity of the sweep height on the surface (`Work.Drive.Final.TiltedGenericity`), the size conditions and the window conditions.  The genericity part is the *proved* `Work.Drive.EpsForm.tiltedSweepGenericity_holds_sized` (called with `ε = 1`), which already delivers `ℓ ≠ 0` and `ℓ v = 0`; the remaining content of this statement is the bookkeeping of the window ends and of the exceptional set, exactly as in the proved `Work.Drive.Final.tiltedGenericity_data_exists` — whose conclusion however drops `ℓ ≠ 0` and `ℓ v = 0`, so the data must be re-derived from the sized genericity statement directly (it is a near-verbatim reuse, with the two extra conjuncts kept).  Note `hs : 0 < s` follows from `hr : 0 < r` and `hrs : r < s`, which is the only side condition the template needs. -/
theorem DataExists_holds : Work.Drive.Mono.DataExists := by
  intro p q hp hq hcperm ψ K d hd hd1 himg hsmall hcl r hr c σ hbox s hrs hs hslice u hu
    hS hU hbound
  have hs0 : 0 < s := lt_trans hr hrs
  obtain ⟨v, h, ℓ, exc, R, hv1, hve, hvℓ, hℓne, hRbox, hεR, c1, c2, c3, c4⟩ :=
    Work.Drive.EpsForm.tiltedSweepGenericity_holds_sized ψ s c σ u 1 (by norm_num)
  have hc : c ∈ Submission.PBox s c σ := by
    rw [Submission.mem_PBox]
    intro i
    rw [sub_self, abs_zero]
    exact mul_pos (Submission.boxSide_pos i) hs0
  have hR0 : 0 ≤ R := by simpa using hRbox c hc
  have hεR' : R < h := by simpa using hεR
  have hh : 0 < h := lt_of_le_of_lt hR0 hεR'
  have hsize : ‖v - Work.BoxShrink.shiftVσ σ 1‖ * R < h := by
    have h1 : ‖v - Work.BoxShrink.shiftVσ σ 1‖ * R ≤ 1 * R :=
      mul_le_mul_of_nonneg_right hve hR0
    rw [one_mul] at h1
    linarith
  -- bounds on `ℓ` over the box and on the elements of `exc`
  set q : ℝ := |ℓ c| + ‖ℓ‖ * R + 1 with hq
  have hq1 : 1 ≤ q := by rw [hq]; nlinarith [abs_nonneg (ℓ c), norm_nonneg ℓ, hR0]
  have hℓy : ∀ y ∈ Submission.PBox s c σ, |ℓ y| ≤ q - 1 := by
    intro y hy
    have h1 : ‖y - c‖ ≤ R := hRbox y hy
    have h2 : ℓ y - ℓ c = ℓ (y - c) := by rw [map_sub]
    have h3 : |ℓ (y - c)| ≤ ‖ℓ‖ * ‖y - c‖ := by
      have := ContinuousLinearMap.le_opNorm ℓ (y - c)
      rwa [Real.norm_eq_abs] at this
    have h4 : |ℓ y| ≤ |ℓ y - ℓ c| + |ℓ c| := by
      have h5 : ℓ y = (ℓ y - ℓ c) + ℓ c := by ring
      calc |ℓ y| = |(ℓ y - ℓ c) + ℓ c| := congrArg (fun t : ℝ => |t|) h5
        _ ≤ |ℓ y - ℓ c| + |ℓ c| := abs_add_le _ _
    rw [h2] at h4
    have h6 : ‖ℓ‖ * ‖y - c‖ ≤ ‖ℓ‖ * R := mul_le_mul_of_nonneg_left h1 (norm_nonneg _)
    have : |ℓ y| ≤ ‖ℓ‖ * R + |ℓ c| := by linarith
    rw [hq]; linarith
  set m : ℝ := 1 + ∑ t ∈ exc, |t| with hm
  have hm1 : 1 ≤ m := by rw [hm]; linarith [Finset.sum_nonneg (fun t (_ : t ∈ exc) => abs_nonneg t)]
  have hexc : ∀ t ∈ exc, |t| ≤ m - 1 := by
    intro t ht
    have h1 : |t| ≤ ∑ t' ∈ exc, |t'| :=
      Finset.single_le_sum (fun t' (_ : t' ∈ exc) => abs_nonneg t') ht
    rw [hm]; linarith
  refine ⟨v, h, R, ℓ, -(q + m), q + m, exc,
    ⟨c1, c2, c3, c4⟩, hv1, hℓne, hvℓ, hsize, hh, hRbox, ?_, ?_, ?_, ?_⟩
  · intro y hy
    have h1 := hℓy y hy
    have h2 : -|ℓ y| ≤ ℓ y := neg_abs_le _
    have h3 : -(q - 1) ≤ -|ℓ y| := neg_le_neg h1
    linarith
  · intro y hy
    have h1 := hℓy y hy
    have h2 : ℓ y ≤ |ℓ y| := le_abs_self _
    linarith
  · linarith
  · intro t ht
    have h1 := hexc t ht
    have h2 := neg_abs_le t
    have h3 := le_abs_self t
    constructor <;> linarith

end Work.Drive.Mono
