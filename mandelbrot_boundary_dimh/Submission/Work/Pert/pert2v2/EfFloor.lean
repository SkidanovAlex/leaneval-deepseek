import Mathlib
import Submission.Work.Pert.pert2v2.HornExt
import Submission.Work.Pert.pert2v2.CoverHalf

/-!
# `Work.Pert.pert2v2.EfFloor` — the floor-based `ℤ`-extension of the horn map

`pert2v2.end_const_le_seg` (the paper's (A.4.4)) needs a function `Ef` on the half plane with

* `hper : Ef (w + 1) = Ef w + 1` (so that `Ef - id` extends to a `1`-periodic function),
* `hdiff : DifferentiableOn ℂ (fun w => Ef w - w) {y ≤ Im}`,
* `hlim : Ef w - w → cp - cm` at the upper end,
* `hseg : ‖Ef (x + iy₀) - d.E (x + iy₀)‖ < δ/2` on a segment.

The paper's definition is `Ẽ_f(w) = Φ_{+,f} ∘ Φ_{-,f}⁻¹(w)` on the gate image, extended by
`ℤ`-periodicity.  The version here uses a **canonical** representative: for `w` with
`y ≤ Im w` take `n := ⌊Re w⌋`, so that `w - n` always has real part in `[0,1)`; then

  `Ef w = Φp (invOn Φm Q (w - n)) + n`.

Two advantages over `HornExt.Ef` (which chooses an arbitrary representative and therefore needs
`SameLevelStructure`, i.e. the walk structure on the whole gate):

* `hper` is *immediate*: `⌊Re (w+1)⌋ = ⌊Re w⌋ + 1` and `(w+1) - (n+1) = w - n`, so the same gate
  representative is used at `w + 1`;
* the representative has `Re ∈ [0,1)`, which is exactly the window produced by the cover lemma
  `waist_cover_seg_zero`/`cover_seg_pointwise`, and stays inside the half-open window handled by
  `pert2v2.gate_preimage_re_bound` (the closed window `[0,1]` is *not* covered by the cover lemma).
-/

namespace Work.Pert.pert2v2

open MandelDim Complex Set

noncomputable section

/-- The floor-based `ℤ`-extension of `Φp ∘ Φm⁻¹` w.r.t. the gate `Q`: at a point `w` whose
`[0,1)`-representative `w - ⌊Re w⌋` is a gate value, the value is `Φp` of that gate point plus the
shift; elsewhere it is set to `0` (junk, as in `pert2v2.Ef`). -/
noncomputable def EfFloor (Φm Φp : ℂ → ℂ) (Q : Set ℂ) (w : ℂ) : ℂ := by
  classical
  exact if w - (((Int.floor w.re : ℤ)) : ℂ) ∈ Φm '' Q then
    Φp (Work.Pert.invOn Φm Q (w - (((Int.floor w.re : ℤ)) : ℂ)))
      + (((Int.floor w.re : ℤ)) : ℂ)
  else 0

/-- **Periodicity of the floor-based extension**, on the region where the canonical representative is
a gate value (which the cover provides for every large height).  The representative of `w + 1` is
that of `w` shifted by `1`, and the shift cancels against the integer. -/
theorem EfFloor_add_one {Φm Φp : ℂ → ℂ} {Q : Set ℂ} (w : ℂ)
    (h : w - (((Int.floor w.re : ℤ)) : ℂ) ∈ Φm '' Q) :
    EfFloor Φm Φp Q (w + 1) = EfFloor Φm Φp Q w + 1 := by
  have hre : (w + 1).re = w.re + 1 := by simp
  have hfloor : Int.floor ((w + 1).re) = Int.floor w.re + 1 := by
    rw [hre]; exact Int.floor_add_one w.re
  have hpt : (w + 1) - (((Int.floor (w + 1).re : ℤ)) : ℂ)
      = w - (((Int.floor w.re : ℤ)) : ℂ) := by
    rw [hfloor]
    push_cast
    ring
  unfold EfFloor
  rw [hpt, hfloor]
  rw [if_pos h, if_pos h]
  push_cast
  ring

end

end Work.Pert.pert2v2
