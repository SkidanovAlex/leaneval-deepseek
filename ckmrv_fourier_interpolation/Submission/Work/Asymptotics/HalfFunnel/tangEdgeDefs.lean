/-
# The three non-contour edges of the tangency rectangle

The rectangle of the tangency analysis is `[0,1/4] × [1/2,3/2] ⊂ ℂ`.  Its contour edge is the
left one, `Re z = 0` (the imaginary axis, along which the CKMRV contour integral runs); the
kernel must be bounded on the *other* three edges, which is what `tangEdgeBound` asserts.

This file only fixes the two sets: `edgeC`, the three edges as a subset of `ℂ` (so that the
hypothesis of `tangEdgeBound` is literally membership in `edgeC`), and `edgeH`, the same set
as a subset of the upper half plane, where the kernel `Kfun` (and `j`) live.
-/
import Mathlib
import Submission.Work.Asymptotics.HalfFunnel.tangLayerDefs

open UpperHalfPlane

namespace Work.Asymptotics.HalfFunnel

noncomputable section

/-- **The three non-contour edges of the rectangle `[0,1/4] × [1/2,3/2]`**, as a set of `ℂ`:
the right edge `Re z = 1/4` (`1/2 ≤ Im z ≤ 3/2`), and the bottom and top edges `Im z = 1/2`
resp. `Im z = 3/2` (`0 ≤ Re z ≤ 1/4`).  The left edge `Re z = 0` — the contour — is *excluded*:
it is the edge across which the residue theorem moves the integral. -/
def edgeC : Set ℂ :=
  {z | (z.re = 1 / 4 ∧ (1 : ℝ) / 2 ≤ z.im ∧ z.im ≤ 3 / 2) ∨
       (z.im = 1 / 2 ∧ 0 ≤ z.re ∧ z.re ≤ 1 / 4) ∨
       (z.im = 3 / 2 ∧ 0 ≤ z.re ∧ z.re ≤ 1 / 4)}

/-- The same three edges, seen inside the upper half plane. -/
def edgeH : Set ℍ := UpperHalfPlane.ofComplex '' edgeC

/-- The three non-contour edges lie strictly above the real axis. -/
lemma edgeC_im_pos {z : ℂ} (hz : z ∈ edgeC) : 0 < z.im := by
  rcases hz with ⟨_, h1, _⟩ | ⟨h1, _, _⟩ | ⟨h1, _, _⟩ <;> linarith

/-- Every point of the three non-contour edges lies in the closed rectangle
`[0,1/4] × [1/2,3/2]`. -/
lemma edgeC_rect {z : ℂ} (hz : z ∈ edgeC) :
    0 ≤ z.re ∧ z.re ≤ 1 / 4 ∧ (1 : ℝ) / 2 ≤ z.im ∧ z.im ≤ 3 / 2 := by
  rcases hz with ⟨hre, h1, h2⟩ | ⟨him, h1, h2⟩ | ⟨him, h1, h2⟩
  · exact ⟨by linarith, by linarith, h1, h2⟩
  · exact ⟨h1, h2, by linarith, by linarith⟩
  · exact ⟨h1, h2, by linarith, by linarith⟩

/-- Membership in `edgeH`, translated to `edgeC` through the coercion `ℍ → ℂ`. -/
lemma mem_edgeH_iff (ζ : ℍ) : ζ ∈ edgeH ↔ (ζ : ℂ) ∈ edgeC := by
  constructor
  · rintro ⟨z, hz, rfl⟩
    rwa [UpperHalfPlane.ofComplex_apply_of_im_pos (edgeC_im_pos hz), UpperHalfPlane.coe_mk]
  · intro h
    exact ⟨(ζ : ℂ), h, UpperHalfPlane.ext (by rw [UpperHalfPlane.ofComplex_apply])⟩

end

end Work.Asymptotics.HalfFunnel
