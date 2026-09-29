import Mathlib
import Submission.Work.Cert.Spec
import Submission.Work.Cert.ACGeom.GeomAux
import Submission.Work.Cert.ACGeom.close_circle
import Submission.Work.Cert.ACGeom.starprod_pos

/-!
# The geometric consequences of `geomOK`

`geomOK L = true` is the `okA` conjunct of the leaf checker: it certifies, in integer mantissas at
scale `S`, that

* `chU ≥ 0` and `|B − A|² ≤ chU²` (`A`, `B` are close, so the leaf is a *short* arc),
* `|B − A|² < (Rk k)²/4` (shorter than half the radius, i.e. the arc is the minor one),
* `Ax·By − Ay·Bx > 0` and `Ax·Bx + Ay·By > 0` (`A → B` runs counter-clockwise by less than `π/2`),
* `|Ax² + Ay² − Rk k²| ≤ 2·Rk k·CTOL` and likewise for `B` (`A`, `B` lie on the circle of radius
  `Rk k` up to `CTOL` of rounding).

This file spells out the real-number consequences that the covering argument
(`Submission/Work/Cert/arc_cover.lean`) consumes: the scaled points `cx L.Ax L.Ay` and `cx L.Bx L.By`
are at distance at most `chU/S`, their Hermitian product `star A · B` has both parts positive
(the arc turns counter-clockwise through an angle in `(0, π/2)`), and both points are within
`2·CTOL/S` of the circle of radius `(Rk L.k)/S`.

The pieces are delegated: `chord_bound` (`GeomAux`), `close_circle`, `starprod_pos`.
-/
namespace Work.Cert.ACGeom

open Work.Cert

theorem geomOK_facts (L : Leaf) (h : geomOK L = true) :
    (0 : ℝ) ≤ (L.chU : ℝ) ∧
    ‖cx L.Ax L.Ay - cx L.Bx L.By‖ ≤ (L.chU : ℝ) / (S : ℝ) ∧
    0 < (star (cx L.Ax L.Ay) * cx L.Bx L.By).im ∧
    0 < (star (cx L.Ax L.Ay) * cx L.Bx L.By).re ∧
    |‖cx L.Ax L.Ay‖ - (Rk L.k : ℝ) / (S : ℝ)| ≤ 2 * (CTOL : ℝ) / (S : ℝ) ∧
    |‖cx L.Bx L.By‖ - (Rk L.k : ℝ) / (S : ℝ)| ≤ 2 * (CTOL : ℝ) / (S : ℝ) := by
  -- unfold the Bool checker into its seven integer conjuncts
  simp only [geomOK, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨h1, h2⟩, _h3⟩, h4⟩, h5⟩, h6⟩, h7⟩ := h
  have hsp := starprod_pos L.Ax L.Ay L.Bx L.By h5 h4
  exact ⟨by exact_mod_cast h1,
    chord_bound L.Ax L.Ay L.Bx L.By L.chU h1 h2,
    hsp.1, hsp.2,
    close_circle L.Ax L.Ay L.k h6,
    close_circle L.Bx L.By L.k h7⟩

end Work.Cert.ACGeom
