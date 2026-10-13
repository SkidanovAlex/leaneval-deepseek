import Mathlib
import Submission.Work.DSM5c.Charts
import Submission.Work.DSPB2.Main

universe a

namespace Work.DSM5c.Eta.U

/-- **The `♯`-map on a `W♭`-algebra is the `W`-algebra structure of the untilt composed with the
tilt.**  For any `W♭`-algebra `φ : PreTilt W p →+* R`, the Teichmüller lift composed with the
untilt quotient map agrees with the `W`-algebra structure of `untiltOf R φ` on the tilt:

  `untiltOf.mk φ ([φ y]) = untiltOf.algebraMap hθ φ (♯ y)`  for `y : PreTilt W p`.

Route: `WittVector.map_teichmuller` moves `𝕎(φ) ([y])` to `[φ y]`, and
`untiltOf.algebraMap_fontaineTheta` together with `WittVector.fontaineTheta_teichmuller`
(`θ([y]) = ♯y`) rewrites the `W`-algebra structure.  This is the general form of the chart-level
statement used by the M5c chart map (`φ := Work.DSM5c.chartPhi Q t tr htr0 htr j₀ e S`). -/
theorem teich_algebraMap {p : ℕ} [Fact p.Prime] {W : Type a} [CommRing W] [Fact ¬IsUnit (p : W)]
    [IsAdicComplete (Ideal.span {(p : W)}) W]
    (hθ : Function.Surjective (WittVector.fontaineTheta (p := p) (R := W)))
    {R : Type a} [CommRing R] (φ : PreTilt W p →+* R) (y : PreTilt W p) :
    (Work.DSM5c.untiltOf.mk φ) (WittVector.teichmuller p (φ y))
      = (Work.DSM5c.untiltOf.algebraMap hθ φ) (PreTilt.untilt y) := by
  rw [← WittVector.map_teichmuller (p := p) φ y]
  rw [← Work.DSM5c.untiltOf.algebraMap_fontaineTheta (p := p) (W := W) hθ φ
    (WittVector.teichmuller p y)]
  rw [WittVector.fontaineTheta_teichmuller]

end Work.DSM5c.Eta.U
