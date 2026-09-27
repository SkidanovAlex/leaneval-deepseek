import Mathlib
import Submission.Work.Drive.N2C.defs
import Submission.Work.Drive.N2.windowDatum
import Submission.Work.Drive.N2C.negTransfer

/-!
# The saddle pin set and the "one component" predicate (`NOTES_LEAD_saddlePacket.md` §1.1)

The anchor level of the saddle window is `a = f p - lam * ηs` (`lam = (ρ_j / 8)²`), and its pinned
part is the set of anchor points whose chart image lies in the marked ball and whose invariant
`|Im (Z ·)²| ≤ m` is small.  `saddlePin D v m` is that set at the level `v` (in the *scaled* chart
coordinates the pin condition is `|2 φ₀ φ₁| ≤ m (ρ/8)²`, because `Im (Zs)² = 2 φ₀ φ₁` and
`Zs = lam0 · Z`).

`OnOneComponent f v S` says that all points of `S` (a subset of the level `f = v`) lie in one
connected component of that level.  It is the conclusion of the dichotomy lemma
(`saddlePin_oneComp_or`, the design's §1.2): for every small `η` either the lower or the upper pin
lies on one component.
-/

namespace Work.Drive.N2Lead

open scoped Manifold ContDiff Topology
open Set Filter

variable {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M]
    [IsManifold (𝓡 2) ((⊤ : ℕ∞) : WithTop ℕ∞) M]

/-- **The pin set of the saddle window at the level `v`.**  Points of the marked chart whose value is
`v`, whose chart image lies in the marked model ball, and whose invariant `|Im (Zs ·)²|` is at most
`m · (ρ_j / 8)²` — i.e. `|Im (Z ·)²| ≤ m` in the scaled coordinate `Z = Zs / lam0`. -/
def saddlePin {f : M → ℝ} {p : M} (D : Work.Drive.N2.WindowDatum f p) (v m : ℝ) : Set M :=
  {x : M | x ∈ (D.φ D.j).source ∧ ‖D.φ D.j x‖ < D.ρ D.j ∧ f x = v ∧
    |2 * (D.φ D.j x 0) * (D.φ D.j x 1)| ≤ m * (D.ρ D.j / 8) ^ 2}

/-- **All of `S` lies on one connected component of the level `f = v`.** -/
def OnOneComponent {f : M → ℝ} (v : ℝ) (S : Set M) : Prop :=
  ∀ x ∈ S, ∀ y ∈ S, y ∈ connectedComponentIn {z : M | f z = v} x

lemma saddlePin_subset_source {f : M → ℝ} {p : M} (D : Work.Drive.N2.WindowDatum f p) {v m : ℝ} :
    saddlePin D v m ⊆ (D.φ D.j).source := fun _ hx => hx.1

lemma saddlePin_val {f : M → ℝ} {p : M} (D : Work.Drive.N2.WindowDatum f p) {v m : ℝ}
    {x : M} (hx : x ∈ saddlePin D v m) : f x = v := hx.2.2.1

lemma saddlePin_norm_lt {f : M → ℝ} {p : M} (D : Work.Drive.N2.WindowDatum f p) {v m : ℝ}
    {x : M} (hx : x ∈ saddlePin D v m) : ‖D.φ D.j x‖ < D.ρ D.j := hx.2.1

lemma saddlePin_im_le {f : M → ℝ} {p : M} (D : Work.Drive.N2.WindowDatum f p) {v m : ℝ}
    {x : M} (hx : x ∈ saddlePin D v m) :
    |2 * (D.φ D.j x 0) * (D.φ D.j x 1)| ≤ m * (D.ρ D.j / 8) ^ 2 := hx.2.2.2

/-- **The pin set is invariant under `f ↦ -f`** with the level negated (the datum `D.neg` carries
the same charts, the same radii and the same marked chart). -/
theorem saddlePin_neg {f : M → ℝ} {p : M} (D : Work.Drive.N2.WindowDatum f p) (v m : ℝ) :
    saddlePin (Work.Drive.N2C.WindowDatum.neg D) (-v) m = saddlePin D v m := by
  ext x
  simp only [saddlePin, Work.Drive.N2C.WindowDatum.neg, Set.mem_setOf_eq]
  constructor
  · rintro ⟨h1, h2, h3, h4⟩
    exact ⟨h1, h2, neg_inj.mp h3, h4⟩
  · rintro ⟨h1, h2, h3, h4⟩
    exact ⟨h1, h2, neg_inj.mpr h3, h4⟩

end Work.Drive.N2Lead
