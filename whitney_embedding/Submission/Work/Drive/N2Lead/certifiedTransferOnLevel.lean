import Mathlib
import Submission.Work.Drive.N2C.defs
import Submission.Work.Drive.N2.footMapDefs

/-!
# Glue for the core of `D2`: transferring a certificate along an equality on the level, and the
foot map on its own level

Two small facts the assembly of the core `Work.Drive.N2Lead.exists_certifiedWindow_saddle_oneComp`
needs, both independent of the packet:

* `Work.Drive.N2Lead.isCertifiedAt_of_eqOn_level`: `IsCertifiedAt` sees a picture only through its
  values on the level, so replacing the picture off the level changes nothing;
* `Work.Drive.N2Lead.footMap_eq_self_of_eq`: the foot map `footMap Φ f a` is the identity on the level
  `f = a` (`footMap Φ f a y = Φ (a - f y, y) = Φ (0, y) = y`), which is why on the anchor level the
  two-piece drawing of the saddle window *is* the park picture `A` (the model piece and the
  transported piece agree there: `hApin` on the region, `foot = id` off it).

The same two facts are what turn the lower certificate of §4.2 (`IsCertifiedAt f a A`) into the
engine's `IsCertifiedAt f a W`.
-/

open scoped Manifold ContDiff

namespace Work.Drive.N2Lead

open scoped Manifold ContDiff Topology
open Set

open scoped Manifold ContDiff in
/-- **`IsCertifiedAt` depends on the picture only through its values on the level.** -/
theorem isCertifiedAt_of_eqOn_level {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M]
    [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2))) ((⊤ : ℕ∞) : WithTop ℕ∞) M]
    {f : M → ℝ} {u : ℝ} {A W : M → EuclideanSpace ℝ (Fin 3)}
    (hAW : ∀ y : M, f y = u → A y = W y)
    (hA : Work.Drive.N2C.IsCertifiedAt f u A) : Work.Drive.N2C.IsCertifiedAt f u W := by
  obtain ⟨n, L, D, e, hD, hiso, h0, h1⟩ := hA
  exact ⟨n, L, D, e, hD, hiso, fun y hy => (h0 y hy).trans (hAW y hy), h1⟩

open scoped Manifold ContDiff in
/-- **The foot map is the identity on its own level.** -/
theorem footMap_eq_self_of_eq {M : Type*} [TopologicalSpace M]
    {Φ : ℝ × M → M} (hΦ0 : ∀ y : M, Φ (0, y) = y) {f : M → ℝ} {a : ℝ}
    {y : M} (hy : f y = a) : Work.Drive.N2.footMap Φ f a y = y := by
  show Φ (a - f y, y) = y
  rw [hy, sub_self]
  exact hΦ0 y

end Work.Drive.N2Lead
