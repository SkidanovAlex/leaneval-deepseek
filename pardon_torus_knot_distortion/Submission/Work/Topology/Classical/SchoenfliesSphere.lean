import Submission.Work.Topology.Classical.Defs
import Submission.Work.Topology.Classical.exists_homeomorph_roundSphere
import Submission.Work.Topology.Classical.schoenfliesData_of_jordanSchoenflies

/-!
# Jordan–Schoenflies on an arbitrary embedded sphere, and on the box boundary

`Work.Topology.Classical.schoenfliesData_of_jordanSchoenflies` transports the classical
Jordan–Schoenflies conclusion along a homeomorphism `RoundSphere ≃ₜ A`.  Two instances are the
useful ones:

* **any embedded sphere** — a `2`-sphere in `ℝ³` that is the image of an injective continuous map
  of `RoundSphere` is homeomorphic to it (`Work.Topology.Classical.exists_homeomorph_roundSphere`),
  so `nonempty_schoenfliesData_of_embeddedSphere` gives the full Jordan–Schoenflies structure for
  families of Jordan curves on it;
* **the box boundary** — `BoxSphere s c σ = ∂PBox s c σ` comes with the *explicit* homeomorphism
  `Work.Topology.SphereSlicing.homeomorph_BoxSphere` (radial projection from the centre of the box
  and its inverse), so `nonempty_schoenfliesData_BoxSphere` gives the same for the polyhedral
  sphere of Pardon's box, without going through the abstract embedded-sphere route.

This is the sharpest form of "assignment item 1" which the chapter reaches: the Jordan–Schoenflies
theorem *stated for the round sphere* (the hypothesis `JordanSchoenfliesSphere`) is available for
every sphere that Pardon's argument meets — in particular for the box boundary, which is the only
sphere the sweep uses when `P = mapHomeomorph ψ` (the transfer of the whole slicing input along an
ambient homeomorphism is the sibling chapter's `sliceData_map_homeomorph_iff`).
-/

open LeanEval.KnotTheory.PardonDistortion
open Set
open Work.CoreTopology
open Work.InnermostDisk

namespace Work.Topology.Classical

noncomputable section

/-- **Jordan–Schoenflies on an arbitrary embedded sphere of `ℝ³`**: from the round-sphere
hypothesis, every family of pairwise disjoint simple closed curves on `S` bounds a nested family of
discs in `S`. -/
theorem nonempty_schoenfliesData_of_embeddedSphere (h : JordanSchoenfliesSphere)
    {A : Set R3} (hA : IsEmbeddedSphere A)
    {ι : Type} [Fintype ι] {c : ι → ℝ → R3}
    (hc : ∀ i : ι, IsJordanCurveOn A (c i))
    (hd : Pairwise fun i j : ι => Disjoint (Set.range (c i)) (Set.range (c j))) :
    Nonempty (SchoenfliesData A ι c) := by
  obtain ⟨φ, _⟩ := exists_homeomorph_roundSphere A hA
  exact schoenfliesData_of_jordanSchoenflies h φ hc hd

/-- **Jordan–Schoenflies on the box boundary** `∂PBox s c σ = BoxSphere s c σ`, via the explicit
homeomorphism `Work.Topology.SphereSlicing.homeomorph_BoxSphere` (radial projection from the
centre of the box and its inverse). -/
theorem nonempty_schoenfliesData_BoxSphere (h : JordanSchoenfliesSphere) {s : ℝ} (hs : 0 < s)
    (c : R3) (σ : Equiv.Perm (Fin 3))
    {ι : Type} [Fintype ι] {γ : ι → ℝ → R3}
    (hc : ∀ i : ι, IsJordanCurveOn (Work.Topology.SphereSlicing.BoxSphere s c σ) (γ i))
    (hd : Pairwise fun i j : ι => Disjoint (Set.range (γ i)) (Set.range (γ j))) :
    Nonempty (SchoenfliesData (Work.Topology.SphereSlicing.BoxSphere s c σ) ι γ) := by
  obtain ⟨Φ, _⟩ := Work.Topology.SphereSlicing.homeomorph_BoxSphere hs c σ
  exact schoenfliesData_of_jordanSchoenflies h Φ.symm hc hd

/-- **The hypothesis `JordanSchoenfliesSphere` is exactly its packaged form**: it says that every
family of pairwise disjoint Jordan curves on the round sphere carries a `SchoenfliesData`. -/
theorem jordanSchoenfliesSphere_iff_schoenfliesData :
    JordanSchoenfliesSphere ↔
      ∀ (ι : Type) [Fintype ι] (c : ι → ℝ → R3),
        (∀ i : ι, IsJordanCurveRound (c i)) →
        (Pairwise fun i j : ι => Disjoint (Set.range (c i)) (Set.range (c j))) →
        Nonempty (SchoenfliesData RoundSphere ι c) := by
  constructor
  · intro h ι _ c hc hd
    exact schoenfliesData_of_jordanSchoenflies h (Homeomorph.refl RoundSphere) hc hd
  · intro h ι _ c hc hd
    obtain ⟨D⟩ := h ι c hc hd
    exact ⟨D.e, D.e', D.rank, D.inj, D.inj', D.boundary, D.boundary', D.mem, D.mem',
      D.open_interior, D.open_interior', D.cover, D.meet, D.nested⟩

end

end Work.Topology.Classical
