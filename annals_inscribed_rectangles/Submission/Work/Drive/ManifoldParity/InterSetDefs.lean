import Submission.Work.Drive.ChartBridge

/-!
# The intersection set and its boundary part, in `ℝ⁵` coordinates

The target of `Work.Drive.transverse_inter_boundary_parity` is a statement about pairs `(s,t)` in
`ℝ² × ℝ³`.  The block identification `mkPart : ℝ² × ℝ³ ≅ ℝ⁵` (`sqPart`, `cbPart`) turns it into a
statement about `ℝ⁵`, which is the form in which the mod-2 chapter (`Work.Drive.boxParity`,
`Work.Drive.ChartData`) is set up.
-/

namespace Work.Drive

open scoped Manifold ContDiff Topology
open Manifold Set

set_option backward.isDefEq.respectTransparency false

noncomputable section

variable {M : Type*} [TopologicalSpace M] [T2Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 4)) M] [IsManifold (𝓡 4) Ctop M]

/-- The intersection set of the two chains, in the box `[0,1]⁵ = [0,1]² × [0,1]³`. -/
def interSet (D : EuclideanSpace ℝ (Fin 2) → M) (N : EuclideanSpace ℝ (Fin 3) → M) :
    Set (Amb 4) :=
  {x | x ∈ Submission.Drive.unitBox 4 ∧ D (sqPart x) = N (cbPart x)}

/-- The part of the intersection set on the boundary of the box: `∂D ⋔ N` together with
`D ⋔ ∂N`. -/
def bInterSet (D : EuclideanSpace ℝ (Fin 2) → M) (N : EuclideanSpace ℝ (Fin 3) → M) :
    Set (Amb 4) :=
  {x | x ∈ Submission.Drive.unitBox 4 ∧ D (sqPart x) = N (cbPart x) ∧
    x ∈ Submission.Drive.unitBoxBdry 4}

@[simp] theorem mem_interSet {D : EuclideanSpace ℝ (Fin 2) → M}
    {N : EuclideanSpace ℝ (Fin 3) → M} {x : Amb 4} :
    x ∈ interSet D N ↔ x ∈ Submission.Drive.unitBox 4 ∧ D (sqPart x) = N (cbPart x) :=
  Iff.rfl

@[simp] theorem mem_bInterSet {D : EuclideanSpace ℝ (Fin 2) → M}
    {N : EuclideanSpace ℝ (Fin 3) → M} {x : Amb 4} :
    x ∈ bInterSet D N ↔ x ∈ Submission.Drive.unitBox 4 ∧ D (sqPart x) = N (cbPart x) ∧
      x ∈ Submission.Drive.unitBoxBdry 4 := Iff.rfl

theorem bInterSet_subset_interSet (D : EuclideanSpace ℝ (Fin 2) → M)
    (N : EuclideanSpace ℝ (Fin 3) → M) : bInterSet D N ⊆ interSet D N :=
  fun _ hx => ⟨hx.1, hx.2.1⟩

/-- The intersection set is compact. -/
theorem isCompact_interSet (D : EuclideanSpace ℝ (Fin 2) → M)
    (N : EuclideanSpace ℝ (Fin 3) → M) (hD : Continuous D) (hN : Continuous N) :
    IsCompact (interSet D N) := by
  have hclosed : IsClosed (interSet D N) := by
    have h1 : IsClosed {x : Amb 4 | D (sqPart x) = N (cbPart x)} :=
      isClosed_eq (hD.comp (by unfold sqPart; fun_prop))
        (hN.comp (by unfold cbPart; fun_prop))
    have h2 : IsClosed (Submission.Drive.unitBox 4 ∩
        {x : Amb 4 | D (sqPart x) = N (cbPart x)}) := (isClosed_unitBox 4).inter h1
    convert h2 using 1
    ext x
    simp [interSet]
  exact (isCompact_unitBox 4).of_isClosed_subset hclosed (fun x hx => hx.1)

end

end Work.Drive
