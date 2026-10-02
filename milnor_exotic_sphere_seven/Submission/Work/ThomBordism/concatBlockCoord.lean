import Submission.Work.PTGeometric.SourceFamily
import Submission.Work.PTGeometric.ConcreteCollapse
import Submission.Work.PTGeometric.SourceZero

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# The two-level block coordinate of the `0`-end `alphaFamily`

`Work.PTGeometric.alphaFamily G m` is the *iterated* concatenation
`genLoopListConcat ⟨0⟩ (List.ofFn (fun _ : Fin m => blockInner G))`, and `blockInner G` is itself
`genLoopListConcat ⟨1⟩ (List.ofFn (blockLoop G))`.  Hence a cube point of `alphaFamily`'s core
preimage is confined to a *block* selected by a pair `(s, j)` (`s : Fin m`, `j` indexing the pieces),
and the reparametrised cube point inside that block is obtained by applying
`Work.PTGeometric.genLoopListConcatStep` twice – once for each level.

The two definitions below name that data, so that the *coordinate* form of the block decomposition
(which `Work.PTGeometric.AFS.blockSpec` / `alphaFamily_corePreimage_homeo_spec` record only as a loop
*value* equation) can be stated.
-/

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

open scoped Topology unitInterval
open Function Set

namespace Work.ThomBordism

noncomputable section

open Work.ThomBordism.PontryaginThom

variable {k : ℕ} {D : ThomTarget k} {ι : Type} [Fintype ι] {Fam : ι → Man8}

/-- The concatenation coordinate of the outer level of `alphaFamily`. -/
def outerCoord (G : Work.PTGeometric.GenuineTubeGeometry k D ι Fam) (m : ℕ) : Fin (k + 8) :=
  ⟨0, by omega⟩

/-- The concatenation coordinate of the inner level of `alphaFamily`. -/
def innerCoord (G : Work.PTGeometric.GenuineTubeGeometry k D ι Fam) (m : ℕ) : Fin (k + 8) :=
  ⟨1, by omega⟩

/-- **The outer block decomposition of `alphaFamily`**: at the cube point `z` it returns the block
index of the `m` copies of the inner concatenation, and the reparametrised cube point inside it. -/
def outerStep (G : Work.PTGeometric.GenuineTubeGeometry k D ι Fam) (m : ℕ)
    (z : Fin (k + 8) → Set.Icc (0 : ℝ) 1) : ℕ × (Fin (k + 8) → Set.Icc (0 : ℝ) 1) :=
  Work.PTGeometric.genLoopListConcatStep (outerCoord G m)
    (List.ofFn (fun _ : Fin m => Work.PTGeometric.blockInner (D := D) (Fam := Fam) G)) z

/-- **The inner block decomposition**: at the outer coordinate it returns the index of the piece's
collapse loop in the inner concatenation, and the reparametrised cube point inside it. -/
def innerStep (G : Work.PTGeometric.GenuineTubeGeometry k D ι Fam) (m : ℕ)
    (z : Fin (k + 8) → Set.Icc (0 : ℝ) 1) : ℕ × (Fin (k + 8) → Set.Icc (0 : ℝ) 1) :=
  Work.PTGeometric.genLoopListConcatStep (innerCoord G m)
    (List.ofFn (Work.PTGeometric.blockLoop (D := D) (Fam := Fam) G)) (outerStep G m z).2

/-- **The tube cube point of the block**: the two-level block coordinate, read in the coordinate
order of the embedding (`Fin (8+k)`). -/
def blockTubePoint (G : Work.PTGeometric.GenuineTubeGeometry k D ι Fam) (m : ℕ)
    (z : Fin (k + 8) → Set.Icc (0 : ℝ) 1) : Fin (8 + k) → Set.Icc (0 : ℝ) 1 :=
  (innerStep G m z).2 ∘ (finCongr (Nat.add_comm k 8)).symm

end

end Work.ThomBordism
