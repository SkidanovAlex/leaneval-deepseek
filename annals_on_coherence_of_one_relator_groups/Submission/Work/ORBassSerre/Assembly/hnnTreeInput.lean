import Mathlib
import Submission.Work.ORAssembly.Defs
import Submission.Work.ORDunwoody.Hypotheses
import Submission.Work.ORBassSerre.Interface
import Submission.Work.ORBassSerre.HNN.Defs
import Submission.Work.ORBassSerre.HNN.Graph
import Submission.Work.ORBassSerre.HNN.Tree

namespace Work.ORBassSerre.Assembly

universe u

/-- Node N12 discharging `Work.ORAssembly.HNNTreeInput`: the Bass--Serre tree of an HNN extension
`E = HNNExtension G A B φ`, a tree on which `E` acts with vertex stabilizers the conjugates of the
image of `G`.  Suggested model: vertices are the cosets `E/G` (equivalently `ℤ ×` nothing, via
`t ^ n * g`), with adjacency `xG ~ xtG`. -/
theorem hnnTreeInput : Work.ORAssembly.HNNTreeInput.{u} := by
  intro G inst A B φ
  refine ⟨Work.ORBassSerre.HNN.VSet (A := A) (B := B) (φ := φ), ?_, ?_, ?_⟩
  · exact inferInstance
  · exact ⟨Work.ORBassSerre.HNN.hnnGraph (A := A) (B := B) (φ := φ),
      Work.ORBassSerre.HNN.hnnGraph_isTree,
      fun e X Y h => Work.ORBassSerre.HNN.smul_adj e h⟩
  · intro v
    obtain ⟨g, rfl⟩ := Quotient.exists_rep v
    exact ⟨g, Work.ORBassSerre.HNN.stabilizer_qmk g⟩

end Work.ORBassSerre.Assembly
