import Mathlib
import Submission.Work.ORLocInd.Howie.Delete
import Submission.Work.ORLocInd.Howie.abstract_tietze
import Submission.Work.ORLocInd.Howie.exists_split_arrowList
import Submission.Work.ORLocInd.Howie.filter_length_one
import Submission.Work.ORLocInd.Howie.Defs2
import Submission.Work.ORLocInd.Howie.TietzeSupport
import Submission.Work.ORLocInd.Howie.mem_relatorNormalClosure_conj
import Submission.Work.ORLocInd.Howie.L4.SubstSupport
import Submission.Work.ORLocInd.Howie.L4.SubstConditions
import Submission.Work.L4.delEraseVG_vertexHom_mul_inv_mem

namespace Work.ORLocInd.Howie.L4

theorem deleteSubInclVG_bijective {V : Type*} [Quiver V] [Quiver.HasInvolutiveReverse V]
    [DecidableEq V] (P : Work.ORLocInd.Howie.Presentation V) (hsep : P.CodeSeparates)
    (i₀ : P.ι) (f : Quiver.Total V)
    (hf₀ : Work.ORLocInd.Howie.edgeCount P.edgeOf (P.path i₀) f = 1)
    (hf : ∀ i, i ≠ i₀ → Work.ORLocInd.Howie.edgeCount P.edgeOf (P.path i) f = 0) (x : V) :
    Function.Bijective (P.deleteSubInclVG (P.keepCode (P.edgeOf f)) (fun i => i ≠ i₀) x) := by
  obtain ⟨D, hK, _hfD, hi₀⟩ := Work.ORLocInd.Howie.exists_tietzeData P hsep i₀ f hf₀
  have hkeep : ∀ i, i ≠ D.i₀ → ∀ e ∈ (P.path i).arrowList, D.K.pred e := by
    intro i hi e he
    have hi' : i ≠ i₀ := fun h => hi (by rw [hi₀, h])
    rw [hK]
    exact Work.ORLocInd.Howie.keepPath_of_edgeCount_zero P i f (hf i hi') e he
  have hcong : ∀ b : Work.ORLocInd.Howie.VertexGroup x,
      Work.ORLocInd.Howie.delEraseVG D.K x (D.pathSubst.vertexHom x b) * b⁻¹ ∈
        P.relatorNormalClosure x :=
    fun b => Work.L4.delEraseVG_vertexHom_mul_inv_mem P D x b
  have h := Work.ORLocInd.Howie.deleteSubInclVG_bijective_of_tietzeData D hkeep x hcong
  rwa [hK, hi₀] at h

end Work.ORLocInd.Howie.L4
