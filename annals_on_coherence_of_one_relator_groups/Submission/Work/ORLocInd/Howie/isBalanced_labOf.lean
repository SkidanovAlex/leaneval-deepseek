import Mathlib
import Submission.Work.ORLocInd.Howie.LabellingAux

namespace Work.ORLocInd.Howie

open Quiver

/-- The composition of the conjugates of a path and of its reverse cancels completely:
`(d a · p · (d b)⁻¹) · (d b · p⁻¹ · (d a)⁻¹) = 1`.  This is the telescoping computation that
makes `conjElem` send reversals to inverses. -/
theorem pmul_conjPath_reverse {V : Type*} [Quiver V] [Quiver.HasInvolutiveReverse V] {v : V}
    (d : ∀ x : V, Quiver.Path v x) {a b : V} (p : Quiver.Path a b) :
    Work.ORLocInd.Howie.pmul (Work.ORLocInd.Howie.conjPath d p)
      (Work.ORLocInd.Howie.conjPath d p.reverse) = Quiver.Path.nil := by
  have step4 : Work.ORLocInd.Howie.pmul
      (Work.ORLocInd.Howie.pmul p (d b).reverse) (d b) = Work.ORLocInd.Howie.red p := by
    rw [Work.ORLocInd.Howie.pmul_assoc, Work.ORLocInd.Howie.pmul_reverse_left,
      Work.ORLocInd.Howie.pmul_nil_right]
  have step6 : Work.ORLocInd.Howie.pmul p
      (Work.ORLocInd.Howie.pmul p.reverse (d a).reverse) =
      Work.ORLocInd.Howie.red (d a).reverse := by
    rw [← Work.ORLocInd.Howie.pmul_assoc, Work.ORLocInd.Howie.pmul_reverse,
      Work.ORLocInd.Howie.pmul_nil_left]
  show Work.ORLocInd.Howie.pmul
      (Work.ORLocInd.Howie.pmul (Work.ORLocInd.Howie.pmul (d a) p) (d b).reverse)
      (Work.ORLocInd.Howie.pmul (Work.ORLocInd.Howie.pmul (d b) p.reverse) (d a).reverse) =
      Quiver.Path.nil
  rw [Work.ORLocInd.Howie.pmul_assoc (d a) p (d b).reverse,
      Work.ORLocInd.Howie.pmul_assoc (d b) p.reverse (d a).reverse,
      Work.ORLocInd.Howie.pmul_assoc (d a) (Work.ORLocInd.Howie.pmul p (d b).reverse)
        (Work.ORLocInd.Howie.pmul (d b) (Work.ORLocInd.Howie.pmul p.reverse (d a).reverse)),
      ← Work.ORLocInd.Howie.pmul_assoc (Work.ORLocInd.Howie.pmul p (d b).reverse) (d b)
        (Work.ORLocInd.Howie.pmul p.reverse (d a).reverse),
      step4, Work.ORLocInd.Howie.pmul_red_left p
        (Work.ORLocInd.Howie.pmul p.reverse (d a).reverse),
      step6, Work.ORLocInd.Howie.pmul_red_right (d a) (d a).reverse,
      Work.ORLocInd.Howie.pmul_reverse]

/-- `conjElem` sends the reverse of a path to the inverse of its conjugate in the vertex group. -/
theorem conjElem_reverse {V : Type*} [Quiver V] [Quiver.HasInvolutiveReverse V] {v : V}
    (d : ∀ x : V, Quiver.Path v x) {a b : V} (p : Quiver.Path a b) :
    Work.ORLocInd.Howie.conjElem d p.reverse =
      (Work.ORLocInd.Howie.conjElem d p)⁻¹ := by
  have h : Work.ORLocInd.Howie.conjElem d p * Work.ORLocInd.Howie.conjElem d p.reverse = 1 := by
    apply Subtype.ext
    show Work.ORLocInd.Howie.pmul (Work.ORLocInd.Howie.conjPath d p)
      (Work.ORLocInd.Howie.conjPath d p.reverse) = Quiver.Path.nil
    exact pmul_conjPath_reverse d p
  exact (inv_eq_of_mul_eq_one_right h).symm

-- The labelling `labOf d ψ e = ψ (d (e.left) · e · (d (e.right))⁻¹)` is *balanced*:
-- reversing an arrow negates its label.
-- Hint: it suffices to show `conjElem d ((Quiver.reverse f).toPath) = (conjElem d f.toPath)⁻¹`;
-- this follows from the telescoping identity (`conjElem_comp` in `ORLocInd/Howie/conjElem_comp`,
-- if it has landed) or directly from the path computation
--   `pmul (conjPath d f.toPath) (conjPath d ((Quiver.reverse f).toPath)) = nil`
-- using `pmul_assoc`, `pmul_reverse`, `pmul_reverse_left`, `pmul_nil_left`, `pmul_red_left`.
-- Then `map_inv` and `toAdd_inv` finish.
theorem isBalanced_labOf {V : Type*} [Quiver V] [Quiver.HasInvolutiveReverse V] {v : V}
    (d : ∀ x : V, Quiver.Path v x) (ψ : Work.ORLocInd.Howie.VertexGroup v →* Multiplicative ℤ) :
    Work.ORLocInd.Howie.IsBalanced (Work.ORLocInd.Howie.labOf d ψ) := by
  intro e
  obtain ⟨a, b, f⟩ := e
  rw [Quiver.totalReverse_mk]
  show Multiplicative.toAdd (ψ (Work.ORLocInd.Howie.conjElem d (Quiver.reverse f).toPath))
      = - Multiplicative.toAdd (ψ (Work.ORLocInd.Howie.conjElem d f.toPath))
  rw [show (Quiver.reverse f).toPath = f.toPath.reverse from (Quiver.Path.reverse_toPath f).symm,
    conjElem_reverse d f.toPath, map_inv, toAdd_inv]

end Work.ORLocInd.Howie
