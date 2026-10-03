import Mathlib
import Submission.Work.ORLocInd.Howie.LabellingAux

namespace Work.ORLocInd.Howie

open Quiver

variable {V : Type*} [Quiver V] [Quiver.HasInvolutiveReverse V]
variable {v : V}

/-! Two elementary path identities, used to compare the two sides of `conjElem_comp`. -/

/-- Left-hand side normal form: `(u · (p · q)) · w = u · (p · (q · w))`. -/
private theorem pmul_comp_assoc {a b c : V} (u : Quiver.Path v a) (p : Quiver.Path a b)
    (q : Quiver.Path b c) (w : Quiver.Path c v) :
    pmul (pmul u (p.comp q)) w = pmul u (pmul p (pmul q w)) := by
  have h : pmul (p.comp q) w = pmul p (pmul q w) :=
    (pmul_red_left (p.comp q) w).symm.trans (pmul_assoc p q w)
  calc pmul (pmul u (p.comp q)) w
      = pmul u (pmul (p.comp q) w) := pmul_assoc u (p.comp q) w
    _ = pmul u (pmul p (pmul q w)) := by rw [h]

/-- Right-hand side normal form: `((u · p) · t⁻¹) · ((t · q) · w) = u · (p · (q · w))`. -/
private theorem pmul_conj_assoc {a b c : V} (u : Quiver.Path v a) (p : Quiver.Path a b)
    (t : Quiver.Path v b) (q : Quiver.Path b c) (w : Quiver.Path c v) :
    pmul (pmul (pmul u p) t.reverse) (pmul (pmul t q) w) = pmul u (pmul p (pmul q w)) := by
  rw [pmul_assoc (pmul u p) t.reverse (pmul (pmul t q) w)]
  rw [← pmul_assoc t.reverse (pmul t q) w]
  rw [← pmul_assoc t.reverse t q]
  rw [pmul_reverse_left t]
  rw [pmul_nil_left]
  rw [pmul_red_left]
  rw [pmul_assoc u p (pmul q w)]

-- `conjElem d p = d a · p · (d b)⁻¹` is multiplicative in `p`:
-- `conjElem d (p.comp q) = conjElem d p * conjElem d q` in the group `VertexGroup v`.
-- Hint: `Subtype.ext` reduces this to the path equality
--   `pmul (pmul (d a) (p.comp q)) (d c).reverse
--      = pmul (pmul (pmul (d a) p) (d b).reverse) (pmul (pmul (d b) q) (d c).reverse)`,
-- both sides equal `pmul (d a) (pmul p (pmul q (d c).reverse))` by `pmul_assoc`,
-- `pmul_reverse_left`, `pmul_nil_left` and `pmul_red_left` (all in `Basic.lean` / `LabellingAux.lean`).
theorem conjElem_comp {V : Type*} [Quiver V] [Quiver.HasInvolutiveReverse V] {v : V}
    (d : ∀ x : V, Quiver.Path v x) {a b c : V} (p : Quiver.Path a b) (q : Quiver.Path b c) :
    Work.ORLocInd.Howie.conjElem d (p.comp q) =
      Work.ORLocInd.Howie.conjElem d p * Work.ORLocInd.Howie.conjElem d q := by
  apply Subtype.ext
  simp only [VertexGroup.coe_mul, conjElem_coe, conjPath]
  exact (pmul_comp_assoc (d a) p q (d c).reverse).trans
    (pmul_conj_assoc (d a) p (d b) q (d c).reverse).symm

end Work.ORLocInd.Howie
