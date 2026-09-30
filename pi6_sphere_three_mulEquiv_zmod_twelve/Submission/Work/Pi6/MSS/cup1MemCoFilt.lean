import Mathlib
import Submission.Work.Cohomology.cup1defs
import Submission.Work.Pi6.MSS.Defs
import Submission.Work.Pi6.MSS.cup1FaceEss
import Submission.Work.Pi6.MSS.serreCohFilt
set_option backward.isDefEq.respectTransparency false  -- v435port
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false  -- v435port
set_option backward.isDefEq.respectTransparency.types false  -- v435port

/-!
# The cup-1 product respects the Serre filtration

`Work.Pi6.MSS.cup1MemCoFilt`: if `α ∈ F^a C^n` and `β ∈ F^b C^m` are cochains in the Serre
cochain filtration `coFilt` of a map `f : X ⟶ Y`, then the cup-1 product `cup1 α β` (of degree
`n+m-1`) lies in `F^{a+b-1} C^{n+m-1}`.

The cup-1 product is the sum over `s : Fin m` of the products of the `α`-value on the front
`n`-face `[s, s+n]` and the `β`-value on the complementary back `m`-face.  For a simplex `σ` whose
image in `Y` has essential dimension `< a+b-1`, the essential dimensions of those two faces add up
to at most `ess (f σ) + 1 ≤ a+b-1` (`cup1FaceEss`), so one of the two factors vanishes by the
membership hypotheses.  The remaining arithmetic (`omega`) also covers the degenerate cases
`a = 0` or `b = 0` (where no hypothesis on the corresponding factor is available), where the
dimension bound forces the other factor to vanish.
-/

set_option autoImplicit false

namespace Work.Pi6.MSS

open CategoryTheory CategoryTheory.Limits Simplicial Opposite
open scoped Simplicial

noncomputable section

theorem cup1MemCoFilt (R : Type) [CommRing R] {X Y : SSet.{0}} (f : X ⟶ Y) (a b n m : ℕ) (α : Work.Cohomology.Cochain R X n) (β : Work.Cohomology.Cochain R X m) (hα : α ∈ Work.Pi6.MSS.coFilt R f a n) (hβ : β ∈ Work.Pi6.MSS.coFilt R f b m) : Work.Cohomology.cup1 R X n m α β ∈ Work.Pi6.MSS.coFilt R f (a + b - 1) (n + m - 1) := by
  intro σ hσ
  rw [Work.Cohomology.genEval_cup1]
  refine Finset.sum_eq_zero fun s _ => ?_
  have hs : s.val + n ≤ n + m - 1 := by have := s.isLt; omega
  set y : Y _⦋n + m - 1⦌ := f.app (op ⦋n + m - 1⦌) σ with hy
  have hface := Work.Pi6.MSS.cup1FaceEss n m s.val s.isLt Y y
  have hN1 : f.app (op ⦋n⦌) (X.map (Work.Cohomology.Fface n m s.val hs).op σ)
      = Y.map (Work.Cohomology.Fface n m s.val hs).op y := by
    rw [hy]
    exact NatTrans.naturality_apply f (Work.Cohomology.Fface n m s.val hs).op σ
  have hN2 : f.app (op ⦋m⦌) (X.map (Work.Cohomology.Gface n m s.val hs).op σ)
      = Y.map (Work.Cohomology.Gface n m s.val hs).op y := by
    rw [hy]
    exact NatTrans.naturality_apply f (Work.Cohomology.Gface n m s.val hs).op σ
  obtain hlt | hge := lt_or_ge (Work.Pi6.MSS.ess (Y.map (Work.Cohomology.Fface n m s.val hs).op y)) a
  · have hA : Work.Cohomology.genEval R X α (X.map (Work.Cohomology.Fface n m s.val hs).op σ) = 0 :=
      hα _ (by rw [hN1]; exact hlt)
    rw [hA, mul_zero, zero_mul]
  · have hB : Work.Cohomology.genEval R X β (X.map (Work.Cohomology.Gface n m s.val hs).op σ) = 0 :=
      hβ _ (by rw [hN2]; omega)
    rw [hB, mul_zero]

end

end Work.Pi6.MSS
