import Mathlib.Algebra.DirectSum.Module
import Mathlib.GroupTheory.QuotientGroup.Defs
import Submission.Work.SSGRoute.prop5.coreGraded
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The graded Lie ring of the lower central series

`graded.GLam q = γ_q/γ_{q+1}` is the `q`-th piece of the associated graded of the lower central
series, and `graded.bracketL p q : Λ p →+ Λ q →+ Λ (p+q+1)` is the graded commutator.

This file collects the pieces into one graded Lie ring `Λbar = ⨁ q, Λ q`.  The bracket is the
bilinear extension of `(lof p a, lof q b) ↦ lof (p+q+1) (bracketL p q a b)`;  because the target
is the direct sum, no `Eq.rec` cast on indices is ever needed.
-/

noncomputable section

open scoped commutatorElement

namespace Work.SSGRoute.prop5
namespace graded

variable {G : Type*} [Group G]

/-- The associated graded of the lower central series, with the index shifted so that the bracket
increases the degree by one: `Λbar = ⨁ k, Λ k` with `Λ k = γ_k/γ_{k+1}`. -/
abbrev Lbar (G : Type*) [Group G] : Type _ :=
  DirectSum ℕ (fun k => Additive (GLam (G := G) k))

instance instAddCommGroupLbar : AddCommGroup (Lbar G) := inferInstance

/-- The graded commutator with a homogeneous first argument, as an additive map in that
argument. -/
noncomputable def bracketBarHom (p : ℕ) :
    Additive (GLam (G := G) p) →+ (Lbar G →+ Lbar G) where
  toFun a :=
    DFinsupp.liftAddHom fun q =>
      (DirectSum.lof ℤ ℕ (fun k => Additive (GLam (G := G) k)) (p + q + 1)).toAddMonoidHom.comp
        (bracketL (G := G) p q a)
  map_zero' := by
    have h : (fun q => (DirectSum.lof ℤ ℕ (fun k => Additive (GLam (G := G) k))
        (p + q + 1)).toAddMonoidHom.comp (bracketL (G := G) p q 0)) = 0 := by
      funext q
      ext y
      simp
    rw [h, map_zero]
  map_add' a a' := by
    have h : (fun q => (DirectSum.lof ℤ ℕ (fun k => Additive (GLam (G := G) k))
        (p + q + 1)).toAddMonoidHom.comp (bracketL (G := G) p q (a + a'))) =
        (fun q => (DirectSum.lof ℤ ℕ (fun k => Additive (GLam (G := G) k))
          (p + q + 1)).toAddMonoidHom.comp (bracketL (G := G) p q a)) +
        (fun q => (DirectSum.lof ℤ ℕ (fun k => Additive (GLam (G := G) k))
          (p + q + 1)).toAddMonoidHom.comp (bracketL (G := G) p q a')) := by
      funext q
      ext y
      simp [map_add]
    rw [h, map_add]

/-- The graded Lie bracket on `Λbar`, written as a definition. -/
noncomputable def bracketBar : Lbar G →+ (Lbar G →+ Lbar G) :=
  DFinsupp.liftAddHom fun p => bracketBarHom (G := G) p

/-- The bracket of two homogeneous elements. -/
theorem bracketBar_lof (p q : ℕ) (a : Additive (GLam (G := G) p))
    (b : Additive (GLam (G := G) q)) :
    bracketBar (G := G) (DirectSum.lof ℤ ℕ (fun k => Additive (GLam (G := G) k)) p a)
        (DirectSum.lof ℤ ℕ (fun k => Additive (GLam (G := G) k)) q b) =
      DirectSum.lof ℤ ℕ (fun k => Additive (GLam (G := G) k)) (p + q + 1)
        (bracketL (G := G) p q a b) := by
  show (DFinsupp.liftAddHom fun p => bracketBarHom (G := G) p)
      (DFinsupp.single p a) (DFinsupp.single q b) = _
  rw [DFinsupp.liftAddHom_apply_single]
  show (DFinsupp.liftAddHom fun q =>
      (DirectSum.lof ℤ ℕ (fun k => Additive (GLam (G := G) k)) (p + q + 1)).toAddMonoidHom.comp
        (bracketL (G := G) p q a)) (DFinsupp.single q b) = _
  rw [DFinsupp.liftAddHom_apply_single]
  rfl

end graded
end Work.SSGRoute.prop5
