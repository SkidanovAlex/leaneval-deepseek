import Mathlib

namespace Work.DSF1.Sheaf

open AlgebraicGeometry CategoryTheory Opposite

theorem isUnit_res_of_le_basicOpen {X : AlgebraicGeometry.Scheme} {U : X.Opens}
    (hU : AlgebraicGeometry.IsAffineOpen U) (g : ↥(X.presheaf.obj (Opposite.op ⊤)))
    (h : U ≤ X.basicOpen g) :
    IsUnit ((X.presheaf.map (CategoryTheory.homOfLE (le_top : U ≤ ⊤)).op).hom g) := by
  let s : Γ(X, U) := (X.presheaf.map (homOfLE le_top).op).hom g
  -- The stalk of the restriction of `g` to `U` agrees with the stalk of `g`.
  have hgerm : ∀ (x : U), X.presheaf.germ U x x.2 s = X.presheaf.germ ⊤ x trivial g := by
    intro x
    convert X.presheaf.germ_res_apply (homOfLE le_top) x x.2 g using 2
  -- Hence `s` is nowhere vanishing on the affine open `U`.
  have hbasic : X.basicOpen s = U := by
    refine le_antisymm (X.basicOpen_le s) ?_
    intro x hx
    rw [X.mem_basicOpen s x hx, hgerm ⟨x, hx⟩]
    exact (X.mem_basicOpen_top g x).mp (h hx)
  -- For an affine open, `basicOpen s = U` forces `s` to be a unit.
  have hspan : Ideal.span ({s} : Set Γ(X, U)) = ⊤ := by
    refine (hU.self_le_iSup_basicOpen_iff (s := ({s} : Set Γ(X, U)))).mp ?_
    exact hbasic.ge.trans (le_iSup (fun f : ({s} : Set Γ(X, U)) => X.basicOpen f.1) ⟨s, rfl⟩)
  exact Ideal.span_singleton_eq_top.mp hspan

end Work.DSF1.Sheaf
