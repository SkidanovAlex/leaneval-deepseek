/-
AREA TOOLKIT/Levelwise — the morphism of truncation towers induced by a morphism of complexes.
-/
import Submission.Work.TOOLKIT.Levelwise.Tower

open CategoryTheory Limits
open _root_.LightCondensed _root_.LightCondensed.Solid

noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace Work.TOOLKIT.Levelwise

attribute [local simp] CategoryTheory.eqToHom_trans

/-- The morphism of towers `T_•K ⟶ T_•L` induced by `φ : K ⟶ L`. -/
def truncTowerMap {K L : Cpx} (φ : K ⟶ L) : truncTower K ⟶ truncTower L where
  app m := truncMap φ (-(m : ℤ))
  naturality {m n} h := by
    have h' : -(n : ℤ) ≤ -(m : ℤ) := by
      have hmn : m ≤ n := leOfHom h
      omega
    show truncIncl (a := -(n : ℤ)) (b := -(m : ℤ)) h' K ≫ truncMap φ (-(n : ℤ)) =
      truncMap φ (-(m : ℤ)) ≫ truncIncl (a := -(n : ℤ)) (b := -(m : ℤ)) h' L
    exact (truncIncl_naturality h' φ).symm

end Work.TOOLKIT.Levelwise
