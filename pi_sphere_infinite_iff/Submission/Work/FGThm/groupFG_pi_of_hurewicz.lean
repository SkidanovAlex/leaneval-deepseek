import Mathlib
import Submission.Work.PiS.Interfaces
import Submission.Work.Stems.HurewiczFirstDegree

/-!
# `π_{n+2}` is finitely generated in the first non-vanishing degree

If `X` is `(n+1)`-connected (all `πᵢ(X,x)` for `i < n+2` trivial) and `H_{n+2}(X;ℤ)` is a finitely
generated abelian group, then `π_{n+2}(X,x)` is finitely generated.

This is the corollary of the integral Hurewicz theorem in the first non-vanishing degree
(`Work.Stems.hurewicz_first_degree`): the Hurewicz map `h : π_{n+2}(X,x) → H_{n+2}(X;ℤ)` is
bijective, and it is additive (`hurewiczMapN_mul`), so it is an isomorphism of groups; finite
generatedness transfers along it.
-/

namespace Work.FGThm

open CategoryTheory

/-- The codomain of the Hurewicz map at degree `n+2` is definitionally `Work.PiS.HZ X (n+2)`. -/
theorem chains_homology_eq_HZ {X : Type} [TopologicalSpace X] (n : ℕ) :
    (Work.Stems.chains (TopCat.of X)).homology (n + 1 + 1) = Work.PiS.HZ X (n + 1 + 1) := rfl

theorem groupFG_pi_of_hurewicz {X : Type} [TopologicalSpace X] (x : X) (n : ℕ)
    (hconn : ∀ i : ℕ, i < n + 1 + 1 → Subsingleton (HomotopyGroup (Fin i) X x))
    (hfin : Module.Finite ℤ (Work.PiS.HZ X (n + 1 + 1))) :
    Group.FG (HomotopyGroup (Fin (n + 1 + 1)) X x) := by
  -- The Hurewicz map is bijective by the Hurewicz theorem in the first non-vanishing degree.
  have hbij : Function.Bijective (Work.Stems.hurewiczMapN (n + 1 + 1) (by omega) x) :=
    Work.Stems.hurewicz_first_degree (n + 1 + 1) (by omega) x hconn
  -- It kills the unit: `h 1 = h 1 + h 1`.
  have hmap_one : Work.Stems.hurewiczMapN (n + 1 + 1) (by omega) x
      (1 : HomotopyGroup (Fin (n + 1 + 1)) X x) = 0 := by
    have h := Work.Stems.hurewiczMapN_mul (n + 1) x
      (1 : HomotopyGroup (Fin (n + 1 + 1)) X x) 1
    rw [mul_one] at h
    exact add_left_cancel (show _ + _ = _ + 0 by rw [add_zero]; exact h.symm)
  -- The Hurewicz map as an additive homomorphism out of `Additive π`.
  let f : Additive (HomotopyGroup (Fin (n + 1 + 1)) X x) →+
      ↥(Work.PiS.HZ X (n + 1 + 1)) :=
    { toFun := fun a => Work.Stems.hurewiczMapN (n + 1 + 1) (by omega) x (Additive.toMul a)
      map_zero' := hmap_one
      map_add' := fun a b => Work.Stems.hurewiczMapN_mul (n + 1) x
        (Additive.toMul a) (Additive.toMul b) }
  have hf : Function.Bijective f := by
    constructor
    · intro a b hab
      exact Additive.toMul.injective (hbij.1 hab)
    · intro y
      obtain ⟨c, hc⟩ := hbij.2 y
      exact ⟨Additive.ofMul c, hc⟩
  -- Transfer finite generation along the resulting additive equivalence.
  let e : Additive (HomotopyGroup (Fin (n + 1 + 1)) X x) ≃+ ↥(Work.PiS.HZ X (n + 1 + 1)) :=
    AddEquiv.ofBijective f hf
  have hfg : AddGroup.FG ↥(Work.PiS.HZ X (n + 1 + 1)) := by
    have heq : (Work.PiS.HZ X (n + 1 + 1)).isModule =
        (AddCommGroup.toIntModule ↥(Work.PiS.HZ X (n + 1 + 1)) :
          Module ℤ ↥(Work.PiS.HZ X (n + 1 + 1))) := Subsingleton.elim _ _
    have h' : @Module.Finite ℤ ↥(Work.PiS.HZ X (n + 1 + 1)) _ _
        (AddCommGroup.toIntModule ↥(Work.PiS.HZ X (n + 1 + 1))) := heq ▸ hfin
    exact Module.Finite.iff_addGroup_fg.mp h'
  have hfg' : AddGroup.FG (Additive (HomotopyGroup (Fin (n + 1 + 1)) X x)) :=
    AddGroup.fg_of_surjective (hG := hfg) (f := e.symm.toAddMonoidHom) e.symm.surjective
  exact GroupFG.iff_add_fg.mpr hfg'

end Work.FGThm
