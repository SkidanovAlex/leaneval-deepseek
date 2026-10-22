import Mathlib
import ChallengeDeps
import Submission.Blueprint.Interfaces
import Submission.Work.ANALYTIC.Basic
import Submission.Work.ANALYTIC.Bounded
import Submission.Work.ANALYTIC.ProdZ
import Submission.Work.ANALYTIC.RealCond

/-!
# The ℝ-valued analogues of `∏_ℕ ℤ` and `∏^bnd ℤ` (AN2, REFS/03 §3)

This file contains the *presheaf*-level definitions of the ℝ-valued analogues of
`Work.ANALYTIC.prodZPresheaf` and `Work.ANALYTIC.boundedPresheaf`:

* `prodRealPresheaf` is the presheaf `S ↦ (ℕ → C(S,ℝ))` (a model of `∏_ℕ ℝ`);
* `boundedRealPresheaf` is the presheaf of uniformly bounded families of continuous real-valued
  functions (`∏^bnd ℝ`).

The sheaf conditions (which promote these to light condensed abelian groups) are proved in
`Submission/Work/ANALYTIC/prodReal_sheaf.lean` and
`Submission/Work/ANALYTIC/boundedReal_sheaf.lean`, and the resulting objects `prodReal`,
`boundedReal` together with the inclusions and the quotient `realQuot = ∏ℝ/∏^bndℝ` are defined in
`Submission/Work/ANALYTIC/RealSide.lean`.

The purpose of the ℝ-side (AN2, REFS/03 §3) is that `∏ℝ/∏^bndℝ` carries a unital action of the
light condensed ring `ℝ`, whence it is solid-null (RC Thm 3.2.4(4)), while
`∏ℤ/∏^bndℤ = ∏ℝ/∏^bndℝ` by the snake lemma; this is the second half of AN2.
-/

open CategoryTheory Limits LightProfinite LightCondensed MonoidalCategory MonoidalClosed
open Opposite

noncomputable section

namespace Work.ANALYTIC

open _root_.LightCondensed _root_.LightCondensed.Solid

/-- The presheaf of `ℕ`-indexed families of continuous `ℝ`-valued functions; it is a model of
`∏_ℕ ℝ` (the ℝ-valued analogue of `Work.ANALYTIC.prodZPresheaf`). -/
def prodRealPresheaf : LightProfiniteᵒᵖ ⥤ ModuleCat ℤ where
  obj S := ModuleCat.of ℤ (ℕ → C(S.unop, ℝ))
  map f := ModuleCat.ofHom
    { toFun := fun x n => (x n).comp (LightProfinite.toTopCat.map f.unop).hom
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  map_id _ := rfl
  map_comp _ _ := rfl

/-- The `ℤ`-submodule of uniformly bounded families of continuous functions `S → ℝ`
(the ℝ-valued analogue of `Work.ANALYTIC.boundedSeqSet`). -/
def boundedRealSet (S : LightProfinite) : Submodule ℤ (ℕ → C(S, ℝ)) where
  carrier := {x | ∃ N : ℝ, ∀ n : ℕ, ∀ s : S, |x n s| ≤ N}
  add_mem' := by
    rintro x y ⟨Nx, hx⟩ ⟨Ny, hy⟩
    exact ⟨Nx + Ny, fun n s => (abs_add_le _ _).trans (add_le_add (hx n s) (hy n s))⟩
  zero_mem' := ⟨0, by intro n s; simp⟩
  smul_mem' := by
    rintro c x ⟨N, hx⟩
    refine ⟨|(c : ℝ)| * max N 0, fun n s => ?_⟩
    calc |(c • x n) s| = |(c : ℝ)| * |x n s| := by simp [abs_mul]
      _ ≤ |(c : ℝ)| * max N 0 := by
          exact mul_le_mul_of_nonneg_left ((hx n s).trans (le_max_left N 0))
            (abs_nonneg (c : ℝ))

/-- The presheaf of uniformly bounded families of continuous `ℝ`-valued functions
(the ℝ-valued analogue of `Work.ANALYTIC.boundedPresheaf`). -/
def boundedRealPresheaf : LightProfiniteᵒᵖ ⥤ ModuleCat ℤ where
  obj S := ModuleCat.of ℤ (boundedRealSet S.unop)
  map {S T} f := ModuleCat.ofHom
    { toFun := fun x =>
        ⟨fun n => (x.1 n).comp (LightProfinite.toTopCat.map f.unop).hom,
          x.2.imp fun N hN n s => hN n _⟩
      map_add' := fun _ _ => Subtype.ext rfl
      map_smul' := fun _ _ => Subtype.ext rfl }
  map_id S := by
    ext x n : 1
    rfl
  map_comp {S T U} f g := by
    ext x n : 1
    rfl

end Work.ANALYTIC
