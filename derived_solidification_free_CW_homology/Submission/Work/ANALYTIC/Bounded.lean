import Mathlib
import ChallengeDeps
import Submission.Blueprint.Interfaces

/-!
# The presheaf of uniformly bounded sequences `∏^bnd ℤ`

`∏^bnd ℤ ⊆ ∏_ℕ ℤ` is the subobject whose `S`-points are the families `(x_n)_{n : ℕ}` of continuous
functions `S → ℤ` whose coordinates are *uniformly* bounded (REFS/03 §2).  This file only defines
the underlying presheaf; the sheaf condition (which promotes it to a light condensed abelian group
`boundedSeq`) is proved in `Submission/Work/ANALYTIC/boundedSeq_sheaf.lean`.
-/

open CategoryTheory Limits LightProfinite LightCondensed MonoidalCategory MonoidalClosed

noncomputable section

namespace Work.ANALYTIC

open _root_.LightCondensed _root_.LightCondensed.Solid

/-- The ℤ-submodule of uniformly bounded families of continuous functions `S → ℤ`. -/
def boundedSeqSet (S : LightProfinite) : Submodule ℤ (ℕ → C(S, ℤ)) where
  carrier := {x | ∃ N : ℤ, ∀ n : ℕ, ∀ s : S, |x n s| ≤ N}
  add_mem' := by
    rintro x y ⟨Nx, hx⟩ ⟨Ny, hy⟩
    exact ⟨Nx + Ny, fun n s => (abs_add_le _ _).trans (add_le_add (hx n s) (hy n s))⟩
  zero_mem' := ⟨0, by intro n s; simp⟩
  smul_mem' := by
    rintro c x ⟨N, hx⟩
    refine ⟨|c| * max N 0, fun n s => ?_⟩
    calc |(c • x n) s| = |c| * |x n s| := by simp [abs_mul]
      _ ≤ |c| * max N 0 := by
          exact mul_le_mul_of_nonneg_left ((hx n s).trans (le_max_left N 0)) (abs_nonneg c)

/-- The presheaf of uniformly bounded sequences of continuous `ℤ`-valued functions. -/
def boundedPresheaf : LightProfiniteᵒᵖ ⥤ ModuleCat ℤ where
  obj S := ModuleCat.of ℤ (boundedSeqSet S.unop)
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
