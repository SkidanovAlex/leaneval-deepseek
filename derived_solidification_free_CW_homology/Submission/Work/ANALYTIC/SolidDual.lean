import Mathlib
import ChallengeDeps
import Submission.Blueprint.Interfaces
import Submission.Work.ANALYTIC.Basic

/-!
# The solid dual `ℤ■[T] = ihom(C(T,ℤ)_disc, ℤ)` (REFS/03 §4)

For a light profinite set `T`, `ℤ■[T]` is the internal hom of the discrete condensed abelian group
`C(T,ℤ)_disc` of locally constant `ℤ`-valued functions into `ℤ`.  The evaluation pairing
`μ_T : ℤ[T] ⟶ ℤ■[T]` and the Haar/Schauder basis identification `ℤ■[T] ≅ ∏ℤ` (REFS/03 §4) are the
content of AN3; see `Submission/Work/ANALYTIC/README.md` for the route.
-/

open CategoryTheory Limits LightProfinite LightCondensed MonoidalCategory MonoidalClosed

noncomputable section

namespace Work.ANALYTIC

open _root_.LightCondensed _root_.LightCondensed.Solid

theorem Cdiscrete_iso (M : ModuleCat ℤ) :
    Nonempty ((LightCondMod.LocallyConstant.functor ℤ).obj M ≅
      (LightCondensed.discrete (ModuleCat ℤ)).obj M) :=
  ⟨(LightCondMod.LocallyConstant.functorIsoDiscrete ℤ).app M⟩

/-- The discrete light condensed abelian group of locally constant `ℤ`-valued functions on `T`,
modelled through `LightCondMod.LocallyConstant.functor` so that its `S`-points are
*definitionally* the locally constant functions `S → LocallyConstant T ℤ` (see `Cdisc_obj_obj`).
It is isomorphic to `(discrete ℤ).obj (LocallyConstant T ℤ)` (`Cdiscrete_iso`). -/
noncomputable def Cdisc (T : LightProfinite) : LightCondAb :=
  (LightCondMod.LocallyConstant.functor ℤ).obj (ModuleCat.of ℤ (LocallyConstant T ℤ))

/-- The `S`-points of `Cdisc T` are the locally constant functions `S → (T → ℤ)`
(definitionally). -/
theorem Cdisc_obj_obj (T S : LightProfinite) :
    ↥((Cdisc T).obj.obj (Opposite.op S)) = LocallyConstant S (LocallyConstant T ℤ) := rfl

/-- **`ℤ■[T]`**, the solid dual of `ℤ[T]` (REFS/03 §4). -/
noncomputable def solidDual (T : LightProfinite) : LightCondAb :=
  (ihom (Cdisc T)).obj (𝟙_ LightCondAb)

/-- The unit of `LightCondAb` is the discrete condensed `ℤ` (definitionally). -/
theorem unit_eq_Z : (𝟙_ LightCondAb) = Z := rfl

end Work.ANALYTIC
