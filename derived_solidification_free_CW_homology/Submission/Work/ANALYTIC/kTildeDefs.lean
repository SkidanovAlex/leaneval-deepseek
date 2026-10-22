import Mathlib
import Submission.Work.ANALYTIC.Basic
import Submission.Work.ANALYTIC.boundedSeq_sheaf
import Submission.Work.ATOM.ZS.Unred.LCZ
import Submission.Work.ATOM.Defs

/-!
# Definitions for `Work.ANALYTIC.exists_kTilde`

The target lemma produces a map `zred T s₀ ⟶ prodZ` which is a solid-equivalence.  The map is
given by its coordinates `zred T s₀ ⟶ Z`; these are the "Haar coordinates" of the null sequence
`g : P ⟶ ℤ[T]` of REFS/03 §1, i.e. the functionals obtained from the locally constant functions
`fCyl T j` (`Submission/Work/ANALYTIC/HaarDefs.lean`).

Because the sections of `Z = (discrete (ModuleCat ℤ)).obj ℤ` are *not* definitionally locally
constant functions, we use the isomorphic object `LCZ =
(LightCondMod.LocallyConstant.functor ℤ).obj ℤ` (area ATOM), whose sections *are*
definitionally locally constant functions, and whose isomorphism with `Z` is
`LightCondMod.LocallyConstant.functorIsoDiscrete`.  All the computations are done with `LCZ` and
transported to `Z` at the end.

This file only contains definitions (plus the trivial transport isomorphisms); the proofs live in
`Submission/Work/ANALYTIC/exists_kTilde.lean`.
-/

open CategoryTheory Limits LightProfinite LightCondensed MonoidalCategory MonoidalClosed
open _root_.LightCondensed _root_.LightCondensed.Solid
open Opposite

noncomputable section

namespace Work.ANALYTIC

/-- The isomorphism `Z ≅ LCZ` between the two models of the constant sheaf `ℤ`
(`LightCondMod.LocallyConstant.functor ℤ ≅ discrete`). -/
noncomputable def ZisoLCZ : Z ≅ Work.ATOM.ZS.Unred.LCZ :=
  ((LightCondMod.LocallyConstant.functorIsoDiscrete ℤ).app (ModuleCat.of ℤ ℤ)).symm

/-- The product `∏_{n : ℕ} LCZ`, the `LCZ`-model of `prodZ = ∏ᶜ (fun _ : ℕ => Z)`. -/
abbrev prodLCZ : LightCondAb := ∏ᶜ (fun _ : ℕ => Work.ATOM.ZS.Unred.LCZ)

/-- `prodZ = ∏ᶜ Z` is isomorphic to `∏ᶜ LCZ`, coordinatewise. -/
noncomputable def prodZisoProdLCZ : prodZ ≅ prodLCZ :=
  Limits.Pi.mapIso fun _ : ℕ => ZisoLCZ

/-- The `j`-th coordinate projection of `∏^bnd ℤ`, landing in the `LCZ`-model of `ℤ`.  On
`S`-points it sends a (uniformly bounded) family of continuous functions to its `j`-th member,
viewed as a locally constant function. -/
noncomputable def coordLCZ (j : ℕ) : boundedSeq ⟶ Work.ATOM.ZS.Unred.LCZ where
  hom :=
    { app := fun S => ModuleCat.ofHom
        { toFun := fun x =>
            ⟨fun s => x.1 j s,
              (IsLocallyConstant.iff_continuous (fun s => x.1 j s)).mpr (x.1 j).continuous⟩
          map_add' := fun a b => by
            apply LocallyConstant.ext
            intro s
            rfl
          map_smul' := fun c a => by
            apply LocallyConstant.ext
            intro s
            rfl }
      naturality := fun S T f => by
        apply ModuleCat.hom_ext
        apply LinearMap.ext
        intro x
        apply LocallyConstant.ext
        intro s
        rfl }

end Work.ANALYTIC
