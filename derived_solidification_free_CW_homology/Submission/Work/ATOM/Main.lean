import Submission.Work.ATOM.Defs
import Submission.Work.ATOM.Assembly
import Submission.Work.ATOM.solidCofibrant_atom_of_finite
import Submission.Work.ATOM.solidCofibrant_singleC_biprod
import Submission.Work.ATOM.zfree_iso_pt_biprod_zred
import Submission.Work.ATOM.flatProp_tensorLeft_P
import Submission.Work.ATOM.ZS.SchemeAssembly
import Submission.Work.ATOM.ZS.NullSeqMaps
import Submission.Work.ATOM.ZS.h_one
import Submission.Work.ATOM.ZS.h_two
import Submission.Work.ATOM.ZS.h_three
import Submission.Work.ATOM.ZS.h_four
import Submission.Work.ATOM.ZS.h_five
import Submission.Work.ATOM.ZS.h_seven
import Submission.Work.FLAT.Main

/-!
# AREA ATOM — `ℤ[S]` is solid-cofibrant

`Submission.Blueprint.AtomProp` states that for every light profinite set `S` and every `n : ℤ`,
the atom `ℤ[S]` in cohomological degree `n` is *solid-cofibrant*: for every complex `N` of solid
objects, `DerivedCategory.Qh` is a bijection on
`Hom_K(singleC n ℤ[S], ιC N) → Hom_D(Q singleC n ℤ[S], Q ιC N)`.

What this directory proves:

* the finite case (`Work.ATOM.solidCofibrant_atom_of_finite`): for finite `S`, `ℤ[S]` is a finite
  coproduct of copies of `ℤ`, hence projective, hence K-projective;
* the *assembly* (`Work.ATOM.solidCofibrant_of_bijective_pre` and
  `Work.ATOM.solidCofibrant_singleC_of_iso`): if for some `g : P ⟶ ℤ[S]` precomposition with
  `singleC n g` is bijective on the relevant `Hom_K`- and `Hom_D`-groups of every complex of solid
  objects (which is what the null-sequence trick of REFS/03 §1 produces), then `singleC n ℤ[S]` is
  solid-cofibrant.  The only non-formal inputs are `singleC n P` being K-projective
  (`Work.ATOM.projective_P`) and the naturality square of `Qh`
  (`Work.ATOM.bijective_pre_map_qci`);
* F7 (`Work.ATOM.pre_oneMinusShift_bijective`, `Work.ATOM.homD_pre_oneMinusShift_bijective`,
  `Work.ATOM.homK_pre_oneMinusShift_bijective`): for solid targets `(1-S) ⊗ id` acts invertibly on
  homomorphisms out of `P ⊗ -`, in `LightCondAb`, in `K(LightCondAb)` and in `D(LightCondAb)`.

`Work.ATOM.atom_prop` below is the main theorem of the area.  For infinite `S` the null sequence
`g : P ⟶ ℤ[S]` of REFS/03 §1 is built in `Submission/Work/ATOM/ZS/NullSeqMaps.lean` from the
explicit continuous maps of `Submission/Work/ATOM/ZS/Topo/` (the cover `T' = {(j,a_j)} ∪ {∞}×S`,
`ẽ`, `β`, `ψ`, `φ_P`), the descent lemmas of `Submission/Work/ATOM/Toolkit/`, and the combinatorial
input `Work.ATOM.exists_level_enumeration` (the level function and the enumeration of `⋃ A_n`);
the seven identities of the scheme (`Work.ATOM.ZS.h_one` … `Work.ATOM.ZS.h_seven`, `Work.ATOM.h_six`)
then feed into `Work.ATOM.solidCofibrant_zred_of_schemeData`
(`Submission/Work/ATOM/ZS/SchemeAssembly.lean`), which shows that the reduced object
`ℤ̃[S] = ℤ[S]/ℤ[s₀]` is solid-cofibrant, and the splitting `ℤ[S] ≅ ℤ[*] ⊞ ℤ̃[S]` transfers this
back to `ℤ[S]`.

`Work.ATOM.atom_prop_of_infiniteData` is an earlier (unused) interface with the same content,
stated as a hypothesis on `g`.
-/

open CategoryTheory Limits LightProfinite LightCondensed MonoidalCategory MonoidalClosed
open _root_.LightCondensed _root_.LightCondensed.Solid

noncomputable section

namespace Work.ATOM

/-- `tensorLeft P` is left exact (`P` is flat): `Work.ATOM.flatProp_tensorLeft_P` applied to the
FLAT area's `FlatProp`. -/
theorem flat_tensorLeft_P :
    CategoryTheory.Limits.PreservesFiniteLimits (MonoidalCategory.tensorLeft P) :=
  flatProp_tensorLeft_P Work.FLAT.flat_prop

/-- **AREA ATOM, assembly.**  Given, for every infinite light profinite set `S` and every degree
`n`, a map `g : P ⟶ ℤ[S]` whose precomposition with `singleC n g` is bijective on the `Hom_K`- and
`Hom_D`-groups of every complex of solid objects (the output of the null-sequence construction of
REFS/03 §1), the atom on every light profinite set is solid-cofibrant. -/
theorem atom_prop_of_infiniteData (hflat : Submission.Blueprint.FlatProp)
    (h : ∀ (S : LightProfinite.{0}) [Infinite S] (n : ℤ), ∃ g : P ⟶ zfree S,
      (∀ N : CochainComplex Solid ℤ,
        Function.Bijective (fun φ : hq.obj ((singleC n).obj (zfree S)) ⟶ hq.obj (Submission.Blueprint.ιC.obj N) =>
          hq.map ((singleC n).map g) ≫ φ)) ∧
      (∀ N : CochainComplex Solid ℤ,
        Function.Bijective (fun ψ : DerivedCategory.Q.obj ((singleC n).obj (zfree S)) ⟶
            DerivedCategory.Q.obj (Submission.Blueprint.ιC.obj N) =>
          DerivedCategory.Q.map ((singleC n).map g) ≫ ψ))) :
    Submission.Blueprint.AtomProp := by
  intro S n
  by_cases hS : Finite S
  · haveI := hS
    exact solidCofibrant_atom_of_finite S n
  · haveI : Infinite S := not_finite_iff_infinite.mp hS
    haveI hlim := flatProp_tensorLeft_P hflat
    obtain ⟨g, hK, hD⟩ := h S n
    exact solidCofibrant_of_bijective_pre (zfree S) g n hK hD

/-! ## The main theorem of the area -/

open CategoryTheory Limits LightProfinite LightCondensed MonoidalCategory MonoidalClosed
open _root_.LightCondensed _root_.LightCondensed.Solid

/-- **AREA ATOM**: for every light profinite set `S` and every degree `n`, the atom `ℤ[S]` in
degree `n` is solid-cofibrant.

For finite `S` this is `Work.ATOM.solidCofibrant_atom_of_finite` (`ℤ[S]` is then a finite
coproduct of copies of `ℤ`, hence projective).  For infinite `S` the null sequence
`Work.ATOM.g : P ⟶ ℤ[S]` of REFS/03 §1 is a "solid-equivalence" test object: the seven identities
`h₁`–`h₇` of `Work.ATOM.ZS` feed into `Work.ATOM.solidCofibrant_zred_of_schemeData`, which shows
that the reduced free object `ℤ̃[S] = ℤ[S]/ℤ[s₀]` is solid-cofibrant; the splitting
`ℤ[S] ≅ ℤ[*] ⊞ ℤ̃[S]` (`Work.ATOM.zfree_iso_pt_biprod_zred`) transfers this back to `ℤ[S]`
(`Work.ATOM.solidCofibrant_singleC_biprod`). -/
theorem atom_prop : Submission.Blueprint.AtomProp := by
  intro S n
  by_cases hS : Finite S
  · exact solidCofibrant_atom_of_finite S n
  · haveI : Infinite S := not_finite_iff_infinite.mp hS
    haveI : CategoryTheory.Limits.PreservesFiniteLimits
        (CategoryTheory.MonoidalCategory.tensorLeft P) := flat_tensorLeft_P
    have hred : Submission.Blueprint.SolidCofibrant
        ((singleC n).obj (zred S (levelData S).s₀)) :=
      solidCofibrant_zred_of_schemeData S n (gRed S) (F S) (s S) (G S) (FP S) sP (m S)
        (ZS.h_one S) (ZS.h_two S) (ZS.h_three S) (ZS.h_four S) (ZS.h_five S) (h_six S)
        (ZS.h_seven S)
    obtain ⟨e⟩ := zfree_iso_pt_biprod_zred S (levelData S).s₀
    have hpt : Submission.Blueprint.SolidCofibrant ((singleC n).obj (zfree pt)) :=
      solidCofibrant_atom_of_finite pt n
    exact solidCofibrant_singleC_of_iso n e.symm (solidCofibrant_singleC_biprod n hpt hred)

end Work.ATOM
