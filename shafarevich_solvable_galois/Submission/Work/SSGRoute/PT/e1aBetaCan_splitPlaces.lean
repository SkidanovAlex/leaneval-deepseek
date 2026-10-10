import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.RepresentationTheory.Rep.Iso
import Mathlib.RepresentationTheory.Rep.Res
import Mathlib.Algebra.Homology.DerivedCategory.Ext.EnoughProjectives
import Submission.Work.SSGRoute.ExtChain.ext2_ct_vanish
import Submission.Work.SSGRoute.PT.e1aBetaCan_aux
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The split places of the landing clause (`e1aBetaCan_le_ker`)

The landing clause reduces (see `PT/NOTE_e1aBetaCan_le_ker.md`) to the vanishing, for every place
`w` of `K`, of the localisation `extLoc w (extToIdeles y)`.  The places split into

* places with `decompK w = ⊥` ("completely split" finite places, and complex places over complex
  places): here the local object `Ext²_{⊥}(res E', K_wˣ)` **vanishes outright** — a module whose
  underlying `ℤ`-module is finitely generated has a two-term free resolution, i.e. projective
  dimension at most `1` over `ℤ` — so *no* local dictionary is needed;
* the remaining (nonsplit) places, where the local chain over the completion is needed.

This file proves the first case: `subsingleton_ext2_of_subsingleton` is the general vanishing
statement for a group whose carrier is a subsingleton (i.e. `H = ⊥`), and
`extLoc_extToIdeles_eq_zero_of_decompK_eq_bot` is the place-by-place form used by the assembly.
-/

namespace Work.SSGRoute.PT

open CategoryTheory SSGRoute.PTExt

noncomputable section

/-! ## `Ext²` of a finite module over the trivial group vanishes -/

/-- **`Ext²` over a group with a subsingleton carrier.**  Such an `H` is trivial, so the underlying
`ℤ`-module of `X` is finitely generated over `ℤ[H] = ℤ` and has projective dimension at most `1`;
hence `Ext²_H(X,U) = 0` for *every* coefficient `U`.

Formally this is `Work.SSGRoute.ExtChain.ext2_ct_vanish` at `↥H`: its cohomological-triviality
hypothesis only has to be checked on the subgroups of `↥H`, which are all `⊥` (and there
`unitRep` is projective, `ℤ` being free over `ℤ`). -/
theorem subsingleton_ext2_of_subsingleton {H : Type} [Group H] [Subsingleton H]
    (X U : Rep.{0} Coeff H) [Module.Finite ℤ X.V] :
    Subsingleton (Abelian.Ext X U 2) := by
  haveI : Fintype H := Fintype.ofSubsingleton 1
  refine Work.SSGRoute.ExtChain.ext2_ct_vanish (G := H) X U ?_
  intro K hKfin n hn
  have hK : K = ⊥ := by
    ext x
    rw [Subgroup.mem_bot]
    exact ⟨fun _ => Subsingleton.elim x 1, fun hx => hx ▸ one_mem K⟩
  rw [hK]
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.pos_iff_ne_zero.mp hn)
  haveI : Projective (Rep.res (⊥ : Subgroup H).subtype (SSGRoute.PTExt.unitRep H)) := by
    rw [show Rep.res (⊥ : Subgroup H).subtype (SSGRoute.PTExt.unitRep H)
        = Rep.trivial Coeff (↥(⊥ : Subgroup H)) Coeff from rfl]
    infer_instance
  exact Abelian.Ext.subsingleton_of_projective _ _ k

/-- **`Ext²` over the trivial subgroup vanishes for finitely generated modules** (the special case
of `subsingleton_ext2_of_subsingleton` used below). -/
theorem subsingleton_ext2_bot {G : Type} [Group G]
    (X U : Rep.{0} Coeff (↥(⊥ : Subgroup G))) [Module.Finite ℤ X.V] :
    Subsingleton (Abelian.Ext X U 2) :=
  subsingleton_ext2_of_subsingleton X U

/-! ## A finite type is a finitely generated `ℤ`-module -/

/-- A `Rep` with finite underlying type has finitely generated underlying `ℤ`-module (the `ℤ`-form
of `Work.SSGRoute.module_finite_coeff_of_finite`). -/
theorem module_finite_int_of_finite {G : Type} [Group G] (X : Rep.{0} Coeff G) [Finite X] :
    Module.Finite ℤ X.V := by
  refine Module.Finite.of_fg_top ?_
  have htop : (⊤ : Submodule ℤ X.V) = Submodule.span ℤ (Set.univ : Set X.V) :=
    (Submodule.span_univ (R := ℤ) (M := X.V)).symm
  rw [htop]
  exact Submodule.fg_span (Set.finite_univ (α := X.V))

/-! ## The split places of the landing clause -/

variable {k : Type} [Field k] [NumberField k] {K : Type} [Field K] [NumberField K] [Algebra k K]
  [FiniteDimensional k K] [IsGalois k K]

/-- **The localisation of `extToIdeles y` vanishes at a place whose decomposition group is
trivial.**  If `decompK w = ⊥` (a completely split finite place, or a complex place over a complex
place), the local object is `Ext²_{⊥}(res M, K_wˣ)`, which vanishes as soon as the underlying
`ℤ`-module of `M` is finitely generated — in particular for `M = E' = DualMod p (E ⊗ T)`.

This is the *split-place* case of the landing clause `Work.SSGRoute.PT.e1aBetaCan_le_ker`: no local
dictionary is needed here. -/
theorem extLoc_extToIdeles_eq_zero_of_decompK_eq_bot
    (M : Rep.{0} Coeff (K ≃ₐ[k] K)) [Finite M]
    (y : Abelian.Ext.{0} M (SSGRoute.PTExt.unitsK k K) 2)
    (w : NK.GlobalCFT.Place K)
    (hw : SSGRoute.PTExt.decompK (k := k) w = ⊥) :
    SSGRoute.PTExt.extLoc (k := k) w (SSGRoute.PTExt.extToIdeles (k := k) y) = 0 := by
  classical
  haveI hfin : Module.Finite ℤ M.V := module_finite_int_of_finite M
  haveI hsubBot : Subsingleton (↥(⊥ : Subgroup (K ≃ₐ[k] K))) :=
    ⟨fun a b => Subtype.ext (by rw [Subgroup.mem_bot.mp a.2, Subgroup.mem_bot.mp b.2])⟩
  haveI hsub : Subsingleton (↥(SSGRoute.PTExt.decompK (k := k) w)) := hw ▸ hsubBot
  haveI : Subsingleton (Abelian.Ext
      (Rep.res (SSGRoute.PTExt.decompK (k := k) w).subtype M)
      (SSGRoute.PTExt.localUnitsK (k := k) w) 2) :=
    subsingleton_ext2_of_subsingleton _ _
  exact Subsingleton.elim _ _

end

end Work.SSGRoute.PT
