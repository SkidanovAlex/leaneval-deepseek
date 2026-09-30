/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Mathlib
import Submission.Work.Subdivision.SkelLevel

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


-- The `haveI` style linter fires on the local instances of this file, which are
-- genuinely used for instance resolution.
set_option linter.style.haveILetI false

/-!
# Quasi-isomorphisms of the subdivision from the maximal skeleton

The subdivision chain map `PolyCW.subdiv : cellChain P ⟶ sdChain P` is compared
with the skeletal filtrations `PolyCW.cellSub n ⊆ cellChain P` and
`PolyCW.sdSub n ⊆ sdChain P` (`Filtration.lean`), whose restrictions are
`PolyCW.subdivSkel n : (cellSub n).chain ⟶ (sdSub n).chain` (`SkelLevel.lean`).

At the maximal dimension `n = P.maxDim` the two filtrations are everything: every
`k`-chain of the cellular complex is a chain of cells of dimension `k ≤ maxDim`
(in a degree above `maxDim` there are no such cells at all, so the chain module
is trivial), and every simplex of the subdivision has all its vertices of
dimension `≤ maxDim`.  Hence the two inclusions
`(cellSub maxDim).incl` and `(sdSub maxDim).incl` are isomorphisms, and the
naturality square

`(cellSub maxDim).incl ≫ subdiv = subdivSkel maxDim ≫ (sdSub maxDim).incl`

identifies `subdiv` with `subdivSkel maxDim` up to isomorphisms.  Consequently a
quasi-isomorphism on the maximal skeleton is a quasi-isomorphism of the whole
subdivision, which is the statement requested here:

`Work.Subdivision.quasiIso_subdiv_of_maxDim`.

This is the last step of the skeletal induction of `SkelInduction.lean`: with
`subdivSkel_quasiIso` (base case `subdivSkel_zero`, step `subdivSkel_succ`) it
turns quasi-isomorphisms of the skeleton maps into a quasi-isomorphism of
`subdiv`.
-/

namespace Work.Subdivision

open CategoryTheory

universe u

variable {C C' : ChainComplex (ModuleCat ℤ) ℕ}

/-! ### The filtrations at the maximal dimension are everything -/

/-- At the maximal dimension the skeletal filtration on the subdivided chain
complex is everything: every vertex of a simplex of the subdivision is a cell of
dimension at most `maxDim`. -/
theorem sdSubMod_maxDim (P : PolyCW) (k : ℕ) : P.sdSubMod P.maxDim k = ⊤ := by
  rw [eq_top_iff]
  intro x _
  rw [← Finsupp.sum_single x]
  refine Submodule.sum_mem _ fun σ _ => ?_
  rw [← Finsupp.smul_single_one σ ((show Simplex P.Cell k →₀ ℤ from x) σ)]
  exact Submodule.smul_mem _ _ (P.sdElem_mem_sdSubMod fun i => P.dim_le_maxDim (σ i))

/-- At the maximal dimension the skeletal filtration on the cellular chain
complex is everything.  In degree `k ≤ maxDim` this is the definition of the
truncation; in degree `k > maxDim` there is no cell of dimension `k`, so the
chain module is trivial and `⊥ = ⊤`. -/
theorem cellSubMod_maxDim (P : PolyCW) (hdd : P.HasDdZero) (k : ℕ) :
    P.cellSubMod hdd P.maxDim k = ⊤ := by
  by_cases hk : k ≤ P.maxDim
  · rw [PolyCW.cellSubMod, ite_eq_left hk]
  · rw [PolyCW.cellSubMod, ite_eq_right hk]
    rw [eq_top_iff]
    intro x _
    rw [Submodule.mem_bot]
    haveI : IsEmpty {e : P.Cell // P.dim e = k} :=
      ⟨fun e => hk (e.2 ▸ P.dim_le_maxDim e.1)⟩
    exact Subsingleton.elim (α := {e : P.Cell // P.dim e = k} →₀ ℤ) x 0

/-- If a subcomplex consists of everything in every degree, its inclusion into
the ambient complex is an isomorphism. -/
theorem isIso_incl_of_sub_eq_top (S : SubData C) (hS : ∀ k, S.sub k = ⊤) :
    IsIso S.incl := by
  haveI : ∀ k, IsIso (S.incl.f k) := fun k => by
    rw [S.incl_f k, ConcreteCategory.isIso_iff_bijective]
    refine ⟨fun a b h => Subtype.ext h, fun y => ⟨⟨y, ?_⟩, rfl⟩⟩
    rw [hS k]
    exact trivial
  exact HomologicalComplex.Hom.isIso_of_components S.incl

/-- **Transport of quasi-isomorphisms across an isomorphism square.**  If
`e.hom ≫ f = f' ≫ e'.hom` with `e`, `e'` isomorphisms, then `f` is a
quasi-isomorphism as soon as the "small" map `f'` is.  (This is the direction
used to deduce that the subdivision is a quasi-isomorphism from the maximal
skeleton: `f` is `subdiv` and `f'` is `subdivSkel maxDim`.) -/
theorem quasiIso_of_iso_square_of_small {A B A' B' : ChainComplex (ModuleCat ℤ) ℕ}
    (e : A ≅ A') (e' : B ≅ B') (f : A' ⟶ B') (f' : A ⟶ B)
    (h : e.hom ≫ f = f' ≫ e'.hom) (hf' : QuasiIso f') : QuasiIso f := by
  have h1 : f = e.inv ≫ f' ≫ e'.hom := by
    calc f = 𝟙 _ ≫ f := (Category.id_comp f).symm
      _ = (e.inv ≫ e.hom) ≫ f := by rw [e.inv_hom_id]
      _ = e.inv ≫ (e.hom ≫ f) := by rw [Category.assoc]
      _ = e.inv ≫ (f' ≫ e'.hom) := by rw [h]
      _ = e.inv ≫ f' ≫ e'.hom := rfl
  rw [h1]
  haveI : QuasiIso f' := hf'
  infer_instance

/-! ### The naturality square of the skeletal restriction -/

namespace PolyCW

variable (P : PolyCW.{u})

/-- **The naturality square of the restriction of the subdivision to the
`n`-skeleton**: the composite of `subdivSkel n` with the inclusion of the
subdivided skeleton is the composite of the inclusion of the cellular skeleton
with `subdiv`. -/
theorem subdivSkel_incl (hdd : P.HasDdZero) (haug : P.HasAugZero) (n : ℕ) :
    (P.cellSub hdd n).incl ≫ P.subdiv hdd haug =
      P.subdivSkel hdd haug n ≫ (P.sdSub n).incl := by
  rw [show P.subdivSkel hdd haug n =
      (P.cellSub hdd n).restrictMap (P.sdSub n) (P.subdiv hdd haug)
        (fun k => subdivCpt_mem P hdd haug n k) from rfl]
  apply HomologicalComplex.hom_ext
  intro k
  rw [HomologicalComplex.comp_f, HomologicalComplex.comp_f, SubData.incl_f_eq, SubData.incl_f_eq]
  exact incl_restrictCptMap (P.cellSub hdd n) (P.sdSub n) (P.subdiv hdd haug)
    (fun k => subdivCpt_mem P hdd haug n k) k

end PolyCW

/-! ### The statement -/

theorem quasiIso_subdiv_of_maxDim (P : Work.Subdivision.PolyCW) (hdd : P.HasDdZero) (haug : P.HasAugZero)
    (h : QuasiIso (Work.Subdivision.PolyCW.subdivSkel P hdd haug P.maxDim)) :
    QuasiIso (Work.Subdivision.PolyCW.subdiv P hdd haug) := by
  haveI : IsIso (P.cellSub hdd P.maxDim).incl :=
    isIso_incl_of_sub_eq_top (P.cellSub hdd P.maxDim) (cellSubMod_maxDim P hdd)
  haveI : IsIso (P.sdSub P.maxDim).incl :=
    isIso_incl_of_sub_eq_top (P.sdSub P.maxDim) (sdSubMod_maxDim P)
  exact quasiIso_of_iso_square_of_small (asIso (P.cellSub hdd P.maxDim).incl)
    (asIso (P.sdSub P.maxDim).incl) (P.subdiv hdd haug) (P.subdivSkel hdd haug P.maxDim)
    (PolyCW.subdivSkel_incl P hdd haug P.maxDim) h

end Work.Subdivision
