/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Mathlib
import Submission.Work.Subdivision.SubDataQuot
import Submission.Work.Subdivision.incl_proj

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# The sub-quotient short complex of a chain complex of `ℤ`-modules is short exact

For a chain complex `C` of `ℤ`-modules and a subcomplex `S` (degreewise submodules
closed under the differential, `SubData`), the short complex

`0 ⟶ S.chain ⟶ C ⟶ S.quot ⟶ 0`

is short exact.  This is the algebraic input for the skeletal induction comparing
the cellular chain complex with its barycentric subdivision: the quotients of the
skeletal filtrations are identified by the five lemma, and for that the filtration
sequences have to be short exact.

## Proof

Short exactness of a short complex of homological complexes can be checked
degreewise (`HomologicalComplex.shortExact_of_degreewise_shortExact`): it suffices
to know, in each degree `k`, that the sequence of `ℤ`-modules

`0 ⟶ ↥(S.sub k) ⟶ C.X k ⟶ C.X k ⧸ S.sub k ⟶ 0`

is short exact.  Its two maps are `Submodule.subtype (S.sub k)` and
`Submodule.mkQ (S.sub k)` (up to the canonical identification of the `k`-th
component of `S.incl`, `S.proj` with those linear maps, `SubData.incl_f`,
`SubData.proj_f`).  Exactness in the middle is
`range (S.sub k).subtype = S.sub k = ker (S.sub k).mkQ`
(`Submodule.range_subtype`, `Submodule.ker_mkQ`), the first map is injective and
the second surjective.

Because `S.chain.X k` and `↥(S.sub k)` (and `S.quot.X k` and `C.X k ⧸ S.sub k`)
are only *definitionally* equal — the `chain`, `quot` constructions are not
reducible — the statement-level reasoning has to unfold these definitions inside
the equalities of submodules, which is what the transparency option below
permits.  The three degreewise ingredients are proved first as standalone lemmas
(where the ambiguity of the `ℤ`-module instance on a submodule and a quotient
module is not an issue), and are then transported to the degreewise short
complexes in the main argument.
-/

namespace Work.Subdivision

open CategoryTheory

variable {C : ChainComplex (ModuleCat ℤ) ℕ}

namespace SubData

variable (S : SubData C)

/-- The `k`-th component of the inclusion of a subcomplex is a monomorphism: in
degree `k` it is the subtype of the submodule `S.sub k`, which is injective. -/
theorem incl_f_mono (k : ℕ) : Mono (S.incl.f k) := by
  rw [ModuleCat.mono_iff_injective]
  intro x y h
  exact Subtype.ext h

/-- The `k`-th component of the projection onto the quotient complex is an
epimorphism: in degree `k` it is the quotient map `C.X k → C.X k ⧸ S.sub k`,
which is surjective. -/
theorem proj_f_epi (k : ℕ) : Epi (S.proj.f k) := by
  rw [ModuleCat.epi_iff_surjective]
  intro x
  obtain ⟨y, rfl⟩ := Quotient.exists_rep x
  exact ⟨y, rfl⟩

set_option backward.isDefEq.respectTransparency false in
/-- Exactness of the sequence `S.sub k ⟶ C.X k ⟶ C.X k ⧸ S.sub k` in degree `k`:
the range of the `k`-th component of the inclusion is the kernel of the `k`-th
component of the projection. -/
theorem incl_f_range_eq_proj_f_ker (k : ℕ) :
    (S.incl.f k).hom.range = (S.proj.f k).hom.ker := by
  rw [SubData.incl_f_hom S k, SubData.proj_f_hom S k, Submodule.range_subtype,
    Submodule.ker_mkQ]

end SubData

set_option backward.isDefEq.respectTransparency false in
theorem shortComplexOf_shortExact {C : ChainComplex (ModuleCat ℤ) ℕ} (S : SubData C)
    (w : CategoryTheory.CategoryStruct.comp S.incl S.proj = 0) :
    (S.shortComplexOf w).ShortExact := by
  apply HomologicalComplex.shortExact_of_degreewise_shortExact
  intro k
  refine ShortComplex.ShortExact.mk' ?_ ?_ ?_
  · rw [ShortComplex.moduleCat_exact_iff_range_eq_ker]
    exact SubData.incl_f_range_eq_proj_f_ker S k
  · rw [ModuleCat.mono_iff_injective]
    intro x y h
    exact Subtype.ext h
  · rw [ModuleCat.epi_iff_surjective]
    intro x
    obtain ⟨y, rfl⟩ := Quotient.exists_rep x
    exact ⟨y, rfl⟩

end Work.Subdivision
