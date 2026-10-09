import Submission.NK.ResidueFrob.Basic
import Submission.NK.ResidueFrob.mem_inertiaSubgroup_of_fixes_rootsOfUnity
import Submission.NK.ResidueFrob.exists_mem_decompositionGroup_restrictNormalHom_eq
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The level inertia subgroups are the images of the local inertia subgroup

The third field of `NK.FrobeniusBridge.PlaceLevelBridgeCore` says that every element of
`Gal(K'/K)` acting trivially on the residue field of a finite normal level `L` at the prime below
the place `A` agrees on `L` with an element of the decomposition group `D_A` whose image under the
local identification `D_A ≃* Gal(κ̄/κ)` lies in the local inertia subgroup `I_κ`.

This file sets up the vocabulary of that statement (`LevelInertiaCovered`) and reduces it to the
third field of `PlaceLevelBridgeCore`
(`NK.ResidueFrob.inertia_surjective_of_levelInertiaCovered`).  **The statement itself is a
theorem of this chapter**, not an input: it is
`NK.ResidueFrob.levelInertiaCovered_of_tameData`, in
`Submission/Work/ResidueFrob/levelInertiaCovered_of_tameData.lean`, proved from two theorems of
this chapter:

* `NK.ResidueFrob.exists_inertia_of_isTrivialOnResidueAtLevel` — the *surjectivity* of the level
  inertia subgroups of the tower: an element `g ∈ D_A` acting trivially on the residue field of
  `L` differs on `L` from an element `δ ∈ D_A` fixing `L` pointwise with `δ * g` acting trivially
  on the residue field of **every** finite normal level;
* `NK.ResidueFrob.inertia_of_levels_of_tameData` — the *projective-limit* description of the
  local inertia: an element of `D_A` acting trivially on the residue field of every finite normal
  level lies in `I_κ` (this is `NK.FrobeniusBridge.InertiaLevelBridge`, proved here from the
  local structure theory).

The content of `exists_inertia_of_isTrivialOnResidueAtLevel` is the classical Fourier–Hilbert
statement that the inertia subgroup of a Galois level surjects onto the inertia subgroup of a
sublevel, made explicit through `NK.Commons.FieldTheory.Galois.exists_mem_stabilizer_restrictNormalHom_eq`
and `NK.ResidueFrob.exists_mem_decompositionGroup_restrictNormalHom_eq` (the transitivity of the
Galois action on the places above `P_L`); no comparison between the completion of a level and the
local field `κ` is needed.

Note (for the reader comparing with `NK.FrobeniusBridge.InertiaLevelBridge`): the direction
proved in `inertia_of_levels_of_tameData` is the one where the element acts trivially on the
residue field of **every** level.  It is *not* equivalent to `LevelInertiaCovered` — an element may
act trivially on the residue field of one level and non-trivially on a larger one — which is
exactly why the two are combined above.
-/

namespace NK.ResidueFrob

open scoped Pointwise Classical

set_option linter.unusedSectionVars false

variable {K : Type*} [Field K] [NumberField K]
variable {K' : Type*} [Field K'] [Algebra K K'] [IsSepClosure K K']

/-- **The inertia half of the local–global dictionary**: for every finite normal level `L`, every
element `h` of the decomposition group of the place `A` acting trivially on the residue field of
`L` at the prime below `A` differs, on `L`, from a local inertia element by an element of `D_A`
fixing `L` pointwise.

This is the projective-limit statement that the level inertia subgroups of the tower below `A` are
the images of the local inertia subgroup `I_κ`; it is *proved* in
`NK.ResidueFrob.levelInertiaCovered_of_tameData`. -/
def LevelInertiaCovered (A : NK.FrobeniusBridge.FinitePlaceOf K K') (p : ℕ) : Prop :=
  ∀ (L : IntermediateField K K') [FiniteDimensional K L] [Normal K L] [NumberField ↥L]
    (h : Gal(K'/K))
    (hh : h ∈ Submission.NeukirchUchida.decompositionGroup (K₁ := K) (K₁' := K') A.1),
    NK.FrobeniusBridge.IsTrivialOnResidueAtLevel A L h →
    ∃ (δ : Gal(K'/K))
      (hδ : δ ∈ Submission.NeukirchUchida.decompositionGroup (K₁ := K) (K₁' := K') A.1),
      AlgEquiv.restrictNormalHom L δ = 1 ∧
        NK.FrobeniusBridge.localGaloisEquiv A
            ⟨δ * h, Subgroup.mul_mem _ hδ hh⟩ ∈
          NK.LocalAnabelian.inertiaSubgroup (κ := NK.FrobeniusBridge.localField A)
            (K' := NK.FrobeniusBridge.localClosure A) p

/-- **The inertia half of the local–global dictionary, from the classical input
`LevelInertiaCovered`.**  This is the field `inertia_surjective` of
`NK.FrobeniusBridge.PlaceLevelBridgeCore`. -/
theorem inertia_surjective_of_levelInertiaCovered (A : NK.FrobeniusBridge.FinitePlaceOf K K')
    {p : ℕ} (hcover : LevelInertiaCovered A p) :
    ∀ (L : IntermediateField K K') [FiniteDimensional K L] [Normal K L] [NumberField ↥L]
      (g : Gal(K'/K)), NK.FrobeniusBridge.IsTrivialOnResidueAtLevel A L g →
      ∃ (h : Gal(K'/K))
        (hh : h ∈ Submission.NeukirchUchida.decompositionGroup (K₁ := K) (K₁' := K') A.1),
        NK.FrobeniusBridge.localGaloisEquiv A ⟨h, hh⟩ ∈
            NK.LocalAnabelian.inertiaSubgroup (κ := NK.FrobeniusBridge.localField A)
              (K' := NK.FrobeniusBridge.localClosure A) p ∧
          AlgEquiv.restrictNormalHom L h = AlgEquiv.restrictNormalHom L g := by
  intro L _ _ _ g hg
  -- lift `g` to an element of `D_A` with the same restriction to `L`
  obtain ⟨h₀, hh₀, hrestrict⟩ := exists_mem_decompositionGroup_restrictNormalHom_eq A L hg
  have hg' : NK.FrobeniusBridge.IsTrivialOnResidueAtLevel A L h₀ := by
    simpa only [NK.FrobeniusBridge.IsTrivialOnResidueAtLevel, hrestrict] using hg
  obtain ⟨δ, hδ, hδfix, hδh⟩ := hcover L h₀ hh₀ hg'
  refine ⟨δ * h₀, Subgroup.mul_mem _ hδ hh₀, hδh, ?_⟩
  rw [map_mul, hδfix, one_mul]
  exact hrestrict

end NK.ResidueFrob
