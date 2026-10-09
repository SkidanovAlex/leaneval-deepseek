/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# The maximal tamely ramified extension of a `p`-adic field

For a uniformiser `π` of `κ = K_𝔭` and a separable closure `K'` of `κ`, the *maximal tamely
ramified extension* of `κ` is

  `κ^{tr} = κ^{ur}(π^{1/n} : n prime to p)`,

realised in `K'` as `tameClosure π` below: the compositum of the maximal unramified extension
`κ^{ur} = unramifiedClosure p` with the Kummer fields `κ^{ur}(π^{1/n})`, i.e. with all `κ⟮α⟯` for
`α ^ n = π` and `p ∤ n`.

The tamely ramified layer of `G_κ` is the quotient `Gal(κ^{tr}/κ^{ur}) = I_κ/V_κ`; its finite
quotients are `Gal(κ^{ur}(π^{1/n})/κ^{ur})` by the directedness of the compositum, and each of these
is `ℤ/n` for `n` prime to `p` (`Tame/Kummer.lean` + Mathlib's Kummer theory).  Consequently every
finite quotient of `Gal(κ^{tr}/κ^{ur})` is cyclic of order prime to `p`, which is the pro-cyclicity
`IsProCyclic` and the pro-prime-to-`p`-ness `IsProPrimeToP` of the tame inertia.

The fixing subgroup of `κ^{tr}` is `V_κ := Gal(K'/κ^{tr})`, and by
`Submission/Work/TameStructureDeep/README.md` §7.2 (corrected four times: the cyclotomic character
on the tame inertia is faithful) it **coincides** with the join `NK.LocalTame.wildInertiaSubgroup`
of the normal pro-`p` subgroups of `G_κ`; see
`NK.TameStructureDeep.Tame.wildInertiaSubgroup_eq_correctedWildInertia`.
-/
import Mathlib
import Submission.NK.TameStructureDeep.Tame.Defs
import Submission.NK.LocalAnabelian.ResidueField.inertiaSubgroup_eq_fixingSubgroup_unramifiedClosure
import Submission.NK.LocalAnabelian.ResidueField.isGalois_unramifiedClosure
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

open scoped Classical
open IntermediateField

set_option linter.unusedVariables false

namespace NK.TameStructureDeep.Tame

noncomputable section

variable {κ K' : Type*} [Field κ] [Field K'] [Algebra κ K']

/-- The set of `n`-th roots of the uniformiser `π`, `n` prime to `p`. -/
def tameRootSet (p : ℕ) (π : κ) : Set K' :=
  {x : K' | ∃ n : ℕ, ¬ p ∣ n ∧ x ^ n = algebraMap κ K' π}

/-- **The maximal tamely ramified extension of `κ` inside `K'`**, for the uniformiser `π`:
the compositum of `κ^{ur} = unramifiedClosure p` with all the Kummer fields `κ^{ur}(π^{1/n})`,
`n` prime to `p`.

(In fact `κ^{tr}` does not depend on the choice of `π`, but this is not needed below: the
structure theory of `Gal(κ^{tr}/κ^{ur})` is computed with the fixed `π`.) -/
noncomputable def tameClosure (p : ℕ) (π : κ) : IntermediateField κ K' :=
  (NK.LocalAnabelian.unramifiedClosure (κ := κ) (K' := K') p) ⊔
    IntermediateField.adjoin κ (tameRootSet (K' := K') p π)

theorem tameRootSet_le_iff {p : ℕ} {π : κ} {L : IntermediateField κ K'} :
    tameRootSet (K' := K') p π ⊆ (L : Set K') ↔
      ∀ (n : ℕ), ¬ p ∣ n → ∀ α : K', α ^ n = algebraMap κ K' π → α ∈ L :=
  ⟨fun h n hn α hα => h ⟨n, hn, hα⟩, fun h _ ⟨n, hn, hα⟩ => h n hn _ hα⟩

/-- The maximal unramified extension is contained in the maximal tamely ramified one. -/
theorem unramifiedClosure_le_tameClosure (p : ℕ) (π : κ) :
    NK.LocalAnabelian.unramifiedClosure (κ := κ) (K' := K') p ≤
      tameClosure (K' := K') p π :=
  le_sup_left

/-- Every `n`-th root of the uniformiser, `n` prime to `p`, generates a subfield of `κ^{tr}`. -/
theorem adjoin_root_mem_tameClosure {p n : ℕ} (hn : ¬ p ∣ n) {π : κ} {α : K'}
    (hα : α ^ n = algebraMap κ K' π) : κ⟮α⟯ ≤ tameClosure (K' := K') p π := by
  refine le_trans ?_ le_sup_right
  rw [IntermediateField.adjoin_le_iff]
  rintro x rfl
  exact IntermediateField.subset_adjoin κ _ ⟨n, hn, hα⟩

/-- **The maximal tamely ramified extension is the compositum of `κ^{ur}` with the Kummer layers
`κ^{ur}(π^{1/n})`, and any element of it which is already integral over `κ^{ur}`... ** — here we
simply record the universal property: `κ^{tr}` is the *smallest* extension of `κ` containing
`κ^{ur}` and all the `n`-th roots of `π` for `n` prime to `p`. -/
theorem tameClosure_le_iff {p : ℕ} {π : κ} {L : IntermediateField κ K'} :
    tameClosure (K' := K') p π ≤ L ↔
      NK.LocalAnabelian.unramifiedClosure (κ := κ) (K' := K') p ≤ L ∧
        ∀ (n : ℕ), ¬ p ∣ n → ∀ α : K', α ^ n = algebraMap κ K' π → α ∈ L := by
  rw [tameClosure, sup_le_iff]
  refine ⟨fun h => ⟨h.1, fun n hn α hα => ?_⟩, fun h => ⟨h.1, ?_⟩⟩
  · exact h.2 (IntermediateField.subset_adjoin κ _ ⟨n, hn, hα⟩)
  · rw [IntermediateField.adjoin_le_iff]
    exact (tameRootSet_le_iff).mpr h.2

/-- The fixing subgroup of `κ^{tr}`: the corrected wild inertia `V_κ = Gal(K'/κ^{tr})`. -/
def correctedWildInertia (p : ℕ) (π : κ) : Subgroup (Gal(K'/κ)) :=
  (tameClosure (K' := K') p π).fixingSubgroup

/-- The corrected wild inertia is contained in the inertia subgroup: this is the statement that
the classical wild inertia `Gal(K'/κ^{tr})` *is* contained in `I_κ = Gal(K'/κ^{ur})`, in contrast
with the join `NK.LocalTame.wildInertiaSubgroup` (README §7). -/
theorem correctedWildInertia_le_inertia (p : ℕ) (π : κ) :
    correctedWildInertia (K' := K') p π ≤
      NK.LocalAnabelian.inertiaSubgroup (κ := κ) (K' := K') p := by
  rw [NK.LocalAnabelian.ResidueField.inertiaSubgroup_eq_fixingSubgroup_unramifiedClosure]
  exact IntermediateField.fixingSubgroup_le (unramifiedClosure_le_tameClosure (K' := K') p π)

end

end NK.TameStructureDeep.Tame
