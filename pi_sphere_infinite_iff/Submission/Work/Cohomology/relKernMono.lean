import Mathlib
import Submission.Work.Cohomology.relCochain_shortExact
import Submission.Work.Cohomology.Pullback

/-!
# Monotonicity of the relative cochains `C^n(X,A)` in the second argument

Vanishing of a cochain on the `A`-chains implies vanishing on the `C`-chains for `C ⊆ A`:

`relKern R X A n ≤ relKern R X C n`.

Since `relKern R X A n = ker ((restr R X A).f n)` and `restr X A` is the dual of the chain map of
the inclusion `A ⊆ X`, this reduces to the factorization of the restriction along
`C ⊆ A ⊆ X`: `restr X C = restr_{C ⊆ A} ≫ restr X A`.

## Main results

* `setInclMap` — the inclusion `C ⊆ A` as a map of the subspaces, and
  `setInclMap_comp_subtypeIncl`: its composite with `A ⊆ X` is `C ⊆ X`;
* `restr_comp` — `restr R X C = setInclMap h ≫ restr R X A` for `C ⊆ A`;
* `relKern_mono` — `relKern R X A n ≤ relKern R X C n`.
-/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option linter.unusedVariables false

open CategoryTheory AlgebraicTopology Limits

namespace Work.Cohomology

noncomputable section

variable {R : Type} [CommRing R]

/-- **The inclusion of a subset `C ⊆ A` as a map of the corresponding subspaces.** -/
def setInclMap {X : TopCat} {C A : Set X} (h : C ⊆ A) : TopCat.of ↥C ⟶ TopCat.of ↥A :=
  TopCat.ofHom ⟨fun c => (⟨c.1, h c.2⟩ : ↥A),
    (continuous_subtype_val : Continuous fun c : ↥C => (c.1 : X)).subtype_mk (fun c => h c.2)⟩

/-- The composite of the inclusions `C ⊆ A ⊆ X` is the inclusion `C ⊆ X`. -/
theorem setInclMap_comp_subtypeIncl {X : TopCat} {C A : Set X} (h : C ⊆ A) :
    setInclMap h ≫ subtypeIncl X A = subtypeIncl X C := by
  apply TopCat.ext
  intro c
  rfl

/-- **The restriction map factors along `C ⊆ A ⊆ X`**: restricting to `C` is restricting to `A`
and then restricting from `A` to `C`. -/
theorem restr_comp {X : TopCat} {C A : Set X} (h : C ⊆ A) :
    restr R X C = restr R X A ≫
      dualChainMap R (TopCat.of ↥C) (TopCat.of ↥A) (setInclMap h) := by
  have hfac : subtypeIncl X C = setInclMap h ≫ subtypeIncl X A :=
    (setInclMap_comp_subtypeIncl h).symm
  rw [restr, restr, hfac, dualChainMap_comp]

/-- **Monotonicity of `relKern` in its second argument.**  A cochain vanishing on the `A`-chains
vanishes on the `C`-chains for `C ⊆ A`. -/
theorem relKern_mono {X : TopCat} {A C : Set X} (h : C ⊆ A) {n : ℕ} :
    relKern R X A n ≤ relKern R X C n := by
  intro α hα
  rw [relKern, LinearMap.mem_ker] at hα ⊢
  rw [restr_comp h, HomologicalComplex.comp_f, ModuleCat.hom_comp, LinearMap.comp_apply, hα,
    map_zero]

end

end Work.Cohomology
