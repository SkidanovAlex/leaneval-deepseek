import Mathlib.GroupTheory.Abelianization.Finite
import Mathlib.RingTheory.IntegralClosure.IntegralRestrict
import Submission.NK.Reconstruct.generalBaseChange
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Naturality of `galToGamma` for the general base change `π_{M/K}`

`NK.Reconstruct.generalBaseChange K M h ℓ : Γ_M → Γ_K` is Shimizu's base change for an
*arbitrary* finite extension `M/K` of number fields (the levels of `Γ_M` are the finite levels of
`Ω` over `M.L`, and the construction replaces the compositum `N ⊔ M` of the classical definition by
the compositum of `N` with the normal closure of `M` over `K.L`; see
`Submission/Work/Reconstruct/generalBaseChange.lean`).

This file proves that it is compatible with the canonical surjections `galToGamma`, i.e. that the
square

```
   Gal(Ω/M.L)  --galToGamma-->  Γ_M
        |                          |
    galRestrict h             π_{M/K}
        v                          v
   Gal(Ω/K.L)  --galToGamma-->  Γ_K
```

commutes, and the transitivity of the base change
`π_{L/K} = π_{N/K} ∘ π_{L/N}` for `K ⊆ N ⊆ L` (the case in which `L` is a finite Galois level of
`Ω/ℚ`).  These are the two functoriality statements needed to run Shimizu's descent
(Lemma 4f.4) at an arbitrary pair of number fields.

## Contents

* `NK.Reconstruct.mem_supClosureM_L`, `NK.Reconstruct.supClosureMOf` — the compositum
  `N ⊔ closure(M)` viewed over `K.L` and over `M.L` have the same underlying subset of `Ω`;
  `supClosureMOf` is the identity of the subsets, as a function;
* `NK.Reconstruct.levelInclGenHom_apply_coe_Ω` — the "forget the `M`-structure" map does not move
  the ambient element (in the form adapted to `supClosureMOf`);
* `NK.Reconstruct.ellInclGen_ellComp` — `ellInclGen` intertwines `ellComp` with
  `Abelianization.map`;
* `NK.Reconstruct.levelRestrict_levelInclGen_restrictNormalHom` — the group-level identity
  underlying the projection formula;
* **`NK.Reconstruct.generalBaseChange_galToGamma`** — the naturality square;
* **`NK.Reconstruct.generalBaseChange_comp_ambientPi`** — the transitivity of the base change.

## References

S. Shimizu, *On the Neukirch–Uchida theorem for small sets of primes*, arXiv:2009.10431, §4.
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

namespace NK.Reconstruct

attribute [local instance] NumFieldIn.finite NumFieldIn.numberField

open scoped Pointwise

variable {Ω : Type*} [Field Ω] [Algebra ℚ Ω] [IsGalois ℚ Ω] [IsSepClosure ℚ Ω]

/-! ## The two presentations of the compositum `N ⊔ closure(M)` -/

/-- **The compositum `N ⊔ closure(M)`, viewed over `K.L` and over `M.L`, has the same underlying
subset of `Ω`**: membership in `(supClosureM K M h N).L` and in `(supClosure K M h N).L` are the
same proposition. -/
theorem mem_supClosureM_L (K M : NumFieldIn ℚ Ω) (h : K.L ≤ M.L) (N : FrobLevel ↥K.L Ω) (x : Ω) :
    x ∈ (supClosureM K M h N).L ↔ x ∈ (supClosure K M h N).L := Iff.rfl

/-- **The identity of the two presentations of the compositum**, as an element of the presentation
over `M.L` of an element of the presentation over `K.L`. -/
noncomputable def supClosureMOf (K M : NumFieldIn ℚ Ω) (h : K.L ≤ M.L) (N : FrobLevel ↥K.L Ω)
    (x : ↥(supClosure K M h N).L) : ↥(supClosureM K M h N).L :=
  ⟨(x : Ω), (mem_supClosureM_L K M h N (x : Ω)).mpr x.2⟩

@[simp] theorem supClosureMOf_coe (K M : NumFieldIn ℚ Ω) (h : K.L ≤ M.L) (N : FrobLevel ↥K.L Ω)
    (x : ↥(supClosure K M h N).L) :
    ((supClosureMOf K M h N x : ↥(supClosureM K M h N).L) : Ω) = (x : Ω) := rfl

/-- **The "forget the `M`-structure" map does not move the ambient element**: the value of
`levelInclGenHom K M h N g` at `x` is the value of `g` at `supClosureMOf K M h N x`. -/
theorem levelInclGenHom_apply_coe_Ω (K M : NumFieldIn ℚ Ω) (h : K.L ≤ M.L) (N : FrobLevel ↥K.L Ω)
    (g : Gal(↥(supClosureM K M h N).L/↥M.L)) (x : ↥(supClosure K M h N).L) :
    (((levelInclGenHom K M h N g : Gal(↥(supClosure K M h N).L/↥K.L)) x :
        ↥(supClosure K M h N).L) : Ω)
      = ((g (supClosureMOf K M h N x)) : Ω) := rfl

/-! ## The projection formula -/

/-- **`ellInclGen` intertwines the ℓ-primary projection `ellComp` with `Abelianization.map`**: the
ℓ-primary component of the image of `y` under `levelInclGenHom` is the image of the ℓ-primary
component of `y`.  Both sides are ℓ-coprime-related to the image of `y`, so they agree by
uniqueness of the ℓ-primary component. -/
theorem ellInclGen_ellComp (K M : NumFieldIn ℚ Ω) (h : K.L ≤ M.L) (ℓ : ℕ)
    (N : FrobLevel ↥K.L Ω)
    (y : LevelAbelianization (K := ↥M.L) (K' := Ω) (supClosureM K M h N).L) :
    ellInclGen K M h ℓ N (ellComp ℓ y)
      = ellComp ℓ (Abelianization.map (levelInclGenHom K M h N) y) := by
  refine eq_ellComp_of_ellCoprimeRel ?_
  rw [ellInclGen_coe]
  exact ellCoprimeRel_map (Abelianization.map (levelInclGenHom K M h N))
    (ellCoprimeRel_ellComp ℓ y)

/-- **The group-level identity underlying the projection formula of the general base change.**

For a level `N` of `Ω` over `K.L`, restricting the automorphism `σ` of `Ω` over `M.L` to the level
`N` (through the compositum `N ⊔ closure(M)`), viewed over `K.L`, is the restriction to `N` of
`σ`, viewed over `K.L` (which is `galRestrict h σ`). -/
theorem levelRestrict_levelInclGen_restrictNormalHom (K M : NumFieldIn ℚ Ω) (h : K.L ≤ M.L)
    (N : FrobLevel ↥K.L Ω) (σ : Gal(Ω/↥M.L)) :
    levelRestrictHom N (supClosure K M h N) (le_supClosure K M h N)
        (levelInclGenHom K M h N
          (AlgEquiv.restrictNormalHom (F := ↥M.L) (K₁ := Ω) (supClosureM K M h N).L σ))
      = AlgEquiv.restrictNormalHom (F := ↥K.L) (K₁ := Ω) N.L (galRestrict h σ) := by
  refine AlgEquiv.ext fun x => Subtype.ext ?_
  rw [levelRestrictHom_apply_coe, levelInclGenHom_apply_coe_Ω]
  have hL : ((AlgEquiv.restrictNormalHom (F := ↥M.L) (K₁ := Ω) (supClosureM K M h N).L σ)
      (supClosureMOf K M h N ⟨(x : Ω), le_supClosure K M h N x.2⟩) : Ω) = σ (x : Ω) :=
    AlgEquiv.restrictNormal_commutes σ (supClosureM K M h N).L
      (supClosureMOf K M h N ⟨(x : Ω), le_supClosure K M h N x.2⟩)
  have hR : ((AlgEquiv.restrictNormalHom (F := ↥K.L) (K₁ := Ω) N.L (galRestrict h σ)) x : Ω)
      = σ (x : Ω) := by
    have hres := AlgEquiv.restrictNormal_commutes (galRestrict h σ) N.L x
    rw [galRestrict_apply] at hres
    exact hres
  rw [hL, hR]

/-! ## The naturality and transitivity -/

/-- **The naturality square of the general base change with `galToGamma`**: the base change
`π_{M/K} : Γ_M → Γ_K` carries the ℓ-adic abelianisation of an automorphism `σ` of `Ω` over `M.L`
to the ℓ-adic abelianisation of the same automorphism viewed over `K.L`. -/
theorem generalBaseChange_galToGamma (K M : NumFieldIn ℚ Ω) (h : K.L ≤ M.L) (ℓ : ℕ)
    (σ : Gal(Ω/↥M.L)) :
    generalBaseChange K M h ℓ (galToGamma (K := ↥M.L) (K' := Ω) ℓ σ)
      = galToGamma (K := ↥K.L) (K' := Ω) ℓ (galRestrict h σ) := by
  refine Gamma.ext (fun N => ?_)
  rw [generalBaseChange_apply]
  rw [galToGamma_proj (K := ↥M.L) (K' := Ω) ℓ (supClosureM K M h N) σ]
  rw [galToGamma_proj (K := ↥K.L) (K' := Ω) ℓ N (galRestrict h σ)]
  rw [levelComponent, levelComponent]
  rw [ellInclGen_ellComp]
  rw [ellRestrict_ellComp]
  rw [levelRestrict, Abelianization.map_of, Abelianization.map_of]
  rw [levelRestrict_levelInclGen_restrictNormalHom]

/-- **Transitivity of the general base change with the classical case**: for number fields
`K ⊆ N` and a finite Galois level `L` of `Ω/ℚ` containing `N`,
`π_{L/K} = π_{N/K} ∘ π_{L/N}`. -/
theorem generalBaseChange_comp_ambientPi (K N : NumFieldIn ℚ Ω) (L : FrobLevel ℚ Ω)
    [IsSepClosure ↥K.L Ω] [IsSepClosure ↥N.L Ω]
    (hKN : K.L ≤ N.L) (hNL : N.L ≤ L.L) (ℓ : ℕ) [Fact ℓ.Prime] :
    (generalBaseChange K N hKN ℓ).comp (ambientPi N L hNL ℓ)
      = ambientPi K L (hKN.trans hNL) ℓ := by
  refine MonoidHom.ext fun f => ?_
  obtain ⟨σ, rfl⟩ := galToGamma_surjective (K := ↥L.L) (K' := Ω) ℓ f
  rw [MonoidHom.comp_apply]
  rw [ambientPi_galToGamma N L hNL ℓ σ]
  rw [generalBaseChange_galToGamma K N hKN ℓ (galRestrict hNL σ)]
  rw [ambientPi_galToGamma K L (hKN.trans hNL) ℓ σ]
  exact congrArg (galToGamma (K := ↥K.L) (K' := Ω) ℓ) (AlgEquiv.ext (fun x => rfl))

end NK.Reconstruct
