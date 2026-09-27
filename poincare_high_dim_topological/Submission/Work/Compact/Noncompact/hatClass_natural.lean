import Mathlib
import Submission.Work.Compact.Noncompact.Good

/-!
# Naturality of Hatcher's class in the support set

For `S ⊆ T` and a `(k+1)`-chain `z` of `X` whose boundary is supported both in `S` and in `T`,
the class of `z` in `H_{k+1}(X, X∖S)` maps to its class in `H_{k+1}(X, X∖T)` under the
restriction map `relMapHom hST (k+1)`.  This is the naturality of `hatClass` in the second
variable, and is the bookkeeping identity used when one enlarges the support set.

The proof is pure chain-complex naturality:
* the quotients `C_*(X)/C_*(S) → C_*(X)/C_*(T)` send `π_S z` to `π_T z`
  (`cokernel_π_relMap`), which identifies the corresponding `hatSingleton` maps;
* `cyclesMap` of the restriction therefore carries `hatCycHom S` to `hatCycHom T`;
* `homologyπ_naturality` then identifies `hatClassHom` after restriction.
-/

namespace Work.Compact.Noncompact

open CategoryTheory AlgebraicTopology CategoryTheory.Limits

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

variable {X : TopCat}

/-- The component of `cokernel_π_relMap` in degree `k+1`, evaluated on a chain: the quotient
map `C_{k+1}(X)/C_{k+1}(S) → C_{k+1}(X)/C_{k+1}(T)` sends `hatQ S k z` to `hatQ T k z`. -/
lemma relMap_f_hatQ {S T : Set X} (hST : S ⊆ T) (k : ℕ) (z : Ch X (k + 1)) :
    ((relMap hST).f (k + 1)).hom (hatQ S k z) = hatQ T k z := by
  have hπ := cokernel_π_relMap hST
  have hπc : (cokernel.π (Work.Cohomology.inclChains X S) ≫ relMap hST).f (k + 1)
      = (𝟙 (Work.Cohomology.singularChains ℤ X) ≫
          cokernel.π (Work.Cohomology.inclChains X T)).f (k + 1) := by
    rw [hπ]
  simp only [HomologicalComplex.comp_f, Category.id_comp] at hπc
  have h2 := congrArg (fun (f : Ch X (k + 1) ⟶ (RC X T).X (k + 1)) => f.hom z) hπc
  rw [ModuleCat.comp_apply] at h2
  simpa only [hatQ] using h2

/-- The `hatSingleton` maps are natural: restricting the support set from `S` to `T` sends the
singleton map attached to `z` for `S` to the one attached to `z` for `T`. -/
lemma hatSingleton_natural {S T : Set X} (hST : S ⊆ T) (k : ℕ) (z : Ch X (k + 1)) :
    hatSingleton S k z ≫ (relMap hST).f (k + 1) = hatSingleton T k z := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext_ring
  rw [ModuleCat.hom_comp, LinearMap.comp_apply]
  rw [hatSingleton, ModuleCat.ofHom_apply, LinearMap.toSpanSingleton_apply_one]
  rw [hatSingleton, ModuleCat.ofHom_apply, LinearMap.toSpanSingleton_apply_one]
  exact relMap_f_hatQ hST k z

/-- The cycle representatives `hatCycHom` are natural: `cyclesMap` of the restriction carries the
cycle of `z` for `S` to the cycle of `z` for `T`. -/
lemma hatCycHom_natural {S T : Set X} (hST : S ⊆ T) (k : ℕ) (z : Ch X (k + 1))
    (hzS : bdry X k z ∈ suppS X S k) (hzT : bdry X k z ∈ suppS X T k) :
    hatCycHom S k z hzS ≫ HomologicalComplex.cyclesMap (relMap hST) (k + 1)
      = hatCycHom T k z hzT := by
  rw [← cancel_mono ((RC X T).iCycles (k + 1))]
  rw [Category.assoc, HomologicalComplex.cyclesMap_i]
  rw [← Category.assoc, iCycles_hatCycHom, iCycles_hatCycHom]
  exact hatSingleton_natural hST k z

/-- The morphisms `hatClassHom` are natural in the support set. -/
lemma hatClassHom_natural {S T : Set X} (hST : S ⊆ T) (k : ℕ) (z : Ch X (k + 1))
    (hzS : bdry X k z ∈ suppS X S k) (hzT : bdry X k z ∈ suppS X T k) :
    hatClassHom S k z hzS ≫ relMapHom hST (k + 1) = hatClassHom T k z hzT := by
  rw [hatClassHom, hatClassHom, relMapHom]
  rw [Category.assoc, HomologicalComplex.homologyπ_naturality, ← Category.assoc,
    hatCycHom_natural hST k z hzS hzT]

theorem hatClass_natural {X : TopCat} {S T : Set X} (hST : S ⊆ T) (k : ℕ)
    (z : Work.Compact.Noncompact.Ch X (k + 1))
    (hzS : Work.Compact.Noncompact.bdry X k z ∈ Work.Compact.Noncompact.suppS X S k)
    (hzT : Work.Compact.Noncompact.bdry X k z ∈ Work.Compact.Noncompact.suppS X T k) :
    Work.Compact.Noncompact.relMapHom hST (k + 1)
        (Work.Compact.Noncompact.hatClass S k z hzS)
      = Work.Compact.Noncompact.hatClass T k z hzT := by
  change (relMapHom hST (k + 1)).hom ((hatClassHom S k z hzS).hom 1)
      = (hatClassHom T k z hzT).hom 1
  rw [← ModuleCat.comp_apply]
  exact congrArg (fun f => f.hom 1) (hatClassHom_natural hST k z hzS hzT)

end Work.Compact.Noncompact
