/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Composition compatibility of the induced map `F(m)/F(m)² → F(n)/F(n)²`

For surjective `G`-operator homomorphisms `Φ : F(m) ⇢ F(n)` and `Ψ : F(n) ⇢ F(l)` the
induced `𝔽_p`-linear maps `quotMapLin` on `F(-)/F(-)²` are compatible with composition:

`quotMapLin (Ψ ∘ Φ) = quotMapLin Ψ ∘ quotMapLin Φ`.

This is the `τ = (1,1)` case of the functoriality of Schmidt–Wingberg's Proposition 5 and is
used to transport the shrinking procedure through compositions of operator maps.

The proof reduces to the corresponding statement for the induced maps
`pCentralMapMul : P_n/P_{n+1} → Q_n/Q_{n+1}` on the subquotients of the descending `p`-central
series, which is checked on a representative (`QuotientGroup.map_mk'`).
-/

import Mathlib
import Submission.Work.CohomologicalShrinking.Functorial
import Submission.Work.CohomologicalShrinking.OperatorMap
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.CohomologicalShrinking.functorial

open Work.CohomologicalShrinking

/-- Value of `pCentralMapMul` on the class of a representative. -/
private theorem pCentralMapMul_mk_apply (p : ℕ) {P Q : Type*} [Group P] [Group Q]
    (ψ : P →* Q) (hψ : Function.Surjective ψ) (n : ℕ)
    (x : ↥(Work.Shrinking.pCentralSeries p P n)) :
    pCentralMapMul p ψ hψ n (QuotientGroup.mk' _ x)
      = QuotientGroup.mk' _ ⟨ψ (x : P), by
          rw [← Work.Shrinking.map_pCentralSeries_surjective p ψ hψ n]
          exact Subgroup.mem_map_of_mem ψ x.2⟩ := by
  rw [pCentralMapMul, QuotientGroup.map_mk']
  rfl

/-- The induced maps on the subquotients of the descending `p`-central series are compatible
with composition. -/
private theorem pCentralMapMul_comp (p : ℕ) {P Q R : Type*} [Group P] [Group Q] [Group R]
    (φ : P →* Q) (hφ : Function.Surjective φ)
    (ψ : Q →* R) (hψ : Function.Surjective ψ) (n : ℕ) :
    pCentralMapMul p (ψ.comp φ) (hψ.comp hφ) n
      = (pCentralMapMul p ψ hψ n).comp (pCentralMapMul p φ hφ n) := by
  apply MonoidHom.ext
  intro x
  obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective
    ((Work.Shrinking.pCentralSeries p P (n + 1)).subgroupOf
      (Work.Shrinking.pCentralSeries p P n)) x
  rw [MonoidHom.comp_apply, pCentralMapMul_mk_apply, pCentralMapMul_mk_apply,
    pCentralMapMul_mk_apply]
  exact congrArg (QuotientGroup.mk' _) (Subtype.ext rfl)

/-- The induced maps `F(m)/F(m)² → F(n)/F(n)²` are compatible with composition. -/
private theorem quotMapAdd_comp (p : ℕ) (G : Type*) [Group G] {m n l : ℕ}
    (φ : Work.Shrinking.freeOperatorGroup G m →* Work.Shrinking.freeOperatorGroup G n)
    (hφ : Function.Surjective φ)
    (ψ : Work.Shrinking.freeOperatorGroup G n →* Work.Shrinking.freeOperatorGroup G l)
    (hψ : Function.Surjective ψ) :
    quotMapAdd p G (ψ.comp φ) (hψ.comp hφ)
      = (quotMapAdd p G ψ hψ).comp (quotMapAdd p G φ hφ) := by
  apply AddMonoidHom.ext
  intro z
  show Additive.ofMul (pCentralMapMul p (ψ.comp φ) (hψ.comp hφ) 0 (Additive.toMul z))
      = Additive.ofMul (pCentralMapMul p ψ hψ 0
          (pCentralMapMul p φ hφ 0 (Additive.toMul z)))
  rw [pCentralMapMul_comp, MonoidHom.comp_apply]

theorem quotMapLin_comp (p : ℕ) (G : Type*) [Group G] {m n l : ℕ}
    (Φ : Work.CohomologicalShrinking.OperatorMap G m n)
    (Ψ : Work.CohomologicalShrinking.OperatorMap G n l) :
    Work.CohomologicalShrinking.quotMapLin p G (Ψ.toHom.comp Φ.toHom)
        (Ψ.surjective.comp Φ.surjective)
      = (Work.CohomologicalShrinking.quotMapLin p G Ψ.toHom Ψ.surjective).comp
          (Work.CohomologicalShrinking.quotMapLin p G Φ.toHom Φ.surjective) := by
  apply LinearMap.ext
  intro z
  show quotMapAdd p G (Ψ.toHom.comp Φ.toHom) (Ψ.surjective.comp Φ.surjective) z
      = quotMapAdd p G Ψ.toHom Ψ.surjective
          (quotMapAdd p G Φ.toHom Φ.surjective z)
  rw [quotMapAdd_comp, AddMonoidHom.comp_apply]

end Work.CohomologicalShrinking.functorial
