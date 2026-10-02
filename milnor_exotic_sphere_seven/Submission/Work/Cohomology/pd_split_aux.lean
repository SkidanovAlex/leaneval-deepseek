import Mathlib

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Transporting (relative) cycles along an equality of degrees

Auxiliary lemmas for `pd_union_split`: a cycle of a chain complex can be transported along an
equality of degrees, compatibly with `iCycles` and `homologyπ`.
-/

open CategoryTheory AlgebraicTopology CategoryTheory.Limits

namespace Work.Cohomology

noncomputable section

set_option maxHeartbeats 800000

/-- **Transport of a cycle along an equality of degrees.** -/
lemma pd_cyclesOfEq {K : ChainComplex (ModuleCat ℤ) ℕ} {i j : ℕ} (h : i = j) (γ : K.cycles i) :
    ∃ γ' : K.cycles j, K.iCycles j γ' = (K.XIsoOfEq h).hom (K.iCycles i γ) := by
  subst h
  exact ⟨γ, by rw [HomologicalComplex.XIsoOfEq_rfl]; rfl⟩

/-- **The cycles of two equal degrees have the same class**, via `XIsoOfEq`. -/
lemma pd_homologyπ_cyclesOfEq {K : ChainComplex (ModuleCat ℤ) ℕ} {i j : ℕ} (h : i = j)
    (γ : K.cycles i) (γ' : K.cycles j)
    (hγ : K.iCycles j γ' = (K.XIsoOfEq h).hom (K.iCycles i γ)) :
    K.homologyπ j γ' = h ▸ K.homologyπ i γ := by
  subst h
  have hmono : Mono (K.iCycles i) := inferInstance
  have h2 : γ' = γ := by
    apply (ModuleCat.mono_iff_injective (K.iCycles i)).mp inferInstance
    simpa [HomologicalComplex.XIsoOfEq_rfl] using hγ
  subst h2
  rfl

/-- **Naturality of `XIsoOfEq` for `iCycles` and an inclusion of degrees.** -/
lemma pd_iCycles_congr {K : ChainComplex (ModuleCat ℤ) ℕ} {i j : ℕ} (h : i = j)
    (γ : K.cycles i) (γ' : K.cycles j)
    (hγ : K.iCycles j γ' = (K.XIsoOfEq h).hom (K.iCycles i γ)) :
    K.iCycles j γ' = h ▸ K.iCycles i γ := by
  subst h
  have hmono : Mono (K.iCycles i) := inferInstance
  have h2 : γ' = γ := by
    apply (ModuleCat.mono_iff_injective (K.iCycles i)).mp inferInstance
    simpa [HomologicalComplex.XIsoOfEq_rfl] using hγ
  subst h2
  rfl

end

end Work.Cohomology
