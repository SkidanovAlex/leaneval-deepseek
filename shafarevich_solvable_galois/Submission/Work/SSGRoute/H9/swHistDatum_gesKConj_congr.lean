import Mathlib.GroupTheory.Nilpotent
import Mathlib.Algebra.Field.ZMod
import Mathlib.FieldTheory.Galois.Basic
import Mathlib.RingTheory.Valuation.ValuationSubring
import Submission.Work.SSGRoute.ZDataMup.swCoreDefs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGRoute.H9

open _root_.SSGRoute
open scoped Pointwise

/-! ## The accumulated datum is invariant under `K`-conjugation of its argument place

The accumulated datum `histDatum K y f` of a history is a sum of correction data
`correctionDatum K (½y) z_j Q_j`, and a correction datum depends on its argument place `A` only
through the two propositions `gesKConj K Q A` (the place lies over the `K`-prime of the escape prime
`Q`) and `IsConjPlace k Q A` (the place lies over the `k`-prime of `Q`).  Both of these are invariant
under `K`-conjugation of `A`, so the accumulated datum is as well.  This is the transport used to
read the Schmidt--Wingberg datum prescribed at one representative per `K`-class off at *every*
place of that class. -/

/-- **`K`-conjugacy on the right is invariant under `K`-conjugacy of the argument.** -/
theorem gesKConj_invariant {k Ω : Type} [Field k] [Field Ω] [Algebra k Ω]
    (K : IntermediateField k Ω) {A A' : ValuationSubring Ω}
    (h : Work.SSGRoute.gesKConj K A A') (Q : ValuationSubring Ω) :
    Work.SSGRoute.gesKConj K Q A ↔ Work.SSGRoute.gesKConj K Q A' := by
  obtain ⟨τ, hτK, hτA⟩ := h
  constructor
  · rintro ⟨σ, hσK, hσQ⟩
    exact ⟨τ * σ, K.fixingSubgroup.mul_mem hτK hσK, by rw [mul_smul, hσQ, hτA]⟩
  · rintro ⟨σ, hσK, hσQ⟩
    exact ⟨τ⁻¹ * σ, K.fixingSubgroup.mul_mem (K.fixingSubgroup.inv_mem hτK) hσK,
      by rw [mul_smul, hσQ, ← hτA, inv_smul_smul]⟩

/-- **`k`-conjugacy on the right is invariant under `K`-conjugacy of the argument.** -/
theorem isConjPlace_invariant {k Ω : Type} [Field k] [Field Ω] [Algebra k Ω]
    (K : IntermediateField k Ω) {A A' : ValuationSubring Ω}
    (h : Work.SSGRoute.gesKConj K A A') (Q : ValuationSubring Ω) :
    SSGRoute.IsConjPlace k Q A ↔ SSGRoute.IsConjPlace k Q A' := by
  obtain ⟨τ, hτK, hτA⟩ := h
  constructor
  · rintro ⟨σ, hσQ⟩
    exact ⟨τ * σ, by rw [mul_smul, hσQ, hτA]⟩
  · rintro ⟨σ, hσQ⟩
    exact ⟨τ⁻¹ * σ, by rw [mul_smul, hσQ, ← hτA, inv_smul_smul]⟩

/-- **The correction datum is invariant under `K`-conjugation of its argument place.** -/
theorem correctionDatum_gesKConj_congr {p : ℕ} [Fact p.Prime] {k Ω : Type} [Field k] [Field Ω]
    [Algebra k Ω] (K : IntermediateField k Ω) (g z : (Ω ≃ₐ[k] Ω) → ZMod p)
    (Q : ValuationSubring Ω) {A A' : ValuationSubring Ω}
    (h : Work.SSGRoute.gesKConj K A A') :
    Work.SSGRoute.ZDataMup.correctionDatum K g z Q A
      = Work.SSGRoute.ZDataMup.correctionDatum K g z Q A' := by
  have h1 : Work.SSGRoute.gesKConj K Q A ↔ Work.SSGRoute.gesKConj K Q A' :=
    gesKConj_invariant K h Q
  have h2 : SSGRoute.IsConjPlace k Q A ↔ SSGRoute.IsConjPlace k Q A' :=
    isConjPlace_invariant K h Q
  funext τ
  by_cases hc : Work.SSGRoute.gesKConj K Q A
  · simp only [Work.SSGRoute.ZDataMup.correctionDatum, if_pos hc, if_pos (h1.mp hc)]
  · have hc' : ¬ Work.SSGRoute.gesKConj K Q A' := fun hh => hc (h1.mpr hh)
    by_cases hd : SSGRoute.IsConjPlace k Q A
    · simp only [Work.SSGRoute.ZDataMup.correctionDatum, if_neg hc, if_neg hc',
        if_pos hd, if_pos (h2.mp hd)]
    · have hd' : ¬ SSGRoute.IsConjPlace k Q A' := fun hh => hd (h2.mpr hh)
      simp only [Work.SSGRoute.ZDataMup.correctionDatum, if_neg hc, if_neg hc',
        if_neg hd, if_neg hd']

theorem swHistDatum_gesKConj_congr {p : ℕ} [Fact p.Prime] {k Ω : Type} [Field k] [Field Ω]
    [Algebra k Ω] (K : IntermediateField k Ω) (y : (Ω ≃ₐ[k] Ω) → ZMod p)
    {n : ℕ} (f : Fin n → (ValuationSubring Ω × ((Ω ≃ₐ[k] Ω) → ZMod p)))
    (A A' : ValuationSubring Ω) (h : Work.SSGRoute.gesKConj K A A') :
    Work.SSGRoute.ZDataMup.histDatum K y f A = Work.SSGRoute.ZDataMup.histDatum K y f A' := by
  funext τ
  simp only [Work.SSGRoute.ZDataMup.histDatum]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  exact congrFun (correctionDatum_gesKConj_congr (p := p) K
    (fun σ => (2 : ZMod p)⁻¹ * y σ) ((f j).2) ((f j).1) h) τ

end Work.SSGRoute.H9
