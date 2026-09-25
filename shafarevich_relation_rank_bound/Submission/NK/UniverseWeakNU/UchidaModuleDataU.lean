/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Uchida's module data split into its two halves, at an arbitrary universe

Universe-polymorphic copies of `NK.WeakNU.isUchidaModuleDataKummer_of_isUchidaModuleData`,
`NK.WeakNU.isUchidaModuleData_of_kummer_and_arith` and `NK.WeakNU.isUchidaModuleData`
(`Submission/Work/WeakNU/UchidaModuleData.lean`): the Kummer-theoretic half
`IsUchidaModuleDataKummerU` is a consequence of the full data `IsUchidaModuleDataU`, and the full
data is equivalent to the conjunction of the two halves `IsUchidaModuleDataKummerU`,
`IsUchidaModuleDataArithU`.

These are the statements a future prover of the *leaves* of the polymorphic chain should target: the
Kummer half is a formalisation gap (the `𝔽_ℓ[Gal(L/ℚ)]`-module structure of a compositum of Kummer
radicals; its cardinality form is a theorem of this workspace), and the arithmetic half is the
`cor:arith equiv` of §6 of arXiv:2601.01251.
-/

import Mathlib
import Submission.NK.UniverseWeakNU.Defs
import Submission.NK.WeakNU.UchidaModuleData

noncomputable section

namespace NK.UniverseWeakNU

open IntermediateField

universe u

/-- **The Kummer half is implied by Uchida's module data**, at an arbitrary universe.  Copy of
`NK.WeakNU.isUchidaModuleDataKummer_of_isUchidaModuleData`. -/
theorem isUchidaModuleDataKummerU_of_isUchidaModuleDataU {ℓ : ℕ}
    (h : IsUchidaModuleDataU.{u} ℓ) : IsUchidaModuleDataKummerU.{u} ℓ := by
  intro n L _ _ _ _ hμ H₁ H₂ hμ₁ hμ₂ hiso
  obtain ⟨N, hfN, hnfN, halgN, halgLN, htower, hgalN, hfinLN, e, he, M₁, M₂, hLM₁, hLM₂,
    -, hspec₁, hspec₂⟩ := h n L hμ H₁ H₂ hμ₁ hμ₂ hiso
  exact ⟨N, hfN, hnfN, halgN, halgLN, htower, hgalN, hfinLN, e, he, M₁, M₂, hLM₁, hLM₂,
    hspec₁, hspec₂⟩

/-- **Uchida's module data from its two halves**, at an arbitrary universe.  Copy of
`NK.WeakNU.isUchidaModuleData_of_kummer_and_arith`. -/
theorem isUchidaModuleDataU_of_kummer_and_arithU {ℓ : ℕ}
    (hK : IsUchidaModuleDataKummerU.{u} ℓ) (hA : IsUchidaModuleDataArithU.{u} ℓ) :
    IsUchidaModuleDataU.{u} ℓ := by
  intro n L _ _ _ _ hμ H₁ H₂ hμ₁ hμ₂ hiso
  obtain ⟨N, hfN, hnfN, halgN, halgLN, htower, hgalN, hfinLN, e, he, M₁, M₂, hLM₁, hLM₂,
    hspec₁, hspec₂⟩ := hK n L hμ H₁ H₂ hμ₁ hμ₂ hiso
  refine ⟨N, hfN, hnfN, halgN, halgLN, htower, hgalN, hfinLN, e, he, M₁, M₂, hLM₁, hLM₂,
    ?_, hspec₁, hspec₂⟩
  exact hA n L H₁ H₂ N e M₁ M₂ he hLM₁ hLM₂ hspec₁ hspec₂

/-- **Uchida's module data from its two halves**, at an arbitrary universe. -/
theorem isUchidaModuleDataU {ℓ : ℕ}
    (hK : IsUchidaModuleDataKummerU.{u} ℓ) (hA : IsUchidaModuleDataArithU.{u} ℓ) :
    IsUchidaModuleDataU.{u} ℓ :=
  isUchidaModuleDataU_of_kummer_and_arithU hK hA

end NK.UniverseWeakNU
