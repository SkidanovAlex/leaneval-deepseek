import Mathlib
import Submission.Work.EKLC6Core.Basic

/-!
# `EKLC6Core.conjBy_neg_inter_U` — conjugation by `aDiag (-t)` preserves a horospherical `U`

For a horospherical subgroup `U ≤ SL₃(ℝ)` (`IsHoro U`) and any exponent vector `t`, the
conjugation map `φ_t(g) = aDiag t · g · (aDiag t)⁻¹` leaves `U` invariant (this is the
`A`-normalisation part of `IsHoro`).  Since `φ_{-t}` is the inverse of `φ_t`, it follows that

  `conjBy (-t) (O ∩ U) = conjBy (-t) O ∩ U`.

Indeed, `conjBy (-t) (O ∩ U) ⊆ conjBy (-t) O ∩ U` uses `φ_{-t}(U) ⊆ U`, and the reverse
inclusion uses the converse: if `g = φ_{-t}(k) ∈ U` with `k ∈ O`, then
`k = φ_t(g) ∈ U`, so `k ∈ O ∩ U`.
-/

open Filter Topology
open LeanEval.Dynamics.EinsiedlerKatokLindenstrauss

set_option linter.unusedVariables false

noncomputable section

namespace Work.EKLC6Core

open Work.EKLContract

/-- `(aDiag t)⁻¹ = aDiag (-t)`. -/
theorem aDiag_inv_eq (t : Fin 3 → ℝ) : (aDiag t)⁻¹ = aDiag (-t) :=
  inv_eq_of_mul_eq_one_left (aDiag_neg_mul t)

/-- Conjugation by `aDiag (-t)` undoes conjugation by `aDiag t`, pointwise. -/
theorem aDiag_conj_neg_conj (t : Fin 3 → ℝ) (g : SL3) :
    aDiag (-t) * (aDiag t * g * (aDiag t)⁻¹) * (aDiag (-t))⁻¹ = g := by
  rw [aDiag_inv_eq t, aDiag_inv_eq (-t), neg_neg]
  calc aDiag (-t) * (aDiag t * g * aDiag (-t)) * aDiag t
      = (aDiag (-t) * aDiag t) * g * (aDiag (-t) * aDiag t) := by group
    _ = g := by rw [aDiag_neg_mul t, one_mul, mul_one]

/-- The image of a horospherical subgroup under conjugation by `aDiag t` is itself. -/
theorem conjBy_eq_self_of_isHoro {U : Subgroup SL3} (hU : IsHoro U) (t : Fin 3 → ℝ) :
    conjBy t (U : Set SL3) = U := by
  refine Set.Subset.antisymm ?_ ?_
  · rintro g ⟨u, hu, rfl⟩
    exact hU.2.1 t u hu
  · intro u hu
    refine ⟨aDiag (-t) * u * (aDiag (-t))⁻¹, hU.2.1 (-t) u hu, ?_⟩
    simpa using aDiag_conj_neg_conj (-t) u

/-- **The target.**  `U` is preserved by conjugation, so intersecting with `U` commutes with
`conjBy (-t)`. -/
theorem conjBy_neg_inter_U {U : Subgroup Work.EKLContract.SL3} (hU : Work.EKLContract.IsHoro U) (t : Fin 3 → ℝ) (O : Set Work.EKLContract.SL3) :
    Work.EKLC6Core.conjBy (-t) (O ∩ (U : Set Work.EKLContract.SL3)) =
      Work.EKLC6Core.conjBy (-t) O ∩ (U : Set Work.EKLContract.SL3) := by
  ext g
  constructor
  · rintro ⟨k, ⟨hkO, hkU⟩, rfl⟩
    exact ⟨⟨k, hkO, rfl⟩, hU.2.1 (-t) k hkU⟩
  · rintro ⟨⟨k, hkO, rfl⟩, hgU⟩
    refine ⟨k, ⟨hkO, ?_⟩, rfl⟩
    have h := hU.2.1 t (aDiag (-t) * k * (aDiag (-t))⁻¹) hgU
    have hkey : aDiag t * (aDiag (-t) * k * (aDiag (-t))⁻¹) * (aDiag t)⁻¹ = k := by
      simpa using aDiag_conj_neg_conj (-t) k
    rwa [hkey] at h

end Work.EKLC6Core

end
