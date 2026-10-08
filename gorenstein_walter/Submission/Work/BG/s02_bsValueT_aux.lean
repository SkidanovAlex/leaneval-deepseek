import Mathlib
import Submission.Work.BG.S02
import Submission.Work.BG.Lambda

/-!
# Area BG: auxiliary lemmas for the `T`-value form of Lemma 1.3 (`BSValueTProp`)

These are the two elementary inputs of `Work.BG.s02_bsValueT` that are used twice in the
support computation for `δ = Ind_{H₀}^{H}(μ - ν)`:

* `lamEquiv_apply_eq_of_mem_U` — if `ν = λ_β μ` then `μ - ν` vanishes on `U` (all `λ ∈ Λ`
  are trivial on `U`, `Work.BG.Lambda.apply_eq_one_of_mem_U`);
* `s_conj_mem_U` — `s` normalizes `U` (`s u s⁻¹ ∈ U` for `u ∈ U`), immediate from the
  hypothesis `s_inverts` of `Sec2Ctx` and the subgroup axioms.
-/

namespace Work.BG

open OddOrder.RepresentationTheory
open Subgroup

variable {G : Type} [Group G] [Finite G]

/-- If `ν = λ_β μ` (`LamEquiv C μ ν`) then the difference `μ - ν` vanishes on `U`: every
`λ ∈ Λ` is trivial on `U`. -/
theorem lamEquiv_apply_eq_of_mem_U (C : Sec2Ctx G)
    {μ ν : ClassFunction ↥C.P.H0 ℂ} (hLam : LamEquiv C μ ν) :
    ∀ u : ↥C.P.H0, u ∈ C.P.U.subgroupOf C.P.H0 → (μ - ν) u = 0 := by
  intro u hu
  obtain ⟨β, hβ⟩ := hLam
  rw [hβ, ClassFunction.sub_apply, ClassFunction.mul_apply]
  have h1 : lamCF C β u = 1 :=
    Lambda.apply_eq_one_of_mem_U (P := C.P) ⟨β, rfl⟩ hu
  rw [h1, one_mul, sub_self]

/-- `s` normalizes `U`: for `u ∈ U`, `s u s⁻¹ ∈ U`.  Indeed `s u s⁻¹ u ∈ U` by
`s_inverts` (`s` inverts `H₀/U`), and `u⁻¹ ∈ U`. -/
theorem s_conj_mem_U (C : Sec2Ctx G) {u : G} (hu : u ∈ C.P.U) :
    (C.s : G) * u * (C.s : G)⁻¹ ∈ C.P.U := by
  have huH0 : u ∈ C.P.H0 := C.P.U_le_H0 hu
  have h := C.s_inverts u huH0
  have heq : (C.s : G) * u * (C.s : G)⁻¹
      = ((C.s : G) * u * (C.s : G)⁻¹ * u) * u⁻¹ := by group
  rw [heq]
  exact C.P.U.mul_mem h (C.P.U.inv_mem hu)

end Work.BG
