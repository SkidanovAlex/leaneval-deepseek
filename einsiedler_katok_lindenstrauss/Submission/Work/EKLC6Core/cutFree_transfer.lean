import Mathlib
import Submission.Work.EKLC6Core.cutHDefs
import Submission.Work.EKLC6Core.uminus_isHoro

/-!
# `Work.EKLC6Core.cutFree_transfer`

The set

`cutFree U = {x : X₃ | ∀ u ∈ U, u • x = x → u = 1}`

of points at which the `U`-action is *free* is, for an admissible subgroup `U`
(`Work.EKLContract.IsHoro U`) and for every `t : Fin 3 → ℝ`:

* forward invariant under `U` itself (a translate of a free point by an element of `U`
  is again free — the stabiliser of `u • x` is the conjugate `u U_x u⁻¹` of that of `x`),
* invariant under the diagonal element `α^t = aDiag t`
  (`IsHoro U` normalises `U`, so the stabiliser of `aDiag t • x` is `aDiag t · U_x · (aDiag t)⁻¹`
  and triviality is preserved in both directions).

The third conjunct records the definitional form of membership.

These are exactly the two "transfer" properties used when the free orbit condition is transported
along the exceptional set of the cut (Pisa 7.12): the *good set* `CutGood` is defined by
`aDiag t`-iterates lying in `cutFree U`, and the leafwise picture must be well defined at every
point of the orbit, not just at time `0`.
-/

open MeasureTheory Set Topology Filter
open scoped ENNReal Pointwise

set_option linter.unusedVariables false
set_option warn.classDefReducibility false
set_option linter.style.haveILetI false

noncomputable section

namespace Work.EKLC6Core

open Work.EKLContract

variable {U : Subgroup SL3} {t : Fin 3 → ℝ}

/-! ## Elementary facts about the action on `X₃ = SL₃(ℝ)/SL₃(ℤ)` -/

theorem mem_cutFree_iff (U : Subgroup SL3) (x : X3) :
    x ∈ cutFree U ↔ ∀ u ∈ U, u • x = x → u = 1 := Iff.rfl

/-- Membership in `cutFree U` is exactly triviality of the `U`-stabiliser. -/
theorem cutFree_eq_setOf (U : Subgroup SL3) :
    cutFree U = {x : X3 | ∀ u ∈ U, u • x = x → u = 1} := rfl

/-- `aDiag (-t)` acts as the inverse of `aDiag t`. -/
theorem inv_aDiag (t : Fin 3 → ℝ) : (aDiag t)⁻¹ = aDiag (-t) :=
  inv_eq_of_mul_eq_one_left (Work.EKLContract.aDiag_neg_mul t)

/-! ## The transfer lemmas -/

/-- **`U` preserves the free locus.**  If the `U`-stabiliser of `x` is trivial then so is that
of `u • x` for `u ∈ U`: the two stabilisers are conjugate, `U_{u • x} = u U_x u⁻¹`, and `U` is
closed under conjugation by its own elements. -/
theorem cutFree_smul_mem {u : SL3} (hu : u ∈ U) {x : X3}
    (hx : x ∈ cutFree U) : u • x ∈ cutFree U := by
  intro v hv hveq
  have hconj : (u⁻¹ * v * u) • x = x := by
    calc (u⁻¹ * v * u) • x = (u⁻¹ * (v * u)) • x := by rw [mul_assoc]
      _ = u⁻¹ • ((v * u) • x) := mul_smul _ _ _
      _ = u⁻¹ • (v • (u • x)) := by rw [mul_smul]
      _ = u⁻¹ • (u • x) := by rw [hveq]
      _ = (u⁻¹ * u) • x := (mul_smul _ _ _).symm
      _ = x := by rw [inv_mul_cancel, one_smul]
  have hmem : u⁻¹ * v * u ∈ U := U.mul_mem (U.mul_mem (U.inv_mem hu) hv) hu
  have h1 := hx _ hmem hconj
  have h2 : v = u * (u⁻¹ * v * u) * u⁻¹ := by group
  rw [h2, h1, mul_one, mul_inv_cancel]

/-- **`aDiag t` preserves the free locus.**  Both implications are the conjugation identity
`U_{aDiag t • x} = aDiag t · U_x · (aDiag t)⁻¹` together with the normalisation of `U` by the
diagonal group, which is the second field of `IsHoro`. -/
theorem aDiag_smul_mem_cutFree_iff (hU : IsHoro U) {x : X3} :
    aDiag t • x ∈ cutFree U ↔ x ∈ cutFree U := by
  constructor
  · intro hy v hv hveq
    have hconj : (aDiag t * v * (aDiag t)⁻¹) • (aDiag t • x) = aDiag t • x := by
      calc (aDiag t * v * (aDiag t)⁻¹) • (aDiag t • x)
          = ((aDiag t * v * (aDiag t)⁻¹) * aDiag t) • x := (mul_smul _ _ _).symm
        _ = (aDiag t * v) • x := by rw [mul_assoc, inv_mul_cancel, mul_one]
        _ = aDiag t • (v • x) := mul_smul _ _ _
        _ = aDiag t • x := by rw [hveq]
    have hmem : aDiag t * v * (aDiag t)⁻¹ ∈ U := hU.2.1 t v hv
    have h1 := hy _ hmem hconj
    have h2 : v = (aDiag t)⁻¹ * (aDiag t * v * (aDiag t)⁻¹) * aDiag t := by group
    rw [h2, h1, mul_one, inv_mul_cancel]
  · intro hy v hv hveq
    have hconj : ((aDiag t)⁻¹ * v * aDiag t) • x = x := by
      calc ((aDiag t)⁻¹ * v * aDiag t) • x
          = (aDiag t)⁻¹ • (v • (aDiag t • x)) := by rw [mul_smul, mul_smul]
        _ = (aDiag t)⁻¹ • (aDiag t • x) := by rw [hveq]
        _ = x := by rw [← mul_smul, inv_mul_cancel, one_smul]
    have hmem : (aDiag t)⁻¹ * v * aDiag t ∈ U := by
      have h := hU.2.1 (-t) v hv
      rw [inv_eq_of_mul_eq_one_left (Work.EKLContract.aDiag_mul_neg t)] at h
      rw [inv_eq_of_mul_eq_one_left (Work.EKLContract.aDiag_neg_mul t)]
      exact h
    have h1 := hy _ hmem hconj
    have h2 : v = aDiag t * ((aDiag t)⁻¹ * v * aDiag t) * (aDiag t)⁻¹ := by group
    rw [h2, h1, mul_one, mul_inv_cancel]

/-- The preimage form of `aDiag_smul_mem_cutFree_iff`. -/
theorem preimage_aDiag_cutFree (hU : IsHoro U) (t : Fin 3 → ℝ) :
    (fun y : X3 => aDiag t • y) ⁻¹' cutFree U = cutFree U :=
  Set.ext fun _ => aDiag_smul_mem_cutFree_iff hU

/-! ## The requested statement -/

theorem cutFree_transfer {U : Subgroup Work.EKLContract.SL3} (hU : Work.EKLContract.IsHoro U)
    (t : Fin 3 → ℝ) :
    (∀ u ∈ U, (fun y : Work.EKLContract.X3 => u • y) '' Work.EKLC6Core.cutFree U ⊆
      Work.EKLC6Core.cutFree U) ∧
    ((fun y : Work.EKLContract.X3 => Work.EKLContract.aDiag t • y) ⁻¹' Work.EKLC6Core.cutFree U =
      Work.EKLC6Core.cutFree U) ∧
    (∀ x : Work.EKLContract.X3, x ∈ Work.EKLC6Core.cutFree U →
      ∀ u ∈ U, u • x = x → u = 1) := by
  refine ⟨?_, ?_, ?_⟩
  · rintro u hu y ⟨z, hz, rfl⟩
    exact cutFree_smul_mem hu hz
  · exact preimage_aDiag_cutFree hU t
  · intro x hx u hu
    exact hx u hu

end Work.EKLC6Core
