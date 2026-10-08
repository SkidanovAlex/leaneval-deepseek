import Mathlib
import Submission.Work.BG.ThmABCCharDefs
import Submission.Work.BG.s02_lamDual
import Submission.Work.BG.s02_assemblyCore

/-!
# Area BG: the fibre of `β ↦ λ_β ν` over `μ` has the cardinality of `Λ_ν`  (Remark 3.1)

Bender–Glauberman, Remark 3.1 (used in the proof of Theorem 3.2, p. 208): if `μ` lies in the
`Λ`-orbit of `ν` (i.e. `LamEquiv C μ ν`), then

`#{β ∈ Λ | λ_β ν = μ} = |Λ_ν|`,

the number of `Λ`-twists of `ν` producing `μ` is the order of the stabiliser `Λ_ν`.

This is the purely group-theoretic statement that the fibre of the orbit map `β ↦ λ_β ν` over a
point of the orbit is a coset of `Λ_ν`: choosing `β₀` with `ν = λ_{β₀} μ`, the map
`β ↦ β₀ β` is a bijection from the fibre over `μ` onto `Λ_ν`, with inverse `γ ↦ β₀⁻¹ γ`.

Formalisation detail: `lamCF C β` is `λ_β` inflated from `H₀/U`, and pointwise multiplication by
`λ_β` is bijective, which is packaged here as the cancellation lemmas
`lamCF_cancel_right`/`lamCF_cancel_left`.
-/

namespace Work.BG

open OddOrder.RepresentationTheory

variable {G : Type} [Group G] [Finite G]

/-! ## The algebra of `lamCF` needed for the fibre computation -/

/-- Reassociation: `λ_β (λ_γ ν) = λ_{βγ} ν`. -/
theorem lamCF_mul_assoc_aux (C : Sec2Ctx G) (β γ : lamDual C) (ν : ClassFunction ↥C.P.H0 ℂ) :
    lamCF C β * (lamCF C γ * ν) = lamCF C (β * γ) * ν := by
  rw [← mul_assoc_cf, ← lamCF_mul]

/-- Cancellation: `λ_β⁻¹ (λ_β ν) = ν`. -/
theorem lamCF_cancel_aux (C : Sec2Ctx G) (β : lamDual C) (ν : ClassFunction ↥C.P.H0 ℂ) :
    lamCF C β⁻¹ * (lamCF C β * ν) = ν := by
  rw [← mul_assoc_cf, ← lamCF_mul, show β⁻¹ * β = 1 from inv_mul_cancel β, lamCF_one,
    one_mul_cf]

/-- Cancellation, other order: `λ_β (λ_β⁻¹ ν) = ν`. -/
theorem lamCF_cancel_left_aux (C : Sec2Ctx G) (β : lamDual C) (ν : ClassFunction ↥C.P.H0 ℂ) :
    lamCF C β * (lamCF C β⁻¹ * ν) = ν := by
  rw [← mul_assoc_cf, ← lamCF_mul, show β * β⁻¹ = 1 from mul_inv_cancel β, lamCF_one,
    one_mul_cf]

/-! ## The fibre cardinality -/

/-- **Remark 3.1, count of twists.** For `μ` in the `Λ`-orbit of `ν`, the set of `β ∈ Λ = (H₀/U)^*`
with `λ_β ν = μ` (i.e. `lamCF C β * ν = μ`) is in bijection with the stabiliser `Λ_ν`, hence has
cardinality `|Λ_ν|`. -/
theorem rem31CardFiber {G : Type} [Group G] [Finite G] (C : Work.BG.Sec2Ctx G)
    [Fintype (Work.BG.lamDual C)] {μ ν : OddOrder.RepresentationTheory.ClassFunction ↥C.P.H0 ℂ}
    (h : Work.BG.LamEquiv C μ ν) :
    Nat.card {β : Work.BG.lamDual C // Work.BG.lamCF C β * ν = μ}
      = Nat.card ↥(Work.BG.lamStab C ν) := by
  -- `β₀` is a twist taking `μ` to `ν`, so `λ_{β₀⁻¹} ν = μ`.
  obtain ⟨β₀, hβ₀⟩ := h
  have hμ : lamCF C β₀⁻¹ * ν = μ := by rw [hβ₀, lamCF_cancel_aux]
  -- The bijection `β ↦ β₀ β` from the fibre over `μ` onto `Λ_ν`.
  refine Nat.card_congr ?_
  refine
    { toFun := fun β => ⟨β₀ * β.1, ?_⟩
      invFun := fun γ => ⟨β₀⁻¹ * γ.1, ?_⟩
      left_inv := ?_
      right_inv := ?_ }
  · show lamCF C (β₀ * β.1) * ν = ν
    rw [← lamCF_mul_assoc_aux C β₀ β.1 ν, β.2, ← hμ, lamCF_cancel_left_aux]
  · show lamCF C (β₀⁻¹ * γ.1) * ν = μ
    rw [← lamCF_mul_assoc_aux C β₀⁻¹ γ.1 ν, (mem_lamStab C ν γ.1).mp γ.2, hμ]
  · intro β
    refine Subtype.ext ?_
    show β₀⁻¹ * (β₀ * β.1) = β.1
    exact inv_mul_cancel_left β₀ β.1
  · intro γ
    refine Subtype.ext ?_
    show β₀ * (β₀⁻¹ * γ.1) = γ.1
    exact mul_inv_cancel_left β₀ γ.1

end Work.BG
