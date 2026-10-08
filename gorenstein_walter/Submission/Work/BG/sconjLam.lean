import Mathlib
import Submission.Work.BG.Defs
import Submission.Work.BG.H0Conj
import Submission.Work.BG.S02
import Submission.Work.BG.conjByH_basic

/-!
# Area BG: Lemma 2.1(b) — `s` inverts `Λ`: `(λ_β ν)^s = λ_{β⁻¹} ν^s`

Bender–Glauberman 1981, Lemma 2.1, second assertion (p. 204).  With `Λ` the group of
linear characters of `H₀/U` inflated to `H₀` (`Work.BG.lamCF`), the involution `s ∈ H ∖ H₀`
acts on `CF(H₀)` by `ν ↦ ν^s` (`Work.BG.conjByH`), and it sends `Λ` to `Λ` by inversion of
the character: for `β : H₀/U →* ℂˣ`,

  `(λ_β · ν)^s = λ_{β⁻¹} · ν^s`.

The content is exactly the hypothesis `s_inverts` of `Sec2Ctx` (`s` inverts `H₀/U`, i.e.
`s x s⁻¹ x ∈ U` for all `x ∈ H₀`): on the quotient `H₀/U` this says
`(s x s⁻¹)·U = (x·U)⁻¹`, so inflating `β` along `H₀ → H₀/U` gives
`λ_β(s x s⁻¹) = β((x·U)⁻¹) = β⁻¹(x·U) = λ_{β⁻¹}(x)`.
-/

namespace Work.BG

open OddOrder.RepresentationTheory

variable {G : Type} [Group G] [Finite G]

/-- `s` inverts `H₀/U`: the class of `s h s⁻¹` in `H₀/U` is the inverse of the class of `h`.
This is the quotient form of `Sec2Ctx.s_inverts`. -/
theorem quotMk_conjMulEquiv_eq_inv (C : Sec2Ctx G) (h : ↥C.P.H0) :
    quotMk C.P (conjMulEquiv C.P C.s h) = (quotMk C.P h)⁻¹ := by
  rw [eq_inv_iff_mul_eq_one, ← map_mul]
  refine (QuotientGroup.eq_one_iff (N := C.P.U.subgroupOf C.P.H0) _).mpr ?_
  show ((conjMulEquiv C.P C.s h * h : ↥C.P.H0) : G) ∈ C.P.U
  rw [Subgroup.coe_mul, conjMulEquiv_apply]
  exact C.s_inverts (h : G) h.2

/-- **Bender–Glauberman 1981, Lemma 2.1(b).** `s` maps `Λ` to `Λ` by inversion:
`(λ_β ν)^s = λ_{β⁻¹} ν^s` for every `β : H₀/U →* ℂˣ` and every class function `ν`. -/
theorem sconjLam {G : Type} [Group G] [Finite G] :
    ∀ C : Work.BG.Sec2Ctx G, Work.BG.SconjLamProp C := by
  intro C β ν
  ext h
  simp only [sconj, conjByH, lamCF, ClassFunction.mul_apply, ClassFunction.compHom_apply,
    linearClassFunction_apply, MulEquiv.coe_toMonoidHom]
  rw [quotMk_conjMulEquiv_eq_inv C h]
  simp

end Work.BG
