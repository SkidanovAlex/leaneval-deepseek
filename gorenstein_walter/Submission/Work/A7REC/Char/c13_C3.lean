import Mathlib
import Submission.Work.A7REC.Defs
import Submission.Work.A7REC.Char.cardInvolutionsCentralizerNorm

/-!
# `c13_C3`: the involutions of `C_G(z)` and the ones inverting `σ`

Design pass 13, `_design_gw/Core13.lean` §3, `C3`.  In the `A₇`-configuration of `A7RecCtx`
(so in particular `U ⊴ C_G(z)`, which is the field `A7RecCtx.hUnorm`) the centralizer
`C = C_G(z) = U ⋊ S` has exactly `9` involutions, and exactly `6` of them invert `σ`.

Both counts are proved in `Submission/Work/A7REC/Char/cardInvolutionsCentralizerNorm.lean`
as `Work.A7REC.Char.A7InvCtx.cardInvolutionsCentralizer_of_normal` and
`Work.A7REC.Char.A7InvCtx.card_involutions_inverting_σ`, for the context `A7InvCtx` (which is
the set of hypotheses used by `c13_C3`, minus `U ⊴ C_G(z)`, plus that normality).  The content
here is only the transport of `A7RecCtx` to `A7InvCtx`; the arithmetic (which is the real
content of `C3`, already worked out in the proof plan of the cited file) is not repeated.

For completeness, the argument behind those two lemmas, in the notation of the cited file:
`C = U ⋊ S`, `K = C_S(U) = S ⊓ C_G(U)` is a four-group (the action of `S` on `U ≅ Z₃` is
nontrivial, since `π ∉ K`, and `K` cannot contain the two elements of order `4` of `S ≅ D₈`),
so `K#` is `3` of the `5` involutions of `S` and `S ∖ K` contains `2`; an element `u * s`
(`u ∈ U`, `s ∈ S`, the unique decomposition) is an involution iff `s``^2 = 1` and (`u = 1` or
`s ∉ K`), giving `5 + 2 · 2 = 9`; and since `U` is abelian, `u * s` inverts `σ` iff `s` does,
i.e. iff `s ∉ K`, which with `s^2 = 1` gives `|U| · 2 = 6`.
-/

namespace Work.A7REC.Char

open Subgroup

/-- **`C3`.**  In the `A₇`-configuration with `U ⊴ C_G(z)`, the centralizer `C_G(z)` has exactly
`9` involutions, and exactly `6` of those invert the nontrivial element `σ` of `U`. -/
theorem c13_C3 (G : Type*) [Group G] [Finite G] (ctx : Work.A7REC.A7RecCtx G) (π σ : G)
    (hσ : σ ∈ ctx.U) (hσ1 : σ ≠ 1) (hπS : π ∈ ctx.Ssub) (hπ4 : orderOf π = 4)
    (hCπ : Subgroup.centralizer ({π} : Set G) = Subgroup.zpowers π) :
    {a : G | a ∈ ctx.C ∧ orderOf a = 2}.ncard = 9 ∧
      {a : G | a ∈ ctx.C ∧ orderOf a = 2 ∧ a * σ * a⁻¹ = σ⁻¹}.ncard = 6 := by
  -- Transport the `A₇`-hypotheses into the shape used by the counting file.  All the fields of
  -- `A7InvCtx` are literally fields of `A7RecCtx`, so this is a matter of re-packaging.
  let h : A7InvCtx G :=
    { S := ctx.S
      hSdih := ctx.hSdih
      z := ctx.z
      hzS := ctx.hzS
      hz2 := ctx.hz2
      U := ctx.U
      hU3 := ctx.hUcard
      hC := ctx.hCz
      π := π
      hπS := hπS
      hπ4 := hπ4
      hCπ := hCπ
      σ := σ
      hσU := hσ
      hσ1 := hσ1 }
  -- `U ⊴ C_G(z)` is the field `hUnorm` of the context.
  have hnorm : (h.U.subgroupOf h.C).Normal := ctx.hUnorm
  exact ⟨A7InvCtx.cardInvolutionsCentralizer_of_normal h hnorm,
    A7InvCtx.card_involutions_inverting_σ h hnorm⟩

end Work.A7REC.Char
