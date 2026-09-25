/-
# The `𝒪[F]`-orbit of a primitive torsion point

Milne, *Classical Field Theory*, Theorem I.3.1: the level `Λ_n` of `π^n`-torsion points of the
Lubin–Tate group of `π` is a free `𝒪[F]/π^n`-module of rank one.  This file records the
consequence of that statement which the local reciprocity law consumes: for a **primitive** point
`y ∈ Λ_n ∖ Λ_{n-1}` (hence a generator of the rank-one module), two multipliers `a b ∈ 𝒪[F]` give
the same point exactly when they agree modulo `π^n`:

  `a · y = b · y  ↔  a - b ∈ 𝔪[F]^n`.

Equivalently, the map `a ↦ a · y` induces an isomorphism `𝒪[F]/π^n ≅ Λ_n`.

## The proof

The kernel of `a ↦ a · y` is `(π^n)` — this is `Eval.smulDiv_eq_zero_iff` (the annihilator of a
primitive point), and the ideal `(π^n)` is the `n`-th power of the maximal ideal because `π` is a
uniformiser (`Irreducible.maximalIdeal_eq`).  It remains to see that `a · y = b · y` is *equivalent*
to `(a - b) · y = 0`.  The action `a ↦ a · y` is **not** additive in `a` (the addition law of the
Lubin–Tate group law is not the addition of `F`), so this needs the corrected addition formula of
`Eval/smulDiv_add.lean`: writing `a = b + (a - b)`,

  `a · y = b · y + ((a - b) · y) · H`

with `H ≠ 0`, which gives both directions at once.
-/
import Mathlib
import Submission.NK.LocalReciprocityLubinTate.Eval.ltLevelIsSimple_of_fibre
import Submission.NK.LocalReciprocityLubinTate.Eval.smulDiv_ann
import Submission.NK.LocalReciprocityLubinTate.Eval.smulDiv_add
import Submission.NK.LocalReciprocityLubinTate.Eval.smulDiv_level
import Submission.NK.LocalReciprocityLubinTate.LubinTate.Integers

namespace NK.LocalReciprocityLubinTate.LubinTate

open scoped ValuativeRel

/-- **Two multipliers give the same point on a primitive torsion point iff they agree modulo `π^n`.**
For `y ∈ Λ_n ∖ Λ_{n-1}` and `a b ∈ 𝒪[F]`,

  `a · y = b · y ↔ a - b ∈ 𝔪[F]^n`,

so that the action of `𝒪[F]` on the rank-one `𝒪[F]/π^n`-module `Λ_n` has kernel exactly `(π^n)`. -/
theorem smulDiv_eq_iff_sub_mem {F : Type*} [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    (π : ↥(ValuativeRel.valuation F).integer) (hπ : Irreducible π) (n : ℕ) (hn : 1 ≤ n)
    (M : LubinTateModule (↥(ValuativeRel.valuation F).integer) π
      (NK.LocalReciprocityLubinTate.residueCard F))
    (hpi : M.toLaw.piEndo = NK.LocalReciprocityLubinTate.piXAddXq π
      (NK.LocalReciprocityLubinTate.residueCard F))
    {y : AlgebraicClosure F}
    (hy : y ∈ NK.LocalReciprocityLubinTate.LTdivisionSet F (π : F)
      (NK.LocalReciprocityLubinTate.residueCard F) n)
    (hy' : y ∉ NK.LocalReciprocityLubinTate.LTdivisionSet F (π : F)
      (NK.LocalReciprocityLubinTate.residueCard F) (n - 1))
    (a b : ↥(ValuativeRel.valuation F).integer) :
    NK.LocalReciprocityLubinTate.Eval.smulDiv π hπ
        (NK.LocalReciprocityLubinTate.residueCard F) n
        (NK.LocalReciprocityLubinTate.two_le_residueCard F) M hy a =
      NK.LocalReciprocityLubinTate.Eval.smulDiv π hπ
        (NK.LocalReciprocityLubinTate.residueCard F) n
        (NK.LocalReciprocityLubinTate.two_le_residueCard F) M hy b ↔
      a - b ∈ (IsLocalRing.maximalIdeal ↥(ValuativeRel.valuation F).integer) ^ n := by
  obtain ⟨Θ, hΘ, hlaw⟩ := LubinTateModule.exists_unit_factorization π hπ
    (NK.LocalReciprocityLubinTate.residueCard F) M
  -- The addition formula `a · y = b · y + ((a - b) · y) · H` with `H ≠ 0` converts equality of
  -- the two points into the vanishing of `(a - b) · y`.
  have key : NK.LocalReciprocityLubinTate.Eval.smulDiv π hπ
        (NK.LocalReciprocityLubinTate.residueCard F) n
        (NK.LocalReciprocityLubinTate.two_le_residueCard F) M hy (a - b) = 0 ↔
      NK.LocalReciprocityLubinTate.Eval.smulDiv π hπ
        (NK.LocalReciprocityLubinTate.residueCard F) n
        (NK.LocalReciprocityLubinTate.two_le_residueCard F) M hy a =
      NK.LocalReciprocityLubinTate.Eval.smulDiv π hπ
        (NK.LocalReciprocityLubinTate.residueCard F) n
        (NK.LocalReciprocityLubinTate.two_le_residueCard F) M hy b := by
    obtain ⟨H, hH, hform⟩ := NK.LocalReciprocityLubinTate.Eval.smulDiv_add_formula π hπ
      (NK.LocalReciprocityLubinTate.residueCard F) n
      (NK.LocalReciprocityLubinTate.two_le_residueCard F) M Θ hΘ hlaw hy b (a - b)
    rw [add_sub_cancel] at hform
    constructor
    · intro hd
      rw [hform, hd, zero_mul, add_zero]
    · intro h
      have hz : NK.LocalReciprocityLubinTate.Eval.smulDiv π hπ
          (NK.LocalReciprocityLubinTate.residueCard F) n
          (NK.LocalReciprocityLubinTate.two_le_residueCard F) M hy (a - b) * H = 0 := by
        have hh : NK.LocalReciprocityLubinTate.Eval.smulDiv π hπ
              (NK.LocalReciprocityLubinTate.residueCard F) n
              (NK.LocalReciprocityLubinTate.two_le_residueCard F) M hy b +
            NK.LocalReciprocityLubinTate.Eval.smulDiv π hπ
              (NK.LocalReciprocityLubinTate.residueCard F) n
              (NK.LocalReciprocityLubinTate.two_le_residueCard F) M hy (a - b) * H =
            NK.LocalReciprocityLubinTate.Eval.smulDiv π hπ
              (NK.LocalReciprocityLubinTate.residueCard F) n
              (NK.LocalReciprocityLubinTate.two_le_residueCard F) M hy b + 0 := by
          rw [add_zero, ← hform, h]
        exact add_left_cancel hh
      rcases mul_eq_zero.mp hz with h1 | h1
      · exact h1
      · exact absurd h1 hH
  -- `(a - b) · y = 0` iff `a - b ∈ (π^n)`, and `(π^n) = 𝔪[F]^n` for a uniformiser `π`.
  rw [← key, NK.LocalReciprocityLubinTate.Eval.smulDiv_eq_zero_iff π hπ
      (NK.LocalReciprocityLubinTate.residueCard F) n
      (NK.LocalReciprocityLubinTate.two_le_residueCard F) M hpi hy hy' hn (a - b),
    ← Ideal.span_singleton_pow, ← hπ.maximalIdeal_eq]

end NK.LocalReciprocityLubinTate.LubinTate
