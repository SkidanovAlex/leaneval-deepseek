import Mathlib
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# A transversal of the left cosets (the coset bookkeeping of the twist map)

This is the coset bookkeeping needed by `Submission/Work/SSGRoute/C6Detector/kummerLevel_quotient.lean`
for **surjectivity** of the descended twist map `twistMapQuotient` onto the left-`N`-invariants.

## The mathematics

For a subgroup `N ≤ Γ` a transversal of the left cosets is a function `rep : Γ → Γ` with

* `rep (n * g) = rep g` for all `n : N` (it factors through the left-coset quotient `N\Γ`), and
* `n * rep g = g` for some `n : N` (equivalently `rep g ∈ N g`, i.e. it is a member of `g`'s coset).

Such a `rep` exists for any group (no finiteness needed): take the composite of the quotient map
`Γ → N\Γ` with `Quotient.out`.  With it, for a left-`N`-invariant `f : Γ → ZMod p`, the function

    h := fun σ => if rep σ = σ then f (σ⁻¹) else 0

has exactly one non-zero value on each left coset, so that the coset-sum computation

    twistMap p N h g = f g

gives `twistMap p N h = f`; descending along `twistMapQuotient` gives surjectivity, hence (with the
basis law `twistMapQuotient_mk_single_of_*` already proved) the linear equivalence
`V/H₀ ≅ coInd_N^{Γ} 𝔽_p`.

## The four elaboration traps (all resolved in this file)

Reviewed twice ("looks correct as stated").  An earlier attempt inside `kummerLevel_quotient.lean`
got as far as the setoid and died on *elaboration*, not mathematics.  The traps, and the fixes that
are now in the proof below:

1. `Quotient.mk` takes the `Setoid` **explicitly**.  With the setoid introduced as a local
   definition, the placeholders `Quotient.mk _ g` and `Quotient _` do **not** synthesize
   ("don't know how to synthesize implicit argument"); this version writes the local `s` at every
   `Quotient.mk s …` site, so all occurrences are syntactically the same term and the `rw` in the
   first clause fires.
2. The setoid's `symm`/`trans` need `Subgroup.coe_inv` / `Subgroup.coe_mul` applied **before**
   `group`: the goal `↑(n⁻¹) * ↑n * y = y` is not closed while the coercion is opaque.
3. The `refl` witness must be typed (`(1 : ↥N)`), otherwise the numeral is ambiguous.
4. `Quotient.out (Quotient.mk s g)` appears in the goal as the **beta-redex**
   `(fun g => ⟦g⟧.out) g`, inside which `rw` cannot see the pattern (the bound variable shadows the
   argument).  Opening each clause with an explicit `show Quotient.out (Quotient.mk s …) = …`
   beta-reduces the redex and the rewrites fire.

The proof is four lines of content once these are in place: the setoid, the section `Quotient.out`,
and the two clauses.
-/

namespace Work.SSGRoute.C6Detector

/-- **A transversal of the left cosets.**  For a subgroup `N` of a group `Γ` there is a choice of one
representative per left coset `N g`: a function `rep : Γ → Γ` which is constant on each left coset
(`rep (n * g) = rep g`) and whose value at `g` lies in `g`'s coset (`n * rep g = g` for some
`n : N`). -/
theorem exists_leftCosetRepresentative {Γ : Type} [Group Γ] (N : Subgroup Γ) :
    ∃ rep : Γ → Γ,
      (∀ (n : ↥N) (g : Γ), rep ((n : Γ) * g) = rep g) ∧
      (∀ g : Γ, ∃ n : ↥N, (n : Γ) * rep g = g) := by
  classical
  -- the setoid of left cosets: `a` lies in the left coset of `b`
  let s : Setoid Γ :=
    { r := fun a b => ∃ n : ↥N, (n : Γ) * b = a
      iseqv := ⟨fun a => ⟨(1 : ↥N), by simp⟩,
        fun h => by
          obtain ⟨n, hn⟩ := h
          exact ⟨n⁻¹, by rw [← hn, Subgroup.coe_inv]; group⟩,
        fun h1 h2 => by
          obtain ⟨n₁, hn₁⟩ := h1
          obtain ⟨n₂, hn₂⟩ := h2
          exact ⟨n₁ * n₂, by rw [Subgroup.coe_mul, mul_assoc, hn₂, hn₁]⟩⟩ }
  refine ⟨fun g => Quotient.out (Quotient.mk s g), ?_, ?_⟩
  · intro n g
    have h : (Quotient.mk s ((n : Γ) * g)) = Quotient.mk s g := Quotient.sound ⟨n, rfl⟩
    show Quotient.out (Quotient.mk s ((n : Γ) * g)) = Quotient.out (Quotient.mk s g)
    rw [h]
  · intro g
    obtain ⟨n, hn⟩ := Quotient.exact (Quotient.out_eq (Quotient.mk s g))
    refine ⟨n⁻¹, ?_⟩
    show ((n⁻¹ : ↥N) : Γ) * Quotient.out (Quotient.mk s g) = g
    rw [← hn, Subgroup.coe_inv]
    group

end Work.SSGRoute.C6Detector
