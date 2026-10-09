import Mathlib
import Submission.Work.SSGRoute.ZConstruction.AuxExistsUnmixed
import Submission.Work.SSGRoute.ZConstruction.exists_junkSpan_complement
import Submission.Work.SSGRoute.ZConstruction.auxExistsGap_of_pairing_and_unmixed
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The line decomposition of the §4 induction that satisfies the no-gap condition

`Work.SSGRoute.ZConstruction.AuxExistsGap` (`ZConstruction/AuxExistsUnmixed.lean`) is the
auxiliary-class obligation of Schmidt--Wingberg §4 with the no-gap condition
`AuxGapFun K Λ S N y₁` as an extra hypothesis on the one-dimensional datum `y₁` at hand.  It is the
correct obligation: the uniform provision `AuxGapProv` (for *every* `ZHyp` datum) is not needed, and
`Work.SSGRoute.ZConstruction.auxExistsGap_of_pairing_and_unmixed`
(`ZConstruction/auxExistsGap_of_pairing_and_unmixed.lean`, proved) derives it from the pairing gate
and the unmixed realisation gate alone.

This file packages the way the no-gap hypothesis is supplied for the *line component* of the §4
induction.  Let

    junkSpan K Λ S y

be the span of the values of `y` on the inertia groups of the `Λ`-split places outside `cs(S)`
(`ZConstruction/AuxExistsUnmixed.lean`).  Then

* `auxGapFun_comp_of_junkSpan_le` (proved): if `E₀ ⊇ junkSpan K Λ S y` and `π` vanishes on `E₀`,
  then `π ∘ y` satisfies `AuxGapFun` at every level;
* `exists_junkSpan_complement` (`ZConstruction/exists_junkSpan_complement.lean`, proved): if
  `junkSpan K Λ S y ≠ ⊤` and `2 ≤ finrank E`, then such a decomposition `E = E₀ ⊕ L` with
  `finrank L = 1`, `finrank E₀ < finrank E` and `junkSpan K Λ S y ≤ E₀` exists.

Combining them, `exists_line_decomposition_auxGap` below produces, for every datum `y` whose junk
ramification is *proper*, a line decomposition `E = E₀ ⊕ L` of the shape used by the §4 induction
(`Work.SSGRoute.line_complement_decomposition`) whose line component satisfies the no-gap condition
at *every* level -- hence, in particular, at the level `N₀ ⊔ Λ` of the induction step.

**Caution (recorded, not formalised).**  This arrangement does not iterate: since `π₀ : E → E₀` is
surjective, `π₀` of a *spanning* junk set spans `E₀`, so the component `π₀ ∘ y` of the next step
again has a spanning junk set; and more generally a hyperplane containing a codimension-one junk
span coincides with it.  So the arrangement can be maintained through the recursion of
`ZConstruction/ZDataAux.lean` only when `junkSpan = 0`, i.e. when the datum is unramified at *every*
place outside `cs(S)` -- Schmidt--Wingberg's (H1), which is stronger than the node's `ZHyp.hyS`.
See `ZConstruction/NOTE_session21.lean`, §4c and §4d, for the full discussion.
-/

open scoped Pointwise BigOperators

open Classical

namespace Work.SSGRoute.ZConstruction

open _root_.SSGRoute

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option maxHeartbeats 1600000

/-- **The line decomposition of the §4 induction whose line component satisfies the no-gap
condition at every level.**

If the ramification of `y` at the `Λ`-split places outside `cs(S)` does not span the coefficient
module, then there is a decomposition `E = E₀ ⊕ L` with `finrank L = 1`, `finrank E₀ < finrank E`
and `junkSpan K Λ S y ≤ E₀`, and the projection `π₁` onto `L` along `E₀` kills the whole junk span;
consequently `π₁ ∘ y` satisfies `AuxGapFun K Λ S N` for *every* level `N`, which is exactly the
extra hypothesis of the obligation `Work.SSGRoute.ZConstruction.AuxExistsGap`. -/
theorem exists_line_decomposition_auxGap (p : ℕ) [Fact p.Prime] {k Ω : Type} [Field k]
    [NumberField k] [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω]
    {K Λ : IntermediateField k Ω} {S : Finset (ValuationSubring Ω)}
    {E : Type} [AddCommGroup E] [Module (ZMod p) E] [Finite E]
    (y : (Ω ≃ₐ[k] Ω) → E) (hdim : 2 ≤ Module.finrank (ZMod p) E)
    (hproper : junkSpan K Λ S y ≠ ⊤) :
    ∃ (L E₀ : Submodule (ZMod p) E) (_ : IsCompl L E₀) (π₁ : E →ₗ[ZMod p] ↥L),
      Module.finrank (ZMod p) L = 1 ∧
      Module.finrank (ZMod p) E₀ < Module.finrank (ZMod p) E ∧
      (∀ (N : IntermediateField k Ω), AuxGapFun K Λ S N (fun σ => π₁ (y σ))) := by
  obtain ⟨L, E₀, hc, hL, hE₀, hsub, π₀, π₁, hsum, hπ₀, _hπ₁, _hkill⟩ :=
    exists_junkSpan_complement p y hdim hproper
  refine ⟨L, E₀, hc, π₁, hL, hE₀, fun N => ?_⟩
  refine auxGapFun_comp_of_junkSpan_le (K := K) (Λ := Λ) (N := N) (S := S) y E₀.toAddSubgroup
    hsub π₁.toAddMonoidHom ?_
  intro x hx
  have h2 : x + (π₁ x : E) = x := by
    have h3 : (π₀ x : E) + (π₁ x : E) = x := hsum x
    rwa [hπ₀ x hx] at h3
  have h1 : (π₁ x : E) = 0 := by
    have h3 : x + (π₁ x : E) = x + 0 := by rw [add_zero, h2]
    exact add_left_cancel h3
  exact Subtype.ext h1

end Work.SSGRoute.ZConstruction
