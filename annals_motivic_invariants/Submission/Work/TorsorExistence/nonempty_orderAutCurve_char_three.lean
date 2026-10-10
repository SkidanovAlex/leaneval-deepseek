import Mathlib
import Submission.Work.Arithmetic.Defs
import Submission.Work.Arithmetic.Aut_orderOf_dvd_of_short
import Submission.Work.TorsorExistence.Defs

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

set_option autoImplicit false
set_option linter.style.haveILetI false

namespace Work.TorsorExistence

noncomputable section

/-!
# An elliptic curve with no automorphism of order `4` in characteristic `3`

The curve `E : y² = x³ + x² + 1`, i.e. the Weierstrass model `⟨0, 1, 0, 0, 1⟩`, is elliptic in
characteristic `3` with `j(E) = 2 ≠ 0 = 1728`, and every automorphism of it satisfies `σ ^ 2 = 1`
(Silverman, *AEC*, A.1.2).  Hence it is an `OrderAutCurve`.
-/

/-- The discriminant of `E : y² = x³ + x² + 1` is `-496`; in characteristic `3` this is `2`. -/
private lemma charThree_Δ {𝕜 : Type} [Field 𝕜] :
    (⟨0, 1, 0, 0, 1⟩ : WeierstrassCurve 𝕜).Δ = -496 := by
  simp only [WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄, WeierstrassCurve.b₆,
    WeierstrassCurve.b₈]
  norm_num

/-- The invariant `c₄` of `E : y² = x³ + x² + 1` is `16`; in characteristic `3` this is `1`. -/
private lemma charThree_c₄ {𝕜 : Type} [Field 𝕜] :
    (⟨0, 1, 0, 0, 1⟩ : WeierstrassCurve 𝕜).c₄ = 16 := by
  simp only [WeierstrassCurve.c₄, WeierstrassCurve.b₂, WeierstrassCurve.b₄]
  norm_num

/-- `2 ≠ 0` in a field of characteristic `3`. -/
private lemma charThree_two_ne_zero {𝕜 : Type} [Field 𝕜] [CharP 𝕜 3] : (2 : 𝕜) ≠ 0 := by
  have h : ((2 : ℕ) : 𝕜) ≠ 0 := by
    intro h
    rw [CharP.cast_eq_zero_iff 𝕜 3] at h
    norm_num at h
  simpa using h

/-- `-496 ≠ 0` in a field of characteristic `3` (`-496 ≡ 2`). -/
private lemma charThree_m496_ne_zero {𝕜 : Type} [Field 𝕜] [CharP 𝕜 3] : (-496 : 𝕜) ≠ 0 := by
  have h : ((496 : ℕ) : 𝕜) ≠ 0 := by
    intro h
    rw [CharP.cast_eq_zero_iff 𝕜 3] at h
    norm_num at h
  intro h1
  exact h (neg_eq_zero.mp h1)

/-- `16 ≠ 0` in a field of characteristic `3` (`16 ≡ 1`). -/
private lemma charThree_16_ne_zero {𝕜 : Type} [Field 𝕜] [CharP 𝕜 3] : (16 : 𝕜) ≠ 0 := by
  have h : ((16 : ℕ) : 𝕜) ≠ 0 := by
    intro h
    rw [CharP.cast_eq_zero_iff 𝕜 3] at h
    norm_num at h
  simpa using h

/-- `1728 = 2 ^ 6 * 3 ^ 3 = 0` in a field of characteristic `3`. -/
private lemma charThree_1728_eq_zero {𝕜 : Type} [Field 𝕜] [CharP 𝕜 3] : (1728 : 𝕜) = 0 := by
  have h : ((1728 : ℕ) : 𝕜) = 0 := by
    rw [CharP.cast_eq_zero_iff 𝕜 3]
    norm_num
  simpa using h

/-- `E : y² = x³ + x² + 1` is an elliptic curve in characteristic `3`, since
`Δ = -496 ≡ 2 ≠ 0`. -/
private lemma charThree_isElliptic {𝕜 : Type} [Field 𝕜] [CharP 𝕜 3] :
    (⟨0, 1, 0, 0, 1⟩ : WeierstrassCurve 𝕜).IsElliptic := by
  rw [WeierstrassCurve.isElliptic_iff, charThree_Δ (𝕜 := 𝕜)]
  exact isUnit_iff_ne_zero.mpr charThree_m496_ne_zero

/-- Every automorphism `σ` of `E : y² = x³ + x² + 1` over a field of characteristic `3`
has order dividing `2`; the coefficient comparison is over the admissible changes of variables
`C = (u, r, s, t)` fixing `E`. -/
private lemma charThree_aut_orderOf_dvd_two {𝕜 : Type} [Field 𝕜] [CharP 𝕜 3]
    (σ : Work.Arithmetic.Aut 𝕜 (⟨0, 1, 0, 0, 1⟩ : WeierstrassCurve 𝕜)) : orderOf σ ∣ 2 := by
  let C : WeierstrassCurve.VariableChange 𝕜 := ↑σ
  have hC : C • (⟨0, 1, 0, 0, 1⟩ : WeierstrassCurve 𝕜) = ⟨0, 1, 0, 0, 1⟩ := σ.2
  have h3 : (3 : 𝕜) = 0 := CharP.cast_eq_zero 𝕜 3
  -- the `a₁`-coefficient of `C • E = E` gives `2 * s = 0`, so `s = 0`
  have hs : C.s = 0 := by
    have h := congrArg WeierstrassCurve.a₁ hC
    rw [WeierstrassCurve.variableChange_a₁] at h
    simp at h
    exact h.resolve_left charThree_two_ne_zero
  -- the `a₃`-coefficient gives `2 * t = 0`, so `t = 0`
  have ht : C.t = 0 := by
    have h := congrArg WeierstrassCurve.a₃ hC
    rw [WeierstrassCurve.variableChange_a₃] at h
    simp at h
    exact h.resolve_left charThree_two_ne_zero
  -- the `a₄`-coefficient gives `2 * r = 0`, so `r = 0`
  have hr : C.r = 0 := by
    have h := congrArg WeierstrassCurve.a₄ hC
    rw [WeierstrassCurve.variableChange_a₄] at h
    simp [hs, ht, h3] at h
    exact h.resolve_left charThree_two_ne_zero
  -- the `a₂`-coefficient gives `u ^ 2 = 1`
  have hu2 : C.u ^ 2 = 1 := by
    have h := congrArg WeierstrassCurve.a₂ hC
    rw [WeierstrassCurve.variableChange_a₂] at h
    simp [hs, h3] at h
    rcases h with h | h
    · rw [h]; simp
    · rw [h]; simp
  -- hence `C = (u, 0, 0, 0)` and `C ^ 2 = 1`
  have hCeq : C = ⟨C.u, 0, 0, 0⟩ := by ext <;> simp [hs, hr, ht]
  have hC2 : C ^ 2 = 1 := by
    rw [hCeq, Work.Arithmetic.vc_pow_zero, hu2, WeierstrassCurve.VariableChange.one_def]
  rw [← Subgroup.orderOf_coe σ]
  change orderOf C ∣ 2
  rw [orderOf_dvd_iff_pow_eq_one]
  exact hC2

/-- Over a field of characteristic `3` there is an elliptic curve with `j ≠ 1728` and with
every automorphism of order dividing `2` or `6` (Silverman, *AEC*, A.1.2).  (Route: take
`E : y² = x³ + x² + 1`, i.e. the Weierstrass curve `⟨0, 1, 0, 0, 1⟩`; then `b₂ = b₆ = b₈ = 1`,
`b₄ = 0`, `Δ = -1 = 2 ≠ 0` and `j = c₄³/Δ = 1/2 = 2 ≠ 0 = 1728` in characteristic `3`.
Comparing the coefficients of an admissible variable change `C = (u, r, s, t)` with `C • E = E`
using the lemmas `WeierstrassCurve.variableChange_aᵢ` gives `s = t = r = 0` and `u ^ 2 = 1`, so
that `C ^ 2 = 1`.) -/
theorem nonempty_orderAutCurve_char_three {𝕜 : Type} [Field 𝕜] [CharP 𝕜 3] :
    Nonempty (OrderAutCurve 𝕜) := by
  haveI : (⟨0, 1, 0, 0, 1⟩ : WeierstrassCurve 𝕜).IsElliptic := charThree_isElliptic
  refine ⟨{ E := ⟨0, 1, 0, 0, 1⟩, j_ne := ?_, order_aut := ?_ }⟩
  · -- `j ≠ 0` because `c₄ = 16 ≠ 0`, while `1728 = 2 ^ 6 * 3 ^ 3 = 0`
    intro h
    rw [charThree_1728_eq_zero] at h
    have hc4 : (⟨0, 1, 0, 0, 1⟩ : WeierstrassCurve 𝕜).c₄ ^ 3 ≠ 0 := by
      rw [charThree_c₄ (𝕜 := 𝕜)]
      exact pow_ne_zero 3 charThree_16_ne_zero
    rw [WeierstrassCurve.j_eq_zero_iff'] at h
    exact hc4 h
  · -- `σ ^ 2 = 1`, so `orderOf σ ∣ 2`
    intro σ
    exact Or.inl (charThree_aut_orderOf_dvd_two σ)

end

end Work.TorsorExistence
