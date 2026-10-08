/-
# Stage B: a fixed point of `P` on `Q` outside `Q₀`

Peterfalvi II, Ch. VII §4 (1)–(10) (see also the lead's design `PSU3Route.lean`, node B2):
if `x ∈ Q ∖ Q₀` is fixed modulo `Q₀` by an odd-order subgroup `P ≤ D = H ∩ Hᵗ`, then some
element of `Q ∖ Q₀` is fixed by `P` on the nose.

The mechanism is the standard vanishing of `H¹(P, Q₀)` for `P` of odd order acting on the
exponent-`2` group `Q₀`: the crossed homomorphism
`c p = p⁻¹ x p x⁻¹` (whose values lie in `Q₀ = Z(Q)` by hypothesis) is a coboundary, namely
`c p = (p⁻¹ z p) z⁻¹` with `z = ∏_{q ∈ P} c q`; then `y = x z` is the required fixed point:

  `p⁻¹ y p = (p⁻¹ x p)(p⁻¹ z p) = (c p · x)(c p · z) = x z = y`,

the last step because `x` commutes with `Q₀` and `c p` is an involution.

The abstract averaging step is isolated in
`Submission.Work.PSU3.StageB.cocycle_prod_is_coboundary`
(`Work.PSU3.StageB.cocycle_prod_is_coboundary`).
-/
import Mathlib
import Submission.Work.PSU3.StageB.NotFpfAux
import Submission.Work.PSU3.StageB.cocycle_prod_is_coboundary

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option autoImplicit false
set_option linter.unusedVariables false

open LeanEval.GroupTheory.Defs Submission.Blueprint
open Work.ThmF

namespace Work.PSU3.StageB

/-- The averaging step in the shape in which it is used below: if `a` is an involution
centralising `x`, and conjugation by `p` turns `x` into `a x` and `z` into `a z`, then
conjugation by `p` fixes `x z`. -/
private lemma conj_mul_of_coboundary {G : Type} [Group G] {a x z p : G}
    (hxp : p⁻¹ * x * p = a * x) (hzp : p⁻¹ * z * p = a * z)
    (hxc : x * a = a * x) (ha2 : a * a = 1) :
    p⁻¹ * (x * z) * p = x * z := by
  rw [show p⁻¹ * (x * z) * p = (p⁻¹ * x * p) * (p⁻¹ * z * p) by group, hxp, hzp]
  calc (a * x) * (a * z) = a * (x * a) * z := by group
    _ = a * (a * x) * z := by rw [hxc]
    _ = x * z := by rw [← mul_assoc, ha2, one_mul]

/-- **A fixed point of an odd-order `P ≤ D` on `Q` outside `Q₀`.**  If `x ∈ Q ∖ Q₀` is fixed
modulo `Q₀` (i.e. `p⁻¹ x p x⁻¹ ∈ Q₀ = Z(Q)` for all `p ∈ P`), then `P` fixes some
`y ∈ Q ∖ Q₀`. -/
theorem exists_mem_Q_centralized_of_fixed_mod_Q0 {G : Type} [Group G] [Finite G] {H Q : Subgroup G} {t : G}
    (hS : Work.PSU3.PSU3Hyp H Q t) {n : ℕ} (fr : Work.PSU3.CoarseFrame H Q t n)
    {P : Subgroup G} (hPD : P ≤ Submission.Blueprint.twoPoint H t) (hPodd : Odd (Nat.card P))
    {x : G} (hx : x ∈ Q) (hx0 : x ∉ fr.Q0)
    (hfix : ∀ p ∈ P, p⁻¹ * x * p * x⁻¹ ∈ fr.Q0) :
    ∃ y ∈ Q, y ∉ fr.Q0 ∧ ∀ p ∈ P, p⁻¹ * y * p = y := by
  -- `Q₀` is normalised by `P ≤ D ≤ H` (`Q ⊴ H`, and `Q₀ = {q ∈ Q | q² = 1}`, so conjugation
  -- preserves `Q₀` as soon as it preserves `Q`).
  have hQ0norm : ∀ p ∈ P, ∀ a ∈ fr.Q0, p⁻¹ * a * p ∈ fr.Q0 := by
    intro p hp a ha
    have hp1 : p ∈ H := (Subgroup.mem_inf.mp (hPD hp)).1
    have h1 : p⁻¹ * a * p ∈ Q := by
      have h := Work.RankOneUniqueness.conj_mem_of_mem hS.split (H.inv_mem hp1) (fr.Q0_le ha)
      simpa using h
    refine (fr.mem_Q0_iff _ h1).mpr ?_
    have ha2 : a * a = 1 := by simpa [pow_two] using Q0_sq_eq_one fr ha
    rw [pow_two]
    calc (p⁻¹ * a * p) * (p⁻¹ * a * p) = p⁻¹ * (a * a) * p := by group
      _ = 1 := by rw [ha2]; group
  -- `Q₀` is abelian of exponent `2`.
  have hcomm : ∀ a ∈ fr.Q0, ∀ b ∈ fr.Q0, a * b = b * a :=
    fun a ha b hb => fr.Q0_central a ha b (fr.Q0_le hb)
  have hsq : ∀ a ∈ fr.Q0, a * a = 1 :=
    fun a ha => by simpa [pow_two] using Q0_sq_eq_one fr ha
  -- The crossed homomorphism `c p = p⁻¹ x p x⁻¹`; `H¹(P, Q₀) = 0` supplies the correction.
  obtain ⟨z, hzA, hzact⟩ :=
    cocycle_prod_is_coboundary (P := P) (A := fr.Q0) hQ0norm hcomm hsq hPodd
      (fun p => p⁻¹ * x * p * x⁻¹) (fun p hp => hfix p hp)
      (fun r hr p hp => by group)
  refine ⟨x * z, Q.mul_mem hx (fr.Q0_le hzA), ?_, ?_⟩
  · -- `x z ∉ Q₀` because `x ∉ Q₀` and `z ∈ Q₀`.
    intro hcon
    exact hx0 (by
      have h : (x * z) * z⁻¹ ∈ fr.Q0 := fr.Q0.mul_mem hcon (fr.Q0.inv_mem hzA)
      simpa [mul_assoc] using h)
  · -- `p⁻¹ (x z) p = (c p · x)(c p · z) = x z`.
    intro p hp
    have hxp : p⁻¹ * x * p = (p⁻¹ * x * p * x⁻¹) * x := by group
    have hzp : p⁻¹ * z * p = (p⁻¹ * x * p * x⁻¹) * z := hzact p hp
    have hxc : x * (p⁻¹ * x * p * x⁻¹) = (p⁻¹ * x * p * x⁻¹) * x :=
      (fr.Q0_central _ (hfix p hp) x hx).symm
    have hcp2 : (p⁻¹ * x * p * x⁻¹) * (p⁻¹ * x * p * x⁻¹) = 1 := hsq _ (hfix p hp)
    exact conj_mul_of_coboundary hxp hzp hxc hcp2

end Work.PSU3.StageB
