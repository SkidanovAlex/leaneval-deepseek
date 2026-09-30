import Mathlib
import Submission.Work.BMF.vkford_defs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BMF

/-!
# The incomplete Vinogradov count with `h = 1` is dominated by the complete one

For `h = 1` the incomplete system `Jincom s k 1 B` imposes exactly the same equations as the
complete system `J s k X` of the Vinogradov mean value theorem (`vJ s k X`), namely equality of
all power sums of degrees `1 ≤ j ≤ k` (the degree `0` equation is automatic, both sides being
`s`).  Hence, for `B ⊆ [1,P]`, every solution pair with entries in `B` is in particular a
solution pair with entries in `[1,P]`, and the count can only decrease:

  `Jincom s k 1 B ≤ vJ s k P`.

This is the `h = 1`, unit-coefficient case of Ford's trivial bound
`Jincom s k h B ≤ s^{h-1} P^{h(h-1)/2} J_{s,k}(P)` for the incomplete system (Ford,
*Vinogradov's integral and bounds for the Riemann zeta function*, (1.9)).

The proof is the honest injection: a pair of `s`-tuples with entries in `B` is sent to the same
pair of `s`-tuples regarded as having entries in `Finset.Icc 1 P` (using `B ⊆ Finset.Icc 1 P`),
so the solution sets are in bijection with a subset of the complete solution set.
-/

/-- Regard an `s`-tuple with entries in `B` as an `s`-tuple with entries in `Finset.Icc 1 P`,
using `hB : B ⊆ Finset.Icc 1 P`. -/
private def pushTuple {s P : ℕ} {B : Finset ℕ} (hB : B ⊆ Finset.Icc 1 P)
    (x : Fin s → B) : Fin s → Finset.Icc 1 P :=
  fun i => ⟨(x i : ℕ), hB (x i).2⟩

private lemma pushTuple_apply {s P : ℕ} {B : Finset ℕ} (hB : B ⊆ Finset.Icc 1 P)
    (x : Fin s → B) (i : Fin s) : ((pushTuple hB x i : Finset.Icc 1 P) : ℕ) = (x i : ℕ) := rfl

theorem Jincom_one_le_vJ (s k P : ℕ) (B : Finset ℕ) (hB : B ⊆ Finset.Icc 1 P) :
    Work.BMF.Jincom s k 1 B ≤ Work.BMF.vJ s k P := by
  -- Work with the underlying `ℕ`-valued cardinalities.
  have key : (Finset.univ.filter (fun xy : (Fin s → B) × (Fin s → B) =>
        ∀ j : ℕ, 1 ≤ j → j ≤ k → (∑ i, (xy.1 i : ℕ) ^ j) = (∑ i, (xy.2 i : ℕ) ^ j))).card
      ≤ Finset.card ({(x, y) : (Fin s → Finset.Icc 1 P) × (Fin s → Finset.Icc 1 P) |
          ∀ j ≤ k, ∑ i, (x i).1 ^ j = ∑ i, (y i).1 ^ j}) := by
    apply Finset.card_le_card_of_injOn
      (fun xy : (Fin s → B) × (Fin s → B) => (pushTuple hB xy.1, pushTuple hB xy.2))
    · -- the image lands in the complete solution set
      intro xy hxy
      simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hxy ⊢
      intro j hj
      rcases Nat.eq_zero_or_pos j with h0 | hpos
      · -- degree `0`: both power sums equal `s`
        subst h0
        simp
      · -- degrees `1 ≤ j ≤ k`: the defining equations of the incomplete system
        simpa only [pushTuple_apply] using hxy j hpos hj
    · -- the map is injective
      intro a _ b _ hab
      have h1 := congrArg Prod.fst hab
      have h2 := congrArg Prod.snd hab
      refine Prod.ext (funext fun i => ?_) (funext fun i => ?_)
      · exact Subtype.ext (Subtype.mk_eq_mk.mp (congrFun h1 i))
      · exact Subtype.ext (Subtype.mk_eq_mk.mp (congrFun h2 i))
  simpa [Jincom, vJ, LeanEval.NumberTheory.VinogradovMeanValue.J] using key

end Work.BMF
