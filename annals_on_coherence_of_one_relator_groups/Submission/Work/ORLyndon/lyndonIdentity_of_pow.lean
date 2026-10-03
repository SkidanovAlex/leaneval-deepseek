import Submission.Work.ORLyndon.lyndon_independence_of_pow
import Submission.Work.ORLyndon.LyndonCombinatorics
import Submission.Work.ORLyndon.lyndon_fourTerm_exact
import Submission.Work.ORLyndon.magnusTwoTerm_of_lyndon

/-!
# Unconditional Lyndon identity, exactness and `gl.dim K[G] ≤ 2` for one-relator groups

`Work.ORLyndon.lyndon_independence_of_pow` (proved via the Cohen--Lyndon route of
`Submission/Work/ORLyndon/CLDirect`, see `CASE2INPUT_LEAD.md`) is the last missing input of the
chapter: combined with `Work.ORLyndon.lyndonIdentity_of_independence` it gives Lyndon's identity
theorem `LyndonIdentity K X r u l` for `r = u^l`, `u` not a proper power, `r ≠ 1`, and then the
node's three headline results become unconditional:

* `Work.ORLyndon.lyndonIdentity_of_pow` (Lyndon's identity theorem = exactness of the resolution);
* `Work.ORLyndon.lyndon_fourTerm_exact_of_pow` (the four-term sequence
  `0 → K[G]/K[G](u-1) → K[G]^X → K[G] → K → 0` is exact);
* `Work.ORLyndon.magnusTwoTerm_of_pow` (the two-term form of JL Claim 5.10);
* `Work.ORLyndon.globalDim_le_two_of_pow` (`Work.ORCoherence.globalDim (K[G]) ≤ 2` for
  `[CharZero K]`).

These are the conditional-free forms of `Work.ORLyndon.lyndon_fourTerm_exact`,
`Work.ORLyndon.magnusTwoTerm_of_lyndon`, `Work.ORLyndon.globalDim_le_two_of_independence` and
`Work.ORLyndon.globalDim_le_two_of_lyndon` (each of which takes `LyndonIdentity` as a hypothesis).
-/

set_option autoImplicit false

namespace Work.ORLyndon

open MonoidAlgebra

universe u v

variable {X : Type u} [DecidableEq X] {K : Type v} [Field K]

/-- `Work.ORLyndon.IsNotProperPower` and the negation of `Work.OROneRel.IsProperPower` agree. -/
theorem isNotProperPower_of_not {u : FreeGroup X}
    (h : ¬ Work.OROneRel.IsProperPower u) : IsNotProperPower u := by
  intro v k hk huv
  exact h ⟨v, k, hk, huv⟩

/-- **Lyndon's identity theorem**, unconditionally, for `r = u ^ l` with `u` not a proper power. -/
theorem lyndonIdentity_of_pow (r u : FreeGroup X) (l : ℕ) (hpos : 1 ≤ l) (hpow : r = u ^ l)
    (hpp : ¬ Work.OROneRel.IsProperPower u) (hr : r ≠ 1) : LyndonIdentity K X r u l :=
  lyndonIdentity_of_independence (by omega) hpow (isNotProperPower_of_not hpp) hr
    (lyndon_independence_of_pow r u l hpos hpow hpp)

/-- **Exactness of the Lyndon four-term sequence**, unconditionally, for `r = u ^ l` with `u` not a
proper power and `r ≠ 1`. -/
theorem lyndon_fourTerm_exact_of_pow (r u : FreeGroup X) (l : ℕ) (hpos : 1 ≤ l) (hpow : r = u ^ l)
    (hpp : ¬ Work.OROneRel.IsProperPower u) (hr : r ≠ 1) :
    Function.Injective (relationModuleMap K r u l (lyndonIdentity_of_pow r u l hpos hpow hpp hr)) ∧
      LinearMap.range (relationModuleMap K r u l (lyndonIdentity_of_pow r u l hpos hpow hpp hr)) =
        LinearMap.ker (lyndonDelta (K := K) r) ∧
      LinearMap.range (lyndonDelta (K := K) r) = augIdeal K (OneRelatorGroup r) ∧
      RingHom.ker (augmentation K (OneRelatorGroup r) :
        MonoidAlgebra K (OneRelatorGroup r) →+* K) = augIdeal K (OneRelatorGroup r) ∧
      Function.Surjective (augmentation K (OneRelatorGroup r)) :=
  lyndon_fourTerm_exact (lyndonIdentity_of_pow r u l hpos hpow hpp hr)

/-- **The two-term form of JL Claim 5.10**, unconditionally, for `r = u ^ l` with `u` not a proper
power (and the Magnus setup `(Y, t)` and the Freiheitssatz hypotheses on `r`). -/
noncomputable def magnusTwoTerm_of_pow (Y : Finset X) (t : X) (ht : t ∉ Y)
    (hY : ∀ x : X, x ∉ Y → x = t) {r u : FreeGroup X} {l : ℕ}
    (hcr : Work.OROneRel.IsCyclicallyReducedRelator r)
    (hnotmem : r ∉ Subgroup.closure (FreeGroup.of '' (Y : Set X)))
    (hpos : 1 ≤ l) (hpow : r = u ^ l) (hpp : ¬ Work.OROneRel.IsProperPower u) (hr : r ≠ 1) :
    Work.ORLyndon.MagnusTwoTermExact K (Subgroup.closure (PresentedGroup.of '' (Y : Set X)))
      (presentRho r u) l ((presentAlg K r) (foxD (K := K) t u)) :=
  magnusTwoTerm_of_lyndon Y t ht hY hcr hnotmem (lyndonIdentity_of_pow r u l hpos hpow hpp hr)

/-- **`globalDim (K[G]) ≤ 2` for a one-relator group `G = ⟨X | r⟩`**, unconditionally, for
`K` of characteristic zero. -/
theorem globalDim_le_two_of_pow [CharZero K] (r u : FreeGroup X) (l : ℕ) (hpos : 1 ≤ l)
    (hpow : r = u ^ l) (hpp : ¬ Work.OROneRel.IsProperPower u) (hr : r ≠ 1) :
    Work.ORCoherence.globalDim (MonoidAlgebra K (OneRelatorGroup r)) ≤ (2 : WithBot ℕ∞) :=
  globalDim_le_two_of_independence (by omega) hpow (isNotProperPower_of_not hpp) hr
    (lyndon_independence_of_pow r u l hpos hpow hpp)

end Work.ORLyndon
