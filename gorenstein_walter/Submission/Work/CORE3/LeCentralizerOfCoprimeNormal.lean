import Mathlib
import Submission.Work.CORE3.Defs

set_option linter.dupNamespace false

namespace Work.CORE3

open Subgroup

/-- Two subgroups `A`, `B` which are both normal in a common subgroup `K` and have coprime orders
centralize each other.

Concretely: `A ≤ K` and `B ≤ K` are normalized by `K`, so each of them normalizes the other as
well (`A ≤ K ≤ N_G(B)` and `B ≤ K ≤ N_G(A)`); hence the commutator `⁅A, B⁆` lies in `A ⊓ B`, while
`A ⊓ B = ⊥` because its order divides both `|A|` and `|B|`, which are coprime.  Thus `⁅A, B⁆ = ⊥`,
i.e. every element of `A` commutes with every element of `B`. -/
theorem LeCentralizerOfCoprimeNormal {G : Type} [Group G] {A B K : Subgroup G}
    (hAK : A ≤ K) (hBK : B ≤ K) (hKA : K ≤ Subgroup.normalizer (A : Set G))
    (hKB : K ≤ Subgroup.normalizer (B : Set G)) (hcop : (Nat.card A).Coprime (Nat.card B)) :
    A ≤ Subgroup.centralizer (B : Set G) := by
  -- Commutation is equivalent to vanishing of the commutator subgroup.
  rw [← Subgroup.commutator_eq_bot_iff_le_centralizer]
  refine le_bot_iff.mp ?_
  -- `A` normalizes `B` through `K`, and vice versa.
  have hAB : A ≤ Subgroup.normalizer (B : Set G) := hAK.trans hKB
  have hBA : B ≤ Subgroup.normalizer (A : Set G) := hBK.trans hKA
  -- So `⁅A, B⁆ ≤ B` and `⁅A, B⁆ ≤ A`, i.e. `⁅A, B⁆ ≤ A ⊓ B`.
  have h1 : ⁅A, B⁆ ≤ B := (Subgroup.le_normalizer_iff_commutator_le_right).mp hAB
  have h2 : ⁅A, B⁆ ≤ A := (Subgroup.le_normalizer_iff_commutator_le_left).mp hBA
  -- And `A ⊓ B = ⊥` since `|A ⊓ B|` divides both `|A|`, `|B|`, which are coprime.
  have hinf : A ⊓ B = ⊥ := (Subgroup.disjoint_of_coprime_natCard hcop).eq_bot
  calc ⁅A, B⁆ ≤ A ⊓ B := le_inf h2 h1
    _ = ⊥ := hinf

namespace Work.CORE3

/-- The same statement, exposed under the doubly nested name
`Work.CORE3.Work.CORE3.LeCentralizerOfCoprimeNormal` of the module's original skeleton. -/
theorem LeCentralizerOfCoprimeNormal {G : Type} [Group G] {A B K : Subgroup G}
    (hAK : A ≤ K) (hBK : B ≤ K) (hKA : K ≤ Subgroup.normalizer (A : Set G))
    (hKB : K ≤ Subgroup.normalizer (B : Set G)) (hcop : (Nat.card A).Coprime (Nat.card B)) :
    A ≤ Subgroup.centralizer (B : Set G) :=
  _root_.Work.CORE3.LeCentralizerOfCoprimeNormal hAK hBK hKA hKB hcop

end Work.CORE3

end Work.CORE3
