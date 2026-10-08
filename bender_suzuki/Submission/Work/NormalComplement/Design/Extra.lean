/-
# Area `NormalComplement`: the vocabulary of §3–§5, in a `sorry`-free module

This module re-exports the lead's design vocabulary
(`Submission.Work.NormalComplement._design.Vocab`, namespace `Work.NormalComplement.Design`) and
adds the three notions that lived in the `sorry`-containing design files
`_design/Sec3.lean`, `_design/Sec4.lean`, `_design/Sec5.lean`:

* `NoCentralizedNormal H t` — the hypothesis of §3 Prop. 1 (`C_K(X) = 1` for every
  `1 ≠ X ⊴ V`);
* `piSec4 H t p` — the set `π` of §4 Prop. 1 (primes `r ≠ p` of `|D|` not dividing `|K|`);
* `Mset u t` — the set `M = {x ∈ C_G(ut) | x^t = x⁻¹}` of §5 Prop. 2;
* `Setup5` — the datum of §5 (`Setup45A` plus the conclusions of §4 Prop. 1, 2).

Everything here is a definition or a structure: the file is `sorry`-free, so it may be imported by
the leaves of the §3–§5 decomposition.  Names are exactly those of the design files (same
namespace), so statements copied from `_design/Sec3.lean`, `_design/Sec4.lean`,
`_design/Sec5.lean` elaborate verbatim against this module.
-/
import Submission.Work.NormalComplement._design.Vocab

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option autoImplicit false

open Classical
open scoped Pointwise commutatorElement
open LeanEval.GroupTheory.Defs
open Submission.Blueprint

namespace Work.NormalComplement.Design

/-! ## The commutator subgroup, named so that statements need no notation scope -/

/-- `[A,B] = ⁅A,B⁆`, as a subgroup of `G` (the bracket notation is scoped, so it cannot appear in a
statement pasted into a file with no `open scoped commutatorElement`). -/
def commSub {G : Type*} [Group G] (A B : Subgroup G) : Subgroup G := ⁅A, B⁆

/-! ## §3 Prop. 1: `C_K(X) = 1` for every `1 ≠ X ⊴ V` -/

/-- §3 Prop. 1 hypothesis: `C_K(X) = 1` for every `1 ≠ X ⊴ V`. -/
def NoCentralizedNormal {G : Type*} [Group G] (H : Subgroup G) (t : G) : Prop :=
  ∀ X : Subgroup G, X ≠ ⊥ → X ≤ centD H t → centD H t ≤ Subgroup.normalizer (X : Set G) →
    CK H t X = {1}

/-! ## §4 Prop. 1: the set `π` -/

/-- The set `π` of §4 Prop. 1: primes `r ∣ |D|`, `r ≠ p`, `r ∤ |K|`. -/
def piSec4 {G : Type*} [Group G] (H : Subgroup G) (t : G) (p : ℕ) : ℕ → Prop :=
  fun r => r.Prime ∧ r ∣ Nat.card ↥(twoPoint H t) ∧ r ≠ p ∧
    ¬ r ∣ (Kset (twoPoint H t) t).ncard

/-! ## §5 Prop. 2: the set `M` -/

/-- `M = {x ∈ C_G(ut) | t x t⁻¹ = x⁻¹}`. -/
def Mset {G : Type*} [Group G] (u t : G) : Set G :=
  {x | x ∈ Subgroup.centralizer ({u * t} : Set G) ∧ t * x * t⁻¹ = x⁻¹}

/-! ## §5: the standing datum -/

/-- The data of §5: `Setup45A` plus the conclusions of §4 Prop. 1, 2. -/
structure Setup5 (G : Type) [Group G] [Finite G] (H : Subgroup G) (t : G) (W : Subgroup G)
    (p : ℕ) (P A : Subgroup G) (r : ℕ) : Prop extends Setup45A G H t W p P A where
  P_syl : IsSylowIn p P (twoPoint H t)
  E_eq : Egrp H t W = Ecomm H t W ⊔ P
  E'_inf : Ecomm H t W ⊓ P = ⊥
  E'_eq : Ecomm H t W = Kgrp (twoPoint H t) t ⊔ ⁅A, P⁆
  E'V : Ecomm H t W ⊓ centD H t = ⁅A, P⁆
  E'_nil : Group.IsNilpotent ↥(Ecomm H t W)
  E'_hall : Nat.Coprime (Nat.card ↥(Ecomm H t W)) (Ecomm H t W).index
  E'_primes : ∀ q : ℕ, q.Prime →
    (q ∣ Nat.card ↥(Ecomm H t W) ↔ q ∣ (Kset (twoPoint H t) t).ncard)
  CAP_cop : ∀ q : ℕ, q.Prime → q ∣ Nat.card ↥(A ⊓ Subgroup.centralizer (P : Set G)) →
    ¬ q ∣ (Kset (twoPoint H t) t).ncard
  r_prime : r.Prime
  r_dvd : r ∣ 2 ^ p - 1
  K_card : ∃ a : ℕ, 1 ≤ a ∧ (Kset (twoPoint H t) t).ncard = r ^ a * (2 ^ p - 1)
  fitV : fitSub (centD H t) = Ecomm H t W ⊓ centD H t
  fitV_ne : fitSub (centD H t) ≠ ⊥
  fitV_syl : IsSylowIn r (fitSub (centD H t)) (centD H t)

end Work.NormalComplement.Design
