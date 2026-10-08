/-
# Assembly of `Setup5` (Ch. III §4): the intermediate conclusions, named

This module `sorry`-free: it contains only definitions.  It packages the §4 results that turn
`Setup45A` into `Setup5`, step by step, so that the steps can be proved (and delegated)
independently:

* `Step1Conc` — §4 Prop. 1 (1): `C_A(P)` is a Hall subgroup of `N_H(P)` with a normal complement
  there (from formula (∗) `Work.NormalComplement.sec4_prop1_star` + `ControlCorollaryProp`);
* `Step2Conc` — §4 Prop. 1 (2): if `C_A(P) ≠ 1` then `P` is not a `p`-Sylow of `H`;
* `Step3Conc` — §4 Prop. 1 (3): every `r`-Sylow `R` of `C_A(P)` has `|R| ∣ p - 1`;
* `Step4Conc` — §4 Prop. 1 (4): `C_A(P)` is a `π`-group (`π = Design.piSec4 H t p`);
* `Step5Conc` — §4 Prop. 1 (5): `C_A(P)` is Hall in `D = twoPoint H t`.

The source is Peterfalvi I Ch. III §4 Prop. 1 (p.180), transcribed in
`REFS/peterfalvi_I_ch3_4.md`; the packing of §4 into `Setup5` is
`Submission/Work/NormalComplement/Design/Extra.lean`.
-/
import Mathlib
import Submission.Work.NormalComplement.Design.Extra
import Submission.Work.NormalComplement.Sections

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

namespace Work.NormalComplement.S5K

variable {G : Type*} [Group G]

/-- **§4 Prop. 1, step 1.**  `C_A(P) = A ⊓ C_G(P)` is a Hall subgroup of `N_H(P) = H ⊓ N_G(P)`
and has a normal complement in `N_H(P)`. -/
def Step1Conc (H : Subgroup G) (t : G) (p : ℕ) (P A : Subgroup G) : Prop :=
  Nat.Coprime (Nat.card ↥(A ⊓ Subgroup.centralizer (P : Set G)))
      ((A ⊓ Subgroup.centralizer (P : Set G)).relIndex (H ⊓ Subgroup.normalizer (P : Set G))) ∧
    ∃ N : Subgroup G, N ≤ H ⊓ Subgroup.normalizer (P : Set G) ∧
      H ⊓ Subgroup.normalizer (P : Set G) ≤ Subgroup.normalizer (N : Set G) ∧
      N ⊓ (A ⊓ Subgroup.centralizer (P : Set G)) = ⊥ ∧
      N ⊔ (A ⊓ Subgroup.centralizer (P : Set G)) = H ⊓ Subgroup.normalizer (P : Set G)

/-- **§4 Prop. 1, step 2.**  If `C_A(P) ≠ 1`, then `P` is not a `p`-Sylow subgroup of `H`. -/
def Step2Conc (H : Subgroup G) (t : G) (p : ℕ) (P A : Subgroup G) : Prop :=
  (A ⊓ Subgroup.centralizer (P : Set G)) ≠ ⊥ → ¬ IsSylowIn p P H

/-- **§4 Prop. 1, step 3.**  Every Sylow subgroup `R` of `C_A(P)` has order dividing `p - 1`. -/
def Step3Conc (H : Subgroup G) (t : G) (p : ℕ) (P A : Subgroup G) : Prop :=
  ∀ (r : ℕ) (R : Subgroup G), r.Prime →
    IsSylowIn r R (A ⊓ Subgroup.centralizer (P : Set G)) → Nat.card R ∣ p - 1

/-- **§4 Prop. 1, step 4.**  `C_A(P)` is a `π`-group, `π = piSec4 H t p` (the primes `r ≠ p` of
`|D|` with `r ∤ |K|`). -/
def Step4Conc (H : Subgroup G) (t : G) (p : ℕ) (P A : Subgroup G) : Prop :=
  ∀ r : ℕ, r.Prime → r ∣ Nat.card ↥(A ⊓ Subgroup.centralizer (P : Set G)) →
    Design.piSec4 H t p r

/-- **§4 Prop. 1, step 5.**  `C_A(P)` is Hall in `D = twoPoint H t`. -/
def Step5Conc (H : Subgroup G) (t : G) (p : ℕ) (P A : Subgroup G) : Prop :=
  ∀ r : ℕ, Design.piSec4 H t p r →
    ¬ r ∣ (A ⊓ Subgroup.centralizer (P : Set G)).relIndex (twoPoint H t)

end Work.NormalComplement.S5K
