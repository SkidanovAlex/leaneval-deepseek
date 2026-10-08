/-
# Area `NormalComplement`: the Ch. I/II input (`BenderPrelimProp`)

Chapter III of Peterfalvi's proof of Theorem D sits on Chapter II §4 and, through it, on the
"Bender group calculus" of Chapter I §1–§2.  Of that calculus the area `ThreePoints` exposes the
clauses of `Submission.Blueprint.ChIIFourProp`; what is *not* exposed by any area `Prop`, and what
Chapter III uses at several points, is

> **Ch. I §2 Prop. 2(b).**  `D = H ∩ H^t` acts transitively on the involutions of `H`.

(Used in Ch. III §2 Prop. 1 case 2, §3 Prop. 2, §4 Prop. 2 and §5; also for the counting statement
`|K| = |Inv H|`, which we *derive* from it together with `ChIIFourProp` P2(a) and App. I (1)(a).)

`BenderPrelimProp` records exactly this statement, so that everything downstream of §1 can be
stated and proved while the Bender calculus is being built.  `BenderPrelimProp` is *provable* from
`IsStronglyEmbedded` alone (it is a theorem of Bender's paper); the lemmas that discharge it live in
`Submission/Work/NormalComplement/Prelim/`, and the main theorem of the area takes it as an
explicit hypothesis until they are complete.
-/
import Mathlib
import ChallengeDeps
import Submission.Blueprint.Interfaces
import Submission.Work.NormalComplement.Defs

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

open Classical
open scoped Pointwise commutatorElement
open LeanEval.GroupTheory.Defs
open Submission.Blueprint

namespace Work.NormalComplement

/-- **The Ch. I/II input of Chapter III** (Peterfalvi, Ch. I §2 Prop. 2(b)): in the situation
(B0)–(B2), for a strongly embedded `H` and an involution `t ∉ H`, the two-point stabiliser
`D = H ∩ H^t` acts transitively on the involutions of `H`. -/
def BenderPrelimProp : Prop :=
  ∀ (G : Type) [Group G] [Finite G], Situation G → ∀ H : Subgroup G, IsStronglyEmbedded H →
    ∀ t : G, orderOf t = 2 → t ∉ H →
      ∀ u ∈ involutions (H : Set G), ∀ v ∈ involutions (H : Set G),
        ∃ d ∈ twoPoint H t, d * u * d⁻¹ = v

/-- The involution count `n = |Inv(H)|` is `|K|`: this is the form in which Ch. III uses
Ch. I §2 Prop. 2.  It is *derived* from `BenderPrelimProp` (D-transitivity on `Inv H`),
`ChIIFourProp` P2(a) (`V = C_D(u)` for some `u ∈ Inv H`) and App. I (1)(a)
(`|K| = |D:V|`). -/
def BenderPrelimCountProp : Prop :=
  ∀ (G : Type) [Group G] [Finite G], Situation G → ∀ H : Subgroup G, IsStronglyEmbedded H →
    ∀ t : G, orderOf t = 2 → t ∉ H →
      (Kset (twoPoint H t) t).ncard = (involutions (H : Set G)).ncard

end Work.NormalComplement
