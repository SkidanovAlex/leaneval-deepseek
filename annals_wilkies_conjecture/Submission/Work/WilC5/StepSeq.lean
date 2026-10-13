/-
  WilC5 — **the sequence of vdDMM Lemma 4.4 and its invariant.**

  In the notation of van den Dries–Macintyre–Marker, Lemma 4.4 (the hard step of §4) is proved by
  iterating the following construction.  Starting from `x₀ = x` (an element outside the model `F₀`
  which is closed under exponentiation and such that `v(F₀(y)^×) ≠ v(F₀^×)` for every `y ∉ F₀`),
  one produces `x_{n+1} = εₙ (log xₙ - βₙ)` with `εₙ = ±1` and `βₙ ∈ F₀`, so that
  `log xₙ = βₙ + εₙ x_{n+1}`; then `ℚ v(x₀) + … + ℚ v(x_{n}) + v(F₀^×)` is direct (their Claim 2),
  which makes the value group of `Fₙ = F₀(x₀,…,x_{n-1})` computable and lets one compute the cuts
  (Claim 4) and prove log-closure/log-preservation (Claim 5).

  This module fixes the *data* of such a sequence and the invariant that the construction maintains;
  the mathematical claims about it (the independence of the values, and the decomposition of an
  element of `Fₙ` into `u (1+ε) x₀^{q₀} ⋯ x_{n-1}^{q_{n-1}}`) are stated here so that they can be
  proved independently.
-/
import Mathlib
import Submission.Work.Wilkies.CG.Spec
import Submission.Work.WilC2.Dcl
import Submission.Work.WilC5.S4StepDefs
import Submission.Work.WilC5.Values
import Submission.Work.WilC5.ValuesLemmas
import Submission.Work.WilC4.Defs
import Submission.Work.WilC5.Bridge

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
open Classical
namespace Work.WilC5

open WilkiesDesign WilkiesDesign.CG WilkiesConjecture FirstOrder Language
open scoped FirstOrder

attribute [local instance] Work.WilC5.reductStruct

/-- **The data of the sequence of vdDMM Lemma 4.4.**

`xs n = xₙ`, `beta n = βₙ ∈ B`, `pos n` records the sign `εₙ = ±1` in the form
`pos n = true → εₙ = 1`, `pos n = false → εₙ = -1`.  The relation `log xₙ = βₙ + εₙ x_{n+1}` and the
positivity `0 < xₙ` are part of the data. -/
structure StepSeq {K : Type} [LEc.Structure K] (B : LRc.Substructure K) where
  /-- the sequence `xₙ` -/
  xs : ℕ → K
  /-- the approximations `βₙ ∈ B` -/
  beta : ℕ → ↥B
  /-- the sign `εₙ` -/
  pos : ℕ → Bool
  /-- `0 < xₙ` -/
  hpos : ∀ n, Work.WilC5.leE Work.WilC5.zeroE (xs n) ∧
    ¬ Work.WilC5.leE (xs n) Work.WilC5.zeroE
  /-- `log xₙ = βₙ + εₙ x_{n+1}` -/
  hrel : ∀ n, Work.WilC5.logFun (xs n) =
    (if pos n then Work.WilC5.addE (beta n : K) (xs (n + 1))
     else Work.WilC5.subE (beta n : K) (xs (n + 1)))

namespace StepSeq

variable {K : Type} [LEc.Structure K] {B : LRc.Substructure K}

/-- **The value-new invariant**: each `xₙ` has a value that no element of `B` has.  Stated with the
ambient instances so that the definition does not depend on the canonical-instance bundle. -/
def ValueNewAll [Field K] [LinearOrder K] (S : StepSeq B) : Prop :=
  ∀ n, ∀ b : ↥B, ¬ SameArch (b : K) (S.xs n)

/-- **The unboundedness invariant**: each `xₙ` dominates every real constant (equivalently, since
`xₙ > 0`, each `xₙ` is infinite). -/
def Unbounded (S : StepSeq B) : Prop :=
  ∀ n, ∀ N : ℕ, Work.WilC5.leE (Work.WilC5.realConst K (N : ℝ)) (S.xs n) ∧
    ¬ Work.WilC5.leE (S.xs n) (Work.WilC5.realConst K (N : ℝ))

/-- **The logarithm is dominated by the identity** at the sequence: `v(log xₙ) > v(xₙ)`. -/
def LogDominated [Field K] [LinearOrder K] (S : StepSeq B) : Prop :=
  ∀ n, VLe (S.xs n) (Work.WilC5.logFun (S.xs n)) ∧
    ¬ VLe (Work.WilC5.logFun (S.xs n)) (S.xs n)

/-! The two mathematical claims about a sequence of this shape — vdDMM's Claim 2 (the values
`v(x₀), …, v(x_{n-1})` are independent modulo `v(B^×)`) and the decomposition
`w^N = u (1+ε) ∏ xᵢ^{pᵢ}` of an element of `Dcl (B ∪ {x₀,…,x_{n-1}})` — are proved in the companion
modules `Submission.Work.WilC5.StepSeqClaims.valIndep` and
`Submission.Work.WilC5.StepSeqClaims.decomposition`. -/

end StepSeq

end Work.WilC5
