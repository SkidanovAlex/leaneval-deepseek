import Mathlib
import Submission.Work.CORE3.Defs
import Submission.Work.CORE3.SixInvSetElements
import Submission.Work.CORE3.SixInvSetMulTable
import Submission.Work.CORE3.CosetInvCountLeSix
import Submission.Work.CORE3.CosetInvCountNeFive
import Submission.Work.CORE3.InvSetVUSingleton
import Submission.Work.CORE3.CosetInvCountBasic
import Submission.Work.CORE3.Case1bDStructure
import Submission.Work.CORE3.RelIndexHHhat
import Submission.Work.CORE3.NormalizerPcoreEqHhat
import Submission.Work.CORE3.Case1bLeFourSplit
import Submission.Work.CORE3.Case1bLeFourV1
import Submission.Work.CORE3.Case1bLeFourM6
import Submission.Work.CORE3.Case1bLeFourNotLeD
import Submission.Work.CORE3.Case1bLeFourNeSix

/-!
# `Work.CORE3.Case1bSevenLeFour`

Bender 1981 §3, items (5)–(7) of *Finite groups with dihedral Sylow 2-subgroups*
(J. Algebra 70, pp. 223–224), subcase `V = O₂(Ĥ)` of type `(2,2)` with `|U| = |O(Ĥ)| = 3`:
every coset of `Ĥ` containing an involution `y ∉ Ĥ` contains at most four involutions.

## The argument

Write `n := cosetInvCount Ĥ y`.  Bender's (5) (`Work.CORE3.InvSetVUSingleton`) says that no
involution outside `Ĥ` inverts a nontrivial element of `VU = O₂(Ĥ) ⊔ O(Ĥ)`; hence
`I_Ĥ(y) → Ĥ/VU` is injective and

* `n ≤ 6` — `Work.CORE3.cosetInvCount_le_six` (`|Ĥ : VU| = 6`);
* `n ≠ 5` — `Work.CORE3.CosetInvCountNeFive`;
* `n ≠ 6` — `Work.CORE3.Case1bLeFourNeSix` (Bender's (6)/(7) for this configuration: the
  elementary exclusion of a coset carrying six involutions).

Therefore `n ≤ 4`.

## Supporting pieces of the `n = 6` analysis (all proved, axiom-clean)

`Case1bLeFourNeSix` itself is proved by the elementary argument ("`n = 6` is absurd") that was
isolated while proving `Case1bLeFourNotLeD`.  The companion pieces record independently
referenced facts of the same configuration (`D := Ĥ ⊓ Ĥ^y`, `M := D ⊓ VU`, `I := invSetIn Ĥ y`):

* `Case1bDStructure`: `D ⊔ VU = Ĥ`, `|D : M| = 6`, `I ⊆ D` (uses `4 ≤ n`);
* `SixInvSetElements`, `SixInvSetMulTable`: `a, b₁, b₂ ∈ I` of orders `3, 2, 2`, `b₁ ≠ b₂`,
  `b₁ * a * b₁ = a⁻¹`, `(b₁ * b₂)³ = 1`;
* `Case1bLeFourSplit`: `b₁b₂ = h·v` with `h ∈ {a, a²}`, `v ∈ M`, and `v ≠ 1 → v ∈ U ∧ h v = v h`
  (so `U = ⟨v⟩ ≤ M`), via the transversal property of `I` over `M`;
* `Case1bLeFourV1`: `b₁b₂ ∈ {a, a²}` is impossible (conjugating by `y` forces `a = a⁻¹` or
  `a² = a⁻²`, so `orderOf a ∣ 2` or `∣ 4`);
* `Case1bLeFourM6`: `|M| ≠ 6`;
* `Case1bLeFourNotLeD`: `¬(U ≤ D)`, i.e. the case `M = U` of the analysis.

The residual case analysis (`|M| ∈ {3, 6, 12}`, with `|M| = 12` excluded by `D = Ĥ` and
`N_G(Ĥ) = Ĥ`) that these pieces support was worked out but is not needed for the final proof:
`Case1bLeFourNeSix` excludes `n = 6` outright.
-/

namespace Work.CORE3

theorem Case1bSevenLeFour (G : Type) [Group G] [Finite G] (I : Work.CORE3.Case1Inputs)
    (hBc : Work.GW2.BenderCtx G) (B : Work.GW2.BenderSetup G) (h1 : Work.GW2.Case1 B)
    (D : Work.GW2.Case1bData B) (hU3 : Nat.card B.U = 3) :
    ∀ y : G, orderOf y = 2 → y ∉ B.Hhat → Work.GW2.cosetInvCount B.Hhat y ≤ 4 := by
  intro y hy2 hyH
  have h5 := InvSetVUSingleton G I hBc B h1 D
  have hle6 := cosetInvCount_le_six G I hBc B h1 D h5 y hy2 hyH
  have hne5 := CosetInvCountNeFive G I hBc B h1 D h5 y hy2 hyH
  have hne6 := Case1bLeFourNeSix G I hBc B h1 D hU3 hy2 hyH
  omega

end Work.CORE3
