import Submission.Work.CORE2B.Basic
import Submission.Work.CORE2B.API
import Submission.Work.CORE2B.isPGroup_pCoreIn_two
import Submission.Work.CORE2B.L27_O2_centralized_by_t
import Submission.Work.CORE2B.L27su_U_helpers
import Submission.Work.CORE2B.L27su_two_core_le_pCoreIn_Hhat
import Submission.Work.CORE2B.L27v12_eq_bot_of_le_pCoreIn_Hhat
import Submission.Work.CORE2B.L27_commutator_le_final
import Submission.Work.CORE2B.L27v12_O2_centralizes_fittingU
import Submission.Work.CORE2B.isSolvable_of_commutator_le
import Submission.Work.CORE2B.L27_centralizer_solvable

/-!
# AREA CORE2B — assembly of Bender's Lemma 2.7(a) (the lead's design pass 12)

Bender's Lemma 2.7(a), `[M,t] ⊆ F_{π'}(M)`, in the form of the leaf
`Work.CORE2B.L27_commutator_le` (hypotheses `L27Hyp`, `M ≠ ⊤` — **no** maximality).  This is the
assembly of `_design_gw/Core12L27.lean`: the only input that was missing from the area is
Bender's step (4), `O₂(M) ≤ C_G(F(U))` (leaf N3, `L27v12_O2_centralizes_fittingU`), and
everything else was already sorry-free.

`L27_commutator_le_v12_of_O2` takes leaf N3 as a hypothesis, so that the assembly is available
before N3 is proved; when N3 is proved it is instantiated in `L27_commutator_le_v12` below.
-/

open scoped MatrixGroups

set_option linter.unusedVariables false

namespace Work.CORE2B

open Subgroup

/-- Leaf N3 of the lead's design pass 12, as a hypothesis-friendly `Prop`: `O₂(M) ≤ C_G(F(U))`. -/
def L27v12_O2_centralizes_fittingU' : Prop :=
  ∀ (T : Work.GW2.LocalToolkit) (h23 : Work.GW2.Lemma23Prop) (h26 : Work.GW2.Thm26Prop)
    (G : Type) [Group G] [Finite G], Work.GW2.FeitThompsonProp → Work.GW2.BenderCtx G →
    ∀ (B : Work.GW2.BenderSetup G) (M : Subgroup G), L27Hyp B M →
      Work.GW2.pCoreIn 2 M ≤
        Subgroup.centralizer ((Work.GW2.fittingIn B.U : Subgroup G) : Set G)

/-- **Bender Lemma 2.7(a)** from leaf N3. -/
theorem L27_commutator_le_v12_of_O2 (hN3 : L27v12_O2_centralizes_fittingU') :
    Work.CORE2B.L27_commutator_le := by
  intro T h23 h26 G _ _ hFT hCtx B M hD
  have hPt := L27_O2_centralized_by_t T h23 h26 G hFT hCtx B M hD
  have hPF := hN3 T h23 h26 G hFT hCtx B M hD
  have hcomm := L27su_commutator_eq_bot_of_centralizes_fitting_U T G hFT hCtx B M hD hPt hPF
  have hPU : Work.GW2.pCoreIn 2 M ≤ Subgroup.centralizer (B.U : Set G) :=
    (Subgroup.commutator_eq_bot_iff_le_centralizer).mp hcomm
  have hle := L27su_two_core_le_pCoreIn_Hhat T h26 G hFT hCtx B
    (Work.GW2.pCoreIn 2 M) (isPGroup_pCoreIn_two M) hPU hPt
  exact L27_commutator_le_of_O2_bot T h23 h26 hFT hCtx B M hD
    (L27v12_eq_bot_of_le_pCoreIn_Hhat T h26 G hFT hCtx B M hD hle)

/-- **Bender Lemma 2.7(a), complete**: `[M,t] ⊆ F_{π'}(M)` under `L27Hyp` (no maximality). -/
theorem L27_commutator_le_v12 : Work.CORE2B.L27_commutator_le :=
  L27_commutator_le_v12_of_O2 L27v12_O2_centralizes_fittingU

/-- **Bender Lemma 2.7(c)**: `M` is solvable.  Follows from conclusion (a) together with the
solvability of `H = C(t)` (`L27_centralizer_solvable`). -/
theorem L27_solvable_v12 : Work.CORE2B.L27_solvable := by
  intro T h23 h26 G _ _ hFT hCtx B M hD
  exact isSolvable_of_commutator_le h23 h26 hFT hCtx B M hD
    (L27_commutator_le_v12 T h23 h26 G hFT hCtx B M hD)
    (L27_centralizer_solvable T G hFT hCtx B)

end Work.CORE2B
