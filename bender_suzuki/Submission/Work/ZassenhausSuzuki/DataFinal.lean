import Submission.Work.ZassenhausSuzuki.suzukiDataProp0
import Submission.Work.ZassenhausSuzuki.suzuki_lemma6
import Submission.Work.ZassenhausSuzuki.twoPoint_cyclic_cyclic
import Submission.Work.ZassenhausSuzuki.Q_suzuki_sq

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `SuzukiDataProp0` from `HigmanProp` alone

`suzukiDataProp0` (`suzukiDataProp0.lean`) builds the structure half of the Suzuki core from
`HigmanProp`, Suzuki's Lemma 6, L2 (cyclicity of `D`) and L3 (`Q` is a Suzuki 2-group with
`|Q| = |Z(Q)|²`).  All three extra inputs are now theorems of this area:

* `suzuki_lemma6 : SuzukiLemma6Prop` (`suzuki_lemma6.lean`);
* `twoPoint_cyclic_cyclic` (L2, `twoPoint_cyclic_cyclic.lean`);
* `Q_suzuki_sq` (L3, `Q_suzuki_sq.lean`),

so `SuzukiDataProp0` is proved modulo `HigmanProp` alone (`suzukiDataProp0_uncond`).  For a
caller that already has L3 in the form of the socket, `suzukiDataProp0_of_L3` is the same
statement with `hL3` as an explicit input.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

open LeanEval.GroupTheory.Defs
open Submission.Blueprint

namespace Work.ZassenhausSuzuki

/-- **L3 is a theorem** (`Q_suzuki_sq`), in the socket shape used by `suzukiDataProp0`. -/
theorem Q_suzuki_sq' : ∀ (G : Type) [Group G] [Finite G], IsSimpleGroup G →
    ∀ (H Q : Subgroup G) (t : G), IsSplitRankOne H Q t → IsZassenhaus H →
      IsPGroup 2 Q → ¬ IsAbelianSubgroup Q →
      IsSuzukiTwoGroup ↥Q ∧ Nat.card ↥Q = Nat.card ↥(Subgroup.center ↥Q) ^ 2 :=
  fun _ _ _ hs H Q t h hZ h2 hnab => Q_suzuki_sq hs H Q t h hZ h2 hnab

/-- **`SuzukiDataProp0` from `HigmanProp` and L3.** -/
theorem suzukiDataProp0_of_L3 (hHig : HigmanProp)
    (hL3 : ∀ (G : Type) [Group G] [Finite G], IsSimpleGroup G → ∀ (H Q : Subgroup G) (t : G),
      IsSplitRankOne H Q t → IsZassenhaus H →
      IsPGroup 2 Q → ¬ IsAbelianSubgroup Q →
      IsSuzukiTwoGroup ↥Q ∧ Nat.card ↥Q = Nat.card ↥(Subgroup.center ↥Q) ^ 2) :
    SuzukiDataProp0 :=
  suzukiDataProp0 hHig suzuki_lemma6 hL3
    (fun _ _ _ _ _ _ hsplit hz h2 hHig' hSuz => twoPoint_cyclic_cyclic hsplit hz h2 hHig' hSuz)

/-- **`SuzukiDataProp0` (the structure half) is proved modulo `HigmanProp` alone.** -/
theorem suzukiDataProp0_uncond (hHig : HigmanProp) : SuzukiDataProp0 :=
  suzukiDataProp0_of_L3 hHig Q_suzuki_sq'

end Work.ZassenhausSuzuki
