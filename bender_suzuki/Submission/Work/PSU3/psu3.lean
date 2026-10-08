/-
# The area theorem: `Submission.Blueprint.PSU3Prop`

Peterfalvi II, Ch. VI–VII: a finite simple group `G` in the situation (B0)–(B2) with a split
rank-one datum `H = Q ⋊ D`, `V = C_D(t) ≠ 1` (i.e. `G` not Zassenhaus), condition (B3) and
`Q` a 2-group is isomorphic to `PSU(3, 2ⁿ)` for some `n ≥ 2`.

The proof is the assembly of the area:

* `Work.PSU3.StageC.psu3_coords_FT` — Stages A–C: `Q` is coordinatised by the case-c Suzuki
  group `SZ (E n)`, `E n = GF(2^{2n})`, in such a way that Peterfalvi's `f`-relation `FRel`
  becomes the model map `fMapTot` (Ch. VI §1–§3, Ch. VII §1–§4; its inputs are the proved
  `StageA.centD_le_W_of_PSU3Hyp_closed` (`V ≤ W`), `StageB.exists_omega_of_fpf_rebuilt`,
  `StageB.exists_omega_of_not_fpf_FT`, `StageA.W_ne_bot_of_PSU3HypFT`, `StageB.theta_trivial`,
  `StageC.frame_normalize`, `StageC.fine_coords_holds`, `StageC.f_formula` and the H1–H6
  identities);
* `Work.PSU3.psu3DatumProp_holds` — Stage D: the model datum of `PSU3Model n` with coordinates
  `(SZ (E n), fMapTot)` (`Model.weylConj_matFun` for the `f`-relation, `Model.psu3_isSplitRankOne`
  for the split datum, `ModelGL.pglHom_injective` for the coordination);
* `Work.PSU3.psu3Prop_of_coords` — the recognition step, using the delivered
  `Work.RankOneUniqueness.rankOneQUniqueness` and `recognize`.

`FeitThompsonProp` is a hypothesis here, as everywhere in the Bender–Suzuki blueprint
(`Assembly.bender_suzuki_of_areas` supplies it); within the area it is the App. X input that
supplies `K = J(D,t) ⊴ D` (`ThmF.ChV12.Ksub_cyclic_normal`).
-/
import Submission.Work.PSU3.Model.psu3DatumProp
import Submission.Work.PSU3.StageC.psu3_coords_FT

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option autoImplicit false

open LeanEval.GroupTheory.Defs
open Submission.Blueprint

namespace Work.PSU3

/-- **The area theorem `PSU3Prop`**: a finite simple group in situation (B0)–(B2) with a split
rank-one datum, `V ≠ 1`, (B3) and `Q` a 2-group is `PSU(3, 2ⁿ)`, `n ≥ 2`. -/
theorem psu3 (hFT : FeitThompsonProp) (hC4 : ChIIFourProp) (hHig : HigmanProp) : PSU3Prop :=
  psu3Prop_of_coords hC4 hHig
    (fun _ _ _ H Q t hS hC4' hHig' => StageC.psu3_coords_FT hS hC4' hHig' hFT)

end Work.PSU3
