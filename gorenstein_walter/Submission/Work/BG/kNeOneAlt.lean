import Mathlib
import Submission.Work.BG.ThmABCDefs
import Submission.Work.BG.Assembly
import Submission.Work.BG.splitglue.Split
import Submission.Work.BG.decompBig
import Submission.Work.BG.kNeOne

namespace Work.BG

open OddOrder.RepresentationTheory Work.GW2 Work.BG Work.GW2.C16 Subgroup

/-! # `Work.BG.kNeOneAlt` — Bender–Glauberman, Remark 3.5 (`K ≠ 1`)

`Work.GW2.C16.KNeOneProp` is the design leaf **G8**: under the hypotheses of Theorem C of
Bender–Glauberman (1981, pp. 200–215) with `G` simple, `K = K₁ ⊓ K₂ ≠ ⊥` (Remark 3.5, p. 210).

The route (BG, p. 210) is the one of design pass 26 (`Submission/Work/_design_gw/Core26.lean`,
namespace `Work.GW2.C26`, **sorry-free**), and avoids the false general lemma
`odd_mem_oddCore_of_sylow_le_centralizer` (refuted by `PSL(2,27):3`):

* if `K = ⊥`, the Frobenius clause forces `U = B`; then `S` centralizes `U`;
* `H = U ⊔ S` (`CentralizerSplitProp`) and `S ≤ N_G(U)`, so `H ≤ N_G(U)`; the fusion step
  `C26.conj_t_of_mem_S` shows every involution of `N_G(U)` is `N_G(U)`-conjugate to `t`
  (`C26.oneClass_normalizer`), because for `x = c t c⁻¹ ∈ S` one has
  `U ≤ C_G(x) = U^c ⊔ S^c` with `U` odd and `S^c` a `2`-group normalizing `U^c`, whence
  `U ≤ U^c` and, by cardinality, `U = U^c`, i.e. `c ∈ N_G(U)`;
* Theorem B applied to the proper subgroup `N_G(U) ⊇ H` with one class of involutions gives
  `|G : N_G(U)| = 5`; a simple group with a subgroup of index `5` has `|G| ∣ 120`, so
  `|U| = 3` is a Sylow `3`-subgroup with `n₃ = 5 ≢ 1 (mod 3)` (`C26.false_of_normalizer_index_five`).

Here Theorem B is instantiated from the proved final assembly of this area: `bgThmB_of` needs
`CentralizerSplitProp` (`Work.BG.SplitGlue.centralizerSplitProp`), the proved Coherence
Theorem 2.3 (`coherenceAll`), DEC-BIG (`decompBig`) and S4-DEC (`s4All`). -/

open OddOrder.RepresentationTheory Work.GW2 Work.BG Work.GW2.C16 in
/-- **G8 / Remark 3.5** (`Work.GW2.C16.KNeOneProp`): with `B' ≠ B` and the Frobenius clause in
force, a simple `G` satisfies `K₁ ⊓ K₂ ≠ ⊥`. -/
theorem kNeOneAlt : Work.GW2.C16.KNeOneProp :=
  Work.BG.kNeOne_of_thmB
    (bgThmB_of coherenceAll
      (fun (G : Type) [Group G] [Finite G] [Fintype G] [Invertible (Nat.card G : ℂ)]
        (D : BGData G) (C : Sec2Ctx G) [Invertible (Nat.card ↥C.P.H0 : ℂ)] =>
        decompBig D C)
      s4All)
    SplitGlue.centralizerSplitProp

end Work.BG
