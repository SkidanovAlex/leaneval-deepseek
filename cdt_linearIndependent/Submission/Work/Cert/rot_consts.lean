import Mathlib
import Submission.Work.Cert.Spec
import Submission.Work.Cert.rot_aux
import Submission.Work.Cert.rot1_bound
import Submission.Work.Cert.rot2_bound
import Submission.Work.Cert.rot3_bound
import Submission.Work.Cert.rotW_bound

/-! Guidance from the project lead (the requester):

Context (from the project lead). Theorem A, ANumerics conjunct 2 (rearrangement integral ≤ 11.2) and the
outer winding of φ_A + 1/72 are certified by a LEAD-BUILT integer certificate ("verify, don't compute"):
`Submission/Work/Cert/Defs.lean` (checker `leafOK`, scale `S = 2^40·10^8`, `fdiv = Int.ediv`, `md` = floor
product, `mu` = ceil product, `dvu` = ceil quotient), `WindDefs.lean` (`qChain`, `gDisc`, `windLeafOK`,
`labelsOK`), 15,511 conjunct-2 leaves in `Chunks/C000..C155` (each `okC### : arcsOK … = true` by
`decide +kernel`, linked in `Final.lean`: `link_ok`, `first_ok`, `total_ok`, `vals_length`), 4,553 winding
leaves in `WChunks/W000..W045` (`WindFinal.lean`: `wlink_ok`, `wfirst_ok`, `wj_ok`, `wlabels_ok`), and
`SrCheck.lean` (`sr_all`, `wsr_all`). The contracts are the `Prop`s in `Submission/Work/Cert/Spec.lean`
(read it first). DO NOT build kernel chains / evaluate numerics in the kernel yourself and do not edit
Defs/WindDefs/Spec/chunks: your job is the real-analysis soundness of the integer operations. Reuse
proved lemmas: APsi `slit_facts`/`differentiableOn_slit`/`slit_norm_lt_one`/`lune_norm_bounds`,
ANum3 `slitM2B_sound`, `luneM2B_sound`, `luneM2B_numeric_core`, `norm_deriv_sub_le_of_ball`,
`norm_rot_sub_le`, `hauptH_norm_le_exp`, `hTailC_le`, `sqrtJS_mem`/`slitEnclJS_mem`/`luneEnclJS_mem`
(same ideas, older interval types), `phiA_analytic_ext`, `psiA_facts`, `haupt_facts`. No native_decide.
Rounding facts you will need repeatedly: `Int.ediv` with positive divisor is floor
(`Int.ediv_mul_le`, `Int.lt_ediv_add_one_mul_self`); prove small helper lemmas for md/mu/dvu once.

The constants are `round(S·cos 2πt)`, `round(S·sin 2πt)` (80-digit reference), so each coordinate is within
1/2 ulp; the claimed bound 2/S has lots of room. Route: `Real.pi_gt_d20`/`Real.pi_lt_d20` for π, then a
Taylor bound for `Complex.exp` of `2πi t` (|2πt| ≤ 0.74) with ~24 terms (`Complex.exp_bound` or
`Real.cos_bound`-style with enough terms; `Complex.norm_exp_sub_le_sum…`), evaluated by `norm_num`
on rationals. One helper lemma parametrised by (t, cr, ci, rational interval for π) used five times.
-/

/-!
# `RotConsts`: the five rotation constants of the Theorem-A contour

`RotConsts` (`Submission/Work/Cert/Spec.lean`) is the contract that the five integer rotation
constants of `Defs.lean` (`rot0`, `rot1`, `rot2`, `rot3`, `W`), read at scale `S = 2^40·10^8`,
approximate `rot t = e^{2πit}` to within `2/S` at the five contour angles
`2033/25000, 2927/25000, 453/12500, -1971/25000, 1/4096`.

This file is only the assembly.  The mathematics — squeezing `2πt` between the two rationals
`2·3.14159…846·t` and `2·3.14159…847·t` (`Real.pi_gt_d20`, `Real.pi_lt_d20`) and enclosing
`cos`/`sin` on `[0, π/4]` by the eleven-term Taylor sums `cosP`/`sinP` of `Work.CNum`
(`Work.ANum.rotGlue`) — lives in `Submission/Work/Cert/rot_aux.lean` as the single glue lemma
`rot_bound_aux`, with `rot0_bound` a fully worked instance; the remaining four instances are
`Work.Cert.rot1_bound`, `rot2_bound`, `rot3_bound`, `rotW_bound`.
-/

namespace Work.Cert

theorem rot_consts : RotConsts :=
  ⟨rot0_bound, rot1_bound, rot2_bound, rot3_bound, rotW_bound⟩

end Work.Cert
