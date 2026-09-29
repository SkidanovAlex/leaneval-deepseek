import Mathlib
import Submission.Work.Cert.Spec
import Submission.Work.ANum3.Z2.wind_leaf_sound_impl

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

As leaf_sound up to the q disc (share `leafOK_spec`-style unfolding of `qChain`), then `gDisc`: A(q) ∈
D(a, eA), B(q) ∈ D(b, eB) (ThetaEncl), |a| ≤ aU, bL ≤ |b| ≤ bU, |B(q)| ≥ Blo > 0. X = A/B:
|X − a/b| ≤ (eA|b| + |a|eB)/(|b||B|) and (xr, xi) = a/b up to the floor terms bounded by
2·⌊(|xr|+|xi|+2)/b2⌋ + 4 (b2 = ⌊|b|²S⌋ > 0); ETOL absorbs cmr/cmi floors in each `sqD`
((c,r)² ⊂ (c², 2|c|r + r²), |c| ≤ |cr|+|ci|); h = −256 q X^8 (ThetaIdentity), g = h + 1/72 in disc
(gr, gi, rg); then Re(g·conj(I^lab)) ≥ labRe − rg > 0.
-/

namespace Work.Cert

/-- The winding leaf soundness: the assembly is `Work.ANum3.Z2.wind_leaf_sound_impl`, whose proof
uses the `WL` pieces of this development (the named mirrors of `gDisc` in `Submission/Work/Cert/WL/Defs.lean`,
the disc rounding `sqD_sound`, the ratio bounds `WL.ratio_le`/`WL.dvu_ratio`/`WL.ratio_floor` and the
product bounds `WL.prod_disc`/`WL.prod256_sound`). -/
theorem wind_leaf_sound (hR : RotConsts) (hS : SlitStageSound) (hL : LuneStageSound)
    (hT : ThetaEncl) (hI : ThetaIdentity) : WindLeafSound :=
  Work.ANum3.Z2.wind_leaf_sound_impl hR hS hL hT hI

end Work.Cert
