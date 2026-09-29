import Mathlib
import Submission.Work.Cert.LeafAux
import Submission.Work.Cert.LeafChain
import Submission.Work.Cert.leaf_st0_mem
import Submission.Work.Cert.P2Z_lower
import Submission.Work.Cert.theta_bounds
import Submission.Work.Cert.leaf_haupt_bound
import Submission.Work.Cert.q_disc_mem

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

Unfold `leafOK L = true` into its conjuncts (write one lemma `leafOK_spec` that exposes st0..st5, the q
disc, Aup/Blo, P2 exactly as in Defs; `qChain` in WindDefs is the same chain — prove
`leafOK L = true → (qChain L).ok = true` and reuse it in wind_leaf_sound). Then for z in the leaf disc:
st0 contains (491/500)z (md K491 rounding ≤ 1 ulp, radius mu rz K491 + 2), apply SlitStageSound four times
with the constants s{j}A… (exact: s0A = S·(19/10)² etc. — check by norm_num) and RotConsts, LuneStageSound
for v = lune(36/5, −w₄), q = psiA z = −(4/5)v within (qr, qi, rq). ThetaEncl gives |A(q)| ≤ Aup,
|B(q)| ≥ Blo > 0; ThetaIdentity gives |h(q)| = 256|q||A|^8/|B|^8, so S·|h|² ≤ P2 ≤ expLo(2G) ≤ S e^{2G/S}.
-/

set_option maxRecDepth 100000

namespace Work.Cert
open Complex Submission.CDTPlan

/-- the last numeric step: `S·‖h(q)‖² ≤ P2 ≤ expLo (2G) ≤ S·e^{2G/S}` gives `‖φ_A‖ ≤ e^{G/S}`. -/
theorem leaf_final (hE : ExpLoSound) {L : Leaf} {z : ℂ} {Aup Blo : ℤ}
    (hhab : (S : ℝ) * ‖Submission.CDTPlan.hauptH (psiA z)‖ ^ 2
      ≤ 65536 * (mZ L : ℝ) ^ 2 * (Aup : ℝ) ^ 16 / ((Blo : ℝ) ^ 16 * (S : ℝ)))
    (hP2l : 65536 * (mZ L : ℝ) ^ 2 * (Aup : ℝ) ^ 16 / ((Blo : ℝ) ^ 16 * (S : ℝ))
      ≤ ((P2Z Aup Blo (mZ L) : ℤ) : ℝ))
    (hP2 : P2Z Aup Blo (mZ L) ≤ expLo (2 * L.G)) :
    ‖phiA z‖ ≤ Real.exp ((L.G : ℝ) / (S : ℝ)) := by
  have h3 : ((P2Z Aup Blo (mZ L) : ℤ) : ℝ) ≤ ((expLo (2 * L.G) : ℤ) : ℝ) := by
    exact_mod_cast hP2
  have h4 : ((expLo (2 * L.G) : ℤ) : ℝ)
      ≤ (S : ℝ) * Real.exp (((L.G : ℝ) / (S : ℝ)) + ((L.G : ℝ) / (S : ℝ))) := by
    have h := hE (2 * L.G)
    have hcast : (((2 * L.G : ℤ)) : ℝ) = 2 * (L.G : ℝ) := by push_cast; ring
    have harg : (((2 * L.G : ℤ)) : ℝ) / (S : ℝ)
        = (L.G : ℝ) / (S : ℝ) + (L.G : ℝ) / (S : ℝ) := by
      rw [hcast]; ring
    rwa [harg] at h
  have h5 : (S : ℝ) * ‖Submission.CDTPlan.hauptH (psiA z)‖ ^ 2
      ≤ (S : ℝ) * Real.exp (((L.G : ℝ) / (S : ℝ)) + ((L.G : ℝ) / (S : ℝ))) :=
    le_trans hhab (le_trans hP2l (le_trans h3 h4))
  have h6 : ‖Submission.CDTPlan.hauptH (psiA z)‖ ^ 2
      ≤ (Real.exp ((L.G : ℝ) / (S : ℝ))) ^ 2 := by
    have h7 := (mul_le_mul_iff_of_pos_left S_posR).mp h5
    rw [Real.exp_add] at h7
    calc ‖Submission.CDTPlan.hauptH (psiA z)‖ ^ 2
        ≤ Real.exp ((L.G : ℝ) / (S : ℝ)) * Real.exp ((L.G : ℝ) / (S : ℝ)) := h7
      _ = (Real.exp ((L.G : ℝ) / (S : ℝ))) ^ 2 := by ring
  have hEpos : (0 : ℝ) < Real.exp ((L.G : ℝ) / (S : ℝ)) := Real.exp_pos _
  have h8 : ‖Submission.CDTPlan.hauptH (psiA z)‖ ≤ Real.exp ((L.G : ℝ) / (S : ℝ)) := by
    have hpos : 0 < ‖Submission.CDTPlan.hauptH (psiA z)‖ + Real.exp ((L.G : ℝ) / (S : ℝ)) := by
      have := norm_nonneg (Submission.CDTPlan.hauptH (psiA z))
      linarith
    have hfac : (‖Submission.CDTPlan.hauptH (psiA z)‖ - Real.exp ((L.G : ℝ) / (S : ℝ)))
        * (‖Submission.CDTPlan.hauptH (psiA z)‖ + Real.exp ((L.G : ℝ) / (S : ℝ))) ≤ 0 := by
      nlinarith [h6]
    nlinarith [hpos, mul_nonpos_iff.mp hfac]
  simpa [phiA] using h8

theorem leaf_sound (hR : RotConsts) (hE : ExpLoSound) (hS : SlitStageSound) (hL : LuneStageSound)
    (hT : ThetaEncl) (hI : ThetaIdentity) : LeafSound := by
  intro L hOK z hz
  obtain ⟨hst5, hmU, hokq, hokm, haU, hA, hbL, hB, hBlo, hmdBlo, hP2⟩ := leafOK_spec L hOK
  -- the ψ_A stage chain
  have hqmem0 : ‖lune (36 / 5) (-(slitsA z)) - cx (stage5 L).cr (stage5 L).ci‖
      ≤ ((stage5 L).rho : ℝ) / (S : ℝ) :=
    stage_chain hR hS hL L hst5 z (leaf_st0_mem L z hz)
  have hqmem : ‖psiA z - cx (qrZ L) (qiZ L)‖ ≤ ((rqZ L : ℤ) : ℝ) / (S : ℝ) := by
    have := q_disc_mem L (lune (36 / 5) (-(slitsA z))) hqmem0
    simpa [psiA] using this
  have hqnb := q_norm_le L z hqmem hmU hokq
  have hq1 := q_norm_lt_one L z hqnb.2 hokm
  -- the θ-enclosures
  have hA' : (Acell (qrZ L) (qiZ L) (rqZ L) (mZ L)).Ar ^ 2
      + (Acell (qrZ L) (qiZ L) (rqZ L) (mZ L)).Ai ^ 2 ≤ L.aU ^ 2 := by
    simpa only [pow_two] using hA
  have hB' : L.bL ^ 2 ≤ (Bcell (qrZ L) (qiZ L) (rqZ L) (mZ L)).Br ^ 2
      + (Bcell (qrZ L) (qiZ L) (rqZ L) (mZ L)).Bi ^ 2 := by
    simpa only [pow_two] using hB
  have hth := theta_bounds hT (qrZ L) (qiZ L) (rqZ L) L.mU (mZ L) L.aU L.bL rfl hmU hokq hqnb.1
    hokm haU hA' hbL hB' (psiA z) hqmem
  have hhab := leaf_haupt_bound hI hBlo (psiA z) hq1 hth.1 hth.2 hqnb.2
  have hP2l := P2Z_lower (AupZ (qrZ L) (qiZ L) (rqZ L) (mZ L) L.aU)
    (BloZ (qrZ L) (qiZ L) (rqZ L) (mZ L) L.bL) (mZ L) hBlo hmdBlo
  exact leaf_final hE hhab hP2l hP2

end Work.Cert
