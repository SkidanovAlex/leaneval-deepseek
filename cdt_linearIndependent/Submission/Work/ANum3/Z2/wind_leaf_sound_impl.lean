import Mathlib
import Submission.Work.Cert.WLDefs
import Submission.Work.Cert.WL.prod256
import Submission.Work.Cert.WL.ratio_le
import Submission.Work.Cert.WL.dvu_ratio
import Submission.Work.Cert.leaf_sound
import Submission.Work.ANum3.Z2.ratio_floor
import Submission.Work.ANum3.Z2.halfplane

/-!
# `WindLeafSound` from the four arc-certificate contracts

The winding leaf test `Work.Cert.windLeafOK lab L bU` asserts that the value disc `gDisc L bU` of
`g = h(ψ_A z) + 1/72` over the leaf disc lies in the open half plane of the label `I^lab`.  This file
proves the soundness `WindLeafSound` from the contracts `RotConsts`, `SlitStageSound`,
`LuneStageSound` (`ψ_A` maps the leaf disc into the `q`-disc `qChain`), `ThetaEncl` (the truncated
θ-sums enclose `A(q)`, `B(q)`) and `ThetaIdentity` (`h(q)·θ₄(q)^8 = -256·q·A(q)^8`).

The long integer checkers are handled by *unfolding in the hypothesis or the goal only*, never by
comparing two projections of the symbolic stage chain (`rfl` on those is exponential).
-/

set_option maxRecDepth 100000
set_option maxHeartbeats 800000

namespace Work.ANum3.Z2
open Work.Cert Complex Submission.CDTPlan

/-! ## Identifications of `qChain` with the leaf stage chain (cheap, structure level) -/

theorem stage5_chain (L : Leaf) :
    stage5 L = luneStage (slitStage s3A s3B2 s3E s3C1 s3G8 s3A2 rot3r rot3i
      (slitStage s2A s2B2 s2E s2C1 s2G8 s2A2 rot2r rot2i
        (slitStage s1A s1B2 s1E s1C1 s1G8 s1A2 rot1r rot1i
          (slitStage s0A s0B2 s0E s0C1 s0G8 s0A2 rot0r rot0i (stage0 L) L.w0) L.w1) L.w2) L.w3) L.wl := rfl

theorem qChain_eq (L : Leaf) :
    qChain L = ⟨(stage5 L).ok, -(md K45 (stage5 L).cr), -(md K45 (stage5 L).ci),
      mu (stage5 L).rho K45 + 2⟩ := by
  unfold qChain
  simp only [stage5_chain, stage0, geomOK, leafCx, leafCy, leafRz]

theorem qChain_cr_eq (L : Leaf) : (qChain L).cr = qrZ L := by rw [qChain_eq L]; rfl
theorem qChain_ci_eq (L : Leaf) : (qChain L).ci = qiZ L := by rw [qChain_eq L]; rfl
theorem qChain_rho_eq (L : Leaf) : (qChain L).rho = rqZ L := by rw [qChain_eq L]; rfl
theorem qChain_ok_eq (L : Leaf) : (qChain L).ok = (stage5 L).ok := by rw [qChain_eq L]

/-! ## Names for the pieces of `gDisc` -/

/-- the truncated `A` sum on the leaf's `q`-disc. -/
noncomputable def QA (L : Leaf) : TS :=
  Acell (qChain L).cr (qChain L).ci (qChain L).rho (L.mU + (qChain L).rho + 1)
/-- the truncated `B` sum on the leaf's `q`-disc. -/
noncomputable def QB (L : Leaf) : BS :=
  Bcell (qChain L).cr (qChain L).ci (qChain L).rho (L.mU + (qChain L).rho + 1)
/-- the tail radius of `A` (mantissas at scale `S`). -/
noncomputable def QeA (L : Leaf) : ℤ :=
  (QA L).dA + tailAZ (qChain L).cr (qChain L).ci (qChain L).rho (L.mU + (qChain L).rho + 1)
/-- the tail radius of `B` (mantissas at scale `S`). -/
noncomputable def QeB (L : Leaf) : ℤ :=
  (QB L).dB + tailBZ (qChain L).cr (qChain L).ci (qChain L).rho (L.mU + (qChain L).rho + 1)
/-- `⌊|B_centre|²/S⌋`. -/
noncomputable def Qb2 (L : Leaf) : ℤ :=
  fdiv ((QB L).Br * (QB L).Br + (QB L).Bi * (QB L).Bi) S
/-- real part (mantissa) of the ratio `A/B`. -/
noncomputable def Qxr (L : Leaf) : ℤ :=
  fdiv ((QA L).Ar * (QB L).Br + (QA L).Ai * (QB L).Bi) (Qb2 L)
/-- imaginary part (mantissa) of the ratio `A/B`. -/
noncomputable def Qxi (L : Leaf) : ℤ :=
  fdiv ((QA L).Ai * (QB L).Br - (QA L).Ar * (QB L).Bi) (Qb2 L)
/-- radius (mantissa) of the disc of `X = A/B`. -/
noncomputable def Qrx (L : Leaf) (bU : ℤ) : ℤ :=
  dvu (mu (QeA L) bU + mu L.aU (QeB L)) (md L.bL (L.bL - QeB L))
    + 2 * fdiv (iabs (Qxr L) + iabs (Qxi L) + 2) (Qb2 L) + 4 + ETOL
/-- the disc of `X^8`. -/
noncomputable def Qy (L : Leaf) (bU : ℤ) : ℤ × ℤ × ℤ :=
  sqD (sqD (sqD (Qxr L, Qxi L, Qrx L bU)))
/-- the cross terms of the radius of the disc of `q·X^8`. -/
noncomputable def Qdd (L : Leaf) (bU : ℤ) : ℤ :=
  mu (iabs (qChain L).cr + iabs (qChain L).ci) (Qy L bU).2.2
    + mu (iabs (Qy L bU).1 + iabs (Qy L bU).2.1) (qChain L).rho
    + mu (qChain L).rho (Qy L bU).2.2
/-- real part of the centre of the disc of `q·X^8`. -/
noncomputable def Qpr (L : Leaf) (bU : ℤ) : ℤ :=
  cmr (qChain L).cr (qChain L).ci (Qy L bU).1 (Qy L bU).2.1
/-- imaginary part of the centre of the disc of `q·X^8`. -/
noncomputable def Qpi (L : Leaf) (bU : ℤ) : ℤ :=
  cmi (qChain L).cr (qChain L).ci (Qy L bU).1 (Qy L bU).2.1
/-- real part of the centre of the disc of `g = -256·q·X^8 + 1/72`. -/
noncomputable def Qgr (L : Leaf) (bU : ℤ) : ℤ := -256 * Qpr L bU + fdiv S 72
/-- imaginary part of the centre of the disc of `g`. -/
noncomputable def Qgi (L : Leaf) (bU : ℤ) : ℤ := -256 * Qpi L bU
/-- radius of the disc of `g`. -/
noncomputable def Qrg (L : Leaf) (bU : ℤ) : ℤ := 256 * Qdd L bU + ETOL + ETOL

theorem gDisc_gr_eq (L : Leaf) (bU : ℤ) : (gDisc L bU).2.1 = Qgr L bU := by
  unfold gDisc Qgr Qpr Qy Qxr Qxi Qrx Qb2 QeA QeB QA QB Acell Bcell tailAZ tailBZ
  rfl

theorem gDisc_gi_eq (L : Leaf) (bU : ℤ) : (gDisc L bU).2.2.1 = Qgi L bU := by
  unfold gDisc Qgi Qpi Qy Qxr Qxi Qrx Qb2 QeA QeB QA QB Acell Bcell tailAZ tailBZ
  rfl

theorem gDisc_rg_eq (L : Leaf) (bU : ℤ) : (gDisc L bU).2.2.2 = Qrg L bU := by
  unfold gDisc Qrg Qdd Qy Qxr Qxi Qrx Qb2 QeA QeB QA QB Acell Bcell tailAZ tailBZ
  rfl

/-- the content of `(gDisc L bU).1 = true`: the `q`-disc data and the θ-numerics. -/
theorem gDisc_ok_facts (L : Leaf) (bU : ℤ) (h : (gDisc L bU).1 = true) :
    (qChain L).ok = true ∧ 0 ≤ L.mU ∧
      (qChain L).cr * (qChain L).cr + (qChain L).ci * (qChain L).ci ≤ L.mU * L.mU ∧
      L.mU + (qChain L).rho + 1 ≤ fdiv (79 * S) 100 ∧ 0 ≤ L.aU ∧
      (QA L).Ar * (QA L).Ar + (QA L).Ai * (QA L).Ai ≤ L.aU * L.aU ∧ 0 ≤ L.bL ∧
      L.bL * L.bL ≤ (QB L).Br * (QB L).Br + (QB L).Bi * (QB L).Bi ∧ 0 ≤ bU ∧
      (QB L).Br * (QB L).Br + (QB L).Bi * (QB L).Bi ≤ bU * bU ∧
      0 < L.bL - QeB L ∧ 0 < md L.bL (L.bL - QeB L) ∧ 0 < Qb2 L := by
  have h' : (qChain L).ok = true ∧ 0 ≤ L.mU ∧
      (qChain L).cr * (qChain L).cr + (qChain L).ci * (qChain L).ci ≤ L.mU * L.mU ∧
      L.mU + (qChain L).rho + 1 ≤ fdiv (79 * S) 100 ∧ 0 ≤ L.aU ∧
      (Acell (qChain L).cr (qChain L).ci (qChain L).rho (L.mU + (qChain L).rho + 1)).Ar *
          (Acell (qChain L).cr (qChain L).ci (qChain L).rho (L.mU + (qChain L).rho + 1)).Ar +
        (Acell (qChain L).cr (qChain L).ci (qChain L).rho (L.mU + (qChain L).rho + 1)).Ai *
          (Acell (qChain L).cr (qChain L).ci (qChain L).rho (L.mU + (qChain L).rho + 1)).Ai ≤
        L.aU * L.aU ∧ 0 ≤ L.bL ∧
      L.bL * L.bL ≤
        (Bcell (qChain L).cr (qChain L).ci (qChain L).rho (L.mU + (qChain L).rho + 1)).Br *
          (Bcell (qChain L).cr (qChain L).ci (qChain L).rho (L.mU + (qChain L).rho + 1)).Br +
        (Bcell (qChain L).cr (qChain L).ci (qChain L).rho (L.mU + (qChain L).rho + 1)).Bi *
          (Bcell (qChain L).cr (qChain L).ci (qChain L).rho (L.mU + (qChain L).rho + 1)).Bi ∧
      0 ≤ bU ∧
      (Bcell (qChain L).cr (qChain L).ci (qChain L).rho (L.mU + (qChain L).rho + 1)).Br *
          (Bcell (qChain L).cr (qChain L).ci (qChain L).rho (L.mU + (qChain L).rho + 1)).Br +
        (Bcell (qChain L).cr (qChain L).ci (qChain L).rho (L.mU + (qChain L).rho + 1)).Bi *
          (Bcell (qChain L).cr (qChain L).ci (qChain L).rho (L.mU + (qChain L).rho + 1)).Bi ≤
        bU * bU ∧
      0 < L.bL - ((Bcell (qChain L).cr (qChain L).ci (qChain L).rho
            (L.mU + (qChain L).rho + 1)).dB +
          tailBZ (qChain L).cr (qChain L).ci (qChain L).rho (L.mU + (qChain L).rho + 1)) ∧
      0 < md L.bL (L.bL - ((Bcell (qChain L).cr (qChain L).ci (qChain L).rho
            (L.mU + (qChain L).rho + 1)).dB +
          tailBZ (qChain L).cr (qChain L).ci (qChain L).rho (L.mU + (qChain L).rho + 1))) ∧
      0 < fdiv ((Bcell (qChain L).cr (qChain L).ci (qChain L).rho
              (L.mU + (qChain L).rho + 1)).Br *
            (Bcell (qChain L).cr (qChain L).ci (qChain L).rho
              (L.mU + (qChain L).rho + 1)).Br +
          (Bcell (qChain L).cr (qChain L).ci (qChain L).rho
              (L.mU + (qChain L).rho + 1)).Bi *
            (Bcell (qChain L).cr (qChain L).ci (qChain L).rho
              (L.mU + (qChain L).rho + 1)).Bi) S := by
    have hh := h
    unfold gDisc at hh
    simp only [Bool.and_eq_true, decide_eq_true_eq, Acell, Bcell, tailAZ, tailBZ] at hh
    tauto
  simpa only [QA, QB, QeA, QeB, Qb2, Acell, Bcell, tailAZ, tailBZ] using h'

/-! ## Unwinding the leaf test -/

theorem windLeafOK_facts (lab : ℕ) (L : Leaf) (bU : ℤ) (h : windLeafOK lab L bU = true) :
    lab < 4 ∧ (gDisc L bU).1 = true ∧
      (gDisc L bU).2.2.2 < labRe lab (gDisc L bU).2.1 (gDisc L bU).2.2.1 := by
  simp only [windLeafOK, Bool.and_eq_true, decide_eq_true_eq] at h
  exact ⟨h.1.1.2, h.1.2, h.2⟩

/-! ## The `q`-disc of a leaf contains `ψ_A` of the leaf disc -/

theorem qChain_disc_impl (hR : RotConsts) (hS : SlitStageSound) (hL : LuneStageSound)
    (L : Leaf) (z : ℂ) (hok : (qChain L).ok = true) (hz : ‖z - leafC L‖ ≤ leafR L) :
    ‖psiA z - cx (qChain L).cr (qChain L).ci‖ ≤ ((qChain L).rho : ℝ) / (S : ℝ) := by
  have hst5 : (stage5 L).ok = true := by
    rw [qChain_ok_eq] at hok
    exact hok
  have h0 : ‖lune (36 / 5) (-(slitsA z)) - cx (stage5 L).cr (stage5 L).ci‖
      ≤ ((stage5 L).rho : ℝ) / (S : ℝ) :=
    stage_chain hR hS hL L hst5 z (leaf_st0_mem L z hz)
  have h1 := q_disc_mem L (lune (36 / 5) (-(slitsA z))) h0
  rw [qChain_cr_eq, qChain_ci_eq, qChain_rho_eq]
  simpa [psiA] using h1

/-! ## The disc of the ratio `X = A(q)/B(q)` -/

theorem ratio_disc_impl {L : Leaf} {bU : ℤ} {q : ℂ}
    (hAcell : ‖thetaA q - cx (QA L).Ar (QA L).Ai‖ ≤ ((QeA L : ℤ) : ℝ) / (S : ℝ))
    (hBcell : ‖thetaB q - cx (QB L).Br (QB L).Bi‖ ≤ ((QeB L : ℤ) : ℝ) / (S : ℝ))
    (hAn : ‖cx (QA L).Ar (QA L).Ai‖ ≤ (L.aU : ℝ) / (S : ℝ))
    (hBl : (L.bL : ℝ) / (S : ℝ) ≤ ‖cx (QB L).Br (QB L).Bi‖)
    (hBu : ‖cx (QB L).Br (QB L).Bi‖ ≤ (bU : ℝ) / (S : ℝ))
    (haU : 0 ≤ L.aU) (hbU : 0 ≤ bU) (hBlo : 0 < L.bL - QeB L)
    (hD : 0 < md L.bL (L.bL - QeB L)) (hb2 : 0 < Qb2 L) :
    ‖thetaA q / thetaB q - cx (Qxr L) (Qxi L)‖ ≤ ((Qrx L bU : ℤ) : ℝ) / (S : ℝ) := by
  have hS : (0 : ℝ) < (S : ℝ) := S_posR
  -- the signs of the enclosure radii come from the enclosures themselves
  have heA : 0 ≤ QeA L := by
    have h : (0 : ℝ) ≤ ((QeA L : ℤ) : ℝ) / (S : ℝ) := le_trans (norm_nonneg _) hAcell
    have h2 : (0 : ℝ) ≤ ((QeA L : ℤ) : ℝ) := by
      have hh := mul_le_mul_of_nonneg_right h (le_of_lt hS)
      rw [div_mul_cancel₀ _ (ne_of_gt hS), zero_mul] at hh
      exact hh
    exact_mod_cast h2
  have heB : 0 ≤ QeB L := by
    have h : (0 : ℝ) ≤ ((QeB L : ℤ) : ℝ) / (S : ℝ) := le_trans (norm_nonneg _) hBcell
    have h2 : (0 : ℝ) ≤ ((QeB L : ℤ) : ℝ) := by
      have hh := mul_le_mul_of_nonneg_right h (le_of_lt hS)
      rw [div_mul_cancel₀ _ (ne_of_gt hS), zero_mul] at hh
      exact hh
    exact_mod_cast h2
  have hbLint : (0 : ℤ) < L.bL := by
    have h2 : (0 : ℤ) ≤ QeB L := heB
    omega
  have hbLpos : (0 : ℝ) < (L.bL : ℝ) := by
    have h : (0 : ℝ) < ((L.bL - QeB L : ℤ) : ℝ) := by exact_mod_cast hBlo
    have h2 : (0 : ℝ) ≤ ((QeB L : ℤ) : ℝ) := by exact_mod_cast heB
    push_cast at h ⊢
    linarith
  -- the lower bound `‖θ₄(q)‖ ≥ (bL - eB)/S`
  have hBq : ((L.bL - QeB L : ℤ) : ℝ) / (S : ℝ) ≤ ‖thetaB q‖ := by
    have htri := abs_norm_sub_norm_le (cx (QB L).Br (QB L).Bi) (thetaB q)
    have h1 : ‖cx (QB L).Br (QB L).Bi‖ - ‖thetaB q - cx (QB L).Br (QB L).Bi‖
        ≤ ‖thetaB q‖ := by
      have hh := (abs_le.mp htri).2
      rw [norm_sub_rev] at hh
      linarith [hh]
    have h3 : ((L.bL - QeB L : ℤ) : ℝ) / (S : ℝ)
        = (L.bL : ℝ) / (S : ℝ) - ((QeB L : ℤ) : ℝ) / (S : ℝ) := by
      push_cast; ring
    rw [h3]
    linarith [h1, hBl, hBcell]
  -- step 1: the perturbation of the division
  have h1 : ‖thetaA q / thetaB q - cx (QA L).Ar (QA L).Ai / cx (QB L).Br (QB L).Bi‖
      ≤ (((QeA L : ℤ) : ℝ) * (bU : ℝ) + (L.aU : ℝ) * ((QeB L : ℤ) : ℝ))
          / (((L.bL - QeB L : ℤ) : ℝ) * (L.bL : ℝ)) :=
    WL.ratio_le (thetaA q) (thetaB q) (cx (QA L).Ar (QA L).Ai) (cx (QB L).Br (QB L).Bi)
      (QeA L) (QeB L) L.aU bU L.bL (L.bL - QeB L)
      hAcell hBcell hAn hBu hBl hBq heA heB haU hbU hbLint hBlo
  -- step 2: the integer rounding of that bound
  have h2 : (S : ℝ) * ((((QeA L : ℤ) : ℝ) * (bU : ℝ) + (L.aU : ℝ) * ((QeB L : ℤ) : ℝ))
        / (((L.bL - QeB L : ℤ) : ℝ) * (L.bL : ℝ)))
      ≤ ((dvu (mu (QeA L) bU + mu L.aU (QeB L)) (md L.bL (L.bL - QeB L)) : ℤ) : ℝ) :=
    WL.dvu_ratio (QeA L) bU L.aU (QeB L) L.bL (L.bL - QeB L) heA hbU haU heB
      (le_of_lt hbLint) (le_of_lt hBlo) hD
  have h3 : ‖thetaA q / thetaB q - cx (QA L).Ar (QA L).Ai / cx (QB L).Br (QB L).Bi‖
      ≤ ((dvu (mu (QeA L) bU + mu L.aU (QeB L)) (md L.bL (L.bL - QeB L)) : ℤ) : ℝ)
          / (S : ℝ) := by
    have h4 : (((QeA L : ℤ) : ℝ) * (bU : ℝ) + (L.aU : ℝ) * ((QeB L : ℤ) : ℝ))
        / (((L.bL - QeB L : ℤ) : ℝ) * (L.bL : ℝ))
        ≤ ((dvu (mu (QeA L) bU + mu L.aU (QeB L)) (md L.bL (L.bL - QeB L)) : ℤ) : ℝ)
          / (S : ℝ) := by
      rw [le_div_iff₀ hS]
      linarith [h2]
    exact le_trans h1 h4
  -- step 3: the floors of the integer approximation of the ratio
  have h5 : ‖cx (QA L).Ar (QA L).Ai / cx (QB L).Br (QB L).Bi - cx (Qxr L) (Qxi L)‖
      ≤ ((2 * fdiv (iabs (Qxr L) + iabs (Qxi L) + 2) (Qb2 L) + 4 + ETOL : ℤ) : ℝ)
          / (S : ℝ) := by
    have hb2' : 0 < WL.gb20 (QB L).Br (QB L).Bi := hb2
    simpa only [Qxr, Qxi, Qb2, WL.gxr0, WL.gxi0, WL.gb20] using ratio_floor
      (ar := (QA L).Ar) (ai := (QA L).Ai) (br := (QB L).Br) (bi := (QB L).Bi) hb2'
  -- assemble
  have h6 : ‖thetaA q / thetaB q - cx (Qxr L) (Qxi L)‖
      ≤ ((dvu (mu (QeA L) bU + mu L.aU (QeB L)) (md L.bL (L.bL - QeB L)) : ℤ) : ℝ) / (S : ℝ)
        + ((2 * fdiv (iabs (Qxr L) + iabs (Qxi L) + 2) (Qb2 L) + 4 + ETOL : ℤ) : ℝ) / (S : ℝ) := by
    have hsplit : thetaA q / thetaB q - cx (Qxr L) (Qxi L)
        = (thetaA q / thetaB q - cx (QA L).Ar (QA L).Ai / cx (QB L).Br (QB L).Bi)
          + (cx (QA L).Ar (QA L).Ai / cx (QB L).Br (QB L).Bi - cx (Qxr L) (Qxi L)) := by ring
    calc ‖thetaA q / thetaB q - cx (Qxr L) (Qxi L)‖
        = ‖(thetaA q / thetaB q - cx (QA L).Ar (QA L).Ai / cx (QB L).Br (QB L).Bi)
          + (cx (QA L).Ar (QA L).Ai / cx (QB L).Br (QB L).Bi - cx (Qxr L) (Qxi L))‖ := by
          rw [hsplit]
      _ ≤ ‖thetaA q / thetaB q - cx (QA L).Ar (QA L).Ai / cx (QB L).Br (QB L).Bi‖
          + ‖cx (QA L).Ar (QA L).Ai / cx (QB L).Br (QB L).Bi - cx (Qxr L) (Qxi L)‖ :=
          norm_add_le _ _
      _ ≤ _ := add_le_add h3 h5
  have h7 : ((dvu (mu (QeA L) bU + mu L.aU (QeB L)) (md L.bL (L.bL - QeB L)) : ℤ) : ℝ) / (S : ℝ)
        + ((2 * fdiv (iabs (Qxr L) + iabs (Qxi L) + 2) (Qb2 L) + 4 + ETOL : ℤ) : ℝ) / (S : ℝ)
      = ((Qrx L bU : ℤ) : ℝ) / (S : ℝ) := by
    simp only [Qrx]
    push_cast
    ring
  rw [h7] at h6
  exact h6

/-! ## Powers of `X` -/

theorem X8_disc_impl {L : Leaf} {bU : ℤ} {X : ℂ}
    (hX : ‖X - cx (Qxr L) (Qxi L)‖ ≤ ((Qrx L bU : ℤ) : ℝ) / (S : ℝ)) :
    ‖X ^ 8 - cx (Qy L bU).1 (Qy L bU).2.1‖ ≤ (((Qy L bU).2.2 : ℤ) : ℝ) / (S : ℝ) := by
  have h2 := WL.sqD_sound (Qxr L, Qxi L, Qrx L bU) X hX
  have h4 := WL.sqD_sound (sqD (Qxr L, Qxi L, Qrx L bU)) (X ^ 2) (by simpa using h2)
  have h8 := WL.sqD_sound (sqD (sqD (Qxr L, Qxi L, Qrx L bU))) ((X ^ 2) ^ 2) (by simpa using h4)
  have hpow : ((X ^ 2) ^ 2) ^ 2 = X ^ 8 := by ring_nf
  rw [hpow] at h8
  simpa only [Qy] using h8

/-! ## The product `q·X^8` and the last rounding -/

theorem prod_disc_impl {L : Leaf} {bU : ℤ} {q X8 : ℂ}
    (hq : ‖q - cx (qChain L).cr (qChain L).ci‖ ≤ (((qChain L).rho : ℤ) : ℝ) / (S : ℝ))
    (h8 : ‖X8 - cx (Qy L bU).1 (Qy L bU).2.1‖ ≤ (((Qy L bU).2.2 : ℤ) : ℝ) / (S : ℝ)) :
    ‖q * X8 - cx (Qpr L bU) (Qpi L bU)‖ ≤ ((Qdd L bU + 4 : ℤ) : ℝ) / (S : ℝ) := by
  have h := WL.prod_disc (qChain L).cr (qChain L).ci (qChain L).rho (Qy L bU).1 (Qy L bU).2.1
    (Qy L bU).2.2 q X8 hq h8
  simpa only [Qpr, Qpi, Qdd] using h

theorem scale_impl {w : ℂ} {pr pi dd : ℤ}
    (hw : ‖w - cx pr pi‖ ≤ ((dd + 4 : ℤ) : ℝ) / (S : ℝ)) :
    ‖-256 * w + (1 / 72 : ℂ) - cx (-256 * pr + fdiv S 72) (-256 * pi)‖
      ≤ ((256 * dd + ETOL + ETOL : ℤ) : ℝ) / (S : ℝ) := by
  have hS : (0 : ℝ) < (S : ℝ) := S_posR
  set e : ℝ := (1 / 72 : ℝ) - ((fdiv S 72 : ℤ) : ℝ) / (S : ℝ) with he
  -- the rounding error of the constant `1/72`
  have hconst : |e| ≤ 1 / (S : ℝ) := by
    rw [he]
    have h1 : ((fdiv S 72 : ℤ) : ℝ) ≤ (S : ℝ) / 72 := fdiv_le_div S 72 (by norm_num)
    have h2 : (S : ℝ) / 72 - 1 < ((fdiv S 72 : ℤ) : ℝ) := by
      have h := Int.lt_ediv_add_one_mul_self S (by norm_num : (0 : ℤ) < 72)
      have hc : (((Int.ediv S 72 + 1) * 72 : ℤ) : ℝ)
          = (((Int.ediv S 72) : ℤ) : ℝ) * 72 + 72 := by push_cast; ring
      have h'' : (S : ℝ) < (((Int.ediv S 72 + 1) * 72 : ℤ) : ℝ) := by exact_mod_cast h
      rw [fdiv]
      linarith [h'', hc]
    have hkey : (1 / 72 : ℝ) - ((fdiv S 72 : ℤ) : ℝ) / (S : ℝ)
        = ((S : ℝ) / 72 - ((fdiv S 72 : ℤ) : ℝ)) / (S : ℝ) := by
      field_simp
    rw [hkey, abs_div, abs_of_pos hS]
    apply div_le_div_of_nonneg_right _ (le_of_lt hS)
    rw [abs_le]
    constructor <;> linarith
  have hcx : cx (-256 * pr + fdiv S 72) (-256 * pi)
      = -256 * cx pr pi + ((((fdiv S 72 : ℤ) : ℝ) / (S : ℝ)) : ℂ) := by
    simp only [cx]
    push_cast
    ring
  have hsplit : -256 * w + (1 / 72 : ℂ) - cx (-256 * pr + fdiv S 72) (-256 * pi)
      = -256 * (w - cx pr pi) + (e : ℂ) := by
    rw [hcx, he]
    push_cast
    ring
  rw [hsplit]
  refine le_trans (norm_add_le _ _) ?_
  have h1 : ‖-256 * (w - cx pr pi)‖ ≤ 256 * (((dd + 4 : ℤ) : ℝ) / (S : ℝ)) := by
    rw [norm_mul]
    have h2 : ‖(-256 : ℂ)‖ = 256 := by norm_num
    rw [h2]
    exact mul_le_mul_of_nonneg_left hw (by norm_num)
  have h3 : ‖(e : ℂ)‖ ≤ 1 / (S : ℝ) := by
    rw [norm_ofReal_cx]
    exact hconst
  have h4 : 256 * (((dd + 4 : ℤ) : ℝ) / (S : ℝ)) + 1 / (S : ℝ)
      ≤ ((256 * dd + ETOL + ETOL : ℤ) : ℝ) / (S : ℝ) := by
    have hL : 256 * (((dd + 4 : ℤ) : ℝ) / (S : ℝ)) + 1 / (S : ℝ)
        = ((256 * ((dd + 4 : ℤ) : ℝ) + 1) / (S : ℝ)) := by ring
    rw [hL]
    apply div_le_div_of_nonneg_right _ (le_of_lt hS)
    push_cast
    have hET : (1025 : ℝ) ≤ (ETOL : ℝ) + (ETOL : ℝ) := by norm_num [ETOL]
    linarith
  linarith [h1, h3, h4]

/-! ## The value disc of `g = h(ψ_A z) + 1/72` -/

theorem gDisc_mem_impl (hT : ThetaEncl) (hI : ThetaIdentity) (L : Leaf) (bU : ℤ) (z : ℂ)
    (hok : (gDisc L bU).1 = true)
    (hqmem : ‖psiA z - cx (qChain L).cr (qChain L).ci‖ ≤ (((qChain L).rho : ℤ) : ℝ) / (S : ℝ)) :
    ‖hauptH (psiA z) + 1 / 72 - cx (Qgr L bU) (Qgi L bU)‖
      ≤ ((Qrg L bU : ℤ) : ℝ) / (S : ℝ) := by
  obtain ⟨hokq, hmU, hq2, hokm, haU, hA, hbL, hB, hbU, hBu2, hBlo, hD, hb2⟩ := gDisc_ok_facts L bU hok
  -- the norm bounds of the `q`-disc
  have hqmemZ : ‖psiA z - cx (qrZ L) (qiZ L)‖ ≤ ((rqZ L : ℤ) : ℝ) / (S : ℝ) := by
    rw [← qChain_cr_eq, ← qChain_ci_eq, ← qChain_rho_eq]
    exact hqmem
  have hq2Z : qrZ L * qrZ L + qiZ L * qiZ L ≤ L.mU * L.mU := by
    rw [← qChain_cr_eq, ← qChain_ci_eq]
    exact hq2
  obtain ⟨hrq, hqle⟩ := q_norm_le L z hqmemZ hmU hq2Z
  have hq1 : ‖psiA z‖ < 1 := q_norm_lt_one L z hqle hokm
  -- the θ-enclosures
  have hth := hT (qChain L).cr (qChain L).ci (qChain L).rho L.mU hmU hq2 hrq hokm (psiA z) hqmem
  have hAcell : ‖thetaA (psiA z) - cx (QA L).Ar (QA L).Ai‖ ≤ ((QeA L : ℤ) : ℝ) / (S : ℝ) := by
    simpa only [QA, QeA, tailAZ, Acell] using hth.1
  have hBcell : ‖thetaB (psiA z) - cx (QB L).Br (QB L).Bi‖ ≤ ((QeB L : ℤ) : ℝ) / (S : ℝ) := by
    simpa only [QB, QeB, tailBZ, Bcell] using hth.2
  have hAn : ‖cx (QA L).Ar (QA L).Ai‖ ≤ (L.aU : ℝ) / (S : ℝ) :=
    norm_cx_le_of_sq_le _ _ _ haU hA
  have hBl : (L.bL : ℝ) / (S : ℝ) ≤ ‖cx (QB L).Br (QB L).Bi‖ :=
    norm_cx_ge_of_sq_le _ _ _ hbL hB
  have hBu' : ‖cx (QB L).Br (QB L).Bi‖ ≤ (bU : ℝ) / (S : ℝ) :=
    norm_cx_le_of_sq_le _ _ _ hbU hBu2
  have hX := ratio_disc_impl hAcell hBcell hAn hBl hBu' haU hbU hBlo hD hb2
  set X : ℂ := thetaA (psiA z) / thetaB (psiA z) with hXdef
  have hX' : ‖X - cx (Qxr L) (Qxi L)‖ ≤ ((Qrx L bU : ℤ) : ℝ) / (S : ℝ) := by
    rw [hXdef]
    exact hX
  have h8 := X8_disc_impl hX'
  have hprod := prod_disc_impl (bU := bU) hqmem h8
  have hg := scale_impl (pr := Qpr L bU) (pi := Qpi L bU) (dd := Qdd L bU) hprod
  -- `θ₄(q) ≠ 0`
  have hθBpos : 0 < ‖thetaB (psiA z)‖ := by
    have htri := abs_norm_sub_norm_le (cx (QB L).Br (QB L).Bi) (thetaB (psiA z))
    have h1 : ‖cx (QB L).Br (QB L).Bi‖ - ‖thetaB (psiA z) - cx (QB L).Br (QB L).Bi‖
        ≤ ‖thetaB (psiA z)‖ := by
      have hh := (abs_le.mp htri).2
      rw [norm_sub_rev] at hh
      linarith [hh]
    have h3 : ((L.bL - QeB L : ℤ) : ℝ) / (S : ℝ)
        = (L.bL : ℝ) / (S : ℝ) - ((QeB L : ℤ) : ℝ) / (S : ℝ) := by
      push_cast; ring
    have h4 : (0 : ℝ) < ((L.bL - QeB L : ℤ) : ℝ) / (S : ℝ) :=
      div_pos (by exact_mod_cast hBlo) S_posR
    linarith [h1, hBl, hBcell, h3, h4]
  have hθB : thetaB (psiA z) ≠ 0 := by
    intro h0
    rw [h0, norm_zero] at hθBpos
    exact lt_irrefl 0 hθBpos
  have hid := hI (psiA z) hq1
  have hhaupt : hauptH (psiA z) = -256 * (psiA z * X ^ 8) := by
    have h8ne : (thetaB (psiA z)) ^ 8 ≠ 0 := pow_ne_zero 8 hθB
    have h1 : hauptH (psiA z)
        = -256 * (psiA z) * thetaA (psiA z) ^ 8 / thetaB (psiA z) ^ 8 := by
      rw [eq_div_iff h8ne]
      exact hid
    rw [h1, hXdef, div_pow]
    ring
  rw [hhaupt]
  simpa only [Qgr, Qgi, Qrg] using hg

/-! ## The main statement -/

theorem wind_leaf_sound_impl (hR : Work.Cert.RotConsts) (hS : Work.Cert.SlitStageSound)
    (hL : Work.Cert.LuneStageSound) (hT : Work.Cert.ThetaEncl) (hI : Work.Cert.ThetaIdentity) :
    Work.Cert.WindLeafSound := by
  intro lab L bU hok z hz
  obtain ⟨hlab, hg1, hgr⟩ := windLeafOK_facts lab L bU hok
  have hokfacts := gDisc_ok_facts L bU hg1
  have hqok : (qChain L).ok = true := hokfacts.1
  have hqdisc := qChain_disc_impl hR hS hL L z hqok hz
  have hgmem := gDisc_mem_impl hT hI L bU z hg1 hqdisc
  have hgmem' : ‖hauptH (psiA z) + 1 / 72 - cx (gDisc L bU).2.1 (gDisc L bU).2.2.1‖
      ≤ (((gDisc L bU).2.2.2 : ℤ) : ℝ) / (S : ℝ) := by
    rw [gDisc_gr_eq, gDisc_gi_eq, gDisc_rg_eq]
    exact hgmem
  have hfin := halfplane (w := hauptH (psiA z) + 1 / 72) (lab := lab) (cr := (gDisc L bU).2.1)
    (ci := (gDisc L bU).2.2.1) (ρ := (gDisc L bU).2.2.2) hlab hgr hgmem'
  simpa [phiA] using hfin

end Work.ANum3.Z2
