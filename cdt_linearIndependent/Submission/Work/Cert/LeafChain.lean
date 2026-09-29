import Submission.Work.Cert.LeafAux

/-! # The ψ_A stage chain of a leaf

`stage_chain` composes the four rotated slit stages and the lune stage (the soundness of each being
the hypotheses `SlitStageSound`, `LuneStageSound`, `RotConsts`) to send the input disc of a leaf to
the `stage5` disc, whose centre/radius are `qChain L`. -/

set_option maxRecDepth 100000

namespace Work.Cert
open Complex Submission.CDTPlan

/-- the composition of the four rotated slit stages and the lune stage maps the leaf input disc
into the `stage5` disc. -/
theorem stage_chain (hR : RotConsts) (hS : SlitStageSound) (hL : LuneStageSound) (L : Leaf)
    (hst5 : (stage5 L).ok = true) (z : ℂ)
    (h1 : ‖(491 / 500 : ℂ) * z - cx (stage0 L).cr (stage0 L).ci‖
      ≤ ((stage0 L).rho : ℝ) / (S : ℝ)) :
    ‖lune (36 / 5) (-(slitsA z)) - cx (stage5 L).cr (stage5 L).ci‖
      ≤ ((stage5 L).rho : ℝ) / (S : ℝ) := by
  have hst4 : (stage4 L).ok = true := stage4_ok L hst5
  have hst3 : (stage3 L).ok = true := stage3_ok L hst4
  have hst2 : (stage2 L).ok = true := stage2_ok L hst3
  have hst1 : (stage1 L).ok = true := stage1_ok L hst2
  have hst0 : (stage0 L).ok = true := stage0_ok L hst1
  set w1 : ℂ := (491 / 500 : ℂ) * z with hw1
  set p2 : ℂ := rot (2033 / 25000) * slit (9 / 10) w1 with hp2
  set p3 : ℂ := rot (2927 / 25000) * slit (379 / 625) p2 with hp3
  set p4 : ℂ := rot (453 / 12500) * slit (673 / 1250) p3 with hp4
  set p5 : ℂ := rot (-1971 / 25000) * slit (7487 / 10000) p4 with hp5
  have h1' : ‖w1 - cx (stage0 L).cr (stage0 L).ci‖ ≤ ((stage0 L).rho : ℝ) / (S : ℝ) := by
    simpa [hw1] using h1
  have h2 : ‖p2 - cx (stage1 L).cr (stage1 L).ci‖ ≤ ((stage1 L).rho : ℝ) / (S : ℝ) := by
    have hs := hS (9 / 10) (2033 / 25000) s0A s0B2 s0E s0C1 s0G8 s0A2 rot0r rot0i (stage0 L)
      L.w0 (by norm_num) (by norm_num) s0A_eq s0B2_eq s0E_eq s0C1_eq s0G8_eq s0A2_eq hR.1 (by simpa [stage1] using hst1)
    simpa [hp2, stage1] using hs w1 h1'
  have h3 : ‖p3 - cx (stage2 L).cr (stage2 L).ci‖ ≤ ((stage2 L).rho : ℝ) / (S : ℝ) := by
    have hs := hS (379 / 625) (2927 / 25000) s1A s1B2 s1E s1C1 s1G8 s1A2 rot1r rot1i (stage1 L)
      L.w1 (by norm_num) (by norm_num) s1A_eq s1B2_eq s1E_eq s1C1_eq s1G8_eq s1A2_eq hR.2.1 (by simpa [stage2] using hst2)
    simpa [hp3, stage2] using hs p2 h2
  have h4 : ‖p4 - cx (stage3 L).cr (stage3 L).ci‖ ≤ ((stage3 L).rho : ℝ) / (S : ℝ) := by
    have hs := hS (673 / 1250) (453 / 12500) s2A s2B2 s2E s2C1 s2G8 s2A2 rot2r rot2i (stage2 L)
      L.w2 (by norm_num) (by norm_num) s2A_eq s2B2_eq s2E_eq s2C1_eq s2G8_eq s2A2_eq hR.2.2.1 (by simpa [stage3] using hst3)
    simpa [hp4, stage3] using hs p3 h3
  have h5 : ‖p5 - cx (stage4 L).cr (stage4 L).ci‖ ≤ ((stage4 L).rho : ℝ) / (S : ℝ) := by
    have hs := hS (7487 / 10000) (-1971 / 25000) s3A s3B2 s3E s3C1 s3G8 s3A2 rot3r rot3i
      (stage3 L) L.w3 (by norm_num) (by norm_num) s3A_eq s3B2_eq s3E_eq s3C1_eq s3G8_eq s3A2_eq
      hR.2.2.2.1 (by simpa [stage4] using hst4)
    simpa [hp5, stage4] using hs p4 h4
  have hp5eq : p5 = slitsA z := by
    rw [hp5, hp4, hp3, hp2, hw1]
    rfl
  have hl := hL (stage4 L) L.wl (by simpa [stage5] using hst5) p5 h5
  simpa [hp5eq, stage5] using hl

/-- `fdiv a b ≤ a/b` for `0 < b` (floor division). -/
lemma fdiv_le_div (a b : ℤ) (hb : 0 < b) : ((fdiv a b : ℤ) : ℝ) ≤ (a : ℝ) / (b : ℝ) := by
  have h := Int.ediv_mul_le a (ne_of_gt hb)
  have hbR : (0 : ℝ) < (b : ℝ) := by exact_mod_cast hb
  rw [fdiv, le_div_iff₀ hbR]
  exact_mod_cast h

/-- the `q`-disc of a leaf: radius non-negative, and `‖ψ_A z‖ ≤ mZ L / S`. -/
theorem q_norm_le (L : Leaf) (z : ℂ)
    (hqmem : ‖psiA z - cx (qrZ L) (qiZ L)‖ ≤ ((rqZ L : ℤ) : ℝ) / (S : ℝ))
    (hmU : 0 ≤ L.mU) (hokq : qrZ L * qrZ L + qiZ L * qiZ L ≤ L.mU * L.mU) :
    0 ≤ rqZ L ∧ ‖psiA z‖ ≤ (mZ L : ℝ) / (S : ℝ) := by
  have hnn : (0 : ℝ) ≤ ((rqZ L : ℤ) : ℝ) / (S : ℝ) := le_trans (norm_nonneg _) hqmem
  have hrqR : (0 : ℝ) ≤ ((rqZ L : ℤ) : ℝ) := by
    have h := mul_nonneg hnn S_posR.le
    rwa [div_mul_cancel₀ _ (ne_of_gt S_posR)] at h
  have hrq : 0 ≤ rqZ L := by exact_mod_cast hrqR
  have hc : ‖cx (qrZ L) (qiZ L)‖ ≤ (L.mU : ℝ) / (S : ℝ) :=
    norm_cx_le_of_sq_le _ _ _ hmU hokq
  have h2 : ‖psiA z‖ ≤ ((rqZ L : ℤ) : ℝ) / (S : ℝ) + (L.mU : ℝ) / (S : ℝ) := by
    calc ‖psiA z‖ = ‖(psiA z - cx (qrZ L) (qiZ L)) + cx (qrZ L) (qiZ L)‖ := by
          rw [sub_add_cancel]
      _ ≤ ‖psiA z - cx (qrZ L) (qiZ L)‖ + ‖cx (qrZ L) (qiZ L)‖ := norm_add_le _ _
      _ ≤ _ := add_le_add hqmem hc
  refine ⟨hrq, ?_⟩
  calc ‖psiA z‖ ≤ ((rqZ L : ℤ) : ℝ) / (S : ℝ) + (L.mU : ℝ) / (S : ℝ) := h2
    _ = (((rqZ L : ℤ) : ℝ) + (L.mU : ℝ)) / (S : ℝ) := by ring
    _ ≤ (mZ L : ℝ) / (S : ℝ) := by
        refine div_le_div_of_nonneg_right ?_ S_posR.le
        simp only [mZ]
        push_cast
        linarith

/-- `‖ψ_A z‖ < 1` on the leaf disc. -/
theorem q_norm_lt_one (L : Leaf) (z : ℂ)
    (h : ‖psiA z‖ ≤ (mZ L : ℝ) / (S : ℝ)) (hokm : mZ L ≤ fdiv (79 * S) 100) :
    ‖psiA z‖ < 1 := by
  have h1 : (mZ L : ℝ) / (S : ℝ) ≤ ((fdiv (79 * S) 100 : ℤ) : ℝ) / (S : ℝ) := by
    refine div_le_div_of_nonneg_right ?_ S_posR.le
    exact_mod_cast hokm
  have h2 : ((fdiv (79 * S) 100 : ℤ) : ℝ) / (S : ℝ) ≤ (79 * (S : ℝ) / 100) / (S : ℝ) := by
    refine div_le_div_of_nonneg_right ?_ S_posR.le
    have h := fdiv_le_div (79 * S) 100 (by norm_num)
    simpa using h
  have h3 : (79 * (S : ℝ) / 100) / (S : ℝ) = 79 / 100 := by
    rw [div_eq_iff (ne_of_gt S_posR)]
    ring
  linarith


end Work.Cert
