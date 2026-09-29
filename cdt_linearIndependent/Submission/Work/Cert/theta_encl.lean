import Mathlib
import Submission.Work.Cert.Spec
import Submission.Work.Cert.ThetaDefs
import Submission.Work.Cert.cx_mul_le
import Submission.Work.Cert.pow_sub_le
import Submission.Work.Cert.thetaA_eq
import Submission.Work.Cert.thetaB_eq
import Submission.Work.Cert.Asum_tail_le
import Submission.Work.Cert.Bsum_tail_le
import Submission.Work.Cert.aLoop_inv
import Submission.Work.Cert.bLoop_inv

/-! # Soundness of the truncated theta sums (`ThetaEncl`)

`ThetaEncl` says that the two accumulator loops `aLoop`/`bLoop` (with their floored complex products)
enclose the Jacobi theta series `thetaA q = Σ q^{tri n}` and `thetaB q = 1 + 2Σ(-1)^n q^{n²}` on the
`q`-disc of radius `rq/S` around the centre `q_c = (qr+qi·i)/S`, with the explicit budgets
`dA + tailA`, `dB + tailB`.

Each series is split at its truncation point (`thetaA_eq`, `thetaB_eq`); the head is bounded by the
loop invariant (`aLoop_inv`, `bLoop_inv`: rounding budget `dA`/`dB`, mean-value credit `BdM`/`BdM2`,
partial-sum enclosure), and the tail by the geometric estimates `Asum_tail_le`, `Bsum_tail_le`. -/

namespace Work.Cert

open Complex Finset
open scoped BigOperators

noncomputable section

/-- Shifting a sum over `range (n+1)`: the `j = 0` term is isolated. -/
lemma sum_range_shift {M : Type*} [AddCommGroup M] (f : ℕ → M) (n : ℕ) :
    (∑ j ∈ Finset.range (n + 1), f j) = f 0 + ∑ j ∈ Finset.range n, f (j + 1) := by
  induction n with
  | zero => simp
  | succ k ih =>
      rw [Finset.sum_range_succ, ih, Finset.sum_range_succ]
      abel

/-- The hypotheses of `ThetaEncl` put the disc inside the `μ`-ball: `‖q‖ ≤ μ ≤ 79/100 < 1`. -/
lemma theta_setup (qr qi rq mU : ℤ) (hm : 1 ≤ mU + rq + 1) (hrq : 0 ≤ rq)
    (hμ : mub (mU + rq + 1) ≤ 79 / 100)
    (hzU : ‖qc qr qi‖ ≤ (mU : ℝ) / ((S : ℝ)))
    (q : ℂ) (hq : ‖q - qc qr qi‖ ≤ (rq : ℝ) / ((S : ℝ))) :
    ‖q‖ ≤ mub (mU + rq + 1) ∧ ‖qc qr qi‖ ≤ mub (mU + rq + 1)
      ∧ (0 : ℝ) ≤ mub (mU + rq + 1) ∧ mub (mU + rq + 1) < 1
      ∧ (0 : ℝ) < 1 - mub (mU + rq + 1) ∧ (mU + rq + 1 : ℤ) < S
      ∧ (0 : ℤ) < S - (mU + rq + 1)
      ∧ ((S - (mU + rq + 1) : ℤ) : ℝ) = (S : ℝ) * (1 - mub (mU + rq + 1)) := by
  have hSp : (0 : ℝ) < ((S : ℝ)) := thS_pos
  have hSnn : (0 : ℝ) ≤ ((S : ℝ)) := le_of_lt hSp
  have hrqR : (0 : ℝ) ≤ (rq : ℝ) := by exact_mod_cast hrq
  have hz : ‖qc qr qi‖ ≤ mub (mU + rq + 1) := by
    have h2 : (mU : ℝ) / ((S : ℝ)) ≤ mub (mU + rq + 1) := by
      rw [mub]
      apply div_le_div_of_nonneg_right _ hSnn
      push_cast
      linarith [hrqR]
    exact hzU.trans h2
  have hqnorm : ‖q‖ ≤ mub (mU + rq + 1) := by
    have h1 : ‖q‖ ≤ (rq : ℝ) / ((S : ℝ)) + (mU : ℝ) / ((S : ℝ)) := by
      calc ‖q‖ = ‖(q - qc qr qi) + qc qr qi‖ := by rw [sub_add_cancel]
        _ ≤ ‖q - qc qr qi‖ + ‖qc qr qi‖ := norm_add_le _ _
        _ ≤ (rq : ℝ) / ((S : ℝ)) + (mU : ℝ) / ((S : ℝ)) := add_le_add hq hzU
    have h2 : (rq : ℝ) / ((S : ℝ)) + (mU : ℝ) / ((S : ℝ)) ≤ mub (mU + rq + 1) := by
      rw [mub, show (rq : ℝ) / ((S : ℝ)) + (mU : ℝ) / ((S : ℝ))
        = (((rq + mU : ℤ)) : ℝ) / ((S : ℝ)) by push_cast; ring]
      apply div_le_div_of_nonneg_right _ hSnn
      push_cast
      linarith
    linarith [h1, h2]
  have hμ0 : (0 : ℝ) ≤ mub (mU + rq + 1) := by rw [mub]; positivity
  have hμ1 : mub (mU + rq + 1) < 1 := by linarith
  have hmS : ((mU + rq + 1 : ℤ) : ℝ) < ((S : ℝ)) := by
    have hmul : mub (mU + rq + 1) * ((S : ℝ)) = ((mU + rq + 1 : ℤ) : ℝ) := by
      rw [mub]; field_simp
    nlinarith [hμ, hSp, hmul]
  have hlt : (mU + rq + 1 : ℤ) < S := by exact_mod_cast hmS
  have hden : ((S - (mU + rq + 1) : ℤ) : ℝ) = (S : ℝ) * (1 - mub (mU + rq + 1)) := by
    rw [mub]; push_cast; field_simp
  refine ⟨hqnorm, hz, hμ0, hμ1, ?_, hlt, ?_, hden⟩
  · linarith
  · omega

/-- The `thetaA` half of `ThetaEncl`: given the loop invariant for `s`, the truncated theta series
encloses `thetaA` on the disc. -/
lemma thetaA_encl_of_state (s : TS) (qr qi rq mU : ℤ) (hm : 1 ≤ mU + rq + 1) (hrq : 0 ≤ rq)
    (hμ : mub (mU + rq + 1) ≤ 79 / 100)
    (hzU : ‖qc qr qi‖ ≤ (mU : ℝ) / ((S : ℝ)))
    (q : ℂ) (hq : ‖q - qc qr qi‖ ≤ (rq : ℝ) / ((S : ℝ)))
    (hA : AInv qr qi rq (mU + rq + 1) KTH s) :
    ‖thetaA q - cx s.Ar s.Ai‖ ≤
      ((((s.dA + (dvu (mu s.mT (mu s.mn (mU + rq + 1) + 1)) (S - (mU + rq + 1)) + 1)) : ℤ)
        : ℝ)) / ((S : ℝ)) := by
  obtain ⟨hqnorm, hz, hμ0, hμ1, h1μ, hlt, hbpos, hden⟩ :=
    theta_setup qr qi rq mU hm hrq hμ hzU q hq
  have hSnn : (0 : ℝ) ≤ ((S : ℝ)) := le_of_lt thS_pos
  obtain ⟨hpn, hpT, hT, hmn, hmT, hdA, hsum⟩ := hA
  have hmT78 : (mub (mU + rq + 1)) ^ 78 ≤ (s.mT : ℝ) / ((S : ℝ)) := by
    have h := hmT
    rw [show tri KTH = 78 by decide] at h
    exact h
  have hmn12 : (mub (mU + rq + 1)) ^ 12 ≤ (s.mn : ℝ) / ((S : ℝ)) := by
    simpa [KTH] using hmn
  have hdA12 : Bd KTH + BdM (mU + rq + 1) rq KTH ≤ (s.dA : ℝ) := hdA
  -- (1) the tail: the geometric estimate is dominated by the certificate tail
  have htail : ‖thetaA q - Asum q 13‖ ≤ ((dvu (mu s.mT (mu s.mn (mU + rq + 1) + 1))
      (S - (mU + rq + 1)) + 1 : ℤ) : ℝ) / ((S : ℝ)) := by
    have hg := Asum_tail_le (q := q) (ρ := mub (mU + rq + 1)) hμ0 hμ1 hqnorm
    have h2 : (mub (mU + rq + 1)) ^ 91 / (1 - mub (mU + rq + 1))
        ≤ ((dvu (mu s.mT (mu s.mn (mU + rq + 1) + 1)) (S - (mU + rq + 1)) + 1 : ℤ) : ℝ)
          / ((S : ℝ)) := by
      have hmK1 : (mub (mU + rq + 1)) ^ 13
          ≤ (((mu s.mn (mU + rq + 1) + 1) : ℤ) : ℝ) / ((S : ℝ)) := by
        have h1 : ((s.mn : ℝ) / ((S : ℝ))) * (((mU + rq + 1 : ℤ) : ℝ) / ((S : ℝ)))
            ≤ ((mu s.mn (mU + rq + 1) : ℤ) : ℝ) / ((S : ℝ)) := thmu_ge _ _
        have h2 : (mub (mU + rq + 1)) ^ 12 * mub (mU + rq + 1)
            ≤ ((mu s.mn (mU + rq + 1) : ℤ) : ℝ) / ((S : ℝ)) :=
          le_trans (mul_le_mul_of_nonneg_right hmn12 hμ0) (by simpa only [mub] using h1)
        have h3 : (mub (mU + rq + 1)) ^ 12 * mub (mU + rq + 1)
            = (mub (mU + rq + 1)) ^ 13 := by rw [← pow_succ]
        rw [h3] at h2
        have h4 : ((mu s.mn (mU + rq + 1) + 1 : ℤ) : ℝ) / ((S : ℝ))
            = ((mu s.mn (mU + rq + 1) : ℤ) : ℝ) / ((S : ℝ)) + 1 / ((S : ℝ)) := by
          push_cast; ring
        rw [h4]
        have h5 : (0 : ℝ) ≤ 1 / ((S : ℝ)) := by positivity
        linarith [h2, h5]
      have h91 : (mub (mU + rq + 1)) ^ 91
          ≤ ((mu s.mT (mu s.mn (mU + rq + 1) + 1) : ℤ) : ℝ) / ((S : ℝ)) := by
        have hmT0 : (0 : ℝ) ≤ (s.mT : ℝ) / ((S : ℝ)) := le_trans (pow_nonneg hμ0 78) hmT78
        have h1 : ((s.mT : ℝ) / ((S : ℝ)))
              * ((((mu s.mn (mU + rq + 1) + 1) : ℤ) : ℝ) / ((S : ℝ)))
            ≤ ((mu s.mT (mu s.mn (mU + rq + 1) + 1) : ℤ) : ℝ) / ((S : ℝ)) := thmu_ge _ _
        have h2 : (mub (mU + rq + 1)) ^ 78 * (mub (mU + rq + 1)) ^ 13
            ≤ ((s.mT : ℝ) / ((S : ℝ)))
              * ((((mu s.mn (mU + rq + 1) + 1) : ℤ) : ℝ) / ((S : ℝ))) :=
          mul_le_mul hmT78 hmK1 (pow_nonneg hμ0 13) hmT0
        have h3 : (mub (mU + rq + 1)) ^ 78 * (mub (mU + rq + 1)) ^ 13
            = (mub (mU + rq + 1)) ^ 91 := by rw [← pow_add]
        rw [h3] at h2
        exact h2.trans h1
      have hdvu := thdvu_ge (mu s.mT (mu s.mn (mU + rq + 1) + 1)) (S - (mU + rq + 1)) hbpos
      have h6 : (mub (mU + rq + 1)) ^ 91 / (1 - mub (mU + rq + 1))
          ≤ ((((mu s.mT (mu s.mn (mU + rq + 1) + 1) : ℤ) : ℝ) / ((S : ℝ)))
            / (1 - mub (mU + rq + 1))) := div_le_div_of_nonneg_right h91 (le_of_lt h1μ)
      have h7 : ((((mu s.mT (mu s.mn (mU + rq + 1) + 1) : ℤ) : ℝ) / ((S : ℝ)))
            / (1 - mub (mU + rq + 1)))
          = ((mu s.mT (mu s.mn (mU + rq + 1) + 1) : ℤ) : ℝ)
            / ((S - (mU + rq + 1) : ℤ) : ℝ) := by rw [hden]; field_simp
      have h9 : ((dvu (mu s.mT (mu s.mn (mU + rq + 1) + 1)) (S - (mU + rq + 1)) : ℤ) : ℝ)
            / ((S : ℝ))
          ≤ ((dvu (mu s.mT (mu s.mn (mU + rq + 1) + 1)) (S - (mU + rq + 1)) + 1 : ℤ) : ℝ)
            / ((S : ℝ)) := by
        have h10 : ((dvu (mu s.mT (mu s.mn (mU + rq + 1) + 1)) (S - (mU + rq + 1)) + 1 : ℤ) : ℝ)
              / ((S : ℝ))
            = ((dvu (mu s.mT (mu s.mn (mU + rq + 1) + 1)) (S - (mU + rq + 1)) : ℤ) : ℝ)
              / ((S : ℝ)) + 1 / ((S : ℝ)) := by
          push_cast; ring
        rw [h10]
        have h11 : (0 : ℝ) ≤ 1 / ((S : ℝ)) := by positivity
        linarith [h11]
      calc (mub (mU + rq + 1)) ^ 91 / (1 - mub (mU + rq + 1))
          ≤ ((((mu s.mT (mu s.mn (mU + rq + 1) + 1) : ℤ) : ℝ) / ((S : ℝ)))
            / (1 - mub (mU + rq + 1))) := h6
        _ = ((mu s.mT (mu s.mn (mU + rq + 1) + 1) : ℤ) : ℝ)
            / ((S - (mU + rq + 1) : ℤ) : ℝ) := h7
        _ ≤ ((dvu (mu s.mT (mu s.mn (mU + rq + 1) + 1)) (S - (mU + rq + 1)) : ℤ) : ℝ)
            / ((S : ℝ)) := hdvu
        _ ≤ ((dvu (mu s.mT (mu s.mn (mU + rq + 1) + 1)) (S - (mU + rq + 1)) + 1 : ℤ) : ℝ)
            / ((S : ℝ)) := h9
    have hsplit := thetaA_eq q (by linarith)
    rw [hsplit, add_sub_cancel_left]
    exact hg.trans h2
  -- (2) the mean-value part
  have hmvt : ‖Asum q 13 - Asum (qc qr qi) 13‖ ≤ (BdM (mU + rq + 1) rq 12) / ((S : ℝ)) := by
    have hterm : ∀ j ∈ Finset.range 13,
        ‖q ^ tri j - (qc qr qi) ^ tri j‖
          ≤ ((tri j : ℝ) * (mub (mU + rq + 1)) ^ (tri j - 1) * (rq : ℝ)) / ((S : ℝ)) := by
      intro j hj
      rcases Nat.eq_zero_or_pos j with h0 | hpos
      · subst h0
        simp
      · have hp := pow_sub_le (z := qc qr qi) (w := q) (ρ := mub (mU + rq + 1))
            (r := (rq : ℝ) / ((S : ℝ))) hμ0 hz hqnorm hq (tri j)
        have hrw : (tri j : ℝ) * (mub (mU + rq + 1)) ^ (tri j - 1) * ((rq : ℝ) / ((S : ℝ)))
            = ((tri j : ℝ) * (mub (mU + rq + 1)) ^ (tri j - 1) * (rq : ℝ)) / ((S : ℝ)) := by
          ring
        rwa [hrw] at hp
    have hsum1 : ‖∑ j ∈ Finset.range 13, (q ^ tri j - (qc qr qi) ^ tri j)‖
        ≤ ∑ j ∈ Finset.range 13,
            ((tri j : ℝ) * (mub (mU + rq + 1)) ^ (tri j - 1) * (rq : ℝ)) / ((S : ℝ)) :=
      (norm_sum_le _ _).trans (Finset.sum_le_sum hterm)
    have hR : (∑ j ∈ Finset.range 13,
          ((tri j : ℝ) * (mub (mU + rq + 1)) ^ (tri j - 1) * (rq : ℝ)) / ((S : ℝ)))
        = (BdM (mU + rq + 1) rq 12) / ((S : ℝ)) := by
      rw [← Finset.sum_div, sum_range_shift]
      simp only [tri_zero, Nat.cast_zero, Nat.zero_sub, pow_zero, mul_one, zero_mul, zero_add]
      rw [BdM]
    rw [hR] at hsum1
    have hsub : Asum q 13 - Asum (qc qr qi) 13
        = ∑ j ∈ Finset.range 13, (q ^ tri j - (qc qr qi) ^ tri j) := by
      rw [Asum, Asum, Finset.sum_sub_distrib]
    rwa [hsub]
  -- (3) the enclosure error of the accumulated partial sum
  have hsum' : ‖Asum (qc qr qi) 13 - cx s.Ar s.Ai‖ ≤ (Bd 12) / ((S : ℝ)) := by
    have h := hsum
    rw [show KTH + 1 = 13 by decide, show KTH = 12 by decide] at h
    rwa [norm_sub_rev]
  have hdA' : Bd 12 + BdM (mU + rq + 1) rq 12 ≤ (s.dA : ℝ) := by
    have h := hdA12
    rwa [show KTH = 12 by decide] at h
  -- (4) combine
  have hcomb : ‖thetaA q - cx s.Ar s.Ai‖
      ≤ (Bd 12) / ((S : ℝ)) + (BdM (mU + rq + 1) rq 12) / ((S : ℝ))
        + ((dvu (mu s.mT (mu s.mn (mU + rq + 1) + 1)) (S - (mU + rq + 1)) + 1 : ℤ) : ℝ)
          / ((S : ℝ)) := by
    have hrew : thetaA q - cx s.Ar s.Ai
        = (thetaA q - Asum q 13) + ((Asum q 13 - Asum (qc qr qi) 13)
          + (Asum (qc qr qi) 13 - cx s.Ar s.Ai)) := by ring
    have hab := norm_add_le (thetaA q - Asum q 13)
      ((Asum q 13 - Asum (qc qr qi) 13) + (Asum (qc qr qi) 13 - cx s.Ar s.Ai))
    have hbc := norm_add_le (Asum q 13 - Asum (qc qr qi) 13) (Asum (qc qr qi) 13 - cx s.Ar s.Ai)
    rw [hrew]
    linarith [htail, hmvt, hsum', hab, hbc]
  have hfin : (Bd 12) / ((S : ℝ)) + (BdM (mU + rq + 1) rq 12) / ((S : ℝ)) ≤ (s.dA : ℝ) / ((S : ℝ)) := by
    have h := div_le_div_of_nonneg_right hdA' hSnn
    rwa [add_div] at h
  have hcast : (((s.dA + (dvu (mu s.mT (mu s.mn (mU + rq + 1) + 1)) (S - (mU + rq + 1)) + 1)
      : ℤ)) : ℝ) / ((S : ℝ))
      = (s.dA : ℝ) / ((S : ℝ))
        + ((dvu (mu s.mT (mu s.mn (mU + rq + 1) + 1)) (S - (mU + rq + 1)) + 1 : ℤ) : ℝ)
          / ((S : ℝ)) := by
    push_cast; ring
  rw [hcast]
  linarith [hcomb, hfin]

/-- The `thetaB` half of `ThetaEncl`: given the loop invariant for `s`, the truncated theta series
encloses `thetaB` on the disc. -/
lemma thetaB_encl_of_state (s : BS) (qr qi rq mU : ℤ) (hm : 1 ≤ mU + rq + 1) (hrq : 0 ≤ rq)
    (hμ : mub (mU + rq + 1) ≤ 79 / 100)
    (hzU : ‖qc qr qi‖ ≤ (mU : ℝ) / ((S : ℝ)))
    (q : ℂ) (hq : ‖q - qc qr qi‖ ≤ (rq : ℝ) / ((S : ℝ)))
    (hB : BInv qr qi rq (mU + rq + 1) KTH s) :
    ‖thetaB q - cx s.Br s.Bi‖ ≤
      ((((s.dB + (2 * dvu (mu s.ms s.mo) (S - (mU + rq + 1)) + 1)) : ℤ) : ℝ)) / ((S : ℝ)) := by
  obtain ⟨hqnorm, hz, hμ0, hμ1, h1μ, hlt, hbpos, hden⟩ :=
    theta_setup qr qi rq mU hm hrq hμ hzU q hq
  have hSnn : (0 : ℝ) ≤ ((S : ℝ)) := le_of_lt thS_pos
  obtain ⟨hpor, hpsr, hms, hmo, hdB, hsumB⟩ := hB
  have hms144 : (mub (mU + rq + 1)) ^ 144 ≤ (s.ms : ℝ) / ((S : ℝ)) := by
    have h := hms
    rw [show KTH * KTH = 144 by decide] at h
    exact h
  have hmo25 : (mub (mU + rq + 1)) ^ 25 ≤ (s.mo : ℝ) / ((S : ℝ)) := by
    have h := hmo
    rw [show 2 * KTH + 1 = 25 by decide] at h
    exact h
  -- (1) the tail
  have htailB : ‖thetaB q - Bsum q 12‖
      ≤ ((2 * dvu (mu s.ms s.mo) (S - (mU + rq + 1)) + 1 : ℤ) : ℝ) / ((S : ℝ)) := by
    have hg := Bsum_tail_le (q := q) (ρ := mub (mU + rq + 1)) hμ0 hμ1 hqnorm
    have h2 : 2 * (mub (mU + rq + 1)) ^ 169 / (1 - mub (mU + rq + 1))
        ≤ ((2 * dvu (mu s.ms s.mo) (S - (mU + rq + 1)) + 1 : ℤ) : ℝ) / ((S : ℝ)) := by
      have hmu : (mub (mU + rq + 1)) ^ 169
          ≤ ((mu s.ms s.mo : ℤ) : ℝ) / ((S : ℝ)) := by
        have h1 : ((s.ms : ℝ) / ((S : ℝ))) * ((s.mo : ℝ) / ((S : ℝ)))
            ≤ ((mu s.ms s.mo : ℤ) : ℝ) / ((S : ℝ)) := thmu_ge _ _
        have hms0 : (0 : ℝ) ≤ (s.ms : ℝ) / ((S : ℝ)) := le_trans (pow_nonneg hμ0 144) hms144
        have h2 : (mub (mU + rq + 1)) ^ 144 * (mub (mU + rq + 1)) ^ 25
            ≤ ((s.ms : ℝ) / ((S : ℝ))) * ((s.mo : ℝ) / ((S : ℝ))) :=
          mul_le_mul hms144 hmo25 (pow_nonneg hμ0 25) hms0
        have h2b : (mub (mU + rq + 1)) ^ 144 * (mub (mU + rq + 1)) ^ 25
            ≤ ((mu s.ms s.mo : ℤ) : ℝ) / ((S : ℝ)) :=
          le_trans h2 (by simpa only [mub] using h1)
        have h3 : (mub (mU + rq + 1)) ^ 144 * (mub (mU + rq + 1)) ^ 25
            = (mub (mU + rq + 1)) ^ 169 := by rw [← pow_add]
        rwa [h3] at h2b
      have hdvu := thdvu_ge (mu s.ms s.mo) (S - (mU + rq + 1)) hbpos
      rw [show 2 * (mub (mU + rq + 1)) ^ 169 / (1 - mub (mU + rq + 1))
          = 2 * ((mub (mU + rq + 1)) ^ 169 / (1 - mub (mU + rq + 1))) by ring]
      calc 2 * ((mub (mU + rq + 1)) ^ 169 / (1 - mub (mU + rq + 1)))
          ≤ 2 * ((((mu s.ms s.mo : ℤ) : ℝ) / ((S : ℝ))) / (1 - mub (mU + rq + 1))) :=
            mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right hmu (le_of_lt h1μ)) (by norm_num)
        _ = 2 * (((mu s.ms s.mo : ℤ) : ℝ) / ((S - (mU + rq + 1) : ℤ) : ℝ)) := by
            rw [hden]; field_simp
        _ ≤ 2 * (((dvu (mu s.ms s.mo) (S - (mU + rq + 1)) : ℤ) : ℝ) / ((S : ℝ))) :=
            mul_le_mul_of_nonneg_left hdvu (by norm_num)
        _ ≤ ((2 * dvu (mu s.ms s.mo) (S - (mU + rq + 1)) + 1 : ℤ) : ℝ) / ((S : ℝ)) := by
            have h10 : ((2 * dvu (mu s.ms s.mo) (S - (mU + rq + 1)) + 1 : ℤ) : ℝ) / ((S : ℝ))
                = 2 * (((dvu (mu s.ms s.mo) (S - (mU + rq + 1)) : ℤ) : ℝ) / ((S : ℝ)))
                  + 1 / ((S : ℝ)) := by
              push_cast; ring
            rw [h10]
            have h11 : (0 : ℝ) ≤ 1 / ((S : ℝ)) := by positivity
            linarith [h11]
    have hsplit := thetaB_eq q (by linarith)
    rw [hsplit, add_sub_cancel_left]
    exact hg.trans h2
  -- (2) the mean-value part
  have hmvtB : ‖Bsum q 12 - Bsum (qc qr qi) 12‖ ≤ (BdM2 (mU + rq + 1) rq 12) / ((S : ℝ)) := by
    have hterm : ∀ j ∈ Finset.range 12,
        ‖2 * (-1 : ℂ) ^ (j + 1) * q ^ ((j + 1) ^ 2)
            - 2 * (-1 : ℂ) ^ (j + 1) * (qc qr qi) ^ ((j + 1) ^ 2)‖
          ≤ (2 * ((((j + 1) ^ 2 : ℕ)) : ℝ) * (mub (mU + rq + 1)) ^ ((j + 1) ^ 2 - 1)
              * (rq : ℝ)) / ((S : ℝ)) := by
      intro j hj
      have hp := pow_sub_le (z := qc qr qi) (w := q) (ρ := mub (mU + rq + 1))
        (r := (rq : ℝ) / ((S : ℝ))) hμ0 hz hqnorm hq ((j + 1) ^ 2)
      have heq : 2 * (-1 : ℂ) ^ (j + 1) * q ^ ((j + 1) ^ 2)
          - 2 * (-1 : ℂ) ^ (j + 1) * (qc qr qi) ^ ((j + 1) ^ 2)
          = 2 * (-1 : ℂ) ^ (j + 1) * (q ^ ((j + 1) ^ 2) - (qc qr qi) ^ ((j + 1) ^ 2)) := by
        ring
      have hnorm : ‖2 * (-1 : ℂ) ^ (j + 1)
            * (q ^ ((j + 1) ^ 2) - (qc qr qi) ^ ((j + 1) ^ 2))‖
          = 2 * ‖q ^ ((j + 1) ^ 2) - (qc qr qi) ^ ((j + 1) ^ 2)‖ := by
        simp only [norm_mul, norm_pow, Complex.norm_ofNat, norm_neg, norm_one, one_pow, mul_one]
      rw [heq, hnorm]
      calc 2 * ‖q ^ ((j + 1) ^ 2) - (qc qr qi) ^ ((j + 1) ^ 2)‖
          ≤ 2 * (((((j + 1) ^ 2 : ℕ)) : ℝ) * (mub (mU + rq + 1)) ^ ((j + 1) ^ 2 - 1)
              * ((rq : ℝ) / ((S : ℝ)))) :=
            mul_le_mul_of_nonneg_left hp (by norm_num)
        _ = (2 * ((((j + 1) ^ 2 : ℕ)) : ℝ) * (mub (mU + rq + 1)) ^ ((j + 1) ^ 2 - 1)
              * (rq : ℝ)) / ((S : ℝ)) := by ring
    have hsum1 : ‖∑ j ∈ Finset.range 12, (2 * (-1 : ℂ) ^ (j + 1) * q ^ ((j + 1) ^ 2)
            - 2 * (-1 : ℂ) ^ (j + 1) * (qc qr qi) ^ ((j + 1) ^ 2))‖
        ≤ ∑ j ∈ Finset.range 12,
            (2 * ((((j + 1) ^ 2 : ℕ)) : ℝ) * (mub (mU + rq + 1)) ^ ((j + 1) ^ 2 - 1)
              * (rq : ℝ)) / ((S : ℝ)) :=
      (norm_sum_le _ _).trans (Finset.sum_le_sum hterm)
    have hR : (∑ j ∈ Finset.range 12,
          (2 * ((((j + 1) ^ 2 : ℕ)) : ℝ) * (mub (mU + rq + 1)) ^ ((j + 1) ^ 2 - 1)
            * (rq : ℝ)) / ((S : ℝ)))
        = (BdM2 (mU + rq + 1) rq 12) / ((S : ℝ)) := by
      rw [← Finset.sum_div]
      rfl
    rw [hR] at hsum1
    have hsub1 : Bsum q 12 - Bsum (qc qr qi) 12
        = (∑ j ∈ Finset.range 12, 2 * (-1 : ℂ) ^ (j + 1) * q ^ ((j + 1) ^ 2))
          - (∑ j ∈ Finset.range 12, 2 * (-1 : ℂ) ^ (j + 1) * (qc qr qi) ^ ((j + 1) ^ 2)) := by
      simp only [Bsum]; ring
    have hsub : Bsum q 12 - Bsum (qc qr qi) 12
        = ∑ j ∈ Finset.range 12, (2 * (-1 : ℂ) ^ (j + 1) * q ^ ((j + 1) ^ 2)
            - 2 * (-1 : ℂ) ^ (j + 1) * (qc qr qi) ^ ((j + 1) ^ 2)) := by
      rw [hsub1, ← Finset.sum_sub_distrib]
    rwa [hsub]
  -- (3) the enclosure error
  have hsumB' : ‖Bsum (qc qr qi) 12 - cx s.Br s.Bi‖ ≤ (Bd2 12) / ((S : ℝ)) := by
    have h := hsumB
    rw [show KTH = 12 by decide] at h
    rwa [norm_sub_rev]
  have hdB' : Bd2 12 + BdM2 (mU + rq + 1) rq 12 ≤ (s.dB : ℝ) := by
    have h := hdB
    rwa [show KTH = 12 by decide] at h
  have hcomb : ‖thetaB q - cx s.Br s.Bi‖
      ≤ (Bd2 12) / ((S : ℝ)) + (BdM2 (mU + rq + 1) rq 12) / ((S : ℝ))
        + ((2 * dvu (mu s.ms s.mo) (S - (mU + rq + 1)) + 1 : ℤ) : ℝ) / ((S : ℝ)) := by
    have hrew : thetaB q - cx s.Br s.Bi
        = (thetaB q - Bsum q 12) + ((Bsum q 12 - Bsum (qc qr qi) 12)
          + (Bsum (qc qr qi) 12 - cx s.Br s.Bi)) := by ring
    have hab := norm_add_le (thetaB q - Bsum q 12)
      ((Bsum q 12 - Bsum (qc qr qi) 12) + (Bsum (qc qr qi) 12 - cx s.Br s.Bi))
    have hbc := norm_add_le (Bsum q 12 - Bsum (qc qr qi) 12) (Bsum (qc qr qi) 12 - cx s.Br s.Bi)
    rw [hrew]
    linarith [htailB, hmvtB, hsumB', hab, hbc]
  have hfin : (Bd2 12) / ((S : ℝ)) + (BdM2 (mU + rq + 1) rq 12) / ((S : ℝ)) ≤ (s.dB : ℝ) / ((S : ℝ)) := by
    have h := div_le_div_of_nonneg_right hdB' hSnn
    rwa [add_div] at h
  have hcast : (((s.dB + (2 * dvu (mu s.ms s.mo) (S - (mU + rq + 1)) + 1) : ℤ)) : ℝ)
        / ((S : ℝ))
      = (s.dB : ℝ) / ((S : ℝ))
        + ((2 * dvu (mu s.ms s.mo) (S - (mU + rq + 1)) + 1 : ℤ) : ℝ) / ((S : ℝ)) := by
    push_cast; ring
  rw [hcast]
  linarith [hcomb, hfin]

theorem theta_encl : ThetaEncl := by
  intro qr qi rq mU hmU hqq hrq hm79 q hq
  have hSp : (0 : ℝ) < ((S : ℝ)) := thS_pos
  have hrqR : (0 : ℝ) ≤ (rq : ℝ) := by exact_mod_cast hrq
  have hqq' : (qr : ℝ) ^ 2 + (qi : ℝ) ^ 2 ≤ (mU : ℝ) ^ 2 := by
    have h1 : ((qr * qr + qi * qi : ℤ) : ℝ) ≤ ((mU * mU : ℤ) : ℝ) := by exact_mod_cast hqq
    push_cast at h1
    nlinarith [h1]
  have hzU : ‖qc qr qi‖ ≤ (mU : ℝ) / ((S : ℝ)) := by
    have := norm_cx_le (x := qr) (y := qi) hqq' (by positivity : (0 : ℝ) ≤ (mU : ℝ))
    simpa [qc] using this
  have hz : ‖qc qr qi‖ ≤ mub (mU + rq + 1) := by
    have h2 : (mU : ℝ) / ((S : ℝ)) ≤ mub (mU + rq + 1) := by
      rw [mub]
      apply div_le_div_of_nonneg_right _ (le_of_lt hSp)
      push_cast
      linarith [hrqR]
    exact hzU.trans h2
  have hμ : mub (mU + rq + 1) ≤ 79 / 100 := by
    have h2 : ((mU + rq + 1 : ℤ) : ℝ) ≤ ((fdiv (79 * S) 100 : ℤ) : ℝ) := by exact_mod_cast hm79
    have h3 : ((fdiv (79 * S) 100 : ℤ) : ℝ) ≤ (79 : ℝ) * ((S : ℝ)) / 100 := by
      have h4 : fdiv (79 * S) 100 * 100 ≤ 79 * S :=
        Int.ediv_mul_le (79 * S) (by norm_num : (100 : ℤ) ≠ 0)
      have h5 : (((fdiv (79 * S) 100 : ℤ) : ℝ)) * 100 ≤ ((79 * S : ℤ) : ℝ) := by
        exact_mod_cast h4
      push_cast at h5
      linarith
    rw [mub, div_le_iff₀ hSp]
    linarith
  have hm : 1 ≤ mU + rq + 1 := by omega
  constructor
  · exact thetaA_encl_of_state (aLoop qr qi rq (mU + rq + 1) KTH 1 ⟨S, 0, S, 0, S, 0, S, S, 0, 0⟩)
      qr qi rq mU hm hrq hμ hzU q hq (aLoop_inv cx_mul_le qr qi rq (mU + rq + 1) hm hrq hμ hz)
  · exact thetaB_encl_of_state
      (bLoop (cmr qr qi qr qi) (cmi qr qi qr qi) rq (mU + rq + 1) KTH 1
        ⟨qr, qi, S, 0, S, 0, mU + rq + 1, S, 0⟩)
      qr qi rq mU hm hrq hμ hzU q hq
      (bLoop_inv cx_mul_le qr qi rq (mU + rq + 1) hm hrq hμ hz)

end

end Work.Cert
