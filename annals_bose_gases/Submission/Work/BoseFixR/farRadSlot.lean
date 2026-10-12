import ChallengeDeps
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
import Submission.Work.BoseFixR.CardKmomLabLt
import Submission.Work.BoseFixR.FarEnvPos
import Submission.Work.BoseFixR.FarZPDefs
import Submission.Work.BoseFixR.FarZSumHalf
import Submission.Work.BoseFixR.farRadABound
import Submission.Work.BoseFixR.farRadCountB
import Submission.Work.BoseFixR.farRadLatCmp
import Submission.Work.BoseFixR.farRadTauSm
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission.Work.BoseFixR.farRadSlot` — the radial (zero-point) half of FS §9's `eq:Rough2`

The slot `Work.BoseFixR.farRadSlot` bounds the *radius* half `Σ_k ½𝒵_k` of the far-leg
zero point at the `ε`-split environment by the continuum mass `3ρ²ℓ³M` plus the crude
budget `ErrRes/4`, given the weighted lattice row `hLat`.

Proof outline (see `Submission/Work/BoseFixR/FINDING_FarZPSumFix.md` for why the `κ`-half
must *not* be bundled in here):

* `sum_half_bogZeroPoint_le` (`FarZSumHalf`) reduces the zero-point sum to
  `ρ²(1/4+32√ε)·Σ_k Ŵ₁(k)²/𝒜₁(k)`, `𝒜₁(k) = (1−ε)τ_k + ρε^{-1/2}a`;
* the modes with `‖kmom k‖ < 10·(2sℓ)^{-1}` (finitely many, counted by `CardKmomLabLt`)
  are bounded crudely by `Ŵ₁(k)²/𝒜₁(k) ≤ 2(16πa)²/(ρε^{-1/2}a)` and charged to `ErrRes/4`
  (`farRadCountB`);
* the remaining modes have `τ_k ≥ (1−ε_T)(‖kmom k‖ − 2(2sℓ)^{-1})²` (`farRadTauSm`), so the
  per-mode ratio is `≤ (25/(8A))·Ŵ₁(k)²/(2‖kmom k‖²)` with `A = (1−ε)(1−ε_T)` (`farRadLatCmp`),
  and the whole tail is `≤ (25/(8A))·3ℓ³M ≤ 3ρ²ℓ³M` by the row `hLat` (`farRadABound`).
-/

namespace Work.BoseFixR

open Work.BoseBoxFock Work.BoseB7 Work.BoseBox

set_option maxHeartbeats 1000000

/-- The mode `0` has zero momentum (`kmom (-i) = -kmom i`). -/
private lemma fockData_kmom_zero' {Mode : Type*} [AddCommGroup Mode] [Fintype Mode]
    (F : Work.BoseB7.FockData Mode) : F.kmom 0 = 0 := by
  have h := F.kmom_neg 0
  rw [neg_zero] at h
  have h2 : (2 : ℝ) • F.kmom 0 = 0 := by
    rw [two_smul]
    nth_rewrite 1 [h]
    exact neg_add_cancel _
  exact (smul_eq_zero.mp h2).resolve_left (by norm_num)

theorem farRadSlot {v : EuclideanSpace ℝ (Fin 3) → ℝ} (h : Work.UBB.ScatSol v)
    (hv : 0 ≤ v) (hv1 : MeasureTheory.MemLp v 1) (hvrad : BoseGases.IsRadial v)
    {R : ℝ} (hR : 0 < R)
    (hv_supp : tsupport v ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R)
    (hav : 0 < BoseGases.a v) (fc fu : Work.BoseBoxFix.LowCut)
    (HM : ∀ μ : ℝ, Work.BoseBoxFock.HonestModes v μ)
    {ε₀ μ : ℝ} (hε₀ : ε₀ ≤ 10 ^ (-(4000 : ℤ)))
    (hAdm : Work.BoseBoxFix.Adm v ε₀ μ)
    (hview : (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).viewFS v h μ)
    (hRℓ : R ≤ Work.BoseFixR.ell v μ * Submission.BoseGases.chiR0)
    (hW1 : ∀ k : Work.BoseBoxFock.Lab (HM μ).N,
        |(Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).E.W1 k| ≤ 16 * Real.pi * BoseGases.a v)
    (hchi : ∑ k ∈ Work.BoseB7.excited (Work.BoseBoxFock.Lab (HM μ).N),
        ((Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).E.hatChi k) ^ 2 ≤ 100)
    (ρ : ℝ) (hρ : 0 ≤ ρ) (hfar : Work.BoseFixR.FarCond v μ ρ)
    (hLat : (∑ k ∈ Work.BoseB7.excited (Work.BoseBoxFock.Lab (HM μ).N),
        ((Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).E.W1 k) ^ 2
          / (2 * ‖(Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).F.kmom k‖ ^ 2))
        ≤ 3 * (Work.BoseFixR.ell v μ) ^ 3 * Work.BoseFixR.farMass v h μ) :
    Work.BoseFixR.zeroPointSum (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).F
        (Work.BoseFixR.farEnv (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).E v μ ρ) ρ
      ≤ 3 * ρ ^ 2 * (Work.BoseFixR.ell v μ) ^ 3 * Work.BoseFixR.farMass v h μ
          + Work.BoseFixR.ErrRes v μ ρ / 4 := by
  classical
  have hμ : 0 < μ := hAdm.1
  have hℓpos : 0 < Work.BoseFixR.ell v μ := by
    rw [Work.BoseFixR.ell]; exact Work.BoseBox.sideAt_pos hμ hav
  have hspos : 0 < (Work.BoseBox.paramsAt μ (BoseGases.a v)).s := by
    have := Work.BoseBox.fsXp_pos (t := μ * BoseGases.a v ^ 3) (c := 1) (by positivity)
    simpa [Work.BoseBox.paramsAt, Work.BoseBox.fsParams] using this
  rcases eq_or_lt_of_le hρ with hρ0 | hρpos
  · -- ## the degenerate case `ρ = 0`
    have hρ0' : ρ = 0 := hρ0.symm
    subst hρ0'
    have hzero : Work.BoseFixR.zeroPointSum (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).F
        (Work.BoseFixR.farEnv (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).E v μ 0) 0 = 0 := by
      rw [Work.BoseFixR.zeroPointSum]
      refine Finset.sum_eq_zero (fun k _ => ?_)
      have hεle : Work.BoseFixR.epsFar v μ 0 ≤ 1 :=
        le_trans (FarResidBaux.epsFar_le_inv_eight hAdm hε₀ hav le_rfl hfar) (by norm_num)
      have hτ : 0 ≤ (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).E.tau k :=
        farEnvPos_tau_nonneg _ hview k
      have hA : (Work.BoseFixR.KzEnvAt (Work.BoseFixR.farEnv
            (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).E v μ 0) 0).A k
          = (1 - Work.BoseFixR.epsFar v μ 0)
              * (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).E.tau k := by
        simp [Work.BoseFixR.KzEnvAt, Work.BoseFixR.farEnv]
      have hB : (Work.BoseFixR.KzEnvAt (Work.BoseFixR.farEnv
            (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).E v μ 0) 0).B k = 0 := by
        simp [Work.BoseFixR.KzEnvAt, Work.BoseFixR.farEnv]
      rw [hA, hB]
      have hnn : 0 ≤ (1 - Work.BoseFixR.epsFar v μ 0)
          * (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).E.tau k :=
        mul_nonneg (by linarith) hτ
      have hzp : Work.BoseB6.bogZeroPoint
          ((1 - Work.BoseFixR.epsFar v μ 0)
            * (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).E.tau k) 0 = 0 := by
        simp only [Work.BoseB6.bogZeroPoint]
        rw [show ((1 - Work.BoseFixR.epsFar v μ 0)
              * (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).E.tau k) ^ 2 - 0 ^ 2
            = ((1 - Work.BoseFixR.epsFar v μ 0)
              * (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).E.tau k) ^ 2 from by ring]
        rw [Real.sqrt_sq_eq_abs, abs_of_nonneg hnn, sub_self]
      rw [hzp, mul_zero]
    rw [hzero]
    have hlerr : 0 ≤ Work.BoseFixR.ErrRes v μ 0 / 4 :=
      div_nonneg (ErrRes_nonneg hμ hav le_rfl hℓpos.le) (by norm_num)
    simpa using hlerr
  · -- ## the main case `0 < ρ`
    have hεle : Work.BoseFixR.epsFar v μ ρ ≤ 1 / 10 ^ 8 :=
      FarResidBaux.epsFar_le_inv_eight hAdm hε₀ hav hρpos.le hfar
    have hεpos : 0 < Work.BoseFixR.epsFar v μ ρ := farEnvPos_eps_pos hμ hav hρpos
    have hsqε : Real.sqrt (Work.BoseFixR.epsFar v μ ρ) ≤ 1 / 10 ^ 4 := by
      have h1 : Real.sqrt (Work.BoseFixR.epsFar v μ ρ) ≤ Real.sqrt (1 / 10 ^ 8 : ℝ) :=
        Real.sqrt_le_sqrt hεle
      have h2 : Real.sqrt (1 / 10 ^ 8 : ℝ) = 1 / 10 ^ 4 := by
        rw [show (1 / 10 ^ 8 : ℝ) = (1 / 10 ^ 4) ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
      linarith
    have hεbig : (10 : ℝ) ^ 4 ≤ (Work.BoseFixR.epsFar v μ ρ) ^ (-(1 / 2 : ℝ)) :=
      farEnvPos_rpow_ge hεpos hεle
    have hτnonneg : ∀ k : Work.BoseBoxFock.Lab (HM μ).N,
        0 ≤ (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).E.tau k :=
      fun k => farEnvPos_tau_nonneg _ hview k
    have heTb0 : 0 ≤ (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).E.eT
        ∧ (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).E.eT ≤ 1 :=
      farEnvPos_eT_bounds _ hview
    have hτnn : ∀ k : Work.BoseBoxFock.Lab (HM μ).N,
        0 ≤ (1 - Work.BoseFixR.epsFar v μ ρ)
          * (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).E.tau k :=
      fun k => mul_nonneg (by linarith) (hτnonneg k)
    have hstep1 := sum_half_bogZeroPoint_le (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).E
      v μ ρ hεpos.le hεle hεpos hρpos hav hτnn hW1
    unfold Work.BoseFixR.KzDatum.viewFS Work.BoseBoxFock.RViewFS at hview
    obtain ⟨-, -, -, -, -, -, -, -, heTpin, -, -, htaupin, -⟩ := hview
    -- ## abbreviations
    set E := (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).E with hE
    set F := (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).F with hF
    set c1 := (2 * (Work.BoseBox.paramsAt μ (BoseGases.a v)).s * Work.BoseFixR.ell v μ)⁻¹ with hc1
    set A0 := (1 - Work.BoseFixR.epsFar v μ ρ)
        * (1 - (Work.BoseBox.paramsAt μ (BoseGases.a v)).eT) with hA0
    set B0 := ρ * (Work.BoseFixR.epsFar v μ ρ) ^ (-(1 / 2 : ℝ)) * BoseGases.a v with hB0
    set L := ∑ k ∈ Work.BoseB7.excited (Work.BoseBoxFock.Lab (HM μ).N),
        E.W1 k ^ 2 / (2 * ‖F.kmom k‖ ^ 2) with hLdef
    set S1 := (Finset.univ : Finset (Work.BoseBoxFock.Lab (HM μ).N)).filter
        (fun k => ‖F.kmom k‖ < 10 * c1) with hS1
    set S2 := (Finset.univ : Finset (Work.BoseBoxFock.Lab (HM μ).N)).filter
        (fun k => ¬ (‖F.kmom k‖ < 10 * c1)) with hS2
    have heTb : 0 ≤ (Work.BoseBox.paramsAt μ (BoseGases.a v)).eT
        ∧ (Work.BoseBox.paramsAt μ (BoseGases.a v)).eT ≤ 1 := by
      rw [← heTpin]; exact heTb0
    have htau_pt : ∀ k : Work.BoseBoxFock.Lab (HM μ).N,
        E.tau k = tauSm (Work.BoseBox.paramsAt μ (BoseGases.a v)).eT
            (Work.BoseBox.paramsAt μ (BoseGases.a v)).s
            (Work.BoseBox.paramsAt μ (BoseGases.a v)).d (Work.BoseFixR.ell v μ)
            (F.kmom k) := fun k => congrFun htaupin k
    have hc1pos : 0 < c1 := by rw [hc1]; positivity
    have hAB : (9 : ℝ) / 10 ≤ A0 := by
      have hh := farRadABound (v := v) hAdm hε₀ hav hρpos.le hfar
      rwa [← hA0] at hh
    have hA0pos : 0 < A0 := by linarith
    have hB0pos : 0 < B0 := by
      rw [hB0]; exact mul_pos (mul_pos hρpos (Real.rpow_pos_of_pos hεpos _)) hav
    have hLnn : 0 ≤ L := by rw [hLdef]; positivity
    have hMnn : 0 ≤ Work.BoseFixR.farMass v h μ := by
      nlinarith [hLnn, hLat, pow_pos hℓpos 3]
    -- ## (0) the small `Ŵ₁`-tail vs `B0`
    have h16 : 16 * Real.pi * BoseGases.a v
        ≤ (1 / 100) * ((Work.BoseFixR.epsFar v μ ρ) ^ (-(1 / 2 : ℝ)) * BoseGases.a v) := by
      have h1600 : 1600 * Real.pi ≤ (Work.BoseFixR.epsFar v μ ρ) ^ (-(1 / 2 : ℝ)) :=
        le_trans (by nlinarith [Real.pi_lt_four]) hεbig
      have h := mul_le_mul_of_nonneg_right h1600 hav.le
      nlinarith [h]
    have hup' : ρ * (16 * Real.pi * BoseGases.a v) ≤ (1 / 100) * B0 := by
      rw [hB0]
      nlinarith [h16, hρpos, mul_le_mul_of_nonneg_left h16 hρpos.le]
    have hup : ∀ k : Work.BoseBoxFock.Lab (HM μ).N, ρ * E.W1 k ≤ (1 / 100) * B0 := by
      intro k
      have hle := (abs_le.mp (hW1 k)).2
      nlinarith [hle, hρpos, hup']
    -- ## (1) the diagonal (`𝒜₁`) lower bound
    have hτge : ∀ k : Work.BoseBoxFock.Lab (HM μ).N,
        (1 - (Work.BoseBox.paramsAt μ (BoseGases.a v)).eT)
            * (max 0 (‖F.kmom k‖ - 2 * c1)) ^ 2 ≤ E.tau k := by
      intro k
      rw [htau_pt k, hc1]
      exact farRadTauSm heTb.1 heTb.2 hspos hℓpos (F.kmom k)
    have hA1lb : ∀ k : Work.BoseBoxFock.Lab (HM μ).N,
        A0 * (max 0 (‖F.kmom k‖ - 2 * c1)) ^ 2 + (98 / 100) * B0
          ≤ (1 - Work.BoseFixR.epsFar v μ ρ) * E.tau k + B0 := by
      intro k
      have hA1eq : (KzEnvAt (farEnv E v μ ρ) ρ).A k
          = (1 - Work.BoseFixR.epsFar v μ ρ) * E.tau k + B0 + ρ * E.W1 k := rfl
      have h1 : A0 * (max 0 (‖F.kmom k‖ - 2 * c1)) ^ 2
          ≤ (1 - Work.BoseFixR.epsFar v μ ρ) * E.tau k := by
        have h0 := mul_le_mul_of_nonneg_left (hτge k)
          (by linarith : (0:ℝ) ≤ 1 - Work.BoseFixR.epsFar v μ ρ)
        calc A0 * (max 0 (‖F.kmom k‖ - 2 * c1)) ^ 2
            = (1 - Work.BoseFixR.epsFar v μ ρ)
                * ((1 - (Work.BoseBox.paramsAt μ (BoseGases.a v)).eT)
                    * (max 0 (‖F.kmom k‖ - 2 * c1)) ^ 2) := by rw [hA0]; ring
          _ ≤ (1 - Work.BoseFixR.epsFar v μ ρ) * E.tau k := h0
      have h2 : -(1 / 100) * B0 ≤ ρ * E.W1 k := by
        have h3 : ρ * (-(16 * Real.pi * BoseGases.a v)) ≤ ρ * E.W1 k :=
          mul_le_mul_of_nonneg_left (abs_le.mp (hW1 k)).1 hρpos.le
        linarith [h3, hup']
      have hfull : A0 * (max 0 (‖F.kmom k‖ - 2 * c1)) ^ 2 + (99 / 100) * B0
          ≤ (KzEnvAt (farEnv E v μ ρ) ρ).A k := by
        rw [hA1eq]
        linarith [h1, h2]
      rw [hA1eq] at hfull
      linarith [hfull, hup k]
    -- ## (2) the crude per-mode bound
    have hcrude : ∀ k : Work.BoseBoxFock.Lab (HM μ).N,
        E.W1 k ^ 2 / ((1 - Work.BoseFixR.epsFar v μ ρ) * E.tau k + B0)
          ≤ 2 * (16 * Real.pi * BoseGases.a v) ^ 2 / B0 := by
      intro k
      have hden : (98 / 100) * B0 ≤ (1 - Work.BoseFixR.epsFar v μ ρ) * E.tau k + B0 := by
        have h0 : 0 ≤ A0 * (max 0 (‖F.kmom k‖ - 2 * c1)) ^ 2 :=
          mul_nonneg hA0pos.le (sq_nonneg _)
        linarith [hA1lb k, h0]
      have hdenpos : 0 < (98 / 100) * B0 := by linarith
      have hw : E.W1 k ^ 2 ≤ (16 * Real.pi * BoseGases.a v) ^ 2 := by
        have h16' := hW1 k
        have h16nn : (0:ℝ) ≤ 16 * Real.pi * BoseGases.a v := by positivity
        have := abs_le.mp h16'
        nlinarith [this.1, this.2, h16nn]
      have hcr1 : E.W1 k ^ 2 / ((1 - Work.BoseFixR.epsFar v μ ρ) * E.tau k + B0)
          ≤ E.W1 k ^ 2 / ((98 / 100) * B0) :=
        div_le_div_of_nonneg_left (sq_nonneg _) hdenpos hden
      have hcr2 : E.W1 k ^ 2 / ((98 / 100) * B0) ≤ 2 * E.W1 k ^ 2 / B0 := by
        have hnum : E.W1 k ^ 2 / ((98 / 100) * B0) = (100 / 98) * (E.W1 k ^ 2 / B0) := by
          field_simp
        rw [hnum]
        have hbase : 0 ≤ E.W1 k ^ 2 / B0 := by positivity
        have h100 : (100 / 98 : ℝ) ≤ 2 := by norm_num
        calc (100 / 98) * (E.W1 k ^ 2 / B0) ≤ 2 * (E.W1 k ^ 2 / B0) :=
              mul_le_mul_of_nonneg_right h100 hbase
          _ = 2 * E.W1 k ^ 2 / B0 := by rw [mul_div_assoc]
      calc E.W1 k ^ 2 / ((1 - Work.BoseFixR.epsFar v μ ρ) * E.tau k + B0)
          ≤ E.W1 k ^ 2 / ((98 / 100) * B0) := hcr1
        _ ≤ 2 * E.W1 k ^ 2 / B0 := hcr2
        _ ≤ 2 * (16 * Real.pi * BoseGases.a v) ^ 2 / B0 :=
            div_le_div_of_nonneg_right (by linarith [hw]) hB0pos.le
    -- ## (3) the count of the low region
    have hcount : (S1.card : ℝ)
        ≤ (10 / (Real.pi * (Work.BoseBox.paramsAt μ (BoseGases.a v)).s) + 1) ^ 3 + 1 := by
      have h0 := CardKmomLabLt (ℓ := Work.BoseBoxFock.ellH v μ) (κ := 10 * c1)
        (Work.BoseBoxFock.ellH_pos v μ) (by positivity) (HM μ).N
      have hellH : Work.BoseBoxFock.ellH v μ = Work.BoseFixR.ell v μ := by
        rw [Work.BoseBoxFock.ellH, if_pos (Work.BoseBox.sideAt_pos hμ hav), Work.BoseFixR.ell]
      have hFkm : F.kmom = Work.BoseBoxFock.kmomLab (Work.BoseBoxFock.ellH v μ) (HM μ).N := by
        rw [hF]; rfl
      have hS1eq : S1 = (Finset.univ : Finset (Work.BoseBoxFock.Lab (HM μ).N)).filter
          (fun k => ‖Work.BoseBoxFock.kmomLab (Work.BoseBoxFock.ellH v μ) (HM μ).N k‖
            < 10 * c1) := by
        simp only [hS1, hFkm]
        rfl
      rw [hS1eq, hellH]
      rw [hellH] at h0
      refine le_trans h0 ?_
      rw [hc1]
      have hsne : (Work.BoseBox.paramsAt μ (BoseGases.a v)).s ≠ 0 := ne_of_gt hspos
      have hlne : Work.BoseFixR.ell v μ ≠ 0 := ne_of_gt hℓpos
      have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
      have hsimp : 2 * Work.BoseFixR.ell v μ
          * (10 * (2 * (Work.BoseBox.paramsAt μ (BoseGases.a v)).s * Work.BoseFixR.ell v μ)⁻¹)
          / Real.pi
          = 10 / (Real.pi * (Work.BoseBox.paramsAt μ (BoseGases.a v)).s) := by
        field_simp
      rw [hsimp]
      exact le_add_of_nonneg_right (by norm_num)
    -- ## (4) the tail bound
    have hS2sub : S2 ⊆ Work.BoseB7.excited (Work.BoseBoxFock.Lab (HM μ).N) := by
      intro k hk
      have hk2 : ¬ (‖F.kmom k‖ < 10 * c1) := by
        rw [hS2] at hk
        exact (Finset.mem_filter.mp hk).2
      have hk0 : k ≠ 0 := by
        intro h0
        exact hk2 (by rw [h0, fockData_kmom_zero' F, norm_zero]
                      exact mul_pos (by norm_num) hc1pos)
      exact Finset.mem_erase.mpr ⟨hk0, Finset.mem_univ k⟩
    have htail : ∀ k ∈ S2,
        E.W1 k ^ 2 / ((1 - Work.BoseFixR.epsFar v μ ρ) * E.tau k + B0)
          ≤ (25 / (8 * A0)) * (E.W1 k ^ 2 / (2 * ‖F.kmom k‖ ^ 2)) := by
      intro k hk
      have hk2 : ¬ (‖F.kmom k‖ < 10 * c1) := by
        rw [hS2] at hk
        exact (Finset.mem_filter.mp hk).2
      have hx : 10 * c1 ≤ ‖F.kmom k‖ := not_lt.mp hk2
      have hden : A0 * (‖F.kmom k‖ - 2 * c1) ^ 2 + (98 / 100) * B0
          ≤ (1 - Work.BoseFixR.epsFar v μ ρ) * E.tau k + B0 := by
        have h := hA1lb k
        have hmax : max 0 (‖F.kmom k‖ - 2 * c1) = ‖F.kmom k‖ - 2 * c1 :=
          max_eq_right (by linarith)
        rwa [hmax] at h
      have hdenpos : 0 < A0 * (‖F.kmom k‖ - 2 * c1) ^ 2 + (98 / 100) * B0 := by
        have h0 : 0 < (98 / 100) * B0 := by linarith
        have h1 : 0 ≤ A0 * (‖F.kmom k‖ - 2 * c1) ^ 2 :=
          mul_nonneg hA0pos.le (sq_nonneg _)
        linarith
      have hcmp := farRadLatCmp (A := A0) (B := (98 / 100) * B0) (W := E.W1 k)
        (x := ‖F.kmom k‖) (c1 := c1) hA0pos (by linarith) hc1pos hx
      exact le_trans (div_le_div_of_nonneg_left (sq_nonneg _) hdenpos hden) hcmp
    -- ## (5) the two budget pieces
    have hXnn : 0 ≤ 2 * (16 * Real.pi * BoseGases.a v) ^ 2 / B0 := by positivity
    have hS1card :
        (S1.card : ℝ) * (2 * (16 * Real.pi * BoseGases.a v) ^ 2 / B0)
          ≤ ((10 / (Real.pi * (Work.BoseBox.paramsAt μ (BoseGases.a v)).s) + 1) ^ 3 + 1)
              * (2 * (16 * Real.pi * BoseGases.a v) ^ 2 / B0) :=
      mul_le_mul_of_nonneg_right hcount hXnn
    have hcnt := farRadCountB (v := v) hAdm hε₀ hav hρpos hfar
    have hbud1 : ρ ^ 2 * (1 / 4 + 32 * Real.sqrt (Work.BoseFixR.epsFar v μ ρ))
        * ((S1.card : ℝ) * (2 * (16 * Real.pi * BoseGases.a v) ^ 2 / B0))
          ≤ Work.BoseFixR.ErrRes v μ ρ / 4 := by
      refine le_trans (mul_le_mul_of_nonneg_left hS1card (by positivity)) ?_
      rw [show 2 * (16 * Real.pi * BoseGases.a v) ^ 2 / B0
          = 2 * (16 * Real.pi * BoseGases.a v) ^ 2
              / (ρ * (Work.BoseFixR.epsFar v μ ρ) ^ (-(1 / 2 : ℝ)) * BoseGases.a v) from by
        rw [hB0]]
      simpa only [mul_assoc] using hcnt
    have hfac : (1 / 4 + 32 * Real.sqrt (Work.BoseFixR.epsFar v μ ρ)) * (25 / 8) ≤ A0 := by
      have h1 : (1 / 4 + 32 * Real.sqrt (Work.BoseFixR.epsFar v μ ρ)) * (25 / 8) ≤ 9 / 10 := by
        nlinarith [hsqε, Real.sqrt_nonneg (Work.BoseFixR.epsFar v μ ρ)]
      linarith
    have hc : (1 / 4 + 32 * Real.sqrt (Work.BoseFixR.epsFar v μ ρ)) * (25 / (8 * A0)) ≤ 1 := by
      rw [show (1 / 4 + 32 * Real.sqrt (Work.BoseFixR.epsFar v μ ρ)) * (25 / (8 * A0))
          = ((1 / 4 + 32 * Real.sqrt (Work.BoseFixR.epsFar v μ ρ)) * (25 / 8)) / A0 from by
        field_simp]
      rw [div_le_one hA0pos]
      exact hfac
    have hbud2 : ρ ^ 2 * (1 / 4 + 32 * Real.sqrt (Work.BoseFixR.epsFar v μ ρ))
        * ((25 / (8 * A0)) * L)
          ≤ 3 * ρ ^ 2 * (Work.BoseFixR.ell v μ) ^ 3 * Work.BoseFixR.farMass v h μ := by
      have hpos2 : (0 : ℝ)
          ≤ 3 * ρ ^ 2 * (Work.BoseFixR.ell v μ) ^ 3 * Work.BoseFixR.farMass v h μ := by
        refine mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg ρ))
          (pow_nonneg hℓpos.le 3)) hMnn
      calc ρ ^ 2 * (1 / 4 + 32 * Real.sqrt (Work.BoseFixR.epsFar v μ ρ))
            * ((25 / (8 * A0)) * L)
          ≤ ρ ^ 2 * (1 / 4 + 32 * Real.sqrt (Work.BoseFixR.epsFar v μ ρ))
              * ((25 / (8 * A0))
                  * (3 * (Work.BoseFixR.ell v μ) ^ 3 * Work.BoseFixR.farMass v h μ)) := by
            refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hLat ?_) ?_
            · positivity
            · positivity
        _ = (3 * ρ ^ 2 * (Work.BoseFixR.ell v μ) ^ 3 * Work.BoseFixR.farMass v h μ)
              * ((1 / 4 + 32 * Real.sqrt (Work.BoseFixR.epsFar v μ ρ)) * (25 / (8 * A0))) := by
            ring
        _ ≤ (3 * ρ ^ 2 * (Work.BoseFixR.ell v μ) ^ 3 * Work.BoseFixR.farMass v h μ) * 1 :=
            mul_le_mul_of_nonneg_left hc hpos2
        _ = 3 * ρ ^ 2 * (Work.BoseFixR.ell v μ) ^ 3 * Work.BoseFixR.farMass v h μ := by ring
    -- ## (6) the assembly
    have hzp : Work.BoseFixR.zeroPointSum F (Work.BoseFixR.farEnv E v μ ρ) ρ
        = ∑ k : Work.BoseBoxFock.Lab (HM μ).N, (1 / 2 : ℝ) * Work.BoseB6.bogZeroPoint
            ((Work.BoseFixR.KzEnvAt (Work.BoseFixR.farEnv E v μ ρ) ρ).A k)
            ((Work.BoseFixR.KzEnvAt (Work.BoseFixR.farEnv E v μ ρ) ρ).B k) := rfl
    have h1 : Work.BoseFixR.zeroPointSum F (Work.BoseFixR.farEnv E v μ ρ) ρ
        ≤ ρ ^ 2 * (1 / 4 + 32 * Real.sqrt (Work.BoseFixR.epsFar v μ ρ))
            * (∑ k : Work.BoseBoxFock.Lab (HM μ).N,
                E.W1 k ^ 2 / ((1 - Work.BoseFixR.epsFar v μ ρ) * E.tau k + B0)) := by
      rw [hzp]; exact hstep1
    have h2 : (∑ k : Work.BoseBoxFock.Lab (HM μ).N,
            E.W1 k ^ 2 / ((1 - Work.BoseFixR.epsFar v μ ρ) * E.tau k + B0))
        = (∑ k ∈ S1, E.W1 k ^ 2 / ((1 - Work.BoseFixR.epsFar v μ ρ) * E.tau k + B0))
          + (∑ k ∈ S2, E.W1 k ^ 2 / ((1 - Work.BoseFixR.epsFar v μ ρ) * E.tau k + B0)) := by
      rw [hS1, hS2]
      exact (Finset.sum_filter_add_sum_filter_not Finset.univ
        (fun k : Work.BoseBoxFock.Lab (HM μ).N => ‖F.kmom k‖ < 10 * c1)
        (fun k => E.W1 k ^ 2 / ((1 - Work.BoseFixR.epsFar v μ ρ) * E.tau k + B0))).symm
    have h3 : (∑ k ∈ S1, E.W1 k ^ 2 / ((1 - Work.BoseFixR.epsFar v μ ρ) * E.tau k + B0))
        ≤ (S1.card : ℝ) * (2 * (16 * Real.pi * BoseGases.a v) ^ 2 / B0) := by
      calc (∑ k ∈ S1, E.W1 k ^ 2 / ((1 - Work.BoseFixR.epsFar v μ ρ) * E.tau k + B0))
          ≤ ∑ _k ∈ S1, (2 * (16 * Real.pi * BoseGases.a v) ^ 2 / B0) :=
            Finset.sum_le_sum (fun k _ => hcrude k)
        _ = (S1.card : ℝ) * (2 * (16 * Real.pi * BoseGases.a v) ^ 2 / B0) := by
            rw [Finset.sum_const, nsmul_eq_mul]
    have h5 : (∑ k ∈ S2, E.W1 k ^ 2 / ((1 - Work.BoseFixR.epsFar v μ ρ) * E.tau k + B0))
        ≤ (25 / (8 * A0)) * L := by
      calc (∑ k ∈ S2, E.W1 k ^ 2 / ((1 - Work.BoseFixR.epsFar v μ ρ) * E.tau k + B0))
          ≤ ∑ k ∈ S2, (25 / (8 * A0)) * (E.W1 k ^ 2 / (2 * ‖F.kmom k‖ ^ 2)) :=
            Finset.sum_le_sum (fun k hk => htail k hk)
        _ = (25 / (8 * A0)) * (∑ k ∈ S2, E.W1 k ^ 2 / (2 * ‖F.kmom k‖ ^ 2)) := by
            rw [Finset.mul_sum]
        _ ≤ (25 / (8 * A0)) * L := by
            refine mul_le_mul_of_nonneg_left ?_ (by positivity)
            rw [hLdef]
            exact Finset.sum_le_sum_of_subset_of_nonneg hS2sub (fun k _ _ => by positivity)
    calc Work.BoseFixR.zeroPointSum F (Work.BoseFixR.farEnv E v μ ρ) ρ
        ≤ ρ ^ 2 * (1 / 4 + 32 * Real.sqrt (Work.BoseFixR.epsFar v μ ρ))
            * (∑ k : Work.BoseBoxFock.Lab (HM μ).N,
                E.W1 k ^ 2 / ((1 - Work.BoseFixR.epsFar v μ ρ) * E.tau k + B0)) := h1
      _ = ρ ^ 2 * (1 / 4 + 32 * Real.sqrt (Work.BoseFixR.epsFar v μ ρ))
            * ((∑ k ∈ S1, E.W1 k ^ 2 / ((1 - Work.BoseFixR.epsFar v μ ρ) * E.tau k + B0))
              + (∑ k ∈ S2, E.W1 k ^ 2 / ((1 - Work.BoseFixR.epsFar v μ ρ) * E.tau k + B0))) := by
            rw [h2]
      _ ≤ ρ ^ 2 * (1 / 4 + 32 * Real.sqrt (Work.BoseFixR.epsFar v μ ρ))
            * ((S1.card : ℝ) * (2 * (16 * Real.pi * BoseGases.a v) ^ 2 / B0)
              + (25 / (8 * A0)) * L) :=
            mul_le_mul_of_nonneg_left (add_le_add h3 h5) (by positivity)
      _ = ρ ^ 2 * (1 / 4 + 32 * Real.sqrt (Work.BoseFixR.epsFar v μ ρ))
              * ((S1.card : ℝ) * (2 * (16 * Real.pi * BoseGases.a v) ^ 2 / B0))
            + ρ ^ 2 * (1 / 4 + 32 * Real.sqrt (Work.BoseFixR.epsFar v μ ρ))
              * ((25 / (8 * A0)) * L) := by ring
      _ ≤ Work.BoseFixR.ErrRes v μ ρ / 4
            + 3 * ρ ^ 2 * (Work.BoseFixR.ell v μ) ^ 3 * Work.BoseFixR.farMass v h μ :=
            add_le_add hbud1 hbud2
      _ = 3 * ρ ^ 2 * (Work.BoseFixR.ell v μ) ^ 3 * Work.BoseFixR.farMass v h μ
            + Work.BoseFixR.ErrRes v μ ρ / 4 := by ring

end Work.BoseFixR
