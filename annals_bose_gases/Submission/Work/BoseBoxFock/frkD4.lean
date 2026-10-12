import ChallengeDeps
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Submission.Work.BoseBoxFock.boxSlotSum_smul_finset_sum
import Submission.Work.BoseBoxFock.frkD4Aux
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.frkD4` — the dictionary `D4` of the FRK route

The dictionary `Work.BoseBoxFock.FRK.FormRowKin4_of_oneBody4`: from the per-fibre one-body
inequality `OBineq4` (at the honest parameters) conclude the box-level kinetic row
`FormRowKin4`.

The proof is the slot/fibre dictionary of FS `prop:Hamilton2ndQuant`:

* `AVgen_kinOnly` expands the kinetic-only `AVgen` into its three rows;
* `rowGood_boxSlotSum` + `star_mul_integrableOn_abox` make the three pieces integrable on the
  compact box, so the real part of the integral splits;
* the `τ̃`-row is `boxSlotSum_rankOne_re_le_fibre` (the slot/fibre dictionary of the rank-one
  slot) followed by `indU_kinFT_winState_fibre_sum_swap` (the finite sum/integral exchange);
* the gap row is `re_boxSlotSum_boxT0_le_cnPlusC` + `cnPlusC_boxRestrictC_eq_cnPlus` +
  `bf3a_cnplus`;
* the `η_H` row is the honest decomposition `NH = (1/32)Σ η_H a†a` (`HonestBoxFam_NH_eq`,
  `dGamma_injective`, `boxSlotSum_smul_finset_sum`) followed by the same two steps;
* `kinGroup_slotSum_le` integrates the fibre inequality into `kinFormB` minus its reserves.
-/

noncomputable section

open MeasureTheory
open scoped BigOperators

namespace Work.BoseBoxFock

local notation "Ω" => EuclideanSpace ℝ (Fin 3)

set_option linter.unusedVariables false
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.style.haveILetI false

/-! ## 1. The `SlotGood` calculus of star and real scalar multiples -/

/-- The pointwise product of two good states is good. -/
theorem slotGood_mul {ι : Type*} {X Y : (ι → Ω) → ℂ} (hX : SlotGood X) (hY : SlotGood Y) :
    SlotGood (X * Y) := by
  obtain ⟨hXm, CX, hCX⟩ := hX
  obtain ⟨hYm, CY, hCY⟩ := hY
  refine ⟨hXm.mul hYm, CX * CY, fun x => ?_⟩
  rw [Pi.mul_apply, norm_mul]
  exact mul_le_mul (hCX x) (hCY x) (norm_nonneg _) (le_trans (norm_nonneg _) (hCX x))

/-- The pointwise conjugate of a good state is good. -/
theorem slotGood_star {ι : Type*} {X : (ι → Ω) → ℂ} (hX : SlotGood X) :
    SlotGood (fun x => star (X x)) := by
  obtain ⟨hm, C, hC⟩ := hX
  exact ⟨continuous_star.measurable.comp hm, C, fun x => by
    rw [norm_star]; exact hC x⟩

/-- A real scalar multiple of a good state is good. -/
theorem slotGood_real_smul {ι : Type*} (c : ℝ) {X : (ι → Ω) → ℂ} (hX : SlotGood X) :
    SlotGood (c • X) := by
  obtain ⟨hm, C, hC⟩ := hX
  refine ⟨measurable_const.smul hm, max (‖c‖ * C) 0, fun x => ?_⟩
  rw [Pi.smul_apply, norm_smul]
  exact le_trans (mul_le_mul_of_nonneg_left (hC x) (norm_nonneg c)) (le_max_left _ _)

/-- A finite sum of good states, in the lambda spelling. -/
theorem slotGood_finset_sum_pointwise {ι κ : Type*} (s : Finset κ)
    {X : κ → (ι → Ω) → ℂ} (h : ∀ i, SlotGood (X i)) :
    SlotGood (fun x => ∑ i ∈ s, X i x) := by
  have h1 : SlotGood (∑ i ∈ s, X i) := SlotGood.finset_sum s h
  have he : (fun x => ∑ i ∈ s, X i x) = ∑ i ∈ s, X i := by
    funext x; rw [Finset.sum_apply]
  rw [he]; exact h1

/-! ## 2. The aggregation of the mode sums over the slots -/

/-- The finite-sum aggregation of one row of the kinetic group: summing the slot integrals over
the lattice and then over the particle slots is the same as summing over the slots first, with the
mode weight pulled inside the integral. -/
theorem sum_weight_fibre_aggregate {N n : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) (w : Lab N → ℝ)
    {Φ : Submission.BoseGases.X n → ℝ} (hΦ : ContDiff ℝ (⊤ : ℕ∞) Φ) :
    (∑ k : Lab N, w k * (∑ j : Fin n, (ℓ ^ 3)⁻¹ * ∫ x in Submission.BoseGases.abox n ℓ,
        Work.BoseKinLoc.indU ℓ 0 (x j) * ((ℓ ^ 3)⁻¹ * ‖Submission.BoseGases.kinFT
          (winState ℓ (Work.BoseKinLoc.fibre n j Φ x)) (kmomLab ℓ N k)‖ ^ 2)))
      = ∑ j : Fin n, (ℓ ^ 3)⁻¹ * ∫ x in Submission.BoseGases.abox n ℓ,
          Work.BoseKinLoc.indU ℓ 0 (x j) * (∑ k : Lab N, w k * ((ℓ ^ 3)⁻¹
            * ‖Submission.BoseGases.kinFT (winState ℓ (Work.BoseKinLoc.fibre n j Φ x))
                (kmomLab ℓ N k)‖ ^ 2)) := by
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  have h1 : (∑ k : Lab N, w k * ((ℓ ^ 3)⁻¹ * ∫ x in Submission.BoseGases.abox n ℓ,
        Work.BoseKinLoc.indU ℓ 0 (x j) * ((ℓ ^ 3)⁻¹ * ‖Submission.BoseGases.kinFT
          (winState ℓ (Work.BoseKinLoc.fibre n j Φ x)) (kmomLab ℓ N k)‖ ^ 2)))
      = (ℓ ^ 3)⁻¹ * ∑ k : Lab N, w k * ∫ x in Submission.BoseGases.abox n ℓ,
        Work.BoseKinLoc.indU ℓ 0 (x j) * ((ℓ ^ 3)⁻¹ * ‖Submission.BoseGases.kinFT
          (winState ℓ (Work.BoseKinLoc.fibre n j Φ x)) (kmomLab ℓ N k)‖ ^ 2) := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun k _ => by ring)
  rw [h1, indU_kinFT_winState_fibre_sum_swap hℓ j hΦ w]
  simp only [Finset.mul_sum]

/-! ## 3. The dictionary `D4` -/

/-- **The dictionary `D4` of the FRK route**: from the per-fibre one-body kinetic inequality
`OBineq4` (at the honest parameters) conclude the box-level kinetic row `FormRowKin4`. -/
theorem FRK.FormRowKin4_of_oneBody4 (v : ℝ³ → ℝ) (h : Work.UBB.ScatSol v)
    (fc fu : Work.BoseBoxFix.LowCut) (R J : ℝ) (Nmin : ℝ → ℕ) (ε₀ : ℝ)
    (hOB : ∀ μ : ℝ, Work.BoseBoxFix.Adm v ε₀ μ → ∀ (N : ℕ) (ψ : Ω → ℝ),
      ContDiff ℝ (⊤ : ℕ∞) ψ →
      FRK.OBineq4 (Work.BoseBox.sideAt μ (BoseGases.a v))
        (Work.BoseBox.paramsAt μ (BoseGases.a v)).s
        (Work.BoseBox.paramsAt μ (BoseGases.a v)).d
        (Work.BoseBox.paramsAt μ (BoseGases.a v)).eT
        (Work.BoseBox.paramsAt μ (BoseGases.a v)).b (FRK.kappaHon v μ) fu N ψ) :
    FRK.FormRowKin4 v h fc fu R J Nmin ε₀ 0 := by
  intro HM hNmin μ
  set ℓ : ℝ := Work.BoseBox.sideAt μ (BoseGases.a v) with hℓdef
  set P : Work.BoseBox.FSParams := Work.BoseBox.paramsAt μ (BoseGases.a v) with hPdef
  intro hAdm hKB n Φ hn hnorm hlow hspec
  intro e hmeas hbdd hsupp horth hint hemem hpin hf hg hθ T_NH hNH
  set N : ℕ := (HM μ).N with hNdef
  set E : Work.BoseB7.Q3Env (Lab N) := (HonestBoxFam v h fc fu HM μ).E with hEdef
  -- ## 0. the parameter facts
  have ht : 0 < μ * (BoseGases.a v) ^ 3 := AdmGate.paramsOK_fsParams_pos hAdm.2.2
  have hav : 0 < BoseGases.a v := by
    have h3 : 0 < (BoseGases.a v) ^ 3 := pos_of_mul_pos_right ht hAdm.1.le
    exact (show Odd 3 by norm_num).pow_pos_iff.mp (by simpa using h3)
  obtain ⟨hℓ0, hspos0, hdpos0, hd10, heT00, heT10, hbpos0⟩ := adm_param_facts v hav hAdm
  have hℓ : 0 < ℓ := hℓ0
  have hspos : 0 < P.s := hspos0
  have hdpos : 0 < P.d := hdpos0
  have hd1 : P.d ≤ 1 := hd10
  have heT0 : 0 ≤ P.eT := heT00
  have heT1 : P.eT ≤ 1 := heT10
  have hbpos : 0 < P.b := hbpos0
  -- ## 1. the pinning of the lattice modes
  have hmemQ : ∀ k : Lab (HM μ).N,
      MemLp (Work.BoseK15.corpusBox.qVec (ellH v μ) (kmomLab (ellH v μ) (HM μ).N k)) 2
        (volume : Measure Ω) := by
    intro k
    rw [ellH_eq_sideAt_asm hℓ]
    exact (memLp_modes ℓ hℓ).1 (kmomLab ℓ N k)
  have hq : ∀ k : Lab N, Work.BoseK15.corpusBox.qVec ℓ (kmomLab ℓ N k)
      =ᵐ[(volume : Measure Ω)] fun x =>
        ((Real.sqrt (ℓ ^ 3) : ℝ) : ℂ) * Work.BoseDict.etaOf e ((HM μ).f k) x := by
    intro k
    have hmemE : ∀ l : Fin (HM μ).m, MemLp (e l) 2 (volume : Measure Ω) :=
      memLp_modes_two hmeas hbdd hsupp
    have hpair : ∀ (k' : Lab (HM μ).N) (l : Fin (HM μ).m),
        (∫ x : Ω, (starRingEnd ℂ) (e l x) * Work.BoseK15.corpusBox.qVec (ellH v μ)
            (kmomLab (ellH v μ) (HM μ).N k') x)
          = (((ellH v μ) ^ (3 / 2 : ℝ) * (HM μ).f k' l : ℝ) : ℂ) := by
      intro k' l
      rw [ellH_eq_sideAt_asm hℓ]
      simpa only [starRingEnd_apply] using hf k' l
    have horthE : ∀ l l', (∫ x : Ω, (starRingEnd ℂ) (e l x) * e l' x)
        = if l = l' then 1 else 0 := by
      intro l l'
      simpa only [starRingEnd_apply] using horth l l'
    have h := qVec_eq_etaOf_of_pairing v μ (HM μ) e horthE hpair hmemE hmemQ k
    rw [ellH_eq_sideAt_asm hℓ] at h
    exact h
  -- ## 2. the box restriction
  have hFold : (fun x : Submission.BoseGases.X n => ((Φ x : ℝ) : ℂ)
      * (Submission.BoseGases.abox n ℓ).indicator (fun _ => (1 : ℝ)) x)
      = boxRestrictC ℓ Φ := rfl
  obtain ⟨hΘcm, hΘcb, -, -, -⟩ := boxRestrictState hℓ Φ
  have hΘm : Measurable (boxRestrictC ℓ Φ) := hFold ▸ hΘcm
  have hΘb : ∃ C : ℝ, ∀ x, ‖boxRestrictC ℓ Φ x‖ ≤ C := hFold ▸ hΘcb
  have hΘzero : ∀ x, x ∉ Submission.BoseGases.abox n ℓ → boxRestrictC ℓ Φ x = 0 := by
    intro x hx
    rw [← hFold]
    beta_reduce
    rw [Set.indicator_of_notMem hx]
    simp
  have hΘsupp : Function.support (boxRestrictC ℓ Φ) ⊆ Submission.BoseGases.abox n ℓ := by
    intro x hx
    by_contra hxnot
    exact hx (hΘzero x hxnot)
  have hgood : SlotGood (boxRestrictC ℓ Φ) := ⟨hΘm, hΘb⟩
  -- ## 3. the three row integrands
  set F1 : Submission.BoseGases.X n → ℂ := fun x => star (boxRestrictC ℓ Φ x)
      * (∑ k : Lab N, E.tau k
        • Work.BoseDict.boxSlotSum e (rankOne ((HM μ).f k)) (boxRestrictC ℓ Φ) x) with hF1def
  set F2 : Submission.BoseGases.X n → ℂ := fun x => ((E.b / (2 * E.ell ^ 2) : ℝ) : ℂ)
      * (star (boxRestrictC ℓ Φ x)
        * Work.BoseDict.boxSlotSum e (boxT0 (HM μ).m) (boxRestrictC ℓ Φ) x) with hF2def
  set F3 : Submission.BoseGases.X n → ℂ := fun x =>
      ((E.eT * E.b / (2 * E.d ^ 2 * E.ell ^ 2) : ℝ) : ℂ)
      * (star (boxRestrictC ℓ Φ x)
        * Work.BoseDict.boxSlotSum e T_NH (boxRestrictC ℓ Φ) x) with hF3def
  have hBA : SlotGood (fun x : Submission.BoseGases.X n =>
      ∑ k : Lab N, E.tau k
        • Work.BoseDict.boxSlotSum e (rankOne ((HM μ).f k)) (boxRestrictC ℓ Φ) x) :=
    slotGood_finset_sum_pointwise Finset.univ (fun k =>
      slotGood_real_smul (E.tau k) (slotGood_boxSlotSum hmeas hbdd hsupp _ hgood))
  have hBG : SlotGood (Work.BoseDict.boxSlotSum e (boxT0 (HM μ).m) (boxRestrictC ℓ Φ)) :=
    slotGood_boxSlotSum hmeas hbdd hsupp _ hgood
  have hBH : SlotGood (Work.BoseDict.boxSlotSum e T_NH (boxRestrictC ℓ Φ)) :=
    slotGood_boxSlotSum hmeas hbdd hsupp _ hgood
  have hInt1 : MeasureTheory.IntegrableOn F1 (Submission.BoseGases.abox n ℓ) :=
    star_mul_integrableOn_abox hℓ.le hgood hBA
  have hInt2 : MeasureTheory.IntegrableOn F2 (Submission.BoseGases.abox n ℓ) :=
    (star_mul_integrableOn_abox hℓ.le hgood hBG).const_mul _
  have hInt3 : MeasureTheory.IntegrableOn F3 (Submission.BoseGases.abox n ℓ) :=
    (star_mul_integrableOn_abox hℓ.le hgood hBH).const_mul _
  -- ## 4. the pointwise expansion of the kinetic group
  have hpt : (fun x : Submission.BoseGases.X n =>
        star (boxRestrictC ℓ Φ x)
          * AVgen (fun T => Work.BoseDict.boxSlotSum e T)
              (id : (Work.BoseDict.Xn n → ℂ) → (Work.BoseDict.Xn n → ℂ))
              (HM μ).f (HM μ).g T_NH (∅ : Finset (Lab N)) (kinOnlyEnv E) 0
              (boxRestrictC ℓ Φ) x)
      = fun x => F1 x + F2 x + F3 x := by
    have h1 : ∀ x : Submission.BoseGases.X n, star (boxRestrictC ℓ Φ x)
          * ((E.b / (2 * E.ell ^ 2))
            • (Work.BoseDict.boxSlotSum e (boxT0 (HM μ).m) (boxRestrictC ℓ Φ) x))
        = ((E.b / (2 * E.ell ^ 2) : ℝ) : ℂ) * (star (boxRestrictC ℓ Φ x)
          * (Work.BoseDict.boxSlotSum e (boxT0 (HM μ).m) (boxRestrictC ℓ Φ) x)) := by
      intro x
      rw [Complex.real_smul]
      simp only [Complex.ofReal_mul, Complex.ofReal_inv, Complex.ofReal_pow, Complex.ofReal_div,
        Complex.ofReal_one, Complex.ofReal_ofNat]
      ring
    have h2 : ∀ x : Submission.BoseGases.X n, star (boxRestrictC ℓ Φ x)
          * ((E.eT * E.b / (2 * E.d ^ 2 * E.ell ^ 2))
            • (Work.BoseDict.boxSlotSum e T_NH (boxRestrictC ℓ Φ) x))
        = ((E.eT * E.b / (2 * E.d ^ 2 * E.ell ^ 2) : ℝ) : ℂ) * (star (boxRestrictC ℓ Φ x)
          * (Work.BoseDict.boxSlotSum e T_NH (boxRestrictC ℓ Φ) x)) := by
      intro x
      rw [Complex.real_smul]
      simp only [Complex.ofReal_mul, Complex.ofReal_inv, Complex.ofReal_pow, Complex.ofReal_div,
        Complex.ofReal_one, Complex.ofReal_ofNat]
      ring
    funext x
    rw [AVgen_kinOnly]
    simp only [Finset.sum_apply, Pi.add_apply, Pi.smul_apply, hF1def, hF2def, hF3def]
    rw [mul_add, mul_add, h1 x, h2 x]
  -- ## 5. the split of the left side
  have hkey : (∫ x in Submission.BoseGases.abox n ℓ, F1 x + F2 x + F3 x)
      = (∫ x in Submission.BoseGases.abox n ℓ, F1 x)
        + (∫ x in Submission.BoseGases.abox n ℓ, F2 x)
        + (∫ x in Submission.BoseGases.abox n ℓ, F3 x) := by
    have e1 : (∫ x in Submission.BoseGases.abox n ℓ, F1 x + F2 x + F3 x)
        = (∫ x in Submission.BoseGases.abox n ℓ, F1 x + F2 x)
          + (∫ x in Submission.BoseGases.abox n ℓ, F3 x) := by
      rw [show (∫ x in Submission.BoseGases.abox n ℓ, F1 x + F2 x + F3 x)
          = (∫ x in Submission.BoseGases.abox n ℓ, (F1 + F2) x + F3 x) from rfl]
      exact MeasureTheory.integral_add (hInt1.add hInt2) hInt3
    have e2 : (∫ x in Submission.BoseGases.abox n ℓ, F1 x + F2 x)
        = (∫ x in Submission.BoseGases.abox n ℓ, F1 x)
          + (∫ x in Submission.BoseGases.abox n ℓ, F2 x) := by
      rw [show (∫ x in Submission.BoseGases.abox n ℓ, F1 x + F2 x)
          = (∫ x in Submission.BoseGases.abox n ℓ, (F1 + F2) x) from rfl]
      exact MeasureTheory.integral_add hInt1 hInt2
    rw [e1, e2]
  have hsplit : (∫ x in Submission.BoseGases.abox n ℓ, star (boxRestrictC ℓ Φ x)
        * AVgen (fun T => Work.BoseDict.boxSlotSum e T)
            (id : (Work.BoseDict.Xn n → ℂ) → (Work.BoseDict.Xn n → ℂ))
            (HM μ).f (HM μ).g T_NH (∅ : Finset (Lab N)) (kinOnlyEnv E) 0
            (boxRestrictC ℓ Φ) x).re
      = (∫ x in Submission.BoseGases.abox n ℓ, F1 x).re
        + (∫ x in Submission.BoseGases.abox n ℓ, F2 x).re
        + (∫ x in Submission.BoseGases.abox n ℓ, F3 x).re := by
    rw [hpt]
    rw [show (∫ x in Submission.BoseGases.abox n ℓ, (fun x => F1 x + F2 x + F3 x) x).re
        = (∫ x in Submission.BoseGases.abox n ℓ, F1 x + F2 x + F3 x).re from rfl]
    rw [hkey]
    simp only [Complex.add_re]
  -- ## 6. the `τ̃` row
  have hτrow : (∫ x in Submission.BoseGases.abox n ℓ, F1 x).re
      ≤ ∑ j : Fin n, (ℓ ^ 3)⁻¹ * ∫ x in Submission.BoseGases.abox n ℓ,
          Work.BoseKinLoc.indU ℓ 0 (x j) * kinTauLat N P.eT P.s P.d ℓ
            (Work.BoseKinLoc.fibre n j Φ x) := by
    have hEtau : ∀ k : Lab N, E.tau k = tauSm P.eT P.s P.d ℓ (kmomLab ℓ N k) :=
      fun k => honest_E_tau v h fc fu HM μ hℓ k
    have hmod : ∀ k : Lab N, (∫ x in Submission.BoseGases.abox n ℓ,
          star (boxRestrictC ℓ Φ x)
            * Work.BoseDict.boxSlotSum e (rankOne ((HM μ).f k)) (boxRestrictC ℓ Φ) x).re
        ≤ ∑ j : Fin n, (ℓ ^ 3)⁻¹ * ∫ x in Submission.BoseGases.abox n ℓ,
            Work.BoseKinLoc.indU ℓ 0 (x j) * ((ℓ ^ 3)⁻¹ * ‖Submission.BoseGases.kinFT
              (winState ℓ (Work.BoseKinLoc.fibre n j Φ x)) (kmomLab ℓ N k)‖ ^ 2) :=
      fun k => boxSlotSum_rankOne_re_le_fibre (n := n) (N := N) hℓ hmeas hbdd hsupp hq
        Φ.contDiff k
    have hsum : (∫ x in Submission.BoseGases.abox n ℓ, F1 x).re
        = ∑ k : Lab N, E.tau k * (∫ x in Submission.BoseGases.abox n ℓ,
            star (boxRestrictC ℓ Φ x)
              * Work.BoseDict.boxSlotSum e (rankOne ((HM μ).f k)) (boxRestrictC ℓ Φ) x).re := by
      have hp : F1 = fun x : Submission.BoseGases.X n => ∑ k : Lab N, (E.tau k : ℂ)
          * (star (boxRestrictC ℓ Φ x)
            * Work.BoseDict.boxSlotSum e (rankOne ((HM μ).f k)) (boxRestrictC ℓ Φ) x) := by
        simp only [hF1def]
        funext x
        simp only [Finset.mul_sum, Complex.real_smul]
        exact Finset.sum_congr rfl (fun k _ => by ring)
      rw [hp]
      have hsum2 : (∫ x in Submission.BoseGases.abox n ℓ, ∑ k : Lab N, (E.tau k : ℂ)
            * (star (boxRestrictC ℓ Φ x)
              * Work.BoseDict.boxSlotSum e (rankOne ((HM μ).f k)) (boxRestrictC ℓ Φ) x))
          = ∑ k : Lab N, ∫ x in Submission.BoseGases.abox n ℓ, (E.tau k : ℂ)
            * (star (boxRestrictC ℓ Φ x)
              * Work.BoseDict.boxSlotSum e (rankOne ((HM μ).f k)) (boxRestrictC ℓ Φ) x) :=
        MeasureTheory.integral_finsetSum Finset.univ (fun k _ =>
          (star_mul_integrableOn_abox hℓ.le hgood
            (slotGood_boxSlotSum hmeas hbdd hsupp _ hgood)).const_mul _)
      rw [hsum2, Complex.re_sum]
      refine Finset.sum_congr rfl (fun k _ => ?_)
      rw [MeasureTheory.integral_const_mul]
      simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
    rw [hsum]
    calc ∑ k : Lab N, E.tau k * (∫ x in Submission.BoseGases.abox n ℓ,
          star (boxRestrictC ℓ Φ x)
            * Work.BoseDict.boxSlotSum e (rankOne ((HM μ).f k)) (boxRestrictC ℓ Φ) x).re
        ≤ ∑ k : Lab N, tauSm P.eT P.s P.d ℓ (kmomLab ℓ N k) * (∑ j : Fin n, (ℓ ^ 3)⁻¹
            * ∫ x in Submission.BoseGases.abox n ℓ, Work.BoseKinLoc.indU ℓ 0 (x j)
              * ((ℓ ^ 3)⁻¹ * ‖Submission.BoseGases.kinFT
                  (winState ℓ (Work.BoseKinLoc.fibre n j Φ x)) (kmomLab ℓ N k)‖ ^ 2)) := by
          refine Finset.sum_le_sum (fun k _ => ?_)
          rw [hEtau k]
          exact mul_le_mul_of_nonneg_left (hmod k) (tauSm_nonneg P.eT P.s P.d ℓ heT0 heT1 _)
      _ = ∑ j : Fin n, (ℓ ^ 3)⁻¹ * ∫ x in Submission.BoseGases.abox n ℓ,
            Work.BoseKinLoc.indU ℓ 0 (x j) * kinTauLat N P.eT P.s P.d ℓ
              (Work.BoseKinLoc.fibre n j Φ x) := by
          rw [sum_weight_fibre_aggregate hℓ
            (fun k => tauSm P.eT P.s P.d ℓ (kmomLab ℓ N k)) Φ.contDiff]
          refine Finset.sum_congr rfl (fun j _ => ?_)
          simp only [kinTauLat]
  -- ## 7. the gap row
  have hgaprow : (∫ x in Submission.BoseGases.abox n ℓ, F2 x).re
      ≤ ∑ j : Fin n, (ℓ ^ 3)⁻¹ * ∫ x in Submission.BoseGases.abox n ℓ,
          Work.BoseKinLoc.indU ℓ 0 (x j)
            * (P.b / (2 * ℓ ^ 2)
              * Work.BoseKinLoc.gapBare ℓ 0 (Work.BoseKinLoc.fibre n j Φ x)) := by
    simp only [hF2def]
    rw [MeasureTheory.integral_const_mul]
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
    have hc : 0 ≤ E.b / (2 * E.ell ^ 2) := by
      rw [honest_E_b, honest_E_ell]
      exact div_nonneg hbpos.le (by positivity)
    have h1 : (∫ x in Submission.BoseGases.abox n ℓ,
          star (boxRestrictC ℓ Φ x)
            * Work.BoseDict.boxSlotSum e (boxT0 (HM μ).m) (boxRestrictC ℓ Φ) x).re
        ≤ Work.BoseBoxFock.cnPlusC ℓ (boxRestrictC ℓ Φ) := by
      rw [setIntegral_re_complex_xn (Submission.BoseGases.abox n ℓ)
        (fun x : Submission.BoseGases.X n => star (boxRestrictC ℓ Φ x)
          * Work.BoseDict.boxSlotSum e (boxT0 (HM μ).m) (boxRestrictC ℓ Φ) x)
        (star_mul_integrableOn_abox hℓ.le hgood hBG)]
      exact re_boxSlotSum_boxT0_le_cnPlusC hℓ hmeas hbdd hsupp horth hint hpin hΘm hΘb hΘsupp
    have h3 : Submission.BoseGases.cnPlus ℓ (Φ : Submission.BoseGases.X n → ℝ)
        = (ℓ ^ 3)⁻¹ * ∑ j : Fin n, ∫ x in Submission.BoseGases.abox n ℓ,
            Work.BoseKinLoc.indU ℓ 0 (x j)
              * Work.BoseKinLoc.gapBare ℓ 0 (Work.BoseKinLoc.fibre n j Φ x) := by
      rw [bf3a_cnplus hℓ Φ.contDiff, ← mul_assoc,
        inv_mul_cancel₀ (by positivity : (ℓ : ℝ) ^ 3 ≠ 0), one_mul]
    calc (E.b / (2 * E.ell ^ 2)) * (∫ x in Submission.BoseGases.abox n ℓ,
          star (boxRestrictC ℓ Φ x)
            * Work.BoseDict.boxSlotSum e (boxT0 (HM μ).m) (boxRestrictC ℓ Φ) x).re
        ≤ (E.b / (2 * E.ell ^ 2)) * Work.BoseBoxFock.cnPlusC ℓ (boxRestrictC ℓ Φ) :=
          mul_le_mul_of_nonneg_left h1 hc
      _ = (E.b / (2 * E.ell ^ 2)) * Submission.BoseGases.cnPlus ℓ (Φ : Submission.BoseGases.X n → ℝ) := by
          rw [cnPlusC_boxRestrictC_eq_cnPlus hℓ Φ]
      _ = (E.b / (2 * E.ell ^ 2)) * ((ℓ ^ 3)⁻¹ * ∑ j : Fin n,
            ∫ x in Submission.BoseGases.abox n ℓ, Work.BoseKinLoc.indU ℓ 0 (x j)
              * Work.BoseKinLoc.gapBare ℓ 0 (Work.BoseKinLoc.fibre n j Φ x)) := by rw [h3]
      _ = ∑ j : Fin n, (ℓ ^ 3)⁻¹ * ∫ x in Submission.BoseGases.abox n ℓ,
            Work.BoseKinLoc.indU ℓ 0 (x j)
              * (P.b / (2 * ℓ ^ 2)
                * Work.BoseKinLoc.gapBare ℓ 0 (Work.BoseKinLoc.fibre n j Φ x)) := by
          have hc : E.b / (2 * E.ell ^ 2) = P.b / (2 * ℓ ^ 2) := by
            rw [honest_E_b, honest_E_ell, ← hℓdef]
          rw [hc, ← mul_assoc, Finset.mul_sum]
          refine Finset.sum_congr rfl (fun j _ => ?_)
          have hBj : (∫ x in Submission.BoseGases.abox n ℓ, Work.BoseKinLoc.indU ℓ 0 (x j)
                * (P.b / (2 * ℓ ^ 2)
                  * Work.BoseKinLoc.gapBare ℓ 0 (Work.BoseKinLoc.fibre n j Φ x)))
              = (P.b / (2 * ℓ ^ 2)) * (∫ x in Submission.BoseGases.abox n ℓ,
                  Work.BoseKinLoc.indU ℓ 0 (x j)
                    * Work.BoseKinLoc.gapBare ℓ 0 (Work.BoseKinLoc.fibre n j Φ x)) := by
            rw [show (fun x : Submission.BoseGases.X n => Work.BoseKinLoc.indU ℓ 0 (x j)
                  * (P.b / (2 * ℓ ^ 2)
                    * Work.BoseKinLoc.gapBare ℓ 0 (Work.BoseKinLoc.fibre n j Φ x)))
                = fun x : Submission.BoseGases.X n => (P.b / (2 * ℓ ^ 2))
                  * (Work.BoseKinLoc.indU ℓ 0 (x j)
                    * Work.BoseKinLoc.gapBare ℓ 0 (Work.BoseKinLoc.fibre n j Φ x)) from by
              funext x; ring]
            rw [MeasureTheory.integral_const_mul]
          rw [hBj]
          ring
  -- ## 8. the `η_H` row
  have hηrow : (∫ x in Submission.BoseGases.abox n ℓ, F3 x).re
      ≤ ∑ j : Fin n, (ℓ ^ 3)⁻¹ * ∫ x in Submission.BoseGases.abox n ℓ,
          Work.BoseKinLoc.indU ℓ 0 (x j)
            * (P.eT * P.b / (2 * P.d ^ 2 * ℓ ^ 2)
              * ((1 / 32 : ℝ) * kinEtaLat N fu (FRK.kappaHon v μ) ℓ
                  (Work.BoseKinLoc.fibre n j Φ x))) := by
    simp only [hF3def]
    rw [MeasureTheory.integral_const_mul]
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
    -- the honest decomposition of `T_NH`
    have hTNH : T_NH = (1 / 32 : ℝ) • ∑ k ∈ Work.BoseB7.excited (Lab N),
        etaH fu (FRK.kappaHon v μ) (kmomLab ℓ N k) • rankOne ((HM μ).f k) := by
      have h2 : (HonestBoxFam v h fc fu HM μ).T.NH
          = Work.BoseB4.dGamma (HM μ).m ((1 / 32 : ℝ) • ∑ k ∈ Work.BoseB7.excited (Lab (HM μ).N),
              etaH fu (FRK.kappaHon v μ) (kmomLab (ellH v μ) (HM μ).N k)
                • rankOnePair ((HM μ).f k) ((HM μ).f k)) := HonestBoxFam_NH_eq v h fc fu HM μ
      rw [hNH] at h2
      have hcongr : ((1 / 32 : ℝ) • ∑ k ∈ Work.BoseB7.excited (Lab (HM μ).N),
              etaH fu (FRK.kappaHon v μ) (kmomLab (ellH v μ) (HM μ).N k)
                • rankOnePair ((HM μ).f k) ((HM μ).f k))
          = ((1 / 32 : ℝ) • ∑ k ∈ Work.BoseB7.excited (Lab N),
              etaH fu (FRK.kappaHon v μ) (kmomLab ℓ N k) • rankOne ((HM μ).f k)) := by
        congr 1
        refine Finset.sum_congr rfl (fun k _ => congrArg₂ (· • ·) ?_ ?_)
        · rw [ellH_eq_sideAt_asm hℓ]
        · rw [← rankOne_eq_rankOnePair]
      rw [hcongr] at h2
      exact dGamma_injective h2
    have hBoxSum : Work.BoseDict.boxSlotSum e T_NH (boxRestrictC ℓ Φ)
        = (1 / 32 : ℝ) • ∑ k ∈ Work.BoseB7.excited (Lab N),
            etaH fu (FRK.kappaHon v μ) (kmomLab ℓ N k)
              • Work.BoseDict.boxSlotSum e (rankOne ((HM μ).f k)) (boxRestrictC ℓ Φ) := by
      rw [hTNH, boxSlotSum_smul_finset_sum]
    have hBox : (∫ x in Submission.BoseGases.abox n ℓ,
          star (boxRestrictC ℓ Φ x)
            * Work.BoseDict.boxSlotSum e T_NH (boxRestrictC ℓ Φ) x).re
        = (1 / 32 : ℝ) * ∑ k ∈ Work.BoseB7.excited (Lab N),
            etaH fu (FRK.kappaHon v μ) (kmomLab ℓ N k)
              * (∫ x in Submission.BoseGases.abox n ℓ, star (boxRestrictC ℓ Φ x)
                  * Work.BoseDict.boxSlotSum e (rankOne ((HM μ).f k)) (boxRestrictC ℓ Φ) x).re := by
      have hp : (fun x : Submission.BoseGases.X n => star (boxRestrictC ℓ Φ x)
            * Work.BoseDict.boxSlotSum e T_NH (boxRestrictC ℓ Φ) x)
          = fun x => ∑ k ∈ Work.BoseB7.excited (Lab N), ((1 / 32 : ℝ) : ℂ)
              * (((etaH fu (FRK.kappaHon v μ) (kmomLab ℓ N k) : ℝ) : ℂ)
                * (star (boxRestrictC ℓ Φ x)
                  * Work.BoseDict.boxSlotSum e (rankOne ((HM μ).f k)) (boxRestrictC ℓ Φ) x)) := by
        funext x
        rw [congrFun hBoxSum x]
        simp only [Pi.smul_apply, Finset.sum_apply, Complex.real_smul, Finset.mul_sum]
        exact Finset.sum_congr rfl (fun k _ => by ring)
      rw [hp]
      have hsum2 : (∫ x in Submission.BoseGases.abox n ℓ,
            ∑ k ∈ Work.BoseB7.excited (Lab N), ((1 / 32 : ℝ) : ℂ)
              * (((etaH fu (FRK.kappaHon v μ) (kmomLab ℓ N k) : ℝ) : ℂ)
                * (star (boxRestrictC ℓ Φ x)
                  * Work.BoseDict.boxSlotSum e (rankOne ((HM μ).f k)) (boxRestrictC ℓ Φ) x)))
          = ∑ k ∈ Work.BoseB7.excited (Lab N),
              ∫ x in Submission.BoseGases.abox n ℓ, ((1 / 32 : ℝ) : ℂ)
                * (((etaH fu (FRK.kappaHon v μ) (kmomLab ℓ N k) : ℝ) : ℂ)
                  * (star (boxRestrictC ℓ Φ x)
                    * Work.BoseDict.boxSlotSum e (rankOne ((HM μ).f k)) (boxRestrictC ℓ Φ) x)) :=
        MeasureTheory.integral_finsetSum _ (fun k _ =>
          ((star_mul_integrableOn_abox hℓ.le hgood
            (slotGood_boxSlotSum hmeas hbdd hsupp _ hgood)).const_mul _).const_mul _)
      rw [hsum2, Complex.re_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl (fun k _ => ?_)
      simp only [MeasureTheory.integral_const_mul, Complex.mul_re, Complex.ofReal_re,
        Complex.ofReal_im, zero_mul, sub_zero]
      try ring
    rw [hBox]
    -- the weight is `η_H`; extend the excited sum to all modes
    have hmod : ∀ k : Lab N, (∫ x in Submission.BoseGases.abox n ℓ,
          star (boxRestrictC ℓ Φ x)
            * Work.BoseDict.boxSlotSum e (rankOne ((HM μ).f k)) (boxRestrictC ℓ Φ) x).re
        ≤ ∑ j : Fin n, (ℓ ^ 3)⁻¹ * ∫ x in Submission.BoseGases.abox n ℓ,
            Work.BoseKinLoc.indU ℓ 0 (x j) * ((ℓ ^ 3)⁻¹ * ‖Submission.BoseGases.kinFT
              (winState ℓ (Work.BoseKinLoc.fibre n j Φ x)) (kmomLab ℓ N k)‖ ^ 2) :=
      fun k => boxSlotSum_rankOne_re_le_fibre (n := n) (N := N) hℓ hmeas hbdd hsupp hq
        Φ.contDiff k
    have hsub : (∑ k ∈ Work.BoseB7.excited (Lab N),
          etaH fu (FRK.kappaHon v μ) (kmomLab ℓ N k)
            * (∫ x in Submission.BoseGases.abox n ℓ, star (boxRestrictC ℓ Φ x)
                * Work.BoseDict.boxSlotSum e (rankOne ((HM μ).f k)) (boxRestrictC ℓ Φ) x).re)
        ≤ ∑ k : Lab N, etaH fu (FRK.kappaHon v μ) (kmomLab ℓ N k)
            * (∑ j : Fin n, (ℓ ^ 3)⁻¹ * ∫ x in Submission.BoseGases.abox n ℓ,
                Work.BoseKinLoc.indU ℓ 0 (x j) * ((ℓ ^ 3)⁻¹ * ‖Submission.BoseGases.kinFT
                  (winState ℓ (Work.BoseKinLoc.fibre n j Φ x)) (kmomLab ℓ N k)‖ ^ 2)) := by
      calc (∑ k ∈ Work.BoseB7.excited (Lab N),
            etaH fu (FRK.kappaHon v μ) (kmomLab ℓ N k)
              * (∫ x in Submission.BoseGases.abox n ℓ, star (boxRestrictC ℓ Φ x)
                  * Work.BoseDict.boxSlotSum e (rankOne ((HM μ).f k)) (boxRestrictC ℓ Φ) x).re)
          ≤ (∑ k ∈ Work.BoseB7.excited (Lab N),
            etaH fu (FRK.kappaHon v μ) (kmomLab ℓ N k)
              * (∑ j : Fin n, (ℓ ^ 3)⁻¹ * ∫ x in Submission.BoseGases.abox n ℓ,
                  Work.BoseKinLoc.indU ℓ 0 (x j) * ((ℓ ^ 3)⁻¹ * ‖Submission.BoseGases.kinFT
                    (winState ℓ (Work.BoseKinLoc.fibre n j Φ x)) (kmomLab ℓ N k)‖ ^ 2))) :=
            Finset.sum_le_sum (fun k _ => mul_le_mul_of_nonneg_left (hmod k) (etaH_nonneg fu _ _))
        _ ≤ (∑ k : Lab N, etaH fu (FRK.kappaHon v μ) (kmomLab ℓ N k)
              * (∑ j : Fin n, (ℓ ^ 3)⁻¹ * ∫ x in Submission.BoseGases.abox n ℓ,
                  Work.BoseKinLoc.indU ℓ 0 (x j) * ((ℓ ^ 3)⁻¹ * ‖Submission.BoseGases.kinFT
                    (winState ℓ (Work.BoseKinLoc.fibre n j Φ x)) (kmomLab ℓ N k)‖ ^ 2))) := by
          refine Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset _ _) ?_
          intro k _ hk
          have hk0 : k = 0 := by
            by_contra h'
            exact hk (Finset.mem_erase.mpr ⟨h', Finset.mem_univ k⟩)
          subst hk0
          refine mul_nonneg (etaH_nonneg fu _ _) ?_
          refine Finset.sum_nonneg (s := Finset.univ) ?_
          intro j _
          refine mul_nonneg (by positivity) ?_
          refine integral_nonneg (fun x => mul_nonneg ?_ (by positivity))
          rw [Work.BoseKinLoc.indU]
          exact Set.indicator_nonneg (s := Work.BoseKinLoc.lamBox ℓ 0)
            (f := fun _ => (1 : ℝ)) (fun _ _ => by norm_num) (x j)
    have hAgg : (∑ k : Lab N, etaH fu (FRK.kappaHon v μ) (kmomLab ℓ N k)
          * (∑ j : Fin n, (ℓ ^ 3)⁻¹ * ∫ x in Submission.BoseGases.abox n ℓ,
              Work.BoseKinLoc.indU ℓ 0 (x j) * ((ℓ ^ 3)⁻¹ * ‖Submission.BoseGases.kinFT
                (winState ℓ (Work.BoseKinLoc.fibre n j Φ x)) (kmomLab ℓ N k)‖ ^ 2)))
        = ∑ j : Fin n, (ℓ ^ 3)⁻¹ * ∫ x in Submission.BoseGases.abox n ℓ,
            Work.BoseKinLoc.indU ℓ 0 (x j)
              * kinEtaLat N fu (FRK.kappaHon v μ) ℓ (Work.BoseKinLoc.fibre n j Φ x) := by
      rw [sum_weight_fibre_aggregate hℓ
        (fun k => etaH fu (FRK.kappaHon v μ) (kmomLab ℓ N k)) Φ.contDiff]
      refine Finset.sum_congr (rfl : (Finset.univ : Finset (Fin n)) = Finset.univ) ?_
      intro j _
      simp only [kinEtaLat]
    calc (E.eT * E.b / (2 * E.d ^ 2 * E.ell ^ 2)) * ((1 / 32 : ℝ)
          * ∑ k ∈ Work.BoseB7.excited (Lab N), etaH fu (FRK.kappaHon v μ) (kmomLab ℓ N k)
              * (∫ x in Submission.BoseGases.abox n ℓ, star (boxRestrictC ℓ Φ x)
                  * Work.BoseDict.boxSlotSum e (rankOne ((HM μ).f k)) (boxRestrictC ℓ Φ) x).re)
        ≤ (E.eT * E.b / (2 * E.d ^ 2 * E.ell ^ 2)) * ((1 / 32 : ℝ)
            * ∑ k : Lab N, etaH fu (FRK.kappaHon v μ) (kmomLab ℓ N k)
              * (∑ j : Fin n, (ℓ ^ 3)⁻¹ * ∫ x in Submission.BoseGases.abox n ℓ,
                  Work.BoseKinLoc.indU ℓ 0 (x j) * ((ℓ ^ 3)⁻¹ * ‖Submission.BoseGases.kinFT
                    (winState ℓ (Work.BoseKinLoc.fibre n j Φ x)) (kmomLab ℓ N k)‖ ^ 2))) := by
          refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hsub (by norm_num)) ?_
          rw [honest_E_eT, honest_E_b, honest_E_d, honest_E_ell, ← hℓdef]
          exact div_nonneg (mul_nonneg heT0 hbpos.le) (by positivity)
      _ = (E.eT * E.b / (2 * E.d ^ 2 * E.ell ^ 2)) * ((1 / 32 : ℝ)
            * ∑ j : Fin n, (ℓ ^ 3)⁻¹ * ∫ x in Submission.BoseGases.abox n ℓ,
                Work.BoseKinLoc.indU ℓ 0 (x j)
                  * kinEtaLat N fu (FRK.kappaHon v μ) ℓ (Work.BoseKinLoc.fibre n j Φ x)) := by
          rw [hAgg]
      _ = ∑ j : Fin n, (ℓ ^ 3)⁻¹ * ∫ x in Submission.BoseGases.abox n ℓ,
            Work.BoseKinLoc.indU ℓ 0 (x j)
              * (P.eT * P.b / (2 * P.d ^ 2 * ℓ ^ 2)
                * ((1 / 32 : ℝ) * kinEtaLat N fu (FRK.kappaHon v μ) ℓ
                    (Work.BoseKinLoc.fibre n j Φ x))) := by
          have hc3 : E.eT * E.b / (2 * E.d ^ 2 * E.ell ^ 2)
              = P.eT * P.b / (2 * P.d ^ 2 * ℓ ^ 2) := by
            rw [honest_E_b, honest_E_eT, honest_E_d, honest_E_ell, ← hℓdef]
          rw [hc3, Finset.mul_sum, Finset.mul_sum]
          refine Finset.sum_congr (rfl : (Finset.univ : Finset (Fin n)) = Finset.univ) ?_
          intro j _
          have hCj : (∫ x in Submission.BoseGases.abox n ℓ, Work.BoseKinLoc.indU ℓ 0 (x j)
                * ((P.eT * P.b / (2 * P.d ^ 2 * ℓ ^ 2))
                  * ((1 / 32 : ℝ) * kinEtaLat N fu (FRK.kappaHon v μ) ℓ
                      (Work.BoseKinLoc.fibre n j Φ x))))
              = (P.eT * P.b / (2 * P.d ^ 2 * ℓ ^ 2)) * ((1 / 32 : ℝ)
                  * (∫ x in Submission.BoseGases.abox n ℓ, Work.BoseKinLoc.indU ℓ 0 (x j)
                      * kinEtaLat N fu (FRK.kappaHon v μ) ℓ
                          (Work.BoseKinLoc.fibre n j Φ x))) := by
            rw [show (fun x : Submission.BoseGases.X n => Work.BoseKinLoc.indU ℓ 0 (x j)
                  * ((P.eT * P.b / (2 * P.d ^ 2 * ℓ ^ 2))
                    * ((1 / 32 : ℝ) * kinEtaLat N fu (FRK.kappaHon v μ) ℓ
                        (Work.BoseKinLoc.fibre n j Φ x))))
                = fun x : Submission.BoseGases.X n => (P.eT * P.b / (2 * P.d ^ 2 * ℓ ^ 2))
                  * ((1 / 32 : ℝ) * (Work.BoseKinLoc.indU ℓ 0 (x j)
                    * kinEtaLat N fu (FRK.kappaHon v μ) ℓ
                        (Work.BoseKinLoc.fibre n j Φ x))) from by
              funext x; ring]
            simp only [MeasureTheory.integral_const_mul]
          rw [hCj]
          ring
  -- ## 9. the three rows combine into the kinetic-group fibre sum
  have hterm : ∀ j : Fin n,
      (∫ x in Submission.BoseGases.abox n ℓ, Work.BoseKinLoc.indU ℓ 0 (x j)
        * kinGroupLL N ℓ P.s P.d P.eT P.b (FRK.kappaHon v μ) fu
            (Work.BoseKinLoc.fibre n j Φ x))
      = (∫ x in Submission.BoseGases.abox n ℓ, Work.BoseKinLoc.indU ℓ 0 (x j)
          * kinTauLat N P.eT P.s P.d ℓ (Work.BoseKinLoc.fibre n j Φ x))
        + (∫ x in Submission.BoseGases.abox n ℓ, Work.BoseKinLoc.indU ℓ 0 (x j)
            * (P.b / (2 * ℓ ^ 2)
              * Work.BoseKinLoc.gapBare ℓ 0 (Work.BoseKinLoc.fibre n j Φ x)))
        + (∫ x in Submission.BoseGases.abox n ℓ, Work.BoseKinLoc.indU ℓ 0 (x j)
            * (P.eT * P.b / (2 * P.d ^ 2 * ℓ ^ 2)
              * ((1 / 32 : ℝ) * kinEtaLat N fu (FRK.kappaHon v μ) ℓ
                  (Work.BoseKinLoc.fibre n j Φ x)))) := by
    intro j
    have hA : MeasureTheory.IntegrableOn (fun x : Submission.BoseGases.X n =>
        Work.BoseKinLoc.indU ℓ 0 (x j)
          * kinTauLat N P.eT P.s P.d ℓ (Work.BoseKinLoc.fibre n j Φ x))
        (Submission.BoseGases.abox n ℓ) :=
      integrableOn_indU_kinTauLat_fibre (N := N) (s := P.s) (d := P.d) (eT := P.eT)
        hℓ j Φ.contDiff
    have hB : MeasureTheory.IntegrableOn (fun x : Submission.BoseGases.X n =>
        Work.BoseKinLoc.indU ℓ 0 (x j)
          * (P.b / (2 * ℓ ^ 2)
            * Work.BoseKinLoc.gapBare ℓ 0 (Work.BoseKinLoc.fibre n j Φ x)))
        (Submission.BoseGases.abox n ℓ) := by
      have h0 : MeasureTheory.IntegrableOn (fun x : Submission.BoseGases.X n =>
          (P.b / (2 * ℓ ^ 2)) * (Work.BoseKinLoc.indU ℓ 0 (x j)
            * Work.BoseKinLoc.gapBare ℓ 0 (Work.BoseKinLoc.fibre n j Φ x)))
          (Submission.BoseGases.abox n ℓ) :=
        (integrableOn_indU_gapBare_fibre (ℓ := ℓ) hℓ j Φ.contDiff).const_mul _
      exact h0.congr (Filter.Eventually.of_forall (fun x => by ring))
    have hC : MeasureTheory.IntegrableOn (fun x : Submission.BoseGases.X n =>
        Work.BoseKinLoc.indU ℓ 0 (x j)
          * (P.eT * P.b / (2 * P.d ^ 2 * ℓ ^ 2)
            * ((1 / 32 : ℝ) * kinEtaLat N fu (FRK.kappaHon v μ) ℓ
                (Work.BoseKinLoc.fibre n j Φ x))))
        (Submission.BoseGases.abox n ℓ) := by
      have h0 : MeasureTheory.IntegrableOn (fun x : Submission.BoseGases.X n =>
          (P.eT * P.b / (2 * P.d ^ 2 * ℓ ^ 2))
            * ((1 / 32 : ℝ) * (Work.BoseKinLoc.indU ℓ 0 (x j)
              * kinEtaLat N fu (FRK.kappaHon v μ) ℓ (Work.BoseKinLoc.fibre n j Φ x))))
          (Submission.BoseGases.abox n ℓ) :=
        ((integrableOn_indU_kinEtaLat_fibre (N := N) (κ := FRK.kappaHon v μ)
          (fu := fu) hℓ j Φ.contDiff).const_mul (1 / 32 : ℝ)).const_mul
          (P.eT * P.b / (2 * P.d ^ 2 * ℓ ^ 2))
      exact h0.congr (Filter.Eventually.of_forall (fun x => by ring))
    have e0 : (∫ x in Submission.BoseGases.abox n ℓ, Work.BoseKinLoc.indU ℓ 0 (x j)
          * kinGroupLL N ℓ P.s P.d P.eT P.b (FRK.kappaHon v μ) fu
              (Work.BoseKinLoc.fibre n j Φ x))
        = (∫ x in Submission.BoseGases.abox n ℓ, (fun y : Submission.BoseGases.X n =>
            Work.BoseKinLoc.indU ℓ 0 (y j)
              * kinTauLat N P.eT P.s P.d ℓ (Work.BoseKinLoc.fibre n j Φ y)
            + Work.BoseKinLoc.indU ℓ 0 (y j)
              * (P.b / (2 * ℓ ^ 2)
                * Work.BoseKinLoc.gapBare ℓ 0 (Work.BoseKinLoc.fibre n j Φ y))
            + Work.BoseKinLoc.indU ℓ 0 (y j)
              * (P.eT * P.b / (2 * P.d ^ 2 * ℓ ^ 2)
                * ((1 / 32 : ℝ) * kinEtaLat N fu (FRK.kappaHon v μ) ℓ
                    (Work.BoseKinLoc.fibre n j Φ y)))) x) := by
      refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun x => ?_))
      simp only [kinGroupLL]
      ring
    have e1 : (∫ x in Submission.BoseGases.abox n ℓ, (fun y : Submission.BoseGases.X n =>
          Work.BoseKinLoc.indU ℓ 0 (y j)
            * kinTauLat N P.eT P.s P.d ℓ (Work.BoseKinLoc.fibre n j Φ y)
          + Work.BoseKinLoc.indU ℓ 0 (y j)
            * (P.b / (2 * ℓ ^ 2)
              * Work.BoseKinLoc.gapBare ℓ 0 (Work.BoseKinLoc.fibre n j Φ y))
          + Work.BoseKinLoc.indU ℓ 0 (y j)
            * (P.eT * P.b / (2 * P.d ^ 2 * ℓ ^ 2)
              * ((1 / 32 : ℝ) * kinEtaLat N fu (FRK.kappaHon v μ) ℓ
                  (Work.BoseKinLoc.fibre n j Φ y)))) x)
        = (∫ x in Submission.BoseGases.abox n ℓ, (fun y : Submission.BoseGases.X n =>
            Work.BoseKinLoc.indU ℓ 0 (y j)
              * kinTauLat N P.eT P.s P.d ℓ (Work.BoseKinLoc.fibre n j Φ y)
            + Work.BoseKinLoc.indU ℓ 0 (y j)
              * (P.b / (2 * ℓ ^ 2)
                * Work.BoseKinLoc.gapBare ℓ 0 (Work.BoseKinLoc.fibre n j Φ y))) x)
          + (∫ x in Submission.BoseGases.abox n ℓ, (fun y : Submission.BoseGases.X n =>
              Work.BoseKinLoc.indU ℓ 0 (y j)
                * (P.eT * P.b / (2 * P.d ^ 2 * ℓ ^ 2)
                  * ((1 / 32 : ℝ) * kinEtaLat N fu (FRK.kappaHon v μ) ℓ
                      (Work.BoseKinLoc.fibre n j Φ y)))) x) :=
      MeasureTheory.integral_add (hA.add hB) hC
    have e2 : (∫ x in Submission.BoseGases.abox n ℓ, (fun y : Submission.BoseGases.X n =>
          Work.BoseKinLoc.indU ℓ 0 (y j)
            * kinTauLat N P.eT P.s P.d ℓ (Work.BoseKinLoc.fibre n j Φ y)
          + Work.BoseKinLoc.indU ℓ 0 (y j)
            * (P.b / (2 * ℓ ^ 2)
              * Work.BoseKinLoc.gapBare ℓ 0 (Work.BoseKinLoc.fibre n j Φ y))) x)
        = (∫ x in Submission.BoseGases.abox n ℓ, (fun y : Submission.BoseGases.X n =>
            Work.BoseKinLoc.indU ℓ 0 (y j)
              * kinTauLat N P.eT P.s P.d ℓ (Work.BoseKinLoc.fibre n j Φ y)) x)
          + (∫ x in Submission.BoseGases.abox n ℓ, (fun y : Submission.BoseGases.X n =>
              Work.BoseKinLoc.indU ℓ 0 (y j)
                * (P.b / (2 * ℓ ^ 2)
                  * Work.BoseKinLoc.gapBare ℓ 0 (Work.BoseKinLoc.fibre n j Φ y))) x) :=
      MeasureTheory.integral_add hA hB
    rw [e0, e1, e2]
  have hcombine : (∑ j : Fin n, (ℓ ^ 3)⁻¹ * ∫ x in Submission.BoseGases.abox n ℓ,
          Work.BoseKinLoc.indU ℓ 0 (x j) * kinTauLat N P.eT P.s P.d ℓ
            (Work.BoseKinLoc.fibre n j Φ x))
        + (∑ j : Fin n, (ℓ ^ 3)⁻¹ * ∫ x in Submission.BoseGases.abox n ℓ,
          Work.BoseKinLoc.indU ℓ 0 (x j)
            * (P.b / (2 * ℓ ^ 2) * Work.BoseKinLoc.gapBare ℓ 0
                (Work.BoseKinLoc.fibre n j Φ x)))
        + (∑ j : Fin n, (ℓ ^ 3)⁻¹ * ∫ x in Submission.BoseGases.abox n ℓ,
          Work.BoseKinLoc.indU ℓ 0 (x j)
            * (P.eT * P.b / (2 * P.d ^ 2 * ℓ ^ 2)
              * ((1 / 32 : ℝ) * kinEtaLat N fu (FRK.kappaHon v μ) ℓ
                  (Work.BoseKinLoc.fibre n j Φ x))))
      = ∑ j : Fin n, (ℓ ^ 3)⁻¹ * ∫ x in Submission.BoseGases.abox n ℓ,
          Work.BoseKinLoc.indU ℓ 0 (x j)
            * kinGroupLL N ℓ P.s P.d P.eT P.b (FRK.kappaHon v μ) fu
                (Work.BoseKinLoc.fibre n j Φ x) := by
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr (rfl : (Finset.univ : Finset (Fin n)) = Finset.univ) ?_
    intro j _
    rw [hterm j]
    ring
  -- ## 10. the integrated fibre inequality
  have hτ : ∀ ψ : Ω → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ →
      kinGroupLL N ℓ P.s P.d P.eT P.b (FRK.kappaHon v μ) fu ψ
        ≤ kinGroupRR ℓ P.s P.d P.eT P.b ψ :=
    fun ψ hψ => (OBineq4_iff_kinRowLHS ℓ P.s P.d P.eT P.b (FRK.kappaHon v μ) fu N ψ).mp
      (hOB μ hAdm N ψ hψ)
  have hrow := kinGroup_slotSum_le (N := N) hℓ hspos hdpos hd1 heT0 hbpos fu hτ
    (Φ := (Φ : Submission.BoseGases.X n → ℝ)) Φ.contDiff
  -- ## 11. the target
  have hL : (∫ x : Submission.BoseGases.X n, star (boxRestrictC ℓ Φ x)
        * AVgen (fun T => Work.BoseDict.boxSlotSum e T)
            (id : (Work.BoseDict.Xn n → ℂ) → (Work.BoseDict.Xn n → ℂ))
            (HM μ).f (HM μ).g T_NH (∅ : Finset (Lab N)) (kinOnlyEnv E) 0
            (boxRestrictC ℓ Φ) x).re
      = (∫ x in Submission.BoseGases.abox n ℓ, star (boxRestrictC ℓ Φ x)
        * AVgen (fun T => Work.BoseDict.boxSlotSum e T)
            (id : (Work.BoseDict.Xn n → ℂ) → (Work.BoseDict.Xn n → ℂ))
            (HM μ).f (HM μ).g T_NH (∅ : Finset (Lab N)) (kinOnlyEnv E) 0
            (boxRestrictC ℓ Φ) x).re := by
    rw [← MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero
      (s := Submission.BoseGases.abox n ℓ)
      (f := fun x : Submission.BoseGases.X n => star (boxRestrictC ℓ Φ x)
        * AVgen (fun T => Work.BoseDict.boxSlotSum e T)
            (id : (Work.BoseDict.Xn n → ℂ) → (Work.BoseDict.Xn n → ℂ))
            (HM μ).f (HM μ).g T_NH (∅ : Finset (Lab N)) (kinOnlyEnv E) 0
            (boxRestrictC ℓ Φ) x) ?_]
    intro x hx
    rw [hΘzero x hx, star_zero, zero_mul]
  refine le_trans (le_of_eq hL) ?_
  calc (∫ x in Submission.BoseGases.abox n ℓ, star (boxRestrictC ℓ Φ x)
        * AVgen (fun T => Work.BoseDict.boxSlotSum e T)
            (id : (Work.BoseDict.Xn n → ℂ) → (Work.BoseDict.Xn n → ℂ))
            (HM μ).f (HM μ).g T_NH (∅ : Finset (Lab N)) (kinOnlyEnv E) 0
            (boxRestrictC ℓ Φ) x).re
      = (∫ x in Submission.BoseGases.abox n ℓ, F1 x).re
        + (∫ x in Submission.BoseGases.abox n ℓ, F2 x).re
        + (∫ x in Submission.BoseGases.abox n ℓ, F3 x).re := hsplit
    _ ≤ (∑ j : Fin n, (ℓ ^ 3)⁻¹ * ∫ x in Submission.BoseGases.abox n ℓ,
          Work.BoseKinLoc.indU ℓ 0 (x j) * kinTauLat N P.eT P.s P.d ℓ
            (Work.BoseKinLoc.fibre n j Φ x))
        + (∑ j : Fin n, (ℓ ^ 3)⁻¹ * ∫ x in Submission.BoseGases.abox n ℓ,
          Work.BoseKinLoc.indU ℓ 0 (x j)
            * (P.b / (2 * ℓ ^ 2) * Work.BoseKinLoc.gapBare ℓ 0
                (Work.BoseKinLoc.fibre n j Φ x)))
        + (∑ j : Fin n, (ℓ ^ 3)⁻¹ * ∫ x in Submission.BoseGases.abox n ℓ,
          Work.BoseKinLoc.indU ℓ 0 (x j)
            * (P.eT * P.b / (2 * P.d ^ 2 * ℓ ^ 2)
              * ((1 / 32 : ℝ) * kinEtaLat N fu (FRK.kappaHon v μ) ℓ
                  (Work.BoseKinLoc.fibre n j Φ x)))) := by
        linarith [hτrow, hgaprow, hηrow]
    _ = ∑ j : Fin n, (ℓ ^ 3)⁻¹ * ∫ x in Submission.BoseGases.abox n ℓ,
          Work.BoseKinLoc.indU ℓ 0 (x j)
            * kinGroupLL N ℓ P.s P.d P.eT P.b (FRK.kappaHon v μ) fu
                (Work.BoseKinLoc.fibre n j Φ x) := hcombine
    _ ≤ Work.BoseKinLoc.kinFormB n ℓ P.d P.s P.eT P.b
          (Φ : Submission.BoseGases.X n → ℝ)
        - P.b / 4 * (ℓ ^ (-2 : ℤ) * Submission.BoseGases.cnPlus ℓ
            (Φ : Submission.BoseGases.X n → ℝ))
        - P.b / 100 * (P.eT * (P.d * ℓ) ^ (-2 : ℤ)
            * Work.BoseBoxFix.nPlusHB ℓ P.d (Φ : Submission.BoseGases.X n → ℝ)) := hrow
    _ = Work.BoseKinLoc.kinFormB n ℓ P.d P.s P.eT P.b (Φ : Submission.BoseGases.X n → ℝ)
        - (P.b / 4 - P.b / 100) * (ℓ ^ (-2 : ℤ) * Submission.BoseGases.cnPlus ℓ
            (Φ : Submission.BoseGases.X n → ℝ))
        - (P.b / 100) * (ℓ ^ (-2 : ℤ) * Submission.BoseGases.cnPlus ℓ
              (Φ : Submission.BoseGases.X n → ℝ)
            + P.eT * (P.d * ℓ) ^ (-2 : ℤ)
                * Work.BoseBoxFix.nPlusHB ℓ P.d (Φ : Submission.BoseGases.X n → ℝ))
        + (1 / 2) * Work.BoseFixR.errKafz v R μ 0 * Work.BoseBoxFix.normB v μ n Φ := by
      rw [show Work.BoseFixR.errKafz v R μ 0 = 0 from by
        simp only [Work.BoseFixR.errKafz, zero_mul, mul_zero]]
      ring

end Work.BoseBoxFock
