import ChallengeDeps
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Data.ZMod.ValMinAbs
import Mathlib.Algebra.Order.Star.Real
import Submission.Work.BoseBoxFock.PotChiLin_aux
import Submission.Work.BoseBoxFock.chiRow_arith_step
import Submission.Work.BoseBoxFock.chiRow_compareSharp2
import Submission.Work.BoseBoxFock.chiRow_muEval
import Submission.Work.BoseBoxFock.chiRow_pairFirstEval
import Submission.Work.BoseBoxFock.chiRow_pairSecond
import Submission.Work.BoseBoxFock.honestPins
import Submission.Work.BoseBoxFock.thRow_pairFirst
import Submission.Work.BoseBoxFock.thRow_pairSecond
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.PotChiLin_exists` — the FS `Q₁` row at a *chosen* lattice cut-off

The target is the repaired (`∃ Nmin`) form of the `χ`-row of FS `prop:Hamilton2ndQuant`
(`lem:2ndQuand`'s `Q₁`); the refutation of the `∀Nmin` form is in
`Submission/Work/BoseBoxFock/FINDING_PotChiLin_holds_FALSE.md`, and the reduction, the verified
slot identity and the arithmetic that closes the row are in
`Submission/Work/BoseBoxFock/FINDING_PotChiLin_exists.md` (sessions 1 and 2).

The proof is assembled from the following modules (all in this directory):

* `PotChiLin_aux` — `wScaled_int_abs_le`, `g0_abs_integral_le`, `g0w0_abs_integral_le`,
  `errKafz_ge_slot`, `one_le_mu_mul_side_sq`, `exists_tails_dil`;
* `honestPins` — the two pins `√ℓ³·η_C =ᵐ chiMode`, `√ℓ³·η_{C'} =ᵐ thMode`;
* `chiRow_pairFirstEval`/`chiRow_pairSecond`/`chiRow_muEval`/`thRow_pairFirst`/`thRow_pairSecond`
  — the six slot-word evaluations (`chiRowSum_eval` combines them);
* `chiRow_compareSharp` — the comparison with `q1word` and the explicit error `BOUND`;
* `chiRow_arith_step` — `BOUND ≤ ½·errKafz·‖Φ‖²`.

Local ingredients: `honest_E_W1_zero` (`E.W1 0 = Ŵ₁(0)`), `bigM_pos`, `kernelData` (the four
kernel-comparison bounds at `A = 16π·C·(R/ℓ)²a`).

The choice of parameters is `Nmin μ = ⌈(μ(a v)³)^{-1}⌉`, `ε₀ = min ε₀(χR0) 1`, and `C = C_arith`.
-/

noncomputable section

open scoped BigOperators
open MeasureTheory

namespace Work.BoseBoxFock

set_option autoImplicit false
set_option maxHeartbeats 1000000

local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-- `E.W1 0` is `Ŵ₁(0)` of the χ-row. -/
theorem honest_E_W1_zero (v : ℝ³ → ℝ) (h : Work.UBB.ScatSol v) (fc fu : Work.BoseBoxFix.LowCut)
    (HM : ∀ μ : ℝ, HonestModes v μ) (μ : ℝ) (hμ : 0 < μ) (hav : 0 < BoseGases.a v) :
    (HonestBoxFam v h fc fu HM μ).E.W1 (0 : Lab (HM μ).N)
      = Work.BoseFixR.chat (Submission.BoseGases.wScaled
          (Work.BoseBox.sideAt μ (BoseGases.a v)) (Submission.BoseGases.g0 v h)) 0 := by
  have hℓ : 0 < Work.BoseBox.sideAt μ (BoseGases.a v) := Work.BoseBox.sideAt_pos hμ hav
  have hell : ellH v μ = Work.BoseBox.sideAt μ (BoseGases.a v) := by rw [ellH, if_pos hℓ]
  have hkm : Work.BoseBoxFock.kmomLab (Work.BoseBox.sideAt μ (BoseGases.a v))
      (HM μ).N (0 : Lab (HM μ).N) = 0 := by
    have hlab0 : Work.BoseBoxFock.labVec (HM μ).N (0 : Lab (HM μ).N) = 0 := by
      funext i; simp [Work.BoseBoxFock.labVec]
    have hvec0 : Work.BoseB4.vec (0 : Fin 3 → ℤ) = 0 := by
      ext i; simp [Work.BoseB4.vec]
    rw [Work.BoseBoxFock.kmomLab, hlab0, hvec0, smul_zero]
  simp only [HonestBoxFam, KzEnvHon, Work.BoseFixR.KzEnvFs, hell]
  change Work.BoseBoxFock.uvCut fu (Work.BoseBoxFock.uvRad (Work.BoseBox.sideAt μ (BoseGases.a v))
        (HM μ).N)
        (Work.BoseBoxFock.kmomLab (Work.BoseBox.sideAt μ (BoseGases.a v)) (HM μ).N 0)
      * Work.BoseFixR.chat (Work.BoseFixR.W1fun v h (Work.BoseBox.sideAt μ (BoseGases.a v)))
          (Work.BoseBoxFock.kmomLab (Work.BoseBox.sideAt μ (BoseGases.a v)) (HM μ).N 0)
      = Work.BoseFixR.chat (Submission.BoseGases.wScaled
          (Work.BoseBox.sideAt μ (BoseGases.a v)) (Submission.BoseGases.g0 v h)) 0
  rw [hkm]
  simp only [norm_zero, zero_div, Work.BoseBoxFock.uvCut, Work.BoseFixR.W1fun]
  rw [Work.BoseBoxFix.LowCut.one fu 0 (by norm_num), one_mul]

/-- The `𝓜`-window at FS's parameters is positive. -/
theorem bigM_pos (μ a : ℝ) (hμ : 0 < μ) (ha : 0 < a) :
    0 < Work.BoseBox.bigM (Work.BoseBox.paramsAt μ a) a μ := by
  have ht : 0 < μ * a ^ 3 := by positivity
  have h1 : 0 < (Work.BoseBox.paramsAt μ a).KM := by
    simp only [Work.BoseBox.paramsAt, Work.BoseBox.fsParams, Work.BoseBox.fsXp]
    exact Real.rpow_pos_of_pos ht _
  have h2 : 0 < (μ * a ^ 3) ^ (-(1 / 4 : ℝ)) := Real.rpow_pos_of_pos ht _
  simp only [Work.BoseBox.bigM]
  exact mul_pos h1 h2

/-- **The kernel-comparison data of the `χ`-row at `A = 16π·C·(R/ℓ)²a`.** -/
theorem kernelData {v : E3 → ℝ} {h : Work.UBB.ScatSol v} {R ℓ C : ℝ}
    (hR : 0 < R) (hℓ : 0 < ℓ) (hv : 0 ≤ v) (hvrad : _root_.BoseGases.IsRadial v)
    (hv_supp : tsupport v ⊆ Metric.ball (0 : E3) R)
    (hRℓ : R ≤ ℓ * Submission.BoseGases.chiR0) (hC : 0 ≤ C)
    (hkcd : ∀ {g : E3 → ℝ} {R' ℓ' : ℝ}, 0 < R' → 0 < ℓ' →
      R' ≤ ℓ' * Submission.BoseGases.chiR0 →
      (∀ z : E3, g (-z) = g z) → tsupport g ⊆ Metric.ball (0 : E3) R' →
      MeasureTheory.Integrable g →
      (∀ x : E3,
        |Work.BoseFixR.chat (Submission.BoseGases.wScaled ℓ' g) 0
            * Submission.BoseGases.chiScale ℓ' x ^ 2
          - Submission.BoseGases.w1Fibre ℓ' (Submission.BoseGases.wLoc ℓ' g 0) x|
          ≤ C * (R' / ℓ') ^ 2 * ∫ z : E3, |Submission.BoseGases.wScaled ℓ' g z|)
      ∧ |(ℓ' ^ 3)⁻¹ * (∫ x in Submission.BoseGases.acube ℓ',
              Submission.BoseGases.w1Fibre ℓ' (Submission.BoseGases.wLoc ℓ' g 0) x)
            - Work.BoseFixR.chat (Submission.BoseGases.wScaled ℓ' g) 0|
          ≤ C * (R' / ℓ') ^ 2 * ∫ z : E3, |Submission.BoseGases.wScaled ℓ' g z|) :
    |Work.BoseFixR.chat (Submission.BoseGases.wScaled ℓ (Submission.BoseGases.g0 v h)) 0|
        ≤ 16 * Real.pi * BoseGases.a v
    ∧ |Work.BoseFixR.chat (Submission.BoseGases.wScaled ℓ
          (fun z => Submission.BoseGases.g0 v h z * Classical.choose h z)) 0|
        ≤ 16 * Real.pi * BoseGases.a v
    ∧ (∀ x : E3,
        |Work.BoseFixR.chat (Submission.BoseGases.wScaled ℓ (Submission.BoseGases.g0 v h)) 0
            * Submission.BoseGases.chiScale ℓ x ^ 2
          - Submission.BoseGases.w1Fibre ℓ (Submission.BoseGases.wLoc ℓ (Submission.BoseGases.g0 v h) 0) x|
        ≤ 16 * Real.pi * C * (R / ℓ) ^ 2 * BoseGases.a v)
    ∧ (∀ x : E3,
        |Work.BoseFixR.chat (Submission.BoseGases.wScaled ℓ
              (fun z => Submission.BoseGases.g0 v h z * Classical.choose h z)) 0
            * Submission.BoseGases.chiScale ℓ x ^ 2
          - Submission.BoseGases.w1Fibre ℓ (Submission.BoseGases.wLoc ℓ
              (fun z => Submission.BoseGases.g0 v h z * Classical.choose h z) 0) x|
        ≤ 16 * Real.pi * C * (R / ℓ) ^ 2 * BoseGases.a v)
    ∧ |(ℓ ^ 3)⁻¹ * (∫ x in Submission.BoseGases.acube ℓ,
            Submission.BoseGases.w1Fibre ℓ (Submission.BoseGases.wLoc ℓ (Submission.BoseGases.g0 v h) 0) x)
          - Work.BoseFixR.chat (Submission.BoseGases.wScaled ℓ (Submission.BoseGases.g0 v h)) 0|
        ≤ 16 * Real.pi * C * (R / ℓ) ^ 2 * BoseGases.a v
    ∧ |(ℓ ^ 3)⁻¹ * (∫ x in Submission.BoseGases.acube ℓ, Submission.BoseGases.w1Fibre ℓ
              (Submission.BoseGases.wLoc ℓ
                (fun z => Submission.BoseGases.g0 v h z * Classical.choose h z) 0) x)
          - Work.BoseFixR.chat (Submission.BoseGases.wScaled ℓ
              (fun z => Submission.BoseGases.g0 v h z * Classical.choose h z)) 0|
        ≤ 16 * Real.pi * C * (R / ℓ) ^ 2 * BoseGases.a v := by
  have hK : 0 ≤ C * (R / ℓ) ^ 2 := mul_nonneg hC (sq_nonneg _)
  have hJ1 : (∫ z : E3, |Submission.BoseGases.wScaled ℓ (Submission.BoseGases.g0 v h) z|)
      ≤ 16 * Real.pi * BoseGases.a v := by
    have h := wScaled_int_abs_le hℓ hR.le hRℓ
      (fun z hz => Submission.BoseGases.g0_zero_of_norm_ge hv_supp hz h)
      (Submission.BoseGases.g0_integrable hR hv_supp h)
      (g0_abs_integral_le hR hv hvrad hv_supp)
    linarith [h]
  have hJ2 : (∫ z : E3, |Submission.BoseGases.wScaled ℓ
        (fun z => Submission.BoseGases.g0 v h z * Classical.choose h z) z|)
      ≤ 16 * Real.pi * BoseGases.a v := by
    have h := wScaled_int_abs_le hℓ hR.le hRℓ
      (fun z hz => by rw [Submission.BoseGases.g0_zero_of_norm_ge hv_supp hz h, zero_mul])
      (Submission.BoseGases.g0w0_integrable hR hv hvrad hv_supp h)
      (g0w0_abs_integral_le hR hv hvrad hv_supp)
    linarith [h]
  have hg0e : ∀ z : E3, Submission.BoseGases.g0 v h (-z) = Submission.BoseGases.g0 v h z :=
    Submission.BoseGases.g0_even hvrad h
  have hωe : ∀ z : E3, Classical.choose h (-z) = Classical.choose h z :=
    Submission.BoseGases.radial_neg (Classical.choose_spec h).1
  have hg0supp0 : Function.support (Submission.BoseGases.g0 v h) ⊆ Function.support v :=
    fun x hx => by
      simp only [Function.mem_support] at hx ⊢
      intro hvx
      exact hx (by rw [Submission.BoseGases.g0, hvx, zero_mul])
  have hg0supp : tsupport (Submission.BoseGases.g0 v h) ⊆ Metric.ball (0 : E3) R :=
    Set.Subset.trans (closure_mono hg0supp0) hv_supp
  have hg2supp : tsupport (fun z : E3 => Submission.BoseGases.g0 v h z * Classical.choose h z)
      ⊆ Metric.ball (0 : E3) R :=
    Set.Subset.trans (closure_mono (fun x hx => by
      simp only [Function.mem_support] at hx ⊢
      intro hvx
      exact hx (by rw [Submission.BoseGases.g0, hvx, zero_mul, zero_mul]))) hv_supp
  have h1 := hkcd (g := Submission.BoseGases.g0 v h) hR hℓ hRℓ hg0e hg0supp
    (Submission.BoseGases.g0_integrable hR hv_supp h)
  have h2 := hkcd (g := fun z => Submission.BoseGases.g0 v h z * Classical.choose h z) hR hℓ hRℓ
    (fun z => by
      show Submission.BoseGases.g0 v h (-z) * Classical.choose h (-z)
        = Submission.BoseGases.g0 v h z * Classical.choose h z
      rw [hg0e z, hωe z]) hg2supp
    (Submission.BoseGases.g0w0_integrable hR hv hvrad hv_supp h)
  have hb1 : C * (R / ℓ) ^ 2 * (∫ z : E3,
        |Submission.BoseGases.wScaled ℓ (Submission.BoseGases.g0 v h) z|)
      ≤ 16 * Real.pi * C * (R / ℓ) ^ 2 * BoseGases.a v := by
    have hh := mul_le_mul_of_nonneg_left hJ1 hK
    linarith [hh]
  have hb2 : C * (R / ℓ) ^ 2 * (∫ z : E3, |Submission.BoseGases.wScaled ℓ
        (fun z => Submission.BoseGases.g0 v h z * Classical.choose h z) z|)
      ≤ 16 * Real.pi * C * (R / ℓ) ^ 2 * BoseGases.a v := by
    have hh := mul_le_mul_of_nonneg_left hJ2 hK
    linarith [hh]
  have hq1 : |Work.BoseFixR.chat (Submission.BoseGases.wScaled ℓ (Submission.BoseGases.g0 v h)) 0|
      ≤ 16 * Real.pi * BoseGases.a v := by
    rw [wLocKC_chat_zero_eq_integral]
    exact le_trans (abs_integral_le_integral_abs) hJ1
  have hq2 : |Work.BoseFixR.chat (Submission.BoseGases.wScaled ℓ
        (fun z => Submission.BoseGases.g0 v h z * Classical.choose h z)) 0|
      ≤ 16 * Real.pi * BoseGases.a v := by
    rw [wLocKC_chat_zero_eq_integral]
    exact le_trans (abs_integral_le_integral_abs) hJ2
  exact ⟨hq1, hq2, fun x => le_trans (h1.1 x) hb1, fun x => le_trans (h2.1 x) hb2,
    le_trans h1.2 hb1, le_trans h2.2 hb2⟩

end Work.BoseBoxFock

namespace Work.BoseBoxFock

/-- **The assembly**: `PotChiLin` at the chosen `Nmin`, `ε₀`, `C`. -/
theorem PotChiLin_exists (v : ℝ³ → ℝ) (h : Work.UBB.ScatSol v) (hv : 0 ≤ v)
    (hv1 : MeasureTheory.MemLp v 1) (hvrad : _root_.BoseGases.IsRadial v) {R : ℝ} (hR : 0 < R)
    (hv_supp : tsupport v ⊆ Metric.ball (0 : ℝ³) R) (hav : 0 < BoseGases.a v)
    (fc fu : Work.BoseBoxFix.LowCut) (J : ℝ) (hB3 : Work.BoseBoxFix.NodeB3B v h R fc) :
    ∃ (Nmin : ℝ → ℕ) (ε₀ C : ℝ), 0 < ε₀ ∧ 0 ≤ C ∧
      Work.BoseBoxFock.PotChiLin v h fc fu R J Nmin ε₀ C := by
  obtain ⟨Ckc, hCkc0, hkcd⟩ := wLoc_fibre_kernelCompare
  obtain ⟨Cd, hCd0, htails⟩ := exists_tails_dil
  obtain ⟨ε₀c, hε₀c, hε₀c'⟩ := Work.BoseFixB2.DvApriori.exists_adm_chiR0_ge v hav hR
  obtain ⟨Car, hCar0, harith⟩ := chiRow_arith_step (a := BoseGases.a v) (R := R) hav hR
      (CA := 16 * Real.pi * Ckc) (CW := 16 * Real.pi) (Cd := Cd) (L := 1)
      (by positivity) (by positivity) hCd0 le_rfl
  refine ⟨fun μ => Nat.ceil ((Work.BoseFixR.dil v μ)⁻¹), min ε₀c 1, Car,
    lt_min hε₀c one_pos, hCar0, ?_⟩
  intro HM hN μ hAdm hJ n Φ hn hnorm hlow hspec e hemeas hebdd hesupp heorth heint hemem
    hpin hKp hLp hθp T_NH hTNH
  have hμpos : 0 < μ := hAdm.1
  have ht1 : μ * (BoseGases.a v) ^ 3 ≤ 1 := le_trans hAdm.2.1 (min_le_right _ _)
  have hAdm₀ : Work.BoseBoxFix.Adm v ε₀c μ :=
    ⟨hAdm.1, le_trans hAdm.2.1 (min_le_left _ _), hAdm.2.2⟩
  have hRℓ : R ≤ Work.BoseBox.sideAt μ (BoseGases.a v) * Submission.BoseGases.chiR0 :=
    hε₀c' μ hAdm₀
  have hSp : 0 < Work.BoseBox.sideAt μ (BoseGases.a v) := Work.BoseBox.sideAt_pos hμpos hav
  have hdil0 : 0 < Work.BoseFixR.dil v μ := by rw [Work.BoseFixR.dil]; positivity
  set E := (HonestBoxFam v h fc fu HM μ).E with hEdef
  have hEmu : E.mu = μ := rfl
  have hEell : E.ell = Work.BoseBox.sideAt μ (BoseGases.a v) := rfl
  -- the state
  set Θ : Submission.BoseGases.X n → ℂ :=
    boxRestrictC (Work.BoseBox.sideAt μ (BoseGases.a v)) Φ with hΘdef
  obtain ⟨hΘmeas, hΘbdd, hΘsupp0, hΘperm, hΘmass⟩ := boxRestrictState hSp Φ
  have hΘsupp : Function.support Θ ⊆ Submission.BoseGases.abox n
      (Work.BoseBox.sideAt μ (BoseGases.a v)) := by
    intro x hx
    have h1 := hΘsupp0 hx
    simp only [Work.MB.boxPow, Set.mem_pi, Set.mem_univ, forall_true_left] at h1
    simp only [Submission.BoseGases.abox, Set.mem_setOf_eq]
    intro i
    rw [← corpusBox_boxL_eq_acube hSp]
    exact h1 i
  have hΦc : Continuous (Φ : Submission.BoseGases.X n → ℝ) := Φ.contDiff.continuous
  -- the pins
  obtain ⟨c, hcc, hun⟩ := hpin
  have he0 : e 0 =ᵐ[MeasureTheory.volume] fun z =>
      ((Real.sqrt ((Work.BoseBox.sideAt μ (BoseGases.a v)) ^ 3))⁻¹ : ℂ)
        * Work.BoseK15.corpusBox.thetaFun (Work.BoseBox.sideAt μ (BoseGases.a v)) z :=
    pin_e0_eq hSp ⟨c, hcc, hun⟩ hθp
  have hpinC : (fun z => ((Real.sqrt ((Work.BoseBox.sideAt μ (BoseGases.a v)) ^ 3) : ℝ) : ℂ)
      * Work.BoseDict.etaOf e (∑ k : Lab (HM μ).N, E.hatChi k • (HM μ).f k) z)
      =ᵐ[MeasureTheory.volume] chiMode (Work.BoseBox.sideAt μ (BoseGases.a v)) (HM μ).N :=
    (honestPins HM hμpos hav hemeas hebdd hesupp heorth hKp hLp he0).1
  have hpinS : (fun z => ((Real.sqrt ((Work.BoseBox.sideAt μ (BoseGases.a v)) ^ 3) : ℝ) : ℂ)
      * Work.BoseDict.etaOf e (∑ s ∈ Work.BoseB7.excited (Lab (HM μ).N),
          E.hatChiSq s • (HM μ).g s) z)
      =ᵐ[MeasureTheory.volume] thMode (Work.BoseBox.sideAt μ (BoseGases.a v)) (HM μ).N :=
    (honestPins HM hμpos hav hemeas hebdd hesupp heorth hKp hLp he0).2
  -- collapsing the mode sums
  have hsum : potChiLin (fun T => Work.BoseDict.boxSlotSum e T) (HM μ).f (HM μ).g E Θ
      = potChiLinSummed (fun T => Work.BoseDict.boxSlotSum e T)
          (∑ k : Lab (HM μ).N, E.hatChi k • (HM μ).f k)
          (∑ s ∈ Work.BoseB7.excited (Lab (HM μ).N), E.hatChiSq s • (HM μ).g s) E Θ :=
    potChiLin_eq_summed_good hemeas hebdd hesupp (HM μ).f (HM μ).g E hΘmeas hΘbdd hΘsupp
  -- the evaluation of the six slot words
  have heval := chiRowSum_eval (n := n) (m := (HM μ).m) (ℓ := Work.BoseBox.sideAt μ (BoseGases.a v))
    (N := (HM μ).N) (e := e)
    (C := ∑ k : Lab (HM μ).N, E.hatChi k • (HM μ).f k)
    (C' := ∑ s ∈ Work.BoseB7.excited (Lab (HM μ).N), E.hatChiSq s • (HM μ).g s)
    (Φ := (Φ : Submission.BoseGases.X n → ℝ)) hSp hΦc hemeas hemem hebdd hesupp
    (chiRow_pairFirstEval hSp he0 hemeas hemem hebdd hesupp hpinC hΦc)
    (chiRow_pairSecond hSp he0 hemeas hemem hebdd hesupp hpinC hΦc)
    (chiRow_muEval hSp he0 hemeas hemem hebdd hesupp hpinC hΦc)
    (thRow_pairFirst hSp he0 hemeas hemem hebdd hesupp hpinS hΦc)
    (thRow_pairSecond hSp he0 hemeas hemem hebdd hesupp hpinS hΦc)
    (E.ell ^ (-(3 : ℝ)) * E.W1 0) (E.mu * E.W1 0) (E.ell ^ (-(3 : ℝ)) * E.W1omega0)
  -- the kernel comparison data
  obtain ⟨hW1b, hW1wb, hKC, hKCw, hKCm, hKCmw⟩ :=
    kernelData (h := h) hR hSp hv hvrad hv_supp hRℓ hCkc0 hkcd
  set A : ℝ := 16 * Real.pi * Ckc * (R / Work.BoseBox.sideAt μ (BoseGases.a v)) ^ 2 * BoseGases.a v
    with hAdef
  have hA0 : 0 ≤ A := by rw [hAdef]; positivity
  have hAle : A ≤ 16 * Real.pi * Ckc * (R / Work.BoseBox.sideAt μ (BoseGases.a v)) ^ 2
      * BoseGases.a v := le_of_eq hAdef
  set W1 : ℝ := Work.BoseFixR.chat (Submission.BoseGases.wScaled
      (Work.BoseBox.sideAt μ (BoseGases.a v)) (Submission.BoseGases.g0 v h)) 0 with hW1def
  set W1w : ℝ := Work.BoseFixR.chat (Submission.BoseGases.wScaled
      (Work.BoseBox.sideAt μ (BoseGases.a v))
      (fun z => Submission.BoseGases.g0 v h z * Classical.choose h z)) 0 with hW1wdef
  obtain ⟨hδχ, hδθ⟩ := htails (v := v) (μ := μ) (N := (HM μ).N) hμpos hav (hN μ)
  set 𝓜 : ℝ := Work.BoseBox.bigM (Work.BoseBox.paramsAt μ (BoseGases.a v)) (BoseGases.a v) μ
    with h𝓜def
  have h𝓜0 : 0 ≤ 𝓜 := (bigM_pos μ (BoseGases.a v) hμpos hav).le
  have h𝓜le : 𝓜 ≤ μ * (Work.BoseBox.sideAt μ (BoseGases.a v)) ^ 3 := by
    rw [h𝓜def]
    exact Work.BoseBox.q3_bigM_le_mu_ell_cube hμpos hav ht1
  have hMM : Submission.BoseGases.cnPlus (Work.BoseBox.sideAt μ (BoseGases.a v))
      (Φ : Submission.BoseGases.X n → ℝ) ≤ 𝓜
        * (∫ x in Submission.BoseGases.abox n (Work.BoseBox.sideAt μ (BoseGases.a v)),
            (Φ x) ^ 2) := by
    rw [h𝓜def]
    exact cnPlus_le_bigM_mul hSp hΦc hspec
  have hμaℓ : 1 ≤ μ * BoseGases.a v * (Work.BoseBox.sideAt μ (BoseGases.a v)) ^ 2 :=
    one_le_mu_mul_side_sq hav hμpos ht1
  -- the comparison with the q₁-word
  have hcmp := chiRow_compareSharp2 (n := n) (ℓ := Work.BoseBox.sideAt μ (BoseGases.a v))
    (μ := μ) (R := R) (v := v) (h := h) (Φ := (Φ : Submission.BoseGases.X n → ℝ))
    (N := (HM μ).N) (δ := Cd * Work.BoseFixR.dil v μ) (A := A) (W1 := W1) (W1w := W1w)
    (𝓜 := 𝓜) hSp hμpos hav hR hv hvrad hv_supp hRℓ hΦc rfl rfl hδχ hδθ
      (mul_nonneg hCd0 hdil0.le) hA0
    hKC hKCw hKCm hKCmw
    (fun z => by rw [Submission.BoseGases.g2, Submission.BoseGases.g0]; ring)
    hn hMM h𝓜0
  -- the arithmetic
  have harith' := harith (μ := μ) (ℓ := Work.BoseBox.sideAt μ (BoseGases.a v)) (𝓜 := 𝓜)
    (A := A) (W1 := W1) (W1w := W1w) (δ := Cd * Work.BoseFixR.dil v μ)
    (t := Work.BoseFixR.dil v μ) (n := n) hμpos hSp rfl hdil0 ht1 hμaℓ hn h𝓜le h𝓜0
    hAle hW1b hW1wb
    (by show Cd * Work.BoseFixR.dil v μ ≤ Cd * (Work.BoseFixR.dil v μ) ^ (1 : ℝ)
        rw [Real.rpow_one])
    (mul_nonneg hCd0 hdil0.le)
  have hslot : Car * μ ^ 2 * R ^ 2 * (Work.BoseBox.sideAt μ (BoseGases.a v)) ^ 3
        * Work.BoseFixR.dil v μ / BoseGases.a v ≤ Work.BoseFixR.errKafz v R μ Car := by
    have h := errKafz_ge_slot (v := v) (R := R) (μ := μ) (C := Car) hμpos hav hR.le hCar0
    simpa only [Work.BoseFixR.ell] using h
  have hbr : (2 * (Work.BoseBox.sideAt μ (BoseGases.a v) ^ 3)⁻¹
          * (4 * A + Cd * Work.BoseFixR.dil v μ * (|W1| + |W1w|)) * (n : ℝ) ^ 2
        + 2 * μ * (A + Cd * Work.BoseFixR.dil v μ * |W1|) * Real.sqrt ((n : ℝ) * 𝓜)
        + 2 * μ * |W1| * (Cd * Work.BoseFixR.dil v μ) * (n : ℝ))
      ≤ (1 / 2) * Work.BoseFixR.errKafz v R μ Car := by
    have h2 : (1 / 2) * (Car * μ ^ 2 * R ^ 2 * (Work.BoseBox.sideAt μ (BoseGases.a v)) ^ 3
          * Work.BoseFixR.dil v μ / BoseGases.a v)
        ≤ (1 / 2) * Work.BoseFixR.errKafz v R μ Car :=
      mul_le_mul_of_nonneg_left hslot (by norm_num)
    have heq : (1 / 2) * (Car * μ ^ 2 * R ^ 2 * (Work.BoseBox.sideAt μ (BoseGases.a v)) ^ 3
          * Work.BoseFixR.dil v μ / BoseGases.a v)
        = (1 / 2) * Car * μ ^ 2 * R ^ 2 * (Work.BoseBox.sideAt μ (BoseGases.a v)) ^ 3
          * Work.BoseFixR.dil v μ / BoseGases.a v := by ring
    linarith [harith', h2, heq]
  have hH0 : 0 ≤ (∫ x in Submission.BoseGases.abox n (Work.BoseBox.sideAt μ (BoseGases.a v)),
      (Φ x) ^ 2) := integral_nonneg_of_ae (Filter.Eventually.of_forall fun x => sq_nonneg _)
  -- the coefficient identities
  have hEW1 : E.W1 0 = W1 := by
    rw [hW1def]
    exact honest_E_W1_zero v h fc fu HM μ hμpos hav
  have hEW1w : E.W1omega0 = W1w := rfl
  have hEpow : E.ell ^ (-(3 : ℝ)) = (Work.BoseBox.sideAt μ (BoseGases.a v) ^ 3)⁻¹ := by
    rw [show E.ell = Work.BoseBox.sideAt μ (BoseGases.a v) from rfl,
      show (-(3 : ℝ)) = -(↑(3 : ℕ) : ℝ) from by norm_num,
      Real.rpow_neg (le_of_lt hSp), Real.rpow_natCast]
  have hbridge : (∫ x : Submission.BoseGases.X n, star (Θ x)
        * potChiLin (fun T => Work.BoseDict.boxSlotSum e T) (HM μ).f (HM μ).g E Θ x).re
      = (Work.BoseDict.cIPn n (boxRestrictC (Work.BoseBox.sideAt μ (BoseGases.a v)) Φ)
          (potChiLinSummed (fun T => Work.BoseDict.boxSlotSum e T)
            (∑ k : Lab (HM μ).N, E.hatChi k • (HM μ).f k)
            (∑ s ∈ Work.BoseB7.excited (Lab (HM μ).N), E.hatChiSq s • (HM μ).g s) E
            (boxRestrictC (Work.BoseBox.sideAt μ (BoseGases.a v)) Φ))).re := by
    rw [hsum]
    rfl
  have heval' : (Work.BoseDict.cIPn n (boxRestrictC (Work.BoseBox.sideAt μ (BoseGases.a v)) Φ)
          (potChiLinSummed (fun T => Work.BoseDict.boxSlotSum e T)
            (∑ k : Lab (HM μ).N, E.hatChi k • (HM μ).f k)
            (∑ s ∈ Work.BoseB7.excited (Lab (HM μ).N), E.hatChiSq s • (HM μ).g s) E
            (boxRestrictC (Work.BoseBox.sideAt μ (BoseGases.a v)) Φ))).re
      = (E.ell ^ (-(3 : ℝ)) * E.W1 0)
            * pairSlot n (Work.BoseBox.sideAt μ (BoseGases.a v))
                (chiW (Work.BoseBox.sideAt μ (BoseGases.a v)) (HM μ).N) Φ
        - (E.mu * E.W1 0) * muForm n (Work.BoseBox.sideAt μ (BoseGases.a v))
                (chiW (Work.BoseBox.sideAt μ (BoseGases.a v)) (HM μ).N) Φ
        + (E.ell ^ (-(3 : ℝ)) * E.W1omega0)
            * pairSlot n (Work.BoseBox.sideAt μ (BoseGases.a v))
                (thW (Work.BoseBox.sideAt μ (BoseGases.a v)) (HM μ).N) Φ := by
    simpa only [potChiLinSummed, Pi.add_apply, Pi.sub_apply, Pi.smul_apply,
      Function.comp_apply] using heval
  have hreorder : ((Work.BoseBox.sideAt μ (BoseGases.a v) ^ 3)⁻¹ * W1
            * pairSlot n (Work.BoseBox.sideAt μ (BoseGases.a v))
                (chiW (Work.BoseBox.sideAt μ (BoseGases.a v)) (HM μ).N) Φ
        - μ * W1 * muForm n (Work.BoseBox.sideAt μ (BoseGases.a v))
                (chiW (Work.BoseBox.sideAt μ (BoseGases.a v)) (HM μ).N) Φ
        + (Work.BoseBox.sideAt μ (BoseGases.a v) ^ 3)⁻¹ * W1w
            * pairSlot n (Work.BoseBox.sideAt μ (BoseGases.a v))
                (thW (Work.BoseBox.sideAt μ (BoseGases.a v)) (HM μ).N) Φ)
      = ((Work.BoseBox.sideAt μ (BoseGases.a v) ^ 3)⁻¹ * W1
            * pairSlot n (Work.BoseBox.sideAt μ (BoseGases.a v))
                (chiW (Work.BoseBox.sideAt μ (BoseGases.a v)) (HM μ).N) Φ
        + (Work.BoseBox.sideAt μ (BoseGases.a v) ^ 3)⁻¹ * W1w
            * pairSlot n (Work.BoseBox.sideAt μ (BoseGases.a v))
                (thW (Work.BoseBox.sideAt μ (BoseGases.a v)) (HM μ).N) Φ
        - μ * W1 * muForm n (Work.BoseBox.sideAt μ (BoseGases.a v))
                (chiW (Work.BoseBox.sideAt μ (BoseGases.a v)) (HM μ).N) Φ) := by ring
  rw [hbridge, heval', hEpow, hEW1, hEW1w, hEmu, hreorder]
  refine le_trans hcmp ?_
  have hh := mul_le_mul_of_nonneg_right hbr hH0
  rw [Work.BoseBoxFix.normB, Work.BoseKinLoc.sqNormB]
  linarith
