import ChallengeDeps
import Mathlib.Algebra.Order.Star.Real
import Submission.Work.BoseB1Cube.CubeCrudeGood
import Submission.Work.BoseFixB1B.oneBodyKineticHalfCube_of_mainWord
import Submission.Work.BoseFixB1C.kineticHalfCubeLeMainWord
import Submission.Work.BoseFixB1S.sbWordCubeIntegrable
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission.Work.BoseB1Cube.CrudePlanAux` — the lead's weak-trim ledger, upstream of the target

The three residual predicates of the lead's design for `Work.BoseB1Cube.cubeCrudeBand_holds`:

* `CubeTrimWeak` (**L1**) — FS `eq:badset` with the outer band paid by the particle number;
* `CountAbsorb` (**L2**) — FS's `U`-argument (the count is absorbed by the mean-field scale,
  `R_Ψ` and the excited count);
* `BandErrSmall` (**L3**) — the band error coefficient is smaller than every fixed multiple of
  `a v`;

and the proved pure-real ledger + the analytic assembly

* `ledger_weak` (PROVED, copy of the lead's `cbc/bose_crudeband_assembly.lean`),
* `aprioriUnif_of_weak` (PROVED, same source): `CubePerBox` + `SlidingBCube` + L1 + L2 + L3
  `⟹ AprioriUnif v h`.

This module is deliberately **upstream** of `Submission.Work.BoseB1Cube.cubeCrudeBand_holds`
(the target's file imports it, not the other way round), so that the three leaves L1–L3 can be
proved in their own modules and consumed by the target's file.
-/

noncomputable section
open MeasureTheory Metric Filter
open scoped Topology Real BigOperators ENNReal

namespace Work.BoseB1Cube.CrudePlan

open _root_.BoseGases Submission.BoseGases Work.BoseBoxFix Work.BoseBox Work.UBB Work.BoseFixB1

local notation "E3" => EuclideanSpace ℝ (Fin 3)

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 4000000

/-- The band error coefficient `B(μ) = bandK·bandS²·|bandSet|`. -/
def bandErr (v : E3 → ℝ) (h : ScatSol v) (μ : ℝ) : ℝ :=
  bandK v h (paramsAt μ (a v)).M
    * bandS (paramsAt μ (a v)).M (sideAt μ (a v)) (paramsAt μ (a v)).d μ ^ 2
    * (volume (Work.SmallBoxSliding.bandSet (sideAt μ (a v)) (paramsAt μ (a v)).d μ)).toReal

lemma bandErr_nonneg (v : E3 → ℝ) (h : ScatSol v) (μ : ℝ) : 0 ≤ bandErr v h μ :=
  mul_nonneg (mul_nonneg (bandK_nonneg _) (sq_nonneg _)) ENNReal.toReal_nonneg

/-- **(L1) Weak trim**: FS `eq:badset` with the outer band paid by the *particle number*,
`∫_{cube∖goodSet} sbWordCube ≥ −μ·B(μ)·n·‖Φ‖²` (from `sbWordCube_ge_neg_bandCount` + `boxCount ≤ n‖Φ‖²`,
no lowness), the layer `goodSet ∖ interiorSet` by `CubeCrudeGood`, and `≥ 0` off the cube. -/
def CubeTrimWeak (v : E3 → ℝ) (h : ScatSol v) : Prop :=
  ∃ ε₀ C : ℝ, 0 < ε₀ ∧ 0 ≤ C ∧
    ∀ (J μ : ℝ), Adm v ε₀ μ → J ≤ (paramsAt μ (a v)).KB ^ 3 →
      ∀ (n : ℕ) (Φ : Work.BoseKinLoc.BoxState n (sideAt μ (a v))), IsLowB v h J μ n Φ →
        (∫ u in Work.SmallBoxSliding.interiorSet (sideAt μ (a v)) (paramsAt μ (a v)).d μ,
            Work.BoseFixB1B.sbWordCube v h μ u (Φ : X n → ℝ))
          ≤ (∫ u : E3, Work.BoseFixB1B.sbWordCube v h μ u (Φ : X n → ℝ))
            + C * (μ ^ 2 * (a v) * sideAt μ (a v) ^ 3 * (paramsAt μ (a v)).KB ^ 3
                    * (μ * (a v) ^ 3) ^ (1 / 2 : ℝ)) * normB v μ n (Φ : X n → ℝ)
            + μ * bandErr v h μ * (n : ℝ) * normB v μ n (Φ : X n → ℝ)

/-- **(L2) Count absorption** (FS's `U`-argument, linear form; no lowness): `μa·n ≲ μ²aℓ³ + R_Ψ + μa⟨n₊⟩`.
From `WB.jensen_integrated`, `psiWeight 1 μ t ≥ μt/3 − μ²`, `WB.sig_eq`, `WB.pq_split_meas` (ε = 1/2),
`WB.U_facts`, `WB.wbW_lower` (`W ≥ πaℓ³`) and `KU/W ≤ C/ℓ³`. -/
def CountAbsorb (v : E3 → ℝ) (h : ScatSol v) : Prop :=
  ∃ ε₀ C : ℝ, 0 < ε₀ ∧ 0 ≤ C ∧
    ∀ μ : ℝ, Adm v ε₀ μ → ∀ (n : ℕ) (Φ : Work.BoseKinLoc.BoxState n (sideAt μ (a v))),
      μ * (a v) * (n : ℝ) * normB v μ n (Φ : X n → ℝ)
        ≤ C * (μ ^ 2 * (a v) * sideAt μ (a v) ^ 3 * normB v μ n (Φ : X n → ℝ)
                + RPsi v h μ (Φ : X n → ℝ)
                + μ * (a v) * cnPlus (sideAt μ (a v)) (Φ : X n → ℝ))

/-- **(L3) The band error is small** (pure parameter arithmetic: `B(μ)/a ≲ t^{11.9}` at `M = 48`). -/
def BandErrSmall (v : E3 → ℝ) (h : ScatSol v) : Prop :=
  ∀ C : ℝ, 0 ≤ C → ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ μ : ℝ, Adm v ε₀ μ →
    C * bandErr v h μ ≤ a v * ((paramsAt μ (a v)).KB ^ 3 * (μ * (a v) ^ 3) ^ (1 / 2 : ℝ)) ∧
    C * bandErr v h μ * (paramsAt μ (a v)).Kl ^ 2 ≤ a v ∧
    C * bandErr v h μ ≤ a v

/-- The pure-real ledger of `aprioriUnif_of_weak`. -/
lemma ledger_weak {c₁ CS CI CW CT C0 Cb A κ N R I Iint Wint W cP P Q B aa μ L Kl2 bb J s : ℝ}
    (hc₁ : 0 < c₁) (hCS : 1 ≤ CS) (hCI : 0 ≤ CI) (hCW : 0 ≤ CW) (hCT : 0 ≤ CT) (hC0 : 0 ≤ C0)
    (hA : 0 ≤ A) (hκ : 0 ≤ κ) (hN : 0 ≤ N) (hR : 0 ≤ R) (hcP : 0 ≤ cP) (hB : 0 ≤ B)
    (haa : 0 < aa) (hμ : 0 < μ) (hL : 0 < L) (hbb : 0 < bb)
    (h1 : c₁ * R ≤ Iint + (1 / 2) * μ ^ 2 * Wint * N + CI * (A * κ) * N)
    (h2 : (1 / 2) * μ ^ 2 * Wint ≤ 4 * π * A * (1 + CW * κ))
    (h3 : Iint ≤ I + CT * (A * κ) * N + P)
    (hPQ : aa * P = B * Q)
    (h4 : Q ≤ C0 * (A * N + R + μ * aa * cP))
    (h5 : (bb / (2 * L)) * cP + (1 / CS) * I ≤ W)
    (h6 : W ≤ -(4 * π * A * (1 - J * s)) * N)
    (hJs : J * s ≤ κ)
    (hKl : μ * aa * L = Kl2)
    (hCb1 : C0 ≤ Cb) (hCb2 : 2 * C0 / c₁ ≤ Cb) (hCb3 : 4 * C0 / bb ≤ Cb)
    (hE1 : Cb * B ≤ aa * κ) (hE2 : Cb * B * Kl2 ≤ aa) (hE3 : Cb * B ≤ aa) :
    R ≤ (2 * (4 * π * (CS + CW) + CI + CT + 1) / c₁) * (A * κ) * N ∧
    (bb / (2 * L)) * cP ≤ (2 * (4 * π * (CS + CW) + CI + CT + 1)) * (A * κ) * N := by
  have hCbn : 0 ≤ Cb := le_trans hC0 hCb1
  -- `C0·B ≤ aκ`, `C0·B ≤ a·c₁/2`, `C0·B·μ ≤ bb/(4L)`
  have hk1 : C0 * B ≤ aa * κ := le_trans (mul_le_mul_of_nonneg_right hCb1 hB) hE1
  have hk2 : C0 * B ≤ aa * (c₁ / 2) := by
    have : (2 * C0 / c₁) * B ≤ aa := le_trans (mul_le_mul_of_nonneg_right hCb2 hB) hE3
    have he : (2 * C0 / c₁) * B = (C0 * B) * (2 / c₁) := by ring
    rw [he] at this
    have h2c : 0 < 2 / c₁ := by positivity
    have := (le_div_iff₀ h2c).mpr this
    calc C0 * B ≤ aa / (2 / c₁) := this
      _ = aa * (c₁ / 2) := by field_simp
  have hk3 : C0 * B * μ * aa ≤ aa * (bb / (4 * L)) := by
    have h0 : (4 * C0 / bb) * B * Kl2 ≤ aa := by
      have hK0 : 0 ≤ Kl2 := by rw [← hKl]; positivity
      exact le_trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hCb3 hB) hK0) hE2
    rw [← hKl] at h0
    have he : (4 * C0 / bb) * B * (μ * aa * L) = (C0 * B * μ * aa) * (4 * L / bb) := by
      field_simp
    rw [he] at h0
    have hp : 0 < 4 * L / bb := by positivity
    have := (le_div_iff₀ hp).mpr h0
    calc C0 * B * μ * aa ≤ aa / (4 * L / bb) := this
      _ = aa * (bb / (4 * L)) := by field_simp
  -- `P ≤ κ·A·N + (c₁/2)R + (bb/(4L))cP`
  have hP : P ≤ κ * A * N + (c₁ / 2) * R + (bb / (4 * L)) * cP := by
    have hBQ : B * Q ≤ C0 * B * (A * N) + C0 * B * R + C0 * B * μ * aa * cP := by
      have := mul_le_mul_of_nonneg_left h4 hB
      nlinarith [this]
    have hAN : 0 ≤ A * N := mul_nonneg hA hN
    have t1 := mul_le_mul_of_nonneg_right hk1 hAN
    have t2 := mul_le_mul_of_nonneg_right hk2 hR
    have t3 := mul_le_mul_of_nonneg_right hk3 hcP
    have haP : aa * P ≤ aa * (κ * A * N + (c₁ / 2) * R + (bb / (4 * L)) * cP) := by
      rw [hPQ]; nlinarith [hBQ, t1, t2, t3]
    exact le_of_mul_le_mul_left haP haa
  -- the sliding bound turned around
  have hCSpos : 0 < CS := lt_of_lt_of_le one_pos hCS
  have hI : I ≤ CS * W - CS * ((bb / (2 * L)) * cP) := by
    have : (1 / CS) * I ≤ W - (bb / (2 * L)) * cP := by linarith
    have h' := mul_le_mul_of_nonneg_left this hCSpos.le
    have he : CS * ((1 / CS) * I) = I := by field_simp
    nlinarith [h', he]
  have hW' : CS * W ≤ CS * (-(4 * π * A * (1 - κ)) * N) := by
    have : W ≤ -(4 * π * A * (1 - κ)) * N := by
      have hAN : 0 ≤ 4 * π * A * N := by positivity
      nlinarith [h6, hJs, hAN]
    exact mul_le_mul_of_nonneg_left this hCSpos.le
  have hAκN : 0 ≤ A * κ * N := by positivity
  have hmass : (1 / 2) * μ ^ 2 * Wint * N ≤ 4 * π * A * (1 + CW * κ) * N :=
    mul_le_mul_of_nonneg_right h2 hN
  have hcPL : 0 ≤ (bb / (4 * L)) * cP := by positivity
  have hsplit : (bb / (2 * L)) * cP = 2 * ((bb / (4 * L)) * cP) := by field_simp; ring
  set K := 4 * π * (CS + CW) + CI + CT + 1 with hK
  have hmain : (c₁ / 2) * R + (CS * 2 - 1) * ((bb / (4 * L)) * cP)
      ≤ K * (A * κ * N) - 4 * π * A * N * (CS - 1) := by
    rw [hsplit] at hI
    have e1 : CS * (-(4 * π * A * (1 - κ)) * N) = -(CS * 4 * π * A * N) + CS * 4 * π * (A * κ * N) := by ring
    have e2 : 4 * π * A * (1 + CW * κ) * N = 4 * π * A * N + 4 * π * CW * (A * κ * N) := by ring
    have e3 : CI * (A * κ) * N = CI * (A * κ * N) := by ring
    have e4 : CT * (A * κ) * N = CT * (A * κ * N) := by ring
    have e5 : κ * A * N = A * κ * N := by ring
    rw [hK]; nlinarith [h1, h3, hP, hI, hW', hmass, e1, e2, e3, e4, e5]
  have hpi : 0 ≤ 4 * π * A * N * (CS - 1) := by
    have : 0 ≤ CS - 1 := by linarith
    positivity
  have hK0 : 0 ≤ K := by rw [hK]; positivity
  constructor
  · have : (c₁ / 2) * R ≤ K * (A * κ * N) := by nlinarith [hmain, hpi, hcPL, hCS]
    have hc2 : 0 < c₁ / 2 := by positivity
    have := (le_div_iff₀' hc2).mpr this
    calc R ≤ K * (A * κ * N) / (c₁ / 2) := by rwa [div_eq_mul_inv, mul_comm] at this ⊢
      _ = (2 * K / c₁) * (A * κ) * N := by field_simp
  · have : (bb / (4 * L)) * cP ≤ K * (A * κ * N) := by nlinarith [hmain, hpi, hcPL, hCS, hR, hc₁]
    calc (bb / (2 * L)) * cP = 2 * ((bb / (4 * L)) * cP) := hsplit
      _ ≤ 2 * (K * (A * κ * N)) := by linarith
      _ = (2 * K) * (A * κ) * N := by ring


/-- **AprioriUnif from the weak trim** (no `CubeTrim`, no `CubeCrudeBand`). -/
theorem aprioriUnif_of_weak {v : E3 → ℝ} (h : ScatSol v) (hv : 0 ≤ v)
    (hv1 : MeasureTheory.MemLp v 1) (hvrad : _root_.BoseGases.IsRadial v) {R : ℝ} (hR : 0 < R)
    (hv_supp : tsupport v ⊆ Metric.ball (0 : E3) R) (hav : 0 < a v)
    (hF : CubePerBox v h R) (hS : Work.BoseFixB1B.SlidingBCube v h)
    (hT : CubeTrimWeak v h) (hN : CountAbsorb v h) (hE : BandErrSmall v h) :
    Work.BoseFixB1S.AprioriUnif v h := by
  obtain ⟨εi, hεi, hInt⟩ := Work.BoseFixB1S.sbWordCubeIntegrable h hv hv1 hvrad hR hv_supp hav
  obtain ⟨εI, c₁, CI, hεI, hc₁, hc₁1, hCI, hI⟩ :=
    Work.BoseFixB1S.perBoxIntegratedUnifCube h hv hv1 hvrad hR hv_supp hav
      (cubePerBoxInterior_of_cubePerBox hF)
      ⟨εi, hεi, fun μ hA {n} Φ => (hInt μ hA Φ).integrableOn⟩
  obtain ⟨εW, CW, hεW, hCW, hW⟩ := cubeMassLaw_holds h hv hv1 hvrad hR hv_supp hav
  obtain ⟨εS, CS, hCS1, hεS, hSfun⟩ := hS
  obtain ⟨εT, CT, hεT, hCT, hTfun⟩ := hT
  obtain ⟨εN, C0, hεN, hC0, hNfun⟩ := hN
  set Cb : ℝ := C0 + 2 * C0 / c₁ + 4 * C0 / bValue with hCbdef
  have hbV : (0 : ℝ) < bValue := by norm_num [bValue]
  have hCb0 : 0 ≤ Cb := by rw [hCbdef]; positivity
  obtain ⟨εE, hεE, hEfun⟩ := hE Cb hCb0
  set K : ℝ := 4 * π * (CS + CW) + CI + CT + 1 with hK
  refine ⟨max 1 (max (2 * K / c₁) (2 * K)),
    min (min (min εI εW) (min εS εT)) (min εN εE), le_max_left _ _, by
      refine lt_min (lt_min (lt_min hεI hεW) (lt_min hεS hεT)) (lt_min hεN hεE), ?_⟩
  intro J μ hAdm hJK n Φ hlow
  have m1 : ∀ {x y z w p q : ℝ}, min (min (min x y) (min z w)) (min p q) ≤ x := fun {x y z w p q} =>
    le_trans (min_le_left _ _) (le_trans (min_le_left _ _) (min_le_left _ _))
  have hAI : Adm v εI μ := Adm.mono hAdm m1
  have hAW : Adm v εW μ := Adm.mono hAdm
    (le_trans (min_le_left _ _) (le_trans (min_le_left _ _) (min_le_right _ _)))
  have hAS : Adm v εS μ := Adm.mono hAdm
    (le_trans (min_le_left _ _) (le_trans (min_le_right _ _) (min_le_left _ _)))
  have hAT : Adm v εT μ := Adm.mono hAdm
    (le_trans (min_le_left _ _) (le_trans (min_le_right _ _) (min_le_right _ _)))
  have hAN : Adm v εN μ := Adm.mono hAdm (le_trans (min_le_right _ _) (min_le_left _ _))
  have hAE : Adm v εE μ := Adm.mono hAdm (le_trans (min_le_right _ _) (min_le_right _ _))
  have hμ : 0 < μ := adm_mu_pos hAdm
  have hℓ : 0 < sideAt μ (a v) := adm_ell_pos hAdm
  have hd : 0 < (paramsAt μ (a v)).d := adm_d_pos hAdm
  have hM1 : 1 ≤ (paramsAt μ (a v)).M := by rw [M_eq_mValue]; norm_num [Work.BoseBox.mValue]
  have hKB : 0 < (paramsAt μ (a v)).KB := paramsAt_KB_pos hAdm
  have ht : 0 ≤ μ * (a v) ^ 3 := (mul_pos hμ (pow_pos hav 3)).le
  have hRnn : 0 ≤ RPsi v h μ (Φ : X n → ℝ) :=
    Work.BoseFixB1.rPsiB_nonneg (v := v) (h := h) (μ := μ)
      (M := (paramsAt μ (a v)).M) (c := 1) (ℓ := sideAt μ (a v))
      (d := (paramsAt μ (a v)).d) (n := n) hv hv1 hvrad hR hv_supp
      hμ hM1 (by norm_num) hℓ hd (Φ : X n → ℝ)
  have hNB : 0 ≤ normB v μ n (Φ : X n → ℝ) := normB_nonneg _
  have hcP : 0 ≤ cnPlus (sideAt μ (a v)) (Φ : X n → ℝ) := by
    rw [cnPlus]; exact Finset.sum_nonneg fun i _ => integral_nonneg fun x => sq_nonneg _
  obtain ⟨hE1, hE2, hE3⟩ := hEfun μ hAE
  have hJs : J * Real.sqrt (μ * (a v) ^ 3)
      ≤ (paramsAt μ (a v)).KB ^ 3 * (μ * (a v) ^ 3) ^ (1 / 2 : ℝ) := by
    rw [← Real.sqrt_eq_rpow]
    exact mul_le_mul_of_nonneg_right hJK (Real.sqrt_nonneg _)
  have hlow' := (isLowB_iff (h := h) (J := J) (μ := μ) (n := n) (Φ := (Φ : X n → ℝ)) hav).mp hlow
  have h1 := hI μ hAI n Φ
  have hLed := ledger_weak (c₁ := c₁) (CS := CS) (CI := CI) (CW := CW) (CT := CT) (C0 := C0) (Cb := Cb)
    (A := μ ^ 2 * (a v) * sideAt μ (a v) ^ 3)
    (κ := (paramsAt μ (a v)).KB ^ 3 * (μ * (a v) ^ 3) ^ (1 / 2 : ℝ))
    (N := normB v μ n (Φ : X n → ℝ)) (R := RPsi v h μ (Φ : X n → ℝ))
    (I := ∫ u : E3, Work.BoseFixB1B.sbWordCube v h μ u (Φ : X n → ℝ))
    (Iint := ∫ u in Work.SmallBoxSliding.interiorSet (sideAt μ (a v)) (paramsAt μ (a v)).d μ,
        Work.BoseFixB1B.sbWordCube v h μ u (Φ : X n → ℝ))
    (Wint := ∫ u in Work.SmallBoxSliding.interiorSet (sideAt μ (a v)) (paramsAt μ (a v)).d μ,
        Work.BoseFixB1.w1MassB h (paramsAt μ (a v)).M (sideAt μ (a v)) (paramsAt μ (a v)).d u)
    (W := wordB v h μ n (Φ : X n → ℝ)) (cP := cnPlus (sideAt μ (a v)) (Φ : X n → ℝ))
    (P := μ * bandErr v h μ * (n : ℝ) * normB v μ n (Φ : X n → ℝ))
    (Q := μ * (a v) * (n : ℝ) * normB v μ n (Φ : X n → ℝ))
    (B := bandErr v h μ) (aa := a v) (μ := μ) (L := sideAt μ (a v) ^ 2)
    (Kl2 := (paramsAt μ (a v)).Kl ^ 2) (bb := (paramsAt μ (a v)).b)
    (J := J) (s := Real.sqrt (μ * (a v) ^ 3))
    hc₁ hCS1 hCI hCW hCT hC0 (by positivity) (by positivity) hNB hRnn hcP (bandErr_nonneg v h μ)
    hav hμ (by positivity) (paramsAt_b_pos μ (a v))
    (by
      have e : CI * (μ ^ 2 * a v * sideAt μ (a v) ^ 3 * (paramsAt μ (a v)).KB ^ 3
            * (μ * a v ^ 3) ^ (1 / 2 : ℝ)) * normB v μ n (Φ : X n → ℝ)
          = CI * (μ ^ 2 * a v * sideAt μ (a v) ^ 3 * ((paramsAt μ (a v)).KB ^ 3
            * (μ * a v ^ 3) ^ (1 / 2 : ℝ))) * normB v μ n (Φ : X n → ℝ) := by ring
      linarith [h1, e])
    (by
      have h2 := hW μ hAW
      have hμ2 : 0 ≤ (1 / 2) * μ ^ 2 := by positivity
      have := mul_le_mul_of_nonneg_left h2 hμ2
      nlinarith [this])
    (by
      have h3 := hTfun J μ hAT hJK n Φ hlow
      have e : CT * (μ ^ 2 * a v * sideAt μ (a v) ^ 3 * (paramsAt μ (a v)).KB ^ 3
            * (μ * a v ^ 3) ^ (1 / 2 : ℝ)) * normB v μ n (Φ : X n → ℝ)
          = CT * (μ ^ 2 * a v * sideAt μ (a v) ^ 3 * ((paramsAt μ (a v)).KB ^ 3
            * (μ * a v ^ 3) ^ (1 / 2 : ℝ))) * normB v μ n (Φ : X n → ℝ) := by ring
      linarith [h3, e])
    (by unfold bandErr; ring)
    (by
      have h4 := hNfun μ hAN n Φ
      have e : μ ^ 2 * a v * sideAt μ (a v) ^ 3 * normB v μ n (Φ : X n → ℝ)
          = μ ^ 2 * a v * sideAt μ (a v) ^ 3 * normB v μ n (Φ : X n → ℝ) := rfl
      linarith [h4])
    (by
      have := hSfun μ hAS n Φ
      have e : (paramsAt μ (a v)).b / (2 * sideAt μ (a v) ^ 2) * cnPlus (sideAt μ (a v)) (Φ : X n → ℝ)
          = (paramsAt μ (a v)).b / (2 * sideAt μ (a v) ^ 2) * cnPlus (sideAt μ (a v)) (Φ : X n → ℝ) := rfl
      linarith [this])
    (by
      have e : 4 * π * μ ^ 2 * a v * sideAt μ (a v) ^ 3 = 4 * π * (μ ^ 2 * a v * sideAt μ (a v) ^ 3) := by ring
      rw [← e]; exact hlow')
    hJs (mu_mul_a_mul_ell_sq μ (a v) hμ hav)
    (by rw [hCbdef]; have : 0 ≤ 2 * C0 / c₁ + 4 * C0 / bValue := by positivity
        linarith)
    (by rw [hCbdef]; have : 0 ≤ 4 * C0 / bValue := by positivity
        linarith)
    (by rw [hCbdef, paramsAt_b_eq]; have : 0 ≤ C0 + 2 * C0 / c₁ := by positivity
        linarith)
    hE1 hE2 hE3
  obtain ⟨hL1, hL2⟩ := hLed
  have hAκN : 0 ≤ μ ^ 2 * a v * sideAt μ (a v) ^ 3 * (paramsAt μ (a v)).KB ^ 3
      * (μ * a v ^ 3) ^ (1 / 2 : ℝ) := by positivity
  refine ⟨hRnn, ?_, ?_⟩
  · calc RPsi v h μ (Φ : X n → ℝ)
        ≤ (2 * K / c₁) * (μ ^ 2 * a v * sideAt μ (a v) ^ 3 * ((paramsAt μ (a v)).KB ^ 3
            * (μ * a v ^ 3) ^ (1 / 2 : ℝ))) * normB v μ n (Φ : X n → ℝ) := by rw [hK]; exact hL1
      _ ≤ max 1 (max (2 * K / c₁) (2 * K)) * (μ ^ 2 * a v * sideAt μ (a v) ^ 3
            * (paramsAt μ (a v)).KB ^ 3 * (μ * a v ^ 3) ^ (1 / 2 : ℝ)) * normB v μ n (Φ : X n → ℝ) := by
          rw [show μ ^ 2 * a v * sideAt μ (a v) ^ 3 * ((paramsAt μ (a v)).KB ^ 3
            * (μ * a v ^ 3) ^ (1 / 2 : ℝ)) = μ ^ 2 * a v * sideAt μ (a v) ^ 3
            * (paramsAt μ (a v)).KB ^ 3 * (μ * a v ^ 3) ^ (1 / 2 : ℝ) by ring]
          exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
            (le_trans (le_max_left _ _) (le_max_right _ _)) hAκN) hNB
  · calc (paramsAt μ (a v)).b / (2 * sideAt μ (a v) ^ 2) * cnPlus (sideAt μ (a v)) (Φ : X n → ℝ)
        ≤ (2 * K) * (μ ^ 2 * a v * sideAt μ (a v) ^ 3 * ((paramsAt μ (a v)).KB ^ 3
            * (μ * a v ^ 3) ^ (1 / 2 : ℝ))) * normB v μ n (Φ : X n → ℝ) := by rw [hK]; exact hL2
      _ ≤ max 1 (max (2 * K / c₁) (2 * K)) * (μ ^ 2 * a v * sideAt μ (a v) ^ 3
            * (paramsAt μ (a v)).KB ^ 3 * (μ * a v ^ 3) ^ (1 / 2 : ℝ)) * normB v μ n (Φ : X n → ℝ) := by
          rw [show μ ^ 2 * a v * sideAt μ (a v) ^ 3 * ((paramsAt μ (a v)).KB ^ 3
            * (μ * a v ^ 3) ^ (1 / 2 : ℝ)) = μ ^ 2 * a v * sideAt μ (a v) ^ 3
            * (paramsAt μ (a v)).KB ^ 3 * (μ * a v ^ 3) ^ (1 / 2 : ℝ) by ring]
          exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
            (le_trans (le_max_right _ _) (le_max_right _ _)) hAκN) hNB


end Work.BoseB1Cube.CrudePlan
