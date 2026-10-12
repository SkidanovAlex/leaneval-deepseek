import ChallengeDeps
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Submission.Work.BoseFixB3.CS.Pieces.CS_side_hyps_integrable
import Submission.Work.BoseFixB3.CS.Pieces.Fmass_le_highMass_pos
import Submission.Work.BoseFixB3.CS.Pieces.ellAt_kapAt_rpow_general
import Submission.Work.BoseFixB3.CS.Pieces.leakCoupl_le_v2
import Submission.Work.BoseFixB3.CS.Pieces.ppMass_le_q4Mass_add_card_mul_cnPlus
import Submission.Work.BoseFixB3.CS.Pieces.q3bar_add_q3om_eq_v3
import Submission.Work.BoseFixB3.CS.Pieces.qcross_bar_om_pair_sum_weighted
import Submission.Work.BoseFixB3.CS.Pieces.sMass_w1_le_cnPlus
import Submission.Work.BoseFixB3.Eps.sideAt_ge_of_dilute
import Submission.Work.BoseFixB3.HighMass.highMass_le_nPlusHB
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixB3.CS.b3CSRoot_holds` — FS `eq:pq'pp-sf` (`cl:advQ3sch` with `Q' = Q̄_L`)

The `CS` step of the `B3` chapter (see `CS/B3CSRoot_ANALYSIS.md`, `CS/SESSION4_HANDOFF.md`).
The statement is FS `eq:pq'pp-sf`:

    q3bar + ¼q4word + (b/200)ℓ⁻²n₊ + q3om ≥ −Kℓ⁻²K_ℓ⁴n₊^H ,     n ≤ 2μℓ³ ,

and the proof performed here is the *ledger*:

1. **decomposition** (`Pieces/q3bar_add_q3om_eq_v3`, FS `eq:3Qto4Q`):
   `q3bar + q3om = 2Σ_p∫F'_p(q4B_p − ω_pS_p)w₁ + 2·leakCoupl·ppMass`
   (the leakage appears because the corpus's `lowMult` is the free-space multiplier, so it
   does not annihilate the condensate);
2. **Cauchy–Schwarz** (`Pieces/qcross_bar_om_pair_sum_weighted`) with free `t = 8`, `ε`:
   pairs the `3Q` amplitude with the `4Q` bracket, consuming `(1/16)·Σ_p∫(q4B_p)²·w` and
   leaving `−(16 + 1/(2ε))·fMass − 2ε·sMass`;
3. **slot-constancy extraction** (`Pieces/extract_ppMass_le`): since
   `X_p = P_{p.1}P_{p.2}Φ` is constant in the slots `p.1, p.2`,
   `omegaSqCoupl·ppMass ≤ 2·q4Mass + 4·cMass + 4·sMassOm`, which pays the leakage
   `2·leakCoupl·ppMass` out of the *remaining* `4Q`-square, because
   `|leakCoupl| ≤ C(ℓκ)^{-N}ℓ³` is super-polynomially small (`Pieces/leakCoupl_le_v2`);
4. **mass bounds**: `fMass ≤ 2C_Fμ·n₊^H` (`Pieces/Fmass_le_highMass_pos` +
   `HighMass.highMass_le_nPlusHB`), `sMass ≤ 2C₁μ·n₊` (`Pieces/sMass_w1_le_cnPlus`),
   `cMass + sMassOm ≤ 2C_Mμ·n₊` (`Pieces/massCS_le_cnPlus`);
5. **arithmetic**: `ε := c₁K_ℓ^{-2}`, `c₁ ≤ ab/(3200C₁)`, `K` large enough
   (it may depend on `ε₀`), `N := 50`, and `ε₀` small enough for the two remaining
   leakage conditions `128C_L(ℓκ)^{-N} ≤ ∫vω²` and `12800C_LC_Mμℓ⁵(ℓκ)^{-N} ≤ b∫vω²`.
-/

noncomputable section

open scoped Real Topology BigOperators
open MeasureTheory Filter Metric

namespace Work.BoseFixB3.CS

open _root_.BoseGases Submission.BoseGases Work.UBB Work.BoseBox Work.BoseKinLoc
open Work.BoseBoxFix

set_option autoImplicit false
set_option maxHeartbeats 8000000

local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-- **The accounting core of the `CS` step.**  All the analytic inputs are hypotheses; the
proof is the bookkeeping of §1–4 of the module docstring, closed by `linarith`. -/
theorem csv_state_le {v : E3 → ℝ} {h : Work.UBB.ScatSol v} {R : ℝ} {fc : LowCut}
    (hv : 0 ≤ v) (hv1 : MeasureTheory.MemLp v 1 MeasureTheory.volume)
    (hvrad : BoseGases.IsRadial v) (hR : 0 < R)
    (hv_supp : tsupport v ⊆ Metric.ball 0 R) (hav : 0 < BoseGases.a v)
    {N : ℕ} (hN : 1 ≤ N) {CL CF C1 : ℝ} (hCL0 : 0 ≤ CL) (hCF0 : 0 ≤ CF)
    (hC10 : 0 ≤ C1)
    (hleak : ∀ (fc : LowCut) (κ ℓ : ℝ), 0 < κ → 0 < ℓ → R ≤ ℓ * chiR0 →
      |leakCoupl fc κ ℓ (omC (Classical.choose h)) (wLoc ℓ (g0 v h) 0)|
        ≤ CL * (ℓ * κ) ^ (-(N : ℝ)) * ℓ ^ 3)
    (hF : ∀ (n : ℕ) (ℓ : ℝ), 0 < ℓ → R ≤ ℓ * chiR0 → ∀ (fc : LowCut) (κ : ℝ), 0 < κ →
      ∀ {Φ : X n → ℝ}, Continuous Φ →
      fMass fc κ ℓ (wLoc ℓ (g0 v h) 0) Φ
        ≤ CF * (ℓ ^ 3)⁻¹ * (n : ℝ) * highMass fc κ ℓ Φ)
    (hsMass : ∀ (n : ℕ) (ℓ : ℝ), 0 < ℓ → R ≤ ℓ * chiR0 → ∀ {Φ : X n → ℝ}, Continuous Φ →
      sMass ℓ (wLoc ℓ (g0 v h) 0) Φ ≤ C1 * (ℓ ^ 3)⁻¹ * (n : ℝ) * cnPlus ℓ Φ)
    {ε₀ : ℝ} (hε₀ : 0 < ε₀) (hε₀1 : ε₀ ≤ 1)
    {μ : ℝ} (hadm : Adm v ε₀ μ)
    (hRℓ : R ≤ ellAt μ (a v) * chiR0)
    {c₁ ε K : ℝ} (hc₁ : 0 < c₁) (hε : 0 < ε) (hK0 : 0 ≤ K)
    {n : ℕ} (Φ : BoxState n (ellAt μ (a v)))
    (hn : (n : ℝ) ≤ 2 * μ * (ellAt μ (a v)) ^ 3)
    (hpay : 2 * |leakCoupl fc (kapAt μ (a v)) (ellAt μ (a v)) (omC (Classical.choose h))
            (wLoc (ellAt μ (a v)) (g0 v h) 0)|
          * ppMass (ellAt μ (a v)) (Φ : X n → ℝ)
        ≤ (1 / 64) * q4Mass (ellAt μ (a v)) (omC (Classical.choose h))
              (wLoc (ellAt μ (a v)) v 0) (Φ : X n → ℝ)
          + ((patAt μ (a v)).b / 1600) * (ellAt μ (a v)) ^ (-2 : ℤ)
              * cnPlus (ellAt μ (a v)) (Φ : X n → ℝ))
    (hN3 : (32 + 1 / ε) * CF * μ
      ≤ K * (ellAt μ (a v)) ^ (-2 : ℤ) * ((patAt μ (a v)).Kl) ^ 4)
    (hN4 : 4 * ε * C1 * μ ≤ (patAt μ (a v)).b / 800 * (ellAt μ (a v)) ^ (-2 : ℤ)) :
    q3barWord fc (kapAt μ (a v)) (ellAt μ (a v)) (wLoc (ellAt μ (a v)) (g0 v h) 0) (Φ : X n → ℝ)
      + (1 / 4) * q4word (ellAt μ (a v)) (wLoc (ellAt μ (a v)) v 0) (omC (Classical.choose h))
          (Φ : X n → ℝ)
      + (patAt μ (a v)).b / 200 * (ellAt μ (a v)) ^ (-2 : ℤ)
          * cnPlus (ellAt μ (a v)) (Φ : X n → ℝ)
      + q3omWord fc (kapAt μ (a v)) (ellAt μ (a v)) (wLoc (ellAt μ (a v)) (g0 v h) 0)
          (omC (Classical.choose h)) (Φ : X n → ℝ)
    ≥ - K * (ellAt μ (a v)) ^ (-2 : ℤ) * ((patAt μ (a v)).Kl) ^ 4
        * nPlusHB (ellAt μ (a v)) (patAt μ (a v)).d (Φ : X n → ℝ) := by
  -- abbreviations (only for `ℝ`-valued ledger entries; `ℓ`, `κ`, … stay literal because
  -- `Φ : BoxState n (ellAt μ (a v))` depends on them)
  set φ : X n → ℝ := (Φ : X n → ℝ) with hφ
  have hφc : Continuous φ := by rw [hφ]; exact Φ.contDiff.continuous
  set ρ₁ : ℝ := ∫ z : E3, v z * (Classical.choose h z) ^ 2 with hρ₁def
  set Aω : ℝ := omegaSqCoupl (ellAt μ (a v)) (omC (Classical.choose h))
      (wLoc (ellAt μ (a v)) v 0) with hAωdef
  set lam : ℝ := leakCoupl fc (kapAt μ (a v)) (ellAt μ (a v)) (omC (Classical.choose h))
      (wLoc (ellAt μ (a v)) (g0 v h) 0) with hlam
  set D : ℝ := q4Mass (ellAt μ (a v)) (omC (Classical.choose h))
      (wLoc (ellAt μ (a v)) v 0) φ with hD
  set cM : ℝ := cMass (ellAt μ (a v)) (wLoc (ellAt μ (a v)) v 0) φ with hcM
  set sMO : ℝ := sMassOm (ellAt μ (a v)) (omC (Classical.choose h))
      (wLoc (ellAt μ (a v)) v 0) φ with hsMO
  set sMO1 : ℝ := sMassOm (ellAt μ (a v)) (fun _ _ => 1) (wLoc (ellAt μ (a v)) v 0) φ with hsMO1
  set mF : ℝ := fMass fc (kapAt μ (a v)) (ellAt μ (a v))
      (wLoc (ellAt μ (a v)) (g0 v h) 0) φ with hmF
  set sM : ℝ := sMass (ellAt μ (a v)) (wLoc (ellAt μ (a v)) (g0 v h) 0) φ with hsM
  set high : ℝ := highMass fc (kapAt μ (a v)) (ellAt μ (a v)) φ with hhigh
  set nH : ℝ := nPlusHB (ellAt μ (a v)) (patAt μ (a v)).d φ with hnH
  set cn : ℝ := cnPlus (ellAt μ (a v)) φ with hcn
  set S1 : ℝ := ∑ p ∈ pairSet n, ∫ x in abox n (ellAt μ (a v)),
      highSlot fc (kapAt μ (a v)) (ellAt μ (a v)) p.2
          (aP (ellAt μ (a v)) p.1 (aQ (ellAt μ (a v)) p.2 φ)) x
        * (q4B (ellAt μ (a v)) (omC (Classical.choose h)) φ p x
            - Classical.choose h (x p.1 - x p.2)
              * (aP (ellAt μ (a v)) p.2 (aQ (ellAt μ (a v)) p.1 φ) x
                  + aQ (ellAt μ (a v)) p.2 (aP (ellAt μ (a v)) p.1 φ) x))
        * wLoc (ellAt μ (a v)) (g0 v h) 0 (x p.1) (x p.2) with hS1
  -- basic positivity and structural facts
  have hℓpos : 0 < ellAt μ (a v) := ellAt_pos μ (a v) hadm.1 hav
  have hℓ2pos : 0 < (ellAt μ (a v)) ^ (2 : ℕ) := pow_pos hℓpos 2
  have hℓ3pos : 0 < (ellAt μ (a v)) ^ (3 : ℕ) := pow_pos hℓpos 3
  have hℓ5pos : 0 < (ellAt μ (a v)) ^ (5 : ℕ) := pow_pos hℓpos 5
  have hdpos : 0 < (patAt μ (a v)).d := by
    rw [patAt_d]
    exact Work.BoseBox.fsXp_pos (mul_pos hadm.1 (pow_pos hav 3))
  have hκpos : 0 < kapAt μ (a v) := by
    have h : 0 < (paramsAt μ (a v)).d ^ 2 * sideAt μ (a v) :=
      mul_pos (pow_pos (by simpa [patAt] using hdpos) 2) (by simpa [ellAt] using hℓpos)
    rw [kapAt]
    exact inv_pos.mpr h
  have hbpos : 0 < (patAt μ (a v)).b := by rw [patAt_b]; exact bValue_pos
  have hKlnn : 0 ≤ ((patAt μ (a v)).Kl) ^ 4 := by positivity
  have hρ₁pos : 0 < ρ₁ := by
    rw [hρ₁def]
    exact (Pieces.v_w0_pos_sq hv hvrad hv1 R hR hv_supp hav h).2
  -- integrability of `w₀²·v`
  have hIntρ : MeasureTheory.Integrable
      (fun z : E3 => (Classical.choose h z) ^ 2 * v z) := by
    have hcomm : (fun z : E3 => (Classical.choose h z) ^ 2 * v z)
        = fun z : E3 => v z * (Classical.choose h z) ^ 2 := by
      funext z; ring
    rw [hcomm]
    obtain ⟨hrad, hw⟩ := Classical.choose_spec h
    obtain ⟨hw0, hw1⟩ := scattering_bounds_ae hR hv hvrad hv_supp hrad hw
    have hv_int : MeasureTheory.Integrable v := memLp_one_iff_integrable.mp hv1
    have hg0_int : MeasureTheory.Integrable
        (fun x : E3 => v x * (1 - Classical.choose h x)) := scatG_integrable hv_supp hw
    have hf_int : MeasureTheory.Integrable (fun x : E3 => v x * Classical.choose h x) := by
      rw [show (fun x : E3 => v x * Classical.choose h x)
          = fun x : E3 => v x - v x * (1 - Classical.choose h x) from by
        funext x; ring]
      exact hv_int.sub hg0_int
    have hw_asm : AEStronglyMeasurable (Classical.choose h) :=
      hw.lhs_integrable.aestronglyMeasurable
    refine hf_int.mono' (hv1.aestronglyMeasurable.mul (hw_asm.pow 2)) ?_
    filter_upwards [hw0, hw1] with x hx0 hx1
    have hsq : (Classical.choose h x) ^ 2 ≤ Classical.choose h x := by
      simpa [pow_two] using mul_le_of_le_one_left hx0 hx1
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (hv x) (sq_nonneg _))]
    exact mul_le_mul_of_nonneg_left hsq (hv x)
  have hsuppρ : ∀ z : E3, R ≤ ‖z‖ → (Classical.choose h z) ^ 2 * v z = 0 := by
    intro z hz
    rw [v_zero_of_norm_ge hv_supp hz, mul_zero]
  have hAωeq : Aω = (ellAt μ (a v)) ^ 3 * ρ₁ := by
    have h := Pieces.omegaSqCoupl_eq (v := v) (w := Classical.choose h) (R := R)
      (ℓ := ellAt μ (a v)) hℓpos hRℓ hIntρ hsuppρ
    rw [hAωdef, hρ₁def, h]
    congr 1
    apply MeasureTheory.integral_congr_ae
    filter_upwards with z
    ring
  have hAωpos : 0 < Aω := by rw [hAωeq]; positivity
  have hwgtnn : ∀ x y : E3, 0 ≤ wLoc (ellAt μ (a v)) v 0 x y := by
    intro x y
    rw [wLoc_zero_eq_wPair, wPair, wScaled]
    exact mul_nonneg (mul_nonneg (chiScale_nonneg _ x)
      (div_nonneg (hv (x - y)) (convScale_nonneg _ (x - y)))) (chiScale_nonneg _ y)
  have hDnn : 0 ≤ D := by
    rw [hD, q4Mass]
    refine Finset.sum_nonneg (fun p hp => integral_nonneg (fun x => ?_))
    exact mul_nonneg (sq_nonneg _) (hwgtnn _ _)
  have hcnnn : 0 ≤ cn := by rw [hcn]; exact cnPlus_nonneg φ
  have hnHnn : 0 ≤ nH := by rw [hnH]; exact nPlusHB_nonneg hℓpos φ
  have hcMnn : 0 ≤ cM := by
    rw [hcM, cMass]
    exact Finset.sum_nonneg (fun p hp => integral_nonneg (fun x =>
      mul_nonneg (sq_nonneg _) (hwgtnn _ _)))
  have hsMOnn : 0 ≤ sMO := by
    rw [hsMO, sMassOm]
    exact Finset.sum_nonneg (fun p hp => integral_nonneg (fun x =>
      mul_nonneg (mul_nonneg (sq_nonneg _) (sq_nonneg _)) (hwgtnn _ _)))
  have hsMO1nn : 0 ≤ sMO1 := by
    rw [hsMO1, sMassOm]
    exact Finset.sum_nonneg (fun p hp => integral_nonneg (fun x =>
      mul_nonneg (mul_nonneg (sq_nonneg _) (by norm_num : (0:ℝ) ≤ (1:ℝ) ^ 2)) (hwgtnn _ _)))
  have hlam_bound : |lam| ≤ CL * (ellAt μ (a v) * kapAt μ (a v)) ^ (-(N : ℝ))
      * (ellAt μ (a v)) ^ 3 := by
    rw [hlam]
    exact hleak fc (kapAt μ (a v)) (ellAt μ (a v)) hκpos hℓpos hRℓ
  have hside := Pieces.CS_side_hyps_of_memLp (fc := fc) (κ := kapAt μ (a v))
    (ℓ := ellAt μ (a v)) hv hvrad hv1 R hR hv_supp hav h hκpos hℓpos hRℓ hφc
  -- (A) the decomposition, with the leakage rewrite
  have hleaksum : (∑ p ∈ pairSet n, ∫ x in abox n (ellAt μ (a v)),
      (aP (ellAt μ (a v)) p.1 (aP (ellAt μ (a v)) p.2 φ) x) ^ 2
        * Work.BoseFixB3.CS.leakFn fc (kapAt μ (a v)) (ellAt μ (a v)) (x p.2)
        * Classical.choose h (x p.1 - x p.2)
        * wLoc (ellAt μ (a v)) (g0 v h) 0 (x p.1) (x p.2))
      = lam * ppMass (ellAt μ (a v)) φ := by
    set G : E3 → E3 → ℝ := fun u w =>
      Work.BoseFixB3.CS.leakFn fc (kapAt μ (a v)) (ellAt μ (a v)) w
        * Classical.choose h (u - w) * wLoc (ellAt μ (a v)) (g0 v h) 0 u w with hG
    have hgG : MeasureTheory.Integrable (fun z : E3 × E3 => G z.1 z.2) := hside.2.1
    have hmid : (∑ p ∈ pairSet n, ∫ x in abox n (ellAt μ (a v)),
        (aP (ellAt μ (a v)) p.1 (aP (ellAt μ (a v)) p.2 φ) x) ^ 2
          * Work.BoseFixB3.CS.leakFn fc (kapAt μ (a v)) (ellAt μ (a v)) (x p.2)
          * Classical.choose h (x p.1 - x p.2)
          * wLoc (ellAt μ (a v)) (g0 v h) 0 (x p.1) (x p.2))
        = ∑ p ∈ pairSet n, ∫ x in abox n (ellAt μ (a v)),
            (aP (ellAt μ (a v)) p.1 (aP (ellAt μ (a v)) p.2 φ) x) ^ 2 * G (x p.1) (x p.2) := by
      refine Finset.sum_congr rfl (fun p hp => ?_)
      apply MeasureTheory.integral_congr_ae
      filter_upwards with x
      simp only [hG] <;> try ring
    have hmainG : (∑ p ∈ pairSet n, ∫ x in abox n (ellAt μ (a v)),
        (aP (ellAt μ (a v)) p.1 (aP (ellAt μ (a v)) p.2 φ) x) ^ 2 * G (x p.1) (x p.2))
        = ((ellAt μ (a v)) ^ 3)⁻¹ * ((ellAt μ (a v)) ^ 3)⁻¹
          * (∫ u in acube (ellAt μ (a v)), ∫ w in acube (ellAt μ (a v)), G u w)
          * (∑ p ∈ pairSet n, ∫ x in abox n (ellAt μ (a v)),
              (aP (ellAt μ (a v)) p.1 (aP (ellAt μ (a v)) p.2 φ) x) ^ 2) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun p hp => ?_)
      have hij : p.1 ≠ p.2 := by simpa [pairSet] using hp
      rw [Pieces.pp_sq_factor (n := n) (ℓ := ellAt μ (a v)) hℓpos hφc hij G hgG] <;> try ring
    have hlc : leakCoupl fc (kapAt μ (a v)) (ellAt μ (a v)) (omC (Classical.choose h))
          (wLoc (ellAt μ (a v)) (g0 v h) 0)
        = ∫ u in acube (ellAt μ (a v)), ∫ w in acube (ellAt μ (a v)), G u w := by
      unfold leakCoupl
      apply MeasureTheory.integral_congr_ae
      filter_upwards with u
      apply MeasureTheory.integral_congr_ae
      filter_upwards with w
      simp only [hG] <;> try rfl
    rw [hmid, hmainG, hlam, hlc]
    unfold ppMass
    ring
  have hdec0 : q3barWord fc (kapAt μ (a v)) (ellAt μ (a v))
        (wLoc (ellAt μ (a v)) (g0 v h) 0) φ
      + q3omWord fc (kapAt μ (a v)) (ellAt μ (a v)) (wLoc (ellAt μ (a v)) (g0 v h) 0)
          (omC (Classical.choose h)) φ
      = 2 * S1 + 2 * lam * ppMass (ellAt μ (a v)) φ := by
    have hv3 := Pieces.q3bar_add_q3om_eq_v3 hv hvrad R hR hv_supp hav h fc (kapAt μ (a v))
      (ellAt μ (a v)) hκpos hℓpos hRℓ φ hφc
    rw [hv3, hleaksum, hS1]
    ring
  have hamgm0' : 2 * S1 ≥ - (2 * (8 + 1 / (4 * ε))) * mF - (1 / (2 * 8)) * D - (2 * ε) * sM := by
    have hineq := Pieces.qcross_bar_om_pair_sum_weighted (N := n) (ℓ := ellAt μ (a v))
      hℓpos hv hvrad hv1 hR hv_supp h hRℓ (fc := fc) (κ := kapAt μ (a v)) hκpos hφc
      (t := 8) (ε := ε) (by norm_num) hε
    rw [hS1, hmF, hD, hsM]
    exact hineq
  have hc8 : (2 : ℝ) * (8 + 1 / (4 * ε)) = 16 + 1 / (2 * ε) := by
    field_simp
    ring
  have hc16 : (1 : ℝ) / (2 * 8) = 1 / 16 := by norm_num
  have hamgm0 : 2 * S1 ≥ - (16 + 1 / (2 * ε)) * mF - (1 / 16) * D - (2 * ε) * sM := by
    rw [← hc8, ← hc16]
    exact hamgm0'
  -- (E) the mass bounds
  have hFb : mF ≤ CF * ((ellAt μ (a v)) ^ 3)⁻¹ * (n : ℝ) * high := by
    have h := hF n (ellAt μ (a v)) hℓpos hRℓ fc (kapAt μ (a v)) hκpos hφc
    rw [hmF, hhigh, hφ]
    exact h
  have hhighb : high ≤ nH := by
    have h := Work.BoseFixB3.HighMass.highMass_le_nPlusHB (fc := fc)
      (κ := kapAt μ (a v)) (ℓ := ellAt μ (a v)) (d := (patAt μ (a v)).d)
      (by rw [kapAt, patAt, ellAt]) hℓpos hφc
    rw [hhigh, hnH, hφ]
    exact h
  have hsMassb : sM ≤ C1 * ((ellAt μ (a v)) ^ 3)⁻¹ * (n : ℝ) * cn := by
    have h := hsMass n (ellAt μ (a v)) hℓpos hRℓ hφc
    rw [hsM, hcn, hφ]
    exact h
  -- (F) the numerical consequences
  have hq4eq : q4word (ellAt μ (a v)) (wLoc (ellAt μ (a v)) v 0)
      (omC (Classical.choose h)) φ = (1 / 2) * D := by
    rw [hD]
    unfold q4word q4Mass
    ring
  have hFleg : (16 + 1 / (2 * ε)) * mF
      ≤ K * (ellAt μ (a v)) ^ (-2 : ℤ) * ((patAt μ (a v)).Kl) ^ 4 * nH := by
    have h1 : mF ≤ CF * ((ellAt μ (a v)) ^ 3)⁻¹ * (n : ℝ) * nH :=
      hFb.trans (mul_le_mul_of_nonneg_left hhighb (by positivity))
    have h3 : ((ellAt μ (a v)) ^ 3)⁻¹ * (n : ℝ) ≤ 2 * μ := by
      rw [inv_mul_le_iff₀ hℓ3pos]
      nlinarith [hn]
    have hcoef_nn : 0 ≤ (16 + 1 / (2 * ε)) * CF := by
      have h1 : (0:ℝ) < 16 + 1 / (2 * ε) := by positivity
      exact mul_nonneg h1.le hCF0
    have hcoef : (16 + 1 / (2 * ε)) * CF * (2 * μ)
        ≤ K * (ellAt μ (a v)) ^ (-2 : ℤ) * ((patAt μ (a v)).Kl) ^ 4 := by
      have h32 : (16 + 1 / (2 * ε)) * CF * (2 * μ) = (32 + 1 / ε) * CF * μ := by
        field_simp
        ring
      rw [h32]
      exact hN3
    have hc1 : 0 ≤ 16 + 1 / (2 * ε) := by positivity
    calc (16 + 1 / (2 * ε)) * mF
        ≤ (16 + 1 / (2 * ε)) * (CF * ((ellAt μ (a v)) ^ 3)⁻¹ * (n : ℝ) * nH) :=
          mul_le_mul_of_nonneg_left h1 hc1
      _ = ((16 + 1 / (2 * ε)) * CF * (((ellAt μ (a v)) ^ 3)⁻¹ * (n : ℝ))) * nH := by ring
      _ ≤ ((16 + 1 / (2 * ε)) * CF * (2 * μ)) * nH :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h3 hcoef_nn) hnHnn
      _ ≤ (K * (ellAt μ (a v)) ^ (-2 : ℤ) * ((patAt μ (a v)).Kl) ^ 4) * nH :=
          mul_le_mul_of_nonneg_right hcoef hnHnn
      _ = K * (ellAt μ (a v)) ^ (-2 : ℤ) * ((patAt μ (a v)).Kl) ^ 4 * nH := by ring
  have hsMassleg : (2 * ε) * sM
      ≤ ((patAt μ (a v)).b / 800) * (ellAt μ (a v)) ^ (-2 : ℤ) * cn := by
    have h3 : ((ellAt μ (a v)) ^ 3)⁻¹ * (n : ℝ) ≤ 2 * μ := by
      rw [inv_mul_le_iff₀ hℓ3pos]
      nlinarith [hn]
    have h4 : (2 * ε) * (C1 * ((ellAt μ (a v)) ^ 3)⁻¹ * (n : ℝ)) ≤ (2 * ε) * (C1 * (2 * μ)) := by
      have h3' : C1 * (((ellAt μ (a v)) ^ 3)⁻¹ * (n : ℝ)) ≤ C1 * (2 * μ) :=
        mul_le_mul_of_nonneg_left h3 hC10
      calc (2 * ε) * (C1 * ((ellAt μ (a v)) ^ 3)⁻¹ * (n : ℝ))
          = (2 * ε) * (C1 * (((ellAt μ (a v)) ^ 3)⁻¹ * (n : ℝ))) := by ring
        _ ≤ (2 * ε) * (C1 * (2 * μ)) := mul_le_mul_of_nonneg_left h3' (by linarith [hε])
    have h5 : (2 * ε) * (C1 * (2 * μ))
        ≤ ((patAt μ (a v)).b / 800) * (ellAt μ (a v)) ^ (-2 : ℤ) := by
      have h44 : (2 * ε) * (C1 * (2 * μ)) = 4 * ε * C1 * μ := by ring
      rw [h44]
      exact hN4
    calc (2 * ε) * sM ≤ (2 * ε) * (C1 * ((ellAt μ (a v)) ^ 3)⁻¹ * (n : ℝ) * cn) :=
          mul_le_mul_of_nonneg_left hsMassb (by positivity)
      _ = ((2 * ε) * (C1 * ((ellAt μ (a v)) ^ 3)⁻¹ * (n : ℝ))) * cn := by ring
      _ ≤ ((2 * ε) * (C1 * (2 * μ))) * cn := mul_le_mul_of_nonneg_right h4 hcnnn
      _ ≤ (((patAt μ (a v)).b / 800) * (ellAt μ (a v)) ^ (-2 : ℤ)) * cn :=
          mul_le_mul_of_nonneg_right h5 hcnnn
      _ = ((patAt μ (a v)).b / 800) * (ellAt μ (a v)) ^ (-2 : ℤ) * cn := rfl
  -- (G) the leakage payment, from the condenser-mass dichotomy hypothesis `hpay`
  have hppMass : 2 * lam * ppMass (ellAt μ (a v)) φ
      ≥ - (1 / 64) * D - ((patAt μ (a v)).b / 1600) * (ellAt μ (a v)) ^ (-2 : ℤ) * cn := by
    have hQnn : 0 ≤ ppMass (ellAt μ (a v)) φ := by
      rw [ppMass]
      exact mul_nonneg (mul_nonneg (inv_nonneg.mpr hℓ3pos.le) (inv_nonneg.mpr hℓ3pos.le))
        (Finset.sum_nonneg (fun p hp => integral_nonneg (fun x => sq_nonneg _)))
    have hneg : -(2 * |lam| * ppMass (ellAt μ (a v)) φ)
        ≤ 2 * lam * ppMass (ellAt μ (a v)) φ := by
      have h2Q : (0:ℝ) ≤ 2 * ppMass (ellAt μ (a v)) φ := by linarith [hQnn]
      have := mul_le_mul_of_nonneg_left (neg_abs_le lam) h2Q
      nlinarith [this]
    linarith [hpay, hneg]
  -- (H) final assembly
  have hq4eq' : (1 / 4) * q4word (ellAt μ (a v)) (wLoc (ellAt μ (a v)) v 0)
      (omC (Classical.choose h)) φ = (1 / 8) * D := by rw [hq4eq]; ring
  have hres : 0 ≤ (((1 : ℝ) / 8) - (1 / 16) - (1 / 64)) * D :=
    mul_nonneg (by norm_num) hDnn
  have hres2 : 0 ≤ (((patAt μ (a v)).b / 200 - (patAt μ (a v)).b / 1600
      - (patAt μ (a v)).b / 800) * (ellAt μ (a v)) ^ (-2 : ℤ)) * cn := by
    refine mul_nonneg (mul_nonneg ?_ (zpow_nonneg hℓpos.le _)) hcnnn
    linarith [hbpos]
  nlinarith [hdec0, hq4eq', hamgm0, hppMass, hFleg, hsMassleg, hres, hres2]


/-! ## The parameter arithmetic of the wrapper

At FS's parameters one has `ℓ = a(μa³)^{-163/323}` and `ℓκ = (μa³)^{-12/323}`
(`Pieces.ellAt_kapAt_rpow_general`), hence for all real `c, d`

    (ℓκ)^c·ℓ^d = (μa³)^{(-(12c)-163d)/323}·a^d .

The instances used below are

    (ℓκ)^{-131}ℓ³ = (μa³)^{1083/323}a³ ,   (ℓκ)^{-131}ℓ⁶ = (μa³)^{594/323}a⁶ ,
    μ·((ℓκ)^{-131}ℓ⁶) = (μa³)^{917/323}a³ .
-/

/-- `(ℓκ)^c·ℓ^d = (μa³)^{(-(12c)-163d)/323}·a^d` at FS's parameters. -/
private lemma ell_kap_pow_mul_ell_pow (μ a : ℝ) (hμ : 0 < μ) (ha : 0 < a) (c d : ℝ) :
    (ellAt μ a * kapAt μ a) ^ c * (ellAt μ a) ^ d
      = (μ * a ^ 3) ^ ((-(12 * c) - 163 * d) / 323) * a ^ d := by
  have hx : 0 < μ * a ^ 3 := by positivity
  have h1 := (Pieces.ellAt_kapAt_rpow_general μ a hμ ha c).1
  have h2 := (Pieces.ellAt_kapAt_rpow_general μ a hμ ha d).2
  have hexp : -(12 * c) / 323 + -(163 * d) / 323 = (-(12 * c) - 163 * d) / 323 := by
    ring
  rw [h1, h2, ← mul_assoc, ← Real.rpow_add hx]
  exact congrArg (fun z => (μ * a ^ 3) ^ z * a ^ d) hexp

/-- `(ℓκ)^{-131}ℓ³ = (μa³)^{1083/323}a³`. -/
private lemma ell_kap_neg131_mul_cube (μ a : ℝ) (hμ : 0 < μ) (ha : 0 < a) :
    (ellAt μ a * kapAt μ a) ^ (-(131 : ℝ)) * (ellAt μ a) ^ 3
      = (μ * a ^ 3) ^ ((1083 : ℝ) / 323) * a ^ 3 := by
  have h := ell_kap_pow_mul_ell_pow μ a hμ ha (-(131 : ℝ)) (((3 : ℕ) : ℝ))
  have hexp : (-(12 * (-(131 : ℝ))) - 163 * (((3 : ℕ) : ℝ))) / 323 = (1083 : ℝ) / 323 := by
    norm_num
  rw [← Real.rpow_natCast (ellAt μ a) 3, h, Real.rpow_natCast a 3]
  exact congrArg (fun z => (μ * a ^ 3) ^ z * a ^ 3) hexp

/-- `(ℓκ)^{-131}ℓ⁶ = (μa³)^{594/323}a⁶`. -/
private lemma ell_kap_neg131_mul_six (μ a : ℝ) (hμ : 0 < μ) (ha : 0 < a) :
    (ellAt μ a * kapAt μ a) ^ (-(131 : ℝ)) * (ellAt μ a) ^ 6
      = (μ * a ^ 3) ^ ((594 : ℝ) / 323) * a ^ 6 := by
  have h := ell_kap_pow_mul_ell_pow μ a hμ ha (-(131 : ℝ)) (((6 : ℕ) : ℝ))
  have hexp : (-(12 * (-(131 : ℝ))) - 163 * (((6 : ℕ) : ℝ))) / 323 = (594 : ℝ) / 323 := by
    norm_num
  rw [← Real.rpow_natCast (ellAt μ a) 6, h, Real.rpow_natCast a 6]
  exact congrArg (fun z => (μ * a ^ 3) ^ z * a ^ 6) hexp

/-- `μ·((ℓκ)^{-131}ℓ⁶) = (μa³)^{917/323}a³`. -/
private lemma mu_ell_kap_neg131_mul_six (μ a : ℝ) (hμ : 0 < μ) (ha : 0 < a) :
    μ * ((ellAt μ a * kapAt μ a) ^ (-(131 : ℝ)) * (ellAt μ a) ^ 6)
      = (μ * a ^ 3) ^ ((917 : ℝ) / 323) * a ^ 3 := by
  have hx : 0 < μ * a ^ 3 := mul_pos hμ (pow_pos ha 3)
  rw [ell_kap_neg131_mul_six μ a hμ ha]
  calc μ * ((μ * a ^ 3) ^ ((594 : ℝ) / 323) * a ^ 6)
      = (μ * a ^ 6) * (μ * a ^ 3) ^ ((594 : ℝ) / 323) := by ring
    _ = ((μ * a ^ 3) * a ^ 3) * (μ * a ^ 3) ^ ((594 : ℝ) / 323) := by
        rw [show μ * a ^ 6 = (μ * a ^ 3) * a ^ 3 by ring]
    _ = (μ * a ^ 3) ^ (1 : ℝ) * (μ * a ^ 3) ^ ((594 : ℝ) / 323) * a ^ 3 := by
        rw [Real.rpow_one]
        ring
    _ = (μ * a ^ 3) ^ ((1 : ℝ) + (594 : ℝ) / 323) * a ^ 3 := by
        rw [Real.rpow_add hx, Real.rpow_one] <;> ring
    _ = (μ * a ^ 3) ^ ((917 : ℝ) / 323) * a ^ 3 := by
        rw [show (1 : ℝ) + (594 : ℝ) / 323 = (917 : ℝ) / 323 by norm_num]

/-- **Threshold A**: once `μa³ ≤ ε` with `ε` below the stated power,
`2·CL·Cq·(ℓκ)^{-131}ℓ³ ≤ 1/64` — the `q4Mass`-slot payment. -/
private lemma pay_leak_A {μ a ε CL Cq : ℝ} (hμ : 0 < μ) (ha : 0 < a)
    (hCL : 0 < CL) (hCq : 0 < Cq) (hε : μ * a ^ 3 ≤ ε)
    (hεb : ε ≤ (1 / (128 * CL * Cq * a ^ 3)) ^ ((323 : ℝ) / 1083)) :
    2 * CL * Cq * ((ellAt μ a * kapAt μ a) ^ (-(131 : ℝ)) * (ellAt μ a) ^ 3) ≤ 1 / 64 := by
  rw [ell_kap_neg131_mul_cube μ a hμ ha]
  have hx : 0 < μ * a ^ 3 := by positivity
  have hεpos : 0 < ε := lt_of_lt_of_le hx hε
  have hpos : 0 < 1 / (128 * CL * Cq * a ^ 3) := by positivity
  have hT : (μ * a ^ 3) ^ ((1083 : ℝ) / 323) * a ^ 3 ≤ 1 / (128 * CL * Cq) := by
    have h1 : (μ * a ^ 3) ^ ((1083 : ℝ) / 323) ≤ ε ^ ((1083 : ℝ) / 323) :=
      Real.rpow_le_rpow hx.le hε (by norm_num)
    have h2 : ε ^ ((1083 : ℝ) / 323)
        ≤ ((1 / (128 * CL * Cq * a ^ 3)) ^ ((323 : ℝ) / 1083)) ^ ((1083 : ℝ) / 323) :=
      Real.rpow_le_rpow hεpos.le hεb (by norm_num)
    have h3 : ((1 / (128 * CL * Cq * a ^ 3)) ^ ((323 : ℝ) / 1083)) ^ ((1083 : ℝ) / 323)
        = 1 / (128 * CL * Cq * a ^ 3) := by
      rw [← Real.rpow_mul hpos.le,
        show (323 : ℝ) / 1083 * ((1083 : ℝ) / 323) = (1 : ℝ) by norm_num, Real.rpow_one]
    have h4 : (1 / (128 * CL * Cq * a ^ 3)) * a ^ 3 = 1 / (128 * CL * Cq) := by
      have h1 : (128 : ℝ) * CL * Cq * a ^ 3 ≠ 0 := by positivity
      have h2 : (128 : ℝ) * CL * Cq ≠ 0 := by positivity
      field_simp
    calc (μ * a ^ 3) ^ ((1083 : ℝ) / 323) * a ^ 3
        ≤ (1 / (128 * CL * Cq * a ^ 3)) * a ^ 3 :=
          mul_le_mul_of_nonneg_right (le_trans h1 (le_trans h2 (le_of_eq h3)))
            (by positivity)
      _ = 1 / (128 * CL * Cq) := h4
  have h5 : 2 * CL * Cq * ((μ * a ^ 3) ^ ((1083 : ℝ) / 323) * a ^ 3)
      ≤ 2 * CL * Cq * (1 / (128 * CL * Cq)) :=
    mul_le_mul_of_nonneg_left hT (by positivity)
  have h6 : 2 * CL * Cq * (1 / (128 * CL * Cq)) = 1 / 64 := by
    have h1 : (128 : ℝ) * CL * Cq ≠ 0 := by positivity
    field_simp <;> ring
  linarith [h5, h6]

/-- **Threshold B**: once `μa³ ≤ ε` with `ε` below the stated power,
`2·CL·Cq·(ℓκ)^{-131}ℓ³·(2μℓ³) ≤ b/1600` — the `cnPlus`-slot payment. -/
private lemma pay_leak_B {μ a ε CL Cq : ℝ} (hμ : 0 < μ) (ha : 0 < a)
    (hCL : 0 < CL) (hCq : 0 < Cq) (hε : μ * a ^ 3 ≤ ε)
    (hεb : ε ≤ (bValue / (6400 * CL * Cq * a ^ 3)) ^ ((323 : ℝ) / 917)) :
    2 * CL * Cq * ((ellAt μ a * kapAt μ a) ^ (-(131 : ℝ)) * (ellAt μ a) ^ 3)
      * (2 * μ * (ellAt μ a) ^ 3) ≤ bValue / 1600 := by
  have hx : 0 < μ * a ^ 3 := by positivity
  have hεpos : 0 < ε := lt_of_lt_of_le hx hε
  have hpos : 0 < bValue / (6400 * CL * Cq * a ^ 3) := by
    rw [bValue]; positivity
  have hT : (μ * a ^ 3) ^ ((917 : ℝ) / 323) * a ^ 3 ≤ bValue / (6400 * CL * Cq) := by
    have h1 : (μ * a ^ 3) ^ ((917 : ℝ) / 323) ≤ ε ^ ((917 : ℝ) / 323) :=
      Real.rpow_le_rpow hx.le hε (by norm_num)
    have h2 : ε ^ ((917 : ℝ) / 323)
        ≤ ((bValue / (6400 * CL * Cq * a ^ 3)) ^ ((323 : ℝ) / 917)) ^ ((917 : ℝ) / 323) :=
      Real.rpow_le_rpow hεpos.le hεb (by norm_num)
    have h3 : ((bValue / (6400 * CL * Cq * a ^ 3)) ^ ((323 : ℝ) / 917)) ^ ((917 : ℝ) / 323)
        = bValue / (6400 * CL * Cq * a ^ 3) := by
      rw [← Real.rpow_mul hpos.le,
        show (323 : ℝ) / 917 * ((917 : ℝ) / 323) = (1 : ℝ) by norm_num, Real.rpow_one]
    have h4 : (bValue / (6400 * CL * Cq * a ^ 3)) * a ^ 3 = bValue / (6400 * CL * Cq) := by
      have h1 : (6400 : ℝ) * CL * Cq * a ^ 3 ≠ 0 := by positivity
      have h2 : (6400 : ℝ) * CL * Cq ≠ 0 := by positivity
      field_simp
    calc (μ * a ^ 3) ^ ((917 : ℝ) / 323) * a ^ 3
        ≤ (bValue / (6400 * CL * Cq * a ^ 3)) * a ^ 3 :=
          mul_le_mul_of_nonneg_right (le_trans h1 (le_trans h2 (le_of_eq h3)))
            (by positivity)
      _ = bValue / (6400 * CL * Cq) := h4
  have hkey : 2 * CL * Cq * ((ellAt μ a * kapAt μ a) ^ (-(131 : ℝ)) * (ellAt μ a) ^ 3)
        * (2 * μ * (ellAt μ a) ^ 3)
      = 4 * CL * Cq
        * (μ * ((ellAt μ a * kapAt μ a) ^ (-(131 : ℝ)) * (ellAt μ a) ^ 6)) := by
    ring
  rw [hkey, mu_ell_kap_neg131_mul_six μ a hμ ha]
  have h5 : 4 * CL * Cq * ((μ * a ^ 3) ^ ((917 : ℝ) / 323) * a ^ 3)
      ≤ 4 * CL * Cq * (bValue / (6400 * CL * Cq)) :=
    mul_le_mul_of_nonneg_left hT (by positivity)
  have h6 : 4 * CL * Cq * (bValue / (6400 * CL * Cq)) = bValue / 1600 := by
    have h1 : (6400 : ℝ) * CL * Cq ≠ 0 := by positivity
    field_simp <;> ring
  linarith [h5, h6]

/-- The `ε`-slot numeric hypothesis of `csv_state_le` (`ε = c₁/K_ℓ²`). -/
private lemma hN4_aux {μ a c₁ C1 : ℝ} (hμ : 0 < μ) (ha : 0 < a) (hC1 : 0 < C1)
    (hc₁ : c₁ ≤ a * bValue / (3200 * C1)) :
    4 * (c₁ / ((patAt μ a).Kl) ^ 2) * C1 * μ
      ≤ (patAt μ a).b / 800 * (ellAt μ a) ^ (-2 : ℤ) := by
  have hℓpos : 0 < ellAt μ a := ellAt_pos μ a hμ ha
  have hKl : ((patAt μ a).Kl) ^ 2 = μ * a * (ellAt μ a) ^ 2 := (mu_a_ell_sq μ a hμ ha).symm
  have hKlpos : 0 < ((patAt μ a).Kl) ^ 2 := by
    rw [hKl]
    exact mul_pos (mul_pos hμ ha) (pow_pos hℓpos 2)
  have hzp : (ellAt μ a) ^ (-2 : ℤ) = ((ellAt μ a) ^ 2)⁻¹ := by
    rw [zpow_neg, zpow_ofNat]
  have hℓ2 : ((ellAt μ a) ^ 2)⁻¹ = μ * a / ((patAt μ a).Kl) ^ 2 := by
    rw [hKl]
    have h1 : μ * a ≠ 0 := by positivity
    have h2 : (ellAt μ a) ^ 2 ≠ 0 := pow_ne_zero 2 (ne_of_gt hℓpos)
    field_simp
  rw [hzp, hℓ2, patAt_b]
  have hC1ne : (3200 : ℝ) * C1 ≠ 0 := by positivity
  have hnum : 4 * c₁ * C1 * μ ≤ bValue * a * μ / 800 := by
    have h1 : c₁ * (3200 * C1) ≤ a * bValue := by
      have h2 := mul_le_mul_of_nonneg_right hc₁ (le_of_lt (by positivity : (0:ℝ) < 3200 * C1))
      rw [div_mul_cancel₀ _ hC1ne] at h2
      linarith [h2]
    nlinarith [h1, hμ, ha, hC1]
  calc 4 * (c₁ / ((patAt μ a).Kl) ^ 2) * C1 * μ
      = (4 * c₁ * C1 * μ) / ((patAt μ a).Kl) ^ 2 := by ring
    _ ≤ (bValue * a * μ / 800) / ((patAt μ a).Kl) ^ 2 :=
        div_le_div_of_nonneg_right hnum hKlpos.le
    _ = bValue / 800 * (μ * a / ((patAt μ a).Kl) ^ 2) := by ring

/-- The `ε⁻¹`-slot numeric hypothesis of `csv_state_le` (`ε = c₁/K_ℓ²`). -/
private lemma hN3_aux {μ a c₁ K CF : ℝ} (hμ : 0 < μ) (ha : 0 < a) (hc₁ : 0 < c₁)
    (hCF : 0 ≤ CF) (hK1 : 64 * CF / a ≤ K) (hK2 : 2 * CF / (c₁ * a) ≤ K)
    (hKl : 1 ≤ (patAt μ a).Kl) :
    (32 + 1 / (c₁ / ((patAt μ a).Kl) ^ 2)) * CF * μ
      ≤ K * (ellAt μ a) ^ (-2 : ℤ) * ((patAt μ a).Kl) ^ 4 := by
  have hKlp : 0 < (patAt μ a).Kl := patAt_Kl_pos μ a hμ ha
  have hKl2pos : 0 < ((patAt μ a).Kl) ^ 2 := by positivity
  have hKl4 : ((patAt μ a).Kl) ^ 4 = ((patAt μ a).Kl) ^ 2 * ((patAt μ a).Kl) ^ 2 := by ring
  have hKl2ge : 1 ≤ ((patAt μ a).Kl) ^ 2 := by nlinarith [hKl, hKl2pos]
  have hℓpos : 0 < ellAt μ a := ellAt_pos μ a hμ ha
  have hKl2eq : ((patAt μ a).Kl) ^ 2 = μ * a * (ellAt μ a) ^ 2 := (mu_a_ell_sq μ a hμ ha).symm
  have hzp : (ellAt μ a) ^ (-2 : ℤ) = ((ellAt μ a) ^ 2)⁻¹ := by
    rw [zpow_neg, zpow_ofNat]
  have hℓ2 : ((ellAt μ a) ^ 2)⁻¹ = μ * a / ((patAt μ a).Kl) ^ 2 := by
    rw [hKl2eq]
    have h1 : μ * a ≠ 0 := by positivity
    have h2 : (ellAt μ a) ^ 2 ≠ 0 := pow_ne_zero 2 (ne_of_gt hℓpos)
    field_simp
  have hinv : 1 / (c₁ / ((patAt μ a).Kl) ^ 2) = ((patAt μ a).Kl) ^ 2 / c₁ := by
    rw [one_div_div]
  rw [hzp, hℓ2, hinv]
  have hb1 : 64 * CF ≤ K * a := by
    have h := mul_le_mul_of_nonneg_right hK1 ha.le
    rw [div_mul_cancel₀ _ (ne_of_gt ha)] at h
    linarith [h]
  have hb2 : 2 * CF / c₁ ≤ K * a := by
    have h := mul_le_mul_of_nonneg_right hK2 ha.le
    have he : 2 * CF / (c₁ * a) * a = 2 * CF / c₁ := by
      have h1 : c₁ * a ≠ 0 := by positivity
      field_simp
    rw [he] at h
    exact h
  have hKann : 0 ≤ K * a := by linarith [hb1, hCF]
  have hkey : (32 + ((patAt μ a).Kl) ^ 2 / c₁) * CF ≤ K * a * ((patAt μ a).Kl) ^ 2 := by
    have h1 : 32 * CF ≤ K * a / 2 * ((patAt μ a).Kl) ^ 2 := by
      have h2 : 32 * CF ≤ K * a / 2 := by linarith [hb1]
      have h3 : K * a / 2 ≤ K * a / 2 * ((patAt μ a).Kl) ^ 2 := by
        nlinarith [hKl2ge, hKann]
      linarith [h2, h3]
    have h4 : ((patAt μ a).Kl) ^ 2 / c₁ * CF ≤ K * a / 2 * ((patAt μ a).Kl) ^ 2 := by
      have h2 : CF / c₁ ≤ K * a / 2 := by
        have h7 : CF / c₁ = (2 * CF / c₁) / 2 := by ring
        rw [h7]
        exact div_le_div_of_nonneg_right hb2 (by norm_num)
      have h5 : CF / c₁ * ((patAt μ a).Kl) ^ 2 ≤ K * a / 2 * ((patAt μ a).Kl) ^ 2 :=
        mul_le_mul_of_nonneg_right h2 (by positivity)
      calc ((patAt μ a).Kl) ^ 2 / c₁ * CF = CF / c₁ * ((patAt μ a).Kl) ^ 2 := by ring
        _ ≤ K * a / 2 * ((patAt μ a).Kl) ^ 2 := h5
    have h6 : (32 + ((patAt μ a).Kl) ^ 2 / c₁) * CF
        = 32 * CF + ((patAt μ a).Kl) ^ 2 / c₁ * CF := by ring
    rw [h6]
    linarith [h1, h4]
  have hkey' : (32 + ((patAt μ a).Kl) ^ 2 / c₁) * CF * μ
      ≤ K * a * ((patAt μ a).Kl) ^ 2 * μ :=
    mul_le_mul_of_nonneg_right hkey hμ.le
  have hrhs : K * a * ((patAt μ a).Kl) ^ 2 * μ
      = K * (μ * a / ((patAt μ a).Kl) ^ 2) * ((patAt μ a).Kl) ^ 4 := by
    rw [hKl4]
    have h1 : ((patAt μ a).Kl) ^ 2 * ((patAt μ a).Kl) ^ 2 ≠ 0 := by positivity
    field_simp <;> ring
  rw [hrhs] at hkey'
  exact hkey'

/-! ## The wrapper: the constants, the thresholds, the assembly -/

/-- **FS `eq:pq'pp-sf`** (step 2 of FS's §7 chain, `cl:advQ3sch` with `Q' = Q̄_L`):
`q3bar + ¼q4 + (b/200)ℓ⁻²n₊ + q3om ≥ −Kℓ⁻²K_ℓ⁴n₊^H` for `n ≤ 2μℓ³` and `μ ≤ ε₀/a³`.

The proof instantiates `csv_state_le` with the four input lemmas of the chapter:

* `Pieces.leakCoupl_le_v2` with `N = 131` (the leakage bound `|λ| ≤ C_L(ℓκ)^{-131}ℓ³`);
* `Pieces.ppMass_le_q4Mass_add_card_mul_cnPlus` (the condensate-mass dichotomy
  `ppMass ≤ C_q(q4Mass + n·ℓ⁻²cnPlus)`), from which the payment hypothesis `hpay`
  follows with the two thresholds `pay_leak_A`/`pay_leak_B`;
* `Pieces.Fmass_le_highMass_pos` and `Pieces.sMass_w1_le_cnPlus` (the two mass bounds);
* the numeric hypotheses `hN3`/`hN4` (`hN3_aux`/`hN4_aux`) at `ε = c₁/K_ℓ²`
  with `c₁ = min 1 (a·b/(3200C₁))`.

`ε₀` is the minimum of `1`, the chapter's `ε₀s` (`Eps.sideAt_ge_of_dilute`, which gives
`R ≤ ℓ·chiR0`) and `ε₀Q` (the two payment thresholds); `K` is the maximum of `1`,
`64C_F/a` and `2C_F/(c₁a)`; all three are independent of `μ, n, Φ`. -/
theorem b3CSRoot_holds (v : EuclideanSpace ℝ (Fin 3) → ℝ)
    (h : Work.UBB.ScatSol v) (R : ℝ) (fc : Work.BoseBoxFix.LowCut)
    (hv : 0 ≤ v) (hv1 : MeasureTheory.MemLp v 1 MeasureTheory.volume)
    (hvrad : BoseGases.IsRadial v) (hR : 0 < R)
    (hv_supp : tsupport v ⊆ Metric.ball 0 R) (hav : 0 < BoseGases.a v) :
    Work.BoseFixB3.B3CSRoot v h R fc := by
  classical
  -- ### 1. the four input constants
  have hN : (1 : ℕ) ≤ 131 := by norm_num
  obtain ⟨CL0, hCL00, hleak0⟩ :=
    Pieces.leakCoupl_le_v2 hv hvrad R hR hv_supp hav h 131 hN
  obtain ⟨Cq0, hCq00, hQT0⟩ :=
    Pieces.ppMass_le_q4Mass_add_card_mul_cnPlus hv hvrad hv1 R hR hv_supp hav h
  obtain ⟨CF0, hCF00, hF0⟩ := Pieces.Fmass_le_highMass_pos hv hvrad R hR hv_supp hav h
  obtain ⟨C10, hC100, hsM0⟩ := Pieces.sMass_w1_le_cnPlus hv hvrad R hR hv_supp hav h
  set CL : ℝ := CL0 + 1 with hCLdef
  set Cq : ℝ := Cq0 + 1 with hCqdef
  set CF : ℝ := CF0 + 1 with hCFdef
  set C1 : ℝ := C10 + 1 with hC1def
  have hCL0 : 0 ≤ CL := by rw [hCLdef]; linarith
  have hCq0 : 0 ≤ Cq := by rw [hCqdef]; linarith
  have hCF0 : 0 ≤ CF := by rw [hCFdef]; linarith
  have hC10 : 0 ≤ C1 := by rw [hC1def]; linarith
  have hCLpos : 0 < CL := by rw [hCLdef]; linarith
  have hCqpos : 0 < Cq := by rw [hCqdef]; linarith
  have hC1pos : 0 < C1 := by rw [hC1def]; linarith
  have hbpos : 0 < bValue := bValue_pos
  -- ### 2. the `∀`-forms of the input lemmas (constants bumped, hence still valid)
  have hleak : ∀ (fc : LowCut) (κ ℓ : ℝ), 0 < κ → 0 < ℓ → R ≤ ℓ * chiR0 →
      |leakCoupl fc κ ℓ (omC (Classical.choose h)) (wLoc ℓ (g0 v h) 0)|
        ≤ CL * (ℓ * κ) ^ (-(131 : ℝ)) * ℓ ^ 3 := by
    intro fc κ ℓ hκ hℓ hRℓ
    have h1 := hleak0 fc κ ℓ hκ hℓ hRℓ
    have h3 : CL0 * (ℓ * κ) ^ (-(131 : ℝ)) * ℓ ^ 3
        ≤ CL * (ℓ * κ) ^ (-(131 : ℝ)) * ℓ ^ 3 := by
      have hA : 0 ≤ (ℓ * κ) ^ (-(131 : ℝ)) * ℓ ^ 3 := by positivity
      calc CL0 * (ℓ * κ) ^ (-(131 : ℝ)) * ℓ ^ 3
          = CL0 * ((ℓ * κ) ^ (-(131 : ℝ)) * ℓ ^ 3) := by ring
        _ ≤ CL * ((ℓ * κ) ^ (-(131 : ℝ)) * ℓ ^ 3) :=
            mul_le_mul_of_nonneg_right (by rw [hCLdef]; linarith) hA
        _ = CL * (ℓ * κ) ^ (-(131 : ℝ)) * ℓ ^ 3 := by ring
    calc |leakCoupl fc κ ℓ (omC (Classical.choose h)) (wLoc ℓ (g0 v h) 0)|
        ≤ CL0 * (ℓ * κ) ^ (-(131 : ℝ)) * ℓ ^ 3 := h1
      _ ≤ CL * (ℓ * κ) ^ (-(131 : ℝ)) * ℓ ^ 3 := h3
  have hQT : ∀ (μ : ℝ), 0 < μ → R ≤ ellAt μ (BoseGases.a v) * chiR0 →
      ∀ (n : ℕ) {Φ : X n → ℝ}, Continuous Φ →
      ppMass (ellAt μ (BoseGases.a v)) Φ
        ≤ Cq * (q4Mass (ellAt μ (BoseGases.a v)) (omC (Classical.choose h))
              (wLoc (ellAt μ (BoseGases.a v)) v 0) Φ
            + (n : ℝ) * (((ellAt μ (BoseGases.a v)) ^ 2)⁻¹
                * cnPlus (ellAt μ (BoseGases.a v)) Φ)) := by
    intro μ hμ hRℓ n Φ hΦc
    have h1 := hQT0 (ellAt μ (BoseGases.a v)) (ellAt_pos μ (BoseGases.a v) hμ hav) hRℓ n hΦc
    have hstuff : 0 ≤ q4Mass (ellAt μ (BoseGases.a v)) (omC (Classical.choose h))
          (wLoc (ellAt μ (BoseGases.a v)) v 0) Φ
        + (n : ℝ) * (((ellAt μ (BoseGases.a v)) ^ 2)⁻¹
            * cnPlus (ellAt μ (BoseGases.a v)) Φ) := by
      refine add_nonneg ?_ (mul_nonneg (by positivity)
        (mul_nonneg (inv_nonneg.mpr (by positivity)) (cnPlus_nonneg Φ)))
      rw [q4Mass]
      exact Finset.sum_nonneg (fun p hp => integral_nonneg (fun x =>
        mul_nonneg (sq_nonneg _) (by
          rw [wLoc_zero_eq_wPair, wPair, wScaled]
          exact mul_nonneg (mul_nonneg (chiScale_nonneg _ _)
            (div_nonneg (hv _) (convScale_nonneg _ _))) (chiScale_nonneg _ _))))
    have h3 : Cq0 * (q4Mass (ellAt μ (BoseGases.a v)) (omC (Classical.choose h))
              (wLoc (ellAt μ (BoseGases.a v)) v 0) Φ
            + (n : ℝ) * (((ellAt μ (BoseGases.a v)) ^ 2)⁻¹
                * cnPlus (ellAt μ (BoseGases.a v)) Φ))
        ≤ Cq * (q4Mass (ellAt μ (BoseGases.a v)) (omC (Classical.choose h))
              (wLoc (ellAt μ (BoseGases.a v)) v 0) Φ
            + (n : ℝ) * (((ellAt μ (BoseGases.a v)) ^ 2)⁻¹
                * cnPlus (ellAt μ (BoseGases.a v)) Φ)) :=
      mul_le_mul_of_nonneg_right (by rw [hCqdef]; linarith) hstuff
    linarith [h1, h3]
  have hF : ∀ (n : ℕ) (ℓ : ℝ), 0 < ℓ → R ≤ ℓ * chiR0 → ∀ (fc : LowCut) (κ : ℝ), 0 < κ →
      ∀ {Φ : X n → ℝ}, Continuous Φ →
      fMass fc κ ℓ (wLoc ℓ (g0 v h) 0) Φ ≤ CF * (ℓ ^ 3)⁻¹ * (n : ℝ) * highMass fc κ ℓ Φ := by
    intro n ℓ hℓ hRℓ fc κ hκ Φ hΦc
    have h1 := hF0 n ℓ hℓ fc κ hκ hRℓ hΦc
    have h2 : 0 ≤ (ℓ ^ 3)⁻¹ * (n : ℝ) * highMass fc κ ℓ Φ := by
      refine mul_nonneg (mul_nonneg ?_ (by positivity)) ?_
      · exact inv_nonneg.mpr (pow_nonneg hℓ.le 3)
      · rw [highMass]
        exact Finset.sum_nonneg (fun i _ => integral_nonneg (fun x => sq_nonneg _))
    have h3 : CF0 * (ℓ ^ 3)⁻¹ * (n : ℝ) * highMass fc κ ℓ Φ
        ≤ CF * (ℓ ^ 3)⁻¹ * (n : ℝ) * highMass fc κ ℓ Φ := by
      calc CF0 * (ℓ ^ 3)⁻¹ * (n : ℝ) * highMass fc κ ℓ Φ
          = CF0 * ((ℓ ^ 3)⁻¹ * (n : ℝ) * highMass fc κ ℓ Φ) := by ring
        _ ≤ CF * ((ℓ ^ 3)⁻¹ * (n : ℝ) * highMass fc κ ℓ Φ) :=
            mul_le_mul_of_nonneg_right (by rw [hCFdef]; linarith) h2
        _ = CF * (ℓ ^ 3)⁻¹ * (n : ℝ) * highMass fc κ ℓ Φ := by ring
    calc fMass fc κ ℓ (wLoc ℓ (g0 v h) 0) Φ
        ≤ CF0 * (ℓ ^ 3)⁻¹ * (n : ℝ) * highMass fc κ ℓ Φ := h1
      _ ≤ CF * (ℓ ^ 3)⁻¹ * (n : ℝ) * highMass fc κ ℓ Φ := h3
  have hsMass : ∀ (n : ℕ) (ℓ : ℝ), 0 < ℓ → R ≤ ℓ * chiR0 → ∀ {Φ : X n → ℝ}, Continuous Φ →
      sMass ℓ (wLoc ℓ (g0 v h) 0) Φ ≤ C1 * (ℓ ^ 3)⁻¹ * (n : ℝ) * cnPlus ℓ Φ := by
    intro n ℓ hℓ hRℓ Φ hΦc
    have h1 := hsM0 n ℓ hℓ hRℓ hΦc
    have h2 : 0 ≤ (ℓ ^ 3)⁻¹ * (n : ℝ) * cnPlus ℓ Φ :=
      mul_nonneg (mul_nonneg (inv_nonneg.mpr (pow_nonneg hℓ.le 3)) (by positivity))
        (cnPlus_nonneg Φ)
    have h3 : C10 * (ℓ ^ 3)⁻¹ * (n : ℝ) * cnPlus ℓ Φ
        ≤ C1 * (ℓ ^ 3)⁻¹ * (n : ℝ) * cnPlus ℓ Φ := by
      calc C10 * (ℓ ^ 3)⁻¹ * (n : ℝ) * cnPlus ℓ Φ
          = C10 * ((ℓ ^ 3)⁻¹ * (n : ℝ) * cnPlus ℓ Φ) := by ring
        _ ≤ C1 * ((ℓ ^ 3)⁻¹ * (n : ℝ) * cnPlus ℓ Φ) :=
            mul_le_mul_of_nonneg_right (by rw [hC1def]; linarith) h2
        _ = C1 * (ℓ ^ 3)⁻¹ * (n : ℝ) * cnPlus ℓ Φ := by ring
    calc sMass ℓ (wLoc ℓ (g0 v h) 0) Φ ≤ C10 * (ℓ ^ 3)⁻¹ * (n : ℝ) * cnPlus ℓ Φ := h1
      _ ≤ C1 * (ℓ ^ 3)⁻¹ * (n : ℝ) * cnPlus ℓ Φ := h3
  -- ### 3. the diluteness threshold
  obtain ⟨ε₀s, hε₀spos, hε₀s1, hε₀s⟩ := Work.BoseFixB3.Eps.sideAt_ge_of_dilute v hav hR
  set ε₀Q : ℝ := min ((1 / (128 * CL * Cq * (BoseGases.a v) ^ 3)) ^ ((323 : ℝ) / 1083))
      ((bValue / (6400 * CL * Cq * (BoseGases.a v) ^ 3)) ^ ((323 : ℝ) / 917)) with hε₀Q
  have hε₀Qpos : 0 < ε₀Q := by
    rw [hε₀Q]
    refine lt_min (Real.rpow_pos_of_pos (div_pos one_pos ?_) _)
      (Real.rpow_pos_of_pos (div_pos hbpos ?_) _) <;>
      (have h1 : 0 < CL := hCLpos
       have h2 : 0 < Cq := hCqpos
       positivity)
  set c₁ : ℝ := min 1 (BoseGases.a v * bValue / (3200 * C1)) with hc₁def
  have hc₁pos : 0 < c₁ := by
    rw [hc₁def]
    refine lt_min one_pos ?_
    positivity
  have hc₁le : c₁ ≤ BoseGases.a v * bValue / (3200 * C1) := by
    rw [hc₁def]
    exact min_le_right _ _
  set K : ℝ := max 1 (max (64 * CF / BoseGases.a v)
      (2 * CF / (c₁ * BoseGases.a v))) with hKdef
  refine ⟨K, min (min 1 ε₀s) ε₀Q, ?_, ?_, ?_⟩
  · exact le_trans (by norm_num : (0 : ℝ) ≤ 1)
      (le_max_left 1 (max (64 * CF / BoseGases.a v) (2 * CF / (c₁ * BoseGases.a v))))
  · exact lt_min (lt_min one_pos hε₀spos) hε₀Qpos
  · intro μ hadm n Φ hn
    have hμ : 0 < μ := hadm.1
    have hΦc : Continuous (Φ : X n → ℝ) := Φ.contDiff.continuous
    have hε₀pos : 0 < min (min 1 ε₀s) ε₀Q := lt_min (lt_min one_pos hε₀spos) hε₀Qpos
    have ht1 : μ * (a v) ^ 3 ≤ 1 :=
      le_trans hadm.2.1 (le_trans (min_le_left _ _) (min_le_left _ _))
    have ht0 : μ * (a v) ^ 3 ≤ ε₀s :=
      le_trans hadm.2.1 (le_trans (min_le_left _ _) (min_le_right _ _))
    have htQ : μ * (a v) ^ 3 ≤ ε₀Q := le_trans hadm.2.1 (min_le_right _ _)
    have hRℓ : R ≤ ellAt μ (a v) * chiR0 := hε₀s μ hμ ht0
    have hℓpos : 0 < ellAt μ (a v) := ellAt_pos μ (a v) hμ hav
    have hκpos : 0 < kapAt μ (a v) := by
      have hd : 0 < (patAt μ (a v)).d := by
        rw [patAt_d]; exact Work.BoseBox.fsXp_pos (mul_pos hμ (pow_pos hav 3))
      rw [kapAt]
      exact inv_pos.mpr (mul_pos (pow_pos (by simpa [patAt] using hd) 2)
        (by simpa [ellAt] using hℓpos))
    have hKl2pos : 0 < ((patAt μ (a v)).Kl) ^ 2 := by
      have := patAt_Kl_pos μ (a v) hμ hav
      positivity
    have hb : (patAt μ (a v)).b = bValue := patAt_b μ (BoseGases.a v)
    have hεbA : ε₀Q ≤ (1 / (128 * CL * Cq * (BoseGases.a v) ^ 3)) ^ ((323 : ℝ) / 1083) := by
      rw [hε₀Q]; exact min_le_left _ _
    have hεbB : ε₀Q ≤ (bValue / (6400 * CL * Cq * (BoseGases.a v) ^ 3)) ^ ((323 : ℝ) / 917) := by
      rw [hε₀Q]; exact min_le_right _ _
    have hA := pay_leak_A hμ hav hCLpos hCqpos htQ hεbA
    have hB := pay_leak_B hμ hav hCLpos hCqpos htQ hεbB
    -- ### the payment hypothesis `hpay`
    have hpay : 2 * |leakCoupl fc (kapAt μ (a v)) (ellAt μ (a v)) (omC (Classical.choose h))
            (wLoc (ellAt μ (a v)) (g0 v h) 0)|
          * ppMass (ellAt μ (a v)) (Φ : X n → ℝ)
        ≤ (1 / 64) * q4Mass (ellAt μ (a v)) (omC (Classical.choose h))
              (wLoc (ellAt μ (a v)) v 0) (Φ : X n → ℝ)
          + ((patAt μ (a v)).b / 1600) * (ellAt μ (a v)) ^ (-2 : ℤ)
              * cnPlus (ellAt μ (a v)) (Φ : X n → ℝ) := by
      set lam : ℝ := leakCoupl fc (kapAt μ (a v)) (ellAt μ (a v)) (omC (Classical.choose h))
        (wLoc (ellAt μ (a v)) (g0 v h) 0) with hlam
      set Q : ℝ := ppMass (ellAt μ (a v)) (Φ : X n → ℝ) with hQ
      set D : ℝ := q4Mass (ellAt μ (a v)) (omC (Classical.choose h))
        (wLoc (ellAt μ (a v)) v 0) (Φ : X n → ℝ) with hD
      set CN : ℝ := cnPlus (ellAt μ (a v)) (Φ : X n → ℝ) with hCN
      set P1 : ℝ := (ellAt μ (a v) * kapAt μ (a v)) ^ (-(131 : ℝ))
        * (ellAt μ (a v)) ^ 3 with hP1
      set Y : ℝ := ((ellAt μ (a v)) ^ 2)⁻¹ * CN with hY
      have hQnn : 0 ≤ Q := by
        rw [hQ, ppMass]
        exact mul_nonneg (mul_nonneg (inv_nonneg.mpr (pow_nonneg hℓpos.le 3))
          (inv_nonneg.mpr (pow_nonneg hℓpos.le 3)))
          (Finset.sum_nonneg (fun p hp => integral_nonneg (fun x => sq_nonneg _)))
      have hDnn : 0 ≤ D := by
        rw [hD, q4Mass]
        exact Finset.sum_nonneg (fun p hp => integral_nonneg (fun x =>
          mul_nonneg (sq_nonneg _) (by
            rw [wLoc_zero_eq_wPair, wPair, wScaled]
            exact mul_nonneg (mul_nonneg (chiScale_nonneg _ _)
              (div_nonneg (hv _) (convScale_nonneg _ _))) (chiScale_nonneg _ _))))
      have hCNnn : 0 ≤ CN := by rw [hCN]; exact cnPlus_nonneg _
      have hYnn : 0 ≤ Y := by
        rw [hY]
        exact mul_nonneg (inv_nonneg.mpr (pow_nonneg hℓpos.le 2)) hCNnn
      have hP1nn : 0 ≤ P1 := by rw [hP1]; positivity
      have h1 : |lam| ≤ CL * P1 := by
        rw [hlam, hP1]
        simpa only [mul_assoc] using
          hleak fc (kapAt μ (a v)) (ellAt μ (a v)) hκpos hℓpos hRℓ
      have h2 : Q ≤ Cq * (D + (n : ℝ) * Y) := by
        rw [hQ, hD, hY, hCN]
        exact hQT μ hμ hRℓ n hΦc
      have h4 : |lam| * Q ≤ (CL * P1) * (Cq * (D + (n : ℝ) * Y)) :=
        mul_le_mul h1 h2 hQnn (mul_nonneg hCL0 hP1nn)
      have h5 : 2 * |lam| * Q ≤ 2 * ((CL * P1) * (Cq * (D + (n : ℝ) * Y))) := by
        linarith [h4]
      have hMnn : 0 ≤ 2 * CL * Cq * P1 := by positivity
      have hA' : 2 * CL * Cq * P1 ≤ 1 / 64 := by rw [hP1]; exact hA
      have hB' : 2 * CL * Cq * P1 * (2 * μ * (ellAt μ (a v)) ^ 3) ≤ bValue / 1600 := by
        rw [hP1]; exact hB
      have hDleg : 2 * CL * Cq * P1 * D ≤ (1 / 64) * D :=
        mul_le_mul_of_nonneg_right hA' hDnn
      have hYleg : 2 * CL * Cq * P1 * (n : ℝ) * Y ≤ (bValue / 1600) * Y := by
        have s1 : 2 * CL * Cq * P1 * (n : ℝ)
            ≤ 2 * CL * Cq * P1 * (2 * μ * (ellAt μ (a v)) ^ 3) :=
          mul_le_mul_of_nonneg_left hn hMnn
        have s2 : 2 * CL * Cq * P1 * (n : ℝ) * Y
            ≤ 2 * CL * Cq * P1 * (2 * μ * (ellAt μ (a v)) ^ 3) * Y :=
          mul_le_mul_of_nonneg_right s1 hYnn
        have s3 : 2 * CL * Cq * P1 * (2 * μ * (ellAt μ (a v)) ^ 3) * Y
            ≤ (bValue / 1600) * Y := mul_le_mul_of_nonneg_right hB' hYnn
        linarith [s2, s3]
      have hrhs : 2 * ((CL * P1) * (Cq * (D + (n : ℝ) * Y)))
          ≤ (1 / 64) * D + (bValue / 1600) * Y := by
        have heq : 2 * ((CL * P1) * (Cq * (D + (n : ℝ) * Y)))
            = 2 * CL * Cq * P1 * D + 2 * CL * Cq * P1 * (n : ℝ) * Y := by ring
        rw [heq]
        linarith [hDleg, hYleg]
      have hfin : (1 / 64) * D + (bValue / 1600) * Y
          = (1 / 64) * D + ((patAt μ (a v)).b / 1600) * (ellAt μ (a v)) ^ (-2 : ℤ)
              * CN := by
        rw [hb, hY, show (ellAt μ (a v)) ^ (-2 : ℤ) = ((ellAt μ (a v)) ^ 2)⁻¹ by
          rw [zpow_neg, zpow_ofNat]]
        ring
      calc 2 * |lam| * Q
          ≤ 2 * ((CL * P1) * (Cq * (D + (n : ℝ) * Y))) := h5
        _ ≤ (1 / 64) * D + (bValue / 1600) * Y := hrhs
        _ = (1 / 64) * D + ((patAt μ (a v)).b / 1600) * (ellAt μ (a v)) ^ (-2 : ℤ)
              * CN := hfin
    -- ### the two numeric hypotheses of `csv_state_le`
    have hKlge1 : 1 ≤ (patAt μ (a v)).Kl := by
      rw [patAt_Kl]
      have h0 : 0 < μ * (BoseGases.a v) ^ 3 := by positivity
      have h1 : (1 : ℝ) = (μ * (BoseGases.a v) ^ 3) ^ (0 : ℝ) := by rw [Real.rpow_zero]
      rw [h1]
      refine Real.rpow_le_rpow_of_exponent_ge h0 ht1 ?_
      norm_num
    have hK1 : 64 * CF / BoseGases.a v ≤ K := by
      rw [hKdef]
      exact le_trans (le_max_left _ _) (le_max_right 1 _)
    have hK2 : 2 * CF / (c₁ * BoseGases.a v) ≤ K := by
      rw [hKdef]
      exact le_trans (le_max_right _ _) (le_max_right 1 _)
    have hN3 := hN3_aux hμ hav hc₁pos hCF0 hK1 hK2 hKlge1
    have hN4 := hN4_aux hμ hav hC1pos hc₁le
    exact csv_state_le hv hv1 hvrad hR hv_supp hav hN hCL0 hCF0 hC10 hleak hF hsMass
      hε₀pos (le_trans (min_le_left _ _) (min_le_left _ _)) hadm hRℓ hc₁pos
      (div_pos hc₁pos hKl2pos) (le_trans (by norm_num : (0:ℝ) ≤ 1)
        (le_max_left 1 (max (64 * CF / BoseGases.a v) (2 * CF / (c₁ * BoseGases.a v)))))
      Φ hn hpay hN3 hN4

end Work.BoseFixB3.CS

