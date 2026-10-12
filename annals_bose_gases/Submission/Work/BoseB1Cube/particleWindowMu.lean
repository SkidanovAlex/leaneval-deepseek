import ChallengeDeps
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Submission.Work.BoseB1Cube.nodeB1B_of_perBoxFNomMu
import Submission.Work.BoseB1Cube.nomAprioriDefs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission.Work.BoseB1Cube.particleWindowMu` — the sharp particle window at the nominal
# (indicator-count) spelling

**Target.**  `Work.BoseB1Cube.ParticleWindowMu v h R` (FS `eq:apriorinn+`, first conjunct) from
`Work.BoseB1Cube.PerBoxFNomMu v h R` (FS `thm:smallbox` at the sliding box, FS's *own* nominal
spelling, slot `μ`).  Equivalently: for every low box state at a dilute `μ`,

    |n − μℓ³| ≤ C₁·nWindow(μ) ,   nWindow = μℓ³·K_B^{3/2}K_ℓ(μ(a v)³)^{1/4} .

## The route (FS `final_v2.tex` l.4050–4190 at the sharp density)

1. `PerBoxFNomMu` + the slot doubling (`perBoxFNomSlots_of_perBoxFNomMu`) + FS's localisation
   `SlidingGoodCube` (PROVED) give FS's a-priori rows `eq:aprioriRn+` at the nominal remainder —
   the **clean rows** `NomAprioriUnif v h` (`nomAprioriDefs.lean`), obtained from `ledgerNom`
   (PROVED) with the prescribed `E·μaκ·n‖Φ‖²` slot removed through the one-sided count window
   `countWindowOfNominal` (PROVED).
2. `NomAprioriUnif ⟹ ParticleWindowMu` is the *nominal particle-window bridge*
   (`nomWindowBridgeMu`, this file) — a verbatim re-run of the PROVED smooth
   `Work.BoseFixB1.windowBridgeUnif_holds` at the nominal objects:
   * Jensen/Jensen-integrated: `nomJensen_integrated` (PROVED);
   * Cauchy–Schwarz: `nomCsWindowLocal` below (the nominal twin of `WB.cs_apply`, built from the
     abstract `WB.cs_weight` and the PROVED `integrableOnMulPsiWeight`);
   * the `U`-identity: `nomSigEqLocal` below (`‖Φ‖²·nomSig = ∫Φ²ΣᵢU(xᵢ)`, from the PROVED
     `sig_sharp_wbUSharp`);
   * the `U`-facts and `∫_ΛU = W`: the PROVED `wbUSharp_facts`, `integral_wbUSharp`;
   * the `P/Q` split: the PROVED `WB.pq_split_meas` at `U = wbUSharp`;
   * the final `ε`-arithmetic: the PROVED `WB.final_arith_exp`, `WB.cs_regime`.

Nothing below depends on `Work.BoseFixB1B.lowCountBound` or on any other `sorry`-carrying node.
-/

noncomputable section

open MeasureTheory Metric Filter
open scoped Topology Real BigOperators ENNReal

namespace Work.BoseB1Cube

open _root_.BoseGases Submission.BoseGases Work.BoseBoxFix Work.BoseBox Work.UBB Work.BoseFixB1
open Work.SmallBoxSliding

local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "X" => Submission.BoseGases.X

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 4000000

/-! ## 1. The standing small-box hypothesis on the interior set -/

/-- On the interior `I₋` of the sliding region the box has volume at least `μ⁻¹`: the regime
`1 ≤ μ(ℓd)³` gives `μ^{-1/3} ≤ ℓd`, hence every side of `B(u)` is at least `μ^{-1/3}` and
`|B(u)| ≥ μ⁻¹`, i.e. `μ|B(u)| ≥ 1` (FS's standing small-box hypothesis). -/
private lemma inv_le_boxMass_of_interior {μ ℓ d : ℝ} (hμ : 0 < μ) (hℓ : 0 < ℓ) (hd : 0 < d)
    (hd1 : d ≤ 1) (hreg : 1 ≤ μ * (ℓ * d) ^ 3) {u : E3}
    (hu : u ∈ Work.SmallBoxSliding.interiorSet ℓ d μ) :
    μ⁻¹ ≤ Work.SmallBoxSliding.boxMass ℓ d u := by
  have hld : 0 < ℓ * d := mul_pos hℓ hd
  have hcube : (μ ^ (-(1 / 3 : ℝ))) ^ 3 = μ⁻¹ := by
    rw [← Real.rpow_natCast (μ ^ (-(1 / 3 : ℝ))) 3, ← Real.rpow_mul hμ.le,
      show (-(1 / 3 : ℝ) * ((3 : ℕ) : ℝ)) = -1 by norm_num, Real.rpow_neg_one]
  have hx3 : μ⁻¹ ≤ (ℓ * d) ^ 3 := by
    rw [inv_le_iff_one_le_mul₀ hμ]
    linarith [hreg]
  have h13 : μ ^ (-(1 / 3 : ℝ)) ≤ ℓ * d := by
    have hnn : 0 ≤ μ ^ (-(1 / 3 : ℝ)) := Real.rpow_nonneg hμ.le _
    calc μ ^ (-(1 / 3 : ℝ)) = ((μ ^ (-(1 / 3 : ℝ))) ^ 3) ^ ((1 : ℝ) / 3) := by
          rw [← Real.rpow_natCast (μ ^ (-(1 / 3 : ℝ))) 3, ← Real.rpow_mul hnn]
          norm_num
      _ = (μ⁻¹) ^ ((1 : ℝ) / 3) := by rw [hcube]
      _ ≤ ((ℓ * d) ^ 3) ^ ((1 : ℝ) / 3) := Real.rpow_le_rpow (by positivity) hx3 (by norm_num)
      _ = ℓ * d := by
          rw [← Real.rpow_natCast (ℓ * d) 3, ← Real.rpow_mul hld.le]
          norm_num
  have hvol : (μ ^ (-(1 / 3 : ℝ))) ^ 3 ≤ Work.SmallBoxSliding.boxMass ℓ d u :=
    Work.BoseFixB1.boxMass_ge_deltaScale_of_goodSet hℓ hd hd1 hμ h13
      (Work.SmallBoxSliding.interiorSet_subset_goodSet hμ hu)
  rw [inv_le_iff_one_le_mul₀ hμ]
  calc (1 : ℝ) = μ * (μ ^ (-(1 / 3 : ℝ))) ^ 3 := by
        rw [hcube, mul_inv_cancel₀ (ne_of_gt hμ)]
    _ ≤ μ * Work.SmallBoxSliding.boxMass ℓ d u := mul_le_mul_of_nonneg_left hvol hμ.le
    _ = Work.SmallBoxSliding.boxMass ℓ d u * μ := by ring

/-! ## 2. The two `ε`-split arithmetics (copies of `countWindowUnif_of_aprioriUnif`'s privates) -/

/-- `(x^{3/2})^2 = x^3` for `x ≥ 0`. -/
private lemma sq_rpow_three_halves {x : ℝ} (hx : 0 ≤ x) :
    (x ^ (3 / 2 : ℝ)) ^ 2 = x ^ 3 := by
  rw [← Real.rpow_natCast (x ^ (3 / 2 : ℝ)) 2, ← Real.rpow_mul hx]
  norm_num

/-- `(y^{1/4})^2 = y^{1/2}` for `y ≥ 0`. -/
private lemma sq_rpow_quarter {y : ℝ} (hy : 0 ≤ y) :
    (y ^ (1 / 4 : ℝ)) ^ 2 = y ^ (1 / 2 : ℝ) := by
  rw [← Real.rpow_natCast (y ^ (1 / 4 : ℝ)) 2, ← Real.rpow_mul hy]
  norm_num

/-- Upper `ε`-split. -/
private lemma split_up_arith {nb ℓ W s ε KU nP I N : ℝ} (hnb : 0 < nb) (hW : 0 < W)
    (hℓ : 0 < ℓ) (hs : s * (nb * W) = I)
    (h : I ≤ (1 + ε) * (W / ℓ ^ 3) * (N * nb - nP) + (1 + ε⁻¹) * KU * nP) :
    s ≤ (1 + ε) * (N - nP / nb) / ℓ ^ 3 + (1 + ε⁻¹) * (KU / W) * (nP / nb) := by
  have hnbW : 0 < nb * W := mul_pos hnb hW
  have hs' : s = I / (nb * W) := (eq_div_iff (ne_of_gt hnbW)).mpr hs
  rw [hs', div_le_iff₀ hnbW]
  have hid : ((1 + ε) * (N - nP / nb) / ℓ ^ 3 + (1 + ε⁻¹) * (KU / W) * (nP / nb)) * (nb * W)
      = (1 + ε) * (W / ℓ ^ 3) * (N * nb - nP) + (1 + ε⁻¹) * KU * nP := by
    field_simp
  rw [hid]
  exact h

/-- Lower `ε`-split: the mirror image of `split_up_arith`. -/
private lemma split_lo_arith {nb ℓ W s ε KU nP I N : ℝ} (hnb : 0 < nb) (hW : 0 < W)
    (hℓ : 0 < ℓ) (hs : s * (nb * W) = I)
    (h : (1 - ε) * (W / ℓ ^ 3) * (N * nb - nP) - (1 + ε⁻¹) * KU * nP ≤ I) :
    (1 - ε) * (N - nP / nb) / ℓ ^ 3 - (1 + ε⁻¹) * (KU / W) * (nP / nb) ≤ s := by
  have hnbW : 0 < nb * W := mul_pos hnb hW
  have hs' : s = I / (nb * W) := (eq_div_iff (ne_of_gt hnbW)).mpr hs
  rw [hs', le_div_iff₀ hnbW]
  have hid : ((1 - ε) * (N - nP / nb) / ℓ ^ 3 - (1 + ε⁻¹) * (KU / W) * (nP / nb)) * (nb * W)
      = (1 - ε) * (W / ℓ ^ 3) * (N * nb - nP) - (1 + ε⁻¹) * KU * nP := by
    field_simp
  rw [hid]
  exact h

/-! ## 3. The nominal Cauchy–Schwarz window (the twin of `WB.cs_apply`) -/

private theorem nomCsWindowLocal {v : E3 → ℝ} {h : ScatSol v} {R : ℝ}
    (hv : 0 ≤ v) (hvrad : _root_.BoseGases.IsRadial v)
    (hv_supp : tsupport v ⊆ Metric.ball (0 : E3) R) (hR : 0 < R)
    {μ : ℝ} (hμ : 0 < μ) (hav : 0 < a v)
    (hM : 1 ≤ (paramsAt μ (a v)).M) (hℓ : 0 < sideAt μ (a v)) (hd : 0 < (paramsAt μ (a v)).d)
    {C₁ : ℝ} (hC₁ : 0 < C₁)
    (hmassU : ∀ u : E3, wbMass v h μ u
      ≤ C₁ * (a v) * chiMass (paramsAt μ (a v)).M (sideAt μ (a v)) (paramsAt μ (a v)).d u)
    {n : ℕ} (Φ : Work.BoseKinLoc.BoxState n (sideAt μ (a v)))
    (hN : 0 < normB v μ n (Φ : X n → ℝ)) :
    |nomSig h μ (Φ : X n → ℝ) - μ * wbW v h μ|
      ≤ Real.sqrt (∫ u in Work.SmallBoxSliding.interiorSet (sideAt μ (a v))
            (paramsAt μ (a v)).d μ,
          wbMass v h μ u * Work.SmallBoxSliding.psiWeight 1 μ (nomDens h μ (Φ : X n → ℝ) u))
        * Real.sqrt (wbW v h μ + nomSig h μ (Φ : X n → ℝ) / μ) := by
  set G : Set E3 := Work.SmallBoxSliding.interiorSet (sideAt μ (a v)) (paramsAt μ (a v)).d μ
    with hGdef
  set t : E3 → ℝ := fun u => nomDens h μ (Φ : X n → ℝ) u with htdef
  set g : E3 → ℝ := fun u => wbMass v h μ u with hgdef
  have hgm : AEStronglyMeasurable g (volume : Measure E3) := by
    rw [hgdef]
    exact Work.BoseFixB1.WB.w1MassB_aeStronglyMeasurable_local (v := v) (h := h) (R0 := R)
      hR hv_supp (paramsAt μ (a v)).M hM (sideAt μ (a v)) (paramsAt μ (a v)).d
  have htm : AEStronglyMeasurable t (volume : Measure E3) := by
    rw [htdef]
    exact aestronglyMeasurableNomDens (v := v) (h := h) (μ := μ) Φ
  have hg0 : ∀ u, 0 ≤ g u := by
    intro u
    rw [hgdef]
    exact wbMass_nonneg (v := v) (h := h) (R0 := R) hv hvrad hv_supp hR hM hℓ hd u
  have ht0 : ∀ u, 0 ≤ t u := by
    intro u
    rw [htdef]
    exact nomDens_nonneg (Φ : X n → ℝ) u
  have hIg : IntegrableOn g G := by
    rw [hgdef, hGdef]
    exact Work.BoseFixB1.WB.integrableOn_wbMass_interior (v := v) (h := h) (R0 := R)
      hv hvrad hv_supp hR hμ hav hM hℓ hd
  have hIgt : IntegrableOn (fun u => g u * t u) G := by
    rw [hgdef, htdef, hGdef]
    exact integrableOnWbMassMulNomDens (v := v) (h := h) (R := R) hv hvrad hv_supp hR hμ hav
      hM hℓ hd hC₁ hmassU Φ hN
  have hItg : IntegrableOn (fun u => t u * g u) G :=
    hIgt.congr (Filter.Eventually.of_forall fun u => by
      show g u * t u = t u * g u
      ring)
  have htG : ∀ u ∈ G, 0 ≤ t u := fun u _ => ht0 u
  have hgG : ∀ u ∈ G, 0 ≤ g u := fun u _ => hg0 u
  have hψint : IntegrableOn (fun u => g u * psiWeight 1 μ (t u)) G :=
    integrableOnMulPsiWeight hμ htG hgG hIg hIgt
      (htm.aemeasurable.mono_measure Measure.restrict_le_self)
  have hint1 : IntegrableOn (fun u => (t u - μ) ^ 2 / (1 + t u / μ) * g u) G :=
    hψint.congr (Filter.Eventually.of_forall fun u => by
      show g u * psiWeight 1 μ (t u) = (t u - μ) ^ 2 / (1 + t u / μ) * g u
      rw [psiWeight]
      ring_nf)
  have hint2 : IntegrableOn (fun u => (1 + t u / μ) * g u) G :=
    (hIg.add (hItg.const_mul μ⁻¹)).congr
      (Filter.Eventually.of_forall fun u => by
        show g u + μ⁻¹ * (t u * g u) = (1 + t u / μ) * g u
        rw [div_eq_mul_inv]
        ring)
  have hint3 : IntegrableOn (fun u => (t u - μ) * g u) G :=
    (hItg.sub (hIg.const_mul μ)).congr
      (Filter.Eventually.of_forall fun u => by
        show t u * g u - μ * g u = (t u - μ) * g u
        ring)
  have hcs := Work.BoseFixB1.WB.cs_weight (G := G) hμ
    (Work.SmallBoxSliding.measurableSet_interiorSet _ _ _) htG hgG hint1 hint2 hint3
  have hSigEq : nomSig h μ (Φ : X n → ℝ) = ∫ u in G, t u * g u := by
    rw [nomSig, hGdef, htdef, hgdef]
    refine MeasureTheory.setIntegral_congr_fun
      (Work.SmallBoxSliding.measurableSet_interiorSet _ _ _) (fun u _ => ?_)
    simp only [Work.BoseFixB1.wbMass]
    ring
  have hWEq : wbW v h μ = ∫ u in G, g u := by
    rw [wbW, hGdef, hgdef]
  have hint3' : (∫ u in G, (t u - μ) * g u) = nomSig h μ (Φ : X n → ℝ) - μ * wbW v h μ := by
    have h1 : (∫ u in G, t u * g u) - μ * (∫ u in G, g u)
        = ∫ u in G, (t u - μ) * g u := by
      rw [← MeasureTheory.integral_const_mul,
        ← MeasureTheory.integral_sub hItg (hIg.const_mul μ)]
      exact MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun u => by ring)
    rw [← h1, hSigEq, hWEq]
  have hint2' : (∫ u in G, (1 + t u / μ) * g u)
      = wbW v h μ + nomSig h μ (Φ : X n → ℝ) / μ := by
    have h1 : (∫ u in G, g u) + μ⁻¹ * (∫ u in G, t u * g u)
        = ∫ u in G, (1 + t u / μ) * g u := by
      rw [← MeasureTheory.integral_const_mul,
        ← MeasureTheory.integral_add hIg (hItg.const_mul μ⁻¹)]
      exact MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun u => by
        show g u + μ⁻¹ * (t u * g u) = (1 + t u / μ) * g u
        rw [div_eq_mul_inv]
        ring)
    rw [← h1, hSigEq, hWEq]
    ring
  have hint1' : (∫ u in G, (t u - μ) ^ 2 / (1 + t u / μ) * g u)
      = ∫ u in G, wbMass v h μ u * psiWeight 1 μ (nomDens h μ (Φ : X n → ℝ) u) := by
    refine MeasureTheory.setIntegral_congr_fun
      (Work.SmallBoxSliding.measurableSet_interiorSet _ _ _) (fun u _ => ?_)
    rw [htdef, hgdef, psiWeight]
    simp only []
    ring_nf
  rw [hint3', hint1', hint2'] at hcs
  rwa [hGdef] at hcs

/-! ## 4. The nominal `U`-identity -/

private theorem nomSigEqLocal {v : E3 → ℝ} {h : ScatSol v} {R : ℝ}
    (hv : 0 ≤ v) (hvrad : _root_.BoseGases.IsRadial v)
    (hv_supp : tsupport v ⊆ Metric.ball (0 : E3) R) (hR : 0 < R)
    {μ : ℝ} (hμ : 0 < μ) (hav : 0 < a v)
    (hM : 1 ≤ (paramsAt μ (a v)).M) (hℓ : 0 < sideAt μ (a v)) (hd : 0 < (paramsAt μ (a v)).d)
    {C₁ : ℝ} (hC₁ : 0 < C₁)
    (hmassU : ∀ u : E3, wbMass v h μ u
      ≤ C₁ * (a v) * chiMass (paramsAt μ (a v)).M (sideAt μ (a v)) (paramsAt μ (a v)).d u)
    {n : ℕ} (Φ : Work.BoseKinLoc.BoxState n (sideAt μ (a v)))
    (hN : 0 < normB v μ n (Φ : X n → ℝ)) :
    normB v μ n (Φ : X n → ℝ) * nomSig h μ (Φ : X n → ℝ)
      = ∫ x in Submission.BoseGases.abox n (sideAt μ (a v)),
          ((Φ : X n → ℝ) x) ^ 2 * ∑ i : Fin n, Work.BoseFixB1S.wbUSharp h μ (x i) := by
  have hsig := Work.BoseFixB1S.sig_sharp_wbUSharp (v := v) (h := h) (R0 := R) hv hvrad hv_supp
    hR hμ hav hM hℓ hd hC₁.le hmassU Φ
  rw [hsig, nomSig]
  rw [← MeasureTheory.integral_const_mul]
  refine MeasureTheory.setIntegral_congr_fun
    (Work.SmallBoxSliding.measurableSet_interiorSet _ _ _) (fun u _ => ?_)
  rw [nomDens]
  have hcnt : (∫ x in Submission.BoseGases.abox n (sideAt μ (a v)),
        ((Φ : X n → ℝ) x) ^ 2 * nomCnt (sideAt μ (a v)) (paramsAt μ (a v)).d u x)
      = ∫ x in Submission.BoseGases.abox n (sideAt μ (a v)),
        ((Φ : X n → ℝ) x) ^ 2 * Work.FockBridge.boxCount
          (Submission.BoseGases.dlBox (sideAt μ (a v)) (paramsAt μ (a v)).d u) x := by
    refine MeasureTheory.setIntegral_congr_fun (Submission.BoseGases.abox_measurable n _)
      (fun x _ => ?_)
    rw [Work.FockBridge.boxCount_eq_sum_indicator]
    simp only [nomCnt, Work.SmallBoxSliding.boxInd]
  rw [hcnt, wbMass]
  rw [← mul_div_assoc, ← mul_div_assoc, mul_div_mul_left _ _ (ne_of_gt hN),
    div_mul_eq_mul_div]

/-! ## 5. The nominal particle-window bridge (the twin of `WB.windowBridgeUnif_holds`) -/

theorem nomWindowBridgeMu {v : E3 → ℝ} (h : ScatSol v) (hv : 0 ≤ v)
    (hvrad : _root_.BoseGases.IsRadial v) {R : ℝ} (hR : 0 < R)
    (hv_supp : tsupport v ⊆ Metric.ball (0 : E3) R) (hav : 0 < a v)
    (hA : NomAprioriUnif v h) :
    ∃ ε₀ C₁ : ℝ, 0 < ε₀ ∧ 0 ≤ C₁ ∧
      ∀ (J : ℝ) (μ : ℝ), Adm v ε₀ μ → J ≤ (paramsAt μ (a v)).KB ^ 3 →
        ∀ (n : ℕ) (Φ : Work.BoseKinLoc.BoxState n (sideAt μ (a v))),
          0 < normB v μ n (Φ : X n → ℝ) → IsLowB v h J μ n Φ →
            |(n : ℝ) - μ * (sideAt μ (a v)) ^ 3|
              ≤ C₁ * Work.BoseBox.nWindow (paramsAt μ (a v)) μ (a v) := by
  obtain ⟨C_A, ε_A, hCA, hεA, hAunif⟩ := hA
  obtain ⟨C₁₀, hC₁₀, hmassU₀⟩ :=
    Work.BoseFixB1.WB.mass_upper (v := v) (h := h) (R0 := R) hv hvrad hv_supp hR
      (M := Work.BoseBox.mValue) (by norm_num [Work.BoseBox.mValue])
  set C₁ : ℝ := max C₁₀ 1 with hC₁def
  have hC₁pos : 0 < C₁ := lt_of_lt_of_le one_pos (le_max_right _ _)
  have hC₁0 : 0 ≤ C₁ := le_of_lt hC₁pos
  obtain ⟨ε_R, hε_R, hregime⟩ :=
    Work.BoseFixB1.WB.window_regime (v := v) (R := R) (C₁ := C₁) (C_A := C_A) hav hR hC₁pos hCA
  have hconst0 : 0 ≤ 2 + 2 * Real.sqrt (3 * (C_A / Real.pi))
      + 4 * (C₁ * (Submission.BoseGases.chiSupAbs
            * Submission.BoseGases.chiSmallDecay Work.BoseBox.mValue) ^ 2 / Real.pi)
          * (2 * C_A / Work.BoseBox.bValue)
      + 2 * C_A / Work.BoseBox.bValue := by
    have h3 : 0 ≤ C₁ * (Submission.BoseGases.chiSupAbs
        * Submission.BoseGases.chiSmallDecay Work.BoseBox.mValue) ^ 2 / Real.pi :=
      div_nonneg (mul_nonneg hC₁0 (sq_nonneg _)) (le_of_lt Real.pi_pos)
    have h4 : 0 ≤ 2 * C_A / Work.BoseBox.bValue :=
      div_nonneg (mul_nonneg (by norm_num) hCA.le) (by norm_num [Work.BoseBox.bValue])
    have h5 : 0 ≤ 4 * (C₁ * (Submission.BoseGases.chiSupAbs
          * Submission.BoseGases.chiSmallDecay Work.BoseBox.mValue) ^ 2 / Real.pi)
        * (2 * C_A / Work.BoseBox.bValue) := mul_nonneg (mul_nonneg (by norm_num) h3) h4
    have h2 : 0 ≤ Real.sqrt (3 * (C_A / Real.pi)) := Real.sqrt_nonneg _
    linarith [h2, h4, h5]
  refine ⟨min ε_A (min ε_R 1),
    2 + 2 * Real.sqrt (3 * (C_A / Real.pi))
      + 4 * (C₁ * (Submission.BoseGases.chiSupAbs
            * Submission.BoseGases.chiSmallDecay Work.BoseBox.mValue) ^ 2 / Real.pi)
          * (2 * C_A / Work.BoseBox.bValue)
      + 2 * C_A / Work.BoseBox.bValue,
    lt_min hεA (lt_min hε_R one_pos), hconst0, ?_⟩
  intro J μ hAdm hJK n Φ hNB hlow
  have hAdmA : Adm v ε_A μ := Adm.mono hAdm (min_le_left _ _)
  have hAdmR : Adm v ε_R μ :=
    Adm.mono hAdm (le_trans (min_le_right _ _) (min_le_left _ _))
  have hAdm1 : Adm v 1 μ :=
    Adm.mono hAdm (le_trans (min_le_right _ _) (min_le_right _ _))
  have ht1 : μ * (a v) ^ 3 ≤ 1 := Work.BoseFixB1.adm_dilute_le_one hAdm1 le_rfl
  obtain ⟨hRchiR0, hRd16, hM3, _ht1', hεhalf, hKB, hθ, hcomp⟩ := hregime μ hAdmR
  have hμ : 0 < μ := hAdm.1
  have hM1 : 1 ≤ (paramsAt μ (a v)).M := le_trans (by norm_num : 1 ≤ 3) hM3
  have hℓ : 0 < sideAt μ (a v) := Work.BoseFixB1.adm_ell_pos hAdm
  have hd : 0 < (paramsAt μ (a v)).d := Work.BoseFixB1.adm_d_pos hAdm
  have ha0 : 0 ≤ a v := le_of_lt hav
  have hmuℓd : 1 ≤ μ * (sideAt μ (a v) * (paramsAt μ (a v)).d) ^ 3 := by
    have h := Work.BoseFixB1.Regime.one_le_mu_d_mul_sideAt_cube hav hμ ht1
    rwa [mul_comm (paramsAt μ (a v)).d (sideAt μ (a v))] at h
  have hd1 : (paramsAt μ (a v)).d ≤ 1 := by
    rw [Work.BoseFixB1.d_eq_fsXp]
    exact Work.BoseBox.fsXp_le_one (by positivity) ht1 (by norm_num)
  have hBu : ∀ u ∈ Work.SmallBoxSliding.interiorSet (sideAt μ (a v)) (paramsAt μ (a v)).d μ,
      μ⁻¹ ≤ Work.SmallBoxSliding.boxMass (sideAt μ (a v)) (paramsAt μ (a v)).d u :=
    fun u hu => inv_le_boxMass_of_interior hμ hℓ hd hd1 hmuℓd hu
  have hmassU : ∀ u : E3, wbMass v h μ u
      ≤ C₁ * a v * chiMass (paramsAt μ (a v)).M (sideAt μ (a v)) (paramsAt μ (a v)).d u := by
    intro u
    have h1 := hmassU₀ hℓ hd hRd16 hRchiR0 u
    calc wbMass v h μ u
        = w1MassB h (paramsAt μ (a v)).M (sideAt μ (a v)) (paramsAt μ (a v)).d u := rfl
      _ ≤ C₁₀ * a v * chiMass (paramsAt μ (a v)).M (sideAt μ (a v)) (paramsAt μ (a v)).d u := h1
      _ ≤ C₁ * a v * chiMass (paramsAt μ (a v)).M (sideAt μ (a v)) (paramsAt μ (a v)).d u := by
          have h2 : C₁₀ * a v ≤ C₁ * a v := mul_le_mul_of_nonneg_right (le_max_left _ _) ha0
          exact mul_le_mul_of_nonneg_right h2 (Work.SmallBoxSliding.chiMass_nonneg _ _ _ _)
  have hmassL : ∀ u : E3, 0 ≤ wbMass v h μ u :=
    fun u => wbMass_nonneg (v := v) (h := h) (R0 := R) hv hvrad hv_supp hR hM1 hℓ hd u
  have htotal_raw := Work.BoseFixB1.WB.mass_total2 (v := v) (h := h) (R0 := R)
    (M := (paramsAt μ (a v)).M) hv_supp hR ha0 hM3 hℓ hd hRd16
    (Submission.BoseGases.chiR0_pos) hRchiR0 (fun x hx => Submission.BoseGases.chiR0_half x hx)
  have hπC : 0 < 8 * Real.pi * (a v) * (sideAt μ (a v)) ^ 3 := by positivity
  have htotal : 8 * Real.pi * (a v) * (sideAt μ (a v)) ^ 3 * (3 / 4)
      ≤ ∫ u : E3, wbMass v h μ u := by
    have h2 : |(∫ u : E3, wbMass v h μ u)
        - 8 * Real.pi * (a v) * (sideAt μ (a v)) ^ 3|
        ≤ (1 / 4) * (8 * Real.pi * (a v) * (sideAt μ (a v)) ^ 3) := by
      refine le_trans htotal_raw ?_
      have h4 : Submission.BoseGases.convDevC (paramsAt μ (a v)).M
          * (R / sideAt μ (a v)) ^ 2 ≤ 1 / 4 := hθ
      nlinarith [h4, hπC]
    have h3 := (abs_le.mp h2).1
    linarith
  have hWlow := Work.BoseFixB1.WB.wbW_lower (v := v) (h := h) (R0 := R) hv hvrad hv_supp hR hμ
    hav hM1 hℓ hd hC₁pos hmassU htotal hcomp
  have hWpos : 0 < wbW v h μ := lt_of_lt_of_le (by positivity) hWlow
  have hJi := nomJensen_integrated (v := v) (h := h) (R := R) hv hvrad hR hv_supp hμ hav hM1
    hℓ hd hBu Φ
  set Cnst : ℝ := C_A * (μ ^ 2 * (a v) * (sideAt μ (a v)) ^ 3 * kappa v μ) with hCnstdef
  have hJb : (∫ u in Work.SmallBoxSliding.interiorSet (sideAt μ (a v))
          (paramsAt μ (a v)).d μ,
        wbMass v h μ u * Work.SmallBoxSliding.psiWeight 1 μ
          (nomDens h μ (Φ : X n → ℝ) u)) ≤ Cnst := by
    have h1 : nomRPsi h μ (Φ : X n → ℝ) ≤ Cnst * normB v μ n (Φ : X n → ℝ) := by
      simpa only [hCnstdef, mul_assoc] using (hAunif J μ hAdmA hJK n Φ hNB hlow).1
    rw [mul_comm] at h1
    exact le_of_mul_le_mul_left (le_trans hJi h1) hNB
  have hCS := nomCsWindowLocal (v := v) (h := h) (R := R) hv hvrad hv_supp hR hμ hav
    hM1 hℓ hd hC₁pos hmassU Φ hNB
  set s : ℝ := nomSig h μ (Φ : X n → ℝ) / wbW v h μ with hsdef
  have hsignn : 0 ≤ nomSig h μ (Φ : X n → ℝ) :=
    integral_nonneg fun u => mul_nonneg (hmassL u) (nomDens_nonneg (Φ : X n → ℝ) u)
  have hs0 : 0 ≤ s := div_nonneg hsignn (le_of_lt hWpos)
  set γ : ℝ := (paramsAt μ (a v)).KB ^ (3 / 2 : ℝ) * (μ * (a v) ^ 3) ^ (1 / 4 : ℝ) with hγdef
  have hγ0 : 0 ≤ γ := by
    rw [hγdef]
    exact mul_nonneg (Real.rpow_nonneg (Work.BoseFixB1.paramsAt_KB_pos hAdm).le _)
      (Real.rpow_nonneg (by positivity) _)
  have hγ2 : γ ^ 2 = kappa v μ := by
    rw [hγdef, kappa, mul_pow,
      sq_rpow_three_halves (Work.BoseFixB1.paramsAt_KB_pos hAdm).le,
      sq_rpow_quarter (by positivity : (0 : ℝ) ≤ μ * (a v) ^ 3)]
  have hsW : nomSig h μ (Φ : X n → ℝ) = s * wbW v h μ := by
    rw [hsdef]
    field_simp
  have hCS' : wbW v h μ * |s - μ| ≤ Real.sqrt Cnst
      * Real.sqrt (wbW v h μ * (1 + s / μ)) := by
    have h3 : wbW v h μ + nomSig h μ (Φ : X n → ℝ) / μ = wbW v h μ * (1 + s / μ) := by
      rw [hsW]; ring
    have h1 : wbW v h μ * |s - μ| = |nomSig h μ (Φ : X n → ℝ) - μ * wbW v h μ| := by
      have h' : |nomSig h μ (Φ : X n → ℝ) - μ * wbW v h μ| = wbW v h μ * |s - μ| := by
        rw [hsW, ← sub_mul, abs_mul, abs_of_pos hWpos]
        ring
      exact h'.symm
    rw [h1]
    refine le_trans hCS ?_
    exact mul_le_mul (Real.sqrt_le_sqrt hJb) (Real.sqrt_le_sqrt (le_of_eq h3))
      (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  have hCnst0 : 0 ≤ Cnst := by
    rw [hCnstdef]
    exact mul_nonneg hCA.le (mul_nonneg (mul_nonneg (mul_nonneg (sq_nonneg μ) ha0)
      (pow_nonneg hℓ.le 3)) (kappa_nonneg hμ hav))
  have hbound : Cnst ≤ (C_A / Real.pi) * wbW v h μ * μ ^ 2 * γ ^ 2 := by
    have heq : Cnst = (C_A / Real.pi) * μ ^ 2 * γ ^ 2
        * (Real.pi * (a v) * (sideAt μ (a v)) ^ 3) := by
      rw [hCnstdef, hγ2]
      field_simp
    rw [heq]
    have hnn : 0 ≤ (C_A / Real.pi) * μ ^ 2 * γ ^ 2 :=
      mul_nonneg (mul_nonneg (div_nonneg hCA.le (le_of_lt Real.pi_pos)) (sq_nonneg μ))
        (sq_nonneg γ)
    calc (C_A / Real.pi) * μ ^ 2 * γ ^ 2 * (Real.pi * (a v) * (sideAt μ (a v)) ^ 3)
        ≤ (C_A / Real.pi) * μ ^ 2 * γ ^ 2 * wbW v h μ := mul_le_mul_of_nonneg_left hWlow hnn
      _ = (C_A / Real.pi) * wbW v h μ * μ ^ 2 * γ ^ 2 := by ring
  have hβ0 : 0 ≤ C_A / Real.pi := div_nonneg hCA.le (le_of_lt Real.pi_pos)
  have hsmall : 3 * (C_A / Real.pi) * γ ^ 2 ≤ 1 := by
    rw [hγ2]
    have h1 : 3 * C_A * kappa v μ ≤ Real.pi := by
      have h := hKB
      rw [le_div_iff₀ (show (0 : ℝ) < 3 * C_A by linarith)] at h
      calc 3 * C_A * kappa v μ = kappa v μ * (3 * C_A) := by ring
        _ ≤ Real.pi := h
    have h2 : 3 * (C_A / Real.pi) * kappa v μ = (3 * C_A * kappa v μ) / Real.pi := by
      field_simp
    rw [h2, div_le_iff₀ Real.pi_pos]
    simpa using h1
  have hs : |s - μ| ≤ Real.sqrt (3 * (C_A / Real.pi)) * μ * γ :=
    Work.BoseFixB1.WB.cs_regime hWpos hμ hCnst0 hs0 hγ0 hβ0 hCS' hbound hsmall
  have hmmu : ∀ u : E3, wbMass v h μ u
      ≤ (C₁ * (Submission.BoseGases.chiSupAbs
            * Submission.BoseGases.chiSmallDecay (paramsAt μ (a v)).M) ^ 2) * (a v)
          * Work.SmallBoxSliding.boxMass (sideAt μ (a v)) (paramsAt μ (a v)).d u := by
    intro u
    have h1 := hmassU u
    have h2 := Work.BoseFixB1S.chiMass_le_const_mul_boxMass (M := (paramsAt μ (a v)).M) hM1 hℓ hd u
    have h3 : 0 ≤ C₁ * (a v) := mul_nonneg hC₁0 ha0
    calc wbMass v h μ u
        ≤ C₁ * (a v) * Work.SmallBoxSliding.chiMass (paramsAt μ (a v)).M (sideAt μ (a v))
            (paramsAt μ (a v)).d u := h1
      _ ≤ C₁ * (a v) * ((Submission.BoseGases.chiSupAbs
            * Submission.BoseGases.chiSmallDecay (paramsAt μ (a v)).M) ^ 2
            * Work.SmallBoxSliding.boxMass (sideAt μ (a v)) (paramsAt μ (a v)).d u) :=
          mul_le_mul_of_nonneg_left h2 h3
      _ = (C₁ * (Submission.BoseGases.chiSupAbs
            * Submission.BoseGases.chiSmallDecay (paramsAt μ (a v)).M) ^ 2) * (a v)
          * Work.SmallBoxSliding.boxMass (sideAt μ (a v)) (paramsAt μ (a v)).d u := by ring
  have hSharpp := Work.BoseB1Cube.wbUSharp_facts (v := v) h hv hvrad hR hv_supp hμ hav hM1 hℓ hd
    (C := C₁ * (Submission.BoseGases.chiSupAbs
      * Submission.BoseGases.chiSmallDecay (paramsAt μ (a v)).M) ^ 2) (by positivity) hmmu
  have hUintW : (∫ z in Submission.BoseGases.acube (sideAt μ (a v)),
      Work.BoseFixB1S.wbUSharp h μ z) = wbW v h μ :=
    Work.BoseFixB1S.integral_wbUSharp (v := v) (h := h) (R0 := R) hv hvrad hv_supp hR hμ hav
      hM1 hℓ hd hC₁0 hmassU
  have hUmeas : AEMeasurable (Work.BoseFixB1S.wbUSharp h μ) (volume : Measure E3) := hSharpp.2.1
  have hUintOn : IntegrableOn (Work.BoseFixB1S.wbUSharp h μ)
      (Submission.BoseGases.acube (sideAt μ (a v))) := hSharpp.2.2.1
  have hUnn : ∀ z : E3, 0 ≤ Work.BoseFixB1S.wbUSharp h μ z := hSharpp.1
  have hKUle : ∀ z : E3, Work.BoseFixB1S.wbUSharp h μ z
      ≤ C₁ * (Submission.BoseGases.chiSupAbs
        * Submission.BoseGases.chiSmallDecay (paramsAt μ (a v)).M) ^ 2 * (a v) := hSharpp.2.2.2
  have hεpos : 0 < wbEps v μ := by
    rw [wbEps]
    have h1 : 0 < (paramsAt μ (a v)).KB ^ (3 / 2 : ℝ) :=
      Real.rpow_pos_of_pos (Work.BoseFixB1.paramsAt_KB_pos hAdm) _
    have h2 : 0 < (paramsAt μ (a v)).Kl := Work.BoseFixB1.adm_Kl_pos hAdm
    have h3 : 0 < (μ * (a v) ^ 3) ^ (1 / 4 : ℝ) := Real.rpow_pos_of_pos (by positivity) _
    positivity
  have hpq := Work.BoseFixB1.WB.pq_split_meas (N := n) (ℓ := sideAt μ (a v)) hℓ
    (Φ := (Φ : X n → ℝ)) Φ.contDiff.continuous
    (g := Work.BoseFixB1S.wbUSharp h μ) (Tvol := wbW v h μ)
    (KU := C₁ * (Submission.BoseGases.chiSupAbs
      * Submission.BoseGases.chiSmallDecay (paramsAt μ (a v)).M) ^ 2 * (a v))
    (ε := wbEps v μ) hεpos hUmeas hUintOn hUnn hUintW hKUle
  have hSigEq := nomSigEqLocal (v := v) (h := h) (R := R) hv hvrad hv_supp hR hμ hav hM1 hℓ hd
    hC₁pos hmassU Φ hNB
  have hpSum := Work.BoseFixB1.pSum_eq (n := n) (ℓ := sideAt μ (a v)) hℓ Φ.contDiff.continuous
  have hqSum : (∑ i : Fin n, ∫ x in Submission.BoseGases.abox n (sideAt μ (a v)),
      (Submission.BoseGases.aQ (sideAt μ (a v)) i (Φ : X n → ℝ) x) ^ 2)
      = cnPlus (sideAt μ (a v)) (Φ : X n → ℝ) :=
    Work.BoseFixB1.qSum_eq (ℓ := sideAt μ (a v)) (Φ : X n → ℝ)
  have hIeq : s * (normB v μ n (Φ : X n → ℝ) * wbW v h μ)
      = ∫ x in Submission.BoseGases.abox n (sideAt μ (a v)),
          ((Φ : X n → ℝ) x) ^ 2 * ∑ i : Fin n, Work.BoseFixB1S.wbUSharp h μ (x i) := by
    rw [hsdef, ← hSigEq]
    field_simp
  have hsplit_up : s ≤ (1 + wbEps v μ)
        * ((n : ℝ) - cnPlus (sideAt μ (a v)) (Φ : X n → ℝ)
            / normB v μ n (Φ : X n → ℝ)) / (sideAt μ (a v)) ^ 3
      + (1 + (wbEps v μ)⁻¹)
          * ((C₁ * (Submission.BoseGases.chiSupAbs
              * Submission.BoseGases.chiSmallDecay (paramsAt μ (a v)).M) ^ 2 * (a v)) / wbW v h μ)
          * (cnPlus (sideAt μ (a v)) (Φ : X n → ℝ) / normB v μ n (Φ : X n → ℝ)) := by
    have hsp := hpq.1
    rw [hpSum, hqSum] at hsp
    exact split_up_arith (nb := normB v μ n (Φ : X n → ℝ)) (ℓ := sideAt μ (a v))
      (W := wbW v h μ) (s := s) (ε := wbEps v μ)
      (KU := C₁ * (Submission.BoseGases.chiSupAbs
        * Submission.BoseGases.chiSmallDecay (paramsAt μ (a v)).M) ^ 2 * (a v))
      (nP := cnPlus (sideAt μ (a v)) (Φ : X n → ℝ))
      (I := ∫ x in Submission.BoseGases.abox n (sideAt μ (a v)),
        ((Φ : X n → ℝ) x) ^ 2 * ∑ i : Fin n, Work.BoseFixB1S.wbUSharp h μ (x i))
      (N := (n : ℝ)) hNB hWpos hℓ hIeq hsp
  have hsplit_lo : (1 - wbEps v μ)
        * ((n : ℝ) - cnPlus (sideAt μ (a v)) (Φ : X n → ℝ)
            / normB v μ n (Φ : X n → ℝ)) / (sideAt μ (a v)) ^ 3
      - (1 + (wbEps v μ)⁻¹)
          * ((C₁ * (Submission.BoseGases.chiSupAbs
              * Submission.BoseGases.chiSmallDecay (paramsAt μ (a v)).M) ^ 2 * (a v)) / wbW v h μ)
          * (cnPlus (sideAt μ (a v)) (Φ : X n → ℝ) / normB v μ n (Φ : X n → ℝ)) ≤ s := by
    have hsp := hpq.2
    rw [hpSum, hqSum] at hsp
    exact split_lo_arith (nb := normB v μ n (Φ : X n → ℝ)) (ℓ := sideAt μ (a v))
      (W := wbW v h μ) (s := s) (ε := wbEps v μ)
      (KU := C₁ * (Submission.BoseGases.chiSupAbs
        * Submission.BoseGases.chiSmallDecay (paramsAt μ (a v)).M) ^ 2 * (a v))
      (nP := cnPlus (sideAt μ (a v)) (Φ : X n → ℝ))
      (I := ∫ x in Submission.BoseGases.abox n (sideAt μ (a v)),
        ((Φ : X n → ℝ) x) ^ 2 * ∑ i : Fin n, Work.BoseFixB1S.wbUSharp h μ (x i))
      (N := (n : ℝ)) hNB hWpos hℓ hIeq hsp
  have hKℓ2 : μ * (a v) * (sideAt μ (a v)) ^ 2 = (paramsAt μ (a v)).Kl ^ 2 :=
    Work.BoseFixB1.mu_mul_a_mul_ell_sq μ (a v) hμ hav
  have hA0nn : 0 ≤ cnPlus (sideAt μ (a v)) (Φ : X n → ℝ) / normB v μ n (Φ : X n → ℝ) :=
    div_nonneg (by
      rw [cnPlus]
      exact Finset.sum_nonneg fun i _ => integral_nonneg fun x => sq_nonneg _) (le_of_lt hNB)
  have hA0cap : cnPlus (sideAt μ (a v)) (Φ : X n → ℝ) / normB v μ n (Φ : X n → ℝ)
      ≤ (2 * C_A / Work.BoseBox.bValue) * μ * (sideAt μ (a v)) ^ 3 * (wbEps v μ) ^ 2 := by
    have hεsq : (wbEps v μ) ^ 2 = kappa v μ * (μ * (a v) * (sideAt μ (a v)) ^ 2) := by
      rw [wbEps, kappa, mul_pow, mul_pow,
        sq_rpow_three_halves (Work.BoseFixB1.paramsAt_KB_pos hAdm).le,
        sq_rpow_quarter (by positivity : (0 : ℝ) ≤ μ * (a v) ^ 3), ← hKℓ2]
      ring
    have hcn : (paramsAt μ (a v)).b * cnPlus (sideAt μ (a v)) (Φ : X n → ℝ)
        ≤ Cnst * normB v μ n (Φ : X n → ℝ) * (2 * (sideAt μ (a v)) ^ 2) := by
      have h1 := (hAunif J μ hAdmA hJK n Φ hNB hlow).2
      rw [div_mul_eq_mul_div,
        div_le_iff₀ (show (0 : ℝ) < 2 * (sideAt μ (a v)) ^ 2 by positivity)] at h1
      linarith [h1]
    have hgoal2 : Cnst * normB v μ n (Φ : X n → ℝ) * (2 * (sideAt μ (a v)) ^ 2)
          / (paramsAt μ (a v)).b
        = (2 * C_A / Work.BoseBox.bValue) * μ * (sideAt μ (a v)) ^ 3 * (wbEps v μ) ^ 2
          * normB v μ n (Φ : X n → ℝ) := by
      rw [hCnstdef, paramsAt_b_eq μ (a v), hεsq]
      simp only [div_eq_mul_inv]
      ring
    have hdiv : cnPlus (sideAt μ (a v)) (Φ : X n → ℝ)
        ≤ Cnst * normB v μ n (Φ : X n → ℝ) * (2 * (sideAt μ (a v)) ^ 2)
          / (paramsAt μ (a v)).b := by
      rw [le_div_iff₀ (Work.BoseFixB1.paramsAt_b_pos μ (a v))]
      calc cnPlus (sideAt μ (a v)) (Φ : X n → ℝ) * (paramsAt μ (a v)).b
          = (paramsAt μ (a v)).b * cnPlus (sideAt μ (a v)) (Φ : X n → ℝ) := by ring
        _ ≤ Cnst * normB v μ n (Φ : X n → ℝ) * (2 * (sideAt μ (a v)) ^ 2) := hcn
    rw [div_le_iff₀ hNB, ← hgoal2]
    exact hdiv
  have hKUW : (C₁ * (Submission.BoseGases.chiSupAbs
        * Submission.BoseGases.chiSmallDecay (paramsAt μ (a v)).M) ^ 2 * (a v)) / wbW v h μ
      ≤ (C₁ * (Submission.BoseGases.chiSupAbs
          * Submission.BoseGases.chiSmallDecay (paramsAt μ (a v)).M) ^ 2 / Real.pi)
        / (sideAt μ (a v)) ^ 3 := by
    rw [div_le_div_iff₀ hWpos (pow_pos hℓ 3)]
    have hc : 0 ≤ C₁ * (Submission.BoseGases.chiSupAbs
        * Submission.BoseGases.chiSmallDecay (paramsAt μ (a v)).M) ^ 2 / Real.pi :=
      div_nonneg (mul_nonneg hC₁0 (sq_nonneg _)) (le_of_lt Real.pi_pos)
    have hkey : (C₁ * (Submission.BoseGases.chiSupAbs
          * Submission.BoseGases.chiSmallDecay (paramsAt μ (a v)).M) ^ 2 * (a v))
          * (sideAt μ (a v)) ^ 3
        = (C₁ * (Submission.BoseGases.chiSupAbs
            * Submission.BoseGases.chiSmallDecay (paramsAt μ (a v)).M) ^ 2 / Real.pi)
          * (Real.pi * (a v) * (sideAt μ (a v)) ^ 3) := by
      field_simp
    calc (C₁ * (Submission.BoseGases.chiSupAbs
          * Submission.BoseGases.chiSmallDecay (paramsAt μ (a v)).M) ^ 2 * (a v))
          * (sideAt μ (a v)) ^ 3
        = (C₁ * (Submission.BoseGases.chiSupAbs
            * Submission.BoseGases.chiSmallDecay (paramsAt μ (a v)).M) ^ 2 / Real.pi)
          * (Real.pi * (a v) * (sideAt μ (a v)) ^ 3) := hkey
      _ ≤ (C₁ * (Submission.BoseGases.chiSupAbs
            * Submission.BoseGases.chiSmallDecay (paramsAt μ (a v)).M) ^ 2 / Real.pi)
          * wbW v h μ := mul_le_mul_of_nonneg_left hWlow hc
  have hγle : γ ≤ wbEps v μ := by
    have hKl1 : 1 ≤ (paramsAt μ (a v)).Kl := Work.BoseFixB1.one_le_Kl hμ hav ht1
    have hfac : 0 ≤ (paramsAt μ (a v)).KB ^ (3 / 2 : ℝ) * (μ * (a v) ^ 3) ^ (1 / 4 : ℝ) :=
      mul_nonneg (Real.rpow_nonneg (Work.BoseFixB1.paramsAt_KB_pos hAdm).le _)
        (Real.rpow_nonneg (by positivity) _)
    rw [hγdef, wbEps]
    calc (paramsAt μ (a v)).KB ^ (3 / 2 : ℝ) * (μ * (a v) ^ 3) ^ (1 / 4 : ℝ)
        ≤ (paramsAt μ (a v)).KB ^ (3 / 2 : ℝ) * (μ * (a v) ^ 3) ^ (1 / 4 : ℝ)
            * (paramsAt μ (a v)).Kl := by
          simpa using mul_le_mul_of_nonneg_left hKl1 hfac
      _ = (paramsAt μ (a v)).KB ^ (3 / 2 : ℝ) * (paramsAt μ (a v)).Kl
            * (μ * (a v) ^ 3) ^ (1 / 4 : ℝ) := by ring
  have hC₂0 : 0 ≤ C₁ * (Submission.BoseGases.chiSupAbs
      * Submission.BoseGases.chiSmallDecay (paramsAt μ (a v)).M) ^ 2 / Real.pi :=
    div_nonneg (mul_nonneg hC₁0 (sq_nonneg _)) (le_of_lt Real.pi_pos)
  have hfinal := Work.BoseFixB1.WB.final_arith_exp (μ := μ) (ℓ := sideAt μ (a v))
    (W := wbW v h μ) (s := s) (C_A := C_A) (ε := wbEps v μ) (γ := γ)
    (C₁ := Real.sqrt (3 * (C_A / Real.pi)))
    (C₂ := C₁ * (Submission.BoseGases.chiSupAbs
      * Submission.BoseGases.chiSmallDecay (paramsAt μ (a v)).M) ^ 2 / Real.pi)
    (KU := C₁ * (Submission.BoseGases.chiSupAbs
      * Submission.BoseGases.chiSmallDecay (paramsAt μ (a v)).M) ^ 2 * (a v))
    (A₀ := cnPlus (sideAt μ (a v)) (Φ : X n → ℝ) / normB v μ n (Φ : X n → ℝ))
    hμ hℓ hWpos hεpos hεhalf hγ0 hγle hCA.le hA0nn (Real.sqrt_nonneg _) hC₂0 hA0cap hs hKUW (n := n)
  have hfin := hfinal hsplit_up hsplit_lo
  rw [Work.BoseFixB1.nWindow_eq_wbEps]
  calc |(n : ℝ) - μ * (sideAt μ (a v)) ^ 3|
      ≤ (2 + 2 * Real.sqrt (3 * (C_A / Real.pi))
          + 4 * (C₁ * (Submission.BoseGases.chiSupAbs * Submission.BoseGases.chiSmallDecay
                (paramsAt μ (a v)).M) ^ 2 / Real.pi) * (2 * C_A / Work.BoseBox.bValue)
          + 2 * C_A / Work.BoseBox.bValue) * μ * (sideAt μ (a v)) ^ 3 * (wbEps v μ) := hfin
    _ = (2 + 2 * Real.sqrt (3 * (C_A / Real.pi))
          + 4 * (C₁ * (Submission.BoseGases.chiSupAbs * Submission.BoseGases.chiSmallDecay
                Work.BoseBox.mValue) ^ 2 / Real.pi) * (2 * C_A / Work.BoseBox.bValue)
          + 2 * C_A / Work.BoseBox.bValue) * (wbEps v μ * (μ * (sideAt μ (a v)) ^ 3)) := by
        rw [Work.BoseFixB1.M_eq_mValue]
        ring

/-! ## 6. The target: the sharp particle window from FS's one-slot nominal per-box row

`PerBoxFNomMu` gives the nominal a-priori rows (`nomCleanRowsMu`, via `ledgerNom` and the one-sided
count window `countWindowOfNominal`); the bridge above turns them into the particle window. -/

/-- **`NomAprioriUnif` from FS's one-slot nominal per-box row.**  `ledgerNom` gives the two
a-priori rows at the nominal remainder with the prescribed error slot `E·μ(a v)κ·n‖Φ‖²`; the
one-sided count window `countWindowOfNominal` (`n ≤ C_W μℓ³`, the *upper* half of `eq:apriorinn+`)
removes that slot by absorption. -/
theorem nomCleanRowsMu {v : E3 → ℝ} (h : ScatSol v) (hv : 0 ≤ v) (hv1 : MeasureTheory.MemLp v 1)
    (hvrad : _root_.BoseGases.IsRadial v) {R : ℝ} (hR : 0 < R)
    (hv_supp : tsupport v ⊆ Metric.ball (0 : E3) R) (hav : 0 < a v)
    (hMu : PerBoxFNomMu v h R) : NomAprioriUnif v h := by
  obtain ⟨εN, c₁, C, hεN, hc₁, hC, hper⟩ := hMu
  have hperS : PerBoxFNomSlots v h R :=
    perBoxFNomSlots_of_perBoxFNomMu h hv hvrad hR hv_supp ⟨εN, c₁, C, hεN, hc₁, hC, hper⟩
  obtain ⟨εN', c₁', C', hεN', hc₁', hC', hper'⟩ := hperS
  have hS : SlidingGoodCube v h :=
    slidingGoodCube h hv hv1 hvrad hR hv_supp hav
  obtain ⟨εL, CA, hεL, hCA, hled⟩ :=
    ledgerNom (v := v) (h := h) (R := R) hv hv1 hvrad hR hv_supp hav
      (c₁ := c₁') (C := C') (E := 1) hc₁' hC' one_pos ⟨εN', hεN', hper'⟩ hS
  obtain ⟨εW, CW, hεW, hCW, hwin⟩ :=
    countWindowOfNominal h hv hv1 hvrad hR hv_supp hav hS ⟨εN', c₁', C', hεN', hc₁', hC', hper'⟩
  have hCAW0 : 0 ≤ CA + CW := add_nonneg hCA hCW
  set CA' : ℝ := max ((CA + CW) / c₁') (CA + CW) + 1 with hCA'def
  have hCA'pos : 0 < CA' := by
    rw [hCA'def]
    exact add_pos_of_nonneg_of_pos (le_trans hCAW0 (le_max_right _ _)) one_pos
  have hle1 : (CA + CW) / c₁' ≤ CA' := by
    rw [hCA'def]
    exact le_trans (le_max_left _ _) (le_add_of_nonneg_right zero_le_one)
  have hle2 : CA + CW ≤ CA' := by
    rw [hCA'def]
    exact le_trans (le_max_right _ _) (le_add_of_nonneg_right zero_le_one)
  refine ⟨CA', min εL εW, hCA'pos, lt_min hεL hεW, ?_⟩
  intro J μ hAdm hJK n Φ hN hlow
  have hμ : 0 < μ := Work.BoseFixB1.adm_mu_pos hAdm
  have hav0 : 0 ≤ a v := (Work.BoseFixB1.adm_a_pos hAdm).le
  have hℓ : 0 < sideAt μ (a v) := Work.BoseFixB1.adm_ell_pos hAdm
  have hAdmL : Adm v εL μ := Work.BoseFixB1.Adm.mono hAdm (min_le_left _ _)
  have hAdmW : Adm v εW μ := Work.BoseFixB1.Adm.mono hAdm (min_le_right _ _)
  have hNnn : 0 ≤ normB v μ n (Φ : X n → ℝ) := Work.BoseFixB1.normB_nonneg _
  have hκnn : 0 ≤ kappa v μ := kappa_nonneg hμ hav
  obtain ⟨hrow1, hrow2⟩ := hled J μ hAdmL hJK n Φ hN hlow
  have hn : (n : ℝ) ≤ CW * μ * (sideAt μ (a v)) ^ 3 := hwin J μ hAdmW hJK n Φ hN hlow
  have hE : (1 * (μ * a v * kappa v μ)) * (n : ℝ) * normB v μ n (Φ : X n → ℝ)
      ≤ CW * (μ ^ 2 * a v * (sideAt μ (a v)) ^ 3 * kappa v μ)
          * normB v μ n (Φ : X n → ℝ) := by
    have h1 : (μ * a v * kappa v μ) * (n : ℝ)
        ≤ (μ * a v * kappa v μ) * (CW * μ * (sideAt μ (a v)) ^ 3) :=
      mul_le_mul_of_nonneg_left hn (mul_nonneg (mul_nonneg hμ.le hav0) hκnn)
    calc (1 * (μ * a v * kappa v μ)) * (n : ℝ) * normB v μ n (Φ : X n → ℝ)
        ≤ ((μ * a v * kappa v μ) * (CW * μ * (sideAt μ (a v)) ^ 3))
            * normB v μ n (Φ : X n → ℝ) := by
          rw [one_mul]
          exact mul_le_mul_of_nonneg_right h1 hNnn
      _ = CW * (μ ^ 2 * a v * (sideAt μ (a v)) ^ 3 * kappa v μ)
            * normB v μ n (Φ : X n → ℝ) := by ring
  have hclean : CA * (μ ^ 2 * a v * (sideAt μ (a v)) ^ 3 * kappa v μ)
            * normB v μ n (Φ : X n → ℝ)
          + CW * (μ ^ 2 * a v * (sideAt μ (a v)) ^ 3 * kappa v μ)
            * normB v μ n (Φ : X n → ℝ)
        = (CA + CW) * (μ ^ 2 * a v * (sideAt μ (a v)) ^ 3 * kappa v μ)
            * normB v μ n (Φ : X n → ℝ) := by ring
  have hsum1 : c₁' * nomRPsi h μ (Φ : X n → ℝ)
      ≤ (CA + CW) * (μ ^ 2 * a v * (sideAt μ (a v)) ^ 3 * kappa v μ)
          * normB v μ n (Φ : X n → ℝ) := by linarith [hrow1, hE, hclean]
  have hDnn : 0 ≤ μ ^ 2 * a v * (sideAt μ (a v)) ^ 3 * kappa v μ :=
    mul_nonneg (mul_nonneg (mul_nonneg (sq_nonneg μ) hav0) (pow_nonneg hℓ.le 3)) hκnn
  constructor
  · have h2 : nomRPsi h μ (Φ : X n → ℝ)
        ≤ ((CA + CW) * (μ ^ 2 * a v * (sideAt μ (a v)) ^ 3 * kappa v μ)
              * normB v μ n (Φ : X n → ℝ)) / c₁' := by
      rw [le_div_iff₀ hc₁']
      rw [mul_comm]
      exact hsum1
    calc nomRPsi h μ (Φ : X n → ℝ)
        ≤ ((CA + CW) * (μ ^ 2 * a v * (sideAt μ (a v)) ^ 3 * kappa v μ)
              * normB v μ n (Φ : X n → ℝ)) / c₁' := h2
      _ = ((CA + CW) / c₁') * (μ ^ 2 * a v * (sideAt μ (a v)) ^ 3 * kappa v μ)
            * normB v μ n (Φ : X n → ℝ) := by ring
      _ ≤ CA' * (μ ^ 2 * a v * (sideAt μ (a v)) ^ 3 * kappa v μ)
            * normB v μ n (Φ : X n → ℝ) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hle1 hDnn) hNnn
  · have hsum2 : ((paramsAt μ (a v)).b / (2 * (sideAt μ (a v)) ^ 2))
          * cnPlus (sideAt μ (a v)) (Φ : X n → ℝ)
        ≤ (CA + CW) * (μ ^ 2 * a v * (sideAt μ (a v)) ^ 3 * kappa v μ)
            * normB v μ n (Φ : X n → ℝ) := by linarith [hrow2, hE, hclean]
    calc ((paramsAt μ (a v)).b / (2 * (sideAt μ (a v)) ^ 2))
          * cnPlus (sideAt μ (a v)) (Φ : X n → ℝ)
        ≤ (CA + CW) * (μ ^ 2 * a v * (sideAt μ (a v)) ^ 3 * kappa v μ)
            * normB v μ n (Φ : X n → ℝ) := hsum2
      _ ≤ CA' * (μ ^ 2 * a v * (sideAt μ (a v)) ^ 3 * kappa v μ)
            * normB v μ n (Φ : X n → ℝ) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hle2 hDnn) hNnn

theorem particleWindowMu {v : EuclideanSpace ℝ (Fin 3) → ℝ} (h : Work.UBB.ScatSol v)
    (hv : 0 ≤ v) (hv1 : MeasureTheory.MemLp v 1) (hvrad : _root_.BoseGases.IsRadial v) {R : ℝ}
    (hR : 0 < R) (hv_supp : tsupport v ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R)
    (hav : 0 < _root_.BoseGases.a v) (hMu : Work.BoseB1Cube.PerBoxFNomMu v h R) :
    Work.BoseB1Cube.ParticleWindowMu v h R :=
  nomWindowBridgeMu h hv hvrad hR hv_supp hav (nomCleanRowsMu h hv hv1 hvrad hR hv_supp hav hMu)

end Work.BoseB1Cube
