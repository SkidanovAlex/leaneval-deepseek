import ChallengeDeps
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Real.Pi.Bounds
import Submission.Work.BoseSWE.clearedScalarT
import Submission.Work.BoseSWE.regularBandThreshold
import Submission.Work.BoseSWE.regularQBlock
import Submission.Work.BoseSWE.regularTBlock
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission.Work.BoseSWE.regularSR2Node_holds` — node **N2** of the small-window `E` route

On a **regular** box (`Regular`: the two FS mass comparisons at loss `1/50` plus `μ|B| ≥ 1000`) the
sharp row `Dem ≤ SR2Rhs` holds for every state of the count window.

The proof is an assembly of PROVED corpus instruments with four delegated arithmetic blocks
(`clearedScalarT`, `regularTBlock`, `regularQBlock`, `regularBandThreshold`):

* `Work.BoseB1Cube.cubeBogPortRefinedR3` — the sliding Bogoliubov port at the single cube cutoff,
  bounding `bSpectralCube + bA2` below by the mass row, the credit row and the band row;
* `Work.BoseB1Cube.boxDataGatesContDiff` — the box gates (`|B| > 0`, `W = boxM1`, `W ≤ M₂`,
  `Pc ≥ S² − S`);
* `Work.BoseFixB1S.b1sCountSplit` — the count split `S + n₊ = n`;
* `Work.BoseB1Cube.bM2_le_two_mul_bW` — `M₂ ≤ 2W` (i.e. `MΔ ≤ W`);
* `Work.BoseB1Cube.w1MassB_le_sharp` + `Work.BoseFixB1S.chiMass_le_const_mul_boxMass` —
  `W ≤ K·(a v)·|B|` for the fixed constant `K`;
* `Work.BoseB1Cube.g0w0Mass_le_eight_pi_mul_a`, `Work.SmallBoxA0.g0w0Mass_nonneg_general`.

The **scalar ledger** is `regularLedgerArith`: the port rows are dominated by `a0MainLocBox`, the pair
square and the free slot `C·(a v)·μ·n₊`, which is precisely the design's
`f(λ) = ¼(λ−1)² − ½ − ν(λ+½) − ν²/4 − [(δ+κΓ)λ² + 3λν]/(2(1−δ)) − bλ − λ/18 ≥ 0` (`δ = 1/50`,
`ν = 1/(μ|B|) ≤ 10⁻³`, `κΓ ≤ 1/50`); its minimum is `f(4) ≈ 1.19` in units of `μ²W`.
-/

noncomputable section

open MeasureTheory Metric Filter
open scoped Topology Real BigOperators ENNReal

namespace Work.BoseSWE

local notation "E3" => EuclideanSpace ℝ (Fin 3)

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

/-- **The scalar ledger of the regular box.**  Pure real arithmetic: the demand, the port's mass row,
the port's credit and the port's band row are dominated by the `A₀`-main term, the pair square and
the free `C·a·μ·n₊` slot. -/
theorem regularLedgerArith {μ V a W χ G Δ S Q Pc Cp Cn K C γ band : ℝ} {n : ℕ}
    (hV : 0 < V) (hμ : 0 < μ) (ha : 0 ≤ a) (hW : 0 ≤ W) (hχ : 0 ≤ χ) (hG0 : 0 ≤ G)
    (hG8 : G ≤ 8 * Real.pi * a)
    (hreg1 : (49 / 50) * (8 * Real.pi * a) * χ ≤ W)
    (hreg2 : (49 / 50) * G * χ ≤ Δ) (hDel0 : 0 ≤ Δ) (hDelW : Δ ≤ W)
    (hS0 : 0 ≤ S) (hQ0 : 0 ≤ Q) (hnS : (n : ℝ) = S + Q) (hPc : S ^ 2 - S ≤ Pc)
    (hCn : 4 ≤ Cn) (hn1 : Cn * μ * V ≤ (n : ℝ)) (hn2 : (n : ℝ) ≤ 2 * Cn * μ * V)
    (hWV : W ≤ K * a * V) (hCp : 0 ≤ Cp) (hK : 0 ≤ K)
    (hγ0 : 0 ≤ γ) (hγle : γ ≤ 1 / 50) (hT : 1000 ≤ μ * V)
    (hband : band * V ^ 2 ≤ (1 / 100) * (n : ℝ) * (μ * V) * W)
    (hC : 3 * Cn * K + Cp * (1 + 2 * Cn) ≤ C) :
    (1 / 18) * μ * ((n : ℝ) / V) * W
        + (1 / 2) * (1 + γ) * G * ((((n : ℝ) + 1) * (n : ℝ)) / V ^ 2) * χ
        + Cp * a * (μ + (n : ℝ) / V) * Q + band
      ≤ Work.BoseFixB1.a0MainLocBox V μ W S + (1 / 2) * (Δ / V ^ 2) * Pc + C * a * μ * Q := by
  have hCn0 : 0 ≤ Cn := le_trans (by norm_num) hCn
  have hn0 : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
  have hpos : 0 < μ * V := mul_pos hμ hV
  have hlam4 : 4 * (μ * V) ≤ (n : ℝ) := by nlinarith [hCn, hn1, hpos]
  have hSc := clearedScalarT (n := (n : ℝ)) (T := μ * V) (γ := γ) hT hlam4 hγ0 hγle
  have hn1' : Cn * (μ * V) ≤ (n : ℝ) := by nlinarith [hn1]
  have hn2' : (n : ℝ) ≤ 2 * Cn * (μ * V) := by nlinarith [hn2]
  have hI := regularTBlock (T := μ * V) (V := V) (a := a) (W := W) (χ := χ)
    (G := G) (Δ := Δ) (n := (n : ℝ)) (γ := γ) (band := band)
    hn0 hW hχ ha hG0 hG8 hreg1 hreg2 hDelW hγ0 hγle hband hSc
  have hII := regularQBlock (V := V) (T := μ * V) (a := a) (W := W) (Δ := Δ)
    (Q := Q) (n := (n : ℝ)) (Cp := Cp) (Cn := Cn) (K := K) (C := C)
    hV (mul_nonneg hμ.le hV.le) ha hW hDel0 hDelW hQ0 hCn0 hn1' hn2' hWV hCp hK
    hC
  have hmain : (1 / 18) * (n : ℝ) * (μ * V) * W
      + (1 / 2) * (1 + γ) * G * χ * ((n : ℝ) + 1) * (n : ℝ) + band * V ^ 2
      + Cp * a * (μ * V + (n : ℝ)) * Q * V
      ≤ (1 / 4) * (S - μ * V) ^ 2 * W - (1 / 2) * (μ * V) ^ 2 * W
        - (W / 2) * (2 * S + μ * V) - W / 4 + (1 / 2) * Δ * Pc + C * a * (μ * V) * Q * V := by
    have hSn : S = (n : ℝ) - Q := by linarith [hnS]
    have hA0 : (1 / 4) * (S - μ * V) ^ 2 * W - (1 / 2) * (μ * V) ^ 2 * W
          - (W / 2) * (2 * S + μ * V) - W / 4
        = ((1 / 4) * ((n : ℝ) - μ * V) ^ 2 * W - (1 / 2) * (μ * V) ^ 2 * W
            - (W / 2) * (2 * (n : ℝ) + μ * V) - W / 4)
          + (-(1 / 2) * ((n : ℝ) - μ * V) * Q * W + (1 / 4) * Q ^ 2 * W + W * Q) := by
      rw [hSn]; ring
    have hJ : (1 / 2) * Δ * ((n : ℝ) ^ 2 - (n : ℝ)) - Δ * (n : ℝ) * Q
          + (1 / 2) * Δ * (Q ^ 2 + Q) ≤ (1 / 2) * Δ * Pc := by
      have hSS : S ^ 2 - S = ((n : ℝ) ^ 2 - (n : ℝ)) + (Q ^ 2 + Q - 2 * (n : ℝ) * Q) := by
        rw [hSn]; ring
      nlinarith [hSS, hPc, hDel0]
    linarith [hI, hII, hA0, hJ]
  have hVne : V ≠ 0 := ne_of_gt hV
  have hA0exp : Work.BoseFixB1.a0MainLocBox V μ W S * V ^ 2
      = (1 / 4) * (S - μ * V) ^ 2 * W - (1 / 2) * (μ * V) ^ 2 * W
        - (W / 2) * (2 * S + μ * V) - W / 4 := by
    unfold Work.BoseFixB1.a0MainLocBox
    field_simp
  have hclearL : ((1 / 18) * μ * ((n : ℝ) / V) * W
        + (1 / 2) * (1 + γ) * G * ((((n : ℝ) + 1) * (n : ℝ)) / V ^ 2) * χ
        + Cp * a * (μ + (n : ℝ) / V) * Q + band) * V ^ 2
      = (1 / 18) * (n : ℝ) * (μ * V) * W
        + (1 / 2) * (1 + γ) * G * χ * ((n : ℝ) + 1) * (n : ℝ) + band * V ^ 2
        + Cp * a * (μ * V + (n : ℝ)) * Q * V := by
    field_simp
    ring
  have hclearR : (Work.BoseFixB1.a0MainLocBox V μ W S + (1 / 2) * (Δ / V ^ 2) * Pc
        + C * a * μ * Q) * V ^ 2
      = Work.BoseFixB1.a0MainLocBox V μ W S * V ^ 2 + (1 / 2) * Δ * Pc
        + C * a * (μ * V) * Q * V := by
    field_simp
  refine (mul_le_mul_iff_of_pos_right (by positivity : (0 : ℝ) < V ^ 2)).mp ?_
  rw [hclearL, hclearR, hA0exp]
  linarith [hmain]


/-- **Node N2 of the `BoseSWE` route**: on a `Regular` box the ledger row `Dem ≤ SR2Rhs` holds for
every state of the count window.  Recipe (see `Submission/Work/BoseSWE/BRIEF.md` §2): the PROVED
sliding Bogoliubov port `Work.BoseB1Cube.cubeBogPortRefinedR3` plus `Pc ≥ S²−S`, `S + n₊ = n`,
`g0w0Mass ≤ 8πa`, `bM2 ≤ 2bW`, the gate `Work.BoseFixB1S.PerBoxGapAbsorbB1`, and the scalar ledger
of the design md §2.3 (margin `f(4) = 1.187` in units of `μ²W`). -/
theorem regularSR2Node_holds {v : EuclideanSpace ℝ (Fin 3) → ℝ} (h : Work.UBB.ScatSol v)
    (hv : 0 ≤ v) (hv1 : MeasureTheory.MemLp v 1) (hvrad : _root_.BoseGases.IsRadial v) {R : ℝ}
    (hR : 0 < R) (hv_supp : tsupport v ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R)
    (hav : 0 < _root_.BoseGases.a v) : Work.BoseSWE.RegularSR2Node v h := by
  intro Cn hCn
  obtain ⟨εP, κ, Cp, hεP, hκ0, hCp0, hport⟩ :=
    Work.BoseB1Cube.cubeBogPortRefinedR3 h hv hv1 hvrad hR hv_supp hav
  obtain ⟨εG, hεG, hgates⟩ := Work.BoseB1Cube.boxDataGatesContDiff h hv hv1 hvrad hR hv_supp hav
  obtain ⟨εΔ, hεΔ, hΔle⟩ := Work.BoseB1Cube.bM2_le_two_mul_bW h hv hv1 hvrad hR hv_supp hav
  obtain ⟨εw, hεw, hWle⟩ :=
    Work.BoseB1Cube.w1MassB_le_sharp h hv hv1 hvrad hR hv_supp hav (δ := 1) (by norm_num)
  obtain ⟨εth, hεth, hth⟩ :=
    regularBandThreshold (v := v) hav (Cp := Cp) (κ := κ) hCp0 hκ0
  let K : ℝ := 2 * (8 * Real.pi) * (Submission.BoseGases.chiSupAbs
    * Submission.BoseGases.chiSmallDecay Work.BoseBox.mValue) ^ 2
  have hK0 : 0 ≤ K := by positivity
  have hCn0 : 0 ≤ Cn := le_trans (by norm_num) hCn
  refine ⟨min (min εP (min εG εΔ)) (min εw (min εth 1)), 3 * Cn * K + Cp * (1 + 2 * Cn),
    lt_min (lt_min hεP (lt_min hεG hεΔ)) (lt_min hεw (lt_min hεth one_pos)), ?_, ?_⟩
  · have h1 : 0 ≤ 3 * Cn * K := mul_nonneg (mul_nonneg (by norm_num) hCn0) hK0
    have h2 : 0 ≤ Cp * (1 + 2 * Cn) := mul_nonneg hCp0 (by linarith)
    linarith
  · intro μ hAdm n Ψ u hu hΨc hsupp hnorm hn1 hn2 hReg
    -- ## admissibility consequences
    have hμ : 0 < μ := hAdm.1
    have hεR : μ * (_root_.BoseGases.a v) ^ 3 ≤ min (min εP (min εG εΔ)) (min εw (min εth 1)) :=
      hAdm.2.1
    have hAdmP : Work.BoseBoxFix.Adm v εP μ :=
      Work.BoseFixB1.Adm.mono hAdm
        (le_trans (min_le_left (min εP (min εG εΔ)) (min εw (min εth 1)))
          (min_le_left εP (min εG εΔ)))
    have hAdmG : Work.BoseBoxFix.Adm v εG μ :=
      Work.BoseFixB1.Adm.mono hAdm
        (le_trans (min_le_left (min εP (min εG εΔ)) (min εw (min εth 1)))
          (le_trans (min_le_right εP (min εG εΔ)) (min_le_left εG εΔ)))
    have hAdmDel : Work.BoseBoxFix.Adm v εΔ μ :=
      Work.BoseFixB1.Adm.mono hAdm
        (le_trans (min_le_left (min εP (min εG εΔ)) (min εw (min εth 1)))
          (le_trans (min_le_right εP (min εG εΔ)) (min_le_right εG εΔ)))
    have hAdmw : Work.BoseBoxFix.Adm v εw μ :=
      Work.BoseFixB1.Adm.mono hAdm
        (le_trans (min_le_right (min εP (min εG εΔ)) (min εw (min εth 1)))
          (min_le_left εw (min εth 1)))
    have hAdmth : Work.BoseBoxFix.Adm v εth μ :=
      Work.BoseFixB1.Adm.mono hAdm
        (le_trans (min_le_right (min εP (min εG εΔ)) (min εw (min εth 1)))
          (le_trans (min_le_right εw (min εth 1)) (min_le_left εth 1)))
    have hℓ : 0 < Work.BoseFixB1.bSide v μ := Work.BoseFixB1.adm_ell_pos hAdm
    have hd : 0 < Work.BoseFixB1.bD v μ := Work.BoseFixB1.adm_d_pos hAdm
    -- ## the box data of the corpus
    obtain ⟨hVpos, hWboxM1, hM1nn, hM2le, hPcnn, hcS2⟩ :=
      hgates μ hAdmG n Ψ hΨc u hu hnorm
    -- ## the count split
    have hvolA : Work.BoseFixB1.bV v μ u
        = (MeasureTheory.volume (Work.BoseFixB1.bA v μ u)).toReal := by
      rw [Work.BoseFixB1.bV, Work.BoseFixB1.bA,
        Work.SmallBoxSliding.boxMass_eq_measureReal, MeasureTheory.Measure.real_def]
    have hsplit := Work.BoseFixB1S.b1sCountSplit (N := n) (ℓ := Work.BoseFixB1.bSide v μ)
      (volA := Work.BoseFixB1.bV v μ u) hℓ hVpos
      (Work.SmallBoxSliding.measurableSet_dlBox (Work.BoseFixB1.bSide v μ)
        (Work.BoseFixB1.bD v μ) u) hvolA
      (Work.SmallBoxSliding.dlBox_subset_acube (Work.BoseFixB1.bSide v μ)
        (Work.BoseFixB1.bD v μ) u) hΨc.continuous hsupp
    rw [hnorm, mul_one] at hsplit
    -- ## the raw hypotheses of the ledger
    have hW0 : 0 ≤ Work.BoseFixB1.bW v h μ u := by
      have h1 := hM1nn
      rw [hWboxM1] at h1
      exact h1
    have hχ0 : 0 ≤ Work.SmallBoxSliding.chiMass (Work.BoseFixB1.bM v μ)
        (Work.BoseFixB1.bSide v μ) (Work.BoseFixB1.bD v μ) u :=
      Work.SmallBoxSliding.chiMass_nonneg _ _ _ _
    have hG0 : 0 ≤ Submission.BoseGases.g0w0Mass h :=
      Work.SmallBoxA0.g0w0Mass_nonneg_general (v := v) hR hv_supp h
    have hG8 : Submission.BoseGases.g0w0Mass h ≤ 8 * Real.pi * (_root_.BoseGases.a v) :=
      Work.BoseB1Cube.g0w0Mass_le_eight_pi_mul_a (v := v) hR hv hvrad hv_supp h
    have hreg1 : (49 / 50) * (8 * Real.pi * (_root_.BoseGases.a v))
        * Work.SmallBoxSliding.chiMass (Work.BoseFixB1.bM v μ) (Work.BoseFixB1.bSide v μ)
            (Work.BoseFixB1.bD v μ) u ≤ Work.BoseFixB1.bW v h μ u := hReg.1
    have hreg2 : (49 / 50) * (Submission.BoseGases.g0w0Mass h)
        * Work.SmallBoxSliding.chiMass (Work.BoseFixB1.bM v μ) (Work.BoseFixB1.bSide v μ)
            (Work.BoseFixB1.bD v μ) u
        ≤ Work.BoseFixB1S.boxM2 (Work.BoseFixB1.bV v μ u) (Work.BoseFixB1.bA v μ u)
            (Submission.BoseGases.wSmallPair (Work.BoseFixB1.bM v μ) (Work.BoseFixB1.bSide v μ)
              (Work.BoseFixB1.bD v μ) u (Submission.BoseGases.g2 v h))
          - Work.BoseFixB1.bW v h μ u := by
      have hh := hReg.2.1
      rw [Work.BoseFixB1.bM2] at hh
      exact hh
    have hDel0 : 0 ≤ Work.BoseFixB1S.boxM2 (Work.BoseFixB1.bV v μ u) (Work.BoseFixB1.bA v μ u)
          (Submission.BoseGases.wSmallPair (Work.BoseFixB1.bM v μ) (Work.BoseFixB1.bSide v μ)
            (Work.BoseFixB1.bD v μ) u (Submission.BoseGases.g2 v h))
        - Work.BoseFixB1.bW v h μ u := by
      have h1 := hM2le
      rw [hWboxM1] at h1
      linarith
    have hDelW : Work.BoseFixB1S.boxM2 (Work.BoseFixB1.bV v μ u) (Work.BoseFixB1.bA v μ u)
          (Submission.BoseGases.wSmallPair (Work.BoseFixB1.bM v μ) (Work.BoseFixB1.bSide v μ)
            (Work.BoseFixB1.bD v μ) u (Submission.BoseGases.g2 v h))
        - Work.BoseFixB1.bW v h μ u ≤ Work.BoseFixB1.bW v h μ u := by
      have h1 := hΔle μ hAdmDel u
      rw [Work.BoseFixB1.bM2] at h1
      linarith
    have hS0 : 0 ≤ Work.BoseFixB1S.boxFlatCount (Work.BoseFixB1.bV v μ u)
        (Work.BoseFixB1.bSide v μ) (Work.BoseFixB1.bA v μ u) Ψ :=
      Finset.sum_nonneg (fun i _ => integral_nonneg (fun x => sq_nonneg _))
    have hQ0 : 0 ≤ Work.BoseFixB1S.boxQCount (Work.BoseFixB1.bV v μ u)
        (Work.BoseFixB1.bSide v μ) (Work.BoseFixB1.bA v μ u) Ψ :=
      Work.BoseFixB1S.boxQCount_nonneg _ _ _ _
    have hPc0 : (Work.BoseFixB1S.boxFlatCount (Work.BoseFixB1.bV v μ u)
          (Work.BoseFixB1.bSide v μ) (Work.BoseFixB1.bA v μ u) Ψ) ^ 2
        - Work.BoseFixB1S.boxFlatCount (Work.BoseFixB1.bV v μ u)
          (Work.BoseFixB1.bSide v μ) (Work.BoseFixB1.bA v μ u) Ψ
        ≤ Work.BoseFixB1S.boxPairCount (Work.BoseFixB1.bV v μ u) (Work.BoseFixB1.bSide v μ)
          (Work.BoseFixB1.bA v μ u) Ψ := by
      simpa only [pow_two] using hcS2
    have hth' := hth μ hAdmth
    have hbandth : Cp * (Work.BoseFixB1.sbCut μ (_root_.BoseGases.a v)) ^ 3 ≤ μ / 100 := hth'.1
    have hγle : κ * Work.BoseFixB1B.PBΓ v μ ≤ 1 / 50 := hth'.2
    have hγ0 : 0 ≤ κ * Work.BoseFixB1B.PBΓ v μ := by
      refine mul_nonneg hκ0 ?_
      rw [Work.BoseB1Cube.PBΓ_eq_rpow hav hμ]
      exact (Real.rpow_pos_of_pos (by positivity) _).le
    -- ## the band row
    have hbandraw : (Cp * (_root_.BoseGases.a v)
          * (Work.BoseFixB1.sbCut μ (_root_.BoseGases.a v)) ^ 3
          * ((n : ℝ) / Work.BoseFixB1.bV v μ u)
          * Work.SmallBoxSliding.chiMass (Work.BoseFixB1.bM v μ) (Work.BoseFixB1.bSide v μ)
              (Work.BoseFixB1.bD v μ) u) * (Work.BoseFixB1.bV v μ u) ^ 2
        ≤ (1 / 100) * (n : ℝ) * (μ * Work.BoseFixB1.bV v μ u) * Work.BoseFixB1.bW v h μ u := by
      have ha0 : 0 < _root_.BoseGases.a v := hav
      have han : 0 ≤ _root_.BoseGases.a v := hav.le
      have hV0 : 0 ≤ Work.BoseFixB1.bV v μ u := hVpos.le
      have hχle : Work.SmallBoxSliding.chiMass (Work.BoseFixB1.bM v μ) (Work.BoseFixB1.bSide v μ)
            (Work.BoseFixB1.bD v μ) u
          ≤ Work.BoseFixB1.bW v h μ u
            / ((49 / 50) * (8 * Real.pi * _root_.BoseGases.a v)) := by
        rw [le_div_iff₀ (by positivity)]
        nlinarith [hreg1]
      have hcore : Cp * (_root_.BoseGases.a v) * (Work.BoseFixB1.sbCut μ (_root_.BoseGases.a v)) ^ 3
            * Work.SmallBoxSliding.chiMass (Work.BoseFixB1.bM v μ) (Work.BoseFixB1.bSide v μ)
                (Work.BoseFixB1.bD v μ) u
          ≤ μ * Work.BoseFixB1.bW v h μ u / 100 := by
        have h1 : Cp * (Work.BoseFixB1.sbCut μ (_root_.BoseGases.a v)) ^ 3
              * ((_root_.BoseGases.a v) * Work.SmallBoxSliding.chiMass (Work.BoseFixB1.bM v μ)
                  (Work.BoseFixB1.bSide v μ) (Work.BoseFixB1.bD v μ) u)
            ≤ (μ / 100) * ((_root_.BoseGases.a v)
                * Work.SmallBoxSliding.chiMass (Work.BoseFixB1.bM v μ) (Work.BoseFixB1.bSide v μ)
                    (Work.BoseFixB1.bD v μ) u) :=
          mul_le_mul_of_nonneg_right hbandth (mul_nonneg han hχ0)
        have h2 : (_root_.BoseGases.a v) * Work.SmallBoxSliding.chiMass (Work.BoseFixB1.bM v μ)
              (Work.BoseFixB1.bSide v μ) (Work.BoseFixB1.bD v μ) u
            ≤ (_root_.BoseGases.a v) * (Work.BoseFixB1.bW v h μ u
                / ((49 / 50) * (8 * Real.pi * _root_.BoseGases.a v))) :=
          mul_le_mul_of_nonneg_left hχle han
        have h3 : (μ / 100) * ((_root_.BoseGases.a v)
              * (Work.BoseFixB1.bW v h μ u
                / ((49 / 50) * (8 * Real.pi * _root_.BoseGases.a v))))
            = μ * Work.BoseFixB1.bW v h μ u / (100 * ((49 / 50) * (8 * Real.pi))) := by
          field_simp
        have hX1 : 1 ≤ (49 / 50) * (8 * Real.pi) := by nlinarith [Real.pi_gt_three]
        have hXpos : 0 < (49 / 50) * (8 * Real.pi) := by linarith
        have hinv : 1 / ((49 / 50) * (8 * Real.pi)) ≤ 1 := by
          rw [div_le_iff₀ hXpos]
          linarith
        have h4 : μ * Work.BoseFixB1.bW v h μ u / (100 * ((49 / 50) * (8 * Real.pi)))
            ≤ μ * Work.BoseFixB1.bW v h μ u / 100 := by
          have hnum : 0 ≤ μ * Work.BoseFixB1.bW v h μ u := mul_nonneg hμ.le hW0
          have he : μ * Work.BoseFixB1.bW v h μ u / (100 * ((49 / 50) * (8 * Real.pi)))
              = (μ * Work.BoseFixB1.bW v h μ u / 100) * (1 / ((49 / 50) * (8 * Real.pi))) := by
            field_simp
          rw [he]
          calc (μ * Work.BoseFixB1.bW v h μ u / 100) * (1 / ((49 / 50) * (8 * Real.pi)))
              ≤ (μ * Work.BoseFixB1.bW v h μ u / 100) * 1 :=
                mul_le_mul_of_nonneg_left hinv (by positivity)
            _ = μ * Work.BoseFixB1.bW v h μ u / 100 := by ring
        nlinarith [h1, h2, h3, h4, hμ.le, han, hχ0]
      have hstep : (Cp * (_root_.BoseGases.a v) * (Work.BoseFixB1.sbCut μ (_root_.BoseGases.a v)) ^ 3
            * ((n : ℝ) / Work.BoseFixB1.bV v μ u)
            * Work.SmallBoxSliding.chiMass (Work.BoseFixB1.bM v μ) (Work.BoseFixB1.bSide v μ)
                (Work.BoseFixB1.bD v μ) u) * (Work.BoseFixB1.bV v μ u) ^ 2
          = (Cp * (_root_.BoseGases.a v) * (Work.BoseFixB1.sbCut μ (_root_.BoseGases.a v)) ^ 3
              * Work.SmallBoxSliding.chiMass (Work.BoseFixB1.bM v μ) (Work.BoseFixB1.bSide v μ)
                  (Work.BoseFixB1.bD v μ) u) * ((n : ℝ) * Work.BoseFixB1.bV v μ u) := by
        field_simp
      rw [hstep]
      have h3 : Cp * (_root_.BoseGases.a v) * (Work.BoseFixB1.sbCut μ (_root_.BoseGases.a v)) ^ 3
            * Work.SmallBoxSliding.chiMass (Work.BoseFixB1.bM v μ) (Work.BoseFixB1.bSide v μ)
                (Work.BoseFixB1.bD v μ) u * ((n : ℝ) * Work.BoseFixB1.bV v μ u)
          ≤ (μ * Work.BoseFixB1.bW v h μ u / 100) * ((n : ℝ) * Work.BoseFixB1.bV v μ u) :=
        mul_le_mul_of_nonneg_right hcore (by positivity)
      have h4 : (μ * Work.BoseFixB1.bW v h μ u / 100) * ((n : ℝ) * Work.BoseFixB1.bV v μ u)
          = (1 / 100) * (n : ℝ) * (μ * Work.BoseFixB1.bV v μ u) * Work.BoseFixB1.bW v h μ u := by
        ring
      linarith [h3, h4]
    -- ## the `W ≤ K a V` bound
    have hWV : Work.BoseFixB1.bW v h μ u ≤ K * (_root_.BoseGases.a v) * Work.BoseFixB1.bV v μ u := by
      have hWall : Work.BoseFixB1.bW v h μ u
          ≤ 2 * (8 * Real.pi * (_root_.BoseGases.a v))
            * Work.SmallBoxSliding.chiMass (Work.BoseFixB1.bM v μ) (Work.BoseFixB1.bSide v μ)
                (Work.BoseFixB1.bD v μ) u := by
        have hh := hWle μ hAdmw u
        simp only [Work.BoseFixB1.bW, Work.BoseFixB1.bM, Work.BoseFixB1.bSide,
          Work.BoseFixB1.bD, Work.BoseFixB1.pM, Work.BoseFixB1.pL, Work.BoseFixB1.pD,
          one_add_one_eq_two] at hh ⊢
        exact hh
      have hχV : Work.SmallBoxSliding.chiMass (Work.BoseFixB1.bM v μ) (Work.BoseFixB1.bSide v μ)
            (Work.BoseFixB1.bD v μ) u
          ≤ (Submission.BoseGases.chiSupAbs
              * Submission.BoseGases.chiSmallDecay Work.BoseBox.mValue) ^ 2
            * Work.BoseFixB1.bV v μ u := by
        have hM48 : 1 ≤ (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M := by
          rw [show (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M = Work.BoseBox.mValue from rfl]
          norm_num [Work.BoseBox.mValue]
        have hh := Work.BoseFixB1S.chiMass_le_const_mul_boxMass
          (M := (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M) hM48 hℓ hd u
        simp only [Work.BoseFixB1.bM, Work.BoseFixB1.bSide, Work.BoseFixB1.bD,
          Work.BoseFixB1.bV] at hh ⊢
        exact hh
      have h2 : 2 * (8 * Real.pi * (_root_.BoseGases.a v))
            * Work.SmallBoxSliding.chiMass (Work.BoseFixB1.bM v μ) (Work.BoseFixB1.bSide v μ)
                (Work.BoseFixB1.bD v μ) u
          ≤ 2 * (8 * Real.pi * (_root_.BoseGases.a v))
            * ((Submission.BoseGases.chiSupAbs
                * Submission.BoseGases.chiSmallDecay Work.BoseBox.mValue) ^ 2
              * Work.BoseFixB1.bV v μ u) :=
        mul_le_mul_of_nonneg_left hχV (by positivity)
      have hKdef : K = 2 * (8 * Real.pi) * (Submission.BoseGases.chiSupAbs
          * Submission.BoseGases.chiSmallDecay Work.BoseBox.mValue) ^ 2 := rfl
      rw [hKdef]
      nlinarith [hWall, h2]
    -- ## the ledger
    have hledger := Work.BoseSWE.regularLedgerArith (μ := μ) (V := Work.BoseFixB1.bV v μ u)
      (a := _root_.BoseGases.a v) (W := Work.BoseFixB1.bW v h μ u)
      (χ := Work.SmallBoxSliding.chiMass (Work.BoseFixB1.bM v μ) (Work.BoseFixB1.bSide v μ)
        (Work.BoseFixB1.bD v μ) u)
      (G := Submission.BoseGases.g0w0Mass h)
      (Δ := Work.BoseFixB1S.boxM2 (Work.BoseFixB1.bV v μ u) (Work.BoseFixB1.bA v μ u)
          (Submission.BoseGases.wSmallPair (Work.BoseFixB1.bM v μ) (Work.BoseFixB1.bSide v μ)
            (Work.BoseFixB1.bD v μ) u (Submission.BoseGases.g2 v h))
        - Work.BoseFixB1.bW v h μ u)
      (S := Work.BoseFixB1S.boxFlatCount (Work.BoseFixB1.bV v μ u) (Work.BoseFixB1.bSide v μ)
        (Work.BoseFixB1.bA v μ u) Ψ)
      (Q := Work.BoseFixB1S.boxQCount (Work.BoseFixB1.bV v μ u) (Work.BoseFixB1.bSide v μ)
        (Work.BoseFixB1.bA v μ u) Ψ)
      (Pc := Work.BoseFixB1S.boxPairCount (Work.BoseFixB1.bV v μ u) (Work.BoseFixB1.bSide v μ)
        (Work.BoseFixB1.bA v μ u) Ψ)
      (Cp := Cp) (Cn := Cn) (K := K) (C := 3 * Cn * K + Cp * (1 + 2 * Cn))
      (γ := κ * Work.BoseFixB1B.PBΓ v μ)
      (band := Cp * (_root_.BoseGases.a v) * (Work.BoseFixB1.sbCut μ (_root_.BoseGases.a v)) ^ 3
        * ((n : ℝ) / Work.BoseFixB1.bV v μ u)
        * Work.SmallBoxSliding.chiMass (Work.BoseFixB1.bM v μ) (Work.BoseFixB1.bSide v μ)
            (Work.BoseFixB1.bD v μ) u)
      (n := n) hVpos hμ hav.le hW0 hχ0 hG0 hG8 hreg1 hreg2 hDel0 hDelW hS0 hQ0
      hsplit.symm hPc0 hCn hn1 hn2 hWV hCp0 hK0 hγ0 hγle hReg.2.2 hbandraw le_rfl
    -- ## the port
    have hn1' : 1 ≤ n := by
      have h1 : (1 : ℝ) ≤ (n : ℝ) := by nlinarith [hn1, hCn, hμ, hVpos, hReg.2.2]
      exact_mod_cast h1
    have hport' := hport μ hAdmP n Ψ u hu hn1' hΨc hnorm
    have hQbr : Work.UBBInputs8.cnPlusBoxInd (Work.BoseFixB1.bSide v μ)
        (Work.BoseFixB1.bA v μ u) (Work.BoseFixB1.bV v μ u) Ψ
        = Work.BoseFixB1S.boxQCount (Work.BoseFixB1.bV v μ u) (Work.BoseFixB1.bSide v μ)
            (Work.BoseFixB1.bA v μ u) Ψ := rfl
    rw [hQbr] at hport'
    simp only [Work.BoseSWE.Dem, Work.BoseSWE.SR2Rhs]
    linarith [hledger, hport']

end Work.BoseSWE
