import ChallengeDeps
import Mathlib.Algebra.Order.Star.Real
import Submission.Work.AprioriCount.cubeDenseAliveRow
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseB1Cube.cubeFibRowManifest` — the manifest fibre row in the `AprioriCount` vocabulary

This module ports the corpus's PROVED manifest fibre bound
(`Submission/Work/BoseFixB1S/fibSum_le_manifest.lean`) into the cone of
`Submission.Work.AprioriCount.cubeDenseAliveRow`, i.e. into the `b*` box vocabulary of
`Work.AprioriCount` (`bSide`, `bRatio`, `bM`, `bW`, `bV`, `bS`, `bNu`, `goodSet`, `Adm`).

## Why a port and not an import

`Submission.Work.BoseFixB1S.fibSum_le_manifest` cannot be imported together with
`Submission.Work.AprioriCount.cubeDenseAliveRow`: `BoseFixB1S.boxMuSumAgree` and
`BoseFixB1S.boxComp_sum_eq` both declare `Work.BoseFixB1S.boxPInd_add_boxQInd` (a
duplicate-declaration landmine), so the two modules cannot sit in one import cone.

## What is done here

1. **`fibSumManifestRowLocal`** — a verbatim copy of the *proof* of
   `Work.BoseFixB1S.fibSum_le_manifest` (same statement, same body, only the declaration name is
   new), using the ingredients that *do* live in this cone:
   `Work.BoseFixB1M.muPart_dlBox` (the exact `P`/`Q` slot decomposition of the fibre at `μ = -1`),
   `Work.BoseFixB1.boxPIndFibreMassB1` (the `P`-line collapses to the manifest flat term),
   `Work.BoseFixB1S.boxMuQP_le_sqrt` (Cauchy–Schwarz on the cross line),
   `Work.BoseFixB1.boxQIndFibreCountB1` (the `Q`-line carried by the excited count),
   `Work.BoseFixB1S.fibManifestArith` (the pure-real `X + 2√(YX) + Y` arithmetic) and
   `Work.BoseFixB1S.boxFibLine_fibre_nonneg` (the pointwise nonnegativity of the fibre).

2. **`boxM1WSmall1Pair_eq_w1MassB`** — the local re-derivation of the identity
   `Work.BoseFixB1S.boxM1_eq_PBW` (which lives in the un-importable
   `BoseFixB1S/condensedArmForWindow.lean`): the localised mass
   `boxM1 ℓ (dlBox ℓ d u) (wSmall1Pair h M ℓ d u)` is the *global* iterated integral
   `w1MassB h M ℓ d u`.  Proof: `Work.BoseFixB1S.boxM1_eq_nested` (the localised kernel vanishes
   off the sliding box, `Work.BoseFixB1S.wSmallPair_eq_zero_of_notMem_dlBox`) plus the definition of
   `Work.BoseFixB1.w1MassB`.

3. **`cubeFibRowManifest`** — the target: the port of the manifest row to the `b*` vocabulary, at
   `M = mValue` (the fixed regularity `(paramsAt μ (a v)).M = mValue`), with the two regime
   hypotheses `R ≤ ℓd/16`, `R ≤ ℓ·χ_R0` supplied by the PROVED
   `Work.BoseFixB1.regime_sideAt_ge` at the smaller `ε₀`, and `0 < boxMass` from the PROVED
   `Work.BoseFixB1.boxMass_pos_of_goodSet`.
-/

noncomputable section

open MeasureTheory Metric Filter
open scoped Topology Real BigOperators ENNReal

local notation "E3" => EuclideanSpace ℝ (Fin 3)

namespace Work.BoseB1Cube

open _root_.BoseGases Submission.BoseGases Work.BoseBoxFix Work.BoseBox Work.UBB
open Work.SmallBoxSliding Work.BoseFixB1

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

/-! ## 1. The manifest fibre row (local copy of the PROVED `Work.BoseFixB1S.fibSum_le_manifest`)

The statement is identical to `Work.BoseFixB1S.fibSum_le_manifest` (with the same proof body); only
the declaration name differs, so that it can live in the `AprioriCount` cone. -/

/-- **The manifest fibre row** (verbatim port of `Work.BoseFixB1S.fibSum_le_manifest`).

The localised one-body fibre integral of the sliding box is dominated by the manifest flat term
plus an `O(a)`-error carried by the excited count `n₊` and the flat count `S`:

    fibSum ≤ (M₁/|B(u)|)·S + C·(a v)·( √(n₊·(M₁/|B(u)|)·S) + n₊ ) .

The constant is `C = max (KfibConst M) (2√(KfibConst M)/√(a v))`, which may depend on `v` and `M`
but not on any box parameter. -/
theorem fibSumManifestRowLocal {v : E3 → ℝ} (h : Work.UBB.ScatSol v)
    (hv : 0 ≤ v) (hv1 : MeasureTheory.MemLp v 1) (hvrad : _root_.BoseGases.IsRadial v)
    {R : ℝ} (hR : 0 < R)
    (hv_supp : tsupport v ⊆ Metric.ball (0 : E3) R)
    (hav : 0 < _root_.BoseGases.a v) {M : ℕ} (hM : 1 ≤ M) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ {ℓ d μ : ℝ} (hℓ : 0 < ℓ) (hd : 0 < d)
        (hR16 : R ≤ ℓ * d / 16) (hRχ : R ≤ ℓ * Submission.BoseGases.chiR0)
        (u : E3) (hvol : 0 < Work.SmallBoxSliding.boxMass ℓ d u)
        {n : ℕ} {Φ : Submission.BoseGases.X n → ℝ} (hΦc : Continuous Φ),
        Work.BoseFixB1.fibSum h M ℓ d u Φ
          ≤ (Work.BoseFixB1S.boxM1 ℓ (Submission.BoseGases.dlBox ℓ d u)
                (Submission.BoseGases.wSmall1Pair h M ℓ d u)
              / Work.SmallBoxSliding.boxMass ℓ d u)
            * (Work.BoseFixB1S.boxFlatCount (Work.SmallBoxSliding.boxMass ℓ d u) ℓ
                (Submission.BoseGases.dlBox ℓ d u) Φ)
          + C * (_root_.BoseGases.a v)
              * (Real.sqrt ((Work.UBBInputs8.cnPlusBoxInd ℓ (Submission.BoseGases.dlBox ℓ d u)
                    (Work.SmallBoxSliding.boxMass ℓ d u) Φ)
                  * ((Work.BoseFixB1S.boxM1 ℓ (Submission.BoseGases.dlBox ℓ d u)
                        (Submission.BoseGases.wSmall1Pair h M ℓ d u)
                      / Work.SmallBoxSliding.boxMass ℓ d u)
                    * (Work.BoseFixB1S.boxFlatCount (Work.SmallBoxSliding.boxMass ℓ d u) ℓ
                        (Submission.BoseGases.dlBox ℓ d u) Φ)))
                + Work.UBBInputs8.cnPlusBoxInd ℓ (Submission.BoseGases.dlBox ℓ d u)
                    (Work.SmallBoxSliding.boxMass ℓ d u) Φ) := by
  classical
  refine ⟨max (Work.BoseFixB1.KfibConst M)
      (2 * Real.sqrt (Work.BoseFixB1.KfibConst M) / Real.sqrt (_root_.BoseGases.a v)),
    le_trans (Work.BoseFixB1.KfibConst_nonneg M) (le_max_left _ _), ?_⟩
  intro ℓ d μ hℓ hd hR16 hRχ u hvol n Φ hΦc
  -- ### abbreviations
  set XP : ℝ := (Work.BoseFixB1S.boxM1 ℓ (Submission.BoseGases.dlBox ℓ d u)
                  (Submission.BoseGases.wSmall1Pair h M ℓ d u)
                / Work.SmallBoxSliding.boxMass ℓ d u)
              * (Work.BoseFixB1S.boxFlatCount (Work.SmallBoxSliding.boxMass ℓ d u) ℓ
                  (Submission.BoseGases.dlBox ℓ d u) Φ) with hXPdef
  set YQ : ℝ := ∑ i : Fin n, Work.BoseFixB1S.boxMuQ (Work.SmallBoxSliding.boxMass ℓ d u) ℓ
      (Submission.BoseGases.dlBox ℓ d u) (Submission.BoseGases.wSmall1Pair h M ℓ d u) Φ i
    with hYQdef
  set ZC : ℝ := ∑ i : Fin n, Work.BoseFixB1S.boxMuQP (Work.SmallBoxSliding.boxMass ℓ d u) ℓ
      (Submission.BoseGases.dlBox ℓ d u) (Submission.BoseGases.wSmall1Pair h M ℓ d u) Φ i
    with hZCdef
  set QN : ℝ := Work.UBBInputs8.cnPlusBoxInd ℓ (Submission.BoseGases.dlBox ℓ d u)
      (Work.SmallBoxSliding.boxMass ℓ d u) Φ with hQNdef
  -- ### the fibre is pointwise nonnegative
  have hfib0 : ∀ z : E3,
      0 ≤ Submission.BoseGases.w1Fibre ℓ (Submission.BoseGases.wSmall1Pair h M ℓ d u) z :=
    fun z => Work.BoseFixB1S.boxFibLine_fibre_nonneg hR hv hvrad hv_supp h u z
  -- ### the decomposition of `fibSum` into the three box-projection fibre lines
  have hdecomp : Work.BoseFixB1.fibSum h M ℓ d u Φ
      = (∑ i : Fin n, Work.BoseFixB1S.boxMuP (Work.SmallBoxSliding.boxMass ℓ d u) ℓ
            (Submission.BoseGases.dlBox ℓ d u)
            (Submission.BoseGases.wSmall1Pair h M ℓ d u) Φ i)
        + 2 * ZC + YQ := by
    have hmu := Work.BoseFixB1M.muPart_dlBox (v := v) (R0 := R) hv_supp hR hv hvrad hv1 h
      (M := M) hM (ℓ := ℓ) (d := d) (μ := -1) hℓ hd hR16 hRχ u hvol (N := n) hΦc
    rw [hZCdef, hYQdef]
    simp only [Work.BoseFixB1.fibSum, Submission.BoseGases.w1Fibre,
      Submission.BoseGases.wSmall1Pair, neg_neg, one_mul] at hmu ⊢
    exact hmu
  -- ### the `P`-line is exactly the manifest flat term
  have hP : (∑ i : Fin n, Work.BoseFixB1S.boxMuP (Work.SmallBoxSliding.boxMass ℓ d u) ℓ
        (Submission.BoseGases.dlBox ℓ d u) (Submission.BoseGases.wSmall1Pair h M ℓ d u) Φ i)
      = XP := by
    rw [hXPdef]
    simpa only [Work.BoseFixB1S.boxMuP] using
      (Work.BoseFixB1.boxPIndFibreMassB1 (v := v) (R0 := R) hv_supp hR hv hvrad hv1 h
        (M := M) hM hℓ hd hR16 hRχ u hvol (N := n) hΦc)
  -- ### the `Q`-line is bounded by the excited count
  have hQ : YQ ≤ Work.BoseFixB1.Kfib (v := v) M * QN := by
    rw [hYQdef, hQNdef]
    simpa only [Work.BoseFixB1S.boxMuQ, Work.BoseFixB1S.boxQCount, Work.UBBInputs8.cnPlusBoxInd]
      using
      (Work.BoseFixB1.boxQIndFibreCountB1 (v := v) (R0 := R) hv_supp hR hv hvrad hv1 h
        (M := M) hM hℓ hd hR16 hRχ u hvol (N := n) hΦc)
  -- ### Cauchy–Schwarz on the cross line
  have hZle : ZC ≤ Real.sqrt YQ * Real.sqrt XP := by
    have h0 : (∑ i : Fin n, Work.BoseFixB1S.boxMuQP (Work.SmallBoxSliding.boxMass ℓ d u) ℓ
          (Submission.BoseGases.dlBox ℓ d u) (Submission.BoseGases.wSmall1Pair h M ℓ d u) Φ i)
        ≤ Real.sqrt (∑ i : Fin n, Work.BoseFixB1S.boxMuQ (Work.SmallBoxSliding.boxMass ℓ d u) ℓ
              (Submission.BoseGases.dlBox ℓ d u)
              (Submission.BoseGases.wSmall1Pair h M ℓ d u) Φ i)
          * Real.sqrt (∑ i : Fin n, Work.BoseFixB1S.boxMuP (Work.SmallBoxSliding.boxMass ℓ d u) ℓ
              (Submission.BoseGases.dlBox ℓ d u)
              (Submission.BoseGases.wSmall1Pair h M ℓ d u) Φ i) :=
      Work.BoseFixB1S.boxMuQP_le_sqrt (v := v) (R0 := R) hv_supp hR hv hvrad hv1 h
        (M := M) hM hℓ hd hR16 hRχ u hvol (N := n) hΦc
    rw [← hZCdef, ← hYQdef, hP] at h0
    exact h0
  -- ### nonnegativity
  have hY0 : 0 ≤ YQ := by
    rw [hYQdef]
    exact Finset.sum_nonneg (fun i _ => MeasureTheory.integral_nonneg_of_ae
      (Filter.Eventually.of_forall (fun x => mul_nonneg (sq_nonneg _) (hfib0 (x i)))))
  have hXP0 : 0 ≤ XP := by
    rw [hXPdef]
    refine mul_nonneg (div_nonneg ?_ (le_of_lt hvol)) ?_
    · exact MeasureTheory.integral_nonneg_of_ae
        (Filter.Eventually.of_forall (fun z => hfib0 z))
    · exact Finset.sum_nonneg (fun i _ => MeasureTheory.integral_nonneg_of_ae
        (Filter.Eventually.of_forall (fun x => sq_nonneg _)))
  have hQN0 : 0 ≤ QN := by
    rw [hQNdef]
    exact Finset.sum_nonneg (fun i _ => MeasureTheory.integral_nonneg_of_ae
      (Filter.Eventually.of_forall (fun x => sq_nonneg _)))
  -- ### the `μ`-slack arithmetic
  have hYle : YQ ≤ Work.BoseFixB1.KfibConst M * _root_.BoseGases.a v * QN := by
    refine hQ.trans (le_of_eq ?_)
    rw [Work.BoseFixB1.Kfib_eq_KfibConst_mul_a]
  have harith := Work.BoseFixB1S.fibManifestArith (κ := Work.BoseFixB1.KfibConst M)
    (a := _root_.BoseGases.a v) (X := XP) (Y := YQ) (Q := QN)
    (Work.BoseFixB1.KfibConst_nonneg M) hav hXP0 hQN0 hY0 hYle
  have hstep : XP + 2 * ZC + YQ ≤ XP + 2 * Real.sqrt (YQ * XP) + YQ := by
    have hZX : ZC ≤ Real.sqrt (YQ * XP) := by
      rw [Real.sqrt_mul hY0 XP]
      exact hZle
    linarith
  rw [hdecomp, hP]
  linarith

/-! ## 2. The bridge `boxM1 = w1MassB` (local copy of `Work.BoseFixB1S.boxM1_eq_PBW`) -/

/-- **The bridge `boxM1 = w1MassB`.**  The localised mass
`boxM1 ℓ (dlBox ℓ d u) (wSmall1Pair h M ℓ d u)`, in which every rung of the sharp-atom family is
stated, equals the global iterated integral `Work.BoseFixB1.w1MassB h M ℓ d u`.

This is the identity that `BoseFixB1S/condensedArmForWindow.lean`'s `Work.BoseFixB1S.boxM1_eq_PBW`
supplies on the other side of the cone divide; it is re-derived here from
`Work.BoseFixB1S.boxM1_eq_nested` (possible because the localised kernel vanishes off the sliding
box, `Work.BoseFixB1S.wSmallPair_eq_zero_of_notMem_dlBox`) and the definition of `w1MassB`. -/
theorem boxM1WSmall1Pair_eq_w1MassB {v : E3 → ℝ} (h : Work.UBB.ScatSol v) {M : ℕ}
    (hM : 1 ≤ M) {ℓ d : ℝ} (hℓ : 0 < ℓ) (hd : 0 < d) (u : E3) :
    Work.BoseFixB1S.boxM1 ℓ (Submission.BoseGases.dlBox ℓ d u)
        (Submission.BoseGases.wSmall1Pair h M ℓ d u)
      = Work.BoseFixB1.w1MassB h M ℓ d u := by
  rw [Work.BoseFixB1.w1MassB]
  refine Work.BoseFixB1S.boxM1_eq_nested u ?_
  intro x y hxy
  simpa only [Submission.BoseGases.wSmall1Pair] using
    Work.BoseFixB1S.wSmallPair_eq_zero_of_notMem_dlBox hM hℓ hd u
      (f := Submission.BoseGases.g0 v h) hxy

/-! ## 3. The target -/

/-- **The manifest fibre row in the `AprioriCount` box vocabulary** — the ledger's fibre row
(`Work.BoseB1Cube.cubeAliveLedgerManifest` documents how it is consumed).  It is the port of the
PROVED `Work.BoseFixB1S.fibSum_le_manifest` into the cone of `Work.AprioriCount.cubeDenseAliveRow`.

**Why a port and not an import**: `Submission.Work.BoseFixB1S.fibSum_le_manifest` cannot be imported
together with `Submission.Work.AprioriCount.cubeDenseAliveRow` — `BoseFixB1S.boxMuSumAgree` and
`BoseFixB1S.boxComp_sum_eq` both declare `Work.BoseFixB1S.boxPInd_add_boxQInd`.

**A complete proof body already exists**: `Submission/Work/BoseB1Cube/_backupManifest.lean.txt` (also
`Submission/Work/BoseB1Cube/_probeManifestCone.lean` shows a compatible cone).  Copy that proof,
dropping the two imports `Submission.Work.BoseFixB1S.fibSum_le_manifest` and
`Submission.Work.BoseFixB1S.condensedArmForWindow`; inside the proof only the *ingredients* are used
(`muPart_dlBox`, `boxPIndFibreMassB1`, `boxQIndFibreCountB1`, `boxMuQP_le_sqrt`, `fibManifestArith`,
`boxFibLine`, `boxMuP/boxMuQ/boxMuQP` of `BoxPotDefs`).

**One identity to re-derive locally** (it lives in the un-importable `condensedArmForWindow`):
`boxM1 ℓ (dlBox ℓ d u) (wSmall1Pair h M ℓ d u) = w1MassB h M ℓ d u` — via
`Work.BoseFixB1S.boxM1_eq_nested` + `Work.BoseFixB1S.wSmallPair_eq_zero_of_notMem_dlBox`, with
`Work.BoseFixB1.w1MassB` unfolded.  (Both ingredients are in the listed cone.) -/
theorem cubeFibRowManifest {v : EuclideanSpace ℝ (Fin 3) → ℝ} (h : Work.UBB.ScatSol v) (hv : 0 ≤ v)
    (hv1 : MeasureTheory.MemLp v 1) (hvrad : _root_.BoseGases.IsRadial v) {R : ℝ} (hR : 0 < R)
    (hv_supp : tsupport v ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R)
    (hav : 0 < _root_.BoseGases.a v) :
    ∃ ε₀ C : ℝ, 0 < ε₀ ∧ 0 ≤ C ∧ ∀ μ : ℝ, Work.BoseBoxFix.Adm v ε₀ μ →
      ∀ (n : ℕ) (Φ : Work.BoseKinLoc.BoxState n (Work.AprioriCount.bSide v μ))
        (u : EuclideanSpace ℝ (Fin 3)),
        u ∈ Work.SmallBoxSliding.goodSet (Work.AprioriCount.bSide v μ)
              (Work.AprioriCount.bRatio v μ) μ →
        μ * Work.BoseFixB1.flatFibSum h (Work.AprioriCount.bM v μ) (Work.AprioriCount.bSide v μ)
            (Work.AprioriCount.bRatio v μ) u (Φ : Submission.BoseGases.X n → ℝ)
          ≤ μ * (Work.AprioriCount.bW v h μ u / Work.AprioriCount.bV v μ u)
              * Work.AprioriCount.bS v μ (Φ : Submission.BoseGases.X n → ℝ) u
            + μ * C * (_root_.BoseGases.a v)
                * (Real.sqrt (Work.AprioriCount.bNu v μ (Φ : Submission.BoseGases.X n → ℝ) u
                    * (Work.AprioriCount.bW v h μ u / Work.AprioriCount.bV v μ u)
                    * Work.AprioriCount.bS v μ (Φ : Submission.BoseGases.X n → ℝ) u)
                  + Work.AprioriCount.bNu v μ (Φ : Submission.BoseGases.X n → ℝ) u) := by
  classical
  obtain ⟨Cm, hCm0, H⟩ := fibSumManifestRowLocal (v := v) h hv hv1 hvrad hR hv_supp hav
    (M := Work.BoseBox.mValue) (by norm_num [Work.BoseBox.mValue])
  obtain ⟨εreg, hεreg, hreg⟩ := Work.BoseFixB1.regime_sideAt_ge (v := v) hav hR
  refine ⟨min 1 εreg, Cm, lt_min one_pos hεreg, hCm0, ?_⟩
  intro μ hAdm n Φ u hu
  have hμ : 0 < μ := hAdm.1
  have hμa : μ * (_root_.BoseGases.a v) ^ 3 ≤ εreg :=
    le_trans hAdm.2.1 (min_le_right _ _)
  obtain ⟨hR16, hRχ⟩ := hreg μ hμ hμa
  have hℓ : 0 < Work.AprioriCount.bSide v μ := by
    rw [Work.AprioriCount.bSide]
    exact Work.BoseFixB1.adm_ell_pos hAdm
  have hd : 0 < Work.AprioriCount.bRatio v μ := by
    rw [Work.AprioriCount.bRatio]
    exact Work.BoseFixB1.adm_d_pos hAdm
  have hM1 : 1 ≤ Work.BoseBox.mValue := by norm_num [Work.BoseBox.mValue]
  have hvol : 0 < Work.SmallBoxSliding.boxMass (Work.AprioriCount.bSide v μ)
      (Work.AprioriCount.bRatio v μ) u :=
    Work.BoseFixB1.boxMass_pos_of_goodSet hℓ hd hμ hu
  have hΦc : Continuous (Φ : Submission.BoseGases.X n → ℝ) := Φ.contDiff.continuous
  -- the manifest row at the box parameters of `μ`
  have hkey := H (μ := (-1 : ℝ)) hℓ hd hR16 hRχ u hvol hΦc
  -- collapse the source's `boxM1` to `w1MassB`
  rw [boxM1WSmall1Pair_eq_w1MassB (v := v) h hM1 hℓ hd u] at hkey
  -- `flatFibSum` and `fibSum` are the same integral
  have hfs : Work.BoseFixB1.fibSum h (Work.BoseBox.mValue) (Work.AprioriCount.bSide v μ)
      (Work.AprioriCount.bRatio v μ) u (Φ : Submission.BoseGases.X n → ℝ)
      = Work.BoseFixB1.flatFibSum h (Work.BoseBox.mValue) (Work.AprioriCount.bSide v μ)
      (Work.AprioriCount.bRatio v μ) u (Φ : Submission.BoseGases.X n → ℝ) := rfl
  rw [hfs] at hkey
  -- unfold the `AprioriCount` box vocabulary on both sides
  simp only [Work.AprioriCount.bW, Work.AprioriCount.bV, Work.AprioriCount.bS,
    Work.AprioriCount.bNu, Work.AprioriCount.bM, Work.AprioriCount.bSide,
    Work.AprioriCount.bRatio, Work.AprioriCount.bA] at hkey ⊢
  -- identify the regularity `M = bM v μ` (`= mValue`)
  rw [Work.BoseFixB1.M_eq_mValue μ (_root_.BoseGases.a v)] at ⊢
  -- normalise the nestings of the products (the `sqrt` argument and the columns)
  simp only [mul_assoc] at hkey ⊢
  have h2 := mul_le_mul_of_nonneg_left hkey hμ.le
  linarith [h2]

end Work.BoseB1Cube
