import ChallengeDeps
import Mathlib.Algebra.Order.Star.Real
import Submission.Work.BoseFixB1.WB.Lead
import Submission.Work.BoseFixB1.WB.jensen_dens
import Submission.Work.BoseFixB1S.BoxNormDefs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission.Work.BoseB1Cube.NomDefs` — the **nominal (indicator-count) sliding objects**

FS `thm:aprioriHLambda` (`final_v2.tex` l.4050–4200) reads its per-box `F`-weight at the
**nominal** local density

    t(u) = (Σᵢ 1_{B(u)}(xᵢ)) / |B(u)| ,

i.e. the sharp *indicator* count of the sliding box divided by the box **volume** `boxMass`.
The corpus's `Work.BoseFixB1.RPsiB` / `wbDens` read the same object at the **smooth** density
`nCountB/chiMass` (`nCountB = Σᵢχ_{B(u)}(xᵢ)²`); by `Submission/Work/BoseFixB1S/BoxNormDefs.lean`
the two are *not* interchangeable (their ratio `chiMass/boxMass` is unbounded below on
`goodSet`), so a genuine FS-faithful chain must be run at the nominal spelling.

This module fixes the nominal objects (the state-level twins of `wbDensBox`/`RPsiBox`, with the
**indicator** count in place of the smooth count) and nothing else:

* `nomCnt`        — the sharp box count `Σᵢ 1_{B(u)}(xᵢ)` (= `FockBridge.boxCount (dlBox u)`);
* `nomBoxInner`   — the `F`-weight `∫_{abox}Φ²·F(t(u))`;
* `nomRPsi`       — FS's remainder `R_Ψ = ∫_{I₋}∬w_{1,B(u)}·F(t(u)) du`;
* `nomDens`       — the state-averaged nominal density `t(u)`;
* `nomSig`        — `∫_{I₋}∬w_{1,B(u)}·t(u) du` (FS's `⟨ΣᵢU(xᵢ)⟩`, up to the factor `wbW`).

The sliding potential `wbUSharp h μ z = ∫_{I₋}(∬w_{1,B(u)}/|B(u)|)·1_{B(u)}(z) du` and its exact
integral identity `∫_Λ U = wbW` already exist (`Submission/Work/BoseFixB1S/integral_wbUSharp.lean`),
as does the configuration-level identity linking `ΣᵢU(xᵢ)` to the sharp box count
(`sig_sharp_wbUSharp`).  The three are reused verbatim; only the `F`-weight objects are new.
-/

noncomputable section

open MeasureTheory Metric Filter
open scoped Topology Real BigOperators ENNReal

namespace Work.BoseB1Cube

open _root_.BoseGases Submission.BoseGases Work.BoseBoxFix Work.BoseBox Work.UBB Work.BoseFixB1

local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "X" => Submission.BoseGases.X

set_option autoImplicit false
set_option linter.unusedVariables false

/-- **The sharp box count** of a configuration: `Σᵢ 1_{B(u)}(xᵢ)`, where `B(u) = dlBox ℓ d u`
is the sliding box.  FS's `n(u)` of `eq:smallboxnn0n+` (`final_v2.tex:3653`), `FockBridge.boxCount`
at the box `dlBox ℓ d u`. -/
noncomputable def nomCnt (ℓ d : ℝ) (u : E3) {n : ℕ} (x : X n) : ℝ :=
  ∑ i : Fin n, Work.SmallBoxSliding.boxInd ℓ d u (x i)

lemma boxInd_nonneg' (ℓ d : ℝ) (u x : E3) : 0 ≤ Work.SmallBoxSliding.boxInd ℓ d u x := by
  rw [Work.SmallBoxSliding.boxInd]
  by_cases h : x ∈ Submission.BoseGases.dlBox ℓ d u <;> simp [h]

lemma boxInd_le_one' (ℓ d : ℝ) (u x : E3) : Work.SmallBoxSliding.boxInd ℓ d u x ≤ 1 := by
  rw [Work.SmallBoxSliding.boxInd]
  by_cases h : x ∈ Submission.BoseGases.dlBox ℓ d u <;> simp [h]

lemma nomCnt_nonneg (ℓ d : ℝ) (u : E3) {n : ℕ} (x : X n) : 0 ≤ nomCnt ℓ d u x :=
  Finset.sum_nonneg fun i _ => boxInd_nonneg' ℓ d u (x i)

lemma nomCnt_le_card (ℓ d : ℝ) (u : E3) {n : ℕ} (x : X n) : nomCnt ℓ d u x ≤ (n : ℝ) := by
  calc nomCnt ℓ d u x ≤ ∑ _i : Fin n, (1 : ℝ) :=
        Finset.sum_le_sum fun i _ => boxInd_le_one' ℓ d u (x i)
    _ = (n : ℝ) := by simp

lemma boxMass_nonneg' (ℓ d : ℝ) (u : E3) : 0 ≤ Work.SmallBoxSliding.boxMass ℓ d u := by
  rw [Work.SmallBoxSliding.boxMass]
  exact integral_nonneg fun x => boxInd_nonneg' ℓ d u x

/-- **FS's per-box `F`-weight at the nominal (indicator-count) density**:
`∫_{abox n ℓ} Φ²·F(n(u)/|B(u)|)` with `F = psiWeight 1 μ`, `n(u) = Σᵢ1_{B(u)}(xᵢ)` and
`|B(u)| = boxMass ℓ d u` (the *sharp* box volume, not the `χ_B²`-mass). -/
noncomputable def nomBoxInner {v : E3 → ℝ} (h : ScatSol v) (μ : ℝ) {n : ℕ}
    (Φ : X n → ℝ) (u : E3) : ℝ :=
  ∫ x in Submission.BoseGases.abox n (sideAt μ (_root_.BoseGases.a v)),
    (Φ x) ^ 2 * Work.SmallBoxSliding.psiWeight 1 μ
      (nomCnt (sideAt μ (_root_.BoseGases.a v)) (paramsAt μ (_root_.BoseGases.a v)).d u x
        / Work.SmallBoxSliding.boxMass (sideAt μ (_root_.BoseGases.a v))
            (paramsAt μ (_root_.BoseGases.a v)).d u)

/-- **FS's `R_Ψ` at the nominal density**: `∫_{I₋} (∬w_{1,B(u)})·F(n(u)/|B(u)|) du`.

`w1MassB h M ℓ d u` is FS's `∬w_{1,B(u)}` (`Work.BoseFixB1.w1MassB`), and `interiorSet` is the
`m(u) = 1` set `I₋`. -/
noncomputable def nomRPsi {v : E3 → ℝ} (h : ScatSol v) (μ : ℝ) {n : ℕ}
    (Φ : X n → ℝ) : ℝ :=
  ∫ u in Work.SmallBoxSliding.interiorSet (sideAt μ (_root_.BoseGases.a v))
        (paramsAt μ (_root_.BoseGases.a v)).d μ,
    w1MassB h (paramsAt μ (_root_.BoseGases.a v)).M (sideAt μ (_root_.BoseGases.a v))
        (paramsAt μ (_root_.BoseGases.a v)).d u
      * nomBoxInner h μ Φ u

/-- **The state-averaged nominal density** `t(u) = (∫Φ²·n(u))/(‖Φ‖²·|B(u)|)`: FS's `n(u)/|B(u)|`
averaged against `|Φ|²` and normalised.  This is the `boxMass`-normalised, *sharp-count* twin of
`Work.BoseFixB1.wbDens` (which uses the smooth count `nCountB` and `chiMass`). -/
noncomputable def nomDens {v : E3 → ℝ} (h : ScatSol v) (μ : ℝ) {n : ℕ}
    (Φ : X n → ℝ) (u : E3) : ℝ :=
  (∫ x in Submission.BoseGases.abox n (sideAt μ (_root_.BoseGases.a v)),
      (Φ x) ^ 2 * nomCnt (sideAt μ (_root_.BoseGases.a v))
        (paramsAt μ (_root_.BoseGases.a v)).d u x)
    / (normB v μ n Φ
        * Work.SmallBoxSliding.boxMass (sideAt μ (_root_.BoseGases.a v))
            (paramsAt μ (_root_.BoseGases.a v)).d u)

/-- **`⟨ΣᵢU(xᵢ)⟩` up to the factor `wbW`**: the `u`-average of the nominal density against the
localised one-body mass, `∫_{I₋}(∬w_{1,B(u)})·t(u) du`.  By
`Work.BoseFixB1S.sig_sharp_wbUSharp` this equals `(1/‖Φ‖²)∫_{abox}Φ²·ΣᵢwbUSharp(xᵢ)`. -/
noncomputable def nomSig {v : E3 → ℝ} (h : ScatSol v) (μ : ℝ) {n : ℕ}
    (Φ : X n → ℝ) : ℝ :=
  ∫ u in Work.SmallBoxSliding.interiorSet (sideAt μ (_root_.BoseGases.a v))
        (paramsAt μ (_root_.BoseGases.a v)).d μ,
    w1MassB h (paramsAt μ (_root_.BoseGases.a v)).M (sideAt μ (_root_.BoseGases.a v))
        (paramsAt μ (_root_.BoseGases.a v)).d u * nomDens h μ Φ u

/-- `nomBoxInner` is nonnegative for `μ > 0`. -/
lemma nomBoxInner_nonneg {v : E3 → ℝ} {h : ScatSol v} {μ : ℝ} {n : ℕ} (hμ : 0 < μ)
    (Φ : X n → ℝ) (u : E3) : 0 ≤ nomBoxInner h μ Φ u := by
  rw [nomBoxInner]
  refine integral_nonneg fun x => mul_nonneg (sq_nonneg _) ?_
  rw [Work.SmallBoxSliding.psiWeight]
  refine div_nonneg (mul_nonneg zero_le_one (sq_nonneg _)) ?_
  have h1 : 0 ≤ (nomCnt (sideAt μ (_root_.BoseGases.a v))
      (paramsAt μ (_root_.BoseGases.a v)).d u x
        / Work.SmallBoxSliding.boxMass (sideAt μ (_root_.BoseGases.a v))
          (paramsAt μ (_root_.BoseGases.a v)).d u) * μ⁻¹ :=
    mul_nonneg (div_nonneg (nomCnt_nonneg _ _ _ _) (boxMass_nonneg' _ _ _))
      (inv_nonneg.mpr hμ.le)
  linarith

/-- `nomDens` is nonnegative. -/
lemma nomDens_nonneg {v : E3 → ℝ} {h : ScatSol v} {μ : ℝ} {n : ℕ} (Φ : X n → ℝ)
    (u : E3) : 0 ≤ nomDens h μ Φ u := by
  rw [nomDens]
  refine div_nonneg (integral_nonneg fun x => mul_nonneg (sq_nonneg _) (nomCnt_nonneg _ _ _ _)) ?_
  exact mul_nonneg (normB_nonneg _) (boxMass_nonneg' _ _ _)

end Work.BoseB1Cube
