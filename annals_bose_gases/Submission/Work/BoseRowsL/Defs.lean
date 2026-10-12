import ChallengeDeps
import Submission.Work.BoseBoxFock.viewFS_of_gate
import Submission.Work.BoseGateFS.GateThresholds
import Submission.Work.BoseRowsFS.Hon
import Submission.Work.BoseRowsFS.chat_g0_lipschitz
import Submission.Work.BoseRowsFS.honest_lattice_W1sq_le_uniform
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseRowsL.Defs` — the decay-free honest interface (`HonestInterfaceL`)

Design item 7 (D5) of `Submission/Work/BOSE_ALL_DESIGN.md`: rows 1–2 of the honest
gate without **any pointwise decay** of `Ŵ₁` / `ĝ`.

## Why the decay rows had to go

`Work.BoseRowsFS.HonestInterface` carries FS's two decay rows

`|Ŵ₁(p)|(1+‖p‖)² ≤ Cw·a v`,  `|ĝ(p)|(1+‖p‖)² ≤ Cw·a v`.

Both are **false** for `v = |x|^{-3/2}·1_B` (which is an admissible potential:
`v ≥ 0`, radial, `L¹`, compactly supported, `0 < a v`): there `ĝ ≍ Ŵ₁ ≍ p^{-3/2}`,
so `|ĝ(p)|(1+‖p‖)² ≍ p^{1/2} → ∞`.  The decay-free replacement is

* `bndW` : `|Ŵ₁(p)| ≤ Cw·a v` — the sup bound (proved, `16π a v`);
* `lipW` : `|Ŵ₁(p) − Ŵ₁(q)| ≤ Cw·a v·R·‖p − q‖` — the Lipschitz bound (proved,
  constant `16π R a v`; the `ĝ` versions, constants `8π a v` and `8π R a v`, are
  **proved in the workspace** as `Work.BoseRowsFS.chat_g0_abs_le` /
  `chat_g0_lipschitz`, so they are not fields here);
* `cutR` : `1/R ≤ 2·uvRad ℓ (Ng' μ)` — the cube is at least the range of `v`;
* `tailL` : the **UV tail** of `ℓ⁻³Σ(ĝ²+Ŵ₁²)/‖k‖²` beyond `uvRad`, over a finite set
  of *lattice* points (finite-set form: no `tsum` junk).

## On the fields, and the continuum-tail field `tailC`

The design's field list is used verbatim (`Cw`, `Cw_nonneg`, `bndW`, `lipW`, `Ng'`, `Ng'_ge`,
`cutR`, `tailL`, `fsp`, `fspKz`, `rkh`, `a16`), plus the **continuum far tail** `tailC`
(`(2π)⁻³∫_{‖p‖>2Λ}(Ŵ₁²+ĝ²)/(4p²) ≤ Cw²a v(R/ℓ)⁴`, `Λ = uvRad (ellH v μ) N`).  `tailC` is a
*provable* row (`Work.BoseRowsL.Tails.tailFields` returns it), and it is carried as a field because
the gate-side composition needs it — in particular `Work.BoseGateAll.LMono`, which moves the
interface to a smaller threshold at a larger cube, matches on it.  The delivered row-2 proof
(`Row2.omegaLatticeRow_of_interface`) does *not* use it (the heat-kernel torus/free Green-function
comparison controls the truncation internally, so its only inputs are `bndW`, `tailL`, `Ng'`,
`Ng'_ge`, `Cw`), but dropping the field would break that consumer, so it stays.

The delivered row-2 proof bounds the UV-cut remainder by `tailL` and the W₁-mass by `bndW`, and
uses `H.Ng' ≥ hthr.Ng` to feed `hthr.dil`; `lipW`, `cutR` are part of the interface for the
gate-facing consumers (`Work.BoseRowsFS.HonestInterface`'s analogues), not for row 2.
-/

noncomputable section

open scoped Real BigOperators Topology
open MeasureTheory Metric

namespace Work.BoseRowsL

open Work.BoseB7 Work.BoseB7A
open Work.BoseFixR Work.BoseBoxFock Work.BoseBoxFix Work.UBB
open _root_.BoseGases Submission.BoseGases

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

/-- **`HonestInterface` with `decayW`/`decayg`/`cut`/`tail` replaced by sup +
Lipschitz bounds on `Ŵ₁`** (those on `ĝ` are the proved `chat_g0_abs_le` /
`chat_g0_lipschitz`), a cube choice `Ng'` above `hthr.Ng`, and the UV tail over
finite sets (no `tsum` junk).

The field list is the design's verbatim (`Submission/Work/BOSE_ALL_STATEMENTS.lean.txt`, item 7),
plus `tailC` (provider: `Work.BoseRowsL.Tails.tailFields`; consumer: `Work.BoseGateAll.LMono`). -/
structure HonestInterfaceL {v : ℝ³ → ℝ} {h : Work.UBB.ScatSol v} {fc fu : Work.BoseBoxFix.LowCut}
    (R : ℝ) (hthr : Work.BoseGateFS.GateThresholds v h fc fu R) where
  Cw : ℝ
  Cw_nonneg : 0 ≤ Cw
  bndW : ∀ ℓ : ℝ, 1 ≤ ℓ → R ≤ ℓ * Submission.BoseGases.chiR0 → ∀ p : ℝ³,
    |Work.BoseFixR.chat (Work.BoseFixR.W1fun v h ℓ) p| ≤ Cw * _root_.BoseGases.a v
  lipW : ∀ ℓ : ℝ, 1 ≤ ℓ → R ≤ ℓ * Submission.BoseGases.chiR0 → ∀ p q : ℝ³,
    |Work.BoseFixR.chat (Work.BoseFixR.W1fun v h ℓ) p
      - Work.BoseFixR.chat (Work.BoseFixR.W1fun v h ℓ) q| ≤ Cw * _root_.BoseGases.a v * R * ‖p - q‖
  Ng' : ℝ → ℕ
  Ng'_ge : ∀ μ, hthr.Ng μ ≤ Ng' μ
  cutR : ∀ μ : ℝ, 0 < μ → μ * _root_.BoseGases.a v ^ 3 ≤ hthr.εg →
    1 / R ≤ 2 * uvRad (ellH v μ) (Ng' μ)
  tailL : ∀ μ : ℝ, 0 < μ → μ * _root_.BoseGases.a v ^ 3 ≤ hthr.εg → ∀ N : ℕ, Ng' μ ≤ N →
    ∀ S : Finset (Fin 3 → ℤ),
      (∀ n ∈ S, uvRad (ellH v μ) N < ‖(ellH v μ)⁻¹ • Work.BoseB4.vec n‖) →
      ellH v μ ^ (-(3 : ℝ)) * ∑ n ∈ S,
          (Work.BoseFixR.chat (Submission.BoseGases.g0 v h) ((ellH v μ)⁻¹ • Work.BoseB4.vec n) ^ 2
            + Work.BoseFixR.chat (Work.BoseFixR.W1fun v h (ellH v μ))
                ((ellH v μ)⁻¹ • Work.BoseB4.vec n) ^ 2)
          / ‖(ellH v μ)⁻¹ • Work.BoseB4.vec n‖ ^ 2
        ≤ Cw ^ 2 * _root_.BoseGases.a v * (R / ellH v μ) ^ 4
  /-- **The continuum far tail** (the one field beyond the design's list; see the module
  docstring).  `(2π)⁻³∫_{‖p‖>2Λ}(Ŵ₁²+ĝ²)/(4p²)` is small, `Λ = uvRad (ellH v μ) N`. -/
  tailC : ∀ μ : ℝ, 0 < μ → μ * _root_.BoseGases.a v ^ 3 ≤ hthr.εg → ∀ N : ℕ, Ng' μ ≤ N →
    ((2 * Real.pi) ^ 3)⁻¹ *
        ∫ p in {p : ℝ³ | 2 * uvRad (ellH v μ) N < ‖p‖},
          (Work.BoseFixR.chat (Work.BoseFixR.W1fun v h (ellH v μ)) p ^ 2
            + Work.BoseFixR.chat (Submission.BoseGases.g0 v h) p ^ 2) / (4 * ‖p‖ ^ 2)
      ≤ Cw ^ 2 * _root_.BoseGases.a v * (R / ellH v μ) ^ 4
  fsp : ∀ (HM : ∀ μ : ℝ, HonestModes v μ) (μ : ℝ), 0 < μ →
    μ * _root_.BoseGases.a v ^ 3 ≤ hthr.εg →
    Work.BoseB7.FSParamsView (Work.BoseRowsFS.honE v h fc fu HM μ)
  fspKz : ∀ (HM : ∀ μ : ℝ, HonestModes v μ) (μ ρ : ℝ), 0 < μ →
    μ * _root_.BoseGases.a v ^ 3 ≤ hthr.εg →
    Work.BoseGateFS.AdmRho (Work.BoseRowsFS.honE v h fc fu HM μ) ρ →
    Work.BoseB7.FSParamsView (Work.BoseFixR.KzEnvAt (Work.BoseRowsFS.honE v h fc fu HM μ) ρ)
  rkh : ∀ (HM : ∀ μ : ℝ, HonestModes v μ) (μ : ℝ), 0 < μ →
    μ * _root_.BoseGases.a v ^ 3 ≤ hthr.εg →
    (R / (Work.BoseRowsFS.honE v h fc fu HM μ).ell) ^ 2 ≤ (Work.BoseRowsFS.honE v h fc fu HM μ).KH⁻¹
  a16 : ∀ (HM : ∀ μ : ℝ, HonestModes v μ) (μ : ℝ), 0 < μ →
    μ * _root_.BoseGases.a v ^ 3 ≤ hthr.εg →
    (Work.BoseRowsFS.honE v h fc fu HM μ).aScat * (Work.BoseRowsFS.honE v h fc fu HM μ).KH
      / ((Work.BoseRowsFS.honE v h fc fu HM μ).s * (Work.BoseRowsFS.honE v h fc fu HM μ).ell)
      ≤ 1 / 16

/-! ## 1. The `Ŵ₁` rows, proved (they are *not* fields: `bndW`/`lipW` with `Cw = 16π`) -/

/-- The sup row `bndW` holds at the honest data with `Cw = 16π`. -/
theorem bndW_data {v : ℝ³ → ℝ} {h : Work.UBB.ScatSol v} {R : ℝ} (hR : 0 < R)
    (hav : 0 < _root_.BoseGases.a v) (hv_nonneg : ∀ x : ℝ³, 0 ≤ v x)
    (hvrad : _root_.BoseGases.IsRadial v)
    (hv_supp : tsupport v ⊆ Metric.ball 0 R) :
    ∀ ℓ : ℝ, 1 ≤ ℓ → R ≤ ℓ * Submission.BoseGases.chiR0 → ∀ p : ℝ³,
      |Work.BoseFixR.chat (Work.BoseFixR.W1fun v h ℓ) p| ≤ 16 * Real.pi * _root_.BoseGases.a v := by
  intro ℓ hℓ1 hRℓ p
  exact Work.BoseB7AK.W1rows.W1hat_abs_le hR (lt_of_lt_of_le zero_lt_one hℓ1) hv_nonneg hvrad
    hv_supp h hRℓ p

/-- The Lipschitz row `lipW` holds at the honest data with `Cw = 16π`. -/
theorem lipW_data {v : ℝ³ → ℝ} {h : Work.UBB.ScatSol v} {R : ℝ} (hR : 0 < R)
    (hav : 0 < _root_.BoseGases.a v) (hv_nonneg : ∀ x : ℝ³, 0 ≤ v x)
    (hvrad : _root_.BoseGases.IsRadial v)
    (hv_supp : tsupport v ⊆ Metric.ball 0 R) :
    ∀ ℓ : ℝ, 1 ≤ ℓ → R ≤ ℓ * Submission.BoseGases.chiR0 → ∀ p q : ℝ³,
      |Work.BoseFixR.chat (Work.BoseFixR.W1fun v h ℓ) p
        - Work.BoseFixR.chat (Work.BoseFixR.W1fun v h ℓ) q|
        ≤ 16 * Real.pi * _root_.BoseGases.a v * R * ‖p - q‖ := by
  intro ℓ hℓ1 hRℓ p q
  have h := Work.BoseGateFS.chat_W1fun_lipschitz (v := v) (h := h) (R := R) (ℓ := ℓ)
    hR (lt_of_lt_of_le zero_lt_one hℓ1) hv_nonneg hvrad hv_supp hRℓ p q
  linarith [h]

/-! ## 2. The `ĝ` rows, proved (`uBndG`, `uLipG`); thin wrappers for reuse -/

/-- `|ĝ(p)| ≤ 8π a v`. -/
theorem uBndG {v : ℝ³ → ℝ} {h : Work.UBB.ScatSol v} {R : ℝ} (hR : 0 < R)
    (hv_nonneg : ∀ x : ℝ³, 0 ≤ v x) (hvrad : _root_.BoseGases.IsRadial v)
    (hv_supp : tsupport v ⊆ Metric.ball 0 R) (p : ℝ³) :
    |Work.BoseFixR.chat (Submission.BoseGases.g0 v h) p| ≤ 8 * Real.pi * _root_.BoseGases.a v :=
  Work.BoseRowsFS.chat_g0_abs_le hR hv_nonneg hvrad hv_supp h p

/-- `ĝ` is `8π R a v`-Lipschitz. -/
theorem uLipG {v : ℝ³ → ℝ} {h : Work.UBB.ScatSol v} {R : ℝ} (hR : 0 < R)
    (hv_nonneg : ∀ x : ℝ³, 0 ≤ v x) (hvrad : _root_.BoseGases.IsRadial v)
    (hv_supp : tsupport v ⊆ Metric.ball 0 R) (p q : ℝ³) :
    |Work.BoseFixR.chat (Submission.BoseGases.g0 v h) p
      - Work.BoseFixR.chat (Submission.BoseGases.g0 v h) q|
      ≤ 8 * Real.pi * R * _root_.BoseGases.a v * ‖p - q‖ :=
  Work.BoseRowsFS.chat_g0_lipschitz hR hv_nonneg hvrad hv_supp p q

/-! ## 3. The honest momentum of a label, and the two elementary consequences -/

/-- The momentum of a label of the honest cube. -/
theorem kmomLab_eq_kvec (ℓ : ℝ) (N : ℕ) (k : Lab N) :
    kmomLab ℓ N k = Work.BoseRowsFS.kvec ℓ (labVec N k) := by
  rw [Work.BoseRowsFS.kvec_eq, kmomLab]

/-- The honest `ℓ`: `ellH v μ` (positive). -/
theorem ellH_pos' (v : ℝ³ → ℝ) (μ : ℝ) : 0 < ellH v μ := ellH_pos v μ

/-- `uvRad` is positive for `N > 0`. -/
theorem uvRad_pos {ℓ : ℝ} (hℓ : 0 < ℓ) {N : ℕ} (hN : 0 < N) : 0 < uvRad ℓ N := by
  rw [uvRad]
  positivity

end Work.BoseRowsL
