import Mathlib
import Submission.Work.Drive.T6GenAtDefs
import Submission.Work.Drive.hdenseDiamBridge
import Submission.Work.Drive.t5FaceAvoid
import Submission.Work.Drive.diamCoreParity
import Submission.Work.Drive.t5BoxRestricted
import Submission.Work.Drive.transportT6Sharp

/-!
# The transport `T6` from its at-one-parameter bundle **with the diameter regularity inside**

*(H4 lane, node `Work.Drive.orderSplit_model`.  Written for the lead's 2026-09-27 message, item 2:
"State the T6 wrapper WITHOUT `hodd₂`: `T6GenAtD := T6GenAt ∧ DiamFamReg` at the core meets, with `ht5`
from `odd_ncard_diamMeet_iff_coreSideCount`.  It covers `R` and `hdense`'s `P₂`; write ONE copy."
Companions: `NOTES_LEAD_hblock_uniformity.md` §4.3, `NOTES_LEAD_hdense.md` §3 (E1), `T6GenAtDefs.lean`,
`diamCoreParity.lean`, `t5FaceAvoid.lean`, `transportT6Sharp.lean`.)*

## What this file adds

`Work.Drive.T6GenAt` (`T6GenAtDefs.lean`) bundles the *loop* regularity of the transport: the core loop
of `Q` meets the sweep of `P₁` in general position, and at every core meet the **diameter** loop of `Q`
meets the sweep of `P₂` in general position.  What it does *not* contain is the *analytic* regularity of
the two interpolation families at the core meets — the four conditions `htransD`/`hfaceD`/`htransA`/
`hfaceA` of `Work.Drive.odd_ncard_diamMeet_iff_coreSideCount`.  This file

* defines the bundle `Work.Drive.DiamFamReg Q θ c P` of those four conditions (the lead's `DiamFamReg`),
  *in the box-restricted form* which is the one the design can actually produce
  (`havoid_diamFam`/`havoid_arcFam` only hold with `u ∈ unitBox 1`; see the discussion at the head of
  `t5FaceAvoid.lean`);
* defines `Work.Drive.T6GenAtD Q P₁ P₂ c₁ c₂ := T6GenAt Q P₁ P₂ c₁ c₂ ∧
  ∀ q ∈ coreMeet Q c₁ P₁, DiamFamReg Q q.1 c₂ P₂`;
* proves the **dictionary** `Work.Drive.odd_ncard_diamMeet_iff_coreSideCount_clampedSweep`, which turns
  `DiamFamReg` plus the chart/plane data into the transport's `ht5` — the composite of the two proved T5
  statements of `t5FaceAvoid.lean` §5 with the avoidances (`havoid_diamFam`, `havoid_arcFam`) and the
  smoothesses (`contMDiff_diamFam`, `contMDiff_arcFam`, `contMDiff_clampedSweep`) discharged;
* proves the wrapper
  **`Work.Drive.odd_topBdryMeet_zero_iff_coreSideCount_mul_of_T6GenAtD`**: T6's conclusion from
  `T6GenAtD` + the box parity `heven` + the truncation data `δc`/`β`, with `hfin`, `hbase`, `hfind` and
  `ht5` all *derived* from the bundle (no `hodd₂`, no `hfib*`, no `hregBase`, no `htube`).

Nothing here is new mathematics: it is the bookkeeping the lead asked for, so that the two consumers
(block `k` of the reference triple, and `hdense`'s `P₂`) can share one statement.
-/

namespace Work.Drive

open Manifold Filter Set
open scoped Manifold ContDiff Topology

attribute [local instance] Work.Drive.cappingCharted Work.Drive.isManifold_cappingCharted
  Work.Drive.t2Space_cappingSpace Work.Drive.projCharted

noncomputable section

set_option linter.style.haveILetI false
set_option linter.unusedVariables false

/-! ## 1. The family regularity at one core meet -/

/-- **The family-regularity datum of the transport at one core meet** (the lead's `DiamFamReg`):
the transversality and the face condition of the *diameter* interpolation family `diamFam Q θ` and of
the *half-circle* family `arcFam Q θ` against the clamped sweep `clampedSweep c (1 - ·) P`.

This is exactly the quartet `htransD`, `hfaceD`, `htransA`, `hfaceA` of
`Work.Drive.odd_ncard_diamMeet_iff_coreSideCount`, restated for the cutoff `ψ = fun s => 1 - s` (which
is the one the design uses) and with the `havoid` conditions kept *out* of the bundle (they are proved,
not assumed — `havoid_diamFam`, `havoid_arcFam`).

**Box-restricted (project lead's decision of 2026-09-26).**  The two *transversality* clauses carry the
box hypotheses `u ∈ unitBox 1`, `x ∈ unitBox 2`.  The unrestricted form quantifies over the *unbounded*
meet set, is neither open nor producible (`DIAMFAMREG_STATUS.md`, `NOTE_DiamFamReg_not_open.md`), and no
consumer ever uses it outside the box; the box-restricted form is exactly what the producer
`exists_diamFamRegBox_of_small_shift` supplies.  The two `hface` clauses (which always carried the box
hypotheses of the engine) are unchanged.  The T5 halves are instantiated through
`Submission.Work.Drive.t5BoxRestricted`. -/
def DiamFamReg (Q : ℂ → CappingSpace) (θ c : ℝ)
    (P : EuclideanSpace ℝ (Fin 2) → CappingSpace) : Prop :=
  -- `htransD`: the diameter family is transverse to the sweep
  (∀ (u : EuclideanSpace ℝ (Fin 2)) (x : EuclideanSpace ℝ (Fin 3)),
    diamFam Q θ u = clampedSweep c (fun s => 1 - s) P x →
    u ∈ Submission.Drive.unitBox 1 → x ∈ Submission.Drive.unitBox 2 →
    LinearMap.range (mfderiv (𝓡 2) (𝓡 4) (diamFam Q θ) u).toLinearMap ⊔
      LinearMap.range (mfderiv (𝓡 3) (𝓡 4) (clampedSweep c (fun s => 1 - s) P) x).toLinearMap
      = ⊤) ∧
  -- `hfaceD`: the face condition of the diameter family
  (∀ (u : EuclideanSpace ℝ (Fin 2)) (x : EuclideanSpace ℝ (Fin 3)),
    diamFam Q θ u = clampedSweep c (fun s => 1 - s) P x →
    u ∈ Submission.Drive.unitBox 1 → x ∈ Submission.Drive.unitBox 2 →
    (u ∈ Submission.Drive.unitBoxBdry 1 ∨ x ∈ Submission.Drive.unitBoxBdry 2) →
    (∃ i : Fin 2, (u i = 0 ∨ u i = 1) ∧ (∀ j : Fin 2, j ≠ i → u j ∈ Set.Ioo (0 : ℝ) 1) ∧
        (∀ j : Fin 3, x j ∈ Set.Ioo (0 : ℝ) 1) ∧
        ∃ (σ : EuclideanSpace ℝ (Fin 2)) (τ : EuclideanSpace ℝ (Fin 3)),
          mfderiv (𝓡 2) (𝓡 4) (diamFam Q θ) u σ
            = mfderiv (𝓡 3) (𝓡 4) (clampedSweep c (fun s => 1 - s) P) x τ ∧ σ i ≠ 0)
      ∨ (∃ j : Fin 3, (x j = 0 ∨ x j = 1) ∧ (∀ k : Fin 3, k ≠ j → x k ∈ Set.Ioo (0 : ℝ) 1) ∧
          (∀ i : Fin 2, u i ∈ Set.Ioo (0 : ℝ) 1) ∧
          ∃ (σ : EuclideanSpace ℝ (Fin 2)) (τ : EuclideanSpace ℝ (Fin 3)),
            mfderiv (𝓡 2) (𝓡 4) (diamFam Q θ) u σ
              = mfderiv (𝓡 3) (𝓡 4) (clampedSweep c (fun s => 1 - s) P) x τ ∧ τ j ≠ 0)) ∧
  -- `htransA`: the half-circle family is transverse to the sweep
  (∀ (u : EuclideanSpace ℝ (Fin 2)) (x : EuclideanSpace ℝ (Fin 3)),
    arcFam Q θ u = clampedSweep c (fun s => 1 - s) P x →
    u ∈ Submission.Drive.unitBox 1 → x ∈ Submission.Drive.unitBox 2 →
    LinearMap.range (mfderiv (𝓡 2) (𝓡 4) (arcFam Q θ) u).toLinearMap ⊔
      LinearMap.range (mfderiv (𝓡 3) (𝓡 4) (clampedSweep c (fun s => 1 - s) P) x).toLinearMap
      = ⊤) ∧
  -- `hfaceA`: the face condition of the half-circle family
  (∀ (u : EuclideanSpace ℝ (Fin 2)) (x : EuclideanSpace ℝ (Fin 3)),
    arcFam Q θ u = clampedSweep c (fun s => 1 - s) P x →
    u ∈ Submission.Drive.unitBox 1 → x ∈ Submission.Drive.unitBox 2 →
    (u ∈ Submission.Drive.unitBoxBdry 1 ∨ x ∈ Submission.Drive.unitBoxBdry 2) →
    (∃ i : Fin 2, (u i = 0 ∨ u i = 1) ∧ (∀ j : Fin 2, j ≠ i → u j ∈ Set.Ioo (0 : ℝ) 1) ∧
        (∀ j : Fin 3, x j ∈ Set.Ioo (0 : ℝ) 1) ∧
        ∃ (σ : EuclideanSpace ℝ (Fin 2)) (τ : EuclideanSpace ℝ (Fin 3)),
          mfderiv (𝓡 2) (𝓡 4) (arcFam Q θ) u σ
            = mfderiv (𝓡 3) (𝓡 4) (clampedSweep c (fun s => 1 - s) P) x τ ∧ σ i ≠ 0)
      ∨ (∃ j : Fin 3, (x j = 0 ∨ x j = 1) ∧ (∀ k : Fin 3, k ≠ j → x k ∈ Set.Ioo (0 : ℝ) 1) ∧
          (∀ i : Fin 2, u i ∈ Set.Ioo (0 : ℝ) 1) ∧
          ∃ (σ : EuclideanSpace ℝ (Fin 2)) (τ : EuclideanSpace ℝ (Fin 3)),
            mfderiv (𝓡 2) (𝓡 4) (arcFam Q θ) u σ
              = mfderiv (𝓡 3) (𝓡 4) (clampedSweep c (fun s => 1 - s) P) x τ ∧ τ j ≠ 0))

/-- **The at-one-parameter transport bundle *with* the diameter-family regularity.**  This is
`Work.Drive.T6GenAt` together with `DiamFamReg` at every core meet; it is the bundle the transport
wrapper `Work.Drive.odd_topBdryMeet_zero_iff_coreSideCount_mul_of_T6GenAtD` consumes.  (One copy, used
both for block `k` of the reference triple and for `hdense`'s `P₂`.) -/
def T6GenAtD (Q : ℂ → CappingSpace) (P₁ P₂ : EuclideanSpace ℝ (Fin 2) → CappingSpace)
    (c₁ c₂ : ℝ) : Prop :=
  T6GenAt Q P₁ P₂ c₁ c₂ ∧ ∀ q ∈ coreMeet Q c₁ P₁, DiamFamReg Q q.1 c₂ P₂

/-- **The box-restricted form of the bundle** (the project lead's name, `NOTES_LEAD_hodd_blockT6.md`
§4.1).  Since `DiamFamReg` of this file is *already* the box-restricted quartet (see its docstring), this
is a definitional restatement; it is kept as a separate name so that the design-facing wrappers read the
same at both nodes. -/
abbrev T6GenAtDBox (Q : ℂ → CappingSpace) (P₁ P₂ : EuclideanSpace ℝ (Fin 2) → CappingSpace)
    (c₁ c₂ : ℝ) : Prop :=
  T6GenAtD Q P₁ P₂ c₁ c₂

/-! ## 2. `ht5` from the bundle -/

/-- **The transport's `ht5` from `DiamFamReg`**: at a core meet `q`, the parity of the diameter meet
count against the sweep of `P` equals the side count of the sweep of `P` at the level `c`.

This is the composite of the two proved T5 statements for the clamped sweep
(`Work.Drive.odd_ncard_diamMeet_iff_arcMeet_clampedSweep` and
`Work.Drive.odd_ncard_arcMeet_iff_core_clampedSweep`, `t5FaceAvoid.lean` §5), which already discharge the
smoothness of the two loop families and the two avoidances.  It is the *sharpened* form of `ht5`
(`NOTES_LEAD_hblock_uniformity.md` §4.2): no uniformity in `θ` is claimed, only the instance at `θ`. -/
theorem odd_ncard_diamMeet_iff_coreSideCount_clampedSweep (Q : ℂ → CappingSpace) (θ c : ℝ)
    (P : EuclideanSpace ℝ (Fin 2) → CappingSpace)
    (hQ : ContMDiff (𝓘(ℝ, ℂ)) (𝓡 4) ((⊤ : ℕ∞) : WithTop ℕ∞) Q)
    (hQseam : ∀ z : ℂ, ‖z‖ = 1 → Q (-z) = Q z)
    (hP : ContMDiff (𝓡 2) (𝓡 4) ((⊤ : ℕ∞) : WithTop ℕ∞) P)
    (hPseam : ∀ y : EuclideanSpace ℝ (Fin 2), onSeam2 y → P y = P (seamInv2 y))
    (hc : 0 < c)
    (hdisj : ∀ (z : ℂ) (y : EuclideanSpace ℝ (Fin 2)), ‖z‖ ≤ 1 → Q z ≠ P y)
    (hlev : ∀ z : ℂ, ‖z‖ ≤ 1 → levelOf (Q z) ≠ c)
    (hreg : DiamFamReg Q θ c P) :
    Odd (diamMeet Q θ (clampedSweep c (fun s => 1 - s) P)).ncard ↔
      Odd (coreSideCount Q c P) :=
  (odd_ncard_diamMeet_iff_arcMeet_clampedSweepBox Q θ c (fun s => 1 - s) P hQ hQseam
    (by fun_prop) hP hPseam (by norm_num) (by norm_num) hc hdisj hlev hreg.1 hreg.2.1).trans
  (odd_ncard_arcMeet_iff_core_clampedSweepBox Q θ c P hQ hQseam hP hPseam hc
    (fun z y hz => hdisj z y (le_of_eq hz)) hlev hreg.2.2.1 hreg.2.2.2)

/-! ## 3. The T6 wrapper -/

/-- **The transport `T6` from its at-one-parameter bundle `T6GenAtD`** — the lead's
`NOTES_LEAD_hblock_uniformity.md` §4.3 wrapper, with `hodd₂` removed and `ht5` derived from the bundle.

Compared with `Work.Drive.odd_topBdryMeet_zero_iff_coreSideCount_mul_of_even_nf` (`transportT6Sharp.lean`),
the binders `hfin`, `hfind`, `hbase` and `ht5` are all *derived*: `hfin` and `hbase` from the loop clause
of `T6GenAt`, `hfind` from its diameter clause (`hfind_of_T6GenAt`), and `ht5` from `T6GenAtD`'s second
conjunct (`DiamFamReg`) via `odd_ncard_diamMeet_iff_coreSideCount_clampedSweep`.  What remains are the
box parity `heven` (the transport's own `S4`/box input), the chart data of `Q`, the plane data of `P₂`,
the truncation data `δc`/`β`, and the bundle. -/
theorem odd_topBdryMeet_zero_iff_coreSideCount_mul_of_T6GenAtD
    (β : ℝ → ℝ) (Q : ℂ → CappingSpace)
    (P₁ P₂ : EuclideanSpace ℝ (Fin 2) → CappingSpace) (c₀ c₁ c₂ : ℝ)
    (heven : Even (colCount β Q (clampedSweep c₁ (fun t => 1 - t) P₁)
          (clampedSweep c₂ (fun t => 1 - t) P₂) 0
        + colCount β Q (clampedSweep c₁ (fun t => 1 - t) P₁)
          (clampedSweep c₂ (fun t => 1 - t) P₂) 1))
    (hQ : ContMDiff (𝓘(ℝ, ℂ)) (𝓡 4) ((⊤ : ℕ∞) : WithTop ℕ∞) Q)
    (hQseam : ∀ z : ℂ, ‖z‖ = 1 → Q (-z) = Q z)
    (hP₂ : ContMDiff (𝓡 2) (𝓡 4) ((⊤ : ℕ∞) : WithTop ℕ∞) P₂)
    (hP₂seam : ∀ y : EuclideanSpace ℝ (Fin 2), onSeam2 y → P₂ y = P₂ (seamInv2 y))
    (hc₂ : 0 < c₂)
    (hdisj : ∀ (z : ℂ) (y : EuclideanSpace ℝ (Fin 2)), ‖z‖ ≤ 1 → Q z ≠ P₂ y)
    (hlev : ∀ z : ℂ, ‖z‖ ≤ 1 → levelOf (Q z) ≠ c₂)
    {δc : ℝ} (hδ : 0 ≤ δc) (hβδ : ∀ t : ℝ, δc ^ 2 ≤ t → β t = Real.sqrt t)
    (hδcut : ∀ x : EuclideanSpace ℝ (Fin 2), ‖cplxOf x‖ ≤ δc →
      x ∉ diskCut Q (clampedSweep c₂ (fun t => 1 - t) P₂))
    (hgen : T6GenAtD Q P₁ P₂ c₁ c₂) :
    Odd (topBdryMeet CappingSpace
        (fun k => clampedSweep (![c₀, c₁, c₂] k) (fun t => 1 - t)
          (![diskPlane Q, P₁, P₂] k)) 0).ncard ↔
      Odd (coreSideCount Q c₁ P₁) ∧ Odd (coreSideCount Q c₂ P₂) := by
  have hGL : GoodLoopChain (coreLoop Q) (clampedSweep c₁ (fun t => 1 - t) P₁) := hgen.1.1
  have hreg : ∀ q ∈ coreMeet Q c₁ P₁, DiamFamReg Q q.1 c₂ P₂ := hgen.2
  -- the loop clause of the bundle: finiteness and interiority of the core meets
  have hfin : (coreMeet Q c₁ P₁).Finite := hGL.1
  have hbase : ∀ y ∈ Submission.Drive.unitBox 2,
      coreLoop Q 1 ≠ clampedSweep c₁ (fun t => 1 - t) P₁ y := by
    intro y hy heq
    have hmem : (1, y) ∈ coreMeet Q c₁ P₁ :=
      ⟨Set.right_mem_Icc.mpr zero_le_one, hy, heq⟩
    exact absurd (hGL.2.1 (1, y) hmem).1.2 (lt_irrefl (1 : ℝ))
  -- `hfind` from the diameter clause of the bundle
  have hfind : ∀ q ∈ coreMeet Q c₁ P₁,
      (diamMeet Q q.1 (clampedSweep c₂ (fun t => 1 - t) P₂)).Finite :=
    hfind_of_T6GenAt hgen.1
  -- `ht5` from `DiamFamReg` at the core meets
  have ht5 : ∀ q ∈ coreMeet Q c₁ P₁,
      Odd (diamMeet Q q.1 (clampedSweep c₂ (fun t => 1 - t) P₂)).ncard ↔
        Odd (coreSideCount Q c₂ P₂) :=
    fun q hq => odd_ncard_diamMeet_iff_coreSideCount_clampedSweep Q q.1 c₂ P₂ hQ hQseam hP₂ hP₂seam
      hc₂ hdisj hlev (hreg q hq)
  exact odd_topBdryMeet_zero_iff_coreSideCount_mul_of_even_nf β Q P₁ P₂ c₀ c₁ c₂ heven hQseam
    hδ hβδ hδcut hfin hfind hbase ht5

end

end Work.Drive
