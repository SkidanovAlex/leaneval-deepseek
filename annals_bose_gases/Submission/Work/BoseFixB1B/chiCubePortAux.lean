import Mathlib.Tactic.Have
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseFixB1.boxA2_add_spectral_ge_bogoliubovMain
import Submission.Work.BoseFixB1.boxWords_eq_zero_of_bI_eq_zero
import Submission.Work.BoseFixB1B.chiCubeCorrB1
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission.Work.BoseFixB1B.chiCubePortAux` — the small lemmas the `chiCubeB` port needs

Holder of `Submission/Work/BoseFixB1B/lowCountBound.lean`.  Queue item (2) of
`FINDING_flatArmCountInputs.md` §17: the sliding Bogoliubov port re-derived at the smooth cube bump.
The port's proof body refers to the window `χ := chiSmallB Mv ℓ dd u` at fourteen sites; the two
`∫χ²`/`≤ κ²·boxMass` sites are *not* pure name swaps and are supplied here, together with the
support contrapositive and the homogeneity of the bumped pairing word `bA2B`.

Declarations
* `chiCubeB_eq_zero_of_notMem_dlBox` — the contrapositive of the (already proved)
  `Work.BoseFixB1B.chiCubeB_mem_dlBox`, i.e. the `χ z = 0` off `dlBox` slot of `chainA2B`;
* **`chiCubeMassB_le_boxMass`** — `∫ (chiCubeB)² ≤ boxMass`, at **constant `1`** (the `chiSmallB`
  originals `chiMass_le_const_mul_boxMass` carry `(chiSupAbs·chiSmallDecay M)² ≈ 10^{62}`, which is
  exactly the `κ`-slot the port's ledger consumes);
* `bA2B_def`, **`bA2B_mul`** — the bumped pairing word is `boxA2` at the bumped kernel
  (`rfl`), hence homogeneous of degree two (`boxA2_mul`).
-/

noncomputable section

open MeasureTheory Metric Filter
open scoped Topology Real BigOperators ENNReal ContDiff

namespace Work.BoseFixB1B

local notation "E3" => EuclideanSpace ℝ (Fin 3)

set_option autoImplicit false
set_option linter.unusedVariables false

open Submission.BoseGases Work.SmallBoxSliding Work.BoseFixB1

/-! ## 1. Support -/

/-- **Off the box the bump vanishes** — the contrapositive of `chiCubeB_mem_dlBox`, i.e. the
`hχsupp` slot of `chainA2B`. -/
lemma chiCubeB_eq_zero_of_notMem_dlBox {M : ℕ} {ℓ d : ℝ} (hℓ : 0 < ℓ) (hd : 0 < d) (u : E3)
    {x : E3} (hx : x ∉ Submission.BoseGases.dlBox ℓ d u) : chiCubeB M ℓ d u x = 0 := by
  by_contra h
  exact hx (chiCubeB_mem_dlBox hℓ hd h)

/-! ## 2. The window mass versus the box mass, at constant `1` -/

/-- **`∫ χ² ≤ boxMass`** at constant `1`: the bumped window is supported in the box and bounded by
`1`, so its `L²`-mass is at most the box's volume.  (The `chiSmallB` twin
`Work.BoseFixB1S.chiMass_le_const_mul_boxMass` carries the astronomically large constant
`(chiSupAbs · chiSmallDecay M)²`; the bumped twin is *sharper*, and that is a genuine gain of the
smooth cube bump, cf. `FINDING_flatArmCountInputs.md` §13.) -/
lemma chiCubeMassB_le_boxMass (M : ℕ) {ℓ d : ℝ} (hℓ : 0 < ℓ) (hd : 0 < d) (u : E3) :
    chiCubeMassB M ℓ d u ≤ Work.SmallBoxSliding.boxMass ℓ d u := by
  set s : Set E3 := Submission.BoseGases.dlBox ℓ d u with hsdef
  have hs : MeasurableSet s := by
    rw [hsdef]; exact Work.SmallBoxSliding.measurableSet_dlBox ℓ d u
  have hfin : (volume : Measure ℝ³) s ≠ ⊤ := by
    rw [hsdef]; exact (Work.SmallBoxSliding.volume_dlBox_lt_top hℓ d u).ne
  have hpt : ∀ x : E3, ENNReal.ofReal ((chiCubeB M ℓ d u x) ^ 2)
      ≤ s.indicator (fun _ => (1 : ℝ≥0∞)) x := by
    intro x
    by_cases hx : x ∈ s
    · rw [Set.indicator_of_mem hx, ← ENNReal.ofReal_one]
      exact ENNReal.ofReal_le_ofReal
        (pow_le_one₀ (chiCubeB_nonneg M ℓ d u x) (chiCubeB_le_one M ℓ d u x))
    · rw [Set.indicator_of_notMem hx, chiCubeB_eq_zero_of_notMem_dlBox hℓ hd u hx]
      simp
  have hlin : ∫⁻ x : E3, ENNReal.ofReal ((chiCubeB M ℓ d u x) ^ 2)
      ≤ (volume : Measure ℝ³) s := by
    calc ∫⁻ x : E3, ENNReal.ofReal ((chiCubeB M ℓ d u x) ^ 2)
        ≤ ∫⁻ x : E3, s.indicator (fun _ => (1 : ℝ≥0∞)) x := lintegral_mono hpt
      _ = volume s := by
          rw [lintegral_indicator hs, lintegral_const, one_mul,
            MeasureTheory.Measure.restrict_apply_univ]
  have hmain : ∫ x : E3, (chiCubeB M ℓ d u x) ^ 2
      = (∫⁻ x : E3, ENNReal.ofReal ((chiCubeB M ℓ d u x) ^ 2)).toReal :=
    MeasureTheory.integral_eq_lintegral_of_nonneg_ae
      (Filter.Eventually.of_forall fun x => sq_nonneg _)
      ((chiCubeB_contDiff M ℓ d u).continuous.aestronglyMeasurable.pow 2)
  rw [chiCubeMassB_def, hmain, Work.SmallBoxSliding.boxMass_eq_measureReal,
    MeasureTheory.Measure.real_def]
  rw [← hsdef]
  exact ENNReal.toReal_mono hfin hlin

/-! ## 3. Homogeneity of the bumped pairing word -/

lemma bA2B_def {v : E3 → ℝ} (h : Work.UBB.ScatSol v) (μ : ℝ) {n : ℕ}
    (Φ : Submission.BoseGases.X n → ℝ) (u : E3) :
    bA2B h μ Φ u = Work.BoseFixB1.boxA2 (Work.BoseFixB1.bSide v μ) (Work.BoseFixB1.bV v μ u)
      (Work.BoseFixB1.bA v μ u) (wSmall1PairCube h (Work.BoseFixB1.bM v μ)
        (Work.BoseFixB1.bSide v μ) (Work.BoseFixB1.bD v μ) u) Φ := rfl

/-- **`bA2B` vanishes when the boxed `L²`-mass does** — the bumped twin of the third component of
`Work.BoseFixB1.boxWords_eq_zero_of_bI_eq_zero` (whose proof is generic in the pair kernel, so it
carries over verbatim to `wSmall1PairCube`).  This is the `hA20` slot of the port's
`∫Φ² = 0` branch. -/
lemma bA2B_eq_zero_of_bI_eq_zero {v : E3 → ℝ} (h : Work.UBB.ScatSol v) {μ : ℝ}
    {n : ℕ} {Φ : Submission.BoseGases.X n → ℝ} {u : E3}
    (hΦ : ContDiff ℝ (⊤ : ℕ∞) Φ) (hI : Work.BoseFixB1.bI v μ Φ = 0) :
    bA2B h μ Φ u = 0 := by
  rw [bA2B_def]
  rcases lt_or_ge (0 : ℝ) (Work.BoseFixB1.bSide v μ) with hpos | hnonpos
  · have h0 : ∀ y, y ∈ Submission.BoseGases.abox n (Work.BoseFixB1.bSide v μ) → Φ y = 0 :=
      Work.BoseKinLoc.Sector.eq_zero_on_abox_of_sqNormB_eq_zero hpos hΦ.continuous
        (by
          show Work.BoseKinLoc.sqNormB n (Work.BoseFixB1.bSide v μ) Φ = 0
          rw [Work.BoseKinLoc.sqNormB]
          exact hI)
    obtain ⟨-, -, -, h3, -⟩ :=
      Work.BoseFixB1.boxWords_eq_zero_of_eq_zero_on_abox (N := n)
        (a := Work.BoseFixB1.bSide v μ) (volA := Work.BoseFixB1.bV v μ u)
        (A := Work.BoseFixB1.bA v μ u) (Work.BoseFixB1.bA_subset_acube v μ u)
        (wSmall1PairCube h (Work.BoseFixB1.bM v μ) (Work.BoseFixB1.bSide v μ)
          (Work.BoseFixB1.bD v μ) u) (fun _ => 0) (fun _ => 0) h0
    exact h3
  · have hℓ : Work.BoseFixB1.bSide v μ ≤ 0 := hnonpos
    rcases n with _ | m
    · simp [Work.BoseFixB1.boxA2, Submission.BoseGases.pairSet]
    · have hvol : (volume : Measure (Submission.BoseGases.X (m + 1)))
          (Submission.BoseGases.abox (m + 1) (Work.BoseFixB1.bSide v μ)) = 0 :=
        Work.BoseFixB2.Polar.abox_volume_eq_zero_of_one_le_of_nonpos (m + 1)
          (Nat.le_add_left 1 m) _ hℓ
      rw [Work.BoseFixB1.boxA2]
      exact Finset.sum_eq_zero (fun p _ => setIntegral_measure_zero _ hvol)

/-- **Homogeneity of `bA2B`** (degree two, in the state), the bumped twin of
`Work.BoseFixB1.bA2_mul`. -/
lemma bA2B_mul {v : E3 → ℝ} (h : Work.UBB.ScatSol v) (μ t : ℝ) {n : ℕ}
    (Φ : Submission.BoseGases.X n → ℝ) (u : E3) :
    bA2B h μ (fun x => t * Φ x) u = t ^ 2 * bA2B h μ Φ u :=
  Work.BoseFixB1.boxA2_mul (Work.BoseFixB1.bSide v μ) (Work.BoseFixB1.bV v μ u)
    (A := Work.BoseFixB1.bA v μ u)
    (wSmall1PairCube h (Work.BoseFixB1.bM v μ) (Work.BoseFixB1.bSide v μ)
      (Work.BoseFixB1.bD v μ) u) t Φ

end Work.BoseFixB1B
