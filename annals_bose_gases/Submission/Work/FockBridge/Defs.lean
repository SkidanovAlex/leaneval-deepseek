import Mathlib.Order.CompletePartialOrder
import Mathlib.Topology.Separation.CompletelyRegular
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.SmallBoxSliding.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission.Work.FockBridge.Defs` — the Fock / particle-number layer of the sliding box

**Read `Submission/Work/hlocWire/README.md` §§4–6, `Submission/Work/UBBInputs2/README.md` §4(c)
and `Submission/Work/UBBInputs8/README.md` (R2) first.**

The `hsum` clause of the sliding per-box bundle
(`Work.hlocWire.BoxSumBoundCoreBig`, the residual named `hsum` there) is the *count ↔
localised-density bridge*: the delivered per-box energy bound
`Submission.BoseGases.smallbox_dl_energy_bound_at_count` is indexed by the **discrete count** `P`
(`Work.BlockBound4.diagWeBAt P`), while the sliding box `B(u)` carries the state's **real local
density** `n(u)/|B(u)|`.  Passing between the two is the operator-level form of FS
`thm:smallbox` (`final_v2.tex` l. 3907–4010), whose whole point is that FS's `n` in `thm:smallbox`
is the *operator*

    n_{B(u)} = Σ_i 1_{B(u)}(x_i)                      (FS eq:smallboxnn0n+, l. 3658)

which commutes with `H_{B(u)}` (`final_v2.tex` l. 3662) and whose *expectation* in the big-box
state is the real localised number — so FS never need the count to be an integer, only the
*convexity* of the per-box bound in `n/|B|`.

This chapter builds the Fock-space layer of that passage:

* **`Defs.lean`** (this file) — the counting function `n_B = Σ_i 1_B(x_i)`, its **sectors**
  (`boxOccupancy = k`), the **sector masses** of a state, the **localised number** and density,
  and the DL threshold functions.
* **`Count.lean`** — the API of the counting layer: the sectors partition the configuration space,
  the mass identity `Σ_k (sector mass) = ∫_{abox} Φ²`, the count identity
  `∫ boxCount·Φ² = Σ_k k·(sector mass)`, the locality of the box projections `P_{B,i}, Q_{B,i}`
  on the sectors, and the **multiplication-form additivity** of the localised potential word.
* **`Mixture.lean`** — the mixture/Jensen layer: the finite-mixture Jensen inequality, the
  convexity of FS's `F(t) = c(t−μ)²/(1+tμ⁻¹)` on `t ≥ 0`, and hence the *count → density* passage
  `Σ_k m_k β(k) ≥ M·β(Σ_k k m_k/M)` for the DL threshold `β`.
* **`Residual.lean`** — the exact residual: the **sector bridge** (the corpus-side form of FS
  `thm:smallbox` at the counting operator) and its two named halves.
* **`Bridge.lean`** — the assembly: the sector bridge + Jensen + the `u`-integration normalisation
  (`∫_u chiMass = ℓ³`, delivered) give the `hsum` inequality.

## Conventions

* `ℝ³ = EuclideanSpace ℝ (Fin 3)`, `X N = Fin N → ℝ³` (the corpus configuration space);
* `abox N L` is the corpus centred `N`-particle box `Λ(L)^N`, and every mass in this chapter is
  taken over `abox N L` — the same normalisation slot as the corpus's `sqNormN N L Φ` and the
  bundle's `sqNormN N L (Φ : X N → ℝ) = 1`;
* `n_B(x) = Σ_{i} 1_B(x_i)` is FS's counting function; the *sectors* are the level sets of
  `boxOccupancy B x = Σ_i 1_B(x_i) : ℕ`;
* the localised number is `∫_{abox} n_B(x)·Φ(x)² dx` and the localised *density* is that number
  divided by the box's `χ`-mass (`Work.SmallBoxSliding.chiMass`), which is FS's `|B(u)| =
  ∫χ_{B(u)}²` (FS `eq:chiBintegral`, l. 3524), **not** the nominal volume `(ℓd)³`;
* `dlThreshold c C μ av V Γ k` is the left-hand side of the delivered per-box bound
  `smallbox_dl_energy_bound_at_count` at count `k`, with `V = |B|` the `χ`-mass;
  `dlDensityThreshold c C μ av V Γ t` is the same at the real density `t`.
-/

noncomputable section

open MeasureTheory Metric Filter
open scoped ContDiff Topology Real BigOperators ENNReal

namespace Work.FockBridge

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

open Submission.BoseGases
open BoseGases
open Classical

set_option autoImplicit false
set_option linter.unusedVariables false

/-! ## 1. The counting function of a box and its sectors -/

variable {N : ℕ}

/-- **The `B`-occupancy** of a configuration `x : X N`: the number of slots `i` whose particle
lies in the box `B`.  This is FS's `n_{B}` of `eq:smallboxnn0n+` before casting to `ℝ`. -/
def boxOccupancy (B : Set ℝ³) (x : X N) : ℕ :=
  (Finset.univ.filter (fun i : Fin N => x i ∈ B)).card

/-- **The box counting function** `n_B(x) = Σ_i 1_B(x_i)` (FS `eq:smallboxnn0n+`).  It is the
multiplication operator whose expectation is the state's localised particle number. -/
def boxCount (B : Set ℝ³) (x : X N) : ℝ := (boxOccupancy B x : ℝ)

/-- The `B`-occupancy as a sum of slot indicators (the form in which measurability and
additivity are proved). -/
theorem boxCount_eq_sum_indicator (B : Set ℝ³) (x : X N) :
    boxCount B x = ∑ i : Fin N, B.indicator (fun _ => (1 : ℝ)) (x i) := by
  classical
  rw [boxCount, boxOccupancy]
  rw [Finset.natCast_card_filter (R := ℝ) (p := fun i : Fin N => x i ∈ B) (s := Finset.univ)]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  by_cases h : x i ∈ B
  · rw [Set.indicator_of_mem h, if_pos h]
  · rw [Set.indicator_of_notMem h, if_neg h]

/-- The `B`-occupancy is at most `N`: the count is a bounded counting function. -/
theorem boxOccupancy_le (B : Set ℝ³) (x : X N) : boxOccupancy B x ≤ N := by
  classical
  have h := Finset.card_le_univ (Finset.univ.filter (fun i : Fin N => x i ∈ B))
  simpa [boxOccupancy, Fintype.card_fin] using h

/-- `0 ≤ n_B ≤ N` pointwise. -/
theorem boxCount_nonneg (B : Set ℝ³) (x : X N) : 0 ≤ boxCount B x := by
  rw [boxCount]; exact Nat.cast_nonneg _

theorem boxCount_le (B : Set ℝ³) (x : X N) : boxCount B x ≤ N := by
  rw [boxCount]; exact_mod_cast boxOccupancy_le B x

/-- Measurability of the counting function. -/
theorem measurable_boxCount (B : Set ℝ³) (hB : MeasurableSet B) :
    Measurable (boxCount (N := N) B) := by
  have h1 : Measurable (fun y : ℝ³ => B.indicator (fun _ => (1 : ℝ)) y) :=
    Measurable.indicator measurable_const hB
  have hfun : boxCount (N := N) B
      = fun x : X N => ∑ i : Fin N, B.indicator (fun _ => (1 : ℝ)) (x i) :=
    funext (boxCount_eq_sum_indicator B)
  rw [hfun]
  exact Finset.measurable_sum _ (fun i _ => h1.comp (measurable_pi_apply i))

/-- **The `B`-sector of count `k`**: the configurations with exactly `k` particles in `B`. -/
def sectorSet (B : Set ℝ³) (k : ℕ) : Set (X N) := {x : X N | boxOccupancy B x = k}

theorem mem_sectorSet_iff (B : Set ℝ³) (k : ℕ) (x : X N) :
    x ∈ sectorSet B k ↔ boxOccupancy B x = k := Iff.rfl

theorem sectorSet_measurable (B : Set ℝ³) (hB : MeasurableSet B) (k : ℕ) :
    MeasurableSet (sectorSet (N := N) B k) := by
  have h : sectorSet B k = (fun x : X N => boxCount B x) ⁻¹' {(k : ℝ)} := by
    ext x
    simp only [Set.mem_preimage, Set.mem_singleton_iff, mem_sectorSet_iff, boxCount,
      Nat.cast_inj]
  rw [h]
  exact (measurable_boxCount B hB) (measurableSet_singleton (k : ℝ))

theorem sectorSet_disjoint (B : Set ℝ³) {k l : ℕ} (hkl : k ≠ l) :
    Disjoint (sectorSet (N := N) B k) (sectorSet B l) := by
  rw [Set.disjoint_left]
  intro x hk hl
  simp only [mem_sectorSet_iff] at hk hl
  exact hkl (hk ▸ hl)

theorem iUnion_sectorSet (B : Set ℝ³) :
    (⋃ k : ℕ, sectorSet (N := N) B k) = Set.univ := by
  ext x
  simp only [Set.mem_iUnion, Set.mem_univ, iff_true, mem_sectorSet_iff]
  exact ⟨boxOccupancy B x, rfl⟩

theorem sectorSet_eq_empty_of_lt (B : Set ℝ³) {k : ℕ} (hk : N < k) :
    sectorSet (N := N) B k = ∅ := by
  ext x
  simp only [mem_sectorSet_iff, Set.mem_empty_iff_false, iff_false]
  intro h
  exact absurd (h ▸ boxOccupancy_le B x : k ≤ N) (not_le.mpr hk)

/-- **The sector partition.**  On the whole configuration space the sector indicators sum to one:
the occupancy always lies in `{0,…,N}`. -/
theorem sum_indicator_sectorSet {α : Type*} [AddCommMonoid α] (B : Set ℝ³) (g : X N → α) (x : X N) :
    ∑ k ∈ Finset.range (N + 1), (sectorSet B k).indicator g x = g x := by
  classical
  have hmem : boxOccupancy B x ∈ Finset.range (N + 1) :=
    Finset.mem_range.mpr (Nat.lt_succ_of_le (boxOccupancy_le B x))
  have h₁ : ∑ k ∈ Finset.range (N + 1), (sectorSet B k).indicator g x
      = ∑ k ∈ Finset.range (N + 1), if k = boxOccupancy B x then g x else 0 := by
    refine Finset.sum_congr rfl (fun k _ => ?_)
    by_cases h : k = boxOccupancy B x
    · rw [if_pos h, h, Set.indicator_of_mem (show x ∈ sectorSet B (boxOccupancy B x) from rfl)]
    · rw [if_neg h, Set.indicator_of_notMem]
      intro hx
      exact h ((mem_sectorSet_iff B k x).mp hx).symm
  rw [h₁, Finset.sum_ite_eq']
  exact if_pos hmem

/-- **The amplitude sector of slot `i`** at count `k`: the configurations from which the slot-`i`
windowed amplitude of a state *supported in the `B`-sector `k`* can be nonzero.  The amplitude
replaces slot `i` by a point `z ∈ supp χ ⊆ B`, so the occupancy seen through the amplitude is
`boxOccupancy A x` when `x i ∈ A` and `boxOccupancy A x + 1` otherwise; this is the shifted count
that the kinetic half of the Fock decomposition sees. -/
def ampSector (A : Set ℝ³) (i : Fin N) (k : ℕ) : Set (X N) :=
  {x : X N | (if x i ∈ A then boxOccupancy A x else boxOccupancy A x + 1) = k}

theorem mem_ampSector_iff (A : Set ℝ³) (i : Fin N) (k : ℕ) (x : X N) :
    x ∈ ampSector A i k
      ↔ (if x i ∈ A then boxOccupancy A x else boxOccupancy A x + 1) = k := Iff.rfl

/-- The amplitude sectors of two different counts are disjoint (the shifted count is a function of
the configuration), so a family of sector-supported pieces produces disjointly supported amplitudes
and the squared-norm sum splits. -/
theorem ampSector_disjoint (A : Set ℝ³) (i : Fin N) {k l : ℕ} (hkl : k ≠ l) :
    Disjoint (ampSector A i k) (ampSector A i l) := by
  rw [Set.disjoint_left]
  intro x hk hl
  rw [mem_ampSector_iff] at hk hl
  exact hkl (hk ▸ hl)

/-- **The sector pieces of a state**: the part of `Φ` in the count-`k` sector. -/
def sectorPiece (B : Set ℝ³) (k : ℕ) (Φ : X N → ℝ) : X N → ℝ :=
  (sectorSet B k).indicator Φ

/-- The sector pieces sum back to the state (Fock/particle-number decomposition, pointwise). -/
theorem sum_sectorPiece (B : Set ℝ³) (Φ : X N → ℝ) (x : X N) :
    ∑ k ∈ Finset.range (N + 1), sectorPiece B k Φ x = Φ x :=
  sum_indicator_sectorSet B Φ x

/-- The sector pieces are disjointly supported. -/
theorem sectorPiece_mul_eq_zero (B : Set ℝ³) {k l : ℕ} (hkl : k ≠ l) (Φ Ψ : X N → ℝ)
    (x : X N) : sectorPiece B k Φ x * sectorPiece B l Ψ x = 0 := by
  by_cases hk : x ∈ sectorSet B k
  · have hl : x ∉ sectorSet B l := by
      intro hl
      exact hkl (mem_sectorSet_iff B k x |>.mp hk ▸ mem_sectorSet_iff B l x |>.mp hl)
    rw [sectorPiece, Set.indicator_of_mem hk, sectorPiece, Set.indicator_of_notMem hl,
      mul_zero]
  · rw [sectorPiece, Set.indicator_of_notMem hk, zero_mul]

/-- **The sector count is local on the sectors**: `boxCount` is constant `= k` there. -/
theorem boxCount_eq_of_mem_sectorSet (B : Set ℝ³) {k : ℕ} {x : X N}
    (hx : x ∈ sectorSet B k) : boxCount B x = k := by
  rw [boxCount, mem_sectorSet_iff B k x |>.mp hx]

/-! ## 2. The sector masses and the localised number

The masses are taken over the corpus analysis box `abox N L`: this is the normalisation slot of the
corpus states (`Work.UBBInputs.sqNormN N L Φ = ∫_{abox N L} Φ²`). -/

/-- The **`ENNReal` sector mass** `∫⁻_{abox} 1_{sector k}·Φ²`; the primary object, finite for
states continuous on the (compact) analysis box. -/
noncomputable def sectorMassENN (L : ℝ) (B : Set ℝ³) (Φ : X N → ℝ) (k : ℕ) : ℝ≥0∞ :=
  ∫⁻ x in abox N L, (sectorSet B k).indicator (fun x => ENNReal.ofReal ((Φ x) ^ 2)) x

/-- The **sector mass** of a state at count `k`: the `abox`-`L²`-mass of its `B`-count-`k` piece,
`m_k = ∫_{abox} 1_{n_B = k}·Φ²`. -/
noncomputable def sectorMass (L : ℝ) (B : Set ℝ³) (Φ : X N → ℝ) (k : ℕ) : ℝ :=
  (sectorMassENN L B Φ k).toReal

/-- **The localised (particle) number** `n(u) = ⟨Φ, n_{B(u)}Φ⟩`: the `abox`-integral of
`boxCount B x·Φ(x)²`.  Divided by the box `χ`-mass this is FS's `n(u)/|B(u)|`. -/
noncomputable def localisedNumber (L : ℝ) (B : Set ℝ³) (Φ : X N → ℝ) : ℝ :=
  ∫ x in abox N L, boxCount B x * (Φ x) ^ 2

/-- **The localised density** at the box `χ`-mass `V = |B| = ∫χ_B²` (FS `eq:chiBintegral`). -/
noncomputable def localisedDensity (L : ℝ) (V : ℝ) (B : Set ℝ³) (Φ : X N → ℝ) : ℝ :=
  localisedNumber L B Φ / V

/-! ## 3. The DL thresholds

The delivered per-box bound (`Submission.BoseGases.smallbox_dl_energy_bound_at_count`, FS
`thm:smallbox`) at count `P`, box `χ`-mass `V`, chemical potential `μ` and symbol
`Γ = (R/s)² + K_B³(μ a³)^{1/2}`:

    (c·((P/V)−μ)²/(1+((P/V)/μ)) − ½μ²)·8π(a v)V − C μ²(a v)Γ V − C μ(a v)
      ≤ diagWeBAt P … .

`dlThreshold` is its left-hand side at the *integer* count `k`; `dlDensityThreshold` at a real
density `t`.  The two agree by construction at `t = k/V`. -/

/-- FS's `F(t) = c(t−μ)²/(1+tμ⁻¹)` (`final_v2.tex` l. 4121) — the convex density factor. -/
noncomputable def dlDensityCoeff (c μ t : ℝ) : ℝ := c * (t - μ) ^ 2 / (1 + t * μ⁻¹)

/-- **The DL threshold at a real density `t`** (`V` = the box `χ`-mass `|B|`). -/
noncomputable def dlDensityThreshold (c C μ av V Γ t : ℝ) : ℝ :=
  (dlDensityCoeff c μ t - μ ^ 2 / 2) * (8 * π * av * V) - C * μ ^ 2 * av * Γ * V - C * μ * av

/-- **The DL threshold at the integer count `k`** (`= dlDensityThreshold` at density `k/V`). -/
noncomputable def dlThreshold (c C μ av V Γ k : ℝ) : ℝ :=
  dlDensityThreshold c C μ av V Γ (k / V)

/-- The DL threshold as a function of the **count** (as a real number, so that it can be mixed):
`dlThreshold` extended off the integers.  Its **convexity in `k`** is what converts the
count-indexed delivered bound into the density-indexed one (FS `final_v2.tex` l. 4114-4135). -/
noncomputable def dlThresholdFun (c C μ av V Γ : ℝ) (k : ℝ) : ℝ :=
  dlDensityThreshold c C μ av V Γ (k / V)

theorem dlThreshold_eq_fun (c C μ av V Γ k : ℝ) :
    dlThreshold c C μ av V Γ k = dlThresholdFun c C μ av V Γ k := rfl

/-- The FS symbol `Γ = (R/λ₁)² + K_B³(μ a³)^{1/2}` of the delivered DL bound at the sliding box.
The `(R/λ₁)²` part is carried by the regime data (see `DLRegime` in `Residual.lean`); the
`K_B³`-part is the one that survives into the bundle's `K_B³√(ρ(a v)³)` slot. -/
noncomputable def dlGamma (K_B μ av : ℝ) : ℝ := K_B ^ 3 * (μ * av ^ 3) ^ (1 / 2 : ℝ)

theorem dlThreshold_eq (c C μ av V Γ k : ℝ) :
    dlThreshold c C μ av V Γ k = dlDensityThreshold c C μ av V Γ (k / V) := rfl

end Work.FockBridge
