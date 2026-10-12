import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import ChallengeDeps
import Submission.SectorProj
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Layer 5 — geometry of the *centred* analysis box Λ(ℓ) = [−ℓ/2, ℓ/2]³

The Fournais--Solovej box analysis (the `hpres` hypothesis, cf. NOTES.md
"geometry decision (A)") lives on the centred cube

    Λ(ℓ) := {y : ℝ³ | ∀ m, y m ∈ Icc (−ℓ/2) (ℓ/2)}

which contains the support of the scaled bump `χ_ℓ(x) := χ(x/ℓ)`
(`supp χ_ℓ ⊆ ball 0 (ℓ/2) ⊆ Λ(ℓ)`), unlike the corpus cube `[0,ℓ]³`.
This module provides the measure-theoretic substrate:

  * `acube ℓ` — the centred cube as a measurable subset of ℝ³, of volume `ℓ³`;
  * `acubeF ℓ` — the coordinate form on `Fin 3 → ℝ` (the image of `acube ℓ`
    under the measure-preserving equivalence `cgEuc3` from `SectorProj`);
  * `abox N ℓ` — the N-particle box `(Λ(ℓ))ᴺ ⊆ X N`, measurable, with the
    product-volume identity `restrict (abox N ℓ) = πᵢ (volume ↾ acube ℓ)`;
  * coordinate/norm facts (`|x m| ≤ ‖x‖` and the corollary
    `ball 0 (ℓ/2) ⊆ acube ℓ` — the geometric reason the χ-kernels are
    supported inside the box), and the monotonicity `acube ℓ ⊆ acube L`
    for `0 ≤ ℓ ≤ L`.

All statements mirror existing corpus lemmas (SectorProj `cgCubeF`/
`cgEuc3`/`cgVolumeCubeF`, Potential `restrict_box_eq_pi`,
`measurePreserving_coordSplitFin`) with the interval `Icc (−ℓ/2) (ℓ/2)`
in place of `Icc 0 L`.

## Route notes (for the child)

* Volume computations go through the coordinate cube: prove
  `acubeF_eq_pi`, `acubeF_measurable`, `acubeF_volume` by copying
  `cgRestrictCubeF_eq_pi`/`cgVolumeCubeF` from `SectorProj.lean` with
  `Real.volume_Icc` giving `ofReal (ℓ/2 − (−ℓ/2)) = ofReal ℓ` for each
  coordinate; then transport with the measure-preserving `cgEuc3`
  (`SectorProj.cgEuc3_mp`, `SectorProj.cgCube_eq_image`-style arguments).
* `abox N ℓ` facts mirror `box N L` facts: `box_eq_pi_cube`,
  `restrict_box_eq_pi`, and BoxMeas's measurability via the coordinate
  projections `(x i).ofLp m`.
* `|x m| ≤ ‖x‖` on `EuclideanSpace ℝ (Fin 3)` is already in the corpus:
  `SubaddVol.abs_coord_le_norm`.  (mem_acube_of_norm_le and ball_subset_acube
  follow directly from it.)
-/

noncomputable section

open MeasureTheory
open scoped Topology ENNReal Real

namespace Submission

open _root_.BoseGases
set_option autoImplicit false

namespace BoseGases

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

/-- The centred cube of side `ℓ`: `Λ(ℓ) := {y | ∀ m, y m ∈ Icc (−ℓ/2) (ℓ/2)}`. -/
def acube (ℓ : ℝ) : Set ℝ³ := {y : ℝ³ | ∀ m : Fin 3, y m ∈ Set.Icc (-ℓ / 2) (ℓ / 2)}

/-- The coordinate form of the centred cube on `Fin 3 → ℝ`. -/
def acubeF (ℓ : ℝ) : Set (Fin 3 → ℝ) := {x : Fin 3 → ℝ | ∀ m : Fin 3, x m ∈ Set.Icc (-ℓ / 2) (ℓ / 2)}

/-- Membership in the centred cube is coordinatewise. -/
@[simp] lemma mem_acube_iff (ℓ : ℝ) (y : ℝ³) :
    y ∈ acube ℓ ↔ ∀ m : Fin 3, y m ∈ Set.Icc (-ℓ / 2) (ℓ / 2) := by
  rfl

/-- `acubeF ℓ` is a product of intervals. -/
lemma acubeF_eq_pi (ℓ : ℝ) :
    acubeF ℓ = Set.univ.pi (fun _ : Fin 3 => Set.Icc (-ℓ / 2) (ℓ / 2)) := by
  ext x
  rw [Set.mem_pi]
  simp [acubeF, Pi.le_def]

/-- `acubeF ℓ` is measurable. -/
lemma acubeF_measurable (ℓ : ℝ) : MeasurableSet (acubeF ℓ) := by
  rw [acubeF_eq_pi]
  exact MeasurableSet.pi (s := (Set.univ : Set (Fin 3)))
    (t := fun _ : Fin 3 => Set.Icc (-ℓ / 2) (ℓ / 2)) Set.countable_univ (by
      intro i hi
      exact measurableSet_Icc)


/-- The restricted coordinate-cube measure equals the product of the restricted
interval measures. -/
lemma acubeF_restrict_eq_pi (ℓ : ℝ) :
    (volume : Measure (Fin 3 → ℝ)).restrict (acubeF ℓ) =
      Measure.pi (fun _ : Fin 3 => (volume : Measure ℝ).restrict (Set.Icc (-ℓ / 2) (ℓ / 2))) := by
  rw [acubeF_eq_pi]
  change (Measure.pi (fun _ : Fin 3 => (volume : Measure ℝ))).restrict
      (Set.univ.pi (fun _ : Fin 3 => Set.Icc (-ℓ / 2) (ℓ / 2))) =
      Measure.pi (fun _ : Fin 3 => (volume : Measure ℝ).restrict (Set.Icc (-ℓ / 2) (ℓ / 2)))
  rw [Measure.restrict_pi_pi]

/-- Volume of the coordinate cube: `vol (acubeF ℓ) = ℓ³` (for `0 ≤ ℓ`). -/
lemma acubeF_volume (ℓ : ℝ) (hℓ : 0 ≤ ℓ) :
    (volume : Measure (Fin 3 → ℝ)) (acubeF ℓ) = ENNReal.ofReal (ℓ ^ 3) := by
  rw [← Measure.restrict_apply_univ, acubeF_restrict_eq_pi, Measure.pi_univ]
  rw [Measure.restrict_apply_univ]
  rw [Real.volume_Icc]
  rw [Finset.prod_const]
  have hcard : (Finset.univ : Finset (Fin 3)).card = 3 := by simp
  rw [hcard]
  have harg : ℓ / 2 - -ℓ / 2 = ℓ := by ring
  rw [harg]
  rw [← ENNReal.ofReal_pow hℓ]

/-- The centred cube is the image of the coordinate cube under `cgEuc3`. -/
lemma acube_eq_image (ℓ : ℝ) : acube ℓ = cgEuc3 '' acubeF ℓ := by
  ext y
  constructor
  · intro hy
    refine ⟨cgEuc3.symm y, ?_, ?_⟩
    · intro k
      have hyk : y k ∈ Set.Icc (-ℓ / 2) (ℓ / 2) := hy k
      simpa [cgEuc3, acubeF] using hyk
    · simp [cgEuc3]
  · rintro ⟨x, hx, rfl⟩
    intro k
    simpa [cgEuc3, acubeF] using hx k

/-- The centred cube is measurable. -/
lemma acube_measurable (ℓ : ℝ) : MeasurableSet (acube ℓ) := by
  rw [show acube ℓ = {y : ℝ³ | ∀ m : Fin 3, y m ∈ Set.Icc (-ℓ / 2) (ℓ / 2)} by rfl]
  rw [show {y : ℝ³ | ∀ m : Fin 3, y m ∈ Set.Icc (-ℓ / 2) (ℓ / 2)} =
      (⋂ m : Fin 3, (fun y : ℝ³ => y m) ⁻¹' (Set.Icc (-ℓ / 2) (ℓ / 2))) by
        ext y
        simp]
  exact MeasurableSet.iInter (fun m =>
    ((by fun_prop : Continuous fun y : ℝ³ => y m).measurable) measurableSet_Icc)

/-- Volume of the centred cube: `vol (acube ℓ) = ℓ³` (for `0 ≤ ℓ`). -/
lemma acube_volume (ℓ : ℝ) (hℓ : 0 ≤ ℓ) :
    (volume : Measure ℝ³) (acube ℓ) = ENNReal.ofReal (ℓ ^ 3) := by
  have hcube : MeasurableSet (acube ℓ) := acube_measurable ℓ
  rw [← cgEuc3_mp.map_eq]
  rw [Measure.map_apply (by measurability : Measurable (⇑cgEuc3)) hcube]
  rw [acube_eq_image, Set.preimage_image_eq _ (MeasurableEquiv.injective cgEuc3)]
  exact acubeF_volume ℓ hℓ

/-- The centred cube has finite measure. -/
lemma acube_lt_top (ℓ : ℝ) (hℓ : 0 ≤ ℓ) : (volume : Measure ℝ³) (acube ℓ) < ∞ := by
  rw [acube_volume ℓ hℓ]
  exact ENNReal.ofReal_lt_top

/-- The restricted cube measure equals the product of the restricted interval measures. -/
lemma acube_restrict_eq_map (ℓ : ℝ) :
    (volume : Measure ℝ³).restrict (acube ℓ) =
      Measure.map (⇑cgEuc3) ((volume : Measure (Fin 3 → ℝ)).restrict (acubeF ℓ)) := by
  have hmap := cgEuc3_mp.map_eq
  rw [← hmap, acube_eq_image]
  have hs : MeasurableSet (cgEuc3 '' acubeF ℓ) := (cgEuc3.measurableSet_image).2 (acubeF_measurable ℓ)
  rw [Measure.restrict_map (by measurability : Measurable (⇑cgEuc3)) hs]
  rw [Set.preimage_image_eq _ (MeasurableEquiv.injective cgEuc3)]

/-- The N-particle box over the centred cube: `(Λ(ℓ))ᴺ`. -/
def abox (N : ℕ) (ℓ : ℝ) : Set (X N) := {x : X N | ∀ i : Fin N, x i ∈ acube ℓ}

/-- Membership in the N-particle centred box. -/
@[simp] lemma mem_abox_iff (N : ℕ) (ℓ : ℝ) (x : X N) :
    x ∈ abox N ℓ ↔ ∀ i : Fin N, x i ∈ acube ℓ := by
  rfl

/-- Coordinate form of membership in the N-particle centred box. -/
lemma mem_abox_iff_coord (N : ℕ) (ℓ : ℝ) (x : X N) :
    x ∈ abox N ℓ ↔ ∀ i : Fin N, ∀ m : Fin 3, (x i).ofLp m ∈ Set.Icc (-ℓ / 2) (ℓ / 2) := by
  simp [abox, acube]

/-- The N-particle centred box is a product of one-particle centred cubes. -/
lemma abox_eq_pi_acube (N : ℕ) (ℓ : ℝ) :
    abox N ℓ = Set.univ.pi (fun _ : Fin N => acube ℓ) := by
  ext x
  simp [abox]

/-- The N-particle centred box is measurable. -/
lemma abox_measurable (N : ℕ) (ℓ : ℝ) : MeasurableSet (abox N ℓ) := by
  rw [abox_eq_pi_acube]
  exact MeasurableSet.pi (s := (Set.univ : Set (Fin N)))
    (t := fun _ : Fin N => acube ℓ) Set.countable_univ (by
      intro i hi
      exact acube_measurable ℓ)

/-- The restricted N-particle volume is the product of the per-particle centred
cube volumes. -/
lemma restrict_abox_eq_pi (N : ℕ) (ℓ : ℝ) :
    (volume : Measure (X N)).restrict (abox N ℓ) =
      Measure.pi (fun _ : Fin N => (volume : Measure ℝ³).restrict (acube ℓ)) := by
  rw [abox_eq_pi_acube]
  rw [show (volume : Measure (X N)) = Measure.pi (fun _ : Fin N => (volume : Measure ℝ³)) by rfl]
  rw [Measure.restrict_pi_pi]

/-- Volume of the N-particle centred box: `(ℓ³)ᴺ`. -/
lemma abox_volume (N : ℕ) (ℓ : ℝ) (hℓ : 0 ≤ ℓ) :
    (volume : Measure (X N)) (abox N ℓ) = ENNReal.ofReal ((ℓ ^ 3) ^ N) := by
  calc
    (volume : Measure (X N)) (abox N ℓ)
        = (Measure.pi (fun _ : Fin N => (volume : Measure ℝ³).restrict (acube ℓ))) Set.univ := by
          rw [← Measure.restrict_apply_univ, restrict_abox_eq_pi]
    _ = (∏ i : Fin N, (volume : Measure ℝ³).restrict (acube ℓ) Set.univ) := by
          rw [Measure.pi_univ]
    _ = (∏ i : Fin N, (volume : Measure ℝ³) (acube ℓ)) := by
          rw [Measure.restrict_apply_univ]
    _ = (∏ i : Fin N, ENNReal.ofReal (ℓ ^ 3)) := by
          refine Finset.prod_congr rfl ?_
          intro i hi
          rw [acube_volume ℓ hℓ]
    _ = ENNReal.ofReal ((ℓ ^ 3) ^ N) := by
          rw [Finset.prod_const]
          rw [Finset.card_fin]
          exact (ENNReal.ofReal_pow (p := ℓ ^ 3) (pow_nonneg hℓ 3) N).symm

/-- The N-particle centred box has finite measure. -/
lemma abox_lt_top (N : ℕ) (ℓ : ℝ) (hℓ : 0 ≤ ℓ) :
    (volume : Measure (X N)) (abox N ℓ) < ∞ := by
  rw [abox_volume N ℓ hℓ]
  exact ENNReal.ofReal_lt_top

/-- The measure-preserving split isolating the `i`-th of `n+1` coordinates
(centred-box version of `Potential.measurePreserving_coordSplitFin`). -/
lemma measurePreserving_coordSplitFinAcube (n : ℕ) (ℓ : ℝ) (i : Fin (n + 1)) :
    let μ' : Measure ℝ³ := (volume : Measure ℝ³).restrict (acube ℓ)
    MeasurePreserving (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ³) i)
      (Measure.pi (fun _ : Fin (n + 1) => μ')) (μ'.prod (Measure.pi (fun _ : Fin n => μ'))) := by
  intro μ'
  simpa using (measurePreserving_piFinSuccAbove (μ := fun _ : Fin (n + 1) => μ') i)

/-- The full `acube`-measure of the fibre is `ℓ³` (restated). -/
lemma restrict_acube_univ (ℓ : ℝ) (hℓ : 0 ≤ ℓ) :
    ((volume : Measure ℝ³).restrict (acube ℓ)) Set.univ = ENNReal.ofReal (ℓ ^ 3) := by
  rw [Measure.restrict_apply_univ]
  exact acube_volume ℓ hℓ

/-! ## Norm/coordinate facts and the ball inside the centred cube -/


/-- A point of norm at most `ℓ/2` lies in the centred cube of side `ℓ`. -/
lemma mem_acube_of_norm_le {x : ℝ³} {ℓ : ℝ} (hℓ : 0 ≤ ℓ) (hx : ‖x‖ ≤ ℓ / 2) :
    x ∈ acube ℓ := by
  have hb0 : 0 ≤ ℓ / 2 := by positivity
  rw [mem_acube_iff]
  intro m
  have hb : |x m| ≤ ℓ / 2 := le_trans (abs_coord_le_norm x m) hx
  rw [Set.mem_Icc]
  exact ⟨by simpa [neg_div] using (abs_le.mp hb).1, (abs_le.mp hb).2⟩

/-- The closed ball of radius `ℓ/2` around the origin is contained in `acube ℓ`. -/
lemma ball_subset_acube {ℓ : ℝ} (hℓ : 0 ≤ ℓ) :
    Metric.ball (0 : ℝ³) (ℓ / 2) ⊆ acube ℓ := by
  intro y hy
  apply mem_acube_of_norm_le hℓ
  have hy' : dist y 0 < ℓ / 2 := hy
  rw [dist_eq_norm] at hy'
  simpa [sub_zero] using le_of_lt hy'

/-- The centred cubes are monotone in the side length. -/
lemma acube_mono {ℓ L : ℝ} (hℓ : 0 ≤ ℓ) (h : ℓ ≤ L) : acube ℓ ⊆ acube L := by
  have hℓ0 : 0 ≤ ℓ := hℓ
  intro y hy
  rw [mem_acube_iff] at hy ⊢
  intro m
  have hyl : -ℓ / 2 ≤ y m := (hy m).1
  have hyu : y m ≤ ℓ / 2 := (hy m).2
  constructor
  · calc
      -L / 2 ≤ -ℓ / 2 := by linarith
      _ ≤ y m := hyl
  · calc
      y m ≤ ℓ / 2 := hyu
      _ ≤ L / 2 := by linarith


end BoseGases

end Submission
