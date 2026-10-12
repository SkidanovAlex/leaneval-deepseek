import Mathlib.Order.CompletePartialOrder
import Mathlib.Tactic.Have
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Mathlib.MeasureTheory.Order.Group.Lattice
import Submission.Work.SmallBoxSliding.goodSet_compl_subset
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The sliding-localisation geometry layer

Basic API for the sets of `Defs` (`goodSet`, `interiorSet`, `farSet`,
`bandSet`): definitional unfoldings, measurability, the containments, and the
`λ₁ ≥ μ^{-1/3}` ("shortest side") reading of the good set which is the reason
FS restricts the sliding sum to `G`.

`bandSet ℓ d μ` is *definitionally* the corpus bad band
`ChiSmallBand.chiSmallBadBand ℓ d μ` (`bandSet_eq_chiSmallBadBand`), so the
CLOSED `chiSmallB_badband_integral_le`/`_law` apply to it verbatim (see
`Sliding.bandSet_mass_integral_le_law`).
-/

noncomputable section

open MeasureTheory Metric Filter
open scoped ContDiff Topology Real BigOperators ENNReal

namespace Work.SmallBoxSliding

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

open Submission.BoseGases
open BoseGases

/-- `bandSet` is the corpus bad band, definitionally. -/
lemma bandSet_eq_chiSmallBadBand (ℓ d μ : ℝ) :
    bandSet ℓ d μ = chiSmallBadBand ℓ d μ := rfl

lemma bandSet_subset_chiSmallBadBand (ℓ d μ : ℝ) :
    bandSet ℓ d μ ⊆ chiSmallBadBand ℓ d μ :=
  le_of_eq (bandSet_eq_chiSmallBadBand ℓ d μ)

@[simp] lemma mem_goodSet_iff {ℓ d μ : ℝ} {u : ℝ³} :
    u ∈ goodSet ℓ d μ ↔ ∀ j : Fin 3,
      |((ℓ * d) • u).ofLp j| ≤ (1 / 2) * ℓ * (1 + d) - μ ^ (-1 / 3 : ℝ) := Iff.rfl

@[simp] lemma mem_interiorSet_iff {ℓ d μ : ℝ} {u : ℝ³} :
    u ∈ interiorSet ℓ d μ ↔ ∀ j : Fin 3,
      |((ℓ * d) • u).ofLp j| ≤ (1 / 2) * ℓ * (1 + d) - 2 * μ ^ (-1 / 3 : ℝ) := Iff.rfl

@[simp] lemma mem_farSet_iff {ℓ d μ : ℝ} {u : ℝ³} :
    u ∈ farSet ℓ d μ ↔ ∃ j : Fin 3,
      (1 / 2) * ℓ * (1 + d) < |((ℓ * d) • u).ofLp j| := Iff.rfl

@[simp] lemma mem_bandSet_iff {ℓ d μ : ℝ} {u : ℝ³} :
    u ∈ bandSet ℓ d μ ↔
      (∃ j : Fin 3,
        (1 / 2) * ℓ * (1 + d) - 2 * μ ^ (-1 / 3 : ℝ) ≤ |((ℓ * d) • u).ofLp j|)
      ∧ (∀ j : Fin 3, |((ℓ * d) • u).ofLp j| ≤ (1 / 2) * ℓ * (1 + d)) := Iff.rfl

/-- The coordinate-`j` half-side of the localised box `B(u)` (i.e. half the
length of the intersection of `[−ℓ/2,ℓ/2]` with `[(ℓd)u_j − ℓd/2,
(ℓd)u_j + ℓd/2]`, by symmetry in the sign of `(ℓd)u_j`). -/
def shortSide (ℓ d : ℝ) (u : ℝ³) (j : Fin 3) : ℝ :=
  min (ℓ * d) ((1 / 2) * ℓ * (1 + d) - |((ℓ * d) • u).ofLp j|)

/-- On the good set (and in the regime `μ^{-1/3} ≤ ℓd`) every box `B(u)` has
shortest side at least `μ^{-1/3}` — the standing hypothesis of FS
`thm:smallbox`. -/
lemma goodSet_shortSide {ℓ d μ : ℝ} (hreg : μ ^ (-1 / 3 : ℝ) ≤ ℓ * d) {u : ℝ³}
    (hu : u ∈ goodSet ℓ d μ) (j : Fin 3) :
    μ ^ (-1 / 3 : ℝ) ≤ shortSide ℓ d u j := by
  rw [shortSide]
  exact le_min hreg (by linarith [hu j])

lemma measurableSet_goodSet (ℓ d μ : ℝ) : MeasurableSet (goodSet ℓ d μ) := by
  have h : goodSet ℓ d μ = ⋂ j : Fin 3,
      {u : ℝ³ | |((ℓ * d) • u).ofLp j| ≤ (1 / 2) * ℓ * (1 + d) - μ ^ (-1 / 3 : ℝ)} := by
    ext u; simp [goodSet]
  rw [h]
  refine MeasurableSet.iInter (fun j => ?_)
  exact measurableSet_le (by fun_prop) measurable_const

lemma measurableSet_interiorSet (ℓ d μ : ℝ) : MeasurableSet (interiorSet ℓ d μ) := by
  have h : interiorSet ℓ d μ = ⋂ j : Fin 3,
      {u : ℝ³ | |((ℓ * d) • u).ofLp j| ≤ (1 / 2) * ℓ * (1 + d) - 2 * μ ^ (-1 / 3 : ℝ)} := by
    ext u; simp [interiorSet]
  rw [h]
  refine MeasurableSet.iInter (fun j => ?_)
  exact measurableSet_le (by fun_prop) measurable_const

lemma measurableSet_farSet (ℓ d μ : ℝ) : MeasurableSet (farSet ℓ d μ) := by
  have h : farSet ℓ d μ = ⋃ j : Fin 3,
      {u : ℝ³ | (1 / 2) * ℓ * (1 + d) < |((ℓ * d) • u).ofLp j|} := by
    ext u; simp [farSet]
  rw [h]
  refine MeasurableSet.iUnion (fun j => ?_)
  exact measurableSet_lt measurable_const (by fun_prop)

lemma measurableSet_bandSet (ℓ d μ : ℝ) : MeasurableSet (bandSet ℓ d μ) := by
  rw [bandSet_eq_chiSmallBadBand]
  exact chiSmallBadBand_measurable

lemma interiorSet_subset_goodSet {ℓ d μ : ℝ} (hμ : 0 < μ) :
    interiorSet ℓ d μ ⊆ goodSet ℓ d μ := by
  intro u hu j
  have hδ : 0 ≤ μ ^ (-1 / 3 : ℝ) := le_of_lt (Real.rpow_pos_of_pos hμ _)
  have := hu j
  linarith

/-- The `μ ↦ 4μ` band `G ∖ I₋` is contained in the (larger, closed-library)
bad band `bandSet`. -/
lemma diff_goodSet_interiorSet_subset_bandSet {ℓ d μ : ℝ} (hμ : 0 < μ) :
    goodSet ℓ d μ \ interiorSet ℓ d μ ⊆ bandSet ℓ d μ := by
  intro u hu
  obtain ⟨huG, huI⟩ := hu
  simp only [mem_goodSet_iff] at huG
  simp only [mem_interiorSet_iff, not_forall, not_le] at huI
  obtain ⟨j, hj⟩ := huI
  have hδ : 0 < μ ^ (-1 / 3 : ℝ) := Real.rpow_pos_of_pos hμ _
  exact ⟨⟨j, by linarith⟩, fun j' => le_trans (huG j') (by linarith)⟩

/-- The far set and the band are disjoint. -/
lemma disjoint_bandSet_farSet (ℓ d μ : ℝ) : Disjoint (bandSet ℓ d μ) (farSet ℓ d μ) := by
  rw [Set.disjoint_left]
  intro u hu hv
  obtain ⟨⟨j, _⟩, hA⟩ := hu
  obtain ⟨j', hj'⟩ := hv
  exact absurd (hA j') (not_le.mpr hj')

/-- The complement of the good set splits into its band part and its far part
(`Gᶜ ⊆ bandSet ∪ farSet` with `bandSet ∩ farSet = ∅`). -/
lemma goodSet_compl_eq {ℓ d μ : ℝ} (hμ : 0 < μ) :
    (goodSet ℓ d μ)ᶜ
      = ((goodSet ℓ d μ)ᶜ ∩ bandSet ℓ d μ) ∪ ((goodSet ℓ d μ)ᶜ ∩ farSet ℓ d μ) := by
  ext u
  constructor
  · intro hu
    rcases goodSet_compl_subset (ℓ := ℓ) (d := d) hμ hu with h | h
    · exact Or.inl ⟨hu, h⟩
    · exact Or.inr ⟨hu, h⟩
  · rintro (⟨hu, _⟩ | ⟨hu, _⟩) <;> exact hu

end Work.SmallBoxSliding
