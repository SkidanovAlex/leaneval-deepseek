import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.MeasureTheory.Order.Group.Lattice
import Submission.Work.FTS.H2.T1Q.Basic

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.H2.T1Q

/-- The supremum of `|u z θ|` over the *rational* points of the open interval `(0,π/2)`, written
as a countable supremum of the values `|u z q|` (and `0` at the rationals outside the interval, so
that the index type stays `ℚ`, which is `Countable` and `Nonempty`). -/
def supRatAbs (u : ℝ → ℝ → ℝ) (z : ℝ) : ℝ :=
  ⨆ (q : ℚ), (if ((q : ℚ) : ℝ) ∈ Set.Ioo 0 (π / 2) then |u z ((q : ℚ) : ℝ)| else 0)

/-- A countable supremum of almost-everywhere strongly measurable functions is almost-everywhere
strongly measurable; here each summand `if q ∈ (0,π/2) then |u z q| else 0` is either the
absolutely continuous image of the hypothesis `z ↦ u z q` or a constant. -/
lemma supRatAbs_aemeasurable {u : ℝ → ℝ → ℝ}
    (hmeas : ∀ q : ℚ, ((q : ℝ) ∈ Set.Ioo 0 (π / 2)) →
      AEMeasurable (fun z => u z (q : ℝ)) (MeasureTheory.volume.restrict Work.Spaces.Iz)) :
    AEMeasurable (supRatAbs u) (MeasureTheory.volume.restrict Work.Spaces.Iz) := by
  unfold supRatAbs
  refine AEMeasurable.iSup (fun q : ℚ => ?_)
  by_cases hq : ((q : ℚ) : ℝ) ∈ Set.Ioo 0 (π / 2)
  · have h1 : (fun z : ℝ => (if ((q : ℚ) : ℝ) ∈ Set.Ioo 0 (π / 2)
        then |u z ((q : ℚ) : ℝ)| else 0)) = fun z => |u z ((q : ℚ) : ℝ)| := by
      funext z; rw [ite_eq_left hq]
    rw [h1]
    exact (hmeas q hq).abs
  · have h1 : (fun z : ℝ => (if ((q : ℚ) : ℝ) ∈ Set.Ioo 0 (π / 2)
        then |u z ((q : ℚ) : ℝ)| else 0)) = fun _ => (0 : ℝ) := by
      funext z; rw [ite_eq_right hq]
    rw [h1]
    exact aemeasurable_const

/-- The rationals of the *open* interval `(0,π/2)` come arbitrarily close to any point of that
interval: a rational can be found in `(θ/2, θ) ∩ (θ-δ, θ+δ)`. -/
lemma exists_rat_mem_Ioo_near {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (π / 2)) {δ : ℝ} (hδ : 0 < δ) :
    ∃ q : ℚ, ((q : ℚ) : ℝ) ∈ Set.Ioo 0 (π / 2) ∧ |((q : ℚ) : ℝ) - θ| < δ := by
  have hθpos : 0 < θ := hθ.1
  have hθlt : θ < π / 2 := hθ.2
  have hη : 0 < min δ (θ / 2) := lt_min hδ (by linarith)
  have hlt : θ - min δ (θ / 2) < θ := by linarith
  obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn hlt
  refine ⟨q, ⟨?_, ?_⟩, ?_⟩
  · have h : θ / 2 ≤ θ - min δ (θ / 2) := by
      have := min_le_right δ (θ / 2); linarith
    linarith
  · linarith
  · rw [abs_lt]
    exact ⟨by linarith [min_le_left δ (θ / 2), hδ],
      by linarith [min_le_left δ (θ / 2)]⟩

/-- On a slice where `θ ↦ u z θ` is continuous (and where the range of `|u z ·|` is bounded
above), the supremum over the open interval agrees with the supremum over its rational points. -/
lemma supAbsThO_eq_supRatAbs {u : ℝ → ℝ → ℝ} {z : ℝ}
    (hcont : ContinuousOn (fun θ => u z θ) (Set.Ioo 0 (π / 2)))
    (hbdd : BddAbove {y : ℝ | ∃ θ ∈ Set.Ioo 0 (π / 2), y = |u z θ|}) :
    Work.FTS.H2.supAbsThO u z = supRatAbs u z := by
  have hmem4 : π / 4 ∈ Set.Ioo 0 (π / 2) :=
    ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩
  have hmem45 : |u z (π / 4)| ∈ {y : ℝ | ∃ θ ∈ Set.Ioo 0 (π / 2), y = |u z θ|} :=
    ⟨π / 4, hmem4, rfl⟩
  have hSne : ({y : ℝ | ∃ θ ∈ Set.Ioo 0 (π / 2), y = |u z θ|} : Set ℝ).Nonempty :=
    ⟨_, hmem45⟩
  have hCnn : 0 ≤ Work.FTS.H2.supAbsThO u z := by
    have h : |u z (π / 4)| ≤ Work.FTS.H2.supAbsThO u z := le_csSup hbdd hmem45
    exact le_trans (abs_nonneg _) h
  have hBddG : BddAbove (Set.range (fun q : ℚ =>
      (if ((q : ℚ) : ℝ) ∈ Set.Ioo 0 (π / 2) then |u z ((q : ℚ) : ℝ)| else 0))) := by
    obtain ⟨C, hC⟩ := hbdd
    refine ⟨max C 0, ?_⟩
    rintro y ⟨q, rfl⟩
    show (if ((q : ℚ) : ℝ) ∈ Set.Ioo 0 (π / 2) then |u z ((q : ℚ) : ℝ)| else 0) ≤ max C 0
    by_cases hq : ((q : ℚ) : ℝ) ∈ Set.Ioo 0 (π / 2)
    · rw [ite_eq_left hq]; exact le_trans (hC ⟨_, hq, rfl⟩) (le_max_left _ _)
    · rw [ite_eq_right hq]; exact le_max_right _ _
  refine le_antisymm ?_ ?_
  · unfold Work.FTS.H2.supAbsThO
    refine csSup_le hSne (fun y hy => ?_)
    obtain ⟨θ, hθ, rfl⟩ := hy
    by_contra hcon
    rw [not_le] at hcon
    have hε : 0 < (|u z θ| - supRatAbs u z) / 2 := by linarith
    have hcont' : ContinuousOn (fun θ => |u z θ|) (Set.Ioo 0 (π / 2)) := hcont.abs
    obtain ⟨δ, hδpos, hδ⟩ :=
      (Metric.continuousOn_iff.mp hcont') θ hθ ((|u z θ| - supRatAbs u z) / 2) hε
    obtain ⟨q, hqIoo, hqdist⟩ := exists_rat_mem_Ioo_near hθ hδpos
    have h1 : |u z ((q : ℚ) : ℝ)| ≤ supRatAbs u z := by
      have hle := le_ciSup hBddG q
      rwa [ite_eq_left hqIoo] at hle
    have h2 : dist (|u z ((q : ℚ) : ℝ)|) (|u z θ|) < (|u z θ| - supRatAbs u z) / 2 :=
      hδ ((q : ℚ) : ℝ) hqIoo (by rw [Real.dist_eq]; exact hqdist)
    rw [Real.dist_eq, abs_sub_comm] at h2
    have h3 : |u z θ| ≤ abs (|u z θ| - |u z ((q : ℚ) : ℝ)|) + |u z ((q : ℚ) : ℝ)| := by
      have := le_abs_self (|u z θ| - |u z ((q : ℚ) : ℝ)|); linarith
    linarith
  · unfold supRatAbs
    refine ciSup_le (fun q => ?_)
    show (if ((q : ℚ) : ℝ) ∈ Set.Ioo 0 (π / 2) then |u z ((q : ℚ) : ℝ)| else 0)
      ≤ Work.FTS.H2.supAbsThO u z
    by_cases hq : ((q : ℚ) : ℝ) ∈ Set.Ioo 0 (π / 2)
    · rw [ite_eq_left hq]
      exact le_csSup hbdd ⟨_, hq, rfl⟩
    · rw [ite_eq_right hq]
      exact hCnn

/-- **Almost-everywhere strong measurability of the interior angular supremum.**
`Work.FTS.H2.supAbsThO u z = sSup {|u z θ| : θ ∈ (0,π/2)}` is the supremum of `|u z ·|` over
the *open* angular interval at the fixed radius `z`.  If

* for every `z ∈ Iz = [0,∞)` the slice `θ ↦ u z θ` is continuous on `(0,π/2)`,
* for every rational `q` of `(0,π/2)` the `z`-slice `z ↦ u z q` is `AEMeasurable` for
  `volume.restrict Iz`, and
* for almost every `z ∈ Iz` the set `{|u z θ| : θ ∈ (0,π/2)}` is bounded above,

then `z ↦ supAbsThO u z` is `AEMeasurable` for `volume.restrict Iz`.

The boundedness hypothesis is needed only to replace the supremum over the open interval by the
supremum over the countable dense set `(0,π/2) ∩ ℚ` (the `ℚ`-supremum is automatically
`AEMeasurable` as a countable supremum of measurable functions; the reverse inequality uses
continuity in `θ` plus density of `ℚ`).  This is the measurability ingredient of
`Work.H2.T1Q.SupThetaIntQ`, the interior-class replacement of the `supAbsTh`-measurability
argument inside `Work.FTS.H2.SupThetaInt`. -/
theorem SupAbsThOAesm : ∀ (u : ℝ → ℝ → ℝ),
    (∀ z ∈ Work.Spaces.Iz, ContinuousOn (fun θ => u z θ) (Set.Ioo 0 (Real.pi / 2))) →
    (∀ q : ℚ, ((q : ℝ) ∈ Set.Ioo 0 (Real.pi / 2)) →
      AEMeasurable (fun z => u z (q : ℝ))
        (MeasureTheory.volume.restrict Work.Spaces.Iz)) →
    (∀ᵐ z ∂(MeasureTheory.volume.restrict Work.Spaces.Iz),
      BddAbove {y : ℝ | ∃ θ ∈ Set.Ioo 0 (Real.pi / 2), y = |u z θ|}) →
    AEMeasurable (fun z => Work.FTS.H2.supAbsThO u z)
      (MeasureTheory.volume.restrict Work.Spaces.Iz) := by
  intro u hcont hmeas hbdd
  refine (supRatAbs_aemeasurable hmeas).congr ?_
  filter_upwards [MeasureTheory.ae_restrict_mem
      (show MeasurableSet Work.Spaces.Iz from measurableSet_Ici), hbdd] with z hz hbddz
  exact (supAbsThO_eq_supRatAbs (hcont z hz) hbddz).symm

end Work.H2.T1Q
