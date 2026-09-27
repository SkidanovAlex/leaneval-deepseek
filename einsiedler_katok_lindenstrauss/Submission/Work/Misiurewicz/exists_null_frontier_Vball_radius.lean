import Mathlib
import Submission.Work.EKLComp.Misiurewicz.Defs
import Submission.Work.Misiurewicz.vMove_lt_iff
import Submission.Work.EKLNonExc.VFacts

/-!
# Radii for which the translate `V δ • z` has measure-null frontier

`Work.EKLComp.Vball δ z = V δ • z` is the image of the "max-entry displacement" neighbourhood
`V δ` of the identity of `SL₃(ℝ)` under the orbit map `u ↦ u • z` on `X₃ = SL₃(ℝ)/SL₃(ℤ)`.
The main result of this file is that for **any** finite Borel measure `ν` on `X₃`, any `z ∈ X₃`
and any `r₀ > 0` there is a radius `r ∈ (0, r₀]` whose ball has `ν`-null frontier.

The argument is the classical one: the balls increase with the radius and _never jump_,

  `closure (Vball r z) ⊆ Vball s z`   for all `r < s`,

because `Vbar r` (the closed entrywise box `|gᵢⱼ - δᵢⱼ| ≤ r`) is **compact**, its image under the
continuous orbit map is closed, and it already contains `Vball r z`; then `Vbar r ⊆ V s` for
`r < s`.  Consequently every frontier sits in a "shell"
`frontier (Vball r z) ⊆ Vball s z \ Vball r z`, so

  `ν (frontier (Vball r z)) + ν (Vball r z) ≤ ν (Vball s z)`   for `s > r`.

If the monotone function `r ↦ ν (Vball r z)` (as a real number) were discontinuous at every point
of `(0, r₀]`, the countable set of its discontinuities would contain the uncountable interval
`(0, r₀]`; so there is a continuity point `r`, and the estimate above with `s ↓ r` forces the
frontier to be null.
-/

set_option linter.style.haveILetI false

namespace Work.Misiurewicz

open MeasureTheory Filter Topology
open Work.EKLContract Work.EKLComp

noncomputable section

/-! ## Elementary facts about the translates -/

/-- The orbit map `u ↦ u • z : SL₃(ℝ) → X₃` is continuous. -/
theorem continuous_smul_X3 (z : X3) : Continuous (fun u : SL3 => u • z) :=
  continuous_id.smul continuous_const

/-- For `r > 0` the translate `Vball r z = V r • z` is open in `X₃`. -/
theorem isOpen_Vball (z : X3) {r : ℝ} (hr : 0 < r) : IsOpen (Vball r z) := by
  have h := Work.EKLNonExc.orbitImage_isOpen z r hr
  simpa [Vball, Set.image, eq_comm, and_comm] using h

/-- The translates grow with the radius. -/
theorem Vball_mono (z : X3) {r s : ℝ} (h : r ≤ s) : Vball r z ⊆ Vball s z :=
  Set.image_mono (V_mono h)

/-- The closure of `Vball r z` is contained in every strictly larger translate: the family of
balls has no jumps. -/
theorem closure_Vball_subset (z : X3) {r s : ℝ} (hrs : r < s) :
    closure (Vball r z) ⊆ Vball s z := by
  haveI : IsClosed (Γ3 : Set SL3) := Work.EKLContract.Lemmas.isClosed_Γ3
  haveI : T2Space X3 := inferInstance
  have hcompact : IsCompact (Vbar r) := Work.EKLNonExc.clBox_isCompact r
  have hclosed : IsClosed ((fun u : SL3 => u • z) '' Vbar r) :=
    (hcompact.image (continuous_smul_X3 z)).isClosed
  have h1 : closure (Vball r z) ⊆ ((fun u : SL3 => u • z) '' Vbar r) := by
    rw [← hclosed.closure_eq]
    exact closure_mono (Vball_subset_Vbar_ball r z)
  intro y hy
  obtain ⟨u, hu, rfl⟩ := h1 hy
  exact ⟨u, fun i j => lt_of_le_of_lt (hu i j) hrs, rfl⟩

/-- For `0 < r < s` the frontier of `Vball r z` lies in the shell `Vball s z \ Vball r z`. -/
theorem frontier_Vball_subset (z : X3) {r s : ℝ} (hr : 0 < r) (hrs : r < s) :
    frontier (Vball r z) ⊆ Vball s z \ Vball r z := by
  have hAopen := isOpen_Vball z hr
  intro y hy
  refine ⟨closure_Vball_subset z hrs (frontier_subset_closure hy), ?_⟩
  intro hyA
  have hyint : y ∈ interior (Vball r z) := by rwa [hAopen.interior_eq]
  exact (Set.disjoint_left.mp (disjoint_interior_frontier (s := Vball r z)) hyint) hy

/-! ## The main result -/

theorem exists_null_frontier_Vball_radius (ν : MeasureTheory.Measure Work.EKLContract.X3) [MeasureTheory.IsFiniteMeasure ν] (z : Work.EKLContract.X3) {r₀ : ℝ} (hr₀ : 0 < r₀) : ∃ r : ℝ, 0 < r ∧ r ≤ r₀ ∧ ν (frontier (Work.EKLComp.Vball r z)) = 0 := by
  -- `F r = ν (Vball r z)` as a real number is monotone in `r`
  have hFmono : Monotone (fun r : ℝ => (ν (Vball r z)).toReal) := by
    intro a b hab
    exact ENNReal.toReal_mono (measure_ne_top ν _) (measure_mono (Vball_mono z hab))
  -- hence it has at most countably many discontinuities
  have hcount : Set.Countable {r : ℝ | ¬ ContinuousAt (fun t : ℝ => (ν (Vball t z)).toReal) r} :=
    hFmono.countable_not_continuousAt
  have hdense : Dense ({r : ℝ | ¬ ContinuousAt (fun t : ℝ => (ν (Vball t z)).toReal) r})ᶜ :=
    Set.Countable.dense_compl ℝ hcount
  -- pick a point of continuity inside `(0, r₀]`
  obtain ⟨r, hrnot, hrIoo⟩ :=
    hdense.exists_mem_open (U := Set.Ioo (0 : ℝ) r₀) isOpen_Ioo
      ⟨r₀ / 2, by constructor <;> linarith⟩
  have hrpos : 0 < r := hrIoo.1
  have hrlt : r < r₀ := hrIoo.2
  have hcont : ContinuousAt (fun t : ℝ => (ν (Vball t z)).toReal) r := by
    by_contra h
    exact hrnot h
  have hfin_fr : ν (frontier (Vball r z)) ≠ ⊤ := measure_ne_top ν _
  have hfin_Ar : ν (Vball r z) ≠ ⊤ := measure_ne_top ν _
  -- the frontier is disjoint from the (open) ball itself
  have hdisj : Disjoint (frontier (Vball r z)) (Vball r z) := by
    have h : Disjoint (interior (Vball r z)) (frontier (Vball r z)) := disjoint_interior_frontier
    rw [(isOpen_Vball z hrpos).interior_eq] at h
    exact h.symm
  have hmeasA : MeasurableSet (Vball r z) := (isOpen_Vball z hrpos).measurableSet
  -- the measure of a ball plus the measure of its frontier is at most the measure of any
  -- strictly larger ball
  have hkey : ∀ s : ℝ, r < s → ν (frontier (Vball r z)) + ν (Vball r z) ≤ ν (Vball s z) := by
    intro s hrs
    calc ν (frontier (Vball r z)) + ν (Vball r z)
        = ν (frontier (Vball r z) ∪ Vball r z) := (measure_union hdisj hmeasA).symm
      _ ≤ ν (Vball s z) := by
          apply measure_mono
          intro y hy
          rcases hy with hy | hy
          · exact (frontier_Vball_subset z hrpos hrs hy).1
          · exact Vball_mono z (le_of_lt hrs) hy
  have hbound : ∀ s : ℝ, r < s →
      (ν (frontier (Vball r z))).toReal ≤ (ν (Vball s z)).toReal - (ν (Vball r z)).toReal := by
    intro s hrs
    have h := hkey s hrs
    have h1 : (ν (frontier (Vball r z)) + ν (Vball r z)).toReal ≤ (ν (Vball s z)).toReal :=
      ENNReal.toReal_mono (measure_ne_top ν _) h
    rw [ENNReal.toReal_add hfin_fr hfin_Ar] at h1
    linarith
  -- continuity at `r` squeezes the frontier measure to `0`
  have hsmall : ∀ ε > 0, (ν (frontier (Vball r z))).toReal < ε := by
    intro ε hε
    obtain ⟨δ, hδpos, hδ⟩ := Metric.continuousAt_iff.mp hcont ε hε
    have hdist : dist (r + δ / 2) r < δ := by
      rw [Real.dist_eq]
      have h2 : r + δ / 2 - r = δ / 2 := by ring
      rw [h2, abs_of_pos (by linarith : (0 : ℝ) < δ / 2)]
      linarith
    have hh := hδ hdist
    rw [Real.dist_eq] at hh
    have hmono' : (ν (Vball r z)).toReal ≤ (ν (Vball (r + δ / 2) z)).toReal :=
      ENNReal.toReal_mono (measure_ne_top ν _) (measure_mono (Vball_mono z (by linarith)))
    have hsub : (ν (Vball (r + δ / 2) z)).toReal - (ν (Vball r z)).toReal < ε := by
      rwa [abs_of_nonneg (sub_nonneg.mpr hmono')] at hh
    have hb := hbound (r + δ / 2) (by linarith)
    linarith
  have hz : (ν (frontier (Vball r z))).toReal = 0 := by
    refine le_antisymm ?_ ENNReal.toReal_nonneg
    refine le_of_forall_pos_lt_add (fun ε hε => ?_)
    simpa using hsmall ε hε
  refine ⟨r, hrpos, le_of_lt hrlt, ?_⟩
  have hof := ENNReal.ofReal_toReal hfin_fr
  rw [hz, ENNReal.ofReal_zero] at hof
  exact hof.symm

end

end Work.Misiurewicz
