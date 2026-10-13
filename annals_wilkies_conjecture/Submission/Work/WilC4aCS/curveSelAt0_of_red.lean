import Mathlib
import Submission.Work.WilC4aCS.Defs

set_option autoImplicit false
noncomputable section
open Classical Topology Filter

namespace Work.WilC4aCS

open WilkiesDesign.CG.C4a

/-- The reduced form of curve selection (all inequality functions vanish at the origin) implies
the general form: the inequality functions that are positive at the origin are harmless, since
their positivity persists on a whole neighbourhood of the origin. -/
theorem curveSelAt0_of_red {m : ℕ} (h : Work.WilC4aCS.CurveSelAt0Red m) :
    Work.WilC4aCS.CurveSelAt0 m := by
  classical
  intro l F g hF hg hcl
  -- (1) Every `g j` is nonnegative at the origin: otherwise the origin is not in the closure.
  have hnonneg : ∀ j, 0 ≤ g j 0 := by
    intro j
    by_contra hneg
    rw [not_le] at hneg
    have hUmem : (g j) ⁻¹' Set.Iio (0 : ℝ) ∈ 𝓝 (0 : Fin m → ℝ) :=
      (hg j).continuousAt.preimage_mem_nhds (isOpen_Iio.mem_nhds hneg)
    obtain ⟨x, hx1, hx2⟩ := (mem_closure_iff_nhds.mp hcl) _ hUmem
    exact absurd (hx2.2 j) (not_lt.mpr (le_of_lt hx1))
  -- (2) Restrict to the indices at which `g` vanishes at the origin, and apply the reduced form.
  let e : {j : Fin l // g j 0 = 0} ≃ Fin (Fintype.card {j : Fin l // g j 0 = 0}) :=
    Fintype.equivFin _
  let g' : Fin (Fintype.card {j : Fin l // g j 0 = 0}) → (Fin m → ℝ) → ℝ :=
    fun k => g (e.symm k).1
  have hg' : ∀ k, AnalyticAt ℝ (g' k) 0 := fun k => hg (e.symm k).1
  have hg'0 : ∀ k, g' k 0 = 0 := fun k => (e.symm k).2
  have hsub : BasicSA F g ⊆ BasicSA F g' := fun x hx => ⟨hx.1, fun k => hx.2 (e.symm k).1⟩
  have hcl' : (0 : Fin m → ℝ) ∈ closure (BasicSA F g') := closure_mono hsub hcl
  obtain ⟨γ, hγan, hγ0, ε, hεpos, hγε⟩ :=
    h (Fintype.card {j : Fin l // g j 0 = 0}) F g' hF hg' hg'0 hcl'
  -- (3) The dropped indices stay positive on a neighbourhood of the origin.
  have hev : ∀ᶠ s in 𝓝 (0 : ℝ), ∀ j, g j 0 ≠ 0 → 0 < g j (γ s) := by
    rw [Filter.eventually_all]
    intro j
    by_cases hj : g j 0 = 0
    · exact Filter.Eventually.of_forall fun s h => (h hj).elim
    · have hpos : 0 < g j 0 := lt_of_le_of_ne (hnonneg j) (Ne.symm hj)
      have hc0 : ContinuousAt (g j) (γ 0) := by rw [hγ0]; exact (hg j).continuousAt
      have hc : ContinuousAt (fun s : ℝ => g j (γ s)) 0 := hc0.comp' hγan.continuousAt
      have hmem : (fun s : ℝ => g j (γ s)) ⁻¹' Set.Ioi (0 : ℝ) ∈ 𝓝 (0 : ℝ) :=
        hc.preimage_mem_nhds (isOpen_Ioi.mem_nhds (by rw [hγ0]; exact hpos))
      have hevj : ∀ᶠ s in 𝓝 (0 : ℝ), 0 < g j (γ s) := by
        rw [Filter.eventually_iff]
        exact hmem
      exact hevj.mono fun s hs _ => hs
  obtain ⟨ε₁, hε₁pos, hε₁⟩ := Metric.eventually_nhds_iff.mp hev
  -- (4) Assemble the arc.
  refine ⟨γ, hγan, hγ0, min ε ε₁, lt_min hεpos hε₁pos, fun s hs => ?_⟩
  have hsε : s ∈ Set.Ioo (0 : ℝ) ε := ⟨hs.1, lt_of_lt_of_le hs.2 (min_le_left _ _)⟩
  have hsε₁ : s ∈ Set.Ioo (0 : ℝ) ε₁ := ⟨hs.1, lt_of_lt_of_le hs.2 (min_le_right _ _)⟩
  refine ⟨(hγε s hsε).1, fun j => ?_⟩
  by_cases hj : g j 0 = 0
  · have hk := (hγε s hsε).2 (e ⟨j, hj⟩)
    have key : g' (e ⟨j, hj⟩) (γ s) = g j (γ s) := by
      simp only [g', Equiv.symm_apply_apply, Subtype.coe_mk]
    rwa [key] at hk
  · refine hε₁ ?_ j hj
    rw [Real.dist_eq, sub_zero, abs_of_pos hs.1]
    exact hsε₁.2

end Work.WilC4aCS
