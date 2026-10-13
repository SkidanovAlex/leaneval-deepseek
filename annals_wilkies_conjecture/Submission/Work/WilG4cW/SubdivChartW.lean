/-
  WilG4cW / `SubdivChartW` — the composed chart `subdivChart α β s ψ` of BNZ §5.4 under the
  corrected chart rule `Work.WilkG4c.ChartInW` (see `ChartW.lean`).

  Two lemmas of the assembly consume the *strict* non-degeneracy `0 < β l` of the chart:

  * `Work.WilkG4c.subdivChart_mem_openCube` (the composed chart maps the cube into itself),
  * `Work.WilkG4c.covers_subdivChart` (the `ε`-cover of the assembly),

  and in both cases the only thing used is that the chart maps the cube into the cube and is
  distance-non-increasing — both available under `ChartInW` (`chartPt_mem_openCubeW`,
  `pullX_lipW`).  This file records the two W-versions.
-/
import Mathlib
import Submission.Work.WilG4c.StepHigherStageDefs
import Submission.Work.WilG4c.FLemAPI
import Submission.Work.WilG4cW.ChartW

set_option autoImplicit false
noncomputable section
open Classical

namespace Work.WilkG4c

open WilkiesDesign WilkiesDesign.CG

/-- **The composed chart maps the cube into itself, under `ChartInW`.**  The subdivision chart
maps the cube into the cube (`subdivMap_mem_openCube`), and the affine chart does by
`chartPt_mem_openCubeW`. -/
theorem subdivChart_mem_openCubeW {p n N : ℕ} (hN : 1 ≤ N) {α β : (Fin p → ℝ) → ℝ}
    {l : Fin p → ℝ} (h : ChartInW α β)
    {s : Fin (n + 1) → Fin (3 * (N - 1) + 1)} {ψ : ChartTuple p (n + 1)}
    (hψ : ∀ t ∈ openCube (n + 1), (fun j => ψ j l t) ∈ openCube (n + 1)) :
    ∀ t ∈ openCube (n + 1), (fun j => subdivChart α β s ψ j l t) ∈ openCube (n + 1) := by
  intro t ht
  have h1 : subdivMap N s (fun k => ψ k l t) ∈ openCube (n + 1) :=
    subdivMap_mem_openCube hN s (hψ t ht)
  exact chartPt_mem_openCubeW (h l) h1

/-- **The `ε`-cover of the assembly, under `ChartInW`.**  This is
`Work.WilkG4c.covers_subdivChart` with the per-chart hypothesis `0 < cb.2 l ∧ …` relaxed to
`ChartInW cb.1 cb.2`; the only place the strictness was used is the cube-membership of the
chart point, which `chartPt_mem_openCubeW` supplies from the image clause. -/
theorem covers_subdivChartW {k p n N : ℕ} (hN : 1 ≤ N) {Λ : Set (Fin p → ℝ)}
    {F : Family k p (n + 1)} {ε : ℝ} (hLip : LipOnCube F 1)
    {Φ₁ : Finset (((Fin p → ℝ) → ℝ) × ((Fin p → ℝ) → ℝ))}
    (hchart : ∀ cb ∈ Φ₁, ChartInW cb.1 cb.2)
    (hdom : ∀ l ∈ Λ, ∀ x ∈ I, ∃ cb ∈ Φ₁, ∃ t ∈ I, |cb.1 l + cb.2 l * t - x| < ε / 2)
    {Ψ : (((Fin p → ℝ) → ℝ) × ((Fin p → ℝ) → ℝ)) → (Fin (n + 1) → Fin (3 * (N - 1) + 1)) →
      Finset (ChartTuple p (n + 1))}
    (hcov : ∀ cb ∈ Φ₁, ∀ s, Covers Λ
      (fun i l t => pullX F cb.1 cb.2 i l (subdivMap N s t)) (Ψ cb s) (ε / 2)) :
    Covers Λ F (Φ₁.biUnion (fun cb => Finset.univ.biUnion (fun s =>
      (Ψ cb s).image (fun ψ => subdivChart cb.1 cb.2 s ψ)))) ε := by
  intro l hl x hx
  -- the `x`-coordinate is covered by an affine chart
  obtain ⟨hx0, hx1⟩ := hx 0
  obtain ⟨cb, hcb, t₀, ht₀, hclose⟩ := hdom l hl (x 0) ⟨hx0, hx1⟩
  have hc := hchart cb hcb
  -- the point of the pullback's cube and its chart point
  have hpt : pt t₀ (Fin.tail x) ∈ openCube (n + 1) :=
    pt_mem_openCube.mpr ⟨ht₀, fun j => hx j.succ⟩
  have hx' : chartPt cb.1 cb.2 l (pt t₀ (Fin.tail x)) ∈ openCube (n + 1) :=
    chartPt_mem_openCubeW (hc l) hpt
  have hdist : dist (chartPt cb.1 cb.2 l (pt t₀ (Fin.tail x))) x < ε / 2 := by
    have htail : Fin.tail (chartPt cb.1 cb.2 l (pt t₀ (Fin.tail x))) = Fin.tail x := by
      rw [chartPt_pt]
      exact tail_pt t₀ (Fin.tail x)
    refine lt_of_le_of_lt (dist_le_of_tail_eq htail) ?_
    rw [chartPt_pt, pt_zero]
    exact hclose
  -- the subdivision cover at that point
  obtain ⟨s, u, hu, hsu⟩ := subdivMap_covers hN hpt
  -- the `hP2`-cover of the subdivided pullback
  obtain ⟨ψ, hψ, t, ht, hbound⟩ := hcov cb hcb s l hl u hu
  refine ⟨subdivChart cb.1 cb.2 s ψ, ?_, t, ht, fun i => ?_⟩
  · refine Finset.mem_biUnion.mpr ⟨cb, hcb, Finset.mem_biUnion.mpr
      ⟨s, Finset.mem_univ s, Finset.mem_image.mpr ⟨ψ, hψ, rfl⟩⟩⟩
  · have h1 : |F i l (fun j => subdivChart cb.1 cb.2 s ψ j l t)
        - F i l (chartPt cb.1 cb.2 l (pt t₀ (Fin.tail x)))| < ε / 2 := by
      have h := hbound i
      simp only [pullX_apply] at h
      rw [hsu] at h
      exact h
    have h2 : |F i l (chartPt cb.1 cb.2 l (pt t₀ (Fin.tail x))) - F i l x| ≤ ε / 2 := by
      calc |F i l (chartPt cb.1 cb.2 l (pt t₀ (Fin.tail x))) - F i l x|
          ≤ 1 * dist (chartPt cb.1 cb.2 l (pt t₀ (Fin.tail x))) x := hLip i l _ x hx' hx
        _ ≤ ε / 2 := by rw [one_mul]; exact le_of_lt hdist
    calc |F i l (fun j => subdivChart cb.1 cb.2 s ψ j l t) - F i l x|
        ≤ |F i l (fun j => subdivChart cb.1 cb.2 s ψ j l t)
            - F i l (chartPt cb.1 cb.2 l (pt t₀ (Fin.tail x)))|
          + |F i l (chartPt cb.1 cb.2 l (pt t₀ (Fin.tail x))) - F i l x| := abs_sub_le _ _ _
      _ < ε / 2 + ε / 2 := add_lt_add_of_lt_of_le h1 h2
      _ = ε := by ring

end Work.WilkG4c
