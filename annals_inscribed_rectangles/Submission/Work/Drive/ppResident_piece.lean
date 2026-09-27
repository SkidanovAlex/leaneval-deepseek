import Mathlib
import Submission.Work.Drive.ppParity.Defs
import Submission.Work.Drive.ppParity.Shift

/-!
# The residency of one piece of the pair map (`S3` of `NOTES_LEAD_residency.md`)

* `Work.Drive.ppResident_piece` — at a base meet `x₀` of the pair family `(E, E')` against the two
  sweeps `(V, W)`, the two charts centred at the two *base values* at `x₀` contain all four values of
  the *intrinsically perturbed* family, for all sufficiently small parameters and all points of a
  compact neighbourhood of `x₀`.

This is a statement about *continuity alone*.  The two chart centres are the two values at `x₀`, so
each of the four conditions of `ppRegion` is the preimage of the (open) source of a chart under a
continuous map of the parameter-point space `ℝ⁸ × ℝ⁹`, and all four hold at `(0, x₀)`: the perturbed
chains reduce to the base ones at the zero parameter (`hΞ0`), and the base values at `x₀` are the
chart centres (`mem_chart_source`).  The only content is uniformity in the point — the standard tube
argument: the four conditions together define an open neighbourhood of `(0, x₀)`, from which one
extracts a product neighbourhood `ball 0 δ × ball x₀ ρ` by `nhds_prod_eq` + `Filter.mem_prod_iff`.
-/

namespace Work.Drive

open Manifold Set Filter
open scoped Topology

/-- **Joint continuity of the first block.**  The perturbed first plane chain
`(τ, y) ↦ (ppShift Ξ w (unpackFst τ) E) (ftS y) (ftU y)` is continuous in `(τ, y)`. -/
private lemma continuous_ppShift_fst
    {M : Type*} [TopologicalSpace M]
    {Ξ : EuclideanSpace ℝ (Fin 4) → M → M}
    (hΞc : Continuous (fun p : EuclideanSpace ℝ (Fin 4) × M => Ξ p.1 p.2))
    {E : ℝ → EuclideanSpace ℝ (Fin 2) → M}
    (hEc : Continuous (fun z : EuclideanSpace ℝ (Fin 9) => E (ftS z) (ftU z)))
    {w : ℝ → ℝ} (hw : Continuous w) :
    Continuous (fun q : EuclideanSpace ℝ (Fin 8) × EuclideanSpace ℝ (Fin 9) =>
      ppShift Ξ w (unpackFst q.1) E (ftS q.2) (ftU q.2)) := by
  have h1 : Continuous fun q : EuclideanSpace ℝ (Fin 8) × EuclideanSpace ℝ (Fin 9) =>
      w (ftS q.2) • unpackFst q.1 :=
    (hw.comp (by unfold ftS; fun_prop)).smul (unpackFst.continuous.comp continuous_fst)
  have h2 : Continuous fun q : EuclideanSpace ℝ (Fin 8) × EuclideanSpace ℝ (Fin 9) =>
      E (ftS q.2) (ftU q.2) := hEc.comp continuous_snd
  have h3 : Continuous fun q : EuclideanSpace ℝ (Fin 8) × EuclideanSpace ℝ (Fin 9) =>
      (w (ftS q.2) • unpackFst q.1, E (ftS q.2) (ftU q.2)) := h1.prodMk h2
  simpa only [ppShift, Function.comp_def] using hΞc.comp h3

/-- **Joint continuity of the second block.** -/
private lemma continuous_ppShift_snd
    {M : Type*} [TopologicalSpace M]
    {Ξ : EuclideanSpace ℝ (Fin 4) → M → M}
    (hΞc : Continuous (fun p : EuclideanSpace ℝ (Fin 4) × M => Ξ p.1 p.2))
    {E' : ℝ → EuclideanSpace ℝ (Fin 2) → M}
    (hE'c : Continuous (fun z : EuclideanSpace ℝ (Fin 9) => E' (ftS z) (ftU z)))
    {w : ℝ → ℝ} (hw : Continuous w) :
    Continuous (fun q : EuclideanSpace ℝ (Fin 8) × EuclideanSpace ℝ (Fin 9) =>
      ppShift Ξ w (unpackSnd q.1) E' (ftS q.2) (ftU q.2)) := by
  have h1 : Continuous fun q : EuclideanSpace ℝ (Fin 8) × EuclideanSpace ℝ (Fin 9) =>
      w (ftS q.2) • unpackSnd q.1 :=
    (hw.comp (by unfold ftS; fun_prop)).smul (unpackSnd.continuous.comp continuous_fst)
  have h2 : Continuous fun q : EuclideanSpace ℝ (Fin 8) × EuclideanSpace ℝ (Fin 9) =>
      E' (ftS q.2) (ftU q.2) := hE'c.comp continuous_snd
  have h3 : Continuous fun q : EuclideanSpace ℝ (Fin 8) × EuclideanSpace ℝ (Fin 9) =>
      (w (ftS q.2) • unpackSnd q.1, E' (ftS q.2) (ftU q.2)) := h1.prodMk h2
  simpa only [ppShift, Function.comp_def] using hΞc.comp h3

theorem ppResident_piece
    {M : Type*} [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 4)) M]
    [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4)))
      ((⊤ : ℕ∞) : WithTop ℕ∞) M]
    {E E' : ℝ → EuclideanSpace ℝ (Fin 2) → M} {V W : EuclideanSpace ℝ (Fin 3) → M}
    (hEc : Continuous (fun z : EuclideanSpace ℝ (Fin 9) => E (Work.Drive.ftS z) (Work.Drive.ftU z)))
    (hE'c : Continuous (fun z : EuclideanSpace ℝ (Fin 9) => E' (Work.Drive.ftS z) (Work.Drive.ftU z)))
    (hVc : Continuous (fun z : EuclideanSpace ℝ (Fin 9) => V (Work.Drive.ftY z)))
    (hWc : Continuous (fun z : EuclideanSpace ℝ (Fin 9) => W (Work.Drive.ftZ z)))
    {x₀ : EuclideanSpace ℝ (Fin 9)} (hx₀ : x₀ ∈ Work.Drive.ppMeet E E' V W)
    (Ξ : EuclideanSpace ℝ (Fin 4) → M → M)
    (hΞc : Continuous (fun p : EuclideanSpace ℝ (Fin 4) × M => Ξ p.1 p.2))
    (hΞ0 : ∀ p : M, Ξ 0 p = p)
    (w : ℝ → ℝ) (hw : Continuous w) :
    ∃ (K : Set (EuclideanSpace ℝ (Fin 9))) (δ : ℝ),
      IsCompact K ∧ 0 < δ ∧ x₀ ∈ interior K ∧
      ∀ (τ : EuclideanSpace ℝ (Fin 8)) (y : EuclideanSpace ℝ (Fin 9)), ‖τ‖ < δ → y ∈ K →
        Work.Drive.ppRegion (E (Work.Drive.ftS x₀) (Work.Drive.ftU x₀))
          (E' (Work.Drive.ftS x₀) (Work.Drive.ftU x₀))
          (Work.Drive.ppShift Ξ w (Work.Drive.unpackFst τ) E)
          (Work.Drive.ppShift Ξ w (Work.Drive.unpackSnd τ) E') V W y := by

  classical
  -- the two chart centres of the piece are the values of the two plane chains at the meet `x₀`
  -- (`set` is only a shorthand; `hp`, `hp'` unfold it when needed)
  obtain ⟨-, hVeq, hWeq⟩ :=
    (mem_ppMeet (E := E) (E' := E') (V := V) (W := W) (x := x₀)).mp hx₀
  set p : M := E (Work.Drive.ftS x₀) (Work.Drive.ftU x₀) with hp
  set p' : M := E' (Work.Drive.ftS x₀) (Work.Drive.ftU x₀) with hp'
  -- the four joint maps of the perturbed configuration are continuous
  have hcA := continuous_ppShift_fst (M := M) hΞc hEc hw
  have hcC := continuous_ppShift_snd (M := M) hΞc hE'c hw
  have hcB : Continuous fun q : EuclideanSpace ℝ (Fin 8) × EuclideanSpace ℝ (Fin 9) =>
      V (Work.Drive.ftY q.2) := hVc.comp continuous_snd
  have hcD : Continuous fun q : EuclideanSpace ℝ (Fin 8) × EuclideanSpace ℝ (Fin 9) =>
      W (Work.Drive.ftZ q.2) := hWc.comp continuous_snd
  -- the four membership conditions are the preimages of the (open) chart sources
  have hA : IsOpen {q : EuclideanSpace ℝ (Fin 8) × EuclideanSpace ℝ (Fin 9) |
      ppShift Ξ w (unpackFst q.1) E (Work.Drive.ftS q.2) (Work.Drive.ftU q.2)
        ∈ (chr p).source} := (chr p).open_source.preimage hcA
  have hB : IsOpen {q : EuclideanSpace ℝ (Fin 8) × EuclideanSpace ℝ (Fin 9) |
      V (Work.Drive.ftY q.2) ∈ (chr p).source} := (chr p).open_source.preimage hcB
  have hC : IsOpen {q : EuclideanSpace ℝ (Fin 8) × EuclideanSpace ℝ (Fin 9) |
      ppShift Ξ w (unpackSnd q.1) E' (Work.Drive.ftS q.2) (Work.Drive.ftU q.2)
        ∈ (chr p').source} := (chr p').open_source.preimage hcC
  have hD : IsOpen {q : EuclideanSpace ℝ (Fin 8) × EuclideanSpace ℝ (Fin 9) |
      W (Work.Drive.ftZ q.2) ∈ (chr p').source} := (chr p').open_source.preimage hcD
  -- at the zero parameter the perturbed chains are the base ones
  have hzero : ∀ (s : ℝ) (u : EuclideanSpace ℝ (Fin 2)),
      ppShift Ξ w (unpackFst (0 : EuclideanSpace ℝ (Fin 8))) E s u = E s u := by
    intro s u
    simp only [ppShift, map_zero, smul_zero]
    exact hΞ0 _
  have hzero' : ∀ (s : ℝ) (u : EuclideanSpace ℝ (Fin 2)),
      ppShift Ξ w (unpackSnd (0 : EuclideanSpace ℝ (Fin 8))) E' s u = E' s u := by
    intro s u
    simp only [ppShift, map_zero, smul_zero]
    exact hΞ0 _
  -- at `(τ, y) = (0, x₀)` all four conditions hold, by `mem_chart_source` at the values at `x₀`
  have hmA : ((0 : EuclideanSpace ℝ (Fin 8)), x₀) ∈
      {q : EuclideanSpace ℝ (Fin 8) × EuclideanSpace ℝ (Fin 9) |
        ppShift Ξ w (unpackFst q.1) E (Work.Drive.ftS q.2) (Work.Drive.ftU q.2)
          ∈ (chr p).source} := by
    show ppShift Ξ w (unpackFst (0 : EuclideanSpace ℝ (Fin 8))) E
      (Work.Drive.ftS x₀) (Work.Drive.ftU x₀) ∈ (chr p).source
    rw [hzero]
    change p ∈ (chr p).source
    exact mem_chart_source _ _
  have hmB : ((0 : EuclideanSpace ℝ (Fin 8)), x₀) ∈
      {q : EuclideanSpace ℝ (Fin 8) × EuclideanSpace ℝ (Fin 9) |
        V (Work.Drive.ftY q.2) ∈ (chr p).source} := by
    show V (Work.Drive.ftY x₀) ∈ (chr p).source
    rw [← hVeq]
    exact mem_chart_source _ _
  have hmC : ((0 : EuclideanSpace ℝ (Fin 8)), x₀) ∈
      {q : EuclideanSpace ℝ (Fin 8) × EuclideanSpace ℝ (Fin 9) |
        ppShift Ξ w (unpackSnd q.1) E' (Work.Drive.ftS q.2) (Work.Drive.ftU q.2)
          ∈ (chr p').source} := by
    show ppShift Ξ w (unpackSnd (0 : EuclideanSpace ℝ (Fin 8))) E'
      (Work.Drive.ftS x₀) (Work.Drive.ftU x₀) ∈ (chr p').source
    rw [hzero']
    change p' ∈ (chr p').source
    exact mem_chart_source _ _
  have hmD : ((0 : EuclideanSpace ℝ (Fin 8)), x₀) ∈
      {q : EuclideanSpace ℝ (Fin 8) × EuclideanSpace ℝ (Fin 9) |
        W (Work.Drive.ftZ q.2) ∈ (chr p').source} := by
    show W (Work.Drive.ftZ x₀) ∈ (chr p').source
    rw [← hWeq]
    exact mem_chart_source _ _
  -- hence the conjunction of the four conditions is a neighbourhood of `(0, x₀)`
  have hW : ({q : EuclideanSpace ℝ (Fin 8) × EuclideanSpace ℝ (Fin 9) |
        ppShift Ξ w (unpackFst q.1) E (Work.Drive.ftS q.2) (Work.Drive.ftU q.2)
          ∈ (chr p).source} ∩
      ({q : EuclideanSpace ℝ (Fin 8) × EuclideanSpace ℝ (Fin 9) |
          V (Work.Drive.ftY q.2) ∈ (chr p).source} ∩
        ({q : EuclideanSpace ℝ (Fin 8) × EuclideanSpace ℝ (Fin 9) |
            ppShift Ξ w (unpackSnd q.1) E' (Work.Drive.ftS q.2) (Work.Drive.ftU q.2)
              ∈ (chr p').source} ∩
          {q : EuclideanSpace ℝ (Fin 8) × EuclideanSpace ℝ (Fin 9) |
            W (Work.Drive.ftZ q.2) ∈ (chr p').source}))) ∈
      𝓝 (((0 : EuclideanSpace ℝ (Fin 8)), x₀)) :=
    (hA.inter (hB.inter (hC.inter hD))).mem_nhds ⟨hmA, hmB, hmC, hmD⟩
  -- extract a product neighbourhood `U' × V` and a uniform radius on the parameter
  rw [nhds_prod_eq] at hW
  obtain ⟨U', hU', Vv, hVv, hUV⟩ := Filter.mem_prod_iff.mp hW
  obtain ⟨r, hr, hrU⟩ := Metric.mem_nhds_iff.mp hU'
  obtain ⟨ρ, hρ, hρV⟩ := Metric.mem_nhds_iff.mp hVv
  refine ⟨Metric.closedBall x₀ (ρ / 2), r, isCompact_closedBall x₀ (ρ / 2), hr, ?_, ?_⟩
  · exact interior_maximal Metric.ball_subset_closedBall Metric.isOpen_ball
      (Metric.mem_ball_self (half_pos hρ))
  · intro τ y hτ hy
    have hyρ : y ∈ Metric.ball x₀ ρ :=
      Metric.closedBall_subset_ball (by linarith) hy
    have hτU : τ ∈ U' := hrU (by rw [Metric.mem_ball, dist_zero_right]; exact hτ)
    have hmem' : (τ, y) ∈ U' ×ˢ Vv := Set.mem_prod.mpr ⟨hτU, hρV hyρ⟩
    exact hUV hmem'

end Work.Drive
