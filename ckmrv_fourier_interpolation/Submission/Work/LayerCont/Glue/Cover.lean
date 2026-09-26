/-
# From a chart family on a compact set to one holomorphic function on a neighbourhood

This is the compactness plumbing of the gluing: given a **compact** `K ⊆ ℍ`, a ball `B(x)` and a
function `chart x` holomorphic on it for every `x ∈ K` such that

* `x ∈ B(x)` for every `x` (so the balls cover `K`, giving a **finite** subcover by compactness),
* `chart x` and `chart y` agree on a non-empty open subset of `B(x) ∩ B(y)` (which is how the charts
  of the layer continuation agree — they all equal `paperLayer` on the `𝒟`-side of their ball),

there is an open `O ⊇ K` and a holomorphic `F₂` on `O`.  The proof takes the finite subcover
(`IsCompact.elim_finite_subcover`), upgrades the local agreement to the pairwise agreement on whole
intersections by the identity theorem on the (preconnected) intersections, and applies
`Work.LayerCont.Glue.exists_glue_finset`.

The chart family itself is a *hypothesis* here: this isolates the plumbing from the analytic work of
building the charts (for the layer continuation: the line charts `WindowCapstone`/`Right`, the arc
charts `Arc`+`ArcHolo`, `paperLayer` in the interior and on the two cusps).
-/
import Mathlib
import Submission.Work.LayerCont.Glue.Finset

set_option linter.unusedVariables false

noncomputable section

open UpperHalfPlane MeasureTheory Filter Topology
open scoped Topology Manifold

namespace Work.LayerCont.Glue

open Work.Asymptotics Work.LayerCont

/-- **Gluing a chart family over a compact set.** -/
theorem exists_glued_on_nbd_of_charts {K : Set UpperHalfPlane} (hK : IsCompact K)
    (c : K → UpperHalfPlane) (ε : K → ℝ) (chart : K → UpperHalfPlane → ℂ)
    (hmem : ∀ x : K, (x : UpperHalfPlane) ∈ Metric.ball (c x) (ε x))
    (hchart : ∀ x, MDifferentiableOn (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ)
      (chart x) (Metric.ball (c x) (ε x)))
    (hpair : ∀ x y : K, ∃ V : Set UpperHalfPlane,
      V ⊆ Metric.ball (c x) (ε x) ∩ Metric.ball (c y) (ε y) ∧ IsOpen V ∧ V.Nonempty ∧
      Set.EqOn (chart x) (chart y) V) :
    ∃ (O : Set UpperHalfPlane) (F₂ : UpperHalfPlane → ℂ),
      IsOpen O ∧ K ⊆ O ∧
      MDifferentiableOn (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ) F₂ O := by
  classical
  have hcover : K ⊆ ⋃ x : K, Metric.ball (c x) (ε x) := by
    intro x hx
    exact Set.mem_iUnion.mpr ⟨⟨x, hx⟩, hmem ⟨x, hx⟩⟩
  obtain ⟨t, ht⟩ := hK.elim_finite_subcover (fun x : K => Metric.ball (c x) (ε x))
    (fun x => Metric.isOpen_ball) hcover
  have hpair' : ∀ x ∈ t, ∀ y ∈ t,
      Set.EqOn (chart x) (chart y) (Metric.ball (c x) (ε x) ∩ Metric.ball (c y) (ε y)) := by
    intro x _ y _
    obtain ⟨V, hVsub, hVopen, hVne, hVeq⟩ := hpair x y
    exact eqOn_of_mdifferentiableOn_of_preconnected
      (Metric.isOpen_ball.inter Metric.isOpen_ball)
      (isPreconnected_inter_ball (c x) (c y) (ε x) (ε y))
      ((hchart x).mono Set.inter_subset_left) ((hchart y).mono Set.inter_subset_right)
      hVsub hVopen hVne hVeq
  obtain ⟨F, hF, -⟩ := exists_glue_finset t c ε chart (fun x _ => hchart x) hpair'
  exact ⟨⋃ x ∈ (t : Set K), Metric.ball (c x) (ε x), F,
    isOpen_biUnion (fun x _ => Metric.isOpen_ball), ht, hF⟩

/-- **The same, specialised to the compact piece of `closure 𝒟`.**  The compactness of
`closure DomainD ∩ {δ ≤ Im ≤ T}` (for `0 < δ ≤ T`) is taken as a hypothesis here: it is the
statement that this set is a closed subset of the compact box `{|Re| ≤ 1} × [δ,T]` inside `ℍ`,
which is a separate (and purely geometric) sub-step. -/
theorem exists_glued_on_nbd_of_charts_DomainD {δ T : ℝ}
    (hK : IsCompact (closure Work.Asymptotics.DomainD ∩
      {z : UpperHalfPlane | δ ≤ z.im ∧ z.im ≤ T}))
    (c : (closure Work.Asymptotics.DomainD ∩ {z : UpperHalfPlane | δ ≤ z.im ∧ z.im ≤ T} :
      Set UpperHalfPlane) → UpperHalfPlane)
    (ε : _ → ℝ) (chart : _ → UpperHalfPlane → ℂ)
    (hmem : ∀ x : (closure Work.Asymptotics.DomainD ∩
        {z : UpperHalfPlane | δ ≤ z.im ∧ z.im ≤ T} : Set UpperHalfPlane),
      (x : UpperHalfPlane) ∈ Metric.ball (c x) (ε x))
    (hchart : ∀ x, MDifferentiableOn (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ)
      (chart x) (Metric.ball (c x) (ε x)))
    (hpair : ∀ x y : (closure Work.Asymptotics.DomainD ∩
        {z : UpperHalfPlane | δ ≤ z.im ∧ z.im ≤ T} : Set UpperHalfPlane),
      ∃ V : Set UpperHalfPlane,
        V ⊆ Metric.ball (c x) (ε x) ∩ Metric.ball (c y) (ε y) ∧ IsOpen V ∧ V.Nonempty ∧
        Set.EqOn (chart x) (chart y) V) :
    ∃ (O : Set UpperHalfPlane) (F₂ : UpperHalfPlane → ℂ),
      IsOpen O ∧
      (closure Work.Asymptotics.DomainD ∩ {z : UpperHalfPlane | δ ≤ z.im ∧ z.im ≤ T}) ⊆ O ∧
      MDifferentiableOn (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ) F₂ O :=
  exists_glued_on_nbd_of_charts hK c ε chart hmem hchart hpair

end Work.LayerCont.Glue
