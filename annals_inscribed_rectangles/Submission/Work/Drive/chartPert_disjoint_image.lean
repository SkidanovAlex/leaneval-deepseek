import Mathlib
import Submission.Work.Drive.exists_chartPert

/-!
# The chart perturbations of the capping space act disjointly for small parameters

`Work.Drive.chartPert` (`Submission/Work/Drive/chartPertData.lean`) is the `4`-parameter family of
self-maps of the capping space `Work.Drive.CappingSpace` that the `hdense`/`sideGerm` design uses as a
*chart perturbation* of the plane charts; `Work.Drive.exists_chartPert`
(`Submission/Work/Drive/exists_chartPert.lean`) proves it to be jointly `C^∞` with `chartPert 0 = id`
and with onto parameter-derivative at every point.

This file proves the **smallness uniformity** of that family: two *disjoint compact* subsets of the
capping space are moved to disjoint subsets as soon as both parameters are small enough:

> `Work.Drive.chartPert_disjoint_image`: for compact disjoint `K`, `K'` there is `r > 0` with
> `Disjoint (chartPert τ₀ '' K) (chartPert τ₁ '' K')` for all `τ₀`, `τ₁` with `‖τ₀‖ < r`, `‖τ₁‖ < r`.

This is the robustness statement the consumers of the design need (the same form as
`Work.Drive.exists_small_chartPert_disjoint` of `Submission/Work/Drive/exists_small_chartPert_disjoint.lean`,
without the rotation factor): because the two images are perturbed by *two independent* parameters, a
uniform radius controls the collision of the graph of the first chart with the image of the second.

The proof is the tube lemma applied to the collision set `{u : Y × Y | u.1 ≠ u.2}`, over the compact
set `K × K'`:

* `(τ₀, τ₁, x, y) ↦ (chartPert τ₀ x, chartPert τ₁ y)` is continuous (joint continuity of the family,
  from the `C^∞` statement `contMDiff_chartPert`), so the collision set is open;
* at the parameter `(0, 0)` the two sides are `K` and `K'` themselves (`chartPert 0 = id`), which are
  disjoint by hypothesis;
* the tube lemma upgrades the pointwise statement into a neighbourhood `V` of `(0, 0)` with
  `V × (K × K') ⊆ {u | u.1 ≠ u.2}`, and a metric ball inside `V` gives the radius `r`.

The local instances below are exactly the ones under which `Work.Drive.contMDiff_chartPert` and
`Work.Drive.t2Space_cappingSpace` are stated.  They do not change the topology of `CappingSpace`,
which is the quotient topology of `Work.Drive.cappingSetoid`, also without them.
-/

namespace Work.Drive

open Filter Set
open scoped Topology

attribute [local instance] Work.Drive.cappingCharted Work.Drive.isManifold_cappingCharted
  Work.Drive.t2Space_cappingSpace Work.Drive.projCharted

noncomputable section

set_option maxHeartbeats 1000000

/-- **The tube lemma.**  If `K` is compact and the open set `U ⊆ P × X` contains `{y₀} × K`, then a
whole neighbourhood `V` of `y₀` satisfies `V × K ⊆ U`.  (A local copy, so that this file depends only
on `exists_chartPert`; it is also the engine of `Work.Drive.tube_smallChartPert`.) -/
theorem tube_chartPert_disjoint_image {P X : Type*} [TopologicalSpace P] [TopologicalSpace X]
    {y₀ : P} {K : Set X} (hK : IsCompact K) {U : Set (P × X)} (hU : IsOpen U)
    (h : ∀ x ∈ K, (y₀, x) ∈ U) :
    ∃ V ∈ 𝓝 y₀, ∀ y ∈ V, ∀ x ∈ K, (y, x) ∈ U := by
  classical
  have key : ∀ x ∈ K, ∃ V ∈ 𝓝 y₀, ∃ W ∈ 𝓝 x, V ×ˢ W ⊆ U := by
    intro x hx
    have hmem : U ∈ 𝓝 (y₀, x) := hU.mem_nhds (h x hx)
    rw [nhds_prod_eq] at hmem
    exact Filter.mem_prod_iff.mp hmem
  choose V hV W hW hVW using key
  obtain ⟨t, ht⟩ := hK.elim_nhds_subcover' W hW
  refine ⟨⋂ i ∈ (t : Set ↥K), V i.1 i.2,
    (Filter.biInter_mem t.finite_toSet).mpr (fun i _ => hV i.1 i.2), ?_⟩
  intro y hy x hx
  obtain ⟨z, hzt, hxz⟩ := Set.mem_iUnion₂.mp (ht hx)
  exact (hVW z.1 z.2) ⟨(Set.mem_iInter₂.mp hy) z hzt, hxz⟩

/-- **Two disjoint compact subsets of the capping space are separated by every pair of small chart
perturbations.**  There is `r > 0` such that `chartPert τ₀ '' K` and `chartPert τ₁ '' K'` are disjoint
whenever `‖τ₀‖ < r` and `‖τ₁‖ < r`. -/
theorem chartPert_disjoint_image {K K' : Set CappingSpace} (hK : IsCompact K)
    (hK' : IsCompact K') (hdisj : Disjoint K K') :
    ∃ r : ℝ, 0 < r ∧ ∀ τ₀ τ₁ : Eucl 3, ‖τ₀‖ < r → ‖τ₁‖ < r →
      Disjoint (chartPert τ₀ '' K) (chartPert τ₁ '' K') := by
  classical
  have hdisj' : ∀ x ∈ K, ∀ y ∈ K', x ≠ y := fun x hx y hy hxy =>
    Set.disjoint_left.mp hdisj hx (hxy.symm ▸ hy)
  -- the joint family `(τ₀, τ₁, x, y) ↦ (chartPert τ₀ x, chartPert τ₁ y)` is continuous
  have hJ : Continuous fun z : (Eucl 3 × Eucl 3) × (CappingSpace × CappingSpace) =>
      (chartPert z.1.1 z.2.1, chartPert z.1.2 z.2.2) := by
    have hcont : Continuous fun q : Eucl 3 × CappingSpace => chartPert q.1 q.2 :=
      contMDiff_chartPert.continuous
    have hlin₁ : Continuous fun z : (Eucl 3 × Eucl 3) × (CappingSpace × CappingSpace) =>
        ((z.1.1, z.2.1) : Eucl 3 × CappingSpace) :=
      continuous_fst.fst.prodMk continuous_snd.fst
    have hlin₂ : Continuous fun z : (Eucl 3 × Eucl 3) × (CappingSpace × CappingSpace) =>
        ((z.1.2, z.2.2) : Eucl 3 × CappingSpace) :=
      continuous_fst.snd.prodMk continuous_snd.snd
    have hc₁ : Continuous ((fun q : Eucl 3 × CappingSpace => chartPert q.1 q.2) ∘
        (fun z : (Eucl 3 × Eucl 3) × (CappingSpace × CappingSpace) =>
          ((z.1.1, z.2.1) : Eucl 3 × CappingSpace))) := hcont.comp hlin₁
    have hc₂ : Continuous ((fun q : Eucl 3 × CappingSpace => chartPert q.1 q.2) ∘
        (fun z : (Eucl 3 × Eucl 3) × (CappingSpace × CappingSpace) =>
          ((z.1.2, z.2.2) : Eucl 3 × CappingSpace))) := hcont.comp hlin₂
    -- write the joint family in the composite form produced by `Continuous.comp`
    rw [show (fun z : (Eucl 3 × Eucl 3) × (CappingSpace × CappingSpace) =>
          (chartPert z.1.1 z.2.1, chartPert z.1.2 z.2.2))
        = fun z : (Eucl 3 × Eucl 3) × (CappingSpace × CappingSpace) =>
            (((fun q : Eucl 3 × CappingSpace => chartPert q.1 q.2) ∘
                (fun z : (Eucl 3 × Eucl 3) × (CappingSpace × CappingSpace) =>
                  ((z.1.1, z.2.1) : Eucl 3 × CappingSpace))) z,
              ((fun q : Eucl 3 × CappingSpace => chartPert q.1 q.2) ∘
                (fun z : (Eucl 3 × Eucl 3) × (CappingSpace × CappingSpace) =>
                  ((z.1.2, z.2.2) : Eucl 3 × CappingSpace))) z) from by
      funext z; rfl]
    exact hc₁.prodMk hc₂
  -- the collision set is open in the capping space, which is Hausdorff
  have hU : IsOpen ((fun z : (Eucl 3 × Eucl 3) × (CappingSpace × CappingSpace) =>
      (chartPert z.1.1 z.2.1, chartPert z.1.2 z.2.2)) ⁻¹'
      {u : CappingSpace × CappingSpace | u.1 ≠ u.2}) :=
    isClosed_diagonal.isOpen_compl.preimage hJ
  -- at the parameter `(0, 0)` the two sides are `K` and `K'`
  have hmem : ∀ x ∈ K ×ˢ K', (((0 : Eucl 3), (0 : Eucl 3)), x) ∈
      ((fun z : (Eucl 3 × Eucl 3) × (CappingSpace × CappingSpace) =>
      (chartPert z.1.1 z.2.1, chartPert z.1.2 z.2.2)) ⁻¹'
      {u : CappingSpace × CappingSpace | u.1 ≠ u.2}) := by
    rintro ⟨p, q⟩ ⟨hp, hq⟩
    show chartPert 0 p ≠ chartPert 0 q
    rw [chartPert_zero, chartPert_zero]
    exact hdisj' p hp q hq
  -- the tube lemma makes the pointwise statement uniform over `K × K'`
  obtain ⟨V, hV, hVsub⟩ := tube_chartPert_disjoint_image
    (y₀ := (((0 : Eucl 3), (0 : Eucl 3)))) (hK.prod hK') hU hmem
  obtain ⟨ρ, hρ, hb⟩ := Metric.mem_nhds_iff.mp hV
  refine ⟨ρ, hρ, fun τ₀ τ₁ h₀ h₁ => ?_⟩
  have hmemV : ((τ₀, τ₁) : Eucl 3 × Eucl 3) ∈ V := hb (by
    simp only [Metric.mem_ball, dist_eq_norm, Prod.norm_def, Prod.fst_sub, Prod.snd_sub, sub_zero]
    exact max_lt h₀ h₁)
  rw [Set.disjoint_left]
  intro x hx hy
  rcases hx with ⟨p, hp, rfl⟩
  rcases hy with ⟨q, hq, hqeq⟩
  exact hVsub (τ₀, τ₁) hmemV (p, q) ⟨hp, hq⟩ hqeq.symm

end

end Work.Drive
