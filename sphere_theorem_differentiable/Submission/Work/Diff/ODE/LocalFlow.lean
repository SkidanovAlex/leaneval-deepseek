import Mathlib
import Submission.Work.Diff.ODE.Basic
import Submission.Work.Diff.ODE.ChartField
import Submission.Work.Diff.ODE.chartField_contDiffOn
import Submission.Commons.Analysis.ODE.uniform_flow_joint
import Submission.Commons.Geometry.Manifold.Tangent.hasMFDerivAt_extChartAt_symm_comp

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The local flow box of a jointly smooth time-dependent vector field

This file collects the four analytic ingredients of the proof of
`Work.Diff.ODE.exists_localBox`, i.e. of the existence of a local flow box
(`Work.Diff.ODE.LocalBox`) for a jointly smooth time-dependent vector field `X` on a boundaryless
`C^∞`-manifold, together with two tiny helpers about `HasDerivAt` into a product.

* `Work.Diff.ODE.chartField_contDiffOn` (already proved in the sibling module
  `Submission/Work/Diff/ODE/chartField_contDiffOn.lean`): the coordinate expression
  `chartField X x₀` of `X` is smooth on `univ × (extChartAt I x₀).target`;
* `hasDerivAt_fst_prod`, `hasDerivAt_snd_prod`: the component derivatives of a `HasDerivAt` into
  `ℝ × E` (used to extract the time coordinate of the extended flow);
* `hasMFDerivAt_chartCurve`: a coordinate curve in the chart target is a manifold curve whose
  velocity is the tangent vector with those coordinates (the chart-to-manifold direction);
* `contMDiffAt_chartFlow`: smooth dependence on the initial parameter and the time, transported
  back to the manifold through the chart;
* `isOpen_chartBox`: the box of parameters (time, point) for which the chart coordinates of the
  point lie in a given open set, is open;
* `fst_flow_eq_add`: for a flow of a field of the shape `x ↦ (1, F x)` the first coordinate is the
  initial first coordinate plus the elapsed time.
-/

namespace Work.Diff.ODE

open scoped Manifold ContDiff Bundle Topology
open Set Bundle Filter

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The first component of a `HasDerivAt` into a product, as a `HasDerivAt` of the component. -/
lemma hasDerivAt_fst_prod {f : ℝ → ℝ × E} {v : ℝ × E} {t : ℝ} (h : HasDerivAt f v t) :
    HasDerivAt (fun s => (f s).1) v.1 t := by
  have h1 := h.hasFDerivAt.fst
  have hclm : (ContinuousLinearMap.fst ℝ ℝ E) ∘SL (ContinuousLinearMap.toSpanSingleton ℝ v)
      = ContinuousLinearMap.toSpanSingleton ℝ v.1 := by
    ext; simp [ContinuousLinearMap.toSpanSingleton_apply]
  rw [hclm] at h1
  exact h1

/-- The second component of a `HasDerivAt` into a product, as a `HasDerivAt` of the component. -/
lemma hasDerivAt_snd_prod {f : ℝ → ℝ × E} {v : ℝ × E} {t : ℝ} (h : HasDerivAt f v t) :
    HasDerivAt (fun s => (f s).2) v.2 t := by
  have h1 := h.hasFDerivAt.snd
  have hclm : (ContinuousLinearMap.snd ℝ ℝ E) ∘SL (ContinuousLinearMap.toSpanSingleton ℝ v)
      = ContinuousLinearMap.toSpanSingleton ℝ v.2 := by
    ext; simp [ContinuousLinearMap.toSpanSingleton_apply]
  rw [hclm] at h1
  exact h1

variable
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]

/-- **A coordinate curve is a manifold curve with the corresponding velocity.**  If the coordinate
curve `w : ℝ → E` has derivative `v` at `τ`, takes its values in the target of the chart at `x₀`
near `τ`, and the coordinate vector `v` is the coordinate reading of the vector
`X (a + τ) (chart⁻¹ (w τ))`, then the chart curve `σ ↦ chart⁻¹ (w σ)` has that vector as its
manifold velocity. -/
theorem hasMFDerivAt_chartCurve
    [IsManifold I ((⊤ : ENat) : WithTop ENat) M]
    {X : ℝ → Π x : M, TangentSpace I x} {x₀ : M} {a τ : ℝ} {w : ℝ → E} {v : E}
    (hw : HasDerivAt w v τ)
    (htgt : w τ ∈ (extChartAt I x₀).target)
    (hstay : Filter.Eventually (fun σ => w σ ∈ (extChartAt I x₀).target) (nhds τ))
    (hv : v = (trivializationAt E (TangentSpace I) x₀).continuousLinearMapAt ℝ
        ((extChartAt I x₀).symm (w τ)) (X (a + τ) ((extChartAt I x₀).symm (w τ)))) :
    HasMFDerivAt (modelWithCornersSelf ℝ ℝ) I (fun σ => (extChartAt I x₀).symm (w σ)) τ
      ((1 : ℝ →L[ℝ] ℝ).smulRight (X (a + τ) ((extChartAt I x₀).symm (w τ)))) := by
  have hmf := Commons.Geometry.Manifold.Tangent.hasMFDerivAt_extChartAt_symm_comp (I := I)
    hw htgt hstay
  have hsrc : (extChartAt I x₀).symm (w τ) ∈ (extChartAt I x₀).source :=
    PartialEquiv.map_target (extChartAt I x₀) htgt
  have hbase : (extChartAt I x₀).symm (w τ) ∈
      (trivializationAt E (TangentSpace I) x₀).baseSet := by
    rw [TangentBundle.trivializationAt_baseSet]
    rwa [extChartAt_source] at hsrc
  rw [hv] at hmf
  have hsym : Trivialization.symmL ℝ (trivializationAt E (TangentSpace I) x₀)
      ((extChartAt I x₀).symm (w τ))
      ((trivializationAt E (TangentSpace I) x₀).continuousLinearMapAt ℝ
        ((extChartAt I x₀).symm (w τ)) (X (a + τ) ((extChartAt I x₀).symm (w τ))))
      = X (a + τ) ((extChartAt I x₀).symm (w τ)) :=
    Trivialization.symmL_continuousLinearMapAt (e := trivializationAt E (TangentSpace I) x₀) hbase _
  have hclm : (Trivialization.symmL ℝ (trivializationAt E (TangentSpace I) x₀)
        ((extChartAt I x₀).symm (w τ))) ∘SL
        (ContinuousLinearMap.toSpanSingleton ℝ
          ((trivializationAt E (TangentSpace I) x₀).continuousLinearMapAt ℝ
            ((extChartAt I x₀).symm (w τ)) (X (a + τ) ((extChartAt I x₀).symm (w τ)))))
      = (1 : ℝ →L[ℝ] ℝ).smulRight (X (a + τ) ((extChartAt I x₀).symm (w τ))) := by
    ext
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.toSpanSingleton_apply,
      ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.one_apply, one_smul]
    rw [hsym]
  rw [← hclm]
  exact hmf

/-- **Smooth dependence of the chart flow on the initial parameter and the time.**  If the model
flow `α` of an autonomous field on `ℝ × E` is smooth at `((a, chart y), τ)`, and the value at time
`τ` starts in the chart target, then the manifold curve
`r ↦ chart⁻¹ ((α (r.1.2, chart r.2) r.1.1).2)` is smooth at `((τ, a), y)`. -/
theorem contMDiffAt_chartFlow
    [IsManifold I ((⊤ : ENat) : WithTop ENat) M] [I.Boundaryless]
    {x₀ : M} {α : (ℝ × E) → ℝ → (ℝ × E)} {a : ℝ} {y : M} {τ : ℝ}
    (hy : y ∈ (extChartAt I x₀).source)
    (hα : ContDiffAt ℝ ((⊤ : ENat) : WithTop ENat)
      (fun q : ((ℝ × E) × ℝ) => α q.1 q.2) ((a, (extChartAt I x₀) y), τ))
    (htgt : (α (a, (extChartAt I x₀) y) τ).2 ∈ (extChartAt I x₀).target) :
    ContMDiffAt (((modelWithCornersSelf ℝ ℝ).prod (modelWithCornersSelf ℝ ℝ)).prod I) I
      ((⊤ : ENat) : WithTop ENat)
      (fun r : (ℝ × ℝ) × M => (extChartAt I x₀).symm ((α (r.1.2, (extChartAt I x₀) r.2) r.1.1).2))
      ((τ, a), y) := by
  have hysrc : y ∈ (chartAt H x₀).source := by rwa [extChartAt_source] at hy
  have h12 : ContMDiffAt (((modelWithCornersSelf ℝ ℝ).prod (modelWithCornersSelf ℝ ℝ)).prod I)
      (modelWithCornersSelf ℝ ℝ) ((⊤ : ENat) : WithTop ENat)
      (fun r : (ℝ × ℝ) × M => r.1.2) ((τ, a), y) :=
    ContMDiffAt.comp ((τ, a), y)
      (contMDiffAt_snd (I := modelWithCornersSelf ℝ ℝ) (J := modelWithCornersSelf ℝ ℝ))
      (contMDiffAt_fst (I := (modelWithCornersSelf ℝ ℝ).prod (modelWithCornersSelf ℝ ℝ)) (J := I))
  have h11 : ContMDiffAt (((modelWithCornersSelf ℝ ℝ).prod (modelWithCornersSelf ℝ ℝ)).prod I)
      (modelWithCornersSelf ℝ ℝ) ((⊤ : ENat) : WithTop ENat)
      (fun r : (ℝ × ℝ) × M => r.1.1) ((τ, a), y) :=
    ContMDiffAt.comp ((τ, a), y)
      (contMDiffAt_fst (I := modelWithCornersSelf ℝ ℝ) (J := modelWithCornersSelf ℝ ℝ))
      (contMDiffAt_fst (I := (modelWithCornersSelf ℝ ℝ).prod (modelWithCornersSelf ℝ ℝ)) (J := I))
  have he : ContMDiffAt (((modelWithCornersSelf ℝ ℝ).prod (modelWithCornersSelf ℝ ℝ)).prod I)
      (modelWithCornersSelf ℝ E) ((⊤ : ENat) : WithTop ENat)
      (fun r : (ℝ × ℝ) × M => (extChartAt I x₀) r.2) ((τ, a), y) :=
    ContMDiffAt.comp ((τ, a), y)
      (contMDiffAt_extChartAt' (x := x₀) (n := ((⊤ : ENat) : WithTop ENat)) hysrc)
      (contMDiffAt_snd (I := (modelWithCornersSelf ℝ ℝ).prod (modelWithCornersSelf ℝ ℝ)) (J := I))
  have hfst : ContMDiffAt (((modelWithCornersSelf ℝ ℝ).prod (modelWithCornersSelf ℝ ℝ)).prod I)
      (modelWithCornersSelf ℝ (ℝ × E)) ((⊤ : ENat) : WithTop ENat)
      (fun r : (ℝ × ℝ) × M => (r.1.2, (extChartAt I x₀) r.2)) ((τ, a), y) :=
    (contMDiffAt_prod_module_iff (fun r : (ℝ × ℝ) × M => (r.1.2, (extChartAt I x₀) r.2))).mpr
      ⟨by simpa [Function.comp_def] using h12, by simpa [Function.comp_def] using he⟩
  have hg : ContMDiffAt (((modelWithCornersSelf ℝ ℝ).prod (modelWithCornersSelf ℝ ℝ)).prod I)
      (modelWithCornersSelf ℝ ((ℝ × E) × ℝ)) ((⊤ : ENat) : WithTop ENat)
      (fun r : (ℝ × ℝ) × M => ((r.1.2, (extChartAt I x₀) r.2), r.1.1)) ((τ, a), y) :=
    (contMDiffAt_prod_module_iff
      (fun r : (ℝ × ℝ) × M => ((r.1.2, (extChartAt I x₀) r.2), r.1.1))).mpr
      ⟨by simpa [Function.comp_def] using hfst, by simpa [Function.comp_def] using h11⟩
  have hα' : ContMDiffAt (modelWithCornersSelf ℝ ((ℝ × E) × ℝ)) (modelWithCornersSelf ℝ (ℝ × E))
      ((⊤ : ENat) : WithTop ENat) (fun q : ((ℝ × E) × ℝ) => α q.1 q.2)
      ((a, (extChartAt I x₀) y), τ) := hα.contMDiffAt
  have hcomp := hα'.comp ((τ, a), y) hg
  have hval : ContMDiffAt (((modelWithCornersSelf ℝ ℝ).prod (modelWithCornersSelf ℝ ℝ)).prod I)
      (modelWithCornersSelf ℝ E) ((⊤ : ENat) : WithTop ENat)
      (fun r : (ℝ × ℝ) × M => (α (r.1.2, (extChartAt I x₀) r.2) r.1.1).2) ((τ, a), y) := by
    have h2 := ((contMDiffAt_prod_module_iff ((fun q : ((ℝ × E) × ℝ) => α q.1 q.2) ∘
      (fun r : (ℝ × ℝ) × M => ((r.1.2, (extChartAt I x₀) r.2), r.1.1)))).mp hcomp).2
    simpa only [Function.comp_def] using h2
  have hsymm : ContMDiffAt (modelWithCornersSelf ℝ E) I ((⊤ : ENat) : WithTop ENat)
      (extChartAt I x₀).symm ((α (a, (extChartAt I x₀) y) τ).2) :=
    (contMDiffOn_extChartAt_symm (I := I) x₀).contMDiffAt
      ((isOpen_extChartAt_target x₀).mem_nhds htgt)
  have hfin := hsymm.comp ((τ, a), y) hval
  simpa only [Function.comp_def] using hfin

/-- **The box of parameters whose chart coordinates lie in an open set is open.** -/
theorem isOpen_chartBox
    {x₀ : M} {O : Set (ℝ × E)} (hO : IsOpen O)
    (hOW : O ⊆ Set.prod Set.univ (extChartAt I x₀).target) :
    IsOpen {p : ℝ × M | p.2 ∈ (chartAt H x₀).source ∧ (p.1, (extChartAt I x₀) p.2) ∈ O} := by
  rw [isOpen_iff_mem_nhds]
  intro p hp
  obtain ⟨hsrc, hOmem⟩ := hp
  have h1 : {q : ℝ × M | q.2 ∈ (chartAt H x₀).source} ∈ 𝓝 p :=
    continuous_snd.continuousAt.preimage_mem_nhds
      ((chartAt H x₀).open_source.mem_nhds hsrc)
  have hca : ContinuousAt (fun q : ℝ × M => (extChartAt I x₀) q.2) p :=
    ((continuousOn_extChartAt x₀).continuousAt
      (by rw [extChartAt_source]; exact (chartAt H x₀).open_source.mem_nhds hsrc)).comp
      continuous_snd.continuousAt
  have hcont : ContinuousAt (fun q : ℝ × M => (q.1, (extChartAt I x₀) q.2)) p :=
    continuous_fst.continuousAt.prodMk hca
  have h2 : {q : ℝ × M | (q.1, (extChartAt I x₀) q.2) ∈ O} ∈ 𝓝 p :=
    hcont.preimage_mem_nhds (hO.mem_nhds hOmem)
  exact inter_mem h1 h2

/-- **The first coordinate of a flow of `x ↦ (1, F x)` advances at unit speed.** -/
theorem fst_flow_eq_add
    {F : ℝ × E → E} {O : Set (ℝ × E)} {ρ : ℝ}
    {α : ℝ × E → ℝ → ℝ × E} (h0 : ∀ p ∈ O, α p 0 = p)
    (hode : ∀ p ∈ O, ∀ t : ℝ, |t| ≤ ρ → HasDerivAt (α p) ((1 : ℝ), F (α p t)) t)
    {p : ℝ × E} (hp : p ∈ O) {σ : ℝ} (hσ : |σ| ≤ ρ) : (α p σ).1 = p.1 + σ := by
  have hfst : ∀ t : ℝ, |t| ≤ ρ → HasDerivAt (fun s : ℝ => (α p s).1) 1 t :=
    fun t ht => hasDerivAt_fst_prod (hode p hp t ht)
  have hderiv : ∀ t ∈ Icc (-ρ) ρ, HasDerivAt (fun s : ℝ => (α p s).1 - s) 0 t := by
    intro t ht
    have ht' : |t| ≤ ρ := by rw [abs_le]; exact ht
    have h := (hfst t ht').sub (hasDerivAt_id t)
    have key : (fun s : ℝ => (α p s).1 - s) = ((fun s : ℝ => (α p s).1) - id) := by
      funext s; simp [Pi.sub_apply]
    rw [key]
    simpa using h
  have hg0 : (fun s : ℝ => (α p s).1 - s) 0 = p.1 := by
    have := congrArg Prod.fst (h0 p hp)
    simp [this]
  have hconst : ∀ t : ℝ, HasDerivAt (fun _ : ℝ => p.1) ((fun _ : ℝ => (0:ℝ)) p.1) t :=
    fun t => by simpa using hasDerivAt_const (𝕜 := ℝ) t p.1
  have hloc_gen : ∀ y : ℝ, ∃ K : NNReal, ∃ U ∈ 𝓝 y, LipschitzOnWith K (fun _ : ℝ => (0:ℝ)) U :=
    fun y => ⟨0, univ, univ_mem, fun x _ z _ => by simp⟩
  rcases le_total 0 σ with hσ0 | hσ0
  · have hσρ : σ ≤ ρ := by rw [abs_of_nonneg hσ0] at hσ; exact hσ
    have hu : ∀ t ∈ Icc (0:ℝ) σ, HasDerivAt (fun s : ℝ => (α p s).1 - s)
        ((fun _ : ℝ => (0:ℝ)) ((fun s : ℝ => (α p s).1 - s) t)) t :=
      fun t ht => hderiv t ⟨by linarith [ht.1], by linarith [ht.2, hσρ]⟩
    have hv : ∀ t ∈ Icc (0:ℝ) σ, HasDerivAt (fun _ : ℝ => p.1) ((fun _ : ℝ => (0:ℝ)) p.1) t :=
      fun t _ => hconst t
    have hloc : ∀ t ∈ Icc (0:ℝ) σ, ∃ K : NNReal, ∃ U ∈ 𝓝 ((fun s : ℝ => (α p s).1 - s) t),
        LipschitzOnWith K (fun _ : ℝ => (0:ℝ)) U := fun t _ => hloc_gen _
    have heq := Commons.Analysis.ODE.eqOn_of_hasDerivAt_of_locallyLipschitz (f := fun _ : ℝ => (0:ℝ))
      (u := fun s : ℝ => (α p s).1 - s) (v := fun _ : ℝ => p.1) hσ0 hu hv hloc hg0
    have := heq (right_mem_Icc.mpr hσ0)
    linarith [this]
  · have hσρ : -σ ≤ ρ := by rw [abs_of_nonpos hσ0] at hσ; exact hσ
    have hu : ∀ t ∈ Icc (0:ℝ) (-σ), HasDerivAt (fun t : ℝ => (α p (-t)).1 + t)
        ((fun _ : ℝ => (0:ℝ)) ((fun t : ℝ => (α p (-t)).1 + t) t)) t := by
      intro t ht
      have htρ : |-t| ≤ ρ := by
        rw [abs_neg, abs_of_nonneg ht.1]; linarith [ht.2, hσρ]
      have h2 : HasDerivAt (fun r : ℝ => (α p (-r)).1) (-1) t := by
        have h := (hfst (-t) htρ).comp t (hasDerivAt_neg t)
        have key : (fun r : ℝ => (α p (-r)).1) = ((fun s : ℝ => (α p s).1) ∘ Neg.neg) := by
          funext r; simp
        rw [key]
        simpa using h
      have h3 := h2.add (hasDerivAt_id t)
      have key : (fun t : ℝ => (α p (-t)).1 + t) = ((fun r : ℝ => (α p (-r)).1) + id) := by
        funext r; simp [Pi.add_apply]
      rw [key]
      simpa using h3
    have hv : ∀ t ∈ Icc (0:ℝ) (-σ), HasDerivAt (fun _ : ℝ => p.1) ((fun _ : ℝ => (0:ℝ)) p.1) t :=
      fun t _ => hconst t
    have hloc : ∀ t ∈ Icc (0:ℝ) (-σ), ∃ K : NNReal, ∃ U ∈ 𝓝 ((fun t : ℝ => (α p (-t)).1 + t) t),
        LipschitzOnWith K (fun _ : ℝ => (0:ℝ)) U := fun t _ => hloc_gen _
    have h0' : (fun t : ℝ => (α p (-t)).1 + t) 0 = p.1 := by
      have := congrArg Prod.fst (h0 p hp)
      simp [this]
    have heq := Commons.Analysis.ODE.eqOn_of_hasDerivAt_of_locallyLipschitz (f := fun _ : ℝ => (0:ℝ))
      (u := fun t : ℝ => (α p (-t)).1 + t) (v := fun _ : ℝ => p.1) (neg_nonneg.mpr hσ0) hu hv hloc h0'
    have hmem : -σ ∈ Icc (0:ℝ) (-σ) := right_mem_Icc.mpr (neg_nonneg.mpr hσ0)
    have hres := heq hmem
    simp only [neg_neg] at hres
    linarith [hres]

end Work.Diff.ODE
