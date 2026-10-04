import Mathlib
import Submission.Work.Diff.GE.deps
import Submission.Work.Diff.GE.cGram_eq_sum_gramInv
import Submission.Work.Diff.EXT.contMDiffAt_matrix_inv
import Submission.Work.Diff.T.metric_pairing_smooth

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Joint smoothness of the chart expression for `∇Rm`

`Work.Diff.GE.covRmChartExpr G x₀ m i j k l` is the component `(∇_{σ_m}Rm)(σᵢ,σⱼ,σₖ,σₗ)` of the
covariant derivative of the curvature of the metric `G t` in the coordinate frame `σ_a = cFrame x₀ a`
of the chart at `x₀`, written out explicitly in terms of the metric components (`mComp`), the
Koszul pairings (`koszulPair`), the inverse Gram matrix (`GramInv`) and the Christoffel symbols
(`chrCoord`) — see `Submission/Work/Diff/GE/norms_defs.lean`.

This file proves that it is *jointly* `C^∞` in `(t, y)` on `Ico 0 T ×ˢ (chartAt H x₀).source` for a
jointly smooth family of metrics `G` (the missing piece of the regularity development REG described
in `Work.Diff.GE.norms_smooth`, needed for the smoothness of `dRmNormSq` along the flow).

The proof is a chain of `ContMDiffOn` statements on the same set
`S = Ico 0 T ×ˢ (chartAt H x₀).source`:

* `mComp_contMDiffOn` — the metric components are metric pairings of smooth sections, hence jointly
  smooth (`Work.Diff.T.metric_pairing_smooth`); this is the base of the chain;
* `dOp_contMDiffOn` — the coordinate derivative `dOp x₀ a Φ t y = mvfderiv I (Φ t) y (σ_a y)` of a
  jointly smooth family is jointly smooth.  This is the only analytic input and it is *assumed* as
  the hypothesis `hder` (the within-set derivative lemma, proved in `Work.Diff.GE.joint_deriv`), so
  that this file is independent of it.  Since the coordinate frame `σ_a` is smooth only on the
  chart while `hder` needs a globally smooth direction field and the global set
  `Ico 0 T ×ˢ univ`, at a point `p = (t,x)` we multiply `Φ` by a bump function `ψ` supported in the
  chart and centred at `x`, we replace `σ_a` by a globally smooth section `Y` agreeing with it near
  `x`, apply `hder`, and transport back with `ContMDiffWithinAt.mono_of_mem_nhdsWithin`;
* `koszulPair_contMDiffOn` — `koszulPair` is `½ (∂_a G_{bc} + ∂_b G_{ac} - ∂_c G_{ab})`
  *definitionally*, so it is a combination of the previous step;
* `gramInv_contMDiffOn` — Cramer's rule: the entries of the inverse of a nonsingular smooth matrix
  family are smooth, applied to the Gram matrix of the coordinate frame (nonsingular on the chart
  because it is the Gram matrix of a basis for a positive definite form);
* `chrCoord_contMDiffOn`, `rmChartExpr_contMDiffOn`, `covRmChartExpr_contMDiffOn` — the explicit
  expressions, which are finite sums and products of the above.
-/

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option maxHeartbeats 1000000

namespace Work.Diff.GE

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology BigOperators
open Bundle ContDiff Set VectorField CovariantDerivative Metric
open Filter Submission.Geodesic

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M] [IsManifold I ∞ M]

noncomputable section

/-! ## Elementary tools -/

/-- `mvfderiv` of `ℝ`-valued functions depends only on the germ at the point. -/
private theorem mvfderiv_congr_germ {f g : M → ℝ} {x : M} (h : f =ᶠ[𝓝 x] g) :
    mvfderiv I f x = mvfderiv I g x := by
  rw [mvfderiv, mvfderiv, h.eq_of_nhds, Filter.EventuallyEq.mfderiv_eq h]
  all_goals rfl

/-- The coordinate frame vector `frameSection x₀ v` is a smooth section at every point of the
chart at `x₀`.  (Copy of `Submission.Geodesic.contMDiffAt_frameSection`, stated without the
Riemannian bundle hypotheses, which its proof does not use.) -/
theorem contMDiffAt_frameSection'
    (x₀ : M) (v : E) {x : M} (hx : x ∈ (chartAt H x₀).source) :
    CMDiffAt ∞ (T% (frameSection (I := I) x₀ v)) x := by
  rw [Trivialization.contMDiffAt_section_iff (trivializationAt E (TangentSpace I) x₀)
    (by simpa using hx)]
  refine (contMDiffAt_const (c := v)).congr_of_eventuallyEq ?_
  filter_upwards [(trivializationAt E (TangentSpace I) x₀).open_baseSet.mem_nhds
    (by simpa using hx)] with y hy
  rw [show frameSection (I := I) x₀ v y
      = (trivializationAt E (TangentSpace I) x₀).symmL ℝ y v from rfl]
  rw [Trivialization.symmL_apply (e := trivializationAt E (TangentSpace I) x₀) (R := ℝ) hy v]
  exact congrArg Prod.snd ((trivializationAt E (TangentSpace I) x₀).apply_mk_symm hy v)

/-- **Extension of a coordinate frame field to a global smooth section.**  For a point `x` of the
chart at `x₀` there is a globally `C^∞` section of the tangent bundle agreeing with the coordinate
frame vector `frameSection x₀ v` in a neighbourhood of `x`. -/
theorem exists_smooth_section_eventuallyEq_frameSection
    (x₀ : M) (v : E) {x : M} (hx : x ∈ (chartAt H x₀).source) :
    ∃ Y : Π y : M, TangentSpace I y,
      CMDiff ∞ (T% Y) ∧ Y =ᶠ[𝓝 x] frameSection (I := I) x₀ v := by
  obtain ⟨ψ, -, hψts⟩ := (SmoothBumpFunction.nhds_basis_tsupport (I := I) x).mem_iff.mp
    ((chartAt H x₀).open_source.mem_nhds hx)
  refine ⟨fun y => ψ y • frameSection (I := I) x₀ v y, ?_, ?_⟩
  · intro y
    by_cases hy : y ∈ (chartAt H x₀).source
    · exact ψ.contMDiffAt.smul_section (contMDiffAt_frameSection' (I := I) x₀ v hy)
    · have hnotin : y ∉ tsupport (ψ : M → ℝ) := fun h => hy (hψts h)
      have h0 : (ψ : M → ℝ) =ᶠ[𝓝 y] 0 := notMem_tsupport_iff_eventuallyEq.mp hnotin
      refine (contMDiffAt_zeroSection (𝕜 := ℝ) (F := E) (E := fun y : M => TangentSpace I y)
        (x := y)).congr_of_eventuallyEq ?_
      filter_upwards [h0] with z hz
      have hz0 : (ψ : M → ℝ) z = 0 := by simpa using hz
      show (⟨z, ψ z • frameSection (I := I) x₀ v z⟩ : TotalSpace E (TangentSpace I))
        = zeroSection E (TangentSpace I) z
      rw [hz0, zero_smul]
      rfl
  · filter_upwards [ψ.eventuallyEq_one] with y hy
    have hy1 : (ψ : M → ℝ) y = 1 := by simpa using hy
    rw [hy1, one_smul]

/-- The global set contains the chart set, as a within-filter statement. -/
private theorem prod_mem_nhdsWithin_prod (x₀ : M) (J : Set ℝ) (p : ℝ × M) :
    J ×ˢ (univ : Set M) ∈ 𝓝[J ×ˢ (chartAt H x₀).source] p :=
  mem_of_superset self_mem_nhdsWithin (Set.prod_mono Subset.rfl (fun _ _ => mem_univ _))

/-- Conversely, the chart set is a neighbourhood of a point of it within the global set. -/
private theorem prod_mem_nhdsWithin_prod' (x₀ : M) (J : Set ℝ) (p : ℝ × M)
    (hp : p.2 ∈ (chartAt H x₀).source) :
    J ×ˢ (chartAt H x₀).source ∈ 𝓝[J ×ˢ (univ : Set M)] p := by
  rw [mem_nhdsWithin_iff_exists_mem_nhds_inter]
  exact ⟨univ ×ˢ (chartAt H x₀).source,
    (isOpen_univ.prod (chartAt H x₀).open_source).mem_nhds ⟨mem_univ _, hp⟩,
    fun y hy => ⟨hy.2.1, hy.1.2⟩⟩

/-- The metric components of a jointly smooth family are `∂_a G_{bc}` in coordinates. -/
private theorem mComp_eq (G : ℝ → SMet I M) (x₀ : M) (b c : Fin (Module.finrank ℝ E)) (t : ℝ) :
    mComp (I := I) G x₀ b c t
      = fun y' : M => (G t).inner y' (cFrame (I := I) x₀ b y') (cFrame (I := I) x₀ c y') :=
  rfl

/-! ## The chart metric components -/

/-- **Joint smoothness of the metric components in the coordinate frame.** -/
theorem mComp_contMDiffOn
    {G : ℝ → SMet I M} {T : ℝ} (hJs : JointSmooth G (Ico 0 T)) (x₀ : M)
    (i j : Fin (Module.finrank ℝ E)) :
    ContMDiffOn (𝓘(ℝ,ℝ).prod I) 𝓘(ℝ,ℝ) ∞
      (fun p : ℝ × M ↦ mComp (I := I) G x₀ i j p.1 p.2)
      (Ico 0 T ×ˢ (chartAt H x₀).source) := by
  intro p hp
  obtain ⟨Y, hY, hYeq⟩ :=
    exists_smooth_section_eventuallyEq_frameSection (I := I) x₀ (cBasis (E := E) i) hp.2
  obtain ⟨Z, hZ, hZeq⟩ :=
    exists_smooth_section_eventuallyEq_frameSection (I := I) x₀ (cBasis (E := E) j) hp.2
  have hmain : ContMDiffWithinAt (𝓘(ℝ,ℝ).prod I) 𝓘(ℝ,ℝ) ∞
      (fun q : ℝ × M ↦ (G q.1).inner q.2 (Y q.2) (Z q.2)) (Ico 0 T ×ˢ univ) p :=
    (Work.Diff.T.metric_pairing_smooth (I := I) (J := Ico 0 T) hJs hY hZ) p
      ⟨hp.1, mem_univ _⟩
  have hev : (fun q : ℝ × M ↦ mComp (I := I) G x₀ i j q.1 q.2)
      =ᶠ[𝓝[Ico 0 T ×ˢ univ] p]
      (fun q : ℝ × M ↦ (G q.1).inner q.2 (Y q.2) (Z q.2)) := by
    have hS : ∀ᶠ q : ℝ × M in 𝓝 p,
        Y q.2 = frameSection (I := I) x₀ (cBasis (E := E) i) q.2 ∧
        Z q.2 = frameSection (I := I) x₀ (cBasis (E := E) j) q.2 :=
      (continuous_snd.tendsto p).eventually (hYeq.and hZeq)
    filter_upwards [hS.filter_mono nhdsWithin_le_nhds] with q hq
    simp only [mComp, cFrame, hq.1, hq.2]
  exact (hmain.congr_of_eventuallyEq_of_mem hev ⟨hp.1, mem_univ _⟩).mono_of_mem_nhdsWithin
    (prod_mem_nhdsWithin_prod x₀ (Ico 0 T) p)

/-! ## Differentiation along the coordinate frame -/

/-- **The coordinate derivative of a jointly smooth family is jointly smooth.**

`dOp x₀ a Φ t y = mvfderiv I (Φ t) y (cFrame x₀ a y)`.  The analytic content is the hypothesis
`hder`; the work here is the reduction of the chart-local coordinate frame to the globally smooth
direction field required by `hder`. -/
theorem dOp_contMDiffOn
    {T : ℝ} (x₀ : M)
    (hder : ∀ {u : ℝ → M → ℝ} {X : Π y : M, TangentSpace I y},
      ContMDiffOn (𝓘(ℝ,ℝ).prod I) 𝓘(ℝ,ℝ) ∞ (fun p : ℝ × M ↦ u p.1 p.2) (Ico 0 T ×ˢ univ) →
      CMDiff ∞ (T% X) →
      ContMDiffOn (𝓘(ℝ,ℝ).prod I) 𝓘(ℝ,ℝ) ∞
        (fun p : ℝ × M ↦ mvfderiv I (u p.1) p.2 (X p.2)) (Ico 0 T ×ˢ univ))
    {Φ : ℝ → M → ℝ}
    (hΦ : ContMDiffOn (𝓘(ℝ,ℝ).prod I) 𝓘(ℝ,ℝ) ∞ (fun p : ℝ × M ↦ Φ p.1 p.2)
      (Ico 0 T ×ˢ (chartAt H x₀).source))
    (a : Fin (Module.finrank ℝ E)) :
    ContMDiffOn (𝓘(ℝ,ℝ).prod I) 𝓘(ℝ,ℝ) ∞
      (fun p : ℝ × M ↦ dOp (I := I) x₀ a Φ p.1 p.2)
      (Ico 0 T ×ˢ (chartAt H x₀).source) := by
  intro p hp
  obtain ⟨t, x⟩ := p
  -- a bump function centred at `x` and supported in the chart, and a global extension of `σ_a`
  obtain ⟨ψ, -, hψts⟩ := (SmoothBumpFunction.nhds_basis_tsupport (I := I) x).mem_iff.mp
    ((chartAt H x₀).open_source.mem_nhds hp.2)
  obtain ⟨Y, hYsm, hYeq⟩ :=
    exists_smooth_section_eventuallyEq_frameSection (I := I) x₀ (cBasis (E := E) a) hp.2
  -- the bump-modified family
  set Φb : ℝ → M → ℝ := fun t y => (ψ : M → ℝ) y * Φ t y with hΦb
  have hΦb_sm : ContMDiffOn (𝓘(ℝ,ℝ).prod I) 𝓘(ℝ,ℝ) ∞ (fun q : ℝ × M ↦ Φb q.1 q.2)
      (Ico 0 T ×ˢ univ) := by
    intro q hq
    by_cases hqx : q.2 ∈ (chartAt H x₀).source
    · have hψglob : ContMDiff (𝓘(ℝ,ℝ).prod I) 𝓘(ℝ,ℝ) ∞
          (fun q : ℝ × M => (ψ : M → ℝ) q.2) :=
        ContMDiff.comp (I := 𝓘(ℝ,ℝ).prod I) (I' := I) (I'' := 𝓘(ℝ,ℝ))
          ψ.contMDiff contMDiff_snd
      have hprod : ContMDiffWithinAt (𝓘(ℝ,ℝ).prod I) 𝓘(ℝ,ℝ) ∞
          (fun q : ℝ × M => (ψ : M → ℝ) q.2 * Φ q.1 q.2)
          (Ico 0 T ×ˢ (chartAt H x₀).source) q :=
        (hψglob q).contMDiffWithinAt.mul (hΦ q ⟨hq.1, hqx⟩)
      exact hprod.mono_of_mem_nhdsWithin (prod_mem_nhdsWithin_prod' x₀ (Ico 0 T) q hqx)
    · have h0 : (ψ : M → ℝ) =ᶠ[𝓝 q.2] 0 :=
        notMem_tsupport_iff_eventuallyEq.mp (fun hc => hqx (hψts hc))
      have hev : (fun q : ℝ × M => Φb q.1 q.2) =ᶠ[𝓝 q] 0 := by
        filter_upwards [(continuous_snd.tendsto q).eventually h0] with q' hq'
        have hq'0 : (ψ : M → ℝ) q'.2 = 0 := by simpa using hq'
        simp only [hΦb, hq'0, zero_mul, Pi.zero_apply, Pi.zero_apply]
      exact (contMDiffWithinAt_const (c := (0 : ℝ))).congr_of_eventuallyEq
        (hev.filter_mono nhdsWithin_le_nhds) (hev.eq_of_nhds)
  -- `hder` applied to the modified family and the global field
  have hdt : ContMDiffOn (𝓘(ℝ,ℝ).prod I) 𝓘(ℝ,ℝ) ∞
      (fun q : ℝ × M ↦ mvfderiv I (Φb q.1) q.2 (Y q.2)) (Ico 0 T ×ˢ univ) :=
    hder hΦb_sm hYsm
  -- the modified derivative agrees with the wanted one near `(t, x)`
  have hfun : (fun q : ℝ × M ↦ mvfderiv I (Φ q.1) q.2 (cFrame (I := I) x₀ a q.2))
      =ᶠ[𝓝 ((t, x) : ℝ × M)]
      (fun q : ℝ × M ↦ mvfderiv I (Φb q.1) q.2 (Y q.2)) := by
    -- the set on which the bump is identically `1` (and hence `Φb = Φ` locally)
    have hU : {y : M | (ψ : M → ℝ) y = 1} ∈ 𝓝 x := ψ.eventuallyEq_one
    have hxU : x ∈ interior {y : M | (ψ : M → ℝ) y = 1} :=
      mem_interior_iff_mem_nhds.mpr hU
    have hUnear : ∀ᶠ q : ℝ × M in 𝓝 ((t, x) : ℝ × M),
        q.2 ∈ interior {y : M | (ψ : M → ℝ) y = 1} :=
      (continuous_snd.tendsto ((t, x) : ℝ × M)).eventually (isOpen_interior.mem_nhds hxU)
    have hYnear : ∀ᶠ q : ℝ × M in 𝓝 ((t, x) : ℝ × M),
        Y q.2 = cFrame (I := I) x₀ a q.2 :=
      (continuous_snd.tendsto ((t, x) : ℝ × M)).eventually
        (show ∀ᶠ y in 𝓝 x, Y y = cFrame (I := I) x₀ a y from hYeq)
    filter_upwards [hUnear, hYnear] with q hqU hqY
    rw [hqY]
    have hsel : Φ q.1 =ᶠ[𝓝 q.2] Φb q.1 := by
      have hψ1 : ∀ᶠ y in 𝓝 q.2, (ψ : M → ℝ) y = 1 :=
        Filter.mem_of_superset (isOpen_interior.mem_nhds hqU) interior_subset
      filter_upwards [hψ1] with y hy
      simp only [hΦb]
      rw [hy, one_mul]
    rw [mvfderiv_congr_germ (I := I) hsel]
  have hgoal : ContMDiffWithinAt (𝓘(ℝ,ℝ).prod I) 𝓘(ℝ,ℝ) ∞
      (fun q : ℝ × M ↦ mvfderiv I (Φ q.1) q.2 (cFrame (I := I) x₀ a q.2))
      (Ico 0 T ×ˢ univ) (t, x) :=
    (hdt (t, x) ⟨hp.1, mem_univ x⟩).congr_of_eventuallyEq
      (hfun.filter_mono nhdsWithin_le_nhds) (hfun.eq_of_nhds)
  exact hgoal.mono_of_mem_nhdsWithin (prod_mem_nhdsWithin_prod x₀ (Ico 0 T) (t, x))

/-! ## The Koszul pairings -/

/-- **Joint smoothness of the Koszul pairings in the coordinate frame.** -/
theorem koszulPair_contMDiffOn
    {G : ℝ → SMet I M} {T : ℝ} (hJs : JointSmooth G (Ico 0 T)) (x₀ : M)
    (hder : ∀ {u : ℝ → M → ℝ} {X : Π y : M, TangentSpace I y},
      ContMDiffOn (𝓘(ℝ,ℝ).prod I) 𝓘(ℝ,ℝ) ∞ (fun p : ℝ × M ↦ u p.1 p.2) (Ico 0 T ×ˢ univ) →
      CMDiff ∞ (T% X) →
      ContMDiffOn (𝓘(ℝ,ℝ).prod I) 𝓘(ℝ,ℝ) ∞
        (fun p : ℝ × M ↦ mvfderiv I (u p.1) p.2 (X p.2)) (Ico 0 T ×ˢ univ))
    (a b c : Fin (Module.finrank ℝ E)) :
    ContMDiffOn (𝓘(ℝ,ℝ).prod I) 𝓘(ℝ,ℝ) ∞
      (fun p : ℝ × M ↦ koszulPair (I := I) G x₀ a b c p.1 p.2)
      (Ico 0 T ×ˢ (chartAt H x₀).source) := by
  intro p hp
  have h1 : ContMDiffWithinAt (𝓘(ℝ,ℝ).prod I) 𝓘(ℝ,ℝ) ∞
      (fun q : ℝ × M ↦ dOp (I := I) x₀ a (mComp (I := I) G x₀ b c) q.1 q.2)
      (Ico 0 T ×ˢ (chartAt H x₀).source) p :=
    dOp_contMDiffOn (I := I) x₀ hder (mComp_contMDiffOn (I := I) hJs x₀ b c) a p hp
  have h2 : ContMDiffWithinAt (𝓘(ℝ,ℝ).prod I) 𝓘(ℝ,ℝ) ∞
      (fun q : ℝ × M ↦ dOp (I := I) x₀ b (mComp (I := I) G x₀ c a) q.1 q.2)
      (Ico 0 T ×ˢ (chartAt H x₀).source) p :=
    dOp_contMDiffOn (I := I) x₀ hder (mComp_contMDiffOn (I := I) hJs x₀ c a) b p hp
  have h3 : ContMDiffWithinAt (𝓘(ℝ,ℝ).prod I) 𝓘(ℝ,ℝ) ∞
      (fun q : ℝ × M ↦ dOp (I := I) x₀ c (mComp (I := I) G x₀ a b) q.1 q.2)
      (Ico 0 T ×ˢ (chartAt H x₀).source) p :=
    dOp_contMDiffOn (I := I) x₀ hder (mComp_contMDiffOn (I := I) hJs x₀ a b) c p hp
  have hexp : ContMDiffWithinAt (𝓘(ℝ,ℝ).prod I) 𝓘(ℝ,ℝ) ∞
      ((fun _ : ℝ × M => (1 / 2 : ℝ)) *
        (fun q : ℝ × M => dOp (I := I) x₀ a (mComp (I := I) G x₀ b c) q.1 q.2
          + dOp (I := I) x₀ b (mComp (I := I) G x₀ c a) q.1 q.2
          - dOp (I := I) x₀ c (mComp (I := I) G x₀ a b) q.1 q.2))
      (Ico 0 T ×ˢ (chartAt H x₀).source) p :=
    contMDiffWithinAt_const.mul ((h1.add h2).sub h3)
  refine hexp.congr_of_mem (fun q _ => ?_) hp
  simp only [koszulPair, dOp, mComp_eq, Pi.mul_apply]

/-! ## The inverse Gram matrix -/

/-- **Joint smoothness of the entries of the inverse Gram matrix.** -/
theorem gramInv_contMDiffOn
    {G : ℝ → SMet I M} {T : ℝ} (hJs : JointSmooth G (Ico 0 T)) (x₀ : M)
    (k m : Fin (Module.finrank ℝ E)) :
    ContMDiffOn (𝓘(ℝ,ℝ).prod I) 𝓘(ℝ,ℝ) ∞
      (fun p : ℝ × M ↦ GramInv (I := I) G x₀ p.1 p.2 k m)
      (Ico 0 T ×ˢ (chartAt H x₀).source) := by
  intro p hp
  have hdet : (Matrix.of (fun i j => GramM (I := I) G x₀ p.1 p.2 i j)).det ≠ 0 := by
    letI : RiemannianBundle (fun y : M ↦ TangentSpace I y) := ⟨(G p.1).toRiemannianMetric⟩
    haveI : IsContMDiffRiemannianBundle I ∞ E (fun y : M ↦ TangentSpace I y) := inferInstance
    have hnd : (CGramInv.gramBil (I := I) G x₀ p.2 p.1).Nondegenerate :=
      CGramInv.gramBil_nondegenerate (I := I) G x₀ hp.2 p.1
    have h := (LinearMap.BilinForm.nondegenerate_iff_det_ne_zero (cBasis (E := E))).mp hnd
    rwa [← CGramInv.GramM_eq_toMatrix (I := I) G x₀ p.2 p.1] at h
  have hMx : ContMDiffWithinAt (𝓘(ℝ,ℝ).prod I)
      𝓘(ℝ,Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) → ℝ) ∞
      (fun q : ℝ × M => fun i j => GramM (I := I) G x₀ q.1 q.2 i j)
      (Ico 0 T ×ˢ (chartAt H x₀).source) p := by
    rw [contMDiffWithinAt_pi_space]
    intro i
    rw [contMDiffWithinAt_pi_space]
    intro j
    exact mComp_contMDiffOn (I := I) hJs x₀ i j p hp
  have hinv := Work.Diff.EXT.contDiffAt_matrix_inv_pi
    (M := fun i j => GramM (I := I) G x₀ p.1 p.2 i j) hdet
  have hcomp := ContDiffWithinAt.comp_contMDiffWithinAt
    (s := Ico 0 T ×ˢ (chartAt H x₀).source) (t := univ)
    hinv.contDiffWithinAt hMx (fun q _ => mem_univ _)
  have h1 := (contMDiffWithinAt_pi_space.mp hcomp) k
  have h2 := (contMDiffWithinAt_pi_space.mp h1) m
  refine h2.congr_of_mem (fun q _ => ?_) hp
  rfl

/-! ## The Christoffel symbols -/

/-- **Joint smoothness of the Christoffel symbols in the coordinate frame.** -/
theorem chrCoord_contMDiffOn
    {G : ℝ → SMet I M} {T : ℝ} (hJs : JointSmooth G (Ico 0 T)) (x₀ : M)
    (hder : ∀ {u : ℝ → M → ℝ} {X : Π y : M, TangentSpace I y},
      ContMDiffOn (𝓘(ℝ,ℝ).prod I) 𝓘(ℝ,ℝ) ∞ (fun p : ℝ × M ↦ u p.1 p.2) (Ico 0 T ×ˢ univ) →
      CMDiff ∞ (T% X) →
      ContMDiffOn (𝓘(ℝ,ℝ).prod I) 𝓘(ℝ,ℝ) ∞
        (fun p : ℝ × M ↦ mvfderiv I (u p.1) p.2 (X p.2)) (Ico 0 T ×ˢ univ))
    (n a b : Fin (Module.finrank ℝ E)) :
    ContMDiffOn (𝓘(ℝ,ℝ).prod I) 𝓘(ℝ,ℝ) ∞
      (fun p : ℝ × M ↦ chrCoord (I := I) G x₀ n a b p.1 p.2)
      (Ico 0 T ×ˢ (chartAt H x₀).source) := by
  intro p hp
  have hsum : ContMDiffWithinAt (𝓘(ℝ,ℝ).prod I) 𝓘(ℝ,ℝ) ∞
      (fun q : ℝ × M => ∑ i : Fin (Module.finrank ℝ E),
        GramInv (I := I) G x₀ q.1 q.2 n i * koszulPair (I := I) G x₀ a b i q.1 q.2)
      (Ico 0 T ×ˢ (chartAt H x₀).source) p := by
    refine ContMDiffWithinAt.sum (t := Finset.univ) (fun i _ => ?_)
    exact (gramInv_contMDiffOn (I := I) hJs x₀ n i p hp).mul
      (koszulPair_contMDiffOn (I := I) hJs x₀ hder a b i p hp)
  refine hsum.congr_of_mem (fun q _ => ?_) hp
  rfl

/-! ## The chart expression for `Rm` -/

/-- **Joint smoothness of the chart expression for the curvature components.** -/
theorem rmChartExpr_contMDiffOn
    {G : ℝ → SMet I M} {T : ℝ} (hJs : JointSmooth G (Ico 0 T)) (x₀ : M)
    (hder : ∀ {u : ℝ → M → ℝ} {X : Π y : M, TangentSpace I y},
      ContMDiffOn (𝓘(ℝ,ℝ).prod I) 𝓘(ℝ,ℝ) ∞ (fun p : ℝ × M ↦ u p.1 p.2) (Ico 0 T ×ˢ univ) →
      CMDiff ∞ (T% X) →
      ContMDiffOn (𝓘(ℝ,ℝ).prod I) 𝓘(ℝ,ℝ) ∞
        (fun p : ℝ × M ↦ mvfderiv I (u p.1) p.2 (X p.2)) (Ico 0 T ×ˢ univ))
    (i j k l : Fin (Module.finrank ℝ E)) :
    ContMDiffOn (𝓘(ℝ,ℝ).prod I) 𝓘(ℝ,ℝ) ∞
      (fun p : ℝ × M ↦ rmChartExpr (I := I) G x₀ i j k l p.1 p.2)
      (Ico 0 T ×ˢ (chartAt H x₀).source) := by
  intro p hp
  have h1 : ContMDiffWithinAt (𝓘(ℝ,ℝ).prod I) 𝓘(ℝ,ℝ) ∞
      (fun q : ℝ × M ↦ dOp (I := I) x₀ i (koszulPair (I := I) G x₀ j l k) q.1 q.2)
      (Ico 0 T ×ˢ (chartAt H x₀).source) p :=
    dOp_contMDiffOn (I := I) x₀ hder (koszulPair_contMDiffOn (I := I) hJs x₀ hder j l k) i p hp
  have h2 : ContMDiffWithinAt (𝓘(ℝ,ℝ).prod I) 𝓘(ℝ,ℝ) ∞
      (fun q : ℝ × M => ∑ m : Fin (Module.finrank ℝ E),
        ∑ n : Fin (Module.finrank ℝ E),
          GramInv (I := I) G x₀ q.1 q.2 m n * koszulPair (I := I) G x₀ j l m q.1 q.2
            * koszulPair (I := I) G x₀ i k n q.1 q.2)
      (Ico 0 T ×ˢ (chartAt H x₀).source) p := by
    refine ContMDiffWithinAt.sum (t := Finset.univ) (fun m _ => ?_)
    refine ContMDiffWithinAt.sum (t := Finset.univ) (fun n _ => ?_)
    exact ((gramInv_contMDiffOn (I := I) hJs x₀ m n p hp).mul
      (koszulPair_contMDiffOn (I := I) hJs x₀ hder j l m p hp)).mul
      (koszulPair_contMDiffOn (I := I) hJs x₀ hder i k n p hp)
  have h3 : ContMDiffWithinAt (𝓘(ℝ,ℝ).prod I) 𝓘(ℝ,ℝ) ∞
      (fun q : ℝ × M ↦ dOp (I := I) x₀ j (koszulPair (I := I) G x₀ i l k) q.1 q.2)
      (Ico 0 T ×ˢ (chartAt H x₀).source) p :=
    dOp_contMDiffOn (I := I) x₀ hder (koszulPair_contMDiffOn (I := I) hJs x₀ hder i l k) j p hp
  have h4 : ContMDiffWithinAt (𝓘(ℝ,ℝ).prod I) 𝓘(ℝ,ℝ) ∞
      (fun q : ℝ × M => ∑ m : Fin (Module.finrank ℝ E),
        ∑ n : Fin (Module.finrank ℝ E),
          GramInv (I := I) G x₀ q.1 q.2 m n * koszulPair (I := I) G x₀ i l m q.1 q.2
            * koszulPair (I := I) G x₀ j k n q.1 q.2)
      (Ico 0 T ×ˢ (chartAt H x₀).source) p := by
    refine ContMDiffWithinAt.sum (t := Finset.univ) (fun m _ => ?_)
    refine ContMDiffWithinAt.sum (t := Finset.univ) (fun n _ => ?_)
    exact ((gramInv_contMDiffOn (I := I) hJs x₀ m n p hp).mul
      (koszulPair_contMDiffOn (I := I) hJs x₀ hder i l m p hp)).mul
      (koszulPair_contMDiffOn (I := I) hJs x₀ hder j k n p hp)
  refine (((h1.sub h2).sub h3).add h4).congr_of_mem (fun q _ => ?_) hp
  simp only [rmChartExpr, Pi.add_apply]

/-! ## The chart expression for `∇Rm` -/

/-- **Joint smoothness of the chart expression for the `∇Rm` components.** -/
theorem covRmChartExpr_contMDiffOn
    {G : ℝ → SMet I M} {T : ℝ} (hJs : JointSmooth G (Ico 0 T)) (x₀ : M)
    (hder : ∀ {u : ℝ → M → ℝ} {X : Π y : M, TangentSpace I y},
      ContMDiffOn (𝓘(ℝ,ℝ).prod I) 𝓘(ℝ,ℝ) ∞ (fun p : ℝ × M ↦ u p.1 p.2) (Ico 0 T ×ˢ univ) →
      CMDiff ∞ (T% X) →
      ContMDiffOn (𝓘(ℝ,ℝ).prod I) 𝓘(ℝ,ℝ) ∞
        (fun p : ℝ × M ↦ mvfderiv I (u p.1) p.2 (X p.2)) (Ico 0 T ×ˢ univ))
    (m i j k l : Fin (Module.finrank ℝ E)) :
    ContMDiffOn (𝓘(ℝ,ℝ).prod I) 𝓘(ℝ,ℝ) ∞
      (fun p : ℝ × M ↦ covRmChartExpr (I := I) G x₀ m i j k l p.1 p.2)
      (Ico 0 T ×ˢ (chartAt H x₀).source) := by
  intro p hp
  have h1 : ContMDiffWithinAt (𝓘(ℝ,ℝ).prod I) 𝓘(ℝ,ℝ) ∞
      (fun q : ℝ × M ↦ dOp (I := I) x₀ m (rmChartExpr (I := I) G x₀ i j k l) q.1 q.2)
      (Ico 0 T ×ˢ (chartAt H x₀).source) p :=
    dOp_contMDiffOn (I := I) x₀ hder
      (rmChartExpr_contMDiffOn (I := I) hJs x₀ hder i j k l) m p hp
  have h2 : ContMDiffWithinAt (𝓘(ℝ,ℝ).prod I) 𝓘(ℝ,ℝ) ∞
      (fun q : ℝ × M => ∑ n : Fin (Module.finrank ℝ E),
        chrCoord (I := I) G x₀ n m i q.1 q.2 * rmChartExpr (I := I) G x₀ n j k l q.1 q.2)
      (Ico 0 T ×ˢ (chartAt H x₀).source) p := by
    refine ContMDiffWithinAt.sum (t := Finset.univ) (fun n _ => ?_)
    exact (chrCoord_contMDiffOn (I := I) hJs x₀ hder n m i p hp).mul
      (rmChartExpr_contMDiffOn (I := I) hJs x₀ hder n j k l p hp)
  have h3 : ContMDiffWithinAt (𝓘(ℝ,ℝ).prod I) 𝓘(ℝ,ℝ) ∞
      (fun q : ℝ × M => ∑ n : Fin (Module.finrank ℝ E),
        chrCoord (I := I) G x₀ n m j q.1 q.2 * rmChartExpr (I := I) G x₀ i n k l q.1 q.2)
      (Ico 0 T ×ˢ (chartAt H x₀).source) p := by
    refine ContMDiffWithinAt.sum (t := Finset.univ) (fun n _ => ?_)
    exact (chrCoord_contMDiffOn (I := I) hJs x₀ hder n m j p hp).mul
      (rmChartExpr_contMDiffOn (I := I) hJs x₀ hder i n k l p hp)
  have h4 : ContMDiffWithinAt (𝓘(ℝ,ℝ).prod I) 𝓘(ℝ,ℝ) ∞
      (fun q : ℝ × M => ∑ n : Fin (Module.finrank ℝ E),
        chrCoord (I := I) G x₀ n m k q.1 q.2 * rmChartExpr (I := I) G x₀ i j n l q.1 q.2)
      (Ico 0 T ×ˢ (chartAt H x₀).source) p := by
    refine ContMDiffWithinAt.sum (t := Finset.univ) (fun n _ => ?_)
    exact (chrCoord_contMDiffOn (I := I) hJs x₀ hder n m k p hp).mul
      (rmChartExpr_contMDiffOn (I := I) hJs x₀ hder i j n l p hp)
  have h5 : ContMDiffWithinAt (𝓘(ℝ,ℝ).prod I) 𝓘(ℝ,ℝ) ∞
      (fun q : ℝ × M => ∑ n : Fin (Module.finrank ℝ E),
        chrCoord (I := I) G x₀ n m l q.1 q.2 * rmChartExpr (I := I) G x₀ i j k n q.1 q.2)
      (Ico 0 T ×ˢ (chartAt H x₀).source) p := by
    refine ContMDiffWithinAt.sum (t := Finset.univ) (fun n _ => ?_)
    exact (chrCoord_contMDiffOn (I := I) hJs x₀ hder n m l p hp).mul
      (rmChartExpr_contMDiffOn (I := I) hJs x₀ hder i j k n p hp)
  refine ((((h1.sub h2).sub h3).sub h4).sub h5).congr_of_mem (fun q _ => ?_) hp
  simp only [covRmChartExpr]

/-! ## The requested statement -/

theorem covRmChartExpr_joint_smooth
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M] [IsManifold I ∞ M]
    [I.Boundaryless] [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    {G : ℝ → SMet I M} {T : ℝ} (hJs : JointSmooth G (Ico 0 T)) (x₀ : M)
    (hder : ∀ {u : ℝ → M → ℝ} {X : Π y : M, TangentSpace I y},
      ContMDiffOn (𝓘(ℝ,ℝ).prod I) 𝓘(ℝ,ℝ) ∞ (fun p : ℝ × M ↦ u p.1 p.2) (Ico 0 T ×ˢ univ) →
      CMDiff ∞ (T% X) →
      ContMDiffOn (𝓘(ℝ,ℝ).prod I) 𝓘(ℝ,ℝ) ∞
        (fun p : ℝ × M ↦ mvfderiv I (u p.1) p.2 (X p.2)) (Ico 0 T ×ˢ univ))
    (m i j k l : Fin (Module.finrank ℝ E)) :
    ContMDiffOn (𝓘(ℝ,ℝ).prod I) 𝓘(ℝ,ℝ) ∞
      (fun p : ℝ × M ↦ covRmChartExpr (I := I) G x₀ m i j k l p.1 p.2)
      (Ico 0 T ×ˢ (chartAt H x₀).source) :=
  covRmChartExpr_contMDiffOn (I := I) hJs x₀ hder m i j k l

end

end Work.Diff.GE
