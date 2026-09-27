import Mathlib
import Submission.Work.Noncompact.CompressionTube.Notation
import Submission.Work.Noncompact.CompressionTube.exists_straightened_chart_twoSided
import Submission.Work.Noncompact.CompressionTube.isLocalDiffeomorph_of_immersion
import Submission.Work.Routing.injOn_nhds_of_compact_of_locallyInjOn

namespace Work.Routing

set_option linter.style.haveILetI false
set_option linter.unusedVariables false

open scoped Manifold ContDiff Topology
open Set Function
open Work.Noncompact.CompressionTube

noncomputable section

set_option backward.isDefEq.respectTransparency false in
/-- **The inverse function theorem at a point, for a map into the model space.**

If `Φ : M → ℝⁿ` is `C^∞` at `x` and its manifold derivative at `x` is injective (the dimensions
agree since both sides are modelled on `ℝⁿ`), then `Φ` is injective on an open neighbourhood
of `x`.

This is the local-injectivity input of `Work.Routing.injectiveOn_nhds_of_injective_arc`.  The
tangent map is invertible (an injective endomorphism of the finite dimensional `ℝⁿ`), so in a
chart at `x` the coordinate expression `g = Φ ∘ c.symm` has an invertible derivative; the inverse
function theorem in normed spaces (`ContDiffAt.toOpenPartialHomeomorph`) makes `g` a local
homeomorphism there, and `Φ = g ∘ c` is then injective on a neighbourhood of `x`. -/
theorem exists_isOpen_injOn_of_contMDiffAt_of_injective_mfderiv {n : ℕ} {M : Type*}
    [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (MC n) smoothOrder M]
    {Φ : M → EuclideanSpace ℝ (Fin n)} {x : M}
    (hsm : ContMDiffAt (MC n) (MC n) smoothOrder Φ x)
    (himm : Function.Injective (mfderiv (MC n) (MC n) Φ x)) :
    ∃ U : Set M, IsOpen U ∧ x ∈ U ∧ Set.InjOn Φ U := by
  classical
  have hn : smoothOrder ≠ (0 : WithTop ℕ∞) := by simp [smoothOrder]
  -- a chart at `x`
  set c : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n)) :=
    chartAt (EuclideanSpace ℝ (Fin n)) x with hcdef
  have hcmax : c ∈ IsManifold.maximalAtlas (MC n) smoothOrder M :=
    IsManifold.chart_mem_maximalAtlas x
  have hxsrc : x ∈ c.source := mem_chart_source _ x
  have hxtgt : c x ∈ c.target := c.map_source hxsrc
  have hcsx : c.symm (c x) = x := c.left_inv hxsrc
  -- the chart inverse is smooth near `c x`
  have hsymm_on : ContMDiffOn (MC n) (MC n) smoothOrder (↑c.symm) c.target :=
    contMDiffOn_symm_of_mem_maximalAtlas hcmax
  have hsymm_within : ContMDiffWithinAt (MC n) (MC n) smoothOrder (↑c.symm) c.target (c x) :=
    hsymm_on (c x) hxtgt
  have hsymm_at : ContMDiffAt (MC n) (MC n) smoothOrder (↑c.symm) (c x) :=
    hsymm_within.contMDiffAt (c.open_target.mem_nhds hxtgt)
  -- the coordinate expression of `Φ`
  set g : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) := fun z => Φ (c.symm z) with hgdef
  have hsm' : ContMDiffAt (MC n) (MC n) smoothOrder Φ (c.symm (c x)) := by rw [hcsx]; exact hsm
  have hg_within : ContMDiffWithinAt (MC n) (MC n) smoothOrder g c.target (c x) := by
    have h := hsm'.comp_contMDiffWithinAt (c x) hsymm_within
    simpa only [g, Function.comp_def] using h
  have hg_at : ContMDiffAt (MC n) (MC n) smoothOrder g (c x) :=
    hg_within.contMDiffAt (c.open_target.mem_nhds hxtgt)
  have hg_cd : ContDiffAt ℝ smoothOrder g (c x) := hg_at.contDiffAt
  -- differentiability of the pieces
  have hc_at : ContMDiffAt (MC n) (MC n) smoothOrder (↑c) x :=
    (contMDiffOn_of_mem_maximalAtlas hcmax).contMDiffAt (c.open_source.mem_nhds hxsrc)
  have hc_md : MDifferentiableAt (MC n) (MC n) (↑c) (c.symm (c x)) := by
    rw [hcsx]; exact hc_at.mdifferentiableAt hn
  have hsymm_md : MDifferentiableAt (MC n) (MC n) (↑c.symm) (c x) := hsymm_at.mdifferentiableAt hn
  have hΦ_md : MDifferentiableAt (MC n) (MC n) Φ (c.symm (c x)) := by
    rw [hcsx]; exact hsm.mdifferentiableAt hn
  have hΦ_md_inj : Function.Injective (mfderiv (MC n) (MC n) Φ (c.symm (c x))) := by
    rw [hcsx]; exact himm
  -- the chain rule at `c x`
  have hchain : mfderiv (MC n) (MC n) g (c x)
      = (mfderiv (MC n) (MC n) Φ (c.symm (c x))).comp (mfderiv (MC n) (MC n) (↑c.symm) (c x)) := by
    have h := mfderiv_comp (I := MC n) (I' := MC n) (I'' := MC n)
      (f := (↑c.symm)) (g := Φ) (c x) hΦ_md hsymm_md
    simpa only [g, Function.comp_def] using h
  -- the differential of the chart inverse is injective: `(d c) ∘ (d c⁻¹) = id`
  have hcomp_id : ((mfderiv (MC n) (MC n) (↑c) (c.symm (c x))).comp
        (mfderiv (MC n) (MC n) (↑c.symm) (c x)) :
        EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
      = ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin n)) := by
    have heq : (↑c ∘ ↑c.symm) =ᶠ[𝓝 (c x)]
        (id : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) := by
      filter_upwards [c.open_target.mem_nhds hxtgt] with z hz
      exact c.right_inv hz
    have h2 : ((mfderiv (MC n) (MC n) (↑c ∘ ↑c.symm) (c x)) :
        EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
        = ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin n)) := by
      rw [heq.mfderiv_eq, mfderiv_id]
      rfl
    have h3 := mfderiv_comp (I := MC n) (I' := MC n) (I'' := MC n)
      (f := (↑c.symm)) (g := (↑c)) (c x) hc_md hsymm_md
    rw [h3] at h2
    exact h2
  have hcs_inj : Function.Injective (mfderiv (MC n) (MC n) (↑c.symm) (c x)) := by
    have h2 : ∀ v : EuclideanSpace ℝ (Fin n),
        (mfderiv (MC n) (MC n) (↑c) (c.symm (c x)))
          ((mfderiv (MC n) (MC n) (↑c.symm) (c x)) v) = v := by
      intro v
      have hv : ((mfderiv (MC n) (MC n) (↑c) (c.symm (c x))).comp
            (mfderiv (MC n) (MC n) (↑c.symm) (c x)) :
            EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) v = v := by
        rw [hcomp_id]
        rfl
      exact hv
    intro v w hvw
    calc v = (mfderiv (MC n) (MC n) (↑c) (c.symm (c x)))
          ((mfderiv (MC n) (MC n) (↑c.symm) (c x)) v) := (h2 v).symm
      _ = (mfderiv (MC n) (MC n) (↑c) (c.symm (c x)))
          ((mfderiv (MC n) (MC n) (↑c.symm) (c x)) w) := by rw [hvw]
      _ = w := h2 w
  -- hence the differential of the coordinate expression is injective
  have hcomp_inj : Function.Injective ((mfderiv (MC n) (MC n) Φ (c.symm (c x))).comp
      (mfderiv (MC n) (MC n) (↑c.symm) (c x))) := by
    intro v w hvw
    exact hcs_inj (hΦ_md_inj hvw)
  have hmfd_inj : Function.Injective (mfderiv (MC n) (MC n) g (c x)) := by
    rw [hchain]
    exact hcomp_inj
  have hfd_inj : Function.Injective (fderiv ℝ g (c x)) := by
    rw [← mfderiv_eq_fderiv (f := g) (x := c x)]
    exact hmfd_inj
  -- the inverse function theorem
  obtain ⟨L, hL⟩ := Work.Noncompact.CompressionTube.exists_continuousLinearEquiv_of_injective
    (E := EuclideanSpace ℝ (Fin n)) (E' := EuclideanSpace ℝ (Fin n)) rfl (fderiv ℝ g (c x)) hfd_inj
  have hFx : HasFDerivAt g (L : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) (c x) :=
    HasFDerivAt.congr_fderiv ((hg_cd.differentiableAt hn).hasFDerivAt) hL.symm
  let Ψ : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin n)) (EuclideanSpace ℝ (Fin n)) :=
    ContDiffAt.toOpenPartialHomeomorph g hg_cd hFx hn
  have hxcΨ : c x ∈ Ψ.source := ContDiffAt.mem_toOpenPartialHomeomorph_source hg_cd hFx hn
  have hΨcoe : (Ψ : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) = g :=
    ContDiffAt.toOpenPartialHomeomorph_coe hg_cd hFx hn
  refine ⟨c.symm '' (Ψ.source ∩ c.target), ?_, ?_, ?_⟩
  · exact c.isOpen_image_symm_of_subset_target (Ψ.open_source.inter c.open_target) inter_subset_right
  · exact ⟨c x, ⟨hxcΨ, hxtgt⟩, c.left_inv hxsrc⟩
  · -- on this neighbourhood `Φ = g ∘ c` with both factors injective
    rintro y ⟨u, hu, rfl⟩ y' ⟨u', hu', rfl⟩ hyy'
    have h2 : Ψ u = Ψ u' := by
      rw [congrFun hΨcoe u, congrFun hΨcoe u']
      exact hyy'
    have h3 : u = u' := Ψ.injOn hu.1 hu'.1 h2
    rw [h3]

/-- **A locally invertible map that is injective along a compact embedded arc is injective near it.**

The shared core of the tube chapter (`NOTES_SESSION_endgame_and_crux.md` §16): both
`Routing/exists_chart_of_arc` and `Routing/chartBallPair_of_open_preconnected` reduce to this once the
proved local tube `Work.Noncompact.CompressionTube.exists_straightened_chart_twoSided` has been pieced
into `Φ` with a partition of unity.  The hypotheses are exactly what that construction delivers:

* `Φ` is smooth with invertible differential at every point of the arc — so a local diffeomorphism
  there (the workspace turns immersions into local diffeomorphisms; Mathlib has the inverse function
  theorem);
* `Φ ∘ γ` is injective on `Icc 0 1`, which the straightened windows give for free: there
  `Φ (γ t) = Φ (γ t₀) + (t - t₀) • w` with `w ≠ 0`.

Honest compactness/EPS proof: if `xₙ ≠ yₙ` with `Φ xₙ = Φ yₙ` approach the arc, extract convergent
subsequences `xₙ → γ s`, `yₙ → γ t` (`s, t ∈ Icc 0 1`); then `Φ (γ s) = Φ (γ t)`, so `s = t` by `hγΦ`;
near `γ s` the map is a local diffeomorphism, hence injective on a neighbourhood, contradicting
`xₙ ≠ yₙ` for large `n`; the radius is made uniform by compactness of `γ '' Icc`.
`Set.InjOn Φ T` for this open `T` is exactly what turns `c := Φ⁻¹` into an `OpenPartialHomeomorph` on
`T`, i.e. the remaining obligation of `exists_chart_of_arc`.

Reviewers' notes for the prover (both reviewers: TRUE as stated): `hγinj` is redundant (`hγΦ` forces
it); there is no metric instance among the hypotheses — only `T2Space` — so the sequential argument
must be run inside a compact coordinate neighbourhood of the arc (finitely many chart domains, whose
union is second-countable and hence metrizable, or directly through charts), budget for that; and the
imported `isLocalDiffeomorph_of_immersion` is stated for a *model-space* source, so the
`M → EuclideanSpace` local-injectivity step must go through a chart (conjugate and apply the
normed-space inverse function theorem, e.g. `ContDiffAt.toOpenPartialHomeomorph`). -/
theorem injectiveOn_nhds_of_injective_arc {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (Work.Noncompact.CompressionTube.MC n)
      Work.Noncompact.CompressionTube.smoothOrder M] [T2Space M]
    {γ : ℝ → M} (hγc : Continuous γ) (hγinj : Set.InjOn γ (Set.Icc (0:ℝ) 1))
    {Φ : M → EuclideanSpace ℝ (Fin n)}
    (hΦsm : ∀ x ∈ γ '' Set.Icc (0:ℝ) 1,
      ContMDiffAt (Work.Noncompact.CompressionTube.MC n)
        (Work.Noncompact.CompressionTube.MC n)
        Work.Noncompact.CompressionTube.smoothOrder Φ x)
    (hΦimm : ∀ x ∈ γ '' Set.Icc (0:ℝ) 1, Function.Injective
      (mfderiv (Work.Noncompact.CompressionTube.MC n)
        (Work.Noncompact.CompressionTube.MC n) Φ x))
    (hγΦ : Set.InjOn (fun t : ℝ => Φ (γ t)) (Set.Icc (0:ℝ) 1)) :
    ∃ T : Set M, IsOpen T ∧ γ '' Set.Icc (0:ℝ) 1 ⊆ T ∧ Set.InjOn Φ T := by
  -- the arc is compact, and a charted space over a locally compact model is locally compact
  haveI : LocallyCompactSpace M :=
    ChartedSpace.locallyCompactSpace (EuclideanSpace ℝ (Fin n)) M
  have hKc : IsCompact (γ '' Set.Icc (0:ℝ) 1) := isCompact_Icc.image hγc
  -- `Φ` is locally injective at each point of the arc (inverse function theorem)
  have hloc : ∀ x ∈ γ '' Set.Icc (0:ℝ) 1,
      ∃ U : Set M, IsOpen U ∧ x ∈ U ∧ Set.InjOn Φ U :=
    fun x hx => exists_isOpen_injOn_of_contMDiffAt_of_injective_mfderiv (hΦsm x hx) (hΦimm x hx)
  have hcont : ∀ x ∈ γ '' Set.Icc (0:ℝ) 1, ContinuousAt Φ x :=
    fun x hx => (hΦsm x hx).continuousAt
  -- and injective on the arc, by hypothesis
  have hKinj : Set.InjOn Φ (γ '' Set.Icc (0:ℝ) 1) := by
    rintro x ⟨s, hs, rfl⟩ y ⟨t, ht, rfl⟩ hxy
    rw [hγΦ hs ht hxy]
  -- the topological compactness argument
  exact injOn_nhds_of_compact_of_locallyInjOn hKc hloc hcont hKinj

end

end Work.Routing
