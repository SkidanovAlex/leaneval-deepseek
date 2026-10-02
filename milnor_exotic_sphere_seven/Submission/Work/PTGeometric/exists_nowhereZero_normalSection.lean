import Mathlib
import Submission.Work.Tubular.Transversality
import Submission.Work.Tubular.Gauss
import Submission.Work.Tubular.NormalFrame

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000

/-!
# A nowhere-zero smooth normal section of a high-codimension embedding

For an embedding `E : V ↪ ℝ^{8+k}` of a compact smooth `8`-manifold with codimension `k > 8 = dim V`
there is a `C^∞` section `s` of the normal bundle (`s x ∈ ν_x = T_x^⊥`) that never vanishes.

The construction is: pick a vector `w` that is not tangent at any point
(`Work.PTGeometric.exists_notMem_tangentSpace_aux`, a dimension count: the union of the tangent
spaces is covered by finitely many images of `C^∞` maps from the `16`-dimensional space
`ℝ^8 × ℝ^8`, and `8 + k ≥ 17 > 16`), and set

  `s x := (d (normalCoord E C))_{e x} w`,

where `normalCoord E C` is the normal coordinate of a tube chart of the embedding
(`Work.Tubular.normalCoord`).  Its derivative at a point of the zero section is the orthogonal
projection onto the normal space `ν_x` along `T_x`:

* it kills `T_x`: the normal coordinate vanishes on a neighbourhood of the image of `E`
  (`normalCoord_eq_zero_iff`), so its derivative kills the tangent space (chain rule);
* it is the identity on `ν_x`: along the curve `t ↦ e x + t v` with `v ∈ ν_x` the normal coordinate
  is `t ↦ t v` (`exists_normalCoord_eq` / `normalCoord_tubeMap`).

Hence `s x` is the component of `w` in `ν_x = (T_x)^⊥`, which is nonzero exactly when `w ∉ T_x`.

Everything is unconditional: `Work.Tubular.hasTubularNeighbourhood` is a theorem of this workspace.
-/

open scoped Manifold ContDiff Topology NNReal ENNReal
open Function Filter

namespace Work.PTGeometric

noncomputable section

open Work.Tubular

variable {V : Work.ThomBordism.Man8} {k : ℕ}
  {E : Work.ThomBordism.PontryaginThom.EmbeddingData V (8 + k)} {ε : ℝ}

/-- **The derivative of the normal coordinate at a point of the zero section kills the tangent
space.**  The normal coordinate vanishes on a neighbourhood of the image of `E`, so its derivative
at `E.e x` is zero on the range of the derivative of `E.e`, i.e. on `T_x`. -/
theorem fderiv_normalCoord_apply_of_mem_tangentSpace (C : TubeChart E ε) (x : V.pt)
    {v : Euc (8 + k)} (hv : v ∈ tangentSpace E x) :
    fderiv ℝ (normalCoord E C) (E.e x) v = 0 := by
  have hzero : (fun x' : V.pt => normalCoord E C (E.e x')) =
      fun _ => (0 : Euc (8 + k)) := by
    funext x'
    rw [← tubeMap_zeroSection E x']
    exact normalCoord_tubeMap E C _ (by simpa using C.eps_pos)
  have hEsmooth' : MDifferentiableAt (𝓡 8) (𝓘(ℝ, Euc (8 + k))) E.e x :=
    E.smooth.mdifferentiableAt (x := x) (by simp)
  have hEsmooth := hEsmooth'.hasMFDerivAt
  have hg : HasMFDerivAt (𝓘(ℝ, Euc (8 + k))) (𝓘(ℝ, Euc (8 + k)))
      (normalCoord E C) (E.e x) (fderiv ℝ (normalCoord E C) (E.e x)) := by
    have h : ContDiffAt ℝ ∞ (normalCoord E C) (E.e x) :=
      ((contMDiffOn_normalCoord E C).contMDiffAt
        (C.openTube_isOpen.mem_nhds (C.mem_openTube x))).contDiffAt
    exact (h.differentiableAt (by simp)).hasFDerivAt.hasMFDerivAt
  have hcomp := HasMFDerivAt.comp (I := 𝓡 8) (I' := 𝓘(ℝ, Euc (8 + k)))
    (I'' := 𝓘(ℝ, Euc (8 + k))) x hg hEsmooth
  have hL : (fderiv ℝ (normalCoord E C) (E.e x)).comp
      (mfderiv (𝓡 8) (𝓘(ℝ, Euc (8 + k))) E.e x) = 0 := by
    rw [← hcomp.mfderiv]
    rw [show (normalCoord E C ∘ E.e) = (fun _ : V.pt => (0 : Euc (8 + k))) from hzero]
    exact mfderiv_const
  rw [tangentSpace, LinearMap.mem_range] at hv
  obtain ⟨u, rfl⟩ := hv
  change ((fderiv ℝ (normalCoord E C) (E.e x)).comp
    (mfderiv (𝓡 8) (𝓘(ℝ, Euc (8 + k))) E.e x)) u = 0
  rw [hL]; rfl

/-- **The derivative of the normal coordinate at a point of the zero section is the identity on the
normal space.**  Along the curve `t ↦ e x + t v`, `v ∈ ν_x`, the normal coordinate is `t ↦ t v`. -/
theorem fderiv_normalCoord_apply_of_mem_normalSpace (C : TubeChart E ε) (x : V.pt)
    {v : Euc (8 + k)} (hv : v ∈ normalSpace E x) :
    fderiv ℝ (normalCoord E C) (E.e x) v = v := by
  have hdiff : DifferentiableAt ℝ (normalCoord E C) (E.e x) := by
    have h : ContDiffAt ℝ ∞ (normalCoord E C) (E.e x) :=
      ((contMDiffOn_normalCoord E C).contMDiffAt
        (C.openTube_isOpen.mem_nhds (C.mem_openTube x))).contDiffAt
    exact h.differentiableAt (by simp)
  have hfd : HasFDerivAt (normalCoord E C)
      (fderiv ℝ (normalCoord E C) (E.e x)) (E.e x) := hdiff.hasFDerivAt
  have hψ : HasDerivAt (fun t : ℝ => E.e x + t • v) v 0 := by
    have h1 : HasDerivAt (fun t : ℝ => t • v) ((1 : ℝ) • v) 0 :=
      (hasDerivAt_id (0 : ℝ)).smul_const v
    simpa using h1.const_add (E.e x)
  have hfd' : HasFDerivAt (normalCoord E C)
      (fderiv ℝ (normalCoord E C) (E.e x)) (E.e x + (0 : ℝ) • v) := by simpa using hfd
  have h1 : HasDerivAt (normalCoord E C ∘ fun t : ℝ => E.e x + t • v)
      ((fderiv ℝ (normalCoord E C) (E.e x)) v) 0 :=
    hfd'.comp_hasDerivAt (x := (0 : ℝ)) (f := fun t : ℝ => E.e x + t • v) hψ
  have h2 : HasDerivAt (fun t : ℝ => t • v) v 0 := by
    have h1' : HasDerivAt (fun t : ℝ => t • v) ((1 : ℝ) • v) 0 :=
      (hasDerivAt_id (0 : ℝ)).smul_const v
    simpa using h1'
  have hδ : 0 < ε / (‖v‖ + 1) := div_pos C.eps_pos (by linarith [norm_nonneg v])
  have hev : (fun t : ℝ => normalCoord E C (E.e x + t • v)) =ᶠ[𝓝 (0 : ℝ)]
      (fun t => t • v) := by
    filter_upwards [Metric.ball_mem_nhds (0 : ℝ) hδ] with t ht
    have ht' : |t| < ε / (‖v‖ + 1) := by
      simpa [Metric.mem_ball, Real.dist_eq, sub_zero] using ht
    have htn : ‖t • v‖ < ε := by
      rw [norm_smul, Real.norm_eq_abs]
      calc |t| * ‖v‖ ≤ |t| * (‖v‖ + 1) :=
            mul_le_mul_of_nonneg_left (by linarith [norm_nonneg v]) (abs_nonneg t)
        _ < (ε / (‖v‖ + 1)) * (‖v‖ + 1) :=
            mul_lt_mul_of_pos_right ht' (by linarith [norm_nonneg v])
        _ = ε := by field_simp
    rw [← tubeMap_mk E x (t • v) (Submodule.smul_mem _ t hv)]
    exact normalCoord_tubeMap E C _ (by simpa using htn)
  exact h1.unique (h2.congr_of_eventuallyEq hev)


/-- **A vector that is nowhere tangent.**  The union of the tangent spaces of the image of `E` is
contained in the union, over a finite cover of `V.pt` by chart sources, of the images of the
`C^∞` maps `(τ, u) ↦ (fderiv ℝ (chartRep E.e i) τ) u` defined on `target i × ℝ^8`.  Each of those
images has Hausdorff dimension at most `16 = dim (ℝ^8 × ℝ^8)`, and there are finitely many of them;
since `16 < 8 + k`, the complement of the union is dense, so a vector outside it exists. -/
theorem exists_notMem_tangentSpace_aux {k : ℕ} (hk : 8 < k) {V : Work.ThomBordism.Man8}
    {E : Work.ThomBordism.PontryaginThom.EmbeddingData V (8 + k)} :
    ∃ w : Euc (8 + k), ∀ x : V.pt, w ∉ tangentSpace E x := by
  classical
  obtain ⟨t, ht⟩ := (isCompact_univ (X := V.pt)).elim_finite_subcover
    (fun x : V.pt => (chartAt (Euc 8) x).source) (fun x => (chartAt (Euc 8) x).open_source)
    (fun x _ => Set.mem_iUnion.mpr ⟨x, mem_chart_source (Euc 8) x⟩)
  have key : {w : Euc (8 + k) | ∃ x : V.pt, w ∈ tangentSpace E x} ⊆
      ⋃ y ∈ t, (fun p : Euc 8 × Euc 8 =>
          fderiv ℝ (Work.ThomBordism.PontryaginThom.chartRep E.e
            (Work.ThomBordism.PontryaginThom.chartAtIdx y)) p.1 p.2) ''
        ((chartAt (Euc 8) y).target ×ˢ (Set.univ : Set (Euc 8))) := by
    rintro w ⟨x, hx⟩
    obtain ⟨y, hyt, hxy⟩ := Set.mem_iUnion₂.mp (ht (Set.mem_univ x))
    refine Set.mem_iUnion₂.mpr ⟨y, hyt, ?_⟩
    have hxsrc : x ∈ (chartAt (Euc 8) y).source := hxy
    have hr : tangentSpace E x =
        LinearMap.range (tangentFrame E (Work.ThomBordism.PontryaginThom.chartAtIdx y) x).toLinearMap :=
      (tangentFrame_range E (Work.ThomBordism.PontryaginThom.chartAtIdx y) hxsrc).symm
    rw [hr] at hx
    obtain ⟨u, hu⟩ := LinearMap.mem_range.mp hx
    exact ⟨((chartAt (Euc 8) y) x, u),
      ⟨(chartAt (Euc 8) y).map_source hxsrc, Set.mem_univ u⟩, hu⟩
  have hbound : dimH {w : Euc (8 + k) | ∃ x : V.pt, w ∈ tangentSpace E x} ≤ 16 := by
    have image_bound : ∀ y : V.pt, dimH ((fun p : Euc 8 × Euc 8 =>
        fderiv ℝ (Work.ThomBordism.PontryaginThom.chartRep E.e
          (Work.ThomBordism.PontryaginThom.chartAtIdx y)) p.1 p.2) ''
        ((chartAt (Euc 8) y).target ×ˢ (Set.univ : Set (Euc 8)))) ≤ 16 := by
      intro y
      have hopen : IsOpen ((chartAt (Euc 8) y).target ×ˢ (Set.univ : Set (Euc 8))) :=
        (chartAt (Euc 8) y).open_target.prod isOpen_univ
      have hcont : ContDiffOn ℝ ∞ (fun p : Euc 8 × Euc 8 =>
          fderiv ℝ (Work.ThomBordism.PontryaginThom.chartRep E.e
            (Work.ThomBordism.PontryaginThom.chartAtIdx y)) p.1 p.2)
          ((chartAt (Euc 8) y).target ×ˢ (Set.univ : Set (Euc 8))) := by
        have h1 : ContDiffOn ℝ ∞ (fun τ : Euc 8 =>
            fderiv ℝ (Work.ThomBordism.PontryaginThom.chartRep E.e
              (Work.ThomBordism.PontryaginThom.chartAtIdx y)) τ)
            (chartAt (Euc 8) y).target :=
          contDiffOn_tangentFrame_coord E (Work.ThomBordism.PontryaginThom.chartAtIdx y)
        have h2 : ContDiffOn ℝ ∞ (fun p : Euc 8 × Euc 8 =>
            fderiv ℝ (Work.ThomBordism.PontryaginThom.chartRep E.e
              (Work.ThomBordism.PontryaginThom.chartAtIdx y)) p.1)
            ((chartAt (Euc 8) y).target ×ˢ (Set.univ : Set (Euc 8))) :=
          h1.comp contDiffOn_fst (fun p hp => hp.1)
        exact h2.clm_apply contDiffOn_snd
      have hloc : ∀ p ∈ ((chartAt (Euc 8) y).target ×ˢ (Set.univ : Set (Euc 8))),
          ∃ C : ℝ≥0, ∃ u ∈ 𝓝[((chartAt (Euc 8) y).target ×ˢ (Set.univ : Set (Euc 8)))] p,
          LipschitzOnWith C (fun p : Euc 8 × Euc 8 =>
            fderiv ℝ (Work.ThomBordism.PontryaginThom.chartRep E.e
              (Work.ThomBordism.PontryaginThom.chartAtIdx y)) p.1 p.2) u := by
        intro p hp
        have hcat : ContDiffAt ℝ 1 (fun p : Euc 8 × Euc 8 =>
            fderiv ℝ (Work.ThomBordism.PontryaginThom.chartRep E.e
              (Work.ThomBordism.PontryaginThom.chartAtIdx y)) p.1 p.2) p :=
          (hcont.contDiffAt (hopen.mem_nhds hp)).of_le (by simp)
        obtain ⟨C, u, hu, hCu⟩ := hcat.exists_lipschitzOnWith
        exact ⟨C, u, nhdsWithin_le_nhds hu, hCu⟩
      calc dimH ((fun p : Euc 8 × Euc 8 =>
              fderiv ℝ (Work.ThomBordism.PontryaginThom.chartRep E.e
                (Work.ThomBordism.PontryaginThom.chartAtIdx y)) p.1 p.2) ''
            ((chartAt (Euc 8) y).target ×ˢ (Set.univ : Set (Euc 8))))
          ≤ dimH ((chartAt (Euc 8) y).target ×ˢ (Set.univ : Set (Euc 8))) :=
            dimH_image_le_of_locally_lipschitzOn hloc
        _ ≤ dimH (Set.univ : Set (Euc 8 × Euc 8)) := dimH_mono (Set.subset_univ _)
        _ = 16 := by
            rw [Real.dimH_univ_eq_finrank]
            simp only [Module.finrank_prod, finrank_euclideanSpace, Fintype.card_fin]
            norm_num
    calc dimH {w : Euc (8 + k) | ∃ x : V.pt, w ∈ tangentSpace E x}
        ≤ dimH (⋃ y ∈ t, (fun p : Euc 8 × Euc 8 =>
            fderiv ℝ (Work.ThomBordism.PontryaginThom.chartRep E.e
              (Work.ThomBordism.PontryaginThom.chartAtIdx y)) p.1 p.2) ''
            ((chartAt (Euc 8) y).target ×ˢ (Set.univ : Set (Euc 8)))) := dimH_mono key
      _ = ⨆ y ∈ t, dimH ((fun p : Euc 8 × Euc 8 =>
            fderiv ℝ (Work.ThomBordism.PontryaginThom.chartRep E.e
              (Work.ThomBordism.PontryaginThom.chartAtIdx y)) p.1 p.2) ''
            ((chartAt (Euc 8) y).target ×ˢ (Set.univ : Set (Euc 8)))) :=
          dimH_bUnion t.finite_toSet.countable _
      _ ≤ 16 := iSup₂_le (fun y _ => image_bound y)
  have hlt : dimH {w : Euc (8 + k) | ∃ x : V.pt, w ∈ tangentSpace E x} <
      (Module.finrank ℝ (Euc (8 + k)) : ℝ≥0∞) := by
    refine lt_of_le_of_lt hbound ?_
    rw [show Module.finrank ℝ (Euc (8 + k)) = 8 + k from by simp [finrank_euclideanSpace]]
    exact_mod_cast (by omega : 16 < 8 + k)
  obtain ⟨w, hw⟩ := (dense_compl_of_dimH_lt_finrank hlt).nonempty
  exact ⟨w, fun x hx => hw ⟨x, hx⟩⟩

/-- **Existence of a `C^∞` nowhere-zero normal section** for an embedding of a compact smooth
`8`-manifold with codimension `k > 8`. -/
theorem exists_nowhereZero_normalSection {k : ℕ} (hk : 8 < k) {V : Work.ThomBordism.Man8}
    {E : Work.ThomBordism.PontryaginThom.EmbeddingData V (8 + k)} [Nonempty V.pt] :
    ∃ s : V.pt → Work.Tubular.Euc (8 + k),
      ContMDiff (𝓘(ℝ, EuclideanSpace ℝ (Fin 8))) (𝓘(ℝ, Work.Tubular.Euc (8 + k)))
        ((⊤ : ENat) : WithTop ENat) s ∧
      (∀ x : V.pt, s x ∈ Work.Tubular.normalSpace E x) ∧
      (∀ x : V.pt, s x ≠ 0) := by
  obtain ⟨ε, hεpos, ⟨C⟩⟩ := hasTubularNeighbourhood E
  obtain ⟨w, hw⟩ := exists_notMem_tangentSpace_aux hk (E := E)
  have hsm : ContMDiff (𝓘(ℝ, EuclideanSpace ℝ (Fin 8))) (𝓘(ℝ, Euc (8 + k)))
      ((⊤ : ENat) : WithTop ENat)
      (fun x : V.pt => fderiv ℝ (normalCoord E C) (E.e x) w) := by
    have hderivOn : ContDiffOn ℝ ∞
        (fun y : Euc (8 + k) => fderiv ℝ (normalCoord E C) y) C.openTube :=
      ((contMDiffOn_normalCoord E C).contDiffOn).fderiv_of_isOpen C.openTube_isOpen (by simp)
    have hderivMD : ContMDiffOn 𝓘(ℝ, Euc (8 + k))
        𝓘(ℝ, Euc (8 + k) →L[ℝ] Euc (8 + k)) ∞
        (fun y => fderiv ℝ (normalCoord E C) y) C.openTube :=
      contMDiffOn_iff_contDiffOn.mpr hderivOn
    have hcompOn : ContMDiffOn (𝓡 8)
        𝓘(ℝ, Euc (8 + k) →L[ℝ] Euc (8 + k)) ∞
        ((fun y => fderiv ℝ (normalCoord E C) y) ∘ E.e) Set.univ :=
      hderivMD.comp E.smooth.contMDiffOn (fun x _ => C.mem_openTube x)
    have hcomp : ContMDiff (𝓡 8)
        𝓘(ℝ, Euc (8 + k) →L[ℝ] Euc (8 + k)) ∞
        ((fun y => fderiv ℝ (normalCoord E C) y) ∘ E.e) := contMDiffOn_univ.mp hcompOn
    have := hcomp.clm_apply (contMDiff_const (c := w))
    simpa using this
  refine ⟨fun x => fderiv ℝ (normalCoord E C) (E.e x) w, hsm, ?_, ?_⟩
  · intro x
    change fderiv ℝ (normalCoord E C) (E.e x) w ∈ normalSpace E x
    have hsup : w ∈ tangentSpace E x ⊔ normalSpace E x := by
      rw [tangentSpace_sup_normalSpace E x]
      exact Submodule.mem_top
    obtain ⟨a, ha, b, hb, hab⟩ :=
      (Submodule.mem_sup (p := tangentSpace E x) (p' := normalSpace E x)).mp hsup
    rw [← hab, map_add, fderiv_normalCoord_apply_of_mem_tangentSpace C x ha,
      fderiv_normalCoord_apply_of_mem_normalSpace C x hb, zero_add]
    exact hb
  · intro x hx
    beta_reduce at hx
    have hsup : w ∈ tangentSpace E x ⊔ normalSpace E x := by
      rw [tangentSpace_sup_normalSpace E x]
      exact Submodule.mem_top
    obtain ⟨a, ha, b, hb, hab⟩ :=
      (Submodule.mem_sup (p := tangentSpace E x) (p' := normalSpace E x)).mp hsup
    have hbw : fderiv ℝ (normalCoord E C) (E.e x) w = b := by
      rw [← hab, map_add, fderiv_normalCoord_apply_of_mem_tangentSpace C x ha,
        fderiv_normalCoord_apply_of_mem_normalSpace C x hb, zero_add]
    have hb0 : b = 0 := by rw [← hbw]; exact hx
    exact hw x (by rw [← hab, hb0, add_zero]; exact ha)

end

end Work.PTGeometric
