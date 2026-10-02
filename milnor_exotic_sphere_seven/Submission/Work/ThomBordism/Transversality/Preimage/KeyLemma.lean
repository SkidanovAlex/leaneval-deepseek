import Mathlib
import Submission.Work.ThomBordism.Transversality.Preimage.Setup

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# The key linear-algebra input at a boundary point of the preimage

At a boundary point `w ∈ ∂M ∩ F ⁻¹' X.core`, the *geometric* input `hbnd` (the restriction of
`Φ ∘ F` to `∂M` is a submersion along its zero set) forces the derivative of `Φ ∘ F` at `w` to
have a kernel which is *not* contained in the tangent space of `∂M`.  In the coordinates of the
submersion normal form at `w`, this reads: the level set direction `ker a` (where `a` is the first
component of the normal form) does not lie in the hyperplane `{z 0 = 0}` cut out by the boundary.

The proof is the "open mapping" argument: on a neighbourhood of `w` inside `∂M`, the boundary
chart and the normal form combine to make `a` restricted to the hyperplane `{z 0 = 0}` (shifted by
the level) an *open* map, so `a '' {z 0 = 0}` is a linear subspace containing a neighbourhood of the
origin, hence everything.
-/

open scoped Manifold Topology ContDiff
open Function Set Manifold
open ModelWithCorners

namespace Work.ThomBordism.Transversality.Preimage

noncomputable section

/-- The zeroth coordinate, as a continuous linear map. -/
def sLin (m : ℕ) : EuclideanSpace ℝ (Fin (m + 1)) →L[ℝ] ℝ :=
  (ContinuousLinearMap.proj (0 : Fin (m + 1))).comp
    (Work.Surgery.euclToPi (m + 1)).toContinuousLinearMap

theorem sLin_apply (m : ℕ) (v : EuclideanSpace ℝ (Fin (m + 1))) : sLin m v = v.ofLp 0 := by
  simp [sLin, Work.Surgery.euclToPi_ofLp]

/-- **A linear subspace containing a neighbourhood of a point is everything.** -/
theorem Submodule.eq_top_of_isOpen_subset {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (M : Submodule ℝ E) {s : Set E} (hs : IsOpen s) (hne : s.Nonempty) (hsub : s ⊆ M) :
    M = ⊤ := by
  obtain ⟨x, hx⟩ := hne
  have hMn : (M : Set E) ∈ 𝓝 x := Filter.mem_of_superset (hs.mem_nhds hx) hsub
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp hMn
  have hxM : x ∈ M := hsub hx
  have hε2 : 0 < ε / 2 := half_pos hε
  refine eq_top_iff.mpr fun y _ => ?_
  set δ : ℝ := (ε / 2) / (‖y‖ + 1) with hδ
  have hδpos : 0 < δ := div_pos hε2 (by positivity)
  have hδy : δ * ‖y‖ < ε := by
    have h1 : δ * (‖y‖ + 1) = ε / 2 := by
      rw [hδ]; field_simp
    nlinarith [norm_nonneg y]
  have hmem : x + δ • y ∈ M := hball (by
    rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul,
      Real.norm_of_nonneg hδpos.le]
    exact lt_of_lt_of_le hδy (by linarith))
  have h2 : δ • y ∈ M := by
    have := M.sub_mem hmem hxM
    simpa using this
  have hδne : δ ≠ 0 := ne_of_gt hδpos
  have hy : y = δ⁻¹ • (δ • y) := by
    rw [smul_smul, inv_mul_cancel₀ hδne, one_smul]
  rw [hy]
  exact M.smul_mem _ h2

variable {k : ℕ} (S : CoreSetup k)

/-- The first component of the normal-form equivalence, as a continuous linear map. -/
def aLin (w : S.Pre) : EuclideanSpace ℝ (Fin ((8 + k) + 1)) →L[ℝ] EuclideanSpace ℝ (Fin k) :=
  (ContinuousLinearMap.fst ℝ (EuclideanSpace ℝ (Fin k)) (S.complType w)).comp
    (S.equivAt w : EuclideanSpace ℝ (Fin ((8 + k) + 1)) →L[ℝ]
      (EuclideanSpace ℝ (Fin k) × S.complType w))

theorem aLin_apply (w : S.Pre) (v : EuclideanSpace ℝ (Fin ((8 + k) + 1))) :
    aLin S w v = (S.equivAt w v).1 := rfl

theorem aLin_surjective (w : S.Pre) : Function.Surjective (aLin S w) := fun y =>
  ⟨(S.equivAt w).symm (y, 0), by simp [aLin_apply]⟩

/-- **The key geometric input.**  At a boundary point `w` of the preimage, the image under the
first component `a` of the normal form of the hyperplane `{z 0 = 0}` is everything. -/
theorem aLin_map_ker_eq_top (w : S.Pre) (hw : w.1 ∈ (𝓡∂ ((8 + k) + 1)).boundary S.M) :
    (LinearMap.ker (sLin (8 + k) : EuclideanSpace ℝ (Fin ((8 + k) + 1)) →ₗ[ℝ] ℝ)).map
      (aLin S w : EuclideanSpace ℝ (Fin ((8 + k) + 1)) →ₗ[ℝ] EuclideanSpace ℝ (Fin k)) = ⊤ := by
  -- the data given by the boundary submersion hypothesis
  obtain ⟨𝔽b, hNACG, hNS, hPb⟩ := S.bndSubmersion w.1 hw (S.zero_mem_coreMap w)
  letI := hNACG
  letI := hNS
  let ρ : OpenPartialHomeomorph ↥((𝓡∂ ((8 + k) + 1)).boundary S.M)
      (EuclideanSpace ℝ (Fin (8 + k))) := hPb.domChart
  let ψb : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin k)) (EuclideanSpace ℝ (Fin k)) :=
    hPb.codChart
  let Ab : EuclideanSpace ℝ (Fin (8 + k)) ≃L[ℝ] (EuclideanSpace ℝ (Fin k) × 𝔽b) := hPb.equiv
  let wb : ↥((𝓡∂ ((8 + k) + 1)).boundary S.M) := ⟨w.1, hw⟩
  let bc : OpenPartialHomeomorph ↥((𝓡∂ ((8 + k) + 1)).boundary S.M)
      (EuclideanSpace ℝ (Fin (8 + k))) := Work.Surgery.boundaryChartAt wb
  let τ : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin (8 + k)))
      (EuclideanSpace ℝ (Fin (8 + k))) := OpenPartialHomeomorph.trans bc.symm ρ
  let ψ : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin k)) (EuclideanSpace ℝ (Fin k)) :=
    S.codChartAt w
  let θ : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin k)) (EuclideanSpace ℝ (Fin k)) :=
    OpenPartialHomeomorph.trans ψb.symm ψ
  -- the normal form of `Φ ∘ F` restricted to `∂M`
  have hNform : ∀ y : ↥((𝓡∂ ((8 + k) + 1)).boundary S.M), y ∈ ρ.source →
      ψb (S.coreMap y.1) = (Ab (ρ y)).1 := by
    intro y hy
    have hz : (ρ.extend (𝓡 (8 + k))) y ∈ (ρ.extend (𝓡 (8 + k))).target :=
      PartialEquiv.map_source _ (by simpa [OpenPartialHomeomorph.extend_source] using hy)
    have h := hPb.writtenInCharts hz
    have hinv : (ρ.extend (𝓡 (8 + k))).symm ((ρ.extend (𝓡 (8 + k))) y) = y :=
      PartialEquiv.left_inv _ (by simpa [OpenPartialHomeomorph.extend_source] using hy)
    rw [Function.comp_apply, Function.comp_apply, hinv] at h
    have h2 : (ψb.extend (𝓡 k)) (S.coreMap y.1) = ψb (S.coreMap y.1) := by
      rw [OpenPartialHomeomorph.extend_coe]; rfl
    rw [h2] at h
    exact h
  -- the neighbourhood of `w` in the boundary-chart coordinates
  let T : Set ↥((𝓡∂ ((8 + k) + 1)).boundary S.M) :=
    {y | y.1 ∈ (S.domChartAt w).source}
  let V : Set (EuclideanSpace ℝ (Fin (8 + k))) :=
    (bc.target ∩ (bc.symm ⁻¹' T)) ∩ τ.source
  have hTopen : IsOpen T := (S.domChartAt w).open_source.preimage continuous_subtype_val
  have hVopen : IsOpen V := (bc.isOpen_inter_preimage_symm hTopen).inter τ.open_source
  -- the composite identity on `V`
  have hident : ∀ z ∈ V,
      aLin S w ((S.domChartAt w).extend (𝓡∂ ((8 + k) + 1)) (bc.symm z).1)
        = θ ((Ab (τ z)).1) := by
    intro z hz
    have hzρ : bc.symm z ∈ ρ.source := by
      have h : z ∈ τ.source := hz.2
      rw [OpenPartialHomeomorph.trans_source, OpenPartialHomeomorph.symm_source] at h
      exact h.2
    have hzφ : (bc.symm z).1 ∈ (S.domChartAt w).source := hz.1.2
    rw [aLin_apply, ← CoreSetup.codChartAt_coreMap S w hzφ]
    rw [OpenPartialHomeomorph.trans_apply]
    rw [OpenPartialHomeomorph.trans_apply bc.symm ρ]
    rw [← hNform (bc.symm z) hzρ]
    rw [show ψb.symm (ψb (S.coreMap (bc.symm z).1)) = S.coreMap (bc.symm z).1 from
      PartialEquiv.left_inv _ (hPb.source_subset_preimage_source hzρ)]
  have hnformw : ψb (S.coreMap w.1) = (Ab (ρ wb)).1 := hNform wb hPb.mem_domChart_source
  -- the open set in the second factor
  have hVτ : V ⊆ τ.source := fun z hz => hz.2
  have hτV : IsOpen (τ '' V) := τ.isOpen_image_of_subset_source hVopen hVτ
  have hAbOpenMap : IsOpenMap (fun z : EuclideanSpace ℝ (Fin (8 + k)) => (Ab z).1) :=
    ContinuousLinearMap.isOpenMap
      ((ContinuousLinearMap.fst ℝ (EuclideanSpace ℝ (Fin k)) 𝔽b).comp
        (Ab : EuclideanSpace ℝ (Fin (8 + k)) →L[ℝ] (EuclideanSpace ℝ (Fin k) × 𝔽b)))
      (fun y => ⟨Ab.symm (y, 0), by simp⟩)
  have hAbV : IsOpen ((fun z : EuclideanSpace ℝ (Fin (8 + k)) => (Ab z).1) '' (τ '' V)) :=
    hAbOpenMap _ hτV
  -- the distinguished point
  have hbcsrc : wb ∈ bc.source := Work.Surgery.boundaryChartAt_mem_source wb
  have hbctgt : bc wb ∈ bc.target := OpenPartialHomeomorph.map_source bc hbcsrc
  have hbcρ : bc.symm (bc wb) ∈ ρ.source := by
    rw [show bc.symm (bc wb) = wb from PartialEquiv.left_inv _ hbcsrc]
    exact hPb.mem_domChart_source
  have hmemV : bc wb ∈ V := by
    refine ⟨⟨hbctgt, ?_⟩, ?_⟩
    · show bc.symm (bc wb) ∈ T
      rw [show bc.symm (bc wb) = wb from PartialEquiv.left_inv _ hbcsrc]
      exact CoreSetup.mem_domChartAt_source S w
    · rw [OpenPartialHomeomorph.trans_source, OpenPartialHomeomorph.symm_source]
      exact ⟨hbctgt, hbcρ⟩
  have hz0 : (Ab (τ (bc wb))).1 = ψb (S.coreMap w.1) := by
    rw [OpenPartialHomeomorph.trans_apply bc.symm ρ,
      show bc.symm (bc wb) = wb from PartialEquiv.left_inv _ hbcsrc]
    exact hnformw.symm
  have hmemθ0 : (Ab (τ (bc wb))).1 ∈ θ.source := by
    rw [hz0]
    refine ⟨ψb.mapsTo (hPb.source_subset_preimage_source hPb.mem_domChart_source), ?_⟩
    rw [Set.mem_preimage]
    show ψb.symm (ψb (S.coreMap w.1)) ∈ ψ.source
    rw [show ψb.symm (ψb (S.coreMap w.1)) = S.coreMap w.1 from
      PartialEquiv.left_inv _ (hPb.source_subset_preimage_source hPb.mem_domChart_source)]
    exact CoreSetup.domChartAt_source_subset S w (CoreSetup.mem_domChartAt_source S w)
  have hS3 : IsOpen (((fun z : EuclideanSpace ℝ (Fin (8 + k)) => (Ab z).1) '' (τ '' V))
      ∩ θ.source) := hAbV.inter θ.open_source
  have hmemS2 : (Ab (τ (bc wb))).1 ∈
      ((fun z : EuclideanSpace ℝ (Fin (8 + k)) => (Ab z).1) '' (τ '' V)) :=
    ⟨τ (bc wb), ⟨bc wb, hmemV, rfl⟩, rfl⟩
  have hne : (θ '' (((fun z : EuclideanSpace ℝ (Fin (8 + k)) => (Ab z).1) '' (τ '' V))
      ∩ θ.source)).Nonempty :=
    ⟨θ ((Ab (τ (bc wb))).1), (Ab (τ (bc wb))).1, ⟨hmemS2, hmemθ0⟩, rfl⟩
  have hθopen : IsOpen (θ '' (((fun z : EuclideanSpace ℝ (Fin (8 + k)) => (Ab z).1)
      '' (τ '' V)) ∩ θ.source)) :=
    θ.isOpen_image_of_subset_source hS3 inter_subset_right
  have hsub_map : θ '' (((fun z : EuclideanSpace ℝ (Fin (8 + k)) => (Ab z).1) '' (τ '' V))
      ∩ θ.source) ⊆
      (LinearMap.ker (sLin (8 + k) : EuclideanSpace ℝ (Fin ((8 + k) + 1)) →ₗ[ℝ] ℝ)).map
        (aLin S w : EuclideanSpace ℝ (Fin ((8 + k) + 1)) →ₗ[ℝ] EuclideanSpace ℝ (Fin k)) := by
    rintro x ⟨y, ⟨hy2, -⟩, rfl⟩
    obtain ⟨z, hz, rfl⟩ := hy2
    obtain ⟨z', hz', rfl⟩ := hz
    have hzφ : (bc.symm z').1 ∈ (S.domChartAt w).source := hz'.1.2
    have hker : (S.domChartAt w).extend (𝓡∂ ((8 + k) + 1)) (bc.symm z').1
        ∈ LinearMap.ker (sLin (8 + k) : EuclideanSpace ℝ (Fin ((8 + k) + 1)) →ₗ[ℝ] ℝ) := by
      change sLin (8 + k) ((S.domChartAt w).extend (𝓡∂ ((8 + k) + 1)) (bc.symm z').1) = 0
      rw [sLin_apply]
      exact (mem_boundary_iff_extend_apply_coord_eq_zero (m := (8 + k) + 1)
        (CoreSetup.domChartAt_mem_maximalAtlas S w) hzφ).mp (bc.symm z').2
    exact ⟨_, hker, hident z' hz'⟩
  exact Submodule.eq_top_of_isOpen_subset _ hθopen hne hsub_map

/-- **The key linear-algebra input at a boundary point.**  At `w ∈ ∂M ∩ F ⁻¹' X.core` there is a
vector in the kernel of the first component `a` of the normal form whose zeroth coordinate does not
vanish: the level set of `Φ ∘ F` at `w` crosses the boundary hyperplane. -/
theorem exists_ker_coord_ne_zero (S : CoreSetup k) (w : S.Pre)
    (hw : w.1 ∈ (𝓡∂ ((8 + k) + 1)).boundary S.M) :
    ∃ v : EuclideanSpace ℝ (Fin ((8 + k) + 1)), aLin S w v = 0 ∧ v 0 ≠ 0 := by
  by_contra hno
  have hkerle : ∀ v, aLin S w v = 0 → v 0 = 0 := by
    intro v hv
    by_contra hne
    exact hno ⟨v, hv, hne⟩
  have htop := aLin_map_ker_eq_top S w hw
  obtain ⟨T, hT⟩ := exists_linearEquiv_prod_ker 8 k (aLin S w) (aLin_surjective S w)
  -- vectors of the form `T.symm (0, z)` have vanishing zeroth coordinate
  have h1 : ∀ z : EuclideanSpace ℝ (Fin (8 + 1)),
      sLin (8 + k) (T.symm (0, z)) = 0 := by
    intro z
    apply hkerle
    rw [← hT (T.symm (0, z))]
    show (T (T.symm (0, z))).1 = 0
    rw [ContinuousLinearEquiv.apply_symm_apply]
  -- consequently every vector of the form `T.symm (y, 0)` does
  have h2 : ∀ y : EuclideanSpace ℝ (Fin k), sLin (8 + k) (T.symm (y, 0)) = 0 := by
    intro y
    obtain ⟨u, hu, hau⟩ := Submodule.mem_map.mp
      (show y ∈ (LinearMap.ker (sLin (8 + k) : EuclideanSpace ℝ (Fin ((8 + k) + 1)) →ₗ[ℝ] ℝ)).map
          (aLin S w : EuclideanSpace ℝ (Fin ((8 + k) + 1)) →ₗ[ℝ] EuclideanSpace ℝ (Fin k)) by
        rw [htop]; exact Submodule.mem_top)
    have hu' : sLin (8 + k) u = 0 := hu
    have hTu : (T u).1 = y := by rw [hT u]; exact hau
    have hpair : (y, 0) = T u - (0, (T u).2) := by
      ext <;> simp [hTu]
    rw [hpair]
    rw [show T.symm (T u - (0, (T u).2)) = T.symm (T u) - T.symm (0, (T u).2) from
      map_sub (T.symm) _ _]
    rw [show sLin (8 + k) (T.symm (T u) - T.symm (0, (T u).2))
        = sLin (8 + k) (T.symm (T u)) - sLin (8 + k) (T.symm (0, (T u).2)) from
      map_sub (sLin (8 + k)) _ _]
    rw [ContinuousLinearEquiv.symm_apply_apply, hu', h1 ((T u).2), sub_zero]
  have h3 : ∀ w' : EuclideanSpace ℝ (Fin k) × EuclideanSpace ℝ (Fin (8 + 1)),
      sLin (8 + k) (T.symm w') = 0 := by
    intro w'
    obtain ⟨y, z⟩ := w'
    have hsplit : T.symm (y, z) = T.symm (y, 0) + T.symm (0, z) := by
      rw [show (y, z) = (y, 0) + (0, z) by ext <;> simp, map_add]
    rw [hsplit, map_add, h2 y, h1 z, zero_add]
  have hs0 : sLin (8 + k) = 0 := by
    ext v
    show sLin (8 + k) v = 0
    rw [← ContinuousLinearEquiv.symm_apply_apply T v]
    exact h3 (T v)
  have hone : sLin (8 + k) (Work.Surgery.e₀ (8 + k)) = 1 := by
    show (Work.Surgery.e₀ (8 + k)).ofLp 0 = 1
    exact Work.Surgery.e₀_apply_zero (8 + k)
  rw [hs0] at hone
  simpa using hone

end

end Work.ThomBordism.Transversality.Preimage
