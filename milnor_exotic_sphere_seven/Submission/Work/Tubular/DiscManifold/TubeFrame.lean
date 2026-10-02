import Submission.Work.Tubular.Global
import Submission.Work.Tubular.DiscManifold.Defs
import Submission.Work.Tubular.Rank
import Submission.Work.ThomBordism.PontryaginThom.Frames
import Submission.Work.ThomBordism.PontryaginThom.FramesRange
import Submission.Work.ThomBordism.PontryaginThom.exists_normalData_of_immersion
import Submission.Work.Tubular.exists_euclidean_normalBundle

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option maxHeartbeats 1600000

/-!
# The normal frame of an embedded manifold, from the tubular neighbourhood

The tubular neighbourhood theorem gives, on the open tube, a smooth map `y ↦ (inv y).1.2` — the
*normal vector* of `y`.  This file reads off from it a smooth family of projections onto the normal
spaces `ν_x = (T_x)^⊥`:

`normalProj C x = fderiv ℝ (fun y => (C.inv y).1.2) (E.e x)`,

which kills the tangent space `T_x` and is the identity on the normal space; by dimension count it is
therefore *the* projection onto `ν_x` along `T_x`.
-/

open scoped Manifold ContDiff Topology
open Function Filter

namespace Work.Tubular

open Work.ThomBordism Work.ThomBordism.PontryaginThom

noncomputable section

variable {V : Work.ThomBordism.Man8} {k : ℕ} {ε : ℝ}

/-! ## The normal vector of a point of the ambient space -/

/-- **The normal vector** of a point of the ambient space, read in the tubular neighbourhood: the
second component of the inverse of the tubular map. -/
def tubeNormal {E : EmbeddingData V (8 + k)} (C : TubeChart E ε) : Euc (8 + k) → Euc (8 + k) :=
  fun y => (C.inv y).1.2

/-- The normal vector is smooth on the open tube. -/
theorem contDiffOn_tubeNormal {E : EmbeddingData V (8 + k)} (C : TubeChart E ε) :
    ContDiffOn ℝ ∞ (tubeNormal C) (C.openTube) := by
  have h := C.contMDiffOn_inv
  have h2 : ContMDiffOn 𝓘(ℝ, Euc (8 + k)) 𝓘(ℝ, Euc (8 + k)) ∞
      (fun y => (C.inv y).1.2) (C.openTube) :=
    ((contMDiffOn_prod_iff _).mp h).2
  rwa [contMDiffOn_iff_contDiffOn] at h2

/-- The normal vector vanishes on the image of the embedding. -/
theorem tubeNormal_embedding {E : EmbeddingData V (8 + k)} (C : TubeChart E ε) (x : V.pt) :
    tubeNormal C (E.e x) = 0 := by
  have h := C.inv_tubeMap (⟨(x, 0), (normalSpace E x).zero_mem⟩ : NormalTotal E)
    (by simpa [normalNorm] using C.eps_pos.le)
  have h2 : tubeMap E (⟨(x, 0), (normalSpace E x).zero_mem⟩ : NormalTotal E) = E.e x := by
    rw [tubeMap_mk, add_zero]
  show (C.inv (E.e x)).1.2 = 0
  rw [← h2, h]

/-- The normal vector of a point of the disc bundle over `x` is the point itself. -/
theorem tubeNormal_add {E : EmbeddingData V (8 + k)} (C : TubeChart E ε) {x : V.pt}
    {τ : Euc (8 + k)} (hτ : τ ∈ normalSpace E x) (hε : ‖τ‖ ≤ ε) :
    tubeNormal C (E.e x + τ) = τ := by
  have h := C.inv_tubeMap (⟨(x, τ), hτ⟩ : NormalTotal E) (by simpa [normalNorm] using hε)
  have h2 : tubeMap E (⟨(x, τ), hτ⟩ : NormalTotal E) = E.e x + τ := tubeMap_mk E x τ hτ
  show (C.inv (E.e x + τ)).1.2 = τ
  rw [← h2, h]

/-! ## The projection onto the normal space -/

/-- **The projection onto the normal space**, read off from the tube chart as the derivative of the
normal-vector map at the point `e x` of the embedded manifold. -/
def normalProj {E : EmbeddingData V (8 + k)} (C : TubeChart E ε) (x : V.pt) :
    Euc (8 + k) →L[ℝ] Euc (8 + k) :=
  fderiv ℝ (tubeNormal C) (E.e x)

/-- The `fderiv` of the normal vector is `C¹` on the open tube. -/
theorem contDiffOn_fderiv_tubeNormal {E : EmbeddingData V (8 + k)} (C : TubeChart E ε) :
    ContDiffOn ℝ 1 (fun y : Euc (8 + k) => fderiv ℝ (tubeNormal C) y) (C.openTube) := by
  have hC2 : ContDiffOn ℝ 2 (tubeNormal C) (C.openTube) :=
    (contDiffOn_tubeNormal C).of_le (ENat.LEInfty.out : (2 : ℕ∞ω) ≤ ∞)
  have huniq : UniqueDiffOn ℝ (C.openTube) :=
    (IsOpen.uniqueDiffOn (𝕜 := ℝ) C.openTube_isOpen : UniqueDiffOn ℝ (C.openTube))
  have h1 : ContDiffOn ℝ 1 (fderivWithin ℝ (tubeNormal C) (C.openTube)) (C.openTube) :=
    ContDiffOn.fderivWithin hC2 huniq (m := 1) (by norm_num)
  refine h1.congr fun y hy => ?_
  rw [fderivWithin_of_isOpen C.openTube_isOpen hy]

/-- The projection onto the normal space depends smoothly on the base point. -/
theorem contMDiffOn_normalProj {E : EmbeddingData V (8 + k)} (C : TubeChart E ε) :
    ContMDiffOn (𝓡 8) 𝓘(ℝ, Euc (8 + k) →L[ℝ] Euc (8 + k)) 1
      (fun x : V.pt => normalProj C x) Set.univ := by
  have hf : ContMDiffOn 𝓘(ℝ, Euc (8 + k)) 𝓘(ℝ, Euc (8 + k) →L[ℝ] Euc (8 + k)) 1
      (fun y : Euc (8 + k) => fderiv ℝ (tubeNormal C) y) (C.openTube) :=
    (contDiffOn_fderiv_tubeNormal C).contMDiffOn
  have he : ContMDiffOn (𝓡 8) 𝓘(ℝ, Euc (8 + k)) 1 (fun x : V.pt => E.e x) Set.univ :=
    (E.smooth.of_le (by simp)).contMDiffOn
  have h := hf.comp he (fun x _ => C.mem_openTube x)
  simpa [normalProj, Function.comp_def] using h

/-! ## The two defining properties of the projection -/

/-- The projection kills the frame of the tangent plane, in any chart. -/
theorem normalProj_apply_frame {E : EmbeddingData V (8 + k)} (C : TubeChart E ε)
    (i : atlas (Euc 8) V.pt) {x : V.pt} (hx : x ∈ i.1.source) (l : Fin 8) :
    normalProj C x (frame E.e i x l) = 0 := by
  have hmem : E.e x ∈ C.openTube := C.mem_openTube x
  have htgt : i.1.target ∈ 𝓝 (i.1 x) := i.1.open_target.mem_nhds (i.1.map_source hx)
  have hw : DifferentiableAt ℝ (tubeNormal C) (E.e x) :=
    ((contDiffOn_tubeNormal C).contDiffAt (C.openTube_isOpen.mem_nhds hmem)).differentiableAt (by simp)
  have hxc : chartRep E.e i (i.1 x) = E.e x := by
    show E.e (i.1.symm (i.1 x)) = E.e x
    rw [i.1.left_inv hx]
  have hz : (fun y : Euc 8 => tubeNormal C (chartRep E.e i y)) =ᶠ[𝓝 (i.1 x)]
      (fun _ => (0 : Euc (8 + k))) := by
    refine Filter.eventuallyEq_of_mem htgt ?_
    intro y hy
    exact tubeNormal_embedding C (i.1.symm y)
  have h0 : fderiv ℝ ((tubeNormal C) ∘ (chartRep E.e i)) (i.1 x) = 0 := by
    change fderiv ℝ (fun y : Euc 8 => tubeNormal C (chartRep E.e i y)) (i.1 x) = 0
    rw [Filter.EventuallyEq.fderiv_eq hz]
    simpa using (fderiv_const (𝕜 := ℝ) (E := Euc 8) (0 : Euc (8 + k)))
  have hdiff : DifferentiableAt ℝ (chartRep E.e i) (i.1 x) :=
    ((contDiffOn_chartRep E.e (E.smooth.of_le (ENat.LEInfty.out : (1 : ℕ∞ω) ≤ ∞)) i).contDiffAt
      htgt).differentiableAt (by norm_num)
  have hcomp := fderiv_comp (f := chartRep E.e i) (g := tubeNormal C) (x := i.1 x)
    (by rw [hxc]; exact hw) hdiff
  have hkey : (fderiv ℝ (tubeNormal C) (E.e x)).comp
      (fderiv ℝ (chartRep E.e i) (i.1 x)) = 0 := by
    rw [← hxc, ← hcomp, h0]
  have := congrArg (fun (L : Euc 8 →L[ℝ] Euc (8 + k)) => L (EuclideanSpace.single l 1)) hkey
  simpa [normalProj, frame, ContinuousLinearMap.comp_apply, ContinuousLinearMap.zero_apply] using this

/-- The projection kills the tangent space. -/
theorem normalProj_apply_of_mem_tangent {E : EmbeddingData V (8 + k)} (C : TubeChart E ε)
    {x : V.pt} {u : Euc (8 + k)} (hu : u ∈ tangentSpace E x) : normalProj C x u = 0 := by
  obtain ⟨i, hi, hx⟩ : ∃ i : OpenPartialHomeomorph V.pt (Euc 8),
      i ∈ atlas (Euc 8) V.pt ∧ x ∈ i.source :=
    ⟨chartAt (Euc 8) x, chart_mem_atlas (H := Euc 8) x, mem_chart_source (Euc 8) x⟩
  rw [← frame_span_eq_tangentSpace E ⟨i, hi⟩ hx] at hu
  obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun (R := ℝ)).mp hu
  rw [map_sum]
  refine Finset.sum_eq_zero fun l _ => ?_
  rw [map_smul, normalProj_apply_frame C ⟨i, hi⟩ hx l, smul_zero]

/-- The projection is the identity on the normal space. -/
theorem normalProj_apply_of_mem_normal {E : EmbeddingData V (8 + k)} (C : TubeChart E ε)
    {x : V.pt} {τ : Euc (8 + k)} (hτ : τ ∈ normalSpace E x) : normalProj C x τ = τ := by
  have hδ : (0 : ℝ) < min 1 (ε / (‖τ‖ + 1)) :=
    lt_min one_pos (div_pos C.eps_pos (add_pos_of_nonneg_of_pos (norm_nonneg τ) one_pos))
  have hcurve : (fun t : ℝ => tubeNormal C (E.e x + t • τ)) =ᶠ[𝓝 (0 : ℝ)]
      (fun t : ℝ => t • τ) := by
    refine Filter.eventuallyEq_of_mem (Metric.ball_mem_nhds 0 hδ) ?_
    intro t ht
    rw [Metric.mem_ball, dist_zero_right, Real.norm_eq_abs] at ht
    have h2 : |t| < ε / (‖τ‖ + 1) := lt_of_lt_of_le ht (min_le_right _ _)
    refine tubeNormal_add C (Submodule.smul_mem _ t hτ) ?_
    rw [norm_smul, Real.norm_eq_abs]
    calc |t| * ‖τ‖ ≤ (ε / (‖τ‖ + 1)) * ‖τ‖ :=
          mul_le_mul_of_nonneg_right h2.le (norm_nonneg τ)
      _ ≤ ε := by
          rw [div_mul_eq_mul_div, div_le_iff₀ (add_pos_of_nonneg_of_pos (norm_nonneg τ) one_pos)]
          nlinarith [norm_nonneg τ, C.eps_pos]
  have hder1 : fderiv ℝ (fun t : ℝ => tubeNormal C (E.e x + t • τ)) 0
      = fderiv ℝ (fun t : ℝ => t • τ) 0 := Filter.EventuallyEq.fderiv_eq hcurve
  have hder2 : fderiv ℝ (fun t : ℝ => tubeNormal C (E.e x + t • τ)) 0
      = (normalProj C x).comp (fderiv ℝ (fun t : ℝ => t • τ) 0) := by
    have hmem : E.e x ∈ C.openTube := C.mem_openTube x
    have h1 : DifferentiableAt ℝ (tubeNormal C) (E.e x) :=
      ((contDiffOn_tubeNormal C).contDiffAt (C.openTube_isOpen.mem_nhds hmem)).differentiableAt (by simp)
    have hdiff2 : DifferentiableAt ℝ (fun t : ℝ => E.e x + t • τ) 0 :=
      (differentiableAt_const (c := E.e x)).add (differentiableAt_id.smul_const τ)
    have hinner : (fun t : ℝ => E.e x + t • τ) = fun t : ℝ => (fun s : ℝ => s • τ) t + E.e x :=
      funext fun t => add_comm _ _
    have h1' : DifferentiableAt ℝ (tubeNormal C) (E.e x + (0 : ℝ) • τ) := by simpa using h1
    have hcomp := fderiv_comp (f := fun t : ℝ => E.e x + t • τ) (g := tubeNormal C) (x := (0 : ℝ))
      h1' hdiff2
    change fderiv ℝ ((tubeNormal C) ∘ (fun t : ℝ => E.e x + t • τ)) 0 = _
    rw [hcomp, hinner, fderiv_add_const, normalProj]
    simp only [zero_smul, add_zero]
  have h4 : fderiv ℝ (fun t : ℝ => t • τ) 0 1 = τ := by
    rw [fderiv_smul_const (c := fun t : ℝ => (t : ℝ)) (x := (0 : ℝ)) (by fun_prop) τ]
    simp [ContinuousLinearMap.smulRight_apply]
  have h3 := congrArg (fun (L : ℝ →L[ℝ] Euc (8 + k)) => L 1) (hder1.symm.trans hder2)
  simp only [ContinuousLinearMap.comp_apply] at h3
  rw [h4] at h3
  exact h3.symm

/-! ## The kernel and the range of the projection -/

/-- The kernel of the projection is the tangent space. -/
theorem ker_normalProj {E : EmbeddingData V (8 + k)} (C : TubeChart E ε) (x : V.pt) :
    tangentSpace E x = (normalProj C x).ker := by
  have hle : tangentSpace E x ≤ (normalProj C x).ker := fun u hu =>
    LinearMap.mem_ker.mpr (normalProj_apply_of_mem_tangent C hu)
  have hν : Module.finrank ℝ ↥(normalSpace E x) = k := by
    have h := finrank_normalSpace E x
    rw [h]
    omega
  have hN : Module.finrank ℝ (Euc (8 + k)) = 8 + k := by
    rw [finrank_euclideanSpace, Fintype.card_fin]
  have him : normalSpace E x ≤ (normalProj C x).range := fun τ hτ =>
    ⟨τ, normalProj_apply_of_mem_normal C hτ⟩
  have hle8 : 8 ≤ Module.finrank ℝ ↥(normalProj C x).ker :=
    calc (8 : ℕ) = Module.finrank ℝ ↥(tangentSpace E x) := (finrank_tangentSpace E x).symm
      _ ≤ Module.finrank ℝ ↥(normalProj C x).ker := Submodule.finrank_mono hle
  have hker : Module.finrank ℝ ↥(normalProj C x).ker = 8 := by
    have h := LinearMap.finrank_range_add_finrank_ker (normalProj C x).toLinearMap
    have hr : k ≤ Module.finrank ℝ ↥(normalProj C x).range := by
      have h2 := Submodule.finrank_mono him
      rwa [hν] at h2
    omega
  exact Submodule.eq_of_le_of_finrank_eq hle (by rw [finrank_tangentSpace E x, hker])

/-- The range of the projection is the normal space. -/
theorem range_normalProj {E : EmbeddingData V (8 + k)} (C : TubeChart E ε) (x : V.pt) :
    normalSpace E x = (normalProj C x).range := by
  refine Submodule.eq_of_le_of_finrank_eq (fun τ hτ => ⟨τ, normalProj_apply_of_mem_normal C hτ⟩) ?_
  have hν : Module.finrank ℝ ↥(normalSpace E x) = k := by
    have h := finrank_normalSpace E x
    rw [h]; omega
  have hN : Module.finrank ℝ (Euc (8 + k)) = 8 + k := by
    rw [finrank_euclideanSpace, Fintype.card_fin]
  have hker : Module.finrank ℝ ↥(normalProj C x).ker = 8 :=
    calc Module.finrank ℝ ↥(normalProj C x).ker
        = Module.finrank ℝ ↥(tangentSpace E x) := by rw [ker_normalProj C x]
      _ = 8 := finrank_tangentSpace E x
  have hrange : Module.finrank ℝ ↥(normalProj C x).range = k := by
    have h := LinearMap.finrank_range_add_finrank_ker (normalProj C x).toLinearMap
    omega
  rw [hν, hrange]

/-! ## The normal frame over the chart cover -/

/-- **The normal frame** of the chart index `i = (i₀,S)`: the projection onto the normal space of the
complement-coordinate insertion of the standard basis.  On the base set of `i` this is a basis of
the normal space `ν_x`, and it depends `C¹` on `x`. -/
def tubeFrame {E : EmbeddingData V (8 + k)} (C : TubeChart E ε) (i : CoverIdx V k) (x : V.pt) :
    Fin k → Euc (8 + k) :=
  fun l => normalProj C x (funToEuc (8 + k) (complInj i.2 (Pi.single l (1 : ℝ))))

/-- The frame vectors lie in the normal space. -/
theorem tubeFrame_mem {E : EmbeddingData V (8 + k)} (C : TubeChart E ε) (i : CoverIdx V k)
    (x : V.pt) (l : Fin k) : tubeFrame C i x l ∈ normalSpace E x := by
  rw [range_normalProj C x]
  exact ⟨_, rfl⟩

/-- The frame is `C¹` in the base point. -/
theorem contMDiffOn_tubeFrame {E : EmbeddingData V (8 + k)} (C : TubeChart E ε) (i : CoverIdx V k)
    (l : Fin k) :
    ContMDiffOn (𝓡 8) 𝓘(ℝ, Euc (8 + k)) 1 (fun x : V.pt => tubeFrame C i x l) (coverBaseSet E.e i) := by
  have hv : ContMDiffOn (𝓡 8) 𝓘(ℝ, Euc (8 + k)) 1
      (fun _ : V.pt => funToEuc (8 + k) (complInj i.2 (Pi.single l (1 : ℝ)))) Set.univ :=
    contMDiffOn_const
  have h := (contMDiffOn_normalProj C).clm_apply hv
  simpa [tubeFrame] using h.mono (Set.inter_subset_left)

/-- The frame is linearly independent on the base set. -/
theorem tubeFrame_linearIndependent {E : EmbeddingData V (8 + k)} (C : TubeChart E ε)
    (i : CoverIdx V k) {x : V.pt} (hx : x ∈ coverBaseSet E.e i) :
    LinearIndependent ℝ (tubeFrame C i x) := by
  have hxc : x ∈ (coverChart i).1.source := hx.1
  have hdet : (Grassmann.frameMatrix i.2 (frame E.e (coverChart i) x)).det ≠ 0 := hx.2
  rw [Fintype.linearIndependent_iff]
  intro c hc
  have hlin : normalProj C x (funToEuc (8 + k) (complInj i.2 c))
      = ∑ l, c l • tubeFrame C i x l := by
    have h1 : c = ∑ l, c l • (Pi.single l 1 : Fin k → ℝ) :=
      (sum_smul_single_eq_self k c).symm
    conv_lhs => rw [h1]
    simp only [map_sum, map_smul, tubeFrame]

  have hzero : normalProj C x (funToEuc (8 + k) (complInj i.2 c)) = 0 := by
    rw [hlin, hc]
  have hker : funToEuc (8 + k) (complInj i.2 c) ∈ tangentSpace E x := by
    rw [ker_normalProj]
    exact LinearMap.mem_ker.mpr hzero
  have hcoord : complInj i.2 c ∈ LinearMap.range (Grassmann.coeffMap (frame E.e (coverChart i) x)) := by
    rw [range_coeffMap_frame_eq_tangentSpace E (coverChart i) hxc]
    exact ⟨funToEuc (8 + k) (complInj i.2 c), hker, eucToFun_funToEuc (8 + k) _⟩
  have hpz : planeProj (frame E.e (coverChart i) x) i.2 hdet (complInj i.2 c) = 0 := by
    have hmem : complInj i.2 c
        ∈ LinearMap.ker (planeProj (frame E.e (coverChart i) x) i.2 hdet) := by
      rw [ker_planeProj (frame E.e (coverChart i) x) i.2 hdet]
      exact hcoord
    exact LinearMap.mem_ker.mp hmem
  have hpc : planeProj (frame E.e (coverChart i) x) i.2 hdet (complInj i.2 c) = c := by
    have h := congrArg (fun (g : (Fin k → ℝ) →ₗ[ℝ] (Fin k → ℝ)) => g c)
      (planeProj_planeInj (frame E.e (coverChart i) x) i.2 hdet)
    simpa [planeInj] using h
  have hc0 : c = 0 := hpc.symm.trans hpz
  intro l
  exact congrFun hc0 l

/-- The frame spans the normal space on the base set. -/
theorem tubeFrame_span {E : EmbeddingData V (8 + k)} (C : TubeChart E ε) (i : CoverIdx V k)
    {x : V.pt} (hx : x ∈ coverBaseSet E.e i) :
    Submodule.span ℝ (Set.range (tubeFrame C i x)) = normalSpace E x := by
  refine Submodule.eq_of_le_of_finrank_eq ?_ ?_
  · exact Submodule.span_le.mpr (Set.range_subset_iff.mpr fun l => tubeFrame_mem C i x l)
  · have hind := tubeFrame_linearIndependent C i hx
    rw [finrank_span_eq_card hind, Fintype.card_fin]
    have h := finrank_normalSpace E x
    rw [h]; omega

end

end Work.Tubular
