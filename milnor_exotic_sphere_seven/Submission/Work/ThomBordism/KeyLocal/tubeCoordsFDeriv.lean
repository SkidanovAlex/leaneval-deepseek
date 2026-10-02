import Mathlib
import Submission.Work.ThomBordism.KeyLocal.tubeSets
import Submission.Work.ThomBordism.FrameSigns.Charts

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

namespace Work.ThomBordism.KeyLocal

open scoped Manifold ContDiff Topology
open Work.Tubular Work.ThomBordism.PontryaginThom

noncomputable section

set_option maxHeartbeats 1600000
set_option linter.unusedVariables false

variable {V : Work.ThomBordism.Man8} {k : ℕ}

/-! ## The neighbourhood on which the tube coordinates are smooth

The tube inverse `C.inv` is smooth on the *open* tube and the foot of a point of the tube lies in the
base set of the normal-datum chart `i` near `E.e x`.  The set `tcfdSet` is the intersection of those
two conditions; it is a neighbourhood of `E.e x` on which every ingredient of the tube coordinates
is well behaved. -/

/-- The neighbourhood of the embedding point on which the tube coordinates are smooth and the foot
stays in the base set of the normal-datum chart `i`. -/
def tcfdSet (E : EmbeddingData V (8 + k)) {ε : ℝ} (C : TubeChart E ε)
    (ND : NormalData V k E.e) (i : CoverIdx V k) : Set (Work.Tubular.Euc (8 + k)) :=
  C.openTube ∩ (fun y => NormalTotal.proj (C.inv y)) ⁻¹' (ND.D.baseSet i)

theorem mem_tcfdSet (E : EmbeddingData V (8 + k)) {ε : ℝ} (C : TubeChart E ε)
    (ND : NormalData V k E.e) (i : CoverIdx V k) (y : Work.Tubular.Euc (8 + k)) :
    y ∈ tcfdSet E C ND i ↔
      y ∈ C.openTube ∧ NormalTotal.proj (C.inv y) ∈ ND.D.baseSet i := Iff.rfl

theorem tcfdSet_sub_openTube (E : EmbeddingData V (8 + k)) {ε : ℝ} (C : TubeChart E ε)
    (ND : NormalData V k E.e) (i : CoverIdx V k) :
    tcfdSet E C ND i ⊆ C.openTube := fun _ h => h.1

theorem tcfdSet_sub_baseSet (E : EmbeddingData V (8 + k)) {ε : ℝ} (C : TubeChart E ε)
    (ND : NormalData V k E.e) (i : CoverIdx V k) :
    ∀ y ∈ tcfdSet E C ND i, NormalTotal.proj (C.inv y) ∈ ND.D.baseSet i := fun _ h => h.2

/-! ## The tube inverse of an embedding point -/

/-- The tube inverse of an embedding point is the corresponding zero-section point. -/
theorem inv_embed_tcfd (E : EmbeddingData V (8 + k)) {ε : ℝ} (C : TubeChart E ε) (x : V.pt) :
    C.inv (E.e x) = (⟨(x, 0), by simp⟩ : NormalTotal E) := by
  have hnorm : normalNorm E (⟨(x, 0), by simp⟩ : NormalTotal E) ≤ ε := by
    simp [C.eps_pos.le]
  have h := C.inv_tubeMap (⟨(x, 0), by simp⟩ : NormalTotal E) hnorm
  simpa using h

theorem proj_inv_embed_tcfd (E : EmbeddingData V (8 + k)) {ε : ℝ} (C : TubeChart E ε)
    (x : V.pt) : NormalTotal.proj (C.inv (E.e x)) = x := by
  rw [inv_embed_tcfd E C x]; rfl

theorem vec_inv_embed_tcfd (E : EmbeddingData V (8 + k)) {ε : ℝ} (C : TubeChart E ε)
    (x : V.pt) : NormalTotal.vec (C.inv (E.e x)) = 0 := by
  rw [inv_embed_tcfd E C x]; rfl

/-! ## Smoothness of the tube coordinates -/

theorem contMDiffOn_proj_inv (E : EmbeddingData V (8 + k)) {ε : ℝ} (C : TubeChart E ε) :
    ContMDiffOn 𝓘(ℝ, Work.Tubular.Euc (8 + k)) (𝓡 8) ∞
      (fun y => NormalTotal.proj (C.inv y)) C.openTube :=
  ((contMDiffOn_prod_iff
    (fun y => (NormalTotal.proj (C.inv y), NormalTotal.vec (C.inv y)))).1
    C.contMDiffOn_inv).1

theorem contMDiffOn_vec_inv (E : EmbeddingData V (8 + k)) {ε : ℝ} (C : TubeChart E ε) :
    ContMDiffOn 𝓘(ℝ, Work.Tubular.Euc (8 + k)) 𝓘(ℝ, Work.Tubular.Euc (8 + k)) ∞
      (fun y => NormalTotal.vec (C.inv y)) C.openTube :=
  ((contMDiffOn_prod_iff
    (fun y => (NormalTotal.proj (C.inv y), NormalTotal.vec (C.inv y)))).1
    C.contMDiffOn_inv).2

theorem tcfdSet_mem_nhds (E : EmbeddingData V (8 + k)) {ε : ℝ} (C : TubeChart E ε)
    (ND : NormalData V k E.e) (i : CoverIdx V k) {x : V.pt} (hx : x ∈ ND.D.baseSet i)
    {y₀ : Work.Tubular.Euc (8 + k)} (hy₀ : y₀ ∈ C.openTube)
    (hproj₀ : NormalTotal.proj (C.inv y₀) = x) : tcfdSet E C ND i ∈ 𝓝 y₀ := by
  have hcont : ContinuousAt (fun y => NormalTotal.proj (C.inv y)) y₀ :=
    (contMDiffOn_proj_inv E C).continuousOn.continuousAt (C.openTube_isOpen.mem_nhds hy₀)
  have hpre : (fun y => NormalTotal.proj (C.inv y)) ⁻¹' (ND.D.baseSet i) ∈ 𝓝 y₀ :=
    hcont.preimage_mem_nhds ((ND.D.isOpen_baseSet i).mem_nhds (by rw [hproj₀]; exact hx))
  exact Filter.inter_mem (C.openTube_isOpen.mem_nhds hy₀) hpre

/-- The second component of the tube coordinates is differentiable at a point of the open tube. -/
theorem hasFDerivAt_vec_inv (E : EmbeddingData V (8 + k)) {ε : ℝ} (C : TubeChart E ε)
    {y₀ : Work.Tubular.Euc (8 + k)} (hy₀ : y₀ ∈ C.openTube) :
    ∃ L2 : Work.Tubular.Euc (8 + k) →L[ℝ] Work.Tubular.Euc (8 + k),
      HasFDerivAt (fun y => NormalTotal.vec (C.inv y)) L2 y₀ := by
  have hca := (contMDiffOn_vec_inv E C).contMDiffAt (C.openTube_isOpen.mem_nhds hy₀)
  exact ⟨_, (hca.mdifferentiableAt (by norm_num)).hasMFDerivAt.hasFDerivAt⟩

/-- The chart coordinate of the foot is differentiable at a point of the open tube whose foot lies
in the base set of the normal-datum chart `i`. -/
theorem hasFDerivAt_chart_inv (E : EmbeddingData V (8 + k)) {ε : ℝ} (C : TubeChart E ε)
    (ND : NormalData V k E.e) (i : CoverIdx V k) {x : V.pt} (hx : x ∈ ND.D.baseSet i)
    {y₀ : Work.Tubular.Euc (8 + k)} (hy₀ : y₀ ∈ C.openTube)
    (hproj₀ : NormalTotal.proj (C.inv y₀) = x) :
    ∃ L1 : Work.Tubular.Euc (8 + k) →L[ℝ] Work.Tubular.Euc 8,
      HasFDerivAt (fun y => FrameSigns.chartMap V i.1 (NormalTotal.proj (C.inv y))) L1 y₀ := by
  have hcmem : (FrameSigns.chartOf V i.1).1 ∈ IsManifold.maximalAtlas (𝓡 8) ∞ V.pt :=
    IsManifold.subset_maximalAtlas (FrameSigns.chartOf V i.1).2
  have hc : ContMDiffOn (𝓡 8) (𝓡 8) ∞ (FrameSigns.chartMap V i.1)
      (FrameSigns.chartOf V i.1).1.source := contMDiffOn_of_mem_maximalAtlas hcmem
  have hfst := (contMDiffOn_proj_inv E C).mono (tcfdSet_sub_openTube E C ND i)
  have hSc : tcfdSet E C ND i ⊆
      (fun y => NormalTotal.proj (C.inv y)) ⁻¹' (FrameSigns.chartOf V i.1).1.source := by
    intro y hy
    exact ND.baseSet_sub i.1 i.2 _ (tcfdSet_sub_baseSet E C ND i y hy)
  have hcomp := hc.comp hfst hSc
  have hSnhds := tcfdSet_mem_nhds E C ND i hx hy₀ hproj₀
  have hca := hcomp.contMDiffAt hSnhds
  exact ⟨_, (hca.mdifferentiableAt (by norm_num)).hasMFDerivAt.hasFDerivAt⟩

/-! ## Two structural identities of the tube

The tubular map is `(y, v) ↦ E.e y + v`, so on the open tube one has the *exact* identity
`E.e (proj (C.inv z)) + vec (C.inv z) = z`, and on the base set of the chart `i` the normal vector is
orthogonal to the tangent frame. -/

theorem tubeMap_inv_eq (E : EmbeddingData V (8 + k)) {ε : ℝ} (C : TubeChart E ε) :
    ∀ y ∈ C.openTube,
      E.e (NormalTotal.proj (C.inv y)) + NormalTotal.vec (C.inv y) = y := by
  intro y hy
  have h := C.tubeMap_inv y (C.openTube_subset_U hy)
  simpa only [Work.Tubular.tubeMap, NormalTotal.proj, NormalTotal.vec] using h

theorem inner_tanFrame_vec_inv (E : EmbeddingData V (8 + k)) {ε : ℝ} (C : TubeChart E ε)
    (ND : NormalData V k E.e) (i : CoverIdx V k) {y : Work.Tubular.Euc (8 + k)}
    (hy : y ∈ tcfdSet E C ND i) (a : Fin 8) :
    inner ℝ (tanFrame E i (NormalTotal.proj (C.inv y)) a) (NormalTotal.vec (C.inv y)) = 0 :=
  Work.Tubular.inner_eq_zero_of_mem_normalSpace (NormalTotal.vec_mem (C.inv y))
    (tanFrame_mem_tangentSpace E ND i (tcfdSet_sub_baseSet E C ND i y hy) a)

/-! ## The coefficient formula for the derivative of the chart representative -/

/-- The derivative of the chart representative of `E.e`, evaluated on the standard basis expansion
of `v`, is the corresponding linear combination of the tangent frame. -/
theorem fderiv_chartRep_funToEuc (E : EmbeddingData V (8 + k)) (i : CoverIdx V k) (x : V.pt)
    (v : Fin 8 → ℝ) :
    fderiv ℝ (chartRep E.e (coverChart i)) (FrameSigns.chartMap V i.1 x)
        (PontryaginThom.funToEuc 8 v)
      = ∑ a, v a • tanFrame E i x a := by
  have hsingle : ∀ a : Fin 8,
      fderiv ℝ (chartRep E.e (coverChart i)) (FrameSigns.chartMap V i.1 x)
        (EuclideanSpace.single a (1 : ℝ)) = tanFrame E i x a := by
    intro a
    simp only [tanFrame, frame, FrameSigns.chartMap_apply, FrameSigns.chartOf, coverChart]
  rw [show PontryaginThom.funToEuc 8 v = ∑ a, v a • EuclideanSpace.single a 1 from
    (sum_smul_single_eq_funToEuc v).symm]
  rw [map_sum]
  exact Finset.sum_congr rfl fun a _ => by rw [map_smul, hsingle a]

theorem coeffMap_tanFrame_eq (E : EmbeddingData V (8 + k)) (i : CoverIdx V k) (x : V.pt)
    (v : Fin 8 → ℝ) :
    PontryaginThom.funToEuc (8 + k) (Grassmann.coeffMap (tanFrame E i x) v)
      = ∑ a, v a • tanFrame E i x a := by
  rw [coeffMap_eq_sum (tanFrame E i x) v, PontryaginThom.funToEuc_eucToFun]

/-! ## The orthogonality of `L2` -/

/-- The second component `L2` of the derivative of the tube coordinates is orthogonal to the tangent
frame: it is the derivative of a normal section along a varying base point, and the difference of
the varying tangent frame is infinitesimal. -/
theorem inner_tanFrame_L2 (E : EmbeddingData V (8 + k)) {ε : ℝ} (C : TubeChart E ε)
    (ND : NormalData V k E.e) (i : CoverIdx V k) {x : V.pt} (hx : x ∈ ND.D.baseSet i)
    {y₀ : Work.Tubular.Euc (8 + k)} (hy₀ : y₀ ∈ C.openTube)
    (hproj₀ : NormalTotal.proj (C.inv y₀) = x)
    (hvec₀ : NormalTotal.vec (C.inv y₀) = 0)
    (L2 : Work.Tubular.Euc (8 + k) →L[ℝ] Work.Tubular.Euc (8 + k))
    (hL2 : HasFDerivAt (fun y => NormalTotal.vec (C.inv y)) L2 y₀) :
    ∀ (u : Work.Tubular.Euc (8 + k)) (a : Fin 8), inner ℝ (tanFrame E i x a) (L2 u) = 0 := by
  intro u a
  set τ : Work.Tubular.Euc (8 + k) → Work.Tubular.Euc (8 + k) :=
    fun y => tanFrame E i (NormalTotal.proj (C.inv y)) a with hτ
  set B : Work.Tubular.Euc (8 + k) → Work.Tubular.Euc (8 + k) :=
    fun y => NormalTotal.vec (C.inv y) with hB
  set φ : Work.Tubular.Euc (8 + k) →L[ℝ] ℝ := innerSL ℝ (tanFrame E i x a) with hφ
  set Φ : Work.Tubular.Euc (8 + k) → ℝ := fun y => φ (B y) with hΦ
  have hB₀ : B y₀ = 0 := by rw [hB]; exact hvec₀
  have hτ₀ : τ y₀ = tanFrame E i x a := by rw [hτ]; simp [hproj₀]
  have hBdiff : HasFDerivAt B L2 y₀ := by rw [hB]; exact hL2
  have hφapply : ∀ w : Work.Tubular.Euc (8 + k), φ w = inner ℝ (tanFrame E i x a) w := by
    intro w
    rw [hφ, coe_innerSL_apply]
  have hΦ₀ : Φ y₀ = 0 := by
    simp [hΦ, hB₀]
  have hτc : ContinuousAt τ y₀ := by
    have hg : ContinuousAt (fun z => tanFrame E i z a) x :=
      (continuousOn_tanFrame E ND i a).continuousAt ((ND.D.isOpen_baseSet i).mem_nhds hx)
    have hg' : ContinuousAt (fun z => tanFrame E i z a) (NormalTotal.proj (C.inv y₀)) := by
      rw [hproj₀]; exact hg
    have hf : ContinuousAt (fun y => NormalTotal.proj (C.inv y)) y₀ :=
      (contMDiffOn_proj_inv E C).continuousOn.continuousAt (C.openTube_isOpen.mem_nhds hy₀)
    have hcomp : ContinuousAt ((fun z => tanFrame E i z a) ∘
        (fun y => NormalTotal.proj (C.inv y))) y₀ :=
      ContinuousAt.comp (f := fun y => NormalTotal.proj (C.inv y)) hg' hf
    simpa only [hτ, Function.comp_def] using hcomp
  have hΦd : HasFDerivAt Φ (φ.comp L2) y₀ := by
    have h1 : HasFDerivAt φ φ (B y₀) := φ.hasFDerivAt
    have h2 : HasFDerivAt (φ ∘ B) (φ.comp L2) y₀ := h1.comp y₀ hBdiff
    simpa only [hΦ, Function.comp_def] using h2
  have hΦlittle : Φ =o[𝓝 y₀] (fun y => y - y₀) := by
    refine Asymptotics.IsLittleO.of_bound (fun c hc => ?_)
    have hBb : ∀ᶠ y in 𝓝 y₀, ‖B y‖ ≤ (1 + ‖L2‖) * ‖y - y₀‖ := by
      have h1 : ∀ᶠ y in 𝓝 y₀, ‖B y - B y₀ - L2 (y - y₀)‖ ≤ 1 * ‖y - y₀‖ :=
        hBdiff.isLittleO.def one_pos
      filter_upwards [h1] with y hy
      have hb : ‖B y - B y₀‖ ≤ (1 + ‖L2‖) * ‖y - y₀‖ := by
        have hsplit : B y - B y₀ = (B y - B y₀ - L2 (y - y₀)) + L2 (y - y₀) := by abel
        rw [hsplit]
        calc ‖(B y - B y₀ - L2 (y - y₀)) + L2 (y - y₀)‖
            ≤ ‖B y - B y₀ - L2 (y - y₀)‖ + ‖L2 (y - y₀)‖ := norm_add_le _ _
          _ ≤ 1 * ‖y - y₀‖ + ‖L2‖ * ‖y - y₀‖ :=
              add_le_add hy (L2.le_opNorm (y - y₀))
          _ = (1 + ‖L2‖) * ‖y - y₀‖ := by ring
      simpa [hB₀] using hb
    have hAb : ∀ᶠ y in 𝓝 y₀, ‖τ y - τ y₀‖ ≤ c / (1 + ‖L2‖) := by
      have ht := hτc.tendsto
      rw [Metric.tendsto_nhds] at ht
      have h2 := ht (c / (1 + ‖L2‖)) (by positivity)
      filter_upwards [h2] with y hy
      rw [dist_eq_norm] at hy
      exact le_of_lt hy
    filter_upwards [tcfdSet_mem_nhds E C ND i hx hy₀ hproj₀, hAb, hBb] with y hyS hyA hyB
    have horth : Φ y = -inner ℝ (τ y - τ y₀) (B y) := by
      have h0 : inner ℝ (τ y) (B y) = 0 := by
        rw [hτ, hB]
        exact inner_tanFrame_vec_inv E C ND i hyS a
      show φ (B y) = -inner ℝ (τ y - τ y₀) (B y)
      rw [hφapply (B y), ← hτ₀, inner_sub_left, h0, zero_sub, neg_neg]
    rw [horth]
    calc ‖-inner ℝ (τ y - τ y₀) (B y)‖ = ‖inner ℝ (τ y - τ y₀) (B y)‖ := norm_neg _
      _ ≤ ‖τ y - τ y₀‖ * ‖B y‖ := norm_inner_le_norm _ _
      _ ≤ (c / (1 + ‖L2‖)) * ((1 + ‖L2‖) * ‖y - y₀‖) :=
          mul_le_mul hyA hyB (norm_nonneg _) (by positivity)
      _ = c * ‖y - y₀‖ := by field_simp
  have hΦ0 : HasFDerivAt Φ (0 : Work.Tubular.Euc (8 + k) →L[ℝ] ℝ) y₀ := by
    rw [hasFDerivAt_iff_isLittleO]
    simpa [hΦ₀] using hΦlittle
  have hkey : φ.comp L2 = 0 := hΦd.unique hΦ0
  have hval : φ (L2 u) = 0 := by
    have := congrArg (fun T : Work.Tubular.Euc (8 + k) →L[ℝ] ℝ => T u) hkey
    simpa using this
  rw [← hφapply (L2 u)]
  exact hval

/-! ## The derivative of the tube coordinates -/

theorem tubeCoordsFDeriv {V : Work.ThomBordism.Man8} {k : ℕ}
    (E : Work.ThomBordism.PontryaginThom.EmbeddingData V (8 + k))
    (ND : Work.ThomBordism.PontryaginThom.NormalData V k E.e) {ε : ℝ}
    (C : Work.Tubular.TubeChart E ε) (i : Work.ThomBordism.PontryaginThom.CoverIdx V k)
    (x : V.pt) (hx : x ∈ ND.D.baseSet i) :
    ∃ (L1 : EuclideanSpace ℝ (Fin (8 + k)) →L[ℝ] EuclideanSpace ℝ (Fin 8))
      (L2 : EuclideanSpace ℝ (Fin (8 + k)) →L[ℝ] EuclideanSpace ℝ (Fin (8 + k))),
      HasFDerivAt
        (fun z : EuclideanSpace ℝ (Fin (8 + k)) =>
          (Work.ThomBordism.FrameSigns.chartMap V i.1 (Work.Tubular.NormalTotal.proj (C.inv (E.e x + z))),
           Work.Tubular.NormalTotal.vec (C.inv (E.e x + z))))
        (L1.prod L2) 0 ∧
      (∀ u : EuclideanSpace ℝ (Fin (8 + k)),
        Work.ThomBordism.Grassmann.coeffMap (Work.ThomBordism.tanFrame E i x)
            (Work.ThomBordism.PontryaginThom.eucToFun 8 (L1 u))
          + Work.ThomBordism.PontryaginThom.eucToFun (8 + k) (L2 u)
          = Work.ThomBordism.PontryaginThom.eucToFun (8 + k) u) ∧
      (∀ (u : EuclideanSpace ℝ (Fin (8 + k))) (a : Fin 8),
        inner ℝ (Work.ThomBordism.tanFrame E i x a) (L2 u) = 0) := by
  classical
  set y₀ : Work.Tubular.Euc (8 + k) := E.e x with hy₀def
  have hproj₀ : NormalTotal.proj (C.inv y₀) = x := by
    rw [hy₀def]; exact proj_inv_embed_tcfd E C x
  have hvec₀ : NormalTotal.vec (C.inv y₀) = 0 := by
    rw [hy₀def]; exact vec_inv_embed_tcfd E C x
  have hy₀open : y₀ ∈ C.openTube := by rw [hy₀def]; exact C.mem_openTube x
  obtain ⟨L1, hL1⟩ := hasFDerivAt_chart_inv E C ND i hx hy₀open hproj₀
  obtain ⟨L2, hL2⟩ := hasFDerivAt_vec_inv E C hy₀open
  refine ⟨L1, L2, ?_, ?_, ?_⟩
  · have hshift : HasFDerivAt (fun z : Work.Tubular.Euc (8 + k) => y₀ + z)
        (ContinuousLinearMap.id ℝ (Work.Tubular.Euc (8 + k))) 0 :=
      (hasFDerivAt_id (0 : Work.Tubular.Euc (8 + k))).const_add y₀
    have h1' : HasFDerivAt (fun y => FrameSigns.chartMap V i.1 (NormalTotal.proj (C.inv y)))
        L1 (y₀ + (0 : Work.Tubular.Euc (8 + k))) := by simpa using hL1
    have h1 : HasFDerivAt
        (fun z => FrameSigns.chartMap V i.1 (NormalTotal.proj (C.inv (y₀ + z)))) L1 0 :=
      h1'.comp 0 hshift
    have h2' : HasFDerivAt (fun y => NormalTotal.vec (C.inv y))
        L2 (y₀ + (0 : Work.Tubular.Euc (8 + k))) := by simpa using hL2
    have h2 : HasFDerivAt (fun z => NormalTotal.vec (C.inv (y₀ + z))) L2 0 :=
      h2'.comp 0 hshift
    have hP := h1.prodMk h2
    simpa [hy₀def] using hP
  · have hSnhds := tcfdSet_mem_nhds E C ND i hx hy₀open hproj₀
    set D : Work.Tubular.Euc 8 →L[ℝ] Work.Tubular.Euc (8 + k) :=
      fderiv ℝ (chartRep E.e (coverChart i)) (FrameSigns.chartMap V i.1 x) with hD
    have hxS : x ∈ (coverChart i).1.source := ND.baseSet_sub i.1 i.2 x hx
    have htarget : (coverChart i).1 x ∈ (coverChart i).1.target := (coverChart i).1.map_source hxS
    have htarget' : FrameSigns.chartMap V i.1 x ∈ (coverChart i).1.target := by
      simpa only [FrameSigns.chartMap_apply, FrameSigns.chartOf, coverChart] using htarget
    have hdiff : DifferentiableAt ℝ (chartRep E.e (coverChart i)) (FrameSigns.chartMap V i.1 x) :=
      (((contDiffOn_chartRep E.e (embedding_contMDiff E) (coverChart i)).differentiableOn
          one_ne_zero) _ htarget').differentiableAt
        ((coverChart i).1.open_target.mem_nhds htarget')
    have hchartD : HasFDerivAt (chartRep E.e (coverChart i)) D (FrameSigns.chartMap V i.1 x) := by
      rw [hD]
      exact hdiff.hasFDerivAt
    have hchartD' : HasFDerivAt (chartRep E.e (coverChart i)) D
        (FrameSigns.chartMap V i.1 (NormalTotal.proj (C.inv y₀))) := by
      simpa only [hproj₀] using hchartD
    have hev : (fun y => E.e (NormalTotal.proj (C.inv y))) =ᶠ[𝓝 y₀]
        ((chartRep E.e (coverChart i)) ∘
          fun y => FrameSigns.chartMap V i.1 (NormalTotal.proj (C.inv y))) := by
      filter_upwards [hSnhds] with y hy
      have hmem : NormalTotal.proj (C.inv y) ∈ (coverChart i).1.source :=
        ND.baseSet_sub i.1 i.2 _ (tcfdSet_sub_baseSet E C ND i y hy)
      have hmap : FrameSigns.chartMap V i.1 (NormalTotal.proj (C.inv y))
          = (coverChart i).1 (NormalTotal.proj (C.inv y)) := rfl
      simp only [Function.comp_apply, chartRep, hmap, (coverChart i).1.left_inv hmem]
    have hL1e : HasFDerivAt (fun y => E.e (NormalTotal.proj (C.inv y))) (D.comp L1) y₀ :=
      (hchartD'.comp y₀ hL1).congr_of_eventuallyEq hev
    have hsum : HasFDerivAt
        (fun y => E.e (NormalTotal.proj (C.inv y)) + NormalTotal.vec (C.inv y))
        (D.comp L1 + L2) y₀ := hL1e.add hL2
    have hevTube : (fun y => E.e (NormalTotal.proj (C.inv y)) + NormalTotal.vec (C.inv y))
        =ᶠ[𝓝 y₀] id := by
      filter_upwards [C.openTube_isOpen.mem_nhds hy₀open] with y hy
      exact tubeMap_inv_eq E C y hy
    have huniq : D.comp L1 + L2 = 1 :=
      (hsum.congr_of_eventuallyEq hevTube.symm).unique (hasFDerivAt_id y₀)
    have hpt : ∀ u : Work.Tubular.Euc (8 + k), D (L1 u) + L2 u = u := by
      intro u
      have := congrArg (fun T : Work.Tubular.Euc (8 + k) →L[ℝ] Work.Tubular.Euc (8 + k) => T u)
        huniq
      simpa using this
    have hfunToEuc_inj : Function.Injective
        (PontryaginThom.funToEuc (8 + k) :
          (Fin (8 + k) → ℝ) → Work.Tubular.Euc (8 + k)) := by
      intro a b h
      have := congrArg (PontryaginThom.eucToFun (8 + k)) h
      simpa [PontryaginThom.eucToFun_funToEuc] using this
    intro u
    refine hfunToEuc_inj ?_
    have hstep : PontryaginThom.funToEuc (8 + k) (Grassmann.coeffMap (tanFrame E i x)
        (PontryaginThom.eucToFun 8 (L1 u))) = D (L1 u) := by
      rw [coeffMap_tanFrame_eq E i x (PontryaginThom.eucToFun 8 (L1 u)),
        ← fderiv_chartRep_funToEuc E i x (PontryaginThom.eucToFun 8 (L1 u)),
        PontryaginThom.funToEuc_eucToFun, hD]
    rw [map_add, PontryaginThom.funToEuc_eucToFun, hstep, hpt u,
      PontryaginThom.funToEuc_eucToFun]
  · intro u a
    exact inner_tanFrame_L2 E C ND i hx hy₀open hproj₀ hvec₀ L2 hL2 u a

end

end Work.ThomBordism.KeyLocal
