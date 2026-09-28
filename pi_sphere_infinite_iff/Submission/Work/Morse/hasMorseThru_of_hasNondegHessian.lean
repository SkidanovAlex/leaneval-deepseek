import Mathlib
import Submission.Work.Morse.Basic
import Submission.Work.Morse.morse_lemma
import Submission.Work.Morse.Transfer
import Submission.Work.Morse.mem_maximalAtlas_trans

set_option synthInstance.maxHeartbeats 400000

namespace Work.Morse

open scoped Manifold ContDiff Topology
open Set Filter Metric

/-! ## Two auxiliary facts

The proof of the Morse lemma in this workspace (`Work.Morse.morse_lemma_general`) applies to a
function which is `C^∞` on the whole model space.  The chart expression of `f` at `x` is only
smooth on a neighbourhood of `x`, so we globalise it by multiplying with a bump function which is
`1` near the origin. -/

/-- The product of a `C^∞` function whose topological support is contained in an open set `V` with
a function which is only `C^∞` on `V` is globally `C^∞`. -/
private lemma contDiff_mul_of_contDiffOn_of_tsupport_subset {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {F χ : E → ℝ} {V : Set E} (hV : IsOpen V) (hχ : ContDiff ℝ ∞ χ)
    (hF : ContDiffOn ℝ ∞ F V) (hsub : tsupport χ ⊆ V) :
    ContDiff ℝ ∞ fun z => χ z * F z := by
  rw [contDiff_iff_contDiffAt]
  intro z
  by_cases hz : z ∈ tsupport χ
  · exact hχ.contDiffAt.mul (hF.contDiffAt (hV.mem_nhds (hsub hz)))
  · refine (contDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq ?_
    refine Filter.eventually_of_mem ((isClosed_tsupport χ).isOpen_compl.mem_nhds hz) ?_
    intro y hy
    simp [image_eq_zero_of_notMem_tsupport hy]

/-- A function which is `C^∞` on a neighbourhood of the origin agrees, on a neighbourhood of the
origin, with a globally `C^∞` function. -/
private lemma exists_contDiff_eventuallyEq_of_contDiffOn {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] {F : E → ℝ} {U : Set E}
    (hU : U ∈ 𝓝 (0 : E)) (hF : ContDiffOn ℝ ∞ F U) :
    ∃ F' : E → ℝ, ContDiff ℝ ∞ F' ∧ F' =ᶠ[𝓝 0] F := by
  obtain ⟨d, hd, hdU⟩ := Metric.nhds_basis_closedBall.mem_iff.mp hU
  let b : ContDiffBump (0 : E) :=
    { rIn := d / 4, rOut := d / 2, rIn_pos := by linarith, rIn_lt_rOut := by linarith }
  have hbR : b.rOut = d / 2 := rfl
  have hsub : tsupport (↑b) ⊆ interior U := by
    rw [b.tsupport_eq]
    have h1 : closedBall (0 : E) b.rOut ⊆ ball (0 : E) d :=
      closedBall_subset_ball (by rw [hbR]; linarith)
    have h2 : ball (0 : E) d ⊆ interior U :=
      interior_maximal (ball_subset_closedBall.trans hdU) isOpen_ball
    exact h1.trans h2
  refine ⟨fun z => b z * F z, ?_, ?_⟩
  · exact contDiff_mul_of_contDiffOn_of_tsupport_subset isOpen_interior b.contDiff
      (hF.mono interior_subset) hsub
  · have h1 : ∀ᶠ z in 𝓝 (0 : E), b z = 1 := b.eventuallyEq_one
    filter_upwards [h1] with z hz
    simp [hz]

/-- A smooth function with a nondegenerate critical point in the sense of `HasNondegHessian` has a
chart in which `f - f x` is *exactly* a nondegenerate quadratic form: this is the classical Morse
lemma, packaging the chart provided by `Work.Morse.morse_lemma_general`. -/
theorem hasMorseThru_of_hasNondegHessian {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    {f : M → ℝ} (hf : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ f) {x : M}
    (h : HasNondegHessian (I := 𝓡 n) (n := ∞) f x) :
    HasMorseThru (n := n) f x := by
  obtain ⟨e, he, hx, hd, hnd⟩ := h
  set c : EuclideanSpace ℝ (Fin n) := e x with hc
  set g : EuclideanSpace ℝ (Fin n) → ℝ := fun y => f (e.symm y) with hg
  have hctgt : c ∈ e.target := by rw [hc]; exact e.map_source hx
  -- ## The chart expression of `f` is smooth on `e.target`
  have hgs : ContDiffOn ℝ ∞ g e.target := by
    have hsymm : ContMDiffOn (𝓡 n) (𝓡 n) ∞ (⇑e.symm) e.target :=
      contMDiffOn_symm_of_mem_maximalAtlas he
    have hcomp : ContMDiffOn (𝓡 n) 𝓘(ℝ, ℝ) ∞ g e.target := by
      rw [hg]; exact hf.comp_contMDiffOn hsymm
    exact (contMDiffOn_iff_contDiffOn).mp hcomp
  -- ## and its first two derivatives vanish / are nondegenerate at `c`
  have hd' : fderiv ℝ g c = 0 := by
    rw [hg, hc]; simpa using hd
  have hnd' : ∀ v : EuclideanSpace ℝ (Fin n),
      (∀ w, (fderiv ℝ (fderiv ℝ g) c) v w = 0) → v = 0 := by
    intro v hv
    rw [hg] at hv
    apply hnd v
    intro w
    have hw := hv w
    rw [hc] at hw
    simpa using hw
  have hgc : g c = f x := by
    simp only [hg, hc]
    rw [e.left_inv hx]
  -- ## The model function whose critical point is at the origin
  set F : EuclideanSpace ℝ (Fin n) → ℝ := fun z => g (z + c) - g c with hF
  have hF0 : F 0 = 0 := by simp only [hF, zero_add, sub_self]
  have hFsmooth : ContDiffOn ℝ ∞ F ((fun z : EuclideanSpace ℝ (Fin n) => z + c) ⁻¹' e.target) := by
    simp only [hF]
    exact (hgs.comp ((contDiff_id.add contDiff_const).contDiffOn) (fun z hz => hz)).sub
      contDiffOn_const
  have hFgrad : fderiv ℝ F 0 = 0 := by
    simp only [hF]
    rw [fderiv_sub_const, fderiv_comp_add_right, zero_add]
    exact hd'
  have hFhess : fderiv ℝ (fderiv ℝ F) 0 = fderiv ℝ (fderiv ℝ g) c := by
    have hFf : fderiv ℝ F = fun z => fderiv ℝ g (z + c) := by
      funext z
      simp only [hF]
      rw [fderiv_sub_const, fderiv_comp_add_right]
    rw [hFf]
    simpa using (fderiv_comp_add_right (𝕜 := ℝ) (f := fderiv ℝ g)
      (x := (0 : EuclideanSpace ℝ (Fin n))) c)
  have hUnhds : ((fun z : EuclideanSpace ℝ (Fin n) => z + c) ⁻¹' e.target)
      ∈ 𝓝 (0 : EuclideanSpace ℝ (Fin n)) := by
    have hcont : Continuous (fun z : EuclideanSpace ℝ (Fin n) => z + c) :=
      continuous_id.add continuous_const
    refine hcont.continuousAt.preimage_mem_nhds ?_
    rw [zero_add]
    exact e.open_target.mem_nhds hctgt
  -- ## Globalise and apply the Morse lemma
  obtain ⟨F', hF'sm, hF'eq⟩ := exists_contDiff_eventuallyEq_of_contDiffOn hUnhds hFsmooth
  have hF'0 : F' 0 = 0 := by rw [hF'eq.eq_of_nhds, hF0]
  have hF'grad : fderiv ℝ F' 0 = 0 := by rw [hF'eq.fderiv_eq, hFgrad]
  have hF'hess : fderiv ℝ (fderiv ℝ F') 0 = fderiv ℝ (fderiv ℝ g) c := by
    rw [hF'eq.fderiv.fderiv_eq, hFhess]
  have hF'nd : ∀ v : EuclideanSpace ℝ (Fin n),
      (∀ w, (fderiv ℝ (fderiv ℝ F') 0) v w = 0) → v = 0 := by
    intro v hv
    rw [hF'hess] at hv
    exact hnd' v hv
  obtain ⟨ψ, hψ0mem, hψ0, hψsm, hψsymm, hψid⟩ :=
    morse_lemma_general hF'sm hF'0 hF'grad hF'nd
  have hψ0tgt : (0 : EuclideanSpace ℝ (Fin n)) ∈ ψ.target := hψ0 ▸ ψ.map_source hψ0mem
  -- ## The chart on `M` obtained by composing `e` with the Morse chart, translated to `x`
  set t : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin n)) (EuclideanSpace ℝ (Fin n)) :=
    (Homeomorph.subRight c).toOpenPartialHomeomorph.trans ψ with ht
  set ê : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n)) := e.trans t with hê
  -- the translation `z ↦ z - c`, encoded as an open partial homeomorphism, is smooth with smooth
  -- inverse, hence an element of the groupoid
  have hsub_symm : ⇑((Homeomorph.subRight c).toOpenPartialHomeomorph).symm
      = fun w : EuclideanSpace ℝ (Fin n) => w + c := by
    funext w
    show (Homeomorph.subRight c).symm w = w + c
    exact Homeomorph.subRight_symm_apply c w
  have hτmem : (Homeomorph.subRight c).toOpenPartialHomeomorph ∈ contDiffGroupoid ∞ (𝓡 n) := by
    refine (mem_contDiffGroupoid_self_iff (E' := EuclideanSpace ℝ (Fin n))).mpr ⟨?_, ?_⟩
    · rw [Homeomorph.toOpenPartialHomeomorph_source, contDiffOn_univ,
        Homeomorph.toOpenPartialHomeomorph_apply, Homeomorph.coe_subRight]
      exact contDiff_id.sub contDiff_const
    · rw [Homeomorph.toOpenPartialHomeomorph_target, contDiffOn_univ, hsub_symm]
      exact contDiff_id.add contDiff_const
  have hψmem : ψ ∈ contDiffGroupoid ∞ (𝓡 n) :=
    (mem_contDiffGroupoid_self_iff (E' := EuclideanSpace ℝ (Fin n))).mpr ⟨hψsm, hψsymm⟩
  have htmem : t ∈ contDiffGroupoid ∞ (𝓡 n) := by
    rw [ht]; exact (contDiffGroupoid ∞ (𝓡 n)).trans hτmem hψmem
  have hêmem : ê ∈ IsManifold.maximalAtlas (𝓡 n) ∞ M := by
    rw [hê]; exact mem_maximalAtlas_trans he htmem
  -- explicit descriptions of `t`
  have ht_apply : ∀ z : EuclideanSpace ℝ (Fin n),
      (t : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) z = ψ (z - c) := by
    intro z
    rw [ht, OpenPartialHomeomorph.trans_apply, Homeomorph.toOpenPartialHomeomorph_apply,
      Homeomorph.subRight_apply]
  have ht_source : t.source = (fun z : EuclideanSpace ℝ (Fin n) => z - c) ⁻¹' ψ.source := by
    rw [ht, OpenPartialHomeomorph.trans_source, Homeomorph.toOpenPartialHomeomorph_source,
      Set.univ_inter]
    congr 1
  have ht_symm_apply : ∀ z : EuclideanSpace ℝ (Fin n),
      ((t.symm : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin n))
        (EuclideanSpace ℝ (Fin n))) : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) z
        = ψ.symm z + c := by
    intro z
    rw [ht, OpenPartialHomeomorph.trans_symm_eq_symm_trans_symm,
      OpenPartialHomeomorph.trans_apply, hsub_symm]
  have hxê : x ∈ ê.source := by
    have h1 : ê.source = e.source ∩ ↑e ⁻¹' t.source := by
      rw [hê, OpenPartialHomeomorph.trans_source]
    rw [h1, Set.mem_inter_iff]
    refine ⟨hx, ?_⟩
    rw [ht_source, Set.mem_preimage]
    show (e : M → EuclideanSpace ℝ (Fin n)) x - c ∈ ψ.source
    rw [← hc, sub_self]
    exact hψ0mem
  have hê0 : ê x = 0 := by
    rw [hê, OpenPartialHomeomorph.trans_apply, ht_apply]
    rw [← hc, sub_self, hψ0]
  have hê_symm_apply : ∀ z : EuclideanSpace ℝ (Fin n),
      (ê.symm : EuclideanSpace ℝ (Fin n) → M) z = e.symm (ψ.symm z + c) := by
    intro z
    rw [hê, OpenPartialHomeomorph.trans_symm_eq_symm_trans_symm,
      OpenPartialHomeomorph.trans_apply, ht_symm_apply z]
  -- ## The quadratic form and the two remaining obligations
  refine ⟨ê, hêmem, hxê, hê0, (1 / 2 : ℝ) • fderiv ℝ (fderiv ℝ F') 0, ?_, ?_⟩
  · intro v hv
    apply hF'nd v
    intro w
    have hw := hv w
    simp only [smul_apply, smul_eq_mul] at hw
    exact (mul_eq_zero.mp hw).resolve_left (by norm_num)
  · -- the identity holds on a neighbourhood of `0`
    have hψsymm0 : ⇑ψ.symm (0 : EuclideanSpace ℝ (Fin n)) = 0 := by
      have h := ψ.left_inv hψ0mem
      rwa [hψ0] at h
    have hcontψ : ContinuousAt (⇑ψ.symm) (0 : EuclideanSpace ℝ (Fin n)) :=
      (hψsymm.contDiffAt (ψ.open_target.mem_nhds hψ0tgt)).continuousAt
    have hmemA : ψ.source ∈ 𝓝 (⇑ψ.symm (0 : EuclideanSpace ℝ (Fin n))) := by
      rw [hψsymm0]; exact ψ.open_source.mem_nhds hψ0mem
    have hA : ∀ᶠ z in 𝓝 (0 : EuclideanSpace ℝ (Fin n)), ψ.symm z ∈ ψ.source :=
      hcontψ.preimage_mem_nhds hmemA
    have hmemB : {w : EuclideanSpace ℝ (Fin n) | F' w = F w}
        ∈ 𝓝 (⇑ψ.symm (0 : EuclideanSpace ℝ (Fin n))) := by
      rw [hψsymm0]; exact hF'eq
    have hB : ∀ᶠ z in 𝓝 (0 : EuclideanSpace ℝ (Fin n)), F' (ψ.symm z) = F (ψ.symm z) :=
      hcontψ.preimage_mem_nhds hmemB
    have hC : ∀ᶠ z in 𝓝 (0 : EuclideanSpace ℝ (Fin n)), z ∈ ψ.target :=
      ψ.open_target.mem_nhds hψ0tgt
    filter_upwards [hA, hB, hC] with z hzA hzB hzC
    rw [hê_symm_apply z]
    have h2 : F (ψ.symm z) = f (e.symm (ψ.symm z + c)) - f x := by
      rw [hF, hgc]
    rw [← h2, ← hzB, hψid _ hzA, ψ.right_inv hzC]
    simp only [smul_apply, smul_eq_mul]

end Work.Morse
