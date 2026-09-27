import Mathlib
import Submission.Work.Whitney.OrientedAtlas
import Submission.Work.Whitney.PairDet
import Submission.Work.Whitney.DoubleDetC
import Submission.Work.Whitney.doubleDetC_untouched

/-!
# Comparing the signs of two double points: the transition formula and the sign choice
-/

namespace Work.Whitney

open scoped Manifold ContDiff
open Topology Filter

/-- **`pairDet` only sees the map near the two points.** -/
theorem pairDet_congr {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    {f f' : M → EuclideanSpace ℝ (Fin (2 * n))}
    (c₁ c₂ : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n))) (a b : M)
    (ha₁ : a ∈ c₁.source) (hb₂ : b ∈ c₂.source)
    (ha : f =ᶠ[𝓝 a] f') (hb : f =ᶠ[𝓝 b] f') :
    pairDet f c₁ c₂ a b = pairDet f' c₁ c₂ a b := by
  have ht₁ : Tendsto (c₁.symm : EuclideanSpace ℝ (Fin n) → M) (𝓝 (c₁ a)) (𝓝 a) := by
    simpa only [c₁.left_inv ha₁] using
      (c₁.continuousOn_symm.continuousAt
        (c₁.open_target.mem_nhds (c₁.map_source ha₁))).tendsto
  have ht₂ : Tendsto (c₂.symm : EuclideanSpace ℝ (Fin n) → M) (𝓝 (c₂ b)) (𝓝 b) := by
    simpa only [c₂.left_inv hb₂] using
      (c₂.continuousOn_symm.continuousAt
        (c₂.open_target.mem_nhds (c₂.map_source hb₂))).tendsto
  have h1 : (fun u : EuclideanSpace ℝ (Fin n) => f (c₁.symm u))
      =ᶠ[𝓝 (c₁ a)] (fun u : EuclideanSpace ℝ (Fin n) => f' (c₁.symm u)) :=
    ha.comp_tendsto ht₁
  have h2 : (fun u : EuclideanSpace ℝ (Fin n) => f (c₂.symm u))
      =ᶠ[𝓝 (c₂ b)] (fun u : EuclideanSpace ℝ (Fin n) => f' (c₂.symm u)) :=
    hb.comp_tendsto ht₂
  rw [pairDet, pairDet, h1.fderiv_eq, h2.fderiv_eq]

/-- **The transition formula for `doubleDetC`.** -/
theorem doubleDetC_transition {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    (f : M → EuclideanSpace ℝ (Fin (2 * n)))
    (c c' : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n)))
    (p q : M) (hp : p ∈ c.source) (hpd : p ∈ c'.source)
    (hq : q ∈ c.source) (hqd : q ∈ c'.source)
    (hdp : DifferentiableAt ℝ (fun v : EuclideanSpace ℝ (Fin n) => f (c.symm v)) (c p))
    (hdq : DifferentiableAt ℝ (fun v : EuclideanSpace ℝ (Fin n) => f (c.symm v)) (c q))
    (hdp' : DifferentiableAt ℝ (fun v : EuclideanSpace ℝ (Fin n) => c (c'.symm v)) (c' p))
    (hdq' : DifferentiableAt ℝ (fun v : EuclideanSpace ℝ (Fin n) => c (c'.symm v)) (c' q)) :
    doubleDetC f c' p q = doubleDetC f c p q *
      ((fderiv ℝ (fun u : EuclideanSpace ℝ (Fin n) => c (c'.symm u)) (c' p)).det *
       (fderiv ℝ (fun u : EuclideanSpace ℝ (Fin n) => c (c'.symm u)) (c' q)).det) := by
  classical
  set Φ : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) :=
    fun u => c (c'.symm u) with hΦ
  have hΦp : Φ (c' p) = c p := by
    simp only [hΦ]
    rw [c'.left_inv hpd]
  have hΦq : Φ (c' q) = c q := by
    simp only [hΦ]
    rw [c'.left_inv hqd]
  have htp : c'.symm (c' p) ∈ c.source := by rw [c'.left_inv hpd]; exact hp
  have htq : c'.symm (c' q) ∈ c.source := by rw [c'.left_inv hqd]; exact hq
  have hevp : (fun u : EuclideanSpace ℝ (Fin n) => f (c'.symm u))
      =ᶠ[𝓝 (c' p)] (fun u : EuclideanSpace ℝ (Fin n) => f (c.symm (Φ u))) := by
    have hcont := c'.continuousOn_symm.continuousAt
      (c'.open_target.mem_nhds (c'.map_source hpd))
    filter_upwards [hcont.preimage_mem_nhds (c.open_source.mem_nhds htp)] with u hu
    simp only [hΦ, Function.comp_apply]
    rw [c.left_inv hu]
  have hevq : (fun u : EuclideanSpace ℝ (Fin n) => f (c'.symm u))
      =ᶠ[𝓝 (c' q)] (fun u : EuclideanSpace ℝ (Fin n) => f (c.symm (Φ u))) := by
    have hcont := c'.continuousOn_symm.continuousAt
      (c'.open_target.mem_nhds (c'.map_source hqd))
    filter_upwards [hcont.preimage_mem_nhds (c.open_source.mem_nhds htq)] with u hu
    simp only [hΦ, Function.comp_apply]
    rw [c.left_inv hu]
  set A₁ : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin (2 * n)) :=
    fderiv ℝ (fun v : EuclideanSpace ℝ (Fin n) => f (c.symm v)) (c p) with hA₁
  set A₂ : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin (2 * n)) :=
    fderiv ℝ (fun v : EuclideanSpace ℝ (Fin n) => f (c.symm v)) (c q) with hA₂
  set T₁ : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) :=
    fderiv ℝ Φ (c' p) with hT₁
  set T₂ : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) :=
    fderiv ℝ Φ (c' q) with hT₂
  have hchainp : fderiv ℝ (fun u : EuclideanSpace ℝ (Fin n) => f (c'.symm u)) (c' p)
      = A₁.comp T₁ := by
    rw [hevp.fderiv_eq]
    rw [show (fun u : EuclideanSpace ℝ (Fin n) => f (c.symm (Φ u)))
        = (fun v : EuclideanSpace ℝ (Fin n) => f (c.symm v)) ∘ Φ from rfl]
    rw [fderiv_comp (c' p) (by rw [hΦp]; exact hdp) hdp']
    rw [hΦp, hA₁, hT₁]
  have hchainq : fderiv ℝ (fun u : EuclideanSpace ℝ (Fin n) => f (c'.symm u)) (c' q)
      = A₂.comp T₂ := by
    rw [hevq.fderiv_eq]
    rw [show (fun u : EuclideanSpace ℝ (Fin n) => f (c.symm (Φ u)))
        = (fun v : EuclideanSpace ℝ (Fin n) => f (c.symm v)) ∘ Φ from rfl]
    rw [fderiv_comp (c' q) (by rw [hΦq]; exact hdq) hdq']
    rw [hΦq, hA₂, hT₂]
  have hcop : ∀ (B₁ B₂ : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin (2 * n)))
      (S₁ S₂ : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)),
      ((B₁.comp S₁).coprod (B₂.comp S₂)).toLinearMap
        = ((B₁.coprod B₂).toLinearMap).comp ((S₁.prodMap S₂).toLinearMap) := by
    intro B₁ B₂ S₁ S₂
    apply LinearMap.ext
    rintro ⟨u, v⟩
    simp only [ContinuousLinearMap.coe_coprod, LinearMap.coprod_apply, LinearMap.prodMap_apply,
      LinearMap.comp_apply, ContinuousLinearMap.coe_prodMap]
    rfl
  have hprod : ∀ (S₁ S₂ : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)),
      (S₁.prodMap S₂).toLinearMap = LinearMap.prodMap S₁.toLinearMap S₂.toLinearMap := by
    intro S₁ S₂
    rfl
  rw [doubleDetC_def, doubleDetC_def, doubleDetRep, doubleDetRep, hchainp, hchainq,
    hcop A₁ A₂ T₁ T₂]
  simp only [← LinearMap.comp_assoc, LinearMap.det_comp, hprod, LinearMap.det_prodMap]
  ring

/-- **The sign of an inserted double point can be chosen.**  Suppose two maps `fp`, `fm` agree
with `f` near the two preimages `p₁`, `p₂` of a transverse double point `P` of `f` (compared through
charts `c₁, c₂` of an oriented atlas `A`), and suppose that at an inserted double point `Q = (p',q')`
their signs, read through one common chart `c₃ ∈ A` containing both `p'` and `q'`, are *opposite* and
nonzero.  Then exactly one of `fp`, `fm` makes `P` and `Q` have opposite signs. -/
theorem oppositeSign_or_of_neg {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    (A : Set (OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n))))
    (f fp fm : M → EuclideanSpace ℝ (Fin (2 * n)))
    (p₁ p₂ p' q' : M)
    (c₁ c₂ c₃ : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n)))
    (hc₁ : c₁ ∈ A) (hc₂ : c₂ ∈ A) (hc₃ : c₃ ∈ A)
    (hp₁ : p₁ ∈ c₁.source) (hp₂ : p₂ ∈ c₂.source)
    (hp' : p' ∈ c₃.source) (hq' : q' ∈ c₃.source)
    (hfp₁ : fp =ᶠ[𝓝 p₁] f) (hfp₂ : fp =ᶠ[𝓝 p₂] f)
    (hfm₁ : fm =ᶠ[𝓝 p₁] f) (hfm₂ : fm =ᶠ[𝓝 p₂] f)
    (hP : pairDet f c₁ c₂ p₁ p₂ ≠ 0)
    (hB : doubleDetC fp c₃ p' q' ≠ 0)
    (hflip : doubleDetC fm c₃ p' q' = - doubleDetC fp c₃ p' q') :
    Work.Whitney.OppositeSign A fp p₁ p₂ p' q' ∨
      Work.Whitney.OppositeSign A fm p₁ p₂ p' q' := by
  have e1 : pairDet fp c₁ c₂ p₁ p₂ = pairDet f c₁ c₂ p₁ p₂ :=
    pairDet_congr c₁ c₂ p₁ p₂ hp₁ hp₂ hfp₁ hfp₂
  have e2 : pairDet fm c₁ c₂ p₁ p₂ = pairDet f c₁ c₂ p₁ p₂ :=
    pairDet_congr c₁ c₂ p₁ p₂ hp₁ hp₂ hfm₁ hfm₂
  rcases lt_or_gt_of_ne (mul_ne_zero hP hB) with h | h
  · exact Or.inl ⟨c₁, c₂, c₃, c₃, hc₁, hc₂, hc₃, hc₃, hp₁, hp₂, hp', hq', by
      rw [e1, pairDet_self]; exact h⟩
  · refine Or.inr ⟨c₁, c₂, c₃, c₃, hc₁, hc₂, hc₃, hc₃, hp₁, hp₂, hp', hq', ?_⟩
    rw [e2, pairDet_self, hflip, mul_neg]
    linarith


#check @contMDiffAt_iff_contDiffAt
#check @ContMDiffAt.contDiffAt
#check @ContDiffAt.contMDiffAt
#check @contMDiff_iff_contDiff
#check @ContinuousOn.isOpen_inter_preimage
#check @IsOpen.preimage
#check @ContMDiffAt.comp
#check @DifferentiableAt.comp
end Work.Whitney
