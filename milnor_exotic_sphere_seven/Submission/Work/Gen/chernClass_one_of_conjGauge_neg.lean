import Mathlib
import Submission.Work.Gen.LineTensor
import Submission.Work.Gen.ConjIso
import Submission.Work.Gen.eulerClass_neg_of_realIso

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 1600000
set_option linter.unusedSectionVars false

/-!
# The first Chern class of the conjugate of a complex line bundle

`Work.Gen.chernClass_one_of_conjGauge_neg`: if two complex line bundles `L`, `L'` over a common
base, presented over the *same* gluing data (same base sets), differ by conjugating the transition
functions — `L'.coordChange i j x = star (scl (L.coordChange i j x)) • id`, i.e. `L' = \bar L` is
the complex conjugate bundle of `L` — then

  `c₁(L') = − c₁(L)`.

The proof is the generalised form of the concrete `ℂPⁿ` computation
(`Work.Gen.tautDual_euler_neg`/`Work.Gen.conjLine_euler_neg`): the fibrewise complex conjugation
`conj` intertwines the two gluing data, hence is a **real** isomorphism
`realification L' ≅ realification L`, and its fibrewise determinant is `−1` up to a positive
factor (orientation reversing).  The sign change of the Euler class under an orientation-reversing
isomorphism (`Work.Gen.eulerClass_neg_of_realIso`) then gives `euler(L') = − euler(L)`, and for a
line bundle the Euler class of the realification *is* `c₁` (`Work.Thom.chernClass_one_top`).
-/

namespace Work.Gen

open Work.TangentClasses Work.Thom

noncomputable section

/-- The model fibre of a complex line bundle, for brevity. -/
abbrev LineFib : Type := EuclideanSpace ℂ (Fin 1)

variable {B : Type} [TopologicalSpace B] {ι : Type}

/-! ## The scalar of a transition function -/

/-- The scalar of a transition function is multiplicative along the cocycle. -/
theorem scl_coordChange_mul (L : VectorBundleCore ℂ B LineFib ι)
    (i j k : ι) (x : B) (hx : x ∈ L.baseSet i ∩ L.baseSet j ∩ L.baseSet k) :
    scl (L.coordChange i j x) * scl (L.coordChange j k x) = scl (L.coordChange i k x) := by
  have h := scl_comp (L.coordChange j k x) (L.coordChange i j x)
  rw [L.coordChange_linear_comp i j k x hx] at h
  rw [h, mul_comm]

/-- The scalar of the transition function of a chart with itself is `1`. -/
theorem scl_coordChange_self (L : VectorBundleCore ℂ B LineFib ι)
    (i : ι) (x : B) (hx : x ∈ L.baseSet i) : scl (L.coordChange i i x) = 1 := by
  have hfun : L.coordChange i i x = ContinuousLinearMap.id ℂ LineFib := by
    apply ContinuousLinearMap.ext
    intro v
    exact L.coordChange_self i x hx v
  rw [hfun, scl_id]

/-- The scalar of a transition function is nonzero wherever it is defined. -/
theorem scl_coordChange_ne_zero (L : VectorBundleCore ℂ B LineFib ι)
    (i j : ι) (x : B) (hx : x ∈ L.baseSet i ∩ L.baseSet j) :
    scl (L.coordChange i j x) ≠ 0 := by
  have hii := scl_coordChange_self L i x hx.1
  have hmul := scl_coordChange_mul L i j i x ⟨⟨hx.1, hx.2⟩, hx.1⟩
  rw [hii] at hmul
  intro h0
  rw [h0, zero_mul] at hmul
  exact zero_ne_one hmul

/-! ## The realification in terms of the transition scalar -/

/-- The realified transition function of a complex line bundle is multiplication by its
`ℂ`-transition scalar. -/
theorem realification_coordChange_smul_id (L : VectorBundleCore ℂ B LineFib ι)
    (i j : ι) (x : B) :
    (realification L).coordChange i j x
      = (scl (L.coordChange i j x)) • ContinuousLinearMap.id ℝ LineFib := by
  apply ContinuousLinearMap.ext
  intro v
  rw [smul_apply, ContinuousLinearMap.id_apply]
  show (realification L).coordChange i j x v = scl (L.coordChange i j x) • v
  rw [show (realification L).coordChange i j x v = L.coordChange i j x v from
    congrFun (realification_coordChange L i j x) v]
  exact scl_apply (L.coordChange i j x) v

/-! ## Calculus of the elementary gauges `c • conj` and `c • id` -/

theorem line_smul_id_comp_conj (a b : ℂ) :
    (a • ContinuousLinearMap.id ℝ LineFib).comp (b • conjCLM) = (a * b) • conjCLM := by
  apply ContinuousLinearMap.ext
  intro v
  simp only [ContinuousLinearMap.comp_apply, smul_apply,
    ContinuousLinearMap.id_apply, smul_smul]

theorem line_conj_comp_smul_id (a b : ℂ) :
    (a • conjCLM).comp (b • ContinuousLinearMap.id ℝ LineFib)
      = (a * star b) • conjCLM := by
  apply ContinuousLinearMap.ext
  intro v
  simp only [ContinuousLinearMap.comp_apply, smul_apply,
    ContinuousLinearMap.id_apply, conjCLM_apply, conjLM_smul, smul_smul]

theorem line_conj_comp_conj (a b : ℂ) :
    (a • conjCLM).comp (b • conjCLM)
      = (a * star b) • ContinuousLinearMap.id ℝ LineFib := by
  apply ContinuousLinearMap.ext
  intro v
  simp only [ContinuousLinearMap.comp_apply, smul_apply,
    ContinuousLinearMap.id_apply, conjCLM_apply, conjLM_smul, conjLM_involutive, smul_smul]

/-! ## The conjugation gauges -/

/-- The gauge `scl(L.coordChange i j x) • conj` comparing the chart `i` of `realification L'`
with the chart `j` of `realification L`, for `L'` the `star`-conjugate of `L`. -/
def linePhi (L : VectorBundleCore ℂ B LineFib ι) (i j : ι) (x : B) : LineFib →L[ℝ] LineFib :=
  (scl (L.coordChange i j x)) • conjCLM

/-- The inverse gauge `(star (scl (L.coordChange i j x)))⁻¹ • conj`. -/
def linePhiInv (L : VectorBundleCore ℂ B LineFib ι) (i j : ι) (x : B) : LineFib →L[ℝ] LineFib :=
  (star (scl (L.coordChange i j x)))⁻¹ • conjCLM

theorem continuousOn_linePhi (L : VectorBundleCore ℂ B LineFib ι) (i j : ι) :
    ContinuousOn (fun b => linePhi L i j b) (L.baseSet i ∩ L.baseSet j) := by
  have h1 : ContinuousOn (fun b => scl (L.coordChange i j b)) (L.baseSet i ∩ L.baseSet j) :=
    continuous_scl.comp_continuousOn (L.continuousOn_coordChange i j)
  have hsmul : Continuous (fun a : ℂ => a • conjCLM) := continuous_id.smul continuous_const
  exact hsmul.comp_continuousOn h1

theorem continuousOn_linePhiInv (L : VectorBundleCore ℂ B LineFib ι) (i j : ι) :
    ContinuousOn (fun b => linePhiInv L i j b) (L.baseSet i ∩ L.baseSet j) := by
  have hne : ∀ b ∈ L.baseSet i ∩ L.baseSet j, star (scl (L.coordChange i j b)) ≠ 0 :=
    fun b hb => star_ne_zero.mpr (scl_coordChange_ne_zero L i j b hb)
  have h1 : ContinuousOn (fun b => (star (scl (L.coordChange i j b)))⁻¹)
      (L.baseSet i ∩ L.baseSet j) :=
    ((continuous_scl.comp_continuousOn (L.continuousOn_coordChange i j)).star).inv₀ hne
  have hsmul : Continuous (fun a : ℂ => a • conjCLM) := continuous_id.smul continuous_const
  exact hsmul.comp_continuousOn h1

/-! ## The four compatibility conditions -/

theorem linePhi_htgt (L : VectorBundleCore ℂ B LineFib ι) (i t t' : ι) (b : B)
    (hi : b ∈ L.baseSet i) (ht : b ∈ L.baseSet t) (ht' : b ∈ L.baseSet t') :
    (realification L).coordChange t t' b ∘SL linePhi L i t b = linePhi L i t' b := by
  have hx : b ∈ L.baseSet i ∩ L.baseSet t ∩ L.baseSet t' := ⟨⟨hi, ht⟩, ht'⟩
  have hsc : scl (L.coordChange t t' b) * scl (L.coordChange i t b)
      = scl (L.coordChange i t' b) := by
    rw [mul_comm]; exact scl_coordChange_mul L i t t' b hx
  rw [realification_coordChange_smul_id, linePhi, linePhi, line_smul_id_comp_conj, hsc]

theorem linePhi_hsrc (L L' : VectorBundleCore ℂ B LineFib ι)
    (h : ∀ (i j : ι) (x : B), L'.coordChange i j x
      = (star (scl (L.coordChange i j x))) • ContinuousLinearMap.id ℂ LineFib)
    (i t i' : ι) (b : B)
    (hi : b ∈ L.baseSet i) (hi' : b ∈ L.baseSet i') (ht : b ∈ L.baseSet t) :
    linePhi L i t b ∘SL (realification L').coordChange i' i b = linePhi L i' t b := by
  have hx : b ∈ L.baseSet i' ∩ L.baseSet i ∩ L.baseSet t := ⟨⟨hi', hi⟩, ht⟩
  have hsc : scl (L.coordChange i t b) * scl (L.coordChange i' i b)
      = scl (L.coordChange i' t b) := by
    rw [mul_comm]; exact scl_coordChange_mul L i' i t b hx
  rw [realification_coordChange_smul_id]
  rw [show scl (L'.coordChange i' i b) = star (scl (L.coordChange i' i b)) from by
    rw [h i' i b, scl_smul_id_eq]]
  rw [linePhi, linePhi, line_conj_comp_smul_id, star_star, hsc]

theorem linePhiInv_htgtinv (L : VectorBundleCore ℂ B LineFib ι) (i t t' : ι) (b : B)
    (hi : b ∈ L.baseSet i) (ht : b ∈ L.baseSet t) (ht' : b ∈ L.baseSet t') :
    linePhiInv L i t b ∘SL (realification L).coordChange t' t b = linePhiInv L i t' b := by
  have hx : b ∈ L.baseSet i ∩ L.baseSet t ∩ L.baseSet t' := ⟨⟨hi, ht⟩, ht'⟩
  have hxt : b ∈ L.baseSet t ∩ L.baseSet t' := ⟨ht, ht'⟩
  have hc : scl (L.coordChange i t' b)
      = scl (L.coordChange i t b) * scl (L.coordChange t t' b) :=
    (scl_coordChange_mul L i t t' b hx).symm
  have hinv : scl (L.coordChange t' t b) = (scl (L.coordChange t t' b))⁻¹ := by
    have hm := scl_coordChange_mul L t t' t b ⟨hxt, ht⟩
    rw [scl_coordChange_self L t b ht] at hm
    exact eq_inv_of_mul_eq_one_right hm
  have hsc : (star (scl (L.coordChange i t b)))⁻¹ * star (scl (L.coordChange t' t b))
      = (star (scl (L.coordChange i t' b)))⁻¹ := by
    rw [hinv, hc, star_inv₀, star_mul, mul_inv_rev]
  rw [realification_coordChange_smul_id, linePhiInv, linePhiInv, line_conj_comp_smul_id, hsc]

theorem linePhiInv_hsrcinv (L L' : VectorBundleCore ℂ B LineFib ι)
    (h : ∀ (i j : ι) (x : B), L'.coordChange i j x
      = (star (scl (L.coordChange i j x))) • ContinuousLinearMap.id ℂ LineFib)
    (i t i' : ι) (b : B)
    (hi : b ∈ L.baseSet i) (hi' : b ∈ L.baseSet i') (ht : b ∈ L.baseSet t) :
    (realification L').coordChange i i' b ∘SL linePhiInv L i t b = linePhiInv L i' t b := by
  have hx : b ∈ L.baseSet i' ∩ L.baseSet i ∩ L.baseSet t := ⟨⟨hi', hi⟩, ht⟩
  have hxii : b ∈ L.baseSet i ∩ L.baseSet i' := ⟨hi, hi'⟩
  have hc : scl (L.coordChange i' t b)
      = scl (L.coordChange i' i b) * scl (L.coordChange i t b) :=
    (scl_coordChange_mul L i' i t b hx).symm
  have hinv : (scl (L.coordChange i' i b))⁻¹ = scl (L.coordChange i i' b) := by
    have hm := scl_coordChange_mul L i i' i b ⟨hxii, hi⟩
    rw [scl_coordChange_self L i b hi] at hm
    exact inv_eq_of_mul_eq_one_left hm
  have hsc : star (scl (L.coordChange i i' b)) * (star (scl (L.coordChange i t b)))⁻¹
      = (star (scl (L.coordChange i' t b)))⁻¹ := by
    rw [← hinv, hc, star_inv₀, star_mul, mul_inv_rev]
  rw [realification_coordChange_smul_id]
  rw [show scl (L'.coordChange i i' b) = star (scl (L.coordChange i i' b)) from by
    rw [h i i' b, scl_smul_id_eq]]
  rw [linePhiInv, linePhiInv, line_smul_id_comp_conj, hsc]

theorem linePhiInv_comp_linePhi (L : VectorBundleCore ℂ B LineFib ι) (i j : ι) (b : B)
    (hx : b ∈ L.baseSet i ∩ L.baseSet j) :
    (linePhiInv L i j b).comp (linePhi L i j b) = ContinuousLinearMap.id ℝ LineFib := by
  have hne : star (scl (L.coordChange i j b)) ≠ 0 :=
    star_ne_zero.mpr (scl_coordChange_ne_zero L i j b hx)
  rw [linePhiInv, linePhi, line_conj_comp_conj, inv_mul_cancel₀ hne, one_smul]

theorem linePhi_comp_linePhiInv (L : VectorBundleCore ℂ B LineFib ι) (i j : ι) (b : B)
    (hx : b ∈ L.baseSet i ∩ L.baseSet j) :
    (linePhi L i j b).comp (linePhiInv L i j b) = ContinuousLinearMap.id ℝ LineFib := by
  have hne : scl (L.coordChange i j b) ≠ 0 := scl_coordChange_ne_zero L i j b hx
  rw [linePhiInv, linePhi, line_conj_comp_conj, star_inv₀, star_star, mul_inv_cancel₀ hne, one_smul]

/-! ## The orientation-reversing real isomorphism -/

def bundleIso_conj (L L' : VectorBundleCore ℂ B LineFib ι)
    (hbs : ∀ i : ι, L'.baseSet i = L.baseSet i)
    (h : ∀ (i j : ι) (x : B), L'.coordChange i j x
      = (star (scl (L.coordChange i j x))) • ContinuousLinearMap.id ℂ LineFib) :
    BundleIso (realification L') (realification L) :=
  bundleIsoOfGauge (realification L') (realification L) (linePhi L) (linePhiInv L)
    (fun i j => by
      rw [realification_baseSet, realification_baseSet, hbs i]
      exact continuousOn_linePhi L i j)
    (fun i j => by
      rw [realification_baseSet, realification_baseSet, hbs i]
      exact continuousOn_linePhiInv L i j)
    (fun i t t' b hi ht ht' => by
      rw [realification_baseSet] at hi
      rw [hbs i] at hi
      rw [realification_baseSet] at ht ht'
      exact linePhi_htgt L i t t' b hi ht ht')
    (fun i t i' b hi hi' ht => by
      rw [realification_baseSet] at hi hi'
      rw [hbs i] at hi
      rw [hbs i'] at hi'
      rw [realification_baseSet] at ht
      exact linePhi_hsrc L L' h i t i' b hi hi' ht)
    (fun i t t' b hi ht ht' => by
      rw [realification_baseSet] at hi ht ht'
      rw [hbs i] at hi
      exact linePhiInv_htgtinv L i t t' b hi ht ht')
    (fun i t i' b hi hi' ht => by
      rw [realification_baseSet] at hi hi' ht
      rw [hbs i] at hi
      rw [hbs i'] at hi'
      exact linePhiInv_hsrcinv L L' h i t i' b hi hi' ht)
    (fun i i' b x hb => by
      rw [realification_baseSet, realification_baseSet] at hb
      rw [hbs i] at hb
      change (linePhiInv L i i' b) ((linePhi L i i' b) x) = x
      rw [← ContinuousLinearMap.comp_apply, linePhiInv_comp_linePhi L i i' b hb,
        ContinuousLinearMap.id_apply])
    (fun i i' b y hb => by
      rw [realification_baseSet, realification_baseSet] at hb
      rw [hbs i] at hb
      change (linePhi L i i' b) ((linePhiInv L i i' b) y) = y
      rw [← ContinuousLinearMap.comp_apply, linePhi_comp_linePhiInv L i i' b hb,
        ContinuousLinearMap.id_apply])

theorem det_bundleIso_conj (L L' : VectorBundleCore ℂ B LineFib ι)
    (hbs : ∀ i : ι, L'.baseSet i = L.baseSet i)
    (h : ∀ (i j : ι) (x : B), L'.coordChange i j x
      = (star (scl (L.coordChange i j x))) • ContinuousLinearMap.id ℂ LineFib)
    (b : B) : LinearMap.det ((bundleIso_conj L L' hbs h).hom b) < 0 := by
  have hb1 : b ∈ L.baseSet (L'.indexAt b) := by
    have := L'.mem_baseSet_at b
    rwa [hbs (L'.indexAt b)] at this
  have hx : b ∈ L.baseSet (L'.indexAt b) ∩ L.baseSet (L.indexAt b) :=
    ⟨hb1, L.mem_baseSet_at b⟩
  have hne : scl (L.coordChange (L'.indexAt b) (L.indexAt b) b) ≠ 0 :=
    scl_coordChange_ne_zero L (L'.indexAt b) (L.indexAt b) b hx
  have hhom : (bundleIso_conj L L' hbs h).hom b
      = (scl (L.coordChange (L'.indexAt b) (L.indexAt b) b)) • conjLM := by
    show (linePhi L ((realification L').indexAt b) ((realification L).indexAt b) b).toLinearMap = _
    rw [realification_indexAt, realification_indexAt]
    rw [linePhi]
    rfl
  rw [hhom]
  change LinearMap.det
    ((scl (L.coordChange (L'.indexAt b) (L.indexAt b) b)) • conjLM :
      LineFib →ₗ[ℝ] LineFib) < 0
  rw [det_smul_conjLM]
  have hpos : 0 < Complex.normSq (scl (L.coordChange (L'.indexAt b) (L.indexAt b) b)) :=
    Complex.normSq_pos.mpr hne
  nlinarith

/-! ## The target lemma -/

theorem chernClass_one_of_conjGauge_neg {B : Type} [TopologicalSpace B] {ι : Type} [Fintype ι]
    (L L' : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin 1)) ι)
    (hbs : ∀ i : ι, L'.baseSet i = L.baseSet i)
    (h : ∀ (i j : ι) (x : B), L'.coordChange i j x
      = (star (Work.Gen.scl (L.coordChange i j x))) •
          ContinuousLinearMap.id ℂ (EuclideanSpace ℂ (Fin 1))) :
    Work.Thom.chernClass 1 1 L' = - Work.Thom.chernClass 1 1 L := by
  have hdet : ∀ b : B, LinearMap.det ((bundleIso_conj L L' hbs h).hom b) < 0 :=
    fun b => det_bundleIso_conj L L' hbs h b
  have key := eulerClass_neg_of_realIso (m := 1) (le_refl 1) L' L
    (bundleIso_conj L L' hbs h) hdet
  rw [chernClass_one_top L', chernClass_one_top L, key, neg_neg]

end

end Work.Gen
