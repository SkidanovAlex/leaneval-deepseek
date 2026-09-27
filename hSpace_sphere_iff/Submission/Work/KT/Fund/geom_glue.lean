import Mathlib
import Submission.Work.KT.Defs
import Submission.Work.KT.Fund.Geom

/-!
# `Work.KT.Fund.geom_glue` — gluing functions along the two-disc decomposition of `S²`

`S² ⊂ ℂ × ℝ` is the union of its two closed hemispheres, each of which is the image of the closed
unit disc `Ball ℂ` under the homeomorphism `up` (third coordinate `+√(1-‖v‖²)`) resp. `dn`
(third coordinate `-√(1-‖v‖²)`).

* `base y` is the point of the disc obtained by forgetting the third coordinate of `y ∈ S²`.  It is
  a continuous section of both parametrisations: `base (up v) = v` and `base (dn v) = v`, while
  conversely `up (base y) = y` for `y₂ ≥ 0` and `dn (base y) = y` for `y₂ ≤ 0`.  Hence each of
  `up`, `dn` is a bijection from the disc onto its hemisphere and the two hemispheres cover `S²`.

* `glueFun gp gm` is the candidate glued function: it is `gp` read through `up` where the third
  coordinate of `y` is nonnegative, and `gm` read through `dn` elsewhere.  It is continuous because
  the two closed hemispheres cover `X × S²` and on their intersection (the equator, where
  `‖base y‖ = 1`) the hypothesis `bdryRestrict X gp = bdryRestrict X gm` makes the two formulas
  agree.

Together with `Work.KT.Fund.bdryRestrict_pullUp_eq_pullDn` this identifies `C(X × S², ℂ)` with the
fibre product of two copies of `C(X × Ball ℂ, ℂ)` over `C(X × Sph ℂ, ℂ)`.
-/

namespace Work.KT.Fund

noncomputable section

open Classical

/-! ## The disc coordinates of a point of `S²` -/

/-- The point of `ℂ` obtained by forgetting the third coordinate of `y ∈ S² ⊂ ℂ × ℝ`.  It lies in
the closed unit disc because `‖basePt y‖² = 1 - y₂²`. -/
def basePt (y : S2) : ℂ :=
  (((y : EuclideanSpace ℝ (Fin 3)) 0 : ℝ) : ℂ) +
    (((y : EuclideanSpace ℝ (Fin 3)) 1 : ℝ) : ℂ) * Complex.I

lemma basePt_re (y : S2) : (basePt y).re = ((y : EuclideanSpace ℝ (Fin 3)) 0 : ℝ) := by
  simp [basePt]

lemma basePt_im (y : S2) : (basePt y).im = ((y : EuclideanSpace ℝ (Fin 3)) 1 : ℝ) := by
  simp [basePt]

lemma norm_basePt_sq (y : S2) :
    ‖basePt y‖ ^ 2 = 1 - ((y : EuclideanSpace ℝ (Fin 3)) 2) ^ 2 := by
  have h := Metric.mem_sphere.mp y.2
  rw [dist_eq_norm, sub_zero] at h
  have h2 := EuclideanSpace.real_norm_sq_eq (y : EuclideanSpace ℝ (Fin 3))
  rw [Fin.sum_univ_three, h] at h2
  rw [Complex.sq_norm, Complex.normSq_apply, basePt_re, basePt_im]
  nlinarith [h2]

lemma norm_basePt_le_one (y : S2) : ‖basePt y‖ ≤ 1 := by
  have h := norm_basePt_sq y
  nlinarith [norm_nonneg (basePt y), sq_nonneg ((y : EuclideanSpace ℝ (Fin 3)) 2),
    sq_nonneg (‖basePt y‖ - 1)]

/-- Forgetting the third coordinate, as a point of the closed unit disc. -/
def base (y : S2) : Ball ℂ :=
  ⟨basePt y, mem_closedBall_zero_iff.mpr (norm_basePt_le_one y)⟩

lemma continuous_base : Continuous base := by
  apply Continuous.subtype_mk
  unfold basePt
  fun_prop

lemma mk3_basePt (y : S2) :
    mk3 (basePt y) ((y : EuclideanSpace ℝ (Fin 3)) 2) = (y : EuclideanSpace ℝ (Fin 3)) := by
  apply PiLp.ext
  intro i
  fin_cases i <;> simp [basePt, mk3]

lemma up_apply_two (v : Ball ℂ) :
    ((up v : S2) : EuclideanSpace ℝ (Fin 3)) 2 = Real.sqrt (1 - ‖(v : ℂ)‖ ^ 2) := by
  simp [up, upPt, mk3]

lemma dn_apply_two (v : Ball ℂ) :
    ((dn v : S2) : EuclideanSpace ℝ (Fin 3)) 2 = -(Real.sqrt (1 - ‖(v : ℂ)‖ ^ 2)) := by
  simp [dn, dnPt, mk3]

/-- `base` is a section of the upper hemisphere parametrisation. -/
lemma base_up (v : Ball ℂ) : base (up v) = v := by
  apply Subtype.ext
  apply Complex.ext <;> simp [base, basePt, up, upPt, mk3]

/-- `base` is a section of the lower hemisphere parametrisation. -/
lemma base_dn (v : Ball ℂ) : base (dn v) = v := by
  apply Subtype.ext
  apply Complex.ext <;> simp [base, basePt, dn, dnPt, mk3]

/-- On the closed upper hemisphere, `up ∘ base` is the identity. -/
lemma up_base (y : S2) (hy : 0 ≤ (y : EuclideanSpace ℝ (Fin 3)) 2) : up (base y) = y := by
  apply Subtype.ext
  have hsq : Real.sqrt (1 - ‖basePt y‖ ^ 2) = (y : EuclideanSpace ℝ (Fin 3)) 2 := by
    rw [show (1 : ℝ) - ‖basePt y‖ ^ 2 = ((y : EuclideanSpace ℝ (Fin 3)) 2) ^ 2 by
      rw [norm_basePt_sq y]; ring, Real.sqrt_sq hy]
  show upPt (base y) = (y : EuclideanSpace ℝ (Fin 3))
  simp only [upPt, base]
  rw [hsq]
  exact mk3_basePt y

/-- On the closed lower hemisphere, `dn ∘ base` is the identity. -/
lemma dn_base (y : S2) (hy : (y : EuclideanSpace ℝ (Fin 3)) 2 ≤ 0) : dn (base y) = y := by
  apply Subtype.ext
  have hsq : -(Real.sqrt (1 - ‖basePt y‖ ^ 2)) = (y : EuclideanSpace ℝ (Fin 3)) 2 := by
    rw [show (1 : ℝ) - ‖basePt y‖ ^ 2 = ((y : EuclideanSpace ℝ (Fin 3)) 2) ^ 2 by
      rw [norm_basePt_sq y]; ring, Real.sqrt_sq_eq_abs, abs_of_nonpos hy]
    ring
  show dnPt (base y) = (y : EuclideanSpace ℝ (Fin 3))
  simp only [dnPt, base]
  rw [hsq]
  exact mk3_basePt y

/-- On the equator `base` lands in the boundary circle of the disc. -/
lemma norm_base_eq_one_of_coord_eq_zero (y : S2) (hy : (y : EuclideanSpace ℝ (Fin 3)) 2 = 0) :
    ‖(base y : ℂ)‖ = 1 := by
  have h : ‖(base y : ℂ)‖ ^ 2 = 1 := by
    rw [show ‖(base y : ℂ)‖ ^ 2 = ‖basePt y‖ ^ 2 from rfl, norm_basePt_sq y, hy]
    ring
  nlinarith [norm_nonneg (base y : ℂ)]

/-- The boundary agreement hypothesis, read on the disc: two functions on `X × Ball ℂ` whose
boundary restrictions agree take the same value at `(x, v)` whenever `‖v‖ = 1`. -/
lemma gp_eq_gm_of_norm_one {X : Type} [TopologicalSpace X] {gp gm : C(X × Ball ℂ, ℂ)}
    (h : bdryRestrict X gp = bdryRestrict X gm) {v : Ball ℂ} (hv : ‖(v : ℂ)‖ = 1) (x : X) :
    gp (x, v) = gm (x, v) := by
  have hv' : (v : ℂ) ∈ Metric.sphere (0 : ℂ) 1 := by
    rw [Metric.mem_sphere, dist_eq_norm, sub_zero]; exact hv
  have hpt := DFunLike.congr_fun h (x, (⟨(v : ℂ), hv'⟩ : Sph ℂ))
  simp only [bdryRestrict_apply] at hpt
  have hsph : sphIncl (⟨(v : ℂ), hv'⟩ : Sph ℂ) = v := Subtype.ext rfl
  rwa [hsph] at hpt

/-! ## The glued function on `X × S²` -/

section Glue

variable {X : Type} [TopologicalSpace X]

/-- The candidate glued function: `gp` read through `up` on the closed upper hemisphere, `gm` read
through `dn` on the closed lower hemisphere. -/
def glueFun (gp gm : C(X × Ball ℂ, ℂ)) (p : X × S2) : ℂ :=
  if 0 ≤ ((p.2 : S2) : EuclideanSpace ℝ (Fin 3)) 2 then gp (p.1, base p.2)
  else gm (p.1, base p.2)

lemma continuous_coord : Continuous (fun p : X × S2 =>
    ((p.2 : S2) : EuclideanSpace ℝ (Fin 3)) 2) := by fun_prop

/-- `glueFun gp gm` is continuous: the two closed hemispheres cover `X × S²`, it agrees with the
continuous function `p ↦ gp (p.1, base p.2)` on the closed upper hemisphere and with
`p ↦ gm (p.1, base p.2)` on the closed lower one, where it remains equal to the latter also on the
equator because there the two formulas agree by the boundary hypothesis. -/
lemma continuous_glueFun (gp gm : C(X × Ball ℂ, ℂ))
    (h : bdryRestrict X gp = bdryRestrict X gm) : Continuous (glueFun gp gm) := by
  have hgp : Continuous (fun p : X × S2 => gp (p.1, base p.2)) :=
    gp.continuous.comp (Continuous.prodMk continuous_fst (continuous_base.comp continuous_snd))
  have hgm : Continuous (fun p : X × S2 => gm (p.1, base p.2)) :=
    gm.continuous.comp (Continuous.prodMk continuous_fst (continuous_base.comp continuous_snd))
  have hA : IsClosed {p : X × S2 | 0 ≤ ((p.2 : S2) : EuclideanSpace ℝ (Fin 3)) 2} :=
    isClosed_le continuous_const continuous_coord
  have hB : IsClosed {p : X × S2 | ((p.2 : S2) : EuclideanSpace ℝ (Fin 3)) 2 ≤ 0} :=
    isClosed_le continuous_coord continuous_const
  have hfA : ContinuousOn (glueFun gp gm)
      {p : X × S2 | 0 ≤ ((p.2 : S2) : EuclideanSpace ℝ (Fin 3)) 2} :=
    hgp.continuousOn.congr (fun p hp => by
      have hp' : 0 ≤ ((p.2 : S2) : EuclideanSpace ℝ (Fin 3)) 2 := hp
      simp only [glueFun, if_pos hp'])
  have hfB : ContinuousOn (glueFun gp gm)
      {p : X × S2 | ((p.2 : S2) : EuclideanSpace ℝ (Fin 3)) 2 ≤ 0} :=
    hgm.continuousOn.congr (fun p hp => by
      have hp' : ((p.2 : S2) : EuclideanSpace ℝ (Fin 3)) 2 ≤ 0 := hp
      by_cases h0 : 0 ≤ ((p.2 : S2) : EuclideanSpace ℝ (Fin 3)) 2
      · have hz : ((p.2 : S2) : EuclideanSpace ℝ (Fin 3)) 2 = 0 := le_antisymm hp' h0
        simp only [glueFun, if_pos h0]
        exact gp_eq_gm_of_norm_one h (norm_base_eq_one_of_coord_eq_zero p.2 hz) p.1
      · simp only [glueFun, if_neg h0])
  have hcover : {p : X × S2 | 0 ≤ ((p.2 : S2) : EuclideanSpace ℝ (Fin 3)) 2} ∪
      {p : X × S2 | ((p.2 : S2) : EuclideanSpace ℝ (Fin 3)) 2 ≤ 0} = Set.univ := by
    ext p
    simp only [Set.mem_union, Set.mem_ofPred_eq, Set.mem_univ, iff_true]
    exact (le_total (((p.2 : S2) : EuclideanSpace ℝ (Fin 3)) 2) 0).symm
  have hmain : ContinuousOn (glueFun gp gm) Set.univ := by
    have h := hfA.union_of_isClosed hfB hA hB
    rwa [hcover] at h
  exact continuousOn_univ.mp hmain

/-- On the upper hemisphere, `glueFun` pulls back to `gp`. -/
lemma glueFun_up (gp gm : C(X × Ball ℂ, ℂ)) (x : X) (v : Ball ℂ) :
    glueFun gp gm (x, up v) = gp (x, v) := by
  have hpos : 0 ≤ (((x, up v).2 : S2) : EuclideanSpace ℝ (Fin 3)) 2 := by
    rw [up_apply_two v]; exact Real.sqrt_nonneg _
  rw [glueFun, if_pos hpos, base_up]

/-- On the lower hemisphere, `glueFun` pulls back to `gm`; on the equator the two formulas agree
by the boundary hypothesis. -/
lemma glueFun_dn (gp gm : C(X × Ball ℂ, ℂ)) (h : bdryRestrict X gp = bdryRestrict X gm)
    (x : X) (v : Ball ℂ) : glueFun gp gm (x, dn v) = gm (x, v) := by
  by_cases hnn : 0 ≤ (((x, dn v).2 : S2) : EuclideanSpace ℝ (Fin 3)) 2
  · rw [glueFun, if_pos hnn, base_dn]
    rw [dn_apply_two] at hnn
    have hs : Real.sqrt (1 - ‖(v : ℂ)‖ ^ 2) = 0 :=
      le_antisymm (neg_nonneg.mp hnn) (Real.sqrt_nonneg _)
    have hx : 0 ≤ 1 - ‖(v : ℂ)‖ ^ 2 := by
      have := ball_norm_le_one v
      nlinarith [norm_nonneg (v : ℂ)]
    have h0 : (1 : ℝ) - ‖(v : ℂ)‖ ^ 2 = 0 := by
      rw [← Real.sq_sqrt hx, hs]; ring
    have hv : ‖(v : ℂ)‖ = 1 := by
      nlinarith [norm_nonneg (v : ℂ), ball_norm_le_one v]
    exact gp_eq_gm_of_norm_one h hv x
  · rw [glueFun, if_neg hnn, base_dn]

end Glue

/-- The gluing property of the two-disc decomposition of `S²`: a pair of continuous functions on the two hemispheres (viewed as discs) whose restrictions to the boundary circle agree is the pair of restrictions of a unique continuous function on `X × S²`.  Together with `Work.KT.Fund.bdryRestrict_pullUp_eq_pullDn` this identifies `C(X × S², ℂ)` with the fibre product of two copies of `C(X × Ball ℂ, ℂ)` over `C(X × Sph ℂ, ℂ)`.  Route: the two hemispheres are closed and cover `S²` (they are the images of the closed disc under the homeomorphisms `up`, `dn`), the glued function defined by `g (x, y) = gp (x, up⁻¹ y)` on the upper hemisphere and `g (x, y) = gm (x, dn⁻¹ y)` on the lower is well defined by the boundary agreement, and continuity follows on the closed cover. -/
theorem geom_glue (X : Type) [TopologicalSpace X] [CompactSpace X] [T2Space X]
    (gp gm : C(X × Ball ℂ, ℂ)) (h : bdryRestrict X gp = bdryRestrict X gm) :
    ∃! g : C(X × S2, ℂ), pullUp X g = gp ∧ pullDn X g = gm := by
  have hcont := continuous_glueFun gp gm h
  have hUp : pullUp X (⟨glueFun gp gm, hcont⟩ : C(X × S2, ℂ)) = gp := by
    ext p
    simp only [pullUp_apply]
    exact glueFun_up gp gm p.1 p.2
  have hDn : pullDn X (⟨glueFun gp gm, hcont⟩ : C(X × S2, ℂ)) = gm := by
    ext p
    simp only [pullDn_apply]
    exact glueFun_dn gp gm h p.1 p.2
  refine ⟨⟨glueFun gp gm, hcont⟩, ⟨hUp, hDn⟩, ?_⟩
  rintro g' ⟨hg'U, hg'D⟩
  ext p
  rcases p with ⟨x, y⟩
  rcases le_total (((y : S2) : EuclideanSpace ℝ (Fin 3)) 2) 0 with hle | hge
  · have hy : dn (base y) = y := dn_base y hle
    calc g' (x, y) = pullDn X g' (x, base y) := by simp only [pullDn_apply, hy]
      _ = gm (x, base y) := by simp only [hg'D]
      _ = pullDn X (⟨glueFun gp gm, hcont⟩ : C(X × S2, ℂ)) (x, base y) := by simp only [hDn]
      _ = (⟨glueFun gp gm, hcont⟩ : C(X × S2, ℂ)) (x, y) := by simp only [pullDn_apply, hy]
  · have hy : up (base y) = y := up_base y hge
    calc g' (x, y) = pullUp X g' (x, base y) := by simp only [pullUp_apply, hy]
      _ = gp (x, base y) := by simp only [hg'U]
      _ = pullUp X (⟨glueFun gp gm, hcont⟩ : C(X × S2, ℂ)) (x, base y) := by simp only [hUp]
      _ = (⟨glueFun gp gm, hcont⟩ : C(X × S2, ℂ)) (x, y) := by simp only [pullUp_apply, hy]

end

end Work.KT.Fund
