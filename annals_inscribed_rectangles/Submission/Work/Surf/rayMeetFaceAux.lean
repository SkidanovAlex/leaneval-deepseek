import Mathlib
import Submission.Work.Surf.defs

/-!
# Copies of the face machinery of `Submission/Work/Surf/smooth_reduction.lean`

`Submission/Work/Surf/smooth_reduction.lean` imports `Submission.Work.Surf.ncard_rayMeet_persist`
(the target of the present development), so that file cannot be imported here.  The lemmas below
re-establish, under the namespace `Work.Surf.RayMeetAux`, the parametrisation of the boundary of the
unit square by its four faces together with the determinant and inner-product estimates needed by
`Work.Surf.ncard_rayMeet_persist`.
-/


namespace Work.Surf.RayMeetAux

open Set

noncomputable section

/-- The first basis vector of the plane. -/
def e0 : EuclideanSpace ℝ (Fin 2) := EuclideanSpace.single 0 1

/-- The second basis vector of the plane. -/
def e1 : EuclideanSpace ℝ (Fin 2) := EuclideanSpace.single 1 1

lemma coord_decomp (x : EuclideanSpace ℝ (Fin 2)) : x = x 0 • e0 + x 1 • e1 := by
  ext j; fin_cases j <;> simp [e0, e1]

lemma norm_e0 : ‖e0‖ = 1 := by simp [e0]
lemma norm_e1 : ‖e1‖ = 1 := by simp [e1]

/-- The bottom face `{(t,0)}`. -/
abbrev faceBot (t : ℝ) : EuclideanSpace ℝ (Fin 2) := t • e0
/-- The top face `{(t,1)}`. -/
abbrev faceTop (t : ℝ) : EuclideanSpace ℝ (Fin 2) := t • e0 + e1
/-- The left face `{(0,t)}`. -/
abbrev faceLft (t : ℝ) : EuclideanSpace ℝ (Fin 2) := t • e1
/-- The right face `{(1,t)}`. -/
abbrev faceRgt (t : ℝ) : EuclideanSpace ℝ (Fin 2) := e0 + t • e1

/-- The four faces, indexed by `Fin 4`. -/
abbrev faceOf (i : Fin 4) (t : ℝ) : EuclideanSpace ℝ (Fin 2) :=
  if i.val = 0 then faceBot t else if i.val = 1 then faceTop t
    else if i.val = 2 then faceLft t else faceRgt t

/-- The direction in which `faceOf i` runs. -/
def faceDir (i : Fin 4) : EuclideanSpace ℝ (Fin 2) := if i.val ≤ 1 then e0 else e1

lemma faceOf_mem_sqBox (i : Fin 4) (t : ℝ) : faceOf i t ∈ sqBox ↔ t ∈ Icc 0 1 := by
  fin_cases i <;> simp [faceOf, faceBot, faceTop, faceLft, faceRgt, sqBox, e0, e1]

lemma faceOf_mem_sqBdry (i : Fin 4) (t : ℝ) (ht : t ∈ Icc 0 1) : faceOf i t ∈ sqBdry := by
  refine ⟨(faceOf_mem_sqBox i t).mpr ht, ?_⟩
  fin_cases i <;> simp [faceOf, faceBot, faceTop, faceLft, faceRgt, sqBox, sqBdry, e0, e1]

lemma faceOf_injective (i : Fin 4) : Function.Injective (faceOf i) := by
  intro a b h
  fin_cases i
  · simpa [faceOf, faceBot, e0] using congrArg (fun x : EuclideanSpace ℝ (Fin 2) => x 0) h
  · simpa [faceOf, faceTop, e0, e1] using congrArg (fun x : EuclideanSpace ℝ (Fin 2) => x 0) h
  · simpa [faceOf, faceLft, e1] using congrArg (fun x : EuclideanSpace ℝ (Fin 2) => x 1) h
  · simpa [faceOf, faceRgt, e0, e1] using congrArg (fun x : EuclideanSpace ℝ (Fin 2) => x 1) h

lemma sqBdry_subset_iUnion_face : sqBdry ⊆ ⋃ i, faceOf i '' Icc 0 1 := by
  intro x hx
  obtain ⟨hxbox, hdisj⟩ := hx
  rcases hdisj with h | h | h | h
  · refine mem_iUnion.mpr ⟨2, x 1, hxbox.2, ?_⟩
    have hx' : x = x 1 • e1 := by ext j; fin_cases j <;> simp [h, e0, e1]
    exact (show faceOf 2 (x 1) = x 1 • e1 by simp [faceOf, faceLft]).trans hx'.symm
  · refine mem_iUnion.mpr ⟨3, x 1, hxbox.2, ?_⟩
    have hx' : x = e0 + x 1 • e1 := by ext j; fin_cases j <;> simp [h, e0, e1]
    exact (show faceOf 3 (x 1) = e0 + x 1 • e1 by simp [faceOf, faceRgt]).trans hx'.symm
  · refine mem_iUnion.mpr ⟨0, x 0, hxbox.1, ?_⟩
    have hx' : x = x 0 • e0 := by ext j; fin_cases j <;> simp [h, e0, e1]
    exact (show faceOf 0 (x 0) = x 0 • e0 by simp [faceOf, faceBot]).trans hx'.symm
  · refine mem_iUnion.mpr ⟨1, x 0, hxbox.1, ?_⟩
    have hx' : x = x 0 • e0 + e1 := by ext j; fin_cases j <;> simp [h, e0, e1]
    exact (show faceOf 1 (x 0) = x 0 • e0 + e1 by simp [faceOf, faceTop]).trans hx'.symm

lemma hasDerivAt_faceOf (i : Fin 4) (t : ℝ) : HasDerivAt (faceOf i) (faceDir i) t := by
  have h0 : HasDerivAt faceBot e0 t := by
    simpa [faceBot] using (hasDerivAt_id t).smul_const e0
  have h1 : HasDerivAt faceTop e0 t := by
    simpa [faceTop] using ((hasDerivAt_id t).smul_const e0).add_const e1
  have h2 : HasDerivAt faceLft e1 t := by
    simpa [faceLft] using (hasDerivAt_id t).smul_const e1
  have h3 : HasDerivAt faceRgt e1 t := by
    simpa [faceRgt] using ((hasDerivAt_id t).smul_const e1).const_add e0
  fin_cases i
  · show HasDerivAt faceBot e0 t; exact h0
  · show HasDerivAt faceTop e0 t; exact h1
  · show HasDerivAt faceLft e1 t; exact h2
  · show HasDerivAt faceRgt e1 t; exact h3

lemma fderiv_faceOf (i : Fin 4) (t : ℝ) :
    fderiv ℝ (faceOf i) t = ContinuousLinearMap.toSpanSingleton ℝ (faceDir i) :=
  (hasDerivAt_faceOf i t).hasFDerivAt.fderiv

lemma norm_fderiv_faceOf_le (i : Fin 4) (t : ℝ) : ‖fderiv ℝ (faceOf i) t‖ ≤ 1 := by
  rw [fderiv_faceOf, ContinuousLinearMap.norm_toSpanSingleton]
  fin_cases i <;> simp [faceDir, norm_e0, norm_e1]

/-- The determinant as a continuous linear functional of its first argument. -/
def det2CLM (v : EuclideanSpace ℝ (Fin 2)) : EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ :=
  (v 1) • (PiLp.proj 2 (fun _ : Fin 2 => ℝ) 0) - (v 0) • (PiLp.proj 2 (fun _ : Fin 2 => ℝ) 1)

lemma det2CLM_apply (v u : EuclideanSpace ℝ (Fin 2)) : det2CLM v u = Work.Drive.det2 u v := by
  simp only [det2CLM, sub_apply, smul_apply, PiLp.proj_apply, Work.Drive.det2]
  ring

/-- The derivative of `s ↦ det2 (G (faceOf i s)) v`. -/
lemma deriv_det2_faceOf (G : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2))
    (hG : ContDiff ℝ 1 G) (v : EuclideanSpace ℝ (Fin 2)) (i : Fin 4) (t : ℝ) :
    deriv (fun s => Work.Drive.det2 (G (faceOf i s)) v) t
      = Work.Drive.det2 (fderiv ℝ G (faceOf i t) (faceDir i)) v := by
  have h1 : HasDerivAt (fun s => G (faceOf i s))
      ((fderiv ℝ G (faceOf i t)) (faceDir i)) t := by
    have hd : DifferentiableAt ℝ G (faceOf i t) := (hG.differentiable (by norm_num)).differentiableAt
    simpa [Function.comp_def] using hd.hasFDerivAt.comp_hasDerivAt t (hasDerivAt_faceOf i t)
  have h2 : HasDerivAt (fun s => Work.Drive.det2 (G (faceOf i s)) v)
      (Work.Drive.det2 ((fderiv ℝ G (faceOf i t)) (faceDir i)) v) t := by
    simpa [Function.comp_def, det2CLM_apply] using
      (ContinuousLinearMap.hasFDerivAt (det2CLM v)).comp_hasDerivAt t h1
  exact h2.deriv

/-- `fderiv` of `H ∘ faceOf i`. -/
lemma fderiv_comp_faceOf (H : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2))
    (hH : ContDiff ℝ 1 H) (i : Fin 4) (t : ℝ) :
    fderiv ℝ (fun s => H (faceOf i s)) t
      = (fderiv ℝ H (faceOf i t)).comp (fderiv ℝ (faceOf i) t) := by
  simpa [Function.comp_def] using fderiv_comp (𝕜 := ℝ) t (f := faceOf i) (g := H)
    ((hH.differentiable (by norm_num)).differentiableAt)
    ((hasDerivAt_faceOf i t).differentiableAt)

/-- Closeness of `fderiv` on the boundary transfers to the parametrised faces. -/
lemma norm_fderiv_comp_faceOf_sub_le (F G : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2))
    (hF : ContDiff ℝ 1 F) (hG : ContDiff ℝ 1 G) (i : Fin 4) (t : ℝ) {δ : ℝ}
    (h : ‖fderiv ℝ G (faceOf i t) - fderiv ℝ F (faceOf i t)‖ ≤ δ) :
    ‖fderiv ℝ (fun s => G (faceOf i s)) t - fderiv ℝ (fun s => F (faceOf i s)) t‖ ≤ δ := by
  rw [fderiv_comp_faceOf G hG i t, fderiv_comp_faceOf F hF i t, fderiv_faceOf]
  have hsplit : (fderiv ℝ G (faceOf i t)).comp (ContinuousLinearMap.toSpanSingleton ℝ (faceDir i)) -
      (fderiv ℝ F (faceOf i t)).comp (ContinuousLinearMap.toSpanSingleton ℝ (faceDir i))
      = ((fderiv ℝ G (faceOf i t)) - fderiv ℝ F (faceOf i t)).comp
          (ContinuousLinearMap.toSpanSingleton ℝ (faceDir i)) := by
    ext w; simp
  rw [hsplit]
  refine (ContinuousLinearMap.opNorm_comp_le _ _).trans ?_
  rw [ContinuousLinearMap.norm_toSpanSingleton]
  have hdir : ‖faceDir i‖ = 1 := by fin_cases i <;> simp [faceDir, norm_e0, norm_e1]
  rw [hdir, mul_one]
  exact h


/-- `w` lies on the open ray spanned by `v`. -/
def IsPosRay (v w : EuclideanSpace ℝ (Fin 2)) : Prop := Work.Drive.det2 w v = 0 ∧ 0 < inner ℝ w v

lemma exists_smul_of_det2_eq_zero {w v : EuclideanSpace ℝ (Fin 2)} (hv : v ≠ 0)
    (h : Work.Drive.det2 w v = 0) : ∃ c : ℝ, w = c • v := by
  refine ⟨(w 0 * v 0 + w 1 * v 1) / (v 0 ^ 2 + v 1 ^ 2), ?_⟩
  have hv' : v 0 ^ 2 + v 1 ^ 2 ≠ 0 := by
    intro hz
    have h0 : v 0 = 0 := by nlinarith [sq_nonneg (v 0), sq_nonneg (v 1), hz]
    have h1 : v 1 = 0 := by nlinarith [sq_nonneg (v 0), sq_nonneg (v 1), hz]
    exact hv (by rw [coord_decomp v, h0, h1]; simp)
  have hden : (0:ℝ) < v 0 ^ 2 + v 1 ^ 2 :=
    lt_of_le_of_ne (by positivity) (Ne.symm hv')
  have hh : w 0 * v 1 - w 1 * v 0 = 0 := h
  ext j
  fin_cases j
  · show w 0 = ((w 0 * v 0 + w 1 * v 1) / (v 0 ^ 2 + v 1 ^ 2)) * v 0
    rw [div_mul_eq_mul_div, eq_div_iff hden.ne']
    linear_combination (v 1) * hh
  · show w 1 = ((w 0 * v 0 + w 1 * v 1) / (v 0 ^ 2 + v 1 ^ 2)) * v 1
    rw [div_mul_eq_mul_div, eq_div_iff hden.ne']
    linear_combination (-(v 0)) * hh

lemma isPosRay_iff {v w : EuclideanSpace ℝ (Fin 2)} (hv : v ≠ 0) :
    IsPosRay v w ↔ ∃ r : ℝ, 0 < r ∧ w = r • v := by
  constructor
  · rintro ⟨hg, hh⟩
    obtain ⟨c, hc⟩ := exists_smul_of_det2_eq_zero hv hg
    refine ⟨c, ?_, hc⟩
    have h2 : inner ℝ w v = c * inner ℝ v v := by rw [hc, inner_smul_left]; simp
    have h3 : 0 < inner ℝ v v := real_inner_self_pos.mpr hv
    rw [h2] at hh
    rcases (mul_pos_iff.mp hh) with ⟨hc, _⟩ | ⟨hc, hneg⟩
    · exact hc
    · linarith
  · rintro ⟨r, hr, rfl⟩
    refine ⟨?_, ?_⟩
    · simp only [Work.Drive.det2, Work.Drive.smul_apply']
      ring
    · rw [inner_smul_left]
      exact mul_pos hr (real_inner_self_pos.mpr hv)

lemma rayMeet_eq_isPosRay (F : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2))
    {v : EuclideanSpace ℝ (Fin 2)} (hv : v ≠ 0) :
    rayMeet F v = {x | IsPosRay v (F x)} := by
  ext x
  exact (isPosRay_iff hv).symm

lemma coord0_faceBot (t : ℝ) : (faceBot t : EuclideanSpace ℝ (Fin 2)) 0 = t := by simp [faceBot, e0]
lemma coord1_faceBot (t : ℝ) : (faceBot t : EuclideanSpace ℝ (Fin 2)) 1 = 0 := by simp [faceBot, e0]
lemma coord0_faceTop (t : ℝ) : (faceTop t : EuclideanSpace ℝ (Fin 2)) 0 = t := by simp [faceTop, e0, e1]
lemma coord1_faceTop (t : ℝ) : (faceTop t : EuclideanSpace ℝ (Fin 2)) 1 = 1 := by simp [faceTop, e0, e1]
lemma coord0_faceLft (t : ℝ) : (faceLft t : EuclideanSpace ℝ (Fin 2)) 0 = 0 := by simp [faceLft, e1]
lemma coord1_faceLft (t : ℝ) : (faceLft t : EuclideanSpace ℝ (Fin 2)) 1 = t := by simp [faceLft, e1]
lemma coord0_faceRgt (t : ℝ) : (faceRgt t : EuclideanSpace ℝ (Fin 2)) 0 = 1 := by simp [faceRgt, e0, e1]
lemma coord1_faceRgt (t : ℝ) : (faceRgt t : EuclideanSpace ℝ (Fin 2)) 1 = t := by simp [faceRgt, e0, e1]

/-- The four possible values of `i : Fin 4`. -/
lemma fin4_eq {i : Fin 4} : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by
  fin_cases i <;> simp

lemma continuous_faceBot : Continuous (faceBot : ℝ → EuclideanSpace ℝ (Fin 2)) := by
  unfold faceBot; fun_prop
lemma continuous_faceTop : Continuous (faceTop : ℝ → EuclideanSpace ℝ (Fin 2)) := by
  unfold faceTop; fun_prop
lemma continuous_faceLft : Continuous (faceLft : ℝ → EuclideanSpace ℝ (Fin 2)) := by
  unfold faceLft; fun_prop
lemma continuous_faceRgt : Continuous (faceRgt : ℝ → EuclideanSpace ℝ (Fin 2)) := by
  unfold faceRgt; fun_prop

lemma continuous_faceOf (i : Fin 4) : Continuous (faceOf i) := by
  rcases fin4_eq (i := i) with h | h | h | h
  · rw [h]; show Continuous faceBot; exact continuous_faceBot
  · rw [h]; show Continuous faceTop; exact continuous_faceTop
  · rw [h]; show Continuous faceLft; exact continuous_faceLft
  · rw [h]; show Continuous faceRgt; exact continuous_faceRgt

/-- At an interior parameter of a face, the corresponding boundary point is not a corner. -/
lemma faceOf_image_Ioo_subset_sqBdry (i : Fin 4) : faceOf i '' Ioo 0 1 ⊆ sqBdry := by
  rintro x ⟨t, ht, rfl⟩
  exact faceOf_mem_sqBdry i t ⟨le_of_lt ht.1, le_of_lt ht.2⟩

lemma faceOf_image_Ioo_disjoint {i j : Fin 4} (hij : i ≠ j) :
    Disjoint (faceOf i '' Ioo 0 1) (faceOf j '' Ioo 0 1) := by
  rw [Set.disjoint_left]
  intro x hx hy
  obtain ⟨a, ha, rfl⟩ := hx
  obtain ⟨b, hb, hb'⟩ := hy
  simp only [Set.mem_Ioo] at ha hb
  fin_cases i <;> fin_cases j
  all_goals
    first
      | exact absurd rfl hij
      | (have h0 := congrArg (fun y : EuclideanSpace ℝ (Fin 2) => y 0) hb'
         have h1 := congrArg (fun y : EuclideanSpace ℝ (Fin 2) => y 1) hb'
         simp [faceOf, faceBot, faceTop, faceLft, faceRgt, e0, e1] at h0 h1
         try linarith)

lemma exists_pos_le_norm_of_isCompact {W : ℝ → EuclideanSpace ℝ (Fin 2)} (hW : Continuous W)
    {K : Set ℝ} (hK : IsCompact K) (hne : K.Nonempty) (h : ∀ t ∈ K, W t ≠ 0) :
    ∃ m : ℝ, 0 < m ∧ ∀ t ∈ K, m ≤ ‖W t‖ := by
  obtain ⟨x, hxK, hxmin⟩ := hK.exists_isMinOn hne (continuous_norm.comp hW).continuousOn
  exact ⟨‖W x‖, norm_pos_iff.mpr (h x hxK), fun t ht => hxmin ht⟩

lemma ncard_union_four {α : Type*} {A B C D : Set α} (hAB : Disjoint A B) (hAC : Disjoint A C)
    (hAD : Disjoint A D) (hBC : Disjoint B C) (hBD : Disjoint B D) (hCD : Disjoint C D)
    (hA : A.Finite) (hB : B.Finite) (hC : C.Finite) (hD : D.Finite) :
    (A ∪ B ∪ C ∪ D).ncard = A.ncard + B.ncard + C.ncard + D.ncard := by
  rw [show A ∪ B ∪ C ∪ D = (A ∪ B) ∪ (C ∪ D) by
    ext x; simp only [mem_union]; tauto]
  rw [ncard_union_eq ?_ (hA.union hB) (hC.union hD), ncard_union_eq hAB hA hB,
    ncard_union_eq hCD hC hD]
  · ring
  · rw [Set.disjoint_left]
    intro x hx hy
    simp only [Set.mem_union] at hx hy
    rcases hx with hx | hx <;> rcases hy with hy | hy
    · exact Set.disjoint_left.mp hAC hx hy
    · exact Set.disjoint_left.mp hAD hx hy
    · exact Set.disjoint_left.mp hBC hx hy
    · exact Set.disjoint_left.mp hBD hx hy


/-! ## The ray sets on the faces -/

/-- The parameters `t ∈ [0,1]` at which `H` takes a value on the ray through `v` at the point
`faceOf i t` of the `i`-th face of the square. -/
def faceRaySet (H : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2))
    (v : EuclideanSpace ℝ (Fin 2)) (i : Fin 4) : Set ℝ :=
  {t : ℝ | t ∈ Icc 0 1 ∧ IsPosRay v (H (faceOf i t))}

lemma faceOf_image_faceRaySet_subset {H : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2)}
    {v : EuclideanSpace ℝ (Fin 2)} (hv : v ≠ 0) (i : Fin 4) :
    faceOf i '' faceRaySet H v i ⊆ rayMeet H v ∩ sqBdry := by
  rintro x ⟨t, ht, rfl⟩
  exact ⟨(isPosRay_iff hv).mp ht.2, faceOf_mem_sqBdry i t ht.1⟩

lemma rayMeet_inter_sqBdry_subset {H : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2)}
    {v : EuclideanSpace ℝ (Fin 2)} (hv : v ≠ 0) :
    rayMeet H v ∩ sqBdry ⊆ ⋃ i, faceOf i '' faceRaySet H v i := by
  rintro x ⟨hx, hxb⟩
  have hxb' : x ∈ ⋃ i, faceOf i '' Icc 0 1 := sqBdry_subset_iUnion_face hxb
  rw [mem_iUnion] at hxb'
  obtain ⟨i, hi⟩ := hxb'
  obtain ⟨t, ht, rfl⟩ := hi
  exact mem_iUnion.mpr ⟨i, t, ⟨ht, (isPosRay_iff hv).mpr hx⟩, rfl⟩

lemma rayMeet_inter_sqBdry_eq_iUnion {H : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2)}
    {v : EuclideanSpace ℝ (Fin 2)} (hv : v ≠ 0) :
    rayMeet H v ∩ sqBdry = ⋃ i, faceOf i '' faceRaySet H v i :=
  Subset.antisymm (rayMeet_inter_sqBdry_subset hv)
    (iUnion_subset fun i => faceOf_image_faceRaySet_subset hv i)

lemma ncard_rayMeet_inter_sqBdry {H : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2)}
    {v : EuclideanSpace ℝ (Fin 2)} (hv : v ≠ 0)
    (hvar : ∀ i, faceRaySet H v i ⊆ Ioo 0 1) (hfin : ∀ i, (faceRaySet H v i).Finite) :
    (rayMeet H v ∩ sqBdry).ncard = ∑ i : Fin 4, (faceRaySet H v i).ncard := by
  rw [rayMeet_inter_sqBdry_eq_iUnion hv,
    Set.ncard_iUnion_of_finite (fun i => (hfin i).image (faceOf i))
      (fun i j hij => (faceOf_image_Ioo_disjoint hij).mono (Set.image_mono (hvar i))
        (Set.image_mono (hvar j))),
    finsum_eq_sum_of_fintype]
  exact Finset.sum_congr rfl fun i _ => Set.ncard_image_of_injective _ (faceOf_injective i)


/-! ## The boundary is compact; positivity of the norm on compact pieces -/

lemma isCompact_sqBdry : IsCompact sqBdry := by
  have h : sqBdry = ⋃ i, faceOf i '' Icc 0 1 := by
    refine Subset.antisymm sqBdry_subset_iUnion_face ?_
    exact iUnion_subset fun i => fun x ⟨t, ht, htx⟩ => htx ▸ faceOf_mem_sqBdry i t ht
  rw [h]
  exact isCompact_iUnion fun i => isCompact_Icc.image (continuous_faceOf i)

lemma sqBdry_nonempty : sqBdry.Nonempty :=
  ⟨faceOf 0 0, faceOf_mem_sqBdry 0 0 ⟨le_refl 0, zero_le_one⟩⟩

/-- A strictly positive continuous function on a compact set is bounded below by a positive
constant. -/
lemma exists_pos_le_of_isCompact_of_pos {α : Type*} [TopologicalSpace α] {f : α → ℝ}
    {K : Set α} (hf : Continuous f) (hK : IsCompact K) (hpos : ∀ x ∈ K, 0 < f x) :
    ∃ c : ℝ, 0 < c ∧ ∀ x ∈ K, c ≤ f x := by
  rcases K.eq_empty_or_nonempty with rfl | hne
  · exact ⟨1, one_pos, by simp⟩
  · obtain ⟨x, hxK, hxmin⟩ := hK.exists_isMinOn hne hf.continuousOn
    exact ⟨f x, hpos x hxK, fun t ht => hxmin ht⟩

lemma faceDir_eq_e0_of_le {i : Fin 4} (h : i.val ≤ 1) : faceDir i = e0 := by
  simp [faceDir, h]

lemma faceDir_eq_e1_of_gt {i : Fin 4} (h : ¬ i.val ≤ 1) : faceDir i = e1 := by
  simp [faceDir, h]

lemma faceOf_not_corner {i : Fin 4} {t : ℝ} (ht : t ∈ Ioo 0 1) :
    ¬ (((faceOf i t) 0 = 0 ∨ (faceOf i t) 0 = 1) ∧
       ((faceOf i t) 1 = 0 ∨ (faceOf i t) 1 = 1)) := by
  rcases fin4_eq (i := i) with h | h | h | h
  · subst h
    rw [show faceOf 0 t = faceBot t from rfl, coord0_faceBot, coord1_faceBot]
    rintro ⟨h1, -⟩
    rcases h1 with h1 | h1 <;> linarith [ht.1, ht.2]
  · subst h
    rw [show faceOf 1 t = faceTop t from rfl, coord0_faceTop, coord1_faceTop]
    rintro ⟨h1, -⟩
    rcases h1 with h1 | h1 <;> linarith [ht.1, ht.2]
  · subst h
    rw [show faceOf 2 t = faceLft t from rfl, coord0_faceLft, coord1_faceLft]
    rintro ⟨-, h1⟩
    rcases h1 with h1 | h1 <;> linarith [ht.1, ht.2]
  · subst h
    rw [show faceOf 3 t = faceRgt t from rfl, coord0_faceRgt, coord1_faceRgt]
    rintro ⟨-, h1⟩
    rcases h1 with h1 | h1 <;> linarith [ht.1, ht.2]

/-- On the bottom or top face the second coordinate is  `0` or `1`. -/
lemma faceDir_eq_e0_of_coord_one {i : Fin 4} {t : ℝ} (ht : t ∈ Ioo 0 1)
    (h : (faceOf i t) 1 = 0 ∨ (faceOf i t) 1 = 1) : faceDir i = e0 := by
  rcases fin4_eq (i := i) with h0 | h0 | h0 | h0
  · subst h0; simp [faceDir]
  · subst h0; simp [faceDir]
  · subst h0; exfalso
    rw [show faceOf 2 t = faceLft t from rfl, coord1_faceLft] at h
    rcases h with h | h <;> linarith [ht.1, ht.2]
  · subst h0; exfalso
    rw [show faceOf 3 t = faceRgt t from rfl, coord1_faceRgt] at h
    rcases h with h | h <;> linarith [ht.1, ht.2]

/-- On the left or right face the first coordinate is `0` or `1`. -/
lemma faceDir_eq_e1_of_coord_zero {i : Fin 4} {t : ℝ} (ht : t ∈ Ioo 0 1)
    (h : (faceOf i t) 0 = 0 ∨ (faceOf i t) 0 = 1) : faceDir i = e1 := by
  rcases fin4_eq (i := i) with h0 | h0 | h0 | h0
  · subst h0; exfalso
    rw [show faceOf 0 t = faceBot t from rfl, coord0_faceBot] at h
    rcases h with h | h <;> linarith [ht.1, ht.2]
  · subst h0; exfalso
    rw [show faceOf 1 t = faceTop t from rfl, coord0_faceTop] at h
    rcases h with h | h <;> linarith [ht.1, ht.2]
  · subst h0; simp [faceDir]
  · subst h0; simp [faceDir]

/-! ## Minima over a finite set of reals -/

/-- The minimum of `f` over the finite set `S`, with the fallback value `1` for the empty set. -/
noncomputable def finf (S : Finset ℝ) (f : ℝ → ℝ) : ℝ :=
  if h : S.Nonempty then (S.image f).min' (Finset.image_nonempty.mpr h) else 1

lemma finf_pos {S : Finset ℝ} {f : ℝ → ℝ} (hf : ∀ s ∈ S, 0 < f s) : 0 < finf S f := by
  rw [finf]
  split_ifs with h
  · obtain ⟨a, ha, hae⟩ := Finset.mem_image.mp (Finset.min'_mem (S.image f) _)
    rw [← hae]
    exact hf a ha
  · exact one_pos

lemma finf_le {S : Finset ℝ} {f : ℝ → ℝ} {s : ℝ} (hs : s ∈ S) : finf S f ≤ f s := by
  rw [finf]
  split_ifs with h
  · exact Finset.min'_le _ _ (Finset.mem_image.mpr ⟨s, hs, rfl⟩)
  · exact absurd ⟨s, hs⟩ h


lemma abs_det2_le (u v : EuclideanSpace ℝ (Fin 2)) :
    |Work.Drive.det2 u v| ≤ (|v 0| + |v 1|) * ‖u‖ := by
  rw [Work.Drive.det2]
  calc |u 0 * v 1 - u 1 * v 0| ≤ |u 0 * v 1| + |u 1 * v 0| := abs_sub _ _
    _ = |u 0| * |v 1| + |u 1| * |v 0| := by rw [abs_mul, abs_mul]
    _ ≤ ‖u‖ * |v 1| + ‖u‖ * |v 0| := by
        gcongr
        · simpa using PiLp.norm_apply_le u 0
        · simpa using PiLp.norm_apply_le u 1
    _ = (|v 0| + |v 1|) * ‖u‖ := by ring

lemma deriv_det2 (W : ℝ → EuclideanSpace ℝ (Fin 2)) (hW : ContDiff ℝ 1 W)
    (v : EuclideanSpace ℝ (Fin 2)) (t : ℝ) :
    deriv (fun s => Work.Drive.det2 (W s) v) t = Work.Drive.det2 (fderiv ℝ W t 1) v := by
  have h2 : HasDerivAt W ((fderiv ℝ W t) 1) t :=
    ((hW.differentiable (by norm_num)).differentiableAt.hasFDerivAt).hasDerivAt
  have h3 : HasDerivAt (fun s => Work.Drive.det2 (W s) v)
      (Work.Drive.det2 ((fderiv ℝ W t) 1) v) t := by
    simpa [Function.comp_def, det2CLM_apply] using
      (ContinuousLinearMap.hasFDerivAt (det2CLM v)).comp_hasDerivAt t h2
  exact h3.deriv

lemma norm_sub_le_of_fderiv_bound {W : ℝ → EuclideanSpace ℝ (Fin 2)} (hW : ContDiff ℝ 1 W)
    {C : ℝ} (hC : ∀ t ∈ Icc 0 1, ‖fderiv ℝ W t‖ ≤ C) {t s : ℝ}
    (ht : t ∈ Icc 0 1) (hs : s ∈ Icc 0 1) : ‖W t - W s‖ ≤ C * |t - s| := by
  have h := Convex.norm_image_sub_le_of_norm_hasFDerivWithin_le (𝕜 := ℝ)
    (f := W) (s := Icc 0 1) (x := s) (y := t) (C := C)
    (f' := fun x => fderiv ℝ W x)
    (fun x _ => ((hW.differentiable (by norm_num)).differentiableAt.hasFDerivAt).hasFDerivWithinAt)
    (fun x hx => hC x hx) (convex_Icc 0 1) hs ht
  exact h

lemma abs_inner_sub_le {W : ℝ → EuclideanSpace ℝ (Fin 2)} (hW : ContDiff ℝ 1 W)
    {C : ℝ} (hC : ∀ t ∈ Icc 0 1, ‖fderiv ℝ W t‖ ≤ C)
    (v : EuclideanSpace ℝ (Fin 2)) {t s : ℝ} (ht : t ∈ Icc 0 1) (hs : s ∈ Icc 0 1) :
    |inner ℝ (W t) v - inner ℝ (W s) v| ≤ C * ‖v‖ * |t - s| := by
  have h := Convex.norm_image_sub_le_of_norm_hasFDerivWithin_le (𝕜 := ℝ)
    (f := fun u => inner ℝ (W u) v) (s := Icc 0 1) (x := s) (y := t) (C := C * ‖v‖)
    (f' := fun x => ContinuousLinearMap.toSpanSingleton ℝ (inner ℝ ((fderiv ℝ W x) 1) v))
    (fun x hx => by
      have hd : HasDerivAt (fun u => W u) ((fderiv ℝ W x) 1) x :=
        ((hW.differentiable (by norm_num)).differentiableAt.hasFDerivAt).hasDerivAt
      have hinner : HasDerivAt (fun u => inner ℝ (W u) v) (inner ℝ ((fderiv ℝ W x) 1) v) x := by
        have := hd.inner ℝ (hasDerivAt_const x v)
        simpa using this
      exact hinner.hasFDerivAt.hasFDerivWithinAt)
    (fun x hx => by
      rw [ContinuousLinearMap.norm_toSpanSingleton]
      calc ‖inner ℝ ((fderiv ℝ W x) 1) v‖ ≤ ‖(fderiv ℝ W x) 1‖ * ‖v‖ := norm_inner_le_norm _ _
        _ ≤ ‖fderiv ℝ W x‖ * ‖v‖ := by
            gcongr
            calc ‖(fderiv ℝ W x) 1‖ ≤ ‖fderiv ℝ W x‖ * ‖(1:ℝ)‖ := ContinuousLinearMap.le_opNorm _ _
              _ = ‖fderiv ℝ W x‖ := by simp
        _ ≤ C * ‖v‖ := by gcongr; exact hC x hx)
    (convex_Icc 0 1) hs ht
  exact h



end

end Work.Surf.RayMeetAux
