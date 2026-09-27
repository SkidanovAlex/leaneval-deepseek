import Mathlib
import Submission.Work.Surf.tame_cut_parity
import Submission.Work.Surf.scpDefs
import Submission.Work.Surf.scpG_exists_regular_perturbation
import Submission.Work.Drive.boxParity

namespace Work.Surf

/-! ## Elementary facts about the bump `χ` -/

lemma scpChi_nonneg (x : EuclideanSpace ℝ (Fin 2)) : 0 ≤ scpChi x := by
  unfold scpChi scpPhi
  have h1 : 0 ≤ Real.smoothTransition (x 0) := Real.smoothTransition.nonneg (x 0)
  have h2 : 0 ≤ Real.smoothTransition (1 - x 0) := Real.smoothTransition.nonneg (1 - x 0)
  have h3 : 0 ≤ Real.smoothTransition (x 1) := Real.smoothTransition.nonneg (x 1)
  have h4 : 0 ≤ Real.smoothTransition (1 - x 1) := Real.smoothTransition.nonneg (1 - x 1)
  exact mul_nonneg (mul_nonneg h1 h2) (mul_nonneg h3 h4)

lemma scpChi_eq_zero_of_mem_sqBdry {x : EuclideanSpace ℝ (Fin 2)} (hx : x ∈ sqBdry) :
    scpChi x = 0 := by
  obtain ⟨hbox, h | h | h | h⟩ := hx
  · have hz : scpPhi (x 0) = 0 := by
      rw [scpPhi_eq_zero_iff]; exact Or.inl (le_of_eq h)
    unfold scpChi; rw [hz, zero_mul]
  · have hz : scpPhi (x 0) = 0 := by
      rw [scpPhi_eq_zero_iff]; exact Or.inr (le_of_eq h.symm)
    unfold scpChi; rw [hz, zero_mul]
  · have hz : scpPhi (x 1) = 0 := by
      rw [scpPhi_eq_zero_iff]; exact Or.inl (le_of_eq h)
    unfold scpChi; rw [hz, mul_zero]
  · have hz : scpPhi (x 1) = 0 := by
      rw [scpPhi_eq_zero_iff]; exact Or.inr (le_of_eq h.symm)
    unfold scpChi; rw [hz, mul_zero]

lemma fderiv_scpChi_eq_zero_of_mem_sqBdry {x : EuclideanSpace ℝ (Fin 2)} (hx : x ∈ sqBdry) :
    fderiv ℝ scpChi x = 0 := by
  have hmin : IsLocalMin scpChi x := Filter.Eventually.of_forall (fun y => by
    rw [scpChi_eq_zero_of_mem_sqBdry hx]; exact scpChi_nonneg y)
  exact hmin.fderiv_eq_zero

lemma scpChi_pos_of_mem_sqBox_of_notMem_sqBdry {x : EuclideanSpace ℝ (Fin 2)}
    (hx : x ∈ sqBox) (hxb : x ∉ sqBdry) : 0 < scpChi x := by
  have h0 : 0 < x 0 ∧ x 0 < 1 :=
    ⟨lt_of_le_of_ne hx.1.1 (Ne.symm fun h => hxb ⟨hx, Or.inl h⟩),
      lt_of_le_of_ne hx.1.2 fun h => hxb ⟨hx, Or.inr (Or.inl h)⟩⟩
  have h1 : 0 < x 1 ∧ x 1 < 1 :=
    ⟨lt_of_le_of_ne hx.2.1 (Ne.symm fun h => hxb ⟨hx, Or.inr (Or.inr (Or.inl h))⟩),
      lt_of_le_of_ne hx.2.2 fun h => hxb ⟨hx, Or.inr (Or.inr (Or.inr h))⟩⟩
  exact scpChi_pos_of (fun i => by fin_cases i; exact h0; exact h1)

/-! ## The perturbation vanishes on the faces of the cube -/

lemma scpPert_eq_zero_of_cutSig_eq_zero {w : EuclideanSpace ℝ (Fin 2)}
    {z : EuclideanSpace ℝ (Fin 3)} (hz : cutSig z = 0) : scpPert w z = 0 := by
  rw [scpPert_apply, hz, Work.Drive.ezPhi_zero, zero_mul, zero_smul]

lemma scpPert_eq_zero_of_mem_sqBdry {w : EuclideanSpace ℝ (Fin 2)}
    {z : EuclideanSpace ℝ (Fin 3)} (hz : cutSp z ∈ sqBdry) : scpPert w z = 0 := by
  rw [scpPert_apply, scpChi_eq_zero_of_mem_sqBdry hz, mul_zero, zero_smul]

lemma scpG_eq_cutMap_of_cutSig_eq_zero (F : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2))
    (v w : EuclideanSpace ℝ (Fin 2)) {z : EuclideanSpace ℝ (Fin 3)} (hz : cutSig z = 0) :
    scpG F v w z = cutMap F v z := by
  rw [scpG_apply, scpPert_eq_zero_of_cutSig_eq_zero hz, sub_zero, cutMap]

lemma scpG_eq_cutMap_of_mem_sqBdry (F : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2))
    (v w : EuclideanSpace ℝ (Fin 2)) {z : EuclideanSpace ℝ (Fin 3)}
    (hz : cutSp z ∈ sqBdry) : scpG F v w z = cutMap F v z := by
  rw [scpG_apply, scpPert_eq_zero_of_mem_sqBdry hz, sub_zero, cutMap]

/-! ## The derivative of the perturbation -/

lemma differentiableAt_scpPert (w : EuclideanSpace ℝ (Fin 2))
    (z : EuclideanSpace ℝ (Fin 3)) : DifferentiableAt ℝ (scpPert w) z := by
  have h : scpPert w = fun y : EuclideanSpace ℝ (Fin 3) => scpAlpha y • w := rfl
  rw [h]
  exact ((contDiff_scpAlpha.differentiable (by simp)).differentiableAt).smul_const w

lemma fderiv_scpPert_apply (w : EuclideanSpace ℝ (Fin 2)) (z u : EuclideanSpace ℝ (Fin 3)) :
    fderiv ℝ (scpPert w) z u =
      (deriv Work.Drive.ezPhi (cutSig z) * scpChi (cutSp z) * cutSig u +
        Work.Drive.ezPhi (cutSig z) * (fderiv ℝ scpChi (cutSp z) (cutSp u))) • w := by
  have hαd : DifferentiableAt ℝ scpAlpha z :=
    (contDiff_scpAlpha.differentiable (by simp)).differentiableAt
  have hφd : DifferentiableAt ℝ (fun y : EuclideanSpace ℝ (Fin 3) =>
      Work.Drive.ezPhi (cutSig y)) z :=
    ((Work.Drive.contDiff_ezPhi.differentiable (by simp)).differentiableAt).comp z
      cutSig.differentiableAt
  have hχd : DifferentiableAt ℝ (fun y : EuclideanSpace ℝ (Fin 3) => scpChi (cutSp y)) z :=
    (contDiff_scpChi.differentiable (by simp)).differentiableAt.comp z cutSp.differentiableAt
  have hsplit : scpAlpha = (fun y : EuclideanSpace ℝ (Fin 3) => Work.Drive.ezPhi (cutSig y)) *
      (fun y : EuclideanSpace ℝ (Fin 3) => scpChi (cutSp y)) := rfl
  rw [show scpPert w = fun y : EuclideanSpace ℝ (Fin 3) => scpAlpha y • w from rfl,
    fderiv_smul_const hαd w]
  rw [hsplit, fderiv_mul hφd hχd]
  rw [show (fun y : EuclideanSpace ℝ (Fin 3) => scpChi (cutSp y)) = scpChi ∘ ⇑cutSp from rfl,
    show (fun y : EuclideanSpace ℝ (Fin 3) => Work.Drive.ezPhi (cutSig y))
      = Work.Drive.ezPhi ∘ ⇑cutSig from rfl]
  rw [fderiv_comp z ((contDiff_scpChi.differentiable (by simp)).differentiableAt)
      cutSp.differentiableAt,
    fderiv_comp z ((Work.Drive.contDiff_ezPhi.differentiable (by simp)).differentiableAt)
      cutSig.differentiableAt]
  rw [cutSp.hasFDerivAt.fderiv, cutSig.hasFDerivAt.fderiv]
  simp only [ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.smul_apply, ContinuousLinearMap.comp_apply]
  rw [fderiv_eq_smul_deriv]
  simp only [smul_eq_mul]
  ring_nf

lemma fderiv_scpG_apply (F : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2))
    (hF : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) F) (v w : EuclideanSpace ℝ (Fin 2))
    (z u : EuclideanSpace ℝ (Fin 3)) :
    fderiv ℝ (scpG F v w) z u =
      fderiv ℝ F (cutSp z) (cutSp u) - cutSig u • v -
        (deriv Work.Drive.ezPhi (cutSig z) * scpChi (cutSp z) * cutSig u +
          Work.Drive.ezPhi (cutSig z) *
            (fderiv ℝ scpChi (cutSp z) (cutSp u))) • w := by
  have hcutd : DifferentiableAt ℝ (cutMap F v) z :=
    ((cut_contDiff_cutMap F v hF).differentiable (by simp)).differentiableAt
  have hpert : DifferentiableAt ℝ (scpPert w) z := differentiableAt_scpPert w z
  have hdecomp : scpG F v w = cutMap F v - scpPert w := rfl
  rw [hdecomp, fderiv_sub hcutd hpert, ContinuousLinearMap.sub_apply]
  rw [cutMap_fderiv_apply F (hF.differentiable (by simp)), fderiv_scpPert_apply]

lemma contDiff_scpG (F : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2))
    (hF : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) F) (v w : EuclideanSpace ℝ (Fin 2)) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (scpG F v w) := by
  have hA := contDiff_scpA F hF v
  have hα := contDiff_scpAlpha.smul_const w
  have h : scpG F v w = fun z => scpA F v z - scpAlpha z • w := by
    funext z; exact scpG_eq F v w z
  rw [h]
  exact hA.sub hα

/-! ## The face-restricted derivative agrees with the unperturbed family on the faces -/

lemma fderiv_scpG_apply_of_cutSig_eq_zero (F : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2))
    (hF : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) F) (v w : EuclideanSpace ℝ (Fin 2))
    {z : EuclideanSpace ℝ (Fin 3)} (hz : cutSig z = 0)
    {u : EuclideanSpace ℝ (Fin 3)} (hu : cutSig u = 0) :
    fderiv ℝ (scpG F v w) z u = fderiv ℝ (cutMap F v) z u := by
  rw [fderiv_scpG_apply F hF, cutMap_fderiv_apply F (hF.differentiable (by simp))]
  rw [hz, hu, Work.Drive.ezPhi_zero]
  simp

lemma fderiv_scpG_eq_cutMap_of_mem_sqBdry (F : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2))
    (hF : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) F) (v w : EuclideanSpace ℝ (Fin 2))
    {z : EuclideanSpace ℝ (Fin 3)} (hz : cutSp z ∈ sqBdry) :
    fderiv ℝ (scpG F v w) z = fderiv ℝ (cutMap F v) z := by
  refine ContinuousLinearMap.ext fun u => ?_
  rw [fderiv_scpG_apply F hF, cutMap_fderiv_apply F (hF.differentiable (by simp))]
  rw [scpChi_eq_zero_of_mem_sqBdry hz, fderiv_scpChi_eq_zero_of_mem_sqBdry hz]
  simp

/-! ## The face condition of `Submission.Drive.ParityProp` for the perturbed family -/

lemma mem_unitBoxBdry_of_not_interior {z : EuclideanSpace ℝ (Fin 3)}
    (hz : z ∈ Submission.Drive.unitBox 2) (hint : ¬ ∀ i : Fin 3, 0 < z i ∧ z i < 1) :
    z ∈ Submission.Drive.unitBoxBdry 2 := by
  classical
  obtain ⟨i, hi⟩ := not_forall.mp hint
  refine (cutMem_unitBoxBdry).mpr ⟨hz, i, ?_⟩
  rcases lt_or_ge (z i) 0 with h | h
  · exact absurd (hz i).1 (not_le_of_gt h)
  · by_cases h0 : z i = 0
    · exact Or.inl h0
    · refine Or.inr (le_antisymm (hz i).2 ?_)
      by_contra hlt
      exact hi ⟨lt_of_le_of_ne h (Ne.symm h0), not_le.mp hlt⟩

lemma mem_sqBdry_of_mem_unitBoxBdry {z : EuclideanSpace ℝ (Fin 3)}
    (hz : z ∈ Submission.Drive.unitBoxBdry 2) (h3 : 0 < z 0) (h4 : z 0 < 1) :
    cutSp z ∈ sqBdry := by
  obtain ⟨hzbox, i, hi⟩ := cutMem_unitBoxBdry.mp hz
  have hx : cutSp z ∈ sqBox := cutSp_mem_sqBox hzbox
  fin_cases i
  · rcases hi with h | h
    · exact absurd h (ne_of_gt h3)
    · exact absurd h (ne_of_lt h4)
  · rcases hi with h | h
    · exact ⟨hx, Or.inl (by rw [cutSp_apply]; simpa using h)⟩
    · exact ⟨hx, Or.inr (Or.inl (by rw [cutSp_apply]; simpa using h))⟩
  · rcases hi with h | h
    · exact ⟨hx, Or.inr (Or.inr (Or.inl (by rw [cutSp_apply]; simpa using h)))⟩
    · exact ⟨hx, Or.inr (Or.inr (Or.inr (by rw [cutSp_apply]; simpa using h)))⟩

lemma scpG_face_condition
    (F : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2))
    (hF : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) F)
    (hbdry : ∀ x ∈ sqBdry, F x ≠ 0)
    (hreg : ∀ x ∈ sqBox, F x = 0 → Function.Surjective (fderiv ℝ F x))
    (v : EuclideanSpace ℝ (Fin 2)) (hv : v ≠ 0)
    (hbig : ∀ x ∈ sqBox, ‖F x‖ < ‖v‖)
    (hcorner : ∀ x ∈ sqBdry, (∃ r : ℝ, 0 < r ∧ F x = r • v) →
      ¬ ((x 0 = 0 ∨ x 0 = 1) ∧ (x 1 = 0 ∨ x 1 = 1)))
    (htrans_bdry : ∀ x ∈ sqBdry, (∃ r : ℝ, 0 < r ∧ F x = r • v) →
      ((x 1 = 0 ∨ x 1 = 1) →
        Work.Drive.det2 (fderiv ℝ F x (EuclideanSpace.single 0 1)) v ≠ 0) ∧
      ((x 0 = 0 ∨ x 0 = 1) →
        Work.Drive.det2 (fderiv ℝ F x (EuclideanSpace.single 1 1)) v ≠ 0))
    (w : EuclideanSpace ℝ (Fin 2)) :
    ∀ z ∈ Submission.Drive.unitBoxBdry 2, scpG F v w z = 0 →
      ∃ i : Fin 3, (z i = 0 ∨ z i = 1) ∧ (∀ j, j ≠ i → z j ∈ Set.Ioo (0:ℝ) 1) ∧
        Function.Surjective (fun u : {u : EuclideanSpace ℝ (Fin 3) // u i = 0} =>
          fderiv ℝ (scpG F v w) z u.1) := by
  intro z hz hzG
  have hFd : Differentiable ℝ F := hF.differentiable (by simp)
  -- the face `σ = 1` carries no zero
  have hz0ne1 : z 0 ≠ 1 := by
    intro h1
    have hFx : F (cutSp z) = v := by
      have h' := hzG
      rw [scpG_apply, scpPert_apply, cutSig_apply, h1, Work.Drive.ezPhi_one, zero_mul,
        zero_smul, sub_zero, one_smul] at h'
      exact sub_eq_zero.mp h'
    have hlt := hbig (cutSp z) (cutSp_mem_sqBox hz.1)
    rw [hFx] at hlt
    exact absurd hlt (lt_irrefl _)
  by_cases hzb : cutSp z ∈ sqBdry
  · -- a zero on a side face of the cube: transfer from the unperturbed family
    have hcut : cutMap F v z = 0 := by
      rw [← scpG_eq_cutMap_of_mem_sqBdry F v w hzb]
      exact hzG
    obtain ⟨i, hi, hoth, hsurj⟩ :=
      cutMap_face_condition F hFd hbdry hreg v hbig hcorner htrans_bdry z hz hcut
    refine ⟨i, hi, hoth, ?_⟩
    have hderiv : fderiv ℝ (scpG F v w) z = fderiv ℝ (cutMap F v) z :=
      fderiv_scpG_eq_cutMap_of_mem_sqBdry F hF v w hzb
    intro y
    obtain ⟨u, hu⟩ := hsurj y
    exact ⟨u, by rw [hderiv]; exact hu⟩
  · -- the zero lies on the face `σ = 0`
    have hz0 : z 0 = 0 := by
      obtain ⟨hzbox, i, hi⟩ := cutMem_unitBoxBdry.mp hz
      revert hi
      fin_cases i <;> intro hi
      · rcases hi with h | h
        · exact h
        · exact absurd h hz0ne1
      · exfalso
        refine hzb ⟨cutSp_mem_sqBox hzbox, ?_⟩
        rcases hi with h | h
        · exact Or.inl (by rw [cutSp_apply]; simpa using h)
        · exact Or.inr (Or.inl (by rw [cutSp_apply]; simpa using h))
      · exfalso
        refine hzb ⟨cutSp_mem_sqBox hzbox, ?_⟩
        rcases hi with h | h
        · exact Or.inr (Or.inr (Or.inl (by rw [cutSp_apply]; simpa using h)))
        · exact Or.inr (Or.inr (Or.inr (by rw [cutSp_apply]; simpa using h)))
    have hx : cutSp z ∈ sqBox := cutSp_mem_sqBox hz.1
    have hxb : cutSp z ∉ sqBdry := hzb
    have hFz : F (cutSp z) = 0 := by
      have h' := hzG
      rw [scpG_apply, scpPert_apply, cutSig_apply, hz0, Work.Drive.ezPhi_zero, zero_mul,
        zero_smul, sub_zero, zero_smul, sub_zero] at h'
      exact h'
    have hx0 : 0 < (cutSp z) 0 ∧ (cutSp z) 0 < 1 :=
      ⟨lt_of_le_of_ne hx.1.1 (Ne.symm fun h => hxb ⟨hx, Or.inl h⟩),
        lt_of_le_of_ne hx.1.2 fun h => hxb ⟨hx, Or.inr (Or.inl h)⟩⟩
    have hx1 : 0 < (cutSp z) 1 ∧ (cutSp z) 1 < 1 :=
      ⟨lt_of_le_of_ne hx.2.1 (Ne.symm fun h => hxb ⟨hx, Or.inr (Or.inr (Or.inl h))⟩),
        lt_of_le_of_ne hx.2.2 fun h => hxb ⟨hx, Or.inr (Or.inr (Or.inr h))⟩⟩
    refine ⟨0, Or.inl hz0, ?_, ?_⟩
    · intro j hj
      fin_cases j
      · exact absurd rfl hj
      · exact hx0
      · exact hx1
    · intro y
      obtain ⟨b, hb⟩ := hreg (cutSp z) hx hFz y
      refine ⟨⟨cutLift 0 b, cutSig_cutLift 0 b⟩, ?_⟩
      change fderiv ℝ (scpG F v w) z (cutLift 0 b) = y
      rw [fderiv_scpG_apply_of_cutSig_eq_zero F hF v w
          (by rw [cutSig_apply]; exact hz0) (cutSig_cutLift 0 b),
        cutMap_fderiv_apply F hFd, cutSp_cutLift, cutSig_cutLift, zero_smul, sub_zero]
      exact hb

/-- **The mod-2 degree theorem (cut/ray form) for a smooth map.**  This is
`Work.Surf.even_ncard_zeros_add_boundary_ray` with `ContDiff ℝ 1` strengthened to `C^∞` and with
`‖F x‖ < ‖v‖` required on the whole closed square (a harmless normalisation: it is achieved for a
rescaled `v`, and the conclusion only depends on the *ray* `{r • v : 0 < r}`, which is unchanged by
rescaling `v`).

Route.  The only gap with respect to `Work.Surf.tame_cut_parity` is that `F` need not be *tame*: at a
point of the square at which `F` is parallel to `v`, the derivative need not, together with `v`,
span the plane.

(1) *Perturb the family.*  Put `ψ t = t (1 - t)` and, for `w : 𝔼²`, let
`G_w (σ, x) = F x - σ • v - ψ σ • w` on the box `[0,1]³`.  Then `G_w (0,·) = F` (so the σ = 0 face
still carries exactly the zeros of `F`, regular by `hreg`) and `G_w (1,·) = F - v`, which has no
zeros by `hbig`.  A *trimmed* version of `Work.Drive.ezc_regularizing_perturbation` — drop that
tool's hypothesis that the family is non-vanishing on the side, keep only the conclusion that `0` is
a *regular value* of the perturbed family on the box, and note that the regularity part of that
tool's proof never uses the side hypothesis — produces `w`, small and outside the (nowhere dense)
set of critical values of the associated solution map, for which every zero of `G_w` in the box is
regular.  Write `w = c • v + u` with `u ⊥ v`; choose `c` small so that `σ ↦ σ + c ψ σ` is an
increasing bijection `[0,1] → [0,1]`, and `u` as the (generic, and small) perpendicular part.

(2) *The side zeros of `G_w` and the ray-meets.*  A side zero is a pair `(σ,x)` with `x ∈ sqBdry`,
`σ ∈ (0,1)` and `F x = η σ`, where `η σ = σ • v + ψ σ • w`.  The map `η` is injective, its image is
uniformly close to the segment `[0,v]`, and the segment meets the closed curve `F ∘ ∂□` exactly in the
boundary ray-meeting points (by `hbig`, the boundary values of `F` have `v`-coefficient `< 1`, and
their norm is bounded away from `0` by `hbdry`); by stability of transversal crossings, for small
enough `u` the crossings of the curve with the image of `η` are in bijection with the boundary
ray-meeting points of `F`, each with a unique `σ`.  Hence the side-zero set of `G_w` has the same
cardinality as `rayMeet F v ∩ sqBdry`.

(3) *Apply the engine.*  With `w ⊥ v`, the side-face restricted derivative of `G_w` at a side zero
`(σ,x)` is `(a,b) ↦ -a • (v + ψ' σ • w) + fderiv ℝ F x (b • face direction)`, whose surjectivity
follows from `htrans_bdry` because `v + ψ' σ • w` is not parallel to `v` while
`fderiv ℝ F x (face direction)` is not parallel to `v`; the other hypotheses of
`Work.Drive.boxParity` (`Submission.Drive.ParityProp`) are as in
`Work.Surf.tame_cut_parity`.  Its conclusion then reads `Even (#Z + #(side zeros)) = Even (#Z + #R)`. -/
theorem smooth_cut_parity
    (F : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2))
    (hF : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) F)
    (hbdry : ∀ x ∈ Work.Surf.sqBdry, F x ≠ 0)
    (hreg : ∀ x ∈ Work.Surf.sqBox, F x = 0 → Function.Surjective (fderiv ℝ F x))
    {v : EuclideanSpace ℝ (Fin 2)} (hv : v ≠ 0)
    (hbig : ∀ x ∈ Work.Surf.sqBox, ‖F x‖ < ‖v‖)
    (hcorner : ∀ x ∈ Work.Surf.sqBdry, (∃ r : ℝ, 0 < r ∧ F x = r • v) →
      ¬ ((x 0 = 0 ∨ x 0 = 1) ∧ (x 1 = 0 ∨ x 1 = 1)))
    (htrans_bdry : ∀ x ∈ Work.Surf.sqBdry, (∃ r : ℝ, 0 < r ∧ F x = r • v) →
      ((x 1 = 0 ∨ x 1 = 1) →
        Work.Drive.det2 (fderiv ℝ F x (EuclideanSpace.single 0 1)) v ≠ 0) ∧
      ((x 0 = 0 ∨ x 0 = 1) →
        Work.Drive.det2 (fderiv ℝ F x (EuclideanSpace.single 1 1)) v ≠ 0))
    (hfin : (Work.Surf.rayMeet F v ∩ Work.Surf.sqBdry).Finite) :
    Even (({x ∈ Work.Surf.sqBox | F x = 0} : Set (EuclideanSpace ℝ (Fin 2))).ncard +
      (Work.Surf.rayMeet F v ∩ Work.Surf.sqBdry : Set (EuclideanSpace ℝ (Fin 2))).ncard) := by
  classical
  obtain ⟨w, hw⟩ := scpG_exists_regular_perturbation F hF v
  have hGs : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (scpG F v w) := contDiff_scpG F hF v w
  have hface := scpG_face_condition F hF hbdry hreg v hv hbig hcorner htrans_bdry w
  -- `0` is a regular value of the perturbed family on the cube
  have hregG : ∀ z ∈ Submission.Drive.unitBox 2, scpG F v w z = 0 →
      Function.Surjective (fderiv ℝ (scpG F v w) z) := by
    intro z hz hz0
    by_cases hint : ∀ i : Fin 3, 0 < z i ∧ z i < 1
    · exact hw z hz hint hz0
    · obtain ⟨i, hi, _hoth, hsurj⟩ := hface z (mem_unitBoxBdry_of_not_interior hz hint) hz0
      intro y
      obtain ⟨u, hu⟩ := hsurj y
      exact ⟨u.1, hu⟩
  obtain ⟨hfinZc, hevenZc⟩ := Work.Drive.boxParity 2 (scpG F v w) hGs hregG hface
  -- the boundary zeros of the perturbed family split into the `σ = 0` face and the side faces
  set Zc : Set (EuclideanSpace ℝ (Fin 3)) :=
    {z | z ∈ Submission.Drive.unitBoxBdry 2 ∧ scpG F v w z = 0} with hZc
  set A : Set (EuclideanSpace ℝ (Fin 3)) :=
    {z | z ∈ Submission.Drive.unitBoxBdry 2 ∧ scpG F v w z = 0 ∧ z 0 = 0} with hA
  set B : Set (EuclideanSpace ℝ (Fin 3)) :=
    {z | z ∈ Submission.Drive.unitBoxBdry 2 ∧ scpG F v w z = 0 ∧ 0 < z 0 ∧ z 0 < 1} with hB
  have hZc_eq : Zc = A ∪ B := by
    ext z
    constructor
    · intro hz
      have hz0Icc : z 0 ∈ Set.Icc (0:ℝ) 1 := (cutMem_unitBoxBdry.mp hz.1).1 0
      have hne1 : z 0 ≠ 1 := by
        intro h1
        have hFx : F (cutSp z) = v := by
          have h' := hz.2
          rw [scpG_apply, scpPert_apply, cutSig_apply, h1, Work.Drive.ezPhi_one, zero_mul,
            zero_smul, sub_zero, one_smul] at h'
          exact sub_eq_zero.mp h'
        have hlt := hbig (cutSp z) (cutSp_mem_sqBox (cutMem_unitBoxBdry.mp hz.1).1)
        rw [hFx] at hlt
        exact absurd hlt (lt_irrefl _)
      rcases lt_trichotomy (z 0) 0 with h | h | h
      · exact absurd hz0Icc.1 (not_le_of_gt h)
      · exact Or.inl ⟨hz.1, hz.2, h⟩
      · exact Or.inr ⟨hz.1, hz.2, h, lt_of_le_of_ne hz0Icc.2 hne1⟩
    · rintro (hz | hz)
      · exact ⟨hz.1, hz.2.1⟩
      · exact ⟨hz.1, hz.2.1⟩
  have hdisj : Disjoint A B := by
    rw [Set.disjoint_left]
    intro z hz hz'
    exact absurd hz.2.2 hz'.2.2.1.ne'
  have hfinA : A.Finite := hfinZc.subset fun z hz => ⟨hz.1, hz.2.1⟩
  have hfinB : B.Finite := hfinZc.subset fun z hz => ⟨hz.1, hz.2.1⟩
  have hZc_ncard : Zc.ncard = A.ncard + B.ncard := by
    rw [hZc_eq, Set.ncard_union_eq hdisj hfinA hfinB]
  rw [hZc_ncard] at hevenZc
  -- the two pieces are the boundary zero sets of the unperturbed family
  have hAeq : A = {z | z ∈ Submission.Drive.unitBoxBdry 2 ∧ cutMap F v z = 0 ∧ z 0 = 0} := by
    ext z
    constructor
    · rintro ⟨h1, h2, h3⟩
      exact ⟨h1, by rw [← scpG_eq_cutMap_of_cutSig_eq_zero F v w
        (by rw [cutSig_apply]; exact h3)]; exact h2, h3⟩
    · rintro ⟨h1, h2, h3⟩
      exact ⟨h1, by rw [scpG_eq_cutMap_of_cutSig_eq_zero F v w
        (by rw [cutSig_apply]; exact h3)]; exact h2, h3⟩
  have hBeq : B = {z | z ∈ Submission.Drive.unitBoxBdry 2 ∧ cutMap F v z = 0 ∧ 0 < z 0 ∧
      z 0 < 1} := by
    ext z
    constructor
    · rintro ⟨h1, h2, h3, h4⟩
      have hzb := mem_sqBdry_of_mem_unitBoxBdry h1 h3 h4
      exact ⟨h1, by rw [← scpG_eq_cutMap_of_mem_sqBdry F v w hzb]; exact h2, h3, h4⟩
    · rintro ⟨h1, h2, h3, h4⟩
      have hzb := mem_sqBdry_of_mem_unitBoxBdry h1 h3 h4
      exact ⟨h1, by rw [scpG_eq_cutMap_of_mem_sqBdry F v w hzb]; exact h2, h3, h4⟩
  have hAnc : A.ncard = ({x : EuclideanSpace ℝ (Fin 2) | x ∈ sqBox ∧ F x = 0} : Set _).ncard := by
    rw [hAeq, ← cut_ncard_zeroSet F v]
  have hBnc : B.ncard = (rayMeet F v ∩ sqBdry).ncard := by
    rw [hBeq, ← cut_ncard_rayMeet F v hv hbig]
  rw [hAnc, hBnc] at hevenZc
  exact hevenZc

end Work.Surf
