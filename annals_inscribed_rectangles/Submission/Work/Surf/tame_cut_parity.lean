import Mathlib
import Submission.Work.Drive.boxParity
import Submission.Work.Surf.defs

namespace Work.Surf

open Set

noncomputable section

/-!
# The auxiliary family of the cut/ray parity

This file proves `Work.Surf.tame_cut_parity` by transporting the box parity theorem
`Work.Drive.boxParity` (`Submission.Drive.ParityProp`, proved) to the three-dimensional family

`cutMap F v : 𝔼³ → 𝔼²`,  `cutMap F v (σ, x₁, x₂) = F (x₁, x₂) - σ • v`.

The boundary zeros of `cutMap F v` on the cube `[0,1]³` are exactly the zeros of `F` on the face
`σ = 0` together with the points of the boundary of the square at which `F` takes a value on the open
ray `{r • v : 0 < r}` (the face `σ = 1` being empty, by `‖F x‖ < ‖v‖`).  Counting the two families
yields the parity statement.

Coordinates of `𝔼³ = EuclideanSpace ℝ (Fin 3)` are `(z 0, z 1, z 2) = (σ, x₁, x₂)`; `cutSp` is the
projection to the last two coordinates and `cutSig` the first one.
-/

/-- The projection `𝔼³ → 𝔼²`, `z ↦ (z 1, z 2)`. -/
def cutSp : EuclideanSpace ℝ (Fin 3) →L[ℝ] EuclideanSpace ℝ (Fin 2) :=
  ((EuclideanSpace.equiv (Fin 2) ℝ).symm.toContinuousLinearMap).comp
    ((ContinuousLinearMap.pi fun i : Fin 2 =>
        (ContinuousLinearMap.proj (Fin.succ i) : (Fin 3 → ℝ) →L[ℝ] ℝ)).comp
      (EuclideanSpace.equiv (Fin 3) ℝ).toContinuousLinearMap)

/-- The first coordinate `𝔼³ → 𝔼`, `z ↦ z 0`. -/
def cutSig : EuclideanSpace ℝ (Fin 3) →L[ℝ] ℝ :=
  (ContinuousLinearMap.proj (0 : Fin 3) : (Fin 3 → ℝ) →L[ℝ] ℝ).comp
    (EuclideanSpace.equiv (Fin 3) ℝ).toContinuousLinearMap

/-- The auxiliary family `(σ, x) ↦ F x - σ • v` on `𝔼³ = 𝔼 × 𝔼²`. -/
def cutMap (F : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2))
    (v : EuclideanSpace ℝ (Fin 2)) : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 2) :=
  fun z => F (cutSp z) - cutSig z • v

/-- The section of `cutSp` with prescribed first coordinate `c`. -/
def cutLift (c : ℝ) (x : EuclideanSpace ℝ (Fin 2)) : EuclideanSpace ℝ (Fin 3) :=
  WithLp.toLp 2 (Fin.cases c (fun i => x i))

lemma cutSp_apply (z : EuclideanSpace ℝ (Fin 3)) (i : Fin 2) : cutSp z i = z i.succ := rfl

lemma cutSig_apply (z : EuclideanSpace ℝ (Fin 3)) : cutSig z = z 0 := rfl

lemma cutLift_zero (c : ℝ) (x : EuclideanSpace ℝ (Fin 2)) : cutLift c x 0 = c := by
  simp [cutLift]

lemma cutLift_succ (c : ℝ) (x : EuclideanSpace ℝ (Fin 2)) (i : Fin 2) :
    cutLift c x i.succ = x i := by simp [cutLift]

lemma cutLift_one (c : ℝ) (x : EuclideanSpace ℝ (Fin 2)) : cutLift c x 1 = x 0 := by
  rw [show (1 : Fin 3) = (0 : Fin 2).succ from rfl, cutLift_succ]

lemma cutLift_two (c : ℝ) (x : EuclideanSpace ℝ (Fin 2)) : cutLift c x 2 = x 1 := by
  rw [show (2 : Fin 3) = (1 : Fin 2).succ from rfl, cutLift_succ]

lemma cutSp_cutLift (c : ℝ) (x : EuclideanSpace ℝ (Fin 2)) : cutSp (cutLift c x) = x := by
  ext i; simp [cutSp, cutLift]

lemma cutSig_cutLift (c : ℝ) (x : EuclideanSpace ℝ (Fin 2)) : cutSig (cutLift c x) = c := by
  simp [cutSig, cutLift]

lemma cutMap_apply (F : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2))
    (v : EuclideanSpace ℝ (Fin 2)) (z : EuclideanSpace ℝ (Fin 3)) :
    cutMap F v z = F (cutSp z) - cutSig z • v := rfl

/-- `cutSp` maps the cube `[0,1]³` into the square `[0,1]²`. -/
lemma cutSp_mem_sqBox {z : EuclideanSpace ℝ (Fin 3)} (hz : z ∈ Submission.Drive.unitBox 2) :
    cutSp z ∈ Work.Surf.sqBox := by
  have h : ∀ i : Fin 3, z i ∈ Set.Icc (0:ℝ) 1 := by
    simpa only [Submission.Drive.unitBox, Set.mem_ofPred_eq] using hz
  exact ⟨h 1, h 2⟩

/-- `cutLift` maps the square into the cube. -/
lemma cutLift_mem_unitBox {c : ℝ} {x : EuclideanSpace ℝ (Fin 2)} (hc : c ∈ Set.Icc (0:ℝ) 1)
    (hx : x ∈ Work.Surf.sqBox) : cutLift c x ∈ Submission.Drive.unitBox 2 := by
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · simpa [cutLift] using hc
  · rw [cutLift_succ]; fin_cases j
    · exact hx.1
    · exact hx.2

/-- Membership of the cube boundary, unfolded. -/
lemma cutMem_unitBoxBdry {z : EuclideanSpace ℝ (Fin 3)} :
    z ∈ Submission.Drive.unitBoxBdry 2 ↔ z ∈ Submission.Drive.unitBox 2 ∧ ∃ i, z i = 0 ∨ z i = 1 :=
  Iff.rfl

/-- `cutLift` is a section of `cutSp`, and the level `c` recovers the first coordinate. -/
lemma cutLift_cutSp_eq_of (c : ℝ) (z : EuclideanSpace ℝ (Fin 3)) (hc : c = z 0) :
    cutLift c (cutSp z) = z := by
  ext j
  refine Fin.cases ?_ (fun i => ?_) j
  · rw [cutLift_zero, hc]
  · rw [cutLift_succ, cutSp_apply]

lemma cut_mem_Ioo_of_Icc {a : ℝ} (h : a ∈ Set.Icc (0:ℝ) 1) (h0 : a ≠ 0) (h1 : a ≠ 1) :
    a ∈ Set.Ioo (0:ℝ) 1 :=
  ⟨lt_of_le_of_ne h.1 (Ne.symm h0), lt_of_le_of_ne h.2 h1⟩

/-! ## The derivative of the auxiliary family -/

lemma cut_hasFDerivAt_cutMap (F : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2))
    (hF : Differentiable ℝ F) (v : EuclideanSpace ℝ (Fin 2)) (z : EuclideanSpace ℝ (Fin 3)) :
    HasFDerivAt (cutMap F v) ((fderiv ℝ F (cutSp z)).comp cutSp - cutSig.smulRight v) z := by
  have h1 : HasFDerivAt (fun z : EuclideanSpace ℝ (Fin 3) => F (cutSp z))
      ((fderiv ℝ F (cutSp z)).comp cutSp) z :=
    (hF (cutSp z)).hasFDerivAt.comp z cutSp.hasFDerivAt
  have h2 : HasFDerivAt (fun z : EuclideanSpace ℝ (Fin 3) => cutSig z • v)
      (cutSig.smulRight v) z := cutSig.hasFDerivAt.smul_const v
  exact h1.sub h2

lemma cut_fderiv_cutMap (F : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2))
    (hF : Differentiable ℝ F) (v : EuclideanSpace ℝ (Fin 2)) (z : EuclideanSpace ℝ (Fin 3)) :
    fderiv ℝ (cutMap F v) z = ((fderiv ℝ F (cutSp z)).comp cutSp) - cutSig.smulRight v :=
  (cut_hasFDerivAt_cutMap F hF v z).fderiv

lemma cutMap_fderiv_apply (F : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2))
    (hF : Differentiable ℝ F) (v : EuclideanSpace ℝ (Fin 2)) (z u : EuclideanSpace ℝ (Fin 3)) :
    fderiv ℝ (cutMap F v) z u = fderiv ℝ F (cutSp z) (cutSp u) - cutSig u • v := by
  rw [cut_fderiv_cutMap F hF v z, sub_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.smulRight_apply]

lemma cut_contDiff_cutMap (F : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2))
    (v : EuclideanSpace ℝ (Fin 2)) (hF : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) F) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (cutMap F v) :=
  (hF.comp cutSp.contDiff).sub (cutSig.contDiff.smul_const v)

/-! ## Two vectors of the plane with non-zero determinant span it -/

lemma cutDet2_add_left (x y z : EuclideanSpace ℝ (Fin 2)) :
    Work.Drive.det2 (x + y) z = Work.Drive.det2 x z + Work.Drive.det2 y z := by
  simp only [Work.Drive.det2, WithLp.ofLp_add, Pi.add_apply]; ring

lemma cutDet2_add_right (x y z : EuclideanSpace ℝ (Fin 2)) :
    Work.Drive.det2 x (y + z) = Work.Drive.det2 x y + Work.Drive.det2 x z := by
  simp only [Work.Drive.det2, WithLp.ofLp_add, Pi.add_apply]; ring

lemma cutDet2_zero_left (z : EuclideanSpace ℝ (Fin 2)) : Work.Drive.det2 0 z = 0 := by
  simp [Work.Drive.det2]

lemma cutDet2_zero_right (z : EuclideanSpace ℝ (Fin 2)) : Work.Drive.det2 z 0 = 0 := by
  simp [Work.Drive.det2]

lemma cutRange_pair_fin2 (u w : EuclideanSpace ℝ (Fin 2)) : Set.range ![u, w] = {u, w} := by
  ext x; simp [Set.mem_insert_iff, Set.mem_singleton_iff, or_comm]

lemma cutSpan_eq_top_of_det2_ne_zero {u w : EuclideanSpace ℝ (Fin 2)}
    (h : Work.Drive.det2 u w ≠ 0) :
    Submodule.span ℝ ({u, w} : Set (EuclideanSpace ℝ (Fin 2))) = ⊤ := by
  have hli : LinearIndependent ℝ ![u, w] := by
    rw [LinearIndependent.pair_iff]
    intro a b hab
    have h1 : Work.Drive.det2 (a • u + b • w) w = 0 := by rw [hab]; exact cutDet2_zero_left w
    simp only [cutDet2_add_left, Work.Drive.det2_smul_left, Work.Drive.det2_self, mul_zero,
      add_zero] at h1
    have h2 : Work.Drive.det2 u (a • u + b • w) = 0 := by rw [hab]; exact cutDet2_zero_right u
    simp only [cutDet2_add_right, Work.Drive.det2_smul_right, Work.Drive.det2_self, mul_zero,
      zero_add] at h2
    exact ⟨(mul_eq_zero.mp h1).resolve_right h, (mul_eq_zero.mp h2).resolve_right h⟩
  have htop := hli.span_eq_top_of_card_eq_finrank (by simp [finrank_euclideanSpace])
  rwa [cutRange_pair_fin2 u w] at htop

lemma cutExists_smul_add_of_det2_ne_zero {u w : EuclideanSpace ℝ (Fin 2)}
    (h : Work.Drive.det2 u w ≠ 0) (y : EuclideanSpace ℝ (Fin 2)) :
    ∃ a b : ℝ, a • u + b • w = y := by
  have htop : Submodule.span ℝ ({u, w} : Set (EuclideanSpace ℝ (Fin 2))) = ⊤ :=
    cutSpan_eq_top_of_det2_ne_zero h
  exact Submodule.mem_span_pair.mp (by rw [htop]; trivial)

/-! ## The regularity and face conditions for `boxParity` -/

/-- The face condition of `Submission.Drive.ParityProp` for the auxiliary family. -/
lemma cutMap_face_condition
    (F : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2))
    (hF : Differentiable ℝ F)
    (hbdry : ∀ x ∈ Work.Surf.sqBdry, F x ≠ 0)
    (hreg : ∀ x ∈ Work.Surf.sqBox, F x = 0 → Function.Surjective (fderiv ℝ F x))
    (v : EuclideanSpace ℝ (Fin 2))
    (hbig : ∀ x ∈ Work.Surf.sqBox, ‖F x‖ < ‖v‖)
    (hcorner : ∀ x ∈ Work.Surf.sqBdry, (∃ r : ℝ, 0 < r ∧ F x = r • v) →
      ¬ ((x 0 = 0 ∨ x 0 = 1) ∧ (x 1 = 0 ∨ x 1 = 1)))
    (htrans_bdry : ∀ x ∈ Work.Surf.sqBdry, (∃ r : ℝ, 0 < r ∧ F x = r • v) →
      ((x 1 = 0 ∨ x 1 = 1) →
        Work.Drive.det2 (fderiv ℝ F x (EuclideanSpace.single 0 1)) v ≠ 0) ∧
      ((x 0 = 0 ∨ x 0 = 1) →
        Work.Drive.det2 (fderiv ℝ F x (EuclideanSpace.single 1 1)) v ≠ 0)) :
    ∀ z ∈ Submission.Drive.unitBoxBdry 2, cutMap F v z = 0 →
      ∃ i : Fin 3, (z i = 0 ∨ z i = 1) ∧ (∀ j, j ≠ i → z j ∈ Set.Ioo (0:ℝ) 1) ∧
        Function.Surjective (fun w : {w : EuclideanSpace ℝ (Fin 3) // w i = 0} =>
          fderiv ℝ (cutMap F v) z w.1) := by
  intro z hz hzG
  obtain ⟨hzbox, hzi⟩ := cutMem_unitBoxBdry.mp hz
  have hzI : ∀ i : Fin 3, z i ∈ Set.Icc (0:ℝ) 1 := by
    simpa only [Submission.Drive.unitBox, Set.mem_ofPred_eq] using hzbox
  have hx : cutSp z ∈ Work.Surf.sqBox := cutSp_mem_sqBox hzbox
  have hFx : F (cutSp z) = cutSig z • v := sub_eq_zero.mp hzG
  have hpar : ∃ r : ℝ, F (cutSp z) = r • v := ⟨cutSig z, hFx⟩
  have hne1 : z 0 ≠ 1 := by
    intro h
    have hnorm : ‖F (cutSp z)‖ = ‖v‖ := by rw [hFx, cutSig_apply, h, one_smul]
    have hlt := hbig (cutSp z) hx
    rw [hnorm] at hlt
    exact lt_irrefl _ hlt
  by_cases hz0 : z 0 = 0
  · -- the face `σ = 0`
    have hF0 : F (cutSp z) = 0 := by rw [hFx, cutSig_apply, hz0, zero_smul]
    have hspnb : cutSp z ∉ Work.Surf.sqBdry := fun hb => hbdry (cutSp z) hb hF0
    have hz1ne0 : z 1 ≠ 0 := fun h => hspnb ⟨hx, Or.inl h⟩
    have hz1ne1 : z 1 ≠ 1 := fun h => hspnb ⟨hx, Or.inr (Or.inl h)⟩
    have hz2ne0 : z 2 ≠ 0 := fun h => hspnb ⟨hx, Or.inr (Or.inr (Or.inl h))⟩
    have hz2ne1 : z 2 ≠ 1 := fun h => hspnb ⟨hx, Or.inr (Or.inr (Or.inr h))⟩
    refine ⟨0, Or.inl hz0, ?_, ?_⟩
    · intro j hj
      fin_cases j
      · exact absurd rfl hj
      · exact cut_mem_Ioo_of_Icc (hzI 1) hz1ne0 hz1ne1
      · exact cut_mem_Ioo_of_Icc (hzI 2) hz2ne0 hz2ne1
    · intro y
      obtain ⟨w, hw⟩ := hreg (cutSp z) hx hF0 y
      refine ⟨⟨cutLift 0 w, cutLift_zero 0 w⟩, ?_⟩
      change fderiv ℝ (cutMap F v) z (cutLift 0 w) = y
      rw [cutMap_fderiv_apply F hF v z, cutSp_cutLift, cutSig_cutLift, zero_smul, sub_zero, hw]
  · -- the side faces
    have hz0I : z 0 ∈ Set.Ioo (0:ℝ) 1 := cut_mem_Ioo_of_Icc (hzI 0) hz0 hne1
    have hray : cutSp z ∈ Work.Surf.rayMeet F v := ⟨z 0, hz0I.1, by rw [hFx, cutSig_apply]⟩
    have hz0not : ¬ (z 0 = 0 ∨ z 0 = 1) := fun h => h.elim hz0 hne1
    by_cases h1 : z 1 = 0 ∨ z 1 = 1
    · -- the face `x₂ = 0` in the cube, i.e. `x₁ = 0` in the square
      have hbdsq : cutSp z ∈ Work.Surf.sqBdry := by
        rcases h1 with h | h
        · exact ⟨hx, Or.inl h⟩
        · exact ⟨hx, Or.inr (Or.inl h)⟩
      have hnb := hcorner (cutSp z) hbdsq hray
      have hz2I : z 2 ∈ Set.Ioo (0:ℝ) 1 :=
        cut_mem_Ioo_of_Icc (hzI 2) (fun h => hnb ⟨h1, Or.inl h⟩) (fun h => hnb ⟨h1, Or.inr h⟩)
      refine ⟨1, h1, ?_, ?_⟩
      · intro j hj
        fin_cases j
        · exact hz0I
        · exact absurd rfl hj
        · exact hz2I
      · intro y
        have htrans := (htrans_bdry (cutSp z) hbdsq hray).2 h1
        obtain ⟨a, b, hab⟩ := cutExists_smul_add_of_det2_ne_zero htrans y
        refine ⟨⟨cutLift (-b) (a • (EuclideanSpace.single 1 (1:ℝ))), ?_⟩, ?_⟩
        · rw [cutLift_one]; simp
        · change fderiv ℝ (cutMap F v) z (cutLift (-b) (a • EuclideanSpace.single 1 1)) = y
          rw [cutMap_fderiv_apply F hF v z, cutSp_cutLift, cutSig_cutLift]
          simp only [map_smul, neg_smul, sub_neg_eq_add]
          exact hab
    · -- the face `x₂ = 0` in the cube, i.e. `x₂ = 0` in the square
      have h2 : z 2 = 0 ∨ z 2 = 1 := by
        rcases hzi with ⟨i, hi⟩
        fin_cases i
        · exact absurd hi hz0not
        · exact absurd hi h1
        · exact hi
      have hbdsq : cutSp z ∈ Work.Surf.sqBdry := by
        rcases h2 with h | h
        · exact ⟨hx, Or.inr (Or.inr (Or.inl h))⟩
        · exact ⟨hx, Or.inr (Or.inr (Or.inr h))⟩
      have hnb := hcorner (cutSp z) hbdsq hray
      have hz1I : z 1 ∈ Set.Ioo (0:ℝ) 1 :=
        cut_mem_Ioo_of_Icc (hzI 1) (fun h => hnb ⟨Or.inl h, h2⟩) (fun h => hnb ⟨Or.inr h, h2⟩)
      refine ⟨2, h2, ?_, ?_⟩
      · intro j hj
        fin_cases j
        · exact hz0I
        · exact hz1I
        · exact absurd rfl hj
      · intro y
        have htrans := (htrans_bdry (cutSp z) hbdsq hray).1 h2
        obtain ⟨a, b, hab⟩ := cutExists_smul_add_of_det2_ne_zero htrans y
        refine ⟨⟨cutLift (-b) (a • (EuclideanSpace.single 0 (1:ℝ))), ?_⟩, ?_⟩
        · rw [cutLift_two]; simp
        · change fderiv ℝ (cutMap F v) z (cutLift (-b) (a • EuclideanSpace.single 0 1)) = y
          rw [cutMap_fderiv_apply F hF v z, cutSp_cutLift, cutSig_cutLift]
          simp only [map_smul, neg_smul, sub_neg_eq_add]
          exact hab

/-! ## The counting

The boundary zeros of the auxiliary family split into the zeros of `F` on the closed square (on the
face `σ = 0`) and the points of `∂[0,1]²` at which `F` takes a positive multiple of `v` (on the
interior of the other faces).  The two correspondences are bijections. -/

lemma cut_eq_of_smul_eq_smul {v : EuclideanSpace ℝ (Fin 2)} (hv : v ≠ 0) {a b : ℝ}
    (h : a • v = b • v) : a = b := by
  have h1 : (a - b) • v = 0 := by rw [sub_smul, h, sub_self]
  exact sub_eq_zero.mp ((smul_eq_zero.mp h1).resolve_right hv)

/-- The positive coefficient of the ray through `v` realising `F x`, if there is one, and `0`
otherwise. -/
def cutRayCoeff (F : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2))
    (v : EuclideanSpace ℝ (Fin 2)) (x : EuclideanSpace ℝ (Fin 2)) : ℝ := by
  classical
  exact if h : ∃ r : ℝ, 0 < r ∧ F x = r • v then h.choose else 0

lemma cutRayCoeff_spec {F : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2)}
    {v x : EuclideanSpace ℝ (Fin 2)} (h : ∃ r : ℝ, 0 < r ∧ F x = r • v) :
    0 < cutRayCoeff F v x ∧ F x = cutRayCoeff F v x • v := by
  classical
  rw [cutRayCoeff, dif_pos h]
  exact h.choose_spec

lemma cutRayCoeff_eq {F : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2)}
    {v x : EuclideanSpace ℝ (Fin 2)} (hv : v ≠ 0) (h : ∃ r : ℝ, 0 < r ∧ F x = r • v)
    {r : ℝ} (hFr : F x = r • v) : cutRayCoeff F v x = r := by
  obtain ⟨-, hspec⟩ := cutRayCoeff_spec h
  exact cut_eq_of_smul_eq_smul hv (hspec.symm.trans hFr)

lemma cut_coeff_lt_one {F : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2)}
    {v : EuclideanSpace ℝ (Fin 2)} (hv : v ≠ 0) (hbig : ∀ x ∈ Work.Surf.sqBox, ‖F x‖ < ‖v‖)
    {x : EuclideanSpace ℝ (Fin 2)} (hx : x ∈ Work.Surf.sqBox) {c : ℝ} (hc : 0 < c)
    (h : F x = c • v) : c < 1 := by
  have hnorm : ‖F x‖ = c * ‖v‖ := by rw [h, norm_smul, Real.norm_of_nonneg hc.le]
  have hlt := hbig x hx
  rw [hnorm] at hlt
  have hvpos : 0 < ‖v‖ := norm_pos_iff.mpr hv
  nlinarith [hlt, hvpos]

/-- The zeros of `F` in the square correspond to the boundary zeros of the auxiliary family on the
face `σ = 0`. -/
lemma cut_ncard_zeroSet (F : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2))
    (v : EuclideanSpace ℝ (Fin 2)) :
    ({x : EuclideanSpace ℝ (Fin 2) | x ∈ Work.Surf.sqBox ∧ F x = 0} : Set _).ncard =
    ({z : EuclideanSpace ℝ (Fin 3) | z ∈ Submission.Drive.unitBoxBdry 2 ∧ cutMap F v z = 0 ∧
      z 0 = 0} : Set _).ncard := by
  refine Set.ncard_congr (fun x (_ : x ∈ ({x : EuclideanSpace ℝ (Fin 2) |
      x ∈ Work.Surf.sqBox ∧ F x = 0} : Set _)) => cutLift 0 x) ?_ ?_ ?_
  · intro x hx
    refine ⟨⟨cutLift_mem_unitBox ⟨le_refl 0, zero_le_one⟩ hx.1, ⟨0, Or.inl (cutLift_zero 0 x)⟩⟩,
      ?_, ?_⟩
    · change F (cutSp (cutLift 0 x)) - cutSig (cutLift 0 x) • v = 0
      rw [cutSp_cutLift, cutSig_cutLift, zero_smul, sub_zero, hx.2]
    · exact cutLift_zero 0 x
  · intro a b ha hb hab
    have h := congrArg cutSp hab
    rwa [cutSp_cutLift, cutSp_cutLift] at h
  · intro z hz
    refine ⟨cutSp z, ⟨cutSp_mem_sqBox hz.1.1, ?_⟩, cutLift_cutSp_eq_of 0 z hz.2.2.symm⟩
    have hFx : F (cutSp z) = cutSig z • v := sub_eq_zero.mp hz.2.1
    rw [hFx, cutSig_apply, hz.2.2, zero_smul]

/-- The boundary points of the square at which `F` takes a value on the open ray correspond to the
boundary zeros of the auxiliary family with `0 < σ < 1`. -/
lemma cut_ncard_rayMeet (F : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2))
    (v : EuclideanSpace ℝ (Fin 2)) (hv : v ≠ 0)
    (hbig : ∀ x ∈ Work.Surf.sqBox, ‖F x‖ < ‖v‖) :
    (Work.Surf.rayMeet F v ∩ Work.Surf.sqBdry).ncard =
    ({z : EuclideanSpace ℝ (Fin 3) | z ∈ Submission.Drive.unitBoxBdry 2 ∧ cutMap F v z = 0 ∧
      0 < z 0 ∧ z 0 < 1} : Set _).ncard := by
  refine Set.ncard_congr (fun x (_ : x ∈ Work.Surf.rayMeet F v ∩ Work.Surf.sqBdry) =>
    cutLift (cutRayCoeff F v x) x) ?_ ?_ ?_
  · intro x hx
    have hxray : ∃ r : ℝ, 0 < r ∧ F x = r • v := hx.1
    have hxsq : x ∈ Work.Surf.sqBox := hx.2.1
    obtain ⟨hcpos, hFx⟩ := cutRayCoeff_spec (F := F) (v := v) hxray
    have hclt : cutRayCoeff F v x < 1 := cut_coeff_lt_one hv hbig hxsq hcpos hFx
    have hcIcc : cutRayCoeff F v x ∈ Set.Icc (0:ℝ) 1 := ⟨hcpos.le, hclt.le⟩
    have hbd : ∃ i : Fin 3, cutLift (cutRayCoeff F v x) x i = 0 ∨
        cutLift (cutRayCoeff F v x) x i = 1 := by
      rcases hx.2.2 with h | h | h | h
      · exact ⟨1, Or.inl (by rw [cutLift_one]; exact h)⟩
      · exact ⟨1, Or.inr (by rw [cutLift_one]; exact h)⟩
      · exact ⟨2, Or.inl (by rw [cutLift_two]; exact h)⟩
      · exact ⟨2, Or.inr (by rw [cutLift_two]; exact h)⟩
    refine ⟨⟨cutLift_mem_unitBox hcIcc hxsq, hbd⟩, ?_, hcpos, hclt⟩
    · change F x - cutRayCoeff F v x • v = 0
      rw [hFx, sub_self]
  · intro a b ha hb hab
    have h := congrArg cutSp hab
    rwa [cutSp_cutLift, cutSp_cutLift] at h
  · intro z hz
    have hzbox : z ∈ Submission.Drive.unitBox 2 := hz.1.1
    have hz0pos : 0 < z 0 := hz.2.2.1
    have hz0lt : z 0 < 1 := hz.2.2.2
    have hFx : F (cutSp z) = z 0 • v := by rw [sub_eq_zero.mp hz.2.1, cutSig_apply]
    have hray : cutSp z ∈ Work.Surf.rayMeet F v := ⟨z 0, hz0pos, hFx⟩
    have hbd : cutSp z ∈ Work.Surf.sqBdry := by
      have hx0 : cutSp z ∈ Work.Surf.sqBox := cutSp_mem_sqBox hzbox
      rcases hz.1.2 with ⟨i, hi⟩
      fin_cases i
      · rcases hi with h | h
        · exact absurd h hz0pos.ne'
        · exact absurd h hz0lt.ne
      · rcases hi with h | h
        · exact ⟨hx0, Or.inl h⟩
        · exact ⟨hx0, Or.inr (Or.inl h)⟩
      · rcases hi with h | h
        · exact ⟨hx0, Or.inr (Or.inr (Or.inl h))⟩
        · exact ⟨hx0, Or.inr (Or.inr (Or.inr h))⟩
    refine ⟨cutSp z, ⟨hray, hbd⟩, ?_⟩
    show cutLift (cutRayCoeff F v (cutSp z)) (cutSp z) = z
    rw [cutRayCoeff_eq hv ⟨z 0, hz0pos, hFx⟩ hFx]
    exact cutLift_cutSp_eq_of (z 0) z rfl

/-- **The cut/ray parity for a map transverse to the ray.**  Hypotheses: `F : 𝔼² → 𝔼²` smooth,
nonzero on the boundary of the unit square `sqBox = [0,1]²`, every zero in the square a regular point,
`‖F x‖ < ‖v‖` for every `x` in the **whole closed square** (so that the auxiliary family below has no
zeros on the face `σ = 1`), and the *tameness* hypothesis: at every `x` in the square at which `F x` is
parallel to `v`, the derivative of `F` together with the line `ℝv` spans the plane (this makes `0` a
regular value of the auxiliary family).  Then the number of zeros of `F` in the square and the number
of boundary points at which `F` is a positive multiple of `v` have the same parity.

Proof: apply `Work.Drive.boxParity` (`Submission.Drive.ParityProp`, proved) to
`G : 𝔼³ → 𝔼²`, `G (σ, x) := F x - σ • v`, on the box `[0,1]³` (coordinates `(σ, x₁, x₂)`).  Its
boundary zeros are exactly: `(0, x)` with `F x = 0` (the σ = 0 face, where the face-restricted
derivative is `fderiv ℝ F x`, surjective by `hreg`); and `(σ, x)` with `x ∈ sqBdry`, `σ ∈ (0,1)` and
`F x = σ • v` — these are in bijection with the boundary ray-meeting points, because on `sqBdry`
`‖F x‖ < ‖v‖` forces the coefficient `σ = r` with `F x = r v` to lie in `(0,1)`.  The `σ = 1` face
carries no zeros by the strengthened `hbig`.  The face-restricted derivative at a side-face zero
`(σ,x)` is `(a, b) ↦ -a • v + fderiv ℝ F x b` on the span of the σ-direction and the face direction,
which is surjective by `htrans_bdry`; the corners are excluded by `hcorner`. -/
theorem tame_cut_parity
    (F : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2))
    (hF : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) F)
    (hbdry : ∀ x ∈ Work.Surf.sqBdry, F x ≠ 0)
    (hreg : ∀ x ∈ Work.Surf.sqBox, F x = 0 → Function.Surjective (fderiv ℝ F x))
    {v : EuclideanSpace ℝ (Fin 2)} (hv : v ≠ 0)
    (hbig : ∀ x ∈ Work.Surf.sqBox, ‖F x‖ < ‖v‖)
    (htame : ∀ x ∈ Work.Surf.sqBox, (∃ r : ℝ, F x = r • v) →
      ∀ y : EuclideanSpace ℝ (Fin 2), ∃ (a : ℝ) (w : EuclideanSpace ℝ (Fin 2)),
        y = a • v + fderiv ℝ F x w)
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
  have _hfin := hfin
  have hFd : Differentiable ℝ F := hF.differentiable (by decide)
  have hG : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (cutMap F v) := cut_contDiff_cutMap F v hF
  have hregG : ∀ z ∈ Submission.Drive.unitBox 2, cutMap F v z = 0 →
      Function.Surjective (fderiv ℝ (cutMap F v) z) := by
    intro z hz hzG y
    have hx : cutSp z ∈ Work.Surf.sqBox := cutSp_mem_sqBox hz
    have hFx : F (cutSp z) = cutSig z • v := sub_eq_zero.mp hzG
    obtain ⟨a, w, haw⟩ := htame (cutSp z) hx ⟨cutSig z, hFx⟩ y
    refine ⟨cutLift (-a) w, ?_⟩
    rw [cutMap_fderiv_apply F hFd v z, cutSp_cutLift, cutSig_cutLift, neg_smul, sub_neg_eq_add,
      haw, add_comm]
  have hfaceG : ∀ z ∈ Submission.Drive.unitBoxBdry 2, cutMap F v z = 0 →
      ∃ i : Fin 3, (z i = 0 ∨ z i = 1) ∧ (∀ j, j ≠ i → z j ∈ Set.Ioo (0:ℝ) 1) ∧
        Function.Surjective (fun w : {w : EuclideanSpace ℝ (Fin 3) // w i = 0} =>
          fderiv ℝ (cutMap F v) z w.1) :=
    cutMap_face_condition F hFd hbdry hreg v hbig hcorner htrans_bdry
  obtain ⟨hfinZc, hevenZc⟩ := Work.Drive.boxParity 2 (cutMap F v) hG hregG hfaceG
  have hZc_eq : ({z : EuclideanSpace ℝ (Fin 3) | z ∈ Submission.Drive.unitBoxBdry 2 ∧
        cutMap F v z = 0} : Set (EuclideanSpace ℝ (Fin 3))) =
      ({z : EuclideanSpace ℝ (Fin 3) | z ∈ Submission.Drive.unitBoxBdry 2 ∧
          cutMap F v z = 0 ∧ z 0 = 0} : Set (EuclideanSpace ℝ (Fin 3))) ∪
        ({z : EuclideanSpace ℝ (Fin 3) | z ∈ Submission.Drive.unitBoxBdry 2 ∧
          cutMap F v z = 0 ∧ 0 < z 0 ∧ z 0 < 1} : Set (EuclideanSpace ℝ (Fin 3))) := by
    ext z
    constructor
    · intro hz
      have hzbox : z ∈ Submission.Drive.unitBox 2 := (cutMem_unitBoxBdry.mp hz.1).1
      have hz0Icc : z 0 ∈ Set.Icc (0:ℝ) 1 := by
        have h : ∀ i : Fin 3, z i ∈ Set.Icc (0:ℝ) 1 := by
          simpa only [Submission.Drive.unitBox, Set.mem_ofPred_eq] using hzbox
        exact h 0
      have hne1 : z 0 ≠ 1 := by
        intro h
        have hFx : F (cutSp z) = cutSig z • v := sub_eq_zero.mp hz.2
        have hnorm : ‖F (cutSp z)‖ = ‖v‖ := by rw [hFx, cutSig_apply, h, one_smul]
        have hlt := hbig (cutSp z) (cutSp_mem_sqBox hzbox)
        rw [hnorm] at hlt
        exact lt_irrefl _ hlt
      rcases lt_trichotomy (z 0) 0 with h | h | h
      · exact absurd hz0Icc.1 (not_le_of_gt h)
      · exact Or.inl ⟨hz.1, hz.2, h⟩
      · exact Or.inr ⟨hz.1, hz.2, h, lt_of_le_of_ne hz0Icc.2 hne1⟩
    · rintro (hz | hz)
      · exact ⟨hz.1, hz.2.1⟩
      · exact ⟨hz.1, hz.2.1⟩
  have hdisj : Disjoint ({z : EuclideanSpace ℝ (Fin 3) | z ∈ Submission.Drive.unitBoxBdry 2 ∧
        cutMap F v z = 0 ∧ z 0 = 0} : Set (EuclideanSpace ℝ (Fin 3)))
      ({z : EuclideanSpace ℝ (Fin 3) | z ∈ Submission.Drive.unitBoxBdry 2 ∧
        cutMap F v z = 0 ∧ 0 < z 0 ∧ z 0 < 1} : Set (EuclideanSpace ℝ (Fin 3))) := by
    rw [Set.disjoint_left]
    intro z hz hz'
    exact absurd hz.2.2 hz'.2.2.1.ne'
  have hfinA : ({z : EuclideanSpace ℝ (Fin 3) | z ∈ Submission.Drive.unitBoxBdry 2 ∧
      cutMap F v z = 0 ∧ z 0 = 0} : Set (EuclideanSpace ℝ (Fin 3))).Finite :=
    hfinZc.subset (fun z hz => ⟨hz.1, hz.2.1⟩)
  have hfinB : ({z : EuclideanSpace ℝ (Fin 3) | z ∈ Submission.Drive.unitBoxBdry 2 ∧
      cutMap F v z = 0 ∧ 0 < z 0 ∧ z 0 < 1} : Set (EuclideanSpace ℝ (Fin 3))).Finite :=
    hfinZc.subset (fun z hz => ⟨hz.1, hz.2.1⟩)
  have hZc_ncard : ({z : EuclideanSpace ℝ (Fin 3) | z ∈ Submission.Drive.unitBoxBdry 2 ∧
      cutMap F v z = 0} : Set (EuclideanSpace ℝ (Fin 3))).ncard =
      ({z : EuclideanSpace ℝ (Fin 3) | z ∈ Submission.Drive.unitBoxBdry 2 ∧
        cutMap F v z = 0 ∧ z 0 = 0} : Set (EuclideanSpace ℝ (Fin 3))).ncard +
      ({z : EuclideanSpace ℝ (Fin 3) | z ∈ Submission.Drive.unitBoxBdry 2 ∧
        cutMap F v z = 0 ∧ 0 < z 0 ∧ z 0 < 1} : Set (EuclideanSpace ℝ (Fin 3))).ncard := by
    rw [hZc_eq, Set.ncard_union_eq hdisj hfinA hfinB]
  rw [hZc_ncard] at hevenZc
  rw [← cut_ncard_zeroSet F v, ← cut_ncard_rayMeet F v hv hbig] at hevenZc
  exact hevenZc

end

end Work.Surf
