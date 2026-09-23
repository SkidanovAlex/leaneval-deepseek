import Mathlib
import Submission.Commons.Topology.Sphere.radial_extension
import Submission.Commons.Topology.Sphere.two_disk_cover_strong

/-!
# Gluing a collar to a disk is a disk

Given a compact Hausdorff space `X = A ∪ C`, where `A` is a closed subset homeomorphic to the
closed unit ball `D^n` and `C` is a closed subset homeomorphic to the collar `S^{n-1} × [0,1]`,
glued along the boundary sphere of `A` (which corresponds to the `t = 0` slice of the collar),
the space `X` is again homeomorphic to `D^n`, and one can arrange that the boundary sphere of `X`
corresponds to the `t = 1` slice of the collar.

This is the "one-half" version of `Commons.Topology.Sphere.two_disk_cover`.
-/

namespace Commons.Topology.Sphere

open Set
open TwoDiskStrong

noncomputable section

/-- The `t = 0` slice of the collar `S^{n-1} × [0,1]`. -/
private def collarBot (n : ℕ) : Set ↥(esphere n ×ˢ Set.Icc (0 : ℝ) 1) :=
  {p | (p : EuclideanSpace ℝ (Fin n) × ℝ).2 = 0}

/-- The point `(v, 0)` of the collar, as an element of the bottom slice. -/
private def botPt (n : ℕ) (v : esphere n) : collarBot n :=
  ⟨⟨((v : EuclideanSpace ℝ (Fin n)), 0), by
      rw [Set.mem_prod]; exact ⟨v.2, by simp⟩⟩, rfl⟩

/-- The first coordinate of a point of the bottom slice of the collar. -/
private def fstS (n : ℕ) (p : collarBot n) : esphere n :=
  ⟨((p.1 : EuclideanSpace ℝ (Fin n) × ℝ).1), p.1.2.1⟩

@[simp] private lemma fstS_botPt (n : ℕ) (v : esphere n) : fstS n (botPt n v) = v := by
  apply Subtype.ext; rfl

@[simp] private lemma botPt_fstS (n : ℕ) (p : collarBot n) : botPt n (fstS n p) = p := by
  apply Subtype.ext; apply Subtype.ext
  exact Prod.ext rfl p.2.symm

@[simp] private lemma botPt_fstS_fst (n : ℕ) (p : collarBot n) : (botPt n (fstS n p)).1 = p.1 := by
  rw [botPt_fstS]

private lemma continuous_botPt (n : ℕ) : Continuous (botPt n) := by unfold botPt; fun_prop
private lemma continuous_fstS (n : ℕ) : Continuous (fstS n) := by unfold fstS; fun_prop

/-- The canonical homeomorphism between the bottom slice of the collar and the sphere. -/
private def chiHomeo (n : ℕ) : collarBot n ≃ₜ esphere n where
  toFun := fstS n
  invFun := botPt n
  left_inv := botPt_fstS n
  right_inv := fstS_botPt n
  continuous_toFun := continuous_fstS n
  continuous_invFun := continuous_botPt n

section Helpers

variable {n : ℕ} {X : Type*} [TopologicalSpace X] {A C : Set X}

/-- A point of `A` whose `eA`-coordinate is on the boundary sphere of `D^n` lies in `C`. -/
private lemma mem_C_of_eA_bsphere (eA : ↥A ≃ₜ eball n)
    (hAc : A ∩ C = eA ⁻¹' bsphere n) (a : ↥A) (ha : eA a ∈ bsphere n) : (a : X) ∈ C := by
  have h : (a : X) ∈ A ∩ C := by
    rw [hAc]; exact ⟨a, ha, rfl⟩
  exact h.2

/-- A point of `C` whose `eC`-coordinate lies in the bottom slice of the collar lies in `A`. -/
private lemma mem_A_of_eC_bot (eC : ↥C ≃ₜ ↥(esphere n ×ˢ Set.Icc (0 : ℝ) 1))
    (hCc : A ∩ C = eC ⁻¹' collarBot n) (c : ↥C) (hc : eC c ∈ collarBot n) : (c : X) ∈ A := by
  have h : (c : X) ∈ A ∩ C := by
    rw [hCc]; exact ⟨c, hc, rfl⟩
  exact h.1

/-- Conversely: a point of `A` lying in `C` has boundary `eA`-coordinate. -/
private lemma eA_mem_bsphere_of_mem_C (eA : ↥A ≃ₜ eball n)
    (hAc : A ∩ C = eA ⁻¹' bsphere n) (a : ↥A) (ha : (a : X) ∈ C) : eA a ∈ bsphere n := by
  have h : (a : X) ∈ A ∩ C := ⟨a.2, ha⟩
  rw [hAc] at h
  obtain ⟨a', ha', ha'a⟩ := h
  have : a' = a := Subtype.ext ha'a
  rw [← this]; exact ha'

/-- Conversely: a point of `C` lying in `A` has `eC`-coordinate in the bottom slice. -/
private lemma eC_mem_bot_of_mem_A (eC : ↥C ≃ₜ ↥(esphere n ×ˢ Set.Icc (0 : ℝ) 1))
    (hCc : A ∩ C = eC ⁻¹' collarBot n) (c : ↥C) (hc : (c : X) ∈ A) : eC c ∈ collarBot n := by
  have h : (c : X) ∈ A ∩ C := ⟨hc, c.2⟩
  rw [hCc] at h
  obtain ⟨c', hc', hc'c⟩ := h
  have : c' = c := Subtype.ext hc'c
  rw [← this]; exact hc'

/-- The boundary identification of the sphere with the boundary of `A`: for `v : S^{n-1}`,
`uFun v` is the point of `A` corresponding (under `eA`) to the collar point `eC⁻¹ (v, 0)`. -/
private def uFun (eA : ↥A ≃ₜ eball n)
    (eC : ↥C ≃ₜ ↥(esphere n ×ˢ Set.Icc (0 : ℝ) 1))
    (hAc : A ∩ C = eA ⁻¹' bsphere n) (hCc : A ∩ C = eC ⁻¹' collarBot n)
    (v : esphere n) : esphere n :=
  let c : ↥C := eC.symm (botPt n v).1
  let a : ↥A := ⟨(c : X), mem_A_of_eC_bot eC hCc c (by
      rw [show eC c = (botPt n v).1 from Homeomorph.apply_symm_apply eC (botPt n v).1]
      exact (botPt n v).2)⟩
  ⟨(eA a : EuclideanSpace ℝ (Fin n)), by
    rw [mem_sphere_zero_iff_norm]
    exact (bsphere_mem_iff n (eA a)).mp (eA_mem_bsphere_of_mem_C eA hAc a c.2)⟩

/-- The inverse boundary identification. -/
private def uInvFun (eA : ↥A ≃ₜ eball n)
    (eC : ↥C ≃ₜ ↥(esphere n ×ˢ Set.Icc (0 : ℝ) 1))
    (hAc : A ∩ C = eA ⁻¹' bsphere n) (hCc : A ∩ C = eC ⁻¹' collarBot n)
    (v : esphere n) : esphere n :=
  let a : ↥A := eA.symm (sphToB n v).1
  let c : ↥C := ⟨(a : X), mem_C_of_eA_bsphere eA hAc a (by
      rw [show eA a = (sphToB n v).1 from Homeomorph.apply_symm_apply eA (sphToB n v).1]
      exact (sphToB n v).2)⟩
  fstS n ⟨eC c, eC_mem_bot_of_mem_A eC hCc c a.2⟩

set_option maxHeartbeats 800000 in
private lemma uInvFun_uFun (eA : ↥A ≃ₜ eball n)
    (eC : ↥C ≃ₜ ↥(esphere n ×ˢ Set.Icc (0 : ℝ) 1))
    (hAc : A ∩ C = eA ⁻¹' bsphere n) (hCc : A ∩ C = eC ⁻¹' collarBot n)
    (v : esphere n) : uInvFun eA eC hAc hCc (uFun eA eC hAc hCc v) = v := by
  apply Subtype.ext
  simp only [uFun, uInvFun, fstS, botPt, sphToB_val, Homeomorph.symm_apply_apply,
    Homeomorph.apply_symm_apply, Subtype.coe_eta]

set_option maxHeartbeats 800000 in
private lemma uFun_uInvFun (eA : ↥A ≃ₜ eball n)
    (eC : ↥C ≃ₜ ↥(esphere n ×ˢ Set.Icc (0 : ℝ) 1))
    (hAc : A ∩ C = eA ⁻¹' bsphere n) (hCc : A ∩ C = eC ⁻¹' collarBot n)
    (v : esphere n) : uFun eA eC hAc hCc (uInvFun eA eC hAc hCc v) = v := by
  apply Subtype.ext
  simp only [uFun, uInvFun, botPt_fstS, sphToB_val,
    Homeomorph.symm_apply_apply, Homeomorph.apply_symm_apply, Subtype.coe_eta]

private lemma continuous_uFun (eA : ↥A ≃ₜ eball n)
    (eC : ↥C ≃ₜ ↥(esphere n ×ˢ Set.Icc (0 : ℝ) 1))
    (hAc : A ∩ C = eA ⁻¹' bsphere n) (hCc : A ∩ C = eC ⁻¹' collarBot n) :
    Continuous (uFun eA eC hAc hCc) := by
  have hmem : ∀ v : esphere n, (eC.symm ((botPt n v).1) : X) ∈ A := fun v =>
    mem_A_of_eC_bot eC hCc _ (by
      rw [show eC (eC.symm ((botPt n v).1)) = (botPt n v).1 from
        Homeomorph.apply_symm_apply eC ((botPt n v).1)]
      exact (botPt n v).2)
  have h1 : Continuous fun v : esphere n =>
      ((botPt n v).1 : ↥(esphere n ×ˢ Set.Icc (0 : ℝ) 1)) :=
    continuous_subtype_val.comp (continuous_botPt n)
  have h2 : Continuous fun v : esphere n => eC.symm ((botPt n v).1) :=
    eC.symm.continuous.comp h1
  have h3 : Continuous fun v : esphere n => (eC.symm ((botPt n v).1) : X) :=
    continuous_subtype_val.comp h2
  have h4 : Continuous fun v : esphere n =>
      (⟨(eC.symm ((botPt n v).1) : X), hmem v⟩ : ↥A) :=
    Continuous.subtype_mk h3 hmem
  have h5 : Continuous fun v : esphere n =>
      ((eA (⟨(eC.symm ((botPt n v).1) : X), hmem v⟩ : ↥A) : eball n) :
        EuclideanSpace ℝ (Fin n)) :=
    continuous_subtype_val.comp (eA.continuous.comp h4)
  have h6 : Continuous fun v : esphere n =>
      (uFun eA eC hAc hCc v : EuclideanSpace ℝ (Fin n)) := by
    simpa only [uFun] using h5
  exact Continuous.subtype_mk h6 (fun v => (uFun eA eC hAc hCc v).2)

/-- The boundary identification of the boundary sphere of `A` with the sphere, as a homeomorphism.
For `x ∈ A ∩ C`, it sends the first coordinate of `eC x` to `eA x`. -/
private def uHomeo (eA : ↥A ≃ₜ eball n)
    (eC : ↥C ≃ₜ ↥(esphere n ×ˢ Set.Icc (0 : ℝ) 1))
    (hAc : A ∩ C = eA ⁻¹' bsphere n) (hCc : A ∩ C = eC ⁻¹' collarBot n) :
    esphere n ≃ₜ esphere n :=
  Continuous.homeoOfEquivCompactToT2
    (f := { toFun := uFun eA eC hAc hCc
            invFun := uInvFun eA eC hAc hCc
            left_inv := uInvFun_uFun eA eC hAc hCc
            right_inv := uFun_uInvFun eA eC hAc hCc })
    (continuous_uFun eA eC hAc hCc)

@[simp] private lemma uHomeo_apply (eA : ↥A ≃ₜ eball n)
    (eC : ↥C ≃ₜ ↥(esphere n ×ˢ Set.Icc (0 : ℝ) 1))
    (hAc : A ∩ C = eA ⁻¹' bsphere n) (hCc : A ∩ C = eC ⁻¹' collarBot n)
    (v : esphere n) : uHomeo eA eC hAc hCc v = uFun eA eC hAc hCc v := rfl

/-- The defining property of the boundary identification: for `x ∈ A ∩ C`, the homeomorphism
`uHomeo` sends the first coordinate of `eC x` to `eA x`. -/
private lemma uFun_apply (eA : ↥A ≃ₜ eball n)
    (eC : ↥C ≃ₜ ↥(esphere n ×ˢ Set.Icc (0 : ℝ) 1))
    (hAc : A ∩ C = eA ⁻¹' bsphere n) (hCc : A ∩ C = eC ⁻¹' collarBot n)
    (x : X) (hxA : x ∈ A) (hxC : x ∈ C) :
    (uFun eA eC hAc hCc
        (fstS n ⟨eC ⟨x, hxC⟩, eC_mem_bot_of_mem_A eC hCc ⟨x, hxC⟩ hxA⟩) :
      EuclideanSpace ℝ (Fin n)) = (eA ⟨x, hxA⟩ : EuclideanSpace ℝ (Fin n)) := by
  have hval : eC.symm ((⟨eC ⟨x, hxC⟩, eC_mem_bot_of_mem_A eC hCc ⟨x, hxC⟩ hxA⟩ :
      collarBot n).1) = ⟨x, hxC⟩ := by
    rw [Homeomorph.symm_apply_apply]
  simp only [uFun, botPt_fstS, hval]

/-- Variant of `uFun_apply` with the argument written as an explicit point of the sphere. -/
private lemma uFun_apply' (eA : ↥A ≃ₜ eball n)
    (eC : ↥C ≃ₜ ↥(esphere n ×ˢ Set.Icc (0 : ℝ) 1))
    (hAc : A ∩ C = eA ⁻¹' bsphere n) (hCc : A ∩ C = eC ⁻¹' collarBot n)
    (x : X) (hxA : x ∈ A) (hxC : x ∈ C) :
    (uFun eA eC hAc hCc ⟨((eC ⟨x, hxC⟩ : EuclideanSpace ℝ (Fin n) × ℝ)).1,
        (eC ⟨x, hxC⟩).2.1⟩ : EuclideanSpace ℝ (Fin n))
      = (eA ⟨x, hxA⟩ : EuclideanSpace ℝ (Fin n)) := by
  rw [show (⟨((eC ⟨x, hxC⟩ : EuclideanSpace ℝ (Fin n) × ℝ)).1,
        (eC ⟨x, hxC⟩).2.1⟩ : esphere n)
      = fstS n ⟨eC ⟨x, hxC⟩, eC_mem_bot_of_mem_A eC hCc ⟨x, hxC⟩ hxA⟩ from rfl]
  exact uFun_apply eA eC hAc hCc x hxA hxC

end Helpers

end


section Main

noncomputable section

variable {n : ℕ} {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
    {A C : Set X}

/-- The "inner disk" chart of `A`: `A` shrunk to the ball of radius `1/2`. -/
private def fA (eA : ↥A ≃ₜ eball n) (a : ↥A) : eball n :=
  ⟨(1 / 2 : ℝ) • (eA a : EuclideanSpace ℝ (Fin n)), by
    rw [Metric.mem_closedBall, dist_zero_right, norm_smul,
      Real.norm_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2)]
    have := norm_le_one_of_mem (eA a)
    linarith⟩

@[simp] private lemma fA_coe (eA : ↥A ≃ₜ eball n) (a : ↥A) :
    ((fA eA a : eball n) : EuclideanSpace ℝ (Fin n))
      = (1 / 2 : ℝ) • (eA a : EuclideanSpace ℝ (Fin n)) := rfl

private lemma norm_fA (eA : ↥A ≃ₜ eball n) (a : ↥A) :
    ‖((fA eA a : eball n) : EuclideanSpace ℝ (Fin n))‖
      = (1 / 2 : ℝ) * ‖(eA a : EuclideanSpace ℝ (Fin n))‖ := by
  rw [fA_coe, norm_smul, Real.norm_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2)]

private lemma fA_injective (eA : ↥A ≃ₜ eball n) : Function.Injective (fA eA) := by
  intro a b h
  have h' : (eA a : EuclideanSpace ℝ (Fin n)) = (eA b : EuclideanSpace ℝ (Fin n)) := by
    have := congrArg (fun z : eball n => (z : EuclideanSpace ℝ (Fin n))) h
    simp only [fA_coe] at this
    exact smul_right_injective (EuclideanSpace ℝ (Fin n)) (by norm_num : (1/2:ℝ) ≠ 0) this
  exact eA.injective (Subtype.ext h')

/-- The "outer annulus" chart of `C`. -/
private def fC (eA : ↥A ≃ₜ eball n) (eC : ↥C ≃ₜ ↥(esphere n ×ˢ Set.Icc (0 : ℝ) 1))
    (hAc : A ∩ C = eA ⁻¹' bsphere n) (hCc : A ∩ C = eC ⁻¹' collarBot n)
    (c : ↥C) : eball n :=
  ⟨(1 / 2 + ((eC c : EuclideanSpace ℝ (Fin n) × ℝ)).2 / 2) •
      ((uHomeo eA eC hAc hCc ⟨((eC c : EuclideanSpace ℝ (Fin n) × ℝ)).1,
        (eC c).2.1⟩ : esphere n) : EuclideanSpace ℝ (Fin n)), by
    rw [Metric.mem_closedBall, dist_zero_right, norm_smul]
    have ht0 : 0 ≤ ((eC c : EuclideanSpace ℝ (Fin n) × ℝ)).2 :=
      (Set.mem_Icc.mp (eC c).2.2).1
    have ht1 : ((eC c : EuclideanSpace ℝ (Fin n) × ℝ)).2 ≤ 1 :=
      (Set.mem_Icc.mp (eC c).2.2).2
    have hc0 : (0 : ℝ) ≤ 1 / 2 + ((eC c : EuclideanSpace ℝ (Fin n) × ℝ)).2 / 2 := by linarith
    rw [Real.norm_of_nonneg hc0,
      mem_sphere_zero_iff_norm.mp (uHomeo eA eC hAc hCc _).2, mul_one]
    linarith⟩

@[simp] private lemma fC_coe (eA : ↥A ≃ₜ eball n) (eC : ↥C ≃ₜ ↥(esphere n ×ˢ Set.Icc (0 : ℝ) 1))
    (hAc : A ∩ C = eA ⁻¹' bsphere n) (hCc : A ∩ C = eC ⁻¹' collarBot n) (c : ↥C) :
    ((fC eA eC hAc hCc c : eball n) : EuclideanSpace ℝ (Fin n))
      = (1 / 2 + ((eC c : EuclideanSpace ℝ (Fin n) × ℝ)).2 / 2) •
        ((uHomeo eA eC hAc hCc ⟨((eC c : EuclideanSpace ℝ (Fin n) × ℝ)).1,
          (eC c).2.1⟩ : esphere n) : EuclideanSpace ℝ (Fin n)) := rfl

private lemma norm_fC (eA : ↥A ≃ₜ eball n) (eC : ↥C ≃ₜ ↥(esphere n ×ˢ Set.Icc (0 : ℝ) 1))
    (hAc : A ∩ C = eA ⁻¹' bsphere n) (hCc : A ∩ C = eC ⁻¹' collarBot n) (c : ↥C) :
    ‖((fC eA eC hAc hCc c : eball n) : EuclideanSpace ℝ (Fin n))‖
      = 1 / 2 + ((eC c : EuclideanSpace ℝ (Fin n) × ℝ)).2 / 2 := by
  rw [fC_coe, norm_smul,
    Real.norm_of_nonneg (by
      have ht0 : 0 ≤ ((eC c : EuclideanSpace ℝ (Fin n) × ℝ)).2 :=
        (Set.mem_Icc.mp (eC c).2.2).1
      linarith),
    mem_sphere_zero_iff_norm.mp (uHomeo eA eC hAc hCc _).2, mul_one]

private lemma fC_injective (eA : ↥A ≃ₜ eball n) (eC : ↥C ≃ₜ ↥(esphere n ×ˢ Set.Icc (0 : ℝ) 1))
    (hAc : A ∩ C = eA ⁻¹' bsphere n) (hCc : A ∩ C = eC ⁻¹' collarBot n) :
    Function.Injective (fC eA eC hAc hCc) := by
  intro c₁ c₂ h
  have hnorm : 1 / 2 + ((eC c₁ : EuclideanSpace ℝ (Fin n) × ℝ)).2 / 2
      = 1 / 2 + ((eC c₂ : EuclideanSpace ℝ (Fin n) × ℝ)).2 / 2 := by
    have := congrArg (fun z : eball n => ‖(z : EuclideanSpace ℝ (Fin n))‖) h
    rwa [norm_fC, norm_fC] at this
  have ht0 : 0 ≤ ((eC c₂ : EuclideanSpace ℝ (Fin n) × ℝ)).2 :=
    (Set.mem_Icc.mp (eC c₂).2.2).1
  have hcoef : (1 / 2 + ((eC c₂ : EuclideanSpace ℝ (Fin n) × ℝ)).2 / 2) ≠ 0 := by linarith
  have hu : ((uHomeo eA eC hAc hCc ⟨((eC c₁ : EuclideanSpace ℝ (Fin n) × ℝ)).1,
        (eC c₁).2.1⟩ : esphere n) : EuclideanSpace ℝ (Fin n))
      = ((uHomeo eA eC hAc hCc ⟨((eC c₂ : EuclideanSpace ℝ (Fin n) × ℝ)).1,
        (eC c₂).2.1⟩ : esphere n) : EuclideanSpace ℝ (Fin n)) := by
    have := congrArg (fun z : eball n => (z : EuclideanSpace ℝ (Fin n))) h
    simp only [fC_coe] at this
    rw [hnorm] at this
    exact smul_right_injective (EuclideanSpace ℝ (Fin n)) hcoef this
  have hw : (⟨((eC c₁ : EuclideanSpace ℝ (Fin n) × ℝ)).1, (eC c₁).2.1⟩ : esphere n)
      = ⟨((eC c₂ : EuclideanSpace ℝ (Fin n) × ℝ)).1, (eC c₂).2.1⟩ :=
    (uHomeo eA eC hAc hCc).injective (Subtype.ext hu)
  have ht : ((eC c₁ : EuclideanSpace ℝ (Fin n) × ℝ)).2
      = ((eC c₂ : EuclideanSpace ℝ (Fin n) × ℝ)).2 := by linarith
  have hp : (eC c₁ : EuclideanSpace ℝ (Fin n) × ℝ)
      = (eC c₂ : EuclideanSpace ℝ (Fin n) × ℝ) := by
    rw [Prod.ext_iff]
    exact ⟨congrArg (fun v : esphere n => (v : EuclideanSpace ℝ (Fin n))) hw, ht⟩
  exact eC.injective (Subtype.ext hp)

/-- The two charts agree on `A ∩ C`. -/
private lemma fA_fC_compat (eA : ↥A ≃ₜ eball n) (eC : ↥C ≃ₜ ↥(esphere n ×ˢ Set.Icc (0 : ℝ) 1))
    (hAc : A ∩ C = eA ⁻¹' bsphere n) (hCc : A ∩ C = eC ⁻¹' collarBot n)
    (x : X) (hxA : x ∈ A) (hxC : x ∈ C) :
    fA eA ⟨x, hxA⟩ = fC eA eC hAc hCc ⟨x, hxC⟩ := by
  have hc : (eC ⟨x, hxC⟩ : EuclideanSpace ℝ (Fin n) × ℝ).2 = 0 :=
    eC_mem_bot_of_mem_A eC hCc ⟨x, hxC⟩ hxA
  apply Subtype.ext
  simp only [fA_coe, fC_coe]
  rw [show (⟨((eC ⟨x, hxC⟩ : EuclideanSpace ℝ (Fin n) × ℝ)).1,
        (eC ⟨x, hxC⟩).2.1⟩ : esphere n)
      = fstS n ⟨eC ⟨x, hxC⟩, eC_mem_bot_of_mem_A eC hCc ⟨x, hxC⟩ hxA⟩ from rfl]
  rw [uHomeo_apply, uFun_apply eA eC hAc hCc x hxA hxC]
  simp only [hc, zero_div, add_zero]

section Paste

open Classical

variable {A C : Set X}

/-- A point of `A ∪ C` which is not in `A` lies in `C`. -/
private theorem otherMem (hAC : A ∪ C = Set.univ) (x : X) (hx : x ∉ A) : x ∈ C := by
  rcases (Set.mem_union x A C).mp (by rw [hAC]; exact Set.mem_univ x) with h | h
  · exact absurd h hx
  · exact h

/-- The map glued from a map on `A` and a map on `C` along the closed cover `A ∪ C = X`. -/
private noncomputable def paste (hAC : A ∪ C = Set.univ) (f : ↥A → eball n) (g : ↥C → eball n) :
    X → eball n :=
  fun x => if hx : x ∈ A then f ⟨x, hx⟩ else g ⟨x, otherMem hAC x hx⟩

private lemma paste_mem {hAC : A ∪ C = Set.univ} {f : ↥A → eball n} {g : ↥C → eball n} {x : X}
    (hx : x ∈ A) : paste hAC f g x = f ⟨x, hx⟩ := dif_pos hx

private lemma paste_notMem {hAC : A ∪ C = Set.univ} {f : ↥A → eball n} {g : ↥C → eball n} {x : X}
    (hx : x ∉ A) : paste hAC f g x = g ⟨x, otherMem hAC x hx⟩ := dif_neg hx

private lemma continuous_paste (hA : IsClosed A) (hC : IsClosed C) (hAC : A ∪ C = Set.univ)
    (f : ↥A → eball n) (g : ↥C → eball n) (hf : Continuous f) (hg : Continuous g)
    (hfg : ∀ (x : ↥A) (y : ↥C), (x : X) = (y : X) → f x = g y) :
    Continuous (paste hAC f g) := by
  have hleft : ContinuousOn (paste hAC f g) A := by
    rw [continuousOn_iff_continuous_domRestrict]
    have hEq : A.domRestrict (paste hAC f g) = f := by
      funext x
      show paste hAC f g (x : X) = f x
      rw [paste_mem x.2]
    rw [hEq]; exact hf
  have hright : ContinuousOn (paste hAC f g) C := by
    rw [continuousOn_iff_continuous_domRestrict]
    have hEq : C.domRestrict (paste hAC f g) = g := by
      funext y
      show paste hAC f g (y : X) = g y
      by_cases hy : (y : X) ∈ A
      · rw [paste_mem hy]
        exact hfg ⟨y, hy⟩ y rfl
      · rw [paste_notMem hy]
    rw [hEq]; exact hg
  have hcont := hleft.union_of_isClosed hright hA hC
  rwa [hAC, continuousOn_univ] at hcont

end Paste

/-- Continuity of the inner disk chart. -/
private lemma continuous_fA (eA : ↥A ≃ₜ eball n) : Continuous (fA eA) := by
  have hcont : Continuous
      (fun a : ↥A => (1 / 2 : ℝ) • (eA a : EuclideanSpace ℝ (Fin n))) := by fun_prop
  exact Continuous.subtype_mk hcont (fun a => (fA eA a).2)

/-- Continuity of the outer annulus chart. -/
private lemma continuous_fC (eA : ↥A ≃ₜ eball n) (eC : ↥C ≃ₜ ↥(esphere n ×ˢ Set.Icc (0 : ℝ) 1))
    (hAc : A ∩ C = eA ⁻¹' bsphere n) (hCc : A ∩ C = eC ⁻¹' collarBot n) :
    Continuous (fC eA eC hAc hCc) := by
  have hcont : Continuous (fun c : ↥C =>
      (1 / 2 + ((eC c : EuclideanSpace ℝ (Fin n) × ℝ)).2 / 2) •
        ((uHomeo eA eC hAc hCc ⟨((eC c : EuclideanSpace ℝ (Fin n) × ℝ)).1,
          (eC c).2.1⟩ : esphere n) : EuclideanSpace ℝ (Fin n))) := by
    have h1 : Continuous fun c : ↥C => ((eC c : EuclideanSpace ℝ (Fin n) × ℝ)) :=
      continuous_subtype_val.comp eC.continuous
    have h2 : Continuous fun c : ↥C => ((eC c : EuclideanSpace ℝ (Fin n) × ℝ)).2 :=
      continuous_snd.comp h1
    have h3 : Continuous fun c : ↥C =>
        (1 / 2 + ((eC c : EuclideanSpace ℝ (Fin n) × ℝ)).2 / 2) :=
      continuous_const.add (h2.div_const 2)
    have h4 : Continuous fun c : ↥C => (⟨((eC c : EuclideanSpace ℝ (Fin n) × ℝ)).1,
        (eC c).2.1⟩ : esphere n) :=
      Continuous.subtype_mk (continuous_fst.comp h1) (fun c => (eC c).2.1)
    have h5 : Continuous fun c : ↥C =>
        ((uHomeo eA eC hAc hCc ⟨((eC c : EuclideanSpace ℝ (Fin n) × ℝ)).1,
          (eC c).2.1⟩ : esphere n) : EuclideanSpace ℝ (Fin n)) :=
      continuous_subtype_val.comp ((uHomeo eA eC hAc hCc).continuous.comp h4)
    exact h3.smul h5
  exact Continuous.subtype_mk hcont (fun c => (fC eA eC hAc hCc c).2)

/-- If `fA a = fC b` then the underlying points of `X` agree. -/
private lemma cross_eq (eA : ↥A ≃ₜ eball n) (eC : ↥C ≃ₜ ↥(esphere n ×ˢ Set.Icc (0 : ℝ) 1))
    (hAc : A ∩ C = eA ⁻¹' bsphere n) (hCc : A ∩ C = eC ⁻¹' collarBot n)
    (a : ↥A) (b : ↥C) (hz : fA eA a = fC eA eC hAc hCc b) : (a : X) = (b : X) := by
  have hnorm : (1 / 2 : ℝ) * ‖(eA a : EuclideanSpace ℝ (Fin n))‖
      = 1 / 2 + ((eC b : EuclideanSpace ℝ (Fin n) × ℝ)).2 / 2 := by
    have := congrArg (fun z : eball n => ‖(z : EuclideanSpace ℝ (Fin n))‖) hz
    rwa [norm_fA, norm_fC] at this
  have hle : ‖(eA a : EuclideanSpace ℝ (Fin n))‖ ≤ 1 := norm_le_one_of_mem (eA a)
  have ht0 : 0 ≤ ((eC b : EuclideanSpace ℝ (Fin n) × ℝ)).2 :=
    (Set.mem_Icc.mp (eC b).2.2).1
  have hae : ‖(eA a : EuclideanSpace ℝ (Fin n))‖ = 1 := by linarith
  have hbt : ((eC b : EuclideanSpace ℝ (Fin n) × ℝ)).2 = 0 := by linarith
  have haC : (a : X) ∈ C := mem_C_of_eA_bsphere eA hAc a ((bsphere_mem_iff n (eA a)).mpr hae)
  have hbA : (b : X) ∈ A := mem_A_of_eC_bot eC hCc b hbt
  have hcompat := fA_fC_compat eA eC hAc hCc (b : X) hbA b.2
  have h2 : fA eA a = fA eA ⟨(b : X), hbA⟩ := by rw [hz, hcompat]
  exact congrArg Subtype.val (fA_injective eA h2)

/-- Injectivity of the glued map. -/
private lemma injective_paste (hAC : A ∪ C = Set.univ) (eA : ↥A ≃ₜ eball n)
    (eC : ↥C ≃ₜ ↥(esphere n ×ˢ Set.Icc (0 : ℝ) 1))
    (hAc : A ∩ C = eA ⁻¹' bsphere n) (hCc : A ∩ C = eC ⁻¹' collarBot n) :
    Function.Injective (paste hAC (fA eA) (fC eA eC hAc hCc)) := by
  intro x y hxy
  by_cases hxA : x ∈ A
  · by_cases hyA : y ∈ A
    · have h' : fA eA ⟨x, hxA⟩ = fA eA ⟨y, hyA⟩ := by
        rw [← paste_mem (hAC := hAC) (f := fA eA) (g := fC eA eC hAc hCc) hxA,
            ← paste_mem (hAC := hAC) (f := fA eA) (g := fC eA eC hAc hCc) hyA]
        exact hxy
      exact Subtype.ext_iff.mp (fA_injective eA h')
    · have hCy : y ∈ C := otherMem hAC y hyA
      have hz : fA eA ⟨x, hxA⟩ = fC eA eC hAc hCc ⟨y, hCy⟩ := by
        rw [← paste_mem (hAC := hAC) (f := fA eA) (g := fC eA eC hAc hCc) hxA,
            ← paste_notMem (hAC := hAC) (f := fA eA) (g := fC eA eC hAc hCc) hyA]
        exact hxy
      exact cross_eq eA eC hAc hCc ⟨x, hxA⟩ ⟨y, hCy⟩ hz
  · by_cases hyA : y ∈ A
    · have hCx : x ∈ C := otherMem hAC x hxA
      have hz : fC eA eC hAc hCc ⟨x, hCx⟩ = fA eA ⟨y, hyA⟩ := by
        rw [← paste_notMem (hAC := hAC) (f := fA eA) (g := fC eA eC hAc hCc) hxA,
            ← paste_mem (hAC := hAC) (f := fA eA) (g := fC eA eC hAc hCc) hyA]
        exact hxy
      exact (cross_eq eA eC hAc hCc ⟨y, hyA⟩ ⟨x, hCx⟩ hz.symm).symm
    · have hCx : x ∈ C := otherMem hAC x hxA
      have hCy : y ∈ C := otherMem hAC y hyA
      have hz : fC eA eC hAc hCc ⟨x, hCx⟩ = fC eA eC hAc hCc ⟨y, hCy⟩ := by
        rw [← paste_notMem (hAC := hAC) (f := fA eA) (g := fC eA eC hAc hCc) hxA,
            ← paste_notMem (hAC := hAC) (f := fA eA) (g := fC eA eC hAc hCc) hyA]
        exact hxy
      exact Subtype.ext_iff.mp (fC_injective eA eC hAc hCc hz)


/-- Surjectivity of the glued map. -/
private lemma surjective_paste (hAC : A ∪ C = Set.univ) (eA : ↥A ≃ₜ eball n)
    (eC : ↥C ≃ₜ ↥(esphere n ×ˢ Set.Icc (0 : ℝ) 1))
    (hAc : A ∩ C = eA ⁻¹' bsphere n) (hCc : A ∩ C = eC ⁻¹' collarBot n) :
    Function.Surjective (paste hAC (fA eA) (fC eA eC hAc hCc)) := by
  intro z
  by_cases hz : ‖(z : EuclideanSpace ℝ (Fin n))‖ ≤ 1 / 2
  · have hmem : (2 : ℝ) • (z : EuclideanSpace ℝ (Fin n)) ∈ eball n := by
      rw [Metric.mem_closedBall, dist_zero_right, norm_smul,
        Real.norm_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
      have := norm_le_one_of_mem z
      linarith
    set a : ↥A := eA.symm ⟨(2 : ℝ) • (z : EuclideanSpace ℝ (Fin n)), hmem⟩ with ha_def
    refine ⟨(a : X), ?_⟩
    rw [paste_mem (hAC := hAC) (f := fA eA) (g := fC eA eC hAc hCc) a.2]
    apply Subtype.ext
    rw [fA_coe, ha_def, Homeomorph.apply_symm_apply]
    simp only [Subtype.coe_mk]
    module
  · push_neg at hz
    have hr1 : ‖(z : EuclideanSpace ℝ (Fin n))‖ ≤ 1 := norm_le_one_of_mem z
    have hr0 : (0 : ℝ) < ‖(z : EuclideanSpace ℝ (Fin n))‖ := by linarith
    set t : ℝ := 2 * ‖(z : EuclideanSpace ℝ (Fin n))‖ - 1 with ht_def
    have ht0 : 0 ≤ t := by rw [ht_def]; linarith
    have ht1 : t ≤ 1 := by rw [ht_def]; linarith
    set v : esphere n := ⟨(‖(z : EuclideanSpace ℝ (Fin n))‖)⁻¹ •
        (z : EuclideanSpace ℝ (Fin n)), by
        rw [mem_sphere_zero_iff_norm, norm_smul, norm_inv,
          Real.norm_of_nonneg (norm_nonneg _)]
        exact inv_mul_cancel₀ (ne_of_gt hr0)⟩ with hv_def
    set w : esphere n := (uHomeo eA eC hAc hCc).symm v with hw_def
    set c : ↥C := eC.symm ⟨((w : EuclideanSpace ℝ (Fin n)), t), by
        rw [Set.mem_prod]
        exact ⟨w.2, Set.mem_Icc.mpr ⟨ht0, ht1⟩⟩⟩ with hc_def
    have heCc : (eC c : EuclideanSpace ℝ (Fin n) × ℝ)
        = ((w : EuclideanSpace ℝ (Fin n)), t) := by
      rw [hc_def, Homeomorph.apply_symm_apply]
    have huw : (uHomeo eA eC hAc hCc ⟨((eC c : EuclideanSpace ℝ (Fin n) × ℝ)).1,
        (eC c).2.1⟩ : esphere n) = v := by
      have h1 : (⟨((eC c : EuclideanSpace ℝ (Fin n) × ℝ)).1, (eC c).2.1⟩ : esphere n) = w := by
        apply Subtype.ext
        show ((eC c : EuclideanSpace ℝ (Fin n) × ℝ)).1 = (w : EuclideanSpace ℝ (Fin n))
        rw [heCc]
      rw [h1, hw_def, Homeomorph.apply_symm_apply]
    refine ⟨(c : X), ?_⟩
    by_cases hcA : (c : X) ∈ A
    · have ht_eq : t = 0 := by
        have h := congrArg (fun p : EuclideanSpace ℝ (Fin n) × ℝ => p.2) heCc
        rw [show (eC c : EuclideanSpace ℝ (Fin n) × ℝ).2 = 0 from
          eC_mem_bot_of_mem_A eC hCc c hcA] at h
        simpa using h.symm
      have hz_half : ‖(z : EuclideanSpace ℝ (Fin n))‖ = 1 / 2 := by
        rw [ht_def] at ht_eq; linarith
      rw [paste_mem (hAC := hAC) (f := fA eA) (g := fC eA eC hAc hCc) hcA]
      apply Subtype.ext
      rw [fA_coe]
      have heA : (eA ⟨(c : X), hcA⟩ : EuclideanSpace ℝ (Fin n))
          = (v : EuclideanSpace ℝ (Fin n)) := by
        rw [← uFun_apply' eA eC hAc hCc (c : X) hcA c.2]
        exact congrArg (fun x : esphere n => (x : EuclideanSpace ℝ (Fin n))) huw
      rw [heA, hv_def]
      simp only [Subtype.coe_mk]
      rw [hz_half]
      module
    · rw [paste_notMem (hAC := hAC) (f := fA eA) (g := fC eA eC hAc hCc) hcA]
      apply Subtype.ext
      rw [fC_coe]
      have hcc : (⟨(c : X), otherMem hAC (c : X) hcA⟩ : ↥C) = c := Subtype.ext rfl
      have hct : (eC c : EuclideanSpace ℝ (Fin n) × ℝ).2 = t := by rw [heCc]
      rw [hcc, huw, hct]
      have hcoef : (1 / 2 + t / 2 : ℝ) = ‖(z : EuclideanSpace ℝ (Fin n))‖ := by
        rw [ht_def]; ring
      rw [hcoef, hv_def]
      simp only [Subtype.coe_mk]
      rw [smul_smul, mul_inv_cancel₀ (ne_of_gt hr0), one_smul]

end

end Main

/-- The `t = 1` slice of the collar `S^{n-1} × [0,1]`. -/
private def collarTop (n : ℕ) : Set ↥(esphere n ×ˢ Set.Icc (0 : ℝ) 1) :=
  {p | (p : EuclideanSpace ℝ (Fin n) × ℝ).2 = 1}

open TwoDiskStrong in
/-- **Gluing a collar to a disk yields a disk.**  If `X = A ∪ C` with `A`, `C` closed, `A` a disk
and `C` a collar `S^{n-1} × [0,1]` glued along the boundary sphere of `A` (the `t = 0` slice), then
`X` is homeomorphic to a disk, and the homeomorphism can be arranged so that the boundary of `X`
corresponds to the `t = 1` slice of the collar. -/
theorem disk_glue_collar {n : ℕ} {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
    {A C : Set X} (hA : IsClosed A) (hC : IsClosed C) (hAC : A ∪ C = Set.univ)
    (eA : A ≃ₜ Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) 1)
    (hAc : A ∩ C = eA ⁻¹' (Metric.sphere (0 : Metric.closedBall
      (0 : EuclideanSpace ℝ (Fin n)) 1) 1))
    (eC : C ≃ₜ (Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1 ×ˢ Set.Icc (0 : ℝ) 1))
    (hCc : A ∩ C = eC ⁻¹' {p : ↥(Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1 ×ˢ
        Set.Icc (0 : ℝ) 1) | (p : EuclideanSpace ℝ (Fin n) × ℝ).2 = 0}) :
    ∃ e : X ≃ₜ Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) 1,
      e ⁻¹' (Metric.sphere (0 : Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) 1) 1)
        = eC ⁻¹' {p : ↥(Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1 ×ˢ
            Set.Icc (0 : ℝ) 1) | (p : EuclideanSpace ℝ (Fin n) × ℝ).2 = 1} := by
  classical
  have hAc' : A ∩ C = eA ⁻¹' bsphere n := hAc
  have hCc' : A ∩ C = eC ⁻¹' collarBot n := hCc
  have hinj := injective_paste hAC eA eC hAc' hCc'
  have hsurj := surjective_paste hAC eA eC hAc' hCc'
  have hcont := continuous_paste hA hC hAC (fA eA) (fC eA eC hAc' hCc')
    (continuous_fA eA) (continuous_fC eA eC hAc' hCc')
    (fun x y hxy => by
      rw [show x = (⟨(y : X), hxy ▸ x.2⟩ : ↥A) from Subtype.ext hxy]
      exact fA_fC_compat eA eC hAc' hCc' (y : X) (hxy ▸ x.2) y.2)
  let f : X ≃ eball n :=
    Equiv.ofBijective (paste hAC (fA eA) (fC eA eC hAc' hCc')) ⟨hinj, hsurj⟩
  have hfc : Continuous (f : X → eball n) := hcont
  let e : X ≃ₜ eball n := Continuous.homeoOfEquivCompactToT2 (f := f) hfc
  have he_apply : ∀ x : X, e x = paste hAC (fA eA) (fC eA eC hAc' hCc') x := fun x => rfl
  have hbound : ∀ x : X, e x ∈ bsphere n ↔
      ∃ (hx : x ∈ C), (eC ⟨x, hx⟩ : EuclideanSpace ℝ (Fin n) × ℝ).2 = 1 := by
    intro x
    by_cases hxA : x ∈ A
    · rw [he_apply x, paste_mem (hAC := hAC) (f := fA eA) (g := fC eA eC hAc' hCc') hxA]
      constructor
      · intro hmem
        have hn : ‖((fA eA ⟨x, hxA⟩ : eball n) : EuclideanSpace ℝ (Fin n))‖ = 1 :=
          (bsphere_mem_iff n _).mp hmem
        have hle : ‖((fA eA ⟨x, hxA⟩ : eball n) : EuclideanSpace ℝ (Fin n))‖ ≤ 1 / 2 := by
          rw [norm_fA]
          have := norm_le_one_of_mem (eA ⟨x, hxA⟩)
          linarith
        linarith
      · rintro ⟨hxC, h1⟩
        exfalso
        have h0 : (eC ⟨x, hxC⟩ : EuclideanSpace ℝ (Fin n) × ℝ).2 = 0 :=
          eC_mem_bot_of_mem_A eC hCc' ⟨x, hxC⟩ hxA
        linarith
    · have hxC : x ∈ C := otherMem hAC x hxA
      rw [he_apply x, paste_notMem (hAC := hAC) (f := fA eA) (g := fC eA eC hAc' hCc') hxA]
      rw [show fC eA eC hAc' hCc' ⟨x, otherMem hAC x hxA⟩
          = fC eA eC hAc' hCc' ⟨x, hxC⟩ from congrArg _ (Subtype.ext rfl)]
      rw [bsphere_mem_iff, norm_fC]
      constructor
      · intro h
        exact ⟨hxC, by linarith⟩
      · rintro ⟨hx, h1⟩
        have h2 : (eC ⟨x, hxC⟩ : EuclideanSpace ℝ (Fin n) × ℝ).2 = 1 := by
          rw [show (⟨x, hxC⟩ : ↥C) = ⟨x, hx⟩ from Subtype.ext rfl]
          exact h1
        linarith
  have hmem_c : ∀ x : X, x ∈ Subtype.val '' (eC ⁻¹' collarTop n) ↔
      ∃ (hx : x ∈ C), (eC ⟨x, hx⟩ : EuclideanSpace ℝ (Fin n) × ℝ).2 = 1 := by
    intro x
    constructor
    · rintro ⟨c, hc, hcx⟩
      exact ⟨hcx ▸ c.2, by
        rw [show (⟨x, hcx ▸ c.2⟩ : ↥C) = c from Subtype.ext hcx.symm]
        exact hc⟩
    · rintro ⟨hx, h1⟩
      exact ⟨⟨x, hx⟩, h1, rfl⟩
  have hset : e ⁻¹' bsphere n = Subtype.val '' (eC ⁻¹' collarTop n) := by
    ext x
    rw [Set.mem_preimage, hmem_c x]
    exact hbound x
  exact ⟨e, hset⟩

end Commons.Topology.Sphere
