import Mathlib
import Submission.Work.Agree.S4Bundle
import Submission.Work.Thom.BundleIso_comap_exists

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

open scoped Topology

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option maxRecDepth 16000

/-!
# Auxiliary material for the stable triviality of `clutchBundle 1 1`
-/

namespace Work.Agree

open Work.TangentClasses

noncomputable section

/-! ## Reflections of `ℍ × ℝ` -/

/-- The model fibre `ℝ⁵ = ℍ × ℝ`. -/
abbrev H5 : Type := Quaternion ℝ × ℝ

/-- The `ℓ²` pairing `⟨(w,d),(v,t)⟩ = ⟪w,v⟫ + d*t`. -/
def pairing (u p : H5) : ℝ := inner ℝ u.1 p.1 + u.2 * p.2

/-- The pair of unit vectors `(w,d)`. -/
def mk (w : Quaternion ℝ) (d : ℝ) : H5 := (w, d)

lemma pairing_mk_mk (w : Quaternion ℝ) (d : ℝ) :
    pairing (mk w d) (mk w d) = inner ℝ w w + d * d := by
  simp [pairing, mk]

lemma pairing_mk (w : Quaternion ℝ) (d : ℝ) (v : Quaternion ℝ) (t : ℝ) :
    pairing (mk w d) (v, t) = inner ℝ w v + d * t := rfl

/-- The pairing with `u`, as a continuous linear functional. -/
def pairingCLM (u : H5) : H5 →L[ℝ] ℝ :=
  (innerSL ℝ u.1).comp (ContinuousLinearMap.fst ℝ (Quaternion ℝ) ℝ)
    + u.2 • (ContinuousLinearMap.snd ℝ (Quaternion ℝ) ℝ)

lemma pairingCLM_apply (u p : H5) : pairingCLM u p = pairing u p := by
  simp [pairingCLM, pairing, innerSL_apply_apply]

lemma pairing_sub_right (u p q : H5) : pairing u (p - q) = pairing u p - pairing u q := by
  obtain ⟨w,d⟩ := u; obtain ⟨v,t⟩ := p; obtain ⟨v',t'⟩ := q
  simp only [pairing, Prod.fst_sub, Prod.snd_sub]
  rw [inner_sub_right]; ring

lemma pairing_smul_right (u : H5) (c : ℝ) (p : H5) :
    pairing u (c • p) = c * pairing u p := by
  obtain ⟨w,d⟩ := u; obtain ⟨v,t⟩ := p
  simp only [pairing, Prod.smul_fst, Prod.smul_snd]
  rw [inner_smul_right]; ring

/-- The reflection of `ℍ × ℝ` in the hyperplane orthogonal to `u`: `p ↦ p - 2⟨u,p⟩u`. -/
def reflU (u : H5) : H5 →L[ℝ] H5 :=
  ContinuousLinearMap.id ℝ H5 - (2:ℝ) • (ContinuousLinearMap.smulRight (pairingCLM u) u)

lemma reflU_apply (u p : H5) : reflU u p = p - (2 * pairing u p) • u := by
  simp [reflU, pairingCLM_apply, ContinuousLinearMap.smulRight_apply, smul_smul]

/-- The reflection is an involution for a unit vector `u`. -/
lemma reflU_comp_self (u : H5) (h : pairing u u = 1) :
    (reflU u).comp (reflU u) = ContinuousLinearMap.id ℝ H5 := by
  apply ContinuousLinearMap.ext
  intro p
  rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply, reflU_apply, reflU_apply,
    pairing_sub_right, pairing_smul_right, h]
  module

/-! ## The null-homotopy of the clutching -/

/-- `c s = cos (s π / 2)`. -/
def cS (s : ℝ) : ℝ := Real.cos (s * Real.pi / 2)

/-- `d s = sin (s π / 2)`. -/
def dS (s : ℝ) : ℝ := Real.sin (s * Real.pi / 2)

lemma cS_sq_add_dS_sq (s : ℝ) : cS s ^ 2 + dS s ^ 2 = 1 := by
  rw [cS, dS, ← Real.cos_sq_add_sin_sq (s * Real.pi / 2)]

@[simp] lemma cS_zero : cS 0 = 1 := by simp [cS]
@[simp] lemma dS_zero : dS 0 = 0 := by simp [dS]
@[simp] lemma cS_one : cS 1 = 0 := by
  rw [cS, show (1:ℝ) * Real.pi / 2 = Real.pi / 2 by ring, Real.cos_pi_div_two]
@[simp] lemma dS_one : dS 1 = 1 := by
  rw [dS, show (1:ℝ) * Real.pi / 2 = Real.pi / 2 by ring, Real.sin_pi_div_two]

lemma reflU_mk_apply (w : Quaternion ℝ) (d : ℝ) (v : Quaternion ℝ) (t : ℝ) :
    reflU (mk w d) (v, t) =
      (v - (2 * (inner ℝ w v + d * t)) • w, t - 2 * (inner ℝ w v + d * t) * d) := by
  rw [reflU_apply, pairing_mk]
  rfl

/-- The operator `v ↦ q * v * q` on `ℍ × ℝ`. -/
def QopCLM (q : Quaternion ℝ) : H5 →L[ℝ] H5 :=
  (((ContinuousLinearMap.mul ℝ (Quaternion ℝ)).flip q).comp
      ((ContinuousLinearMap.mul ℝ (Quaternion ℝ)) q)).prodMap
    (ContinuousLinearMap.id ℝ ℝ)

lemma QopCLM_apply (q : Quaternion ℝ) (v : Quaternion ℝ) (t : ℝ) :
    QopCLM q (v, t) = (q * v * q, t) := by
  simp [QopCLM]

/-- The null-homotopy: `M_s(q) = R_{z_s(q)} ∘ R_{w_s}` for `w_s = (c_s, d_s)`,
`z_s(q) = (c_s q, d_s)`. -/
def MsCLM (s : ℝ) (q : Quaternion ℝ) : H5 →L[ℝ] H5 :=
  (reflU (mk (cS s • q) (dS s))).comp (reflU (mk (cS s • (1:Quaternion ℝ)) (dS s)))

/-- The pointwise inverse of `MsCLM s q`. -/
def MsInvCLM (s : ℝ) (q : Quaternion ℝ) : H5 →L[ℝ] H5 :=
  (reflU (mk (cS s • (1:Quaternion ℝ)) (dS s))).comp (reflU (mk (cS s • q) (dS s)))

lemma pairing_mk_self (s : ℝ) (q : Quaternion ℝ) (hq : inner ℝ q q = 1) :
    pairing (mk (cS s • q) (dS s)) (mk (cS s • q) (dS s)) = 1 := by
  rw [pairing_mk_mk]
  have h1 : inner ℝ (cS s • q) (cS s • q) = cS s ^ 2 * inner ℝ q q := by
    rw [real_inner_smul_left, real_inner_smul_right]; ring
  rw [h1, hq]
  have := cS_sq_add_dS_sq s
  nlinarith

lemma pairing_mk_unit (s : ℝ) :
    pairing (mk (cS s • (1:Quaternion ℝ)) (dS s))
      (mk (cS s • (1:Quaternion ℝ)) (dS s)) = 1 := by
  rw [pairing_mk_mk]
  have h1 : inner ℝ (cS s • (1:Quaternion ℝ)) (cS s • (1:Quaternion ℝ)) = cS s ^ 2 := by
    rw [real_inner_smul_left, real_inner_smul_right]; simp; ring
  rw [h1]
  have := cS_sq_add_dS_sq s
  linarith

lemma MsInvCLM_comp_MsCLM (s : ℝ) (q : Quaternion ℝ) (hq : inner ℝ q q = 1) :
    (MsInvCLM s q).comp (MsCLM s q) = ContinuousLinearMap.id ℝ H5 := by
  have hRz := reflU_comp_self (mk (cS s • q) (dS s)) (pairing_mk_self s q hq)
  have hRw := reflU_comp_self (mk (cS s • (1:Quaternion ℝ)) (dS s)) (pairing_mk_unit s)
  show (reflU (mk (cS s • (1:Quaternion ℝ)) (dS s))).comp
      ((reflU (mk (cS s • q) (dS s))).comp
        ((reflU (mk (cS s • q) (dS s))).comp
          (reflU (mk (cS s • (1:Quaternion ℝ)) (dS s)))))
    = ContinuousLinearMap.id ℝ H5
  rw [← ContinuousLinearMap.comp_assoc (reflU (mk (cS s • q) (dS s)))
        (reflU (mk (cS s • q) (dS s))) (reflU (mk (cS s • (1:Quaternion ℝ)) (dS s)))]
  rw [hRz, ContinuousLinearMap.id_comp, hRw]

lemma MsCLM_comp_MsInvCLM (s : ℝ) (q : Quaternion ℝ) (hq : inner ℝ q q = 1) :
    (MsCLM s q).comp (MsInvCLM s q) = ContinuousLinearMap.id ℝ H5 := by
  have hRz := reflU_comp_self (mk (cS s • q) (dS s)) (pairing_mk_self s q hq)
  have hRw := reflU_comp_self (mk (cS s • (1:Quaternion ℝ)) (dS s)) (pairing_mk_unit s)
  show (reflU (mk (cS s • q) (dS s))).comp
      ((reflU (mk (cS s • (1:Quaternion ℝ)) (dS s))).comp
        ((reflU (mk (cS s • (1:Quaternion ℝ)) (dS s))).comp
          (reflU (mk (cS s • q) (dS s)))))
    = ContinuousLinearMap.id ℝ H5
  rw [← ContinuousLinearMap.comp_assoc (reflU (mk (cS s • (1:Quaternion ℝ)) (dS s)))
        (reflU (mk (cS s • (1:Quaternion ℝ)) (dS s))) (reflU (mk (cS s • q) (dS s)))]
  rw [hRw, ContinuousLinearMap.id_comp, hRz]

@[simp] lemma MsCLM_one (q : Quaternion ℝ) :
    MsCLM 1 q = ContinuousLinearMap.id ℝ H5 := by
  have h : mk (cS 1 • q) (dS 1) = mk (cS 1 • (1:Quaternion ℝ)) (dS 1) := by simp
  rw [MsCLM, h]
  exact reflU_comp_self _ (by rw [pairing_mk_mk]; simp)

/-! ### The value at `s = 0` -/

lemma inner_one_left (v : Quaternion ℝ) : inner ℝ (1:Quaternion ℝ) v = v.re := by
  rw [Quaternion.inner_def]; simp

lemma sub_two_re_smul_one (v : Quaternion ℝ) :
    v - (2 * v.re : ℝ) • (1:Quaternion ℝ) = - star v := by
  rw [Quaternion.star_eq_two_re_sub, neg_sub]
  congr 1
  rw [Algebra.smul_def, Quaternion.algebraMap_def, mul_one]

lemma inner_neg_star (q v : Quaternion ℝ) : inner ℝ q (- star v) = -(q * v).re := by
  rw [inner_neg_right, Quaternion.inner_def]
  simp

lemma two_re_smul_eq (q v : Quaternion ℝ) (hq : star q * q = 1) :
    (2 * (q * v).re : ℝ) • (q : Quaternion ℝ) = q * v * q + star v := by
  rw [Algebra.smul_def, Quaternion.algebraMap_def, ← Quaternion.self_add_star']
  rw [add_mul, star_mul, mul_assoc (star v) (star q) q, hq, mul_one]

lemma MsCLM_zero (q : Quaternion ℝ) (hq : inner ℝ q q = 1) :
    MsCLM 0 q = QopCLM q := by
  have hstar : star q * q = 1 := by
    have h1 : Quaternion.normSq q = 1 := by rw [← Quaternion.inner_self]; exact hq
    rw [Quaternion.star_mul_self, h1]; norm_num
  apply ContinuousLinearMap.ext
  intro p
  obtain ⟨v, t⟩ := p
  rw [MsCLM, QopCLM_apply, ContinuousLinearMap.comp_apply, reflU_mk_apply, reflU_mk_apply]
  simp only [cS_zero, dS_zero, one_smul, mul_zero, zero_mul, add_zero, sub_zero]
  apply Prod.ext
  · rw [inner_one_left, sub_two_re_smul_one, inner_neg_star]
    rw [show (2 * (-(q * v).re)) = -(2 * (q * v).re) by ring, neg_smul, sub_neg_eq_add]
    rw [two_re_smul_eq q v hstar]
    abel
  · simp

end

end Work.Agree

namespace Work.Agree

open Work.TangentClasses

noncomputable section

/-! ## The identification of the fibre with `ℍ × ℝ` -/

/-- `ℝ⁴ ≃ ℍ`. -/
def e4 : EuclideanSpace ℝ (Fin 4) ≃L[ℝ] Quaternion ℝ :=
  Quaternion.linearIsometryEquivTuple.symm.toContinuousLinearEquiv

/-- `ℝ¹ ≃ ℝ`. -/
def e1 : EuclideanSpace ℝ (Fin 1) ≃L[ℝ] ℝ :=
  (EuclideanSpace.equiv (Fin 1) ℝ).trans (ContinuousLinearEquiv.funUnique (Fin 1) ℝ ℝ)

/-- `ℝ⁴ × ℝ¹ ≃ ℍ × ℝ`. -/
def e45 : (EuclideanSpace ℝ (Fin 4) × EuclideanSpace ℝ (Fin 1)) ≃L[ℝ] H5 :=
  e4.prodCongr e1

/-- `ℝ⁵ ≃ ℍ × ℝ`. -/
def e5 : EuclideanSpace ℝ (Fin 5) ≃L[ℝ] H5 :=
  (EuclideanSpace.finAddEquivProd (n := 4) (m := 1)).trans e45

@[simp] lemma e4_apply (v : EuclideanSpace ℝ (Fin 4)) :
    e4 v = Quaternion.linearIsometryEquivTuple.symm v := rfl

lemma e4_ofQ (v : Quaternion ℝ) : e4 (ofQ v) = v := by
  rw [e4_apply]
  show Quaternion.linearIsometryEquivTuple.symm (Quaternion.linearIsometryEquivTuple v) = v
  exact Quaternion.linearIsometryEquivTuple.symm_apply_apply v

lemma e4_eq_toQ (v : EuclideanSpace ℝ (Fin 4)) : e4 v = toQ v := rfl

lemma e45_apply (v : EuclideanSpace ℝ (Fin 4)) (t : EuclideanSpace ℝ (Fin 1)) :
    e45 (v, t) = (e4 v, e1 t) := rfl

lemma e45_symm_apply (p : H5) : e45.symm p = (e4.symm p.1, e1.symm p.2) := rfl

/-- The operator `v ↦ q^a * v * q^b` on `ℍ × ℝ`. -/
def QzCLM (a b : ℤ) (q : Quaternion ℝ) : H5 →L[ℝ] H5 :=
  (((ContinuousLinearMap.mul ℝ (Quaternion ℝ)).flip (q ^ b)).comp
      ((ContinuousLinearMap.mul ℝ (Quaternion ℝ)) (q ^ a))).prodMap
    (ContinuousLinearMap.id ℝ ℝ)

lemma QzCLM_apply (a b : ℤ) (q v : Quaternion ℝ) (t : ℝ) :
    QzCLM a b q (v, t) = (q ^ a * v * q ^ b, t) := by
  simp [QzCLM]

lemma QzCLM_one_one : QzCLM 1 1 = QopCLM := by
  funext q; rw [QopCLM, QzCLM]; norm_num

lemma e4_qTwist (a b : ℤ) (q : Quaternion ℝ) (w : EuclideanSpace ℝ (Fin 4)) :
    e4 (qTwist a b q w) = q ^ a * e4 w * q ^ b := by
  rw [qTwist_apply, e4_ofQ]
  rfl

/-- **The transition functions of `clutchBundle a b` are `QzCLM a b` in the model `ℍ × ℝ`.** -/
lemma e45_qTwist (a b : ℤ) (q : Quaternion ℝ) :
    (e45 : _ →L[ℝ] H5).comp
        (((qTwist a b q).prodMap (ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin 1)))).comp
          (e45.symm : H5 →L[ℝ] _))
      = QzCLM a b q := by
  apply ContinuousLinearMap.ext
  intro p
  obtain ⟨v, t⟩ := p
  show e45 (((qTwist a b q).prodMap
      (ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin 1)))) (e45.symm (v, t)))
    = QzCLM a b q (v, t)
  have hsymm : e45.symm (v, t) = (e4.symm v, e1.symm t) := rfl
  rw [hsymm, QzCLM_apply]
  show (e4 (qTwist a b q (e4.symm v)), e1 (e1.symm t)) = (q ^ a * v * q ^ b, t)
  rw [e4_qTwist, e4.apply_symm_apply, e1.apply_symm_apply]

end

end Work.Agree

namespace Work.Agree

open Work.TangentClasses

noncomputable section

/-! ## The bump function -/

/-- The bump function `ψ` of `ℝ⁴`: `1` on `‖x‖ ≤ 1/2`, `0` on `‖x‖ ≥ 1`. -/
def psi (x : EuclideanSpace ℝ (Fin 4)) : ℝ := min 1 (max 0 (2 - 2 * ‖x‖))

lemma psi_nonneg (x : EuclideanSpace ℝ (Fin 4)) : 0 ≤ psi x := le_min zero_le_one (le_max_left _ _)

lemma psi_le_one (x : EuclideanSpace ℝ (Fin 4)) : psi x ≤ 1 := min_le_left _ _

lemma psi_eq_one {x : EuclideanSpace ℝ (Fin 4)} (hx : ‖x‖ ≤ 1/2) : psi x = 1 := by
  rw [psi, max_eq_right (by linarith), min_eq_left (by linarith)]

lemma psi_eq_zero {x : EuclideanSpace ℝ (Fin 4)} (hx : 1 ≤ ‖x‖) : psi x = 0 := by
  rw [psi, max_eq_left (by linarith), min_eq_right (by norm_num)]

lemma continuous_psi : Continuous psi := by
  unfold psi
  fun_prop

end

end Work.Agree

namespace Work.Agree

open Work.TangentClasses

noncomputable section

/-! ## Continuity of the reflection family -/

lemma continuous_pairingCLM : Continuous (fun u : H5 => pairingCLM u) := by
  have h1 : Continuous (fun p : H5 =>
      (innerSL ℝ p.1).comp (ContinuousLinearMap.fst ℝ (Quaternion ℝ) ℝ)) :=
    Continuous.clm_comp ((innerSL ℝ).continuous.comp continuous_fst)
      (continuous_const : Continuous (fun _ : H5 => ContinuousLinearMap.fst ℝ (Quaternion ℝ) ℝ))
  have h2 : Continuous (fun p : H5 =>
      p.2 • (ContinuousLinearMap.snd ℝ (Quaternion ℝ) ℝ)) :=
    continuous_snd.smul
      (continuous_const : Continuous (fun _ : H5 => ContinuousLinearMap.snd ℝ (Quaternion ℝ) ℝ))
  rw [show (fun u : H5 => pairingCLM u) = fun p : H5 =>
      (innerSL ℝ p.1).comp (ContinuousLinearMap.fst ℝ (Quaternion ℝ) ℝ)
        + p.2 • (ContinuousLinearMap.snd ℝ (Quaternion ℝ) ℝ) from rfl]
  exact h1.add h2

lemma continuous_reflU : Continuous (fun u : H5 => reflU u) := by
  have h3 : Continuous (fun u : H5 =>
      ContinuousLinearMap.smulRightL ℝ H5 H5 (pairingCLM u)) :=
    (ContinuousLinearMap.smulRightL ℝ H5 H5).continuous.comp continuous_pairingCLM
  have h4 : Continuous (fun u : H5 =>
      ContinuousLinearMap.smulRight (pairingCLM u) u) := h3.clm_apply continuous_id
  have h5 : Continuous (fun u : H5 =>
      (2:ℝ) • ContinuousLinearMap.smulRight (pairingCLM u) u) :=
    Continuous.const_smul h4 (2:ℝ)
  have h6 : Continuous (fun u : H5 =>
      (ContinuousLinearMap.id ℝ H5)
        - (2:ℝ) • ContinuousLinearMap.smulRight (pairingCLM u) u) :=
    (continuous_const : Continuous (fun _ : H5 => (ContinuousLinearMap.id ℝ H5))).sub h5
  simpa only [reflU] using h6

/-! ## Continuity of the null-homotopy in `(s,q)` -/

/-- `M_s(q)` as a function of the pair `(s,q)`. -/
def MsCLMFun (p : ℝ × Quaternion ℝ) : H5 →L[ℝ] H5 := MsCLM p.1 p.2

/-- `M_s(q)^{-1}` as a function of the pair `(s,q)`. -/
def MsInvCLMFun (p : ℝ × Quaternion ℝ) : H5 →L[ℝ] H5 := MsInvCLM p.1 p.2

lemma continuous_cS : Continuous cS := by unfold cS; fun_prop
lemma continuous_dS : Continuous dS := by unfold dS; fun_prop

lemma continuous_MsCLMFun : Continuous MsCLMFun := by
  have h1 : Continuous (fun p : ℝ × Quaternion ℝ => mk (cS p.1 • p.2) (dS p.1)) := by
    rw [show (fun p : ℝ × Quaternion ℝ => mk (cS p.1 • p.2) (dS p.1))
        = fun p => ((cS p.1) • p.2, dS p.1) from rfl]
    exact ((continuous_cS.comp continuous_fst).smul continuous_snd).prodMk
      (continuous_dS.comp continuous_fst)
  have h2 : Continuous (fun p : ℝ × Quaternion ℝ =>
      mk (cS p.1 • (1:Quaternion ℝ)) (dS p.1)) := by
    rw [show (fun p : ℝ × Quaternion ℝ => mk (cS p.1 • (1:Quaternion ℝ)) (dS p.1))
        = fun p => ((cS p.1) • (1:Quaternion ℝ), dS p.1) from rfl]
    exact ((continuous_cS.comp continuous_fst).smul continuous_const).prodMk
      (continuous_dS.comp continuous_fst)
  convert (continuous_reflU.comp h1).clm_comp (continuous_reflU.comp h2) using 1
  funext p
  rfl

lemma continuous_MsInvCLMFun : Continuous MsInvCLMFun := by
  have h1 : Continuous (fun p : ℝ × Quaternion ℝ => mk (cS p.1 • p.2) (dS p.1)) := by
    rw [show (fun p : ℝ × Quaternion ℝ => mk (cS p.1 • p.2) (dS p.1))
        = fun p => ((cS p.1) • p.2, dS p.1) from rfl]
    exact ((continuous_cS.comp continuous_fst).smul continuous_snd).prodMk
      (continuous_dS.comp continuous_fst)
  have h2 : Continuous (fun p : ℝ × Quaternion ℝ =>
      mk (cS p.1 • (1:Quaternion ℝ)) (dS p.1)) := by
    rw [show (fun p : ℝ × Quaternion ℝ => mk (cS p.1 • (1:Quaternion ℝ)) (dS p.1))
        = fun p => ((cS p.1) • (1:Quaternion ℝ), dS p.1) from rfl]
    exact ((continuous_cS.comp continuous_fst).smul continuous_const).prodMk
      (continuous_dS.comp continuous_fst)
  convert (continuous_reflU.comp h2).clm_comp (continuous_reflU.comp h1) using 1
  funext p
  rfl

/-- `M_0(q) ∘ X = id` for the transition `X`, in operator form. -/
lemma QzCLM_one_one_comp_MsInvCLM_zero (q : Quaternion ℝ) (hq : inner ℝ q q = 1) :
    (QzCLM 1 1 q).comp (MsInvCLM 0 q) = ContinuousLinearMap.id ℝ H5 := by
  rw [show QzCLM 1 1 q = QopCLM q from congrFun QzCLM_one_one q, ← MsCLM_zero q hq]
  exact MsCLM_comp_MsInvCLM 0 q hq

lemma MsInvCLM_zero_comp_QzCLM_one_one (q : Quaternion ℝ) (hq : inner ℝ q q = 1) :
    (MsInvCLM 0 q).comp (QzCLM 1 1 q) = ContinuousLinearMap.id ℝ H5 := by
  rw [show QzCLM 1 1 q = QopCLM q from congrFun QzCLM_one_one q, ← MsCLM_zero q hq]
  exact MsInvCLM_comp_MsCLM 0 q hq

lemma inner_uDir (b : S4) : inner ℝ (uDir b) (uDir b) = 1 := by
  have h : ‖uDir b‖ = 1 := by
    have h2 := (Submission.Milnor.unitDir (coord0 b)).2
    rw [Metric.mem_sphere, dist_zero_right] at h2
    exact h2
  rw [real_inner_self_eq_norm_mul_norm, h]
  norm_num

end

end Work.Agree

namespace Work.Agree

open Work.TangentClasses

noncomputable section

/-! ## The inverse relations among the `QzCLM` -/

lemma QzCLM_one_one_comp_neg (q : Quaternion ℝ) (hq : q ≠ 0) :
    (QzCLM 1 1 q).comp (QzCLM (-1) (-1) q) = ContinuousLinearMap.id ℝ H5 := by
  apply ContinuousLinearMap.ext
  intro p
  obtain ⟨v, t⟩ := p
  rw [ContinuousLinearMap.comp_apply, QzCLM_apply, QzCLM_apply, ContinuousLinearMap.id_apply]
  simp only [zpow_one, zpow_neg_one]
  have hmain : q * (q⁻¹ * v * q⁻¹) * q = v := by
    rw [mul_assoc q (q⁻¹ * v * q⁻¹) q, mul_assoc (q⁻¹ * v) q⁻¹ q,
      inv_mul_cancel₀ hq, mul_one, ← mul_assoc q q⁻¹ v, mul_inv_cancel₀ hq, one_mul]
  rw [hmain]

lemma QzCLM_neg_comp_one_one (q : Quaternion ℝ) (hq : q ≠ 0) :
    (QzCLM (-1) (-1) q).comp (QzCLM 1 1 q) = ContinuousLinearMap.id ℝ H5 := by
  apply ContinuousLinearMap.ext
  intro p
  obtain ⟨v, t⟩ := p
  rw [ContinuousLinearMap.comp_apply, QzCLM_apply, QzCLM_apply, ContinuousLinearMap.id_apply]
  simp only [zpow_one, zpow_neg_one]
  have hmain : q⁻¹ * (q * v * q) * q⁻¹ = v := by
    rw [mul_assoc q⁻¹ (q * v * q) q⁻¹, mul_assoc (q * v) q q⁻¹,
      mul_inv_cancel₀ hq, mul_one, ← mul_assoc q⁻¹ q v, inv_mul_cancel₀ hq, one_mul]
  rw [hmain]

end

end Work.Agree

namespace Work.Agree

open Work.TangentClasses
open Classical

noncomputable section

lemma MsInvCLM_one (q : Quaternion ℝ) :
    MsInvCLM 1 q = ContinuousLinearMap.id ℝ H5 := by
  have h : mk (cS 1 • q) (dS 1) = mk (cS 1 • (1:Quaternion ℝ)) (dS 1) := by simp
  rw [MsInvCLM, h]
  exact reflU_comp_self _ (by rw [pairing_mk_mk]; simp)

/-! ## The bundle-level data -/

variable (ι₀ : Type) [Inhabited ι₀]

/-- The bundle `L¹R¹ ⊕ ε¹` over `S⁴`. -/
abbrev Zb : RealBundle S4 (EuclideanSpace ℝ (Fin 4) × EuclideanSpace ℝ (Fin 1)) (Bool × ι₀) :=
  RealBundle.sum (clutchBundle (1 : ℤ) 1)
    (RealBundle.trivial S4 (EuclideanSpace ℝ (Fin 1)) ι₀)

/-- The parameter `ψ(coord0 b)` of the null-homotopy. -/
def sOf (b : S4) : ℝ := psi (coord0 b)

def HomModel (b : S4) : H5 →L[ℝ] H5 := MsCLMFun (sOf b, uDir b)

def InvModel (b : S4) : H5 →L[ℝ] H5 := MsInvCLMFun (sOf b, uDir b)

def XModel (b : S4) : H5 →L[ℝ] H5 :=
  if b = OnePoint.infty then ContinuousLinearMap.id ℝ H5 else QzCLM (-1) (-1) (uDir b)

def YModel (b : S4) : H5 →L[ℝ] H5 :=
  if b = OnePoint.infty then ContinuousLinearMap.id ℝ H5 else QzCLM 1 1 (uDir b)

def HomTrue (b : S4) : H5 →L[ℝ] H5 := (HomModel b).comp (XModel b)

def InvTrue (b : S4) : H5 →L[ℝ] H5 := (YModel b).comp (InvModel b)

/-- The points where the coordinate of the first chart is nonzero. -/
def W2 : Set S4 := {b | coord0 b ≠ 0}

lemma coord0_eq_zero_iff (b : S4) :
    coord0 b = 0 ↔ b = OnePoint.infty ∨ b = (↑(0 : EuclideanSpace ℝ (Fin 4)) : S4) := by
  constructor
  · intro h
    by_cases hb : b = OnePoint.infty
    · exact Or.inl hb
    · obtain ⟨x, rfl⟩ := Option.ne_none_iff_exists'.mp hb
      exact Or.inr (by rw [← h]; rfl)
  · rintro (rfl | rfl) <;> rfl

lemma isOpen_W2 : IsOpen W2 := by
  have h : ({OnePoint.infty} ∪ {(↑(0 : EuclideanSpace ℝ (Fin 4)) : S4)})ᶜ = W2 := by
    ext b
    simp only [W2, Set.mem_setOf_eq, ne_eq, coord0_eq_zero_iff, Set.mem_compl_iff,
      Set.mem_union, Set.mem_singleton_iff, not_or]
  rw [← h]
  exact (OnePoint.isClosed_infty.union isClosed_singleton).isOpen_compl

lemma W2_sub : W2 ⊆ hemi0 ∩ hemi1 := by
  intro b hb
  rw [W2, Set.mem_setOf_eq] at hb
  rw [Set.mem_inter_iff, hemi0, hemi1, Set.mem_setOf_eq, Set.mem_setOf_eq]
  exact ⟨fun h => hb (by rw [h]; rfl), fun h => hb (by rw [h]; rfl)⟩

lemma W2_ne_infty {b : S4} (hb : b ∈ W2) : b ≠ OnePoint.infty := by
  rw [W2, Set.mem_setOf_eq] at hb
  intro h; exact hb (by rw [h]; rfl)

lemma W2_sub_base (j : ι₀) :
    W2 ⊆ (Zb ι₀).baseSet (true, j) ∩ (Zb ι₀).baseSet (false, default) := by
  intro b hb
  rw [Zb, RealBundle.sum_baseSet, RealBundle.sum_baseSet, clutchBundle_baseSet,
    clutchBundle_baseSet, RealBundle.trivial_baseSet, RealBundle.trivial_baseSet,
    Set.inter_univ, Set.inter_univ]
  exact ⟨(W2_sub hb).2, (W2_sub hb).1⟩

lemma continuousOn_uDir_W2 : ContinuousOn uDir W2 := continuousOn_uDir.mono W2_sub

lemma continuousOn_sOf_W2 : ContinuousOn (fun b : S4 => sOf b) W2 := by
  have : ContinuousOn (fun b : S4 => coord0 b) W2 :=
    continuousOn_coord0.mono (W2_sub.trans Set.inter_subset_left)
  simpa only [sOf, Function.comp_def] using continuous_psi.comp_continuousOn this

lemma continuousOn_HomModel_W2 : ContinuousOn (fun b : S4 => HomModel b) W2 := by
  have hpair : ContinuousOn (fun b : S4 => (sOf b, uDir b)) W2 :=
    continuousOn_sOf_W2.prodMk continuousOn_uDir_W2
  simpa only [HomModel, Function.comp_def] using continuous_MsCLMFun.comp_continuousOn hpair

lemma continuousOn_InvModel_W2 : ContinuousOn (fun b : S4 => InvModel b) W2 := by
  have hpair : ContinuousOn (fun b : S4 => (sOf b, uDir b)) W2 :=
    continuousOn_sOf_W2.prodMk continuousOn_uDir_W2
  simpa only [InvModel, Function.comp_def] using
    continuous_MsInvCLMFun.comp_continuousOn hpair

lemma Zb_coordChange_true_false (j : ι₀) (b : S4) :
    (Zb ι₀).coordChange (true, j) (false, default) b
      = (qTwist (-1) (-1) (uDir b)).prodMap
          (ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin 1))) := by
  rw [Zb, RealBundle.sum_coordChange, clutchBundle_coordChange_true_false,
    RealBundle.trivial_coordChange]

lemma Zb_coordChange_false_true (j : ι₀) (b : S4) :
    (Zb ι₀).coordChange (false, j) (true, default) b
      = (qTwist (1) (1) (uDir b)).prodMap
          (ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin 1))) := by
  rw [Zb, RealBundle.sum_coordChange, clutchBundle_coordChange_false_true,
    RealBundle.trivial_coordChange]

lemma continuousOn_conj_true_false (j : ι₀) :
    ContinuousOn (fun b : S4 => (e45 : _ →L[ℝ] H5).comp
      (((Zb ι₀).coordChange (true, j) (false, default) b).comp (e45.symm : H5 →L[ℝ] _))) W2 := by
  have h1 : ContinuousOn (fun _ : S4 =>
      (e45 : (EuclideanSpace ℝ (Fin 4) × EuclideanSpace ℝ (Fin 1)) →L[ℝ] H5)) W2 := by
    simpa using (continuous_const : Continuous (fun _ : S4 =>
      (e45 : (EuclideanSpace ℝ (Fin 4) × EuclideanSpace ℝ (Fin 1)) →L[ℝ] H5))).continuousOn
  have h2 : ContinuousOn (fun b : S4 => (Zb ι₀).coordChange (true, j) (false, default) b) W2 :=
    ((Zb ι₀).continuousOn_coordChange (true, j) (false, default)).mono (W2_sub_base ι₀ j)
  have h3 : ContinuousOn (fun _ : S4 => (e45.symm : H5 →L[ℝ] (EuclideanSpace ℝ (Fin 4) × EuclideanSpace ℝ (Fin 1)))) W2 := by
    simpa using (continuous_const : Continuous (fun _ : S4 =>
      (e45.symm : H5 →L[ℝ] (EuclideanSpace ℝ (Fin 4) × EuclideanSpace ℝ (Fin 1))))).continuousOn
  simpa only [ContinuousLinearMap.comp_assoc] using (h1.clm_comp h2).clm_comp h3

lemma continuousOn_conj_false_true (j : ι₀) :
    ContinuousOn (fun b : S4 => (e45 : _ →L[ℝ] H5).comp
      (((Zb ι₀).coordChange (false, j) (true, default) b).comp (e45.symm : H5 →L[ℝ] _))) W2 := by
  have h1 : ContinuousOn (fun _ : S4 =>
      (e45 : (EuclideanSpace ℝ (Fin 4) × EuclideanSpace ℝ (Fin 1)) →L[ℝ] H5)) W2 := by
    simpa using (continuous_const : Continuous (fun _ : S4 =>
      (e45 : (EuclideanSpace ℝ (Fin 4) × EuclideanSpace ℝ (Fin 1)) →L[ℝ] H5))).continuousOn
  have h2 : ContinuousOn (fun b : S4 => (Zb ι₀).coordChange (false, j) (true, default) b) W2 :=
    ((Zb ι₀).continuousOn_coordChange (false, j) (true, default)).mono
      (by
        intro b hb
        rw [Zb, RealBundle.sum_baseSet, RealBundle.sum_baseSet, clutchBundle_baseSet,
          clutchBundle_baseSet, RealBundle.trivial_baseSet, RealBundle.trivial_baseSet,
          Set.inter_univ, Set.inter_univ]
        exact ⟨(W2_sub hb).1, (W2_sub hb).2⟩)
  have h3 : ContinuousOn (fun _ : S4 => (e45.symm : H5 →L[ℝ] (EuclideanSpace ℝ (Fin 4) × EuclideanSpace ℝ (Fin 1)))) W2 := by
    simpa using (continuous_const : Continuous (fun _ : S4 =>
      (e45.symm : H5 →L[ℝ] (EuclideanSpace ℝ (Fin 4) × EuclideanSpace ℝ (Fin 1))))).continuousOn
  simpa only [ContinuousLinearMap.comp_assoc] using (h1.clm_comp h2).clm_comp h3

lemma e45_conj_true_false (j : ι₀) (b : S4) :
    (e45 : _ →L[ℝ] H5).comp
        (((Zb ι₀).coordChange (true, j) (false, default) b).comp (e45.symm : H5 →L[ℝ] _))
      = QzCLM (-1) (-1) (uDir b) := by
  rw [Zb_coordChange_true_false, e45_qTwist]

lemma e45_conj_false_true (j : ι₀) (b : S4) :
    (e45 : _ →L[ℝ] H5).comp
        (((Zb ι₀).coordChange (false, j) (true, default) b).comp (e45.symm : H5 →L[ℝ] _))
      = QzCLM 1 1 (uDir b) := by
  rw [Zb_coordChange_false_true, e45_qTwist]

lemma continuousOn_XModel_W2 (j : ι₀) : ContinuousOn (fun b : S4 => XModel b) W2 := by
  refine (continuousOn_conj_true_false ι₀ j).congr (fun b hb => ?_)
  show XModel b = (e45 : (EuclideanSpace ℝ (Fin 4) × EuclideanSpace ℝ (Fin 1)) →L[ℝ] H5).comp
      (((Zb ι₀).coordChange (true, j) (false, default) b).comp (e45.symm : H5 →L[ℝ] _))
  rw [e45_conj_true_false, XModel, if_neg (W2_ne_infty hb)]

lemma continuousOn_YModel_W2 (j : ι₀) : ContinuousOn (fun b : S4 => YModel b) W2 := by
  refine (continuousOn_conj_false_true ι₀ j).congr (fun b hb => ?_)
  show YModel b = (e45 : (EuclideanSpace ℝ (Fin 4) × EuclideanSpace ℝ (Fin 1)) →L[ℝ] H5).comp
      (((Zb ι₀).coordChange (false, j) (true, default) b).comp (e45.symm : H5 →L[ℝ] _))
  rw [e45_conj_false_true, YModel, if_neg (W2_ne_infty hb)]

lemma continuousOn_HomTrue_W2 (j : ι₀) : ContinuousOn (fun b : S4 => HomTrue b) W2 := by
  have h := continuousOn_HomModel_W2.clm_comp (continuousOn_XModel_W2 ι₀ j)
  simpa only [HomTrue, Function.comp_def] using h

lemma continuousOn_InvTrue_W2 (j : ι₀) : ContinuousOn (fun b : S4 => InvTrue b) W2 := by
  have h := (continuousOn_YModel_W2 ι₀ j).clm_comp continuousOn_InvModel_W2
  simpa only [InvTrue, Function.comp_def] using h

end

end Work.Agree

namespace Work.Agree

open Work.TangentClasses
open Classical

noncomputable section

variable (ι₀ : Type) [Inhabited ι₀]

/-! ## Neighbourhoods of `0` and `∞` -/

def U0 : Set S4 := (↑) '' {x : EuclideanSpace ℝ (Fin 4) | ‖x‖ < 1/2}

lemma isOpen_U0 : IsOpen U0 := by
  have hset : Metric.ball (0 : EuclideanSpace ℝ (Fin 4)) (1/2) = {x | ‖x‖ < 1/2} := by
    ext x; simp [Metric.mem_ball, dist_zero_right]
  rw [U0, ← hset]
  exact OnePoint.isOpen_image_coe.mpr Metric.isOpen_ball

lemma zero_mem_U0 : (↑(0 : EuclideanSpace ℝ (Fin 4)) : S4) ∈ U0 := by
  refine ⟨0, ?_, rfl⟩
  simp

def Uinf : Set S4 := {OnePoint.infty} ∪ (↑) '' {x : EuclideanSpace ℝ (Fin 4) | 1 < ‖x‖}

lemma isOpen_Uinf : IsOpen Uinf := by
  have hpre : ((↑) : EuclideanSpace ℝ (Fin 4) → S4) ⁻¹' Uinf
      = {x : EuclideanSpace ℝ (Fin 4) | 1 < ‖x‖} := by
    ext x
    simp only [Set.mem_preimage, Uinf, Set.mem_union, Set.mem_singleton_iff, OnePoint.coe_ne_infty,
      false_or, Set.mem_image, Set.mem_setOf_eq]
    constructor
    · rintro ⟨y, hy, hyx⟩
      rwa [OnePoint.coe_injective hyx] at hy
    · exact fun h => ⟨x, h, rfl⟩
  rw [OnePoint.isOpen_iff_of_mem' (by simp [Uinf]), hpre]
  constructor
  · have hc : ({x : EuclideanSpace ℝ (Fin 4) | 1 < ‖x‖})ᶜ
        = Metric.closedBall (0 : EuclideanSpace ℝ (Fin 4)) 1 := by
      ext x
      simp only [Set.mem_compl_iff, Set.mem_setOf_eq, not_lt, Metric.mem_closedBall,
        dist_zero_right]
    rw [hc]
    exact isCompact_closedBall 0 1
  · exact isOpen_lt continuous_const continuous_norm

lemma infty_mem_Uinf : (OnePoint.infty : S4) ∈ Uinf := Or.inl rfl

/-! ## Values of the models at the two special points -/

lemma coord0_infty : coord0 (OnePoint.infty : S4) = 0 := rfl

lemma sOf_infty : sOf (OnePoint.infty : S4) = 1 := by
  rw [sOf, coord0_infty]
  exact psi_eq_one (by norm_num)

lemma sOf_coe (x : EuclideanSpace ℝ (Fin 4)) : sOf (↑x : S4) = psi x := rfl

@[simp] lemma HomModel_infty : HomModel (OnePoint.infty : S4) = ContinuousLinearMap.id ℝ H5 := by
  rw [HomModel, sOf_infty, MsCLMFun, MsCLM_one]

@[simp] lemma InvModel_infty : InvModel (OnePoint.infty : S4) = ContinuousLinearMap.id ℝ H5 := by
  rw [InvModel, sOf_infty, MsInvCLMFun, MsInvCLM_one]

@[simp] lemma XModel_infty : XModel (OnePoint.infty : S4) = ContinuousLinearMap.id ℝ H5 := by
  rw [XModel, if_pos rfl]

@[simp] lemma YModel_infty : YModel (OnePoint.infty : S4) = ContinuousLinearMap.id ℝ H5 := by
  rw [YModel, if_pos rfl]

lemma XModel_coe (x : EuclideanSpace ℝ (Fin 4)) :
    XModel (↑x : S4) = QzCLM (-1) (-1) (uDir (↑x : S4)) := by
  rw [XModel, if_neg (OnePoint.coe_ne_infty x)]

lemma YModel_coe (x : EuclideanSpace ℝ (Fin 4)) :
    YModel (↑x : S4) = QzCLM 1 1 (uDir (↑x : S4)) := by
  rw [YModel, if_neg (OnePoint.coe_ne_infty x)]

lemma HomModel_coe_big (x : EuclideanSpace ℝ (Fin 4)) (hx : 1 < ‖x‖) :
    HomModel (↑x : S4) = QzCLM 1 1 (uDir (↑x : S4)) := by
  rw [HomModel, sOf_coe, psi_eq_zero (le_of_lt hx), MsCLMFun,
    MsCLM_zero (uDir (↑x : S4)) (inner_uDir (↑x : S4))]
  exact (congrFun QzCLM_one_one (uDir (↑x : S4))).symm

lemma InvModel_coe_big (x : EuclideanSpace ℝ (Fin 4)) (hx : 1 < ‖x‖) :
    InvModel (↑x : S4) = MsInvCLM 0 (uDir (↑x : S4)) := by
  rw [InvModel, sOf_coe, psi_eq_zero (le_of_lt hx), MsInvCLMFun]

/-! ## Eventual constancy -/

lemma eventually_HomModel_at_zero :
    HomModel =ᶠ[𝓝[hemi0] ((↑(0 : EuclideanSpace ℝ (Fin 4))) : S4)]
      (fun _ => ContinuousLinearMap.id ℝ H5) := by
  have hU0 : U0 ∈ 𝓝 ((↑(0 : EuclideanSpace ℝ (Fin 4))) : S4) :=
    isOpen_U0.mem_nhds zero_mem_U0
  have hev : HomModel =ᶠ[𝓝 ((↑(0 : EuclideanSpace ℝ (Fin 4))) : S4)]
      (fun _ => ContinuousLinearMap.id ℝ H5) :=
    Filter.mem_of_superset hU0 (fun y hy => by
      obtain ⟨x, hx, rfl⟩ := hy
      show HomModel (↑x : S4) = ContinuousLinearMap.id ℝ H5
      rw [HomModel, sOf_coe, psi_eq_one (le_of_lt hx), MsCLMFun, MsCLM_one])
  exact Filter.Eventually.filter_mono
    (nhdsWithin_le_nhds : 𝓝[hemi0] ((↑(0 : EuclideanSpace ℝ (Fin 4))) : S4)
      ≤ 𝓝 ((↑(0 : EuclideanSpace ℝ (Fin 4))) : S4)) hev

lemma eventually_InvModel_at_zero :
    InvModel =ᶠ[𝓝[hemi0] ((↑(0 : EuclideanSpace ℝ (Fin 4))) : S4)]
      (fun _ => ContinuousLinearMap.id ℝ H5) := by
  have hU0 : U0 ∈ 𝓝 ((↑(0 : EuclideanSpace ℝ (Fin 4))) : S4) :=
    isOpen_U0.mem_nhds zero_mem_U0
  have hev : InvModel =ᶠ[𝓝 ((↑(0 : EuclideanSpace ℝ (Fin 4))) : S4)]
      (fun _ => ContinuousLinearMap.id ℝ H5) :=
    Filter.mem_of_superset hU0 (fun y hy => by
      obtain ⟨x, hx, rfl⟩ := hy
      show InvModel (↑x : S4) = ContinuousLinearMap.id ℝ H5
      rw [InvModel, sOf_coe, psi_eq_one (le_of_lt hx), MsInvCLMFun, MsInvCLM_one])
  exact Filter.Eventually.filter_mono
    (nhdsWithin_le_nhds : 𝓝[hemi0] ((↑(0 : EuclideanSpace ℝ (Fin 4))) : S4)
      ≤ 𝓝 ((↑(0 : EuclideanSpace ℝ (Fin 4))) : S4)) hev

lemma eventually_HomTrue_at_infty :
    HomTrue =ᶠ[𝓝[hemi1] (OnePoint.infty : S4)]
      (fun _ => ContinuousLinearMap.id ℝ H5) := by
  have hU : Uinf ∈ 𝓝 (OnePoint.infty : S4) := isOpen_Uinf.mem_nhds infty_mem_Uinf
  have hev : HomTrue =ᶠ[𝓝 (OnePoint.infty : S4)]
      (fun _ => ContinuousLinearMap.id ℝ H5) :=
    Filter.mem_of_superset hU (fun y hy => by
      rcases hy with rfl | ⟨x, hx, rfl⟩
      · show (HomModel OnePoint.infty).comp (XModel OnePoint.infty) = _
        rw [HomModel_infty, XModel_infty, ContinuousLinearMap.id_comp]
      · show (HomModel (↑x)).comp (XModel (↑x)) = _
        rw [HomModel_coe_big x hx, XModel_coe x]
        exact QzCLM_one_one_comp_neg (uDir (↑x : S4)) (uDir_ne_zero (↑x : S4)))
  exact Filter.Eventually.filter_mono
    (nhdsWithin_le_nhds : 𝓝[hemi1] (OnePoint.infty : S4) ≤ 𝓝 (OnePoint.infty : S4)) hev

lemma eventually_InvTrue_at_infty :
    InvTrue =ᶠ[𝓝[hemi1] (OnePoint.infty : S4)]
      (fun _ => ContinuousLinearMap.id ℝ H5) := by
  have hU : Uinf ∈ 𝓝 (OnePoint.infty : S4) := isOpen_Uinf.mem_nhds infty_mem_Uinf
  have hev : InvTrue =ᶠ[𝓝 (OnePoint.infty : S4)]
      (fun _ => ContinuousLinearMap.id ℝ H5) :=
    Filter.mem_of_superset hU (fun y hy => by
      rcases hy with rfl | ⟨x, hx, rfl⟩
      · show (YModel OnePoint.infty).comp (InvModel OnePoint.infty) = _
        rw [YModel_infty, InvModel_infty, ContinuousLinearMap.id_comp]
      · show (YModel (↑x)).comp (InvModel (↑x)) = _
        rw [YModel_coe x, InvModel_coe_big x hx]
        exact QzCLM_one_one_comp_MsInvCLM_zero (uDir (↑x : S4)) (inner_uDir (↑x : S4)))
  exact Filter.Eventually.filter_mono
    (nhdsWithin_le_nhds : 𝓝[hemi1] (OnePoint.infty : S4) ≤ 𝓝 (OnePoint.infty : S4)) hev

/-! ## Continuity -/

lemma continuousWithinAt_HomModel_zero :
    ContinuousWithinAt HomModel hemi0 ((↑(0 : EuclideanSpace ℝ (Fin 4))) : S4) := by
  refine ContinuousWithinAt.congr_of_eventuallyEq ?_ eventually_HomModel_at_zero ?_
  · exact (continuous_const : Continuous (fun _ : S4 => ContinuousLinearMap.id ℝ H5)
      ).continuousAt.continuousWithinAt
  · rw [HomModel, sOf_coe, psi_eq_one (by norm_num), MsCLMFun, MsCLM_one]

lemma continuousWithinAt_InvModel_zero :
    ContinuousWithinAt InvModel hemi0 ((↑(0 : EuclideanSpace ℝ (Fin 4))) : S4) := by
  refine ContinuousWithinAt.congr_of_eventuallyEq ?_ eventually_InvModel_at_zero ?_
  · exact (continuous_const : Continuous (fun _ : S4 => ContinuousLinearMap.id ℝ H5)
      ).continuousAt.continuousWithinAt
  · rw [InvModel, sOf_coe, psi_eq_one (by norm_num), MsInvCLMFun, MsInvCLM_one]

lemma continuousWithinAt_HomTrue_infty :
    ContinuousWithinAt HomTrue hemi1 (OnePoint.infty : S4) := by
  refine ContinuousWithinAt.congr_of_eventuallyEq ?_ eventually_HomTrue_at_infty ?_
  · exact (continuous_const : Continuous (fun _ : S4 => ContinuousLinearMap.id ℝ H5)
      ).continuousAt.continuousWithinAt
  · show (HomModel OnePoint.infty).comp (XModel OnePoint.infty) = _
    rw [HomModel_infty, XModel_infty, ContinuousLinearMap.id_comp]

lemma continuousWithinAt_InvTrue_infty :
    ContinuousWithinAt InvTrue hemi1 (OnePoint.infty : S4) := by
  refine ContinuousWithinAt.congr_of_eventuallyEq ?_ eventually_InvTrue_at_infty ?_
  · exact (continuous_const : Continuous (fun _ : S4 => ContinuousLinearMap.id ℝ H5)
      ).continuousAt.continuousWithinAt
  · show (YModel OnePoint.infty).comp (InvModel OnePoint.infty) = _
    rw [YModel_infty, InvModel_infty, ContinuousLinearMap.id_comp]

lemma continuousOn_HomModel_hemi0 : ContinuousOn (fun b : S4 => HomModel b) hemi0 := by
  intro x hx
  by_cases hx0 : coord0 x = 0
  · have hx' : x = (↑(0 : EuclideanSpace ℝ (Fin 4)) : S4) := by
      rcases (coord0_eq_zero_iff x).mp hx0 with h | h
      · exact absurd h hx
      · exact h
    rw [hx']
    exact continuousWithinAt_HomModel_zero
  · have hxW : x ∈ W2 := hx0
    exact ((continuousOn_HomModel_W2.continuousWithinAt hxW).continuousAt
      (isOpen_W2.mem_nhds hxW)).continuousWithinAt

lemma continuousOn_InvModel_hemi0 : ContinuousOn (fun b : S4 => InvModel b) hemi0 := by
  intro x hx
  by_cases hx0 : coord0 x = 0
  · have hx' : x = (↑(0 : EuclideanSpace ℝ (Fin 4)) : S4) := by
      rcases (coord0_eq_zero_iff x).mp hx0 with h | h
      · exact absurd h hx
      · exact h
    rw [hx']
    exact continuousWithinAt_InvModel_zero
  · have hxW : x ∈ W2 := hx0
    exact ((continuousOn_InvModel_W2.continuousWithinAt hxW).continuousAt
      (isOpen_W2.mem_nhds hxW)).continuousWithinAt

lemma continuousOn_HomTrue_hemi1 (j : ι₀) : ContinuousOn (fun b : S4 => HomTrue b) hemi1 := by
  intro x hx
  by_cases hxi : x = OnePoint.infty
  · rw [hxi]
    exact continuousWithinAt_HomTrue_infty
  · have hxW : x ∈ W2 := by
      rw [W2, Set.mem_setOf_eq]
      intro h0
      rcases (coord0_eq_zero_iff x).mp h0 with h | h
      · exact hxi h
      · exact hx h
    exact ((continuousOn_HomTrue_W2 ι₀ j).continuousWithinAt hxW).continuousAt
      (isOpen_W2.mem_nhds hxW) |>.continuousWithinAt

lemma continuousOn_InvTrue_hemi1 (j : ι₀) : ContinuousOn (fun b : S4 => InvTrue b) hemi1 := by
  intro x hx
  by_cases hxi : x = OnePoint.infty
  · rw [hxi]
    exact continuousWithinAt_InvTrue_infty
  · have hxW : x ∈ W2 := by
      rw [W2, Set.mem_setOf_eq]
      intro h0
      rcases (coord0_eq_zero_iff x).mp h0 with h | h
      · exact hxi h
      · exact hx h
    exact ((continuousOn_InvTrue_W2 ι₀ j).continuousWithinAt hxW).continuousAt
      (isOpen_W2.mem_nhds hxW) |>.continuousWithinAt

end

end Work.Agree

namespace Work.Agree

open Work.TangentClasses
open Classical

noncomputable section

variable (ι₀ : Type) [Inhabited ι₀]

/-- The candidate isomorphism `L¹R¹ ⊕ ε¹ → ε⁵`, first chart. -/
def HomCLM (b : S4) :
    (EuclideanSpace ℝ (Fin 4) × EuclideanSpace ℝ (Fin 1)) →L[ℝ] EuclideanSpace ℝ (Fin 5) :=
  (e5.symm : H5 →L[ℝ] EuclideanSpace ℝ (Fin 5)).comp
    ((HomModel b).comp
      (e45 : (EuclideanSpace ℝ (Fin 4) × EuclideanSpace ℝ (Fin 1)) →L[ℝ] H5))

/-- Its inverse. -/
def InvCLM (b : S4) :
    EuclideanSpace ℝ (Fin 5) →L[ℝ] (EuclideanSpace ℝ (Fin 4) × EuclideanSpace ℝ (Fin 1)) :=
  (e45.symm : H5 →L[ℝ] (EuclideanSpace ℝ (Fin 4) × EuclideanSpace ℝ (Fin 1))).comp
    ((InvModel b).comp (e5 : EuclideanSpace ℝ (Fin 5) →L[ℝ] H5))

lemma prodMap_id_id {F G : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G] :
    (ContinuousLinearMap.id ℝ F).prodMap (ContinuousLinearMap.id ℝ G)
      = ContinuousLinearMap.id ℝ (F × G) := by
  apply ContinuousLinearMap.ext
  intro p
  simp [ContinuousLinearMap.coe_prodMap', Prod.map_apply]

lemma e45_qTwist' (a b : ℤ) (q : Quaternion ℝ) :
    (e45 : _ →L[ℝ] H5).comp ((qTwist a b q).prodMap
        (ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin 1))))
      = (QzCLM a b q).comp (e45 : _ →L[ℝ] H5) := by
  rw [← e45_qTwist]
  apply ContinuousLinearMap.ext
  intro v
  simp only [ContinuousLinearMap.comp_apply]
  exact (congrArg (fun w => e45 (((qTwist a b q).prodMap
    (ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin 1)))) w))
    (ContinuousLinearEquiv.symm_apply_apply e45 v)).symm

lemma e45_qTwist'' (a b : ℤ) (q : Quaternion ℝ) :
    ((qTwist a b q).prodMap (ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin 1)))).comp
        (e45.symm : H5 →L[ℝ] (EuclideanSpace ℝ (Fin 4) × EuclideanSpace ℝ (Fin 1)))
      = (e45.symm : H5 →L[ℝ] (EuclideanSpace ℝ (Fin 4) × EuclideanSpace ℝ (Fin 1))).comp
          (QzCLM a b q) := by
  rw [← e45_qTwist, ← ContinuousLinearMap.comp_assoc]
  have hcomp : (e45.symm : H5 →L[ℝ] (EuclideanSpace ℝ (Fin 4) × EuclideanSpace ℝ (Fin 1))).comp
      (e45 : _ →L[ℝ] H5)
        = ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin 4) × EuclideanSpace ℝ (Fin 1)) := by
    apply ContinuousLinearMap.ext
    intro v
    rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply]
    simpa using ContinuousLinearEquiv.symm_apply_apply e45 v
  rw [hcomp, ContinuousLinearMap.id_comp]

lemma Zb_coordChange (i j : Bool) (a c : ι₀) (b : S4) :
    (Zb ι₀).coordChange (i, a) (j, c) b = (ct (1:ℤ) 1 i j b).prodMap
      (ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin 1))) := by
  rw [Zb, RealBundle.sum_coordChange, clutchBundle_coordChange, RealBundle.trivial_coordChange]

lemma Zb_coordChange_ff (a c : ι₀) (b : S4) :
    (Zb ι₀).coordChange (false, a) (false, c) b = ContinuousLinearMap.id ℝ _ := by
  rw [Zb_coordChange, show ct (1:ℤ) 1 false false b = 1 from rfl]
  exact prodMap_id_id

lemma Zb_coordChange_tt (a c : ι₀) (b : S4) :
    (Zb ι₀).coordChange (true, a) (true, c) b = ContinuousLinearMap.id ℝ _ := by
  rw [Zb_coordChange, show ct (1:ℤ) 1 true true b = 1 from rfl]
  exact prodMap_id_id

lemma Zb_coordChange_tf (a : ι₀) (b : S4) :
    (Zb ι₀).coordChange (true, a) (false, default) b
      = (qTwist (-1) (-1) (uDir b)).prodMap
          (ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin 1))) := by
  rw [Zb_coordChange, show ct (1:ℤ) 1 true false b = qTwist (-1) (-1) (uDir b) from rfl]

lemma Zb_coordChange_ft (a : ι₀) (b : S4) :
    (Zb ι₀).coordChange (false, default) (true, a) b
      = (qTwist (1) (1) (uDir b)).prodMap
          (ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin 1))) := by
  rw [Zb_coordChange, show ct (1:ℤ) 1 false true b = qTwist (1) (1) (uDir b) from rfl]

lemma Zb_indexAt_of_ne (b : S4) (hb : b ≠ OnePoint.infty) :
    (Zb ι₀).indexAt b = (false, default) := by
  rw [Zb, RealBundle.sum_indexAt, clutchBundle, RealBundle.trivial_indexAt]
  simp [hb]

lemma Zb_indexAt_infty : (Zb ι₀).indexAt (OnePoint.infty : S4) = (true, default) := by
  rw [Zb, RealBundle.sum_indexAt, clutchBundle, RealBundle.trivial_indexAt]
  simp

lemma Zb_baseSet_false (j : ι₀) : (Zb ι₀).baseSet (false, j) = hemi0 := by
  rw [Zb, RealBundle.sum_baseSet, clutchBundle_baseSet, RealBundle.trivial_baseSet,
    Set.inter_univ]
  rfl

lemma Zb_baseSet_true (j : ι₀) : (Zb ι₀).baseSet (true, j) = hemi1 := by
  rw [Zb, RealBundle.sum_baseSet, clutchBundle_baseSet, RealBundle.trivial_baseSet,
    Set.inter_univ]
  rfl

lemma continuousOn_HomCLM_baseSet (j : ι₀) :
    ContinuousOn (fun b : S4 => HomCLM b) ((Zb ι₀).baseSet (false, j)) := by
  rw [Zb_baseSet_false]
  have h1 : ContinuousOn (fun _ : S4 =>
      (e5.symm : H5 →L[ℝ] EuclideanSpace ℝ (Fin 5))) hemi0 := by
    simpa using (continuous_const : Continuous (fun _ : S4 =>
      (e5.symm : H5 →L[ℝ] EuclideanSpace ℝ (Fin 5)))).continuousOn
  have h2 : ContinuousOn (fun b : S4 => HomModel b) hemi0 := continuousOn_HomModel_hemi0
  have h3 : ContinuousOn (fun _ : S4 =>
      (e45 : (EuclideanSpace ℝ (Fin 4) × EuclideanSpace ℝ (Fin 1)) →L[ℝ] H5)) hemi0 := by
    simpa using (continuous_const : Continuous (fun _ : S4 =>
      (e45 : (EuclideanSpace ℝ (Fin 4) × EuclideanSpace ℝ (Fin 1)) →L[ℝ] H5))).continuousOn
  simpa only [HomCLM, ContinuousLinearMap.comp_assoc] using (h1.clm_comp h2).clm_comp h3

lemma continuousOn_InvCLM_baseSet (j : ι₀) :
    ContinuousOn (fun b : S4 => InvCLM b) ((Zb ι₀).baseSet (false, j)) := by
  rw [Zb_baseSet_false]
  have h1 : ContinuousOn (fun _ : S4 =>
      (e45.symm : H5 →L[ℝ] (EuclideanSpace ℝ (Fin 4) × EuclideanSpace ℝ (Fin 1)))) hemi0 := by
    simpa using (continuous_const : Continuous (fun _ : S4 =>
      (e45.symm : H5 →L[ℝ] (EuclideanSpace ℝ (Fin 4) × EuclideanSpace ℝ (Fin 1))))).continuousOn
  have h2 : ContinuousOn (fun b : S4 => InvModel b) hemi0 := continuousOn_InvModel_hemi0
  have h3 : ContinuousOn (fun _ : S4 =>
      (e5 : EuclideanSpace ℝ (Fin 5) →L[ℝ] H5)) hemi0 := by
    simpa using (continuous_const : Continuous (fun _ : S4 =>
      (e5 : EuclideanSpace ℝ (Fin 5) →L[ℝ] H5))).continuousOn
  simpa only [InvCLM, ContinuousLinearMap.comp_assoc] using (h1.clm_comp h2).clm_comp h3

lemma HomExpr_true (j : ι₀) (b : S4) :
    (HomCLM b).comp ((Zb ι₀).coordChange (true, j) ((Zb ι₀).indexAt b) b)
      = (e5.symm : H5 →L[ℝ] EuclideanSpace ℝ (Fin 5)).comp
          ((HomTrue b).comp
            (e45 : (EuclideanSpace ℝ (Fin 4) × EuclideanSpace ℝ (Fin 1)) →L[ℝ] H5)) := by
  by_cases hb : b = OnePoint.infty
  · subst hb
    simp only [Zb_indexAt_infty, Zb_coordChange_tt, HomCLM, HomTrue, HomModel_infty,
      XModel_infty, ContinuousLinearMap.comp_id, ContinuousLinearMap.id_comp]
  · rw [Zb_indexAt_of_ne ι₀ b hb, Zb_coordChange_tf, HomCLM, HomTrue, XModel, if_neg hb]
    simp only [ContinuousLinearMap.comp_assoc]
    rw [e45_qTwist']

lemma InvExpr_true (j : ι₀) (b : S4) :
    ((Zb ι₀).coordChange ((Zb ι₀).indexAt b) (true, j) b).comp (InvCLM b)
      = (e45.symm : H5 →L[ℝ] (EuclideanSpace ℝ (Fin 4) × EuclideanSpace ℝ (Fin 1))).comp
          ((InvTrue b).comp (e5 : EuclideanSpace ℝ (Fin 5) →L[ℝ] H5)) := by
  by_cases hb : b = OnePoint.infty
  · subst hb
    simp only [Zb_indexAt_infty, Zb_coordChange_tt, InvCLM, InvTrue, YModel_infty,
      InvModel_infty, ContinuousLinearMap.comp_id, ContinuousLinearMap.id_comp]
  · rw [Zb_indexAt_of_ne ι₀ b hb, Zb_coordChange_ft, InvCLM, InvTrue, YModel, if_neg hb]
    conv_lhs => rw [← ContinuousLinearMap.comp_assoc]
    rw [e45_qTwist'']
    simp only [ContinuousLinearMap.comp_assoc]

lemma continuousOn_HomExpr_hemi1 (j : ι₀) :
    ContinuousOn (fun b : S4 =>
      (HomCLM b).comp ((Zb ι₀).coordChange (true, j) ((Zb ι₀).indexAt b) b)) hemi1 := by
  have h1 : ContinuousOn (fun _ : S4 =>
      (e5.symm : H5 →L[ℝ] EuclideanSpace ℝ (Fin 5))) hemi1 := by
    simpa using (continuous_const : Continuous (fun _ : S4 =>
      (e5.symm : H5 →L[ℝ] EuclideanSpace ℝ (Fin 5)))).continuousOn
  have h2 : ContinuousOn (fun b : S4 => HomTrue b) hemi1 := continuousOn_HomTrue_hemi1 ι₀ j
  have h3 : ContinuousOn (fun _ : S4 =>
      (e45 : (EuclideanSpace ℝ (Fin 4) × EuclideanSpace ℝ (Fin 1)) →L[ℝ] H5)) hemi1 := by
    simpa using (continuous_const : Continuous (fun _ : S4 =>
      (e45 : (EuclideanSpace ℝ (Fin 4) × EuclideanSpace ℝ (Fin 1)) →L[ℝ] H5))).continuousOn
  have h := (h1.clm_comp h2).clm_comp h3
  refine h.congr (fun b _ => ?_)
  rw [HomExpr_true]
  simp only [ContinuousLinearMap.comp_assoc]

lemma continuousOn_InvExpr_hemi1 (j : ι₀) :
    ContinuousOn (fun b : S4 =>
      ((Zb ι₀).coordChange ((Zb ι₀).indexAt b) (true, j) b).comp (InvCLM b)) hemi1 := by
  have h1 : ContinuousOn (fun _ : S4 =>
      (e45.symm : H5 →L[ℝ] (EuclideanSpace ℝ (Fin 4) × EuclideanSpace ℝ (Fin 1)))) hemi1 := by
    simpa using (continuous_const : Continuous (fun _ : S4 =>
      (e45.symm : H5 →L[ℝ] (EuclideanSpace ℝ (Fin 4) × EuclideanSpace ℝ (Fin 1))))).continuousOn
  have h2 : ContinuousOn (fun b : S4 => InvTrue b) hemi1 := continuousOn_InvTrue_hemi1 ι₀ j
  have h3 : ContinuousOn (fun _ : S4 =>
      (e5 : EuclideanSpace ℝ (Fin 5) →L[ℝ] H5)) hemi1 := by
    simpa using (continuous_const : Continuous (fun _ : S4 =>
      (e5 : EuclideanSpace ℝ (Fin 5) →L[ℝ] H5))).continuousOn
  have h := (h1.clm_comp h2).clm_comp h3
  refine h.congr (fun b _ => ?_)
  rw [InvExpr_true]
  simp only [ContinuousLinearMap.comp_assoc]

end

end Work.Agree

namespace Work.Agree

open Work.TangentClasses
open Classical

noncomputable section

variable (ι₀ : Type) [Inhabited ι₀]

lemma Zb_coordChange_false_indexAt (j : ι₀) (b : S4) (hb : b ∈ (Zb ι₀).baseSet (false, j)) :
    (Zb ι₀).coordChange (false, j) ((Zb ι₀).indexAt b) b = ContinuousLinearMap.id ℝ _ := by
  have hb0 : b ∈ hemi0 := by rwa [Zb_baseSet_false ι₀ j] at hb
  rw [Zb_indexAt_of_ne ι₀ b hb0, Zb_coordChange_ff]

lemma Zb_coordChange_indexAt_false (j : ι₀) (b : S4) (hb : b ∈ (Zb ι₀).baseSet (false, j)) :
    (Zb ι₀).coordChange ((Zb ι₀).indexAt b) (false, j) b = ContinuousLinearMap.id ℝ _ := by
  have hb0 : b ∈ hemi0 := by rwa [Zb_baseSet_false ι₀ j] at hb
  rw [Zb_indexAt_of_ne ι₀ b hb0, Zb_coordChange_ff]

end

end Work.Agree

namespace Work.Agree

open Work.TangentClasses
open Classical

noncomputable section

theorem clutchStable_aux (ι₀ : Type) [Inhabited ι₀] (ι' : Type) [Inhabited ι'] :
    Nonempty (Work.Thom.BundleIso (Zb ι₀)
      (RealBundle.trivial S4 (EuclideanSpace ℝ (Fin 5)) ι')) := by
  refine ⟨{
    hom := fun b => (HomCLM b).toLinearMap
    inv := fun b => (InvCLM b).toLinearMap
    left_inv := ?_
    right_inv := ?_
    continuous_hom := ?_
    continuous_inv := ?_ }⟩
  · intro b x
    have h := congrArg (fun (f : H5 →L[ℝ] H5) => f (e45 x))
      (MsInvCLM_comp_MsCLM (sOf b) (uDir b) (inner_uDir b))
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply] at h
    show e45.symm (InvModel b (e5 (e5.symm (HomModel b (e45 x))))) = x
    rw [ContinuousLinearEquiv.apply_symm_apply]
    show e45.symm ((MsInvCLM (sOf b) (uDir b)) ((MsCLM (sOf b) (uDir b)) (e45 x))) = x
    rw [h]
    exact ContinuousLinearEquiv.symm_apply_apply e45 x
  · intro b y
    have h := congrArg (fun (f : H5 →L[ℝ] H5) => f (e5 y))
      (MsCLM_comp_MsInvCLM (sOf b) (uDir b) (inner_uDir b))
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply] at h
    show e5.symm (HomModel b (e45 (e45.symm (InvModel b (e5 y))))) = y
    rw [ContinuousLinearEquiv.apply_symm_apply]
    show e5.symm ((MsCLM (sOf b) (uDir b)) ((MsInvCLM (sOf b) (uDir b)) (e5 y))) = y
    rw [h]
    exact ContinuousLinearEquiv.symm_apply_apply e5 y
  · refine Work.Thom.continuous_totalSpaceMap_clm_gen (Zb ι₀)
      (RealBundle.trivial S4 (EuclideanSpace ℝ (Fin 5)) ι') (ContinuousMap.id S4)
      (fun b => HomCLM b) ?_
    intro i₁ i₂
    simp only [RealBundle.trivial_coordChange, RealBundle.trivial_baseSet, Set.univ_inter,
      Set.inter_univ, Set.preimage_univ, ContinuousMap.id_apply,
      ContinuousLinearMap.id_comp]
    obtain ⟨i, j⟩ := i₁
    cases i
    · refine (continuousOn_HomCLM_baseSet ι₀ j).congr (fun b hb => ?_)
      rw [Zb_coordChange_false_indexAt ι₀ j b hb, ContinuousLinearMap.comp_id]
    · rw [Zb_baseSet_true ι₀ j]
      exact continuousOn_HomExpr_hemi1 ι₀ j
  · refine Work.Thom.continuous_totalSpaceMap_clm_gen
      (RealBundle.trivial S4 (EuclideanSpace ℝ (Fin 5)) ι') (Zb ι₀) (ContinuousMap.id S4)
      (fun b => InvCLM b) ?_
    intro i₂ i₁
    simp only [RealBundle.trivial_coordChange, RealBundle.trivial_baseSet, Set.univ_inter,
      Set.inter_univ, Set.preimage_univ, ContinuousMap.id_apply,
      ContinuousLinearMap.comp_id]
    obtain ⟨i, j⟩ := i₁
    cases i
    · refine (continuousOn_InvCLM_baseSet ι₀ j).congr (fun b hb => ?_)
      rw [Zb_coordChange_indexAt_false ι₀ j b hb, ContinuousLinearMap.id_comp]
    · rw [Zb_baseSet_true ι₀ j]
      exact continuousOn_InvExpr_hemi1 ι₀ j

end

end Work.Agree
