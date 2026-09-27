import Mathlib
import Submission.Work.Mostow.gapA.defs
import Submission.Work.Mostow.gapA.geodFacts
import Submission.Work.Mostow.gapA.mem_geodSet_iff_span
import Submission.Work.Mostow.gapA.rotSetup
import Submission.Work.Mostow.perpNullUnit
import Submission.Work.Mostow.finite_nearStab

/-!
# The axis of a rotation about a geodesic: vocabulary

`NormSub a b` is the Minkowski-orthogonal complement of the two null vectors `θ_a`, `θ_b`
(the normal plane of the geodesic `geodSet a b`), `AxisBasis a b` bundles a positive definite
orthonormal basis of it, and `AxisFix hA a b` / `AxisStab hA a b` are the effective and the
geometric pointwise stabilisers of the geodesic.
-/

namespace Work.Mostow.gapA
open Submission.Mostow LeanEval.Geometry.MostowRigidity MeasureTheory
open _root_.Matrix
noncomputable section
variable {a b : E 3}

def NormSub (a b : E 3) : Submodule ℝ (Fin 3 ⊕ Fin 1 → ℝ) where
  carrier := {Z | mink Z (nvec a) = 0 ∧ mink Z (nvec b) = 0}
  zero_mem' := ⟨by simp [mink], by simp [mink]⟩
  add_mem' := by
    rintro x y ⟨hx1, hx2⟩ ⟨hy1, hy2⟩
    exact ⟨by rw [minkSeg_add_left, hx1, hy1, add_zero],
           by rw [minkSeg_add_left, hx2, hy2, add_zero]⟩
  smul_mem' := by
    rintro c x ⟨hx1, hx2⟩
    exact ⟨by rw [mink_smul_left'', hx1, mul_zero],
           by rw [mink_smul_left'', hx2, mul_zero]⟩

lemma mem_NormSub {Z : Fin 3 ⊕ Fin 1 → ℝ} :
    Z ∈ NormSub a b ↔ mink Z (nvec a) = 0 ∧ mink Z (nvec b) = 0 := Iff.rfl

lemma mink_nvec_pair_ne_zero (ha : a ∈ Sph 3) (hb : b ∈ Sph 3) (hab : a ≠ b) :
    mink (nvec a) (nvec b) ≠ 0 := by
  have ha' : ‖a‖ = 1 := (mem_Sph_iff a).mp ha
  have hb' : ‖b‖ = 1 := (mem_Sph_iff b).mp hb
  rw [mink_nvec_nvec']
  intro h
  exact hab ((inner_eq_one_iff_of_norm_eq_one ha' hb').mp (sub_eq_zero.mp h))

lemma mink_self_of_mem_NormSub (ha : a ∈ Sph 3) {Z : Fin 3 ⊕ Fin 1 → ℝ}
    (hZ : Z ∈ NormSub a b) : mink Z Z = ‖hspat (horoProj a Z)‖ ^ 2 := by
  have hza : mform Z (theta a) = 0 := by
    rw [← mink_eq_mform, ← nvec_eq_theta]
    exact hZ.1
  rw [mink_eq_mform, mform_self_eq_hspat_horoProj ha hza]

lemma mink_nonneg_of_mem_NormSub (ha : a ∈ Sph 3) {Z : Fin 3 ⊕ Fin 1 → ℝ}
    (hZ : Z ∈ NormSub a b) : 0 ≤ mink Z Z := by
  rw [mink_self_of_mem_NormSub ha hZ]; positivity

lemma eq_zero_of_mem_NormSub_of_mink_self_eq_zero (ha : a ∈ Sph 3) (hb : b ∈ Sph 3)
    (hab : a ≠ b) {Z : Fin 3 ⊕ Fin 1 → ℝ} (hZ : Z ∈ NormSub a b) (h0 : mink Z Z = 0) :
    Z = 0 := by
  have hza : mform Z (theta a) = 0 := by
    rw [← mink_eq_mform, ← nvec_eq_theta]
    exact hZ.1
  have hnorm : ‖hspat (horoProj a Z)‖ = 0 := by
    have h := mink_self_of_mem_NormSub ha hZ
    rw [h0] at h
    exact pow_eq_zero_iff (n := 2) (by norm_num) |>.mp h.symm
  have hsp : hspat (horoProj a Z) = 0 := norm_eq_zero.mp hnorm
  have hht : htime (horoProj a Z) = 0 :=
    htime_eq_zero_of_horoProj a ha (horoProj_idem a ha Z)
  have hproj : horoProj a Z = 0 := by
    rw [eq_elim_hspat_htime (horoProj a Z), hsp, hht]
    ext k
    rcases k with i | j
    · simp
    · simp
  have hdec : Z = horoProj a Z + (mform Z (horoEta a) / 2) • theta a :=
    eq_horoProj_add hza
  rw [hproj, zero_add] at hdec
  have hq : mform Z (horoEta a) = 0 := by
    have hpair : mink Z (nvec b)
        = (mform Z (horoEta a) / 2) * mink (nvec a) (nvec b) := by
      conv_lhs => rw [hdec]
      rw [mink_smul_left'', ← nvec_eq_theta, mink_nvec_nvec']
    rw [hZ.2] at hpair
    have h3 := (mul_eq_zero.mp hpair.symm).resolve_right (mink_nvec_pair_ne_zero ha hb hab)
    linarith
  rw [hdec, hq]
  simp

structure AxisBasis (a b : E 3) where
  E1 : Fin 3 ⊕ Fin 1 → ℝ
  E2 : Fin 3 ⊕ Fin 1 → ℝ
  mem1 : E1 ∈ NormSub a b
  mem2 : E2 ∈ NormSub a b
  n11 : mink E1 E1 = 1
  n22 : mink E2 E2 = 1
  n12 : mink E1 E2 = 0
  span : ∀ Z : Fin 3 ⊕ Fin 1 → ℝ, Z ∈ NormSub a b → ∃ α β : ℝ, Z = α • E1 + β • E2
  spanV : ∀ Z : Fin 3 ⊕ Fin 1 → ℝ, ∃ α β γ δ : ℝ,
    Z = α • nvec a + β • nvec b + γ • E1 + δ • E2

variable {B : AxisBasis a b}

lemma mink_E2_E1 : mink B.E2 B.E1 = 0 := by
  rw [minkSeg_comm B.E2 B.E1]; exact B.n12
lemma mink_a_E1 : mink (nvec a) B.E1 = 0 := by rw [minkSeg_comm]; exact B.mem1.1
lemma mink_a_E2 : mink (nvec a) B.E2 = 0 := by rw [minkSeg_comm]; exact B.mem2.1
lemma mink_b_E1 : mink (nvec b) B.E1 = 0 := by rw [minkSeg_comm]; exact B.mem1.2
lemma mink_b_E2 : mink (nvec b) B.E2 = 0 := by rw [minkSeg_comm]; exact B.mem2.2

include B in
lemma axisBasis_independent : ∀ α β : ℝ, α • B.E1 + β • B.E2 = 0 → α = 0 ∧ β = 0 := by
  intro α β h
  have h2 : mink (α • B.E1 + β • B.E2) B.E2 = 0 := by rw [h]; simp [mink]
  have hβ : β = 0 := by
    rw [minkSeg_add_left, mink_smul_left'', mink_smul_left''] at h2
    simpa only [B.n12, B.n22, mul_zero, mul_one, zero_add, add_zero] using h2
  have h1 : mink (α • B.E1 + β • B.E2) B.E1 = 0 := by rw [h]; simp [mink]
  subst hβ
  rw [minkSeg_add_left, mink_smul_left'', mink_smul_left''] at h1
  have hα : α = 0 := by
    simpa only [B.n11, mul_one, mul_zero, zero_mul, zero_add, add_zero, mink_E2_E1] using h1
  exact ⟨hα, rfl⟩

include B in
lemma axisBasis_pairE1 (α β γ δ : ℝ) :
    mink (α • nvec a + β • nvec b + γ • B.E1 + δ • B.E2) B.E1 = γ := by
  rw [show α • nvec a + β • nvec b + γ • B.E1 + δ • B.E2
      = (α • nvec a + β • nvec b) + (γ • B.E1 + δ • B.E2) from by abel,
    minkSeg_add_left, minkSeg_add_left, minkSeg_add_left,
    mink_smul_left'', mink_smul_left'', mink_smul_left'', mink_smul_left'']
  simp only [mink_a_E1, mink_b_E1, B.n11, mink_E2_E1, mul_zero, mul_one,
    zero_add, add_zero]

include B in
lemma axisBasis_pairE2 (α β γ δ : ℝ) :
    mink (α • nvec a + β • nvec b + γ • B.E1 + δ • B.E2) B.E2 = δ := by
  rw [show α • nvec a + β • nvec b + γ • B.E1 + δ • B.E2
      = (α • nvec a + β • nvec b) + (γ • B.E1 + δ • B.E2) from by abel,
    minkSeg_add_left, minkSeg_add_left, minkSeg_add_left,
    mink_smul_left'', mink_smul_left'', mink_smul_left'', mink_smul_left'']
  simp only [mink_a_E2, mink_b_E2, B.n12, B.n22, mul_zero, mul_one,
    zero_add, add_zero]

lemma mink_nvec_self_a (ha : a ∈ Sph 3) : mink (nvec a) (nvec a) = 0 := by
  rw [mink_nvec_nvec', real_inner_self_eq_norm_sq, (mem_Sph_iff a).mp ha]
  norm_num

lemma mink_nvec_self_b (hb : b ∈ Sph 3) : mink (nvec b) (nvec b) = 0 := by
  rw [mink_nvec_nvec', real_inner_self_eq_norm_sq, (mem_Sph_iff b).mp hb]
  norm_num

lemma mink_nvec_b_a : mink (nvec b) (nvec a) = inner ℝ a b - 1 := by
  rw [minkSeg_comm (nvec b) (nvec a), mink_nvec_nvec', real_inner_comm]

include B in
lemma axisBasis_independentV (ha : a ∈ Sph 3) (hb : b ∈ Sph 3) (hab : a ≠ b) :
    ∀ α β γ δ : ℝ,
    α • nvec a + β • nvec b + γ • B.E1 + δ • B.E2 = 0 → α = 0 ∧ β = 0 ∧ γ = 0 ∧ δ = 0 := by
  intro α β γ δ h
  have hγ : γ = 0 := by
    have h1 : mink (α • nvec a + β • nvec b + γ • B.E1 + δ • B.E2) B.E1 = 0 := by
      rw [h]; simp [mink]
    rwa [axisBasis_pairE1 (B := B) α β γ δ] at h1
  have hδ : δ = 0 := by
    have h1 : mink (α • nvec a + β • nvec b + γ • B.E1 + δ • B.E2) B.E2 = 0 := by
      rw [h]; simp [mink]
    rwa [axisBasis_pairE2 (B := B) α β γ δ] at h1
  rw [hγ, hδ] at h
  simp only [zero_smul, add_zero] at h
  have hαβ : α = 0 ∧ β = 0 := by
    have h1 : mink (α • nvec a + β • nvec b) (nvec a) = 0 := by rw [h]; simp [mink]
    have h2 : mink (α • nvec a + β • nvec b) (nvec b) = 0 := by rw [h]; simp [mink]
    rw [minkSeg_add_left, mink_smul_left'', mink_smul_left''] at h1 h2
    rw [mink_nvec_self_a ha, mink_nvec_b_a] at h1
    rw [mink_nvec_nvec', mink_nvec_self_b hb] at h2
    simp only [mul_zero, zero_add, add_zero] at h1 h2
    have hc : inner ℝ a b - 1 ≠ 0 := by
      intro hh
      exact hab ((inner_eq_one_iff_of_norm_eq_one ((mem_Sph_iff a).mp ha)
        ((mem_Sph_iff b).mp hb)).mp (sub_eq_zero.mp hh))
    exact ⟨(mul_eq_zero.mp h2).resolve_right hc, (mul_eq_zero.mp h1).resolve_right hc⟩
  exact ⟨hαβ.1, hαβ.2, hγ, hδ⟩

def AxisStab (hA : POActionProp 3) (a b : E 3) : Subgroup (PO 3 1) where
  carrier := {g | ∀ u : E 3, u ∈ geodSet a b → g • u = u}
  mul_mem' := by
    intro g h hg hh u hu
    rw [(POBasic.ofProp hA).mul_smul, hh u hu, hg u hu]
  one_mem' := by
    intro u _
    exact (POBasic.ofProp hA).one_smul u
  inv_mem' := by
    intro g hg u hu
    calc g⁻¹ • u = g⁻¹ • (g • u) := by rw [hg u hu]
      _ = (g⁻¹ * g) • u := ((POBasic.ofProp hA).mul_smul g⁻¹ g u).symm
      _ = (1 : PO 3 1) • u := by rw [inv_mul_cancel]
      _ = u := (POBasic.ofProp hA).one_smul u

def AxisFix (hA : POActionProp 3) (a b : E 3) : Subgroup (PO 3 1) where
  carrier := {g | Matrix.mulVec (emat g) (nvec a) = nvec a ∧
    Matrix.mulVec (emat g) (nvec b) = nvec b ∧ (emat g).det = 1}
  mul_mem' := by
    rintro g h ⟨hg1, hg2, hgd⟩ ⟨hh1, hh2, hhd⟩
    refine ⟨?_, ?_, ?_⟩
    · rw [emat_mul hA, ← Matrix.mulVec_mulVec (nvec a) (emat g) (emat h), hh1, hg1]
    · rw [emat_mul hA, ← Matrix.mulVec_mulVec (nvec b) (emat g) (emat h), hh2, hg2]
    · rw [emat_mul hA, Matrix.det_mul, hgd, hhd, one_mul]
  one_mem' := by
    refine ⟨?_, ?_, ?_⟩
    · rw [emat_one hA, Matrix.one_mulVec]
    · rw [emat_one hA, Matrix.one_mulVec]
    · rw [emat_one hA, Matrix.det_one]
  inv_mem' := by
    rintro g ⟨hg1, hg2, hgd⟩
    have hg'g : emat g⁻¹ * emat g = 1 := by rw [← emat_mul hA, inv_mul_cancel, emat_one hA]
    have hgg' : emat g * emat g⁻¹ = 1 := by rw [← emat_mul hA, mul_inv_cancel, emat_one hA]
    refine ⟨?_, ?_, ?_⟩
    · have h := congrArg (fun z => Matrix.mulVec (emat g⁻¹) z) hg1
      rw [Matrix.mulVec_mulVec (nvec a) (emat g⁻¹) (emat g), hg'g,
        Matrix.one_mulVec] at h
      exact h.symm
    · have h := congrArg (fun z => Matrix.mulVec (emat g⁻¹) z) hg2
      rw [Matrix.mulVec_mulVec (nvec b) (emat g⁻¹) (emat g), hg'g,
        Matrix.one_mulVec] at h
      exact h.symm
    · have h : (emat g).det * (emat g⁻¹).det = 1 := by
        rw [← Matrix.det_mul, hgg', Matrix.det_one]
      rw [hgd, one_mul] at h
      exact h

lemma det_emat_eq_one_of_isOriented (g : PO 3 1) (h : IsOriented g) : (emat g).det = 1 := by
  have h1 : (emat g).det = (mat (rep g)).det := det_emat3 g
  have h2 : (mat (rep g)).det * (mat (rep g)).det = 1 := by
    have h3 : IsJOrth (mat (rep g)) := O1_form_col _
    have h := congrArg Matrix.det h3
    rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose] at h
    have hJ : (pmOneMat (p := Fin 3) (q := Fin 1) (α := ℝ)).det = -1 := by
      rw [pmOneMat, Matrix.det_fromBlocks_zero₁₂, Matrix.det_one, Matrix.det_fin_one]
      norm_num
    rw [hJ] at h
    linarith
  rw [h1]
  have h2' : (mat (rep g)).det ^ 2 = 1 := by rw [pow_two]; exact h2
  rcases sq_eq_one_iff.mp h2' with h4 | h4
  · exact h4
  · have h5 : 0 < (mat (rep g)).det := h
    rw [h4] at h5
    norm_num at h5

lemma geodSet_fixed_of_mem_axisFix (hA : POActionProp 3) {g : PO 3 1}
    (ha : a ∈ Sph 3) (hb : b ∈ Sph 3) (hab : a ≠ b) (hg : g ∈ AxisFix hA a b) :
    ∀ u : E 3, u ∈ geodSet a b → g • u = u := by
  intro u hu
  obtain ⟨α, β, hαβ⟩ := (mem_geodSet_iff_span a b ha hb hab u).mp hu
  have hml : Matrix.mulVec (emat g) (hlift u) = hlift u := by
    rw [hαβ, Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_smul, hg.1, hg.2.1]
  have h2 : hlift (g • u) = hlift u := by rw [← emat_hlift g u, hml]
  exact Submission.Mostow.Hyper.hlift_injective h2
end
end Work.Mostow.gapA
