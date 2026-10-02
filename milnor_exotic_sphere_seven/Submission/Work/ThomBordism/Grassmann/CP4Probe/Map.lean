import Mathlib
import Submission.Work.ThomBordism.Grassmann.CP4Probe.Basic

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option linter.unusedSimpArgs false

namespace Work.ThomBordism.Grassmann

open Work.TangentClasses Work.Projective

noncomputable section

/-! ## Continuity of the frame family -/

theorem continuous_cfOf : Continuous (cfOf : (Fin 5 → ℂ) → E5) :=
  PiLp.continuous_toLp 2 (fun _ : Fin 5 => ℂ)

theorem continuousOn_cfUnit :
    ContinuousOn (fun v : Fin 5 → ℂ => cfUnit v) {v | v ≠ 0} := by
  refine ContinuousOn.smul (ContinuousOn.inv₀
    (f := fun v : Fin 5 → ℂ => ‖cfOf v‖) (s := {v | v ≠ 0})
    (continuous_norm.comp continuous_cfOf).continuousOn ?_) continuous_cfOf.continuousOn
  intro v hv
  exact norm_ne_zero_iff.mpr (cfOf_ne_zero hv)

theorem continuous_lineFrame_subtype :
    Continuous (fun a : {v : Fin 5 → ℂ // v ≠ 0} => lineFrame a.1) := by
  have hcu : Continuous fun a : {v : Fin 5 → ℂ // v ≠ 0} => cfUnit a.1 :=
    continuousOn_iff_continuous_domRestrict.mp continuousOn_cfUnit
  have h0 : Continuous fun a : {v : Fin 5 → ℂ // v ≠ 0} => emb5 (cfUnit a.1) :=
    emb5.continuous.comp hcu
  have h1 : Continuous fun a : {v : Fin 5 → ℂ // v ≠ 0} => emb5 (Complex.I • cfUnit a.1) :=
    emb5.continuous.comp (Continuous.const_smul hcu Complex.I)
  rw [continuous_pi_iff]
  intro j
  fin_cases j
  · exact h0
  · exact h1.neg

/-! ## Orthonormality of the frame -/

theorem lineFrame_inner_self (v : Fin 5 → ℂ) (hv : v ≠ 0) :
    inner ℝ (lineFrame v 0) (lineFrame v 0) = 1 := by
  rw [lineFrame_zero, inner_emb5, real_inner_self_eq_norm_sq, cfUnit_norm hv]
  norm_num

theorem lineFrame_inner_I (v : Fin 5 → ℂ) (hv : v ≠ 0) :
    inner ℝ (lineFrame v 0) (lineFrame v 1) = 0 := by
  rw [lineFrame_zero, lineFrame_one, inner_neg_right, inner_emb5]
  rw [show inner ℝ (cfUnit v) (Complex.I • cfUnit v) = 0 from
    real_inner_I_smul_self ℂ (cfUnit v)]
  simp

theorem lineFrame_inner_II (v : Fin 5 → ℂ) (hv : v ≠ 0) :
    inner ℝ (lineFrame v 1) (lineFrame v 1) = 1 := by
  rw [lineFrame_one, inner_neg_left, inner_neg_right, inner_emb5, real_inner_self_eq_norm_sq,
    norm_smul, Complex.norm_I, one_mul, cfUnit_norm hv]
  norm_num

theorem lineFrame_orthonormal (v : Fin 5 → ℂ) (hv : v ≠ 0) : Orthonormal ℝ (lineFrame v) := by
  rw [orthonormal_iff_ite]
  intro a a'
  fin_cases a <;> fin_cases a'
  · simpa using lineFrame_inner_self v hv
  · simpa using lineFrame_inner_I v hv
  · rw [real_inner_comm]; simpa using lineFrame_inner_I v hv
  · simpa using lineFrame_inner_II v hv

/-! ## The `SO(2)`-equivariance of the frame -/

theorem isSO_probeRotMat {μ : ℂ} (hμ : ‖μ‖ = 1) : IsSO (probeRotMat μ) :=
  ⟨probeRotMat_transpose_mul hμ, probeRotMat_det hμ⟩

theorem lineFrame_congr {v v' : Fin 5 → ℂ} (h : cfUnit v = cfUnit v') :
    lineFrame v = lineFrame v' := by
  unfold lineFrame
  rw [h]

theorem cdiv_norm_smul (v : Fin 5 → ℂ) {c : ℂ} (hc : c ≠ 0) :
    c • v = ((‖c‖ : ℝ)) • ((c / ((‖c‖ : ℝ) : ℂ)) • v) := by
  rw [← smul_assoc, Complex.real_smul]
  congr 1
  exact (mul_div_cancel₀ c (by simpa using (norm_ne_zero_iff.mpr hc))).symm

theorem div_norm_norm_eq_one {c : ℂ} (hc : c ≠ 0) : ‖c / ((‖c‖ : ℝ) : ℂ)‖ = 1 := by
  rw [norm_div]
  have h2 : ‖((‖c‖ : ℝ) : ℂ)‖ = ‖c‖ := by simp
  rw [h2, div_self (norm_ne_zero_iff.mpr hc)]

theorem div_norm_ne_zero {c : ℂ} (hc : c ≠ 0) : c / ((‖c‖ : ℝ) : ℂ) ≠ 0 := by
  have h := div_norm_norm_eq_one hc
  intro h0; rw [h0] at h; simp at h

theorem lineFrame_smul_norm (v : Fin 5 → ℂ) (hv : v ≠ 0) {c : ℂ} (hc : c ≠ 0) :
    lineFrame (c • v) = lineFrame ((c / ((‖c‖ : ℝ) : ℂ)) • v) := by
  rw [cdiv_norm_smul v hc]
  exact lineFrame_congr (cfUnit_smul_pos (smul_ne_zero (div_norm_ne_zero hc) hv)
    (norm_pos_iff.mpr hc))

theorem I_smul_I_smul' (x : E5) : (Complex.I : ℂ) • (Complex.I • x) = -x := by
  rw [smul_smul, Complex.I_mul_I, neg_one_smul]

theorem lineFrame_smul_apply (v : Fin 5 → ℂ) (hv : v ≠ 0) {μ : ℂ} (hμ : ‖μ‖ = 1) :
    lineFrame (μ • v) = soActFun (k := 2) (m := 8) (probeRotMat μ) (lineFrame v) := by
  have hcu : cfUnit (μ • v) = μ • cfUnit v := cfUnit_smul_unit hv hμ
  have hIcu : Complex.I • cfUnit (μ • v) = μ • (Complex.I • cfUnit v) := by
    rw [hcu, smul_comm]
  have h0 : lineFrame (μ • v) 0
      = soActFun (k := 2) (m := 8) (probeRotMat μ) (lineFrame v) 0 := by
    rw [lineFrame_zero, soActFun, Fin.sum_univ_two, probeRotMat_zero_zero,
      probeRotMat_one_zero, lineFrame_zero, lineFrame_one, hcu, emb5_complex_smul]
    simp
  have h1 : lineFrame (μ • v) 1
      = soActFun (k := 2) (m := 8) (probeRotMat μ) (lineFrame v) 1 := by
    rw [lineFrame_one, soActFun, Fin.sum_univ_two, probeRotMat_zero_one,
      probeRotMat_one_one, lineFrame_zero, lineFrame_one, hIcu, emb5_complex_smul, I_smul_I_smul',
      map_neg]
    simp [smul_neg]
  funext a
  fin_cases a
  · exact h0
  · exact h1

theorem lineFrame_smul (v : Fin 5 → ℂ) (hv : v ≠ 0) {c : ℂ} (hc : c ≠ 0) :
    lineFrame (c • v)
      = soActFun (k := 2) (m := 8) (probeRotMat (c / ((‖c‖ : ℝ) : ℂ))) (lineFrame v) := by
  rw [lineFrame_smul_norm v hv hc]
  exact lineFrame_smul_apply v hv (div_norm_norm_eq_one hc)

/-! ## The map `ℂP⁴ → G̃r₂(ℝ¹⁰)` -/

/-- The frame of the complex line of a nonzero representative, as an element of the Stiefel
manifold. -/
noncomputable def lineStiefel (v : {v : Fin 5 → ℂ // v ≠ 0}) : Stiefel 2 8 :=
  ⟨lineFrame v.1, lineFrame_orthonormal v.1 v.2⟩

theorem lineStiefel_val (v : {v : Fin 5 → ℂ // v ≠ 0}) : (lineStiefel v).1 = lineFrame v.1 := rfl

theorem lineStiefel_smul_condition :
    ∀ (a b : {v : Fin 5 → ℂ // v ≠ 0}) (t : ℂ), (a : Fin 5 → ℂ) = t • (b : Fin 5 → ℂ) →
      ogMk 2 8 (lineStiefel a) = ogMk 2 8 (lineStiefel b) := by
  intro a b t h
  by_cases ht : t = 0
  · rw [ht, zero_smul] at h
    exact absurd h a.2
  · set A : SOk 2 := ⟨probeRotMat (t / ((‖t‖ : ℝ) : ℂ)), isSO_probeRotMat (div_norm_norm_eq_one ht)⟩
      with hA
    have heq : lineStiefel a = A.act (lineStiefel b) := by
      apply Subtype.ext
      show lineFrame (a : Fin 5 → ℂ)
        = soActFun (k := 2) (m := 8) (probeRotMat (t / ((‖t‖ : ℝ) : ℂ)))
            (lineFrame (b : Fin 5 → ℂ))
      rw [h]
      exact lineFrame_smul (b : Fin 5 → ℂ) b.2 ht
    rw [heq]
    exact Quotient.sound ⟨A.transpose, (SOk.act_transpose_act A (lineStiefel b)).symm⟩

/-- The underlying function of the `ℂP⁴`-probe. -/
noncomputable def probeCP4MapFun (x : CP 4) : OG 2 8 :=
  Projectivization.lift (fun v : {v : Fin 5 → ℂ // v ≠ 0} => ogMk 2 8 (lineStiefel v))
    lineStiefel_smul_condition x

theorem probeCP4MapFun_apply (v : {v : Fin 5 → ℂ // v ≠ 0}) :
    probeCP4MapFun (Projectivization.mk' ℂ v) = ogMk 2 8 (lineStiefel v) :=
  Projectivization.lift_mk _ _ v.1 v.2

theorem continuous_lineStiefel :
    Continuous (fun v : {v : Fin 5 → ℂ // v ≠ 0} => lineStiefel v) :=
  Continuous.subtype_mk continuous_lineFrame_subtype (fun v => lineFrame_orthonormal v.1 v.2)

theorem continuous_probeCP4MapFun : Continuous probeCP4MapFun := by
  have hq : Topology.IsQuotientMap (Projectivization.mk' ℂ :
      {v : Fin 5 → ℂ // v ≠ 0} → CP 4) := isQuotientMap_quotient_mk'
  have hφ : Continuous (fun v : {v : Fin 5 → ℂ // v ≠ 0} => ogMk 2 8 (lineStiefel v)) :=
    (ogMk 2 8).continuous.comp continuous_lineStiefel
  have hcomp : probeCP4MapFun ∘ (Projectivization.mk' ℂ :
        {v : Fin 5 → ℂ // v ≠ 0} → CP 4)
      = fun v => ogMk 2 8 (lineStiefel v) :=
    funext (fun v => probeCP4MapFun_apply v)
  rw [hq.continuous_iff]
  rw [hcomp]
  exact hφ

/-- **The `ℂP⁴`-probe**: the map sending a complex line of `ℂ⁵` to the oriented real `2`-plane it
spans in `ℝ¹⁰ = ℂ⁵`. -/
noncomputable def probeCP4Map : C(CP 4, OG 2 8) :=
  ⟨probeCP4MapFun, continuous_probeCP4MapFun⟩

theorem probeCP4Map_apply (v : {v : Fin 5 → ℂ // v ≠ 0}) :
    probeCP4Map (Projectivization.mk' ℂ v) = ogMk 2 8 (lineStiefel v) :=
  probeCP4MapFun_apply v

theorem probeCP4Map_apply_cpMk (v : {v : Fin 5 → ℂ // v ≠ 0}) :
    probeCP4Map (cpMk 4 v) = ogMk 2 8 (lineStiefel v) :=
  probeCP4Map_apply v

end

end Work.ThomBordism.Grassmann
