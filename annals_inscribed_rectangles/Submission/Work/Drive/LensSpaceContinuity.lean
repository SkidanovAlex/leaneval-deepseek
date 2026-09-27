import Mathlib
import Submission.Work.Drive.LensSpaceGlue
import Submission.Work.Drive.phiCap_eq_phiConf

/-!
# Continuity of the glueing map `phi : S³ → LensSpace`

The map `Work.Drive.phi` of `Submission/Work/Drive/LensSpaceGlue` is defined by the two branches
`capPt` and `confPt` on the two closed hemispheres `capHemi ∪ confHemi = S³`.  Both branches are
composites of continuous explicit formulas with `Quotient.mk'' ∘ Sum.inl` (resp. `∘ Sum.inr`), hence
`phi` is continuous on each of the two closed pieces, and `ContinuousOn.union_of_isClosed` (the two
pieces are closed and cover the sphere) gives `Continuous phi`.
-/

set_option maxHeartbeats 8000000

namespace Work.Drive

noncomputable section

open scoped Topology

/-- The unit complex number `z` of norm `1`, as an element of the circle `Circle`. -/
def toCircle (z : ℂ) (hz : ‖z‖ = 1) : Circle := ⟨z, by
  change z ∈ (Submonoid.unitSphere ℂ : Set ℂ)
  rw [Submonoid.coe_unitSphere]
  simpa [Metric.mem_sphere, dist_eq_norm] using hz⟩

/-- The inverse of `circleOf`: the element of `ℝ/ℤ` of a point of the circle. -/
def circOf' (z : Circle) : UnitAddCircle :=
  (AddCircle.homeomorphCircle (T := 1) one_ne_zero).symm z

lemma circOf_eq (z : ℂ) (hz : ‖z‖ = 1) : circOf z hz = circOf' (toCircle z hz) := rfl

lemma continuous_circOf' : Continuous circOf' :=
  (AddCircle.homeomorphCircle (T := 1) one_ne_zero).symm.continuous

section Cap

/-- The first-coordinate formula of `capPt`. -/
def capThetaFun (w : {v : unitSphere 3 // ‖c₁ v.1‖ ≤ ‖c₂ v.1‖}) : ℂ :=
  ((((‖c₂ w.1.1‖ : ℝ) : ℂ) / c₂ w.1.1) ^ 2)

/-- The disk-coordinate formula of `capPt`. -/
def capDiskFun (w : {v : unitSphere 3 // ‖c₁ v.1‖ ≤ ‖c₂ v.1‖}) : ℂ :=
  (Real.sqrt 2 : ℂ) * c₁ w.1.1 * c₂ w.1.1 / (((‖c₂ w.1.1‖ : ℝ)) : ℂ)

lemma continuous_cap_c₁ : Continuous fun w : {v : unitSphere 3 // ‖c₁ v.1‖ ≤ ‖c₂ v.1‖} =>
    c₁ w.1.1 :=
  continuous_c₁.comp (continuous_subtype_val.comp continuous_subtype_val)

lemma continuous_cap_c₂ : Continuous fun w : {v : unitSphere 3 // ‖c₁ v.1‖ ≤ ‖c₂ v.1‖} =>
    c₂ w.1.1 :=
  continuous_c₂.comp (continuous_subtype_val.comp continuous_subtype_val)

lemma continuous_cap_norm₂ : Continuous fun w : {v : unitSphere 3 // ‖c₁ v.1‖ ≤ ‖c₂ v.1‖} =>
    ‖c₂ w.1.1‖ :=
  continuous_norm.comp continuous_cap_c₂

lemma continuous_capThetaFun : Continuous capThetaFun := by
  rw [show capThetaFun = fun w : {v : unitSphere 3 // ‖c₁ v.1‖ ≤ ‖c₂ v.1‖} =>
      ((((‖c₂ w.1.1‖ : ℝ) : ℂ) / c₂ w.1.1) ^ 2) from rfl]
  refine Continuous.pow (Continuous.div ?_ ?_ ?_) 2
  · exact Complex.continuous_ofReal.comp continuous_cap_norm₂
  · exact continuous_cap_c₂
  · intro w
    exact ne_zero_of_norm_le (a := c₁ w.1.1) (b := c₂ w.1.1) w.2 (sq_norm_eq_one w.1)

lemma capTheta_norm (w : {v : unitSphere 3 // ‖c₁ v.1‖ ≤ ‖c₂ v.1‖}) : ‖capThetaFun w‖ = 1 := by
  rw [show capThetaFun w = ((((‖c₂ w.1.1‖ : ℝ) : ℂ) / c₂ w.1.1) ^ 2) from rfl]
  exact norm_sq_self_div _ (ne_zero_of_norm_le w.2 (sq_norm_eq_one w.1))

lemma continuous_capDiskFun : Continuous capDiskFun := by
  rw [show capDiskFun = fun w : {v : unitSphere 3 // ‖c₁ v.1‖ ≤ ‖c₂ v.1‖} =>
      (Real.sqrt 2 : ℂ) * c₁ w.1.1 * c₂ w.1.1 / (((‖c₂ w.1.1‖ : ℝ)) : ℂ) from rfl]
  refine Continuous.div ?_ ?_ ?_
  · exact (continuous_const.mul continuous_cap_c₁).mul continuous_cap_c₂
  · exact Complex.continuous_ofReal.comp continuous_cap_norm₂
  · intro w
    have hz : ‖c₂ w.1.1‖ ≠ 0 :=
      norm_ne_zero_iff.mpr (ne_zero_of_norm_le w.2 (sq_norm_eq_one w.1))
    simpa using hz

lemma capDisk_mem (w : {v : unitSphere 3 // ‖c₁ v.1‖ ≤ ‖c₂ v.1‖}) :
    capDiskFun w ∈ Metric.closedBall (0 : ℂ) 1 := by
  rw [Metric.mem_closedBall, dist_eq_norm, sub_zero]
  exact norm_sqrt_two_mul_div_le _ _
    (ne_zero_of_norm_le w.2 (sq_norm_eq_one w.1))
    (norm_le_inv_sqrt_two w.2 (sq_norm_eq_one w.1))

/-- The cap point map is continuous. -/
lemma continuous_capPt : Continuous capPt := by
  have h1 : Continuous fun w : {v : unitSphere 3 // ‖c₁ v.1‖ ≤ ‖c₂ v.1‖} => (capPt w).1 := by
    have hc : Continuous fun w => circOf' (toCircle (capThetaFun w) (capTheta_norm w)) :=
      continuous_circOf'.comp (Continuous.subtype_mk continuous_capThetaFun
        (fun w => mem_unitSphere_of_norm (capTheta_norm w)))
    exact hc.congr (fun w => (circOf_eq _ _).symm)
  have h2 : Continuous fun w : {v : unitSphere 3 // ‖c₁ v.1‖ ≤ ‖c₂ v.1‖} => (capPt w).2 := by
    have hc : Continuous fun w => (⟨capDiskFun w, capDisk_mem w⟩ : Metric.closedBall (0 : ℂ) 1) :=
      Continuous.subtype_mk continuous_capDiskFun capDisk_mem
    exact hc.congr (fun w => (Subtype.ext (capPt_snd w).symm).symm)
  exact (h1.prodMk h2).congr (fun w => rfl)

end Cap

section Conf

/-- The second-coordinate formula of `confPt`. -/
def confEtaFun (w : {v : unitSphere 3 // ‖c₂ v.1‖ ≤ ‖c₁ v.1‖}) : ℂ :=
  (c₁ w.1.1 / ((‖c₁ w.1.1‖ : ℝ) : ℂ)) ^ 2

/-- The disk-coordinate formula of `confPt`. -/
def confDiskFun (w : {v : unitSphere 3 // ‖c₂ v.1‖ ≤ ‖c₁ v.1‖}) : ℂ :=
  (Real.sqrt 2 : ℂ) * c₂ w.1.1 * c₁ w.1.1 / (((‖c₁ w.1.1‖ : ℝ)) : ℂ)

lemma continuous_conf_c₁ : Continuous fun w : {v : unitSphere 3 // ‖c₂ v.1‖ ≤ ‖c₁ v.1‖} =>
    c₁ w.1.1 :=
  continuous_c₁.comp (continuous_subtype_val.comp continuous_subtype_val)

lemma continuous_conf_c₂ : Continuous fun w : {v : unitSphere 3 // ‖c₂ v.1‖ ≤ ‖c₁ v.1‖} =>
    c₂ w.1.1 :=
  continuous_c₂.comp (continuous_subtype_val.comp continuous_subtype_val)

lemma continuous_conf_norm₁ : Continuous fun w : {v : unitSphere 3 // ‖c₂ v.1‖ ≤ ‖c₁ v.1‖} =>
    ‖c₁ w.1.1‖ :=
  continuous_norm.comp continuous_conf_c₁

lemma continuous_confEtaFun : Continuous confEtaFun := by
  rw [show confEtaFun = fun w : {v : unitSphere 3 // ‖c₂ v.1‖ ≤ ‖c₁ v.1‖} =>
      (c₁ w.1.1 / ((‖c₁ w.1.1‖ : ℝ) : ℂ)) ^ 2 from rfl]
  refine Continuous.pow (Continuous.div ?_ ?_ ?_) 2
  · exact continuous_conf_c₁
  · exact Complex.continuous_ofReal.comp continuous_conf_norm₁
  · intro w
    have hz : ‖c₁ w.1.1‖ ≠ 0 :=
      norm_ne_zero_iff.mpr (ne_zero_of_norm_le w.2 (sq_norm_eq_one_comm w.1))
    simpa using hz

lemma confEta_norm (w : {v : unitSphere 3 // ‖c₂ v.1‖ ≤ ‖c₁ v.1‖}) : ‖confEtaFun w‖ = 1 := by
  rw [show confEtaFun w = (c₁ w.1.1 / ((‖c₁ w.1.1‖ : ℝ) : ℂ)) ^ 2 from rfl]
  exact norm_sq_div_self _ (ne_zero_of_norm_le w.2 (sq_norm_eq_one_comm w.1))

lemma continuous_confDiskFun : Continuous confDiskFun := by
  rw [show confDiskFun = fun w : {v : unitSphere 3 // ‖c₂ v.1‖ ≤ ‖c₁ v.1‖} =>
      (Real.sqrt 2 : ℂ) * c₂ w.1.1 * c₁ w.1.1 / (((‖c₁ w.1.1‖ : ℝ)) : ℂ) from rfl]
  refine Continuous.div ?_ ?_ ?_
  · exact (continuous_const.mul continuous_conf_c₂).mul continuous_conf_c₁
  · exact Complex.continuous_ofReal.comp continuous_conf_norm₁
  · intro w
    have hz : ‖c₁ w.1.1‖ ≠ 0 :=
      norm_ne_zero_iff.mpr (ne_zero_of_norm_le w.2 (sq_norm_eq_one_comm w.1))
    simpa using hz

lemma confDisk_mem (w : {v : unitSphere 3 // ‖c₂ v.1‖ ≤ ‖c₁ v.1‖}) :
    confDiskFun w ∈ Metric.closedBall (0 : ℂ) 1 := by
  rw [Metric.mem_closedBall, dist_eq_norm, sub_zero]
  exact norm_sqrt_two_mul_div_le _ _
    (ne_zero_of_norm_le w.2 (sq_norm_eq_one_comm w.1))
    (norm_le_inv_sqrt_two w.2 (sq_norm_eq_one_comm w.1))

/-- The configuration point map is continuous. -/
lemma continuous_confPt : Continuous confPt := by
  have h2 : Continuous fun w : {v : unitSphere 3 // ‖c₂ v.1‖ ≤ ‖c₁ v.1‖} => (confPt w).2 := by
    have hc : Continuous fun w => circOf' (toCircle (confEtaFun w) (confEta_norm w)) :=
      continuous_circOf'.comp (Continuous.subtype_mk continuous_confEtaFun
        (fun w => mem_unitSphere_of_norm (confEta_norm w)))
    exact hc.congr (fun w => (circOf_eq _ _).symm)
  have h1 : Continuous fun w : {v : unitSphere 3 // ‖c₂ v.1‖ ≤ ‖c₁ v.1‖} => (confPt w).1 := by
    have hc : Continuous fun w => (⟨confDiskFun w, confDisk_mem w⟩ : Metric.closedBall (0 : ℂ) 1) :=
      Continuous.subtype_mk continuous_confDiskFun confDisk_mem
    exact hc.congr (fun w => (Subtype.ext (by rw [confPt_fst]; rfl)).symm)
  exact (h1.prodMk h2).congr (fun w => rfl)

end Conf

/-- On the cap hemisphere `phiCap` is the composite of `capPt` with the quotient map. -/
lemma continuousOn_phiCap : ContinuousOn phiCap capHemi := by
  rw [show capHemi = {v : unitSphere 3 | ‖c₁ v.1‖ ≤ ‖c₂ v.1‖} from rfl,
    continuousOn_iff_continuous_domRestrict]
  have hfun : ({v : unitSphere 3 | ‖c₁ v.1‖ ≤ ‖c₂ v.1‖} : Set (unitSphere 3)).domRestrict phiCap
      = fun w => Quotient.mk'' (Sum.inl (capPt w)) := by
    funext w
    rw [Set.domRestrict_apply, phiCap,
      dif_pos (show ‖c₁ (↑↑w)‖ ≤ ‖c₂ (↑↑w)‖ from w.2)]
    rfl
  rw [hfun]
  exact continuous_quotient_mk'.comp (continuous_inl.comp continuous_capPt)

/-- On the configuration hemisphere `phiConf` is the composite of `confPt` with the quotient map. -/
lemma continuousOn_phiConf : ContinuousOn phiConf confHemi := by
  rw [show confHemi = {v : unitSphere 3 | ‖c₂ v.1‖ ≤ ‖c₁ v.1‖} from rfl,
    continuousOn_iff_continuous_domRestrict]
  have hfun : ({v : unitSphere 3 | ‖c₂ v.1‖ ≤ ‖c₁ v.1‖} : Set (unitSphere 3)).domRestrict phiConf
      = fun w => Quotient.mk'' (Sum.inr (confPt w)) := by
    funext w
    rw [Set.domRestrict_apply, phiConf,
      dif_pos (show ‖c₂ (↑↑w)‖ ≤ ‖c₁ (↑↑w)‖ from w.2)]
    rfl
  rw [hfun]
  exact continuous_quotient_mk'.comp (continuous_inr.comp continuous_confPt)

/-- **The glueing map `phi : S³ → LensSpace` is continuous.** -/
theorem continuous_phi : Continuous phi := by
  classical
  have hfun : phi = fun v : unitSphere 3 =>
      if h : ‖c₁ v.1‖ ≤ ‖c₂ v.1‖ then phiCap v else phiConf v := by
    funext v
    rw [phi]
    by_cases h : ‖c₁ v.1‖ ≤ ‖c₂ v.1‖
    · rw [dif_pos h, dif_pos h, phiCap, dif_pos h]
    · rw [dif_neg h, dif_neg h, phiConf, dif_pos (le_of_not_ge h)]
  rw [hfun]
  refine continuous_if ?_ ?_ ?_
  · intro v hv
    rw [frontier_eq_closure_inter_closure] at hv
    have hp : ‖c₁ v.1‖ ≤ ‖c₂ v.1‖ := by
      have h1 : v ∈ capHemi := by
        have : v ∈ closure capHemi := hv.1
        rwa [isClosed_capHemi.closure_eq] at this
      exact h1
    have hq : ‖c₂ v.1‖ ≤ ‖c₁ v.1‖ := by
      have h1 : v ∈ closure (capHemiᶜ) := hv.2
      have hsub : capHemiᶜ ⊆ confHemi := by
        intro u hu
        simp only [capHemi, Set.mem_compl_iff, Set.mem_setOf_eq] at hu
        simp only [confHemi, Set.mem_setOf_eq]
        exact le_of_lt (lt_of_not_ge hu)
      have h2 : closure (capHemiᶜ) ⊆ confHemi := by
        rw [← isClosed_confHemi.closure_eq]
        exact closure_mono hsub
      exact h2 h1
    exact phiCap_eq_phiConf v (le_antisymm hp hq)
  · refine continuousOn_phiCap.mono ?_
    have : {v : unitSphere 3 | ‖c₁ v.1‖ ≤ ‖c₂ v.1‖} = capHemi := rfl
    rw [this, isClosed_capHemi.closure_eq]
  · refine continuousOn_phiConf.mono ?_
    have hsub : {v : unitSphere 3 | ¬(‖c₁ v.1‖ ≤ ‖c₂ v.1‖)} ⊆ confHemi := by
      intro u hu
      simp only [Set.mem_setOf_eq, not_le] at hu
      simp only [confHemi, Set.mem_setOf_eq]
      exact le_of_lt hu
    calc closure {v : unitSphere 3 | ¬(‖c₁ v.1‖ ≤ ‖c₂ v.1‖)}
        ⊆ closure confHemi := closure_mono hsub
      _ = confHemi := isClosed_confHemi.closure_eq

end

end Work.Drive
