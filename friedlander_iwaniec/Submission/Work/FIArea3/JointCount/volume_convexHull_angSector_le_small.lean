import Mathlib
import Submission.Work.FIArea3.JointCount.angSector
import Submission.Work.FIArea3.JointCount.polarBand_volume
import Submission.Work.FIArea3.JointCount.angSector_geom_defs
import Submission.Work.FIArea3.JointCount.volume_convexHull_triangle
import Submission.Work.FIArea3.JointCount.volume_angSector_Icc
import Submission.Work.FIArea3.JointCount.crs_cone_iff
import Submission.Work.FIArea3.JointCount.angSector_proj_ge

namespace Work.FIArea3.JointCount

open MeasureTheory Set
open scoped ENNReal

noncomputable section

attribute [local instance] Classical.propDecidable

/-! ## Linear functionals -/

/-- Projection onto the direction `cs m`: `z ↦ z.re * cos m + z.im * sin m`. -/
def projL (m : ℝ) : ℂ →ₗ[ℝ] ℝ where
  toFun z := z.re * Real.cos m + z.im * Real.sin m
  map_add' x y := by simp only [Complex.add_re, Complex.add_im]; ring
  map_smul' r z := by
    simp only [Complex.smul_re, Complex.smul_im, smul_eq_mul, RingHom.id_apply]; ring

/-- The functional `z ↦ crs u z = u.re * z.im - u.im * z.re`. -/
def crsL (u : ℂ) : ℂ →ₗ[ℝ] ℝ where
  toFun z := u.re * z.im - u.im * z.re
  map_add' x y := by simp only [Complex.add_re, Complex.add_im]; ring
  map_smul' r z := by
    simp only [Complex.smul_re, Complex.smul_im, smul_eq_mul, RingHom.id_apply]; ring

/-- The functional `z ↦ crs z v = z.re * v.im - z.im * v.re`. -/
def crsR (v : ℂ) : ℂ →ₗ[ℝ] ℝ where
  toFun z := z.re * v.im - z.im * v.re
  map_add' x y := by simp only [Complex.add_re, Complex.add_im]; ring
  map_smul' r z := by
    simp only [Complex.smul_re, Complex.smul_im, smul_eq_mul, RingHom.id_apply]; ring

@[simp] lemma projL_apply (m : ℝ) (z : ℂ) :
    projL m z = z.re * Real.cos m + z.im * Real.sin m := rfl

@[simp] lemma crsL_apply (u z : ℂ) : crsL u z = u.re * z.im - u.im * z.re := rfl

@[simp] lemma crsR_apply (v z : ℂ) : crsR v z = z.re * v.im - z.im * v.re := rfl

lemma crs_eq_crsL (u z : ℂ) : crs u z = crsL u z := rfl
lemma crs_eq_crsR (v z : ℂ) : crs z v = crsR v z := rfl

/-! ## Evaluations on `cs` -/

lemma projL_smul_cs (r φ m : ℝ) : projL m (r • cs φ) = r * Real.cos (φ - m) := by
  rw [projL_apply, Complex.smul_re, Complex.smul_im, cs_re, cs_im, smul_eq_mul, smul_eq_mul,
    Real.cos_sub]
  ring

lemma crs_cs_cs (α β : ℝ) : crs (cs α) (cs β) = Real.sin (β - α) := by
  rw [crs_apply, cs_re, cs_im, cs_re, cs_im,
    show Real.cos α * Real.sin β - Real.sin α * Real.cos β
      = Real.sin β * Real.cos α - Real.cos β * Real.sin α by ring,
    ← Real.sin_sub]

lemma crsL_cs_smul (u : ℂ) (r : ℝ) (z : ℂ) : crsL u (r • z) = r * crsL u z := by
  rw [crsL_apply, crsL_apply, Complex.smul_re, Complex.smul_im, smul_eq_mul, smul_eq_mul]; ring

lemma crsR_cs_smul (v : ℂ) (r : ℝ) (z : ℂ) : crsR v (r • z) = r * crsR v z := by
  rw [crsR_apply, crsR_apply, Complex.smul_re, Complex.smul_im, smul_eq_mul, smul_eq_mul]; ring

lemma crsL_cs_cs_self (α : ℝ) : crsL (cs α) (cs α) = 0 := by
  rw [crsL_apply, cs_re, cs_im]; ring

lemma crsR_cs_cs_self (β : ℝ) : crsR (cs β) (cs β) = 0 := by
  rw [crsR_apply, cs_re, cs_im]; ring

lemma crs_cs_smul_cs_self (α a : ℝ) : crs (cs α) (a • cs α) = 0 := by
  rw [crs_eq_crsL, crsL_cs_smul, crsL_cs_cs_self, mul_zero]

lemma crs_smul_cs_cs_self (β a : ℝ) : crs (a • cs β) (cs β) = 0 := by
  rw [crs_eq_crsR, crsR_cs_smul, crsR_cs_cs_self, mul_zero]

lemma crs_cs_smul_cs (α β a : ℝ) : crs (cs α) (a • cs β) = a * Real.sin (β - α) := by
  rw [crs_eq_crsL, crsL_cs_smul, ← crs_eq_crsL (cs α) (cs β), crs_cs_cs]

lemma crs_smul_cs_cs (α β a : ℝ) : crs (a • cs α) (cs β) = a * Real.sin (β - α) := by
  rw [crs_eq_crsR, crsR_cs_smul, ← crs_eq_crsR (cs β) (cs α), crs_cs_cs]

lemma sin_sub_nonneg (α β : ℝ) (h : α ≤ β) (hℓ : β - α ≤ Real.pi) :
    0 ≤ Real.sin (β - α) := Real.sin_nonneg_of_nonneg_of_le_pi (by linarith) hℓ

/-! ## The cone, half-plane and closed ball -/

/-- The closed cone of directions from `cs α` to `cs β`, described by the two half-planes
`crs (cs α) z ≥ 0`, `crs z (cs β) ≥ 0`. -/
def coneC (α β : ℝ) : Set ℂ :=
  (crsL (cs α)) ⁻¹' Set.Ici (0 : ℝ) ∩ (crsR (cs β)) ⁻¹' Set.Ici (0 : ℝ)

@[simp] lemma mem_coneC {α β : ℝ} {z : ℂ} :
    z ∈ coneC α β ↔ 0 ≤ crs (cs α) z ∧ 0 ≤ crs z (cs β) := by
  rw [coneC, Set.mem_inter_iff, Set.mem_preimage, Set.mem_preimage, Set.mem_Ici, Set.mem_Ici,
    crs_eq_crsL, crs_eq_crsR]

lemma convex_coneC (α β : ℝ) : Convex ℝ (coneC α β) :=
  ((convex_Ici (0 : ℝ)).linear_preimage (crsL (cs α))).inter
    ((convex_Ici (0 : ℝ)).linear_preimage (crsR (cs β)))

/-- The half-plane `c ≤ projL m z`. -/
def halfH (c m : ℝ) : Set ℂ := (projL m) ⁻¹' Set.Ici c

@[simp] lemma mem_halfH {c m : ℝ} {z : ℂ} : z ∈ halfH c m ↔ c ≤ projL m z := Iff.rfl

lemma convex_halfH (c m : ℝ) : Convex ℝ (halfH c m) :=
  (convex_Ici c).linear_preimage (projL m)

/-- The closed ball of radius `b`. -/
def ballB (b : ℝ) : Set ℂ := Metric.closedBall (0 : ℂ) b

@[simp] lemma mem_ballB {b : ℝ} {z : ℂ} : z ∈ ballB b ↔ ‖z‖ ≤ b := by
  rw [ballB, Metric.mem_closedBall, dist_zero_right]

lemma convex_ballB (b : ℝ) : Convex ℝ (ballB b) := by
  rw [ballB]; exact convex_closedBall _ _

/-! ## Two null sets -/

/-- The kernel of a nonzero real-linear functional `ℂ → ℝ` is null. -/
lemma volume_ker_eq_zero {f : ℂ →ₗ[ℝ] ℝ} (hf : f ≠ 0) :
    volume (LinearMap.ker f : Set ℂ) = 0 := by
  refine MeasureTheory.Measure.addHaar_submodule volume _ ?_
  intro h
  apply hf
  refine LinearMap.ext fun z => ?_
  have hz : z ∈ LinearMap.ker f := by rw [h]; exact Submodule.mem_top
  simpa using (LinearMap.mem_ker.mp hz)

/-- A level set of a nonzero real-linear functional `ℂ → ℝ` is null. -/
lemma volume_levelSet_eq_zero {f : ℂ →ₗ[ℝ] ℝ} (hf : f ≠ 0) (c : ℝ) :
    volume {z : ℂ | f z = c} = 0 := by
  obtain ⟨z, hz⟩ : ∃ z, f z ≠ 0 := by
    by_contra h
    simp only [not_exists, not_not] at h
    exact hf (LinearMap.ext fun w => by simpa using h w)
  set z₀ : ℂ := (c / f z) • z with hz₀
  have hz₀f : f z₀ = c := by
    rw [hz₀, map_smul, smul_eq_mul, div_mul_cancel₀ _ hz]
  have hset : {w : ℂ | f w = c} = (fun k => z₀ + k) '' (LinearMap.ker f : Set ℂ) := by
    ext w; constructor
    · intro hw
      exact ⟨w - z₀, LinearMap.mem_ker.mpr (by rw [map_sub, hw, hz₀f, sub_self]), by ring⟩
    · rintro ⟨k, hk, rfl⟩
      have hk0 : f k = 0 := LinearMap.mem_ker.mp hk
      change f (z₀ + k) = c
      rw [map_add, hk0, hz₀f, add_zero]
  have hinj : Function.Injective (fun k : ℂ => z₀ + k) := add_right_injective z₀
  rw [hset]
  have h1 := (MeasureTheory.measure_preimage_add volume z₀
      ((fun k => z₀ + k) '' (LinearMap.ker f : Set ℂ))).symm
  rw [Set.preimage_image_eq _ hinj] at h1
  rw [h1]
  exact volume_ker_eq_zero hf

/-- The ray in direction `cs α` is null. -/
lemma volume_ray_eq_zero (α : ℝ) :
    volume {z : ℂ | ∃ t : ℝ, 0 ≤ t ∧ z = t • cs α} = 0 := by
  have hne : crsR (cs α) ≠ 0 := by
    intro h
    have hval : crsR (cs α) (cs (α + Real.pi / 2)) = -1 := by
      rw [crsR_apply, cs_re, cs_im, cs_re, cs_im, Real.cos_add_pi_div_two, Real.sin_add_pi_div_two]
      nlinarith [Real.sin_sq_add_cos_sq α]
    rw [h] at hval
    simp at hval
  refine measure_mono_null ?_ (volume_ker_eq_zero hne)
  rintro z ⟨t, ht, rfl⟩
  exact LinearMap.mem_ker.mpr (by rw [crsR_cs_smul, crsR_cs_cs_self, mul_zero])

/-! ## The three regions entering the estimate -/

/-- The triangle `conv {0, a • cs α, a • cs β}`. -/
def hullT (a α β : ℝ) : Set ℂ := convexHull ℝ ({(0 : ℂ), a • cs α, a • cs β} : Set ℂ)

/-- The region `coneC α β ∩ {a cos(Δ/2) ≤ projL m} ∩ {‖·‖ ≤ b}`, `m = (α+β)/2`. -/
def hullR (a b α β : ℝ) : Set ℂ :=
  coneC α β ∩ halfH (a * Real.cos ((β - α) / 2)) ((α + β) / 2) ∩ ballB b

/-- The closed angular sector of radius `b`. -/
def secClosed (b α β : ℝ) : Set ℂ := angSector 0 b (Set.Icc α β)

/-- Area of the inner triangle `conv {0, a cs α, a cs β}`: `(a²/2) sin(β - α)`. -/
lemma volume_hullT (a α β : ℝ) (ha : 0 ≤ a) (hsin : 0 ≤ Real.sin (β - α)) :
    volume (hullT a α β) = ENNReal.ofReal (a ^ 2 / 2 * Real.sin (β - α)) := by
  have htri : (volume (hullT a α β)).toReal = |a ^ 2 * Real.sin (β - α)| / 2 := by
    have h := volume_convexHull_triangle (a • cs α) (a • cs β)
    have hdet : (a • cs α).re * (a • cs β).im - (a • cs α).im * (a • cs β).re
        = a ^ 2 * Real.sin (β - α) := by
      simp only [Complex.smul_re, Complex.smul_im, cs_re, cs_im, smul_eq_mul, Real.sin_sub]
      ring
    unfold hullT
    rw [hdet] at h
    exact h
  have hbdd : Bornology.IsBounded (hullT a α β) := by
    have hsub : hullT a α β ⊆ Metric.closedBall (0 : ℂ) a := by
      unfold hullT
      refine convexHull_min ?_ (convex_closedBall (0 : ℂ) a)
      intro w hw
      rw [Metric.mem_closedBall, dist_zero_right]
      rcases hw with rfl | rfl | rfl
      · rw [norm_zero]; exact ha
      · rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg ha, norm_cs, mul_one]
      · rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg ha, norm_cs, mul_one]
    exact Metric.isBounded_closedBall.subset hsub
  have hfin : volume (hullT a α β) ≠ ⊤ := hbdd.measure_lt_top.ne
  rw [← ENNReal.ofReal_toReal hfin, htri, abs_of_nonneg (mul_nonneg (sq_nonneg a) hsin)]
  congr 1
  ring

theorem volume_convexHull_angSector_le_small (a b α β : ℝ) (ha : 0 < a) (hab : a ≤ b)
    (hα : -Real.pi ≤ α) (hβ : β ≤ Real.pi) (hαβ : α ≤ β) (hℓ : β - α ≤ Real.pi) :
    (MeasureTheory.volume (convexHull ℝ (angSector a b (Set.Ioc α β)))).toReal
      ≤ b ^ 2 / 2 * (β - α) - a ^ 2 / 2 * Real.sin (β - α) := by
  have hb0 : 0 ≤ b := le_trans ha.le hab
  rcases lt_or_eq_of_le hαβ with hlt | heq
  · have hΔ0 : 0 ≤ β - α := sub_nonneg.mpr hαβ
    have hsinΔ0 : 0 ≤ Real.sin (β - α) := sin_sub_nonneg α β hαβ hℓ
    set γ : ℝ := (β - α) / 2 with hγ
    set m : ℝ := (α + β) / 2 with hm
    have hγle : γ ≤ Real.pi / 2 := by rw [hγ]; linarith
    have hcosγ0 : 0 ≤ Real.cos γ :=
      Real.cos_nonneg_of_neg_pi_div_two_le_of_le (by linarith) hγle
    have hαm : α - m = -γ := by rw [hγ, hm]; ring
    have hβm : β - m = γ := by rw [hγ, hm]; ring
    set c : ℝ := a * Real.cos γ with hc
    have hc0 : 0 ≤ c := by rw [hc]; exact mul_nonneg ha.le hcosγ0
    have heq2 : hullR a b α β = coneC α β ∩ halfH c m ∩ ballB b := by
      simp only [hullR, hγ, hm, hc]
    have hS_C : angSector a b (Set.Ioc α β) ⊆ coneC α β := by
      intro z hz
      have hz0 : z ≠ 0 := by
        intro h
        rw [h] at hz
        have hlt0 : a < ‖(0 : ℂ)‖ := hz.1
        rw [norm_zero] at hlt0
        linarith
      rw [mem_coneC]
      exact (crs_cone_iff α β hα hβ hlt hℓ z hz0).mpr (Or.inl (Set.Ioc_subset_Icc_self hz.2.2))
    have hS_H : angSector a b (Set.Ioc α β) ⊆ halfH c m := by
      intro z hz
      rw [hc, hγ, hm, mem_halfH, projL_apply]
      exact angSector_proj_ge a b α β ha hab hαβ hℓ z hz
    have hS_B : angSector a b (Set.Ioc α β) ⊆ ballB b := by
      intro z hz; rw [mem_ballB]; exact hz.2.1
    have hvol_conv_le :
        volume (convexHull ℝ (angSector a b (Set.Ioc α β))) ≤ volume (hullR a b α β) := by
      have h1 := convexHull_min hS_C (convex_coneC α β)
      have h2 := convexHull_min hS_H (convex_halfH c m)
      have h3 := convexHull_min hS_B (convex_ballB b)
      rw [heq2]
      apply measure_mono
      intro z hz
      exact ⟨⟨h1 hz, h2 hz⟩, h3 hz⟩
    have hT_C : hullT a α β ⊆ coneC α β := by
      unfold hullT
      refine convexHull_min ?_ (convex_coneC α β)
      intro z hz
      rw [mem_coneC]
      rcases hz with rfl | rfl | rfl
      · constructor <;> simp [crs_apply]
      · constructor
        · rw [crs_cs_smul_cs_self]
        · rw [crs_smul_cs_cs]; exact mul_nonneg ha.le hsinΔ0
      · constructor
        · rw [crs_cs_smul_cs]; exact mul_nonneg ha.le hsinΔ0
        · rw [crs_smul_cs_cs_self]
    have hT_B : hullT a α β ⊆ ballB b := by
      unfold hullT
      refine convexHull_min ?_ (convex_ballB b)
      intro z hz
      rw [mem_ballB]
      rcases hz with rfl | rfl | rfl
      · rw [norm_zero]; exact hb0
      · rw [norm_smul, Real.norm_eq_abs, abs_of_pos ha, norm_cs, mul_one]; exact hab
      · rw [norm_smul, Real.norm_eq_abs, abs_of_pos ha, norm_cs, mul_one]; exact hab
    have hproj_0 : projL m (0 : ℂ) = 0 := by
      rw [projL_apply]; simp
    have hproj_α : projL m (a • cs α) = c := by
      have h1 : projL m (a • cs α) = a * Real.cos γ := by
        rw [projL_smul_cs, hαm, Real.cos_neg]
      exact h1.trans hc.symm
    have hproj_β : projL m (a • cs β) = c := by
      have h1 : projL m (a • cs β) = a * Real.cos γ := by
        rw [projL_smul_cs, hβm]
      exact h1.trans hc.symm
    have hT_proj : hullT a α β ⊆ (projL m) ⁻¹' Set.Iic c := by
      unfold hullT
      refine convexHull_min ?_ ((convex_Iic c).linear_preimage (projL m))
      intro z hz
      rw [Set.mem_preimage, Set.mem_Iic]
      rcases hz with rfl | rfl | rfl
      · rw [hproj_0]; exact hc0
      · exact le_of_eq hproj_α
      · exact le_of_eq hproj_β
    have hRT_le : ∀ z ∈ coneC α β ∩ halfH c m ∩ ballB b, z ∈ hullT a α β → projL m z = c := by
      intro z hz hzT
      have h1 : c ≤ projL m z := mem_halfH.mp hz.1.2
      have h2 : projL m z ≤ c := Set.mem_Iic.mp (hT_proj hzT)
      exact le_antisymm h2 h1
    have hproj_ne : projL m ≠ 0 := by
      intro h
      have h1 : projL m (1 : ℂ) = 0 := by rw [h]; simp
      have h2 : projL m Complex.I = 0 := by rw [h]; simp
      rw [projL_apply] at h1 h2
      simp only [Complex.one_re, Complex.one_im, mul_one, Complex.I_re, Complex.I_im, mul_zero,
        add_zero, zero_mul] at h1 h2
      nlinarith [Real.sin_sq_add_cos_sq m]
    have hRT_null : volume (coneC α β ∩ halfH c m ∩ ballB b ∩ hullT a α β) = 0 := by
      refine measure_mono_null ?_ (volume_levelSet_eq_zero hproj_ne c)
      intro z hz
      exact hRT_le z hz.1 hz.2
    have hR2_meas : MeasurableSet (coneC α β ∩ halfH c m ∩ ballB b) := by
      have h1 : IsClosed (coneC α β) := by
        rw [coneC]
        exact (isClosed_Ici.preimage (crsL (cs α)).continuous_of_finiteDimensional).inter
          (isClosed_Ici.preimage (crsR (cs β)).continuous_of_finiteDimensional)
      have h2 : IsClosed (halfH c m) :=
        isClosed_Ici.preimage (projL m).continuous_of_finiteDimensional
      have h3 : IsClosed (ballB b) := by rw [ballB]; exact Metric.isClosed_closedBall
      exact ((h1.inter h2).inter h3).measurableSet
    have hvol_T := volume_hullT a α β ha.le hsinΔ0
    have hvol_sec : volume (secClosed b α β) = ENNReal.ofReal (b ^ 2 / 2 * (β - α)) := by
      have h := volume_angSector_Icc 0 b α β le_rfl hb0 hα hβ hαβ
      unfold secClosed
      rw [h]
      congr 1
      ring
    have hT_meas : MeasurableSet (hullT a α β) := by
      have hc : IsCompact (hullT a α β) := by
        unfold hullT
        exact (Set.Finite.insert (0 : ℂ)
          (Set.Finite.insert (a • cs α) (Set.finite_singleton (a • cs β)))).isCompact_convexHull ℝ
      exact hc.isClosed.measurableSet
    have hvol_R2T : volume ((coneC α β ∩ halfH c m ∩ ballB b) ∪ hullT a α β)
        = volume (coneC α β ∩ halfH c m ∩ ballB b) + volume (hullT a α β) :=
      measure_union₀ (μ := volume) (s := coneC α β ∩ halfH c m ∩ ballB b) (t := hullT a α β)
        hT_meas.nullMeasurableSet hRT_null
    have h_aux : ∀ z, z ∈ coneC α β → ‖z‖ ≤ b →
        z ∈ secClosed b α β ∪ ({z : ℂ | ∃ t : ℝ, 0 ≤ t ∧ z = t • cs α} ∪ {0}) := by
      intro z hzC hzb
      by_cases hz0 : z = 0
      · exact Or.inr (Or.inr hz0)
      · rcases (crs_cone_iff α β hα hβ hlt hℓ z hz0).mp (mem_coneC.mp hzC) with harg | hray
        · refine Or.inl ?_
          unfold secClosed
          show 0 < ‖z‖ ∧ ‖z‖ ≤ b ∧ Complex.arg z ∈ Set.Icc α β
          exact ⟨norm_pos_iff.mpr hz0, hzb, harg⟩
        · exact Or.inr (Or.inl hray)
    have hN_null : volume ({z : ℂ | ∃ t : ℝ, 0 ≤ t ∧ z = t • cs α} ∪ {0}) = 0 :=
      measure_union_null (volume_ray_eq_zero α) (measure_singleton 0)
    have hR2T_sub : (coneC α β ∩ halfH c m ∩ ballB b) ∪ hullT a α β ⊆
        secClosed b α β ∪ ({z : ℂ | ∃ t : ℝ, 0 ≤ t ∧ z = t • cs α} ∪ {0}) := by
      intro z hz
      rcases hz with hz | hz
      · exact h_aux z hz.1.1 (mem_ballB.mp hz.2)
      · exact h_aux z (hT_C hz) (mem_ballB.mp (hT_B hz))
    have hvol_RT_le : volume ((coneC α β ∩ halfH c m ∩ ballB b) ∪ hullT a α β)
        ≤ volume (secClosed b α β) := by
      calc volume ((coneC α β ∩ halfH c m ∩ ballB b) ∪ hullT a α β)
          ≤ volume (secClosed b α β ∪ ({z : ℂ | ∃ t : ℝ, 0 ≤ t ∧ z = t • cs α} ∪ {0})) :=
            measure_mono hR2T_sub
        _ ≤ volume (secClosed b α β)
              + volume ({z : ℂ | ∃ t : ℝ, 0 ≤ t ∧ z = t • cs α} ∪ {0}) :=
            measure_union_le _ _
        _ = volume (secClosed b α β) + 0 := by rw [hN_null]
        _ = volume (secClosed b α β) := add_zero _
    have hXY : a ^ 2 / 2 * Real.sin (β - α) ≤ b ^ 2 / 2 * (β - α) := by
      have hsin_le : Real.sin (β - α) ≤ β - α := Real.sin_le hΔ0
      have ha2 : a ^ 2 ≤ b ^ 2 := by nlinarith [ha.le, hab]
      have h1 : a ^ 2 / 2 * Real.sin (β - α) ≤ a ^ 2 / 2 * (β - α) :=
        mul_le_mul_of_nonneg_left hsin_le (by positivity)
      have h2 : a ^ 2 / 2 * (β - α) ≤ b ^ 2 / 2 * (β - α) :=
        mul_le_mul_of_nonneg_right (by linarith) hΔ0
      linarith
    have hmain : volume (convexHull ℝ (angSector a b (Set.Ioc α β)))
        ≤ ENNReal.ofReal (b ^ 2 / 2 * (β - α) - a ^ 2 / 2 * Real.sin (β - α)) := by
      have hstep : volume (coneC α β ∩ halfH c m ∩ ballB b)
          ≤ ENNReal.ofReal (b ^ 2 / 2 * (β - α))
              - ENNReal.ofReal (a ^ 2 / 2 * Real.sin (β - α)) := by
        refine (ENNReal.le_sub_iff_add_le_right ENNReal.ofReal_ne_top
          (ENNReal.ofReal_le_ofReal hXY)).mpr ?_
        have hRT : volume (coneC α β ∩ halfH c m ∩ ballB b) + volume (hullT a α β)
            ≤ volume (secClosed b α β) := by rw [← hvol_R2T]; exact hvol_RT_le
        rw [hvol_T, hvol_sec] at hRT
        exact hRT
      calc volume (convexHull ℝ (angSector a b (Set.Ioc α β)))
          ≤ volume (hullR a b α β) := hvol_conv_le
        _ = volume (coneC α β ∩ halfH c m ∩ ballB b) := congrArg volume heq2
        _ ≤ ENNReal.ofReal (b ^ 2 / 2 * (β - α))
              - ENNReal.ofReal (a ^ 2 / 2 * Real.sin (β - α)) := hstep
        _ = ENNReal.ofReal (b ^ 2 / 2 * (β - α) - a ^ 2 / 2 * Real.sin (β - α)) :=
              (ENNReal.ofReal_sub _ (mul_nonneg (by positivity) hsinΔ0)).symm
    have htoReal := ENNReal.toReal_mono ENNReal.ofReal_ne_top hmain
    rw [ENNReal.toReal_ofReal (sub_nonneg.mpr hXY)] at htoReal
    exact htoReal
  · rw [heq, Set.Ioc_self]
    have hnil : angSector a b (∅ : Set ℝ) = ∅ := by ext z; simp [angSector]
    rw [hnil, convexHull_empty, MeasureTheory.measure_empty]
    simp

end

end Work.FIArea3.JointCount
