import Mathlib
import Submission.Work.Whitney.RankTwo.RepDefs

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option maxHeartbeats 1600000

namespace Work.Whitney.RankTwo

open Work.Thom Work.Cohomology Work.Thom.Orientation
open CategoryTheory AlgebraicTopology CategoryTheory.Limits
open scoped Simplicial

noncomputable section

variable (Y : Type) [TopologicalSpace Y]

/-- Port bridge (Lean v4.35): naturality of `TopCat.toSSetObjEquivOld` in the space. -/
private theorem toSSetObjEquivOld_naturality_space {A B : TopCat} (f : A ⟶ B) (n : ℕ)
    (σ : (TopCat.toSSet.obj A).obj (Opposite.op (SimplexCategory.mk n))) :
    (TopCat.toSSetObjEquivOld B (Opposite.op (SimplexCategory.mk n)))
        ((TopCat.toSSet.map f).app (Opposite.op (SimplexCategory.mk n)) σ)
      = (ConcreteCategory.hom f).comp
          ((TopCat.toSSetObjEquivOld A (Opposite.op (SimplexCategory.mk n))) σ) := rfl

theorem tcmF_apply (x : X Y) : tcmF Y 1 1 x = (x.1, tcmSumLin 1 1 x.2) := rfl

/-- The arc of the hexagon is the pushforward of the corresponding arc simplex of `X`. -/
theorem tcmF_arcSimp (y : Y) (k : ℕ) :
    (TopCat.toSSet.map (TopCat.ofHom (tcmF Y 1 1))).app (Opposite.op ⦋1⦌) (arcSimp Y y k)
      = arcUSimp Y y k := by
  apply (eR2 Y 1).injective
  rw [toSSetObjEquivOld_naturality_space, sEquiv_arcSimp, eR2_arcUSimp]
  apply ContinuousMap.ext
  intro q
  rw [ContinuousMap.comp_apply]
  change tcmF Y 1 1 (arcC Y y k q) = arcUC Y y k q
  rw [tcmF_apply, arcC_apply, ContinuousLinearEquiv.apply_symm_apply]
  rfl

/-- The arc simplex of the rank-two sphere bundle pushes forward to the arc of `Y × ℝ²`. -/
theorem incl_arcSSimp (y : Y) (k : ℕ) :
    (TopCat.toSSet.map (subtypeIncl (TopCat.of (R2 Y)) (Sph Y 2))).app (Opposite.op ⦋1⦌)
        (arcSSimp Y y k) = arcUSimp Y y k := by
  apply (eR2 Y 1).injective
  rw [toSSetObjEquivOld_naturality_space, eSph2_arcSSimp, eR2_arcUSimp]
  apply ContinuousMap.ext
  intro q
  rw [ContinuousMap.comp_apply]
  change (↑(arcSC Y y k q) : R2 Y) = arcUC Y y k q
  rw [arcSC_apply, arcUC_apply]

/-- The lower arcs of the hexagon lie in the lower band. -/
theorem arc_lower_geom (y : Y) {k : ℕ} (hk : k = 3 ∨ k = 4 ∨ k = 5) :
    ∀ q : stdSimplex ℝ (Fin 2),
      ((((eSph2 Y 1) (arcSSimp Y y k)) q : ↥(Sph Y 2)) : R2 Y).2 ∈ mLower 1 := by
  intro q
  rw [eSph2_arcSSimp, arcSC_apply]
  show u2 (arcAngC k q) ∈ mLower 1
  have hb := arcC_angle_bounds k q
  constructor
  · exact norm_u2 _
  · rw [show (Fin.last 1 : Fin 2) = (1 : Fin 2) from rfl, u2_apply_one]
    have hπ : (k : ℝ) * Real.pi / 3 ≤ arcAngC k q := hb.1
    have hπ' : arcAngC k q ≤ ((k : ℝ) + 1) * Real.pi / 3 := hb.2
    rcases hk with rfl | rfl | rfl
    · have h1 : Real.pi ≤ arcAngC 3 q := by
        have := hπ; norm_num at this ⊢; linarith
      have h2 : arcAngC 3 q ≤ 2 * Real.pi := by
        have := hπ'; norm_num at this ⊢; linarith
      have h3 := Real.sin_nonpos_of_nonpos_of_neg_pi_le (x := arcAngC 3 q - 2 * Real.pi)
        (by linarith) (by linarith)
      rw [Real.sin_sub_two_pi] at h3
      linarith
    · have h1 : Real.pi ≤ arcAngC 4 q := by
        have := hπ; norm_num at this ⊢; linarith
      have h2 : arcAngC 4 q ≤ 2 * Real.pi := by
        have := hπ'; norm_num at this ⊢; linarith
      have h3 := Real.sin_nonpos_of_nonpos_of_neg_pi_le (x := arcAngC 4 q - 2 * Real.pi)
        (by linarith) (by linarith)
      rw [Real.sin_sub_two_pi] at h3
      linarith
    · have h1 : Real.pi ≤ arcAngC 5 q := by
        have := hπ; norm_num at this ⊢; linarith
      have h2 : arcAngC 5 q ≤ 2 * Real.pi := by
        have := hπ'; norm_num at this ⊢; linarith
      have h3 := Real.sin_nonpos_of_nonpos_of_neg_pi_le (x := arcAngC 5 q - 2 * Real.pi)
        (by linarith) (by linarith)
      rw [Real.sin_sub_two_pi] at h3
      linarith

/-- The cap map on the straight simplex of the ball is the unit vector of the corresponding arc. -/
theorem capMap_one_segVecC (k : ℕ) (q : stdSimplex ℝ (Fin 2)) (hk : k ≤ 2) :
    capMap 1 (segVecC k q) = arcVecC k q := by
  have hcos : (segVecC k q).ofLp 0 = Real.cos (arcAngC k q) := by
    simp only [segVecC_apply, WithLp.ofLp_smul, Pi.smul_apply, one1_ofLp_zero, smul_eq_mul,
      mul_one, segCosC, ContinuousMap.comp_apply]
    rfl
  have hnorm : ‖segVecC k q‖ = |Real.cos (arcAngC k q)| := by
    simp only [segVecC_apply, norm_smul, norm_one1, mul_one, Real.norm_eq_abs, segCosC,
      ContinuousMap.comp_apply]
    rfl
  have hb := arcC_angle_bounds k q
  have h0' : 0 ≤ arcAngC k q := by
    rw [arcAngC_apply]
    have h := hb.1
    have hk0 : 0 ≤ (k : ℝ) * Real.pi / 3 := by positivity
    linarith
  have hπ : arcAngC k q ≤ Real.pi := by
    rw [arcAngC_apply]
    have h1' : ang k * q 0 + ang (k + 1) * q 1 ≤ ((k : ℝ) + 1) * Real.pi / 3 := hb.2
    have h2' : ((k : ℝ) + 1) * Real.pi / 3 ≤ Real.pi := by
      have hk' : (k : ℝ) ≤ 2 := by exact_mod_cast hk
      nlinarith [Real.pi_pos]
    linarith
  have hsin : 0 ≤ Real.sin (arcAngC k q) := Real.sin_nonneg_of_mem_Icc ⟨h0', hπ⟩
  have hroot : √(1 - Real.cos (arcAngC k q) ^ 2) = Real.sin (arcAngC k q) := by
    rw [show 1 - Real.cos (arcAngC k q) ^ 2 = Real.sin (arcAngC k q) ^ 2 from by
      nlinarith [Real.sin_sq_add_cos_sq (arcAngC k q)]]
    rw [Real.sqrt_sq_eq_abs, abs_of_nonneg hsin]
  apply WithLp.ofLp_injective 2
  funext i
  fin_cases i
  · show (capMap 1 (segVecC k q)).ofLp (0 : Fin 2) = (arcVecC k q).ofLp (0 : Fin 2)
    rw [show (0 : Fin 2) = (0 : Fin 1).castSucc from rfl, capMap_castSucc, hcos, arcVecC_apply]
    exact u2_apply_zero (arcAngC k q)
  · show (capMap 1 (segVecC k q)).ofLp (1 : Fin 2) = (arcVecC k q).ofLp (1 : Fin 2)
    rw [show (1 : Fin 2) = Fin.last 1 from rfl, capMap_last, hnorm, sq_abs, hroot, arcVecC_apply,
      show (Fin.last 1 : Fin 2) = (1 : Fin 2) from rfl]
    exact u2_apply_one (arcAngC k q)

/-- The upper arcs of the hexagon are the cap images of the straight simplices of the ball. -/
theorem arc_cap_geom (y : Y) {k : ℕ} (hk : k ≤ 2) :
    arcSSimp Y y k
      = (TopCat.toSSet.map (TopCat.ofHom (capHomeo Y))).app (Opposite.op ⦋1⦌) (segSimp Y y k) := by
  apply (eSph2 Y 1).injective
  rw [toSSetObjEquivOld_naturality_space, eBall_segSimp, eSph2_arcSSimp]
  apply ContinuousMap.ext
  intro q
  rw [ContinuousMap.comp_apply]
  change (arcSC Y y k) q = capHomeo Y (segC Y y k q)
  rw [arcSC_apply, segC_apply]
  apply Subtype.ext
  change (y, arcVecC k q) = (y, capMap 1 (segVecC k q))
  rw [capMap_one_segVecC k q hk]

end

end Work.Whitney.RankTwo
