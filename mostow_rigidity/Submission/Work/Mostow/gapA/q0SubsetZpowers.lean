import Mathlib
import Submission.Work.Mostow.gapA.tubeDefs
import Submission.Work.Mostow.gapA.nmatDet
import Submission.Work.Mostow.gapA.nearId_isOriented

namespace Work.Mostow.gapA

open Submission.Mostow LeanEval.Geometry.MostowRigidity
open _root_.Matrix

noncomputable section

variable {a b : E 3}

/-- The scalar identity of a rotation about `geodSet a b` by `±2π/M`, with `M ≥ 3`
(a copy of `Work.Mostow.gapA.scalar_identity` with the `6 ≤ M` hypothesis removed, which its
proof never used). -/
lemma scalar_identity_ge3 (hA : POActionProp 3) (hI : HypIsometryProp 3)
    (ha : a ∈ Sph 3) (hb : b ∈ Sph 3) (hab : a ≠ b) (M : ℕ) (f : PO 3 1)
    (hfix : ∀ u : E 3, u ∈ geodSet a b → f • u = u)
    (hdisp : ∀ u : E 3, hdist u (f • u)
      = 2 * Real.arsinh (Real.sinh (distGeod a b u) * Real.sin (Real.pi / (M : ℝ))))
    (hsurj : ∀ Z : Fin 3 ⊕ Fin 1 → ℝ, Z ∈ NormSub a b → ∃ u : E 3, gcN a b u = Z) :
    ∀ Z : Fin 3 ⊕ Fin 1 → ℝ, Z ∈ NormSub a b →
      mink (Matrix.mulVec (emat f) Z) Z = cM M * mink Z Z := by
  intro Z hZ
  obtain ⟨u, hu⟩ := hsurj Z hZ
  have h1 := mink_hlift_emat_hlift_rot hA hI ha hb hab f hfix u
  have h2 : Real.cosh (hdist u (f • u))
      = -mink (hlift u) (Matrix.mulVec (emat f) (hlift u)) := by
    rw [emat_hlift f u, mink_hlift_neg_cosh']
    ring
  have h3 : Real.cosh (hdist u (f • u))
      = 1 + 2 * Real.sin (Real.pi / (M : ℝ)) ^ 2 * mink (gcN a b u) (gcN a b u) := by
    rw [hdisp u, Real.cosh_two_mul, Real.cosh_arsinh, Real.sinh_arsinh,
      Real.sq_sqrt (by positivity), ← sinh_sq_distGeod a b u ha hb hab]
    ring
  rw [hu] at h1 h3
  rw [h2] at h3
  have key : mink Z (Matrix.mulVec (emat f) Z)
      = (1 - 2 * Real.sin (Real.pi / (M : ℝ)) ^ 2) * mink Z Z := by linarith
  rw [minkSeg_comm, key, cM]

/-- `(cM M)^2 < 1` for `M ≥ 3`, where `cM M = cos (2π/M)`. -/
lemma cM_sq_lt_one_ge3 (M : ℕ) (hM : 3 ≤ M) : (cM M) ^ 2 < 1 := by
  rw [cM_eq_cos]
  have hMpos : (0 : ℝ) < (M : ℝ) := by exact_mod_cast (by omega : 0 < M)
  have hxpos : 0 < 2 * Real.pi / (M : ℝ) := by
    apply div_pos _ hMpos
    positivity
  have hxlt : 2 * Real.pi / (M : ℝ) < Real.pi := by
    rw [div_lt_iff₀ hMpos]
    have hM3 : (3 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM
    nlinarith [Real.pi_pos]
  have hsin : 0 < Real.sin (2 * Real.pi / (M : ℝ)) :=
    Real.sin_pos_of_pos_of_lt_pi hxpos hxlt
  have hsq : 0 < (Real.sin (2 * Real.pi / (M : ℝ))) ^ 2 := sq_pos_of_pos hsin
  nlinarith [Real.sin_sq_add_cos_sq (2 * Real.pi / (M : ℝ)), hsq]

/-- The normal action matrix of a rotation about `geodSet a b` by `±2π/M` is the rotation
matrix with diagonal entry `cM M = cos (2π/M)`. -/
lemma nmat_rot_form (hA : POActionProp 3) (hI : HypIsometryProp 3)
    (ha : a ∈ Sph 3) (hb : b ∈ Sph 3) (hab : a ≠ b) (B : AxisBasis a b) (M : ℕ) (f : PO 3 1)
    (hfix : ∀ u : E 3, u ∈ geodSet a b → f • u = u)
    (hdisp : ∀ u : E 3, hdist u (f • u)
      = 2 * Real.arsinh (Real.sinh (distGeod a b u) * Real.sin (Real.pi / (M : ℝ)))) :
    ∃ q : ℝ, q ^ 2 = 1 - (cM M) ^ 2 ∧ nmat B f = !![cM M, -q; q, cM M] := by
  obtain ⟨hfa, hfb⟩ := emat_fixes_nvec hA hI f a b ha hb hab hfix
  have hFmem : ∀ Z ∈ NormSub a b, emat f *ᵥ Z ∈ NormSub a b :=
    fun Z hZ => emat_mulVec_mem_NormSub f hfa hfb hZ
  have hscal : ∀ Z ∈ NormSub a b, mink (emat f *ᵥ Z) Z = cM M * mink Z Z :=
    scalar_identity_ge3 hA hI ha hb hab M f hfix hdisp (gcN_surjective a b ha hb hab)
  obtain ⟨q, hq, hE1, hE2⟩ := normal_action_matrix B f (cM M) hFmem hscal
  refine ⟨q, hq, ?_⟩
  have h00 : nmat B f 0 0 = cM M := by rw [nmat_zero_zero, hE1, mink_smulE_E1]
  have h10 : nmat B f 1 0 = q := by rw [nmat_one_zero, hE1, mink_smulE_E2]
  have h01 : nmat B f 0 1 = -q := by rw [nmat_zero_one, hE2, mink_smulE_E1]
  have h11 : nmat B f 1 1 = cM M := by rw [nmat_one_one, hE2, mink_smulE_E2]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [h00, h10, h01, h11]

theorem q0SubsetZpowers (hA : Submission.Mostow.POActionProp 3) (hI : Submission.Mostow.HypIsometryProp 3)
    (Γ : Subgroup (LeanEval.Geometry.MostowRigidity.PO 3 1))
    (a b : Submission.Mostow.E 3) (ha : a ∈ Submission.Mostow.Sph 3) (hb : b ∈ Submission.Mostow.Sph 3)
    (hab : a ≠ b) (M : ℕ) (hM : 3 ≤ M) (b₀ : LeanEval.Geometry.MostowRigidity.PO 3 1)
    (hrot : Work.Mostow.IsRotationAbout b₀ a b (2 * Real.pi / (M : ℝ)))
    (hstab : ∀ g : LeanEval.Geometry.MostowRigidity.PO 3 1, g ∈ Γ →
      (∀ u : Submission.Mostow.E 3, u ∈ Work.Mostow.geodSet a b → g • u = u) →
      (∃ k : ℤ, g = b₀ ^ k) ∨ ¬ Work.Mostow.IsOriented g)
    (c : LeanEval.Geometry.MostowRigidity.PO 3 1) (hc : c ∈ Work.Mostow.gapA.cent Γ b₀)
    (hfix : ∀ u : Submission.Mostow.E 3, u ∈ Work.Mostow.geodSet a b → c • u = u) :
    ∃ k : ℤ, c = b₀ ^ k := by
  rcases hstab c hc.2 hfix with hk | hnor
  · exact hk
  · exfalso
    obtain ⟨B⟩ := existsAxisBasis (a := a) (b := b) ha hb hab
    obtain ⟨hca, hcb⟩ := emat_fixes_nvec hA hI c a b ha hb hab hfix
    have hb0fix : ∀ u : E 3, u ∈ geodSet a b → b₀ • u = u := fun u hu => (hrot.1 u).mpr hu
    obtain ⟨hb0a, hb0b⟩ := emat_fixes_nvec hA hI b₀ a b ha hb hab hb0fix
    have hcP : ∀ Z ∈ NormSub a b, emat c *ᵥ Z ∈ NormSub a b :=
      fun Z hZ => emat_mulVec_mem_NormSub c hca hcb hZ
    have hbP : ∀ Z ∈ NormSub a b, emat b₀ *ᵥ Z ∈ NormSub a b :=
      fun Z hZ => emat_mulVec_mem_NormSub b₀ hb0a hb0b hZ
    -- `emat c` has determinant `-1`
    have hcdet : (emat c).det = -1 := by
      rcases det_eq_pm_one (emat_isJOrth c) with h | h
      · exact absurd (by rw [isOriented_iff_det, h]; norm_num) hnor
      · exact h
    -- the normal action of `c` is a reflection
    have hAdet : (nmat B c).det = -1 := by rw [nmatDet ha hb hab B c hca hcb, hcdet]
    obtain ⟨ho1, ho2, ho3⟩ := nmat_orth B c hcP
    have hdet2 : nmat B c 0 0 * nmat B c 1 1 - nmat B c 0 1 * nmat B c 1 0 = -1 := by
      simpa [Matrix.det_fin_two] using hAdet
    have hkey : (nmat B c 0 0 + nmat B c 1 1) ^ 2 + (nmat B c 0 1 - nmat B c 1 0) ^ 2 = 0 := by
      nlinarith [ho1, ho2, hdet2]
    have hsum : nmat B c 0 0 + nmat B c 1 1 = 0 := by
      nlinarith [hkey, sq_nonneg (nmat B c 0 0 + nmat B c 1 1),
        sq_nonneg (nmat B c 0 1 - nmat B c 1 0)]
    have hdiff' : nmat B c 0 1 = nmat B c 1 0 := by
      nlinarith [hkey, sq_nonneg (nmat B c 0 0 + nmat B c 1 1),
        sq_nonneg (nmat B c 0 1 - nmat B c 1 0)]
    have hsum' : nmat B c 1 1 = - nmat B c 0 0 := by linarith
    have hAform : nmat B c = !![nmat B c 0 0, nmat B c 1 0; nmat B c 1 0, -(nmat B c 0 0)] := by
      ext i j
      fin_cases i <;> fin_cases j <;> simp [hdiff', hsum']
    -- the normal action of `b₀` is a rotation with nonzero off-diagonal
    have hdisp_b0 : ∀ u : E 3, hdist u (b₀ • u)
        = 2 * Real.arsinh (Real.sinh (distGeod a b u) * Real.sin (Real.pi / (M : ℝ))) := by
      intro u
      rw [hrot.2 u, show (2 * Real.pi / (M : ℝ)) / 2 = Real.pi / (M : ℝ) from by ring]
    obtain ⟨μ, hμsq, hBform⟩ := nmat_rot_form hA hI ha hb hab B M b₀ hb0fix hdisp_b0
    have hμ : μ ≠ 0 := by
      intro h0
      rw [h0] at hμsq
      have h1 : (cM M) ^ 2 = 1 := by linarith
      exact absurd h1 (ne_of_lt (cM_sq_lt_one_ge3 M hM))
    -- `c` commutes with `b₀`
    have hcomm : c * b₀ = b₀ * c :=
      ((Subgroup.mem_centralizer_iff.mp hc.1) b₀ (Set.mem_singleton b₀)).symm
    have hmat : nmat B c * nmat B b₀ = nmat B b₀ * nmat B c := by
      rw [← nmat_mul B hA c b₀ hcP hbP, ← nmat_mul B hA b₀ c hbP hcP, hcomm]
    rw [hAform, hBform] at hmat
    have e00 : nmat B c 0 0 * cM M + nmat B c 1 0 * μ
        = cM M * nmat B c 0 0 + (-μ) * nmat B c 1 0 := by
      have h := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℝ => M 0 0) hmat
      simpa [Matrix.mul_fin_two] using h
    have e01 : nmat B c 0 0 * (-μ) + nmat B c 1 0 * cM M
        = cM M * nmat B c 1 0 + (-μ) * (-(nmat B c 0 0)) := by
      have h := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℝ => M 0 1) hmat
      simpa [Matrix.mul_fin_two] using h
    have hpm : nmat B c 0 0 * μ = 0 := by ring_nf at e01; linarith [e01]
    have hqm : nmat B c 1 0 * μ = 0 := by ring_nf at e00; linarith [e00]
    have hp0 : nmat B c 0 0 = 0 := (mul_eq_zero.mp hpm).resolve_right hμ
    have hq0 : nmat B c 1 0 = 0 := (mul_eq_zero.mp hqm).resolve_right hμ
    rw [hp0, hq0] at ho1
    norm_num at ho1

end

end Work.Mostow.gapA
