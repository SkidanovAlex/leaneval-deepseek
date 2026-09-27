import Mathlib
import Submission.Work.Mostow.gapA.defs
import Submission.Work.Mostow.gapA.screwDefs
import Submission.Work.Mostow.gapA.screwNorm
import Submission.Work.Mostow.gapA.screwGeod
import Submission.Work.Mostow.gapA.screwLine
import Submission.Work.Mostow.gapA.screwGeodParam
import Submission.Work.Mostow.gapA.screwDisp
import Submission.Work.Mostow.gapA.screwReal
import Submission.Work.Mostow.gapA.screwDim
import Submission.Work.Mostow.gapA.screwPlane
import Submission.Work.Mostow.gapA.screwTrig
import Submission.Work.Mostow.gapA.geodFacts
import Submission.Work.Mostow.gapA.mem_geodSet_iff_span
import Submission.Work.Mostow.gapA.rotationFormula
import Submission.Work.Mostow.gapA.rotSetup
import Submission.Work.Mostow.gapA.axisNormDefs
import Submission.Work.Mostow.gapA.normSub_orthonormalBasis
import Submission.Work.Mostow.gapA.commutingRotation_eq_or_inv
import Submission.Work.Mostow.gapA.screwRot
import Submission.Work.Mostow.gapA.screwScale
import Submission.Work.Mostow.bieberbach
import Submission.Work.Mostow.BoostTransitive

/-!
# `screwShort3`

A screw motion `g` translating the geodesic `geodSet a b` by `ℓ > 0` and commuting with the
rotation `b₀` about that geodesic of angle `2π/M` produces an infinite-order element `g * b₀ ^ j`
whose displacement at `z` is at most `2 * (ℓ + π/M) * cosh (distGeod a b z)`.

The proof combines the eigenvalue relation `emat g *ᵥ nvec a = ρ • nvec a`,
`emat g *ᵥ nvec b = ρ⁻¹ • nvec b` with `ρ + ρ⁻¹ = 2 cosh ℓ` (`screwScale`), the displacement
identity `screwDisp`, the rotation pigeonhole `screwRot` on the normal plane, and the explicit
estimates `screwReal`.
-/
open scoped Matrix

namespace Work.Mostow.gapA

open Submission.Mostow LeanEval.Geometry.MostowRigidity

noncomputable section

lemma Phi_emat (g : LeanEval.Geometry.MostowRigidity.PO 3 1) (x : Fin 3 ⊕ Fin 1 → ℝ) :
    Work.Mostow.gapA.Phi g x = Work.Mostow.emat g *ᵥ x := rfl

lemma nvec3_ne_zero (ξ : Submission.Mostow.E 3) : nvec ξ ≠ 0 := by
  intro h
  have h1 := congrFun h (Sum.inr 0)
  simp [nvec] at h1

lemma emat_pow_mulVec {c : LeanEval.Geometry.MostowRigidity.PO 3 1} {ρ : ℝ}
    (x : Fin 3 ⊕ Fin 1 → ℝ) (h : Work.Mostow.emat c *ᵥ x = ρ • x) (k : ℕ) :
    (Work.Mostow.emat c) ^ k *ᵥ x = ρ ^ k • x := by
  induction k with
  | zero => rw [pow_zero, pow_zero, _root_.Matrix.one_mulVec, one_smul]
  | succ k ih =>
      rw [pow_succ, pow_succ, ← _root_.Matrix.mulVec_mulVec, h, _root_.Matrix.mulVec_smul, ih,
        smul_smul, mul_comm]

theorem screwShort3 (hA : Submission.Mostow.POActionProp 3) (hI : Submission.Mostow.HypIsometryProp 3)
    (a b : Submission.Mostow.E 3) (ha : a ∈ Submission.Mostow.Sph 3) (hb : b ∈ Submission.Mostow.Sph 3)
    (hab : a ≠ b) (M : ℕ) (hM : 0 < M) (b₀ g : LeanEval.Geometry.MostowRigidity.PO 3 1) (ℓ : ℝ)
    (z : Submission.Mostow.E 3) (hℓ : 0 < ℓ)
    (hrot : Work.Mostow.IsRotationAbout b₀ a b (2 * Real.pi / (M : ℝ)))
    (hg : ∀ u : Submission.Mostow.E 3, u ∈ Work.Mostow.geodSet a b → Submission.Mostow.hdist u (g • u) = ℓ)
    (hcomm : g * b₀ = b₀ * g) :
    ∃ j : ℤ, ¬ IsOfFinOrder (g * b₀ ^ j) ∧
      Submission.Mostow.hdist z ((g * b₀ ^ j) • z) ≤
        2 * (ℓ + Real.pi / (M : ℝ)) * Real.cosh (Work.Mostow.distGeod a b z) := by
  have hB : Work.Mostow.POBasic 3 := Work.Mostow.POBasic.ofProp hA
  have hId : Work.Mostow.HypIsoData 3 := Work.Mostow.HypIsoData.ofProp hI
  have hfix₀ : ∀ u : Submission.Mostow.E 3, u ∈ Work.Mostow.geodSet a b → b₀ • u = u :=
    fun u hu => (hrot.1 u).mpr hu
  have hfixpow : ∀ (j : ℤ) (u : Submission.Mostow.E 3),
      u ∈ Work.Mostow.geodSet a b → (b₀ ^ j) • u = u := by
    intro j u hu
    have hinv : b₀⁻¹ • u = u := by
      calc b₀⁻¹ • u = b₀⁻¹ • (b₀ • u) := by rw [hfix₀ u hu]
        _ = (b₀⁻¹ * b₀) • u := (hB.mul_smul b₀⁻¹ b₀ u).symm
        _ = u := by rw [inv_mul_cancel, hB.one_smul]
    induction j using Int.induction_on with
    | zero => rw [zpow_zero, hB.one_smul]
    | succ k ih => rw [zpow_add_one, hB.mul_smul, hfix₀ u hu, ih]
    | pred k ih => rw [zpow_sub_one, hB.mul_smul, hinv, ih]
  have hdisp₀ : ∀ u : Submission.Mostow.E 3, Submission.Mostow.hdist u (b₀ • u)
      = 2 * Real.arsinh (Real.sinh (Work.Mostow.distGeod a b u) * Real.sin (Real.pi / (M : ℝ))) := by
    intro u
    rw [hrot.2 u, show (2 * Real.pi / (M : ℝ)) / 2 = Real.pi / (M : ℝ) from by ring]
  have hmapg : ∀ u : Submission.Mostow.E 3,
      u ∈ Work.Mostow.geodSet a b → g • u ∈ Work.Mostow.geodSet a b := by
    intro u hu
    have h1 : b₀ • (g • u) = g • u := by
      rw [← hB.mul_smul, ← hcomm, hB.mul_smul, hfix₀ u hu]
    exact (hrot.1 (g • u)).mp h1
  obtain ⟨ρ, hρpos, hρa, hρb, hρcosh⟩ := screwScale hA hI ha hb hab g ℓ hℓ hmapg hg
  have hρne : ρ ≠ 0 := ne_of_gt hρpos
  have hρne1 : ρ ≠ 1 := by
    intro h1
    have h2 : Real.cosh ℓ = 1 := by
      have h3 := hρcosh
      rw [h1, inv_one] at h3
      linarith
    have h4 : Real.sinh ℓ = 0 := by
      have h5 := Real.cosh_sq_sub_sinh_sq ℓ
      rw [h2] at h5
      nlinarith [sq_nonneg (Real.sinh ℓ)]
    exact (ne_of_gt hℓ) (Real.sinh_eq_zero.mp h4)
  -- the normal component of `hlift z`
  set Z : Fin 3 ⊕ Fin 1 → ℝ := gcN a b z with hZdef
  have hZA : mink Z (nvec a) = 0 := mink_gcN_nvec_a a b ha hb hab z
  have hZB : mink Z (nvec b) = 0 := mink_gcN_nvec_b a b ha hb hab z
  have hZmem : Z ∈ NormSub a b := mem_NormSub.mpr ⟨hZA, hZB⟩
  -- `emat g⁻¹` on the two null vectors
  have hρa' : Work.Mostow.gapA.Phi g⁻¹ (nvec a) = ρ⁻¹ • nvec a := by
    have h := Phi_mul_apply hA g⁻¹ g (nvec a)
    rw [inv_mul_cancel, Phi_one hA] at h
    rw [Phi_emat g (nvec a), hρa, map_smul] at h
    have h2 := congrArg (fun w => ρ⁻¹ • w) h
    rw [smul_smul, inv_mul_cancel₀ hρne, one_smul] at h2
    exact h2.symm
  have hρb' : Work.Mostow.gapA.Phi g⁻¹ (nvec b) = ρ • nvec b := by
    have h := Phi_mul_apply hA g⁻¹ g (nvec b)
    rw [inv_mul_cancel, Phi_one hA] at h
    rw [Phi_emat g (nvec b), hρb, map_smul] at h
    have h2 := congrArg (fun w => ρ • w) h
    rw [smul_smul, mul_inv_cancel₀ hρne, one_smul] at h2
    exact h2.symm
  -- `W := emat g⁻¹ *ᵥ Z`
  set W : Fin 3 ⊕ Fin 1 → ℝ := Work.Mostow.emat g⁻¹ *ᵥ Z with hWdef
  have hWmem : W ∈ NormSub a b := by
    refine mem_NormSub.mpr ⟨?_, ?_⟩
    · rw [hWdef, ← Phi_emat g⁻¹ Z, Phi_adjoint hA g⁻¹ Z (nvec a), inv_inv,
        Phi_emat g (nvec a), hρa, mink_smul_right3, hZA, mul_zero]
    · rw [hWdef, ← Phi_emat g⁻¹ Z, Phi_adjoint hA g⁻¹ Z (nvec b), inv_inv,
        Phi_emat g (nvec b), hρb, mink_smul_right3, hZB, mul_zero]
  have hWnorm : mink W W = mink Z Z := by
    rw [hWdef, ← Phi_emat g⁻¹ Z]
    exact Phi_form hA g⁻¹ Z Z
  -- the rotation pigeonhole
  obtain ⟨j, hj⟩ := screwRot hA hI ha hb hab M hM b₀ hfix₀ hdisp₀ Z W hZmem hWmem hWnorm
  -- `emat` of powers of `b₀` fixes the two null vectors
  have hfixnvecA : ∀ k : ℤ, Work.Mostow.emat (b₀ ^ k) *ᵥ nvec a = nvec a := fun k =>
    (emat_fixes_nvec hA hI (b₀ ^ k) a b ha hb hab (fun u hu => hfixpow k u hu)).1
  have hfixnvecB : ∀ k : ℤ, Work.Mostow.emat (b₀ ^ k) *ᵥ nvec b = nvec b := fun k =>
    (emat_fixes_nvec hA hI (b₀ ^ k) a b ha hb hab (fun u hu => hfixpow k u hu)).2
  have hNA : Work.Mostow.gapA.Phi (g * b₀ ^ j) (nullA a) = ρ • nullA a := by
    rw [Phi_mul_apply hA g (b₀ ^ j), Phi_emat (b₀ ^ j), show nullA a = nvec a from rfl,
      hfixnvecA j, Phi_emat g, hρa]
  have hNB : Work.Mostow.gapA.Phi (g * b₀ ^ j) (nullB b) = ρ⁻¹ • nullB b := by
    rw [Phi_mul_apply hA g (b₀ ^ j), Phi_emat (b₀ ^ j), show nullB b = nvec b from rfl,
      hfixnvecB j, Phi_emat g, hρb]
  have hformN : ∀ x y : Fin 3 ⊕ Fin 1 → ℝ,
      mink (Work.Mostow.gapA.Phi (g * b₀ ^ j) x) (Work.Mostow.gapA.Phi (g * b₀ ^ j) y) = mink x y :=
    fun x y => Phi_form hA (g * b₀ ^ j) x y
  have hfixInvA : Work.Mostow.emat (b₀ ^ j)⁻¹ *ᵥ nvec a = nvec a := by
    rw [show (b₀ ^ j)⁻¹ = b₀ ^ (-j) from (zpow_neg b₀ j).symm]
    exact hfixnvecA (-j)
  have hfixInvB : Work.Mostow.emat (b₀ ^ j)⁻¹ *ᵥ nvec b = nvec b := by
    rw [show (b₀ ^ j)⁻¹ = b₀ ^ (-j) from (zpow_neg b₀ j).symm]
    exact hfixnvecB (-j)
  have hmemInvA : Work.Mostow.gapA.Phi (g * b₀ ^ j)⁻¹ (nvec a) = ρ⁻¹ • nvec a := by
    rw [mul_inv_rev, Phi_mul_apply hA (b₀ ^ j)⁻¹ g⁻¹, hρa', map_smul,
      Phi_emat (b₀ ^ j)⁻¹ (nvec a), hfixInvA]
  have hmemInvB : Work.Mostow.gapA.Phi (g * b₀ ^ j)⁻¹ (nvec b) = ρ • nvec b := by
    rw [mul_inv_rev, Phi_mul_apply hA (b₀ ^ j)⁻¹ g⁻¹, hρb', map_smul,
      Phi_emat (b₀ ^ j)⁻¹ (nvec b), hfixInvB]
  have hmemN : ∀ x : Fin 3 ⊕ Fin 1 → ℝ, x ∈ Nsub a b →
      Work.Mostow.gapA.Phi (g * b₀ ^ j) x ∈ Nsub a b := by
    intro x hx
    have hxA : mink x (nvec a) = 0 := hx.1
    have hxB : mink x (nvec b) = 0 := hx.2
    refine ⟨?_, ?_⟩
    · rw [Phi_adjoint hA (g * b₀ ^ j) x, show nullA a = nvec a from rfl, hmemInvA,
        mink_smul_right3, hxA, mul_zero]
    · rw [Phi_adjoint hA (g * b₀ ^ j) x, show nullB b = nvec b from rfl, hmemInvB,
        mink_smul_right3, hxB, mul_zero]
  -- the coefficient identity
  have hα : alC a b (hlift z) = gcA a b z := by
    simp only [alC, gcA, gcL, smB, nullA, nullB]
    rw [minkSeg_comm (hlift z) (nvec b), Work.Mostow.mink_nvec_hlift, mink_nvec_nvec']
    rw [show inner ℝ a b - 1 = -(1 - inner ℝ a b) from by ring, neg_div_neg_eq]
    ring
  have hβ : beC a b (hlift z) = gcB a b z := by
    simp only [beC, gcB, gcL, smB, nullA, nullB]
    rw [minkSeg_comm (hlift z) (nvec a), Work.Mostow.mink_nvec_hlift, mink_nvec_nvec']
    rw [show inner ℝ a b - 1 = -(1 - inner ℝ a b) from by ring, neg_div_neg_eq]
    ring
  have hcoef : alC a b (hlift z) * beC a b (hlift z) * smB a b = -((1 + mink Z Z) / 2) := by
    rw [hα, hβ]
    have hS0 := mink_S0_self a b ha hb hab z
    have hexp : mink (gcA a b z • nvec a + gcB a b z • nvec b)
        (gcA a b z • nvec a + gcB a b z • nvec b) = 2 * (gcA a b z * gcB a b z * smB a b) := by
      simp only [smB, nullA, nullB, Work.Mostow.minkSeg_add_left, Work.Mostow.minkSeg_add_right,
        Work.Mostow.minkSeg_smul, mink_nvec_self' ha, mink_nvec_self' hb,
        Work.Mostow.minkSeg_comm (nvec b) (nvec a), mink_nvec_nvec']
      ring
    rw [← hZdef, hexp] at hS0
    linarith
  -- the displacement identity
  have hadj : mink Z (Work.Mostow.gapA.Phi g (Work.Mostow.gapA.Phi (b₀ ^ j) Z))
      = mink W (Work.Mostow.emat (b₀ ^ j) *ᵥ Z) := by
    have hW' : W = (Work.Mostow.gapA.Phi g⁻¹) Z := by rw [hWdef, Phi_emat]
    rw [hW', ← Phi_emat (b₀ ^ j) Z,
      minkSeg_comm Z (Work.Mostow.gapA.Phi g (Work.Mostow.gapA.Phi (b₀ ^ j) Z)),
      Phi_adjoint hA g (Work.Mostow.gapA.Phi (b₀ ^ j) Z) Z,
      minkSeg_comm (Work.Mostow.gapA.Phi (b₀ ^ j) Z) ((Work.Mostow.gapA.Phi g⁻¹) Z)]
  have hdispJ : mink (hlift z) (Work.Mostow.gapA.Phi (g * b₀ ^ j) (hlift z))
      = -((1 + mink Z Z) / 2) * (ρ + ρ⁻¹) + mink W (Work.Mostow.emat (b₀ ^ j) *ᵥ Z) := by
    have h1 := screwDisp ha hb hab (Work.Mostow.gapA.Phi (g * b₀ ^ j)) ρ hρne hNA hNB
      hformN hmemN (hlift z)
    rw [h1, prjN_hlift_eq_gcN a b z, ← hZdef, Phi_mul_apply hA g (b₀ ^ j), hcoef, hadj]
  -- cosh of the displacement
  have hcoshEq : Real.cosh (Submission.Mostow.hdist z ((g * b₀ ^ j) • z))
      = - mink (hlift z) (Work.Mostow.gapA.Phi (g * b₀ ^ j) (hlift z)) := by
    have h := mink_hlift_neg_cosh' z ((g * b₀ ^ j) • z)
    rw [← Phi_hlift hA (g * b₀ ^ j) z] at h
    linarith
  have hD : Real.cosh (Work.Mostow.distGeod a b z) ^ 2 = 1 + mink Z Z := by
    have h1 := sinh_sq_distGeod a b z ha hb hab
    rw [← hZdef] at h1
    have h2 := Real.cosh_sq_sub_sinh_sq (Work.Mostow.distGeod a b z)
    linarith
  have hD1 : 1 ≤ Real.cosh (Work.Mostow.distGeod a b z) := Real.one_le_cosh _
  have hsr := screwReal ℓ hℓ M hM (Real.cosh (Work.Mostow.distGeod a b z)) hD1
  have hmain : Real.cosh (Submission.Mostow.hdist z ((g * b₀ ^ j) • z))
      ≤ Real.cosh (2 * (ℓ + Real.pi / (M : ℝ)) * Real.cosh (Work.Mostow.distGeod a b z)) := by
    rw [hcoshEq, hdispJ, hρcosh]
    have h3 : -(-((1 + mink Z Z) / 2) * (2 * Real.cosh ℓ)
          + mink W (Work.Mostow.emat (b₀ ^ j) *ᵥ Z))
        ≤ (1 + mink Z Z) * Real.cosh ℓ - Real.cos (Real.pi / M) * mink Z Z := by
      nlinarith [hj]
    have h4 : (1 + mink Z Z) * Real.cosh ℓ - Real.cos (Real.pi / M) * mink Z Z
        = Real.cosh (Work.Mostow.distGeod a b z) ^ 2 * (Real.cosh ℓ - Real.cos (Real.pi / M))
          + Real.cos (Real.pi / M) := by
      rw [hD]; ring
    linarith [h3, h4, hsr]
  refine ⟨j, ?_, ?_⟩
  · intro hfinord
    obtain ⟨k, hkpos, hk⟩ := isOfFinOrder_iff_pow_eq_one.mp hfinord
    have h1 : (Work.Mostow.emat (g * b₀ ^ j)) ^ k *ᵥ nvec a = ρ ^ k • nvec a := by
      have hh : Work.Mostow.emat (g * b₀ ^ j) *ᵥ nvec a = ρ • nvec a := by
        rw [← Phi_emat (g * b₀ ^ j), Phi_mul_apply hA g (b₀ ^ j), Phi_emat (b₀ ^ j),
          hfixnvecA j, Phi_emat g, hρa]
      exact emat_pow_mulVec (nvec a) hh k
    have h2 : (Work.Mostow.emat (g * b₀ ^ j)) ^ k = 1 := by
      rw [← emat_pow hA, hk, emat_one hA]
    rw [h2, _root_.Matrix.one_mulVec] at h1
    have h3 : ρ ^ k = 1 := by
      have h4 := congrFun h1 (Sum.inr 0)
      simp [nvec] at h4
      linarith
    have hkne : (k : ℝ) ≠ 0 := by
      exact_mod_cast (Nat.pos_iff_ne_zero.mp hkpos)
    have h5 : ρ = 1 := by
      have hlog : Real.log ρ = 0 := by
        have h6 := Real.log_pow ρ k
        rw [h3, Real.log_one] at h6
        have h7 : (k : ℝ) * Real.log ρ = 0 := h6.symm
        exact (mul_eq_zero.mp h7).resolve_left hkne
      rw [← Real.exp_log hρpos, hlog, Real.exp_zero]
    exact hρne1 h5
  · have h1 := Real.cosh_le_cosh.mp hmain
    rw [abs_of_nonneg (hId.1 _ _), abs_of_nonneg (by positivity)] at h1
    exact h1

end

end Work.Mostow.gapA
