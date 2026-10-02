import Submission.Work.PTGeometric.RieszProj.Basic

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# The Riesz projection is the spectral projection onto the top cluster
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

open scoped ContDiff
open Set Function MeasureTheory

namespace Work.PTGeometric

noncomputable section

variable {n : ℕ}

/-- `contDen S θ` is invertible when `S` is self-adjoint with all eigenvalues in the two clusters. -/
lemma isUnit_contDen {S : EndOp n} (hSsym : (S : Amb n →ₗ[ℝ] Amb n).IsSymmetric)
    (hS : Cluster S) (θ : ℝ) : IsUnit (contDen S θ) := by
  rw [ContinuousLinearMap.isUnit_iff_isUnit_toLinearMap, LinearMap.isUnit_iff_ker_eq_bot,
    Submodule.eq_bot_iff]
  intro v hv
  rw [LinearMap.mem_ker] at hv
  have hT : ∀ x y : Amb n, inner ℝ ((cc θ • (1 : EndOp n) - S) x) y
      = inner ℝ x ((cc θ • (1 : EndOp n) - S) y) := by
    intro x y
    have hx : (cc θ • (1 : EndOp n) - S) x = cc θ • x - S x := by
      rw [sub_apply, smul_apply, one_apply_eq_self]
    have hy : (cc θ • (1 : EndOp n) - S) y = cc θ • y - S y := by
      rw [sub_apply, smul_apply, one_apply_eq_self]
    have hSsym' : inner ℝ (S x) y = inner ℝ x (S y) := hSsym x y
    rw [hx, hy, inner_sub_right, inner_sub_left, real_inner_smul_right, real_inner_smul_left,
      hSsym']
  have hkey : ‖(cc θ • (1 : EndOp n) - S) v‖ ^ 2 + (ss θ) ^ 2 * ‖v‖ ^ 2 = 0 := by
    have h1 : inner ℝ (contDen S θ v) v
        = ‖(cc θ • (1 : EndOp n) - S) v‖ ^ 2 + (ss θ) ^ 2 * ‖v‖ ^ 2 := by
      have hexp : contDen S θ v
          = (cc θ • (1 : EndOp n) - S) ((cc θ • (1 : EndOp n) - S) v) + (ss θ) ^ 2 • v := by
        rw [contDen, add_apply, ContinuousLinearMap.mul_apply, smul_apply, one_apply_eq_self]
      rw [hexp, inner_add_left, hT ((cc θ • (1 : EndOp n) - S) v) v,
        real_inner_self_eq_norm_sq, real_inner_smul_left, real_inner_self_eq_norm_sq]
    rw [show contDen S θ v = 0 from hv, inner_zero_left] at h1
    linarith [h1]
  have hA : (cc θ • (1 : EndOp n) - S) v = 0 := by
    have hnorm : ‖(cc θ • (1 : EndOp n) - S) v‖ ^ 2 = 0 := by
      nlinarith [hkey, sq_nonneg (ss θ), sq_nonneg ‖v‖]
    exact norm_eq_zero.mp (sq_eq_zero_iff.mp hnorm)
  by_cases hs : ss θ = 0
  · have hsin : Real.sin θ = 0 := by
      have h := hs
      rw [ss_eq] at h
      linarith
    have hcos : Real.cos θ = 1 ∨ Real.cos θ = -1 := by
      have h2 : Real.cos θ ^ 2 = 1 := by
        have h := Real.sin_sq_add_cos_sq θ
        rw [hsin] at h
        linarith
      rcases sq_eq_one_iff.mp h2 with h | h
      · exact Or.inl h
      · exact Or.inr h
    have hev : S v = cc θ • v := by
      have hA' := hA
      rw [sub_apply, smul_apply, one_apply_eq_self, sub_eq_zero] at hA'
      exact hA'.symm
    have hcc1 : cc θ = 3/2 ∨ cc θ = 1/2 := by
      rcases hcos with hc | hc
      · left; rw [cc_eq, hc]; norm_num
      · right; rw [cc_eq, hc]; norm_num
    rcases hcc1 with hc1 | hc1
    · by_cases hv0 : v = 0
      · exact hv0
      · exfalso
        refine hS.ne_three_half (Module.End.hasEigenvalue_of_hasEigenvector (x := v) ?_) rfl
        refine ⟨?_, hv0⟩
        rw [Module.End.mem_eigenspace_iff]
        exact hev.trans (by rw [hc1])
    · by_cases hv0 : v = 0
      · exact hv0
      · exfalso
        refine hS.ne_half (Module.End.hasEigenvalue_of_hasEigenvector (x := v) ?_) rfl
        refine ⟨?_, hv0⟩
        rw [Module.End.mem_eigenspace_iff]
        exact hev.trans (by rw [hc1])
  · have h3 : (ss θ) ^ 2 * ‖v‖ ^ 2 = 0 := by
      nlinarith [hkey, sq_nonneg (ss θ), sq_nonneg ‖v‖]
    have h4 : ‖v‖ ^ 2 = 0 := by
      rcases mul_eq_zero.mp h3 with h | h
      · exact absurd h (pow_ne_zero 2 hs)
      · exact h
    simpa using norm_eq_zero.mp (sq_eq_zero_iff.mp h4)



/-- **The value of the Riesz projection on an eigenvector.**  For a self-adjoint `S` with all
eigenvalues in the two clusters, `Phi S` acts on an eigenvector with eigenvalue `lam` as `1` if
`|lam - 1| < 1/2` and as `0` otherwise. -/
theorem Phi_apply_eigen (S : EndOp n)
    (hSsym : (S : Amb n →ₗ[ℝ] Amb n).IsSymmetric) (hS : Cluster S) {u : Amb n} (hu : u ≠ 0)
    (lam : ℝ) (hlam : Module.End.HasEigenvalue (S : Amb n →ₗ[ℝ] Amb n) lam) (h : S u = lam • u) :
    Phi S u = (if |lam - 1| < 1/2 then (1:ℝ) else 0) • u := by
  have ha : lam ≠ 1/2 := hS.ne_half hlam
  have hb : lam ≠ 3/2 := hS.ne_three_half hlam
  have ha2 : (lam - 1) ^ 2 ≠ 1/4 := by
    intro hh
    have h2 : (lam - 1) ^ 2 = ((1/2 : ℝ)) ^ 2 := by norm_num; exact hh
    rcases sq_eq_sq_iff_eq_or_eq_neg.mp h2 with h3 | h3
    · exact hb (by linarith)
    · exact ha (by linarith)
  have hne : |lam - 1| ≠ 1/2 := by
    intro hh
    exact ha2 (by rw [← sq_abs]; rw [hh]; norm_num)
  have hmu : ∀ θ : ℝ, (cc θ - lam) ^ 2 + (ss θ) ^ 2 ≠ 0 := by
    intro θ
    have h1 := den_pos (lam - 1) ha2 θ
    have h2 : (cc θ - lam) ^ 2 + (ss θ) ^ 2 = (lam - 1)^2 + 1/4 - (lam-1)*Real.cos θ := by
      have h3 := den_eq (lam - 1) θ
      rw [show (1 : ℝ) + (lam - 1) = lam from by ring] at h3
      exact h3
    rw [h2]
    exact ne_of_gt h1
  have hcont : ∀ θ : ℝ, (Ring.inverse (contDen S θ) * contNum S θ) u
      = (1/2 + (1/4 - (lam - 1) ^ 2)/2 * ((lam - 1) ^ 2 + 1/4 - (lam - 1) * Real.cos θ)⁻¹) • u := by
    intro θ
    have hinv : Ring.inverse (contDen S θ) u = ((cc θ - lam) ^ 2 + (ss θ) ^ 2)⁻¹ • u :=
      ringInverse_apply_of_eigen (isUnit_contDen hSsym hS θ) (hmu θ) (contDen_apply_of_eigen h θ)
    rw [ContinuousLinearMap.mul_apply, contNum_apply_of_eigen h θ, map_smul, hinv, smul_smul]
    congr 1
    have h1 : cc θ - lam = cc θ - (1 + (lam - 1)) := by ring
    rw [h1, ratio_eq (lam - 1) θ,
      scalar_factor (lam - 1) θ (ne_of_gt (den_pos (lam - 1) ha2 θ))]
  have hint : IntervalIntegrable
      (fun θ : ℝ => Ring.inverse (contDen S θ) * contNum S θ) volume 0 (2 * Real.pi) := by
    apply ContinuousOn.intervalIntegrable
    have hcc : Continuous cc := by
      rw [show cc = fun θ : ℝ => 1 + (1/2) * Real.cos θ from funext (fun θ => by rw [cc])]
      fun_prop
    have hss : Continuous ss := by
      rw [show ss = fun θ : ℝ => (1/2) * Real.sin θ from funext (fun θ => by rw [ss])]
      fun_prop
    have hden : Continuous fun θ : ℝ => contDen S θ := by
      simp only [contDen]; fun_prop
    have hnum : Continuous fun θ : ℝ => contNum S θ := by
      simp only [contNum]; fun_prop
    have hinv : ContinuousOn (fun θ : ℝ => Ring.inverse (contDen S θ)) (uIcc 0 (2 * Real.pi)) := by
      intro θ₀ _
      obtain ⟨u₀, hu₀⟩ := isUnit_contDen hSsym hS θ₀
      have h2 : ContinuousAt (fun y : EndOp n => Ring.inverse y) (contDen S θ₀) := by
        have h3 : ContinuousAt (fun y : EndOp n => Ring.inverse y) (↑u₀ : EndOp n) :=
          (hasFDerivAt_ringInverse (𝕜 := ℝ) u₀).continuousAt
        rwa [hu₀] at h3
      have h1 : ContinuousAt (fun θ : ℝ => Ring.inverse (contDen S θ)) θ₀ := by
        simpa only [Function.comp_def] using h2.comp hden.continuousAt
      exact h1.continuousWithinAt
    exact hinv.mul hnum.continuousOn
  rw [Phi, ContinuousLinearMap.smul_apply]
  show (2 * Real.pi)⁻¹ • ((∫ θ in (0:ℝ)..(2 * Real.pi),
    Ring.inverse (contDen S θ) * contNum S θ) u) = _
  rw [ContinuousLinearMap.intervalIntegral_apply hint]
  simp_rw [hcont]
  rw [intervalIntegral.integral_smul_const, smul_smul]
  congr 1
  by_cases hlt : |lam - 1| < 1/2
  · rw [if_pos hlt, scalar_value_top (lam - 1) ha2 hlt]
  · rw [if_neg hlt, scalar_value_bot (lam - 1) ha2 (lt_of_le_of_ne (not_lt.mp hlt) (fun hh => hne hh.symm))]

end

end Work.PTGeometric
