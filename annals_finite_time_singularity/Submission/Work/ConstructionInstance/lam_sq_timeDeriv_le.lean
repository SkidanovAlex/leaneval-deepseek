import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Submission.Work.ConstructionInstance.Defs
import Submission.Work.ConstructionInstance.profile_add_z_pz_abs_le
import Submission.Work.ConstructionInstance.hasDerivAt_inv_mul_comp

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.ConstructionInstance

/-- **The `∂ₜω` box, derived from the self-similar ansatz**: differentiating
`ω(x,t) = λ̄(t)⁻¹•omegaSz p g (ρ(x)^p/λ̄(t)) x` in `t` gives `λ̄²·∂ₜω = -λ̄'·(F + z∂_zF)·e_θ`, and
`F_* + z∂_zF_* = p(Γ/c)·4z/(1+z)³ ≤ 20p`, so the honest box for `∂ₜω` carries the `λ̄²` weight. -/
theorem lam_sq_timeDeriv_le {p : ℝ} (hp : 0 < p) (hp1 : p ≤ 1) {g : ℝ → ℝ → ℝ} {Cg Cg' K : ℝ}
    (hgbdd : ∀ z θ : ℝ, 0 ≤ z → θ ∈ Work.Spaces.Iθ → |g z θ| ≤ Cg)
    (hg2 : ∀ z θ : ℝ, 0 ≤ z → θ ∈ Work.Spaces.Iθ → |z * Work.Spaces.pz g z θ| ≤ Cg')
    (hgdiff : ∀ z θ : ℝ, 0 < z →
      HasDerivAt (fun z' => Work.ConstructionInstance.profile p g z' θ)
        (Work.Spaces.pz (Work.ConstructionInstance.profile p g) z θ) z)
    {lam : ℝ → ℝ} {T : ℝ} (hK : 0 ≤ K)
    (hlam : ∀ t ∈ Work.SolutionDelivery.extWindow T, 0 < lam t)
    (hlamdif : ∀ t ∈ Work.SolutionDelivery.extWindow T, HasDerivAt lam (deriv lam t) t)
    (hlamd : ∀ t ∈ Work.SolutionDelivery.extWindow T, |deriv lam t| ≤ K)
    {ω : Work.ConstructionInstance.R3 → ℝ → Work.ConstructionInstance.R3}
    (hans : ∀ t : ℝ, ∀ x : Work.ConstructionInstance.R3,
      ω x t = (lam t)⁻¹ • Work.ConstructionInstance.omegaSz p g
        (Work.Cyl.rho x ^ p / lam t) x) :
    ∀ t ∈ Work.SolutionDelivery.extWindow T, ∀ y : Work.ConstructionInstance.R3,
      (lam t) ^ 2 * ‖FiniteTimeSingularity.timeDeriv ω y t‖ ≤ K * (20 * p + Cg + Cg') := by
  have hI0 : (0 : ℝ) ∈ Work.Spaces.Iθ := ⟨le_rfl, by linarith [Real.pi_pos]⟩
  have hCg : 0 ≤ Cg := le_trans (abs_nonneg _) (hgbdd 0 0 le_rfl hI0)
  have hCg' : 0 ≤ Cg' := by simpa using hg2 0 0 le_rfl hI0
  have hsum : 0 ≤ 20 * p + Cg + Cg' := by linarith
  intro t ht y
  have hlt : 0 < lam t := hlam t ht
  by_cases hrad : Work.Cyl.radial y = 0
  · have he0 : Work.Cyl.eTheta y = 0 := by
      rw [Work.Cyl.eTheta, hrad, div_zero, zero_smul]
    have hω0 : ω y = fun _ => 0 := by
      funext s
      rw [hans s y, Work.ConstructionInstance.omegaSz_apply, he0, smul_zero, smul_zero]
    rw [FiniteTimeSingularity.timeDeriv, hω0]
    have hdz : deriv (fun _ : ℝ => (0 : R3)) t = 0 := deriv_const t 0
    rw [hdz, norm_zero, mul_zero]
    exact mul_nonneg hK hsum
  · have hy : y ≠ 0 := by
      intro h0
      exact hrad (by rw [h0, Work.Cyl.radial_eq_zero_iff]; exact ⟨rfl, rfl⟩)
    have hρpos : 0 < Work.Cyl.rho y := by
      rw [Work.Cyl.rho_pos_iff]; exact hy
    set c : ℝ := Work.Cyl.rho y ^ p with hc
    set θ : ℝ := Work.Cyl.theta y with hθdef
    set e : R3 := Work.Cyl.eTheta y with he
    have hcpos : 0 < c := by rw [hc]; exact Real.rpow_pos_of_pos hρpos p
    have hzpos : 0 < c / lam t := div_pos hcpos hlt
    have hθabs : |θ| ≤ Real.pi / 2 := by
      rw [hθdef, abs_le]
      exact ⟨le_of_lt (Real.neg_pi_div_two_lt_arctan _),
        le_of_lt (Real.arctan_lt_pi_div_two _)⟩
    have hD4 := profile_add_z_pz_abs_le hp hp1 hgbdd hg2 hgdiff hzpos hθabs
    set φ : ℝ → ℝ := fun s => (lam s)⁻¹ * profile p g (c / lam s) θ with hφdef
    have hφ : HasDerivAt φ
        (-(deriv lam t * (profile p g (c / lam t) θ
          + (c / lam t) * Work.Spaces.pz (profile p g) (c / lam t) θ) / (lam t) ^ 2)) t :=
      hasDerivAt_inv_mul_comp (F := fun z' => profile p g z' θ) (hlamdif t ht) (ne_of_gt hlt)
        (hgdiff (c / lam t) θ hzpos)
    have hωeq : ω y = fun s => φ s • e := by
      funext s
      rw [hans s y, Work.ConstructionInstance.omegaSz_apply, ← hc, ← hθdef, ← he]
      rw [smul_smul, hφdef]
    have hderivω : deriv (ω y) t = deriv φ t • e := by
      rw [hωeq, deriv_smul_const hφ.differentiableAt]
    rw [FiniteTimeSingularity.timeDeriv, hderivω]
    have hlt2 : (0 : ℝ) < (lam t) ^ 2 := by positivity
    have hkey : (lam t) ^ 2 * |deriv φ t|
        = |deriv lam t * (profile p g (c / lam t) θ
            + (c / lam t) * Work.Spaces.pz (profile p g) (c / lam t) θ)| := by
      rw [hφ.deriv, abs_neg, abs_div, abs_of_pos hlt2]
      rw [abs_mul]
      field_simp
    calc (lam t) ^ 2 * ‖deriv φ t • e‖
        = (lam t) ^ 2 * (|deriv φ t| * ‖e‖) := by rw [norm_smul, Real.norm_eq_abs]
      _ = ((lam t) ^ 2 * |deriv φ t|) * ‖e‖ := by ring
      _ = |deriv lam t * (profile p g (c / lam t) θ
            + (c / lam t) * Work.Spaces.pz (profile p g) (c / lam t) θ)| * ‖e‖ := by
            rw [hkey]
      _ ≤ (K * (20 * p + Cg + Cg')) * 1 := by
            apply mul_le_mul
            · rw [abs_mul]
              exact mul_le_mul (hlamd t ht) hD4 (abs_nonneg _) hK
            · rw [he]; exact le_of_eq (Work.Cyl.norm_eTheta y hrad)
            · exact norm_nonneg e
            · exact mul_nonneg hK hsum
      _ = K * (20 * p + Cg + Cg') := by ring

end Work.ConstructionInstance
