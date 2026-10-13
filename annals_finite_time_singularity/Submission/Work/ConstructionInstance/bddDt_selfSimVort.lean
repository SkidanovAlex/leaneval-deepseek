import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Submission.Work.ConstructionInstance.SelfSim
import Submission.Work.ConstructionInstance.lam_sq_timeDeriv_le_Ioo

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.ConstructionInstance

/-- **The `∂ₜ` box for the constructed (cut) self-similar vorticity.**

The cut field is `selfSimVort p g L lam x t = χ(ρ(x)/L) • U x t`, where
`U x t = λ̄(t)⁻¹ • omegaSz p g (ρ(x)^p/λ̄(t)) x` is the *uncut* self-similar field.  Since the
cut-off factor `χ(ρ(x)/L)` does not depend on `t`, differentiating in `t` just multiplies the
derivative of `U` by `χ(ρ(x)/L)`; and `|χ| ≤ 1`.  Hence the box for the cut field follows from the
box for the uncut one (which is `lam_sq_timeDeriv_le_Ioo`, proved by the chain rule
`dasdt(λ̄⁻¹F(c/λ̄)) = -λ̄'(F + (c/λ̄)∂_zF)/λ̄²` and `|F + z∂_zF| ≤ 20p + Cg + Cg'`). -/
theorem bddDt_selfSimVort {p : ℝ} (hp : 0 < p) (hp1 : p ≤ 1) {g : ℝ → ℝ → ℝ}
    {Cg Cg' K : ℝ}
    (hgbdd : ∀ z θ : ℝ, 0 ≤ z → θ ∈ Work.Spaces.Iθ → |g z θ| ≤ Cg)
    (hg2 : ∀ z θ : ℝ, 0 ≤ z → θ ∈ Work.Spaces.Iθ → |z * Work.Spaces.pz g z θ| ≤ Cg')
    (hgdiff : ∀ z θ : ℝ, 0 < z →
      HasDerivAt (fun z' => Work.ConstructionInstance.profile p g z' θ)
        (Work.Spaces.pz (Work.ConstructionInstance.profile p g) z θ) z)
    {L : ℝ} {lam : ℝ → ℝ} {T : ℝ} (hK : 0 ≤ K)
    (hlam : ∀ t ∈ Work.ConstructionInstance.preWindow T, 0 < lam t)
    (hlamdif : ∀ t ∈ Work.ConstructionInstance.preWindow T, HasDerivAt lam (deriv lam t) t)
    (hlamd : ∀ t ∈ Work.ConstructionInstance.preWindow T, |deriv lam t| ≤ K)
    {t : ℝ} (ht : t ∈ Work.ConstructionInstance.preWindow T) (y : Work.ConstructionInstance.R3) :
    (lam t) ^ 2 * ‖FiniteTimeSingularity.timeDeriv
      (Work.ConstructionInstance.selfSimVort p g L lam) y t‖ ≤ K * (20 * p + Cg + Cg') := by
  have hI0 : (0 : ℝ) ∈ Work.Spaces.Iθ := ⟨le_rfl, by linarith [Real.pi_pos]⟩
  have hCg : 0 ≤ Cg := le_trans (abs_nonneg _) (hgbdd 0 0 le_rfl hI0)
  have hCg' : 0 ≤ Cg' := by simpa using hg2 0 0 le_rfl hI0
  have hsum : 0 ≤ 20 * p + Cg + Cg' := by linarith
  have hlt : 0 < lam t := hlam t ht
  by_cases hrad : Work.Cyl.radial y = 0
  · -- on the symmetry axis the field vanishes identically
    have he0 : Work.Cyl.eTheta y = 0 := by
      rw [Work.Cyl.eTheta, hrad, div_zero, zero_smul]
    have hω0 : selfSimVort p g L lam y = fun _ => 0 := by
      funext s
      rw [selfSimVort_apply, omegaSz_apply, he0, smul_zero, smul_zero, smul_zero]
    rw [FiniteTimeSingularity.timeDeriv, hω0, deriv_const, norm_zero, mul_zero]
    exact mul_nonneg hK hsum
  · have hy : y ≠ 0 := by
      intro h0
      exact hrad (by rw [h0, Work.Cyl.radial_eq_zero_iff]; exact ⟨rfl, rfl⟩)
    have hρpos : 0 < Work.Cyl.rho y := by rw [Work.Cyl.rho_pos_iff]; exact hy
    set c : ℝ := Work.Cyl.rho y ^ p with hc
    set θ : ℝ := Work.Cyl.theta y with hθdef
    set e : R3 := Work.Cyl.eTheta y with he
    set a : ℝ := Work.Stability.chi (Work.Cyl.rho y / L) with ha
    have ha0 : 0 ≤ a := by rw [ha]; exact Work.Stability.chi_nonneg _
    have ha1 : |a| ≤ 1 := by
      rw [abs_of_nonneg ha0, ha]; exact Work.Stability.chi_le_one _
    have hcpos : 0 < c := by rw [hc]; exact Real.rpow_pos_of_pos hρpos p
    have hzpos : 0 < c / lam t := div_pos hcpos hlt
    have hlt2 : (0 : ℝ) < (lam t) ^ 2 := by positivity
    have hθabs : |θ| ≤ Real.pi / 2 := by
      rw [hθdef, abs_le]
      exact ⟨le_of_lt (Real.neg_pi_div_two_lt_arctan _),
        le_of_lt (Real.arctan_lt_pi_div_two _)⟩
    have hD4 := profile_add_z_pz_abs_le hp hp1 hgbdd hg2 hgdiff hzpos hθabs
    -- the scalar chain rule for `s ↦ λ̄(s)⁻¹ · F(c/λ̄(s))`
    have hφ : HasDerivAt (fun s => (lam s)⁻¹ * profile p g (c / lam s) θ)
        (-(deriv lam t * (profile p g (c / lam t) θ
          + (c / lam t) * Work.Spaces.pz (profile p g) (c / lam t) θ) / (lam t) ^ 2)) t :=
      hasDerivAt_inv_mul_comp (F := fun z' => profile p g z' θ) (hlamdif t ht) (ne_of_gt hlt)
        (hgdiff (c / lam t) θ hzpos)
    set X : ℝ := -(deriv lam t * (profile p g (c / lam t) θ
      + (c / lam t) * Work.Spaces.pz (profile p g) (c / lam t) θ) / (lam t) ^ 2) with hXdef
    -- the cut field is `χ(ρ(y)/L) = a` times the uncut one
    have hcut : selfSimVort p g L lam y
        = fun s => (a * ((lam s)⁻¹ * profile p g (c / lam s) θ)) • e := by
      funext s
      rw [selfSimVort_apply, ← ha, omegaSz_apply, ← hc, ← hθdef, ← he]
      rw [smul_smul, smul_smul]
      congr 1
      ring
    have hderivG : HasDerivAt (selfSimVort p g L lam y) ((a * X) • e) t := by
      rw [hcut, hXdef]
      exact (hφ.const_mul a).smul_const e
    have hdt : FiniteTimeSingularity.timeDeriv (selfSimVort p g L lam) y t
        = (a * X) • e := by
      rw [FiniteTimeSingularity.timeDeriv]
      exact hderivG.deriv
    rw [hdt, norm_smul, Real.norm_eq_abs, he, Work.Cyl.norm_eTheta y hrad, mul_one, abs_mul]
    have hkey : (lam t) ^ 2 * |X| = |deriv lam t * (profile p g (c / lam t) θ
        + (c / lam t) * Work.Spaces.pz (profile p g) (c / lam t) θ)| := by
      rw [hXdef, abs_neg, abs_div, abs_of_pos hlt2]
      rw [abs_mul]
      field_simp
    calc (lam t) ^ 2 * (|a| * |X|)
        = |a| * ((lam t) ^ 2 * |X|) := by ring
      _ ≤ 1 * ((lam t) ^ 2 * |X|) := mul_le_mul_of_nonneg_right ha1 (by positivity)
      _ = |deriv lam t * (profile p g (c / lam t) θ
            + (c / lam t) * Work.Spaces.pz (profile p g) (c / lam t) θ)| := by
            rw [one_mul, hkey]
      _ ≤ K * (20 * p + Cg + Cg') := by
            rw [abs_mul]
            exact mul_le_mul (hlamd t ht) hD4 (abs_nonneg _) hK

end Work.ConstructionInstance
