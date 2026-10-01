/-
# Area 4 / HB (11.9) — the regularised integrand agrees with the naive integrand off `s = 0`

The regularised contour integrand
`Phi s = Γ(s+1) · dslope (u ↦ L(ρ+u)) 0 s · X^s · F(ρ+s)`
coincides, for `s ≠ 0`, with the naive integrand `Γ(s) X^s L(ρ+s) F(ρ+s)` whenever `L(ρ) = 0`:
the pole of `Γ` at the origin is cancelled by the zero of `L` at `ρ`.  It is continuous on the
half-plane `Re s > -1` (where `Γ(s+1)` is holomorphic).
-/
import Mathlib
import Submission.Work.LinnikAreas.Density4.SsmSetup
import Submission.Work.LinnikAreas.Density4.diffOn_Gamma_dslope_mul_lcmF

open DirichletCharacter Complex
open scoped Classical BigOperators
noncomputable section

namespace Work.LinnikAreas.Density4

/-- For `s ≠ 0`, and provided `L(ρ,χ) = 0`, the regularised integrand `Phi` agrees with the
naive integrand `Γ(s) X^s L(ρ+s) F(ρ+s)`. -/
theorem Phi_eq_naive (q : ℕ) [NeZero q] (U V W X : ℝ) (χ : DirichletCharacter ℂ q) (ρ s : ℂ)
    (hL0 : DirichletCharacter.LFunction χ ρ = 0) (hs : s ≠ 0) :
    Phi q U V W X χ ρ s
      = Complex.Gamma s * (X : ℂ) ^ s * DirichletCharacter.LFunction χ (ρ + s)
          * lcmF q U V W χ (ρ + s) := by
  have hds : dslope (fun u : ℂ => DirichletCharacter.LFunction χ (ρ + u)) 0 s
      = DirichletCharacter.LFunction χ (ρ + s) / s := by
    rw [dslope_of_ne _ hs, slope]
    simp only [add_zero, hL0, vsub_eq_sub, sub_zero, smul_eq_mul, div_eq_mul_inv]
    ring
  rw [Phi, hds, Complex.Gamma_add_one s hs]
  field_simp

/-- `Phi` is continuous on the half-plane `Re s > -1`. -/
theorem continuousOn_Phi (q : ℕ) [NeZero q] (U V W X : ℝ) (χ : DirichletCharacter ℂ q) (ρ : ℂ)
    (hX : 0 < X) (hχ : χ ≠ 1) :
    ContinuousOn (Phi q U V W X χ ρ) {s : ℂ | -1 < s.re} := by
  have hshift : Continuous (fun u : ℂ => ρ + u) := continuous_const.add continuous_id
  have hL : Differentiable ℂ (fun u : ℂ => DirichletCharacter.LFunction χ (ρ + u)) :=
    (differentiable_LFunction hχ).comp (differentiable_id.const_add ρ)
  have hd : Differentiable ℂ
      (dslope (fun u : ℂ => DirichletCharacter.LFunction χ (ρ + u)) 0) := by
    have h := (differentiableOn_dslope (f := fun u : ℂ => DirichletCharacter.LFunction χ (ρ + u))
      (c := 0) (s := Set.univ) (by simp)).mpr hL.differentiableOn
    rwa [differentiableOn_univ] at h
  have hlcm : Differentiable ℂ (lcmF q U V W χ) := differentiable_lcmF q U V W χ
  have hXne : (X : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt hX
  have hΓset : ContinuousOn Complex.Gamma {z : ℂ | ∀ m : ℕ, z ≠ -(m : ℂ)} := fun z hz =>
    (Complex.continuousAt_Gamma z hz).continuousWithinAt
  have hmaps : Set.MapsTo (fun s : ℂ => s + 1) {s : ℂ | -1 < s.re} {z : ℂ | ∀ m : ℕ, z ≠ -(m : ℂ)} := by
    intro s hs m hm
    have hs' : -1 < s.re := hs
    have h1 : (s + 1).re = (-(m : ℂ)).re := congrArg Complex.re hm
    simp only [Complex.add_re, Complex.one_re, Complex.neg_re, Complex.natCast_re] at h1
    have h2 : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
    linarith
  have hΓ : ContinuousOn (fun s : ℂ => Complex.Gamma (s + 1)) {s : ℂ | -1 < s.re} :=
    hΓset.comp (continuous_id.add continuous_const).continuousOn hmaps
  unfold Phi
  exact ((hΓ.mul hd.continuous.continuousOn).mul
    ((differentiable_id.const_cpow (Or.inl hXne)).continuous.continuousOn)).mul
    (hlcm.continuous.comp hshift).continuousOn

end Work.LinnikAreas.Density4
