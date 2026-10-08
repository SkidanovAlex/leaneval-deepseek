/-
# Anisotropy of Higman's Column-V squaring forms

The families `B(n,θ,ε)`, `C(n,ε)`, `D(n,θ,ε)` of Higman's table are Suzuki 2-groups, i.e. the
squaring form `u ↦ b u u` of the associated cocycle is *anisotropic* (`b u u ≠ 0` for `u ≠ 0`)
exactly when `ε` avoids the excluded values of Column III.  These are the elementary verifications
which make `Work.Higman.cocycle_normal_form`'s normal form a *Suzuki* two-step group, and hence
which let `Work.Higman.cocycle_of_mulEquiv` be applied to it.

This file treats the families `B`, `C` and `D`.
-/

import Mathlib
import Submission.Work.Higman.Family
import Submission.Work.Higman.cocycle_setup

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

namespace Work.Higman

/-- **Anisotropy of the `B` squaring form.**  If `ε ≠ ρ⁻¹ + θ ρ` for every `ρ` (this includes
`ε ≠ 0`, the case `ρ = 0`), then `bCocycle F θ ε u u ≠ 0` for `u ≠ 0`. -/
theorem bCocycle_anisotropic {F : Type*} [Field F] [CharP F 2] (θ : F ≃+* F) (ε : F)
    (hρ : ∀ ρ : F, ε ≠ ρ⁻¹ + θ ρ) (u : F × F) (hu : u ≠ 0) :
    bCocycle F θ ε u u ≠ 0 := by
  obtain ⟨a, b⟩ := u
  show a * θ a + ε * (a * θ b) + b * θ b ≠ 0
  intro hzero
  rcases eq_or_ne b 0 with hb | hb
  · -- `b = 0`: the value is `a * θ a ≠ 0`
    subst hb
    simp only [map_zero, mul_zero, add_zero, zero_mul] at hzero
    have ha : a ≠ 0 := fun h => hu (by simp [h])
    have hθa : θ a ≠ 0 := fun h => ha (θ.injective (by rw [h, map_zero]))
    exact mul_ne_zero ha hθa hzero
  · -- `b ≠ 0`
    have ha : a ≠ 0 := by
      intro h
      subst h
      simp only [map_zero, mul_zero, zero_mul, zero_add] at hzero
      exact mul_ne_zero hb (fun hh => hb (θ.injective (by rw [hh, map_zero]))) hzero
    set ρ : F := a / b with hρdef
    have hbθb : b * θ b ≠ 0 :=
      mul_ne_zero hb (fun hh => hb (θ.injective (by rw [hh, map_zero])))
    have haeq : a = ρ * b := by
      rw [hρdef, div_mul_cancel₀ a hb]
    have hρne : ρ ≠ 0 := fun h => ha (by rw [haeq, h, zero_mul])
    have hfac : (b * θ b) * (ρ * θ ρ + ε * ρ + 1) = 0 := by
      rw [haeq, map_mul] at hzero
      rw [← hzero]; ring
    have hfac0 : ρ * θ ρ + ε * ρ + 1 = 0 := by
      rcases mul_eq_zero.mp hfac with h | h
      · exact absurd h hbθb
      · exact h
    have hkey : ε = ρ⁻¹ + θ ρ := by
      have h2 : ρ * θ ρ = ε * ρ + 1 :=
        AddExpTwo.eq_of_add_eq_zero (by rw [← add_assoc]; exact hfac0)
      have h1 : ε * ρ = ρ * θ ρ + 1 := by
        rw [h2, add_assoc, CharTwo.add_self_eq_zero, add_zero]
      have h3 : ε = (ρ * θ ρ + 1) / ρ := by
        rw [← h1]; field_simp
      rw [h3]
      field_simp
      ring
    exact hρ ρ hkey

/-- **Anisotropy of the `C` squaring form.**  Here `θ` satisfies `(θ (θ a)) ^ 2 = a` (i.e.
`2θ² = 1` in Higman's notation, so `θ²` is the inverse Frobenius) and `ε ≠ ρ⁻¹ + ρ^{2θ+1}` for
all `ρ`; then `cCocycle F θ ε u u ≠ 0` for `u ≠ 0`. -/
theorem cCocycle_anisotropic {F : Type*} [Field F] [CharP F 2] [Finite F]
    (θ : F ≃+* F) (ε : F) (hθ : ∀ a : F, (θ (θ a)) ^ 2 = a)
    (hρ : ∀ ρ : F, ε ≠ ρ⁻¹ + θ ρ ^ 2 * ρ) (u : F × F) (hu : u ≠ 0) :
    cCocycle F θ ε u u ≠ 0 := by
  obtain ⟨a, b⟩ := u
  set γ : F := sqrtF F a with hγdef
  have hγ2 : γ ^ 2 = a := by rw [hγdef]; exact sqrtF_sq F a
  have hγdef' : sqrtF F a = γ := hγdef.symm
  have hgoal : a * θ a + ε * (sqrtF F a * θ (b * b)) + b * b =
      γ ^ 2 * (θ γ) ^ 2 + ε * (γ * (θ b) ^ 2) + b ^ 2 := by
    have h1 : θ a = (θ γ) ^ 2 := by rw [← hγ2, map_pow]
    have h2 : θ (b * b) = (θ b) ^ 2 := by rw [map_mul, pow_two]
    rw [h1, h2, hγ2]
    ring
  show a * θ a + ε * (sqrtF F a * θ (b * b)) + b * b ≠ 0
  rw [hgoal]
  intro hQ
  rcases eq_or_ne b 0 with hb | hb
  · subst hb
    have hQ0 : γ ^ 2 * (θ γ) ^ 2 = 0 := by simpa using hQ
    have hγne : γ ≠ 0 := by
      intro h
      have ha : a = 0 := by rw [← hγ2, h]; ring
      exact hu (by simp [ha])
    have hθγne : θ γ ≠ 0 := fun h => hγne (θ.injective (by rw [h, map_zero]))
    exact mul_ne_zero (pow_ne_zero 2 hγne) (pow_ne_zero 2 hθγne) hQ0
  · set μ : F := θ b with hμdef
    set ν : F := θ μ with hνdef
    have hμne : μ ≠ 0 := by
      intro h
      rw [hμdef] at h
      exact hb (θ.injective (by rw [h, map_zero]))
    have hν2 : ν ^ 2 = b := hθ b
    have hb2ne : b ^ 2 ≠ 0 := pow_ne_zero 2 hb
    have hμ2ne : μ ^ 2 ≠ 0 := pow_ne_zero 2 hμne
    have hγne : γ ≠ 0 := by
      intro h
      have hQ0 : b ^ 2 = 0 := by simpa [h] using hQ
      exact hb2ne hQ0
    set ρ : F := γ * μ ^ 2 / b ^ 2 with hρdef
    have hγeq : γ = ρ * b ^ 2 / μ ^ 2 := by
      rw [hρdef]; field_simp
    have hθγeq : θ γ = θ ρ * μ ^ 2 / b := by
      rw [hγeq, map_div₀, map_mul, map_pow, map_pow, ← hμdef, ← hνdef, hν2]
    have hA : γ ^ 2 * (θ γ) ^ 2 = ρ ^ 2 * (θ ρ) ^ 2 * b ^ 2 := by
      rw [hθγeq, hγeq]
      field_simp
    have hB : ε * (γ * μ ^ 2) = ε * ρ * b ^ 2 := by
      rw [hγeq]
      field_simp
    have hzero : ρ ^ 2 * (θ ρ) ^ 2 + ε * ρ + 1 = 0 := by
      have h := hQ
      rw [hA, hB] at h
      have : b ^ 2 * (ρ ^ 2 * (θ ρ) ^ 2 + ε * ρ + 1) = 0 := by
        rw [← h]; ring
      rcases mul_eq_zero.mp this with h' | h'
      · exact absurd h' hb2ne
      · exact h'
    have hρne : ρ ≠ 0 := by
      intro h
      have hγ0 : γ = 0 := by rw [hγeq, h, zero_mul, zero_div]
      exact hγne hγ0
    have hkey : ε = ρ⁻¹ + θ ρ ^ 2 * ρ := by
      have h2 : ρ ^ 2 * (θ ρ) ^ 2 = ε * ρ + 1 :=
        AddExpTwo.eq_of_add_eq_zero (by rw [← add_assoc]; exact hzero)
      have h1 : ε * ρ = ρ ^ 2 * (θ ρ) ^ 2 + 1 := by
        rw [h2, add_assoc, CharTwo.add_self_eq_zero, add_zero]
      have h3 : ε = (ρ ^ 2 * (θ ρ) ^ 2 + 1) / ρ := by
        rw [← h1]; field_simp
      rw [h3]
      field_simp
      ring
    exact hρ ρ hkey

/-- **Anisotropy of the `D` squaring form.**  Here `θ ^ 5 = 1` (Higman's condition on the
family `D`, together with `θ ≠ 1` and `5 ∣ n`) and `ε ≠ ρ⁻¹ + θ⁴ρ · θρ · ρ⁻¹` for all `ρ`; then
`dCocycle F θ ε u u ≠ 0` for `u ≠ 0`. -/
theorem dCocycle_anisotropic {F : Type*} [Field F] [CharP F 2] (θ : F ≃+* F) (ε : F)
    (hθ : θ ^ 5 = 1)
    (hρ : ∀ ρ : F, ε ≠ ρ⁻¹ + θ (θ (θ (θ ρ))) * θ ρ * ρ⁻¹)
    (u : F × F) (hu : u ≠ 0) : dCocycle F θ ε u u ≠ 0 := by
  obtain ⟨a, b⟩ := u
  have h5 : ∀ x : F, θ (θ (θ (θ (θ x)))) = x := by
    intro x
    have h := congrArg (fun f : F ≃+* F => f x) hθ
    rw [show (θ ^ 5) x = θ (θ (θ (θ (θ x)))) from rfl] at h
    simpa using h
  show a * θ a + ε * (θ (θ (θ a)) * θ b) + b * θ (θ b) ≠ 0
  intro hQ
  rcases eq_or_ne b 0 with hb | hb
  · subst hb
    simp only [map_zero, mul_zero, zero_mul, add_zero] at hQ
    have ha : a ≠ 0 := fun h => hu (by simp [h])
    have hθa : θ a ≠ 0 := fun h => ha (θ.injective (by rw [h, map_zero]))
    exact mul_ne_zero ha hθa hQ
  · have hbne : b ≠ 0 := hb
    have hμne : θ b ≠ 0 := fun h => hbne (θ.injective (by rw [h, map_zero]))
    have hνne : θ (θ b) ≠ 0 := fun h => hμne (θ.injective (by rw [h, map_zero]))
    have hωne : θ (θ (θ b)) ≠ 0 := fun h => hνne (θ.injective (by rw [h, map_zero]))
    have hκne : θ (θ (θ (θ b))) ≠ 0 := fun h => hωne (θ.injective (by rw [h, map_zero]))
    have hbνne : b * θ (θ b) ≠ 0 := mul_ne_zero hbne hνne
    set ρ : F := a * θ (θ (θ b)) / (θ (θ b) * θ (θ (θ (θ b)))) with hρdef
    have haeq : a = ρ * (θ (θ b) * θ (θ (θ (θ b)))) / θ (θ (θ b)) := by
      rw [hρdef]; field_simp [hνne, hωne, hκne]
    have hθaeq : θ a = θ ρ * (θ (θ (θ b)) * b) / θ (θ (θ (θ b))) := by
      rw [haeq]
      simp only [map_div₀, map_mul]
      rw [h5 b]
    have hθ3aeq : θ (θ (θ a)) = θ (θ (θ ρ)) * (b * θ (θ b)) / θ b := by
      rw [haeq]
      simp only [map_div₀, map_mul]
      simp only [h5 b, h5 (θ b), h5 (θ (θ b))]
    have hmain : a * θ a + ε * (θ (θ (θ a)) * θ b) + b * θ (θ b) =
        (b * θ (θ b)) * (ρ * θ ρ + ε * θ (θ (θ ρ)) + 1) := by
      rw [hθ3aeq, hθaeq, haeq]
      field_simp
    have hzero : ρ * θ ρ + ε * θ (θ (θ ρ)) + 1 = 0 := by
      have h := hQ
      rw [hmain] at h
      rcases mul_eq_zero.mp h with h' | h'
      · exact absurd h' hbνne
      · exact h'
    have hρne : ρ ≠ 0 := by
      intro h
      have ha0 : a = 0 := by rw [haeq, h, zero_mul, zero_div]
      have hQ0 : b * θ (θ b) = 0 := by simpa [ha0] using hQ
      exact hbνne hQ0
    have hθρne : θ ρ ≠ 0 := fun h => hρne (θ.injective (by rw [h, map_zero]))
    have hθ3ρne : θ (θ (θ ρ)) ≠ 0 := by
      intro h
      have h1 : θ ρ = 0 := by
        have h3 : θ (θ (θ ρ)) = θ (θ (θ 0)) := by rw [h, map_zero, map_zero, map_zero]
        have h4 := θ.injective h3
        have h5 := θ.injective h4
        rw [map_zero] at h5
        exact h5
      exact hρne (θ.injective (by rw [h1, map_zero]))
    have hε : ε = (ρ * θ ρ + 1) / θ (θ (θ ρ)) := by
      have h1 : ε * θ (θ (θ ρ)) = ρ * θ ρ + 1 := by
        have h2 : ρ * θ ρ = ε * θ (θ (θ ρ)) + 1 :=
          AddExpTwo.eq_of_add_eq_zero (by rw [← add_assoc]; exact hzero)
        rw [h2, add_assoc, CharTwo.add_self_eq_zero, add_zero]
      rw [← h1, mul_div_cancel_right₀ ε hθ3ρne]
    set σ : F := θ (θ (θ ρ)) / (θ ρ * ρ) with hσdef
    have hσinv : σ⁻¹ = θ ρ * ρ / θ (θ (θ ρ)) := by
      rw [hσdef, inv_div]
    have h4σ : θ (θ (θ (θ σ))) = θ (θ ρ) / (ρ * θ (θ (θ (θ ρ)))) := by
      rw [hσdef]
      simp only [map_div₀, map_mul]
      simp only [h5 ρ, h5 (θ (θ ρ))]
    have h1σ : θ σ = θ (θ (θ (θ ρ))) / (θ (θ ρ) * θ ρ) := by
      rw [hσdef, map_div₀, map_mul]
    have hθ2ρne : θ (θ ρ) ≠ 0 := by
      intro h
      rw [← map_zero θ] at h
      exact hθρne (θ.injective h)
    have hθ4ρne : θ (θ (θ (θ ρ))) ≠ 0 := by
      intro h
      rw [← map_zero θ] at h
      exact hθ3ρne (θ.injective h)
    have hkey : ε = σ⁻¹ + θ (θ (θ (θ σ))) * θ σ * σ⁻¹ := by
      rw [hε, hσinv, h4σ, h1σ]
      field_simp [hρne, hθρne, hθ2ρne, hθ3ρne, hθ4ρne]
    exact hρ σ hkey

end Work.Higman
