import Mathlib
import Submission.Work.ZassenhausSuzuki.TitsAux

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.ZassenhausSuzuki

theorem TitsCoordIdentities {K : Type*} [Field K] [CharP K 2] (θ : K ≃+* K) :
    (∀ lam nu : K, Work.ZassenhausSuzuki.SzA.hLam θ lam (Work.ZassenhausSuzuki.Xrep θ nu)
        = (⟨lam * (1 + nu), lam * θ lam * (θ nu * (1 + nu))⟩ :
            Work.ZassenhausSuzuki.SzA K θ)) ∧
    (∀ al nu s : K, al ≠ 0 → 1 + nu ≠ 0 → s = al * θ al → θ nu * (1 + s) = s →
        Work.ZassenhausSuzuki.SzA.hLam θ (al⁻¹ / (1 + nu))
            (Work.ZassenhausSuzuki.Xrep θ nu) = (⟨al⁻¹, 1⟩ : Work.ZassenhausSuzuki.SzA K θ)) ∧
    (∀ nu s : K, nu ≠ 0 → 1 + nu ≠ 0 → s * (1 + θ nu) = θ nu →
        Work.ZassenhausSuzuki.SzA.hLam θ (nu / (1 + nu))
            (Work.ZassenhausSuzuki.Xrep θ nu⁻¹) = (⟨1, 1 + s⟩ : Work.ZassenhausSuzuki.SzA K θ)) ∧
    (∀ nu xi : K, nu ≠ 0 → xi * θ xi = 1 + nu⁻¹ * θ nu⁻¹ →
        (nu * xi) * θ (nu * xi) = 1 + nu * θ nu) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- the first identity is the definition of `h_λ` evaluated at `X_ν`
    intro lam nu
    rfl
  · -- HB III XI 11.13 (b), first half: `h_{α⁻¹/(1+ν)}(X_ν) = (α⁻¹, 1)`
    intro al nu s hal hnu hs h1
    have hθal : θ al ≠ 0 := fun h => hal (θ.injective (by rw [h, map_zero]))
    refine SzA.ext ?_ ?_
    · simp only [SzA.hLam_a, Xrep_a]
      field_simp
    · simp only [SzA.hLam_b, Xrep_b]
      rw [map_div₀, map_add, map_one, map_inv₀]
      subst hs
      have hθnu0 : 1 + θ nu ≠ 0 := by
        have h : θ (1 + nu) ≠ 0 := fun hh => hnu (θ.injective (by rw [hh, map_zero]))
        simpa using h
      have h1' : θ nu + θ nu * (al * θ al) = al * θ al := by
        have h := h1
        rw [mul_add, mul_one] at h
        exact h
      field_simp
      rw [mul_add, mul_one, mul_comm (al * θ al) (θ nu)]
      exact (sub_eq_iff_eq_add).mp (by rw [CharTwo.sub_eq_add]; exact h1')
  · -- HB III XI 11.13 (b), second half: `h_{ν/(1+ν)}(X_{ν⁻¹}) = (1, 1+s)`
    intro nu s hnu h1nu h
    have hθν0 : θ nu ≠ 0 := fun hh => hnu (θ.injective (by rw [hh, map_zero]))
    have h1θν0 : 1 + θ nu ≠ 0 := by
      intro hh
      have : θ nu = 0 := by rw [← h, hh, mul_zero]
      exact hθν0 this
    have hkey : (1 + θ nu) * (1 + s) = 1 := by
      rw [mul_comm, add_mul, one_mul, h, add_assoc, CharTwo.add_self_eq_zero, add_zero]
    refine SzA.ext ?_ ?_
    · simp only [SzA.hLam_a, Xrep_a]
      field_simp
      exact add_comm nu 1
    · simp only [SzA.hLam_b, Xrep_b]
      rw [map_div₀, map_add, map_one, map_inv₀]
      field_simp
      rw [mul_assoc, hkey, mul_one]
      exact add_comm nu 1
  · -- the auxiliary unit `ξ`, with `ξ·θξ = 1 + ν⁻¹·θ(ν⁻¹)`, rescales `ν`
    intro nu xi hnu h
    have hθν0 : θ nu ≠ 0 := fun hh => hnu (θ.injective (by rw [hh, map_zero]))
    rw [map_inv₀] at h
    have hnu_inv : nu * nu⁻¹ = 1 := mul_inv_cancel₀ hnu
    have hθnu_inv : θ nu * (θ nu)⁻¹ = 1 := mul_inv_cancel₀ hθν0
    rw [map_mul]
    calc (nu * xi) * (θ nu * θ xi) = nu * θ nu * (xi * θ xi) := by ring
      _ = nu * θ nu * (1 + nu⁻¹ * (θ nu)⁻¹) := by rw [h]
      _ = 1 + nu * θ nu := by
          rw [mul_add, mul_one,
            show nu * θ nu * (nu⁻¹ * (θ nu)⁻¹)
                = (nu * nu⁻¹) * (θ nu * (θ nu)⁻¹) by ring,
            hnu_inv, hθnu_inv, mul_one]
          exact add_comm (nu * θ nu) 1

end Work.ZassenhausSuzuki
