import Mathlib
import Submission.Work.SSGRoute.TPatom.orbitBlockSystem
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The Shapiro transversal compatible with the block system

This file adds, to the block system `Work.SSGRoute.TPatom.exists_orbitBlockSystem`, the *transversal*
`c : Γ → Γ → ↥H` of the Shapiro `1`-cocycle, chosen so that the block representatives `x ∈ X` are
fixed points of the underlying section.  The last clause

  `c x (d ^ f) = x * d ^ f * x⁻¹`   for every `x ∈ X`

is the one the value formula `Work.Sha2Lib.coindValueFormula_orbits` uses: it makes the detected
element `c x d^f` literally a conjugate of the telescoped element `d^f`, i.e. the Frobenius of the
place of the block `x` (see `Submission/Work/SSGRoute/NOTE_TPatom_route.md`).

Everything here is pure group theory and `sorry`-free.
-/

namespace Work.SSGRoute.TPatom

/-- **The block system together with its Shapiro transversal.** -/
theorem exists_blockSystem_transversal {Γ : Type} [Group Γ] [Fintype Γ] [DecidableEq Γ]
    (H : Subgroup Γ) (hH : H.Normal) (D : Subgroup Γ) (d : ↥D) (f : ℕ) (hfpos : 0 < f)
    (hdH : ((d : Γ)) ^ f ∈ H)
    (hdgen : ∀ δ : ↥D, ∃ m : ℕ, ((δ : Γ))⁻¹ * (d : Γ) ^ m ∈ H)
    (hfmin : ∀ m : ℕ, 0 < m → m < f → ((d : Γ) ^ m) ∉ H) :
    ∃ (X : Finset Γ) (c : Γ → Γ → ↥H),
      (∀ γ : Γ, ∃! q : Γ × Fin f, q.1 ∈ X ∧ γ * (q.1 * (d : Γ) ^ (q.2 : ℕ))⁻¹ ∈ H) ∧
      (∀ x ∈ X, ∀ δ : ↥D, ∃ j : Fin f, (x * (δ : Γ)) * (x * (d : Γ) ^ (j : ℕ))⁻¹ ∈ H) ∧
      (∀ g γ γ' : Γ,
        ((c g (γ * γ') : ↥H) : Γ) = ((c g γ : ↥H) : Γ) * ((c (g * γ) γ' : ↥H) : Γ)) ∧
      (∀ g : Γ, ((c g 1 : ↥H) : Γ) = 1) ∧
      (∀ (g γ : Γ) (n : ↥H), c ((n : Γ) * g) γ = c g γ) ∧
      (∀ x ∈ X, ((c x ((d : Γ) ^ f) : ↥H) : Γ) = x * (d : Γ) ^ f * x⁻¹) := by
  classical
  obtain ⟨X, hpart, hblock⟩ := exists_orbitBlockSystem H hH D d f hfpos hdH hdgen hfmin
  -- the block coordinate of a group element, and the induced section
  let rep : Γ → Γ × Fin f := fun γ => Classical.choose (hpart γ)
  have hrep : ∀ γ : Γ, (rep γ).1 ∈ X ∧
      γ * ((rep γ).1 * (d : Γ) ^ ((rep γ).2 : ℕ))⁻¹ ∈ H :=
    fun γ => (Classical.choose_spec (hpart γ)).1
  have hrepuniq : ∀ (γ : Γ) (q : Γ × Fin f),
      (q.1 ∈ X ∧ γ * (q.1 * (d : Γ) ^ (q.2 : ℕ))⁻¹ ∈ H) → q = rep γ :=
    fun γ q hq => (Classical.choose_spec (hpart γ)).2 q hq
  let s : Γ → Γ := fun γ => (rep γ).1 * (d : Γ) ^ ((rep γ).2 : ℕ)
  -- `s γ` lies in the left coset `H γ`
  have hs_coset : ∀ γ : Γ, ∃ h ∈ H, s γ = h * γ := by
    intro γ
    obtain ⟨-, hmem⟩ := hrep γ
    refine ⟨(γ * (s γ)⁻¹)⁻¹, H.inv_mem hmem, ?_⟩
    show s γ = (γ * (s γ)⁻¹)⁻¹ * γ
    group
  -- the section is invariant under the left `H`-action
  have hs_inv : ∀ (n : Γ), n ∈ H → ∀ γ : Γ, s (n * γ) = s γ := by
    intro n hn γ
    have hvalid : (rep γ).1 ∈ X ∧ (n * γ) * ((rep γ).1 * (d : Γ) ^ ((rep γ).2 : ℕ))⁻¹ ∈ H :=
      ⟨(hrep γ).1, by
        have hmem := (hrep γ).2
        have h1 : (n * γ) * (s γ)⁻¹ = n * (γ * (s γ)⁻¹) := by group
        rw [h1]
        exact H.mul_mem hn hmem⟩
    have huniq := hrepuniq (n * γ) (rep γ) hvalid
    dsimp only [s]
    rw [← huniq]
  -- the section fixes the block representatives
  have hs_self : ∀ x ∈ X, s x = x := by
    intro x hx
    have hvalid : x ∈ X ∧ x * (x * (d : Γ) ^ ((⟨0, hfpos⟩ : Fin f) : ℕ))⁻¹ ∈ H :=
      ⟨hx, by simp⟩
    have huniq := hrepuniq x (x, ⟨0, hfpos⟩) hvalid
    dsimp only [s]
    rw [← huniq]
    simp
  have hs_df : ∀ x ∈ X, s (x * (d : Γ) ^ f) = x := by
    intro x hx
    have hvalid : x ∈ X ∧
        (x * (d : Γ) ^ f) * (x * (d : Γ) ^ ((⟨0, hfpos⟩ : Fin f) : ℕ))⁻¹ ∈ H :=
      ⟨hx, by
        simp only [pow_zero, mul_one]
        exact hH.conj_mem ((d : Γ) ^ f) hdH x⟩
    have huniq := hrepuniq (x * (d : Γ) ^ f) (x, ⟨0, hfpos⟩) hvalid
    dsimp only [s]
    rw [← huniq]
    simp
  -- the Shapiro transversal
  let c : Γ → Γ → ↥H := fun g γ =>
    ⟨s g * γ * (s (g * γ))⁻¹, by
      obtain ⟨h₁, hh₁, h₁eq⟩ := hs_coset g
      obtain ⟨h₂, hh₂, h₂eq⟩ := hs_coset (g * γ)
      have hkey : s g * γ * (s (g * γ))⁻¹ = h₁ * h₂⁻¹ := by
        rw [h₁eq, h₂eq]
        group
      rw [hkey]
      exact H.mul_mem hh₁ (H.inv_mem hh₂)⟩
  have hcmul : ∀ g γ γ' : Γ,
      ((c g (γ * γ') : ↥H) : Γ) = ((c g γ : ↥H) : Γ) * ((c (g * γ) γ' : ↥H) : Γ) := by
    intro g γ γ'
    dsimp only [c, s]
    show (rep g).1 * (d : Γ) ^ ((rep g).2 : ℕ) * (γ * γ')
        * ((rep (g * (γ * γ'))).1 * (d : Γ) ^ ((rep (g * (γ * γ'))).2 : ℕ))⁻¹
      = ((rep g).1 * (d : Γ) ^ ((rep g).2 : ℕ) * γ
          * ((rep (g * γ)).1 * (d : Γ) ^ ((rep (g * γ)).2 : ℕ))⁻¹)
        * ((rep (g * γ)).1 * (d : Γ) ^ ((rep (g * γ)).2 : ℕ) * γ'
          * ((rep ((g * γ) * γ')).1 * (d : Γ) ^ ((rep ((g * γ) * γ')).2 : ℕ))⁻¹)
    rw [← mul_assoc g γ γ']
    group
  have hcunit : ∀ g : Γ, ((c g 1 : ↥H) : Γ) = 1 := by
    intro g
    dsimp only [c, s]
    show (rep g).1 * (d : Γ) ^ ((rep g).2 : ℕ) * 1
        * ((rep (g * 1)).1 * (d : Γ) ^ ((rep (g * 1)).2 : ℕ))⁻¹ = 1
    rw [mul_one, mul_one, mul_inv_cancel]
  have hcoinv : ∀ (g γ : Γ) (n : ↥H), c ((n : Γ) * g) γ = c g γ := by
    intro g γ n
    apply Subtype.ext
    dsimp only [c, s]
    show (rep ((n : Γ) * g)).1 * (d : Γ) ^ ((rep ((n : Γ) * g)).2 : ℕ) * γ
        * ((rep (((n : Γ) * g) * γ)).1 * (d : Γ) ^ ((rep (((n : Γ) * g) * γ)).2 : ℕ))⁻¹
      = (rep g).1 * (d : Γ) ^ ((rep g).2 : ℕ) * γ
        * ((rep (g * γ)).1 * (d : Γ) ^ ((rep (g * γ)).2 : ℕ))⁻¹
    have h1 : s ((n : Γ) * g) = s g := hs_inv (n : Γ) n.2 g
    have h2 : s (((n : Γ) * g) * γ) = s (g * γ) := by
      rw [mul_assoc]
      exact hs_inv (n : Γ) n.2 (g * γ)
    dsimp only [s] at h1 h2
    rw [h1, h2]
  refine ⟨X, c, hpart, hblock, hcmul, hcunit, hcoinv, ?_⟩
  intro x hx
  dsimp only [c, s]
  show (rep x).1 * (d : Γ) ^ ((rep x).2 : ℕ) * (d : Γ) ^ f
      * ((rep (x * (d : Γ) ^ f)).1 * (d : Γ) ^ ((rep (x * (d : Γ) ^ f)).2 : ℕ))⁻¹
    = x * (d : Γ) ^ f * x⁻¹
  have h1 : s x = x := hs_self x hx
  have h2 : s (x * (d : Γ) ^ f) = x := hs_df x hx
  dsimp only [s] at h1 h2
  rw [h1, h2]

end Work.SSGRoute.TPatom
