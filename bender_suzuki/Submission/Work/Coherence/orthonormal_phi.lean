import Mathlib
import Submission.Work.Coherence.Basic

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.Coherence

/-- **The orthonormality of the shift of an isometry.**

Let `S` be an orthonormal finite set of class functions on `H`, all of the same degree (`x 1`
is independent of `x ∈ S`, witnessed at `x₀ ∈ S`), and let `τ` be an integral linear map that is
an isometry on `ℤ[S]^0`.  Any map `φ : (H → ℂ) → (G → ℂ)` which differs from `τ` by a *constant*
on `S` (`φ x - τ x` does not depend on `x ∈ S`) and which reproduces the inner products of `x₀`
against the elements of `S` (`⟨φ x₀, φ x⟩ = ⟨x₀, x⟩`) is itself orthonormal on `S`.

This is the elementary computation underlying the coherence argument of Feit–Thompson §10: a
"minimal" extension of the Dade isometry is automatically again an isometry on the lattice
spanned by `S`. -/
theorem orthonormal_phi {H G : Type*} [Group H] [Fintype H] [Group G] [Fintype G]
    {S : Finset (H → ℂ)} {τ : (H → ℂ) →ₗ[ℤ] (G → ℂ)} (hS : Orthonormal S)
    {x₀ : H → ℂ} (hx₀ : x₀ ∈ S) (hdeg : ∀ x ∈ S, x 1 = x₀ 1)
    (hτ : IsometryOn S τ) {φ : (H → ℂ) → (G → ℂ)}
    (hφorth : ∀ x ∈ S, cfInner (φ x₀) (φ x) = cfInner x₀ x)
    (hφshift : ∀ x ∈ S, φ x - τ x = φ x₀ - τ x₀) :
    ∀ x ∈ S, ∀ y ∈ S, cfInner (φ x) (φ y) = if x = y then 1 else 0 := by
  intro x hx y hy
  -- `x₀ - z ∈ ℤ[S]^0` for every `z ∈ S`, because all elements of `S` have the same degree.
  have hspan : ∀ z ∈ S, x₀ - z ∈ ZSpan0 S := by
    intro z hz
    refine mem_zSpan0.mpr ⟨?_, ?_⟩
    · exact AddSubgroup.sub_mem _ (self_mem_zSpan hx₀) (self_mem_zSpan hz)
    · simp [Pi.sub_apply, hdeg z hz]
  -- `φ` is `τ` plus a constant on `S`: `φ x₀ - φ z = τ x₀ - τ z`.
  have hsub : ∀ z ∈ S, φ x₀ - φ z = τ x₀ - τ z := by
    intro z hz
    linear_combination -hφshift z hz
  have hkey := hτ.inner_eq (x₀ - x) (hspan x hx) (x₀ - y) (hspan y hy)
  have e1 : τ (x₀ - x) = φ x₀ - φ x := by rw [map_sub]; exact (hsub x hx).symm
  have e2 : τ (x₀ - y) = φ x₀ - φ y := by rw [map_sub]; exact (hsub y hy).symm
  have hkey' : cfInner (φ x₀ - φ x) (φ x₀ - φ y) = cfInner (x₀ - x) (x₀ - y) := by
    rw [← e1, ← e2]; exact hkey
  have hselfS : cfInner x₀ x₀ = 1 := hS.cfInner_self hx₀
  have hselfP : cfInner (φ x₀) (φ x₀) = 1 := by rw [hφorth x₀ hx₀, hselfS]
  have hconj : cfInner (φ x) (φ x₀) = cfInner x x₀ := by
    rw [cfInner_conj_symm, hφorth x hx, ← cfInner_conj_symm x x₀]
  -- Expand both sides of `hkey'` and cancel the common terms.
  rw [cfInner_sub_left, cfInner_sub_right, cfInner_sub_right,
      cfInner_sub_left, cfInner_sub_right, cfInner_sub_right,
      hselfP, hconj, hφorth y hy, hselfS] at hkey'
  rw [← hS x hx y hy]
  linear_combination hkey'

end Work.Coherence
