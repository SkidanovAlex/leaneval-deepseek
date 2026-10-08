/-
Copyright (c) 2024. All rights reserved.

# The eigenvalue argument for Higman's Lemma 8

This file isolates the linear-algebra core of the proof of `Work.Higman.SZ.lemma8`
(Higman 1963, *Suzuki 2-groups*, Lemma 8), namely the "eigenvalue bookkeeping" which
shows that a certain quadratic map must vanish.

The setting is a field `K`, three `K`-vector spaces `V`, `W`, `U`, a `K`-linear
endomorphism `ηV`, `ηW`, `ηU` of each, a nondegenerate bilinear form `B : V →ₗ V →ₗ W`,
a bilinear map `θ : V →ₗ W →ₗ U`, an injective linear map `σ : W →ₗ U`, and a
`K`-quadratic map `s : V → W` whose polar form is `B`.  All the data is required to be
`η`-equivariant, and the key relation is

`θ y (s x) + θ x (B x y) = σ (B x y)` for all `x y : V`.

Assuming that `W` has no nonzero `η`-fixed vectors and that `V` is spanned by
eigenvectors of `ηV`, one shows `s ≡ 0`.

The proof: if `x` is an eigenvector of `ηV` with eigenvalue `μ ≠ 1` and `y` an eigenvector
with eigenvalue `ν ≠ 0`, then in the relation above the right hand side has `η`-weight
`μ * ν`, whereas (using that `s (μ • x) = μ ^ 2 • s x`) both terms on the left have weight
`μ ^ 2 * ν`; as `μ ≠ 1`, `μ ≠ 0`, `ν ≠ 0` these weights differ, so `σ (B x y) = 0` and
`B x y = 0`.  Hence every eigenvector with eigenvalue `≠ 1` is killed by the nondegenerate
form `B`, so is `0`; consequently `V` is spanned by `η`-fixed vectors, i.e. `ηV = id`, and
then `η (s x) = s (η x) = s x` forces `s x = 0` for each `x`.
-/

import Mathlib

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option autoImplicit false

namespace Work.Higman.SZ

/-- A vector space is spanned by eigenvectors of the endomorphism `η`.  This is the
hypothesis that `η` is diagonalizable over the (large enough) field `K`. -/
def SpannedByEigen {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    (η : V →ₗ[K] V) : Prop :=
  ∀ v : V, ∃ (n : ℕ) (μ : Fin n → K) (x : Fin n → V) (c : Fin n → K),
    (∀ i, η (x i) = μ i • x i) ∧ v = ∑ i, c i • x i

/-- **The eigenvalue argument.**  See the module docstring for the precise setting. -/
theorem eigen_arg {K V W U : Type*} [Field K]
    [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W] [AddCommGroup U] [Module K U]
    (ηV : V →ₗ[K] V) (ηW : W →ₗ[K] W) (ηU : U →ₗ[K] U)
    (hinjV : Function.Injective ηV)
    (B : V →ₗ[K] V →ₗ[K] W) (hBnondeg : ∀ x, (∀ y, B x y = 0) → x = 0)
    (θ : V →ₗ[K] W →ₗ[K] U) (σ : W →ₗ[K] U) (hσ : Function.Injective σ)
    (s : V → W) (hssmul : ∀ (a : K) (x : V), s (a • x) = a^2 • s x)
    (hBη : ∀ x y, B (ηV x) (ηV y) = ηW (B x y))
    (hθη : ∀ x w, θ (ηV x) (ηW w) = ηU (θ x w))
    (hση : ∀ w, σ (ηW w) = ηU (σ w))
    (hsη : ∀ x, s (ηV x) = ηW (s x))
    (hf : ∀ x y, θ y (s x) + θ x (B x y) = σ (B x y))
    (hV : SpannedByEigen ηV)
    (hfixW : ∀ w, ηW w = w → w = 0) :
    ∀ x, s x = 0 := by
  -- Step 1: a pair of eigenvectors with `μ ≠ 1` is orthogonal under `B`.
  have wf : ∀ (x : V) (μ : K), ηV x = μ • x → μ ≠ 0 →
      ∀ (y : V) (ν : K), ηV y = ν • y → ν ≠ 0 → μ ≠ 1 → B x y = 0 := by
    intro x μ hx hμ0 y ν hy hν0 hμ1
    have h1 : ηU (θ y (s x)) = (μ^2 * ν) • θ y (s x) := by
      rw [← hθη y (s x), hy, ← hsη x, hx, hssmul]
      simp only [LinearMap.smul_apply, map_smul, smul_smul, mul_comm]
    have h2 : ηU (θ x (B x y)) = (μ^2 * ν) • θ x (B x y) := by
      rw [← hθη x (B x y), hx, ← hBη x y, hx, hy]
      simp only [LinearMap.smul_apply, map_smul, smul_smul]
      congr 1
      ring
    have h3 : ηU (σ (B x y)) = (μ * ν) • σ (B x y) := by
      rw [← hση (B x y), ← hBη x y, hx, hy]
      simp only [LinearMap.smul_apply, map_smul, smul_smul, mul_comm]
    have h4 := congrArg ηU (hf x y)
    rw [map_add, h1, h2, h3] at h4
    have h5 : (μ^2 * ν) • σ (B x y) = (μ * ν) • σ (B x y) := by
      rw [← h4, ← smul_add, hf x y]
    have h6 : (μ^2 * ν - μ * ν) • σ (B x y) = 0 := by
      rw [sub_smul, h5, sub_self]
    have h7 : μ^2 * ν - μ * ν ≠ 0 := by
      intro hc
      have h8 : μ * ν * (μ - 1) = 0 := by linear_combination hc
      rcases mul_eq_zero.mp h8 with h | h
      · rcases mul_eq_zero.mp h with h' | h'
        · exact hμ0 h'
        · exact hν0 h'
      · exact hμ1 (sub_eq_zero.mp h)
    have h9 : σ (B x y) = 0 := by
      rcases smul_eq_zero.mp h6 with h | h
      · exact absurd h h7
      · exact h
    exact hσ (by rw [h9, map_zero])
  -- Step 2: eigenvectors with eigenvalue `≠ 1` vanish.
  have vlast : ∀ (x : V) (μ : K), ηV x = μ • x → μ ≠ 1 → x = 0 := by
    intro x μ hx hμ1
    rcases eq_or_ne x 0 with h | h
    · exact h
    · have hμ0 : μ ≠ 0 := by
        intro h0
        rw [h0, zero_smul] at hx
        exact h (hinjV (by rw [hx, map_zero]))
      apply hBnondeg x
      intro y
      obtain ⟨n, ν, z, c, hz, hy⟩ := hV y
      rw [hy, map_sum]
      apply Finset.sum_eq_zero
      intro i _
      rw [map_smul]
      rcases eq_or_ne (z i) 0 with hzi | hzi
      · rw [hzi, map_zero, smul_zero]
      · have hν0 : ν i ≠ 0 := by
          intro h0
          have hh := hz i
          rw [h0, zero_smul] at hh
          exact hzi (hinjV (by rw [hh, map_zero]))
        rw [wf x μ hx hμ0 (z i) (ν i) (hz i) hν0 hμ1, smul_zero]
  -- Step 3: `ηV` is the identity, since `V` is spanned by eigenvectors.
  have hidV : ∀ x, ηV x = x := by
    intro x
    obtain ⟨n, ν, z, c, hz, hy⟩ := hV x
    have hzfix : ∀ i, ηV (z i) = z i := by
      intro i
      rcases eq_or_ne (z i) 0 with h | h
      · rw [h, map_zero]
      · rw [hz i]
        have h1 : ν i = 1 := by
          by_contra hν
          exact h (vlast (z i) (ν i) (hz i) hν)
        rw [h1, one_smul]
    rw [hy, map_sum]
    exact Finset.sum_congr rfl (fun i _ => by rw [map_smul, hzfix i])
  -- Step 4: `s` takes values in the fixed points of `ηW`, which are trivial.
  intro x
  have hh := hsη x
  rw [hidV x] at hh
  exact hfixW (s x) hh.symm

end Work.Higman.SZ
