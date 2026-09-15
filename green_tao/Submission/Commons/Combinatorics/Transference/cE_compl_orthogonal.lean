import Mathlib
import Submission.Commons.Combinatorics.Transference.condExp_selfadjoint

namespace Commons.Combinatorics.Transference

open Finset
open scoped BigOperators

/-- **Orthogonality of the complement-weighted residual against the refinement difference.**

`P`, `Q` are finite σ-algebras on a finite type `X` presented by their atoms (`P x` is the atom
containing `x`), with `Q` refining `P`; `Ω` is a union of `P`-atoms.  Then the function
`(1 - 1_Ω)·𝔼(f|P)` is orthogonal to `𝔼(f|Q) - 𝔼(f|P)`, where `𝔼(f|part) x` is the average of `f`
over the atom `part x`.  (The identity is used in the Furstenberg tower step, Green–Tao Prop. 7.2.) -/
theorem cE_compl_orthogonal {X : Type*} [Fintype X] [DecidableEq X]
    (P Q : X → Finset X) (hPmem : ∀ x, x ∈ P x)
    (hPeq : ∀ x y : X, y ∈ P x → P y = P x) (hQmem : ∀ x, x ∈ Q x)
    (hQeq : ∀ x y : X, y ∈ Q x → Q y = Q x) (href : ∀ x, Q x ⊆ P x)
    {Ω : Finset X} (hΩ : ∀ x ∈ Ω, P x ⊆ Ω) (f : X → ℝ) :
    ∑ x, (if x ∈ Ω then (0 : ℝ) else 1)
        * ((((P x).card : ℝ)⁻¹ * ∑ y ∈ P x, f y)
          * (((Q x).card : ℝ)⁻¹ * ∑ y ∈ Q x, f y - ((P x).card : ℝ)⁻¹ * ∑ y ∈ P x, f y)) = 0 := by
  -- The complement weight `1 - 1_Ω` is constant on `P`-atoms, because `Ω` is a union of them.
  have hwP : ∀ x y : X, y ∈ P x →
      (if y ∈ Ω then (0 : ℝ) else 1) = (if x ∈ Ω then (0 : ℝ) else 1) := by
    intro x y hy
    by_cases hx : x ∈ Ω
    · have hyΩ : y ∈ Ω := hΩ x hx hy
      rw [if_pos hyΩ, if_pos hx]
    · have hyΩ : y ∉ Ω := by
        intro hyΩ
        have hxΩ : x ∈ Ω := hΩ y hyΩ (by rw [hPeq x y hy]; exact hPmem x)
        exact hx hxΩ
      rw [if_neg hyΩ, if_neg hx]
  -- `𝔼(f|P)` is constant on `P`-atoms.
  have hcP : ∀ x y : X, y ∈ P x →
      ((P y).card : ℝ)⁻¹ * ∑ z ∈ P y, f z = ((P x).card : ℝ)⁻¹ * ∑ z ∈ P x, f z := by
    intro x y hy
    rw [hPeq x y hy]
  -- Hence `h x = (1 - 1_Ω x) * 𝔼(f|P) x` is constant on `P`-atoms, ...
  have hhP : ∀ x y : X, y ∈ P x →
      (if y ∈ Ω then (0 : ℝ) else 1) * (((P y).card : ℝ)⁻¹ * ∑ z ∈ P y, f z)
        = (if x ∈ Ω then (0 : ℝ) else 1) * (((P x).card : ℝ)⁻¹ * ∑ z ∈ P x, f z) := by
    intro x y hy
    rw [hwP x y hy, hcP x y hy]
  -- ... and therefore also constant on `Q`-atoms, since `Q` refines `P`.
  have hhQ : ∀ x y : X, y ∈ Q x →
      (if y ∈ Ω then (0 : ℝ) else 1) * (((P y).card : ℝ)⁻¹ * ∑ z ∈ P y, f z)
        = (if x ∈ Ω then (0 : ℝ) else 1) * (((P x).card : ℝ)⁻¹ * ∑ z ∈ P x, f z) := by
    intro x y hy
    exact hhP x y (href x hy)
  -- Self-adjointness of the `Q`-conditional expectation against the `Q`-measurable weight.
  have h1 := condExp_selfadjoint Q hQmem hQeq f
      (fun x => (if x ∈ Ω then (0 : ℝ) else 1) * (((P x).card : ℝ)⁻¹ * ∑ z ∈ P x, f z)) hhQ
  -- Self-adjointness of the `P`-conditional expectation against the same weight.
  have h2 := condExp_selfadjoint P hPmem hPeq f
      (fun x => (if x ∈ Ω then (0 : ℝ) else 1) * (((P x).card : ℝ)⁻¹ * ∑ z ∈ P x, f z)) hhP
  -- Expand the summand: `w·(E_P f)·(E_Q f - E_P f) = (E_Q f)·h - (E_P f)·h` with `h = w·E_P f`.
  have hT : ∑ x, (if x ∈ Ω then (0 : ℝ) else 1)
        * ((((P x).card : ℝ)⁻¹ * ∑ z ∈ P x, f z)
          * (((Q x).card : ℝ)⁻¹ * ∑ z ∈ Q x, f z - ((P x).card : ℝ)⁻¹ * ∑ z ∈ P x, f z))
      = ∑ x, ((((Q x).card : ℝ)⁻¹ * ∑ z ∈ Q x, f z)
            * ((if x ∈ Ω then (0 : ℝ) else 1) * (((P x).card : ℝ)⁻¹ * ∑ z ∈ P x, f z))
          - (((P x).card : ℝ)⁻¹ * ∑ z ∈ P x, f z)
            * ((if x ∈ Ω then (0 : ℝ) else 1) * (((P x).card : ℝ)⁻¹ * ∑ z ∈ P x, f z))) := by
    apply Finset.sum_congr rfl
    intro x _
    ring
  rw [hT, Finset.sum_sub_distrib, h1, h2]
  ring

end Commons.Combinatorics.Transference
