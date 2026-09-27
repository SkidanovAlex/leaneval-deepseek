import Mathlib

set_option linter.style.haveILetI false

namespace Work.Mostow.gapA

/-- **The standard primitive `Nat.card G`-th root of unity lies in `G`.**

If `G` is a finite subgroup of `ℂˣ`, then every element of `G` is a `Nat.card G`-th root of unity
(Lagrange), so `G` is contained in `rootsOfUnity (Nat.card G) ℂ`; since that group has at most
`Nat.card G` elements, the containment is an equality.  Hence the primitive `n`-th root of unity
`exp (-(2π/n) I)` (with `n = Nat.card G`) belongs to `G`. -/
theorem stdRoot_in_finite_subgroup (G : Subgroup ℂˣ) (hfin : Finite G) :
    ∃ z : ℂˣ, z ∈ G ∧ (z : ℂ) = Complex.exp (-(2 * Real.pi / (Nat.card G : ℝ)) * Complex.I) := by
  classical
  haveI : Finite G := hfin
  haveI : Nonempty G := ⟨⟨1, G.one_mem⟩⟩
  -- `G` is non-trivial, so its cardinal is positive, whence `NeZero`.
  have hN0 : Nat.card G ≠ 0 := Nat.card_pos.ne'
  haveI : NeZero (Nat.card G) := ⟨hN0⟩
  -- Step 1: `G` is contained in the group of `Nat.card G`-th roots of unity.
  have hle : G ≤ rootsOfUnity (Nat.card G) ℂ := by
    intro z hz
    rw [mem_rootsOfUnity]
    -- Lagrange: an element of a finite group of order `Nat.card G` has `Nat.card G`-th power `1`.
    have h1 : (⟨z, hz⟩ : G) ^ Nat.card G = 1 := pow_card_eq_one'
    have h2 := congrArg (fun w : G => (w : ℂˣ)) h1
    simp only [Subgroup.coe_pow, Subgroup.coe_one] at h2
    exact h2
  -- Step 2: the two subgroups have the same (finite) cardinality, hence are equal.
  have hEq : G = rootsOfUnity (Nat.card G) ℂ :=
    Subgroup.eq_of_le_of_card_ge hle (card_rootsOfUnity ℂ (Nat.card G))
  -- Step 3: `exp (-(2π/n) I)` is an `n`-th root of unity.
  have hmem : (Units.mk0 (Complex.exp (-(2 * Real.pi / (Nat.card G : ℝ)) * Complex.I))
      (Complex.exp_ne_zero _)) ∈ rootsOfUnity (Nat.card G) ℂ := by
    rw [mem_rootsOfUnity', Units.val_mk0]
    rw [← Complex.exp_nat_mul, Complex.exp_eq_one_iff]
    -- `n * (-(2π/n) I) = (-1) * (2π I)`, so the exponential is `1` by periodicity.
    refine ⟨-1, ?_⟩
    push_cast
    have hNc : ((Nat.card G : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hN0
    field_simp
  rw [← hEq] at hmem
  exact ⟨_, hmem, rfl⟩

end Work.Mostow.gapA
