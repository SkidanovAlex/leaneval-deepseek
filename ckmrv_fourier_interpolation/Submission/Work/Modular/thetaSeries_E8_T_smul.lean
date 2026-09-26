import Mathlib
import Submission.Work.Modular.Basic
import Submission.Work.Modular.Lattice

namespace Work.Modular

open UpperHalfPlane
open scoped Real MatrixGroups

/-!
# The theta series of `E₈` is invariant under `τ ↦ τ + 1`

The point of this file is the elementary observation that makes the theta series of an
even lattice a power series in `q = e^{2πiτ}`: since every vector of `E₈` has even
squared length `‖x‖² = 2k`, the summand `exp (π i τ ‖x‖²)` picks up the factor
`exp (π i ‖x‖²) = exp (k · 2πi) = 1` when `τ` is replaced by `τ + 1`.

The whole content is therefore the arithmetic fact that `E₈` is *even*, which we prove
here in the form needed (`thetaSeries_E8_norm_sq_even`).  The lattice is presented in
`Lattice.lean` as the `ℤ`-span of the vectors with pairwise congruent coordinates and
even coordinate sum; writing `yᵢ = 2 xᵢ ∈ ℤ` for the doubled coordinates, the two
defining conditions say that (i) all `yᵢ` have the same parity and (ii) `∑ᵢ yᵢ = 4m`.
If every `yᵢ` is odd then `yᵢ² ≡ 1 (mod 8)`, so `∑ yᵢ² ≡ 8 ≡ 0 (mod 8)`; if every `yᵢ`
is even, `yᵢ = 2zᵢ` and the condition `∑ yᵢ = 4m` forces `∑ zᵢ` to be even, so that
`∑ yᵢ² = 4 ∑ zᵢ²` is again divisible by `8`.  As `4 ‖x‖² = ∑ yᵢ²`, this gives the
evenness of `‖x‖²`.
-/

/-- If all the integers `y i` (`i : Fin 8`) are odd, then the sum of their squares is
divisible by `8`.  Indeed each square is `≡ 1 (mod 8)`. -/
theorem eight_dvd_sum_sq_of_odd (y : Fin 8 → ℤ) (h : ∀ i, Odd (y i)) :
    (8 : ℤ) ∣ ∑ i, y i ^ 2 := by
  rw [show (8 : ℤ) = ((8 : ℕ) : ℤ) by norm_num, ← ZMod.intCast_zmod_eq_zero_iff_dvd]
  push_cast
  have hterm : ∀ i ∈ (Finset.univ : Finset (Fin 8)), ((y i : ZMod 8)) ^ 2 = 1 := by
    intro i _
    obtain ⟨t, ht⟩ := h i
    rw [ht]
    push_cast
    have h2 : ∀ u : ZMod 8, (2 * u + 1) ^ 2 = 1 := by decide
    simpa using h2 (t : ZMod 8)
  rw [Finset.sum_congr rfl hterm]
  decide

/-- If the sum of the integers `z i` (`i : Fin 8`) is even, then so is the sum of their
squares; indeed `z² ≡ z (mod 2)` for every integer `z`. -/
theorem two_dvd_sum_sq_of_two_dvd_sum (z : Fin 8 → ℤ) (h : (2 : ℤ) ∣ ∑ i, z i) :
    (2 : ℤ) ∣ ∑ i, z i ^ 2 := by
  rw [show (2 : ℤ) = ((2 : ℕ) : ℤ) by norm_num, ← ZMod.intCast_zmod_eq_zero_iff_dvd]
  push_cast
  have hz : ((∑ i, z i : ℤ) : ZMod 2) = 0 := by
    rw [show (2 : ℤ) = ((2 : ℕ) : ℤ) by norm_num, ← ZMod.intCast_zmod_eq_zero_iff_dvd] at h
    exact h
  calc ∑ i, (z i : ZMod 2) ^ 2 = ∑ i, (z i : ZMod 2) := by
        apply Finset.sum_congr rfl; intro i _; exact (by decide : ∀ u : ZMod 2, u ^ 2 = u) _
    _ = ((∑ i, z i : ℤ) : ZMod 2) := by push_cast; rfl
    _ = 0 := hz

/-- Every vector of the `E₈` lattice has even squared length: `‖x‖ ^ 2 = 2 * k` for some
natural number `k`.  This is the arithmetic input of the `T`-invariance of `Θ_{E₈}`. -/
lemma thetaSeries_E8_norm_sq_even (x : EuclideanSpace ℝ (Fin 8)) (hx : x ∈ E8) :
    ∃ k : ℕ, ‖x‖ ^ 2 = 2 * (k : ℝ) := by
  rw [mem_E8] at hx
  obtain ⟨h1, h2, h3⟩ := hx
  -- doubled coordinates: `y i = 2 * x i`
  choose y hy using fun i => (h1 i).imp fun m hm => hm.symm
  -- pairwise differences of the doubled coordinates are even
  have hyij : ∀ i j, ∃ m : ℤ, y i - y j = 2 * m := by
    intro i j
    obtain ⟨m, hm⟩ := h2 i j
    refine ⟨m, ?_⟩
    have hc : ((y i - y j : ℤ) : ℝ) = ((2 * m : ℤ) : ℝ) := by
      push_cast
      rw [hy i, hy j]
      linear_combination 2 * hm
    exact_mod_cast hc
  have hnorm : ‖x‖ ^ 2 = ∑ i, (x.ofLp i) ^ 2 := by
    rw [PiLp.norm_sq_eq_of_L2]
    apply Finset.sum_congr rfl
    intro i _
    rw [Real.norm_eq_abs, sq_abs]
  have hx_eq : ∀ i, x.ofLp i = (y i : ℝ) / 2 := by
    intro i
    have := hy i
    linarith
  set S : ℤ := ∑ i, y i ^ 2 with hSdef
  -- `4 ‖x‖² = ∑ yᵢ²`
  have hS4 : 4 * ‖x‖ ^ 2 = (S : ℝ) := by
    rw [hnorm, hSdef]
    push_cast
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [hx_eq i]
    ring
  -- `8 ∣ ∑ yᵢ²`
  have h8 : (8 : ℤ) ∣ S := by
    rcases Int.even_or_odd (y 0) with h0e | h0o
    · -- all `yᵢ` are even
      have hye : ∀ i, Even (y i) := by
        intro i
        obtain ⟨m, hm⟩ := hyij i 0
        rw [show y i = (y i - y 0) + y 0 by ring]
        refine Even.add ?_ h0e
        rw [hm]; exact even_two_mul m
      set z : Fin 8 → ℤ := fun i => y i / 2 with hzdef
      have hyz : ∀ i, y i = 2 * z i := by
        intro i
        have h2dvd : (2 : ℤ) ∣ y i := even_iff_two_dvd.mp (hye i)
        rw [hzdef]
        show y i = 2 * (y i / 2)
        rw [mul_comm]
        exact (Int.ediv_mul_cancel h2dvd).symm
      obtain ⟨m, hm⟩ := h3
      -- `2 ∣ ∑ zᵢ`
      have h2z : (2 : ℤ) ∣ ∑ i, z i := by
        refine ⟨m, ?_⟩
        have h : ((∑ i, z i : ℤ) : ℝ) = ((2 * m : ℤ) : ℝ) := by
          push_cast
          have : ∑ i, (z i : ℝ) = ∑ i, x.ofLp i := by
            apply Finset.sum_congr rfl
            intro i _
            rw [hx_eq i, hyz i]
            push_cast
            ring
          rw [this, hm]
        exact_mod_cast h
      obtain ⟨t, ht⟩ := two_dvd_sum_sq_of_two_dvd_sum z h2z
      refine ⟨t, ?_⟩
      rw [hSdef]
      have hsum4 : ∑ i, y i ^ 2 = 4 * ∑ i, z i ^ 2 := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _
        rw [hyz i]
        ring
      rw [hsum4, ht]
      ring
    · -- all `yᵢ` are odd
      have hyo : ∀ i, Odd (y i) := by
        intro i
        obtain ⟨m, hm⟩ := hyij i 0
        rw [show y i = (y i - y 0) + y 0 by ring, hm]
        exact Even.add_odd (even_two_mul m) h0o
      rw [hSdef]
      exact eight_dvd_sum_sq_of_odd y hyo
  obtain ⟨k, hk⟩ := h8
  have hR : 4 * ‖x‖ ^ 2 = 8 * (k : ℝ) := by
    have h := hS4
    rw [hk] at h
    push_cast at h
    linarith
  have hkn : 0 ≤ k := by
    have h : (0 : ℝ) ≤ (k : ℝ) := by
      have h2 : (0 : ℝ) ≤ 8 * (k : ℝ) := by rw [← hR]; positivity
      linarith
    exact_mod_cast h
  refine ⟨k.toNat, ?_⟩
  have hkcast : (k : ℝ) = (k.toNat : ℝ) := by
    rw [← Int.toNat_of_nonneg hkn]
    push_cast
    rfl
  rw [show ‖x‖ ^ 2 = 2 * (k : ℝ) by linarith, hkcast]

/-- `Θ_{E₈}` is invariant under `τ ↦ τ + 1`, because `E₈` is an even lattice. -/
theorem thetaSeries_E8_T_smul (τ : ℍ) :
    thetaSeries E8 (ModularGroup.T • τ) = thetaSeries E8 τ := by
  rw [thetaSeries]
  refine tsum_congr (fun x => ?_)
  simp only [thetaTerm]
  have hT : ((ModularGroup.T • τ : ℍ) : ℂ) = (τ : ℂ) + 1 := by
    rw [modular_T_smul, UpperHalfPlane.coe_vadd]
    push_cast
    ring
  obtain ⟨k, hk⟩ := thetaSeries_E8_norm_sq_even (x : EuclideanSpace ℝ (Fin 8)) x.2
  have hper : Complex.exp (π * Complex.I * ((‖(x : EuclideanSpace ℝ (Fin 8))‖ ^ 2 : ℝ) : ℂ)) = 1 := by
    rw [hk]
    push_cast
    rw [show π * Complex.I * (2 * (k : ℂ)) = (k : ℂ) * (2 * π * Complex.I) by ring]
    exact Complex.exp_nat_mul_two_pi_mul_I k
  rw [hT, show π * Complex.I * ((τ : ℂ) + 1) * ((‖(x : EuclideanSpace ℝ (Fin 8))‖ ^ 2 : ℝ) : ℂ)
        = π * Complex.I * (τ : ℂ) * ((‖(x : EuclideanSpace ℝ (Fin 8))‖ ^ 2 : ℝ) : ℂ)
          + π * Complex.I * ((‖(x : EuclideanSpace ℝ (Fin 8))‖ ^ 2 : ℝ) : ℂ) by ring]
  rw [Complex.exp_add, hper, mul_one]

end Work.Modular
