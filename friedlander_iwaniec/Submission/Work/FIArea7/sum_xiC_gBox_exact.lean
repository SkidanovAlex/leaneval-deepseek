import Mathlib
import Submission.Work.FIArea7.sum_gBox_periodic_decomp
import Submission.Work.FIArea7.FIsymbols
import Submission.Work.FIArea7.card_charMod4d_eq_card_units
import Submission.Work.FIArea7.GaussUnits
import Submission.Work.FIArea7.sum_xiGaussMod_units

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.FIArea7

/-- Each factor `ξ_w(p) = (w.re·p₁ − w.im·p₂ | |w|²)` of the inner sum is a Jacobi symbol, hence
(or `0`, which is also fine) of modulus at most `1`. -/
lemma norm_xiC_le_one (q : ℕ) (w : GaussianInt) (p : ZMod q × ZMod q) :
    ‖xiC q w p‖ ≤ 1 := by
  rcases jacobiSym.trichotomy (w.re * ((p.1).val : ℤ) - w.im * ((p.2).val : ℤ))
    (Work.FIPlan.gnorm w) with h | h | h <;>
    simp [xiC, h]

/-- **The inner sum of *FI* Lemma 21.2: the box sum of `ξ_{w₁}ξ_{w₂}` in terms of the exact class
sum.**  For `w₁, w₂` with `|wᵢ|² = Nᵢ` and `q = N₁N₂`, the sum over the box `gBox R` of the product
of the two Dirichlet symbols is the complete character sum scaled by the average class size
`A = ⌊(2R+1)/q⌋`, up to `E` with `‖E‖ ≤ 2((2R+1)q + q²)`:

  `Σ_{z ∈ gBox R} ξ_{w₁}(z)ξ_{w₂}(z) = A²·Σ_{p ∈ (Z/q)²} ξ_{w₁}(p)ξ_{w₂}(p) + E`.

This is the display *"Splitting the inner summation into residue classes … by elementary counting"*
in the proof of *FI* Lemma 21.2; the complete character sum is evaluated exactly by
`Work.FIArea7.sum_xiC_general` (the corrected Lemma 21.1).  Immediate from
`Work.FIArea7.sum_gBox_periodic_decomp` with `F u v = xiC q w₁ (u,v)·xiC q w₂ (u,v)`: each factor is
a Jacobi symbol, hence of modulus `≤ 1`. -/
theorem sum_xiC_gBox_exact (N1 N2 : ℕ) [NeZero N1] [NeZero N2] (w1 w2 : GaussianInt) (R : ℤ)
    (hN1 : Work.FIPlan.gnorm w1 = N1) (hN2 : Work.FIPlan.gnorm w2 = N2) :
    ∃ E : ℂ, ‖E‖ ≤ 2 * ((((2 * R + 1).toNat : ℝ) * ((N1 * N2 : ℕ) : ℝ))
        + (((N1 * N2 : ℕ) : ℝ)) ^ 2) ∧
      (∑ z ∈ Work.FIPlan.gBox R,
          xiC (N1 * N2) w1 ((z.re : ZMod (N1 * N2)), (z.im : ZMod (N1 * N2)))
            * xiC (N1 * N2) w2 ((z.re : ZMod (N1 * N2)), (z.im : ZMod (N1 * N2))))
        = ((((2 * R + 1).toNat / (N1 * N2) : ℕ) : ℂ)) ^ 2
            * (∑ p : ZMod (N1 * N2) × ZMod (N1 * N2),
                xiC (N1 * N2) w1 p * xiC (N1 * N2) w2 p) + E := by
  classical
  haveI : NeZero (N1 * N2) := ⟨mul_ne_zero (NeZero.ne N1) (NeZero.ne N2)⟩
  -- Apply the elementary counting lemma to the periodic function `F = ξ_{w₁}ξ_{w₂}`.
  obtain ⟨E, hE, hsum⟩ := sum_gBox_periodic_decomp R (N1 * N2)
    (fun u v => xiC (N1 * N2) w1 (u, v) * xiC (N1 * N2) w2 (u, v))
    (fun u v => by
      rw [norm_mul]
      have h1 := norm_xiC_le_one (N1 * N2) w1 (u, v)
      have h2 := norm_xiC_le_one (N1 * N2) w2 (u, v)
      have n1 := norm_nonneg (xiC (N1 * N2) w1 (u, v))
      have n2 := norm_nonneg (xiC (N1 * N2) w2 (u, v))
      nlinarith)
  refine ⟨E, hE, ?_⟩
  rw [hsum]
  -- Identify the iterated sum with the sum over the product `(ZMod q)²`.
  have hinner : (∑ u : ZMod (N1 * N2), ∑ v : ZMod (N1 * N2),
        xiC (N1 * N2) w1 (u, v) * xiC (N1 * N2) w2 (u, v))
      = ∑ p : ZMod (N1 * N2) × ZMod (N1 * N2),
          xiC (N1 * N2) w1 p * xiC (N1 * N2) w2 p :=
    (Fintype.sum_prod_type (fun p : ZMod (N1 * N2) × ZMod (N1 * N2) =>
      xiC (N1 * N2) w1 p * xiC (N1 * N2) w2 p)).symm
  rw [hinner]

end Work.FIArea7
