import Mathlib
import Submission.Work.BMF.Xsum_pow_defs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The `2s`-th power of the inner `b`-sum `Xsum`

Ford's Lemma 5.1 (*Vinogradov's integral and bounds for the Riemann zeta function*, Proc. LMS 85
(2002)) bounds the `2s`-th moment of the inner sum

  `Xsum k M₂ γ ε c = Σ_{b ∈ [1,M₂]} ε_b e(Σ_{j<k} γ_j b^{j+1} c_j)`

over a box of frequencies `c`.  The first step is to expand that power as a sum over pairs of
`s`-tuples:

  `‖Xsum k M₂ γ ε c‖^{2s}
     = Σ_{p : Pair s M₂} (Π_i ε_{(p.1 i)} star ε_{(p.2 i)})
          · e(Σ_j γ_j c_j (Σ_i (p.1 i)^{j+1} - Σ_i (p.2 i)^{j+1}))`,

i.e. precisely

  `((‖Xsum k M₂ γ ε c‖ ^ (2 * s) : ℝ) : ℂ)
     = ∑ p : Pair s M₂, epsp ε p * eZ (∑ j, γ_j c_j dvec (j+1) p)`

(`Work.BMF.Xsum_norm_pow`), which is the identity used to pass to the incomplete-system count
`Jincom` in the proof of `Work.BMF.vkford_lemma51`.

The proof is the following chain:
`‖Xsum‖^{2s} = (Xsum)^s (star Xsum)^s` (norm and conjugate),
then `Fintype.sum_pow` expands each `s`-th power over `s`-tuples and `Fintype.sum_mul_sum` pairs
them up.  Per pair the product of characters is combined with `prod_eZ`/`eZ_add`/`star_eZ`
(`Xterm_mul_star`), and the resulting phase is identified with the pair-difference `dvec`
(`Xphase_add_dvec`).
-/

namespace Work.BMF

open Finset
open scoped BigOperators

/-- `‖z‖^{2s} = z^s (star z)^s` : the starting point of the expansion. -/
lemma norm_pow_eq_mul_star (z : ℂ) (s : ℕ) :
    ((‖z‖ ^ (2 * s) : ℝ) : ℂ) = z ^ s * star z ^ s := by
  have h1 : ((‖z‖ ^ (2 * s) : ℝ) : ℂ) = (((‖z‖ ^ 2 : ℝ)) : ℂ) ^ s := by
    rw [pow_mul]
    push_cast
    ring
  rw [h1]
  have h2 : ((‖z‖ ^ 2 : ℝ) : ℂ) = z * star z := by
    rw [← Complex.normSq_eq_norm_sq]
    exact (Complex.mul_conj z).symm
  rw [h2, mul_pow]

/-- The conjugate of a summand of `Xsum`. -/
lemma star_Xterm (k : ℕ) (γ : Fin k → ℝ) (ε : ℕ → ℂ) (c : Fin k → ℤ) (b : ℕ) :
    star (Xterm k γ ε c b) = star (ε b) * eZ (-(Xphase k γ c b)) := by
  rw [Xterm, star_mul, star_eZ, mul_comm]

/-- **Pointwise pairing of the terms.**  The product of a summand of `Xsum^s` with a conjugate
summand of `(star Xsum)^s` is the pair weight `epsp` times the character of the pair phase. -/
lemma Xterm_mul_star (k s M₂ : ℕ) (γ : Fin k → ℝ) (ε : ℕ → ℂ) (c : Fin k → ℤ)
    (u v : Fin s → Finset.Icc 1 M₂) :
    (∏ i : Fin s, Xterm k γ ε c (u i).1) * (∏ i : Fin s, star (Xterm k γ ε c (v i).1))
      = epsp ε (u, v)
        * eZ ((∑ i : Fin s, Xphase k γ c (u i).1)
              + ∑ i : Fin s, -(Xphase k γ c (v i).1)) := by
  have h1 : (∏ i : Fin s, Xterm k γ ε c (u i).1)
      = (∏ i : Fin s, ε (u i).1) * (∏ i : Fin s, eZ (Xphase k γ c (u i).1)) := by
    rw [← Finset.prod_mul_distrib]
    rfl
  have h2 : (∏ i : Fin s, star (Xterm k γ ε c (v i).1))
      = (∏ i : Fin s, star (ε (v i).1))
        * (∏ i : Fin s, eZ (-(Xphase k γ c (v i).1))) := by
    rw [← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun i _ => star_Xterm k γ ε c (v i).1
  have h3 : (∏ i : Fin s, eZ (Xphase k γ c (u i).1))
      = eZ (∑ i : Fin s, Xphase k γ c (u i).1) := prod_eZ _
  have h4 : (∏ i : Fin s, eZ (-(Xphase k γ c (v i).1)))
      = eZ (∑ i : Fin s, -(Xphase k γ c (v i).1)) := prod_eZ _
  have h5 : epsp ε (u, v) = (∏ i : Fin s, ε (u i).1) * (∏ i : Fin s, star (ε (v i).1)) := by
    rw [epsp, Finset.prod_mul_distrib]
  rw [h1, h2, h3, h4, h5, eZ_add]
  ring

/-- **The pair phase is the pair difference.**  The phase `Σ_i Xphase (p.1 i) - Σ_i Xphase (p.2 i)`
attached to a pair by the expansion is `Σ_j γ_j c_j dvec (j+1) p`, the sum over the power
differences `dvec` appearing in the right-hand side of `Work.BMF.Xsum_norm_pow`. -/
lemma Xphase_add_dvec (k s M₂ : ℕ) (γ : Fin k → ℝ) (c : Fin k → ℤ) (p : Pair s M₂) :
    (∑ i : Fin s, Xphase k γ c (p.1 i).1) + (∑ i : Fin s, -(Xphase k γ c (p.2 i).1))
      = ∑ j : Fin k, γ j * (c j : ℝ) * ((dvec ((j : ℕ) + 1) p : ℤ) : ℝ) := by
  -- the phase of a single `s`-tuple, with the sums exchanged and the `j`-th factor taken out
  have key : ∀ w : Fin s → Finset.Icc 1 M₂,
      (∑ i : Fin s, Xphase k γ c (w i).1)
        = ∑ j : Fin k, γ j * (c j : ℝ)
            * (∑ i : Fin s, (((w i).1 : ℕ) : ℝ) ^ ((j : ℕ) + 1)) := by
    intro w
    simp_rw [Xphase_eq]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun j _ => (Finset.mul_sum ..).symm
  have h2 : (∑ i : Fin s, -(Xphase k γ c (p.2 i).1))
      = ∑ j : Fin k, γ j * (c j : ℝ)
          * (-(∑ i : Fin s, (((p.2 i).1 : ℕ) : ℝ) ^ ((j : ℕ) + 1))) := by
    rw [Finset.sum_neg_distrib, key p.2, ← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun j _ => by ring
  rw [key p.1, h2, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [dvec_cast]
  ring

theorem Xsum_norm_pow (k s M₂ : ℕ) (γ : Fin k → ℝ) (ε : ℕ → ℂ) (c : Fin k → ℤ) :
    ((‖Xsum k M₂ γ ε c‖ ^ (2 * s) : ℝ) : ℂ)
      = ∑ p : Pair s M₂, epsp ε p
          * eZ (∑ j : Fin k, γ j * (c j : ℝ) * ((dvec ((j : ℕ) + 1) p : ℤ) : ℝ)) := by
  rw [norm_pow_eq_mul_star, Xterm_pow, star_Xsum_pow, Fintype.sum_mul_sum]
  rw [← Fintype.sum_prod_type (f := fun p : (Fin s → Icc 1 M₂) × (Fin s → Icc 1 M₂) =>
        (∏ i : Fin s, Xterm k γ ε c (p.1 i).1)
          * ∏ i : Fin s, star (Xterm k γ ε c (p.2 i).1))]
  refine Finset.sum_congr rfl (fun p _ => ?_)
  rw [Xterm_mul_star, Xphase_add_dvec]

end Work.BMF
