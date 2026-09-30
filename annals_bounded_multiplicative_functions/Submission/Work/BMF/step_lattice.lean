import Mathlib
import Submission.Work.BMF.adi_descent
import Submission.Work.BMF.lattice_top_coeff

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BMF

open Polynomial Finset

/-- **One step of the ADI descent preserves lattice-integrality.**

The descent replaces `G` by `G - G.coeff j · X^j - nval` at level `j - 1`, where
`nval ∈ ℤ`.  Since `Dfac k (j-1) = j! · Dfac k j`, the part `Dfac k (j-1) · G` is an integer
multiple of the known integral object `Dfac k j · G`, while the removed top monomial becomes
integral because `Dfac k j · j! · G.coeff j / Qm^j ∈ ℤ` (the `j`-th forward difference of `G`
on `(1/Qm)ℤ`), and the constant is plainly integral. -/
theorem step_lattice (p : ADIPar) (s : DSt) (hp : ADIHyp p) (hs : DInv p s) (hj : 1 ≤ s.j) :
    IntegralOn (1 / (p.Qm : ℝ)) (C (((Dfac p.k (s.j - 1) : ℕ) : ℝ)) * (dstep p s).G) := by
  obtain ⟨hjk, _, _, hGdeg, _, _, _, _, hInt, _, _, _⟩ := hs
  obtain ⟨_, _, _, _, hQm1, _, _, _, _, _, _, _⟩ := hp
  rw [dstep_G]
  -- `Dfac k (j-1) = j! · Dfac k j`
  have hfac : ((Dfac p.k (s.j - 1) : ℕ) : ℝ)
      = (s.j.factorial : ℝ) * ((Dfac p.k s.j : ℕ) : ℝ) := by
    rw [Dfac_step p.k s.j hj hjk]
    push_cast
    ring
  -- integrality of the top coefficient, from the `j`-th finite difference on `(1/Qm)ℤ`
  have hDpos : 1 ≤ Dfac p.k s.j :=
    Nat.one_le_iff_ne_zero.mpr (Nat.pos_iff_ne_zero.mp (Dfac_pos p.k s.j))
  have hint : ∀ n : ℤ, ∃ m : ℤ,
      ((Dfac p.k s.j : ℕ) : ℝ) * s.G.eval ((1 / (p.Qm : ℝ)) * n) = m := by
    intro n
    obtain ⟨m, hm⟩ := hInt n
    exact ⟨m, by simpa [Polynomial.eval_mul] using hm⟩
  obtain ⟨z, hz⟩ := lattice_top_coeff (j := s.j) hDpos hQm1 hGdeg hint
  -- the `G` part
  have hA : IntegralOn (1 / (p.Qm : ℝ)) (C (((Dfac p.k (s.j - 1) : ℕ) : ℝ)) * s.G) := by
    intro n
    obtain ⟨m, hm⟩ := hInt n
    refine ⟨m * (s.j.factorial : ℤ), ?_⟩
    simp only [Polynomial.eval_mul, Polynomial.eval_C] at hm ⊢
    rw [hfac, mul_assoc, hm]
    push_cast
    ring
  -- the removed top monomial `G.coeff j · X^j`
  have hB : IntegralOn (1 / (p.Qm : ℝ))
      (C (((Dfac p.k (s.j - 1) : ℕ) : ℝ)) * (C (s.G.coeff s.j) * X ^ s.j)) := by
    intro n
    refine ⟨z * n ^ s.j, ?_⟩
    simp only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
      at hz ⊢
    rw [hfac]
    push_cast
    rw [show (1 / (p.Qm : ℝ)) * (n : ℝ) = (n : ℝ) / (p.Qm : ℝ) by ring, div_pow]
    rw [show ((s.j.factorial : ℝ) * ((Dfac p.k s.j : ℕ) : ℝ)) *
          ((s.G.coeff s.j) * ((n : ℝ) ^ s.j / (p.Qm : ℝ) ^ s.j))
        = (((Dfac p.k s.j : ℕ) : ℝ) * (s.j.factorial : ℝ) * s.G.coeff s.j
            / (p.Qm : ℝ) ^ s.j) * (n : ℝ) ^ s.j by ring]
    rw [hz]
  -- the constant term
  have hC : IntegralOn (1 / (p.Qm : ℝ))
      (C (((Dfac p.k (s.j - 1) : ℕ) : ℝ)) * C (nval p s : ℝ)) := by
    convert IntegralOn.const ((((Dfac p.k (s.j - 1) : ℕ) : ℤ)) * nval p s) using 1
    rw [← Polynomial.C_mul]
    congr 1
    push_cast
    ring
  have hEq : C (((Dfac p.k (s.j - 1) : ℕ) : ℝ)) *
      (s.G - C (s.G.coeff s.j) * X ^ s.j - C (nval p s : ℝ))
      = C (((Dfac p.k (s.j - 1) : ℕ) : ℝ)) * s.G
        - C (((Dfac p.k (s.j - 1) : ℕ) : ℝ)) * (C (s.G.coeff s.j) * X ^ s.j)
        - C (((Dfac p.k (s.j - 1) : ℕ) : ℝ)) * C (nval p s : ℝ) := by ring
  rw [hEq]
  exact (hA.sub hB).sub hC

end Work.BMF
