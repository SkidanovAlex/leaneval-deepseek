import Mathlib
import Submission.Work.BMF.adi_descent
import Submission.Work.BMF.lattice_top_coeff

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BMF

open Polynomial Finset

set_option maxHeartbeats 800000

/-- One step of the descent preserves the structural form of the extracted lattice
coefficients `μ m` for all degrees `m` still present at the new level `s.j - 1`, i.e. for
`m ∈ [s.j, p.k]`.

At the top degree `m = s.j` the fresh coefficient `muval p s = G.coeff s.j / q_j` is
integral: the lattice condition `(D_k/D_{s.j}) · G ∈ Poly((1/Q_m)ℤ → ℤ)` combined with
`deg G ≤ s.j` forces (via the `s.j`-th finite difference, `lattice_top_coeff`) that
`D_{s.j} · (s.j)! · G.coeff s.j / Q_m^{s.j} ∈ ℤ`; clearing denominators gives the claim.
For `m > s.j` nothing changes and the property is inherited from the invariant `DInv p s`. -/
theorem step_mu_struct (p : ADIPar) (s : DSt) (hp : ADIHyp p) (hs : DInv p s) (hj : 1 ≤ s.j) :
    ∀ m ∈ Finset.Icc s.j p.k, ∃ z : ℤ,
      (dstep p s).mu m = z * (p.Qm : ℝ) ^ m /
        (((Dfac p.k m : ℕ) : ℝ) * ((m.factorial : ℕ) : ℝ) *
          (((qj p.a p.b m : ℕ) : ℝ))) := by
  intro m hm
  rw [Finset.mem_Icc] at hm
  obtain ⟨hmlo, hmhi⟩ := hm
  rcases eq_or_lt_of_le hmlo with heq | hlt
  · -- top degree `m = s.j`: the new coefficient is lattice valued
    subst heq
    have hint : ∀ n : ℤ, ∃ m : ℤ, (Dfac p.k s.j : ℝ) * s.G.eval ((1 / (p.Qm : ℝ)) * n) = m := by
      intro n
      obtain ⟨m, hm⟩ := hs.2.2.2.2.2.2.2.2.1 n
      exact ⟨m, by simpa only [Polynomial.eval_mul, Polynomial.eval_C] using hm⟩
    obtain ⟨z, hz⟩ := lattice_top_coeff (j := s.j) (D := Dfac p.k s.j) (Qm := p.Qm) (G := s.G)
      (Nat.one_le_iff_ne_zero.mpr (ne_of_gt (Dfac_pos p.k s.j))) hp.2.2.2.2.1
      hs.2.2.2.1 hint
    refine ⟨z, ?_⟩
    rw [dstep_mu, Function.update_self]
    simp only [muval]
    have hQ0 : (p.Qm : ℝ) ≠ 0 := by
      have : (0 : ℝ) < (p.Qm : ℝ) := by
        exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hp.2.2.2.2.1)
      exact ne_of_gt this
    have hDF : ((Dfac p.k s.j : ℕ) : ℝ) * ((s.j.factorial : ℕ) : ℝ) ≠ 0 := by
      have h1 : ((Dfac p.k s.j : ℕ) : ℝ) ≠ 0 :=
        Nat.cast_ne_zero.mpr (ne_of_gt (Dfac_pos p.k s.j))
      have h2 : ((s.j.factorial : ℕ) : ℝ) ≠ 0 :=
        Nat.cast_ne_zero.mpr (ne_of_gt (Nat.factorial_pos s.j))
      exact mul_ne_zero h1 h2
    have hz' : (z : ℝ) * (p.Qm : ℝ) ^ s.j =
        ((Dfac p.k s.j : ℕ) : ℝ) * ((s.j.factorial : ℕ) : ℝ) * s.G.coeff s.j := by
      rw [← hz, div_mul_cancel₀ _ (pow_ne_zero _ hQ0)]
    rw [hz']
    exact (mul_div_mul_left (s.G.coeff s.j) (((qj p.a p.b s.j : ℕ) : ℝ)) hDF).symm
  · -- lower degrees: inherited from the invariant
    have hmne : m ≠ s.j := ne_of_gt hlt
    have hmu : (dstep p s).mu m = s.mu m := by
      rw [dstep_mu]
      exact Function.update_of_ne hmne (muval p s) s.mu
    rw [hmu]
    exact hs.2.2.2.2.2.2.2.2.2.2.2 m (by rw [Finset.mem_Icc]; exact ⟨by omega, hmhi⟩)

end Work.BMF
