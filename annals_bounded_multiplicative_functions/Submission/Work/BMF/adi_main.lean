import Mathlib
import Submission.Work.BMF.adi_descent
import Submission.Work.BMF.step_degrees
import Submission.Work.BMF.step_relation
import Submission.Work.BMF.step_bound
import Submission.Work.BMF.step_Alev
import Submission.Work.BMF.step_lattice
import Submission.Work.BMF.abs_Tval_le
import Submission.Work.BMF.step_T_bound
import Submission.Work.BMF.step_mu_struct
import Submission.Work.BMF.step_decomp

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The ADI descent, assembled

One step preserves the invariant, so `k` steps bring a state satisfying the approximate
dilation invariance of degree `≤ k` down to a constant plus the explicit log-approximation data.
-/

namespace Work.BMF

open Polynomial Finset

/-- The accumulated modulus `∏_{m=1}^{k} q_m` (without the `(k!)^{k+1}` factor). -/
noncomputable def qprod (k a b : ℕ) : ℕ := ∏ m ∈ Finset.Icc 1 k, qj a b m

theorem Dfac_self (k : ℕ) : Dfac k k = 1 := by
  unfold Dfac
  simp

theorem Alev_self (k : ℕ) (C₀ : ℝ) : Alev k C₀ k = (C₀ + (k : ℝ) + 2) * (1 + Dgrow k C₀) * 2 := by
  unfold Alev
  simp

/-- One step of the descent preserves the invariant. -/
theorem dstep_inv (p : ADIPar) (s : DSt) (hp : ADIHyp p) (hs : DInv p s) (hj : 1 ≤ s.j) :
    DInv p (dstep p s) := by
  have hdeg := step_degrees p s hp hs hj
  have hrel := step_relation p s hp hs hj
  have hbnd := step_bound p s hp hs hj
  have hAlev := step_Alev p s hp hs hj
  have hlatt := step_lattice p s hp hs hj
  have hT := step_T_bound p s hp hs hj
  have hmu := step_mu_struct p s hp hs hj
  have hdec := step_decomp p s hp hs hj
  have hjk : s.j ≤ p.k := hs.1
  have hA0 : 0 ≤ s.A := hs.2.2.2.2.2.2.1
  rw [DInv]
  refine ⟨?_, ?_, ?_, ?_, hrel, hbnd, ?_, ?_, ?_, hdec, ?_, ?_⟩
  · rw [dstep_j]; omega
  · rw [dstep_j]; exact hdeg.1
  · rw [dstep_j]; exact hdeg.2.1
  · rw [dstep_j]; exact hdeg.2.2
  · rw [dstep_A]
    have hD : 0 ≤ Dgrow p.k p.C₀ := Dgrow_nonneg p.k p.C₀ hp.1
    nlinarith [hA0]
  · rw [dstep_j]; exact hAlev
  · rw [dstep_j]; exact hlatt
  · intro m hm
    rw [dstep_j] at hm
    rw [Nat.sub_add_cancel hj] at hm
    exact hT m hm
  · intro m hm
    rw [dstep_j] at hm
    rw [Nat.sub_add_cancel hj] at hm
    exact hmu m hm

/-- `k` steps of the descent from level `k` reach level `0`. -/
theorem descend_exists (p : ADIPar) (hp : ADIHyp p) (s0 : DSt) (hs0 : DInv p s0)
    (hjk : s0.j = p.k) :
    ∃ s : DSt, s.j = 0 ∧ DInv p s := by
  have hiter : ∀ m ≤ p.k, ∃ s : DSt, s.j = p.k - m ∧ DInv p s := by
    intro m
    induction m with
    | zero =>
        intro _
        exact ⟨s0, by rw [hjk]; simp, hs0⟩
    | succ m ih =>
        intro hm
        obtain ⟨s, hsj, hsi⟩ := ih (by omega)
        have h1 : 1 ≤ s.j := by omega
        exact ⟨dstep p s, by rw [dstep_j, hsj]; omega, dstep_inv p s hp hsi h1⟩
  obtain ⟨s, hsj, hsi⟩ := hiter p.k le_rfl
  exact ⟨s, by omega, hsi⟩

/-- **One-sided output of the descent.**  From the approximate dilation invariance
`P₀(a·) - P₀(b·) = E₀ + G₀` with `|E₀| ≤ A` and `G₀` integer valued on `(1/Qm)ℤ`, the
polynomial is a constant plus `∑_m [(T_m/2π) Tay_m + μ_m X^m]` with the announced bounds on
`T_m` and lattice structure of `μ_m`. -/
theorem descent_result (p : ADIPar) (hp : ADIHyp p)
    (E0 G0 : ℝ[X]) (hE0 : E0.natDegree ≤ p.k) (hG0 : G0.natDegree ≤ p.k)
    (hrel0 : dil (p.a : ℝ) p.P₀ - dil (p.b : ℝ) p.P₀ = E0 + G0)
    (hbd0 : ∀ t ∈ Set.Icc (p.x / (p.a : ℝ)) ((p.x + p.L) / (p.a : ℝ)), |E0.eval t| ≤ p.C₀)
    (hlatt0 : IntegralOn (1 / (p.Qm : ℝ)) G0) :
    ∃ c0 : ℝ, ∃ T mu : ℕ → ℝ,
      (p.P₀ = C c0 + ∑ m ∈ Finset.Icc 1 p.k,
        (C (T m / (2 * Real.pi)) * Tay m p.x + C (mu m) * X ^ m)) ∧
      (∀ m ∈ Finset.Icc 1 p.k, |T m| ≤ CTc p.k p.C₀ * p.N ^ (m + 1)) ∧
      (∀ m ∈ Finset.Icc 1 p.k, ∃ z : ℤ,
        mu m = z * (p.Qm : ℝ) ^ m /
          (((Dfac p.k m : ℕ) : ℝ) * ((m.factorial : ℕ) : ℝ) *
            (((qj p.a p.b m : ℕ) : ℝ)))) := by
  have hp' := hp
  obtain ⟨hC₀, hP0deg, hL2, hN100, hQm1, hxpos, hxNL1, hxNL2, hb1, hba, ha1, ha2⟩ := hp'
  let s0 : DSt :=
    { j := p.k, P := p.P₀, E := E0, G := G0, A := p.C₀, T := fun _ => 0, mu := fun _ => 0 }
  have hs0 : DInv p s0 := by
    have hD : 0 ≤ Dgrow p.k p.C₀ := Dgrow_nonneg p.k p.C₀ hC₀
    have hAlevk : p.C₀ ≤ Alev p.k p.C₀ p.k := by
      rw [Alev_self]
      nlinarith [hC₀, hD]
    have hint : IntegralOn (1 / (p.Qm : ℝ)) (C (((Dfac p.k p.k : ℕ) : ℝ)) * G0) := by
      rw [Dfac_self]
      simpa using hlatt0
    refine ⟨le_rfl, hP0deg, hE0, hG0, hrel0, ?_, by linarith, hAlevk, hint, ?_, ?_, ?_⟩
    · intro t ht
      exact hbd0 t ht
    · have hempty : Finset.Icc (p.k + 1) p.k = ∅ := by
        ext m; simp only [Finset.mem_Icc, Finset.notMem_empty, iff_false]; omega
      simp only [s0, hempty, Finset.sum_empty, add_zero]
    · intro m hm
      have h1 : p.k + 1 ≤ m := (Finset.mem_Icc.mp hm).1
      have h2 : m ≤ p.k := (Finset.mem_Icc.mp hm).2
      exact absurd (le_trans h1 h2) (Nat.not_succ_le_self p.k)
    · intro m hm
      have h1 : p.k + 1 ≤ m := (Finset.mem_Icc.mp hm).1
      have h2 : m ≤ p.k := (Finset.mem_Icc.mp hm).2
      exact absurd (le_trans h1 h2) (Nat.not_succ_le_self p.k)
  obtain ⟨s, hsj, hsi⟩ := descend_exists p hp s0 hs0 rfl
  simp only [DInv] at hsi
  have hPc : s.P = C (s.P.coeff 0) := by
    refine Polynomial.eq_C_of_natDegree_eq_zero ?_
    have h := hsi.2.1
    rw [hsj] at h
    omega
  have hdec := hsi.2.2.2.2.2.2.2.2.2.1
  rw [hsj] at hdec
  refine ⟨s.P.coeff 0, s.T, s.mu, ?_, ?_, ?_⟩
  · have h1 : Finset.Icc (0 + 1) p.k = Finset.Icc 1 p.k := by norm_num
    rw [hPc, h1] at hdec
    exact hdec
  · intro m hm
    exact hsi.2.2.2.2.2.2.2.2.2.2.1 m (by simpa [hsj] using hm)
  · intro m hm
    exact hsi.2.2.2.2.2.2.2.2.2.2.2 m (by simpa [hsj] using hm)

end Work.BMF
