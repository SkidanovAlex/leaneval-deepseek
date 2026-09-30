import Mathlib
import Submission.Work.BMF.adi_descent

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BMF

open Polynomial Finset

set_option linter.unusedVariables false

/-- One step of the descent keeps the decomposition of `P₀` into the current polynomial plus the
peeled-off Taylor/lattice terms: at level `s.j` the term `(T_{s.j}/2π) Tay_{s.j} + μ_{s.j} t^{s.j}`
is absorbed into `(dstep p s).P`, and the remaining sum runs over `m ∈ [s.j+1, k]`. -/
theorem step_decomp (p : ADIPar) (s : DSt) (hp : ADIHyp p) (hs : DInv p s) (hj : 1 ≤ s.j) :
    p.P₀ = (dstep p s).P + ∑ m ∈ Finset.Icc ((dstep p s).j + 1) p.k,
      (C ((dstep p s).T m / (2 * Real.pi)) * Tay m p.x + C ((dstep p s).mu m) * X ^ m) := by
  obtain ⟨hjk, -, -, -, -, -, -, -, -, heq, -⟩ := hs
  have hsucc : (dstep p s).j + 1 = s.j := by rw [dstep_j]; omega
  rw [hsucc, heq, dstep_P, dstep_T, dstep_mu]
  have hnot : s.j ∉ Finset.Icc (s.j + 1) p.k := by
    simp only [Finset.mem_Icc, not_and]
    intro h; omega
  have hsplit :
      (∑ m ∈ Finset.Icc s.j p.k,
        (C ((Function.update s.T s.j (Tval p s)) m / (2 * Real.pi)) * Tay m p.x +
          C ((Function.update s.mu s.j (muval p s)) m) * X ^ m))
      = (∑ m ∈ Finset.Icc (s.j + 1) p.k,
          (C (s.T m / (2 * Real.pi)) * Tay m p.x + C (s.mu m) * X ^ m))
        + (C (Tval p s / (2 * Real.pi)) * Tay s.j p.x + C (muval p s) * X ^ s.j) := by
    rw [show (Finset.Icc s.j p.k) = insert s.j (Finset.Icc (s.j + 1) p.k) from
      (Finset.insert_Icc_succ_left_eq_Icc hjk).symm]
    rw [Finset.sum_insert hnot]
    have hfj : (C (Function.update s.T s.j (Tval p s) s.j / (2 * Real.pi)) * Tay s.j p.x +
        C (Function.update s.mu s.j (muval p s) s.j) * X ^ s.j)
        = (C (Tval p s / (2 * Real.pi)) * Tay s.j p.x + C (muval p s) * X ^ s.j) := by
      rw [Function.update_self, Function.update_self]
    have hsum2 :
        (∑ m ∈ Finset.Icc (s.j + 1) p.k,
          (C ((Function.update s.T s.j (Tval p s)) m / (2 * Real.pi)) * Tay m p.x +
            C ((Function.update s.mu s.j (muval p s)) m) * X ^ m))
        = (∑ m ∈ Finset.Icc (s.j + 1) p.k,
            (C (s.T m / (2 * Real.pi)) * Tay m p.x + C (s.mu m) * X ^ m)) := by
      refine Finset.sum_congr rfl fun m hm => ?_
      have hmne : m ≠ s.j := by
        simp only [Finset.mem_Icc] at hm; omega
      rw [Function.update_of_ne hmne, Function.update_of_ne hmne]
    rw [hfj, hsum2, add_comm]
  rw [hsplit]
  ring

end Work.BMF
