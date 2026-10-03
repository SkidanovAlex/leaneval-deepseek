import Mathlib
import Submission.Work.FIChain.TailDefs

namespace Work.FIChain

open Finset

attribute [local instance] Classical.propDecidable

/-- **The arithmetic reindexing of the Rankin tail (step 2).**

For a fixed `d`, the double sum over `(m, N)` with `d ∣ N` and `m·N ≤ x`, weighted by
`τ(m)² · ã(m·N)`, is the same as the double sum over `(K, N)` with `d ∣ K`, `d ∣ N`, `N ∣ K`,
weighted by `ã(K) · τ(K/N)²`: the substitution `(m, N) ↦ (K, N) = (m·N, N)` is a bijection of
the two index sets (its inverse is `(K, N) ↦ (K/N, N)`), and on matched pairs the weights agree
because `(m·N)/N = m`.

This is an *identity*, hence in particular the requested inequality. -/
lemma tail_arith_step2_inner (x d : ℕ) :
    (∑ m ∈ Finset.Icc 1 x, ((m.divisors.card : ℝ)) ^ 2 *
        ∑ N ∈ (Finset.Icc 1 x).filter (fun N => d ∣ N ∧ m * N ≤ x),
          Work.FIChain.atilc (m * N))
      = ∑ K ∈ (Finset.Icc 1 x).filter (fun K => d ∣ K),
          Work.FIChain.atilc K * ∑ N ∈ (Finset.Icc 1 x).filter (fun N => d ∣ N ∧ N ∣ K),
            ((K / N).divisors.card : ℝ) ^ 2 := by
  classical
  -- Rewrite both nested sums as sums over the `Sigma` (dependent pair) index sets.
  have hL : (∑ m ∈ Finset.Icc 1 x, ((m.divisors.card : ℝ)) ^ 2 *
        ∑ N ∈ (Finset.Icc 1 x).filter (fun N => d ∣ N ∧ m * N ≤ x), atilc (m * N))
      = ∑ p ∈ (Finset.Icc 1 x).sigma
            (fun m => (Finset.Icc 1 x).filter (fun N => d ∣ N ∧ m * N ≤ x)),
          ((p.1.divisors.card : ℝ)) ^ 2 * atilc (p.1 * p.2) := by
    simp only [Finset.mul_sum]
    rw [Finset.sum_sigma']
  have hR : (∑ K ∈ (Finset.Icc 1 x).filter (fun K => d ∣ K),
          atilc K * ∑ N ∈ (Finset.Icc 1 x).filter (fun N => d ∣ N ∧ N ∣ K),
            ((K / N).divisors.card : ℝ) ^ 2)
      = ∑ q ∈ ((Finset.Icc 1 x).filter (fun K => d ∣ K)).sigma
            (fun K => (Finset.Icc 1 x).filter (fun N => d ∣ N ∧ N ∣ K)),
          atilc q.1 * ((q.1 / q.2).divisors.card : ℝ) ^ 2 := by
    simp only [Finset.mul_sum]
    rw [Finset.sum_sigma']
  rw [hL, hR]
  -- The bijection `(m, N) ↦ (m·N, N)` between the two index sets.
  refine Finset.sum_bij (fun p _ => (⟨p.1 * p.2, p.2⟩ : Sigma (fun _ : ℕ => ℕ))) ?_ ?_ ?_ ?_
  · -- the map sends the source index set into the target index set
    intro p hp
    rw [Finset.mem_sigma] at hp
    obtain ⟨hm, hN⟩ := hp
    rw [Finset.mem_filter] at hN
    obtain ⟨hNS, hdvd, hmNx⟩ := hN
    have hm' : 1 ≤ p.1 ∧ p.1 ≤ x := by simpa [Finset.mem_Icc] using hm
    have hNS' : 1 ≤ p.2 ∧ p.2 ≤ x := by simpa [Finset.mem_Icc] using hNS
    rw [Finset.mem_sigma]
    refine ⟨?_, ?_⟩
    · rw [Finset.mem_filter]
      exact ⟨by rw [Finset.mem_Icc]; exact ⟨one_le_mul hm'.1 hNS'.1, hmNx⟩,
             dvd_mul_of_dvd_right hdvd p.1⟩
    · rw [Finset.mem_filter]
      exact ⟨hNS, hdvd, dvd_mul_of_dvd_right (dvd_refl p.2) p.1⟩
  · -- injectivity on the source index set
    intro p1 hp1 p2 hp2 h
    have hh : p1.1 * p1.2 = p2.1 * p2.2 ∧ p1.2 = p2.2 := by simpa using h
    obtain ⟨hK, hN⟩ := hh
    have hp2pos : 0 < p1.2 := by
      rw [Finset.mem_sigma] at hp1
      obtain ⟨_, hNmem⟩ := hp1
      rw [Finset.mem_filter, Finset.mem_Icc] at hNmem
      exact hNmem.1.1
    rw [← hN] at hK
    have hm : p1.1 = p2.1 := Nat.mul_right_cancel hp2pos hK
    rw [Sigma.ext_iff]
    exact ⟨hm, heq_of_eq hN⟩
  · -- surjectivity: the inverse map is `(K, N) ↦ (K/N, N)`
    intro q hq
    rw [Finset.mem_sigma] at hq
    obtain ⟨hK, hN⟩ := hq
    rw [Finset.mem_filter] at hK hN
    obtain ⟨hKS, hdvdK⟩ := hK
    obtain ⟨hNS, hdvdN, hNK⟩ := hN
    have hKS' : 1 ≤ q.1 ∧ q.1 ≤ x := by simpa [Finset.mem_Icc] using hKS
    have hNS' : 1 ≤ q.2 ∧ q.2 ≤ x := by simpa [Finset.mem_Icc] using hNS
    refine ⟨⟨q.1 / q.2, q.2⟩, ?_, ?_⟩
    · rw [Finset.mem_sigma]
      refine ⟨?_, ?_⟩
      · rw [Finset.mem_Icc]
        exact ⟨Nat.div_pos (Nat.le_of_dvd (by omega) hNK) hNS'.1,
               le_trans (Nat.div_le_self q.1 q.2) hKS'.2⟩
      · rw [Finset.mem_filter]
        exact ⟨hNS, hdvdN, by rw [Nat.div_mul_cancel hNK]; exact hKS'.2⟩
    · exact Sigma.ext (Nat.div_mul_cancel hNK) (heq_of_eq rfl)
  · -- the weights agree on matched pairs
    intro p hp
    rw [Finset.mem_sigma] at hp
    obtain ⟨hm, hN⟩ := hp
    rw [Finset.mem_filter] at hN
    obtain ⟨hNS, _, _⟩ := hN
    have hNS' : 1 ≤ p.2 ∧ p.2 ≤ x := by simpa [Finset.mem_Icc] using hNS
    have hpos : 0 < p.2 := by omega
    rw [Nat.mul_div_cancel p.1 hpos]
    ring

theorem tail_arith_step2 (x Pz D : ℕ) :
    (∑ d ∈ Work.FIChain.Dsp Pz D,
        ∑ m ∈ Finset.Icc 1 x, ((m.divisors.card : ℝ)) ^ 2 *
          ∑ N ∈ (Finset.Icc 1 x).filter (fun N => d ∣ N ∧ m * N ≤ x),
            Work.FIChain.atilc (m * N))
      ≤ ∑ d ∈ Work.FIChain.Dsp Pz D,
          ∑ K ∈ (Finset.Icc 1 x).filter (fun K => d ∣ K),
            Work.FIChain.atilc K * ∑ N ∈ (Finset.Icc 1 x).filter (fun N => d ∣ N ∧ N ∣ K),
              ((K / N).divisors.card : ℝ) ^ 2 := by
  classical
  refine Finset.sum_le_sum (fun d _ => ?_)
  exact le_of_eq (tail_arith_step2_inner x d)

end Work.FIChain
