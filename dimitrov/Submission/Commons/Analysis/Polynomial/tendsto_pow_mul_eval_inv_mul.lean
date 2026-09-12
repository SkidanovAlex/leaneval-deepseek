import Mathlib.Algebra.Polynomial.Eval.Degree
import Mathlib.Analysis.CStarAlgebra.Classes

open Filter Finset
open scoped Topology

namespace Commons.Analysis.Polynomial

theorem tendsto_pow_mul_eval_inv_mul {P : Polynomial ℂ} (hP : Polynomial.Monic P) {N : ℕ}
    (hN : Polynomial.natDegree P = N) {D : ℂ → ℂ} (hD : ContinuousAt D 0) (hD0 : D 0 = 1) :
    Filter.Tendsto (fun u : ℂ => u ^ N * Polynomial.eval (u⁻¹ * D u) P)
      (nhdsWithin (0 : ℂ) {(0 : ℂ)}ᶜ) (nhds 1) := by
  -- The expression equals, on the punctured neighbourhood of 0, the finite sum
  -- `∑ k ≤ N, coeff_k * u^{N-k} * (D u)^k`.
  set g : ℂ → ℂ := fun u => ∑ k ∈ Finset.range (N + 1), P.coeff k * u ^ (N - k) * (D u) ^ k with hgdef
  have hcoeff : P.coeff N = 1 := by
    rw [← hN]; exact hP.coeff_natDegree
  -- Eventually-equality of the two expressions on {0}ᶜ.
  have hEq : (fun u : ℂ => u ^ N * Polynomial.eval (u⁻¹ * D u) P) =ᶠ[nhdsWithin (0 : ℂ) {(0 : ℂ)}ᶜ] g := by
    filter_upwards [self_mem_nhdsWithin] with u hu
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff] at hu
    have key : u ^ N * Polynomial.eval (u⁻¹ * D u) P
        = ∑ k ∈ Finset.range (N + 1), P.coeff k * u ^ (N - k) * (D u) ^ k := by
      rw [Polynomial.eval_eq_sum_range' (p := P) (n := N + 1) (by rw [hN]; exact Nat.lt_succ_self N)
            (u⁻¹ * D u)]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k hk
      have hkN : k ≤ N := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
      have h2 : u ^ N * (u⁻¹) ^ k = u ^ (N - k) := by
        have h1 : u ^ (N - k) * u ^ k = u ^ N := by
          rw [← pow_add, Nat.sub_add_cancel hkN]
        rw [← h1, mul_assoc, ← mul_pow, mul_inv_cancel₀ hu, one_pow, mul_one]
      calc u ^ N * (P.coeff k * (u⁻¹ * D u) ^ k)
          = P.coeff k * (u ^ N * ((u⁻¹) ^ k * (D u) ^ k)) := by rw [mul_pow]; ring
        _ = P.coeff k * (u ^ (N - k) * (D u) ^ k) := by
              rw [show u ^ N * ((u⁻¹) ^ k * (D u) ^ k) = (u ^ N * (u⁻¹) ^ k) * (D u) ^ k by ring,
                  h2]
        _ = P.coeff k * u ^ (N - k) * (D u) ^ k := by ring
    simpa [hgdef] using key
  -- Limit of the sum.
  have hsum : (∑ k ∈ Finset.range (N + 1), P.coeff k * (0 : ℂ) ^ (N - k) * (1 : ℂ) ^ k) = 1 := by
    rw [Finset.sum_eq_single N]
    · rw [Nat.sub_self, pow_zero, mul_one, one_pow, mul_one]
      exact hcoeff
    · intro b hb hbne
      have hbN : b < N := by
        have h1 : b < N + 1 := Finset.mem_range.mp hb
        omega
      have hne : N - b ≠ 0 := by omega
      simp [zero_pow hne]
    · intro hmem
      exact absurd (Finset.mem_range.mpr (Nat.lt_succ_self N)) hmem
  have hg_tendsto : Filter.Tendsto g (nhdsWithin (0 : ℂ) {(0 : ℂ)}ᶜ) (nhds 1) := by
    have hbase : Filter.Tendsto g (nhdsWithin (0 : ℂ) {(0 : ℂ)}ᶜ)
        (nhds (∑ k ∈ Finset.range (N + 1), P.coeff k * (0 : ℂ) ^ (N - k) * (1 : ℂ) ^ k)) := by
      rw [hgdef]
      refine tendsto_finsetSum _ (fun k hk => ?_)
      have h_u : Filter.Tendsto (fun u : ℂ => u ^ (N - k))
          (nhdsWithin (0 : ℂ) {(0 : ℂ)}ᶜ) (nhds ((0 : ℂ) ^ (N - k))) :=
        ((continuousAt_id (x := (0 : ℂ))).pow (N - k)).tendsto.mono_left (nhdsWithin_le_nhds (s := {(0 : ℂ)}ᶜ))
      have h_D : Filter.Tendsto (fun u : ℂ => (D u) ^ k)
          (nhdsWithin (0 : ℂ) {(0 : ℂ)}ᶜ) (nhds ((1 : ℂ) ^ k)) := by
        have h : Filter.Tendsto (fun u : ℂ => D u ^ k)
            (nhdsWithin (0 : ℂ) {(0 : ℂ)}ᶜ) (nhds (D 0 ^ k)) :=
          (hD.pow k).tendsto.mono_left (nhdsWithin_le_nhds (s := {(0 : ℂ)}ᶜ))
        simpa [hD0] using h
      exact (tendsto_const_nhds.mul h_u).mul h_D
    rwa [hsum] at hbase
  exact Filter.Tendsto.congr' hEq.symm hg_tendsto

end Commons.Analysis.Polynomial