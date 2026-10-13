import Mathlib
import Submission.Work.DSM2p.N5_helpers
import Submission.Work.DSM2p.N5c_exists_monic_root

namespace Work.DSM2p

/-- **Node `N5`, part (b).**  Let `Λ = A[T^{1/p^∞}]`, `ϖ_k := algebraMap A Λ (P.ϖ k)`, and let
`q : ℕ → Λ` be a compatible system of `p`-power roots modulo `ϖ_0^{m+1}`, with `q 0` a good
approximation of `F(T)` modulo `ϖ_N`.  Then every `q j` is congruent, modulo `ϖ_{j+N}`, to the
value at `T^{1/p^j}` of a *monic* polynomial over `A`.

Indeed `ϖ_0 = ϖ_N ^ (p ^ N)` (root system), so both `(ϖ_0^{m+1})` and — because
`ϖ_0 ^ p = p · unit` — `(p)` are contained in `(ϖ_N)`.  Hence, modulo `ϖ_N`,

`q j ^ (p ^ j) ≡ q 0 ≡ F(T) ≡ (g_j(T^{1/p^j})) ^ (p ^ j)`,

where `g_j` is the monic `p ^ j`-th root of `F` modulo `p` produced by `N5c`.  The Freshman's
dream `(x - y) ^ (p ^ j) ≡ x ^ (p ^ j) - y ^ (p ^ j) (mod p)` then gives

`(g_j(T^{1/p^j}) - q j) ^ (p ^ j) ∈ (ϖ_N)`,

and iterated (scaled) Frobenius injectivity `varpi_iterate_mem` yields
`g_j(T^{1/p^j}) - q j ∈ (ϖ_{N+j})`. -/
theorem N5_AAL_Lam_b (A : Type*) [CommRing A] (p : ℕ) [Fact p.Prime]
    (P : DSMap.PerfectoidData p A) (F : Polynomial A) (hF : F.Monic) (m : ℕ)
    (q : ℕ → Lam1 A p) (N : ℕ) (hN : 0 < N)
    (hcongr : ∀ j, q (j + 1) ^ p - q j ∈
      Ideal.span {algebraMap A (Lam1 A p) (P.ϖ 0 ^ (m + 1))})
    (ha : Polynomial.aeval (T1 A p 0) F - q 0 ∈
      Ideal.span {algebraMap A (Lam1 A p) (P.ϖ N)}) :
    ∀ j, ∃ n : ℕ, ∃ g : Polynomial A, g.Monic ∧
      q j - Polynomial.aeval (T1 A p n) g ∈
        Ideal.span {algebraMap A (Lam1 A p) (P.ϖ (j + N))} := by
  classical
  have hp : p.Prime := Fact.out
  -- `ϖ_0 = ϖ_N ^ (p ^ N)`, hence `ϖ_0 ∈ (ϖ_N)`
  have hϖ0mem : algebraMap A (Lam1 A p) (P.ϖ 0) ∈
      Ideal.span {algebraMap A (Lam1 A p) (P.ϖ N)} := by
    rw [← Lam1_varpi_pow A p P N]
    exact Ideal.pow_mem_of_mem _ (Ideal.mem_span_singleton_self _) _
      (pow_pos hp.pos N)
  have hspan0 : Ideal.span {algebraMap A (Lam1 A p) (P.ϖ 0)} ≤
      Ideal.span {algebraMap A (Lam1 A p) (P.ϖ N)} :=
    Ideal.span_le.mpr (Set.singleton_subset_iff.mpr hϖ0mem)
  -- `ϖ_0 ^ p = p * unit`, hence `p ∈ (ϖ_0) ⊆ (ϖ_N)`
  have hpmem : (p : Lam1 A p) ∈ Ideal.span {algebraMap A (Lam1 A p) (P.ϖ N)} := by
    obtain ⟨v, hv⟩ := P.unit
    let vu : (Lam1 A p)ˣ := Units.map (algebraMap A (Lam1 A p)) v
    have hvp : (algebraMap A (Lam1 A p) (P.ϖ 0)) ^ p = (p : Lam1 A p) * (vu : Lam1 A p) := by
      show (algebraMap A (Lam1 A p) (P.ϖ 0)) ^ p
        = (p : Lam1 A p) * algebraMap A (Lam1 A p) (v : A)
      rw [← map_pow, hv, map_mul, map_natCast]
    have h0p : (algebraMap A (Lam1 A p) (P.ϖ 0)) ^ p ∈
        Ideal.span {algebraMap A (Lam1 A p) (P.ϖ N)} :=
      hspan0 (Ideal.pow_mem_of_mem _ (Ideal.mem_span_singleton_self _) p hp.pos)
    have hp_eq : (p : Lam1 A p) = (algebraMap A (Lam1 A p) (P.ϖ 0)) ^ p * ↑vu⁻¹ := by
      rw [hvp, mul_assoc, Units.mul_inv, mul_one]
    rw [hp_eq]
    exact Ideal.mul_mem_right _ _ h0p
  have hspanp : Ideal.span {(p : Lam1 A p)} ≤
      Ideal.span {algebraMap A (Lam1 A p) (P.ϖ N)} :=
    Ideal.span_le.mpr (Set.singleton_subset_iff.mpr hpmem)
  -- `(ϖ_0 ^ (m + 1)) ⊆ (ϖ_N)`
  have hspan_ϖ0pow : Ideal.span {algebraMap A (Lam1 A p) (P.ϖ 0 ^ (m + 1))} ≤
      Ideal.span {algebraMap A (Lam1 A p) (P.ϖ N)} := by
    refine Ideal.span_le.mpr (Set.singleton_subset_iff.mpr ?_)
    rw [map_pow, ← Lam1_varpi_pow A p P N, ← pow_mul]
    exact Ideal.pow_mem_of_mem _ (Ideal.mem_span_singleton_self _) _
      (Nat.mul_pos (pow_pos hp.pos N) (Nat.succ_pos m))
  intro j
  obtain ⟨g, hgmonic, hg⟩ := N5c_exists_monic_root A p P F hF j
  -- the three summands of `(g(T^{1/p^j})) ^ (p ^ j) - q j ^ (p ^ j)`, all in `(ϖ_N)`
  have h1 : q j ^ (p ^ j) - q 0 ∈ Ideal.span {algebraMap A (Lam1 A p) (P.ϖ N)} :=
    hspan_ϖ0pow (pow_pow_sub_mem_of_root_congr q p
      (Ideal.span {algebraMap A (Lam1 A p) (P.ϖ 0 ^ (m + 1))}) hcongr j)
  have h2 : Polynomial.aeval (T1 A p 0) F - q 0 ∈
      Ideal.span {algebraMap A (Lam1 A p) (P.ϖ N)} := ha
  have h3 : (Polynomial.aeval (T1 A p j) g) ^ (p ^ j) - Polynomial.aeval (T1 A p 0) F ∈
      Ideal.span {algebraMap A (Lam1 A p) (P.ϖ N)} := hspanp hg
  have hdiff : (Polynomial.aeval (T1 A p j) g) ^ (p ^ j) - q j ^ (p ^ j) ∈
      Ideal.span {algebraMap A (Lam1 A p) (P.ϖ N)} := by
    have hsum : (Polynomial.aeval (T1 A p j) g) ^ (p ^ j) - q j ^ (p ^ j)
        = ((Polynomial.aeval (T1 A p j) g) ^ (p ^ j) - Polynomial.aeval (T1 A p 0) F)
          + ((Polynomial.aeval (T1 A p 0) F - q 0) - (q j ^ (p ^ j) - q 0)) := by ring
    rw [hsum]
    exact Ideal.add_mem _ h3 (Ideal.sub_mem _ h2 h1)
  -- Freshman's dream: `(g(T^{1/p^j}) - q j) ^ (p ^ j) ∈ (ϖ_N)`
  have hd : (Polynomial.aeval (T1 A p j) g - q j) ^ (p ^ j) ∈
      Ideal.span {algebraMap A (Lam1 A p) (P.ϖ N)} := by
    have hfresh := sub_pow_pow_sub_mem_span_p hp j (Polynomial.aeval (T1 A p j) g) (q j)
    have hsum : (Polynomial.aeval (T1 A p j) g - q j) ^ (p ^ j)
        = ((Polynomial.aeval (T1 A p j) g - q j) ^ (p ^ j)
            - ((Polynomial.aeval (T1 A p j) g) ^ (p ^ j) - q j ^ (p ^ j)))
          + ((Polynomial.aeval (T1 A p j) g) ^ (p ^ j) - q j ^ (p ^ j)) := by ring
    rw [hsum]
    exact Ideal.add_mem _ (hspanp hfresh) hdiff
  -- iterated scaled Frobenius injectivity gives the claim at level `N + j = j + N`
  have hmem := varpi_iterate_mem A p P (Polynomial.aeval (T1 A p j) g - q j) N j hd
  rw [Nat.add_comm N j] at hmem
  refine ⟨j, g, hgmonic, ?_⟩
  have hneg : q j - Polynomial.aeval (T1 A p j) g
      = 0 - (Polynomial.aeval (T1 A p j) g - q j) := by ring
  rw [hneg]
  exact Ideal.sub_mem _ (Ideal.zero_mem _) hmem

end Work.DSM2p
