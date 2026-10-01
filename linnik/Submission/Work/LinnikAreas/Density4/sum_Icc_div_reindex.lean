import Mathlib

namespace Work.LinnikAreas.Density4

/-- Reindexing identity: summing a function of pairs `(d, m)` with `1 ≤ d ≤ N`, `P d`,
`1 ≤ m ≤ N / d` is the same as summing over `n ≤ N` and the divisors `d` of `n`
satisfying `P d`, with `m = n / d`.  The implicit bijection is `(d, m) ↦ (d * m, d)`. -/
theorem sum_Icc_div_reindex {M : Type*} [AddCommMonoid M] (N : ℕ) (P : ℕ → Prop)
    [DecidablePred P] (Φ : ℕ → ℕ → M) :
    (∑ d ∈ (Finset.Icc 1 N).filter P, ∑ m ∈ Finset.Icc 1 (N / d), Φ d m)
      = ∑ n ∈ Finset.Icc 1 N, ∑ d ∈ n.divisors.filter P, Φ d (n / d) := by
  classical
  rw [Finset.sum_sigma', Finset.sum_sigma']
  refine Finset.sum_bij
    (fun (x : Sigma fun _ : ℕ => ℕ) _ => (⟨x.1 * x.2, x.1⟩ : Sigma fun _ : ℕ => ℕ)) ?_ ?_ ?_ ?_
  · -- `(d, m) ↦ (d * m, d)` lands in `(Icc 1 N).sigma (fun n => n.divisors.filter P)`
    intro x hx
    simp only [Finset.mem_sigma, Finset.mem_filter, Finset.mem_Icc] at hx
    obtain ⟨⟨⟨hxIcc1, hxIcc2⟩, hxP⟩, hx21, hx22⟩ := hx
    have h1 : x.1 ≠ 0 := by omega
    have h2 : x.2 ≠ 0 := by omega
    simp only [Finset.mem_sigma, Finset.mem_Icc, Finset.mem_filter]
    refine ⟨⟨?_, ?_⟩, ?_, hxP⟩
    · exact Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero h1 h2)
    · calc x.1 * x.2 ≤ x.1 * (N / x.1) := Nat.mul_le_mul_left x.1 hx22
        _ ≤ N := Nat.mul_div_le N x.1
    · rw [Nat.mem_divisors]
      exact ⟨dvd_mul_right x.1 x.2, Nat.mul_ne_zero h1 h2⟩
  · -- injectivity
    intro x1 hx1 x2 hx2 heq
    obtain ⟨d1, m1⟩ := x1
    obtain ⟨d2, m2⟩ := x2
    rw [Sigma.mk.injEq] at heq
    obtain ⟨hf, hs⟩ := heq
    have hseq : d1 = d2 := eq_of_heq hs
    have hd1pos : 0 < d1 := by
      simp only [Finset.mem_sigma, Finset.mem_filter, Finset.mem_Icc] at hx1
      omega
    subst hseq
    have hm : m1 = m2 := Nat.mul_left_cancel hd1pos hf
    rw [hm]
  · -- surjectivity
    intro y hy
    obtain ⟨n, d⟩ := y
    simp only [Finset.mem_sigma, Finset.mem_filter, Finset.mem_Icc] at hy
    obtain ⟨⟨hyn1, hynN⟩, hydmem, hyP⟩ := hy
    rw [Nat.mem_divisors] at hydmem
    obtain ⟨hydvd, hynz⟩ := hydmem
    have hdpos : 0 < d := Nat.pos_of_dvd_of_pos hydvd (Nat.pos_of_ne_zero hynz)
    have hdn : d ≤ n := Nat.le_of_dvd (Nat.pos_of_ne_zero hynz) hydvd
    refine ⟨⟨d, n / d⟩, ?_, ?_⟩
    · simp only [Finset.mem_sigma, Finset.mem_filter, Finset.mem_Icc]
      exact ⟨⟨⟨show 1 ≤ d by omega, le_trans hdn hynN⟩, hyP⟩,
             (Nat.one_le_div_iff hdpos).mpr hdn, Nat.div_le_div_right hynN⟩
    · show (⟨d * (n / d), d⟩ : Sigma fun _ : ℕ => ℕ) = ⟨n, d⟩
      rw [Nat.mul_div_cancel' hydvd]
  · -- the two summands agree: `Φ d m = Φ d ((d * m) / d)`
    intro x hx
    simp only [Finset.mem_sigma, Finset.mem_filter, Finset.mem_Icc] at hx
    obtain ⟨hxIcc, _⟩ := hx
    have hpos : 0 < x.1 := by omega
    rw [Nat.mul_div_right x.2 hpos]

end Work.LinnikAreas.Density4
