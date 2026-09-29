import Mathlib
import Submission.Work.TMC14Core.Assembly

/-!
# `RatDenomLarge`: rationals with bounded denominator stay away from an irrational

For an irrational `α` and any `N`, the set of rationals `p/q` with `0 < q < N` is closed
(it is a finite union of copies `(1/q) · ℤ` of the integers) and does not contain `α`
(every element is rational).  Hence it has positive distance to `α`, which is the statement
that all rationals with denominator `< N` stay at distance at least some `ρ > 0` from `α`.
-/

namespace Work.TMC14Core

theorem ratDenomLarge : Work.TMC14Core.RatDenomLarge := by
  intro α hα N
  -- The set of rationals with denominator `< N`.
  let S : Set ℝ := {x | ∃ p : ℤ, ∃ q : ℕ, 0 < q ∧ q < N ∧ x = (p : ℝ) / (q : ℝ)}
  -- `S` is a finite union of closed sets: for each `q ∈ {1, …, N-1}`, the set `(1/q) · ℤ` is
  -- the preimage of `ℤ ⊆ ℝ` under the (continuous) map `x ↦ q * x`.
  have hS_closed : IsClosed S := by
    have h_eq : S = ⋃ q ∈ (Finset.Ico 1 N), {x : ℝ | ∃ p : ℤ, x = (p : ℝ) / (q : ℝ)} := by
      ext x
      simp only [S, Set.mem_ofPred_eq, Set.mem_iUnion, Finset.mem_Ico, exists_prop]
      constructor
      · rintro ⟨p, q, hq0, hqN, rfl⟩
        exact ⟨q, ⟨hq0, hqN⟩, p, rfl⟩
      · rintro ⟨q, ⟨hq0, hqN⟩, p, rfl⟩
        exact ⟨p, q, hq0, hqN, rfl⟩
    rw [h_eq]
    refine isClosed_biUnion_finset (fun q hq => ?_)
    have hq1 : 1 ≤ q := (Finset.mem_Ico.mp hq).1
    have hqR : (q : ℝ) ≠ 0 := by exact_mod_cast (show q ≠ 0 by omega)
    have hpre : {x : ℝ | ∃ p : ℤ, x = (p : ℝ) / (q : ℝ)}
        = (fun x : ℝ => (q : ℝ) * x) ⁻¹' (Set.range ((↑) : ℤ → ℝ)) := by
      ext x
      simp only [Set.mem_ofPred_eq, Set.mem_preimage, Set.mem_range]
      constructor
      · rintro ⟨p, rfl⟩
        exact ⟨p, (mul_div_cancel₀ (p : ℝ) hqR).symm⟩
      · rintro ⟨p, hp⟩
        refine ⟨p, ?_⟩
        rw [eq_div_iff hqR, mul_comm x (q : ℝ)]
        exact hp.symm
    rw [hpre]
    exact Real.isClosed_range_intCast.preimage (continuous_const.mul continuous_id)
  -- `α` is not one of those rationals.
  have hαS : α ∉ S := by
    rintro ⟨p, q, hq0, hqN, hpq⟩
    have hq0' : q ≠ 0 := by omega
    have hqR : (q : ℝ) ≠ 0 := by positivity
    have hmul : α * (q : ℝ) = (p : ℝ) := by
      rw [hpq]
      exact div_mul_cancel₀ (p : ℝ) hqR
    have h1 : Irrational (α * (q : ℝ)) := hα.mul_natCast hq0'
    rw [hmul] at h1
    exact Int.not_irrational p h1
  -- Being closed and avoiding `α`, `S` has an open neighbourhood disjoint from it.
  obtain ⟨ε, hεpos, hεball⟩ := Metric.mem_nhds_iff.mp (hS_closed.isOpen_compl.mem_nhds hαS)
  refine ⟨ε, hεpos, ?_⟩
  intro p q hq0 hqN
  by_contra hcon
  have hlt : |α - (p : ℝ) / (q : ℝ)| < ε := not_le.mp hcon
  have hmem : (p : ℝ) / (q : ℝ) ∈ S := ⟨p, q, hq0, hqN, rfl⟩
  have hball : (p : ℝ) / (q : ℝ) ∈ Metric.ball α ε := by
    rw [Metric.mem_ball, Real.dist_eq, abs_sub_comm]
    exact hlt
  exact (hεball hball) hmem

end Work.TMC14Core
