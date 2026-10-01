import Mathlib
import Submission.Work.LinnikAreas.FarRepel.zetaDiffExplicit_of_ballPF

/-!
# Summability of the multiplicity-weighted zero sum of `Λ = completedRiemannZeta`

We reproduce here the proof of the corresponding statement for `Ξ = Work.LinnikAreas.DhK.Xi`
(the private lemma `xiZeroSum_summable` of `Submission/Work/LinnikAreas/FarRepel/zetaDiffExplicit_of_ballPF.lean`)
and transfer it to `Λ = completedRiemannZeta` through the pointwise equality of vanishing orders
`ord_u(Ξ) = ord_u(Λ)`.

The argument: the zeros of `Ξ` lie in the strip `Re u ≤ 1` (`DhK.Xi_zero_re_le_one`), so for
`Re s > 1` and any zero `u` one has `Re s - 1 ≤ ‖s - u‖`, whence `‖(1/(s-u))^{k+1}‖ ≤ A/‖u‖²`
for `‖u‖ ≥ 2`; those of norm `≤ 2` are finite (`MeromorphicOn.divisor` support), and the
inverse-square tail of the zero multiplicities is bounded by `xiCZeroInvSqTailBound`.  This gives a
finite-set tail bound, and `Commons.Analysis.InfiniteSum.summable_of_finset_tail_bound` concludes.
-/

open scoped Classical BigOperators Topology
open Filter

namespace Work.ZeroFreeTables.P9

noncomputable section

/-! ## The vanishing orders of `Ξ` and of `Λ` agree -/

/-- The vanishing multiplicities of the entire completion `Ξ = DhK.Xi` and of
`Λ = completedRiemannZeta` agree everywhere. -/
private lemma analyticOrderNatAt_Xi_eq (u : ℂ) :
    analyticOrderNatAt Work.LinnikAreas.DhK.Xi u
      = analyticOrderNatAt completedRiemannZeta u := by
  by_cases h0 : u = 0
  · subst h0
    have hx : analyticOrderAt Work.LinnikAreas.DhK.Xi 0 = 0 :=
      analyticOrderAt_eq_zero.mpr (Or.inr (by rw [Work.LinnikAreas.DhK.Xi_zero]; norm_num))
    rw [show analyticOrderNatAt Work.LinnikAreas.DhK.Xi 0 = 0 from by
          simp [analyticOrderNatAt, hx],
      analyticOrderNatAt_of_not_analyticAt
        Work.LinnikAreas.not_analyticAt_completedZeta_zero]
  · by_cases h1 : u = 1
    · subst h1
      have hx : analyticOrderAt Work.LinnikAreas.DhK.Xi 1 = 0 :=
        analyticOrderAt_eq_zero.mpr (Or.inr (by
          rw [show Work.LinnikAreas.DhK.Xi 1 = 1 / 2 by simp [Work.LinnikAreas.DhK.Xi]]
          norm_num))
      rw [show analyticOrderNatAt Work.LinnikAreas.DhK.Xi 1 = 0 from by
            simp [analyticOrderNatAt, hx],
        analyticOrderNatAt_of_not_analyticAt
          Work.LinnikAreas.not_analyticAt_completedZeta_one]
    · exact Work.LinnikAreas.analyticOrderNatAt_xiC_eq u h0 h1

/-! ## The zero sum of `Ξ` is summable -/

/-- **Absolute summability of the zeta zero sum.** -/
private lemma xiZeroSum_summable (k : ℕ) (hk : 1 ≤ k) {s : ℂ} (hs : 1 < s.re) :
    Summable (fun u : ℂ =>
      (analyticOrderNatAt Work.LinnikAreas.DhK.Xi u : ℂ) * (1 / (s - u)) ^ (k + 1)) := by
  have hδ : 0 < s.re - 1 := by linarith
  have hfar : ∀ u : ℂ, Work.LinnikAreas.DhK.Xi u = 0 → s.re - 1 ≤ ‖s - u‖ := by
    intro u hu
    have hle : u.re ≤ 1 := Work.LinnikAreas.DhK.Xi_zero_re_le_one hu
    have hre : s.re - 1 ≤ (s - u).re := by simp only [Complex.sub_re]; linarith
    calc s.re - 1 ≤ (s - u).re := hre
      _ ≤ ‖s - u‖ := Complex.re_le_norm _
  have hfin : ({u : ℂ | analyticOrderNatAt Work.LinnikAreas.DhK.Xi u ≠ 0 ∧ ‖u‖ ≤ 2} : Set ℂ).Finite := by
    have h1 : (Function.support (fun u : ℂ =>
        MeromorphicOn.divisor Work.LinnikAreas.DhK.Xi (Metric.closedBall 0 2) u)).Finite :=
      (MeromorphicOn.divisor Work.LinnikAreas.DhK.Xi (Metric.closedBall 0 2)).finiteSupport
        (isCompact_closedBall 0 2)
    refine h1.subset ?_
    intro u hu
    obtain ⟨hord, hnorm⟩ := hu
    rw [Function.mem_support]
    have hmem : u ∈ Metric.closedBall (0 : ℂ) 2 := by
      rw [Metric.mem_closedBall, dist_zero_right]; exact hnorm
    rw [Commons.Analysis.Complex.divisor_eq_analyticOrderNatAt_cast
      (Work.LinnikAreas.DhK.Xi_analyticOnNhd _) hmem]
    exact_mod_cast hord
  obtain ⟨C0, hC0pos, hC0⟩ := Work.LinnikAreas.xiCZeroInvSqTailBound
  let A : ℝ := max ((2 : ℝ) ^ (k + 1)) ((2 * ‖s‖ + 2) ^ 2 / (s.re - 1) ^ (k + 1))
  have hAnn : 0 ≤ A := le_trans (by positivity) (le_max_left _ _)
  set f : ℂ → ℝ := fun u =>
    (analyticOrderNatAt Work.LinnikAreas.DhK.Xi u : ℝ) * ‖(1 / (s - u)) ^ (k + 1)‖ with hfdef
  have hfnn : ∀ u : ℂ, 0 ≤ f u := by intro u; rw [hfdef]; positivity
  have hsmall : ∃ c : ℝ, ∀ t : Finset ℂ, (∀ u ∈ t, ‖u‖ ≤ 2) → ∑ u ∈ t, f u ≤ c := by
    refine ⟨∑ u ∈ hfin.toFinset, f u, ?_⟩
    intro t ht
    calc ∑ u ∈ t, f u ≤ ∑ u ∈ t ∪ hfin.toFinset, f u :=
          Finset.sum_le_sum_of_subset_of_nonneg Finset.subset_union_left (fun i _ _ => hfnn i)
      _ = ∑ u ∈ hfin.toFinset, f u := by
          refine (Finset.sum_subset Finset.subset_union_right ?_).symm
          intro u hu hnot
          have hut : u ∈ t := by
            rcases Finset.mem_union.mp hu with h | h
            · exact h
            · exact absurd h hnot
          have h0 : analyticOrderNatAt Work.LinnikAreas.DhK.Xi u = 0 := by
            by_contra hc
            exact hnot (by rw [Set.Finite.mem_toFinset]; exact ⟨hc, ht u hut⟩)
          rw [hfdef]; simp [h0]
  have htail : ∀ t : Finset ℂ, (∀ u ∈ t, 2 < ‖u‖) → ∑ u ∈ t, f u ≤ A * C0 := by
    intro t ht
    have hpt : ∀ u ∈ t, f u ≤ A * ((analyticOrderNatAt Work.LinnikAreas.DhK.Xi u : ℝ) / ‖u‖ ^ 2) := by
      intro u hu
      by_cases hord : analyticOrderNatAt Work.LinnikAreas.DhK.Xi u = 0
      · rw [hfdef]; simp [hord]
      · have hzu : Work.LinnikAreas.DhK.Xi u = 0 :=
          apply_eq_zero_of_analyticOrderNatAt_ne_zero hord
        have hdist : s.re - 1 ≤ ‖s - u‖ := hfar u hzu
        have h2u : 2 ≤ ‖u‖ := le_of_lt (ht u hu)
        have hupos : 0 < ‖u‖ := by linarith
        have hden : 0 < ‖s - u‖ := lt_of_lt_of_le hδ hdist
        have hb : ‖(1 / (s - u)) ^ (k + 1)‖ ≤ A / ‖u‖ ^ 2 := by
          rw [norm_pow, norm_div, norm_one]
          rcases lt_or_ge (2 * ‖s‖ + 2) ‖u‖ with hlt | hge
          · have htri : ‖u‖ - ‖s‖ ≤ ‖s - u‖ := by
              have h := abs_norm_sub_norm_le u s
              rw [norm_sub_rev u s] at h
              linarith [le_abs_self (‖u‖ - ‖s‖)]
            have hhalf : ‖u‖ / 2 ≤ ‖s - u‖ := by linarith only [htri, hlt]
            have hle1 : (1 : ℝ) / ‖s - u‖ ≤ 2 / ‖u‖ := by
              rw [div_le_div_iff₀ hden hupos]; linarith only [hhalf]
            calc (1 / ‖s - u‖) ^ (k + 1) ≤ (2 / ‖u‖) ^ (k + 1) :=
                  pow_le_pow_left₀ (by positivity) hle1 _
              _ = (2 : ℝ) ^ (k + 1) / ‖u‖ ^ (k + 1) := by rw [div_pow]
              _ ≤ (2 : ℝ) ^ (k + 1) / ‖u‖ ^ 2 :=
                  div_le_div_of_nonneg_left (by positivity) (by positivity)
                    (pow_le_pow_right₀ (by linarith : 1 ≤ ‖u‖) (by omega : 2 ≤ k + 1))
              _ ≤ A / ‖u‖ ^ 2 :=
                  div_le_div_of_nonneg_right (le_max_left _ _) (by positivity)
          · have hun : ‖u‖ ^ 2 ≤ A * (s.re - 1) ^ (k + 1) := by
              have h1 : (2 * ‖s‖ + 2) ^ 2 ≤ A * (s.re - 1) ^ (k + 1) := by
                have hA : (2 * ‖s‖ + 2) ^ 2 / (s.re - 1) ^ (k + 1) ≤ A := le_max_right _ _
                exact (div_le_iff₀ (pow_pos hδ _)).mp hA
              have h2 : ‖u‖ ^ 2 ≤ (2 * ‖s‖ + 2) ^ 2 :=
                pow_le_pow_left₀ (norm_nonneg u) hge 2
              linarith
            have hfin2 : (1 / (s.re - 1)) ^ (k + 1) ≤ A / ‖u‖ ^ 2 := by
              rw [one_div_pow, div_le_div_iff₀ (by positivity) (by positivity)]
              linarith
            calc (1 / ‖s - u‖) ^ (k + 1) ≤ (1 / (s.re - 1)) ^ (k + 1) :=
                  pow_le_pow_left₀ (by positivity) (one_div_le_one_div_of_le hδ hdist) _
              _ ≤ A / ‖u‖ ^ 2 := hfin2
        calc (analyticOrderNatAt Work.LinnikAreas.DhK.Xi u : ℝ) * ‖(1 / (s - u)) ^ (k + 1)‖
            ≤ (analyticOrderNatAt Work.LinnikAreas.DhK.Xi u : ℝ) * (A / ‖u‖ ^ 2) :=
              mul_le_mul_of_nonneg_left hb (Nat.cast_nonneg _)
          _ = A * ((analyticOrderNatAt Work.LinnikAreas.DhK.Xi u : ℝ) / ‖u‖ ^ 2) := by ring
    calc ∑ u ∈ t, f u
        ≤ ∑ u ∈ t, A * ((analyticOrderNatAt Work.LinnikAreas.DhK.Xi u : ℝ) / ‖u‖ ^ 2) :=
          Finset.sum_le_sum hpt
      _ = A * ∑ u ∈ t, ((analyticOrderNatAt Work.LinnikAreas.DhK.Xi u : ℝ) / ‖u‖ ^ 2) := by
          rw [Finset.mul_sum]
      _ ≤ A * C0 := mul_le_mul_of_nonneg_left (hC0 t ht) hAnn
  have hsumm_f : Summable f :=
    Commons.Analysis.InfiniteSum.summable_of_finset_tail_bound hfnn hsmall htail
  refine Summable.of_norm ?_
  rw [show (fun u : ℂ => ‖(analyticOrderNatAt Work.LinnikAreas.DhK.Xi u : ℂ)
        * (1 / (s - u)) ^ (k + 1)‖) = f from funext fun u => by
      rw [hfdef, norm_mul, Complex.norm_natCast]]
  exact hsumm_f

/-! ## Transfer to `Λ = completedRiemannZeta` -/

/-- **Summability of the multiplicity-weighted zero sum of the completed Riemann zeta function.**
`Λ = completedRiemannZeta`, `ord_u(Λ) = analyticOrderNatAt Λ u`.  For `k ≥ 1` and `1 < Re s` the
family `u ↦ ord_u(Λ)·(1/(s-u))^{k+1}` is summable (the zeros of `Λ` are the non-trivial zeros of
`ζ`, they lie in `0 < Re u < 1`).

ROUTE: the identical statement for `Ξ = Work.LinnikAreas.DhK.Xi` is proved *privately* inside
`Submission/Work/LinnikAreas/FarRepel/zetaDiffExplicit_of_ballPF.lean` (lemma
`xiZeroSum_summable`): read it there and reproduce it here, then transfer to `Λ` using the pointwise
equality of vanishing orders `ord_u(Ξ) = ord_u(Λ)` (the *private* lemma `analyticOrderNatAt_Xi_eq`
in the same file; ingredients: `Work.LinnikAreas.analyticOrderNatAt_xiC_eq`, `DhK.Xi_zero`,
`Xi 1 = 1/2` by `simp [DhK.Xi]`, `Work.LinnikAreas.not_analyticAt_completedZeta_zero`, `.._one`). -/
theorem zetaZeroSum_summable_gen (k : ℕ) (hk : 1 ≤ k) {s : ℂ} (hs : 1 < s.re) :
    Summable (fun u : ℂ => (analyticOrderNatAt completedRiemannZeta u : ℂ) * (1 / (s - u)) ^ (k + 1)) := by
  rw [show (fun u : ℂ => (analyticOrderNatAt completedRiemannZeta u : ℂ)
        * (1 / (s - u)) ^ (k + 1))
      = (fun u : ℂ => (analyticOrderNatAt Work.LinnikAreas.DhK.Xi u : ℂ)
        * (1 / (s - u)) ^ (k + 1)) from funext fun u => by rw [analyticOrderNatAt_Xi_eq u]]
  exact xiZeroSum_summable k hk hs

end

end Work.ZeroFreeTables.P9
