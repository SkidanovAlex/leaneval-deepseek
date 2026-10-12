import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.InnerProductSpace.PiL2
import Submission.Work.BoseBoxFock.PCFU.kappaL_windowSum_le
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.PCFU.windowPartialSumLe` — the windowed partial sum of `‖kinFT W‖²/‖κ‖²`

This is a short assembly on top of the sharp lattice window sum
`Work.BoseBoxFock.PCFU.kappaL_windowSum_le`

    ∑_{n ∈ S, Λ ≤ ‖κ_n‖}  1 / ((1 + ‖κ_n‖)² ‖κ_n‖²)  ≤  C · ℓ³ / Λ ,      κ_n = kappaL ℓ n .

Suppose the Fourier transform of the one-body state `W` obeys the decay hypothesis

    ‖kinFT W q‖ ≤ K / (1 + ‖q‖)      for every momentum q .

Then on the window `Λ ≤ ‖κ_n‖` the summand `‖kinFT W κ_n‖² / ‖κ_n‖²` is dominated pointwise by

    K² / ((1 + ‖κ_n‖)² ‖κ_n‖²) ,

and summing that over the windowed lattice momenta and invoking the lattice window sum gives

    ∑_{n ∈ u, Λ ≤ ‖κ_n‖} ‖kinFT W κ_n‖² / ‖κ_n‖²  ≤  C · K² · ℓ³ / Λ ,

which is the statement, with the *same* constant `C` as the lattice lemma.

No positivity of `‖κ_n‖` is needed: on the window it follows from `0 < Λ`, and off the window the
`if … then 1 else 0` factor kills the summand (and in any case division by `0` is `0`).
-/

namespace Work.BoseBoxFock.PCFU

noncomputable section

open Finset

theorem windowPartialSumLe : ∃ C : ℝ, 0 ≤ C ∧
    ∀ {ℓ Λ K : ℝ} {W : EuclideanSpace ℝ (Fin 3) → ℂ},
      0 < ℓ → 0 < Λ → 0 ≤ K →
      (∀ q : EuclideanSpace ℝ (Fin 3),
        ‖Submission.BoseGases.kinFT W q‖ ≤ K / (1 + ‖q‖)) →
      ∀ u : Finset (Fin 3 → ℤ),
        ∑ n ∈ u,
            (if Λ ≤ ‖Work.BoseBoxFock.kappaL ℓ n‖ then (1 : ℝ) else 0)
              * (‖Submission.BoseGases.kinFT W (Work.BoseBoxFock.kappaL ℓ n)‖ ^ 2
                  / ‖Work.BoseBoxFock.kappaL ℓ n‖ ^ 2)
          ≤ C * K ^ 2 * ℓ ^ 3 / Λ := by
  obtain ⟨C, hC, hbound⟩ := kappaL_windowSum_le
  refine ⟨C, hC, ?_⟩
  intro ℓ Λ K W hℓ hΛ hK hW u
  classical
  -- 1. The `if`-weighted sum over `u` is the sum over the windowed sub-finset.
  have hcongr : ∑ n ∈ u,
        (if Λ ≤ ‖Work.BoseBoxFock.kappaL ℓ n‖ then (1 : ℝ) else 0)
          * (‖Submission.BoseGases.kinFT W (Work.BoseBoxFock.kappaL ℓ n)‖ ^ 2
              / ‖Work.BoseBoxFock.kappaL ℓ n‖ ^ 2)
      = ∑ n ∈ u.filter (fun n => Λ ≤ ‖Work.BoseBoxFock.kappaL ℓ n‖),
          ‖Submission.BoseGases.kinFT W (Work.BoseBoxFock.kappaL ℓ n)‖ ^ 2
            / ‖Work.BoseBoxFock.kappaL ℓ n‖ ^ 2 := by
    rw [Finset.sum_filter]
    exact Finset.sum_congr rfl (fun n _ =>
      by by_cases h : Λ ≤ ‖Work.BoseBoxFock.kappaL ℓ n‖ <;> simp [h])
  rw [hcongr]
  -- 2. The pointwise domination by the lattice-lemma summand.
  have hpt : ∀ n ∈ u.filter (fun n => Λ ≤ ‖Work.BoseBoxFock.kappaL ℓ n‖),
      ‖Submission.BoseGases.kinFT W (Work.BoseBoxFock.kappaL ℓ n)‖ ^ 2
        / ‖Work.BoseBoxFock.kappaL ℓ n‖ ^ 2
      ≤ K ^ 2 / ((1 + ‖Work.BoseBoxFock.kappaL ℓ n‖) ^ 2
          * ‖Work.BoseBoxFock.kappaL ℓ n‖ ^ 2) := by
    intro n _
    have h1 : ‖Submission.BoseGases.kinFT W (Work.BoseBoxFock.kappaL ℓ n)‖ ^ 2
        ≤ (K / (1 + ‖Work.BoseBoxFock.kappaL ℓ n‖)) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) (hW _) 2
    calc ‖Submission.BoseGases.kinFT W (Work.BoseBoxFock.kappaL ℓ n)‖ ^ 2
          / ‖Work.BoseBoxFock.kappaL ℓ n‖ ^ 2
        ≤ (K / (1 + ‖Work.BoseBoxFock.kappaL ℓ n‖)) ^ 2
            / ‖Work.BoseBoxFock.kappaL ℓ n‖ ^ 2 :=
          div_le_div_of_nonneg_right h1 (by positivity)
      _ = K ^ 2 / ((1 + ‖Work.BoseBoxFock.kappaL ℓ n‖) ^ 2
            * ‖Work.BoseBoxFock.kappaL ℓ n‖ ^ 2) := by
          rw [div_pow, div_div]
  -- 3. Sum, factor out `K²`, apply the lattice window sum.
  calc ∑ n ∈ u.filter (fun n => Λ ≤ ‖Work.BoseBoxFock.kappaL ℓ n‖),
        ‖Submission.BoseGases.kinFT W (Work.BoseBoxFock.kappaL ℓ n)‖ ^ 2
          / ‖Work.BoseBoxFock.kappaL ℓ n‖ ^ 2
      ≤ ∑ n ∈ u.filter (fun n => Λ ≤ ‖Work.BoseBoxFock.kappaL ℓ n‖),
          K ^ 2 / ((1 + ‖Work.BoseBoxFock.kappaL ℓ n‖) ^ 2
            * ‖Work.BoseBoxFock.kappaL ℓ n‖ ^ 2) := Finset.sum_le_sum hpt
    _ = K ^ 2 * ∑ n ∈ u.filter (fun n => Λ ≤ ‖Work.BoseBoxFock.kappaL ℓ n‖),
          1 / ((1 + ‖Work.BoseBoxFock.kappaL ℓ n‖) ^ 2
            * ‖Work.BoseBoxFock.kappaL ℓ n‖ ^ 2) := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl (fun n _ => by rw [mul_one_div])
    _ ≤ K ^ 2 * (C * ℓ ^ 3 / Λ) :=
        mul_le_mul_of_nonneg_left
          (hbound hℓ hΛ (u.filter (fun n => Λ ≤ ‖Work.BoseBoxFock.kappaL ℓ n‖))
            (fun n hn => (Finset.mem_filter.mp hn).2))
          (by positivity)
    _ = C * K ^ 2 * ℓ ^ 3 / Λ := by ring

end

end Work.BoseBoxFock.PCFU
