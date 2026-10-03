import Mathlib
import Submission.Work.Analysis.Variation.Dyadic

namespace Work.Analysis.Variation

/-- The two-dimensional dyadic telescoping: for `N < 2 ^ M` and `a : ℕ → ℕ → ℂ` vanishing on
the axes (`a k 0 = 0`, `a 0 k = 0`),
`∑_{m₁ < M} ∑_{m₂ < M} (a (rnd N m₁) (rnd N m₂) - a (rnd N (m₁+1)) (rnd N m₂)
  - a (rnd N m₁) (rnd N (m₂+1)) + a (rnd N (m₁+1)) (rnd N (m₂+1))) = a N N`.
Proof: apply the one-dimensional telescoping `telescope_rnd` (in `Submission.Work.Analysis.Variation.Dyadic`)
in the second coordinate to each term, then use `Finset.sum_sub_distrib`, and finally apply
`telescope_rnd` to `g m = a (rnd N m) N` in the first coordinate; the boundary terms vanish by the
axis assumptions (`rnd N 0 = N`, `rnd N M = 0`). -/
theorem telescope2_rnd (a : ℕ → ℕ → ℂ) (h1 : ∀ k, a k 0 = 0) (h2 : ∀ k, a 0 k = 0)
    {N M : ℕ} (h : N < 2 ^ M) :
    ∑ m₁ ∈ Finset.range M, ∑ m₂ ∈ Finset.range M,
        (a (rnd N m₁) (rnd N m₂) - a (rnd N (m₁ + 1)) (rnd N m₂)
          - a (rnd N m₁) (rnd N (m₂ + 1)) + a (rnd N (m₁ + 1)) (rnd N (m₂ + 1)))
      = a N N := by
  -- For each first-coordinate slice, the inner sum is a one-dimensional telescoping
  -- in the second coordinate: regroup the summand as
  -- `(b₁ (rnd N m₂) - b₁ (rnd N (m₂+1))) - (b₂ (rnd N m₂) - b₂ (rnd N (m₂+1)))`
  -- with `b₁ = a (rnd N m₁)` and `b₂ = a (rnd N (m₁+1))`, split by `Finset.sum_sub_distrib`,
  -- and telescope each half with `telescope_rnd`.  The boundary terms `bᵢ 0` vanish by `h1`.
  have key : ∀ m₁ : ℕ, ∑ m₂ ∈ Finset.range M,
        (a (rnd N m₁) (rnd N m₂) - a (rnd N (m₁ + 1)) (rnd N m₂)
          - a (rnd N m₁) (rnd N (m₂ + 1)) + a (rnd N (m₁ + 1)) (rnd N (m₂ + 1)))
      = a (rnd N m₁) N - a (rnd N (m₁ + 1)) N := by
    intro m₁
    have e : ∀ m₂ : ℕ,
        (a (rnd N m₁) (rnd N m₂) - a (rnd N (m₁ + 1)) (rnd N m₂)
          - a (rnd N m₁) (rnd N (m₂ + 1)) + a (rnd N (m₁ + 1)) (rnd N (m₂ + 1)))
        = (a (rnd N m₁) (rnd N m₂) - a (rnd N m₁) (rnd N (m₂ + 1)))
          - (a (rnd N (m₁ + 1)) (rnd N m₂) - a (rnd N (m₁ + 1)) (rnd N (m₂ + 1))) :=
      fun m₂ => by ring
    calc ∑ m₂ ∈ Finset.range M,
          (a (rnd N m₁) (rnd N m₂) - a (rnd N (m₁ + 1)) (rnd N m₂)
            - a (rnd N m₁) (rnd N (m₂ + 1)) + a (rnd N (m₁ + 1)) (rnd N (m₂ + 1)))
        = ∑ m₂ ∈ Finset.range M,
            ((a (rnd N m₁) (rnd N m₂) - a (rnd N m₁) (rnd N (m₂ + 1)))
              - (a (rnd N (m₁ + 1)) (rnd N m₂) - a (rnd N (m₁ + 1)) (rnd N (m₂ + 1)))) :=
          Finset.sum_congr rfl (fun m₂ _ => e m₂)
      _ = (∑ m₂ ∈ Finset.range M,
              (a (rnd N m₁) (rnd N m₂) - a (rnd N m₁) (rnd N (m₂ + 1))))
          - ∑ m₂ ∈ Finset.range M,
              (a (rnd N (m₁ + 1)) (rnd N m₂) - a (rnd N (m₁ + 1)) (rnd N (m₂ + 1))) :=
          Finset.sum_sub_distrib _ _
      _ = (a (rnd N m₁) N - a (rnd N m₁) 0) - (a (rnd N (m₁ + 1)) N - a (rnd N (m₁ + 1)) 0) := by
          rw [telescope_rnd (a (rnd N m₁)) h, telescope_rnd (a (rnd N (m₁ + 1))) h]
      _ = a (rnd N m₁) N - a (rnd N (m₁ + 1)) N := by
          rw [h1 (rnd N m₁), h1 (rnd N (m₁ + 1))]; ring
  -- Rewrite each inner sum with `key`; what remains is a one-dimensional telescoping of
  -- `g k = a k N` in the first coordinate, whose boundary term `g 0 = a 0 N` vanishes by `h2`.
  calc ∑ m₁ ∈ Finset.range M, ∑ m₂ ∈ Finset.range M,
          (a (rnd N m₁) (rnd N m₂) - a (rnd N (m₁ + 1)) (rnd N m₂)
            - a (rnd N m₁) (rnd N (m₂ + 1)) + a (rnd N (m₁ + 1)) (rnd N (m₂ + 1)))
      = ∑ m₁ ∈ Finset.range M, (a (rnd N m₁) N - a (rnd N (m₁ + 1)) N) :=
        Finset.sum_congr rfl (fun m₁ _ => key m₁)
    _ = a N N - a 0 N := telescope_rnd (fun k => a k N) h
    _ = a N N := by rw [h2 N, sub_zero]

end Work.Analysis.Variation
