import Mathlib
import Submission.Commons.Combinatorics.exists_bad_exponents_small_fn_pos

namespace Commons.Combinatorics

-- PROOF STRATEGY (uniform measure on the block-compositions):
-- Let `Comp d := {c : Fin N → Fin (d+1) // ∑ k, (c k : ℕ) = d}` and
-- `S := Finset.univ.pi (fun h : Fin m => Comp (d h))` (block-compositions of `d`, so
-- `S.card = ∏ h, (d h + N - 1).choose (N - 1)`, cf. `Combinatorics/card_weakComposition`).
-- Define `bad := S.filter (fun j => ∃ k, (m:ℝ)/N + m*W < ∑ h, (j h k : ℝ)/(d h : ℝ))`.
-- Facts (symmetry of the permutation action on `Fin N` and the product structure of `S`):
-- (i)  `∑ j ∈ S, j h k = S.card * d h / N`  (cf. `Combinatorics/sum_weakComposition_apply`);
-- (ii) `∑ j ∈ S, (j h k) * (j h' k) = S.card * d h * d h' / N^2` for `h ≠ h'`;
-- (iii) `j h k ≤ d h` on `S`, hence `∑ j ∈ S, (j h k)^2 ≤ d h * ∑ j ∈ S, j h k`.
-- Expanding, (i)–(iii) give `∑ j ∈ S, (S_k j - m/N)^2 ≤ S.card * m * (N-1) / N^2`, where
-- `S_k j := ∑ h, (j h k : ℝ)/(d h : ℝ)`; Chebyshev then gives, for each `k`,
-- `#{j ∈ S : m/N + m*W < S_k j} * (m*W)^2 ≤ S.card * m * (N-1) / N^2`,
-- so `bad.card ≤ N * S.card * (N-1)/(N^2 * m * W^2) ≤ S.card / (m*W^2) ≤ S.card / (2*r)`.
theorem exists_bad_exponents_small_fn {m N : ℕ} (hN : 2 ≤ N) (d : Fin m → ℕ)
    (hd : ∀ h : Fin m, 1 ≤ d h)
    (W : ℝ) (hW : 0 < W) (r : ℕ) (hWm : 2 * r ≤ (m : ℝ) * W ^ 2) :
    ∃ bad : Finset (Fin m → Fin N → ℕ),
      (∀ j ∈ bad, ∀ h : Fin m, ∑ k : Fin N, j h k = d h) ∧
      (∀ j, (∀ h : Fin m, ∑ k : Fin N, j h k = d h) → j ∉ bad →
        ∀ k : Fin N,
          |(∑ h : Fin m, (j h k : ℝ) / (d h : ℝ)) - (m : ℝ) / (N : ℝ)|
            ≤ (m : ℝ) * W) ∧
      2 * r * bad.card < ∏ h : Fin m, (d h + N - 1).choose (N - 1) := by
  -- This is exactly the statement already proved (with the same hypotheses,
  -- in particular `1 ≤ d h`) by a teammate as
  -- `Commons.Combinatorics.exists_bad_exponents_small_fn_pos`;
  -- the argument is the uniform-measure/Chebyshev computation described above.
  exact exists_bad_exponents_small_fn_pos hN d hd W hW r hWm

end Commons.Combinatorics
