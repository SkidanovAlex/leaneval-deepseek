import Mathlib
import Submission.Work.Diff.MP.Basic

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Diff.MP

open Submission.Diff.Alg

/-- **First-order optimality (supporting hyperplane) for the Frobenius distance.**
If `v ∈ K` is a nearest point of the convex set `K` to `P`, then the vector `v` is
"supported" at the obtuse angle: for every `S ∈ K` the inner product
`⟪P - v, S - v⟫` is `≤ 0`.

This is the elementary convexity fact behind the maximum-principle argument: the
segment `v + t (S - v)` stays in `K`, so `t ↦ frobDist P (v + t (S - v))²` has a
minimum at `t = 0`; expanding the square and letting `t → 0⁺` gives the claim. -/
theorem frobDot_nonpos_of_frobDist_min (n : ℕ) (K : Set (Submission.Diff.Alg.Curv4 n))
    (hKcv : Convex ℝ K) (P v : Submission.Diff.Alg.Curv4 n) (hv : v ∈ K)
    (hmin : ∀ S ∈ K, Work.Diff.MP.frobDist P v ≤ Work.Diff.MP.frobDist P S) :
    ∀ S ∈ K, Work.Diff.MP.frobDot (P - v) (S - v) ≤ 0 := by
  intro S hS
  by_cases hSv : S = v
  · subst hSv
    simp [frobDot]
  · -- bilinearity helper: `frobDot` is additive in its second argument
    have hsr : ∀ (R S T : Curv4 n),
        frobDot R (S - T) = frobDot R S - frobDot R T := by
      intro R S T
      rw [sub_eq_add_neg, frobDot_add_right, frobDot_neg_right]; ring
    -- exact expansion of the squared distance along the segment `v + t (S - v)`
    have hexp : ∀ t : ℝ, frobDist P (v + t • (S - v)) ^ 2
        = frobDist P v ^ 2 + t * (-(2 * frobDot (P - v) (S - v))
            + t * frobDot (S - v) (S - v)) := by
      intro t
      have hsub : P - (v + t • (S - v)) = (P - v) - t • (S - v) := by abel
      rw [frobDist, frobDist, hsub, frobNorm_sq, frobNorm_sq]
      rw [frobDot_sub_left, hsr (P - v) (P - v) (t • (S - v)),
          hsr (t • (S - v)) (P - v) (t • (S - v)),
          frobDot_smul_left, frobDot_smul_right, frobDot_smul_left, frobDot_smul_right,
          frobDot_comm (S - v) (P - v)]
      ring
    -- the minimum condition, divided by `t`
    have hineq : ∀ t ∈ Set.Ioc (0:ℝ) 1,
        2 * frobDot (P - v) (S - v) ≤ t * frobDot (S - v) (S - v) := by
      intro t ht
      have hmem : (1 - t) • v + t • S ∈ K :=
        hKcv hv hS (sub_nonneg.mpr ht.2) (le_of_lt ht.1) (by ring)
      have hmin' := hmin ((1 - t) • v + t • S) hmem
      rw [show (1 - t) • v + t • S = v + t • (S - v) from by module] at hmin'
      have hsq : frobDist P v ^ 2 ≤ frobDist P (v + t • (S - v)) ^ 2 := by
        nlinarith [hmin', frobDist_nonneg P v, frobDist_nonneg P (v + t • (S - v))]
      rw [hexp t] at hsq
      nlinarith [hsq, ht.1]
    -- let `t → 0⁺`
    have hmain : 2 * frobDot (P - v) (S - v) ≤ 0 := by
      apply le_of_forall_pos_le_add
      intro ε hε
      by_cases hB : frobDot (S - v) (S - v) = 0
      · have h1 := hineq 1 (by constructor <;> norm_num)
        rw [hB, mul_zero] at h1; linarith
      · have hBpos : 0 < frobDot (S - v) (S - v) :=
          lt_of_le_of_ne (frobDot_self_nonneg (S - v)) (Ne.symm hB)
        set t := min 1 (ε / frobDot (S - v) (S - v)) with ht
        have htpos : 0 < t := lt_min one_pos (div_pos hε hBpos)
        have htle1 : t ≤ 1 := min_le_left _ _
        have h1 := hineq t ⟨htpos, htle1⟩
        have h2 : t ≤ ε / frobDot (S - v) (S - v) := min_le_right _ _
        have h3 : t * frobDot (S - v) (S - v) ≤ ε := by
          calc t * frobDot (S - v) (S - v)
              ≤ (ε / frobDot (S - v) (S - v)) * frobDot (S - v) (S - v) := by
                apply mul_le_mul_of_nonneg_right h2 (le_of_lt hBpos)
            _ = ε := by field_simp
        linarith
    linarith

end Work.Diff.MP
