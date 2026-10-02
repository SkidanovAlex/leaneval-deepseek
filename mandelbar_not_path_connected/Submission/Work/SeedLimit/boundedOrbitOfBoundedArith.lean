import Mathlib
import Submission.Work.SeedLimit.Defs

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.SeedLimit

open LeanEval.ComplexAnalysis (Tantibar Mandelbar)

/-- **A bounded arithmetic subsequence of the critical orbit bounds the whole orbit.**  If for some
`q ≥ 1` and `r` the subsequence `(T_c^[q n + r] 0)_n` is bounded, then the critical orbit of `T_c` is
bounded, i.e. `c ∈ Mandelbar`.

Correct route: for the tricorn the escape criterion is monotone — once `‖z‖ > max 2 ‖c‖` we have
`‖T_c z‖ > ‖z‖` and the norms strictly increase forever (`norm_sq_sub_le_norm_Tantibar`,
`work.ParamRays.norm_orbit_ge_add`), so an unbounded critical orbit has *every* infinite subsequence
unbounded, in particular `(T_c^[q n + r] 0)_n` for `q ≥ 1`.  Hence a bounded arithmetic subsequence
forces the critical orbit to be bounded (bound it by `max M (max 2 ‖c‖)`).  Do *not* argue with
residue classes of bounded forward iterates. -/
theorem boundedOrbitOfBoundedArith (c : ℂ) {q r : ℕ} (hq : 0 < q)
    (h : ∃ M : ℝ, ∀ n : ℕ, ‖(LeanEval.ComplexAnalysis.Tantibar c)^[q * n + r] 0‖ ≤ M) :
    Work.ParamRays.BoundedOrbit c 0 := by
  obtain ⟨M, hM⟩ := h
  by_contra hnb
  -- An unbounded critical orbit comes above the escape radius `max 2 ‖c‖` at some time `n₀`.
  have hex : ∃ n : ℕ, max 2 ‖c‖ < ‖Work.ParamRays.orbit c 0 n‖ := by
    by_contra hcon
    simp only [not_exists, not_lt] at hcon
    exact hnb ⟨max 2 ‖c‖, hcon⟩
  obtain ⟨n₀, hn₀⟩ := hex
  set z : ℂ := Work.ParamRays.orbit c 0 n₀ with hz
  have hzlt : max 2 ‖c‖ < ‖z‖ := by rw [hz]; exact hn₀
  have hz2 : 2 < ‖z‖ := lt_of_le_of_lt (le_max_left 2 ‖c‖) hzlt
  -- Once above the escape radius, the norm grows at least linearly, with slope `s > 0`.
  set s : ℝ := ‖z‖ * (‖z‖ - 2) with hs
  have hspos : 0 < s := by rw [hs]; nlinarith
  have hgrowth : ∀ m : ℕ, ‖z‖ + (m : ℝ) * s ≤ ‖Work.ParamRays.orbit c z m‖ := by
    intro m
    have h1 := Work.ParamRays.norm_orbit_ge_add c z hzlt m
    rwa [← hs] at h1
  -- Choose an index `k ≥ n₀` for which the linear lower bound exceeds `M`.
  set k : ℕ := n₀ + (Nat.ceil (max 0 ((M - ‖z‖) / s)) + 1) with hk
  have hkn : n₀ ≤ k := by simp [hk]
  have hqk : k ≤ q * k := by
    have h' := Nat.mul_le_mul_right k hq
    simpa using h'
  have hkr : k ≤ q * k + r := le_trans hqk (Nat.le_add_right _ _)
  have hmn : n₀ ≤ q * k + r := le_trans hkn hkr
  set m : ℕ := q * k + r - n₀ with hm
  have hnm : n₀ + m = q * k + r := by rw [hm]; omega
  have hmk : (k : ℝ) - n₀ ≤ (m : ℝ) := by
    have h1 : k - n₀ ≤ m := by
      rw [hm]
      exact Nat.sub_le_sub_right hkr n₀
    have h2 : ((k - n₀ : ℕ) : ℝ) = (k : ℝ) - n₀ := Nat.cast_sub hkn
    rw [← h2]
    exact_mod_cast h1
  have hceil : (M - ‖z‖) / s < ((Nat.ceil (max 0 ((M - ‖z‖) / s)) : ℕ) : ℝ) + 1 := by
    have h1 : (M - ‖z‖) / s ≤ max 0 ((M - ‖z‖) / s) := le_max_right _ _
    have h2 := Nat.le_ceil (max 0 ((M - ‖z‖) / s))
    linarith
  have hkcast : (k : ℝ) - n₀ = ((Nat.ceil (max 0 ((M - ‖z‖) / s)) : ℕ) : ℝ) + 1 := by
    rw [hk]; push_cast; ring
  have hMs : M - ‖z‖ < (m : ℝ) * s := by
    have h1 : ((k : ℝ) - n₀) * s ≤ (m : ℝ) * s :=
      mul_le_mul_of_nonneg_right hmk (le_of_lt hspos)
    have h2 : (M - ‖z‖) < ((k : ℝ) - n₀) * s := by
      rw [hkcast]
      have h4 : ((M - ‖z‖) / s) * s <
          (((Nat.ceil (max 0 ((M - ‖z‖) / s)) : ℕ) : ℝ) + 1) * s :=
        mul_lt_mul_of_pos_right hceil hspos
      rwa [div_mul_cancel₀ _ (ne_of_gt hspos)] at h4
    linarith
  -- The bounded subsequence at index `q * k + r = n₀ + m` contradicts that lower bound.
  have hbound : ‖Work.ParamRays.orbit c z m‖ ≤ M := by
    have h1 := hM k
    rw [← hnm] at h1
    have h2 : Work.ParamRays.orbit c z m = Work.ParamRays.orbit c 0 (n₀ + m) := by
      rw [hz]
      exact (Work.ParamRays.orbit_add c 0 n₀ m).symm
    rw [h2]
    exact h1
  have hgm := hgrowth m
  linarith

end Work.SeedLimit
