import Mathlib
import Submission.Work.Drive.zeroSet_projection_interior_eq_empty

/-!
# Avoiding the zero set of a smooth family over an open region

This file proves `Work.Drive.avoid_zeroSet_open`: for a smooth
`Ψ : ℝ^m × ℝ^d → ℝ^n` with `d < n` which is a *submersion at every zero whose second coordinate
lies in a fixed open set `U`*, and for every centre `c` and radius `ρ > 0`, there is `t` with
`‖t - c‖ < ρ` whose slice `Ψ (t, ·)` has **no** zero in `U`.

The proof is the `σ`-compact-exhaustion + Baire form of the compact statement
`Work.Drive.zeroSet_projection_interior_eq_empty` (which says that for compact `K₁`, `K₂` the set of
parameters admitting a zero in `K₂` has empty interior):

* `Work.Drive.exists_isCompact_exhaustion_open` writes the open `U ⊆ ℝ^d` as the union of the
  *nested* family `K n = closedBall 0 n ∩ {x | ∀ y ∉ U, 1/(n+1) ≤ dist x y}` of compact subsets of
  `U` (compactness: closed inside the compact ball; `K n ⊆ U` because `x ∉ U` applied to `y = x`
  gives `1/(n+1) ≤ 0`; covering: `1/(n+1) ≤ dist x Uᶜ` for `n` large, from openness at `x`);
* for each `n` the set `C n = {t ∈ closedBall 0 n | ∃ z ∈ K n, Ψ (t, z) = 0}` is the first-coordinate
  projection of the compact set `(closedBall 0 n ×ˢ K n) ∩ {Ψ = 0}`, hence compact, hence closed;
* `C n` has empty interior by the compact statement, applied with `K₂ = K n ⊆ U` so that the
  submersion hypothesis is available there;
* the bad set `B = {t | ∃ z ∈ U, Ψ (t, z) = 0}` is covered by `⋃ n, C n` (given `t ∈ B` and a
  witness `z ∈ U`, take `N` with `z ∈ K N` — possible since the exhaustion is nested — and
  `‖t‖ ≤ N`), so Baire (`Work.Sard.wp.interior_eq_empty_iUnion_isClosed`) gives `interior B = ∅`.

Finally, `interior B = ∅` means that no ball is contained in `B`: if `ball c ρ ⊆ B` then
`ball c ρ ⊆ interior B = ∅`, contradicting the nonemptiness of the ball.  This is exactly the
`σ`-compact/Baire globalization of the compact statement needed by the chart-genericity arguments of
the counting lane.
-/

namespace Work.Drive

open Metric Set

/-- **A nested compact exhaustion of an open subset of `ℝ^d`.**

For `U ⊆ ℝ^d` open there is a monotone sequence `K : ℕ → Set ℝ^d` of compact subsets of `U` with
`U = ⋃ n, K n`.

The exhaustion is explicit: `K n = closedBall 0 n ∩ {x | ∀ y ∉ U, 1/(n+1) ≤ dist x y}`.  A point of
`K n` lies in `U` because applying the defining property to `y = x` (for `x ∉ U`) gives
`1/(n+1) ≤ dist x x = 0`; and every `x ∈ U` lies in some `K n` because `U` is open at `x`, so
`{y | dist x y < ε} ⊆ U` for some `ε > 0`, whence `ε ≤ dist x y` for `y ∉ U` and it suffices to take
`1/(n+1) ≤ ε` and `‖x‖ ≤ n`. -/
lemma exists_isCompact_exhaustion_open {d : ℕ} (U : Set (EuclideanSpace ℝ (Fin d)))
    (hUo : IsOpen U) :
    ∃ K : ℕ → Set (EuclideanSpace ℝ (Fin d)),
      (∀ n, IsCompact (K n)) ∧ (∀ n, K n ⊆ U) ∧ Monotone K ∧ (∀ x ∈ U, ∃ n, x ∈ K n) := by
  classical
  set K : ℕ → Set (EuclideanSpace ℝ (Fin d)) := fun n =>
    Metric.closedBall (0 : EuclideanSpace ℝ (Fin d)) (n : ℝ) ∩
      {x | ∀ y, y ∉ U → (1 : ℝ) / (n + 1) ≤ dist x y} with hK
  have hKU : ∀ n, K n ⊆ U := by
    intro n x hx
    by_contra hxU
    have h := hx.2 x hxU
    rw [dist_self] at h
    have hpos : 0 < (1 : ℝ) / (n + 1) := by positivity
    linarith
  have hKc : ∀ n, IsCompact (K n) := by
    intro n
    rw [hK]
    refine IsCompact.of_isClosed_subset (isCompact_closedBall 0 (n : ℝ)) ?_ Set.inter_subset_left
    refine IsClosed.inter isClosed_closedBall ?_
    rw [show {x : EuclideanSpace ℝ (Fin d) | ∀ y, y ∉ U → (1 : ℝ) / (n + 1) ≤ dist x y}
        = ⋂ y ∈ Uᶜ, {x | (1 : ℝ) / (n + 1) ≤ dist x y} from by ext x; simp]
    exact isClosed_biInter fun y _ =>
      isClosed_le continuous_const (continuous_dist.comp (continuous_id.prodMk continuous_const))
  have hKmono : Monotone K := by
    intro n m hnm x hx
    rw [hK] at hx ⊢
    refine ⟨Metric.closedBall_subset_closedBall (by exact_mod_cast hnm) hx.1, fun y hy => ?_⟩
    exact le_trans
      (one_div_le_one_div_of_le (by positivity) (by exact_mod_cast Nat.succ_le_succ hnm))
      (hx.2 y hy)
  have hKcov : ∀ x ∈ U, ∃ n, x ∈ K n := by
    intro x hxU
    obtain ⟨ε, hεpos, hεsub⟩ := Metric.isOpen_iff.mp hUo x hxU
    obtain ⟨n, hn⟩ := exists_nat_ge (max ‖x‖ (1 / ε))
    refine ⟨n, ?_, ?_⟩
    · rw [Metric.mem_closedBall, dist_zero_right]
      exact le_trans (le_max_left _ _) hn
    · intro y hy
      have hxy : ε ≤ dist x y := by
        by_contra hc
        push Not at hc
        exact hy (hεsub (by rw [Metric.mem_ball]; rw [dist_comm]; exact hc))
      have h1ε : (1 : ℝ) / (n + 1) ≤ ε := by
        rw [div_le_iff₀ (by positivity)]
        have h2 : 1 / ε ≤ (n : ℝ) + 1 := by linarith [le_max_right ‖x‖ (1 / ε), hn]
        calc (1 : ℝ) = ε * (1 / ε) := by field_simp
          _ ≤ ε * ((n : ℝ) + 1) := mul_le_mul_of_nonneg_left h2 (le_of_lt hεpos)
      linarith
  exact ⟨K, hKc, hKU, hKmono, hKcov⟩

theorem avoid_zeroSet_open {m d n : ℕ} (hdn : d < n)
    (Ψ : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin n))
    (hΨ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Ψ)
    (U : Set (EuclideanSpace ℝ (Fin d))) (hUo : IsOpen U)
    (hsub : ∀ p : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin d), p.2 ∈ U → Ψ p = 0 →
      Function.Surjective (fderiv ℝ Ψ p))
    (c : EuclideanSpace ℝ (Fin m)) (ρ : ℝ) (hρ : 0 < ρ) :
    ∃ t : EuclideanSpace ℝ (Fin m), ‖t - c‖ < ρ ∧ ∀ z ∈ U, Ψ (t, z) ≠ 0 := by
  classical
  obtain ⟨K, hKc, hKU, hKmono, hKcov⟩ := exists_isCompact_exhaustion_open U hUo
  -- the set of "bad" parameters, i.e. those whose slice has a zero in `U`
  set B : Set (EuclideanSpace ℝ (Fin m)) := {t | ∃ z ∈ U, Ψ (t, z) = 0} with hB
  -- ## the bad set has empty interior
  have hBint : interior B = ∅ := by
    -- the bad set of the `n`-th compact piece
    have hCint : ∀ n : ℕ, interior {t : EuclideanSpace ℝ (Fin m) |
        t ∈ Metric.closedBall 0 (n : ℝ) ∧ ∃ z ∈ K n, Ψ (t, z) = 0} = ∅ := by
      intro n
      exact Work.Drive.zeroSet_projection_interior_eq_empty hdn Ψ hΨ
        (Metric.closedBall 0 (n : ℝ)) (isCompact_closedBall 0 (n : ℝ)) (K n) (hKc n)
        (fun p hp h0 => hsub p (hKU n hp.2) h0)
    have hCclosed : ∀ n : ℕ, IsClosed {t : EuclideanSpace ℝ (Fin m) |
        t ∈ Metric.closedBall 0 (n : ℝ) ∧ ∃ z ∈ K n, Ψ (t, z) = 0} := by
      intro n
      have hZc : IsCompact ((Metric.closedBall (0 : EuclideanSpace ℝ (Fin m)) (n : ℝ) ×ˢ K n)
          ∩ {p : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin d) | Ψ p = 0}) := by
        refine IsCompact.of_isClosed_subset ((isCompact_closedBall 0 (n : ℝ)).prod (hKc n)) ?_ ?_
        · exact ((isCompact_closedBall 0 (n : ℝ)).isClosed.prod (hKc n).isClosed).inter
            (isClosed_eq hΨ.continuous continuous_const)
        · exact Set.inter_subset_left
      have hCe : {t : EuclideanSpace ℝ (Fin m) |
            t ∈ Metric.closedBall 0 (n : ℝ) ∧ ∃ z ∈ K n, Ψ (t, z) = 0}
          = Prod.fst '' ((Metric.closedBall (0 : EuclideanSpace ℝ (Fin m)) (n : ℝ) ×ˢ K n)
              ∩ {p : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin d) | Ψ p = 0}) := by
        ext t
        constructor
        · rintro ⟨ht, z, hz, h0⟩
          exact ⟨(t, z), ⟨⟨ht, hz⟩, h0⟩, rfl⟩
        · rintro ⟨p, hp, rfl⟩
          exact ⟨hp.1.1, p.2, hp.1.2, hp.2⟩
      rw [hCe]
      exact (hZc.image continuous_fst).isClosed
    have hcover : B ⊆ ⋃ n : ℕ, {t : EuclideanSpace ℝ (Fin m) |
        t ∈ Metric.closedBall 0 (n : ℝ) ∧ ∃ z ∈ K n, Ψ (t, z) = 0} := by
      intro t ht
      rw [hB] at ht
      obtain ⟨z, hzU, h0⟩ := ht
      obtain ⟨n, hzn⟩ := hKcov z hzU
      obtain ⟨N, hN⟩ := exists_nat_ge (max (n : ℝ) ‖t‖)
      rw [Set.mem_iUnion]
      refine ⟨N, ?_, ?_⟩
      · rw [Metric.mem_closedBall, dist_zero_right]
        exact le_trans (le_max_right _ _) hN
      · exact ⟨z, hKmono (Nat.cast_le.mp (le_trans (le_max_left _ _) hN)) hzn, h0⟩
    rw [hB]
    exact le_bot_iff.mp ((interior_mono hcover).trans (le_of_eq
      (Work.Sard.wp.interior_eq_empty_iUnion_isClosed hCclosed hCint)))
  -- ## a parameter near `c` avoiding `B`
  by_contra hcon
  push Not at hcon
  have hball : Metric.ball c ρ ⊆ B := by
    intro t ht
    rw [hB]
    exact hcon t (by rw [Metric.mem_ball, dist_eq_norm] at ht; exact ht)
  have hmem : c ∈ interior B := interior_maximal hball Metric.isOpen_ball (Metric.mem_ball_self hρ)
  rw [hBint] at hmem
  exact absurd hmem (Set.notMem_empty c)

end Work.Drive
