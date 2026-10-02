import Mathlib

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.ParamRays

/-- If the sequence `ζ ^ (2 ^ k)` converges to `1`, then `ζ` is a root of unity of
2-power order: some `ζ ^ (2 ^ N) = 1`.

The proof is the "doubling map" argument.  Writing `d k = ‖ζ ^ (2 ^ k) - 1‖`, we have
`d k → 0` and the recurrence `d (k+1) = d k * ‖ζ ^ (2 ^ k) + 1‖`.  Since
`‖ζ ^ (2 ^ k) + 1‖ ≥ 2 - d k`, whenever `d k ≤ 1/2` we get `d (k+1) ≥ (3/2) * d k`.
So from some index `K` on, `d` grows at least geometrically; combined with `d k → 0`
this forces `d K = 0`, i.e. `ζ ^ (2 ^ K) = 1`.  Note no separate argument that
`‖ζ‖ = 1` is needed. -/
theorem exists_pow_two_pow_eq_one {ζ : ℂ}
    (h : Filter.Tendsto (fun k : ℕ => ζ ^ (2 ^ k)) Filter.atTop (nhds 1)) :
    ∃ N : ℕ, ζ ^ (2 ^ N) = 1 := by
  let a : ℕ → ℂ := fun k => ζ ^ (2 ^ k)
  -- The doubling relation on the sequence.
  have ha_succ : ∀ k, a (k+1) = (a k)^2 := by
    intro k
    dsimp only [a]
    rw [show 2 ^ (k+1) = 2^k * 2 from by rw [pow_succ], pow_mul]
  have hlim : Filter.Tendsto a Filter.atTop (nhds 1) := h
  -- The distance to `1` tends to `0`.
  have hd : Filter.Tendsto (fun k => ‖a k - 1‖) Filter.atTop (nhds 0) := by
    have h1 : Filter.Tendsto (fun k => a k - 1) Filter.atTop (nhds ((1:ℂ) - 1)) :=
      hlim.sub_const (1:ℂ)
    have h2 := h1.norm
    simpa using h2
  have hev : ∀ᶠ k in Filter.atTop, ‖a k - 1‖ < (1:ℝ)/2 :=
    hd.eventually (Iio_mem_nhds (by norm_num : (0:ℝ) < 1/2))
  obtain ⟨K, hK⟩ := Filter.eventually_atTop.1 hev
  -- The recurrence `d (k+1) = d k * ‖a k + 1‖`.
  have hrec : ∀ k, ‖a (k+1) - 1‖ = ‖a k - 1‖ * ‖a k + 1‖ := by
    intro k
    rw [ha_succ k, show (a k)^2 - 1 = (a k - 1) * (a k + 1) from by ring, norm_mul]
  -- The reverse triangle inequality `‖a k + 1‖ ≥ 2 - d k`.
  have hlow : ∀ k, (2:ℝ) - ‖a k - 1‖ ≤ ‖a k + 1‖ := by
    intro k
    have hh := norm_sub_norm_le (2:ℂ) (1 - a k)
    rw [show ‖(2:ℂ)‖ = 2 from by norm_num,
        show ‖1 - a k‖ = ‖a k - 1‖ from by rw [norm_sub_rev],
        show (2:ℂ) - (1 - a k) = a k + 1 from by ring] at hh
    exact hh
  -- Wherever `d k ≤ 1/2`, the distance grows by a factor at least `3/2`.
  have hgrowth : ∀ k, ‖a k - 1‖ ≤ (1:ℝ)/2 → (3/2) * ‖a k - 1‖ ≤ ‖a (k+1) - 1‖ := by
    intro k hk
    have h1 : (3:ℝ)/2 ≤ ‖a k + 1‖ := by linarith [hlow k, hk]
    have h2 : 0 ≤ ‖a k - 1‖ := norm_nonneg _
    calc (3/2) * ‖a k - 1‖ = ‖a k - 1‖ * (3/2) := by ring
      _ ≤ ‖a k - 1‖ * ‖a k + 1‖ := mul_le_mul_of_nonneg_left h1 h2
      _ = ‖a (k+1) - 1‖ := (hrec k).symm
  -- Hence the geometric lower bound beyond `K`.
  have hmain : ∀ m, (3/2)^m * ‖a K - 1‖ ≤ ‖a (K+m) - 1‖ := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
        have hk : ‖a (K+m) - 1‖ ≤ (1:ℝ)/2 := le_of_lt (hK (K+m) (Nat.le_add_right K m))
        calc (3/2)^(m+1) * ‖a K - 1‖
            = (3/2) * ((3/2)^m * ‖a K - 1‖) := by rw [pow_succ]; ring
          _ ≤ (3/2) * ‖a (K+m) - 1‖ := mul_le_mul_of_nonneg_left ih (by norm_num)
          _ ≤ ‖a (K + (m+1)) - 1‖ := hgrowth (K+m) hk
  -- Since `d` stays below `1/2` beyond `K`, this forces `d K = 0`.
  have hzero : ‖a K - 1‖ = 0 := by
    by_contra hne
    have hpos : 0 < ‖a K - 1‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hne)
    obtain ⟨m, hm⟩ := pow_unbounded_of_one_lt (1 / (2 * ‖a K - 1‖)) (by norm_num : (1:ℝ) < 3/2)
    have hlt : ‖a (K+m) - 1‖ < (1:ℝ)/2 := hK (K+m) (Nat.le_add_right K m)
    have hmul : (1 / (2 * ‖a K - 1‖)) * ‖a K - 1‖ < (3/2)^m * ‖a K - 1‖ :=
      mul_lt_mul_of_pos_right hm hpos
    have hl : (1 / (2 * ‖a K - 1‖)) * ‖a K - 1‖ = (1:ℝ)/2 := by
      have h2 : (2:ℝ) * ‖a K - 1‖ ≠ 0 := ne_of_gt (by linarith)
      field_simp
    rw [hl] at hmul
    have := hmain m
    linarith
  refine ⟨K, ?_⟩
  have h1 : a K = 1 := sub_eq_zero.mp (norm_eq_zero.mp hzero)
  exact h1

end Work.ParamRays
