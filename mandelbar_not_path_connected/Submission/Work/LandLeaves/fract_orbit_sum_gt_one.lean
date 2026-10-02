import Mathlib

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.LandLeaves

/-- For `d > 1`, any positive orbit `ℓ` of the expanding folding map
`x ↦ Int.fract (d * x)` (i.e. `ℓ (n+1) = Int.fract (d * ℓ n)` with all `ℓ n > 0`)
has partial sums of `ℓ` that eventually exceed `1`.

The proof is by contradiction: if all partial sums were `≤ 1`, then `∑ ℓ n` would
converge, hence `ℓ n → 0`. But on `(0, 1/d)`, the map acts as multiplication by `d`,
so any orbit value below `1/d` grows geometrically until it reaches `[1/d, 1)`;
consequently `ℓ n ≥ 1/d` for arbitrarily large `n`, contradicting `ℓ n → 0`. -/
theorem fract_orbit_sum_gt_one {d : ℝ} (hd : 1 < d) {ℓ : ℕ → ℝ}
    (hstep : ∀ n, ℓ (n + 1) = Int.fract (d * ℓ n)) (hpos : ∀ n, 0 < ℓ n) :
    ∃ N : ℕ, 1 < ∑ n ∈ Finset.range N, ℓ n := by
  by_contra hcon
  push Not at hcon
  -- hcon : ∀ N, ∑ n ∈ range N, ℓ n ≤ 1
  set c : ℝ := 1 / d with hc_def
  have hdpos : 0 < d := lt_trans one_pos hd
  have hc_pos : 0 < c := by rw [hc_def]; exact div_pos one_pos hdpos
  have hc_lt_one : c < 1 := by rw [hc_def]; exact (div_lt_one hdpos).mpr hd
  have hdc : d * c = 1 := by rw [hc_def, mul_one_div, div_self (ne_of_gt hdpos)]
  have hnonneg : ∀ n, 0 ≤ ℓ n := fun n => le_of_lt (hpos n)
  -- bounded partial sums of a nonnegative series force summability
  have hsumm : Summable ℓ := summable_of_sum_range_le hnonneg hcon
  have hlim : Filter.Tendsto ℓ Filter.atTop (nhds 0) := hsumm.tendsto_atTop_zero
  -- hence eventually ℓ n < c
  have hev : ∀ᶠ n in Filter.atTop, ℓ n < c :=
    Filter.Tendsto.eventually_lt_const hc_pos hlim
  obtain ⟨N0, hN0⟩ := Filter.eventually_atTop.1 hev
  -- Key claim: for every `N` there is `m ≥ N` with `c ≤ ℓ m`.
  have key : ∀ N, ∃ m ≥ N, c ≤ ℓ m := by
    intro N
    by_cases hN : c ≤ ℓ N
    · exact ⟨N, le_rfl, hN⟩
    · push Not at hN
      have hℓNpos : 0 < ℓ N := hpos N
      -- there exists `k` with `c ≤ d^k * ℓ N`
      have hne : ∃ k : ℕ, c ≤ d ^ k * ℓ N := by
        have h1 : ∀ᶠ k in Filter.atTop, c / ℓ N ≤ d ^ k :=
          (tendsto_pow_atTop_atTop_of_one_lt hd).eventually_ge_atTop (c / ℓ N)
        obtain ⟨k0, hk0⟩ := Filter.eventually_atTop.1 h1
        exact ⟨k0, by
          have := hk0 k0 le_rfl
          rwa [div_le_iff₀ hℓNpos] at this⟩
      let k := Nat.find hne
      have hspec : c ≤ d ^ k * ℓ N := Nat.find_spec hne
      have hkpos : 0 < k := by
        rcases Nat.eq_zero_or_pos k with h | h
        · exfalso
          rw [h] at hspec
          simp only [pow_zero, one_mul] at hspec
          linarith
        · exact h
      have hklt : k - 1 < k := Nat.sub_one_lt_of_lt hkpos
      -- minimality gives `d^(k-1) * ℓ N < c`
      have hprev : d ^ (k - 1) * ℓ N < c := not_le.1 (Nat.find_min hne hklt)
      -- consequently `d^k * ℓ N < 1`
      have htop : d ^ k * ℓ N < 1 := by
        have h2 : d * (d ^ (k - 1) * ℓ N) < d * c :=
          mul_lt_mul_of_pos_left hprev hdpos
        rw [hdc] at h2
        have heq : d * (d ^ (k - 1) * ℓ N) = d ^ k * ℓ N := by
          rw [← mul_assoc, ← pow_succ', Nat.sub_add_cancel (Nat.one_le_of_lt hkpos)]
        rwa [heq] at h2
      -- along the first `k` steps the orbit is pure geometric growth
      have hP : ∀ j, j ≤ k → ℓ (N + j) = d ^ j * ℓ N := by
        intro j
        induction j with
        | zero => intro _; simp
        | succ j ih =>
          intro hj
          have hjle : j ≤ k := Nat.le_of_succ_le hj
          have ihj : ℓ (N + j) = d ^ j * ℓ N := ih hjle
          have hlt1 : d ^ (j + 1) * ℓ N < 1 := by
            have hle : d ^ (j + 1) ≤ d ^ k := pow_le_pow_right₀ (le_of_lt hd) hj
            calc d ^ (j + 1) * ℓ N ≤ d ^ k * ℓ N :=
                  mul_le_mul_of_nonneg_right hle (le_of_lt hℓNpos)
              _ < 1 := htop
          have hge0 : 0 ≤ d ^ (j + 1) * ℓ N := by positivity
          have hstepj : ℓ (N + (j + 1)) = Int.fract (d ^ (j + 1) * ℓ N) := by
            rw [show N + (j + 1) = (N + j) + 1 by omega, hstep (N + j), ihj]
            congr 1
            rw [pow_succ']
            ring
          rw [hstepj, Int.fract_eq_self.mpr ⟨hge0, hlt1⟩]
      have hkval : c ≤ ℓ (N + k) := by
        rw [hP k le_rfl]; exact hspec
      exact ⟨N + k, Nat.le_add_right N k, hkval⟩
  obtain ⟨m, hm1, hm2⟩ := key N0
  exact absurd (hN0 m hm1) (not_lt.2 hm2)

end Work.LandLeaves
