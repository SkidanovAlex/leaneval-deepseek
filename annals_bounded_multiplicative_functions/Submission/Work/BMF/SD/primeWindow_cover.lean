import Mathlib
import Submission.Work.BMF.Defs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Covering a prime window by the geometric windows of the scaling step

This is the elementary covering step used when a prime window `[a, b]` is refined into the
`M` geometric windows `[a(1+ρ)^j, min b (a(1+ρ)^{j+1})]` of the MRT/MRTTZ scaling argument
(`rho_window_arith` produces `M = ⌈1/ρ⌉` with `b ≤ a (1+ρ)^M`).

The only content is the geometric fact that, for `a ≤ p` and `p ≤ a r^M` with `M ≥ 1`, the
point `p` lies in one of the windows `[a r^j, a r^{j+1}]`, `j < M`; membership of the primes
then follows from the definition of `primesIn` as `ℕ ∩ [·, ·]` filtered by primality.
-/

namespace Work.BMF.SD

/-- Geometric covering by the windows `[a r^j, a r^{j+1}]`, `j < M`: if `1 ≤ M`, `a ≤ p` and
`p ≤ a r^M`, then for some `j < M` one has `a r^j ≤ p ≤ a r^{j+1}`.

(No hypothesis on the sign of `a` or `r` is needed: the statement is proved by induction on `M`
and is vacuous when the two hypotheses are incompatible.) -/
lemma exists_pow_window (a r : ℝ) :
    ∀ M : ℕ, 1 ≤ M → ∀ p : ℕ, a ≤ (p : ℝ) → (p : ℝ) ≤ a * r ^ M →
      ∃ j, j < M ∧ a * r ^ j ≤ (p : ℝ) ∧ (p : ℝ) ≤ a * r ^ (j + 1) := by
  intro M
  induction M with
  | zero => intro h; omega
  | succ M ih =>
    intro _hM p h0 hMp
    rcases Nat.eq_zero_or_pos M with hM0 | hMpos
    · -- `M = 0`: the single window is `[a, a r]` and `p = a`
      subst hM0
      exact ⟨0, by norm_num, by simpa using h0, by simpa using hMp⟩
    · by_cases h : (p : ℝ) ≤ a * r ^ M
      · -- `p` already lies below the top of the previous window
        obtain ⟨j, hj, h1, h2⟩ := ih hMpos p h0 h
        exact ⟨j, Nat.lt_succ_of_lt hj, h1, h2⟩
      · -- otherwise the top window `[a r^M, a r^{M+1}]` contains `p`
        rw [not_le] at h
        exact ⟨M, Nat.lt_succ_self M, le_of_lt h, hMp⟩

theorem primeWindow_cover (ρ a b : ℝ) (M : ℕ) (hρ : 0 < ρ) (ha : 0 < a) (hM : 1 ≤ M)
    (hbig : b ≤ a * (1 + ρ) ^ M) :
    Work.BMF.primesIn a b ⊆ (Finset.range M).biUnion
      (fun j => Work.BMF.primesIn (a * (1 + ρ) ^ j) (min b (a * (1 + ρ) ^ (j + 1)))) := by
  intro p hp
  -- unpack `p ∈ primesIn a b` as `⌈a⌉₊ ≤ p ≤ ⌊b⌋₊` and `p` prime
  rw [Work.BMF.primesIn, Work.BMF.natIcc, Finset.mem_filter, Finset.mem_Icc] at hp
  obtain ⟨⟨hpa, hpb⟩, hprime⟩ := hp
  have hap : a ≤ (p : ℝ) := le_trans (Nat.le_ceil a) (by exact_mod_cast hpa)
  -- `p ≥ 2` forces `b > 0`, hence `(p : ℝ) ≤ ⌊b⌋₊ ≤ b`
  have hfloor : 0 < ⌊b⌋₊ := lt_of_lt_of_le hprime.pos hpb
  have hb0 : (0 : ℝ) ≤ b := (Nat.pos_of_floor_pos hfloor).le
  have hpb' : (p : ℝ) ≤ b := le_trans (by exact_mod_cast hpb) (Nat.floor_le hb0)
  have hMp : (p : ℝ) ≤ a * (1 + ρ) ^ M := le_trans hpb' hbig
  -- place `p` in one of the geometric windows
  obtain ⟨j, hj, h1, h2⟩ := exists_pow_window a (1 + ρ) M hM p hap hMp
  rw [Finset.mem_biUnion]
  refine ⟨j, Finset.mem_range.mpr hj, ?_⟩
  rw [Work.BMF.primesIn, Work.BMF.natIcc, Finset.mem_filter, Finset.mem_Icc]
  exact ⟨⟨Nat.ceil_le.mpr (by exact_mod_cast h1),
      Nat.le_floor (by exact_mod_cast (le_min hpb' h2))⟩, hprime⟩

end Work.BMF.SD
