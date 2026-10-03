import Mathlib
import Submission.Work.KMTContract.Defs

open scoped NNReal

namespace Work.KMTPlan.A6

/-!
# The lacunary levels of a `Λ`-lacunary sequence are uniformly bounded

For a `Λ`-lacunary sequence `a : ℕ → ℝ≥0` with `Λ > 1` and `a n ≥ 1`, the index `n` is a strictly
increasing function of `a n` which grows at least geometrically with ratio `Λ`.  Hence at most
`log 8 / log Λ + 1` indices can have `⌊a n⌋_ℕ` in a fixed dyadic window `[2^{m}, 2^{m+1})`.  Since
`Work.Analysis.EndVar.logN N = ⌊log₂ (max N 2)⌋` is exactly the dyadic level of `N`, this bounds
the cardinality of any set of indices on which the logarithmic level is constant — uniformly in
that level, and in particular for *every* finite set `t` of indices.

This is the lemma `lacunaryLevel` of area A6 (`ROUTE_LEAD.md`): the number of scales of a lacunary
family that can fall into a single `Log`-level is bounded by a constant depending only on the
lacunarity `Λ`.

## Structure of the proof

* `lacunary_growth_pow` : the iterated growth `Λ ^ k * a p ≤ a (p + k)`.
* `lacunaryLevel_maxFloor_le` / `lacunaryLevel_lt_maxFloor_add_one` : the two elementary estimates
  relating `a n` to `max ⌊a n⌋ 2`, giving the *ratio* bound `a n₂ < 8 · a n₁` for two indices `n₁ ≤ n₂`
  of the same level.
* the main argument: two indices of equal level differ by at most `⌊log 8 / log Λ⌋`, so the level
  set has diameter at most that, hence the filter is contained in `Icc (min) (max)` and has at most
  `⌊log 8 / log Λ⌋ + 1` elements.
-/

/-- Growth of a lacunary sequence: `Λ`-lacunarity together with `a n ≥ 1` gives the pointwise
multiplicative bound `Λ * a n ≤ a (n + 1)`. -/
theorem lacunary_growth_step (Λ : ℝ≥0) (a : ℕ → ℝ≥0)
    (ha : PointwiseErgodicTheorems.Lacunary Λ a) (ha1 : ∀ n, 1 ≤ a n) :
    ∀ n, Λ * a n ≤ a (n + 1) := by
  intro n
  have hpos : (0 : NNReal) < a n := lt_of_lt_of_le zero_lt_one (ha1 n)
  have h : Λ * a n ≤ a (n + 1) := le_of_lt ((lt_div_iff₀ hpos).mp (ha n))
  exact h

/-- The iterated form of the growth: `Λ ^ k * a p ≤ a (p + k)` in `ℝ`. -/
theorem lacunary_growth_pow (Λ : ℝ≥0) (a : ℕ → ℝ≥0)
    (hgr : ∀ n, Λ * a n ≤ a (n + 1)) :
    ∀ p k, (Λ : ℝ) ^ k * (a p : ℝ) ≤ (a (p + k) : ℝ) := by
  intro p k
  induction k with
  | zero => simp
  | succ j ih =>
    have hstep : (Λ : ℝ) * (a (p + j) : ℝ) ≤ (a (p + j + 1) : ℝ) := by
      have h := hgr (p + j)
      have h' : ((Λ * a (p + j) : ℝ≥0) : ℝ) ≤ (a (p + j + 1) : ℝ) := by exact_mod_cast h
      simpa using h'
    calc (Λ : ℝ) ^ (j + 1) * (a p : ℝ)
        = (Λ : ℝ) * ((Λ : ℝ) ^ j * (a p : ℝ)) := by ring
      _ ≤ (Λ : ℝ) * (a (p + j) : ℝ) := mul_le_mul_of_nonneg_left ih (by positivity)
      _ ≤ (a (p + j + 1) : ℝ) := hstep

/-- `max ⌊a⌋ 2 ≤ 2 a` for `a : ℝ≥0` with `a ≥ 1`: the "windowed" integer `max ⌊a⌋ 2` controls `a`
from above up to the factor `2`. -/
theorem lacunaryLevel_maxFloor_le {x : ℝ≥0} (hx : 1 ≤ x) :
    ((max (Nat.floor x) 2 : ℕ) : ℝ) ≤ 2 * (x : ℝ) := by
  have hf : ((Nat.floor x : ℕ) : ℝ) ≤ (x : ℝ) := by
    have h : ((Nat.floor x : ℕ) : ℝ≥0) ≤ x := Nat.floor_le (by positivity : (0 : ℝ≥0) ≤ x)
    exact_mod_cast h
  have hx' : (1 : ℝ) ≤ (x : ℝ) := by exact_mod_cast hx
  have : max ((Nat.floor x : ℕ) : ℝ) 2 ≤ 2 * (x : ℝ) := by
    apply max_le
    · linarith
    · linarith
  simpa using this

/-- `a < max ⌊a⌋ 2 + 1` for `a : ℝ≥0`. -/
theorem lacunaryLevel_lt_maxFloor_add_one (x : ℝ≥0) :
    (x : ℝ) < ((max (Nat.floor x) 2 : ℕ) : ℝ) + 1 := by
  have h : x < ((Nat.floor x : ℕ) : ℝ≥0) + 1 := Nat.lt_floor_add_one x
  have h3 : (x : ℝ) < ((Nat.floor x : ℕ) : ℝ) + 1 := by exact_mod_cast h
  have h4 : ((Nat.floor x : ℕ) : ℝ) + 1 ≤ ((max (Nat.floor x) 2 : ℕ) : ℝ) + 1 := by
    have : (Nat.floor x : ℕ) ≤ max (Nat.floor x) 2 := le_max_left _ _
    exact_mod_cast Nat.add_le_add_right this 1
  linarith

/-- **The lacunary levels are uniformly bounded.**  There is a function `M` of the lacunarity `Λ`
such that for every `Λ`-lacunary sequence `a` with `a n ≥ 1`, every finite set `t` of indices and
every level `m`, at most `M Λ` elements of `t` have `logN ⌊a n⌋ = m`.

(We may take `M Λ = ⌊log 8 / log Λ⌋ + 1` for `Λ > 1`; the bound is only ever used under the
hypothesis `1 < Λ`.) -/
theorem lacunaryLevel :
    ∃ M : NNReal → ℕ, ∀ (a : ℕ → NNReal) (Λ : NNReal), 1 < Λ → PointwiseErgodicTheorems.Lacunary Λ a →
      (∀ n, 1 ≤ a n) → ∀ (m : ℤ) (t : Finset ℕ),
      (t.filter (fun n => Work.Analysis.EndVar.logN (Nat.floor (a n)) = m)).card ≤ M Λ := by
  refine ⟨fun Λ => Nat.floor (Real.log 8 / Real.log (Λ : ℝ)) + 1, ?_⟩
  intro a Λ hΛ ha ha1 m t
  have hΛpos : (0 : ℝ) < (Λ : ℝ) := by
    have : (1 : ℝ) < (Λ : ℝ) := by exact_mod_cast hΛ
    linarith
  have hgr := lacunary_growth_step Λ a ha ha1
  have hpowmul := lacunary_growth_pow Λ a hgr
  have hlogΛ : 0 < Real.log (Λ : ℝ) := Real.log_pos (by exact_mod_cast hΛ)
  -- Two indices of the same level are multiplicatively close: `a n₂ < 8 · a n₁` for `n₁ ≤ n₂`.
  have key : ∀ n1 n2 : ℕ, n1 ≤ n2 →
      Work.Analysis.EndVar.logN (Nat.floor (a n1)) = m →
      Work.Analysis.EndVar.logN (Nat.floor (a n2)) = m →
      (n2 - n1) ≤ Nat.floor (Real.log 8 / Real.log (Λ : ℝ)) := by
    intro n1 n2 hle h1 h2
    rw [Work.Analysis.EndVar.logN] at h1 h2
    have hk1 : Nat.log 2 (max (Nat.floor (a n1)) 2) = m.toNat := by
      rw [← h1]; exact Int.toNat_natCast _
    have hk2 : Nat.log 2 (max (Nat.floor (a n2)) 2) = m.toNat := by
      rw [← h2]; exact Int.toNat_natCast _
    -- upper bound: `a n₂ < 2 · (max ⌊a n₂⌋ 2) ≤ 2 · 2 ^ (m.toNat + 1) = 4 · 2 ^ m.toNat`
    have hA : max (Nat.floor (a n2)) 2 < 2 ^ (m.toNat + 1) := by
      have h := Nat.lt_pow_succ_log_self (by norm_num : 1 < 2) (max (Nat.floor (a n2)) 2)
      rwa [hk2] at h
    have hupper : (a n2 : ℝ) < 4 * (2 : ℝ) ^ (m.toNat) := by
      have hM2 : (a n2 : ℝ) < ((max (Nat.floor (a n2)) 2 : ℕ) : ℝ) + 1 :=
        lacunaryLevel_lt_maxFloor_add_one _
      have hM2b : ((max (Nat.floor (a n2)) 2 : ℕ) : ℝ) + 1
          ≤ 2 * ((max (Nat.floor (a n2)) 2 : ℕ) : ℝ) := by
        have h2ge : (2 : ℝ) ≤ ((max (Nat.floor (a n2)) 2 : ℕ) : ℝ) := by
          have : (2 : ℕ) ≤ max (Nat.floor (a n2)) 2 := le_max_right _ _
          exact_mod_cast this
        linarith
      have hA' : ((max (Nat.floor (a n2)) 2 : ℕ) : ℝ) < (2 : ℝ) ^ (m.toNat + 1) := by
        exact_mod_cast hA
      have hExp : (2 : ℝ) ^ (m.toNat + 1) = 2 * (2 : ℝ) ^ (m.toNat) := pow_succ' 2 (m.toNat)
      linarith
    -- lower bound: `2 ^ m.toNat ≤ max ⌊a n₁⌋ 2 ≤ 2 · a n₁`
    have hlower : (2 : ℝ) ^ (m.toNat) ≤ 2 * (a n1 : ℝ) := by
      have hB : 2 ^ m.toNat ≤ max (Nat.floor (a n1)) 2 := by
        have hmax : max (Nat.floor (a n1)) 2 ≠ 0 := by omega
        have h := Nat.pow_log_le_self 2 hmax
        rwa [hk1] at h
      have hB' : (2 : ℝ) ^ (m.toNat) ≤ ((max (Nat.floor (a n1)) 2 : ℕ) : ℝ) := by
        exact_mod_cast hB
      have hM1 : ((max (Nat.floor (a n1)) 2 : ℕ) : ℝ) ≤ 2 * (a n1 : ℝ) :=
        lacunaryLevel_maxFloor_le (ha1 n1)
      linarith
    have hratio : (a n2 : ℝ) < 8 * (a n1 : ℝ) := by linarith
    -- growth: `Λ ^ (n₂ - n₁) * a n₁ ≤ a n₂`
    have hgrowth : (Λ : ℝ) ^ (n2 - n1) * (a n1 : ℝ) ≤ (a n2 : ℝ) := by
      have h := hpowmul n1 (n2 - n1)
      rwa [Nat.add_sub_of_le hle] at h
    have hpos1 : (0 : ℝ) < (a n1 : ℝ) := by
      have := ha1 n1
      exact_mod_cast (lt_of_lt_of_le zero_lt_one this)
    have hlt8 : (Λ : ℝ) ^ (n2 - n1) < 8 := by
      have h1 : (Λ : ℝ) ^ (n2 - n1) * (a n1 : ℝ) < 8 * (a n1 : ℝ) :=
        lt_of_le_of_lt hgrowth hratio
      exact lt_of_mul_lt_mul_right h1 hpos1.le
    have hlog : ((n2 - n1 : ℕ) : ℝ) * Real.log (Λ : ℝ) < Real.log 8 := by
      have h := Real.log_lt_log (pow_pos hΛpos (n2 - n1)) hlt8
      rwa [Real.log_pow] at h
    have hfin : ((n2 - n1 : ℕ) : ℝ) < Real.log 8 / Real.log (Λ : ℝ) := by
      rw [lt_div_iff₀ hlogΛ]
      simpa [mul_comm] using hlog
    exact Nat.le_floor hfin.le
  -- The level set has diameter at most `⌊log 8 / log Λ⌋`; it is contained in `Icc min max`.
  let s : Finset ℕ := t.filter (fun n => Work.Analysis.EndVar.logN (Nat.floor (a n)) = m)
  have hsle : s.card ≤ Nat.floor (Real.log 8 / Real.log (Λ : ℝ)) + 1 := by
    rcases Finset.eq_empty_or_nonempty s with hem | hne
    · rw [hem]; simp
    · have hmin : s.min' hne ∈ s := Finset.min'_mem s hne
      have hmax : s.max' hne ∈ s := Finset.max'_mem s hne
      have hcard : s.card ≤ s.max' hne + 1 - s.min' hne := by
        calc s.card ≤ (Finset.Icc (s.min' hne) (s.max' hne)).card := by
              apply Finset.card_le_card
              intro x hx
              exact Finset.mem_Icc.mpr ⟨Finset.min'_le s x hx, Finset.le_max' s x hx⟩
          _ = s.max' hne + 1 - s.min' hne := Nat.card_Icc _ _
      have hkey : (s.max' hne - s.min' hne) ≤ Nat.floor (Real.log 8 / Real.log (Λ : ℝ)) := by
        refine key (s.min' hne) (s.max' hne) (Finset.min'_le s _ hmax) ?_ ?_
        · exact (Finset.mem_filter.mp hmin).2
        · exact (Finset.mem_filter.mp hmax).2
      omega
  exact hsle

end Work.KMTPlan.A6
