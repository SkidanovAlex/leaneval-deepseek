import Mathlib
import Submission.Work.TMC16Core.Defs

set_option maxHeartbeats 1000000

/-!
# `Core.orbit_blkmin` — the "orbit/block minimum" bound of AJ §9

Statement (see `orbit_blkmin` at the bottom): let `q` be a continued-fraction
denominator sequence for the frequency `α` with errors `Δ m = fracDist (q m · α)`
satisfying the usual sandwich `1/(q(m+1)+q m) < Δ m < 1/q(m+1)` and the
best-approximation property, let `n ≥ 2`, and let `M` blocks of `q(n-1)`
consecutive sites be given inside a window of length `M·q(n-1) ≤ q n` on which the
orbit `ξ + kα` stays at distance `≥ c` from the integers.  Then for any choice of
one site `m j` in each block,

  `∑_{j<M} log (1/(2 fracDist (ξ + m j · α))) ≤ M log (1/Δ(n-1)) + 100 M + log (1/c)`.

## Structure of the proof

The whole content is a *counting* statement: at most **two** of the chosen sites can
be closer than `Δ(n-1)/4` to the integers, and at most **one** of them can be closer
than `Δ(n-1)^2/2` times the size of the window.

* `orbit_smallT`: for `1 ≤ T < q 0`, the elementary determinant identity
  `T·round(q0 α) - round(T α)·q0 = q0·(Tα - round(Tα)) - T·(q0α - round(q0α))`
  (an integer) gives the lower bound `fracDist (T α) > 1/(2 q0 q1)` even in the range
  `T < q 0` where `hbest` is silent.
* `orbit_bigT`: for `q 0 ≤ T < q n`, `hbest` at the CF index of `T` together with the
  sandwich gives `fracDist (T α) > Δ(n-1)/2`.
* Two orbit points `ξ + m i α`, `ξ + m j α` differ by `(m i - m j) α`, and
  `fracDist ((m i - m j) α) ≤ D i + D j`; the difference `|m i - m j|` is `< q n`
  because the window has length `< q n`.  Hence two points that are both
  `< Δ(n-1)/4`-close to `0` must have `|m i - m j| < q 0`; but the blocks are `q(n-1)`
  apart with `q(n-1) ≥ q 0`, so this forces them to be in consecutive blocks, and
  three such points are impossible.
* The two exceptional sites are then handled by the *product* bound
  `D i · D j > c · Δ(n-1)^2/4` coming from `D i + D j > Δ(n-1)^2/2`.
-/

namespace Work.TMC16Core.Core

open Work.TMC16Core
open scoped BigOperators

noncomputable section

/-! ## Elementary facts about `fracDist` -/

lemma fracDist_even' (x : ℝ) : fracDist (-x) = fracDist x := by
  have h1 : fracDist (-x) ≤ fracDist x := by
    calc fracDist (-x) = |(-x) - ↑(round (-x))| := rfl
      _ ≤ |(-x) - ↑(-(round x))| := round_le (-x) (-(round x))
      _ = fracDist x := by
            rw [show (-x : ℝ) - ↑(-(round x)) = -(x - ↑(round x)) by push_cast; ring, abs_neg]
            rfl
  have h2 : fracDist x ≤ fracDist (-x) := by
    calc fracDist x = |x - ↑(round x)| := rfl
      _ ≤ |x - ↑(-(round (-x)))| := round_le x (-(round (-x)))
      _ = fracDist (-x) := by
            rw [show (x : ℝ) - ↑(-(round (-x))) = -((-x) - ↑(round (-x))) by push_cast; ring, abs_neg]
            rfl
  exact le_antisymm h1 h2

lemma fracDist_nonneg' (x : ℝ) : 0 ≤ fracDist x := abs_nonneg _

lemma fracDist_le_half' (x : ℝ) : fracDist x ≤ 1 / 2 := abs_sub_round x

lemma fracDist_add_le' (a b : ℝ) : fracDist (a + b) ≤ fracDist a + fracDist b := by
  have h : fracDist (a + b) ≤ |(a + b) - ↑(round a + round b)| := by
    simpa only [fracDist] using round_le (a + b) (round a + round b)
  refine h.trans ?_
  calc |(a + b) - ↑(round a + round b)| = |(a - ↑(round a)) + (b - ↑(round b))| := by
        push_cast; ring_nf
    _ ≤ |a - ↑(round a)| + |b - ↑(round b)| := abs_add_le _ _
    _ = fracDist a + fracDist b := rfl

/-! ## The two number-theoretic inputs -/

/-- For `1 ≤ T < q 0` — the range where the best-approximation hypothesis is silent —
the determinant identity still gives a polynomial lower bound for `fracDist (T α)`. -/
theorem orbit_smallT {α : ℝ} {q : ℕ → ℕ} {Δ : ℕ → ℝ}
    (hqpos : ∀ m, 0 < q m) (hmono : StrictMono q)
    (hΔpos : ∀ m, 0 < Δ m)
    (hΔeq : ∀ m, Δ m = fracDist ((q m : ℝ) * α))
    (hΔup : ∀ m, Δ m < 1 / ((q (m + 1) : ℝ)))
    (hΔlo : ∀ m, 1 / (((q (m + 1) : ℝ)) + (q m : ℝ)) < Δ m)
    {T : ℕ} (hT1 : 1 ≤ T) (hT2 : T < q 0) :
    1 / (2 * (q 0 : ℝ) * (q 1 : ℝ)) < fracDist ((T : ℝ) * α) := by
  have hq0pos : (0 : ℝ) < (q 0 : ℝ) := by exact_mod_cast hqpos 0
  have hq1pos : (0 : ℝ) < (q 1 : ℝ) := by exact_mod_cast hqpos 1
  have h01 : q 0 < q 1 := hmono (by norm_num)
  have h01R : (q 0 : ℝ) < (q 1 : ℝ) := by exact_mod_cast h01
  have hTpos : (0 : ℝ) < (T : ℝ) := by exact_mod_cast hT1
  have hTlt : (T : ℝ) < (q 0 : ℝ) := by exact_mod_cast hT2
  have hΔ0pos : 0 < Δ 0 := hΔpos 0
  have hq0ne : (q 0 : ℝ) ≠ 0 := ne_of_gt hq0pos
  have hfrT : fracDist ((T : ℝ) * α) = |(T : ℝ) * α - (round ((T : ℝ) * α) : ℝ)| := rfl
  have hfrQ : fracDist ((q 0 : ℝ) * α) = |(q 0 : ℝ) * α - (round ((q 0 : ℝ) * α) : ℝ)| := rfl
  have hΔ0eq : Δ 0 = fracDist ((q 0 : ℝ) * α) := hΔeq 0
  have hdet : (((T : ℤ) * round ((q 0 : ℝ) * α) - round ((T : ℝ) * α) * (q 0 : ℤ) : ℤ) : ℝ)
      = (q 0 : ℝ) * ((T : ℝ) * α - (round ((T : ℝ) * α) : ℝ))
        - (T : ℝ) * ((q 0 : ℝ) * α - (round ((q 0 : ℝ) * α) : ℝ)) := by
    push_cast; ring
  by_cases hD : (T : ℤ) * round ((q 0 : ℝ) * α) - round ((T : ℝ) * α) * (q 0 : ℤ) = 0
  · have hrel : (q 0 : ℝ) * ((T : ℝ) * α - (round ((T : ℝ) * α) : ℝ))
        = (T : ℝ) * ((q 0 : ℝ) * α - (round ((q 0 : ℝ) * α) : ℝ)) := by
      have h := hdet
      rw [hD] at h
      push_cast at h
      linarith
    have habs : (q 0 : ℝ) * fracDist ((T : ℝ) * α) = (T : ℝ) * Δ 0 := by
      have h := congrArg (fun z : ℝ => |z|) hrel
      rw [abs_mul, abs_mul, abs_of_nonneg (le_of_lt hq0pos), abs_of_nonneg (le_of_lt hTpos)] at h
      rw [hfrT, hΔ0eq, hfrQ]
      exact h
    have hval : fracDist ((T : ℝ) * α) = (T : ℝ) * Δ 0 / (q 0 : ℝ) := by
      rw [eq_div_iff hq0ne]; linarith [habs]
    rw [hval]
    have h1 : 1 / (2 * (q 1 : ℝ)) < Δ 0 := by
      have hb : (1 : ℝ) / (2 * (q 1 : ℝ)) < 1 / ((q 1 : ℝ) + (q 0 : ℝ)) := by
        apply one_div_lt_one_div_of_lt (by linarith)
        linarith
      linarith [hΔlo 0]
    have h2 : Δ 0 ≤ (T : ℝ) * Δ 0 := by
      have hT : (1 : ℝ) ≤ (T : ℝ) := by exact_mod_cast hT1
      nlinarith [hΔ0pos]
    have e1 : 1 / (2 * (q 0 : ℝ) * (q 1 : ℝ)) = (1 / (2 * (q 1 : ℝ))) / (q 0 : ℝ) := by
      field_simp
    rw [e1]
    exact lt_of_lt_of_le (div_lt_div_of_pos_right h1 hq0pos)
      (div_le_div_of_nonneg_right h2 (le_of_lt hq0pos))
  · have h1 : (1 : ℝ) ≤
        |(((T : ℤ) * round ((q 0 : ℝ) * α) - round ((T : ℝ) * α) * (q 0 : ℤ) : ℤ) : ℝ)| := by
      have := Int.one_le_abs hD
      exact_mod_cast this
    have hb : |(((T : ℤ) * round ((q 0 : ℝ) * α) - round ((T : ℝ) * α) * (q 0 : ℤ) : ℤ) : ℝ)|
        ≤ (q 0 : ℝ) * fracDist ((T : ℝ) * α) + (T : ℝ) * Δ 0 := by
      rw [hdet]
      have h3 : |(q 0 : ℝ) * ((T : ℝ) * α - (round ((T : ℝ) * α) : ℝ))
            - (T : ℝ) * ((q 0 : ℝ) * α - (round ((q 0 : ℝ) * α) : ℝ))|
          ≤ |(q 0 : ℝ) * ((T : ℝ) * α - (round ((T : ℝ) * α) : ℝ))|
            + |(T : ℝ) * ((q 0 : ℝ) * α - (round ((q 0 : ℝ) * α) : ℝ))| := by
        have h := abs_add_le ((q 0 : ℝ) * ((T : ℝ) * α - (round ((T : ℝ) * α) : ℝ)))
          (-((T : ℝ) * ((q 0 : ℝ) * α - (round ((q 0 : ℝ) * α) : ℝ))))
        rw [show (q 0 : ℝ) * ((T : ℝ) * α - (round ((T : ℝ) * α) : ℝ))
              + -((T : ℝ) * ((q 0 : ℝ) * α - (round ((q 0 : ℝ) * α) : ℝ)))
            = (q 0 : ℝ) * ((T : ℝ) * α - (round ((T : ℝ) * α) : ℝ))
              - (T : ℝ) * ((q 0 : ℝ) * α - (round ((q 0 : ℝ) * α) : ℝ)) by ring,
            abs_neg] at h
        exact h
      have h4 : |(q 0 : ℝ) * ((T : ℝ) * α - (round ((T : ℝ) * α) : ℝ))|
          = (q 0 : ℝ) * fracDist ((T : ℝ) * α) := by
        rw [abs_mul, abs_of_nonneg (le_of_lt hq0pos), ← hfrT]
      have h5 : |(T : ℝ) * ((q 0 : ℝ) * α - (round ((q 0 : ℝ) * α) : ℝ))| = (T : ℝ) * Δ 0 := by
        rw [abs_mul, abs_of_nonneg (le_of_lt hTpos), ← hfrQ, ← hΔ0eq]
      rw [h4, h5] at h3
      exact h3
    have h2 : 1 - (T : ℝ) * Δ 0 ≤ (q 0 : ℝ) * fracDist ((T : ℝ) * α) := by linarith
    have hc : 1 - (q 0 : ℝ) * Δ 0 < (q 0 : ℝ) * fracDist ((T : ℝ) * α) := by
      have : (T : ℝ) * Δ 0 < (q 0 : ℝ) * Δ 0 := mul_lt_mul_of_pos_right hTlt hΔ0pos
      linarith
    have h4' : (1 - (q 0 : ℝ) * Δ 0) / (q 0 : ℝ) < fracDist ((T : ℝ) * α) := by
      rw [div_lt_iff₀ hq0pos]; linarith
    have h5' : (1 - (q 0 : ℝ) * Δ 0) / (q 0 : ℝ) = 1 / (q 0 : ℝ) - Δ 0 := by
      field_simp
    rw [h5'] at h4'
    have h6 : Δ 0 < 1 / (q 1 : ℝ) := hΔup 0
    have h7 : 1 / (q 0 : ℝ) - 1 / (q 1 : ℝ) = ((q 1 : ℝ) - (q 0 : ℝ)) / ((q 0 : ℝ) * (q 1 : ℝ)) := by
      field_simp
    have h8 : (1 : ℝ) ≤ (q 1 : ℝ) - (q 0 : ℝ) := by
      have h : (1 : ℤ) ≤ (q 1 : ℤ) - (q 0 : ℤ) := by omega
      exact_mod_cast h
    have h9 : (1 : ℝ) / ((q 0 : ℝ) * (q 1 : ℝ))
        ≤ ((q 1 : ℝ) - (q 0 : ℝ)) / ((q 0 : ℝ) * (q 1 : ℝ)) :=
      div_le_div_of_nonneg_right h8 (by positivity)
    have hx : (0 : ℝ) < (q 0 : ℝ) * (q 1 : ℝ) := by positivity
    have h10 : 1 / (2 * ((q 0 : ℝ) * (q 1 : ℝ))) < 1 / ((q 0 : ℝ) * (q 1 : ℝ)) := by
      have e : 1 / (2 * ((q 0 : ℝ) * (q 1 : ℝ)))
          = ((1 : ℝ) / 2) / ((q 0 : ℝ) * (q 1 : ℝ)) := by ring
      rw [e, div_lt_div_iff_of_pos_right hx]
      norm_num
    calc 1 / (2 * (q 0 : ℝ) * (q 1 : ℝ)) = 1 / (2 * ((q 0 : ℝ) * (q 1 : ℝ))) := by ring
      _ < 1 / ((q 0 : ℝ) * (q 1 : ℝ)) := h10
      _ ≤ ((q 1 : ℝ) - (q 0 : ℝ)) / ((q 0 : ℝ) * (q 1 : ℝ)) := h9
      _ = 1 / (q 0 : ℝ) - 1 / (q 1 : ℝ) := h7.symm
      _ < 1 / (q 0 : ℝ) - Δ 0 := by linarith
      _ < fracDist ((T : ℝ) * α) := h4'

/-- For `q 0 ≤ T < q n` the best-approximation hypothesis at the continued-fraction
index of `T` together with the sandwich bounds gives `fracDist (T α) > Δ(n-1)/2`. -/
theorem orbit_bigT {α : ℝ} {q : ℕ → ℕ} {Δ : ℕ → ℝ}
    (hqpos : ∀ m, 0 < q m) (hmono : StrictMono q)
    (hΔpos : ∀ m, 0 < Δ m)
    (hΔeq : ∀ m, Δ m = fracDist ((q m : ℝ) * α))
    (hΔup : ∀ m, Δ m < 1 / ((q (m + 1) : ℝ)))
    (hΔlo : ∀ m, 1 / (((q (m + 1) : ℝ)) + (q m : ℝ)) < Δ m)
    (hbest : ∀ m k : ℕ, q m ≤ k → k < q (m + 1) → Δ m ≤ fracDist ((k : ℝ) * α))
    {n T : ℕ} (hn : 1 ≤ n) (hT1 : q 0 ≤ T) (hT2 : T < q n) :
    Δ (n - 1) / 2 < fracDist ((T : ℝ) * α) := by
  set s : Finset ℕ := (Finset.range n).filter (fun k => q k ≤ T) with hs
  have hne : s.Nonempty := by
    refine ⟨0, ?_⟩
    rw [hs, Finset.mem_filter]
    exact ⟨Finset.mem_range.mpr (by omega), hT1⟩
  set m : ℕ := s.max' hne with hmdef
  have hms : m ∈ s := by rw [hmdef]; exact s.max'_mem hne
  have hm1 : q m ≤ T := by
    have h := hms; rw [hs, Finset.mem_filter] at h; exact h.2
  have hmn : m < n := by
    have h := hms; rw [hs, Finset.mem_filter] at h; exact Finset.mem_range.mp h.1
  have hmn1 : m + 1 ≤ n := hmn
  have hm2 : T < q (m + 1) := by
    by_contra hcon
    push Not at hcon
    rcases lt_or_eq_of_le hmn1 with hlt | heq
    · have hmem : m + 1 ∈ s := by
        rw [hs, Finset.mem_filter]
        exact ⟨Finset.mem_range.mpr hlt, hcon⟩
      have hle : m + 1 ≤ s.max' hne := Finset.le_max' s (m + 1) hmem
      omega
    · rw [heq] at hcon
      omega
  have hDm : Δ m ≤ fracDist ((T : ℝ) * α) := hbest m T hm1 hm2
  have hqmlt : q (m + 1) ≤ q n := hmono.monotone hmn1
  have hstep : 1 / (2 * (q n : ℝ)) < Δ m := by
    have hlo := hΔlo m
    have hqlt : (q m : ℝ) < (q (m + 1) : ℝ) := by
      have h := hmono (Nat.lt_succ_self m)
      exact_mod_cast h
    have hqn : (q (m + 1) : ℝ) ≤ (q n : ℝ) := by exact_mod_cast hqmlt
    have hqnpos : (0 : ℝ) < (q n : ℝ) := by exact_mod_cast hqpos n
    have hqmp : (0 : ℝ) < (q m : ℝ) := by exact_mod_cast hqpos m
    have : (1 : ℝ) / (2 * (q n : ℝ)) < 1 / ((q (m + 1) : ℝ) + (q m : ℝ)) := by
      apply one_div_lt_one_div_of_lt (by linarith)
      linarith
    linarith
  have hfinal : Δ (n - 1) / 2 < 1 / (2 * (q n : ℝ)) := by
    have h := hΔup (n - 1)
    have hn1 : n - 1 + 1 = n := Nat.sub_add_cancel hn
    rw [hn1] at h
    have h2 : (1 : ℝ) / (2 * (q n : ℝ)) = (1 / (q n : ℝ)) / 2 := by ring
    rw [h2]
    linarith
  linarith [hDm, hstep, hfinal]


/-- **Main counting argument** for `orbit_blkmin`, with the two number-theoretic
inputs (`orbit_smallT`, `orbit_bigT`) as hypotheses. -/
theorem orbit_core {α : ℝ} {q : ℕ → ℕ} {Δ : ℕ → ℝ}
    {n : ℕ} (hn : 2 ≤ n) {p : ℤ} {ξ c : ℝ} {M : ℕ} (hM : 1 ≤ M) (hc : 0 < c)
    (hqn1pos : 0 < q (n - 1)) (hq0n1 : q 0 ≤ q (n - 1))
    (hDDpos : 0 < Δ (n - 1)) (hDDup : Δ (n - 1) < 1 / (q n : ℝ))
    (hq0pos : (0 : ℝ) < (q 0 : ℝ)) (hq1pos : (0 : ℝ) < (q 1 : ℝ))
    (hqnpos : (0 : ℝ) < (q n : ℝ))
    (hq0n : (q 0 : ℝ) < (q n : ℝ)) (hq1n : (q 1 : ℝ) < (q n : ℝ))
    (hsmall : ∀ T : ℕ, 1 ≤ T → T < q 0 →
      1 / (2 * (q 0 : ℝ) * (q 1 : ℝ)) < fracDist ((T : ℝ) * α))
    (hbig : ∀ T : ℕ, q 0 ≤ T → T < q n → Δ (n - 1) / 2 < fracDist ((T : ℝ) * α))
    (hclow : ∀ k ∈ Finset.Icc p (p + (M : ℤ) * (q (n - 1) : ℤ) - 1),
      c ≤ fracDist (ξ + (k : ℝ) * α))
    (hTn : (M : ℤ) * (q (n - 1) : ℤ) ≤ (q n : ℤ))
    (m : ℕ → ℤ)
    (hmem : ∀ j, j < M → m j ∈ Finset.Icc (p + (j : ℤ) * (q (n - 1) : ℤ))
      (p + (j : ℤ) * (q (n - 1) : ℤ) + (q (n - 1) : ℤ) - 1)) :
    ∑ j ∈ Finset.range M, Real.log (1 / (2 * fracDist (ξ + (m j : ℝ) * α)))
      ≤ (M : ℝ) * Real.log (1 / Δ (n - 1)) + 100 * (M : ℝ) + Real.log (1 / c) := by
  let D : ℕ → ℝ := fun j => fracDist (ξ + (m j : ℝ) * α)
  let f : ℕ → ℝ := fun j => Real.log (1 / (2 * D j))
  let L : ℝ := Real.log (1 / Δ (n - 1))
  set S : Finset ℕ := (Finset.range M).filter (fun j => D j < Δ (n - 1) / 4) with hSdef
  change ∑ j ∈ Finset.range M, f j ≤ (M : ℝ) * L + 100 * (M : ℝ) + Real.log (1 / c)
  have hqZ : (1 : ℤ) ≤ (q (n - 1) : ℤ) := by exact_mod_cast hqn1pos
  have hqZ0 : (0 : ℤ) < (q (n - 1) : ℤ) := by exact_mod_cast hqn1pos
  have hq0n1Z : (q 0 : ℤ) ≤ (q (n - 1) : ℤ) := by exact_mod_cast hq0n1
  have hqn1 : (1 : ℝ) ≤ (q n : ℝ) := by
    have h : (0 : ℕ) < q n := by exact_mod_cast hqnpos
    exact_mod_cast (by omega : 1 ≤ q n)
  have hlog2 : Real.log 2 ≤ 1 := by
    have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 by norm_num); linarith
  have hlog2pos : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hLpos : 0 ≤ L := by
    have h : 1 ≤ 1 / Δ (n - 1) := by
      rw [le_div_iff₀ hDDpos]
      have h3 : 1 / (q n : ℝ) ≤ 1 := by
        rw [div_le_one hqnpos]; exact hqn1
      linarith
    simpa only [L] using Real.log_nonneg h
  -- the window contains all chosen sites
  have hwin : ∀ j, j < M → m j ∈ Finset.Icc p (p + (M : ℤ) * (q (n - 1) : ℤ) - 1) := by
    intro j hj
    obtain ⟨h1, h2⟩ := Finset.mem_Icc.mp (hmem j hj)
    rw [Finset.mem_Icc]
    constructor
    · have hz : (0 : ℤ) ≤ (j : ℤ) * (q (n - 1) : ℤ) :=
        mul_nonneg (by positivity) (le_of_lt hqZ0)
      linarith
    · have hjM : (j : ℤ) + 1 ≤ (M : ℤ) := by exact_mod_cast Nat.succ_le_of_lt hj
      nlinarith [h2, hjM, hqZ]
  have hDlow : ∀ j, j < M → c ≤ D j := by
    intro j hj
    have := hclow (m j) (hwin j hj)
    simpa only [D] using this
  have hDpos : ∀ j, j < M → 0 < D j := fun j hj => lt_of_lt_of_le hc (hDlow j hj)
  have hcle : c ≤ 1 / 2 := by
    have h1 := hDlow 0 hM
    have h2 : D 0 ≤ 1 / 2 := by
      have := fracDist_le_half' (ξ + (m 0 : ℝ) * α)
      simpa only [D] using this
    linarith
  -- the blocks are ordered and separated
  have hlt_blocks : ∀ i j, i < M → j < M → i < j → m i < m j := by
    intro i j hi hj hij
    obtain ⟨-, hi2⟩ := Finset.mem_Icc.mp (hmem i hi)
    obtain ⟨hj1, -⟩ := Finset.mem_Icc.mp (hmem j hj)
    have hij1 : (i : ℤ) + 1 ≤ (j : ℤ) := by exact_mod_cast (by omega : i + 1 ≤ j)
    have hstep : ((i : ℤ) + 1) * (q (n - 1) : ℤ) ≤ (j : ℤ) * (q (n - 1) : ℤ) :=
      mul_le_mul_of_nonneg_right hij1 (le_of_lt hqZ0)
    nlinarith [hi2, hj1, hstep]
  have hTd1 : ∀ i j, i < M → j < M → i ≠ j → 1 ≤ (m i - m j).natAbs := by
    intro i j hi hj hij
    have hne : m i ≠ m j := by
      intro heq
      rcases lt_or_gt_of_ne hij with hlt | hgt
      · have := hlt_blocks i j hi hj hlt; omega
      · have := hlt_blocks j i hj hi hgt; omega
    have h : m i - m j ≠ 0 := sub_ne_zero.mpr hne
    have h2 := Int.natAbs_pos.mpr h
    omega
  have hTd2 : ∀ i j, i < M → j < M → (m i - m j).natAbs < q n := by
    intro i j hi hj
    obtain ⟨hi1, hi2⟩ := Finset.mem_Icc.mp (hmem i hi)
    obtain ⟨hj1, hj2⟩ := Finset.mem_Icc.mp (hmem j hj)
    have hiM : (i : ℤ) + 1 ≤ (M : ℤ) := by exact_mod_cast Nat.succ_le_of_lt hi
    have hjM : (j : ℤ) + 1 ≤ (M : ℤ) := by exact_mod_cast Nat.succ_le_of_lt hj
    have hb1 : m i ≤ p + (M : ℤ) * (q (n - 1) : ℤ) - 1 := by nlinarith [hi2, hiM, hqZ]
    have hb2 : m j ≤ p + (M : ℤ) * (q (n - 1) : ℤ) - 1 := by nlinarith [hj2, hjM, hqZ]
    have habs : |m i - m j| ≤ (M : ℤ) * (q (n - 1) : ℤ) - 1 := by
      rw [abs_le]
      constructor
      · nlinarith [hi1, hb2]
      · nlinarith [hj1, hb1]
    have hnat : (((m i - m j).natAbs : ℤ)) ≤ (M : ℤ) * (q (n - 1) : ℤ) - 1 := by
      rw [← Int.abs_eq_natAbs]; exact habs
    have hlt : (((m i - m j).natAbs : ℤ)) < (q n : ℤ) := by
      have h := hTn; linarith
    exact_mod_cast hlt
  have hTd3 : ∀ i j, i < M → j < M → fracDist (((m i - m j : ℤ) : ℝ) * α) ≤ D i + D j := by
    intro i j hi hj
    have h := fracDist_add_le' (ξ + (m i : ℝ) * α) (-(ξ + (m j : ℝ) * α))
    have e : ξ + (m i : ℝ) * α + -(ξ + (m j : ℝ) * α) = ((m i - m j : ℤ) : ℝ) * α := by
      push_cast; ring
    rw [e, fracDist_even'] at h
    simpa only [D] using h
  have hconv : ∀ z : ℤ, fracDist ((z : ℝ) * α)
      = fracDist (((z.natAbs : ℕ) : ℝ) * α) := by
    intro z
    rcases Int.natAbs_eq z with h | h
    · have hz : ((z : ℝ)) = ((z.natAbs : ℕ) : ℝ) := by
        rw [h]; simp
      rw [hz]
    · have hz : ((z : ℝ)) = -(((z.natAbs : ℕ) : ℝ)) := by
        rw [h]; push_cast; simp
      rw [hz, show (-(((z.natAbs : ℕ) : ℝ))) * α = -((((z.natAbs : ℕ) : ℝ)) * α) by ring,
        fracDist_even']
  -- the pairwise claims
  have hpair_big : ∀ i j, i < M → j < M → i ≠ j → D i < Δ (n - 1) / 4 → D j < Δ (n - 1) / 4 →
      ¬ (q 0 ≤ (m i - m j).natAbs) := by
    intro i j hi hj hij hdi hdj hge
    have hT2 := hTd2 i j hi hj
    have hbig' := hbig _ hge hT2
    have hle := hTd3 i j hi hj
    rw [hconv (m i - m j)] at hle
    linarith
  have hnum : Δ (n - 1) * Δ (n - 1) / 2 < 1 / (2 * (q 0 : ℝ) * (q 1 : ℝ)) := by
    have hsq : Δ (n - 1) * Δ (n - 1) < (1 / (q n : ℝ)) * (1 / (q n : ℝ)) := by
      have h2 : (0 : ℝ) < 1 / (q n : ℝ) := by positivity
      nlinarith [hDDup, hDDpos, h2]
    have hlt : (q 0 : ℝ) * (q 1 : ℝ) < (q n : ℝ) * (q n : ℝ) := by
      nlinarith [hq0n, hq1n, hq0pos, hq1pos, hqnpos]
    have hstep : 1 / (2 * ((q n : ℝ) * (q n : ℝ))) < 1 / (2 * ((q 0 : ℝ) * (q 1 : ℝ))) := by
      apply one_div_lt_one_div_of_lt (by positivity)
      linarith
    have e1 : 1 / (2 * ((q n : ℝ) * (q n : ℝ))) = (1 / (q n : ℝ)) * (1 / (q n : ℝ)) / 2 := by
      ring
    have e2 : 1 / (2 * ((q 0 : ℝ) * (q 1 : ℝ))) = 1 / (2 * (q 0 : ℝ) * (q 1 : ℝ)) := by ring
    rw [e1] at hstep
    rw [e2] at hstep
    have h5 : Δ (n - 1) * Δ (n - 1) / 2 < (1 / (q n : ℝ)) * (1 / (q n : ℝ)) / 2 := by linarith
    linarith
  have hpair_small : ∀ i j, i < M → j < M → i ≠ j → D i < Δ (n - 1) / 4 →
      D j < Δ (n - 1) / 4 → (m i - m j).natAbs < q 0 →
      Δ (n - 1) * Δ (n - 1) / 2 < D i + D j := by
    intro i j hi hj hij hdi hdj hlt
    have hT1 := hTd1 i j hi hj hij
    have hs := hsmall _ hT1 hlt
    have hle := hTd3 i j hi hj
    rw [hconv (m i - m j)] at hle
    linarith
  have hprod : ∀ i j, i < M → j < M → i ≠ j → D i < Δ (n - 1) / 4 →
      D j < Δ (n - 1) / 4 → Δ (n - 1) * Δ (n - 1) / 2 < D i + D j := by
    intro i j hi hj hij hdi hdj
    rcases lt_or_ge ((m i - m j).natAbs) (q 0) with hlt | hge
    · exact hpair_small i j hi hj hij hdi hdj hlt
    · exact absurd hge (hpair_big i j hi hj hij hdi hdj)
  have hfar : ∀ i j, i < M → j < M → D i < Δ (n - 1) / 4 → D j < Δ (n - 1) / 4 →
      i + 2 ≤ j → False := by
    intro i j hi hj hdi hdj hij
    have hge : q 0 ≤ (m i - m j).natAbs := by
      obtain ⟨-, hi2⟩ := Finset.mem_Icc.mp (hmem i hi)
      obtain ⟨hj1, -⟩ := Finset.mem_Icc.mp (hmem j hj)
      have hij' : (i : ℤ) + 2 ≤ (j : ℤ) := by exact_mod_cast hij
      have hlow : m j - m i ≥ (q (n - 1) : ℤ) + 1 := by nlinarith [hi2, hj1, hij', hqZ]
      have hle : m i ≤ m j := by linarith
      have hmm : m i - m j ≤ 0 := by omega
      have hnat : (((m i - m j).natAbs : ℤ)) = m j - m i := by
        have h1 : (((m i - m j).natAbs : ℤ)) = |m i - m j| := (Int.abs_eq_natAbs _).symm
        rw [h1, abs_of_nonpos hmm]
        ring
      have : (q 0 : ℤ) ≤ (((m i - m j).natAbs : ℤ)) := by omega
      exact_mod_cast this
    exact hpair_big i j hi hj (by omega) hdi hdj hge
  -- at most two exceptional sites
  have hcard2 : S.card ≤ 2 := by
    by_contra hcon
    push Not at hcon
    have hne : S.Nonempty := Finset.card_pos.mp (by omega)
    set a : ℕ := S.min' hne with ha
    set b : ℕ := S.max' hne with hb
    have haS : a ∈ S := by rw [ha]; exact S.min'_mem hne
    have hbS : b ∈ S := by rw [hb]; exact S.max'_mem hne
    have hle : ∀ x ∈ S, a ≤ x := fun x hx => by rw [ha]; exact S.min'_le x hx
    have hge : ∀ x ∈ S, x ≤ b := fun x hx => by rw [hb]; exact S.le_max' x hx
    have haM : a < M := by
      have h := haS; rw [hSdef, Finset.mem_filter] at h; exact Finset.mem_range.mp h.1
    have hbM : b < M := by
      have h := hbS; rw [hSdef, Finset.mem_filter] at h; exact Finset.mem_range.mp h.1
    have haD : D a < Δ (n - 1) / 4 := by
      have h := haS; rw [hSdef, Finset.mem_filter] at h; exact h.2
    have hbD : D b < Δ (n - 1) / 4 := by
      have h := hbS; rw [hSdef, Finset.mem_filter] at h; exact h.2
    have hltab : a < b := by
      by_contra hc2
      push Not at hc2
      have hsub : S ⊆ {a} := by
        intro x hx
        have h1 := hle x hx
        have h2 := hge x hx
        simp only [Finset.mem_singleton]
        omega
      have hcard := Finset.card_le_card hsub
      simp only [Finset.card_singleton] at hcard
      omega
    have hfar' : a + 2 ≤ b := by
      by_contra hc2
      push Not at hc2
      have hsub : S ⊆ {a, b} := by
        intro x hx
        have h1 := hle x hx
        have h2 := hge x hx
        simp only [Finset.mem_insert, Finset.mem_singleton]
        omega
      have hcard := Finset.card_le_card hsub
      have h2 : ({a, b} : Finset ℕ).card ≤ 2 := Finset.card_le_two
      omega
    exact hfar a b haM hbM haD hbD hfar'
  -- the sum bound
  have hsplit := Finset.sum_filter_add_sum_filter_not (Finset.range M)
    (fun j => D j < Δ (n - 1) / 4) f
  rw [← hSdef] at hsplit
  set S' : Finset ℕ := (Finset.range M).filter (fun j => ¬ D j < Δ (n - 1) / 4) with hS'def
  have hcompl : ∀ j ∈ S', f j ≤ L + Real.log 2 := by
    intro j hj
    have hjM : j < M := by
      have h := hj; rw [hS'def, Finset.mem_filter] at h; exact Finset.mem_range.mp h.1
    have hnot : ¬ D j < Δ (n - 1) / 4 := by
      have h := hj; rw [hS'def, Finset.mem_filter] at h; exact h.2
    have hge : Δ (n - 1) / 4 ≤ D j := by rw [not_lt] at hnot; exact hnot
    have hDp : 0 < D j := hDpos j hjM
    have h1 : 1 / (2 * D j) ≤ 2 / Δ (n - 1) := by
      have hkey : Δ (n - 1) ≤ 4 * D j := by linarith
      calc 1 / (2 * D j) = Δ (n - 1) / (2 * D j * Δ (n - 1)) := by
            field_simp
        _ ≤ 4 * D j / (2 * D j * Δ (n - 1)) := by
              apply div_le_div_of_nonneg_right hkey (by positivity)
        _ = 2 / Δ (n - 1) := by
              field_simp
              ring
    calc f j = Real.log (1 / (2 * D j)) := rfl
      _ ≤ Real.log (2 / Δ (n - 1)) := Real.log_le_log (by positivity) h1
      _ = L + Real.log 2 := by
            rw [Real.log_div (by norm_num) (ne_of_gt hDDpos)]
            simp only [L, one_div, Real.log_inv]
            ring
  have hS'card : S'.card = M - S.card := by
    have h1 := Finset.card_filter_add_card_filter_not (s := Finset.range M)
      (p := fun j => D j < Δ (n - 1) / 4)
    rw [← hSdef, ← hS'def] at h1
    have h2 : (Finset.range M).card = M := Finset.card_range M
    omega
  have hS'sum : ∑ j ∈ S', f j ≤ ((M - S.card : ℕ) : ℝ) * (L + Real.log 2) := by
    have h1 : ∑ j ∈ S', f j ≤ S'.card • (L + Real.log 2) :=
      Finset.sum_le_card_nsmul S' f (L + Real.log 2) hcompl
    rw [nsmul_eq_mul, hS'card] at h1
    exact h1
  have hlog2M : (M : ℝ) * Real.log 2 ≤ 100 * (M : ℝ) := by
    have hM' : (0 : ℝ) ≤ (M : ℝ) := by positivity
    nlinarith [hlog2, hM']
  rcases lt_or_ge 1 S.card with hcard | hcard
  · -- exactly two exceptional sites
    have hcard_eq : S.card = 2 := by omega
    obtain ⟨a, b, hab, hSab⟩ := Finset.card_eq_two.mp hcard_eq
    have haS : a ∈ S := by rw [hSab]; simp
    have hbS : b ∈ S := by rw [hSab]; simp
    have haM : a < M := by
      have h := haS; rw [hSdef, Finset.mem_filter] at h; exact Finset.mem_range.mp h.1
    have hbM : b < M := by
      have h := hbS; rw [hSdef, Finset.mem_filter] at h; exact Finset.mem_range.mp h.1
    have haD : D a < Δ (n - 1) / 4 := by
      have h := haS; rw [hSdef, Finset.mem_filter] at h; exact h.2
    have hbD : D b < Δ (n - 1) / 4 := by
      have h := hbS; rw [hSdef, Finset.mem_filter] at h; exact h.2
    have hpair := hprod a b haM hbM hab haD hbD
    have hcDa : c ≤ D a := hDlow a haM
    have hcDb : c ≤ D b := hDlow b hbM
    have hDa : 0 < D a := hDpos a haM
    have hDb : 0 < D b := hDpos b hbM
    have hquart : (0 : ℝ) < Δ (n - 1) * Δ (n - 1) / 4 := by positivity
    have hprod' : c * (Δ (n - 1) * Δ (n - 1) / 4) < D a * D b := by
      rcases le_total (D a) (D b) with hle | hle
      · have h1 : Δ (n - 1) * Δ (n - 1) / 4 < D b := by linarith
        have hA : c * (Δ (n - 1) * Δ (n - 1) / 4) ≤ D a * (Δ (n - 1) * Δ (n - 1) / 4) :=
          mul_le_mul_of_nonneg_right hcDa hquart.le
        have hB : D a * (Δ (n - 1) * Δ (n - 1) / 4) < D a * D b :=
          mul_lt_mul_of_pos_left h1 hDa
        linarith
      · have h1 : Δ (n - 1) * Δ (n - 1) / 4 < D a := by linarith
        have hA : c * (Δ (n - 1) * Δ (n - 1) / 4) ≤ D b * (Δ (n - 1) * Δ (n - 1) / 4) :=
          mul_le_mul_of_nonneg_right hcDb hquart.le
        have hB : D b * (Δ (n - 1) * Δ (n - 1) / 4) < D b * D a :=
          mul_lt_mul_of_pos_left h1 hDb
        linarith
    have hSsum : ∑ j ∈ S, f j ≤ Real.log (1 / c) + 2 * L := by
      rw [hSab, Finset.sum_pair hab]
      have h1 : f a + f b = Real.log (1 / (4 * (D a * D b))) := by
        rw [show f a = Real.log (1 / (2 * D a)) from rfl,
          show f b = Real.log (1 / (2 * D b)) from rfl]
        rw [← Real.log_mul (by positivity) (by positivity)]
        congr 1
        field_simp
        ring
      rw [h1]
      have h2 : 1 / (4 * (D a * D b)) ≤ 1 / (c * (Δ (n - 1) * Δ (n - 1))) := by
        rw [one_div, one_div, inv_le_inv₀]
        · linarith
        · positivity
        · positivity
      calc Real.log (1 / (4 * (D a * D b)))
          ≤ Real.log (1 / (c * (Δ (n - 1) * Δ (n - 1)))) := by
            apply Real.log_le_log (by positivity) h2
        _ = Real.log (1 / c) + 2 * L := by
              rw [one_div, Real.log_inv, Real.log_mul (ne_of_gt hc) (by positivity),
                show Δ (n - 1) * Δ (n - 1) = (Δ (n - 1)) ^ 2 by ring, Real.log_pow]
              simp only [L, one_div, Real.log_inv]
              ring
    rw [← hsplit]
    have hM2 : 2 ≤ M := by
      have h := Finset.card_le_card (Finset.filter_subset (fun j => D j < Δ (n - 1) / 4)
        (Finset.range M))
      rw [← hSdef, Finset.card_range] at h
      omega
    have hcast : ((M - S.card : ℕ) : ℝ) = (M : ℝ) - 2 := by
      rw [hcard_eq]
      exact Nat.cast_sub hM2
    rw [hcast] at hS'sum
    have hM' : (0 : ℝ) ≤ (M : ℝ) := by positivity
    have h2 : ((M : ℝ) - 2) * Real.log 2 ≤ 100 * (M : ℝ) := by nlinarith [hlog2, hM']
    calc ∑ x ∈ S, f x + ∑ x ∈ S', f x
        ≤ (Real.log (1 / c) + 2 * L) + (((M : ℝ) - 2) * (L + Real.log 2)) :=
          add_le_add hSsum hS'sum
      _ = Real.log (1 / c) + (M : ℝ) * L + ((M : ℝ) - 2) * Real.log 2 := by ring
      _ ≤ Real.log (1 / c) + (M : ℝ) * L + 100 * (M : ℝ) :=
            add_le_add (le_refl (Real.log (1 / c) + (M : ℝ) * L)) h2
      _ = (M : ℝ) * L + 100 * (M : ℝ) + Real.log (1 / c) := by ring
  · -- at most one exceptional site
    have hSsum : ∑ j ∈ S, f j ≤ Real.log (1 / c) := by
      rcases Finset.eq_empty_or_nonempty S with hemp | ⟨j₀, hj₀⟩
      · rw [hemp]; simp only [Finset.sum_empty]
        apply Real.log_nonneg
        rw [le_div_iff₀ hc]; linarith
      · have hsingle : S = {j₀} := by
          rw [Finset.card_le_one] at hcard
          ext x
          simp only [Finset.mem_singleton]
          exact ⟨fun hx => hcard x hx j₀ hj₀, fun hx => hx ▸ hj₀⟩
        rw [hsingle, Finset.sum_singleton]
        have hjM : j₀ < M := by
          have h := hj₀; rw [hSdef, Finset.mem_filter] at h; exact Finset.mem_range.mp h.1
        have hcD : c ≤ D j₀ := hDlow j₀ hjM
        have hDp : 0 < D j₀ := hDpos j₀ hjM
        calc f j₀ = Real.log (1 / (2 * D j₀)) := rfl
          _ ≤ Real.log (1 / c) := by
                apply Real.log_le_log (by positivity)
                exact one_div_le_one_div_of_le hc (by linarith)
    have h1 : ((M - S.card : ℕ) : ℝ) ≤ (M : ℝ) := by
      have : M - S.card ≤ M := Nat.sub_le _ _
      exact_mod_cast this
    have h2 : 0 ≤ L + Real.log 2 := by linarith
    have h3 : ((M - S.card : ℕ) : ℝ) * (L + Real.log 2) ≤ (M : ℝ) * (L + Real.log 2) :=
      mul_le_mul_of_nonneg_right h1 h2
    rw [← hsplit]
    calc ∑ x ∈ S, f x + ∑ x ∈ S', f x
        ≤ Real.log (1 / c) + (M : ℝ) * (L + Real.log 2) :=
          add_le_add hSsum (le_trans hS'sum h3)
      _ = Real.log (1 / c) + (M : ℝ) * L + (M : ℝ) * Real.log 2 := by ring
      _ ≤ Real.log (1 / c) + (M : ℝ) * L + 100 * (M : ℝ) :=
            add_le_add (le_refl (Real.log (1 / c) + (M : ℝ) * L)) hlog2M
      _ = (M : ℝ) * L + 100 * (M : ℝ) + Real.log (1 / c) := by ring

/-- **AJ §9, orbit/block-minimum estimate.**  See the module docstring. -/
theorem orbit_blkmin {α : ℝ} {q : ℕ → ℕ} {Δ : ℕ → ℝ}
    (hqpos : ∀ m, 0 < q m) (hmono : StrictMono q)
    (hΔpos : ∀ m, 0 < Δ m)
    (hΔeq : ∀ m, Δ m = Work.TMC16Core.fracDist ((q m : ℝ) * α))
    (hΔup : ∀ m, Δ m < 1 / ((q (m + 1) : ℝ)))
    (hΔlo : ∀ m, 1 / (((q (m + 1) : ℝ)) + (q m : ℝ)) < Δ m)
    (hbest : ∀ m k : ℕ, q m ≤ k → k < q (m + 1) → Δ m ≤ Work.TMC16Core.fracDist ((k : ℝ) * α))
    {n : ℕ} (hn : 2 ≤ n) {p : ℤ} {ξ c : ℝ} {M : ℕ} (hM : 1 ≤ M) (hc : 0 < c)
    (hclow : ∀ k ∈ Finset.Icc p (p + (M : ℤ) * (q (n - 1) : ℤ) - 1),
      c ≤ Work.TMC16Core.fracDist (ξ + (k : ℝ) * α))
    (hTn : (M : ℤ) * (q (n - 1) : ℤ) ≤ (q n : ℤ))
    (m : ℕ → ℤ)
    (hmem : ∀ j, j < M → m j ∈ Finset.Icc (p + (j : ℤ) * (q (n - 1) : ℤ))
      (p + (j : ℤ) * (q (n - 1) : ℤ) + (q (n - 1) : ℤ) - 1)) :
    ∑ j ∈ Finset.range M, Real.log (1 / (2 * Work.TMC16Core.fracDist (ξ + (m j : ℝ) * α)))
      ≤ (M : ℝ) * Real.log (1 / Δ (n - 1)) + 100 * (M : ℝ) + Real.log (1 / c) := by
  have hn1 : 1 ≤ n := by omega
  have hqn1pos : 0 < q (n - 1) := hqpos (n - 1)
  have hq0n1 : q 0 ≤ q (n - 1) := hmono.monotone (by omega)
  have hDDpos' : 0 < Δ (n - 1) := hΔpos (n - 1)
  have hDDup' : Δ (n - 1) < 1 / (q n : ℝ) := by
    have h := hΔup (n - 1)
    have : n - 1 + 1 = n := Nat.sub_add_cancel hn1
    rwa [this] at h
  have hq0pos' : (0 : ℝ) < (q 0 : ℝ) := by exact_mod_cast hqpos 0
  have hq1pos' : (0 : ℝ) < (q 1 : ℝ) := by exact_mod_cast hqpos 1
  have hqnpos' : (0 : ℝ) < (q n : ℝ) := by exact_mod_cast hqpos n
  have hq0n' : (q 0 : ℝ) < (q n : ℝ) := by
    have h : q 0 < q n := hmono (by omega)
    exact_mod_cast h
  have hq1n' : (q 1 : ℝ) < (q n : ℝ) := by
    have h : q 1 < q n := hmono (by omega)
    exact_mod_cast h
  exact orbit_core hn hM hc hqn1pos hq0n1 hDDpos' hDDup' hq0pos' hq1pos' hqnpos'
    hq0n' hq1n'
    (fun T h1 h2 => orbit_smallT hqpos hmono hΔpos hΔeq hΔup hΔlo h1 h2)
    (fun T h1 h2 => orbit_bigT hqpos hmono hΔpos hΔeq hΔup hΔlo hbest hn1 h1 h2)
    hclow hTn m hmem

end

end Work.TMC16Core.Core
