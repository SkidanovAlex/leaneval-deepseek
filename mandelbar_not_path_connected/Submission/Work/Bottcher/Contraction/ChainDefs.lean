/-
# The inverse-branch pullback chain for the quartic `pMap c`

This file sets up the *combinatorial* backbone of the inverse Böttcher coordinate
`exists_inverseBottcher_of_mem_mandelbar`:

* `preim1 c u`, `preim2 c u`, `preim3 c u`, `preim4 c u` are the four explicit preimages of `u`
  under the monic quartic `pMap c` (`Contraction.preimage_pMap_eq_iff`), and
  `preimages c u` is the finite set of them;
* `closestPreimage c u a` is the preimage of `u` closest to the *anchor* `a`; it is a genuine
  preimage (`closestPreimage_pMap`) and it is minimal (`closestPreimage_le`);
* `chainPrefix c ψ R w N` is the value obtained by starting from `ψ (w ^ 4 ^ N)` and pulling back
  `N` times, using at level `k` the preimage closest to the anchor `w ^ (4 ^ k)`.

The analytic content (existence of `ψ` on the far region, estimates, convergence of
`chainPrefix` as `N → ∞`, continuity of the limit) is proved elsewhere; this file only contains
the definitions and the elementary facts about them.
-/
import Mathlib
import Submission.Work.Bottcher.Defs
import Submission.Work.Bottcher.Contraction.preimage_pMap_eq_iff

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


open Filter Function
open scoped Topology ComplexConjugate

namespace Work.Bottcher.Contraction

open LeanEval.ComplexAnalysis (Tantibar)

noncomputable section

variable (c : ℂ)

/-! ## The four explicit preimages -/

/-- The first of the four preimages of `u` under `pMap c`. -/
def preim1 (c u : ℂ) : ℂ := Complex.sqrt (Complex.sqrt (u - c) - conj c)

/-- The second preimage: the negative of the first. -/
def preim2 (c u : ℂ) : ℂ := -preim1 c u

/-- The third preimage (the "other branch" of the outer square root). -/
def preim3 (c u : ℂ) : ℂ := Complex.sqrt (-(Complex.sqrt (u - c)) - conj c)

/-- The fourth preimage: the negative of the third. -/
def preim4 (c u : ℂ) : ℂ := -preim3 c u

theorem pMap_preim1 (u : ℂ) : Work.Bottcher.pMap c (preim1 c u) = u := by
  show Work.Bottcher.pMap c (Complex.sqrt (Complex.sqrt (u - c) - conj c)) = u
  exact (preimage_pMap_eq_iff c u _).mpr (Or.inl rfl)

theorem pMap_preim3 (u : ℂ) : Work.Bottcher.pMap c (preim3 c u) = u := by
  rw [show preim3 c u = Complex.sqrt (-(Complex.sqrt (u - c)) - conj c) from rfl]
  exact (preimage_pMap_eq_iff c u _).mpr (Or.inr (Or.inr (Or.inl rfl)))

/-- **Every** preimage of `u` under `pMap c` is one of the four explicit ones. -/
theorem eq_preim_of_pMap_eq {u z : ℂ} (h : Work.Bottcher.pMap c z = u) :
    z = preim1 c u ∨ z = preim2 c u ∨ z = preim3 c u ∨ z = preim4 c u := by
  rcases (preimage_pMap_eq_iff c u z).mp h with h1 | h2 | h3 | h4
  · exact Or.inl h1
  · exact Or.inr (Or.inl (by rw [preim2, preim1, h2]))
  · exact Or.inr (Or.inr (Or.inl h3))
  · exact Or.inr (Or.inr (Or.inr (by rw [preim4, preim3, h4])))

/-! ## The closest preimage -/

/-- The preimage of `u` under `pMap c` closest to the anchor `a` (decision tree). -/
def closestPreimage (c u a : ℂ) : ℂ :=
  if ‖preim1 c u - a‖ ≤ ‖preim2 c u - a‖ then
    if ‖preim1 c u - a‖ ≤ ‖preim3 c u - a‖ then
      if ‖preim1 c u - a‖ ≤ ‖preim4 c u - a‖ then preim1 c u else preim4 c u
    else
      if ‖preim3 c u - a‖ ≤ ‖preim4 c u - a‖ then preim3 c u else preim4 c u
  else
    if ‖preim2 c u - a‖ ≤ ‖preim3 c u - a‖ then
      if ‖preim2 c u - a‖ ≤ ‖preim4 c u - a‖ then preim2 c u else preim4 c u
    else
      if ‖preim3 c u - a‖ ≤ ‖preim4 c u - a‖ then preim3 c u else preim4 c u

theorem pMap_preim2 (u : ℂ) : Work.Bottcher.pMap c (preim2 c u) = u :=
  (preimage_pMap_eq_iff c u _).mpr (Or.inr (Or.inl rfl))

theorem pMap_preim4 (u : ℂ) : Work.Bottcher.pMap c (preim4 c u) = u :=
  (preimage_pMap_eq_iff c u _).mpr (Or.inr (Or.inr (Or.inr rfl)))

theorem closestPreimage_pMap (u a : ℂ) :
    Work.Bottcher.pMap c (closestPreimage c u a) = u := by
  unfold closestPreimage
  split_ifs
  · exact pMap_preim1 c u
  · exact pMap_preim4 c u
  · exact pMap_preim3 c u
  · exact pMap_preim4 c u
  · exact pMap_preim2 c u
  · exact pMap_preim4 c u
  · exact pMap_preim3 c u
  · exact pMap_preim4 c u

/-- **Minimality** of `closestPreimage` among the four preimages. -/
theorem closestPreimage_le_preim (u a : ℂ) :
    ‖closestPreimage c u a - a‖ ≤ ‖preim1 c u - a‖ ∧
    ‖closestPreimage c u a - a‖ ≤ ‖preim2 c u - a‖ ∧
    ‖closestPreimage c u a - a‖ ≤ ‖preim3 c u - a‖ ∧
    ‖closestPreimage c u a - a‖ ≤ ‖preim4 c u - a‖ := by
  unfold closestPreimage
  split_ifs <;> refine ⟨?_, ?_, ?_, ?_⟩ <;> simp_all <;> linarith

/-- **Minimality** of `closestPreimage`: it is at least as close to the anchor as any preimage. -/
theorem closestPreimage_le {u a z : ℂ} (h : Work.Bottcher.pMap c z = u) :
    ‖closestPreimage c u a - a‖ ≤ ‖z - a‖ := by
  rcases eq_preim_of_pMap_eq c h with h1 | h2 | h3 | h4
  · rw [h1]; exact (closestPreimage_le_preim c u a).1
  · rw [h2]; exact (closestPreimage_le_preim c u a).2.1
  · rw [h3]; exact (closestPreimage_le_preim c u a).2.2.1
  · rw [h4]; exact (closestPreimage_le_preim c u a).2.2.2

/-! ## The pullback chain -/

/-- The anchor of level `k` of the orbit of `w`: `w ^ (4 ^ k)`. -/
def level (w : ℂ) (k : ℕ) : ℂ := w ^ (4 ^ k)

/-- Raw pullback sequence: start from the target value `z₀` at level `N`, pull back `n` times
using the anchors `w ^ (4 ^ (N-1))`, ..., `w ^ (4 ^ (N-n))`. -/
def pullback (c w : ℂ) (z₀ : ℂ) : ℕ → ℕ → ℂ
  | 0, _N => z₀
  | (n + 1), N => closestPreimage c (pullback c w z₀ n N) (level w (N - 1 - n))

/-- The value at level `0` of the length-`N` pullback chain of `w` starting from the far value
`ψ (w ^ (4 ^ N))`. -/
def chainPrefix (c : ℂ) (ψ : ℂ → ℂ) (w : ℂ) (N : ℕ) : ℂ :=
  pullback c w (ψ (level w N)) N N

/-- The value at level `k` of the length-`N` pullback chain of `w` (for `k ≤ N`). -/
def chainPrefixAt (c : ℂ) (ψ : ℂ → ℂ) (w : ℂ) (N k : ℕ) : ℂ :=
  pullback c w (ψ (level w N)) (N - k) N


theorem level_pow_four (w : ℂ) (m : ℕ) : level (w ^ 4) m = level w (m + 1) := by
  unfold level
  rw [← pow_mul, pow_succ, Nat.mul_comm]

/-- The pullback at one step less returns the `pMap c`-image: each chain value maps to the next. -/
theorem pMap_pullback (c w : ℂ) (z₀ : ℂ) (n N : ℕ) :
    Work.Bottcher.pMap c (pullback c w z₀ (n + 1) N) = pullback c w z₀ n N :=
  closestPreimage_pMap c _ _

/-- Same chain from `w ^ 4` with one level fewer (`M + 1` levels of `w` correspond to `M` levels
of `w ^ 4`): the anchors and the starting value coincide. -/
theorem pullback_shift_aux (c : ℂ) (w : ℂ) (z₀ : ℂ) (M : ℕ) :
    ∀ n : ℕ, n ≤ M → pullback c (w ^ 4) z₀ n M = pullback c w z₀ n (M + 1) := by
  intro n
  induction n with
  | zero => intro _; rfl
  | succ n ih =>
      intro hn
      rw [pullback, pullback]
      have h1 : pullback c (w ^ 4) z₀ n M = pullback c w z₀ n (M + 1) := ih (by omega)
      rw [h1]
      have h2 : level (w ^ 4) (M - 1 - n) = level w (M - n) := by
        rw [level_pow_four]
        congr 1
        omega
      rw [h2, show M + 1 - 1 - n = M - n by omega]

/-- **The level shift**: the level-`1` value of the `N`-chain of `w` equals the level-`0` value
of the `(N-1)`-chain of `w ^ 4`.  Consequently any limit of the chains is a semiconjugacy of
`pMap c` and `w ↦ w ^ 4`. -/
theorem chainPrefixAt_shift (c : ℂ) (ψ : ℂ → ℂ) (w : ℂ) (N : ℕ) (hN : 1 ≤ N) :
    chainPrefixAt c ψ w N 1 = chainPrefix c ψ (w ^ 4) (N - 1) := by
  unfold chainPrefixAt chainPrefix
  have hN' : N - 1 + 1 = N := by omega
  have hlev : level (w ^ 4) (N - 1) = level w N := by
    rw [level_pow_four, hN']
  rw [hlev, show N - 1 = N - 1 from rfl]
  have hN' : N - 1 + 1 = N := by omega
  simpa only [hN'] using
    (pullback_shift_aux c w (ψ (level w N)) (N - 1) (N - 1) (by omega)).symm



/-- **The recurrence**: the level-`k` chain value is the preimage of the level-`k+1` value
closest to the anchor `w ^ (4 ^ k)`.  This is the step the uniform estimate is inducted on. -/
theorem chainPrefixAt_eq_closestPreimage (c : ℂ) (ψ : ℂ → ℂ) (w : ℂ) (N k : ℕ) (hk : k < N) :
    chainPrefixAt c ψ w N k
      = closestPreimage c (chainPrefixAt c ψ w N (k + 1)) (level w k) := by
  unfold chainPrefixAt
  have hNk : N - k = (N - k - 1) + 1 := by omega
  rw [hNk, pullback]
  have h2 : N - 1 - (N - k - 1) = k := by omega
  rw [h2]
  congr 1

/-- The top of the chain is the far value. -/
theorem chainPrefixAt_self (c : ℂ) (ψ : ℂ → ℂ) (w : ℂ) (N : ℕ) :
    chainPrefixAt c ψ w N N = ψ (level w N) := by
  unfold chainPrefixAt
  rw [show N - N = 0 from by omega]
  rfl

/-- The bottom of the chain is `chainPrefix`. -/
theorem chainPrefixAt_zero (c : ℂ) (ψ : ℂ → ℂ) (w : ℂ) (N : ℕ) :
    chainPrefixAt c ψ w N 0 = chainPrefix c ψ w N := by
  unfold chainPrefixAt chainPrefix
  rw [show N - 0 = N from by omega]


end

end Work.Bottcher.Contraction
