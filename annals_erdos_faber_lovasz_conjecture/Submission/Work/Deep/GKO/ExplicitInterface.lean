import Submission.Work.Deep.GKO.Defs
import Submission.Work.Deep.GKO.Combine
import Submission.Work.Deep.GKO.gkoStatementTau_of_KOExplicit

/-!
# The explicit-threshold interface for Theorem 10.8

Two ways of reading the Kühn–Osthus theorem are equivalent:

* `Work.Deep.GKO.KOStatement` — the existential form: for every `α > 0` there is a
  robustness threshold `τ > 0`;
* `Work.Deep.GKO.KOStatementExplicit τ` — the same theorem with a *named* threshold
  function `τ`.

`Work.Deep.GKO.exists_KOStatementExplicit_of_KO` extracts an explicit `τ` (with
`0 < τ α ≤ 1` for `α ∈ (0,1)`) from the existential form, and
`Work.Deep.GKO.gkoStatementExplicit_of_KOExplicit` turns it into the explicit-hierarchy
form `Work.Deep.GKO.GKOStatementExplicit τ` of Theorem 10.8.

The point of the explicit form is that a consumer (e.g. §12 of the paper) can then *check* its
own concrete numerical margins against a named hierarchy, instead of being handed an
existential threshold it cannot instantiate.  The price is that one must know something about
`τ` — for the existential form of Theorem 10.8 this information is exactly what is being
hidden by the existential quantifier.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

open scoped BigOperators

namespace Work.Deep.GKO

open ErdosFaberLovaszConjecture

noncomputable section

/-- **Explicit Theorem 10.8 from explicit Kühn–Osthus.**  This is the form of Theorem 10.8 in
which the consumer knows the hierarchy it has to meet. -/
theorem gkoStatementExplicit_of_KOExplicit (τ : ℝ → ℝ)
    (hτ1 : ∀ α : ℝ, 0 < α → α < 1 → 0 < τ α)
    (hτ2 : ∀ α : ℝ, 0 < α → α < 1 → τ α ≤ 1) (hKO : KOStatementExplicit τ) :
    GKOStatementExplicit τ :=
  gkoStatementTau_of_KOExplicit τ hτ1 hτ2 hKO

/-- **The existential and explicit forms of Kühn–Osthus are equivalent.**  From the
existential `KOStatement` one extracts a threshold function `τ` with `0 < τ α ≤ 1` on `(0,1)`
such that the explicit form `KOStatementExplicit τ` holds. -/
theorem exists_KOStatementExplicit_of_KO (hKO : KOStatement) :
    ∃ τ : ℝ → ℝ, (∀ α : ℝ, 0 < α → α < 1 → 0 < τ α) ∧
      (∀ α : ℝ, 0 < α → α < 1 → τ α ≤ 1) ∧ KOStatementExplicit τ := by
  classical
  set τ : ℝ → ℝ :=
    fun α => if h : 0 < α then min (Classical.choose (hKO α h)) 1 else 1 with hτdef
  have hτmin : ∀ α (hα : 0 < α), τ α = min (Classical.choose (hKO α hα)) (1 : ℝ) := by
    intro α hα
    rw [hτdef]
    exact dif_pos hα
  have hnone : ∀ α, ¬ 0 < α → τ α = 1 := by
    intro α hα
    rw [hτdef]
    exact dif_neg hα
  refine ⟨τ, ?_, ?_, ?_⟩
  · intro α hα _
    have hpos : (0 : ℝ) < Classical.choose (hKO α hα) :=
      (Classical.choose_spec (hKO α hα)).1
    rw [hτmin α hα]
    exact lt_min hpos (by norm_num)
  · intro α hα _
    by_cases hpos : 0 < α
    · rw [hτmin α hpos]
      exact min_le_right (Classical.choose (hKO α hpos)) (1 : ℝ)
    · rw [hnone α hpos]
  · intro α hα ν hν hντ
    obtain ⟨hpos, hall⟩ := Classical.choose_spec (hKO α hα)
    have hντ' : ν ≤ Classical.choose (hKO α hα) := by
      refine le_trans hντ ?_
      rw [hτmin α hα]
      exact min_le_left (Classical.choose (hKO α hα)) (1 : ℝ)
    obtain ⟨n₀, hn₀⟩ := hall ν hν hντ'
    refine ⟨n₀, ?_⟩
    intro n hn G hG r hr hrn hre
    refine hn₀ n hn G (robustExpander_mono_tau ?_ hG) r hr hrn hre
    rw [hτmin α hα]
    exact min_le_left (Classical.choose (hKO α hα)) (1 : ℝ)

/-- **The linear hierarchy does not imply the explicit one.**  For every threshold function
`τ ≤ 1` on `(0,1)` there are `ν, ε, p` satisfying the *linear* hierarchy
`10 ^ 10 * (ν + ε) ≤ p` of `ErdosFaberLovaszConjecture.GKOStatement` while violating the
explicit hierarchy `Work.Deep.GKO.GKOExplicitHierarchy τ ν ε p` of Theorem 10.8 (witness
`p = 10^-6`, `ν = ε = 10^-17`: the linear hierarchy allows `ν ≈ p/10^10`, while
`GKOExplicitHierarchy` needs `ν ≤ α p^2 τ(α)^2 / 14336 ≤ p^3 / 28672 ≈ 3.5·10^-23`).  The
threshold function is assumed to satisfy `0 < τ α ≤ 1`, as it does in
`gkoStatementExplicit_of_KOExplicit`.

This is the formal reason why the linear form of Theorem 10.8 cannot be obtained from
`KOStatement` through the reduction of `gkoStatementTau_of_KOExplicit` (nor through any
reduction of the same shape): the hypothesis `ν, ε ≲ p/10^10` is far weaker than the
hierarchy `ν ≲ α p^2 τ(α)^2`, `ε ≲ p τ(α)` that the pseudorandom route forces. -/
theorem linearHierarchy_not_explicitHierarchy {τ : ℝ → ℝ}
    (hτ1 : ∀ α : ℝ, 0 < α → α < 1 → 0 < τ α)
    (hτ2 : ∀ α : ℝ, 0 < α → α < 1 → τ α ≤ 1) :
    ∃ ν ε p : ℝ, 0 < ν ∧ 0 < ε ∧ ε < p ∧ p < 1 ∧ 10 ^ 10 * (ν + ε) ≤ p ∧
      ¬ Work.Deep.GKO.GKOExplicitHierarchy τ ν ε p := by
  refine ⟨(1 / 10 ^ 6) / 10 ^ 11, (1 / 10 ^ 6) / 10 ^ 11, 1 / 10 ^ 6,
    by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, ?_⟩
  intro h
  have hν := h.1
  have hτsq : (τ (min ((1 : ℝ) / 10 ^ 6 / 2) (1 / 10))) ^ 2 ≤ 1 := by
    have h1 := hτ1 (min ((1 : ℝ) / 10 ^ 6 / 2) (1 / 10))
      (lt_min (by norm_num) (by norm_num)) (by norm_num)
    have h2 := hτ2 (min ((1 : ℝ) / 10 ^ 6 / 2) (1 / 10))
      (lt_min (by norm_num) (by norm_num)) (by norm_num)
    nlinarith [h1, h2]
  have hαle : min ((1 : ℝ) / 10 ^ 6 / 2) (1 / 10) ≤ (1 : ℝ) / 10 ^ 6 / 2 := min_le_left _ _
  have hα0 : (0 : ℝ) ≤ min ((1 : ℝ) / 10 ^ 6 / 2) (1 / 10) :=
    (lt_min (by norm_num) (by norm_num)).le
  have hA : min ((1 : ℝ) / 10 ^ 6 / 2) (1 / 10) * ((1 : ℝ) / 10 ^ 6) ^ 2
        * (τ (min ((1 : ℝ) / 10 ^ 6 / 2) (1 / 10))) ^ 2 / 14336
      < (1 / 10 ^ 6) / 10 ^ 11 := by
    nlinarith [hαle, hα0, hτsq]
  have hmin : min (min (min ((1 : ℝ) / 10 ^ 6 / 2) (1 / 10) * ((1 : ℝ) / 10 ^ 6) ^ 2
        * (τ (min ((1 : ℝ) / 10 ^ 6 / 2) (1 / 10))) ^ 2 / 14336)
        ((min ((1 : ℝ) / 10 ^ 6 / 2) (1 / 10)) ^ 3 / 2240000))
        (min ((1 : ℝ) / 10 ^ 6 / 2) (1 / 10) * ((1 : ℝ) / 10 ^ 6) ^ 2 / 2240000)
      < (1 / 10 ^ 6) / 10 ^ 11 :=
    lt_of_le_of_lt (le_trans (min_le_left _ _) (min_le_left _ _)) hA
  linarith [hν, hmin]

end

end Work.Deep.GKO
