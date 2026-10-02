import Submission.Work.Deep.GKO.Defs
import Submission.Work.Deep.GKO.ExplicitInterface
import Submission.Work.Deep.GKO.corollary_10_13_odd_from_fixed

/-!
# Theorem 10.8 with *named* thresholds, and what the linear hierarchy needs

The paper's Theorem 10.8 reads `0 < 1/n₀ ≪ ν, ε ≪ p < 1`: for every `p` there are thresholds
`ν₀(p), ε₀(p)`, and `n₀` may depend on `ν, ε, p` as well.  `Work.Deep.GKO.GKOStatementFixed`
records this faithfully with *existential* thresholds; the version used by the final assembly,
`ErdosFaberLovaszConjecture.GKOStatement`, instead imposes the *linear* hierarchy
`10^10 (ν + ε) ≤ p`.

This module isolates the difference.

* `Work.Deep.GKO.GKOStatementQuantitative ν₀ ε₀` is the faithful statement with the thresholds
  `ν₀, ε₀` supplied as functions of `p`.
* `Work.Deep.GKO.gkoNu₀ τ`, `Work.Deep.GKO.gkoEps₀ τ` are the two explicit thresholds that the
  formalised reduction from Kühn–Osthus' theorem with explicit robustness threshold `τ`
  (`Work.Deep.GKO.gkoStatementTau_of_KOExplicit`) actually produces.
* `Work.Deep.GKO.gkoStatement_of_quantitative` shows that the linear form follows from the
  quantitative one as soon as `ν₀ p ≥ p/10^10` and `ε₀ p ≥ p/10^10` — this is the *exact*
  numerical demand the assembly makes on the deep input.
* `Work.Deep.GKO.linearHierarchy_requires_large_p` shows that the explicit thresholds produced
  by the formalised reduction *cannot* meet that demand for small `p`: whenever `ν` satisfies
  both `gkoNu₀ τ p` and the linear hierarchy, necessarily `p ≥ 1/1000`.  (The reduction's
  threshold is `ν₀(p) ≈ p^3 τ(p/2)^2`; the linear hierarchy wants `ν₀(p) ≥ p/10^10`, which is
  impossible for `p` below `≈ 1.7 · 10^{-3}` even with `τ ≡ 1`.)

## Main definitions and results

* `Work.Deep.GKO.GKOStatementQuantitative`
* `Work.Deep.GKO.gkoStatementQuantitative_thresholds_of_KOExplicit`
* `Work.Deep.GKO.gkoStatement_of_quantitative`
* `Work.Deep.GKO.gkoStatementFixed_of_quantitative`
* `Work.Deep.GKO.linearHierarchy_requires_large_p`
-/

set_option autoImplicit false
set_option linter.unusedVariables false

open scoped BigOperators

namespace Work.Deep.GKO

open ErdosFaberLovaszConjecture

noncomputable section

/-! ## The explicit thresholds of the reduction -/

/-- The bound on the discrepancy `ν` used by the formalised reduction from the explicit-threshold
Kühn–Osthus theorem: `ν ≤ ν₀(p)` with `ν₀(p)` as in `GKOExplicitHierarchy`. -/
def gkoNu₀ (τ : ℝ → ℝ) (p : ℝ) : ℝ :=
  let α := min (p / 2) (1 / 10)
  min (min (α * p ^ 2 * (τ α) ^ 2 / 14336) (α ^ 3 / 2240000)) (α * p ^ 2 / 2240000)

/-- The bound on the regularity parameter `ε` used by the formalised reduction from the
explicit-threshold Kühn–Osthus theorem: `ε ≤ ε₀(p)` with `ε₀(p)` as in `GKOExplicitHierarchy`. -/
def gkoEps₀ (τ : ℝ → ℝ) (p : ℝ) : ℝ :=
  let α := min (p / 2) (1 / 10)
  min (min (p * (τ α) / 16) (α / 200)) (min (p / 200) ((τ α) / 2))

/-- `GKOExplicitHierarchy τ ν ε p` is exactly the pair of inequalities
`ν ≤ gkoNu₀ τ p`, `ε ≤ gkoEps₀ τ p`. -/
theorem gkoExplicitHierarchy_iff (τ : ℝ → ℝ) (ν ε p : ℝ) :
    GKOExplicitHierarchy τ ν ε p ↔ ν ≤ gkoNu₀ τ p ∧ ε ≤ gkoEps₀ τ p := Iff.rfl

/-! ## Theorem 10.8 with named thresholds -/

/-- **Theorem 10.8 of the paper with *given* thresholds.**  For functions `ν₀, ε₀ : ℝ → ℝ`
(thought of as the thresholds the paper's `≪` hides), the conclusion of Theorem 10.8 holds for
all `0 < ν ≤ ν₀ p`, `0 < ε ≤ ε₀ p` and large `n`. -/
def GKOStatementQuantitative (ν₀ ε₀ : ℝ → ℝ) : Prop :=
  ∀ p : ℝ, 0 < p → p < 1 → ∀ ν ε : ℝ, 0 < ν → ν ≤ ν₀ p → 0 < ε → ε ≤ ε₀ p → ∃ N₀ : ℕ,
    ∀ n ≥ N₀, ∀ 𝓖 : ErdosFaberLovaszConjecture.Hypergraph (Fin n),
      (∀ e ∈ 𝓖, ErdosFaberLovaszConjecture.edgeSize e = 2) →
      ErdosFaberLovaszConjecture.SelfLowerRegular 𝓖 Set.univ p ε →
      (∀ v : Fin n, ((ErdosFaberLovaszConjecture.hypergraphMaxDegree 𝓖 : ℝ) -
        (ErdosFaberLovaszConjecture.degAt 𝓖 v : ℝ)) ≤ ν * (n : ℝ)) →
      Even n →
      (∃ w : Fin n, (∀ v : Fin n, ErdosFaberLovaszConjecture.degAt 𝓖 w ≤
          ErdosFaberLovaszConjecture.degAt 𝓖 v) ∧
        ((ErdosFaberLovaszConjecture.hypergraphMaxDegree 𝓖 : ℝ) -
            (ErdosFaberLovaszConjecture.degAt 𝓖 w : ℝ)) ≤
          ∑ v ∈ (Finset.univ.erase w),
            ((ErdosFaberLovaszConjecture.hypergraphMaxDegree 𝓖 : ℝ) -
              (ErdosFaberLovaszConjecture.degAt 𝓖 v : ℝ))) →
      ErdosFaberLovaszConjecture.Hypergraph.Colorable
        (ErdosFaberLovaszConjecture.hypergraphMaxDegree 𝓖) 𝓖

/-- The thresholds of `GKOStatementQuantitative` are the two bounds appearing in
`GKOStatementFixed`, hoisted out as functions. -/
theorem gkoStatementFixed_of_quantitative {ν₀ ε₀ : ℝ → ℝ}
    (hν₀ : ∀ p : ℝ, 0 < p → p < 1 → 0 < ν₀ p) (hε₀ : ∀ p : ℝ, 0 < p → p < 1 → 0 < ε₀ p)
    (hε₀p : ∀ p : ℝ, 0 < p → p < 1 → ε₀ p ≤ p) (h : GKOStatementQuantitative ν₀ ε₀) :
    GKOStatementFixed := by
  intro p hp0 hp1
  exact ⟨ν₀ p, ε₀ p, hν₀ p hp0 hp1, hε₀ p hp0 hp1, hε₀p p hp0 hp1,
    fun ν ε hν hνle hε hεle => h p hp0 hp1 ν ε hν hνle hε hεle⟩

/-- **What the linear hierarchy demands of the thresholds.**  `GKOStatementLinear` (*the linear*
*hierarchy* `10^10 (ν+ε) ≤ p` — the cone switched `GKOStatement` itself to the faithful form on
2026-09-23, so this is now the separately named linear form) follows from the quantitative form as
soon as the thresholds dominate `p/10^10` on `(0,1)`.  These two inequalities are the
exact numerical requirement on the deep input: the paper's proof supplies
`ν₀(p) ≈ p^3 τ(p/2)^2`, `ε₀(p) ≈ p τ(p/2)`, which fail them for small `p`
(`Work.Deep.GKO.linearHierarchy_requires_large_p`). -/
theorem gkoStatement_of_quantitative {ν₀ ε₀ : ℝ → ℝ}
    (hν : ∀ p : ℝ, 0 < p → p < 1 → p / 10 ^ 10 ≤ ν₀ p)
    (hε : ∀ p : ℝ, 0 < p → p < 1 → p / 10 ^ 10 ≤ ε₀ p)
    (h : GKOStatementQuantitative ν₀ ε₀) : GKOStatementLinear := by
  intro ν ε p hν0 hε0 hεp hp1 hlin
  have hp0 : 0 < p := lt_trans hε0 hεp
  have hνle : ν ≤ p / 10 ^ 10 := by
    have h1 : ν + ε ≤ p / 10 ^ 10 := by
      rw [le_div_iff₀ (by norm_num : (0 : ℝ) < 10 ^ 10)]
      linarith
    linarith
  have hεle : ε ≤ p / 10 ^ 10 := by
    have h1 : ν + ε ≤ p / 10 ^ 10 := by
      rw [le_div_iff₀ (by norm_num : (0 : ℝ) < 10 ^ 10)]
      linarith
    linarith
  obtain ⟨N₀, hN₀⟩ :=
    h p hp0 hp1 ν ε hν0 (le_trans hνle (hν p hp0 hp1)) hε0 (le_trans hεle (hε p hp0 hp1))
  exact ⟨N₀, fun n hn => hN₀ n hn⟩

/-- **The explicit-threshold Kühn–Osthus theorem yields the quantitative form of Theorem 10.8**
with the thresholds `gkoNu₀ τ`, `gkoEps₀ τ` that the formalised reduction actually produces. -/
theorem gkoStatementQuantitative_thresholds_of_KOExplicit (τ : ℝ → ℝ)
    (hτ1 : ∀ α : ℝ, 0 < α → α < 1 → 0 < τ α)
    (hτ2 : ∀ α : ℝ, 0 < α → α < 1 → τ α ≤ 1) (hKO : KOStatementExplicit τ) :
    GKOStatementQuantitative (gkoNu₀ τ) (gkoEps₀ τ) := by
  intro p hp0 hp1 ν ε hν hν₀ hε hε₀
  have hεp : ε < p := by
    have h1 : ε ≤ gkoEps₀ τ p := hε₀
    have h2 : gkoEps₀ τ p ≤ p / 200 := by
      dsimp only [gkoEps₀]
      exact le_trans (min_le_right _ _) (min_le_left _ _)
    linarith
  exact gkoStatementTau_of_KOExplicit τ hτ1 hτ2 hKO ν ε p hν hε hεp hp1 ⟨hν₀, hε₀⟩

/-- **Corollary 10.13 with named thresholds.**  A thin wrapper around
`Work.Deep.GKO.corollary_10_13_from_fixed`, stating the corollary for the quantitative form of
Theorem 10.8.  A consumer with concrete numbers (such as §12 of the paper) should instantiate
this rather than the existential `GKOStatementFixed`. -/
theorem corollary_10_13_of_quantitative {ν₀ ε₀ : ℝ → ℝ}
    (hν₀ : ∀ p : ℝ, 0 < p → p < 1 → 0 < ν₀ p) (hε₀ : ∀ p : ℝ, 0 < p → p < 1 → 0 < ε₀ p)
    (hε₀p : ∀ p : ℝ, 0 < p → p < 1 → ε₀ p ≤ p) (h : GKOStatementQuantitative ν₀ ε₀) :
    ∀ p : ℝ, 0 < p → p < 1 → ∃ η₀ ε₀' : ℝ, 0 < η₀ ∧ 0 < ε₀' ∧ ε₀' ≤ p ∧
      (∀ η ε : ℝ, 0 < η → η ≤ η₀ → 0 < ε → ε ≤ ε₀' → ∃ N₀ : ℕ,
        ∀ n ≥ N₀, ∀ 𝓖 : ErdosFaberLovaszConjecture.Hypergraph (Fin n),
        (∀ e ∈ 𝓖, ErdosFaberLovaszConjecture.edgeSize e = 2) →
        ErdosFaberLovaszConjecture.SelfLowerRegular 𝓖 Set.univ p ε →
        (∀ v : Fin n, ((ErdosFaberLovaszConjecture.hypergraphMaxDegree 𝓖 : ℝ) -
          (ErdosFaberLovaszConjecture.degAt 𝓖 v : ℝ)) ≤ η * (n : ℝ)) →
        (({v : Fin n | ErdosFaberLovaszConjecture.degAt 𝓖 v <
          ErdosFaberLovaszConjecture.hypergraphMaxDegree 𝓖}.ncard : ℝ) ≥
          (ErdosFaberLovaszConjecture.hypergraphMaxDegree 𝓖 : ℝ)) →
        𝓖.Colorable (ErdosFaberLovaszConjecture.hypergraphMaxDegree 𝓖)) :=
  corollary_10_13_from_fixed (gkoStatementFixed_of_quantitative hν₀ hε₀ hε₀p h)

/-! ## The numerical obstruction for the linear hierarchy -/

/-- **The linear hierarchy cannot be met by the explicit thresholds for small `p`.**  If `ν` lies
below the threshold `gkoNu₀ τ p` produced by the formalised reduction (with `τ α ≤ 1`) and also
above the linear hierarchy's `p/10^10`, then `p ≥ 1/1000`.

Indeed `gkoNu₀ τ p ≤ (p/2) p^2 / 14336 = p^3/28672`, so `p/10^10 ≤ p^3/28672` forces
`p^2 ≥ 28672/10^10 ≈ 2.87·10^{-6}`, i.e. `p ≥ 1.69·10^{-3}`.

Consequently `ErdosFaberLovaszConjecture.GKOStatement` is *not* a consequence of the
explicit-threshold Kühn–Osthus theorem with a uniform bound on `τ`: for `p` below `1/1000` the
linear hierarchy contradicts the threshold produced by the reduction. -/
theorem linearHierarchy_requires_large_p {τ : ℝ → ℝ}
    (hτ1 : ∀ α : ℝ, 0 < α → α < 1 → 0 < τ α)
    (hτ2 : ∀ α : ℝ, 0 < α → α < 1 → τ α ≤ 1)
    {p ν : ℝ} (hp0 : 0 < p) (hp : p ≤ 1 / 5) (hν : p / 10 ^ 10 ≤ ν) (h : ν ≤ gkoNu₀ τ p) :
    (1 : ℝ) / 1000 ≤ p := by
  have hα : min (p / 2) (1 / 10) = p / 2 := by
    exact min_eq_left (by linarith)
  have hαpos : 0 < min (p / 2) (1 / 10) := lt_min (by linarith) (by norm_num)
  have hαlt1 : min (p / 2) (1 / 10) < 1 :=
    lt_of_le_of_lt (min_le_right _ _) (by norm_num)
  have hτpos : 0 < τ (min (p / 2) (1 / 10)) := hτ1 _ hαpos hαlt1
  have hτle : τ (min (p / 2) (1 / 10)) ≤ 1 := hτ2 _ hαpos hαlt1
  dsimp only [gkoNu₀] at h
  rw [hα] at h hτpos hτle
  have h1 : ν ≤ (p / 2) * p ^ 2 * (τ (p / 2)) ^ 2 / 14336 :=
    le_trans h (le_trans (min_le_left _ _) (min_le_left _ _))
  have h2 : (τ (p / 2)) ^ 2 ≤ 1 := by nlinarith [hτpos, hτle]
  have h3 : ν ≤ p ^ 3 / 28672 := by
    have h4 : (p / 2) * p ^ 2 * (τ (p / 2)) ^ 2 / 14336 ≤ (p / 2) * p ^ 2 / 14336 := by
      have h5 : (0 : ℝ) ≤ (p / 2) * p ^ 2 / 14336 := by positivity
      nlinarith [h2, h5]
    have h6 : (p / 2) * p ^ 2 / 14336 = p ^ 3 / 28672 := by ring
    linarith [h1, h4, h6.le, h6.ge]
  have h7 : p ^ 2 ≥ 28672 / 10 ^ 10 := by nlinarith [hν, h3, hp0]
  nlinarith [h7, hp0]

end

end Work.Deep.GKO
