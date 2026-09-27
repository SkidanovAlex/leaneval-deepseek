import Mathlib
import Submission.Work.EQ.CycleDefs
import Submission.Work.EQ.HeteroAlgebra
import Submission.Work.EQ.exists_analyticAt_sq_eq

/-!
# Shared definitions for `bwdP_fan_degenerate_countable`

This module contains the definitions and the purely algebraic identities used by
`Work.EQ.bwdP_fan_degenerate_countable` (the countability of the degenerate locus of backward
chains from a stable fan).

* `fanWords n` enumerates all sign lists of length `n` (`mem_fanWords` characterises membership);
* `bwdProd a h ε n w` is the product, over all levels `i ≤ n` and all sign lists `σ` of length
  `i`, of the labelled radicands `bsq (subO1 a (bwdP a σ (fan a h ε w)))`;
* `bwdProdU a h ε n u` is the same product after the substitution `w = λ^n u`, where every
  factor is a value of `fan` at a small argument;
* `bwdP_fan_eq_fan_aux` rewrites `bwdP a l (fan a h ε u)` as `fan a h (l.reverse ++ ε) (u/λ^|l|)`.
-/

namespace Work.EQ

open Filter _root_.Topology

open scoped BigOperators

noncomputable section

/-! ## Unfolding of `fan` and the backward identity -/

lemma fan_unfold_nil (a : ℝ) (h : ℂ → ℂ) (u : ℂ) : fan a h [] u = germC a h u := rfl

lemma fan_unfold_cons (a : ℝ) (h : ℂ → ℂ) (s : Bool) (ε : List Bool) (u : ℂ) :
    fan a h (s :: ε) u = invBranch a s (fan a h ε (((eqLam a : ℝ) : ℂ) * u)) := rfl

/-- **`bwdP` applied to a fan value is a fan value again.**  With `λ = eqLam a`,
`bwdP a l (fan a h ε u) = fan a h (l.reverse ++ ε) (u/λ^{|l|})`.  This is a purely algebraic
identity of the recursion defining `fan`; the only side condition is `λ ≠ 0`. -/
lemma bwdP_fan_eq_fan_aux {a : ℝ} (h : ℂ → ℂ) (hlam : ((eqLam a : ℝ) : ℂ) ≠ 0)
    (l ε : List Bool) (u : ℂ) :
    bwdP a l (fan a h ε u) =
      fan a h (l.reverse ++ ε) (u / (((eqLam a : ℝ) : ℂ) ^ l.length)) := by
  induction l generalizing ε u with
  | nil => simp [bwdP]
  | cons s₀ l' ih =>
      have h1 : bwdP a (s₀ :: l') (fan a h ε u) =
          bwdP a l' (fan a h (s₀ :: ε) (u / ((eqLam a : ℝ) : ℂ))) := by
        rw [bwdP_cons, fan_unfold_cons]
        congr 1
        field_simp
      rw [h1, ih]
      have hL : l'.reverse ++ (s₀ :: ε) = (s₀ :: l').reverse ++ ε := by
        rw [List.reverse_cons, List.append_assoc]
        congr 1
      have hR : (u / ((eqLam a : ℝ) : ℂ)) / (((eqLam a : ℝ) : ℂ) ^ l'.length)
          = u / (((eqLam a : ℝ) : ℂ) ^ (s₀ :: l').length) := by
        rw [List.length_cons, div_div, pow_succ]
        ring
      rw [hL, hR]

/-! ## Enumerating the sign lists of a given length -/

/-- All sign lists of length `n`, built by appending one symbol at a time. -/
def fanWords : ℕ → List (List Bool)
  | 0 => [[]]
  | n + 1 => (fanWords n).flatMap (fun l => [l ++ [true], l ++ [false]])

theorem mem_fanWords {n : ℕ} {σ : List Bool} : σ ∈ fanWords n ↔ σ.length = n := by
  induction n generalizing σ with
  | zero =>
      rw [show fanWords 0 = [[]] from rfl, List.mem_singleton, List.length_eq_zero_iff]
  | succ n ih =>
      rw [show fanWords (n + 1) = (fanWords n).flatMap
        (fun l => [l ++ [true], l ++ [false]]) from rfl, List.mem_flatMap]
      constructor
      · rintro ⟨l, hl, hσ⟩
        rw [ih] at hl
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hσ
        rcases hσ with hσ | hσ
        · rw [hσ, List.length_append, List.length_singleton, hl]
        · rw [hσ, List.length_append, List.length_singleton, hl]
      · intro hlen
        rcases List.eq_nil_or_concat σ with rfl | ⟨L, b, hL⟩
        · simp at hlen
        · subst hL
          have hLlen : L.length = n := by
            rw [List.length_concat] at hlen
            omega
          refine ⟨L, ih.mpr hLlen, ?_⟩
          rw [List.concat_eq_append]
          cases b <;> simp

/-! ## A chosen local analytic square root -/

/-- A chosen local analytic square root of `R` at the point `u₀`: if `R` is analytic at `u₀` and
`R u₀ ≠ 0`, this is the square root produced by `exists_analyticAt_sq_eq` (analytic at `u₀`,
nonvanishing at `u₀`, with `(rootC R u₀ u)^2 = R u` for every `u`); otherwise it is `0`. -/
noncomputable def rootC (R : ℂ → ℂ) (u₀ : ℂ) : ℂ → ℂ := by
  classical
  exact if h : AnalyticAt ℂ R u₀ ∧ R u₀ ≠ 0 then
    Classical.choose (exists_analyticAt_sq_eq h.1 h.2) else 0

/-- The defining properties of `rootC`. -/
theorem rootC_spec {R : ℂ → ℂ} {u₀ : ℂ} (hR : AnalyticAt ℂ R u₀) (h0 : R u₀ ≠ 0) :
    AnalyticAt ℂ (rootC R u₀) u₀ ∧ rootC R u₀ u₀ ≠ 0 ∧ ∀ u, (rootC R u₀ u) ^ 2 = R u := by
  have h : AnalyticAt ℂ R u₀ ∧ R u₀ ≠ 0 := ⟨hR, h0⟩
  have hval : rootC R u₀ = Classical.choose (exists_analyticAt_sq_eq hR h0) := by
    unfold rootC
    exact dite_eq_left h
  rw [hval]
  exact Classical.choose_spec (exists_analyticAt_sq_eq hR h0)

/-! ## The labelled radicand products -/

/-- The product of the labelled radicands `bsq (subO1 a (bwdP a σ (fan a h ε w)))` over all
levels `i ≤ n` and all sign lists `σ` of length `i`. -/
def bwdProd (a : ℝ) (h : ℂ → ℂ) (ε : List Bool) (n : ℕ) (w : ℂ) : ℂ :=
  ((List.range (n + 1)).map (fun i =>
    ((fanWords i).map (fun σ => bsq (subO1 a (bwdP a σ (fan a h ε w))))).prod)).prod

/-- The same product rewritten with an arbitrary family of points indexed by sign lists (used with
the local analytic sheets `su` in place of the labelled points). -/
def sheetProd (a : ℝ) (n : ℕ) (u : List Bool → ℂ × ℂ) : ℂ :=
  ((List.range (n + 1)).map (fun i =>
    ((fanWords i).map (fun σ => bsq (subO1 a (u σ)))).prod)).prod

end

end Work.EQ
