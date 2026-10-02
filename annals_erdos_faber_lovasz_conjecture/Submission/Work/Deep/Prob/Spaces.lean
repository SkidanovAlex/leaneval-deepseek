/-
# Concrete finite probability spaces

The sampling spaces that the concentration and nibble layers run on:

* `FinProbSpace.uniform` — the uniform measure on a nonempty finite type,
* `FinProbSpace.uniformColouring` — the uniform measure on `Fin n → Fin k` (random
  colourings), atom probability `1 / k ^ n`,
* `FinProbSpace.bernoulli` — the product measure on `ι → Bool` where coordinate `i` is
  `true` with probability `q i`, atom probability `∏ i, (if s i then q i else 1 - q i)`, and
  its constant-parameter version `bernoulliConst`,
* `FinProbSpace.uniformOn` — the uniform measure on a nonempty `Finset`,
* `FinProbSpace.cond` — conditioning a finite probability space on a positive-probability
  event.

All the definitions are here; the lemmas about them (atom probabilities, independence of
coordinates, expectations of coordinate sums) live in separate modules that import this one.
-/
import Submission.Work.Deep.Prob.Basic
import Submission.Commons.Probability.Chernoff.chernoff_two_sided_finite_weighted

set_option autoImplicit false

open scoped BigOperators
open Finset

namespace Work.Deep.Prob

namespace FinProbSpace

variable {Ω : Type*} [Fintype Ω]

/-- The uniform probability measure on a nonempty finite type. -/
noncomputable def uniform (Ω : Type*) [Fintype Ω] [Nonempty Ω] : FinProbSpace Ω where
  mass _ := (Fintype.card Ω : ℝ)⁻¹
  mass_nonneg _ := by positivity
  mass_sum := by
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    have h : (Fintype.card Ω : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
    field_simp

@[simp]
theorem uniform_mass [Nonempty Ω] (ω : Ω) :
    (uniform Ω).mass ω = (Fintype.card Ω : ℝ)⁻¹ := rfl

/-- The uniform measure on the set of colourings `Fin n → Fin k` of a set of `n` vertices
with `k ≥ 1` colours. -/
noncomputable def uniformColouring (n k : ℕ) (hk : 0 < k) : FinProbSpace (Fin n → Fin k) :=
  letI : Nonempty (Fin n → Fin k) := ⟨fun _ => ⟨0, hk⟩⟩
  uniform (Fin n → Fin k)

@[simp]
theorem uniformColouring_mass {n k : ℕ} {hk : 0 < k} (σ : Fin n → Fin k) :
    (uniformColouring n k hk).mass σ = ((Fintype.card (Fin n → Fin k) : ℕ) : ℝ)⁻¹ := rfl

/-- The product measure on `ι → Bool`: coordinate `i` is `true` with probability `q i`. -/
noncomputable def bernoulli {ι : Type*} [Fintype ι] [DecidableEq ι] (q : ι → ℝ)
    (hq0 : ∀ i, 0 ≤ q i) (hq1 : ∀ i, q i ≤ 1) : FinProbSpace (ι → Bool) where
  mass s := ∏ i, if s i then q i else 1 - q i
  mass_nonneg s := Finset.prod_nonneg fun i _ => by
    by_cases h : s i = true
    · rw [if_pos h]; exact hq0 i
    · rw [if_neg h]; linarith [hq1 i]
  mass_sum := Commons.Probability.Chernoff.sum_weight_eq_one q

/-- The product measure on `ι → Bool` with constant inclusion probability `p`. -/
noncomputable def bernoulliConst {ι : Type*} [Fintype ι] [DecidableEq ι] (p : ℝ)
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) : FinProbSpace (ι → Bool) :=
  bernoulli (fun _ => p) (fun _ => hp0) (fun _ => hp1)

@[simp]
theorem bernoulli_mass {ι : Type*} [Fintype ι] [DecidableEq ι] {q : ι → ℝ}
    {hq0 : ∀ i, 0 ≤ q i} {hq1 : ∀ i, q i ≤ 1} (s : ι → Bool) :
    (bernoulli q hq0 hq1).mass s = ∏ i, if s i then q i else 1 - q i := rfl

@[simp]
theorem bernoulliConst_mass {ι : Type*} [Fintype ι] [DecidableEq ι] {p : ℝ}
    {hp0 : 0 ≤ p} {hp1 : p ≤ 1} (s : ι → Bool) :
    (bernoulliConst p hp0 hp1).mass s = ∏ _i : ι, if s _i then p else 1 - p := rfl

/-- The uniform measure on a nonempty finite set. -/
noncomputable def uniformOn [DecidableEq Ω] (A : Finset Ω) (hA : A.Nonempty) : FinProbSpace Ω where
  mass ω := if ω ∈ A then (A.card : ℝ)⁻¹ else 0
  mass_nonneg ω := by
    by_cases h : ω ∈ A
    · rw [if_pos h]; positivity
    · rw [if_neg h]
  mass_sum := by
    have hcard : (A.card : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hA.card_pos.ne'
    rw [← Finset.sum_filter]
    have hfilter : (Finset.univ.filter fun ω => ω ∈ A) = A := by
      ext ω; simp
    rw [hfilter, Finset.sum_const, nsmul_eq_mul]
    field_simp

@[simp]
theorem uniformOn_mass [DecidableEq Ω] (A : Finset Ω) (hA : A.Nonempty) (ω : Ω) :
    (uniformOn A hA).mass ω = if ω ∈ A then (A.card : ℝ)⁻¹ else 0 := rfl

/-- Conditioning a finite probability space on a positive-probability event. -/
noncomputable def cond (P : FinProbSpace Ω) (B : Set Ω) (hB : 0 < P.prob B) :
    FinProbSpace Ω where
  mass ω := B.indicator P.mass ω / P.prob B
  mass_nonneg ω := div_nonneg (ind_nonneg P B ω) hB.le
  mass_sum := by
    rw [← Finset.sum_div]
    exact div_self (ne_of_gt hB)

@[simp]
theorem cond_mass (P : FinProbSpace Ω) (B : Set Ω) (hB : 0 < P.prob B) (ω : Ω) :
    (cond P B hB).mass ω = B.indicator P.mass ω / P.prob B := rfl

end FinProbSpace

end Work.Deep.Prob
