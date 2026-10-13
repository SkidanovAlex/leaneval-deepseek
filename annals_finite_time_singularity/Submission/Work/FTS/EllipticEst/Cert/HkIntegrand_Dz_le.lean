import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.Spaces.Defs
import Submission.Work.Spaces.mixed_comm
import Submission.Work.Coercivity.SumShiftZ_le
import Submission.Work.Coercivity.SumRowShift_eq

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# Pointwise domination of the `H^k`-integrand of `D_z Ψ`

This module proves the pure index-bookkeeping statement `HkIntegrand_Dz_le`: the sum of
squares making up the `H^k`-integrand of `D_z Ψ` is dominated by the `H^k`-integrands of
`Ψ` and of `D_θ Ψ` together with the two "top order" summands they do not contain.

Write `H = w/√sin(2θ)^η` and `W = Wt α` for the two weights, so that

`HkIntegrand α k f = Σ_{i≤k} (D_z^i f·H)² + Σ_{1≤i, i+j≤k} (D_z^j D_θ^i f·W)²`.

Since `D_z^i (D_z Ψ) = D_z^{i+1} Ψ` and (by commutativity of `D_z` and `D_θ` on the closed
quadrant, `Work.Spaces.mixed_comm`, available from `SmoothNbhd Ψ`)

`D_z^j D_θ^i (D_z Ψ) = D_z^{j+1} D_θ^i Ψ` on `[0,∞) × [0,π/2]`,

the radial summands of `HkIntegrand α k (D_z Ψ)` are the radial summands of `Ψ` of order
`1 ≤ i ≤ k+1`, and the mixed summands are `(D_z^{j+1}D_θ^iΨ·W)²` with `1 ≤ i`, `i+j ≤ k`.
The latter are covered as follows:

* `i ≥ 2`: they are the mixed summands of `HkIntegrand α k (D_θΨ)` under the index shift
  `(i,j) ↦ (i-1,j+1)`, since `D_z^{j+1}D_θ^{i-1}(D_θΨ) = D_z^{j+1}D_θ^iΨ`;
* `i = 1` and `j + 2 ≤ k`: they are the `(1, j+1)`-mixed summands of `HkIntegrand α k Ψ`;
* `i = 1` and `j + 1 = k`: this single summand is `(D_z^kD_θΨ·W)²`, added on the right.

The radial summand `D_z^{k+1}Ψ·H` (order `k+1`) is the other summand added on the right.
No weight comparison is needed: matching summands carry literally the same weight.

The combinatorial content of the mixed part is `Coercivity.SumShiftZ_le` (the shift
`j ↦ j+1` inside the triangle `1 ≤ i`, `i+j ≤ k+1`, valid for nonnegative terms) and
`Coercivity.SumRowShift_eq` (splitting off the row `i = 1` of that triangle).  Everything
else is the algebra of `D_z`, `D_θ` iterates.
-/

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.Cert

set_option autoImplicit false
set_option linter.unusedVariables false

/-! ## Index identities for iterated derivatives -/

/-- The pure family of the `H^k`-integrand of `D_z f` is the pure family of `f` shifted by
one: `D_z^i (D_z f) = D_z^{i+1} f`. -/
private lemma DzIter_Dz (i : ℕ) (f : ℝ → ℝ → ℝ) :
    Spaces.DzIter i (Spaces.Dz f) = Spaces.DzIter (i + 1) f := by
  rw [Spaces.DzIter_add_right]
  rfl

/-- The mixed family of the `H^k`-integrand of `D_z f` is the mixed family of `f` with the
`D_z`-order raised by one: `D_z^j D_θ^i (D_z f) = D_z^{j+1} D_θ^i f` on the closed quadrant,
by commutation of `D_z` and `D_θ`. -/
private lemma mixed_Dz (j i : ℕ) {f : ℝ → ℝ → ℝ} (hsm : Spaces.SmoothNbhd f) {z θ : ℝ}
    (hz : z ∈ Spaces.Iz) (hθ : θ ∈ Spaces.Iθ) :
    Spaces.mixed j i (Spaces.Dz f) z θ = Spaces.mixed (j + 1) i f z θ := by
  simpa using Spaces.mixed_comm f hsm j i 1 0 z θ hz hθ

/-- The mixed family of the `H^k`-integrand of `D_θ f` is the mixed family of `f` with the
`D_θ`-order raised by one: `D_z^j D_θ^i (D_θ f) = D_z^j D_θ^{i+1} f`. -/
private lemma mixed_Dth (j i : ℕ) (f : ℝ → ℝ → ℝ) :
    Spaces.mixed j i (Spaces.Dth f) = Spaces.mixed j (i + 1) f := by
  simp only [Spaces.mixed]
  have h : Spaces.Dth f = Spaces.DthIter 1 f := rfl
  rw [h, Spaces.DthIter_add_right]

/-- `D_z^k (D_θ f) = mixed k 1 f`. -/
private lemma DzIter_Dth_eq_mixed (k : ℕ) (f : ℝ → ℝ → ℝ) :
    Spaces.DzIter k (Spaces.Dth f) = Spaces.mixed k 1 f := by
  simp only [Spaces.mixed, Spaces.DthIter_succ, Spaces.DthIter_zero]

/-! ## Combinatorial lemmas -/

/-- A conditionally defined summand with nonnegative values is nonnegative. -/
private lemma ite_cond_nonneg {G : ℕ → ℕ → ℝ} (hG : ∀ a b, 0 ≤ G a b) (a b k : ℕ) :
    0 ≤ (if 1 ≤ a ∧ a + b ≤ k then G a b else 0) := by
  split_ifs with h
  · exact hG a b
  · exact le_refl 0

/-- The shifted version of `ite_cond_nonneg`: the condition still refers to the indices
`(a,b)`, but the summand is `G (a+1) b`. -/
private lemma ite_cond_nonneg_shift {G : ℕ → ℕ → ℝ} (hG : ∀ a b, 0 ≤ G a b) (a b k : ℕ) :
    0 ≤ (if 1 ≤ a ∧ a + b ≤ k then G (a + 1) b else 0) := by
  split_ifs with h
  · exact hG (a + 1) b
  · exact le_refl 0

/-- Shifting the radial index by one: `Σ_{i≤k} R(i+1) ≤ Σ_{i≤k} R i + R(k+1)` when the
missed term `R 0` is nonnegative. -/
private lemma radial_le (k : ℕ) (R : ℕ → ℝ) (hR : 0 ≤ R 0) :
    (∑ i ∈ Finset.range (k + 1), R (i + 1))
      ≤ (∑ i ∈ Finset.range (k + 1), R i) + R (k + 1) := by
  have h1 : (∑ x ∈ Finset.range (k + 1 + 1), R x)
      = (∑ i ∈ Finset.range (k + 1), R (i + 1)) + R 0 :=
    Finset.sum_range_succ' R (k + 1)
  have h2 : (∑ x ∈ Finset.range (k + 1 + 1), R x)
      = (∑ i ∈ Finset.range (k + 1), R i) + R (k + 1) :=
    Finset.sum_range_succ R (k + 1)
  linarith

/-- The mixed-index bookkeeping.  For a nonnegative `G`, the double sum over the triangle
`1 ≤ i`, `i + j ≤ k` with the term `G i (j+1)` is dominated by the sum of

* the same triangle with the term `G a b`,
* the same triangle with the term `G (a+1) b`,
* the single term `G 1 k`.

Indeed, `SumShiftZ_le` puts the left-hand side inside the triangle `1 ≤ a`, `a + b ≤ k+1`
with term `G a b`; `SumRowShift_eq` splits off the row `a = 1` of that triangle, leaving
exactly the second sum; and the row `a = 1` itself is `Σ_{i<k} G 1 i + G 1 k`. -/
private lemma mixed_le (k : ℕ) (G : ℕ → ℕ → ℝ) (hG : ∀ a b, 0 ≤ G a b) :
    (∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1),
        (if 1 ≤ i ∧ i + j ≤ k then G i (j + 1) else 0))
      ≤ (∑ a ∈ Finset.range (k + 1), ∑ b ∈ Finset.range (k + 1),
            (if 1 ≤ a ∧ a + b ≤ k then G a b else 0))
        + (∑ a ∈ Finset.range (k + 1), ∑ b ∈ Finset.range (k + 1),
            (if 1 ≤ a ∧ a + b ≤ k then G (a + 1) b else 0))
        + G 1 k := by
  by_cases hk : k = 0
  · rw [hk]
    have h1 : (∑ i ∈ Finset.range (0 + 1), ∑ j ∈ Finset.range (0 + 1),
        (if 1 ≤ i ∧ i + j ≤ 0 then G i (j + 1) else 0)) = 0 := by
      apply Finset.sum_eq_zero
      intro i _
      apply Finset.sum_eq_zero
      intro j _
      exact ite_eq_right (by omega)
    rw [h1]
    refine add_nonneg (add_nonneg ?_ ?_) (hG 1 0)
    · exact Finset.sum_nonneg fun a _ =>
        Finset.sum_nonneg fun b _ => ite_cond_nonneg hG a b 0
    · exact Finset.sum_nonneg fun a _ =>
        Finset.sum_nonneg fun b _ => ite_cond_nonneg_shift hG a b 0
  · set A : ℝ := ∑ a ∈ Finset.range (k + 1), ∑ b ∈ Finset.range (k + 1),
        (if 1 ≤ a ∧ a + b ≤ k then G a b else 0) with hA
    set B : ℝ := ∑ a ∈ Finset.range (k + 1), ∑ b ∈ Finset.range (k + 1),
        (if 1 ≤ a ∧ a + b ≤ k then G (a + 1) b else 0) with hB
    set T : ℝ := ∑ a ∈ Finset.range (k + 2), ∑ b ∈ Finset.range (k + 2),
        (if 1 ≤ a ∧ a + b ≤ k + 1 then G a b else 0) with hT
    have hshift : (∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1),
        (if 1 ≤ i ∧ i + j ≤ k then G i (j + 1) else 0)) ≤ T := by
      rw [hT]
      exact Work.Coercivity.SumShiftZ_le k G hG
    have hrow : (∑ i ∈ Finset.range (k + 1), G 1 i) + B = T := by
      rw [hB, hT]
      exact Work.Coercivity.SumRowShift_eq k G
    have hrow1 : (∑ b ∈ Finset.range (k + 1),
          (if 1 ≤ (1 : ℕ) ∧ (1 : ℕ) + b ≤ k then G 1 b else 0))
        = ∑ i ∈ Finset.range k, G 1 i := by
      rw [Finset.sum_range_succ]
      have hz : (if 1 ≤ (1 : ℕ) ∧ (1 : ℕ) + k ≤ k then G 1 k else 0) = 0 := by
        rw [ite_eq_right (by omega)]
      rw [hz, add_zero]
      refine Finset.sum_congr rfl (fun b hb => ?_)
      rw [Finset.mem_range] at hb
      rw [ite_eq_left (by omega)]
    have hArow : (∑ i ∈ Finset.range (k + 1), G 1 i) ≤ A + G 1 k := by
      rw [Finset.sum_range_succ (fun i => G 1 i) k, hA]
      have hsub : (∑ i ∈ Finset.range k, G 1 i)
          ≤ ∑ a ∈ Finset.range (k + 1), ∑ b ∈ Finset.range (k + 1),
              (if 1 ≤ a ∧ a + b ≤ k then G a b else 0) := by
        have hmem : (1 : ℕ) ∈ Finset.range (k + 1) := by
          rw [Finset.mem_range]
          omega
        refine le_trans (le_of_eq hrow1.symm) ?_
        exact Finset.single_le_sum
          (f := fun a => ∑ b ∈ Finset.range (k + 1),
            (if 1 ≤ a ∧ a + b ≤ k then G a b else 0))
          (s := Finset.range (k + 1))
          (fun a _ => Finset.sum_nonneg fun b _ => ite_cond_nonneg hG a b k) hmem
      linarith
    have hmain : (∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1),
        (if 1 ≤ i ∧ i + j ≤ k then G i (j + 1) else 0)) ≤ A + B + G 1 k := by
      linarith [hshift, hrow, hArow]
    rwa [hA, hB] at hmain

/-! ## The main statement -/

/-- **Pointwise domination of the `H^k`-integrand of `D_z Ψ`.**  This is a pure index
bookkeeping statement (summands of `HkIntegrand`), using only that `D_z` and `D_θ` commute for a
function smooth on a neighbourhood of the closed quadrant (`Work.Spaces.mixed_comm`).  Writing
`H = w/sin(2θ)^{η/2}` and `W = Wt α z θ = w/sin(2θ)^{γ/2}`,

`HkIntegrand α k (D_zΨ) = Σ_{i≤k} (D_z^{i+1}Ψ·H)² + Σ_{1≤i, i+j≤k} (D_z^{j+1}D_θ^iΨ·W)²`,

and since `mixed j i (Dz Ψ) = D_z^{j+1}D_θ^iΨ` on the quadrant, the summands split as follows:
the radial summands with `i+1 ≤ k` are radial summands of `HkIntegrand α k Ψ`; the mixed
summands with `i ≥ 2` are mixed summands of `HkIntegrand α k (D_θΨ)` (index shift
`(i,j) ↦ (i-1,j+1)`); the mixed summands with `i = 1` and `j+1 ≤ k-1` are mixed summands of
`HkIntegrand α k Ψ` (index `(1,j+1)`); and exactly two summands are *not* covered, namely
`(D_z^{k+1}Ψ·H)²` and `(D_z^kD_θΨ·W)²`, which are added on the right.  No weight comparison is
needed (the weights of matching summands are literally equal); at the boundary points `z = 0`,
`θ ∈ {0, π/2}` every term vanishes.  Template for the Finset bookkeeping:
`Submission/Work/Spaces/HkSq_mixed_le.lean`. -/
theorem HkIntegrand_Dz_le (α : ℝ) (k : ℕ) (Ψ : ℝ → ℝ → ℝ)
    (hsm : Work.Spaces.SmoothNbhd Ψ) (hα : 0 < α) (z θ : ℝ) (hz : z ∈ Work.Spaces.Iz)
    (hθ : θ ∈ Work.Spaces.Iθ) :
    Work.Spaces.HkIntegrand α k (Work.Spaces.Dz Ψ) z θ
      ≤ Work.Spaces.HkIntegrand α k Ψ z θ + Work.Spaces.HkIntegrand α k (Work.Spaces.Dth Ψ) z θ
        + (Work.Spaces.DzIter (k + 1) Ψ z θ *
            (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2
        + (Work.Spaces.DzIter k (Work.Spaces.Dth Ψ) z θ * Work.Spaces.Wt α z θ) ^ 2 := by
  set H : ℝ := Spaces.w z / (Real.sin (2 * θ)) ^ (Spaces.eta / 2) with hH
  set W : ℝ := Spaces.Wt α z θ with hW
  -- Unfolding the integrand in the two weights `H` and `W`.
  have hunfold : ∀ f : ℝ → ℝ → ℝ, Spaces.HkIntegrand α k f z θ
      = (∑ i ∈ Finset.range (k + 1), (Spaces.DzIter i f z θ * H) ^ 2)
        + ∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1),
            (if 1 ≤ i ∧ i + j ≤ k then (Spaces.mixed j i f z θ * W) ^ 2 else 0) := by
    intro f
    simp only [Spaces.HkIntegrand, ← hH, ← hW]
  -- The radial (pure) part of `D_z Ψ`.
  have hPL : (∑ i ∈ Finset.range (k + 1), (Spaces.DzIter i (Spaces.Dz Ψ) z θ * H) ^ 2)
      ≤ (∑ i ∈ Finset.range (k + 1), (Spaces.DzIter i Ψ z θ * H) ^ 2)
        + (Spaces.DzIter (k + 1) Ψ z θ * H) ^ 2 := by
    have hcongr : (∑ i ∈ Finset.range (k + 1),
          (Spaces.DzIter i (Spaces.Dz Ψ) z θ * H) ^ 2)
        = ∑ i ∈ Finset.range (k + 1), (Spaces.DzIter (i + 1) Ψ z θ * H) ^ 2 :=
      Finset.sum_congr rfl (fun i _ => by rw [DzIter_Dz i Ψ])
    rw [hcongr]
    exact radial_le k (fun a => (Spaces.DzIter a Ψ z θ * H) ^ 2)
      (sq_nonneg (Spaces.DzIter 0 Ψ z θ * H))
  -- The mixed part of `D_z Ψ`: push `D_θ` past `D_z`.
  have hmixedcongr : (∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1),
        (if 1 ≤ i ∧ i + j ≤ k then (Spaces.mixed j i (Spaces.Dz Ψ) z θ * W) ^ 2 else 0))
      = ∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1),
          (if 1 ≤ i ∧ i + j ≤ k then (Spaces.mixed (j + 1) i Ψ z θ * W) ^ 2 else 0) := by
    refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
    by_cases hc : 1 ≤ i ∧ i + j ≤ k
    · rw [ite_eq_left hc, ite_eq_left hc, mixed_Dz j i hsm hz hθ]
    · rw [ite_eq_right hc, ite_eq_right hc]
  -- The mixed part of the `D_θ Ψ`-integrand, with the `D_θ`-order reduced by one.
  have hBcongr : (∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1),
        (if 1 ≤ i ∧ i + j ≤ k then (Spaces.mixed j i (Spaces.Dth Ψ) z θ * W) ^ 2 else 0))
      = ∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1),
          (if 1 ≤ i ∧ i + j ≤ k then (Spaces.mixed j (i + 1) Ψ z θ * W) ^ 2 else 0) := by
    refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
    by_cases hc : 1 ≤ i ∧ i + j ≤ k
    · rw [ite_eq_left hc, ite_eq_left hc, mixed_Dth j i Ψ]
    · rw [ite_eq_right hc, ite_eq_right hc]
  have hML : (∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1),
        (if 1 ≤ i ∧ i + j ≤ k then (Spaces.mixed j i (Spaces.Dz Ψ) z θ * W) ^ 2 else 0))
      ≤ (∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1),
          (if 1 ≤ i ∧ i + j ≤ k then (Spaces.mixed j i Ψ z θ * W) ^ 2 else 0))
        + (∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1),
          (if 1 ≤ i ∧ i + j ≤ k then (Spaces.mixed j i (Spaces.Dth Ψ) z θ * W) ^ 2 else 0))
        + (Spaces.DzIter k (Spaces.Dth Ψ) z θ * W) ^ 2 := by
    rw [hmixedcongr, hBcongr]
    rw [show (Spaces.DzIter k (Spaces.Dth Ψ) z θ * W) ^ 2
        = (Spaces.mixed k 1 Ψ z θ * W) ^ 2 by
      rw [show Spaces.DzIter k (Spaces.Dth Ψ) = Spaces.mixed k 1 Ψ from
        DzIter_Dth_eq_mixed k Ψ]]
    exact mixed_le k (fun p q => (Spaces.mixed q p Ψ z θ * W) ^ 2)
      (fun p q => sq_nonneg _)
  have hPB : 0 ≤ ∑ i ∈ Finset.range (k + 1), (Spaces.DzIter i (Spaces.Dth Ψ) z θ * H) ^ 2 :=
    Finset.sum_nonneg fun i _ => sq_nonneg _
  rw [hunfold (Spaces.Dz Ψ), hunfold Ψ, hunfold (Spaces.Dth Ψ)]
  linarith [hPL, hML, hPB]

end Work.FTS.EllipticEst.Cert
