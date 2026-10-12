import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Submission.Commons.Analysis.Fourier.box3_parseval_cos
import Submission.Work.SmallBoxA0.sin_parseval_shifted
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Dependency aggregator: the mixed (per-coordinate cosine/sine) box Parseval

Declares the per-coordinate mode family (`mixedMode`) and its squared `L²`-norm weight
(`mixedWgt`) used by `Work.SmallBoxA0.boxParseval_mixed`, and pulls the three available
one-dimensional/`n`-dimensional Parseval identities into scope:

* `Commons.Analysis.Fourier.boxParseval_hasSum` — the `n`-dimensional *cosine* Parseval
  (`HasSum` form, any `n`), the template for the mixed statement;
* `Commons.Analysis.Fourier.cos_parseval_scaled_hasSum` — the 1-D cosine (`HasSum`) step;
* `Work.SmallBoxA0.sin_parseval_shifted` — the 1-D sine Parseval (tsum form).

`boxSet n ℓ = Set.pi Set.univ (fun _ : Fin n => boxB ℓ)` with `boxB ℓ = Set.Icc (-(ℓ/2)) (ℓ/2)`,
`boxMode ℓ k x = cos ((kπ/ℓ)(x + ℓ/2))` and `boxWgt ℓ k = if k = 0 then ℓ else ℓ/2`.
-/

open scoped Real BigOperators

noncomputable section

namespace Work.SmallBoxA0

/-- The per-coordinate mode family: the Dirichlet sine (`b = true`) or the Neumann cosine
(`b = false`), at wave number `k`, on the centred interval `[-ℓ/2, ℓ/2]`. -/
def mixedMode (ℓ : ℝ) (b : Bool) (k : ℕ) (x : ℝ) : ℝ :=
  if b then Real.sin (((k : ℝ) * Real.pi / ℓ) * (x + ℓ / 2))
       else Real.cos (((k : ℝ) * Real.pi / ℓ) * (x + ℓ / 2))

/-- The squared `L²`-norm of `mixedMode ℓ b k` over `[-ℓ/2, ℓ/2]`: `ℓ/2` for the sine modes
(including `k = 0`, where the mode is the zero function) and for the excited cosine modes,
and `ℓ` for the constant cosine mode. -/
def mixedWgt (ℓ : ℝ) (b : Bool) (k : ℕ) : ℝ :=
  if b then ℓ / 2 else if k = 0 then ℓ else ℓ / 2

lemma mixedMode_false (ℓ : ℝ) (k : ℕ) (x : ℝ) :
    mixedMode ℓ false k x = Commons.Analysis.Fourier.boxMode ℓ k x := rfl

lemma mixedMode_true (ℓ : ℝ) (k : ℕ) (x : ℝ) :
    mixedMode ℓ true k x = Real.sin (((k : ℝ) * Real.pi / ℓ) * (x + ℓ / 2)) := rfl

lemma mixedWgt_false (ℓ : ℝ) (k : ℕ) :
    mixedWgt ℓ false k = Commons.Analysis.Fourier.boxWgt ℓ k := rfl

lemma mixedWgt_true (ℓ : ℝ) (k : ℕ) : mixedWgt ℓ true k = ℓ / 2 := by
  unfold mixedWgt; simp

lemma mixedWgt_pos {ℓ : ℝ} (hℓ : 0 < ℓ) (b : Bool) (k : ℕ) : 0 < mixedWgt ℓ b k := by
  unfold mixedWgt
  split
  · linarith
  · split <;> linarith

lemma mixedWgt_ne_zero {ℓ : ℝ} (hℓ : 0 < ℓ) (b : Bool) (k : ℕ) : mixedWgt ℓ b k ≠ 0 :=
  ne_of_gt (mixedWgt_pos hℓ b k)

lemma mixedMode_true_zero (ℓ : ℝ) (x : ℝ) : mixedMode ℓ true 0 x = 0 := by
  simp [mixedMode]

lemma mixedMode_false_zero (ℓ : ℝ) (x : ℝ) : mixedMode ℓ false 0 x = 1 := by
  simp [mixedMode]

/-- The reciprocal weight in the corpus normalisation. -/
lemma inv_mixedWgt {ℓ : ℝ} (b : Bool) (k : ℕ) :
    (mixedWgt ℓ b k)⁻¹ = if b then 2 / ℓ else if k = 0 then 1 / ℓ else 2 / ℓ := by
  cases b
  · simp only [Bool.false_eq_true, if_false]
    unfold mixedWgt
    simp only [Bool.false_eq_true, if_false]
    by_cases hk : k = 0
    · rw [if_pos hk, if_pos hk, one_div]
    · rw [if_neg hk, if_neg hk, inv_div]
  · simp only [if_true]
    unfold mixedWgt
    rw [if_pos rfl, inv_div]

/-- The weight of a coordinate-tuple factors over `Fin.cons`. -/
lemma mixedWgt_prod_cons {n : ℕ} {ℓ : ℝ} (b : Bool) (ε : Fin n → Bool) (k0 : ℕ)
    (k : Fin n → ℕ) :
    (∏ i : Fin (n + 1), mixedWgt ℓ ((Fin.cons b ε : Fin (n + 1) → Bool) i)
        ((Fin.cons k0 k : Fin (n + 1) → ℕ) i))
      = mixedWgt ℓ b k0 * ∏ i : Fin n, mixedWgt ℓ (ε i) (k i) := by
  rw [Fin.prod_univ_succ]
  simp only [Fin.cons_zero, Fin.cons_succ]

end Work.SmallBoxA0
