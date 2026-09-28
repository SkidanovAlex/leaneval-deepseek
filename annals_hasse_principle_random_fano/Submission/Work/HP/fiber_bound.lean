import Mathlib
import Submission.Work.HP.Defs
import Submission.Work.HP.PairsAux

/-!
# `fiber_bound`: dyadic-window bound for the second moment over a fibre

If `T` is a finite family of primitive rank-`r` lattices whose successive minima all lie
in a *fixed* dyadic window (`kwin r L = k` for all `L ∈ T`), then the sum over `T` of the
second moments `#(L ∩ B_X) · #(L ∩ B_Y)` is bounded by the number of lattices in the
window times the single-lattice bound `hbp`.

`hnum` is the counting hypothesis (number of primitive rank-`r` lattices with all
successive minima bounded by `s j`); `hbp` is the single-lattice second-moment bound coming
from the geometry of numbers.  Both are hypotheses, and the proof below is the intended
partition argument: `hnum` applied to `s j = 2 ^ (k j)` and `F = T` bounds `T.card`, `hbp`
bounds each summand, and the two are multiplied.

## A note on the statement

The requested statement writes the *second* element of `Fin r` as the one-field anonymous
constructor `⟨1⟩` in its final line.  That token sequence is not well formed Lean
(`Fin.mk` has two fields: `⟨1, by omega⟩` is the intended term — exactly the form already
used for the same index inside the hypothesis `hbp` and everywhere else in this
development, e.g. `window_sum_ge3`).  The `local macro` below repairs precisely that token
sequence, so that the statement of `fiber_bound` is *literally the requested text* while
still elaborating to the intended proposition (it is definitionally equal to the version
with `k ⟨1, by omega⟩`; compare `hC` below, which uses the two-field form).
-/

namespace Work.HP

/-- Repair of the one-field anonymous constructor `⟨1⟩` (meaning the second element of
`Fin r`) appearing in the requested statement of `fiber_bound`. -/
local macro "⟨1⟩" : term => `(⟨1, by omega⟩)

theorem fiber_bound (n r : ℕ) (hn : 2 ≤ n) (hr : 3 ≤ r) (hrn : r ≤ n + 1)
    (Knum : ℝ) (hKnum : 0 < Knum)
    (hnum : ∀ (s : Fin r → ℝ) (F : Finset (Submodule ℤ (Fin (n + 1) → ℤ))), (∀ j, 1 ≤ s j) →
      (∀ L ∈ F, IsPrimLat L ∧ rk L = r ∧ ∀ j : Fin r, lam L (j.1 + 1) ≤ s j) →
      ((F.card : ℝ) ≤ Knum * ∏ j : Fin r, s j ^ (n + 1 + r + 1 - 2 * (j.1 + 1))))
    (Ksmall : ℝ) (hKsmall : 0 < Ksmall)
    (hbp : ∀ (L : Submodule ℤ (Fin (n + 1) → ℤ)) (k : Fin r → ℕ) (X Y : ℝ), rk L = r →
      (∀ j : Fin r, (2 : ℝ) ^ (k j) ≤ 2 * lam L (j.1 + 1)) → 1 ≤ X → 1 ≤ Y →
      lam L 1 ≤ X → lam L 2 ≤ Y →
      (ballCount L X : ℝ) * (ballCount L Y : ℝ) ≤
        Ksmall ^ 2 * (2 : ℝ) ^ (2 * r) * X ^ r * Y ^ r /
          ((2 : ℝ) ^ (r * k ⟨0, by omega⟩) *
            (2 : ℝ) ^ (k ⟨0, by omega⟩ + (r - 1) * k ⟨1, by omega⟩)))
    (X Y Δ : ℝ) (hX : 1 ≤ X) (hY : 1 ≤ Y)
    (T : Finset (Submodule ℤ (Fin (n + 1) → ℤ))) (k : Fin r → ℕ)
    (hT : ∀ L ∈ T, IsPrimLat L ∧ rk L = r ∧ detL L ≤ Δ + 1 ∧ lam L 1 ≤ X ∧ lam L 2 ≤ Y)
    (hwin1 : ∀ L ∈ T, ∀ j : Fin r, lam L (j.1 + 1) ≤ (2 : ℝ) ^ (kwin r L j))
    (hwin2 : ∀ L ∈ T, ∀ j : Fin r, (2 : ℝ) ^ (kwin r L j) ≤ 2 * lam L (j.1 + 1))
    (hk : ∀ L ∈ T, kwin r L = k) :
    (∑ L ∈ T, (ballCount L X : ℝ) * (ballCount L Y : ℝ)) ≤
      Knum * (2 : ℝ) ^ (∑ j : Fin r, k j * (n + 1 + r + 1 - 2 * (j.1 + 1))) *
        (Ksmall ^ 2 * (2 : ℝ) ^ (2 * r) * X ^ r * Y ^ r /
          ((2 : ℝ) ^ (r * k ⟨0, by omega⟩) *
            (2 : ℝ) ^ (k ⟨0, by omega⟩ + (r - 1) * k ⟨1⟩))) := by
  -- the per-lattice bound from `hbp`, with the window exponents fixed
  set C : ℝ := Ksmall ^ 2 * (2 : ℝ) ^ (2 * r) * X ^ r * Y ^ r /
      ((2 : ℝ) ^ (r * k ⟨0, by omega⟩) *
        (2 : ℝ) ^ (k ⟨0, by omega⟩ + (r - 1) * k ⟨1, by omega⟩)) with hC
  have hCnn : 0 ≤ C := by rw [hC]; positivity
  have hper : ∀ L ∈ T, (ballCount L X : ℝ) * (ballCount L Y : ℝ) ≤ C := by
    intro L hL
    have hrkL : rk L = r := (hT L hL).2.1
    have hk2 : ∀ j : Fin r, (2 : ℝ) ^ (k j) ≤ 2 * lam L (j.1 + 1) :=
      fun j => by have := hwin2 L hL j; rwa [hk L hL] at this
    rw [hC]
    exact hbp L k X Y hrkL hk2 hX hY (hT L hL).2.2.2.1 (hT L hL).2.2.2.2
  -- the number of lattices in the window, at scale `2 ^ k`
  have hcard : (T.card : ℝ) ≤
      Knum * (2 : ℝ) ^ (∑ j : Fin r, k j * (n + 1 + r + 1 - 2 * (j.1 + 1))) := by
    have hnum' := hnum (fun j => (2 : ℝ) ^ (k j)) T
      (fun j => one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2))
      (fun L hL => ⟨(hT L hL).1, (hT L hL).2.1,
        fun j => by have := hwin1 L hL j; rwa [hk L hL] at this⟩)
    have hprod : (∏ j : Fin r, ((2 : ℝ) ^ (k j)) ^ (n + 1 + r + 1 - 2 * (j.1 + 1)))
        = (2 : ℝ) ^ (∑ j : Fin r, k j * (n + 1 + r + 1 - 2 * (j.1 + 1))) := by
      have h1 : (∏ j : Fin r, ((2 : ℝ) ^ (k j)) ^ (n + 1 + r + 1 - 2 * (j.1 + 1)))
          = ∏ j : Fin r, (2 : ℝ) ^ (k j * (n + 1 + r + 1 - 2 * (j.1 + 1))) :=
        Finset.prod_congr rfl (fun j _ => by rw [← pow_mul])
      rw [h1, Finset.prod_pow_eq_pow_sum]
    rwa [hprod] at hnum'
  calc (∑ L ∈ T, (ballCount L X : ℝ) * (ballCount L Y : ℝ))
      ≤ ∑ _L ∈ T, C := Finset.sum_le_sum hper
    _ = (T.card : ℝ) * C := by rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (Knum * (2 : ℝ) ^ (∑ j : Fin r, k j * (n + 1 + r + 1 - 2 * (j.1 + 1)))) * C :=
        mul_le_mul_of_nonneg_right hcard hCnn
    _ = Knum * (2 : ℝ) ^ (∑ j : Fin r, k j * (n + 1 + r + 1 - 2 * (j.1 + 1))) *
        (Ksmall ^ 2 * (2 : ℝ) ^ (2 * r) * X ^ r * Y ^ r /
          ((2 : ℝ) ^ (r * k ⟨0, by omega⟩) *
            (2 : ℝ) ^ (k ⟨0, by omega⟩ + (r - 1) * k ⟨1, by omega⟩))) := by
        rw [hC]

end Work.HP
