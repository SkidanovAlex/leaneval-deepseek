import Mathlib
import Submission.Work.WilC4.Defs

namespace Work.WilC4

/-- Splitting one integer power over a product into a product of integer powers. -/
private lemma zpow_mul_split {M : Type} [Field M] {m : ℕ} (d b : Fin m → M) (N : Fin m → ℤ)
    (a : Fin m → ℤ) :
    (∏ j, (d j * b j ^ N j) ^ a j) = (∏ j, d j ^ a j) * (∏ j, b j ^ (N j * a j)) := by
  rw [← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl (fun j _ => by rw [mul_zpow, ← zpow_mul])

theorem prod_div_expand {M : Type} [Field M] {r m : ℕ} (d b : Fin m → M) (N : Fin m → ℤ)
    (x : Fin r → M) (q : Fin m → Fin r → ℤ) (a : Fin m → ℤ) :
    ∏ j, (d j * b j ^ N j / Work.WilC4.zmono x (q j)) ^ a j
      = (∏ j, d j ^ a j) * Work.WilC4.zmono b (fun j => N j * a j)
        * (∏ j, (Work.WilC4.zmono x (q j)) ^ a j)⁻¹ := by
  simp only [div_zpow]
  rw [Finset.prod_div_distrib, zpow_mul_split, div_eq_mul_inv]
  simp only [zmono]

end Work.WilC4
