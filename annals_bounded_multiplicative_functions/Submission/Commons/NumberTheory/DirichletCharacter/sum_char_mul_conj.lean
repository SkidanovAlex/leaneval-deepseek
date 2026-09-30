import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.NumberTheory.DirichletCharacter.Bounds
import Mathlib.NumberTheory.DirichletCharacter.Orthogonality
import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed
import Mathlib.RingTheory.SimpleRing.Principal

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

open scoped BigOperators ComplexConjugate
set_option autoImplicit false

namespace Commons.NumberTheory.DirichletCharacter

open Complex

/-- For a complex Dirichlet character, conjugation of a value equals its inverse:
every value is `0` (at non-units) or lies on the unit circle (at units). -/
lemma conj_char_apply_eq_inv {q : ℕ} (χ : DirichletCharacter ℂ q) (x : ZMod q) :
    conj (χ x : ℂ) = (χ x : ℂ)⁻¹ := by
  by_cases hx : IsUnit x
  · rcases hx with ⟨u, rfl⟩
    have hnorm : ‖χ (u : ZMod q)‖ = 1 := DirichletCharacter.unit_norm_eq_one χ u
    have hprod : χ (u : ZMod q) * conj (χ (u : ZMod q)) = 1 := by
      have hmc : χ (u : ZMod q) * conj (χ (u : ZMod q)) = ↑‖χ (u : ZMod q)‖ ^ 2 :=
        Complex.mul_conj' (χ (u : ZMod q))
      rw [hmc, hnorm]
      norm_num
    exact eq_inv_of_mul_eq_one_right hprod
  · rw [MulChar.map_nonunit χ hx]
    simp

/-- For a unit `a`, conjugation of the value of a complex Dirichlet character at `a`
equals its value at the inverse of `a`. -/
lemma conj_char_apply_inv {q : ℕ} {a : ZMod q} (χ : DirichletCharacter ℂ q) (ha : IsUnit a) :
    conj (χ a : ℂ) = χ (a⁻¹ : ZMod q) := by
  rcases ha with ⟨u, rfl⟩
  have h1 : conj (χ (u : ZMod q)) = (χ (u : ZMod q))⁻¹ := by
    have hnorm : ‖χ (u : ZMod q)‖ = 1 := DirichletCharacter.unit_norm_eq_one χ u
    have hprod : χ (u : ZMod q) * conj (χ (u : ZMod q)) = 1 := by
      have hmc : χ (u : ZMod q) * conj (χ (u : ZMod q)) = ↑‖χ (u : ZMod q)‖ ^ 2 :=
        Complex.mul_conj' (χ (u : ZMod q))
      rw [hmc, hnorm]
      norm_num
    exact eq_inv_of_mul_eq_one_right hprod
  have h2 : (χ (u : ZMod q))⁻¹ = χ (((u⁻¹ : (ZMod q)ˣ) : ZMod q)) := by
    have hprod0 : χ (u : ZMod q) * χ (((u⁻¹ : (ZMod q)ˣ) : ZMod q)) = 1 := by
      have hmap : χ ((u : ZMod q) * ((u⁻¹ : (ZMod q)ˣ) : ZMod q)) =
          χ (u : ZMod q) * χ (((u⁻¹ : (ZMod q)ˣ) : ZMod q)) := by
        exact map_mul (χ : ZMod q →* ℂ) (u : ZMod q) ((u⁻¹ : (ZMod q)ˣ) : ZMod q)
      have hu1 : (u : ZMod q) * (((u⁻¹ : (ZMod q)ˣ)) : ZMod q) = 1 := by
        calc
          (u : ZMod q) * (((u⁻¹ : (ZMod q)ˣ)) : ZMod q) = (((u * u⁻¹ : (ZMod q)ˣ)) : ZMod q) := by
            rw [← Units.val_mul u (u⁻¹ : (ZMod q)ˣ)]
          _ = 1 := by
            rw [mul_inv_cancel u]
            simp
      calc
        χ (u : ZMod q) * χ (((u⁻¹ : (ZMod q)ˣ) : ZMod q)) =
            χ ((u : ZMod q) * ((u⁻¹ : (ZMod q)ˣ) : ZMod q)) := hmap.symm
        _ = χ (1 : ZMod q) := by rw [hu1]
        _ = 1 := map_one (χ : ZMod q →* ℂ)
    exact (eq_inv_of_mul_eq_one_right hprod0).symm
  rw [h1, h2, ZMod.inv_coe_unit]

/-- Pairwise orthogonality of Dirichlet characters with conjugate over `ℂ`: for a unit
`a` and arbitrary `b` in `ZMod q`, `∑_χ χ(a)·conj(χ(b))` equals `q.totient` when
`a = b` and `0` otherwise. -/
theorem sum_char_mul_conj (q : ℕ) [NeZero q] {a : ZMod q} (ha : IsUnit a) (b : ZMod q) :
    (∑ χ : DirichletCharacter ℂ q, (χ a : ℂ) * conj (χ b : ℂ)) =
      if a = b then (q.totient : ℂ) else 0 := by
  classical
  have hT :
      (∑ χ : DirichletCharacter ℂ q, conj (χ a : ℂ) * (χ b : ℂ)) =
        if a = b then (q.totient : ℂ) else 0 := by
    calc
      (∑ χ : DirichletCharacter ℂ q, conj (χ a : ℂ) * (χ b : ℂ))
          = (∑ χ : DirichletCharacter ℂ q, χ (a⁻¹ : ZMod q) * (χ b : ℂ)) := by
            apply Finset.sum_congr rfl
            intro χ hχ
            rw [conj_char_apply_inv χ ha]
      _ = if a = b then (q.totient : ℂ) else 0 := by
            exact DirichletCharacter.sum_char_inv_mul_char_eq (R := ℂ) (n := q) ha b
  calc
    (∑ χ : DirichletCharacter ℂ q, (χ a : ℂ) * conj (χ b : ℂ))
        = conj (∑ χ : DirichletCharacter ℂ q, conj (χ a : ℂ) * (χ b : ℂ)) := by
          rw [map_sum]
          simp
    _ = if a = b then (q.totient : ℂ) else 0 := by
          rw [hT]
          split_ifs with hab <;> simp

end Commons.NumberTheory.DirichletCharacter