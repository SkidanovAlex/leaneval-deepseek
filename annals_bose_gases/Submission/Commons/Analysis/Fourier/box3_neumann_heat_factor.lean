import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Factoring the three-dimensional Neumann heat kernel sum into one-dimensional sums

The mode sum
`∑' k : Fin 3 → ℕ, ∏ j, F j (k j)`
of a product of per-coordinate summands factors as the product `∏ j, ∑' m, F j m`
whenever each one-dimensional summand is absolutely summable on `ℕ`.  This is the
combinatorial heart of the `box3_neumann_heat_factor` identity, obtained by identifying
`Fin 3 → ℕ` with the product `ℕ × ℕ × ℕ` and iterating `tsum_mul_tsum_of_summable_norm`.
-/

namespace Commons.Analysis.Fourier

open scoped BigOperators

noncomputable section

/-- The bijection `(Fin 3 → ℕ) ≃ ℕ × ℕ × ℕ` sending `k` to `(k 0, k 1, k 2)`. -/
private def fin3NatEquivProd : (Fin 3 → ℕ) ≃ ℕ × ℕ × ℕ where
  toFun k := (k 0, k 1, k 2)
  invFun p := ![p.1, p.2.1, p.2.2]
  left_inv := by
    intro k
    funext i
    fin_cases i <;> simp
  right_inv := by
    intro p
    obtain ⟨a, b, c⟩ := p
    simp

/-- A product of three independent absolutely summable series over `ℕ`, re-indexed by
`Fin 3 → ℕ`, equals the product of the one-dimensional sums. -/
theorem tsum_fin3_prod (F : Fin 3 → ℕ → ℝ)
    (hF : ∀ j, Summable fun m => ‖F j m‖) :
    (∑' k : Fin 3 → ℕ, ∏ j : Fin 3, F j (k j)) = ∏ j : Fin 3, ∑' m, F j m := by
  have h01 : Summable fun q : ℕ × ℕ => ‖F 1 q.1 * F 2 q.2‖ :=
    Summable.mul_norm (hF 1) (hF 2)
  have hinner : (∑' m, F 1 m) * (∑' m, F 2 m) = ∑' q : ℕ × ℕ, F 1 q.1 * F 2 q.2 :=
    tsum_mul_tsum_of_summable_norm (hF 1) (hF 2)
  have hmain : (∑' m, F 0 m) * (∑' q : ℕ × ℕ, F 1 q.1 * F 2 q.2)
      = ∑' p : ℕ × ℕ × ℕ, F 0 p.1 * (F 1 p.2.1 * F 2 p.2.2) :=
    tsum_mul_tsum_of_summable_norm (hF 0) h01
  rw [show (∏ j : Fin 3, ∑' m, F j m) = (∑' m, F 0 m) * (∑' m, F 1 m) * (∑' m, F 2 m) by
    rw [Fin.prod_univ_three]]
  rw [← Equiv.tsum_eq fin3NatEquivProd.symm (fun k : Fin 3 → ℕ => ∏ j : Fin 3, F j (k j))]
  rw [show (∑' p : ℕ × ℕ × ℕ, ∏ j : Fin 3, F j ((fin3NatEquivProd.symm p) j))
      = ∑' p : ℕ × ℕ × ℕ, F 0 p.1 * (F 1 p.2.1 * F 2 p.2.2) by
    apply tsum_congr; intro p
    obtain ⟨a, b, c⟩ := p
    simp only [fin3NatEquivProd, Equiv.coe_fn_symm_mk]
    rw [Fin.prod_univ_three]
    simp [mul_assoc]]
  rw [← hmain, ← hinner]
  ring

/-- The summand of the `Fin 3 → ℕ` mode sum factors as a product of the per-coordinate
summands, using `Real.exp` of a sum of the squared lattice points. -/
private lemma summand_factor {s t : ℝ} (x y : Fin 3 → ℝ) (k : Fin 3 → ℕ) :
    (∏ j : Fin 3, (if k j = 0 then s else s / 2)⁻¹)
      * (∏ j : Fin 3, (Real.cos (Real.pi * (k j : ℝ) * (x j + s / 2) / s)
          * Real.cos (Real.pi * (k j : ℝ) * (y j + s / 2) / s)))
      * Real.exp (-(t * (Real.pi / s) ^ 2 * ∑ j : Fin 3, ((k j : ℝ)) ^ 2))
    = ∏ j : Fin 3,
        ((if k j = 0 then s else s / 2)⁻¹
          * (Real.cos (Real.pi * (k j : ℝ) * (x j + s / 2) / s)
              * Real.cos (Real.pi * (k j : ℝ) * (y j + s / 2) / s))
          * Real.exp (-(t * (Real.pi * (k j : ℝ) / s) ^ 2))) := by
  have hexp : Real.exp (-(t * (Real.pi / s) ^ 2 * ∑ j : Fin 3, ((k j : ℝ)) ^ 2))
      = ∏ j : Fin 3, Real.exp (-(t * (Real.pi * (k j : ℝ) / s) ^ 2)) := by
    rw [← Real.exp_sum]
    congr 1
    rw [Finset.sum_neg_distrib]
    congr 1
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [hexp]
  simp only [Fin.prod_univ_three]
  ring

/-- Absolute summability of the one-dimensional summand of the Neumann heat kernel:
it is dominated by a constant multiple of `exp (-c m²)`. -/
private lemma summable_F {s t : ℝ} (hs : 0 < s) (ht : 0 < t) (x y : Fin 3 → ℝ) (j : Fin 3) :
    Summable (fun m : ℕ => ‖(if m = 0 then s else s / 2)⁻¹
      * (Real.cos (Real.pi * (m : ℝ) * (x j + s / 2) / s)
          * Real.cos (Real.pi * (m : ℝ) * (y j + s / 2) / s))
      * Real.exp (-(t * (Real.pi * (m : ℝ) / s) ^ 2))‖) := by
  set c0 : ℝ := -(t * (Real.pi / s) ^ 2) with hc0
  have hc0neg : c0 < 0 := by
    rw [hc0]
    have hp : 0 < t * (Real.pi / s) ^ 2 := by
      apply mul_pos ht
      apply sq_pos_of_pos
      exact div_pos Real.pi_pos hs
    linarith
  have hgeom : Summable (fun m : ℕ => Real.exp (c0 * (m : ℝ) ^ 2)) :=
    Real.summable_exp_nat_mul_of_ge hc0neg (f := fun i : ℕ => (i : ℝ) ^ 2) (fun i => by
      rcases i with _ | i
      · simp
      · push_cast
        have h : (0 : ℝ) ≤ (i : ℝ) := Nat.cast_nonneg i
        have h2 : (0 : ℝ) ≤ (i : ℝ) ^ 2 := by positivity
        nlinarith)
  set M : ℝ := max s⁻¹ (s / 2)⁻¹ with hM
  have hMnn : 0 ≤ M := by
    rw [hM]; exact le_max_of_le_left (inv_nonneg.mpr hs.le)
  refine Summable.of_nonneg_of_le (fun m => norm_nonneg _) (fun m => ?_) (hgeom.mul_left M)
  have hposw : 0 ≤ (if m = 0 then s else s / 2)⁻¹ := by
    split
    · exact inv_nonneg.mpr hs.le
    · exact inv_nonneg.mpr (by linarith)
  have hw : ‖(if m = 0 then s else s / 2)⁻¹‖ ≤ M := by
    rw [Real.norm_eq_abs, abs_of_nonneg hposw, hM]
    split
    · exact le_max_left _ _
    · exact le_max_right _ _
  have hc1 : ‖Real.cos (Real.pi * (m : ℝ) * (x j + s / 2) / s)‖ ≤ 1 := by
    rw [Real.norm_eq_abs]; exact Real.abs_cos_le_one _
  have hc2 : ‖Real.cos (Real.pi * (m : ℝ) * (y j + s / 2) / s)‖ ≤ 1 := by
    rw [Real.norm_eq_abs]; exact Real.abs_cos_le_one _
  have he : ‖Real.exp (-(t * (Real.pi * (m : ℝ) / s) ^ 2))‖ ≤ Real.exp (c0 * (m : ℝ) ^ 2) := by
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    apply Real.exp_le_exp.mpr
    rw [hc0]
    exact le_of_eq (by ring)
  have h1 : ‖(if m = 0 then s else s / 2)⁻¹‖ * ‖Real.cos (Real.pi * (m : ℝ) * (x j + s / 2) / s)‖
      ≤ M * 1 := mul_le_mul hw hc1 (norm_nonneg _) hMnn
  have h2 : (‖(if m = 0 then s else s / 2)⁻¹‖ * ‖Real.cos (Real.pi * (m : ℝ) * (x j + s / 2) / s)‖)
        * ‖Real.cos (Real.pi * (m : ℝ) * (y j + s / 2) / s)‖ ≤ (M * 1) * 1 :=
    mul_le_mul h1 hc2 (norm_nonneg _) (by positivity)
  have h3 : ((‖(if m = 0 then s else s / 2)⁻¹‖ * ‖Real.cos (Real.pi * (m : ℝ) * (x j + s / 2) / s)‖)
        * ‖Real.cos (Real.pi * (m : ℝ) * (y j + s / 2) / s)‖)
        * ‖Real.exp (-(t * (Real.pi * (m : ℝ) / s) ^ 2))‖
      ≤ ((M * 1) * 1) * Real.exp (c0 * (m : ℝ) ^ 2) :=
    mul_le_mul h2 he (norm_nonneg _) (by positivity)
  calc ‖(if m = 0 then s else s / 2)⁻¹
        * (Real.cos (Real.pi * (m : ℝ) * (x j + s / 2) / s)
            * Real.cos (Real.pi * (m : ℝ) * (y j + s / 2) / s))
        * Real.exp (-(t * (Real.pi * (m : ℝ) / s) ^ 2))‖
      = (‖(if m = 0 then s else s / 2)⁻¹‖ * ‖Real.cos (Real.pi * (m : ℝ) * (x j + s / 2) / s)‖)
          * ‖Real.cos (Real.pi * (m : ℝ) * (y j + s / 2) / s)‖
          * ‖Real.exp (-(t * (Real.pi * (m : ℝ) / s) ^ 2))‖ := by
        rw [norm_mul, norm_mul, norm_mul]; ring
    _ ≤ ((M * 1) * 1) * Real.exp (c0 * (m : ℝ) ^ 2) := h3
    _ = M * Real.exp (c0 * (m : ℝ) ^ 2) := by ring

theorem box3_neumann_heat_factor {s t : ℝ} (hs : 0 < s) (ht : 0 < t) (x y : Fin 3 → ℝ) :
    (∑' k : Fin 3 → ℕ,
      (∏ j : Fin 3, (if k j = 0 then s else s / 2)⁻¹)
      * (∏ j : Fin 3, (Real.cos (Real.pi * (k j : ℝ) * (x j + s / 2) / s)
          * Real.cos (Real.pi * (k j : ℝ) * (y j + s / 2) / s)))
      * Real.exp (-(t * (Real.pi / s) ^ 2 * ∑ j : Fin 3, ((k j : ℝ)) ^ 2)))
    = ∏ j : Fin 3,
        (∑' k : ℕ, (if k = 0 then s else s / 2)⁻¹
          * (Real.cos (Real.pi * k * (x j + s / 2) / s)
              * Real.cos (Real.pi * k * (y j + s / 2) / s))
          * Real.exp (-(t * (Real.pi * k / s) ^ 2))) := by
  let F : Fin 3 → ℕ → ℝ := fun j m =>
    (if m = 0 then s else s / 2)⁻¹
      * (Real.cos (Real.pi * (m : ℝ) * (x j + s / 2) / s)
          * Real.cos (Real.pi * (m : ℝ) * (y j + s / 2) / s))
      * Real.exp (-(t * (Real.pi * (m : ℝ) / s) ^ 2))
  have hsumm : ∀ j, Summable fun m => ‖F j m‖ := fun j => summable_F hs ht x y j
  have hL : (∑' k : Fin 3 → ℕ,
      (∏ j : Fin 3, (if k j = 0 then s else s / 2)⁻¹)
      * (∏ j : Fin 3, (Real.cos (Real.pi * (k j : ℝ) * (x j + s / 2) / s)
          * Real.cos (Real.pi * (k j : ℝ) * (y j + s / 2) / s)))
      * Real.exp (-(t * (Real.pi / s) ^ 2 * ∑ j : Fin 3, ((k j : ℝ)) ^ 2)))
      = ∑' k : Fin 3 → ℕ, ∏ j : Fin 3, F j (k j) := by
    apply tsum_congr
    intro k
    exact summand_factor x y k
  have hR : (∏ j : Fin 3,
        (∑' k : ℕ, (if k = 0 then s else s / 2)⁻¹
          * (Real.cos (Real.pi * k * (x j + s / 2) / s)
              * Real.cos (Real.pi * k * (y j + s / 2) / s))
          * Real.exp (-(t * (Real.pi * k / s) ^ 2))))
      = ∏ j : Fin 3, ∑' m, F j m := by
    apply Finset.prod_congr rfl
    intro j _
    apply tsum_congr
    intro m
    rfl
  rw [hL, hR]
  exact tsum_fin3_prod F hsumm

end

end Commons.Analysis.Fourier