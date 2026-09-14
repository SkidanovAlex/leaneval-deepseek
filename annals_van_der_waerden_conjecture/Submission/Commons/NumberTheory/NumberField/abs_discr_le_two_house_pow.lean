import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.NumberTheory.NumberField.House
import Mathlib.RingTheory.Adjoin.PowerBasis
import Submission.Commons.NumberTheory.NumberField.abs_discr_rat_le_abs_discr_of_isIntegral_basis
import Submission.Commons.FieldTheory.Discriminant.discr_powerBasis_eq_discr

namespace Commons.NumberTheory.NumberField

/-- **Discriminant bound in terms of the house of an integral generator.**

If `α` is an algebraic integer generating a number field `K` of degree `n` over `ℚ`, then
`|discr K| ≤ (2 · house α) ^ (n (n - 1))`.

Indeed the powers `1, α, …, α ^ (n - 1)` form a `ℚ`-basis of `K` consisting of algebraic
integers, so `|discr K| ≤ |Algebra.discr ℚ b|` for that basis
(`Commons.NumberTheory.NumberField.abs_discr_rat_le_abs_discr_of_isIntegral_basis`), and the
discriminant of the power basis factors over the `ℚ`-embeddings of `K` into `ℂ` as
`∏_{i < j} (σ_j α - σ_i α) ^ 2`, each factor of which is bounded by `(2 · house α) ^ 2`
because `‖σ α‖ ≤ house α` (`NumberField.norm_embedding_le_house`). -/
theorem abs_discr_le_two_house_pow {K : Type*} [Field K] [NumberField K] {n : ℕ}
    (hn : Module.finrank ℚ K = n) {α : K} (hgen : Algebra.adjoin ℚ ({α} : Set K) = ⊤)
    (hint : IsIntegral ℤ α) :
    |((NumberField.discr K : ℤ) : ℝ)| ≤ (2 * NumberField.house α) ^ (n * (n - 1)) := by
  classical
  have hx : IsIntegral ℚ α := hint.tower_top
  let pb : PowerBasis ℚ K := PowerBasis.ofAdjoinEqTop hx hgen
  have hgenpb : pb.gen = α := by simp only [pb, PowerBasis.ofAdjoinEqTop_gen]
  have hdim : pb.dim = n := by
    rw [(PowerBasis.finrank pb).symm, hn]
  have hb : ∀ i : Fin pb.dim, IsIntegral ℤ (pb.basis i) := by
    intro i
    rw [PowerBasis.coe_basis, hgenpb]
    exact hint.pow i
  have hab := abs_discr_rat_le_abs_discr_of_isIntegral_basis pb.basis hb
  obtain e : Fin pb.dim ≃ (K →ₐ[ℚ] ℂ) := by
    refine Fintype.equivOfCardEq ?_
    rw [Fintype.card_fin, AlgHom.card ℚ K ℂ]
    exact (PowerBasis.finrank pb).symm
  have hprod := Algebra.discr_powerBasis_eq_prod ℚ ℂ pb e
  simp only [hgenpb] at hprod
  have hnorm : |(Algebra.discr ℚ ⇑pb.basis : ℝ)| ≤
      (2 * NumberField.house α) ^ (pb.dim * (pb.dim - 1)) := by
    rw [← Complex.norm_ratCast (Algebra.discr ℚ ⇑pb.basis)]
    have hcq : (Algebra.discr ℚ ⇑pb.basis : ℂ) =
        (algebraMap ℚ ℂ) (Algebra.discr ℚ ⇑pb.basis) := rfl
    rw [hcq, hprod]
    have hle : ∀ i j : Fin pb.dim,
        ‖((e j) α - (e i) α) ^ 2‖ ≤ (2 * NumberField.house α) ^ 2 := by
      intro i j
      rw [norm_pow]
      apply pow_le_pow_left₀ (norm_nonneg _)
      calc ‖(e j) α - (e i) α‖ ≤ ‖(e j) α‖ + ‖(e i) α‖ := norm_sub_le _ _
        _ ≤ NumberField.house α + NumberField.house α :=
              add_le_add (NumberField.norm_embedding_le_house α _)
                (NumberField.norm_embedding_le_house α _)
        _ = 2 * NumberField.house α := by ring
    calc ‖∏ i : Fin pb.dim, ∏ j ∈ Finset.Ioi i, ((e j) α - (e i) α) ^ 2‖
        = ∏ i : Fin pb.dim, ∏ j ∈ Finset.Ioi i, ‖((e j) α - (e i) α) ^ 2‖ := by
          rw [norm_prod]
          refine Finset.prod_congr rfl (fun i _ => ?_)
          rw [norm_prod]
      _ ≤ ∏ i : Fin pb.dim, ∏ j ∈ Finset.Ioi i, (2 * NumberField.house α) ^ 2 := by
          apply Finset.prod_le_prod
          · intro i _
            apply Finset.prod_nonneg
            intro j _
            positivity
          · intro i _
            apply Finset.prod_le_prod
            · intro j _
              positivity
            · intro j _
              exact hle i j
      _ = (2 * NumberField.house α) ^ (pb.dim * (pb.dim - 1)) := by
          simp only [Finset.prod_const]
          rw [Finset.prod_pow_eq_pow_sum, Polynomial.sum_card_Ioi]
          rw [← pow_mul, Nat.two_mul_div_two_of_even (Nat.even_mul_pred_self pb.dim)]
  have hnorm' : |(Algebra.discr ℚ ⇑pb.basis : ℝ)| ≤
      (2 * NumberField.house α) ^ (n * (n - 1)) := by
    have hexp : pb.dim * (pb.dim - 1) = n * (n - 1) := by rw [hdim]
    rw [hexp] at hnorm
    exact hnorm
  have hQ : |(NumberField.discr K : ℚ)| ≤ |(Algebra.discr ℚ ⇑pb.basis : ℚ)| := hab
  calc |((NumberField.discr K : ℤ) : ℝ)|
      = ((|(NumberField.discr K : ℚ)| : ℚ) : ℝ) := by
          rw [Rat.cast_abs]
          congr 1
    _ ≤ ((|(Algebra.discr ℚ ⇑pb.basis : ℚ)| : ℚ) : ℝ) := by exact_mod_cast hQ
    _ = |(Algebra.discr ℚ ⇑pb.basis : ℝ)| := by rw [Rat.cast_abs]
    _ ≤ _ := hnorm'

end Commons.NumberTheory.NumberField