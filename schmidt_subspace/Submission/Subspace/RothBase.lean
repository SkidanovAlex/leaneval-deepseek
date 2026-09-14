import Mathlib
import Submission.Subspace.RothWronskian
import Submission.Subspace.RothIndex
import Submission.Commons.Algebra.MvPolynomial.pderivIter_map
import Submission.Commons.Algebra.MvPolynomial.eval_uniqueAlgEquiv
import Submission.Commons.Algebra.MvPolynomial.uniqueAlgEquiv_pderivIter
import Submission.Commons.Algebra.MvPolynomial.uniqueAlgEquiv_map
import Submission.Commons.Algebra.Polynomial.derivative_iter_rootMultiplicity_eval_ne_zero
import Submission.Commons.NumberTheory.Height.MahlerMeasure.rootMultiplicity_mvFin1_mul_logHeight_one

/-!
# The base case (`m = 1`) of the multivariate Roth lemma

For a polynomial in one variable the index at `β` with weight `r` is `ord_β(P)/r`, where `ord_β(P)`
is the order of vanishing.  Consequently the Roth hypothesis plus the Mahler-measure input
`ord_β(P)·h(β) ≤ hZ P` gives `Ind ≤ η ≤ 4η`.

Here we reduce the base case to the completely explicit input "`ord` is an order of vanishing at
`β`" (the derivative of order `ord` does not vanish at `β`, all lower derivatives do), leaving only
the transfer to the classical root multiplicity to the Mahler-measure lemma
`Commons.NumberTheory.Height.MahlerMeasure.rootMultiplicity_mul_logHeight_one`.
-/

open scoped BigOperators

namespace Submission.Subspace

open MvPolynomial

variable {K : Type*} [Field K] [CharZero K]

/-- **Base case of the Roth lemma.**  If `ord` is an order of vanishing of `P ∈ ℤ[x_0]` at `β`
(the `ord`-th derivative does not vanish at `β`, the lower ones do not) and the Mahler-measure input
`ord · h(β) ≤ hZ P` holds, then the Roth hypothesis forces `Ind ≤ 4η`. -/
theorem index_fin_one_le_of_mahler {P : MvPolynomial (Fin 1) ℤ} (hP : P ≠ 0)
    (r : Fin 1 → ℕ) (hr : 1 ≤ r 0) (β : Fin 1 → ℚ) (η : ℝ) (hη0 : 0 < η)
    (ord : ℕ)
    (hord : Commons.Algebra.MvPolynomial.pderivIter
      (ord • Finsupp.single (0 : Fin 1) 1) P ≠ 0)
    (hordβ : MvPolynomial.eval β ((Commons.Algebra.MvPolynomial.pderivIter
      (ord • Finsupp.single (0 : Fin 1) 1) P).map (Int.castRingHom ℚ)) ≠ 0)
    (hmahler : (ord : ℝ) * Height.logHeight₁ (β 0) ≤ hZ P)
    (hcond : η * ((r 0 : ℝ) * Height.logHeight₁ (β 0)) ≥ hZ P + 100 * (r 0 : ℝ)) :
    index β r (P.map (Int.castRingHom ℚ)) ≤ 4 * η := by
  classical
  set ν : Fin 1 →₀ ℕ := ord • Finsupp.single (0 : Fin 1) 1 with hν
  have hr0pos : 0 < (r 0 : ℝ) := by exact_mod_cast (show 1 ≤ r 0 from hr)
  have hrpos : ∀ i : Fin 1, 0 < r i := by
    intro i
    fin_cases i
    exact lt_of_lt_of_le Nat.zero_lt_one hr
  have hQne : (P.map (Int.castRingHom ℚ)) ≠ 0 := fun h =>
    hP (MvPolynomial.map_injective (Int.castRingHom ℚ) Int.cast_injective
      (by rw [h, map_zero]))
  have hdQ : Commons.Algebra.MvPolynomial.pderivIter ν (P.map (Int.castRingHom ℚ)) ≠ 0 := by
    rw [Commons.Algebra.MvPolynomial.pderivIter_map]
    exact fun h => hord (MvPolynomial.map_injective (Int.castRingHom ℚ) Int.cast_injective
      (by rw [h, map_zero]))
  have hzero : index β r (Commons.Algebra.MvPolynomial.pderivIter ν
      (P.map (Int.castRingHom ℚ))) = 0 := by
    rw [index_eq_zero_iff β r hrpos _ hdQ, Commons.Algebra.MvPolynomial.pderivIter_map]
    exact hordβ
  have hdiff := index_sub_indexWt_le_index_pderivIter β r ν (P.map (Int.castRingHom ℚ)) hdQ
  rw [hzero] at hdiff
  have hwt : Commons.Algebra.MvPolynomial.indexWt r ν = (ord : ℝ) / (r 0 : ℝ) := by
    rw [hν, indexWt_smul_single]
  rw [hwt] at hdiff
  have hZ0 : 0 ≤ hZ P := by rw [hZ_eq]; exact logHeight_gP_nonneg _
  have hhpos : 0 < Height.logHeight₁ (β 0) := by
    have h1 : 0 < (r 0 : ℝ) * Height.logHeight₁ (β 0) := by
      nlinarith [hcond, hη0, hZ0, hr0pos]
    by_contra hcon
    push_neg at hcon
    nlinarith [h1, hcon, hr0pos]
  have hord_le : (ord : ℝ) ≤ η * (r 0 : ℝ) := by
    have := hhpos
    nlinarith [hmahler, hcond]
  have hindex_le : index β r (P.map (Int.castRingHom ℚ)) ≤ (ord : ℝ) / (r 0 : ℝ) := by
    linarith [hdiff]
  have hfinal : (ord : ℝ) / (r 0 : ℝ) ≤ η := by
    rw [div_le_iff₀ hr0pos]
    linarith [hord_le]
  linarith [hindex_le, hfinal, hη0]

/-- **The base case `m = 1` of the Roth lemma.** -/
theorem index_fin_one_le {P : MvPolynomial (Fin 1) ℤ} (hP : P ≠ 0) (r : Fin 1 → ℕ)
    (hr : 1 ≤ r 0) (β : Fin 1 → ℚ) (η : ℝ) (hη0 : 0 < η)
    (hcond : η * ((r 0 : ℝ) * Height.logHeight₁ (β 0)) ≥ hZ P + 100 * (r 0 : ℝ)) :
    index β r (P.map (Int.castRingHom ℚ)) ≤ 4 * η := by
  classical
  set Q : Polynomial ℤ := MvPolynomial.uniqueAlgEquiv ℤ (Fin 1) P with hQ
  have hQmap : Q.map (Int.castRingHom ℚ) =
      MvPolynomial.uniqueAlgEquiv ℚ (Fin 1) (P.map (Int.castRingHom ℚ)) := by
    rw [hQ]; exact Commons.Algebra.MvPolynomial.uniqueAlgEquiv_map P
  have hQne : Q.map (Int.castRingHom ℚ) ≠ 0 := by
    rw [hQmap]
    intro h
    have h1 : P.map (Int.castRingHom ℚ) = 0 :=
      (MvPolynomial.uniqueAlgEquiv ℚ (Fin 1)).injective (by rw [map_zero]; exact h)
    exact hP (MvPolynomial.map_injective (Int.castRingHom ℚ) Int.cast_injective
      (by rw [h1, map_zero]))
  set ord : ℕ := Polynomial.rootMultiplicity (β 0) (Q.map (Int.castRingHom ℚ)) with hord
  have hder : ((Polynomial.derivative^[ord]) (Q.map (Int.castRingHom ℚ))).eval (β 0) ≠ 0 :=
    Commons.Algebra.Polynomial.derivative_iter_rootMultiplicity_eval_ne_zero _ hQne (β 0)
  -- transfer to `P`
  have htrans : MvPolynomial.uniqueAlgEquiv ℚ (Fin 1)
      ((Commons.Algebra.MvPolynomial.pderivIter (ord • Finsupp.single (0 : Fin 1) 1) P).map
        (Int.castRingHom ℚ)) =
      (Polynomial.derivative^[ord]) (Q.map (Int.castRingHom ℚ)) := by
    have hthis := Commons.Algebra.MvPolynomial.uniqueAlgEquiv_pderivIter (σ := Fin 1) ord
      (P.map (Int.castRingHom ℚ))
    rw [Commons.Algebra.MvPolynomial.pderivIter_map, ← hQmap] at hthis
    rw [show (ord • Finsupp.single (0 : Fin 1) 1) = ord • Finsupp.single (default : Fin 1) 1
      from by congr 2]
    exact hthis
  have hne : Commons.Algebra.MvPolynomial.pderivIter (ord • Finsupp.single (0 : Fin 1) 1) P ≠ 0 := by
    intro h
    refine hder ?_
    have hzero : (Polynomial.derivative^[ord]) (Q.map (Int.castRingHom ℚ)) = 0 := by
      rw [← htrans, h]
      simp
    rw [hzero]
    simp
  have heval : MvPolynomial.eval β ((Commons.Algebra.MvPolynomial.pderivIter
      (ord • Finsupp.single (0 : Fin 1) 1) P).map (Int.castRingHom ℚ)) ≠ 0 := by
    rw [Commons.Algebra.MvPolynomial.eval_uniqueAlgEquiv, htrans]
    simpa using hder
  have hmahler : (ord : ℝ) * Height.logHeight₁ (β 0) ≤ hZ P := by
    rcases Nat.eq_zero_or_pos ord with h0 | hpos
    · rw [h0, Nat.cast_zero, zero_mul]
      rw [hZ_eq]
      exact logHeight_gP_nonneg _
    · have hroot : (Q.map (Int.castRingHom ℚ)).IsRoot (β 0) :=
        (Polynomial.rootMultiplicity_pos'.mp (by rw [← hord]; exact hpos)).2
      have hthis := Commons.NumberTheory.Height.MahlerMeasure.rootMultiplicity_mvFin1_mul_logHeight_one hP hroot
      rw [← hord] at hthis
      rw [hZ_eq]
      exact hthis
  exact index_fin_one_le_of_mahler hP r hr β η hη0 ord hne heval hmahler hcond

end Submission.Subspace
