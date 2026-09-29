import Mathlib
import Submission.Work.ZeroEst.defs
import Submission.Work.ZeroEst.coeff_prod_embedVar
import Submission.Work.ZeroEst.phi_extract
import Submission.Work.ZeroEst.degree_extractPoly
import Submission.Work.ZeroEst.exists_minCoeff

/-!
# The multivariate lift of the one-variable zero estimate (`Work.ZeroEst.reduction`)

This file proves the *reduction* step of Area Z: if the one-variable (Shidlovsky) bound

`h1 : ∀ D P, (∀ i, (P i).degree < D) → Σ_i P_i f_i ≠ 0 → order (Σ_i P_i f_i) ≤ m·D + C`

holds for the family `f : Fin m → ℚ⟦x⟧` with a constant `C`, then the multivariate Shidlovsky
lemma `ZeroEstimate` holds for `f` with the same constant `C`: every nonzero series

`auxSeries f Q = Σ_i Q_i(x) · f_{i_1}(x_1) ⋯ f_{i_d}(x_d)`

has a nonzero monomial of minimal total degree whose every exponent is `≤ m·D + C`.

## The argument

Let `G = auxSeries f Q ≠ 0` and let `n : Fin d →₀ ℕ` be an exponent of `G` of minimal total
degree `Finsupp.degree` (its existence is `Work.ZeroEst.exists_minCoeff`).  For a coordinate
`j : Fin d` form the one-variable series

`Φ_j G = Σ_t (coeff (n.update j t) G) x^t ∈ ℚ⟦x⟧`

(keep all coordinates `≠ j` at `n`'s values, vary the `j`-th).  Then

* `coeff (n j) (Φ_j G) = coeff n G ≠ 0`, so `Φ_j G ≠ 0` and `order (Φ_j G) ≤ n j`;
* if `t < n j` then `(n.update j t).degree < n.degree`, so by minimality of `n` the coefficient
  `coeff (n.update j t) G` vanishes; hence `n j ≤ order (Φ_j G)`.

So `order (Φ_j G) = n j`.  It remains to see that `Φ_j G` is a polynomial combination
`Σ_a R_a · f_a` of the `f_a` with `deg R_a < D`; applying `h1` then gives
`n j = order (Φ_j G) ≤ m·D + C`.

The extraction `Φ_j` of the term `(Q i) · ∏_s f_{i_s}(x_s)` is the content of the lemma
`Work.ZeroEst.phi_extract`: isolating the `j`-th variable turns the `d`-variable monomial into a
`ℚ[X]`-polynomial in `x_j` (whose `x_j`-degree is `≤ deg_{x_j}(Q i) < D`) times the single series
`f_{i_j}`.  `Work.ZeroEst.degree_extractPoly` is the corresponding degree bound, and
`Work.ZeroEst.coeff_prod_embedVar` the coefficient formula for a product of one-variable
embeddings used in its proof.
-/

namespace Work.ZeroEst

open Submission.CDTPlan
open scoped BigOperators

/-- Coefficient extraction of the terms of a polynomial: keep only the monomials `c` of `P` whose
non-`j` coordinates are `≤ n`, and map the remaining `j`-part `c j` to `X ^ (c j)`, the
non-`j`-coefficients of the ambient family being contracted to constants.  This is the polynomial
`R` of `phi_extract`. -/
noncomputable def extractPoly {d : ℕ} (n : Fin d →₀ ℕ) (j : Fin d)
    (P : MvPolynomial (Fin d) ℚ) (g : Fin d → PowerSeries ℚ) : Polynomial ℚ :=
  ∑ c ∈ P.support,
    if ∀ s, s ≠ j → c s ≤ n s then
      Polynomial.monomial (c j)
        (P.coeff c * ∏ s ∈ Finset.univ.erase j, PowerSeries.coeff (n s - c s) (g s))
    else 0

/-- `Φ_j G = Σ_t (coeff (n.update j t) G) x^t`: the one-variable series obtained by fixing the
coordinates `≠ j` of the exponent vector to `n`'s values. -/
noncomputable def Phi {d : ℕ} (n : Fin d →₀ ℕ) (j : Fin d)
    (G : MvPowerSeries (Fin d) ℚ) : PowerSeries ℚ :=
  PowerSeries.mk fun t => MvPowerSeries.coeff (n.update j t) G

@[simp] lemma Phi_coeff {d : ℕ} (n : Fin d →₀ ℕ) (j : Fin d)
    (G : MvPowerSeries (Fin d) ℚ) (t : ℕ) :
    PowerSeries.coeff t (Phi n j G) = MvPowerSeries.coeff (n.update j t) G := by
  rw [Phi, PowerSeries.coeff_mk]

lemma Phi_sum {d : ℕ} (n : Fin d →₀ ℕ) (j : Fin d) {ι : Type*} (s : Finset ι)
    (A : ι → MvPowerSeries (Fin d) ℚ) :
    Phi n j (∑ i ∈ s, A i) = ∑ i ∈ s, Phi n j (A i) := by
  ext t
  simp [Phi]

/-- A finite sum of polynomials of degree `< D` still has degree `< D`. -/
lemma degree_sum_lt {ι : Type*} (s : Finset ι) (p : ι → Polynomial ℚ) (D : ℕ)
    (h : ∀ i ∈ s, (p i).degree < (D : WithBot ℕ)) :
    (∑ i ∈ s, p i).degree < (D : WithBot ℕ) := by
  refine lt_of_le_of_lt (Polynomial.degree_sum_le s p) ?_
  refine (Finset.sup_lt_iff (show (⊥ : WithBot ℕ) < (D : WithBot ℕ) from by simp)).mpr ?_
  intro i hi
  exact h i hi

/-- Replacing the `j`-th coordinate of `n` by `t`. -/
lemma update_eq_erase_add_single {d : ℕ} (n : Fin d →₀ ℕ) (j : Fin d) (t : ℕ) :
    n.update j t = n.erase j + Finsupp.single j t := by
  ext s
  rw [Finsupp.update_apply, Finsupp.add_apply, Finsupp.erase_apply]
  by_cases h : s = j
  · subst h; simp
  · simp [h]

lemma degree_update_add {d : ℕ} (n : Fin d →₀ ℕ) (j : Fin d) (t : ℕ) :
    (n.update j t).degree = (n.erase j).degree + t := by
  have key := map_add (Finsupp.degree : (Fin d →₀ ℕ) →+ ℕ) (n.erase j) (Finsupp.single j t)
  simp only [Finsupp.degree_single] at key
  rw [update_eq_erase_add_single]
  exact key

/-- Decreasing the `j`-th coordinate strictly below its old value strictly decreases the total
degree. -/
lemma degree_update_lt {d : ℕ} (n : Fin d →₀ ℕ) (j : Fin d) (t : ℕ) (ht : t < n j) :
    (n.update j t).degree < n.degree := by
  have key := map_add (Finsupp.degree : (Fin d →₀ ℕ) →+ ℕ) (n.erase j)
    (Finsupp.single j (n j))
  simp only [Finsupp.degree_single] at key
  calc (n.update j t).degree = (n.erase j).degree + t := degree_update_add n j t
    _ < (n.erase j).degree + n j := by omega
    _ = (n.erase j + Finsupp.single j (n j)).degree := key.symm
    _ = n.degree := by rw [Finsupp.erase_add_single j n]

lemma degree_update_self {d : ℕ} (n : Fin d →₀ ℕ) (j : Fin d) :
    (n.update j (n j)).degree = n.degree := by
  have key := map_add (Finsupp.degree : (Fin d →₀ ℕ) →+ ℕ) (n.erase j)
    (Finsupp.single j (n j))
  simp only [Finsupp.degree_single] at key
  calc (n.update j (n j)).degree = (n.erase j).degree + n j := degree_update_add n j (n j)
    _ = (n.erase j + Finsupp.single j (n j)).degree := key.symm
    _ = n.degree := by rw [Finsupp.erase_add_single j n]

theorem reduction (m : ℕ) (f : Fin m → PowerSeries ℚ) (C : ℕ)
    (h1 : ∀ (D : ℕ) (P : Fin m → Polynomial ℚ),
      (∀ i, (P i).degree < (D : WithBot ℕ)) →
      (∑ i, (P i : PowerSeries ℚ) * f i) ≠ 0 →
      (∑ i, (P i : PowerSeries ℚ) * f i).order ≤ (m * D + C : ℕ∞)) :
    ∀ (d D : ℕ) (Q : (Fin d → Fin m) → MvPolynomial (Fin d) ℚ),
      (∀ i j, (Q i).degreeOf j < D) → Submission.CDTPlan.auxSeries f Q ≠ 0 →
      ∃ n : Fin d →₀ ℕ, MvPowerSeries.coeff n (Submission.CDTPlan.auxSeries f Q) ≠ 0 ∧
        (∀ n' : Fin d →₀ ℕ, n'.degree < n.degree →
          MvPowerSeries.coeff n' (Submission.CDTPlan.auxSeries f Q) = 0) ∧
        ∀ j, n j ≤ m * D + C := by
  intro d D Q hQD hGne
  rcases Nat.eq_zero_or_pos d with hd | hd
  · -- `d = 0`: the only exponent is `0`, so there is nothing to bound
    subst hd
    refine ⟨0, ?_, ?_, ?_⟩
    · intro h
      refine hGne (MvPowerSeries.ext fun n => ?_)
      rw [show n = 0 from Subsingleton.elim n 0, h]
      simp
    · intro n' hn'
      exact absurd hn' (by rw [show n' = 0 from Subsingleton.elim n' 0]; simp)
    · intro j
      exact j.elim0
  · -- `d ≥ 1`: the main argument
    obtain ⟨n, hncoeff, hnmin⟩ := exists_minCoeff (auxSeries f Q) hGne
    have key : ∀ j : Fin d, n j ≤ m * D + C := by
      intro j
      -- the extracted polynomials `E i` and their grouping `R a = Σ_{i j = a} E i`
      set E : (Fin d → Fin m) → Polynomial ℚ :=
        fun i => extractPoly n j (Q i) (fun s => f (i s)) with hE
      set R : Fin m → Polynomial ℚ :=
        fun a => ∑ i : Fin d → Fin m, if i j = a then E i else 0 with hR
      have hEdeg : ∀ i, (E i).degree < (D : WithBot ℕ) :=
        fun i => degree_extractPoly (Q i) (fun s => f (i s)) n j (hQD i j)
      have hRdeg : ∀ a, (R a).degree < (D : WithBot ℕ) := by
        intro a
        rw [hR]
        refine degree_sum_lt Finset.univ (fun i : Fin d → Fin m => if i j = a then E i else 0) D ?_
        intro i _
        by_cases h : i j = a
        · simpa [h] using hEdeg i
        · simp [h]
      -- the extraction of each term of `auxSeries`
      have hterm : ∀ i : Fin d → Fin m,
          Phi n j ((Q i : MvPowerSeries (Fin d) ℚ) * ∏ s, embedVar s (f (i s)))
            = (E i : PowerSeries ℚ) * f (i j) := by
        intro i
        rw [hE]
        refine PowerSeries.ext fun t => ?_
        rw [Phi_coeff]
        exact phi_extract (Q i) (fun s => f (i s)) n j t
      have hPhi_eq : Phi n j (auxSeries f Q)
          = ∑ i : Fin d → Fin m, (E i : PowerSeries ℚ) * f (i j) := by
        rw [auxSeries,
          Phi_sum n j Finset.univ
            (fun i => (Q i : MvPowerSeries (Fin d) ℚ) * ∏ s, embedVar s (f (i s)))]
        exact Finset.sum_congr rfl fun i _ => hterm i
      -- grouping by the `j`-th coordinate
      have hcoe : ∀ a : Fin m,
          (R a : PowerSeries ℚ)
            = ∑ i : Fin d → Fin m, (if i j = a then (E i : PowerSeries ℚ) else 0) := by
        intro a
        rw [hR]
        rw [show ((∑ i : Fin d → Fin m, if i j = a then E i else 0 : Polynomial ℚ) :
              PowerSeries ℚ)
            = Polynomial.coeToPowerSeries.ringHom
                (∑ i : Fin d → Fin m, if i j = a then E i else 0) from rfl, map_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        by_cases h : i j = a <;> simp [h]
      have hRsum : (∑ a : Fin m, (R a : PowerSeries ℚ) * f a)
          = ∑ i : Fin d → Fin m, (E i : PowerSeries ℚ) * f (i j) := by
        calc ∑ a : Fin m, (R a : PowerSeries ℚ) * f a
            = ∑ a : Fin m, (∑ i : Fin d → Fin m,
                (if i j = a then (E i : PowerSeries ℚ) else 0)) * f a := by
              refine Finset.sum_congr rfl fun a _ => ?_
              rw [hcoe a]
          _ = ∑ a : Fin m, ∑ i : Fin d → Fin m,
                (if i j = a then (E i : PowerSeries ℚ) else 0) * f a := by
              refine Finset.sum_congr rfl fun a _ => Finset.sum_mul _ _ _
          _ = ∑ a : Fin m, ∑ i : Fin d → Fin m,
                (if i j = a then (E i : PowerSeries ℚ) * f a else 0) := by
              refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun i _ => ?_
              by_cases h : i j = a <;> simp [h]
          _ = ∑ i : Fin d → Fin m, ∑ a : Fin m,
                (if i j = a then (E i : PowerSeries ℚ) * f a else 0) := Finset.sum_comm
          _ = ∑ i : Fin d → Fin m, (E i : PowerSeries ℚ) * f (i j) := by
              refine Finset.sum_congr rfl fun i _ => ?_
              rw [Finset.sum_ite_eq]
              simp
      have hPhi_ne : Phi n j (auxSeries f Q) ≠ 0 := by
        intro hzero
        have hc : PowerSeries.coeff (n j) (Phi n j (auxSeries f Q)) ≠ 0 := by
          rw [Phi_coeff, Finsupp.update_self]
          exact hncoeff
        rw [hzero] at hc
        exact hc (by simp)
      have hRne : (∑ a : Fin m, (R a : PowerSeries ℚ) * f a) ≠ 0 := by
        rw [hRsum, ← hPhi_eq]
        exact hPhi_ne
      -- the order of `Φ_j G` is exactly `n j`
      have hord : (Phi n j (auxSeries f Q)).order = (n j : ℕ∞) := by
        refine le_antisymm ?_ ?_
        · exact PowerSeries.order_le (n j)
            (by rw [Phi_coeff, Finsupp.update_self]; exact hncoeff)
        · refine PowerSeries.le_order _ _ fun i hi => ?_
          rw [Phi_coeff]
          exact hnmin (n.update j i)
            (degree_update_lt n j i (ENat.natCast_lt_natCast.mp hi))
      -- the one-variable bound, applied to `Σ_a R_a f_a = Φ_j G`
      have hb := h1 D R hRdeg hRne
      rw [hRsum, ← hPhi_eq, hord] at hb
      exact ENat.natCast_le_natCast.mp hb
    exact ⟨n, hncoeff, hnmin, key⟩

end Work.ZeroEst
