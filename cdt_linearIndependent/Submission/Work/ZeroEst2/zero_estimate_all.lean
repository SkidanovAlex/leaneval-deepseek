import Mathlib
import Submission.CDTPlan.Interfaces
import Submission.Work.ZeroEst.reduction
import Submission.Work.ZeroEst.case_det
import Submission.Work.ZeroEst.lang24_rank
import Submission.Work.ZeroEst.fixed_deg_order_bound
import Submission.Work.ZeroEst2.one_var_of_boundedBasis
import Submission.Work.ZeroEst.bounded_basis

/-!
# Area Z-all — the strong zero estimate (`Submission.CDTPlan.ZeroEstimateAll`)

This file proves the paper's Lemma `lem_Shidlovsky` in its *strong* form: for a `ℚ(x)`-linearly
independent `D`-closed family `f : Fin m → ℚ⟦x⟧` there is a constant `C` such that for every
multivariable polynomial combination

`G = auxSeries f Q = Σ_i Q_i(x) · f_{i_1}(x_1) ⋯ f_{i_d}(x_d)`,  `deg_{x_j} Q_i < D`,

**every** nonzero monomial `n` of `G` of minimal total degree satisfies `n j ≤ m·D + C`
(`ZeroEstimateAll`), whereas `ZeroEstimate` only asks for the existence of one such monomial.

The proof is the argument of `Work.ZeroEst.reduction`, which in fact never uses how the
minimal-degree monomial was produced: it fixes an arbitrary monomial `n` with `coeff n G ≠ 0` and
`coeff n' G = 0` for `n'.degree < n.degree`, and bounds each coordinate as follows.  Extracting the
coefficients of `G` in all variables except `j` gives a one-variable series `Φ_j G` with
`order (Φ_j G) = n j` which is a polynomial combination `Σ_a R_a f_a` with `deg R_a < D`; the
one-variable Shidlovsky bound `h1` then gives `n j = order (Φ_j G) ≤ m·D + C`.

`reduction_all` below is therefore a verbatim transcription of the body of `Work.ZeroEst.reduction`
with the monomial `n` (and its two defining properties) taken as parameters; the one-variable input
`Work.ZeroEst.one_var` is the deep step of Area Z and is supplied by the sibling area
`Submission/Work/ZeroEst/`.
-/

namespace Work.ZeroEst2

open Submission.CDTPlan
open scoped BigOperators

/-- **The multivariate lift for an arbitrary minimal-degree monomial.** If the one-variable
(Shidlovsky) bound `h1` holds for the family `f` with constant `C`, then for every multivariable
combination `auxSeries f Q` with `deg_{x_j} Q_i < D` and every exponent `n` of nonzero coefficient
that is of minimal total degree, all coordinates of `n` are `≤ m·D + C`. -/
theorem reduction_all (m : ℕ) (f : Fin m → PowerSeries ℚ) (C : ℕ)
    (h1 : ∀ (D : ℕ) (P : Fin m → Polynomial ℚ),
      (∀ i, (P i).degree < (D : WithBot ℕ)) →
      (∑ i, (P i : PowerSeries ℚ) * f i) ≠ 0 →
      (∑ i, (P i : PowerSeries ℚ) * f i).order ≤ (m * D + C : ℕ∞)) :
    ∀ (d D : ℕ) (Q : (Fin d → Fin m) → MvPolynomial (Fin d) ℚ),
      (∀ i j, (Q i).degreeOf j < D) →
      ∀ n : Fin d →₀ ℕ, MvPowerSeries.coeff n (auxSeries f Q) ≠ 0 →
        (∀ n' : Fin d →₀ ℕ, n'.degree < n.degree →
          MvPowerSeries.coeff n' (auxSeries f Q) = 0) →
        ∀ j, n j ≤ m * D + C := by
  intro d D Q hQD n hncoeff hnmin j
  -- the extracted polynomials `E i` and their grouping `R a = Σ_{i, i j = a} E i`
  set E : (Fin d → Fin m) → Polynomial ℚ :=
    fun i => Work.ZeroEst.extractPoly n j (Q i) (fun s => f (i s)) with hE
  set R : Fin m → Polynomial ℚ :=
    fun a => ∑ i : Fin d → Fin m, if i j = a then E i else 0 with hR
  have hEdeg : ∀ i, (E i).degree < (D : WithBot ℕ) :=
    fun i => Work.ZeroEst.degree_extractPoly (Q i) (fun s => f (i s)) n j (hQD i j)
  have hRdeg : ∀ a, (R a).degree < (D : WithBot ℕ) := by
    intro a
    rw [hR]
    refine Work.ZeroEst.degree_sum_lt Finset.univ
      (fun i : Fin d → Fin m => if i j = a then E i else 0) D ?_
    intro i _
    by_cases h : i j = a
    · simpa [h] using hEdeg i
    · simp [h]
  -- the extraction of each term of `auxSeries`
  have hterm : ∀ i : Fin d → Fin m,
      Work.ZeroEst.Phi n j ((Q i : MvPowerSeries (Fin d) ℚ) * ∏ s, embedVar s (f (i s)))
        = (E i : PowerSeries ℚ) * f (i j) := by
    intro i
    rw [hE]
    refine PowerSeries.ext fun t => ?_
    rw [Work.ZeroEst.Phi_coeff]
    exact Work.ZeroEst.phi_extract (Q i) (fun s => f (i s)) n j t
  have hPhi_eq : Work.ZeroEst.Phi n j (auxSeries f Q)
      = ∑ i : Fin d → Fin m, (E i : PowerSeries ℚ) * f (i j) := by
    rw [auxSeries,
      Work.ZeroEst.Phi_sum n j Finset.univ
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
  have hPhi_ne : Work.ZeroEst.Phi n j (auxSeries f Q) ≠ 0 := by
    intro hzero
    have hc : PowerSeries.coeff (n j) (Work.ZeroEst.Phi n j (auxSeries f Q)) ≠ 0 := by
      rw [Work.ZeroEst.Phi_coeff, Finsupp.update_self]
      exact hncoeff
    rw [hzero] at hc
    exact hc (by simp)
  have hRne : (∑ a : Fin m, (R a : PowerSeries ℚ) * f a) ≠ 0 := by
    rw [hRsum, ← hPhi_eq]
    exact hPhi_ne
  -- the order of `Φ_j G` is exactly `n j`
  have hord : (Work.ZeroEst.Phi n j (auxSeries f Q)).order = (n j : ℕ∞) := by
    refine le_antisymm ?_ ?_
    · exact PowerSeries.order_le (n j)
        (by rw [Work.ZeroEst.Phi_coeff, Finsupp.update_self]; exact hncoeff)
    · refine PowerSeries.le_order _ _ fun i hi => ?_
      rw [Work.ZeroEst.Phi_coeff]
      exact hnmin (n.update j i)
        (Work.ZeroEst.degree_update_lt n j i (ENat.natCast_lt_natCast.mp hi))
  -- the one-variable bound, applied to `Σ_a R_a f_a = Φ_j G`
  have hb := h1 D R hRdeg hRne
  rw [hRsum, ← hPhi_eq, hord] at hb
  exact ENat.natCast_le_natCast.mp hb

/-- The glue: the one-variable bound for the family `f` implies `ZeroEstimateAll`'s conclusion for
`f` (with the same constant). -/
theorem zeroEstimateAll_glue (m : ℕ) (f : Fin m → PowerSeries ℚ)
    (h : ∃ C : ℕ, ∀ (D : ℕ) (P : Fin m → Polynomial ℚ),
      (∀ i, (P i).degree < (D : WithBot ℕ)) →
      (∑ i, (P i : PowerSeries ℚ) * f i) ≠ 0 →
      (∑ i, (P i : PowerSeries ℚ) * f i).order ≤ (m * D + C : ℕ∞)) :
    ∃ C : ℕ, ∀ (d D : ℕ) (Q : (Fin d → Fin m) → MvPolynomial (Fin d) ℚ),
      (∀ i j, (Q i).degreeOf j < D) →
      ∀ n : Fin d →₀ ℕ, MvPowerSeries.coeff n (auxSeries f Q) ≠ 0 →
        (∀ n' : Fin d →₀ ℕ, n'.degree < n.degree →
          MvPowerSeries.coeff n' (auxSeries f Q) = 0) →
        ∀ j, n j ≤ m * D + C := by
  obtain ⟨C, hC⟩ := h
  exact ⟨C, reduction_all m f C hC⟩

/-- The one-variable Shidlovsky bound for the family `f`, given Lang's Lemma 2.4 in the
"bounded polynomial basis of `Λ`-stable subspaces" form (the conclusion of the sibling area's
`Work.ZeroEst3.lang24_bounded_basis`, taken here as the hypothesis `hL2`) and the orbit-rank
reduction + rank-slope order bound `Work.ZeroEst2.one_var_of_boundedBasis` (steps L1 + L3 of
`REFS/NOTES_LEAD_zero_estimate.md`). -/
theorem one_var_local_of_L2 (m : ℕ) (f : Fin m → PowerSeries ℚ) (hpi : PolyIndependent f)
    (hdc : DClosed f)
    (hL2 : ∀ (q : Polynomial ℚ) (hq : q ≠ 0) (A : Fin m → Fin m → Polynomial ℚ),
      ∃ c : ℕ, ∀ (r : ℕ) (Q : Fin r → Fin m → Polynomial ℚ),
        LinearIndependent (RatFunc ℚ)
          (fun k => fun j => algebraMap (Polynomial ℚ) (RatFunc ℚ) (Q k j)) →
        (∀ k, (fun j => algebraMap (Polynomial ℚ) (RatFunc ℚ)
            (q * Polynomial.derivative (Q k j) + ∑ i, Q k i * A i j)) ∈
          Submodule.span (RatFunc ℚ)
            (Set.range fun k => fun j => algebraMap (Polynomial ℚ) (RatFunc ℚ) (Q k j))) →
        ∃ v : Fin r → Fin m → Polynomial ℚ, (∀ i j, (v i j).natDegree ≤ c) ∧
          Submodule.span (RatFunc ℚ)
              (Set.range fun i => fun j => algebraMap (Polynomial ℚ) (RatFunc ℚ) (v i j)) =
            Submodule.span (RatFunc ℚ)
              (Set.range fun k => fun j => algebraMap (Polynomial ℚ) (RatFunc ℚ) (Q k j))) :
    ∃ C : ℕ, ∀ (D : ℕ) (P : Fin m → Polynomial ℚ),
      (∀ i, (P i).degree < (D : WithBot ℕ)) →
      (∑ i, (P i : PowerSeries ℚ) * f i) ≠ 0 →
      (∑ i, (P i : PowerSeries ℚ) * f i).order ≤ (m * D + C : ℕ∞) := by
  obtain ⟨q, hq, A, hrel⟩ := hdc
  exact Work.ZeroEst2.one_var_of_boundedBasis q hq A (hL2 q hq A) f hpi hrel

/-- `zero_estimate_all` modulo Lang's Lemma 2.4 (L2 of `REFS/NOTES_LEAD_zero_estimate.md`). -/
theorem zeroEstimateAll_of_L2
    (hL2 : ∀ (m : ℕ) (q : Polynomial ℚ) (hq : q ≠ 0) (A : Fin m → Fin m → Polynomial ℚ),
      ∃ c : ℕ, ∀ (r : ℕ) (Q : Fin r → Fin m → Polynomial ℚ),
        LinearIndependent (RatFunc ℚ)
          (fun k => fun j => algebraMap (Polynomial ℚ) (RatFunc ℚ) (Q k j)) →
        (∀ k, (fun j => algebraMap (Polynomial ℚ) (RatFunc ℚ)
            (q * Polynomial.derivative (Q k j) + ∑ i, Q k i * A i j)) ∈
          Submodule.span (RatFunc ℚ)
            (Set.range fun k => fun j => algebraMap (Polynomial ℚ) (RatFunc ℚ) (Q k j))) →
        ∃ v : Fin r → Fin m → Polynomial ℚ, (∀ i j, (v i j).natDegree ≤ c) ∧
          Submodule.span (RatFunc ℚ)
              (Set.range fun i => fun j => algebraMap (Polynomial ℚ) (RatFunc ℚ) (v i j)) =
            Submodule.span (RatFunc ℚ)
              (Set.range fun k => fun j => algebraMap (Polynomial ℚ) (RatFunc ℚ) (Q k j))) :
    ZeroEstimateAll := by
  intro m f hpi hdc
  exact zeroEstimateAll_glue m f (one_var_local_of_L2 m f hpi hdc (hL2 m))

theorem zero_estimate_all : ZeroEstimateAll :=
  zeroEstimateAll_of_L2 (fun m q hq A => Work.ZeroEst.bounded_basis m q hq A)

end Work.ZeroEst2
