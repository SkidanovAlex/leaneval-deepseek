import Mathlib
import Submission.Work.Holonomy3.comp_defs
import Submission.Work.Holonomy3.min_coeff
import Submission.Work.Holonomy3.coeff_cleared_eq
import Submission.Work.Holonomy3.clearedFun_pointwise_bound
import Submission.Work.Holonomy3.seeding_defs

/-!
# Assembly lemmas for the fine holonomy bound

Small technical facts used in the final assembly of `Work.Holonomy3.holonomy_bound_l2`:

* `clearedFun_pointwise_bound_max` — the pointwise bound of `clearedFun_pointwise_bound`, in the
  `max · 0` form that does not require `clearedFun ≠ 0`;
* `diagComp_vanishes_below` / `lexmin_transfer` — minimality of the leading multi-index transfers
  from the auxiliary series to its diagonal composition;
* `coeff_cleared_ne_zero` — the leading coefficient of the cleared composite is nonzero.
-/

namespace Work.Holonomy3

open Submission.CDTPlan
open scoped BigOperators

noncomputable section

/-- The pointwise bound on the cleared composite, in the `max · 0` form: valid at *every* point of
the torus, including the zeros of `clearedFun`. -/
theorem clearedFun_pointwise_bound_max {d m : ℕ} (Q : (Fin d → Fin m) → MvPolynomial (Fin d) ℂ)
    (ψ : Fin d → ℂ → ℂ) (N : Fin m → Fin d → ℂ → ℂ) (P : Fin m → Fin d → Polynomial ℂ)
    (H M Nr : ℝ) (hH : 1 ≤ H) (hM : 1 ≤ M) (hNr : 1 ≤ Nr) (hm : 1 ≤ m)
    (hNrc : ∀ i, ((Q i).support.card : ℝ) ≤ Nr)
    (hQc : ∀ i k, k ∈ (Q i).support → ‖(Q i).coeff k‖ ≤ H)
    (K : Finset (Fin d →₀ ℕ)) (hKne : K.Nonempty) (hK : ∀ i, (Q i).support ⊆ K)
    (hU : ∀ i s z, ‖z‖ = 1 → ‖N i s z * ∏ i' ∈ Finset.univ.erase i, (P i' s).eval z‖ ≤ M)
    (z : Fin d → ℂ) (hz : ∀ s, ‖z s‖ = 1) :
    Real.log ‖clearedFun Q ψ N P z‖ ≤
      max (Real.log H + Real.log Nr + (d : ℝ) * Real.log m + (d : ℝ) * Real.log M +
        K.sup' hKne (fun k : Fin d →₀ ℕ => ∑ s : Fin d, (k s : ℝ) * Real.log ‖ψ s (z s)‖)) 0 := by
  rcases eq_or_ne (clearedFun Q ψ N P z) 0 with h0 | h0
  · rw [h0, norm_zero, Real.log_zero]
    exact le_max_right _ _
  · exact le_max_of_le_left
      (clearedFun_pointwise_bound Q ψ N P H M Nr hH hM hNr hm hNrc hQc K hKne hK hU z hz h0)

/-- Minimality of the leading multi-index transfers to the diagonal composition. -/
theorem diagComp_vanishes_below {d : ℕ} (Φ : Fin d → PowerSeries ℂ) (g : MvPowerSeries (Fin d) ℂ)
    (n : Fin d →₀ ℕ)
    (hmin : ∀ n' : Fin d →₀ ℕ, n'.degree < n.degree → MvPowerSeries.coeff n' g = 0) :
    ∀ m : Fin d →₀ ℕ, m.degree < n.degree → MvPowerSeries.coeff m (diagComp Φ g) = 0 :=
  fun m hm => diagComp_coeff_eq_zero Φ g hmin hm

/-- Lexicographic minimality of the leading multi-index transfers to the diagonal composition:
the only same-degree monomials of `diagComp Φ g` that can be nonzero are those of `g`
(the convolution is diagonal in this degree). -/
theorem lexmin_transfer {d : ℕ} (Φ : Fin d → PowerSeries ℂ) (g : MvPowerSeries (Fin d) ℂ)
    (n : Fin d →₀ ℕ) (hΦ0 : ∀ s, PowerSeries.coeff 0 (Φ s) = 0)
    (hmin : ∀ n' : Fin d →₀ ℕ, n'.degree < n.degree → MvPowerSeries.coeff n' g = 0)
    (hlex : ∀ m : Fin d →₀ ℕ, m.degree = n.degree → MvPowerSeries.coeff m g ≠ 0 →
      m = n ∨ ∃ j : Fin d, (∀ i : Fin d, i < j → m i = n i) ∧ n j < m j)
    (hΦ1 : ∀ s, PowerSeries.coeff 1 (Φ s) ≠ 0) :
    ∀ m : Fin d →₀ ℕ, m.degree = n.degree → MvPowerSeries.coeff m (diagComp Φ g) ≠ 0 →
      m = n ∨ ∃ j : Fin d, (∀ i : Fin d, i < j → m i = n i) ∧ n j < m j := by
  intro m hm hmn
  rw [diagComp_coeff_eq (n := m) Φ g (fun m' hm' => hmin m' (hm ▸ hm')) hΦ0] at hmn
  exact hlex m hm (fun hc => hmn (by rw [hc, zero_mul]))

/-- The leading coefficient of the cleared composite is nonzero. -/
theorem coeff_cleared_ne_zero {d m : ℕ} (f : Fin m → PowerSeries ℚ)
    (Q : (Fin d → Fin m) → MvPolynomial (Fin d) ℚ) (Φ : Fin d → PowerSeries ℂ)
    (P : Fin m → Fin d → Polynomial ℂ) (n : Fin d →₀ ℕ)
    (hΦ0 : ∀ s, PowerSeries.coeff 0 (Φ s) = 0)
    (hβ : (Submission.CDTPlan.auxSeries f Q).coeff n ≠ 0)
    (hP0 : ∀ i s, (P i s).eval 0 ≠ 0)
    (hΦ1 : ∀ s, PowerSeries.coeff 1 (Φ s) ≠ 0)
    (hmin : ∀ n' : Fin d →₀ ℕ, n'.degree < n.degree →
      MvPowerSeries.coeff n' (auxSeriesC (fun i => PowerSeries.map (algebraMap ℚ ℂ) (f i))
        (fun i => MvPolynomial.map (algebraMap ℚ ℂ) (Q i))) = 0) :
    MvPowerSeries.coeff n (uPoly P *
      diagComp Φ (auxSeriesC (fun i => PowerSeries.map (algebraMap ℚ ℂ) (f i))
        (fun i => MvPolynomial.map (algebraMap ℚ ℂ) (Q i)))) ≠ 0 := by
  rw [coeff_cleared_eq f Q Φ P n hΦ0 hmin]
  refine mul_ne_zero (mul_ne_zero ?_ ?_) ?_
  · refine Finset.prod_ne_zero_iff.mpr (fun s _ => Finset.prod_ne_zero_iff.mpr (fun i _ => ?_))
    exact hP0 i s
  · exact_mod_cast hβ
  · exact Finset.prod_ne_zero_iff.mpr (fun s _ => pow_ne_zero _ (hΦ1 s))

/-- Reindexing the block sum along a permutation. -/
theorem sum_comp_blockIdx {d l : ℕ} (m : ℕ) (γ : Fin (l + 2) → ℝ) (L : Fin (l + 1) → ℝ)
    (n : Fin d → ℕ) (π : Equiv.Perm (Fin d)) :
    ∑ s : Fin d, (n s : ℝ) * L (blockIdx m γ (π.symm s)) =
      ∑ j : Fin d, (n (π j) : ℝ) * L (blockIdx m γ j) := by
  refine Fintype.sum_equiv π.symm _ _ (fun s => ?_)
  simp only [Equiv.apply_symm_apply]

end

end Work.Holonomy3
