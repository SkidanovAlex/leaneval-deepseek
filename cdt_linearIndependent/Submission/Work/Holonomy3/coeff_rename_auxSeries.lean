import Mathlib
import Submission.Work.Holonomy3.coeff_auxSeries
import Submission.Work.Holonomy3.embedVarC_prod_coeff
import Submission.Work.Holonomy3.finProdFin_symm_fst

namespace Work.Holonomy3

open scoped BigOperators

section Helpers

variable {m d : ℕ}

/-- Coefficient formula for the one-variable lift `PowerSeries.toMvPowerSeries s` (the `ℚ` version
of `Work.Holonomy3.coeff_toMvPowerSeries`). -/
private lemma coeff_toMvPowerSeries_rat (s : Fin d) (h : PowerSeries ℚ) (n : Fin d →₀ ℕ) :
    MvPowerSeries.coeff n (PowerSeries.toMvPowerSeries s h) =
      if n = Finsupp.single s (n s) then PowerSeries.coeff (n s) h else 0 := by
  rw [PowerSeries.toMvPowerSeries_eq_subst,
    PowerSeries.coeff_subst (PowerSeries.HasSubst.X s)]
  simp only [MvPowerSeries.coeff_X_pow, smul_eq_mul]
  by_cases hn : n = Finsupp.single s (n s)
  · rw [if_pos hn]
    rw [finsum_eq_single
      (fun e => PowerSeries.coeff e h * (if n = Finsupp.single s e then 1 else 0)) (n s)]
    · rw [if_pos hn, mul_one]
    · intro x hx
      have hx' : n ≠ Finsupp.single s x := by
        intro hh
        refine hx ?_
        calc x = (Finsupp.single s x) s := Finsupp.single_eq_same.symm
          _ = n s := by rw [← hh]
      rw [if_neg hx', mul_zero]
  · rw [if_neg hn]
    have hzero : (fun e : ℕ => PowerSeries.coeff e h * (if n = Finsupp.single s e then 1 else 0))
        = fun _ => (0 : ℚ) := by
      funext e
      have : n ≠ Finsupp.single s e := fun hh => hn (by rw [hh, Finsupp.single_eq_same])
      rw [if_neg this, mul_zero]
    rw [hzero, finsum_zero]

/-- `Submission.CDTPlan.embedVar s h` is Mathlib's one-variable lift
`PowerSeries.toMvPowerSeries s h`. -/
private lemma embedVar_eq_toMvPowerSeries_rat (s : Fin d) (h : PowerSeries ℚ) :
    Submission.CDTPlan.embedVar s h = PowerSeries.toMvPowerSeries s h := by
  funext n
  exact (coeff_toMvPowerSeries_rat s h n).symm

/-- Renaming variables `x_s ↦ x_{e s}` of a one-variable lift is the lift at the variable `e s`. -/
private lemma rename_embedVar_rat (e : Fin d ≃ Fin d) (s : Fin d) (h : PowerSeries ℚ) :
    MvPowerSeries.rename (⇑e) (Submission.CDTPlan.embedVar s h)
      = Submission.CDTPlan.embedVar (e s) h := by
  rw [embedVar_eq_toMvPowerSeries_rat s h, embedVar_eq_toMvPowerSeries_rat (e s) h]
  exact MvPowerSeries.rename_toMvPowerSeries (⇑e) s h

/-- Coefficients of a renamed series: for a bijection `e` of the variables, the coefficient of
`rename e p` at `mapDomain e x` is the coefficient of `p` at `x`. -/
private lemma coeff_rename_equiv_rat (e : Fin d ≃ Fin d) (p : MvPowerSeries (Fin d) ℚ)
    (x : Fin d →₀ ℕ) :
    MvPowerSeries.coeff (Finsupp.mapDomain (⇑e) x) (MvPowerSeries.rename (⇑e) p)
      = MvPowerSeries.coeff x p := by
  have h := MvPowerSeries.coeff_embDomain_rename (e.toEmbedding) p x
  rwa [Finsupp.embDomain_eq_mapDomain] at h

/-- The reindexing equivalence of species vectors `i ↦ i ∘ π` (inverse `j ↦ j ∘ π⁻¹`). -/
private def permCompEquiv (π : Equiv.Perm (Fin d)) : (Fin d → Fin m) ≃ (Fin d → Fin m) where
  toFun i := i ∘ π
  invFun j := j ∘ π.symm
  left_inv i := by funext t; simp
  right_inv j := by funext t; simp

/-- The product of one-variable lifts after renaming the variables by `π.symm`, reindexed: the
`π`-permutation of the variables turns `∏_s (f_{i_s} ∘ x_s) ∘ π` into `∏_t f_{i_{π t}} ∘ x_t`. -/
private lemma prod_embedVar_perm (f : Fin m → PowerSeries ℚ) (π : Equiv.Perm (Fin d))
    (i : Fin d → Fin m) :
    (∏ s, MvPowerSeries.rename (⇑π.symm) (Submission.CDTPlan.embedVar s (f (i s))))
      = ∏ t, Submission.CDTPlan.embedVar t (f (i (π t))) := by
  rw [show (∏ s, MvPowerSeries.rename (⇑π.symm) (Submission.CDTPlan.embedVar s (f (i s))))
      = ∏ s, Submission.CDTPlan.embedVar (π.symm s) (f (i s)) from
    Finset.prod_congr rfl (fun s _ => rename_embedVar_rat π.symm s (f (i s)))]
  rw [← Equiv.prod_comp π (fun s => Submission.CDTPlan.embedVar (π.symm s) (f (i s)))]
  exact Finset.prod_congr rfl (fun t _ => by rw [Equiv.symm_apply_apply])

/-- One summand of the auxiliary series, transported by the relabelling `x_s ↦ x_{π.symm s}`. -/
private lemma rename_auxSeries_term (f : Fin m → PowerSeries ℚ)
    (Q : (Fin d → Fin m) → MvPolynomial (Fin d) ℚ) (π : Equiv.Perm (Fin d))
    (i : Fin d → Fin m) :
    MvPowerSeries.rename (⇑π.symm)
        ((Q i : MvPowerSeries (Fin d) ℚ) * ∏ s, Submission.CDTPlan.embedVar s (f (i s)))
      = (MvPolynomial.rename π.symm (Q i) : MvPowerSeries (Fin d) ℚ) *
          ∏ t, Submission.CDTPlan.embedVar t (f (i (π t))) := by
  rw [map_mul, map_prod, MvPowerSeries.rename_coe, prod_embedVar_perm]

end Helpers

/-- **Transport of the auxiliary series under a relabelling of the variables.**

Let `Q : (Fin d → Fin m) → MvPolynomial (Fin d) ℚ` be a template, `π` a permutation of the `d`
variables and `n : Fin d →₀ ℕ` an exponent vector.  Relabelling the variables by `π` (so that the
species-vector `i` becomes `i ∘ π⁻¹` and the polynomial `Q i` is renamed by `π⁻¹`) transports the
exponent vector `n` to the exponent vector `nT` with `nT j = n (π j)`, and the coefficients of the
auxiliary series are unchanged:

  `coeff nT (auxSeries f QT) = coeff n (auxSeries f Q)`

where `QT i = (rename π.symm) (Q (i ∘ π.symm))`.

This is what lets one *sort* a minimal-order exponent vector (the paper's "upon relabeling the
variables we may assume `n_1 ≤ ⋯ ≤ n_d`"): the sorted exponent vector `nT` is the one for which the
denominator bound `Work.Holonomy3.log_den_coeff_le` applies, while the coefficient — hence
`β_n` and the whole coefficient identity — is the same one. -/
theorem coeff_rename_auxSeries {m d : ℕ} (f : Fin m → PowerSeries ℚ)
    (Q : (Fin d → Fin m) → MvPolynomial (Fin d) ℚ) (π : Equiv.Perm (Fin d)) (n : Fin d →₀ ℕ) :
    MvPowerSeries.coeff (Finsupp.equivFunOnFinite.symm (fun j => n (π j)))
        (Submission.CDTPlan.auxSeries f (fun i => MvPolynomial.rename π.symm (Q (i ∘ π.symm))))
      = MvPowerSeries.coeff n (Submission.CDTPlan.auxSeries f Q) := by
  classical
  -- Step 1: relabelling the auxiliary series
  have hstep1 : MvPowerSeries.rename (⇑π.symm) (Submission.CDTPlan.auxSeries f Q)
      = Submission.CDTPlan.auxSeries f (fun i => MvPolynomial.rename π.symm (Q (i ∘ π.symm))) := by
    have hA : MvPowerSeries.rename (⇑π.symm) (Submission.CDTPlan.auxSeries f Q)
        = ∑ i, ((MvPolynomial.rename π.symm (Q i) : MvPowerSeries (Fin d) ℚ) *
            ∏ t, Submission.CDTPlan.embedVar t (f (i (π t)))) := by
      rw [Submission.CDTPlan.auxSeries, map_sum]
      exact Finset.sum_congr rfl (fun i _ => rename_auxSeries_term f Q π i)
    have hB : (∑ i, ((MvPolynomial.rename π.symm (Q i) : MvPowerSeries (Fin d) ℚ) *
            ∏ t, Submission.CDTPlan.embedVar t (f (i (π t)))))
        = ∑ j, ((MvPolynomial.rename π.symm (Q (j ∘ π.symm)) : MvPowerSeries (Fin d) ℚ) *
            ∏ t, Submission.CDTPlan.embedVar t (f (j t))) := by
      refine Fintype.sum_equiv (permCompEquiv π) _ _ (fun i => ?_)
      have hcomp : (⇑(permCompEquiv π) i) ∘ π.symm = i := by
        funext t; simp [permCompEquiv]
      rw [hcomp]
      refine congrArg₂ (· * ·) ?_ (Finset.prod_congr rfl (fun t _ => ?_))
      · rfl
      · rfl
    have hC : (∑ j, ((MvPolynomial.rename π.symm (Q (j ∘ π.symm)) :
            MvPowerSeries (Fin d) ℚ) * ∏ t, Submission.CDTPlan.embedVar t (f (j t))))
        = Submission.CDTPlan.auxSeries f
            (fun i => MvPolynomial.rename π.symm (Q (i ∘ π.symm))) := by
      rw [Submission.CDTPlan.auxSeries]
    exact hA.trans (hB.trans hC)
  -- Step 2: the coefficients are transported by the bijection `π`
  have hnm : Finsupp.equivFunOnFinite.symm (fun j => n (π j))
      = Finsupp.mapDomain (⇑π.symm) n := by
    ext a
    rw [Finsupp.equivFunOnFinite_symm_apply_apply, Finsupp.mapDomain_equiv_apply]
    simp
  rw [← hstep1, hnm]
  exact coeff_rename_equiv_rat π.symm (Submission.CDTPlan.auxSeries f Q) n

end Work.Holonomy3
