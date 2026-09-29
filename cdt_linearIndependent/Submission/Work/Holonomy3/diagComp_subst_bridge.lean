import Mathlib
import Submission.Work.Holonomy3.subst_liftV
import Submission.Work.Holonomy3.cleared_defs
import Submission.Work.Holonomy3.embedVarC_prod_coeff
import Submission.Work.Holonomy3.embedVarC_eq_liftV

/-!
# The diagonal composition is the substitution `X_s ↦ Φ_s(x_s)`

`Work.Holonomy3.diagComp Φ g` is the diagonal composition `(z_1,…,z_d) ↦ g(Φ_1(z_1),…,Φ_d(z_d))`,
written coefficientwise as `∑_{m ≤ n} g.coeff m · ∏_s (Φ_s ^ {m_s}).coeff (n_s)`; the Mathlib
substitution `MvPowerSeries.subst (substFam Φ) g` replaces the variable `X_s` by the one-variable
lift `liftV s (Φ s)`.  This file identifies the two: they have the same coefficients.

The proof is coefficientwise.  By `MvPowerSeries.coeff_subst` the `n`-th coefficient of the
substitution is the (finite) sum over all multi-indices `m` of
`g.coeff m · coeff n (∏_s (liftV s (Φ s)) ^ {m_s})`; the `n`-th coefficient of a product of
one-variable lifts is the product `∏_s (Φ_s ^ {m_s}).coeff (n_s)` (a one-variable lift to the
`s`-th coordinate contributes only exponents supported at `s`), and the term vanishes unless
`m ≤ n` because `Φ_s` has vanishing constant coefficient, so `Φ_s ^ {m_s}` has order `m_s` and
cannot contribute to the coefficient of an exponent `n_s < m_s`.
-/

namespace Work.Holonomy3

open scoped BigOperators

/-- `substFam Φ` is a legitimate substitution family as soon as every `Φ s` vanishes at `0`. -/
lemma hasSubst_substFam {d : ℕ} (Φ : Fin d → PowerSeries ℂ)
    (hΦ0 : ∀ s : Fin d, PowerSeries.coeff 0 (Φ s) = 0) :
    MvPowerSeries.HasSubst (substFam Φ) := by
  refine MvPowerSeries.hasSubst_of_constantCoeff_zero (fun t => ?_)
  simp only [substFam, liftV]
  rw [PowerSeries.toMvPowerSeries_apply, MvPowerSeries.constantCoeff_rename,
    ← PowerSeries.constantCoeff_eq, ← PowerSeries.coeff_zero_eq_constantCoeff_apply, hΦ0 t]

/-- The `n`-th coefficient of a product of one-variable lifts `∏_s (Φ_s(x_s))^{m_s}` is the
product of the corresponding univariate coefficients. -/
lemma coeff_prod_substFam_pow {d : ℕ} (Φ : Fin d → PowerSeries ℂ) (m n : Fin d →₀ ℕ) :
    MvPowerSeries.coeff n (∏ s : Fin d, (substFam Φ s) ^ (m s)) =
      ∏ s : Fin d, PowerSeries.coeff (n s) ((Φ s) ^ (m s)) := by
  have h₂ : (∏ s : Fin d, (substFam Φ s) ^ (m s))
      = ∏ s : Fin d, liftV s ((Φ s) ^ (m s)) := by
    refine Finset.prod_congr rfl (fun s _ => ?_)
    exact (map_pow (PowerSeries.toMvPowerSeries (R := ℂ) s) (Φ s) (m s)).symm
  have h₃ : (∏ s : Fin d, liftV s ((Φ s) ^ (m s)))
      = ∏ s : Fin d, embedVarC s ((Φ s) ^ (m s)) :=
    Finset.prod_congr rfl fun s _ => (embedVarC_eq_liftV s ((Φ s) ^ (m s))).symm
  rw [h₂, h₃, embedVarC_prod_coeff]

/-- The coefficient of the `Finsupp.prod` form of a product of one-variable lifts. -/
lemma coeff_finsupp_prod_substFam {d : ℕ} (Φ : Fin d → PowerSeries ℂ) (m n : Fin d →₀ ℕ) :
    MvPowerSeries.coeff n (m.prod fun s e => (substFam Φ s) ^ e) =
      ∏ s : Fin d, PowerSeries.coeff (n s) ((Φ s) ^ (m s)) := by
  rw [Finsupp.prod_of_support_subset m (Finset.subset_univ _)
    (fun s e => (substFam Φ s) ^ e) (fun i _ => pow_zero _)]
  exact coeff_prod_substFam_pow Φ m n

theorem diagComp_subst_bridge {d : ℕ} (Φ : Fin d → PowerSeries ℂ)
    (hΦ0 : ∀ s : Fin d, PowerSeries.coeff 0 (Φ s) = 0) (g : MvPowerSeries (Fin d) ℂ) :
    Work.Holonomy3.diagComp Φ g =
      MvPowerSeries.subst (Work.Holonomy3.substFam Φ) g := by
  classical
  ext n
  have ha : MvPowerSeries.HasSubst (substFam Φ) := hasSubst_substFam Φ hΦ0
  rw [show MvPowerSeries.coeff n (Work.Holonomy3.diagComp Φ g)
      = ∑ m ∈ Finset.Iic n, g.coeff m * ∏ s, (Φ s ^ (m s)).coeff (n s) from rfl]
  rw [MvPowerSeries.coeff_subst ha g n]
  -- terms of the substitution sum vanish unless `m ≤ n`
  have hzero : ∀ m : Fin d →₀ ℕ, ¬ m ≤ n →
      g.coeff m • MvPowerSeries.coeff n (m.prod fun s e => (substFam Φ s) ^ e) = 0 := by
    intro m hmn
    have hm' : ∃ s : Fin d, n s < m s := by
      rw [Finsupp.le_def] at hmn
      simpa only [not_forall, not_le] using hmn
    obtain ⟨s, hs⟩ := hm'
    have hprod0 : (∏ s : Fin d, PowerSeries.coeff (n s) ((Φ s) ^ (m s))) = 0 :=
      Finset.prod_eq_zero (Finset.mem_univ s)
        (coeff_pow_eq_zero_of_lt (hΦ0 s) (k := m s) (m := n s) hs)
    rw [coeff_finsupp_prod_substFam Φ m n, hprod0, smul_zero]
  have hsupp : Function.support (fun m : Fin d →₀ ℕ =>
      g.coeff m • MvPowerSeries.coeff n (m.prod fun s e => (substFam Φ s) ^ e))
      ⊆ ↑(Finset.Iic n) := by
    intro m hm
    by_contra hmem
    refine hm (hzero m ?_)
    intro hle
    exact hmem (by simpa using hle)
  rw [finsum_eq_sum_of_support_subset
    (fun m : Fin d →₀ ℕ =>
      g.coeff m • MvPowerSeries.coeff n (m.prod fun s e => (substFam Φ s) ^ e))
    (s := Finset.Iic n) hsupp]
  refine Finset.sum_congr rfl (fun m _ => ?_)
  rw [smul_eq_mul, coeff_finsupp_prod_substFam Φ m n]

end Work.Holonomy3
