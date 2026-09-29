import Mathlib
import Submission.Work.Holonomy3.cleared_defs
import Submission.Work.Holonomy3.cleared_setup
import Submission.Work.Holonomy3.embedVarC_eq_liftV
import Submission.Work.Holonomy3.embedVarC_prod_coeff
import Submission.Work.Holonomy3.subst_liftV
import Submission.Work.Holonomy3.diagComp_subst_bridge
import Submission.Work.Holonomy3.compPS_subst_bridge

/-!
# Decomposition of the cleared series (STEP 3 of the fine holonomy bound)

The cleared pullback `uPoly P * diagComp Φ (auxSeriesC F Q)` is re-expanded, species by species
and monomial by monomial, as the finite sum

`∑_i ∑_{k ∈ Q_i.support} (Q_i)_k • ∏_s embedVarC s (Φ_s^{k_s} · (∏_{i'} P_{i',s}) · (F_{i_s} ∘ Φ_s))`.

The proof rewrites `diagComp` as the substitution `MvPowerSeries.subst (substFam Φ)` and
`compPS` as the univariate substitution `PowerSeries.subst`, expands each `Q_i` over its
support, and pulls the common factor `uPoly P = ∏_s embedVarC s (∏_{i'} P_{i',s})` out of the
inner sums.
-/

namespace Work.Holonomy3

open scoped BigOperators
open MvPowerSeries

noncomputable section

/-! ## Auxiliary facts about the lifts `embedVarC s` -/

/-- The lift `embedVarC s` is an algebra map, so it commutes with products of a tuple. -/
lemma embedVarC_prod_mul {d : ℕ} (α β : Fin d → PowerSeries ℂ) :
    (∏ s : Fin d, embedVarC s (α s * β s)) =
      (∏ s : Fin d, embedVarC s (α s)) * (∏ s : Fin d, embedVarC s (β s)) := by
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl (fun s _ => ?_)
  rw [embedVarC_eq_liftV, embedVarC_eq_liftV, embedVarC_eq_liftV, map_mul]

/-- The product over `s` of `embedVarC s ((Φ s)^(k s))` is the `Finsupp.prod` of the individual
lifts. -/
lemma prod_embedVarC_pow {d : ℕ} (Φ : Fin d → PowerSeries ℂ) (k : Fin d →₀ ℕ) :
    (∏ s : Fin d, embedVarC s ((Φ s) ^ (k s))) =
      Finsupp.prod k (fun s e => (embedVarC s (Φ s)) ^ e) := by
  rw [Finsupp.prod_of_support_subset (s := Finset.univ) k (Finset.subset_univ _) _
    (fun s _ => pow_zero _)]
  refine Finset.prod_congr rfl (fun s _ => ?_)
  rw [embedVarC_eq_liftV, embedVarC_eq_liftV, map_pow]

/-- The substitution family `substFam Φ` is the family of lifts of the `Φ s`. -/
lemma substFam_apply {d : ℕ} (Φ : Fin d → PowerSeries ℂ) (s : Fin d) :
    substFam Φ s = embedVarC s (Φ s) := by
  unfold substFam liftV
  exact (embedVarC_eq_liftV s (Φ s)).symm

/-- Substitution commutes with the lift `embedVarC s` (the `embedVarC`-form of `subst_liftV`). -/
lemma subst_liftV_embedVarC {d : ℕ} (Φ : Fin d → PowerSeries ℂ)
    (hΦ0 : ∀ s : Fin d, PowerSeries.coeff 0 (Φ s) = 0) (h : PowerSeries ℂ) (s : Fin d) :
    MvPowerSeries.subst (substFam Φ) (embedVarC s h) =
      embedVarC s (PowerSeries.subst (Φ s) h) := by
  rw [embedVarC_eq_liftV, embedVarC_eq_liftV]
  exact subst_liftV Φ hΦ0 h s

/-- The pole-clearing polynomial as a product of lifts. -/
lemma uPoly_eq {d m : ℕ} (P : Fin m → Fin d → Polynomial ℂ) :
    uPoly P = ∏ s : Fin d, embedVarC s (((∏ i', P i' s) : Polynomial ℂ) : PowerSeries ℂ) := by
  unfold uPoly
  refine Finset.prod_congr rfl (fun s _ => ?_)
  refine congrArg (embedVarC s) ?_
  have h : Polynomial.coeToPowerSeries.ringHom (∏ i, P i s)
      = ∏ i, Polynomial.coeToPowerSeries.ringHom (P i s) :=
    map_prod Polynomial.coeToPowerSeries.ringHom (fun i => P i s) Finset.univ
  simpa only [Polynomial.coeToPowerSeries.ringHom_apply] using h.symm

/-- Substitution into a polynomial, expanded over its support. -/
lemma subst_polynomial_eq_sum {d : ℕ} (Φ : Fin d → PowerSeries ℂ) (Q : MvPolynomial (Fin d) ℂ) :
    MvPowerSeries.subst (substFam Φ) (Q : MvPowerSeries (Fin d) ℂ) =
      ∑ k ∈ Q.support,
        Q.coeff k • Finsupp.prod k (fun s e => (embedVarC s (Φ s)) ^ e) := by
  rw [MvPowerSeries.subst_coe (a := substFam Φ) Q]
  conv_lhs => rw [MvPolynomial.as_sum Q]
  rw [map_sum]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [MvPolynomial.aeval_monomial, Algebra.smul_def]
  rw [Finsupp.prod_congr (f := k) (g1 := fun i j => (substFam Φ) i ^ j)
        (g2 := fun s e => (embedVarC s (Φ s)) ^ e) (fun s _ => by
      rw [substFam_apply])]

lemma subst_finset_sum {d : ℕ} (Φ : Fin d → PowerSeries ℂ)
    (hΦ0 : ∀ s : Fin d, PowerSeries.coeff 0 (Φ s) = 0) {ι : Type*} (s : Finset ι)
    (f : ι → MvPowerSeries (Fin d) ℂ) :
    MvPowerSeries.subst (substFam Φ) (∑ i ∈ s, f i) =
      ∑ i ∈ s, MvPowerSeries.subst (substFam Φ) (f i) := by
  have ha := hasSubst_substFam Φ hΦ0
  simpa only [MvPowerSeries.substAlgHom_apply] using
    (map_sum (MvPowerSeries.substAlgHom ha) f s)

lemma subst_finset_prod {d : ℕ} (Φ : Fin d → PowerSeries ℂ)
    (hΦ0 : ∀ s : Fin d, PowerSeries.coeff 0 (Φ s) = 0) {ι : Type*} (s : Finset ι)
    (f : ι → MvPowerSeries (Fin d) ℂ) :
    MvPowerSeries.subst (substFam Φ) (∏ i ∈ s, f i) =
      ∏ i ∈ s, MvPowerSeries.subst (substFam Φ) (f i) := by
  have ha := hasSubst_substFam Φ hΦ0
  simpa only [MvPowerSeries.substAlgHom_apply] using
    (map_prod (MvPowerSeries.substAlgHom ha) f s)

lemma smul_mul_pull {d : ℕ} (c : ℂ) (A B X : MvPowerSeries (Fin d) ℂ) :
    c • (A * B * X) = (c • A) * (B * X) := by
  rw [mul_assoc, ← smul_mul_assoc]

/-! ## The pointwise (per species vector) rearrangement -/

lemma inner_eq {d m : ℕ} (P : Fin m → Fin d → Polynomial ℂ)
    (Q : (Fin d → Fin m) → MvPolynomial (Fin d) ℂ) (Φ : Fin d → PowerSeries ℂ)
    (F : Fin m → PowerSeries ℂ) (h0 : ∀ s : Fin d, PowerSeries.coeff 0 (Φ s) = 0)
    (i : Fin d → Fin m) :
    (∑ k ∈ (Q i).support, (Q i).coeff k •
        ∏ s : Fin d, embedVarC s ((Φ s) ^ (k s) *
          (((∏ i', P i' s) : Polynomial ℂ) : PowerSeries ℂ) * compPS (Φ s) (F (i s))))
      = uPoly P * (MvPowerSeries.subst (substFam Φ) (Q i : MvPowerSeries (Fin d) ℂ) *
          ∏ s : Fin d, MvPowerSeries.subst (substFam Φ) (embedVarC s (F (i s)))) := by
  have hCs : (∏ s : Fin d, embedVarC s (compPS (Φ s) (F (i s))))
      = ∏ s : Fin d, MvPowerSeries.subst (substFam Φ) (embedVarC s (F (i s))) := by
    refine Finset.prod_congr rfl (fun s _ => ?_)
    rw [compPS_subst_bridge (h0 s), ← subst_liftV_embedVarC Φ h0 (F (i s)) s]
  have hterm : ∀ k : Fin d →₀ ℕ,
      (∏ s : Fin d, embedVarC s ((Φ s) ^ (k s) *
          (((∏ i', P i' s) : Polynomial ℂ) : PowerSeries ℂ) * compPS (Φ s) (F (i s))))
        = Finsupp.prod k (fun s e => (embedVarC s (Φ s)) ^ e) * uPoly P *
            (∏ s : Fin d, MvPowerSeries.subst (substFam Φ) (embedVarC s (F (i s)))) := by
    intro k
    rw [embedVarC_prod_mul (fun s => (Φ s) ^ (k s) *
            (((∏ i', P i' s) : Polynomial ℂ) : PowerSeries ℂ))
          (fun s => compPS (Φ s) (F (i s))),
        embedVarC_prod_mul (fun s => (Φ s) ^ (k s))
          (fun s => (((∏ i', P i' s) : Polynomial ℂ) : PowerSeries ℂ)),
        prod_embedVarC_pow, ← uPoly_eq, hCs]
  calc
    (∑ k ∈ (Q i).support, (Q i).coeff k •
        ∏ s : Fin d, embedVarC s ((Φ s) ^ (k s) *
          (((∏ i', P i' s) : Polynomial ℂ) : PowerSeries ℂ) * compPS (Φ s) (F (i s))))
      = ∑ k ∈ (Q i).support, (Q i).coeff k •
          (Finsupp.prod k (fun s e => (embedVarC s (Φ s)) ^ e) * uPoly P *
            (∏ s : Fin d, MvPowerSeries.subst (substFam Φ) (embedVarC s (F (i s))))) := by
        refine Finset.sum_congr rfl (fun k _ => ?_)
        rw [hterm k]
      _ = ∑ k ∈ (Q i).support, ((Q i).coeff k •
            Finsupp.prod k (fun s e => (embedVarC s (Φ s)) ^ e)) *
            (uPoly P *
              (∏ s : Fin d, MvPowerSeries.subst (substFam Φ) (embedVarC s (F (i s))))) := by
        refine Finset.sum_congr rfl (fun k _ => ?_)
        rw [smul_mul_pull]
      _ = (∑ k ∈ (Q i).support, (Q i).coeff k •
            Finsupp.prod k (fun s e => (embedVarC s (Φ s)) ^ e)) *
            (uPoly P *
              (∏ s : Fin d, MvPowerSeries.subst (substFam Φ) (embedVarC s (F (i s))))) := by
        rw [Finset.sum_mul]
      _ = uPoly P * (MvPowerSeries.subst (substFam Φ) (Q i : MvPowerSeries (Fin d) ℂ) *
            (∏ s : Fin d, MvPowerSeries.subst (substFam Φ) (embedVarC s (F (i s))))) := by
        rw [← subst_polynomial_eq_sum Φ (Q i)]
        ring

/-! ## The full rearrangement -/

lemma sum_eq {d m : ℕ} (P : Fin m → Fin d → Polynomial ℂ)
    (Q : (Fin d → Fin m) → MvPolynomial (Fin d) ℂ) (Φ : Fin d → PowerSeries ℂ)
    (F : Fin m → PowerSeries ℂ) (h0 : ∀ s : Fin d, PowerSeries.coeff 0 (Φ s) = 0) :
    (∑ i : Fin d → Fin m, ∑ k ∈ (Q i).support, (Q i).coeff k •
        ∏ s : Fin d, embedVarC s ((Φ s) ^ (k s) *
          (((∏ i', P i' s) : Polynomial ℂ) : PowerSeries ℂ) * compPS (Φ s) (F (i s))))
      = uPoly P * MvPowerSeries.subst (substFam Φ) (auxSeriesC F Q) := by
  have ha := hasSubst_substFam Φ h0
  rw [auxSeriesC, subst_finset_sum Φ h0 Finset.univ, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [inner_eq P Q Φ F h0 i]
  rw [MvPowerSeries.subst_mul ha, subst_finset_prod Φ h0 Finset.univ]

theorem cleared_series_decomp {d m : ℕ} (P : Fin m → Fin d → Polynomial ℂ)
    (Q : (Fin d → Fin m) → MvPolynomial (Fin d) ℂ) (Φ : Fin d → PowerSeries ℂ)
    (F : Fin m → PowerSeries ℂ) (h0 : ∀ s, PowerSeries.coeff 0 (Φ s) = 0) :
    Work.Holonomy3.uPoly P * Work.Holonomy3.diagComp Φ (Work.Holonomy3.auxSeriesC F Q) =
      ∑ i, ∑ k ∈ (Q i).support, (Q i).coeff k •
          ∏ s, Work.Holonomy3.embedVarC s ((Φ s) ^ (k s) *
            (((∏ i', P i' s) : Polynomial ℂ) : PowerSeries ℂ) *
              Work.Holonomy3.compPS (Φ s) (F (i s))) := by
  rw [diagComp_subst_bridge Φ h0]
  exact (sum_eq P Q Φ F h0).symm

end

end Work.Holonomy3
