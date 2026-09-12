import Submission.ThreePages
import Submission.Quantile
import Submission.PotentialContinuity
import Submission.SerreExample
import Submission.SupportConcentration
import Submission.EnergyDeliver
import Submission.EnergyRootBound
import Submission.EnergyPairs
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Topology.Algebra.Polynomial
import Mathlib.Tactic

noncomputable section

open MeasureTheory
open scoped Real BigOperators
open Polynomial

namespace Submission.EnergyHalf

open Submission.Quantile
open Submission.PotentialContinuity
open Submission.SerreExample
open Submission.ThreePages
open Submission.PotentialDefs

/-- `muS` has no atoms (as a typeclass instance for this module). -/
instance : MeasureTheory.NullSingletonClass muS :=
  ⟨muS_atom_free⟩

/-- The energy `I(μ) = ∫ U^μ dμ` of the Serre measure (classical-log
convention, matching Smith's `U^μ = ∫ −log|z−t|dμ`). -/
noncomputable def energy : ℝ :=
  ∫ x : ℝ, logPotential muS (x : ℂ) ∂muS

/-- The potential `U^μ(x)` at a real point, as a function of `x`. -/
noncomputable def pot (x : ℝ) : ℝ := logPotential muS (x : ℂ)

/-- Sum of the potentials at the roots. -/
noncomputable def Usum (n : ℕ) : ℝ :=
  ∑ k ∈ Finset.Icc 1 n, logPotential muS ((alpha n k : ℝ) : ℂ)

/-- The Vandermonde-style product `∏_{1 ≤ i < j ≤ n} |α_i − α_j|`. -/
noncomputable def Vprod (n : ℕ) : ℝ :=
  ∏ i ∈ Finset.Icc 1 n, ∏ j ∈ Finset.Icc (i + 1) n, |alpha n i - alpha n j|

/-- `log Vprod n`. -/
noncomputable def logV (n : ℕ) : ℝ :=
  ∑ i ∈ Finset.Icc 1 n, ∑ j ∈ Finset.Icc (i + 1) n, Real.log |alpha n i - alpha n j|

/-! ### elementary index / root facts -/

/-- cardinality of the root index set -/
lemma Icc_one_n_card (n : ℕ) : (Finset.Icc 1 n).card = n := by
  rw [Nat.card_Icc]
  omega

/-- distinct roots have distinct values -/
lemma alpha_ne_alpha {n i j : ℕ} (hn : 1 ≤ n)
    (hi : i ∈ Finset.Icc 1 n) (hj : j ∈ Finset.Icc 1 n) (hne : i ≠ j) :
    alpha n i ≠ alpha n j := by
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · intro h
    have hst := alpha_strict_mono hn (Finset.mem_Icc.mp hi).1 hlt (Finset.mem_Icc.mp hj).2
    rw [h] at hst
    exact (lt_irrefl _) hst
  · intro h
    have hst := alpha_strict_mono hn (Finset.mem_Icc.mp hj).1 hgt (Finset.mem_Icc.mp hi).2
    rw [h] at hst
    exact (lt_irrefl _) hst

/-- root-to-root distances are positive -/
lemma alpha_dist_pos {n i j : ℕ} (hn : 1 ≤ n)
    (hi : i ∈ Finset.Icc 1 n) (hj : j ∈ Finset.Icc 1 n) (hne : i ≠ j) :
    0 < |alpha n i - alpha n j| :=
  abs_pos.mpr (sub_ne_zero.mpr (alpha_ne_alpha hn hi hj hne))

/-- every inner factor of the Vandermonde product is positive -/
lemma inner_factor_pos {n i j : ℕ} (hn : 1 ≤ n)
    (hi : i ∈ Finset.Icc 1 n) (hj : j ∈ Finset.Icc (i + 1) n) :
    0 < |alpha n i - alpha n j| := by
  have hmemj : j ∈ Finset.Icc 1 n := by
    rw [Finset.mem_Icc] at hj ⊢
    exact ⟨by have h1 : 1 ≤ i := (Finset.mem_Icc.mp hi).1; omega, hj.2⟩
  have hne : i ≠ j := by
    have hij : i + 1 ≤ j := (Finset.mem_Icc.mp hj).1
    omega
  exact alpha_dist_pos hn hi hmemj hne

/-- `rho n x = 0` implies `x` is one of the roots -/
lemma rho_eq_zero_root {n : ℕ} (hn : 1 ≤ n) (x : ℝ) (hx : rho n x = 0) :
    ∃ k : ℕ, k ∈ Finset.Icc 1 n ∧ x = alpha n k := by
  rcases exists_index_rho n hn x with ⟨k, hk, hr⟩
  refine ⟨k, hk, ?_⟩
  have h0 : |x - alpha n k| = 0 := by
    rw [← hr, hx]
  have hsub : x - alpha n k = 0 := abs_eq_zero.mp h0
  linarith

/-- the (finite) set of roots has measure zero -/
lemma roots_null (n : ℕ) (hn : 1 ≤ n) :
    muS {x : ℝ | rho n x = 0} = 0 := by
  have hsub : {x : ℝ | rho n x = 0} ⊆
      {x : ℝ | ∃ k : ℕ, k ∈ Finset.Icc 1 n ∧ x = alpha n k} := by
    intro x hx
    exact rho_eq_zero_root hn x hx
  have h1 : {x : ℝ | ∃ k : ℕ, k ∈ (Finset.Icc 1 n : Set ℕ) ∧ x = alpha n k} =
      (fun k : ℕ => alpha n k) '' ((Finset.Icc 1 n : Set ℕ)) := by
    ext x
    constructor
    · rintro ⟨k, hk, rfl⟩
      exact ⟨k, hk, rfl⟩
    · rintro ⟨k, hk, rfl⟩
      exact ⟨k, hk, rfl⟩
  have hfin : Set.Finite {x : ℝ | ∃ k : ℕ, k ∈ (Finset.Icc 1 n : Set ℕ) ∧ x = alpha n k} := by
    rw [h1]
    exact Set.Finite.image _ (by simp : Set.Finite ((Finset.Icc 1 n : Set ℕ)))
  have hμ : muS {x : ℝ | ∃ k : ℕ, k ∈ (Finset.Icc 1 n : Set ℕ) ∧ x = alpha n k} = 0 := by
    exact Set.Finite.measure_zero hfin muS
  exact measure_mono_null hsub (by simpa [h1] using hμ)

/-- a.e. the distance to the roots is positive -/
lemma rho_pos_ae (n : ℕ) (hn : 1 ≤ n) :
    ∀ᵐ x ∂muS, 0 < rho n x := by
  apply MeasureTheory.mem_ae_iff.mpr
  have hsub : ({x : ℝ | 0 < rho n x})ᶜ ⊆ {x : ℝ | rho n x = 0} := by
    intro x hx
    have hx0 : ¬ 0 < rho n x := by simpa [Set.compl_setOf] using hx
    exact le_antisymm (le_of_not_gt hx0) (rho_nonneg (n := n) x)
  exact measure_mono_null hsub (roots_null n hn)

/-! ### integrability -/

/-- `x ↦ U^μ(x)` is integrable against `muS` (bounded continuous on the
support interval). -/
lemma integrable_logPotential :
    Integrable (fun x : ℝ => logPotential muS (x : ℂ)) muS := by
  let f : ℝ → ℝ := fun x => logPotential muS (x : ℂ)
  have hcont : Continuous f := by
    simpa [f] using logPotential_continuous_real
  have hbdU : BddAbove (f '' (Set.Icc aSerre bSerre)) :=
    isCompact_Icc.bddAbove_image hcont.continuousOn
  have hbdL : BddBelow (f '' (Set.Icc aSerre bSerre)) :=
    isCompact_Icc.bddBelow_image hcont.continuousOn
  rcases hbdU with ⟨M, hM⟩
  rcases hbdL with ⟨m, hm⟩
  have hb : ∀ x ∈ Set.Icc aSerre bSerre, f x ∈ Set.Icc m M := by
    intro x hx
    exact ⟨hm ⟨x, hx, rfl⟩, hM ⟨x, hx, rfl⟩⟩
  have hae : ∀ᵐ x ∂muS, f x ∈ Set.Icc m M := by
    apply MeasureTheory.mem_ae_iff.mpr
    have hsub : {x : ℝ | ¬ f x ∈ Set.Icc m M} ⊆ (Set.Icc aSerre bSerre)ᶜ := by
      intro x hx hxI
      exact hx (hb x hxI)
    have hnull : muS {x : ℝ | ¬ f x ∈ Set.Icc m M} = 0 :=
      measure_mono_null hsub (by simpa using muS_compl_Icc)
    exact hnull
  exact MeasureTheory.Integrable.of_mem_Icc m M hcont.aemeasurable hae

/-- integrability of `log ∘ rho` -/
lemma log_rho_integrable (n : ℕ) (hn : 1 ≤ n) :
    Integrable (fun x : ℝ => Real.log (rho n x)) muS :=
  Submission.EnergyDeliver.log_rho_integrable hn

/-- integrability of `-log |x − c|` -/
lemma log_neg_integrable (c : ℝ) :
    Integrable (fun x : ℝ => -Real.log |x - c|) muS := by
  have h := (log_integrable c).neg
  -- h : Integrable (fun t => -Real.log |c - t|)
  refine MeasureTheory.Integrable.congr h ?_
  exact Filter.Eventually.of_forall (fun x => by simp [abs_sub_comm x c])

/-- integrability of a finite sum of integrable functions -/
lemma integrable_finset_sum_real {ι : Type*} [DecidableEq ι] (f : ι → ℝ → ℝ) :
    ∀ (s : Finset ι), (∀ i ∈ s, Integrable (f i) muS) →
      Integrable (fun x : ℝ => ∑ i ∈ s, f i x) muS := by
  classical
  intro s
  refine Finset.induction_on s ?_ ?_
  · intro h
    simp
  · intro a t hat ih h
    have hpt : (fun x : ℝ => ∑ i ∈ insert a t, f i x)
        = fun x : ℝ => f a x + ∑ i ∈ t, f i x := by
      funext x
      rw [Finset.sum_insert hat]
    rw [hpt]
    exact (h a (Finset.mem_insert_self a t)).add
      (ih (fun i hi => h i (Finset.mem_insert_of_mem hi)))

/-! ### step 3: root-average vs energy -/

/-- `(Σ_k U(α_k)) − n·energy` equals the integral of the discrepancy. -/
lemma Usum_sub_energy_eq_integral (n : ℕ) (hn : 2 ≤ n) :
    Usum n - (n : ℝ) * energy =
      ∫ x : ℝ, ((∑ k ∈ Finset.Icc 1 n, -Real.log |x - alpha n k|)
        - (n : ℝ) * logPotential muS (x : ℂ)) ∂muS := by
  have hf : ∀ k ∈ Finset.Icc 1 n, Integrable
      (fun x : ℝ => -Real.log |x - alpha n k|) muS := by
    intro k hk
    exact log_neg_integrable (alpha n k)
  have h1 : ∀ k ∈ Finset.Icc 1 n, (∫ x : ℝ, -Real.log |x - alpha n k| ∂muS)
      = logPotential muS ((alpha n k : ℝ) : ℂ) := by
    intro k hk
    calc
      (∫ x : ℝ, -Real.log |x - alpha n k| ∂muS)
          = (∫ x : ℝ, -Real.log |alpha n k - x| ∂muS) := by
              apply MeasureTheory.integral_congr_ae
              exact Filter.Eventually.of_forall (fun x => by simp [abs_sub_comm x (alpha n k)])
      _ = logPotential muS ((alpha n k : ℝ) : ℂ) := by
              rw [logPotential_eq_integral_log]
  have hIntA : Integrable
      (fun x : ℝ => (∑ k ∈ Finset.Icc 1 n, -Real.log |x - alpha n k|)) muS := by
    exact integrable_finset_sum_real (fun k x => -Real.log |x - alpha n k|)
      (Finset.Icc 1 n) hf
  have hIntB : Integrable (fun x : ℝ => (n : ℝ) * logPotential muS (x : ℂ)) muS :=
    integrable_logPotential.const_mul (n : ℝ)
  have hsumEq : (∑ k ∈ Finset.Icc 1 n, logPotential muS ((alpha n k : ℝ) : ℂ))
      = (∫ x : ℝ, (∑ k ∈ Finset.Icc 1 n, -Real.log |x - alpha n k|) ∂muS) := by
    rw [MeasureTheory.integral_finset_sum (s := Finset.Icc 1 n)
      (f := fun k x => -Real.log |x - alpha n k|) hf]
    exact Finset.sum_congr rfl (fun k hk => (h1 k hk).symm)
  calc
    Usum n - (n : ℝ) * energy
        = (∑ k ∈ Finset.Icc 1 n, logPotential muS ((alpha n k : ℝ) : ℂ)) - (n : ℝ) * energy := rfl
    _ = (∫ x : ℝ, (∑ k ∈ Finset.Icc 1 n, -Real.log |x - alpha n k|) ∂muS)
        - (n : ℝ) * energy := by rw [hsumEq]
    _ = (∫ x : ℝ, (∑ k ∈ Finset.Icc 1 n, -Real.log |x - alpha n k|) ∂muS)
        - (∫ x : ℝ, (n : ℝ) * logPotential muS (x : ℂ) ∂muS) := by
            congr 1
            rw [MeasureTheory.integral_const_mul]
            rfl
    _ = ∫ x : ℝ, ((∑ k ∈ Finset.Icc 1 n, -Real.log |x - alpha n k|)
        - (n : ℝ) * logPotential muS (x : ℂ)) ∂muS := by
            rw [MeasureTheory.integral_sub hIntA hIntB]

/-- pointwise upper bound of the discrepancy at good points -/
lemma discrepancy_le_of_good (n : ℕ) (hn : 2 ≤ n) (C0 : ℝ)
    (hC0 : ∀ x ∈ Set.Icc aSerre bSerre, 0 < rho n x →
      |(n : ℝ) * logPotential muS (x : ℂ) + Real.log |(approxPoly n).eval x|
          - Real.log (rho n x)| ≤ C0 * Real.log ((n : ℝ) + 2))
    {x : ℝ} (hxI : x ∈ Set.Icc aSerre bSerre) (hxpos : 0 < rho n x) :
    (∑ k ∈ Finset.Icc 1 n, -Real.log |x - alpha n k|)
        - (n : ℝ) * logPotential muS (x : ℂ) ≤
      -Real.log (rho n x) + C0 * Real.log ((n : ℝ) + 2) := by
  have hn1 : 1 ≤ n := by omega
  have hmain := hC0 x hxI hxpos
  have hlogP : Real.log |(approxPoly n).eval x| =
      ∑ k ∈ Finset.Icc 1 n, Real.log |x - alpha n k| := log_abs_eval n hn1 x hxpos
  have hZge : - (C0 * Real.log ((n : ℝ) + 2)) ≤
      (n : ℝ) * logPotential muS (x : ℂ) + Real.log |(approxPoly n).eval x|
        - Real.log (rho n x) := (abs_le.mp hmain).1
  have hZ : Real.log (rho n x) - C0 * Real.log ((n : ℝ) + 2) ≤
      (n : ℝ) * logPotential muS (x : ℂ) + (∑ k ∈ Finset.Icc 1 n, Real.log |x - alpha n k|) := by
    rw [← hlogP]
    linarith
  have hneg : -((n : ℝ) * logPotential muS (x : ℂ) +
      (∑ k ∈ Finset.Icc 1 n, Real.log |x - alpha n k|)) ≤
      -Real.log (rho n x) + C0 * Real.log ((n : ℝ) + 2) := by
    linarith
  have hrewrite : -((n : ℝ) * logPotential muS (x : ℂ) +
      (∑ k ∈ Finset.Icc 1 n, Real.log |x - alpha n k|))
      = (∑ k ∈ Finset.Icc 1 n, -Real.log |x - alpha n k|)
        - (n : ℝ) * logPotential muS (x : ℂ) := by
    rw [neg_add_rev, Finset.sum_neg_distrib]
    ring
  rwa [hrewrite] at hneg

/-- a.e. upper bound of the discrepancy -/
lemma discrepancy_ae_le (n : ℕ) (hn : 2 ≤ n) (C0 : ℝ)
    (hC0 : ∀ x ∈ Set.Icc aSerre bSerre, 0 < rho n x →
      |(n : ℝ) * logPotential muS (x : ℂ) + Real.log |(approxPoly n).eval x|
          - Real.log (rho n x)| ≤ C0 * Real.log ((n : ℝ) + 2)) :
    (fun x : ℝ => (∑ k ∈ Finset.Icc 1 n, -Real.log |x - alpha n k|)
        - (n : ℝ) * logPotential muS (x : ℂ))
      ≤ᵐ[muS]
    (fun x : ℝ => -Real.log (rho n x) + C0 * Real.log ((n : ℝ) + 2)) := by
  apply MeasureTheory.mem_ae_iff.mpr
  have hn1 : 1 ≤ n := by omega
  let D : ℝ → ℝ := fun x => (∑ k ∈ Finset.Icc 1 n, -Real.log |x - alpha n k|)
        - (n : ℝ) * logPotential muS (x : ℂ)
  let R : ℝ → ℝ := fun x => -Real.log (rho n x) + C0 * Real.log ((n : ℝ) + 2)
  have hnull : muS {x : ℝ | ¬ D x ≤ R x} = 0 := by
    have hsub : {x : ℝ | ¬ D x ≤ R x} ⊆
        (Set.Icc aSerre bSerre)ᶜ ∪ {x : ℝ | rho n x = 0} := by
      intro x hx
      by_cases hxI : x ∈ Set.Icc aSerre bSerre
      · by_cases hxpos : 0 < rho n x
        · exfalso
          exact hx (discrepancy_le_of_good n hn C0 hC0 hxI hxpos)
        · right
          exact le_antisymm (le_of_not_gt hxpos) (rho_nonneg (n := n) x)
      · left
        exact hxI
    have hc : muS ((Set.Icc aSerre bSerre)ᶜ) = 0 := by simpa using muS_compl_Icc
    have hr : muS {x : ℝ | rho n x = 0} = 0 := roots_null n hn1
    have hu : muS ((Set.Icc aSerre bSerre)ᶜ ∪ {x : ℝ | rho n x = 0}) = 0 :=
      MeasureTheory.measure_union_null hc hr
    exact measure_mono_null hsub hu
  change muS {x : ℝ | ¬ D x ≤ R x} = 0
  exact hnull

/-- step 3: `Σ_k U^μ(α_k) ≤ n·energy + C·log(n+2)` -/
lemma root_potential_upper :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 2 ≤ n →
      (∑ k ∈ Finset.Icc 1 n, logPotential muS ((alpha n k : ℝ) : ℂ)) ≤
        (n : ℝ) * energy + C * Real.log ((n : ℝ) + 2) := by
  rcases approx_potential_bound with ⟨C0, hC0pos, hC0⟩
  rcases Submission.EnergyDeliver.deliver_me with ⟨C1, hC1pos, hC1⟩
  refine ⟨C0 + C1 + 1, by positivity, ?_⟩
  intro n hn
  have hn1 : 1 ≤ n := by omega
  let c : ℝ := C0 * Real.log ((n : ℝ) + 2)
  let hC0' : ∀ x ∈ Set.Icc aSerre bSerre, 0 < rho n x →
      |(n : ℝ) * logPotential muS (x : ℂ) + Real.log |(approxPoly n).eval x|
          - Real.log (rho n x)| ≤ C0 * Real.log ((n : ℝ) + 2) := by
    intro x hxI hr
    exact hC0 n hn x hxI hr
  have hD_int : Integrable
      (fun x : ℝ => (∑ k ∈ Finset.Icc 1 n, -Real.log |x - alpha n k|)
        - (n : ℝ) * logPotential muS (x : ℂ)) muS := by
    have hA : Integrable
        (fun x : ℝ => (∑ k ∈ Finset.Icc 1 n, -Real.log |x - alpha n k|)) muS := by
      refine integrable_finset_sum_real (fun k x => -Real.log |x - alpha n k|)
        (Finset.Icc 1 n) ?_
      intro k hk
      exact log_neg_integrable (alpha n k)
    have hB : Integrable (fun x : ℝ => (n : ℝ) * logPotential muS (x : ℂ)) muS :=
      integrable_logPotential.const_mul (n : ℝ)
    exact hA.sub hB
  have hR_int : Integrable
      (fun x : ℝ => -Real.log (rho n x) + C0 * Real.log ((n : ℝ) + 2)) muS := by
    have hL : Integrable (fun x : ℝ => Real.log (rho n x)) muS := log_rho_integrable n hn1
    have hConst : Integrable (fun x : ℝ => C0 * Real.log ((n : ℝ) + 2)) muS :=
      MeasureTheory.integrable_const (C0 * Real.log ((n : ℝ) + 2))
    exact hL.neg.add hConst
  have him := MeasureTheory.integral_mono_ae hD_int hR_int (discrepancy_ae_le n hn C0 hC0')
  have hid := Usum_sub_energy_eq_integral n hn
  have hcalc : (∫ x : ℝ, (-Real.log (rho n x) + C0 * Real.log ((n : ℝ) + 2)) ∂muS)
      = -(∫ x : ℝ, Real.log (rho n x) ∂muS) + C0 * Real.log ((n : ℝ) + 2) := by
    let cval : ℝ := C0 * Real.log ((n : ℝ) + 2)
    have hsplit : (fun x : ℝ => -Real.log (rho n x) + C0 * Real.log ((n : ℝ) + 2))
        = (fun x : ℝ => -Real.log (rho n x)) + (fun _ : ℝ => cval) := rfl
    have hnegI : Integrable (fun x : ℝ => -Real.log (rho n x)) muS :=
      (log_rho_integrable n hn1).neg
    have hconstI : Integrable (fun _ : ℝ => cval) muS := by
      simpa [cval] using (MeasureTheory.integrable_const cval)
    have h2 : (∫ x : ℝ, cval ∂muS) = cval := by
      rw [MeasureTheory.integral_const]
      rw [smul_eq_mul]
      rw [MeasureTheory.Measure.real_def]
      rw [muS_univ]
      norm_num
    calc
      (∫ x : ℝ, (-Real.log (rho n x) + C0 * Real.log ((n : ℝ) + 2)) ∂muS)
          = (∫ x : ℝ, (-Real.log (rho n x) + cval) ∂muS) := rfl
      _ = (∫ x : ℝ, -Real.log (rho n x) ∂muS) + (∫ x : ℝ, cval ∂muS) := by
            rw [hsplit]
            exact MeasureTheory.integral_add hnegI hconstI
      _ = -(∫ x : ℝ, Real.log (rho n x) ∂muS) + C0 * Real.log ((n : ℝ) + 2) := by
            rw [MeasureTheory.integral_neg]
            simpa [cval] using h2
  have hneg : -(∫ x : ℝ, Real.log (rho n x) ∂muS) ≤ C1 * Real.log ((n : ℝ) + 2) := by
    have hDeliver : -C1 * Real.log ((n : ℝ) + 2) ≤ (∫ x : ℝ, Real.log (rho n x) ∂muS) := hC1 n hn
    linarith
  have hstep : Usum n - (n : ℝ) * energy ≤ (C0 + C1) * Real.log ((n : ℝ) + 2) := by
    rw [hid]
    calc
      (∫ x : ℝ, ((∑ k ∈ Finset.Icc 1 n, -Real.log |x - alpha n k|)
            - (n : ℝ) * logPotential muS (x : ℂ)) ∂muS) ≤
          (∫ x : ℝ, (-Real.log (rho n x) + C0 * Real.log ((n : ℝ) + 2)) ∂muS) := him
      _ = -(∫ x : ℝ, Real.log (rho n x) ∂muS) + C0 * Real.log ((n : ℝ) + 2) := hcalc
      _ ≤ C1 * Real.log ((n : ℝ) + 2) + C0 * Real.log ((n : ℝ) + 2) := by linarith
      _ = (C0 + C1) * Real.log ((n : ℝ) + 2) := by ring
  have hlogpos : 0 ≤ Real.log ((n : ℝ) + 2) := by
    have h4 : (4 : ℝ) ≤ (n : ℝ) + 2 := by exact_mod_cast (by omega : (4 : ℕ) ≤ n + 2)
    exact le_trans (le_of_lt (Real.log_pos (by norm_num))) (Real.log_le_log (by norm_num) h4)
  have hfinal : Usum n ≤ (n : ℝ) * energy + (C0 + C1 + 1) * Real.log ((n : ℝ) + 2) := by
    nlinarith
  change (∑ k ∈ Finset.Icc 1 n, logPotential muS ((alpha n k : ℝ) : ℂ)) ≤
      (n : ℝ) * energy + (C0 + C1 + 1) * Real.log ((n : ℝ) + 2)
  simpa [Usum] using hfinal

/-! ### step 2: sum of the root bounds -/

/-- Sum of the root bounds: `|n·ΣU + 2·log V| ≤ n·C·log(n+2)`. -/
lemma root_sum_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 2 ≤ n →
      |(n : ℝ) * Usum n + 2 * logV n| ≤ (n : ℝ) * C * Real.log ((n : ℝ) + 2) := by
  rcases Submission.EnergyRootBound.root_bound with ⟨C0, hC0pos, hC0⟩
  refine ⟨C0, hC0pos, ?_⟩
  intro n hn
  let L : ℝ := Real.log ((n : ℝ) + 2)
  let term : ℕ → ℝ := fun k => (n : ℝ) * logPotential muS ((alpha n k : ℝ) : ℂ)
      + ∑ j ∈ (Finset.Icc 1 n).erase k, Real.log |alpha n k - alpha n j|
  have hterm : ∀ k ∈ Finset.Icc 1 n, |term k| ≤ C0 * L := by
    intro k hk
    simpa [term, L] using hC0 n hn k hk
  have hsumT : (∑ k ∈ Finset.Icc 1 n, term k) = (n : ℝ) * Usum n + 2 * logV n := by
    have hlin : (∑ k ∈ Finset.Icc 1 n, (n : ℝ) * logPotential muS ((alpha n k : ℝ) : ℂ))
        = (n : ℝ) * Usum n := by
      calc
        (∑ k ∈ Finset.Icc 1 n, (n : ℝ) * logPotential muS ((alpha n k : ℝ) : ℂ))
            = (∑ k ∈ Finset.Icc 1 n, logPotential muS ((alpha n k : ℝ) : ℂ) * (n : ℝ)) := by
              apply Finset.sum_congr rfl
              intro k hk
              rw [mul_comm]
        _ = (∑ k ∈ Finset.Icc 1 n, logPotential muS ((alpha n k : ℝ) : ℂ)) * (n : ℝ) := by
              exact (Finset.sum_mul (Finset.Icc 1 n)
                (fun k => logPotential muS ((alpha n k : ℝ) : ℂ)) (n : ℝ)).symm
        _ = (n : ℝ) * Usum n := by
              rw [mul_comm]
              rfl
    have hpair : (∑ k ∈ Finset.Icc 1 n, ∑ j ∈ (Finset.Icc 1 n).erase k,
        Real.log |alpha n k - alpha n j|) = 2 * logV n := by
      dsimp [logV]
      exact Submission.EnergyPairs.erase_sum_eq_two_lt_sum n
    calc
      (∑ k ∈ Finset.Icc 1 n, term k)
          = (∑ k ∈ Finset.Icc 1 n, (n : ℝ) * logPotential muS ((alpha n k : ℝ) : ℂ))
            + (∑ k ∈ Finset.Icc 1 n, ∑ j ∈ (Finset.Icc 1 n).erase k,
                Real.log |alpha n k - alpha n j|) := by
              dsimp [term]
              rw [Finset.sum_add_distrib]
      _ = (n : ℝ) * Usum n + 2 * logV n := by
              rw [hlin, hpair]
  have hsumabs : (∑ k ∈ Finset.Icc 1 n, |term k|) ≤ (n : ℝ) * (C0 * L) := by
    calc
      (∑ k ∈ Finset.Icc 1 n, |term k|)
          ≤ (∑ k ∈ Finset.Icc 1 n, C0 * L) := by
            apply Finset.sum_le_sum
            intro k hk
            exact hterm k hk
      _ = (n : ℝ) * (C0 * L) := by
            rw [Finset.sum_const]
            rw [Icc_one_n_card n]
            simp
  have habsall : |∑ k ∈ Finset.Icc 1 n, term k| ≤ (∑ k ∈ Finset.Icc 1 n, |term k|) := by
    exact Finset.abs_sum_le_sum_abs term (Finset.Icc 1 n)
  have hfinal : |(n : ℝ) * Usum n + 2 * logV n| ≤ (n : ℝ) * C0 * Real.log ((n : ℝ) + 2) := by
    rw [← hsumT]
    calc
      |∑ k ∈ Finset.Icc 1 n, term k| ≤ (∑ k ∈ Finset.Icc 1 n, |term k|) := habsall
      _ ≤ (n : ℝ) * (C0 * L) := hsumabs
      _ = (n : ℝ) * C0 * L := by ring
  simpa [L] using hfinal

/-! ### Vandermonde product and its log -/

/-- `Vprod n` is positive -/
lemma Vprod_pos (n : ℕ) (hn : 1 ≤ n) : 0 < Vprod n := by
  unfold Vprod
  refine Finset.prod_pos ?_
  intro i hi
  refine Finset.prod_pos ?_
  intro j hj
  exact inner_factor_pos hn hi hj

/-- `log (Vprod n) = logV n` -/
lemma log_Vprod (n : ℕ) (hn : 1 ≤ n) : Real.log (Vprod n) = logV n := by
  unfold Vprod logV
  have hinner : ∀ i ∈ Finset.Icc 1 n,
      0 < ∏ j ∈ Finset.Icc (i + 1) n, |alpha n i - alpha n j| := by
    intro i hi
    refine Finset.prod_pos ?_
    intro j hj
    exact inner_factor_pos hn hi hj
  calc
    Real.log (∏ i ∈ Finset.Icc 1 n, (∏ j ∈ Finset.Icc (i + 1) n, |alpha n i - alpha n j|))
        = ∑ i ∈ Finset.Icc 1 n,
            Real.log (∏ j ∈ Finset.Icc (i + 1) n, |alpha n i - alpha n j|) := by
            apply Real.log_prod
            intro i hi
            exact ne_of_gt (hinner i hi)
    _ = ∑ i ∈ Finset.Icc 1 n, ∑ j ∈ Finset.Icc (i + 1) n,
            Real.log |alpha n i - alpha n j| := by
            apply Finset.sum_congr rfl
            intro i hi
            apply Real.log_prod
            intro j hj
            exact ne_of_gt (inner_factor_pos hn hi hj)

/-- `log(n+2) ≤ 2·log n` for `n ≥ 2`. -/
lemma log_np2_le_two_log_n {n : ℕ} (hn : 2 ≤ n) :
    Real.log ((n : ℝ) + 2) ≤ 2 * Real.log (n : ℝ) := by
  have hnpos : 0 < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
  have hsq : (n : ℝ) + 2 ≤ (n : ℝ) * (n : ℝ) := by
    have hn2 : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    nlinarith
  have h1 := Real.log_le_log (by linarith : 0 < (n : ℝ) + 2) hsq
  have h2 : Real.log ((n : ℝ) * (n : ℝ)) = 2 * Real.log (n : ℝ) := by
    rw [Real.log_mul (by positivity : (n : ℝ) ≠ 0) (by positivity : (n : ℝ) ≠ 0)]
    ring
  rwa [h2] at h1


/-- `eq:deliver_me`: the μ-average of `log ρ_n` is bounded below by
`−O(log n)` (proved in `Submission.EnergyDeliver`). -/
theorem deliver_me :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 2 ≤ n →
      -C * Real.log ((n : ℝ) + 2) ≤
        ∫ x : ℝ, Real.log (Submission.ThreePages.rho n x) ∂muS := by
  exact Submission.EnergyDeliver.deliver_me

/-- `eq:energy_approx`: the Vandermonde product of the quantile roots is
bounded below by `n^{−C·n}·exp(−(1/2)n²·energy)`. -/
theorem energy_half :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 2 ≤ n →
      (n : ℝ) ^ (-C * (n : ℝ)) *
          Real.exp (-(1 / 2 : ℝ) * (n : ℝ) ^ 2 * energy) ≤
        ∏ i ∈ Finset.Icc 1 n, ∏ j ∈ Finset.Icc (i + 1) n,
          |alpha n i - alpha n j| := by
  rcases root_sum_bound with ⟨CA, hCA, hAb⟩
  rcases root_potential_upper with ⟨CB, hCB, hBb⟩
  refine ⟨CA + CB + 2, by positivity, ?_⟩
  intro n hn
  let E : ℝ := -(1 / 2 : ℝ) * (n : ℝ) ^ 2 * energy
  let L : ℝ := Real.log ((n : ℝ) + 2)
  let B : ℝ := -(1 / 2 : ℝ) * (n : ℝ) * (CA + CB) * L
  let A : ℝ := -(CA + CB + 2) * (n : ℝ) * Real.log (n : ℝ)
  have hn1 : 1 ≤ n := by omega
  have hnpos : 0 < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
  have hnn : 0 ≤ (n : ℝ) := le_of_lt hnpos
  have hnpos1 : (1 : ℝ) < (n : ℝ) := by exact_mod_cast (by omega : 1 < n)
  have hlogpos0 : 0 < Real.log (n : ℝ) := Real.log_pos hnpos1
  have hlogpos : 0 ≤ Real.log (n : ℝ) := le_of_lt hlogpos0
  have hCAB0 : 0 ≤ CA + CB := by linarith
  have hVpos : 0 < Vprod n := Vprod_pos n hn1
  -- 2·logV ≥ −n²energy − n(CA+CB)·L  (from the summed root bounds + step 3)
  have hVlow : E + B ≤ logV n := by
    have h1e : -(n : ℝ) * CA * Real.log ((n : ℝ) + 2) ≤
        (n : ℝ) * Usum n + 2 * logV n := by
      have hh := (abs_le.mp (hAb n hn)).1
      simpa [L] using hh
    have h2e : (n : ℝ) * Usum n ≤
        (n : ℝ) * ((n : ℝ) * energy) + (n : ℝ) * (CB * Real.log ((n : ℝ) + 2)) := by
      have hm := mul_le_mul_of_nonneg_left (hBb n hn) hnn
      have hm2 : (n : ℝ) * ((n : ℝ) * energy + CB * Real.log ((n : ℝ) + 2))
          = (n : ℝ) * ((n : ℝ) * energy) + (n : ℝ) * (CB * Real.log ((n : ℝ) + 2)) := by ring
      rwa [hm2] at hm
    have hs2 : (n : ℝ) ^ 2 = (n : ℝ) * (n : ℝ) := by ring
    dsimp [E, B, L]
    rw [hs2]
    nlinarith
  have hVexp : Real.exp (E + B) ≤ Vprod n := by
    have h0 := Real.exp_le_exp.mpr hVlow
    have h1 : Real.exp (E + B) ≤ Real.exp (logV n) := h0
    have h2 : Real.exp (logV n) = Vprod n := by
      rw [← log_Vprod n hn1]
      exact Real.exp_log hVpos
    rw [h2] at h1
    exact h1
  -- A ≤ B  (so exp A ≤ exp B)
  have hAB : A ≤ B := by
    dsimp [A, B]
    have hLle : Real.log ((n : ℝ) + 2) ≤ 2 * Real.log (n : ℝ) := log_np2_le_two_log_n hn
    have hmid : (1 / 2 : ℝ) * (CA + CB) * Real.log ((n : ℝ) + 2)
        ≤ (CA + CB) * Real.log (n : ℝ) := by
      have hm := mul_le_mul_of_nonneg_left hLle (mul_nonneg (by norm_num : 0 ≤ (1 / 2 : ℝ)) hCAB0)
      have hmr : (1 / 2 : ℝ) * (CA + CB) * (2 * Real.log (n : ℝ))
          = (CA + CB) * Real.log (n : ℝ) := by ring
      nlinarith
    have hmid2 : (1 / 2 : ℝ) * (CA + CB) * Real.log ((n : ℝ) + 2)
        ≤ (CA + CB + 2) * Real.log (n : ℝ) := by
      nlinarith
    have hmul := mul_le_mul_of_nonneg_left hmid2 (le_of_lt hnpos)
    nlinarith
  have hpow : (n : ℝ) ^ (-(CA + CB + 2) * (n : ℝ)) = Real.exp A := by
    dsimp [A]
    rw [Real.rpow_def_of_pos hnpos]
    congr 1
    ring
  have hchain1 : Real.exp A * Real.exp E ≤ Real.exp (E + B) := by
    have h1 : Real.exp A ≤ Real.exp B := Real.exp_le_exp.mpr hAB
    have hm := mul_le_mul_of_nonneg_right h1 (le_of_lt (Real.exp_pos E))
    have hxy : Real.exp B * Real.exp E = Real.exp (E + B) := by
      rw [mul_comm]
      rw [← Real.exp_add]
    rwa [hxy] at hm
  have hres : (n : ℝ) ^ (-(CA + CB + 2) * (n : ℝ)) * Real.exp E ≤ Vprod n := by
    calc
      (n : ℝ) ^ (-(CA + CB + 2) * (n : ℝ)) * Real.exp E
          = Real.exp A * Real.exp E := by rw [hpow]
      _ ≤ Real.exp (E + B) := hchain1
      _ ≤ Vprod n := hVexp
  simpa [Vprod, E] using hres

end Submission.EnergyHalf
