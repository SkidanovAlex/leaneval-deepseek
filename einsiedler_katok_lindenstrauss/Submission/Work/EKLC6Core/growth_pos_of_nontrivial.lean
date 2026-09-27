import Mathlib
import Submission.Work.EKLC6Core.Basic
import Submission.Work.EKLC6Core.Covariant
import Submission.Work.EKLC6Core.conjBox_nhds
import Submission.Work.EKLC6Core.conjBox_measurable
import Submission.Work.EKLContract.Interfaces
import Submission.Work.EKLProd.aDiag_nsmul
import Submission.Work.EKLC6Core.conjBox_nsmul_mass
import Submission.Work.EKLC6Core.dirac_of_mass
import Submission.Work.EKLC6Core.box_facts

/-!
# `Work.EKLC6Core.growth_pos_of_nontrivial`

Pisa 7.39 / Theorem 7.6(iii), in the form needed by the C6 assembly: if the leaf-wise measures
are non-trivial a.e. (`ν x ≠ δ_1`), then the entropy contribution
`∫ growthFun U ν t = ∫ -log ν x (conjBox U t)` is **strictly positive**.

The proof is the contrapositive and is elementary (no σ-algebras): the contraction hypothesis
forces `conjBox U t ⊆ Box1 U`, hence `growthFun ≥ 0` on `X'`; if the integral vanishes then
`ν x (conjBox U t) = 1` a.e., the telescoping identities (`covariant_mul` and its mirror
`conjBox_nsmul_mass`) propagate this to `ν x (conjBox U (±n t)) = 1` for all `n`, and since
`conjBox U (-n t) ↑ U` while `conjBox U (n t) ↓ {1}` the leaf-wise measure is forced to be
`δ_1`, contradicting `hnontriv`.
-/

open MeasureTheory Filter Topology
open scoped ENNReal
open LeanEval.Dynamics.EinsiedlerKatokLindenstrauss

set_option linter.unusedVariables false

noncomputable section

namespace Work.EKLC6Core

open Work.EKLContract

/-! ## The main theorem -/

theorem growth_pos_of_nontrivial {μ : MeasureTheory.Measure Work.EKLContract.X3}
    [MeasureTheory.IsProbabilityMeasure μ] {U : Subgroup Work.EKLContract.SL3}
    {ν : Work.EKLContract.X3 → MeasureTheory.Measure Work.EKLContract.SL3}
    {X' X'' : Set Work.EKLContract.X3}
    (hL : Work.EKLContract.IsLeafwise μ U ν X') (hU : Work.EKLContract.IsHoro U)
    (hcov : Work.EKLC6Core.ACovariant ν X'') (hX'' : μ (X''ᶜ) = 0) (t : Fin 3 → ℝ)
    (hcontr : ∀ u ∈ U, Filter.Tendsto
      (fun n : ℕ => Work.EKLContract.aDiag t ^ n * u * (Work.EKLContract.aDiag t ^ n)⁻¹)
      Filter.atTop (nhds 1))
    (hAinv : Work.EKLContract.IsAInvariant μ)
    (hnontriv : ∀ᵐ x ∂μ, ν x ≠ MeasureTheory.Measure.dirac 1)
    (hmeas : Measurable (Work.EKLC6Core.growthFun U ν t))
    (hint : MeasureTheory.Integrable (Work.EKLC6Core.growthFun U ν t) μ) :
    0 < ∫ x, Work.EKLC6Core.growthFun U ν t x ∂μ := by
  have hBox : ∀ w : Fin 3 → ℝ, MeasurableSet (conjBox U w) := fun w => conjBox_measurable hU w
  have hBox1 : MeasurableSet (Box1 U) := measurableSet_box1 hU
  obtain ⟨hsub, hmono, hanti, hunion, hinter⟩ := box_facts hU hcontr
  have hX'ae : ∀ᵐ x ∂μ, x ∈ X' := by rw [ae_iff]; exact hL.conull
  have hX''ae : ∀ᵐ x ∂μ, x ∈ X'' := by rw [ae_iff]; exact hX''
  have hRle : ∀ x ∈ X', ν x (conjBox U t) ≤ 1 := by
    intro x hx
    rw [← hL.normalised x hx]
    exact measure_mono hsub
  have hgfnn : ∀ x ∈ X', 0 ≤ growthFun U ν t x := by
    intro x hx
    have htoReal : (ν x (conjBox U t)).toReal ≤ 1 := by
      have h1 := ENNReal.toReal_mono (by norm_num : (1 : ℝ≥0∞) ≠ ⊤) (hRle x hx)
      simpa using h1
    rw [growthFun, neg_nonneg]
    exact Real.log_nonpos ENNReal.toReal_nonneg htoReal
  have hnn : 0 ≤ᵐ[μ] growthFun U ν t := by
    filter_upwards [hX'ae] with x hx using hgfnn x hx
  by_contra hlt
  have hzero : ∫ x, growthFun U ν t x ∂μ = 0 :=
    le_antisymm (not_lt.mp hlt) (integral_nonneg_of_ae hnn)
  have hgf0 : growthFun U ν t =ᵐ[μ] 0 :=
    (integral_eq_zero_iff_of_nonneg_ae hnn hint).mp hzero
  have hG1 : ∀ᵐ y ∂μ, y ∈ X' ∩ X'' ∧ ν y (conjBox U t) = 1 := by
    have hbwdae : ∀ᵐ y ∂μ, aDiag (-t) • y ∈ X' ∩ X'' := by
      have h1 : ∀ᵐ y ∂μ, aDiag (-t) • y ∈ X' :=
        ((hAinv (-t)).quasiMeasurePreserving).ae hX'ae
      have h2 : ∀ᵐ y ∂μ, aDiag (-t) • y ∈ X'' :=
        ((hAinv (-t)).quasiMeasurePreserving).ae hX''ae
      exact h1.and h2
    filter_upwards [hX'ae, hX''ae, hbwdae, hgf0] with y hy' hy'' hyb hy0
    have hRne0 : ν y (conjBox U t) ≠ 0 := by
      have hstep := covariant_step hL hcov hBox1 t ⟨hy', hy''⟩ ⟨hyb.1, hyb.2⟩
        (C := conjBox U (-t)) (hBox (-t))
      have hconj : conjBy t (conjBox U (-t)) = Box1 U := by
        rw [conjBy_conjBox]
        have h0 : t + -t = (0 : Fin 3 → ℝ) := by funext i; simp
        rw [h0, conjBox_zero]
      rw [hconj, hL.normalised y hy'] at hstep
      intro hzero'
      rw [hzero', mul_zero] at hstep
      exact zero_ne_one hstep
    refine ⟨⟨hy', hy''⟩, ?_⟩
    have htoReal : (ν y (conjBox U t)).toReal = 1 := by
      refine Real.eq_one_of_pos_of_log_eq_zero ?_ ?_
      · exact ENNReal.toReal_pos hRne0 (ne_of_lt (lt_of_le_of_lt (hRle y hy') ENNReal.one_lt_top))
      · simpa [growthFun] using hy0
    rw [← ENNReal.toReal_eq_one_iff]
    exact htoReal
  have hGood : ∀ᵐ x ∂μ,
      (∀ j : ℕ, aDiag (((j : ℝ)) • t) • x ∈ X' ∩ X'' ∧
        ν (aDiag (((j : ℝ)) • t) • x) (conjBox U t) = 1) ∧
      (∀ j : ℕ, aDiag (-(((j : ℝ)) • t)) • x ∈ X' ∩ X'' ∧
        ν (aDiag (-(((j : ℝ)) • t)) • x) (conjBox U t) = 1) := by
    have h1 : ∀ j : ℕ, ∀ᵐ x ∂μ, aDiag (((j : ℝ)) • t) • x ∈ X' ∩ X'' ∧
        ν (aDiag (((j : ℝ)) • t) • x) (conjBox U t) = 1 := fun j =>
      ((hAinv (((j : ℝ)) • t)).quasiMeasurePreserving).ae hG1
    have h2 : ∀ j : ℕ, ∀ᵐ x ∂μ, aDiag (-(((j : ℝ)) • t)) • x ∈ X' ∩ X'' ∧
        ν (aDiag (-(((j : ℝ)) • t)) • x) (conjBox U t) = 1 := fun j =>
      ((hAinv (-(((j : ℝ)) • t))).quasiMeasurePreserving).ae hG1
    exact (eventually_countable_forall.mpr h1).and (eventually_countable_forall.mpr h2)
  have hcontra : ∀ᵐ x ∂μ, ν x = Measure.dirac 1 := by
    filter_upwards [hGood] with x hx
    have hfwd := hx.1
    have hbwd := hx.2
    have hxX' : x ∈ X' := by
      have h := (hfwd 0).1.1
      simpa [aDiag_zero] using h
    have hExp : ∀ n : ℕ, ν x (conjBox U (-(((n : ℝ)) • t))) = 1 := by
      intro n
      have horbit : ∀ j : ℕ, j ≤ n + 2 → aDiag (((j : ℝ)) • t) • x ∈ X' ∩ X'' :=
        fun j _ => (hfwd j).1
      have h := covariant_mul hL hcov hBox t n x horbit
      have hprod : (∏ j ∈ Finset.range n,
          ν (aDiag ((((j : ℝ)) + 1) • t) • x) (conjBox U t)) = 1 := by
        refine Finset.prod_eq_one (fun j _ => ?_)
        have hv : (((j : ℝ)) + 1) = (((j + 1 : ℕ) : ℝ)) := by push_cast; ring
        rw [hv]
        exact (hfwd (j + 1)).2
      rw [hprod, mul_one] at h
      exact h
    have hShr : ∀ n : ℕ, ν x (conjBox U (((n : ℝ)) • t)) = 1 := by
      intro n
      have h := conjBox_nsmul_mass hL hcov hBox t n x (fun j _ => (hbwd j).1)
      have hprod : (∏ j ∈ Finset.range n,
          ν (aDiag (-(((j : ℝ)) • t)) • x) (conjBox U t)) = 1 :=
        Finset.prod_eq_one (fun j _ => (hbwd j).2)
      rw [hprod] at h
      exact h
    have hmassU : ν x (U : Set SL3) = 1 := by
      rw [← hunion, hmono.measure_iUnion]
      rw [show (⨆ n : ℕ, ν x (conjBox U (-(((n : ℝ)) • t)))) = 1 from by
        simp [hExp]]
    have hone : ν x ({1} : Set SL3) = 1 := by
      have hfin : ∃ i : ℕ, ν x (conjBox U (((i : ℝ)) • t)) ≠ ⊤ :=
        ⟨0, by
          rw [Nat.cast_zero, zero_smul, conjBox_zero, hL.normalised x hxX']
          exact ENNReal.one_ne_top⟩
      rw [← hinter, hanti.measure_iInter (fun n => (hBox _).nullMeasurableSet) hfin]
      rw [show (⨅ n : ℕ, ν x (conjBox U (((n : ℝ)) • t))) = 1 from by
        simp [hShr]]
    exact dirac_of_mass (hL.carried x hxX') hmassU hone
  have hfalse : ∀ᵐ x ∂μ, False := (hcontra.and hnontriv).mono (fun x h => h.2 h.1)
  have hμ0 : μ Set.univ = 0 := by simpa using (ae_iff.mp hfalse)
  rw [measure_univ] at hμ0
  exact one_ne_zero hμ0

end Work.EKLC6Core
