import ChallengeDeps
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Submission.Work.BoseFixB1S.BoxSpectralDefs
import Submission.Work.BoseFixB1S.FlatFib.flatFibSumEqZero
import Submission.Work.BoseFixB1S.boxPInd_fib_collapse
import Submission.Work.BoseFixB1S.integrableOn_chiSmallB_pow_dlBox
import Submission.Work.BoseFixB1S.mfFewFlatCornerStep1
import Submission.Work.SlotWord.chiSmallB_support_mem_dlBox
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixB1S.flatFibreMeanFieldB1Oper` — the flat fibre identity, non-degenerate box

A copy of `Submission/Work/BoseFixB1S/flatFibreMeanFieldB1.lean` with

* the import of `Submission.Work.BoseFixB1.flatAuxW` **removed** (that module's cone reaches
  `Submission.Work.BoseFixB1S.perBoxCrudeLowerB1`, so importing it would couple this module to an
  in-progress file of another area), and
* the corresponding `by_cases hvol0 : volA = 0` branch replaced by the hypothesis
  `hvol : boxMass ℓ d u ≠ 0` (the only two uses of `flatAuxW` were in that branch).

The hypothesis `hvol` holds in every application here: the target's good-set gives
`1 ≤ μ · boxMass` (`Work.BoseFixB1.SectorAux.one_le_mu_boxMassGood`).  Nothing else is changed.
-/

noncomputable section

open MeasureTheory Metric Filter
open scoped Topology Real BigOperators ENNReal

namespace Work.BoseFixB1S

open Submission.BoseGases Work.SmallBoxSliding Work.UBBInputs8

local notation "E3" => EuclideanSpace ℝ (Fin 3)

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 2000000

theorem flatFibreMeanFieldB1Oper {v : EuclideanSpace ℝ (Fin 3) → ℝ} (h : Work.UBB.ScatSol v)
    {M : ℕ} (hM : 1 ≤ M) {ℓ d : ℝ} (hℓ : 0 < ℓ) (hd : 0 < d)
    (u : EuclideanSpace ℝ (Fin 3)) {n : ℕ} {Φ : Submission.BoseGases.X n → ℝ}
    (hvol : Work.SmallBoxSliding.boxMass ℓ d u ≠ 0)
    (hΦc : Continuous Φ)
    (hflat : Work.UBBInputs8.cnPlusBoxInd ℓ (Submission.BoseGases.dlBox ℓ d u)
      (Work.SmallBoxSliding.boxMass ℓ d u) Φ = 0)
    (hint : MeasureTheory.IntegrableOn
      (fun x : Submission.BoseGases.X n => (Φ x) ^ 2 * ∑ i : Fin n,
        ∫ y in Submission.BoseGases.acube ℓ,
          Submission.BoseGases.wSmall1Pair h M ℓ d u (x i) y)
      (Submission.BoseGases.abox n ℓ)) :
    Work.BoseFixB1.flatFibSum h M ℓ d u Φ
      = (Work.BoseFixB1.w1MassB h M ℓ d u / Work.SmallBoxSliding.chiMass M ℓ d u)
        * Work.BoseFixB1.flatScountB M ℓ d u Φ := by
  classical
  set A : Set E3 := Submission.BoseGases.dlBox ℓ d u with hAdef
  set volA : ℝ := Work.SmallBoxSliding.boxMass ℓ d u with hvolAdef
  set fib : E3 → ℝ :=
    (fun z => ∫ y in Submission.BoseGases.acube ℓ,
      Submission.BoseGases.wSmall1Pair h M ℓ d u z y) with hfibdef
  have hAmeas : MeasurableSet A := by
    rw [hAdef]; exact Work.SmallBoxSliding.measurableSet_dlBox ℓ d u
  have hAc : A ⊆ Submission.BoseGases.acube ℓ := by
    rw [hAdef]; exact Work.SmallBoxSliding.dlBox_subset_acube ℓ d u
  have hVOL : volA = (MeasureTheory.volume A).toReal := by
    rw [hvolAdef, hAdef, Work.SmallBoxSliding.boxMass_eq_measureReal,
      MeasureTheory.Measure.real_def]
  have hVOLreal : volA = (MeasureTheory.volume : MeasureTheory.Measure E3).real A :=
    hVOL.trans (MeasureTheory.Measure.real_def (MeasureTheory.volume) A).symm
  have hfib_off : ∀ z : E3, z ∉ A → fib z = 0 := by
    intro z hz
    have hz' : z ∉ Submission.BoseGases.dlBox ℓ d u := by rw [← hAdef]; exact hz
    have h0 : (fun y : E3 => Submission.BoseGases.wSmall1Pair h M ℓ d u z y)
        = fun _ => (0 : ℝ) :=
      funext (fun y => Work.BoseFixB1S.wSmall1Pair_eq_zero_of_notMem_left hM hℓ hd u y hz')
    show (∫ y in Submission.BoseGases.acube ℓ, Submission.BoseGases.wSmall1Pair h M ℓ d u z y) = 0
    rw [h0]
    simp
  have hfib_ind : ∀ z : E3, A.indicator fib z = fib z := by
    intro z
    by_cases hz : z ∈ A
    · rw [Set.indicator_of_mem hz]
    · rw [Set.indicator_of_notMem hz, hfib_off z hz]
  have hfib_ind1 : ∀ z : E3, A.indicator (fun _ => (1 : ℝ)) z * fib z = fib z := by
    intro z
    by_cases hz : z ∈ A
    · rw [Set.indicator_of_mem hz, one_mul]
    · rw [Set.indicator_of_notMem hz, zero_mul, hfib_off z hz]
  have hfib_int : (∫ z in A, fib z) = Work.BoseFixB1.w1MassB h M ℓ d u := by
    rw [hAdef]
    have hinner : ∀ x : E3, (∫ y in Submission.BoseGases.acube ℓ,
          Submission.BoseGases.wSmall1Pair h M ℓ d u x y)
        = ∫ y : E3, Submission.BoseGases.wSmall1Pair h M ℓ d u x y := by
      intro x
      refine MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero (fun y hy => ?_)
      by_contra hne
      exact hy (Work.SmallBoxSliding.dlBox_subset_acube ℓ d u
        (by
          by_contra hmem
          exact hne (Work.BoseFixB1S.wSmallPair_eq_zero_of_notMem_right hM hℓ hd u
            (Submission.BoseGases.g0 v h) x hmem)))
    rw [show fib = fun x : E3 => ∫ y in Submission.BoseGases.acube ℓ,
        Submission.BoseGases.wSmall1Pair h M ℓ d u x y from hfibdef]
    rw [MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall hinner)]
    exact Work.BoseFixB1S.fibreMass_eq_w1MassB hM hℓ hd u
  rcases Nat.eq_zero_or_pos n with hn0 | hnpos
  · subst hn0
    simp only [Work.BoseFixB1.flatFibSum, Work.BoseFixB1.flatScountB,
      Work.BoseFixB1.nCountB]
    simp
  by_cases hvol0 : volA = 0
  · exact absurd (hvolAdef.symm.trans hvol0) hvol
  · have hvolpos : 0 < volA := lt_of_le_of_ne
      (by
        rw [hvolAdef]
        show 0 ≤ ∫ x : E3, Work.SmallBoxSliding.boxInd ℓ d u x
        refine MeasureTheory.integral_nonneg (fun x => ?_)
        show 0 ≤ (Submission.BoseGases.dlBox ℓ d u).indicator (fun _ => (1 : ℝ)) x
        exact Set.indicator_nonneg (fun _ _ => zero_le_one) x)
      (Ne.symm hvol0)
    have hQ0 : Work.BoseFixB1S.boxQCount volA ℓ A Φ = 0 := by
      simp only [Work.BoseFixB1S.boxQCount, Work.UBBInputs8.cnPlusBoxInd]
      exact hflat
    have hQae : ∀ i : Fin n, Work.UBBInputs8.boxQInd volA A i Φ
        =ᵐ[MeasureTheory.volume.restrict (Submission.BoseGases.abox n ℓ)] 0 :=
      fun i => Work.BoseFixB1S.boxQInd_ae_zero_of_boxQCount_eq_zero hℓ hvolpos hAmeas hVOL hAc
        hΦc hQ0 i
    have hsqae : ∀ i : Fin n,
        (fun x : Submission.BoseGases.X n =>
            A.indicator (fun _ => (1 : ℝ)) (x i) * (Φ x) ^ 2)
          =ᵐ[MeasureTheory.volume.restrict (Submission.BoseGases.abox n ℓ)]
        (fun x => (Work.UBBInputs8.boxPInd volA A i Φ x) ^ 2) := by
      intro i
      have h1 := Work.BoseFixB1S.indicator_mul_eq_boxPInd_of_boxQCount_eq_zero hℓ hvolpos hAmeas
        hVOL hAc hΦc hQ0 i
      filter_upwards [h1] with x hx
      by_cases hmem : x i ∈ A
      · rw [Set.indicator_of_mem hmem, one_mul] at hx ⊢
        rw [hx]
      · rw [Set.indicator_of_notMem hmem, zero_mul] at hx ⊢
        rw [← hx]
        ring
    obtain ⟨CΦ, hCΦ0, hCΦb⟩ := Work.BoseFixB1S.exists_abox_bound (N := n) (ℓ := ℓ) hℓ hΦc
    have hchi_ind : ∀ x : Submission.BoseGases.X n, ∀ i : Fin n,
        (Submission.BoseGases.chiSmallB M ℓ d u (x i)) ^ 2
          = A.indicator (fun _ => (1 : ℝ)) (x i)
            * (Submission.BoseGases.chiSmallB M ℓ d u (x i)) ^ 2 := by
      intro x i
      by_cases hmem : x i ∈ A
      · rw [Set.indicator_of_mem hmem, one_mul]
      · rw [Set.indicator_of_notMem hmem, zero_mul]
        have hz : Submission.BoseGases.chiSmallB M ℓ d u (x i) = 0 := by
          by_contra hne
          exact hmem (by
            rw [hAdef]
            exact Work.SlotWord.chiSmallB_support_mem_dlBox hM hℓ hd hne)
        rw [hz]; ring
    have hind_chi : ∀ z : E3,
        A.indicator (fun z => (Submission.BoseGases.chiSmallB M ℓ d u z) ^ 2) z
          = (Submission.BoseGases.chiSmallB M ℓ d u z) ^ 2 := by
      intro z
      by_cases hz : z ∈ A
      · rw [Set.indicator_of_mem hz]
      · rw [Set.indicator_of_notMem hz]
        have h0 : Submission.BoseGases.chiSmallB M ℓ d u z = 0 := by
          by_contra hne
          exact hz (by rw [hAdef]; exact Work.SlotWord.chiSmallB_support_mem_dlBox hM hℓ hd hne)
        rw [h0]; ring
    by_cases hIntFib : MeasureTheory.IntegrableOn fib A
    · have hPb : ∀ i : Fin n, ∀ x ∈ Submission.BoseGases.abox n ℓ,
          |(Work.UBBInputs8.boxPInd volA A i Φ x) ^ 2| ≤ CΦ ^ 2 := by
        intro i x hx
        have h1 := Work.BoseFixB1S.abs_boxPInd_le hℓ hvolpos hAmeas hVOL hAc i hCΦb x hx
        rw [abs_of_nonneg (sq_nonneg _)]
        simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg _) h1 2
      have hPm : ∀ i : Fin n, Measurable (Work.UBBInputs8.boxPInd volA A i Φ) :=
        fun i => Work.BoseFixB1S.measurable_boxPInd volA A hAmeas i hΦc.measurable
      have hInt_i : ∀ i : Fin n, MeasureTheory.IntegrableOn
          (fun x : Submission.BoseGases.X n =>
            (Work.UBBInputs8.boxPInd volA A i Φ x) ^ 2 * fib (x i))
          (Submission.BoseGases.abox n ℓ) := by
        intro i
        have hraw := Work.BoseFixB1S.integrableOn_coord_fib (N := n) (ℓ := ℓ) hℓ i hAmeas hAc
          ((hPm i).pow_const 2).aestronglyMeasurable (hPb i) hIntFib
        refine hraw.congr ?_
        filter_upwards with x
        rw [hfib_ind (x i)]
      have hsplit : (∫ x in Submission.BoseGases.abox n ℓ,
            ∑ i : Fin n, (Work.UBBInputs8.boxPInd volA A i Φ x) ^ 2 * fib (x i))
          = ∑ i : Fin n, ∫ x in Submission.BoseGases.abox n ℓ,
              (Work.UBBInputs8.boxPInd volA A i Φ x) ^ 2 * fib (x i) :=
        integral_finsetSum _ (fun i _ => hInt_i i)
      have hcol := (Work.BoseFixB1S.boxPInd_fib_collapse (N := n) (ℓ := ℓ) (volA := volA) hℓ
        hvolpos hAmeas hAc hVOLreal hΦc hIntFib).1
      have hpt_fib : ∀ i : Fin n, ∀ᵐ x ∂(MeasureTheory.volume.restrict
          (Submission.BoseGases.abox n ℓ)),
          (Φ x) ^ 2 * fib (x i)
            = (Work.UBBInputs8.boxPInd volA A i Φ x) ^ 2 * fib (x i) := by
        intro i
        filter_upwards [hsqae i] with x hx
        calc (Φ x) ^ 2 * fib (x i)
            = (Φ x) ^ 2 * (A.indicator (fun _ => (1 : ℝ)) (x i) * fib (x i)) := by
              rw [hfib_ind1 (x i)]
          _ = (A.indicator (fun _ => (1 : ℝ)) (x i) * (Φ x) ^ 2) * fib (x i) := by ring
          _ = (Work.UBBInputs8.boxPInd volA A i Φ x) ^ 2 * fib (x i) := by rw [hx]
      have hpt_chi : ∀ i : Fin n, ∀ᵐ x ∂(MeasureTheory.volume.restrict
          (Submission.BoseGases.abox n ℓ)),
          (Φ x) ^ 2 * (Submission.BoseGases.chiSmallB M ℓ d u (x i)) ^ 2
            = (Work.UBBInputs8.boxPInd volA A i Φ x) ^ 2
              * (Submission.BoseGases.chiSmallB M ℓ d u (x i)) ^ 2 := by
        intro i
        filter_upwards [hsqae i] with x hx
        calc (Φ x) ^ 2 * (Submission.BoseGases.chiSmallB M ℓ d u (x i)) ^ 2
            = (Φ x) ^ 2 * (A.indicator (fun _ => (1 : ℝ)) (x i)
                * (Submission.BoseGases.chiSmallB M ℓ d u (x i)) ^ 2) := by
              conv_lhs => rw [hchi_ind x i]
          _ = (A.indicator (fun _ => (1 : ℝ)) (x i) * (Φ x) ^ 2)
                * (Submission.BoseGases.chiSmallB M ℓ d u (x i)) ^ 2 := by ring
          _ = (Work.UBBInputs8.boxPInd volA A i Φ x) ^ 2
                * (Submission.BoseGases.chiSmallB M ℓ d u (x i)) ^ 2 := by rw [hx]
      have hFibForm : Work.BoseFixB1.flatFibSum h M ℓ d u Φ
          = (Work.BoseFixB1.w1MassB h M ℓ d u / volA)
            * Work.BoseFixB1S.boxFlatCount volA ℓ A Φ := by
        rw [Work.BoseFixB1.flatFibSum]
        trans (∫ x in Submission.BoseGases.abox n ℓ,
          ∑ i : Fin n, (Work.UBBInputs8.boxPInd volA A i Φ x) ^ 2 * fib (x i))
        · refine MeasureTheory.integral_congr_ae ?_
          have hall := MeasureTheory.ae_all_iff.mpr hpt_fib
          filter_upwards [hall] with x hx
          show (Φ x) ^ 2 * ∑ i : Fin n, fib (x i)
            = ∑ i : Fin n, (Work.UBBInputs8.boxPInd volA A i Φ x) ^ 2 * fib (x i)
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl (fun i _ => hx i)
        · rw [hsplit, hcol, hfib_int]
          ring
      have hchiInt : MeasureTheory.IntegrableOn
          (fun z : E3 => (Submission.BoseGases.chiSmallB M ℓ d u z) ^ 2) A := by
        rw [hAdef]
        exact Work.BoseFixB1S.integrableOn_chiSmallB_pow_dlBox hM hℓ hd u 2
      have hchiMassId : (∫ z in A, (Submission.BoseGases.chiSmallB M ℓ d u z) ^ 2)
          = Work.SmallBoxSliding.chiMass M ℓ d u := by
        rw [hAdef]; exact Work.BoseFixB1S.chiMass_eq_setIntegral_dlBox hM hℓ hd u
      have hInt_i_chi : ∀ i : Fin n, MeasureTheory.IntegrableOn
          (fun x : Submission.BoseGases.X n =>
            (Work.UBBInputs8.boxPInd volA A i Φ x) ^ 2
              * (Submission.BoseGases.chiSmallB M ℓ d u (x i)) ^ 2)
          (Submission.BoseGases.abox n ℓ) := by
        intro i
        have hraw := Work.BoseFixB1S.integrableOn_coord_fib (N := n) (ℓ := ℓ) hℓ i hAmeas hAc
          ((hPm i).pow_const 2).aestronglyMeasurable (hPb i) hchiInt
        refine hraw.congr ?_
        filter_upwards with x
        rw [hind_chi (x i)]
      have hscount : Work.BoseFixB1.flatScountB M ℓ d u Φ
          = (Work.SmallBoxSliding.chiMass M ℓ d u / volA)
            * Work.BoseFixB1S.boxFlatCount volA ℓ A Φ := by
        change (∫ x in Submission.BoseGases.abox n ℓ, (Φ x) ^ 2
            * (∑ i : Fin n, (Submission.BoseGases.chiSmallB M ℓ d u (x i)) ^ 2)) = _
        trans (∫ x in Submission.BoseGases.abox n ℓ,
          ∑ i : Fin n, (Work.UBBInputs8.boxPInd volA A i Φ x) ^ 2
            * (Submission.BoseGases.chiSmallB M ℓ d u (x i)) ^ 2)
        · refine MeasureTheory.integral_congr_ae ?_
          have hall := MeasureTheory.ae_all_iff.mpr hpt_chi
          filter_upwards [hall] with x hx
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl (fun i _ => hx i)
        · trans (∑ i : Fin n, ∫ x in Submission.BoseGases.abox n ℓ,
              (Work.UBBInputs8.boxPInd volA A i Φ x) ^ 2
                * (Submission.BoseGases.chiSmallB M ℓ d u (x i)) ^ 2)
          · exact integral_finsetSum _ (fun i _ => hInt_i_chi i)
          · have hcol2 := (Work.BoseFixB1S.boxPInd_fib_collapse (N := n) (ℓ := ℓ) (volA := volA)
              hℓ hvolpos hAmeas hAc hVOLreal hΦc hchiInt).1
            rw [hcol2, hchiMassId]
            ring
      by_cases hchi : Work.SmallBoxSliding.chiMass M ℓ d u = 0
      · have hglob : MeasureTheory.Integrable
            (fun z : E3 => (Submission.BoseGases.chiSmallB M ℓ d u z) ^ 2) := by
          have h1 : MeasureTheory.IntegrableOn
              (fun z : E3 => (Submission.BoseGases.chiSmallB M ℓ d u z) ^ 2)
              (Submission.BoseGases.dlBox ℓ d u) :=
            Work.BoseFixB1S.integrableOn_chiSmallB_pow_dlBox hM hℓ hd u 2
          have h2 : (fun z : E3 => (Submission.BoseGases.chiSmallB M ℓ d u z) ^ 2)
              = fun z => (Submission.BoseGases.dlBox ℓ d u).indicator
                  (fun z => (Submission.BoseGases.chiSmallB M ℓ d u z) ^ 2) z := by
            funext z
            by_cases hz : z ∈ Submission.BoseGases.dlBox ℓ d u
            · rw [Set.indicator_of_mem hz]
            · rw [Set.indicator_of_notMem hz]
              have h0 : Submission.BoseGases.chiSmallB M ℓ d u z = 0 := by
                by_contra hne
                exact hz (Work.SlotWord.chiSmallB_support_mem_dlBox hM hℓ hd hne)
              rw [h0]; ring
          rw [h2]
          exact (MeasureTheory.integrable_indicator_iff
            (Work.SmallBoxSliding.measurableSet_dlBox ℓ d u)).mpr h1
        have hzero : (∫ z : E3, (Submission.BoseGases.chiSmallB M ℓ d u z) ^ 2) = 0 := by
          rw [← Work.SmallBoxSliding.chiMass_def]; exact hchi
        have hsq : (fun z : E3 => (Submission.BoseGases.chiSmallB M ℓ d u z) ^ 2)
            =ᵐ[MeasureTheory.volume] 0 :=
          (MeasureTheory.integral_eq_zero_iff_of_nonneg (fun z => sq_nonneg _) hglob).mp hzero
        have hχae : Submission.BoseGases.chiSmallB M ℓ d u =ᵐ[MeasureTheory.volume] 0 := by
          filter_upwards [hsq] with z hz
          exact (pow_eq_zero_iff (n := 2) (by norm_num)).mp hz
        have hw1zero : Work.BoseFixB1.w1MassB h M ℓ d u = 0 := by
          rw [← hfib_int]
          have hfibae : fib =ᵐ[MeasureTheory.volume.restrict A] 0 := by
            filter_upwards [MeasureTheory.ae_restrict_of_ae hχae] with z hz
            simp only [Pi.zero_apply] at hz
            have h0 : (fun y : E3 => Submission.BoseGases.wSmall1Pair h M ℓ d u z y)
                = fun _ => (0 : ℝ) := by
              funext y
              simp only [Submission.BoseGases.wSmall1Pair, Submission.BoseGases.wSmallPair, hz,
                zero_mul, mul_zero]
            show (∫ y in Submission.BoseGases.acube ℓ,
              Submission.BoseGases.wSmall1Pair h M ℓ d u z y) = 0
            rw [h0]; simp
          rw [MeasureTheory.integral_congr_ae hfibae]
          simp
        rw [hFibForm, hw1zero]
        simp
      · rw [hFibForm, hscount]
        field_simp
    · have hfibm : MeasureTheory.AEStronglyMeasurable fib
          (MeasureTheory.volume.restrict A) := by
        have hg0 : AEMeasurable (Submission.BoseGases.g0 v h)
            (MeasureTheory.volume : MeasureTheory.Measure E3) :=
          (Submission.BoseGases.w0_spec h).2.rhs_integrable.aestronglyMeasurable.aemeasurable
        have hh := Work.BoseFixB1.aestronglyMeasurable_wSmallPairFibre (ℓ := ℓ) (d := d) M u hg0
        have hh2 : MeasureTheory.AEStronglyMeasurable
            (fun z : E3 => ∫ y in Submission.BoseGases.acube ℓ,
              Submission.BoseGases.wSmallPair M ℓ d u (Submission.BoseGases.g0 v h) z y)
            (MeasureTheory.volume.restrict (Submission.BoseGases.acube ℓ)) := hh
        have hh3 := hh2.mono_measure (MeasureTheory.Measure.restrict_mono hAc le_rfl)
        refine hh3.congr ?_
        filter_upwards with z
        show (∫ y in Submission.BoseGases.acube ℓ,
            Submission.BoseGases.wSmallPair M ℓ d u (Submission.BoseGases.g0 v h) z y)
          = ∫ y in Submission.BoseGases.acube ℓ,
            Submission.BoseGases.wSmall1Pair h M ℓ d u z y
        rfl
      have hSa : (∫⁻ z in A, ENNReal.ofReal |fib z|) = ⊤ := by
        have hh : (∫⁻ z in A, ‖fib z‖ₑ) = ⊤ := by
          by_contra hc
          exact hIntFib ⟨hfibm, (MeasureTheory.hasFiniteIntegral_iff_enorm).mpr
            (lt_top_iff_ne_top.mpr hc)⟩
        simpa only [Real.enorm_eq_ofReal_abs] using hh
      have hcase : Work.BoseFixB1.flatFibSum h M ℓ d u Φ = 0 := by
        -- to be replaced by the delegated lemma `Work.BoseFixB1S.FlatFib.flatFibSumEqZero`
        exact Work.BoseFixB1S.FlatFib.flatFibSumEqZero h hM hℓ hd u hΦc hQae hint hSa
      rw [hcase]
      have hw1zero : Work.BoseFixB1.w1MassB h M ℓ d u = 0 := by
        rw [← hfib_int]
        exact MeasureTheory.integral_undef hIntFib
      rw [hw1zero]
      simp

end Work.BoseFixB1S


