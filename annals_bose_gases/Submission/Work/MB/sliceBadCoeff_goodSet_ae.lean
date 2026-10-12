import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Submission.Work.BoseBoxFock.exists_slice_le_window
import Submission.Work.MB.SlotSumSplitAux
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.MB

open MeasureTheory

local notation "E3" => EuclideanSpace ℝ (Fin 3)

set_option linter.unusedVariables false

/-! ## The weak (measurable, everywhere bounded) form of the measurability of the slice coefficient

`Work.BoseBoxFock.aemeasurable_sliceCoeff` proves the a.e.-measurability of
`y ↦ ∫_u conj (M_α u) · slice_y u` under the *strong* mode hypotheses (`Continuouus` +
`HasCompactSupport`), through the continuity of the sector.  The only thing used there is that the
sector `slotExact e S Ψ` is measurable, so the same argument goes through verbatim with the weak
hypotheses: the sector of a measurable, everywhere bounded state is measurable
(`Work.MB.slotExact_mb_weak`). -/
theorem aemeasurable_sliceCoeff_weak {m n : ℕ} {ℓ : ℝ}
    (e : Fin m → E3 → ℂ) (hmeas : ∀ l, Measurable (e l))
    (hbdd : ∀ l, ∃ C, ∀ x, ‖e l x‖ ≤ C)
    (hsupp : ∀ l, Function.support (e l) ⊆ Work.BoseK15.corpusBox.boxL ℓ)
    (α : Fin m →₀ ℕ) (S : Finset (Fin n))
    {Φ : (Fin n → E3) → ℂ} (hΦm : Measurable Φ) (hΦb : ∃ C, ∀ x, ‖Φ x‖ ≤ C) :
    AEMeasurable
      (fun y : {i // i ∉ S} → E3 =>
        ∫ u : Fin S.card → E3,
          (starRingEnd ℂ) (Work.BoseDict.modeProd e S.card α u)
            * Work.BoseBoxFock.sliceF e S Φ y u)
      (MeasureTheory.volume : MeasureTheory.Measure ({i // i ∉ S} → E3)) := by
  classical
  -- the mode product is measurable in the `u`-variable
  have hmeas_mode : Measurable (fun u : Fin S.card → E3 =>
      Work.BoseDict.modeProd e S.card α u) := by
    simp only [Work.BoseDict.modeProd]
    exact Finset.measurable_sum _ (fun σ _ => measurable_const.mul
      (Finset.measurable_prod _ (fun i _ => (hmeas (σ i)).comp (measurable_pi_apply i))))
  -- the reassembling map `(u, y) ↦ pairCoord S (u ∘ S.equivFin) y` is measurable
  have hpair : Measurable (fun p : (Fin S.card → E3) × ({i // i ∉ S} → E3) =>
      Work.BoseBoxFock.pairCoord S (fun i : {i // i ∈ S} => p.1 (S.equivFin i)) p.2) := by
    rw [measurable_pi_iff]
    intro j
    by_cases hj : j ∈ S
    · simp only [Work.BoseBoxFock.pairCoord, dif_pos hj]
      exact (measurable_pi_apply (S.equivFin ⟨j, hj⟩)).comp measurable_fst
    · simp only [Work.BoseBoxFock.pairCoord, dif_neg hj]
      exact (measurable_pi_apply (⟨j, hj⟩ : {i // i ∉ S})).comp measurable_snd
  -- the sector is measurable, hence so is the slice as a function of `(u, y)`
  have hsec : Measurable (Work.BoseBoxFock.slotExact e S Φ) :=
    (Work.MB.slotExact_mb_weak hmeas hbdd hsupp S hΦm hΦb).1
  have hslice : StronglyMeasurable (fun p : (Fin S.card → E3) × ({i // i ∉ S} → E3) =>
      Work.BoseBoxFock.sliceF e S Φ p.2 p.1) := by
    have h2 : Measurable (fun p : (Fin S.card → E3) × ({i // i ∉ S} → E3) =>
        Work.BoseBoxFock.slotExact e S Φ
          (Work.BoseBoxFock.pairCoord S (fun i : {i // i ∈ S} => p.1 (S.equivFin i)) p.2)) :=
      hsec.comp hpair
    simpa only [Work.BoseBoxFock.sliceF, Work.BoseBoxFock.sectorSlice] using h2.stronglyMeasurable
  -- hence the integrand is jointly strongly measurable
  have hG : StronglyMeasurable (fun p : (Fin S.card → E3) × ({i // i ∉ S} → E3) =>
      (starRingEnd ℂ) (Work.BoseDict.modeProd e S.card α p.1)
        * Work.BoseBoxFock.sliceF e S Φ p.2 p.1) :=
    ((Complex.continuous_conj.measurable.comp
        (hmeas_mode.comp measurable_fst)).stronglyMeasurable).mul hslice
  -- and its `u`-integral is strongly measurable in `y`
  have hint : StronglyMeasurable (fun y : {i // i ∉ S} → E3 =>
      ∫ u : Fin S.card → E3,
        (starRingEnd ℂ) (Work.BoseDict.modeProd e S.card α u)
          * Work.BoseBoxFock.sliceF e S Φ y u) :=
    MeasureTheory.StronglyMeasurable.integral_prod_left'
      (μ := (MeasureTheory.volume : MeasureTheory.Measure (Fin S.card → E3))) hG
  exact hint.aemeasurable

theorem sliceBadCoeff_goodSet_ae {m n : ℕ} [NeZero m] {ℓ M : ℝ}
    (hℓ : 0 < ℓ) {e : Fin m → EuclideanSpace ℝ (Fin 3) → ℂ}
    (hmeas : ∀ l, Measurable (e l)) (hbdE : ∀ l, ∃ C, ∀ x, ‖e l x‖ ≤ C)
    (horth : ∀ l l', (∫ z : EuclideanSpace ℝ (Fin 3), star (e l z) * e l' z)
      = (if l = l' then (1 : ℂ) else 0))
    (hsupp : ∀ l, Function.support (e l) ⊆ Work.BoseK15.corpusBox.boxL ℓ)
    (hpin : ∃ c : ℂ, (starRingEnd ℂ) c * c = (ℓ ^ 3)⁻¹ ∧
      (∀ᵐ x ∂(MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin 3))),
        e 0 x = c * Work.BoseK15.corpusBox.thetaFun ℓ x))
    (Φ : Submission.BoseGases.X n → ℝ) (hΦ : Continuous Φ)
    (hΦcs : HasCompactSupport Φ)
    (hΦsupp : tsupport Φ ⊆ Submission.BoseGases.abox n ℓ)
    (hM : 0 ≤ M) (hmom : Work.BoseBox.SpectralNPlusLe ℓ M Φ)
    (S : Finset (Fin n)) :
    ∃ G : Set ({i // i ∉ S} → EuclideanSpace ℝ (Fin 3)),
      MeasurableSet G ∧
      (∀ᵐ y ∂(MeasureTheory.volume :
          MeasureTheory.Measure ({i // i ∉ S} → EuclideanSpace ℝ (Fin 3))), y ∈ G) ∧
      (∀ y ∈ G, ∀ α : Fin m →₀ ℕ, α.sum (fun _ k => k) = S.card →
        ((S.card - α 0 : ℕ) : ℝ) > (⌊M⌋₊ : ℝ) →
        Work.BoseDict.cIPn S.card (Work.BoseDict.modeProd e S.card α)
          (Work.BoseBoxFock.sliceF e S
            (fun x : Submission.BoseGases.X n => ((Φ x : ℝ) : ℂ)) y) = 0) := by
  classical
  -- the weak mode hypotheses give `L^∞` modes
  have hbdd : ∀ l, MemLp (e l) ⊤ := memLp_modes_weak hmeas hbdE
  have he : ∀ l l', (∫ z : E3, (starRingEnd ℂ) (e l z) * e l' z)
      = if l = l' then 1 else 0 := by
    intro l l'
    simpa only [starRingEnd_apply] using horth l l'
  set Φc : Submission.BoseGases.X n → ℂ := fun x => ((Φ x : ℝ) : ℂ) with hΦcdef
  have hΦcm : Measurable Φc := Complex.continuous_ofReal.measurable.comp hΦ.measurable
  have hΦcb : ∃ C, ∀ x, ‖Φc x‖ ≤ C := by
    obtain ⟨C, hC⟩ := hΦ.bounded_above_of_compact_support hΦcs
    exact ⟨C, fun x => by simpa [hΦcdef] using hC x⟩
  -- the monomial coefficient of the slice
  set coeff : (Fin m →₀ ℕ) → ({i // i ∉ S} → E3) → ℂ :=
    (fun α y => Work.BoseDict.cIPn S.card (Work.BoseDict.modeProd e S.card α)
      (Work.BoseBoxFock.sliceF e S Φc y)) with hcoeffdef
  -- the *finite* set of bad multi-indices
  set badSet : Finset (Fin m →₀ ℕ) :=
    (Finset.finsuppAntidiag (Finset.univ : Finset (Fin m)) S.card).filter
      (fun α => ((S.card - α 0 : ℕ) : ℝ) > (⌊M⌋₊ : ℝ)) with hbadSetdef
  have hslice_int : Integrable (fun y : {i // i ∉ S} → E3 =>
      ∫ u in Submission.BoseGases.abox S.card ℓ, ‖Work.BoseBoxFock.sliceF e S Φc y u‖ ^ 2)
      (volume : Measure ({i // i ∉ S} → E3)) := by
    have h := (Work.BoseBoxFock.slice_Xpow_fubini_bdd_cb ℓ hℓ hsupp hbdd S hΦ hΦsupp 0).2
    simpa only [Work.BoseBoxFock.XSpow] using h
  -- the a.e. vanishing of each bad coefficient
  have hcoeff_ae : ∀ α ∈ badSet,
      ∀ᵐ y ∂(volume : Measure ({i // i ∉ S} → E3)), coeff α y = 0 := by
    intro α hα
    obtain ⟨hαmem, hαbad⟩ := Finset.mem_filter.mp hα
    have hsum : (Finset.univ : Finset (Fin m)).sum (fun i => α i) = S.card :=
      (Finset.mem_finsuppAntidiag.mp hαmem).1
    have hdeg : α.sum (fun _ k => k) = S.card := by
      have h1 : α.sum (fun _ k => k) = ∑ i ∈ α.support, α i := by rw [Finsupp.sum]
      have h2 : (∑ i ∈ α.support, α i)
          = ∑ i ∈ (Finset.univ : Finset (Fin m)), α i :=
        Finset.sum_subset (Finset.subset_univ _) (fun x _ hx => by
          simp [Finsupp.notMem_support_iff.mp hx])
      rw [h1, h2]
      exact hsum
    have hkpos : 0 < S.card - α 0 := by
      have h0 : (0 : ℝ) < ((S.card - α 0 : ℕ) : ℝ) :=
        lt_of_le_of_lt (Nat.cast_nonneg _) hαbad
      exact_mod_cast h0
    -- the vanishing integral (`ExcWindow`, step 6)
    have hzero : ∫ y : {i // i ∉ S} → E3, ‖coeff α y‖ ^ 2
        ∂(volume : Measure ({i // i ∉ S} → E3)) = 0 := by
      have h := Work.BoseBoxFock.sliceBadCoeff_zero ℓ hℓ hΦ hΦsupp hM hmom he hbdd hsupp hpin S α hdeg hαbad
      simpa only [hcoeffdef, Work.BoseDict.cIPn, hΦcdef] using h
    -- the a.e. pointwise bound (Cauchy--Schwarz for the slice coefficient)
    have hle : ∀ᵐ y ∂(volume : Measure ({i // i ∉ S} → E3)),
        ‖coeff α y‖ ^ 2
          ≤ (∫ u in Submission.BoseGases.abox S.card ℓ,
                ‖Work.BoseDict.modeProd e S.card α u‖ ^ 2)
            * (∫ u in Submission.BoseGases.abox S.card ℓ,
                ‖Work.BoseBoxFock.sliceF e S Φc y u‖ ^ 2) := by
      have h := Work.BoseBoxFock.ae_sliceCoeff_le hℓ he hbdd hsupp hpin S hΦ hΦsupp α hkpos
      simpa only [hcoeffdef, Work.BoseDict.cIPn, hΦcdef] using h
    -- integrability of the squared modulus of the coefficient
    have hbd : Integrable (fun y : {i // i ∉ S} → E3 =>
        (∫ u in Submission.BoseGases.abox S.card ℓ,
            ‖Work.BoseDict.modeProd e S.card α u‖ ^ 2)
          * (∫ u in Submission.BoseGases.abox S.card ℓ,
              ‖Work.BoseBoxFock.sliceF e S Φc y u‖ ^ 2))
        (volume : Measure ({i // i ∉ S} → E3)) :=
      hslice_int.const_mul _
    have haesm : AEStronglyMeasurable
        (fun y : {i // i ∉ S} → E3 => ‖coeff α y‖ ^ 2)
        (volume : Measure ({i // i ∉ S} → E3)) :=
      ((aemeasurable_sliceCoeff_weak e hmeas hbdE hsupp α S hΦcm hΦcb).norm.pow_const 2)
        |>.aestronglyMeasurable
    have hii : Integrable (fun y : {i // i ∉ S} → E3 => ‖coeff α y‖ ^ 2)
        (volume : Measure ({i // i ∉ S} → E3)) := by
      refine Integrable.mono' hbd haesm ?_
      filter_upwards [hle] with y hy
      rw [Real.norm_of_nonneg (by positivity)]
      exact hy
    have hz := (integral_eq_zero_iff_of_nonneg_ae
      (Filter.Eventually.of_forall (fun y => by positivity)) hii).mp hzero
    filter_upwards [hz] with y hy
    have h2 : ‖coeff α y‖ * ‖coeff α y‖ = 0 := by simpa [pow_two] using hy
    exact norm_eq_zero.mp (mul_self_eq_zero.mp h2)
  -- the good set: the complement of the (finite) union of the non-vanishing sets
  set U : Set ({i // i ∉ S} → E3) :=
    (⋃ α ∈ badSet, toMeasurable (volume : Measure ({i // i ∉ S} → E3))
      {y | coeff α y ≠ 0}) with hUdef
  have hUm : MeasurableSet U := by
    rw [hUdef]
    exact Finset.measurableSet_biUnion badSet
      (fun α _ => measurableSet_toMeasurable _ _)
  set G : Set ({i // i ∉ S} → E3) := Uᶜ with hGdef
  have hGm : MeasurableSet G := by rw [hGdef]; exact hUm.compl
  have hU0 : (volume : Measure ({i // i ∉ S} → E3)) U = 0 := by
    have hnull : ∀ α ∈ badSet,
        (volume : Measure ({i // i ∉ S} → E3))
          (toMeasurable (volume : Measure ({i // i ∉ S} → E3)) {y | coeff α y ≠ 0}) = 0 := by
      intro α hα
      rw [measure_toMeasurable]
      exact MeasureTheory.ae_iff.mp (hcoeff_ae α hα)
    rw [hUdef]
    refine le_antisymm ?_ bot_le
    calc (volume : Measure ({i // i ∉ S} → E3))
          (⋃ α ∈ badSet, toMeasurable (volume : Measure ({i // i ∉ S} → E3))
            {y | coeff α y ≠ 0})
        ≤ ∑ α ∈ badSet, (volume : Measure ({i // i ∉ S} → E3))
            (toMeasurable (volume : Measure ({i // i ∉ S} → E3)) {y | coeff α y ≠ 0}) :=
          MeasureTheory.measure_biUnion_finset_le _ _
      _ = 0 := Finset.sum_eq_zero hnull
  have hGae : ∀ᵐ y ∂(volume : Measure ({i // i ∉ S} → E3)), y ∈ G := by
    rw [hGdef]
    exact MeasureTheory.measure_eq_zero_iff_ae_notMem.mp hU0
  refine ⟨G, hGm, hGae, ?_⟩
  intro y hy α hdeg hbad
  have hαmem : α ∈ Finset.finsuppAntidiag (Finset.univ : Finset (Fin m)) S.card := by
    rw [Finset.mem_finsuppAntidiag]
    refine ⟨?_, Finset.subset_univ _⟩
    have h1 : α.sum (fun _ k => k) = ∑ i ∈ α.support, α i := by rw [Finsupp.sum]
    have h2 : (∑ i ∈ α.support, α i)
        = ∑ i ∈ (Finset.univ : Finset (Fin m)), α i :=
      Finset.sum_subset (Finset.subset_univ _) (fun x _ hx => by
        simp [Finsupp.notMem_support_iff.mp hx])
    rw [← h2, ← h1]
    exact hdeg
  have hαbad : α ∈ badSet := by
    rw [hbadSetdef]
    exact Finset.mem_filter.mpr ⟨hαmem, hbad⟩
  have hg : coeff α y = 0 := by
    by_contra hne
    have hyU : y ∈ U := by
      rw [hUdef]
      exact Set.mem_biUnion hαbad (subset_toMeasurable _ _ (by simpa using hne))
    rw [hGdef, Set.mem_compl_iff] at hy
    exact hy hyU
  simpa only [hcoeffdef, hΦcdef] using hg

end Work.MB
