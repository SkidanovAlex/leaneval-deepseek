import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseBoxFock.ae_sliceCoeff_le
import Submission.Work.BoseBoxFock.aemeasurable_sliceCoeff
import Submission.Work.BoseBoxFock.exists_fibre_le_of_integral_ae_hq0_restrict
import Submission.Work.BoseBoxFock.sliceBadCoeff_zero
import Submission.Work.BoseBoxFock.sliceFubini
import Submission.Work.BoseBoxFock.sliceQZeroAe
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

open MeasureTheory

namespace Work.BoseBoxFock

local notation "Ω" => EuclideanSpace ℝ (Fin 3)

set_option maxHeartbeats 2000000

/-- **The fibre selection *with the `ExcWindow` condition* (the last piece of the BF3c selection
layer).**  This is `Work.BoseBoxFock.exists_slice_le_of_slotSum` with the window added: the
returned complement configuration `y` is not merely a no-worse-ratio point, it also carries the
condition `hG` of `Work.BoseBoxFock.sliceModelWindow` — the `cIPn`-coefficient of every *bad*
monomial `M_α` (`S.card − α 0 > ⌊M⌋₊`) of the slice vanishes.  Together with `sliceModelWindow`
this turns the selection into a real model vector in the excited window.

Proof route (`FINDING_BF3c_selection_s9.md` §2 (A)):
* the `V`-sector selection `exists_sector_le_of_slotSum` gives `S` with positive mass and no worse
  ratio;
* `slotSum_sectorPointwise` (form) and `massR_slotExact_eq_integral` (norm) decouple the sector
  quantities into `∫_y q(y) ≤ c ∫_y ν(y)` with `ν(y) := ∫_u ‖sectorSlice … y u‖²`, `∫_y ν > 0`;
* for each bad `α`, `sliceBadCoeff_zero` gives `∫_y ‖c_α(y)‖² = 0`, hence `c_α = 0` for a.e. `y`
  (needs the integrability of `‖c_α‖²`, which follows from the slice's boundedness and compact
  support — the helpers of `SliceBadAux`/`XSpow_sliceF_pointwise` are the place to look); let `G`
  be the (finite) intersection of those full-measure sets;
* transfer the two integral inequalities to `∫_{y∈G}` (`MeasureTheory.integral_eq_setIntegral`,
  from `∀ᵐ y, y ∈ G`) and apply `exists_fibre_le_of_integral_ae` at the restricted measure.

Note (`FINDING_BF3c_selection_s9.md` §2): `G` depends on the sector `S` (`S.card − α 0` enters the
badness), so the sector selection must be run *first*; the sectors are finitely many so there is no
measurable-selection issue. -/
theorem exists_slice_le_window {m n : ℕ} [NeZero m] {ℓ M : ℝ}
    (hℓ : 0 < ℓ) (e : Fin m → EuclideanSpace ℝ (Fin 3) → ℂ)
    (hcont : ∀ l, Continuous (e l)) (hcomp : ∀ l, HasCompactSupport (e l))
    (horth : ∀ l l', (∫ z : EuclideanSpace ℝ (Fin 3), star (e l z) * e l' z)
      = (if l = l' then (1 : ℂ) else 0))
    (hint : ∀ l l', MeasureTheory.Integrable
      (fun z : EuclideanSpace ℝ (Fin 3) => star (e l z) * e l' z))
    (hbdd : ∀ l, MeasureTheory.MemLp (e l) ⊤)
    (hsupp : ∀ l, Function.support (e l) ⊆ Work.BoseK15.corpusBox.boxL ℓ)
    (hpin : ∃ c : ℂ, (starRingEnd ℂ) c * c = (ℓ ^ 3)⁻¹ ∧
      (∀ᵐ x ∂(volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin 3))),
        e 0 x = c * Work.BoseK15.corpusBox.thetaFun ℓ x))
    (Φ : Submission.BoseGases.X n → ℝ) (hΦ : Continuous Φ)
    (hΦcomp : HasCompactSupport Φ)
    (hΦc : tsupport Φ ⊆ Submission.BoseGases.abox n ℓ)
    (hΦsym : ∀ σ : Equiv.Perm (Fin n),
      (fun x : Submission.BoseGases.X n => Φ (x ∘ σ)) = Φ)
    (hM : 0 ≤ M) (hmom : Work.BoseBox.SpectralNPlusLe ℓ M Φ)
    (T : (Fin m → ℝ) →ₗ[ℝ] (Fin m → ℝ)) (c : ℝ)
    (hpos : 0 < massR (fun x : Submission.BoseGases.X n => ((Φ x : ℝ) : ℂ)))
    (hcle : (∫ x : Submission.BoseGases.X n,
        star ((fun x => ((Φ x : ℝ) : ℂ)) x)
          * Work.BoseDict.boxSlotSum e T (fun x => ((Φ x : ℝ) : ℂ)) x).re
      ≤ c * massR (fun x => ((Φ x : ℝ) : ℂ))) :
    ∃ (S : Finset (Fin n)) (y : {i // i ∉ S} → EuclideanSpace ℝ (Fin 3)),
      0 < (∫ u : {i // i ∈ S} → EuclideanSpace ℝ (Fin 3),
            ‖sectorSlice e S (fun x => ((Φ x : ℝ) : ℂ)) y u‖ ^ 2) ∧
      (∫ u : {i // i ∈ S} → EuclideanSpace ℝ (Fin 3),
          (star (sectorSlice e S (fun x => ((Φ x : ℝ) : ℂ)) y u)
            * slotSumSub e T S (sectorSlice e S (fun x => ((Φ x : ℝ) : ℂ)) y) u).re)
        ≤ c * (∫ u : {i // i ∈ S} → EuclideanSpace ℝ (Fin 3),
            ‖sectorSlice e S (fun x => ((Φ x : ℝ) : ℂ)) y u‖ ^ 2) ∧
      (∀ α : Fin m →₀ ℕ, α.sum (fun _ k => k) = S.card →
        ((S.card - α 0 : ℕ) : ℝ) > (⌊M⌋₊ : ℝ) →
        Work.BoseDict.cIPn S.card (Work.BoseDict.modeProd e S.card α)
          (sliceF e S (fun x => ((Φ x : ℝ) : ℂ)) y) = 0) := by
  classical
  set Φc : Submission.BoseGases.X n → ℂ := fun x => ((Φ x : ℝ) : ℂ) with hΦcdef
  have hΦcont : Continuous Φc := Complex.continuous_ofReal.comp hΦ
  have hΦcomp' : HasCompactSupport Φc :=
    hΦcomp.comp_left (g := fun r : ℝ => (r : ℂ)) (by simp)
  have he : ∀ l l', (∫ x : Work.BoseDict.Sp, (starRingEnd ℂ) (e l x) * e l' x)
      = if l = l' then 1 else 0 := by
    intro l l'
    simpa only [starRingEnd_apply] using horth l l'
  -- step 1: the `V`-sector selection
  obtain ⟨S, hSpos, hSle⟩ :=
    exists_sector_le_of_slotSum e T hcont hcomp horth hint Φc hΦcont hΦcomp' c hpos hcle
  -- step 2: the Fubini package at that sector
  obtain ⟨hqint0, hνint0, hqeq0, hνeq0⟩ :=
    sliceFubini e T hcont hcomp horth hint S Φc hΦcont hΦcomp'
  have hq0ae0 := sliceQZeroAe e T hcont hcomp horth hint S Φc hΦcont hΦcomp'
  -- the two fibre functions
  set ν : ({i // i ∉ S} → Ω) → ℝ :=
    (fun y => ∫ u : {i // i ∈ S} → Ω, ‖sectorSlice e S Φc y u‖ ^ 2) with hνdef
  set q : ({i // i ∉ S} → Ω) → ℝ :=
    (fun y => ∫ u : {i // i ∈ S} → Ω,
      (star (sectorSlice e S Φc y u) * slotSumSub e T S (sectorSlice e S Φc y) u).re) with hqdef
  have hqint : MeasureTheory.Integrable q (volume : Measure ({i // i ∉ S} → Ω)) := hqint0
  have hνint : MeasureTheory.Integrable ν (volume : Measure ({i // i ∉ S} → Ω)) := hνint0
  have hqeq : ∫ y : {i // i ∉ S} → Ω, q y ∂(volume : Measure ({i // i ∉ S} → Ω))
      = (∫ x : Submission.BoseGases.X n, star (slotExact e S Φc x)
          * Work.BoseDict.boxSlotSum e T (slotExact e S Φc) x).re := hqeq0
  have hνeq : ∫ y : {i // i ∉ S} → Ω, ν y ∂(volume : Measure ({i // i ∉ S} → Ω))
      = massR (slotExact e S Φc) := hνeq0
  have hq0ae : ∀ᵐ y ∂(volume : Measure ({i // i ∉ S} → Ω)), ν y = 0 → q y = 0 := hq0ae0
  have hνnn : ∀ y : {i // i ∉ S} → Ω, 0 ≤ ν y :=
    fun y => integral_nonneg (fun u => by positivity)
  -- step 3: the a.e. vanishing of the bad monomial coefficients
  set coeff : (Fin m →₀ ℕ) → ({i // i ∉ S} → Ω) → ℂ :=
    (fun α y => Work.BoseDict.cIPn S.card (Work.BoseDict.modeProd e S.card α) (sliceF e S Φc y))
    with hcoeffdef
  set badSet : Finset (Fin m →₀ ℕ) :=
    (Finset.finsuppAntidiag (Finset.univ : Finset (Fin m)) S.card).filter
      (fun α => ((S.card - α 0 : ℕ) : ℝ) > (⌊M⌋₊ : ℝ)) with hbadSetdef
  have hslice_int : MeasureTheory.Integrable (fun y : {i // i ∉ S} → Ω =>
      ∫ u in Submission.BoseGases.abox S.card ℓ, ‖sliceF e S Φc y u‖ ^ 2)
      (volume : Measure ({i // i ∉ S} → Ω)) := by
    have h := (slice_Xpow_fubini_bdd_cb ℓ hℓ hsupp hbdd S hΦ hΦc 0).2
    simpa only [XSpow] using h
  have hcoeff_ae : ∀ α ∈ badSet,
      ∀ᵐ y ∂(volume : Measure ({i // i ∉ S} → Ω)), coeff α y = 0 := by
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
    -- the vanishing integral
    have hzero : ∫ y : {i // i ∉ S} → Ω, ‖coeff α y‖ ^ 2
        ∂(volume : Measure ({i // i ∉ S} → Ω)) = 0 := by
      have h := sliceBadCoeff_zero ℓ hℓ hΦ hΦc hM hmom he hbdd hsupp hpin S α hdeg hαbad
      simpa only [hcoeffdef, Work.BoseDict.cIPn, hΦcdef] using h
    -- the a.e. pointwise bound
    have hle : ∀ᵐ y ∂(volume : Measure ({i // i ∉ S} → Ω)),
        ‖coeff α y‖ ^ 2
          ≤ (∫ u in Submission.BoseGases.abox S.card ℓ,
                ‖Work.BoseDict.modeProd e S.card α u‖ ^ 2)
            * (∫ u in Submission.BoseGases.abox S.card ℓ, ‖sliceF e S Φc y u‖ ^ 2) := by
      have h := ae_sliceCoeff_le hℓ he hbdd hsupp hpin S hΦ hΦc α hkpos
      simpa only [hcoeffdef, Work.BoseDict.cIPn, hΦcdef] using h
    -- integrability of the squared modulus
    have hbd : MeasureTheory.Integrable (fun y : {i // i ∉ S} → Ω =>
        (∫ u in Submission.BoseGases.abox S.card ℓ,
            ‖Work.BoseDict.modeProd e S.card α u‖ ^ 2)
          * (∫ u in Submission.BoseGases.abox S.card ℓ, ‖sliceF e S Φc y u‖ ^ 2))
        (volume : Measure ({i // i ∉ S} → Ω)) :=
      hslice_int.const_mul _
    have haesm : AEStronglyMeasurable
        (fun y : {i // i ∉ S} → Ω => ‖coeff α y‖ ^ 2)
        (volume : Measure ({i // i ∉ S} → Ω)) :=
      (aemeasurable_sliceCoeff (S := S) e hcont hcomp α hΦcont hΦcomp').norm.pow_const 2
        |>.aestronglyMeasurable
    have hii : MeasureTheory.Integrable (fun y : {i // i ∉ S} → Ω => ‖coeff α y‖ ^ 2)
        (volume : Measure ({i // i ∉ S} → Ω)) := by
      refine MeasureTheory.Integrable.mono' hbd haesm ?_
      filter_upwards [hle] with y hy
      rw [Real.norm_of_nonneg (by positivity)]
      exact hy
    have hz := (MeasureTheory.integral_eq_zero_iff_of_nonneg_ae
      (Filter.Eventually.of_forall (fun y => by positivity)) hii).mp hzero
    filter_upwards [hz] with y hy
    have h2 : ‖coeff α y‖ * ‖coeff α y‖ = 0 := by simpa [pow_two] using hy
    exact norm_eq_zero.mp (mul_self_eq_zero.mp h2)
  -- step 4: the good set
  set U : Set ({i // i ∉ S} → Ω) :=
    (⋃ α ∈ badSet, toMeasurable (volume : Measure ({i // i ∉ S} → Ω))
      {y | coeff α y ≠ 0}) with hUdef
  have hUm : MeasurableSet U := by
    rw [hUdef]
    exact Finset.measurableSet_biUnion badSet
      (fun α _ => measurableSet_toMeasurable _ _)
  set G : Set ({i // i ∉ S} → Ω) := Uᶜ with hGdef
  have hGm : MeasurableSet G := by rw [hGdef]; exact hUm.compl
  have hU0 : (volume : Measure ({i // i ∉ S} → Ω)) U = 0 := by
    have hnull : ∀ α ∈ badSet,
        (volume : Measure ({i // i ∉ S} → Ω))
          (toMeasurable (volume : Measure ({i // i ∉ S} → Ω)) {y | coeff α y ≠ 0}) = 0 := by
      intro α hα
      rw [measure_toMeasurable]
      exact MeasureTheory.ae_iff.mp (hcoeff_ae α hα)
    rw [hUdef]
    refine le_antisymm ?_ bot_le
    calc (volume : Measure ({i // i ∉ S} → Ω))
          (⋃ α ∈ badSet, toMeasurable (volume : Measure ({i // i ∉ S} → Ω))
            {y | coeff α y ≠ 0})
        ≤ ∑ α ∈ badSet, (volume : Measure ({i // i ∉ S} → Ω))
            (toMeasurable (volume : Measure ({i // i ∉ S} → Ω)) {y | coeff α y ≠ 0}) :=
          MeasureTheory.measure_biUnion_finset_le _ _
      _ = 0 := Finset.sum_eq_zero hnull
  have hGae : ∀ᵐ y ∂(volume : Measure ({i // i ∉ S} → Ω)), y ∈ G := by
    rw [hGdef]
    exact MeasureTheory.measure_eq_zero_iff_ae_notMem.mp hU0
  have hGcoeff : ∀ y ∈ G, ∀ α ∈ badSet, coeff α y = 0 := by
    intro y hy α hα
    by_contra hne
    have hyU : y ∈ U := by
      rw [hUdef]
      exact Set.mem_biUnion hα (subset_toMeasurable _ _ (by simpa using hne))
    rw [hGdef, Set.mem_compl_iff] at hy
    exact hy hyU
  -- step 5: transfer the two integral inequalities to `G`
  have hsub0 : ∫ y in G, (q y - c * ν y) ∂(volume : Measure ({i // i ∉ S} → Ω))
      = ∫ y : {i // i ∉ S} → Ω, (q y - c * ν y) := by
    refine MeasureTheory.setIntegral_eq_integral_of_ae_compl_eq_zero ?_
    filter_upwards [hGae] with y hy hyG
    exact absurd hy hyG
  have hGint : ∫ y in G, (q y - c * ν y) ∂(volume : Measure ({i // i ∉ S} → Ω)) ≤ 0 := by
    rw [hsub0, integral_sub hqint (hνint.const_mul c), integral_const_mul, hqeq, hνeq]
    exact sub_nonpos.mpr hSle
  have hν0 : ∫ y in G, ν y ∂(volume : Measure ({i // i ∉ S} → Ω))
      = ∫ y : {i // i ∉ S} → Ω, ν y := by
    refine MeasureTheory.setIntegral_eq_integral_of_ae_compl_eq_zero ?_
    filter_upwards [hGae] with y hy hyG
    exact absurd hy hyG
  have hGpos : 0 < ∫ y in G, ν y ∂(volume : Measure ({i // i ∉ S} → Ω)) := by
    rw [hν0, hνeq]
    exact hSpos
  -- step 6: the selection inside `G`
  obtain ⟨y, hyG, hypos, hyle⟩ :=
    exists_fibre_le_of_integral_ae_hq0_restrict q ν c G hGm hνnn hq0ae hqint hνint hGint hGpos
  refine ⟨S, y, hypos, hyle, ?_⟩
  intro α hdeg hbad
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
  have hg := hGcoeff y hyG α hαbad
  simpa only [hcoeffdef, hΦcdef] using hg

end Work.BoseBoxFock
