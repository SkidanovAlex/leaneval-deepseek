import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseBoxFock.sliceForm_zero_of_sliceMass_zero
import Submission.Work.MB.sliceBadCoeff_goodSet_weak
import Submission.Work.MB.sliceMassFubini_weak
import Submission.Work.MB.slotFacts_dec_fibre_ae
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The weak-state twin of `Work.MB.exists_slice_le_window_of_op_ae`

Same statement, with the state hypotheses `Continuous Φ` + `HasCompactSupport Φ` +
`tsupport Φ ⊆ abox n ℓ` replaced by `Measurable Φ` + a global bound + `support Φ ⊆ abox n ℓ`
(the class of the box restriction `Φ·1_abox`).  The only state-dependent input of the proof is
`Work.MB.sliceBadCoeff_goodSet_ae`, replaced by `Work.MB.sliceBadCoeff_goodSet_weak`; step 0
re-derives `hΦm`, `hΦb`, `hΦs` from the new hypotheses, and everything else is verbatim.
-/

namespace Work.MB

open MeasureTheory

local notation "Ω" => EuclideanSpace ℝ (Fin 3)

set_option linter.unusedVariables false
set_option maxHeartbeats 3200000

theorem exists_slice_le_window_of_op_weak {m n : ℕ} [NeZero m] {ℓ M : ℝ}
    (hℓ : 0 < ℓ) {e : Fin m → EuclideanSpace ℝ (Fin 3) → ℂ}
    (hmeas : ∀ l, Measurable (e l)) (hbdE : ∀ l, ∃ C, ∀ x, ‖e l x‖ ≤ C)
    (horth : ∀ l l', (∫ z : EuclideanSpace ℝ (Fin 3), star (e l z) * e l' z)
      = (if l = l' then (1 : ℂ) else 0))
    (hint : ∀ l l', MeasureTheory.Integrable
      (fun z : EuclideanSpace ℝ (Fin 3) => star (e l z) * e l' z))
    (hbdd : ∀ l, MeasureTheory.MemLp (e l) ⊤)
    (hsupp : ∀ l, Function.support (e l) ⊆ Work.BoseK15.corpusBox.boxL ℓ)
    (hpin : ∃ c : ℂ, (starRingEnd ℂ) c * c = (ℓ ^ 3)⁻¹ ∧
      (∀ᵐ x ∂(MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin 3))),
        e 0 x = c * Work.BoseK15.corpusBox.thetaFun ℓ x))
    (Φ : Submission.BoseGases.X n → ℝ) (hΦm0 : Measurable Φ)
    (hΦb0 : ∃ C : ℝ, ∀ x, |Φ x| ≤ C)
    (hΦsupp : Function.support Φ ⊆ Submission.BoseGases.abox n ℓ)
    (hΦsym : ∀ σ : Equiv.Perm (Fin n),
      (fun x : Submission.BoseGases.X n => Φ (x ∘ σ)) = Φ)
    (hM : 0 ≤ M) (hmom : Work.BoseBox.SpectralNPlusLe ℓ M Φ)
    (Φc : Work.BoseDict.Xn n → ℂ)
    (hΦc_eq : Φc = fun x : Work.BoseDict.Xn n => ((Φ x : ℝ) : ℂ))
    (Op : (Work.BoseDict.Xn n → ℂ) → (Work.BoseDict.Xn n → ℂ))
    (OpS : (S : Finset (Fin n)) → (({i // i ∈ S} → EuclideanSpace ℝ (Fin 3)) → ℂ)
      → (({i // i ∈ S} → EuclideanSpace ℝ (Fin 3)) → ℂ))
    (hsplit : (∫ x : Work.BoseDict.Xn n, star (Φc x) * Op Φc x).re
      = ∑ S : Finset (Fin n),
          (∫ x : Work.BoseDict.Xn n, star (Work.BoseBoxFock.slotExact e S Φc x)
            * Op (Work.BoseBoxFock.slotExact e S Φc) x).re)
    (hdec : ∀ S : Finset (Fin n),
      (∫ x : Work.BoseDict.Xn n, star (Work.BoseBoxFock.slotExact e S Φc x)
          * Op (Work.BoseBoxFock.slotExact e S Φc) x).re
        = ∫ y : {i // i ∉ S} → EuclideanSpace ℝ (Fin 3),
            ∫ u : {i // i ∈ S} → EuclideanSpace ℝ (Fin 3),
              (star (Work.BoseBoxFock.sectorSlice e S Φc y u)
                * OpS S (Work.BoseBoxFock.sectorSlice e S Φc y) u).re)
    (hqint : ∀ S : Finset (Fin n),
      MeasureTheory.Integrable (fun y : {i // i ∉ S} → EuclideanSpace ℝ (Fin 3) =>
        ∫ u : {i // i ∈ S} → EuclideanSpace ℝ (Fin 3),
          (star (Work.BoseBoxFock.sectorSlice e S Φc y u)
            * OpS S (Work.BoseBoxFock.sectorSlice e S Φc y) u).re))
    (c : ℝ) (hpos : 0 < Work.BoseBoxFock.massR Φc)
    (hc : (∫ x : Work.BoseDict.Xn n, star (Φc x) * Op Φc x).re
      ≤ c * Work.BoseBoxFock.massR Φc) :
    ∃ (S : Finset (Fin n)) (y : {i // i ∉ S} → EuclideanSpace ℝ (Fin 3)),
      0 < (∫ u : {i // i ∈ S} → EuclideanSpace ℝ (Fin 3),
            ‖Work.BoseBoxFock.sectorSlice e S Φc y u‖ ^ 2) ∧
      (∫ u : {i // i ∈ S} → EuclideanSpace ℝ (Fin 3),
          (star (Work.BoseBoxFock.sectorSlice e S Φc y u)
            * OpS S (Work.BoseBoxFock.sectorSlice e S Φc y) u).re)
        ≤ c * (∫ u : {i // i ∈ S} → EuclideanSpace ℝ (Fin 3),
            ‖Work.BoseBoxFock.sectorSlice e S Φc y u‖ ^ 2) ∧
      (∀ α : Fin m →₀ ℕ, α.sum (fun _ k => k) = S.card →
        ((S.card - α 0 : ℕ) : ℝ) > (⌊M⌋₊ : ℝ) →
        Work.BoseDict.cIPn S.card (Work.BoseDict.modeProd e S.card α)
          (Work.BoseBoxFock.sliceF e S Φc y) = 0) := by
  classical
  -- ## 0. the state data in the weak mode bundle
  have hΦm : Measurable Φc := by
    rw [hΦc_eq]
    exact Complex.continuous_ofReal.measurable.comp hΦm0
  have hΦb : ∃ C, ∀ x, ‖Φc x‖ ≤ C := by
    obtain ⟨C, hC⟩ := hΦb0
    refine ⟨max C 0, fun x => ?_⟩
    rw [hΦc_eq, Complex.norm_real, Real.norm_eq_abs]
    exact le_trans (hC x) (le_max_left C 0)
  have hΦs : Function.support Φc ⊆ boxPow n ℓ := by
    intro x hx
    rw [mem_boxPow_iff]
    intro i
    simp only [Function.mem_support] at hx
    rw [hΦc_eq] at hx
    have hx1 : Φ x ≠ 0 := by
      simpa using hx
    have hx2 : x ∈ Submission.BoseGases.abox n ℓ :=
      hΦsupp (Function.mem_support.mpr hx1)
    exact acube_subset_boxL_all ((Submission.BoseGases.mem_abox_iff n ℓ x).mp hx2 i)
  -- ## 1. the sector data
  have hsecm : ∀ S : Finset (Fin n), Measurable (Work.BoseBoxFock.slotExact e S Φc) :=
    fun S => (slotExact_mb_weak hmeas hbdE hsupp S hΦm hΦb).1
  have hsecb : ∀ S : Finset (Fin n),
      ∃ C, ∀ x, ‖Work.BoseBoxFock.slotExact e S Φc x‖ ≤ C :=
    fun S => ((slotExact_mb_weak hmeas hbdE hsupp S hΦm hΦb).2.1).imp (fun C hC => hC.2)
  have hsecs : ∀ S : Finset (Fin n),
      Function.support (Work.BoseBoxFock.slotExact e S Φc) ⊆ boxPow n ℓ :=
    fun S => (slotExact_mb_weak hmeas hbdE hsupp S hΦm hΦb).2.2 hΦs
  have hintΦ : ∀ S : Finset (Fin n),
      MeasureTheory.Integrable (fun x : Work.BoseDict.Xn n =>
        star (Φc x) * Work.BoseBoxFock.slotExact e S Φc x) :=
    fun S => integrable_star_mul_of_support_boxPow hΦm hΦb hΦs (hsecm S) (hsecb S) (hsecs S)
  -- ## 2. the mass splits over the fibre sectors
  have hmass : Work.BoseBoxFock.massR Φc
      = ∑ S : Finset (Fin n), Work.BoseBoxFock.massR (Work.BoseBoxFock.slotExact e S Φc) := by
    have horthC : ∀ S : Finset (Fin n),
        (∫ x : Work.BoseDict.Xn n, star (Φc x) * Work.BoseBoxFock.slotExact e S Φc x)
          = (∫ x : Work.BoseDict.Xn n, star (Work.BoseBoxFock.slotExact e S Φc x)
              * Work.BoseBoxFock.slotExact e S Φc x) := by
      intro S
      have h := slotExact_orth_ae hmeas hbdE hsupp horth S S Φc Φc hΦm hΦb hΦs hΦm hΦb hΦs
      rw [if_pos rfl] at h
      exact h.symm
    rw [Work.BoseBoxFock.massR]
    have hpt : (fun x : Work.BoseDict.Xn n => star (Φc x) * Φc x)
        = fun x => ∑ S : Finset (Fin n),
            star (Φc x) * Work.BoseBoxFock.slotExact e S Φc x := by
      funext x
      have hx : (∑ S : Finset (Fin n), Work.BoseBoxFock.slotExact e S Φc x) = Φc x := by
        simpa only [Finset.sum_apply] using congrFun (Work.BoseBoxFock.slotExact_sum_eq e Φc) x
      rw [← Finset.mul_sum, hx]
    rw [hpt, MeasureTheory.integral_finsetSum _ (fun S _ => hintΦ S),
      Finset.sum_congr rfl (fun S _ => horthC S)]
    simp [Work.BoseBoxFock.massR]
  -- ## 3. the fibre (slice) mass of a sector
  have hfib : ∀ S : Finset (Fin n),
      MeasureTheory.Integrable (fun y : {i // i ∉ S} → Ω =>
        ∫ u : {i // i ∈ S} → Ω,
          ‖Work.BoseBoxFock.sectorSlice e S Φc y u‖ ^ 2) ∧
      (∫ y : {i // i ∉ S} → Ω, ∫ u : {i // i ∈ S} → Ω,
          ‖Work.BoseBoxFock.sectorSlice e S Φc y u‖ ^ 2)
        = Work.BoseBoxFock.massR (Work.BoseBoxFock.slotExact e S Φc) :=
    fun S => ⟨(sliceMassFubini_weak hmeas hbdE hsupp S Φc hΦm hΦb hΦs).2.1,
      (sliceMassFubini_weak hmeas hbdE hsupp S Φc hΦm hΦb hΦs).2.2⟩
  have hsliceIntAe : ∀ S : Finset (Fin n), ∀ᵐ y : {i // i ∉ S} → Ω,
      MeasureTheory.Integrable (fun u : {i // i ∈ S} → Ω =>
        ‖Work.BoseBoxFock.sectorSlice e S Φc y u‖ ^ 2) :=
    fun S => (sliceMassFubini_weak hmeas hbdE hsupp S Φc hΦm hΦb hΦs).1
  -- ## 4. the degenerate slice: vanishing mass kills every slice form (a.e. in `y`)
  have hform0 : ∀ S : Finset (Fin n), ∀ᵐ y : {i // i ∉ S} → Ω,
      (∫ u : {i // i ∈ S} → Ω,
        ‖Work.BoseBoxFock.sectorSlice e S Φc y u‖ ^ 2) = 0 →
      (∫ u : {i // i ∈ S} → Ω,
          (star (Work.BoseBoxFock.sectorSlice e S Φc y u)
            * OpS S (Work.BoseBoxFock.sectorSlice e S Φc y) u).re) = 0 := by
    intro S
    filter_upwards [hsliceIntAe S] with y hy h0
    exact Work.BoseBoxFock.integral_re_star_mul_eq_zero_of_ae_eq_zero
      (Work.BoseBoxFock.sectorSlice_mass_eq_zero_ae e S Φc y hy h0)
  -- ## 5. the sector functionals
  set qS : Finset (Fin n) → ℝ := fun S =>
    (∫ x : Work.BoseDict.Xn n, star (Work.BoseBoxFock.slotExact e S Φc x)
      * Op (Work.BoseBoxFock.slotExact e S Φc) x).re with hqSdef
  set νS : Finset (Fin n) → ℝ :=
    fun S => Work.BoseBoxFock.massR (Work.BoseBoxFock.slotExact e S Φc) with hνSdef
  -- ## 6. a sector of vanishing mass carries no charge
  have hq0sum : ∀ S : Finset (Fin n), νS S = 0 → qS S = 0 := by
    intro S hS0
    have hS0' : Work.BoseBoxFock.massR (Work.BoseBoxFock.slotExact e S Φc) = 0 := hS0
    obtain ⟨hνint, hνeq⟩ := hfib S
    have hνz : (∫ y : {i // i ∉ S} → Ω, ∫ u : {i // i ∈ S} → Ω,
        ‖Work.BoseBoxFock.sectorSlice e S Φc y u‖ ^ 2) = 0 := by
      rw [hνeq, hS0']
    have hνae : (fun y : {i // i ∉ S} → Ω =>
        ∫ u : {i // i ∈ S} → Ω,
          ‖Work.BoseBoxFock.sectorSlice e S Φc y u‖ ^ 2) =ᵐ[volume] 0 :=
      (MeasureTheory.integral_eq_zero_iff_of_nonneg_ae
        (Filter.Eventually.of_forall fun y => integral_nonneg fun u => by positivity)
        hνint).mp hνz
    have hzero : (∫ y : {i // i ∉ S} → Ω, ∫ u : {i // i ∈ S} → Ω,
        (star (Work.BoseBoxFock.sectorSlice e S Φc y u)
          * OpS S (Work.BoseBoxFock.sectorSlice e S Φc y) u).re) = 0 := by
      refine MeasureTheory.integral_eq_zero_of_ae ?_
      filter_upwards [hνae, hform0 S] with y hy hy0
      exact hy0 hy
    have hmain : (∫ x : Work.BoseDict.Xn n,
        star (Work.BoseBoxFock.slotExact e S Φc x)
          * Op (Work.BoseBoxFock.slotExact e S Φc) x).re = 0 := by
      rw [hdec S, hzero]
    exact hmain
  -- ## 7. the summed inequality and the sector selection
  have hνnn : ∀ S : Finset (Fin n), 0 ≤ νS S := fun S => Work.BoseBoxFock.massR_nonneg _
  have hsumle : ∑ S : Finset (Fin n), qS S ≤ c * ∑ S : Finset (Fin n), νS S := by
    rw [← hsplit, ← hmass]
    exact hc
  have hcpos : 0 < ∑ S : Finset (Fin n), νS S := by
    rw [← hmass]
    exact hpos
  obtain ⟨S, -, hSpos, hSle⟩ :=
    Work.BoseBoxFock.exists_fibre_le_of_sum_le (Finset.univ : Finset (Finset (Fin n)))
      qS νS (fun S _ => hνnn S) (fun S _ => hq0sum S) hcpos hsumle
  -- ## 8. the fibre-level objects at the selected sector
  set ν : ({i // i ∉ S} → Ω) → ℝ :=
    fun y => ∫ u : {i // i ∈ S} → Ω,
      ‖Work.BoseBoxFock.sectorSlice e S Φc y u‖ ^ 2 with hνdef
  set q : ({i // i ∉ S} → Ω) → ℝ :=
    fun y => ∫ u : {i // i ∈ S} → Ω,
      (star (Work.BoseBoxFock.sectorSlice e S Φc y u)
        * OpS S (Work.BoseBoxFock.sectorSlice e S Φc y) u).re with hqdef
  have hqi : MeasureTheory.Integrable q (volume : Measure (({i // i ∉ S} → Ω))) := hqint S
  have hνi : MeasureTheory.Integrable ν (volume : Measure (({i // i ∉ S} → Ω))) := (hfib S).1
  have hqint_eq : (∫ y : {i // i ∉ S} → Ω, q y) = qS S := by
    simp only [hqdef]
    exact (hdec S).symm
  have hνint_eq : (∫ y : {i // i ∉ S} → Ω, ν y) = νS S := by
    simp only [hνdef]
    exact (hfib S).2
  -- ## 9. the good set (the window condition)
  obtain ⟨G, hGm, hGae, hGwin⟩ :=
    sliceBadCoeff_goodSet_weak hℓ hmeas hbdE horth hsupp hpin Φ hΦm0 hΦb0 hΦsupp hM hmom S
  -- ## 10. the restricted inequalities
  have hνnn' : ∀ y, 0 ≤ ν y := fun y => integral_nonneg fun u => by positivity
  have hq0ae : ∀ᵐ y ∂(volume : Measure (({i // i ∉ S} → Ω))), ν y = 0 → q y = 0 := by
    filter_upwards [hform0 S] with y hy h0
    have h0' : (∫ u : {i // i ∈ S} → Ω,
        ‖Work.BoseBoxFock.sectorSlice e S Φc y u‖ ^ 2) = 0 := by
      simpa only [hνdef] using h0
    simpa only [hqdef] using hy h0'
  have hsub0 : (∫ y in G, (q y - c * ν y)) = ∫ y : {i // i ∉ S} → Ω, (q y - c * ν y) := by
    refine MeasureTheory.setIntegral_eq_integral_of_ae_compl_eq_zero ?_
    filter_upwards [hGae] with y hy hyG
    exact absurd hy hyG
  have hGint : (∫ y in G, (q y - c * ν y)) ≤ 0 := by
    rw [hsub0, MeasureTheory.integral_sub hqi (hνi.const_mul c),
      MeasureTheory.integral_const_mul, hqint_eq, hνint_eq]
    linarith [hSle]
  have hν0 : (∫ y in G, ν y) = ∫ y : {i // i ∉ S} → Ω, ν y := by
    refine MeasureTheory.setIntegral_eq_integral_of_ae_compl_eq_zero ?_
    filter_upwards [hGae] with y hy hyG
    exact absurd hy hyG
  have hGpos : 0 < ∫ y in G, ν y := by
    rw [hν0, hνint_eq]
    exact hSpos
  -- ## 11. the selection inside the good set
  obtain ⟨y, hyG, hypos, hyle⟩ :=
    Work.BoseBoxFock.exists_fibre_le_of_integral_ae_hq0_restrict q ν c G hGm hνnn' hq0ae
      hqi hνi hGint hGpos
  simp only [hνdef] at hypos
  simp only [hqdef, hνdef] at hyle
  exact ⟨S, y, hypos, hyle, fun α hdeg hbad => by
    simpa only [hΦc_eq] using hGwin y hyG α hdeg hbad⟩


end Work.MB
