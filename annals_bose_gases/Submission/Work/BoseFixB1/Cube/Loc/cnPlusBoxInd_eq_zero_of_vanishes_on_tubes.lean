import Mathlib.Tactic.Have
import Mathlib.Topology.Separation.CompletelyRegular
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseFixB1S.boxPInd_ae_eq_zero_of_ae_eq_zero
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixB1.Cube.Loc.cnPlusBoxInd_eq_zero_of_vanishes_on_tubes`

FS `eq:HBU`: the excited (mean-free) count of the box `B` in a state `Ψ` is

  `n₊(B) = cnPlusBoxInd a A V Ψ = Σ_i ∫_{abox} (Q_{B,i}Ψ)²`,

with `Q_{B,i}Ψ = 1_A(x i)·Ψ - P_{B,i}Ψ` and `P_{B,i}` FS's box projection
(`Work.UBBInputs8.boxPInd`, carrying the box indicator).

**Statement.**  If `Ψ` vanishes a.e. on *every* tube `{w | w j ∈ A}` (intersected with the box)
— in particular `Ψ` is carried by configurations with no particle in `A` — then `n₊(B) = 0`.

**Proof.**  Two observations.

* `Φ := 1_A(x i)·Ψ` is a.e. zero on the box (on the tube this is the hypothesis, off the tube the
  indicator kills it), and `P_{B,i}Φ = P_{B,i}Ψ` *pointwise*, because for `z ∈ A` the updated
  configuration `x|i↦z` has its `i`-th slot in `A`, so `Φ(x|i↦z) = Ψ(x|i↦z)`.
  Hence `Q_{B,i}Ψ = Q_{B,i}Φ` pointwise.
* For an a.e.-vanishing state, `P_{B,i}` of it is a.e. zero
  (`boxPInd_ae_eq_zero_of_ae_eq_zero_aux`, the `volA`-identification-free version of the tree's
  `Work.BoseFixB1S.boxPInd_ae_eq_zero_of_ae_eq_zero`), so `Q_{B,i}Φ = Φ - P_{B,i}Φ` is a.e. zero.

Each summand `∫_{abox} (Q_{B,i}Ψ)²` is therefore the integral of a function that vanishes a.e.,
whence `n₊(B) = 0`.
-/

namespace Work.BoseFixB1.Cube.Loc

open MeasureTheory
open scoped BigOperators ENNReal

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 2000000

/-- **The box projection of an a.e.-vanishing state vanishes a.e.**

This is `Work.BoseFixB1S.boxPInd_ae_eq_zero_of_ae_eq_zero` with the three hypotheses
`0 < ℓ`, `0 < volA`, `volA = (volume A).toReal` removed: the proof of that lemma never uses them
(they are linter-flagged as unused variables in its source). -/
theorem boxPInd_ae_eq_zero_of_ae_eq_zero_aux {N : ℕ} {ℓ volA : ℝ}
    {A : Set (EuclideanSpace ℝ (Fin 3))} (hA : MeasurableSet A)
    (hAc : A ⊆ Submission.BoseGases.acube ℓ) (i : Fin N)
    {Φ : Submission.BoseGases.X N → ℝ} (hΦm : Measurable Φ)
    (hΦ : Φ =ᵐ[MeasureTheory.volume.restrict (Submission.BoseGases.abox N ℓ)] 0) :
    Work.UBBInputs8.boxPInd volA A i Φ
      =ᵐ[MeasureTheory.volume.restrict (Submission.BoseGases.abox N ℓ)] 0 := by
  classical
  rcases N with _ | n
  · exact i.elim0
  -- ### the measure-preserving peel at slot `i`, and its inverse (`kcInsN n i`)
  have hmp : MeasurePreserving
      (⇑(MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ³) i))
      (MeasureTheory.volume.restrict (Submission.BoseGases.abox (n + 1) ℓ))
      (((MeasureTheory.volume : Measure ℝ³).restrict (Submission.BoseGases.acube ℓ)).prod
        ((MeasureTheory.volume : Measure (Submission.BoseGases.X n)).restrict
          (Submission.BoseGases.abox n ℓ))) :=
    Submission.BoseGases.abox_peel_mp (n := n) ℓ i
  have hkc : ∀ x : Submission.BoseGases.X (n + 1),
      Submission.BoseGases.kcInsN n i
        (⇑(MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ³) i) x) = x := by
    intro x
    simp only [Submission.BoseGases.kcInsN, MeasurableEquiv.symm_apply_apply]
  -- ### the a.e.-zero set in the product space `ℝ³ × X n` is measurable …
  have hZmeas : MeasurableSet {q : ℝ³ × Submission.BoseGases.X n |
      Φ (Submission.BoseGases.kcInsN n i q) ≠ 0} := by
    have h : MeasurableSet ((fun q : ℝ³ × Submission.BoseGases.X n =>
        Φ (Submission.BoseGases.kcInsN n i q)) ⁻¹' ({0}ᶜ : Set ℝ)) :=
      (hΦm.comp (Submission.BoseGases.kcInsN n i).measurable) (measurableSet_singleton 0).compl
    convert h using 1
    ext q
    simp
  -- … and the a.e.-zero set in the box is null
  have hnull : (MeasureTheory.volume.restrict (Submission.BoseGases.abox (n + 1) ℓ))
      {x : Submission.BoseGases.X (n + 1) | Φ x ≠ 0} = 0 := by
    have hΦ' : ∀ᵐ x ∂(MeasureTheory.volume.restrict (Submission.BoseGases.abox (n + 1) ℓ)),
        Φ x = 0 := hΦ
    simpa using MeasureTheory.ae_iff.mp hΦ'
  -- ### … hence the product space set is null
  have hZnull :
      (((MeasureTheory.volume : Measure ℝ³).restrict (Submission.BoseGases.acube ℓ)).prod
        ((MeasureTheory.volume : Measure (Submission.BoseGases.X n)).restrict
          (Submission.BoseGases.abox n ℓ)))
      {q : ℝ³ × Submission.BoseGases.X n | Φ (Submission.BoseGases.kcInsN n i q) ≠ 0} = 0 := by
    have hpre : ⇑(MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ³) i) ⁻¹'
        {q : ℝ³ × Submission.BoseGases.X n | Φ (Submission.BoseGases.kcInsN n i q) ≠ 0}
        = {x : Submission.BoseGases.X (n + 1) | Φ x ≠ 0} := by
      ext x
      simp only [Set.mem_preimage, Set.mem_setOf_eq]
      rw [hkc x]
    calc (((MeasureTheory.volume : Measure ℝ³).restrict (Submission.BoseGases.acube ℓ)).prod
            ((MeasureTheory.volume : Measure (Submission.BoseGases.X n)).restrict
              (Submission.BoseGases.abox n ℓ)))
            {q : ℝ³ × Submission.BoseGases.X n | Φ (Submission.BoseGases.kcInsN n i q) ≠ 0}
        = (MeasureTheory.volume.restrict (Submission.BoseGases.abox (n + 1) ℓ))
            (⇑(MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ³) i) ⁻¹'
              {q : ℝ³ × Submission.BoseGases.X n |
                Φ (Submission.BoseGases.kcInsN n i q) ≠ 0}) :=
          (hmp.measure_preimage hZmeas.nullMeasurableSet).symm
      _ = (MeasureTheory.volume.restrict (Submission.BoseGases.abox (n + 1) ℓ))
            {x : Submission.BoseGases.X (n + 1) | Φ x ≠ 0} := by rw [hpre]
      _ = 0 := hnull
  -- ### the section function `r ↦ μA {t | Φ (kcInsN n i (t,r)) ≠ 0}` is measurable …
  have hφmeas : Measurable (fun r : Submission.BoseGases.X n =>
      ((MeasureTheory.volume : Measure ℝ³).restrict (Submission.BoseGases.acube ℓ))
        {t : ℝ³ | Φ (Submission.BoseGases.kcInsN n i (t, r)) ≠ 0}) :=
    measurable_measure_prodMk_right
      (μ := (MeasureTheory.volume : Measure ℝ³).restrict (Submission.BoseGases.acube ℓ)) hZmeas
  -- … so the set of slots whose section does not vanish is measurable …
  have hBadmeas : MeasurableSet {r : Submission.BoseGases.X n |
      ¬ (((MeasureTheory.volume : Measure ℝ³).restrict (Submission.BoseGases.acube ℓ))
        {t : ℝ³ | Φ (Submission.BoseGases.kcInsN n i (t, r)) ≠ 0} = 0)} := by
    have h : MeasurableSet ((fun r : Submission.BoseGases.X n =>
        ((MeasureTheory.volume : Measure ℝ³).restrict (Submission.BoseGases.acube ℓ))
          {t : ℝ³ | Φ (Submission.BoseGases.kcInsN n i (t, r)) ≠ 0}) ⁻¹'
            ({0}ᶜ : Set ℝ≥0∞)) :=
      hφmeas (measurableSet_singleton 0).compl
    convert h using 1
    ext r
    simp
  -- ### Fubini: for a.e. slot the section is null
  have hsec : ∀ᵐ r ∂((MeasureTheory.volume : Measure (Submission.BoseGases.X n)).restrict
        (Submission.BoseGases.abox n ℓ)),
      ((MeasureTheory.volume : Measure ℝ³).restrict (Submission.BoseGases.acube ℓ))
        {t : ℝ³ | Φ (Submission.BoseGases.kcInsN n i (t, r)) ≠ 0} = 0 :=
    Work.Measure.ae_measure_section_right_null
      ((MeasureTheory.volume : Measure ℝ³).restrict (Submission.BoseGases.acube ℓ))
      ((MeasureTheory.volume : Measure (Submission.BoseGases.X n)).restrict
        (Submission.BoseGases.abox n ℓ)) hZmeas hZnull
  -- … and hence that set is null
  have hBadnull : ((MeasureTheory.volume : Measure (Submission.BoseGases.X n)).restrict
      (Submission.BoseGases.abox n ℓ))
      {r : Submission.BoseGases.X n |
        ¬ (((MeasureTheory.volume : Measure ℝ³).restrict (Submission.BoseGases.acube ℓ))
          {t : ℝ³ | Φ (Submission.BoseGases.kcInsN n i (t, r)) ≠ 0} = 0)} = 0 :=
    MeasureTheory.ae_iff.mp hsec
  -- ### the slot mean of `Φ` over `A` vanishes whenever the section is null
  have hgood : ∀ r : Submission.BoseGases.X n,
      (((MeasureTheory.volume : Measure ℝ³).restrict (Submission.BoseGases.acube ℓ))
        {t : ℝ³ | Φ (Submission.BoseGases.kcInsN n i (t, r)) ≠ 0} = 0) →
      (∫ t in A, Φ (Submission.BoseGases.kcInsN n i (t, r))) = 0 := by
    intro r hr
    have h1 : (fun t : ℝ³ => Φ (Submission.BoseGases.kcInsN n i (t, r)))
        =ᵐ[(MeasureTheory.volume : Measure ℝ³).restrict (Submission.BoseGases.acube ℓ)] 0 :=
      MeasureTheory.ae_iff.mpr (by simpa using hr)
    have h2 : (fun t : ℝ³ => Φ (Submission.BoseGases.kcInsN n i (t, r)))
        =ᵐ[(MeasureTheory.volume : Measure ℝ³).restrict A] 0 := by
      have h := h1.filter_mono (MeasureTheory.ae_mono
        (MeasureTheory.Measure.restrict_le_self (s := A)))
      rwa [MeasureTheory.Measure.restrict_restrict_of_subset hAc] at h
    rw [MeasureTheory.setIntegral_eq_zero_of_ae_eq_zero]
    rwa [← MeasureTheory.ae_restrict_iff' hA]
  -- ### peels apart `P_iΦ`: it vanishes as soon as the section is null
  have hcover : {q : ℝ³ × Submission.BoseGases.X n |
        Work.UBBInputs8.boxPInd volA A i Φ (Submission.BoseGases.kcInsN n i q) ≠ 0}
      ⊆ Set.univ ×ˢ {r : Submission.BoseGases.X n |
        ¬ (((MeasureTheory.volume : Measure ℝ³).restrict (Submission.BoseGases.acube ℓ))
          {t : ℝ³ | Φ (Submission.BoseGases.kcInsN n i (t, r)) ≠ 0} = 0)} := by
    rintro ⟨t, r⟩ hq
    exact ⟨Set.mem_univ _, by
      by_contra hcon
      refine hq ?_
      rw [Work.BoseFixB1S.Q0C.boxPInd_kcInsN volA A i Φ t r, hgood r (by simpa using hcon)]
      ring⟩
  -- ### so `P_iΦ ∘ kcInsN` vanishes `μA ⊗ ν`-a.e. on the product space
  have hSnull : (((MeasureTheory.volume : Measure ℝ³).restrict (Submission.BoseGases.acube ℓ)).prod
      ((MeasureTheory.volume : Measure (Submission.BoseGases.X n)).restrict
        (Submission.BoseGases.abox n ℓ)))
      {q : ℝ³ × Submission.BoseGases.X n |
        Work.UBBInputs8.boxPInd volA A i Φ (Submission.BoseGases.kcInsN n i q) ≠ 0} = 0 := by
    refine le_antisymm ?_ (by simp)
    calc (((MeasureTheory.volume : Measure ℝ³).restrict (Submission.BoseGases.acube ℓ)).prod
            ((MeasureTheory.volume : Measure (Submission.BoseGases.X n)).restrict
              (Submission.BoseGases.abox n ℓ)))
            {q : ℝ³ × Submission.BoseGases.X n |
              Work.UBBInputs8.boxPInd volA A i Φ (Submission.BoseGases.kcInsN n i q) ≠ 0}
        ≤ (((MeasureTheory.volume : Measure ℝ³).restrict (Submission.BoseGases.acube ℓ)).prod
            ((MeasureTheory.volume : Measure (Submission.BoseGases.X n)).restrict
              (Submission.BoseGases.abox n ℓ)))
            (Set.univ ×ˢ {r : Submission.BoseGases.X n |
              ¬ (((MeasureTheory.volume : Measure ℝ³).restrict (Submission.BoseGases.acube ℓ))
                {t : ℝ³ | Φ (Submission.BoseGases.kcInsN n i (t, r)) ≠ 0} = 0)}) :=
          measure_mono hcover
      _ = ((MeasureTheory.volume : Measure ℝ³).restrict (Submission.BoseGases.acube ℓ)) Set.univ
            * ((MeasureTheory.volume : Measure (Submission.BoseGases.X n)).restrict
                (Submission.BoseGases.abox n ℓ))
              {r : Submission.BoseGases.X n |
                ¬ (((MeasureTheory.volume : Measure ℝ³).restrict
                    (Submission.BoseGases.acube ℓ))
                  {t : ℝ³ | Φ (Submission.BoseGases.kcInsN n i (t, r)) ≠ 0} = 0)} :=
          Measure.prod_prod _ _
      _ = 0 := by rw [hBadnull, mul_zero]
  -- ### transport back to the box
  have hSnullmeas : NullMeasurableSet
      {q : ℝ³ × Submission.BoseGases.X n |
        Work.UBBInputs8.boxPInd volA A i Φ (Submission.BoseGases.kcInsN n i q) ≠ 0}
      (((MeasureTheory.volume : Measure ℝ³).restrict (Submission.BoseGases.acube ℓ)).prod
        ((MeasureTheory.volume : Measure (Submission.BoseGases.X n)).restrict
          (Submission.BoseGases.abox n ℓ))) :=
    NullMeasurableSet.of_null hSnull
  have hsetpre : {x : Submission.BoseGases.X (n + 1) |
        Work.UBBInputs8.boxPInd volA A i Φ x ≠ 0}
      = ⇑(MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ³) i) ⁻¹'
        {q : ℝ³ × Submission.BoseGases.X n |
          Work.UBBInputs8.boxPInd volA A i Φ (Submission.BoseGases.kcInsN n i q) ≠ 0} := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_preimage]
    rw [hkc x]
  have hboxnull : (MeasureTheory.volume.restrict (Submission.BoseGases.abox (n + 1) ℓ))
      {x : Submission.BoseGases.X (n + 1) | Work.UBBInputs8.boxPInd volA A i Φ x ≠ 0} = 0 := by
    rw [hsetpre, hmp.measure_preimage hSnullmeas]
    exact hSnull
  exact MeasureTheory.ae_iff.mpr hboxnull

/-- **`n₊(B) = 0` for a state vanishing a.e. on every tube `{w | w j ∈ A}`.** -/
theorem cnPlusBoxInd_eq_zero_of_vanishes_on_tubes {m : ℕ} {a V : ℝ} (ha : 0 < a)
    {A : Set (EuclideanSpace ℝ (Fin 3))} (hA : MeasurableSet A)
    (hAc : A ⊆ Submission.BoseGases.acube a)
    {Ψ : Submission.BoseGases.X m → ℝ} (hΨm : Measurable Ψ)
    (h : ∀ j : Fin m,
      Ψ =ᵐ[((MeasureTheory.volume : MeasureTheory.Measure (Submission.BoseGases.X m)).restrict
        (Submission.BoseGases.abox m a)).restrict {w | w j ∈ A}] 0) :
    Work.UBBInputs8.cnPlusBoxInd a A V Ψ = 0 := by
  classical
  rw [Work.UBBInputs8.cnPlusBoxInd]
  refine Finset.sum_eq_zero (fun i _ => ?_)
  -- the tube of slot `i` is measurable
  have hTube : MeasurableSet {w : Submission.BoseGases.X m | w i ∈ A} :=
    (measurable_pi_apply i) hA
  -- the tube-carried part of `Ψ`
  set Φ : Submission.BoseGases.X m → ℝ :=
    fun x => A.indicator (fun _ => (1 : ℝ)) (x i) * Ψ x with hΦdef
  have hΦm : Measurable Φ := by
    rw [hΦdef]
    exact ((measurable_const.indicator hA).comp (measurable_pi_apply i)).mul hΨm
  -- `Φ` vanishes a.e. on the box
  have hΦ : Φ =ᵐ[MeasureTheory.volume.restrict (Submission.BoseGases.abox m a)] 0 := by
    have hh : ∀ᵐ x ∂(MeasureTheory.volume.restrict (Submission.BoseGases.abox m a)),
        x ∈ {w : Submission.BoseGases.X m | w i ∈ A} → Ψ x = 0 :=
      (MeasureTheory.ae_restrict_iff' hTube).mp (h i)
    filter_upwards [hh] with x hx
    by_cases hxi : x i ∈ A
    · simp only [hΦdef, Set.indicator_of_mem hxi, Pi.one_apply, one_mul, Pi.zero_apply]
      exact hx hxi
    · simp only [hΦdef, Set.indicator_of_notMem hxi, Pi.one_apply, zero_mul, Pi.zero_apply]
  -- `P_i` of `Φ` vanishes a.e.
  have hP := boxPInd_ae_eq_zero_of_ae_eq_zero_aux (N := m) (ℓ := a) (volA := V) hA hAc i hΦm hΦ
  -- `Q_{B,i}Φ = Φ - P_iΦ` pointwise, hence vanishes a.e.
  have hQΦ : Work.UBBInputs8.boxQInd V A i Φ
      =ᵐ[MeasureTheory.volume.restrict (Submission.BoseGases.abox m a)] 0 := by
    have hpt : ∀ x, Work.UBBInputs8.boxQInd V A i Φ x
        = Φ x - Work.UBBInputs8.boxPInd V A i Φ x := by
      intro x
      by_cases hxi : x i ∈ A
      · rw [Work.UBBInputs8.boxQInd]
        simp only [Set.indicator_of_mem hxi, Pi.one_apply, one_mul]
      · rw [Work.UBBInputs8.boxQInd]
        simp only [hΦdef, Set.indicator_of_notMem hxi, Pi.one_apply, zero_mul]
    filter_upwards [hΦ, hP] with x hx1 hx2
    rw [hpt x, hx1, hx2]
    simp
  -- `Q_{B,i}Ψ = Q_{B,i}Φ` pointwise
  have hcongr : ∀ x, Work.UBBInputs8.boxQInd V A i Ψ x = Work.UBBInputs8.boxQInd V A i Φ x := by
    intro x
    -- the two `boxPInd` values agree: on `A` the integrands coincide
    have hPind : Work.UBBInputs8.boxPInd V A i Φ x = Work.UBBInputs8.boxPInd V A i Ψ x := by
      have hI : (∫ z in A, Φ (Function.update x i z))
          = (∫ z in A, Ψ (Function.update x i z)) := by
        refine MeasureTheory.setIntegral_congr_fun hA (fun z hz => ?_)
        simp only [hΦdef, Function.update_self, Set.indicator_of_mem hz, Pi.one_apply, one_mul]
      simp only [Work.UBBInputs8.boxPInd, hI]
    rw [Work.UBBInputs8.boxQInd, Work.UBBInputs8.boxQInd, hPind, hΦdef]
    by_cases hxi : x i ∈ A
    · simp only [Set.indicator_of_mem hxi, Pi.one_apply, one_mul]
    · simp only [Set.indicator_of_notMem hxi, Pi.one_apply, zero_mul]
  have hQΨ : Work.UBBInputs8.boxQInd V A i Ψ
      =ᵐ[MeasureTheory.volume.restrict (Submission.BoseGases.abox m a)] 0 := by
    filter_upwards [hQΦ] with x hx
    rw [hcongr x, hx]
  -- the summand is the integral of an a.e.-vanishing function
  have hsq : (fun x =>
        (Work.UBBInputs8.boxQInd V A i Ψ x) ^ 2)
      =ᵐ[MeasureTheory.volume.restrict (Submission.BoseGases.abox m a)] 0 := by
    filter_upwards [hQΨ] with x hx
    simp [hx]
  rw [MeasureTheory.integral_congr_ae hsq]
  simp

end Work.BoseFixB1.Cube.Loc
