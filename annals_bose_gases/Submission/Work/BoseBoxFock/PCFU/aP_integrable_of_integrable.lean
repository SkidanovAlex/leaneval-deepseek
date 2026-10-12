import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Submission.Work.BoseBoxFock.modeProd_XS_pairing
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.PCFU.aP_integrable_of_integrable`

The condensate slot mean `aP ℓ i Φ` (the average of `Φ` over the centred box in slot `i`)
maps `L¹(abox n ℓ)` into `L¹(abox n ℓ)`: if `Φ` is integrable on the box, then `aP ℓ i Φ`
is a.e. strongly measurable on the box and integrable there.

The corpus statement `Submission.BoseGases.aP_integrableOn` proves this for *continuous*
states only (through a sup-norm bound on the compact box).  Here only integrability is
assumed, and the proof is the peel/Fubini argument.  Write `n = m + 1` and let

    `e = kcInsN m i : E3 × X m ≃ᵐ X (m+1)`

be the insertion into slot `i`, which is measure preserving from
`ν.prod boxM` to `boxN` (`Submission.BoseGases.abox_peel_mp`), where
`ν = volume.restrict (acube ℓ)`, `boxM = volume.restrict (abox m ℓ)`,
`boxN = volume.restrict (abox (m+1) ℓ)`.  Then

* the pullback `Ψ = Φ ∘ e` is integrable on `ν.prod boxM`;
* the fibre average `h r = ∫_ν Ψ (·, r)` is integrable on `boxM` (Fubini);
* for `x = e (y, r)` one has, by `Submission.BoseGases.aP_kcInsN`,
  `aP ℓ i Φ x = (1/ℓ³) · h r`, so `aP ℓ i Φ = ((1/ℓ³) · h ∘ snd) ∘ e.symm`.

The function `(1/ℓ³) · h ∘ snd` is integrable on the product `ν.prod boxM`
(`Integrable.comp_snd`, `Integrable.const_mul`) and a.e. strongly measurable there
(`AEStronglyMeasurable.comp_snd`), and both properties are transported along the
measure-preserving equivalence `e.symm`.
-/

noncomputable section

open MeasureTheory

namespace Work.BoseBoxFock.PCFU

local notation "E3" => EuclideanSpace ℝ (Fin 3)

set_option linter.style.haveILetI false

theorem aP_integrable_of_integrable {n : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) (i : Fin n)
    {Φ : Submission.BoseGases.X n → ℝ}
    (hΦ : MeasureTheory.IntegrableOn Φ (Submission.BoseGases.abox n ℓ) MeasureTheory.volume) :
    MeasureTheory.AEStronglyMeasurable (Submission.BoseGases.aP ℓ i Φ)
        (MeasureTheory.volume.restrict (Submission.BoseGases.abox n ℓ))
      ∧ MeasureTheory.IntegrableOn (Submission.BoseGases.aP ℓ i Φ)
          (Submission.BoseGases.abox n ℓ) MeasureTheory.volume := by
  cases n with
  | zero => exact i.elim0
  | succ m =>
    -- the three measures: the one-particle centred cube, the `m`-box and the `(m+1)`-box
    set ν : Measure E3 := (volume : Measure E3).restrict (Submission.BoseGases.acube ℓ) with hν
    set boxM : Measure (Submission.BoseGases.X m) :=
      (volume : Measure (Submission.BoseGases.X m)).restrict (Submission.BoseGases.abox m ℓ) with hboxM
    set boxN : Measure (Submission.BoseGases.X (m + 1)) :=
      (volume : Measure (Submission.BoseGases.X (m + 1))).restrict
        (Submission.BoseGases.abox (m + 1) ℓ) with hboxN
    have hνfin : IsFiniteMeasure ν :=
      ⟨by rw [hν, Measure.restrict_apply_univ, Submission.BoseGases.acube_volume ℓ hℓ.le]
          exact ENNReal.ofReal_lt_top⟩
    haveI : IsFiniteMeasure ν := hνfin
    have hMfin : IsFiniteMeasure boxM :=
      ⟨by rw [hboxM, Measure.restrict_apply_univ]
          exact Submission.BoseGases.abox_lt_top m ℓ hℓ.le⟩
    haveI : IsFiniteMeasure boxM := hMfin
    -- the peel: insertion into slot `i` is measure preserving from `ν.prod boxM` to `boxN`
    have hmp : MeasurePreserving (⇑(Submission.BoseGases.kcInsN m i)) (ν.prod boxM) boxN := by
      have h := MeasurePreserving.symm
        (e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (m + 1) => E3) i)
        (Submission.BoseGases.abox_peel_mp (n := m) ℓ i)
      simpa [hν, hboxM, hboxN, Submission.BoseGases.kcInsN] using h
    have hΦint : Integrable Φ boxN := hΦ
    -- the pullback of the state to peeled coordinates
    set Ψ : E3 × Submission.BoseGases.X m → ℝ :=
      fun p => Φ ((Submission.BoseGases.kcInsN m i) p) with hΨ
    have hΨint : Integrable Ψ (ν.prod boxM) := by
      have h2 := (hmp.integrable_comp (g := Φ) hΦint.aestronglyMeasurable).mpr hΦint
      simpa [hΨ, Function.comp_def] using h2
    -- the fibre average over the insertion slot
    set h : Submission.BoseGases.X m → ℝ := fun r => ∫ y : E3, Ψ (y, r) ∂ν with hh
    have hhint : Integrable h boxM := by
      have hs : Integrable (fun z : Submission.BoseGases.X m × E3 => Ψ z.swap) (boxM.prod ν) :=
        hΨint.swap
      have h3 := hs.integral_prod_left
      simpa [hh] using h3
    -- its extension to the product is integrable there
    have hWint : Integrable
        (fun p : E3 × Submission.BoseGases.X m => (1 / ℓ ^ 3) * h p.2) (ν.prod boxM) :=
      (hhint.comp_snd ν).const_mul _
    -- the pointwise identification of the slot mean with the fibre average
    have key : ∀ (y : E3) (r : Submission.BoseGases.X m),
        Submission.BoseGases.aP ℓ i Φ ((Submission.BoseGases.kcInsN m i) (y, r))
          = (1 / ℓ ^ 3) * h r := by
      intro y r
      rw [Submission.BoseGases.aP_kcInsN]
    have haP : Submission.BoseGases.aP ℓ i Φ
        = fun x : Submission.BoseGases.X (m + 1) =>
            (1 / ℓ ^ 3) * h ((Submission.BoseGases.kcInsN m i).symm x).2 := by
      funext x
      conv_lhs => rw [← (Submission.BoseGases.kcInsN m i).apply_symm_apply x]
      rw [key]
    refine ⟨?_, ?_⟩
    · rw [haP]
      exact hWint.aestronglyMeasurable.comp_measurePreserving
        (MeasurePreserving.symm (e := Submission.BoseGases.kcInsN m i) hmp)
    · rw [haP]
      exact ((MeasurePreserving.symm (e := Submission.BoseGases.kcInsN m i) hmp).integrable_comp
        hWint.aestronglyMeasurable).mpr hWint

/-! ## The `ℂ`-linear twin

The same argument applies verbatim to the complex slot mean
`Work.BoseBoxFock.aPC ℓ i : (X N → ℂ) → X N → ℂ` (`Submission/Work/BoseBoxFock/slotCountsComplex.lean`),
whose peel form `Work.BoseBoxFock.aPC_kcInsN` is imported here.  This is the form needed by the
cubic-dictionary consumers, which run Fubini/slot manipulations on `ℂ`-valued box states that are
only assumed integrable. -/

theorem aPC_integrable_of_integrable {n : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) (i : Fin n)
    {Φ : Submission.BoseGases.X n → ℂ}
    (hΦ : MeasureTheory.IntegrableOn Φ (Submission.BoseGases.abox n ℓ) MeasureTheory.volume) :
    MeasureTheory.AEStronglyMeasurable (Work.BoseBoxFock.aPC ℓ i Φ)
        (MeasureTheory.volume.restrict (Submission.BoseGases.abox n ℓ))
      ∧ MeasureTheory.IntegrableOn (Work.BoseBoxFock.aPC ℓ i Φ)
          (Submission.BoseGases.abox n ℓ) MeasureTheory.volume := by
  cases n with
  | zero => exact i.elim0
  | succ m =>
    set ν : Measure E3 := (volume : Measure E3).restrict (Submission.BoseGases.acube ℓ) with hν
    set boxM : Measure (Submission.BoseGases.X m) :=
      (volume : Measure (Submission.BoseGases.X m)).restrict (Submission.BoseGases.abox m ℓ) with hboxM
    set boxN : Measure (Submission.BoseGases.X (m + 1)) :=
      (volume : Measure (Submission.BoseGases.X (m + 1))).restrict
        (Submission.BoseGases.abox (m + 1) ℓ) with hboxN
    haveI : IsFiniteMeasure ν :=
      ⟨by rw [hν, Measure.restrict_apply_univ, Submission.BoseGases.acube_volume ℓ hℓ.le]
          exact ENNReal.ofReal_lt_top⟩
    haveI : IsFiniteMeasure boxM :=
      ⟨by rw [hboxM, Measure.restrict_apply_univ]
          exact Submission.BoseGases.abox_lt_top m ℓ hℓ.le⟩
    have hmp : MeasurePreserving (⇑(Submission.BoseGases.kcInsN m i)) (ν.prod boxM) boxN := by
      have h := MeasurePreserving.symm
        (e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (m + 1) => E3) i)
        (Submission.BoseGases.abox_peel_mp (n := m) ℓ i)
      simpa [hν, hboxM, hboxN, Submission.BoseGases.kcInsN] using h
    have hΦint : Integrable Φ boxN := hΦ
    set Ψ : E3 × Submission.BoseGases.X m → ℂ :=
      fun p => Φ ((Submission.BoseGases.kcInsN m i) p) with hΨ
    have hΨint : Integrable Ψ (ν.prod boxM) := by
      have h2 := (hmp.integrable_comp (g := Φ) hΦint.aestronglyMeasurable).mpr hΦint
      simpa [hΨ, Function.comp_def] using h2
    set h : Submission.BoseGases.X m → ℂ := fun r => ∫ y : E3, Ψ (y, r) ∂ν with hh
    have hhint : Integrable h boxM := by
      have hs : Integrable (fun z : Submission.BoseGases.X m × E3 => Ψ z.swap) (boxM.prod ν) :=
        hΨint.swap
      have h3 := hs.integral_prod_left
      simpa [hh] using h3
    have hWint : Integrable
        (fun p : E3 × Submission.BoseGases.X m => ((1 / ℓ ^ 3 : ℝ) : ℂ) * h p.2) (ν.prod boxM) :=
      (hhint.comp_snd ν).const_mul _
    have key : ∀ (y : E3) (r : Submission.BoseGases.X m),
        Work.BoseBoxFock.aPC ℓ i Φ ((Submission.BoseGases.kcInsN m i) (y, r))
          = ((1 / ℓ ^ 3 : ℝ) : ℂ) * h r := by
      intro y r
      rw [Work.BoseBoxFock.aPC_kcInsN]
    have haP : Work.BoseBoxFock.aPC ℓ i Φ
        = fun x : Submission.BoseGases.X (m + 1) =>
            ((1 / ℓ ^ 3 : ℝ) : ℂ) * h ((Submission.BoseGases.kcInsN m i).symm x).2 := by
      funext x
      conv_lhs => rw [← (Submission.BoseGases.kcInsN m i).apply_symm_apply x]
      rw [key]
    refine ⟨?_, ?_⟩
    · rw [haP]
      exact hWint.aestronglyMeasurable.comp_measurePreserving
        (MeasurePreserving.symm (e := Submission.BoseGases.kcInsN m i) hmp)
    · rw [haP]
      exact ((MeasurePreserving.symm (e := Submission.BoseGases.kcInsN m i) hmp).integrable_comp
        hWint.aestronglyMeasurable).mpr hWint

end Work.BoseBoxFock.PCFU
