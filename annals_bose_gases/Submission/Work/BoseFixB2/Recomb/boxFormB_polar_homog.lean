import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseFixB2.Polar.boxFormB_parallelogram
import Submission.Work.BoseFixB2.Recomb.fsT_hpol
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixB2.Recomb.boxFormB_polar_homog`

**The box-restricted word `boxFormB` of FS `eq:Def_HB` is homogeneously polarised.**

For every real `t` and smooth `N`-body states `Φ, Ψ`,

`boxFormB (t·Φ + Ψ) − boxFormB (t·Φ − Ψ) = t · (boxFormB (Φ + Ψ) − boxFormB (Φ − Ψ))`,

i.e. the polar form `B Φ Ψ = (boxFormB (Φ+Ψ) − boxFormB (Φ−Ψ))/4` is `ℝ`-homogeneous in its
first variable.  Together with the parallelogram law (`Polar.boxFormB_parallelogram`) and
`2`-homogeneity (`Polar.boxFormB_smul`) this is exactly the `hpol` hypothesis of
`Work.BoseFixB2.Polar.par_polarisation_hpol`, i.e. it makes `boxFormB` the diagonal of a
genuine real-bilinear form — the content of FS §6 (`lem:LocMatrices`).

## Route

`boxFormB = kinFormB + ∫_{abox}(·)²·potWordU` (`Work.BoseKinLoc.boxFormB`), and the two parts
are handled separately:

* **kinetic**: slot by slot, the slot-`i` fibre is linear in the state
  (`fibre i (t·Φ+Ψ) x = t·(fibre i Φ x) + (fibre i Ψ x)`), so the one-body polar homogeneity
  `Work.BoseFixB2.Recomb.fsT_hpol` applies to each fibre; the passage from the pointwise
  identity to the box integral is `setIntegral_sub_eq_smul_sub`, whose integrability inputs are
  `Work.BoseFixB2.Sector.integrableOn_fsT_fibre_smooth` (`kinFormB_hpol`);
* **potential**: the profile `potWordU` does not depend on the state, so this is the pointwise
  identity `(tΦ+Ψ)² − (tΦ−Ψ)² = t((Φ+Ψ)² − (Φ−Ψ)²)` integrated against it
  (`potIntB_hpol`).

The hypotheses are exactly those of `Polar.boxFormB_parallelogram`: smoothness of the two
states (so that the slot integrands are integrable) and integrability of `potWordU` on the box.
-/

noncomputable section

open scoped Topology

namespace Work.BoseFixB2.Recomb

open Submission.BoseGases MeasureTheory
open Work.BoseKinLoc

set_option autoImplicit false
set_option linter.unusedVariables false

/-! ## 1. The integral step -/

/-- **The scalar step for the Bochner integral.**  If four functions on a measurable set `s` are
integrable on `s` and satisfy the pointwise identity `F₁ − F₂ = t·(F₃ − F₄)` on `s`, then the
same identity holds for their integrals.  (Integrability of all four is what makes this a
statement about Bochner integrals rather than a formal identity.) -/
lemma setIntegral_sub_eq_smul_sub {α : Type*} [MeasurableSpace α] {μ : Measure α} {s : Set α}
    (hs : MeasurableSet s) {F1 F2 F3 F4 : α → ℝ} (t : ℝ)
    (h1 : IntegrableOn F1 s μ) (h2 : IntegrableOn F2 s μ)
    (h3 : IntegrableOn F3 s μ) (h4 : IntegrableOn F4 s μ)
    (hpt : ∀ x ∈ s, F1 x - F2 x = t * (F3 x - F4 x)) :
    (∫ x in s, F1 x ∂μ) - (∫ x in s, F2 x ∂μ)
      = t * ((∫ x in s, F3 x ∂μ) - (∫ x in s, F4 x ∂μ)) := by
  rw [← MeasureTheory.integral_sub h1 h2, ← MeasureTheory.integral_sub h3 h4,
    ← MeasureTheory.integral_const_mul t (fun x => F3 x - F4 x)]
  exact MeasureTheory.setIntegral_congr_fun hs hpt

/-! ## 2. The kinetic part, slot by slot -/

/-- **The box-restricted kinetic word is homogeneously polarised.**  Slot by slot: the fibre is
linear in the state, `fsT` is homogeneously polarised (`fsT_hpol`, taken here as the explicit
hypothesis `hfsT`), and the slot integrands are integrable on the box. -/
theorem kinFormB_hpol {n : ℕ} {ℓ d s εT b t : ℝ} (hℓ : 0 < ℓ)
    {Φ Ψ : Submission.BoseGases.X n → ℝ} (hΦ : ContDiff ℝ (⊤ : ℕ∞) Φ)
    (hΨ : ContDiff ℝ (⊤ : ℕ∞) Ψ)
    (hfsT : ∀ {f g : EuclideanSpace ℝ (Fin 3) → ℝ}, ContDiff ℝ (⊤ : ℕ∞) f →
      ContDiff ℝ (⊤ : ℕ∞) g →
      fsT ℓ d s εT b 0 (fun z => t * f z + g z) - fsT ℓ d s εT b 0 (fun z => t * f z - g z)
        = t * (fsT ℓ d s εT b 0 (fun z => f z + g z)
          - fsT ℓ d s εT b 0 (fun z => f z - g z))) :
    kinFormB n ℓ d s εT b (fun x => t * Φ x + Ψ x)
        - kinFormB n ℓ d s εT b (fun x => t * Φ x - Ψ x)
      = t * (kinFormB n ℓ d s εT b (fun x => Φ x + Ψ x)
        - kinFormB n ℓ d s εT b (fun x => Φ x - Ψ x)) := by
  have hms : MeasurableSet (Submission.BoseGases.abox n ℓ) :=
    Submission.BoseGases.abox_measurable n ℓ
  have htΦ : ContDiff ℝ (⊤ : ℕ∞) (fun x : Submission.BoseGases.X n => t * Φ x) := by
    simpa only [smul_eq_mul] using hΦ.const_smul t
  have hsum : ContDiff ℝ (⊤ : ℕ∞) (fun x : Submission.BoseGases.X n => t * Φ x + Ψ x) :=
    htΦ.add hΨ
  have hsub : ContDiff ℝ (⊤ : ℕ∞) (fun x : Submission.BoseGases.X n => t * Φ x - Ψ x) :=
    htΦ.sub hΨ
  have hsum1 : ContDiff ℝ (⊤ : ℕ∞) (fun x : Submission.BoseGases.X n => Φ x + Ψ x) :=
    hΦ.add hΨ
  have hsub1 : ContDiff ℝ (⊤ : ℕ∞) (fun x : Submission.BoseGases.X n => Φ x - Ψ x) :=
    hΦ.sub hΨ
  have hslot : ∀ i : Fin n,
      (∫ x in Submission.BoseGases.abox n ℓ,
          indU ℓ 0 (x i) * fsT ℓ d s εT b 0 (fibre n i (fun y => t * Φ y + Ψ y) x))
        - (∫ x in Submission.BoseGases.abox n ℓ,
          indU ℓ 0 (x i) * fsT ℓ d s εT b 0 (fibre n i (fun y => t * Φ y - Ψ y) x))
      = t * ((∫ x in Submission.BoseGases.abox n ℓ,
          indU ℓ 0 (x i) * fsT ℓ d s εT b 0 (fibre n i (fun y => Φ y + Ψ y) x))
        - (∫ x in Submission.BoseGases.abox n ℓ,
          indU ℓ 0 (x i) * fsT ℓ d s εT b 0 (fibre n i (fun y => Φ y - Ψ y) x))) := by
    intro i
    refine setIntegral_sub_eq_smul_sub hms t
      (Work.BoseFixB2.Sector.integrableOn_fsT_fibre_smooth (d := d) (s := s) (εT := εT)
        (b := b) hℓ i hsum)
      (Work.BoseFixB2.Sector.integrableOn_fsT_fibre_smooth (d := d) (s := s) (εT := εT)
        (b := b) hℓ i hsub)
      (Work.BoseFixB2.Sector.integrableOn_fsT_fibre_smooth (d := d) (s := s) (εT := εT)
        (b := b) hℓ i hsum1)
      (Work.BoseFixB2.Sector.integrableOn_fsT_fibre_smooth (d := d) (s := s) (εT := εT)
        (b := b) hℓ i hsub1) ?_
    intro x _
    have hfa : fibre n i (fun y => t * Φ y + Ψ y) x
        = fun z => t * (fibre n i Φ x) z + (fibre n i Ψ x) z := rfl
    have hfb : fibre n i (fun y => t * Φ y - Ψ y) x
        = fun z => t * (fibre n i Φ x) z - (fibre n i Ψ x) z := rfl
    have hfc : fibre n i (fun y => Φ y + Ψ y) x
        = fun z => (fibre n i Φ x) z + (fibre n i Ψ x) z := rfl
    have hfd : fibre n i (fun y => Φ y - Ψ y) x
        = fun z => (fibre n i Φ x) z - (fibre n i Ψ x) z := rfl
    have hT := hfsT (Work.BoseFixB2.Polar.contDiff_fibre hΦ i x)
      (Work.BoseFixB2.Polar.contDiff_fibre hΨ i x)
    rw [hfa, hfb, hfc, hfd, ← mul_sub, ← mul_sub, hT]
    ring
  have hsumS : (∑ i : Fin n, ∫ x in Submission.BoseGases.abox n ℓ,
        indU ℓ 0 (x i) * fsT ℓ d s εT b 0 (fibre n i (fun y => t * Φ y + Ψ y) x))
      - (∑ i : Fin n, ∫ x in Submission.BoseGases.abox n ℓ,
        indU ℓ 0 (x i) * fsT ℓ d s εT b 0 (fibre n i (fun y => t * Φ y - Ψ y) x))
      = t * ((∑ i : Fin n, ∫ x in Submission.BoseGases.abox n ℓ,
        indU ℓ 0 (x i) * fsT ℓ d s εT b 0 (fibre n i (fun y => Φ y + Ψ y) x))
        - (∑ i : Fin n, ∫ x in Submission.BoseGases.abox n ℓ,
        indU ℓ 0 (x i) * fsT ℓ d s εT b 0 (fibre n i (fun y => Φ y - Ψ y) x))) := by
    rw [← Finset.sum_sub_distrib, Finset.sum_congr rfl (fun i _ => hslot i),
      ← Finset.mul_sum, ← Finset.sum_sub_distrib]
  unfold kinFormB
  rw [← mul_sub, ← mul_sub, hsumS]
  ring

/-! ## 3. The potential part -/

/-- **The potential part of the box word is homogeneously polarised.**  The profile `potWordU`
does not depend on the state, so this is the pointwise identity
`(tΦ+Ψ)² − (tΦ−Ψ)² = t((Φ+Ψ)² − (Φ−Ψ)²)` integrated against it; integrability comes from
`hw` and the boundedness of the squares of the smooth states on the compact box. -/
theorem potIntB_hpol {n : ℕ} {v g : EuclideanSpace ℝ (Fin 3) → ℝ} {ℓ μ t : ℝ} (hℓ : 0 < ℓ)
    {Φ Ψ : Submission.BoseGases.X n → ℝ} (hΦ : ContDiff ℝ (⊤ : ℕ∞) Φ)
    (hΨ : ContDiff ℝ (⊤ : ℕ∞) Ψ)
    (hw : IntegrableOn (fun x : Submission.BoseGases.X n =>
      potWordU n v g ℓ μ 0 x) (Submission.BoseGases.abox n ℓ)) :
    (∫ x in Submission.BoseGases.abox n ℓ,
        (t * Φ x + Ψ x) ^ 2 * potWordU n v g ℓ μ 0 x)
      - (∫ x in Submission.BoseGases.abox n ℓ,
        (t * Φ x - Ψ x) ^ 2 * potWordU n v g ℓ μ 0 x)
      = t * ((∫ x in Submission.BoseGases.abox n ℓ,
          (Φ x + Ψ x) ^ 2 * potWordU n v g ℓ μ 0 x)
        - (∫ x in Submission.BoseGases.abox n ℓ,
          (Φ x - Ψ x) ^ 2 * potWordU n v g ℓ μ 0 x)) := by
  have hK : IsCompact (Submission.BoseGases.abox n ℓ) :=
    Submission.BoseGases.abox_compact n hℓ
  have hms : MeasurableSet (Submission.BoseGases.abox n ℓ) :=
    Submission.BoseGases.abox_measurable n ℓ
  have hI : ∀ Ξ : Submission.BoseGases.X n → ℝ, ContDiff ℝ (⊤ : ℕ∞) Ξ →
      IntegrableOn (fun x => (Ξ x) ^ 2 * potWordU n v g ℓ μ 0 x)
        (Submission.BoseGases.abox n ℓ) := by
    intro Ξ hΞ
    exact MeasureTheory.IntegrableOn.continuousOn_mul
      (g := fun x : Submission.BoseGases.X n => (Ξ x) ^ 2)
      (g' := fun x : Submission.BoseGases.X n => potWordU n v g ℓ μ 0 x)
      (hΞ.continuous.continuousOn.pow 2) hw hK
  have htΦ : ContDiff ℝ (⊤ : ℕ∞) (fun x : Submission.BoseGases.X n => t * Φ x) := by
    simpa only [smul_eq_mul] using hΦ.const_smul t
  refine setIntegral_sub_eq_smul_sub hms t (hI _ (htΦ.add hΨ)) (hI _ (htΦ.sub hΨ))
    (hI _ (hΦ.add hΨ)) (hI _ (hΦ.sub hΨ)) ?_
  intro x _
  ring

/-! ## 4. The box word -/

theorem boxFormB_polar_homog {n : ℕ} {v g : EuclideanSpace ℝ (Fin 3) → ℝ} {ℓ μ d s εT b t : ℝ} (hℓ : 0 < ℓ) (hd : 0 < d) (hs : 0 < s) (hεT : 0 < εT) (hb : 0 < b) {Φ Ψ : Submission.BoseGases.X n → ℝ} (hΦ : ContDiff ℝ (⊤ : ℕ∞) Φ) (hΨ : ContDiff ℝ (⊤ : ℕ∞) Ψ) (hw : MeasureTheory.IntegrableOn (fun x : Submission.BoseGases.X n => Work.BoseKinLoc.potWordU n v g ℓ μ 0 x) (Submission.BoseGases.abox n ℓ)) : Work.BoseKinLoc.boxFormB n v g ℓ μ d s εT b (fun x => t * Φ x + Ψ x) - Work.BoseKinLoc.boxFormB n v g ℓ μ d s εT b (fun x => t * Φ x - Ψ x) = t * (Work.BoseKinLoc.boxFormB n v g ℓ μ d s εT b (fun x => Φ x + Ψ x) - Work.BoseKinLoc.boxFormB n v g ℓ μ d s εT b (fun x => Φ x - Ψ x)) := by
  have hk := kinFormB_hpol (n := n) (ℓ := ℓ) (d := d) (s := s) (εT := εT) (b := b) (t := t)
    (Φ := Φ) (Ψ := Ψ) hℓ hΦ hΨ
    (fun {f g} hf hg => fsT_hpol (ℓ := ℓ) (d := d) (s := s) (εT := εT) (b := b) (t := t)
      hℓ hd hs hεT hb 0 hf hg)
  have hp := potIntB_hpol (n := n) (v := v) (g := g) (ℓ := ℓ) (μ := μ) (t := t) hℓ hΦ hΨ hw
  unfold boxFormB
  linear_combination hk + hp

end Work.BoseFixB2.Recomb
