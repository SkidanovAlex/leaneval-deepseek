import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseFixB2.Polar.fsT_parallelogram
import Submission.Work.BoseFixB2.Sector.integrableOn_fsT_fibre_smooth
import Submission.Work.BoseFixB2.Sector.jointProj_contDiff
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixB2.Polar.boxFormB_parallelogram` — FS's box word is a quadratic form

The box-restricted form `boxFormB n v g ℓ μ d s εT b` of the box Hamiltonian `H_Λ(μ)`
(FS `eq:Def_HB`, see `Work.BoseKinLoc.Defs`) satisfies the parallelogram identity

`boxFormB (Φ+Ψ) + boxFormB (Φ−Ψ) = 2·boxFormB Φ + 2·boxFormB Ψ`,

i.e. it is a *quadratic form* in the state.  This is the analytic content of §6
(`lem:LocMatrices`): together with `boxFormB_smul` (2-homogeneity) it makes the
polarisation `polB` (`Work.BoseFixB2.polB`) a symmetric bilinear form.

## The two parts

`boxFormB = kinFormB + ∫_{abox}(Φ x)²·potWordU x` (`Work.BoseKinLoc.boxFormB`).

* **Potential part** `∫_{x∈abox}(Φ x)²·potWordU x`: the potential profile is independent of
  the state, so the identity is the pointwise `(f+g)² + (f−g)² = 2f² + 2g²`.  Additivity of
  the Bochner integral requires the four integrands to be integrable: `potWordU` is integrable
  on the box by hypothesis, and `Φ²`, `Ψ²`, `(Φ±Ψ)²` are continuous hence bounded on the
  compact box `abox n ℓ`, so `IntegrableOn.mul_continuousOn` applies.
* **Kinetic part** `kinFormB = ℓ⁻³ Σᵢ ∫_{x∈abox} 1_{Λ}(xᵢ)·fsT(fibreᵢ Φ x)`: slot by slot,
  the fibre is linear in the state (`fibreᵢ (Φ+Ψ) = fibreᵢ Φ + fibreᵢ Ψ` pointwise), the
  one-body localised kinetic word `fsT` is a quadratic form
  (`Work.BoseFixB2.Polar.fsT_parallelogram`), and the slot-`i` integrand of a *globally
  smooth* state is integrable on the box
  (`Work.BoseFixB2.Sector.integrableOn_fsT_fibre_smooth` — this is exactly why the statement
  carries the smoothness hypotheses `hΦ`, `hΨ`, and not merely box-local information).

Both parts are instances of a single elementary lemma `integral_add_sub` below: for four
integrable functions on a measurable set satisfying `F₁ + F₂ = 2F₃ + 2F₄` pointwise, the
integrals satisfy the same relation.
-/

noncomputable section

open MeasureTheory
open scoped BigOperators

namespace Work.BoseFixB2.Polar

set_option autoImplicit false
set_option linter.unusedVariables false

/-! ## 1. The elementary integral step -/

/-- **The parallelogram step for the Bochner integral.**  For four functions on a measurable
set `s` with `F₁ + F₂ = 2F₃ + 2F₄` pointwise on `s`, all four integrable on `s`, the integrals
satisfy the same relation.  (Integrability of all four integrands is what makes this a
statement about Bochner integrals rather than a formal identity.) -/
lemma integral_add_sub {α : Type*} [MeasurableSpace α] {μ : Measure α} {s : Set α}
    (hs : MeasurableSet s) {F1 F2 F3 F4 : α → ℝ}
    (h1 : IntegrableOn F1 s μ) (h2 : IntegrableOn F2 s μ)
    (h3 : IntegrableOn F3 s μ) (h4 : IntegrableOn F4 s μ)
    (hpt : ∀ x ∈ s, F1 x + F2 x = 2 * F3 x + 2 * F4 x) :
    (∫ x in s, F1 x ∂μ) + (∫ x in s, F2 x ∂μ)
      = 2 * (∫ x in s, F3 x ∂μ) + 2 * (∫ x in s, F4 x ∂μ) := by
  calc (∫ x in s, F1 x ∂μ) + (∫ x in s, F2 x ∂μ)
      = ∫ x in s, (F1 x + F2 x) ∂μ := (MeasureTheory.integral_add h1 h2).symm
    _ = ∫ x in s, (2 * F3 x + 2 * F4 x) ∂μ :=
        MeasureTheory.setIntegral_congr_fun hs hpt
    _ = (∫ x in s, 2 * F3 x ∂μ) + (∫ x in s, 2 * F4 x ∂μ) :=
        MeasureTheory.integral_add (h3.const_mul 2) (h4.const_mul 2)
    _ = 2 * (∫ x in s, F3 x ∂μ) + 2 * (∫ x in s, F4 x ∂μ) := by
        rw [MeasureTheory.integral_const_mul (2 : ℝ) (fun x => F3 x),
          MeasureTheory.integral_const_mul (2 : ℝ) (fun x => F4 x)]

/-! ## 2. Smoothness of the slot fibres -/

/-- The slot-`i` fibre of a globally smooth `n`-body state is a smooth one-body state. -/
lemma contDiff_fibre {n : ℕ} {Φ : Submission.BoseGases.X n → ℝ}
    (hΦ : ContDiff ℝ (⊤ : ℕ∞) Φ) (i : Fin n) (x : Submission.BoseGases.X n) :
    ContDiff ℝ (⊤ : ℕ∞) (Work.BoseKinLoc.fibre n i Φ x) := by
  show ContDiff ℝ (⊤ : ℕ∞) (fun z : ℝ³ => Φ (Function.update x i z))
  exact hΦ.comp (contDiff_update (⊤ : ℕ∞) x i)

/-! ## 3. The kinetic part -/

/-- **The box-restricted kinetic word is a quadratic form.**  Slot by slot: the fibre is
linear in the state, `fsT` satisfies the parallelogram identity
(`Work.BoseFixB2.Polar.fsT_parallelogram`), and the slot integrands are integrable on the box
(`Work.BoseFixB2.Sector.integrableOn_fsT_fibre_smooth`). -/
lemma kinFormB_parallelogram {n : ℕ} {Φ Ψ : Submission.BoseGases.X n → ℝ}
    {ℓ d s εT b : ℝ} (hℓ : 0 < ℓ) (hd : 0 < d) (hs : 0 < s) (hεT : 0 < εT) (hb : 0 < b)
    (hΦ : ContDiff ℝ (⊤ : ℕ∞) Φ) (hΨ : ContDiff ℝ (⊤ : ℕ∞) Ψ) :
    Work.BoseKinLoc.kinFormB n ℓ d s εT b (fun x => Φ x + Ψ x)
      + Work.BoseKinLoc.kinFormB n ℓ d s εT b (fun x => Φ x - Ψ x)
      = 2 * Work.BoseKinLoc.kinFormB n ℓ d s εT b Φ
        + 2 * Work.BoseKinLoc.kinFormB n ℓ d s εT b Ψ := by
  have hms : MeasurableSet (Submission.BoseGases.abox n ℓ) :=
    Submission.BoseGases.abox_measurable n ℓ
  have hsum : ContDiff ℝ (⊤ : ℕ∞) (fun x : Submission.BoseGases.X n => Φ x + Ψ x) :=
    hΦ.add hΨ
  have hsub : ContDiff ℝ (⊤ : ℕ∞) (fun x : Submission.BoseGases.X n => Φ x - Ψ x) :=
    hΦ.sub hΨ
  -- slot by slot
  have hA : ∀ i : Fin n,
      (∫ x in Submission.BoseGases.abox n ℓ,
          Work.BoseKinLoc.indU ℓ 0 (x i) * Work.BoseKinLoc.fsT ℓ d s εT b 0
            (Work.BoseKinLoc.fibre n i (fun y => Φ y + Ψ y) x))
        + (∫ x in Submission.BoseGases.abox n ℓ,
          Work.BoseKinLoc.indU ℓ 0 (x i) * Work.BoseKinLoc.fsT ℓ d s εT b 0
            (Work.BoseKinLoc.fibre n i (fun y => Φ y - Ψ y) x))
      = 2 * (∫ x in Submission.BoseGases.abox n ℓ,
          Work.BoseKinLoc.indU ℓ 0 (x i) * Work.BoseKinLoc.fsT ℓ d s εT b 0
            (Work.BoseKinLoc.fibre n i Φ x))
        + 2 * (∫ x in Submission.BoseGases.abox n ℓ,
          Work.BoseKinLoc.indU ℓ 0 (x i) * Work.BoseKinLoc.fsT ℓ d s εT b 0
            (Work.BoseKinLoc.fibre n i Ψ x)) := by
    intro i
    refine integral_add_sub hms
      (Work.BoseFixB2.Sector.integrableOn_fsT_fibre_smooth (d := d) (s := s) (εT := εT)
        (b := b) hℓ i hsum)
      (Work.BoseFixB2.Sector.integrableOn_fsT_fibre_smooth (d := d) (s := s) (εT := εT)
        (b := b) hℓ i hsub)
      (Work.BoseFixB2.Sector.integrableOn_fsT_fibre_smooth (d := d) (s := s) (εT := εT)
        (b := b) hℓ i hΦ)
      (Work.BoseFixB2.Sector.integrableOn_fsT_fibre_smooth (d := d) (s := s) (εT := εT)
        (b := b) hℓ i hΨ) ?_
    intro x _
    have hfa : Work.BoseKinLoc.fibre n i (fun y => Φ y + Ψ y) x
        = fun z => Work.BoseKinLoc.fibre n i Φ x z
            + Work.BoseKinLoc.fibre n i Ψ x z := rfl
    have hfs : Work.BoseKinLoc.fibre n i (fun y => Φ y - Ψ y) x
        = fun z => Work.BoseKinLoc.fibre n i Φ x z
            - Work.BoseKinLoc.fibre n i Ψ x z := rfl
    rw [hfa, hfs, ← mul_add,
      fsT_parallelogram (ℓ := ℓ) (d := d) (s := s) (εT := εT) (b := b)
        hℓ hd hs hεT hb 0 (contDiff_fibre hΦ i x) (contDiff_fibre hΨ i x)]
    ring
  have hsumA : (∑ i : Fin n, ∫ x in Submission.BoseGases.abox n ℓ,
        Work.BoseKinLoc.indU ℓ 0 (x i) * Work.BoseKinLoc.fsT ℓ d s εT b 0
          (Work.BoseKinLoc.fibre n i (fun y => Φ y + Ψ y) x))
      + (∑ i : Fin n, ∫ x in Submission.BoseGases.abox n ℓ,
        Work.BoseKinLoc.indU ℓ 0 (x i) * Work.BoseKinLoc.fsT ℓ d s εT b 0
          (Work.BoseKinLoc.fibre n i (fun y => Φ y - Ψ y) x))
      = 2 * (∑ i : Fin n, ∫ x in Submission.BoseGases.abox n ℓ,
        Work.BoseKinLoc.indU ℓ 0 (x i) * Work.BoseKinLoc.fsT ℓ d s εT b 0
          (Work.BoseKinLoc.fibre n i Φ x))
        + 2 * (∑ i : Fin n, ∫ x in Submission.BoseGases.abox n ℓ,
        Work.BoseKinLoc.indU ℓ 0 (x i) * Work.BoseKinLoc.fsT ℓ d s εT b 0
          (Work.BoseKinLoc.fibre n i Ψ x)) := by
    rw [← Finset.sum_add_distrib]
    rw [Finset.sum_congr rfl (fun i _ => hA i)]
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
  unfold Work.BoseKinLoc.kinFormB
  rw [← mul_add, hsumA]
  ring

/-! ## 4. The potential part -/

/-- **The box-restricted potential part is a quadratic form.**  The potential profile is
independent of the state, so this is the pointwise identity `(f+g)² + (f−g)² = 2f² + 2g²`
together with integral additivity; integrability comes from the hypothesis on `potWordU` and
the boundedness of the squares of the smooth state on the compact box. -/
lemma potIntB_parallelogram {n : ℕ} {v g : ℝ³ → ℝ} {ℓ μ : ℝ}
    {Φ Ψ : Submission.BoseGases.X n → ℝ} (hℓ : 0 < ℓ)
    (hΦ : ContDiff ℝ (⊤ : ℕ∞) Φ) (hΨ : ContDiff ℝ (⊤ : ℕ∞) Ψ)
    (hw : IntegrableOn (fun x : Submission.BoseGases.X n =>
        Work.BoseKinLoc.potWordU n v g ℓ μ 0 x) (Submission.BoseGases.abox n ℓ)) :
    (∫ x in Submission.BoseGases.abox n ℓ,
        (Φ x + Ψ x) ^ 2 * Work.BoseKinLoc.potWordU n v g ℓ μ 0 x)
      + (∫ x in Submission.BoseGases.abox n ℓ,
        (Φ x - Ψ x) ^ 2 * Work.BoseKinLoc.potWordU n v g ℓ μ 0 x)
      = 2 * (∫ x in Submission.BoseGases.abox n ℓ,
          (Φ x) ^ 2 * Work.BoseKinLoc.potWordU n v g ℓ μ 0 x)
        + 2 * (∫ x in Submission.BoseGases.abox n ℓ,
          (Ψ x) ^ 2 * Work.BoseKinLoc.potWordU n v g ℓ μ 0 x) := by
  have hK : IsCompact (Submission.BoseGases.abox n ℓ) :=
    Submission.BoseGases.abox_compact n hℓ
  have hms : MeasurableSet (Submission.BoseGases.abox n ℓ) :=
    Submission.BoseGases.abox_measurable n ℓ
  have hsum : ContDiff ℝ (⊤ : ℕ∞) (fun x : Submission.BoseGases.X n => Φ x + Ψ x) :=
    hΦ.add hΨ
  have hsub : ContDiff ℝ (⊤ : ℕ∞) (fun x : Submission.BoseGases.X n => Φ x - Ψ x) :=
    hΦ.sub hΨ
  -- integrability of the four integrands
  have hI : ∀ Ξ : Submission.BoseGases.X n → ℝ, ContDiff ℝ (⊤ : ℕ∞) Ξ →
      IntegrableOn (fun x => (Ξ x) ^ 2 * Work.BoseKinLoc.potWordU n v g ℓ μ 0 x)
        (Submission.BoseGases.abox n ℓ) := by
    intro Ξ hΞ
    exact MeasureTheory.IntegrableOn.continuousOn_mul
      (g := fun x : Submission.BoseGases.X n => (Ξ x) ^ 2)
      (g' := fun x : Submission.BoseGases.X n => Work.BoseKinLoc.potWordU n v g ℓ μ 0 x)
      (hΞ.continuous.continuousOn.pow 2) hw hK
  refine integral_add_sub hms (hI _ hsum) (hI _ hsub) (hI _ hΦ) (hI _ hΨ) ?_
  intro x _
  ring

/-! ## 5. The box word -/

theorem boxFormB_parallelogram {v g : EuclideanSpace ℝ (Fin 3) → ℝ} {ℓ μ d s εT b : ℝ} (hℓ : 0 < ℓ) (hd : 0 < d) (hs : 0 < s) (hεT : 0 < εT) (hb : 0 < b) {n : ℕ} {Φ Ψ : Submission.BoseGases.X n → ℝ} (hΦ : ContDiff ℝ (⊤ : ℕ∞) Φ) (hΨ : ContDiff ℝ (⊤ : ℕ∞) Ψ) (hw : MeasureTheory.IntegrableOn (fun x : Submission.BoseGases.X n => Work.BoseKinLoc.potWordU n v g ℓ μ 0 x) (Submission.BoseGases.abox n ℓ)) : Work.BoseKinLoc.boxFormB n v g ℓ μ d s εT b (fun x => Φ x + Ψ x) + Work.BoseKinLoc.boxFormB n v g ℓ μ d s εT b (fun x => Φ x - Ψ x) = 2 * Work.BoseKinLoc.boxFormB n v g ℓ μ d s εT b Φ + 2 * Work.BoseKinLoc.boxFormB n v g ℓ μ d s εT b Ψ := by
  have hk := kinFormB_parallelogram (n := n) (Φ := Φ) (Ψ := Ψ) hℓ hd hs hεT hb hΦ hΨ
  have hp := potIntB_parallelogram (n := n) (v := v) (g := g) (ℓ := ℓ) (μ := μ)
    hℓ hΦ hΨ hw
  unfold Work.BoseKinLoc.boxFormB
  linarith [hk, hp]

end Work.BoseFixB2.Polar
