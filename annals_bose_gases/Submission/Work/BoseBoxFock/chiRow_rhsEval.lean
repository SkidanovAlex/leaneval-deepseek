import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Q0Value
import Submission.Work.BoseBoxFock.chiRow_diagZero
import Submission.Work.BoseBoxFock.chiRow_gbar_eq_c
import Submission.Work.BoseBoxFock.chiRow_slotWeightMean
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.chiRow_rhsEval` — the constant-shift evaluation of the χ-row

The χ-row of the `n₀`-sandwich (`chiRow_slotIdentity`) carries a slot-`i`-only weight
`g(xᵢ)`.  Only the *mean-free* part of the weight survives: with `g = h + c` and
`∫_{acube ℓ} h = 0`, the row with weight `g` equals the row with weight `h` **exactly on
the diagonal-free part of the double sum**,

    2 Σ_{i≠j} ∫_{abox} (PᵢΦ)(x)·g(xᵢ)·(QᵢPⱼΦ)(x)
      = 2 Σ_{i≠j} ∫_{abox} (PᵢΦ)(x)·h(xᵢ)·(PⱼΦ)(x) .

The content is the per-pair evaluation (`chiRow_offDiag` below), which uses only

* `Qᵢ = 1 − Pᵢ`, the self-adjointness of `Pᵢ` over the box (`aP_sym_box`) and
* the same-slot weight pull-out `Pᵢ(Aᵢ·w(·ᵢ)) = Aᵢ·⟨w⟩` (`chiRow_slotWeightMean`),

the constant part cancelling because `⟨g⟩ = c` (`chiRow_gbar_eq_c`) while `g − c = h`.
The diagonal terms `i = j` of the unrestricted double sum on the right vanish separately
(`chiRow_diagZero`), since `(PᵢΦ)²` is constant in slot `i`.
-/

noncomputable section

open MeasureTheory

namespace Work.BoseBoxFock

open Submission.BoseGases

set_option autoImplicit false

/-- **Per-pair (off-diagonal) evaluation of the χ-row slot weight.**  For `i ≠ j`,

`∫_{abox} (PᵢΦ)·g(xᵢ)·(QᵢPⱼΦ) = ∫_{abox} (PᵢΦ)·h(xᵢ)·(PⱼΦ)`,

whenever `g = h + c` with `h` of zero cube mean.  (The index hypothesis is not used in
the proof — for `i = j` both sides also vanish — but it documents the intended use.) -/
lemma chiRow_offDiag {n : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ)
    {Φ : Submission.BoseGases.X n → ℝ} (hΦc : Continuous Φ)
    {g : EuclideanSpace ℝ (Fin 3) → ℝ} (hgc : Continuous g)
    {h : EuclideanSpace ℝ (Fin 3) → ℝ} (hhc : Continuous h)
    (hmean : (∫ z in Submission.BoseGases.acube ℓ, h z) = 0)
    {c : ℝ} (hg : ∀ z, g z = h z + c) {i j : Fin n} :
    (∫ x in Submission.BoseGases.abox n ℓ,
        (Submission.BoseGases.aP ℓ i Φ x) * g (x i) *
          (Submission.BoseGases.aQ ℓ i
            (fun y : Submission.BoseGases.X n => Submission.BoseGases.aP ℓ j Φ y) x))
      = ∫ x in Submission.BoseGases.abox n ℓ,
          (Submission.BoseGases.aP ℓ i Φ x) * h (x i) * (Submission.BoseGases.aP ℓ j Φ x) := by
  set gbar : ℝ := (1 / ℓ ^ 3) * ∫ z in Submission.BoseGases.acube ℓ, g z with hgbar
  have hgbarc : gbar = c := by
    rw [hgbar]
    exact chiRow_gbar_eq_c hℓ hhc hmean hg
  have hW : ∀ x : Submission.BoseGases.X n,
      Submission.BoseGases.aP ℓ i (fun z : Submission.BoseGases.X n =>
        Submission.BoseGases.aP ℓ i Φ z * g (z i)) x
        = Submission.BoseGases.aP ℓ i Φ x * gbar := by
    intro x
    rw [hgbar]
    exact chiRow_slotWeightMean hℓ i hΦc g x
  have hAc : Continuous (fun x : Submission.BoseGases.X n => Submission.BoseGases.aP ℓ i Φ x) :=
    aP_continuous hℓ i hΦc
  have hBc : Continuous (fun x : Submission.BoseGases.X n => Submission.BoseGases.aP ℓ j Φ x) :=
    aP_continuous hℓ j hΦc
  have hPc : Continuous (fun x : Submission.BoseGases.X n =>
      Submission.BoseGases.aP ℓ i
        (fun y : Submission.BoseGases.X n => Submission.BoseGases.aP ℓ j Φ y) x) :=
    aP_continuous hℓ i hBc
  have hgc2 : Continuous (fun x : Submission.BoseGases.X n => g (x i)) :=
    hgc.comp (continuous_apply i)
  have hFc : Continuous (fun x : Submission.BoseGases.X n =>
      Submission.BoseGases.aP ℓ i Φ x * g (x i)) :=
    hAc.mul hgc2
  have hAdj := aP_sym_box hℓ i
    (Φ := fun z : Submission.BoseGases.X n => Submission.BoseGases.aP ℓ i Φ z * g (z i))
    (Ψ := fun y : Submission.BoseGases.X n => Submission.BoseGases.aP ℓ j Φ y) hFc hBc
  have hPint : (∫ x in Submission.BoseGases.abox n ℓ,
        (fun z : Submission.BoseGases.X n => Submission.BoseGases.aP ℓ i Φ z * g (z i)) x *
          (Submission.BoseGases.aP ℓ i
            (fun y : Submission.BoseGases.X n => Submission.BoseGases.aP ℓ j Φ y) x))
      = ∫ x in Submission.BoseGases.abox n ℓ,
          (Submission.BoseGases.aP ℓ i Φ x * gbar) * (Submission.BoseGases.aP ℓ j Φ x) := by
    rw [← hAdj]
    apply integral_congr_ae
    filter_upwards with x
    rw [hW x]
  have hI0 : IntegrableOn (fun x : Submission.BoseGases.X n =>
      Submission.BoseGases.aP ℓ i Φ x * g (x i) * (Submission.BoseGases.aP ℓ j Φ x))
      (Submission.BoseGases.abox n ℓ) volume :=
    integrableOn_abox_of_continuous hℓ (hFc.mul hBc)
  have hI1 : IntegrableOn (fun x : Submission.BoseGases.X n =>
      (fun z : Submission.BoseGases.X n => Submission.BoseGases.aP ℓ i Φ z * g (z i)) x *
        (Submission.BoseGases.aP ℓ j Φ x)) (Submission.BoseGases.abox n ℓ) volume :=
    integrableOn_abox_of_continuous hℓ (hFc.mul hBc)
  have hI2 : IntegrableOn (fun x : Submission.BoseGases.X n =>
      (fun z : Submission.BoseGases.X n => Submission.BoseGases.aP ℓ i Φ z * g (z i)) x *
        (Submission.BoseGases.aP ℓ i
          (fun y : Submission.BoseGases.X n => Submission.BoseGases.aP ℓ j Φ y) x))
      (Submission.BoseGases.abox n ℓ) volume :=
    integrableOn_abox_of_continuous hℓ (hFc.mul hPc)
  have hI3 : IntegrableOn (fun x : Submission.BoseGases.X n =>
      (Submission.BoseGases.aP ℓ i Φ x * c) * (Submission.BoseGases.aP ℓ j Φ x))
      (Submission.BoseGases.abox n ℓ) volume :=
    integrableOn_abox_of_continuous hℓ ((hAc.mul continuous_const).mul hBc)
  have hQ : ∀ x : Submission.BoseGases.X n,
      Submission.BoseGases.aP ℓ i Φ x * g (x i) *
        (Submission.BoseGases.aQ ℓ i
          (fun y : Submission.BoseGases.X n => Submission.BoseGases.aP ℓ j Φ y) x)
      = (fun z : Submission.BoseGases.X n =>
            Submission.BoseGases.aP ℓ i Φ z * g (z i) * (Submission.BoseGases.aP ℓ j Φ z)) x
        - (fun z : Submission.BoseGases.X n =>
            Submission.BoseGases.aP ℓ i Φ z * g (z i) *
              (Submission.BoseGases.aP ℓ i
                (fun y : Submission.BoseGases.X n => Submission.BoseGases.aP ℓ j Φ y) z)) x := by
    intro x
    unfold Submission.BoseGases.aQ
    ring
  calc (∫ x in Submission.BoseGases.abox n ℓ, Submission.BoseGases.aP ℓ i Φ x * g (x i) *
          (Submission.BoseGases.aQ ℓ i
            (fun y : Submission.BoseGases.X n => Submission.BoseGases.aP ℓ j Φ y) x))
      = ∫ x in Submission.BoseGases.abox n ℓ,
          ((fun z : Submission.BoseGases.X n =>
              Submission.BoseGases.aP ℓ i Φ z * g (z i) * (Submission.BoseGases.aP ℓ j Φ z)) x
            - (fun z : Submission.BoseGases.X n =>
              Submission.BoseGases.aP ℓ i Φ z * g (z i) *
                (Submission.BoseGases.aP ℓ i
                  (fun y : Submission.BoseGases.X n => Submission.BoseGases.aP ℓ j Φ y) z)) x) := by
          apply integral_congr_ae
          filter_upwards with x
          exact hQ x
    _ = (∫ x in Submission.BoseGases.abox n ℓ, (fun z : Submission.BoseGases.X n =>
            Submission.BoseGases.aP ℓ i Φ z * g (z i) * (Submission.BoseGases.aP ℓ j Φ z)) x)
        - (∫ x in Submission.BoseGases.abox n ℓ, (fun z : Submission.BoseGases.X n =>
            Submission.BoseGases.aP ℓ i Φ z * g (z i) *
              (Submission.BoseGases.aP ℓ i
                (fun y : Submission.BoseGases.X n => Submission.BoseGases.aP ℓ j Φ y) z)) x) :=
        MeasureTheory.integral_sub hI1 hI2
    _ = (∫ x in Submission.BoseGases.abox n ℓ,
            Submission.BoseGases.aP ℓ i Φ x * g (x i) * (Submission.BoseGases.aP ℓ j Φ x))
        - (∫ x in Submission.BoseGases.abox n ℓ,
            (Submission.BoseGases.aP ℓ i Φ x * gbar) * (Submission.BoseGases.aP ℓ j Φ x)) := by
        rw [hPint]
    _ = (∫ x in Submission.BoseGases.abox n ℓ,
            Submission.BoseGases.aP ℓ i Φ x * g (x i) * (Submission.BoseGases.aP ℓ j Φ x))
        - (∫ x in Submission.BoseGases.abox n ℓ,
            (Submission.BoseGases.aP ℓ i Φ x * c) * (Submission.BoseGases.aP ℓ j Φ x)) := by
        rw [hgbarc]
    _ = ∫ x in Submission.BoseGases.abox n ℓ,
          ((Submission.BoseGases.aP ℓ i Φ x * g (x i) * (Submission.BoseGases.aP ℓ j Φ x))
            - ((Submission.BoseGases.aP ℓ i Φ x * c) * (Submission.BoseGases.aP ℓ j Φ x))) :=
        (MeasureTheory.integral_sub hI0 hI3).symm
    _ = ∫ x in Submission.BoseGases.abox n ℓ,
          Submission.BoseGases.aP ℓ i Φ x * h (x i) * (Submission.BoseGases.aP ℓ j Φ x) := by
        apply integral_congr_ae
        filter_upwards with x
        rw [hg (x i)]
        ring

theorem chiRow_rhsEval {n : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ)
    {Φ : Submission.BoseGases.X n → ℝ} (hΦc : Continuous Φ)
    {g : EuclideanSpace ℝ (Fin 3) → ℝ} (hgc : Continuous g)
    {h : EuclideanSpace ℝ (Fin 3) → ℝ} (hhc : Continuous h)
    (hmean : (∫ z in Submission.BoseGases.acube ℓ, h z) = 0)
    {c : ℝ} (hg : ∀ z, g z = h z + c) :
    2 * ∑ i : Fin n, ∑ j : Fin n, (if i = j then 0 else
        (∫ x in Submission.BoseGases.abox n ℓ,
          (Submission.BoseGases.aP ℓ i Φ x) * g (x i) *
            (Submission.BoseGases.aQ ℓ i
              (fun y : Submission.BoseGases.X n => Submission.BoseGases.aP ℓ j Φ y) x)))
      = 2 * ∑ i : Fin n, ∑ j : Fin n,
          (∫ x in Submission.BoseGases.abox n ℓ,
            (Submission.BoseGases.aP ℓ i Φ x) * h (x i) * (Submission.BoseGases.aP ℓ j Φ x)) := by
  congr 1
  refine Finset.sum_congr rfl (fun i _ => ?_)
  calc ∑ j : Fin n, (if i = j then 0 else
        (∫ x in Submission.BoseGases.abox n ℓ,
          (Submission.BoseGases.aP ℓ i Φ x) * g (x i) *
            (Submission.BoseGases.aQ ℓ i
              (fun y : Submission.BoseGases.X n => Submission.BoseGases.aP ℓ j Φ y) x)))
      = ∑ j : Fin n, (if i = j then 0 else
          (∫ x in Submission.BoseGases.abox n ℓ,
            (Submission.BoseGases.aP ℓ i Φ x) * h (x i) * (Submission.BoseGases.aP ℓ j Φ x))) := by
        apply Finset.sum_congr rfl
        intro j _
        by_cases hij : i = j
        · simp [hij]
        · rw [if_neg hij, if_neg hij]
          exact chiRow_offDiag hℓ hΦc hgc hhc hmean hg
    _ = ∑ j : Fin n, (∫ x in Submission.BoseGases.abox n ℓ,
            (Submission.BoseGases.aP ℓ i Φ x) * h (x i) * (Submission.BoseGases.aP ℓ j Φ x)) := by
        apply Finset.sum_congr rfl
        intro j _
        by_cases hij : i = j
        · rw [if_pos hij, hij, chiRow_diagZero hℓ j hΦc hhc hmean]
        · rw [if_neg hij]

end Work.BoseBoxFock
