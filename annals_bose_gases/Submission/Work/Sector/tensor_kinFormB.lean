import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Submission.Work.BoseKinLoc.Sector.fsT_box_invariant
import Submission.Work.BoseKinLoc.Word.kinForm_prod
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.Sector.tensor_kinFormB` — the box kinetic word on a product state

The box-restricted `N`-body kinetic word `Work.BoseKinLoc.kinFormB` is FS `eq:Def_HB`'s
`Σᵢ 𝒯_u^{(i)}` with the configuration integral taken over the box `abox N ℓ` rather than
all of `(ℝ³)ᴺ`,

    `kinFormB N ℓ d s εT b Φ = ℓ⁻³ Σᵢ ∫_{x ∈ abox N ℓ} 1_{Λ(0)}(xᵢ) · 𝒯₀(fibre i Φ x)`,

where the slot-`i` fibre is `fibre N i Φ x = z ↦ Φ(x with xᵢ = z)`.

For the **product state** `Φ x = ∏ i, ψ (x i)` the fibre is the scalar multiple
`(∏_{j≠i} ψ(x j)) · ψ` of `ψ`, the one-body word `fsT` is a quadratic form
(`fsT_const_mul'` below), and the slot integral therefore factorises:

* `indU ℓ 0 = 1_{acube ℓ}` and `abox N ℓ = (acube ℓ)ᴺ`, so the restricted Fubini identity
  `integral_abox_indU_erase` evaluates each slot integral to

      `ℓ³ · (∫_{acube ℓ} ψ²)^{N-1} · 𝒯₀ ψ`;

* the normalisation `ℓ⁻³` of `kinFormB` cancels the box volume `ℓ³`, and summing the `N`
  identical slots gives the stated

      `kinFormB N ℓ d s εT b (∏ ψ) = N · 𝒯₀ψ · (∫_{acube ℓ} ψ²)^{N-1}`.

The one-body word `fsT` is only a quadratic *form*, so `fsT (c·ψ) = c² fsT ψ` is the
non-trivial analytic input on the one-body side; it needs no smoothness, support or
integrability hypothesis on `ψ` (`Work.BoseKinLoc.Word.fsT_const_mul` carries the
smoothness/compact-support hypotheses only because its consumers state the word on such
states — the four summands of FS `eq:DefT` are each `2`-homogeneous unconditionally).
-/

noncomputable section

open MeasureTheory
open scoped Real BigOperators

namespace Work.Sector

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

/-! ## 1. The one-body word is `2`-homogeneous (no smoothness hypothesis)

`Work.BoseKinLoc.Word.fsT_const_mul` records `fsT (c·ψ) = c² fsT ψ` but asks for
`ContDiff ℝ ⊤ ψ` and `HasCompactSupport ψ`.  Neither hypothesis is used by any of the four
summands: `neuFrac` is an infimum over smooth compactly supported *trials*,
`gapBare`/`momForm`/`bsOneBody` are built from unconditional Bochner-integral identities.
We restate the homogeneity without them, since the product states of the target carry only
smoothness. -/

theorem fsT_const_mul' {ℓ d s εT b c : ℝ} (u : ℝ³) (ψ : ℝ³ → ℝ) :
    Work.BoseKinLoc.fsT ℓ d s εT b u (fun z => c * ψ z)
      = c ^ 2 * Work.BoseKinLoc.fsT ℓ d s εT b u ψ := by
  have ha2 : 0 ≤ (d * ℓ) ^ (-2 : ℤ) := by
    rw [zpow_neg]
    exact inv_nonneg.mpr (sq_nonneg _)
  have hQ : Work.BoseKinLoc.Qfree ℓ u (fun z => c * ψ z)
      = fun z => c * Work.BoseKinLoc.Qfree ℓ u ψ z :=
    Work.BoseKinLoc.Word.FsTAux.Qfree_const_mul ℓ u c ψ
  have hgap : Work.BoseKinLoc.gapWord ℓ b u (fun z => c * ψ z)
      = c ^ 2 * Work.BoseKinLoc.gapWord ℓ b u ψ := by
    unfold Work.BoseKinLoc.gapWord
    rw [Work.BoseKinLoc.Word.FsTAux.gapBare_const_mul]
    ring
  have hmom : Work.BoseKinLoc.momWord ℓ d εT b u (fun z => c * ψ z)
      = c ^ 2 * Work.BoseKinLoc.momWord ℓ d εT b u ψ := by
    unfold Work.BoseKinLoc.momWord
    rw [Work.BoseKinLoc.Word.momForm_const_mul u c ψ]
    ring
  have hmain : Work.BoseKinLoc.mainWord ℓ d s εT u (fun z => c * ψ z)
      = c ^ 2 * Work.BoseKinLoc.mainWord ℓ d s εT u ψ := by
    unfold Work.BoseKinLoc.mainWord
    rw [Work.BoseKinLoc.Word.bsOneBody_const_mul
          (Submission.BoseGases.fsKinCoeff ((2 * (s * ℓ))⁻¹)) u c ψ,
        Work.BoseKinLoc.Word.bsOneBody_const_mul
          (Submission.BoseGases.fsKinCoeff ((2 * (d * s * ℓ))⁻¹)) u c ψ]
    ring
  have hneu : Work.BoseKinLoc.neuWord ℓ d εT u (fun z => c * ψ z)
      = c ^ 2 * Work.BoseKinLoc.neuWord ℓ d εT u ψ := by
    unfold Work.BoseKinLoc.neuWord
    rw [hQ, Work.BoseKinLoc.NeuFrac.neuFrac_const_mul ha2 u (Work.BoseKinLoc.Qfree ℓ u ψ)]
    ring
  rw [Work.BoseKinLoc.fsT_eq_sum, Work.BoseKinLoc.fsT_eq_sum, hneu, hgap, hmom, hmain]
  ring

/-! ## 2. The centred box is the box of the window at `u = 0` -/

/-- The moving box `Λ(u) = ℓu + [−ℓ/2,ℓ/2]³` at `u = 0` is the centred cube `acube ℓ`. -/
lemma lamBox_zero (ℓ : ℝ) : Work.BoseKinLoc.lamBox ℓ 0 = Submission.BoseGases.acube ℓ := by
  ext x
  simp [Work.BoseKinLoc.lamBox, Work.BSKinetic.bsBox]

/-- The window-indicator `θ_0 = indU ℓ 0` is the indicator of the centred cube. -/
lemma indU_zero_eq_indicator (ℓ : ℝ) :
    Work.BoseKinLoc.indU ℓ 0 = (Submission.BoseGases.acube ℓ).indicator (fun _ => (1 : ℝ)) := by
  rw [Work.BoseKinLoc.indU, lamBox_zero]

/-- The indicator of the centred cube integrates to `ℓ³` against the *centred-cube
restricted* volume: on `acube ℓ` the indicator is `1`, and `acube ℓ` has volume `ℓ³`. -/
lemma integral_indU_zero_restrict_acube {ℓ : ℝ} (hℓ : 0 < ℓ) :
    (∫ x : ℝ³, Work.BoseKinLoc.indU ℓ 0 x
        ∂((volume : Measure ℝ³).restrict (Submission.BoseGases.acube ℓ))) = ℓ ^ 3 := by
  rw [indU_zero_eq_indicator ℓ]
  rw [MeasureTheory.setIntegral_congr_fun (Submission.BoseGases.acube_measurable ℓ)
        (fun x hx => Set.indicator_of_mem hx (fun _ => (1 : ℝ)))]
  rw [MeasureTheory.setIntegral_const]
  rw [MeasureTheory.Measure.real_def, Submission.BoseGases.acube_volume ℓ hℓ.le,
      ENNReal.toReal_ofReal (pow_nonneg hℓ.le 3)]
  simp

/-! ## 3. The restricted erase-slot Fubini identity

This is the box-restricted analogue of `Work.BoseKinLoc.Word.integral_prod_erase_mul_indU`:
the configuration integral runs over `abox n ℓ`, i.e. against the measure
`Measure.pi (fun _ => volume.restrict (acube ℓ))`, and only the `i`-th slot carries the
window indicator.  The remaining `n - 1` slots contribute `∫_{acube ℓ} f` each and the
`i`-th slot contributes the normalisation `∫ indU ℓ 0 = ℓ³` of the box (`acube ℓ` being
exactly the support of `indU ℓ 0`). -/

theorem integral_abox_indU_erase {n : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ)
    (i : Fin n) (f : ℝ³ → ℝ) :
    (∫ x in Submission.BoseGases.abox n ℓ,
        Work.BoseKinLoc.indU ℓ 0 (x i) * (∏ j ∈ Finset.univ.erase i, f (x j)))
      = ℓ ^ 3 * (∫ z in Submission.BoseGases.acube ℓ, f z) ^ (n - 1) := by
  -- the integrand is a product over all slots, the `i`-th carrying `indU`
  set g : Fin n → ℝ³ → ℝ :=
    Function.update (fun _ : Fin n => f) i (Work.BoseKinLoc.indU ℓ 0) with hg
  have hpoint : ∀ x : Submission.BoseGases.X n,
      (∏ j : Fin n, g j (x j))
        = Work.BoseKinLoc.indU ℓ 0 (x i) * (∏ j ∈ Finset.univ.erase i, f (x j)) := by
    intro x
    rw [← Finset.prod_erase_mul Finset.univ (fun j : Fin n => g j (x j)) (Finset.mem_univ i)]
    have h1 : (∏ j ∈ Finset.univ.erase i, g j (x j))
        = ∏ j ∈ Finset.univ.erase i, f (x j) := by
      refine Finset.prod_congr rfl (fun j hj => ?_)
      rw [hg, Function.update_of_ne (Finset.mem_erase.mp hj).1]
    have h2 : g i (x i) = Work.BoseKinLoc.indU ℓ 0 (x i) := by
      rw [hg, Function.update_self]
    rw [h1, h2, mul_comm]
  have hfun : (fun x : Submission.BoseGases.X n =>
        Work.BoseKinLoc.indU ℓ 0 (x i) * (∏ j ∈ Finset.univ.erase i, f (x j)))
      = fun x : Submission.BoseGases.X n => ∏ j : Fin n, g j (x j) :=
    funext (fun x => (hpoint x).symm)
  rw [hfun, Submission.BoseGases.restrict_abox_eq_pi n ℓ,
      MeasureTheory.integral_fintype_prod_eq_prod g]
  -- the factor of each slot
  have hfac : ∀ j : Fin n,
      (∫ x : ℝ³, g j x ∂((volume : Measure ℝ³).restrict (Submission.BoseGases.acube ℓ)))
        = if j = i then ℓ ^ 3 else (∫ z in Submission.BoseGases.acube ℓ, f z) := by
    intro j
    by_cases hj : j = i
    · rw [hj, if_pos rfl, hg, Function.update_self]
      exact integral_indU_zero_restrict_acube hℓ
    · rw [if_neg hj, hg, Function.update_of_ne hj]
  rw [Finset.prod_congr rfl (fun j _ => hfac j)]
  -- one `ℓ³` for the `i`-th slot, `∫ f` for each of the others
  have hprodeval : (∏ j : Fin n,
        (if j = i then ℓ ^ 3 else (∫ z in Submission.BoseGases.acube ℓ, f z)))
      = (∫ z in Submission.BoseGases.acube ℓ, f z) ^ (n - 1) * ℓ ^ 3 := by
    rw [← Finset.prod_erase_mul Finset.univ
          (fun j : Fin n => if j = i then ℓ ^ 3 else (∫ z in Submission.BoseGases.acube ℓ, f z))
          (Finset.mem_univ i)]
    rw [if_pos rfl,
        Finset.prod_congr rfl (fun j hj => if_neg (Finset.mem_erase.mp hj).1),
        Finset.prod_const, Finset.card_erase_of_mem (Finset.mem_univ i),
        Finset.card_univ, Fintype.card_fin]
  rw [hprodeval]
  ring

/-! ## 4. The main theorem -/

theorem tensor_kinFormB {m : ℕ} {ℓ d s εT b : ℝ} (hℓ : 0 < ℓ) {ψ : ℝ³ → ℝ}
    (hψ : ContDiff ℝ (⊤ : ENat) ψ) :
    Work.BoseKinLoc.kinFormB m ℓ d s εT b
        (fun z : Submission.BoseGases.X m => ∏ i : Fin m, ψ (z i))
      = (m : ℝ) * Work.BoseKinLoc.fsT ℓ d s εT b 0 ψ
        * (∫ x in Submission.BoseGases.acube ℓ, (ψ x) ^ 2) ^ (m - 1) := by
  rw [Work.BoseKinLoc.kinFormB]
  -- every slot contributes the same value
  have hterm : ∀ i : Fin m,
      (∫ x in Submission.BoseGases.abox m ℓ, Work.BoseKinLoc.indU ℓ 0 (x i) *
        Work.BoseKinLoc.fsT ℓ d s εT b 0
          (Work.BoseKinLoc.fibre m i
            (fun y : Submission.BoseGases.X m => ∏ j : Fin m, ψ (y j)) x))
      = ℓ ^ 3 * (∫ x in Submission.BoseGases.acube ℓ, (ψ x) ^ 2) ^ (m - 1)
          * Work.BoseKinLoc.fsT ℓ d s εT b 0 ψ := by
    intro i
    have hfib : ∀ x : Submission.BoseGases.X m,
        Work.BoseKinLoc.fibre m i
            (fun y : Submission.BoseGases.X m => ∏ j : Fin m, ψ (y j)) x
          = fun z => (∏ j ∈ Finset.univ.erase i, ψ (x j)) * ψ z :=
      fun x => Work.BoseKinLoc.Word.fibre_prod_eq ψ i x
    have hpt : ∀ x : Submission.BoseGases.X m,
        Work.BoseKinLoc.fsT ℓ d s εT b 0
            (Work.BoseKinLoc.fibre m i
              (fun y : Submission.BoseGases.X m => ∏ j : Fin m, ψ (y j)) x)
          = (∏ j ∈ Finset.univ.erase i, ψ (x j)) ^ 2
              * Work.BoseKinLoc.fsT ℓ d s εT b 0 ψ := by
      intro x
      rw [hfib x]
      exact fsT_const_mul' 0 ψ
    have hfun : (fun x : Submission.BoseGases.X m => Work.BoseKinLoc.indU ℓ 0 (x i) *
          Work.BoseKinLoc.fsT ℓ d s εT b 0
            (Work.BoseKinLoc.fibre m i
              (fun y : Submission.BoseGases.X m => ∏ j : Fin m, ψ (y j)) x))
        = fun x => (Work.BoseKinLoc.indU ℓ 0 (x i) *
            ∏ j ∈ Finset.univ.erase i, (ψ (x j)) ^ 2)
              * Work.BoseKinLoc.fsT ℓ d s εT b 0 ψ := by
      funext x
      rw [hpt x, ← Finset.prod_pow]
      ring
    rw [hfun, MeasureTheory.integral_mul_const,
        integral_abox_indU_erase hℓ i (fun z => (ψ z) ^ 2)]
  rw [Finset.sum_congr rfl (fun i _ => hterm i), Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul]
  -- the normalisation `ℓ⁻³` cancels the box volume `ℓ³`
  have hz : ℓ ^ (-3 : ℤ) * ℓ ^ 3 = 1 := by
    rw [zpow_neg]
    exact inv_mul_cancel₀ (pow_ne_zero 3 (ne_of_gt hℓ))
  calc ℓ ^ (-3 : ℤ) * ((m : ℝ) * (ℓ ^ 3
          * (∫ x in Submission.BoseGases.acube ℓ, (ψ x) ^ 2) ^ (m - 1)
          * Work.BoseKinLoc.fsT ℓ d s εT b 0 ψ))
      = (m : ℝ) * Work.BoseKinLoc.fsT ℓ d s εT b 0 ψ
          * (∫ x in Submission.BoseGases.acube ℓ, (ψ x) ^ 2) ^ (m - 1)
          * (ℓ ^ (-3 : ℤ) * ℓ ^ 3) := by
        ring
    _ = (m : ℝ) * Work.BoseKinLoc.fsT ℓ d s εT b 0 ψ
          * (∫ x in Submission.BoseGases.acube ℓ, (ψ x) ^ 2) ^ (m - 1) := by
        rw [hz]
        ring

end Work.Sector
