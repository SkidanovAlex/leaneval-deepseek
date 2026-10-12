import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseFixB1.BoxPairIntGenC2.EvenC2Cont
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixB1.BoxPairIntGenC2.EvenC2Peel`

The two-slot peel of the *indicator-free* box pair integrand at the two parametrisations
`(i, i.succAbove j')` and `(i.succAbove j', i)` of the same slice.  Since the integrand carries no
box indicator, the peel `Submission.BoseGases.peel_pair_kernel` applied to it produces genuine
identities of weighted integrals of the *free* fibre, valid for every continuous weight:

    `∫_y∫_z W y z · Free_{i,j'}(y,z) = ∫_y∫_z W z y · Free_{i.succAbove j', i}(y,z)`.

This is the step that makes the symmetry of the free fibre available (together with the
continuity of the latter, proved in `EvenC2Cont`).
-/

noncomputable section

open MeasureTheory Metric Filter
open scoped Topology Real BigOperators ENNReal

namespace Work.BoseFixB1.BoxPairIntGenC2

open _root_.BoseGases Submission.BoseGases

local notation "E3" => EuclideanSpace ℝ (Fin 3)

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

/-- The indicator-free peeled pair integrand is invariant under the interchange of the two
parametrisations of the slice. -/
lemma evenC2Integrand_swap {N : ℕ} {ℓ volA : ℝ} {A : Set E3}
    (hA : MeasurableSet A) (hℓ : 0 < ℓ) (hAc : A ⊆ Submission.BoseGases.acube ℓ)
    {Φ : Submission.BoseGases.X (N + 2) → ℝ} (hΦc : Continuous Φ)
    (i : Fin (N + 2)) (j' : Fin (N + 1)) (x : Submission.BoseGases.X (N + 2)) :
    evenC2Integrand volA A Φ i j' x
      = evenC2Integrand volA A Φ (i.succAbove j')
          (Submission.BoseGases.sucAboveInv (i.succAbove j') i (Fin.ne_succAbove i j').symm) x := by
  have hij' : i.succAbove j' ≠ i := (Fin.ne_succAbove i j').symm
  have hjj : (i.succAbove j').succAbove
      (Submission.BoseGases.sucAboveInv (i.succAbove j') i hij') = i :=
    Submission.BoseGases.succAbove_sucAboveInv (i.succAbove j') i hij'
  unfold evenC2Integrand
  rw [hjj]
  rw [Work.BoseFixB1S.twoMean_comm hℓ hA hAc hij' hΦc x]
  ring

/-- **The weighted peel identity of the free fibre.**  For every continuous weight `W` the
`r2`-integral of the free integrand over the `(i, i.succAbove j')`-parametrisation of the slice
equals the same with the two slots interchanged. -/
theorem evenC2Free_peel {N : ℕ} {ℓ volA : ℝ} {A : Set E3}
    (hA : MeasurableSet A) (hℓ : 0 < ℓ) (hAc : A ⊆ Submission.BoseGases.acube ℓ)
    {Φ : Submission.BoseGases.X (N + 2) → ℝ} (hΦc : Continuous Φ)
    (i : Fin (N + 2)) (j' : Fin (N + 1))
    (W : E3 → E3 → ℝ) (hWc : Continuous (Function.uncurry W)) :
    (∫ y in Submission.BoseGases.acube ℓ, ∫ z in Submission.BoseGases.acube ℓ,
        W y z * evenC2Free volA ℓ A Φ i j' y z)
      = ∫ y in Submission.BoseGases.acube ℓ, ∫ z in Submission.BoseGases.acube ℓ,
          W z y * evenC2Free volA ℓ A Φ (i.succAbove j')
            (Submission.BoseGases.sucAboveInv (i.succAbove j') i (Fin.ne_succAbove i j').symm)
            y z := by
  have hij' : i.succAbove j' ≠ i := (Fin.ne_succAbove i j').symm
  have hjj : (i.succAbove j').succAbove
      (Submission.BoseGases.sucAboveInv (i.succAbove j') i hij') = i :=
    Submission.BoseGases.succAbove_sucAboveInv (i.succAbove j') i hij'
  set Ht : Submission.BoseGases.X (N + 2) → ℝ :=
    fun x => evenC2Integrand volA A Φ i j' x with hHt
  have hHtc : Continuous Ht := continuous_evenC2Integrand hA hℓ hAc hΦc i j'
  -- bounds
  obtain ⟨Ch₀, hCh₀⟩ := (Submission.BoseGases.abox_compact (N + 2) hℓ).exists_bound_of_continuousOn
    hHtc.continuousOn
  have hChb : ∀ x ∈ Submission.BoseGases.abox (N + 2) ℓ, |Ht x| ≤ max Ch₀ 0 := fun x hx => by
    have h := hCh₀ x hx
    rw [Real.norm_eq_abs] at h
    exact le_trans h (le_max_left _ _)
  obtain ⟨CW₀, hCW₀⟩ := ((Submission.BoseGases.acube_compact hℓ).prod
    (Submission.BoseGases.acube_compact hℓ)).exists_bound_of_continuousOn hWc.continuousOn
  have hCWb : ∀ y ∈ Submission.BoseGases.acube ℓ, ∀ z ∈ Submission.BoseGases.acube ℓ,
      |W y z| ≤ max CW₀ 0 := fun y hy z hz => by
    have h := hCW₀ (y, z) ⟨hy, hz⟩
    rw [Real.norm_eq_abs] at h
    exact le_trans h (le_max_left _ _)
  -- integrability of the two weighted integrands on the box
  have hbound1 : ∀ x ∈ Submission.BoseGases.abox (N + 2) ℓ,
      ‖Ht x * W (x i) (x (i.succAbove j'))‖ ≤ max Ch₀ 0 * max CW₀ 0 := by
    intro x hx
    rw [Real.norm_eq_abs, abs_mul]
    exact mul_le_mul (hChb x hx) (hCWb (x i) (hx i) (x (i.succAbove j')) (hx (i.succAbove j')))
      (abs_nonneg _) (le_max_right _ _)
  have hF1 : IntegrableOn (fun x : Submission.BoseGases.X (N + 2) =>
      Ht x * W (x i) (x (i.succAbove j'))) (Submission.BoseGases.abox (N + 2) ℓ) volume := by
    refine IntegrableOn.of_bound (Submission.BoseGases.abox_lt_top (N + 2) ℓ hℓ.le) ?_
      (max Ch₀ 0 * max CW₀ 0) ?_
    · exact (hHtc.measurable.mul (hWc.measurable.comp (((continuous_apply i).measurable).prodMk
        ((continuous_apply (i.succAbove j')).measurable)))).aestronglyMeasurable
    · rw [ae_restrict_iff' (Submission.BoseGases.abox_measurable (N + 2) ℓ)]
      filter_upwards with x hx
      exact hbound1 x hx
  have hbound2 : ∀ x ∈ Submission.BoseGases.abox (N + 2) ℓ,
      ‖Ht x * W (x ((i.succAbove j').succAbove (Submission.BoseGases.sucAboveInv
        (i.succAbove j') i hij'))) (x (i.succAbove j'))‖ ≤ max Ch₀ 0 * max CW₀ 0 := by
    intro x hx
    rw [hjj]
    rw [Real.norm_eq_abs, abs_mul]
    exact mul_le_mul (hChb x hx) (hCWb (x i) (hx i) (x (i.succAbove j')) (hx (i.succAbove j')))
      (abs_nonneg _) (le_max_right _ _)
  have hF2 : IntegrableOn (fun x : Submission.BoseGases.X (N + 2) =>
      Ht x * W (x ((i.succAbove j').succAbove (Submission.BoseGases.sucAboveInv
        (i.succAbove j') i hij'))) (x (i.succAbove j')))
      (Submission.BoseGases.abox (N + 2) ℓ) volume := by
    refine IntegrableOn.of_bound (Submission.BoseGases.abox_lt_top (N + 2) ℓ hℓ.le) ?_
      (max Ch₀ 0 * max CW₀ 0) ?_
    · exact (hHtc.measurable.mul (hWc.measurable.comp
        (((continuous_apply ((i.succAbove j').succAbove (Submission.BoseGases.sucAboveInv
          (i.succAbove j') i hij'))).measurable).prodMk
          ((continuous_apply (i.succAbove j')).measurable)))).aestronglyMeasurable
    · rw [ae_restrict_iff' (Submission.BoseGases.abox_measurable (N + 2) ℓ)]
      filter_upwards with x hx
      exact hbound2 x hx
  -- the two peels
  have hpeel1 := Submission.BoseGases.peel_pair_kernel hℓ i j' (G := Ht) (w := W) hF1
  have hpeel2 := Submission.BoseGases.peel_pair_kernel hℓ (i.succAbove j')
    (Submission.BoseGases.sucAboveInv (i.succAbove j') i hij') (G := Ht)
    (w := fun y z => W z y) hF2
  rw [hjj] at hpeel2
  -- the two weighted integrals agree
  have hkey : (∫ y in Submission.BoseGases.acube ℓ, ∫ z in Submission.BoseGases.acube ℓ,
        W y z * (∫ r2 in Submission.BoseGases.abox N ℓ, Ht (ins2 i j' y z r2)))
      = ∫ y in Submission.BoseGases.acube ℓ, ∫ z in Submission.BoseGases.acube ℓ,
          W z y * (∫ r2 in Submission.BoseGases.abox N ℓ,
            Ht (ins2 (i.succAbove j')
              (Submission.BoseGases.sucAboveInv (i.succAbove j') i hij') y z r2)) := by
    rw [← hpeel1, hpeel2]
  -- convert the left side into the fibre
  have hL : (∫ y in Submission.BoseGases.acube ℓ, ∫ z in Submission.BoseGases.acube ℓ,
        W y z * evenC2Free volA ℓ A Φ i j' y z)
      = ∫ y in Submission.BoseGases.acube ℓ, ∫ z in Submission.BoseGases.acube ℓ,
          W y z * (∫ r2 in Submission.BoseGases.abox N ℓ, Ht (ins2 i j' y z r2)) := by
    simp only [evenC2Free, hHt]
  -- the inner integral on the right is the fibre of the interchanged parametrisation
  have hinner : ∀ y z : E3, (∫ r2 in Submission.BoseGases.abox N ℓ,
        Ht (ins2 (i.succAbove j')
          (Submission.BoseGases.sucAboveInv (i.succAbove j') i hij') y z r2))
      = evenC2Free volA ℓ A Φ (i.succAbove j')
          (Submission.BoseGases.sucAboveInv (i.succAbove j') i hij') y z := by
    intro y z
    rw [evenC2Free]
    refine integral_congr_ae (Eventually.of_forall fun r2 => ?_)
    show Ht (ins2 (i.succAbove j')
        (Submission.BoseGases.sucAboveInv (i.succAbove j') i hij') y z r2)
      = evenC2Integrand volA A Φ (i.succAbove j')
        (Submission.BoseGases.sucAboveInv (i.succAbove j') i hij')
        (ins2 (i.succAbove j')
          (Submission.BoseGases.sucAboveInv (i.succAbove j') i hij') y z r2)
    rw [hHt]
    exact evenC2Integrand_swap hA hℓ hAc hΦc i j' _
  -- convert the right side into the fibre
  have hR : (∫ y in Submission.BoseGases.acube ℓ, ∫ z in Submission.BoseGases.acube ℓ,
        W z y * (∫ r2 in Submission.BoseGases.abox N ℓ,
          Ht (ins2 (i.succAbove j')
            (Submission.BoseGases.sucAboveInv (i.succAbove j') i hij') y z r2)))
      = ∫ y in Submission.BoseGases.acube ℓ, ∫ z in Submission.BoseGases.acube ℓ,
          W z y * evenC2Free volA ℓ A Φ (i.succAbove j')
            (Submission.BoseGases.sucAboveInv (i.succAbove j') i hij') y z := by
    refine integral_congr_ae (Eventually.of_forall fun y => ?_)
    refine integral_congr_ae (Eventually.of_forall fun z => ?_)
    show W z y * (∫ r2 in Submission.BoseGases.abox N ℓ,
        Ht (ins2 (i.succAbove j')
          (Submission.BoseGases.sucAboveInv (i.succAbove j') i hij') y z r2))
      = W z y * evenC2Free volA ℓ A Φ (i.succAbove j')
          (Submission.BoseGases.sucAboveInv (i.succAbove j') i hij') y z
    rw [hinner y z]
  exact hL.trans (hkey.trans hR)

end Work.BoseFixB1.BoxPairIntGenC2
