import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseFixB1S.BoxPotDefs
import Submission.Work.BoseFixB1S.BoxQIndCore
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

noncomputable section

open MeasureTheory Metric Filter
open scoped Topology Real BigOperators ENNReal

namespace Work.BoseFixB1S

open _root_.BoseGases Submission.BoseGases

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

/-- **The peel at the box projections** (measurable-argument form). -/
theorem boxPeelGen {N : ℕ} {ℓ volA : ℝ} (hℓ : 0 < ℓ) (hvol : 0 < volA)
    {A : Set (EuclideanSpace ℝ (Fin 3))} (hA : MeasurableSet A)
    (hvolA : volA = (MeasureTheory.volume A).toReal) (hAc : A ⊆ acube ℓ)
    {i j : Fin N} (hij : i ≠ j)
    {k : (EuclideanSpace ℝ (Fin 3)) → (EuclideanSpace ℝ (Fin 3)) → ℝ} {C : ℝ}
    (hkC : ∀ a : EuclideanSpace ℝ (Fin 3),
      |∫ y in acube ℓ, Aind A y * k a y| ≤ C)
    {Ψ : X N → ℝ}
    (hΨm : AEStronglyMeasurable Ψ (MeasureTheory.volume.restrict (abox N ℓ)))
    {B : ℝ} (hB : ∀ᵐ x ∂(MeasureTheory.volume.restrict (abox N ℓ)), |Ψ x| ≤ B)
    (hPi : MeasureTheory.IntegrableOn
      (fun x : X N => (Work.UBBInputs8.boxPInd volA A i Ψ x) ^ 2) (abox N ℓ)
      MeasureTheory.volume)
    (hki : MeasureTheory.IntegrableOn (fun x : X N =>
      (Work.UBBInputs8.boxPInd volA A i Ψ x) ^ 2 * k (x j) (x i)) (abox N ℓ)
      MeasureTheory.volume) :
    (∫ x in abox N ℓ, (Work.UBBInputs8.boxPInd volA A i Ψ x) ^ 2 * k (x j) (x i))
      ≤ C * volA⁻¹ * (∫ x in abox N ℓ, (Work.UBBInputs8.boxPInd volA A i Ψ x) ^ 2) := by
  rcases N with _ | _ | p
  · exact absurd i.isLt (Nat.not_lt_zero _)
  · exact absurd (Fin.ext (by omega)) hij
  · obtain ⟨j', hj'⟩ := Fin.exists_succAbove_eq (n := p + 1) hij.symm
    -- `hj' : i.succAbove j' = j`
    set A0 : X (p + 1) → ℝ :=
      fun r => (1 / volA * ∫ z in A, Ψ (kcInsN (p + 1) i (z, r))) ^ 2 with hA0def
    set F : X (p + 2) → ℝ :=
      fun x => (Work.UBBInputs8.boxPInd volA A i Ψ x) ^ 2 * k (x j) (x i) with hFdef
    set Fp : X (p + 2) → ℝ :=
      fun x => (Work.UBBInputs8.boxPInd volA A i Ψ x) ^ 2 with hFpdef
    have hj'' : i.succAbove j' = j := hj'
    -- the inserted-fibre value
    have hpoint : ∀ (r : X (p + 1)) (t : EuclideanSpace ℝ (Fin 3)),
        F (kcInsN (p + 1) i (t, r))
          = Aind A t * (A0 r * k (r j') t) := by
      intro r t
      have h1 : (kcInsN (p + 1) i (t, r)) j = r j' := by
        rw [← hj'']; exact kc_insN_apply_succ (p + 1) i t r j'
      have h2 : (kcInsN (p + 1) i (t, r)) i = t := kc_insN_apply_same (p + 1) i t r
      have h3 := boxPInd_kcInsN (volA := volA) (A := A) (i := i) Ψ t r
      simp only [hFdef, h1, h2, h3, hA0def, Aind]
      have hA2 : A.indicator (fun _ => (1 : ℝ)) t * A.indicator (fun _ => (1 : ℝ)) t
          = A.indicator (fun _ => (1 : ℝ)) t := Aind_mul_self A t
      rw [mul_pow, sq, hA2]
      ring
    have hpointP : ∀ (r : X (p + 1)) (t : EuclideanSpace ℝ (Fin 3)),
        Fp (kcInsN (p + 1) i (t, r)) = Aind A t * A0 r := by
      intro r t
      have h3 := boxPInd_kcInsN (volA := volA) (A := A) (i := i) Ψ t r
      simp only [hFpdef, h3, hA0def, Aind]
      have hA2 : A.indicator (fun _ => (1 : ℝ)) t * A.indicator (fun _ => (1 : ℝ)) t
          = A.indicator (fun _ => (1 : ℝ)) t := Aind_mul_self A t
      rw [mul_pow, sq, hA2]
    -- the two peels
    have hpeel := abox_integral_peel (n := p + 1) (i := i) (F := F) hki
    have hpeelP := abox_integral_peel (n := p + 1) (i := i) (F := Fp) hPi
    have hInnIntP : Integrable (fun r : X (p + 1) =>
        ∫ t in acube ℓ, Fp (kcInsN (p + 1) i (t, r)))
        (MeasureTheory.volume.restrict (abox (p + 1) ℓ)) :=
      abox_peel_inner_integrable (n := p + 1) (i := i) (F := Fp) hPi
    have hInnInt : Integrable (fun r : X (p + 1) =>
        ∫ t in acube ℓ, F (kcInsN (p + 1) i (t, r)))
        (MeasureTheory.volume.restrict (abox (p + 1) ℓ)) :=
      abox_peel_inner_integrable (n := p + 1) (i := i) (F := F) hki
    -- the `t`-integral of the indicator
    have hind : (∫ t in acube ℓ, Aind A t) = volA := by
      have h1 := setIntegral_indicator_one_mul (ℓ := ℓ) (A := A) hA hAc (fun _ => (1 : ℝ))
      have h2 : (∫ t in acube ℓ, Aind A t) = ∫ t in A, (1 : ℝ) := by
        simpa [Aind, mul_one] using h1
      rw [h2, MeasureTheory.setIntegral_const]
      simp only [mul_one, smul_eq_mul]
      rw [hvolA]
      rfl
    -- the value of the indicator-weighted integral of `A0`
    have hA0int : ∀ r : X (p + 1),
        (∫ t in acube ℓ, Fp (kcInsN (p + 1) i (t, r))) = volA * A0 r := by
      intro r
      calc (∫ t in acube ℓ, Fp (kcInsN (p + 1) i (t, r)))
          = ∫ t in acube ℓ, Aind A t * A0 r := by
            apply integral_congr_ae
            filter_upwards with t
            exact hpointP r t
        _ = (∫ t in acube ℓ, Aind A t) * A0 r := by
            rw [MeasureTheory.integral_mul_const]
        _ = volA * A0 r := by rw [hind]
    -- the bound on the `t`-integral of `F`
    have hFint : ∀ r : X (p + 1),
        (∫ t in acube ℓ, F (kcInsN (p + 1) i (t, r))) ≤ A0 r * C := by
      intro r
      have hconst : ∀ t : EuclideanSpace ℝ (Fin 3),
          F (kcInsN (p + 1) i (t, r)) = A0 r * (Aind A t * k (r j') t) := by
        intro t
        rw [hpoint r t]; ring
      calc (∫ t in acube ℓ, F (kcInsN (p + 1) i (t, r)))
          = ∫ t in acube ℓ, A0 r * (Aind A t * k (r j') t) := by
            apply integral_congr_ae
            filter_upwards with t
            exact hconst t
        _ = A0 r * (∫ t in acube ℓ, Aind A t * k (r j') t) := by
            rw [MeasureTheory.integral_const_mul]
        _ ≤ A0 r * C := by
            refine mul_le_mul_of_nonneg_left ?_ (sq_nonneg _)
            exact (abs_le.mp (hkC (r j'))).2
    -- assemble
    have hmain : (∫ x in abox (p + 2) ℓ, F x) = ∫ r in abox (p + 1) ℓ,
        ∫ t in acube ℓ, F (kcInsN (p + 1) i (t, r)) := hpeel
    have hmainP : (∫ x in abox (p + 2) ℓ, Fp x) = ∫ r in abox (p + 1) ℓ,
        ∫ t in acube ℓ, Fp (kcInsN (p + 1) i (t, r)) := hpeelP
    have hA0int_ae : (fun r : X (p + 1) => ∫ t in acube ℓ, Fp (kcInsN (p + 1) i (t, r)))
        = fun r : X (p + 1) => volA * A0 r := funext hA0int
    have hA0int_meas : Integrable (fun r : X (p + 1) => A0 r)
        (MeasureTheory.volume.restrict (abox (p + 1) ℓ)) := by
      have h1 : Integrable (fun r : X (p + 1) => volA * A0 r)
          (MeasureTheory.volume.restrict (abox (p + 1) ℓ)) := by
        rw [← hA0int_ae]; exact hInnIntP
      refine (h1.const_mul volA⁻¹).congr (Filter.Eventually.of_forall fun r => ?_)
      show volA⁻¹ * (volA * A0 r) = A0 r
      rw [← mul_assoc, inv_mul_cancel₀ (ne_of_gt hvol), one_mul]
    have hle : (∫ x in abox (p + 2) ℓ, F x) ≤ C * (∫ r in abox (p + 1) ℓ, A0 r) := by
      rw [hmain]
      calc (∫ r in abox (p + 1) ℓ, ∫ t in acube ℓ, F (kcInsN (p + 1) i (t, r)))
          ≤ ∫ r in abox (p + 1) ℓ, A0 r * C := by
            refine integral_mono_ae hInnInt (hA0int_meas.mul_const C) ?_
            filter_upwards with r
            exact hFint r
        _ = C * (∫ r in abox (p + 1) ℓ, A0 r) := by
            rw [MeasureTheory.integral_mul_const]
            ring
    have hEq : (∫ x in abox (p + 2) ℓ, Fp x) = volA * (∫ r in abox (p + 1) ℓ, A0 r) := by
      rw [hmainP]
      calc (∫ r in abox (p + 1) ℓ, ∫ t in acube ℓ, Fp (kcInsN (p + 1) i (t, r)))
          = ∫ r in abox (p + 1) ℓ, volA * A0 r := by
            apply integral_congr_ae
            filter_upwards with r
            exact hA0int r
        _ = volA * (∫ r in abox (p + 1) ℓ, A0 r) := by
            rw [MeasureTheory.integral_const_mul]
    calc (∫ x in abox (p + 2) ℓ, F x)
        = (∫ x in abox (p + 2) ℓ, (Work.UBBInputs8.boxPInd volA A i Ψ x) ^ 2
            * k (x j) (x i)) := rfl
      _ ≤ C * (∫ r in abox (p + 1) ℓ, A0 r) := hle
      _ = C * volA⁻¹ * (volA * (∫ r in abox (p + 1) ℓ, A0 r)) := by
            field_simp
      _ = C * volA⁻¹ * (∫ x in abox (p + 2) ℓ,
            (Work.UBBInputs8.boxPInd volA A i Ψ x) ^ 2) := by
            rw [← hEq]

end Work.BoseFixB1S
