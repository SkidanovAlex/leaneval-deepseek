import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseFixB1.Q1FormDefs
import Submission.Work.BoseFixB1.q1pair_peel_localised
import Submission.Work.BoseFixB1S.integrableOn_boxFragments
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

noncomputable section

open MeasureTheory
open scoped Real BigOperators ENNReal

namespace Work.BoseFixB1P

local notation "E3" => EuclideanSpace ℝ (Fin 3)

set_option maxHeartbeats 1000000
set_option linter.unusedVariables false

theorem boxPeel_general {N : ℕ} {ℓ V : ℝ} (hℓ : 0 < ℓ) (hV : 0 < V)
    {A : Set (EuclideanSpace ℝ (Fin 3))} (hA : MeasurableSet A)
    (hAc : A ⊆ Submission.BoseGases.acube ℓ)
    (hVeq : V = (MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin 3))).real A)
    {K : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3) → ℝ}
    {fib : EuclideanSpace ℝ (Fin 3) → ℝ}
    (hfib : ∀ z : EuclideanSpace ℝ (Fin 3),
      (∫ y in Submission.BoseGases.acube ℓ,
        A.indicator (fun _ => (1 : ℝ)) y * K y z) = fib z)
    {Θ Λ : Submission.BoseGases.X N → ℝ}
    {s t : Fin N} (hst : s ≠ t)
    (hIntL : MeasureTheory.IntegrableOn
      (fun x : Submission.BoseGases.X N =>
        Work.UBBInputs8.boxPInd V A s Θ x
          * Work.UBBInputs8.boxPInd V A s Λ x * K (x s) (x t))
      (Submission.BoseGases.abox N ℓ) MeasureTheory.volume)
    (hIntR : MeasureTheory.IntegrableOn
      (fun x : Submission.BoseGases.X N =>
        Work.UBBInputs8.boxPInd V A s Θ x
          * Work.UBBInputs8.boxPInd V A s Λ x * fib (x t))
      (Submission.BoseGases.abox N ℓ) MeasureTheory.volume) :
    (∫ x in Submission.BoseGases.abox N ℓ,
        Work.UBBInputs8.boxPInd V A s Θ x
          * Work.UBBInputs8.boxPInd V A s Λ x * K (x s) (x t))
      = V⁻¹ * (∫ x in Submission.BoseGases.abox N ℓ,
        Work.UBBInputs8.boxPInd V A s Θ x
          * Work.UBBInputs8.boxPInd V A s Λ x * fib (x t)) := by
  classical
  -- A pair of distinct slots forces `N ≥ 2`; write `N = p + 2`.
  obtain ⟨p, rfl⟩ : ∃ p, N = p + 2 := by
    cases N with
    | zero => exact Fin.elim0 s
    | succ n =>
      cases n with
      | zero => exact absurd (Fin.ext (by omega)) hst
      | succ p => exact ⟨p, by omega⟩
  -- Write the second slot as `s.succAbove j'`.
  obtain ⟨j', hj'⟩ := Fin.exists_succAbove_eq (x := t) (y := s) hst.symm
  -- Abbreviations: the two integrands, and the product of the two slot-`s` means.
  set FL : Submission.BoseGases.X (p + 2) → ℝ := fun x =>
      Work.UBBInputs8.boxPInd V A s Θ x
        * Work.UBBInputs8.boxPInd V A s Λ x * K (x s) (x t) with hFLdef
  set FR : Submission.BoseGases.X (p + 2) → ℝ := fun x =>
      Work.UBBInputs8.boxPInd V A s Θ x
        * Work.UBBInputs8.boxPInd V A s Λ x * fib (x t) with hFRdef
  set A0 : Submission.BoseGases.X (p + 1) → ℝ := fun r =>
      ((1 / V) * ∫ z in A, Θ (Submission.BoseGases.kcInsN (p + 1) s (z, r)))
        * ((1 / V) * ∫ z in A, Λ (Submission.BoseGases.kcInsN (p + 1) s (z, r)))
    with hA0def
  -- Integrability of the two abbreviations on the box.
  have hIntL' : MeasureTheory.IntegrableOn FL (Submission.BoseGases.abox (p + 2) ℓ)
      MeasureTheory.volume := by
    simpa only [hFLdef] using hIntL
  have hIntR' : MeasureTheory.IntegrableOn FR (Submission.BoseGases.abox (p + 2) ℓ)
      MeasureTheory.volume := by
    simpa only [hFRdef] using hIntR
  -- The mass of the indicator: `∫_{acube ℓ} 1_A = V`.
  have hind : (∫ u in Submission.BoseGases.acube ℓ, Work.BoseFixB1S.Aind A u) = V := by
    have h1 := Work.BoseFixB1S.setIntegral_indicator_one_mul (ℓ := ℓ) (A := A) hA hAc
      (fun _ : E3 => (1 : ℝ))
    have h2 : (∫ u in Submission.BoseGases.acube ℓ, Work.BoseFixB1S.Aind A u)
        = ∫ u in A, (1 : ℝ) := by
      simpa only [Work.BoseFixB1S.Aind, mul_one] using h1
    rw [h2, MeasureTheory.setIntegral_const]
    simp only [smul_eq_mul, mul_one]
    rw [hVeq, MeasureTheory.Measure.real_def]
  -- Pointwise value of the left integrand at a configuration with the `s`-slot inserted.
  have hpointL : ∀ (r : Submission.BoseGases.X (p + 1)) (u : E3),
      FL (Submission.BoseGases.kcInsN (p + 1) s (u, r))
        = A0 r * (Work.BoseFixB1S.Aind A u * K u (r j')) := by
    intro r u
    have h1 : (Submission.BoseGases.kcInsN (p + 1) s (u, r)) s = u :=
      Submission.BoseGases.kc_insN_apply_same (p + 1) s u r
    have h2 : (Submission.BoseGases.kcInsN (p + 1) s (u, r)) (s.succAbove j') = r j' :=
      Submission.BoseGases.kc_insN_apply_succ (p + 1) s u r j'
    simp only [hFLdef]
    rw [← hj', h1, h2,
      Work.BoseFixB1S.boxPInd_kcInsN (volA := V) (A := A) (i := s) (Ψ := Θ) (t := u) (r := r),
      Work.BoseFixB1S.boxPInd_kcInsN (volA := V) (A := A) (i := s) (Ψ := Λ) (t := u) (r := r)]
    simp only [hA0def, Work.BoseFixB1S.Aind]
    by_cases hu : u ∈ A <;> simp [Set.indicator_of_mem, Set.indicator_of_notMem, hu]
  -- Pointwise value of the right integrand at a configuration with the `s`-slot inserted.
  have hpointR : ∀ (r : Submission.BoseGases.X (p + 1)) (u : E3),
      FR (Submission.BoseGases.kcInsN (p + 1) s (u, r))
        = A0 r * (Work.BoseFixB1S.Aind A u * fib (r j')) := by
    intro r u
    have h2 : (Submission.BoseGases.kcInsN (p + 1) s (u, r)) (s.succAbove j') = r j' :=
      Submission.BoseGases.kc_insN_apply_succ (p + 1) s u r j'
    simp only [hFRdef]
    rw [← hj', h2,
      Work.BoseFixB1S.boxPInd_kcInsN (volA := V) (A := A) (i := s) (Ψ := Θ) (t := u) (r := r),
      Work.BoseFixB1S.boxPInd_kcInsN (volA := V) (A := A) (i := s) (Ψ := Λ) (t := u) (r := r)]
    simp only [hA0def, Work.BoseFixB1S.Aind]
    by_cases hu : u ∈ A <;> simp [Set.indicator_of_mem, Set.indicator_of_notMem, hu]
  -- The two inner `u`-integrals on the fibre.
  have hinnerL : ∀ r : Submission.BoseGases.X (p + 1),
      (∫ u in Submission.BoseGases.acube ℓ, FL (Submission.BoseGases.kcInsN (p + 1) s (u, r)))
        = A0 r * fib (r j') := by
    intro r
    have hcongr : (∫ u in Submission.BoseGases.acube ℓ,
          FL (Submission.BoseGases.kcInsN (p + 1) s (u, r)))
        = ∫ u in Submission.BoseGases.acube ℓ,
            A0 r * (Work.BoseFixB1S.Aind A u * K u (r j')) := by
      apply MeasureTheory.integral_congr_ae
      filter_upwards with u
      exact hpointL r u
    calc (∫ u in Submission.BoseGases.acube ℓ,
          FL (Submission.BoseGases.kcInsN (p + 1) s (u, r)))
        = ∫ u in Submission.BoseGases.acube ℓ,
            A0 r * (Work.BoseFixB1S.Aind A u * K u (r j')) := hcongr
      _ = A0 r * (∫ u in Submission.BoseGases.acube ℓ,
            Work.BoseFixB1S.Aind A u * K u (r j')) := by
            rw [MeasureTheory.integral_const_mul]
      _ = A0 r * fib (r j') := by
            simp only [Work.BoseFixB1S.Aind]
            rw [hfib (r j')]
  have hinnerR : ∀ r : Submission.BoseGases.X (p + 1),
      (∫ u in Submission.BoseGases.acube ℓ, FR (Submission.BoseGases.kcInsN (p + 1) s (u, r)))
        = A0 r * fib (r j') * V := by
    intro r
    have hcongr : (∫ u in Submission.BoseGases.acube ℓ,
          FR (Submission.BoseGases.kcInsN (p + 1) s (u, r)))
        = ∫ u in Submission.BoseGases.acube ℓ,
            A0 r * (Work.BoseFixB1S.Aind A u * fib (r j')) := by
      apply MeasureTheory.integral_congr_ae
      filter_upwards with u
      exact hpointR r u
    calc (∫ u in Submission.BoseGases.acube ℓ,
          FR (Submission.BoseGases.kcInsN (p + 1) s (u, r)))
        = ∫ u in Submission.BoseGases.acube ℓ,
            A0 r * (Work.BoseFixB1S.Aind A u * fib (r j')) := hcongr
      _ = A0 r * (∫ u in Submission.BoseGases.acube ℓ,
            Work.BoseFixB1S.Aind A u * fib (r j')) := by
            rw [MeasureTheory.integral_const_mul]
      _ = A0 r * ((∫ u in Submission.BoseGases.acube ℓ, Work.BoseFixB1S.Aind A u)
            * fib (r j')) := by
            rw [MeasureTheory.integral_mul_const]
      _ = A0 r * (V * fib (r j')) := by rw [hind]
      _ = A0 r * fib (r j') * V := by ring
  -- Peel both sides at the `s`-slot, then integrate out the fibre.
  have hL : (∫ r in Submission.BoseGases.abox (p + 1) ℓ,
        ∫ u in Submission.BoseGases.acube ℓ, FL (Submission.BoseGases.kcInsN (p + 1) s (u, r)))
      = ∫ r in Submission.BoseGases.abox (p + 1) ℓ, A0 r * fib (r j') := by
    apply MeasureTheory.integral_congr_ae
    filter_upwards with r
    exact hinnerL r
  have hR : (∫ r in Submission.BoseGases.abox (p + 1) ℓ,
        ∫ u in Submission.BoseGases.acube ℓ, FR (Submission.BoseGases.kcInsN (p + 1) s (u, r)))
      = ∫ r in Submission.BoseGases.abox (p + 1) ℓ, A0 r * fib (r j') * V := by
    apply MeasureTheory.integral_congr_ae
    filter_upwards with r
    exact hinnerR r
  have hpeelL := Submission.BoseGases.abox_integral_peel (n := p + 1) (ℓ := ℓ) (i := s)
    (F := FL) hIntL'
  have hpeelR := Submission.BoseGases.abox_integral_peel (n := p + 1) (ℓ := ℓ) (i := s)
    (F := FR) hIntR'
  rw [hpeelL, hpeelR, hL, hR]
  -- Pull the constant `V` out of the right-hand integral and cancel `V⁻¹`.
  rw [show (∫ r in Submission.BoseGases.abox (p + 1) ℓ, A0 r * fib (r j') * V)
      = V * (∫ r in Submission.BoseGases.abox (p + 1) ℓ, A0 r * fib (r j')) from by
        rw [MeasureTheory.integral_mul_const]
        ring]
  rw [inv_mul_cancel_left₀ (ne_of_gt hV)]

end Work.BoseFixB1P
