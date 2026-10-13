/-
Copyright: work module for the Elgindi finite-time singularity project.

# `FkTileAux/fkPairingAux` — the three priced pieces of the top-slot majorant

* `TT_int_le` — `∫_z w² T₀ ≤ HkSq α 6 f` (and integrability) through the `leafOne`-weighted
  `D_z`-slot `i = 6` of `HkIntegrand α 6 f` (`val_le_HkSq`);
* `Etale_int_le` — `∫∫ leafEta · (D_z^6 f)² ≤ HkSq α 6 f`, the `leafEta`-weighted version;
* `leafEta_T0_int` — the separable Fubini identity
  `∫∫ leafEta(z,θ) T₀(z) = C_η ∫_z w(z)² T₀(z)` with `C_η = ∫_θ sin(2θ)^{-η}`.

Everything rests on `[propext, Classical.choice, Quot.sound]`.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.Prod
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.FkTileAux.fkPairingDefs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.FkTileAux

open Work.FTS.StrongPersist.H6Rows.Npair6BWork (PM aesm_mixed aesm_leafW val_le_HkSq)

set_option autoImplicit false
set_option maxHeartbeats 3200000

/-- `∫_z w² T₀ ≤ HkSq α 6 f` (and integrability), via the `leafOne`-weighted `D_z`-slot of
`HkIntegrand α 6 f`. -/
theorem TT_int_le {α : ℝ} {f : ℝ → ℝ → ℝ}
    (hsm : Work.FTS.EllipticEst.SmoothOpen f) (hmem : Work.Spaces.HkMem α 6 f) :
    MeasureTheory.Integrable (TT f) (MeasureTheory.volume.restrict Work.Spaces.Iz) ∧
      (∫ z in Work.Spaces.Iz, TT f z) ≤ Work.Spaces.HkSq α 6 f := by
  have hρnn : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      0 ≤ Work.FTS.TransportS.leafOne z θ := fun z θ _ _ _ => sq_nonneg _
  have hdom : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      Work.FTS.TransportS.leafOne z θ * (Work.Spaces.DzIter 6 f z θ) ^ 2
        ≤ Work.Spaces.HkIntegrand α 6 f z θ := by
    intro z θ hz hθ0 hθ1
    have hs : 0 ≤ Real.sin (2 * θ) :=
      Real.sin_nonneg_of_nonneg_of_le_pi (by linarith) (by linarith [Real.pi_pos])
    have hWhz : (Work.FTS.H2.Whz z θ) ^ 2
        = (Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) :=
      Work.FTS.H2.hbi_Whz_sq z θ hs
    have h1 : (1 : ℝ) ≤ (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) :=
      Work.FTS.TransportS.one_le_rpow_neg Work.Spaces.eta_nonneg ⟨hθ0, hθ1⟩
    calc Work.FTS.TransportS.leafOne z θ * (Work.Spaces.DzIter 6 f z θ) ^ 2
        = (Work.Spaces.w z) ^ 2 * (Work.Spaces.DzIter 6 f z θ) ^ 2 := by
          rw [Work.FTS.TransportS.leafOne]
      _ = ((Work.Spaces.w z) ^ 2 * (Work.Spaces.DzIter 6 f z θ) ^ 2) * 1 := by ring
      _ ≤ ((Work.Spaces.w z) ^ 2 * (Work.Spaces.DzIter 6 f z θ) ^ 2)
            * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) :=
          mul_le_mul_of_nonneg_left h1 (mul_nonneg (sq_nonneg _) (sq_nonneg _))
      _ = (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) * (Work.Spaces.w z) ^ 2
            * (Work.Spaces.DzIter 6 f z θ) ^ 2 := by ring
      _ = (Work.Spaces.DzIter 6 f z θ * Work.FTS.H2.Whz z θ) ^ 2 := by
          rw [mul_pow, hWhz]; ring
      _ = (Work.Spaces.DzIter 6 f z θ
            * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2 := by
          rw [Work.FTS.H2.Whz_eq]
      _ ≤ Work.Spaces.HkIntegrand α 6 f z θ :=
          Work.Spaces.sq_le_HkIntegrand_z α 6 f z θ 6 le_rfl
  have hmeas : MeasureTheory.AEStronglyMeasurable
      (fun p : ℝ × ℝ => Work.FTS.TransportS.leafOne p.1 p.2
        * (Work.Spaces.DzIter 6 f p.1 p.2) ^ 2) PM :=
    (aesm_leafW (α := α) (a := 0) (ρ := Work.FTS.TransportS.leafOne)
        (Or.inr (Or.inl rfl))).mul ((aesm_mixed hsm 6 0).pow 2)
  obtain ⟨hint, hval⟩ := val_le_HkSq (α := α) (k := 6) (f := f)
    (ρv := Work.FTS.TransportS.leafOne) (X := Work.Spaces.DzIter 6 f) hsm hmem hρnn hdom hmeas
  have hkey : (fun z => ∫ θ in Work.Spaces.Iθ, Work.FTS.TransportS.leafOne z θ
        * (Work.Spaces.DzIter 6 f z θ) ^ 2)
      = TT f := by
    funext z
    show (∫ θ in Work.Spaces.Iθ, (Work.Spaces.w z) ^ 2
        * (Work.Spaces.DzIter 6 f z θ) ^ 2) = (Work.Spaces.w z) ^ 2 * T0 f z
    rw [MeasureTheory.integral_const_mul]
    rfl
  constructor
  · rw [← hkey]
    exact hint.integral_prod_left
  · rw [← hkey]
    rw [MeasureTheory.integral_integral (μ := MeasureTheory.volume.restrict Work.Spaces.Iz)
      (ν := MeasureTheory.volume.restrict Work.Spaces.Iθ)
      (f := fun z θ => Work.FTS.TransportS.leafOne z θ
        * (Work.Spaces.DzIter 6 f z θ) ^ 2) hint]
    exact hval

/-- `∫∫ leafEta · (D_z^6 f)² ≤ HkSq α 6 f` (and integrability): the `D_z`-slot `i = 6` of the
`ℋ⁶`-integrand, weighted by `leafEta = w² sin(2θ)^{-η}`. -/
theorem Etale_int_le {α : ℝ} {f : ℝ → ℝ → ℝ}
    (hsm : Work.FTS.EllipticEst.SmoothOpen f) (hmem : Work.Spaces.HkMem α 6 f) :
    MeasureTheory.Integrable (fun p : ℝ × ℝ => Work.FTS.TransportS.leafEta p.1 p.2
        * (Work.Spaces.DzIter 6 f p.1 p.2) ^ 2) PM ∧
      (∫ p, Work.FTS.TransportS.leafEta p.1 p.2
        * (Work.Spaces.DzIter 6 f p.1 p.2) ^ 2 ∂PM) ≤ Work.Spaces.HkSq α 6 f := by
  have hρnn : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      0 ≤ Work.FTS.TransportS.leafEta z θ := by
    intro z θ _ hθ0 hθ1
    rw [Work.FTS.TransportS.leafEta]
    exact mul_nonneg (sq_nonneg _) (Real.rpow_nonneg
      (Real.sin_nonneg_of_nonneg_of_le_pi (by linarith) (by linarith [Real.pi_pos])) _)
  have hdom : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      Work.FTS.TransportS.leafEta z θ * (Work.Spaces.DzIter 6 f z θ) ^ 2
        ≤ Work.Spaces.HkIntegrand α 6 f z θ := by
    intro z θ hz hθ0 hθ1
    have hs : 0 ≤ Real.sin (2 * θ) :=
      Real.sin_nonneg_of_nonneg_of_le_pi (by linarith) (by linarith [Real.pi_pos])
    have hWhz : (Work.FTS.H2.Whz z θ) ^ 2
        = (Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) :=
      Work.FTS.H2.hbi_Whz_sq z θ hs
    have heq : Work.FTS.TransportS.leafEta z θ = (Work.FTS.H2.Whz z θ) ^ 2 := by
      rw [Work.FTS.TransportS.leafEta, hWhz]
    rw [heq, show (Work.FTS.H2.Whz z θ) ^ 2 * (Work.Spaces.DzIter 6 f z θ) ^ 2
        = (Work.Spaces.DzIter 6 f z θ * Work.FTS.H2.Whz z θ) ^ 2 by ring,
      Work.FTS.H2.Whz_eq]
    exact Work.Spaces.sq_le_HkIntegrand_z α 6 f z θ 6 le_rfl
  have hmeas : MeasureTheory.AEStronglyMeasurable
      (fun p : ℝ × ℝ => Work.FTS.TransportS.leafEta p.1 p.2
        * (Work.Spaces.DzIter 6 f p.1 p.2) ^ 2) PM :=
    (aesm_leafW (α := α) (a := 0) (ρ := Work.FTS.TransportS.leafEta)
        (Or.inl rfl)).mul ((aesm_mixed hsm 6 0).pow 2)
  exact val_le_HkSq (α := α) (k := 6) (f := f) (ρv := Work.FTS.TransportS.leafEta)
    (X := Work.Spaces.DzIter 6 f) hsm hmem hρnn hdom hmeas

/-- The separable Fubini identity `∫∫ leafEta(z,θ)·T₀(z) = C_η ∫_z w(z)² T₀(z)`, with
`C_η = ∫_θ sin(2θ)^{-η}`. -/
theorem leafEta_T0_int {Cη : ℝ}
    (hCη : Cη = ∫ θ in Work.Spaces.Iθ, (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))
    {f : ℝ → ℝ → ℝ} (hTT : MeasureTheory.Integrable (TT f)
      (MeasureTheory.volume.restrict Work.Spaces.Iz)) :
    MeasureTheory.Integrable (fun p : ℝ × ℝ => Work.FTS.TransportS.leafEta p.1 p.2 * T0 f p.1)
        PM ∧
      (∫ p, Work.FTS.TransportS.leafEta p.1 p.2 * T0 f p.1 ∂PM)
        = Cη * ∫ z in Work.Spaces.Iz, TT f z := by
  have hσ : MeasureTheory.Integrable
      (fun θ : ℝ => (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))
      (MeasureTheory.volume.restrict Work.Spaces.Iθ) :=
    (Work.Spaces.sin_two_rpow (-(Work.Spaces.eta)) (by norm_num [Work.Spaces.eta])
      (by norm_num [Work.Spaces.eta])).1
  have hmul : MeasureTheory.Integrable
      (fun p : ℝ × ℝ => TT f p.1 * (Real.sin (2 * p.2)) ^ (-(Work.Spaces.eta))) PM :=
    hTT.mul_prod hσ
  have hcongr : (fun p : ℝ × ℝ => Work.FTS.TransportS.leafEta p.1 p.2 * T0 f p.1)
      =ᵐ[PM] fun p : ℝ × ℝ => TT f p.1 * (Real.sin (2 * p.2)) ^ (-(Work.Spaces.eta)) :=
    Filter.Eventually.of_forall fun p => by
      simp only [Work.FTS.TransportS.leafEta, TT]
      ring
  refine ⟨hmul.congr hcongr.symm, ?_⟩
  rw [MeasureTheory.integral_congr_ae hcongr, MeasureTheory.integral_prod _ hmul]
  have hinner : ∀ z : ℝ, (∫ θ in Work.Spaces.Iθ, TT f z
      * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))
      = TT f z * (∫ θ in Work.Spaces.Iθ, (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))) :=
    fun z => MeasureTheory.integral_const_mul _ _
  simp only [hinner]
  rw [MeasureTheory.integral_mul_const, ← hCη]
  ring

end Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.FkTileAux
