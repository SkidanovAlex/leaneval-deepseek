/-
Copyright: work module for the Elgindi finite-time singularity project.

# `PkgJets.pinningBoundClean` — the `ℋ⁰`-bound on the pinned slot `Φ̃/cos θ`

This is a *clash-free* copy of `PkgJets.pinningBound`.  The sibling module `PkgJets/pinningBound.lean`
proves the same claim, but it imports `PkgJets/hkZero.lean`, which declares
`Work.FTS_EllLimOK.PkgJets.HkIntegrand_zero_le` with a *different* signature from the same-named
declaration in `PkgJets/thetaBound.lean` (also proved, axiom-clean).  Importing `pinningBound` and
`thetaBound` together is therefore impossible (name clash), yet a consumer (`PkgJets/boxDataD_uniform`)
needs both claims.  This module is importable *together with* `PkgJets/thetaBound.lean`: it does
**not** import `PkgJets/hkZero.lean`; the two facts of `hkZero` are copied below under the fresh
names `HkIntegrand_zero_eq_pin` / `HkIntegrand_zero_le_pin`, and the proof of
`PkgJets/pinningBound.lean` is copied verbatim (with `thetaHardy` renamed to `thetaHardyClean` so
that this module may also be imported alongside `PkgJets/pinningBound.lean` itself).

From the fully repaired elliptic package `HasPkgE α Ce E` — in particular from

* the pinning field `PkgCos` (`Φ̃/cos θ ∈ ℋ⁰`, which kills the homogeneous mode
  `z^{-3/α}/cos θ` of the elliptic problem), and
* the level-`6` estimate on the coefficient slot `Vop Φ̃` of `EllPkgK`,

the slot `Φ̃/cos θ` is controlled in `ℋ⁰` by the source: there is a constant `C`, *independent of
`g` and `E`*, with

`|Φ̃/cos θ|²_{ℋ⁰} ≤ C·(1 + |g|_{ℋ⁶})²`,   `Φ̃ = PhiTil α g (E g)`.

The proof is pointwise in `z`: the weighted Hardy inequality `thetaHardyClean` bounds the
`z`-slice integral `∫_θ (Φ̃/cos θ)²·sin(2θ)^{-η}` by `∫_θ (Vop Φ̃)²·sin(2θ)^{-η}`, with the
same constant for every `z`; integrating in `z` against the radial weight `w(z)²` and comparing
with the `ℋ⁶`-integrand of `Vop Φ̃` (whose `i = 0` summand is exactly
`w(z)²·(Vop Φ̃)²·sin(2θ)^{-η}`) gives the bound.
-/
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Submission.Work.FTS_EllLimOK.PkgRepair
import Submission.Work.FTS_EllLimOK.Pinning.hpin_of_hasPkgD
import Submission.Work.FTS_EllLimOK.PkgJets.pinHardy
import Submission.Work.FTS_EllLimOK.PkgJets.pinWeights
import Submission.Work.FTS_EllLimOK.PkgJets.cosWeightPrim_sq_le
import Submission.Work.FTS_EllLimOK.PkgJets.cosWeightTail_le
import Submission.Work.FTS_EllLimOK.PkgJets.integral_Icc_le_of_subinterval_le
import Submission.Work.FTS.GalFields.Tail.FrBoxAux

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS_EllLimOK.PkgJets

open scoped Real Topology
open MeasureTheory Set Filter

set_option autoImplicit false
set_option maxHeartbeats 800000

/-! ## §0  The level-`0` `ℋ`-integrand (copies of `PkgJets.hkZero`, under fresh names)

Two elementary facts about `Work.Spaces.HkIntegrand` at level `0`, used to transfer the
per-slice weighted Hardy inequality of `PkgJets.pinHardy` to the `ℋ⁰`-norm of the slot
`Φ̃/cos θ`.  They are the facts of `PkgJets/hkZero.lean`, copied verbatim under the names
`HkIntegrand_zero_eq_pin` / `HkIntegrand_zero_le_pin` so that this module does not need to
import `hkZero` (whose `HkIntegrand_zero_le` clashes with `PkgJets/thetaBound.lean`). -/

theorem HkIntegrand_zero_eq_pin (α : ℝ) (f : ℝ → ℝ → ℝ) (z θ : ℝ)
    (hθ : θ ∈ Work.Spaces.Iθ) :
    Work.Spaces.HkIntegrand α 0 f z θ = (Work.Spaces.w z) ^ 2 * ((f z θ) ^ 2 * wNu θ) := by
  have h1 : Work.Spaces.HkIntegrand α 0 f z θ
      = (f z θ * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2 := by
    rw [Work.Spaces.HkIntegrand]
    simp
  have hs : 0 ≤ Real.sin (2 * θ) := sin_two_nonneg_of_mem_Iθ hθ
  rcases eq_or_ne z 0 with hz | hz
  · -- `w 0 = 0`: both sides vanish
    subst hz
    have hw0 : Work.Spaces.w 0 = 0 := by simp [Work.Spaces.w]
    rw [h1, hw0, zero_div, mul_zero, wNu]
    simp
  · rcases eq_or_ne (Real.sin (2 * θ)) 0 with h0 | h0
    · -- the endpoint `sin(2θ) = 0`: both sides vanish
      have hz1 : (0 : ℝ) ^ (Work.Spaces.eta / 2) = 0 :=
        Real.zero_rpow (by norm_num [Work.Spaces.eta])
      have hz2 : (0 : ℝ) ^ (-(Work.Spaces.eta)) = 0 :=
        Real.zero_rpow (by norm_num [Work.Spaces.eta])
      rw [h1, wNu, h0, hz1, hz2]
      ring
    · have hpos : 0 < Real.sin (2 * θ) := lt_of_le_of_ne hs (Ne.symm h0)
      have hkey : ((Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2)) ^ (2 : ℕ)
          = (Real.sin (2 * θ)) ^ (Work.Spaces.eta) := by
        rw [sq, ← Real.rpow_add hpos,
          show Work.Spaces.eta / 2 + Work.Spaces.eta / 2 = Work.Spaces.eta by ring]
      rw [h1, wNu, mul_pow, div_pow, hkey, div_eq_mul_inv,
        show ((Real.sin (2 * θ)) ^ (Work.Spaces.eta))⁻¹
          = (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) from (Real.rpow_neg hpos.le _).symm]
      ring

theorem HkIntegrand_zero_le_pin (α : ℝ) (k : ℕ) (f : ℝ → ℝ → ℝ) (z θ : ℝ) :
    Work.Spaces.HkIntegrand α 0 f z θ ≤ Work.Spaces.HkIntegrand α k f z θ := by
  rw [Work.Spaces.HkIntegrand, Work.Spaces.HkIntegrand]
  have h2 : (∑ i ∈ Finset.range 1, ∑ j ∈ Finset.range 1,
      (if 1 ≤ i ∧ i + j ≤ 0 then (Work.Spaces.mixed j i f z θ * Work.Spaces.Wt α z θ) ^ 2
        else 0)) = 0 := by
    refine Finset.sum_eq_zero fun i hi => Finset.sum_eq_zero fun j hj => ?_
    have this : ¬ (1 ≤ i ∧ i + j ≤ 0) := by omega
    rw [if_neg this]
  rw [h2, add_zero]
  refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg
    (Finset.range_subset_range.mpr (Nat.le_add_left 1 k)) (fun i _ _ => sq_nonneg _)) ?_
  exact le_add_of_nonneg_right (Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => by
    split_ifs with h
    · exact sq_nonneg _
    · exact le_refl 0)

/-! ## §1  The angular weighted Hardy inequality -/

/-- The angular weighted Hardy inequality, with the constants supplied by the two numerical
lemmas (`cosWeightPrim_sq_le`, `cosWeightTail_le`). -/
theorem thetaHardyClean :
    ∃ K : ℝ, 0 < K ∧ ∀ (Ψ : ℝ → ℝ → ℝ) (z : ℝ), 0 < z →
      Work.FTS.EllipticEst.SmoothOpen Ψ →
      Filter.Tendsto (fun s => Real.cos s * Ψ z s) (𝓝[<] (π / 2)) (𝓝 0) →
      MeasureTheory.IntegrableOn (fun θ => (Ψ z θ / Real.cos θ) ^ 2 * wNu θ) Work.Spaces.Iθ →
      MeasureTheory.IntegrableOn (fun θ => (pinV Ψ z θ) ^ 2 * wNu θ) Work.Spaces.Iθ →
      (∫ θ in Work.Spaces.Iθ, (Ψ z θ / Real.cos θ) ^ 2 * wNu θ)
        ≤ K * (∫ θ in Work.Spaces.Iθ, (pinV Ψ z θ) ^ 2 * wNu θ) := by
  obtain ⟨C₁, hC₁, hLamB⟩ := cosWeightPrim_sq_le
  obtain ⟨C₂, hC₂, hTailB⟩ := cosWeightTail_le
  refine ⟨4 * (C₁ + C₂), by linarith, ?_⟩
  intro Ψ z hz hsm hpin hL hR
  exact thetaHardy_of_bounds hC₁ hC₂ hLamB hTailB Ψ z hz hsm hpin hL hR

/-! ## §2  The pinning bound -/

theorem pinningBoundClean {α Ce : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ (E : Work.FTS.Galerkin.Fn →ₗ[ℝ] Work.FTS.Galerkin.Fn),
      Work.FTS_EllLimOK.HasPkgE α Ce E → ∀ g : Work.FTS.Galerkin.Fn,
      Work.FTS.ClassC.ClassC α g →
      Work.Spaces.HkMem α 0
        (fun z θ => Work.Construction.PhiTil α g (E g) z θ / Real.cos θ) ∧
      Work.Spaces.HkSq α 0
        (fun z θ => Work.Construction.PhiTil α g (E g) z θ / Real.cos θ)
        ≤ C * (1 + Work.FTS.StrongGlobal.Xn6 α g) ^ 2 := by
  obtain ⟨K, hKpos, hHardy⟩ := thetaHardyClean
  refine ⟨K * Ce ^ 2 + 1, by positivity, ?_⟩
  intro E hE g hg
  set Ψ : ℝ → ℝ → ℝ := fun z θ => Work.Construction.PhiTil α g (E g) z θ with hΨ
  obtain ⟨hGo, hK6⟩ := hE.toHasPkgD.toHasPkg g hg
  refine ⟨hE.toHasPkgD.cos g hg, ?_⟩
  have hsm : Work.FTS.EllipticEst.SmoothOpen Ψ :=
    Work.FTS.GalFields.RHS.Sharp.smoothOpen_PhiTil hα hGo
  have hsmdiv : Work.FTS.EllipticEst.SmoothOpen (fun z θ => Ψ z θ / Real.cos θ) :=
    Work.FTS_EllLimOK.Pinning.smoothOpen_div_cos hsm
  have hcos_mem : Work.Spaces.HkMem α 0 (fun z θ => Ψ z θ / Real.cos θ) :=
    hE.toHasPkgD.cos g hg
  have hVsmooth : Work.FTS.EllipticEst.SmoothOpen (fun z θ => pinV Ψ z θ) := hK6.V.1.1
  have hV6 : Work.Spaces.HkMem α 6 (fun z θ => pinV Ψ z θ) := hK6.V.1.2
  have hV0 : Work.Spaces.HkMem α 0 (fun z θ => pinV Ψ z θ) :=
    Work.FTS.OpenPkg.HkMem_mono_open hVsmooth 0 (by norm_num) hV6
  have hVnorm : Work.Spaces.HkNorm α 6 (fun z θ => pinV Ψ z θ)
      ≤ Ce * Work.FTS.StrongGlobal.Xn6 α g := hK6.V.2
  have hpin := Work.FTS_EllLimOK.Pinning.hpin_of_hasPkgD hα hα1 hE.toHasPkgD g hg
  -- the pointwise-in-`z` step
  have hstep : ∀ z ∈ Work.Spaces.Iz,
      (Work.Spaces.w z) ^ 2 * (∫ θ in Work.Spaces.Iθ, (Ψ z θ / Real.cos θ) ^ 2 * wNu θ)
        ≤ K * (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 6
            (fun z θ => pinV Ψ z θ) z θ) := by
    intro z hz
    rcases eq_or_ne z 0 with hz0 | hz0
    · subst hz0
      have hw0 : Work.Spaces.w 0 = 0 := by simp [Work.Spaces.w]
      rw [hw0, zero_pow (by norm_num : (2 : ℕ) ≠ 0), zero_mul]
      exact mul_nonneg hKpos.le (MeasureTheory.integral_nonneg
        (fun θ => Work.Spaces.HkIntegrand_nonneg α 6 _ 0 θ))
    · have hzpos : 0 < z := lt_of_le_of_ne hz (Ne.symm hz0)
      have hLint := Work.FTS_EllLimOK.Pinning.integrableOn_sq_rpow_of_HkMem hsmdiv hcos_mem z hzpos
      have hRint := Work.FTS_EllLimOK.Pinning.integrableOn_sq_rpow_of_HkMem hVsmooth hV0 z hzpos
      have hH := hHardy Ψ z hzpos hsm (hpin z hzpos) hLint hRint
      have h1 : (Work.Spaces.w z) ^ 2
            * (∫ θ in Work.Spaces.Iθ, (Ψ z θ / Real.cos θ) ^ 2 * wNu θ)
          ≤ (Work.Spaces.w z) ^ 2
            * (K * (∫ θ in Work.Spaces.Iθ, (pinV Ψ z θ) ^ 2 * wNu θ)) :=
        mul_le_mul_of_nonneg_left hH (sq_nonneg _)
      have h2 : (Work.Spaces.w z) ^ 2 * (∫ θ in Work.Spaces.Iθ, (pinV Ψ z θ) ^ 2 * wNu θ)
          ≤ ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 6 (fun z θ => pinV Ψ z θ) z θ := by
        rw [← MeasureTheory.integral_const_mul]
        refine MeasureTheory.integral_mono_of_nonneg ?_ (hV6.1 z (Set.mem_Ici.mpr hzpos.le)) ?_
        · exact (MeasureTheory.ae_restrict_iff' measurableSet_Icc).mpr
            (Filter.Eventually.of_forall fun θ hθ =>
              mul_nonneg (sq_nonneg _) (mul_nonneg (sq_nonneg _) (wNu_nonneg hθ)))
        · exact (MeasureTheory.ae_restrict_iff' measurableSet_Icc).mpr
            (Filter.Eventually.of_forall fun θ hθ =>
              le_of_eq_of_le
                (HkIntegrand_zero_eq_pin α (fun z θ => pinV Ψ z θ) z θ hθ).symm
                (HkIntegrand_zero_le_pin α 6 (fun z θ => pinV Ψ z θ) z θ))
      calc (Work.Spaces.w z) ^ 2 * (∫ θ in Work.Spaces.Iθ, (Ψ z θ / Real.cos θ) ^ 2 * wNu θ)
          ≤ (Work.Spaces.w z) ^ 2
              * (K * (∫ θ in Work.Spaces.Iθ, (pinV Ψ z θ) ^ 2 * wNu θ)) := h1
        _ = K * ((Work.Spaces.w z) ^ 2
              * (∫ θ in Work.Spaces.Iθ, (pinV Ψ z θ) ^ 2 * wNu θ)) := by ring
        _ ≤ K * (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 6
              (fun z θ => pinV Ψ z θ) z θ) := mul_le_mul_of_nonneg_left h2 hKpos.le
  -- the identification of the two sides
  have hId : Work.Spaces.HkSq α 0 (fun z θ => Ψ z θ / Real.cos θ)
      = ∫ z in Work.Spaces.Iz, (Work.Spaces.w z) ^ 2
          * (∫ θ in Work.Spaces.Iθ, (Ψ z θ / Real.cos θ) ^ 2 * wNu θ) := by
    rw [Work.Spaces.HkSq]
    refine MeasureTheory.setIntegral_congr_fun measurableSet_Ici (fun z _ => ?_)
    rw [show (∫ θ in Work.Spaces.Iθ,
          Work.Spaces.HkIntegrand α 0 (fun z θ => Ψ z θ / Real.cos θ) z θ)
        = ∫ θ in Work.Spaces.Iθ, (Work.Spaces.w z) ^ 2
            * ((Ψ z θ / Real.cos θ) ^ 2 * wNu θ) from
      MeasureTheory.setIntegral_congr_fun measurableSet_Icc
        (fun θ hθ => HkIntegrand_zero_eq_pin α (fun z θ => Ψ z θ / Real.cos θ) z θ hθ)]
    rw [MeasureTheory.integral_const_mul]
  -- the `z`-integration
  have hMain : (∫ z in Work.Spaces.Iz, (Work.Spaces.w z) ^ 2
        * (∫ θ in Work.Spaces.Iθ, (Ψ z θ / Real.cos θ) ^ 2 * wNu θ))
      ≤ K * Work.Spaces.HkSq α 6 (fun z θ => pinV Ψ z θ) := by
    have hInt : MeasureTheory.Integrable
        (fun z => K * ∫ θ in Work.Spaces.Iθ,
          Work.Spaces.HkIntegrand α 6 (fun z θ => pinV Ψ z θ) z θ)
        (MeasureTheory.volume.restrict Work.Spaces.Iz) := hV6.2.const_mul K
    have hmono := MeasureTheory.integral_mono_of_nonneg
      (μ := MeasureTheory.volume.restrict Work.Spaces.Iz)
      (f := fun z => (Work.Spaces.w z) ^ 2
        * (∫ θ in Work.Spaces.Iθ, (Ψ z θ / Real.cos θ) ^ 2 * wNu θ))
      (g := fun z => K * ∫ θ in Work.Spaces.Iθ,
        Work.Spaces.HkIntegrand α 6 (fun z θ => pinV Ψ z θ) z θ) ?_ hInt ?_
    · rw [MeasureTheory.integral_const_mul] at hmono
      rw [Work.Spaces.HkSq]
      exact hmono
    · exact (MeasureTheory.ae_restrict_iff' measurableSet_Ici).mpr
        (Filter.Eventually.of_forall fun z _ =>
          mul_nonneg (sq_nonneg _) (MeasureTheory.integral_nonneg_of_ae
            ((MeasureTheory.ae_restrict_iff' measurableSet_Icc).mpr
              (Filter.Eventually.of_forall fun θ hθ =>
                mul_nonneg (sq_nonneg _) (wNu_nonneg hθ)))))
    · exact (MeasureTheory.ae_restrict_iff' measurableSet_Ici).mpr
        (Filter.Eventually.of_forall fun z hz => hstep z hz)
  -- the conclusion
  have hSq6 : Work.Spaces.HkSq α 6 (fun z θ => pinV Ψ z θ)
      = (Work.Spaces.HkNorm α 6 (fun z θ => pinV Ψ z θ)) ^ 2 :=
    Work.FTS.GalFields.Tail.HkSq_eq_HkNorm_sq α 6 _
  have hXn : 0 ≤ Work.FTS.StrongGlobal.Xn6 α g := Work.Spaces.HkNorm_nonneg α 6 g
  calc Work.Spaces.HkSq α 0 (fun z θ => Ψ z θ / Real.cos θ)
      = ∫ z in Work.Spaces.Iz, (Work.Spaces.w z) ^ 2
          * (∫ θ in Work.Spaces.Iθ, (Ψ z θ / Real.cos θ) ^ 2 * wNu θ) := hId
    _ ≤ K * Work.Spaces.HkSq α 6 (fun z θ => pinV Ψ z θ) := hMain
    _ = K * (Work.Spaces.HkNorm α 6 (fun z θ => pinV Ψ z θ)) ^ 2 := by rw [hSq6]
    _ ≤ K * (Ce * Work.FTS.StrongGlobal.Xn6 α g) ^ 2 :=
        mul_le_mul_of_nonneg_left
          (pow_le_pow_left₀ (Work.Spaces.HkNorm_nonneg α 6 (fun z θ => pinV Ψ z θ)) hVnorm 2)
          hKpos.le
    _ = K * Ce ^ 2 * (Work.FTS.StrongGlobal.Xn6 α g) ^ 2 := by ring
    _ ≤ (K * Ce ^ 2 + 1) * (1 + Work.FTS.StrongGlobal.Xn6 α g) ^ 2 := by
        have hKnn : 0 ≤ K * Ce ^ 2 + 1 := by positivity
        have hsq : (Work.FTS.StrongGlobal.Xn6 α g) ^ 2
            ≤ (1 + Work.FTS.StrongGlobal.Xn6 α g) ^ 2 := by nlinarith
        calc K * Ce ^ 2 * (Work.FTS.StrongGlobal.Xn6 α g) ^ 2
            = (K * Ce ^ 2) * (Work.FTS.StrongGlobal.Xn6 α g) ^ 2 := by ring
          _ ≤ (K * Ce ^ 2 + 1) * (Work.FTS.StrongGlobal.Xn6 α g) ^ 2 := by
              have := sq_nonneg (Work.FTS.StrongGlobal.Xn6 α g); nlinarith
          _ ≤ (K * Ce ^ 2 + 1) * (1 + Work.FTS.StrongGlobal.Xn6 α g) ^ 2 :=
              mul_le_mul_of_nonneg_left hsq hKnn

end Work.FTS_EllLimOK.PkgJets
