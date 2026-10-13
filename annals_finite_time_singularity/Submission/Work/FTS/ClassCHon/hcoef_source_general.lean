import Mathlib.Analysis.PSeries
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.Spaces.Defs
import Submission.Work.Elliptic.Defs
import Submission.Work.FTS.PhiStar.Series.Defs
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.FTS.ClassCHon.sliceMass_continuous
import Submission.Work.FTS.ClassCHon.radGreen_sup_le
import Submission.Work.FTS.PhiStar.Honesty.cmode_modeEnergy_integrable
import Submission.Work.FTS.PhiStar.Honesty.cmode_isLittleO_at_zero
import Submission.Work.FTS.PhiStar.Honesty.continuousOn_cmode_of_hkMem_one
import Submission.Work.FTS.PhiStar.Honesty.eNorm_mul_cmode_sq_le_sliceMass
import Submission.Work.FTS.ClassC.bessel_z
import Submission.Work.FTS.EllipticEst.Cores.HonSlot
import Submission.Work.FTS.H2.ModalSolR.radGreenContinuousOn
import Submission.Work.FTS.PhiStar.Honesty.integrableOn_sq_sEta_of_HkMem
import Submission.Work.FTS.PhiStar.Series.acoeff_zero_of_fstar
import Submission.Work.EllipticEst.ModalSolution.cmode_bessel
import Submission.Work.EllipticEst.ModalSolution.cmode_memLp
import Submission.Work.FTS.EllExist.RadGreenDefs
import Submission.Work.FTS.ClassCHon.Hcoef.cmode_slice_bound
import Submission.Work.FTS.ClassCHon.Hcoef.cmode_L2_bound
import Submission.Work.FTS.ClassCHon.HcoefSplit.radGreen_split_le_gen
import Submission.Work.FTS.ClassCHon.HcoefSplit.hcoef_Lterm_le
import Submission.Work.FTS.ClassCHon.HcoefSplit.hcoef_Bterm_le

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.ClassCHon

/-- **The weighted `ℓ¹`-summability of the modal coefficients of the decaying solution for a
general source** (the `hcoef` input of the level-`0` honesty capstones).

`acoeff α m F = radGreen α m (cmode m F)` is the decaying mode-`m` coefficient of
`psiSeries α F` (`Work.FTS.PhiStar.Series.Defs`).  For a source `F` which is `C^∞` on the open
quadrant, honest at levels `0` and `1`, with `z ∂_z F` honest at level `0`, and whose source
moment `Work.Elliptic.Fstar F` vanishes on `(0,∞)`, the family
`m ↦ ((m : ℝ) + 1) * |acoeff α m F z|` is summable for every `z > 0`.

This is the every-`z` (slicewise) piece of the level-`0` honesty of the modal solution: it is
exactly what `Work.FTS.ClassC.HonestCut.HkMem_zero_psiSeries_of_capstone` consumes.

Proof route (for the prover's convenience; not part of the statement).
Write `c_m := cmode m F`, `q := (2m+5)/α`, `p := 2m/α`.  The explicit Green formula gives
`a_m(z) = radGreen α m c_m z = (α(4m+5))⁻¹ (z^{-q}∫_0^z c_m t^{q-1} + z^{p}∫_z^∞ c_m t^{-p-1})`.
Split the first integral at `z/2` and the second at `2z`:
* on the compact middle `[z/2, 2z]` use `M_z,m := sup_{[z/2,2z]} |c_m|`, which by
  `Work.FTS.PhiStar.Honesty.eNorm_mul_cmode_sq_le_sliceMass` and the *continuity of the
  `σ`-weighted slice mass* (`Work.FTS.ClassCHon.sliceMass_continuous`, whose extra hypothesis is
  `hDz`) is bounded by `√(K_z / eNorm m)` with `K_z := sup_{[z/2,2z]} ∫_θ (F t θ)² sin(2θ)^{-η}`
  — finite for each `z > 0` by continuity on the compact interval;
* the outer halves are bounded by Cauchy–Schwarz against `∫_t (c_m t w t)²` (using
  `(w t)^{-2} ≤ t^4`, valid for all `t > 0`), which by the integrated Bessel inequality
  (`Work.FTS.ClassC.sum_eNorm_cmode_sq_le_HkSq`) is at most `HkSq α 0 F / eNorm m`; the split
  produces the factors `2^{-q}` and `2^{-p}`, i.e. geometric decay in `m`
  (`q ≥ 2m/α ≥ 8m`, `p ≥ 8m`).
With `eNorm m ≥ m` this gives, for `m ≥ 1`, `(m+1)|a_m(z)| ≤ Λ(z)·(m^{-3/2} + 2^{-8m})`, and
every term is summable.  (`m = 0` contributes a single finite term.) -/
theorem hcoef_source_general {α : ℝ} {F : ℝ → ℝ → ℝ}
    (hα : 0 < α) (hα4 : α ≤ 1 / 4)
    (hsm : Work.FTS.EllipticEst.SmoothOpen F)
    (hF0 : Work.Spaces.HkMem α 0 F)
    (hF1 : Work.Spaces.HkMem α 1 F)
    (hDz : Work.Spaces.HkMem α 0 (Work.Spaces.Dz F))
    (hmom : ∀ z : ℝ, 0 < z → Work.Elliptic.Fstar F z = 0) :
    ∀ z : ℝ, 0 < z → Summable (fun m : ℕ =>
      ((m : ℝ) + 1) * |Work.FTS.PhiStar.Series.acoeff α m F z|) := by
  intro z hz
  -- the uniform-on-`[z/2,2z]` bound on the mode coefficients of the source
  obtain ⟨L, hL0, hLbd⟩ := Work.FTS.ClassCHon.Hcoef.cmode_slice_bound hsm hF0 hDz z hz
  -- the two constants of the dominating family
  set β : ℝ := Real.sqrt (Work.Spaces.HkSq α 0 F) with hβdef
  have hβnn : 0 ≤ β := Real.sqrt_nonneg _
  have hβ0 : 0 ≤ β / α := div_nonneg hβnn hα.le
  -- comparison with the summable family `m ↦ L·m^{-3/2} + (β/α)·(1/2)^m`
  refine Summable.of_nonneg_of_le
    (g := fun m : ℕ => ((m : ℝ) + 1) * |Work.FTS.PhiStar.Series.acoeff α m F z|)
    (f := fun m : ℕ => L * (m : ℝ) ^ (-(3 / 2 : ℝ)) + (β / α) * (1 / 2 : ℝ) ^ m)
    (fun m => mul_nonneg (by positivity) (abs_nonneg _)) ?_ ?_
  · intro m
    rcases Nat.eq_zero_or_pos m with hm0 | hpos
    · -- `m = 0`: the coefficient vanishes by the vanishing source moment
      subst hm0
      rw [Work.FTS.PhiStar.Series.acoeff_zero_of_fstar α F hmom z hz, abs_zero]
      have h0 : (0 : ℝ) ^ (-(3 / 2 : ℝ)) = 0 := Real.zero_rpow (by norm_num)
      simp only [Nat.cast_zero, zero_add, mul_zero, pow_zero, mul_one, h0]
      exact hβ0
    · -- `m ≥ 1`: the split Green bound, then the two arithmetic reductions
      have hm : 1 ≤ m := hpos
      have hEpos : 0 < Work.EllipticEst.ModalSolution.eNorm m :=
        Work.EllipticEst.ModalSolution.eNorm_pos m
      obtain ⟨hcint, hcbess⟩ := Work.FTS.ClassCHon.Hcoef.cmode_L2_bound (α := α) hsm hF0 m
      have hcm : MeasureTheory.AEStronglyMeasurable
          (fun t : ℝ => Work.FTS.PhiStar.Series.cmode m F t * Work.Spaces.w t)
          (MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))) :=
        (Work.EllipticEst.ModalSolution.aesm_cmode hsm m).mul
          ((Work.FTS.ClassCHon.Hcoef.continuousOn_w_Ioi.aemeasurable
            measurableSet_Ioi).aestronglyMeasurable)
      have hBs : Real.sqrt (∫ t in Set.Ioi (0 : ℝ),
            (Work.FTS.PhiStar.Series.cmode m F t * Work.Spaces.w t) ^ 2)
          ≤ β / Real.sqrt (Work.EllipticEst.ModalSolution.eNorm m) := by
        have hIle : (∫ t in Set.Ioi (0 : ℝ),
              (Work.FTS.PhiStar.Series.cmode m F t * Work.Spaces.w t) ^ 2)
            ≤ Work.Spaces.HkSq α 0 F / Work.EllipticEst.ModalSolution.eNorm m := by
          rw [le_div_iff₀ hEpos, mul_comm]
          exact hcbess
        calc Real.sqrt (∫ t in Set.Ioi (0 : ℝ),
              (Work.FTS.PhiStar.Series.cmode m F t * Work.Spaces.w t) ^ 2)
            ≤ Real.sqrt (Work.Spaces.HkSq α 0 F / Work.EllipticEst.ModalSolution.eNorm m) :=
              Real.sqrt_le_sqrt hIle
          _ = β / Real.sqrt (Work.EllipticEst.ModalSolution.eNorm m) := by
              rw [hβdef, Real.sqrt_div (Work.Spaces.HkSq_nonneg α 0 F)
                (Work.EllipticEst.ModalSolution.eNorm m)]
      have hsplit := Work.FTS.ClassCHon.HcoefSplit.radGreen_split_le_gen (α := α) hα hα4 hm
        (c := fun t : ℝ => Work.FTS.PhiStar.Series.cmode m F t) (z := z)
        (L := L / Real.sqrt (Work.EllipticEst.ModalSolution.eNorm m))
        (B := β / Real.sqrt (Work.EllipticEst.ModalSolution.eNorm m))
        hz (div_nonneg hL0 (Real.sqrt_nonneg _)) (div_nonneg hβnn (Real.sqrt_nonneg _))
        (fun t ht => hLbd m t ht) hcint hcm hBs
      have hLterm := Work.FTS.ClassCHon.HcoefSplit.hcoef_Lterm_le (α := α) (L := L)
        hα hα4 hL0 hm
      have hBterm := Work.FTS.ClassCHon.HcoefSplit.hcoef_Bterm_le (α := α) (β := β)
        hα hα4 hβnn hm
      calc ((m : ℝ) + 1) * |Work.FTS.PhiStar.Series.acoeff α m F z|
          = ((m : ℝ) + 1) * |Work.FTS.PhiStar.Radial.radGreen α m
              (fun t : ℝ => Work.FTS.PhiStar.Series.cmode m F t) z| := rfl
        _ ≤ ((m : ℝ) + 1) * (Work.FTS.EllExist.rgK α m *
              ((L / Real.sqrt (Work.EllipticEst.ModalSolution.eNorm m))
                * (1 / Work.FTS.EllExist.rgQ α m + 1 / Work.FTS.EllExist.rgP α m)
              + (β / Real.sqrt (Work.EllipticEst.ModalSolution.eNorm m))
                * ((2 : ℝ) ^ (-(Work.FTS.EllExist.rgQ α m))
                      / Real.sqrt (2 * Work.FTS.EllExist.rgQ α m - 1)
                    + (2 : ℝ) ^ (-(Work.FTS.EllExist.rgP α m))
                      / Real.sqrt (2 * Work.FTS.EllExist.rgP α m - 3)))) :=
            mul_le_mul_of_nonneg_left hsplit (by positivity)
        _ = ((m : ℝ) + 1) * (Work.FTS.EllExist.rgK α m *
              ((L / Real.sqrt (Work.EllipticEst.ModalSolution.eNorm m))
                * (1 / Work.FTS.EllExist.rgQ α m + 1 / Work.FTS.EllExist.rgP α m)))
            + ((m : ℝ) + 1) * (Work.FTS.EllExist.rgK α m *
              ((β / Real.sqrt (Work.EllipticEst.ModalSolution.eNorm m))
                * ((2 : ℝ) ^ (-(Work.FTS.EllExist.rgQ α m))
                      / Real.sqrt (2 * Work.FTS.EllExist.rgQ α m - 1)
                    + (2 : ℝ) ^ (-(Work.FTS.EllExist.rgP α m))
                      / Real.sqrt (2 * Work.FTS.EllExist.rgP α m - 3)))) := by ring
        _ ≤ L * (m : ℝ) ^ (-(3 / 2 : ℝ)) + (β / α) * (1 / 2 : ℝ) ^ m :=
            add_le_add hLterm hBterm
  · -- the dominating family is summable
    have hsum1 : Summable (fun m : ℕ => (m : ℝ) ^ (-(3 / 2 : ℝ))) := by
      have h0 : Summable (fun m : ℕ => ((m : ℝ) ^ (3 / 2 : ℝ))⁻¹) :=
        Real.summable_nat_rpow_inv.mpr (by norm_num)
      convert h0 using 1
      ext m
      rw [Real.rpow_neg (Nat.cast_nonneg m)]
    have hsum2 : Summable (fun m : ℕ => (1 / 2 : ℝ) ^ m) :=
      summable_geometric_of_norm_lt_one (by norm_num)
    exact (hsum1.mul_left L).add (hsum2.mul_left (β / α))

end Work.FTS.ClassCHon
