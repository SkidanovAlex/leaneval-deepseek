import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.Prod
import Submission.Work.Spaces.Defs
import Submission.Work.Elliptic.Defs
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.FTS.EllipticEst.ae_restrict_Icc_of_forall_Ioo
import Submission.Work.FTS.EllipticEst.aesm_uncurry_restrict_open
import Submission.Work.FTS.EllipticEst.integrable_prod_ae
import Submission.Work.FTS.EllipticEst.remov.SourceBound.pzSliceFtcBound

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!

# Integrability of `∂_zΨ · sinθcos²θ` on the radial rectangle `(r, z₁] × Iθ`

This is the Fubini/Tonelli bookkeeping step that turns an *honest* slice integrability of the
second `z`-derivative of the source into joint integrability of the first `z`-derivative against
the angular weight `sinCos2 θ = sinθ cos²θ`.

The hypotheses are exactly the two "honest" consequences of the weak positivity class produced
by the sibling target `remov/hkMemSliceAbsIntegrable`:

* `hsl` : every angular slice `θ ↦ |∂_z²Ψ(z,θ)| sinθcos²θ`, `z ∈ [r,z₁]`, is integrable;
* `hFint` : the iterated integral `z ↦ ∫_{Iθ} |∂_z²Ψ(z,θ)| sinθcos²θ` is integrable on `[r,z₁]`.

(Without `hsl`/`hFint` the statement would be *false*: the Bochner integral of a non-integrable
nonnegative function is `0`, so a hypothesis stated with such an integral carries no information —
see `NOTES_pzMulSinCos2RectIntegrable_FALSE.md` for the machine-checked counterexample of the
naive form.)

The proof:

1. `Fubini–Tonelli` (`Work.FTS.EllipticEst.integrable_prod_ae`) applied to the *nonnegative*
   source `g z θ = |∂_z²Ψ(z,θ)| sinθcos²θ` gives joint integrability of `g` on `(r,z₁] × Iθ`;
   a.e. strong measurability comes from continuity on the open quadrant
   (`aesm_uncurry_restrict_open`), the slice hypothesis from `hsl` and the iterated-integral
   hypothesis from `hFint` (up to the null difference between `Icc` and `Ioc`).
2. `Integrable.integral_prod_right` then makes `θ ↦ ∫_r^{z₁} ‖∂_z²Ψ(s,θ) sinθcos²θ‖ ds`
   integrable on `Iθ`.
3. The elementary slice FTC bound `remov/SourceBound/pzSliceFtcBound` bounds the weighted first
   `z`-derivative by `‖∂_zΨ(r,θ) sinθcos²θ‖ + ∫_r^{z₁} ‖∂_z²Ψ(s,θ) sinθcos²θ‖ ds` for every
   `z ∈ (r,z₁]` and every interior angle, and the first summand is integrable by `hBr`.  Hence
   the slice `θ ↦ ∂_zΨ(z,θ) sinθcos²θ` is integrable (`Integrable.mono'`) for *every*
   `z ∈ (r,z₁]`.
4. The same dominating function is independent of `z` and integrable in `θ`, so the outer
   integral `z ↦ ∫_θ ‖∂_zΨ(z,θ) sinθcos²θ‖ dθ` is bounded by a constant, hence integrable on the
   bounded interval `(r,z₁]`; `integrable_prod_iff` concludes.

-/

namespace Work.FTS.EllipticEst.remov

open scoped Real Topology
open MeasureTheory Set Filter

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option linter.style.haveILetI false

private theorem sinCos2_nonneg_Iθ {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) :
    0 ≤ Work.Elliptic.sinCos2 θ := by
  rw [Work.Spaces.Iθ, Set.mem_Icc] at hθ
  have hs : 0 ≤ Real.sin θ := Real.sin_nonneg_of_nonneg_of_le_pi hθ.1 (by linarith [Real.pi_pos])
  have hc : 0 ≤ Real.cos θ := Real.cos_nonneg_of_neg_pi_div_two_le_of_le (by linarith) hθ.2
  rw [Work.Elliptic.sinCos2]
  positivity

private theorem continuous_sinCos2 : Continuous Work.Elliptic.sinCos2 :=
  Real.continuous_sin.mul (Real.continuous_cos.pow 2)

theorem pzSinCos2_rectIntegrable {Ψ : ℝ → ℝ → ℝ}
    (hsm : Work.FTS.EllipticEst.SmoothOpen Ψ)
    {r z₁ : ℝ} (hr : 0 < r) (hrz : r < z₁)
    (hBr : MeasureTheory.Integrable
      (fun θ : ℝ => Work.Spaces.pz Ψ r θ * Work.Elliptic.sinCos2 θ)
      (MeasureTheory.volume.restrict Work.Spaces.Iθ))
    (hsl : ∀ z ∈ Set.Icc r z₁, MeasureTheory.IntegrableOn
      (fun θ : ℝ => |Work.Spaces.pzIter 2 Ψ z θ| * Work.Elliptic.sinCos2 θ)
      Work.Spaces.Iθ)
    (hFint : MeasureTheory.IntegrableOn
      (fun s : ℝ => ∫ θ in Work.Spaces.Iθ,
        |Work.Spaces.pzIter 2 Ψ s θ| * Work.Elliptic.sinCos2 θ)
      (Set.Icc r z₁)) :
    MeasureTheory.Integrable
      (Function.uncurry (fun z θ : ℝ => Work.Spaces.pz Ψ z θ * Work.Elliptic.sinCos2 θ))
      ((MeasureTheory.volume.restrict (Set.Ioc r z₁)).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ))
  := by
  -- `(r,z₁]` and `[r,z₁]` carry the same measure (they differ by the null set `{r}`).
  have hIocIcc : MeasureTheory.volume.restrict (Set.Ioc r z₁)
      = MeasureTheory.volume.restrict (Set.Icc r z₁) :=
    MeasureTheory.Measure.restrict_congr_set MeasureTheory.Ioc_ae_eq_Icc
  -- the radial measure of the bounded interval `(r,z₁]` is finite
  haveI hfinμ : MeasureTheory.IsFiniteMeasure (MeasureTheory.volume.restrict (Set.Ioc r z₁)) :=
    ⟨by rw [MeasureTheory.Measure.restrict_apply MeasurableSet.univ, Set.univ_inter,
        Real.volume_Ioc]
        exact ENNReal.ofReal_lt_top⟩
  -- the angular weight is nonnegative on `Iθ`
  have hsrc_nn : ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ),
      0 ≤ Work.Elliptic.sinCos2 θ :=
    MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc
      (fun θ hθ => sinCos2_nonneg_Iθ hθ)
  -- the angular slices of the source are a.e. strongly measurable
  have hcont_src : ContinuousOn
      (fun p : ℝ × ℝ => |Work.Spaces.pzIter 2 Ψ p.1 p.2| * Work.Elliptic.sinCos2 p.2)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)) :=
    ((hsm.pzIter 2).continuousOn.abs).mul
      (continuous_sinCos2.comp continuous_snd).continuousOn
  -- continuity of the uncurried integrand on the open quadrant
  have hcont_pz : ContinuousOn
      (fun p : ℝ × ℝ => Work.Spaces.pz Ψ p.1 p.2 * Work.Elliptic.sinCos2 p.2)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)) :=
    ((hsm.pz).continuousOn).mul
      (continuous_sinCos2.comp continuous_snd).continuousOn
  -- ## Step 1: joint integrability of the nonnegative second-derivative source
  have hgInt : MeasureTheory.Integrable
      (Function.uncurry
        (fun z θ : ℝ => |Work.Spaces.pzIter 2 Ψ z θ| * Work.Elliptic.sinCos2 θ))
      ((MeasureTheory.volume.restrict (Set.Ioc r z₁)).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)) := by
    refine Work.FTS.EllipticEst.integrable_prod_ae ?_ ?_ ?_ ?_
    · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioc] with z hz
      exact MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc
        (fun θ hθ => mul_nonneg (abs_nonneg _) (sinCos2_nonneg_Iθ hθ))
    · exact Work.FTS.EllipticEst.aesm_uncurry_restrict_open _ hcont_src (le_of_lt hr)
    · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioc] with z hz
      exact hsl z ⟨le_of_lt hz.1, hz.2⟩
    · rw [hIocIcc]
      simpa only [MeasureTheory.IntegrableOn] using hFint
  -- ## Step 2: the radial integral of the second derivative is integrable in `θ`
  have hIntZ : MeasureTheory.Integrable
      (fun θ : ℝ => (∫ z in Set.Ioc r z₁, |Work.Spaces.pzIter 2 Ψ z θ|)
        * Work.Elliptic.sinCos2 θ)
      (MeasureTheory.volume.restrict Work.Spaces.Iθ) := by
    have hraw := hgInt.integral_prod_right
    refine hraw.congr (Filter.Eventually.of_forall (fun θ => ?_))
    show (∫ z in Set.Ioc r z₁, |Work.Spaces.pzIter 2 Ψ z θ| * Work.Elliptic.sinCos2 θ)
      = (∫ z in Set.Ioc r z₁, |Work.Spaces.pzIter 2 Ψ z θ|) * Work.Elliptic.sinCos2 θ
    rw [MeasureTheory.integral_mul_const]
  have hA2 : MeasureTheory.Integrable
      (fun θ : ℝ => ∫ s in r..z₁, ‖Work.Spaces.pzIter 2 Ψ s θ * Work.Elliptic.sinCos2 θ‖)
      (MeasureTheory.volume.restrict Work.Spaces.Iθ) := by
    refine hIntZ.congr ?_
    filter_upwards [hsrc_nn] with θ hθ
    show (∫ z in Set.Ioc r z₁, |Work.Spaces.pzIter 2 Ψ z θ|) * Work.Elliptic.sinCos2 θ
      = ∫ s in r..z₁, ‖Work.Spaces.pzIter 2 Ψ s θ * Work.Elliptic.sinCos2 θ‖
    rw [intervalIntegral.integral_of_le hrz.le]
    rw [← MeasureTheory.integral_mul_const]
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun z => ?_))
    show |Work.Spaces.pzIter 2 Ψ z θ| * Work.Elliptic.sinCos2 θ
      = ‖Work.Spaces.pzIter 2 Ψ z θ * Work.Elliptic.sinCos2 θ‖
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hθ]
  -- ## Step 3: the dominating angular function is integrable
  have hA1 : MeasureTheory.Integrable
      (fun θ : ℝ => ‖Work.Spaces.pz Ψ r θ * Work.Elliptic.sinCos2 θ‖)
      (MeasureTheory.volume.restrict Work.Spaces.Iθ) := hBr.norm
  have hH : MeasureTheory.Integrable
      (fun θ : ℝ => ‖Work.Spaces.pz Ψ r θ * Work.Elliptic.sinCos2 θ‖
        + ∫ s in r..z₁, ‖Work.Spaces.pzIter 2 Ψ s θ * Work.Elliptic.sinCos2 θ‖)
      (MeasureTheory.volume.restrict Work.Spaces.Iθ) := hA1.add hA2
  -- ## Step 4: the slice FTC bound, a.e. in the angle
  have hbound : ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ),
      ∀ z ∈ Set.Ioc r z₁,
        ‖Work.Spaces.pz Ψ z θ * Work.Elliptic.sinCos2 θ‖
          ≤ ‖Work.Spaces.pz Ψ r θ * Work.Elliptic.sinCos2 θ‖
              + ∫ s in r..z₁, ‖Work.Spaces.pzIter 2 Ψ s θ * Work.Elliptic.sinCos2 θ‖ := by
    filter_upwards [Work.FTS.EllipticEst.ae_restrict_Icc_of_forall_Ioo
      (p := fun θ : ℝ => θ ∈ Set.Ioo (0 : ℝ) (π / 2)) (fun θ hθ => hθ)] with θ hθ
    intro z hz
    exact Work.FTS.EllipticEst.remov.SourceBound.pzSliceFtcBound hr hrz.le
      ⟨le_rfl, hrz.le⟩ hsm hz hθ
  -- ## Step 5: every angular slice of `∂_zΨ · sinCos2` in the rectangle is integrable
  have hsliceAll : ∀ z ∈ Set.Ioc r z₁, MeasureTheory.Integrable
      (fun θ : ℝ => Work.Spaces.pz Ψ z θ * Work.Elliptic.sinCos2 θ)
      (MeasureTheory.volume.restrict Work.Spaces.Iθ) := by
    intro z hz
    have hzpos : 0 < z := lt_trans hr hz.1
    refine MeasureTheory.Integrable.mono' hH ?_ ?_
    · refine Work.Spaces.aesm_slice_of_continuousOn_Qd
        (fun p : ℝ × ℝ => Work.Spaces.pz Ψ p.1 p.2 * Work.Elliptic.sinCos2 p.2)
        hcont_pz hzpos
    · exact hbound.mono (fun θ hθ => hθ z hz)
  -- ## Step 6: a.e. strong measurability of the uncurried integrand
  have hAESM : MeasureTheory.AEStronglyMeasurable
      (Function.uncurry (fun z θ : ℝ => Work.Spaces.pz Ψ z θ * Work.Elliptic.sinCos2 θ))
      ((MeasureTheory.volume.restrict (Set.Ioc r z₁)).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)) :=
    Work.FTS.EllipticEst.aesm_uncurry_restrict_open _ hcont_pz (le_of_lt hr)
  -- ## Step 7: the outer integral is integrable (bounded by a constant on a bounded interval)
  have hout : MeasureTheory.Integrable
      (fun z : ℝ => ∫ θ, ‖Work.Spaces.pz Ψ z θ * Work.Elliptic.sinCos2 θ‖
        ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ))
      (MeasureTheory.volume.restrict (Set.Ioc r z₁)) := by
    refine MeasureTheory.Integrable.mono' (MeasureTheory.integrable_const (α := ℝ)
      (∫ θ, (‖Work.Spaces.pz Ψ r θ * Work.Elliptic.sinCos2 θ‖
        + ∫ s in r..z₁, ‖Work.Spaces.pzIter 2 Ψ s θ * Work.Elliptic.sinCos2 θ‖)
        ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ))) ?_ ?_
    · exact hAESM.norm.integral_prod_right'
    · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioc] with z hz
      have hb : ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ),
          ‖Work.Spaces.pz Ψ z θ * Work.Elliptic.sinCos2 θ‖
            ≤ ‖Work.Spaces.pz Ψ r θ * Work.Elliptic.sinCos2 θ‖
              + ∫ s in r..z₁, ‖Work.Spaces.pzIter 2 Ψ s θ * Work.Elliptic.sinCos2 θ‖ :=
        hbound.mono (fun θ hθ => hθ z hz)
      have h1 : MeasureTheory.Integrable
          (fun θ : ℝ => ‖Work.Spaces.pz Ψ z θ * Work.Elliptic.sinCos2 θ‖)
          (MeasureTheory.volume.restrict Work.Spaces.Iθ) := (hsliceAll z hz).norm
      rw [Real.norm_of_nonneg (MeasureTheory.integral_nonneg_of_ae
        (Filter.Eventually.of_forall (fun θ => norm_nonneg _)))]
      exact MeasureTheory.integral_mono_ae h1 hH hb
  -- ## Conclusion: Fubini for the (not necessarily nonnegative) integrand
  refine (MeasureTheory.integrable_prod_iff hAESM).2
    ⟨MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioc hsliceAll, hout⟩

end Work.FTS.EllipticEst.remov
