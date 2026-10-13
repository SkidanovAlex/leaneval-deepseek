/-
# `f · w` is in `L²`: the `Xw` block of the `ℋ¹` pairing is honest

For `f` smooth on a neighbourhood of the closed quadrant and `HkMem α 1 f`, the
weighted block `Xw f = f · w` occurring in the plain `w²`-pairing of the `ℋ¹`
inner product has an honest iterated `L²` integral.

The point is that `HkMem α 1 f` controls the *stronger* weighted block
`U0 f = f · w / sin(2θ)^{η/2}`: since `η > 0` and `0 < sin(2θ) ≤ 1` on the open
quadrant, division by `sin(2θ)^{η/2}` only increases the size, i.e.
`|f w| ≤ |f w / sin(2θ)^{η/2}|` off the null set `{θ = 0, π/2}`.  The two
measurability requirements are supplied by the continuity of the integrand on the
open quadrant (`aesm_of_continuousOn_Qd`, `aesm_slice_of_continuousOn_Qd`).

The comparison `(a/t)² ≥ a²` for `0 < t ≤ 1` is the whole content of the estimate;
everything else is bookkeeping with the iterated integral.
-/
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.Prod
import Submission.Work.FTS.H2.T2Aesm
import Submission.Work.Coercivity.H1IPAddDefs
import Submission.Work.Coercivity.Eztheta1_eq_HkSq_one
import Submission.Work.Spaces.AesmSqProdSmooth
import Submission.Work.Spaces.aesm_of_continuousOn_Qd
import Submission.Work.Spaces.aesm_slice_of_continuousOn_Qd

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.Coercivity

set_option autoImplicit false

/-! ## The elementary comparison -/

/-- For `0 < t ≤ 1` and any `a`, dividing by `t` does not decrease the square:
`a ^ 2 ≤ (a / t) ^ 2`. -/
private lemma sq_le_div_sq {a t : ℝ} (ht0 : 0 < t) (ht1 : t ≤ 1) : a ^ 2 ≤ (a / t) ^ 2 := by
  have ht2 : 0 < t ^ 2 := pow_pos ht0 2
  have ht2le : t ^ 2 ≤ 1 := by nlinarith [ht0, ht1]
  rw [div_pow, le_div_iff₀ ht2]
  simpa using mul_le_mul_of_nonneg_left ht2le (sq_nonneg a)

/-! ## Continuity of the integrand on the open quadrant -/

/-- The open quadrant `(0,∞) × (0,π/2)`. -/
private def Qd : Set (ℝ × ℝ) := Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)

private lemma Qd_subset_nbhU : Qd ⊆ Spaces.nbhU := by
  rintro ⟨z, θ⟩ ⟨hz, hθ⟩
  exact Spaces.mem_nbhU (Set.mem_Ici.mpr (le_of_lt hz))
    (Set.mem_Icc.mpr ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩)

/-- `(f z θ · w z)²` is continuous on the open quadrant. -/
private lemma continuousOn_Xw_sq (f : ℝ → ℝ → ℝ) (hsm : Spaces.SmoothNbhd f) :
    ContinuousOn (fun p : ℝ × ℝ => (Xw f p.1 p.2) ^ 2) Qd := by
  have hf : ContinuousOn (fun p : ℝ × ℝ => f p.1 p.2) Qd :=
    hsm.continuousOn.mono Qd_subset_nbhU
  have hw : ContinuousOn (fun p : ℝ × ℝ => Spaces.w p.1) Qd := by
    simp only [Spaces.w]
    exact ContinuousOn.div ((continuousOn_const.add continuousOn_fst).pow 2)
      (continuousOn_fst.pow 2) (fun p hp => pow_ne_zero 2 (ne_of_gt hp.1))
  exact (hf.mul hw).pow 2

/-- Almost everywhere strong measurability of `(f · w)²`, both on the product measure
`(dz)|_{Iz} ⊗ (dθ)|_{Iθ}` and on every angular slice. -/
private theorem aesm_Xw_sq (f : ℝ → ℝ → ℝ) (hsm : Spaces.SmoothNbhd f) :
    AEStronglyMeasurable (fun p : ℝ × ℝ => (Xw f p.1 p.2) ^ 2)
        ((volume.restrict Spaces.Iz).prod (volume.restrict Spaces.Iθ))
      ∧ ∀ z ∈ Spaces.Iz, AEStronglyMeasurable (fun θ : ℝ => (Xw f z θ) ^ 2)
          (volume.restrict Spaces.Iθ) := by
  refine ⟨Spaces.aesm_of_continuousOn_Qd _ (continuousOn_Xw_sq f hsm), ?_⟩
  intro z hz
  rcases eq_or_lt_of_le (show (0 : ℝ) ≤ z from hz) with h0 | hpos
  · subst h0
    have hz0 : (fun θ : ℝ => (Xw f 0 θ) ^ 2) = fun _ : ℝ => (0 : ℝ) := by
      funext θ
      simp [Xw, Spaces.w]
    rw [hz0]
    exact aestronglyMeasurable_const
  · exact Spaces.aesm_slice_of_continuousOn_Qd _ (continuousOn_Xw_sq f hsm) hpos

/-! ## The a.e. comparison with the `H¹`-integrand -/

/-- Off the two null endpoints of `Iθ`, `(f · w)²` is bounded by the `H¹`-integrand,
because the `D_z⁰`-summand of the latter is `(f · w / sin(2θ)^{η/2})²` and
`0 < sin(2θ) ≤ 1` there. -/
private lemma sq_Xw_le_HkIntegrand_ae (α : ℝ) (f : ℝ → ℝ → ℝ) (z : ℝ) :
    ∀ᵐ θ ∂(volume.restrict Spaces.Iθ),
      (Xw f z θ) ^ 2 ≤ Spaces.HkIntegrand α 1 f z θ := by
  have hmeas : volume.restrict (Set.Ioo 0 (π / 2)) = volume.restrict Spaces.Iθ :=
    Measure.restrict_congr_set MeasureTheory.Ioo_ae_eq_Icc
  rw [← hmeas]
  filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioo] with θ hθ
  have hs0 : 0 < Real.sin (2 * θ) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])
  have hs1 : Real.sin (2 * θ) ≤ 1 := Real.sin_le_one _
  have ht0 : 0 < (Real.sin (2 * θ)) ^ (Spaces.eta / 2) := Real.rpow_pos_of_pos hs0 _
  have ht1 : (Real.sin (2 * θ)) ^ (Spaces.eta / 2) ≤ 1 := by
    calc (Real.sin (2 * θ)) ^ (Spaces.eta / 2)
        ≤ (1 : ℝ) ^ (Spaces.eta / 2) := Real.rpow_le_rpow (le_of_lt hs0) hs1
          (div_nonneg (le_of_lt Spaces.eta_pos) (by norm_num))
      _ = 1 := by simp
  have hkey : (f z θ * Spaces.w z) ^ 2
      ≤ ((f z θ * Spaces.w z) / (Real.sin (2 * θ)) ^ (Spaces.eta / 2)) ^ 2 :=
    sq_le_div_sq ht0 ht1
  have hterm : (Xw f z θ) ^ 2
      ≤ (Spaces.DzIter 0 f z θ
          * (Spaces.w z / (Real.sin (2 * θ)) ^ (Spaces.eta / 2))) ^ 2 := by
    simp only [Xw, Spaces.DzIter_zero]
    rw [← mul_div_assoc]
    exact hkey
  exact le_trans hterm (Spaces.sq_le_HkIntegrand_z α 1 f z θ 0 (by norm_num))

/-! ## The main statement -/

theorem L2Mem_Xw (α : ℝ) (f : ℝ → ℝ → ℝ) (hsm : Spaces.SmoothNbhd f)
    (hmem : Spaces.HkMem α 1 f) : Spaces.L2Mem (Xw f) := by
  obtain ⟨hA, hAs⟩ := aesm_Xw_sq f hsm
  constructor
  · intro z hz
    refine MeasureTheory.Integrable.mono' (hmem.1 z hz) (hAs z hz) ?_
    filter_upwards [sq_Xw_le_HkIntegrand_ae α f z] with θ hθ
    rwa [Real.norm_of_nonneg (sq_nonneg _)]
  · refine MeasureTheory.Integrable.mono' hmem.2 hA.integral_prod_right' ?_
    filter_upwards [MeasureTheory.ae_restrict_mem
      (show MeasurableSet Spaces.Iz from measurableSet_Ici)] with z hz
    rw [Real.norm_of_nonneg (integral_nonneg fun θ => sq_nonneg _)]
    exact MeasureTheory.integral_mono_of_nonneg
      (MeasureTheory.ae_restrict_of_forall_mem
        (show MeasurableSet Spaces.Iθ from measurableSet_Icc) (fun θ _ => sq_nonneg _))
      (hmem.1 z hz) (sq_Xw_le_HkIntegrand_ae α f z)

end Work.Coercivity
