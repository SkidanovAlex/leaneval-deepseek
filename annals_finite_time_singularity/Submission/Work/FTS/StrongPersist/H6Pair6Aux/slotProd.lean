/-
Copyright: work module for the Elgindi finite-time singularity project.

# Product-measure integrability of the single weighted slots of `HkIntegrand`

For a datum `f` which is `C^∞` on the open quadrant (`Work.FTS.EllipticEst.SmoothOpen f`)
and honestly in `ℋ^n` (`Work.Spaces.HkMem α n f`), this file proves that the individual
weighted slots of the `ℋ^n`-integrand are integrable on the product measure
`(volume|Iz).prod (volume|Iθ)`:

* the pure `D_z`-slots `w(z)² · sin(2θ)^{-η} · (D_z^i f)²` for `i ≤ n`;
* the mixed slots `w(z)² · sin(2θ)^{-γ} · (D_z^j D_θ^i f)²` for `1 ≤ i`, `i + j ≤ n`.

Both statements are the product-measure counterparts of a single summand of
`Work.Spaces.HkIntegrand`, dominated pointwise by the whole integrand
(`Work.Spaces.sq_le_HkIntegrand_z`, `Work.Spaces.sq_le_HkIntegrand_mixed`), whose angular
slices and radial marginal are integrable by `HkMem`.  The bridge from the iterated integral
to the product integral is `Work.Spaces.integrable_prod_of_iterated` (nonnegative Tonelli);
a.e. strong measurability comes from continuity of the weighted derivative on the open
quadrant (`Work.Spaces.aesm_of_continuousOn_Qd`), and the statement's integrand (a raw
product of weights rather than a square of a weighted derivative) is recognized as the
square of the weighted derivative through the `rpow` identities collected below.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.Prod
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.Spaces.HkSq_terms
import Submission.Work.Spaces.bt_prod_integrable
import Submission.Work.Spaces.aesm_of_continuousOn_Qd
import Submission.Work.Spaces.integrable_prod_of_iterated

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongPersist.H6Pair6Aux

set_option autoImplicit false

/-! ## Pointwise facts on `Iθ` and on the open quadrant -/

/-- `sin (2θ) ≥ 0` on `Iθ = [0, π/2]`. -/
private theorem sin_two_nonneg_Iθ {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) :
    0 ≤ Real.sin (2 * θ) :=
  Real.sin_nonneg_of_mem_Icc ⟨by linarith [hθ.1], by linarith [hθ.2, Real.pi_pos]⟩

/-- `sin (2θ) > 0` on the open quadrant. -/
private theorem sin_two_pos_Q0 {p : ℝ × ℝ}
    (hp : p ∈ (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2) : Set (ℝ × ℝ))) :
    0 < Real.sin (2 * p.2) :=
  Real.sin_pos_of_pos_of_lt_pi (by linarith [hp.2.1]) (by linarith [hp.2.2, Real.pi_pos])

/-- `(a ^ p) ^ 2 = a ^ (2p)` for `a ≥ 0`. -/
private theorem sq_rpow_mul_two {a : ℝ} (ha : 0 ≤ a) (p : ℝ) :
    (a ^ p) ^ 2 = a ^ (p * 2) := by
  rw [← Real.rpow_natCast (a ^ p) 2]
  exact (Real.rpow_mul ha p 2).symm

/-- Squaring the weight `W = w · sin(2θ)^{-γ/2}` gives the raw weight
`w² · sin(2θ)^{-γ}` of the energy. -/
private theorem Wt_sq_eq (α z θ : ℝ) (hθ : θ ∈ Work.Spaces.Iθ) :
    (Work.Spaces.Wt α z θ) ^ 2
      = (Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) := by
  have h1 : Work.Spaces.Wt α z θ
      = Work.Spaces.w z * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α / 2)) := by
    rw [Work.Spaces.Wt, Work.Spaces.wTheta]
  rw [h1, mul_pow, sq_rpow_mul_two (sin_two_nonneg_Iθ hθ) (-(Work.Spaces.gam α / 2)),
    show (-(Work.Spaces.gam α / 2)) * 2 = -(Work.Spaces.gam α) by ring]

/-- Squaring the weight `w / sin(2θ)^{η/2}` gives the raw weight `w² · sin(2θ)^{-η}`. -/
private theorem whz_sq_eq (z θ : ℝ) (hθ : θ ∈ Work.Spaces.Iθ) :
    (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2)) ^ 2
      = (Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) := by
  have ha := sin_two_nonneg_Iθ hθ
  have h1 : Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2)
      = Work.Spaces.w z * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta / 2)) := by
    rw [div_eq_mul_inv, Real.rpow_neg ha (Work.Spaces.eta / 2)]
  rw [h1, mul_pow, sq_rpow_mul_two ha (-(Work.Spaces.eta / 2)),
    show (-(Work.Spaces.eta / 2)) * 2 = -(Work.Spaces.eta) by ring]

/-- The `γ`-slot integrand is the square of the weighted mixed derivative. -/
private theorem mixed_slot_eq (α z θ : ℝ) (hθ : θ ∈ Work.Spaces.Iθ) (X : ℝ) :
    (Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) * X ^ 2
      = (X * Work.Spaces.Wt α z θ) ^ 2 := by
  rw [mul_pow, Wt_sq_eq α z θ hθ]
  ring

/-- The `η`-slot integrand is the square of the weighted `D_z`-derivative. -/
private theorem z_slot_eq (z θ : ℝ) (hθ : θ ∈ Work.Spaces.Iθ) (X : ℝ) :
    (Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) * X ^ 2
      = (X * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2 := by
  rw [mul_pow, whz_sq_eq z θ hθ]
  ring

/-- Almost every point of the product measure has its angular coordinate in `Iθ`. -/
private theorem ae_snd_mem_Iθ :
    ∀ᵐ p ∂((volume.restrict Work.Spaces.Iz).prod (volume.restrict Work.Spaces.Iθ)),
      p.2 ∈ Work.Spaces.Iθ := by
  rw [MeasureTheory.Measure.prod_restrict]
  exact (MeasureTheory.ae_restrict_mem
    (show MeasurableSet (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ) from
      measurableSet_Ici.prod measurableSet_Icc)).mono (fun _ hp => hp.2)

/-! ## Continuity on the open quadrant -/

private theorem continuousOn_w_sq_Q0 :
    ContinuousOn (fun p : ℝ × ℝ => (Work.Spaces.w p.1) ^ 2)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2) : Set (ℝ × ℝ)) := by
  have h : (fun p : ℝ × ℝ => (Work.Spaces.w p.1) ^ 2)
      = fun p : ℝ × ℝ => ((1 + p.1) ^ 2 / p.1 ^ 2) ^ 2 := by
    funext p; simp only [Work.Spaces.w]
  rw [h]
  exact (ContinuousOn.div ((continuousOn_const.add continuousOn_fst).pow 2)
    (continuousOn_fst.pow 2) (fun p hp => pow_ne_zero 2 (ne_of_gt hp.1))).pow 2

private theorem continuousOn_w_Q0 :
    ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.w p.1)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2) : Set (ℝ × ℝ)) := by
  have h : (fun p : ℝ × ℝ => Work.Spaces.w p.1)
      = fun p : ℝ × ℝ => (1 + p.1) ^ 2 / p.1 ^ 2 := by
    funext p; simp only [Work.Spaces.w]
  rw [h]
  exact ContinuousOn.div ((continuousOn_const.add continuousOn_fst).pow 2)
    (continuousOn_fst.pow 2) (fun p hp => pow_ne_zero 2 (ne_of_gt hp.1))

private theorem continuousOn_sinpow_Q0 (q : ℝ) :
    ContinuousOn (fun p : ℝ × ℝ => (Real.sin (2 * p.2)) ^ q)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2) : Set (ℝ × ℝ)) :=
  ((Real.continuous_sin.comp (continuous_const.mul continuous_snd)).continuousOn).rpow_const
    (fun _p hp => Or.inl (ne_of_gt (sin_two_pos_Q0 hp)))

private theorem continuousOn_Wt_Q0 (α : ℝ) :
    ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.Wt α p.1 p.2)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2) : Set (ℝ × ℝ)) := by
  have h : (fun p : ℝ × ℝ => Work.Spaces.Wt α p.1 p.2)
      = fun p : ℝ × ℝ =>
          Work.Spaces.w p.1 * (Real.sin (2 * p.2)) ^ (-(Work.Spaces.gam α / 2)) := by
    funext p; simp only [Work.Spaces.Wt, Work.Spaces.wTheta]
  rw [h]
  exact continuousOn_w_Q0.mul (continuousOn_sinpow_Q0 (-(Work.Spaces.gam α / 2)))

private theorem continuousOn_wdivsin_Q0 :
    ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.w p.1
        / (Real.sin (2 * p.2)) ^ (Work.Spaces.eta / 2))
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2) : Set (ℝ × ℝ)) :=
  continuousOn_w_Q0.div (continuousOn_sinpow_Q0 (Work.Spaces.eta / 2))
    (fun _p hp => ne_of_gt (Real.rpow_pos_of_pos (sin_two_pos_Q0 hp) _))

private theorem aesm_mixed_slot (α : ℝ) {j i : ℕ} {f : ℝ → ℝ → ℝ}
    (hf : Work.FTS.EllipticEst.SmoothOpen f) :
    AEStronglyMeasurable
      (fun p : ℝ × ℝ => (Work.Spaces.mixed j i f p.1 p.2 * Work.Spaces.Wt α p.1 p.2) ^ 2)
      ((volume.restrict Work.Spaces.Iz).prod (volume.restrict Work.Spaces.Iθ)) :=
  Work.Spaces.aesm_of_continuousOn_Qd _
    (ContinuousOn.pow (((hf.mixed j i).continuousOn).mul (continuousOn_Wt_Q0 α)) 2)

private theorem aesm_z_slot {i : ℕ} {f : ℝ → ℝ → ℝ}
    (hf : Work.FTS.EllipticEst.SmoothOpen f) :
    AEStronglyMeasurable
      (fun p : ℝ × ℝ => (Work.Spaces.DzIter i f p.1 p.2
        * (Work.Spaces.w p.1 / (Real.sin (2 * p.2)) ^ (Work.Spaces.eta / 2))) ^ 2)
      ((volume.restrict Work.Spaces.Iz).prod (volume.restrict Work.Spaces.Iθ)) :=
  Work.Spaces.aesm_of_continuousOn_Qd _
    (ContinuousOn.pow (((hf.DzIter i).continuousOn).mul continuousOn_wdivsin_Q0) 2)

/-! ## The mixed slots -/

/-- **The `γ`-weighted mixed slots are jointly integrable.** -/
theorem mixedSlotProd (α : ℝ) (n : ℕ) {f : ℝ → ℝ → ℝ}
    (hsm : Work.FTS.EllipticEst.SmoothOpen f) (hm : Work.Spaces.HkMem α n f) :
    ∀ j i : ℕ, 1 ≤ i → i + j ≤ n → MeasureTheory.Integrable
        (fun p : ℝ × ℝ => (Work.Spaces.w p.1) ^ 2
          * (Real.sin (2 * p.2)) ^ (-(Work.Spaces.gam α))
          * (Work.Spaces.mixed j i f p.1 p.2) ^ 2)
        ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
          (MeasureTheory.volume.restrict Work.Spaces.Iθ)) := by
  intro j i hi hij
  have hAE : AEStronglyMeasurable
      (fun p : ℝ × ℝ => (Work.Spaces.mixed j i f p.1 p.2 * Work.Spaces.Wt α p.1 p.2) ^ 2)
      ((volume.restrict Work.Spaces.Iz).prod (volume.restrict Work.Spaces.Iθ)) :=
    aesm_mixed_slot α hsm
  -- the angular slices are dominated by the `HkIntegrand`-slice
  have hslice : ∀ᵐ z ∂(volume.restrict Work.Spaces.Iz),
      Integrable (fun θ => (Work.Spaces.mixed j i f z θ * Work.Spaces.Wt α z θ) ^ 2)
        (volume.restrict Work.Spaces.Iθ) := by
    filter_upwards [hAE.prodMk_left,
      ae_restrict_mem (show MeasurableSet Work.Spaces.Iz from measurableSet_Ici)]
      with z hzm hz
    refine Integrable.mono' (hm.1 z hz) hzm ?_
    filter_upwards [ae_restrict_mem (show MeasurableSet Work.Spaces.Iθ from measurableSet_Icc)]
      with θ _
    rw [Real.norm_of_nonneg (sq_nonneg _)]
    exact Work.Spaces.sq_le_HkIntegrand_mixed α n f z θ i j hi hij
  -- the radial marginal is integrable, by the same domination
  have houter : Integrable
      (fun z => ∫ θ, (Work.Spaces.mixed j i f z θ * Work.Spaces.Wt α z θ) ^ 2
        ∂(volume.restrict Work.Spaces.Iθ)) (volume.restrict Work.Spaces.Iz) := by
    refine Integrable.mono' hm.2 hAE.integral_prod_right' ?_
    filter_upwards [ae_restrict_mem (show MeasurableSet Work.Spaces.Iz from measurableSet_Ici)]
      with z hz
    rw [Real.norm_of_nonneg (integral_nonneg fun θ => sq_nonneg _)]
    exact integral_mono_of_nonneg
      (ae_restrict_of_forall_mem (show MeasurableSet Work.Spaces.Iθ from measurableSet_Icc)
        (fun θ _ => sq_nonneg _))
      (hm.1 z hz)
      (ae_restrict_of_forall_mem (show MeasurableSet Work.Spaces.Iθ from measurableSet_Icc)
        (fun θ _ => Work.Spaces.sq_le_HkIntegrand_mixed α n f z θ i j hi hij))
  -- Tonelli turns the iterated integral into the product integral
  have hnice : Integrable
      (Function.uncurry (fun z θ : ℝ =>
        (Work.Spaces.mixed j i f z θ * Work.Spaces.Wt α z θ) ^ 2))
      ((volume.restrict Work.Spaces.Iz).prod (volume.restrict Work.Spaces.Iθ)) :=
    (Work.Spaces.integrable_prod_of_iterated
      (G := fun z θ : ℝ => (Work.Spaces.mixed j i f z θ * Work.Spaces.Wt α z θ) ^ 2)
      (fun _ _ => sq_nonneg _) hAE hslice houter).1
  -- and the statement's integrand agrees with it a.e. on the domain
  refine MeasureTheory.Integrable.congr hnice ?_
  filter_upwards [ae_snd_mem_Iθ] with p hp
  exact (mixed_slot_eq α p.1 p.2 hp (Work.Spaces.mixed j i f p.1 p.2)).symm

/-! ## The pure `D_z` slots -/

/-- **The `η`-weighted pure `D_z`-slots are jointly integrable.** -/
theorem zSlotProd' (α : ℝ) (n : ℕ) {f : ℝ → ℝ → ℝ}
    (hsm : Work.FTS.EllipticEst.SmoothOpen f) (hm : Work.Spaces.HkMem α n f) :
    ∀ i : ℕ, i ≤ n → MeasureTheory.Integrable
        (fun p : ℝ × ℝ => (Work.Spaces.w p.1) ^ 2
          * (Real.sin (2 * p.2)) ^ (-(Work.Spaces.eta))
          * (Work.Spaces.DzIter i f p.1 p.2) ^ 2)
        ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
          (MeasureTheory.volume.restrict Work.Spaces.Iθ)) := by
  intro i hi
  have hAE : AEStronglyMeasurable
      (fun p : ℝ × ℝ => (Work.Spaces.DzIter i f p.1 p.2
        * (Work.Spaces.w p.1 / (Real.sin (2 * p.2)) ^ (Work.Spaces.eta / 2))) ^ 2)
      ((volume.restrict Work.Spaces.Iz).prod (volume.restrict Work.Spaces.Iθ)) :=
    aesm_z_slot hsm
  have hslice : ∀ᵐ z ∂(volume.restrict Work.Spaces.Iz),
      Integrable (fun θ => (Work.Spaces.DzIter i f z θ
        * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2)
        (volume.restrict Work.Spaces.Iθ) := by
    filter_upwards [hAE.prodMk_left,
      ae_restrict_mem (show MeasurableSet Work.Spaces.Iz from measurableSet_Ici)]
      with z hzm hz
    refine Integrable.mono' (hm.1 z hz) hzm ?_
    filter_upwards [ae_restrict_mem (show MeasurableSet Work.Spaces.Iθ from measurableSet_Icc)]
      with θ _
    rw [Real.norm_of_nonneg (sq_nonneg _)]
    exact Work.Spaces.sq_le_HkIntegrand_z α n f z θ i hi
  have houter : Integrable
      (fun z => ∫ θ, (Work.Spaces.DzIter i f z θ
        * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2
        ∂(volume.restrict Work.Spaces.Iθ)) (volume.restrict Work.Spaces.Iz) := by
    refine Integrable.mono' hm.2 hAE.integral_prod_right' ?_
    filter_upwards [ae_restrict_mem (show MeasurableSet Work.Spaces.Iz from measurableSet_Ici)]
      with z hz
    rw [Real.norm_of_nonneg (integral_nonneg fun θ => sq_nonneg _)]
    exact integral_mono_of_nonneg
      (ae_restrict_of_forall_mem (show MeasurableSet Work.Spaces.Iθ from measurableSet_Icc)
        (fun θ _ => sq_nonneg _))
      (hm.1 z hz)
      (ae_restrict_of_forall_mem (show MeasurableSet Work.Spaces.Iθ from measurableSet_Icc)
        (fun θ _ => Work.Spaces.sq_le_HkIntegrand_z α n f z θ i hi))
  have hnice : Integrable
      (Function.uncurry (fun z θ : ℝ =>
        (Work.Spaces.DzIter i f z θ
          * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2))
      ((volume.restrict Work.Spaces.Iz).prod (volume.restrict Work.Spaces.Iθ)) :=
    (Work.Spaces.integrable_prod_of_iterated
      (G := fun z θ : ℝ => (Work.Spaces.DzIter i f z θ
        * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2)
      (fun _ _ => sq_nonneg _) hAE hslice houter).1
  refine MeasureTheory.Integrable.congr hnice ?_
  filter_upwards [ae_snd_mem_Iθ] with p hp
  exact (z_slot_eq p.1 p.2 hp (Work.Spaces.DzIter i f p.1 p.2)).symm

/-! ## The two slots of the `ℋ^n`-integrand, jointly -/

theorem slotProd (α : ℝ) (n : ℕ) {f : ℝ → ℝ → ℝ}
    (hsm : Work.FTS.EllipticEst.SmoothOpen f) (hm : Work.Spaces.HkMem α n f) :
    (∀ i : ℕ, i ≤ n → MeasureTheory.Integrable
        (fun p : ℝ × ℝ => (Work.Spaces.w p.1) ^ 2
          * (Real.sin (2 * p.2)) ^ (-(Work.Spaces.eta))
          * (Work.Spaces.DzIter i f p.1 p.2) ^ 2)
        ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
          (MeasureTheory.volume.restrict Work.Spaces.Iθ))) ∧
    (∀ j i : ℕ, 1 ≤ i → i + j ≤ n → MeasureTheory.Integrable
        (fun p : ℝ × ℝ => (Work.Spaces.w p.1) ^ 2
          * (Real.sin (2 * p.2)) ^ (-(Work.Spaces.gam α))
          * (Work.Spaces.mixed j i f p.1 p.2) ^ 2)
        ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
          (MeasureTheory.volume.restrict Work.Spaces.Iθ))) :=
  ⟨zSlotProd' α n hsm hm, mixedSlotProd α n hsm hm⟩

end Work.FTS.StrongPersist.H6Pair6Aux
