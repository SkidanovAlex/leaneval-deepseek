/-
Copyright: work module for the Elgindi finite-time singularity project.

# The chain rule for the angular moment along the radial operator `D_z`

For a source `F : ℝ → ℝ → ℝ` which is `C^∞` on the open quadrant
(`Work.FTS.EllipticEst.SmoothOpen F`) and honestly in the weighted space `ℋ^k`
(`Work.Spaces.HkMem α k F`), and for `j + 1 ≤ k`, the angular moment

  `F_*(D_z^j F)(z) = ∫_θ D_z^j F(z,θ) · sinθcos²θ dθ`

(`Work.Elliptic.Fstar`) is an antiderivative in the radial variable of the next moment
divided by the radius:

  `F_*(D_z^j F)(z) - F_*(D_z^j F)(s) = ∫_s^z F_*(D_z^{j+1} F)(r) / r dr`,   `0 < s ≤ z`.

This is the identity that turns the `H^k`-energy estimates of §'Elliptic Regularity
Estimates' of

  T. M. Elgindi, *Finite-time singularity formation for `C^{1,α}` solutions to the
  incompressible Euler equations on `ℝ³`*, Annals of Math. **194** (2021)

into statements about the next level of derivatives; it is the input `G1` of the
`HkMem_Gbar_sin` certificate.

## Proof

The identity `D_z F = r ∂_r F` gives, pointwise in `θ`,

  `D_z^j F(z,θ) - D_z^j F(s,θ) = ∫_r∈[s,z] ∂_r(D_z^j F)(r,θ) dr`
  and      `D_z^{j+1} F(r,θ) = r ∂_r(D_z^j F)(r,θ)`,

so it suffices to exchange the two integrations (Fubini–Tonelli for the interval
integral and the angular integral) after pulling the angular weight `sinθcos²θ` inside.
The four inputs are

* `DzIter_slice_FTC_open` : the fundamental theorem of calculus along a radial slice;
* `integrableOn_DzIter_mul_sinCos2` : integrability of the angular slice
  `θ ↦ D_z^j F(z,θ)·sinθcos²θ` at the two endpoints, obtained from the `ℋ^k`-bound
  (`integrableOn_zSummand`) and the pointwise absorption
  `abs_mul_sinCos2_le_weighted`;
* `integrable_uncurry_pz_mul_sinCos2` : joint integrability on the rectangle
  `(s,z] × Iθ` of the mixed derivative against the weight, from `integrable_prod_sq_restrict_open`
  and `aesm_uncurry_restrict_open` (i.e. Tonelli plus continuity on the open quadrant);
* `Work.Spaces.DzIter_succ` : the definitional identity `D_z^j F = r ∂_r`.

Everything here is `sorry`-free and rests on `[propext, Classical.choice, Quot.sound]`.
-/
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.Prod
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.Spaces.Defs
import Submission.Work.Elliptic.Defs
import Submission.Work.FTS.EllipticEst.FstarDzIter_sq_mul_w_le_open
import Submission.Work.FTS.EllipticEst.DzIter_slice_FTC_open
import Submission.Work.FTS.EllipticEst.aesm_uncurry_restrict_open
import Submission.Work.FTS.EllipticEst.integrable_prod_sq_restrict_open
import Submission.Work.FTS.EllipticEst.abs_mul_sinCos2_le_weighted

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.Cert.GbarSin

set_option autoImplicit false
set_option maxHeartbeats 800000

/-! ## Auxiliary lemmas of the assembly -/

/-- A predicate which holds on the open interval `(0, π/2)` holds almost everywhere on `Iθ`
(the two endpoints `0` and `π/2` form a null set). -/
theorem ae_imp_of_mem_Ioo {p : ℝ → Prop} (h : ∀ θ ∈ Set.Ioo 0 (π / 2), p θ) :
    ∀ᵐ θ ∂(MeasureTheory.volume), θ ∈ Work.Spaces.Iθ → p θ := by
  rw [MeasureTheory.ae_iff]
  refine MeasureTheory.measure_mono_null (t := ({0, π / 2} : Set ℝ)) ?_ ?_
  · intro θ hθ
    have hθI : θ ∈ Work.Spaces.Iθ := by
      by_contra hc
      exact hθ (fun h' => absurd h' hc)
    have hpθ : ¬ p θ := fun hp => hθ (fun _ => hp)
    rw [Set.mem_insert_iff, Set.mem_singleton_iff]
    by_contra hcon
    have hcon1 : θ ≠ 0 := fun h => hcon (Or.inl h)
    have hcon2 : θ ≠ π / 2 := fun h => hcon (Or.inr h)
    rw [Work.Spaces.Iθ, Set.mem_Icc] at hθI
    exact hpθ (h θ ⟨lt_of_le_of_ne hθI.1 (Ne.symm hcon1), lt_of_le_of_ne hθI.2 hcon2⟩)
  · have hset : ({0, π / 2} : Set ℝ) = ({0} : Set ℝ) ∪ {π / 2} := by
      ext x; simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_union]
    rw [hset]
    exact MeasureTheory.measure_union_null (MeasureTheory.measure_singleton 0)
      (MeasureTheory.measure_singleton (π / 2))

/-- The angular slice of `D_z^i F` against the weight `sinθcos²θ` is integrable on `Iθ`.
(Specialisation of the Cauchy--Schwarz bound `integrableOn_zSummand` to the bounded angular
weight `sinθcos²θ` of the moment `F_*`.) -/
theorem integrableOn_DzIter_mul_sinCos2 (α : ℝ) (k : ℕ) (F : ℝ → ℝ → ℝ)
    (hF : Work.FTS.EllipticEst.SmoothOpen F) (hmem : Work.Spaces.HkMem α k F)
    {i : ℕ} (hi : i ≤ k) {z : ℝ} (hz : 0 < z) :
    IntegrableOn (fun θ : ℝ => Work.Spaces.DzIter i F z θ * Work.Elliptic.sinCos2 θ)
      Work.Spaces.Iθ := by
  have hzI : z ∈ Work.Spaces.Iz := by rw [Work.Spaces.Iz]; exact le_of_lt hz
  have hsq := Work.FTS.EllipticEst.integrableOn_zSummand α k hF hmem i hi hzI
  have hconst : IntegrableOn (fun _ : ℝ => (1 : ℝ)) Work.Spaces.Iθ :=
    integrableOn_const (by rw [Work.Spaces.Iθ, Real.volume_Icc]; exact ENNReal.ofReal_ne_top)
  have hsum : IntegrableOn (fun θ : ℝ => (Work.Spaces.DzIter i F z θ
      * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2 + 1)
      Work.Spaces.Iθ := hsq.add hconst
  refine Integrable.mono' hsum ?_ ?_
  · exact Work.Spaces.aesm_slice_of_continuousOn_Qd
      (fun p : ℝ × ℝ => Work.Spaces.DzIter i F p.1 p.2 * Work.Elliptic.sinCos2 p.2)
      (((hF.DzIter i).continuousOn).mul (by unfold Work.Elliptic.sinCos2; fun_prop)) hz
  · rw [Work.Spaces.Iθ, ae_restrict_iff' measurableSet_Icc]
    refine Eventually.of_forall fun θ hθ => ?_
    have hb := Work.FTS.EllipticEst.abs_mul_sinCos2_le_weighted
      (f := fun θ => Work.Spaces.DzIter i F z θ) hz hθ
    simpa only [Real.norm_eq_abs] using hb

/-- The uncurried function `(r,θ) ↦ ∂_z(D_z^j F)(r,θ)·sinθcos²θ` is integrable on
`(s,z] × Iθ`: this is the Fubini hypothesis for the chain rule. -/
theorem integrable_uncurry_pz_mul_sinCos2 (α : ℝ) (k : ℕ) (F : ℝ → ℝ → ℝ)
    (hF : Work.FTS.EllipticEst.SmoothOpen F) (hmem : Work.Spaces.HkMem α k F) (j : ℕ)
    (hj : j + 1 ≤ k) {s z : ℝ} (hs : 0 < s) :
    MeasureTheory.Integrable
      (Function.uncurry (fun r θ : ℝ => Work.Spaces.pz (Work.Spaces.DzIter j F) r θ
        * Work.Elliptic.sinCos2 θ))
      ((MeasureTheory.volume.restrict (Set.Ioc s z)).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)) := by
  have h2 := Work.FTS.EllipticEst.integrable_prod_sq_restrict_open α k F hF hmem (j + 1) hj
    (a := s) (b := z) (le_of_lt hs)
  have hD : MeasureTheory.Integrable
      (fun p : ℝ × ℝ => (1 / s) * ((Work.Spaces.DzIter (j + 1) F p.1 p.2
        * (Work.Spaces.w p.1 / (Real.sin (2 * p.2)) ^ (Work.Spaces.eta / 2))) ^ 2 + 1))
      ((MeasureTheory.volume.restrict (Set.Ioc s z)).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)) :=
    (h2.add (MeasureTheory.integrable_const (1 : ℝ))).const_mul (1 / s)
  refine Integrable.mono' hD ?_ ?_
  · exact Work.FTS.EllipticEst.aesm_uncurry_restrict_open
      (fun p : ℝ × ℝ => Work.Spaces.pz (Work.Spaces.DzIter j F) p.1 p.2
        * Work.Elliptic.sinCos2 p.2)
      ((((hF.DzIter j).pz).continuousOn).mul (by unfold Work.Elliptic.sinCos2; fun_prop))
      (le_of_lt hs)
  · have hprod : (MeasureTheory.volume.restrict (Set.Ioc s z)).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)
        = (MeasureTheory.volume.prod MeasureTheory.volume).restrict
            (Set.Ioc s z ×ˢ Work.Spaces.Iθ) := MeasureTheory.Measure.prod_restrict _ _
    rw [hprod]
    refine MeasureTheory.ae_restrict_of_forall_mem
      (measurableSet_Ioc.prod measurableSet_Icc) fun p hp => ?_
    obtain ⟨hp1, hp2⟩ := hp
    have hr : 0 < p.1 := lt_of_lt_of_le hs (le_of_lt hp1.1)
    have hDz : Work.Spaces.DzIter (j + 1) F p.1 p.2
        = p.1 * Work.Spaces.pz (Work.Spaces.DzIter j F) p.1 p.2 := by
      simp only [Work.Spaces.DzIter_succ, Work.Spaces.Dz]
    have hb := Work.FTS.EllipticEst.abs_mul_sinCos2_le_weighted
      (f := fun θ => Work.Spaces.DzIter (j + 1) F p.1 θ) hr hp2
    have hstep : |Work.Spaces.pz (Work.Spaces.DzIter j F) p.1 p.2
          * Work.Elliptic.sinCos2 p.2|
        = |Work.Spaces.DzIter (j + 1) F p.1 p.2 * Work.Elliptic.sinCos2 p.2| / p.1 := by
      rw [eq_div_iff hr.ne']
      calc |Work.Spaces.pz (Work.Spaces.DzIter j F) p.1 p.2 * Work.Elliptic.sinCos2 p.2| * p.1
          = |Work.Spaces.pz (Work.Spaces.DzIter j F) p.1 p.2 * Work.Elliptic.sinCos2 p.2|
              * |p.1| := by rw [abs_of_pos hr]
        _ = |(Work.Spaces.pz (Work.Spaces.DzIter j F) p.1 p.2
              * Work.Elliptic.sinCos2 p.2) * p.1| := (abs_mul _ _).symm
        _ = |Work.Spaces.DzIter (j + 1) F p.1 p.2 * Work.Elliptic.sinCos2 p.2| := by
            rw [hDz]; congr 1; ring
    have hle : |Work.Spaces.DzIter (j + 1) F p.1 p.2 * Work.Elliptic.sinCos2 p.2| / p.1
        ≤ |Work.Spaces.DzIter (j + 1) F p.1 p.2 * Work.Elliptic.sinCos2 p.2| / s :=
      div_le_div_of_nonneg_left (abs_nonneg _) hs (le_of_lt hp1.1)
    calc ‖Work.Spaces.pz (Work.Spaces.DzIter j F) p.1 p.2 * Work.Elliptic.sinCos2 p.2‖
        = |Work.Spaces.pz (Work.Spaces.DzIter j F) p.1 p.2 * Work.Elliptic.sinCos2 p.2| :=
          Real.norm_eq_abs _
      _ = |Work.Spaces.DzIter (j + 1) F p.1 p.2 * Work.Elliptic.sinCos2 p.2| / p.1 := hstep
      _ ≤ |Work.Spaces.DzIter (j + 1) F p.1 p.2 * Work.Elliptic.sinCos2 p.2| / s := hle
      _ ≤ (1 / s) * ((Work.Spaces.DzIter (j + 1) F p.1 p.2
            * (Work.Spaces.w p.1 / (Real.sin (2 * p.2)) ^ (Work.Spaces.eta / 2))) ^ 2 + 1) := by
          rw [show |Work.Spaces.DzIter (j + 1) F p.1 p.2 * Work.Elliptic.sinCos2 p.2| / s
              = (1 / s) * |Work.Spaces.DzIter (j + 1) F p.1 p.2
                  * Work.Elliptic.sinCos2 p.2| by ring]
          exact mul_le_mul_of_nonneg_left hb (by positivity)

/-! ## The chain rule -/

/-- **The chain rule for the angular moment along `D_z`.**  For `F` smooth on the open
quadrant with `F ∈ ℋ^k` and `j + 1 ≤ k`, the moment `F_*(D_z^j F)` is an antiderivative of
`F_*(D_z^{j+1} F)/r`: `F_*(D_z^j F)(z) - F_*(D_z^j F)(s) = ∫_s^z F_*(D_z^{j+1} F)(r)/r dr`
for `0 < s ≤ z`. -/
theorem FstarDzIter_chain_open (α : ℝ) (k : ℕ) (F : ℝ → ℝ → ℝ)
    (hF : Work.FTS.EllipticEst.SmoothOpen F) (hmem : Work.Spaces.HkMem α k F) (j : ℕ)
    (hj : j + 1 ≤ k) {s z : ℝ} (hs : 0 < s) (hsz : s ≤ z) :
    Work.Elliptic.Fstar (Work.Spaces.DzIter j F) z
        - Work.Elliptic.Fstar (Work.Spaces.DzIter j F) s
      = ∫ r in s..z, Work.Elliptic.Fstar (Work.Spaces.DzIter (j + 1) F) r / r := by
  rcases eq_or_lt_of_le hsz with hsz0 | hszlt
  · rw [← hsz0, sub_self, intervalIntegral.integral_same]
  have hzpos : 0 < z := lt_of_lt_of_le hs (le_of_lt hszlt)
  have hjle : j ≤ k := Nat.le_of_succ_le hj
  have hIz := integrableOn_DzIter_mul_sinCos2 α k F hF hmem hjle hzpos
  have hIs := integrableOn_DzIter_mul_sinCos2 α k F hF hmem hjle hs
  have hFub := integrable_uncurry_pz_mul_sinCos2 α k F hF hmem j hj (s := s) (z := z) hs
  have h1 : Work.Elliptic.Fstar (Work.Spaces.DzIter j F) z
        - Work.Elliptic.Fstar (Work.Spaces.DzIter j F) s
      = ∫ θ in Work.Spaces.Iθ, (Work.Spaces.DzIter j F z θ
          - Work.Spaces.DzIter j F s θ) * Work.Elliptic.sinCos2 θ := by
    simp only [Work.Elliptic.Fstar]
    rw [show (fun θ : ℝ => (Work.Spaces.DzIter j F z θ - Work.Spaces.DzIter j F s θ)
          * Work.Elliptic.sinCos2 θ)
        = fun θ => Work.Spaces.DzIter j F z θ * Work.Elliptic.sinCos2 θ
            - Work.Spaces.DzIter j F s θ * Work.Elliptic.sinCos2 θ from by
      funext θ; ring]
    rw [MeasureTheory.integral_sub hIz hIs]
  have h2 : ∫ θ in Work.Spaces.Iθ, (Work.Spaces.DzIter j F z θ
        - Work.Spaces.DzIter j F s θ) * Work.Elliptic.sinCos2 θ
      = ∫ θ in Work.Spaces.Iθ, (∫ r in s..z, Work.Spaces.pz (Work.Spaces.DzIter j F) r θ)
          * Work.Elliptic.sinCos2 θ := by
    refine MeasureTheory.setIntegral_congr_ae measurableSet_Icc ?_
    refine ae_imp_of_mem_Ioo fun θ hθ => ?_
    rw [Work.FTS.EllipticEst.DzIter_slice_FTC_open hF j hs hsz hθ]
  have h3 : ∫ θ in Work.Spaces.Iθ, (∫ r in s..z, Work.Spaces.pz (Work.Spaces.DzIter j F) r θ)
        * Work.Elliptic.sinCos2 θ
      = ∫ θ in Work.Spaces.Iθ, ∫ r in s..z, Work.Spaces.pz (Work.Spaces.DzIter j F) r θ
          * Work.Elliptic.sinCos2 θ := by
    refine MeasureTheory.setIntegral_congr_fun measurableSet_Icc fun θ _ => ?_
    exact (intervalIntegral.integral_mul_const (Work.Elliptic.sinCos2 θ)
      (fun r => Work.Spaces.pz (Work.Spaces.DzIter j F) r θ)).symm
  have h4 : ∫ θ in Work.Spaces.Iθ, ∫ r in s..z, Work.Spaces.pz (Work.Spaces.DzIter j F) r θ
          * Work.Elliptic.sinCos2 θ
      = ∫ r in s..z, ∫ θ in Work.Spaces.Iθ, Work.Spaces.pz (Work.Spaces.DzIter j F) r θ
          * Work.Elliptic.sinCos2 θ := by
    refine (MeasureTheory.intervalIntegral_integral_swap (a := s) (b := z)
      (μ := MeasureTheory.volume.restrict Work.Spaces.Iθ)
      (f := fun r θ => Work.Spaces.pz (Work.Spaces.DzIter j F) r θ
        * Work.Elliptic.sinCos2 θ) ?_).symm
    rwa [Set.uIoc_of_le hsz]
  have h5 : ∫ r in s..z, (∫ θ in Work.Spaces.Iθ, Work.Spaces.pz (Work.Spaces.DzIter j F) r θ
          * Work.Elliptic.sinCos2 θ)
      = ∫ r in s..z, Work.Elliptic.Fstar (Work.Spaces.DzIter (j + 1) F) r / r := by
    refine intervalIntegral.integral_congr fun r hr => ?_
    have hsr : s ≤ r := le_trans (le_of_eq (min_eq_left hsz).symm) hr.1
    have hr0 : 0 < r := lt_of_lt_of_le hs hsr
    have hval : Work.Elliptic.Fstar (Work.Spaces.DzIter (j + 1) F) r
        = r * ∫ θ in Work.Spaces.Iθ, Work.Spaces.pz (Work.Spaces.DzIter j F) r θ
            * Work.Elliptic.sinCos2 θ := by
      rw [Work.Elliptic.Fstar]
      rw [show (fun θ : ℝ => Work.Spaces.DzIter (j + 1) F r θ * Work.Elliptic.sinCos2 θ)
          = fun θ => r * (Work.Spaces.pz (Work.Spaces.DzIter j F) r θ
              * Work.Elliptic.sinCos2 θ) from by
        funext θ; simp only [Work.Spaces.DzIter_succ, Work.Spaces.Dz]; ring]
      rw [MeasureTheory.integral_const_mul]
    rw [hval, mul_div_cancel_left₀ _ hr0.ne']
  calc Work.Elliptic.Fstar (Work.Spaces.DzIter j F) z
        - Work.Elliptic.Fstar (Work.Spaces.DzIter j F) s
      = ∫ θ in Work.Spaces.Iθ, (Work.Spaces.DzIter j F z θ
          - Work.Spaces.DzIter j F s θ) * Work.Elliptic.sinCos2 θ := h1
    _ = ∫ θ in Work.Spaces.Iθ, (∫ r in s..z, Work.Spaces.pz (Work.Spaces.DzIter j F) r θ)
          * Work.Elliptic.sinCos2 θ := h2
    _ = ∫ θ in Work.Spaces.Iθ, ∫ r in s..z, Work.Spaces.pz (Work.Spaces.DzIter j F) r θ
          * Work.Elliptic.sinCos2 θ := h3
    _ = ∫ r in s..z, ∫ θ in Work.Spaces.Iθ, Work.Spaces.pz (Work.Spaces.DzIter j F) r θ
          * Work.Elliptic.sinCos2 θ := h4
    _ = ∫ r in s..z, Work.Elliptic.Fstar (Work.Spaces.DzIter (j + 1) F) r / r := h5

end Work.FTS.EllipticEst.Cert.GbarSin
