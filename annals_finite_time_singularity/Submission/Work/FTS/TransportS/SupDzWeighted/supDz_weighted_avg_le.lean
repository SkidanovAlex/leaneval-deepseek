/-
Copyright: work module for the Elgindi finite-time singularity project.

# The weighted angular average of `D_z^b f` is uniformly bounded in `z`

For a datum `f` of the open class (`Work.FTS.EllipticEst.SmoothOpen`) which lies honestly in
`ℋ⁴` (`Work.Spaces.HkMem α 4 f`), and for `b ≤ 2`,

  `∫_{Iθ} (D_z^b f z θ)² · sin(2θ)^{-η}  ≤  C · |f|²_{ℋ⁴}`  for every `z > 0`,

with a universal constant `C` (`C = 3` works).  This is the `η`-weighted companion of
`Work.FTS.TransportS.SupDzAux.sup_dz_avg_le`; it is one of the two inputs of
`Work.FTS.TransportS.sup_dz_le_hk`.

ROUTE (the same scheme as `sup_dz_avg_le`, with the angular weight `sin(2θ)^{-η}` kept):

1. The 1-dimensional window form of the radial Hardy inequality
   (`Work.FTS.TransportS.half_line_window_bound`), applied slicewise in the angle `σ` to
   `h := fun x => D_z^b f x σ`, `h' := fun x => ∂_z(D_z^b f) x σ`, gives for `z ≤ R₀`
   `h(z)² ≤ 2 ∫_z^{2R₀}(x h'(x) w(x))² + (2/R₀)∫_{R₀}^{2R₀} h²`; since `x h'(x) = D_z^{b+1}f x σ`,
   multiplying by `sin(2σ)^{-η} ≥ 0` turns both window integrands into the corresponding
   summands of `HkIntegrand α 4 f x σ`:
   `(D_z^{b+1}f x σ · w x)² sin(2σ)^{-η}` is exactly the `i = b+1` summand and
   `(D_z^b f x σ)² sin(2σ)^{-η} ≤ (D_z^b f x σ)² w(x)² sin(2σ)^{-η}` is the `i = b` summand
   (using `w ≥ 1` on `z > 0`).  Note `b ≤ 2` so both indices are `≤ 3 ≤ 4`.
2. Integrate the resulting a.e. inequality in `σ` against the measure
   `volume.restrict Iθ`; the right-hand side `σ ↦ ∫_s HkIntegrand α 4 f s σ` is integrable by
   (the `SmoothOpen`-version of) Tonelli, and its integral over `σ` is `HkSq α 4 f`
   (`Work.FTS.TransportS.SupDzAux.avgHkSqSwap`).
3. Choose `R₀ = max z 2`, so that `2 + 2/R₀ ≤ 3`.

The angular slice integrability in step 2 comes from the fact that the weighted square is
(up to the constant factor `w^{-2}`) one of the summands of `HkIntegrand α 4 f`, whose angular
integral is finite for every `z` by `HkMem`; this is
`Work.FTS.EllipticEst.integrableOn_zSummand` plus the algebraic identity
`a² x^{-η} = (a · w / x^{η/2})² · w^{-2}`.

All declarations here are `sorry`-free.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.FTS.TransportS.SupDzAux.sup_dz_avg_le

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.TransportS.SupDzWeighted

set_option autoImplicit false
set_option maxHeartbeats 4000000

/-! ## Elementary algebraic identities for the weights -/

/-- `sin(2θ) > 0` in the interior of `Iθ`. -/
theorem sin_two_pos_of_mem_Ioo {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (π / 2)) :
    0 < Real.sin (2 * θ) :=
  Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])

/-- The weight identity behind the comparison with the `i`-th summand of `HkIntegrand`:
`(a·w)² x^{-c} = (a · w/x^{c/2})²`  (`x ≥ 0`, `c ≠ 0`). -/
theorem mul_w_sq_mul_rpow_neg (a w x c : ℝ) (hx : 0 ≤ x) (hc : c ≠ 0) :
    (a * w) ^ 2 * x ^ (-c) = (a * (w / x ^ (c / 2))) ^ 2 := by
  have h : (a * (w / x ^ (c / 2))) ^ 2 = a ^ 2 * (w ^ 2 * x ^ (-c)) := by
    rw [mul_pow, Work.FTS.H2.div_rpow_sq w x c hx hc]
  rw [h]; ring

/-- The inverse of the previous identity, in the form needed to read off integrability:
`(a · w/x^{c/2})² · w^{-2} = a² x^{-c}`  (`w ≠ 0`, `x ≥ 0`, `c ≠ 0`). -/
theorem sq_div_rpow_sq (a w x c : ℝ) (hw : w ≠ 0) (hx : 0 ≤ x) (hc : c ≠ 0) :
    (a * (w / x ^ (c / 2))) ^ 2 * (w⁻¹) ^ 2 = a ^ 2 * x ^ (-c) := by
  have h : (a * (w / x ^ (c / 2))) ^ 2 = a ^ 2 * (w ^ 2 * x ^ (-c)) := by
    rw [mul_pow, Work.FTS.H2.div_rpow_sq w x c hx hc]
  rw [h, inv_pow]
  field_simp

/-! ## Pointwise domination by the `ℋ⁴`-integrand -/

/-- The `i = j` summand of `HkIntegrand` dominates `(D_z^j f · w)² sin(2θ)^{-η}` for `j ≤ 4`
(`z > 0`, `sin(2θ) > 0`). -/
theorem dzIter_mul_w_sq_mul_rpow_neg_le_HkIntegrand (α : ℝ) (f : ℝ → ℝ → ℝ) {z θ : ℝ}
    (hsin : 0 < Real.sin (2 * θ)) (j : ℕ) (hj : j ≤ 4) :
    (Work.Spaces.DzIter j f z θ * Work.Spaces.w z) ^ 2
        * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))
      ≤ Work.Spaces.HkIntegrand α 4 f z θ := by
  rw [mul_w_sq_mul_rpow_neg (Work.Spaces.DzIter j f z θ) (Work.Spaces.w z) (Real.sin (2 * θ))
    Work.Spaces.eta (le_of_lt hsin) (ne_of_gt Work.Spaces.eta_pos)]
  exact Work.Spaces.sq_le_HkIntegrand_z α 4 f z θ j hj

/-- **The pointwise domination of the weighted square of `D_z^j f` by the `ℋ⁴`-integrand**:
for `z > 0`, `sin(2θ) > 0` and `j ≤ 4`,
`(D_z^j f)² sin(2θ)^{-η} ≤ HkIntegrand α 4 f`.  (This is *not* a direct summand — it is the
`i = j` summand divided by `w² ≥ 1`.) -/
theorem dzIter_sq_mul_rpow_neg_le_HkIntegrand (α : ℝ) (f : ℝ → ℝ → ℝ) {z θ : ℝ}
    (hz : 0 < z) (hsin : 0 < Real.sin (2 * θ)) (j : ℕ) (hj : j ≤ 4) :
    (Work.Spaces.DzIter j f z θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))
      ≤ Work.Spaces.HkIntegrand α 4 f z θ := by
  have hw2 : (1 : ℝ) ≤ (Work.Spaces.w z) ^ 2 :=
    one_le_pow₀ (Work.FTS.TransportS.one_le_w hz)
  have hnn : 0 ≤ (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) :=
    Real.rpow_nonneg (le_of_lt hsin) _
  have hstep : (Work.Spaces.DzIter j f z θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))
      ≤ (Work.Spaces.DzIter j f z θ * Work.Spaces.w z) ^ 2
        * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) := by
    rw [mul_pow]
    simpa only [mul_one] using
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hw2 (sq_nonneg (Work.Spaces.DzIter j f z θ))) hnn
  exact le_trans hstep
    (dzIter_mul_w_sq_mul_rpow_neg_le_HkIntegrand α f hsin j hj)

/-! ## Integrability of the weighted angular slice -/

/-- The weighted square `(D_z^j f z ·)² sin(2·)^{-η}` is integrable on the angular interval,
for `z > 0` and `j ≤ 4`, as soon as `f` is of the open class and `ℋ⁴`.  Indeed it equals
`(D_z^j f z · · (w z / sin(2·)^{η/2}))² · (w z)^{-2}`, a constant multiple of the `j`-th
summand of `HkIntegrand α 4 f`, whose angular integral is finite for every `z` by `HkMem`
(`Work.FTS.EllipticEst.integrableOn_zSummand`). -/
theorem integrableOn_dzIter_sq_mul_rpow_neg (α : ℝ) (f : ℝ → ℝ → ℝ)
    (hF : Work.FTS.EllipticEst.SmoothOpen f) (hmem : Work.Spaces.HkMem α 4 f)
    (j : ℕ) (hj : j ≤ 4) {z : ℝ} (hz : 0 < z) :
    IntegrableOn
      (fun θ : ℝ => (Work.Spaces.DzIter j f z θ) ^ 2
        * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))) Work.Spaces.Iθ := by
  have hsum := Work.FTS.EllipticEst.integrableOn_zSummand α 4 hF hmem j hj (le_of_lt hz)
  have hwne : Work.Spaces.w z ≠ 0 := ne_of_gt (Work.FTS.TransportS.w_pos_of_pos hz)
  have hmul : Integrable
      (fun θ : ℝ => (Work.Spaces.DzIter j f z θ
        * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2
        * ((Work.Spaces.w z)⁻¹) ^ 2) (volume.restrict Work.Spaces.Iθ) :=
    hsum.mul_const _
  refine hmul.congr ?_
  refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc fun θ hθ => ?_
  exact (sq_div_rpow_sq (Work.Spaces.DzIter j f z θ) (Work.Spaces.w z) (Real.sin (2 * θ))
    Work.Spaces.eta hwne (Work.Spaces.bt_sin_nonneg hθ)
    (ne_of_gt Work.Spaces.eta_pos))

/-! ## The main estimate -/

theorem supDz_weighted_avg_le :
    ∃ C : ℝ, 0 < C ∧ ∀ (α : ℝ) (f : ℝ → ℝ → ℝ) (b : ℕ), 0 < α → α ≤ 1 →
      Work.FTS.EllipticEst.SmoothOpen f → Work.Spaces.HkMem α 4 f → b ≤ 2 →
      ∀ z : ℝ, 0 < z →
        (∫ θ in Work.Spaces.Iθ,
            (Work.Spaces.DzIter b f z θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))
          ≤ C * Work.Spaces.HkSq α 4 f := by
  refine ⟨3, by norm_num, ?_⟩
  intro α f b hα hα1 hF hmem hb z hz
  obtain ⟨hswap, hGint, hGslice⟩ := Work.FTS.TransportS.SupDzAux.avgHkSqSwap α f hF hmem
  -- almost every angle is interior
  have haeθ : ∀ᵐ σ ∂(volume.restrict Work.Spaces.Iθ), σ ∈ Set.Ioo 0 (π / 2) := by
    rw [MeasureTheory.ae_restrict_iff' (s := Work.Spaces.Iθ) measurableSet_Icc]
    filter_upwards [MeasureTheory.Ioo_ae_eq_Icc (μ := volume) (a := (0 : ℝ)) (b := π / 2)]
      with σ h
    exact fun hmem' => h.mpr hmem'
  -- the window bound, for every radius `R₀ ≥ z`
  have hbound : ∀ R₀ : ℝ, z ≤ R₀ →
      (∫ θ in Work.Spaces.Iθ, (Work.Spaces.DzIter b f z θ) ^ 2
          * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))
        ≤ (2 + 2 / R₀) * Work.Spaces.HkSq α 4 f := by
    intro R₀ hR
    have hRpos : 0 < R₀ := lt_of_lt_of_le hz hR
    have hz2R : z ≤ 2 * R₀ := by linarith
    have hR2R : R₀ ≤ 2 * R₀ := by linarith
    have hσbound : ∀ σ : ℝ, σ ∈ Set.Ioo 0 (π / 2) →
        IntegrableOn (fun s => Work.Spaces.HkIntegrand α 4 f s σ) Work.Spaces.Iz →
        (Work.Spaces.DzIter b f z σ) ^ 2 * (Real.sin (2 * σ)) ^ (-(Work.Spaces.eta))
          ≤ (2 + 2 / R₀) * ∫ s in Work.Spaces.Iz, Work.Spaces.HkIntegrand α 4 f s σ := by
      intro σ hσ hσint
      have hsinσ : 0 < Real.sin (2 * σ) := sin_two_pos_of_mem_Ioo hσ
      have hlam : 0 ≤ (Real.sin (2 * σ)) ^ (-(Work.Spaces.eta)) :=
        Real.rpow_nonneg (le_of_lt hsinσ) _
      -- the hypotheses of the one-dimensional window inequality
      have hderiv : ∀ x ∈ Set.Icc z (2 * R₀),
          HasDerivAt (fun x : ℝ => Work.Spaces.DzIter b f x σ)
            (Work.Spaces.pz (Work.Spaces.DzIter b f) x σ) x :=
        fun x hx => hF.hasDerivAt_slice_DzIter b hσ (lt_of_lt_of_le hz hx.1)
      have hcont : ContinuousOn (fun x : ℝ => Work.Spaces.DzIter b f x σ)
          (Set.Icc R₀ (2 * R₀)) :=
        ((hF.DzIter b).curry_z hσ).continuousOn.mono (fun x hx => lt_of_lt_of_le hRpos hx.1)
      have hcont' : ContinuousOn
          (fun x : ℝ => Work.Spaces.pz (Work.Spaces.DzIter b f) x σ)
          (Set.Icc z (2 * R₀)) :=
        (((hF.DzIter b).pz).curry_z hσ).continuousOn.mono
          (fun x hx => lt_of_lt_of_le hz hx.1)
      have hint : IntegrableOn
          (fun x : ℝ => (Work.Spaces.DzIter b f x σ) ^ 2) (Set.Icc R₀ (2 * R₀)) :=
        (hcont.pow 2).integrableOn_Icc
      have hwin := Work.FTS.TransportS.half_line_window_bound
        (h := fun x : ℝ => Work.Spaces.DzIter b f x σ)
        (h' := fun x : ℝ => Work.Spaces.pz (Work.Spaces.DzIter b f) x σ)
        hz hR hderiv hcont hcont' hint
      -- continuity of the relevant slices
      have hcontW : ContinuousOn
          (fun x : ℝ => x * Work.Spaces.pz (Work.Spaces.DzIter b f) x σ * Work.Spaces.w x)
          (Set.Icc z (2 * R₀)) := by
        refine ContinuousOn.mul (ContinuousOn.mul continuousOn_id hcont') ?_
        refine ContinuousOn.div ((continuousOn_const.add continuousOn_id).pow 2)
          (continuousOn_id.pow 2) ?_
        intro x hx
        exact pow_ne_zero 2 (ne_of_gt (lt_of_lt_of_le hz hx.1))
      have hHkcont : ContinuousOn (fun x : ℝ => Work.Spaces.HkIntegrand α 4 f x σ)
          (Set.Icc z (2 * R₀)) := by
        have hmap : MapsTo (fun x : ℝ => (x, σ)) (Set.Icc z (2 * R₀))
            Work.FTS.EllipticEst.Q0 :=
          fun x hx => Work.FTS.EllipticEst.mem_Q0.mpr ⟨lt_of_lt_of_le hz hx.1, hσ.1, hσ.2⟩
        have hc := (hF.continuousOn_HkIntegrand α 4).comp
          (continuousOn_id.prodMk continuousOn_const) hmap
        simpa only [Function.comp_def, id_eq] using hc
      -- interval integrability
      have hIntL1 : IntervalIntegrable
          (fun x : ℝ => (Real.sin (2 * σ)) ^ (-(Work.Spaces.eta))
            * (x * Work.Spaces.pz (Work.Spaces.DzIter b f) x σ * Work.Spaces.w x) ^ 2)
          volume z (2 * R₀) := by
        refine (show ContinuousOn (fun x : ℝ => (Real.sin (2 * σ)) ^ (-(Work.Spaces.eta))
            * (x * Work.Spaces.pz (Work.Spaces.DzIter b f) x σ * Work.Spaces.w x) ^ 2)
            (Set.uIcc z (2 * R₀)) from ?_).intervalIntegrable
        rw [Set.uIcc_of_le hz2R]
        exact ContinuousOn.mul continuousOn_const (hcontW.pow 2)
      have hIntR1 : IntervalIntegrable (fun x : ℝ => Work.Spaces.HkIntegrand α 4 f x σ)
          volume z (2 * R₀) := by
        refine (show ContinuousOn (fun x : ℝ => Work.Spaces.HkIntegrand α 4 f x σ)
          (Set.uIcc z (2 * R₀)) from ?_).intervalIntegrable
        rw [Set.uIcc_of_le hz2R]
        exact hHkcont
      have hIntL2 : IntervalIntegrable
          (fun x : ℝ => (Real.sin (2 * σ)) ^ (-(Work.Spaces.eta))
            * (Work.Spaces.DzIter b f x σ) ^ 2) volume R₀ (2 * R₀) := by
        refine (show ContinuousOn (fun x : ℝ => (Real.sin (2 * σ)) ^ (-(Work.Spaces.eta))
            * (Work.Spaces.DzIter b f x σ) ^ 2) (Set.uIcc R₀ (2 * R₀)) from ?_).intervalIntegrable
        rw [Set.uIcc_of_le hR2R]
        exact ContinuousOn.mul continuousOn_const (hcont.pow 2)
      have hIntR2 : IntervalIntegrable (fun x : ℝ => Work.Spaces.HkIntegrand α 4 f x σ)
          volume R₀ (2 * R₀) := by
        refine (show ContinuousOn (fun x : ℝ => Work.Spaces.HkIntegrand α 4 f x σ)
          (Set.uIcc R₀ (2 * R₀)) from ?_).intervalIntegrable
        rw [Set.uIcc_of_le hR2R]
        exact hHkcont.mono (fun x hx => ⟨le_trans hR hx.1, hx.2⟩)
      -- pointwise domination of the two window integrands
      have hptA : ∀ x ∈ Set.Icc z (2 * R₀),
          (Real.sin (2 * σ)) ^ (-(Work.Spaces.eta))
            * (x * Work.Spaces.pz (Work.Spaces.DzIter b f) x σ * Work.Spaces.w x) ^ 2
            ≤ Work.Spaces.HkIntegrand α 4 f x σ := by
        intro x hx
        have hcomm : x * Work.Spaces.pz (Work.Spaces.DzIter b f) x σ
            = Work.Spaces.DzIter (b + 1) f x σ := rfl
        rw [hcomm]
        have h1 : (Real.sin (2 * σ)) ^ (-(Work.Spaces.eta))
            * (Work.Spaces.DzIter (b + 1) f x σ * Work.Spaces.w x) ^ 2
            = (Work.Spaces.DzIter (b + 1) f x σ * Work.Spaces.w x) ^ 2
              * (Real.sin (2 * σ)) ^ (-(Work.Spaces.eta)) := by ring
        rw [h1]
        exact dzIter_mul_w_sq_mul_rpow_neg_le_HkIntegrand α f hsinσ (b + 1) (by omega)
      have hptB : ∀ x ∈ Set.Icc R₀ (2 * R₀),
          (Real.sin (2 * σ)) ^ (-(Work.Spaces.eta))
            * (Work.Spaces.DzIter b f x σ) ^ 2 ≤ Work.Spaces.HkIntegrand α 4 f x σ := by
        intro x hx
        have h1 : (Real.sin (2 * σ)) ^ (-(Work.Spaces.eta))
            * (Work.Spaces.DzIter b f x σ) ^ 2
            = (Work.Spaces.DzIter b f x σ) ^ 2
              * (Real.sin (2 * σ)) ^ (-(Work.Spaces.eta)) := by ring
        rw [h1]
        exact dzIter_sq_mul_rpow_neg_le_HkIntegrand α f (lt_of_lt_of_le hRpos hx.1) hsinσ b
          (by omega)
      -- the two window integrals are dominated by the full radial integral
      have hbigA : ∫ x in z..(2 * R₀), Work.Spaces.HkIntegrand α 4 f x σ
          ≤ ∫ s in Work.Spaces.Iz, Work.Spaces.HkIntegrand α 4 f s σ := by
        rw [intervalIntegral.integral_of_le hz2R]
        refine MeasureTheory.setIntegral_mono_set hσint
          (Eventually.of_forall fun x => Work.Spaces.HkIntegrand_nonneg α 4 f x σ) ?_
        exact Eventually.of_forall fun x hx => le_of_lt (lt_trans hz hx.1)
      have hbigB : ∫ x in R₀..(2 * R₀), Work.Spaces.HkIntegrand α 4 f x σ
          ≤ ∫ s in Work.Spaces.Iz, Work.Spaces.HkIntegrand α 4 f s σ := by
        rw [intervalIntegral.integral_of_le hR2R]
        refine MeasureTheory.setIntegral_mono_set hσint
          (Eventually.of_forall fun x => Work.Spaces.HkIntegrand_nonneg α 4 f x σ) ?_
        exact Eventually.of_forall fun x hx => le_of_lt (lt_trans hRpos hx.1)
      have hmonoA := intervalIntegral.integral_mono_on hz2R hIntL1 hIntR1 hptA
      have hmonoB := intervalIntegral.integral_mono_on hR2R hIntL2 hIntR2 hptB
      -- the weight factors out of the interval integrals
      have hAeq : (Real.sin (2 * σ)) ^ (-(Work.Spaces.eta))
            * (∫ x in z..(2 * R₀), (x * Work.Spaces.pz (Work.Spaces.DzIter b f) x σ
                * Work.Spaces.w x) ^ 2)
          = ∫ x in z..(2 * R₀), (Real.sin (2 * σ)) ^ (-(Work.Spaces.eta))
              * (x * Work.Spaces.pz (Work.Spaces.DzIter b f) x σ * Work.Spaces.w x) ^ 2 :=
        (intervalIntegral.integral_const_mul _ _).symm
      have hBeq : (Real.sin (2 * σ)) ^ (-(Work.Spaces.eta))
            * (∫ x in R₀..(2 * R₀), (Work.Spaces.DzIter b f x σ) ^ 2)
          = ∫ x in R₀..(2 * R₀), (Real.sin (2 * σ)) ^ (-(Work.Spaces.eta))
              * (Work.Spaces.DzIter b f x σ) ^ 2 :=
        (intervalIntegral.integral_const_mul _ _).symm
      calc (Work.Spaces.DzIter b f z σ) ^ 2 * (Real.sin (2 * σ)) ^ (-(Work.Spaces.eta))
          = (Real.sin (2 * σ)) ^ (-(Work.Spaces.eta))
              * (Work.Spaces.DzIter b f z σ) ^ 2 := by ring
        _ ≤ (Real.sin (2 * σ)) ^ (-(Work.Spaces.eta))
              * (2 * (∫ x in z..(2 * R₀),
                    (x * Work.Spaces.pz (Work.Spaces.DzIter b f) x σ
                      * Work.Spaces.w x) ^ 2)
                + (2 / R₀) * ∫ x in R₀..(2 * R₀),
                    (Work.Spaces.DzIter b f x σ) ^ 2) :=
              mul_le_mul_of_nonneg_left hwin hlam
        _ = 2 * ((Real.sin (2 * σ)) ^ (-(Work.Spaces.eta))
                * (∫ x in z..(2 * R₀), (x * Work.Spaces.pz (Work.Spaces.DzIter b f) x σ
                    * Work.Spaces.w x) ^ 2))
              + (2 / R₀) * ((Real.sin (2 * σ)) ^ (-(Work.Spaces.eta))
                * (∫ x in R₀..(2 * R₀), (Work.Spaces.DzIter b f x σ) ^ 2)) := by ring
        _ = 2 * (∫ x in z..(2 * R₀), (Real.sin (2 * σ)) ^ (-(Work.Spaces.eta))
                * (x * Work.Spaces.pz (Work.Spaces.DzIter b f) x σ
                    * Work.Spaces.w x) ^ 2)
              + (2 / R₀) * (∫ x in R₀..(2 * R₀), (Real.sin (2 * σ)) ^ (-(Work.Spaces.eta))
                  * (Work.Spaces.DzIter b f x σ) ^ 2) := by
              rw [hAeq, hBeq]
        _ ≤ 2 * (∫ s in Work.Spaces.Iz, Work.Spaces.HkIntegrand α 4 f s σ)
              + (2 / R₀) * (∫ s in Work.Spaces.Iz, Work.Spaces.HkIntegrand α 4 f s σ) :=
              add_le_add (mul_le_mul_of_nonneg_left (le_trans hmonoA hbigA) (by norm_num))
                (mul_le_mul_of_nonneg_left (le_trans hmonoB hbigB) (by positivity))
        _ = (2 + 2 / R₀) * (∫ s in Work.Spaces.Iz, Work.Spaces.HkIntegrand α 4 f s σ) := by
              ring
    -- integrate the a.e. pointwise bound
    have hle : (fun σ : ℝ => (Work.Spaces.DzIter b f z σ) ^ 2
          * (Real.sin (2 * σ)) ^ (-(Work.Spaces.eta)))
        ≤ᵐ[volume.restrict Work.Spaces.Iθ]
        (fun σ : ℝ => (2 + 2 / R₀) * ∫ s in Work.Spaces.Iz,
          Work.Spaces.HkIntegrand α 4 f s σ) := by
      filter_upwards [hGslice, haeθ] with σ hσint hσθ
      exact hσbound σ hσθ hσint
    have hLI : Integrable (fun σ : ℝ => (Work.Spaces.DzIter b f z σ) ^ 2
        * (Real.sin (2 * σ)) ^ (-(Work.Spaces.eta)))
        (volume.restrict Work.Spaces.Iθ) :=
      integrableOn_dzIter_sq_mul_rpow_neg α f hF hmem b (by omega) hz
    calc (∫ θ in Work.Spaces.Iθ, (Work.Spaces.DzIter b f z θ) ^ 2
            * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))
        ≤ ∫ σ in Work.Spaces.Iθ, (2 + 2 / R₀) * ∫ s in Work.Spaces.Iz,
            Work.Spaces.HkIntegrand α 4 f s σ :=
          MeasureTheory.integral_mono_ae hLI (hGint.const_mul _) hle
      _ = (2 + 2 / R₀) * (∫ σ in Work.Spaces.Iθ, ∫ s in Work.Spaces.Iz,
            Work.Spaces.HkIntegrand α 4 f s σ) := MeasureTheory.integral_const_mul _ _
      _ = (2 + 2 / R₀) * Work.Spaces.HkSq α 4 f := by rw [hswap]
  -- take `R₀ = max z 2`, so that the coefficient is at most `3`
  have hzmax : z ≤ max z 2 := le_max_left z 2
  have hbnd := hbound (max z 2) hzmax
  have hpos : 0 < max z 2 := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 2) (le_max_right z 2)
  have h2max : 2 ≤ max z 2 := le_max_right z 2
  have hcoef : 2 + 2 / max z 2 ≤ 3 := by
    have h : 2 / max z 2 ≤ 1 := by
      rw [div_le_one hpos]
      exact h2max
    linarith
  calc (∫ θ in Work.Spaces.Iθ, (Work.Spaces.DzIter b f z θ) ^ 2
        * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))
      ≤ (2 + 2 / max z 2) * Work.Spaces.HkSq α 4 f := hbnd
    _ ≤ 3 * Work.Spaces.HkSq α 4 f :=
        mul_le_mul_of_nonneg_right hcoef (Work.Spaces.HkSq_nonneg α 4 f)

end Work.FTS.TransportS.SupDzWeighted
