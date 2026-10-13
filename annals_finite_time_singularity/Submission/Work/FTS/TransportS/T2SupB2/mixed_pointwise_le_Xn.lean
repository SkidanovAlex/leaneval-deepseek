/-
Copyright: work module for the Elgindi finite-time singularity project.

# Pointwise bounds on the mixed slots of order `≤ 2` by the `ℋ⁴`-norm

For a datum `f` which is `C^∞` on the open quadrant (`Work.FTS.EllipticEst.SmoothOpen`) and
honestly in `ℋ⁴` (`Work.Spaces.HkMem α 4 f`), every mixed derivative `D_z^j D_θ^i f` with
`1 ≤ i`, `i + j ≤ 2` is bounded pointwise on the open quadrant by a universal multiple of
`Xn α f = |f|_{ℋ⁴}`:

  `|D_z^j D_θ^i f(z,θ)| ≤ C · |f|_{ℋ⁴}`   (`z > 0`, `0 < θ < π/2`),

with a constant `C` independent of `α ∈ (0,1]`, of `f` and of `(z,θ)`.  This is item **(P)**
of `Submission/Work/FTS/TransportS/NOTES_t2SupF_b2_analysis.md`; it is the `α`-uniform
pointwise bound that the transport rows consume.

## Route (radial Hardy window at fixed angle + the angular total-variation bound)

Fix the angle `θ ∈ (0,π/2)`, put `h(x) := D_z^jD_θ^i f(x,θ)` and `R := max z 2`.  The window
form of the radial Hardy inequality (`Work.FTS.TransportS.half_line_window_bound`) says, for
`z ≤ R`,

  `h(z)² ≤ 2 ∫_z^{2R} (x h'(x) w(x))² dx + (2/R) ∫_R^{2R} h(x)² dx`,

and the identity `x · ∂_x(D_z^jD_θ^i f) = D_z^{j+1}D_θ^i f` makes the first integrand the
`(j+1,i)` mixed slot weighted by `w`.  Both integrands are then dominated *pointwise in `x`*
by the angular slice of the `ℋ⁴`-integrand, by the angular total-variation bound
`Work.FTS.TransportS.T2SupB2.slice_bound`:

  `(D_z^jD_θ^if(x,θ))² w(x)² ≤ 5 ∫_{Iθ} HkIntegrand α 4 f x θ'`     (`1 ≤ i`, `i+j+1 ≤ 4`),

proved from the equality `D_θ^{i+1}f = sin(2θ)·∂_θ(D_θ^if)` and an angular Cauchy–Schwarz; the
admissible exponents are `γ ≥ 1` for *both* slots of the mixed chain, which is exactly why the
mixed slots (and not the pure ones, `i = 0`) are `α`-uniform.  The hypothesis `i + j ≤ 2` is
what makes the slot `(j+1,i)` — of total order `i+j+1 ≤ 3 ≤ 4` — legal.

Integrating this domination in `x` and using `HkMem α 4 f` (finiteness of `∫_z ∫_θ` of the
integrand) bounds both window terms by `5 · HkSq α 4 f`, so

  `(D_z^jD_θ^if(z,θ))² ≤ 15 · HkSq α 4 f`,  hence  `|D_z^jD_θ^if(z,θ)| ≤ √15 · |f|_{ℋ⁴}`,

uniformly in `α`, `f` and `(z,θ)`.

§1–§2 contain the ingredients of an independent *angular Agmon* route to the same statement:
the angular shift identity for mixed slots, the `θ`-integrability of a slot with its own
weight and the corresponding integral identity.  Feeding a one-dimensional `sup`-inequality
for the `C¹`-slice `v := D_z^jD_θ^i f(z,·)` with the two single-slot bounds of
`Work.FTS.TransportS.T2SupB2.mixed_slice_z_uniform` (device **(Z)**) into the same assembly
yields the claim with the constant `√(40·3)` as well.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.FTS.TransportS.T2SupB2.mixed_slice_theta_uniform
import Submission.Work.FTS.TransportS.SupDzAux.HalfLineWindow
import Submission.Work.FTS.EllipticEst.SliceDecompDefs
import Submission.Work.FTS.TransportS.sup_dz_le_hk
import Submission.Work.FTS.Vocab

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.TransportS.T2SupB2

set_option autoImplicit false
set_option maxHeartbeats 1600000

/-! ## 1. The angular shift identity for mixed slots -/

/-- `sin(2θ) · ∂_θ(D_z^jD_θ^i f) = D_z^jD_θ^{i+1} f` on the open quadrant, for a datum which is
`C^∞` there.  (The `D_θ`-iterate form of `Work.FTS.TransportS.mixed_one_eq_sin_mul_pth`.) -/
theorem sin_mul_pth_mixed {f : ℝ → ℝ → ℝ} (hF : Work.FTS.EllipticEst.SmoothOpen f) (j i : ℕ)
    {z θ : ℝ} (hz : 0 < z) (hθ : θ ∈ Set.Ioo 0 (π / 2)) :
    Real.sin (2 * θ) * Work.Spaces.pth (Work.Spaces.mixed j i f) z θ
      = Work.Spaces.mixed j (i + 1) f z θ := by
  have hp : (z, θ) ∈ Work.FTS.EllipticEst.Q0 :=
    Work.FTS.EllipticEst.mem_Q0.mpr ⟨hz, hθ.1, hθ.2⟩
  have h2 : Work.Spaces.pth (Work.Spaces.DzIter j (Work.Spaces.DthIter i f)) z θ
      = Work.Spaces.DzIter j (Work.Spaces.pth (Work.Spaces.DthIter i f)) z θ :=
    Work.FTS.EllipticEst.ThetaU.OpenSliceAux.pth_DzIter_eqOn_of_isOpen
      Work.FTS.EllipticEst.isOpen_Q0
      ((Work.FTS.EllipticEst.smoothOpen_iff_forall (Work.Spaces.DthIter i f)).mp
        (hF.DthIter i)) j hp
  have h3 : Real.sin (2 * θ)
        * Work.Spaces.DzIter j (Work.Spaces.pth (Work.Spaces.DthIter i f)) z θ
      = Work.Spaces.DzIter j
          (fun z θ' => Real.sin (2 * θ') * Work.Spaces.pth (Work.Spaces.DthIter i f) z θ')
          z θ :=
    (Work.FTS.TransportS.DzIter_const_mul j (fun θ' => Real.sin (2 * θ'))
      (Work.Spaces.pth (Work.Spaces.DthIter i f)) z θ).symm
  calc Real.sin (2 * θ) * Work.Spaces.pth (Work.Spaces.mixed j i f) z θ
      = Real.sin (2 * θ)
          * Work.Spaces.pth (Work.Spaces.DzIter j (Work.Spaces.DthIter i f)) z θ := rfl
    _ = Real.sin (2 * θ)
          * Work.Spaces.DzIter j (Work.Spaces.pth (Work.Spaces.DthIter i f)) z θ := by rw [h2]
    _ = Work.Spaces.DzIter j
          (fun z θ' => Real.sin (2 * θ') * Work.Spaces.pth (Work.Spaces.DthIter i f) z θ')
          z θ := h3
    _ = Work.Spaces.mixed j (i + 1) f z θ := rfl

/-! ## 2. Integrability of the two weighted angular slices -/

/-- For `z > 0`, the `(j,i)` mixed slot with its own weight `sin(2θ)^{-γ}` is `θ`-integrable
on `Iθ`, as soon as the slot belongs to `HkIntegrand α 4 f`.  (The transfer from
`Work.FTS.EllipticEst.integrableOn_mixedSummand`, whose integrand carries the weight `Wt`.) -/
theorem integrableOn_mixed_sq_rpow {α : ℝ} {f : ℝ → ℝ → ℝ}
    (hF : Work.FTS.EllipticEst.SmoothOpen f) (hmem : Work.Spaces.HkMem α 4 f)
    (j i : ℕ) (hi : 1 ≤ i) (hij : i + j ≤ 4) {z : ℝ} (hz : 0 < z) :
    MeasureTheory.IntegrableOn
      (fun t => (Work.Spaces.mixed j i f z t) ^ 2
        * (Real.sin (2 * t)) ^ (-(Work.Spaces.gam α))) Work.Spaces.Iθ := by
  have hbase := Work.FTS.EllipticEst.integrableOn_mixedSummand α 4 hF hmem i j hi hij
    (z := z) (Set.mem_Ici.mpr (le_of_lt hz))
  have hw : (Work.Spaces.w z) ≠ 0 :=
    ne_of_gt (lt_of_lt_of_le zero_lt_one (Work.FTS.TransportS.one_le_w hz))
  have hae : (fun t => (Work.Spaces.mixed j i f z t) ^ 2
        * (Real.sin (2 * t)) ^ (-(Work.Spaces.gam α)))
      =ᵐ[MeasureTheory.volume.restrict Work.Spaces.Iθ]
      (fun t => (Work.Spaces.mixed j i f z t * Work.Spaces.Wt α z t) ^ 2
        * ((Work.Spaces.w z) ^ 2)⁻¹) := by
    rw [Work.FTS.EllipticEst.restrict_Iθ_eq_restrict_Ioo]
    refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioo (fun t ht => ?_)
    show (Work.Spaces.mixed j i f z t) ^ 2 * (Real.sin (2 * t)) ^ (-(Work.Spaces.gam α))
      = (Work.Spaces.mixed j i f z t * Work.Spaces.Wt α z t) ^ 2
        * ((Work.Spaces.w z) ^ 2)⁻¹
    have hs : 0 < Real.sin (2 * t) :=
      Real.sin_pos_of_pos_of_lt_pi (by linarith [ht.1]) (by linarith [ht.2, Real.pi_pos])
    have hw2 : ((Work.Spaces.w z) ^ 2) ≠ 0 := pow_ne_zero 2 hw
    rw [mul_pow, Work.H2.T1Q.Wt_sq_eq α z t hs]
    field_simp
  exact (hbase.mul_const _).congr hae.symm

/-- For `z > 0`, the `∂_θ`-slice of a mixed slot with the weight `sin(2θ)^{2-γ}` is
`θ`-integrable: it equals the next slot `(j,i+1)` with the weight `sin(2θ)^{-γ}`. -/
theorem integrableOn_pth_sq_rpow {α : ℝ} {f : ℝ → ℝ → ℝ}
    (hF : Work.FTS.EllipticEst.SmoothOpen f) (hmem : Work.Spaces.HkMem α 4 f)
    (j i : ℕ) (hij : i + j ≤ 3) {z : ℝ} (hz : 0 < z) :
    MeasureTheory.IntegrableOn
      (fun t => (Work.Spaces.pth (Work.Spaces.mixed j i f) z t) ^ 2
        * (Real.sin (2 * t)) ^ (2 - Work.Spaces.gam α)) Work.Spaces.Iθ := by
  refine (integrableOn_mixed_sq_rpow hF hmem j (i + 1) (by omega) (by omega) hz).congr ?_
  rw [Work.FTS.EllipticEst.restrict_Iθ_eq_restrict_Ioo]
  refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioo (fun t ht => ?_)
  show (Work.Spaces.mixed j (i + 1) f z t) ^ 2 * (Real.sin (2 * t)) ^ (-(Work.Spaces.gam α))
      = (Work.Spaces.pth (Work.Spaces.mixed j i f) z t) ^ 2
        * (Real.sin (2 * t)) ^ (2 - Work.Spaces.gam α)
  have hs : 0 < Real.sin (2 * t) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith [ht.1]) (by linarith [ht.2, Real.pi_pos])
  have hsplit : (Real.sin (2 * t)) ^ (2 - Work.Spaces.gam α)
      = (Real.sin (2 * t)) ^ 2 * (Real.sin (2 * t)) ^ (-(Work.Spaces.gam α)) := by
    rw [show (2 : ℝ) - Work.Spaces.gam α
        = (2 : ℝ) + (-(Work.Spaces.gam α)) by ring, Real.rpow_add hs, Real.rpow_two]
  rw [← sin_mul_pth_mixed hF j i hz ht, hsplit]
  ring

/-- The integral identity behind the previous lemma: the `∂_θ`-slot with the weight
`sin(2θ)^{2-γ}` integrates to the next mixed slot with the weight `sin(2θ)^{-γ}`. -/
theorem setIntegral_pth_sq_eq {α : ℝ} {f : ℝ → ℝ → ℝ}
    (hF : Work.FTS.EllipticEst.SmoothOpen f) (j i : ℕ) {z : ℝ} (hz : 0 < z) :
    (∫ t in Work.Spaces.Iθ, (Work.Spaces.pth (Work.Spaces.mixed j i f) z t) ^ 2
        * (Real.sin (2 * t)) ^ (2 - Work.Spaces.gam α))
      = ∫ t in Work.Spaces.Iθ, (Work.Spaces.mixed j (i + 1) f z t) ^ 2
        * (Real.sin (2 * t)) ^ (-(Work.Spaces.gam α)) := by
  refine Work.FTS.EllipticEst.setIntegral_Iθ_congr_of_forall_Ioo (fun t ht => ?_)
  show (Work.Spaces.pth (Work.Spaces.mixed j i f) z t) ^ 2
        * (Real.sin (2 * t)) ^ (2 - Work.Spaces.gam α)
      = (Work.Spaces.mixed j (i + 1) f z t) ^ 2 * (Real.sin (2 * t)) ^ (-(Work.Spaces.gam α))
  have hs : 0 < Real.sin (2 * t) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith [ht.1]) (by linarith [ht.2, Real.pi_pos])
  have hsplit : (Real.sin (2 * t)) ^ (2 - Work.Spaces.gam α)
      = (Real.sin (2 * t)) ^ 2 * (Real.sin (2 * t)) ^ (-(Work.Spaces.gam α)) := by
    rw [show (2 : ℝ) - Work.Spaces.gam α
        = (2 : ℝ) + (-(Work.Spaces.gam α)) by ring, Real.rpow_add hs, Real.rpow_two]
  rw [← sin_mul_pth_mixed hF j i hz ht, hsplit]
  ring

/-! ## 3. The pointwise bound -/

theorem mixed_pointwise_le_Xn :
    ∃ C : ℝ, 0 < C ∧ ∀ (α : ℝ) (f : ℝ → ℝ → ℝ), 0 < α → α ≤ 1 →
      Work.FTS.EllipticEst.SmoothOpen f → Work.Spaces.HkMem α 4 f →
      ∀ (j i : ℕ), 1 ≤ i → i + j ≤ 2 → ∀ z θ : ℝ, 0 < z → 0 < θ → θ < π / 2 →
        |Work.Spaces.mixed j i f z θ| ≤ C * Work.FTS.Nonlin.Xn α f := by
  refine ⟨Real.sqrt 15, Real.sqrt_pos_of_pos (by norm_num), ?_⟩
  intro α f hα hα1 hF hmem j i hi hij z θ hz hθ hθ2
  have hθI : θ ∈ Set.Ioo 0 (π / 2) := ⟨hθ, hθ2⟩
  set R : ℝ := max z 2 with hRdef
  have hzR : z ≤ R := le_max_left z 2
  have hR2 : (2 : ℝ) ≤ R := le_max_right z 2
  have hRpos : 0 < R := lt_of_lt_of_le (by norm_num) hR2
  have hz2R : z ≤ 2 * R := by linarith
  have hR2R : R ≤ 2 * R := by linarith
  have hHknn : 0 ≤ Work.Spaces.HkSq α 4 f := Work.Spaces.HkSq_nonneg α 4 f
  -- hypotheses of the radial window bound
  have hderiv : ∀ x ∈ Set.Icc z (2 * R),
      HasDerivAt (fun x => Work.Spaces.mixed j i f x θ)
        (Work.Spaces.pz (Work.Spaces.mixed j i f) x θ) x :=
    fun x hx => (hF.mixed j i).hasDerivAt_slice hθI (lt_of_lt_of_le hz hx.1)
  have hcont : ContinuousOn (fun x => Work.Spaces.mixed j i f x θ) (Set.Icc R (2 * R)) :=
    ((hF.mixed j i).curry_z hθI).continuousOn.mono
      (fun x hx => lt_of_lt_of_le hRpos hx.1)
  have hcont' : ContinuousOn (fun x => Work.Spaces.pz (Work.Spaces.mixed j i f) x θ)
      (Set.Icc z (2 * R)) :=
    (((hF.mixed j i).pz).curry_z hθI).continuousOn.mono
      (fun x hx => lt_of_lt_of_le hz hx.1)
  have hint : IntegrableOn (fun x => (Work.Spaces.mixed j i f x θ) ^ 2)
      (Set.Icc R (2 * R)) := (hcont.pow 2).integrableOn_Icc
  have hwin := Work.FTS.TransportS.half_line_window_bound hz hzR hderiv hcont hcont' hint
  have hwin' : (Work.Spaces.mixed j i f z θ) ^ 2
      ≤ 2 * (∫ x in z..(2 * R),
            (x * Work.Spaces.pz (Work.Spaces.mixed j i f) x θ * Work.Spaces.w x) ^ 2)
        + (2 / R) * ∫ x in R..(2 * R), (Work.Spaces.mixed j i f x θ) ^ 2 := hwin
  -- the weighted-derivative term
  have hwcont1 : ContinuousOn (fun x : ℝ => Work.Spaces.w x) (Set.Icc z (2 * R)) := by
    change ContinuousOn (fun x : ℝ => (1 + x) ^ 2 / x ^ 2) (Set.Icc z (2 * R))
    refine ContinuousOn.div ((continuousOn_const.add continuousOn_id).pow 2)
      (continuousOn_id.pow 2) ?_
    intro x hx
    exact pow_ne_zero 2 (ne_of_gt (lt_of_lt_of_le hz hx.1))
  have hmcont1 : ContinuousOn (fun x : ℝ => Work.Spaces.mixed (j + 1) i f x θ)
      (Set.Icc z (2 * R)) :=
    (((hF.mixed (j + 1) i).curry_z hθI).continuousOn).mono
      (fun x hx => lt_of_lt_of_le hz hx.1)
  have hIntL1 : IntervalIntegrable
      (fun x => (Work.Spaces.mixed (j + 1) i f x θ * Work.Spaces.w x) ^ 2)
      volume z (2 * R) := by
    refine (show ContinuousOn
      (fun x => (Work.Spaces.mixed (j + 1) i f x θ * Work.Spaces.w x) ^ 2)
      (Set.uIcc z (2 * R)) from ?_).intervalIntegrable
    rw [Set.uIcc_of_le hz2R]
    exact (hmcont1.mul hwcont1).pow 2
  have hIntR1 : IntervalIntegrable
      (fun x => 5 * ∫ θ' in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 f x θ')
      volume z (2 * R) :=
    (show IntegrableOn (fun x => 5 * ∫ θ' in Work.Spaces.Iθ,
        Work.Spaces.HkIntegrand α 4 f x θ') (Set.uIcc z (2 * R)) volume from by
      rw [Set.uIcc_of_le hz2R]
      exact (hmem.2.mono_set (fun x hx => le_of_lt (lt_of_lt_of_le hz hx.1))).const_mul
        5).intervalIntegrable
  have hpt1 : ∀ x ∈ Set.Icc z (2 * R),
      (Work.Spaces.mixed (j + 1) i f x θ * Work.Spaces.w x) ^ 2
        ≤ 5 * ∫ θ' in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 f x θ' := by
    intro x hx
    have hx0 : 0 < x := lt_of_lt_of_le hz hx.1
    have h := slice_bound hα hα1 hF hmem (j := j + 1) (i := i) hi (by omega) hx0 hθI
    have h2 : (Work.Spaces.mixed (j + 1) i f x θ * Work.Spaces.w x) ^ 2
        = (Work.Spaces.mixed (j + 1) i f x θ) ^ 2 * (Work.Spaces.w x) ^ 2 := by ring
    rw [h2]; exact h
  have hmono1 : (∫ x in z..(2 * R), (Work.Spaces.mixed (j + 1) i f x θ
        * Work.Spaces.w x) ^ 2)
      ≤ 5 * ∫ x in z..(2 * R),
          (∫ θ' in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 f x θ') := by
    rw [← intervalIntegral.integral_const_mul]
    exact intervalIntegral.integral_mono_on hz2R hIntL1 hIntR1 hpt1
  have hbig1 : (∫ x in z..(2 * R),
        (∫ θ' in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 f x θ'))
      ≤ Work.Spaces.HkSq α 4 f := by
    rw [intervalIntegral.integral_of_le hz2R]
    refine setIntegral_mono_set hmem.2 (Eventually.of_forall fun x => ?_)
      (Eventually.of_forall fun x hx => ?_)
    · exact integral_nonneg fun θ' => Work.Spaces.HkIntegrand_nonneg α 4 f x θ'
    · exact le_of_lt (lt_trans hz hx.1)
  have hcongr1 : (∫ x in z..(2 * R), (x * Work.Spaces.pz (Work.Spaces.mixed j i f) x θ
        * Work.Spaces.w x) ^ 2)
      = ∫ x in z..(2 * R), (Work.Spaces.mixed (j + 1) i f x θ * Work.Spaces.w x) ^ 2 := by
    refine intervalIntegral.integral_congr fun x _ => ?_
    rfl
  have hstep1 : (∫ x in z..(2 * R), (x * Work.Spaces.pz (Work.Spaces.mixed j i f) x θ
        * Work.Spaces.w x) ^ 2) ≤ 5 * Work.Spaces.HkSq α 4 f := by
    rw [hcongr1]
    calc (∫ x in z..(2 * R), (Work.Spaces.mixed (j + 1) i f x θ * Work.Spaces.w x) ^ 2)
        ≤ 5 * ∫ x in z..(2 * R),
            (∫ θ' in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 f x θ') := hmono1
      _ ≤ 5 * Work.Spaces.HkSq α 4 f := by linarith
  -- the window average term
  have hIntL2 : IntervalIntegrable (fun x => (Work.Spaces.mixed j i f x θ) ^ 2)
      volume R (2 * R) := by
    refine (show ContinuousOn (fun x => (Work.Spaces.mixed j i f x θ) ^ 2)
      (Set.uIcc R (2 * R)) from ?_).intervalIntegrable
    rw [Set.uIcc_of_le hR2R]
    exact hcont.pow 2
  have hwcont2 : ContinuousOn (fun x : ℝ => Work.Spaces.w x) (Set.Icc R (2 * R)) := by
    change ContinuousOn (fun x : ℝ => (1 + x) ^ 2 / x ^ 2) (Set.Icc R (2 * R))
    refine ContinuousOn.div ((continuousOn_const.add continuousOn_id).pow 2)
      (continuousOn_id.pow 2) ?_
    intro x hx
    exact pow_ne_zero 2 (ne_of_gt (lt_of_lt_of_le hRpos hx.1))
  have hIntM2 : IntervalIntegrable
      (fun x => (Work.Spaces.mixed j i f x θ) ^ 2 * (Work.Spaces.w x) ^ 2)
      volume R (2 * R) := by
    refine (show ContinuousOn
      (fun x => (Work.Spaces.mixed j i f x θ) ^ 2 * (Work.Spaces.w x) ^ 2)
      (Set.uIcc R (2 * R)) from ?_).intervalIntegrable
    rw [Set.uIcc_of_le hR2R]
    exact (hcont.pow 2).mul (hwcont2.pow 2)
  have hIntR2 : IntervalIntegrable
      (fun x => 5 * ∫ θ' in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 f x θ')
      volume R (2 * R) :=
    (show IntegrableOn (fun x => 5 * ∫ θ' in Work.Spaces.Iθ,
        Work.Spaces.HkIntegrand α 4 f x θ') (Set.uIcc R (2 * R)) volume from by
      rw [Set.uIcc_of_le hR2R]
      exact (hmem.2.mono_set (fun x hx => le_of_lt (lt_of_lt_of_le hRpos hx.1))).const_mul
        5).intervalIntegrable
  have hpt2a : ∀ x ∈ Set.Icc R (2 * R),
      (Work.Spaces.mixed j i f x θ) ^ 2
        ≤ (Work.Spaces.mixed j i f x θ) ^ 2 * (Work.Spaces.w x) ^ 2 := by
    intro x hx
    have hx0 : 0 < x := lt_of_lt_of_le hRpos hx.1
    have h1 : 1 ≤ (Work.Spaces.w x) ^ 2 :=
      one_le_pow₀ (Work.FTS.TransportS.one_le_w hx0)
    nlinarith [sq_nonneg (Work.Spaces.mixed j i f x θ)]
  have hpt2b : ∀ x ∈ Set.Icc R (2 * R),
      (Work.Spaces.mixed j i f x θ) ^ 2 * (Work.Spaces.w x) ^ 2
        ≤ 5 * ∫ θ' in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 f x θ' := by
    intro x hx
    have hx0 : 0 < x := lt_of_lt_of_le hRpos hx.1
    exact slice_bound hα hα1 hF hmem (j := j) (i := i) hi (by omega) hx0 hθI
  have hmono2a : (∫ x in R..(2 * R), (Work.Spaces.mixed j i f x θ) ^ 2)
      ≤ ∫ x in R..(2 * R),
          (Work.Spaces.mixed j i f x θ) ^ 2 * (Work.Spaces.w x) ^ 2 :=
    intervalIntegral.integral_mono_on hR2R hIntL2 hIntM2 hpt2a
  have hmono2b : (∫ x in R..(2 * R),
        (Work.Spaces.mixed j i f x θ) ^ 2 * (Work.Spaces.w x) ^ 2)
      ≤ 5 * ∫ x in R..(2 * R),
          (∫ θ' in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 f x θ') := by
    rw [← intervalIntegral.integral_const_mul]
    exact intervalIntegral.integral_mono_on hR2R hIntM2 hIntR2 hpt2b
  have hbig2 : (∫ x in R..(2 * R),
        (∫ θ' in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 f x θ'))
      ≤ Work.Spaces.HkSq α 4 f := by
    rw [intervalIntegral.integral_of_le hR2R]
    refine setIntegral_mono_set hmem.2 (Eventually.of_forall fun x => ?_)
      (Eventually.of_forall fun x hx => ?_)
    · exact integral_nonneg fun θ' => Work.Spaces.HkIntegrand_nonneg α 4 f x θ'
    · exact le_of_lt (lt_trans hRpos hx.1)
  have hstep2 : (∫ x in R..(2 * R), (Work.Spaces.mixed j i f x θ) ^ 2)
      ≤ 5 * Work.Spaces.HkSq α 4 f := by
    have h1 : 5 * (∫ x in R..(2 * R),
          (∫ θ' in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 f x θ'))
        ≤ 5 * Work.Spaces.HkSq α 4 f := by linarith
    linarith [hmono2a, hmono2b, h1]
  -- conclusion
  have hYnn : 0 ≤ ∫ x in R..(2 * R), (Work.Spaces.mixed j i f x θ) ^ 2 :=
    intervalIntegral.integral_nonneg hR2R fun x _ => sq_nonneg _
  have hcoef : 2 / R ≤ 1 := by
    rw [div_le_one hRpos]; linarith
  have hcoef2 : (2 / R) * (∫ x in R..(2 * R), (Work.Spaces.mixed j i f x θ) ^ 2)
      ≤ (∫ x in R..(2 * R), (Work.Spaces.mixed j i f x θ) ^ 2) := by
    have h := mul_le_mul_of_nonneg_right hcoef hYnn
    rwa [one_mul] at h
  have hfinal : (Work.Spaces.mixed j i f z θ) ^ 2 ≤ 15 * Work.Spaces.HkSq α 4 f := by
    linarith [hwin', hcoef2, hstep1, hstep2]
  calc |Work.Spaces.mixed j i f z θ| = Real.sqrt ((Work.Spaces.mixed j i f z θ) ^ 2) :=
        (Real.sqrt_sq_eq_abs _).symm
    _ ≤ Real.sqrt (15 * Work.Spaces.HkSq α 4 f) := Real.sqrt_le_sqrt hfinal
    _ = Real.sqrt 15 * Real.sqrt (Work.Spaces.HkSq α 4 f) := Real.sqrt_mul (by norm_num) _
    _ = Real.sqrt 15 * Work.FTS.Nonlin.Xn α f := by
        rw [Work.FTS.Nonlin.Xn, Work.Spaces.HkNorm]

end Work.FTS.TransportS.T2SupB2
