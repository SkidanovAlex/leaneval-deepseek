import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Order.CompletePartialOrder
import Mathlib.Order.Interval.Basic
import Mathlib.Tactic.Have
import Submission.Work.FTS.Vocab
import Submission.Work.Elliptic.Defs
import Submission.Work.Spaces.Defs
import Submission.Work.Elliptic.Gsing_ode
import Submission.Work.Elliptic.GsingFuncs
import Submission.Work.FTS.EllipticEst.HkMem_FstarSin_open
import Submission.Work.FTS.EllipticEst.GbarSin.FstarDzIter_chain_open
import Submission.Work.FTS.EllipticEst.GbarSin.Fstar_local_integrableOn
import Submission.Work.FTS.EllipticEst.Gsing_deriv_rel

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.UopHk

open scoped Real Topology ContDiff Interval
open MeasureTheory Set Filter

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option linter.unusedVariables false

/-!
# Smoothness and the ODE of the singular term, in the interior class `RegQ`

This module proves `Work.FTS.EllipticEst.UopHk.GsingFactsInterior`: for `0 < α ≤ 1/4` and
`k ≥ 2`, a source `F` in the interior class `RegQ α k F` (`C^∞` on the open quadrant, honest
`ℋ^k`-membership, boundary traces), a stream function `Ψ` with `RegQ α k Ψ` solving
(PolarBSL) with source `F`, the three radial functions

* `F_*(F) = ∫_θ F(z,θ) sinθcos²θ dθ` (the angular moment),
* `Gsing α F = Gstar α F + Gbar α F` (the singular term), and
* `Gbar α F z = -(3/(4α)) z^{-5/α} ∫_0^z s^{(5-α)/α} F_*(s) ds`

are `C^{k-1}` on `(0,∞)`, and they satisfy the two relations

* `α z ∂_z Gsing = -5 Gbar`,
* `α² z² ∂_zz Gsing + α(5+α) z ∂_z Gsing = (15/4) F_*`.

## The route

The whole content at the level of `(0,∞)` is the *interior* regularity of the angular moment
of a `C^∞`-on-the-open-quadrant source in `ℋ^k`:

* `FstarDzIter_chain_open` writes the increment of the `j`-th radial moment
  `S_j = PsiInt F j = ∫_θ D_z^j F · sinθcos²θ` as the integral of `S_{j+1}(r)/r`;
* `PsiInt_continuousOn` upgrades that to continuity of `S_j` for `j + 1 ≤ k`
  (weighted square-root bound + the integrable slice functionals `AjF`);
* `hasDerivAt_PsiInt` gives `S_j' = S_{j+1}(z)/z` at every `z > 0` for `j + 2 ≤ k`.

Induction downwards on `j` then gives `S_j ∈ C^{k-1-j}` (`S_j` is a primitive of the
`C^{k-2-j}`-function `z ↦ S_{j+1}(z)/z`), and the case `j = 0` is `F_* = S_0`
(`PsiInt_eq_Fstar`).  From there `L₁₂(F) = 3∫_z^∞ F_*(r)/r dr` is `C^{k-1}` as a tail integral
of a `C^{k-1}`-integrand, `Ḡ` is a product of the smooth factor `Abar` with the primitive
`Jfun` of `s^{(5-α)/α}F_*(s)`, and the two relations are the general
`Gsing_deriv_rel` / `Work.Elliptic.Gsing_ode` of the `GsingFuncs` calculus.

## A remark on the hypotheses

The conclusions are *consequences of `RegQ α k F` and `k ≥ 2` alone*: the two hypotheses
`RegQ α k Ψ` and `IsBslSol α F Ψ` are not needed.  The reason is that the whole interior
regularity of `F_*` is supplied by the *source*: the chain rule `FstarDzIter_chain_open`, the
continuity `PsiInt_continuousOn` and the derivative `hasDerivAt_PsiInt` for the moments
`PsiInt F j` use only `SmoothOpen F` and `HkMem α k F`.  In particular a datum with a jump of
the slices of `Ψ` at `θ = 0` (the counterexample class of
`Cores/honestFstarFacts.lean`) is irrelevant here: what the moment `F_*` sees is `F`, not `Ψ`.
-/

/-! ## Elementary helpers -/

/-- A function with a prescribed derivative everywhere on `(0,∞)` gains one order of
smoothness. -/
theorem contDiffOn_succ_of_hasDerivAt {f g : ℝ → ℝ} {m : ℕ}
    (hf : ∀ x ∈ Set.Ioi (0 : ℝ), HasDerivAt f (g x) x)
    (hg : ContDiffOn ℝ m g (Set.Ioi 0)) :
    ContDiffOn ℝ (m + 1) f (Set.Ioi 0) := by
  have h : ContDiffOn ℝ ((m : ℕ∞ω) + 1) f (Set.Ioi 0) := by
    rw [contDiffOn_succ_iff_deriv_of_isOpen (𝕜 := ℝ) (f := f) (s := Set.Ioi (0 : ℝ))
      (n := (m : ℕ∞ω)) isOpen_Ioi]
    exact ⟨fun x hx => (hf x hx).differentiableAt.differentiableWithinAt,
      fun h => absurd h (by simp),
      hg.congr fun x hx => (hf x hx).deriv⟩
  simpa only [Nat.cast_add, Nat.cast_one] using h

/-- A function which is `C^∞` on the open quadrant is `C^∞` on the smaller open quadrant
`Q0 = (0,∞) × (0,π/2)`. -/
theorem smoothOpen_of_smoothQuad {F : ℝ → ℝ → ℝ} (h : Work.FTS.LocData.SmoothQuad F) :
    Work.FTS.EllipticEst.SmoothOpen F := by
  refine h.mono fun p hp => ?_
  rw [Work.FTS.EllipticEst.Q0, Set.mem_prod, Set.mem_Ioi, Set.mem_Ioo] at hp
  rw [Set.mem_prod, Set.mem_Ioi, Set.mem_Ioo]
  exact ⟨by linarith [hp.1], hp.2⟩

/-! ## Regularity of the angular moment `F_*` in the interior -/

/-- **The angular moment is `C^{k-1}` on `(0,∞)`.**

For `F` smooth on the open quadrant with `HkMem α k F` (`k ≥ 1`), the moment
`F_*(F) = PsiInt F 0` is `C^{k-1}` on `(0,∞)`.  The proof is the downward induction on `j`
described in the module docstring: `S_j` is a primitive of `z ↦ S_{j+1}(z)/z`, which is one
order smoother than `S_{j+1}`. -/
theorem contDiffOn_Fstar_of_smoothOpen_Hk (α : ℝ) (k : ℕ) (F : ℝ → ℝ → ℝ)
    (hF : Work.FTS.EllipticEst.SmoothOpen F) (hmem : Work.Spaces.HkMem α k F)
    (hk : 1 ≤ k) :
    ContDiffOn ℝ (k - 1) (Work.Elliptic.Fstar F) (Set.Ioi 0) := by
  have hmain : ∀ m : ℕ, ∀ j : ℕ, j + m = k - 1 →
      ContDiffOn ℝ m (fun z => Work.FTS.EllipticEst.PsiInt F j z) (Set.Ioi 0) := by
    intro m
    induction m with
    | zero =>
      intro j hj
      refine (contDiffOn_zero (𝕜 := ℝ)).mpr ?_
      exact Work.FTS.EllipticEst.PsiInt_continuousOn α k F hF hmem j (by omega)
    | succ m ih =>
      intro j hj
      have hj2 : j + 2 ≤ k := by omega
      have hj1 : (j + 1) + m = k - 1 := by omega
      have hg : ContDiffOn ℝ m (fun z => Work.FTS.EllipticEst.PsiInt F (j + 1) z / z)
          (Set.Ioi 0) :=
        (ih (j + 1) hj1).div contDiffOn_id fun z hz => ne_of_gt hz
      exact contDiffOn_succ_of_hasDerivAt
        (fun z hz => Work.FTS.EllipticEst.hasDerivAt_PsiInt α k F hF hmem j hj2 hz) hg
  exact (hmain (k - 1) 0 (by omega)).congr fun z _ =>
    Work.FTS.EllipticEst.PsiInt_eq_Fstar F z

/-! ## Integrability of the density `F_*(r)/r` -/

/-- `(z/(1+z)²)²` is integrable on `(0,∞)`. -/
theorem integrableOn_sq_div_one_add_sq_sq :
    MeasureTheory.IntegrableOn (fun z : ℝ => (z / (1 + z) ^ 2) ^ 2) (Set.Ioi 0) := by
  have hcont_Ioc : ContinuousOn (fun z : ℝ => (z / (1 + z) ^ 2) ^ 2) (Set.Ioc (0 : ℝ) 1) := by
    refine ContinuousOn.pow (ContinuousOn.div continuousOn_id
      ((continuousOn_const.add continuousOn_id).pow 2) ?_) 2
    intro z hz
    have hz' : (0 : ℝ) < 1 + z := by linarith [hz.1]
    exact pow_ne_zero 2 (ne_of_gt hz')
  have hle_Ioc : ∀ z ∈ Set.Ioc (0 : ℝ) 1, ‖(z / (1 + z) ^ 2) ^ 2‖ ≤ (1 : ℝ) := by
    intro z hz
    have hz0 : (0 : ℝ) ≤ z := le_of_lt hz.1
    have hdiv0 : 0 ≤ z / (1 + z) ^ 2 := div_nonneg hz0 (sq_nonneg _)
    rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg hdiv0 2)]
    have hle : z / (1 + z) ^ 2 ≤ 1 := by
      have hpos : (0 : ℝ) < (1 + z) ^ 2 := by positivity
      rw [div_le_one hpos]
      nlinarith [hz0, hz.2]
    exact pow_le_one₀ hdiv0 hle
  have hA : MeasureTheory.IntegrableOn (fun z : ℝ => (z / (1 + z) ^ 2) ^ 2)
      (Set.Ioc (0 : ℝ) 1) := by
    refine MeasureTheory.Integrable.mono'
      (MeasureTheory.integrableOn_const (s := Set.Ioc (0 : ℝ) 1) (C := (1 : ℝ))
        (by rw [Real.volume_Ioc]; exact ENNReal.ofReal_ne_top)) ?_ ?_
    · exact hcont_Ioc.aestronglyMeasurable measurableSet_Ioc
    · exact MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioc hle_Ioc
  have hcont_Ioi : ContinuousOn (fun z : ℝ => (z / (1 + z) ^ 2) ^ 2) (Set.Ioi (1 : ℝ)) := by
    refine ContinuousOn.pow (ContinuousOn.div continuousOn_id
      ((continuousOn_const.add continuousOn_id).pow 2) ?_) 2
    intro z hz
    have hz1 : (1 : ℝ) < z := Set.mem_Ioi.mp hz
    have hz' : (0 : ℝ) < 1 + z := by linarith
    exact pow_ne_zero 2 (ne_of_gt hz')
  have hle_Ioi : ∀ z ∈ Set.Ioi (1 : ℝ),
      ‖(z / (1 + z) ^ 2) ^ 2‖ ≤ z ^ (-2 : ℝ) := by
    intro z hz
    have hz1 : (0 : ℝ) < z := lt_trans zero_lt_one hz
    have hz0 : (0 : ℝ) ≤ z := le_of_lt hz1
    have hdiv0 : 0 ≤ z / (1 + z) ^ 2 := div_nonneg hz0 (sq_nonneg _)
    rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg hdiv0 2)]
    have hstep : z / (1 + z) ^ 2 ≤ z / z ^ 2 := by
      refine div_le_div_of_nonneg_left hz0 (by positivity) ?_
      exact pow_le_pow_left₀ hz0 (by linarith) 2
    calc (z / (1 + z) ^ 2) ^ 2 ≤ (z / z ^ 2) ^ 2 :=
          pow_le_pow_left₀ hdiv0 hstep 2
      _ = z ^ (-2 : ℝ) := by
          rw [Real.rpow_neg hz0, Real.rpow_two]
          field_simp
  have hB : MeasureTheory.IntegrableOn (fun z : ℝ => (z / (1 + z) ^ 2) ^ 2)
      (Set.Ioi (1 : ℝ)) := by
    refine MeasureTheory.Integrable.mono'
      (integrableOn_Ioi_rpow_of_lt (a := (-2 : ℝ)) (c := (1 : ℝ))
        (by norm_num) (by norm_num)) ?_ ?_
    · exact hcont_Ioi.aestronglyMeasurable measurableSet_Ioi
    · exact MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioi hle_Ioi
  have hunion := hA.union hB
  rw [Set.Ioc_union_Ioi (a := (0 : ℝ)) (b := 1) (c := 1) (by norm_num),
    min_eq_left (by norm_num : (0 : ℝ) ≤ 1)] at hunion
  exact hunion

/-- **The density `F_*(r)/r` is integrable on `(0,∞)`.**

The Cauchy–Schwarz bound `|F_*(z)| ≤ √(π/2)√(A_0(z))·z²/(1+z)²` together with the
integrability of the slice functional `A_0 = AjF F 0` and of `(z/(1+z)²)²` (AM–GM) bounds the
density by an `L¹` function; measurability is that of the parametric integral
(`PsiInt_aesm`), since `F` is continuous on the open quadrant. -/
theorem integrableOn_Fstar_div_of_smoothOpen_Hk (α : ℝ) (k : ℕ) (F : ℝ → ℝ → ℝ)
    (hF : Work.FTS.EllipticEst.SmoothOpen F) (hmem : Work.Spaces.HkMem α k F) :
    MeasureTheory.IntegrableOn (fun r : ℝ => Work.Elliptic.Fstar F r / r) (Set.Ioi 0) := by
  have hA : MeasureTheory.IntegrableOn (fun z : ℝ => Work.FTS.EllipticEst.AjF F 0 z)
      (Set.Ioi 0) :=
    Work.FTS.EllipticEst.AjF_integrableOn α k F hF hmem 0 (Nat.zero_le k)
  have hAnn : ∀ᵐ z ∂(volume.restrict (Set.Ioi 0)),
      0 ≤ Work.FTS.EllipticEst.AjF F 0 z :=
    Eventually.of_forall fun z => Work.FTS.EllipticEst.AjF_nonneg F 0 z
  have hB : MeasureTheory.IntegrableOn (fun z : ℝ => (z / (1 + z) ^ 2) ^ 2) (Set.Ioi 0) :=
    integrableOn_sq_div_one_add_sq_sq
  have hBm : AEStronglyMeasurable (fun z : ℝ => z / (1 + z) ^ 2)
      (volume.restrict (Set.Ioi 0)) := by
    refine ContinuousOn.aestronglyMeasurable ?_ measurableSet_Ioi
    refine ContinuousOn.div continuousOn_id ((continuousOn_const.add continuousOn_id).pow 2) ?_
    intro z hz
    have hz' : (0 : ℝ) < 1 + z := by linarith [Set.mem_Ioi.mp hz]
    exact pow_ne_zero 2 (ne_of_gt hz')
  -- the AM–GM majorant `√(π/2)·(A z + (B z)^2)/2` is integrable
  have hmaj : MeasureTheory.IntegrableOn
      (fun z : ℝ => Real.sqrt (π / 2)
        * ((Work.FTS.EllipticEst.AjF F 0 z + (z / (1 + z) ^ 2) ^ 2) / 2)) (Set.Ioi 0) :=
    ((hA.add hB).div_const 2).const_mul (Real.sqrt (π / 2))
  -- measurability of `F_*(r)/r`
  have haesm : AEStronglyMeasurable (fun r : ℝ => Work.Elliptic.Fstar F r / r)
      (volume.restrict (Set.Ioi 0)) := by
    have h1 : AEStronglyMeasurable (fun r : ℝ => Work.FTS.EllipticEst.PsiInt F 0 r)
        (volume.restrict (Set.Ioi 0)) :=
      Work.FTS.EllipticEst.PsiInt_aesm F hF 0
    have h2 : AEMeasurable (fun r : ℝ => r) (volume.restrict (Set.Ioi 0)) :=
      measurable_id.aemeasurable
    have h3 : AEMeasurable (fun r : ℝ => Work.FTS.EllipticEst.PsiInt F 0 r / r)
        (volume.restrict (Set.Ioi 0)) := h1.aemeasurable.div h2
    refine h3.aestronglyMeasurable.congr ?_
    filter_upwards with r
    rw [Work.FTS.EllipticEst.PsiInt_eq_Fstar F r]
  refine MeasureTheory.Integrable.mono' hmaj haesm ?_
  filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with r hr
  have hr0 : (0 : ℝ) < r := hr
  have hbd := Work.FTS.EllipticEst.PsiInt_sqrt_bound α k F hF hmem 0 (Nat.zero_le k) hr0
  rw [Work.FTS.EllipticEst.PsiInt_eq_Fstar F r] at hbd
  have hA0 : 0 ≤ Work.FTS.EllipticEst.AjF F 0 r := Work.FTS.EllipticEst.AjF_nonneg F 0 r
  have hw : (Work.Spaces.w r * r)⁻¹ = r / (1 + r) ^ 2 := by
    rw [Work.Spaces.w]; field_simp
  have hpow : Real.sqrt (π / 2) * Real.sqrt (Work.FTS.EllipticEst.AjF F 0 r) / Work.Spaces.w r
        / r
      = Real.sqrt (π / 2)
        * (Real.sqrt (Work.FTS.EllipticEst.AjF F 0 r) * (r / (1 + r) ^ 2)) := by
    rw [div_div, div_eq_mul_inv, hw]; ring
  rw [Real.norm_eq_abs, abs_div, abs_of_pos hr0]
  calc |Work.Elliptic.Fstar F r| / r
      ≤ (Real.sqrt (π / 2) * Real.sqrt (Work.FTS.EllipticEst.AjF F 0 r) / Work.Spaces.w r) / r :=
        div_le_div_of_nonneg_right hbd hr0.le
    _ = Real.sqrt (π / 2)
          * (Real.sqrt (Work.FTS.EllipticEst.AjF F 0 r) * (r / (1 + r) ^ 2)) := hpow
    _ ≤ Real.sqrt (π / 2)
          * ((Work.FTS.EllipticEst.AjF F 0 r + (r / (1 + r) ^ 2) ^ 2) / 2) := by
        refine mul_le_mul_of_nonneg_left ?_ (Real.sqrt_nonneg _)
        have h : 0 ≤ (Real.sqrt (Work.FTS.EllipticEst.AjF F 0 r) - (r / (1 + r) ^ 2)) ^ 2 :=
          sq_nonneg _
        rw [sub_sq, Real.sq_sqrt hA0] at h
        linarith

/-! ## Tail integrals -/

/-- **The tail integral of a `C^m` integrable function is `C^{m+1}`**, and its derivative is
minus the integrand. -/
theorem contDiffOn_tailIntegral_of_cont {g : ℝ → ℝ} {m : ℕ}
    (hcont : ContinuousOn g (Set.Ioi 0)) (hint : MeasureTheory.IntegrableOn g (Set.Ioi 0))
    (hsm : ContDiffOn ℝ m g (Set.Ioi 0)) :
    ContDiffOn ℝ (m + 1) (fun z => ∫ r in Set.Ioi z, g r) (Set.Ioi 0) ∧
      ∀ z ∈ Set.Ioi (0 : ℝ), HasDerivAt (fun w : ℝ => ∫ r in Set.Ioi w, g r) (-(g z)) z := by
  have hderiv : ∀ z ∈ Set.Ioi (0 : ℝ),
      HasDerivAt (fun w : ℝ => ∫ r in Set.Ioi w, g r) (-(g z)) z := by
    intro z hz
    have hz0 : (0 : ℝ) < z := hz
    have hEq : (fun w : ℝ => ∫ r in Set.Ioi w, g r) =ᶠ[𝓝 z]
        ((fun _ : ℝ => ∫ r in Set.Ioi (0 : ℝ), g r) - fun w : ℝ => ∫ x in (0 : ℝ)..w, g x) := by
      filter_upwards [isOpen_Ioi.mem_nhds hz] with w hw
      have hw0 : (0 : ℝ) < w := hw
      have hIoi : MeasureTheory.IntegrableOn g (Set.Ioi w) :=
        hint.mono_set (Set.Ioi_subset_Ioi hw0.le)
      have h := intervalIntegral.integral_interval_add_Ioi (f := g) (a := (0 : ℝ)) (b := w)
        hint hIoi
      simp only [Pi.sub_apply]
      linarith
    have hInt : IntervalIntegrable g volume (0 : ℝ) z := by
      rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hz0.le]
      exact hint.mono_set fun x hx => hx.1
    have hprim : HasDerivAt (fun w : ℝ => ∫ x in (0 : ℝ)..w, g x) (g z) z :=
      intervalIntegral.integral_hasDerivAt_right hInt
        (hcont.stronglyMeasurableAtFilter isOpen_Ioi z hz)
        (hcont.continuousAt (isOpen_Ioi.mem_nhds hz))
    have hmain : HasDerivAt
        ((fun _ : ℝ => ∫ r in Set.Ioi (0 : ℝ), g r) - fun w : ℝ => ∫ x in (0 : ℝ)..w, g x)
        (0 - g z) z :=
      (hasDerivAt_const (x := z) (c := ∫ r in Set.Ioi (0 : ℝ), g r)).sub hprim
    exact (hmain.congr_of_eventuallyEq hEq).congr_deriv (zero_sub (g z))
  exact ⟨contDiffOn_succ_of_hasDerivAt hderiv hsm.neg, hderiv⟩

/-! ## The singular term `L₁₂` in the interior -/

/-- **`L₁₂(F) = 3∫_z^∞ F_*(r)/r dr` is `C^{k-1}` and differentiable at every `z > 0`** with
derivative `-3F_*(z)/z`. -/
theorem contDiffOn_L12_of_smoothOpen_Hk (α : ℝ) (k : ℕ) (F : ℝ → ℝ → ℝ)
    (hF : Work.FTS.EllipticEst.SmoothOpen F) (hmem : Work.Spaces.HkMem α k F) (hk : 2 ≤ k) :
    ContDiffOn ℝ (k - 1) (Work.Elliptic.L12 F) (Set.Ioi 0) ∧
      ∀ z ∈ Set.Ioi (0 : ℝ),
        HasDerivAt (Work.Elliptic.L12 F) (-(3 * Work.Elliptic.Fstar F z / z)) z := by
  have hk1 : 1 ≤ k := by omega
  have hFstar := contDiffOn_Fstar_of_smoothOpen_Hk α k F hF hmem hk1
  have hFstar_cont : ContinuousOn (Work.Elliptic.Fstar F) (Set.Ioi 0) := hFstar.continuousOn
  have hcont : ContinuousOn (fun r : ℝ => Work.Elliptic.Fstar F r / r) (Set.Ioi 0) :=
    hFstar_cont.div continuousOn_id fun r hr => ne_of_gt hr
  have hint : MeasureTheory.IntegrableOn (fun r : ℝ => Work.Elliptic.Fstar F r / r)
      (Set.Ioi 0) :=
    integrableOn_Fstar_div_of_smoothOpen_Hk α k F hF hmem
  have hm2 : ((k - 2 : ℕ) : ℕ∞ω) ≤ ((k - 1 : ℕ) : ℕ∞ω) := by
    exact_mod_cast (by omega : k - 2 ≤ k - 1)
  have hsm : ContDiffOn ℝ (k - 2) (fun r : ℝ => Work.Elliptic.Fstar F r / r) (Set.Ioi 0) :=
    (hFstar.of_le hm2).div contDiffOn_id fun r hr => ne_of_gt hr
  have htail := contDiffOn_tailIntegral_of_cont hcont hint hsm
  have htail' : ((k - 2 : ℕ) : ℕ∞ω) + 1 = ((k - 1 : ℕ) : ℕ∞ω) := by
    exact_mod_cast (by omega : k - 2 + 1 = k - 1)
  constructor
  · have h := htail.1
    rw [htail'] at h
    have hfun : (Work.Elliptic.L12 F)
        = fun z : ℝ => 3 * ∫ r in Set.Ioi z, Work.Elliptic.Fstar F r / r := by
      funext z
      rw [Work.Elliptic.L12_eq_radial, Work.Elliptic.L12rad]
    rw [hfun]
    exact contDiffOn_const.mul h
  · intro z hz
    have h := htail.2 z hz
    have h3 : HasDerivAt (fun z : ℝ => 3 * ∫ r in Set.Ioi z, Work.Elliptic.Fstar F r / r)
        (3 * (-(Work.Elliptic.Fstar F z / z))) z := h.const_mul 3
    have hfun : (fun z : ℝ => 3 * ∫ r in Set.Ioi z, Work.Elliptic.Fstar F r / r)
        = Work.Elliptic.L12 F := by
      funext z
      rw [Work.Elliptic.L12_eq_radial, Work.Elliptic.L12rad]
    rw [hfun] at h3
    refine h3.congr_deriv ?_
    ring

/-! ## The primitive `Jfun` of `Gbar` -/

/-- **The primitive `z ↦ ∫_0^z s^{(5-α)/α}F_*(s) ds` is `C^{k-1}` and its derivative is the
integrand.**  The interval integrability on `(0,z]` is supplied by the local integrability of
`F_*` and the bound `|F_*(s)| ≤ √(π/2)√(A_0(s))·s²/(1+s)²`. -/
theorem contDiffOn_Jfun_of_smoothOpen_Hk (α : ℝ) (k : ℕ) (F : ℝ → ℝ → ℝ) (hα : 0 < α)
    (hα1 : α ≤ 1) (hF : Work.FTS.EllipticEst.SmoothOpen F) (hmem : Work.Spaces.HkMem α k F)
    (hk : 2 ≤ k) :
    ContDiffOn ℝ (k - 1)
        (fun z : ℝ => ∫ s in (0 : ℝ)..z, s ^ ((5 - α) / α) * Work.Elliptic.Fstar F s)
        (Set.Ioi 0) ∧
      ∀ z ∈ Set.Ioi (0 : ℝ),
        HasDerivAt (fun z' : ℝ => ∫ s in (0 : ℝ)..z',
            s ^ ((5 - α) / α) * Work.Elliptic.Fstar F s)
          (z ^ ((5 - α) / α) * Work.Elliptic.Fstar F z) z := by
  have hk1 : 1 ≤ k := by omega
  have hFstar := contDiffOn_Fstar_of_smoothOpen_Hk α k F hF hmem hk1
  -- the integrand is `C^{k-1}`
  have hsm : ContDiffOn ℝ (k - 1)
      (fun s : ℝ => s ^ ((5 - α) / α) * Work.Elliptic.Fstar F s) (Set.Ioi 0) :=
    (ContDiffOn.rpow_const_of_ne contDiffOn_id (fun x hx => ne_of_gt hx)).mul hFstar
  -- interval integrability on `(0,z]` at every `z > 0`
  have hI : ∀ z ∈ Set.Ioi (0 : ℝ),
      IntervalIntegrable (fun s : ℝ => s ^ ((5 - α) / α) * Work.Elliptic.Fstar F s)
        volume 0 z := by
    intro z hz
    have hloc := (Work.FTS.EllipticEst.GbarSin.Fstar_local_integrableOn α k F hα hα1 hF hmem
      0 (Nat.zero_le k)).2 z hz
    refine hloc.congr ?_
    intro s hs
    have hpexp : s ^ ((5 - α) / α) = s ^ (5 / α - 1) := by
      rw [show (5 - α) / α = 5 / α - 1 by field_simp]
    show s ^ (5 / α - 1) * Work.Elliptic.Fstar F s
        = s ^ ((5 - α) / α) * Work.Elliptic.Fstar F s
    rw [hpexp]
  have hprim : ∀ z ∈ Set.Ioi (0 : ℝ),
      HasDerivAt (fun z' : ℝ => ∫ s in (0 : ℝ)..z',
          s ^ ((5 - α) / α) * Work.Elliptic.Fstar F s)
        (z ^ ((5 - α) / α) * Work.Elliptic.Fstar F z) z := by
    intro z hz
    exact intervalIntegral.integral_hasDerivAt_right (hI z hz)
      (hsm.continuousOn.stronglyMeasurableAtFilter isOpen_Ioi z hz)
      (hsm.continuousOn.continuousAt (isOpen_Ioi.mem_nhds hz))
  refine ⟨?_, hprim⟩
  -- `C^{k-1}`: the primitive gains one order over `C^{k-2}`
  have hm2 : ((k - 2 : ℕ) : ℕ∞ω) ≤ ((k - 1 : ℕ) : ℕ∞ω) := by
    exact_mod_cast (by omega : k - 2 ≤ k - 1)
  have h := contDiffOn_succ_of_hasDerivAt hprim (hsm.of_le hm2)
  have heq : ((k - 2 : ℕ) : ℕ∞ω) + 1 = ((k - 1 : ℕ) : ℕ∞ω) := by
    exact_mod_cast (by omega : k - 2 + 1 = k - 1)
  rw [heq] at h
  exact h

/-! ## Smoothness of `Ḡ` and `Gsing` -/

/-- **`Ḡ = Abar · Jfun` is `C^{k-1}` on `(0,∞)`.** -/
theorem contDiffOn_Gbar_of_smoothOpen_Hk (α : ℝ) (k : ℕ) (F : ℝ → ℝ → ℝ) (hα : 0 < α)
    (hα1 : α ≤ 1) (hF : Work.FTS.EllipticEst.SmoothOpen F) (hmem : Work.Spaces.HkMem α k F)
    (hk : 2 ≤ k) :
    ContDiffOn ℝ (k - 1) (Work.Elliptic.Gbar α F) (Set.Ioi 0) := by
  have hJ := (contDiffOn_Jfun_of_smoothOpen_Hk α k F hα hα1 hF hmem hk).1
  have hA : ContDiffOn ℝ (k - 1) (Work.Elliptic.Abar α) (Set.Ioi 0) := by
    have h : ContDiffOn ℝ (k - 1) (fun z : ℝ => z ^ (-(5 / α))) (Set.Ioi 0) :=
      ContDiffOn.rpow_const_of_ne contDiffOn_id fun x hx => ne_of_gt hx
    exact contDiffOn_const.mul h
  have hfun : (Work.Elliptic.Gbar α F)
      = fun z => Work.Elliptic.Abar α z * Work.Elliptic.Jfun α F z := rfl
  rw [hfun]
  exact hA.mul hJ

/-- **`Gsing = Gstar + Ḡ` is `C^{k-1}` on `(0,∞)`.** -/
theorem contDiffOn_Gsing_of_smoothOpen_Hk (α : ℝ) (k : ℕ) (F : ℝ → ℝ → ℝ) (hα : 0 < α)
    (hα1 : α ≤ 1) (hF : Work.FTS.EllipticEst.SmoothOpen F) (hmem : Work.Spaces.HkMem α k F)
    (hk : 2 ≤ k) :
    ContDiffOn ℝ (k - 1) (Work.Elliptic.Gsing α F) (Set.Ioi 0) := by
  have hL12 := (contDiffOn_L12_of_smoothOpen_Hk α k F hF hmem hk).1
  have hgs : ContDiffOn ℝ (k - 1) (Work.Elliptic.Gstar α F) (Set.Ioi 0) := by
    have hfun : (Work.Elliptic.Gstar α F) = fun z => -(1 / (4 * α)) * Work.Elliptic.L12 F z :=
      rfl
    rw [hfun]
    exact contDiffOn_const.mul hL12
  have hgb := contDiffOn_Gbar_of_smoothOpen_Hk α k F hα hα1 hF hmem hk
  have hfun : (Work.Elliptic.Gsing α F)
      = fun z => Work.Elliptic.Gstar α F z + Work.Elliptic.Gbar α F z := rfl
  rw [hfun]
  exact hgs.add hgb

/-! ## The target -/

theorem GsingFactsInterior (α : ℝ) (k : ℕ) (F Ψ : ℝ → ℝ → ℝ)
    (hα : 0 < α) (hα4 : α ≤ 1 / 4) (hk : 2 ≤ k)
    (hF : Work.FTS.Nonlin.RegQ α k F) (hΨ : Work.FTS.Nonlin.RegQ α k Ψ)
    (hsol : Work.Elliptic.IsBslSol α F Ψ) :
    ContDiffOn ℝ (k - 1) (Work.Elliptic.Fstar F) (Set.Ioi 0) ∧
      ContDiffOn ℝ (k - 1) (Work.Elliptic.Gsing α F) (Set.Ioi 0) ∧
      ContDiffOn ℝ (k - 1) (Work.Elliptic.Gbar α F) (Set.Ioi 0) ∧
      (∀ z ∈ Set.Ioi (0 : ℝ),
        α * z * deriv (Work.Elliptic.Gsing α F) z = -5 * Work.Elliptic.Gbar α F z) ∧
      (∀ z ∈ Set.Ioi (0 : ℝ),
        α ^ 2 * z ^ 2 * deriv (fun z' => deriv (Work.Elliptic.Gsing α F) z') z
          + α * (5 + α) * z * deriv (Work.Elliptic.Gsing α F) z
        = (15 / 4) * Work.Elliptic.Fstar F z) := by
  have hα1 : α ≤ 1 := by linarith
  have hFopen : Work.FTS.EllipticEst.SmoothOpen F := smoothOpen_of_smoothQuad hF.1
  have hmem : Work.Spaces.HkMem α k F := hF.2.1
  obtain ⟨-, hL12diff⟩ := contDiffOn_L12_of_smoothOpen_Hk α k F hFopen hmem hk
  have hFstar := contDiffOn_Fstar_of_smoothOpen_Hk α k F hFopen hmem (by omega)
  -- the derivative data of `F_*`
  have hFc : ∀ z ∈ Set.Ioi (0 : ℝ),
      HasDerivAt (Work.Elliptic.Fstar F) (deriv (Work.Elliptic.Fstar F) z) z := by
    intro z hz
    have h1 : ContDiffOn ℝ (1 : ℕ) (Work.Elliptic.Fstar F) (Set.Ioi 0) := by
      have hle : ((1 : ℕ) : ℕ∞ω) ≤ ((k - 1 : ℕ) : ℕ∞ω) := by
        exact_mod_cast (by omega : 1 ≤ k - 1)
      exact hFstar.of_le hle
    exact ((h1.differentiableOn (by simp)).differentiableAt
      (isOpen_Ioi.mem_nhds hz)).hasDerivAt
  have hJ := (contDiffOn_Jfun_of_smoothOpen_Hk α k F hα hα1 hFopen hmem hk).2
  refine ⟨hFstar, contDiffOn_Gsing_of_smoothOpen_Hk α k F hα hα1 hFopen hmem hk,
    contDiffOn_Gbar_of_smoothOpen_Hk α k F hα hα1 hFopen hmem hk, ?_, ?_⟩
  · intro z hz
    exact Work.FTS.EllipticEst.Gsing_deriv_rel α F hα hL12diff hFc hJ z hz
  · intro z hz
    exact Work.Elliptic.Gsing_ode α F hα hL12diff hFc hJ z hz

end Work.FTS.EllipticEst.UopHk
