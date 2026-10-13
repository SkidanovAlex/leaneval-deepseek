/-
Copyright: work module for the Elgindi finite-time singularity project.

# The weak-hypothesis slice slots of the elliptic chapter

For a datum `(F, Ψ)` of the weak hypothesis class `Work.FTS.EllipticEst.TT.EllWeakPos α k F Ψ`
with `2 ≤ k`, the angular slices of the four quantities occurring in the elliptic estimates
are `C²` (for `Ψ` and `∂_zΨ`) and the six `η`-weighted squares

  `(∂_θ²Ψ)² sEta`, `(∂_z∂_θ²Ψ)² sEta`, `(∂_z²Ψ)² sEta`, `(z∂_z³Ψ)² sEta`,
  `F² sEta`, `(z∂_zF)² sEta`

are integrable on `Iθ`, for every `z > 0` (`sEta θ = sin(2θ)^{-η}`, `η = 99/100`).

## Route

* the two `C²`-statements are the `θ`-slices of the joint `C^∞`-regularity of `Ψ` on the open
  quadrant, at the fixed radius `z > 0` (`SmoothOpen.curry_θ`, and the same for `∂_zΨ`);
* each of the six integrability statements is a single summand of the weighted integrand
  `HkIntegrand` of one of the three `HkMem`-fields of the hypothesis class (`F`, `z²∂_z²Ψ`,
  `∂_θ²Ψ`):
  - `(∂_θ²Ψ)² sEta` and `(∂_z∂_θ²Ψ)² sEta` come from `HkMem α k (∂_θ²Ψ)` with `i = 0, 1`
    (the `i = 1` slot carries the factor `z` of `D_z = z∂_z`, removed by dividing by
    `z² ≠ 0`);
  - `(∂_z²Ψ)² sEta` is the `i = 0` slot of `HkMem α k (z²∂_z²Ψ)`, divided by `z⁴ ≠ 0`;
  - `(z∂_z³Ψ)² sEta` is obtained from the `i = 1` slot of the same field, i.e. from the
    honesty of `∂_z(z²∂_z²Ψ) = 2z∂_z²Ψ + z³∂_z³Ψ`, through the elementary inequality
    `(z³∂_z³Ψ)² ≤ 2(∂_z(z²∂_z²Ψ))² + 8z⁴(∂_z²Ψ)²` (i.e. `(a-b)² ≤ 2a² + 2b²`);
  - `F² sEta` and `(z∂_zF)² sEta` are the `i = 0, 1` slots of `HkMem α k F`;
* the passage from the weighted integrand to the unweighted form is the pointwise identity
  `(a · w/sin(2θ)^{η/2})² = a² w² sEta θ` (`Work.FTS.EllipticEst.mul_w_sin_rpow_sq`) together
  with the extraction of a single summand (`Work.Spaces.sq_le_HkIntegrand_z`) and the division
  by `w(z)² ≠ 0` for `z > 0`; this is the lemma
  `integrableOn_DzIter_sq_mul_sEta` of the sibling module
  `Submission.Work.FTS.EllipticEst.remov.SourceBound.integrableOn_DzIter_sq_mul_sEta`;
* the a.e. strong measurability needed by `Integrable.mono'` comes from the continuity of the
  relevant functions on the open quadrant: for the `Ψ`-derived quantities directly
  (`aesm_slice_sq_mul_sEta`), and for the two `F`-slots through the equation `bslOp α Ψ = F` on
  the open quadrant (the measurability of `F` is *not* a hypothesis; see the module docstring of
  `WeakDefs`) — this is `aesm_F_slots` of the same sibling directory.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.EllipticEst.TT.WeakDefs
import Submission.Work.FTS.EllipticEst.StraightDefs
import Submission.Work.Spaces.Defs
import Submission.Work.Spaces.HkSq_terms
import Submission.Work.Spaces.CurrySmooth
import Submission.Work.Elliptic.Defs
import Submission.Work.FTS.EllipticEst.mul_w_sin_rpow_sq
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.FTS.EllipticEst.remov.SmoothOpen_bslOp_of_smoothOpen
import Submission.Work.FTS.EllipticEst.remov.SourceBound.sliceAesmSq
import Submission.Work.FTS.EllipticEst.remov.SourceBound.integrableOn_DzIter_sq_mul_sEta
import Submission.Work.FTS.EllipticEst.remov.SourceBound.aesm_F_slots

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.remov.SourceBound

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

set_option autoImplicit false
set_option maxHeartbeats 1600000

/-! ## Arithmetic and order facts -/

/-- `sEta` is nonnegative on the open angular interval. -/
theorem sEta_nonneg_Ioo {θ : ℝ} (hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)) :
    0 ≤ Work.FTS.EllipticEst.sEta θ := by
  rw [Work.FTS.EllipticEst.sEta]
  exact Real.rpow_nonneg (Real.sin_nonneg_of_nonneg_of_le_pi (by linarith [hθ.1])
    (by linarith [hθ.2, Real.pi_pos])) _

/-- The positive order `2` is below the smooth order of the open-quadrant class. -/
theorem two_le_smoothOrder : (2 : WithTop ℕ∞) ≤ Work.Stability.smoothOrder := by
  rw [Work.Stability.smoothOrder]
  exact WithTop.coe_le_coe.mpr le_top

/-! ## The radial product rule for `z²∂_z²Ψ` and the `D_z`-continuity on the quadrant -/

/-- The product rule in the radial variable: `∂_z(z²·B(·,θ))(z,θ) = 2z B(z,θ) + z²∂_zB(z,θ)`. -/
theorem pz_zsq_mul (B : ℝ → ℝ → ℝ) {z θ d : ℝ}
    (h : HasDerivAt (fun z' : ℝ => B z' θ) d z) :
    Work.Spaces.pz (fun z θ' => z ^ 2 * B z θ') z θ = 2 * z * B z θ + z ^ 2 * d := by
  have hz2 : HasDerivAt (fun z' : ℝ => z' ^ 2) (2 * z) z := by
    simpa using (hasDerivAt_pow 2 z)
  have hprod := hz2.mul h
  have hd := hprod.deriv
  show deriv (fun z' : ℝ => z' ^ 2 * B z' θ) z = 2 * z * B z θ + z ^ 2 * d
  exact hd

/-- The uncurried `D_z`-derivative of a function smooth on the open quadrant is continuous
there. -/
theorem continuousOn_uncurry_Dz_of_smoothOpen {A : ℝ → ℝ → ℝ}
    (hA : Work.FTS.EllipticEst.SmoothOpen A) :
    ContinuousOn (Function.uncurry (Work.Spaces.Dz A)) Work.FTS.EllipticEst.Q0 := by
  have h1 : ContinuousOn
      (fun p : ℝ × ℝ => p.1 * Function.uncurry (Work.Spaces.pz A) p)
      Work.FTS.EllipticEst.Q0 :=
    continuousOn_fst.mul (hA.pz).continuousOn
  have hEq : Function.uncurry (Work.Spaces.Dz A)
      = fun p : ℝ × ℝ => p.1 * Function.uncurry (Work.Spaces.pz A) p := by
    funext p; rfl
  rw [hEq]; exact h1

/-- `z²∂_z²Ψ` is `C^∞` on the open quadrant when `Ψ` is. -/
theorem smoothOpen_zsq_mul_pzIter_two {Ψ : ℝ → ℝ → ℝ}
    (hSO : Work.FTS.EllipticEst.SmoothOpen Ψ) :
    Work.FTS.EllipticEst.SmoothOpen (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) :=
  Work.FTS.EllipticEst.Cert.smoothOpen_mul_bsl
    Work.FTS.EllipticEst.Cert.smoothOpen_zsq_bsl (hSO.pzIter 2)

/-! ## The pointwise inequality behind the fourth integrability slot -/

/-- **The pointwise inequality for `z∂_z³Ψ`.**

With `G = z²∂_z²Ψ`, the identity `∂_zG = 2z∂_z²Ψ + z³∂_z³Ψ` gives
`(z∂_z³Ψ)² ≤ 2z^{-4}(∂_zG)² + 8(∂_z²Ψ)²`, hence the same inequality after multiplication by the
nonnegative weight `sEta θ`. -/
theorem slot6_pointwise {Ψ : ℝ → ℝ → ℝ} (hSO : Work.FTS.EllipticEst.SmoothOpen Ψ) {z θ : ℝ}
    (hz : 0 < z) (hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)) :
    (Work.Spaces.Dz (Work.Spaces.pzIter 2 Ψ) z θ) ^ 2
        * Work.FTS.EllipticEst.sEta θ
      ≤ (2 * (z ^ 4)⁻¹)
          * ((Work.Spaces.DzIter 1 (fun z θ' => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ') z θ) ^ 2
            * Work.FTS.EllipticEst.sEta θ)
        + 8 * ((Work.Spaces.pzIter 2 Ψ z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ) := by
  obtain ⟨hz4, hsq, hs⟩ : z ^ 4 ≠ 0 ∧ (0 : ℝ) < z ^ 4 ∧ 0 ≤ Work.FTS.EllipticEst.sEta θ :=
    ⟨pow_ne_zero 4 (ne_of_gt hz), by positivity, sEta_nonneg_Ioo hθ⟩
  have hB' : HasDerivAt (fun z' : ℝ => Work.Spaces.pzIter 2 Ψ z' θ)
      (Work.Spaces.pzIter 3 Ψ z θ) z := hSO.hasDerivAt_slice_pzIter 2 hθ hz
  have hpzG := pz_zsq_mul (Work.Spaces.pzIter 2 Ψ) (d := Work.Spaces.pzIter 3 Ψ z θ) hB'
  have hEq : Work.Spaces.DzIter 1 (fun z θ' => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ') z θ
      = 2 * z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ + z ^ 3 * Work.Spaces.pzIter 3 Ψ z θ := by
    show z * Work.Spaces.pz (fun z θ' => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ') z θ
      = 2 * z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ + z ^ 3 * Work.Spaces.pzIter 3 Ψ z θ
    rw [hpzG]
    ring
  have hDz : Work.Spaces.Dz (Work.Spaces.pzIter 2 Ψ) z θ
      = z * Work.Spaces.pzIter 3 Ψ z θ := rfl
  rw [hDz]
  have key : z ^ 3 * Work.Spaces.pzIter 3 Ψ z θ
      = Work.Spaces.DzIter 1 (fun z θ' => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ') z θ
        - 2 * z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ := by
    rw [hEq]; ring
  have h1 : (z ^ 3 * Work.Spaces.pzIter 3 Ψ z θ) ^ 2
      ≤ 2 * (Work.Spaces.DzIter 1 (fun z θ' => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ') z θ) ^ 2
        + 8 * z ^ 4 * (Work.Spaces.pzIter 2 Ψ z θ) ^ 2 := by
    rw [key]
    nlinarith [sq_nonneg (Work.Spaces.DzIter 1 (fun z θ' => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ')
        z θ + 2 * z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ)]
  have h2 : z ^ 4 * ((z * Work.Spaces.pzIter 3 Ψ z θ) ^ 2)
      = (z ^ 3 * Work.Spaces.pzIter 3 Ψ z θ) ^ 2 := by ring
  have h3 : (z * Work.Spaces.pzIter 3 Ψ z θ) ^ 2
      ≤ (z ^ 4)⁻¹
        * (2 * (Work.Spaces.DzIter 1 (fun z θ' => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ') z θ) ^ 2
          + 8 * z ^ 4 * (Work.Spaces.pzIter 2 Ψ z θ) ^ 2) := by
    have h4 := mul_le_mul_of_nonneg_left h1 (le_of_lt (inv_pos.mpr hsq))
    rwa [← h2, inv_mul_cancel_left₀ hz4] at h4
  calc (z * Work.Spaces.pzIter 3 Ψ z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ
      ≤ ((z ^ 4)⁻¹
          * (2 * (Work.Spaces.DzIter 1 (fun z θ' => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ') z θ) ^ 2
            + 8 * z ^ 4 * (Work.Spaces.pzIter 2 Ψ z θ) ^ 2))
        * Work.FTS.EllipticEst.sEta θ := mul_le_mul_of_nonneg_right h3 hs
    _ = (2 * (z ^ 4)⁻¹)
          * ((Work.Spaces.DzIter 1 (fun z θ' => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ') z θ) ^ 2
            * Work.FTS.EllipticEst.sEta θ)
        + 8 * ((Work.Spaces.pzIter 2 Ψ z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ) := by
        field_simp
        try ring

/-! ## The target -/

theorem weakSliceSlots {α : ℝ} {k : ℕ} {F Ψ : ℝ → ℝ → ℝ} (hk : 2 ≤ k)
    (h : Work.FTS.EllipticEst.TT.EllWeakPos α k F Ψ) :
    ∀ z, 0 < z →
      ContDiffOn ℝ 2 (fun θ => Ψ z θ) (Set.Ioo 0 (Real.pi / 2)) ∧
      ContDiffOn ℝ 2 (fun θ => Work.Spaces.pz Ψ z θ) (Set.Ioo 0 (Real.pi / 2)) ∧
      MeasureTheory.IntegrableOn
        (fun θ => (Work.Spaces.pthIter 2 Ψ z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)
        Work.Spaces.Iθ ∧
      MeasureTheory.IntegrableOn
        (fun θ => (Work.Spaces.pz (Work.Spaces.pthIter 2 Ψ) z θ) ^ 2
          * Work.FTS.EllipticEst.sEta θ) Work.Spaces.Iθ ∧
      MeasureTheory.IntegrableOn
        (fun θ => (Work.Spaces.pzIter 2 Ψ z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)
        Work.Spaces.Iθ ∧
      MeasureTheory.IntegrableOn
        (fun θ => (Work.Spaces.Dz (Work.Spaces.pzIter 2 Ψ) z θ) ^ 2
          * Work.FTS.EllipticEst.sEta θ) Work.Spaces.Iθ ∧
      MeasureTheory.IntegrableOn
        (fun θ => (F z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ) Work.Spaces.Iθ ∧
      MeasureTheory.IntegrableOn
        (fun θ => (Work.Spaces.Dz F z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)
        Work.Spaces.Iθ := by
  intro z hz
  have hSO : Work.FTS.EllipticEst.SmoothOpen Ψ :=
    Work.FTS.EllipticEst.smoothOpen_of_forall h.smooth
  have hSOB : Work.FTS.EllipticEst.SmoothOpen (Work.Spaces.pthIter 2 Ψ) :=
    Work.FTS.EllipticEst.Cert.smoothOpen_pthIter_bsl hSO 2
  have hGso : Work.FTS.EllipticEst.SmoothOpen
      (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) :=
    smoothOpen_zsq_mul_pzIter_two hSO
  have hz2 : z ^ 2 ≠ 0 := pow_ne_zero 2 (ne_of_gt hz)
  have hz4 : z ^ 4 ≠ 0 := pow_ne_zero 4 (ne_of_gt hz)
  -- slot 3: `(∂_θ²Ψ)² sEta`
  have h3 : MeasureTheory.IntegrableOn
      (fun θ => (Work.Spaces.pthIter 2 Ψ z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)
      Work.Spaces.Iθ :=
    integrableOn_DzIter_sq_mul_sEta h.memB 0 (Nat.zero_le k) hz
      (aesm_slice_sq_mul_sEta (A := Work.Spaces.pthIter 2 Ψ) hSOB.continuousOn hz)
  -- slot 4: `(∂_z∂_θ²Ψ)² sEta`
  have h4 : MeasureTheory.IntegrableOn
      (fun θ => (Work.Spaces.pz (Work.Spaces.pthIter 2 Ψ) z θ) ^ 2
        * Work.FTS.EllipticEst.sEta θ) Work.Spaces.Iθ := by
    have h1 := integrableOn_DzIter_sq_mul_sEta h.memB 1 (by omega) hz
      (aesm_slice_sq_mul_sEta (A := Work.Spaces.DzIter 1 (Work.Spaces.pthIter 2 Ψ))
        (continuousOn_uncurry_Dz_of_smoothOpen hSOB) hz)
    refine MeasureTheory.IntegrableOn.congr_fun (h1.const_mul ((z ^ 2)⁻¹))
      (fun θ _ => ?_) measurableSet_Icc
    show (z ^ 2)⁻¹ * ((Work.Spaces.DzIter 1 (Work.Spaces.pthIter 2 Ψ) z θ) ^ 2
        * Work.FTS.EllipticEst.sEta θ) = (Work.Spaces.pz (Work.Spaces.pthIter 2 Ψ) z θ) ^ 2
        * Work.FTS.EllipticEst.sEta θ
    rw [show Work.Spaces.DzIter 1 (Work.Spaces.pthIter 2 Ψ) z θ
        = z * Work.Spaces.pz (Work.Spaces.pthIter 2 Ψ) z θ from rfl, mul_pow, mul_assoc,
      inv_mul_cancel_left₀ hz2]
  -- slot 5: `(∂_z²Ψ)² sEta`
  have h5 : MeasureTheory.IntegrableOn
      (fun θ => (Work.Spaces.pzIter 2 Ψ z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)
      Work.Spaces.Iθ := by
    have h1 := integrableOn_DzIter_sq_mul_sEta h.memA 0 (Nat.zero_le k) hz
      (aesm_slice_sq_mul_sEta (A := fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ)
        hGso.continuousOn hz)
    refine MeasureTheory.IntegrableOn.congr_fun (h1.const_mul ((z ^ 4)⁻¹))
      (fun θ _ => ?_) measurableSet_Icc
    have hsq : (z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) ^ 2
        = z ^ 4 * (Work.Spaces.pzIter 2 Ψ z θ) ^ 2 := by ring
    show (z ^ 4)⁻¹ * (((z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) ^ 2)
        * Work.FTS.EllipticEst.sEta θ) = (Work.Spaces.pzIter 2 Ψ z θ) ^ 2
        * Work.FTS.EllipticEst.sEta θ
    rw [hsq, mul_assoc, inv_mul_cancel_left₀ hz4]
  -- slot 6: `(z∂_z³Ψ)² sEta`
  have h6 : MeasureTheory.IntegrableOn
      (fun θ => (Work.Spaces.Dz (Work.Spaces.pzIter 2 Ψ) z θ) ^ 2
        * Work.FTS.EllipticEst.sEta θ) Work.Spaces.Iθ := by
    have hAinteg : MeasureTheory.IntegrableOn
        (fun θ => (Work.Spaces.DzIter 1 (fun z θ' => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ')
          z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ) Work.Spaces.Iθ :=
      integrableOn_DzIter_sq_mul_sEta h.memA 1 (by omega) hz
        (aesm_slice_sq_mul_sEta
          (A := Work.Spaces.DzIter 1 (fun z θ' => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ'))
          (by simpa only [Work.Spaces.DzIter_succ, Work.Spaces.DzIter_zero] using
            continuousOn_uncurry_Dz_of_smoothOpen hGso) hz)
    have hAesm : MeasureTheory.AEStronglyMeasurable
        (fun θ => (Work.Spaces.Dz (Work.Spaces.pzIter 2 Ψ) z θ) ^ 2
          * Work.FTS.EllipticEst.sEta θ) (MeasureTheory.volume.restrict Work.Spaces.Iθ) :=
      aesm_slice_sq_mul_sEta (A := Work.Spaces.Dz (Work.Spaces.pzIter 2 Ψ))
        (continuousOn_uncurry_Dz_of_smoothOpen (hSO.pzIter 2)) hz
    refine Integrable.mono'
      (g := fun θ => (2 * (z ^ 4)⁻¹)
        * ((Work.Spaces.DzIter 1 (fun z θ' => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ')
            z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)
        + 8 * ((Work.Spaces.pzIter 2 Ψ z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ))
      ((hAinteg.const_mul (2 * (z ^ 4)⁻¹)).add (h5.const_mul 8)) hAesm ?_
    filter_upwards [ae_mem_Ioo_of_mem_Iθ] with θ hθ
    rw [Real.norm_of_nonneg (mul_nonneg (sq_nonneg _) (sEta_nonneg_Ioo hθ))]
    exact slot6_pointwise hSO hz hθ
  -- slots 7, 8: `F² sEta` and `(z∂_zF)² sEta`
  have h7 : MeasureTheory.IntegrableOn
      (fun θ => (F z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ) Work.Spaces.Iθ :=
    integrableOn_DzIter_sq_mul_sEta h.memF 0 (Nat.zero_le k) hz
      (aesm_F_slots h z hz).1
  have h8 : MeasureTheory.IntegrableOn
      (fun θ => (Work.Spaces.Dz F z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)
      Work.Spaces.Iθ :=
    integrableOn_DzIter_sq_mul_sEta h.memF 1 (by omega) hz (aesm_F_slots h z hz).2
  exact ⟨(hSO.curry_θ hz).of_le two_le_smoothOrder,
    ((hSO.pz).curry_θ hz).of_le two_le_smoothOrder, h3, h4, h5, h6, h7, h8⟩

end

end Work.FTS.EllipticEst.remov.SourceBound
