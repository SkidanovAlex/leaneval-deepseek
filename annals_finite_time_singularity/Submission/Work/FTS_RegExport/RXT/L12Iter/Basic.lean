/-
Copyright: work module for the Elgindi finite-time singularity project.

# Shared analytic tools for the iterated `D_z`-derivatives of `L₁₂`

This module is the foundation of
`Work.FTS_RegExport.RXT.L12DzIterTendsto`: the iterated radial derivatives
`D_z^j (L₁₂(F n))` converge to `D_z^j (L₁₂ G)` along a sequence `F n` of profiles which are

* `C⁴` on the open quadrant `Q0 = (0,∞) × (0,π/2)` (`hF`),
* bounded, together with their mixed slots of order `≤ 2`, by `C₀ · z^{3/2}/(1+z)²` (`hbnd`),
* pointwise convergent, together with their mixed slots of order `≤ 4` (`hconv`).

The route is the *angular-moment* identity

  `D_z^{k+1}(L₁₂ f)(z) = - Qang f k z`,   `Qang f k z = ∫_θ K(θ)·D_z^k f (z,θ) dθ`,

so that nothing beyond the `θ`-integrability of `D_z^k f` is needed: the convergence of
`D_z^j(L₁₂ F n)` follows by dominated convergence *in `θ`* from `hconv`/`hbnd`.

This file collects what is needed for the base case `k = 0` and for the differentiation of
`Qang`:

* `Rwt`, the radial weight `z^{3/2}/(1+z)²` of `hbnd`, and its basic properties;
* the slice derivative `∂_z D_z^k f (z,θ) = D_z^{k+1} f (z,θ)/z` at finite order
  (`DzIter_slice_hasDerivAt`), from `ContDiffOn ℝ 4` on the *open* quadrant;
* the pointwise and a.e. bounds of `K(θ)·D_z^k f (z,θ)` by `3·C₀·Rwt z` on `Iθ`
  (`abs_Ktheta_mul_DzIter_le`), the a.e. strong measurability of the `θ`-slices
  (`aesm_Ktheta_mul_DzIter`) and the resulting `θ`-integrability
  (`integrable_Ktheta_mul_DzIter`);
* continuity of `z ↦ Qang f k z` on `(0,∞)` for `k ≤ 2` (`Qang_continuousAt`), by
  domination in `θ`;
* the identification `L12dens (f) s = Qang f 0 s / s` and the bound
  `|L12dens (f) s| ≤ 3(π/2) C₀ s^{1/2}/(1+s)²`, together with the integrability of
  `L12dens (f)` on `Ioi a` (`a > 0`) and the derivative formula
  `∂_z L₁₂(f)(z) = - L12dens (f)(z)`.

Everything here is `sorry`-free.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Order.CompletePartialOrder
import Submission.Work.Spaces.Defs
import Submission.Work.Spaces.aesm_slice_of_continuousOn_Qd
import Submission.Work.Elliptic.Defs
import Submission.Work.Elliptic.L12Aux
import Submission.Work.FM.Core2
import Submission.Work.Construction.Defs
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.FTS.StrongEps.HkMem_of_tendsto

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS_RegExport.RXT.L12Iter

set_option autoImplicit false
set_option maxHeartbeats 800000

/-! ## The radial weight of the standing bound -/

/-- The radial weight `z^{3/2}/(1+z)²` appearing in the standing pointwise bound
`|mixed b a (F n) z θ| ≤ C₀ · Rwt z`. -/
def Rwt (z : ℝ) : ℝ := z ^ ((3 : ℝ) / 2) / (1 + z) ^ 2

theorem Rwt_nonneg {z : ℝ} (hz : 0 ≤ z) : 0 ≤ Rwt z := by
  rw [Rwt]
  exact div_nonneg (Real.rpow_nonneg hz _) (by positivity)

theorem Rwt_pos {z : ℝ} (hz : 0 < z) : 0 < Rwt z := by
  rw [Rwt]
  exact div_pos (Real.rpow_pos_of_pos hz _) (by positivity)

/-- `Rwt s / s = s^{1/2}/(1+s)²`. -/
theorem Rwt_div (s : ℝ) (hs : 0 < s) : Rwt s / s = s ^ ((1 : ℝ) / 2) / (1 + s) ^ 2 := by
  have h1 : s ^ ((3 : ℝ) / 2) / s = s ^ ((1 : ℝ) / 2) := by
    have h := Real.rpow_sub hs ((3 : ℝ) / 2) 1
    rw [Real.rpow_one] at h
    rw [← h]
    norm_num
  rw [Rwt, div_div, mul_comm ((1 + s) ^ 2) s, ← div_div, h1]

/-! ## Finite-order smoothness of the `D_z`-iterates -/

/-- `D_z^k f` is `C¹` on the open quadrant as soon as `f` is `C⁴` there and `k ≤ 3`. -/
theorem contDiffOn_one_DzIter {f : ℝ → ℝ → ℝ}
    (h4 : ContDiffOn ℝ 4 (Function.uncurry f) Work.FTS.EllipticEst.Q0) {k : ℕ} (hk : k ≤ 3) :
    ContDiffOn ℝ 1 (Function.uncurry (Work.Spaces.DzIter k f)) Work.FTS.EllipticEst.Q0 :=
  Work.FTS.StrongEps.contDiffOn_uncurry_DzIter_shift Work.FTS.EllipticEst.isOpen_Q0 k 1
    (h4.of_le (Nat.cast_le.mpr (by omega : 1 + k ≤ 4)))

/-- `D_z^k f` is continuous on the open quadrant as soon as `f` is `C⁴` there and `k ≤ 3`. -/
theorem continuousOn_DzIter {f : ℝ → ℝ → ℝ}
    (h4 : ContDiffOn ℝ 4 (Function.uncurry f) Work.FTS.EllipticEst.Q0) {k : ℕ} (hk : k ≤ 3) :
    ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.DzIter k f p.1 p.2)
      Work.FTS.EllipticEst.Q0 :=
  (contDiffOn_one_DzIter h4 hk).continuousOn

/-! ## Differentiability of the radial slices -/

/-- For a function which is `C¹` on the open quadrant, the `z`-slice is differentiable and its
derivative is `pz`. -/
lemma hasDerivAt_slice_fst_Q0 {g : ℝ → ℝ → ℝ}
    (h : ContDiffOn ℝ 1 (Function.uncurry g) Work.FTS.EllipticEst.Q0)
    {z θ : ℝ} (hz : 0 < z) (hθ0 : 0 < θ) (hθ1 : θ < Real.pi / 2) :
    HasDerivAt (fun z' => g z' θ) (Work.Spaces.pz g z θ) z := by
  have hd : DifferentiableAt ℝ (Function.uncurry g) (z, θ) :=
    (h.differentiableOn one_ne_zero).differentiableAt
      (Work.FTS.EllipticEst.isOpen_Q0.mem_nhds ⟨hz, hθ0, hθ1⟩)
  have h2 : HasFDerivAt (fun z' : ℝ => (z', θ)) (ContinuousLinearMap.inl ℝ ℝ ℝ) z :=
    hasFDerivAt_prodMk_left z θ
  have h3 : HasDerivAt (fun z' : ℝ => Function.uncurry g (z', θ))
      ((fderiv ℝ (Function.uncurry g) (z, θ)).comp (ContinuousLinearMap.inl ℝ ℝ ℝ) 1) z := by
    simpa only [Function.comp_def] using (hd.hasFDerivAt.comp z h2).hasDerivAt
  have hval : (fderiv ℝ (Function.uncurry g) (z, θ)).comp (ContinuousLinearMap.inl ℝ ℝ ℝ) 1
      = Work.Spaces.pz g z θ := by
    rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.inl_apply]
    exact (Work.Spaces.deriv_slice_fst (Function.uncurry g) z θ hd).symm
  rw [hval] at h3
  exact h3

/-- **The slice derivative of `D_z^k f`.**  For `f` of class `C⁴` on the open quadrant,
`k ≤ 3`, `z > 0` and `θ ∈ (0,π/2)`,

  `∂_z (D_z^k f(·,θ))(z) = D_z^{k+1} f (z,θ)/z`.

(This is the definitional relation `D_z^{k+1} f = z ∂_z D_z^k f` read at a point where the
slice derivative exists, which is supplied by `C¹` smoothness of the slice.) -/
theorem DzIter_slice_hasDerivAt {f : ℝ → ℝ → ℝ}
    (h4 : ContDiffOn ℝ 4 (Function.uncurry f) Work.FTS.EllipticEst.Q0) {k : ℕ} (hk : k ≤ 3)
    {z θ : ℝ} (hz : 0 < z) (hθ0 : 0 < θ) (hθ1 : θ < Real.pi / 2) :
    HasDerivAt (fun x => Work.Spaces.DzIter k f x θ)
      (Work.Spaces.DzIter (k + 1) f z θ / z) z := by
  have h := hasDerivAt_slice_fst_Q0 (contDiffOn_one_DzIter h4 hk) hz hθ0 hθ1
  have hval : Work.Spaces.pz (Work.Spaces.DzIter k f) z θ
      = Work.Spaces.DzIter (k + 1) f z θ / z := by
    have h1 : Work.Spaces.DzIter (k + 1) f z θ
        = z * Work.Spaces.pz (Work.Spaces.DzIter k f) z θ := by
      rw [Work.Spaces.DzIter_succ]; rfl
    rw [h1, mul_div_cancel_left₀ _ (ne_of_gt hz)]
  rwa [hval] at h

/-! ## The angular weight `K(θ) = 3 sin θ cos²θ` -/

theorem abs_Ktheta_le_three (θ : ℝ) : |Work.Elliptic.Ktheta θ| ≤ 3 := by
  have hsin : |Real.sin θ| ≤ 1 := abs_le.mpr ⟨Real.neg_one_le_sin θ, Real.sin_le_one θ⟩
  have hcos : |Real.cos θ| ≤ 1 := abs_le.mpr ⟨Real.neg_one_le_cos θ, Real.cos_le_one θ⟩
  have hcos2 : |Real.cos θ ^ 2| ≤ 1 := by
    rw [abs_of_nonneg (sq_nonneg _)]
    nlinarith [hcos, abs_nonneg (Real.cos θ), sq_abs (Real.cos θ)]
  rw [Work.Elliptic.Ktheta, abs_mul, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 3)]
  nlinarith [hsin, hcos2, abs_nonneg (Real.sin θ), abs_nonneg (Real.cos θ ^ 2)]

theorem Ktheta_zero_left : Work.Elliptic.Ktheta 0 = 0 := by
  rw [Work.Elliptic.Ktheta]; norm_num

theorem Ktheta_zero_right : Work.Elliptic.Ktheta (Real.pi / 2) = 0 := by
  rw [Work.Elliptic.Ktheta, Real.cos_pi_div_two]; norm_num

/-! ## Pointwise bounds on the angular slices -/

/-- The pointwise bound of a `K(θ)·D_z^k f (z,θ)` slice, valid a.e. on `Iθ`, for `k ≤ 2`:
`‖K(θ)·D_z^k f (z,θ)‖ ≤ 3·C₀·Rwt z`.  (At the two endpoints `K` vanishes, so the bound holds
there too, but only the a.e. statement is needed.) -/
theorem abs_Ktheta_mul_DzIter_le {f : ℝ → ℝ → ℝ} {C0 : ℝ} (hC0 : 0 ≤ C0)
    (hbd : ∀ k : ℕ, k ≤ 2 → ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      |Work.Spaces.DzIter k f z θ| ≤ C0 * Rwt z)
    {k : ℕ} (hk : k ≤ 2) {z : ℝ} (hz : 0 < z) :
    ∀ᵐ θ ∂(volume.restrict Work.Spaces.Iθ),
      ‖Work.Elliptic.Ktheta θ * Work.Spaces.DzIter k f z θ‖ ≤ 3 * (C0 * Rwt z) := by
  rw [show Work.Spaces.Iθ = Set.Icc (0 : ℝ) (Real.pi / 2) from rfl]
  rw [MeasureTheory.ae_restrict_iff' measurableSet_Icc]
  refine Eventually.of_forall fun θ hθ => ?_
  rcases eq_or_lt_of_le hθ.1 with h0 | h0
  · subst h0
    rw [Ktheta_zero_left, zero_mul, norm_zero]
    exact mul_nonneg (by norm_num) (mul_nonneg hC0 (Rwt_nonneg hz.le))
  · rcases eq_or_lt_of_le hθ.2 with h1 | h1
    · subst h1
      rw [Ktheta_zero_right, zero_mul, norm_zero]
      exact mul_nonneg (by norm_num) (mul_nonneg hC0 (Rwt_nonneg hz.le))
    · rw [Real.norm_eq_abs, abs_mul]
      have := mul_le_mul (abs_Ktheta_le_three θ) (hbd k hk z θ hz h0 h1)
        (abs_nonneg (Work.Spaces.DzIter k f z θ)) (by norm_num : (0 : ℝ) ≤ 3)
      simpa [mul_assoc] using this

/-- The `θ`-slice `θ ↦ K(θ)·D_z^k f (z,θ)` is a.e. strongly measurable for the restriction of
Lebesgue measure to `Iθ` (it is continuous on the open interval). -/
theorem aesm_Ktheta_mul_DzIter {f : ℝ → ℝ → ℝ}
    (h4 : ContDiffOn ℝ 4 (Function.uncurry f) Work.FTS.EllipticEst.Q0) {k : ℕ} (hk : k ≤ 3)
    {z : ℝ} (hz : 0 < z) :
    AEStronglyMeasurable
      (fun θ => Work.Elliptic.Ktheta θ * Work.Spaces.DzIter k f z θ)
      (volume.restrict Work.Spaces.Iθ) := by
  have hK : ContinuousOn (fun p : ℝ × ℝ => Work.Elliptic.Ktheta p.2)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) := by
    have hfun : (fun p : ℝ × ℝ => Work.Elliptic.Ktheta p.2)
        = fun p : ℝ × ℝ => 3 * Real.sin p.2 * Real.cos p.2 ^ 2 := by
      funext p; rw [Work.Elliptic.Ktheta]
    rw [hfun]
    exact ((continuous_const.mul (Real.continuous_sin.comp continuous_snd)).mul
      ((Real.continuous_cos.comp continuous_snd).pow 2)).continuousOn
  have hD : ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.DzIter k f p.1 p.2)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) := continuousOn_DzIter h4 hk
  exact Work.Spaces.aesm_slice_of_continuousOn_Qd _ (hK.mul hD) hz

/-- **`θ`-integrability of the angular slices.** -/
theorem integrable_Ktheta_mul_DzIter {f : ℝ → ℝ → ℝ} {C0 : ℝ} (hC0 : 0 ≤ C0)
    (h4 : ContDiffOn ℝ 4 (Function.uncurry f) Work.FTS.EllipticEst.Q0)
    (hbd : ∀ k : ℕ, k ≤ 2 → ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      |Work.Spaces.DzIter k f z θ| ≤ C0 * Rwt z)
    {k : ℕ} (hk : k ≤ 2) {z : ℝ} (hz : 0 < z) :
    Integrable (fun θ => Work.Elliptic.Ktheta θ * Work.Spaces.DzIter k f z θ)
      (volume.restrict Work.Spaces.Iθ) :=
  MeasureTheory.Integrable.mono' (MeasureTheory.integrable_const (3 * (C0 * Rwt z)))
    (aesm_Ktheta_mul_DzIter h4 (by omega) hz)
    (abs_Ktheta_mul_DzIter_le hC0 hbd hk hz)

/-! ## Continuity of the angular moments -/

/-- **Continuity of `z ↦ Qang f k z` on `(0,∞)` for `k ≤ 2`.**  Dominated convergence in `θ`,
the domination being the constant `3·C₀·(2z)^{3/2}` on the neighbourhood
`(z/2, 2z) ∋ z` (where the standing bound gives `|D_z^k f (x,θ)| ≤ C₀ x^{3/2}/(1+x)² ≤
C₀ (2z)^{3/2}`). -/
theorem Qang_continuousAt {f : ℝ → ℝ → ℝ} {C0 : ℝ} (hC0 : 0 ≤ C0)
    (h4 : ContDiffOn ℝ 4 (Function.uncurry f) Work.FTS.EllipticEst.Q0)
    (hbd : ∀ k : ℕ, k ≤ 2 → ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      |Work.Spaces.DzIter k f z θ| ≤ C0 * Rwt z)
    {k : ℕ} (hk : k ≤ 2) {z : ℝ} (hz : 0 < z) :
    ContinuousAt (fun z => Work.Elliptic.Qang f k z) z := by
  have hCnn : 0 ≤ 3 * (C0 * (2 * z) ^ ((3 : ℝ) / 2)) := by positivity
  have hmeas : ∀ᶠ x in 𝓝 z, AEStronglyMeasurable
      (fun θ => Work.Elliptic.Ktheta θ * Work.Spaces.DzIter k f x θ)
      (volume.restrict Work.Spaces.Iθ) := by
    filter_upwards [isOpen_Ioi.mem_nhds hz] with x hx
    exact aesm_Ktheta_mul_DzIter h4 (by omega) hx
  have hbound : ∀ᶠ x in 𝓝 z, ∀ᵐ θ ∂(volume.restrict Work.Spaces.Iθ),
      ‖Work.Elliptic.Ktheta θ * Work.Spaces.DzIter k f x θ‖
        ≤ 3 * (C0 * (2 * z) ^ ((3 : ℝ) / 2)) := by
    filter_upwards [isOpen_Ioo.mem_nhds
      (show z ∈ Set.Ioo (z / 2) (2 * z) from ⟨by linarith, by linarith⟩)] with x hx
    have hxz : 0 < x := by linarith [hx.1]
    have hxle : x ≤ 2 * z := hx.2.le
    have hRwt : Rwt x ≤ (2 * z) ^ ((3 : ℝ) / 2) := by
      rw [Rwt, div_le_iff₀ (by positivity : (0 : ℝ) < (1 + x) ^ 2)]
      have h1 : x ^ ((3 : ℝ) / 2) ≤ (2 * z) ^ ((3 : ℝ) / 2) :=
        Real.rpow_le_rpow hxz.le hxle (by norm_num)
      have h2 : (1 : ℝ) ≤ (1 + x) ^ 2 := by nlinarith
      have h3 : (0 : ℝ) ≤ (2 * z) ^ ((3 : ℝ) / 2) :=
        Real.rpow_nonneg (by linarith) _
      nlinarith [h1, h2, h3]
    refine (abs_Ktheta_mul_DzIter_le hC0 hbd hk hxz).mono fun θ hθ => ?_
    have h2 : C0 * Rwt x ≤ C0 * (2 * z) ^ ((3 : ℝ) / 2) :=
      mul_le_mul_of_nonneg_left hRwt hC0
    linarith [hθ, mul_le_mul_of_nonneg_left h2 (by norm_num : (0 : ℝ) ≤ 3)]
  have hcont : ∀ᵐ θ ∂(volume.restrict Work.Spaces.Iθ),
      ContinuousAt (fun x => Work.Elliptic.Ktheta θ * Work.Spaces.DzIter k f x θ) z := by
    rw [show Work.Spaces.Iθ = Set.Icc (0 : ℝ) (Real.pi / 2) from rfl]
    rw [MeasureTheory.ae_restrict_iff' measurableSet_Icc]
    refine Eventually.of_forall fun θ hθ => ?_
    rcases eq_or_lt_of_le hθ.1 with h0 | h0
    · subst h0
      have hzero : (fun x : ℝ => Work.Elliptic.Ktheta 0 * Work.Spaces.DzIter k f x 0)
          = fun _ => (0 : ℝ) := by
        funext x; rw [Ktheta_zero_left, zero_mul]
      rw [hzero]
      exact continuousAt_const
    · rcases eq_or_lt_of_le hθ.2 with h1 | h1
      · subst h1
        have hzero : (fun x : ℝ => Work.Elliptic.Ktheta (Real.pi / 2)
            * Work.Spaces.DzIter k f x (Real.pi / 2)) = fun _ => (0 : ℝ) := by
          funext x; rw [Ktheta_zero_right, zero_mul]
        rw [hzero]
        exact continuousAt_const
      · have hK : ContinuousOn (fun p : ℝ × ℝ => Work.Elliptic.Ktheta p.2)
            (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) := by
          have hfun : (fun p : ℝ × ℝ => Work.Elliptic.Ktheta p.2)
              = fun p : ℝ × ℝ => 3 * Real.sin p.2 * Real.cos p.2 ^ 2 := by
            funext p; rw [Work.Elliptic.Ktheta]
          rw [hfun]
          exact ((continuous_const.mul (Real.continuous_sin.comp continuous_snd)).mul
            ((Real.continuous_cos.comp continuous_snd).pow 2)).continuousOn
        have hjoint : ContinuousWithinAt
            (fun p : ℝ × ℝ => Work.Elliptic.Ktheta p.2 * Work.Spaces.DzIter k f p.1 p.2)
            (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) (z, θ) :=
          (hK.mul (continuousOn_DzIter h4 (by omega : k ≤ 3))).continuousWithinAt
            (Work.FTS.EllipticEst.mem_Q0.mpr ⟨hz, h0, h1⟩)
        have hmap : ContinuousWithinAt (fun x : ℝ => (x, θ)) (Set.Ioi 0) z :=
          continuousWithinAt_id.prodMk continuousWithinAt_const
        have hcomp : ContinuousWithinAt
            ((fun p : ℝ × ℝ => Work.Elliptic.Ktheta p.2 * Work.Spaces.DzIter k f p.1 p.2)
              ∘ fun x : ℝ => (x, θ)) (Set.Ioi 0) z :=
          hjoint.comp (x := z) hmap (fun x hx =>
            Work.FTS.EllipticEst.mem_Q0.mpr ⟨hx, h0, h1⟩)
        have heqfun : ((fun p : ℝ × ℝ => Work.Elliptic.Ktheta p.2
              * Work.Spaces.DzIter k f p.1 p.2) ∘ fun x : ℝ => (x, θ))
            = fun x : ℝ => Work.Elliptic.Ktheta θ * Work.Spaces.DzIter k f x θ := by
          funext x; rfl
        rw [heqfun] at hcomp
        exact hcomp.continuousAt (isOpen_Ioi.mem_nhds hz)
  have key := MeasureTheory.continuousAt_of_dominated
    (μ := volume.restrict Work.Spaces.Iθ)
    (F := fun x θ => Work.Elliptic.Ktheta θ * Work.Spaces.DzIter k f x θ)
    (bound := fun _ => 3 * (C0 * (2 * z) ^ ((3 : ℝ) / 2)))
    (x₀ := z) hmeas hbound (MeasureTheory.integrable_const _) hcont
  simpa only [Work.Elliptic.Qang] using key

/-! ## The angular moment at level `0`, and the density of `L₁₂` -/

/-- The bound `|Qang f 0 s| ≤ 3(π/2) C₀ Rwt s`, by the `θ`-integral mean inequality. -/
theorem abs_Qang_zero_le {f : ℝ → ℝ → ℝ} {C0 : ℝ} (hC0 : 0 ≤ C0)
    (h4 : ContDiffOn ℝ 4 (Function.uncurry f) Work.FTS.EllipticEst.Q0)
    (hbd : ∀ k : ℕ, k ≤ 2 → ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      |Work.Spaces.DzIter k f z θ| ≤ C0 * Rwt z)
    {s : ℝ} (hs : 0 < s) :
    |Work.Elliptic.Qang f 0 s| ≤ 3 * (Real.pi / 2) * (C0 * Rwt s) := by
  have hint := integrable_Ktheta_mul_DzIter hC0 h4 hbd (k := 0) (by omega) hs
  have hbnd := abs_Ktheta_mul_DzIter_le hC0 hbd (k := 0) (by omega) hs
  have h1 : ‖Work.Elliptic.Qang f 0 s‖
      ≤ ∫ θ in Work.Spaces.Iθ, ‖Work.Elliptic.Ktheta θ * Work.Spaces.DzIter 0 f s θ‖ := by
    rw [Work.Elliptic.Qang]
    exact MeasureTheory.norm_integral_le_integral_norm _
  have h2 : (∫ θ in Work.Spaces.Iθ, ‖Work.Elliptic.Ktheta θ
        * Work.Spaces.DzIter 0 f s θ‖)
      ≤ ∫ θ in Work.Spaces.Iθ, 3 * (C0 * Rwt s) :=
    MeasureTheory.integral_mono_ae hint.norm (MeasureTheory.integrable_const _) hbnd
  have h3 : (∫ θ in Work.Spaces.Iθ, 3 * (C0 * Rwt s))
      = 3 * (Real.pi / 2) * (C0 * Rwt s) := by
    rw [Work.Elliptic.integral_Iθ_eq_interval, intervalIntegral.integral_const]
    simp only [sub_zero, smul_eq_mul]
    ring
  rw [Real.norm_eq_abs] at h1
  linarith [h1, h2, le_of_eq h3]

/-- `Work.FM.L12dens Work.Spaces.K f` is the elliptic density `Work.Elliptic.L12dens f`, i.e.
`Qang f 0 s / s`. -/
theorem L12dens_eq_Qang_zero (f : ℝ → ℝ → ℝ) (s : ℝ) :
    Work.FM.L12dens Work.Spaces.K f s = Work.Elliptic.Qang f 0 s / s :=
  Work.Elliptic.L12dens_eq_Qang_div f s

/-- The pointwise bound on the density of `L₁₂`:
`|L12dens (f) s| ≤ 3(π/2) C₀ s^{1/2}/(1+s)²`. -/
theorem abs_L12dens_le {f : ℝ → ℝ → ℝ} {C0 : ℝ} (hC0 : 0 ≤ C0)
    (h4 : ContDiffOn ℝ 4 (Function.uncurry f) Work.FTS.EllipticEst.Q0)
    (hbd : ∀ k : ℕ, k ≤ 2 → ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      |Work.Spaces.DzIter k f z θ| ≤ C0 * Rwt z)
    {s : ℝ} (hs : 0 < s) :
    |Work.FM.L12dens Work.Spaces.K f s|
      ≤ 3 * (Real.pi / 2) * C0 * (s ^ ((1 : ℝ) / 2) / (1 + s) ^ 2) := by
  have h := abs_Qang_zero_le hC0 h4 hbd hs
  have hstep : (3 * (Real.pi / 2) * (C0 * Rwt s)) / s
      = 3 * (Real.pi / 2) * C0 * (Rwt s / s) := by
    rw [div_eq_mul_inv, div_eq_mul_inv]
    ring
  calc |Work.FM.L12dens Work.Spaces.K f s|
      = |Work.Elliptic.Qang f 0 s| / s := by
        rw [L12dens_eq_Qang_zero, abs_div, abs_of_pos hs]
    _ ≤ (3 * (Real.pi / 2) * (C0 * Rwt s)) / s := div_le_div_of_nonneg_right h hs.le
    _ = 3 * (Real.pi / 2) * C0 * (Rwt s / s) := hstep
    _ = 3 * (Real.pi / 2) * C0 * (s ^ ((1 : ℝ) / 2) / (1 + s) ^ 2) := by
        rw [Rwt_div s hs]

/-- Continuity of the density of `L₁₂` on `(0,∞)`. -/
theorem L12dens_continuousOn {f : ℝ → ℝ → ℝ} {C0 : ℝ} (hC0 : 0 ≤ C0)
    (h4 : ContDiffOn ℝ 4 (Function.uncurry f) Work.FTS.EllipticEst.Q0)
    (hbd : ∀ k : ℕ, k ≤ 2 → ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      |Work.Spaces.DzIter k f z θ| ≤ C0 * Rwt z) :
    ContinuousOn (Work.FM.L12dens Work.Spaces.K f) (Set.Ioi 0) := by
  refine ContinuousOn.congr (s := Set.Ioi 0)
    (f := fun s => Work.Elliptic.Qang f 0 s / s)
    (g := Work.FM.L12dens Work.Spaces.K f) ?_ ?_
  · intro s hs
    exact ((Qang_continuousAt hC0 h4 hbd (k := 0) (by omega) hs).div continuousAt_id
      (ne_of_gt hs)).continuousWithinAt
  · intro s _
    exact L12dens_eq_Qang_zero f s

/-! ## Integrability of the density and of the majorant -/

/-- `s ↦ s^{1/2}/(1+s)²` is integrable on `(a,∞)` for `a > 0` (it is dominated by
`s^{-3/2}`). -/
theorem integrable_majorant {a : ℝ} (ha : 0 < a) :
    Integrable (fun s : ℝ => s ^ ((1 : ℝ) / 2) / (1 + s) ^ 2)
      (volume.restrict (Set.Ioi a)) := by
  have hbase : Integrable (fun s : ℝ => s ^ (-(3 : ℝ) / 2))
      (volume.restrict (Set.Ioi a)) :=
    integrableOn_Ioi_rpow_of_lt (by norm_num : (-(3 : ℝ) / 2) < -1) ha
  refine MeasureTheory.Integrable.mono' hbase ?_ ?_
  · refine ContinuousOn.aestronglyMeasurable (s := Set.Ioi a) ?_ measurableSet_Ioi
    refine ContinuousOn.div ?_ ?_ ?_
    · exact continuousOn_id.rpow_const (fun s hs => Or.inl (ne_of_gt (ha.trans hs)))
    · exact (continuousOn_const.add continuousOn_id).pow 2
    · intro s hs
      exact pow_ne_zero 2 (by linarith [ha.trans hs] : (1 : ℝ) + s ≠ 0)
  · rw [MeasureTheory.ae_restrict_iff' measurableSet_Ioi]
    refine Eventually.of_forall fun s hs => ?_
    have hs' : 0 < s := ha.trans hs
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    have h1 : s ^ ((1 : ℝ) / 2) / (1 + s) ^ 2 ≤ s ^ ((1 : ℝ) / 2) / s ^ 2 := by
      rw [div_le_div_iff₀ (by positivity : (0 : ℝ) < (1 + s) ^ 2)
        (by positivity : (0 : ℝ) < s ^ 2)]
      have h2 : s ^ 2 ≤ (1 + s) ^ 2 := by nlinarith
      exact mul_le_mul_of_nonneg_left h2 (by positivity)
    have h2 : s ^ ((1 : ℝ) / 2) / s ^ 2 = s ^ (-(3 : ℝ) / 2) := by
      rw [← Real.rpow_natCast s 2]
      rw [← Real.rpow_sub hs']
      norm_num
    linarith [h1, le_of_eq h2]

/-- **Integrability of the `L₁₂`-density** on `(a,∞)` for `a > 0`. -/
theorem L12dens_integrableOn {f : ℝ → ℝ → ℝ} {C0 : ℝ} (hC0 : 0 ≤ C0)
    (h4 : ContDiffOn ℝ 4 (Function.uncurry f) Work.FTS.EllipticEst.Q0)
    (hbd : ∀ k : ℕ, k ≤ 2 → ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      |Work.Spaces.DzIter k f z θ| ≤ C0 * Rwt z)
    {a : ℝ} (ha : 0 < a) :
    Integrable (Work.FM.L12dens Work.Spaces.K f) (volume.restrict (Set.Ioi a)) := by
  have hcont := L12dens_continuousOn hC0 h4 hbd
  have haesm : AEStronglyMeasurable (Work.FM.L12dens Work.Spaces.K f)
      (volume.restrict (Set.Ioi a)) :=
    (hcont.mono (Set.Ioi_subset_Ioi ha.le)).aestronglyMeasurable measurableSet_Ioi
  have hmaj : Integrable
      (fun s : ℝ => 3 * (Real.pi / 2) * C0 * (s ^ ((1 : ℝ) / 2) / (1 + s) ^ 2))
      (volume.restrict (Set.Ioi a)) :=
    (integrable_majorant ha).const_mul _
  refine MeasureTheory.Integrable.mono' hmaj haesm ?_
  rw [MeasureTheory.ae_restrict_iff' measurableSet_Ioi]
  refine Eventually.of_forall fun s hs => ?_
  rw [Real.norm_eq_abs]
  exact abs_L12dens_le hC0 h4 hbd (ha.trans hs)

/-! ## The derivative of `L₁₂` -/

/-- **`∂_z L₁₂(f)(z) = - L12dens (f)(z)`** for `z > 0`. -/
theorem Construction_L12_hasDerivAt {f : ℝ → ℝ → ℝ} {C0 : ℝ} (hC0 : 0 ≤ C0)
    (h4 : ContDiffOn ℝ 4 (Function.uncurry f) Work.FTS.EllipticEst.Q0)
    (hbd : ∀ k : ℕ, k ≤ 2 → ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      |Work.Spaces.DzIter k f z θ| ≤ C0 * Rwt z)
    {z : ℝ} (hz : 0 < z) :
    HasDerivAt (fun z => Work.Construction.L12 f z)
      (-(Work.Construction.L12dens f z)) z := by
  have hint : Integrable (Work.FM.L12dens Work.Spaces.K f)
      (volume.restrict (Set.Ioi (z / 2))) :=
    L12dens_integrableOn hC0 h4 hbd (by linarith)
  have hcont : ContinuousAt (Work.FM.L12dens Work.Spaces.K f) z :=
    (L12dens_continuousOn hC0 h4 hbd).continuousAt (isOpen_Ioi.mem_nhds hz)
  simpa only [Work.Construction.L12, Work.Construction.L12dens] using
    Work.FM.hasDerivAt_L12 (K := Work.Spaces.K) (f := f) hint hcont (by linarith)

end Work.FTS_RegExport.RXT.L12Iter
