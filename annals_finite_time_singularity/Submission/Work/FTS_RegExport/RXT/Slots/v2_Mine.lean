/-
Copyright: work module for the Elgindi finite-time singularity project.

# `v2_Mine` — the analytic core of `v2_L12DzIterTendsto`

This module reduces the target

  `∀ j ≤ 3, ∀ z > 0, D_z^j (L₁₂ ∘ F n)(z) → D_z^j (L₁₂ ∘ G)(z)`

to the *angular-moment* identity

  `D_z^{k+1} (L₁₂ f)(z) = - Qang f k z`,   `Qang f k z = ∫_θ K(θ)·D_z^k f(z,θ) dθ`

for `k ≤ 2`, together with the two dominated-convergence statements in `θ`
(`Qang`-convergence) and in `z` (`L₁₂`-convergence, i.e. the convergence of the
`k = 0` base case).

The hypotheses of the slot are exactly the `ContDiffOn ℝ 4`-on-the-open-quadrant plus the
pointwise bound `JetBnd C0` and the pointwise convergence `hconv`; nothing else (no `C^∞`,
no `ℋ^k`-membership) is used.

Everything here is `sorry`-free.
-/
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Order.CompletePartialOrder
import Submission.Work.Spaces.Defs
import Submission.Work.Spaces.aesm_slice_of_continuousOn_Qd
import Submission.Work.Elliptic.Defs
import Submission.Work.Elliptic.L12Aux
import Submission.Work.Construction.Defs
import Submission.Work.FM.Core2
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.FTS.EllipticEst.RegQ.pthU_slot_alg
import Submission.Work.FTS_RegExport.RXT.Slots.v2_Prelim

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS_RegExport.RXT.Slots

set_option autoImplicit false
set_option maxHeartbeats 800000

/-! ## The jet of `L₁₂` -/

/-- The `j`-th `D_z`-jet of `L₁₂ f`: the value `L₁₂ f` for `j = 0` and `-Qang f (j-1)`
for `j ≥ 1`.  This is the value produced by the angular-moment identity. -/
def L12jet (f : ℝ → ℝ → ℝ) (j : ℕ) (z : ℝ) : ℝ :=
  match j with
  | 0 => Work.Construction.L12 f z
  | (k + 1) => -Work.Elliptic.Qang f k z

@[simp] theorem L12jet_zero (f : ℝ → ℝ → ℝ) (z : ℝ) :
    L12jet f 0 z = Work.Construction.L12 f z := rfl

@[simp] theorem L12jet_succ (f : ℝ → ℝ → ℝ) (k : ℕ) (z : ℝ) :
    L12jet f (k + 1) z = -Work.Elliptic.Qang f k z := rfl

/-! ## Transfer of the pointwise bound to the limit -/

/-- The pointwise bound passes to the limit. -/
theorem JetBnd.of_tendsto {C0 : ℝ} {F : ℕ → ℝ → ℝ → ℝ} {G : ℝ → ℝ → ℝ}
    (hbnd : ∀ n : ℕ, JetBnd C0 (F n))
    (hconv : ∀ (b a : ℕ), a + b ≤ 2 → ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      Filter.Tendsto (fun n : ℕ => Work.Spaces.mixed b a (F n) z θ) Filter.atTop
        (nhds (Work.Spaces.mixed b a G z θ))) :
    JetBnd C0 G := by
  intro b a hab z θ hz h0 h1
  exact le_of_tendsto (hconv b a hab z θ hz h0 h1).abs
    (Filter.Eventually.of_forall (fun n => hbnd n b a hab z θ hz h0 h1))

/-! ## The a.e. bound on the angular slices -/

/-- A.e. on `Iθ`, `‖K(θ)·D_z^k f(z,θ)‖ ≤ 3·C₀·z^{3/2}/(1+z)²` for `k ≤ 2`. -/
theorem JetBnd.abs_Ktheta_mul_DzIter_le_ae {C0 : ℝ} {f : ℝ → ℝ → ℝ} (hb : JetBnd C0 f)
    {k : ℕ} (hk : k ≤ 2) {z : ℝ} (hz : 0 < z) :
    ∀ᵐ θ ∂(volume.restrict Work.Spaces.Iθ),
      ‖Work.Elliptic.Ktheta θ * Work.Spaces.DzIter k f z θ‖
        ≤ 3 * (C0 * (z ^ ((3 : ℝ) / 2) / (1 + z) ^ 2)) := by
  rw [restrict_Iθ_eq_restrict_Ioo]
  refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioo (fun θ hθ => ?_)
  rw [Real.norm_eq_abs, abs_mul]
  refine le_trans (mul_le_mul (abs_Ktheta_le θ) (hb k 0 (by omega) z θ hz hθ.1 hθ.2)
    (abs_nonneg _) (by norm_num)) (le_of_eq (by ring))

/-! ## Slice derivatives of the `D_z`-iterates -/

/-- For `f` of class `C⁴` on the open quadrant and `k ≤ 3`, the radial slice of `D_z^k f`
has derivative `pz (D_z^k f)` at every point of the open quadrant. -/
theorem DzIter_slice_hasDerivAt_pz {f : ℝ → ℝ → ℝ}
    (hF : ContDiffOn ℝ 4 (Function.uncurry f) Work.FTS.EllipticEst.Q0) {k : ℕ} (hk : k ≤ 3)
    {z θ : ℝ} (hz : 0 < z) (h0 : 0 < θ) (h1 : θ < Real.pi / 2) :
    HasDerivAt (fun x => Work.Spaces.DzIter k f x θ)
      (Work.Spaces.pz (Work.Spaces.DzIter k f) z θ) z := by
  have hcd := Work.FTS.EllipticEst.RegQ.Q2.contDiffOn_DzIter_fin
    Work.FTS.EllipticEst.isOpen_Q0 hF k (Nat.le_trans hk (by norm_num))
  have hcd1 : ContDiffOn ℝ 1 (Function.uncurry (Work.Spaces.DzIter k f))
      Work.FTS.EllipticEst.Q0 :=
    hcd.of_le (Nat.cast_le.mpr (by omega : 1 ≤ 4 - k))
  have hslice : ContDiffOn ℝ 1 (fun x => Work.Spaces.DzIter k f x θ) (Set.Ioi 0) :=
    Work.FTS.EllipticEst.RegQ.Q2.contDiffOn_slice_z_fin hcd1 ⟨h0, h1⟩
  have hdiff : DifferentiableAt ℝ (fun x => Work.Spaces.DzIter k f x θ) z :=
    (hslice.differentiableOn one_ne_zero).differentiableAt (isOpen_Ioi.mem_nhds hz)
  exact hdiff.hasDerivAt

/-- `D_z^k f` is `C¹` on the open quadrant as soon as `f` is `C⁴` there and `k ≤ 3`. -/
theorem contDiffOn_one_DzIter_jet {f : ℝ → ℝ → ℝ}
    (hF : ContDiffOn ℝ 4 (Function.uncurry f) Work.FTS.EllipticEst.Q0) {k : ℕ} (hk : k ≤ 3) :
    ContDiffOn ℝ 1 (Function.uncurry (Work.Spaces.DzIter k f)) Work.FTS.EllipticEst.Q0 :=
  (Work.FTS.EllipticEst.RegQ.Q2.contDiffOn_DzIter_fin Work.FTS.EllipticEst.isOpen_Q0 hF k
    (Nat.le_trans hk (by norm_num))).of_le (Nat.cast_le.mpr (by omega : 1 ≤ 4 - k))

/-- `K(θ)` is continuous on the open quadrant. -/
theorem continuousOn_Ktheta_jet :
    ContinuousOn (fun p : ℝ × ℝ => Work.Elliptic.Ktheta p.2) Work.FTS.EllipticEst.Q0 := by
  have hfun : (fun p : ℝ × ℝ => Work.Elliptic.Ktheta p.2)
      = fun p : ℝ × ℝ => 3 * Real.sin p.2 * Real.cos p.2 ^ 2 := by
    funext p; rw [Work.Elliptic.Ktheta]
  rw [hfun]
  exact ((continuous_const.mul (Real.continuous_sin.comp continuous_snd)).mul
    ((Real.continuous_cos.comp continuous_snd).pow 2)).continuousOn

/-- The same with the derivative written in the divided form `D_z^{k+1} f(z,θ)/z`. -/
theorem DzIter_slice_hasDerivAt_div {f : ℝ → ℝ → ℝ}
    (hF : ContDiffOn ℝ 4 (Function.uncurry f) Work.FTS.EllipticEst.Q0) {k : ℕ} (hk : k ≤ 3)
    {z θ : ℝ} (hz : 0 < z) (h0 : 0 < θ) (h1 : θ < Real.pi / 2) :
    HasDerivAt (fun x => Work.Spaces.DzIter k f x θ)
      (Work.Spaces.DzIter (k + 1) f z θ / z) z := by
  have h := DzIter_slice_hasDerivAt_pz hF hk hz h0 h1
  have hval : Work.Spaces.pz (Work.Spaces.DzIter k f) z θ
      = Work.Spaces.DzIter (k + 1) f z θ / z := by
    rw [show Work.Spaces.DzIter (k + 1) f z θ
        = z * Work.Spaces.pz (Work.Spaces.DzIter k f) z θ from rfl,
      mul_div_cancel_left₀ _ (ne_of_gt hz)]
  rwa [hval] at h

/-! ## The moment identities -/

/-- `Qang f (k+1) z = z · ∫_θ K(θ)·∂_z(D_z^k f)(z,θ) dθ`, by linearity of the `θ`-integral. -/
theorem Qang_succ_eq (f : ℝ → ℝ → ℝ) (k : ℕ) (z : ℝ) :
    Work.Elliptic.Qang f (k + 1) z
      = z * ∫ θ in Work.Spaces.Iθ,
          Work.Elliptic.Ktheta θ * Work.Spaces.pz (Work.Spaces.DzIter k f) z θ := by
  have h1 : Work.Elliptic.Qang f (k + 1) z
      = ∫ θ in Work.Spaces.Iθ, Work.Elliptic.Ktheta θ
          * (z * Work.Spaces.pz (Work.Spaces.DzIter k f) z θ) := rfl
  rw [h1, show (fun θ => Work.Elliptic.Ktheta θ
        * (z * Work.Spaces.pz (Work.Spaces.DzIter k f) z θ))
      = fun θ => z * (Work.Elliptic.Ktheta θ
          * Work.Spaces.pz (Work.Spaces.DzIter k f) z θ) from by funext θ; ring,
    MeasureTheory.integral_const_mul]

/-- The divided form of `Qang_succ_eq`. -/
theorem Qang_succ_div (f : ℝ → ℝ → ℝ) (k : ℕ) {z : ℝ} (hz : z ≠ 0) :
    (∫ θ in Work.Spaces.Iθ,
        Work.Elliptic.Ktheta θ * Work.Spaces.pz (Work.Spaces.DzIter k f) z θ)
      = Work.Elliptic.Qang f (k + 1) z / z := by
  rw [Qang_succ_eq f k z, mul_div_cancel_left₀ _ hz]

/-! ## The derivative of `L₁₂` -/

/-- `∂_z L₁₂(f) = -(Qang f 0 z / z)`: the `k = 0` base case of the tower. -/
theorem Construction_L12_hasDerivAt_jet {C0 : ℝ} {f : ℝ → ℝ → ℝ} (hC0 : 0 ≤ C0)
    (hb : JetBnd C0 f)
    (hcont : ContinuousOn (fun s => Work.Elliptic.L12dens f s) (Set.Ioi 0))
    {z : ℝ} (hz : 0 < z) :
    HasDerivAt (fun σ => Work.Construction.L12 f σ) (-(Work.Elliptic.Qang f 0 z / z)) z := by
  have hint : IntegrableOn (fun s => Work.Elliptic.L12dens f s) (Set.Ioi (z / 2)) :=
    hb.dens_integrable hC0 hcont (by linarith)
  have hint' : IntegrableOn (Work.FM.L12dens Work.Spaces.K f) (Set.Ioi (z / 2)) := hint
  have hcontAt : ContinuousAt (Work.FM.L12dens Work.Spaces.K f) z :=
    (hcont.continuousAt (isOpen_Ioi.mem_nhds hz))
  have key := Work.FM.hasDerivAt_L12_of_integrable (K := Work.Spaces.K) (f := f)
    (a := z / 2) (ρ := z) hint' (fun s hs => hcont.continuousAt
      (isOpen_Ioi.mem_nhds (by linarith : (0 : ℝ) < s))) (by linarith)
  have hden : Work.FM.L12dens Work.Spaces.K f z = Work.Elliptic.Qang f 0 z / z :=
    Work.Elliptic.L12dens_eq_Qang_div f z
  rw [hden] at key
  simpa only [Work.Construction.L12] using key

/-! ## The two `Qang`-derivatives and the two dominated-convergence statements -/

/-- The elliptic density is the fundamental-model density for `K = K(θ) = 3 sin θ cos²θ`. -/
theorem L12dens_eq_fm (f : ℝ → ℝ → ℝ) :
    Work.Elliptic.L12dens f = Work.FM.L12dens Work.Spaces.K f := rfl

/-- `∂_z (Qang f 0)(z) = Qang f 1 z / z`. -/
theorem QangZeroDeriv_jet {C0 : ℝ} {f : ℝ → ℝ → ℝ} (hC0 : 0 ≤ C0)
    (hF : ContDiffOn ℝ 4 (Function.uncurry f) Work.FTS.EllipticEst.Q0) (hb : JetBnd C0 f)
    {z : ℝ} (hz : 0 < z) :
    HasDerivAt (Work.Elliptic.Qang f 0) (Work.Elliptic.Qang f 1 z / z) z := by
  haveI : IsFiniteMeasure (volume.restrict Work.Spaces.Iθ) := isFiniteMeasure_restrict_Iθ
  have hz2 : 0 < z / 2 := by linarith
  have hVmem : z ∈ Set.Ioi (z / 2) := Set.mem_Ioi.mpr (by linarith)
  have hVpos : ∀ x ∈ Set.Ioi (z / 2), 0 < x :=
    fun x hx => lt_trans hz2 (Set.mem_Ioi.mp hx)
  have hcf : ContinuousOn (Function.uncurry (fun x θ => Work.Elliptic.Ktheta θ * f x θ))
      Work.FTS.EllipticEst.Q0 :=
    show ContinuousOn (fun p : ℝ × ℝ => Work.Elliptic.Ktheta p.2 * f p.1 p.2)
      Work.FTS.EllipticEst.Q0 from
      continuousOn_Ktheta_jet.mul (show ContinuousOn (fun p : ℝ × ℝ => f p.1 p.2)
        Work.FTS.EllipticEst.Q0 from hF.continuousOn)
  have hcpz : ContinuousOn
      (Function.uncurry (fun x θ => Work.Elliptic.Ktheta θ * Work.Spaces.pz f x θ))
      Work.FTS.EllipticEst.Q0 :=
    show ContinuousOn (fun p : ℝ × ℝ => Work.Elliptic.Ktheta p.2 * Work.Spaces.pz f p.1 p.2)
      Work.FTS.EllipticEst.Q0 from
      continuousOn_Ktheta_jet.mul
        (show ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.pz f p.1 p.2)
          Work.FTS.EllipticEst.Q0 from
          (Work.FTS.EllipticEst.RegQ.Q2.contDiffOn_pz_fin Work.FTS.EllipticEst.isOpen_Q0
            (n := 3) hF).continuousOn)
  have hint : Integrable (fun θ => Work.Elliptic.Ktheta θ * f z θ)
      (volume.restrict Work.Spaces.Iθ) :=
    Integrable.mono' (integrable_const (3 * (C0 * (z ^ ((3 : ℝ) / 2) / (1 + z) ^ 2))))
      (aesm_slice_Q0 hcf hz) (hb.abs_Ktheta_mul_DzIter_le_ae (k := 0) (by norm_num) hz)
  have hbound : ∀ᵐ θ ∂(volume.restrict Work.Spaces.Iθ), ∀ x ∈ Set.Ioi (z / 2),
      ‖Work.Elliptic.Ktheta θ * Work.Spaces.pz f x θ‖
        ≤ 3 * C0 * ((z / 2) ^ (-(3 : ℝ) / 2) + 1) := by
    rw [restrict_Iθ_eq_restrict_Ioo]
    refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioo (fun θ hθ x hx => ?_)
    rw [Real.norm_eq_abs, abs_mul]
    refine le_trans (mul_le_mul (abs_Ktheta_le θ)
      (le_trans (hb.pz_DzIter_le (k := 0) (by norm_num) (hVpos x hx) hθ.1 hθ.2)
        (mul_le_mul_of_nonneg_left (rpow_half_div_sq_le hz2 (le_of_lt (Set.mem_Ioi.mp hx))) hC0))
      (abs_nonneg _) (by norm_num)) (le_of_eq (by ring))
  have hdiff : ∀ θ ∈ Set.Ioo 0 (Real.pi / 2), ∀ x ∈ Set.Ioi (z / 2),
      HasDerivAt (fun y => Work.Elliptic.Ktheta θ * f y θ)
        (Work.Elliptic.Ktheta θ * Work.Spaces.pz f x θ) x :=
    fun θ hθ x hx =>
      (DzIter_slice_hasDerivAt_pz hF (k := 0) (by norm_num) (hVpos x hx) hθ.1 hθ.2).const_mul _
  have key := hasDerivAt_integral_Itheta_Q0 (V := Set.Ioi (z / 2)) isOpen_Ioi hVmem hVpos
    hcf hcpz hint hbound hdiff
  have hval : (∫ θ in Work.Spaces.Iθ, Work.Elliptic.Ktheta θ * Work.Spaces.pz f z θ)
      = Work.Elliptic.Qang f 1 z / z := Qang_succ_div f 0 (ne_of_gt hz)
  rw [hval] at key
  exact key

/-- `∂_z (Qang f 1)(z) = Qang f 2 z / z`. -/
theorem QangOneDeriv_jet {C0 : ℝ} {f : ℝ → ℝ → ℝ} (hC0 : 0 ≤ C0)
    (hF : ContDiffOn ℝ 4 (Function.uncurry f) Work.FTS.EllipticEst.Q0) (hb : JetBnd C0 f)
    {z : ℝ} (hz : 0 < z) :
    HasDerivAt (Work.Elliptic.Qang f 1) (Work.Elliptic.Qang f 2 z / z) z := by
  haveI : IsFiniteMeasure (volume.restrict Work.Spaces.Iθ) := isFiniteMeasure_restrict_Iθ
  have hz2 : 0 < z / 2 := by linarith
  have hVmem : z ∈ Set.Ioi (z / 2) := Set.mem_Ioi.mpr (by linarith)
  have hVpos : ∀ x ∈ Set.Ioi (z / 2), 0 < x :=
    fun x hx => lt_trans hz2 (Set.mem_Ioi.mp hx)
  have hcd3 : ContDiffOn ℝ 3 (Function.uncurry (Work.Spaces.DzIter 1 f))
      Work.FTS.EllipticEst.Q0 :=
    Work.FTS.EllipticEst.RegQ.Q2.contDiffOn_DzIter_fin Work.FTS.EllipticEst.isOpen_Q0 hF 1
      (by norm_num)
  have hcd2 : ContDiffOn ℝ 2 (Function.uncurry (Work.Spaces.pz (Work.Spaces.DzIter 1 f)))
      Work.FTS.EllipticEst.Q0 :=
    Work.FTS.EllipticEst.RegQ.Q2.contDiffOn_pz_fin Work.FTS.EllipticEst.isOpen_Q0 (n := 2) hcd3
  have hcg : ContinuousOn
      (Function.uncurry (fun x θ => Work.Elliptic.Ktheta θ * Work.Spaces.DzIter 1 f x θ))
      Work.FTS.EllipticEst.Q0 :=
    show ContinuousOn (fun p : ℝ × ℝ => Work.Elliptic.Ktheta p.2
        * Work.Spaces.DzIter 1 f p.1 p.2) Work.FTS.EllipticEst.Q0 from
      continuousOn_Ktheta_jet.mul (show ContinuousOn (fun p : ℝ × ℝ =>
        Work.Spaces.DzIter 1 f p.1 p.2) Work.FTS.EllipticEst.Q0 from hcd3.continuousOn)
  have hcg' : ContinuousOn
      (Function.uncurry (fun x θ => Work.Elliptic.Ktheta θ
        * Work.Spaces.pz (Work.Spaces.DzIter 1 f) x θ)) Work.FTS.EllipticEst.Q0 :=
    show ContinuousOn (fun p : ℝ × ℝ => Work.Elliptic.Ktheta p.2
        * Work.Spaces.pz (Work.Spaces.DzIter 1 f) p.1 p.2) Work.FTS.EllipticEst.Q0 from
      continuousOn_Ktheta_jet.mul (show ContinuousOn (fun p : ℝ × ℝ =>
        Work.Spaces.pz (Work.Spaces.DzIter 1 f) p.1 p.2) Work.FTS.EllipticEst.Q0 from
        hcd2.continuousOn)
  have hint : Integrable (fun θ => Work.Elliptic.Ktheta θ * Work.Spaces.DzIter 1 f z θ)
      (volume.restrict Work.Spaces.Iθ) :=
    Integrable.mono' (integrable_const (3 * (C0 * (z ^ ((3 : ℝ) / 2) / (1 + z) ^ 2))))
      (aesm_slice_Q0 hcg hz) (hb.abs_Ktheta_mul_DzIter_le_ae (k := 1) (by norm_num) hz)
  have hbound : ∀ᵐ θ ∂(volume.restrict Work.Spaces.Iθ), ∀ x ∈ Set.Ioi (z / 2),
      ‖Work.Elliptic.Ktheta θ * Work.Spaces.pz (Work.Spaces.DzIter 1 f) x θ‖
        ≤ 3 * C0 * ((z / 2) ^ (-(3 : ℝ) / 2) + 1) := by
    rw [restrict_Iθ_eq_restrict_Ioo]
    refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioo (fun θ hθ x hx => ?_)
    rw [Real.norm_eq_abs, abs_mul]
    refine le_trans (mul_le_mul (abs_Ktheta_le θ)
      (le_trans (hb.pz_DzIter_le (k := 1) (by norm_num) (hVpos x hx) hθ.1 hθ.2)
        (mul_le_mul_of_nonneg_left (rpow_half_div_sq_le hz2 (le_of_lt (Set.mem_Ioi.mp hx))) hC0))
      (abs_nonneg _) (by norm_num)) (le_of_eq (by ring))
  have hdiff : ∀ θ ∈ Set.Ioo 0 (Real.pi / 2), ∀ x ∈ Set.Ioi (z / 2),
      HasDerivAt (fun y => Work.Elliptic.Ktheta θ * Work.Spaces.DzIter 1 f y θ)
        (Work.Elliptic.Ktheta θ * Work.Spaces.pz (Work.Spaces.DzIter 1 f) x θ) x :=
    fun θ hθ x hx =>
      (DzIter_slice_hasDerivAt_pz hF (k := 1) (by norm_num) (hVpos x hx) hθ.1 hθ.2).const_mul _
  have key := hasDerivAt_integral_Itheta_Q0 (V := Set.Ioi (z / 2)) isOpen_Ioi hVmem hVpos
    hcg hcg' hint hbound hdiff
  have hval : (∫ θ in Work.Spaces.Iθ,
        Work.Elliptic.Ktheta θ * Work.Spaces.pz (Work.Spaces.DzIter 1 f) z θ)
      = Work.Elliptic.Qang f 2 z / z := Qang_succ_div f 1 (ne_of_gt hz)
  rw [hval] at key
  exact key

/-- Dominated convergence in `θ`: `Qang (F n) k z → Qang G k z` for `k ≤ 2`. -/
theorem QangTendsto_conv {C0 : ℝ} {Fs : ℕ → ℝ → ℝ → ℝ} {Gl : ℝ → ℝ → ℝ} (hC0 : 0 ≤ C0)
    (hF : ∀ n : ℕ, ContDiffOn ℝ 4 (Function.uncurry (Fs n)) Work.FTS.EllipticEst.Q0)
    (hbnd : ∀ n : ℕ, JetBnd C0 (Fs n)) (hbndG : JetBnd C0 Gl)
    (hconv : ∀ (b a : ℕ), a + b ≤ 4 → ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      Filter.Tendsto (fun n : ℕ => Work.Spaces.mixed b a (Fs n) z θ) Filter.atTop
        (nhds (Work.Spaces.mixed b a Gl z θ)))
    {k : ℕ} (hk : k ≤ 2) {z : ℝ} (hz : 0 < z) :
    Filter.Tendsto (fun n : ℕ => Work.Elliptic.Qang (Fs n) k z) Filter.atTop
      (nhds (Work.Elliptic.Qang Gl k z)) := by
  haveI : IsFiniteMeasure (volume.restrict Work.Spaces.Iθ) := isFiniteMeasure_restrict_Iθ
  have hk3 : k ≤ 3 := by omega
  have hmeasn : ∀ n : ℕ, AEStronglyMeasurable
      (fun θ => Work.Elliptic.Ktheta θ * Work.Spaces.DzIter k (Fs n) z θ)
      (volume.restrict Work.Spaces.Iθ) :=
    fun n => aesm_slice_Q0
      (show ContinuousOn (Function.uncurry (fun x θ => Work.Elliptic.Ktheta θ
          * Work.Spaces.DzIter k (Fs n) x θ)) Work.FTS.EllipticEst.Q0 from
        continuousOn_Ktheta_jet.mul (show ContinuousOn (fun p : ℝ × ℝ =>
          Work.Spaces.DzIter k (Fs n) p.1 p.2) Work.FTS.EllipticEst.Q0 from
          (contDiffOn_one_DzIter_jet (hF n) hk3).continuousOn)) hz
  have hboundn : ∀ n : ℕ, ∀ᵐ θ ∂(volume.restrict Work.Spaces.Iθ),
      ‖Work.Elliptic.Ktheta θ * Work.Spaces.DzIter k (Fs n) z θ‖
        ≤ 3 * (C0 * (z ^ ((3 : ℝ) / 2) / (1 + z) ^ 2)) :=
    fun n => (hbnd n).abs_Ktheta_mul_DzIter_le_ae hk hz
  have hlimit : ∀ᵐ θ ∂(volume.restrict Work.Spaces.Iθ),
      Filter.Tendsto (fun n : ℕ => Work.Elliptic.Ktheta θ * Work.Spaces.DzIter k (Fs n) z θ)
        Filter.atTop (nhds (Work.Elliptic.Ktheta θ * Work.Spaces.DzIter k Gl z θ)) := by
    rw [restrict_Iθ_eq_restrict_Ioo]
    refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioo (fun θ hθ => ?_)
    exact (hconv k 0 (by omega) z θ hz hθ.1 hθ.2).const_mul _
  have key := MeasureTheory.tendsto_integral_of_dominated_convergence
    (μ := volume.restrict Work.Spaces.Iθ)
    (F := fun (n : ℕ) (θ : ℝ) => Work.Elliptic.Ktheta θ * Work.Spaces.DzIter k (Fs n) z θ)
    (f := fun θ : ℝ => Work.Elliptic.Ktheta θ * Work.Spaces.DzIter k Gl z θ)
    (fun _ => 3 * (C0 * (z ^ ((3 : ℝ) / 2) / (1 + z) ^ 2)))
    hmeasn (integrable_const _) hboundn hlimit
  simpa only [Work.Elliptic.Qang] using key

/-- Dominated convergence in the radial variable: `L₁₂ (F n) z → L₁₂ G z`. -/
theorem L12Tendsto_dens {C0 z : ℝ} {Fs : ℕ → ℝ → ℝ → ℝ} {Gl : ℝ → ℝ → ℝ} (hC0 : 0 ≤ C0)
    (hbnd : ∀ n : ℕ, JetBnd C0 (Fs n))
    (hmeas : ∀ n : ℕ, AEStronglyMeasurable
      (fun s => Work.Elliptic.L12dens (Fs n) s) (volume.restrict (Set.Ioi z)))
    (hconv : ∀ s : ℝ, 0 < s → Filter.Tendsto (fun n : ℕ => Work.Elliptic.L12dens (Fs n) s)
      Filter.atTop (nhds (Work.Elliptic.L12dens Gl s)))
    (hz : 0 < z) :
    Filter.Tendsto (fun n : ℕ => Work.Construction.L12 (Fs n) z) Filter.atTop
      (nhds (Work.Construction.L12 Gl z)) := by
  have hmaj : Integrable (fun s : ℝ => 6 * C0 * s ^ (-(3 : ℝ) / 2))
      (volume.restrict (Set.Ioi z)) :=
    (integrableOn_Ioi_rpow_of_lt (by norm_num : (-(3 : ℝ) / 2) < -1) hz).const_mul _
  have hboundn : ∀ n : ℕ, ∀ᵐ s ∂(volume.restrict (Set.Ioi z)),
      ‖Work.Elliptic.L12dens (Fs n) s‖ ≤ 6 * C0 * s ^ (-(3 : ℝ) / 2) := by
    intro n
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
    exact (hbnd n).dens_bound hC0 (lt_of_lt_of_le hz (le_of_lt hs))
  have hlimit : ∀ᵐ s ∂(volume.restrict (Set.Ioi z)),
      Filter.Tendsto (fun n : ℕ => Work.Elliptic.L12dens (Fs n) s) Filter.atTop
        (nhds (Work.Elliptic.L12dens Gl s)) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
    exact hconv s (lt_of_lt_of_le hz (le_of_lt hs))
  have key := MeasureTheory.tendsto_integral_of_dominated_convergence
    (μ := volume.restrict (Set.Ioi z))
    (F := fun (n : ℕ) (s : ℝ) => Work.Elliptic.L12dens (Fs n) s)
    (f := fun s : ℝ => Work.Elliptic.L12dens Gl s)
    (fun s => 6 * C0 * s ^ (-(3 : ℝ) / 2)) hmeas hmaj hboundn hlimit
  simpa only [Work.Construction.L12, Work.FM.L12, L12dens_eq_fm] using key

/-! ## The angular-moment tower -/

/-- **The tower.**  Given, for every `w > 0`, the three derivative formulas
`∂_z Qang f 0 = Qang f 1 / z`, `∂_z Qang f 1 = Qang f 2 / z` and `∂_z L₁₂ f = -Qang f 0 / z`,
the `D_z`-jets of `L₁₂ f` up to order three are the `L12jet`s. -/
theorem dzdIter_L12_jet {C0 : ℝ} {f : ℝ → ℝ → ℝ} (hC0 : 0 ≤ C0)
    (hF : ContDiffOn ℝ 4 (Function.uncurry f) Work.FTS.EllipticEst.Q0) (hb : JetBnd C0 f)
    (hQ0 : ∀ w : ℝ, 0 < w →
      HasDerivAt (Work.Elliptic.Qang f 0) (Work.Elliptic.Qang f 1 w / w) w)
    (hQ1 : ∀ w : ℝ, 0 < w →
      HasDerivAt (Work.Elliptic.Qang f 1) (Work.Elliptic.Qang f 2 w / w) w)
    (hL : ∀ w : ℝ, 0 < w →
      HasDerivAt (fun σ => Work.Construction.L12 f σ) (-(Work.Elliptic.Qang f 0 w / w)) w)
    {j : ℕ} (hj : j ≤ 3) {z : ℝ} (hz : 0 < z) :
    Work.Elliptic.DzdIter j (fun z => Work.Construction.L12 f z) z = L12jet f j z := by
  have h1 : ∀ w : ℝ, 0 < w →
      Work.Elliptic.DzdIter 1 (fun z => Work.Construction.L12 f z) w
        = -Work.Elliptic.Qang f 0 w := by
    intro w hw
    show w * deriv (fun z => Work.Construction.L12 f z) w = -Work.Elliptic.Qang f 0 w
    rw [(hL w hw).deriv, mul_neg, ← mul_div_assoc, mul_div_cancel_left₀ _ (ne_of_gt hw)]
  have h2 : ∀ w : ℝ, 0 < w →
      Work.Elliptic.DzdIter 2 (fun z => Work.Construction.L12 f z) w
        = -Work.Elliptic.Qang f 1 w := by
    intro w hw
    have heq : Work.Elliptic.DzdIter 1 (fun z => Work.Construction.L12 f z)
        =ᶠ[𝓝 w] fun u => -Work.Elliptic.Qang f 0 u := by
      filter_upwards [isOpen_Ioi.mem_nhds hw] with u hu
      exact h1 u hu
    have hd : deriv (Work.Elliptic.DzdIter 1 (fun z => Work.Construction.L12 f z)) w
        = -(Work.Elliptic.Qang f 1 w / w) := by
      rw [heq.deriv_eq]
      exact (hQ0 w hw).neg.deriv
    show w * deriv (Work.Elliptic.DzdIter 1 (fun z => Work.Construction.L12 f z)) w
        = -Work.Elliptic.Qang f 1 w
    rw [hd, mul_neg, ← mul_div_assoc, mul_div_cancel_left₀ _ (ne_of_gt hw)]
  have h3 : ∀ w : ℝ, 0 < w →
      Work.Elliptic.DzdIter 3 (fun z => Work.Construction.L12 f z) w
        = -Work.Elliptic.Qang f 2 w := by
    intro w hw
    have heq : Work.Elliptic.DzdIter 2 (fun z => Work.Construction.L12 f z)
        =ᶠ[𝓝 w] fun u => -Work.Elliptic.Qang f 1 u := by
      filter_upwards [isOpen_Ioi.mem_nhds hw] with u hu
      exact h2 u hu
    have hd : deriv (Work.Elliptic.DzdIter 2 (fun z => Work.Construction.L12 f z)) w
        = -(Work.Elliptic.Qang f 2 w / w) := by
      rw [heq.deriv_eq]
      exact (hQ1 w hw).neg.deriv
    show w * deriv (Work.Elliptic.DzdIter 2 (fun z => Work.Construction.L12 f z)) w
        = -Work.Elliptic.Qang f 2 w
    rw [hd, mul_neg, ← mul_div_assoc, mul_div_cancel_left₀ _ (ne_of_gt hw)]
  have hj' : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 := by omega
  rcases hj' with rfl | rfl | rfl | rfl
  · simp
  · exact h1 z hz
  · exact h2 z hz
  · exact h3 z hz

end Work.FTS_RegExport.RXT.Slots
