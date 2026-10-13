/-
# `Work.FTS.LocData.ZFBase` — shared ingredients for the far-part `𝓗⁴`-majorant

This module collects the elementary facts that the pointwise estimate
`HkIntegrand α 4 (zfar L F_*) z θ ≤ C·α²·angMaj α θ/(1+z)²` of the localisation chapter
needs about

* the cut-off factor `1 - χ(·/L)`: a **uniform-in-`L`** bound on its iterated `D_z`-derivatives
  (`DzIter_oneSubChi_bound_uniform`),
* the profile `F_* = Fstar α`: the weighted derivative bounds
  `|D_z^a F_* · w| ≤ 4αΓ/z` and `|D_z^j D_θ^i F_* · w| ≤ 4·10⁵·αΓ/z` (`z ≥ 1`),
* the `z`-slice smoothness of everything in sight (the Leibniz rule
  `Work.FTS.LocData.DzIter_mul_smoothQuad` is phrased with the *genuine* smooth order
  `Work.Stability.smoothOrder`, which is the only order in which a cut-off is smooth),
* the elementary filter facts that make a function which vanishes on a whole neighbourhood of
  a point have vanishing derivatives there (`eventDzIter_zero`, `eventDthIter_zero`), which is
  how the estimates are saved below the cut-off where `w(z)` blows up.

This is the `ZfarFstar` counterpart of the (unbuildable) `ZFBasic` sketch.
-/
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.FTS.LocData.Defs
import Submission.Work.FTS.LocData.DzIter_mul_smoothQuad
import Submission.Work.FTS.LocData.DthIter_mul_smoothQuad
import Submission.Work.FTS.LocData.DzIter_oneSubChi_bound
import Submission.Work.FTS.LocData.DthIter_Gam_abs_le
import Submission.Work.FTS.LocData.Fstar_factor
import Submission.Work.FTS.LocData.PhiZ_eq
import Submission.Work.FTS.LocData.Phi_w_le
import Submission.Work.FTS.LocData.c_ge_three_fifths
import Submission.Work.Spaces.Gam_bounds
import Submission.Work.Stability.Cutoff

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.LocData
namespace ZFBase

set_option autoImplicit false
set_option maxHeartbeats 1000000

/-! ## 1. Elementary angular facts -/

theorem sin_two_nonneg_Iθ {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) : 0 ≤ Real.sin (2 * θ) :=
  Real.sin_nonneg_of_mem_Icc ⟨by linarith [hθ.1], by linarith [hθ.2, Real.pi_pos]⟩

/-! ## 2. `D_θ` of a product with a `z`-only factor -/

/-- `D_θ` is a derivation which, on a product `c(z)·g(z,θ)` with a factor depending only on `z`,
acts on the second factor only. -/
theorem DthIter_mul_left_z (i : ℕ) (c : ℝ → ℝ) (g : ℝ → ℝ → ℝ) :
    Work.Spaces.DthIter i (fun z θ => c z * g z θ)
      = fun z θ => c z * Work.Spaces.DthIter i g z θ := by
  induction i with
  | zero => rfl
  | succ i ih =>
      rw [Work.Spaces.DthIter_succ, ih, Work.Spaces.DthIter_succ]
      funext z θ
      simp only [Work.Spaces.Dth, Work.Spaces.pth]
      rw [deriv_const_mul_field]
      ring

/-! ## 3. `z`-slice smoothness -/

theorem contDiffOn_slice_oneSubChi (L : ℝ) :
    ContDiffOn ℝ Work.Stability.smoothOrder
      (fun z : ℝ => 1 - Work.Stability.chi (z / L)) (Set.Ioi (-1)) :=
  (contDiff_const.sub (Work.Stability.chi_contDiff.comp (contDiff_id.div_const L))).contDiffOn

theorem contDiffOn_slice_FM_Fstar :
    ContDiffOn ℝ Work.Stability.smoothOrder (fun z : ℝ => Work.FM.Fstar z) (Set.Ioi (-1)) := by
  have hnum : ContDiffOn ℝ Work.Stability.smoothOrder (fun z : ℝ => 2 * z) (Set.Ioi (-1)) :=
    contDiffOn_const.mul contDiffOn_id
  have hden : ContDiffOn ℝ Work.Stability.smoothOrder (fun z : ℝ => (1 + z) ^ 2) (Set.Ioi (-1)) :=
    (contDiffOn_const.add contDiffOn_id).pow 2
  have h := hnum.div hden
    (fun z hz => pow_ne_zero 2 (by have hz' : (-1 : ℝ) < z := hz; linarith))
  have hfun : (fun z : ℝ => Work.FM.Fstar z)
      = ((fun z : ℝ => 2 * z) / fun z : ℝ => (1 + z) ^ 2) := by
    funext z
    simp [Work.FM.Fstar, Pi.div_apply]
  rw [hfun]
  exact h

theorem contDiffOn_slice_Fstar (α : ℝ) (θ : ℝ) :
    ContDiffOn ℝ Work.Stability.smoothOrder (fun z : ℝ => Work.Construction.Fstar α z θ)
      (Set.Ioi (-1)) := by
  have h := contDiffOn_slice_FM_Fstar.const_smul (α * (Work.Spaces.Gam α θ / Work.Spaces.c α))
  refine h.congr (fun z _ => ?_)
  rw [Work.Construction.Fstar]
  ring

/-- The `z`-slices of `D_θ^i F_*` are smooth: `D_θ^i F_* = (α/c)·D_θ^iΓ(0,θ)·φ(z)` with
`φ = FM.Fstar` a function of `z` only. -/
theorem contDiffOn_slice_DthIter_Fstar (α : ℝ) (i : ℕ) (θ : ℝ) :
    ContDiffOn ℝ Work.Stability.smoothOrder
      (fun z : ℝ => Work.Spaces.DthIter i (Work.Construction.Fstar α) z θ) (Set.Ioi (-1)) := by
  have hfun : (fun z : ℝ => Work.Spaces.DthIter i (Work.Construction.Fstar α) z θ)
      = fun z : ℝ => ((α / Work.Spaces.c α)
          * Work.Spaces.DthIter i (fun _ θ' => Work.Spaces.Gam α θ') 0 θ) * Work.FM.Fstar z := by
    funext z
    rw [congrFun (congrFun (DthIter_Fstar_eq α i) z) θ, DthIter_gamFn_z_indep α i z 0 θ]
    ring
  rw [hfun]
  have h := contDiffOn_slice_FM_Fstar.const_smul ((α / Work.Spaces.c α)
    * Work.Spaces.DthIter i (fun _ θ' => Work.Spaces.Gam α θ') 0 θ)
  simpa [smul_eq_mul] using h

/-! ## 4. The uniform bound on the derivatives of the cut-off factor

The iterated `D_z`-derivatives of `1 - χ(·/L)` are bounded by a constant *independent of `L`*:
by the Stirling expansion `D_z^c = ∑_k S(c,k) (z/L)^k ∂^k(·/L)` the derivatives of the
rescaled cut-off reduce to `(z/L)^k ∂^k(1-χ)(z/L)`, and those are bounded uniformly by
`OneSubChi_deriv_bound` of `Work.FTS.LocData.DzIter_oneSubChi_bound`. -/

theorem DzIter_oneSubChi_bound_uniform :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (L : ℝ), 1 ≤ L → ∀ (c : ℕ), c ≤ 4 →
      ∀ z ∈ Work.Spaces.Iz, ∀ θ : ℝ,
      |Work.Spaces.DzIter c (fun z _ => (1 : ℝ) - Work.Stability.chi (z / L)) z θ| ≤ C := by
  obtain ⟨M, hM0, hMb⟩ := OneSubChi_deriv_bound
  have hM1 : 1 ≤ M := by
    have h := hMb 0 (by norm_num) (2 : ℝ)
    have h2 : iteratedDeriv 0 (fun x : ℝ => (1 : ℝ) - Work.Stability.chi x) (2 : ℝ) = 1 := by
      rw [iteratedDeriv_zero, Work.Stability.chi_eq_zero (by norm_num)]
      norm_num
    simpa [h2] using h
  refine ⟨100 * M, by linarith, fun L hL c hc z hz θ => ?_⟩
  have hLpos : 0 < L := lt_of_lt_of_le zero_lt_one hL
  have hLne : L ≠ 0 := ne_of_gt hLpos
  have hsmg : ContDiff ℝ Work.Stability.smoothOrder (fun x : ℝ => (1 : ℝ) - Work.Stability.chi x) :=
    contDiff_const.sub Work.Stability.chi_contDiff
  have hsmL : ContDiff ℝ Work.Stability.smoothOrder
      (fun x : ℝ => (1 : ℝ) - Work.Stability.chi (x / L)) :=
    hsmg.comp (contDiff_id.div_const L)
  -- 1. the θ-independent function is a `z`-only multiplier
  have h1 : Work.Spaces.DzIter c (fun z _ => (1 : ℝ) - Work.Stability.chi (z / L)) z θ
      = Work.Coercivity.CommutZ.DzIterZ c
          (fun x : ℝ => (1 : ℝ) - Work.Stability.chi (x / L)) z := by
    have h := congrFun (congrFun (Work.Coercivity.CommutZ.DzIter_mulZ c
      (fun x : ℝ => (1 : ℝ) - Work.Stability.chi (x / L))) z) θ
    have hfun : Work.Coercivity.CommutZ.mulZ (fun x : ℝ => (1 : ℝ) - Work.Stability.chi (x / L))
        = (fun z _ => (1 : ℝ) - Work.Stability.chi (z / L)) := rfl
    rw [hfun] at h
    simpa only [Work.Coercivity.CommutZ.mulZ_apply] using h
  rw [h1]
  -- 2. the Stirling expansion
  have h2 : Work.Coercivity.CommutZ.DzIterZ c
        (fun x : ℝ => (1 : ℝ) - Work.Stability.chi (x / L)) z
      = ∑ k ∈ Finset.range (c + 1), (Work.Spaces.scoef c k : ℝ) *
          (z ^ k * iteratedDeriv k (fun x : ℝ => (1 : ℝ) - Work.Stability.chi (x / L)) z) := by
    simpa only [] using congrFun (DzIterZ_eq_sum_scoef
      (fun x : ℝ => (1 : ℝ) - Work.Stability.chi (x / L)) hsmL c) z
  rw [h2]
  -- 3. each summand is bounded by `M`
  have hb : ∀ k ≤ c, |z ^ k * iteratedDeriv k
      (fun x : ℝ => (1 : ℝ) - Work.Stability.chi (x / L)) z| ≤ M := by
    intro k hk
    have hk4 : k ≤ 4 := le_trans hk hc
    have hrew : iteratedDeriv k (fun x : ℝ => (1 : ℝ) - Work.Stability.chi (x / L)) z
        = (L⁻¹) ^ k * iteratedDeriv k (fun x : ℝ => (1 : ℝ) - Work.Stability.chi x) (z / L) :=
      IteratedDeriv_comp_div (fun x : ℝ => (1 : ℝ) - Work.Stability.chi x) hsmg hLne k z
    have hzL : z ^ k * ((L⁻¹) ^ k *
          iteratedDeriv k (fun x : ℝ => (1 : ℝ) - Work.Stability.chi x) (z / L))
        = (z / L) ^ k * iteratedDeriv k (fun x : ℝ => (1 : ℝ) - Work.Stability.chi x) (z / L) := by
      have hdiv : z / L = z * L⁻¹ := by rw [div_eq_mul_inv]
      rw [hdiv, mul_pow]
      ring
    rw [hrew, hzL]
    exact hMb k hk4 (z / L)
  have hsum := Work.Spaces.abs_sum_scoef_mul_le c M
    (fun k => z ^ k * iteratedDeriv k (fun x : ℝ => (1 : ℝ) - Work.Stability.chi (x / L)) z) hb
  have hbell : (Work.Spaces.bell c : ℝ) ≤ 100 := by
    exact_mod_cast Work.Spaces.bell_le c hc
  calc |∑ k ∈ Finset.range (c + 1), (Work.Spaces.scoef c k : ℝ) *
        (z ^ k * iteratedDeriv k (fun x : ℝ => (1 : ℝ) - Work.Stability.chi (x / L)) z)|
      ≤ (Work.Spaces.bell c : ℝ) * M := hsum
    _ ≤ 100 * M := mul_le_mul_of_nonneg_right hbell hM0

/-! ## 5. The weighted derivatives of the profile -/

/-- `|D_z^a F_* · w| ≤ 4αΓ/z` for `z ≥ 1`, `a ≤ 4`: `D_z^a F_* = (α/c)Γ·Φ_a` and
`|w·Φ_a| ≤ 2/z` (`Phi_w_le`), while `(α/c)·2 ≤ 4α` because `1/c ≤ 5/3 ≤ 2` (`c ≥ 3/5`). -/
theorem DzIter_Fstar_w_le (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) {a : ℕ} (ha : a ≤ 4)
    {z : ℝ} (hz1 : 1 ≤ z) {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) :
    |Work.Spaces.DzIter a (Work.Construction.Fstar α) z θ * Work.Spaces.w z|
      ≤ 4 * α * Work.Spaces.Gam α θ / z := by
  have hc : (3 : ℝ) / 5 ≤ Work.Spaces.c α := c_ge_three_fifths α hα hα1
  have hcpos : 0 < Work.Spaces.c α := lt_of_lt_of_le (by norm_num) hc
  have hG0 : 0 ≤ Work.Spaces.Gam α θ := (Work.Spaces.Gam_bounds α θ hα hθ).1
  have hz : 0 < z := by linarith
  have hPhi : |Work.Spaces.w z * Phi a z θ| ≤ 2 / z := Phi_w_le a ha hz1 θ
  have heq : Work.Spaces.DzIter a (Work.Construction.Fstar α) z θ
      = (α / Work.Spaces.c α) * Work.Spaces.Gam α θ * Phi a z θ := by
    rw [congrFun (congrFun (DzIter_Fstar_eq α a) z) θ, PhiZ_eq a ha z θ]
  rw [heq]
  have hsplit : (α / Work.Spaces.c α) * Work.Spaces.Gam α θ * Phi a z θ * Work.Spaces.w z
      = ((α / Work.Spaces.c α) * Work.Spaces.Gam α θ)
          * (Work.Spaces.w z * Phi a z θ) := by ring
  rw [hsplit, abs_mul]
  have hA : |(α / Work.Spaces.c α) * Work.Spaces.Gam α θ|
      = (α / Work.Spaces.c α) * Work.Spaces.Gam α θ :=
    abs_of_nonneg (by positivity)
  rw [hA]
  have hmu : (α / Work.Spaces.c α) * Work.Spaces.Gam α θ * (2 / z)
      ≤ 4 * α * Work.Spaces.Gam α θ / z := by
    have hcinv : (Work.Spaces.c α)⁻¹ ≤ 2 := by
      have h2 : (2 : ℝ)⁻¹ ≤ Work.Spaces.c α := by
        rw [show (2 : ℝ)⁻¹ = 1 / 2 by norm_num]
        linarith
      exact (inv_le_comm₀ hcpos (by norm_num : (0 : ℝ) < 2)).mpr h2
    have hfact : (α / Work.Spaces.c α) * Work.Spaces.Gam α θ * (2 / z)
        = (α * Work.Spaces.Gam α θ / z) * (2 * (Work.Spaces.c α)⁻¹) := by ring
    have hfact2 : 4 * α * Work.Spaces.Gam α θ / z
        = (α * Work.Spaces.Gam α θ / z) * 4 := by ring
    rw [hfact, hfact2]
    exact mul_le_mul_of_nonneg_left (by linarith [hcinv]) (by positivity)
  calc (α / Work.Spaces.c α) * Work.Spaces.Gam α θ * |Work.Spaces.w z * Phi a z θ|
      ≤ (α / Work.Spaces.c α) * Work.Spaces.Gam α θ * (2 / z) :=
        mul_le_mul_of_nonneg_left hPhi (by positivity)
    _ ≤ 4 * α * Work.Spaces.Gam α θ / z := hmu

/-- `|D_z^j D_θ^i F_* · w| ≤ 4·10⁵·αΓ/z` for `z ≥ 1`, `i, j ≤ 4`, from
`mixed_Fstar_eq` (`mixed = (α/c)·D_θ^iΓ(0,θ)·Φ_j`), `|D_θ^iΓ| ≤ 10⁵Γ` (`DthIter_Gam_abs_le`)
and `|w·Φ_j| ≤ 2/z`. -/
theorem mixed_Fstar_w_le (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) {a i : ℕ} (ha : a ≤ 4) (hi : i ≤ 4)
    {z : ℝ} (hz1 : 1 ≤ z) {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) :
    |Work.Spaces.mixed a i (Work.Construction.Fstar α) z θ * Work.Spaces.w z|
      ≤ 400000 * α * Work.Spaces.Gam α θ / z := by
  have hc : (3 : ℝ) / 5 ≤ Work.Spaces.c α := c_ge_three_fifths α hα hα1
  have hcpos : 0 < Work.Spaces.c α := lt_of_lt_of_le (by norm_num) hc
  have hG0 : 0 ≤ Work.Spaces.Gam α θ := (Work.Spaces.Gam_bounds α θ hα hθ).1
  have hz : 0 < z := by linarith
  have hPhi : |Work.Spaces.w z * Phi a z θ| ≤ 2 / z := Phi_w_le a ha hz1 θ
  have hGam : |Work.Spaces.DthIter i (fun _ θ' => Work.Spaces.Gam α θ') 0 θ|
      ≤ 100000 * Work.Spaces.Gam α θ := DthIter_Gam_abs_le i hi α hα hα1 hθ
  have heq : Work.Spaces.mixed a i (Work.Construction.Fstar α) z θ
      = (α / Work.Spaces.c α)
          * Work.Spaces.DthIter i (fun _ θ' => Work.Spaces.Gam α θ') 0 θ * Phi a z θ := by
    rw [congrFun (congrFun (mixed_Fstar_eq α i a) z) θ, PhiZ_eq a ha z θ]
  rw [heq]
  have hsplit : (α / Work.Spaces.c α)
        * Work.Spaces.DthIter i (fun _ θ' => Work.Spaces.Gam α θ') 0 θ * Phi a z θ
        * Work.Spaces.w z
      = ((α / Work.Spaces.c α)
          * Work.Spaces.DthIter i (fun _ θ' => Work.Spaces.Gam α θ') 0 θ)
        * (Work.Spaces.w z * Phi a z θ) := by ring
  rw [hsplit, abs_mul]
  have hA : |(α / Work.Spaces.c α)
        * Work.Spaces.DthIter i (fun _ θ' => Work.Spaces.Gam α θ') 0 θ|
      ≤ (α / Work.Spaces.c α) * (100000 * Work.Spaces.Gam α θ) := by
    rw [abs_mul, abs_of_nonneg (by positivity)]
    exact mul_le_mul_of_nonneg_left hGam (by positivity)
  refine le_trans (mul_le_mul hA hPhi (abs_nonneg _) (by positivity)) ?_
  have hcinv : (Work.Spaces.c α)⁻¹ ≤ 2 := by
    have h2 : (2 : ℝ)⁻¹ ≤ Work.Spaces.c α := by
      rw [show (2 : ℝ)⁻¹ = 1 / 2 by norm_num]
      linarith
    exact (inv_le_comm₀ hcpos (by norm_num : (0 : ℝ) < 2)).mpr h2
  have hfact : (α / Work.Spaces.c α) * (100000 * Work.Spaces.Gam α θ) * (2 / z)
      = (α * Work.Spaces.Gam α θ / z) * (200000 * (Work.Spaces.c α)⁻¹) := by ring
  have hfact2 : 400000 * α * Work.Spaces.Gam α θ / z
      = (α * Work.Spaces.Gam α θ / z) * 400000 := by ring
  rw [hfact, hfact2]
  exact mul_le_mul_of_nonneg_left (by linarith [hcinv]) (by positivity)

/-! ## 6. Functions vanishing on a neighbourhood have vanishing `D`-derivatives

Below the cut-off (`z < L`) the far part `zfar L F_*` vanishes identically on a whole
neighbourhood of `z`, so every `D`-derivative of it vanishes at `z` as well — this is what
rescues the estimates there, where the radial weight `w(z) = (1+z)²/z²` blows up. -/

/-- `D_θ^i` of a function vanishing on a neighbourhood of `z` (in the `z`-variable, uniformly
in `θ`) vanishes there too. -/
theorem eventDthIter_zero {f : ℝ → ℝ → ℝ} {z : ℝ}
    (h : ∀ᶠ z' in 𝓝 z, ∀ θ' : ℝ, f z' θ' = 0) (i : ℕ) :
    ∀ᶠ z' in 𝓝 z, ∀ θ' : ℝ, Work.Spaces.DthIter i f z' θ' = 0 := by
  induction i with
  | zero => exact h
  | succ i ih =>
      rcases mem_nhds_iff.mp ih with ⟨U, hU, hUopen, hzU⟩
      filter_upwards [hUopen.mem_nhds hzU] with z' hz'
      intro θ'
      have hfun : (fun t : ℝ => Work.Spaces.DthIter i f z' t) = fun _ : ℝ => (0 : ℝ) :=
        funext (fun t => hU hz' t)
      simp only [Work.Spaces.DthIter_succ, Work.Spaces.Dth, Work.Spaces.pth]
      rw [hfun, deriv_const, mul_zero]

/-- `D_z^i` of a function vanishing on a neighbourhood of `z` (uniformly in `θ`) vanishes
there too. -/
theorem eventDzIter_zero {f : ℝ → ℝ → ℝ} {z : ℝ}
    (h : ∀ᶠ z' in 𝓝 z, ∀ θ' : ℝ, f z' θ' = 0) (i : ℕ) :
    ∀ᶠ z' in 𝓝 z, ∀ θ' : ℝ, Work.Spaces.DzIter i f z' θ' = 0 := by
  induction i with
  | zero => exact h
  | succ i ih =>
      rcases mem_nhds_iff.mp ih with ⟨U, hU, hUopen, hzU⟩
      filter_upwards [hUopen.mem_nhds hzU] with z' hz'
      intro θ'
      have hev : (fun w : ℝ => Work.Spaces.DzIter i f w θ') =ᶠ[𝓝 z'] fun _ : ℝ => (0 : ℝ) :=
        Filter.eventually_of_mem (hUopen.mem_nhds hz') (fun w hw => hU hw θ')
      simp only [Work.Spaces.DzIter_succ, Work.Spaces.Dz, Work.Spaces.pz]
      rw [hev.deriv_eq, deriv_const, mul_zero]

/-- Every `D_z`-iterate of such a function vanishes at `z`. -/
theorem DzIter_eq_zero_of_eventually_zero {f : ℝ → ℝ → ℝ} {z θ : ℝ}
    (h : ∀ᶠ z' in 𝓝 z, ∀ θ' : ℝ, f z' θ' = 0) (i : ℕ) :
    Work.Spaces.DzIter i f z θ = 0 :=
  Filter.EventuallyEq.eq_of_nhds ((eventDzIter_zero h i).mono (fun z' hz' => hz' θ))

/-- Every mixed `D`-iterate of such a function vanishes at `z`. -/
theorem mixed_eq_zero_of_eventually_zero {f : ℝ → ℝ → ℝ} {z θ : ℝ}
    (h : ∀ᶠ z' in 𝓝 z, ∀ θ' : ℝ, f z' θ' = 0) (j i : ℕ) :
    Work.Spaces.mixed j i f z θ = 0 :=
  DzIter_eq_zero_of_eventually_zero (eventDthIter_zero h i) j

/-- The whole `ℋ^k`-integrand of such a function vanishes at `z`. -/
theorem HkIntegrand_eq_zero_of_eventually_zero {α : ℝ} {k : ℕ} {f : ℝ → ℝ → ℝ} {z θ : ℝ}
    (h : ∀ᶠ z' in 𝓝 z, ∀ θ' : ℝ, f z' θ' = 0) :
    Work.Spaces.HkIntegrand α k f z θ = 0 := by
  have hD : ∀ i : ℕ, Work.Spaces.DzIter i f z θ = 0 :=
    fun i => DzIter_eq_zero_of_eventually_zero h i
  have hM : ∀ j i : ℕ, Work.Spaces.mixed j i f z θ = 0 :=
    fun j i => mixed_eq_zero_of_eventually_zero h j i
  rw [Work.Spaces.HkIntegrand]
  have h1 : (∑ i ∈ Finset.range (k + 1),
      (Work.Spaces.DzIter i f z θ
        * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2) = 0 := by
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [hD i]
    ring
  have h2 : (∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1),
      if 1 ≤ i ∧ i + j ≤ k then (Work.Spaces.mixed j i f z θ * Work.Spaces.Wt α z θ) ^ 2
      else 0) = 0 := by
    refine Finset.sum_eq_zero fun i _ => ?_
    refine Finset.sum_eq_zero fun j _ => ?_
    by_cases hc : 1 ≤ i ∧ i + j ≤ k
    · rw [if_pos hc, hM j i]
      ring
    · rw [if_neg hc]
  rw [h1, h2, add_zero]

/-- The far part `zfar L F_*` vanishes identically on a neighbourhood of `z` whenever
`z < L` (`χ(z'/L) = 1` for `|z'| < L`). -/
theorem zfar_eventually_zero {α L z : ℝ} (hL : 0 < L) (hz0 : 0 ≤ z) (hz : z < L) :
    ∀ᶠ z' in 𝓝 z, ∀ θ' : ℝ,
      Work.Stability.zfar L (Work.Construction.Fstar α) z' θ' = 0 := by
  have hzabs : |z| < L := by rw [abs_of_nonneg hz0]; exact hz
  filter_upwards [(isOpen_lt continuous_abs continuous_const).mem_nhds hzabs] with z' hz'
  intro θ'
  have h1 : |z' / L| ≤ 1 := by
    rw [abs_div, abs_of_pos hL, div_le_one hL]
    exact le_of_lt hz'
  rw [Work.Stability.zfar_apply, Work.Stability.chi_eq_one h1]
  ring

end ZFBase
end Work.FTS.LocData
