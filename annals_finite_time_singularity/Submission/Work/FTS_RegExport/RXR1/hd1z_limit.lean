import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.FTS.FinalV2.Defs
import Submission.Work.FTS.RegPkgGal.R5Parts
import Submission.Work.FTS.RegExportIface.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.FTS_RegExport.RXR1.hd1z_limit`

The R1 field `hd1z` for the sanitised right-Taylor family `gS α (tauExt g)`: for every
`θ ∈ Iθ` the `z`-derivative of the `τ`-derivative at `τ = 0` of the `θ`-slice tends to `0`
along `z → 0⁺`.

The proof is a difference-quotient argument.  The hypothesis `hw` supplies the uniform-in-`τ`
estimate

`|D_z (g(τ) - g(τ'))| ≤ C z^{3/2}/(1+z)^2 |τ - τ'|`  (`a + b ≤ 1`, in particular `a = 0, b = 1`),

so the family of difference quotients `Φ_τ = (g(τ) - g(0))/τ` has, on `(0,∞)`, a
`z`-derivative bounded by `C √z`; the pointwise limit of `Φ_τ` as `τ → 0⁺` is the
`τ`-derivative at `0` (`H5.h0` is a two-sided `τ`-derivative at `0`), and a pointwise limit of
differentiable functions whose derivatives are bounded by a monotone continuous `φ` satisfies
`|G'| ≤ φ`.  Passing to the limit at `z → 0⁺` gives the claim.  On the two boundary angles
`θ = 0, π/2` the family vanishes identically (it is `0` there by `RegPkgMin.vanish`).
-/

namespace Work.FTS_RegExport.RXR1

open Filter Set
open scoped Topology

/-! ## Auxiliary real-analysis lemmas -/

/-- **Uniformly bounded derivatives pass to a pointwise limit.**  If `F i` is differentiable on
`(0,∞)` with `|deriv (F i) x| ≤ φ x`, where `φ` is continuous, nonnegative and monotone, and
`F i x → G x` along the filter `l`, then `|deriv G x| ≤ φ x` for `x > 0`.

(`deriv G x` is `0` at a point where `G` is not differentiable, so that case is trivial.) -/
theorem deriv_bound_of_pointwise_tendsto {ι : Type*} {l : Filter ι} [Filter.NeBot l]
    {F : ι → ℝ → ℝ} {G φ : ℝ → ℝ}
    (hF : ∀ i, ∀ x ∈ Set.Ioi (0 : ℝ), DifferentiableAt ℝ (F i) x)
    (hφc : ContinuousOn φ (Set.Ioi 0))
    (hφ0 : ∀ x ∈ Set.Ioi 0, 0 ≤ φ x)
    (hφm : ∀ x ∈ Set.Ioi 0, ∀ y ∈ Set.Ioi 0, x ≤ y → φ x ≤ φ y)
    (hd : ∀ i, ∀ x ∈ Set.Ioi 0, |deriv (F i) x| ≤ φ x)
    (hpt : ∀ x ∈ Set.Ioi 0, Filter.Tendsto (fun i => F i x) l (nhds (G x))) :
    ∀ x ∈ Set.Ioi 0, |deriv G x| ≤ φ x := by
  have key_le : ∀ x ∈ Set.Ioi (0 : ℝ), ∀ y ∈ Set.Ioi (0 : ℝ), x ≤ y →
      |G y - G x| ≤ φ y * |y - x| := by
    intro x hx y hy hxy
    have hbdd : ∀ᶠ i in l, |F i y - F i x| ≤ φ y * |y - x| := by
      refine Filter.Eventually.of_forall (fun i => ?_)
      have hmvt := Convex.norm_image_sub_le_of_norm_deriv_le (f := F i) (s := Set.Icc x y)
        (x := x) (y := y) (C := φ y)
        (fun t ht => hF i t (lt_of_lt_of_le hx ht.1))
        (fun t ht => by
          rw [Real.norm_eq_abs]
          exact le_trans (hd i t (lt_of_lt_of_le hx ht.1))
            (hφm t (lt_of_lt_of_le hx ht.1) y hy ht.2))
        (convex_Icc x y) ⟨le_rfl, hxy⟩ ⟨hxy, le_rfl⟩
      simpa only [Real.norm_eq_abs] using hmvt
    have hlim : Filter.Tendsto (fun i => |F i y - F i x|) l (nhds |G y - G x|) :=
      ((hpt y hy).sub (hpt x hx)).abs
    exact le_of_tendsto_of_tendsto hlim tendsto_const_nhds hbdd
  have key : ∀ x ∈ Set.Ioi (0 : ℝ), ∀ y ∈ Set.Ioi (0 : ℝ),
      |G y - G x| ≤ φ (max x y) * |y - x| := by
    intro x hx y hy
    rcases le_total x y with hxy | hyx
    · simpa only [max_eq_right hxy] using key_le x hx y hy hxy
    · have h1 := key_le y hy x hx hyx
      rw [max_eq_left hyx]
      rwa [abs_sub_comm (G x) (G y), abs_sub_comm x y] at h1
  intro x hx
  have hx' : (0 : ℝ) < x := hx
  by_cases hD : DifferentiableAt ℝ G x
  · have hslope : Filter.Tendsto (fun t : ℝ => t⁻¹ • (G (x + t) - G x))
        (nhdsWithin (0 : ℝ) {0}ᶜ) (nhds (deriv G x)) := hD.hasDerivAt.tendsto_slope_zero
    have hslope' : Filter.Tendsto (fun t : ℝ => t⁻¹ * (G (x + t) - G x))
        (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds (deriv G x)) := by
      have h1 := hslope.mono_left
        (nhdsWithin_mono 0 (fun t (ht : t ∈ Set.Ioi (0 : ℝ)) => ne_of_gt ht))
      simpa only [smul_eq_mul] using h1
    have hbnd : ∀ᶠ t in nhdsWithin (0 : ℝ) (Set.Ioi 0),
        |t⁻¹ * (G (x + t) - G x)| ≤ φ (x + t) := by
      filter_upwards [self_mem_nhdsWithin] with t ht
      have ht0 : (0 : ℝ) < t := ht
      have hxt : (0 : ℝ) < x + t := by linarith
      have h1 : |G (x + t) - G x| ≤ φ (x + t) * t := by
        have h2 := key x hx (x + t) hxt
        rw [max_eq_right (by linarith : x ≤ x + t)] at h2
        rwa [add_sub_cancel_left, abs_of_pos ht0] at h2
      have htne : t ≠ 0 := ne_of_gt ht0
      calc |t⁻¹ * (G (x + t) - G x)| = t⁻¹ * |G (x + t) - G x| := by
            rw [abs_mul, abs_inv, abs_of_pos ht0]
        _ ≤ t⁻¹ * (φ (x + t) * t) :=
            mul_le_mul_of_nonneg_left h1 (inv_nonneg.mpr ht0.le)
        _ = φ (x + t) := by field_simp
    have hlimφ : Filter.Tendsto (fun t : ℝ => φ (x + t)) (nhdsWithin (0 : ℝ) (Set.Ioi 0))
        (nhds (φ x)) := by
      have hcont : ContinuousAt φ x := hφc.continuousAt (isOpen_Ioi.mem_nhds hx)
      have hadd : ContinuousAt (fun t : ℝ => x + t) 0 :=
        continuousAt_const.add continuousAt_id
      have h1 : Filter.Tendsto (fun t : ℝ => x + t) (nhdsWithin (0 : ℝ) (Set.Ioi 0))
          (nhds x) := by
        simpa using hadd.tendsto.mono_left nhdsWithin_le_nhds
      simpa only [Function.comp_def] using hcont.tendsto.comp h1
    exact le_of_tendsto_of_tendsto hslope'.abs hlimφ hbnd
  · rw [deriv_zero_of_not_differentiableAt hD]
    simpa using hφ0 x hx

/-- **A `√z` bound on the derivative gives the limit `0` at `0⁺`.** -/
theorem tendsto_deriv_of_abs_le_sqrt {G : ℝ → ℝ} {C : ℝ} (hC : 0 ≤ C)
    (h : ∀ z ∈ Set.Ioi (0 : ℝ), |deriv G z| ≤ C * Real.sqrt z) :
    Filter.Tendsto (fun p : ℝ × ℝ => deriv G p.1)
      (nhdsWithin (0, 0) (Set.prod (Set.Ioi (0 : ℝ)) Set.univ)) (nhds 0) := by
  have hbdd : ∀ᶠ p : ℝ × ℝ in nhdsWithin (0, 0) (Set.prod (Set.Ioi (0 : ℝ)) Set.univ),
      |deriv G p.1| ≤ C * Real.sqrt p.1 := by
    filter_upwards [self_mem_nhdsWithin] with p hp
    exact h p.1 hp.1
  have hlim : Filter.Tendsto (fun p : ℝ × ℝ => C * Real.sqrt p.1)
      (nhdsWithin (0, 0) (Set.prod (Set.Ioi (0 : ℝ)) Set.univ)) (nhds 0) := by
    have h1 : Filter.Tendsto (fun p : ℝ × ℝ => p.1)
        (nhdsWithin (0, 0) (Set.prod (Set.Ioi (0 : ℝ)) Set.univ)) (nhds (0 : ℝ)) :=
      (continuous_fst.tendsto (0, 0)).mono_left nhdsWithin_le_nhds
    have h2 : Filter.Tendsto (fun p : ℝ × ℝ => Real.sqrt p.1)
        (nhdsWithin (0, 0) (Set.prod (Set.Ioi (0 : ℝ)) Set.univ)) (nhds 0) := by
      simpa only [Function.comp_def, Real.sqrt_zero] using
        (Real.continuous_sqrt.tendsto (0 : ℝ)).comp h1
    simpa using h2.const_mul C
  rw [tendsto_zero_iff_norm_tendsto_zero]
  simpa only [Real.norm_eq_abs] using
    squeeze_zero' (Filter.Eventually.of_forall (fun p => abs_nonneg _)) hbdd hlim

/-! ## Slice differentiability and the boundary-angle degenerate case -/

/-- The `z`-slices of the family are differentiable at every interior point of the quadrant,
from the `C⁴`-regularity hypothesis `RegPkgMin.c4`. -/
private lemma slice_differentiableAt {g : Work.FTS.Galerkin.Fam}
    (hc4 : ∀ τ, 0 ≤ τ → ContDiffOn ℝ 4 (Function.uncurry (Work.FTS.Galerkin.slice g τ))
      Work.FTS.EllipticEst.Q0)
    {τ x θ : ℝ} (hτ : 0 ≤ τ) (hx : 0 < x) (hθ0 : 0 < θ) (hθ1 : θ < Real.pi / 2) :
    DifferentiableAt ℝ (fun z => g z θ τ) x := by
  have hmem : (x, θ) ∈ Work.FTS.EllipticEst.Q0 := ⟨hx, hθ0, hθ1⟩
  have hopen : Work.FTS.EllipticEst.Q0 ∈ 𝓝 (x, θ) :=
    (isOpen_Ioi.prod isOpen_Ioo).mem_nhds hmem
  have hca : ContDiffAt ℝ 4 (Function.uncurry (Work.FTS.Galerkin.slice g τ)) (x, θ) :=
    (hc4 τ hτ).contDiffAt hopen
  have hpd : DifferentiableAt ℝ (Function.uncurry (Work.FTS.Galerkin.slice g τ)) (x, θ) :=
    hca.differentiableAt (by norm_num)
  have hf : DifferentiableAt ℝ (fun z : ℝ => (z, θ)) x :=
    differentiableAt_id.prodMk (differentiableAt_const θ)
  have hcomp := hpd.comp x hf
  simpa only [Function.comp_def, Function.uncurry_apply_pair, Work.FTS.Galerkin.slice_apply]
    using hcomp

/-- On the two boundary angles `θ = 0, π/2` the sanitised family vanishes identically in
`(z, τ)` (the boundary values of `g` vanish by `RegPkgMin.vanish`, and the right-Taylor
extension reproduces them). -/
private lemma gS_tauExt_eq_zero_of_boundary {α : ℝ} {g : Work.FTS.Galerkin.Fam}
    (hvan : ∀ τ : ℝ, 0 ≤ τ → ∀ z : ℝ, 0 ≤ z →
      g z 0 τ = 0 ∧ g z (Real.pi / 2) τ = 0)
    {θ : ℝ} (hθ : θ = 0 ∨ θ = Real.pi / 2) :
    ∀ z s : ℝ, Work.FTS.FinalV2.gS α (Work.FTS.FinalV2.tauExt g) z θ s = 0 := by
  intro z s
  rcases hθ with rfl | rfl
  · by_cases hz : 0 < z
    · have hb : (0 : ℝ) ≤ 0 ∧ (0 : ℝ) ≤ Real.pi / 2 := ⟨le_rfl, by positivity⟩
      simp only [Work.FTS.FinalV2.gS, ite_eq_left hz, ite_eq_left hb, Work.FTS.FinalV2.tauExt]
      by_cases hs : s < 0
      · rw [ite_eq_left hs]
        have hv : g z 0 0 = 0 := (hvan 0 le_rfl z hz.le).1
        have h0mem : (0 : ℝ) ∈ Set.Ici 0 := by simp
        have hd : derivWithin (fun t => g z 0 t) (Set.Ici 0) 0 = 0 := by
          have he : Set.EqOn (fun t => g z 0 t) (fun _ : ℝ => (0 : ℝ)) (Set.Ici 0) :=
            fun t ht => (hvan t ht z hz.le).1
          rw [derivWithin_congr he (he h0mem)]
          simp
        rw [hv, hd]
        ring
      · rw [ite_eq_right hs]
        exact (hvan s (not_lt.mp hs) z hz.le).1
    · simp only [Work.FTS.FinalV2.gS, ite_eq_right hz]
  · by_cases hz : 0 < z
    · have hb : (0 : ℝ) ≤ Real.pi / 2 ∧ Real.pi / 2 ≤ Real.pi / 2 := ⟨by positivity, le_rfl⟩
      simp only [Work.FTS.FinalV2.gS, ite_eq_left hz, ite_eq_left hb, Work.FTS.FinalV2.tauExt]
      by_cases hs : s < 0
      · rw [ite_eq_left hs]
        have hv : g z (Real.pi / 2) 0 = 0 := (hvan 0 le_rfl z hz.le).2
        have h0mem : (0 : ℝ) ∈ Set.Ici 0 := by simp
        have hd : derivWithin (fun t => g z (Real.pi / 2) t) (Set.Ici 0) 0 = 0 := by
          have he : Set.EqOn (fun t => g z (Real.pi / 2) t) (fun _ : ℝ => (0 : ℝ)) (Set.Ici 0) :=
            fun t ht => (hvan t ht z hz.le).2
          rw [derivWithin_congr he (he h0mem)]
          simp
        rw [hv, hd]
        ring
      · rw [ite_eq_right hs]
        exact (hvan s (not_lt.mp hs) z hz.le).2
    · simp only [Work.FTS.FinalV2.gS, ite_eq_right hz]

/-- If the `θ`-slice vanishes identically then the target function vanishes identically. -/
private lemma tendsto_deriv_of_slice_eq_zero {h : Work.FTS.Galerkin.Fam} {θ : ℝ}
    (hz : ∀ z s : ℝ, h z θ s = 0) :
    Filter.Tendsto (fun p : ℝ × ℝ => deriv (fun z => deriv (fun s => h z θ s) 0) p.1)
      (nhdsWithin (0, 0) (Set.prod (Set.Ioi (0 : ℝ)) Set.univ)) (nhds 0) := by
  have hG : (fun z : ℝ => deriv (fun s => h z θ s) 0) = fun _ => (0 : ℝ) := by
    funext z
    have h1 : (fun s => h z θ s) = fun _ => (0 : ℝ) := funext (fun s => hz z s)
    rw [h1]
    exact deriv_const 0 0
  have hfinal : (fun p : ℝ × ℝ => deriv (fun z => deriv (fun s => h z θ s) 0) p.1)
      = fun _ => (0 : ℝ) := by
    rw [hG]
    funext p
    exact deriv_const p.1 0
  rw [hfinal]
  exact tendsto_const_nhds

/-- `z^{3/2} = √z · z`. -/
private lemma rpow_three_halves (x : ℝ) (hx : 0 < x) :
    x ^ ((3 : ℝ) / 2) = Real.sqrt x * x := by
  rw [show (3 : ℝ) / 2 = 1 / 2 + 1 by norm_num, Real.rpow_add hx, Real.rpow_one,
    ← Real.sqrt_eq_rpow]

/-! ## The interior estimate -/

/-- **The interior case**: for `0 < θ < π/2`, the difference-quotient argument described in the
module docstring.  `hgh` records that the sanitised family agrees with `g` on the closed quadrant
at nonnegative times, `hc4` the `C⁴`-regularity of the slices, `hdiff` the two-sided `τ`
differentiability at `τ = 0`, and `hwC` the `hw` estimate. -/
private lemma interior_case {h g : Work.FTS.Galerkin.Fam} {C : ℝ} (hC : 0 ≤ C)
    (hgh : ∀ z θ τ : ℝ, 0 < z → 0 ≤ θ → θ ≤ Real.pi / 2 → 0 ≤ τ → h z θ τ = g z θ τ)
    (hc4 : ∀ τ, 0 ≤ τ → ContDiffOn ℝ 4 (Function.uncurry (Work.FTS.Galerkin.slice g τ))
      Work.FTS.EllipticEst.Q0)
    (hdiff : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      DifferentiableAt ℝ (fun s => h z θ s) 0)
    (hwC : ∀ τ ∈ Set.Icc (0 : ℝ) 1, ∀ τ' ∈ Set.Icc (0 : ℝ) 1, ∀ b a : ℕ, a + b ≤ 1 →
      ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
        |Work.Spaces.mixed b a (Work.FTS.Galerkin.slice g τ - Work.FTS.Galerkin.slice g τ') z θ| ≤
          C * (z ^ ((3 : ℝ) / 2) / (1 + z) ^ 2) * |τ - τ'|)
    {θ : ℝ} (hθ0 : 0 < θ) (hθ1 : θ < Real.pi / 2) :
    Filter.Tendsto (fun p : ℝ × ℝ => deriv (fun z => deriv (fun s => h z θ s) 0) p.1)
      (nhdsWithin (0, 0) (Set.prod (Set.Ioi (0 : ℝ)) Set.univ)) (nhds 0) := by
  set F : ℝ → ℝ → ℝ :=
    (fun i z => if 0 < i ∧ i ≤ 1 then (h z θ i - h z θ 0) / i else 0) with hF
  -- the slices of `g` are differentiable in `z` at interior points of the quadrant
  have hslicei : ∀ i : ℝ, 0 < i → ∀ x ∈ Set.Ioi (0 : ℝ),
      DifferentiableAt ℝ (fun z => g z θ i) x :=
    fun i hi x hx => slice_differentiableAt hc4 hi.le hx hθ0 hθ1
  have hslice0 : ∀ x ∈ Set.Ioi (0 : ℝ), DifferentiableAt ℝ (fun z => g z θ 0) x :=
    fun x hx => slice_differentiableAt hc4 le_rfl hx hθ0 hθ1
  -- (1) the difference quotients are differentiable on `(0,∞)`
  have hFdiff : ∀ i, ∀ x ∈ Set.Ioi (0 : ℝ), DifferentiableAt ℝ (F i) x := by
    intro i x hx
    by_cases hi : 0 < i ∧ i ≤ 1
    · have hFi : F i = fun z => (h z θ i - h z θ 0) / i := by
        funext z; rw [hF]; exact ite_eq_left hi
      rw [hFi]
      have h1 : DifferentiableAt ℝ (fun z => h z θ i) x := by
        refine (hslicei i hi.1 x hx).congr_of_eventuallyEq ?_
        filter_upwards [isOpen_Ioi.mem_nhds hx] with z hz
        exact hgh z θ i hz hθ0.le hθ1.le hi.1.le
      have h2 : DifferentiableAt ℝ (fun z => h z θ 0) x := by
        refine (hslice0 x hx).congr_of_eventuallyEq ?_
        filter_upwards [isOpen_Ioi.mem_nhds hx] with z hz
        exact hgh z θ 0 hz hθ0.le hθ1.le le_rfl
      exact (h1.sub h2).div_const i
    · have hFi : F i = fun _ => (0 : ℝ) := by
        funext z; rw [hF]; exact ite_eq_right hi
      rw [hFi]
      exact differentiableAt_const 0
  -- (2) the derivative bound `|deriv (F i) x| ≤ C √x`
  have hFbnd : ∀ i, ∀ x ∈ Set.Ioi (0 : ℝ), |deriv (F i) x| ≤ C * Real.sqrt x := by
    intro i x hx
    by_cases hi : 0 < i ∧ i ≤ 1
    · have hFi : F i = fun z => (h z θ i - h z θ 0) / i := by
        funext z; rw [hF]; exact ite_eq_left hi
      have hx' : (0 : ℝ) < x := hx
      have h1 : DifferentiableAt ℝ (fun z => g z θ i) x := hslicei i hi.1 x hx
      have h2 : DifferentiableAt ℝ (fun z => g z θ 0) x := hslice0 x hx
      -- identify the derivative of the difference quotient
      have hev : (fun z => (h z θ i - h z θ 0) / i) =ᶠ[𝓝 x]
          fun z => (g z θ i - g z θ 0) / i := by
        filter_upwards [isOpen_Ioi.mem_nhds hx] with z hz
        rw [hgh z θ i hz hθ0.le hθ1.le hi.1.le, hgh z θ 0 hz hθ0.le hθ1.le le_rfl]
      have hsub : deriv (fun z => g z θ i - g z θ 0) x
          = deriv (fun z => g z θ i) x - deriv (fun z => g z θ 0) x := deriv_sub h1 h2
      have hderiv : deriv (F i) x
          = (deriv (fun z => g z θ i - g z θ 0) x) / i := by
        rw [hFi, hev.deriv_eq, deriv_div_const, hsub]
      -- the `hw` bound, in the form `|mixed ...| ≤ C (x^{3/2}/(1+x)^2) * i`
      have hb := hwC i ⟨hi.1.le, hi.2⟩ 0 ⟨le_rfl, zero_le_one⟩ 1 0 (by norm_num) x θ hx hθ0 hθ1
      rw [sub_zero, abs_of_pos hi.1] at hb
      -- identify `x * deriv (g i - g 0)` with `mixed 1 0 (slice g i - slice g 0)`
      have hmix : Work.Spaces.mixed 1 0
            (Work.FTS.Galerkin.slice g i - Work.FTS.Galerkin.slice g 0) x θ
          = x * deriv (fun z => g z θ i - g z θ 0) x := by
        simp only [Work.Spaces.mixed, Work.Spaces.DzIter_succ, Work.Spaces.DzIter_zero,
          Work.Spaces.DthIter_zero, Work.Spaces.Dz, Work.Spaces.pz, Pi.sub_apply,
          Work.FTS.Galerkin.slice_apply]
      have hxabs : |x| = x := abs_of_pos hx
      have hiabs : |i| = i := abs_of_pos hi.1
      have hxne : x ≠ 0 := ne_of_gt hx
      have hine : i ≠ 0 := ne_of_gt hi.1
      have hmain : |deriv (F i) x| = |x * deriv (fun z => g z θ i - g z θ 0) x| / (i * x) := by
        rw [hderiv, abs_div, abs_mul, hxabs, hiabs]
        field_simp
      rw [hmain, ← hmix]
      have hix : 0 < i * x := mul_pos hi.1 hx
      calc |Work.Spaces.mixed 1 0
              (Work.FTS.Galerkin.slice g i - Work.FTS.Galerkin.slice g 0) x θ| / (i * x)
          ≤ (C * (x ^ ((3 : ℝ) / 2) / (1 + x) ^ 2) * i) / (i * x) :=
            div_le_div_of_nonneg_right hb hix.le
        _ = C * (Real.sqrt x / (1 + x) ^ 2) := by
            have h1x : (1 + x) ≠ 0 := by positivity
            have h1x2 : (1 + x) ^ 2 ≠ 0 := pow_ne_zero 2 h1x
            rw [rpow_three_halves x hx]
            field_simp
        _ ≤ C * Real.sqrt x := by
            have hone : (1 : ℝ) ≤ (1 + x) ^ 2 := by nlinarith [sq_nonneg x, hx']
            have hnn : 0 ≤ C * Real.sqrt x := by positivity
            calc C * (Real.sqrt x / (1 + x) ^ 2)
                = C * Real.sqrt x / (1 + x) ^ 2 := by ring
              _ ≤ C * Real.sqrt x / 1 :=
                  div_le_div_of_nonneg_left hnn zero_lt_one hone
              _ = C * Real.sqrt x := by ring
    · have hFi : F i = fun _ => (0 : ℝ) := by
        funext z; rw [hF]; exact ite_eq_right hi
      rw [hFi, deriv_const, abs_zero]
      exact mul_nonneg hC (Real.sqrt_nonneg x)
  -- (3) pointwise convergence of the difference quotients to the `τ`-derivative at `0`
  have hpt : ∀ x ∈ Set.Ioi (0 : ℝ),
      Filter.Tendsto (fun i => F i x) (nhdsWithin (0 : ℝ) (Set.Ioi 0))
        (nhds (deriv (fun s => h x θ s) 0)) := by
    intro x hx
    have hslope : Filter.Tendsto (fun t : ℝ => t⁻¹ * (h x θ t - h x θ 0))
        (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds (deriv (fun s => h x θ s) 0)) := by
      have h1 : Filter.Tendsto
          (fun t : ℝ => t⁻¹ • ((fun s => h x θ s) (0 + t) - (fun s => h x θ s) 0))
          (nhdsWithin (0 : ℝ) {0}ᶜ) (nhds (deriv (fun s => h x θ s) 0)) :=
        (hdiff x θ hx hθ0 hθ1).hasDerivAt.tendsto_slope_zero
      have h2 := h1.mono_left
        (nhdsWithin_mono 0 (fun t (ht : t ∈ Set.Ioi (0 : ℝ)) => ne_of_gt ht))
      simpa only [zero_add, smul_eq_mul] using h2
    have hi1 : ∀ᶠ i in nhdsWithin (0 : ℝ) (Set.Ioi 0), i ≤ 1 := by
      have hmem : Set.Iio (1 : ℝ) ∈ 𝓝 (0 : ℝ) := isOpen_Iio.mem_nhds (by norm_num)
      filter_upwards [nhdsWithin_le_nhds hmem] with i hi using le_of_lt hi
    refine hslope.congr' ?_
    filter_upwards [self_mem_nhdsWithin, hi1] with i hi hi1'
    rw [hF]
    have hicond : 0 < i ∧ i ≤ 1 := ⟨hi, hi1'⟩
    simp only [ite_eq_left hicond, div_eq_inv_mul]
  -- (4) assemble
  have hbound : ∀ x ∈ Set.Ioi (0 : ℝ),
      |deriv (fun z => deriv (fun s => h z θ s) 0) x| ≤ C * Real.sqrt x :=
    deriv_bound_of_pointwise_tendsto (φ := fun x => C * Real.sqrt x)
      (G := fun z => deriv (fun s => h z θ s) 0) hFdiff
      (Real.continuous_sqrt.continuousOn.const_mul C)
      (fun x hx => mul_nonneg hC (Real.sqrt_nonneg x))
      (fun x hx y hy hxy => mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hxy) hC)
      hFbnd hpt
  exact tendsto_deriv_of_abs_le_sqrt hC hbound

/-! ## The target -/

theorem hd1z_limit {α C₀ : ℝ} {Φs : Work.FTS.Galerkin.Fn}
    {E : Work.FTS.Galerkin.Fn →ₗ[ℝ] Work.FTS.Galerkin.Fn} {g : Work.FTS.Galerkin.Fam}
    (hα : 0 < α) (hα13 : α ≤ 1 / 3)
    (hOK : Work.FTS.FinalV2.DynOK' (Work.FTS.Regularity.pExp α) C₀ Φs E g)
    (H5 : ∀ S > 0, Work.FTS.RegPkgGal.R5Parts α S
      (Work.FTS.FinalV2.gS α (Work.FTS.FinalV2.tauExt g))
      (Work.FTS.RegExportIface.psiR α Φs E (Work.FTS.FinalV2.tauExt g)))
    (hw : ∃ C : ℝ, 0 ≤ C ∧ ∀ τ ∈ Set.Icc (0:ℝ) 1, ∀ τ' ∈ Set.Icc (0:ℝ) 1,
      ∀ b a : ℕ, a + b ≤ 1 → ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
        |Work.Spaces.mixed b a (Work.FTS.Galerkin.slice g τ - Work.FTS.Galerkin.slice g τ') z θ| ≤
          C * (z ^ ((3 : ℝ) / 2) / (1 + z) ^ 2) * |τ - τ'|) :
    ∀ θ ∈ Work.Spaces.Iθ, Filter.Tendsto
      (fun p : ℝ × ℝ => deriv (fun z => deriv
        (fun s => Work.FTS.FinalV2.gS α (Work.FTS.FinalV2.tauExt g) z θ s) 0) p.1)
      (nhdsWithin (0, 0) (Set.prod (Set.Ioi (0:ℝ)) Set.univ)) (nhds 0) := by
  obtain ⟨C, hC, hwC⟩ := hw
  set h : Work.FTS.Galerkin.Fam := Work.FTS.FinalV2.gS α (Work.FTS.FinalV2.tauExt g) with hh
  have hc4 : ∀ τ, 0 ≤ τ → ContDiffOn ℝ 4 (Function.uncurry (Work.FTS.Galerkin.slice g τ))
      Work.FTS.EllipticEst.Q0 := fun τ hτ => hOK.1.1.c4 τ hτ
  have hvan : ∀ τ : ℝ, 0 ≤ τ → ∀ z : ℝ, 0 ≤ z →
      g z 0 τ = 0 ∧ g z (Real.pi / 2) τ = 0 := fun τ hτ z hz => hOK.1.1.vanish τ hτ z hz
  have hgh : ∀ z θ τ : ℝ, 0 < z → 0 ≤ θ → θ ≤ Real.pi / 2 → 0 ≤ τ → h z θ τ = g z θ τ := by
    intro z θ τ hz hθ0 hθ1 hτ
    have hb : (0 : ℝ) ≤ θ ∧ θ ≤ Real.pi / 2 := ⟨hθ0, hθ1⟩
    simp only [hh, Work.FTS.FinalV2.gS, ite_eq_left hz, ite_eq_left hb,
      Work.FTS.FinalV2.tauExt_of_nonneg g hτ]
  have hdiff : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      DifferentiableAt ℝ (fun s => h z θ s) 0 := by
    intro z θ hz hθ0 hθ1
    have hmem : (z, θ) ∈ Work.Construction.Qd := ⟨hz, hθ0, hθ1⟩
    exact ((H5 1 one_pos).h0 z θ hz hmem).differentiableAt
  intro θ hθ
  rcases eq_or_lt_of_le hθ.1 with h0 | h0
  · exact tendsto_deriv_of_slice_eq_zero
      (gS_tauExt_eq_zero_of_boundary hvan (Or.inl h0.symm))
  rcases eq_or_lt_of_le hθ.2 with hpi | hpi
  · exact tendsto_deriv_of_slice_eq_zero
      (gS_tauExt_eq_zero_of_boundary hvan (Or.inr hpi))
  · exact interior_case hC hgh hc4 hdiff hwC h0 hpi

end Work.FTS_RegExport.RXR1
