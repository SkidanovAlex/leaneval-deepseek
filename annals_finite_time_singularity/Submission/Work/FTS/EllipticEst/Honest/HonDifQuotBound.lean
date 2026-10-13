import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Submission.Work.FTS.EllipticEst.Honest.Basic
import Submission.Work.FTS.EllipticEst.Blocks.PzIterTwoContinuousOn

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.Honest

set_option autoImplicit false

/-! # The mean-value bound for the `z`-difference quotient of an honest pair

The honest class `Hon` gives `C^∞`-smoothness of `Ψ` on the *open* quadrant only.  On the
interior of the quadrant the slices are therefore as smooth as one wishes, and the second-order
Taylor bound

  `|(Ψ z θ - Ψ (z - hh) θ) / hh - ∂_zΨ(z,θ)| ≤ ∫_{z-hh}^{z} |∂_z²Ψ|`

holds.  Since `hh < z/2` the interval `[z - hh, z]` is contained in `[z/2, z]`, which is the
form stated (the wider interval is the one that will be available later, when `∂_z²Ψ` is only
known to be a measurable function).

The proof is the two-step mean-value argument: `ξ ∈ (z - hh, z)` with
`(Ψ z θ - Ψ (z-hh) θ)/hh = ∂_zΨ(ξ,θ)` (Lagrange), and then `∂_zΨ(z,θ) - ∂_zΨ(ξ,θ) = ∫_ξ^z ∂_z²Ψ`
(Fundamental theorem of calculus), bounded by the integral of the absolute value over the
enlarged interval.
-/

/-- The open quadrant, on which the honest class `Hon` is smooth. -/
abbrev HonQd : Set (ℝ × ℝ) := Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (0 : ℝ) (Real.pi / 2)

theorem isOpen_HonQd : IsOpen HonQd := isOpen_Ioi.prod isOpen_Ioo

/-! ## Generic slice facts for `C^n`-functions on an open subset of `ℝ × ℝ` -/

/-- A `C¹`-function on an open subset of `ℝ × ℝ` has differentiable `z`-slices on that set,
with derivative the `z`-partial `pz`. -/
theorem hasDerivAt_slice_of_contDiffOn {G : ℝ → ℝ → ℝ} {U : Set (ℝ × ℝ)} (hU : IsOpen U)
    (hG : ContDiffOn ℝ 1 (Function.uncurry G) U) {u θ : ℝ} (hmem : (u, θ) ∈ U) :
    HasDerivAt (fun u' => G u' θ) (Work.Spaces.pz G u θ) u := by
  have hd : DifferentiableAt ℝ (Function.uncurry G) (u, θ) :=
    (hG.differentiableOn (by norm_num)).differentiableAt (hU.mem_nhds hmem)
  have hcur : DifferentiableAt ℝ (fun u' => G u' θ) u :=
    Work.Spaces.differentiableAt_curry_left hd
  simpa [Work.Spaces.pz] using hcur.hasDerivAt

/-- `z`-slices of a `C^n`-function on an open subset of `ℝ × ℝ`, restricted to a subset of that
open set.  (Renamed from `contDiffOn_slice` to avoid a name clash with
`Honest.contDiffOn_slice` of `Honest/HonSliceRightTendsto.lean`, which is the version used by the
whole `Ae`/`ang` chapter; importing both files used to make the environment inconsistent.) -/
theorem contDiffOn_slice_Icc {G : ℝ → ℝ → ℝ} {U : Set (ℝ × ℝ)} {n : WithTop ℕ∞}
    (hG : ContDiffOn ℝ n (Function.uncurry G) U) {a b θ : ℝ}
    (hmaps : ∀ s ∈ Set.Icc a b, (s, θ) ∈ U) :
    ContDiffOn ℝ n (fun s => G s θ) (Set.Icc a b) :=
  hG.comp (by fun_prop) hmaps

/-! ## The mean-value bound -/

/-- **Second-order Taylor bound for a backward difference quotient.**  If `g` is the derivative
of `f` on `[a,b]`, `g'` the derivative of `g` there, and `a ≤ b - hh` with `hh > 0`, then the
backward difference quotient of `f` at `b` approximates `g b` up to the integral of `|g'|` over
the whole interval `[a,b]`. -/
theorem abs_difquot_sub_deriv_le {f g g' : ℝ → ℝ} {a b hh : ℝ}
    (hh_pos : 0 < hh) (ha : a ≤ b - hh)
    (hfcont : ContinuousOn f (Set.Icc (b - hh) b))
    (hfdiff : DifferentiableOn ℝ f (Set.Ioo (b - hh) b))
    (hfderiv : ∀ x ∈ Set.Icc a b, HasDerivAt f (g x) x)
    (hgderiv : ∀ x ∈ Set.Icc a b, HasDerivAt g (g' x) x)
    (hgi : IntervalIntegrable g' volume a b) :
    |(f b - f (b - hh)) / hh - g b| ≤ ∫ x in a..b, |g' x| := by
  have hbhh : b - hh < b := by linarith
  have hab : a ≤ b := le_trans ha (le_of_lt hbhh)
  -- Lagrange's mean value theorem on the slice
  obtain ⟨ξ, hξ, hξderiv⟩ := exists_deriv_eq_slope f hbhh hfcont hfdiff
  have hξle : ξ ≤ b := le_of_lt hξ.2
  have haξ : a ≤ ξ := le_trans ha (le_of_lt hξ.1)
  have hξmem : ξ ∈ Set.Icc a b := ⟨haξ, hξle⟩
  -- the slope is the derivative of `f`, which is `g`
  have hgξ : deriv f ξ = g ξ := (hfderiv ξ hξmem).deriv
  have hslope : (f b - f (b - hh)) / hh = g ξ := by
    have h1 : b - (b - hh) = hh := by ring
    have h2 : (f b - f (b - hh)) / (b - (b - hh)) = g ξ := hξderiv.symm.trans hgξ
    rwa [h1] at h2
  -- the fundamental theorem of calculus for `g` on `[ξ,b]`
  have hftc : ∫ x in ξ..b, g' x = g b - g ξ := by
    refine intervalIntegral.integral_eq_sub_of_hasDerivAt (f := g) (f' := g') ?_ ?_
    · intro x hx
      rw [Set.uIcc_of_le hξle] at hx
      exact hgderiv x ⟨le_trans haξ hx.1, hx.2⟩
    · refine hgi.mono_set ?_
      rw [Set.uIcc_of_le hξle, Set.uIcc_of_le hab]
      exact Set.Icc_subset_Icc_left haξ
  rw [hslope]
  calc |g ξ - g b| = |∫ x in ξ..b, g' x| := by rw [hftc]; exact abs_sub_comm _ _
    _ ≤ ∫ x in ξ..b, |g' x| := intervalIntegral.abs_integral_le_integral_abs hξle
    _ ≤ ∫ x in a..b, |g' x| :=
        intervalIntegral.integral_mono_interval haξ hξle le_rfl
          (Eventually.of_forall fun x => abs_nonneg _) hgi.abs

/-! ## The honest difference-quotient bound -/

theorem HonDifQuotBound (α : ℝ) (F Ψ : ℝ → ℝ → ℝ) (h : Work.FTS.EllipticEst.Honest.Hon α F Ψ) :
    ∀ z : ℝ, 0 < z → ∀ hh : ℝ, 0 < hh → hh < z / 2 → ∀ θ : ℝ, 0 < θ → θ < Real.pi / 2 →
      |(Ψ z θ - Ψ (z - hh) θ) / hh - Work.Spaces.pz Ψ z θ|
        ≤ ∫ u in (z / 2)..z, |Work.Spaces.pzIter 2 Ψ u θ| := by
  intro z hz hh hh_pos hh_lt θ hθ0 hθ1
  have hz2le : z / 2 ≤ z := by linarith
  have hz2thh : z / 2 ≤ z - hh := by linarith
  -- every point of the relevant rectangles lies in the open quadrant
  have hmemIcc : ∀ s ∈ Set.Icc (z / 2) z, (s, θ) ∈ HonQd := fun s hs =>
    ⟨Set.mem_Ioi.mpr (by linarith [hs.1]), hθ0, hθ1⟩
  have hmemIcc' : ∀ s ∈ Set.Icc (z - hh) z, (s, θ) ∈ HonQd := fun s hs =>
    ⟨Set.mem_Ioi.mpr (by linarith [hs.1, hz2thh]), hθ0, hθ1⟩
  -- smoothness of the slice, and the two derivative facts
  have hslice2 : ContDiffOn ℝ 2 (fun s : ℝ => Ψ s θ) (Set.Icc (z - hh) z) :=
    contDiffOn_slice_Icc (h.sm 2) hmemIcc'
  have hfcont : ContinuousOn (fun s : ℝ => Ψ s θ) (Set.Icc (z - hh) z) := hslice2.continuousOn
  have hfdiff : DifferentiableOn ℝ (fun s : ℝ => Ψ s θ) (Set.Ioo (z - hh) z) :=
    (hslice2.differentiableOn (by norm_num)).mono Set.Ioo_subset_Icc_self
  have hfderiv : ∀ x ∈ Set.Icc (z / 2) z,
      HasDerivAt (fun s : ℝ => Ψ s θ) (Work.Spaces.pz Ψ x θ) x := fun x hx =>
    hasDerivAt_slice_of_contDiffOn isOpen_HonQd (h.sm 1) (hmemIcc x hx)
  have hpz1 : ContDiffOn ℝ 1 (Function.uncurry (Work.Spaces.pz Ψ)) HonQd :=
    Work.FTS.EllipticEst.Blocks.contDiffOn_uncurry_pz_succ isOpen_HonQd (h.sm 2)
  have hgderiv : ∀ x ∈ Set.Icc (z / 2) z,
      HasDerivAt (fun s : ℝ => Work.Spaces.pz Ψ s θ) (Work.Spaces.pzIter 2 Ψ x θ) x := by
    intro x hx
    have h' := hasDerivAt_slice_of_contDiffOn isOpen_HonQd hpz1 (hmemIcc x hx)
    simpa [Work.Spaces.pzIter_succ] using h'
  -- interval integrability of `∂_z²Ψ` on the slice
  have hcs : ContinuousOn (fun s : ℝ => Work.Spaces.pzIter 2 Ψ s θ) (Set.Icc (z / 2) z) :=
    (Work.FTS.EllipticEst.Blocks.PzIterTwoContinuousOn isOpen_HonQd (h.sm 2)).comp
      (by fun_prop) hmemIcc
  have hgi : IntervalIntegrable (fun s : ℝ => Work.Spaces.pzIter 2 Ψ s θ) volume (z / 2) z := by
    refine ContinuousOn.intervalIntegrable ?_
    rw [Set.uIcc_of_le hz2le]
    exact hcs
  exact abs_difquot_sub_deriv_le (f := fun s : ℝ => Ψ s θ)
    (g := fun s : ℝ => Work.Spaces.pz Ψ s θ) (g' := fun s : ℝ => Work.Spaces.pzIter 2 Ψ s θ)
    (a := z / 2) (b := z) (hh := hh) hh_pos hz2thh hfcont hfdiff hfderiv hgderiv hgi

end Work.FTS.EllipticEst.Honest
