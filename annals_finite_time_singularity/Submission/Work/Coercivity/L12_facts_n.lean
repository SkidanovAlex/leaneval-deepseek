/-
# The basic analytic facts about `L₁₂^K(g)` for `g ∈ ℋ^n`

This module proves `Work.Coercivity.L12_facts_n`: for `0 < α ≤ 1`, `n ≥ 1` and a function
`g` which is smooth (in this Mathlib: *analytic*, since `ContDiffOn ℝ ⊤` is `C^ω`) on a
neighbourhood of the closed quadrant and belongs to the weighted space `ℋ^n`
(`Work.Spaces.HkMem α n g`), the density

  `L12dens K g z = ∫_θ K(θ) g(z,θ)/z`

is integrable on `(0,∞)`, is the (negative) derivative of the tail integral
`L₁₂^K(g)(z) = ∫_z^∞ L12dens K g s ds`, is continuous there, and `L₁₂^K(g)` is `C^ω`
(analytic) on `(0,∞)`.

The first three facts already occur, for the fixed value `n = 4`, in
`Work.Elliptic.L12densFacts`; here they are stated for the general `n ≥ 1` (the estimate
only ever uses the `D_z^0` term of `HkIntegrand`, which is present for every `n`), and the
`C^ω`-statement is added.  Since this Mathlib denotes `⊤ : ℕ∞ω` by `ω` (analyticity) and
`(⊤ : ℕ∞) : ℕ∞ω` by `∞` (smoothness), the last conjunct of the requested statement is an
*analyticity* statement; it holds because `SmoothNbhd g` itself says that `g` is jointly
analytic on a neighbourhood of the closed quadrant, and both the angular integral and the
tail integral of a jointly analytic function are analytic.
-/
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Submission.Work.Coercivity.CTDefs
import Submission.Work.Elliptic.L12densFacts
import Submission.Work.Coercivity.contDiffOn_setIntegral_Itheta
import Submission.Work.Coercivity.analyticAt_intervalIntegral
import Submission.Work.Coercivity.L12dens_integrableOn

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology ContDiff ENNReal
open MeasureTheory Set Filter

namespace Work.Coercivity

set_option autoImplicit false

/-! ## Bridges to the `Work.Elliptic` vocabulary -/

/-- `FM.L12dens Spaces.K g` is `Elliptic.L12dens g` (`Ktheta = Spaces.K`, `Iθ = Icc 0 (π/2)`). -/
theorem L12dens_K_eq_Elliptic (g : ℝ → ℝ → ℝ) :
    Work.FM.L12dens Work.Spaces.K g = Work.Elliptic.L12dens g := by
  funext s
  rw [Work.Elliptic.L12dens, Work.FM.L12dens]
  exact setIntegral_congr_fun measurableSet_Icc (fun θ _ => by rw [Work.Elliptic.Ktheta_eq_K])

/-- `Coercivity.L12f g` is `Elliptic.L12 g` (`Spaces.K = FM.Kpaper`). -/
theorem L12f_eq_Elliptic_L12 (g : ℝ → ℝ → ℝ) :
    L12f g = Work.Elliptic.L12 g := by
  funext z
  rw [L12f, Work.Elliptic.L12_eq_FM]
  rfl

/-- The density `L12dens Spaces.K g` is continuous at every `z > 0`. -/
theorem L12dens_continuousAt_K (g : ℝ → ℝ → ℝ) (hsm : Work.Spaces.SmoothNbhd g)
    (z : ℝ) (hz : 0 < z) : ContinuousAt (Work.FM.L12dens Work.Spaces.K g) z := by
  rw [L12dens_K_eq_Elliptic]
  exact Work.Elliptic.L12dens_continuousAt_aux g hsm z hz


/-! ## Joint analyticity of the density integrand -/

/-- The integrand `(z,θ) ↦ K(θ) g(z,θ)/z` of the density is jointly `C^ω` (analytic) on
`(0,∞) × (-1, π/2+1)`, as it is a product/quotient of the jointly analytic `g` and the
entire angular weight `K`. -/
theorem contDiffOn_uncurry_densIntegrand (g : ℝ → ℝ → ℝ) (hsm : Work.Spaces.SmoothNbhd g) :
    ContDiffOn ℝ ⊤ (Function.uncurry (fun z θ => Work.Spaces.K θ * g z θ / z))
      (Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (-1) (π / 2 + 1)) := by
  have hsub : Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (-1) (π / 2 + 1)
      ⊆ Set.Ioi (-1) ×ˢ Set.Ioo (-1) (π / 2 + 1) := by
    rintro ⟨z, θ⟩ ⟨hz, hθ⟩
    exact ⟨by simp only [Set.mem_Ioi] at hz ⊢; linarith, hθ⟩
  have hg : ContDiffOn ℝ ⊤ (fun p : ℝ × ℝ => g p.1 p.2)
      (Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (-1) (π / 2 + 1)) := hsm.mono hsub
  have hfun : Function.uncurry (fun z θ => Work.Spaces.K θ * g z θ / z)
      = fun p : ℝ × ℝ => Work.Spaces.K p.2 * g p.1 p.2 / p.1 := rfl
  rw [hfun]
  refine ContDiffOn.div ?_ contDiffOn_fst ?_
  · have hK : ContDiffOn ℝ ⊤ (fun p : ℝ × ℝ => Work.Spaces.K p.2)
        (Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (-1) (π / 2 + 1)) := by
      unfold Work.Spaces.K
      fun_prop
    exact hK.mul hg
  · intro p hp
    exact ne_of_gt hp.1

/-! ## Analyticity of the tail integral from analyticity of the density -/

/-- **The tail integral of an analytic density is analytic**: if the density `L12dens K g`
is integrable on `(0,∞)` and its primitive is analytic (automatically, by
`Work.Coercivity.analyticAt_intervalIntegral`, whenever the density is analytic), then so
is `L₁₂^K(g)`. -/
theorem contDiffOn_L12f_of_dens (g : ℝ → ℝ → ℝ)
    (hint : MeasureTheory.IntegrableOn (Work.FM.L12dens Work.Spaces.K g) (Set.Ioi 0))
    (hprim : ∀ z₀ : ℝ, 0 < z₀ →
      AnalyticAt ℝ (fun z => ∫ s in z₀..z, Work.FM.L12dens Work.Spaces.K g s) z₀) :
    ContDiffOn ℝ ⊤ (fun z => L12f g z) (Set.Ioi 0) := by
  rw [contDiffOn_omega_iff_analyticOn isOpen_Ioi.uniqueDiffOn,
    isOpen_Ioi.analyticOn_iff_analyticOnNhd]
  intro z hz
  have hzpos : 0 < z := hz
  have hAnal : AnalyticAt ℝ (fun t => ∫ s in z..t, Work.FM.L12dens Work.Spaces.K g s) z :=
    hprim z hzpos
  have hev : (fun t => L12f g t) =ᶠ[𝓝 z]
      (fun t => L12f g z - ∫ s in z..t, Work.FM.L12dens Work.Spaces.K g s) := by
    filter_upwards [isOpen_Ioi.mem_nhds hz] with t ht
    have htpos : 0 < t := ht
    have hint_z : MeasureTheory.IntegrableOn (Work.FM.L12dens Work.Spaces.K g) (Set.Ioi z) :=
      hint.mono_set fun x hx => lt_trans hzpos hx
    have hint_t : MeasureTheory.IntegrableOn (Work.FM.L12dens Work.Spaces.K g) (Set.Ioi t) :=
      hint.mono_set fun x hx => lt_trans htpos hx
    have hzt : (∫ s in Set.Ioi z, Work.FM.L12dens Work.Spaces.K g s)
        - (∫ s in Set.Ioi t, Work.FM.L12dens Work.Spaces.K g s)
        = ∫ s in z..t, Work.FM.L12dens Work.Spaces.K g s := by
      rcases le_total z t with hle | hle
      · exact intervalIntegral.integral_Ioi_sub_Ioi hint_z hle
      · have hsym : (∫ s in z..t, Work.FM.L12dens Work.Spaces.K g s)
            = -∫ s in t..z, Work.FM.L12dens Work.Spaces.K g s :=
          intervalIntegral.integral_symm (a := t) (b := z)
        have h := intervalIntegral.integral_Ioi_sub_Ioi hint_t hle
        rw [hsym]
        linarith
    show Work.FM.L12 Spaces.K g t
      = Work.FM.L12 Spaces.K g z - ∫ s in z..t, Work.FM.L12dens Work.Spaces.K g s
    rw [Work.FM.L12, Work.FM.L12]
    linarith
  refine ((analyticAt_const : AnalyticAt ℝ (fun _ : ℝ => L12f g z) z).sub hAnal).congr ?_
  exact hev.symm



/-! ## The main theorem -/

/-- **The basic facts about `L₁₂^K(g)`** (the analytic input of the `ℋ^k`-coercivity of
`𝓛_Γ`): for `g` smooth on a neighbourhood of the closed quadrant and `g ∈ ℋ^n`, the density
`L12dens K g` is integrable on `(0,∞)`, is the negative derivative of `L₁₂^K(g)` at every
`z > 0`, is continuous there, and `L₁₂^K(g)` is analytic on `(0,∞)`.

`SmoothNbhd g` says that `g` is jointly analytic on a neighbourhood of the closed quadrant
(`ContDiffOn ℝ ⊤` is `C^ω`, i.e. real analytic, in this Mathlib revision), so the density
`∫_θ K(θ)g(z,θ)/z dθ` is analytic in `z` by `Work.Coercivity.contDiffOn_setIntegral_Itheta`,
and its primitive / tail integral is analytic by `Work.Coercivity.analyticAt_intervalIntegral`. -/
theorem L12_facts_n (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) (n : ℕ) (hn : 1 ≤ n)
    (g : ℝ → ℝ → ℝ) (hsm : Work.Spaces.SmoothNbhd g) (hmem : Work.Spaces.HkMem α n g) :
    MeasureTheory.IntegrableOn (Work.FM.L12dens Work.Spaces.K g) (Set.Ioi 0)
    ∧ (∀ z : ℝ, 0 < z → HasDerivAt (fun t => Work.Coercivity.L12f g t) (-(Work.FM.L12dens Work.Spaces.K g z)) z)
    ∧ (∀ z : ℝ, 0 < z → ContinuousAt (Work.FM.L12dens Work.Spaces.K g) z)
    ∧ ContDiffOn ℝ ⊤ (fun z => Work.Coercivity.L12f g z) (Set.Ioi 0) := by
  -- integrability of the density (from `ℋⁿ`-membership, for any `n`)
  have hint : MeasureTheory.IntegrableOn (Work.FM.L12dens Work.Spaces.K g) (Set.Ioi 0) :=
    L12dens_integrableOn α n g hsm hmem
  -- analyticity of the density (from the joint analyticity of `g`)
  have hcd : ContDiffOn ℝ ⊤ (fun z => Work.FM.L12dens Work.Spaces.K g z) (Set.Ioi 0) :=
    contDiffOn_setIntegral_Itheta (fun z θ => Work.Spaces.K θ * g z θ / z)
      (contDiffOn_uncurry_densIntegrand g hsm)
  have hAnalOn : AnalyticOn ℝ (Work.FM.L12dens Work.Spaces.K g) (Set.Ioi 0) :=
    (contDiffOn_omega_iff_analyticOn isOpen_Ioi.uniqueDiffOn).1 hcd
  have hAnalAt : ∀ z₀ : ℝ, 0 < z₀ → AnalyticAt ℝ (Work.FM.L12dens Work.Spaces.K g) z₀ :=
    fun z₀ hz₀ => (isOpen_Ioi.analyticOn_iff_analyticOnNhd).1 hAnalOn z₀ hz₀
  have hcontAt : ∀ z : ℝ, 0 < z → ContinuousAt (Work.FM.L12dens Work.Spaces.K g) z :=
    fun z hz => L12dens_continuousAt_K g hsm z hz
  refine ⟨hint, ?_, hcontAt, ?_⟩
  · intro z hz
    exact Work.FM.hasDerivAt_L12 (K := Work.Spaces.K) (f := g) (a := 0) (ρ := z)
      hint (hcontAt z hz) hz
  · exact contDiffOn_L12f_of_dens g hint (fun z₀ hz₀ => analyticAt_intervalIntegral (hAnalAt z₀ hz₀))

end Work.Coercivity
