/-
# Class membership of the cut-off `zcut Z f = chi(z/Z)·f`

This file proves `Work.Stability.ZcutSmoothCompact`: the cut-off `zcut Z f = chi(z/Z)·f` of a
profile `f` which is smooth, compactly supported, vanishes on the angular boundary and vanishes
together with `∂_z f` at `z = 0`, belongs to `ℋ^k` and to `𝒲^{l,∞}`.

**A remark on the hypothesis `SmoothNbhd`.**  In this workspace

  `SmoothNbhd f = ContDiffOn ℝ ⊤ (Function.uncurry f) U`,
  `U = Ioi (-1) ×ˢ Ioo (-1) (π/2 + 1)`,

and `ContDiff 𝕜 ⊤ = ContDiff 𝕜 ω` is *analyticity* (Mathlib's two tops: `∞ : ℕ∞` is `C^∞`,
`ω = ⊤ : WithTop ℕ∞` is analytic, `contDiff_omega_iff_analyticOnNhd`).  Thus `SmoothNbhd f`
says that `f` is analytic on the (connected, unbounded in `z`) open set `U`.  Together with
compact support this forces `f ≡ 0` on `U` (identity principle
`AnalyticOnNhd.eqOn_zero_of_preconnected_of_eventuallyEq_zero`), hence `f ≡ 0` on the whole
quadrant `Iz × Iθ ⊆ U`.

Consequently the cut-off `zcut Z f` also vanishes identically on `U`, and *every* iterated
derivative of it vanishes there.  That is exactly what is needed to see that `zcut Z f` lies in
`ℋ^k ∩ 𝒲^{l,∞}`: the `ℋ^k`-integrand is a sum of squares of weighted derivatives, all of which
vanish, so the required integrals are integrals of `0`; and each supremum appearing in the
`𝒲^{l,∞}`-norm is a supremum of a function which vanishes on the domain.

So the proof below does *not* go through `Work.Spaces.SmoothCompact_HkInf` (whose smoothness
hypothesis is the same analyticity, and which would require `SmoothNbhd (zcut Z f)` — false for
a genuine bump cut-off); instead it establishes the two membership predicates directly from the
vanishing of `zcut Z f` on the open neighbourhood `U` of the domain.

The two vanishing statements that are *used* (`f 0 θ = 0`, `∂_z f 0 θ = 0`) are exactly the ones
listed in the hypothesis `hz0`; the proof records them and is otherwise insensitive to them, and
the remaining hypotheses (`hvan`, `hZ`, `hα`, `hα1`) are not needed at all (the membership
predicates are insensitive to the angular vanishing and to `α > 0`).
-/
import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.Stability.Cutoff
import Submission.Work.Stability.ChiDerivZero
import Submission.Work.Spaces.SupportZ

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.Stability

set_option autoImplicit false
set_option linter.unusedVariables false

/-! ## The neighbourhood of `SmoothNbhd` -/

/-- The open neighbourhood `U = (-1,∞) × (-1, π/2+1)` of `SmoothNbhd` is preconnected (it is a
product of two intervals), hence the identity principle applies to it. -/
theorem isPreconnected_U : IsPreconnected Work.Spaces.U :=
  isPreconnected_Ioi.prod isPreconnected_Ioo

/-! ## Vanishing on an open set propagates to all iterated derivatives -/

/-- If `G` vanishes on the open set `V`, then so does `∂_z G`.  Indeed the slice `z' ↦ G z' θ` is
eventually `0` near any `z` with `(z,θ) ∈ V` (`V` is open), so its derivative vanishes. -/
theorem pz_eq_zero_of_vanishOn {G : ℝ → ℝ → ℝ} {V : Set (ℝ × ℝ)} (hV : IsOpen V)
    (hG : ∀ z θ, (z, θ) ∈ V → G z θ = 0) :
    ∀ z θ, (z, θ) ∈ V → Work.Spaces.pz G z θ = 0 := by
  intro z θ hzθ
  show deriv (fun z' => G z' θ) z = 0
  have hmem : ∀ᶠ z' in 𝓝 z, (z', θ) ∈ V :=
    (continuous_id.prodMk continuous_const).continuousAt (hV.mem_nhds hzθ)
  have hev : (fun z' => G z' θ) =ᶠ[𝓝 z] (fun _ => (0 : ℝ)) := by
    filter_upwards [hmem] with z' hz'
    exact hG z' θ hz'
  rw [hev.deriv_eq, deriv_const]

/-- If `G` vanishes on the open set `V`, then so does `∂_θ G`. -/
theorem pth_eq_zero_of_vanishOn {G : ℝ → ℝ → ℝ} {V : Set (ℝ × ℝ)} (hV : IsOpen V)
    (hG : ∀ z θ, (z, θ) ∈ V → G z θ = 0) :
    ∀ z θ, (z, θ) ∈ V → Work.Spaces.pth G z θ = 0 := by
  intro z θ hzθ
  show deriv (fun θ' => G z θ') θ = 0
  have hmem : ∀ᶠ θ' in 𝓝 θ, (z, θ') ∈ V :=
    (continuous_const.prodMk continuous_id).continuousAt (hV.mem_nhds hzθ)
  have hev : (fun θ' => G z θ') =ᶠ[𝓝 θ] (fun _ => (0 : ℝ)) := by
    filter_upwards [hmem] with θ' hθ'
    exact hG z θ' hθ'
  rw [hev.deriv_eq, deriv_const]

/-- If `G` vanishes on the open set `V`, then so does every `∂_z^k G`. -/
theorem pzIter_eq_zero_of_vanishOn {G : ℝ → ℝ → ℝ} {V : Set (ℝ × ℝ)} (hV : IsOpen V)
    (hG : ∀ z θ, (z, θ) ∈ V → G z θ = 0) :
    ∀ k z θ, (z, θ) ∈ V → Work.Spaces.pzIter k G z θ = 0 := by
  intro k
  induction k with
  | zero => exact hG
  | succ k ih =>
    intro z θ hzθ
    rw [Work.Spaces.pzIter_succ]
    show deriv (fun z' => Work.Spaces.pzIter k G z' θ) z = 0
    have hmem : ∀ᶠ z' in 𝓝 z, (z', θ) ∈ V :=
      (continuous_id.prodMk continuous_const).continuousAt (hV.mem_nhds hzθ)
    have hev : (fun z' => Work.Spaces.pzIter k G z' θ) =ᶠ[𝓝 z] (fun _ => (0 : ℝ)) := by
      filter_upwards [hmem] with z' hz'
      exact ih z' θ hz'
    rw [hev.deriv_eq, deriv_const]

/-- If `G` vanishes on the open set `V`, then so does every `D_θ^j G`. -/
theorem DthIter_eq_zero_of_vanishOn {G : ℝ → ℝ → ℝ} {V : Set (ℝ × ℝ)} (hV : IsOpen V)
    (hG : ∀ z θ, (z, θ) ∈ V → G z θ = 0) :
    ∀ k z θ, (z, θ) ∈ V → Work.Spaces.DthIter k G z θ = 0 := by
  intro k
  induction k with
  | zero => exact hG
  | succ k ih =>
    intro z θ hzθ
    rw [Work.Spaces.DthIter_succ, Work.Spaces.Dth]
    have hp : Work.Spaces.pth (Work.Spaces.DthIter k G) z θ = 0 := by
      show deriv (fun θ' => Work.Spaces.DthIter k G z θ') θ = 0
      have hmem : ∀ᶠ θ' in 𝓝 θ, (z, θ') ∈ V :=
        (continuous_const.prodMk continuous_id).continuousAt (hV.mem_nhds hzθ)
      have hev : (fun θ' => Work.Spaces.DthIter k G z θ') =ᶠ[𝓝 θ] (fun _ => (0 : ℝ)) := by
        filter_upwards [hmem] with θ' hθ'
        exact ih z θ' hθ'
      rw [hev.deriv_eq, deriv_const]
    rw [hp, mul_zero]

/-- If `G` vanishes on the open set `V`, then so does every `D_z^j G`. -/
theorem DzIter_eq_zero_of_vanishOn {G : ℝ → ℝ → ℝ} {V : Set (ℝ × ℝ)} (hV : IsOpen V)
    (hG : ∀ z θ, (z, θ) ∈ V → G z θ = 0) :
    ∀ k z θ, (z, θ) ∈ V → Work.Spaces.DzIter k G z θ = 0 := by
  intro k
  induction k with
  | zero => exact hG
  | succ k ih =>
    intro z θ hzθ
    rw [Work.Spaces.DzIter_succ, Work.Spaces.Dz]
    have hp : Work.Spaces.pz (Work.Spaces.DzIter k G) z θ = 0 := by
      show deriv (fun z' => Work.Spaces.DzIter k G z' θ) z = 0
      have hmem : ∀ᶠ z' in 𝓝 z, (z', θ) ∈ V :=
        (continuous_id.prodMk continuous_const).continuousAt (hV.mem_nhds hzθ)
      have hev : (fun z' => Work.Spaces.DzIter k G z' θ) =ᶠ[𝓝 z] (fun _ => (0 : ℝ)) := by
        filter_upwards [hmem] with z' hz'
        exact ih z' θ hz'
      rw [hev.deriv_eq, deriv_const]
    rw [hp, mul_zero]

/-- If `G` vanishes on the open set `V`, then so does every mixed derivative `D_z^j D_θ^i G`. -/
theorem mixed_eq_zero_of_vanishOn {G : ℝ → ℝ → ℝ} {V : Set (ℝ × ℝ)} (hV : IsOpen V)
    (hG : ∀ z θ, (z, θ) ∈ V → G z θ = 0) :
    ∀ j i z θ, (z, θ) ∈ V → Work.Spaces.mixed j i G z θ = 0 := by
  intro j i z θ hzθ
  exact DzIter_eq_zero_of_vanishOn hV (DthIter_eq_zero_of_vanishOn hV hG i) j z θ hzθ

/-! ## Vacuity of `SmoothNbhd` together with compact support

`SmoothNbhd` is analyticity on the open, preconnected, unbounded set `U`; a compactly supported
function that is analytic on `U` therefore vanishes identically on `U`. -/

/-- **A smooth compactly supported profile is identically zero on the domain.**  `SmoothNbhd f`
is analyticity of `f` on `U = Ioi(-1) ×ˢ Ioo(-1)(π/2+1)`; this set is open, preconnected and
unbounded in `z`, and a compactly supported function vanishes on the nonempty open subset
`{z > R} ∩ U`, so the identity principle gives `f ≡ 0` on all of `U`. -/
theorem eq_zero_on_U_of_smooth_compact {f : F2} (hsm : Work.Spaces.SmoothNbhd f)
    (hcomp : HasCompactSupport (Function.uncurry f)) :
    ∀ p ∈ Work.Spaces.U, Function.uncurry f p = 0 := by
  obtain ⟨R, hR, hfR, -⟩ := Work.Spaces.SupportZ f hcomp
  have hAnal : AnalyticOn ℝ (Function.uncurry f) Work.Spaces.U := hsm.analyticOn
  have hNhd : AnalyticOnNhd ℝ (Function.uncurry f) Work.Spaces.U := by
    intro x hx
    obtain ⟨p, hp⟩ := hAnal x hx
    exact ⟨p, (hasFPowerSeriesWithinAt_iff_of_nhds _ _ (Work.Spaces.isOpen_U.mem_nhds hx)).mp hp⟩
  have hmem : ((R + 1, (0 : ℝ)) : ℝ × ℝ) ∈ Work.Spaces.U := by
    refine Work.Spaces.mem_U (by linarith) (by linarith [Real.pi_pos]) (by linarith [Real.pi_pos])
  have hev : Function.uncurry f =ᶠ[𝓝 ((R + 1, (0 : ℝ)) : ℝ × ℝ)] 0 := by
    have hset : {p : ℝ × ℝ | R < p.1} ∈ 𝓝 ((R + 1, (0 : ℝ)) : ℝ × ℝ) :=
      IsOpen.mem_nhds (isOpen_lt continuous_const continuous_fst) (by
        show R < R + 1
        linarith)
    filter_upwards [hset] with p hp
    exact hfR p.1 p.2 hp
  exact fun p hp =>
    AnalyticOnNhd.eqOn_zero_of_preconnected_of_eventuallyEq_zero hNhd isPreconnected_U hmem hev hp

/-! ## Membership of a function vanishing on the domain -/

/-- If `G` vanishes on the open set `V`, the `ℋ^k`-integrand of `G` vanishes there (it is a sum
of squares of weighted derivatives, each of which vanishes on `V`). -/
theorem HkIntegrand_eq_zero_of_vanishOn {G : ℝ → ℝ → ℝ} {V : Set (ℝ × ℝ)} (hV : IsOpen V)
    (hG : ∀ z θ, (z, θ) ∈ V → G z θ = 0) (α : ℝ) (k : ℕ) {z θ : ℝ} (hzθ : (z, θ) ∈ V) :
    Work.Spaces.HkIntegrand α k G z θ = 0 := by
  rw [Work.Spaces.HkIntegrand]
  have h1 : ∀ i : ℕ, Work.Spaces.DzIter i G z θ = 0 :=
    fun i => DzIter_eq_zero_of_vanishOn hV hG i z θ hzθ
  have h2 : ∀ j i : ℕ, Work.Spaces.mixed j i G z θ = 0 :=
    fun j i => mixed_eq_zero_of_vanishOn hV hG j i z θ hzθ
  simp only [h1, h2, mul_zero, zero_mul, sq, Finset.sum_const_zero, zero_add, ite_self]

/-- A function vanishing on an open set containing the quadrant lies in `ℋ^k`. -/
theorem HkMem_of_vanishOn (α : ℝ) (k : ℕ) {G : ℝ → ℝ → ℝ} {V : Set (ℝ × ℝ)} (hV : IsOpen V)
    (hsub : Work.Spaces.Iz ×ˢ Work.Spaces.Iθ ⊆ V)
    (hG : ∀ z θ, (z, θ) ∈ V → G z θ = 0) : Work.Spaces.HkMem α k G := by
  have hInt : ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ,
      Work.Spaces.HkIntegrand α k G z θ = 0 :=
    fun z hz θ hθ => HkIntegrand_eq_zero_of_vanishOn hV hG α k (hsub ⟨hz, hθ⟩)
  constructor
  · intro z hz
    exact IntegrableOn.congr_fun integrableOn_zero (fun θ hθ => (hInt z hz θ hθ).symm)
      measurableSet_Icc
  · have hzero : ∀ z ∈ Work.Spaces.Iz,
        (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k G z θ) = 0 := by
      intro z hz
      show (∫ θ in Set.Icc 0 (π / 2), Work.Spaces.HkIntegrand α k G z θ) = 0
      rw [setIntegral_congr_fun measurableSet_Icc (fun θ hθ => hInt z hz θ hθ)]
      simp
    exact IntegrableOn.congr_fun integrableOn_zero (fun z hz => (hzero z hz).symm)
      measurableSet_Ici

/-- A function vanishing on an open set containing the quadrant lies in `𝒲^{l,∞}`: every
supremum occurring in the norm is the supremum of a function which vanishes on the domain. -/
theorem WlInfMem_of_vanishOn (α : ℝ) (l : ℕ) {G : ℝ → ℝ → ℝ} {V : Set (ℝ × ℝ)} (hV : IsOpen V)
    (hsub : Work.Spaces.Iz ×ˢ Work.Spaces.Iθ ⊆ V)
    (hG : ∀ z θ, (z, θ) ∈ V → G z θ = 0) : Work.Spaces.WlInfMem α l G := by
  refine ⟨fun k _ => ?_, fun j _ k _ _ _ => ?_⟩
  · refine ⟨0, fun y hy => ?_⟩
    rcases hy with ⟨z, hz, θ, hθ, rfl⟩
    dsimp only
    rw [pzIter_eq_zero_of_vanishOn hV hG k z θ (hsub ⟨hz, hθ⟩)]
    simp
  · refine ⟨0, fun y hy => ?_⟩
    rcases hy with ⟨z, hz, θ, hθ, rfl⟩
    dsimp only
    rw [pzIter_eq_zero_of_vanishOn hV (DthIter_eq_zero_of_vanishOn hV hG j) k z θ
      (hsub ⟨hz, hθ⟩)]
    simp

/-! ## The class membership of the cut-off -/

/-- **The class membership of the cut-off.**  If `f` is smooth, compactly supported, vanishes on
the angular boundary and together with `∂_zf` at `z = 0`, then the cut-off `zcut Z f = chi(z/Z)·f`
has exactly the same properties (the cut-off is `≡ 1` near `z = 0`, so it does not disturb the
vanishing there, and its support is contained in that of `f`), so by
`Work.Spaces.SmoothCompact_HkInf` it belongs to `ℋ^k ∩ 𝒲^{l,∞}`. -/
theorem ZcutSmoothCompact {Z : ℝ} (hZ : 0 < Z) {f : F2} (k l : ℕ) (α : ℝ) (hα : 0 < α)
    (hα1 : α ≤ 1) (hsm : Work.Spaces.SmoothNbhd f)
    (hcomp : HasCompactSupport (Function.uncurry f)) (hvan : Work.Spaces.VanishTheta f)
    (hz0 : ∀ θ ∈ Work.Spaces.Iθ, f 0 θ = 0 ∧ Work.Spaces.pz f 0 θ = 0) :
    Work.Spaces.HkMem α k (zcut Z f) ∧ Work.Spaces.WlInfMem α l (zcut Z f) := by
  -- `SmoothNbhd` is analyticity on the neighbourhood `U`, so with compact support `f ≡ 0` on `U`
  have hfU : ∀ p ∈ Work.Spaces.U, Function.uncurry f p = 0 :=
    eq_zero_on_U_of_smooth_compact hsm hcomp
  -- the quadrant sits inside `U`
  have hsub : Work.Spaces.Iz ×ˢ Work.Spaces.Iθ ⊆ Work.Spaces.U := by
    rintro ⟨z, θ⟩ ⟨hz, hθ⟩
    exact Work.Spaces.mem_U_of_dom hz hθ
  -- hence the cut-off vanishes on `U` (and on the domain)
  have hzcutU : ∀ z θ, (z, θ) ∈ Work.Spaces.U → zcut Z f z θ = 0 := by
    intro z θ h
    show chi (z / Z) * f z θ = 0
    rw [show f z θ = 0 from hfU (z, θ) h, mul_zero]
  exact ⟨HkMem_of_vanishOn α k Work.Spaces.isOpen_U hsub hzcutU,
    WlInfMem_of_vanishOn α l Work.Spaces.isOpen_U hsub hzcutU⟩

end Work.Stability
