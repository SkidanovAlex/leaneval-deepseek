import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.TotallySplit
import Submission.Work.FTS.BSIdent.Weyl.Levels.merPsiT_origin_aux2
import Submission.Work.FTS.BSIdent.hid_of_corrected
import Submission.Work.FTS.FinalV2.Defs
import Submission.Work.FTS.StrongEps.EComparison.SlotsZeroSliceInt
import Submission.Work.FTS.StrongPersist.DthFstar_W6
import Submission.Work.FTS_BSIdentP.Producers
import Submission.Work.FTS_RegExport.RXT.Sys.abs_L12dens_Fstar_add_le
import Submission.Work.Stability.mul_rpow_le
-- ===== merged: Submission.Work.FTS.StreamBdryIface.Producers =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.FTS.StreamBdryIface.Producers` — the (9″) producer: BSIdent port + StreamBdry
(curric-46 lead install, 2026-10-10)

Design `cbc/fts_streambdry_design.md` (+ `.lean`), corrected by `cbc/fts_streambdry_design_REVIEW.md`:

* **FIX-A** (replaces the design's new inputs (1d)): NO `EllGrowth`/`StarGrowth`, no `Growth`
  hypothesis anywhere, no `ExistsEllSolC` change. The slot-invisible gauge mode
  `gaugeMode αG = z^{-3/αG}/cos θ` is *subtracted*: SB1′ (`sb1_gauge`) decomposes every slice as
  `Ψ = psiP αG Ψ + κ·gaugeMode αG`, SB2–SB6 run on `psiP` (the "U-slot part"), and the new SB0
  (`sb0_psiField`) shows the gauge summand is invisible to `Cyl.psiField` on `Uax` (this replaces
  the design's P3 function equality `merPsi_dict`, false when `κ ≠ 0`).
* **FIX P2**: the slim variant `hid_of_corrected'_slim` plus `continuous_axisLevel_slim` (the
  `z = 0` case of `Weyl/Levels/continuous_axisLevel`, where `w = ρ(0,z)^p/B = 0`).
* **FIX-SB5**: the barrier is `w = (M + δφ(θ))(z/L)^{-k}` with `φ ≥ 0` blowing up at both ends and
  `𝓐φ` bounded below (`sb5_barrier`, an explicit sub-leaf consumed by `sb5_decay`).
* SB2 consumes the explicit sub-leaf `sb2_dthDV` (`∂_θ D_z V(psiP)` bounded, from the `D_z³` bound).

Every theorem below except where stated is `:= by sorry` on purpose (one named producer per item).
`hid9''_of_parts` is the assembly: it is NOT glue (the law for `psiHatP` needs `bslOp gaugeMode = 0`,
and the firing family `extG G` must be matched with `extG g` inside `physOmega`), so it is a named
sorry; `FinalV2.hid9''` is proved from it.

| item | theorem | owner |
|---|---|---|
| SB0 | `sb0_psiField` | StreamBdry (mechanical) |
| SB1′ | `sb1_gauge` | StreamBdry (low) |
| SB2 | `sb2_dthDV` (sub-leaf), `sb2_c2` | StreamBdry (medium) |
| SB3 | `sb3_bounds` | StreamBdry (low) |
| SB4 | `sb4_near0` | StreamBdry (low–medium; shared weighted sup with RX-B/RX-A1w) |
| SB5 | `sb5_barrier` (sub-leaf), `sb5_decay` | StreamBdry (medium) |
| SB6 | `sb6_rates` | StreamBdry (low) |
| inputs | `slice_inputs` | StreamBdry (after RX-VP `dbnd`) |
| P1 | `hid_of_corrected'` | BSIdent port (mechanical) |
| P2 | `hid_of_corrected'_slim`, `continuous_axisLevel_slim` | BSIdent port (gate) |
| (9″) | `hid9''_of_parts` | assembly |
-/

noncomputable section
open scoped Real Topology NNReal
open Set Filter

namespace Work.FTS.StreamBdryIface

open Work.FTS.Galerkin (Fn Fam slice IsDynGSolWith)
open Work.FTS.Nonlin (PsiCan)
open Work.FTS.Physical (PhysClock)
open Work.FTS.Final
open Work.FTS.FinalClock
open Work.FTS.FinalV2
open Work.FTS.Regularity (pExp)
open Work.FTS.RegPkgGal (extG)

set_option autoImplicit false

/-! ## §0 Vocabulary -/

/-- The `U`-slot `U(Ψ)/sin 2θ`, with `U(Ψ) = -3Ψ - αG z∂_zΨ`. -/
def Uprime (αG : ℝ) (Ψ : Fn) : Fn := fun z θ =>
  Work.Construction.Uop αG Ψ z θ / Work.Construction.s2 θ

/-- Slot bounds on the open quadrant (from RX-VP `VelPkg.dbnd`, full stream function). -/
def SlotBd (αG : ℝ) (Ψ : Fn) (M : ℝ) : Prop :=
  ∀ z θ, (z, θ) ∈ Work.Construction.Qd →
    (∀ j ≤ 2, |Work.Spaces.DzIter j (Uprime αG Ψ) z θ| ≤ M) ∧
    |Work.Spaces.mixed 0 1 (Uprime αG Ψ) z θ| ≤ M ∧
    (∀ j ≤ 1, |Work.Spaces.DzIter j (Work.Construction.Vop Ψ) z θ| ≤ M)

/-- Source facts on the closed angular strip (from `RegPkg'`: `hvan`, `hg`, `hpz`, `hsupp`). -/
def SrcOK (F : Fn) (L M : ℝ) : Prop :=
  ContinuousOn (Function.uncurry F) (Ioi 0 ×ˢ Work.Spaces.Iθ) ∧
  ContinuousOn (Function.uncurry (Work.Spaces.Dz F)) (Ioi 0 ×ˢ Work.Spaces.Iθ) ∧
  (∀ z θ, 0 < z → θ ∈ Work.Spaces.Iθ → |F z θ| ≤ M ∧ |Work.Spaces.Dz F z θ| ≤ M) ∧
  (∀ z, 0 < z → F z 0 = 0 ∧ F z (π / 2) = 0) ∧
  (0 < L ∧ ∀ z θ, L ≤ z → θ ∈ Work.Spaces.Iθ → F z θ = 0)

/-- **The slot-invisible gauge mode** `z^{-3/αG}/cos θ`: `Uop = Vop = Rop = bslOp = 0` (REVIEW (1b),
sympy). It is subtracted, not excluded (FIX-A). -/
def gaugeMode (αG : ℝ) : Fn := fun z θ => z ^ (-(3 / αG)) / Real.cos θ

/-- **The `U`-slot part** of a stream function: the solution of `αG·D_zP + 3P = -s2·U'(Ψ)` regular at
the origin, `P = -(s2/αG)∫₀¹ v^{3/αG-1} U'(Ψ)(zv) dv`. -/
def psiP (αG : ℝ) (Ψ : Fn) : Fn := fun z θ =>
  -(Work.Construction.s2 θ / αG) *
    ∫ v in (0 : ℝ)..1, v ^ (3 / αG - 1) * Uprime αG Ψ (z * v) θ

/-- Slice-level odd extension across `θ = 0` of the `θ > 0` part, then odd reflection across
`θ = ±π/2` (π-periodic odd function on `|θ| < π/2 + 1`). -/
def oddPerS (Ψ : Fn) : Fn := fun w θ =>
  let P : ℝ → ℝ := fun θ' => if 0 < θ' then Ψ w θ' else if θ' < 0 then -Ψ w (-θ') else 0
  if θ < -(π / 2) then -P (-π - θ) else if θ ≤ π / 2 then P θ else -P (π - θ)

/-- **The family handed to BSIdent** (`psiHat°` of the review): `oddPerS` of the `U`-slot part of the
canonical slice on `w > 0`, `0` on `w ≤ 0`. -/
def psiHatP (αG : ℝ) (Φs : Fn) (E : Fn → Fn) (g : Fam) : Fam := fun w θ τ =>
  if 0 < w then oddPerS (psiP αG (slice (PsiCan Φs E g) τ)) w θ else 0

/-- The barrier condition of FIX-SB5 (one-dimensional): `φ ≥ 0` on `(0,π/2)`, `C²` there, blowing up
at both ends (like `1/θ` and `1/(π/2-θ)²`, plus log corrections), and
`𝓐φ := -φ'' - (4 cot 2θ - tan θ) φ'` bounded below. -/
def SB5Barrier : Prop :=
  ∃ (φ : ℝ → ℝ) (Cφ : ℝ), ContDiffOn ℝ 2 φ (Ioo 0 (π / 2)) ∧
    (∀ θ ∈ Ioo (0 : ℝ) (π / 2), 0 ≤ φ θ) ∧
    Tendsto φ (𝓝[>] 0) atTop ∧ Tendsto φ (𝓝[<] (π / 2)) atTop ∧
    ∀ θ ∈ Ioo (0 : ℝ) (π / 2),
      -Cφ ≤ -deriv (deriv φ) θ
        - (4 * Real.cos (2 * θ) / Real.sin (2 * θ) - Real.tan θ) * deriv φ θ

/-! ## §1 BSIdent port -/




/-! ## §2 StreamBdry leaves (slice level; FIX-A: no `Growth`, SB2–SB6 on `psiP`) -/


/-- **SB0 (mechanical, replaces P3)**: the gauge summand is invisible to the meridian field. With
`slice PsiCan = psiP + κ(τ)·gaugeMode` (SB1′), `merPsi` of the gauge part is
`A⁻¹B^{3/p}κ·sgn(z)/r`, whose `Cyl.psiField` vanishes on `Uax` (`u_r = ∂_zψ = 0`,
`u_z = -ψ/r - ∂_rψ = 0`); conclude by additivity of `pdR/pdZ` (differentiability of the `psiP` part
from `hPsm` = SB2, of the full part from `hC3` = (13′)). For `θP > 0` `psiFire = PsiCan`, for
`θP < 0` both families are the odd reflections. -/
theorem sb0_psiField {a : ℝ} (ha : 0 < a) {Φs : Fn} {E : Fn → Fn} {g : Fam} {A B : ℝ → ℝ}
    {C : PhysClock}
    (hC3 : ∀ τ : ℝ, 0 ≤ τ →
      ContDiffOn ℝ 3 (fun q : ℝ × ℝ => PsiCan Φs E g q.1 q.2 τ) Work.Construction.Qd)
    (hdec : ∀ τ : ℝ, 0 ≤ τ → ∃ κ : ℝ, ∀ z θ, (z, θ) ∈ Work.Construction.Qd →
      slice (PsiCan Φs E g) τ z θ
        = psiP (pExp a) (slice (PsiCan Φs E g) τ) z θ + κ * gaugeMode (pExp a) z θ)
    (hPsm : ∀ τ : ℝ, 0 ≤ τ →
      ContDiffOn ℝ 2 (Function.uncurry (oddPerS (psiP (pExp a) (slice (PsiCan Φs E g) τ))))
        (Ioi 0 ×ˢ Ioo (-(π / 2) - 1) (π / 2 + 1)))
    (hB : ∀ τ : ℝ, 0 ≤ τ → 0 < B τ) :
    ∀ t ∈ Set.Ioo (0 : ℝ) C.T, ∀ x ∈ Work.FTS.BSIdent.Uax,
      Work.Cyl.psiField
          (fun r z => Work.FTS.MeridianDyn.merPsi (pExp a) A B (psiFire Φs E g) C r z t) x
        = Work.Cyl.psiField
          (fun r z => Work.FTS.BSIdent.merPsi a A B (psiHatP (pExp a) Φs E g) C r z t) x := by
  sorry


/-- **SB2 sub-leaf (REVIEW §3 correction)**: `∂_θ D_z V(psiP)` is bounded, from the `D_z³` bound:
`∂_θ D_zV = -D_z(αG²D_z² + 5αG D_z + 6)psiP - D_zF`. This is the θ-Lipschitz bound of `D_zV` that
the limits of `∂_z∂_θ psiP = (D_zV + tan θ·D_z psiP)/z` at the ends need. -/
theorem sb2_dthDV {αG M L Mf : ℝ} (hαG : 0 < αG) {F Ψ : Fn}
    (hsol : Work.FTS.StrongGlobal.IsBslSolPos αG F Ψ)
    (h3 : ContDiffOn ℝ 3 (Function.uncurry Ψ) Work.Construction.Qd)
    (hslot : SlotBd αG Ψ M) (hF : SrcOK F L Mf)
    (hD3 : ∃ K : ℝ, ∀ z θ, (z, θ) ∈ Work.Construction.Qd →
      ∀ j ≤ 3, |Work.Spaces.DzIter j (psiP αG Ψ) z θ| ≤ K * Work.Construction.s2 θ) :
    ∃ K' : ℝ, ∀ z θ, (z, θ) ∈ Work.Construction.Qd →
      |Work.Spaces.pth (Work.Spaces.DzIter 1 (Work.Construction.Vop (psiP αG Ψ))) z θ| ≤ K' := by
  sorry

/-- **SB2 (research medium)**: `C²` of the `U`-slot part up to `θ = 0, π/2` (all second partials have
locally uniform limits; `psiP` and `∂²_θ psiP` vanish there, `∂²_θ psiP(π/2) = (2/3)∂_θV(π/2) = 0`),
hence its odd/π-reflection is `C²` on the strip `w > 0`. Consumes the sub-leaf `sb2_dthDV`. -/
theorem sb2_c2 {αG M L Mf : ℝ} (hαG : 0 < αG) {F Ψ : Fn}
    (hsol : Work.FTS.StrongGlobal.IsBslSolPos αG F Ψ)
    (h3 : ContDiffOn ℝ 3 (Function.uncurry Ψ) Work.Construction.Qd)
    (hslot : SlotBd αG Ψ M) (hF : SrcOK F L Mf)
    (hdthDV : ∃ K' : ℝ, ∀ z θ, (z, θ) ∈ Work.Construction.Qd →
      |Work.Spaces.pth (Work.Spaces.DzIter 1 (Work.Construction.Vop (psiP αG Ψ))) z θ| ≤ K') :
    ContDiffOn ℝ 2 (Function.uncurry (oddPerS (psiP αG Ψ)))
      (Ioi 0 ×ˢ Ioo (-(π / 2) - 1) (π / 2 + 1)) := by
  sorry




/-- **SB6 (research low)**: slim rates of the reflected `U`-slot part with `lam = 4/αG`
(`αG·lam = 4 ≥ 2`): compact part from SB3/SB4, far part from SB5 (`∂_θ psiP = V + tan θ·psiP`; `V`
has zero `cos`-mean, `∂_θV` decays by the law); the `w = 0` values are junk-safe (`Φ = 0` on
`w ≤ 0`; `deriv` at `w = 0` is `0` or by the mean-value theorem). -/
theorem sb6_rates {αG M L Mf : ℝ} (hαG : 0 < αG) {F Ψ : Fn}
    (hsol : Work.FTS.StrongGlobal.IsBslSolPos αG F Ψ)
    (h3 : ContDiffOn ℝ 3 (Function.uncurry Ψ) Work.Construction.Qd)
    (hslot : SlotBd αG Ψ M) (hF : SrcOK F L Mf)
    (hnear0 : ∃ K : ℝ, ∀ z θ, (z, θ) ∈ Work.Construction.Qd → z ≤ 1 →
      |Work.Spaces.DzIter 1 (psiP αG Ψ) z θ| ≤ K * z * Work.Construction.s2 θ) :
    let Φ : Fn := fun w θ => if 0 < w then oddPerS (psiP αG Ψ) w θ else 0
    ∃ C₀ : ℝ, 0 < C₀ ∧ ∀ w θ : ℝ, 0 ≤ w → 0 ≤ θ → θ < π / 2 →
      |Φ w θ| ≤ C₀ * (π / 2 - θ) * (1 + w) ^ (-(4 / αG)) ∧
      |deriv (fun w' => Φ w' θ) w| ≤ C₀ * (π / 2 - θ) * (1 + w) ^ (-(4 / αG) - 1) ∧
      |deriv (fun θ' => Φ w θ') θ| ≤ C₀ * (1 + w) ^ (-(4 / αG)) := by
  sorry

/-! ## §3 Slice adapter and the assembly (9″) -/

/-- **Slice adapter (research-free)**: the canonical slice at `τ ≥ 0` meets the SB hypotheses:
`C³` = `psiCan_C3` (13′); `SlotBd` from RX-VP `VelPkg.dbnd` (VP-sup) at the horizon `S = τ + 1`;
`SrcOK` with `F = F_* + slice g τ` from `hreg (τ+1)` (`hvan`, `hg`, `hpz`, `hsupp`) and `hG`.
(The law `IsBslSolPos` is the first clause of `Sol`.) No growth clause (FIX-A). -/
theorem slice_inputs {a C₀ Ce Cs : ℝ} (ha : 0 < a) (ha13 : a ≤ 1 / 3) {Φs : Fn} {E : Fn →ₗ[ℝ] Fn}
    (hEll : ∀ u : Fn, Work.FTS.ClassC.ClassC (pExp a) u →
      EllPkgGo (pExp a) Ce u (E u) ∧ Work.FTS.ClassC.EllPkgK (pExp a) 6 Ce u (E u))
    (hEL : EllLimOK3 (pExp a) E) (hStar : StarPkgo2 (pExp a) Cs Φs)
    {g G : Fam} {A B : ℝ → ℝ} (hSol : Sol (pExp a) Φs E g) (hOK : DynOK' (pExp a) C₀ Φs E g)
    (hreg : ∀ S : ℝ, 0 < S → Work.FTS.RegPkgGal.RegPkg' a S A B (extG G))
    (hG : ∀ z θ τ, 0 < z → θ ∈ Work.Spaces.Iθ → 0 ≤ τ → G z θ τ = g z θ τ) :
    ∀ τ, 0 ≤ τ → ∃ M L Mf : ℝ,
      ContDiffOn ℝ 3 (Function.uncurry (slice (PsiCan Φs E g) τ)) Work.Construction.Qd ∧
      SlotBd (pExp a) (slice (PsiCan Φs E g) τ) M ∧
      SrcOK (Work.Construction.Ftau (pExp a) g τ) L Mf := by
  sorry


end Work.FTS.StreamBdryIface
end
end
-- ===== merged: Submission.Work.FTS_RegExport.RXR1.dz_tau_cont =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.FTS_RegExport.RXR1.dz_tau_cont`

If `τ ↦ g z θ τ` has the primitive `R z θ τ`, i.e. `g z θ k - g z θ 0 = ∫_0^k R z θ s ds`, and
every `z`-section `x ↦ R x θ τ` is differentiable on `(0,∞)` with a derivative bounded by `Nz`
in absolute value, then the `z`-derivatives of the `τ`-slices of `g` differ by at most `Nz * τ`.

This is "differentiation under the integral sign", with the caveat that for the Bochner integral a
non-integrable integrand contributes `0` (junk value): so the argument splits according to whether
the section `s ↦ R z θ s` is interval-integrable, `intervalIntegral.integral_undef` dispensing with
the other case.  The key structural fact is that the *set of `z` whose section is integrable is
closed*: the sections are uniformly Lipschitz in `x` (hence a pointwise limit of integrable
sections is measurable) and dominated by an integrable function.

The `z`-derivative of `∫_0^τ R x θ s ds` is then bounded by rewriting the difference over two
integrable sections as the integral of the difference and applying
`intervalIntegral.norm_integral_le_of_norm_le_const`, and using the fact that `g(·,θ,τ) - g(·,θ,0)`
is differentiable.
-/

namespace Work.FTS_RegExport.RXR1

open scoped Topology
open Filter
open MeasureTheory

set_option autoImplicit false

section Helpers

variable {R : ℝ → ℝ → ℝ → ℝ} {θ Nz τ : ℝ}

/-- **Auxiliary (pointwise Lipschitz bound).**  If every section `x ↦ R x θ s` (`s ∈ [0,1]`) is
differentiable on `(0,∞)` with derivative bounded by `Nz`, then those sections are `Nz`-Lipschitz. -/
private lemma section_lip
    (hbd : ∀ τ ∈ Set.Icc (0:ℝ) 1, ∀ z' ∈ Set.Ioi (0:ℝ),
      ∃ d : ℝ, HasDerivAt (fun z'' => R z'' θ τ) d z' ∧ |d| ≤ Nz)
    {s : ℝ} (hs : s ∈ Set.Icc (0:ℝ) 1) {x y : ℝ}
    (hx : x ∈ Set.Ioi (0:ℝ)) (hy : y ∈ Set.Ioi (0:ℝ)) :
    |R x θ s - R y θ s| ≤ Nz * |x - y| := by
  have hdiff : ∀ w ∈ Set.Ioi (0:ℝ), DifferentiableAt ℝ (fun u => R u θ s) w :=
    fun w hw => ((hbd s hs w hw).choose_spec.1).differentiableAt
  have hbound : ∀ w ∈ Set.Ioi (0:ℝ), ‖deriv (fun u => R u θ s) w‖ ≤ Nz := by
    intro w hw
    obtain ⟨d, hd, hle⟩ := hbd s hs w hw
    rw [hd.deriv]
    simpa [Real.norm_eq_abs] using hle
  have h := Convex.norm_image_sub_le_of_norm_deriv_le hdiff hbound (convex_Ioi (0:ℝ)) hy hx
  simpa [Real.norm_eq_abs] using h

/-- **Auxiliary (the integrability locus is open in its complement).**  If the section at `z' > 0`
is *not* interval-integrable on `[0,τ]`, then neither is the section at any nearby positive point:
otherwise a sequence of integrable sections would converge to the non-integrable one, contradicting
`Work.FTS_RegExport.RXR1Aux.intervalIntegrable_of_tendsto`. -/
private lemma bad_nhds (hNz : 0 ≤ Nz)
    (hbd : ∀ τ ∈ Set.Icc (0:ℝ) 1, ∀ z' ∈ Set.Ioi (0:ℝ),
      ∃ d : ℝ, HasDerivAt (fun z'' => R z'' θ τ) d z' ∧ |d| ≤ Nz)
    (hτ0 : 0 ≤ τ) (hτ1 : τ ≤ 1) {z' : ℝ} (hz' : z' ∈ Set.Ioi (0:ℝ))
    (hbad : ¬ IntervalIntegrable (fun s => R z' θ s) volume (0:ℝ) τ) :
    ∃ ε > 0, ∀ x ∈ Set.Ioi (0:ℝ), |x - z'| < ε →
      ¬ IntervalIntegrable (fun s => R x θ s) volume (0:ℝ) τ := by
  by_contra hcon
  push_neg at hcon
  have hsel : ∀ n : ℕ, ∃ x : ℝ, x ∈ Set.Ioi (0:ℝ) ∧ |x - z'| < 1 / ((n : ℝ) + 1) ∧
      IntervalIntegrable (fun s => R x θ s) volume (0:ℝ) τ :=
    fun n => hcon (1 / ((n : ℝ) + 1)) (by positivity)
  choose u hu using hsel
  have htu : Filter.Tendsto u Filter.atTop (𝓝 z') := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    simp only [Real.norm_eq_abs]
    refine squeeze_zero (fun n => abs_nonneg _) (fun n => le_of_lt (hu n).2.1) ?_
    simpa using (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  exact hbad (Work.FTS_RegExport.RXR1Aux.intervalIntegrable_of_tendsto
    (R := fun x s => R x θ s) hNz hτ0 hτ1
    (fun s hs x hx y hy => section_lip hbd hs hx hy) hz' htu (fun n => (hu n).1)
    (fun n => (hu n).2.2))

end Helpers

theorem dz_tau_cont {g R : ℝ → ℝ → ℝ → ℝ} {θ Nz z : ℝ}
    (hNz : 0 ≤ Nz)
    (hFTC : ∀ z' ∈ Set.Ioi (0:ℝ), ∀ k ∈ Set.Icc (0:ℝ) 1,
      g z' θ k - g z' θ 0 = ∫ s in (0:ℝ)..k, R z' θ s)
    (hbd : ∀ τ ∈ Set.Icc (0:ℝ) 1, ∀ z' ∈ Set.Ioi (0:ℝ),
      ∃ d : ℝ, HasDerivAt (fun z'' => R z'' θ τ) d z' ∧ |d| ≤ Nz)
    (hd0 : ∀ z' ∈ Set.Ioi (0:ℝ), HasDerivAt (fun z'' => g z'' θ 0)
      (deriv (fun z'' => g z'' θ 0) z') z')
    (hdτ : ∀ τ ∈ Set.Ioc (0:ℝ) 1, ∀ z' ∈ Set.Ioi (0:ℝ), HasDerivAt (fun z'' => g z'' θ τ)
      (deriv (fun z'' => g z'' θ τ) z') z') :
    ∀ z' ∈ Set.Ioi (0:ℝ), ∀ τ ∈ Set.Icc (0:ℝ) 1,
      |deriv (fun z'' => g z'' θ τ) z' - deriv (fun z'' => g z'' θ 0) z'| ≤ Nz * τ := by
  intro z' hz' τ hτ
  obtain ⟨hτ0, hτ1⟩ := hτ
  rcases eq_or_lt_of_le hτ0 with hτeq | hτpos
  · subst hτeq
    simp
  have hC0 : 0 ≤ Nz * τ := mul_nonneg hNz hτ0
  -- the difference of the two slices is the integral of `R`
  set I : ℝ → ℝ := fun x => ∫ s in (0:ℝ)..τ, R x θ s with hIdef
  have hiff : I =ᶠ[𝓝 z'] ((fun x => g x θ τ) - (fun x => g x θ 0)) := by
    filter_upwards [isOpen_Ioi.mem_nhds hz'] with x hx
    have h := hFTC x hx τ ⟨hτ0, hτ1⟩
    rw [hIdef]
    simp only [Pi.sub_apply]
    exact h.symm
  have hd_sub : HasDerivAt ((fun x => g x θ τ) - (fun x => g x θ 0))
      (deriv (fun x => g x θ τ) z' - deriv (fun x => g x θ 0) z') z' := by
    have h1 : HasDerivAt (fun x => g x θ τ) (deriv (fun x => g x θ τ) z') z' :=
      hdτ τ ⟨hτpos, hτ1⟩ z' hz'
    have h0 : HasDerivAt (fun x => g x θ 0) (deriv (fun x => g x θ 0) z') z' := hd0 z' hz'
    exact h1.sub h0
  have hd_I : HasDerivAt I (deriv (fun x => g x θ τ) z' - deriv (fun x => g x θ 0) z') z' :=
    hd_sub.congr_of_eventuallyEq hiff
  have hset : Set.uIoc (0:ℝ) τ ⊆ Set.Icc (0:ℝ) 1 := by
    intro s hs
    have h1 : s ∈ Set.uIcc 0 τ := Set.uIoc_subset_uIcc hs
    rw [Set.uIcc_of_le hτ0] at h1
    exact ⟨h1.1, le_trans h1.2 hτ1⟩
  -- the integral of a non-integrable section is `0`
  have hzero : ∀ x, ¬ IntervalIntegrable (fun s => R x θ s) volume (0:ℝ) τ → I x = 0 := by
    intro x hx
    rw [hIdef]
    simp only
    exact intervalIntegral.integral_undef hx
  -- Lipschitz bound between two integrable sections
  have hlip : ∀ x y : ℝ, x ∈ Set.Ioi (0:ℝ) → y ∈ Set.Ioi (0:ℝ) →
      IntervalIntegrable (fun s => R x θ s) volume (0:ℝ) τ →
      IntervalIntegrable (fun s => R y θ s) volume (0:ℝ) τ →
      ‖I x - I y‖ ≤ Nz * τ * ‖x - y‖ := by
    intro x y hx hy hgx hgy
    have hsub := intervalIntegral.integral_sub hgx hgy
    have hIxy : I x - I y = ∫ s in (0:ℝ)..τ, (R x θ s - R y θ s) := by
      rw [hIdef]
      simp only
      exact hsub.symm
    rw [hIxy]
    have hb : ∀ s ∈ Set.uIoc (0:ℝ) τ, ‖R x θ s - R y θ s‖ ≤ Nz * |x - y| := by
      intro s hs
      have hs1 : s ∈ Set.Icc (0:ℝ) 1 := hset hs
      have h := section_lip hbd hs1 hx hy
      simpa [Real.norm_eq_abs] using h
    have hmain := intervalIntegral.norm_integral_le_of_norm_le_const (a := (0:ℝ)) (b := τ)
      (C := Nz * |x - y|) (f := fun s => R x θ s - R y θ s) hb
    calc ‖∫ s in (0:ℝ)..τ, (R x θ s - R y θ s)‖ ≤ Nz * |x - y| * |τ - 0| := hmain
      _ = Nz * τ * ‖x - y‖ := by rw [sub_zero, abs_of_pos hτpos, Real.norm_eq_abs]; ring
  -- the eventual Lipschitz bound at `z'`
  have hEv : ∀ᶠ x in 𝓝 z', ‖I x - I z'‖ ≤ (Nz * τ) * ‖x - z'‖ := by
    by_cases hgz : IntervalIntegrable (fun s => R z' θ s) volume (0:ℝ) τ
    · by_cases hIz : I z' = 0
      · -- `z'` is integrable, but its integral vanishes
        filter_upwards [isOpen_Ioi.mem_nhds hz'] with x hx
        by_cases hgx : IntervalIntegrable (fun s => R x θ s) volume (0:ℝ) τ
        · exact hlip x z' hx hz' hgx hgz
        · rw [hzero x hgx, hIz]
          simp only [sub_self, norm_zero]
          exact mul_nonneg hC0 (norm_nonneg _)
      · -- `z'` is integrable with nonzero integral: nearby points are integrable too
        have hev : ∀ᶠ x in 𝓝 z', I x ≠ 0 := hd_I.continuousAt.eventually_ne hIz
        filter_upwards [hev, isOpen_Ioi.mem_nhds hz'] with x hxne hx
        have hgx : IntervalIntegrable (fun s => R x θ s) volume (0:ℝ) τ := by
          by_contra hxb
          exact hxne (hzero x hxb)
        exact hlip x z' hx hz' hgx hgz
    · -- `z'` is not integrable: a whole neighbourhood of `z'` consists of non-integrable points
      have hIz : I z' = 0 := hzero z' hgz
      obtain ⟨ε, hεpos, hεb⟩ := bad_nhds hNz hbd hτ0 hτ1 hz' hgz
      have hev : ∀ᶠ x in 𝓝 z', ¬ IntervalIntegrable (fun s => R x θ s) volume (0:ℝ) τ := by
        rw [Metric.eventually_nhds_iff]
        refine ⟨min ε z', lt_min hεpos hz', ?_⟩
        intro x hx
        rw [Real.dist_eq] at hx
        have hxz : |x - z'| < ε := lt_of_lt_of_le hx (min_le_left _ _)
        have hxle : |x - z'| < z' := lt_of_lt_of_le hx (min_le_right _ _)
        have hxpos : 0 < x := by
          have h2 := (abs_lt.mp hxle).1
          linarith
        exact hεb x hxpos hxz
      filter_upwards [hev] with x hxb
      rw [hzero x hxb, hIz]
      simp only [sub_self, norm_zero]
      exact mul_nonneg hC0 (norm_nonneg _)
  have hLip := hd_I.le_of_lip' hC0 hEv
  simpa [Real.norm_eq_abs] using hLip

end Work.FTS_RegExport.RXR1
end
-- ===== merged: Submission.Work.FTS_RegExport.RXR1.oneSided_expansion =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

section OseAux

open scoped Topology
open Filter

/-- The `ε`-`δ` content of `HasDerivAt` in the shifted variable `a = x' - x`. -/
private lemma hasDerivAt_shift {f : ℝ → ℝ} {f' x : ℝ} (h : HasDerivAt f f' x) {c : ℝ}
    (hc : 0 < c) :
    ∀ᶠ a in 𝓝 (0 : ℝ), ‖f (x + a) - f x - f' * a‖ ≤ c * |a| := by
  have hlit : ∀ᶠ y in 𝓝 x, ‖f y - f x - (y - x) • f'‖ ≤ c * ‖y - x‖ := (h.isLittleO).bound hc
  have htend : Filter.Tendsto (fun a : ℝ => x + a) (𝓝 0) (𝓝 x) := by
    simpa using (tendsto_const_nhds : Filter.Tendsto (fun _ : ℝ => x) (𝓝 (0 : ℝ)) (𝓝 x)).add
      (tendsto_id : Filter.Tendsto (fun a : ℝ => a) (𝓝 (0 : ℝ)) (𝓝 (0 : ℝ)))
  filter_upwards [htend.eventually hlit] with a ha
  have h1 : x + a - x = a := by ring
  have h2 : a * f' = f' * a := mul_comm _ _
  rw [h1] at ha
  simpa only [smul_eq_mul, Real.norm_eq_abs, h2] using ha

/-- For `0 ≤ N` there are arbitrarily small positive `δ` with `N · δ ^ α ≤ c` (`c > 0`,
`α > 0`). -/
private lemma exists_rpow_small {N α : ℝ} (hN : 0 ≤ N) (hα : 0 < α) {c : ℝ} (hc : 0 < c) :
    ∃ δ > 0, N * δ ^ α ≤ c := by
  have hN1 : (0 : ℝ) < N + 1 := by linarith
  refine ⟨(c / (N + 1)) ^ (1 / α), Real.rpow_pos_of_pos (by positivity) _, ?_⟩
  rw [← Real.rpow_mul (le_of_lt (by positivity : (0 : ℝ) < c / (N + 1))), one_div,
    inv_mul_cancel₀ (ne_of_gt hα), Real.rpow_one]
  rw [← mul_div_assoc, div_le_iff₀ hN1]
  nlinarith

/-- The `τ`-slices of a `Jet` are continuous on `[0,1]`. -/
private lemma jet_slice_continuousOn {h : ℝ → ℝ → ℝ → ℝ} {α N : ℝ}
    (H : Work.FTS.Regularity.Jet α 1 N h) (hα : 0 < α) {z θ : ℝ} (hz : 0 ≤ z)
    (hθ : θ ∈ Work.Spaces.Iθ) :
    ContinuousOn (fun s => h z θ s) (Set.Icc 0 1) := by
  have hN : 0 ≤ N := H.1
  intro s₀ hs₀
  rw [Metric.continuousWithinAt_iff]
  intro ε hε
  obtain ⟨t, htpos, htle⟩ := exists_rpow_small hN hα (c := ε / 2) (by linarith)
  refine ⟨t, htpos, ?_⟩
  intro s' hs' hd
  have hb := H.2.2 z z θ θ s' s₀ hz hz hθ hθ hs' hs₀
  simp only [sub_self, abs_zero, zero_add] at hb
  have hds : dist s' s₀ = |s' - s₀| := Real.dist_eq _ _
  rw [hds] at hd
  have h1 : |s' - s₀| ^ α ≤ t ^ α := Real.rpow_le_rpow (abs_nonneg _) hd.le hα.le
  have h2 : dist (h z θ s') (h z θ s₀) = |h z θ s' - h z θ s₀| := Real.dist_eq _ _
  rw [h2]
  calc |h z θ s' - h z θ s₀| ≤ N * |s' - s₀| ^ α := hb
    _ ≤ N * t ^ α := mul_le_mul_of_nonneg_left h1 hN
    _ ≤ ε / 2 := htle
    _ < ε := by linarith

end OseAux

namespace Work.FTS_RegExport.RXR1

theorem oneSided_expansion {g R : ℝ → ℝ → ℝ → ℝ} {θ Nc α z : ℝ} (hα : 0 < α) (hNc : 0 ≤ Nc)
    (hθ : θ ∈ Work.Spaces.Iθ) (hz : 0 < z)
    (hFTC : ∀ z' ∈ Set.Ioi (0:ℝ), ∀ k ∈ Set.Icc (0:ℝ) 1,
      g z' θ k - g z' θ 0 = ∫ s in (0:ℝ)..k, R z' θ s)
    (hjet : Work.FTS.Regularity.Jet α 1 Nc (fun z θ τ => R z θ τ))
    (hder0 : HasDerivAt (fun z' => g z' θ 0) (deriv (fun z' => g z' θ 0) z) z) :
    ∀ ε > 0, ∃ δ > 0, ∀ y : ℝ × ℝ, ‖y - (z, (0:ℝ))‖ < δ → 0 ≤ y.2 →
      ‖g y.1 θ y.2 - g z θ 0 - deriv (fun z' => g z' θ 0) z * (y.1 - z) - R z θ 0 * y.2‖
        ≤ ε * ‖y - (z, (0:ℝ))‖ := by
  intro ε hε
  set D : ℝ := deriv (fun z' => g z' θ 0) z with hD
  have hε2 : 0 < ε / 2 := by linarith
  -- (1) the one-dimensional differentiability in `z`
  obtain ⟨δ₁, hδ₁pos, hδ₁⟩ : ∃ δ > 0, ∀ a : ℝ, |a| < δ →
      ‖g (z + a) θ 0 - g z θ 0 - D * a‖ ≤ (ε / 2) * |a| := by
    have h := hasDerivAt_shift hder0 hε2
    rw [Metric.eventually_nhds_iff] at h
    obtain ⟨δ, hδ, hδ'⟩ := h
    exact ⟨δ, hδ, fun a ha => hδ' (by simpa [Real.dist_eq] using ha)⟩
  -- (2) the smallness threshold for the `τ`-integral
  obtain ⟨δ₂, hδ₂pos, hδ₂⟩ : ∃ δ > 0, ∀ r : ℝ, 0 ≤ r → r < δ → Nc * (2 * r) ^ α ≤ ε / 2 := by
    obtain ⟨t, htpos, htle⟩ := exists_rpow_small hNc hα hε2
    refine ⟨t / 2, by linarith, fun r hr hrt => ?_⟩
    have h2r : 2 * r < t := by linarith
    have hle : (2 * r) ^ α ≤ t ^ α := Real.rpow_le_rpow (by linarith) h2r.le hα.le
    calc Nc * (2 * r) ^ α ≤ Nc * t ^ α := mul_le_mul_of_nonneg_left hle hNc
      _ ≤ ε / 2 := htle
  have hδz : 0 < min δ₁ (min δ₂ (min (z / 2) (1 / 2))) :=
    lt_min hδ₁pos (lt_min hδ₂pos (lt_min (by linarith) (by norm_num)))
  refine ⟨min δ₁ (min δ₂ (min (z / 2) (1 / 2))), hδz, ?_⟩
  rintro ⟨y1, y2⟩ hy hy2
  -- the distance is the sup-distance
  have hdist : ‖(y1, y2) - (z, (0 : ℝ))‖ = max |y1 - z| |y2| := by
    rw [← dist_eq_norm, Prod.dist_eq, Real.dist_eq, Real.dist_eq, sub_zero]
  have hδ₁' : min δ₁ (min δ₂ (min (z / 2) (1 / 2))) ≤ δ₁ := min_le_left _ _
  have hδ₂' : min δ₁ (min δ₂ (min (z / 2) (1 / 2))) ≤ δ₂ :=
    le_trans (min_le_right _ _) (min_le_left _ _)
  have hδz' : min δ₁ (min δ₂ (min (z / 2) (1 / 2))) ≤ z / 2 :=
    le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_left _ _))
  have hδu' : min δ₁ (min δ₂ (min (z / 2) (1 / 2))) ≤ 1 / 2 :=
    le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_right _ _))
  have habs1 : |y1 - z| ≤ ‖(y1, y2) - (z, (0 : ℝ))‖ := by
    rw [hdist]; exact le_max_left _ _
  have habs2 : |y2| ≤ ‖(y1, y2) - (z, (0 : ℝ))‖ := by
    rw [hdist]; exact le_max_right _ _
  have hy1z : |y1 - z| < δ₁ := lt_of_lt_of_le (lt_of_le_of_lt habs1 hy) hδ₁'
  have hr₂ : ‖(y1, y2) - (z, (0 : ℝ))‖ < δ₂ := lt_of_lt_of_le hy hδ₂'
  have hy1pos : 0 < y1 := by
    have h : |y1 - z| < z :=
      lt_of_lt_of_le (lt_of_le_of_lt habs1 hy) (by linarith [hδz'])
    have h' : -z < y1 - z := (abs_lt.mp h).1
    linarith
  have hy1nn : 0 ≤ y1 := hy1pos.le
  have hy2le1 : y2 ≤ 1 := by
    have h : |y2| < 1 := lt_of_lt_of_le (lt_of_le_of_lt habs2 hy) (by linarith [hδu'])
    exact le_of_lt (lt_of_le_of_lt (le_abs_self y2) h)
  -- the `z`-part
  have hzA : ‖g y1 θ 0 - g z θ 0 - D * (y1 - z)‖
      ≤ (ε / 2) * ‖(y1, y2) - (z, (0 : ℝ))‖ := by
    have h := hδ₁ (y1 - z) hy1z
    have h2 : z + (y1 - z) = y1 := by ring
    rw [h2] at h
    calc ‖g y1 θ 0 - g z θ 0 - D * (y1 - z)‖ ≤ (ε / 2) * |y1 - z| := h
      _ ≤ (ε / 2) * ‖(y1, y2) - (z, (0 : ℝ))‖ :=
          mul_le_mul_of_nonneg_left habs1 (by linarith)
  -- the `τ`-part
  have hkB : ‖g y1 θ y2 - g y1 θ 0 - R z θ 0 * y2‖
      ≤ (ε / 2) * ‖(y1, y2) - (z, (0 : ℝ))‖ := by
    have hFTC' := hFTC y1 hy1pos y2 ⟨hy2, hy2le1⟩
    have hcont : ContinuousOn (fun s => R y1 θ s) (Set.Icc 0 1) :=
      jet_slice_continuousOn hjet hα hy1nn hθ
    have hInt : IntervalIntegrable (fun s => R y1 θ s) MeasureTheory.volume 0 y2 :=
      ContinuousOn.intervalIntegrable_of_Icc (u := fun s => R y1 θ s) hy2
        (hcont.mono (Set.Icc_subset_Icc le_rfl hy2le1))
    have hid : (∫ s in (0 : ℝ)..y2, R y1 θ s) - R z θ 0 * y2
        = ∫ s in (0 : ℝ)..y2, (R y1 θ s - R z θ 0) := by
      rw [intervalIntegral.integral_sub hInt intervalIntegrable_const,
        intervalIntegral.integral_const]
      rw [sub_zero, smul_eq_mul]
      ring
    rw [hFTC', hid]
    have hC : ∀ s ∈ Set.uIoc (0 : ℝ) y2,
        ‖R y1 θ s - R z θ 0‖ ≤ Nc * (2 * ‖(y1, y2) - (z, (0 : ℝ))‖) ^ α := by
      intro s hs
      rw [Set.uIoc_of_le hy2] at hs
      have hs1 : s ∈ Set.Icc (0 : ℝ) 1 := ⟨hs.1.le, le_trans hs.2 hy2le1⟩
      have h0 : (0 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := ⟨le_rfl, by norm_num⟩
      have hb := hjet.2.2 y1 z θ θ s 0 hy1nn hz.le hθ hθ hs1 h0
      simp only [sub_self, abs_zero, add_zero, sub_zero, abs_of_pos hs.1] at hb
      have hle : |y1 - z| + s ≤ 2 * ‖(y1, y2) - (z, (0 : ℝ))‖ := by
        have hs : s ≤ ‖(y1, y2) - (z, (0 : ℝ))‖ :=
          le_trans hs.2 (le_trans (le_abs_self y2) habs2)
        linarith [habs1]
      have hrpow : (|y1 - z| + s) ^ α ≤ (2 * ‖(y1, y2) - (z, (0 : ℝ))‖) ^ α :=
        Real.rpow_le_rpow (by linarith [abs_nonneg (y1 - z), hs.1]) hle hα.le
      calc ‖R y1 θ s - R z θ 0‖ = |R y1 θ s - R z θ 0| := Real.norm_eq_abs _
        _ ≤ Nc * (|y1 - z| + s) ^ α := hb
        _ ≤ Nc * (2 * ‖(y1, y2) - (z, (0 : ℝ))‖) ^ α :=
            mul_le_mul_of_nonneg_left hrpow hNc
    have hnorm := intervalIntegral.norm_integral_le_of_norm_le_const hC
    calc ‖∫ s in (0 : ℝ)..y2, (R y1 θ s - R z θ 0)‖
        ≤ (Nc * (2 * ‖(y1, y2) - (z, (0 : ℝ))‖) ^ α) * |y2 - 0| := hnorm
      _ = (Nc * (2 * ‖(y1, y2) - (z, (0 : ℝ))‖) ^ α) * y2 := by
          rw [sub_zero, abs_of_nonneg hy2]
      _ ≤ (Nc * (2 * ‖(y1, y2) - (z, (0 : ℝ))‖) ^ α) * ‖(y1, y2) - (z, (0 : ℝ))‖ :=
          mul_le_mul_of_nonneg_left (le_trans (le_abs_self y2) habs2) (by positivity)
      _ ≤ (ε / 2) * ‖(y1, y2) - (z, (0 : ℝ))‖ :=
          mul_le_mul_of_nonneg_right (hδ₂ _ (norm_nonneg _) hr₂) (norm_nonneg _)
  have hdec : g y1 θ y2 - g z θ 0 - D * (y1 - z) - R z θ 0 * y2
      = (g y1 θ 0 - g z θ 0 - D * (y1 - z)) + (g y1 θ y2 - g y1 θ 0 - R z θ 0 * y2) := by
    ring
  calc ‖g y1 θ y2 - g z θ 0 - D * (y1 - z) - R z θ 0 * y2‖
      = ‖(g y1 θ 0 - g z θ 0 - D * (y1 - z))
          + (g y1 θ y2 - g y1 θ 0 - R z θ 0 * y2)‖ := by rw [hdec]
    _ ≤ ‖g y1 θ 0 - g z θ 0 - D * (y1 - z)‖
        + ‖g y1 θ y2 - g y1 θ 0 - R z θ 0 * y2‖ := norm_add_le _ _
    _ ≤ (ε / 2) * ‖(y1, y2) - (z, (0 : ℝ))‖ + (ε / 2) * ‖(y1, y2) - (z, (0 : ℝ))‖ :=
        add_le_add hzA hkB
    _ = ε * ‖(y1, y2) - (z, (0 : ℝ))‖ := by ring

end Work.FTS_RegExport.RXR1
end
end
-- ===== merged: Submission.Work.FTS_RegExport.RXR5L.Auxiliary.Tlim_aux =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS_RegExport.RXR5L.Auxiliary

set_option autoImplicit false

local notation "Rwt" => Work.FTS_RegExport.RXT.L12Iter.Rwt
local notation "Dth" => Work.Spaces.Dth
local notation "L12" => Work.Construction.L12

/-- `(z,θ) ↦ 3·D_θ F(z,θ)/(1+z)` is continuous on the open quadrant as soon as `F` is `C⁴`
there: `D_θ F` is `C³` and the radial factor `3/(1+z)` is smooth and nonvanishing on `z > 0`. -/
theorem continuousOn_uncurry_three_div_Dth {F : ℝ → ℝ → ℝ}
    (hF : ContDiffOn ℝ 4 (Function.uncurry F) Work.FTS.EllipticEst.Q0) :
    ContinuousOn (Function.uncurry (fun z θ => 3 * Dth F z θ / (1 + z)))
      Work.FTS.EllipticEst.Q0 := by
  have h3 : ContDiffOn ℝ 3 (Function.uncurry (Dth F)) Work.FTS.EllipticEst.Q0 :=
    Work.FTS.StrongEps.contDiffOn_uncurry_Dth_fin (n := 3) Work.FTS.EllipticEst.isOpen_Q0 hF
  have hfac : ContinuousOn (fun p : ℝ × ℝ => 3 / (1 + p.1)) Work.FTS.EllipticEst.Q0 := by
    refine ContinuousOn.div continuousOn_const
      (continuousOn_const.add continuous_fst.continuousOn) ?_
    intro p hp
    have hp1 : (0 : ℝ) < p.1 := (Work.FTS.EllipticEst.mem_Q0.mp hp).1
    positivity
  have hmul : ContinuousOn (fun p : ℝ × ℝ =>
      (3 / (1 + p.1)) * Function.uncurry (Dth F) p) Work.FTS.EllipticEst.Q0 :=
    hfac.mul h3.continuousOn
  refine hmul.congr (fun p hp => ?_)
  simp only [Function.uncurry]
  ring

/-- **The assembly.**  Given the pointwise inputs `hsub` (linearity of `L₁₂` in the profile) and
`hbnd` (bound and `τ`-modulus of `D_θ(slice g ·)`), the transport zero-mode of the family `g` is
uniformly bounded and Lipschitz in the fake time on `[0,S]`. -/
theorem Tlim_bounds_from_aux {α C₀ : ℝ} {Φs : Work.FTS.Galerkin.Fn}
    {E : Work.FTS.Galerkin.Fn →ₗ[ℝ] Work.FTS.Galerkin.Fn} {g : Work.FTS.Galerkin.Fam}
    (hOK : Work.FTS.FinalV2.DynOK' (Work.FTS.Regularity.pExp α) C₀ Φs E g)
    {S : ℝ}
    (hsub : ∀ {a b : ℝ → ℝ → ℝ} {A B : ℝ}, 0 ≤ A → 0 ≤ B →
      ContinuousOn (Function.uncurry a) Work.FTS.EllipticEst.Q0 →
      ContinuousOn (Function.uncurry b) Work.FTS.EllipticEst.Q0 →
      (∀ s θ : ℝ, 0 < s → θ ∈ Set.Ioo 0 (Real.pi / 2) →
        |a s θ| ≤ A * (Rwt s / (1 + s))) →
      (∀ s θ : ℝ, 0 < s → θ ∈ Set.Ioo 0 (Real.pi / 2) →
        |b s θ| ≤ B * (Rwt s / (1 + s))) →
      L12 a 0 - L12 b 0 = L12 (fun z θ => a z θ - b z θ) 0)
    (hbnd : ∃ C1 : ℝ, 0 ≤ C1 ∧
      (∀ τ ∈ Set.Icc (0 : ℝ) S, ∀ z θ : ℝ, 0 < z → θ ∈ Work.Spaces.Iθ →
        |Dth (Work.FTS.Galerkin.slice g τ) z θ| ≤ C1 * Rwt z) ∧
      (∀ τ ∈ Set.Icc (0 : ℝ) S, ∀ τ' ∈ Set.Icc (0 : ℝ) S, ∀ z θ : ℝ, 0 < z →
        θ ∈ Work.Spaces.Iθ →
        |Dth (Work.FTS.Galerkin.slice g τ) z θ - Dth (Work.FTS.Galerkin.slice g τ') z θ|
          ≤ C1 * Rwt z * |τ - τ'|)) :
    ∃ M : ℝ, 0 ≤ M ∧
      (∀ τ ∈ Set.Icc (0:ℝ) S,
        |L12 (fun z θ => 3 * Dth (Work.FTS.Galerkin.slice g τ) z θ / (1 + z)) 0| ≤ M) ∧
      (∀ τ ∈ Set.Icc (0:ℝ) S, ∀ τ' ∈ Set.Icc (0:ℝ) S,
        |L12 (fun z θ => 3 * Dth (Work.FTS.Galerkin.slice g τ) z θ / (1 + z)) 0
          - L12 (fun z θ => 3 * Dth (Work.FTS.Galerkin.slice g τ') z θ / (1 + z)) 0|
          ≤ M * |τ - τ'|) := by
  obtain ⟨hDyn, _hLim⟩ := hOK
  obtain ⟨C1, hC1, hbd, hlip⟩ := hbnd
  -- the data `3·D_θ(slice g τ)/(1+z)` are continuous on the open quadrant
  have hcont : ∀ τ ∈ Set.Icc (0 : ℝ) S,
      ContinuousOn (Function.uncurry
        (fun z θ => 3 * Dth (Work.FTS.Galerkin.slice g τ) z θ / (1 + z)))
        Work.FTS.EllipticEst.Q0 := fun τ hτ =>
    continuousOn_uncurry_three_div_Dth (hDyn.1.c4 τ hτ.1)
  -- ## the two pointwise bounds for the data
  -- (a) on the closed angular interval, in the form required by `abs_L12_zero_le_of_pointwise`
  have hbddI : ∀ τ ∈ Set.Icc (0 : ℝ) S, ∀ z θ : ℝ, 0 < z → θ ∈ Work.Spaces.Iθ →
      |3 * Dth (Work.FTS.Galerkin.slice g τ) z θ / (1 + z)| ≤ (3 * C1) * Rwt z := by
    intro τ hτ z θ hz hθ
    have h1 := hbd τ hτ z θ hz hθ
    have hR : 0 ≤ Rwt z := Work.FTS_RegExport.RXT.L12Iter.Rwt_nonneg hz.le
    have hz1 : (0 : ℝ) < 1 + z := by linarith
    have h2 : |3 * Dth (Work.FTS.Galerkin.slice g τ) z θ / (1 + z)|
        = 3 * |Dth (Work.FTS.Galerkin.slice g τ) z θ| / (1 + z) := by
      rw [abs_div, abs_mul, abs_of_pos hz1, abs_of_pos (by norm_num : (0 : ℝ) < 3)]
    rw [h2]
    have hA : 0 ≤ 3 * (C1 * Rwt z) := mul_nonneg (by norm_num) (mul_nonneg hC1 hR)
    calc 3 * |Dth (Work.FTS.Galerkin.slice g τ) z θ| / (1 + z)
        ≤ 3 * (C1 * Rwt z) / (1 + z) := by gcongr
      _ ≤ 3 * (C1 * Rwt z) := by
          rw [div_le_iff₀ hz1]
          nlinarith [mul_nonneg hA hz.le]
      _ = (3 * C1) * Rwt z := by ring
  -- (b) on the open angular interval, in the form required by `hsub`
  have hbdd : ∀ τ ∈ Set.Icc (0 : ℝ) S, ∀ s θ : ℝ, 0 < s →
      θ ∈ Set.Ioo 0 (Real.pi / 2) →
      |3 * Dth (Work.FTS.Galerkin.slice g τ) s θ / (1 + s)|
        ≤ (3 * C1) * (Rwt s / (1 + s)) := by
    intro τ hτ s θ hs hθ
    have h1 := hbd τ hτ s θ hs ⟨hθ.1.le, hθ.2.le⟩
    have hs1 : (0 : ℝ) < 1 + s := by linarith
    have h2 : |3 * Dth (Work.FTS.Galerkin.slice g τ) s θ / (1 + s)|
        = 3 * |Dth (Work.FTS.Galerkin.slice g τ) s θ| / (1 + s) := by
      rw [abs_div, abs_mul, abs_of_pos hs1, abs_of_pos (by norm_num : (0 : ℝ) < 3)]
    rw [h2]
    calc 3 * |Dth (Work.FTS.Galerkin.slice g τ) s θ| / (1 + s)
        ≤ 3 * (C1 * Rwt s) / (1 + s) := by gcongr
      _ = (3 * C1) * (Rwt s / (1 + s)) := by ring
  refine ⟨3 * Real.pi * (3 * C1), by positivity, ?_, ?_⟩
  · -- ## the uniform bound
    intro τ hτ
    have hM0 : (0 : ℝ) ≤ 3 * C1 := by linarith
    have hb := Work.FTS_RegExport.RXR5L.aux.abs_L12_zero_le_of_pointwise
      (f := fun z θ => 3 * Dth (Work.FTS.Galerkin.slice g τ) z θ / (1 + z))
      (M := 3 * C1) hM0 (hbddI τ hτ)
    refine le_trans hb (le_of_eq ?_)
    ring
  · -- ## the `τ`-modulus
    intro τ hτ τ' hτ'
    have hM0 : (0 : ℝ) ≤ 3 * C1 := by linarith
    have hsub' := hsub
      (a := fun z θ => 3 * Dth (Work.FTS.Galerkin.slice g τ) z θ / (1 + z))
      (b := fun z θ => 3 * Dth (Work.FTS.Galerkin.slice g τ') z θ / (1 + z))
      (A := 3 * C1) (B := 3 * C1) hM0 hM0 (hcont τ hτ) (hcont τ' hτ')
      (hbdd τ hτ) (hbdd τ' hτ')
    rw [hsub']
    have hb := Work.FTS_RegExport.RXR5L.aux.abs_L12_zero_le_of_pointwise
      (f := fun z θ => 3 * Dth (Work.FTS.Galerkin.slice g τ) z θ / (1 + z)
        - 3 * Dth (Work.FTS.Galerkin.slice g τ') z θ / (1 + z))
      (M := 3 * C1 * |τ - τ'|) (by positivity) ?_
    · refine le_trans hb (le_of_eq ?_)
      ring
    · intro z θ hz hθ
      have hR : 0 ≤ Rwt z := Work.FTS_RegExport.RXT.L12Iter.Rwt_nonneg hz.le
      have hz1 : (0 : ℝ) < 1 + z := by linarith
      have h2 : |3 * Dth (Work.FTS.Galerkin.slice g τ) z θ / (1 + z)
            - 3 * Dth (Work.FTS.Galerkin.slice g τ') z θ / (1 + z)|
          = 3 * |Dth (Work.FTS.Galerkin.slice g τ) z θ
              - Dth (Work.FTS.Galerkin.slice g τ') z θ| / (1 + z) := by
        rw [show 3 * Dth (Work.FTS.Galerkin.slice g τ) z θ / (1 + z)
              - 3 * Dth (Work.FTS.Galerkin.slice g τ') z θ / (1 + z)
            = 3 * (Dth (Work.FTS.Galerkin.slice g τ) z θ
              - Dth (Work.FTS.Galerkin.slice g τ') z θ) / (1 + z) from by ring]
        rw [abs_div, abs_mul, abs_of_pos hz1, abs_of_pos (by norm_num : (0 : ℝ) < 3)]
      rw [h2]
      have hd := hlip τ hτ τ' hτ' z θ hz hθ
      have hA : 0 ≤ C1 * Rwt z * |τ - τ'| :=
        mul_nonneg (mul_nonneg hC1 hR) (abs_nonneg _)
      have hB : 0 ≤ 3 * (C1 * Rwt z * |τ - τ'|) := mul_nonneg (by norm_num) hA
      rw [div_le_iff₀ hz1]
      calc 3 * |Dth (Work.FTS.Galerkin.slice g τ) z θ
              - Dth (Work.FTS.Galerkin.slice g τ') z θ|
          ≤ 3 * (C1 * Rwt z * |τ - τ'|) := by linarith
        _ ≤ 3 * (C1 * Rwt z * |τ - τ'|) * (1 + z) := by
            nlinarith [mul_nonneg hB hz.le]
        _ = (3 * C1 * |τ - τ'|) * Rwt z * (1 + z) := by ring

end Work.FTS_RegExport.RXR5L.Auxiliary
end
end
