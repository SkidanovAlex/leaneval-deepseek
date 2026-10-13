import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Submission.Work.FTS.FinalV2.Defs
import Submission.Work.FTS.BSIdent.hid_of_corrected
import Submission.Work.FTS.BSIdent.Weyl.Levels.continuous_axisLevel
import Submission.Work.FTS_BSIdentP.Producers

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

/-- **BSIdent-P1 (mechanical)**: `hid_of_corrected` with `RegPkg'` (physVort facts from
`FireFix.Prime.*`; clock positivity from `hreg.hA/hB`) and the decay constants chosen per `t`
(`merPsi_corrected_bundle` is per-`t`). -/
theorem hid_of_corrected' {α : ℝ≥0} {A B : ℝ → ℝ} {g : Fam} {C : PhysClock} {Φ : Fam}
    (hreg : ∀ S : ℝ, 0 < S → Work.FTS.RegPkgGal.RegPkg' (α : ℝ) S A B g)
    (hlaw : ∀ t ∈ Set.Ioo 0 C.T, ∀ w θ, 0 < w → 0 < θ → θ < π / 2 →
      Work.Elliptic.bslOp (pExp (α : ℝ)) (fun z θ' => Φ z θ' (Work.FTS.Physical.clockInv C t)) w θ
        = Work.Construction.Fstar (pExp (α : ℝ)) w θ + g w θ (Work.FTS.Physical.clockInv C t))
    (hΦsm : ∀ t ∈ Set.Ioo 0 C.T, ∀ w θ : ℝ, -1 < w → -Real.pi / 2 - 1 < θ →
      θ < Real.pi / 2 + 1 → ContDiffAt ℝ 2
        (fun p : ℝ × ℝ => Φ p.1 p.2 (Work.FTS.Physical.clockInv C t)) (w, θ))
    (hΦplane : ∀ t ∈ Set.Ioo 0 C.T, ∀ w : ℝ, 0 < w → Φ w 0 (Work.FTS.Physical.clockInv C t) = 0)
    (hΦaxis : ∀ t ∈ Set.Ioo 0 C.T, ∀ w : ℝ, 0 < w →
      Φ w (Real.pi / 2) (Work.FTS.Physical.clockInv C t) = 0)
    (hrate : ∀ t ∈ Set.Ioo 0 C.T, ∃ lam C₀ : ℝ, 0 < lam ∧ 0 < C₀ ∧
      2 ≤ pExp (α : ℝ) * lam ∧ ∀ w θ : ℝ, 0 ≤ w → 0 ≤ θ → θ < Real.pi / 2 →
      |Φ w θ (Work.FTS.Physical.clockInv C t)| ≤ C₀ * (Real.pi / 2 - θ) * (1 + w) ^ (-lam) ∧
      |deriv (fun w' : ℝ => Φ w' θ (Work.FTS.Physical.clockInv C t)) w|
        ≤ C₀ * (Real.pi / 2 - θ) * (1 + w) ^ (-lam - 1) ∧
      |deriv (fun θ' : ℝ => Φ w θ' (Work.FTS.Physical.clockInv C t)) θ| ≤ C₀ * (1 + w) ^ (-lam) ∧
      |deriv (fun θ' : ℝ => deriv (fun θ'' : ℝ => Φ w θ'' (Work.FTS.Physical.clockInv C t)) θ') θ|
        ≤ C₀ * (1 + w) ^ (-lam) ∧
      |deriv (fun θ' : ℝ => deriv (fun w' : ℝ => Φ w' θ' (Work.FTS.Physical.clockInv C t)) w) θ|
        ≤ C₀ * (1 + w) ^ (-lam - 1) ∧
      |deriv (fun w' : ℝ => deriv (fun w'' : ℝ => Φ w'' θ (Work.FTS.Physical.clockInv C t)) w') w|
        ≤ C₀ * (Real.pi / 2 - θ) * (1 + w) ^ (-lam - 2)) :
    ∀ t ∈ Set.Ioo 0 C.T, ∀ x ∈ Work.FTS.BSIdent.Uax,
      Work.FTS.Physical.physVel (-(Work.FTS.Physical.physOmega (α : ℝ) A B g C)) x t
        = Work.Cyl.psiField (fun r z => Work.FTS.BSIdent.merPsi (α : ℝ) A B Φ C r z t) x :=
  Work.FTS_BSIdentP.hid_of_corrected'_proved hreg hlaw hΦsm hΦplane hΦaxis hrate  -- curric-46 lead 10-10: delivered by FTS_BSIdentP

/-- **BSIdent-P2 (gate)**: the slim variant — `C²` only on `w > 0`, and only the three first-order
rates (the `hid_of_corrected` closure reads only clauses 1–3 of `hrate`, REVIEW §4). Its one
`w = 0` call site is `continuous_axisLevel`; see `continuous_axisLevel_slim`. Audit the remaining
`hsm` call sites. If this does not go through, StreamBdry must also deliver `C²` across `w = 0` and
the second-order rates. -/
theorem hid_of_corrected'_slim {α : ℝ≥0} {A B : ℝ → ℝ} {g : Fam} {C : PhysClock} {Φ : Fam}
    (hreg : ∀ S : ℝ, 0 < S → Work.FTS.RegPkgGal.RegPkg' (α : ℝ) S A B g)
    (hlaw : ∀ t ∈ Set.Ioo 0 C.T, ∀ w θ, 0 < w → 0 < θ → θ < π / 2 →
      Work.Elliptic.bslOp (pExp (α : ℝ)) (fun z θ' => Φ z θ' (Work.FTS.Physical.clockInv C t)) w θ
        = Work.Construction.Fstar (pExp (α : ℝ)) w θ + g w θ (Work.FTS.Physical.clockInv C t))
    (hΦsm : ∀ t ∈ Set.Ioo 0 C.T, ∀ w θ : ℝ, 0 < w → -Real.pi / 2 - 1 < θ →
      θ < Real.pi / 2 + 1 → ContDiffAt ℝ 2
        (fun p : ℝ × ℝ => Φ p.1 p.2 (Work.FTS.Physical.clockInv C t)) (w, θ))
    (hΦplane : ∀ t ∈ Set.Ioo 0 C.T, ∀ w : ℝ, 0 < w → Φ w 0 (Work.FTS.Physical.clockInv C t) = 0)
    (hΦaxis : ∀ t ∈ Set.Ioo 0 C.T, ∀ w : ℝ, 0 < w →
      Φ w (Real.pi / 2) (Work.FTS.Physical.clockInv C t) = 0)
    (hrate : ∀ t ∈ Set.Ioo 0 C.T, ∃ lam C₀ : ℝ, 0 < lam ∧ 0 < C₀ ∧
      2 ≤ pExp (α : ℝ) * lam ∧ ∀ w θ : ℝ, 0 ≤ w → 0 ≤ θ → θ < Real.pi / 2 →
      |Φ w θ (Work.FTS.Physical.clockInv C t)| ≤ C₀ * (Real.pi / 2 - θ) * (1 + w) ^ (-lam) ∧
      |deriv (fun w' : ℝ => Φ w' θ (Work.FTS.Physical.clockInv C t)) w|
        ≤ C₀ * (Real.pi / 2 - θ) * (1 + w) ^ (-lam - 1) ∧
      |deriv (fun θ' : ℝ => Φ w θ' (Work.FTS.Physical.clockInv C t)) θ| ≤ C₀ * (1 + w) ^ (-lam)) :
    ∀ t ∈ Set.Ioo 0 C.T, ∀ x ∈ Work.FTS.BSIdent.Uax,
      Work.FTS.Physical.physVel (-(Work.FTS.Physical.physOmega (α : ℝ) A B g C)) x t
        = Work.Cyl.psiField (fun r z => Work.FTS.BSIdent.merPsi (α : ℝ) A B Φ C r z t) x :=
  Work.FTS_BSIdentP.hid_of_corrected'_slim_proved hreg hlaw hΦsm hΦplane hΦaxis hrate  -- curric-46 lead 10-10: delivered by FTS_BSIdentP

/-- **BSIdent-P2, the `z = 0` patch (REVIEW §4)**: `continuous_axisLevel` under the slim hypotheses.
`Weyl/Levels/continuous_axisLevel` calls `Dev2.continuousAt_pdZ_Phi hsm` at `w = ρ(0,z)^p/B`, which
is `0` at `z = 0`; there treat `axisLevel = -z·A⁻¹·∂_θΦ(w(z),π/2)` as a product `z · (bounded)`,
the bound being clause 3 of `hrate` extended to `θ = π/2` by closure (continuity of `∂_θΦ` at
`(w,π/2)`, `w > 0`, from `hsm`). For `z ≠ 0`, `w > 0` and the original argument applies. -/
theorem continuous_axisLevel_slim {α : ℝ} {A B : ℝ → ℝ} {Φ : Work.FTS.BSIdent.Fam}
    {C : Work.FTS.Physical.PhysClock} {t : ℝ}
    (hα : 0 < α) (hA : A (Work.FTS.Physical.clockInv C t) ≠ 0)
    (hB : 0 < B (Work.FTS.Physical.clockInv C t))
    (hsm : ∀ w θ : ℝ, 0 < w → -Real.pi / 2 - 1 < θ → θ < Real.pi / 2 + 1 →
      ContDiffAt ℝ 2 (fun p : ℝ × ℝ => Φ p.1 p.2 (Work.FTS.Physical.clockInv C t)) (w, θ))
    (hzeroPlane : ∀ w : ℝ, 0 < w → Φ w 0 (Work.FTS.Physical.clockInv C t) = 0)
    (hzeroAxis : ∀ w : ℝ, 0 < w → Φ w (Real.pi / 2) (Work.FTS.Physical.clockInv C t) = 0)
    {lam C₀ : ℝ} (hlam : 0 < lam) (hC₀ : 0 < C₀)
    (hexp : 2 ≤ Work.FTS.Regularity.pExp α * lam)
    (hrate : ∀ w θ : ℝ, 0 ≤ w → 0 ≤ θ → θ < Real.pi / 2 →
      |Φ w θ (Work.FTS.Physical.clockInv C t)| ≤ C₀ * (Real.pi / 2 - θ) * (1 + w) ^ (-lam) ∧
      |deriv (fun w' : ℝ => Φ w' θ (Work.FTS.Physical.clockInv C t)) w|
        ≤ C₀ * (Real.pi / 2 - θ) * (1 + w) ^ (-lam - 1) ∧
      |deriv (fun θ' : ℝ => Φ w θ' (Work.FTS.Physical.clockInv C t)) θ| ≤ C₀ * (1 + w) ^ (-lam)) :
    Continuous (Work.FTS.BSIdent.Weyl.Dev12.axisLevel α A B Φ (Work.FTS.Physical.clockInv C t)) :=
  Work.FTS_BSIdentP.continuous_axisLevel_slim_proved hα hA hB hsm hzeroPlane hzeroAxis hlam hC₀ hexp hrate  -- curric-46 lead 10-10: delivered by FTS_BSIdentP

/-! ## §2 StreamBdry leaves (slice level; FIX-A: no `Growth`, SB2–SB6 on `psiP`) -/

/-- **SB1′ (research low)**: the gauge decomposition, with NO growth hypothesis. The ODE
`αG·D_zΨ + 3Ψ = -s2·U'` makes `c(θ) := z^{3/αG}(Ψ - psiP)` independent of `z`; `V(Ψ)` is bounded
(`SlotBd`) and `V(psiP)` is bounded at each fixed `θ` as `z → 0` (`psiP` carries `s2`, and
`|∂_θU'| ≤ M`), hence `c' = tan θ · c`, i.e. `c = κ / cos θ`. -/
theorem sb1_gauge {αG M : ℝ} (hαG : 0 < αG) {Ψ : Fn}
    (h3 : ContDiffOn ℝ 3 (Function.uncurry Ψ) Work.Construction.Qd)
    (hslot : SlotBd αG Ψ M) :
    ∃ κ : ℝ, ∀ z θ, (z, θ) ∈ Work.Construction.Qd →
      Ψ z θ = psiP αG Ψ z θ + κ * gaugeMode αG z θ := by
  sorry

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

/-- **SB3 (research low, from SB1′ + the law)**: uniform bounds for the `U`-slot part on the open
quadrant. `D_z^j psiP` from the integral (`j ≤ 2`) and the ODE (`j = 3`); θ-derivatives from
`V(psiP) = V(Ψ)` (`V(gaugeMode) = 0`), `∂_θV = -(αG²D_z² + 5αG D_z + 6)psiP - F` and
`W = psiP·cos θ`, `∂_θW = V cos θ`. -/
theorem sb3_bounds {αG M L Mf : ℝ} (hαG : 0 < αG) {F Ψ : Fn}
    (hsol : Work.FTS.StrongGlobal.IsBslSolPos αG F Ψ)
    (h3 : ContDiffOn ℝ 3 (Function.uncurry Ψ) Work.Construction.Qd)
    (hslot : SlotBd αG Ψ M) (hF : SrcOK F L Mf) :
    ∃ K : ℝ, ∀ z θ, (z, θ) ∈ Work.Construction.Qd →
      (∀ j ≤ 3, |Work.Spaces.DzIter j (psiP αG Ψ) z θ| ≤ K * Work.Construction.s2 θ) ∧
      (∀ j ≤ 1, |Work.Spaces.pth (Work.Spaces.DzIter j (psiP αG Ψ)) z θ| ≤ K) ∧
      (∀ j ≤ 1, |Work.Spaces.pthIter 2 (Work.Spaces.DzIter j (psiP αG Ψ)) z θ| ≤ K) := by
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

/-- **SB4 (research low–medium)**: first-order behaviour at the origin of the `U`-slot part of the
canonical slice, `|D_z psiP| ≤ K z s2` on `z ≤ 1` (equivalently `D_zU' = O(z)`: star part
`StarPkgo2.UszW`; `Θ(F)` explicit via `htay`; `Φ̃(f)` the `z^{3/2}`-weighted sup of the `ℋ⁴` slot —
shared with RX-A1w/RX-B). -/
theorem sb4_near0 {a C₀ Ce Cs : ℝ} (ha : 0 < a) (ha13 : a ≤ 1 / 3) {Φs : Fn} {E : Fn →ₗ[ℝ] Fn}
    (hEll : ∀ u : Fn, Work.FTS.ClassC.ClassC (pExp a) u →
      EllPkgGo (pExp a) Ce u (E u) ∧ Work.FTS.ClassC.EllPkgK (pExp a) 6 Ce u (E u))
    (hEL : EllLimOK3 (pExp a) E) (hStar : StarPkgo2 (pExp a) Cs Φs)
    {g G : Fam} {A B : ℝ → ℝ} (hSol : Sol (pExp a) Φs E g) (hOK : DynOK' (pExp a) C₀ Φs E g)
    (hreg : ∀ S : ℝ, 0 < S → Work.FTS.RegPkgGal.RegPkg' a S A B (extG G))
    (hG : ∀ z θ τ, 0 < z → θ ∈ Work.Spaces.Iθ → 0 ≤ τ → G z θ τ = g z θ τ) :
    ∀ τ, 0 ≤ τ → ∃ K : ℝ, ∀ z θ, (z, θ) ∈ Work.Construction.Qd → z ≤ 1 →
      |Work.Spaces.DzIter 1 (psiP (pExp a) (slice (PsiCan Φs E g) τ)) z θ|
        ≤ K * z * Work.Construction.s2 θ := by
  sorry

/-- **SB5 sub-leaf: the FIX-SB5 barrier exists** (one-dimensional ODE fact). E.g.
`φ = 1/θ + β log(1/θ)` near `0`, `1/(π/2-θ)² + β log(1/(π/2-θ))` near `π/2`, glued: the leading
terms are `𝓐`-harmonic, the log terms dominate the `O(1/θ)`/`O(1/(π/2-θ)²)` remainders. -/
theorem sb5_barrier : SB5Barrier := by
  sorry

/-- **SB5 (research medium)**: decay of the `U`-slot part outside the support, by comparison with the
slowest angular mode. For `j ≤ 2`, `u_j = D_z^j psiP / s2` solves the ground-state-transformed
equation `-αG²D_z²u - 5αG D_z u + 𝓐u = 0` on `z > L`, `𝓐 = -∂_θ² - (4 cot 2θ - tan θ)∂_θ` (no
zero-order term, no mixed term: slice-wise maximum principle). **Barrier (FIX-SB5)**:
`w = (M + δφ(θ))(z/L)^{-k}`, `αG k = 4 < 5`, `φ` from `sb5_barrier`; then
`𝓛w ≥ (z/L)^{-k}(4M - Cφδ) > 0`; at `z = R → ∞` only local-uniform decay on compact θ-sets is
needed (pointwise decay of `IsBslSolPos` + equicontinuity from SB3), near the ends `δφ ≥ sup|u|`.
`j ≥ 1`: Landau in `log z`; `j = 2` via difference quotients `Δ_h D_z psiP / h`. -/
theorem sb5_decay {αG M L Mf : ℝ} (hαG : 0 < αG) {F Ψ : Fn}
    (hsol : Work.FTS.StrongGlobal.IsBslSolPos αG F Ψ)
    (h3 : ContDiffOn ℝ 3 (Function.uncurry Ψ) Work.Construction.Qd)
    (hslot : SlotBd αG Ψ M) (hF : SrcOK F L Mf) (hbar : SB5Barrier) :
    ∃ K : ℝ, ∀ z θ, (z, θ) ∈ Work.Construction.Qd → L ≤ z →
      ∀ j ≤ 2, |Work.Spaces.DzIter j (psiP αG Ψ) z θ|
        ≤ K * Work.Construction.s2 θ * (L / z) ^ (4 / αG) := by
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

/-- **(9″) — the assembly** (replaces the false-as-stated `FinalV2.hid9'`; `FinalV2.hid9''` is this).
Adds only `hreg` (the adapter's `hRegG`, at the same clock; `G := gS a g` there) and `hG`; NO growth
inputs (FIX-A). Route at fixed `t`, `τ = clockInv C t ≥ 0`: SB0 rewrites the field to
`BSIdent.merPsi a A B (psiHatP (pExp a) Φs E g) C`; `hid_of_corrected'_slim` (or `'`) at
`Φ := psiHatP`, `g := extG G`; `hlaw` from `Sol` + `bslOp gaugeMode = 0` + `hG`; `hΦsm` = SB2;
plane/axis = `oddPerS` values; rates = SB6 with `slice_inputs` + SB4; finally
`physOmega (extG G) = physOmega (extG g)` (they agree at `θ ∈ [0,π/2]`, `z ≥ 0`, `τ ≥ 0` by `hG`).
Not glue, hence a named producer. -/
theorem hid9''_of_parts {a C₀ Ce Cs : ℝ} (ha : 0 < a) (ha13 : a ≤ 1 / 3) {Φs : Fn}
    {E : Fn →ₗ[ℝ] Fn}
    (hEll : ∀ u : Fn, Work.FTS.ClassC.ClassC (pExp a) u →
      EllPkgGo (pExp a) Ce u (E u) ∧ Work.FTS.ClassC.EllPkgK (pExp a) 6 Ce u (E u))
    (hEL : EllLimOK3 (pExp a) E) (hStar : StarPkgo2 (pExp a) Cs Φs) :
    ∀ (g G : Fam) (A B : ℝ → ℝ) (C : PhysClock),
      Sol (pExp a) Φs E g → DynOK' (pExp a) C₀ Φs E g →
      ClockData (pExp a) (PsiCan Φs E g) g A B C →
      (∀ S : ℝ, 0 < S → Work.FTS.RegPkgGal.RegPkg' a S A B (extG G)) →
      (∀ z θ τ, 0 < z → θ ∈ Work.Spaces.Iθ → 0 ≤ τ → G z θ τ = g z θ τ) →
      ∀ t ∈ Set.Ioo (0 : ℝ) C.T, ∀ x ∈ Uax,
        Work.FTS.Physical.physVel
          (fun x s => - Work.FTS.Physical.physOmega a A B (extG g) C x s) x t
          = Work.Cyl.psiField
              (fun r z => Work.FTS.MeridianDyn.merPsi (pExp a) A B (psiFire Φs E g) C r z t) x := by
  sorry

end Work.FTS.StreamBdryIface
