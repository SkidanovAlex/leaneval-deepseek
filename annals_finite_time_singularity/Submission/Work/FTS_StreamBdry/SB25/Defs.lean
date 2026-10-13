import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.FTS_StreamBdry.Basic

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.FTS_StreamBdry.SB25.Defs` — vocabulary and the W0/W1/W2/W3 leaf interface for SB2/SB5

Transcription of the lead's per-leaf plan `sources/ftsV2/fts_sb25_leafplans.{md,lean}`
(curric-46, 2026-10-10) into the `FTS_StreamBdry` subproject.  The mathematical content is
*identical*; the statements are re-packaged as `Prop`-valued definitions (`<Leaf> ... : Prop`)
so that a delegated lemma can be stated with no notation beyond a fully qualified name, and so
that the leaf interface is documented in one place.

Vocabulary added here: `Lgs` (the ground-state-transformed operator, `bslOp α (s2·u) = s2·Lgs α u`)
and `phiB` (the explicit FIX-SB5 barrier, `𝓐 phiB = -15/4` exactly).
-/

noncomputable section
open scoped Real Topology NNReal
open Set Filter MeasureTheory

namespace Work.FTS_StreamBdry.SB25

open Work.FTS.StreamBdryIface (Uprime SlotBd SrcOK gaugeMode psiP psiHatP SB5Barrier oddPerS)
open Work.FTS.Galerkin (Fn Fam slice)

set_option autoImplicit false

/-! ## §0 Vocabulary -/

/-- **The ground-state-transformed operator**: `bslOp α (s2·u) = s2 · Lgs α u`.  It has no
zero-order and no mixed term (sympy residual ≡ 0). -/
def Lgs (α : ℝ) (u : Fn) : Fn := fun z θ =>
  -(α ^ 2) * Work.Spaces.DzIter 2 u z θ - 5 * α * Work.Spaces.Dz u z θ
    - Work.Spaces.pthIter 2 u z θ
    - (4 * Real.cos (2 * θ) / Real.sin (2 * θ) - Real.tan θ) * Work.Spaces.pth u z θ

/-- **The explicit FIX-SB5 barrier**: `phiB' = -G/m` with `m = 4 sin²θ cos³θ`,
`G = 1 - 5 sin³θ + 3 sin⁵θ`; then `𝓐 phiB = -15/4` exactly, `phiB ≥ 0`, and `phiB → ∞` at both
ends (`phiB ≥ 1/(4 sin θ)` and `phiB ≥ 1/(16(1 - sin θ))`). -/
def phiB (θ : ℝ) : ℝ :=
  1 / (4 * Real.sin θ) + 1 / (16 * (1 - Real.sin θ)) + 3 / (16 * (1 + Real.sin θ))
    - 3 / 16 * Real.log (1 - Real.sin θ) - 9 / 16 * Real.log (1 + Real.sin θ) + 1

/-! ## §1 The leaf statements (W0/W1/W2/W3 of the plan) -/

/-- **C1 `gaugeMode_facts`**: the gauge mode is smooth on `Qd`, is `Vop`-free and is
`bslOp`-harmonic. -/
def GaugeModeFacts (αG : ℝ) : Prop :=
  ContDiffOn ℝ ⊤ (Function.uncurry (gaugeMode αG)) Work.Construction.Qd ∧
    ∀ z θ, (z, θ) ∈ Work.Construction.Qd →
      Work.Construction.Vop (gaugeMode αG) z θ = 0 ∧
        Work.Elliptic.bslOp αG (gaugeMode αG) z θ = 0

/-- **C2 `psiP_facts`**: the structure of the `U`-slot part (from `sb1_gauge` + C1). -/
def PsiPFacts (αG M : ℝ) (F Ψ : Fn) : Prop :=
  Work.FTS.StrongGlobal.IsBslSolPos αG F Ψ →
    ContDiffOn ℝ 3 (Function.uncurry Ψ) Work.Construction.Qd → SlotBd αG Ψ M →
      ContDiffOn ℝ 3 (Function.uncurry (psiP αG Ψ)) Work.Construction.Qd ∧
      (∀ z θ, (z, θ) ∈ Work.Construction.Qd →
        Work.Elliptic.bslOp αG (psiP αG Ψ) z θ = F z θ) ∧
      (∀ z θ, (z, θ) ∈ Work.Construction.Qd →
        Work.Construction.Vop (psiP αG Ψ) z θ = Work.Construction.Vop Ψ z θ) ∧
      (∀ z, psiP αG Ψ z 0 = 0 ∧ psiP αG Ψ z (π / 2) = 0) ∧
      (∀ θ ∈ Ioo (0 : ℝ) (π / 2), Tendsto (fun z => psiP αG Ψ z θ) atTop (𝓝 0))

/-- **C3 `law_Dform`**: the elliptic law in `D`-form, `∂_θV(P) = -(α²D²P + 5αDP + 6P) - F`. -/
def LawDform (α : ℝ) (F P : Fn) : Prop :=
  ContDiffOn ℝ 2 (Function.uncurry P) Work.Construction.Qd →
    (∀ z θ, (z, θ) ∈ Work.Construction.Qd → Work.Elliptic.bslOp α P z θ = F z θ) →
      ∀ z θ, (z, θ) ∈ Work.Construction.Qd →
        Work.Spaces.pth (Work.Construction.Vop P) z θ
          = -(α ^ 2 * Work.Spaces.DzIter 2 P z θ + 5 * α * Work.Spaces.Dz P z θ
              + 6 * P z θ) - F z θ

/-- **B2 `lip_edge_trace`**: a uniformly `θ`-Lipschitz function on a strip has continuous edge
traces, approached at linear rate. -/
def LipEdgeTrace (f : Fn) (a b K : ℝ) : Prop :=
  a < b → ContinuousOn (Function.uncurry f) (Ioi 0 ×ˢ Ioo a b) →
    (∀ z θ, 0 < z → θ ∈ Ioo a b → DifferentiableAt ℝ (fun θ' => f z θ') θ) →
    (∀ z θ, 0 < z → θ ∈ Ioo a b → |Work.Spaces.pth f z θ| ≤ K) →
      ∃ fa fb : ℝ → ℝ, ContinuousOn fa (Ioi 0) ∧ ContinuousOn fb (Ioi 0) ∧
        ∀ z θ, 0 < z → θ ∈ Ioo a b →
          |f z θ - fa z| ≤ K * (θ - a) ∧ |f z θ - fb z| ≤ K * (b - θ)

/-- **B3 `axis_tan_bound`** (1-D): if `V := f' - tan·f` converges to `v₀` at rate
`A(π/2 - θ)`, then `tan θ·f → -v₀/2` at that rate. -/
def AxisTanBound (f : ℝ → ℝ) (v0 A B : ℝ) : Prop :=
  (∀ θ ∈ Ioo (0 : ℝ) (π / 2), DifferentiableAt ℝ f θ) →
    (∀ θ ∈ Ioo (0 : ℝ) (π / 2), |f θ| ≤ B) →
    (∀ θ ∈ Ioo (0 : ℝ) (π / 2),
      |deriv f θ - Real.tan θ * f θ - v0| ≤ A * (π / 2 - θ)) →
      ∀ θ ∈ Ioo (0 : ℝ) (π / 2),
        |Real.tan θ * f θ + v0 / 2| ≤ |v0| * (π / 2 - θ) ^ 2 + 3 * A * (π / 2 - θ)

/-- **B4 `axis_d2_bound`** (1-D): the axis expansion to second order. -/
def AxisD2Bound (f : ℝ → ℝ) (v0 B ε θ0 : ℝ) : Prop :=
  θ0 ∈ Ioo (0 : ℝ) (π / 2) →
    (∀ θ ∈ Ioo (0 : ℝ) (π / 2),
      DifferentiableAt ℝ f θ ∧ DifferentiableAt ℝ (deriv f) θ) →
    (∀ θ ∈ Ioo (0 : ℝ) (π / 2), |f θ| ≤ B) →
    (∀ t ∈ Ico θ0 (π / 2), |deriv f t - Real.tan t * f t - v0| ≤ ε * (π / 2 - t)) →
    (∀ t ∈ Ico θ0 (π / 2),
      |deriv (fun s => deriv f s - Real.tan s * f s) t| ≤ ε) →
      |deriv (deriv f) θ0| ≤ 6 * ε + |v0| * (π / 2 - θ0)

/-- **B5 `psiP_edge_zero`**: the edge limits of `psiP` at `θ = 0`. -/
def PsiPEdgeZero (αG M L Mf : ℝ) (F Ψ : Fn) : Prop :=
  Work.FTS.StrongGlobal.IsBslSolPos αG F Ψ →
    ContDiffOn ℝ 3 (Function.uncurry Ψ) Work.Construction.Qd →
    SlotBd αG Ψ M → SrcOK F L Mf →
    (∃ K' : ℝ, ∀ z θ, (z, θ) ∈ Work.Construction.Qd →
      |Work.Spaces.pth (Work.Spaces.DzIter 1
        (Work.Construction.Vop (psiP αG Ψ))) z θ| ≤ K') →
      ∀ z0 : ℝ, 0 < z0 →
        let P := psiP αG Ψ
        Tendsto (Function.uncurry P) (𝓝[Work.Construction.Qd] (z0, 0)) (𝓝 0) ∧
        Tendsto (Function.uncurry (Work.Spaces.pz P))
          (𝓝[Work.Construction.Qd] (z0, 0)) (𝓝 0) ∧
        Tendsto (Function.uncurry (Work.Spaces.pz (Work.Spaces.pz P)))
          (𝓝[Work.Construction.Qd] (z0, 0)) (𝓝 0) ∧
        Tendsto (Function.uncurry (Work.Spaces.pth (Work.Spaces.pth P)))
          (𝓝[Work.Construction.Qd] (z0, 0)) (𝓝 0) ∧
        (∃ l, Tendsto (Function.uncurry (Work.Spaces.pth P))
          (𝓝[Work.Construction.Qd] (z0, 0)) (𝓝 l)) ∧
        (∃ l, Tendsto (Function.uncurry (Work.Spaces.pz (Work.Spaces.pth P)))
            (𝓝[Work.Construction.Qd] (z0, 0)) (𝓝 l) ∧
          Tendsto (Function.uncurry (Work.Spaces.pth (Work.Spaces.pz P)))
            (𝓝[Work.Construction.Qd] (z0, 0)) (𝓝 l))

/-- **B6 `psiP_edge_axis`**: the edge limits of `psiP` at `θ = π/2`. -/
def PsiPEdgeAxis (αG M L Mf : ℝ) (F Ψ : Fn) : Prop :=
  Work.FTS.StrongGlobal.IsBslSolPos αG F Ψ →
    ContDiffOn ℝ 3 (Function.uncurry Ψ) Work.Construction.Qd →
    SlotBd αG Ψ M → SrcOK F L Mf →
    (∃ K' : ℝ, ∀ z θ, (z, θ) ∈ Work.Construction.Qd →
      |Work.Spaces.pth (Work.Spaces.DzIter 1
        (Work.Construction.Vop (psiP αG Ψ))) z θ| ≤ K') →
      ∀ z0 : ℝ, 0 < z0 →
        let P := psiP αG Ψ
        Tendsto (Function.uncurry P) (𝓝[Work.Construction.Qd] (z0, π / 2)) (𝓝 0) ∧
        Tendsto (Function.uncurry (Work.Spaces.pz P))
          (𝓝[Work.Construction.Qd] (z0, π / 2)) (𝓝 0) ∧
        Tendsto (Function.uncurry (Work.Spaces.pz (Work.Spaces.pz P)))
          (𝓝[Work.Construction.Qd] (z0, π / 2)) (𝓝 0) ∧
        Tendsto (Function.uncurry (Work.Spaces.pth (Work.Spaces.pth P)))
          (𝓝[Work.Construction.Qd] (z0, π / 2)) (𝓝 0) ∧
        (∃ l, Tendsto (Function.uncurry (Work.Spaces.pth P))
          (𝓝[Work.Construction.Qd] (z0, π / 2)) (𝓝 l)) ∧
        (∃ l, Tendsto (Function.uncurry (Work.Spaces.pz (Work.Spaces.pth P)))
            (𝓝[Work.Construction.Qd] (z0, π / 2)) (𝓝 l) ∧
          Tendsto (Function.uncurry (Work.Spaces.pth (Work.Spaces.pz P)))
            (𝓝[Work.Construction.Qd] (z0, π / 2)) (𝓝 l))

/-- **B7a `glue_line_C1`**: `C¹` gluing across the line `θ = c`. -/
def GlueLineC1 (h : Fn) (c r : ℝ) : Prop :=
  0 < r →
    ContDiffOn ℝ 1 (Function.uncurry h)
      (Ioi 0 ×ˢ (Ioo (c - r) c ∪ Ioo c (c + r))) →
    ContinuousOn (Function.uncurry h) (Ioi 0 ×ˢ Ioo (c - r) (c + r)) →
    (∀ z0 : ℝ, 0 < z0 → ∃ l, Tendsto (Function.uncurry (Work.Spaces.pz h))
      (𝓝[Ioi 0 ×ˢ (Ioo (c - r) c ∪ Ioo c (c + r))] (z0, c)) (𝓝 l)) →
    (∀ z0 : ℝ, 0 < z0 → ∃ l, Tendsto (Function.uncurry (Work.Spaces.pth h))
      (𝓝[Ioi 0 ×ˢ (Ioo (c - r) c ∪ Ioo c (c + r))] (z0, c)) (𝓝 l)) →
      ContDiffOn ℝ 1 (Function.uncurry h) (Ioi 0 ×ˢ Ioo (c - r) (c + r)) ∧
      ContinuousOn (Function.uncurry (Work.Spaces.pz h)) (Ioi 0 ×ˢ Ioo (c - r) (c + r)) ∧
      ContinuousOn (Function.uncurry (Work.Spaces.pth h)) (Ioi 0 ×ˢ Ioo (c - r) (c + r))

/-- **B7b `contDiffOn_two_of_partials`**: `C¹` with `C¹` partials gives `C²` on an open set. -/
def ContDiffTwoOfPartials (h : Fn) (U : Set (ℝ × ℝ)) : Prop :=
  IsOpen U → ContDiffOn ℝ 1 (Function.uncurry h) U →
    ContDiffOn ℝ 1 (Function.uncurry (Work.Spaces.pz h)) U →
    ContDiffOn ℝ 1 (Function.uncurry (Work.Spaces.pth h)) U →
      ContDiffOn ℝ 2 (Function.uncurry h) U

/-- **B7c `glue_line_C2`**: `C²` gluing across `θ = c`. -/
def GlueLineC2 (h : Fn) (c r : ℝ) : Prop :=
  0 < r →
    ContDiffOn ℝ 2 (Function.uncurry h) (Ioi 0 ×ˢ (Ioo (c - r) c ∪ Ioo c (c + r))) →
    ContinuousOn (Function.uncurry h) (Ioi 0 ×ˢ Ioo (c - r) (c + r)) →
    (∀ D ∈ ({Work.Spaces.pz h, Work.Spaces.pth h, Work.Spaces.pz (Work.Spaces.pz h),
        Work.Spaces.pth (Work.Spaces.pz h), Work.Spaces.pz (Work.Spaces.pth h),
        Work.Spaces.pth (Work.Spaces.pth h)} : Set Fn),
      ∀ z0 : ℝ, 0 < z0 → ∃ l, Tendsto (Function.uncurry D)
        (𝓝[Ioi 0 ×ˢ (Ioo (c - r) c ∪ Ioo c (c + r))] (z0, c)) (𝓝 l)) →
      ContDiffOn ℝ 2 (Function.uncurry h) (Ioi 0 ×ˢ Ioo (c - r) (c + r))

/-- **B8a `oddPerS_pieces`**: `oddPerS P` is odd in `θ` on the strip and agrees with `P` (resp.
`-P(-·)`, `-P(π - ·)`) on the three pieces (given `P z (π/2) = 0`). -/
def OddPerSPieces (P : Fn) : Prop :=
  (∀ z, P z (π / 2) = 0) →
    (∀ w θ, oddPerS P w (-θ) = -oddPerS P w θ) ∧
    (∀ w θ, 0 < θ → θ ≤ π / 2 → oddPerS P w θ = P w θ) ∧
    (∀ w θ, -(π / 2) ≤ θ → θ < 0 → oddPerS P w θ = -P w (-θ)) ∧
    (∀ w θ, π / 2 < θ → θ < π → oddPerS P w θ = -P w (π - θ)) ∧
    (∀ w, oddPerS P w 0 = 0)

/-- **E1 `phiB_barrier`**: `phiB` witnesses `SB5Barrier` with `Cφ = 15/4` and `𝓐 phiB = -15/4`. -/
def PhiBBarrier : Prop :=
  ContDiffOn ℝ 2 phiB (Ioo 0 (π / 2)) ∧ (∀ θ ∈ Ioo (0 : ℝ) (π / 2), 0 ≤ phiB θ) ∧
    Tendsto phiB (𝓝[>] 0) atTop ∧ Tendsto phiB (𝓝[<] (π / 2)) atTop ∧
    ∀ θ ∈ Ioo (0 : ℝ) (π / 2),
      -deriv (deriv phiB) θ
        - (4 * Real.cos (2 * θ) / Real.sin (2 * θ) - Real.tan θ) * deriv phiB θ = -(15 / 4)

/-- **E2a `bslOp_dilate`**: `bslOp` commutes with dilations in `z`. -/
def BslOpDilate (α lam : ℝ) (P : Fn) : Prop :=
  ∀ z θ, Work.Elliptic.bslOp α (fun z' θ' => P (lam * z') θ') z θ
    = Work.Elliptic.bslOp α P (lam * z) θ

/-- **E2b `bslOp_lincomb`**: `bslOp` is linear at points of the open quadrant where both arguments
are `C²`.  (The restriction to `Qd` is necessary: `Real.tan` is not differentiable at `π/2`, so the
`∂_θ(tan θ·X)` slot of `Lzero` is not additive at `θ = π/2`; see the counterexample found by the
prover of the unrestricted version.) -/
def BslOpLincomb (α a b : ℝ) (P Q : Fn) : Prop :=
  ∀ z θ, (z, θ) ∈ Work.Construction.Qd → ContDiffAt ℝ 2 (Function.uncurry P) (z, θ) →
    ContDiffAt ℝ 2 (Function.uncurry Q) (z, θ) →
      Work.Elliptic.bslOp α (fun z' θ' => a * P z' θ' + b * Q z' θ') z θ
        = a * Work.Elliptic.bslOp α P z θ + b * Work.Elliptic.bslOp α Q z θ

/-- **E3 `bslOp_eq_s2_Lgs`**: the ground-state identity `bslOp α Q = s2 · Lgs α (Q/s2)` on `Qd`. -/
def BslOpEqS2Lgs (α : ℝ) (Q : Fn) : Prop :=
  ∀ z θ, (z, θ) ∈ Work.Construction.Qd → ContDiffAt ℝ 2 (Function.uncurry Q) (z, θ) →
    Work.Elliptic.bslOp α Q z θ
      = Work.Construction.s2 θ * Lgs α (fun z' θ' => Q z' θ' / Work.Construction.s2 θ') z θ

/-- **E4a `Lgs_nonneg_of_max`**: the coordinatewise maximum principle at an interior maximum. -/
def LgsNonnegOfMax (α : ℝ) (v : Fn) : Prop :=
  ∀ z0 θ0, 0 < z0 → θ0 ∈ Ioo (0 : ℝ) (π / 2) →
    ContDiffAt ℝ 2 (Function.uncurry v) (z0, θ0) →
    IsLocalMax (fun z => v z θ0) z0 → IsLocalMax (fun θ => v z0 θ) θ0 →
      0 ≤ Lgs α v z0 θ0

/-- **E4b `Lgs_barrier`**: `Lgs` of the barrier `w = (M + δφ)(z/L)^{-k} + η`. -/
def LgsBarrier (α k L M δ η : ℝ) : Prop :=
  ∀ φ : ℝ → ℝ, ContDiffOn ℝ 2 φ (Ioo 0 (π / 2)) → 0 < L →
    ∀ z θ, (z, θ) ∈ Work.Construction.Qd →
      Lgs α (fun z' θ' => (M + δ * φ θ') * (z' / L) ^ (-k) + η) z θ
        = (z / L) ^ (-k) * (α * k * (5 - α * k) * (M + δ * φ θ)
            + δ * (-deriv (deriv φ) θ
              - (4 * Real.cos (2 * θ) / Real.sin (2 * θ) - Real.tan θ) * deriv φ θ))

/-- **E4c `sb5_compare`**: comparison on the half-strip `z ≥ L`. -/
def Sb5Compare (α k L Mb : ℝ) (Q : Fn) : Prop :=
  0 < α → 0 < L → 0 < α * k → α * k < 5 → SB5Barrier →
    ContDiffOn ℝ 2 (Function.uncurry Q) Work.Construction.Qd →
    (∀ z θ, L < z → θ ∈ Ioo (0 : ℝ) (π / 2) →
      Work.Elliptic.bslOp α Q z θ = 0) →
    (∀ z θ, L ≤ z → θ ∈ Ioo (0 : ℝ) (π / 2) →
      |Q z θ| ≤ Mb * Work.Construction.s2 θ) →
    (∀ ε > 0, ∃ R, ∀ z θ, R ≤ z → θ ∈ Ioo (0 : ℝ) (π / 2) →
      |Q z θ| ≤ ε * Work.Construction.s2 θ) →
      ∀ z θ, L ≤ z → θ ∈ Ioo (0 : ℝ) (π / 2) →
        |Q z θ| ≤ Mb * Work.Construction.s2 θ * (L / z) ^ k

/-- **E5 `unif_decay_ratio`**: pointwise decay plus uniform `∂_θ`-bounds and vanishing at the ends
give `|P| ≤ ε·s2` uniformly in `θ` for `z ≥ R`. -/
def UnifDecayRatio (P : Fn) (K : ℝ) : Prop :=
  (∀ z θ, (z, θ) ∈ Work.Construction.Qd →
    DifferentiableAt ℝ (fun θ' => P z θ') θ ∧
      DifferentiableAt ℝ (fun θ' => Work.Spaces.pth P z θ') θ) →
    (∀ z θ, (z, θ) ∈ Work.Construction.Qd → |Work.Spaces.pth P z θ| ≤ K) →
    (∀ z θ, (z, θ) ∈ Work.Construction.Qd → |Work.Spaces.pthIter 2 P z θ| ≤ K) →
    (∀ z, 0 < z → Tendsto (fun θ => P z θ) (𝓝[>] 0) (𝓝 0) ∧
      Tendsto (fun θ => P z θ) (𝓝[<] (π / 2)) (𝓝 0)) →
    (∀ θ ∈ Ioo (0 : ℝ) (π / 2), Tendsto (fun z => P z θ) atTop (𝓝 0)) →
      ∀ ε > 0, ∃ R, ∀ z θ, R ≤ z → θ ∈ Ioo (0 : ℝ) (π / 2) →
        |P z θ| ≤ ε * Work.Construction.s2 θ

/-- **E6a `dq1_facts`**: the first log-difference quotient. -/
def Dq1Facts (g : ℝ → ℝ) (L B : ℝ) : Prop :=
  0 < L → (∀ z, L ≤ z → DifferentiableAt ℝ g z) →
    (∀ z, L ≤ z → |z * deriv g z| ≤ B) →
      (∀ h > 0, ∀ z, L ≤ z → |(g (Real.exp h * z) - g z) / h| ≤ B) ∧
      (∀ z, L < z → Tendsto (fun h => (g (Real.exp h * z) - g z) / h) (𝓝[>] 0)
        (𝓝 (z * deriv g z)))

/-- **E6b `dq2_facts`**: the second log-difference quotient. -/
def Dq2Facts (g : ℝ → ℝ) (L B : ℝ) : Prop :=
  0 < L →
    (∀ z, L ≤ z → DifferentiableAt ℝ g z ∧
      DifferentiableAt ℝ (fun z' => z' * deriv g z') z) →
    ContinuousOn (fun z => z * deriv (fun z' => z' * deriv g z') z) (Ici L) →
    (∀ z, L ≤ z → |z * deriv (fun z' => z' * deriv g z') z| ≤ B) →
      (∀ h > 0, ∀ z, L ≤ z →
        |(g (Real.exp (2 * h) * z) - 2 * g (Real.exp h * z) + g z) / h ^ 2| ≤ B) ∧
      (∀ z, L < z → Tendsto
        (fun h => (g (Real.exp (2 * h) * z) - 2 * g (Real.exp h * z) + g z) / h ^ 2)
        (𝓝[>] 0) (𝓝 (z * deriv (fun z' => z' * deriv g z') z)))

end Work.FTS_StreamBdry.SB25
