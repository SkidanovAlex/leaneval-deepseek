/-
Copyright: work module for the Elgindi finite-time singularity project.

# `remov/AeChainDefs` — the interface of the level-`0` weak elliptic estimate

The deliverable of the node is

```
theorem EllWeak0_exists : ∃ C : ℝ, 0 < C ∧ Work.FTS.EllipticEst.TT.EllWeak0 C
```

(the paper's `(radialandangularweightL2)` at level `0`, i.e. the weighted `L²` estimate of
Step 2 of Proposition `prop:H2`, tex 879 of Elgindi, Annals **194** (2021)), in the weak class
`TT.EllWeakPos α 0 F Ψ`.

Every route through a *stronger* class is dead — formally so: `Work.Spaces.SmoothNbhd` is
*analyticity* on a neighbourhood of the closed quadrant, so no truncation of a weak datum is a
strong datum (see `Mine/WeakOfStrong`, `Mine/WeakClassStrict`,
`remov/NOTES_level0WeakBridge_truncation.md`).  The estimate therefore has to be proved
**directly in the weak class**.

## The decomposition

Everything is phrased in the a.e.-class `Work.FTS.EllipticEst.H2W.Ae.AeData`, which is implied by
`TT.EllWeakPos α 0 F Ψ` (the pointwise moment conditions of `EllWeakPos` imply the a.e. ones).
Write `ρ = w²σ`, `σ = sin(2θ)^{-η}`, `‖g‖_ρ = H2W.Ae.nrm α g = √(HkSq α 0 g)`,
`A = z²∂_zzu`, `B = ∂_θθu`, `U = z∂_zu`, `G` the source, and
`IP g h = ∫_z∫_θ g h w²σ` (`AngSecond.IP`).

The workspace already provides the two *assemblies*, both sorry-free:

* `H2W.Ae.Assembly.level0Ae_of` — the target from `Ae.Step1`, `Ae.Step2`, `Ae.Step3`;
* the four-way decomposition of Step 2 (the paper's pairing of `bslOp α u = G` against
  `-B ρ`, then Cauchy–Schwarz and a quadratic solve) — see `AeStep2_of` in
  `remov/AeStep2Weak.lean`.

The analytic content is the following five pieces, each a genuine independent part of the
paper's proof of `prop:H2`:

| piece | statement | file |
|---|---|---|
| Step 1 (energy + `σ`-upgrade + `u/cos θ` companion) | `remov.AeStep1Full` | `remov/AeStep1Full.lean` |
| `I₁` lower bound (`α²⟨A,B⟩` coercivity) | `remov.AeI1Lower` | `remov/AeI1Lower.lean` |
| `I₄` upper bound (`⟨∂_θ(tan θ u), B⟩`) | `remov.AeI4Upper` | `remov/AeI4Upper.lean` |
| pairing bookkeeping (`IPMem` of the six slots) | `remov.AeIPMemsBook` | `remov/AeIPMemsBook.lean` |
| radial recovery (`α²z²∂_zzu` from the equation) | `H2W.Ae.Step3` | `remov/AeStep3Weak.lean` |

`AeStep1Full` is the *join* of the two Step-1 interfaces in the workspace (`H2W.Ae.Step1` wants
`α‖U‖_ρ ≤ C‖G‖_ρ` for the final quadratic form; the `AngAWeak.AeStep1` of the sibling workstream
wants the `u/cos θ` companion for the `I₄` slot): the paper's Step 1 gives all four inequalities
at once, so joining them costs nothing and lets a single prover do the single energy argument.
Both interfaces follow from `AeStep1Full` by dropping conjuncts.
-/
import Mathlib.Analysis.Complex.Trigonometric
import Submission.Work.Spaces.Defs
import Submission.Work.Elliptic.Defs
import Submission.Work.FTS.EllipticEst.Defs
import Submission.Work.FTS.EllipticEst.H2W.Ae.Defs
import Submission.Work.FTS.EllipticEst.H2W.Ae.Assembly
import Submission.Work.FTS.EllipticEst.AngSecond.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.remov

set_option autoImplicit false

/-- **Step 1 of the level-`0` estimate in the weak class `AeData`** (the paper's Step 1, i.e. the
energy identity obtained by pairing `(PolarBSL)` with `u` and integrating, followed by the
`σ`-upgrade and the Hardy-based `Ψ̄ = u/cos θ` companion).

For every datum `AeData α u G` there is a universal `C` with

* `u`, `z ∂_z u` and `u / cos θ` honest in `ℋ⁰` (`HkMem α 0`),
* `‖u‖_ρ ≤ C‖G‖_ρ` and `α‖z∂_zu‖_ρ ≤ C‖G‖_ρ`,
* `‖u/cos θ‖_ρ ≤ C(‖G‖_ρ + α‖z∂_zu‖_ρ)`.

(Paper's ingredients: multiply `(PolarBSL)` by `u` and integrate against the weight; the angular
part gives `|∂_θu|² - 6|u|² ≤ |G||u|`, and the moment condition `F_*(u) = 0` a.e. (used through
the Fourier/Parseval decomposition `u = Σ u_n(z)sin(2nθ)`) excludes the `n = 1` mode, which is
what makes `-6|u|²` absorbable; then `‖u/cos θ‖` and the `σ`-upgrade follow from the Hardy
inequalities `∫ f²/sin²(2θ) ≤ 10∫(f')²` and the constrained slice Poincaré
(`Honest.SigmaPoincare`, `Honest.Gap9Open`, both proved) — cf. `Honest/NOTES_step1.md`.) -/
def AeStep1Full : Prop :=
  ∃ C : ℝ, 0 < C ∧
    ∀ (α : ℝ) (u G : ℝ → ℝ → ℝ), Work.FTS.EllipticEst.H2W.Ae.AeData α u G →
      Work.Spaces.HkMem α 0 u ∧
      Work.Spaces.HkMem α 0 (Work.FTS.EllipticEst.H2W.Ae.grad u) ∧
      Work.Spaces.HkMem α 0 (fun z θ => u z θ / Real.cos θ) ∧
      Work.FTS.EllipticEst.H2W.Ae.nrm α u ≤ C * Work.FTS.EllipticEst.H2W.Ae.nrm α G ∧
      α * Work.FTS.EllipticEst.H2W.Ae.nrm α (Work.FTS.EllipticEst.H2W.Ae.grad u)
        ≤ C * Work.FTS.EllipticEst.H2W.Ae.nrm α G ∧
      Work.FTS.EllipticEst.H2W.Ae.nrm α (fun z θ => u z θ / Real.cos θ)
        ≤ C * (Work.FTS.EllipticEst.H2W.Ae.nrm α G
          + α * Work.FTS.EllipticEst.H2W.Ae.nrm α (Work.FTS.EllipticEst.H2W.Ae.grad u))

/-- `AeStep1Full` implies `H2W.Ae.Step1` (drop the two `u/cos θ` conjuncts). -/
theorem AeStep1Full.toStep1 (h : AeStep1Full) : Work.FTS.EllipticEst.H2W.Ae.Step1 := by
  obtain ⟨C, hC, h'⟩ := h
  refine ⟨C, hC, fun α u G hA => ?_⟩
  obtain ⟨hmu, hmU, -, huB, hUB, -⟩ := h' α u G hA
  exact ⟨hmu, hmU, huB, hUB⟩

/-- **The `I₁` lower bound in the class `AeData`** (the deep coercivity input of Step 2):

`-C α²(⟨U,U⟩ + √⟨U,U⟩·√⟨B,B⟩) ≤ α²⟨A,B⟩`, where `A = z²∂_zzu`, `B = ∂_θθu`, `U = z∂_zu`
and `⟨·,·⟩ = AngSecond.IP` (`IP g h = ∫_z∫_θ g h w²σ`).

Paper's ingredients (tex 873–890): the `z`-IBP `I₁ = -α²⟨z²∂_zu, ∂_{zθθ}u ρ⟩ + E`, the second
`θ`-IBP, the identity `∂_θθ(sin(2θ)^{-η}) = 4η(η+1)cos²(2θ)sin^{-(2+η)}(2θ) + 4η sin^{-η}(2θ)`,
and then the **sharp Hardy inequality** (`SharpHardyInequality2`,
`∫f²/sin^{2+η}(2θ) ≤ (1+η)^{-2}∫(f')²/sin^η(2θ) + 100|f|²_{H¹}`) applied slicewise to
`f = z∂_zu(z,·)`.  This yields the positive gain `(1-η)/(1+η)·α²‖z∂_z∂_θu‖²_ρ` (with
`z∂_z∂_θu = ∂_θ(z∂_zu) = Work.Spaces.pth (H2W.Ae.grad u)`) and error terms which the paper
denotes `E` and controls exactly as `I₂`/`I₅`, i.e. by `‖G‖_ρ·‖B‖_ρ` and `‖G‖²_ρ` (the latter
also using Step 1's `α‖z∂_{zθ}u‖_{w²} ≤ C‖Gw‖` and `L2Sq(z∂_zu·w) ≤ C|Gw|²`).

WARNING: dropping the positive term and replacing it by `⟨U,U⟩`-data — which is what
`AngAWeak.AeI1` and `AngAWeak/aeI1Lower.lean` do — gives a **FALSE** statement; see
`remov/NOTES_AeChain_design.md` §2 and `AngAWeak/NOTES_aeI1Lower_FALSE.md`. -/
def AeI1LowerPos : Prop :=
  ∃ C : ℝ, 0 < C ∧
    ∀ (α : ℝ) (u G : ℝ → ℝ → ℝ), Work.FTS.EllipticEst.H2W.Ae.AeData α u G →
      ((1 - Work.Spaces.eta) / (1 + Work.Spaces.eta)) *
          (α ^ 2 * Work.Spaces.HkSq α 0
            (Work.Spaces.pth (Work.FTS.EllipticEst.H2W.Ae.grad u)))
        - C * (Work.FTS.EllipticEst.H2W.Ae.nrm α G
              * Work.FTS.EllipticEst.H2W.Ae.nrm α (Work.Spaces.pthIter 2 u)
            + (Work.FTS.EllipticEst.H2W.Ae.nrm α G) ^ 2)
        ≤ α ^ 2 * Work.FTS.EllipticEst.AngSecond.IP
            (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 u z θ) (Work.Spaces.pthIter 2 u)

/-- **The `I₄` upper bound in the class `AeData`** (the second deep input of Step 2):

`⟨∂_θ(tan θ·u), B⟩ ≤ C‖G‖²_ρ`, `B = ∂_θθu`.

Paper's ingredients (tex 873–890, "We now turn to `I₄`"): write `∂_θ(tan θ u) = ∂_θ(sin θ Ψ̄)`
with `Ψ̄ = u/cos θ`, decompose `∂_θθ(cos θ Ψ̄)` into `I_{4,1} + I_{4,2} + I_{4,3}`; `I_{4,2} ≥ 0` is
discarded, `I_{4,1} = ((1-η)/2)⟨cos 2θ(∂_θΨ̄)², w²/sin^η⟩` is also ≥ 0 on the relevant part, and
`I_{4,3}` is integrated by parts (`|I_{4,3}| ≤ C|Fw|² ≤ C‖G‖²_ρ`); the boundary terms of that
integration by parts vanish because `HkMem α 0 (∂_θθu)` and the equation force `u` to vanish at
the angular endpoints faster than `θ^{3/2}` (see `remov/NOTES_AeChain_design.md` §3).  The
`Hon`-class versions of the same computation are `Honest/I4UpperHonest` (proved) and
`AngClean/I4_lower_bound_slice`; `Honest/I4GlobalAssembly`, `Honest/I4BoundaryVanish` are proved
and reusable. -/
def AeI4Upper : Prop :=
  ∃ C : ℝ, 0 < C ∧
    ∀ (α : ℝ) (u G : ℝ → ℝ → ℝ), Work.FTS.EllipticEst.H2W.Ae.AeData α u G →
      Work.FTS.EllipticEst.AngSecond.IP
          (fun z θ => Work.Spaces.pth (fun z θ => Real.tan θ * u z θ) z θ)
          (Work.Spaces.pthIter 2 u)
        ≤ C * Work.Spaces.HkSq α 0 G

/-- **The `IPMem` bookkeeping of the Step-2 identity in the class `AeData`**: the six pairings
occurring in the identity are honest, given the honesty of `u` and of `z∂_zu` supplied by Step 1.

Each slot follows from `HkMem` of the two entries by Cauchy–Schwarz
(`AngClean.HkMem_zero_IPMem`, `AngClean.IPMem_F_Phi`); the only new piece is
`HkMem α 0 (∂_θ(tan θ·u))`, which follows from `u + sin θ·∂_θ(u/cos θ)` plus
`HkMem α 0 u`, `HkMem α 0 (z∂_zu)` and the slice Hardy inequalities
(`Honest/HonMemU/honMemPthTan.lean` is the `Hon`-class version). -/
def AeIPMemsBook : Prop :=
  ∀ (α : ℝ) (u G : ℝ → ℝ → ℝ), Work.FTS.EllipticEst.H2W.Ae.AeData α u G →
    Work.Spaces.HkMem α 0 u →
    Work.Spaces.HkMem α 0 (Work.FTS.EllipticEst.H2W.Ae.grad u) →
      Work.FTS.EllipticEst.AngSecond.IPMem G (Work.Spaces.pthIter 2 u) ∧
      Work.FTS.EllipticEst.AngSecond.IPMem
        (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 u z θ) (Work.Spaces.pthIter 2 u) ∧
      Work.FTS.EllipticEst.AngSecond.IPMem (Work.FTS.EllipticEst.H2W.Ae.grad u)
        (Work.Spaces.pthIter 2 u) ∧
      Work.FTS.EllipticEst.AngSecond.IPMem
        (fun z θ => Work.Spaces.pth (fun z θ => Real.tan θ * u z θ) z θ)
        (Work.Spaces.pthIter 2 u) ∧
      Work.FTS.EllipticEst.AngSecond.IPMem u (Work.Spaces.pthIter 2 u) ∧
      Work.FTS.EllipticEst.AngSecond.IPMem (Work.Spaces.pthIter 2 u)
        (Work.Spaces.pthIter 2 u)

end Work.FTS.EllipticEst.remov
