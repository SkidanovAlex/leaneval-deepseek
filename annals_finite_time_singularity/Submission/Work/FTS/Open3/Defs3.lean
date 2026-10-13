/-
# `FTS/Open3/Defs3` — the corrected hypotheses of the open-package chain (design §4)

This module copies **verbatim** the statements of the design's statement file
`Submission/Work/FTS/FTS_ELL_GALERKIN_STMTS.lean.txt` (namespace `Work.FTS.ScratchC46`)
that belong to the Open3 re-run, into the namespace `Work.FTS.Open3`.  Only the namespace
and the imports change; the statements are character-for-character those of the design.

What is corrected, and why (design `FTS_ELL_GALERKIN.md` §4):

* `IsBslSolPos` — the elliptic law for the corrected (positivity-only) boundary conditions:
  `IsBslSol` asks `Ψ z 0 = 0` for **all** `z`, which the open-quadrant solution of the
  modulated problem does not satisfy off the slab `z ≥ 0`.
* `hDataLimit'` — the initial-value identification only for `z ∈ Iz`, `θ ∈ Iθ` (the two
  sides of the identity are only known on the closed quadrant, not on all of `ℝ²`).
* `hRegLimit'` — the output of the compactness step is **not** `RegPkg α g` for the limit
  `g`; what holds is that there is `g'` agreeing with `g` on the slab with `RegPkg α g'`
  **and** `EqExtra α g' Φ` (the "extra" regularity of the two sides of the equation, which
  the identification of the weak and strong forms needs).
* `hPsiLim'` — a further subsequence is extracted (`ψ ∘ ψ'`), which removes the need for
  elliptic uniqueness.
* `hField_lip'` / `hField_bound'` / `hField_cont'` — the Lipschitz/bound/continuity
  conditions of the projected field are assumed on the **Euclidean** ball `EBall n (2R)`
  (the ball that the a-priori estimate `hCoeffBound` actually controls), not on the
  sup-norm ball `Metric.closedBall 0 (2R)`, where they are false for large `n`.
* `IPLinHQo` — the pairing is linear/bounded on the **open** class `HQo α 4` (interior
  `C^∞` plus `HkMem`), not on `RegQ α 4` (which asks `SmoothQuad`, i.e. `C^∞` through
  `z = 0` and hence is false for the transport terms).
* `WeakDetermines'` — the weak form determines the equation only from the *corrected*
  data: `RegPkg α g` **and** `EqExtra α g Φ`.

The providers of the *hypotheses* of the corrected chain are the sibling subprojects of design §5:
`IsBslSolPos` (the law), `hRegLimit'` (the persistence-of-regularity node, `FTS/RegPkgGal`),
`hField_*'`, `hProfileSpace`, `hProfileTau` (`FTS/GalFields`), `hPsiLim'`, `hDataLimit'`,
`hGalWeak` and `WeakDetermines'` (`FTS/GalLimit`, where `weakDetermines'_of` and its
`weakDetermines'_of_open3` transfer prove the last one), and `IPLinHQo` (`FTS/IPGen`).

Everything rests on `[propext, Classical.choice, Quot.sound]`.
-/
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Submission.Work.FTS.Open2.Chain2
import Submission.Work.FTS.Open2.Compat
import Submission.Work.FTS.TransportS.ClauseBridge
import Submission.Work.FTS.CoercivityFix.Assembly.Defs
import Submission.Work.FTS.OpenPkg.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.Open3

open Work.FTS.Nonlin
open Work.FTS.VocabO
open Work.FTS.VocabO2
open Work.FTS.Galerkin (Fn Fam slice galFun galField IsGalFam ConvLocUnif IsDynWeakOn
  IsDynEqOn RegPkg galFam gdot dynLin dynRHS Slab)

set_option autoImplicit false

/-! ## The elliptic law for the corrected boundary conditions -/

/-- `IsBslSolPos α F Ψ`: the elliptic equation `bslOp α Ψ = F` on the **open** quadrant and the
boundary conditions only for `z ≥ 0`.  This is the (corrected) elliptic law `Law` of the chain:
`Work.Elliptic.IsBslSol` asks `Ψ z 0 = 0` for all real `z`, which the modulated solution on the
closed quadrant does not satisfy. -/
def IsBslSolPos (α : ℝ) (F Ψ : Fn) : Prop :=
  (∀ z, 0 < z → ∀ θ, 0 < θ → θ < π / 2 → Work.Elliptic.bslOp α Ψ z θ = F z θ) ∧
    (∀ z, 0 ≤ z → Ψ z 0 = 0) ∧ (∀ z, 0 ≤ z → Ψ z (π / 2) = 0) ∧
    (∀ θ ∈ Work.Spaces.Iθ, Tendsto (fun z => Ψ z θ) atTop (𝓝 0))

/-! ## The extra regularity of the two sides of the equation -/

/-- `EqExtra α g Φ`: at every fake time `τ ≥ 0`, the stream function's slice is `C^∞` on the open
quadrant, and **both sides** of the dynamic modulated equation are in the class in which the
pairing is defined and the weak form can be identified with the strong one: `HQo α 4` (interior
`C^∞` + `HkMem`), `BdryTraces α 4` (vanishing of the integration-by-parts boundary terms) and
vanishing of the zero mode `L₁₂(·)(0) = 0`. -/
def EqExtra (α : ℝ) (g Φ : Fam) : Prop :=
  ∀ τ, 0 ≤ τ → Work.FTS.EllipticEst.SmoothOpen (slice Φ τ) ∧
    HQo α 4 (gdot g τ) ∧ BdryTraces α 4 (gdot g τ) ∧ Work.Construction.L12 (gdot g τ) 0 = 0 ∧
    HQo α 4 (dynLin α g τ + dynRHS α Φ g τ) ∧ BdryTraces α 4 (dynLin α g τ + dynRHS α Φ g τ) ∧
    Work.Construction.L12 (dynLin α g τ + dynRHS α Φ g τ) 0 = 0

/-! ## The corrected hypotheses of the limit passage -/

/-- **`hRegLimit'`**: the limit of a convergent subsequence of Galerkin profiles has a
`RegPkg`-regular *representative* `g'` which agrees with the limit `g` on the slab **and**
carries the `EqExtra` data of the equation (design §4, the corrected form of the false
`hRegLimit : … → RegPkg α g`). -/
def hRegLimit' (α : ℝ) (IP : ℝ → Fn → Fn → ℝ) (φ : ℕ → Fn) (Φs : Fn) (EllSol : Fn → Fn)
    (R : ℝ) : Prop :=
  ∀ c, IsGalFam α (IP α) φ (PsiCan Φs EllSol) R c → ∀ (ψ : ℕ → ℕ) (g Φ : Fam), StrictMono ψ →
    ConvLocUnif (fun n => galFam φ (ψ n) (c (ψ n))) g →
    ConvLocUnif (fun n => PsiCan Φs EllSol (galFam φ (ψ n) (c (ψ n)))) Φ →
    ∃ g' : Fam, (∀ p ∈ Slab, g' p.1 p.2.1 p.2.2 = g p.1 p.2.1 p.2.2) ∧ RegPkg α g' ∧ EqExtra α g' Φ

/-- **`hDataLimit'`**: the initial-value identification of the limit, on the closed quadrant
only (the corrected form of `hDataLimit : … → ∀ z θ, g z θ 0 = g₀ z θ`). -/
def hDataLimit' (α : ℝ) (IP : ℝ → Fn → Fn → ℝ) (φ : ℕ → Fn) (Φs : Fn) (EllSol : Fn → Fn)
    (R : ℝ) (g₀ : Fn) : Prop :=
  ∀ c, IsGalFam α (IP α) φ (PsiCan Φs EllSol) R c → ∀ (ψ : ℕ → ℕ) (g : Fam), StrictMono ψ →
    ConvLocUnif (fun n => galFam φ (ψ n) (c (ψ n))) g →
    ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ, g z θ 0 = g₀ z θ

/-- **`hPsiLim'`**: from a convergent subsequence of Galerkin profiles one may pass to a
**further** subsequence along which the stream functions converge; no uniqueness of the
elliptic solution is used (design §4). -/
def hPsiLim' (α : ℝ) (IP : ℝ → Fn → Fn → ℝ) (φ : ℕ → Fn) (Φs : Fn) (EllSol : Fn → Fn)
    (R : ℝ) : Prop :=
  ∀ c, IsGalFam α (IP α) φ (PsiCan Φs EllSol) R c → ∀ (ψ : ℕ → ℕ) (g : Fam), StrictMono ψ →
    ConvLocUnif (fun n => galFam φ (ψ n) (c (ψ n))) g →
    ∃ (ψ' : ℕ → ℕ) (Φ : Fam), StrictMono ψ' ∧
      ConvLocUnif (fun n => PsiCan Φs EllSol (galFam φ (ψ (ψ' n)) (c (ψ (ψ' n))))) Φ

/-! ## The corrected field conditions, on the Euclidean ball -/

/-- The **Euclidean ball** of radius `r` in `Fin n → ℝ`: `EBall n r = {c | ∑ cₖ² ≤ r²}`.  This is
the ball that the a-priori estimate `hCoeffBound` controls; the sup-norm ball of the same radius
(`Metric.closedBall 0 r`) contains it strictly and is the wrong hypothesis for the projected
field (design §4). -/
def EBall (n : ℕ) (r : ℝ) : Set (Fin n → ℝ) := {c | ∑ k, c k ^ 2 ≤ r ^ 2}

/-- **`hField_lip'`**: the projected field is Lipschitz on the Euclidean ball `EBall n (2R)` with
constant `K n`. -/
def hField_lip' (α : ℝ) (IP : ℝ → Fn → Fn → ℝ) (φ : ℕ → Fn) (Φs : Fn) (EllSol : Fn → Fn)
    (R : ℝ) (K : ℕ → ℝ) (hK : ∀ n, 0 ≤ K n) : Prop :=
  ∀ (n : ℕ) (τ : ℝ), 0 ≤ τ →
    LipschitzOnWith ⟨K n, hK n⟩ (galField α (IP α) φ n (PsiCan Φs EllSol) τ) (EBall n (2 * R))

/-- **`hField_bound'`**: the projected field is bounded on the Euclidean ball `EBall n (2R)`. -/
def hField_bound' (α : ℝ) (IP : ℝ → Fn → Fn → ℝ) (φ : ℕ → Fn) (Φs : Fn) (EllSol : Fn → Fn)
    (R : ℝ) (L : ℕ → ℝ) : Prop :=
  ∀ (n : ℕ) (τ : ℝ) (c : Fin n → ℝ), 0 ≤ τ → c ∈ EBall n (2 * R) →
    ‖galField α (IP α) φ n (PsiCan Φs EllSol) τ c‖ ≤ L n

/-- **`hField_cont'`**: the projected field is continuous in the fake time on the Euclidean ball
`EBall n (2R)`. -/
def hField_cont' (α : ℝ) (IP : ℝ → Fn → Fn → ℝ) (φ : ℕ → Fn) (Φs : Fn) (EllSol : Fn → Fn)
    (R : ℝ) : Prop :=
  ∀ (n : ℕ) (c : Fin n → ℝ), c ∈ EBall n (2 * R) →
    ContinuousOn (fun τ => galField α (IP α) φ n (PsiCan Φs EllSol) τ c) (Set.Ici 0)

/-! ## The corrected bilinearity class of the pairing -/

/-- **`IPLinHQo`**: the pairing is additive and homogeneous in its first argument, bounded by
`Ct·|f₁|_{ℋ⁴}·|g|_{ℋ⁴}`, and only depends on the values on the open quadrant — all on the
*open* class `HQo α 4` (interior `C^∞` + `HkMem`), which is the class in which the transport
terms of the equation lie.  This replaces the `RegQ`-based clauses of `UnifIP` for the two
sides of the dynamic equation (design §4). -/
def IPLinHQo (IP : ℝ → Fn → Fn → ℝ) (α₂ Ct : ℝ) : Prop :=
  ∀ α ∈ Set.Ioc 0 α₂, ∀ f₁ f₂ g : Fn, HQo α 4 f₁ → HQo α 4 f₂ → HQo α 4 g →
    IP α (f₁ + f₂) g = IP α f₁ g + IP α f₂ g ∧
    (∀ c : ℝ, IP α (fun z θ => c * f₁ z θ) g = c * IP α f₁ g) ∧
    |IP α f₁ g| ≤ Ct * Xn α f₁ * Xn α g ∧
    (∀ f', (∀ z θ, (z, θ) ∈ Work.Construction.Qd → f₁ z θ = f' z θ) → IP α f₁ g = IP α f' g)

/-- The second-argument expansion of the pairing over the Galerkin span, in the open class: for
`f ∈ HQo α 4`, `IP α f (∑ₖ cₖφₖ) = ∑ₖ cₖ IP α f (φₖ)`.  It is the `ip_galFun_snd` of the design
(`OpenPkg/AprioriOpen/Bridge.lean`) with the `RegQ` hypothesis relaxed to `HQo`, which is what
the corrected bridge needs.  It is *proved* in `Open3/ip_galFun_snd_hqo`. -/
def ipGalFunSndO (IP : ℝ → Fn → Fn → ℝ) (α₂ : ℝ) (φ : ℕ → Fn) : Prop :=
  ∀ α ∈ Set.Ioc 0 α₂, ∀ f : Fn, HQo α 4 f → ∀ (n : ℕ) (c : Fin n → ℝ),
    IP α f (galFun φ c) = ∑ k : Fin n, c k * IP α f (φ (k : ℕ))

/-! ## The density classes of the corrected Galerkin basis -/

/-- **`DenseSpanO`**: the span of the first `n` test functions is dense in the open class with
boundary traces and vanishing zero mode, in the `ℋ⁴`-norm (design item 3). -/
def DenseSpanO (α : ℝ) (IP : ℝ → Fn → Fn → ℝ) (φ : ℕ → Fn) : Prop :=
  ∀ f : Fn, HQo α 4 f → BdryTraces α 4 f → Work.Construction.L12 f 0 = 0 → ∀ ε : ℝ, 0 < ε →
    ∃ (n : ℕ) (c : Fin n → ℝ), Work.Spaces.HkNorm α 4 (fun z θ => f z θ - galFun φ c z θ) < ε

/-- **`CcBasis φ`**: every test function is `C^∞` and compactly supported in a box of the slab
(design item 3). -/
def CcBasis (φ : ℕ → Fn) : Prop :=
  ∀ k, ∃ a b : ℝ, 0 < a ∧ a < b ∧ ∃ δ : ℝ, 0 < δ ∧ ContDiff ℝ (⊤ : ℕ∞) (Function.uncurry (φ k)) ∧
    ∀ z θ, (z ∉ Set.Icc a b ∨ θ ∉ Set.Icc δ (π / 2 - δ)) → φ k z θ = 0

/-! ## The corrected determination of the equation by its weak form -/

/-- **`WeakDetermines'`**: from the `RegPkg` regularity of the solution, the `EqExtra` data of
the equation and the tested weak form, the dynamic modulated equation follows pointwise on the
open quadrant (design §4; the corrected form of `WeakDetermines`, which does not ask for the
`EqExtra` data that the identification of the two sides needs). -/
def WeakDetermines' (α : ℝ) (IP : Fn → Fn → ℝ) (φ : ℕ → Fn) : Prop :=
  ∀ g Φ : Fam, RegPkg α g → EqExtra α g Φ → IsDynWeakOn α IP φ g Φ → IsDynEqOn α Φ g

end Work.FTS.Open3
