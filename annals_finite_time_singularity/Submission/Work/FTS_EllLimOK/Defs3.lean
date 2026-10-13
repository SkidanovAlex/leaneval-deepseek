/-
Copyright: work module for the Elgindi finite-time singularity project.

# `FTS_EllLimOK.Defs3` — the order-3 vocabulary and the small-α obligation shapes

The integration redesign (`sources/ftsV2/fts_final_redesign.md` §G5 and the lead's message of
2026-10-10) moves the deliverable of this area to

  `Work.FTS_EllLimOK.core1_1a3_proved`, with the identical type of `FinalV2.Producers.core1_1a3`,

i.e. Final's conjuncts (1) + (1a′) from `ExistsEllSolC`: one linear `E` carrying the two packages on
the class `C` **and** `EllLimOK3` (the *order-`3`* limit closure: the limit `E f` is `C³` on `Qd`
and the jets of order `≤ 3` converge — this is what the later conjunct (13) needs).

Two changes with respect to the order-`2` vocabulary of `Defs.lean`:

* everything is restated **at small α** — the analytic obligations are only expected for
  `α ∈ (0, α₁]` (`SmallCompact3`, `SmallUniq3`, `SmallLocalBound4`), and the thresholds are
  threaded through the glue (`min α₀ α₁`, as `EllSol.existsEllSolC_of_threshold` does);
* the jet-limit of an operator along a `LimSeq4` now carries the **Fatou package** (`FatouPkg`):
  the honest `ℋ⁰`/`L²` memberships and the decay of the limit, i.e. exactly the fields of the
  tree's `EllipticEst.EllHyp`/`EllHypN` that the uniqueness theorem
  `EllipticEst.bslSol_unique_fts` consumes.  These bounds are what excludes the homogeneous mode
  `z^{-5/α} sin 2θ` (the only negative-power Cauchy–Euler mode, which is *not* `L²` near `z = 0`),
  and they are the reason the ruling demands them here: without them `ClosedUniq` is false.
-/
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS_EllLimOK.Defs
import Submission.Work.FTS_EllLimOK.Closed
import Submission.Work.FTS_EllLimOK.BoxReg
import Submission.Work.FTS.EllipticEst.Defs
import Submission.Work.Spaces.ProductTools

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS_EllLimOK

open Work.FTS.Galerkin (Fn)

set_option autoImplicit false

/-! ## Order-3 jet convergence -/

/-- Convergence of the `C³`-jets on the open quadrant. -/
def JConv3 (Ψn : ℕ → Fn) (Ψ : Fn) : Prop :=
  ∀ j i : ℕ, j + i ≤ 3 → ∀ z θ, (z, θ) ∈ Work.Construction.Qd →
    Tendsto (fun n => Work.Spaces.mixed j i (Ψn n) z θ) atTop
      (𝓝 (Work.Spaces.mixed j i Ψ z θ))

/-- `JConv3` implies `JConv`. -/
theorem JConv.of_JConv3 {Ψn : ℕ → Fn} {Ψ : Fn} (h : JConv3 Ψn Ψ) : JConv Ψn Ψ :=
  fun j i hji => h j i (le_trans hji (by norm_num))

/-! ## The Fatou package -/

/-- **The Fatou package of a pair (source, solution)**: the ellipticity law, `C³`-regularity on
`Qd`, and the honest `ℋ⁰`-memberships, `L²`-memberships and decay that the tree's uniqueness
theorem consumes.  These are exactly the non-smoothness fields of `EllipticEst.EllHyp 0` /
`EllHypN 0`, and they are what pins the limit down to the correct solution (they exclude the
homogeneous mode `z^{-5/α} sin 2θ`). -/
def FatouPkg (α : ℝ) (f Ψ : Fn) : Prop :=
  Work.FTS.StrongGlobal.IsBslSolPos α f Ψ ∧
  ContDiffOn ℝ 3 (Function.uncurry Ψ) Work.Construction.Qd ∧
  Work.Spaces.HkMem α 0 Ψ ∧
  Work.Spaces.HkMem α 0 (Work.Spaces.pth Ψ) ∧
  Work.Spaces.HkMem α 0 (Work.Spaces.pthIter 2 Ψ) ∧
  Work.Spaces.HkMem α 0 (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) ∧
  Work.Spaces.HkMem α 0 (fun z θ => Ψ z θ / Real.cos θ) ∧
  Work.Spaces.L2Mem (Work.Spaces.pthIter 2 Ψ) ∧
  Work.Spaces.L2Mem (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) ∧
  Work.Spaces.L2Mem (fun z θ => Ψ z θ / Real.cos θ) ∧
  Work.FTS.EllipticEst.ZDecay Ψ ∧
  BoxReg Ψ

theorem FatouPkg.sol {α : ℝ} {f Ψ : Fn} (h : FatouPkg α f Ψ) :
    Work.FTS.StrongGlobal.IsBslSolPos α f Ψ := h.1

theorem FatouPkg.contDiffOn {α : ℝ} {f Ψ : Fn} (h : FatouPkg α f Ψ) :
    ContDiffOn ℝ 3 (Function.uncurry Ψ) Work.Construction.Qd := h.2.1

/-! ## The order-3 limit vocabulary -/

/-- **`Ψ` is an order-`3` jet-cluster-limit of `E` along the sequence `fn`**: `Ψ` is in the Fatou
package for the limit profile `f`, and the `C³`-jets of `E (fn n)` converge to those of `Ψ` along
some cofinal reindexing. -/
def IsJetLimit3 (α : ℝ) (E : Fn → Fn) (fn : ℕ → Fn) (f Ψ : Fn) : Prop :=
  FatouPkg α f Ψ ∧
    ∃ σ : ℕ → ℕ, Tendsto σ atTop atTop ∧ JConv3 (fun n => E (fn (σ n))) Ψ

/-- **Order-3 closure of an operator** (the second half of `EllLimOK3`, with the Fatou package
replacing the bare `C³`): along every `LimSeq4`, the `C³`-jets of `E (fn n)` converge — *no
reindexing* — to an element of the Fatou package. -/
def ClosedE3 (α : ℝ) (E : Fn → Fn) : Prop :=
  ∀ (fn : ℕ → Fn) (f : Fn), LimSeq4 α fn f → ∃ Ψ : Fn, FatouPkg α f Ψ ∧ JConv3 (fun n => E (fn n)) Ψ

/-- **Obligation 1 at order 3 (compactness)**: along every `LimSeq4`, some cofinal reindexing of
the `C³`-jets converges, to a Fatou-package solution of the limit profile. -/
def ClosedCompact3 (α Ce : ℝ) : Prop :=
  ∀ E : Fn →ₗ[ℝ] Fn, HasPkg α Ce E → ∀ (fn : ℕ → Fn) (f : Fn), LimSeq4 α fn f →
    ∃ Ψ : Fn, IsJetLimit3 α E fn f Ψ

/-- **Obligation 2 at order 3 (uniqueness of the limit jets)**: two order-`3` jet-cluster-limits of
the same operator along the same sequence have the same `C³`-jets on the open quadrant.  (This is
the port of `EllipticEst.bslSol_unique_fts` to the `C³`-on-`Qd` class with the Fatou package — the
unique power-Cauchy–Euler mode `z^{-5/α} sin 2θ` is excluded by the package's bounds at `z = 0`.) -/
def ClosedUniq3 (α Ce : ℝ) : Prop :=
  ∀ E : Fn →ₗ[ℝ] Fn, HasPkg α Ce E → ∀ (fn : ℕ → Fn) (f : Fn), LimSeq4 α fn f →
    ∀ Ψ Ψ' : Fn, IsJetLimit3 α E fn f Ψ → IsJetLimit3 α E fn f Ψ' →
      ∀ j i : ℕ, j + i ≤ 3 → ∀ z θ, (z, θ) ∈ Work.Construction.Qd →
        Work.Spaces.mixed j i Ψ z θ = Work.Spaces.mixed j i Ψ' z θ

/-- **The analytic content of obligation 1 at order 3** — **RETIRED (2026-10-11)**: the far-field
rate `1/(1+z)` is *false* for class-`C` sources with `z^{-s}` tails, `s ∈ (1/2,3/2)`
(`sources/ftsV2/fts_ellimok_ruling.md` §1), so no package can supply this predicate.  The
replacement is `FatouH.LocalBoundH` (same shape, **constant** right-hand side), proved from
`HasPkg ∧ PkgCos` by `FatouH.localBoundH_of_hasPkgH`; the far-field decay of the limit is then
recovered by `Decay.decay_of_hkMem0_jetBound` (weighted membership + constant first-order bounds).
The definition is kept only because the inner (also retired) modules `ClosedCompact3_of_bounds_fatou`
and `SmallAssemblyG` still mention it. -/
def LocalBound4 (α Ce : ℝ) : Prop :=
  ∀ E : Fn →ₗ[ℝ] Fn, HasPkg α Ce E → ∀ (fn : ℕ → Fn) (f : Fn), LimSeq4 α fn f →
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, ∀ j i : ℕ, j + i ≤ 4 → ∀ z θ : ℝ,
      (z, θ) ∈ Work.Construction.Qd →
      |Work.Spaces.mixed j i (E (fn n)) z θ|
        ≤ C * (1 + 1 / z + 1 / (θ * (π / 2 - θ))) / (1 + z)

/-- `LocalBound4` implies `LocalBound` (fewer orders required). -/
theorem LocalBound.of_localBound4 {α Ce : ℝ} (h : LocalBound4 α Ce) : LocalBound α Ce :=
  fun E hE fn f hL => by
    obtain ⟨C, hC, hb⟩ := h E hE fn f hL
    exact ⟨C, hC, fun n j i hji => hb n j i (le_trans hji (by norm_num))⟩

/-! ## The order-3 limit closure (a verbatim copy of the lead's `FinalV2.EllLimOK3`) -/

/-- **The order-`3` limit closure** (ruling §G5): as `EllLimOK`, but the limit `E f` is `C³` on
`Qd` and the jets of order `≤ 3` converge.  *Verbatim copy* of `Work.FTS.FinalV2.EllLimOK3` (same
body ⇒ definitionally equal; `FinalCore.Lead_EllLimOK3_iff` is the bridge). -/
def EllLimOK3 (α : ℝ) (E : Fn → Fn) : Prop :=
  ∀ (fn : ℕ → Fn) (f : Fn) (B : ℝ),
    (∀ n, Work.FTS.ClassC.ClassC α (fn n)) →
    (∀ n, Work.FTS.StrongGlobal.Xn6 α (fn n) ≤ B) →
    ContDiffOn ℝ 4 (Function.uncurry f) Work.Construction.Qd →
    (∀ j i : ℕ, j + i ≤ 4 → ∀ z θ, (z, θ) ∈ Work.Construction.Qd →
      Tendsto (fun n => Work.Spaces.mixed j i (fn n) z θ) atTop
        (𝓝 (Work.Spaces.mixed j i f z θ))) →
    Work.FTS.StrongGlobal.IsBslSolPos α f (E f) ∧
    ContDiffOn ℝ 3 (Function.uncurry (E f)) Work.Construction.Qd ∧
    ∀ j i : ℕ, j + i ≤ 3 → ∀ z θ, (z, θ) ∈ Work.Construction.Qd →
      Tendsto (fun n => Work.Spaces.mixed j i (E (fn n)) z θ) atTop
        (𝓝 (Work.Spaces.mixed j i (E f) z θ))

/-- `EllLimOK3` implies `EllLimOK` (a stronger conclusion on a smaller jet range). -/
theorem EllLimOK3.toEllLimOK {α : ℝ} {E : Fn → Fn} (h : EllLimOK3 α E) :
    EllLimOK α E := by
  intro fn f B hC hB h4 hj
  obtain ⟨hlaw, -, hconv⟩ := h fn f B hC hB h4 hj
  exact ⟨hlaw, fun j i hji z θ hzθ => hconv j i (by omega) z θ hzθ⟩

/-! ## The small-α obligation shapes (the ruling's `∃ α₁ > 0, ∀ α ∈ (0, α₁], ∀ Ce, …`) -/

/-- **Obligation 1 at small α**: there is `α₁ > 0` such that for every `α ∈ (0, α₁]` and every
constant `Ce`, `E` is compact at order 3. -/
def SmallCompact3 : Prop :=
  ∃ α₁ : ℝ, 0 < α₁ ∧ ∀ α : ℝ, 0 < α → α ≤ α₁ → ∀ Ce : ℝ, ClosedCompact3 α Ce

/-- **Obligation 2 at small α**: there is `α₁ > 0` such that for every `α ∈ (0, α₁]` and every
constant `Ce`, the order-`3` limit jets are unique. -/
def SmallUniq3 : Prop :=
  ∃ α₁ : ℝ, 0 < α₁ ∧ ∀ α : ℝ, 0 < α → α ≤ α₁ → ∀ Ce : ℝ, ClosedUniq3 α Ce

/-- **The analytic content of obligation 1 at small α** — RETIRED with `LocalBound4`. -/
def SmallLocalBound4 : Prop :=
  ∃ α₁ : ℝ, 0 < α₁ ∧ ∀ α : ℝ, 0 < α → α ≤ α₁ → ∀ Ce : ℝ, LocalBound4 α Ce

/-- The five `ℋ⁰`-quantities that `FatouPkg` requires of a solution: `Ψ`, `∂_θΨ`, `∂_θ²Ψ`,
`z²∂_zzΨ` and `Ψ/cos θ` (the fields of `EllipticEst.EllHyp` that the uniqueness theorem consumes,
without the smoothness). -/
def HkBundleLists (α : ℝ) (Ψ : Fn) : List (Fn) :=
  [Ψ, Work.Spaces.pth Ψ, Work.Spaces.pthIter 2 Ψ,
    (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ), (fun z θ => Ψ z θ / Real.cos θ)]

/-- The five `ℋ⁰`-memberships of `HkBundleLists`. -/
def HkBundle (α : ℝ) (Ψ : Fn) : Prop :=
  Work.Spaces.HkMem α 0 Ψ ∧
  Work.Spaces.HkMem α 0 (Work.Spaces.pth Ψ) ∧
  Work.Spaces.HkMem α 0 (Work.Spaces.pthIter 2 Ψ) ∧
  Work.Spaces.HkMem α 0 (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) ∧
  Work.Spaces.HkMem α 0 (fun z θ => Ψ z θ / Real.cos θ)

/-- The five `ℋ⁰`-energies of `HkBundleLists`, uniformly bounded by `C` (outer integral). -/
def HkSqBundle (α : ℝ) (C : ℝ) (Ψ : Fn) : Prop :=
  Work.Spaces.HkSq α 0 Ψ ≤ C ∧
  Work.Spaces.HkSq α 0 (Work.Spaces.pth Ψ) ≤ C ∧
  Work.Spaces.HkSq α 0 (Work.Spaces.pthIter 2 Ψ) ≤ C ∧
  Work.Spaces.HkSq α 0 (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) ≤ C ∧
  Work.Spaces.HkSq α 0 (fun z θ => Ψ z θ / Real.cos θ) ≤ C

/-- The five `θ`-integral bounds of `HkBundleLists`, uniformly in `z ∈ Iz` and bounded by `C`
(so that Fatou in `θ` gives the limit's membership at *every* `z ∈ Iz`). -/
def ThetaBundle (α : ℝ) (C : ℝ) (Ψ : Fn) : Prop :=
  (∀ z ∈ Work.Spaces.Iz, (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 0 Ψ z θ) ≤ C) ∧
  (∀ z ∈ Work.Spaces.Iz,
    (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 0 (Work.Spaces.pth Ψ) z θ) ≤ C) ∧
  (∀ z ∈ Work.Spaces.Iz,
    (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 0 (Work.Spaces.pthIter 2 Ψ) z θ) ≤ C) ∧
  (∀ z ∈ Work.Spaces.Iz,
    (∫ θ in Work.Spaces.Iθ,
      Work.Spaces.HkIntegrand α 0 (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) z θ) ≤ C) ∧
  (∀ z ∈ Work.Spaces.Iz,
    (∫ θ in Work.Spaces.Iθ,
      Work.Spaces.HkIntegrand α 0 (fun z θ => Ψ z θ / Real.cos θ) z θ) ≤ C)

/-- **The box data of obligation 1** (the boundary/trace half of `FatouData`): on every closed box
`[a,b] × [0,π/2]` with `0 < a ≤ b` the sequence along a `LimSeq4` converges to a limit `G` which
is jointly `C²` on the box and which vanishes on the two angular boundary lines.

This is the sequence-level form of the closed-quadrant regularity on boxes away from `z = 0`
that elliptic regularity supplies for the paper's solutions (`FTS_EllLimOK.BoxReg`); it is the
hypothesis that makes the `θ`-boundary terms of the uniqueness argument (`Lzero_self_form`,
`Lzero_orthogonal`, `angQ_ge`) vanish, and it is *not* a consequence of the integral memberships
of `FatouData`, which are stated with weights integrable at the angular endpoints.  The bridge
from primitive uniform estimates to this predicate is `FTS_EllLimOK.BoxReg_of_uniform`. -/
def BoxData (α Ce : ℝ) : Prop :=
  ∀ E : Fn →ₗ[ℝ] Fn, HasPkg α Ce E → ∀ (fn : ℕ → Fn) (f : Fn), LimSeq4 α fn f →
    ∀ a b : ℝ, 0 < a → a ≤ b → ∃ G : Fn,
      ContDiffOn ℝ 2 (Function.uncurry G) (cbox a b) ∧
      (∀ z ∈ Set.Icc a b, ∀ θ ∈ Set.Icc 0 (π / 2),
        Tendsto (fun n => E (fn n) z θ) atTop (𝓝 (G z θ))) ∧
      (∀ z ∈ Set.Icc a b, G z 0 = 0 ∧ G z (π / 2) = 0)

/-- **The sequence-level Fatou data of obligation 1** (the correction the order-3 review forced):
`LocalBound4` gives the convergence and the `C³`-regularity of a cluster limit, but *not* the
limit's `FatouPkg`, because
* `HkMem α 0 G` is a *lower* vanishing condition at `z = 0` (no pointwise upper bound supplies it),
* `ZDecay Ψ` needs the order-`≤ 2` jets to be `o(1/z)` — a decay exponent `> 1`, stronger than the
  `1/(1+z)` of `LocalBound4` — and
* the `L²`-memberships are integrability statements of their own.

This predicate is what the packages must supply: along every `LimSeq4`, uniformly in `n`, the five
`ℋ⁰`-memberships, their uniform `θ`- and `z`-integral bounds, the `L²`-memberships, the decay
rate `|D_z^j D_θ^i Ψ_n| ≤ C (1+z)^{-3/2}` for `j + i ≤ 2` (which gives `z²·jet² ≤ C²z²/(1+z)³ → 0`,
i.e. `ZDecay`, for the limit), and the closed-box regularity `BoxData`. -/
def FatouData (α Ce : ℝ) : Prop :=
  (∀ E : Fn →ₗ[ℝ] Fn, HasPkg α Ce E → ∀ (fn : ℕ → Fn) (f : Fn), LimSeq4 α fn f →
    ∃ C : ℝ, 0 < C ∧
      (∀ n, HkBundle α (E (fn n))) ∧
      (∀ n, HkSqBundle α C (E (fn n))) ∧
      (∀ n, ThetaBundle α C (E (fn n))) ∧
      (∀ n, Work.Spaces.L2Mem (Work.Spaces.pthIter 2 (E (fn n)))) ∧
      (∀ n, Work.Spaces.L2Mem (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 (E (fn n)) z θ)) ∧
      (∀ n, Work.Spaces.L2Mem (fun z θ => E (fn n) z θ / Real.cos θ)) ∧
      (∀ n j i : ℕ, j + i ≤ 2 → ∀ z θ, (z, θ) ∈ Work.Construction.Qd →
        (1 + z) ^ (3 / 2 : ℝ) * |Work.Spaces.mixed j i (E (fn n)) z θ| ≤ C)) ∧
  BoxData α Ce

/-- At small α, the Fatou data. -/
def SmallFatouData : Prop :=
  ∃ α₁ : ℝ, 0 < α₁ ∧ ∀ α : ℝ, 0 < α → α ≤ α₁ → ∀ Ce : ℝ, FatouData α Ce

/-- At small α, `SmallLocalBound4` gives the order-`3` bound of `Defs.LocalBound`. -/
theorem SmallLocalBound4.to_localBound {h : SmallLocalBound4} :
    ∃ α₁ : ℝ, 0 < α₁ ∧ ∀ α : ℝ, 0 < α → α ≤ α₁ → ∀ Ce : ℝ, LocalBound α Ce := by
  obtain ⟨α₁, hα₁, h⟩ := h
  exact ⟨α₁, hα₁, fun α hα hαle Ce => LocalBound.of_localBound4 (h α hα hαle Ce)⟩

end Work.FTS_EllLimOK
