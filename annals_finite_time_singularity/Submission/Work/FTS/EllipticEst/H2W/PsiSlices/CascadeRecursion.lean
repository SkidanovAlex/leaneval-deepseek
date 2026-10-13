import Mathlib.Algebra.EuclideanDomain.Basic
import Mathlib.Algebra.EuclideanDomain.Field
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Submission.Work.Spaces.Defs
import Submission.Work.Elliptic.Defs
import Submission.Work.FTS.EllipticEst.StraightDefs
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.FTS.EllipticEst.H2W.PropH2Base
import Submission.Work.FTS.EllipticEst.H2W.lzeroSliceFiber
import Submission.Work.FTS.EllipticEst.TT.bslOp_DzIter_eq
import Submission.Work.FTS.EllipticEst.TT.HkMem_descend_open
import Submission.Work.FTS.EllipticEst.Cert.SmoothOpen_bslOp
import Submission.Work.FTS.EllipticEst.remov.SmoothOpen_bslOp_of_smoothOpen
import Submission.Work.FTS.EllipticEst.H2W.WeakPureAux.cascadeSourceless
import Submission.Work.FTS.EllipticEst.Cores.Pieces.TL2.shiftZeroSlots

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `H2W/PsiSlices/CascadeRecursion` — the cascade recursion for class-legal data

The amplitude balance of the level tower at `θ = π/2` (`(1-N²)·B = α²z²·B₂ + α(5+α)z·B₁`, from
`WeakPureAux.cascadeBalance` / `cascadeBalance_sourceless`), transported to the radial shifts of a
weak-class datum, where the class makes the source `ℋ⁰`-honest for the levels `m ≤ 2`:

* `hkMem_zero_DzIter_source` — `HkMem α 2 F` implies `HkMem α 0 (D_z^m F)` for `m ≤ 2`;
* `contDiffOn_slice_DzIter_psi` — the `θ`-slice of a radial shift is `C^∞` on `(0, π/2)`;
* **`cascadeRecursion`** — the level-`m` (`m ≤ 2`) amplitude balance for a class datum;
* **`cascadeAmpZero_level`** — a nonzero order-`N` (`N ≥ 2`) amplitude of the level-`m` slice
  (`m ≤ 2`) is incompatible with the order-`N` amplitudes of its two `z`-derivatives existing;
* **`cascadeAscentStep`** / **`cascadeAscentStepLevel`** — the top-order step: with `B ≠ 0`, the
  order-`(N+2)` amplitude of `D_z^{m+1} Ψ` or of `D_z^{m+2} Ψ` is nonzero.

See `PsiSlices/NOTES_pzIterSliceIntegrable_addendum3.md` §5 for what these prove collectively
(the amplitude world is asymmetric; the iteration stops at level `2`, where the class's source
honesty ends).
-/

namespace Work.FTS.EllipticEst.H2W.PsiSlices

open scoped Real Topology
open MeasureTheory Set Filter

set_option autoImplicit false

noncomputable section

/-! ## The cascade recursion at the radial shifts of a class datum

`H2W/WeakPureAux/cascadeBalance.lean` and `cascadeSourceless.lean` prove the amplitude balance of
the tower at `θ = π/2` for a datum whose *source* is `ℋ⁰`-honest:

  `(1 - N²)·B = α²z²·B₂ + α(5+α)z·B₁`   (`N ≥ 2`),

`B` being the order-`N` amplitude of the slice and `B₁`, `B₂` the order-`(N+2)` amplitudes of its
two `z`-derivatives.  For the *weak class* that source honesty is available only at the levels
`m ≤ 2` (`HkMem α 2 F` implies `HkMem α 0 (D_z^m F)` there), and the level-`m` equation is that of
the shifted datum `(D_z^m F, D_z^m Ψ)` (`TT.bslOp_DzIter_eq`).  This section records the resulting
*class-level* recursion — the object the cascade analysis of `WeakPureAux/NOTES_cascade.md` runs
on — together with the level-`m` "no isolated higher-order amplitude" statement: a nonzero
order-`N` (`N ≥ 2`) amplitude at level `m ≤ 2` forces the order-`N` amplitudes of the two
neighbouring slices to *fail to exist*.  (The remaining two ingredients of the cascade — the
*ascent* along the levels and the *summability obstruction* — are recorded as the next steps in
`NOTES_pzIterSliceIntegrable_addendum3.md`.) -/

/-- **The shifted sources are `ℋ⁰`-honest at the levels the class controls.**  `HkMem α 2 F`
implies `HkMem α 0 (D_z^m F)` for `m ≤ 2`: the level-`0` integrand of `D_z^m F` is one summand of
the level-`2` integrand of `F`. -/
theorem hkMem_zero_DzIter_source {α : ℝ} {F Ψ : ℝ → ℝ → ℝ} (hα : 0 < α) (hα4 : α ≤ 1 / 4)
    (h : Work.FTS.EllipticEst.WeakPos2 α F Ψ) {m : ℕ} (hm : m ≤ 2) :
    Work.Spaces.HkMem α 0 (Work.Spaces.DzIter m F) := by
  have hFsm : Work.FTS.EllipticEst.SmoothOpen F :=
    Work.FTS.EllipticEst.Cert.smoothOpen_congr_bsl
      (Work.FTS.EllipticEst.remov.SmoothOpen_bslOp_of_smoothOpen (α := α)
        (Work.FTS.EllipticEst.smoothOpen_of_forall h.2.2.2.2.2.2.1))
      (fun z' θ hz' hθ0 hθ1 => h.1 z' hz' θ hθ0 hθ1)
  have hdesc := Work.FTS.EllipticEst.Cores.Pieces.TL2.hkMem_dzIter_le (α := α) (k := 2)
    hFsm h.2.2.2.2.2.2.2 m hm
  exact Work.FTS.EllipticEst.TT.HkMem_descend_open (k := 0) (l := 2 - m) (Nat.zero_le _)
    ((Work.FTS.EllipticEst.smoothOpen_iff_forall _).mp (hFsm.DzIter m)) hdesc

/-- The `θ`-slice of a radial shift of an open-quadrant-smooth datum is `C^∞` on `(0, π/2)`. -/
theorem contDiffOn_slice_DzIter_psi {Ψ : ℝ → ℝ → ℝ}
    (hΨ : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry Ψ)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2))) {z : ℝ} (hz : 0 < z) (m : ℕ) :
    ∀ n : ℕ, ContDiffOn ℝ n (fun θ : ℝ => Work.Spaces.DzIter m Ψ z θ)
      (Set.Ioo (0 : ℝ) (Real.pi / 2)) := by
  have hso : Work.FTS.EllipticEst.SmoothOpen Ψ :=
    Work.FTS.EllipticEst.smoothOpen_of_forall hΨ
  have hcur := (hso.DzIter m).curry_θ hz
  intro n
  exact (contDiffOn_iff_forall_nat_le.mp hcur) n le_top

/-- **The cascade recursion at the levels the class controls (`m ≤ 2`).**  For a weak-class datum
the level-`m` slice satisfies the amplitude balance of the tower, with *no* hypothesis beyond the
existence of the amplitudes: the source's order-`(N+2)` amplitude is then provably `0`
(`sourceAmp_vanishes`, applied to the shifted source `D_z^m F`, which is `ℋ⁰`-honest by
`hkMem_zero_DzIter_source`).  This is the recursion the cascade analysis runs on. -/
theorem cascadeRecursion {α : ℝ} {F Ψ : ℝ → ℝ → ℝ} (hα : 0 < α) (hα4 : α ≤ 1 / 4)
    (h : Work.FTS.EllipticEst.WeakPos2 α F Ψ) {z : ℝ} (hz : 0 < z) {m : ℕ} (hm : m ≤ 2)
    {N : ℕ} (hN : 2 ≤ N) {B B₁ B₂ c : ℝ}
    (h0 : Filter.Tendsto (fun θ : ℝ => (Real.pi / 2 - θ) ^ N * Work.Spaces.DzIter m Ψ z θ)
      (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds B))
    (h1 : Filter.Tendsto (fun θ : ℝ => (Real.pi / 2 - θ) ^ (N + 1) *
        deriv (fun θ' : ℝ => Work.Spaces.DzIter m Ψ z θ') θ)
      (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds ((N : ℝ) * B)))
    (h2 : Filter.Tendsto (fun θ : ℝ => (Real.pi / 2 - θ) ^ (N + 2) *
        deriv (fun s : ℝ => deriv (fun θ' : ℝ => Work.Spaces.DzIter m Ψ z θ') s) θ)
      (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2)))
      (nhds ((N : ℝ) * ((N : ℝ) + 1) * B)))
    (hB₁ : Filter.Tendsto (fun θ : ℝ => (Real.pi / 2 - θ) ^ (N + 2)
        * Work.Spaces.pz (Work.Spaces.DzIter m Ψ) z θ)
      (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds B₁))
    (hB₂ : Filter.Tendsto (fun θ : ℝ => (Real.pi / 2 - θ) ^ (N + 2)
        * Work.Spaces.pzIter 2 (Work.Spaces.DzIter m Ψ) z θ)
      (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds B₂))
    (hlimG : Filter.Tendsto (fun θ : ℝ => (Real.pi / 2 - θ) ^ (N + 2)
        * Work.Spaces.DzIter m F z θ)
      (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds c)) :
    (1 - (N : ℝ) ^ 2) * B = α ^ 2 * z ^ 2 * B₂ + α * (5 + α) * z * B₁ := by
  have hFsm : Work.FTS.EllipticEst.SmoothOpen F :=
    Work.FTS.EllipticEst.Cert.smoothOpen_congr_bsl
      (Work.FTS.EllipticEst.remov.SmoothOpen_bslOp_of_smoothOpen (α := α)
        (Work.FTS.EllipticEst.smoothOpen_of_forall h.2.2.2.2.2.2.1))
      (fun z' θ hz' hθ0 hθ1 => h.1 z' hz' θ hθ0 hθ1)
  refine Work.FTS.EllipticEst.H2W.WeakPureAux.cascadeBalance_sourceless (α := α)
    (G := Work.Spaces.DzIter m F) (Φ := Work.Spaces.DzIter m Ψ) (z := z) hz
    (hFsm.DzIter m) (hkMem_zero_DzIter_source hα hα4 h hm) hN ?_ ?_
    h0 h1 h2 hB₁ hB₂ hlimG
  · intro z' hz' θ hθ0 hθ1
    exact Work.FTS.EllipticEst.TT.bslOp_DzIter_eq α F Ψ m h.2.2.2.2.2.2.1 h.1 z' hz' θ hθ0 hθ1
  · exact contDiffOn_slice_DzIter_psi h.2.2.2.2.2.2.1 hz m

/-- **No isolated higher-order amplitude at the levels the class controls (`m ≤ 2`).**  If the
level-`m` slice has an amplitude `B` at order `N ≥ 2`, and the two neighbouring slices
(`∂_z(D_z^mΨ)`, `∂_z²(D_z^mΨ)`) have *order-`N`* amplitudes `A₁`, `A₂`, then `B = 0`.
Contrapositive: a nonzero order-`N` amplitude of the level-`m` slice (`m ≤ 2`) forces the
order-`N` amplitudes of the two neighbouring slices to fail to exist (or to be infinite) — the
mechanism by which the cascade can only start from a power-like behaviour. -/
theorem cascadeAmpZero_level {α : ℝ} {F Ψ : ℝ → ℝ → ℝ} (hα : 0 < α) (hα4 : α ≤ 1 / 4)
    (h : Work.FTS.EllipticEst.WeakPos2 α F Ψ) {z : ℝ} (hz : 0 < z) {m : ℕ} (hm : m ≤ 2)
    {N : ℕ} (hN : 2 ≤ N) {B B₁ B₂ c A₁ A₂ : ℝ}
    (h0 : Filter.Tendsto (fun θ : ℝ => (Real.pi / 2 - θ) ^ N * Work.Spaces.DzIter m Ψ z θ)
      (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds B))
    (h1 : Filter.Tendsto (fun θ : ℝ => (Real.pi / 2 - θ) ^ (N + 1) *
        deriv (fun θ' : ℝ => Work.Spaces.DzIter m Ψ z θ') θ)
      (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds ((N : ℝ) * B)))
    (h2 : Filter.Tendsto (fun θ : ℝ => (Real.pi / 2 - θ) ^ (N + 2) *
        deriv (fun s : ℝ => deriv (fun θ' : ℝ => Work.Spaces.DzIter m Ψ z θ') s) θ)
      (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2)))
      (nhds ((N : ℝ) * ((N : ℝ) + 1) * B)))
    (hB₁ : Filter.Tendsto (fun θ : ℝ => (Real.pi / 2 - θ) ^ (N + 2)
        * Work.Spaces.pz (Work.Spaces.DzIter m Ψ) z θ)
      (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds B₁))
    (hB₂ : Filter.Tendsto (fun θ : ℝ => (Real.pi / 2 - θ) ^ (N + 2)
        * Work.Spaces.pzIter 2 (Work.Spaces.DzIter m Ψ) z θ)
      (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds B₂))
    (hlimG : Filter.Tendsto (fun θ : ℝ => (Real.pi / 2 - θ) ^ (N + 2)
        * Work.Spaces.DzIter m F z θ)
      (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds c))
    (hA₁ : Filter.Tendsto (fun θ : ℝ => (Real.pi / 2 - θ) ^ N
        * Work.Spaces.pz (Work.Spaces.DzIter m Ψ) z θ)
      (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds A₁))
    (hA₂ : Filter.Tendsto (fun θ : ℝ => (Real.pi / 2 - θ) ^ N
        * Work.Spaces.pzIter 2 (Work.Spaces.DzIter m Ψ) z θ)
      (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds A₂)) :
    B = 0 := by
  have hFsm : Work.FTS.EllipticEst.SmoothOpen F :=
    Work.FTS.EllipticEst.Cert.smoothOpen_congr_bsl
      (Work.FTS.EllipticEst.remov.SmoothOpen_bslOp_of_smoothOpen (α := α)
        (Work.FTS.EllipticEst.smoothOpen_of_forall h.2.2.2.2.2.2.1))
      (fun z' θ hz' hθ0 hθ1 => h.1 z' hz' θ hθ0 hθ1)
  refine Work.FTS.EllipticEst.H2W.WeakPureAux.cascadeAmp_zero_of_radialAmp_exists (z := z) hz
    (hFsm.DzIter m) (hkMem_zero_DzIter_source hα hα4 h hm) hN ?_ ?_
    h0 h1 h2 hB₁ hB₂ hlimG hA₁ hA₂
  · intro z' hz' θ hθ0 hθ1
    exact Work.FTS.EllipticEst.TT.bslOp_DzIter_eq α F Ψ m h.2.2.2.2.2.2.1 h.1 z' hz' θ hθ0 hθ1
  · exact contDiffOn_slice_DzIter_psi h.2.2.2.2.2.2.1 hz m

/-- **The ascent step of the cascade** (the "top-order step" at the levels the class controls).

For a weak-class datum, `z > 0` and `m ≤ 2`: if the level-`m` slice has a *nonzero* amplitude `B`
at order `N ≥ 2`, and the order-`(N+2)` amplitudes `B₁`, `B₂` of its two `z`-derivatives and `c`
of the shifted source *exist*, then `B₁ ≠ 0` or `B₂ ≠ 0`: the nonzero amplitude can only move to
the *next* level, at order `N+2`.

Note the complementarity with `cascadeAmpZero_level`: there the *order-`N`* amplitudes of the two
neighbouring slices were assumed to exist — which, together with `B ≠ 0`, is in fact *impossible*
(`amp_next_vanishes` kills their order-`(N+2)` amplitudes, and then the balance forces `B = 0`).
Here nothing is assumed about the neighbours' order-`N` amplitudes, which is exactly why the
statement carries information.  Since the source honesty used by `cascadeRecursion` is available
only for `m ≤ 2`, the iteration of this step beyond the levels `3, 4` requires the missing
`ℋ⁰`-honesty of `D_z^ℓ F` for `ℓ ≥ 3` (see `NOTES_pzIterSliceIntegrable_addendum3.md`). -/
theorem cascadeAscentStep {α : ℝ} {F Ψ : ℝ → ℝ → ℝ} (hα : 0 < α) (hα4 : α ≤ 1 / 4)
    (h : Work.FTS.EllipticEst.WeakPos2 α F Ψ) {z : ℝ} (hz : 0 < z) {m : ℕ} (hm : m ≤ 2)
    {N : ℕ} (hN : 2 ≤ N) {B B₁ B₂ c : ℝ} (hB : B ≠ 0)
    (h0 : Filter.Tendsto (fun θ : ℝ => (Real.pi / 2 - θ) ^ N * Work.Spaces.DzIter m Ψ z θ)
      (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds B))
    (h1 : Filter.Tendsto (fun θ : ℝ => (Real.pi / 2 - θ) ^ (N + 1) *
        deriv (fun θ' : ℝ => Work.Spaces.DzIter m Ψ z θ') θ)
      (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds ((N : ℝ) * B)))
    (h2 : Filter.Tendsto (fun θ : ℝ => (Real.pi / 2 - θ) ^ (N + 2) *
        deriv (fun s : ℝ => deriv (fun θ' : ℝ => Work.Spaces.DzIter m Ψ z θ') s) θ)
      (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2)))
      (nhds ((N : ℝ) * ((N : ℝ) + 1) * B)))
    (hB₁ : Filter.Tendsto (fun θ : ℝ => (Real.pi / 2 - θ) ^ (N + 2)
        * Work.Spaces.pz (Work.Spaces.DzIter m Ψ) z θ)
      (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds B₁))
    (hB₂ : Filter.Tendsto (fun θ : ℝ => (Real.pi / 2 - θ) ^ (N + 2)
        * Work.Spaces.pzIter 2 (Work.Spaces.DzIter m Ψ) z θ)
      (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds B₂))
    (hlimG : Filter.Tendsto (fun θ : ℝ => (Real.pi / 2 - θ) ^ (N + 2)
        * Work.Spaces.DzIter m F z θ)
      (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds c)) :
    B₁ ≠ 0 ∨ B₂ ≠ 0 := by
  have hbal := cascadeRecursion hα hα4 h hz hm hN h0 h1 h2 hB₁ hB₂ hlimG
  have hne : (1 - (N : ℝ) ^ 2) * B ≠ 0 := by
    refine mul_ne_zero ?_ hB
    have h2N : (2 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
    nlinarith
  by_contra hcon
  push_neg at hcon
  obtain ⟨hb1, hb2⟩ := hcon
  rw [hbal, hb1, hb2] at hne
  simp at hne

/-- **The level form of the ascent step.**  `cascadeAscentStep` gives `B₁ ≠ 0 ∨ B₂ ≠ 0` for the
order-`(N+2)` amplitudes of the two *derivatives* `pz (D_z^m Ψ)`, `pzIter 2 (D_z^m Ψ)`.  Since
`D_z^{m+1} Ψ = z·pz (D_z^m Ψ)` (definitionally) and
`z²·pzIter 2 (D_z^m Ψ) = D_z^{m+2} Ψ − D_z^{m+1} Ψ` (`H2W.lzsf_DzIter_two_eq`), the same
conclusion reads: the order-`(N+2)` amplitude of `D_z^{m+1} Ψ` or that of `D_z^{m+2} Ψ` is nonzero.
This is the form in which the ascent is iterated along the levels. -/
theorem cascadeAscentStepLevel {α : ℝ} {F Ψ : ℝ → ℝ → ℝ} (hα : 0 < α) (hα4 : α ≤ 1 / 4)
    (h : Work.FTS.EllipticEst.WeakPos2 α F Ψ) {z : ℝ} (hz : 0 < z) {m : ℕ} (hm : m ≤ 2)
    {N : ℕ} (hN : 2 ≤ N) {B : ℝ} (hB : B ≠ 0)
    (h0 : Filter.Tendsto (fun θ : ℝ => (Real.pi / 2 - θ) ^ N * Work.Spaces.DzIter m Ψ z θ)
      (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds B))
    (h1 : Filter.Tendsto (fun θ : ℝ => (Real.pi / 2 - θ) ^ (N + 1) *
        deriv (fun θ' : ℝ => Work.Spaces.DzIter m Ψ z θ') θ)
      (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds ((N : ℝ) * B)))
    (h2 : Filter.Tendsto (fun θ : ℝ => (Real.pi / 2 - θ) ^ (N + 2) *
        deriv (fun s : ℝ => deriv (fun θ' : ℝ => Work.Spaces.DzIter m Ψ z θ') s) θ)
      (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2)))
      (nhds ((N : ℝ) * ((N : ℝ) + 1) * B)))
    {B₁ B₂ : ℝ}
    (hB₁ : Filter.Tendsto (fun θ : ℝ => (Real.pi / 2 - θ) ^ (N + 2)
        * Work.Spaces.DzIter (m + 1) Ψ z θ)
      (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds B₁))
    (hB₂ : Filter.Tendsto (fun θ : ℝ => (Real.pi / 2 - θ) ^ (N + 2)
        * Work.Spaces.DzIter (m + 2) Ψ z θ)
      (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds B₂))
    (hlimG : ∃ c : ℝ, Filter.Tendsto (fun θ : ℝ => (Real.pi / 2 - θ) ^ (N + 2)
        * Work.Spaces.DzIter m F z θ)
      (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds c)) :
    B₁ ≠ 0 ∨ B₂ ≠ 0 := by
  have hso : Work.FTS.EllipticEst.SmoothOpen Ψ :=
    Work.FTS.EllipticEst.smoothOpen_of_forall h.2.2.2.2.2.2.1
  have hA₁ : Filter.Tendsto (fun θ : ℝ => (Real.pi / 2 - θ) ^ (N + 2)
      * Work.Spaces.pz (Work.Spaces.DzIter m Ψ) z θ)
      (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds (B₁ / z)) := by
    refine Filter.Tendsto.congr (fun θ => ?_) (hB₁.div_const z)
    have hid : Work.Spaces.DzIter (m + 1) Ψ z θ
        = z * Work.Spaces.pz (Work.Spaces.DzIter m Ψ) z θ := rfl
    show (Real.pi / 2 - θ) ^ (N + 2) * Work.Spaces.DzIter (m + 1) Ψ z θ / z
      = (Real.pi / 2 - θ) ^ (N + 2) * Work.Spaces.pz (Work.Spaces.DzIter m Ψ) z θ
    rw [hid]; field_simp
  have hA₂ : Filter.Tendsto (fun θ : ℝ => (Real.pi / 2 - θ) ^ (N + 2)
      * Work.Spaces.pzIter 2 (Work.Spaces.DzIter m Ψ) z θ)
      (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds ((B₂ - B₁) / z ^ 2)) := by
    have hmem : ∀ᶠ θ in nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2)),
        θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) := by
      filter_upwards [self_mem_nhdsWithin,
        nhdsWithin_le_nhds (isOpen_Ioi.mem_nhds (half_pos Real.pi_pos))] with θ hθ hθ0
      exact ⟨hθ0, hθ⟩
    refine Filter.Tendsto.congr' ?_ ((hB₂.sub hB₁).div_const (z ^ 2))
    filter_upwards [hmem] with θ hθ
    have hid := Work.FTS.EllipticEst.H2W.lzsf_DzIter_two_eq (Work.Spaces.DzIter m Ψ)
      ((hso.DzIter m).hasDerivAt_slice_pzIter 1 hθ hz)
    have e1 : Work.Spaces.DzIter 2 (Work.Spaces.DzIter m Ψ) z θ
        = Work.Spaces.DzIter (m + 2) Ψ z θ := rfl
    have e2 : Work.Spaces.DzIter 1 (Work.Spaces.DzIter m Ψ) z θ
        = Work.Spaces.DzIter (m + 1) Ψ z θ := rfl
    rw [e1, e2] at hid
    have hz2 : z ^ 2 * Work.Spaces.pzIter 2 (Work.Spaces.DzIter m Ψ) z θ
        = Work.Spaces.DzIter (m + 2) Ψ z θ - Work.Spaces.DzIter (m + 1) Ψ z θ := by
      linarith [hid]
    have hnum : (Real.pi / 2 - θ) ^ (N + 2) * Work.Spaces.DzIter (m + 2) Ψ z θ
        - (Real.pi / 2 - θ) ^ (N + 2) * Work.Spaces.DzIter (m + 1) Ψ z θ
        = (Real.pi / 2 - θ) ^ (N + 2)
          * (z ^ 2 * Work.Spaces.pzIter 2 (Work.Spaces.DzIter m Ψ) z θ) := by
      have h1 : (Real.pi / 2 - θ) ^ (N + 2) * Work.Spaces.DzIter (m + 2) Ψ z θ
          - (Real.pi / 2 - θ) ^ (N + 2) * Work.Spaces.DzIter (m + 1) Ψ z θ
          = (Real.pi / 2 - θ) ^ (N + 2)
            * (Work.Spaces.DzIter (m + 2) Ψ z θ - Work.Spaces.DzIter (m + 1) Ψ z θ) := by
        ring
      rw [h1, ← hz2]
    rw [hnum, mul_div_assoc, mul_div_cancel_left₀ _ (pow_ne_zero 2 (ne_of_gt hz))]
  obtain ⟨c, hc⟩ := hlimG
  rcases cascadeAscentStep hα hα4 h hz hm hN hB h0 h1 h2 hA₁ hA₂ hc with hs | hs
  · by_cases hb1 : B₁ = 0
    · exact absurd (hs (by rw [hb1]; simp)) (not_false)
    · exact Or.inl hb1
  · by_cases hb1 : B₁ = 0
    · refine Or.inr fun hb2 => absurd (hs ?_) (not_false)
      rw [hb2, hb1]; ring
    · exact Or.inl hb1

end
end Work.FTS.EllipticEst.H2W.PsiSlices
