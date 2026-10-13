/-
Copyright: work module for the Elgindi finite-time singularity project.

# `Submission/Work/FTS/StrongEps/EpsE4Thr/AprioriSixthBound.lean` — the `ℋ⁶`-clause of `AprioriP`

`EpsE4Thr/AprioriSixth.lean` proves the algebraic core `apriori_sixth`: once the E3P energy
facts, the level-six loop `HkSq α 6 x ≤ e` and the *combined* transfer of the profile are given,
the `ℋ⁶`-size of the *raw* slices is bounded by the explicit number
`√(2(1+K7²)(1+E0) e^{Λ T'})`.

This module turns that core into the form in which the `AprioriP`-bootstrap consumes it:

* `HkSq_le_IP6` — the loop `HkSq α 6 f ≤ IP6 1 … 1 α f f` for an honest `HQo α 6` profile (the
  proved `IP6_lo_coeffs` at `α₂ = 1`);
* `apriori_sixth_bound` — the same conclusion as `apriori_sixth`, with

  - the derivative input given in the **one-sided** form `HasDerivWithinAt … (Ici 0)` in which
    E3P's `hid` delivers it (the two-sided form at interior points is recovered from it),
  - the level-six loop taken from the *class* of the projected slice
    (`HQo α 6 (slice (JfamP ρ ε g) τ)`, which `EpsDatumP`'s class-`C` conjunct supplies) instead
    of as a hypothesis about `e`.

`E0` is the datum's energy bound (`EpsE4Thr/epsEnergy6Q_zero_le` produces it as
`C0 · (K α²)²` from `h6 : Xn6 α g₀ ≤ K α²`; the point of separating it is recorded in the header
of `AprioriSixth.lean`).

Everything here is `sorry`-free.
-/
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.Normed.Order.Lattice
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.FTS.StrongEps.EpsE4Thr.AprioriSixth

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.EpsE4Thr

open Work.FTS.Galerkin (Fn Fam slice)
open Work.FTS.StrongGlobal (Xn6)

set_option autoImplicit false
set_option linter.unusedVariables false

/-- **The level-six loop**: for an honest `HQo α 6` profile, the squared `ℋ⁶`-norm is dominated by
the diagonal of the concrete pairing `IP6 1 … 1`.  This is `IP6_lo_coeffs` at `α₂ = 1`. -/
theorem HkSq_le_IP6 {α : ℝ} (hα : α ∈ Set.Ioc 0 1) {f : Fn}
    (hsm : Work.FTS.EllipticEst.SmoothOpen f) (hmem : Work.Spaces.HkMem α 6 f) :
    Work.Spaces.HkSq α 6 f
      ≤ Work.FTS.StrongPersist.IP6 1 1 1 1 1 1 1 1 1 1 α f f :=
  Work.FTS.StrongPersist.IP6_lo_coeffs (α₂ := 1) one_pos
    le_rfl le_rfl le_rfl le_rfl le_rfl le_rfl le_rfl le_rfl le_rfl le_rfl α hα f ⟨hsm, hmem⟩

/-- **The `ℋ⁶`-clause of `AprioriP`, in the form E3P delivers its inputs.**

Same conclusion as `AprioriSixth.apriori_sixth`, but

* the derivative input is the *one-sided* `HasDerivWithinAt … (Set.Ici 0)` that E3P's `hid`
  provides (at interior points it converts to a two-sided `HasDerivAt`),
* the level-six loop `HkSq α 6 x ≤ e` is taken from the honest-`ℋ⁶` class of the projected slice
  (`EpsDatumP`'s class-`C` conjunct gives `HQo α 6 (slice (JfamP ρ ε g) τ)`),
* the `hM`-slot is filled by the explicit number, so the conclusion is a concrete bound on
  `Xn6 α (slice g τ)`. -/
theorem apriori_sixth_bound {α Λ K7 A E0 : ℝ} {ρ : ℝ × ℝ → ℝ} {Φs : Fn} {E : Fn → Fn}
    {ε T T' : ℝ} {g : Fam}
    (hT' : 0 < T') (hT'le : T' ≤ T) (hΛ : 0 ≤ Λ) (hK7 : 0 ≤ K7) (hA : 0 ≤ A)
    (hE0 : 0 ≤ E0) (hα : 0 < α) (hα1 : α ≤ 1)
    (hid : ∀ τ ∈ Set.Ioo 0 T',
      HasDerivWithinAt (epsEnergy6Q α ρ ε g) (epsEnergy6Qdot α ρ ε Φs E g τ) (Set.Ici 0) τ)
    (hΛb : ∀ τ ∈ Set.Ioo 0 T',
      epsEnergy6Qdot α ρ ε Φs E g τ ≤ Λ * (1 + epsEnergy6Q α ρ ε g τ))
    (hcont : ContinuousOn (epsEnergy6Q α ρ ε g) (Set.Icc 0 T'))
    (he0 : epsEnergy6Q α ρ ε g 0 ≤ E0)
    (hloQ : ∀ τ ∈ Set.Icc 0 T',
      Work.FTS.VocabO.HQo α 6 (slice (JfamP ρ ε g) τ))
    (htr : ∀ τ ∈ Set.Icc 0 T', Work.Spaces.HkSq α 6 (slice g τ)
      ≤ A * Work.Spaces.HkSq α 6 (slice (JfamP ρ ε g) τ)
        + A * K7 ^ 2 * (1 + epsEnergy6Q α ρ ε g τ)) :
    ∀ τ ∈ Set.Icc 0 T', Xn6 α (slice g τ)
      ≤ Real.sqrt (A * (1 + K7 ^ 2) * (1 + E0) * Real.exp (Λ * T')) := by
  refine apriori_sixth hT' hT'le hΛ hK7 hA hE0 ?_ hΛb hcont he0 ?_ htr le_rfl
  · intro τ hτ
    exact (hid τ hτ).hasDerivAt (Ici_mem_nhds hτ.1)
  · intro τ hτ
    obtain ⟨hsm, hmem⟩ := hloQ τ hτ
    exact HkSq_le_IP6 ⟨hα, hα1⟩ hsm hmem

end Work.FTS.StrongEps.EpsE4Thr
