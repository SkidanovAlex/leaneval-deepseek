/-
Copyright: work module for the Elgindi finite-time singularity project.

# `Submission/Work/FTS/StrongEps/EpsE4Thr/AprioriHalves.lean` — `AprioriP` is the conjunction of two halves

`EpsE4Thr/Reduction.AprioriP` is the two-clause sub-horizon a-priori bound of the projected
`ε`-scheme.  Its proof splits into two *independent* barrier arguments, which this module records
as separate `Prop`s so that each can be produced (and consumed) on its own:

* `AprioriPSixth α ρ ε T Φs E g₀ M` — the `ℋ⁶`-clause `Xn6 α (slice g τ) ≤ M`.  The route is
  assembled in `EpsE4Thr/AprioriSixth*.lean` (E3P's energy facts + the transfer of the profile +
  the two `ε`-controls); its conclusion is the explicit bound
  `√(A(1+K7²)(1+E0)e^{ΛT'})`, so this half is a one-line consequence of `apriori_sixth_scheme`.
* `AprioriPFourth α ρ ε T Φs E g₀ C₀` — the small-ball clause
  `Xn α (slice (JfamP ρ ε g) τ) ≤ C₀ α²`.  This half needs the barrier argument for the
  level-four energy of the *mollified* family, i.e. a coercive pairing (`Work.FTS.Nonlin.UnifIP`:
  `clo HkSq₄ ≤ IP α x x ≤ Cup HkSq₄`, `cc HkSq₄ ≤ IP α (𝓛x) x`, `|IP α f g| ≤ Ccs Xn f Xn g`) with
  the `ε`-**perturbation** `|IP α (J_ε w) x − IP α w x| ≤ Ccs ‖J_ε w − w‖₄ Xn x ≤ C ε (…) Xn x`
  absorbed for small `ε`.  The barrier engine itself is proved
  (`Work.FTS.Apriori.barrier_within`, the one used by `StrongGlobal.Apriori.apriori_strong`), and
  the level-four norm rows are available (`Work.FTS.Nonlinear.n4norm_exists`); what is missing is
  the coercive pairing (no inhabitation theorem in the tree, and it is not a hypothesis of
  `EpsE4Thr` — see the owner message in `StrongEps/NOTES.md`, item (B)).

`AprioriP_of_halves` assembles `AprioriP` from the two; it is the exact place where a producer of
either half plugs in.

Everything here is `sorry`-free (it is pure bookkeeping).
-/
import Mathlib.Basic.Real.Basic
import Mathlib.Order.Filter.Defs
import Submission.Work.FTS.StrongEps.EpsE4Thr.Reduction

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

set_option autoImplicit false
set_option linter.unusedVariables false

/-- The **`ℋ⁶`-half** of `AprioriP`: the datum's `ℋ⁶`-size bound implies the `ℋ⁶`-size bound of
the raw slices along every regular `P₀`-solution on any `[0,T']`, `T' ≤ T`. -/
def AprioriPSixth (α : ℝ) (ρ : ℝ × ℝ → ℝ) (ε T : ℝ) (Φs : Fn) (E : Fn → Fn) (g₀ : Fn)
    (M : ℝ) : Prop :=
  Work.FTS.StrongGlobal.Xn6 α g₀ ≤ M →
    ∀ T' : ℝ, 0 < T' → T' ≤ T → ∀ g : Fam, IsEpsSolP α ρ ε T' Φs E g₀ g →
      EpsRegP α ρ ε T' g →
      ∀ τ ∈ Set.Icc 0 T', Work.FTS.StrongGlobal.Xn6 α (slice g τ) ≤ M

/-- The **small-ball half** of `AprioriP`: the datum's small-ball condition implies the small-ball
bound for the projected mollified slices along every regular `P₀`-solution on any `[0,T']`,
`T' ≤ T`. -/
def AprioriPFourth (α : ℝ) (ρ : ℝ × ℝ → ℝ) (ε T : ℝ) (Φs : Fn) (E : Fn → Fn) (g₀ : Fn)
    (C₀ : ℝ) : Prop :=
  Work.FTS.Nonlin.Xn α (Pz (Jeps ρ ε g₀)) ≤ C₀ * α ^ 2 →
    ∀ T' : ℝ, 0 < T' → T' ≤ T → ∀ g : Fam, IsEpsSolP α ρ ε T' Φs E g₀ g →
      EpsRegP α ρ ε T' g →
      ∀ τ ∈ Set.Icc 0 T',
        Work.FTS.Nonlin.Xn α (slice (JfamP ρ ε g) τ) ≤ C₀ * α ^ 2

/-- **`AprioriP` is the conjunction of its two halves.** -/
theorem AprioriP_of_halves {α M C₀ : ℝ} {ρ : ℝ × ℝ → ℝ} {ε T : ℝ} {Φs : Fn} {E : Fn → Fn}
    {g₀ : Fn} (h6 : AprioriPSixth α ρ ε T Φs E g₀ M)
    (h4 : AprioriPFourth α ρ ε T Φs E g₀ C₀) :
    AprioriP α ρ ε T Φs E g₀ C₀ M :=
  fun hg₀M hsmall₀ T' hT' hT'le g hsol hreg τ hτ =>
    ⟨h6 hg₀M T' hT' hT'le g hsol hreg τ hτ,
      h4 hsmall₀ T' hT' hT'le g hsol hreg τ hτ⟩

/-! ## Why there is no converse

`AprioriP ⟹ AprioriPSixth` is **not** available: to evaluate `AprioriP` at the `ℋ⁶`-half one must
supply the datum's *small-ball* condition, and the only place it appears in `AprioriP`'s own
conclusion is at `τ = 0` — reading it off requires applying `AprioriP` again, i.e. the argument is
circular.  The two halves are therefore genuinely *independent inputs* of the clause, not
projections of it; that is exactly why the barrier argument must be run **jointly** (each half's
hypothesis is the other's conclusion along the flow). -/

end Work.FTS.StrongEps.EpsE4Thr
