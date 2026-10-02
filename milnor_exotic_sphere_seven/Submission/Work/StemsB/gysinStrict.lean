import Mathlib
import Submission.Work.Serre.Engine
import Submission.Work.Stems.c2EvenStepLocal

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# The boundary case of `SerreE3b`, and why the C2 even step does not need it

`Work.Serre.SerreE3b` asserts the Gysin isomorphism `x ↦ x ⌣ e` in the range `m + r + 1 ≤ N + 1`,
where `N` bounds the *fibre's* knowledge.  In the two-line degeneration of the Serre spectral
sequence this range is delicate exactly at the top degree `m + r + 1 = N + 1`: the convergence
`H_t(E) = 0` gives `E^∞_{p,q} = 0` for `p + q > 0` (each `E^∞` term is a *subquotient* of `H_{p+q}(E)`,
so the fibre's *unknown* homology in degree `N+1` is harmless), and that yields the **surjectivity**
of the transgression at the top, but the **injectivity** there needs the fibre's vanishing in degree
`N+1` (or an equivalent argument).  The intended proof of `SerreE3b` — the cell-by-cell disc-pair
Thom class, `Work.Serre.DiscPairRelCohIso` + multiplicativity — is *not* affected by this, because it
runs on the long exact sequence of the pair `(D, S)` rather than on the spectral sequence.

This file isolates the *weaker* range, `m + r + 1 ≤ N` (one degree of slack), as
`Work.StemsB.SerreE3bStrict`, and records the arithmetic which shows that the C2 free-top even step
(`Work.Stems.evenStepLocal`) consumes `SerreE3b` only in that *strict* range:

in that proof `T := (N - 1) - c * (2j - 1)` is the largest degree in which the cohomology of the
model is computed, `SerreE3b` is applied with fibre parameter `N' := T - 1`, and the periodicity is
used at the degrees `d < N - c * (2j)` required by `EvenClause`.  Hence the strongest instance used
is `d + 1 ≤ T = N' + 1`, i.e. `m + r + 1 ≤ N' + 1` with `m = d - 2j`; and since
`T - (N - c*(2j) - 1) = c ≥ 1`, the top degree `d = T` is *never* reached.  So `SerreE3bStrict`
suffices — in particular the allowance `c = 3` used by
`Work.Stems.c2oddFree_three` has two degrees of slack.

**Consequence.**  Proving `Work.StemsB.SerreE3bStrict` instead of `SerreE3b` is *enough* for the
stable-stems contract **for every allowance `c ≥ 1`** (via the port `Work.StemsB.evenStepLocalStrict`,
the statement isolated for the fleet in this file), and it is the form that the spectral-sequence
argument does deliver.  The hypothesis `1 ≤ c` is *necessary*: at `c = 0` the clause's top degree
`d = N - 1` meets the excluded boundary `m + r + 1 = N' + 1` — both reviewers of the delegation
independently caught this — while the consumer `Work.Stems.c2oddFree_three` uses `c = 3` with two
degrees of slack.
-/

open CategoryTheory CategoryTheory.Limits

namespace Work.StemsB

noncomputable section

/-- **The fibre-range Gysin / Euler-class theorem with one degree of slack**: same as
`Work.Serre.SerreE3b` but with the range `m + r + 1 ≤ N` instead of `m + r + 1 ≤ N + 1`. -/
def SerreE3bStrict : Prop :=
  ∀ (E B : Type) [TopologicalSpace E] [TopologicalSpace B] (p : C(E, B)) (e₀ : E) (r N : ℕ),
    1 ≤ r → Work.StemsB.IsSerreFibration p → SimplyConnectedSpace B → Work.Serre.RatAcyclic E →
      (∀ t : ℕ, 0 < t → t ≠ r → t ≤ N →
        IsZero (Work.Serre.ratH (TopCat.of (Work.RatHurewicz.homotopyFibre p e₀)) t)) →
      Nonempty (Work.Serre.ratH (TopCat.of (Work.RatHurewicz.homotopyFibre p e₀)) r ≅
        ModuleCat.of ℚ ℚ) →
      ∀ m : ℕ, m + r + 1 ≤ N →
        ∃ e : Work.Serre.ratCoh (TopCat.of B) (r + 1),
          IsIso (ModuleCat.ofHom (Work.Serre.cupWith (TopCat.of B) (r + 1) e m))

/-- The full range implies the strict range (trivially). -/
theorem serreE3bStrict_of_serreE3b (h : Work.Serre.SerreE3b) : SerreE3bStrict :=
  fun E B _ _ p e₀ r N hr hp hB hE hfib hgen m hm =>
    h E B p e₀ r N hr hp hB hE hfib hgen m (by omega)

/-- **The arithmetic of the boundary**: in `Work.Stems.evenStepLocal` with allowance `c ≥ 1`, every
degree `d` at which the periodicity is consumed satisfies `d + 1 ≤ T`, i.e. it stays one degree below
the top of the range `SerreE3b` is asserted in.  Hence the boundary case `m + r + 1 = N + 1` is never
used. -/
theorem slack_of_evenStepLocal (c j N d : ℕ) (hc : 1 ≤ c) (hj : 1 ≤ j)
    (hd : d < N - c * (2 * j)) :
    d + 1 ≤ (N - 1) - c * (2 * j - 1) := by
  have h1 : d + c * (2 * j) < N := by omega
  have h2 : c * (2 * j) = c * (2 * j - 1) + c := by
    rw [← Nat.mul_succ]; congr 1; omega
  omega

-- **The port is proved elsewhere.**  The statement isolated here (`evenStepLocalStrict`,
-- the verbatim port of `Work.Stems.evenStepLocal` to `SerreE3bStrict` with the sharp hypothesis
-- `1 <= c`) is proved in module `Submission.Work.StemsB.evenStepLocalStrict` (no `sorry`, axioms
-- `{propext, Classical.choice, Quot.sound}`); it cannot be imported here because that module
-- imports this one for `SerreE3bStrict`.  See `Submission/Work/StemsB/rh3Strict.lean` for the
-- instantiated hedge.

#print axioms Work.StemsB.serreE3bStrict_of_serreE3b
#print axioms Work.StemsB.slack_of_evenStepLocal

end

end Work.StemsB
