import Mathlib
import Submission.Work.Whitney.Stability
import Submission.Work.Whitney.ChernProduct

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option linter.unusedSectionVars false

/-!
# The two classical inputs of the Whitney formula, and their exact statements

`README.md` §6 reduces the Whitney sum formula

  `c_k(E ⊕ F) = Σ_{i+j=k} c_i(E) ⌣ c_j(F)`

to exactly two inputs, neither of which is available in this workspace yet.  This module states them
precisely, as `Prop`s, so that

* a theorem of the form `SplitsOffLine → TopClassMul → (the Whitney formula)` can be written with a
  *named*, checkable hypothesis (instead of an anonymous one), and
* a next stretch knows exactly what to prove (and with which extra hypothesis: `(S)` is *false*
  over an arbitrary topological base — see the module docstring of `SectionStability.lean` and
  `README.md` §6 — and true, by a Hermitian metric, over a paracompact base).

## (S) `Work.Whitney.SplitsOffLine`

*A nowhere-zero section splits off a trivial line, at the level of bundles.*  For every complex
gluing-data bundle `V` of rank `m+1` in the standard fibre over every base, and every continuous
nowhere-zero section `σ` of `V`, there is an isomorphism

  `V ≅ σ^*(Q_V) ⊕ ε¹`,

where `Q_V = Work.Thom.tautQuotient V` is the tautological quotient over `V∖0` and `σ^*(Q_V)` its
pullback along `σ`.  The class-level shadow of (S) — the only part used in the *low* degrees — is
proved unconditionally in `Submission/Work/Whitney/SectionStability.lean`
(`Work.Whitney.chernClass_eq_of_nowhereZeroSection`).

## (T) `Work.Whitney.TopClassMul`

*The top Chern class is multiplicative under direct sums*, i.e. the Euler class of a direct sum of
oriented real bundles is the product of the Euler classes: for complex bundles `E` (rank `m`) and
`F` (rank `n`),

  `c_{m+n}(E ⊕ F) = c_m(E) ⌣ c_n(F)`.

Both formulations agree with `README.md` §6: for complex bundles the top Chern class *is* the Euler
class of the realification (`Work.Thom.chernClass_succ_top'`).

## The reduction, and its exact extent

The reduction of the Whitney formula recorded in `README.md` §6 is **not** complete from (S) and (T)
alone, and this was confirmed by two independent reviews of the naive conditional statement
`SplitsOffLine → TopClassMul → (the formula)`: the degrees `max(m,n) ≤ k ≤ m+n-1` are not reachable
from them.  Concretely, for two complex line bundles `L₁, L₂` the descent over `X_{L₁} = L₁∖0` gives
only `π^*(c₁(L₁⊕L₂) - c₁(L₁) - c₁(L₂)) = 0`, i.e. (by the Gysin exactness of
`Work.Thom.gysin_exact_at_base`) `c₁(L₁⊕L₂) - c₁(L₁) - c₁(L₂) ∈ ℤ·c₁(L₁)`; symmetrically it lies in
`ℤ·c₁(L₂)`, and neither membership forces it to vanish when `c₁(L₁) = c₁(L₂) = x ≠ 0`.

What (S) *does* give, unconditionally, is the **low-degree part**: for `k ≤ max(m,n) - 1` the
Whitney formula follows from (S) (through its class-level shadow
`Work.Whitney.chernClass_eq_of_nowhereZeroSection`), the induction hypothesis for the pairs
`(m, n-1)` and `(m-1, n)`, and the injectivity of `π_E^*`/`π_F^*`
(`Work.Thom.bijective_proj_zeroComplementA`) — `README.md` §6 items 1.

The missing ingredient for the intermediate degrees is a *separation* statement of Leray–Hirsch
type: to conclude an identity on `X_{E⊕F}` from its restrictions to the two pieces
`{f ≠ 0} ⊔ {f = 0}`, one needs the restriction map `H^k(X_{E⊕F}) → H^k{f ≠ 0} ⊕ H^k{f = 0}` to be
injective on the classes of interest.  It is **not** injective for an arbitrary pair (open, closed
complement) — the review of the naive statement produced the standard counterexample
`X = S¹`, `A` an open arc: `H¹(S¹) = ℤ` while both halves are contractible — which is why the
classical proof of the Whitney formula goes through the flag bundle and Leray–Hirsch, exactly as
`Submission/Work/Thom/README.md` (ADDENDUM 23.5 item 2) anticipated.

## What this module provides

* `Work.Whitney.SplitsOffLine` and `Work.Whitney.TopClassMul`: the two inputs, named and stated.
* `Work.Whitney.topClassMul_apply`: (T) in the form of the single top summand of the Whitney
  formula, which is the top-degree case of the formula and the only place (T) enters.
-/

namespace Work.Whitney

open Work.TangentClasses Work.Thom

noncomputable section

/-- **(S)**: every nowhere-zero section of a complex bundle splits off a trivial line, at the level
of bundles.  This is the bundle-level form of "a nowhere-zero section splits off a line"; it is
proved in the literature from a Hermitian metric (equivalently, over a paracompact base), and it is
**false** for a completely arbitrary topological base (see `README.md` §6).  Its class-level shadow
is `Work.Whitney.chernClass_eq_of_nowhereZeroSection`. -/
def SplitsOffLine : Prop :=
  ∀ {B : Type} [TopologicalSpace B] {ι : Type} [Fintype ι] {m : ℕ}
    (V : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin (m + 1))) ι)
    (σ : C(B, ↥(zeroComplement (realification V))))
    (hσ : ∀ b, ((σ b : ↥(zeroComplement (realification V))) :
      (realification V).TotalSpace).1 = b)
    {ι₀ : Type} [Inhabited ι₀],
    Nonempty (BundleIso V
      (whitneySum (bundleComap (tautQuotient V) σ)
        (trivialVectorBundleCore ℂ B (EuclideanSpace ℂ (Fin 1)) ι₀)))

/-- **(T)**: the top Chern class is multiplicative under direct sums (equivalently, the Euler class
of a direct sum of complex bundles is the product of the Euler classes of the summands; the classical
proof is "the Thom class of a sum is the product of the Thom classes", which needs a relative cross
product / Künneth for the cohomology of a product). -/
def TopClassMul : Prop :=
  ∀ {B : Type} [TopologicalSpace B] {ι₁ ι₂ : Type} [Fintype ι₁] [Fintype ι₂] {m n : ℕ}
    (E : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι₁)
    (F : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin n)) ι₂),
    chernClass (m + n) (m + n) (whitneySum E F)
      = cupChern m n (chernClass m m E) (chernClass n n F)

/-- `TopClassMul` in the "un-normalised" degree, i.e. with the right-hand side in `H^{2(m+n)}`. -/
theorem topClassMul_apply (h : TopClassMul) {B : Type} [TopologicalSpace B] {ι₁ ι₂ : Type}
    [Fintype ι₁] [Fintype ι₂] {m n : ℕ}
    (E : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι₁)
    (F : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin n)) ι₂) :
    chernClass (m + n) (m + n) (whitneySum E F) = chernSummand E F m n := by
  exact h E F

end

end Work.Whitney
