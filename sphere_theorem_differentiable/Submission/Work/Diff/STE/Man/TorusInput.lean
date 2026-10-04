/-
# The manifold layer: the flat Cauchy theorem as consumed by the geometric layer

The flat analytic core of the short-time existence proof is proved in
`Submission/Work/Diff/STE/TorusCauchy.lean` as `Work.Diff.STE.flat.torus_cauchy_symm`, whose
statement is `Work.Diff.STE.Flat.TorusShortTimeExistenceSymm`.  That module is (at the time of
writing) still under construction, and the geometric layer must be able to refer to its statement.

This file therefore records a *copy of the statement* under the name
`Work.Diff.STE.Man.FlatCauchySymm`; nothing is lost: `FlatCauchySymm n` and
`TorusShortTimeExistenceSymm n` are the same proposition, and once the flat module builds, the
bridging lemma

  `Work.Diff.STE.Man.flatCauchySymm_of_torus` : `TorusShortTimeExistenceSymm n → FlatCauchySymm n`

is a one-line term.  Everything in the geometric layer is stated with `FlatCauchySymm` as an
explicit hypothesis, so that it does not depend on the (incomplete) flat module.
-/
import Mathlib
import Submission.Work.Diff.STE.Man.Defs
import Submission.Work.Diff.STE.TorusCauchy

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Diff.STE.Man

/-- **The flat Cauchy theorem, in the form consumed by the geometric layer.**  Identical to
`Work.Diff.STE.Flat.TorusShortTimeExistenceSymm`: a DeTurck-shaped, conjugation-equivariant
nonlinearity that maps symmetric jets to symmetric values, applied to a smooth, `1`-periodic, real,
positive definite initial datum, has a smooth, `1`-periodic, real, symmetric, positive definite
solution on some `[0, T)`. -/
def FlatCauchySymm (n : ℕ) : Prop :=
  ∀ (Φ : (Fin n → ℝ) × Work.Diff.STE.Flat.Jet n → Work.Diff.STE.Flat.MatC n),
    Work.Diff.STE.Flat.IsDeTurckNonlin Φ → Work.Diff.STE.Flat.ConjEquivNonlin Φ →
    (∀ (x : Fin n → ℝ) (A : Work.Diff.STE.Flat.MatC n)
        (L : Fin n → Work.Diff.STE.Flat.MatC n)
        (B : Fin n → Fin n → Work.Diff.STE.Flat.MatC n),
      (∀ i j, A i j = A j i) → (∀ c i j, L c i j = L c j i) →
      (∀ c d i j, B c d i j = B c d j i) → (∀ c d, B c d = B d c) →
      ∀ i j, Φ (x, (A, L, B)) i j = Φ (x, (A, L, B)) j i) →
    ∀ u₀ : Work.Diff.STE.Flat.Torus n, ContDiff ℝ (⊤ : ℕ∞) u₀ → Work.Diff.STE.Periodic1 u₀ →
      (∀ x i j, (u₀ x i j).im = 0) → (∀ x, Work.Diff.STE.Flat.PosDefM (u₀ x)) →
      ∃ T : ℝ, 0 < T ∧ ∃ u : ℝ → Work.Diff.STE.Flat.Torus n,
        Work.Diff.STE.Flat.SolvesOn Φ T u ∧ u 0 = u₀ ∧
        (∀ t ∈ Set.Ico (0 : ℝ) T, ∀ x, Work.Diff.STE.Flat.PosDefM (u t x)) ∧
        (∀ t ∈ Set.Ico (0 : ℝ) T, ∀ x i j, (u t x i j).im = 0) ∧
        (∀ t ∈ Set.Ico (0 : ℝ) T, ∀ x i j, u t x i j = u t x j i)

/-- The bridging lemma: the flat Cauchy theorem of `TorusCauchy.lean`
(`Work.Diff.STE.flat.TorusShortTimeExistenceSymm`) *is* the proposition `FlatCauchySymm` used by
the geometric layer — the two definitions are syntactically the same statement. -/
theorem flatCauchySymm_of_torus (n : ℕ)
    (h : Work.Diff.STE.flat.TorusShortTimeExistenceSymm n) : FlatCauchySymm n := h

/-- **The flat Cauchy theorem, unconditionally**: the diamond of the flat analytic core,
`Work.Diff.STE.flat.torus_cauchy_symm`, transported to the vocabulary of this file.  Consumers in
the manifold layer may now call `flatCauchySymm n` instead of assuming `FlatCauchySymm n`. -/
theorem flatCauchySymm (n : ℕ) : FlatCauchySymm n :=
  flatCauchySymm_of_torus n (Work.Diff.STE.flat.torus_cauchy_symm n)

end Work.Diff.STE.Man
