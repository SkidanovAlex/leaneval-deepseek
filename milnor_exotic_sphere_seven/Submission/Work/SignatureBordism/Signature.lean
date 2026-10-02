import Mathlib

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The signature of a quadratic form

This is the algebraic core of the *signature* half of the dimension-`8` Hirzebruch chapter: for a
quadratic form `Q` over a linearly ordered field `𝕜` (for us always `𝕜 = ℚ`), its **signature** is
the difference of the maximal dimension of a subspace on which `Q` is positive definite and of the
maximal dimension of a subspace on which `Q` is negative definite.

```lean
def signature (Q : QuadraticForm 𝕜 V) : ℤ := (sigPos Q : ℤ) - (sigNeg Q : ℤ)
```

## Conventions

* `sigPos`/`sigNeg` are Mathlib's `QuadraticMap.sigPos`/`QuadraticMap.sigNeg`, whose basic
  properties (Sylvester's law of inertia, `sigPos_of_equiv_weightedSumSquares`, and the additivity
  identity `sigPos Q + sigNeg Q + finrank (radical Q) = finrank V`) are proved in
  `Mathlib.LinearAlgebra.QuadraticForm.Signature`.
* Note that `Module.finrank 𝕜 V = 0` when `V` is infinite dimensional, so `sigPos Q = 0` for every
  form on an infinite dimensional space.  All the interesting statements therefore carry a
  spanning hypothesis `Submodule.span 𝕜 {v} = ⊤` (which forces finite-dimensionality) or an
  explicit `FiniteDimensional` hypothesis.

## Main results

* `Work.SignatureBordism.signature_neg` — `σ(-Q) = -σ(Q)` (reversing the orientation of a manifold
  negates its signature);
* `Work.SignatureBordism.signature_eq_of_equiv` — isometric forms have the same signature
  (Sylvester's law of inertia);
* `Work.SignatureBordism.signature_of_span_singleton_pos`,
  `Work.SignatureBordism.signature_of_span_singleton_neg` — the computation of the signature of a
  form on a space spanned by a single vector `v` with `Q v = a`, `a ≠ 0`: the signature is `±1`.
  This is the *only* computation which the closed `8`-manifold `X` needs.
-/

set_option backward.isDefEq.respectTransparency false

namespace Work.SignatureBordism

open QuadraticMap

noncomputable section

variable {𝕜 V W : Type*}

/-- **The signature of a quadratic form** over a linearly ordered field: the number of positive
directions minus the number of negative directions, `sigPos Q - sigNeg Q`, as an integer. -/
def signature [Field 𝕜] [LinearOrder 𝕜] [AddCommGroup V] [Module 𝕜 V]
    (Q : QuadraticForm 𝕜 V) : ℤ :=
  (sigPos Q : ℤ) - (sigNeg Q : ℤ)

section Basic

variable [Field 𝕜] [LinearOrder 𝕜] [AddCommGroup V] [Module 𝕜 V] [AddCommGroup W] [Module 𝕜 W]

/-- **The signature changes sign under `Q ↦ -Q`.**  Geometrically: the intersection form of a
closed oriented manifold changes sign when the orientation is reversed, so `σ(-M) = -σ(M)`. -/
@[simp] theorem signature_neg (Q : QuadraticForm 𝕜 V) : signature (-Q) = -signature Q := by
  simp only [signature, sigPos_neg, sigNeg_neg]
  ring

/-- **The signature of a weighted sum of squares**: the number of positive weights minus the
number of negative weights (a direct consequence of Mathlib's
`QuadraticMap.sigPos_weightedSumSquares`/`sigNeg_weightedSumSquares`). -/
theorem signature_weightedSumSquares {ι : Type*} [Fintype ι] [IsStrictOrderedRing 𝕜]
    (w : ι → 𝕜) :
    signature (weightedSumSquares 𝕜 w) =
      (({i | 0 < w i}.ncard : ℤ) - ({i | w i < 0}.ncard : ℤ)) := by
  simp only [signature, QuadraticForm.sigPos_weightedSumSquares,
    QuadraticForm.sigNeg_weightedSumSquares]

/-- **Sylvester's law of inertia, signature form**: isometric quadratic forms have the same
signature. -/
theorem signature_eq_of_equiv {Q : QuadraticForm 𝕜 V} {Q' : QuadraticForm 𝕜 W}
    (h : Equivalent Q Q') : signature Q = signature Q' := by
  simp only [signature, QuadraticMap.Equivalent.sigPos_eq h, QuadraticMap.Equivalent.sigNeg_eq h]

/-- Equal quadratic forms have equal signature. -/
theorem signature_congr {Q Q' : QuadraticForm 𝕜 V} (h : Q = Q') : signature Q = signature Q' := by
  rw [h]

/-- `signature` is invariant under a linear isometry equivalence, in the form of a rewrite rule for
a form transported along `LinearEquiv`. -/
theorem signature_comp_linearEquiv (Q : QuadraticForm 𝕜 W) (e : V ≃ₗ[𝕜] W) :
    signature (Q.comp (e : V →ₗ[𝕜] W)) = signature Q := by
  refine signature_eq_of_equiv ?_
  exact ⟨QuadraticMap.IsometryEquiv.mk e (fun m => rfl)⟩

end Basic

/-! ## The signature of a form on a subsingleton module

The one degenerate case in which the signature is computed without any linear algebra: if the
module carrying the form is a subsingleton (as is the middle cohomology of an even-dimensional
sphere in the middle degree), every form on it is the zero form and the signature vanishes.  This
is what makes the disc bordism in `Submission/Work/SignatureBordism/DiscBordism.lean` give
`σ(S^{2k}) = 0`. -/

section Subsingleton

variable {𝕜 V : Type*} [Field 𝕜] [LinearOrder 𝕜] [AddCommGroup V] [Module 𝕜 V]

/-- The positive index of a quadratic form on a subsingleton module vanishes. -/
lemma sigPos_eq_zero_of_subsingleton (Q : QuadraticForm 𝕜 V) [Subsingleton V] : sigPos Q = 0 :=
  le_antisymm (by
    calc sigPos Q ≤ Module.finrank 𝕜 V := sigPos_le_finrank Q
      _ = 0 := Module.finrank_zero_of_subsingleton) (Nat.zero_le _)

/-- The negative index of a quadratic form on a subsingleton module vanishes. -/
lemma sigNeg_eq_zero_of_subsingleton (Q : QuadraticForm 𝕜 V) [Subsingleton V] : sigNeg Q = 0 := by
  have h : sigPos (-Q) = 0 := sigPos_eq_zero_of_subsingleton (-Q)
  rwa [sigPos_neg] at h

/-- **The signature of a quadratic form on a subsingleton module is zero.** -/
theorem signature_eq_zero_of_subsingleton (Q : QuadraticForm 𝕜 V) [Subsingleton V] :
    signature Q = 0 := by
  rw [signature, sigPos_eq_zero_of_subsingleton Q, sigNeg_eq_zero_of_subsingleton Q]
  norm_num

end Subsingleton

end

end Work.SignatureBordism
