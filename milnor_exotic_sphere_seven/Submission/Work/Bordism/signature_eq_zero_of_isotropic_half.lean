import Mathlib
import Submission.Work.SignatureBordism.Signature

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# A form with an isotropic subspace of half the dimension has signature zero

Let `Q` be a quadratic form on a finite-dimensional vector space `V` over a linearly ordered field
`𝕜` (for us always `𝕜 = ℚ`), whose associated bilinear form `B = associated Q` is **non-degenerate**
(the radical of `Q` is trivial: `hrad`).  Let `K ≤ V` be **totally isotropic** — `Q` vanishes on
`K` (`hK`) — with

```lean
2 * finrank 𝕜 K = finrank 𝕜 V        -- `hfin`
```

i.e. exactly half the dimension of `V`.  Then

```lean
Work.SignatureBordism.signature Q = 0.
```

## The argument

Write `p = sigPos Q`, `n = sigNeg Q`, `k = finrank 𝕜 K` and `m = finrank 𝕜 V`.

1. Since the radical is trivial, `p + n = m` (`hsum`).  Indeed, `radical Q = ker (associated Q)`
   (`QuadraticMap.radical_eq_ker_associated`) and `hrad` says precisely that this kernel vanishes,
   so Mathlib's `QuadraticForm.sigPos_add_sigNeg_add_radical` gives `p + n + 0 = m`.
2. `p + k ≤ m` (`hpos`) and `n + k ≤ m` (`hneg`), by
   `QuadraticForm.sigPos_add_finrank_le_of_nonpos` applied to `Q`, respectively to `-Q`, on `K`
   (where the form is `≤ 0` because it *vanishes* there, `hK`).  The dual statement for `-Q` uses
   `sigPos (-Q) = sigNeg Q`.
3. `m ≤ 2k` is exactly `hfin`.

From `p + k ≤ m = p + n` we get `k ≤ n`; from `n + k ≤ m = p + n` we get `k ≤ p`; and from
`m ≤ 2k`, `m = p + n` with `p, n ≥ k` we get `p = n = k`; hence `signature Q = p - n = 0`.

This is the *algebraic core* of the statement that a closed oriented manifold bounds: a compact
`4k`-manifold `X` with boundary has middle intersection form carrying a Lagrangian (the image of the
relative cohomology `H^{2k}(X, ∂X) → H^{2k}(X)`, which is totally isotropic of half the dimension),
and such a form has signature `0`.  It is also the algebraic ingredient of the bordism invariance of
the signature.  It is the same argument as `Work.SignatureBordism.signature_of_isLagrangian`, except
that the half-dimension hypothesis is supplied directly (`hfin`) rather than through the equality
`K = Kᗮ` of `K` with its own orthogonal complement.
-/

namespace Work.Bordism

open QuadraticMap

/-- **A non-degenerate quadratic form with an isotropic subspace of half the dimension has
signature zero.**

Here `hK` says that `K` is totally isotropic (`Q` vanishes on `K`), `hrad` that the associated
bilinear form is non-degenerate, and `hfin` that `K` has exactly half the dimension of `V`.  The
result is `signature Q = 0`. -/
theorem signature_eq_zero_of_isotropic_half {𝕜 V : Type*} [Field 𝕜] [LinearOrder 𝕜]
    [IsStrictOrderedRing 𝕜] [Invertible (2 : 𝕜)] [AddCommGroup V] [Module 𝕜 V]
    [FiniteDimensional 𝕜 V] (Q : QuadraticForm 𝕜 V) (K : Submodule 𝕜 V)
    (hK : ∀ x ∈ K, Q x = 0)
    (hrad : ∀ x : V, (∀ y : V, QuadraticMap.associated Q x y = 0) → x = 0)
    (hfin : 2 * Module.finrank 𝕜 ↥K = Module.finrank 𝕜 V) :
    Work.SignatureBordism.signature Q = 0 := by
  -- The radical of `Q` is trivial, because it is the kernel of `associated Q` and `hrad` says
  -- that this kernel vanishes.
  have hrad_bot : Q.radical = ⊥ := by
    rw [QuadraticMap.radical_eq_ker_associated]
    rw [Submodule.eq_bot_iff]
    intro x hx
    rw [LinearMap.mem_ker] at hx
    exact hrad x (fun y => by simpa using congrArg (fun g => g y) hx)
  -- Hence `sigPos Q + sigNeg Q = finrank V` (Sylvester's law of inertia).
  have hsum : sigPos Q + sigNeg Q = Module.finrank 𝕜 V := by
    have h := QuadraticForm.sigPos_add_sigNeg_add_radical (Q := Q)
    rw [hrad_bot] at h
    rw [finrank_bot] at h
    omega
  -- The positive and negative definite parts are disjoint from `K`, since `Q` vanishes on `K`.
  have hpos : sigPos Q + Module.finrank 𝕜 ↥K ≤ Module.finrank 𝕜 V :=
    QuadraticForm.sigPos_add_finrank_le_of_nonpos (Q := Q) (fun x hx => by rw [hK x hx])
  have hneg : sigNeg Q + Module.finrank 𝕜 ↥K ≤ Module.finrank 𝕜 V := by
    have h := QuadraticForm.sigPos_add_finrank_le_of_nonpos (Q := -Q)
      (fun x hx => by rw [neg_apply, hK x hx, neg_zero])
    rwa [sigPos_neg] at h
  -- `K` has half the dimension of `V` (`hfin`), and `p + n = m`, forcing `p = n`.
  have hps : sigPos Q = sigNeg Q := by omega
  simp [Work.SignatureBordism.signature, hps]

end Work.Bordism
