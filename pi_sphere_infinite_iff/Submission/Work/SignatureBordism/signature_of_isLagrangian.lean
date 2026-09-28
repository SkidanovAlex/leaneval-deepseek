import Mathlib
import Submission.Work.SignatureBordism.Signature

/-!
# A quadratic form with a Lagrangian has signature zero

Let `Q` be a quadratic form on a finite-dimensional vector space `V` over a linearly ordered field
`𝕜` (for us always `𝕜 = ℚ`), with associated bilinear form `B = associated Q`.  A subspace
`K ≤ V` is a **Lagrangian** of `Q` when

* `Q` vanishes on `K` (`K` is totally isotropic: `hK`), and
* `K` is exactly its own orthogonal complement: `B x y = 0` for all `y ∈ K` iff `x ∈ K` (`horth`).

The main result of this file,

```lean
Work.SignatureBordism.signature_of_isLagrangian :
  signature Q = 0,
```

is the algebraic core of the statement that the signature of a closed oriented manifold bounds: an
`n`-manifold with boundary has middle intersection form carrying a Lagrangian (the image of the
relative cohomology), and such a form has signature `0`.  It is also the algebraic ingredient of
bordism invariance of the signature.

## The argument

Write `p = sigPos Q`, `n = sigNeg Q`, `k = finrank 𝕜 K` and `m = finrank 𝕜 V`.  Four inequalities
are put together.

1. `p + n = m` (`hsum`).  The radical of `Q` is trivial: `radical Q = ker (associated Q)`
   (`QuadraticMap.radical_eq_ker_associated`) and `hrad` says precisely that this kernel vanishes.
   Mathlib's additivity identity `QuadraticForm.sigPos_add_sigNeg_add_radical` then gives
   `p + n + finrank (radical Q) = m`.
2. `p + k ≤ m` (`hpos`) and `n + k ≤ m` (`hneg`).  This is
   `QuadraticForm.sigPos_add_finrank_le_of_nonpos` applied to `Q`, respectively to `-Q`, on the
   subspace `K`, where the form is `≤ 0` because it *vanishes* on `K` (`hK`).
3. `m ≤ 2k` (`hm_le`).  The linear map `V →ₗ[𝕜] (K →ₗ[𝕜] 𝕜)`, `x ↦ (y ↦ B x y)`, has kernel `K`
   by `horth`; rank–nullity and `finrank (K →ₗ[𝕜] 𝕜) = finrank K` therefore bound
   `m = finrank (range) + k ≤ k + k`.

From `p + k ≤ m = p + n` we get `k ≤ n`, from `n + k ≤ m = p + n` we get `k ≤ p`, and from
`m ≤ 2k` and `m = p + n` with `p, n ≥ k` we get `p = n = k`; hence
`signature Q = p - n = 0`.  (Note that `hrad` enters only through the radical computation: `horth`
already forces `m ≤ 2k`, and in fact `horth` alone forces `m = 2k`, hence already the triviality of
the radical.)

## Main results

* `Work.SignatureBordism.finrank_le_two_mul_finrank_of_lagrangian` — a subspace equal to its own
  orthogonal complement has at least half the dimension of the whole space;
* `Work.SignatureBordism.signature_of_isLagrangian` — **`signature Q = 0`**.
-/

namespace Work.SignatureBordism

open QuadraticMap

/-- **A Lagrangian has half the dimension.**  If the subspace `K` satisfies
`(∀ y ∈ K, associated Q x y = 0) ↔ x ∈ K` — that is, `K` is its own orthogonal complement with
respect to the bilinear form associated with `Q` — then `finrank 𝕜 V ≤ 2 * finrank 𝕜 K`.

Indeed the linear map `x ↦ (y ↦ associated Q x y)` from `V` to the dual of `K` has kernel exactly
`K` by hypothesis, so rank–nullity embeds `V ⧸ K` into `K*`. -/
lemma finrank_le_two_mul_finrank_of_lagrangian {𝕜 V : Type*} [Field 𝕜] [LinearOrder 𝕜]
    [Invertible (2 : 𝕜)] [AddCommGroup V] [Module 𝕜 V] [FiniteDimensional 𝕜 V]
    (Q : QuadraticForm 𝕜 V) (K : Submodule 𝕜 V)
    (horth : ∀ x : V, (∀ y ∈ K, QuadraticMap.associated Q x y = 0) ↔ x ∈ K) :
    Module.finrank 𝕜 V ≤ 2 * Module.finrank 𝕜 ↥K := by
  -- The "orthogonal projection" `x ↦ (y ↦ B x y)` from `V` to the dual of `K`.
  let f : V →ₗ[𝕜] (↥K →ₗ[𝕜] 𝕜) := (QuadraticMap.associated Q).compl₂ K.subtype
  -- Its kernel is `K`, by the hypothesis that `K` is its own orthogonal complement.
  have hker : LinearMap.ker f = K := by
    ext x
    rw [LinearMap.mem_ker]
    constructor
    · intro hx
      apply (horth x).mp
      intro y hy
      have h := congrArg (fun g : ↥K →ₗ[𝕜] 𝕜 => g ⟨y, hy⟩) hx
      simpa [f] using h
    · intro hx
      ext z
      exact (horth x).mpr hx z z.2
  have h1 := LinearMap.finrank_range_add_finrank_ker f
  have h2 : Module.finrank 𝕜 ↥(LinearMap.range f) ≤ Module.finrank 𝕜 ↥K := by
    calc Module.finrank 𝕜 ↥(LinearMap.range f)
        ≤ Module.finrank 𝕜 (↥K →ₗ[𝕜] 𝕜) := Submodule.finrank_le _
      _ = Module.finrank 𝕜 ↥K := by
            rw [Module.finrank_linearMap, Module.finrank_self, mul_one]
  have h3 : Module.finrank 𝕜 ↥(LinearMap.ker f) = Module.finrank 𝕜 ↥K := by rw [hker]
  omega

open QuadraticMap in
theorem signature_of_isLagrangian {𝕜 V : Type*} [Field 𝕜] [LinearOrder 𝕜]
    [IsStrictOrderedRing 𝕜] [Invertible (2 : 𝕜)] [AddCommGroup V] [Module 𝕜 V]
    [FiniteDimensional 𝕜 V] (Q : QuadraticForm 𝕜 V) (K : Submodule 𝕜 V)
    (hK : ∀ x ∈ K, Q x = 0)
    (horth : ∀ x : V, (∀ y ∈ K, QuadraticMap.associated Q x y = 0) ↔ x ∈ K)
    (hrad : ∀ x : V, (∀ y : V, QuadraticMap.associated Q x y = 0) → x = 0) :
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
  -- And `K` being a Lagrangian bounds the dimension of `V`.
  have hm_le : Module.finrank 𝕜 V ≤ 2 * Module.finrank 𝕜 ↥K :=
    finrank_le_two_mul_finrank_of_lagrangian Q K horth
  have hps : sigPos Q = sigNeg Q := by omega
  simp [Work.SignatureBordism.signature, hps]

end Work.SignatureBordism
