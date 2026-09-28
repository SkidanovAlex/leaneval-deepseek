import Submission.Work.ThreeConnected.Basic

/-!
# A single surgery below the middle dimension, and the killing of a degree

This module contains the **interface of Step 1** of the surgical route: what a single surgery on an
embedded framed sphere is, as far as the homological part of the argument is concerned, and the
induction which kills a whole homology group by a finite sequence of such surgeries.

## The classical statement and its formal shape

Let `M` be a closed oriented smooth `n`-manifold, let `k` be an index with `2k < n` (`k ≤ 3` when
`n = 8`), and let `S^k ⊂ M` be an embedded `k`-sphere with trivialised normal bundle, with tube
`S^k × D^{n-k} ⊂ M`.  The surgery replaces the interior of the tube by a `(k+1)`-disc bundle,

`M' = (M ∖ S^k × D̊^{n-k}) ∪_{S^k × S^{n-k-1}} (D^{k+1} × S^{n-k-1})`,

and its **trace** `W = (M × [0,1]) ∪_φ (D^{k+1} × D^{n-k})` is a bordism from `M` to `M'`.
The homology of the trace is computed from the elementary observation that `W` has the homotopy
type of `M` with a single `(k+1)`-cell attached along the map `S^k → M`; the long exact sequence of
the pair `(W, M)`, whose relative homology is `ℤ` in degree `k+1` and zero elsewhere, gives in turn

* `[S^k]` dies in `H_k(W)` — the sphere is filled in;
* `H_j(W) ≅ H_j(M)` for `j ∉ {k, k+1}` and `H_k(W) ≅ H_k(M)/⟨[S^k]⟩`: the pair `(W, M)` has relative
  homology `ℤ` in degree `k+1` and `0` elsewhere;
* **the *same* `W` is obtained from `M'` by attaching a single `(n-k)`-cell** (the belt disc, glued
  along the belt sphere `S^{n-k-1} = S^l`): `H_j(W) ≅ H_j(M')` for `j ∉ {n-k-1, n-k}`.  *This is why
  the effect of the surgery on homology is not simply "unchanged outside `k, k+1`"*: the degrees
  `k, k+1` (the attaching side) **and** `n-k-1, n-k` (the belt side) are affected.  For `n = 8`:
  `k = 1` affects `1,2` and `6,7`; `k = 2` affects `2,3` and `5,6`; `k = 3` affects `3,4` and `4,5`;
* hence `H_j(M') ≅ H_j(M)` for `j ∉ {k, k+1, n-k-1, n-k}`, and in particular **below the middle
  dimension** (`j < k ≤ n-k-1`) the surgery does not disturb homology — which is all that the
  killing iteration needs; and `H_k(M') ≅ H_k(M)/⟨[S^k]⟩` (because `k ∉ {n-k-1, n-k}` in the range
  `3k < n`, which holds for `n = 8`, `k ≤ 3`);
* `H_j(M')` is finitely generated whenever `H_j(M)` is, for every `j`: `H_j(W,M) = 0` off degree
  `k+1` makes `H_j(W)` isomorphic to `H_j(M)` or an extension of a subgroup of `ℤ` by a quotient of
  it, and the same argument applies on the belt side.

Note that **the framing does not enter any of these statements**: the trace is `M` with a `(k+1)`-cell
attached along the map `S^k → M`, and the framing only affects which cell attachment is used, not
the homotopy type of the trace (which is `M ∪_f e^{k+1}`).  In particular the classical
normal-framing bookkeeping — `π₁(SO(7)) = ℤ/2` for `k = 1`, `π₃(SO(5)) = ℤ` for `k = 3`, and the
automatic framing `π₂(SO(6)) = 0` for `k = 2` — is *not* needed for Step 1.  It is needed in the
middle dimension (`k = 4`), and is recorded in `README.md` and in `Submission/Work/Surgery/Framing`.

## What is in this file

* `Work.ThreeConnected.LowRangeSurgery` — a single low-range surgery and its homological effect;
* `Work.ThreeConnected.LowRangeSurgery.bordant`, `..._isZero_iff_below`, `..._isZero_of_span_top` —
  the elementary consequences of that data;
  (the long exact sequences of the two pairs `(W, M)` and `(W, M')` and the exact range of degrees in
  which the surgery changes homology are worked out in
  `Submission/Work/ThreeConnected/PairLES.lean` and `SurgeryHomology.lean`);
* `Work.ThreeConnected.CanKill` — **the geometric existence input** (item 2 of the brief): every
  homology class of a `(k-1)`-connected closed oriented `n`-manifold is killed by some surgery;
* `Work.ThreeConnected.KillSequence` — a finite sequence of low-range surgeries, with the lemmas
  `KillSequence.bordant` (the composite bordism), `KillSequence.isZero_iff_below` (the effect below
  the middle dimension) and `KillSequence.finite` (finite generation is preserved);
* `Work.ThreeConnected.KillState` — the state of the killing iteration, carrying the surjection
  `H_k(M) → H_k(N)` and its kernel.
-/

set_option backward.isDefEq.respectTransparency false

open scoped Manifold Topology ContDiff
open CategoryTheory CategoryTheory.Limits

namespace Work.ThreeConnected

open Work.Bordism Work.Surgery Work.SignatureBordism Work.Cohomology

noncomputable section

variable {n k : ℕ}

/-- **A single surgery below the middle dimension, with its effect on homology.**

`LowRangeSurgery n k M N` says: `N` is obtained from `M` by surgery on an embedded framed `k`-sphere
whose class in `H_k(M;ℤ)` is `cls`, in the range in which the surgery is *below the middle dimension*
(so that it does not disturb the homology of `M` in degrees `< k`, and only quotients out the class
`cls` in degree `k`).

This is the classical input of Step 1 (see the module docstring and `Submission/Work/ThreeConnected/README.md`):
the field `bord` is the trace of the surgery, `kill` records that the surgery fills the sphere in,
`below` and `quotient` record the effect on homology, and `fin` records that finite generation of
homology is preserved. -/
structure LowRangeSurgery (n k : ℕ) (M N : ClosedOriented n) where
  /-- the class of the embedded sphere which the surgery kills -/
  cls : M.hom k
  /-- the trace of the surgery, as a bordism from `M` to `N` -/
  bord : Bordism M N
  /-- the class of the sphere becomes zero in the trace -/
  kill : HomologicalComplex.homologyMap (chainMap ℤ M.X bord.W bord.iM) k cls = 0
  /-- below the middle dimension the surgery does not change homology -/
  below : ∀ j, j < k → M.hom j ≃+ N.hom j
  /-- the effect in the middle degree: the quotient by the class of the sphere -/
  quotient : M.hom k →ₗ[ℤ] N.hom k
  /-- the quotient map of the effect is surjective -/
  quotient_surj : Function.Surjective quotient
  /-- the kernel of the effect is the subgroup generated by the class of the sphere -/
  quotient_ker : LinearMap.ker quotient = Submodule.span ℤ {cls}
  /-- finite generation of homology is preserved by the surgery -/
  fin : ∀ j, Module.Finite ℤ (M.hom j) → Module.Finite ℤ (N.hom j)

namespace LowRangeSurgery

variable {M N : ClosedOriented n}

/-- **A low-range surgery is a bordism**: `M` and `N` are bordant, along the trace. -/
theorem bordant (h : LowRangeSurgery n k M N) : Bordant M N := ⟨h.bord⟩

/-- **Below the middle dimension, the surgery does not change the vanishing of homology.** -/
theorem isZero_iff_below (h : LowRangeSurgery n k M N) {j : ℕ} (hj : j < k) :
    IsZero (Hom M j) ↔ IsZero (Hom N j) := by
  rw [isZero_hom_iff, isZero_hom_iff]
  exact ⟨fun hsub => haveI := hsub; Function.Surjective.subsingleton (h.below j hj).surjective,
    fun hsub => haveI := hsub; Function.Injective.subsingleton (h.below j hj).injective⟩

/-- **If the class of the sphere generates `H_k(M)`, the surgery kills `H_k`.**

This is the elementary case of the killing iteration: `H_k(N) ≅ H_k(M)/⟨cls⟩` and the latter is
zero when `cls` generates `H_k(M)`. -/
theorem isZero_of_span_top (h : LowRangeSurgery n k M N)
    (hspan : Submodule.span ℤ {h.cls} = ⊤) : IsZero (Hom N k) := by
  rw [isZero_hom_iff]
  have hker : LinearMap.ker h.quotient = ⊤ := by rw [h.quotient_ker, hspan]
  have hzero : h.quotient = 0 := by
    ext x
    have hx : x ∈ LinearMap.ker h.quotient := by rw [hker]; trivial
    simpa using hx
  refine ⟨fun a b => ?_⟩
  obtain ⟨x, rfl⟩ := h.quotient_surj a
  obtain ⟨y, rfl⟩ := h.quotient_surj b
  rw [hzero]
  simp

end LowRangeSurgery

/-- **The geometric input of Step 1** (items 1 and 2 of the brief): every homology class of a
`(k-1)`-connected closed oriented `n`-manifold is killed by a single low-range surgery on an embedded
framed `k`-sphere.

Classically, in the range `2k < n`: a class of `H_k(M;ℤ)` is realised by a continuous map
`S^k → M` (Hurewicz, using `(k-1)`-connectedness when `k ≥ 2`), which in the range `2k < n` can be
approximated by an *embedding* (Whitney); the normal bundle of the embedded sphere is trivial (it is
stably trivial because `TS^k` is stably trivial and `ν ⊕ TM|_S ≅ εⁿ`, and the stabilisation
`π_{k-1}(SO(n-k)) → π_{k-1}(SO)` is injective in this range); and the trace of the surgery has the
homotopy type of `M` with a `(k+1)`-cell attached, which gives the effect fields of
`LowRangeSurgery`.

For `n = 8` and `k = 1, 2, 3` the implications of the last point are:

* `k = 1`: the normal bundle has rank `7` and is automatically trivial (`π₀(SO(7)) = 0`), but the
  *framing* is a `ℤ/2 = π₁(SO(7))` choice — it does not matter for the class killed;
* `k = 2`: rank `6`; the normal bundle is stably trivial and `π₁(SO(6)) → π₁(SO)` is an
  isomorphism, so it is trivial, and `π₂(SO(6)) = 0` means the framing is unique up to homotopy;
* `k = 3`: rank `5`; the normal bundle is automatically trivial (`π₂(SO(5)) = 0`) but the framing is
  a `ℤ = π₃(SO(5))` choice — again irrelevant for the class killed.

This is *not* proved here (see `README.md`). -/
def CanKill (n k : ℕ) : Prop :=
  ∀ (M : ClosedOriented n), IsConnectedUpTo (k - 1) M → FiniteHomology M →
    ∀ x : M.hom k, ∃ (N : ClosedOriented n) (h : LowRangeSurgery n k M N), h.cls = x

/-! ## Finite sequences of low-range surgeries -/

/-- **A finite sequence of low-range surgeries**: `KillSequence n k M N` records that `N` is obtained
from `M` by finitely many surgeries of index `k`, in the low range, performed in order.

The sequence is deliberately *not* required to kill anything: the killing happens in the iteration
`Work.ThreeConnected.KillState`, where the classes are tracked. -/
inductive KillSequence (n k : ℕ) : ClosedOriented n → ClosedOriented n → Prop
  | nil (M : ClosedOriented n) : KillSequence n k M M
  | step {M N P : ClosedOriented n} (h : LowRangeSurgery n k M N)
      (tail : KillSequence n k N P) : KillSequence n k M P

namespace KillSequence

/-- **The composite bordism of a sequence of surgeries**: `M` is bordant to `N`. -/
theorem bordant {M N : ClosedOriented n} : KillSequence n k M N → Bordant M N
  | .nil M => bordant_refl M
  | .step g tail => bordant_trans g.bordant tail.bordant

/-- **Below the middle dimension a sequence of surgeries does not change the vanishing of
homology.** -/
theorem isZero_iff_below {M N : ClosedOriented n} {j : ℕ} (hj : j < k) :
    KillSequence n k M N → (IsZero (Hom M j) ↔ IsZero (Hom N j))
  | .nil _ => Iff.rfl
  | .step g tail => (g.isZero_iff_below hj).trans (tail.isZero_iff_below hj)

/-- **Finite generation of homology is preserved by a sequence of surgeries.** -/
theorem finite {M N : ClosedOriented n} : KillSequence n k M N → FiniteHomology M → FiniteHomology N
  | .nil _, h => h
  | .step g tail, h => tail.finite (fun j => g.fin j (h j))

/-- **Sequences compose.** -/
theorem trans {M N P : ClosedOriented n} :
    KillSequence n k M N → KillSequence n k N P → KillSequence n k M P
  | .nil _, h' => h'
  | .step g tail, h' => .step g (trans tail h')

/-- **Appending one more surgery at the end of a sequence.** -/
theorem append_step {M N P : ClosedOriented n} (h : KillSequence n k M N)
    (g : LowRangeSurgery n k N P) : KillSequence n k M P :=
  trans h (.step g (.nil P))


end KillSequence

/-! ## The killing iteration -/

/-- **The state of the killing iteration.**  We are killing the homology of `M` in degree `k` by a
sequence of low-range surgeries; at each stage we have

* the manifold `N` reached so far, together with the sequence of surgeries from `M`;
* the connectivity and finite generation of `N` (so that `CanKill` can be applied again);
* the surjection `q : H_k(M) → H_k(N)` induced by the surgeries;
* the set `K ⊆ H_k(M)` of classes already killed — recorded through the identity
  `ker q = span K`.

When `K` spans `H_k(M)`, the last condition makes `q` the zero map and hence `H_k(N) = 0`. -/
structure KillState (n k : ℕ) (M : ClosedOriented n) where
  /-- the manifold reached so far -/
  N : ClosedOriented n
  /-- the sequence of surgeries from `M` to `N` -/
  seq : KillSequence n k M N
  /-- `N` is still `(k-1)`-connected, so that the killing can go on -/
  conn : IsConnectedUpTo (k - 1) N
  /-- `N` still has finitely generated homology -/
  fin : FiniteHomology N
  /-- the surjection induced on `H_k` -/
  q : M.hom k →ₗ[ℤ] N.hom k
  /-- it is surjective -/
  surj : Function.Surjective q
  /-- the classes already killed -/
  K : Set (M.hom k)
  /-- the classes already killed are exactly the kernel -/
  ker : LinearMap.ker q = Submodule.span ℤ K

namespace KillState

variable {M : ClosedOriented n}

/-- **The initial state**: no surgery has been performed, nothing has been killed. -/
def init (M : ClosedOriented n) (hconn : IsConnectedUpTo (k - 1) M) (hfin : FiniteHomology M) :
    KillState n k M where
  N := M
  seq := KillSequence.nil M
  conn := hconn
  fin := hfin
  q := LinearMap.id
  surj := Function.surjective_id
  K := ∅
  ker := by
    rw [LinearMap.ker_id]
    simp

/-- **The conclusion of the iteration**: if the classes already killed span `H_k(M)`, then the
homology of the manifold reached so far vanishes in degree `k`.

Indeed `q` is then the zero map (`ker q = ⊤`), and it is surjective. -/
theorem isZero_hom (h : KillState n k M) (hspan : Submodule.span ℤ h.K = ⊤) :
    IsZero (Hom h.N k) := by
  rw [isZero_hom_iff]
  have hker : LinearMap.ker h.q = ⊤ := by rw [h.ker, hspan]
  have hzero : h.q = 0 := by
    ext x
    have hx : x ∈ LinearMap.ker h.q := by rw [hker]; trivial
    simpa using hx
  refine ⟨fun a b => ?_⟩
  obtain ⟨x, rfl⟩ := h.surj a
  obtain ⟨y, rfl⟩ := h.surj b
  rw [hzero]
  simp

end KillState

end

end Work.ThreeConnected
