import Mathlib
import Submission.Work.ANALYTIC.RealSide

namespace Work.ANALYTIC

/-! ## The square `∏^bnd ℤ ⊆ ∏ℤ`, `∏^bnd ℝ ⊆ ∏ℝ` is a pullback

In `Submission.Work.ANALYTIC.RealSide` the square

```
boundedSeq  --boundedIntRealIncl-->  boundedReal
    |                                     |
boundedSeqIncl                      boundedRealIncl
    v                                     v
prodZModel  --prodZRealIncl-------->  prodReal
```

is a pullback in `LightCondAb`.  Sectionwise (all the `_obj_obj` lemmas are `rfl`): an
`ℕ`-indexed family of continuous `ℤ`-valued functions on `S` whose image in `ℕ → C(S,ℝ)` is
uniformly bounded is itself uniformly bounded, so `boundedSeqSet S` is the fibre product of
`ℕ → C(S,ℤ)` and `boundedRealSet S` over `ℕ → C(S,ℝ)`.  (`LightCondAb` is a category of sheaves
of modules, so limits are computed pointwise; here a direct construction is easiest.)

Proof route: `w` is `boundedIntRealIncl_boundedRealIncl.symm`; uniqueness is
`cancel_mono boundedSeqIncl` (`mono_boundedSeqIncl`); for the lift, given `T : LightCondAb`,
`u : T ⟶ prodZModel`, `v : T ⟶ boundedReal` with `u ≫ prodZRealIncl = v ≫ boundedRealIncl`, define
`l : T ⟶ boundedSeq` by `l.hom.app (op S) x = ⟨u.hom.app (op S) x, _⟩`, the bound being that of
`v.hom.app (op S) x ∈ boundedRealSet S` (convert the real bound `N` to the integer bound `⌈N⌉`
using `Int.le_ceil`), using the pointwise identity
`((u.hom.app (op S) x n) s : ℝ) = (v.hom.app (op S) x).1 n s` that follows from the commutativity
hypothesis.  Naturality of `l` and the two identities `l ≫ boundedSeqIncl = u`,
`l ≫ boundedIntRealIncl = v` are checked elementwise.

Useful existing lemmas: `boundedSeq_obj_obj`, `prodZModel_obj_obj`, `boundedReal_obj_obj`,
`prodReal_obj_obj`, `boundedSeqIncl_apply`, `boundedIntRealIncl_apply`, `boundedRealIncl_apply`,
`prodZRealIncl_apply`, `mono_boundedSeqIncl`, `boundedIntRealIncl_boundedRealIncl`.

## Implementation notes

The `S`-points of these models are only *definitionally* equal to the explicit families
(`prodZModel_obj_obj`, `boundedSeq_obj_obj`, … are `rfl`), i.e. the identification is invisible at
`implicit` transparency.  Consequently tactics that re-typecheck a goal (in particular `rw`) fail
on a goal containing a raw term such as `(u.hom.app S x : ℕ → C(S,ℤ))` or a raw
`LinearMap.codRestrict (boundedSeqSet S) (u.hom.app S).hom …`, even though such terms elaborate.
The way out used below: (i) the sectionwise component `realSideLiftApp` of the lift is packaged as
an *opaque* definition, so that occurrences of the lift in a goal have a genuine, syntactic type;
(ii) the interface used to compute with it (`realSideLiftApp_apply`, `realSideLiftApp_incl`,
`realSide_map_apply`) is stated with `Subtype.val` and proved by `rfl` — these statements elaborate
at default transparency, and after rewriting with them the goals contain only opaque terms. -/

noncomputable section

open CategoryTheory Limits LightProfinite LightCondensed MonoidalCategory MonoidalClosed
open Opposite
open _root_.LightCondensed _root_.LightCondensed.Solid

/-- The inclusion `∏^bnd ℤ ⟶ ∏ℤ` is a monomorphism (used for the uniqueness part of the
pullback property and for the second compatibility of the lift). -/
private instance instMonoBoundedSeqIncl : Mono boundedSeqIncl := mono_boundedSeqIncl

/-- The inclusion `∏^bnd ℝ ⟶ ∏ℝ` is a monomorphism (used for the second compatibility of the
lift). -/
private instance instMonoBoundedRealIncl : Mono boundedRealIncl := mono_boundedRealIncl

/-- **The bound conversion.**  A family of continuous `ℤ`-valued functions on `S` whose real
values are bounded by the real number `N` is uniformly bounded by the integer `⌈N⌉`. -/
private lemma realSide_int_bound_of_real_bound {S : LightProfinite} (x : ℕ → C(S, ℤ)) (N : ℝ)
    (hN : ∀ n s, |((x n s : ℤ) : ℝ)| ≤ N) : ∃ M : ℤ, ∀ n s, |x n s| ≤ M := by
  refine ⟨⌈N⌉, fun n s => ?_⟩
  have h1 : ((|x n s| : ℤ) : ℝ) ≤ N := by rw [Int.cast_abs]; exact hN n s
  exact Int.cast_le.mp (h1.trans (Int.le_ceil N))

/-- **The pointwise identity.**  If `u ≫ prodZRealIncl = v ≫ boundedRealIncl` then the real values
of the family `u.hom.app (op S) x` are those of the bounded real family `v.hom.app (op S) x`. -/
private lemma realSide_pointwise_eq {T : LightCondAb} (u : T ⟶ prodZModel) (v : T ⟶ boundedReal)
    (hu : u ≫ prodZRealIncl = v ≫ boundedRealIncl)
    (S : LightProfinite) (x : T.obj.obj (op S)) (n : ℕ) (s : S) :
    (((u.hom.app (op S) x) n s : ℤ) : ℝ) = (v.hom.app (op S) x).1 n s := by
  have h := congrArg (fun (m : T ⟶ prodReal) => ((m.hom.app (op S) x) n : C(S, ℝ)) s) hu
  exact h

/-- **The sectionwise component of the lift.**  For a cone over the square, this is the map on
`S`-points sending `x` to the bounded integer family `u.hom.app (op S) x`; the bound is obtained
from the real bound of `v.hom.app (op S) x` via `realSide_int_bound_of_real_bound`.

It is defined as an opaque `def` on purpose: the body relies on the definitional identification of
the carriers with the explicit families, which would make every later occurrence of the lift
ill-typed at `implicit` transparency (see the implementation notes above). -/
private noncomputable def realSideLiftApp {T : LightCondAb} (u : T ⟶ prodZModel)
    (v : T ⟶ boundedReal) (hu : u ≫ prodZRealIncl = v ≫ boundedRealIncl) (S : LightProfiniteᵒᵖ) :
    T.obj.obj S ⟶ boundedSeq.obj.obj S :=
  ModuleCat.ofHom (LinearMap.codRestrict (boundedSeqSet S.unop) (u.hom.app S).hom (fun x => by
    obtain ⟨N, hN⟩ := (v.hom.app S x).2
    exact realSide_int_bound_of_real_bound (u.hom.app S x) N
      (fun n s => by rw [realSide_pointwise_eq u v hu S.unop x n s]; exact hN n s)))

/-- The defining property of `realSideLiftApp`: its underlying family is the family `u.hom.app S x`
(note the `rfl`). -/
private lemma realSideLiftApp_apply {T : LightCondAb} (u : T ⟶ prodZModel)
    (v : T ⟶ boundedReal) (hu : u ≫ prodZRealIncl = v ≫ boundedRealIncl) (S : LightProfiniteᵒᵖ)
    (x : T.obj.obj S) (n : ℕ) :
    (Subtype.val (realSideLiftApp u v hu S x)) n = (u.hom.app S x : ℕ → C(S.unop, ℤ)) n := rfl

/-- The defining property of the presheaf map on `∏^bnd ℤ`: it is precomposition of the
coordinates with `f` (note the `rfl`). -/
private lemma realSide_map_apply (S S' : LightProfiniteᵒᵖ) (f : S ⟶ S')
    (y : boundedSeq.obj.obj S) (n : ℕ) :
    (Subtype.val (boundedSeq.obj.map f y)) n
      = (Subtype.val y n).comp (LightProfinite.toTopCat.map f.unop).hom := rfl

/-- **Naturality of the sectionwise lift.**  This is the only place where naturality of `u` is
used; the remaining two compatibilities of the lift are formal consequences of the definitions. -/
private lemma realSideLiftApp_naturality {T : LightCondAb} (u : T ⟶ prodZModel)
    (v : T ⟶ boundedReal) (hu : u ≫ prodZRealIncl = v ≫ boundedRealIncl) (S S' : LightProfiniteᵒᵖ)
    (f : S ⟶ S') (x : T.obj.obj S) :
    realSideLiftApp u v hu S' (T.obj.map f x) = boundedSeq.obj.map f (realSideLiftApp u v hu S x) := by
  apply Subtype.ext
  funext n
  rw [realSideLiftApp_apply, realSide_map_apply, realSideLiftApp_apply]
  exact congrArg (fun (y : ↥(prodZModel.obj.obj S')) => (y : ℕ → C(S'.unop, ℤ)) n)
    (LightCondMod.hom_naturality_apply ℤ u f x)

/-- **The lift of a cone over the pullback square to `∏^bnd ℤ`.** -/
private noncomputable def realSideLift {T : LightCondAb} (u : T ⟶ prodZModel)
    (v : T ⟶ boundedReal) (hu : u ≫ prodZRealIncl = v ≫ boundedRealIncl) : T ⟶ boundedSeq where
  hom :=
    { app := fun S => realSideLiftApp u v hu S
      naturality := fun S S' f => by
        apply ModuleCat.hom_ext
        apply LinearMap.ext
        intro x
        exact realSideLiftApp_naturality u v hu S S' f x }

/-- The first compatibility of the lift: it lifts `u` along `boundedSeqIncl` (note the `rfl`:
the underlying family of `realSideLiftApp` is by construction that of `u`). -/
private lemma realSideLiftApp_incl {T : LightCondAb} (u : T ⟶ prodZModel)
    (v : T ⟶ boundedReal) (hu : u ≫ prodZRealIncl = v ≫ boundedRealIncl) (S : LightProfiniteᵒᵖ)
    (x : T.obj.obj S) :
    boundedSeqIncl.hom.app S (realSideLiftApp u v hu S x) = u.hom.app S x := rfl

/-- The first compatibility of the lift, as an identity of morphisms. -/
private lemma realSideLift_comp_incl {T : LightCondAb} (u : T ⟶ prodZModel)
    (v : T ⟶ boundedReal) (hu : u ≫ prodZRealIncl = v ≫ boundedRealIncl) :
    realSideLift u v hu ≫ boundedSeqIncl = u := by
  apply LightCondensed.hom_ext
  intro S
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  exact realSideLiftApp_incl u v hu S x

/-- The second compatibility of the lift: it lifts `v` along `boundedIntRealIncl`.  This follows
from the first compatibility, the commutativity of the square and the fact that `boundedRealIncl`
is a monomorphism (no elementwise verification is needed). -/
private lemma realSideLift_comp_intRealIncl {T : LightCondAb} (u : T ⟶ prodZModel)
    (v : T ⟶ boundedReal) (hu : u ≫ prodZRealIncl = v ≫ boundedRealIncl) :
    realSideLift u v hu ≫ boundedIntRealIncl = v := by
  refine (cancel_mono boundedRealIncl).mp ?_
  rw [Category.assoc, boundedIntRealIncl_boundedRealIncl, ← Category.assoc, realSideLift_comp_incl,
    hu]

theorem isPullback_realSide :
    CategoryTheory.IsPullback Work.ANALYTIC.boundedSeqIncl Work.ANALYTIC.boundedIntRealIncl
      Work.ANALYTIC.prodZRealIncl Work.ANALYTIC.boundedRealIncl := by
  have hsq : boundedSeqIncl ≫ prodZRealIncl = boundedIntRealIncl ≫ boundedRealIncl :=
    boundedIntRealIncl_boundedRealIncl.symm
  refine IsPullback.of_isLimit (c := PullbackCone.mk boundedSeqIncl boundedIntRealIncl hsq) ?_
  refine PullbackCone.IsLimit.mk hsq (fun s => realSideLift s.fst s.snd s.condition) ?_ ?_ ?_
  · intro s
    exact realSideLift_comp_incl s.fst s.snd s.condition
  · intro s
    exact realSideLift_comp_intRealIncl s.fst s.snd s.condition
  · intro s m hm1 hm2
    refine (cancel_mono boundedSeqIncl).mp ?_
    rw [hm1, realSideLift_comp_incl]

end

end Work.ANALYTIC
