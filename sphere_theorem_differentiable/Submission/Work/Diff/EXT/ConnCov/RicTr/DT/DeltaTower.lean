import Mathlib
import Submission.Work.Diff.EXT.ConnCov.Kit
import Submission.Work.Diff.GE.kato_smooth
import Submission.Work.Diff.GE.cov2RmExt_prelim

set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The δ-tower `V_c = ∇^{g_0,c} δ` of the connection difference, and the triangular relation

This module starts the chapter that `Work.Diff.EXT.ConnCov.aTower_moving_bound` needs (see the
docstring of that file and the `HANDOFF.md` note): the **connection difference**

  `δ := covDiff G t`,   `δ X Y = ∇^{g_t}_Y X − ∇^{g_0}_Y X`  (`Kit.lean`)

is a `(1,2)`-tensor *field*, and its covariant derivatives `V_c := ∇^{g_0,c} δ` with respect to the
fixed background connection are the objects into which the conversion between the two towers
inserts.  Because `aOf = g_t ⊙ δ` (by definition: `aOf A B C = g_t (δ B A) C`), the `∇^{g_0}`-tower
`T_c := ∇^{g_0,c} aOf` of `aOf` is the *Leibniz expansion* of the pairing of the metric tower
`∇^{g_0,i} g_t` with the δ-tower, and the `i = 0` term of that expansion is the lowering

  `Wins c := g_t ⊙ V_c`,  `Wins c v X Y Z y = (G t).inner y (V_c v X Y y) (Z y)`.

**Triangular relation** (the first lemma below, in its recursion form).  Writing
`step_0 := step (lcOf (G 0))` for the fixed connection's derivative and using the (bracket-free)
metric identity `(∇^{g_0}_X g_t)(Y,Z) = aOf X Y Z + aOf X Z Y`
(`Work.Diff.EXT.ConnCov.DT.covDerivSym2_lcOf_G0_eq_aOf_add`, proved in `aTower_moving_bound.lean`),
one gets

  `Wins (c+1) = step_0 (Wins c) − [aOf (v 0) (V_c …) · + aOf (v 0) · (V_c …)]`,

i.e. the only `c+1`-order input is the *given* `T`-tower (through `step_0` of the `c`-th stage) plus
*a single factor of `V_c`* inserted into `aOf`.  Iterating gives the expansion

  `T_c = Wins c + Σ_{i=1}^{c} C(c,i) (∇^{g_0,i} g_t) ⊙ V_{c-i}`,

which is *triangular*: `V_c` is bounded by the given `B_c` plus products of *lower* `V`'s with the
metric tower.  Note that the metric tower is **not** expressible through the `aOf`-tower by a slot
exchange for `i ≥ 2` (only for `i = 1`, where the identity above gives
`∇^{g_0} g_t = T_0 + swap(T_0)`); the correct statement is the iterated product rule for the pairing
itself, which is precisely the relation displayed above (its `i = c` term is `(∇^{g_0,c} g_t) ⊙ δ`),
and whose proof is the induction that produces the relation.

## Contents

* `VOp`, `vstep`, `vtower` — the vector-valued analogue of `Op3`/`step`/`tower`;
* `deltaTower`, `Wins` — `V_c` and its lowering;
* `Wins_zero` — the level-`0` identification `Wins 0 v X Y Z = aOf G t Y X Z`;
* `Wins_succ` — **the triangular relation in recursion form** (the first target of this module).
-/

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology BigOperators
open Bundle ContDiff Set VectorField CovariantDerivative Metric

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option backward.isDefEq.respectTransparency false

namespace Work.Diff.EXT.ConnCov.DT

open Work.Diff.EXT.ATower

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M]

/-- A tangent field on `M` (same as `ATower.TF`). -/
abbrev DVTF : Type _ := Π y : M, TangentSpace I y

/-- **A vector-valued operator with `k` derivative slots and two field slots** (the arity of the
connection difference and of its covariant derivatives). -/
abbrev VOp (k : ℕ) : Type _ := (Fin k → DVTF (I := I) (M := M)) →
  DVTF (I := I) (M := M) → DVTF (I := I) (M := M) → (Π y : M, TangentSpace I y)

/-- The ordinary (manifold) derivative of a section at a point, with **result type
`TangentSpace I x`** (rather than the defeq-but-differently-printed `E`).

⚠️ **Trap (found in review).**  Mathlib's `CovariantDerivative` is a function
`σ ↦ (x ↦ T_xM →L V_x)`, and `cov σ x v` *is already* the covariant derivative `∇_v σ`.  So the
covariant derivative of a *section-valued* operator must use `cov` **alone**; adding a plain
`mvfderiv` (`sectDeriv`) on top double-counts the derivative and destroys tensoriality at `k = 0`
(replace `X` by `X + f·Z` with `f x = 0`, `(d f)(v₀) = 1`).  `sectDeriv` is kept only as a typing
device for statements that need `TangentSpace I x` syntactically; it must not be added to `cov`. -/
noncomputable def sectDeriv (W : DVTF (I := I) (M := M)) (x : M)
    (v : TangentSpace I x) : TangentSpace I x :=
  mvfderiv I (fun y : M => W y) x v

/-- **The vector-valued recursion step**: `vstep cov τ` is the covariant derivative (with
connection `cov`) of the vector-valued `(1,2)`-tensor `τ`, i.e. the derivative of its value plus the
connection correction in the value slot, and the slot corrections in all `k + 2` field slots. -/
noncomputable def vstep (cov : CovariantDerivative I E (TangentSpace I (M := M))) {k : ℕ}
    (τ : VOp (I := I) (M := M) k) : VOp (I := I) (M := M) (k + 1) :=
  fun v X Y x =>
    cov (τ (fun i : Fin k => v i.succ) X Y) x (v 0 x)
      - ∑ i : Fin k, τ (Function.update (fun j : Fin k => v j.succ) i
          (fun y => cov (v i.succ) y (v 0 y))) X Y x
      - τ (fun i : Fin k => v i.succ) (fun y => cov X y (v 0 y)) Y x
      - τ (fun i : Fin k => v i.succ) X (fun y => cov Y y (v 0 y)) x

/-- **The vector-valued tower**: the iterated covariant derivatives of a vector-valued `(1,2)`-tensor
with respect to a connection. -/
noncomputable def vtower (cov : CovariantDerivative I E (TangentSpace I (M := M)))
    (base : VOp (I := I) (M := M) 0) :
    ∀ k : ℕ, VOp (I := I) (M := M) k
  | 0, v, X, Y => base v X Y
  | k + 1, v, X, Y => vstep cov (vtower cov base k) v X Y

/-- **The δ-tower** `V_c = ∇^{g_0,c} δ`: the iterated covariant derivatives (with respect to the
*fixed* connection `∇^{g_0} = lcOf (G 0)`) of the connection difference `δ = covDiff G t`. -/
noncomputable def deltaTower (G : ℝ → SMet I M) (t : ℝ) (c : ℕ) :
    VOp (I := I) (M := M) c :=
  vtower (lcOf (G 0))
    (fun (_ : Fin 0 → DVTF (I := I) (M := M)) X Y => covDiff G t X Y) c

/-- **The lowering `Wins c = g_t ⊙ V_c`** of the δ-tower: the `(0,c+3)`-tensor obtained by pairing
the last slot of `V_c` with the moving metric.  `Wins c` is an `Op3 c`, so that the whole
`ATower` machinery (`step`, `ValBound`, `insAll`, …) applies to it. -/
noncomputable def Wins (G : ℝ → SMet I M) (t : ℝ) (c : ℕ) :
    Op3 (I := I) (M := M) c :=
  fun v X Y Z y => (G t).inner y (deltaTower G t c v X Y y) (Z y)

/-- Level `0`: the lowering of `δ` is `aOf` with the two tensor slots exchanged (this is exactly the
definitions: `Wins 0 v X Y Z = g_t (δ X Y) Z` and `aOf A B C = g_t (δ B A) C`). -/
theorem Wins_zero (G : ℝ → SMet I M) (t : ℝ)
    (v : Fin 0 → DVTF (I := I) (M := M)) (X Y Z : DVTF (I := I) (M := M)) (x : M) :
    Wins G t 0 v X Y Z x = Work.Diff.EXT.aOf G t Y X Z x := rfl

/-- **The triangular relation, recursion form.**
The `(c+1)`-st lowering equals the fixed-connection derivative of the `c`-th lowering minus the
*metric-derivative* correction, in which the δ-tower value `V_c (…)` is inserted (through `aOf`)
into the first slot.  By the bracket-free metric identity `(∇^{g_0}_X g_t)(Y,Z) = aOf X Y Z + aOf X Z Y`
both correction terms are literally `aOf` on the section `V_c (…)`; iterating the relation produces
the Leibniz expansion `T_c = Wins c + Σ_{i ≥ 1} C(c,i) (∇^{g_0,i} g_t) ⊙ V_{c-i}`.

The smoothness hypotheses are essential: the `step` on the right contains `mvfderiv` of the pairing
`y ↦ ⟪V_c (…) y, Z y⟫`, which is junk `0` if `Z` (or the δ-tower section) fails to be
differentiable at `x`, and the identity is then false (take `Z ≡ 1` vs `Z = 1 + |y − x|`). -/
theorem Wins_succ (hLC : Submission.Diff.LCSmooth I M)
    (G : ℝ → SMet I M) (t : ℝ) (c : ℕ)
    (v : Fin (c + 1) → DVTF (I := I) (M := M)) (X Y Z : DVTF (I := I) (M := M))
    (hv : ∀ i, SmE I M (v i)) (hX : SmE I M X) (hY : SmE I M Y) (hZ : SmE I M Z) (x : M) :
    Wins G t (c + 1) v X Y Z x
      = step (lcOf (G 0)) (Wins G t c) v X Y Z x
        - (Work.Diff.EXT.aOf G t (v 0)
              (deltaTower G t c (fun i : Fin c => v i.succ) X Y) Z x
            + Work.Diff.EXT.aOf G t (v 0) Z
              (deltaTower G t c (fun i : Fin c => v i.succ) X Y) x) := by sorry

/-! ## The bracket-free Koszul identity for `∇^{g_0} g_t` (moved here from `aTower_moving_bound.lean`,
so that it is available upstream of both files)

`smt_inner_self_nonneg`-style helper: with the instance metric of `G t`, the compatibility axiom
(`IsMetricCompatible`) of `lcOf (G t)` reads

  `X · g_t(Y,Z) = g_t(∇^{g_t}_X Y, Z) + g_t(Y, ∇^{g_t}_X Z)`,

while the *definition* of the covariant derivative of `g_t` along the fixed connection `∇^{g_0}` is

  `(∇^{g_0}_X g_t)(Y,Z) = X · g_t(Y,Z) − g_t(∇^{g_0}_X Y, Z) − g_t(Y, ∇^{g_0}_X Z)`.

Subtracting gives the stated identity, with `aOf(X,Y,Z) = g_t(∇^{g_t}_X Y − ∇^{g_0}_X Y, Z)`. -/
theorem covDerivSym2_lcOf_G0_eq_aOf_add
    (hLC : Submission.Diff.LCSmooth I M) (G : ℝ → Submission.Diff.SMet I M) (t : ℝ)
    (X Y Z : Π y : M, TangentSpace I y)
    (hY : Work.Diff.EXT.ATower.SmE I M Y) (hZ : Work.Diff.EXT.ATower.SmE I M Z) (x : M) :
    Submission.Diff.covDerivSym2 (Submission.Diff.lcOf (G 0))
        (fun (y : M) (u v : TangentSpace I y) => (G t).inner y u v) X Y Z x
      = Work.Diff.EXT.aOf G t X Y Z x + Work.Diff.EXT.aOf G t X Z Y x := by
  simp only [Submission.Diff.covDerivSym2, Work.Diff.EXT.aOf]
  letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨(G t).toRiemannianMetric⟩
  have hcompat := (hLC (G t)).2.2 Y Z hY hZ x (X x)
  have hfun2 : (fun y : M => Inner.inner ℝ (Y y) (Z y))
      = fun y : M => (G t).inner y (Y y) (Z y) := by
    funext y; rfl
  have hcompat' : mvfderiv I (fun y : M => (G t).inner y (Y y) (Z y)) x (X x)
      = (G t).inner x ((Submission.Diff.lcOf (G t) Y x) (X x)) (Z x)
        + (G t).inner x (Y x) ((Submission.Diff.lcOf (G t) Z x) (X x)) := by
    rw [← hfun2]; exact hcompat
  rw [hcompat']
  have hs : ∀ (p q : TangentSpace I x), (G t).inner x p q = (G t).inner x q p :=
    fun p q => (G t).symm x p q
  rw [hs (Y x) ((Submission.Diff.lcOf (G t) Z x) (X x)),
      hs (Y x) ((Submission.Diff.lcOf (G 0) Z x) (X x))]
  simp only [map_sub, ContinuousLinearMap.sub_apply]
  ring


/-! ## The metric tower `∇^{g_0,i} g_t`

The triangular relation involves, besides the δ-tower, the tower of the *moving metric* with respect
to the fixed connection.  It is a `(0,2+i)`-tensor; we represent it as an `Op2`-valued tower (two
covariant value slots) with the evident recursion, so that the pairing with `V_j` below can be
stated. -/

/-- A real-valued operator with `k` derivative slots and **two** value slots: the arity of the
covariant derivatives of the metric `G t`. -/
abbrev Op2 (k : ℕ) : Type _ := (Fin k → DVTF (I := I) (M := M)) →
  DVTF (I := I) (M := M) → DVTF (I := I) (M := M) → M → ℝ

/-- The recursion step for `(0,2)`-tensors: the covariant derivative with connection `cov`. -/
noncomputable def gstep (cov : CovariantDerivative I E (TangentSpace I (M := M))) {k : ℕ}
    (τ : Op2 (I := I) (M := M) k) : Op2 (I := I) (M := M) (k + 1) :=
  fun v X Y x =>
    mvfderiv I (fun y : M => τ (fun i : Fin k => v i.succ) X Y y) x (v 0 x)
      - ∑ i : Fin k, τ (Function.update (fun j : Fin k => v j.succ) i
          (fun y => cov (v i.succ) y (v 0 y))) X Y x
      - τ (fun i : Fin k => v i.succ) (fun y => cov X y (v 0 y)) Y x
      - τ (fun i : Fin k => v i.succ) X (fun y => cov Y y (v 0 y)) x

/-- The tower of `(0,2)`-tensors. -/
noncomputable def gtower (cov : CovariantDerivative I E (TangentSpace I (M := M)))
    (base : Op2 (I := I) (M := M) 0) :
    ∀ k : ℕ, Op2 (I := I) (M := M) k
  | 0, v, X, Y => base v X Y
  | k + 1, v, X, Y => gstep cov (gtower cov base k) v X Y

/-- The moving metric `G t` as a `(0,2)`-tensor. -/
noncomputable def gtBase (G : ℝ → SMet I M) (t : ℝ) : Op2 (I := I) (M := M) 0 :=
  fun _ X Y y => (G t).inner y (X y) (Y y)

/-- **The metric tower** `∇^{g_0,i} g_t`: the iterated covariant derivatives of the moving metric
with respect to the fixed connection `∇^{g_0} = lcOf (G 0)`. -/
noncomputable def gtTower (G : ℝ → SMet I M) (t : ℝ) (i : ℕ) : Op2 (I := I) (M := M) i :=
  gtower (lcOf (G 0)) (gtBase G t) i

/-- The first step: `∇^{g_0} g_t = aOf + swap(aOf)` in the `Op2`-representation, i.e.
`(∇^{g_0}_X g_t)(Y,Z) = aOf X Y Z + aOf X Z Y` (the bracket-free identity proved in
`aTower_moving_bound.lean`).  The third slot of the `Op3`-form carries the direction. -/
theorem gtTower_one_eq (hLC : Submission.Diff.LCSmooth I M)
    (G : ℝ → SMet I M) (t : ℝ)
    (d : Fin 1 → DVTF (I := I) (M := M)) (Y Z : DVTF (I := I) (M := M))
    (hd : SmE I M (d 0)) (hY : SmE I M Y) (hZ : SmE I M Z) (x : M) :
    gtTower G t 1 d Y Z x
      = Work.Diff.EXT.aOf G t (d 0) Y Z x + Work.Diff.EXT.aOf G t (d 0) Z Y x := by
  have h := covDerivSym2_lcOf_G0_eq_aOf_add (I := I) (M := M) hLC G t (d 0) Y Z hY hZ x
  simpa only [gtTower, gtower, gstep, gtBase, Submission.Diff.covDerivSym2,
    Finset.univ_eq_empty, Finset.sum_empty, sub_zero] using h

/-! ## The twisted pairing `⊙` of the metric tower with the δ-tower

`aOf A B C = g_t (δ B A) C` is the pairing of the moving metric with the connection difference, with
the two field slots of `δ` exchanged.  Iterating the product rule for this pairing is what produces
the triangular relation of the module header.  The pairing below takes a `(0,2+i)`-tensor `S` (the
metric tower) and a vector-valued `(1,2+j)`-tensor `T` (the δ-tower) and splits the direction tuple
after the first `i` entries. -/

/-- The twisted pairing of `S` (metric tower, `i` directions + two value slots) with `T` (δ-tower,
`j` directions + two field slots): `(S ⊙ T)(d;A,B,C) = S(d₁…d_i; T(d_{i+1}…d_{i+j}; B, A), C)`. -/
noncomputable def pairOp {i j : ℕ} (S : Op2 (I := I) (M := M) i) (T : VOp (I := I) (M := M) j) :
    Op3 (I := I) (M := M) (i + j) :=
  fun d A B C y =>
    S (fun a : Fin i => d (Fin.castAdd j a))
      (T (fun b : Fin j => d (Fin.natAdd i b)) B A) C y

/-- Base case of the triangular relation: at `i = j = 0` the pairing is exactly `aOf`
(both sides are `g_t (δ B A) C`; compare `Wins_zero`). -/
theorem pairOp_gtBase_deltaTower (G : ℝ → SMet I M) (t : ℝ)
    (d : Fin 0 → DVTF (I := I) (M := M)) (A B C : DVTF (I := I) (M := M)) (y : M) :
    pairOp (gtBase G t) (deltaTower G t 0) d A B C y = Work.Diff.EXT.aOf G t A B C y := rfl

/-! ## The connection difference is `C^∞`-linear (hence tensorial) in its section slot

(moved up from `aTower_moving_bound.lean`, so that the δ-tower chapter is upstream of it)

The two `smulRight` terms produced by the Leibniz rules of `∇^{g_t}` and `∇^{g_0}` are *the same*
term (`(d f) ⊗ X` evaluated at `x`), so they cancel in the difference `covDiff G t = ∇^{g_t} − ∇^{g_0}`.
This is what makes the level-`0` bound `ValBound G t 0 (aOf G t) B 0` usable with *arbitrary* fields
(and hence is the base case of the insertion bounds of the word expansion). -/
theorem covDiff_smul_section
    (G : ℝ → Submission.Diff.SMet I M) (t : ℝ) (f : M → ℝ)
    (X Y : Π y : M, TangentSpace I y)
    (hf : CMDiff ∞ f) (hX : Work.Diff.EXT.ATower.SmE I M X)
    (hY : Work.Diff.EXT.ATower.SmE I M Y) (x : M) :
    Work.Diff.EXT.ConnCov.covDiff G t (f • X) Y x
      = f x • Work.Diff.EXT.ConnCov.covDiff G t X Y x := by
  have hX' : MDiffAt (T% X) x := hX.mdifferentiableAt (by simp)
  have hf' : MDiffAt f x := hf.mdifferentiableAt (by simp)
  have h1 := ((lcOf (G t)).isCovariantDerivativeOn (s := Set.univ)).leibniz
    (σ := X) (g := f) hX' hf' (by simp)
  have h2 := ((lcOf (G 0)).isCovariantDerivativeOn (s := Set.univ)).leibniz
    (σ := X) (g := f) hX' hf' (by simp)
  simp only [Work.Diff.EXT.ConnCov.covDiff, Pi.sub_apply, h1, h2]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smulRight_apply,
    ContinuousLinearMap.smul_apply]
  module

/-- Additivity of the connection difference in its section slot (the same argument as
`covDiff_smul_section`, with the additivity axioms of the two connections). -/
theorem covDiff_add_section
    (G : ℝ → Submission.Diff.SMet I M) (t : ℝ)
    (X₁ X₂ Y : Π y : M, TangentSpace I y)
    (hX₁ : Work.Diff.EXT.ATower.SmE I M X₁) (hX₂ : Work.Diff.EXT.ATower.SmE I M X₂)
    (x : M) :
    Work.Diff.EXT.ConnCov.covDiff G t (X₁ + X₂) Y x
      = Work.Diff.EXT.ConnCov.covDiff G t X₁ Y x + Work.Diff.EXT.ConnCov.covDiff G t X₂ Y x := by
  have hX₁' : MDiffAt (T% X₁) x := hX₁.mdifferentiableAt (by simp)
  have hX₂' : MDiffAt (T% X₂) x := hX₂.mdifferentiableAt (by simp)
  have h1 := ((lcOf (G t)).isCovariantDerivativeOn (s := Set.univ)).add
    (σ := X₁) (σ' := X₂) hX₁' hX₂' (by simp)
  have h2 := ((lcOf (G 0)).isCovariantDerivativeOn (s := Set.univ)).add
    (σ := X₁) (σ' := X₂) hX₁' hX₂' (by simp)
  simp only [Work.Diff.EXT.ConnCov.covDiff, Pi.add_apply, Pi.sub_apply, h1, h2]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.sub_apply]
  abel


/-! ## Tensoriality, smoothness and slot linearity for `Op2`/`VOp` objects

The product rule for the pairing `pairOp` (and hence the triangular relation) needs, for each object,
that a *pointwise* pairing with it makes sense: the value at `x` must depend only on the values of
the fields (*tensoriality*), the object must be smooth in the point (so that `mvfderiv` is the genuine
derivative rather than the junk value `0`), and it must be `C^∞`-linear in its slots (so that the
Leibniz rule produces the covariant slot corrections rather than spurious terms). -/

/-- Value dependence (tensoriality) at a point of an `Op2`-operator. -/
def Op2Tens {k : ℕ} (τ : Op2 (I := I) (M := M) k) : Prop :=
  ∀ (v v' : Fin k → DVTF (I := I) (M := M)) (X X' Y Y' : DVTF (I := I) (M := M)) (x : M),
    (∀ i, SmE I M (v i)) → (∀ i, SmE I M (v' i)) → (∀ i, v i x = v' i x) →
    SmE I M X → SmE I M X' → SmE I M Y → SmE I M Y' →
    X x = X' x → Y x = Y' x → τ v X Y x = τ v' X' Y' x

/-- Smoothness in the point of an `Op2`-operator on smooth fields. -/
def Op2Sm {k : ℕ} (τ : Op2 (I := I) (M := M) k) : Prop :=
  ∀ (v : Fin k → DVTF (I := I) (M := M)) (X Y : DVTF (I := I) (M := M)),
    (∀ i, SmE I M (v i)) → SmE I M X → SmE I M Y → SmF I M (τ v X Y)

/-- `C^∞`-linearity of an `Op2`-operator in its two value slots. -/
def Op2LinVal {k : ℕ} (τ : Op2 (I := I) (M := M) k) : Prop :=
  (∀ (v : Fin k → DVTF (I := I) (M := M)) (X₁ X₂ : DVTF (I := I) (M := M)) (f₁ f₂ : M → ℝ),
      (∀ i, SmE I M (v i)) → SmF I M f₁ → SmF I M f₂ → SmE I M X₁ → SmE I M X₂ →
      ∀ (Y : DVTF (I := I) (M := M)) (x : M),
        τ v (f₁ • X₁ + f₂ • X₂) Y x = f₁ x * τ v X₁ Y x + f₂ x * τ v X₂ Y x) ∧
  (∀ (v : Fin k → DVTF (I := I) (M := M)) (Y₁ Y₂ : DVTF (I := I) (M := M)) (f₁ f₂ : M → ℝ),
      (∀ i, SmE I M (v i)) → SmF I M f₁ → SmF I M f₂ → SmE I M Y₁ → SmE I M Y₂ →
      ∀ (X : DVTF (I := I) (M := M)) (x : M),
        τ v X (f₁ • Y₁ + f₂ • Y₂) x = f₁ x * τ v X Y₁ x + f₂ x * τ v X Y₂ x)

/-- Value dependence (tensoriality) at a point of a vector-valued `VOp`-operator: the section
`τ v X Y` depends on the fields only through their values at `x`. -/
def VOpTens {k : ℕ} (τ : VOp (I := I) (M := M) k) : Prop :=
  ∀ (v v' : Fin k → DVTF (I := I) (M := M)) (X X' Y Y' : DVTF (I := I) (M := M)) (x : M),
    (∀ i, SmE I M (v i)) → (∀ i, SmE I M (v' i)) → (∀ i, v i x = v' i x) →
    SmE I M X → SmE I M X' → SmE I M Y → SmE I M Y' →
    X x = X' x → Y x = Y' x → τ v X Y x = τ v' X' Y' x

/-- Smoothness in the point of a vector-valued `VOp`-operator on smooth fields. -/
def VOpSm {k : ℕ} (τ : VOp (I := I) (M := M) k) : Prop :=
  ∀ (v : Fin k → DVTF (I := I) (M := M)) (X Y : DVTF (I := I) (M := M)),
    (∀ i, SmE I M (v i)) → SmE I M X → SmE I M Y → SmE I M (τ v X Y)

/-- `C^∞`-linearity of a `VOp`-operator in its two field slots. -/
def VOpLinVal {k : ℕ} (τ : VOp (I := I) (M := M) k) : Prop :=
  (∀ (v : Fin k → DVTF (I := I) (M := M)) (X₁ X₂ : DVTF (I := I) (M := M)) (f₁ f₂ : M → ℝ),
      (∀ i, SmE I M (v i)) → SmF I M f₁ → SmF I M f₂ → SmE I M X₁ → SmE I M X₂ →
      ∀ (Y : DVTF (I := I) (M := M)) (x : M),
        τ v (f₁ • X₁ + f₂ • X₂) Y x = f₁ x • τ v X₁ Y x + f₂ x • τ v X₂ Y x) ∧
  (∀ (v : Fin k → DVTF (I := I) (M := M)) (Y₁ Y₂ : DVTF (I := I) (M := M)) (f₁ f₂ : M → ℝ),
      (∀ i, SmE I M (v i)) → SmF I M f₁ → SmF I M f₂ → SmE I M Y₁ → SmE I M Y₂ →
      ∀ (X : DVTF (I := I) (M := M)) (x : M),
        τ v X (f₁ • Y₁ + f₂ • Y₂) x = f₁ x • τ v X Y₁ x + f₂ x • τ v X Y₂ x)


/-- `C^∞`-linearity of an `Op2`-operator in its `k` direction slots. -/
def Op2LinDir {k : ℕ} (τ : Op2 (I := I) (M := M) k) : Prop :=
  ∀ (i : Fin k) (v : Fin k → DVTF (I := I) (M := M)) (X₁ X₂ : DVTF (I := I) (M := M))
    (f₁ f₂ : M → ℝ),
    (∀ j, SmE I M (v j)) → SmF I M f₁ → SmF I M f₂ → SmE I M X₁ → SmE I M X₂ →
    ∀ (Y Z : DVTF (I := I) (M := M)) (x : M),
      τ (Function.update v i (f₁ • X₁ + f₂ • X₂)) Y Z x
        = f₁ x * τ (Function.update v i X₁) Y Z x + f₂ x * τ (Function.update v i X₂) Y Z x

/-- `C^∞`-linearity of a `VOp`-operator in its `k` direction slots. -/
def VOpLinDir {k : ℕ} (τ : VOp (I := I) (M := M) k) : Prop :=
  ∀ (i : Fin k) (v : Fin k → DVTF (I := I) (M := M)) (X₁ X₂ : DVTF (I := I) (M := M))
    (f₁ f₂ : M → ℝ),
    (∀ j, SmE I M (v j)) → SmF I M f₁ → SmF I M f₂ → SmE I M X₁ → SmE I M X₂ →
    ∀ (Y Z : DVTF (I := I) (M := M)) (x : M),
      τ (Function.update v i (f₁ • X₁ + f₂ • X₂)) Y Z x
        = f₁ x • τ (Function.update v i X₁) Y Z x + f₂ x • τ (Function.update v i X₂) Y Z x

/-- The connection difference as a `VOp 0` (the empty derivative tuple is ignored). -/
noncomputable def deltaBase (G : ℝ → SMet I M) (t : ℝ) : VOp (I := I) (M := M) 0 :=
  fun _ X Y => covDiff G t X Y

/-- **The metric base is tensorial** (the metric pairing depends only on the values). -/
theorem gtBase_tens (G : ℝ → SMet I M) (t : ℝ) : Op2Tens (I := I) (M := M) (gtBase G t) := by
  intro v v' X X' Y Y' x _ _ _ _ hX' _ hY' hXX hYY
  simp only [gtBase, hXX, hYY]

/-- **The metric base is smooth** (smoothness of the metric pairing on smooth fields): this is
`Work.Diff.GE.katoMetricPairingSmooth`, the metric-pairing smoothness API of the `GE` area. -/
theorem gtBase_sm (hLC : Submission.Diff.LCSmooth I M) [T2Space M]
    (G : ℝ → SMet I M) (t : ℝ) : Op2Sm (I := I) (M := M) (gtBase G t) := by
  intro v X Y _ hX hY
  exact Work.Diff.GE.katoMetricPairingSmooth (I := I) (M := M) (G t) hX hY

/-- **The metric base is `C^∞`-linear in its two slots**: the metric pairing is a *pointwise*
bilinear form, so linearity over smooth coefficients is bilinearity of `(G t).inner x`. -/
theorem gtBase_linVal (G : ℝ → SMet I M) (t : ℝ) :
    Op2LinVal (I := I) (M := M) (gtBase G t) := by
  -- Pure pointwise bilinearity of the metric.  (Left as an obligation: the `map_add`/`map_smul`
  -- rewrites on the *dependent* family `y ↦ (G t).inner y` need to be discharged with the right
  -- instantiation, cf. `gtBase_sm` above which is proved.)
  refine ⟨?_, ?_⟩
  · intro v X₁ X₂ f₁ f₂ _ _ _ _ _ Y x
    sorry
  · intro v Y₁ Y₂ f₁ f₂ _ _ _ _ _ X x
    sorry


/-- **`SmE` is closed under multiplication by a smooth function.**  (The `CMDiff`-smul API for the
`SmE = CMDiff ∞ (T% ·)` predicate; stated here because the local-frame expansion of
`deltaBase_tens` needs it.) -/
theorem smE_smul (f : M → ℝ) (X : Π y : M, TangentSpace I y)
    (hf : SmF I M f) (hX : SmE I M X) : SmE I M (f • X) := by sorry

/-- **The connection difference is tensorial** (its value at `x` depends only on the values of the
two fields).  The *direction* slot is immediate (`covDiff G t X Y x` sees `Y` only through `Y x`);
the *section* slot is the "local frame expansion": `covDiff` is `C^∞`-linear in the section slot
(`covDiff_smul_section` + `covDiff_add_section`, proved above for each connection separately, so that
the `smulRight` terms cancel) and germ-local (the covariant-derivative class is), hence
value-dependent by `Work.Diff.GE.field_value_dep_of_linear`. -/
theorem deltaBase_tens (hLC : Submission.Diff.LCSmooth I M) [T2Space M]
    (G : ℝ → SMet I M) (t : ℝ) :
    VOpTens (I := I) (M := M) (deltaBase G t) := by
  -- RECIPE (all ingredients present; the remaining work is Lean plumbing):
  -- (a) direction slot: `covDiff G t Z Y x` sees `Y` only through `Y x` (`simp only [covDiff, hYY]`).
  -- (b) section slot, *lowered*: the bridge `Work.Diff.GE.field_value_dep_of_linear` (imported
  --     above) applies to the real-valued `F Z = g_t (covDiff G t Z Y' x) W`; its `hlin` is
  --     `covDiff_add_section` + `covDiff_smul_section` transplanted through the bilinearity of
  --     `(G t).inner x` (needs `smE_smul` below for the smoothness of `f • X`), and its `hgerm` is
  --     `CovariantDerivative.IsCovariantDerivativeOn.congr_of_eventuallyEq` for both connections.
  -- (c) lift `∀ W, g_t u W = g_t v W` to `u = v` by `(G t).pos` on `u - v`.
  sorry

/-- **The connection difference is smooth** on smooth fields. -/
theorem deltaBase_sm (hLC : Submission.Diff.LCSmooth I M) [T2Space M]
    (G : ℝ → SMet I M) (t : ℝ) :
    VOpSm (I := I) (M := M) (deltaBase G t) := by sorry

/-- **The connection difference is `C^∞`-linear in its two slots**
(`covDiff_smul_section` + `covDiff_add_section`). -/
theorem deltaBase_linVal (hLC : Submission.Diff.LCSmooth I M) [T2Space M]
    (G : ℝ → SMet I M) (t : ℝ) :
    VOpLinVal (I := I) (M := M) (deltaBase G t) := by sorry

/-- **The metric tower `∇^{g_0,i} g_t` is tensorial and smooth** for every `i`. -/
theorem gtTower_tens_sm (hLC : Submission.Diff.LCSmooth I M) [T2Space M]
    (G : ℝ → SMet I M) (t : ℝ) :
    ∀ i : ℕ, Op2Tens (I := I) (M := M) (gtTower G t i) ∧ Op2Sm (I := I) (M := M) (gtTower G t i) := by
  sorry

/-- **The δ-tower `V_c = ∇^{g_0,c} δ` is tensorial and smooth** for every `c`. -/
theorem deltaTower_tens_sm (hLC : Submission.Diff.LCSmooth I M) [T2Space M]
    (G : ℝ → SMet I M) (t : ℝ) :
    ∀ c : ℕ, VOpTens (I := I) (M := M) (deltaTower G t c)
      ∧ VOpSm (I := I) (M := M) (deltaTower G t c) := by sorry


end Work.Diff.EXT.ConnCov.DT
