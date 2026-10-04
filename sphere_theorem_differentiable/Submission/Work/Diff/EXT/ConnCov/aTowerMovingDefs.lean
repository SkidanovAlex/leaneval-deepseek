import Mathlib
import Submission.Work.Diff.EXT.ATower.Defs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The packed calculus for the two-tower comparison (`aTower_moving_bound`)

`Work.Diff.EXT.ConnCov.aTower_moving_bound` converts bounds on the *fixed*-connection tower
`tower (lcOf (G 0)) aOf k` into bounds on the *moving*-connection tower `tower (lcOf (G t)) aOf k`.
The tool is the flip identity `step cov_t τ = step cov_0 τ + insAll δ τ`
(`Work.Diff.EXT.ATower.step_flip`, proved): writing `pD cov` for the recursion step `step cov` in the
*packed* convention (slot `0` of the tuple is the direction, slots `1..N` are the slots of the
object) and `Ins δ` for `insAll δ`, one has

  `pD cov_t = pD cov_0 + Ins δ`

so that `tower (lcOf (G t)) aOf k = (pD cov_0 + Ins δ)^k aOf` — a finite sum of **word objects**
`W(w) aOf`.  Bounding them needs the derivative of an insertion, which is the identity `pD_Ins`
(module `Submission.Work.Diff.EXT.ConnCov.pD_Ins`): for a `(1,2)`-tensor `Δ` and an object `τ`,

  `pD cov (Ins Δ τ) = (Δ inserted into the slots of `pD cov τ`) + (∇_dir Δ inserted into `τ`)`

where the second summand inserts the *honest tensor derivative* `∇_dir Δ` of `Δ` along the outer
direction into `τ`.  The pairing-direction correction of the covariant derivative and the
`Δ(X,∇Z)` term of the Leibniz rule cancel exactly, which is why no jets appear in the identity.

The bound shape used everywhere is the *monotone* one, `Bnd1 τ C`: it is monotone in the set of
slots (so the "deleted slot" of the identity costs nothing) and converts into the product shape of
the target `ValBound` by homogeneity of the objects (scale the tuple by `λ` and let `λ → ∞`).
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology BigOperators
open Bundle ContDiff Set VectorField CovariantDerivative Metric

namespace Work.Diff.EXT.ConnCov
namespace AMB

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M]

/-- A tangent field on `M`. -/
abbrev TF := Π y : M, TangentSpace I y

/-- A `real`-valued tensor-valued expression with `N` slots. -/
abbrev Fam (N : ℕ) := (Fin N → TF (I:=I) (M:=M)) → M → ℝ

/-- A `(1,2)`-tensor field as a function of two fields (section and direction). -/
abbrev Tens12 := TF (I:=I) (M:=M) → TF (I:=I) (M:=M) → TF (I:=I) (M:=M)

/-- **The packed covariant derivative**: slot `0` of the tuple is the direction and slots `1..N` are
the slots of `τ`; the connection corrections are applied in all `N` slots of `τ`. -/
noncomputable def pD (cov : CovariantDerivative I E (TangentSpace I (M := M))) {N : ℕ}
    (τ : Fam (I:=I) (M:=M) N) : Fam (I:=I) (M:=M) (N+1) :=
  fun F x => mvfderiv I (τ (fun j : Fin N => F j.succ)) x (F 0 x)
    - ∑ j : Fin N, τ (Function.update (fun i : Fin N => F i.succ) j
        (fun y => cov (F j.succ) y (F 0 y))) x

/-- **The insertion**: `Ins Δ τ` is `τ` with every slot field `τσ_j` replaced by `Δ τσ_j dir`, where
`dir` is slot `0` of the tuple.  This is `Work.Diff.EXT.ConnCov.insAll` in the packed convention. -/
noncomputable def Ins {N : ℕ} (Δ : Tens12 (I:=I) (M:=M))
    (τ : Fam (I:=I) (M:=M) N) : Fam (I:=I) (M:=M) (N+1) :=
  fun F x => ∑ j : Fin N, τ (Function.update (fun i : Fin N => F i.succ) j
    (Δ (F j.succ) (F 0))) x

/-- The honest tensor derivative `∇_W Δ` of a `(1,2)`-tensor field `Δ` along the field `W`. -/
noncomputable def nab (cov : CovariantDerivative I E (TangentSpace I (M := M))) (W : TF (I:=I) (M:=M))
    (Δ : Tens12 (I:=I) (M:=M)) : Tens12 (I:=I) (M:=M) :=
  fun X Z => fun y => cov (Δ X Z) y (W y)
    - Δ (fun y' => cov X y' (W y')) Z y - Δ X (fun y' => cov Z y' (W y')) y

/-- The injection `Fin (N+1) → Fin (N+2)` skipping index `1`. -/
def skip (N : ℕ) : Fin (N+1) → Fin (N+2) := Fin.cases 0 (fun k : Fin N => (k.succ).succ)

/-- The injection `Fin N → Fin (N+2)`, `j ↦ j + 2`. -/
def skip2 (N : ℕ) : Fin N → Fin (N+2) := fun j => (j.succ).succ

@[simp] lemma skip_zero (N : ℕ) : skip N 0 = 0 := rfl
@[simp] lemma skip_succ (N : ℕ) (j : Fin N) : skip N j.succ = (j.succ).succ := rfl
@[simp] lemma skip2_apply (N : ℕ) (j : Fin N) : skip2 N j = (j.succ).succ := rfl

/-- **The tautological Leibniz rule** (the definition of `pD` read backwards): the ordinary
derivative of `τ` applied to a tuple of fields is its covariant derivative minus the corrections. -/
theorem mvfderiv_eq_pD_add (cov : CovariantDerivative I E (TangentSpace I (M := M))) {N : ℕ}
    (τ : Fam (I:=I) (M:=M) N) (Y : TF (I:=I) (M:=M)) (H : Fin N → TF (I:=I) (M:=M)) (x : M) :
    mvfderiv I (τ H) x (Y x)
      = pD cov τ (Fin.cons Y H) x
        + ∑ j : Fin N, τ (Function.update H j (fun y => cov (H j) y (Y y))) x := by
  simp only [pD, Fin.cons_zero, Fin.cons_succ]
  ring

/-- **Packed slot additivity**: `τ` is additive in each slot over smooth fields. -/
def SlotAddP {N : ℕ} (τ : Fam (I:=I) (M:=M) N) : Prop :=
  ∀ (j : Fin N) (H : Fin N → TF (I:=I) (M:=M)) (W W' : TF (I:=I) (M:=M)),
    (∀ i, Work.Diff.EXT.ATower.SmE I M (H i)) → Work.Diff.EXT.ATower.SmE I M W →
    Work.Diff.EXT.ATower.SmE I M W' →
    ∀ x, τ (Function.update H j (W + W')) x = τ (Function.update H j W) x
      + τ (Function.update H j W') x

/-- Smoothness of a packed object on smooth tuples. -/
def SmP {N : ℕ} (τ : Fam (I:=I) (M:=M) N) : Prop :=
  ∀ (H : Fin N → TF (I:=I) (M:=M)), (∀ i, Work.Diff.EXT.ATower.SmE I M (H i)) →
    Work.Diff.EXT.ATower.SmF I M (τ H)

/-- **The monotone bound shape**: a bound for *all* smooth tuples by `C ∏_j (1 + ‖F_j(x)‖_t)`.  It is
monotone in the set of slots, which is what makes the deleted slot of `pD_Ins` harmless, and it is
converted into the product shape of the target `ValBound` by homogeneity (scale the tuple). -/
def Bnd1 (G : ℝ → SMet I M) (t : ℝ) {N : ℕ} (τ : Fam (I:=I) (M:=M) N) (C : ℝ) : Prop :=
  ∀ (F : Fin N → TF (I:=I) (M:=M)) (x : M),
    (∀ j, Work.Diff.EXT.ATower.SmE I M (F j)) →
    |τ F x| ≤ C * ∏ j, (1 + Real.sqrt ((G t).inner x (F j x) (F j x)))

/-- The δ-derivative bound shape: a bound for the value of a vector-valued `(1,2+c)`-tensor (a `c`-th
covariant derivative of the connection difference `δ = covDiff G t`) at `x`, measured in the `G t`
metric, for all smooth tuples. -/
def BndV (G : ℝ → SMet I M) (t : ℝ) {c : ℕ}
    (Θ : (Fin c → TF (I:=I) (M:=M)) → TF (I:=I) (M:=M) → TF (I:=I) (M:=M) → TF (I:=I) (M:=M))
    (C : ℝ) : Prop :=
  ∀ (v : Fin c → TF (I:=I) (M:=M)) (X Z : TF (I:=I) (M:=M)),
    (∀ i, Work.Diff.EXT.ATower.SmE I M (v i)) → Work.Diff.EXT.ATower.SmE I M X →
    Work.Diff.EXT.ATower.SmE I M Z → ∀ x : M,
    Real.sqrt ((G t).inner x (Θ v X Z x) (Θ v X Z x))
      ≤ C * (∏ i, (1 + Real.sqrt ((G t).inner x (v i x) (v i x))))
          * (1 + Real.sqrt ((G t).inner x (X x) (X x)))
          * (1 + Real.sqrt ((G t).inner x (Z x) (Z x)))


/-- Reading a curried `Op3 k` object (`Work.Diff.EXT.ATower.Op3`) as a packed object with
`k + 3` slots: the first `k` slots are the direction tuple, the last three the value slots. -/
noncomputable def pack {k : ℕ} (τ : Work.Diff.EXT.ATower.Op3 (I:=I) (M:=M) k) : Fam (I:=I) (M:=M) (k+3) :=
  fun F => τ (fun i : Fin k => F (Fin.castAdd 3 i)) (F (Fin.natAdd k 0))
    (F (Fin.natAdd k 1)) (F (Fin.natAdd k 2))

@[simp] lemma pack_apply {k : ℕ} (τ : Work.Diff.EXT.ATower.Op3 (I:=I) (M:=M) k)
    (F : Fin (k+3) → TF (I:=I) (M:=M)) (x : M) :
    pack τ F x = τ (fun i : Fin k => F (Fin.castAdd 3 i)) (F (Fin.natAdd k 0))
      (F (Fin.natAdd k 1)) (F (Fin.natAdd k 2)) x := rfl

end AMB
end Work.Diff.EXT.ConnCov
