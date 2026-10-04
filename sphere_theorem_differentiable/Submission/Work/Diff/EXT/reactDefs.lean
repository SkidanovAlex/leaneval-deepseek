import Mathlib
import Submission.Work.Diff.EXT.evolKDefs
import Submission.Work.Diff.GE.ExtTensor

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Diff.EXT

/-!
# Vocabulary for the reaction ladder of the `k`-th order Shi estimate

This module (sorry-free) collects the definitions shared by the proof of

`Work.Diff.EXT.EvolCompKFixReact k` (`Submission/Work/Diff/EXT/evolCompKFix_all.lean`),
i.e. the sharp (classical) `k`-th order Shi reaction estimate for `∇^k Rm` along a Ricci flow:

`D ≤ Δ(∇^k Rm) + C · (∑_{i+j=k} √f_i √f_j) · ∏‖·‖`,  `f_i = curvNormK (G t) x i`.

## The architecture (the *ladder*)

Write `T_k := ∇^k Rm` (the tower of `Work.Diff.EXT.ckt`) and let

`R_k := ∂ₜ T_k − Δ T_k`  (the *reaction*)

be the `(0,k+4)`-tensor field along the flow.  The classical identity
`∂ₜ∇^k Rm = Δ∇^kRm + ∑_{i+j=k} ∇^iRm ∗ ∇^jRm` says that `R_k` is a sum of metric
contractions of *two* jets whose levels add to `k`; hence `|R_k| ≤ C Shape_k`.

Instead of building a datatype of "reaction expressions" one carries the *ladder*

* `Ladder(k,j)`: for every flow, `t`, `x` and tuples, `|(∇^j R_k)(x)(vectors)| ≤ C_{k,j} Shape_{k+j} ∏‖vec‖`,

whose step is `R_{k+1} = ∇R_k + B_k`, whence `∇^j R_{k+1} = ∇^{j+1}R_k + ∇^j B_k`: the first term is
`Ladder(k, j+1)` (an induction hypothesis at level `k`, for *all* `j`), and the second needs only
`B_k`, which is **explicit**: `B_k = [∇,Δ]T_k + (∂ₜ∇)`-insertions into `T_k`.  The recursion
`(k,j) → (k−1,j+1) → … → (0, k+j)` therefore terminates at the explicit base case `R_0 = Q(Rm)`
(a *quadratic* expression in `Rm`): every `∇^j R_0` is a sum of products `∇^aRm ∗ ∇^bRm` with
`a + b = j` by the product rule (the metric is parallel), so `Ladder(0,j)` holds directly.

The definitions below are the vocabulary of that induction:

* `Shape g x m = ∑_{i ≤ m} √(f_i) √(f_{m−i})` — the reaction shape (`Shape 0 = f₀`);
* `extStep` — the generic packed covariant-derivative step; `extStep_ckt` records that the tower
  `ckt` is its iteration;
* `jetAll g j K S G x` — the `j`-fold iterated covariant derivative of the packed tensorial
  operator `S` (of arity `K`), evaluated at `x` on the *single* tuple `G` of arity `K + j` whose
  first `j` entries are the derivative directions.  **The iteration is the tower-style recursion
  `extStep`, not the iteration of `extD`**: the correction terms of `extStep` cover *all* the slots
  of the running tuple, including the inner direction slots, which is what makes `jetAll` the true
  tensor `∇^j S` (iterating `extD` with the directions kept as separate arguments misses the
  `∇_{X₀}X_r` corrections and is *not* tensorial in the inner directions);
* `JetBnd g x S m C` — the *ladder predicate*: **all** jets of `S` are bounded by `C · Shape_{m+j}`
  times the metric norms of the vectors.  `JetBnd` at `j = 0` is what the target
  `EvolCompKFixReact k` asks for (with `S = R_k`).

## Status

The mathematical inputs of the induction, as separate (delegated) lemmas, are

* `Work.Diff.EXT.reaction0_jets` — the base case `Ladder(0,j)`: the jets of the *quadratic*
  level-`0` reaction `Q(Rm)` are bounded by `C Shape_j`.  (Pure Riemannian geometry: no flow is
  involved; the product rule plus the Cauchy–Schwarz bound for a metric contraction of two jets.)
* `Work.Diff.EXT.lapComm_tower` — the Weitzenböck commutator `[Δ, ∇]` for the tower, i.e. the
  bound on the term `[∇,Δ]T_k` of `B_k` (a tensor identity between `Δ(∇_X T_k)` and `∇_X(ΔT_k)`).
* the `(∂ₜ∇)`-insertions into `T_k`: `Work.Diff.EXT.ckt_step_tderiv` (**proved**: the `s`-derivative
  of one recursion step of the tower) with the bound `Work.Diff.EXT.connVar_bound` (**proved**) on
  the connection-variation tensor.
-/

set_option linter.unusedSectionVars false
set_option maxHeartbeats 800000

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology BigOperators
open Bundle ContDiff Set VectorField CovariantDerivative Metric

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M]

/-- **The reaction shape** `Shape g x m = ∑_{i=0}^{m} √(f_i) √(f_{m−i})`, where
`f_i = curvNormK g x i = |∇^i Rm|²`.  This is the sharp reaction shape of the `k`-th order Shi
estimate: `Shape g x 0 = f₀` and the classical reaction bound is `C Shape g x k ∏‖·‖`. -/
noncomputable def Shape (g : SMet I M) (x : M) (m : ℕ) : ℝ :=
  ∑ i ∈ Finset.range (m + 1), Real.sqrt (curvNormK g x i) * Real.sqrt (curvNormK g x (m - i))

/-- `0 ≤ Shape g x m`. -/
theorem Shape_nonneg (g : SMet I M) (x : M) (m : ℕ) : 0 ≤ Shape g x m :=
  Finset.sum_nonneg fun _ _ => mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)

/-- **The level arithmetic of the two-factor reaction**: a product of two jets of levels `a`, `b`
is bounded by `Shape (a+b)` — the term `(a,b)` of the defining sum, provided `a + b - a = b`. -/
theorem sqrt_mul_sqrt_le_Shape (g : SMet I M) (x : M) {a b m : ℕ} (hab : a + b = m) :
    Real.sqrt (curvNormK g x a) * Real.sqrt (curvNormK g x b) ≤ Shape g x m := by
  have ha : a ∈ Finset.range (m + 1) := Finset.mem_range.mpr (by omega)
  have key : Real.sqrt (curvNormK g x a) * Real.sqrt (curvNormK g x (m - a))
      ≤ Shape g x m :=
    Finset.single_le_sum (f := fun i => Real.sqrt (curvNormK g x i)
        * Real.sqrt (curvNormK g x (m - i)))
      (fun i _ => mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)) ha
  have hsub : m - a = b := by omega
  rwa [hsub] at key

/-- **The generic covariant-derivative step on packed field-level tensors.**
`extStep g S F` is `∇_{F 0}(S (F ∘ Fin.succ))` written out with the Leibniz corrections of the
`K` slots of `S` (all of them, including any direction slots already present), i.e. exactly the
recursion of the tower `Work.Diff.EXT.ckt` (see `extStep_ckt`, which is a definitional restatement
of `ckt_succ`). -/
noncomputable def extStep (g : SMet I M) {K : ℕ}
    (S : (Fin K → TField (I := I) (M := M)) → M → ℝ) :
    (Fin (K + 1) → TField (I := I) (M := M)) → M → ℝ :=
  fun F y =>
    (mvfderiv I (S (fun i : Fin K => F i.succ)) y) (F 0 y)
      - ∑ s : Fin K, S (Function.update (fun i : Fin K => F i.succ) s
          (dirF g ((fun i : Fin K => F i.succ) s) (F 0))) y

/-- The tower is the iterated `extStep` (definitional restatement of `ckt_succ`). -/
theorem extStep_ckt [T2Space M] (g : SMet I M) (K : ℕ)
    (F : Fin (K + 5) → TField (I := I) (M := M)) :
    ckt g (K + 1) F = extStep (I := I) (M := M) g (ckt g K) F := by
  funext y
  rw [ckt_succ]
  simp only [extStep, Pi.sub_apply, Finset.sum_apply]

/-- **The `j`-fold iterated covariant derivative** of a packed field-level tensorial operator `S`
of arity `K`: `jetAll g j K S G x` is the value at `x` of `(∇^{G 0} ∇^{G 1} … ∇^{G (j-1)} S)`
(the operator `S` taken on the last `K` entries of the tuple `G : Fin (K + j) → TField`).

This is the iterate of `extStep`, i.e. the *tower-style* recursion: at every stage the correction
terms involve *all* the slots of the running tuple (the operator's slots and the inner direction
slots), so `jetAll` really is the tensor `∇^j S`.  In particular `jetAll g j (k+4) (ckt g k)` is the
tower `ckt g (k+j)` up to the reindexing of the tuple. -/
noncomputable def jetAll (g : SMet I M) : ∀ (j K : ℕ),
    ((Fin K → TField (I := I) (M := M)) → M → ℝ) →
      (Fin (K + j) → TField (I := I) (M := M)) → M → ℝ
  | 0, K, S => fun F x => S F x
  | l + 1, K, S => fun F x =>
      extStep (I := I) (M := M) g
        (fun (F' : Fin (K + l) → TField (I := I) (M := M)) => fun (y : M) =>
          jetAll g l K S F' y) F x

/-- **The ladder predicate**: the `j`-th jet of the packed tensorial operator `S` at `x` is bounded
by `C j · Shape g x (m + j)` times the product of the metric norms of the `K + j` vectors of the
tuple.  `m` is the *level* of `S` (`S` is a sum of metric contractions of two jets whose levels add
to `m`), so that its `j`-th jet is bounded by `Shape (m+j)`.

**The constant is a function of the jet order `j`** (`C : ℕ → ℝ`), and this is essential: the
product rule gives `∇^j(A ∗ B) = ∑_{i≤j} binom(j,i) ∇^i A ∗ ∇^{j−i}B`, so the constants grow like
`2^j` and no single real bounds all orders at once (this is why the base case
`Work.Diff.EXT.reaction0_jets` is stated `∀ j, ∃ C` and not `∃ C, ∀ j`). -/
def JetBnd (g : SMet I M) (x : M) {K : ℕ}
    (S : (Fin K → TField (I := I) (M := M)) → M → ℝ) (m : ℕ) (C : ℕ → ℝ) : Prop :=
  ∀ (j : ℕ) (G : Fin (K + j) → TField (I := I) (M := M)),
    (∀ i, Work.Diff.GE.SmoothFieldT (I := I) (M := M) (G i)) →
    |jetAll g j K S G x| ≤ C j * Shape g x (m + j)
      * ∏ r : Fin (K + j), Real.sqrt (g.inner x (G r x) (G r x))

end Work.Diff.EXT
