import Mathlib
import Submission.Work.Diff.EXT.reactDefs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The jet calculus: strength of packed operators, the Leibniz (product) rule, and the
contraction of a strongly bounded operator with a vector-valued one

This module (sorry-free definitions) fixes the vocabulary of the two general estimates that the
connection-variation source of the reaction ladder needs.

* `Work.Diff.EXT.evolX.StrongAt g x p C S` — the **single-level strength** of a packed operator `S`
  (arity `K`): its `a`-th jet at `x` is bounded by `C a · √(|∇^{p+a} Rm|²)` times the product of the
  metric norms of the entries of the tuple.  This is the shape in which the individual factors of a
  quadratic curvature expression are bounded: the tower `∇^m Rm` has strength `m`, and the first
  variation `∂ₜ∇` of the Levi-Civita connection along a Ricci flow (equivalently `∇Ric`, by the
  contracted second Bianchi identity) has strength `1`.

* `Work.Diff.EXT.evolX.ShapeAt g x m C S` — the **shape strength**: the `a`-th jet is bounded by
  `C a · Shape g x (m+a)` times the product of the norms, where
  `Shape g x m = ∑_{i ≤ m} √f_i √f_{m-i}`.  This is the shape of a *product*: a product of a
  level-`p` and a level-`q` factor has shape strength `p + q`.

* `Work.Diff.EXT.evolX.mulOp A B` — the **product** of two packed operators acting on disjoint
  (concatenated) tuples; the Leibniz rule of the jet calculus is the statement that the jets of a
  product are the sum, over the `2^j` distributions of the differentiation directions among the two
  factors, of products of jets of the factors.

* `Work.Diff.EXT.evolX.substOp g k s V` — the **contraction**: the level-`k` tower `∇^k Rm` with its
  `s`-th slot filled by the field produced by a vector-valued operator `V`; the resulting operator has
  arity `k + 5` and shape strength `(k − 4) + 1 = k − 3`.

The two consumers are the connection-variation source `Work.Diff.EXT.evolX.connVarOp` (where `V` is
`∂ₜ∇`, whose pairing strength is `Work.Diff.EXT.evolX.connVar_pair_jets`) and the quadratic reaction
`Q(Rm)` (`Work.Diff.EXT.reaction0_jets`, the case of two level-`0` factors).
-/

set_option linter.unusedSectionVars false
set_option maxHeartbeats 800000

open scoped Manifold ContDiff Bundle Topology BigOperators

namespace Work.Diff.EXT.evolX

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M]

/-- **The single-level strength of a packed operator.** -/
def StrongAt (g : Submission.Diff.SMet I M) (x : M) {K : ℕ} (p : ℕ) (C : ℕ → ℝ)
    (S : (Fin K → Work.Diff.EXT.TField (I := I) (M := M)) → M → ℝ) : Prop :=
  ∀ (a : ℕ) (G : Fin (K + a) → Work.Diff.EXT.TField (I := I) (M := M)),
    (∀ i, Work.Diff.EXT.SmoothF (I := I) (M := M) (G i)) →
    |Work.Diff.EXT.jetAll g a K S G x|
      ≤ C a * Real.sqrt (Work.Diff.EXT.curvNormK g x (p + a))
        * ∏ r : Fin (K + a), Real.sqrt (g.inner x (G r x) (G r x))

/-- **The shape strength of a packed operator.** -/
def ShapeAt (g : Submission.Diff.SMet I M) (x : M) {K : ℕ} (m : ℕ) (C : ℕ → ℝ)
    (S : (Fin K → Work.Diff.EXT.TField (I := I) (M := M)) → M → ℝ) : Prop :=
  ∀ (a : ℕ) (G : Fin (K + a) → Work.Diff.EXT.TField (I := I) (M := M)),
    (∀ i, Work.Diff.EXT.SmoothF (I := I) (M := M) (G i)) →
    |Work.Diff.EXT.jetAll g a K S G x|
      ≤ C a * Work.Diff.EXT.Shape g x (m + a)
        * ∏ r : Fin (K + a), Real.sqrt (g.inner x (G r x) (G r x))

/-- **The product of two packed operators on disjoint (concatenated) tuples.**  The first `K₁`
entries of the tuple are the slots of `A`, the last `K₂` those of `B`, and the value is the pointwise
product. -/
noncomputable def mulOp {K₁ K₂ : ℕ}
    (A : (Fin K₁ → Work.Diff.EXT.TField (I := I) (M := M)) → M → ℝ)
    (B : (Fin K₂ → Work.Diff.EXT.TField (I := I) (M := M)) → M → ℝ) :
    (Fin (K₁ + K₂) → Work.Diff.EXT.TField (I := I) (M := M)) → M → ℝ :=
  fun F y => A (fun i => F (Fin.castAdd K₂ i)) y * B (fun i => F (Fin.natAdd K₁ i)) y

/-- **The contracted tower.**  The level-`k` tower `∇^k Rm` (a packed operator of arity `k + 4`) with
its `s`-th slot filled by the value at the current point of a vector-valued operator `V` whose two
arguments are the entries `0` and `s+1` of the tuple; the resulting packed operator has arity
`k + 5`.

The field inserted into the slot is the smooth extension `smoothExt y (V · y)` of the value of `V` at
the current point: since the tower depends only on the values of its slots
(`Work.Diff.EXT.ckt_val_dep_all`), this is the same operator as the one built with any other smooth
extension. -/
noncomputable def substOp (g : Submission.Diff.SMet I M) (k : ℕ) (s : Fin (k + 4))
    (V : (Fin 2 → Work.Diff.EXT.TField (I := I) (M := M)) → (y : M) → TangentSpace I y) :
    (Fin (k + 5) → Work.Diff.EXT.TField (I := I) (M := M)) → M → ℝ :=
  fun F y => Work.Diff.EXT.ckt g k
    (Function.update (fun i : Fin (k + 4) => F i.succ) s
      (Submission.Diff.smoothExt y (V (Fin.cons (F 0)
        (Fin.cons (F s.succ) (Fin.elim0 : Fin 0 →
          Work.Diff.EXT.TField (I := I) (M := M)))) y))) y

/-- **The pairing of a vector-valued operator with a field slot.**  `pairOp g V G y` is the metric
pairing at `y` of the value `V (G 0) (G 1) y` with the value `G 2 y`.  Its single-level strength
(with level `p`) is how the strength of the vector-valued operator `V` is expressed: the jets of the
pairing with *arbitrary* fields encode the jets of `V`.  This is the form of the workspace's
`Work.Diff.EXT.evolX.connVar_pair_jets` (the case `V = ∂ₜ∇`, `p = 1`). -/
noncomputable def pairOp (g : Submission.Diff.SMet I M)
    (V : (Fin 2 → Work.Diff.EXT.TField (I := I) (M := M)) → (y : M) → TangentSpace I y) :
    (Fin 3 → Work.Diff.EXT.TField (I := I) (M := M)) → M → ℝ :=
  fun G y => g.inner y (V (fun t : Fin 2 => G (Fin.castSucc t)) y) (G 2 y)

end Work.Diff.EXT.evolX
