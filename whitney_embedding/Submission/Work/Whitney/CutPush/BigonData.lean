import Mathlib
import Submission.Work.Whitney.ArcFraming

/-!
# The hypothesis block of the Whitney bigon, packaged

Every statement in the `CutPush` development that consumes the data of `Work.Whitney.HasPushSigned`
carries the *same* forty-line hypothesis block: the smooth immersion `f : M → ℝ^{2n}`, the open `W`
with compact closure and its two clean transverse double points `(p₁,p₂)`, `(q₁,q₂)`, and the two
continuous arcs `γ₁ : p₁ → q₁`, `γ₂ : p₂ → q₂` realising the bigon with `hsign : OppositeType`.

This file collects that block into a single `Prop`-valued structure so that

* delegation requests and new statements only have to name it
  (retyping the forty lines by hand repeatedly corrupted statements — see
  `CutPush/NOTES_hasFingerData_S44.md` §13);
* a prover can project the single hypothesis they need (`h.immersed`, `h.opp`, …).

`Work.Whitney.CutPush.HasBigonData n M f W p₁ p₂ q₁ q₂ γ₁ γ₂` unfolds to exactly the hypothesis list
of `Work.Whitney.CutPush.wall_positive_part_bigon`
(`CutPush/wallPositivePartBigon_statement.lean`) and of `Work.Whitney.CutPush.wall_avoids_frontier`
(`CutPush/bigon_confinement_statement.lean`, declared as `bigon_confinement`), minus the single binder `hn : 3 ≤ n`.
-/

open scoped Manifold ContDiff
open Topology

namespace Work.Whitney.CutPush

/-- **The bigon hypothesis block.**  See the module docstring. -/
structure HasBigonData (n : ℕ) (M : Type*) [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) ((⊤ : ℕ∞) : WithTop ℕ∞) M]
    [T2Space M] [CompactSpace M] [SecondCountableTopology M]
    (f : M → EuclideanSpace ℝ (Fin (2 * n))) (W : Set M)
    (p₁ p₂ q₁ q₂ : M) (γ₁ γ₂ : ℝ → M) : Prop where
  /-- `f` is a smooth immersion. -/
  smooth : ContMDiff (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
    (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (2 * n)))) ((⊤ : ℕ∞) : WithTop ℕ∞) f
  immersed : ∀ y : M, Function.Injective
    (mfderiv (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (2 * n)))) f y)
  isOpen_W : IsOpen W
  isCompact_W : IsCompact (closure W)
  mem₁ : p₁ ∈ W
  mem₂ : p₂ ∈ W
  mem₃ : q₁ ∈ W
  mem₄ : q₂ ∈ W
  ne₁₂ : p₁ ≠ p₂
  ne₃₄ : q₁ ≠ q₂
  ne₁₃ : p₁ ≠ q₁
  ne₁₄ : p₁ ≠ q₂
  ne₂₃ : p₂ ≠ q₁
  ne₂₄ : p₂ ≠ q₂
  /-- the first double point -/
  val₁₂ : f p₁ = f p₂
  /-- the second double point -/
  val₃₄ : f q₁ = f q₂
  /-- `W` contains no other collisions -/
  clean : ∀ y z : M, y ∈ W → z ∈ W → f y = f z →
    y = z ∨ (y = p₁ ∧ z = p₂) ∨ (y = p₂ ∧ z = p₁) ∨ (y = q₁ ∧ z = q₂) ∨
      (y = q₂ ∧ z = q₁)
  /-- nothing in `W` collides with anything outside it -/
  sep : ∀ y z : M, y ∈ W → z ∉ W → f y ≠ f z
  /-- the first double point is transverse -/
  transP : (mfderiv (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (2 * n)))) f p₁).range ⊔
    (mfderiv (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (2 * n)))) f p₂).range = ⊤
  /-- the second double point is transverse -/
  transQ : (mfderiv (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (2 * n)))) f q₁).range ⊔
    (mfderiv (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (2 * n)))) f q₂).range = ⊤
  cont₁ : Continuous γ₁
  cont₂ : Continuous γ₂
  arc₁₀ : γ₁ 0 = p₁
  arc₁₁ : γ₁ 1 = q₁
  arc₂₀ : γ₂ 0 = p₂
  arc₂₁ : γ₂ 1 = q₂
  arcW₁ : ∀ t : ℝ, t ∈ Set.Icc (0 : ℝ) 1 → γ₁ t ∈ W
  arcW₂ : ∀ t : ℝ, t ∈ Set.Icc (0 : ℝ) 1 → γ₂ t ∈ W
  inj₁ : Set.InjOn γ₁ (Set.Icc (0 : ℝ) 1)
  inj₂ : Set.InjOn γ₂ (Set.Icc (0 : ℝ) 1)
  disj : ∀ s : ℝ, s ∈ Set.Icc (0 : ℝ) 1 → ∀ t : ℝ, t ∈ Set.Icc (0 : ℝ) 1 →
    γ₁ s = γ₂ t → (s = 0 ∧ t = 0) ∨ (s = 1 ∧ t = 1)
  /-- the two arcs' images meet only at the two ends -/
  endpt : ∀ s : ℝ, s ∈ Set.Icc (0 : ℝ) 1 → ∀ t : ℝ, t ∈ Set.Icc (0 : ℝ) 1 →
    f (γ₁ s) = f (γ₂ t) → (s = 0 ∧ t = 0) ∨ (s = 1 ∧ t = 1)
  /-- the sign correlation: the two double points have opposite types -/
  opp : Work.Whitney.OppositeType f γ₁ γ₂ p₁ p₂ q₁ q₂

end Work.Whitney.CutPush
