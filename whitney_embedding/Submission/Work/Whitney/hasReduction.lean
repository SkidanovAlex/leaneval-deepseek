import Mathlib
import Submission.Work.Whitney.cancellation_of_pushData
import Submission.Work.Whitney.reduce_double_points_abstract
import Submission.Work.Whitney.endgame_abstract
import Submission.Work.Whitney.exists_insertedDoublePoint

/-!
# The two interfaces of the endgame, instantiated up to the push construction

* `Work.Whitney.HasAmbientPush` is the leftover geometric input: the *existence* of the target-side
  push data (`Work.Whitney.HasAmbientPushData`) for a bigon with two opposite-signed double points.
  It is exactly what `Work.Whitney.exists_ambient_push_data`
  (`Submission/Work/Whitney/exists_ambient_push_data.lean`, currently blocked by an unrelated file
  being edited) proves.

* `Work.Whitney.hasCancellation_of_hasAmbientPush` turns it into the cancellation interface
  `Work.Whitney.HasCancellation`, using the proved
  `Work.Whitney.cancellation_of_pushData` (the gluing `i = ψ ∘ f` on the collar and the
  `pairDet`-preservation off `W`).

* `Work.Whitney.hasReduction_of` assembles the reduction interface `Work.Whitney.HasReduction` from
  `Work.Whitney.HasInsertion` (instantiated by `Work.Whitney.exists_insertedDoublePoint`) and
  `Work.Whitney.HasCancellation`, via `Work.Whitney.exists_reduce_double_points`.
-/

namespace Work.Whitney

open scoped Manifold ContDiff
open Topology

/-- **The leftover geometric input of the Whitney cancellation**: the bigon with two
opposite-signed transverse double points produces the target-side push data. -/
def HasAmbientPush (n : ℕ) (M : Type*) [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) ((⊤ : ℕ∞) : WithTop ℕ∞) M]
    [T2Space M] [CompactSpace M] [SecondCountableTopology M] : Prop :=
  ∀ (hn : 3 ≤ n)
    (f : M → EuclideanSpace ℝ (Fin (2 * n)))
    (hf : ContMDiff (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (2 * n)))) ((⊤ : ℕ∞) : WithTop ℕ∞) f)
    (himm : ∀ y, Function.Injective
      (mfderiv (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
        (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (2 * n)))) f y))
    (A : Set (OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n))))
    (hA : IsOrientedAtlas A)
    (W : Set M) (hWopen : IsOpen W) (hWcpt : IsCompact (closure W))
    (p₁ p₂ q₁ q₂ : M)
    (hW₁ : p₁ ∈ W) (hW₂ : p₂ ∈ W) (hW₃ : q₁ ∈ W) (hW₄ : q₂ ∈ W)
    (hp₁p₂ : p₁ ≠ p₂) (hq₁q₂ : q₁ ≠ q₂)
    (hp₁q₁ : p₁ ≠ q₁) (hp₁q₂ : p₁ ≠ q₂) (hp₂q₁ : p₂ ≠ q₁) (hp₂q₂ : p₂ ≠ q₂)
    (hfp : f p₁ = f p₂) (hfq : f q₁ = f q₂)
    (hclean : ∀ y z : M, y ∈ W → z ∈ W → f y = f z →
      y = z ∨ (y = p₁ ∧ z = p₂) ∨ (y = p₂ ∧ z = p₁) ∨ (y = q₁ ∧ z = q₂) ∨
        (y = q₂ ∧ z = q₁))
    (hsep : ∀ y z : M, y ∈ W → z ∉ W → f y ≠ f z)
    (γ₁ γ₂ : ℝ → M) (hγ₁ : Continuous γ₁) (hγ₂ : Continuous γ₂)
    (hγ₁0 : γ₁ 0 = p₁) (hγ₁1 : γ₁ 1 = q₁) (hγ₂0 : γ₂ 0 = p₂) (hγ₂1 : γ₂ 1 = q₂)
    (hγW₁ : ∀ t : ℝ, t ∈ Set.Icc (0 : ℝ) 1 → γ₁ t ∈ W)
    (hγW₂ : ∀ t : ℝ, t ∈ Set.Icc (0 : ℝ) 1 → γ₂ t ∈ W)
    (hγ₁inj : Set.InjOn γ₁ (Set.Icc (0 : ℝ) 1))
    (hγ₂inj : Set.InjOn γ₂ (Set.Icc (0 : ℝ) 1))
    (hγdisj : ∀ s : ℝ, s ∈ Set.Icc (0 : ℝ) 1 → ∀ t : ℝ, t ∈ Set.Icc (0 : ℝ) 1 →
      γ₁ s = γ₂ t → (s = 0 ∧ t = 0) ∨ (s = 1 ∧ t = 1))
    (hγend : ∀ s : ℝ, s ∈ Set.Icc (0 : ℝ) 1 → ∀ t : ℝ, t ∈ Set.Icc (0 : ℝ) 1 →
      f (γ₁ s) = f (γ₂ t) → (s = 0 ∧ t = 0) ∨ (s = 1 ∧ t = 1))
    (hsign : OppositeSign A f p₁ p₂ q₁ q₂),
    HasAmbientPushData f W p₁ p₂ q₁ q₂

/-- The cancellation interface follows from the push construction. -/
theorem hasCancellation_of_hasAmbientPush {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) ((⊤ : ℕ∞) : WithTop ℕ∞) M]
    [T2Space M] [CompactSpace M] [SecondCountableTopology M]
    (h : HasAmbientPush n M) : HasCancellation n M := by
  intro hn f hf himm A hA W hWopen hWcpt p₁ p₂ q₁ q₂ hW₁ hW₂ hW₃ hW₄ hp₁p₂ hq₁q₂
    hp₁q₁ hp₁q₂ hp₂q₁ hp₂q₂ hfp hfq hclean hsep γ₁ γ₂ hγ₁ hγ₂ hγ₁0 hγ₁1 hγ₂0 hγ₂1
    hγW₁ hγW₂ hγ₁inj hγ₂inj hγdisj hγend hsign
  obtain ⟨W₀, O, ψ, σ, h₁, h₂, h₃, h₄, h₅, h₆, h₇, h₈, h₉, h₁₀, h₁₁, h₁₂, h₁₃, h₁₄, h₁₅,
    h₁₆⟩ := h hn f hf himm A hA.1 W hWopen hWcpt p₁ p₂ q₁ q₂ hW₁ hW₂ hW₃ hW₄ hp₁p₂ hq₁q₂
      hp₁q₁ hp₁q₂ hp₂q₁ hp₂q₂ hfp hfq hclean hsep γ₁ γ₂ hγ₁ hγ₂ hγ₁0 hγ₁1 hγ₂0 hγ₂1
      hγW₁ hγW₂ hγ₁inj hγ₂inj hγdisj hγend hsign
  exact cancellation_of_pushData hn f hf himm W hWopen p₁ p₂ q₁ q₂ hW₁ hW₂ hW₃ hW₄ hclean hsep
    W₀ O ψ σ h₁ h₂ h₃ h₄ h₅ h₆ h₇ h₈ h₉ h₁₂ h₁₃ h₁₀ h₁₁ h₁₄ h₁₅ h₁₆

/-- The insertion interface of the endgame. -/
theorem hasInsertion_of {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) ((⊤ : ℕ∞) : WithTop ℕ∞) M]
    [T2Space M] [CompactSpace M] [SecondCountableTopology M]
    (hn : 2 ≤ n) : HasInsertion n M :=
  fun f hf himm hfin A hA hsimple htrans p₁ p₂ hp₁p₂ hfp =>
    exists_insertedDoublePoint hn f hf himm hfin A hA hsimple htrans p₁ p₂ hp₁p₂ hfp

/-- The reduction interface of the endgame follows from the insertion and cancellation interfaces. -/
theorem hasReduction_of {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) ((⊤ : ℕ∞) : WithTop ℕ∞) M]
    [T2Space M] [CompactSpace M] [ConnectedSpace M] [SecondCountableTopology M]
    (hn : 3 ≤ n) (hins : HasInsertion n M) (hcancel : HasCancellation n M) :
    HasReduction n M :=
  fun f hf himm hfin A hA hsimple htrans p₁ p₂ hp₁p₂ hfp =>
    exists_reduce_double_points (M := M) hn hins hcancel f hf himm hfin A hA hsimple htrans
      p₁ p₂ hp₁p₂ hfp

end Work.Whitney
