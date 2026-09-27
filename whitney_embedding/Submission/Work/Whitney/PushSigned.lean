import Mathlib
import Submission.Work.Whitney.EndgameNFTrans
import Submission.Work.Whitney.ArcFraming

/-!
# The signed collar ("bigon") push interface

The workspace's push interface `Work.Whitney.HasPushNFT` is *sign-free*: it asks for the ambient
diffeomorphism data of the Whitney move at the two double points of a clean region without any
hypothesis comparing the two double points along the arcs.  Both readers of the review at
SESSION 14 flagged this as wrong: the classical Whitney move needs the two crossings to be of
*opposite* type along the bigon (otherwise the total degree on the bounding sphere is `±2 ≠ 0` and
no cut-and-paste map can disengage them), and nothing in the clean-region/arc hypotheses forces
that.  (`NOTES_framing_for_push.md` asks for exactly the framed hypothesis used below, and
`NOTES_compact_route_obstruction.md` explains why the local cut-form version cannot be the source
of a sign-free push.)

`Work.Whitney.HasPushSigned` below is `Work.Whitney.HasPushNFT` with the missing hypothesis added:
the two double points are of opposite type along the two arcs, in the sense of the (proved) framed
comparison `Work.Whitney.OppositeType f γ₁ γ₂ p₁ p₂ q₁ q₂` of `Submission/Work/Whitney/ArcFraming.lean`.

The endgame can supply that hypothesis: `Work.Whitney.exists_oppositeType_of_insertion` (proved)
produces a partner double point of the opposite type, so the pairs the endgame cancels are always
opposite-typed.
-/

namespace Work.Whitney

open scoped Manifold ContDiff
open Topology

set_option linter.unusedVariables false

/-- **The signed collar push.**  This is `Work.Whitney.HasPushNFT` with the framing hypothesis
`Work.Whitney.OppositeType f γ₁ γ₂ p₁ p₂ q₁ q₂` added; the conclusion is the ambient
diffeomorphism data of the Whitney move. -/
def HasPushSigned (n : ℕ) (M : Type*) [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (𝓡 n) ∞ M]
    [T2Space M] [CompactSpace M] [SecondCountableTopology M] : Prop :=
  ∀ (hn : 3 ≤ n) (f : M → EuclideanSpace ℝ (Fin (2 * n)))
      (hf : ContMDiff (𝓡 n) (𝓡 (2 * n)) ∞ f)
      (himm : ∀ y, Function.Injective (mfderiv (𝓡 n) (𝓡 (2 * n)) f y))
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
      (htransP : (mfderiv (𝓡 n) (𝓡 (2 * n)) f p₁).range ⊔
        (mfderiv (𝓡 n) (𝓡 (2 * n)) f p₂).range = ⊤)
      (htransQ : (mfderiv (𝓡 n) (𝓡 (2 * n)) f q₁).range ⊔
        (mfderiv (𝓡 n) (𝓡 (2 * n)) f q₂).range = ⊤)
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
    (hsign : OppositeType f γ₁ γ₂ p₁ p₂ q₁ q₂),
    Work.Whitney.HasAmbientPushData f W p₁ p₂ q₁ q₂

end Work.Whitney
