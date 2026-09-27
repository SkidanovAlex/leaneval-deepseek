import Mathlib
import Submission.Work.Drive.PushDisc.milnorLens
import Submission.Work.Drive.PushDisc.asymChart
import Submission.Work.Drive.PushDisc.chartObligation
import Submission.Work.Drive.PushDisc.asymSignTransport
import Submission.Work.Whitney.PushSigned

/-!
# The configuration rows of the lens wiring (bundle for the sub-lemmas)

`Work.Drive.PushDisc.LWConfig n M` bundles exactly the hypothesis list of
`Work.Drive.PushDisc.lensWiringSolid` (the configuration of the Whitney-trick bigon), so that the
sub-lemmas of the lens wiring can be stated compactly as `(C : LWConfig (k+1) M)`.
-/

open scoped ContDiff Manifold
open Set

namespace Work.Drive.PushDisc

/-- **The configuration rows** of the target `lensWiringSolid`. -/
structure LWConfig (n : ℕ) (M : Type*) [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) ((⊤ : ℕ∞) : WithTop ℕ∞) M]
    [T2Space M] [CompactSpace M] [SecondCountableTopology M] where
  hn : 3 ≤ n
  f : M → EuclideanSpace ℝ (Fin (2 * n))
  hf : ContMDiff (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (2 * n)))) ((⊤ : ℕ∞) : WithTop ℕ∞) f
  himm : ∀ y : M, Function.Injective (mfderiv
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (2 * n)))) f y)
  W : Set M
  hWopen : IsOpen W
  hWcpt : IsCompact (closure W)
  p₁ : M
  p₂ : M
  q₁ : M
  q₂ : M
  hW₁ : p₁ ∈ W
  hW₂ : p₂ ∈ W
  hW₃ : q₁ ∈ W
  hW₄ : q₂ ∈ W
  hp₁p₂ : p₁ ≠ p₂
  hq₁q₂ : q₁ ≠ q₂
  hp₁q₁ : p₁ ≠ q₁
  hp₁q₂ : p₁ ≠ q₂
  hp₂q₁ : p₂ ≠ q₁
  hp₂q₂ : p₂ ≠ q₂
  hfp : f p₁ = f p₂
  hfq : f q₁ = f q₂
  hclean : ∀ y z : M, y ∈ W → z ∈ W → f y = f z →
      y = z ∨ (y = p₁ ∧ z = p₂) ∨ (y = p₂ ∧ z = p₁) ∨ (y = q₁ ∧ z = q₂) ∨
        (y = q₂ ∧ z = q₁)
  hsep : ∀ y z : M, y ∈ W → z ∉ W → f y ≠ f z
  hfibp : ∀ z : M, f z = f p₁ → z = p₁ ∨ z = p₂
  hfibq : ∀ z : M, f z = f q₁ → z = q₁ ∨ z = q₂
  htransP : (mfderiv (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
        (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (2 * n)))) f p₁).range ⊔
      (mfderiv (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
        (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (2 * n)))) f p₂).range = ⊤
  htransQ : (mfderiv (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
        (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (2 * n)))) f q₁).range ⊔
      (mfderiv (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
        (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (2 * n)))) f q₂).range = ⊤
  γ₁ : ℝ → M
  γ₂ : ℝ → M
  hγ₁ : Continuous γ₁
  hγ₂ : Continuous γ₂
  hγ₁0 : γ₁ 0 = p₁
  hγ₁1 : γ₁ 1 = q₁
  hγ₂0 : γ₂ 0 = p₂
  hγ₂1 : γ₂ 1 = q₂
  hγW₁ : ∀ t : ℝ, t ∈ Set.Icc (0 : ℝ) 1 → γ₁ t ∈ W
  hγW₂ : ∀ t : ℝ, t ∈ Set.Icc (0 : ℝ) 1 → γ₂ t ∈ W
  hγ₁inj : Set.InjOn γ₁ (Set.Icc (0 : ℝ) 1)
  hγ₂inj : Set.InjOn γ₂ (Set.Icc (0 : ℝ) 1)
  hγ₁smooth : ContMDiff (modelWithCornersSelf ℝ ℝ)
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) ((⊤ : ℕ∞) : WithTop ℕ∞) γ₁
  hγ₂smooth : ContMDiff (modelWithCornersSelf ℝ ℝ)
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) ((⊤ : ℕ∞) : WithTop ℕ∞) γ₂
  hγ₁imm : ∀ t : ℝ, t ∈ Set.Icc (0 : ℝ) 1 → Function.Injective (mfderiv
      (modelWithCornersSelf ℝ ℝ)
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) γ₁ t)
  hγ₂imm : ∀ t : ℝ, t ∈ Set.Icc (0 : ℝ) 1 → Function.Injective (mfderiv
      (modelWithCornersSelf ℝ ℝ)
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) γ₂ t)
  hγdisj : ∀ s : ℝ, s ∈ Set.Icc (0 : ℝ) 1 → ∀ t : ℝ, t ∈ Set.Icc (0 : ℝ) 1 →
      γ₁ s = γ₂ t → (s = 0 ∧ t = 0) ∨ (s = 1 ∧ t = 1)
  hγend : ∀ s : ℝ, s ∈ Set.Icc (0 : ℝ) 1 → ∀ t : ℝ, t ∈ Set.Icc (0 : ℝ) 1 →
      f (γ₁ s) = f (γ₂ t) → (s = 0 ∧ t = 0) ∨ (s = 1 ∧ t = 1)
  hsign : Work.Whitney.OppositeType f γ₁ γ₂ p₁ p₂ q₁ q₂

end Work.Drive.PushDisc
