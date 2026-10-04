import Mathlib
import Submission.Work.Diff.EXT.ConnCov.honestTower
import Submission.Work.Diff.EXT.ConnCov.RicTowerDefs
import Submission.Work.Diff.EXT.ConnCov.RicTr.baseRic_sm

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Diff.EXT.ConnCov

theorem baseRic_tower_hypotheses
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M]
    [I.Boundaryless] [T2Space M]
    (hLC : Submission.Diff.LCSmooth I M) (g : Submission.Diff.SMet I M) :
    (∀ (v : Fin 0 → Π y : M, TangentSpace I y) (A B Cc : Π y : M, TangentSpace I y),
      Work.Diff.EXT.ATower.SmE I M A → Work.Diff.EXT.ATower.SmE I M B →
      Work.Diff.EXT.ATower.SmE I M Cc →
      Work.Diff.EXT.ATower.SmF I M (Work.Diff.EXT.ConnCov.baseRic (I := I) (M := M) g v A B Cc)) ∧
    (∀ (v : Fin 0 → Π y : M, TangentSpace I y)
      (A₁ A₂ : Π y : M, TangentSpace I y) (f₁ f₂ : M → ℝ)
      (B Cc : Π y : M, TangentSpace I y) (x : M),
      Work.Diff.EXT.ATower.SmF I M f₁ → Work.Diff.EXT.ATower.SmF I M f₂ →
      Work.Diff.EXT.ATower.SmE I M A₁ → Work.Diff.EXT.ATower.SmE I M A₂ →
      Work.Diff.EXT.ATower.SmE I M B → Work.Diff.EXT.ATower.SmE I M Cc →
      Work.Diff.EXT.ConnCov.baseRic (I := I) (M := M) g v (f₁ • A₁ + f₂ • A₂) B Cc x
        = f₁ x * Work.Diff.EXT.ConnCov.baseRic (I := I) (M := M) g v A₁ B Cc x
          + f₂ x * Work.Diff.EXT.ConnCov.baseRic (I := I) (M := M) g v A₂ B Cc x) ∧
    (∀ (v : Fin 0 → Π y : M, TangentSpace I y)
      (B₁ B₂ : Π y : M, TangentSpace I y) (f₁ f₂ : M → ℝ)
      (A Cc : Π y : M, TangentSpace I y) (x : M),
      Work.Diff.EXT.ATower.SmF I M f₁ → Work.Diff.EXT.ATower.SmF I M f₂ →
      Work.Diff.EXT.ATower.SmE I M B₁ → Work.Diff.EXT.ATower.SmE I M B₂ →
      Work.Diff.EXT.ATower.SmE I M A → Work.Diff.EXT.ATower.SmE I M Cc →
      Work.Diff.EXT.ConnCov.baseRic (I := I) (M := M) g v A (f₁ • B₁ + f₂ • B₂) Cc x
        = f₁ x * Work.Diff.EXT.ConnCov.baseRic (I := I) (M := M) g v A B₁ Cc x
          + f₂ x * Work.Diff.EXT.ConnCov.baseRic (I := I) (M := M) g v A B₂ Cc x) ∧
    (∀ (v : Fin 0 → Π y : M, TangentSpace I y) (A A' B B' C C' : Π y : M, TangentSpace I y)
      (x : M), Work.Diff.EXT.ATower.SmE I M A → Work.Diff.EXT.ATower.SmE I M A' →
      Work.Diff.EXT.ATower.SmE I M B → Work.Diff.EXT.ATower.SmE I M B' →
      Work.Diff.EXT.ATower.SmE I M C → Work.Diff.EXT.ATower.SmE I M C' →
      A x = A' x → B x = B' x → C x = C' x →
      Work.Diff.EXT.ConnCov.baseRic (I := I) (M := M) g v A B C x
        = Work.Diff.EXT.ConnCov.baseRic (I := I) (M := M) g v A' B' C' x) ∧
    Work.Diff.EXT.ConnCov.CIndep (Work.Diff.EXT.ConnCov.baseRic (I := I) (M := M) g) := by
  classical
  -- the Levi-Civita connection of `g` is a smooth covariant derivative (contract T1)
  have hcov : CovariantDerivative.ContMDiffCovariantDerivative (Submission.Diff.lcOf g)
      (⊤ : ℕ∞) := (hLC g).1.some
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · -- smoothness on smooth fields
    intro v A B Cc hA hB hC
    exact RicTr.baseRic_sm (I := I) (M := M) g hcov A B Cc hA hB hC
  · -- linearity in the first value slot
    intro v A₁ A₂ f₁ f₂ B Cc x _ _ hA₁ hA₂ hB hC
    exact baseRic_linA (I := I) (M := M) hcov v A₁ A₂ f₁ f₂ B Cc x
  · -- linearity in the second value slot
    intro v B₁ B₂ f₁ f₂ A Cc x _ _ hB₁ hB₂ hA hC
    exact baseRic_linB (I := I) (M := M) hcov v B₁ B₂ f₁ f₂ A Cc x
  · -- value dependence
    intro v A A' B B' C C' x _ _ _ _ _ _ hA hB _
    exact baseRic_vd (I := I) (M := M) v A A' B B' C C' x hA hB
  · -- third-slot independence
    exact baseRic_cind (I := I) (M := M) g

end Work.Diff.EXT.ConnCov
