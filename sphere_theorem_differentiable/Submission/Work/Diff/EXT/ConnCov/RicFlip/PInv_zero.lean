import Mathlib
import Submission.Work.Diff.EXT.ConnCov.RicFlip.TInvDefs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Diff.EXT.ConnCov.RicFlip

-- Base case of the induction: at level `0` the packed tower is the base operator applied to the
-- three value slots (`packTower_zero`), and the three invariant clauses of `PInv g base 0` are
-- *exactly* the hypotheses `hsm` (smoothness), `hlinA`/`hlinB`/`hlinC` (linearity in the three
-- value slots, pointwise at each `x` — turn them into equalities of functions with `funext`), and
-- `hvd` (value dependence at each `x`, which gives germ-locality: from `A =ᶠ[𝓝 x] A'` deduce
-- `A x = A' x` etc. and filter the neighbourhood where all three pairs agree).
-- `Fin.natAdd 0 (p : Fin 3)` is definitionally `p` (`rfl`); `Function.update` at a `Fin 3` slot is
-- handled by `fin_cases` + `Function.update_self`/`Function.update_of_ne`.

theorem PInv_zero
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M] [T2Space M]
    (g : Submission.Diff.SMet I M)
    {base : Work.Diff.EXT.ATower.Op3 (I := I) (M := M) 0}
    (hsm : ∀ (v : Fin 0 → (Π y : M, TangentSpace I y)) (A B C : Π y : M, TangentSpace I y),
      Work.Diff.EXT.ATower.SmE I M A → Work.Diff.EXT.ATower.SmE I M B →
      Work.Diff.EXT.ATower.SmE I M C → Work.Diff.EXT.ATower.SmF I M (base v A B C))
    (hvd : ∀ (b0 : Fin 0 → (Π y : M, TangentSpace I y))
      (A A' B B' C C' : Π y : M, TangentSpace I y) (x : M),
      Work.Diff.EXT.ATower.SmE I M A → Work.Diff.EXT.ATower.SmE I M A' →
      Work.Diff.EXT.ATower.SmE I M B → Work.Diff.EXT.ATower.SmE I M B' →
      Work.Diff.EXT.ATower.SmE I M C → Work.Diff.EXT.ATower.SmE I M C' →
      A x = A' x → B x = B' x → C x = C' x →
      base b0 A B C x = base b0 A' B' C' x)
    (hlinA : ∀ (b0 : Fin 0 → (Π y : M, TangentSpace I y))
      (X₁ X₂ : Π y : M, TangentSpace I y) (f₁ f₂ : M → ℝ),
      Work.Diff.EXT.ATower.SmF I M f₁ → Work.Diff.EXT.ATower.SmF I M f₂ →
      Work.Diff.EXT.ATower.SmE I M X₁ → Work.Diff.EXT.ATower.SmE I M X₂ →
      ∀ (B C : Π y : M, TangentSpace I y) (x : M),
      base b0 (f₁ • X₁ + f₂ • X₂) B C x
        = f₁ x * base b0 X₁ B C x + f₂ x * base b0 X₂ B C x)
    (hlinB : ∀ (b0 : Fin 0 → (Π y : M, TangentSpace I y))
      (X₁ X₂ : Π y : M, TangentSpace I y) (f₁ f₂ : M → ℝ),
      Work.Diff.EXT.ATower.SmF I M f₁ → Work.Diff.EXT.ATower.SmF I M f₂ →
      Work.Diff.EXT.ATower.SmE I M X₁ → Work.Diff.EXT.ATower.SmE I M X₂ →
      ∀ (A C : Π y : M, TangentSpace I y) (x : M),
      base b0 A (f₁ • X₁ + f₂ • X₂) C x
        = f₁ x * base b0 A X₁ C x + f₂ x * base b0 A X₂ C x)
    (hlinC : ∀ (b0 : Fin 0 → (Π y : M, TangentSpace I y))
      (X₁ X₂ : Π y : M, TangentSpace I y) (f₁ f₂ : M → ℝ),
      Work.Diff.EXT.ATower.SmF I M f₁ → Work.Diff.EXT.ATower.SmF I M f₂ →
      Work.Diff.EXT.ATower.SmE I M X₁ → Work.Diff.EXT.ATower.SmE I M X₂ →
      ∀ (A B : Π y : M, TangentSpace I y) (x : M),
      base b0 A B (f₁ • X₁ + f₂ • X₂) x
        = f₁ x * base b0 A B X₁ x + f₂ x * base b0 A B X₂ x) :
    Work.Diff.EXT.ConnCov.RicFlip.PInv g base 0 := by
  intro F hF
  refine ⟨?_, ?_, ?_⟩
  · -- smoothness: `packTower g base 0 F` is the base operator at the three value slots
    rw [packTower_zero]
    exact hsm (fun i : Fin 0 => i.elim0) (F 0) (F 1) (F 2) (hF 0) (hF 1) (hF 2)
  · -- linearity in each of the three value slots, pointwise
    intro s X₁ X₂ f₁ f₂ hX₁ hX₂ hf₁ hf₂
    funext x
    rw [packTower_zero]
    fin_cases s
    · exact hlinA (fun i : Fin 0 => i.elim0) X₁ X₂ f₁ f₂ hf₁ hf₂ hX₁ hX₂ (F 1) (F 2) x
    · exact hlinB (fun i : Fin 0 => i.elim0) X₁ X₂ f₁ f₂ hf₁ hf₂ hX₁ hX₂ (F 0) (F 2) x
    · exact hlinC (fun i : Fin 0 => i.elim0) X₁ X₂ f₁ f₂ hf₁ hf₂ hX₁ hX₂ (F 0) (F 1) x
  · -- germ-locality: intersect the three neighbourhoods where the slots agree pairwise
    intro x F' hF' hagree
    rw [packTower_zero]
    refine ((hagree 0).and ((hagree 1).and (hagree 2))).mono (fun y hy => ?_)
    exact hvd (fun i : Fin 0 => i.elim0) (F 0) (F' 0) (F 1) (F' 1) (F 2) (F' 2) y
      (hF 0) (hF' 0) (hF 1) (hF' 1) (hF 2) (hF' 2) hy.1 hy.2.1 hy.2.2

end Work.Diff.EXT.ConnCov.RicFlip
