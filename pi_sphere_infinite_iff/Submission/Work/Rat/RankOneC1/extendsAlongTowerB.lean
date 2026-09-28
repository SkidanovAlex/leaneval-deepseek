import Mathlib
import Submission.Work.Serre.towerStepMap
import Submission.Work.Serre.E3aModel

namespace Work.Rat.RankOneC1

/-- **The tower step, iterated.**  If `π_{n+2}(L, l₀)` vanishes for all `n ≤ K`, a based map
`h₀ : towerB … 0 → L` which is a bijection on `π₁` extends to the `(K+1)`-st stage of the model
tower, and the extension is still a bijection on `π₁`.

The proof is the induction on `k` whose step is `Work.Serre.towerStepMap`, applied to the stage
`towerB B b₀ s₀ (k+1)`. -/
theorem extendsAlongTowerB {B : Type} [TopologicalSpace B] (b₀ : B)
    (s₀ : Work.Serre.CWModel.StA B b₀ 0) (K : ℕ)
    {L : Type} [TopologicalSpace L] (l₀ : L)
    (hK : ∀ n : ℕ, n ≤ K → Subsingleton (HomotopyGroup (Fin (n + 2)) L l₀))
    (h₀ : C((Work.Serre.E3aModel.towerB B b₀ s₀ 0).Y, L))
    (h₀b : h₀ (Work.Serre.E3aModel.towerB B b₀ s₀ 0).y₀ = l₀)
    (h₀bij : Function.Bijective (Work.Serre.piMapN h₀ 1
      (Work.Serre.E3aModel.towerB B b₀ s₀ 0).y₀)) :
    ∃ h : C((Work.Serre.E3aModel.towerB B b₀ s₀ (K + 1)).Y, L),
      h (Work.Serre.E3aModel.towerB B b₀ s₀ (K + 1)).y₀ = l₀ ∧
      Function.Bijective (Work.Serre.piMapN h 1
        (Work.Serre.E3aModel.towerB B b₀ s₀ (K + 1)).y₀) := by
  -- the extension exists at level `k + 1` for every `k` with vanishing `π_{n+2}(L)`, `n ≤ k`
  have key : ∀ k : ℕ,
      (∀ n : ℕ, n ≤ k → Subsingleton (HomotopyGroup (Fin (n + 2)) L l₀)) →
      ∃ h : C((Work.Serre.E3aModel.towerB B b₀ s₀ (k + 1)).Y, L),
        h (Work.Serre.E3aModel.towerB B b₀ s₀ (k + 1)).y₀ = l₀ ∧
        Function.Bijective (Work.Serre.piMapN h 1
          (Work.Serre.E3aModel.towerB B b₀ s₀ (k + 1)).y₀) := by
    intro k
    induction k with
    | zero =>
      -- the first two steps (the generator step and the killing step over `s₀`)
      intro hk
      exact Work.Serre.towerStepMap s₀ l₀ h₀ h₀b h₀bij (hk 0 le_rfl)
    | succ k ih =>
      intro hk
      obtain ⟨h, hb, hbij⟩ := ih (fun n hn => hk n (Nat.le_succ_of_le hn))
      -- the two steps over the stage `towerB B b₀ s₀ (k + 1)`
      exact Work.Serre.towerStepMap (Work.Serre.E3aModel.towerB B b₀ s₀ (k + 1)) l₀ h hb hbij
        (hk (k + 1) le_rfl)
  exact key K hK

end Work.Rat.RankOneC1
