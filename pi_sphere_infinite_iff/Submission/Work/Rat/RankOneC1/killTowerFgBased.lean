import Mathlib
import Submission.Work.RatHurewicz.killTowerFg
import Submission.Work.RatHurewicz.killHighFinite
import Submission.Work.RatHurewicz.killKernelFinite
import Submission.Work.RatHurewicz.killFamily_subsingleton
import Submission.Work.StemsB.killToFgModel
import Submission.Work.Serre.attachIncl_piMap_bijective_of_compress
import Submission.Work.Serre.attachIncl_pi0_bijective
import Submission.Work.RatHurewicz.ConnectivityBridge
import Submission.Work.Serre.piMapN_monoidHom
import Submission.Work.Serre.CWModel.Defs

namespace Work.Rat.RankOneC1

open scoped Topology Topology.Homotopy unitInterval

set_option linter.unusedVariables false

noncomputable section

/-- The auxiliary form of `killTowerFgBased`, inducting on the height `n` exactly as
`Work.RatHurewicz.killTowerFgAux` does, but carrying the additional conjunct `χ y₀ = y₀'` that
records that the base point of the new space is the image of the old one. -/
private theorem killTowerFgBasedAux (n : ℕ) :
    ∀ (k : ℕ), 1 ≤ k →
    ∀ (Y : Type) [TopologicalSpace Y] (y₀ : Y) (X : Type) [TopologicalSpace X] (φ : C(Y, X))
      [PathConnectedSpace Y],
      (∀ i : ℕ, k + 1 ≤ i → i ≤ k + n → ∀ x : X, Subsingleton (HomotopyGroup (Fin i) X x)) →
      Group.FG (HomotopyGroup (Fin 1) Y y₀) →
      Function.Injective (Work.Serre.piMapN φ 1 y₀) →
      (∀ j : ℕ, 2 ≤ j → j ≤ k → Subsingleton (HomotopyGroup (Fin j) Y y₀)) →
      ∃ (Y' : Type) (_ : TopologicalSpace Y') (y₀' : Y') (ψ : C(Y', X)) (χ : C(Y, Y')),
        ψ.comp χ = φ ∧ χ y₀ = y₀' ∧ PathConnectedSpace Y' ∧
        Group.FG (HomotopyGroup (Fin 1) Y' y₀') ∧
        Function.Injective (Work.Serre.piMapN ψ 1 y₀') ∧
        (∀ j : ℕ, 2 ≤ j → j ≤ k + n → Subsingleton (HomotopyGroup (Fin j) Y' y₀')) := by
  induction n with
  | zero =>
    intro k hk Y _ y₀ X _ φ _ hX hfg hinj hlo
    exact ⟨Y, inferInstance, y₀, φ, ContinuousMap.id Y, by ext y; rfl, rfl, inferInstance, hfg,
      hinj, fun j hj2 hj => hlo j hj2 (by omega)⟩
  | succ m ih =>
    intro k hk Y _ y₀ X _ φ _ hX hfg hinj hlo
    let ι := HomotopyGroup (Fin (k + 1)) Y y₀
    let f : ι → C(Work.RatHurewicz.cellSphere k, Y) := Work.RatHurewicz.killFamily k Y y₀
    let Y₁ : Type := Work.RatHurewicz.attachCells k Y ι f
    letI : TopologicalSpace Y₁ := inferInstance
    let χ₁ : C(Y, Y₁) := Work.RatHurewicz.attachIncl k Y ι f
    let y₁ : Y₁ := χ₁ y₀
    have hXstep : Subsingleton (HomotopyGroup (Fin (k + 1)) X (φ y₀)) :=
      hX (k + 1) le_rfl (by omega) (φ y₀)
    obtain ⟨ψ₁, hψ₁⟩ := Work.StemsB.killFamily_extend k Y y₀ X φ hXstep
    have hsurj₁ : Function.Surjective (Work.StemsB.πmap χ₁ 0 y₀) :=
      Work.RatHurewicz.surjective_piMap_attachIncl_of_le k Y ι f y₀ 0 (by omega)
    haveI hpc₁ : PathConnectedSpace Y₁ :=
      Work.Serre.CWModel.pathConnectedSpace_attachCells k Y ι f
    have hfg₁ : Group.FG (HomotopyGroup (Fin 1) Y₁ y₁) := by
      haveI := hfg
      exact Group.fg_of_surjective (f := Work.StemsB.πmap χ₁ 0 y₀) hsurj₁
    have hinj₁ : Function.Injective (Work.Serre.piMapN ψ₁ 1 y₁) :=
      Work.RatHurewicz.injective_piMap_of_comp_eq ψ₁ χ₁ y₀ φ hψ₁ hsurj₁ hinj
    have hlo₁ : ∀ j : ℕ, 2 ≤ j → j ≤ k + 1 → Subsingleton (HomotopyGroup (Fin j) Y₁ y₁) := by
      intro j hj2 hjk1
      rcases eq_or_lt_of_le hjk1 with heq | hlt
      · subst heq
        exact Work.RatHurewicz.killFamily_subsingleton k Y y₀
      · have hjk : j ≤ k := by omega
        have hb := Work.RatHurewicz.surjective_piMap_attachIncl_of_le k Y ι f y₀ (j - 1) (by omega)
        have hsi : j - 1 + 1 = j := Nat.sub_add_cancel (by omega)
        have h1 : Subsingleton (HomotopyGroup (Fin (j - 1 + 1)) Y y₀) := by
          simpa only [hsi] using hlo j hj2 hjk
        simpa only [hsi] using
          Work.StemsB.subsingleton_of_surjective (Work.StemsB.πmap χ₁ (j - 1) y₀) hb h1
    have hX' : ∀ i : ℕ, (k + 1) + 1 ≤ i → i ≤ (k + 1) + m →
        ∀ x : X, Subsingleton (HomotopyGroup (Fin i) X x) :=
      fun i hi hle => hX i (by omega) (by omega)
    obtain ⟨Y', instY', y₀', ψ', χ', hχ', hbased', hpc', hfg', hinj', hkilled'⟩ :=
      ih (k + 1) (by omega) Y₁ y₁ X ψ₁ hX' hfg₁ hinj₁ hlo₁
    refine ⟨Y', instY', y₀', ψ', χ'.comp χ₁, ?_, ?_, hpc', hfg', hinj', ?_⟩
    · rw [← ContinuousMap.comp_assoc, hχ', hψ₁]
    · rw [ContinuousMap.comp_apply]
      exact hbased'
    · intro j hj2 hle
      exact hkilled' j hj2 (by omega)

end

/-- This is `Work.RatHurewicz.killTowerFg` (`Submission/Work/RatHurewicz/killTowerFg.lean`, whose
proof `killTowerFgAux` is available there to copy) with one added conjunct: the base point of the
resulting space is the image of the old one, `χ y₀ = y₀'`.  If `Y` is path connected with finitely
generated `π₁`, `φ : Y → X` is based and injective on `π₁`, `π_i(Y) = 0` for `2 ≤ i ≤ k`, and
`π_i(X) = 0` for `k+1 ≤ i ≤ k+n`, then `φ` factors as `ψ ∘ χ` through a path connected space `Y'`
with `χ y₀ = y₀'`, finitely generated `π₁`, injective `π₁(ψ)`, and `π_i(Y') = 0` for `2 ≤ i ≤ k+n`.

PROOF HINT.  Copy the induction of `Work.RatHurewicz.killTowerFgAux`
(`Submission/Work/RatHurewicz/killTowerFg.lean`) and strengthen *both* the auxiliary statement and
the final result by the conjunct `χ y₀ = y₀'`.  In the `zero` case `χ = ContinuousMap.id Y` and
`y₀' = y₀`, so the conjunct is `rfl`; in the `succ` case the new base point is *by definition*
`y₁ := χ₁ y₀`, so with `ih` giving `χ' y₁ = y₀'` one gets `(χ'.comp χ₁) y₀ = y₀'` by
`rw [ContinuousMap.comp_apply, ‹χ' y₁ = y₀'›]`.  Nothing else changes. -/
theorem killTowerFgBased (n k : ℕ) (hk : 1 ≤ k)
    {Y X : Type} [TopologicalSpace Y] [TopologicalSpace X] (y₀ : Y) (φ : C(Y, X))
    [PathConnectedSpace Y]
    (hX : ∀ i : ℕ, k + 1 ≤ i → i ≤ k + n → ∀ x : X, Subsingleton (HomotopyGroup (Fin i) X x))
    (hfg : Group.FG (HomotopyGroup (Fin 1) Y y₀))
    (hinj : Function.Injective (Work.Serre.piMapN φ 1 y₀))
    (hlo : ∀ j : ℕ, 2 ≤ j → j ≤ k → Subsingleton (HomotopyGroup (Fin j) Y y₀)) :
    ∃ (Y' : Type) (_ : TopologicalSpace Y') (y₀' : Y') (ψ : C(Y', X)) (χ : C(Y, Y')),
      ψ.comp χ = φ ∧ χ y₀ = y₀' ∧ PathConnectedSpace Y' ∧
      Group.FG (HomotopyGroup (Fin 1) Y' y₀') ∧
      Function.Injective (Work.Serre.piMapN ψ 1 y₀') ∧
      (∀ j : ℕ, 2 ≤ j → j ≤ k + n → Subsingleton (HomotopyGroup (Fin j) Y' y₀')) :=
  killTowerFgBasedAux n k hk Y y₀ X φ hX hfg hinj hlo

end Work.Rat.RankOneC1
