import Mathlib
import Submission.Work.Serre.Defs
import Submission.Work.RatHurewicz.killHighFinite
import Submission.Work.RatHurewicz.killKernelFinite

set_option linter.unusedVariables false

namespace Work.RatHurewicz

open scoped Topology Topology.Homotopy unitInterval

noncomputable section

/-!
HINT (do not change the statement).  This is the `Group.FG` version of the existing, sorry-free
`Work.RatHurewicz.killTowerAux` / `Work.RatHurewicz.killHighFinite`
(`Submission/Work/RatHurewicz/killHighFinite.lean`) — copy that induction and change:
* `Finite (HomotopyGroup (Fin 1) · ·)` ↦ `Group.FG (HomotopyGroup (Fin 1) · ·)`, using
  `Group.fg_of_surjective` where the original uses `Finite.of_surjective`;
* drop the (there unused) hypothesis `∀ x : X, Subsingleton (HomotopyGroup (Fin 0) X x)`;
* the π₀ bookkeeping `Subsingleton (HomotopyGroup (Fin 0) · ·)` becomes `[PathConnectedSpace Y]`
  in and `PathConnectedSpace Y'` out: `Work.Serre.CWModel.pathConnectedSpace_attachCells` gives
  path-connectedness of the attachment, and
  `Work.RatHurewicz.pathConnectedSpace_of_subsingleton_pi_zero` (with
  `HomotopyGroup.pi0EquivZerothHomotopy`) converts between `Subsingleton π₀` and
  `PathConnectedSpace`.
Useful existing pieces (all sorry-free): `Work.StemsB.killFamily_extend`,
`Work.RatHurewicz.surjective_piMap_attachIncl_of_le`,
`Work.RatHurewicz.injective_piMap_of_comp_eq`,
`Work.RatHurewicz.killFamily_subsingleton`, `Work.Serre.subsingleton_homotopyGroup_of_joined`.
Note `Work.Serre.piMapN f 1 x` and `Work.StemsB.πmap f 0 x` are definitionally equal.
-/

/-- **The killing tower, finitely generated version** (auxiliary form, inducting on the height `n`
with the bottom degree `k` universally quantified so that the recursive call may use `k + 1`). -/
private theorem killTowerFgAux (n : ℕ) :
    ∀ (k : ℕ), 1 ≤ k →
    ∀ (Y : Type) [TopologicalSpace Y] (y₀ : Y) (X : Type) [TopologicalSpace X] (φ : C(Y, X))
      [PathConnectedSpace Y],
      (∀ i : ℕ, k + 1 ≤ i → i ≤ k + n → ∀ x : X, Subsingleton (HomotopyGroup (Fin i) X x)) →
      Group.FG (HomotopyGroup (Fin 1) Y y₀) →
      Function.Injective (Work.Serre.piMapN φ 1 y₀) →
      (∀ j : ℕ, 2 ≤ j → j ≤ k → Subsingleton (HomotopyGroup (Fin j) Y y₀)) →
      ∃ (Y' : Type) (_ : TopologicalSpace Y') (y₀' : Y') (ψ : C(Y', X)) (χ : C(Y, Y')),
        ψ.comp χ = φ ∧ PathConnectedSpace Y' ∧
        Group.FG (HomotopyGroup (Fin 1) Y' y₀') ∧
        Function.Injective (Work.Serre.piMapN ψ 1 y₀') ∧
        (∀ j : ℕ, 2 ≤ j → j ≤ k + n → Subsingleton (HomotopyGroup (Fin j) Y' y₀')) := by
  induction n with
  | zero =>
    intro k hk Y _ y₀ X _ φ _ hX hfg hinj hlo
    exact ⟨Y, inferInstance, y₀, φ, ContinuousMap.id Y, by ext y; rfl, inferInstance, hfg, hinj,
      fun j hj2 hj => hlo j hj2 (by omega)⟩
  | succ m ih =>
    intro k hk Y _ y₀ X _ φ _ hX hfg hinj hlo
    let ι := HomotopyGroup (Fin (k + 1)) Y y₀
    let f : ι → C(cellSphere k, Y) := killFamily k Y y₀
    let Y₁ : Type := attachCells k Y ι f
    letI : TopologicalSpace Y₁ := inferInstance
    let χ₁ : C(Y, Y₁) := attachIncl k Y ι f
    let y₁ : Y₁ := χ₁ y₀
    have hXstep : Subsingleton (HomotopyGroup (Fin (k + 1)) X (φ y₀)) :=
      hX (k + 1) le_rfl (by omega) (φ y₀)
    obtain ⟨ψ₁, hψ₁⟩ := Work.StemsB.killFamily_extend k Y y₀ X φ hXstep
    have hsurj₁ : Function.Surjective (Work.StemsB.πmap χ₁ 0 y₀) :=
      surjective_piMap_attachIncl_of_le k Y ι f y₀ 0 (by omega)
    haveI hpc₁ : PathConnectedSpace Y₁ :=
      Work.Serre.CWModel.pathConnectedSpace_attachCells k Y ι f
    have hfg₁ : Group.FG (HomotopyGroup (Fin 1) Y₁ y₁) := by
      haveI := hfg
      exact Group.fg_of_surjective (f := Work.StemsB.πmap χ₁ 0 y₀) hsurj₁
    have hinj₁ : Function.Injective (Work.Serre.piMapN ψ₁ 1 y₁) :=
      injective_piMap_of_comp_eq ψ₁ χ₁ y₀ φ hψ₁ hsurj₁ hinj
    have hlo₁ : ∀ j : ℕ, 2 ≤ j → j ≤ k + 1 → Subsingleton (HomotopyGroup (Fin j) Y₁ y₁) := by
      intro j hj2 hjk1
      rcases eq_or_lt_of_le hjk1 with heq | hlt
      · subst heq
        exact killFamily_subsingleton k Y y₀
      · have hjk : j ≤ k := by omega
        have hb := surjective_piMap_attachIncl_of_le k Y ι f y₀ (j - 1) (by omega)
        have hsi : j - 1 + 1 = j := Nat.sub_add_cancel (by omega)
        have h1 : Subsingleton (HomotopyGroup (Fin (j - 1 + 1)) Y y₀) := by
          simpa only [hsi] using hlo j hj2 hjk
        simpa only [hsi] using
          Work.StemsB.subsingleton_of_surjective (Work.StemsB.πmap χ₁ (j - 1) y₀) hb h1
    have hX' : ∀ i : ℕ, (k + 1) + 1 ≤ i → i ≤ (k + 1) + m →
        ∀ x : X, Subsingleton (HomotopyGroup (Fin i) X x) :=
      fun i hi hle => hX i (by omega) (by omega)
    obtain ⟨Y', instY', y₀', ψ', χ', hχ', hpc', hfg', hinj', hkilled'⟩ :=
      ih (k + 1) (by omega) Y₁ y₁ X ψ₁ hX' hfg₁ hinj₁ hlo₁
    refine ⟨Y', instY', y₀', ψ', χ'.comp χ₁, ?_, hpc', hfg', hinj', ?_⟩
    · rw [← ContinuousMap.comp_assoc, hχ', hψ₁]
    · intro j hj2 hle
      exact hkilled' j hj2 (by omega)

theorem killTowerFg (n k : ℕ) (hk : 1 ≤ k)
    (Y : Type) [TopologicalSpace Y] (y₀ : Y) (X : Type) [TopologicalSpace X] (φ : C(Y, X))
    [PathConnectedSpace Y]
    (hX : ∀ i : ℕ, k + 1 ≤ i → i ≤ k + n → ∀ x : X, Subsingleton (HomotopyGroup (Fin i) X x))
    (hfg : Group.FG (HomotopyGroup (Fin 1) Y y₀))
    (hinj : Function.Injective (Work.Serre.piMapN φ 1 y₀))
    (hlo : ∀ j : ℕ, 2 ≤ j → j ≤ k → Subsingleton (HomotopyGroup (Fin j) Y y₀)) :
    ∃ (Y' : Type) (_ : TopologicalSpace Y') (y₀' : Y') (ψ : C(Y', X)) (χ : C(Y, Y')),
      ψ.comp χ = φ ∧ PathConnectedSpace Y' ∧
      Group.FG (HomotopyGroup (Fin 1) Y' y₀') ∧
      Function.Injective (Work.Serre.piMapN ψ 1 y₀') ∧
      (∀ j : ℕ, 2 ≤ j → j ≤ k + n → Subsingleton (HomotopyGroup (Fin j) Y' y₀')) :=
  killTowerFgAux n k hk Y y₀ X φ hX hfg hinj hlo

end

end Work.RatHurewicz
