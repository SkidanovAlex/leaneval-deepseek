import Mathlib
import Submission.NK.LocalCFT.Brauer.Basic
import Submission.NK.LocalCFT.Brauer.localH2Nonvanishing_iff_surviving
import Submission.NK.LocalCFT.Brauer.Transport
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

universe u

namespace NK.LocalCFT.Brauer

theorem exists_ne_zero_H2Profinite_of_mulEquiv {p : ℕ} {K K' κ κ' : Type u} [Field K]
    [Field K'] [Algebra K K'] [IsSepClosure K K'] [Field κ] [Field κ'] [Algebra κ κ']
    [IsSepClosure κ κ'] (H : Subgroup Gal(K'/K)) (hH : IsClosed (H : Set Gal(K'/K)))
    (e : ↥H ≃* Gal(κ'/κ))
    (hopenH : ∀ U : Subgroup ↥H, U.FiniteIndex → IsOpen (U : Set ↥H))
    (hopenκ : ∀ U : Subgroup Gal(κ'/κ), U.FiniteIndex → IsOpen (U : Set Gal(κ'/κ)))
    (hne : NK.LocalCFT.LocalH2Nonvanishing p κ κ') :
    ∃ y : NK.BrauerHasse.H2Profinite (K := K) (K' := K') p H, y ≠ 0 := by
  classical
  obtain ⟨L₀, a₀, ha₀, hsurv⟩ :=
    (NK.LocalCFT.Brauer.localH2Nonvanishing_iff_surviving (p := p)).mp hne
  let N₀ : Subgroup ↥H := L₀.fixingSubgroup.comap (e : ↥H →* Gal(κ'/κ))
  have hN₀fin : N₀.FiniteIndex := by
    rw [Subgroup.finiteIndex_iff]
    rw [Subgroup.index_comap_of_surjective L₀.fixingSubgroup
      (f := (e : ↥H →* Gal(κ'/κ))) e.surjective]
    exact (fixingSubgroup_finiteIndex L₀).index_ne_zero
  have hN₀open : IsOpen (N₀ : Set ↥H) := hopenH N₀ hN₀fin
  obtain ⟨M₀, hM₀⟩ := exists_fixingSubgroup_subgroupOf_le_of_isOpen (K := K) (K' := K')
    (H := H) hN₀open
  have hL₀M₀ : L₀ ≤ transportLevelField H e hopenκ M₀ :=
    le_transportLevelField H e hopenκ hM₀
  let A : NK.BrauerHasse.LevelH2 p (⊤ : Subgroup Gal(κ'/κ))
      (transportLevelField H e hopenκ M₀) :=
    (NK.BrauerHasse.levelMap p (U := (⊤ : Subgroup Gal(κ'/κ))) hL₀M₀) a₀
  let b : NK.BrauerHasse.LevelH2 p H M₀ :=
    (NK.BrauerHasse.H2.map (p := p) (levelMulEquiv H e hopenκ M₀).toMonoidHom).hom A
  have hb : b ≠ 0 := H2_map_ne_zero_of_mulEquiv (levelMulEquiv H e hopenκ M₀) A
    (hsurv (transportLevelField H e hopenκ M₀) hL₀M₀)
  refine ⟨NK.BrauerHasse.H2Profinite.ofLevel M₀ b, ?_⟩
  intro hy
  have hy' : NK.BrauerHasse.H2Profinite.ofLevel M₀ b
      = NK.BrauerHasse.H2Profinite.ofLevel (⊥ : FiniteGaloisIntermediateField K K')
          (0 : NK.BrauerHasse.LevelH2 p H ⊥) :=
    hy.trans (NK.BrauerHasse.ofLevel_zero _).symm
  obtain ⟨M₁, h₁, h₂, heq⟩ :=
    (NK.BrauerHasse.ofLevel_eq_iff (p := p) (U := H) b
      (0 : NK.BrauerHasse.LevelH2 p H ⊥)).mp hy'
  have hz : (NK.BrauerHasse.levelMap p (U := H) h₁) b = 0 := by
    rw [heq]
    simp
  have hM₁ : M₁.fixingSubgroup.subgroupOf H ≤
      L₀.fixingSubgroup.comap (e : ↥H →* Gal(κ'/κ)) :=
    le_trans (NK.BrauerHasse.fixingSubgroup_subgroupOf_le h₁ H) hM₀
  have hL₀M₁ : L₀ ≤ transportLevelField H e hopenκ M₁ := le_transportLevelField H e hopenκ hM₁
  have key := levelMap_levelMulEquiv (p := p) H e hopenκ h₁ hL₀M₀ hL₀M₁ a₀
  have hne' : (NK.BrauerHasse.levelMap p (U := H) h₁) b ≠ 0 := by
    rw [key]
    exact H2_map_ne_zero_of_mulEquiv (levelMulEquiv H e hopenκ M₁) _
      (hsurv (transportLevelField H e hopenκ M₁) hL₀M₁)
  exact hne' hz


end NK.LocalCFT.Brauer
