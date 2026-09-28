import Mathlib
import Submission.Work.Rat.RankOneEMDefs
import Submission.Work.Rat.U.FamModel
import Submission.Work.Rat.U.EM
import Submission.Work.RatHurewicz.isEMSpaceUpTo_pi_fin
import Submission.Work.Serre.C1SphOne
import Submission.Work.Serre.sphOneAspherical
import Submission.Work.Serre.baseStageFamMap
import Submission.Work.Serre.E3aModel
import Submission.Work.Serre.towerStepMap
import Submission.Work.Serre.RangeOne.rangeWhitehead
import Submission.Work.Serre.RangeOne.towerColim
import Submission.Work.Serre.bijective_piMapN_of_joined
import Submission.Work.Rat.RankOneC1.extendsAlongTowerB
import Submission.Work.Rat.RankOneC1.sphereProd_rangeModel

/-!
# The finitely generated rank-one case of `RankOneC1Ab`

`Work.Rat.c1Fg`: for a *finitely generated* rank-one coefficient group `ℤ × F` (`F` finite), a
range model `Z` of `K(ℤ × F, 1)` through degree `N` has vanishing rational homology in degrees
`1 < j ≤ N - 1`.

The proof compares `Z` with the model `L = S¹ × M` of `Work.Rat.RankOneC1.sphereProd_rangeModel`
(which is rationally a circle through degree `N + 4`): the model tower of `Z`
(`Work.Serre.E3aModel.towerB`) gives a space `Γ` mapping `π`-isomorphically to `Z` through degree
`N + 2`; the base stage map to `L` (`Work.Serre.baseStageFamMap`, from the two coefficient-group
isomorphisms) extends along the tower by `Work.Rat.RankOneC1.extendsAlongTowerB`, and the two
range-Whitehead comparisons (`Work.Serre.RangeOne.rangeWhitehead`) transport the vanishing of
`H_j(L;ℚ)` to `Z`.
-/

set_option linter.style.haveILetI false
set_option maxHeartbeats 800000

namespace Work.Rat

open CategoryTheory CategoryTheory.Limits

noncomputable section

theorem c1Fg {F : Type} [AddCommGroup F] [Fintype F] (N : ℕ)
    {Z : Type} [TopologicalSpace Z] (z₀ : Z)
    (hZ : Work.Serre.IsEMSpaceUpTo (ℤ × F) 1 (by norm_num) N Z z₀) :
    ∀ j : ℕ, 1 < j → j ≤ N - 1 → IsZero (Work.Serre.ratH (TopCat.of Z) j) := by
  classical
  intro j hj1 hjN
  haveI : Nonempty (Fin 1) := ⟨⟨0, by norm_num⟩⟩
  have hZ0 : Subsingleton (HomotopyGroup (Fin 0) Z z₀) := hZ.2 0 (by norm_num) (Or.inl (by norm_num))
  haveI hZpc : PathConnectedSpace Z :=
    Work.RatHurewicz.pathConnectedSpace_of_subsingleton_pi_zero z₀ hZ0
  set s₀ := Work.Serre.E3aModel.baseState Z z₀ with hs₀
  set sT := Work.Serre.E3aModel.towerB Z z₀ s₀ (N + 3) with hsT
  set g := (Work.Serre.E3aModel.towerB Z z₀ s₀ (N + 3)).g with hg
  have hgbij : ∀ i : ℕ, i ≤ N + 2 → ∀ x : sT.Y, Function.Bijective (Work.Serre.piMapN g i x) := by
    intro i hi x
    exact Work.Serre.E3aModel.towerB_piMapN_bijective Z z₀ s₀ (N + 2) i hi x
  obtain ⟨L, instL, l₀, hLmodel, hLzero⟩ :=
    Work.Rat.RankOneC1.sphereProd_rangeModel F (N + 4)
  letI : TopologicalSpace L := instL
  haveI hLpc : PathConnectedSpace L :=
    Work.RatHurewicz.pathConnectedSpace_of_subsingleton_pi_zero l₀
      (hLmodel.2 0 (by norm_num) (Or.inl (by norm_num)))
  have hLpi : ∀ i : ℕ, i ≠ 1 → (i < 1 ∨ i ≤ N + 4) →
      Subsingleton (HomotopyGroup (Fin i) L l₀) := fun i => hLmodel.2 i
  obtain ⟨eZ⟩ := hZ.1
  obtain ⟨eL⟩ := hLmodel.1
  obtain ⟨φ⟩ : Nonempty (HomotopyGroup (Fin 1) Z z₀ ≃* HomotopyGroup (Fin 1) L l₀) :=
    ⟨eZ.trans eL.symm⟩
  obtain ⟨gL₀, hgL₀base, hgL₀bij⟩ := Work.Serre.baseStageFamMap z₀ l₀ φ
  have hK : ∀ n : ℕ, n ≤ N + 2 → Subsingleton (HomotopyGroup (Fin (n + 2)) L l₀) := by
    intro n hn
    exact hLpi (n + 2) (by omega) (Or.inr (by omega))
  obtain ⟨h, hhbase, hhbij⟩ :=
    Work.Rat.RankOneC1.extendsAlongTowerB z₀ s₀ (N + 2) l₀ hK gL₀ hgL₀base hgL₀bij
  haveI hTpc : PathConnectedSpace sT.Y := sT.conn
  -- `π`-vanishing of `Γ` at the base point, in the range where `Z` is known
  have hΓ0 : ∀ i : ℕ, 2 ≤ i → i ≤ N →
      Subsingleton (HomotopyGroup (Fin i) sT.Y sT.y₀) := by
    intro i hi2 hi3
    have hZsub : Subsingleton (HomotopyGroup (Fin i) Z (g sT.y₀)) := by
      rw [sT.gbase]
      exact hZ.2 i (by omega) (Or.inr hi3)
    haveI := hZsub
    have hb := hgbij i (by omega) sT.y₀
    exact ⟨fun a b => hb.1 (Subsingleton.elim (Work.Serre.piMapN g i sT.y₀ a)
      (Work.Serre.piMapN g i sT.y₀ b))⟩
  have hΓpi : ∀ i : ℕ, 2 ≤ i → i ≤ N → ∀ x : sT.Y,
      Subsingleton (HomotopyGroup (Fin i) sT.Y x) := by
    intro i hi2 hi3 x
    exact Work.Serre.RangeOne.subsingleton_homotopyGroup_of_joined'
      (PathConnectedSpace.joined sT.y₀ x) i (by omega) (hΓ0 i hi2 hi3)
  have hLpiAll : ∀ i : ℕ, 2 ≤ i → i ≤ N → ∀ y : L,
      Subsingleton (HomotopyGroup (Fin i) L y) := by
    intro i hi2 hi3 y
    exact Work.Serre.RangeOne.subsingleton_homotopyGroup_of_joined'
      (PathConnectedSpace.joined l₀ y) i (by omega)
      (hLpi i (by omega) (Or.inr (by omega)))
  have hbij_all : ∀ i : ℕ, i ≤ N → ∀ x : sT.Y,
      Function.Bijective (Work.Serre.piMapN h i x) := by
    intro i hi3 x
    rcases Nat.eq_zero_or_pos i with h0 | hpos
    · subst h0
      have h1 : Subsingleton (HomotopyGroup (Fin 0) sT.Y x) :=
        (HomotopyGroup.pi0EquivZerothHomotopy (X := sT.Y) (x := x)).injective.subsingleton
      have h2 : Subsingleton (HomotopyGroup (Fin 0) L (h x)) :=
        (HomotopyGroup.pi0EquivZerothHomotopy (X := L) (x := h x)).injective.subsingleton
      exact ⟨fun a b _ => h1.elim a b, fun y => ⟨default, h2.elim _ _⟩⟩
    · rcases lt_or_eq_of_le (show 1 ≤ i by omega) with h1 | h1
      · have h3 : 2 ≤ i := h1
        have h2 : Subsingleton (HomotopyGroup (Fin i) sT.Y x) := hΓpi i h3 hi3 x
        have h4 : Subsingleton (HomotopyGroup (Fin i) L (h x)) := hLpiAll i h3 hi3 (h x)
        exact ⟨fun a b _ => h2.elim a b, fun y => ⟨default, h4.elim _ _⟩⟩
      · subst h1
        exact Work.Serre.bijective_piMapN_of_joined h
          (PathConnectedSpace.joined sT.y₀ x) 1 (by simpa using hhbij)
  have hGL : IsIso (Work.Serre.ratHomologyMap h j) :=
    Work.Serre.RangeOne.rangeWhitehead sT.Y L sT.y₀ h N hbij_all j (by omega)
  have hΓ0zero : IsZero (Work.Serre.ratH (TopCat.of sT.Y) j) :=
    IsZero.of_iso (hLzero j (by omega) (by omega) (by omega))
      (asIso (Work.Serre.ratHomologyMap h j))
  have hGZ : IsIso (Work.Serre.ratHomologyMap g j) :=
    Work.Serre.RangeOne.rangeWhitehead sT.Y Z sT.y₀ g (N + 2) hgbij j (by omega)
  exact IsZero.of_iso hΓ0zero (asIso (Work.Serre.ratHomologyMap g j)).symm


end

end Work.Rat
