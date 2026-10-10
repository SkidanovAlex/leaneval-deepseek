import Mathlib.GroupTheory.Frattini
import Mathlib.Order.CompletePartialOrder
import Mathlib.FieldTheory.Normal.Defs
import Submission.Work.GroupTheory.isElementaryAbelian_of_minimal_normal
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.Fitting

open scoped Classical
open Subgroup

variable {G : Type*} [Group G]

/-- The **Fitting subgroup** of a group: the supremum of all normal nilpotent subgroups.  For a
finite group this is the largest normal nilpotent subgroup (see `fitting_nilpotent` in
`Submission/Work/Fitting/Join.lean`). -/
noncomputable def fitting (G : Type*) [Group G] : Subgroup G :=
  sSup {N : Subgroup G | N.Normal ∧ Group.IsNilpotent N}

theorem fitting_def : fitting G = sSup {N : Subgroup G | N.Normal ∧ Group.IsNilpotent N} := rfl

/-- Every normal nilpotent subgroup is contained in the Fitting subgroup. -/
theorem le_fitting {N : Subgroup G} (hN : N.Normal) (hnil : Group.IsNilpotent N) :
    N ≤ fitting G :=
  le_sSup ⟨hN, hnil⟩

/-- Universal property of the Fitting subgroup: it is the largest normal nilpotent subgroup. -/
theorem fitting_le_iff {H : Subgroup G} :
    fitting G ≤ H ↔ ∀ N : Subgroup G, N.Normal → Group.IsNilpotent N → N ≤ H :=
  ⟨fun h N hN hnil => (le_sSup (show N ∈ {N : Subgroup G | N.Normal ∧ Group.IsNilpotent N}
      from ⟨hN, hnil⟩)).trans h,
    fun h => sSup_le fun N hN => h N hN.1 hN.2⟩

theorem fitting_normal : (fitting G).Normal :=
  Subgroup.sSup_normal _ fun _ hN => hN.1

/-- The Fitting subgroup is characteristic. -/
theorem fitting_characteristic : (fitting G).Characteristic := by
  rw [Subgroup.characteristic_iff_map_eq]
  intro φ
  refine le_antisymm ?_ ?_
  · -- `F(G).map φ ≤ F(G)`: the image of a normal nilpotent subgroup is normal nilpotent
    rw [Subgroup.map_le_iff_le_comap]
    refine (fitting_le_iff (G := G) (H := (fitting G).comap φ.toMonoidHom)).mpr fun N hN hnil => ?_
    exact (Subgroup.map_le_iff_le_comap (f := φ.toMonoidHom)).mp
      (le_fitting (hN.map φ.toMonoidHom φ.surjective)
        ((Group.isNilpotent_congr (Subgroup.equivMapOfInjective N φ.toMonoidHom
          φ.injective)).mp hnil))
  · -- `F(G) ≤ F(G).map φ`: it suffices that `φ⁻¹` of a normal nilpotent subgroup is one
    refine (fitting_le_iff (G := G) (H := (fitting G).map φ.toMonoidHom)).mpr fun N hN hnil => ?_
    have hmapn : (N.map φ.symm.toMonoidHom).Normal :=
      hN.map φ.symm.toMonoidHom φ.symm.surjective
    have hmapn' : Group.IsNilpotent ↥(N.map φ.symm.toMonoidHom) :=
      (Group.isNilpotent_congr (Subgroup.equivMapOfInjective N φ.symm.toMonoidHom
        φ.symm.injective)).mp hnil
    have hle : (N.map φ.symm.toMonoidHom) ≤ fitting G := le_fitting hmapn hmapn'
    intro x hx
    rw [Subgroup.mem_map_equiv]
    exact hle (Subgroup.mem_map_of_mem φ.symm.toMonoidHom hx)

instance fittingCharacteristic : (fitting G).Characteristic := fitting_characteristic

/-- A nilpotent group is its own Fitting subgroup. -/
theorem fitting_eq_top (h : Group.IsNilpotent G) : fitting G = ⊤ :=
  le_antisymm le_top <| le_fitting (N := ⊤) inferInstance
    ((Group.isNilpotent_congr Subgroup.topEquiv).mpr h)

/-- The Frattini subgroup is contained in the Fitting subgroup: for a finite group the Frattini
subgroup is nilpotent. -/
theorem frattini_le_fitting [Finite G] : frattini G ≤ fitting G :=
  le_fitting (inferInstance : (frattini G).Normal) frattini_nilpotent

/-- The Frattini subgroup of a nontrivial finite group is a proper subgroup. -/
theorem frattini_ne_top [Finite G] (hG : ¬ Subsingleton G) : frattini G ≠ ⊤ := by
  rcases IsCoatomic.eq_top_or_exists_le_coatom (⊥ : Subgroup G) with h | ⟨K, hK, -⟩
  · exfalso
    refine hG ⟨fun x y => ?_⟩
    have hx : x = 1 := Subgroup.mem_bot.mp (h ▸ (Subgroup.mem_top x : x ∈ (⊤ : Subgroup G)))
    have hy : y = 1 := Subgroup.mem_bot.mp (h ▸ (Subgroup.mem_top y : y ∈ (⊤ : Subgroup G)))
    rw [hx, hy]
  · exact fun htop => hK.1 (top_le_iff.mp (htop ▸ frattini_le_coatom hK))

/-- A commutative group is nilpotent (stated for `IsMulCommutative`, which is what
`isElementaryAbelian_of_minimal_normal` produces). -/
theorem isNilpotent_of_isMulCommutative {A : Type*} [Group A] (h : IsMulCommutative A) :
    Group.IsNilpotent A :=
  letI : CommGroup A := { mul_comm := h.is_comm.comm }
  inferInstance

/-- Every nontrivial finite group has a nontrivial minimal normal subgroup. -/
theorem exists_minimal_normal (G : Type*) [Group G] [Finite G] (hsub : ¬ Subsingleton G) :
    ∃ A : Subgroup G, A.Normal ∧ A ≠ ⊥ ∧
      ∀ B : Subgroup G, B.Normal → B ≤ A → B ≠ ⊥ → B = A := by
  classical
  have htop : (⊤ : Subgroup G) ≠ ⊥ := by
    intro h
    refine hsub ⟨fun x y => ?_⟩
    have hx : x = 1 := Subgroup.mem_bot.mp (h ▸ (Subgroup.mem_top x : x ∈ (⊤ : Subgroup G)))
    have hy : y = 1 := Subgroup.mem_bot.mp (h ▸ (Subgroup.mem_top y : y ∈ (⊤ : Subgroup G)))
    rw [hx, hy]
  have hex : ∃ n : ℕ, ∃ A : Subgroup G, A.Normal ∧ A ≠ ⊥ ∧ Nat.card A = n :=
    ⟨Nat.card (⊤ : Subgroup G), ⊤, inferInstance, htop, rfl⟩
  obtain ⟨A, hAn, hAne, hAcard⟩ := Nat.find_spec hex
  refine ⟨A, hAn, hAne, ?_⟩
  intro B hBn hBA hBne
  have hcardB : Nat.find hex ≤ Nat.card B := Nat.find_min' hex ⟨B, hBn, hBne, rfl⟩
  have hcardA : Nat.card A ≤ Nat.card B := by rw [hAcard]; exact hcardB
  exact Subgroup.eq_of_le_of_card_ge hBA hcardA

/-- The Fitting subgroup of a nontrivial finite solvable group is nontrivial. -/
theorem fitting_ne_bot [Finite G] [Group.IsSolvable G] (h : ¬ Subsingleton G) :
    fitting G ≠ ⊥ := by
  obtain ⟨A, hAn, hAne, hAmin⟩ := exists_minimal_normal G h
  obtain ⟨p, hp, hcomm, -⟩ :=
    Work.GroupTheory.isElementaryAbelian_of_minimal_normal G A hAne hAmin
  have hle : A ≤ fitting G := le_fitting hAn (isNilpotent_of_isMulCommutative hcomm)
  intro hbot
  exact hAne (le_bot_iff.mp (hbot ▸ hle))

end Work.Fitting
