import Mathlib
import Submission.Work.CORE2B.Basic
import Submission.Work.CORE2B.API
import Submission.Work.CORE2B.oddCore_odd
import Submission.Work.CORE2B.L27cf_helpers

/-!
# `F(U) ≠ 1`, `N_G(F(U)) = Ĥ` and `F(U) ≤ F(Ĥ)`  (Bender 1981, proof of Theorem 2.10)

With `U = O(H) = O(C_G(t))` and `Ĥ` a maximal subgroup containing `H = C_G(t)`, Bender uses
`X := F(U)` as the witness subgroup of `F(U)` in case (2) of Theorem 2.10 (p. 222): indeed

* `F(U) ≠ 1`: `U` has odd order (it is the odd core of `H`), hence is solvable by
  Feit–Thompson, and a nontrivial finite solvable group has nontrivial Fitting subgroup;
* `N_G(F(U)) = Ĥ`: Theorem 2.6 gives `U = O(Ĥ) ◁ Ĥ`, and `F(U)` is characteristic in `U`, so
  `Ĥ ≤ N_G(F(U))`; since `F(U) ≠ 1` and `F(U) ≤ U ≤ Ĥ ≠ ⊤`, simplicity of `G` forbids
  `N_G(F(U)) = ⊤`, and `Ĥ` is coatomic;
* `F(U) ≤ F(Ĥ)`: this is `F(K) ≤ F(X)` for `K ◁ X` applied to `U ◁ Ĥ`.

The general pieces (`F(K)` is the greatest normal nilpotent subgroup, `F(K)` is characteristic in
`K`, `X ≤ N_G(K) → X ≤ N_G(F(K))`, `K ◁ X → F(K) ≤ F(X)`, `N_G(Z) = K` for a nontrivial
`Z ≤ K` with `K` coatomic) are proved here; the bridge
`Work.GW2.fitting = OddOrder.Isaacs.Ch01.fitting` (hence Fitting's theorem for this custom
Fitting subgroup) is `L27cf_fitting_eq_isaacsFitting` / `L27cf_isNilpotent_fitting`.

The statement `X ≤ N_G(K) → X ≤ N_G(F(K))` is also available as
`Work.CORE2B.le_normalizer_fittingIn_of_le_normalizer` (a sibling module); it is duplicated here
under the `_local` name only so that this module does not import
`Submission.Work.CORE2B.L27_su_not_le_h22_proved` (and hence not the in-flux
`L29_contra_proved`).
-/

open scoped MatrixGroups

namespace Work.CORE2B

open Subgroup

set_option linter.unusedVariables false
set_option linter.style.haveILetI false

/-! ## 1. The Fitting subgroup is the greatest normal nilpotent subgroup -/

/-- A normal nilpotent subgroup of `X` lies in `F(X)`. -/
theorem le_fitting_of_normal_isNilpotent_local {X : Type} [Group X] {N : Subgroup X}
    [N.Normal] [Group.IsNilpotent ↥N] : N ≤ Work.GW2.fitting X := by
  rw [Work.GW2.fitting]
  exact Subgroup.normal_le_normalCore.mpr (le_sSup ⟨inferInstance, inferInstance⟩)

/-- The Fitting subgroup is characteristic. -/
theorem fitting_characteristic_local {X : Type} [Group X] [Finite X] :
    (Work.GW2.fitting X).Characteristic := by
  rw [L27cf_fitting_eq_isaacsFitting]
  exact OddOrder.Isaacs.Ch01.fitting.characteristic X

/-- **The normalizer of a subgroup normalizes its Fitting subgroup**: `C ≤ N_G(K)` implies
`C ≤ N_G(F(K))`, since `F(K)` is characteristic in `K`. -/
theorem le_normalizer_fittingIn_of_le_normalizer_local {G : Type} [Group G] [Finite G]
    {K C : Subgroup G} (h : C ≤ Subgroup.normalizer (K : Set G)) :
    C ≤ Subgroup.normalizer ((Work.GW2.fittingIn K : Subgroup G) : Set G) := by
  have hchar : (Work.GW2.fitting ↥K).Characteristic := fitting_characteristic_local
  intro c hc
  have hnormK : c ∈ Subgroup.normalizer (K : Set G) := h hc
  have hmapK : K.map (MulAut.conj c).toMonoidHom = K :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp hnormK
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  change ((Work.GW2.fitting ↥K).map K.subtype).map (MulAut.conj c).toMonoidHom
      = (Work.GW2.fitting ↥K).map K.subtype
  -- conjugation by `c ∈ N_G(K)` restricts to an automorphism of `↥K`
  let σ : ↥K ≃* ↥K :=
    (Subgroup.equivMapOfInjective K (MulAut.conj c).toMonoidHom (MulAut.conj c).injective).trans
      (MulEquiv.subgroupCongr hmapK)
  have hσ : (Work.GW2.fitting ↥K).map σ.toMonoidHom = Work.GW2.fitting ↥K :=
    (Subgroup.characteristic_iff_map_eq.mp hchar) σ
  have hcomp : (MulAut.conj c).toMonoidHom.comp K.subtype = K.subtype.comp σ.toMonoidHom := by
    ext x
    rfl
  calc ((Work.GW2.fitting ↥K).map K.subtype).map (MulAut.conj c).toMonoidHom
      = (Work.GW2.fitting ↥K).map ((MulAut.conj c).toMonoidHom.comp K.subtype) :=
        Subgroup.map_map _ _ _
    _ = (Work.GW2.fitting ↥K).map (K.subtype.comp σ.toMonoidHom) := by rw [hcomp]
    _ = ((Work.GW2.fitting ↥K).map σ.toMonoidHom).map K.subtype :=
        (Subgroup.map_map _ _ _).symm
    _ = (Work.GW2.fitting ↥K).map K.subtype := by rw [hσ]

/-- A normal nilpotent subgroup `N ≤ X` whose image in `X` is normal in `↥X` lies in `F(X)`. -/
theorem le_fittingIn_of_le_normalizer_of_isNilpotent_local {G : Type} [Group G]
    {N X : Subgroup G} (hNX : N ≤ X) [Group.IsNilpotent ↥N]
    (h : X ≤ Subgroup.normalizer (N : Set G)) : N ≤ Work.GW2.fittingIn X := by
  haveI hNorm : (N.subgroupOf X).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hNX).mpr h
  haveI hNil : Group.IsNilpotent ↥(N.subgroupOf X) :=
    (Group.isNilpotent_congr (Subgroup.subgroupOfEquivOfLe hNX)).mpr inferInstance
  calc N = (N.subgroupOf X).map X.subtype := (Subgroup.map_subgroupOf_eq_of_le hNX).symm
    _ ≤ (Work.GW2.fitting ↥X).map X.subtype :=
        Subgroup.map_mono (le_fitting_of_normal_isNilpotent_local (X := ↥X) (N := N.subgroupOf X))
    _ = Work.GW2.fittingIn X := rfl

/-- **`F(K) ≤ F(X)` for `K ◁ X`**: `F(K)` is normal (characteristic in `K ◁ X`) and nilpotent. -/
theorem fittingIn_le_fittingIn_of_normal_local {G : Type} [Group G] [Finite G]
    {K X : Subgroup G} (hKX : K ≤ X) (hKn : (K.subgroupOf X).Normal) :
    Work.GW2.fittingIn K ≤ Work.GW2.fittingIn X := by
  have hXnormK : X ≤ Subgroup.normalizer (K : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hKX).mp hKn
  have hXnormF : X ≤ Subgroup.normalizer ((Work.GW2.fittingIn K : Subgroup G) : Set G) :=
    le_normalizer_fittingIn_of_le_normalizer_local (C := X) (K := K) hXnormK
  haveI hNil : Group.IsNilpotent ↥(Work.GW2.fittingIn K) := by
    haveI h1 : Group.IsNilpotent ↥(Work.GW2.fitting ↥K) := L27cf_isNilpotent_fitting (G := ↥K)
    exact (Group.isNilpotent_congr (Subgroup.equivMapOfInjective (Work.GW2.fitting ↥K)
      K.subtype K.subtype_injective)).mp h1
  exact le_fittingIn_of_le_normalizer_of_isNilpotent_local
    ((Subgroup.map_subtype_le (Work.GW2.fitting ↥K)).trans hKX) hXnormF

/-- For a coatomic `K` of a finite simple group, a nontrivial `Z ≤ K` normalised by `K` has
`N_G(Z) = K`: the normalizer contains the coatom `K`, and `N_G(Z) = ⊤` would make `Z` a
nontrivial proper normal subgroup. -/
theorem normalizer_eq_of_coatom_local {G : Type} [Group G] [Finite G] [IsSimpleGroup G]
    {K Z : Subgroup G} (hK : IsCoatom K) (hZK : Z ≤ K) (hZ : Z ≠ ⊥)
    (hKnorm : K ≤ Subgroup.normalizer (Z : Set G)) :
    Subgroup.normalizer (Z : Set G) = K := by
  rcases lt_or_eq_of_le hKnorm with hlt | heq
  · have htop : Subgroup.normalizer (Z : Set G) = ⊤ := hK.lt_iff.mp hlt
    haveI hZn : Z.Normal := Subgroup.normalizer_eq_top_iff.mp htop
    rcases Subgroup.Normal.eq_bot_or_eq_top Z with hbot | htopZ
    · exact absurd hbot hZ
    · exact absurd (top_le_iff.mp (htopZ ▸ hZK)) hK.ne_top
  · exact heq.symm

/-- A nontrivial finite solvable group has nontrivial Fitting subgroup. -/
theorem fitting_ne_bot_of_isSolvable_nontrivial_local {X : Type} [Group X] [Finite X]
    [Nontrivial X] [Group.IsSolvable X] : Work.GW2.fitting X ≠ ⊥ := by
  rw [L27cf_fitting_eq_isaacsFitting]
  exact OddOrder.Isaacs.Ch01.fitting_ne_bot_of_isSolvable_nontrivial X

/-! ## 2. The main statement -/

/-- Bender 1981, proof of Theorem 2.10 (p. 222): with `U = O(C_G(t)) ≠ 1`,
`F(U) ≠ 1`, `N_G(F(U)) = Ĥ` and `F(U) ≤ F(Ĥ)`. -/
theorem fittingIn_U_normalizer (h26 : Work.GW2.Thm26Prop) (G : Type) [Group G] [Finite G]
    (hFT : Work.GW2.FeitThompsonProp) (hCtx : Work.GW2.BenderCtx G) (B : Work.GW2.BenderSetup G)
    (hU : B.U ≠ ⊥) :
    Work.GW2.fittingIn B.U ≠ ⊥ ∧
      Subgroup.normalizer (Work.GW2.fittingIn B.U : Set G) = B.Hhat ∧
      Work.GW2.fittingIn B.U ≤ Work.GW2.fittingIn B.Hhat := by
  have h26B := h26 G hFT hCtx B
  -- Theorem 2.6: `U = O(Ĥ)`
  have hUeq : Work.GW2.oddCoreIn B.Hhat = B.U := h26B.1
  have hUleHhat : B.U ≤ B.Hhat := hUeq ▸ (Work.CORE2B.in_le_self B.Hhat 2 B.pi).1
  -- ## Part 1: `U` is odd, hence solvable, hence `F(U) ≠ 1`
  have hoddU : Odd (Nat.card ↥B.U) := by
    rw [Work.GW2.BenderSetup.U, Work.GW2.oddCoreIn,
      Subgroup.card_map_of_injective B.H.subtype_injective]
    exact oddCore_odd (G := ↥B.H)
  haveI : Group.IsSolvable ↥B.U := hFT ↥B.U hoddU
  haveI : Nontrivial ↥B.U := (Subgroup.nontrivial_iff_ne_bot B.U).mpr hU
  have hUfit : Work.GW2.fitting ↥B.U ≠ ⊥ := fitting_ne_bot_of_isSolvable_nontrivial_local
  have hFne : Work.GW2.fittingIn B.U ≠ ⊥ := by
    intro h
    refine hUfit (Subgroup.map_injective B.U.subtype_injective ?_)
    rw [Subgroup.map_bot]
    exact h
  -- ## Part 2: `N_G(F(U)) = Ĥ`
  have hFUleU : Work.GW2.fittingIn B.U ≤ B.U := (Work.CORE2B.in_le_self B.U 2 B.pi).2.2.1
  have hFUleHhat : Work.GW2.fittingIn B.U ≤ B.Hhat := hFUleU.trans hUleHhat
  -- `Ĥ ≤ N_G(U)` because `U = O(Ĥ) ◁ Ĥ`, and `N_G(U) ≤ N_G(F(U))` since `F(U)` is
  -- characteristic in `U`.
  have hUleNorm : B.Hhat ≤ Subgroup.normalizer (B.U : Set G) := by
    rw [← hUeq]
    exact le_normalizer_map_subtype_local B.Hhat (Work.GW2.oddCore ↥B.Hhat)
      (Work.GW2.oddCore_normal ↥B.Hhat)
  have hle_fit : B.Hhat ≤ Subgroup.normalizer ((Work.GW2.fittingIn B.U : Subgroup G) : Set G) :=
    le_normalizer_fittingIn_of_le_normalizer_local hUleNorm
  have hEq : Subgroup.normalizer (Work.GW2.fittingIn B.U : Set G) = B.Hhat := by
    haveI : IsSimpleGroup G := hCtx.simple
    exact normalizer_eq_of_coatom_local B.Hhat_coatom hFUleHhat hFne hle_fit
  -- ## Part 3: `F(U) ≤ F(Ĥ)`, from `U = O(Ĥ) ◁ Ĥ` and `F(K) ≤ F(X)` for `K ◁ X`
  have hUsub : (B.U.subgroupOf B.Hhat).Normal := by
    have hUsub_eq : B.U.subgroupOf B.Hhat = Work.GW2.oddCore ↥B.Hhat := by
      rw [hUeq.symm, Work.GW2.oddCoreIn, Subgroup.subgroupOf]
      exact Subgroup.comap_map_eq_self_of_injective B.Hhat.subtype_injective _
    exact hUsub_eq ▸ Work.GW2.oddCore_normal ↥B.Hhat
  exact ⟨hFne, hEq, fittingIn_le_fittingIn_of_normal_local hUleHhat hUsub⟩

end Work.CORE2B
