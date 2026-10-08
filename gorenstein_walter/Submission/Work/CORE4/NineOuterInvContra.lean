import Mathlib
import Submission.Work.CORE4.Defs
import Submission.Work.CORE4.Defs10
import Submission.Work.CORE4.API
import Submission.Work.CORE4.Case2CountSetup
import Submission.Work.CORE4.Case2K1_ne_bot

namespace Work.CORE4

open Work.GW2 Subgroup

set_option linter.style.haveILetI false
set_option linter.unusedVariables false

/-- `N_G(X) ≤ N_G(C_G(X))`: an element conjugating the subgroup `X` to itself permutes `X`,
hence preserves the set of elements commuting with all of `X`. -/
theorem normalizer_le_normalizer_centralizer {G : Type} [Group G] {X : Subgroup G} :
    Subgroup.normalizer (X : Set G) ≤
      Subgroup.normalizer (Subgroup.centralizer (X : Set G) : Set G) := by
  intro y hy
  rw [Subgroup.mem_normalizer_iff]
  intro h
  rw [Subgroup.mem_centralizer_iff, Subgroup.mem_centralizer_iff]
  constructor
  · intro hh x hx
    have hx' : y⁻¹ * x * y ∈ X := by
      have h := (Subgroup.mem_normalizer_iff.mp ((Subgroup.normalizer (X : Set G)).inv_mem hy)) x
      simpa using h.mp hx
    have hcomm := hh (y⁻¹ * x * y) hx'
    calc x * (y * h * y⁻¹) = y * (y⁻¹ * x * y * h) * y⁻¹ := by group
      _ = y * (h * (y⁻¹ * x * y)) * y⁻¹ := by rw [hcomm]
      _ = (y * h * y⁻¹) * x := by group
  · intro hh x hx
    have hx' : y * x * y⁻¹ ∈ X := ((Subgroup.mem_normalizer_iff.mp hy) x).mp hx
    have hcomm := hh (y * x * y⁻¹) hx'
    calc x * h = y⁻¹ * ((y * x * y⁻¹) * (y * h * y⁻¹)) * y := by group
      _ = y⁻¹ * ((y * h * y⁻¹) * (y * x * y⁻¹)) * y := by rw [hcomm]
      _ = h * x := by group

/-- The core of the argument, isolated: for `X := S ∩ M`, the intersection `F(U) ∩ C_G(X)`
is exactly `D.F`. -/
theorem fittingIn_inf_centralizer_inf_eq_F {G : Type} [Group G] [Finite G]
    (B : Work.GW2.BenderSetup G) (D : Work.GW2.Case2Data B)
    (hpre : Work.GW2.Case2Pre B D) {X : Subgroup G}
    (hsX : D.s ∈ X) (hX : X ≤ Work.GW2.layerIn D.M) :
    Work.GW2.fittingIn B.U ⊓ Subgroup.centralizer (X : Set G) = D.F := by
  have hFU_le_U : Work.GW2.fittingIn B.U ≤ B.U := Subgroup.map_subtype_le _
  have hDF_le_CX : D.F ≤ Subgroup.centralizer (X : Set G) :=
    le_trans (Work.GW2.Case2Pre.F_cent B D hpre)
      (Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr hX))
  apply le_antisymm
  · intro z hz
    rw [Subgroup.mem_inf] at hz
    have hzs : z ∈ Subgroup.centralizer ({D.s} : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro w hw
      rw [Set.mem_singleton_iff] at hw
      subst hw
      exact hz.2 D.s hsX
    have hzB0 : z ∈ D.B0 := by
      rw [Work.GW2.Case2Pre.B0_eq B D hpre, Subgroup.mem_inf]
      exact ⟨hFU_le_U hz.1, hzs⟩
    rw [D.F_def, Subgroup.mem_inf]
    exact ⟨hzB0, hz.1⟩
  · exact le_inf (Work.GW2.Case2Data.F_le_fitting B D) hDF_le_CX

/-- **Bender 1981, §4, p. 226, first half of the paragraph proving (9).**

In the §4 configuration of Bender's 2.10 (`B : BenderSetup G`, `D : Case2Data B` with
`Case2Pre B D`), if `S ∩ M ≤ E(M) = layerIn D.M` then already `S ≤ E(M)`.

Route (all ingredients are already in the workspace):
* put `X := (B.S : Subgroup G) ⊓ D.M` and `E := layerIn D.M`; by hypothesis `X ≤ E`, and `E ≤ M`,
  so `X = (B.S) ⊓ E`;
* `C_{F(U)}(X) = D.F`: `D.F = D.B0 ⊓ F(U) = (U ⊓ C_G(s)) ⊓ F(U) = F(U) ⊓ C_G(s)` because
  `F(U) ≤ U`; and `s ∈ X` (`Case2Data.s_mem`), so `F(U) ⊓ C_G(X) ≤ F(U) ⊓ C_G(s) = D.F`, while
  `D.F ≤ F(U)` (`F_le_fitting`) and `D.F ≤ C_G(E) ≤ C_G(X)` (`Case2Pre.F_cent`);
* hence `N_S(X) ≤ N_G(D.F) = M` (`Case2Pre.N_F`): an element `y ∈ S` normalizing `X` lies in
  `S ≤ H = C_G(t)` (`BenderSetup.S_le_H`), so it normalizes `F(U)`
  (`BenderSetup.H_le_normalizer_fittingIn`), and it normalizes `C_G(X)`, so it normalizes the
  intersection `D.F`;
* if `X ≠ (B.S)` then the subgroup `X.subgroupOf (B.S)` of the `2`-group `↥(B.S)` (nilpotent, so
  it satisfies the normalizer condition, `normalizerCondition_iff_only_full_group_self_normalizing`)
  is proper and self-normalizing (`Work.CORE4.normalizer_subgroupOf_eq_inf` plus the previous
  point and `X ≤ S ⊓ N_G(X)`), a contradiction;
* so `X = (B.S)`, i.e. `(B.S) ≤ D.M`, and `(B.S) = X ≤ E`.

(The hypothesis `Case2PrePlus` is not needed by this route; it is kept because that is how the
statement is instantiated.) -/
theorem NineOuterInvContra {G : Type} [Group G] [Finite G]
    (B : Work.GW2.BenderSetup G) (D : Work.GW2.Case2Data B)
    (hpre : Work.GW2.Case2Pre B D) (hpp : Work.GW2.Case2PrePlus B D) :
    (B.S : Subgroup G) ⊓ D.M ≤ Work.GW2.layerIn D.M →
      (B.S : Subgroup G) ≤ Work.GW2.layerIn D.M := by
  intro h
  set X : Subgroup G := (B.S : Subgroup G) ⊓ D.M with hXdef
  have hXleS : X ≤ (B.S : Subgroup G) := inf_le_left
  -- `s ∈ X`
  have hsX : D.s ∈ X :=
    ⟨D.s_mem_S B, Work.CORE4.layerIn_le D.M (D.s_mem_layer B)⟩
  -- `F(U) ∩ C_G(X) = D.F`
  have hCFX : Work.GW2.fittingIn B.U ⊓ Subgroup.centralizer (X : Set G) = D.F :=
    fittingIn_inf_centralizer_inf_eq_F B D hpre hsX h
  -- `S ∩ N_G(X) = X`
  have hNSe : (B.S : Subgroup G) ⊓ Subgroup.normalizer (X : Set G) = X := by
    refine le_antisymm ?_ ?_
    · intro y hy
      obtain ⟨hyS, hyN⟩ := Subgroup.mem_inf.mp hy
      have hyM : y ∈ D.M := by
        have h1 : y ∈ Subgroup.normalizer ((Work.GW2.fittingIn B.U : Subgroup G) : Set G) :=
          Work.CORE4.BenderSetup.H_le_normalizer_fittingIn B
            (Work.GW2.BenderSetup.S_le_H B hyS)
        have h2 : y ∈ Subgroup.normalizer (Subgroup.centralizer (X : Set G) : Set G) :=
          normalizer_le_normalizer_centralizer hyN
        have h3 := Subgroup.inf_normalizer_le_normalizer_inf (Subgroup.mem_inf.mpr ⟨h1, h2⟩)
        simpa only [hCFX, Work.GW2.Case2Pre.N_F B D hpre] using h3
      rw [hXdef]
      exact Subgroup.mem_inf.mpr ⟨hyS, hyM⟩
    · refine le_inf inf_le_left ?_
      rw [Subgroup.le_normalizer_iff]
      intro a ha b hb
      exact X.mul_mem (X.mul_mem ha hb) (X.inv_mem ha)
  -- `↥(B.S)` is a finite 2-group, hence nilpotent, hence satisfies the normalizer condition
  haveI : Group.IsNilpotent ↥(B.S : Subgroup G) := (B.S).isPGroup'.isNilpotent
  have hnorm : Subgroup.normalizer
      ((X.subgroupOf (B.S : Subgroup G) : Subgroup ↥(B.S : Subgroup G)) :
        Set ↥(B.S : Subgroup G)) = X.subgroupOf (B.S : Subgroup G) := by
    rw [normalizer_subgroupOf_eq_inf hXleS, hNSe]
  have htop : X.subgroupOf (B.S : Subgroup G) = ⊤ :=
    (normalizerCondition_iff_only_full_group_self_normalizing.mp
      (Group.normalizerCondition_of_isNilpotent (G := ↥(B.S : Subgroup G))))
      _ hnorm
  have hSleX : (B.S : Subgroup G) ≤ X := Subgroup.subgroupOf_eq_top.mp htop
  exact (le_antisymm hSleX hXleS).trans_le h

end Work.CORE4
