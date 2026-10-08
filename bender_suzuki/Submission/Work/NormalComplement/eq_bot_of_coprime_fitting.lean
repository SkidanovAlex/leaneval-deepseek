import Mathlib
import Submission.Work.Fitting.centralizer_fitting_le

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# A normal subgroup of coprime order to the Fitting subgroup is trivial

`Work.NormalComplement.eq_bot_of_coprime_fitting`: if `V` is a finite solvable group (here a
subgroup of `G`), `M ≤ V` is normalized by `V`, and the order of `M` is coprime to the order of
the Fitting subgroup `F(V)`, then `M = ⊥`.

Proof.  View `M` inside `V` as `M' = M.subgroupOf V`, which is normal in `V` (this is exactly the
hypothesis `hnorm`).  Since `M'` and `F = F(V)` are both normal in `V`, the commutator `⁅M', F⁆`
is contained in `M' ⊓ F`.  As `|M'| = |M|` is coprime to `|F|`, we get `M' ⊓ F = ⊥`, hence
`⁅M', F⁆ = ⊥`, i.e. `M' ≤ C_V(F)`.  By the self-centralizing property of the Fitting subgroup in
a solvable group (`Work.Fitting.centralizer_fitting_le`), `C_V(F) ≤ F`, so `M' ≤ F`; therefore
`|M'|` divides `|F|`, and coprimality forces `|M'| = 1`, i.e. `M = ⊥`.
-/

open scoped commutatorElement

set_option linter.style.haveILetI false

namespace Work.NormalComplement

theorem eq_bot_of_coprime_fitting {G : Type*} [Group G] [Finite G]
    (V M : Subgroup G) (hsolv : Group.IsSolvable ↥V) (hMV : M ≤ V)
    (hnorm : ∀ v ∈ V, ∀ m ∈ M, v * m * v⁻¹ ∈ M)
    (hcop : Nat.Coprime (Nat.card ↥M) (Nat.card ↥(Work.Fitting.fitting ↥V))) : M = ⊥ := by
  classical
  -- `M` viewed inside `V`
  let M' : Subgroup ↥V := M.subgroupOf V
  let F : Subgroup ↥V := Work.Fitting.fitting ↥V
  -- `M'` is normal in `V`: this is the hypothesis `hnorm`
  have hM'norm : M'.Normal :=
    (Subgroup.normal_subgroupOf_iff hMV).mpr fun h k hh hk => hnorm k hk h hh
  -- `F` is normal in `V`, being characteristic
  have hFnorm : F.Normal := Subgroup.normal_of_characteristic F
  haveI : M'.Normal := hM'norm
  haveI : F.Normal := hFnorm
  -- Coprimality forces `M' ⊓ F = ⊥`
  have hDbot : M' ⊓ F = ⊥ := by
    have hcard : Nat.card ↥M' = Nat.card ↥M :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hMV).toEquiv
    have hdvd : Nat.card ↥(M' ⊓ F) ∣ Nat.card ↥M' := Subgroup.card_dvd_of_le inf_le_left
    have hdvd2 : Nat.card ↥(M' ⊓ F) ∣ Nat.card ↥F := Subgroup.card_dvd_of_le inf_le_right
    have hcopM' : Nat.Coprime (Nat.card ↥M') (Nat.card ↥F) := by rw [hcard]; exact hcop
    have hcopD : Nat.Coprime (Nat.card ↥(M' ⊓ F)) (Nat.card ↥F) :=
      Nat.Coprime.coprime_dvd_left hdvd hcopM'
    exact Subgroup.card_eq_one.mp (hcopD.eq_one_of_dvd hdvd2)
  -- hence `M'` and `F` commute
  have hcomm : ⁅M', F⁆ = ⊥ :=
    le_bot_iff.mp (hDbot ▸ Subgroup.commutator_le_inf M' F)
  have hM'C : M' ≤ Subgroup.centralizer (F : Set ↥V) :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcomm
  -- the Fitting subgroup of the solvable group `V` is self-centralizing
  haveI : Group.IsSolvable ↥V := hsolv
  have hM'leF : M' ≤ F := hM'C.trans (Work.Fitting.centralizer_fitting_le ↥V)
  -- a subgroup of `F` of coprime order is trivial
  have hcard : Nat.card ↥M' = Nat.card ↥M :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hMV).toEquiv
  have hcopM' : Nat.Coprime (Nat.card ↥M') (Nat.card ↥F) := by rw [hcard]; exact hcop
  have hdvd : Nat.card ↥M' ∣ Nat.card ↥F := Subgroup.card_dvd_of_le hM'leF
  have h1 : Nat.card ↥M = 1 := by rw [← hcard]; exact hcopM'.eq_one_of_dvd hdvd
  exact Subgroup.card_eq_one.mp h1

end Work.NormalComplement
