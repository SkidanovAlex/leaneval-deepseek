import Mathlib
import Submission.Work.NormalComplement.Design.Extra
import Submission.Work.Fitting.fitting_isNilpotent
import Submission.Work.Fitting.fitting_eq_iSup_pCore

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option linter.style.haveILetI false

namespace Work.NormalComplement

/-- If a prime `q` divides the order of the Fitting subgroup of `V`, then `V` has a nontrivial
normal `q`-subgroup: the (characteristic, hence normal) Sylow `q`-subgroup of `F(V)`. -/
theorem normal_pSubgroup_of_dvd_fitting {G : Type} [Group G] [Finite G] {V : Subgroup G} {q : ℕ}
    (hq : q.Prime) (hdvd : q ∣ Nat.card ↥(Work.NormalComplement.Design.fitSub V)) :
    ∃ X : Subgroup G, X ≤ V ∧ V ≤ Subgroup.normalizer (X : Set G) ∧ IsPGroup q ↥X ∧ X ≠ ⊥ := by
  haveI : Fact q.Prime := ⟨hq⟩
  -- `F = F(V)`, the Fitting subgroup of `V`, viewed as a subgroup of `↥V`.
  let F : Subgroup ↥V := Work.Fitting.fitting ↥V
  haveI : Group.IsNilpotent ↥F := Work.Fitting.fitting_isNilpotent ↥V
  have hFnorm : F.Normal :=
    Work.Fitting.normal_sSup (S := Work.Fitting.fittingSet ↥V)
      (fun N hN => (Work.Fitting.mem_fittingSet.mp hN).1)
  -- A Sylow `q`-subgroup of `F`; it is normal (whence characteristic) because `F` is nilpotent.
  obtain ⟨Q : Sylow q ↥F⟩ := Sylow.nonempty (p := q) (G := ↥F)
  have hQnorm : (Q : Subgroup ↥F).Normal := inferInstance
  have hQchar : (Q : Subgroup ↥F).Characteristic := Sylow.characteristic_of_normal Q hQnorm
  -- Push it into `↥V`; it is normal in `↥V` since `F` is.
  let N : Subgroup ↥V := (Q : Subgroup ↥F).map F.subtype
  have hNnorm : N.Normal := Work.Fitting.map_characteristic_normal hFnorm hQchar
  -- Push it into `G`: this is the desired normal `q`-subgroup of `V`.
  let X : Subgroup G := N.map V.subtype
  have hXleV : X ≤ V := Subgroup.map_subtype_le N
  -- `q ∣ |F(V)| = |F|`.
  have hdvdF : q ∣ Nat.card ↥F := by
    have hcard : Nat.card ↥(Work.NormalComplement.Design.fitSub V) = Nat.card ↥F := by
      rw [Work.NormalComplement.Design.fitSub,
        Subgroup.card_map_of_injective (Subgroup.subtype_injective V)]
    rwa [hcard] at hdvd
  have hfact : 0 < (Nat.card ↥F).factorization q :=
    Nat.Prime.factorization_pos_of_dvd hq Nat.card_pos.ne' hdvdF
  -- `Q` is nontrivial, so `X` is.
  have hQgt : 1 < Nat.card ↥(Q : Subgroup ↥F) := by
    rw [Sylow.card_eq_multiplicity Q]
    exact Nat.one_lt_pow hfact.ne' hq.one_lt
  have hcardXQ : Nat.card ↥X = Nat.card ↥(Q : Subgroup ↥F) := by
    show Nat.card ↥(N.map V.subtype) = Nat.card ↥(Q : Subgroup ↥F)
    rw [Subgroup.card_map_of_injective (K := N) (Subgroup.subtype_injective V),
      Subgroup.card_map_of_injective (K := (Q : Subgroup ↥F)) (Subgroup.subtype_injective F)]
  refine ⟨X, hXleV, ?_, ?_, ?_⟩
  · -- `V` normalizes `X`: both are obtained by pushing a normal subgroup through `↥V → G`.
    refine (Subgroup.normal_subgroupOf_iff_le_normalizer hXleV).mp
      ((Subgroup.normal_subgroupOf_iff hXleV).mpr ?_)
    intro h k hh hk
    obtain ⟨n, hn, he⟩ := Subgroup.mem_map.mp hh
    rw [← he]
    exact Subgroup.mem_map.mpr ⟨⟨k, hk⟩ * n * ⟨k, hk⟩⁻¹,
      hNnorm.conj_mem n hn ⟨k, hk⟩, by simp⟩
  · -- `X` is a `q`-group, being the image of the `q`-group `Q` under injective maps.
    exact ((Q.isPGroup').map F.subtype).map V.subtype
  · exact (Subgroup.one_lt_card_iff_ne_bot X).mp (hcardXQ.symm ▸ hQgt)

end Work.NormalComplement
