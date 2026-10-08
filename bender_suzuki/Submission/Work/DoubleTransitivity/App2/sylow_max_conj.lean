import Mathlib
import Submission.Work.DoubleTransitivity.Action

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

open scoped Pointwise

namespace Work.DoubleTransitivity.App2

/-- Two `p`-subgroups of `K` that are maximal among the `p`-subgroups of `K`
(Sylow `p`-subgroups of `K`) are conjugate by an element of `K`: this is the
conjugacy part of Sylow's theorem, transported between subgroups of `K` and
subgroups of the ambient group `X` along `Subgroup.subtype`. -/
theorem sylow_max_conj {X : Type} [Group X] [Finite X] {p : ℕ} [Fact p.Prime]
    {Q R K : Subgroup X}
    (hQ : IsPGroup p Q) (hQK : Q ≤ K)
    (hmaxQ : ∀ T : Subgroup X, IsPGroup p T → Q ≤ T → T ≤ K → T = Q)
    (hR : IsPGroup p R) (hRK : R ≤ K)
    (hmaxR : ∀ T : Subgroup X, IsPGroup p T → R ≤ T → T ≤ K → T = R) :
    ∃ k ∈ K, Subgroup.map (MulAut.conj k).toMonoidHom R = Q := by
  have hQ' : IsPGroup p (Q.subgroupOf K) := by
    rw [← Subgroup.comap_subtype]
    exact hQ.comap_subtype
  have hR' : IsPGroup p (R.subgroupOf K) := by
    rw [← Subgroup.comap_subtype]
    exact hR.comap_subtype
  -- `Q.subgroupOf K` is a Sylow `p`-subgroup of `K`
  have hmaxQ'' : ∀ {T : Subgroup K}, IsPGroup p T → Q.subgroupOf K ≤ T → T = Q.subgroupOf K := by
    intro T hT hle
    have hle' : Q ≤ T.map K.subtype := by
      have h := Subgroup.map_mono (f := K.subtype) hle
      rwa [Subgroup.map_subgroupOf_eq_of_le hQK] at h
    have hTle : T.map K.subtype ≤ K := Subgroup.map_subtype_le T
    have hT' := hmaxQ (T.map K.subtype) (hT.map K.subtype) hle' hTle
    have : Subgroup.map K.subtype T = Subgroup.map K.subtype (Q.subgroupOf K) := by
      rw [hT', Subgroup.map_subgroupOf_eq_of_le hQK]
    exact Subgroup.map_injective K.subtype_injective this
  -- `R.subgroupOf K` is a Sylow `p`-subgroup of `K`
  have hmaxR'' : ∀ {T : Subgroup K}, IsPGroup p T → R.subgroupOf K ≤ T → T = R.subgroupOf K := by
    intro T hT hle
    have hle' : R ≤ T.map K.subtype := by
      have h := Subgroup.map_mono (f := K.subtype) hle
      rwa [Subgroup.map_subgroupOf_eq_of_le hRK] at h
    have hTle : T.map K.subtype ≤ K := Subgroup.map_subtype_le T
    have hT' := hmaxR (T.map K.subtype) (hT.map K.subtype) hle' hTle
    have : Subgroup.map K.subtype T = Subgroup.map K.subtype (R.subgroupOf K) := by
      rw [hT', Subgroup.map_subgroupOf_eq_of_le hRK]
    exact Subgroup.map_injective K.subtype_injective this
  let Q' : Sylow p K := ⟨Q.subgroupOf K, hQ', hmaxQ''⟩
  let R' : Sylow p K := ⟨R.subgroupOf K, hR', hmaxR''⟩
  -- Sylow's conjugacy theorem inside `K`
  obtain ⟨k, hk⟩ := MulAction.exists_smul_eq K R' Q'
  have hk' : MulAut.conj k • (R.subgroupOf K) = Q.subgroupOf K := by
    have h := congrArg (fun S : Sylow p K => (S : Subgroup K)) hk
    rw [Sylow.coe_subgroup_smul] at h
    exact h
  refine ⟨(k : X), k.2, ?_⟩
  have h1 : (MulAut.conj (k : X) • R).subgroupOf K = Q.subgroupOf K := by
    rw [← Subgroup.conj_smul_subgroupOf hRK k]
    exact hk'
  have h2 := congrArg (Subgroup.map K.subtype) h1
  rw [Subgroup.subgroupOf_map_subtype, Subgroup.map_subgroupOf_eq_of_le hQK,
      inf_eq_left.2 (Subgroup.conj_smul_le_of_le hRK k)] at h2
  show MulAut.conj (k : X) • R = Q
  exact h2

end Work.DoubleTransitivity.App2
