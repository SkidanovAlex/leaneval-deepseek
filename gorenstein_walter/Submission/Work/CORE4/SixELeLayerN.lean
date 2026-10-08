import Mathlib
import Submission.Work.CORE4.Defs
import Submission.Work.CORE4.Defs19
import Submission.Work.CORE4.LayerFactsProper
import Submission.Work.CORE4.API
import Submission.Work.CORE4.LayerCtx6
import Submission.Work.CORE4.CountSetup
import Submission.Work.CORE4.subnormal_le_center_or_eq_of_center

open scoped MatrixGroups

namespace Work.CORE4

open Work.GW2 Subgroup

/-- **Design-19 leaf S3**: `E = layerIn D.M ≤ E₀ := layerIn (N_G(X))`.

Statement (verbatim): `SixELeLayerNProp I` = for `BenderCtx G`, `B`, `D` with `Case2Pre B D`, and
`X ≠ ⊥`, `X ≤ D.F`, `B.t ∈ layerIn (N_G(X))` (leaf S2):
`layerIn D.M ≤ layerIn (N_G(X))`.

Route: `E ≤ C_G(X) ≤ N_G(X) ≤ N_G(E₀)` (`Work.CORE4.layerIn_le_normalizer`), so
`E ⊓ E₀ ⊴ E`; it contains `t` (S2), and `t ∉ Z(E)` since `|Z(E)|` is odd
(`Work.CORE4.layer_facts_proper_quasisimple`, which also supplies `IsQuasisimple E` — the
`layer_facts_proper` variant does not expose it).  A normal subgroup `N ⊴ E` of the quasisimple `E`
with `N ≰ Z(E)` equals `E` (`N Z(E)/Z(E) ⊴ E/Z(E)` is nontrivial in the simple `E/Z(E)`, so it is
everything; then `E = [E,E] = [N,N] ≤ N`). -/
theorem SixELeLayerN (I : Work.GW2.C4Inputs) : Work.GW2.C19.SixELeLayerNProp I := by
  intro G _inst _fin hbc B D hpre X _hX hXF ht
  obtain ⟨-, -, -, -, -, hFcen, -, -⟩ := hpre
  -- `E := layerIn D.M` is quasisimple with odd centre (`Bender §4, p. 224`)
  obtain ⟨E1, hE1norm, hlayer, hQ1, hZodd1, hshape⟩ :=
    Work.CORE4.layer_facts_proper_quasisimple I hbc D.M_coatom.ne_top D.t_mem
  have hQ : Work.GW2.IsQuasisimple (Work.GW2.layerIn D.M) := by
    rw [Work.GW2.layerIn, hlayer]
    exact Work.CORE4.isQuasisimple_map _ (Subgroup.subtype_injective D.M) hQ1
  have hZodd : Odd (Nat.card (Subgroup.center ↥(Work.GW2.layerIn D.M))) := by
    rw [Work.GW2.layerIn, hlayer]
    exact (Work.CORE4.quasisimple_shape_map _ (Subgroup.subtype_injective D.M) hQ1 hZodd1
      hshape).2.1
  set K : Subgroup G := Subgroup.normalizer (X : Set G) with hK
  -- `E ≤ C_G(X)`: `X ≤ D.F ≤ C_G(E)`
  have hEcenX : Work.GW2.layerIn D.M ≤ Subgroup.centralizer (X : Set G) := by
    intro y hy
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    have hxE : x ∈ Subgroup.centralizer ((Work.GW2.layerIn D.M : Subgroup G) : Set G) :=
      hFcen (hXF hx)
    exact (Subgroup.mem_centralizer_iff.mp hxE y hy).symm
  -- `E ≤ C_G(X) ≤ N_G(X) = K`
  have hEK : Work.GW2.layerIn D.M ≤ K := by
    rw [hK]
    exact le_trans hEcenX (Subgroup.centralizer_le_normalizer (X : Set G))
  -- `E₀ := layerIn K` is normal in `K`
  have hE0norm : ((Work.GW2.layerIn K).subgroupOf K).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer (Work.CORE4.layerIn_le K)).mpr
      (Work.CORE4.layerIn_le_normalizer K)
  -- `N = (E ⊓ E₀) ≤ E`, viewed inside `↥E`, is normal there and contains `t`
  let φ : ↥(Work.GW2.layerIn D.M) →* ↥K := Subgroup.inclusion hEK
  let N : Subgroup ↥(Work.GW2.layerIn D.M) := ((Work.GW2.layerIn K).subgroupOf K).comap φ
  have hNnorm : N.Normal := hE0norm.comap φ
  have hNsub : N.IsSubnormal := hNnorm.isSubnormal
  -- `↥E` is perfect (`E = [E,E]`)
  have hperf : commutator ↥(Work.GW2.layerIn D.M) = ⊤ := by
    refine Subgroup.map_injective (f := (Work.GW2.layerIn D.M).subtype) Subtype.val_injective ?_
    rw [Subgroup.map_subtype_commutator, hQ.1, Subgroup.map_top, Subgroup.range_subtype]
  -- the dichotomy: `N ≤ Z(E)` or `N = E`
  rcases subnormal_le_center_or_eq_of_center N hNsub hperf hQ.2 with hNle | hNtop
  · -- `N ≤ Z(E)` is impossible: `t ∈ N` has order `2`, but `|Z(E)|` is odd
    exfalso
    have htE : B.t ∈ Work.GW2.layerIn D.M := D.t_mem
    have htN : (⟨B.t, htE⟩ : ↥(Work.GW2.layerIn D.M)) ∈ N := by
      rw [Subgroup.mem_comap]
      rw [Subgroup.mem_subgroupOf]
      exact ht
    have hcenter : (⟨B.t, htE⟩ : ↥(Work.GW2.layerIn D.M)) ∈
        Subgroup.center ↥(Work.GW2.layerIn D.M) := hNle htN
    have hdvd : orderOf (⟨B.t, htE⟩ : ↥(Work.GW2.layerIn D.M)) ∣
        Nat.card (Subgroup.center ↥(Work.GW2.layerIn D.M)) :=
      Subgroup.orderOf_dvd_natCard _ hcenter
    have hord : orderOf (⟨B.t, htE⟩ : ↥(Work.GW2.layerIn D.M)) = 2 := by
      rw [← Subgroup.orderOf_coe (⟨B.t, htE⟩ : ↥(Work.GW2.layerIn D.M))]
      exact B.t_order
    rw [hord] at hdvd
    exact (Nat.not_even_iff_odd.mpr hZodd) (even_iff_two_dvd.mpr hdvd)
  · -- `N = ⊤` means `E ≤ E₀`
    intro y hy
    have hmem : (⟨y, hy⟩ : ↥(Work.GW2.layerIn D.M)) ∈ N := by
      rw [hNtop]
      exact Subgroup.mem_top _
    rw [Subgroup.mem_comap] at hmem
    rw [Subgroup.mem_subgroupOf] at hmem
    rwa [show ((φ ⟨y, hy⟩ : ↥K) : G) = y from rfl] at hmem

end Work.CORE4
