import Mathlib
import Submission.Work.CORE2A.TorusDefs
import Submission.Work.L2F.Defs
import Submission.Work.CORE2A.c14_R_map
import Submission.Work.CORE2A.Thm26bVocab
import Submission.Work.CORE2A.Basic

open scoped MatrixGroups

namespace Work.CORE2A

open Subgroup Work.GW2

theorem c14_four_dvd (T : Work.GW2.LocalToolkit) (hFT : Work.GW2.FeitThompsonProp) {G : Type} [Group G] [Finite G] (hbc : Work.GW2.BenderCtx G) {B : Work.GW2.BenderSetup G} {p k : ℕ} [Fact p.Prime] (hCom : Work.L2F.PGL2CommutatorTorusProp) (D : Work.GW2.PGLData B p k) (hp : Odd p) (hk : 5 ≤ p ^ k) (ht : B.t ∈ Work.GW2.layerIn B.Hhat) {s : G} (hsS : s ∈ (B.S : Subgroup G)) (hs2 : orderOf s = 2) (hsE : s ∉ Work.GW2.layerIn B.Hhat) : 4 ∣ Nat.card ↥(Subgroup.zpowers B.t ⊔ Work.GW2.torusR B s ⊔ Work.GW2.torusR B (B.t * s)) := by
  -- ## elementary facts about `t`, `s`, `t * s`
  have htSE : B.t ∈ SE B := mem_SE_of_mem_layerIn ht
  have hsSE : s ∈ SE B := mem_SE_of_mem_S hsS
  have htsS : B.t * s ∈ (B.S : Subgroup G) :=
    (B.S : Subgroup G).mul_mem (B.S0_le B.t_mem) hsS
  have htsSE : B.t * s ∈ SE B := mem_SE_of_mem_S htsS
  have hts_comm : B.t * s = s * B.t :=
    (Subgroup.mem_centralizer_singleton_iff.mp
      (show s ∈ Subgroup.centralizer ({B.t} : Set G) from bSetup_S_le_H B hsS)).symm
  have ht2 : B.t * B.t = 1 := by rw [← pow_two, ← B.t_order]; exact pow_orderOf_eq_one B.t
  have hs2' : s * s = 1 := by rw [← pow_two, ← hs2]; exact pow_orderOf_eq_one s
  have hts_sq : (B.t * s) * (B.t * s) = 1 := by
    calc (B.t * s) * (B.t * s) = B.t * (s * B.t) * s := by group
      _ = B.t * (B.t * s) * s := by rw [← hts_comm]
      _ = (B.t * B.t) * (s * s) := by group
      _ = 1 := by rw [ht2, hs2', one_mul]
  have hts_ne1 : B.t * s ≠ 1 := by
    intro h
    have hs_eq : s = B.t := by
      have h2 : s = B.t⁻¹ * (B.t * s) := by group
      rw [h, mul_one, inv_eq_of_mul_eq_one_right ht2] at h2
      exact h2
    exact hsE (by rw [hs_eq]; exact ht)
  have hts2 : orderOf (B.t * s) = 2 := by
    rw [orderOf_eq_iff (by norm_num : 0 < 2)]
    refine ⟨by rw [pow_two]; exact hts_sq, ?_⟩
    intro m hm hm2
    interval_cases m
    simpa using hts_ne1
  -- `t ∉ Z(E)`
  have ht_not_zE : B.t ∉ zE B := by
    intro htmem
    by_cases hE : layerIn B.Hhat = ⊥
    · have h1 : B.t = 1 := by rw [hE] at ht; simpa using ht
      exact bSetup_t_ne_one B h1
    · have hodd : Odd (Nat.card ↥(zE B)) := zE_odd T hFT hbc B hE
      have h2dvd : 2 ∣ Nat.card ↥(zE B) := by
        have h := Subgroup.orderOf_dvd_natCard (zE B) htmem
        rwa [B.t_order] at h
      exact Nat.not_even_iff_odd.mpr hodd (even_iff_two_dvd.mpr h2dvd)
  -- ## the two elements of `PGL₂(q)`
  have ht'2 : orderOf (D.φ ⟨B.t, htSE⟩) = 2 := by
    have hdvd : orderOf (D.φ ⟨B.t, htSE⟩) ∣ orderOf (⟨B.t, htSE⟩ : ↥(SE B)) :=
      orderOf_map_dvd D.φ _
    rw [Subgroup.orderOf_mk, B.t_order] at hdvd
    rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h | h
    · exfalso
      have h1 : D.φ ⟨B.t, htSE⟩ = 1 := orderOf_eq_one_iff.mp h
      have hmem : (⟨B.t, htSE⟩ : ↥(SE B)) ∈ D.φ.ker := MonoidHom.mem_ker.mpr h1
      rw [D.ker] at hmem
      exact ht_not_zE (Subgroup.mem_subgroupOf.mp hmem)
    · exact h
  have hs'2 : orderOf (D.φ ⟨s, hsSE⟩) = 2 := by
    have hdvd : orderOf (D.φ ⟨s, hsSE⟩) ∣ orderOf (⟨s, hsSE⟩ : ↥(SE B)) :=
      orderOf_map_dvd D.φ _
    rw [Subgroup.orderOf_mk, hs2] at hdvd
    rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h | h
    · exfalso
      have h1 : D.φ ⟨s, hsSE⟩ = 1 := orderOf_eq_one_iff.mp h
      have hmem : (⟨s, hsSE⟩ : ↥(SE B)) ∈ D.φ.ker := MonoidHom.mem_ker.mpr h1
      rw [D.ker] at hmem
      exact hsE (zE_le (Subgroup.mem_subgroupOf.mp hmem))
    · exact h
  have hcomm : D.φ ⟨B.t, htSE⟩ * D.φ ⟨s, hsSE⟩ = D.φ ⟨s, hsSE⟩ * D.φ ⟨B.t, htSE⟩ := by
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext hts_comm
  have ht'L : D.φ ⟨B.t, htSE⟩ ∈ Lsub p k := (D.mem_layer_iff ⟨B.t, htSE⟩).mp ht
  have hs'L : D.φ ⟨s, hsSE⟩ ∉ Lsub p k :=
    fun h => hsE ((D.mem_layer_iff ⟨s, hsSE⟩).mpr h)
  -- ## the commutator–torus input
  have hcom := hCom p k hp hk (D.φ ⟨B.t, htSE⟩) (D.φ ⟨s, hsSE⟩) ht'2 hs'2 hcomm ht'L hs'L
  obtain ⟨-, -, -, -, -, -, h4dvd⟩ := hcom
  -- ## name the pieces
  let R : Subgroup (Matrix.ProjGenLinGroup (Fin 2) (GaloisField p k)) :=
    ⁅Subgroup.zpowers (D.φ ⟨B.t, htSE⟩),
      Lsub p k ⊓ Subgroup.centralizer ({D.φ ⟨s, hsSE⟩} : Set _)⁆
  let R' : Subgroup (Matrix.ProjGenLinGroup (Fin 2) (GaloisField p k)) :=
    ⁅Subgroup.zpowers (D.φ ⟨B.t, htSE⟩),
      Lsub p k ⊓ Subgroup.centralizer ({D.φ ⟨B.t, htSE⟩ * D.φ ⟨s, hsSE⟩} : Set _)⁆
  have h4A : 4 ∣ Nat.card ↥(Subgroup.zpowers (D.φ ⟨B.t, htSE⟩) ⊔ R ⊔ R') := h4dvd
  -- ## P3: the images of the two tori
  have hRs : ((torusR B s).subgroupOf (SE B)).map D.φ = R := by
    rw [c14_R_map T hFT hbc D ht hsS hs2 htSE hsSE]
  have htsphi : D.φ ⟨B.t * s, htsSE⟩ =
      D.φ ⟨B.t, htSE⟩ * D.φ ⟨s, hsSE⟩ := by
    rw [← map_mul]
    congr 1
  have hRts : ((torusR B (B.t * s)).subgroupOf (SE B)).map D.φ = R' := by
    rw [c14_R_map T hFT hbc D ht htsS hts2 htSE htsSE]
    rw [htsphi]
  -- ## the group `X` and its image `M`
  let X : Subgroup G := Subgroup.zpowers B.t ⊔ torusR B s ⊔ torusR B (B.t * s)
  let M : Subgroup (Matrix.ProjGenLinGroup (Fin 2) (GaloisField p k)) :=
    (X.subgroupOf (SE B)).map D.φ
  have hXtorus : torusR B s ≤ X := le_trans le_sup_right le_sup_left
  have hXtorus' : torusR B (B.t * s) ≤ X := le_sup_right
  have hsubA : Subgroup.zpowers (D.φ ⟨B.t, htSE⟩) ⊔ R ⊔ R' ≤ M := by
    refine sup_le (sup_le ?_ ?_) ?_
    · rw [Subgroup.zpowers_le]
      refine Subgroup.mem_map.mpr ⟨⟨B.t, htSE⟩, ?_, rfl⟩
      rw [Subgroup.mem_subgroupOf]
      exact Subgroup.mem_sup_left (Subgroup.mem_sup_left (Subgroup.mem_zpowers B.t))
    · rw [← hRs]
      exact Subgroup.map_mono (fun x hx =>
        Subgroup.mem_subgroupOf.mpr (hXtorus (Subgroup.mem_subgroupOf.mp hx)))
    · rw [← hRts]
      exact Subgroup.map_mono (fun x hx =>
        Subgroup.mem_subgroupOf.mpr (hXtorus' (Subgroup.mem_subgroupOf.mp hx)))
  have hcardAle : Nat.card ↥(Subgroup.zpowers (D.φ ⟨B.t, htSE⟩) ⊔ R ⊔ R') ∣ Nat.card ↥M := by
    have h := Subgroup.relIndex_mul_card (Subgroup.zpowers (D.φ ⟨B.t, htSE⟩) ⊔ R ⊔ R') M
    rw [inf_eq_left.mpr hsubA] at h
    exact ⟨_, by rw [mul_comm]; exact h.symm⟩
  have hXSE : X ≤ SE B := by
    refine sup_le (sup_le ?_ ?_) ?_
    · exact Subgroup.zpowers_le.mpr htSE
    · rw [torusR]
      refine le_trans (Subgroup.commutator_le_sup (Subgroup.zpowers B.t)
        (layerIn B.Hhat ⊓ Subgroup.centralizer ({s} : Set G))) ?_
      exact sup_le (Subgroup.zpowers_le.mpr htSE) (le_trans inf_le_left layerIn_le_SE)
    · rw [torusR]
      refine le_trans (Subgroup.commutator_le_sup (Subgroup.zpowers B.t)
        (layerIn B.Hhat ⊓ Subgroup.centralizer ({B.t * s} : Set G))) ?_
      exact sup_le (Subgroup.zpowers_le.mpr htSE) (le_trans inf_le_left layerIn_le_SE)
  have hcardMX : Nat.card ↥M ∣ Nat.card ↥X := by
    have h := Subgroup.card_map_dvd (X.subgroupOf (SE B)) D.φ
    have h2 : Nat.card ↥(X.subgroupOf (SE B)) = Nat.card ↥X :=
      (Subgroup.card_map_of_injective (SE B).subtype_injective).symm.trans (by
        congr 1
        rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hXSE])
    rwa [h2] at h
  exact dvd_trans (dvd_trans h4A hcardAle) hcardMX

end Work.CORE2A
