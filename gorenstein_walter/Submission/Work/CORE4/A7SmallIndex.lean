import Mathlib
import Submission.Work.CORE4.Defs
import Submission.Work.CORE4.Defs10
import Submission.Work.CORE4.API
import Submission.Work.CORE4.CountSetup
import Submission.Work.CORE4.LayerCtx6
import Submission.Work.CORE4.relIndex_inter_H_eq_of_oneInvClass
import Submission.Work.CORE4.A7KBound.K_le_layerIn_and_inf_center
import Submission.Work.CORE4.A7SI.SylowDihedral4
import Submission.Work.CORE4.A7SI.A7InvolutionsCard
import Submission.Work.CORE4.A7SI.RelIndexInfCentralizer
import Submission.Work.CORE4.A7SI.InvolutionsSdiff
import Submission.Work.CORE2A.involution_class_card

set_option maxHeartbeats 1000000

namespace Work.CORE4

open Subgroup

/-- **LEAF C10.A7 `A7SmallIndex`** (Bender p. 226): "`|J| ≤ |J ∩ M| + 21|G : M|`, … `|G : M| ≤ 7`",
and `7 ∣ |M|`.

`A7SmallIndexProp I` gives, from `Hyp9 G B C`, `IsA7Case C.D`, `A7Facts1`–`A7Facts6`:

    C.D.M.index ≤ 7  ∧  7 ∣ Nat.card C.D.M

Route (design pass 10 §3.2, A7), with `E = E(M) = layerIn C.D.M`, `H = C_G(t)`,
`J = {x : G | orderOf x = 2}`, `R = |M : M ⊓ H| = |E : C_E(t)|`:

* `Z(E)` has odd order (`CORE4/LayerCtx6`), hence `S ≃* D₈` (`A7SI/SylowDihedral4`) and
  `H = U ⊔ S` (`toolkit.split`); it follows that `M = E ⊔ F` with `|F| = 3`, so every involution
  of `M` lies in `E`;
* `|J ∩ M| = |J ∩ E| = R` (one class of involutions in `E`, `CORE2A/involution_class_card`);
* `3 · H.index = R · M.index` (`A7Facts5` and `Subgroup.relIndex_mul_index`);
* `H.index ≤ |J| ≤ |J ∩ M| + 21 · M.index = R + 21 · M.index` (the `21` is `A7Facts6` via
  `A7SI/InvolutionsSdiff`), while `105 ≤ R` (`A7SI/RelIndexInfCentralizer`); a short case
  analysis gives `M.index ≤ 7`;
* `7 ∣ |M|` because `7 ∣ |A₇| = 2520`, `E/Z(E) ≅ A₇` and `E ≤ M`. -/
theorem A7SmallIndex (I : Work.GW2.C4Inputs) : Work.GW2.A7SmallIndexProp I := by
  intro G _ _ B C hHyp hA7 hf1 hf2 hf3 hf4 hf5 hf6
  obtain ⟨hbc, hcase2, hplus, hseven, height⟩ := hHyp
  -- ## 0. The centre of `E` is odd, and `S` is dihedral of order eight
  have hZodd : Odd (Nat.card (Subgroup.center ↥(Work.GW2.layerIn C.D.M))) :=
    (LayerCtx6 I hbc C (DihOrCycSub hbc.sylow C.D.M)).2.1
  have hSE : (B.S : Subgroup G) ≤ Work.GW2.layerIn C.D.M := hf2.2.2.1
  have hScard : Nat.card (B.S : Subgroup G) = 8 := hf2.2.2.2.1
  have hEM : Work.GW2.layerIn C.D.M ≤ C.D.M := Work.CORE4.layerIn_le C.D.M
  have hdih : Nonempty ((B.S : Subgroup G) ≃* DihedralGroup 4) :=
    A7SI.SylowDihedral4 B.S hSE hScard hA7 hZodd I.toolkit.a7
  -- ## 1. `H = U ⊔ S`, and `M ⊓ H ≤ E ⊔ F`
  have hHUS : B.H = B.U ⊔ (B.S : Subgroup G) :=
    (I.toolkit.split G B.S 4 (by norm_num) hdih B.t B.t_mem_S B.t_order B.t_central).symm
  have hKE : C.D.K ≤ Work.GW2.layerIn C.D.M := by
    rw [hplus.2.1]
    exact Work.CORE4.A7KBound.commutator_le_of_le_normalizer
      (N := Work.GW2.layerIn C.D.M) (M := C.D.M)
      (A := (B.S : Subgroup G) ⊓ Work.GW2.layerIn C.D.M) (B := B.U ⊓ C.D.M)
      inf_le_right (Work.CORE4.layerIn_le_normalizer C.D.M) inf_le_right
  have hFM : C.D.F ≤ C.D.M :=
    le_trans (C.D.F_le_B0 B) (le_trans (C.D.B0_le B) inf_le_right)
  have hFH : C.D.F ≤ B.H := by
    refine le_trans (Work.GW2.Case2Pre.F_cent B C.D C.pre) ?_
    refine Subgroup.centralizer_le ?_
    intro y hy
    rw [Set.mem_singleton_iff] at hy
    subst hy
    exact C.D.t_mem
  have hMH : C.D.M ⊓ B.H ≤ Work.GW2.layerIn C.D.M ⊔ C.D.F := by
    intro x hx
    obtain ⟨hxM, hxH⟩ := Subgroup.mem_inf.mp hx
    haveI : (B.U.subgroupOf B.H).Normal := B.U_normal
    have htop : (B.U.subgroupOf B.H) ⊔ ((B.S : Subgroup G).subgroupOf B.H) = ⊤ := by
      rw [← Subgroup.subgroupOf_sup B.U_le_H B.S_le_H, ← hHUS, Subgroup.subgroupOf_self]
    have hxH' : (⟨x, hxH⟩ : ↥B.H) ∈
        (B.U.subgroupOf B.H) ⊔ ((B.S : Subgroup G).subgroupOf B.H) := by
      rw [htop]; exact Subgroup.mem_top _
    obtain ⟨u, hu, s, hs, hus⟩ := Subgroup.mem_sup_of_normal_left.mp hxH'
    have huU : (u : G) ∈ B.U := Subgroup.mem_subgroupOf.mp hu
    have hsS : (s : G) ∈ (B.S : Subgroup G) := Subgroup.mem_subgroupOf.mp hs
    have hxs : (u : G) * (s : G) = x := by
      have hh := congrArg (Subtype.val) hus
      simpa using hh
    have huM : (u : G) ∈ C.D.M := by
      have h2 : (u : G) = x * (s : G)⁻¹ := by rw [← hxs]; group
      rw [h2]
      exact C.D.M.mul_mem hxM (C.D.M.inv_mem (hEM (hSE hsS)))
    have huKF : (u : G) ∈ Work.GW2.layerIn C.D.M ⊔ C.D.F := by
      have h1 : (u : G) ∈ B.U ⊓ C.D.M := Subgroup.mem_inf.mpr ⟨huU, huM⟩
      rw [Work.GW2.Case2Pre.U_eq B C.D C.pre, hf3.2.1] at h1
      exact (sup_le (le_trans hKE le_sup_left)
        (le_sup_right : C.D.F ≤ Work.GW2.layerIn C.D.M ⊔ C.D.F)) h1
    rw [← hxs]
    exact (Work.GW2.layerIn C.D.M ⊔ C.D.F).mul_mem huKF (Subgroup.mem_sup_left (hSE hsS))
  -- ## 2. `M = E ⊔ F`
  have hMEF : C.D.M = Work.GW2.layerIn C.D.M ⊔ C.D.F := by
    have h1 : C.D.M = Work.GW2.layerIn C.D.M ⊔ (C.D.M ⊓ B.H) :=
      M_eq_layerIn_sup_of_oneInvClass C.D.M C.pre.2.1 C.D.t_mem
    have hF_H : C.D.F ≤ C.D.M ⊓ B.H := le_inf hFM hFH
    have h2 : Work.GW2.layerIn C.D.M ⊔ (C.D.M ⊓ B.H) = Work.GW2.layerIn C.D.M ⊔ C.D.F :=
      le_antisymm
        (sup_le (le_sup_left : Work.GW2.layerIn C.D.M ≤ Work.GW2.layerIn C.D.M ⊔ C.D.F) hMH)
        (sup_le (le_sup_left : Work.GW2.layerIn C.D.M ≤
            Work.GW2.layerIn C.D.M ⊔ (C.D.M ⊓ B.H)) (le_sup_of_le_right hF_H))
    exact h1.trans h2
  -- ## 3. Every involution of `M` lies in `E`
  have hinvME : ∀ x ∈ C.D.M, orderOf x = 2 → x ∈ Work.GW2.layerIn C.D.M := by
    intro x hxM hx2
    have hE'norm : ((Work.GW2.layerIn C.D.M).subgroupOf C.D.M).Normal :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer (Work.CORE4.layerIn_le C.D.M)).mpr
        (Work.CORE4.layerIn_le_normalizer C.D.M)
    have htop : ((Work.GW2.layerIn C.D.M).subgroupOf C.D.M) ⊔ (C.D.F.subgroupOf C.D.M) = ⊤ := by
      rw [← Subgroup.subgroupOf_sup (Work.CORE4.layerIn_le C.D.M) hFM]
      rw [← hMEF, Subgroup.subgroupOf_self]
    have hxM' : (⟨x, hxM⟩ : ↥C.D.M) ∈
        ((Work.GW2.layerIn C.D.M).subgroupOf C.D.M) ⊔ (C.D.F.subgroupOf C.D.M) := by
      rw [htop]; exact Subgroup.mem_top _
    haveI := hE'norm
    obtain ⟨u, hu, v, hv, huv⟩ := Subgroup.mem_sup_of_normal_left.mp hxM'
    have huE : (u : G) ∈ Work.GW2.layerIn C.D.M := Subgroup.mem_subgroupOf.mp hu
    have hvF : (v : G) ∈ C.D.F := Subgroup.mem_subgroupOf.mp hv
    have hxuv : (u : G) * (v : G) = x := by
      have hh := congrArg (Subtype.val) huv
      simpa using hh
    have hcomm : (u : G) * (v : G) = (v : G) * (u : G) := by
      have hf := Work.GW2.Case2Pre.F_cent B C.D C.pre hvF
      rw [Subgroup.mem_centralizer_iff] at hf
      exact hf (u : G) huE
    have hx2' : x * x = 1 := by
      rw [← pow_two, ← orderOf_dvd_iff_pow_eq_one, hx2]
    have hv2E : (v : G) ^ 2 ∈ Work.GW2.layerIn C.D.M := by
      have hsq : ((u : G) ^ 2) * ((v : G) ^ 2) = 1 := by
        have h1 : ((u : G) * (v : G)) ^ 2 = 1 := by rw [hxuv, pow_two]; exact hx2'
        rwa [Commute.mul_pow hcomm] at h1
      have hvv : (v : G) ^ 2 = (((u : G) ^ 2))⁻¹ := eq_inv_of_mul_eq_one_right hsq
      rw [hvv]
      exact (Work.GW2.layerIn C.D.M).inv_mem ((Work.GW2.layerIn C.D.M).pow_mem huE 2)
    have hvE : (v : G) ∈ Work.GW2.layerIn C.D.M := by
      have hv3 : (v : G) ^ 3 = 1 := by
        rw [← orderOf_dvd_iff_pow_eq_one]
        exact dvd_trans (Subgroup.orderOf_dvd_natCard C.D.F hvF) (hf1.2.1 ▸ dvd_rfl)
      have hv_eq : (v : G) = (((v : G) ^ 2))⁻¹ :=
        eq_inv_of_mul_eq_one_right (by rw [← pow_succ, hv3])
      rw [hv_eq]
      exact (Work.GW2.layerIn C.D.M).inv_mem hv2E
    rw [← hxuv]
    exact (Work.GW2.layerIn C.D.M).mul_mem huE hvE
  -- ## 4. `|J ∩ M| = R`, where `R = |M : M ⊓ H|`
  have hJMin_expr : {x : G | orderOf x = 2 ∧ x ∈ C.D.M}.ncard =
      (C.D.M ⊓ B.H).relIndex C.D.M := by
    have hset : {x : G | orderOf x = 2 ∧ x ∈ C.D.M} =
        {x : G | x ∈ Work.GW2.layerIn C.D.M ∧ orderOf x = 2} := by
      ext x
      constructor
      · rintro ⟨hx2, hxM⟩
        exact ⟨hinvME x hxM hx2, hx2⟩
      · rintro ⟨hxE, hx2⟩
        exact ⟨hx2, Work.CORE4.layerIn_le C.D.M hxE⟩
    rw [hset]
    rw [Work.CORE2A.involution_class_card (Work.GW2.layerIn C.D.M) B.t C.D.t_mem B.t_order]
    · have hcentE : (Subgroup.centralizer ({B.t} : Set G)).relIndex (Work.GW2.layerIn C.D.M) =
          (Work.GW2.layerIn C.D.M ⊓ B.H).relIndex (Work.GW2.layerIn C.D.M) := by
        simp only [Subgroup.relIndex]
        congr 1
        ext y
        simp [Subgroup.mem_subgroupOf]
      rw [hcentE, Work.CORE4.relIndex_inter_H_eq_of_oneInvClass C.D.M C.pre.2.1 C.D.t_mem]
    · intro x y hxE hyE hx2 hy2
      exact C.pre.2.1 x ⟨hxE, hx2⟩ y ⟨hyE, hy2⟩
  set R : ℕ := (C.D.M ⊓ B.H).relIndex C.D.M with hRdef
  have hJMin : {x : G | orderOf x = 2 ∧ x ∈ C.D.M}.ncard = R := by
    rw [hRdef]; exact hJMin_expr
  have hR : 105 ≤ R := by
    rw [hRdef]
    rw [Work.CORE4.relIndex_inter_H_eq_of_oneInvClass C.D.M C.pre.2.1 C.D.t_mem]
    exact A7SI.RelIndexInfCentralizer (Work.GW2.layerIn C.D.M) B.t hA7 hZodd C.D.t_mem
      B.t_order I.toolkit.a7
  -- ## 5. `3 * H.index = R * M.index`
  have hkey : 3 * B.H.index = R * C.D.M.index := by
    have h1 : (C.D.M ⊓ B.H).relIndex B.H * B.H.index = (C.D.M ⊓ B.H).index :=
      Subgroup.relIndex_mul_index (H := C.D.M ⊓ B.H) (K := B.H) inf_le_right
    have h2 : (C.D.M ⊓ B.H).relIndex C.D.M * C.D.M.index = (C.D.M ⊓ B.H).index :=
      Subgroup.relIndex_mul_index (H := C.D.M ⊓ B.H) (K := C.D.M) inf_le_left
    have h3 : (C.D.M ⊓ B.H).relIndex B.H = 3 := by
      rw [inf_comm]; exact hf5.1
    rw [h3] at h1
    rw [hRdef, h2]
    exact h1
  -- ## 6. `H.index ≤ |J|`
  have hJH : B.H.index ≤ {x : G | orderOf x = 2}.ncard := by
    have h1 : B.H.index = (conjugatesOf B.t).ncard := by
      show (Subgroup.centralizer ({B.t} : Set G)).index = (conjugatesOf B.t).ncard
      exact Subgroup.index_centralizer_eq_ncard B.t
    rw [h1]
    refine Set.ncard_le_ncard ?_
    intro x hx
    simp only [conjugatesOf] at hx
    change IsConj B.t x at hx
    rw [isConj_iff] at hx
    obtain ⟨c, rfl⟩ := hx
    change orderOf (c * B.t * c⁻¹) = 2
    rw [show c * B.t * c⁻¹ = MulAut.conj c B.t from by simp [MulAut.conj_apply],
      MulEquiv.orderOf_eq (MulAut.conj c) B.t]
    exact B.t_order
  -- ## 7. `|J| ≤ |J ∩ M| + |J \ M| ≤ R + 21 · M.index`
  have hJle : {x : G | orderOf x = 2}.ncard ≤
      {x : G | orderOf x = 2 ∧ x ∈ C.D.M}.ncard +
        {x : G | orderOf x = 2 ∧ x ∉ C.D.M}.ncard := by
    refine le_trans (Set.ncard_le_ncard ?_) (Set.ncard_union_le _ _)
    intro x hx
    by_cases h : x ∈ C.D.M
    · exact Or.inl ⟨hx, h⟩
    · exact Or.inr ⟨hx, h⟩
  have hJout : {x : G | orderOf x = 2 ∧ x ∉ C.D.M}.ncard ≤ 21 * C.D.M.index :=
    A7SI.InvolutionsSdiff C.D.M hf6
  have hHindex_le : B.H.index ≤ R + 21 * C.D.M.index := by
    have h1 : B.H.index ≤ {x : G | orderOf x = 2 ∧ x ∈ C.D.M}.ncard +
        {x : G | orderOf x = 2 ∧ x ∉ C.D.M}.ncard := le_trans hJH hJle
    rw [hJMin] at h1
    omega
  -- ## 8. The arithmetic
  have hmain : R * C.D.M.index ≤ 3 * R + 63 * C.D.M.index := by
    calc R * C.D.M.index = 3 * B.H.index := hkey.symm
      _ ≤ 3 * (R + 21 * C.D.M.index) := Nat.mul_le_mul_left 3 hHindex_le
      _ = 3 * R + 63 * C.D.M.index := by ring
  have hi7 : C.D.M.index ≤ 7 := by
    by_cases h : C.D.M.index ≤ 3
    · omega
    · have h3i : 3 ≤ C.D.M.index := by omega
      have hsub : (C.D.M.index - 3) * R ≤ 63 * C.D.M.index := by
        have h2 : C.D.M.index * R - 3 * R ≤ 63 * C.D.M.index := by
          have h3 := Nat.sub_le_sub_right hmain (3 * R)
          rw [Nat.add_sub_cancel_left] at h3
          rwa [← mul_comm C.D.M.index R] at h3
        rwa [← Nat.sub_mul] at h2
      have h4 : 105 * (C.D.M.index - 3) ≤ 63 * C.D.M.index := by
        calc 105 * (C.D.M.index - 3) = (C.D.M.index - 3) * 105 := Nat.mul_comm _ _
          _ ≤ (C.D.M.index - 3) * R := Nat.mul_le_mul_left _ hR
          _ ≤ 63 * C.D.M.index := hsub
      have h5 : 105 * (C.D.M.index - 3) = 105 * C.D.M.index - 315 := by
        rw [Nat.mul_sub_left_distrib]
      have h6 : 105 * C.D.M.index - 315 ≤ 63 * C.D.M.index := by
        rw [← h5]; exact h4
      omega
  -- ## 9. `7 ∣ |M|`
  refine ⟨hi7, ?_⟩
  obtain ⟨e⟩ := hA7
  have hEcard : Nat.card ↥(Work.GW2.layerIn C.D.M) =
      2520 * Nat.card (Subgroup.center ↥(Work.GW2.layerIn C.D.M)) := by
    have h := Subgroup.card_eq_card_quotient_mul_card_subgroup
      (Subgroup.center ↥(Work.GW2.layerIn C.D.M))
    rw [h, Nat.card_congr e.toEquiv, I.toolkit.a7.1]
  have h7E : 7 ∣ Nat.card ↥(Work.GW2.layerIn C.D.M) := by
    rw [hEcard]
    exact dvd_mul_of_dvd_left (by norm_num : (7 : ℕ) ∣ 2520) _
  exact dvd_trans h7E (Subgroup.card_dvd_of_le (Work.CORE4.layerIn_le C.D.M))

end Work.CORE4
