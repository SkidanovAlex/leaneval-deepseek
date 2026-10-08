import Mathlib
import Submission.Work.ThreePoints.ThmC.Defs
import Submission.Work.ThreePoints.ThmC.Base
import Submission.Work.ThreePoints.ThmC.closure_pairwise_commuting_involutions
import Submission.Work.ThreePoints.TwoPointTransitive
import Submission.Work.BrauerSuzuki.OddCore.oddCard_oddCore
import Submission.Work.Fitting.piCore_isPiNat
import Submission.Work.PGroup.ZJ_map_of_ker_inf_eq_bot
import Submission.Work.GlaubermanZJ.ZJ_eq
import Submission.Work.GlaubermanZJ.pPrimeCore_eq_fitting

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option maxHeartbeats 1000000

namespace Work.ThreePoints.ThmC

open LeanEval.GroupTheory.Defs

/-! ## Auxiliary lemmas -/

/-- Conjugation intertwines with the image of a subgroup under a homomorphism. -/
theorem map_conj_eq_conj_map {G H : Type*} [Group G] [Group H] (f : G →* H) (g : G)
    (A : Subgroup G) :
    (A.map (MulAut.conj g).toMonoidHom).map f =
      (A.map f).map (MulAut.conj (f g)).toMonoidHom := by
  have h : f.comp (MulAut.conj g).toMonoidHom = (MulAut.conj (f g)).toMonoidHom.comp f := by
    ext x
    simp [MulAut.conj_apply]
  rw [Subgroup.map_map, Subgroup.map_map, h]

/-- If `N` is a normal subgroup of a finite group `G` meeting `K` trivially, then `|N|` divides
the index `[G : K]`. -/
theorem card_dvd_index_of_normal_inf_eq_bot {G : Type*} [Group G] [Finite G]
    (N K : Subgroup G) [N.Normal] (h : N ⊓ K = ⊥) : Nat.card ↥N ∣ K.index := by
  have hsub : N.subgroupOf K = ⊥ := by
    rw [eq_bot_iff]
    intro z hz
    rw [Subgroup.mem_bot]
    have hz1 : (z : G) ∈ N ⊓ K := ⟨Subgroup.mem_subgroupOf.mp hz, z.2⟩
    rw [h, Subgroup.mem_bot] at hz1
    exact Subtype.ext hz1
  have hidx : (N.subgroupOf (K ⊔ N)).index = Nat.card ↥K := by
    have hs := Subgroup.relIndex_sup_right K N
    rw [Subgroup.relIndex, Subgroup.relIndex] at hs
    rw [hs, hsub, Subgroup.index_bot]
  have hcard : Nat.card ↥(K ⊔ N) = Nat.card ↥N * Nat.card ↥K := by
    have h3 := Subgroup.card_mul_index (N.subgroupOf (K ⊔ N))
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe le_sup_right).toEquiv, hidx] at h3
    exact h3.symm
  have hdvd : Nat.card ↥N * Nat.card ↥K ∣ Nat.card G := by
    have h := Subgroup.card_dvd_of_le (le_top : (K ⊔ N : Subgroup G) ≤ ⊤)
    rw [Nat.card_congr Subgroup.topEquiv.toEquiv, hcard] at h
    exact h
  rw [mul_comm (Nat.card ↥N) (Nat.card ↥K), ← Subgroup.card_mul_index K] at hdvd
  exact (Nat.mul_dvd_mul_iff_left Nat.card_pos).mp hdvd

/-- A maximal `p`-subgroup of `D` (in the sense of `IsSylowOf`) has `p`-coprime index in `D`. -/
theorem not_dvd_index_of_isSylowOf {G : Type} [Group G] [Finite G] {p : ℕ} (hp : p.Prime)
    {R D : Subgroup G} (hR : Work.ThreePoints.ThmC.IsSylowOf p R D) :
    ¬ p ∣ (R.subgroupOf D).index := by
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨T, hTle⟩ :=
    (hR.2.1.of_equiv (Subgroup.subgroupOfEquivOfLe hR.1).symm).exists_le_sylow
  have hRle : R ≤ (T : Subgroup ↥D).map D.subtype := by
    have h1 : (R.subgroupOf D).map D.subtype ≤ (T : Subgroup ↥D).map D.subtype :=
      Subgroup.map_mono hTle
    rwa [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hR.1] at h1
  have hleD : (T : Subgroup ↥D).map D.subtype ≤ D := by
    rintro y ⟨t, ht, rfl⟩
    exact t.2
  have hpg : IsPGroup p ((T : Subgroup ↥D).map D.subtype) :=
    (T.isPGroup').of_equiv (Subgroup.equivMapOfInjective (T : Subgroup ↥D) D.subtype
      D.subtype_injective)
  have hTeq : (T : Subgroup ↥D) = R.subgroupOf D := by
    have hRT := hR.2.2 _ hRle hleD hpg
    ext z
    constructor
    · intro hz
      have h1 : (z : G) ∈ (T : Subgroup ↥D).map D.subtype := Subgroup.mem_map_of_mem _ hz
      rw [hRT] at h1
      exact h1
    · intro hz
      have h1 : (z : G) ∈ R := Subgroup.mem_subgroupOf.mp hz
      rw [← hRT] at h1
      obtain ⟨w, hw, hwz⟩ := Subgroup.mem_map.mp h1
      have hwz' : w = z := Subtype.ext hwz
      rwa [hwz'] at hw
  simpa only [hTeq] using T.not_dvd_index

/-- Let `G` be a finite group, `N ⊴ G` of odd order and `M ⊴ G` with `N ≤ M`, `M` of odd index in
`G`, such that every square of an element of `M` lies in `N` (i.e. `M/N` has exponent `2`).  Then
every Sylow `2`-subgroup of `G` is abelian (elementwise form, which is
`Submission.Blueprint.IsAbelianSubgroup`). -/
theorem sylow_two_isAbelian_of_normal_odd_exponent_two {G : Type*} [Group G] [Finite G]
    {N M : Subgroup G} (hN : N.Normal) (hNM : N ≤ M) (hM : M.Normal)
    (hodd : Odd (Nat.card ↥N)) (hidx : Odd M.index)
    (hexp : ∀ x ∈ M, x * x ∈ N) :
    ∀ S : Sylow 2 G, ∀ x ∈ (S : Subgroup G), ∀ y ∈ (S : Subgroup G), x * y = y * x := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro S x hx y hy
  -- `S ⊓ N = ⊥`
  have hSN : (S : Subgroup G) ⊓ N = ⊥ := by
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp (S.isPGroup' : IsPGroup 2 (S : Subgroup G))
    have hcop : Nat.Coprime (Nat.card ↥(S : Subgroup G)) (Nat.card ↥N) := by
      rw [hk]
      refine Nat.Coprime.pow_left k ?_
      exact (Nat.prime_two.coprime_iff_not_dvd).mpr
        (fun hdiv => Nat.not_even_iff_odd.mpr hodd (even_iff_two_dvd.mpr hdiv))
    rw [eq_bot_iff]
    intro z hz
    obtain ⟨hzS, hzN⟩ := Subgroup.mem_inf.mp hz
    rw [Subgroup.mem_bot]
    have h1 : orderOf z ∣ Nat.card ↥(S : Subgroup G) := by
      have h := orderOf_dvd_natCard (⟨z, hzS⟩ : ↥(S : Subgroup G))
      rwa [Subgroup.orderOf_mk] at h
    have h2 : orderOf z ∣ Nat.card ↥N := by
      have h := orderOf_dvd_natCard (⟨z, hzN⟩ : ↥N)
      rwa [Subgroup.orderOf_mk] at h
    exact orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes hcop h1 h2)
  -- `M.map (mk' N)` is a normal `2`-subgroup of `G ⧸ N`
  have hNmap_pg : IsPGroup 2 (M.map (QuotientGroup.mk' N)) := by
    rw [isPGroup_iff_orderOf_dvd_pow]
    rintro ⟨z, hz⟩
    obtain ⟨y, hy, hyz⟩ := Subgroup.mem_map.mp hz
    refine ⟨1, ?_⟩
    rw [pow_one, orderOf_dvd_iff_pow_eq_one, pow_two]
    apply Subtype.ext
    have h2 : (QuotientGroup.mk' N) (y * y) = 1 :=
      (QuotientGroup.eq_one_iff (y * y)).mpr (hexp y hy)
    calc (z : G ⧸ N) * (z : G ⧸ N)
        = (QuotientGroup.mk' N) y * (QuotientGroup.mk' N) y := by rw [hyz]
      _ = (QuotientGroup.mk' N) (y * y) := (map_mul (QuotientGroup.mk' N) y y).symm
      _ = 1 := h2
  have hNmap_normal : (M.map (QuotientGroup.mk' N)).Normal :=
    hM.map _ (QuotientGroup.mk'_surjective N)
  have hmap_le : M.map (QuotientGroup.mk' N) ≤ (S : Subgroup G).map (QuotientGroup.mk' N) := by
    have h := IsPGroup.le_sylow_of_normal (p := 2) hNmap_pg
      (S.mapSurjective (QuotientGroup.mk'_surjective N))
    rwa [Sylow.coe_mapSurjective] at h
  -- the orders of `S` and of `M.map (mk' N)` agree
  have hSmap_card : Nat.card ↥((S : Subgroup G).map (QuotientGroup.mk' N)) =
      Nat.card ↥(S : Subgroup G) := by
    have hsub : N.subgroupOf (S : Subgroup G) = ⊥ := by
      rw [eq_bot_iff]
      intro z hz
      rw [Subgroup.mem_bot]
      have hz1 : (z : G) ∈ (S : Subgroup G) ⊓ N := ⟨z.2, Subgroup.mem_subgroupOf.mp hz⟩
      rw [hSN, Subgroup.mem_bot] at hz1
      exact Subtype.ext hz1
    have h := Subgroup.relIndex_ker (S : Subgroup G) (QuotientGroup.mk' N)
    rw [QuotientGroup.ker_mk', Subgroup.relIndex, hsub, Subgroup.index_bot] at h
    exact h.symm
  have hcardM : Nat.card ↥M = Nat.card ↥N * Nat.card ↥(M.map (QuotientGroup.mk' N)) := by
    have h1 : Nat.card ↥(N.subgroupOf M) = Nat.card ↥N :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hNM).toEquiv
    have h2 : (N.subgroupOf M).index = Nat.card ↥(M.map (QuotientGroup.mk' N)) := by
      have h := Subgroup.relIndex_ker M (QuotientGroup.mk' N)
      rw [QuotientGroup.ker_mk'] at h
      exact h
    have h3 := Subgroup.card_mul_index (N.subgroupOf M)
    rw [h1, h2] at h3
    exact h3.symm
  have hdvd_le : Nat.card ↥(M.map (QuotientGroup.mk' N)) ∣ Nat.card ↥(S : Subgroup G) := by
    rw [← hSmap_card]
    exact Subgroup.card_dvd_of_le hmap_le
  have hcop_idx : Nat.Coprime (Nat.card ↥(S : Subgroup G)) M.index := by
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp (S.isPGroup' : IsPGroup 2 (S : Subgroup G))
    rw [hk]
    refine Nat.Coprime.pow_left k ?_
    exact (Nat.prime_two.coprime_iff_not_dvd).mpr
      (fun hdiv => Nat.not_even_iff_odd.mpr hidx (even_iff_two_dvd.mpr hdiv))
  have hcop_N : Nat.Coprime (Nat.card ↥(S : Subgroup G)) (Nat.card ↥N) := by
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp (S.isPGroup' : IsPGroup 2 (S : Subgroup G))
    rw [hk]
    refine Nat.Coprime.pow_left k ?_
    exact (Nat.prime_two.coprime_iff_not_dvd).mpr
      (fun hdiv => Nat.not_even_iff_odd.mpr hodd (even_iff_two_dvd.mpr hdiv))
  have hdvd1 : Nat.card ↥(S : Subgroup G) ∣ Nat.card ↥M := by
    have h : Nat.card ↥(S : Subgroup G) ∣ Nat.card ↥M * M.index := by
      have h0 := Subgroup.card_dvd_of_le (le_top : (S : Subgroup G) ≤ ⊤)
      rw [Nat.card_congr Subgroup.topEquiv.toEquiv, ← Subgroup.card_mul_index M] at h0
      exact h0
    exact hcop_idx.dvd_of_dvd_mul_right h
  have hdvd2 : Nat.card ↥(S : Subgroup G) ∣ Nat.card ↥(M.map (QuotientGroup.mk' N)) := by
    rw [hcardM, mul_comm (Nat.card ↥N)
      (Nat.card ↥(M.map (QuotientGroup.mk' N)))] at hdvd1
    exact hcop_N.dvd_of_dvd_mul_right hdvd1
  have hcard_eq : Nat.card ↥(M.map (QuotientGroup.mk' N)) = Nat.card ↥(S : Subgroup G) :=
    le_antisymm (Nat.le_of_dvd Nat.card_pos hdvd_le) (Nat.le_of_dvd Nat.card_pos hdvd2)
  have hmap_eq : M.map (QuotientGroup.mk' N) = (S : Subgroup G).map (QuotientGroup.mk' N) :=
    Subgroup.eq_of_le_of_card_ge hmap_le (le_of_eq (hSmap_card.trans hcard_eq.symm))
  have hcardSN : Nat.card ↥((S : Subgroup G) ⊔ N) =
      Nat.card ↥N * Nat.card ↥(S : Subgroup G) := by
    have hNS_index : (N.subgroupOf (S : Subgroup G)).index = Nat.card ↥(S : Subgroup G) := by
      have h := Subgroup.relIndex_ker (S : Subgroup G) (QuotientGroup.mk' N)
      rw [QuotientGroup.ker_mk'] at h
      rw [← hSmap_card, ← h]
      rfl
    have h1 : Nat.card ↥(N.subgroupOf ((S : Subgroup G) ⊔ N)) = Nat.card ↥N :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe le_sup_right).toEquiv
    have h2 : (N.subgroupOf ((S : Subgroup G) ⊔ N)).index = Nat.card ↥(S : Subgroup G) := by
      have hs := Subgroup.relIndex_sup_right (S : Subgroup G) N
      rw [Subgroup.relIndex, Subgroup.relIndex] at hs
      rw [hs]
      exact hNS_index
    have h3 := Subgroup.card_mul_index (N.subgroupOf ((S : Subgroup G) ⊔ N))
    rw [h1, h2] at h3
    exact h3.symm
  have hMS : M ≤ (S : Subgroup G) ⊔ N := by
    have h : M ≤ ((S : Subgroup G).map (QuotientGroup.mk' N)).comap (QuotientGroup.mk' N) :=
      (Subgroup.map_le_iff_le_comap (f := QuotientGroup.mk' N)).mp (le_of_eq hmap_eq)
    rw [Subgroup.comap_map_eq, QuotientGroup.ker_mk'] at h
    exact h
  have hcardM_le : Nat.card ↥((S : Subgroup G) ⊔ N) ≤ Nat.card ↥M := by
    have hcalc : Nat.card ↥((S : Subgroup G) ⊔ N) = Nat.card ↥M := by
      calc Nat.card ↥((S : Subgroup G) ⊔ N) = Nat.card ↥N * Nat.card ↥(S : Subgroup G) := hcardSN
        _ = Nat.card ↥N * Nat.card ↥(M.map (QuotientGroup.mk' N)) := by rw [hcard_eq]
        _ = Nat.card ↥M := hcardM.symm
    exact le_of_eq hcalc
  have hMS_eq : M = (S : Subgroup G) ⊔ N := Subgroup.eq_of_le_of_card_ge hMS hcardM_le
  have hS_le_M : (S : Subgroup G) ≤ M := hMS_eq ▸ le_sup_left
  -- conclude
  have hcomm : (QuotientGroup.mk' N) x * (QuotientGroup.mk' N) y =
      (QuotientGroup.mk' N) y * (QuotientGroup.mk' N) x := by
    have hsq : ∀ z ∈ M.map (QuotientGroup.mk' N), z * z = 1 := by
      rintro z hz
      obtain ⟨w, hw, hwz⟩ := Subgroup.mem_map.mp hz
      have h2 : (QuotientGroup.mk' N) (w * w) = 1 :=
        (QuotientGroup.eq_one_iff (w * w)).mpr (hexp w hw)
      rw [← hwz, ← map_mul]
      exact h2
    have ha : (QuotientGroup.mk' N) x ∈ M.map (QuotientGroup.mk' N) :=
      Subgroup.mem_map_of_mem _ (hS_le_M hx)
    have hb : (QuotientGroup.mk' N) y ∈ M.map (QuotientGroup.mk' N) :=
      Subgroup.mem_map_of_mem _ (hS_le_M hy)
    have h1 : ((QuotientGroup.mk' N) x * (QuotientGroup.mk' N) y) *
        ((QuotientGroup.mk' N) x * (QuotientGroup.mk' N) y) = 1 := hsq _ (mul_mem ha hb)
    have h2 : (QuotientGroup.mk' N) x * (QuotientGroup.mk' N) x = 1 := hsq _ ha
    have h3 : (QuotientGroup.mk' N) y * (QuotientGroup.mk' N) y = 1 := hsq _ hb
    have h4 : ((QuotientGroup.mk' N) x * (QuotientGroup.mk' N) y)⁻¹ =
        (QuotientGroup.mk' N) x * (QuotientGroup.mk' N) y := inv_eq_of_mul_eq_one_right h1
    have h5 : ((QuotientGroup.mk' N) x * (QuotientGroup.mk' N) y)⁻¹ =
        (QuotientGroup.mk' N) y * (QuotientGroup.mk' N) x := by
      rw [mul_inv_rev, inv_eq_of_mul_eq_one_right h3, inv_eq_of_mul_eq_one_right h2]
    exact h4.symm.trans h5
  have hmem : x * y * (y * x)⁻¹ ∈ (S : Subgroup G) ⊓ N := by
    refine ⟨?_, ?_⟩
    · exact (S : Subgroup G).mul_mem ((S : Subgroup G).mul_mem hx hy)
        ((S : Subgroup G).inv_mem ((S : Subgroup G).mul_mem hy hx))
    · have h2 : (QuotientGroup.mk' N) (y * x) = (QuotientGroup.mk' N) (x * y) := by
        rw [map_mul, map_mul]
        exact hcomm.symm
      have hconv : (QuotientGroup.mk' N) (x * y * (y * x)⁻¹) =
          (QuotientGroup.mk' N) x * (QuotientGroup.mk' N) y *
            ((QuotientGroup.mk' N) y * (QuotientGroup.mk' N) x)⁻¹ := by
        simp only [map_mul, map_inv]
      have h3 : (QuotientGroup.mk' N) (x * y * (y * x)⁻¹) = 1 := by
        rw [hconv, hcomm]
        exact mul_inv_cancel _
      exact (QuotientGroup.eq_one_iff (x * y * (y * x)⁻¹)).mp h3
  rw [hSN, Subgroup.mem_bot] at hmem
  exact mul_inv_eq_one.mp hmem

/-- Two equal subgroups have isomorphic underlying groups. -/
noncomputable def subgroupCongrMulEquiv {G : Type*} [Group G] {H K : Subgroup G} (h : H = K) :
    ↥H ≃* ↥K where
  toFun x := ⟨x.1, h ▸ x.2⟩
  invFun x := ⟨x.1, h.symm ▸ x.2⟩
  left_inv x := Subtype.ext rfl
  right_inv x := Subtype.ext rfl
  map_mul' x y := rfl

/-- **Peterfalvi I Ch. II §2, third numbered item (pp. 165–166).**  Let `F` be a finite group of
2-rank `≥ 2` (`HasFourGroup F`) with a proper Bender group `H` (`IsStronglyEmbedded`), suppose the
involutions of `H` commute modulo `O_{2'}(F)` (the hypothesis `hcomm`, supplied in the application
by **(B1-a)**, i.e. by `Work.ThreePoints.involutions_commute_of_below`), let `t ∈ Inv(F∖H)`,
`D = H ∩ H^t`, `p` an odd prime and `R` a `p`-Sylow of `D`.  If `O_{p'}(D) = 1` and `D` has a
`p`-subgroup normalised but not centralised by an involution of `H`, then every involution of `H`
normalises `A(R) = ZJ R`.

(`hFT`/`hZJ` are consumed for the solvability of `ED` and for Glauberman's ZJ result; `ZJ R` is
`Submission.Blueprint.ZJ`, i.e. `Z(J(R))`.  Source sketch: `E = ⟨Inv H⟩` has `O_{2'}(F) ≤ D`,
`ED/D` of 2-power order with `ED/O_{2'}(F)` elementary abelian, hence `ED` is solvable with abelian
Sylow 2-subgroups and no `SL(2,p)` section; `R` is a `p`-Sylow of `ED` and `O_{p'}(ED) = 1` (else
`Inv(H) ⊆ O_{p'}(ED)`, contradicting the hypothesis), so Glauberman's ZJ result applied to `ED`
makes `A(R)` normal in `ED`.) -/
theorem ch2_sec2_lem3 {F : Type} [Group F] [Finite F]
    (hFT : Submission.Blueprint.FeitThompsonProp) (hZJ : Submission.Blueprint.GlaubermanZJProp)
    (hfour : Submission.Blueprint.HasFourGroup F) {H : Subgroup F}
    (hH : LeanEval.GroupTheory.Defs.IsStronglyEmbedded H)
    (hcomm : ∀ u v : F, u ∈ Submission.Blueprint.involutions (H : Set F) →
      v ∈ Submission.Blueprint.involutions (H : Set F) →
      u * v * u⁻¹ * v⁻¹ ∈ Submission.Blueprint.oddCore F)
    {t : F} (ht : orderOf t = 2) (htH : t ∉ H) {p : ℕ} (hp : p.Prime) (hpodd : p ≠ 2)
    {R : Subgroup F} (hR : Work.ThreePoints.ThmC.IsSylowOf p R (Submission.Blueprint.twoPoint H t))
    (hOp' : Submission.Blueprint.pPrimeCore p (Submission.Blueprint.twoPoint H t) = ⊥)
    (hP : ∃ Q : Subgroup F, Q ≤ Submission.Blueprint.twoPoint H t ∧ IsPGroup p Q ∧
      ∃ u ∈ Submission.Blueprint.involutions (H : Set F),
        u ∈ Subgroup.normalizer (Q : Set F) ∧ ¬ ∀ x ∈ Q, u * x = x * u) :
    Submission.Blueprint.involutions (H : Set F) ⊆
      (Subgroup.normalizer (Submission.Blueprint.ZJ R : Set F) : Set F) := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro u hu
  -- ## Set-up
  let O : Subgroup F := Submission.Blueprint.oddCore F
  let D : Subgroup F := Submission.Blueprint.twoPoint H t
  let E : Subgroup F := Subgroup.closure (Submission.Blueprint.involutions (H : Set F))
  let M : Subgroup F := E ⊔ O
  let ED : Subgroup F := E ⊔ D
  have hD_le_H : D ≤ H := inf_le_left
  have hE_le_H : E ≤ H := (Subgroup.closure_le H).mpr fun x hx => hx.1
  have hED_le_H : ED ≤ H := sup_le hE_le_H hD_le_H
  have hD_odd : Odd (Nat.card ↥D) := IsStronglyEmbedded.odd_card_inf_conj hH htH
  have hO_le_H : O ≤ H := Work.ThreePoints.oddCore_le_of_stronglyEmbedded hH hfour
  have hO_le_conj : O ≤ Submission.Blueprint.conj t H := by
    show Submission.Blueprint.oddCore F ≤ Submission.Blueprint.conj t H
    rw [Work.ThreePoints.ThmC.oddCore_eq_iInf_conj hH hfour]
    exact iInf_le _ t
  have hO_le_D : O ≤ D := le_inf hO_le_H hO_le_conj
  have hO_le_ED : O ≤ ED := le_trans hO_le_D le_sup_right
  have hM_le_ED : M ≤ ED := sup_le le_sup_left (le_trans hO_le_D le_sup_right)
  have hE_le_ED : E ≤ ED := le_sup_left
  have hR_le_ED : R ≤ ED := le_trans hR.1 le_sup_right
  -- ## Conjugation action on `E` and on `M`
  have hE_conj_le : ∀ g ∈ H, E.map (MulAut.conj g).toMonoidHom ≤ E := by
    intro g hg
    show Subgroup.map (MulAut.conj g).toMonoidHom
      (Subgroup.closure (Submission.Blueprint.involutions (H : Set F))) ≤
      Subgroup.closure (Submission.Blueprint.involutions (H : Set F))
    rw [MonoidHom.map_closure]
    refine Subgroup.closure_mono ?_
    rintro x ⟨y, ⟨hyH, hy2⟩, hyx⟩
    refine ⟨?_, ?_⟩
    · rw [← hyx]
      exact H.mul_mem (H.mul_mem hg hyH) (H.inv_mem hg)
    · rw [← hyx]
      show orderOf ((MulAut.conj g) y) = 2
      rw [(MulAut.conj g).orderOf_eq y]
      exact hy2
  have hE_conj : ∀ g ∈ H, E.map (MulAut.conj g).toMonoidHom = E := by
    intro g hg
    refine le_antisymm (hE_conj_le g hg) ?_
    intro x hx
    have h1 : (MulAut.conj g⁻¹) x ∈ E.map (MulAut.conj g⁻¹).toMonoidHom :=
      Subgroup.mem_map.mpr ⟨x, hx, rfl⟩
    have h2 : (MulAut.conj g⁻¹) x ∈ E := hE_conj_le g⁻¹ (H.inv_mem hg) h1
    have h3 : x = (MulAut.conj g) ((MulAut.conj g⁻¹) x) := by
      rw [MulAut.conj_apply, MulAut.conj_apply]
      group
    rw [h3]
    exact Subgroup.mem_map.mpr ⟨_, h2, rfl⟩
  have hE_normal_ED : ∀ g ∈ ED, E.map (MulAut.conj g).toMonoidHom = E :=
    fun g hg => hE_conj g (hED_le_H hg)
  have hM_norm : ∀ g ∈ ED, M.map (MulAut.conj g).toMonoidHom = M := by
    intro g hg
    show (E ⊔ O).map (MulAut.conj g).toMonoidHom = E ⊔ O
    rw [Subgroup.map_sup]
    rw [hE_normal_ED g hg]
    rw [show Subgroup.map (MulAut.conj g).toMonoidHom O = O from Subgroup.Normal.map_conj_eq O g]
  -- ## `(E ⊔ O)/O` is elementary abelian
  have hOm : O.map (QuotientGroup.mk' O) = ⊥ := by
    rw [eq_bot_iff]
    rintro x ⟨y, hy, rfl⟩
    show (QuotientGroup.mk' O) y = 1
    exact (QuotientGroup.eq_one_iff y).mpr hy
  have hEmap : E.map (QuotientGroup.mk' O) = (E ⊔ O).map (QuotientGroup.mk' O) := by
    rw [Subgroup.map_sup, hOm, sup_bot_eq]
  have hEbar : IsMulCommutative ↥((E ⊔ O).map (QuotientGroup.mk' O)) ∧
      (∀ x : ↥((E ⊔ O).map (QuotientGroup.mk' O)), x ^ 2 = 1) ∧
      IsPGroup 2 ↥((E ⊔ O).map (QuotientGroup.mk' O)) := by
    have hcl : (E ⊔ O).map (QuotientGroup.mk' O) =
        Subgroup.closure ((QuotientGroup.mk' O) ''
          (Submission.Blueprint.involutions (H : Set F))) := by
      show Subgroup.map (QuotientGroup.mk' O)
          (Subgroup.closure (Submission.Blueprint.involutions (H : Set F)) ⊔ O) = _
      rw [Subgroup.map_sup, MonoidHom.map_closure, hOm, sup_bot_eq]
    refine hcl ▸ closure_pairwise_commuting_involutions (G := F ⧸ O) ?_ ?_
    · rintro x ⟨y, ⟨hyH, hy2⟩, rfl⟩
      have hy : y * y = 1 := by rw [← pow_two, ← hy2]; exact pow_orderOf_eq_one y
      rw [← map_mul]
      refine (QuotientGroup.eq_one_iff _).mpr ?_
      rw [hy]
      exact O.one_mem
    · rintro x ⟨a, ⟨haH, ha2⟩, rfl⟩ y ⟨b, ⟨hbH, hb2⟩, rfl⟩
      have h5 : (a * b) * (b * a)⁻¹ ∈ O := by
        rw [show (a * b) * (b * a)⁻¹ = a * b * a⁻¹ * b⁻¹ from by group]
        exact hcomm a b ⟨haH, ha2⟩ ⟨hbH, hb2⟩
      have h6 : (QuotientGroup.mk' O) ((a * b) * (b * a)⁻¹) = 1 :=
        (QuotientGroup.eq_one_iff _).mpr h5
      have h7 : (QuotientGroup.mk' O) (a * b) * ((QuotientGroup.mk' O) (b * a))⁻¹ =
          (QuotientGroup.mk' O) ((a * b) * (b * a)⁻¹) := by
        rw [map_mul (QuotientGroup.mk' O) (a * b) ((b * a)⁻¹)]
        rw [map_inv (QuotientGroup.mk' O) (b * a)]
      have h8 : (QuotientGroup.mk' O) (a * b) * ((QuotientGroup.mk' O) (b * a))⁻¹ = 1 := by
        rw [h7, h6]
      have h2' : (QuotientGroup.mk' O) (a * b) = (QuotientGroup.mk' O) (b * a) :=
        mul_inv_eq_one.mp h8
      rw [← map_mul, ← map_mul]
      exact h2'
  have hEbar_comm : IsMulCommutative ↥(E.map (QuotientGroup.mk' O)) := hEmap ▸ hEbar.1
  have hEbar_pg : IsPGroup 2 ((E ⊔ O).map (QuotientGroup.mk' O)) := hEbar.2.2
  have hEbar_two : ∀ x : ↥((E ⊔ O).map (QuotientGroup.mk' O)), x ^ 2 = 1 := hEbar.2.1
  -- ## squares of `M` land in `O`
  have hM_sq : ∀ x ∈ M, x * x ∈ O := by
    intro x hx
    have hx' : (QuotientGroup.mk' O) x ∈ (E ⊔ O).map (QuotientGroup.mk' O) :=
      Subgroup.mem_map_of_mem _ hx
    have h2 : (⟨(QuotientGroup.mk' O) x, hx'⟩ :
        ↥((E ⊔ O).map (QuotientGroup.mk' O))) ^ 2 = 1 := hEbar_two ⟨_, hx'⟩
    have h3 : ((QuotientGroup.mk' O) x) ^ 2 = 1 := congrArg Subtype.val h2
    rw [pow_two] at h3
    have h4 : (QuotientGroup.mk' O) (x * x) = 1 := by rw [map_mul]; exact h3
    exact (QuotientGroup.eq_one_iff (x * x)).mp h4
  -- ## `|ED : D|` is a power of `2`
  have hD_norm_E : D ≤ Subgroup.normalizer (E : Set F) := by
    intro d hd
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    exact hE_conj d (hD_le_H hd)
  have hErel : E.relIndex D = E.relIndex ED := by
    letI := Subgroup.normal_subgroupOf_of_le_normalizer (H := D) (N := E) hD_norm_E
    letI := Subgroup.normal_subgroupOf_sup_of_le_normalizer (H := D) (N := E) hD_norm_E
    have h1 : E.relIndex D = E.relIndex (D ⊔ E) :=
      Nat.card_congr (QuotientGroup.quotientInfEquivProdNormalizerQuotient (H := D) (N := E)
        hD_norm_E).toEquiv
    rw [show D ⊔ E = ED from (sup_comm E D).symm] at h1
    exact h1
  have hmul1 : E.relIndex ED * D.relIndex ED = (E ⊓ D).relIndex ED := by
    have h := Subgroup.relIndex_mul_relIndex (E ⊓ D) D ED inf_le_right le_sup_right
    rwa [Subgroup.inf_relIndex_right, hErel] at h
  have hmul2 : D.relIndex E * E.relIndex ED = (E ⊓ D).relIndex ED := by
    have h := Subgroup.relIndex_mul_relIndex (E ⊓ D) E ED inf_le_left le_sup_left
    rwa [Subgroup.inf_relIndex_left] at h
  have hDrel : D.relIndex ED = D.relIndex E := by
    have h1 : E.relIndex ED * D.relIndex ED = E.relIndex ED * D.relIndex E := by
      rw [hmul1, mul_comm (E.relIndex ED) (D.relIndex E), ← hmul2]
    exact Nat.mul_left_cancel (show 0 < E.relIndex ED from
      Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite) h1
  have hErel_O : (E ⊓ O).relIndex E = Nat.card ↥((E ⊔ O).map (QuotientGroup.mk' O)) := by
    have h := Subgroup.relIndex_ker E (QuotientGroup.mk' O)
    rw [QuotientGroup.ker_mk'] at h
    rw [← Subgroup.inf_relIndex_left E O] at h
    rw [h, hEmap]
  have hdvd : D.relIndex ED ∣ Nat.card ↥((E ⊔ O).map (QuotientGroup.mk' O)) := by
    have h1 : D.relIndex E ∣ (E ⊓ O).relIndex E := by
      have h := Subgroup.relIndex_dvd_of_le_left E (inf_le_inf_left E hO_le_D)
      rw [Subgroup.inf_relIndex_left] at h
      exact h
    rw [hDrel, ← hErel_O]
    exact h1
  obtain ⟨m, hm⟩ := IsPGroup.iff_card.mp hEbar_pg
  have hpow : ∃ k, D.relIndex ED = 2 ^ k := by
    obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp (hm ▸ hdvd)
    exact ⟨k, hk⟩
  have hDidx_nvd : ¬ p ∣ (D.subgroupOf ED).index := by
    obtain ⟨k, hk⟩ := hpow
    show ¬ p ∣ D.relIndex ED
    rw [hk]
    intro hdiv
    exact hpodd (((Nat.dvd_prime Nat.prime_two).mp (hp.dvd_of_dvd_pow hdiv)).resolve_left hp.ne_one)
  -- ## `ED/E·O` is odd
  have hM_index_odd : Odd ((M.subgroupOf ED).index) := by
    have hD_norm_M : D ≤ Subgroup.normalizer (M : Set F) :=
      fun d hd => Subgroup.mem_normalizer_iff_map_conj_eq.mpr
        (hM_norm d (Subgroup.mem_sup_right hd))
    letI := Subgroup.normal_subgroupOf_of_le_normalizer (H := D) (N := M) hD_norm_M
    letI := Subgroup.normal_subgroupOf_sup_of_le_normalizer (H := D) (N := M) hD_norm_M
    have h1 : (M.subgroupOf D).index = (M.subgroupOf (D ⊔ M)).index :=
      Nat.card_congr (QuotientGroup.quotientInfEquivProdNormalizerQuotient (H := D) (N := M)
        hD_norm_M).toEquiv
    rw [show D ⊔ M = ED from by
      show D ⊔ (E ⊔ O) = E ⊔ D
      rw [sup_comm E O, ← sup_assoc, show D ⊔ O = D from sup_eq_left.mpr hO_le_D, sup_comm]] at h1
    have hodd' : Odd ((M.subgroupOf D).index) :=
      Odd.of_dvd_nat hD_odd (Subgroup.index_dvd_card (M.subgroupOf D))
    rwa [h1] at hodd'
  -- ## `R` is a `p`-Sylow of `ED`
  have hRidx_nvd : ¬ p ∣ (R.subgroupOf ED).index := by
    have hmul : (R.subgroupOf ED).index = (R.subgroupOf D).index * (D.subgroupOf ED).index := by
      have h := Subgroup.relIndex_mul_relIndex R D ED hR.1 le_sup_right
      rw [Subgroup.relIndex, Subgroup.relIndex, Subgroup.relIndex] at h
      exact h.symm
    rw [hmul]
    exact hp.not_dvd_mul (not_dvd_index_of_isSylowOf hp hR) hDidx_nvd
  let P : Sylow p ↥ED :=
    (hR.2.1.of_equiv (Subgroup.subgroupOfEquivOfLe (hR.1.trans le_sup_right)).symm).toSylow
      hRidx_nvd
  have hPcoe : (P : Subgroup ↥ED) = R.subgroupOf ED := IsPGroup.toSylow_coe _ _
  -- ## `O_{p'}(ED) = 1`
  have hpCore_bot : Work.Fitting.pPrimeCore p ↥ED = ⊥ := by
    by_contra hne
    let N₀ : Subgroup F := (Work.Fitting.pPrimeCore p ↥ED).map ED.subtype
    haveI : (Work.Fitting.pPrimeCore p ↥ED).Normal := inferInstance
    have hN₀_conj : ∀ g ∈ ED, N₀.map (MulAut.conj g).toMonoidHom = N₀ := by
      intro g hg
      have hfix : (Work.Fitting.pPrimeCore p ↥ED).map
          (MulAut.conj (⟨g, hg⟩ : ↥ED)).toMonoidHom = Work.Fitting.pPrimeCore p ↥ED :=
        Subgroup.characteristic_iff_map_eq.mp
          (Work.Fitting.pPrimeCore_characteristic p ↥ED) _
      have h := map_conj_eq_conj_map (f := ED.subtype) (g := (⟨g, hg⟩ : ↥ED))
        (A := Work.Fitting.pPrimeCore p ↥ED)
      rw [hfix, show ED.subtype (⟨g, hg⟩ : ↥ED) = g from rfl] at h
      exact h.symm
    have hN₀D : N₀ ⊓ D = ⊥ := by
      have hXnormal : (N₀.subgroupOf D).Normal := by
        refine ⟨fun z hz g => ?_⟩
        rw [Subgroup.mem_subgroupOf] at hz ⊢
        have hmem := hN₀_conj (g : F) ((show D ≤ ED from le_sup_right) g.2)
        exact hmem ▸ Subgroup.mem_map.mpr ⟨_, hz, rfl⟩
      have hN₀_cop : Nat.Coprime (Nat.card ↥N₀) p := by
        have h1 : Nat.card ↥N₀ = Nat.card ↥(Work.Fitting.pPrimeCore p ↥ED) :=
          Subgroup.card_map_of_injective ED.subtype_injective
        rw [h1]
        exact (Work.GlaubermanZJ.isPiNat_ne_iff_coprime hp).mp
          (Work.Fitting.piCore_isPiNat ↥ED (fun q => q ≠ p))
      have hXcop : Nat.Coprime (Nat.card ↥(N₀.subgroupOf D)) p := by
        have h1 : Nat.card ↥(N₀.subgroupOf D) ∣ Nat.card ↥N₀ := by
          rw [← Subgroup.card_map_of_injective D.subtype_injective,
            Subgroup.subgroupOf_map_subtype]
          exact Subgroup.card_dvd_of_le inf_le_left
        exact Nat.Coprime.of_dvd_left h1 hN₀_cop
      have hle : N₀.subgroupOf D ≤ Submission.Blueprint.pPrimeCore p ↥D :=
        le_sSup ⟨hXnormal, hXcop⟩
      rw [hOp'] at hle
      rw [eq_bot_iff]
      intro z hz
      obtain ⟨hzN, hzD⟩ := Subgroup.mem_inf.mp hz
      rw [Subgroup.mem_bot]
      have hz' : (⟨z, hzD⟩ : ↥D) ∈ N₀.subgroupOf D := by
        rw [Subgroup.mem_subgroupOf]
        exact hzN
      have hzbot : (⟨z, hzD⟩ : ↥D) ∈ (⊥ : Subgroup ↥D) := hle hz'
      rw [Subgroup.mem_bot] at hzbot
      exact congrArg Subtype.val hzbot
    obtain ⟨j, hj⟩ : ∃ j, Nat.card ↥(Work.Fitting.pPrimeCore p ↥ED) = 2 ^ j := by
      obtain ⟨k, hk⟩ := hpow
      have h : Nat.card ↥(Work.Fitting.pPrimeCore p ↥ED) ∣ (D.subgroupOf ED).index :=
        card_dvd_index_of_normal_inf_eq_bot (Work.Fitting.pPrimeCore p ↥ED) (D.subgroupOf ED)
          (by
            rw [eq_bot_iff]
            intro z hz
            obtain ⟨hzN', hzD'⟩ := Subgroup.mem_inf.mp hz
            rw [Subgroup.mem_bot]
            have h1 : (z : F) ∈ N₀ := Subgroup.mem_map_of_mem ED.subtype hzN'
            have h2 : (z : F) ∈ D := Subgroup.mem_subgroupOf.mp hzD'
            have h3 : (z : F) ∈ N₀ ⊓ D := ⟨h1, h2⟩
            rw [hN₀D, Subgroup.mem_bot] at h3
            exact Subtype.ext h3)
      rw [show (D.subgroupOf ED).index = 2 ^ k from hk] at h
      obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp h
      exact ⟨j, hj⟩
    have h2dvd : 2 ∣ Nat.card ↥(Work.Fitting.pPrimeCore p ↥ED) := by
      cases j with
      | zero =>
        exact absurd ((Subgroup.one_lt_card_iff_ne_bot _).mpr hne)
          (hj.symm ▸ lt_irrefl (Nat.card ↥(Work.Fitting.pPrimeCore p ↥ED)))
      | succ j' =>
        exact hj ▸ (show 2 ∣ 2 ^ (j' + 1) from by
          rw [pow_succ]
          exact dvd_mul_left 2 (2 ^ j'))
    obtain ⟨z, hz2⟩ := exists_prime_orderOf_dvd_card' 2 h2dvd
    -- `Inv H ⊆ N₀`
    have hzinv : ((z : ↥ED) : F) ∈ Submission.Blueprint.involutions (H : Set F) := by
      refine ⟨hED_le_H (z : ↥ED).2, ?_⟩
      have h1 : orderOf z = orderOf (z : ↥ED) := Subgroup.orderOf_mk (z : ↥ED) z.2
      have h2 : orderOf (z : ↥ED) = orderOf ((z : ↥ED) : F) :=
        Subgroup.orderOf_mk ((z : ↥ED) : F) (z : ↥ED).2
      rw [← h2, ← h1, hz2]
    have hzN₀ : ((z : ↥ED) : F) ∈ N₀ := Subgroup.mem_map_of_mem ED.subtype z.2
    have hInv_sub : Submission.Blueprint.involutions (H : Set F) ⊆ (N₀ : Set F) := by
      intro y hy
      obtain ⟨d, hd, hdy⟩ :=
        Work.ThreePoints.twoPoint_transitive_on_involutions hH ht htH hzinv hy
      have hconj := hN₀_conj d ((show D ≤ ED from le_sup_right) hd)
      have h1 : (MulAut.conj d) ((z : ↥ED) : F) ∈ N₀ :=
        hconj ▸ Subgroup.mem_map.mpr ⟨_, hzN₀, rfl⟩
      rw [← hdy]
      exact h1
    obtain ⟨Q, hQD, hQpg, u', hu', hu'N, hu'nc⟩ := hP
    have hu'N₀ : u' ∈ N₀ := hInv_sub hu'
    refine hu'nc fun x hx => ?_
    have hxED : x ∈ ED := (show D ≤ ED from le_sup_right) (hQD hx)
    have hu'N' : Q.map (MulAut.conj u').toMonoidHom = Q :=
      Subgroup.mem_normalizer_iff_map_conj_eq.mp hu'N
    have hqu : u' * x * u'⁻¹ ∈ Q := by
      have h1 : (MulAut.conj u') x ∈ Q.map (MulAut.conj u').toMonoidHom :=
        Subgroup.mem_map.mpr ⟨x, hx, rfl⟩
      rw [hu'N'] at h1
      exact h1
    have hmemQ : u' * x * u'⁻¹ * x⁻¹ ∈ Q := Q.mul_mem hqu (Q.inv_mem hx)
    have hconjx : N₀.map (MulAut.conj x).toMonoidHom = N₀ := hN₀_conj x hxED
    have hxN : x * u'⁻¹ * x⁻¹ ∈ N₀ := by
      have h1 : (MulAut.conj x) u' ∈ N₀ := by
        have h2 : (MulAut.conj x) u' ∈ N₀.map (MulAut.conj x).toMonoidHom :=
          Subgroup.mem_map.mpr ⟨u', hu'N₀, rfl⟩
        rwa [hconjx] at h2
      have h3 : x * u'⁻¹ * x⁻¹ = ((MulAut.conj x) u')⁻¹ := by
        rw [MulAut.conj_apply]
        group
      rw [h3]
      exact N₀.inv_mem h1
    have hmemN : u' * x * u'⁻¹ * x⁻¹ ∈ N₀ := by
      rw [show u' * x * u'⁻¹ * x⁻¹ = u' * (x * u'⁻¹ * x⁻¹) from by group]
      exact N₀.mul_mem hu'N₀ hxN
    have hmemD : u' * x * u'⁻¹ * x⁻¹ ∈ D := hQD hmemQ
    have hbot : u' * x * u'⁻¹ * x⁻¹ ∈ (⊥ : Subgroup F) := by
      have h1 : u' * x * u'⁻¹ * x⁻¹ ∈ N₀ ⊓ D := ⟨hmemN, hmemD⟩
      rw [hN₀D, Subgroup.mem_bot] at h1
      exact h1
    rw [Subgroup.mem_bot] at hbot
    have h2 : u' * x * (x * u')⁻¹ = 1 := by
      rw [show u' * x * (x * u')⁻¹ = u' * x * u'⁻¹ * x⁻¹ from by group]
      exact hbot
    exact mul_inv_eq_one.mp h2
  -- ## `ED` is solvable
  have hsolv : Group.IsSolvable ↥ED := by
    haveI : (O.subgroupOf ED).Normal :=
      Subgroup.Normal.subgroupOf (Work.BrauerSuzuki.oddCore_normal F) ED
    haveI hN'solv : Group.IsSolvable ↥(O.subgroupOf ED) := by
      refine hFT ↥(O.subgroupOf ED) ?_
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hO_le_ED).toEquiv]
      exact Work.BrauerSuzuki.OddCore.oddCard_oddCore
    have hquot : Group.IsSolvable (↥ED ⧸ (O.subgroupOf ED)) := by
      have hleW : E.map (QuotientGroup.mk' O) ≤ (ED).map (QuotientGroup.mk' O) :=
        Subgroup.map_mono le_sup_left
      haveI hBnormal : ((E.map (QuotientGroup.mk' O)).subgroupOf
          ((ED).map (QuotientGroup.mk' O))).Normal := by
        rw [Subgroup.normal_subgroupOf_iff_le_normalizer hleW]
        intro w hw
        rw [Subgroup.mem_normalizer_iff_map_conj_eq]
        obtain ⟨g, hg, hgw⟩ := Subgroup.mem_map.mp hw
        rw [← hgw]
        have h := map_conj_eq_conj_map (f := QuotientGroup.mk' O) (g := g) (A := E)
        rw [hE_normal_ED g hg] at h
        exact h.symm
      haveI : IsMulCommutative ↥(E.map (QuotientGroup.mk' O)) := hEbar_comm
      haveI hBsolv : Group.IsSolvable ((E.map (QuotientGroup.mk' O)).subgroupOf
          ((ED).map (QuotientGroup.mk' O))) :=
        Group.isSolvable_of_isSolvable_injective
          (f := (Subgroup.subgroupOfEquivOfLe hleW).toMonoidHom)
          (Subgroup.subgroupOfEquivOfLe hleW).injective
      haveI hquotB : Group.IsSolvable (((ED).map (QuotientGroup.mk' O)) ⧸
          ((E.map (QuotientGroup.mk' O)).subgroupOf ((ED).map (QuotientGroup.mk' O)))) := by
        refine hFT _ ?_
        rw [← Subgroup.index_eq_card
          ((E.map (QuotientGroup.mk' O)).subgroupOf ((ED).map (QuotientGroup.mk' O)))]
        have hrel : ((E.map (QuotientGroup.mk' O)).subgroupOf
            ((ED).map (QuotientGroup.mk' O))).index = (M.subgroupOf ED).index := by
          have h1 : ((E.map (QuotientGroup.mk' O)).subgroupOf
              ((ED).map (QuotientGroup.mk' O))).index =
              (E.map (QuotientGroup.mk' O)).relIndex ((ED).map (QuotientGroup.mk' O)) := rfl
          rw [h1, Subgroup.relIndex_map_map (f := QuotientGroup.mk' O) E ED,
            QuotientGroup.ker_mk',
            show ED ⊔ O = ED from sup_eq_left.mpr hO_le_ED]
          rfl
        rw [hrel]
        exact hM_index_odd
      haveI hWsolv : Group.IsSolvable ↥((ED).map (QuotientGroup.mk' O)) :=
        Group.isSolvable_of_subgroup_quotient
          ((E.map (QuotientGroup.mk' O)).subgroupOf ((ED).map (QuotientGroup.mk' O)))
      have hker : ((QuotientGroup.mk' O).comp ED.subtype).ker = O.subgroupOf ED := by
        ext x
        show (QuotientGroup.mk' O) ((x : ↥ED) : F) = 1 ↔ x ∈ O.subgroupOf ED
        rw [Subgroup.mem_subgroupOf]
        exact QuotientGroup.eq_one_iff ((x : ↥ED) : F)
      have hrange : ((QuotientGroup.mk' O).comp ED.subtype).range = (ED).map (QuotientGroup.mk' O) := by
        ext y
        constructor
        · rintro ⟨x, rfl⟩
          exact Subgroup.mem_map_of_mem _ x.2
        · rintro ⟨x, hx, rfl⟩
          exact ⟨⟨x, hx⟩, rfl⟩
      have hiso : (↥ED ⧸ (O.subgroupOf ED)) ≃* ↥((ED).map (QuotientGroup.mk' O)) :=
        (QuotientGroup.quotientMulEquivOfEq hker.symm).trans
          ((QuotientGroup.quotientKerEquivRange ((QuotientGroup.mk' O).comp ED.subtype)).trans
            (subgroupCongrMulEquiv hrange))
      exact Group.isSolvable_of_isSolvable_injective (f := hiso.toMonoidHom) hiso.injective
    exact Group.isSolvable_of_subgroup_quotient (O.subgroupOf ED)
  -- ## Sylow `2`-subgroups of `ED` are abelian
  have hSyl2 : ∀ S : Sylow 2 ↥ED, Submission.Blueprint.IsAbelianSubgroup (S : Subgroup ↥ED) := by
    refine sylow_two_isAbelian_of_normal_odd_exponent_two
      (N := O.subgroupOf ED) (M := M.subgroupOf ED) ?_ ?_ ?_ ?_ ?_ ?_
    · exact Subgroup.Normal.subgroupOf (Work.BrauerSuzuki.oddCore_normal F) ED
    · intro x hx
      rw [Subgroup.mem_subgroupOf] at hx ⊢
      exact (show O ≤ E ⊔ O from le_sup_right) hx
    · rw [Subgroup.normal_subgroupOf_iff_le_normalizer hM_le_ED]
      intro g hg
      rw [Subgroup.mem_normalizer_iff_map_conj_eq]
      exact hM_norm g hg
    · rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hO_le_ED).toEquiv]
      exact Work.BrauerSuzuki.OddCore.oddCard_oddCore
    · exact hM_index_odd
    · intro x hx
      rw [Subgroup.mem_subgroupOf]
      exact hM_sq x (Subgroup.mem_subgroupOf.mp hx)
  -- ## Glauberman's `ZJ` theorem in `ED`
  have hpCore_bot' : Submission.Blueprint.pPrimeCore p ↥ED = ⊥ := by
    rw [Work.GlaubermanZJ.pPrimeCore_eq_fitting p hp]
    exact hpCore_bot
  have hchar := hZJ ↥ED p hp hpodd hsolv hSyl2 P
  rw [hPcoe, hpCore_bot', bot_sup_eq] at hchar
  -- ## transport `ZJ` back to `F` and conclude
  have hZJmap : Submission.Blueprint.ZJ R =
      (Submission.Blueprint.ZJ (R.subgroupOf ED)).map ED.subtype := by
    rw [Work.GlaubermanZJ.ZJ_eq R, Work.GlaubermanZJ.ZJ_eq (R.subgroupOf ED)]
    have hker : (R.subgroupOf ED) ⊓ ED.subtype.ker = ⊥ := by
      rw [show ED.subtype.ker = ⊥ from
          (MonoidHom.ker_eq_bot_iff ED.subtype).mpr ED.subtype_injective, inf_bot_eq]
    have h := Work.PGroup.ZJ_map_of_ker_inf_eq_bot ED.subtype (R.subgroupOf ED) hker
    rw [show (R.subgroupOf ED).map ED.subtype = R from by
      rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hR_le_ED]] at h
    exact h
  rw [hZJmap]
  refine Subgroup.mem_normalizer_iff_map_conj_eq.mpr ?_
  have huED : u ∈ ED := hE_le_ED (Subgroup.subset_closure hu)
  have hfix : (Submission.Blueprint.ZJ (R.subgroupOf ED)).map
      (MulAut.conj (⟨u, huED⟩ : ↥ED)).toMonoidHom = Submission.Blueprint.ZJ (R.subgroupOf ED) :=
    (Subgroup.characteristic_iff_map_eq (H := Submission.Blueprint.ZJ (R.subgroupOf ED))).mp hchar
      (MulAut.conj (⟨u, huED⟩ : ↥ED))
  have h := congrArg (fun X : Subgroup ↥ED => X.map ED.subtype) hfix
  rw [Subgroup.map_map] at h
  rw [show (ED.subtype.comp (MulAut.conj (⟨u, huED⟩ : ↥ED)).toMonoidHom) =
      ((MulAut.conj u).toMonoidHom.comp ED.subtype) from by ext x; rfl] at h
  rw [← Subgroup.map_map] at h
  exact h

end Work.ThreePoints.ThmC
