import Mathlib
import Submission.Work.BSW.S3.Defs
import Submission.Work.BSW.S3.S31setup
import Submission.Work.BSW.Cases.S31core
import Submission.Work.BSW.Cases.bswCompletionBase
import Submission.Work.BSW.Cases.ncard_conjClassSet_K
import Submission.Work.BSW.Cases.conjClassSet_K_eq_centralizer
import Submission.Work.BSW.Cases.sum_iFn_conjClassSet_K
import Submission.Work.BSW.Cases.bswS32Setup
import Submission.Work.BSW.Api.card_sup_zpowers
import Submission.Work.BSW.Api.ncard_involutions_eq_index
import Submission.Work.BSW.Cases.Order.hallProp
import Submission.OddOrder.GroupTheory.TISubsetCounting
import Submission.Work.BSW.S3.hallConj
import Submission.Work.BSW.S3.exists_involution_inverts_of_isConj_inv
import Submission.Work.BSW.S3.order_eq_of_two_classes
import Submission.Work.BSW.S3.prime_orderOf_of_centralizer_subset

open scoped BigOperators Pointwise

namespace Work.BSW.S3

open Subgroup Work.GW2

variable {G : Type} [Group G] [Finite G] {t s : G} {K : Subgroup G} {x : G}

/-- `H = C_G(t)` has order `2k`. -/
theorem card_centralizer_t_s35 (h : BSWHyps2 G t s K) :
    Nat.card (Subgroup.centralizer ({t} : Set G)) = 2 * Nat.card K := by
  rw [Work.BSW.centralizer_t_eq h, Work.BSW.Api.card_sup_zpowers h]

/-- `|G : C_G(t)| = (2k-1)(k-1)`. -/
theorem index_centralizer_t_s35 (h : BSWHyps2 G t s K)
    (hG : Nat.card G = (2 * Nat.card K - 1) * (Nat.card K - 1) * (2 * Nat.card K))
    (hk : 4 < Nat.card K) :
    (Subgroup.centralizer ({t} : Set G)).index = (2 * Nat.card K - 1) * (Nat.card K - 1) := by
  have h1 := Subgroup.card_mul_index (Subgroup.centralizer ({t} : Set G))
  rw [card_centralizer_t_s35 h, hG] at h1
  refine Nat.eq_of_mul_eq_mul_left (by omega : 0 < 2 * Nat.card K) ?_
  rw [h1]; ring

/-- `|G : C_G(x)| = (2k-1)·2k`. -/
theorem index_centralizer_x_s35 (h : BSWHyps2 G t s K)
    (hG : Nat.card G = (2 * Nat.card K - 1) * (Nat.card K - 1) * (2 * Nat.card K))
    (hk : 4 < Nat.card K)
    (hf : Nat.card (Subgroup.centralizer ({x} : Set G)) = Nat.card K - 1) :
    (Subgroup.centralizer ({x} : Set G)).index = (2 * Nat.card K - 1) * (2 * Nat.card K) := by
  have h1 := Subgroup.card_mul_index (Subgroup.centralizer ({x} : Set G))
  rw [hf, hG] at h1
  refine Nat.eq_of_mul_eq_mul_left (by omega : 0 < Nat.card K - 1) ?_
  rw [h1]; ring

/-- `|G : N_G(C_G(x))| = (2k-1)·k`. -/
theorem index_normalizer_x_s35 (h : BSWHyps2 G t s K)
    (hG : Nat.card G = (2 * Nat.card K - 1) * (Nat.card K - 1) * (2 * Nat.card K))
    (hk : 4 < Nat.card K)
    (hM : Nat.card (Subgroup.normalizer (Subgroup.centralizer ({x} : Set G) : Set G)) =
      2 * (Nat.card K - 1)) :
    (Subgroup.normalizer (Subgroup.centralizer ({x} : Set G) : Set G)).index =
      (2 * Nat.card K - 1) * Nat.card K := by
  have h1 := Subgroup.card_mul_index
    (Subgroup.normalizer (Subgroup.centralizer ({x} : Set G) : Set G))
  rw [hM, hG] at h1
  refine Nat.eq_of_mul_eq_mul_left (by omega : 0 < 2 * (Nat.card K - 1)) ?_
  rw [h1]; ring

/-- `F = C_G(x)` meets `H^G = K^G` only in the identity. -/
theorem centralizer_inf_HG_s35 (h : BSWHyps2 G t s K) (hx : x ∉ HG t)
    (hinv : t⁻¹ * x * t = x⁻¹)
    {a : G} (ha : a ∈ Subgroup.centralizer ({x} : Set G)) (haH : a ∈ HG t) : a = 1 := by
  by_contra ha1
  obtain ⟨g, hg⟩ := haH
  have hcomm' : (g * a * g⁻¹) * t = t * (g * a * g⁻¹) :=
    Subgroup.mem_centralizer_singleton_iff.mp hg
  have hcomm : a * (g⁻¹ * t * g) = (g⁻¹ * t * g) * a := by
    calc a * (g⁻¹ * t * g) = g⁻¹ * ((g * a * g⁻¹) * t) * g := by group
      _ = g⁻¹ * (t * (g * a * g⁻¹)) * g := by rw [hcomm']
      _ = (g⁻¹ * t * g) * a := by group
  have ht'2 : orderOf (g⁻¹ * t * g) = 2 := by
    have hh : g⁻¹ * t * g = (MulAut.conj g⁻¹) t := by rw [MulAut.conj_apply]; group
    rw [hh, MulEquiv.orderOf_eq, Work.BSW.orderOf_t h]
  have ht'C : g⁻¹ * t * g ∈ Subgroup.centralizer ({x} : Set G) := by
    rw [← centralizer_eq_of_mem_centralizer h hx hinv a ha ha1]
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact hcomm.symm
  have hdvd : 2 ∣ Nat.card (Subgroup.centralizer ({x} : Set G)) := by
    rw [← ht'2]
    exact Subgroup.orderOf_dvd_natCard _ ht'C
  exact (Nat.not_even_iff_odd.mpr (odd_card_centralizer_of_notMem_HG h hx))
    (even_iff_two_dvd.mpr hdvd)

/-- `F = C_G(x)` is TI, with normalizer `N_G(F)`. -/
theorem centralizer_TI_s35 (h : BSWHyps2 G t s K) (hx : x ∉ HG t)
    (hinv : t⁻¹ * x * t = x⁻¹)
    {g : G} (hg : g ∉ Subgroup.normalizer (Subgroup.centralizer ({x} : Set G) : Set G)) :
    Subgroup.centralizer ({x} : Set G) ⊓ conjSub g (Subgroup.centralizer ({x} : Set G)) =
      ⊥ := by
  rw [eq_bot_iff]
  intro w hw
  rw [Subgroup.mem_bot]
  rw [Subgroup.mem_inf] at hw
  obtain ⟨hwF, hwc⟩ := hw
  obtain ⟨a, haF, haw⟩ :=
    (Work.BSW.Cases.mem_conjSub_K (K := Subgroup.centralizer ({x} : Set G))).mp hwc
  by_cases hw1 : w = 1
  · exact hw1
  have ha1 : a ≠ 1 := by
    rintro rfl
    exact hw1 (by rw [← haw]; group)
  have hCab : IsMulCommutative ↥(Subgroup.centralizer ({x} : Set G)) :=
    isMulCommutative_centralizer h hx hinv
  have haw' : g⁻¹ * w * g = a := by rw [← haw]; group
  have hmap : Subgroup.map (MulAut.conj g).toMonoidHom
      (Subgroup.centralizer ({x} : Set G)) = Subgroup.centralizer ({x} : Set G) := by
    refine le_antisymm ?_ ?_
    · intro z hz
      obtain ⟨u, hu, huz⟩ := Subgroup.mem_map.mp hz
      rw [← huz]
      have hcu : a * u = u * a :=
        congrArg Subtype.val (hCab.is_comm.comm ⟨a, haF⟩ ⟨u, hu⟩)
      have hc : (g * a * g⁻¹) * (g * u * g⁻¹) = (g * u * g⁻¹) * (g * a * g⁻¹) := by
        rw [show (g * a * g⁻¹) * (g * u * g⁻¹) = g * (a * u) * g⁻¹ from by group,
            show (g * u * g⁻¹) * (g * a * g⁻¹) = g * (u * a) * g⁻¹ from by group, hcu]
      have hmem : g * u * g⁻¹ ∈ Subgroup.centralizer ({w} : Set G) :=
        Subgroup.mem_centralizer_singleton_iff.mpr (by rw [← haw]; exact hc.symm)
      rw [centralizer_eq_of_mem_centralizer h hx hinv w hwF hw1] at hmem
      exact hmem
    · intro z hz
      have hz' : g⁻¹ * z * g ∈ Subgroup.centralizer ({x} : Set G) := by
        have hcz : w * z = z * w :=
          congrArg Subtype.val (hCab.is_comm.comm ⟨w, hwF⟩ ⟨z, hz⟩)
        have hc : (g⁻¹ * z * g) * a = a * (g⁻¹ * z * g) := by
          rw [show (g⁻¹ * z * g) * a = (g⁻¹ * z * g) * (g⁻¹ * w * g)
                from by rw [haw'],
              show a * (g⁻¹ * z * g) = (g⁻¹ * w * g) * (g⁻¹ * z * g)
                from by rw [haw'],
              show (g⁻¹ * z * g) * (g⁻¹ * w * g) = g⁻¹ * (z * w) * g from by group,
              show (g⁻¹ * w * g) * (g⁻¹ * z * g) = g⁻¹ * (w * z) * g from by group, hcz]
        have hca : g⁻¹ * z * g ∈ Subgroup.centralizer ({a} : Set G) :=
          Subgroup.mem_centralizer_singleton_iff.mpr hc
        rwa [centralizer_eq_of_mem_centralizer h hx hinv a haF ha1] at hca
      refine Subgroup.mem_map.mpr ⟨g⁻¹ * z * g, hz', ?_⟩
      change (MulAut.conj g) (g⁻¹ * z * g) = z
      rw [MulAut.conj_apply]; group
  exact (hg (Subgroup.mem_normalizer_iff_map_conj_eq.mpr hmap)).elim

/-- Conjugation by an element of the normalizer preserves a subgroup. -/
theorem mulAut_conj_smul_eq_self' {G : Type} [Group G] {H : Subgroup G} {l : G}
    (hl : l ∈ Subgroup.normalizer (H : Set G)) : MulAut.conj l • (H : Set G) = (H : Set G) := by
  have hiff := Subgroup.mem_normalizer_iff.mp hl
  ext y
  rw [Set.mem_smul_set]
  constructor
  · rintro ⟨z, hz, hzy⟩
    have hzy' : l * z * l⁻¹ = y := by simpa [MulAut.smul_def, MulAut.conj_apply] using hzy
    rw [← hzy']; exact (hiff z).mp hz
  · intro hy
    refine ⟨l⁻¹ * y * l, ?_, ?_⟩
    · exact (hiff (l⁻¹ * y * l)).mpr
        (by rw [show l * (l⁻¹ * y * l) * l⁻¹ = y from by group]; exact hy)
    · rw [MulAut.smul_def, MulAut.conj_apply]; group

/-- `F \ {1}` is TI with normalizer bound `N_G(F)`. -/
theorem isTISubset_F_sdiff (h : BSWHyps2 G t s K) (hx : x ∉ HG t)
    (hinv : t⁻¹ * x * t = x⁻¹) :
    OddOrder.GroupTheory.IsTISubset
      ((Subgroup.centralizer ({x} : Set G) : Set G) \ {1})
      (Subgroup.normalizer (Subgroup.centralizer ({x} : Set G) : Set G)) := by
  intro g hg
  by_contra hgN
  obtain ⟨a, ha, hga⟩ := hg
  have hbot := centralizer_TI_s35 h hx hinv hgN
  have hmem : g * a * g⁻¹ ∈ (Subgroup.centralizer ({x} : Set G) ⊓
      conjSub g (Subgroup.centralizer ({x} : Set G)) : Subgroup G) :=
    ⟨hga.1, ⟨a, ha.1, rfl⟩⟩
  rw [hbot] at hmem
  refine ha.2 ?_
  have h1 : g * a * g⁻¹ = 1 := Subgroup.mem_bot.mp hmem
  have h2 : a = 1 := by
    calc a = g⁻¹ * (g * a * g⁻¹) * g := by group
      _ = 1 := by rw [h1]; group
  rw [h2]; exact Set.mem_singleton 1

/-- The stabilizer of `F \ {1}` under conjugation by `N_G(F)`. -/
theorem smul_sdiff_one_centralizer (h : BSWHyps2 G t s K) (hx : x ∉ HG t)
    (hinv : t⁻¹ * x * t = x⁻¹)
    {l : G} (hl : l ∈ Subgroup.normalizer (Subgroup.centralizer ({x} : Set G) : Set G)) :
    MulAut.conj l • ((Subgroup.centralizer ({x} : Set G) : Set G) \ {1})
      = (Subgroup.centralizer ({x} : Set G) : Set G) \ {1} := by
  rw [Set.smul_set_sdiff, mulAut_conj_smul_eq_self' hl, Set.smul_set_singleton,
    MulAut.smul_def, MulAut.conj_apply]
  simp

/-- Cardinality of a TI-saturation. -/
theorem ncard_conjClassSet_of_isTISubset' {G : Type} [Group G] [Finite G]
    {A : Set G} {L : Subgroup G}
    (hTI : OddOrder.GroupTheory.IsTISubset A L)
    (hstab : ∀ l ∈ L, MulAut.conj l • A = A) :
    (OddOrder.GroupTheory.conjClassSet A).ncard = A.ncard * L.index := by
  have h := OddOrder.GroupTheory.IsTISubset.sum_conjClassSet (A := A) (L := L)
      (f := fun _ : G => (1 : ℕ)) hTI hstab (fun g x => rfl)
  simp only [Finset.sum_const, smul_eq_mul, mul_one, nsmul_eq_mul] at h
  rw [← Set.ncard_eq_toFinset_card A (Set.toFinite A),
      ← Set.ncard_eq_toFinset_card (OddOrder.GroupTheory.conjClassSet A) (Set.toFinite _)] at h
  rw [h]; exact Nat.mul_comm _ _

/-- `|(F \ {1})^G| = (k-2)·[G : N_G(F)]`. -/
theorem ncard_conjClassSet_F_sdiff (h : BSWHyps2 G t s K) (hx : x ∉ HG t)
    (hinv : t⁻¹ * x * t = x⁻¹) (hf : Nat.card (Subgroup.centralizer ({x} : Set G)) =
      Nat.card K - 1) (hk : 4 < Nat.card K) :
    (OddOrder.GroupTheory.conjClassSet
        ((Subgroup.centralizer ({x} : Set G) : Set G) \ {1})).ncard
      = (Nat.card K - 2) *
        (Subgroup.normalizer (Subgroup.centralizer ({x} : Set G) : Set G)).index := by
  rw [ncard_conjClassSet_of_isTISubset' (isTISubset_F_sdiff h hx hinv)
    (fun l hl => smul_sdiff_one_centralizer h hx hinv hl)]
  congr 1
  have h1 : ((Subgroup.centralizer ({x} : Set G) : Set G) \ {1}).ncard + 1
      = Nat.card (Subgroup.centralizer ({x} : Set G)) := by
    rw [show Nat.card (Subgroup.centralizer ({x} : Set G))
        = ((Subgroup.centralizer ({x} : Set G) : Set G)).ncard from rfl]
    exact Set.ncard_sdiff_singleton_add_one (Subgroup.centralizer ({x} : Set G)).one_mem
  rw [hf] at h1
  omega

/-- Every non-identity element of `F = C_G(x)` has `i = |F| = k - 1`. -/
theorem iFn_eq_of_mem_centralizer_s35 (h : BSWHyps2 G t s K) (hx : x ∉ HG t)
    (hinv : t⁻¹ * x * t = x⁻¹) (hf : Nat.card (Subgroup.centralizer ({x} : Set G)) =
      Nat.card K - 1)
    {a : G} (ha : a ∈ Subgroup.centralizer ({x} : Set G)) (ha1 : a ≠ 1) :
    Work.BSW.iFn G a = Nat.card K - 1 := by
  have hCa : Subgroup.centralizer ({a} : Set G) = Subgroup.centralizer ({x} : Set G) :=
    centralizer_eq_of_mem_centralizer h hx hinv a ha ha1
  have hodd : Odd (Nat.card (Subgroup.centralizer ({a} : Set G))) := by
    rw [hCa]; exact odd_card_centralizer_of_notMem_HG h hx
  have hinva : t⁻¹ * a * t = a⁻¹ := by
    rw [Work.BSW.t_inv h]; exact inverts_centralizer h hx hinv a ha
  have hres := (Work.BSW.Cases.S31core h (x := a) (u := t) hodd (Work.BSW.orderOf_t h) hinva).1
  rw [← hres, hCa, hf]

/-- `∑_{a ∈ F#} i(a) = (k-2)(k-1)`. -/
theorem sum_iFn_F_sdiff_s35 (h : BSWHyps2 G t s K) (hx : x ∉ HG t)
    (hinv : t⁻¹ * x * t = x⁻¹) (hf : Nat.card (Subgroup.centralizer ({x} : Set G)) =
      Nat.card K - 1) (hk : 4 < Nat.card K) :
    ∑ a ∈ (Set.toFinite
        ((Subgroup.centralizer ({x} : Set G) : Set G) \ {1})).toFinset,
        (Work.BSW.iFn G a : ℤ)
      = ((Nat.card K : ℤ) - 2) * ((Nat.card K : ℤ) - 1) := by
  classical
  set A : Set G := (Subgroup.centralizer ({x} : Set G) : Set G) \ {1} with hA
  have hconst : ∀ a ∈ (Set.toFinite A).toFinset,
      (Work.BSW.iFn G a : ℤ) = ((Nat.card K : ℤ) - 1) := by
    intro a ha
    have ha' : a ∈ Subgroup.centralizer ({x} : Set G) ∧ a ≠ 1 := by
      have hmem := Set.Finite.mem_toFinset (Set.toFinite A) |>.mp ha
      rw [hA] at hmem
      exact ⟨hmem.1, by simpa [Set.mem_singleton_iff] using hmem.2⟩
    rw [iFn_eq_of_mem_centralizer_s35 h hx hinv hf ha'.1 ha'.2,
      Nat.cast_sub (by omega : 1 ≤ Nat.card K)]
    norm_num
  have hAcard : (Set.toFinite A).toFinset.card = Nat.card K - 2 := by
    have h1 : (Set.toFinite A).toFinset.card + 1
        = Nat.card (Subgroup.centralizer ({x} : Set G)) := by
      rw [show Nat.card (Subgroup.centralizer ({x} : Set G))
          = ((Subgroup.centralizer ({x} : Set G) : Set G)).ncard from rfl]
      rw [← Set.ncard_eq_toFinset_card A (Set.toFinite A), hA]
      exact Set.ncard_sdiff_singleton_add_one (Subgroup.centralizer ({x} : Set G)).one_mem
    rw [hf] at h1
    omega
  calc ∑ a ∈ (Set.toFinite A).toFinset, (Work.BSW.iFn G a : ℤ)
      = ∑ a ∈ (Set.toFinite A).toFinset, ((Nat.card K : ℤ) - 1) :=
        Finset.sum_congr rfl hconst
    _ = ((Set.toFinite A).toFinset.card) • ((Nat.card K : ℤ) - 1) := Finset.sum_const _
    _ = (((Set.toFinite A).toFinset.card : ℕ) : ℤ) * ((Nat.card K : ℤ) - 1) := by
        rw [nsmul_eq_mul]
    _ = ((Nat.card K : ℤ) - 2) * ((Nat.card K : ℤ) - 1) := by
        rw [hAcard, Nat.cast_sub (by omega : 2 ≤ Nat.card K)]; norm_num

/-- `∑_{a ∈ (F\{1})^G} i(a) = (k-2)(k-1)·[G : N_G(F)]`. -/
theorem sum_iFn_conjClassSet_F_sdiff (h : BSWHyps2 G t s K) (hx : x ∉ HG t)
    (hinv : t⁻¹ * x * t = x⁻¹) (hf : Nat.card (Subgroup.centralizer ({x} : Set G)) =
      Nat.card K - 1) (hk : 4 < Nat.card K) :
    ∑ a ∈ (Set.toFinite (OddOrder.GroupTheory.conjClassSet
        ((Subgroup.centralizer ({x} : Set G) : Set G) \ {1}))).toFinset,
        (Work.BSW.iFn G a : ℤ)
      = ((Nat.card K : ℤ) - 2) * ((Nat.card K : ℤ) - 1) *
        ((Subgroup.normalizer (Subgroup.centralizer ({x} : Set G) : Set G)).index : ℤ) := by
  have hsum := OddOrder.GroupTheory.IsTISubset.sum_conjClassSet
      (A := (Subgroup.centralizer ({x} : Set G) : Set G) \ {1})
      (L := Subgroup.normalizer (Subgroup.centralizer ({x} : Set G) : Set G))
      (f := fun a : G => (Work.BSW.iFn G a : ℤ))
      (isTISubset_F_sdiff h hx hinv) (fun l hl => smul_sdiff_one_centralizer h hx hinv hl)
      (fun g a => by rw [Work.BSW.Cases.iFn_conj g a])
  rw [hsum, sum_iFn_F_sdiff_s35 h hx hinv hf hk, nsmul_eq_mul]
  ring

/-! ## The set `Y = G \ (H^G ∪ F^G)` -/

/-- Bender's set `Y = G ∖ (H^G ∪ F^G)` of §3.5. -/
def Ysub {G : Type} [Group G] (x t : G) : Set G :=
  {y : G | y ∉ HG t ∧
    y ∉ OddOrder.GroupTheory.conjClassSet (Subgroup.centralizer ({x} : Set G) : Set G)}

theorem mem_Ysub {G : Type} [Group G] {x t y : G} :
    y ∈ Ysub x t ↔ y ∉ HG t ∧
      ∀ g : G, g * y * g⁻¹ ∉ Subgroup.centralizer ({x} : Set G) := by
  rw [Ysub]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨h1, fun g hg => h2 ?_⟩
    rw [← Work.BSW.Cases.setOf_exists_conj_mem_eq_conjClassSet
      (Subgroup.centralizer ({x} : Set G))]
    exact ⟨g, hg⟩
  · rintro ⟨h1, h2⟩
    refine ⟨h1, fun hc => ?_⟩
    rw [← Work.BSW.Cases.setOf_exists_conj_mem_eq_conjClassSet
      (Subgroup.centralizer ({x} : Set G))] at hc
    obtain ⟨g, hg⟩ := hc
    exact h2 g hg

/-- The conjugacy saturation of a subgroup is closed under inversion. -/
theorem conjClassSet_inv_mem {G : Type} [Group G] {T : Set G} (hT : ∀ a ∈ T, a⁻¹ ∈ T)
    {y : G} (hy : y ∈ OddOrder.GroupTheory.conjClassSet T) :
    y⁻¹ ∈ OddOrder.GroupTheory.conjClassSet T := by
  rw [OddOrder.GroupTheory.mem_conjClassSet] at hy ⊢
  obtain ⟨a, ha, g, hg⟩ := hy
  refine ⟨a⁻¹, hT a ha, g, ?_⟩
  rw [← hg]; group

theorem HG_eq_conjClassSet_K (h : BSWHyps2 G t s K) :
    HG t = OddOrder.GroupTheory.conjClassSet (K : Set G) :=
  (Work.BSW.Cases.conjClassSet_K_eq_centralizer h).symm

/-- `H^G ∩ F^G = {1}`. -/
theorem HG_inter_FG (h : BSWHyps2 G t s K) (hx : x ∉ HG t) (hinv : t⁻¹ * x * t = x⁻¹) :
    HG t ∩ OddOrder.GroupTheory.conjClassSet (Subgroup.centralizer ({x} : Set G) : Set G)
      = {1} := by
  ext w
  constructor
  · rintro ⟨hwH, hwF⟩
    obtain ⟨g, hg⟩ :=
      (Work.BSW.Cases.setOf_exists_conj_mem_eq_conjClassSet
        (Subgroup.centralizer ({x} : Set G))).symm ▸ hwF
    obtain ⟨hh, hhh⟩ := hwH
    have hgw : g * w * g⁻¹ ∈ HG t := ⟨hh * g⁻¹, by
      show (hh * g⁻¹) * (g * w * g⁻¹) * (hh * g⁻¹)⁻¹ ∈ Subgroup.centralizer ({t} : Set G)
      have he : (hh * g⁻¹) * (g * w * g⁻¹) * (hh * g⁻¹)⁻¹ = hh * w * hh⁻¹ := by group
      rw [he]; exact hhh⟩
    have h1 : g * w * g⁻¹ = 1 := centralizer_inf_HG_s35 h hx hinv hg hgw
    rw [Set.mem_singleton_iff]
    calc w = g⁻¹ * (g * w * g⁻¹) * g := by group
      _ = 1 := by rw [h1]; group
  · intro hw
    rw [Set.mem_singleton_iff] at hw
    subst hw
    refine ⟨⟨1, by simp⟩, ?_⟩
    rw [← Work.BSW.Cases.setOf_exists_conj_mem_eq_conjClassSet
      (Subgroup.centralizer ({x} : Set G))]
    exact ⟨1, by simp⟩

theorem Ysub_conj (h : BSWHyps2 G t s K) {g y : G} (hy : y ∈ Ysub x t) :
    g * y * g⁻¹ ∈ Ysub x t := by
  rw [Ysub] at hy ⊢
  refine ⟨?_, ?_⟩
  · intro hc
    exact hy.1 (by
      rw [HG_eq_conjClassSet_K h] at hc ⊢
      exact (OddOrder.GroupTheory.mem_conjClassSet_conj_iff g y).mp hc)
  · intro hc
    exact hy.2 ((OddOrder.GroupTheory.mem_conjClassSet_conj_iff g y).mp hc)

theorem Ysub_inv (h : BSWHyps2 G t s K) {y : G} (hy : y ∈ Ysub x t) :
    y⁻¹ ∈ Ysub x t := by
  rw [Ysub] at hy ⊢
  refine ⟨fun hc => hy.1 ?_, fun hc => hy.2 ?_⟩
  · have hc' : y⁻¹ ∈ OddOrder.GroupTheory.conjClassSet (K : Set G) := by
      rw [HG_eq_conjClassSet_K h] at hc; exact hc
    have h1 := conjClassSet_inv_mem (T := (K : Set G)) (fun a ha => K.inv_mem ha) hc'
    rw [HG_eq_conjClassSet_K h]; simpa using h1
  · simpa using conjClassSet_inv_mem (T := (Subgroup.centralizer ({x} : Set G) : Set G))
      (fun a ha => (Subgroup.centralizer ({x} : Set G)).inv_mem ha) hc

/-- `|Y| = 4k(k-1)`. -/
theorem ncard_Ysub (h : BSWHyps2 G t s K) (hx : x ∉ HG t) (hinv : t⁻¹ * x * t = x⁻¹)
    (hf : Nat.card (Subgroup.centralizer ({x} : Set G)) = Nat.card K - 1)
    (hM : Nat.card (Subgroup.normalizer (Subgroup.centralizer ({x} : Set G) : Set G)) =
      2 * (Nat.card K - 1))
    (hG : Nat.card G = (2 * Nat.card K - 1) * (Nat.card K - 1) * (2 * Nat.card K))
    (hk : 4 < Nat.card K) :
    (Ysub x t).ncard = 4 * Nat.card K * (Nat.card K - 1) := by
  set B : Set G := OddOrder.GroupTheory.conjClassSet
      (Subgroup.centralizer ({x} : Set G) : Set G) with hBdef
  have hY : Ysub x t = (HG t ∪ B)ᶜ := by
    rw [Ysub, hBdef]
    ext y
    simp only [Set.mem_setOf_eq, Set.mem_compl_iff, Set.mem_union, not_or]
  have hBdiff : B \ {1} = OddOrder.GroupTheory.conjClassSet
      ((Subgroup.centralizer ({x} : Set G) : Set G) \ {1}) := by
    rw [hBdef]
    ext y
    constructor
    · rintro ⟨hy, hy1⟩
      rw [OddOrder.GroupTheory.mem_conjClassSet] at hy ⊢
      obtain ⟨a, ha, g, hg⟩ := hy
      refine ⟨a, ⟨ha, ?_⟩, g, hg⟩
      intro h1
      rw [Set.mem_singleton_iff] at h1
      exact hy1 (by rw [← hg, h1]; simp)
    · intro hy
      rw [OddOrder.GroupTheory.mem_conjClassSet] at hy
      obtain ⟨a, ⟨ha, ha1⟩, g, hg⟩ := hy
      refine ⟨?_, ?_⟩
      · rw [OddOrder.GroupTheory.mem_conjClassSet]; exact ⟨a, ha, g, hg⟩
      · intro h1
        rw [Set.mem_singleton_iff] at h1
        exact ha1 (by
          calc a = g⁻¹ * (g * a * g⁻¹) * g := by group
            _ = g⁻¹ * y * g := by rw [← hg]
            _ = 1 := by rw [h1]; group)
  have h1A : (1 : G) ∈ HG t := ⟨1, by simp⟩
  have hdisj : Disjoint (HG t) (B \ {1}) := by
    rw [Set.disjoint_left]
    rintro y hy hyB
    have : y ∈ HG t ∩ B := ⟨hy, hyB.1⟩
    rw [HG_inter_FG h hx hinv] at this
    rw [Set.mem_singleton_iff] at this
    exact hyB.2 this
  have hunion1 : HG t ∪ B = HG t ∪ (B \ {1}) := by
    ext y
    simp only [Set.mem_union, Set.mem_sdiff, Set.mem_singleton_iff]
    constructor
    · rintro (hy | hy)
      · exact Or.inl hy
      · by_cases hy1 : y = 1
        · exact Or.inl (by rw [hy1]; exact h1A)
        · exact Or.inr ⟨hy, hy1⟩
    · rintro (hy | ⟨hy, _⟩)
      · exact Or.inl hy
      · exact Or.inr hy
  have hABcard : (HG t ∪ B).ncard = (HG t).ncard + (B \ {1}).ncard := by
    rw [hunion1]
    exact Set.ncard_union_eq hdisj (Set.toFinite _) (Set.toFinite _)
  have hAcard : (HG t).ncard =
      (2 * Nat.card K - 1) * (Nat.card K - 1) * (Nat.card K - 1) + 1 := by
    rw [HG_eq_conjClassSet_K h, Work.BSW.Cases.ncard_conjClassSet_K h]
    have hI : Work.BSW.invCount G = (2 * Nat.card K - 1) * (Nat.card K - 1) := by
      show {u : G | orderOf u = 2}.ncard = (2 * Nat.card K - 1) * (Nat.card K - 1)
      rw [Work.BSW.Api.ncard_involutions_eq_index h]
      exact index_centralizer_t_s35 h hG hk
    rw [hI]
  have hBcard : (B \ {1}).ncard =
      (Nat.card K - 2) * ((2 * Nat.card K - 1) * Nat.card K) := by
    rw [hBdiff, ncard_conjClassSet_F_sdiff h hx hinv hf hk,
      index_normalizer_x_s35 h hG hk hM]
  have hle : (HG t ∪ B).ncard ≤ Nat.card G := by
    have := Set.ncard_le_ncard (Set.subset_univ (HG t ∪ B)) (Set.toFinite (Set.univ : Set G))
    rwa [Set.ncard_univ G] at this
  have hZ : (((Ysub x t).ncard : ℕ) : ℤ) = ((4 * Nat.card K * (Nat.card K - 1) : ℕ) : ℤ) := by
    have hcompl : ((HG t ∪ B)ᶜ).ncard = Nat.card G - (HG t ∪ B).ncard :=
      Set.ncard_compl (HG t ∪ B) (Set.toFinite _) (Set.toFinite _)
    rw [← hY] at hcompl
    rw [hcompl, Nat.cast_sub hle, hABcard, hAcard, hBcard, hG]
    have hk2 : 2 ≤ Nat.card K := by omega
    have hk1 : 1 ≤ Nat.card K := by omega
    have h2k : 1 ≤ 2 * Nat.card K := by omega
    push_cast [Nat.cast_sub hk2, Nat.cast_sub hk1, Nat.cast_sub h2k]
    ring
  exact Nat.cast_injective hZ

/-- For `y ∈ Y` the value `i(y)` vanishes: `∑_{y ∈ Y} i(y) = 0`. -/
theorem sum_iFn_Ysub (h : BSWHyps2 G t s K) (hx : x ∉ HG t) (hinv : t⁻¹ * x * t = x⁻¹)
    (hf : Nat.card (Subgroup.centralizer ({x} : Set G)) = Nat.card K - 1)
    (hM : Nat.card (Subgroup.normalizer (Subgroup.centralizer ({x} : Set G) : Set G)) =
      2 * (Nat.card K - 1))
    (hG : Nat.card G = (2 * Nat.card K - 1) * (Nat.card K - 1) * (2 * Nat.card K))
    (hk : 4 < Nat.card K) :
    ∑ y ∈ (Set.toFinite (Ysub x t)).toFinset, (Work.BSW.iFn G y : ℤ) = 0 := by
  classical
  haveI : Fintype G := Fintype.ofFinite G
  set F : Subgroup G := Subgroup.centralizer ({x} : Set G) with hFdef
  set sA : Finset G := (Set.toFinite (HG t)).toFinset with hsA
  set sB : Finset G := (Set.toFinite (OddOrder.GroupTheory.conjClassSet ((F : Set G) \ {1}))).toFinset
    with hsB
  set sY : Finset G := (Set.toFinite (Ysub x t)).toFinset with hsY
  have hmA : ∀ y : G, y ∈ sA ↔ y ∈ HG t := by
    intro y; rw [hsA]; exact Set.Finite.mem_toFinset _
  have hmB : ∀ y : G, y ∈ sB ↔ y ∈ OddOrder.GroupTheory.conjClassSet ((F : Set G) \ {1}) := by
    intro y; rw [hsB]; exact Set.Finite.mem_toFinset _
  have hmY : ∀ y : G, y ∈ sY ↔ y ∈ Ysub x t := by
    intro y; rw [hsY]; exact Set.Finite.mem_toFinset _
  -- the three sets cover `G`
  have hcover : sA ∪ sB ∪ sY = Finset.univ := by
    apply Finset.eq_univ_iff_forall.mpr
    intro y
    rw [Finset.mem_union, Finset.mem_union, hmA y, hmB y, hmY y]
    by_cases h1 : y ∈ HG t
    · exact Or.inl (Or.inl h1)
    · by_cases h2 : y ∈ OddOrder.GroupTheory.conjClassSet (F : Set G)
      · refine Or.inl (Or.inr ?_)
        rw [OddOrder.GroupTheory.mem_conjClassSet] at h2 ⊢
        obtain ⟨a, ha, g, hg⟩ := h2
        refine ⟨a, ⟨ha, ?_⟩, g, hg⟩
        intro ha1
        rw [Set.mem_singleton_iff] at ha1
        have hy1 : y = 1 := by rw [← hg, ha1]; group
        exact h1 (hy1 ▸ ⟨1, by simp⟩)
      · exact Or.inr ⟨h1, h2⟩
  have hdAB : Disjoint sA sB := by
    rw [Finset.disjoint_left]
    intro y hyA hyB
    rw [hmA y] at hyA
    rw [hmB y] at hyB
    have hyF : y ∈ OddOrder.GroupTheory.conjClassSet (F : Set G) :=
      OddOrder.GroupTheory.conjClassSet_mono (fun z hz => hz.1) hyB
    have hmem : y ∈ HG t ∩ OddOrder.GroupTheory.conjClassSet (F : Set G) := ⟨hyA, hyF⟩
    rw [HG_inter_FG h hx hinv] at hmem
    rw [Set.mem_singleton_iff] at hmem
    rw [OddOrder.GroupTheory.mem_conjClassSet] at hyB
    obtain ⟨a, ⟨-, ha1⟩, g, hg⟩ := hyB
    exact ha1 (by
      calc a = g⁻¹ * (g * a * g⁻¹) * g := by group
        _ = 1 := by rw [hg, hmem]; group)
  have hdAY : Disjoint sA sY := by
    rw [Finset.disjoint_left]
    intro y hyA hyY
    rw [hmA y] at hyA
    rw [hmY y] at hyY
    exact hyY.1 hyA
  have hdBY : Disjoint sB sY := by
    rw [Finset.disjoint_left]
    intro y hyB hyY
    rw [hmB y] at hyB
    rw [hmY y] at hyY
    exact hyY.2 (OddOrder.GroupTheory.conjClassSet_mono (fun z hz => hz.1) hyB)
  have hd1 : Disjoint (sA ∪ sB) sY := by
    rw [Finset.disjoint_left] at hdAY hdBY ⊢
    intro y hy hyY
    rcases Finset.mem_union.mp hy with h' | h'
    · exact hdAY h' hyY
    · exact hdBY h' hyY
  have hsumAll : ∑ y : G, (Work.BSW.iFn G y : ℤ)
      = (Work.BSW.invCount G : ℤ) ^ 2 + (Work.BSW.invCount G : ℤ) := by
    rw [← Nat.cast_sum (s := Finset.univ) (f := fun y : G => Work.BSW.iFn G y),
      Work.BSW.Cases.sum_iFn G]
    push_cast
    ring
  have hI : Work.BSW.invCount G = (2 * Nat.card K - 1) * (Nat.card K - 1) := by
    show {u : G | orderOf u = 2}.ncard = (2 * Nat.card K - 1) * (Nat.card K - 1)
    rw [Work.BSW.Api.ncard_involutions_eq_index h]
    exact index_centralizer_t_s35 h hG hk
  have hsAeq : sA = (Set.toFinite (OddOrder.GroupTheory.conjClassSet (K : Set G))).toFinset := by
    ext y
    rw [hmA y, Set.Finite.mem_toFinset, HG_eq_conjClassSet_K h]
  have hsumA : ∑ y ∈ sA, (Work.BSW.iFn G y : ℤ)
      = (Work.BSW.invCount G : ℤ) * ((Nat.card K : ℤ) ^ 2 - (Nat.card K : ℤ) + 1)
        + (Work.BSW.invCount G : ℤ) := by
    rw [hsAeq]; exact Work.BSW.Cases.sum_iFn_conjClassSet_K h
  have hsumB : ∑ y ∈ sB, (Work.BSW.iFn G y : ℤ)
      = ((Nat.card K : ℤ) - 2) * ((Nat.card K : ℤ) - 1)
        * (((2 * Nat.card K - 1) * Nat.card K : ℕ) : ℤ) := by
    rw [sum_iFn_conjClassSet_F_sdiff h hx hinv hf hk, index_normalizer_x_s35 h hG hk hM]
  have hpart : ∑ y : G, (Work.BSW.iFn G y : ℤ)
      = ∑ y ∈ sA, (Work.BSW.iFn G y : ℤ) + ∑ y ∈ sB, (Work.BSW.iFn G y : ℤ)
        + ∑ y ∈ sY, (Work.BSW.iFn G y : ℤ) := by
    rw [← hcover, Finset.sum_union hd1, Finset.sum_union hdAB]
  have hkey : (Work.BSW.invCount G : ℤ) ^ 2 + (Work.BSW.invCount G : ℤ)
      = (Work.BSW.invCount G : ℤ) * ((Nat.card K : ℤ) ^ 2 - (Nat.card K : ℤ) + 1)
        + (Work.BSW.invCount G : ℤ)
        + ((Nat.card K : ℤ) - 2) * ((Nat.card K : ℤ) - 1)
          * (((2 * Nat.card K - 1) * Nat.card K : ℕ) : ℤ) := by
    have hk2 : 2 ≤ Nat.card K := by omega
    have hk1 : 1 ≤ Nat.card K := by omega
    have h2k : 1 ≤ 2 * Nat.card K := by omega
    rw [hI]
    push_cast [Nat.cast_sub hk1, Nat.cast_sub hk2, Nat.cast_sub h2k]
    ring
  rw [hsumAll, hsumA, hsumB] at hpart
  rw [hkey] at hpart
  linarith

/-- For `y ∈ Y`, `i(y) = 0`; in particular `y` is not conjugate to `y⁻¹`. -/
theorem iFn_eq_zero_of_mem_Ysub (h : BSWHyps2 G t s K) (hx : x ∉ HG t)
    (hinv : t⁻¹ * x * t = x⁻¹)
    (hf : Nat.card (Subgroup.centralizer ({x} : Set G)) = Nat.card K - 1)
    (hM : Nat.card (Subgroup.normalizer (Subgroup.centralizer ({x} : Set G) : Set G)) =
      2 * (Nat.card K - 1))
    (hG : Nat.card G = (2 * Nat.card K - 1) * (Nat.card K - 1) * (2 * Nat.card K))
    (hk : 4 < Nat.card K) {y : G} (hy : y ∈ Ysub x t) :
    Work.BSW.iFn G y = 0 := by
  classical
  have hs : ∑ z ∈ (Set.toFinite (Ysub x t)).toFinset, (Work.BSW.iFn G z : ℤ) = 0 :=
    sum_iFn_Ysub h hx hinv hf hM hG hk
  have hnonneg : ∀ z ∈ (Set.toFinite (Ysub x t)).toFinset, (0 : ℤ) ≤ (Work.BSW.iFn G z : ℤ) :=
    fun z _ => Int.natCast_nonneg _
  have hall := (Finset.sum_eq_zero_iff_of_nonneg hnonneg).mp hs
  have hmem : y ∈ (Set.toFinite (Ysub x t)).toFinset :=
    Set.Finite.mem_toFinset _ |>.mpr hy
  have h1 : (Work.BSW.iFn G y : ℤ) = 0 := hall y hmem
  exact_mod_cast h1

/-! ## `|C_G(y)|` for `y ∈ Y` -/

theorem even_card_K (h : BSWHyps2 G t s K) : Even (Nat.card K) := by
  have hdvd : 2 ∣ Nat.card K := by
    rw [← Work.BSW.orderOf_t h]
    exact Subgroup.orderOf_dvd_natCard _ (Work.BSW.t_mem_K h)
  exact even_iff_two_dvd.mpr hdvd

theorem coprime_of_no_common_prime {a b : ℕ}
    (h : ∀ p, p.Prime → p ∣ a → p ∣ b → False) : Nat.Coprime a b := by
  rw [Nat.coprime_iff_gcd_eq_one]
  by_contra hc
  obtain ⟨p, hp, hpd⟩ := Nat.exists_prime_and_dvd hc
  exact h p hp (hpd.trans (Nat.gcd_dvd_left a b)) (hpd.trans (Nat.gcd_dvd_right a b))

/-- `C_G(x)` is a Hall subgroup. -/
theorem coprime_card_centralizer_x (h : BSWHyps2 G t s K)
    (hG : Nat.card G = (2 * Nat.card K - 1) * (Nat.card K - 1) * (2 * Nat.card K))
    (hk : 4 < Nat.card K)
    (hf : Nat.card (Subgroup.centralizer ({x} : Set G)) = Nat.card K - 1) :
    Nat.Coprime (Nat.card (Subgroup.centralizer ({x} : Set G)))
      (Subgroup.centralizer ({x} : Set G)).index := by
  have heven : Even (Nat.card K) := even_card_K h
  rw [hf, index_centralizer_x_s35 h hG hk hf]
  have h1 : Nat.Coprime (Nat.card K - 1) (2 * Nat.card K - 1) := by
    apply coprime_of_no_common_prime
    intro p hp hpa hpb
    have hdvd : p ∣ (2 * Nat.card K - 1) - 2 * (Nat.card K - 1) :=
      Nat.dvd_sub hpb (dvd_mul_of_dvd_right hpa 2)
    have h2 : (2 * Nat.card K - 1) - 2 * (Nat.card K - 1) = 1 := by omega
    rw [h2] at hdvd
    exact hp.not_dvd_one hdvd
  have h2 : Nat.Coprime (Nat.card K - 1) (2 * Nat.card K) := by
    apply coprime_of_no_common_prime
    intro p hp hpa hpb
    rcases hp.dvd_mul.mp hpb with h' | h'
    · have hp2 : p = 2 := ((Nat.dvd_prime Nat.prime_two).mp h').resolve_left hp.ne_one
      rw [hp2] at hpa
      rcases heven with ⟨j, hj⟩
      omega
    · have hdvd : p ∣ Nat.card K - (Nat.card K - 1) := Nat.dvd_sub h' hpa
      have h3 : Nat.card K - (Nat.card K - 1) = 1 := by omega
      rw [h3] at hdvd
      exact hp.not_dvd_one hdvd
  exact h1.mul_right h2

/-- Every prime divisor of `|C_G(y)|`, for `y ∈ Y`, is coprime to `(k-1)·2k`. -/
theorem centralizer_card_dvd_sub_one (h : BSWHyps2 G t s K) (hx : x ∉ HG t)
    (hinv : t⁻¹ * x * t = x⁻¹)
    (hf : Nat.card (Subgroup.centralizer ({x} : Set G)) = Nat.card K - 1)
    (hG : Nat.card G = (2 * Nat.card K - 1) * (Nat.card K - 1) * (2 * Nat.card K))
    (hk : 4 < Nat.card K) {y : G} (hy : y ∈ Ysub x t) :
    Nat.card (Subgroup.centralizer ({y} : Set G)) ∣ 2 * Nat.card K - 1 := by
  set F : Subgroup G := Subgroup.centralizer ({x} : Set G) with hFdef
  have hFcard : Nat.card F = Nat.card K - 1 := by rw [hFdef]; exact hf
  have hcopF : Nat.Coprime (Nat.card F) F.index := by
    rw [hFdef]; exact coprime_card_centralizer_x h hG hk hf
  have hcopH : Nat.Coprime (Nat.card (Subgroup.centralizer ({t} : Set G)))
      (Subgroup.centralizer ({t} : Set G)).index := by
    rw [card_centralizer_t_s35 h]
    exact Work.BSW.Cases.Order.hallProp h
  have hodd : Odd (Nat.card (Subgroup.centralizer ({y} : Set G))) :=
    odd_card_centralizer_of_notMem_HG h hy.1
  have hcop : Nat.Coprime (Nat.card (Subgroup.centralizer ({y} : Set G)))
      ((Nat.card K - 1) * (2 * Nat.card K)) := by
    apply coprime_of_no_common_prime
    intro r hr hrd hrm
    have hrne2 : r ≠ 2 := by
      rintro rfl
      exact Nat.not_even_iff_odd.mpr hodd (even_iff_two_dvd.mpr hrd)
    haveI : Fact r.Prime := ⟨hr⟩
    obtain ⟨z, hzord⟩ := exists_prime_orderOf_dvd_card'
      (G := ↥(Subgroup.centralizer ({y} : Set G))) r hrd
    have hzgord : orderOf ((z : G)) = r := by rw [Subgroup.orderOf_coe z, hzord]
    have hzy : y * (z : G) = (z : G) * y :=
      (Subgroup.mem_centralizer_singleton_iff.mp z.2).symm
    rcases hr.dvd_mul.mp hrm with hrk1 | hr2k
    · have hrdvdF : r ∣ Nat.card F := by rw [hFcard]; exact hrk1
      obtain ⟨g, hg⟩ := hallConj hcopF hr hzgord hrdvdF
      have hz1 : (z : G) ≠ 1 := by
        intro h1
        rw [h1, orderOf_one] at hzgord
        exact hr.ne_one hzgord.symm
      have hgz1 : g * (z : G) * g⁻¹ ≠ 1 := by
        intro h1
        exact hz1 (by
          calc (z : G) = g⁻¹ * (g * (z : G) * g⁻¹) * g := by group
            _ = 1 := by rw [h1]; group)
      have hcommg : (g * y * g⁻¹) * (g * (z : G) * g⁻¹)
          = (g * (z : G) * g⁻¹) * (g * y * g⁻¹) := by
        calc (g * y * g⁻¹) * (g * (z : G) * g⁻¹) = g * (y * (z : G)) * g⁻¹ := by group
          _ = g * ((z : G) * y) * g⁻¹ := by rw [hzy]
          _ = (g * (z : G) * g⁻¹) * (g * y * g⁻¹) := by group
      have hygF : g * y * g⁻¹ ∈ F := by
        rw [hFdef,
          ← centralizer_eq_of_mem_centralizer h hx hinv (g * (z : G) * g⁻¹) hg hgz1]
        rw [Subgroup.mem_centralizer_singleton_iff]
        exact hcommg
      exact hy.2 ((Work.BSW.Cases.setOf_exists_conj_mem_eq_conjClassSet F).symm ▸ ⟨g, hygF⟩)
    · have hrk : r ∣ Nat.card K := by
        rcases hr.dvd_mul.mp hr2k with h' | h'
        · exact absurd (((Nat.dvd_prime Nat.prime_two).mp h').resolve_left hr.ne_one) hrne2
        · exact h'
      have hrdvdH : r ∣ Nat.card (Subgroup.centralizer ({t} : Set G)) := by
        rw [card_centralizer_t_s35 h]; exact dvd_mul_of_dvd_right hrk 2
      obtain ⟨g, hg⟩ := hallConj hcopH hr hzgord hrdvdH
      have hshow : orderOf (g * (z : G) * g⁻¹) = r := by
        rw [show g * (z : G) * g⁻¹ = (MulAut.conj g) (z : G) from by rw [MulAut.conj_apply],
          MulEquiv.orderOf_eq, hzgord]
      have hgzK : g * (z : G) * g⁻¹ ∈ K := by
        rcases (Work.BSW.Api.mem_centralizer_iff h (g * (z : G) * g⁻¹)).mp hg with h' | ⟨c, hc, hce⟩
        · exact h'
        · exfalso
          have h2 : orderOf (c * s) = 2 := orderOf_mul_s_eq_two h hc
          rw [← hce] at h2
          rw [hshow] at h2
          exact hrne2 h2
      have hz1 : (z : G) ≠ 1 := by
        intro h1
        rw [h1, orderOf_one] at hzgord
        exact hr.ne_one hzgord.symm
      have hgz1 : g * (z : G) * g⁻¹ ≠ 1 := by
        intro h1
        exact hz1 (by
          calc (z : G) = g⁻¹ * (g * (z : G) * g⁻¹) * g := by group
            _ = 1 := by rw [h1]; group)
      have hcommg : (g * y * g⁻¹) * (g * (z : G) * g⁻¹)
          = (g * (z : G) * g⁻¹) * (g * y * g⁻¹) := by
        calc (g * y * g⁻¹) * (g * (z : G) * g⁻¹) = g * (y * (z : G)) * g⁻¹ := by group
          _ = g * ((z : G) * y) * g⁻¹ := by rw [hzy]
          _ = (g * (z : G) * g⁻¹) * (g * y * g⁻¹) := by group
      exact hy.1 ⟨g, Work.BSW.Cases.mem_centralizer_of_commute_mem_K h hgzK hgz1 hcommg⟩
  have hdvdG : Nat.card (Subgroup.centralizer ({y} : Set G)) ∣ Nat.card G :=
    ⟨_, (Subgroup.card_mul_index _).symm⟩
  have hdvd : Nat.card (Subgroup.centralizer ({y} : Set G))
      ∣ (2 * Nat.card K - 1) * ((Nat.card K - 1) * (2 * Nat.card K)) := by
    have hGeq : Nat.card G = (2 * Nat.card K - 1) * ((Nat.card K - 1) * (2 * Nat.card K)) := by
      rw [hG]; ring
    rw [← hGeq]; exact hdvdG
  exact hcop.dvd_of_dvd_mul_right hdvd

/-- `|C_G(y)| = 2k-1` for `y ∈ Y`. -/
theorem card_centralizer_Ysub (h : BSWHyps2 G t s K) (hx : x ∉ HG t)
    (hinv : t⁻¹ * x * t = x⁻¹)
    (hf : Nat.card (Subgroup.centralizer ({x} : Set G)) = Nat.card K - 1)
    (hM : Nat.card (Subgroup.normalizer (Subgroup.centralizer ({x} : Set G) : Set G)) =
      2 * (Nat.card K - 1))
    (hG : Nat.card G = (2 * Nat.card K - 1) * (Nat.card K - 1) * (2 * Nat.card K))
    (hk : 4 < Nat.card K) {y : G} (hy : y ∈ Ysub x t) :
    Nat.card (Subgroup.centralizer ({y} : Set G)) = 2 * Nat.card K - 1 := by
  set d : ℕ := Nat.card (Subgroup.centralizer ({y} : Set G)) with hddef
  have hdvd : d ∣ 2 * Nat.card K - 1 := by
    rw [hddef]; exact centralizer_card_dvd_sub_one h hx hinv hf hG hk hy
  obtain ⟨m, hm⟩ := hdvd
  have hdpos : 0 < d := by rw [hddef]; exact Nat.card_pos
  have hmpos : 0 < m := by
    rcases Nat.eq_zero_or_pos m with h' | h'
    · rw [h', mul_zero] at hm; omega
    · exact h'
  have hmodd : Odd m := by
    have hodd2k : Odd (d * m) := by
      rw [← hm]; exact ⟨Nat.card K - 1, by omega⟩
    exact Odd.of_dvd_nat hodd2k (dvd_mul_left m d)
  have hclass : d * (conjugatesOf y).ncard = Nat.card G := by
    rw [hddef, ← Subgroup.index_centralizer_eq_ncard y]
    exact Subgroup.card_mul_index _
  have hle : (conjugatesOf y).ncard ≤ (Ysub x t).ncard := by
    apply Set.ncard_le_ncard
    · rintro w hw
      obtain ⟨g, hg⟩ := isConj_iff.mp hw
      rw [← hg]
      exact Ysub_conj h hy
    · exact Set.toFinite _
  have hYcard := ncard_Ysub h hx hinv hf hM hG hk
  have hcl : (conjugatesOf y).ncard = m * (Nat.card K - 1) * (2 * Nat.card K) := by
    have h2 : d * (conjugatesOf y).ncard = d * (m * (Nat.card K - 1) * (2 * Nat.card K)) := by
      rw [hclass, hG, hm]; ring
    exact Nat.eq_of_mul_eq_mul_left hdpos h2
  have hbound : m * (Nat.card K - 1) * (2 * Nat.card K) ≤ 4 * Nat.card K * (Nat.card K - 1) := by
    rw [← hcl]
    exact hle.trans (le_of_eq hYcard)
  have hfac : 0 < (Nat.card K - 1) * (2 * Nat.card K) :=
    Nat.mul_pos (by omega) (by omega)
  have h1 : m * ((Nat.card K - 1) * (2 * Nat.card K))
      ≤ 2 * ((Nat.card K - 1) * (2 * Nat.card K)) := by
    have hrw1 : m * (Nat.card K - 1) * (2 * Nat.card K)
        = m * ((Nat.card K - 1) * (2 * Nat.card K)) := by ring
    have hrw2 : 4 * Nat.card K * (Nat.card K - 1)
        = 2 * ((Nat.card K - 1) * (2 * Nat.card K)) := by ring
    rw [hrw1, hrw2] at hbound
    exact hbound
  have hmle : m ≤ 2 := Nat.le_of_mul_le_mul_right h1 hfac
  have hm1 : m = 1 := by rcases hmodd with ⟨j, hj⟩; omega
  have : d = 2 * Nat.card K - 1 := by rw [hm, hm1, mul_one]
  rw [hddef] at this
  exact this

/-- Every non-identity element of `C_G(y)`, for `y ∈ Y`, lies in `Y`. -/
theorem mem_Ysub_of_mem_centralizer (h : BSWHyps2 G t s K) (hx : x ∉ HG t)
    (hinv : t⁻¹ * x * t = x⁻¹)
    (hf : Nat.card (Subgroup.centralizer ({x} : Set G)) = Nat.card K - 1)
    (hM : Nat.card (Subgroup.normalizer (Subgroup.centralizer ({x} : Set G) : Set G)) =
      2 * (Nat.card K - 1))
    (hG : Nat.card G = (2 * Nat.card K - 1) * (Nat.card K - 1) * (2 * Nat.card K))
    (hk : 4 < Nat.card K) {y : G} (hy : y ∈ Ysub x t) {z : G}
    (hz : z ∈ Subgroup.centralizer ({y} : Set G)) (hz1 : z ≠ 1) : z ∈ Ysub x t := by
  set F : Subgroup G := Subgroup.centralizer ({x} : Set G) with hFdef
  have hdy := card_centralizer_Ysub h hx hinv hf hM hG hk hy
  have hzdvd : orderOf z ∣ 2 * Nat.card K - 1 := by
    rw [← hdy]
    exact Subgroup.orderOf_dvd_natCard _ hz
  have hzodd : Odd (orderOf z) :=
    Odd.of_dvd_nat (show Odd (2 * Nat.card K - 1) from ⟨Nat.card K - 1, by omega⟩) hzdvd
  have hzy : y * z = z * y := by
    rw [Subgroup.mem_centralizer_singleton_iff] at hz
    exact hz.symm
  refine ⟨?_, ?_⟩
  · intro hzH
    obtain ⟨g, hg⟩ := hzH
    have hgor : orderOf (g * z * g⁻¹) = orderOf z := by
      rw [show g * z * g⁻¹ = (MulAut.conj g) z from by rw [MulAut.conj_apply],
        MulEquiv.orderOf_eq]
    have hgzK : g * z * g⁻¹ ∈ K := by
      rcases (Work.BSW.Api.mem_centralizer_iff h (g * z * g⁻¹)).mp hg with h' | ⟨c, hc, hce⟩
      · exact h'
      · exfalso
        have h2 : orderOf (c * s) = 2 := orderOf_mul_s_eq_two h hc
        rw [← hce] at h2
        rw [hgor] at h2
        rw [h2] at hzodd
        rcases hzodd with ⟨j, hj⟩
        omega
    have hgz1 : g * z * g⁻¹ ≠ 1 := by
      intro h1
      exact hz1 (by
        calc z = g⁻¹ * (g * z * g⁻¹) * g := by group
          _ = 1 := by rw [h1]; group)
    have hcommg : (g * y * g⁻¹) * (g * z * g⁻¹) = (g * z * g⁻¹) * (g * y * g⁻¹) := by
      calc (g * y * g⁻¹) * (g * z * g⁻¹) = g * (y * z) * g⁻¹ := by group
        _ = g * (z * y) * g⁻¹ := by rw [hzy]
        _ = (g * z * g⁻¹) * (g * y * g⁻¹) := by group
    exact hy.1 ⟨g, Work.BSW.Cases.mem_centralizer_of_commute_mem_K h hgzK hgz1 hcommg⟩
  · intro hzF
    obtain ⟨g, hg⟩ := (Work.BSW.Cases.setOf_exists_conj_mem_eq_conjClassSet F).symm ▸ hzF
    have hgz1 : g * z * g⁻¹ ≠ 1 := by
      intro h1
      exact hz1 (by
        calc z = g⁻¹ * (g * z * g⁻¹) * g := by group
          _ = 1 := by rw [h1]; group)
    have hcommg : (g * y * g⁻¹) * (g * z * g⁻¹) = (g * z * g⁻¹) * (g * y * g⁻¹) := by
      calc (g * y * g⁻¹) * (g * z * g⁻¹) = g * (y * z) * g⁻¹ := by group
        _ = g * (z * y) * g⁻¹ := by rw [hzy]
        _ = (g * z * g⁻¹) * (g * y * g⁻¹) := by group
    have hygF : g * y * g⁻¹ ∈ F := by
      rw [hFdef, ← centralizer_eq_of_mem_centralizer h hx hinv (g * z * g⁻¹) hg hgz1]
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact hcommg
    exact hy.2 ((Work.BSW.Cases.setOf_exists_conj_mem_eq_conjClassSet F).symm ▸ ⟨g, hygF⟩)

/-! ## Bender §3.5 -/

theorem s35 : Work.BSW.BSWS35Prop := by
  intro G _ _ t s K x h hk hG hx hinv hf hM
  have hYcard := ncard_Ysub h hx hinv hf hM hG hk
  have hYpos : 0 < (Ysub x t).ncard := by
    rw [hYcard]
    exact Nat.mul_pos (Nat.mul_pos (by norm_num) (by omega)) (by omega)
  obtain ⟨y0, hy0⟩ := (Set.ncard_pos (Set.toFinite _)).mp hYpos
  haveI : Fintype G := Fintype.ofFinite G
  have hclass : ∀ z : G, z ∈ Ysub x t →
      (conjugatesOf z).ncard = 2 * Nat.card K * (Nat.card K - 1) := by
    intro z hz
    have hd := card_centralizer_Ysub h hx hinv hf hM hG hk hz
    have h1 : Nat.card (Subgroup.centralizer ({z} : Set G)) * (conjugatesOf z).ncard
        = Nat.card G := by
      rw [← Subgroup.index_centralizer_eq_ncard z]
      exact Subgroup.card_mul_index _
    rw [hd, hG] at h1
    have h1' : (2 * Nat.card K - 1) * (conjugatesOf z).ncard
        = (2 * Nat.card K - 1) * ((Nat.card K - 1) * (2 * Nat.card K)) := by
      rw [h1]; ring
    have h2 := Nat.eq_of_mul_eq_mul_left (by omega : 0 < 2 * Nat.card K - 1) h1'
    rw [h2]; ring
  have hnotconj : ∀ z : G, z ∈ Ysub x t → ¬ IsConj z z⁻¹ := by
    intro z hz hc
    have hz1 : z ≠ 1 := by rintro rfl; exact hz.1 ⟨1, by simp⟩
    have hoddz : Odd (Nat.card (Subgroup.centralizer ({z} : Set G))) := by
      rw [card_centralizer_Ysub h hx hinv hf hM hG hk hz]
      exact ⟨Nat.card K - 1, by omega⟩
    obtain ⟨u, hu2, hu⟩ := exists_involution_inverts_of_isConj_inv hz1 hoddz hc
    have hpos : 0 < Work.BSW.iFn G z := by
      rw [Work.BSW.iFn]
      exact (Set.ncard_pos (Set.toFinite _)).mpr ⟨u, hu2, hu⟩
    rw [iFn_eq_zero_of_mem_Ysub h hx hinv hf hM hG hk hz] at hpos
    exact lt_irrefl 0 hpos
  have hsames := order_eq_of_two_classes (Y := Ysub x t)
    (a := 2 * Nat.card K * (Nat.card K - 1))
    (fun g z hz => Ysub_conj h hz) (fun z hz => Ysub_inv h hz) hclass
    (by rw [hYcard]; ring) hnotconj
  have hy0ne1 : y0 ≠ 1 := by rintro rfl; exact hy0.1 ⟨1, by simp⟩
  have hprime : (orderOf y0).Prime :=
    prime_orderOf_of_centralizer_subset hy0ne1 rfl
      (fun z hz => hsames z y0 hz hy0)
      (fun z hz hz1 => mem_Ysub_of_mem_centralizer h hx hinv hf hM hG hk hy0 hz hz1)
  have hc0 := card_centralizer_Ysub h hx hinv hf hM hG hk hy0
  have hpow : ∃ e : ℕ, 2 * Nat.card K - 1 = (orderOf y0) ^ e := by
    haveI : Fact (orderOf y0).Prime := ⟨hprime⟩
    have hpg : IsPGroup (orderOf y0) ↥(Subgroup.centralizer ({y0} : Set G)) := by
      intro z
      refine ⟨1, ?_⟩
      rw [pow_one]
      by_cases hz1 : ((z : G)) = 1
      · refine Subtype.ext ?_
        show ((z : G)) ^ orderOf y0 = (1 : G)
        rw [hz1]; simp
      · have hzY : ((z : G)) ∈ Ysub x t :=
          mem_Ysub_of_mem_centralizer h hx hinv hf hM hG hk hy0 z.2 hz1
        have hz' : orderOf ((z : G)) = orderOf y0 := hsames (z : G) y0 hzY hy0
        refine Subtype.ext ?_
        show ((z : G)) ^ orderOf y0 = (1 : G)
        rw [← hz']
        exact pow_orderOf_eq_one ((z : G))
    obtain ⟨e, he⟩ := IsPGroup.iff_card.mp hpg
    exact ⟨e, by rw [← hc0, he]⟩
  refine ⟨orderOf y0, h, hk, hG, hx, hinv, hf, hM, hprime, hpow, ?_⟩
  intro y hy1 hyH hyF
  have hyY : y ∈ Ysub x t := by
    refine ⟨hyH, ?_⟩
    rw [← Work.BSW.Cases.setOf_exists_conj_mem_eq_conjClassSet
      (Subgroup.centralizer ({x} : Set G))]
    intro hcon
    obtain ⟨g, hg⟩ := hcon
    exact hyF g hg
  exact ⟨card_centralizer_Ysub h hx hinv hf hM hG hk hyY,
    hsames y y0 hyY hy0, hnotconj y hyY⟩

end Work.BSW.S3
