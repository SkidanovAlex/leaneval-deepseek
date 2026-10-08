import Mathlib
import Submission.Work.AUTA7.Defs
import Submission.Work.AUTA7.A7.D16MaxIntersect
import Submission.Work.AUTA7.A7.dihedral_subgroup_isCyclic_or_dihedral
import Submission.Work.AUTA7.A7.exists_subgroup_index_two_of_isPGroup_two
import Submission.Work.AUTA7.A7.A7InvolutionLocal
import Submission.Work.AUTA7.A7.sylow_two_of_A7_iso_dihedral
import Submission.Work.AUTA7.A7.a7_local_of_iso
import Submission.Work.AUTA7.A7.eq_of_card_three_of_normal_in_card_twentyfour
import Submission.Work.AUTA7.A7.contradiction_of_four_group
import Submission.Work.AUTA7.A7.reduce_to_index_two

namespace Work.AUTA7.A7

open Subgroup

set_option maxHeartbeats 1000000
set_option linter.style.haveILetI false

/-! ## Auxiliary facts -/

/-- A subgroup of order `4` all of whose elements are involutions is not cyclic. -/
theorem not_isCyclic_of_card_four {G : Type*} [Group G] (V : Subgroup G)
    (hcard : Nat.card ↥V = 4) (hexp : ∀ v ∈ V, v ^ 2 = 1) : ¬ IsCyclic V := by
  intro hcyc
  haveI := hcyc
  obtain ⟨v, hv⟩ := IsCyclic.exists_generator (α := ↥V)
  have htop : Subgroup.zpowers v = ⊤ := by
    ext x; exact ⟨fun _ => trivial, fun _ => hv x⟩
  have hord : orderOf v = 4 := by
    rw [← Nat.card_zpowers (a := v), htop, Subgroup.card_top, hcard]
  have h2 : (v : G) * (v : G) = 1 := by
    have := hexp (v : G) v.2
    rwa [sq] at this
  have h3 : orderOf (v : G) = orderOf v :=
    orderOf_injective (Subgroup.subtype V) Subtype.val_injective v
  have hdvd : orderOf (v : G) ∣ 2 := orderOf_dvd_iff_pow_eq_one.mpr (by rw [pow_two]; exact h2)
  have hle : orderOf (v : G) ≤ 2 := Nat.le_of_dvd (by norm_num) hdvd
  omega

/-! ## The index `2` case -/

/-- **The index `2` case is impossible.**  A finite group `Q` with a normal subgroup `L ≅ A₇`,
trivial centralizer and cyclic-or-dihedral Sylow `2`-subgroups cannot have `[Q : L] = 2`. -/
theorem index_two_core (Q : Type) [Group Q] [Finite Q] (L : Subgroup Q) (hL : L.Normal)
    (φ : L ≃* alternatingGroup (Fin 7))
    (hC : Subgroup.centralizer (L : Set Q) = ⊥)
    (hS : Work.GW2.DihOrCycSylow Q)
    (hidx : L.index = 2) : False := by
  classical
  have hcardL : Nat.card ↥L = 2520 := by
    rw [Nat.card_congr φ.toEquiv, Work.A7.card_alternatingGroup_seven]
  have hcardQ : Nat.card Q = 2520 * 2 := by
    have h := Subgroup.card_mul_index L
    rw [hcardL, hidx] at h
    omega
  obtain ⟨P⟩ := Sylow.nonempty (p := 2) (G := Q)
  set D : Subgroup Q := (P : Subgroup Q) ⊓ L with hDdef
  have hcardD : Nat.card ↥D = 8 := by
    rw [hDdef]
    exact Work.AUTA7.GroupTheory.CardInfSylowTwo L hL hcardL P
  have hDP : D ≤ (P : Subgroup Q) := by rw [hDdef]; exact inf_le_left
  have hDL : D ≤ L := by rw [hDdef]; exact inf_le_right
  have hfac5040 : (2520 * 2 : ℕ).factorization 2 = 4 := by
    rw [show (2520 * 2 : ℕ) = 2 ^ 4 * 315 from by norm_num,
      Nat.factorization_mul (by norm_num) (by norm_num : (315 : ℕ) ≠ 0)]
    rw [Finsupp.add_apply, Nat.factorization_pow_self Nat.prime_two,
      Nat.factorization_eq_zero_of_not_dvd (by norm_num : ¬ (2 : ℕ) ∣ 315)]
  have hcardP : Nat.card ↥(P : Subgroup Q) = 16 := by
    rw [Sylow.card_eq_multiplicity, hcardQ, hfac5040]; norm_num
  have hcardDsubL : Nat.card ↥(D.subgroupOf L) = 8 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hDL).toEquiv, hcardD]
  have hDnotcyc : ¬ IsCyclic D := by
    obtain ⟨e⟩ := sylow_two_of_A7_iso_dihedral φ (D.subgroupOf L) hcardDsubL
    intro hc
    haveI := hc
    have hc' : IsCyclic ↥(D.subgroupOf L) :=
      isCyclic_of_surjective ((Subgroup.subgroupOfEquivOfLe hDL).symm :
        D →* D.subgroupOf L) (Subgroup.subgroupOfEquivOfLe hDL).symm.surjective
    exact DihedralGroup.not_isCyclic (n := 4) (by decide)
      (isCyclic_of_surjective (e : D.subgroupOf L →* DihedralGroup 4) e.surjective)
  have hPnotcyc : ¬ IsCyclic (P : Subgroup Q) := by
    intro hc
    haveI := hc
    apply hDnotcyc
    haveI : IsCyclic (D.subgroupOf (P : Subgroup Q)) := inferInstance
    exact isCyclic_of_surjective
      (Subgroup.subgroupOfEquivOfLe hDP : D.subgroupOf (P : Subgroup Q) →* D)
      (Subgroup.subgroupOfEquivOfLe hDP).surjective
  rcases hS P with hcyc | ⟨m, hψ⟩
  · exact absurd hcyc hPnotcyc
  obtain ⟨ψ⟩ := hψ
  have hm : m = 8 := by
    have h := Nat.card_congr ψ.toEquiv
    rw [DihedralGroup.nat_card, hcardP] at h
    omega
  subst hm
  -- the central involution of `P`
  let zP : ↥(P : Subgroup Q) := ψ.symm (DihedralGroup.r 4)
  have hzP_psi : ψ zP = DihedralGroup.r 4 := by simp [zP]
  let z : Q := (zP : Q)
  have hzP_center : ∀ x : ↥(P : Subgroup Q), x * zP = zP * x := by
    intro x
    have hr4 : (DihedralGroup.r 4 : DihedralGroup 8) ∈ Subgroup.center (DihedralGroup 8) := by
      rw [DihedralGroup.center_eq_closure_of_even_ne_two (by decide) (by decide)]
      exact Subgroup.mem_zpowers _
    have h := (Subgroup.mem_center_iff.mp hr4) (ψ x)
    have hψ : ψ (x * zP) = ψ (zP * x) := by
      rw [map_mul, map_mul, hzP_psi]; exact h
    exact ψ.injective hψ
  have hcardDsub : Nat.card ↥(D.subgroupOf (P : Subgroup Q)) = 8 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hDP).toEquiv, hcardD]
  have hidx2 : ((D.subgroupOf (P : Subgroup Q)).map
      (ψ : ↥(P : Subgroup Q) →* DihedralGroup 8)).index = 2 := by
    have hcardimg : Nat.card ↥((D.subgroupOf (P : Subgroup Q)).map
        (ψ : ↥(P : Subgroup Q) →* DihedralGroup 8)) = 8 := by
      rw [Subgroup.card_map_of_injective
        (f := (ψ : ↥(P : Subgroup Q) →* DihedralGroup 8)) ψ.injective, hcardDsub]
    have h := Subgroup.card_mul_index ((D.subgroupOf (P : Subgroup Q)).map
        (ψ : ↥(P : Subgroup Q) →* DihedralGroup 8))
    rw [hcardimg, DihedralGroup.nat_card] at h
    omega
  have hr4mem : (DihedralGroup.r 4 : DihedralGroup 8) ∈
      (D.subgroupOf (P : Subgroup Q)).map (ψ : ↥(P : Subgroup Q) →* DihedralGroup 8) := by
    have h := Subgroup.sq_mem_of_index_two hidx2 (DihedralGroup.r 2 : DihedralGroup 8)
    have h2 : (DihedralGroup.r 2 : DihedralGroup 8) ^ 2 = DihedralGroup.r 4 := by
      rw [pow_two, DihedralGroup.r_mul_r]; decide
    rwa [h2] at h
  have hzPD : zP ∈ D.subgroupOf (P : Subgroup Q) := by
    obtain ⟨x, hx, hxψ⟩ := Subgroup.mem_map.mp hr4mem
    have hxψ' : ψ x = DihedralGroup.r 4 := hxψ
    have : x = zP := ψ.injective (by rw [hxψ', hzP_psi])
    rwa [this] at hx
  have hzD : z ∈ D := Subgroup.mem_subgroupOf.mp hzPD
  have hzL : z ∈ L := hDL hzD
  have hz_ord : orderOf z = 2 := by
    have h1 : orderOf (ψ zP) = orderOf zP :=
      orderOf_injective (ψ : ↥(P : Subgroup Q) →* DihedralGroup 8) ψ.injective zP
    rw [hzP_psi] at h1
    have h2 : orderOf (DihedralGroup.r 4 : DihedralGroup 8) = 2 := by
      rw [DihedralGroup.orderOf_r]; decide
    have h3 : orderOf (zP : Q) = orderOf zP :=
      orderOf_injective (Subgroup.subtype (P : Subgroup Q)) Subtype.val_injective zP
    have h4 : (zP : Q) = z := rfl
    rw [← h4, h3, ← h1, h2]
  -- the `A₇`-local data, transported to `L`
  have hzL_ord : orderOf (⟨z, hzL⟩ : L) = 2 :=
    (orderOf_injective (Subgroup.subtype L) Subtype.val_injective (⟨z, hzL⟩ : L)).symm.trans hz_ord
  obtain ⟨hcard_CLz, K_L, hKL_le, hKL_norm, hKL_card, hCKL_card, hNKL_card, h2sub, hno4⟩ :=
    a7_local_of_iso A7InvolutionLocal φ ⟨z, hzL⟩ hzL_ord
  -- the subgroups of `Q`
  set CLz : Subgroup Q := (Subgroup.centralizer ({⟨z, hzL⟩} : Set L)).map L.subtype with hCLzdef
  set K : Subgroup Q := K_L.map L.subtype with hKdef
  set CK : Subgroup Q := Subgroup.centralizer (K : Set Q) with hCKdef
  set CLK : Subgroup Q := (Subgroup.centralizer (K_L : Set L)).map L.subtype with hCLKdef
  set NK : Subgroup Q := Subgroup.normalizer (K : Set Q) with hNKdef
  set NLK : Subgroup Q := (Subgroup.normalizer (K_L : Set L)).map L.subtype with hNLKdef
  have hcardCLz : Nat.card ↥CLz = 24 := by
    rw [hCLzdef,
      Subgroup.card_map_of_injective (f := L.subtype) Subtype.val_injective, hcard_CLz]
  have hcardK : Nat.card ↥K = 3 := by
    rw [hKdef, Subgroup.card_map_of_injective (f := L.subtype) Subtype.val_injective, hKL_card]
  have hcardCLK : Nat.card ↥CLK = 36 := by
    rw [hCLKdef, Subgroup.card_map_of_injective (f := L.subtype) Subtype.val_injective, hCKL_card]
  have hcardNLK : Nat.card ↥NLK = 72 := by
    rw [hNLKdef, Subgroup.card_map_of_injective (f := L.subtype) Subtype.val_injective, hNKL_card]
  have hKleL : K ≤ L := by
    rw [hKdef]
    rintro x ⟨y, hy, rfl⟩
    exact y.2
  have hCLKleL : CLK ≤ L := by
    rw [hCLKdef]
    rintro x ⟨y, hy, rfl⟩
    exact y.2
  have hKleCLz : K ≤ CLz := by
    rw [hKdef, hCLzdef]
    exact Subgroup.map_mono hKL_le
  have hKnorm : (K.subgroupOf CLz).Normal := by
    rw [Subgroup.normal_subgroupOf_iff hKleCLz]
    intro a b ha hb
    rw [hKdef] at ha
    obtain ⟨a₀, ha₀, rfl⟩ := Subgroup.mem_map.mp ha
    rw [hCLzdef] at hb
    obtain ⟨b₀, hb₀, rfl⟩ := Subgroup.mem_map.mp hb
    rw [hKdef]
    exact Subgroup.mem_map.mpr ⟨b₀ * a₀ * b₀⁻¹,
      (Subgroup.normal_subgroupOf_iff hKL_le).mp hKL_norm a₀ b₀ ha₀ hb₀, rfl⟩
  -- transfer of the `A₇`-local bounds for `2`-groups and elements of order `4`
  have h2subQ : ∀ P : Subgroup Q, P ≤ CLK → IsPGroup 2 ↥P → Nat.card ↥P ≤ 4 := by
    intro Pname hP hPg
    have hPL : Pname ≤ L := hP.trans hCLKleL
    have hsub : Pname.subgroupOf L ≤ Subgroup.centralizer (K_L : Set L) := by
      intro x hx
      have hxP : (x : Q) ∈ Pname := Subgroup.mem_subgroupOf.mp hx
      obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.mp (hCLKdef ▸ hP hxP)
      have : y = x := Subtype.ext hyx
      rwa [this] at hy
    have hisP : IsPGroup 2 ↥(Pname.subgroupOf L) :=
      hPg.of_equiv (Subgroup.subgroupOfEquivOfLe hPL).symm
    have := h2sub (Pname.subgroupOf L) hsub hisP
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hPL).toEquiv] at this
    exact this
  have hno4Q : ∀ x ∈ CLK, orderOf x ≠ 4 := by
    intro x hx h4
    obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.mp (hCLKdef ▸ hx)
    have hord : orderOf y = orderOf x :=
      (orderOf_injective (Subgroup.subtype L) Subtype.val_injective y).symm.trans (by rw [hyx])
    exact hno4 y hy (hord.trans h4)
  -- `z` is central in `P`
  have hz_comm : ∀ p : ↥(P : Subgroup Q), (p : Q) * z = z * (p : Q) := fun p =>
    congrArg (fun y : ↥(P : Subgroup Q) => (y : Q)) (hzP_center p)
  have hCLz_conj : ∀ p : ↥(P : Subgroup Q), ∀ c ∈ CLz, (p : Q) * c * (p : Q)⁻¹ ∈ CLz := by
    intro p c hc
    rw [hCLzdef] at hc ⊢
    obtain ⟨c₀, hc₀, rfl⟩ := Subgroup.mem_map.mp hc
    have hpz : (p : Q) * z * (p : Q)⁻¹ = z := by rw [hz_comm p]; group
    have hpinvz : (p : Q)⁻¹ * z * (p : Q) = z := by
      calc (p : Q)⁻¹ * z * (p : Q)
          = (p : Q)⁻¹ * ((p : Q) * z * (p : Q)⁻¹) * (p : Q) := by rw [hpz]
        _ = z := by group
    refine Subgroup.mem_map.mpr
      ⟨⟨(p : Q) * (c₀ : Q) * (p : Q)⁻¹,
        hL.conj_mem (c₀ : Q) (show (c₀ : Q) ∈ L from (c₀ : L).2) p⟩, ?_, rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff] at hc₀ ⊢
    refine Subtype.ext ?_
    have hc₀' : (c₀ : Q) * z = z * (c₀ : Q) := congrArg (fun y : L => (y : Q)) hc₀
    calc (p : Q) * (c₀ : Q) * (p : Q)⁻¹ * z
        = (p : Q) * (c₀ : Q) * ((p : Q)⁻¹ * z * (p : Q)) * (p : Q)⁻¹ := by group
      _ = (p : Q) * (c₀ : Q) * z * (p : Q)⁻¹ := by rw [hpinvz]
      _ = (p : Q) * ((c₀ : Q) * z) * (p : Q)⁻¹ := by group
      _ = (p : Q) * (z * (c₀ : Q)) * (p : Q)⁻¹ := by rw [hc₀']
      _ = ((p : Q) * z * (p : Q)⁻¹) * ((p : Q) * (c₀ : Q) * (p : Q)⁻¹) := by group
      _ = z * ((p : Q) * (c₀ : Q) * (p : Q)⁻¹) := by rw [hpz]
  have hP_le_NK : (P : Subgroup Q) ≤ NK := by
    intro p hp
    have hK'le : K.map (MulAut.conj (p : Q)).toMonoidHom ≤ CLz := by
      rintro y ⟨k, hk, rfl⟩
      simpa [MulAut.conj_apply] using hCLz_conj ⟨p, hp⟩ k (hKleCLz hk)
    have hK'eq : K.map (MulAut.conj (p : Q)).toMonoidHom = K := by
      refine (eq_of_card_three_of_normal_in_card_twentyfour (Z := CLz) (K := K)
        (L := K.map (MulAut.conj (p : Q)).toMonoidHom) hKleCLz hK'le hKnorm hcardK ?_ hcardCLz).symm
      rw [Subgroup.card_map_of_injective (f := (MulAut.conj (p : Q)).toMonoidHom)
        (MulAut.conj (p : Q)).injective, hcardK]
    rw [hNKdef, Subgroup.mem_normalizer_iff]
    intro k
    constructor
    · intro hk
      have hmem : (p : Q) * k * (p : Q)⁻¹ ∈ K.map (MulAut.conj (p : Q)).toMonoidHom :=
        Subgroup.mem_map.mpr ⟨k, hk, by simp [MulAut.conj_apply]⟩
      rwa [hK'eq] at hmem
    · intro hk
      rw [← hK'eq] at hk
      obtain ⟨k', hk', hk'eq⟩ := Subgroup.mem_map.mp hk
      have hkk : k' = k := by
        apply (MulAut.conj (p : Q)).injective
        simpa [MulAut.conj_apply] using hk'eq
      rwa [← hkk]
  have hPnotleL : ¬ (P : Subgroup Q) ≤ L := by
    intro hle
    have hDL' : D = (P : Subgroup Q) := by
      rw [hDdef]
      exact le_antisymm inf_le_left (le_inf le_rfl hle)
    rw [hDL', hcardP] at hcardD
    norm_num at hcardD
  -- `N_Q(K)` and `C_Q(K)`
  have hNLKleNK : NLK ≤ NK := by
    rw [hNKdef, hNLKdef, hKdef]
    exact Subgroup.le_normalizer_map L.subtype
  have hNLKleL : NLK ≤ L := by
    rw [hNLKdef]
    rintro x ⟨y, hy, rfl⟩
    exact y.2
  have hNKcard_ge : 144 ≤ Nat.card ↥NK := by
    have h := Subgroup.relIndex_mul_card NLK NK
    rw [inf_of_le_left hNLKleNK, hcardNLK] at h
    have hne : NLK.subgroupOf NK ≠ ⊤ := by
      intro htop
      have heq : NLK = NK := le_antisymm hNLKleNK (Subgroup.subgroupOf_eq_top.mp htop)
      exact hPnotleL (hP_le_NK.trans (heq ▸ hNLKleL))
    have hlt : 1 < (NLK.subgroupOf NK).index := Subgroup.one_lt_index_of_ne_top hne
    have : (NLK.subgroupOf NK).index = NLK.relIndex NK := rfl
    omega
  have hCKcard_ge : 72 ≤ Nat.card ↥CK := by
    have hcardAut : Nat.card (MulAut ↥K) = 2 := by
      haveI : IsCyclic ↥K := isCyclic_of_prime_card (p := 3) hcardK
      rw [IsCyclic.card_mulAut, hcardK, Nat.totient_prime Nat.prime_three]
    set f := Subgroup.normalizerMonoidHom K with hf
    have hker : f.ker = CK.subgroupOf NK := by
      rw [hf, Subgroup.normalizerMonoidHom_ker]
    have hCKleNK : CK ≤ NK := by
      rw [hCKdef, hNKdef]
      exact Subgroup.centralizer_le_normalizer (K : Set Q)
    have hker_card : Nat.card ↥f.ker = Nat.card ↥CK := by
      rw [hker]
      exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hCKleNK).toEquiv
    have hrange_le : Nat.card ↥f.range ≤ 2 := by
      have h1 := Subgroup.card_le_card_group (H := f.range)
      rw [hcardAut] at h1
      exact h1
    have hmain : Nat.card ↥CK * Nat.card ↥f.range = Nat.card ↥NK := by
      have h := Subgroup.card_ker_mul_card_range f
      rw [hker_card] at h
      exact h
    have hbound : Nat.card ↥CK * Nat.card ↥f.range ≤ Nat.card ↥CK * 2 :=
      Nat.mul_le_mul_left _ hrange_le
    rw [hmain] at hbound
    omega
  have hCKinfL : CK ⊓ L = CLK := by
    ext x
    constructor
    · intro hx
      obtain ⟨hxCK, hxL⟩ := Subgroup.mem_inf.mp hx
      rw [hCKdef, Subgroup.mem_centralizer_iff] at hxCK
      refine Subgroup.mem_map.mpr ⟨⟨x, hxL⟩, ?_, rfl⟩
      rw [Subgroup.mem_centralizer_iff]
      intro k hk
      have hkK : (k : Q) ∈ K := Subgroup.mem_map.mpr ⟨k, hk, rfl⟩
      exact Subtype.ext (hxCK (k : Q) hkK)
    · intro hx
      obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.mp (hCLKdef ▸ hx)
      rw [Subgroup.mem_inf]
      refine ⟨?_, ?_⟩
      · rw [hCKdef, Subgroup.mem_centralizer_iff]
        intro k hk
        obtain ⟨k₀, hk₀, hk₀k⟩ := Subgroup.mem_map.mp (hKdef ▸ hk)
        rw [Subgroup.mem_centralizer_iff] at hy
        rw [← hyx, ← hk₀k]
        exact congrArg (fun y : L => (y : Q)) (hy k₀ hk₀)
      · rw [← hyx]; exact y.2
  have hCLKleCK : CLK ≤ CK := by rw [← hCKinfL]; exact inf_le_left
  have hCKcard_le : Nat.card ↥CK ≤ 72 := by
    have h := Subgroup.relIndex_mul_card CLK CK
    rw [inf_of_le_left hCLKleCK, hcardCLK] at h
    have hrel_le : CLK.relIndex CK ≤ 2 := by
      have hLpos : 0 < Nat.card ↥L := Nat.card_pos
      have h1 : CLK.relIndex CK = (L.subgroupOf (CK ⊔ L)).index := by
        change CLK.relIndex CK = L.relIndex (CK ⊔ L)
        rw [← hCKinfL, inf_comm, Subgroup.inf_relIndex_right,
          ← Subgroup.relIndex_sup_right (H := CK) (K := L)]
      rw [h1]
      have hcard := Subgroup.card_mul_index (L.subgroupOf (CK ⊔ L))
      have hcardLsub : Nat.card ↥(L.subgroupOf (CK ⊔ L)) = Nat.card ↥L :=
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe le_sup_right).toEquiv
      rw [hcardLsub] at hcard
      have hle : Nat.card ↥(CK ⊔ L) ≤ Nat.card Q := Subgroup.card_le_card_group (H := CK ⊔ L)
      have hQ := Subgroup.card_mul_index L
      rw [hidx] at hQ
      have h2 : Nat.card ↥L * (L.subgroupOf (CK ⊔ L)).index ≤ Nat.card ↥L * 2 := by
        rw [hcard, hQ]
        exact hle
      exact Nat.le_of_mul_le_mul_left h2 hLpos
    omega
  have hCKcard : Nat.card ↥CK = 72 := le_antisymm hCKcard_le hCKcard_ge
  have hCKnotleL : ¬ CK ≤ L := by
    intro hle
    have : CK ⊓ L = CK := le_antisymm inf_le_left (le_inf le_rfl hle)
    rw [← this, hCKinfL, hcardCLK] at hCKcard
    norm_num at hCKcard
  -- `V := T_Q ⊓ L` is a four-group, where `T` is a Sylow of `C_Q(K)` chosen to contain
  -- a Sylow `2`-subgroup of `C_L(K)` (of order `4`)
  obtain ⟨W⟩ := Sylow.nonempty (p := 2) (G := ↥CLK)
  have hfac36 : (36 : ℕ).factorization 2 = 2 := by
    rw [show (36 : ℕ) = 2 ^ 2 * 9 from by norm_num,
      Nat.factorization_mul (by norm_num) (by norm_num : (9 : ℕ) ≠ 0)]
    rw [Finsupp.add_apply, Nat.factorization_pow_self Nat.prime_two,
      Nat.factorization_eq_zero_of_not_dvd (by norm_num : ¬ (2 : ℕ) ∣ 9)]
  have hcardW : Nat.card ↥(W : Subgroup ↥CLK) = 4 := by
    rw [Sylow.card_eq_multiplicity, hcardCLK, hfac36]; norm_num
  set W' : Subgroup ↥CK := (W : Subgroup ↥CLK).map (Subgroup.inclusion hCLKleCK) with hW'def
  have hcardW' : Nat.card ↥W' = 4 := by
    rw [hW'def, Subgroup.card_map_of_injective (f := Subgroup.inclusion hCLKleCK)
      (Subgroup.inclusion_injective hCLKleCK), hcardW]
  have hW'isP : IsPGroup 2 ↥W' := IsPGroup.of_card (n := 2) (by rw [hcardW']; norm_num)
  obtain ⟨T, hW'leT⟩ := hW'isP.exists_le_sylow
  set TQ : Subgroup Q := (T : Subgroup ↥CK).map CK.subtype with hTQdef
  have hcardT : Nat.card ↥(T : Subgroup ↥CK) = 8 := by
    rw [Sylow.card_eq_multiplicity, hCKcard]
    have hfac72 : (72 : ℕ).factorization 2 = 3 := by
      rw [show (72 : ℕ) = 2 ^ 3 * 9 from by norm_num,
        Nat.factorization_mul (by norm_num) (by norm_num : (9 : ℕ) ≠ 0)]
      rw [Finsupp.add_apply, Nat.factorization_pow_self Nat.prime_two,
        Nat.factorization_eq_zero_of_not_dvd (by norm_num : ¬ (2 : ℕ) ∣ 9)]
    rw [hfac72]; norm_num
  have hcardTQ : Nat.card ↥TQ = 8 := by
    rw [hTQdef, Subgroup.card_map_of_injective (f := CK.subtype) Subtype.val_injective, hcardT]
  have hTQleCK : TQ ≤ CK := by
    rw [hTQdef]
    rintro x ⟨y, hy, rfl⟩
    exact y.2
  have hTQisP : IsPGroup 2 ↥TQ := IsPGroup.of_card (by rw [hcardTQ, show (8:ℕ) = 2^3 from by norm_num])
  have hTQnotleL : ¬ TQ ≤ L := by
    intro hle
    have hinf : TQ ⊓ L = TQ := le_antisymm inf_le_left (le_inf le_rfl hle)
    have hsub : TQ ⊓ L ≤ CLK := by
      rw [← hCKinfL]
      exact le_inf (inf_le_left.trans hTQleCK) inf_le_right
    have hisP : IsPGroup 2 ↥(TQ ⊓ L) := IsPGroup.to_le hTQisP inf_le_left
    have hle4 := h2subQ (TQ ⊓ L) hsub hisP
    rw [hinf, hcardTQ] at hle4
    norm_num at hle4
  set V : Subgroup Q := TQ ⊓ L with hVdef
  have hVleTQ : V ≤ TQ := by rw [hVdef]; exact inf_le_left
  have hVleCLK : V ≤ CLK := by
    rw [hVdef, ← hCKinfL]
    exact le_inf (inf_le_left.trans hTQleCK) inf_le_right
  have hVcard_le : Nat.card ↥V ≤ 4 := by
    exact h2subQ V hVleCLK (IsPGroup.to_le hTQisP hVleTQ)
  have hWQleV : ((W : Subgroup ↥CLK).map CLK.subtype) ≤ V := by
    intro x hx
    obtain ⟨w, hw, rfl⟩ := Subgroup.mem_map.mp hx
    have hwW' : Subgroup.inclusion hCLKleCK w ∈ W' :=
      Subgroup.mem_map.mpr ⟨w, hw, rfl⟩
    have hwT : Subgroup.inclusion hCLKleCK w ∈ (T : Subgroup ↥CK) := hW'leT hwW'
    rw [hVdef, Subgroup.mem_inf]
    refine ⟨?_, ?_⟩
    · rw [hTQdef]
      exact Subgroup.mem_map.mpr ⟨Subgroup.inclusion hCLKleCK w, hwT, rfl⟩
    · exact hCLKleL w.2
  have hcardWQ : Nat.card ↥((W : Subgroup ↥CLK).map CLK.subtype) = 4 := by
    rw [Subgroup.card_map_of_injective (f := CLK.subtype) Subtype.val_injective, hcardW]
  have hVcard_ge : 4 ≤ Nat.card ↥V := by
    rw [← hcardWQ]
    exact Nat.card_le_card_of_injective _ (Subgroup.inclusion_injective hWQleV)
  have hVcard : Nat.card ↥V = 4 := le_antisymm hVcard_le hVcard_ge
  have hVexp : ∀ v ∈ V, v ^ 2 = 1 := by
    intro v hv
    have hvCLK : v ∈ CLK := hVleCLK hv
    have hdvd' : orderOf v ∣ 4 := by
      rw [show orderOf v = Nat.card ↥(Subgroup.zpowers (⟨v, hv⟩ : ↥V)) from by
        rw [Nat.card_zpowers, Subgroup.orderOf_mk], ← hVcard]
      exact Subgroup.card_subgroup_dvd_card (Subgroup.zpowers (⟨v, hv⟩ : ↥V))
    have hne4 : orderOf v ≠ 4 := hno4Q v hvCLK
    have hle2 : orderOf v ∣ 2 := by
      rcases (Nat.dvd_prime_pow (p := 2) (m := 2) Nat.prime_two).mp hdvd' with ⟨k, hk, hk2⟩
      interval_cases k
      · exact ⟨2, by rw [hk2]; norm_num⟩
      · exact ⟨1, by rw [hk2]; norm_num⟩
      · exact absurd (by rw [hk2]; norm_num : orderOf v = 4) hne4
    exact orderOf_dvd_iff_pow_eq_one.mp hle2
  -- `T_Q` is non-cyclic
  have hTQnotcyc : ¬ IsCyclic TQ := by
    intro hc
    haveI := hc
    have hcycV : IsCyclic ↥V :=
      isCyclic_of_surjective (Subgroup.subgroupOfEquivOfLe hVleTQ : V.subgroupOf TQ →* V)
        (Subgroup.subgroupOfEquivOfLe hVleTQ).surjective
    exact not_isCyclic_of_card_four V hVcard hVexp hcycV
  -- extend `T_Q` to a Sylow `2`-subgroup of `Q`
  obtain ⟨P₁, hTQleP₁⟩ := hTQisP.exists_le_sylow
  have hcardP₁ : Nat.card ↥(P₁ : Subgroup Q) = 16 := by
    rw [Sylow.card_eq_multiplicity, hcardQ, hfac5040]; norm_num
  have hP₁notcyc : ¬ IsCyclic (P₁ : Subgroup Q) := by
    intro hc
    haveI := hc
    apply hTQnotcyc
    haveI : IsCyclic (TQ.subgroupOf (P₁ : Subgroup Q)) := inferInstance
    exact isCyclic_of_surjective
      (Subgroup.subgroupOfEquivOfLe hTQleP₁ : TQ.subgroupOf (P₁ : Subgroup Q) →* TQ)
      (Subgroup.subgroupOfEquivOfLe hTQleP₁).surjective
  rcases hS P₁ with hcyc | ⟨m, hψ⟩
  · exact absurd hcyc hP₁notcyc
  obtain ⟨ψ₁⟩ := hψ
  have hm : m = 8 := by
    have h := Nat.card_congr ψ₁.toEquiv
    rw [DihedralGroup.nat_card, hcardP₁] at h
    omega
  subst hm
  have hD''card : Nat.card ↥((P₁ : Subgroup Q) ⊓ L) = 8 :=
    Work.AUTA7.GroupTheory.CardInfSylowTwo L hL hcardL P₁
  have hne : TQ ≠ (P₁ : Subgroup Q) ⊓ L := by
    intro heq
    exact hTQnotleL (heq ▸ inf_le_right)
  exact contradiction_of_four_group L P₁ ψ₁ TQ hTQleP₁ hcardTQ hD''card hne hVcard hVexp

/-- **The even index case.** -/
theorem EvenIndex : Work.GW2.AutA7EvenIndexProp := by
  intro Q _ _ L hL hφ hC hS h2
  obtain ⟨Q₀, L₀, hL₀norm, hL₀idx, hL₀iso, hL₀C, hL₀S⟩ :=
    reduce_to_index_two Q L hL hφ hC hS h2
  obtain ⟨φ₀⟩ := hL₀iso
  exact index_two_core ↥Q₀ L₀ hL₀norm φ₀ hL₀C hL₀S hL₀idx

end Work.AUTA7.A7
