import Mathlib
import Submission.Work.BSW.Concl
import Submission.Work.BSW.Cases.sylow_two_structure
import Submission.Work.BSW.Cases.normalizer_centralizer_card
import Submission.Work.BSW.Cases.normalizer_centralizer_structure
import Submission.Work.BSW.Cases.involution_outside_normalizer_normalizes

namespace Work.BSW.Cases

set_option linter.style.haveILetI false
set_option linter.unusedVariables false

open Subgroup

/-- **Bender 1974, §1** (`REFS/vision/bender1974_bsw/p0002.md`), the `|K| = 2` case:
for an involution `u` outside `N = N_G(C_G(t))` the intersection `N ⊓ N^u` has order `3`.

Proof: `N ⊓ N^u` has order dividing `|N| = 12`; it contains the subgroup of order `3` produced by
`involution_outside_normalizer_normalizes`; and it has no involution. Indeed an involution `w` of
`N ⊓ N^u` lies in `H = C_G(t)` (involutions of `N` lie in `H`) and also in `H^u` (its conjugate
`u⁻¹ w u` is an involution of `N`, hence lies in `H`); since both `H` and `H^u` are abelian of
order `4`, both equal `C_G(w)`, so `H = H^u`, i.e. `u ∈ N_G(H) = N`, contradiction. -/
theorem k2c_inter_card_three {G : Type} [Group G] [Finite G]
    (hsimple : IsSimpleGroup G) (hnab : ∃ a b : G, a * b ≠ b * a)
    {t s : G} {K : Subgroup G} (h : Work.GW2.BSWHyps2 G t s K) (hk : Nat.card ↥K = 2)
    {u : G} (hu : orderOf u = 2) (huN : u ∉ K2N G t) :
    Nat.card ↥(K2N G t ⊓ (K2N G t).map (MulAut.conj u).toMonoidHom) = 3 := by
  haveI : Fact (Nat.Prime 2) := ⟨by norm_num⟩
  set M : Subgroup G := K2N G t ⊓ (K2N G t).map (MulAut.conj u).toMonoidHom with hMdef
  change Nat.card ↥M = 3
  have hN12 : Nat.card ↥(K2N G t) = 12 := by simpa [K2N] using iwn_card_normalizer h hk
  have hM12 : Nat.card ↥M ∣ 12 := by
    rw [← hN12]; exact Subgroup.card_dvd_of_le inf_le_left
  obtain ⟨T, hT3, hTN, huT⟩ :=
    involution_outside_normalizer_normalizes hsimple hnab t s K h hk u hu huN
  have hTleNu : T ≤ (K2N G t).map (MulAut.conj u).toMonoidHom := by
    have hTu : T.map (MulAut.conj u).toMonoidHom = T :=
      Subgroup.mem_normalizer_iff_map_conj_eq.mp huT
    rw [← hTu]
    exact Subgroup.map_mono hTN
  have h3dvd : 3 ∣ Nat.card ↥M := by
    rw [← hT3]
    exact Subgroup.card_dvd_of_le (show T ≤ M from fun x hx => ⟨hTN hx, hTleNu hx⟩)
  -- `M` has no involution
  have hno2 : ∀ w : ↥M, orderOf w ≠ 2 := by
    intro w hw
    have hwG2 : orderOf (w : G) = 2 := (Subgroup.orderOf_coe w).trans hw
    have hwN : (w : G) ∈ K2N G t := w.2.1
    have hwNu : (w : G) ∈ (K2N G t).map (MulAut.conj u).toMonoidHom := w.2.2
    have hwH : (w : G) ∈ K2C G t :=
      iwn_mem_of_mem_normalizer_of_orderOf_two h hk hwN hwG2
    -- the conjugate `x = u⁻¹ * w * u` lies in `H`
    set x : G := (MulAut.conj u).symm (w : G) with hxdef
    have hxN : x ∈ K2N G t := by
      obtain ⟨n, hnN, hnx⟩ := Subgroup.mem_map.mp hwNu
      have hxn : x = n := by
        rw [hxdef, ← hnx]
        exact MulEquiv.symm_apply_apply (MulAut.conj u) n
      rw [hxn]; exact hnN
    have hx2 : orderOf x = 2 :=
      (MulEquiv.orderOf_eq (MulAut.conj u).symm (w : G)).trans hwG2
    have hxH : x ∈ K2C G t := iwn_mem_of_mem_normalizer_of_orderOf_two h hk hxN hx2
    have hwHu : (w : G) ∈ (K2C G t).map (MulAut.conj u).toMonoidHom := by
      refine Subgroup.mem_map.mpr ⟨x, hxH, ?_⟩
      show (MulAut.conj u).toMonoidHom x = (w : G)
      exact MulEquiv.apply_symm_apply (MulAut.conj u) (w : G)
    -- both `H` and `H^u` are abelian of order `4`, hence both equal `C_G(w)`
    have hCH : Subgroup.centralizer ({(w : G)} : Set G) = K2C G t := by
      refine (Subgroup.eq_of_le_of_card_ge ?_ ?_).symm
      · intro y hy
        rw [Subgroup.mem_centralizer_singleton_iff]
        exact iwn_H_comm h hk y hy (w : G) hwH
      · exact le_of_eq ((iwn_involution_centralizer_card h hk hwG2).trans
          (Work.BSW.Api.card_centralizer_of_card_K_two h hk).symm)
    have hCHu : Subgroup.centralizer ({(w : G)} : Set G) =
        (K2C G t).map (MulAut.conj u).toMonoidHom := by
      refine (Subgroup.eq_of_le_of_card_ge ?_ ?_).symm
      · intro y hy
        rw [Subgroup.mem_centralizer_singleton_iff]
        obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.mp hy
        obtain ⟨b, hb, hbw⟩ := Subgroup.mem_map.mp hwHu
        rw [← hbw, ← map_mul, ← map_mul, iwn_H_comm h hk a ha b hb]
      · exact le_of_eq ((iwn_involution_centralizer_card h hk hwG2).trans
          ((Subgroup.card_map_of_injective (MulAut.conj u).injective).trans
            (Work.BSW.Api.card_centralizer_of_card_K_two h hk)).symm)
    have hHne : (K2C G t).map (MulAut.conj u).toMonoidHom ≠ K2C G t :=
      fun heq => huN (Subgroup.mem_normalizer_iff_map_conj_eq.mpr heq)
    exact hHne (hCHu ▸ hCH)
  have hodd : Odd (Nat.card ↥M) := by
    rw [← Nat.not_even_iff_odd, even_iff_two_dvd]
    intro h2
    obtain ⟨w, hw⟩ := exists_prime_orderOf_dvd_card' (G := ↥M) 2 h2
    exact hno2 w hw
  have hcop : Nat.Coprime (Nat.card ↥M) 4 := by
    have hpow : Nat.Coprime (Nat.card ↥M) (2 ^ 2) := Nat.Coprime.pow_right 2
      (Nat.coprime_two_right.mpr hodd)
    simpa using hpow
  have hdvd3 : Nat.card ↥M ∣ 3 := hcop.dvd_of_dvd_mul_right (by rw [show (12:ℕ) = 3 * 4 from rfl] at hM12; exact hM12)
  exact (Nat.dvd_antisymm h3dvd hdvd3).symm

/-- **Conjugacy of the order-`3` subgroups of `N = N_G(C_G(t))`** (`|K| = 2` case).

`N` has exactly four order-`3` subgroups, and each of them is self-normalizing in `N`
(`normalizer_centralizer_structure`).  Hence the orbit of `T` under `N` consists of
`|N : T| = 12/3 = 4` distinct conjugates, all of them order-`3` subgroups of `N`; since there are
only four in total, every order-`3` subgroup of `N` is an `N`-conjugate of `T`. -/
theorem k2c_conj_order_three {G : Type} [Group G] [Finite G]
    {t s : G} {K : Subgroup G} (h : Work.GW2.BSWHyps2 G t s K) (hk : Nat.card ↥K = 2)
    {T T' : Subgroup G} (hTN : T ≤ K2N G t) (hT : Nat.card T = 3)
    (hT'N : T' ≤ K2N G t) (hT' : Nat.card T' = 3) :
    ∃ n : ↥(K2N G t), T' = T.map (MulAut.conj (n : G)).toMonoidHom := by
  set N : Subgroup G := K2N G t with hNdef
  have hconjmul : ∀ (a b : G) (S : Subgroup G),
      S.map (MulAut.conj (a * b)).toMonoidHom
        = (S.map (MulAut.conj b).toMonoidHom).map (MulAut.conj a).toMonoidHom := by
    intro a b S
    rw [Subgroup.map_map]
    congr 1
    ext x
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom]
    rw [MulAut.conj_apply, MulAut.conj_apply, MulAut.conj_apply]
    group
  have hS4 : Nat.card {X : Subgroup G // X ≤ N ∧ Nat.card X = 3} = 4 := by
    simpa [N, K2N] using (normalizer_centralizer_structure t s K h hk).2.2
  have hN12 : Nat.card ↥N = 12 := by simpa [N, K2N] using iwn_card_normalizer h hk
  have hstab : N ⊓ Subgroup.normalizer (T : Set G) = T := by
    have hh := (normalizer_centralizer_structure t s K h hk).2.1 T hTN hT
    simpa [N, K2N] using hh
  let Φ : ↥N → {X : Subgroup G // X ≤ N ∧ Nat.card X = 3} := fun n =>
    ⟨T.map (MulAut.conj (n : G)).toMonoidHom,
      fun x hx => by
        obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.mp hx
        exact N.mul_mem (N.mul_mem n.2 (hTN ha)) (N.inv_mem n.2),
      by rw [Subgroup.card_map_of_injective (MulAut.conj (n : G)).injective, hT]⟩
  -- the fiber over a point of the range has three elements
  have hfiber : ∀ (X : {X : Subgroup G // X ≤ N ∧ Nat.card X = 3}) (n₀ : ↥N), Φ n₀ = X →
      Nat.card {n : ↥N // Φ n = X} = 3 := by
    intro X n₀ hn₀
    have hMcard : Nat.card ↥(T.subgroupOf N) = 3 := by
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hTN).toEquiv, hT]
    let ψ : ↥(T.subgroupOf N) → {n : ↥N // Φ n = X} := fun m =>
      ⟨n₀ * (m : ↥N), by
        refine Subtype.ext ?_
        rw [← hn₀]
        show T.map (MulAut.conj (((n₀ * (m : ↥N) : ↥N)) : G)).toMonoidHom
            = T.map (MulAut.conj ((n₀ : ↥N) : G)).toMonoidHom
        rw [Subgroup.coe_mul, hconjmul]
        congr 1
        exact Subgroup.mem_normalizer_iff_map_conj_eq.mp
          (Subgroup.le_normalizer (Subgroup.mem_subgroupOf.mp m.2))⟩
    have hinj : Function.Injective ψ := by
      intro m₁ m₂ hm
      have h1 : n₀ * (m₁ : ↥N) = n₀ * (m₂ : ↥N) := congrArg Subtype.val hm
      exact Subtype.ext (mul_left_cancel h1)
    have hsurj : Function.Surjective ψ := by
      rintro ⟨n, hn⟩
      have heq : T.map (MulAut.conj ((n : ↥N) : G)).toMonoidHom
          = T.map (MulAut.conj ((n₀ : ↥N) : G)).toMonoidHom :=
        congrArg Subtype.val (hn.trans hn₀.symm)
      have hkey : T.map (MulAut.conj (((n₀ : ↥N) : G)⁻¹ * ((n : ↥N) : G))).toMonoidHom = T := by
        rw [hconjmul, heq, ← hconjmul, inv_mul_cancel, map_one]
        exact Subgroup.map_id T
      have hmem : (((n₀⁻¹ * n : ↥N)) : G) ∈ N ⊓ Subgroup.normalizer (T : Set G) := by
        refine ⟨N.mul_mem (N.inv_mem n₀.2) n.2, ?_⟩
        show (((n₀⁻¹ * n : ↥N)) : G) ∈ Subgroup.normalizer (T : Set G)
        rw [show (((n₀⁻¹ * n : ↥N)) : G) = ((n₀ : ↥N) : G)⁻¹ * ((n : ↥N) : G) from by
          rw [Subgroup.coe_mul, Subgroup.coe_inv]]
        exact Subgroup.mem_normalizer_iff_map_conj_eq.mpr hkey
      refine ⟨⟨n₀⁻¹ * n, ?_⟩, ?_⟩
      · rw [Subgroup.mem_subgroupOf, ← hstab]
        exact hmem
      · apply Subtype.ext
        show n₀ * (n₀⁻¹ * n) = n
        rw [← mul_assoc, mul_inv_cancel, one_mul]
    exact (Nat.card_congr (Equiv.ofBijective ψ ⟨hinj, hsurj⟩)).symm.trans hMcard
  have hrange4 : Nat.card (Set.range Φ) = 4 := by
    have hfib : ∀ y : Set.range Φ,
        Nat.card {n : ↥N // (⟨Φ n, ⟨n, rfl⟩⟩ : Set.range Φ) = y} = 3 := by
      rintro ⟨X, hXr⟩
      obtain ⟨n₀, hn₀⟩ := hXr
      exact (Nat.card_congr (Equiv.subtypeEquivRight (fun n => Subtype.ext_iff))).trans
        (hfiber X n₀ hn₀)
    have h12 := Work.COPR.card_mul_of_fibers
      (fun n : ↥N => (⟨Φ n, ⟨n, rfl⟩⟩ : Set.range Φ)) 3 hfib
    rw [hN12, show (12:ℕ) = 4 * 3 from rfl] at h12
    exact (Nat.mul_right_cancel (by norm_num) h12).symm
  have hrange_univ : Set.range Φ = Set.univ := by
    refine Set.eq_of_subset_of_ncard_le (Set.subset_univ _) ?_
    rw [Set.ncard_univ, hS4]
    exact le_of_eq hrange4.symm
  obtain ⟨n, hn⟩ := show (⟨T', hT'N, hT'⟩ : {X : Subgroup G // X ≤ N ∧ Nat.card X = 3}) ∈
      Set.range Φ from by rw [hrange_univ]; exact Set.mem_univ _
  exact ⟨n, (congrArg Subtype.val hn).symm⟩

/-- Conjugation of subgroups commutes with taking normalizers, in the form needed below:
`N_G(T)^n = N_G(T^n)`. -/
theorem k2c_normalizer_map_conj {G : Type} [Group G] (T : Subgroup G) (n : G) :
    (Subgroup.normalizer (T : Set G)).map (MulAut.conj n).toMonoidHom
      = Subgroup.normalizer (T.map (MulAut.conj n).toMonoidHom : Set G) := by
  apply le_antisymm
  · exact Subgroup.le_normalizer_map _
  · have hcomp : (MulAut.conj n).toMonoidHom.comp (MulAut.conj n⁻¹).toMonoidHom
        = MonoidHom.id G := by
      ext x
      simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MonoidHom.id_apply]
      rw [MulAut.conj_apply, MulAut.conj_apply]
      group
    have hcomp' : (MulAut.conj n⁻¹).toMonoidHom.comp (MulAut.conj n).toMonoidHom
        = MonoidHom.id G := by
      ext x
      simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MonoidHom.id_apply]
      rw [MulAut.conj_apply, MulAut.conj_apply]
      group
    have hle : (Subgroup.normalizer (T.map (MulAut.conj n).toMonoidHom : Set G)).map
        (MulAut.conj n⁻¹).toMonoidHom ≤ Subgroup.normalizer (T : Set G) := by
      have hh := Subgroup.le_normalizer_map (H := T.map (MulAut.conj n).toMonoidHom)
        (f := (MulAut.conj n⁻¹).toMonoidHom)
      rw [Subgroup.map_map, hcomp', Subgroup.map_id] at hh
      exact hh
    calc Subgroup.normalizer (T.map (MulAut.conj n).toMonoidHom : Set G)
        = ((Subgroup.normalizer (T.map (MulAut.conj n).toMonoidHom : Set G)).map
            (MulAut.conj n⁻¹).toMonoidHom).map (MulAut.conj n).toMonoidHom := by
          rw [Subgroup.map_map, hcomp, Subgroup.map_id]
      _ ≤ (Subgroup.normalizer (T : Set G)).map (MulAut.conj n).toMonoidHom :=
          Subgroup.map_mono hle

/-- **The number of involutions of `N_G(T)` is the same for all order-`3` subgroups `T` of
`N = N_G(C_G(t))`** (`|K| = 2` case).

Indeed any two such subgroups are `N`-conjugate (`k2c_conj_order_three`), and conjugating by the
conjugating element is a bijection on `G` which preserves `orderOf` and carries `N_G(T)` onto
`N_G(T')` (`k2c_normalizer_map_conj`). -/
theorem k2c_inv_card_eq {G : Type} [Group G] [Finite G]
    {t s : G} {K : Subgroup G} (h : Work.GW2.BSWHyps2 G t s K) (hk : Nat.card ↥K = 2)
    {T T' : Subgroup G} (hTN : T ≤ K2N G t) (hT : Nat.card T = 3)
    (hT'N : T' ≤ K2N G t) (hT' : Nat.card T' = 3) :
    Nat.card {u : G // orderOf u = 2 ∧ u ∈ Subgroup.normalizer (T' : Set G)} =
      Nat.card {u : G // orderOf u = 2 ∧ u ∈ Subgroup.normalizer (T : Set G)} := by
  obtain ⟨n, hn⟩ := k2c_conj_order_three h hk hTN hT hT'N hT'
  rw [hn]
  have hmem : ∀ u : G, (MulAut.conj (n : G)) u ∈
      Subgroup.normalizer (T.map (MulAut.conj (n : G)).toMonoidHom : Set G) ↔
      u ∈ Subgroup.normalizer (T : Set G) := by
    intro u
    rw [← k2c_normalizer_map_conj T (n : G)]
    constructor
    · intro hh
      obtain ⟨x, hx, hxeq⟩ := Subgroup.mem_map.mp hh
      have hxu : x = u := (MulAut.conj (n : G)).injective hxeq
      rwa [hxu] at hx
    · intro hu
      exact Subgroup.mem_map.mpr ⟨u, hu, rfl⟩
  refine (Nat.card_congr
    (Equiv.subtypeEquiv (MulAut.conj (n : G)) (fun u => ⟨?_, ?_⟩))).symm
  · rintro ⟨hu2, huT⟩
    exact ⟨(MulEquiv.orderOf_eq (MulAut.conj (n : G)) u).trans hu2, (hmem u).mpr huT⟩
  · rintro ⟨hu2, huT⟩
    exact ⟨(MulEquiv.orderOf_eq (MulAut.conj (n : G)) u).symm.trans hu2, (hmem u).mp huT⟩

/-- **Uniqueness of the order-`3` subgroup of `N` normalized by an involution outside `N`**
(`|K| = 2` case).

For an involution `u ∉ N` the intersection `M = N ⊓ N^u` has order `3` (`k2c_inter_card_three`),
is normalized by `u`, and is the only such subgroup: any order-`3` subgroup `T ≤ N` normalized
by `u` is contained in `N ⊓ N^u` and hence equals `M` by cardinality. -/
theorem k2c_existsUnique_normalized {G : Type} [Group G] [Finite G]
    (hsimple : IsSimpleGroup G) (hnab : ∃ a b : G, a * b ≠ b * a)
    {t s : G} {K : Subgroup G} (h : Work.GW2.BSWHyps2 G t s K) (hk : Nat.card ↥K = 2)
    {u : G} (hu : orderOf u = 2) (huN : u ∉ K2N G t) :
    ∃! T' : {X : Subgroup G // X ≤ K2N G t ∧ Nat.card X = 3},
      u ∈ Subgroup.normalizer (T'.1 : Set G) := by
  have hMcard : Nat.card ↥(K2N G t ⊓ (K2N G t).map (MulAut.conj u).toMonoidHom) = 3 :=
    k2c_inter_card_three hsimple hnab h hk hu huN
  have hu2 : u * u = 1 := by
    have := pow_orderOf_eq_one u
    rw [hu] at this
    simpa [pow_two] using this
  have huinv : u⁻¹ = u := inv_eq_of_mul_eq_one_left hu2
  have hconjsq : (MulAut.conj u).toMonoidHom.comp (MulAut.conj u).toMonoidHom
      = MonoidHom.id G := by
    ext x
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MonoidHom.id_apply]
    rw [MulAut.conj_apply, MulAut.conj_apply, huinv,
      show u * (u * x * u) * u = (u * u) * x * (u * u) from by group, hu2]
    simp
  have hMmap : (K2N G t ⊓ (K2N G t).map (MulAut.conj u).toMonoidHom).map
      (MulAut.conj u).toMonoidHom
      = K2N G t ⊓ (K2N G t).map (MulAut.conj u).toMonoidHom := by
    rw [Subgroup.map_inf _ _ _ (MulAut.conj u).injective, Subgroup.map_map, hconjsq,
      Subgroup.map_id, inf_comm]
  refine ⟨⟨K2N G t ⊓ (K2N G t).map (MulAut.conj u).toMonoidHom, inf_le_left, hMcard⟩, ?_, ?_⟩
  · exact Subgroup.mem_normalizer_iff_map_conj_eq.mpr hMmap
  · intro y hy
    have hyNu : y.1 ≤ (K2N G t).map (MulAut.conj u).toMonoidHom := by
      have hy' : y.1.map (MulAut.conj u).toMonoidHom = y.1 :=
        Subgroup.mem_normalizer_iff_map_conj_eq.mp hy
      rw [← hy']
      exact Subgroup.map_mono y.2.1
    have hle : y.1 ≤ K2N G t ⊓ (K2N G t).map (MulAut.conj u).toMonoidHom :=
      fun x hx => ⟨y.2.1 hx, hyNu hx⟩
    exact Subtype.ext (Subgroup.eq_of_le_of_card_ge hle
      (by rw [hMcard, y.2.2]))

theorem k2_count_involutions_outside {G : Type} [Group G] [Finite G] (hsimple : IsSimpleGroup G)
    (hnab : ∃ a b : G, a * b ≠ b * a) (t s : G) (K : Subgroup G)
    (h : Work.GW2.BSWHyps2 G t s K) (hk : Nat.card ↥K = 2) (T : Subgroup G)
    (hT : Nat.card T = 3)
    (hTN : T ≤ Subgroup.normalizer ((Subgroup.centralizer ({t} : Set G)) : Set G)) :
    Nat.card {u : G // orderOf u = 2 ∧
        u ∉ Subgroup.normalizer ((Subgroup.centralizer ({t} : Set G)) : Set G)} =
      4 * Nat.card {u : G // orderOf u = 2 ∧ u ∈ Subgroup.normalizer (T : Set G)} := by
  have hS4 : Nat.card {X : Subgroup G // X ≤ K2N G t ∧ Nat.card X = 3} = 4 := by
    simpa [K2N] using (normalizer_centralizer_structure t s K h hk).2.2
  have huniq : ∀ u : G, orderOf u = 2 → u ∉ K2N G t →
      ∃! T' : {X : Subgroup G // X ≤ K2N G t ∧ Nat.card X = 3},
        u ∈ Subgroup.normalizer (T'.1 : Set G) :=
    fun u hu huN => k2c_existsUnique_normalized hsimple hnab h hk hu huN
  let f : {u : G // orderOf u = 2 ∧ u ∉ K2N G t} →
      {X : Subgroup G // X ≤ K2N G t ∧ Nat.card X = 3} :=
    fun u => (huniq u.1 u.2.1 u.2.2).choose
  have f_spec : ∀ u : {u : G // orderOf u = 2 ∧ u ∉ K2N G t},
      u.1 ∈ Subgroup.normalizer ((f u).1 : Set G) :=
    fun u => (huniq u.1 u.2.1 u.2.2).choose_spec.1
  have hfiber : ∀ T' : {X : Subgroup G // X ≤ K2N G t ∧ Nat.card X = 3},
      Nat.card {u : {u : G // orderOf u = 2 ∧ u ∉ K2N G t} // f u = T'} =
      Nat.card {u : G // orderOf u = 2 ∧ u ∈ Subgroup.normalizer (T : Set G)} := by
    intro T'
    let g : {u : {u : G // orderOf u = 2 ∧ u ∉ K2N G t} // f u = T'} →
        {v : G // orderOf v = 2 ∧ v ∈ Subgroup.normalizer (T'.1 : Set G)} :=
      fun u => ⟨u.1.1, u.1.2.1, by
        have h := f_spec u.1
        rw [u.2] at h
        exact h⟩
    have hginj : Function.Injective g := by
      intro a b hab
      have h1 : (g a).1 = (g b).1 := congrArg (fun w => w.1) hab
      exact Subtype.ext (Subtype.ext h1)
    have hgsurj : Function.Surjective g := by
      rintro ⟨v, hv2, hvN⟩
      have hstab : K2N G t ⊓ Subgroup.normalizer (T'.1 : Set G) = T'.1 :=
        (normalizer_centralizer_structure t s K h hk).2.1 T'.1 T'.2.1 T'.2.2
      have hvnotN : v ∉ K2N G t := by
        intro hv
        have hmem : v ∈ T'.1 := by rw [← hstab]; exact ⟨hv, hvN⟩
        have hdvd : orderOf v ∣ Nat.card T'.1 := by
          rw [← Nat.card_zpowers]
          exact Subgroup.card_dvd_of_le (Subgroup.zpowers_le.mpr hmem)
        rw [T'.2.2, hv2] at hdvd
        norm_num at hdvd
      refine ⟨⟨⟨v, hv2, hvnotN⟩, ?_⟩, rfl⟩
      exact (huniq v hv2 hvnotN).unique (f_spec ⟨v, hv2, hvnotN⟩) hvN
    exact (Nat.card_congr (Equiv.ofBijective g ⟨hginj, hgsurj⟩)).trans
      (k2c_inv_card_eq h hk (show T ≤ K2N G t from hTN) hT T'.2.1 T'.2.2)
  have hmain := Work.COPR.card_mul_of_fibers f
    (Nat.card {u : G // orderOf u = 2 ∧ u ∈ Subgroup.normalizer (T : Set G)}) hfiber
  rw [hS4] at hmain
  simpa [K2N] using hmain

end Work.BSW.Cases
