import Mathlib
import Submission.Work.BSW.Concl
import Submission.Work.BSW.Basic
import Submission.Work.BSW.Api.card_centralizer_of_card_K_two
import Submission.Work.BSW.Api.ncard_involutions_eq_index
import Submission.Work.BSW.Api.mem_centralizer_iff
import Submission.Work.BSW.Cases.bswK2Involution
import Submission.Work.COPR.card_mul_of_fibers

/-!
# The normalizer of `C_G(t)` in the `|K| = 2` case of Bender's BSW theorem

Hypotheses `Work.GW2.BSWHyps2 G t s K` together with `|K| = 2` say that `H = C_G(t) = K⟨s⟩`
is a Klein four group: `K = {1, t}`, `s` is an involution inverting `K`, `s ∉ K`, and
`t s = s t`.  We prove here that the normalizer of `H` in `G` has order `12`.

The mathematics is a double count:

* every involution `x` of `G` has `|C_G(x)| = 4` (`bswK2Involution`), so `C_G(x)` has order `2²`
  and is maximal among `2`-subgroups: if `L ≥ C_G(x)` is a `2`-group then `L` is nontrivial, its
  centre contains an involution `z`, and `L ≤ C_G(z)` with `|C_G(z)| = 4`.  Hence the Sylow
  `2`-subgroups of `G` are exactly the subgroups `C_G(x)` (`x` an involution) and they all have
  order `4`;
* a Sylow `2`-subgroup `P` of order `4` is commutative, so it lies in the centralizer of each of
  its involutions, and consequently `P` is the unique Sylow subgroup containing the involution `x`;
* `H = C_G(t)` has exactly the three involutions `t`, `s`, `t s`, and by conjugacy every Sylow
  `2`-subgroup has three involutions.  Counting the pairs `(x, P)` with `x` an involution in the
  Sylow `2`-subgroup `P` gives `#{involutions of G} = 3 · #{Sylow 2-subgroups}`;
* since `#{involutions of G} = |G : C_G(t)| = |G|/4` and
  `#{Sylow 2-subgroups} = |G : N_G(C_G(t))|`, we get `|G : C_G(t)| = 3|G : N_G(C_G(t))|`, i.e.
  `|N_G(C_G(t)) : C_G(t)| = 3` and `|N_G(C_G(t))| = 3 · 4 = 12`.
-/

open Subgroup

namespace Work.BSW.Cases

/-! ## Elementary facts about the Sylow `2`-subgroups in the `|K| = 2` case -/

/-- Every `2`-subgroup of `G` has order dividing `4`: it is either trivial, or nontrivial and
hence has a nontrivial centre, which contains an involution `z` (`Z(L)` is a nontrivial finite
`2`-group, so `2 ∣ |Z(L)|` and Cauchy applies); then `L ≤ C_G(z)` and
`|C_G(z)| = 4` by `bswK2Involution`. -/
theorem ncc_two_subgroup_card_dvd_four {G : Type} [Group G] [Finite G] {t s : G} {K : Subgroup G}
    (h : Work.GW2.BSWHyps2 G t s K) (hk : Nat.card ↥K = 2)
    (L : Subgroup G) (hL : IsPGroup 2 L) : Nat.card ↥L ∣ 4 := by
  by_cases hbot : L = ⊥
  · rw [hbot]
    simp
  haveI hnt : Nontrivial ↥L := (Subgroup.nontrivial_iff_ne_bot L).mpr hbot
  have hZnt : Nontrivial ↥(Subgroup.center ↥L) := IsPGroup.center_nontrivial hL
  have hZ2 : IsPGroup 2 ↥(Subgroup.center ↥L) := hL.to_subgroup (Subgroup.center ↥L)
  have h2dvd : 2 ∣ Nat.card ↥(Subgroup.center ↥L) := by
    obtain ⟨n, hn0, hn⟩ := hZ2.nontrivial_iff_card.mp hZnt
    exact ⟨2 ^ (n - 1), by rw [hn, mul_comm, ← pow_succ, Nat.sub_add_cancel hn0]⟩
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' (G := ↥(Subgroup.center ↥L)) 2 h2dvd
  have hw2 : orderOf (((z : ↥L)) : G) = 2 :=
    (Subgroup.orderOf_coe (z : ↥L)).trans ((Subgroup.orderOf_coe z).trans hz)
  have hLle : L ≤ Subgroup.centralizer ({(((z : ↥L)) : G)} : Set G) := by
    intro y hy
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hzy : (⟨y, hy⟩ : ↥L) * (z : ↥L) = (z : ↥L) * ⟨y, hy⟩ :=
      Subgroup.mem_center_iff.mp z.2 ⟨y, hy⟩
    exact congrArg (fun w : ↥L => (w : G)) hzy
  have hdvd : Nat.card ↥L ∣ Nat.card ↥(Subgroup.centralizer ({(((z : ↥L)) : G)} : Set G)) :=
    Subgroup.card_dvd_of_le hLle
  rw [(bswK2Involution h hk hw2).1] at hdvd
  exact hdvd

/-- For every involution `x`, the centralizer `C_G(x)` has order `4` and is a maximal
`2`-subgroup, i.e. a Sylow `2`-subgroup. -/
theorem ncc_centralizer_isSylow {G : Type} [Group G] [Finite G] {t s : G} {K : Subgroup G}
    (h : Work.GW2.BSWHyps2 G t s K) (hk : Nat.card ↥K = 2)
    {x : G} (hx : orderOf x = 2) :
    ∃ P : Sylow 2 G, (P : Subgroup G) = Subgroup.centralizer ({x} : Set G) := by
  have hC4 : Nat.card ↥(Subgroup.centralizer ({x} : Set G)) = 4 := (bswK2Involution h hk hx).1
  refine ⟨⟨Subgroup.centralizer ({x} : Set G), ?_, ?_⟩, rfl⟩
  · exact IsPGroup.of_card (n := 2) (by rw [hC4]; norm_num)
  · intro Q hQ hCQ
    have hdvd1 : 4 ∣ Nat.card ↥Q := by
      have h1 : Nat.card ↥(Subgroup.centralizer ({x} : Set G)) ∣ Nat.card ↥Q :=
        Subgroup.card_dvd_of_le hCQ
      rwa [hC4] at h1
    have hdvd2 : Nat.card ↥Q ∣ 4 := ncc_two_subgroup_card_dvd_four h hk Q hQ
    have hQ4 : Nat.card ↥Q = 4 := Nat.dvd_antisymm hdvd2 hdvd1
    exact (Subgroup.eq_of_le_of_card_ge hCQ (by rw [hQ4, hC4])).symm

/-- Every Sylow `2`-subgroup has order `4` (it is isomorphic to `C_G(t)`). -/
theorem ncc_sylow_card_four {G : Type} [Group G] [Finite G] {t s : G} {K : Subgroup G}
    (h : Work.GW2.BSWHyps2 G t s K) (hk : Nat.card ↥K = 2) (P : Sylow 2 G) :
    Nat.card ↥(P : Subgroup G) = 4 := by
  obtain ⟨P₀, hP₀⟩ := ncc_centralizer_isSylow h hk (Work.BSW.orderOf_t h)
  have hH4 : Nat.card ↥(Subgroup.centralizer ({t} : Set G)) = 4 :=
    Work.BSW.Api.card_centralizer_of_card_K_two h hk
  have h1 : Nat.card ↥(P : Subgroup G) = Nat.card ↥(P₀ : Subgroup G) :=
    Nat.card_congr (Sylow.equiv P P₀).toEquiv
  rw [h1, hP₀, hH4]

/-- Every Sylow `2`-subgroup is commutative (it has order `4 = 2²`). -/
theorem ncc_sylow_comm {G : Type} [Group G] [Finite G] {t s : G} {K : Subgroup G}
    (h : Work.GW2.BSWHyps2 G t s K) (hk : Nat.card ↥K = 2) (P : Sylow 2 G) :
    IsMulCommutative ↥(P : Subgroup G) :=
  IsPGroup.isMulCommutative_of_card_eq_prime_sq (G := ↥(P : Subgroup G)) (p := 2)
    (by rw [ncc_sylow_card_four h hk P]; norm_num)

/-- A Sylow `2`-subgroup containing an involution `x` is exactly `C_G(x)`: it is commutative, so
it lies in `C_G(x)`, and both have order `4`. -/
theorem ncc_sylow_eq_centralizer {G : Type} [Group G] [Finite G] {t s : G} {K : Subgroup G}
    (h : Work.GW2.BSWHyps2 G t s K) (hk : Nat.card ↥K = 2) (P : Sylow 2 G) {x : G}
    (hxP : x ∈ (P : Subgroup G)) (hx : orderOf x = 2) :
    (P : Subgroup G) = Subgroup.centralizer ({x} : Set G) := by
  haveI hcomm : IsMulCommutative ↥(P : Subgroup G) := ncc_sylow_comm h hk P
  have hle : (P : Subgroup G) ≤ Subgroup.centralizer ({x} : Set G) := by
    intro y hy
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact congrArg Subtype.val ((IsMulCommutative.is_comm (M := ↥(P : Subgroup G))).comm
      (⟨y, hy⟩ : ↥(P : Subgroup G)) ⟨x, hxP⟩)
  have hC4 : Nat.card ↥(Subgroup.centralizer ({x} : Set G)) = 4 := (bswK2Involution h hk hx).1
  refine Subgroup.eq_of_le_of_card_ge hle ?_
  rw [hC4, ncc_sylow_card_four h hk P]

/-! ## The involutions of `C_G(t)` -/

/-- `C_G(t) = K⟨s⟩` with `K = {1, t}` has exactly the three involutions `t`, `s` and `t * s`. -/
theorem ncc_involutions_centralizer_t {G : Type} [Group G] [Finite G] {t s : G} {K : Subgroup G}
    (h : Work.GW2.BSWHyps2 G t s K) (hk : Nat.card ↥K = 2) :
    Nat.card {y : G // y ∈ Subgroup.centralizer ({t} : Set G) ∧ orderOf y = 2} = 3 := by
  have htC : t ∈ Subgroup.centralizer ({t} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.mpr rfl
  have hsC : s ∈ Subgroup.centralizer ({t} : Set G) := Work.BSW.s_mem_centralizer_t h
  have htsC : t * s ∈ Subgroup.centralizer ({t} : Set G) :=
    (Subgroup.centralizer ({t} : Set G)).mul_mem htC hsC
  -- `K = ⟨t⟩ = {1, t}`
  have hKz : Subgroup.zpowers t = K :=
    Subgroup.eq_of_le_of_card_ge (Work.BSW.zpowers_t_le_K h)
      (by rw [Nat.card_zpowers, Work.BSW.orderOf_t h, hk])
  have hKm : ∀ y ∈ K, y = 1 ∨ y = t := fun y hy => Work.BSW.mem_zpowers_t h (hKz.symm ▸ hy)
  -- the three involutions are distinct
  have ht_ne_hs : t ≠ s := fun h1 => Work.BSW.s_notMem_K h (h1 ▸ Work.BSW.t_mem_K h)
  have ht_ne_hts : t ≠ t * s := by
    intro h1
    have h2 : s = 1 := by
      have h3 := congrArg (fun z => t⁻¹ * z) h1
      simpa [← mul_assoc] using h3.symm
    exact Work.BSW.s_ne_one h h2
  have hs_ne_hts : s ≠ t * s := by
    intro h1
    have h2 : t = 1 := by
      have h3 := congrArg (fun z => z * s⁻¹) h1
      simpa [mul_assoc] using h3.symm
    exact Work.BSW.t_ne_one h h2
  -- `t * s` is an involution
  have hts2 : (t * s) * (t * s) = 1 := by
    calc (t * s) * (t * s) = t * (s * t) * s := by noncomm_ring
      _ = t * (t * s) * s := by rw [Work.BSW.s_mul_t_eq_t_mul_s h]
      _ = (t * t) * (s * s) := by noncomm_ring
      _ = 1 := by rw [Work.BSW.t_mul_self h, Work.BSW.s_mul_self h, one_mul]
  have hts_ne_one : t * s ≠ 1 := by
    intro h1
    have h2 : s = t := by
      have h3 := congrArg (fun z => t⁻¹ * z) h1
      have h4 : s = t⁻¹ := by simpa [← mul_assoc] using h3
      rw [h4, Work.BSW.t_inv h]
    exact Work.BSW.s_notMem_K h (h2 ▸ Work.BSW.t_mem_K h)
  have hts_order : orderOf (t * s) = 2 :=
    orderOf_eq_prime (p := 2) (by rw [pow_two]; exact hts2) hts_ne_one
  -- the set of involutions of `C_G(t)`
  have hset : ({y : G | y ∈ Subgroup.centralizer ({t} : Set G) ∧ orderOf y = 2} : Set G)
      = {t, s, t * s} := by
    ext y
    constructor
    · intro hy
      have hyC : y ∈ Subgroup.centralizer ({t} : Set G) := hy.1
      have hy2 : orderOf y = 2 := hy.2
      rcases (Work.BSW.Api.mem_centralizer_iff h y).mp hyC with hyK | ⟨k, hkK, hyk⟩
      · rcases hKm y hyK with h1 | h1
        · rw [h1, orderOf_one] at hy2
          exact absurd hy2 (by norm_num)
        · rw [h1]
          simp
      · rcases hKm k hkK with h1 | h1
        · rw [h1, one_mul] at hyk
          rw [hyk]
          simp
        · rw [h1] at hyk
          rw [hyk]
          simp
    · intro hy
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
      rcases hy with rfl | rfl | rfl
      · exact ⟨htC, Work.BSW.orderOf_t h⟩
      · exact ⟨hsC, Work.BSW.orderOf_s h⟩
      · exact ⟨htsC, hts_order⟩
  have hcoe : Nat.card {y : G // y ∈ Subgroup.centralizer ({t} : Set G) ∧ orderOf y = 2}
      = ({y : G | y ∈ Subgroup.centralizer ({t} : Set G) ∧ orderOf y = 2} : Set G).ncard := rfl
  rw [hcoe, hset]
  have h1 : t ∉ ({s, t * s} : Set G) := by
    rw [Set.mem_insert_iff, Set.mem_singleton_iff]
    push_neg
    exact ⟨ht_ne_hs, ht_ne_hts⟩
  have h2 : s ∉ ({t * s} : Set G) := by
    simpa using hs_ne_hts
  rw [Set.ncard_insert_of_notMem h1, Set.ncard_insert_of_notMem h2, Set.ncard_singleton]

/-! ## Transfer of the involution count between Sylow `2`-subgroups -/

/-- The involutions of a subgroup, counted inside the subgroup or inside `G`. -/
theorem ncc_fiber_card_eq_subtype {G : Type} [Group G] (P : Subgroup G) :
    Nat.card {x : G // x ∈ P ∧ orderOf x = 2} = Nat.card {x : ↥P // orderOf x = 2} :=
  Nat.card_congr
    { toFun := fun x => ⟨⟨x.1, x.2.1⟩,
        (Subgroup.orderOf_coe (⟨x.1, x.2.1⟩ : ↥P)).symm.trans x.2.2⟩
      invFun := fun y => ⟨y.1.1, y.1.2, (Subgroup.orderOf_coe y.1).trans y.2⟩
      left_inv := fun x => Subtype.ext rfl
      right_inv := fun y => Subtype.ext rfl }

/-- Isomorphic subgroups have the same number of involutions. -/
theorem ncc_involution_card_eq_of_mulEquiv {G : Type} [Group G] {P Q : Subgroup G}
    (e : ↥P ≃* ↥Q) :
    Nat.card {x : ↥P // orderOf x = 2} = Nat.card {y : ↥Q // orderOf y = 2} :=
  Nat.card_congr
    { toFun := fun x => ⟨e x.1, (MulEquiv.orderOf_eq e x.1).trans x.2⟩
      invFun := fun y => ⟨e.symm y.1, (MulEquiv.orderOf_eq e.symm y.1).trans y.2⟩
      left_inv := fun x => Subtype.ext (e.symm_apply_apply x.1)
      right_inv := fun y => Subtype.ext (e.apply_symm_apply y.1) }

/-- Every Sylow `2`-subgroup contains exactly three involutions: the number of involutions of a
Sylow subgroup is that of `C_G(t)`, which is `3`. -/
theorem ncc_fiber_card_three {G : Type} [Group G] [Finite G] {t s : G} {K : Subgroup G}
    (h : Work.GW2.BSWHyps2 G t s K) (hk : Nat.card ↥K = 2)
    (hsyl : ∀ x : G, orderOf x = 2 →
      ∃ P : Sylow 2 G, (P : Subgroup G) = Subgroup.centralizer ({x} : Set G))
    (P : Sylow 2 G) :
    Nat.card {x : G // x ∈ (P : Subgroup G) ∧ orderOf x = 2} = 3 := by
  obtain ⟨P₀, hP₀⟩ := hsyl t (Work.BSW.orderOf_t h)
  calc Nat.card {x : G // x ∈ (P : Subgroup G) ∧ orderOf x = 2}
      = Nat.card {x : ↥(P : Subgroup G) // orderOf x = 2} :=
        ncc_fiber_card_eq_subtype (P : Subgroup G)
    _ = Nat.card {x : ↥(P₀ : Subgroup G) // orderOf x = 2} :=
        ncc_involution_card_eq_of_mulEquiv (Sylow.equiv P P₀)
    _ = Nat.card {x : G // x ∈ (P₀ : Subgroup G) ∧ orderOf x = 2} :=
        (ncc_fiber_card_eq_subtype (P₀ : Subgroup G)).symm
    _ = Nat.card {x : G // x ∈ Subgroup.centralizer ({t} : Set G) ∧ orderOf x = 2} := by
        rw [hP₀]
    _ = 3 := ncc_involutions_centralizer_t h hk

/-! ## The double count -/

/-- Double counting of the set of pairs `(x, P)` with `x` an involution in the Sylow
`2`-subgroup `P`: if every involution lies in a Sylow `2`-subgroup, two Sylow `2`-subgroups
containing a common involution coincide, and every Sylow `2`-subgroup has three involutions, then
`G` has `3 · #{Sylow 2-subgroups}` involutions. -/
theorem ncc_card_involutions_eq_three_mul_sylow {G : Type} [Group G] [Finite G]
    (hex : ∀ x : G, orderOf x = 2 → ∃ P : Sylow 2 G, x ∈ (P : Subgroup G))
    (huniq : ∀ (P Q : Sylow 2 G) (x : G), x ∈ (P : Subgroup G) → x ∈ (Q : Subgroup G) →
      orderOf x = 2 → P = Q)
    (hfib : ∀ P : Sylow 2 G, Nat.card {x : G // x ∈ (P : Subgroup G) ∧ orderOf x = 2} = 3) :
    Nat.card {x : G // orderOf x = 2} = 3 * Nat.card (Sylow 2 G) := by
  let f : {x : G // orderOf x = 2} → Sylow 2 G := fun x => (hex x.1 x.2).choose
  have hf : ∀ x : {x : G // orderOf x = 2}, x.1 ∈ (f x : Subgroup G) :=
    fun x => (hex x.1 x.2).choose_spec
  have hfib' : ∀ P : Sylow 2 G, Nat.card {x : {x : G // orderOf x = 2} // f x = P} = 3 := by
    intro P
    have hb : Nat.card {x : {x : G // orderOf x = 2} // f x = P}
        = Nat.card {y : G // y ∈ (P : Subgroup G) ∧ orderOf y = 2} :=
      Nat.card_congr
        { toFun := fun x => ⟨x.1.1,
            (congrArg (fun Q : Sylow 2 G => (Q : Subgroup G)) x.2).le (hf x.1), x.1.2⟩
          invFun := fun y => ⟨⟨y.1, y.2.2⟩,
            huniq (f ⟨y.1, y.2.2⟩) P y.1 (hf ⟨y.1, y.2.2⟩) y.2.1 y.2.2⟩
          left_inv := fun x => Subtype.ext (Subtype.ext rfl)
          right_inv := fun y => Subtype.ext rfl }
    rw [hb, hfib P]
  have h := Work.COPR.card_mul_of_fibers f 3 hfib'
  rw [h, Nat.mul_comm]

/-! ## The normalizer of `C_G(t)` -/

theorem normalizer_centralizer_card {G : Type} [Group G] [Finite G] (hsimple : IsSimpleGroup G)
    (hnab : ∃ a b : G, a * b ≠ b * a) (t s : G) (K : Subgroup G)
    (h : Work.GW2.BSWHyps2 G t s K) (hk : Nat.card ↥K = 2) :
    Nat.card ↥(Subgroup.normalizer ((Subgroup.centralizer ({t} : Set G)) : Set G)) = 12 := by
  have hsyl : ∀ x : G, orderOf x = 2 →
      ∃ P : Sylow 2 G, (P : Subgroup G) = Subgroup.centralizer ({x} : Set G) :=
    fun x hx => ncc_centralizer_isSylow h hk hx
  obtain ⟨P₀, hP₀⟩ := hsyl t (Work.BSW.orderOf_t h)
  have hH4 : Nat.card ↥(Subgroup.centralizer ({t} : Set G)) = 4 :=
    Work.BSW.Api.card_centralizer_of_card_K_two h hk
  -- the number of Sylow 2-subgroups is the index of `N_G(C_G(t))`
  have hsylidx : Nat.card (Sylow 2 G)
      = (Subgroup.normalizer ((Subgroup.centralizer ({t} : Set G)) : Set G)).index := by
    have hN := Sylow.card_eq_index_normalizer P₀
    have hset : ((Subgroup.centralizer ({t} : Set G)) : Set G) = ((P₀ : Subgroup G) : Set G) := by
      rw [hP₀]
    rw [hset]
    exact hN
  -- every involution lies in a Sylow 2-subgroup, uniquely
  have hex : ∀ x : G, orderOf x = 2 → ∃ P : Sylow 2 G, x ∈ (P : Subgroup G) := by
    intro x hx
    obtain ⟨P, hP⟩ := hsyl x hx
    exact ⟨P, by rw [hP]; exact Subgroup.mem_centralizer_singleton_iff.mpr rfl⟩
  have huniq : ∀ (P Q : Sylow 2 G) (x : G), x ∈ (P : Subgroup G) → x ∈ (Q : Subgroup G) →
      orderOf x = 2 → P = Q := by
    intro P Q x hxP hxQ hx2
    exact Sylow.ext ((ncc_sylow_eq_centralizer h hk P hxP hx2).trans
      (ncc_sylow_eq_centralizer h hk Q hxQ hx2).symm)
  have hfib : ∀ P : Sylow 2 G, Nat.card {x : G // x ∈ (P : Subgroup G) ∧ orderOf x = 2} = 3 :=
    fun P => ncc_fiber_card_three h hk hsyl P
  have hcount := ncc_card_involutions_eq_three_mul_sylow hex huniq hfib
  -- the involutions of `G` number `|G : C_G(t)|`
  have hIidx : Nat.card {x : G // orderOf x = 2} = (Subgroup.centralizer ({t} : Set G)).index := by
    rw [← Work.BSW.Api.ncard_involutions_eq_index h]
    rfl
  -- arithmetic
  have hcardN : (Subgroup.normalizer ((Subgroup.centralizer ({t} : Set G)) : Set G)).index *
      Nat.card ↥(Subgroup.normalizer ((Subgroup.centralizer ({t} : Set G)) : Set G)) =
      Nat.card G := Subgroup.index_mul_card _
  have hcardH : (Subgroup.centralizer ({t} : Set G)).index *
      Nat.card ↥(Subgroup.centralizer ({t} : Set G)) = Nat.card G :=
    Subgroup.index_mul_card _
  have hn0 : 0 < (Subgroup.normalizer ((Subgroup.centralizer ({t} : Set G)) : Set G)).index :=
    Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite
  refine Nat.mul_left_cancel hn0 ?_
  rw [hcardN, ← hcardH, ← hIidx, hcount, hH4, ← hsylidx]
  ring

end Work.BSW.Cases
