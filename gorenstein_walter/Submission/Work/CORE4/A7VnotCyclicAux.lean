import Mathlib
import Submission.Work.CORE4.Defs
import Submission.Work.CORE4.Defs10
import Submission.Work.CORE4.CountSetup
import Submission.Work.CORE4.DihOrCycSub
import Submission.Work.CORE4.LayerCtx6
import Submission.Work.CORE4.CentralizerConjMap
import Submission.Work.CORE4.PcoreInMapMulEquiv
import Submission.Work.CORE4.A7ModelO2

open scoped MatrixGroups

namespace Work.CORE4

open Subgroup

variable {G : Type} [Group G] [Finite G]

/-! ## General purpose helpers -/

/-- `O_p(K)`, viewed in `G`, is a `p`-group. -/
theorem isPGroup_pCoreIn (p : ℕ) (K : Subgroup G) : IsPGroup p (Work.GW2.pCoreIn p K) := by
  have hsup : IsPGroup p ↥(sSup {N : Subgroup ↥K | N.Normal ∧ IsPGroup p N}) :=
    Sylow.sSup_of_normal {N : Subgroup ↥K | N.Normal ∧ IsPGroup p N}
      (fun N hN => hN.2) (fun N hN => hN.1)
  exact (hsup.to_le (Subgroup.normalCore_le _)).map K.subtype

/-- `O_p(K) ≤ K`. -/
theorem pCoreIn_le_self (p : ℕ) (K : Subgroup G) : Work.GW2.pCoreIn p K ≤ K :=
  Subgroup.map_subtype_le _

/-- `O_p(K) ◁ K`. -/
theorem subgroupOf_pCoreIn_normal (p : ℕ) (K : Subgroup G) :
    ((Work.GW2.pCoreIn p K).subgroupOf K).Normal := by
  have h : (Work.GW2.pCoreIn p K).subgroupOf K = Work.GW2.pCore p ↥K := by
    rw [Work.GW2.pCoreIn]
    exact Subgroup.comap_map_eq_self_of_injective K.subtype_injective _
  rw [h]
  exact Work.GW2.pCore_normal p ↥K

/-- Conjugation within `K` preserves `O_p(K)`. -/
theorem conj_mem_pCoreIn (p : ℕ) (K : Subgroup G) {h x : G} (hh : h ∈ K)
    (hx : x ∈ Work.GW2.pCoreIn p K) : h * x * h⁻¹ ∈ Work.GW2.pCoreIn p K := by
  obtain ⟨y, hy, hyx⟩ := hx
  have hmem : (⟨h, hh⟩ : ↥K) * y * (⟨h, hh⟩ : ↥K)⁻¹ ∈ Work.GW2.pCore p ↥K :=
    (Work.GW2.pCore_normal p ↥K).conj_mem y hy ⟨h, hh⟩
  exact ⟨_, hmem, by rw [← hyx]; simp⟩

/-- Universal property of `O_p(K)`: a normal `p`-subgroup of `K` lies in it. -/
theorem le_pCoreIn_of_normal_isPGroup (p : ℕ) (K : Subgroup G) {A : Subgroup G} (hA : A ≤ K)
    (hAn : (A.subgroupOf K).Normal) (hAp : IsPGroup p (A.subgroupOf K)) :
    A ≤ Work.GW2.pCoreIn p K := by
  haveI := hAn
  have h1 : A.subgroupOf K ≤ Work.GW2.pCore p (↥K) :=
    Subgroup.normal_le_normalCore.mpr (le_sSup ⟨hAn, hAp⟩)
  calc A = (A.subgroupOf K).map K.subtype := (Subgroup.map_subgroupOf_eq_of_le hA).symm
    _ ≤ (Work.GW2.pCore p (↥K)).map K.subtype := Subgroup.map_mono h1
    _ = Work.GW2.pCoreIn p K := rfl

/-- `IsFourGroup` is carried by a multiplicative equivalence. -/
theorem isFourGroup_map_mulEquiv {G' : Type} [Group G'] (φ : G ≃* G') {V : Subgroup G}
    (hV : Work.GW2.IsFourGroup V) : Work.GW2.IsFourGroup (V.map φ.toMonoidHom) := by
  refine ⟨?_, ?_⟩
  · rw [Subgroup.card_map_of_injective φ.injective]; exact hV.1
  · rintro _ ⟨v, hv, rfl⟩
    show φ.toMonoidHom v ^ 2 = 1
    rw [← map_pow, hV.2 v hv, map_one]

/-- A four-group is not cyclic. -/
theorem not_isCyclic_of_isFourGroup {V : Subgroup G} (hV : Work.GW2.IsFourGroup V) :
    ¬ IsCyclic V := by
  intro hcyc
  haveI : IsCyclic ↥V := hcyc
  obtain ⟨g, hg⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := ↥V)
  have h2 : g ^ 2 = 1 := by
    apply Subtype.ext
    have h := hV.2 (g : G) g.2
    simpa using h
  have hdvd : orderOf g ∣ 2 := orderOf_dvd_iff_pow_eq_one.mpr h2
  rw [hg, hV.1] at hdvd
  omega

/-- A `2`-subgroup and a subgroup of odd order meet trivially. -/
theorem inf_eq_bot_of_two_group_of_odd {A Bc : Subgroup G} (hA : IsPGroup 2 A)
    (hB : Odd (Nat.card Bc)) : A ⊓ Bc = ⊥ := by
  obtain ⟨n, hn⟩ := hA.exists_card_eq
  rw [Subgroup.eq_bot_iff_forall]
  intro x hx
  obtain ⟨hxA, hxB⟩ := Subgroup.mem_inf.mp hx
  have h1 : orderOf x ∣ 2 ^ n := by
    rw [← hn]; exact Subgroup.orderOf_dvd_natCard A hxA
  have h2 : orderOf x ∣ Nat.card Bc := Subgroup.orderOf_dvd_natCard Bc hxB
  have h3 : orderOf x ∣ (2 ^ n).gcd (Nat.card Bc) := Nat.dvd_gcd h1 h2
  have hcop : Nat.Coprime (2 ^ n) (Nat.card Bc) :=
    Nat.Coprime.pow_left n (Nat.coprime_two_left.mpr hB)
  rw [hcop] at h3
  exact orderOf_eq_one_iff.mp (Nat.dvd_one.mp h3)

/-! ## Cyclic groups and four-groups -/

/-- In a cyclic group the involution is unique. -/
theorem eq_of_orderOf_eq_two_of_isCyclic {H : Type*} [Group H] [Finite H] [IsCyclic H]
    {a b : H} (ha : orderOf a = 2) (hb : orderOf b = 2) : a = b := by
  classical
  haveI := Fintype.ofFinite H
  have hd : 2 ∣ Fintype.card H := by
    rw [← Nat.card_eq_fintype_card, ← ha]
    exact orderOf_dvd_natCard a
  have hcard : Fintype.card {x : H // orderOf x = 2} = 1 := by
    rw [Fintype.card_subtype, IsCyclic.card_orderOf_eq_totient (α := H) hd, Nat.totient_two]
  exact Subtype.ext_iff.mp (Fintype.card_le_one_iff.mp (le_of_eq hcard) ⟨a, ha⟩ ⟨b, hb⟩)

/-- A subgroup of a cyclic group is cyclic. -/
theorem isCyclic_of_le_cyclic {S0 V : Subgroup G} (hS0 : IsCyclic S0) (hV : V ≤ S0) :
    IsCyclic V := by
  haveI : IsCyclic ↥S0 := hS0
  haveI : IsCyclic ↥(V.subgroupOf S0) := inferInstance
  exact (MulEquiv.isCyclic (Subgroup.subgroupOfEquivOfLe hV)).mp ‹IsCyclic ↥(V.subgroupOf S0)›

/-- A four-group is never contained in a cyclic group. -/
theorem not_isFourGroup_of_le_cyclic {S0 V : Subgroup G} (hS0 : IsCyclic S0) (hV : V ≤ S0)
    (hV4 : Work.GW2.IsFourGroup V) : False := by
  haveI : IsCyclic ↥V := isCyclic_of_le_cyclic hS0 hV
  exact not_isCyclic_of_isFourGroup hV4 inferInstance

/-! ## Cardinality of preimages -/

/-- The preimage of a subgroup under an injective homomorphism has the cardinality of its
image. -/
theorem card_comap_eq_card_inf_range {X Y : Type*} [Group X] [Group Y] (f : X →* Y)
    (L : Subgroup Y) (hf : Function.Injective f) :
    Nat.card ↥(L.comap f) = Nat.card ↥(L ⊓ f.range) := by
  rw [inf_comm, ← Subgroup.map_comap_eq f L]
  exact Nat.card_congr (Subgroup.equivMapOfInjective (L.comap f) f hf).toEquiv

/-- `IsFourGroup` for a subgroup of `K` and for its image in the ambient group agree. -/
theorem isFourGroup_map_subtype_iff (K : Subgroup G) (L : Subgroup ↥K) :
    Work.GW2.IsFourGroup (L.map K.subtype) ↔ Work.GW2.IsFourGroup L := by
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · rw [← Subgroup.card_map_of_injective K.subtype_injective]; exact h.1
    · intro v hv
      have hm : K.subtype v ∈ L.map K.subtype := Subgroup.mem_map_of_mem K.subtype hv
      have h' := h.2 (K.subtype v) hm
      exact Subtype.ext (by simpa using h')
  · rintro ⟨h1, h2⟩
    refine ⟨?_, ?_⟩
    · rw [Subgroup.card_map_of_injective K.subtype_injective]; exact h1
    · rintro _ ⟨v, hv, rfl⟩
      simpa using congrArg Subtype.val (h2 v hv)

/-! ## `S ≤ C_G(t)` and the `2`-core of a normal subgroup -/

/-- `S₀ ◁ S`. -/
theorem bSetup_S0_normal (B : Work.GW2.BenderSetup G) :
    (B.S0.subgroupOf (B.S : Subgroup G)).Normal := by
  refine Subgroup.normal_of_index_eq_two ?_
  simpa [Subgroup.relIndex] using B.S0_index

/-- **Bender p. 219**: `S ≤ C_G(t) = H`.  The involution `t` of the cyclic subgroup `S₀` is
central in `S`, because `S/S₀` acts on the cyclic group `S₀` and a cyclic group has a unique
element of order two. -/
theorem bSetup_S_le_H (B : Work.GW2.BenderSetup G) : (B.S : Subgroup G) ≤ B.H := by
  intro x hxS
  rw [show B.H = Subgroup.centralizer ({B.t} : Set G) from rfl, Subgroup.mem_centralizer_iff]
  intro y hy
  rw [Set.mem_singleton_iff] at hy
  subst hy
  by_cases hx0 : x ∈ B.S0
  · haveI : IsCyclic ↥B.S0 := B.S0_cyclic
    have h := mul_comm' (⟨B.t, B.t_mem⟩ : ↥B.S0) ⟨x, hx0⟩
    exact congrArg Subtype.val h
  · have hconj : x * B.t * x⁻¹ ∈ B.S0 := by
      have hN := bSetup_S0_normal B
      have hxT : x * B.t * x⁻¹ ∈ (B.S : Subgroup G) :=
        (B.S : Subgroup G).mul_mem
          ((B.S : Subgroup G).mul_mem hxS (B.S0_le B.t_mem)) (inv_mem hxS)
      have hmem : (⟨x * B.t * x⁻¹, hxT⟩ : ↥(B.S : Subgroup G)) ∈
          B.S0.subgroupOf (B.S : Subgroup G) := by
        have hcm := hN.conj_mem (⟨B.t, B.S0_le B.t_mem⟩ : ↥(B.S : Subgroup G))
          (by rw [Subgroup.mem_subgroupOf]; exact B.t_mem) (⟨x, hxS⟩ : ↥(B.S : Subgroup G))
        rw [Subgroup.mem_subgroupOf] at hcm
        exact hcm
      rw [Subgroup.mem_subgroupOf] at hmem
      exact hmem
    have hord : orderOf (x * B.t * x⁻¹) = 2 := by
      have hsemi : SemiconjBy x B.t (x * B.t * x⁻¹) := by
        simp [SemiconjBy, mul_assoc]
      exact (SemiconjBy.orderOf_eq x hsemi).symm.trans B.t_order
    haveI : IsCyclic ↥B.S0 := B.S0_cyclic
    have heq : (⟨x * B.t * x⁻¹, hconj⟩ : ↥B.S0) = ⟨B.t, B.t_mem⟩ :=
      eq_of_orderOf_eq_two_of_isCyclic (a := (⟨x * B.t * x⁻¹, hconj⟩ : ↥B.S0))
        (b := (⟨B.t, B.t_mem⟩ : ↥B.S0))
        (by rw [Subgroup.orderOf_mk]; exact hord)
        (by rw [Subgroup.orderOf_mk]; exact B.t_order)
    have hval : x * B.t * x⁻¹ = B.t := congrArg Subtype.val heq
    have hx1 : x * B.t = B.t * x := by
      have h2 : (x * B.t * x⁻¹) * x = B.t * x := by rw [hval]
      simpa [mul_assoc] using h2
    exact hx1.symm

/-- If `A ◁ K` then `K` normalises `O_p(A)`. -/
theorem conj_mem_pCoreIn_of_normal {A K : Subgroup G} (hA : A ≤ K)
    (hAn : (A.subgroupOf K).Normal) (p : ℕ) {k x : G} (hk : k ∈ K)
    (hx : x ∈ Work.GW2.pCoreIn p A) : k * x * k⁻¹ ∈ Work.GW2.pCoreIn p A := by
  have hgen : ∀ (y : G) (_ : y ∈ A) (g : G) (_ : g ∈ K), g * y * g⁻¹ ∈ A := fun y hy g hg =>
    (Subgroup.normal_subgroupOf_iff hA).mp hAn y g hy hg
  have hmap : A.map (MulAut.conj k).toMonoidHom = A := by
    apply le_antisymm
    · rintro y ⟨z, hz, rfl⟩
      simpa [MulAut.conj_apply] using hgen z hz k hk
    · intro y hy
      refine Subgroup.mem_map.mpr ⟨k⁻¹ * y * k, ?_, ?_⟩
      · simpa using hgen y hy k⁻¹ (K.inv_mem hk)
      · show k * (k⁻¹ * y * k) * k⁻¹ = y
        group
  have key : (Work.GW2.pCoreIn p A).map (MulAut.conj k).toMonoidHom = Work.GW2.pCoreIn p A := by
    rw [← PcoreInMapMulEquiv (MulAut.conj k) p A, hmap]
  have hx' : (MulAut.conj k) x ∈ (Work.GW2.pCoreIn p A).map (MulAut.conj k).toMonoidHom :=
    Subgroup.mem_map_of_mem _ hx
  have hx'' : (MulAut.conj k) x ∈ Work.GW2.pCoreIn p A := key ▸ hx'
  rwa [MulAut.conj_apply] at hx''

/-- If `A ◁ K` then `O_p(A) ≤ O_p(K)`. -/
theorem pCoreIn_le_pCoreIn_of_normal {A K : Subgroup G} (hA : A ≤ K)
    (hAn : (A.subgroupOf K).Normal) (p : ℕ) : Work.GW2.pCoreIn p A ≤ Work.GW2.pCoreIn p K := by
  have hAK : Work.GW2.pCoreIn p A ≤ K := (pCoreIn_le_self p A).trans hA
  refine le_pCoreIn_of_normal_isPGroup p K hAK ?_ ?_
  · rw [Subgroup.normal_subgroupOf_iff hAK]
    intro a b ha hb
    exact conj_mem_pCoreIn_of_normal hA hAn p hb ha
  · exact (isPGroup_pCoreIn p A).of_equiv (Subgroup.subgroupOfEquivOfLe hAK).symm

/-- `O_p(X)` lies in every Sylow `p`-subgroup of `X`. -/
theorem pCoreIn_le_sylow (p : ℕ) [Fact p.Prime] (K : Subgroup G) (P : Sylow p ↥K) :
    (Work.GW2.pCoreIn p K).subgroupOf K ≤ (P : Subgroup ↥K) := by
  haveI := subgroupOf_pCoreIn_normal p K
  exact IsPGroup.le_sylow_of_normal
    ((isPGroup_pCoreIn p K).of_equiv (Subgroup.subgroupOfEquivOfLe (pCoreIn_le_self p K)).symm) P

/-- If the kernel of `f` meets `H` trivially then `H` and `H.map f` have the same cardinality. -/
theorem card_map_eq_card_of_disjoint_ker {X Y : Type*} [Group X] [Group Y] (f : X →* Y)
    {H : Subgroup X} (h : H ⊓ f.ker = ⊥) : Nat.card ↥(H.map f) = Nat.card ↥H :=
  (Nat.card_congr (Equiv.ofBijective
    (fun x : ↥H => (⟨f x, Subgroup.mem_map_of_mem f x.2⟩ : ↥(H.map f)))
    ⟨fun x y hxy => by
      have h2 : f (x : X) = f (y : X) := congrArg Subtype.val hxy
      have h3 : f ((x : X) * (y : X)⁻¹) = 1 := by
        rw [map_mul, map_inv, h2, mul_inv_cancel]
      have h4 : (x : X) * (y : X)⁻¹ ∈ H ⊓ f.ker :=
        ⟨H.mul_mem x.2 (H.inv_mem y.2), MonoidHom.mem_ker.mpr h3⟩
      rw [h] at h4
      exact Subtype.ext (mul_inv_eq_one.mp (Subgroup.mem_bot.mp h4)),
     fun y => by
      obtain ⟨x, hx, hxy⟩ := Subgroup.mem_map.mp y.2
      exact ⟨⟨x, hx⟩, Subtype.ext hxy⟩⟩)).symm

/-- **Cardinality of a preimage**: `Nat.card H = |H.map f| · |ker f|` when `ker f ≤ H`. -/
theorem card_eq_card_map_mul_card_ker {X Y : Type*} [Group X] [Group Y] (f : X →* Y)
    (H : Subgroup X) (hker : f.ker ≤ H) :
    Nat.card ↥H = Nat.card ↥(H.map f) * Nat.card ↥f.ker := by
  set g : ↥H →* Y := f.comp H.subtype with hg
  have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup g.ker
  have h2 : Nat.card (↥H ⧸ g.ker) = Nat.card ↥g.range :=
    Nat.card_congr (QuotientGroup.quotientKerEquivRange g).toEquiv
  have hr : g.range = H.map f := by
    rw [hg, MonoidHom.range_eq_map, ← Subgroup.map_map,
      show (⊤ : Subgroup ↥H).map H.subtype = H from
        (MonoidHom.range_eq_map H.subtype).symm.trans (Subgroup.range_subtype H)]
  have hk : Nat.card ↥g.ker = Nat.card ↥f.ker := by
    have h3 : g.ker = f.ker.subgroupOf H := by
      ext x
      rw [MonoidHom.mem_ker, hg, MonoidHom.comp_apply, Subgroup.mem_subgroupOf,
        MonoidHom.mem_ker]
      rfl
    rw [h3]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hker).toEquiv
  rw [h2, hr, hk] at h1
  exact h1

/-- **A four-group from a central cover**: if `V ≤ X`, `|V| = 4`, `V` has exponent `2`, and every
element of `X` is a product `z * v` with `z` central in `X` and `v ∈ V`, then `V ◁ X`. -/
theorem subgroupOf_normal_of_central_cover {X V Z : Subgroup G} (hVX : V ≤ X)
    (hZc : ∀ z ∈ Z, ∀ x ∈ X, x * z = z * x)
    (hVcard : Nat.card V = 4) (hVexp : ∀ v ∈ V, v ^ 2 = 1)
    (hcover : ∀ x ∈ X, ∃ v ∈ V, ∃ z ∈ Z, x = z * v) :
    (V.subgroupOf X).Normal := by
  have hcomm : ∀ a ∈ V, ∀ v ∈ V, a * v = v * a := by
    intro a ha v hv
    have h1 : (a * v) ^ 2 = 1 := hVexp (a * v) (V.mul_mem ha hv)
    have h2 : a ^ 2 = 1 := hVexp a ha
    have h3 : v ^ 2 = 1 := hVexp v hv
    have h1' : a * v * (a * v) = 1 := by rw [← pow_two]; exact h1
    have h2' : a * a = 1 := by rw [← pow_two]; exact h2
    have h3' : v * v = 1 := by rw [← pow_two]; exact h3
    calc a * v = (a * v)⁻¹ := (inv_eq_of_mul_eq_one_right h1').symm
      _ = v⁻¹ * a⁻¹ := mul_inv_rev a v
      _ = v * a := by rw [inv_eq_of_mul_eq_one_right h3', inv_eq_of_mul_eq_one_right h2']
  rw [Subgroup.normal_subgroupOf_iff hVX]
  intro h x hh hx
  obtain ⟨v, hv, z, hz, hxz⟩ := hcover x hx
  have hcv : v * h = h * v := hcomm v hv h hh
  have hcz : z * h = h * z := (hZc z hz h (hVX hh)).symm
  have hx' : z * v * h * (z * v)⁻¹ = h := by
    calc z * v * h * (z * v)⁻¹ = z * (v * h * v⁻¹) * z⁻¹ := by group
      _ = z * (h * v * v⁻¹) * z⁻¹ := by rw [hcv]
      _ = z * h * z⁻¹ := by group
      _ = h * z * z⁻¹ := by rw [hcz]
      _ = h := by group
  rw [hxz, hx']
  exact hh

end Work.CORE4
