import Mathlib
import Submission.Work.CORE2B.Defs

/-!
# CORE2B — the fusion chain of Bender 1981, Lemma 2.9 (p. 222)

Let `A ≤ N` be a normal subgroup of odd order, `V ≤ N` a Klein four-group, and `t, s ∈ V`
distinct involutions that are `N`-conjugate (`g t g⁻¹ = s` with `g ∈ N`).  In the "bad" case
where `V` centralizes the fixed points of `t` on `A` (`C_A(t) = C_A(V)`), the whole group `A`
is centralized by the product `t * s`.

The proof is a three-step fusion chain:

* `V ≤ C_G(C_A(t))` gives `C_A(t) ≤ C_A(s)`; since `A ◁ N` and `g ∈ N`, conjugation by `g`
  carries `C_A(t)` onto `C_A(s)`, so the two subgroups have the same order, hence are equal.
* `V ≤ C_G(C_A(t))` also gives `C_A(t) ≤ C_A(t * s)`, since `t * s ∈ V`.
* Bender's coprime action 1.1(iii) (`Work.GW2.Coprime11iiiProp`) applied to the 2-group `V`
  acting on the odd group `A` splits `A` as the join of the three subgroups `C_A(a)`, `a ∈ V#`,
  i.e. `A = C_A(t) ⊔ C_A(s) ⊔ C_A(t * s)`.  Each of the three summands is contained in
  `C_A(t * s)`, so `A ≤ C_A(t * s)`, as required.
-/

namespace Work.CORE2B

open Subgroup

/-! ## Elementary helpers -/

/-- `x` commutes with `y` iff `x` lies in the centralizer of `{y}`. -/
private theorem L29_mem_centralizer_singleton_iff {G : Type} [Group G] {x y : G} :
    x ∈ Subgroup.centralizer ({y} : Set G) ↔ y * x = x * y := by
  rw [Subgroup.mem_centralizer_iff]
  exact ⟨fun h => h y (Set.mem_singleton y), fun h z hz => by
    rw [Set.mem_singleton_iff] at hz
    subst hz
    exact h⟩

/-- Conjugation by `g` carries `C_G({y})` onto `C_G({g y g⁻¹})`. -/
private theorem L29_conjSub_centralizer_singleton {G : Type} [Group G] (g y : G) :
    Work.GW2.conjSub g (Subgroup.centralizer ({y} : Set G))
      = Subgroup.centralizer ({g * y * g⁻¹} : Set G) := by
  ext x
  show x ∈ (Subgroup.centralizer ({y} : Set G)).map (MulAut.conj g).toMonoidHom ↔
      x ∈ Subgroup.centralizer ({g * y * g⁻¹} : Set G)
  rw [Subgroup.mem_map]
  constructor
  · rintro ⟨z, hz, rfl⟩
    rw [L29_mem_centralizer_singleton_iff] at hz ⊢
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    rw [show g * y * g⁻¹ * (g * z * g⁻¹) = g * (y * z) * g⁻¹ by group,
        show g * z * g⁻¹ * (g * y * g⁻¹) = g * (z * y) * g⁻¹ by group, hz]
  · intro hx
    rw [L29_mem_centralizer_singleton_iff] at hx
    refine ⟨g⁻¹ * x * g, ?_, ?_⟩
    · rw [L29_mem_centralizer_singleton_iff]
      rw [show y * (g⁻¹ * x * g) = g⁻¹ * (g * y * g⁻¹ * x) * g by group,
          show (g⁻¹ * x * g) * y = g⁻¹ * (x * (g * y * g⁻¹)) * g by group, hx]
    · simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      group

/-- `conjSub g` preserves intersections. -/
private theorem L29_conjSub_inf {G : Type} [Group G] (g : G) (H K : Subgroup G) :
    Work.GW2.conjSub g (H ⊓ K) = Work.GW2.conjSub g H ⊓ Work.GW2.conjSub g K :=
  Subgroup.map_inf H K _ (MulAut.conj g).injective

/-- If `A ◁ N` (as a subgroup of `N`) and `g ∈ N`, then conjugation by `g` fixes `A`. -/
private theorem L29_conjSub_eq_self_of_normal {G : Type} [Group G] {A N : Subgroup G}
    (hAN : A ≤ N) (hAnorm : (A.subgroupOf N).Normal) {g : G} (hg : g ∈ N) :
    Work.GW2.conjSub g A = A := by
  have key : ∀ n ∈ N, ∀ a ∈ A, n * a * n⁻¹ ∈ A :=
    fun n hn a ha => (Subgroup.normal_subgroupOf_iff hAN).mp hAnorm a n ha hn
  apply le_antisymm
  · intro x hx
    rw [Work.GW2.conjSub, Subgroup.mem_map] at hx
    obtain ⟨a, ha, rfl⟩ := hx
    rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    exact key g hg a ha
  · intro x hx
    rw [Work.GW2.conjSub, Subgroup.mem_map]
    have h1 : g⁻¹ * x * g ∈ A := by simpa using key g⁻¹ (N.inv_mem hg) x hx
    exact ⟨g⁻¹ * x * g, h1, by rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]; group⟩

/-- A Klein four-group has exponent two, hence is abelian. -/
private theorem L29_isMulCommutative_of_isFourGroup {G : Type} [Group G] {V : Subgroup G}
    (hV : Work.GW2.IsFourGroup V) : IsMulCommutative V := by
  obtain ⟨hcard, hsq⟩ := hV
  refine IsMulCommutative.of_comm (fun x y => ?_)
  apply Subtype.ext
  show (x : G) * y = (y : G) * x
  have hx : (x : G) * x = 1 := by simpa [pow_two] using hsq x x.2
  have hy : (y : G) * y = 1 := by simpa [pow_two] using hsq y y.2
  have hxy : ((x * y : V) : G) * ((x * y : V) : G) = 1 := by
    have := hsq ((x * y : V) : G) (x * y).2
    simpa [pow_two] using this
  have hx' : (x : G)⁻¹ = x := inv_eq_of_mul_eq_one_left hx
  have hy' : (y : G)⁻¹ = y := inv_eq_of_mul_eq_one_left hy
  have h1 : ((x : G) * y) * ((x : G) * y) = 1 := by simpa using hxy
  have h3 : ((x : G) * y)⁻¹ = (x : G) * y := inv_eq_of_mul_eq_one_left h1
  calc (x : G) * y = ((x : G) * y)⁻¹ := h3.symm
    _ = (y : G)⁻¹ * (x : G)⁻¹ := mul_inv_rev _ _
    _ = (y : G) * x := by rw [hx', hy']

/-- **The Klein four-group is `{1, t, s, t * s}`.**  For two distinct non-identity elements
`t ≠ s` of a four-group `V`, every non-identity element of `V` is one of `t`, `s`, `t * s`. -/
private theorem L29_mem_fourGroup_cases {G : Type} [Group G] [Finite G] {V : Subgroup G}
    (hV : Work.GW2.IsFourGroup V) {t s a : G} (ht : t ∈ V) (hs : s ∈ V)
    (ht1 : t ≠ 1) (hs1 : s ≠ 1) (hne : s ≠ t) (ha : a ∈ V) (ha1 : a ≠ 1) :
    a = t ∨ a = s ∨ a = t * s := by
  obtain ⟨hcard, hsq⟩ := hV
  have hts : t * s ∈ V := V.mul_mem ht hs
  have htt : t * t = 1 := by simpa [pow_two] using hsq t ht
  have hss : s * s = 1 := by simpa [pow_two] using hsq s hs
  have hts_ne_one : t * s ≠ 1 := by
    intro h
    refine hne ?_
    calc s = t * (t * s) := by rw [← mul_assoc, htt, one_mul]
      _ = t * 1 := by rw [h]
      _ = t := mul_one t
  have hts_ne_t : t * s ≠ t := by
    intro h
    refine hs1 ?_
    calc s = t * (t * s) := by rw [← mul_assoc, htt, one_mul]
      _ = t * t := by rw [h]
      _ = 1 := htt
  have hts_ne_s : t * s ≠ s := by
    intro h
    refine ht1 ?_
    calc t = (t * s) * s := by rw [mul_assoc, hss, mul_one]
      _ = s * s := by rw [h]
      _ = 1 := hss
  have h3 : ({s, t * s} : Set G).ncard = 2 := by
    rw [Set.ncard_insert_of_notMem, Set.ncard_singleton]
    simp only [Set.mem_singleton_iff]
    exact fun h => hts_ne_s h.symm
  have h2 : ({t, s, t * s} : Set G).ncard = 3 := by
    rw [Set.ncard_insert_of_notMem, h3]
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
    exact ⟨fun h => hne h.symm, fun h => hts_ne_t h.symm⟩
  have h4 : ({1, t, s, t * s} : Set G).ncard = 4 := by
    rw [Set.ncard_insert_of_notMem, h2]
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
    exact ⟨fun h => ht1 h.symm, fun h => hs1 h.symm, fun h => hts_ne_one h.symm⟩
  have hsub : ({1, t, s, t * s} : Set G) ⊆ (V : Set G) := by
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · exact V.one_mem
    · exact ht
    · exact hs
    · exact hts
  have hVncard : (V : Set G).ncard = 4 := by
    rw [← Nat.card_coe_set_eq]
    exact hcard
  have heq : (V : Set G) = {1, t, s, t * s} := by
    refine (Set.eq_of_subset_of_ncard_le hsub ?_).symm
    rw [hVncard, h4]
  have hmem : a ∈ ({1, t, s, t * s} : Set G) := by rw [← heq]; exact ha
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hmem
  rcases hmem with h | h | h | h
  · exact absurd h ha1
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr h)

/-! ## The fusion chain -/

/-- **The fusion chain of Bender 1981, Lemma 2.9.**  Let `A ◁ N` have odd order, let `V ≤ N` be a
Klein four-group, and let `t, s ∈ V` be distinct involutions conjugated by `g ∈ N`
(`g * t * g⁻¹ = s`).  If `V` centralizes `C_A(t)`, then `t * s` centralizes `A`. -/
theorem L29_fusion_chain (h11iii : Work.GW2.Coprime11iiiProp) {G : Type} [Group G] [Finite G]
    (A N : Subgroup G) (hAN : A ≤ N) (hAnorm : (A.subgroupOf N).Normal) (hodd : Odd (Nat.card A))
    (V : Subgroup G) (hV : Work.GW2.IsFourGroup V) (hVN : V ≤ N)
    (t s g : G) (ht : t ∈ V) (hs : s ∈ V) (hne : s ≠ t) (hgN : g ∈ N) (hgt : g * t * g⁻¹ = s)
    (hbad : V ≤ Subgroup.centralizer ((Subgroup.centralizer ({t} : Set G) ⊓ A : Subgroup G) : Set G)) :
    A ≤ Subgroup.centralizer ({t * s} : Set G) := by
  classical
  have hVcard : Nat.card V = 4 := hV.1
  have hVsq : ∀ v ∈ V, v ^ 2 = 1 := hV.2
  -- `t, s ≠ 1`: `t = 1` would force `s = g * 1 * g⁻¹ = 1 = t`, and symmetrically.
  have ht_ne_one : t ≠ 1 := by
    intro h1
    refine hne ?_
    have hs1 : s = 1 := by rw [← hgt, h1]; group
    rw [hs1, h1]
  have hs_ne_one : s ≠ 1 := by
    intro h1
    refine hne ?_
    have ht1 : t = 1 := by
      calc t = g⁻¹ * (g * t * g⁻¹) * g := by group
        _ = g⁻¹ * s * g := by rw [hgt]
        _ = 1 := by rw [h1]; group
    rw [h1, ht1]
  -- Rewrite the hypothesis `hbad` with the intersection in the order `A ⊓ C_G(t)`.
  have hbad1 : V ≤ Subgroup.centralizer
      ((A ⊓ Subgroup.centralizer ({t} : Set G) : Subgroup G) : Set G) := by
    simpa only [inf_comm] using hbad
  -- Step 1: `C_A(t) ≤ C_A(s)`.
  have hCt_le_Cs : A ⊓ Subgroup.centralizer ({t} : Set G) ≤
      A ⊓ Subgroup.centralizer ({s} : Set G) := by
    intro x hx
    rw [Subgroup.mem_inf] at hx ⊢
    refine ⟨hx.1, ?_⟩
    rw [L29_mem_centralizer_singleton_iff]
    have hxZ : x ∈ (A ⊓ Subgroup.centralizer ({t} : Set G) : Subgroup G) := ⟨hx.1, hx.2⟩
    have hscent := (Subgroup.mem_centralizer_iff.mp (hbad1 hs)) x hxZ
    exact hscent.symm
  -- Step 2: `C_A(s) = g C_A(t) g⁻¹`, so the two have the same order, hence are equal.
  have hconjA : Work.GW2.conjSub g A = A := L29_conjSub_eq_self_of_normal hAN hAnorm hgN
  have hconjC : Work.GW2.conjSub g (Subgroup.centralizer ({t} : Set G)) =
      Subgroup.centralizer ({s} : Set G) := by
    rw [L29_conjSub_centralizer_singleton, hgt]
  have hCs_eq : A ⊓ Subgroup.centralizer ({s} : Set G) =
      Work.GW2.conjSub g (A ⊓ Subgroup.centralizer ({t} : Set G)) := by
    rw [L29_conjSub_inf, hconjA, hconjC]
  have hcard_Cs : Nat.card (A ⊓ Subgroup.centralizer ({s} : Set G) : Subgroup G) =
      Nat.card (A ⊓ Subgroup.centralizer ({t} : Set G) : Subgroup G) := by
    rw [hCs_eq, Work.GW2.conjSub,
      Subgroup.card_map_of_injective (MulAut.conj g).injective]
  have hCt_eq_Cs : A ⊓ Subgroup.centralizer ({t} : Set G) =
      A ⊓ Subgroup.centralizer ({s} : Set G) :=
    Subgroup.eq_of_le_of_card_ge hCt_le_Cs (le_of_eq hcard_Cs)
  -- Step 3: `C_A(t) ≤ C_A(t * s)`, because `t * s ∈ V` centralizes `C_A(t)`.
  have hCt_le_Cts : A ⊓ Subgroup.centralizer ({t} : Set G) ≤
      A ⊓ Subgroup.centralizer ({t * s} : Set G) := by
    intro x hx
    rw [Subgroup.mem_inf] at hx ⊢
    refine ⟨hx.1, ?_⟩
    rw [L29_mem_centralizer_singleton_iff]
    have hxZ : x ∈ (A ⊓ Subgroup.centralizer ({t} : Set G) : Subgroup G) := ⟨hx.1, hx.2⟩
    have htsV : t * s ∈ V := V.mul_mem ht hs
    have hcent := (Subgroup.mem_centralizer_iff.mp (hbad1 htsV)) x hxZ
    exact hcent.symm
  -- Bender 1.1(iii): `A` is the join of the three centralizers `C_A(a)`, `a ∈ V#`.
  have hNnorm : N ≤ Subgroup.normalizer (A : Set G) :=
    Subgroup.le_normalizer_iff.mpr (fun n hn a ha =>
      (Subgroup.normal_subgroupOf_iff hAN).mp hAnorm a n ha hn)
  have hVnorm : V ≤ Subgroup.normalizer (A : Set G) := hVN.trans hNnorm
  have hVp2 : IsPGroup 2 V := IsPGroup.of_card (n := 2) (by rw [hVcard]; norm_num)
  have hcop : Nat.Coprime 2 (Nat.card A) := Nat.coprime_two_left.mpr hodd
  have hVcomm : IsMulCommutative V := L29_isMulCommutative_of_isFourGroup hV
  have hsplit := h11iii G 2 V A V hVp2 hcop hVnorm le_rfl
    (by rw [hVcard]; norm_num) hVsq hVcomm
  have hle_sup : (⨆ (a : G) (_ : a ∈ V) (_ : a ≠ 1), A ⊓ Subgroup.centralizer ({a} : Set G))
      ≤ A ⊓ Subgroup.centralizer ({t * s} : Set G) := by
    refine iSup_le (fun a => iSup_le (fun haV => iSup_le (fun ha1 => ?_)))
    rcases L29_mem_fourGroup_cases hV ht hs ht_ne_one hs_ne_one hne haV ha1 with h | h | h
    · rw [h]; exact hCt_le_Cts
    · rw [h, ← hCt_eq_Cs]; exact hCt_le_Cts
    · rw [h]
  rw [hsplit]
  exact hle_sup.trans inf_le_right

end Work.CORE2B
