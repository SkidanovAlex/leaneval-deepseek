/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gorenstein–Walter formalisation team (area CORE4, `Work.CORE4`)

# CORE4: the 2-rank of a group with cyclic or dihedral Sylow 2-subgroups is at most two

`Work.CORE4.ElementaryAbelianRankTwo`: if `V ≤ G` is a Klein four-group (`IsFourGroup V`, i.e.
`|V| = 4` and every element of `V` is an involution) and `y` is an involution of `G` which lies
outside `V` and centralizes `V`, then `G` cannot have cyclic-or-dihedral Sylow 2-subgroups.

The mathematics is the elementary two-rank argument.  Because `y` centralizes the Klein four-group
`V`, the subgroup `D = V ⊔ ⟨y⟩` is *elementary abelian*: its elements commute and each of them
squares to `1`.  If `y ∉ V`, then `D` strictly contains `V`, so `|D| ≥ 2·|V| = 8`.  On the other
hand a group whose Sylow 2-subgroups are cyclic or dihedral has 2-rank at most two — every subgroup
all of whose elements are involutions has at most `4` elements (`card_le_four_of_sq_eq_one` below,
which reduces to Sylow, to Mathlib's cyclic case and to the dihedral 2-rank fact of area RED) — so
`|D| ≤ 4`.  The two bounds contradict each other.

The cardinality `|D| = 8` is never computed: since `V ≤ D` and `|V| = 4`, the order of `D` is a
multiple of `4`, and `|D| ≤ 4` forces `|D| = 4`, whence `V = D` and `y ∈ V`, contradicting `hyV`
(this is the trick used by `Work.CORE2A.odd_card_centralizer_of_four_subgroup`).

Imports.  The statement uses the vocabulary of this area (`Submission.Work.CORE4.Defs`); the
dihedral input `elementary_abelian_card_le_four` comes from area RED
(`Submission.Work.RED.DihedralFacts`, which is proved, is sorry-free and, like this file, builds on
`Submission.Work.CORE4.Defs`).  The alternative rank theorem of area DSTR, `Work.DSTR.twoRank`,
lives in the disjoint copy of the contract vocabulary (`Submission.Work.ASM.Defs`) and can
therefore not be imported together with `Submission.Work.CORE4.Defs`.
-/
import Mathlib
import Submission.Work.CORE4.Defs
import Submission.Work.RED.DihedralFacts

namespace Work.CORE4

open Subgroup

/-! ## Elementary commutation lemmas for joins -/

/-- Two elements of a commutative subgroup commute. -/
lemma mul_comm_of_mem_of_isMulCommutative {G : Type*} [Group G] {H : Subgroup G}
    (hH : IsMulCommutative ↥H) {x y : G} (hx : x ∈ H) (hy : y ∈ H) : x * y = y * x :=
  congrArg Subtype.val (mul_comm' (⟨x, hx⟩ : ↥H) ⟨y, hy⟩)

/-- The join of two commutative subgroups that centralize each other is commutative. -/
lemma isMulCommutative_sup_of_le_centralizer {G : Type*} [Group G] {H K : Subgroup G}
    (hHK : K ≤ Subgroup.centralizer (H : Set G)) (hH : IsMulCommutative ↥H)
    (hK : IsMulCommutative ↥K) : IsMulCommutative ↥(H ⊔ K) := by
  -- it suffices that the join centralizes itself, and it does because the generating set
  -- `H ∪ K` consists of pairwise commuting elements
  have hsup : (H ⊔ K : Subgroup G) ≤ Subgroup.centralizer (((H ⊔ K : Subgroup G)) : Set G) := by
    rw [Subgroup.sup_eq_closure, Subgroup.centralizer_closure, Subgroup.closure_le]
    intro x hx
    change x ∈ Subgroup.centralizer ((H : Set G) ∪ (K : Set G))
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    rcases hx with hxH | hxK
    · rcases hy with hyH | hyK
      · exact (mul_comm_of_mem_of_isMulCommutative hH hxH hyH).symm
      · exact ((Subgroup.mem_centralizer_iff.mp (hHK hyK)) x hxH).symm
    · rcases hy with hyH | hyK
      · exact (Subgroup.mem_centralizer_iff.mp (hHK hxK)) y hyH
      · exact (mul_comm_of_mem_of_isMulCommutative hK hxK hyK).symm
  refine IsMulCommutative.of_comm fun a b => Subtype.ext ?_
  exact ((Subgroup.mem_centralizer_iff.mp (hsup a.2)) (b : G) b.2).symm

/-- A subgroup all of whose elements are involutions is commutative (in a group, `a ^ 2 = 1` and
`b ^ 2 = 1` and `(a * b) ^ 2 = 1` give `a * b = b * a`). -/
lemma isMulCommutative_of_forall_sq_eq_one {G : Type*} [Group G] {H : Subgroup G}
    (h2 : ∀ x ∈ H, x ^ 2 = 1) : IsMulCommutative ↥H := by
  refine IsMulCommutative.of_comm fun x z => ?_
  have hx : x ^ 2 = 1 := Subtype.ext (by simpa using h2 x x.2)
  have hz : z ^ 2 = 1 := Subtype.ext (by simpa using h2 z z.2)
  have hx' : x⁻¹ = x := inv_eq_of_mul_eq_one_left (by simpa [pow_two] using hx)
  have hz' : z⁻¹ = z := inv_eq_of_mul_eq_one_left (by simpa [pow_two] using hz)
  have hxz : (x * z) ^ 2 = 1 := Subtype.ext (by simpa using h2 (x * z) (mul_mem x.2 z.2))
  have h1 : x * z = (x * z)⁻¹ := by
    have h2' : (x * z) * (x * z) = 1 := by simpa [pow_two] using hxz
    exact (inv_eq_of_mul_eq_one_left h2').symm
  rw [h1]
  show (x * z)⁻¹ = z * x
  rw [mul_inv_rev, hx', hz']

/-- A Klein four-group is commutative. -/
lemma isMulCommutative_of_isFourGroup {G : Type*} [Group G] {V : Subgroup G}
    (hV : Work.GW2.IsFourGroup V) : IsMulCommutative ↥V :=
  isMulCommutative_of_forall_sq_eq_one hV.2

/-- `⟨y⟩` is commutative. -/
lemma isMulCommutative_zpowers (G : Type*) [Group G] (y : G) :
    IsMulCommutative ↥(Subgroup.zpowers y) := by
  refine IsMulCommutative.of_comm fun a b => Subtype.ext ?_
  obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp a.2
  obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp b.2
  show (a : G) * (b : G) = (b : G) * (a : G)
  rw [← hm, ← hn, ← zpow_add, ← zpow_add, add_comm]

/-! ## The 2-rank is at most two -/

/-- A cyclic group all of whose elements square to `1` has at most two elements (it is generated
by an element of order dividing `2`). -/
lemma card_le_two_of_isCyclic_of_sq_eq_one {H : Type*} [Group H] (hcyc : IsCyclic H)
    (h2 : ∀ x : H, x ^ 2 = 1) : Nat.card H ≤ 2 := by
  obtain ⟨g, htop⟩ := isCyclic_iff_exists_zpowers_eq_top.mp hcyc
  have horder : orderOf g ∣ 2 := orderOf_dvd_iff_pow_eq_one.mpr (h2 g)
  calc Nat.card H = Nat.card ↥(⊤ : Subgroup H) :=
        (Nat.card_congr (Subgroup.topEquiv : ↥(⊤ : Subgroup H) ≃* H)).symm
    _ = Nat.card ↥(Subgroup.zpowers g) :=
        (congrArg (fun K : Subgroup H => Nat.card ↥K) htop).symm
    _ = orderOf g := Nat.card_zpowers g
    _ ≤ 2 := Nat.le_of_dvd (by norm_num) horder

/-- **The 2-rank bound.**  If the Sylow 2-subgroups of a finite group `X` are cyclic or dihedral,
then every subgroup `E ≤ X` all of whose elements are involutions has at most `4` elements.

`E` is a 2-group, so it lies in a Sylow 2-subgroup `Q`.  If `Q` is cyclic, `E` is cyclic of
exponent `2`, hence `|E| ≤ 2`.  If `Q` is dihedral, isomorphic to `DihedralGroup n` through
`e`, then `E` embeds in `DihedralGroup n` as a subgroup all of whose elements are involutions,
and the dihedral 2-rank fact `Work.RED.DihedralFacts.elementary_abelian_card_le_four` gives
`|E| ≤ 4`. -/
lemma card_le_four_of_sq_eq_one {X : Type} [Group X] [Finite X]
    (hsyl : Work.GW2.DihOrCycSylow X) (E : Subgroup X) (h2 : ∀ x ∈ E, x ^ 2 = 1) :
    Nat.card ↥E ≤ 4 := by
  have h2E : ∀ g : ↥E, g ^ 2 = 1 := fun g => Subtype.ext (by simpa using h2 (g : X) g.2)
  -- `E` has exponent `2`, so it is a 2-group and lies in a Sylow 2-subgroup of `X`
  have hPE : IsPGroup 2 ↥E := by
    rw [isPGroup_iff_orderOf_dvd_pow]
    intro g
    exact ⟨1, by rw [pow_one, orderOf_dvd_iff_pow_eq_one]; exact h2E g⟩
  obtain ⟨Q, hEQ⟩ := hPE.exists_le_sylow
  rcases hsyl Q with hcycQ | ⟨n, ⟨e⟩⟩
  · -- `Q` cyclic: `E` is cyclic of exponent `2`
    haveI : IsCyclic ↥E := @Subgroup.isCyclic_of_le X _ E (Q : Subgroup X) hEQ hcycQ
    have hle2 := card_le_two_of_isCyclic_of_sq_eq_one (inferInstance : IsCyclic ↥E) h2E
    omega
  · -- `Q` dihedral: transport `E` into `DihedralGroup n` along `e`
    have hn : n ≠ 0 := by
      intro h0
      have hcard : Nat.card ↥Q = Nat.card (DihedralGroup n) := Nat.card_congr e.toEquiv
      have hzero : Nat.card ↥Q = 0 := by rw [hcard, DihedralGroup.nat_card, h0, mul_zero]
      haveI : Nonempty ↥Q := ⟨1⟩
      exact absurd hzero (Nat.card_pos.ne')
    haveI : NeZero n := ⟨hn⟩
    let f : ↥E →* DihedralGroup n := e.toMonoidHom.comp (Subgroup.inclusion hEQ)
    have hfinj : Function.Injective f := e.injective.comp (Subgroup.inclusion_injective hEQ)
    let A : Subgroup (DihedralGroup n) := (⊤ : Subgroup ↥E).map f
    have hAcard : Nat.card ↥A = Nat.card ↥E := by
      rw [Subgroup.card_map_of_injective hfinj]
      simp
    have hA2 : ∀ x ∈ A, x ^ 2 = 1 := by
      intro x hx
      simp only [A, Subgroup.mem_map, Subgroup.mem_top, true_and] at hx
      obtain ⟨w, rfl⟩ := hx
      rw [← map_pow, h2E w, map_one]
    have h4 := Work.RED.DihedralFacts.elementary_abelian_card_le_four n A hA2
    rw [← hAcard]
    exact h4

/-- **The join with an outside involution.**  Let `V ≤ G` be a Klein four-group and let `y ∈ G`
be an involution centralizing `V`.  Then `y ∈ V`: the join `V ⊔ ⟨y⟩` is elementary abelian, so
the 2-rank bound forces `|V ⊔ ⟨y⟩| ≤ 4 = |V|`, and hence `V ⊔ ⟨y⟩ = V`. -/
lemma mem_of_isFourGroup_of_sq_eq_one {G : Type} [Group G] [Finite G]
    (hsyl : Work.GW2.DihOrCycSylow G) (V : Subgroup G) (hV : Work.GW2.IsFourGroup V)
    (y : G) (hy2 : y ^ 2 = 1) (hcomm : y ∈ Subgroup.centralizer (V : Set G)) : y ∈ V := by
  -- `D = V ⊔ ⟨y⟩` is elementary abelian
  have hzpC : Subgroup.zpowers y ≤ Subgroup.centralizer (V : Set G) :=
    Subgroup.zpowers_le.mpr hcomm
  have hDcomm : IsMulCommutative ↥(V ⊔ Subgroup.zpowers y : Subgroup G) :=
    isMulCommutative_sup_of_le_centralizer hzpC (isMulCommutative_of_isFourGroup hV)
      (isMulCommutative_zpowers G y)
  have hD2 : ∀ x ∈ (V ⊔ Subgroup.zpowers y : Subgroup G), x ^ 2 = 1 := by
    -- the elements of `D` that square to `1` form a subgroup containing the generators
    let T : Subgroup G :=
      { carrier := {x : G | x ∈ (V ⊔ Subgroup.zpowers y : Subgroup G) ∧ x ^ 2 = 1}
        mul_mem' := by
          intro a b ha hb
          obtain ⟨haD, ha2⟩ := ha
          obtain ⟨hbD, hb2⟩ := hb
          have hc : Commute a b := mul_comm_of_mem_of_isMulCommutative hDcomm haD hbD
          exact ⟨mul_mem haD hbD, by rw [hc.mul_pow 2, ha2, hb2, one_mul]⟩
        one_mem' := ⟨one_mem _, by simp⟩
        inv_mem' := by
          intro a ha
          obtain ⟨haD, ha2⟩ := ha
          exact ⟨inv_mem haD, by rw [inv_pow, ha2, inv_one]⟩ }
    have hmem : ∀ x : G, x ∈ T ↔ x ∈ (V ⊔ Subgroup.zpowers y : Subgroup G) ∧ x ^ 2 = 1 :=
      fun x => Iff.rfl
    have hVT : V ≤ T := fun v hv => ⟨Subgroup.mem_sup_left hv, hV.2 v hv⟩
    have hzpT : Subgroup.zpowers y ≤ T :=
      Subgroup.zpowers_le.mpr ⟨Subgroup.mem_sup_right (Subgroup.mem_zpowers y), hy2⟩
    have hDT : (V ⊔ Subgroup.zpowers y : Subgroup G) ≤ T := sup_le hVT hzpT
    intro x hx
    exact ((hmem x).mp (hDT hx)).2
  -- the 2-rank bound, and the divisibility `|V| ∣ |D|`, pin `|D|` down to `4 = |V|`
  have hcardD : Nat.card ↥(V ⊔ Subgroup.zpowers y : Subgroup G) ≤ 4 :=
    card_le_four_of_sq_eq_one hsyl (V ⊔ Subgroup.zpowers y) hD2
  have hVcard : Nat.card ↥V = 4 := hV.1
  have hVeq : V = (V ⊔ Subgroup.zpowers y : Subgroup G) :=
    Subgroup.eq_of_le_of_card_ge (le_sup_left : V ≤ (V ⊔ Subgroup.zpowers y : Subgroup G))
      (by rw [hVcard]; exact hcardD)
  have hyD : y ∈ (V ⊔ Subgroup.zpowers y : Subgroup G) :=
    Subgroup.mem_sup_right (Subgroup.mem_zpowers y)
  exact hVeq ▸ hyD

/-! ## The requested lemma -/

theorem ElementaryAbelianRankTwo (G : Type) [Group G] [Finite G]
    (hsyl : Work.GW2.DihOrCycSylow G) (V : Subgroup G) (hV : Work.GW2.IsFourGroup V)
    (y : G) (hy2 : y * y = 1) (hyV : y ∉ V)
    (hcomm : y ∈ Subgroup.centralizer (V : Set G)) : False := by
  have hy2' : y ^ 2 = 1 := by rw [pow_two]; exact hy2
  exact hyV (mem_of_isFourGroup_of_sq_eq_one hsyl V hV y hy2' hcomm)

end Work.CORE4
