/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gorenstein–Walter formalisation team (area BSW)

# Bender 1974 §3.2: the coset count

This is the counting argument of `Work.BSW.BSWS32Prop` (Bender §3.2).  With `F = C_G(x)`,
`M = N_G(F)`, `f = |F|`, `n = |K ⊓ M|`, `m = |G : M|`, `a = 2k/n`:

* every involution `u ∈ M` fixes exactly `a` cosets of `M` (`card_fixSet`), and distinct
  involutions of `M` share only the coset `M` (`fixSet_disjoint`);
* the non-identity special cosets number `f(a-1)` (`card_special`), giving `1 + f(a-1) ≤ m`
  (`claim1`);
* `F` acts freely on the non-special cosets, giving `f ∣ m - (1 + f(a-1))` (`claim2`);
* the involutions commuting with an element of `M` number `f(k+1)`, giving `f(k+1) ≤ I`
  (`claim3`) and, together with the injection of the remaining involutions into the
  non-special cosets, `I - f(k+1) ≤ m - (1 + f(a-1))` (`claim4`).
-/
import Mathlib
import Submission.Work.BSW.Cases.bswS32Setup
import Submission.Work.BSW.Cases.bswCompletionBase
import Submission.Work.BSW.S3.bswCompletionPropFromLeaves
import Submission.Work.BSW.Api.ncard_involutions_eq_index

namespace Work.BSW.Cases
open Subgroup Work.GW2
open Work.BSW.S3
open Work.BSW.Api

variable {G : Type} [Group G] [Finite G] {t s : G} {K : Subgroup G} {x : G}

variable {G : Type} [Group G] [Finite G] {t s : G} {K : Subgroup G} {x : G}

/-- The involutions of `M = N_G(F)`. -/
abbrev Tty (x : G) : Type := {u : G // orderOf u = 2 ∧ u ∈ NF x}

theorem card_Tty (h : BSWHyps2 G t s K) (hx : x ∉ HG t) (hinv : t⁻¹ * x * t = x⁻¹) :
    Nat.card (Tty x) = Nat.card ↥(CF x) := card_invM h hx hinv

/-- The value of the action on cosets. -/
theorem smul_mk (u g : G) : u • (g : G ⧸ NF x) = ((u * g : G) : G ⧸ NF x) := rfl

/-- `u` fixes the identity coset of `G ⧸ M` when `u ∈ M`. -/
theorem smul_one_eq_one (u : G) (hu : u ∈ NF x) :
    u • ((1 : G) : G ⧸ NF x) = ((1 : G) : G ⧸ NF x) := by
  have hstab1 : MulAction.stabilizer G ((1 : G) : G ⧸ NF x) = NF x :=
    MulAction.stabilizer_quotient (NF x)
  rw [← MulAction.mem_stabilizer_iff, hstab1]
  exact hu

/-- Membership in a conjugate of `M`. -/
theorem mem_conjSub_iff {g y : G} : y ∈ conjSub g (NF x) ↔ g⁻¹ * y * g ∈ NF x := by
  rw [conjSub, Subgroup.mem_map]
  constructor
  · rintro ⟨m, hm, hmy⟩
    have hmy' : g * m * g⁻¹ = y := by
      simpa only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] using hmy
    have he : g⁻¹ * (g * m * g⁻¹) * g = m := by group
    rw [← hmy', he]
    exact hm
  · intro h
    refine ⟨g⁻¹ * y * g, h, ?_⟩
    show g * (g⁻¹ * y * g) * g⁻¹ = y
    group

/-- The stabilizer of the coset of `g` is `gMg⁻¹`. -/
theorem stabilizer_coset (g : G) :
    MulAction.stabilizer G (g : G ⧸ NF x) = conjSub g (NF x) := by
  ext y
  rw [MulAction.mem_stabilizer_iff, smul_mk, QuotientGroup.eq, mem_conjSub_iff]
  constructor
  · intro h
    have h' : (g⁻¹ * y⁻¹ * g) ∈ NF x := by simpa only [mul_inv_rev] using h
    have h2 : (g⁻¹ * y⁻¹ * g)⁻¹ ∈ NF x := (NF x).inv_mem h'
    have he : (g⁻¹ * y⁻¹ * g)⁻¹ = g⁻¹ * y * g := by group
    rw [he] at h2
    exact h2
  · intro h
    have h2 : (g⁻¹ * y * g)⁻¹ ∈ NF x := (NF x).inv_mem h
    have he : (g⁻¹ * y * g)⁻¹ = g⁻¹ * y⁻¹ * g := by group
    rw [he] at h2
    simpa only [mul_inv_rev] using h2

/-- Two elements of `T` are `M`-conjugate. -/
theorem conj_T_transitive (h : BSWHyps2 G t s K) (hx : x ∉ HG t)
    (hinv : t⁻¹ * x * t = x⁻¹) {u w : G} (hu2 : orderOf u = 2) (huM : u ∈ NF x)
    (hw2 : orderOf w = 2) (hwM : w ∈ NF x) : ∃ m ∈ NF x, u = m⁻¹ * w * m := by
  obtain ⟨c₁, hc₁, hu⟩ := conj_involution_transitive (x := x) h hx hinv hu2 huM
  obtain ⟨c₂, hc₂, hw⟩ := conj_involution_transitive (x := x) h hx hinv hw2 hwM
  refine ⟨c₂ * c₁⁻¹, (NF x).mul_mem ((CF x).le_normalizer hc₂)
    ((NF x).inv_mem ((CF x).le_normalizer hc₁)), ?_⟩
  calc u = c₁ * t * c₁⁻¹ := hu
    _ = (c₂ * c₁⁻¹)⁻¹ * (c₂ * t * c₂⁻¹) * (c₂ * c₁⁻¹) := by group
    _ = (c₂ * c₁⁻¹)⁻¹ * w * (c₂ * c₁⁻¹) := by rw [hw]


/-- The product of two involutions of `M` lies in `F`. -/
theorem mul_mem_CF_of_mem_T (h : BSWHyps2 G t s K) (hx : x ∉ HG t) (hinv : t⁻¹ * x * t = x⁻¹)
    {u v : G} (hu2 : orderOf u = 2) (huM : u ∈ NF x) (hv2 : orderOf v = 2) (hvM : v ∈ NF x) :
    u * v ∈ CF x := by
  obtain ⟨c, hc, hu⟩ := (mem_NF_involution_iff (x := x) h hx hinv u).mp ⟨hu2, huM⟩
  obtain ⟨d, hd, hv⟩ := (mem_NF_involution_iff (x := x) h hx hinv v).mp ⟨hv2, hvM⟩
  rw [hu, hv]
  have h1 : (t * c) * (t * d) = c⁻¹ * d := by
    rw [show (t * c) * (t * d) = (t * c * t) * d by group,
      inverts_centralizer h hx hinv c hc]
  rw [h1]
  exact (CF x).mul_mem ((CF x).inv_mem hc) hd

/-- The cosets fixed by two distinct involutions of `M` meet only in the coset `M`. -/
theorem fixSet_disjoint (h : BSWHyps2 G t s K) (hx : x ∉ HG t) (hinv : t⁻¹ * x * t = x⁻¹)
    (hHall : ∀ g : G, g ∉ NF x → CF x ⊓ conjSub g (NF x) = ⊥)
    {u v : G} (hu2 : orderOf u = 2) (huM : u ∈ NF x) (hv2 : orderOf v = 2) (hvM : v ∈ NF x)
    (huv : u ≠ v) :
    ∀ q : G ⧸ NF x, u • q = q → v • q = q → q = ((1 : G) : G ⧸ NF x) := by
  intro q huq hvq
  by_contra hq
  obtain ⟨g, rfl⟩ : ∃ g : G, q = (g : G ⧸ NF x) :=
    ⟨Quotient.out q, (QuotientGroup.out_eq' q).symm⟩
  have hgM : g ∉ NF x := by
    intro hg
    exact hq (by
      rw [QuotientGroup.eq]
      simpa using (NF x).inv_mem hg)
  have hu_stab : u ∈ MulAction.stabilizer G (g : G ⧸ NF x) :=
    MulAction.mem_stabilizer_iff.mpr huq
  have hv_stab : v ∈ MulAction.stabilizer G (g : G ⧸ NF x) :=
    MulAction.mem_stabilizer_iff.mpr hvq
  rw [stabilizer_coset (x := x) g] at hu_stab hv_stab
  have huv_bot : u * v ∈ CF x ⊓ conjSub g (NF x) :=
    ⟨mul_mem_CF_of_mem_T (x := x) h hx hinv hu2 huM hv2 hvM,
      (conjSub g (NF x)).mul_mem hu_stab hv_stab⟩
  rw [hHall g hgM] at huv_bot
  have : u * v = 1 := Subgroup.mem_bot.mp huv_bot
  have huv' : u = v⁻¹ := mul_eq_one_iff_eq_inv.mp this
  have hvv : v⁻¹ = v :=
    inv_eq_of_mul_eq_one_left (Work.BSW.mul_self_eq_one_of_orderOf_eq_two hv2)
  rw [hvv] at huv'
  exact huv huv'

/-- `n = |K ⊓ M| > 0`. -/
theorem pos_card_inf (h : BSWHyps2 G t s K) (hx : x ∉ HG t) (hinv : t⁻¹ * x * t = x⁻¹) :
    0 < Nat.card ↥(K ⊓ NF x) := by
  haveI : Nonempty ↥(K ⊓ NF x) := ⟨⟨t, Work.BSW.t_mem_K h, t_mem_NF h hx hinv⟩⟩
  exact Nat.card_pos


/-- **The fixed cosets of an involution of `M` number `2k/n`.** -/
theorem card_fixSet (h : BSWHyps2 G t s K) (hx : x ∉ HG t) (hinv : t⁻¹ * x * t = x⁻¹)
    {u : G} (hu2 : orderOf u = 2) (huM : u ∈ NF x)
    (hcardC : Nat.card ↥(Subgroup.centralizer ({u} : Set G)) = 2 * Nat.card K) :
    Nat.card {q : G ⧸ NF x // u • q = q} = 2 * Nat.card K / Nat.card ↥(K ⊓ NF x) := by
  let C : Subgroup G := Subgroup.centralizer ({u} : Set G)
  let b : G ⧸ NF x := ((1 : G) : G ⧸ NF x)
  have hb_eq : b = ((1 : G) : G ⧸ NF x) := rfl
  -- the orbit of the identity coset under `C_G(u)` is exactly the set of fixed cosets
  have horb : MulAction.orbit ↥C b = {q : G ⧸ NF x | u • q = q} := by
    ext q
    constructor
    · rintro ⟨c, rfl⟩
      have hcu : (c : G) * u = u * (c : G) :=
        Subgroup.mem_centralizer_singleton_iff.mp c.2
      have hub : u • b = b := smul_one_eq_one (x := x) u huM
      have hcu' : (c : G) * u = u * (c : G) := hcu
      calc u • (c • b) = u • ((c : G) • b) := by rw [Submonoid.smul_def]
        _ = (u * (c : G)) • b := by rw [mul_smul]
        _ = ((c : G) * u) • b := by rw [hcu']
        _ = (c : G) • (u • b) := by rw [mul_smul]
        _ = (c : G) • b := by rw [hub]
        _ = c • b := by rw [Submonoid.smul_def]
    · intro hq
      obtain ⟨g, hgq⟩ : ∃ g : G, (g : G ⧸ NF x) = q :=
        ⟨Quotient.out q, QuotientGroup.out_eq' q⟩
      rw [← hgq] at hq ⊢
      have hu_stab : u ∈ MulAction.stabilizer G (g : G ⧸ NF x) :=
        MulAction.mem_stabilizer_iff.mpr hq
      rw [stabilizer_coset (x := x) g, mem_conjSub_iff] at hu_stab
      have hw2 : orderOf (g⁻¹ * u * g) = 2 := by
        have he : g⁻¹ * u * g = (MulAut.conj g⁻¹) u := by
          rw [MulAut.conj_apply]; group
        rw [he, MulEquiv.orderOf_eq, hu2]
      obtain ⟨m, hm, hmu⟩ := conj_T_transitive (x := x) h hx hinv hu2 huM hw2 hu_stab
      refine ⟨⟨g * m, ?_⟩, ?_⟩
      · rw [Subgroup.mem_centralizer_singleton_iff]
        have key : m * u = (g⁻¹ * u * g) * m := by
          conv_lhs => rw [hmu]
          group
        calc (g * m) * u = g * (m * u) := by group
          _ = g * ((g⁻¹ * u * g) * m) := by rw [key]
          _ = u * (g * m) := by group
      · show (g * m : G) • b = (g : G ⧸ NF x)
        rw [hb_eq, smul_mk, mul_one, QuotientGroup.eq]
        have he : (g * m)⁻¹ * g = m⁻¹ := by group
        rw [he]
        exact (NF x).inv_mem hm
  -- orbit-stabilizer
  have hOS : Nat.card (MulAction.orbit ↥C b) * Nat.card ↥(MulAction.stabilizer ↥C b)
      = Nat.card ↥C := by
    rw [← Nat.card_prod]
    exact Nat.card_congr (MulAction.orbitProdStabilizerEquivGroup (↥C) b)
  have hmem : ∀ y : ↥C, y ∈ MulAction.stabilizer ↥C b ↔ (y : G) ∈ NF x := by
    intro y
    rw [MulAction.mem_stabilizer_iff, Submonoid.smul_def, hb_eq, smul_mk, mul_one,
      QuotientGroup.eq]
    constructor
    · intro h; simpa using (NF x).inv_mem h
    · intro h; simpa using (NF x).inv_mem h
  have hstab : MulAction.stabilizer ↥C b = (NF x).subgroupOf C := by
    ext y
    rw [hmem y, Subgroup.mem_subgroupOf]
  have hstabcard : Nat.card ↥(MulAction.stabilizer ↥C b) = Nat.card ↥(K ⊓ NF x) := by
    rw [hstab]
    trans Nat.card ↥(NF x ⊓ C)
    · exact Nat.card_congr {
        toFun := fun x => ⟨(x.1 : G), x.2, x.1.2⟩
        invFun := fun y => ⟨⟨(y : G), y.2.2⟩, y.2.1⟩
        left_inv := fun x => by ext; rfl
        right_inv := fun y => by ext; rfl }
    · exact card_CM (x := x) h hx hinv huM hu2
  have hprod : Nat.card (MulAction.orbit ↥C b) * Nat.card ↥(K ⊓ NF x) = 2 * Nat.card K := by
    rw [← hcardC, ← hOS, ← hstabcard]
  have horbcard : Nat.card (MulAction.orbit ↥C b) =
      2 * Nat.card K / Nat.card ↥(K ⊓ NF x) := by
    rw [← hprod, mul_comm]
    exact (Nat.mul_div_right _ (pos_card_inf h hx hinv)).symm
  have hiff : ∀ q : G ⧸ NF x, (u • q = q) ↔ (q ∈ MulAction.orbit ↥C b) := by
    intro q
    rw [horb, Set.mem_setOf_eq]
  have horb2 : Nat.card {q : G ⧸ NF x // u • q = q} = Nat.card (MulAction.orbit ↥C b) :=
    Nat.card_congr (Equiv.subtypeEquivRight hiff)
  rw [horb2]
  exact horbcard


/-- Splitting a subtype at an element. -/
theorem card_subtype_ne_add_one {α : Type} [Finite α] (p : α → Prop) (a : α) (ha : p a) :
    Nat.card {x : α // p x ∧ x ≠ a} + 1 = Nat.card {x : α // p x} := by
  classical
  haveI : Fintype α := Fintype.ofFinite α
  have e : {x : α // p x} ≃ Option {x : α // p x ∧ x ≠ a} := {
    toFun := fun x => if h : (x : α) = a then none else some ⟨x.1, x.2, h⟩
    invFun := fun o => o.elim ⟨a, ha⟩ (fun y => ⟨y.1, y.2.1⟩)
    left_inv := by
      intro x
      dsimp only
      split_ifs with h
      · exact Subtype.ext h.symm
      · rfl
    right_inv := by
      intro o
      cases o with
      | none => simp
      | some y => simp [y.2.2] }
  haveI : Fintype {x : α // p x ∧ x ≠ a} := Fintype.ofFinite _
  have h1 : Nat.card (Option {x : α // p x ∧ x ≠ a}) =
      Nat.card {x : α // p x ∧ x ≠ a} + 1 := by
    rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
    exact Fintype.card_option
  rw [Nat.card_congr e, h1]

/-- A coset of `M` is *special* if it is fixed by an involution of `M`. -/
abbrev Special (x : G) (q : G ⧸ NF x) : Prop :=
  ∃ u : G, orderOf u = 2 ∧ u ∈ NF x ∧ u • q = q

/-- **Bender §3.2(ii)**: the non-identity special cosets number `f(a - 1)`, `a = 2k/n`. -/
theorem card_special (h : BSWHyps2 G t s K) (hx : x ∉ HG t) (hinv : t⁻¹ * x * t = x⁻¹)
    (hHall : ∀ g : G, g ∉ NF x → CF x ⊓ conjSub g (NF x) = ⊥)
    (hcardC : ∀ u : G, orderOf u = 2 → u ∈ NF x →
      Nat.card ↥(Subgroup.centralizer ({u} : Set G)) = 2 * Nat.card K) :
    {q : G ⧸ NF x | q ≠ ((1 : G) : G ⧸ NF x) ∧ Special x q}.ncard =
      Nat.card ↥(CF x) * (2 * Nat.card K / Nat.card ↥(K ⊓ NF x) - 1) := by
  classical
  haveI : Fintype (Tty x) := Fintype.ofFinite _
  set one : G ⧸ NF x := ((1 : G) : G ⧸ NF x) with hone
  have hne_one : ∀ u : G, u ∈ NF x → u • one = one := fun u hu => smul_one_eq_one (x := x) u hu
  have hterm : ∀ u : Tty x, ({q : G ⧸ NF x | u.1 • q = q} \ {one}).ncard =
      2 * Nat.card K / Nat.card ↥(K ⊓ NF x) - 1 := by
    intro u
    have hmem : one ∈ {q : G ⧸ NF x | u.1 • q = q} := hne_one u.1 u.2.2
    have hsingle : ({one} : Set (G ⧸ NF x)).ncard = 1 := Set.ncard_singleton one
    have hfix : ({q : G ⧸ NF x | u.1 • q = q}).ncard =
        2 * Nat.card K / Nat.card ↥(K ⊓ NF x) := by
      rw [← Nat.card_coe_set_eq]
      exact card_fixSet (x := x) h hx hinv u.2.1 u.2.2 (hcardC u.1 u.2.1 u.2.2)
    rw [Set.ncard_sdiff (by rintro x hx; rw [Set.mem_singleton_iff] at hx; rw [hx]; exact hmem),
      hsingle, hfix]
  have hUnion : {q : G ⧸ NF x | q ≠ one ∧ Special x q} =
      ⋃ u : Tty x, ({q : G ⧸ NF x | u.1 • q = q} \ {one}) := by
    ext q
    rw [Set.mem_setOf_eq, Set.mem_iUnion]
    constructor
    · rintro ⟨hne, u, hu2, huM, huq⟩
      exact ⟨⟨u, hu2, huM⟩, huq, hne⟩
    · rintro ⟨u, huq, hne⟩
      exact ⟨hne, u.1, u.2.1, u.2.2, huq⟩
  rw [hUnion, Set.ncard_iUnion_of_finite (fun u => Set.toFinite _)]
  · rw [finsum_eq_sum_of_fintype,
      Finset.sum_congr rfl (fun u _ => hterm u), Finset.sum_const, Finset.card_univ,
      smul_eq_mul, ← Nat.card_eq_fintype_card, card_Tty (x := x) h hx hinv]
  · intro u v huv
    rw [Function.onFun, Set.disjoint_left]
    rintro q ⟨hqu, hqne⟩ ⟨hqv, _⟩
    exact hqne (fixSet_disjoint (x := x) h hx hinv hHall u.2.1 u.2.2 v.2.1 v.2.2
      (fun h => huv (Subtype.ext h)) q hqu hqv)


/-- `a * (a * b) * a = b * a` for an involution `a`. -/
theorem self_mul_mul_self {a b : G} (ha : a * a = 1) : a * (a * b) * a = b * a := by
  calc a * (a * b) * a = (a * a) * (b * a) := by simp only [mul_assoc]
    _ = b * a := by rw [ha, one_mul]

/-- `Special` is invariant under the `F`-action. -/
theorem special_smul_iff (h : BSWHyps2 G t s K) (hx : x ∉ HG t) (hinv : t⁻¹ * x * t = x⁻¹)
    {f : G} (hf : f ∈ CF x) (q : G ⧸ NF x) : Special x (f • q) ↔ Special x q := by
  have hfM : f ∈ NF x := (CF x).le_normalizer hf
  have hfinvM : f⁻¹ ∈ NF x := (NF x).inv_mem hfM
  constructor
  · rintro ⟨u, hu2, huM, huq⟩
    have h2 : f⁻¹ • (u • (f • q)) = f⁻¹ • (f • q) := by rw [huq]
    have e1 : f⁻¹ • (u • (f • q)) = (f⁻¹ * u * f) • q := by
      rw [smul_smul, smul_smul]
    have e2 : f⁻¹ • (f • q) = q := by
      obtain ⟨g, rfl⟩ : ∃ g : G, q = (g : G ⧸ NF x) :=
        ⟨Quotient.out q, (QuotientGroup.out_eq' q).symm⟩
      rw [smul_mk, smul_mk, ← mul_assoc, inv_mul_cancel, one_mul]
    have h3 : (f⁻¹ * u * f) • q = q := by rw [e1, e2] at h2; exact h2
    refine ⟨f⁻¹ * u * f, ?_, ?_, h3⟩
    · have hconj : f⁻¹ * u * f = (MulAut.conj f⁻¹) u := by rw [MulAut.conj_apply]; group
      rw [hconj, MulEquiv.orderOf_eq, hu2]
    · exact mul_mem (mul_mem hfinvM huM) hfM
  · rintro ⟨u, hu2, huM, huq⟩
    have h2 : f • (u • q) = f • q := by rw [huq]
    have e1 : f • (u • q) = (f * u * f⁻¹) • (f • q) := by
      obtain ⟨g, rfl⟩ : ∃ g : G, q = (g : G ⧸ NF x) :=
        ⟨Quotient.out q, (QuotientGroup.out_eq' q).symm⟩
      rw [smul_mk]
      exact congrArg QuotientGroup.mk
        (by group : f * (u * g) = (f * u * f⁻¹) * (f * g))
    have h3 : (f * u * f⁻¹) • (f • q) = f • q := by rw [e1] at h2; exact h2
    refine ⟨f * u * f⁻¹, ?_, ?_, h3⟩
    · have hconj : f * u * f⁻¹ = (MulAut.conj f) u := MulAut.conj_apply f u
      rw [hconj, MulEquiv.orderOf_eq, hu2]
    · exact mul_mem (mul_mem hfM huM) hfinvM

/-- The `F`-action on the non-special cosets of `M`. -/
def nonspecialMulAction (h : BSWHyps2 G t s K) (hx : x ∉ HG t) (hinv : t⁻¹ * x * t = x⁻¹) :
    MulAction ↥(CF x) {q : G ⧸ NF x // ¬ Special x q} where
  smul f q := ⟨(f : G) • q.1,
    fun hspec => q.2 ((special_smul_iff h hx hinv f.2 q.1).mp hspec)⟩
  one_smul q := Subtype.ext (one_smul (↥(CF x)) q.1)
  mul_smul f g q := Subtype.ext (mul_smul f g q.1)

/-- `Nat.card` of a subtype is the `Set.ncard` of the corresponding set. -/
theorem natCard_subtype_eq_ncard {α : Type} (p : α → Prop) :
    Nat.card {x : α // p x} = {x : α | p x}.ncard := by
  rw [← Nat.card_coe_set_eq]
  rfl

/-- Removing one point from a finite set. -/
theorem card_sdiff_singleton_add_one {α : Type} [Finite α] (s : Set α) (a : α) (ha : a ∈ s) :
    Nat.card ↥(s \ {a}) + 1 = Nat.card ↥s := by
  have h := card_subtype_ne_add_one (p := fun x => x ∈ s) a ha
  have e : {x : α // x ∈ s ∧ x ≠ a} ≃ ↥(s \ {a}) := {
    toFun := fun x => ⟨x.1, by
      rw [Set.mem_diff, Set.mem_singleton_iff]
      exact ⟨x.2.1, x.2.2⟩⟩
    invFun := fun y => ⟨y.1, by
      have hy := y.2
      rw [Set.mem_diff, Set.mem_singleton_iff] at hy
      exact hy⟩
    left_inv := fun x => rfl
    right_inv := fun y => rfl }
  rw [← Nat.card_congr e, h]

/-- Removing one point from a finite set (`Set.ncard` form). -/
theorem ncard_sdiff_singleton_add_one {α : Type} [Finite α] (s : Set α) (a : α) (ha : a ∈ s) :
    (s \ {a}).ncard + 1 = s.ncard := by
  rw [← Nat.card_coe_set_eq, ← Nat.card_coe_set_eq]
  exact card_sdiff_singleton_add_one s a ha

/-- **Claim 1** of `BSWS32Prop`: `1 + f(a-1) ≤ m`. -/
theorem claim1 (h : BSWHyps2 G t s K) (hx : x ∉ HG t) (hinv : t⁻¹ * x * t = x⁻¹)
    (hHall : ∀ g : G, g ∉ NF x → CF x ⊓ conjSub g (NF x) = ⊥)
    (hcardC : ∀ u : G, orderOf u = 2 → u ∈ NF x →
      Nat.card ↥(Subgroup.centralizer ({u} : Set G)) = 2 * Nat.card K) :
    1 + Nat.card ↥(CF x) * (2 * Nat.card K / Nat.card ↥(K ⊓ NF x) - 1) ≤ (NF x).index := by
  have hcard := card_special (x := x) h hx hinv hHall hcardC
  have hle : ({q : G ⧸ NF x | q ≠ ((1 : G) : G ⧸ NF x) ∧ Special x q}).ncard ≤
      ({q : G ⧸ NF x | q ≠ ((1 : G) : G ⧸ NF x)}).ncard :=
    Set.ncard_le_ncard (fun q hq => hq.1)
  have hsplit : ({q : G ⧸ NF x | q ≠ ((1 : G) : G ⧸ NF x)}).ncard + 1 = (NF x).index := by
    have h1 : ({q : G ⧸ NF x | q ≠ ((1 : G) : G ⧸ NF x)}) =
        ((Set.univ : Set (G ⧸ NF x)) \ {((1 : G) : G ⧸ NF x)}) := by
      ext q; simp [Set.mem_diff, Set.mem_singleton_iff]
    rw [h1, ncard_sdiff_singleton_add_one (Set.univ) _ trivial, Set.ncard_univ]
    rfl
  omega


/-- **Claim 2** of `BSWS32Prop`: `f ∣ m - (1 + f(a-1))`. -/
theorem claim2 (h : BSWHyps2 G t s K) (hx : x ∉ HG t) (hinv : t⁻¹ * x * t = x⁻¹)
    (hHall : ∀ g : G, g ∉ NF x → CF x ⊓ conjSub g (NF x) = ⊥)
    (hcardC : ∀ u : G, orderOf u = 2 → u ∈ NF x →
      Nat.card ↥(Subgroup.centralizer ({u} : Set G)) = 2 * Nat.card K) :
    Nat.card ↥(CF x) ∣ (NF x).index -
      (1 + Nat.card ↥(CF x) * (2 * Nat.card K / Nat.card ↥(K ⊓ NF x) - 1)) := by
  classical
  letI := nonspecialMulAction (x := x) h hx hinv
  have hone : Special x (((1 : G) : G ⧸ NF x)) :=
    ⟨t, Work.BSW.orderOf_t h, t_mem_NF h hx hinv, smul_one_eq_one t (t_mem_NF h hx hinv)⟩
  have hfree : ∀ f : ↥(CF x), ∀ q : {q : G ⧸ NF x // ¬ Special x q}, f • q = q → f = 1 := by
    intro f q hfq
    have hq : (f : G) • q.1 = q.1 := congrArg Subtype.val hfq
    have hne : q.1 ≠ ((1 : G) : G ⧸ NF x) := by
      intro h1
      exact q.2 (h1 ▸ hone)
    obtain ⟨g, hg⟩ : ∃ g : G, q.1 = (g : G ⧸ NF x) :=
      ⟨Quotient.out q.1, (QuotientGroup.out_eq' q.1).symm⟩
    have hgM : g ∉ NF x := by
      intro hgM
      exact hne (by rw [hg, QuotientGroup.eq]; simpa using (NF x).inv_mem hgM)
    have hstab : (f : G) ∈ conjSub g (NF x) := by
      rw [← stabilizer_coset (x := x) g, MulAction.mem_stabilizer_iff, ← hg]
      exact hq
    have hbot : (f : G) ∈ CF x ⊓ conjSub g (NF x) := ⟨f.2, hstab⟩
    rw [hHall g hgM] at hbot
    exact Subtype.ext (Subgroup.mem_bot.mp hbot)
  have hdvd := dvd_card_of_fixedPointFree (A := ↥(CF x))
    (α := {q : G ⧸ NF x // ¬ Special x q}) hfree
  -- the count of non-special cosets
  have hdiff : Nat.card ↥({q : G ⧸ NF x | Special x q} \ {((1 : G) : G ⧸ NF x)}) =
      Nat.card ↥{q : G ⧸ NF x | q ≠ ((1 : G) : G ⧸ NF x) ∧ Special x q} := by
    refine Nat.card_congr (Equiv.subtypeEquivRight (fun q => ?_))
    simp only [Set.mem_sdiff, Set.mem_singleton_iff]
    exact and_comm
  have hcardsp : Nat.card {q : G ⧸ NF x // q ≠ ((1 : G) : G ⧸ NF x) ∧ Special x q} =
      Nat.card ↥(CF x) * (2 * Nat.card K / Nat.card ↥(K ⊓ NF x) - 1) :=
    (natCard_subtype_eq_ncard _).trans (card_special (x := x) h hx hinv hHall hcardC)
  have hsplitT : Nat.card {q : G ⧸ NF x // Special x q} =
      1 + Nat.card ↥(CF x) * (2 * Nat.card K / Nat.card ↥(K ⊓ NF x) - 1) := by
    have h := card_subtype_ne_add_one (p := fun q : G ⧸ NF x => Special x q)
      (((1 : G) : G ⧸ NF x)) hone
    have h2 : Nat.card {q : G ⧸ NF x // Special x q ∧ q ≠ ((1 : G) : G ⧸ NF x)} =
        Nat.card ↥(CF x) * (2 * Nat.card K / Nat.card ↥(K ⊓ NF x) - 1) := by
      rw [Nat.card_congr (Equiv.subtypeEquivRight (fun q => and_comm)), hcardsp]
    omega
  have hsum : Nat.card (G ⧸ NF x) = Nat.card {q : G ⧸ NF x // Special x q} +
      Nat.card {q : G ⧸ NF x // ¬ Special x q} := by
    rw [← Nat.card_congr (Equiv.sumCompl (fun q : G ⧸ NF x => Special x q)), Nat.card_sum]
  have hcount : Nat.card {q : G ⧸ NF x // ¬ Special x q} = (NF x).index -
      (1 + Nat.card ↥(CF x) * (2 * Nat.card K / Nat.card ↥(K ⊓ NF x) - 1)) := by
    have hidx : (NF x).index = Nat.card (G ⧸ NF x) := rfl
    omega
  rw [← hcount]
  exact hdvd

/-- **Claim 3** of `BSWS32Prop`: `f(k+1) ≤ I`. -/
theorem claim3 (h : BSWHyps2 G t s K) (hx : x ∉ HG t) (hinv : t⁻¹ * x * t = x⁻¹)
    (hU : Nat.card {y : G // orderOf y = 2 ∧ ∃ u : G, orderOf u = 2 ∧ u ∈ NF x ∧
        y * u = u * y} = Nat.card ↥(CF x) * (Nat.card K + 1)) :
    Nat.card ↥(CF x) * (Nat.card K + 1) ≤ (Subgroup.centralizer ({t} : Set G)).index := by
  rw [← hU, ← ncard_involutions_eq_index h, ← Nat.card_coe_set_eq]
  refine Nat.card_le_card_of_injective (fun y : {y : G // orderOf y = 2 ∧ ∃ u : G,
      orderOf u = 2 ∧ u ∈ NF x ∧ y * u = u * y} => (⟨y.1, y.2.1⟩ : {y : G // orderOf y = 2})) ?_
  intro a b hab
  exact Subtype.ext (congrArg (fun z : {y : G // orderOf y = 2} => (z : G)) hab)

/-- Uniqueness of the element of `T` in a conjugate of `M`. -/
theorem mem_T_conjSub_unique (h : BSWHyps2 G t s K) (hx : x ∉ HG t)
    (hinv : t⁻¹ * x * t = x⁻¹)
    (hHall : ∀ g : G, g ∉ NF x → CF x ⊓ conjSub g (NF x) = ⊥) {g : G} (hgM : g ∉ NF x)
    {u v : G} (hu2 : orderOf u = 2) (huM : u ∈ NF x) (hu : u ∈ conjSub g (NF x))
    (hv2 : orderOf v = 2) (hvM : v ∈ NF x) (hv : v ∈ conjSub g (NF x)) : u = v := by
  have huv : u * v ∈ CF x := mul_mem_CF_of_mem_T (x := x) h hx hinv hu2 huM hv2 hvM
  have huv2 : u * v ∈ conjSub g (NF x) := (conjSub g (NF x)).mul_mem hu hv
  have hbot : u * v ∈ CF x ⊓ conjSub g (NF x) := ⟨huv, huv2⟩
  rw [hHall g hgM] at hbot
  have h1 : u * v = 1 := Subgroup.mem_bot.mp hbot
  have h2 : u = v⁻¹ := mul_eq_one_iff_eq_inv.mp h1
  have h3 : v⁻¹ = v :=
    inv_eq_of_mul_eq_one_left (Work.BSW.mul_self_eq_one_of_orderOf_eq_two hv2)
  rwa [h3] at h2

/-- **Claim 4** of `BSWS32Prop`: `I - f(k+1) ≤ m - (1 + f(a-1))`. -/
theorem claim4 (h : BSWHyps2 G t s K) (hx : x ∉ HG t) (hinv : t⁻¹ * x * t = x⁻¹)
    (hHall : ∀ g : G, g ∉ NF x → CF x ⊓ conjSub g (NF x) = ⊥)
    (hcardC : ∀ u : G, orderOf u = 2 → u ∈ NF x →
      Nat.card ↥(Subgroup.centralizer ({u} : Set G)) = 2 * Nat.card K)
    (hU : Nat.card {y : G // orderOf y = 2 ∧ ∃ u : G, orderOf u = 2 ∧ u ∈ NF x ∧
        y * u = u * y} = Nat.card ↥(CF x) * (Nat.card K + 1))
    (hInvertM : ∀ m : G, m ∈ NF x → m ≠ 1 → ∀ y : G, orderOf y = 2 →
      y⁻¹ * m * y = m⁻¹ → ∃ u : G, u ∈ NF x ∧ orderOf u = 2 ∧ y * u = u * y) :
    (Subgroup.centralizer ({t} : Set G)).index - Nat.card ↥(CF x) * (Nat.card K + 1) ≤
      (NF x).index -
        (1 + Nat.card ↥(CF x) * (2 * Nat.card K / Nat.card ↥(K ⊓ NF x) - 1)) := by
  classical
  have hone : Special x (((1 : G) : G ⧸ NF x)) :=
    ⟨t, Work.BSW.orderOf_t h, t_mem_NF h hx hinv, smul_one_eq_one t (t_mem_NF h hx hinv)⟩
  -- the non-special cosets
  have hNS : Nat.card {q : G ⧸ NF x // ¬ Special x q} = (NF x).index -
      (1 + Nat.card ↥(CF x) * (2 * Nat.card K / Nat.card ↥(K ⊓ NF x) - 1)) := by
    have hcardsp : Nat.card {q : G ⧸ NF x // q ≠ ((1 : G) : G ⧸ NF x) ∧ Special x q} =
        Nat.card ↥(CF x) * (2 * Nat.card K / Nat.card ↥(K ⊓ NF x) - 1) :=
      (natCard_subtype_eq_ncard _).trans (card_special (x := x) h hx hinv hHall hcardC)
    have hsplitT : Nat.card {q : G ⧸ NF x // Special x q} =
        1 + Nat.card ↥(CF x) * (2 * Nat.card K / Nat.card ↥(K ⊓ NF x) - 1) := by
      have h1 := card_subtype_ne_add_one (p := fun q : G ⧸ NF x => Special x q)
        (((1 : G) : G ⧸ NF x)) hone
      have h2 : Nat.card {q : G ⧸ NF x // Special x q ∧ q ≠ ((1 : G) : G ⧸ NF x)} =
          Nat.card ↥(CF x) * (2 * Nat.card K / Nat.card ↥(K ⊓ NF x) - 1) :=
        (Nat.card_congr (Equiv.subtypeEquivRight (fun q => and_comm))).trans hcardsp
      omega
    have hsum : Nat.card (G ⧸ NF x) = Nat.card {q : G ⧸ NF x // Special x q} +
        Nat.card {q : G ⧸ NF x // ¬ Special x q} := by
      rw [← Nat.card_congr (Equiv.sumCompl (fun q : G ⧸ NF x => Special x q)), Nat.card_sum]
    have hidx : (NF x).index = Nat.card (G ⧸ NF x) := rfl
    omega
  -- the involutions not commuting with any involution of `M`
  have hVcard : Nat.card {y : G // orderOf y = 2 ∧ ¬∃ u : G, orderOf u = 2 ∧ u ∈ NF x ∧
      y * u = u * y} = (Subgroup.centralizer ({t} : Set G)).index -
        Nat.card ↥(CF x) * (Nat.card K + 1) := by
    have hUncard : {y : G | orderOf y = 2 ∧ ∃ u : G, orderOf u = 2 ∧ u ∈ NF x ∧
        y * u = u * y}.ncard = Nat.card ↥(CF x) * (Nat.card K + 1) :=
      (natCard_subtype_eq_ncard _).symm.trans hU
    have hunion : {y : G | orderOf y = 2} =
        {y : G | orderOf y = 2 ∧ ∃ u : G, orderOf u = 2 ∧ u ∈ NF x ∧ y * u = u * y} ∪
        {y : G | orderOf y = 2 ∧ ¬∃ u : G, orderOf u = 2 ∧ u ∈ NF x ∧ y * u = u * y} := by
      ext y
      constructor
      · intro hy
        by_cases hp : ∃ u : G, orderOf u = 2 ∧ u ∈ NF x ∧ y * u = u * y
        · exact Or.inl ⟨hy, hp⟩
        · exact Or.inr ⟨hy, hp⟩
      · rintro (hy | hy)
        · exact hy.1
        · exact hy.1
    have hdisj : Disjoint {y : G | orderOf y = 2 ∧ ∃ u : G, orderOf u = 2 ∧ u ∈ NF x ∧
          y * u = u * y}
        {y : G | orderOf y = 2 ∧ ¬∃ u : G, orderOf u = 2 ∧ u ∈ NF x ∧ y * u = u * y} := by
      rw [Set.disjoint_left]
      rintro y ⟨-, hy⟩ ⟨-, hy'⟩
      exact hy' hy
    have hmain : ({y : G | orderOf y = 2} : Set G).ncard =
        {y : G | orderOf y = 2 ∧ ∃ u : G, orderOf u = 2 ∧ u ∈ NF x ∧ y * u = u * y}.ncard +
        {y : G | orderOf y = 2 ∧ ¬∃ u : G, orderOf u = 2 ∧ u ∈ NF x ∧ y * u = u * y}.ncard := by
      rw [hunion, Set.ncard_union_eq hdisj (Set.toFinite _) (Set.toFinite _)]
    rw [ncard_involutions_eq_index h, hUncard] at hmain
    rw [natCard_subtype_eq_ncard]
    omega
  -- the injection of `V` into the non-special cosets
  have hinj : Function.Injective (fun y : {y : G // orderOf y = 2 ∧ ¬∃ u : G,
      orderOf u = 2 ∧ u ∈ NF x ∧ y * u = u * y} =>
      (⟨(y.1 : G ⧸ NF x), by
        rintro ⟨u, hu2, huM, huq⟩
        have hu_stab : u ∈ MulAction.stabilizer G (y.1 : G ⧸ NF x) :=
          MulAction.mem_stabilizer_iff.mpr huq
        rw [stabilizer_coset (x := x) y.1] at hu_stab
        have hy_ne : y.1 ∉ NF x := by
          intro hyM
          exact y.2.2 ⟨y.1, y.2.1, hyM, rfl⟩
        have hm2 : orderOf (y.1⁻¹ * u * y.1) = 2 := by
          have he : y.1⁻¹ * u * y.1 = (MulAut.conj y.1⁻¹) u := by
            rw [MulAut.conj_apply]; group
          rw [he, MulEquiv.orderOf_eq, hu2]
        have hmM : y.1⁻¹ * u * y.1 ∈ NF x := mem_conjSub_iff.mp hu_stab
        have hyy : y.1 * y.1 = 1 :=
          Work.BSW.mul_self_eq_one_of_orderOf_eq_two y.2.1
        have hyinv : y.1⁻¹ = y.1 := inv_eq_of_mul_eq_one_left hyy
        have hm_stab : y.1⁻¹ * u * y.1 ∈ conjSub y.1 (NF x) := by
          rw [mem_conjSub_iff]
          have he : y.1⁻¹ * (y.1⁻¹ * u * y.1) * y.1 = u := by
            rw [hyinv]
            have h1 : y.1 * (y.1 * u * y.1) = u * y.1 := by
              rw [← mul_assoc, ← mul_assoc, hyy, one_mul]
            have h2 : (u * y.1) * y.1 = u := by rw [mul_assoc, hyy, mul_one]
            calc y.1 * (y.1 * u * y.1) * y.1 = (u * y.1) * y.1 := by rw [h1]
              _ = u := h2
          rw [he]
          exact huM
        have heq := mem_T_conjSub_unique (x := x) h hx hinv hHall hy_ne hu2 huM hu_stab
          hm2 hmM hm_stab
        refine y.2.2 ⟨u, hu2, huM, ?_⟩
        have huyu : y.1 * u * y.1 = u := by
          rw [hyinv] at heq
          exact heq.symm
        calc y.1 * u = (y.1 * u * y.1) * y.1 := by
              conv_rhs => rw [mul_assoc, hyy, mul_one]
          _ = u * y.1 := by rw [huyu]⟩ :
        {q : G ⧸ NF x // ¬ Special x q})) := by
    intro y₁ y₂ heq
    have h1 : (y₁.1 : G ⧸ NF x) = (y₂.1 : G ⧸ NF x) := congrArg Subtype.val heq
    have hy1 : y₁.1⁻¹ = y₁.1 := inv_eq_of_mul_eq_one_left
      (Work.BSW.mul_self_eq_one_of_orderOf_eq_two y₁.2.1)
    have hy2 : y₂.1⁻¹ = y₂.1 := inv_eq_of_mul_eq_one_left
      (Work.BSW.mul_self_eq_one_of_orderOf_eq_two y₂.2.1)
    have hm : y₁.1 * y₂.1 ∈ NF x := by
      have h2 := h1
      rw [QuotientGroup.eq, hy1] at h2
      exact h2
    by_cases hm1 : y₁.1 * y₂.1 = 1
    · have h2' : y₁.1 = y₂.1⁻¹ := mul_eq_one_iff_eq_inv.mp hm1
      have h3' : y₁.1 = y₂.1 := by rw [h2', hy2]
      exact Subtype.ext h3'
    · have hcomm : y₁.1⁻¹ * (y₁.1 * y₂.1) * y₁.1 = (y₁.1 * y₂.1)⁻¹ := by
        rw [hy1, mul_inv_rev, hy2, hy1]
        exact self_mul_mul_self (Work.BSW.mul_self_eq_one_of_orderOf_eq_two y₁.2.1)
      obtain ⟨u, huM, hu2, hcu⟩ :=
        hInvertM (m := y₁.1 * y₂.1) hm hm1 (y := y₁.1) y₁.2.1 hcomm
      exact absurd ⟨u, hu2, huM, hcu⟩ y₁.2.2
  have hle := Nat.card_le_card_of_injective _ hinj
  rw [hVcard, hNS] at hle
  exact hle

end Work.BSW.Cases
