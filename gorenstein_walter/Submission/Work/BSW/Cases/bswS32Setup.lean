/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gorenstein–Walter formalisation team (area BSW, `Work.BSW`)

# Bender 1974 §3.2: the vocabulary of the coset count

For `x ∉ H^G` inverted by `t`, put `F = C_G(x)` and `M = N_G(F)`.  This file collects the
structural facts about `F` and `M` that the coset count of `Work.BSW.BSWS32Prop` rests on:

* the involutions of `M` are exactly the coset `tF`, and they form a single `M`-conjugacy class
  (`card_invM`, `mul_t_mem_CF`, `conj_involution_transitive`);
* two involutions `tc`, `td` of `M` commute if and only if `c = d` (`commute_involutions_iff`);
* `|M| = |F| · |K ⊓ M|` (`card_NF`), hence `M = F · (K ⊓ M)` as a set, and `|C_M(u)| = |K ⊓ M|`
  for every involution `u ∈ M` (`card_CM`).
-/
import Mathlib
import Submission.Work.BSW.S3.Defs
import Submission.Work.BSW.S3.S31setup
import Submission.Work.BSW.Cases.S31core
import Submission.Work.BSW.Api.card_sup_zpowers
import Submission.Work.BSW.Api.ncard_involutions_eq_index
import Submission.Work.BSW.Api.mem_centralizer_iff
import Submission.Work.BSW.Cases.bswCompletionBase

namespace Work.BSW.Cases

open Subgroup Work.GW2
open Work.BSW.S3

variable {G : Type} [Group G] [Finite G] {t s : G} {K : Subgroup G} {x : G}

/-- `F = C_G(x)`. -/
abbrev CF (x : G) : Subgroup G := Subgroup.centralizer ({x} : Set G)

/-- `M = N_G(F)`. -/
abbrev NF (x : G) : Subgroup G := Subgroup.normalizer (CF x : Set G)

/-- `t ∈ M`. -/
theorem t_mem_NF (h : BSWHyps2 G t s K) (hx : x ∉ HG t) (hinv : t⁻¹ * x * t = x⁻¹) :
    t ∈ NF x := t_mem_normalizer_centralizer h hx hinv

section Basic

/-- Elements of `F = C_G(x)` commute. -/
theorem CF_comm (h : BSWHyps2 G t s K) (hx : x ∉ HG t) (hinv : t⁻¹ * x * t = x⁻¹)
    {a b : G} (ha : a ∈ CF x) (hb : b ∈ CF x) : a * b = b * a := by
  haveI := isMulCommutative_centralizer h hx hinv
  exact congrArg Subtype.val ((IsMulCommutative.is_comm (M := ↥(CF x))).comm ⟨a, ha⟩ ⟨b, hb⟩)

/-- `F` has odd order, so it has no `2`-torsion. -/
theorem CF_eq_one_of_sq_eq_one (h : BSWHyps2 G t s K) (hx : x ∉ HG t)
    {a : G} (ha : a ∈ CF x) (hsq : a * a = 1) : a = 1 := by
  have hodd := odd_card_centralizer_of_notMem_HG h hx
  have hdvd2 : orderOf a ∣ 2 := by rw [orderOf_dvd_iff_pow_eq_one]; simpa [pow_two] using hsq
  have hdvdF : orderOf a ∣ Nat.card ↥(CF x) := by
    have := orderOf_dvd_natCard (⟨a, ha⟩ : ↥(CF x)); simpa using this
  rcases (Nat.dvd_prime Nat.prime_two).mp hdvd2 with h1 | h2
  · exact orderOf_eq_one_iff.mp h1
  · exfalso
    have h2' : 2 ∣ Nat.card ↥(CF x) := by rw [← h2]; exact hdvdF
    exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr h2')

/-- Squaring is injective on `F`. -/
theorem CF_sq_inj (h : BSWHyps2 G t s K) (hx : x ∉ HG t) (hinv : t⁻¹ * x * t = x⁻¹)
    {a b : G} (ha : a ∈ CF x) (hb : b ∈ CF x) (hab : a * a = b * b) : a = b := by
  have hcomm : a * b⁻¹ = b⁻¹ * a := CF_comm h hx hinv ha ((CF x).inv_mem hb)
  have hmem : a * b⁻¹ ∈ CF x := (CF x).mul_mem ha ((CF x).inv_mem hb)
  have hsq : (a * b⁻¹) * (a * b⁻¹) = 1 := by
    calc (a * b⁻¹) * (a * b⁻¹) = a * (b⁻¹ * a) * b⁻¹ := by group
      _ = a * (a * b⁻¹) * b⁻¹ := by rw [hcomm]
      _ = (a * a) * (b⁻¹ * b⁻¹) := by group
      _ = (b * b) * (b⁻¹ * b⁻¹) := by rw [hab]
      _ = 1 := by group
  have := CF_eq_one_of_sq_eq_one h hx hmem hsq
  exact mul_inv_eq_one.mp this

/-- Squaring is surjective on `F` (a finite group of odd order). -/
theorem CF_exists_sq (h : BSWHyps2 G t s K) (hx : x ∉ HG t) (hinv : t⁻¹ * x * t = x⁻¹)
    {d : G} (hd : d ∈ CF x) : ∃ c ∈ CF x, c * c = d := by
  have hinj : Function.Injective (fun a : ↥(CF x) => a * a) := by
    intro a b hab
    exact Subtype.ext (CF_sq_inj h hx hinv a.2 b.2 (congrArg Subtype.val hab))
  obtain ⟨c, hc⟩ := Finite.surjective_of_injective hinj (⟨d, hd⟩ : ↥(CF x))
  exact ⟨c, c.2, congrArg Subtype.val hc⟩

/-- The product of an involution of `M` with `t` lies in `F`. -/
theorem mul_t_mem_CF (h : BSWHyps2 G t s K) (hx : x ∉ HG t) (hinv : t⁻¹ * x * t = x⁻¹)
    {u : G} (huM : u ∈ NF x) (hu2 : orderOf u = 2) : u * t ∈ CF x := by
  have key : u * t ∈ Subgroup.centralizer
      ((Subgroup.centralizer ({x} : Set G) : Subgroup G) : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro c hc
    have huc : u * c * u⁻¹ = c⁻¹ :=
      (involution_mem_normalizer_inverts h hx hinv huM hu2).1 c hc
    have htc : t * c * t⁻¹ = c⁻¹ := by
      rw [Work.BSW.t_inv h]
      exact inverts_centralizer h hx hinv c hc
    have key2 : (u * t) * c * (u * t)⁻¹ = c := by
      rw [mul_inv_rev]
      calc u * t * c * (t⁻¹ * u⁻¹) = u * (t * c * t⁻¹) * u⁻¹ := by group
        _ = u * c⁻¹ * u⁻¹ := by rw [htc]
        _ = (u * c * u⁻¹)⁻¹ := by group
        _ = c := by rw [huc, inv_inv]
    calc c * (u * t) = ((u * t) * c * (u * t)⁻¹) * (u * t) := by rw [key2]
      _ = (u * t) * c := by group
  rwa [centralizer_centralizer_eq_self h hx hinv] at key

/-- `t * u ∈ F` for an involution `u ∈ M`. -/
theorem t_mul_mem_CF (h : BSWHyps2 G t s K) (hx : x ∉ HG t) (hinv : t⁻¹ * x * t = x⁻¹)
    {u : G} (huM : u ∈ NF x) (hu2 : orderOf u = 2) : t * u ∈ CF x := by
  have h1 : u * t ∈ CF x := mul_t_mem_CF h hx hinv huM hu2
  have h2 : (u * t)⁻¹ ∈ CF x := (CF x).inv_mem h1
  have hinvu : u⁻¹ = u :=
    inv_eq_of_mul_eq_one_left (Work.BSW.mul_self_eq_one_of_orderOf_eq_two hu2)
  have he : (u * t)⁻¹ = t * u := by rw [mul_inv_rev, hinvu, Work.BSW.t_inv h]
  rwa [he] at h2

/-- `t * c` is an involution of `M` for `c ∈ F`. -/
theorem mul_t_mem_NF (h : BSWHyps2 G t s K) (hx : x ∉ HG t) (hinv : t⁻¹ * x * t = x⁻¹)
    {c : G} (hc : c ∈ CF x) : t * c ∈ NF x :=
  (NF x).mul_mem (t_mem_NF h hx hinv) ((CF x).le_normalizer hc)

/-- `t * c ≠ 1` for `c ∈ F`. -/
theorem mul_t_ne_one (h : BSWHyps2 G t s K) (hx : x ∉ HG t) (hinv : t⁻¹ * x * t = x⁻¹)
    {c : G} (hc : c ∈ CF x) : t * c ≠ 1 := by
  intro h1
  refine t_notMem_centralizer h hx ?_
  have : t = c⁻¹ := by
    calc t = t * c * c⁻¹ := by rw [mul_assoc, mul_inv_cancel, mul_one]
      _ = 1 * c⁻¹ := by rw [h1]
      _ = c⁻¹ := one_mul _
  rw [this]
  exact (CF x).inv_mem hc

/-- `t * c` has order `2` for `c ∈ F`. -/
theorem orderOf_mul_t (h : BSWHyps2 G t s K) (hx : x ∉ HG t) (hinv : t⁻¹ * x * t = x⁻¹)
    {c : G} (hc : c ∈ CF x) : orderOf (t * c) = 2 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine orderOf_eq_prime ?_ (mul_t_ne_one h hx hinv hc)
  rw [pow_two]
  calc (t * c) * (t * c) = (t * c * t) * c := by group
    _ = c⁻¹ * c := by rw [inverts_centralizer h hx hinv c hc]
    _ = 1 := inv_mul_cancel c

end Basic

section TStructure

/-- The involutions of `M` are exactly the elements `t * c` with `c ∈ F`. -/
theorem mem_NF_involution_iff (h : BSWHyps2 G t s K) (hx : x ∉ HG t)
    (hinv : t⁻¹ * x * t = x⁻¹) (u : G) :
    (orderOf u = 2 ∧ u ∈ NF x) ↔ ∃ c ∈ CF x, u = t * c := by
  constructor
  · rintro ⟨hu2, huM⟩
    exact ⟨t * u, t_mul_mem_CF h hx hinv huM hu2,
      by rw [← mul_assoc, Work.BSW.t_mul_self h, one_mul]⟩
  · rintro ⟨c, hc, rfl⟩
    exact ⟨orderOf_mul_t h hx hinv hc, mul_t_mem_NF h hx hinv hc⟩

/-- The involutions of `M` number `|F|`. -/
theorem card_invM (h : BSWHyps2 G t s K) (hx : x ∉ HG t) (hinv : t⁻¹ * x * t = x⁻¹) :
    Nat.card {u : G // orderOf u = 2 ∧ u ∈ NF x} = Nat.card ↥(CF x) := by
  refine (Nat.card_congr (Equiv.ofBijective
    (fun c : ↥(CF x) => (⟨t * (c : G), orderOf_mul_t h hx hinv c.2,
      mul_t_mem_NF h hx hinv c.2⟩ : {u : G // orderOf u = 2 ∧ u ∈ NF x})) ?_)).symm
  constructor
  · intro c d hcd
    exact Subtype.ext (mul_left_cancel (congrArg (fun z : {u : G // orderOf u = 2 ∧ u ∈ NF x}
      => (z : G)) hcd))
  · intro u
    obtain ⟨c, hc, hcu⟩ := (mem_NF_involution_iff h hx hinv (u : G)).mp u.2
    exact ⟨⟨c, hc⟩, Subtype.ext hcu.symm⟩

/-- Two involutions `t * c`, `t * d` of `M` commute if and only if `c = d`. -/
theorem commute_involutions_iff (h : BSWHyps2 G t s K) (hx : x ∉ HG t)
    (hinv : t⁻¹ * x * t = x⁻¹) {c d : G} (hc : c ∈ CF x) (hd : d ∈ CF x) :
    (t * c) * (t * d) = (t * d) * (t * c) ↔ c = d := by
  constructor
  · intro hab
    have h1 : (t * c) * (t * d) = c⁻¹ * d := by
      rw [show (t * c) * (t * d) = (t * c * t) * d by group,
        inverts_centralizer h hx hinv c hc]
    have h2 : (t * d) * (t * c) = d⁻¹ * c := by
      rw [show (t * d) * (t * c) = (t * d * t) * c by group,
        inverts_centralizer h hx hinv d hd]
    have h3 : c⁻¹ * d = (c⁻¹ * d)⁻¹ := by
      calc c⁻¹ * d = (t * c) * (t * d) := h1.symm
        _ = (t * d) * (t * c) := hab
        _ = d⁻¹ * c := h2
        _ = (c⁻¹ * d)⁻¹ := by group
    have hsq : (c⁻¹ * d) * (c⁻¹ * d) = 1 := by
      have h := congrArg (fun z => z * (c⁻¹ * d)) h3
      simpa using h
    have hmem : c⁻¹ * d ∈ CF x := (CF x).mul_mem ((CF x).inv_mem hc) hd
    exact inv_mul_eq_one.mp (CF_eq_one_of_sq_eq_one h hx hmem hsq)
  · rintro rfl
    rfl

/-- **Bender §3.1 (f) engine**: `c⁻¹ * (t * d) * c = t` when `c² = d⁻¹`. -/
theorem conj_mul_t_eq_t (h : BSWHyps2 G t s K) (hx : x ∉ HG t) (hinv : t⁻¹ * x * t = x⁻¹)
    {c d : G} (hc : c ∈ CF x) (hd : d ∈ CF x) (hcd : c * c = d⁻¹) :
    c⁻¹ * (t * d) * c = t := by
  have hcdc : c⁻¹ * d * c = d := by
    calc c⁻¹ * d * c = c⁻¹ * (d * c) := by group
      _ = c⁻¹ * (c * d) := by rw [CF_comm h hx hinv hd hc]
      _ = (c⁻¹ * c) * d := by group
      _ = d := by group
  have htc : c⁻¹ * t * c = (c * c)⁻¹ * t := by
    have h1 : t * c = c⁻¹ * t := by
      calc t * c = t * c * (t * t) := by rw [Work.BSW.t_mul_self h, mul_one]
        _ = (t * c * t) * t := by group
        _ = c⁻¹ * t := by rw [inverts_centralizer h hx hinv c hc]
    calc c⁻¹ * t * c = c⁻¹ * (t * c) := by group
      _ = c⁻¹ * (c⁻¹ * t) := by rw [h1]
      _ = (c * c)⁻¹ * t := by group
  have htd : t * d = d⁻¹ * t := by
    calc t * d = t * d * (t * t) := by rw [Work.BSW.t_mul_self h, mul_one]
      _ = (t * d * t) * t := by group
      _ = d⁻¹ * t := by rw [inverts_centralizer h hx hinv d hd]
  calc c⁻¹ * (t * d) * c = (c⁻¹ * t * c) * (c⁻¹ * d * c) := by group
    _ = ((c * c)⁻¹ * t) * (c⁻¹ * d * c) := by rw [htc]
    _ = ((c * c)⁻¹ * t) * d := by rw [hcdc]
    _ = (c * c)⁻¹ * (t * d) := by group
    _ = (c * c)⁻¹ * (d⁻¹ * t) := by rw [htd]
    _ = (c * c)⁻¹ * ((c * c) * t) := by rw [← hcd]
    _ = t := by group

/-- The involutions of `M` form a single class under `M`-conjugation: every one of them is
`c * t * c⁻¹` for some `c ∈ F`. -/
theorem conj_involution_transitive (h : BSWHyps2 G t s K) (hx : x ∉ HG t)
    (hinv : t⁻¹ * x * t = x⁻¹) {u : G} (hu2 : orderOf u = 2) (huM : u ∈ NF x) :
    ∃ c ∈ CF x, u = c * t * c⁻¹ := by
  obtain ⟨d, hd, rfl⟩ := (mem_NF_involution_iff h hx hinv u).mp ⟨hu2, huM⟩
  obtain ⟨c, hc, hcs⟩ := CF_exists_sq h hx hinv ((CF x).inv_mem hd)
  refine ⟨c, hc, ?_⟩
  have hkey : c⁻¹ * (t * d) * c = t := conj_mul_t_eq_t h hx hinv hc hd hcs
  calc t * d = c * (c⁻¹ * (t * d) * c) * c⁻¹ := by group
    _ = c * t * c⁻¹ := by rw [hkey]

end TStructure

/-- Membership in a conjugate of a subgroup. -/
theorem mem_conjSub_iff' {g y : G} {H : Subgroup G} : y ∈ conjSub g H ↔ g⁻¹ * y * g ∈ H := by
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

/-- Conjugation carries centralizers to centralizers. -/
theorem centralizer_conj (a y : G) :
    Subgroup.centralizer ({a * y * a⁻¹} : Set G) =
      conjSub a (Subgroup.centralizer ({y} : Set G)) := by
  ext x
  rw [Subgroup.mem_centralizer_singleton_iff, mem_conjSub_iff',
    Subgroup.mem_centralizer_singleton_iff]
  constructor
  · intro h
    calc a⁻¹ * x * a * y = a⁻¹ * (x * (a * y * a⁻¹)) * a := by group
      _ = a⁻¹ * ((a * y * a⁻¹) * x) * a := by rw [h]
      _ = y * (a⁻¹ * x * a) := by group
  · intro h
    calc x * (a * y * a⁻¹) = a * (a⁻¹ * x * a * y) * a⁻¹ := by group
      _ = a * (y * (a⁻¹ * x * a)) * a⁻¹ := by rw [h]
      _ = (a * y * a⁻¹) * x := by group

/-- Conjugation preserves cardinality. -/
theorem card_conjSub (a : G) (H : Subgroup G) :
    Nat.card ↥(conjSub a H) = Nat.card ↥H := by
  refine Nat.card_congr {
    toFun := fun x => ⟨a⁻¹ * (x : G) * a, (mem_conjSub_iff' (g := a)).mp x.2⟩
    invFun := fun y => ⟨a * (y : G) * a⁻¹, ?_⟩
    left_inv := fun x => by ext; group
    right_inv := fun y => by ext; group }
  rw [mem_conjSub_iff']
  have he : a⁻¹ * (a * (y : G) * a⁻¹) * a = (y : G) := by group
  rw [he]
  exact y.2

/-- Every involution has centralizer of order `2k`. -/
theorem card_centralizer_eq (h : BSWHyps2 G t s K) {u : G} (hu : orderOf u = 2) :
    Nat.card ↥(Subgroup.centralizer ({u} : Set G)) = 2 * Nat.card K := by
  obtain ⟨c, hc⟩ := isConj_iff.mp (Work.BSW.involutions_conj h u hu)
  have hcu : u = c⁻¹ * t * c := by rw [← hc]; group
  rw [hcu, show c⁻¹ * t * c = c⁻¹ * t * (c⁻¹)⁻¹ from by group, centralizer_conj,
    card_conjSub, Work.BSW.centralizer_t_eq h, Work.BSW.Api.card_sup_zpowers h]

section Cardinality

/-- The conjugation action of `M = N_G(F)` on the set of its involutions. -/
instance instMulActionInvM (x : G) :
    MulAction ↥(NF x) {u : G // orderOf u = 2 ∧ u ∈ NF x} where
  smul m u := ⟨(m : G) * (u : G) * (m : G)⁻¹, by
    refine ⟨by rw [orderOf_conj]; exact u.2.1, ?_⟩
    exact (NF x).mul_mem ((NF x).mul_mem m.2 u.2.2) ((NF x).inv_mem m.2)⟩
  one_smul u := by
    apply Subtype.ext
    change (1 : G) * (u : G) * (1 : G)⁻¹ = (u : G)
    group
  mul_smul m n u := by
    apply Subtype.ext
    change ((m : G) * (n : G)) * (u : G) * ((m : G) * (n : G))⁻¹
      = (m : G) * ((n : G) * (u : G) * (n : G)⁻¹) * (m : G)⁻¹
    group

/-- The value of the conjugation action. -/
theorem smul_coe (x : G) (m : ↥(NF x)) (u : {u : G // orderOf u = 2 ∧ u ∈ NF x}) :
    ((m • u : {u : G // orderOf u = 2 ∧ u ∈ NF x}) : G) = (m : G) * (u : G) * (m : G)⁻¹ :=
  rfl

/-- `|M| = |F| · |K ⊓ M|`.  This is Bender's `n = |M : F| = |K ∩ M|`. -/
theorem card_NF (h : BSWHyps2 G t s K) (hx : x ∉ HG t) (hinv : t⁻¹ * x * t = x⁻¹) :
    Nat.card ↥(NF x) = Nat.card ↥(CF x) * Nat.card ↥(K ⊓ NF x) := by
  set b : {u : G // orderOf u = 2 ∧ u ∈ NF x} :=
    ⟨t, Work.BSW.orderOf_t h, t_mem_NF h hx hinv⟩ with hbdef
  have hb : (b : G) = t := by rw [hbdef]
  have h1 : Nat.card ↥(NF x) =
      Nat.card (MulAction.orbit ↥(NF x) b) *
        Nat.card ↥(MulAction.stabilizer ↥(NF x) b) := by
    rw [← Nat.card_prod]
    exact (Nat.card_congr (MulAction.orbitProdStabilizerEquivGroup (↥(NF x)) b)).symm
  have h2 : Nat.card (MulAction.orbit ↥(NF x) b) = Nat.card ↥(CF x) := by
    refine (Nat.card_congr (Equiv.ofBijective (fun c : ↥(CF x) =>
      (⟨⟨t * (c : G), orderOf_mul_t h hx hinv c.2, mul_t_mem_NF h hx hinv c.2⟩, by
        obtain ⟨c', hc', hcs⟩ := CF_exists_sq h hx hinv ((CF x).inv_mem c.2)
        refine ⟨⟨c', (CF x).le_normalizer hc'⟩, ?_⟩
        apply Subtype.ext
        simp only [smul_coe, Subtype.coe_mk, hb]
        have hkey : c'⁻¹ * (t * (c : G)) * c' = t := conj_mul_t_eq_t h hx hinv hc' c.2 hcs
        calc c' * t * c'⁻¹ = c' * (c'⁻¹ * (t * (c : G)) * c') * c'⁻¹ := by rw [hkey]
          _ = t * (c : G) := by group⟩ :
        MulAction.orbit ↥(NF x) b)) ?_)).symm
    constructor
    · intro c d hcd
      have hcd' : t * (c : G) = t * (d : G) :=
        congrArg (fun z : MulAction.orbit ↥(NF x) b =>
          ((z : {u : G // orderOf u = 2 ∧ u ∈ NF x}) : G)) hcd
      exact Subtype.ext (mul_left_cancel hcd')
    · rintro ⟨u, _hu⟩
      obtain ⟨c, hc, hcu⟩ := (mem_NF_involution_iff h hx hinv u).mp u.2
      exact ⟨⟨c, hc⟩, Subtype.ext (Subtype.ext hcu.symm)⟩
  have h3 : Nat.card ↥(MulAction.stabilizer ↥(NF x) b) = Nat.card ↥(K ⊓ NF x) := by
    refine Nat.card_congr {
      toFun := fun m => ⟨(m.1 : G), by
        have hm : (m.1 : ↥(NF x)) • b = b := MulAction.mem_stabilizer_iff.mp m.2
        have hmv : (m.1 : G) * t * (m.1 : G)⁻¹ = t := by
          have hh := congrArg (fun z : {u : G // orderOf u = 2 ∧ u ∈ NF x} => (z : G)) hm
          rw [smul_coe, hb] at hh
          exact hh
        have hc : (m.1 : G) ∈ NF x ⊓ Subgroup.centralizer ({t} : Set G) := by
          refine ⟨m.1.2, ?_⟩
          exact Subgroup.mem_centralizer_singleton_iff.mpr (by
            calc (m.1 : G) * t = ((m.1 : G) * t * (m.1 : G)⁻¹) * (m.1 : G) := by group
              _ = t * (m.1 : G) := by rw [hmv])
        rw [inf_normalizer_centralizer_t_eq_inf_K h hx hinv] at hc
        exact ⟨hc.2, hc.1⟩⟩
      invFun := fun y => ⟨⟨(y : G), y.2.2⟩, by
        have hy : (y : G) * t = t * (y : G) := by
          have hK := Work.BSW.K_le_centralizer_t h y.2.1
          rwa [Subgroup.mem_centralizer_singleton_iff] at hK
        refine MulAction.mem_stabilizer_iff.mpr ?_
        apply Subtype.ext
        simp only [smul_coe, Subtype.coe_mk, hb]
        calc (y : G) * t * (y : G)⁻¹ = (t * (y : G)) * (y : G)⁻¹ := by rw [hy]
          _ = t := by group⟩
      left_inv := fun m => by ext; rfl
      right_inv := fun y => by ext; rfl }
  rw [h1, h2, h3]

/-- `|C_M(u)| = |K ⊓ M|` for every involution `u ∈ M`. -/
theorem card_CM (h : BSWHyps2 G t s K) (hx : x ∉ HG t) (hinv : t⁻¹ * x * t = x⁻¹)
    {u : G} (huM : u ∈ NF x) (hu2 : orderOf u = 2) :
    Nat.card ↥(NF x ⊓ Subgroup.centralizer ({u} : Set G)) = Nat.card ↥(K ⊓ NF x) := by
  obtain ⟨c, hc, hcu⟩ := conj_involution_transitive h hx hinv hu2 huM
  have hcM : c ∈ NF x := (CF x).le_normalizer hc
  have hcinvM : c⁻¹ ∈ NF x := (NF x).inv_mem hcM
  have hct : t = c⁻¹ * u * c := by rw [hcu]; group
  have hmem1 : ∀ y : G, y ∈ NF x ⊓ Subgroup.centralizer ({u} : Set G) →
      c⁻¹ * y * c ∈ NF x ⊓ Subgroup.centralizer ({t} : Set G) := by
    intro y hy
    have hyc : y * c ∈ NF x := mul_mem hy.1 hcM
    refine ⟨?_, ?_⟩
    · rw [mul_assoc]
      exact mul_mem hcinvM hyc
    have hy' : y * u = u * y := Subgroup.mem_centralizer_singleton_iff.mp hy.2
    exact Subgroup.mem_centralizer_singleton_iff.mpr (by
      calc c⁻¹ * y * c * t = c⁻¹ * y * c * (c⁻¹ * u * c) := by rw [hct]
        _ = c⁻¹ * (y * u) * c := by group
        _ = c⁻¹ * (u * y) * c := by rw [hy']
        _ = t * (c⁻¹ * y * c) := by rw [hct]; group)
  have hmem2 : ∀ y : G, y ∈ NF x ⊓ Subgroup.centralizer ({t} : Set G) →
      c * y * c⁻¹ ∈ NF x ⊓ Subgroup.centralizer ({u} : Set G) := by
    intro y hy
    have hyc : y * c⁻¹ ∈ NF x := mul_mem hy.1 hcinvM
    refine ⟨?_, ?_⟩
    · rw [mul_assoc]
      exact mul_mem hcM hyc
    have hy' : y * t = t * y := Subgroup.mem_centralizer_singleton_iff.mp hy.2
    exact Subgroup.mem_centralizer_singleton_iff.mpr (by
      calc c * y * c⁻¹ * u = c * y * c⁻¹ * (c * t * c⁻¹) := by rw [hcu]
        _ = c * (y * t) * c⁻¹ := by group
        _ = c * (t * y) * c⁻¹ := by rw [hy']
        _ = u * (c * y * c⁻¹) := by rw [hcu]; group)
  have hmain : Nat.card ↥(NF x ⊓ Subgroup.centralizer ({u} : Set G)) =
      Nat.card ↥(NF x ⊓ Subgroup.centralizer ({t} : Set G)) :=
    Nat.card_congr {
      toFun := fun y => ⟨c⁻¹ * (y : G) * c, hmem1 (y : G) y.2⟩
      invFun := fun y => ⟨c * (y : G) * c⁻¹, hmem2 (y : G) y.2⟩
      left_inv := fun y => by ext; group
      right_inv := fun y => by ext; group }
  rw [hmain, inf_normalizer_centralizer_t_eq_inf_K h hx hinv, inf_comm]

end Cardinality

end Work.BSW.Cases
