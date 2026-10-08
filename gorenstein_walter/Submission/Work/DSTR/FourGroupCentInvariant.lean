import Mathlib
import Submission.Work.DSTR.D110iDefs

/-!
# Bender 1.10(i) for a self-centralising normal four-group

Let `Q` be a finite group and `V ⊴ Q` a (Klein) four-group whose centraliser in `Q` is `V`
itself.  This file proves that then `Q` satisfies `Work.DSTR.CentInvariant`, i.e. Bender 1981,
1.10(i) in the shape of clause 2 of `DShape`:

every odd `p`-subgroup `P ≤ Q` normalised by the centraliser of an involution `t ∈ Q` is
centralised by `t`.

## Structure of the argument

Write `Cent(t) = C_Q(t)`.  Given an involution `t`, an odd prime `p`, a `p`-subgroup `P` with
`Cent(t) ≤ N_Q(P)`, we must show `P ≤ Cent(t)`; we prove that actually the hypothesis forces
`P = 1`.

* `P ⊓ V = ⊥`: `P ∩ V` has order dividing `|V| = 4` and is a power of the odd prime `p`.
* `C_Q(P) ⊓ V = ⊥` (`centralizer_inf_eq_bot_of_isPGroup_odd`): `P` acts on `V` by conjugation
  and the action is faithful because `C_Q(V) = V` and `P ⊓ V = ⊥`; the fixed-point congruence
  `|V| ≡ |C_V(P)| [MOD p]` (`IsPGroup.card_modEq_card_fixedPoints`) together with `|V| = 4`
  and `|C_V(P)| ≤ 4` excludes `|C_V(P)| = 4` (which would give `P ≤ C_Q(V) = V`, whence
  `P ≤ P ⊓ V = ⊥`), so `|C_V(P)| = 1`.
* `V ⊓ N_Q(P) = ⊥`: if `v ∈ V` normalises `P` then for `x ∈ P` the commutator `[v,x]` lies in
  `P` (as `v ∈ N(P)`) and in `V` (as `V ⊴ Q`), hence in `P ⊓ V = ⊥`; so `v ∈ C_Q(P)`, and
  `C_Q(P) ⊓ V = ⊥`.
* If `t ∈ V` then `t ∈ C_Q(t) ≤ N_Q(P)` gives `t ∈ V ⊓ N_Q(P) = ⊥`, i.e. `t = 1`,
  contradicting `orderOf t = 2`.
* If `t ∉ V` then `⟨t⟩` acts on `V` by conjugation and faithfully, so
  `4 ≡ |C_V(t)| [MOD 2]` forces `|C_V(t)| ≥ 2`: there is `1 ≠ w ∈ V` with `w t = t w`
  (`exists_commuting_of_orderOf_eq_two`).  Then `w ∈ C_Q(t) ≤ N_Q(P)` gives
  `w ∈ V ⊓ N_Q(P) = ⊥`, a contradiction.

In particular the extra hypothesis `O(Q) = 1` (no nontrivial normal subgroup of odd order),
which belongs to the mathematical setting of Bender 1.10(i), is not needed for this shape.
-/

set_option linter.style.haveILetI false

namespace Work.DSTR

open Subgroup

/-- **A nontrivial odd-prime-power subgroup acting faithfully on a group of order `4` has
trivial centraliser there.**  If `P ≤ Q` with `P ≠ 1` is a `p`-group for an odd prime `p`,
`V ⊴ Q` has order `4`, `P ⊓ V = ⊥` and `C_Q(V) = V`, then `C_Q(P) ⊓ V = ⊥`.

`P` acts on `V` by conjugation, faithfully: the kernel of the action is `C_Q(P) ⊓ V` and meets
`P` in `P ⊓ V = ⊥`.  The coprime-action congruence `|V| ≡ |C_V(P)| [MOD p]` shows that the
fixed-point subgroup `C_V(P) ≤ V` has order congruent to `4` modulo `p` and at most `4`;
order `4` is excluded because it forces `P ≤ C_Q(V) = V`, hence `P ≤ P ⊓ V = ⊥`. -/
theorem centralizer_inf_eq_bot_of_isPGroup_odd {Q : Type*} [Group Q] [Finite Q]
    {V P : Subgroup Q} (hVn : V.Normal) (hcard : Nat.card V = 4)
    (hVc : Subgroup.centralizer (V : Set Q) = V)
    (hPV : P ⊓ V = ⊥) (hPne : P ≠ ⊥) {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    (hP : IsPGroup p P) :
    Subgroup.centralizer (P : Set Q) ⊓ V = ⊥ := by
  classical
  haveI : V.Normal := hVn
  let inst : MulAction P V := MulAction.compHom V ((MulAut.conjNormal (H := V)).comp P.subtype)
  letI : MulAction P V := inst
  let Fix : Set V := @MulAction.fixedPoints P V _ inst
  have hFixEq : Fix = {a : V | ∀ m : P, m • a = a} := rfl
  have hmod : 4 ≡ Nat.card ↥Fix [MOD p] := by
    rw [← hcard]; exact hP.card_modEq_card_fixedPoints V
  have hle : Nat.card ↥Fix ≤ 4 := by
    have h := Nat.card_le_card_of_injective (fun x : ↥Fix => (x : V)) Subtype.val_injective
    rwa [hcard] at h
  have hone : (⟨1, V.one_mem⟩ : V) ∈ Fix := by
    rw [hFixEq]; intro m
    change (MulAut.conjNormal (H := V) (m : Q)) (⟨1, V.one_mem⟩ : V) = ⟨1, V.one_mem⟩
    exact map_one _
  have hne4 : Nat.card ↥Fix ≠ 4 := by
    intro hk4
    have hFixuniv : Fix = Set.univ := by
      refine Set.eq_of_subset_of_ncard_le (Set.subset_univ _) ?_
      rw [Set.ncard_univ, ← Nat.card_coe_set_eq (s := Fix), hcard, hk4]
    have hPle : P ≤ Subgroup.centralizer (V : Set Q) := by
      intro g hg
      rw [Subgroup.mem_centralizer_iff]
      intro w hw
      have hw' : (⟨w, hw⟩ : V) ∈ Fix := by rw [hFixuniv]; trivial
      rw [hFixEq] at hw'
      have hsm := hw' ⟨g, hg⟩
      have hsm' : (MulAut.conjNormal (H := V) g) (⟨w, hw⟩ : V) = ⟨w, hw⟩ := hsm
      have hval : g * w * g⁻¹ = w := by
        have h2 := congrArg (Subtype.val) hsm'
        simpa only [MulAut.conjNormal_apply] using h2
      conv_lhs => rw [← hval]
      group
    have hleV : P ≤ V := le_trans hPle (le_of_eq hVc)
    have hPbot : P ≤ ⊥ := by rw [← hPV]; exact le_inf le_rfl hleV
    exact hPne (le_bot_iff.mp hPbot)
  have hk1 : Nat.card ↥Fix = 1 := by
    have hdvd : p ∣ 4 - Nat.card ↥Fix := (Nat.modEq_iff_dvd' hle).mp hmod.symm
    have hpge3 : 3 ≤ p := by have := (Fact.out : p.Prime).two_le; omega
    have hk3 : Nat.card ↥Fix ≤ 3 := by omega
    have : p ≤ 4 - Nat.card ↥Fix := Nat.le_of_dvd (by omega) hdvd
    haveI : Nonempty ↥Fix := ⟨⟨⟨1, V.one_mem⟩, hone⟩⟩
    have hge1 : 1 ≤ Nat.card ↥Fix := Nat.card_pos
    omega
  rw [eq_bot_iff]
  intro v hv
  rw [Subgroup.mem_bot]
  have hvV : v ∈ V := hv.2
  have hvC : v ∈ Subgroup.centralizer (P : Set Q) := hv.1
  have hmem : (⟨v, hvV⟩ : V) ∈ Fix := by
    rw [hFixEq]; intro m
    change (MulAut.conjNormal (H := V) (m : Q)) ⟨v, hvV⟩ = ⟨v, hvV⟩
    apply Subtype.ext
    rw [MulAut.conjNormal_apply]
    have hcomm := (Subgroup.mem_centralizer_iff.mp hvC) (m : Q) m.2
    rw [hcomm]; group
  haveI : Subsingleton ↥Fix := (Nat.card_eq_one_iff_unique.mp hk1).1
  have hm := Subsingleton.elim (⟨⟨v, hvV⟩, hmem⟩ : ↥Fix) (⟨⟨1, V.one_mem⟩, hone⟩ : ↥Fix)
  have h1 : (⟨v, hvV⟩ : V) = ⟨1, V.one_mem⟩ := Subtype.ext_iff.mp hm
  exact Subtype.ext_iff.mp h1

/-- **An involution acting on a group of order `4` fixes a nonidentity element.**  If `V ⊴ Q`
has order `4` and `t ∈ Q` is an involution, then some `1 ≠ w ∈ V` commutes with `t`.

`⟨t⟩` is a `2`-group acting on `V` by conjugation, so `|V| ≡ |C_V(t)| [MOD 2]`; hence
`|C_V(t)|` is even, and since `1 ∈ C_V(t)` we get `|C_V(t)| ≥ 2`. -/
theorem exists_commuting_of_orderOf_eq_two {Q : Type*} [Group Q] [Finite Q]
    {V : Subgroup Q} (hVn : V.Normal) (hcard : Nat.card V = 4)
    {t : Q} (ht : orderOf t = 2) :
    ∃ w ∈ V, w ≠ 1 ∧ w * t = t * w := by
  classical
  haveI : V.Normal := hVn
  let inst : MulAction ↥(Subgroup.zpowers t) V :=
    MulAction.compHom V ((MulAut.conjNormal (H := V)).comp (Subgroup.zpowers t).subtype)
  letI : MulAction ↥(Subgroup.zpowers t) V := inst
  have hzp2 : Nat.card ↥(Subgroup.zpowers t) = 2 := by rw [Nat.card_zpowers, ht]
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hPg : IsPGroup 2 ↥(Subgroup.zpowers t) :=
    IsPGroup.of_card (n := 1) (by rw [hzp2]; norm_num)
  have hmod := hPg.card_modEq_card_fixedPoints V
  have hmod' : 4 ≡ Nat.card ↥(@MulAction.fixedPoints ↥(Subgroup.zpowers t) V _ inst) [MOD 2] := by
    rw [← hcard]; exact hmod
  have hFixEq : @MulAction.fixedPoints ↥(Subgroup.zpowers t) V _ inst
      = {a : V | ∀ m : ↥(Subgroup.zpowers t), m • a = a} := rfl
  have hone : (⟨1, V.one_mem⟩ : V) ∈ @MulAction.fixedPoints ↥(Subgroup.zpowers t) V _ inst := by
    rw [hFixEq]; intro m
    change (MulAut.conjNormal (m : Q)) (⟨1, V.one_mem⟩ : V) = ⟨1, V.one_mem⟩
    exact map_one _
  have heven : Even (Nat.card ↥(@MulAction.fixedPoints ↥(Subgroup.zpowers t) V _ inst)) := by
    have h0 : Nat.card ↥(@MulAction.fixedPoints ↥(Subgroup.zpowers t) V _ inst) ≡ 0 [MOD 2] :=
      hmod'.symm.trans (by decide)
    exact even_iff_two_dvd.mpr (Nat.modEq_zero_iff_dvd.mp h0)
  haveI : Nonempty ↥(@MulAction.fixedPoints ↥(Subgroup.zpowers t) V _ inst) :=
    ⟨⟨⟨1, V.one_mem⟩, hone⟩⟩
  haveI : Finite ↥(@MulAction.fixedPoints ↥(Subgroup.zpowers t) V _ inst) := inferInstance
  have h2 : 2 ≤ Nat.card ↥(@MulAction.fixedPoints ↥(Subgroup.zpowers t) V _ inst) := by
    obtain ⟨j, hj⟩ := heven
    have := Nat.card_pos (α := ↥(@MulAction.fixedPoints ↥(Subgroup.zpowers t) V _ inst))
    omega
  haveI : Fintype ↥(@MulAction.fixedPoints ↥(Subgroup.zpowers t) V _ inst) := Fintype.ofFinite _
  obtain ⟨a, ha⟩ := Fintype.exists_ne_of_one_lt_card
    (α := ↥(@MulAction.fixedPoints ↥(Subgroup.zpowers t) V _ inst))
    (by rw [Fintype.card_eq_nat_card]; omega) ⟨⟨1, V.one_mem⟩, hone⟩
  have haFix : a.1 ∈ {x : V | ∀ m : ↥(Subgroup.zpowers t), m • x = x} := hFixEq ▸ a.2
  have hsmul := haFix ⟨t, Subgroup.mem_zpowers t⟩
  have hsmul' : (MulAut.conjNormal (H := V) t) a.1 = a.1 := hsmul
  have hval : t * (a.1 : Q) * t⁻¹ = (a.1 : Q) := by
    have h2' := congrArg (Subtype.val) hsmul'
    simpa only [MulAut.conjNormal_apply] using h2'
  have ha1 : (a.1 : Q) ≠ 1 := by
    intro h
    exact ha (Subtype.ext (Subtype.ext h))
  refine ⟨(a.1 : Q), a.1.2, ha1, ?_⟩
  have hcomm : t * (a.1 : Q) = (a.1 : Q) * t := by
    calc t * (a.1 : Q) = (t * (a.1 : Q) * t⁻¹) * t := by group
      _ = (a.1 : Q) * t := by rw [hval]
  exact hcomm.symm

theorem FourGroupCentInvariant (Q : Type*) [Group Q] [Finite Q] (V : Subgroup Q) (hVn : V.Normal)
    (hcard : Nat.card V = 4) (hsq : ∀ v ∈ V, v ^ 2 = 1)
    (hVc : Subgroup.centralizer (V : Set Q) = V)
    (hO : ∀ N : Subgroup Q, N.Normal → Odd (Nat.card N) → N = ⊥) :
    Work.DSTR.CentInvariant Q := by
  intro t ht p hp hp2 P hP hC
  by_cases hPbot : P = ⊥
  · rw [hPbot]; exact bot_le
  exfalso
  -- `P` meets `V` trivially
  have hPV : P ⊓ V = ⊥ := by
    rw [← Subgroup.card_eq_one]
    have h1 : Nat.card ↥(P ⊓ V) ∣ Nat.card ↥V := Subgroup.card_dvd_of_le inf_le_right
    have h2 : Nat.card ↥(P ⊓ V) ∣ Nat.card ↥P := Subgroup.card_dvd_of_le inf_le_left
    rw [hcard] at h1
    obtain ⟨m, hm⟩ := IsPGroup.iff_card.mp hP
    rw [hm] at h2
    have hoddp : Odd p := (Fact.out : p.Prime).odd_of_ne_two hp2
    have hodd : Odd (Nat.card ↥(P ⊓ V)) := Odd.of_dvd_nat (hoddp.pow (n := m)) h2
    have h1' : Nat.card ↥(P ⊓ V) ∣ 2 ^ 2 := by
      rw [show (2 : ℕ) ^ 2 = 4 from by norm_num]; exact h1
    obtain ⟨k, _hk, hkeq⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp h1'
    have hk0 : k = 0 := by
      by_contra hk
      have hkpos : 0 < k := Nat.pos_of_ne_zero hk
      have h2dvd : 2 ∣ 2 ^ k := dvd_pow_self 2 (Nat.pos_iff_ne_zero.mp hkpos)
      rw [hkeq] at hodd
      exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr h2dvd)
    rw [hkeq, hk0]
    simp
  -- `C_Q(P) ⊓ V = ⊥`
  have hCP : Subgroup.centralizer (P : Set Q) ⊓ V = ⊥ :=
    centralizer_inf_eq_bot_of_isPGroup_odd hVn hcard hVc hPV hPbot hp2 hP
  -- `V ⊓ N_Q(P) = ⊥`
  have hVN : V ⊓ Subgroup.normalizer (P : Set Q) = ⊥ := by
    rw [eq_bot_iff]
    intro v hv
    rw [Subgroup.mem_bot]
    have hvV : v ∈ V := hv.1
    have hvN : v ∈ Subgroup.normalizer (P : Set Q) := hv.2
    have hCv : v ∈ Subgroup.centralizer (P : Set Q) := by
      rw [Subgroup.mem_centralizer_iff]
      intro g hg
      have hgP : v * g * v⁻¹ ∈ P := (Subgroup.mem_normalizer_iff.mp hvN g).mp hg
      have hmemP : v * g * v⁻¹ * g⁻¹ ∈ P := P.mul_mem hgP (P.inv_mem hg)
      have hmemV : v * g * v⁻¹ * g⁻¹ ∈ V := by
        have h1 : (g * v * g⁻¹ * v⁻¹)⁻¹ ∈ V :=
          V.inv_mem (V.mul_mem (hVn.conj_mem v hvV g) (V.inv_mem hvV))
        have heq : (g * v * g⁻¹ * v⁻¹)⁻¹ = v * g * v⁻¹ * g⁻¹ := by group
        rwa [heq] at h1
      have hone : v * g * v⁻¹ * g⁻¹ = 1 := by
        have hk : v * g * v⁻¹ * g⁻¹ ∈ P ⊓ V := ⟨hmemP, hmemV⟩
        rw [hPV] at hk
        exact Subgroup.mem_bot.mp hk
      have hvge : v * g * v⁻¹ = g := by
        calc v * g * v⁻¹ = v * g * v⁻¹ * g⁻¹ * g := by group
          _ = 1 * g := by rw [hone]
          _ = g := by rw [one_mul]
      calc g * v = (v * g * v⁻¹) * v := by rw [hvge]
        _ = v * g := by group
    have hvbot : v ∈ Subgroup.centralizer (P : Set Q) ⊓ V := ⟨hCv, hvV⟩
    rw [hCP] at hvbot
    exact Subgroup.mem_bot.mp hvbot
  by_cases htV : t ∈ V
  · -- `t ∈ V ⊓ N_Q(P) = ⊥` contradicts `orderOf t = 2`
    have htC : t ∈ Subgroup.centralizer ({t} : Set Q) :=
      (Subgroup.mem_centralizer_singleton_iff (g := t) (k := t)).mpr rfl
    have htN : t ∈ Subgroup.normalizer (P : Set Q) := hC htC
    have htbot : t ∈ V ⊓ Subgroup.normalizer (P : Set Q) := ⟨htV, htN⟩
    rw [hVN] at htbot
    have ht1 : t = 1 := Subgroup.mem_bot.mp htbot
    rw [ht1] at ht
    simp at ht
  · -- some `1 ≠ w ∈ V` commutes with `t`, and `w ∈ V ⊓ N_Q(P) = ⊥`
    obtain ⟨w, hwV, hw1, hwcomm⟩ := exists_commuting_of_orderOf_eq_two hVn hcard ht
    have hwC : w ∈ Subgroup.centralizer ({t} : Set Q) :=
      (Subgroup.mem_centralizer_singleton_iff (g := t) (k := w)).mpr hwcomm
    have hwN : w ∈ Subgroup.normalizer (P : Set Q) := hC hwC
    have hwbot : w ∈ V ⊓ Subgroup.normalizer (P : Set Q) := ⟨hwV, hwN⟩
    rw [hVN] at hwbot
    exact hw1 (Subgroup.mem_bot.mp hwbot)

end Work.DSTR
