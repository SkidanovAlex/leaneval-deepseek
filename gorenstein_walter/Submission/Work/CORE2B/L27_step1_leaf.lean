import Mathlib
import Submission.Work.CORE2B.Basic
import Submission.Work.CORE2B.API
import Submission.Work.CORE2B.t_central_in_S
import Submission.Work.CORE2B.BenderCtx_sylow_not_cyclic
import Submission.Work.CORE2B.sylow_central_of_large_inter
import Submission.Work.RED.DihedralSubgroup
import Submission.Work.RED.even_dihedral_param_of_isPGroup_two_not_isCyclic
import Submission.Work.FUS.DihedralSylow.subgroup_cyclic_or_dihedral
import Submission.Work.AUTA7.GroupTheory.SylowInfNormal
import Submission.Work.Dihedral.Defs
import Submission.Work.FUS.thompson_transfer

/-!
# `Work.CORE2B.L27_step1_leaf` — Bender 1981, Lemma 2.7, step 1

Bender's Lemma 2.7 begins: *"Our assumptions force every normal subgroup of `M` of order
divisible by `4` to contain `t`."*  This file proves that leaf, i.e.

`L27_normal_contains_t`:  for `N ≤ M` with `N ◁ M` and `4 ∣ |N|`, we have `t ∈ N`.

The argument, in the shape in which it is formalised here:

* (`sylow_central_of_large_inter`, already in the workspace) — if `8 ≤ |S ⊓ M|`, some Sylow
  2-subgroup `P` of `M` centralises `t`;
* (`card_four_centralizes`) — if `|S| = 4`, every 2-subgroup of `G` has order `≤ 4` and is
  commutative, so a Sylow 2-subgroup `P` of `M` containing `t` centralises `t`;
* (`twoResidual_centralizes`) — if `t ∈ O²(M)`, Thompson's transfer lemma forces a Sylow
  2-subgroup `P` of `M` with `t ∈ Z(P)` (otherwise a normal subgroup of `M` of index `2`
  avoiding `t` exists, which is impossible since `t ∈ O²(M)`);
* (`normal_contains_center`) — once `t ∈ Z(P)` for a Sylow 2-subgroup `P` of `M` (`P` is a
  non-cyclic 2-subgroup of a group with dihedral Sylow 2-subgroups, hence dihedral), any normal
  `N ◁ M` with `4 ∣ |N|` satisfies `|N ⊓ P| ≥ 4`, and every 2-subgroup of a dihedral 2-group of
  order `≥ 4` contains the centre, i.e. `t`.
-/

open scoped MatrixGroups

set_option linter.unusedVariables false
set_option linter.style.haveILetI false

namespace Work.CORE2B

open Subgroup

/-! ## 1. A cyclic group has at most one involution -/

private theorem eq_of_orderOf_eq_two_of_isCyclic {H : Type*} [Group H] [Finite H] [IsCyclic H]
    {a b : H} (ha : orderOf a = 2) (hb : orderOf b = 2) : a = b := by
  classical
  haveI := Fintype.ofFinite H
  have hd : 2 ∣ Fintype.card H := by
    rw [← Nat.card_eq_fintype_card, ← ha]
    exact orderOf_dvd_natCard a
  have hcard : Fintype.card {x : H // orderOf x = 2} = 1 := by
    rw [Fintype.card_subtype, IsCyclic.card_orderOf_eq_totient (α := H) hd, Nat.totient_two]
  exact Subtype.ext_iff.mp (Fintype.card_le_one_iff.mp (le_of_eq hcard) ⟨a, ha⟩ ⟨b, hb⟩)

/-- A group of order at most `4` is commutative. -/
private theorem isMulCommutative_of_card_le_four {X : Type} [Group X] [Finite X]
    (h : Nat.card X ≤ 4) : IsMulCommutative X := by
  by_cases hcyc : IsCyclic X
  · exact hcyc.isMulCommutative
  · have htwo : ∀ x : X, orderOf x ∣ 2 := by
      intro x
      have hdvd : orderOf x ∣ Nat.card X := orderOf_dvd_natCard x
      have hne : orderOf x ≠ Nat.card X := fun hc =>
        hcyc (isCyclic_iff_exists_orderOf_eq_natCard.mpr ⟨x, hc⟩)
      have hcard : Nat.card X = 1 ∨ Nat.card X = 2 ∨ Nat.card X = 3 ∨ Nat.card X = 4 := by
        have := Nat.card_pos (α := X)
        omega
      rcases hcard with hc | hc | hc | hc
      · rw [hc, Nat.dvd_one] at hdvd
        rw [hdvd]; exact one_dvd 2
      · rw [hc] at hdvd
        rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h1 | h2
        · rw [h1]; exact one_dvd 2
        · exact absurd (by rw [hc, h2]) hne
      · rw [hc] at hdvd
        rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h1 | h3
        · rw [h1]; exact one_dvd 2
        · exact absurd (by rw [hc, h3]) hne
      · rw [hc] at hdvd
        rcases (Nat.dvd_prime_pow (p := 2) (m := 2) Nat.prime_two).mp (by simpa using hdvd) with
          ⟨k, hk, hkx⟩
        interval_cases k
        · rw [show orderOf x = 1 from by simpa using hkx]; exact one_dvd 2
        · rw [show orderOf x = 2 from by simpa using hkx]
        · exact absurd (by rw [hc]; simpa using hkx) hne
    have hsq : ∀ x : X, x * x = 1 := by
      intro x
      rw [← pow_two]
      exact (orderOf_dvd_iff_pow_eq_one (n := 2)).mp (htwo x)
    refine ⟨⟨fun a b => ?_⟩⟩
    have hab : (a * b) * (a * b) = 1 := hsq (a * b)
    calc a * b = ((a * b) * (a * b)) * (a * b) := by rw [hab, one_mul]
      _ = (a * b)⁻¹ := by rw [hab, one_mul, inv_eq_of_mul_eq_one_right hab]
      _ = b⁻¹ * a⁻¹ := mul_inv_rev a b
      _ = b * a := by
          rw [inv_eq_of_mul_eq_one_right (hsq a), inv_eq_of_mul_eq_one_right (hsq b)]

/-! ## 2. The centre of a dihedral 2-group -/

/-- `(r (m/2))^2 = 1` for even `m`. -/
private lemma dihedral_r_half_sq {m : ℕ} (hm : Even m) :
    (DihedralGroup.r ((m / 2 : ℕ) : ZMod m) : DihedralGroup m) ^ 2 = 1 := by
  obtain ⟨k, hk⟩ := hm
  have h2m : m / 2 + m / 2 = m := by omega
  rw [pow_two, DihedralGroup.r_mul_r]
  have h : ((m / 2 : ℕ) : ZMod m) + ((m / 2 : ℕ) : ZMod m) = 0 := by
    rw [← Nat.cast_add, h2m, ZMod.natCast_self]
  rw [h, DihedralGroup.r_zero]

/-- `r (m/2)` has order `2` for even `m ≠ 0`. -/
private lemma dihedral_orderOf_r_half {m : ℕ} (hm : Even m) (hm0 : m ≠ 0) :
    orderOf (DihedralGroup.r ((m / 2 : ℕ) : ZMod m) : DihedralGroup m) = 2 := by
  obtain ⟨k, hk⟩ := hm
  refine orderOf_eq_prime (dihedral_r_half_sq ⟨k, hk⟩) ?_
  intro h
  have h0 : ((m / 2 : ℕ) : ZMod m) = 0 :=
    DihedralGroup.r.inj (by rw [h, DihedralGroup.r_zero])
  rw [ZMod.natCast_eq_zero_iff] at h0
  have hpos : 0 < m / 2 := by omega
  have := Nat.le_of_dvd hpos h0
  omega

/-- A central involution of `DihedralGroup m` (`m` even, `m ≠ 0, 2`) is `r (m/2)`. -/
private lemma dihedral_center_inv_eq_r_half {m : ℕ} (hm : Even m) (hm0 : m ≠ 0) (hm2 : m ≠ 2)
    {u : DihedralGroup m} (hu : u ∈ Subgroup.center (DihedralGroup m))
    (hu2 : orderOf u = 2) : u = DihedralGroup.r ((m / 2 : ℕ) : ZMod m) := by
  haveI : NeZero m := ⟨hm0⟩
  set g : DihedralGroup m := DihedralGroup.r ((m / 2 : ℕ) : ZMod m) with hg
  have huz : u ∈ Subgroup.zpowers g := by
    rw [hg, ← DihedralGroup.center_eq_closure_of_even_ne_two hm hm2]
    exact hu
  haveI : IsCyclic ↥(Subgroup.zpowers g) := Subgroup.isCyclic_zpowers g
  have h1 : orderOf (⟨u, huz⟩ : ↥(Subgroup.zpowers g)) = 2 := by
    rw [Subgroup.orderOf_mk]; exact hu2
  have h2 : orderOf (⟨g, Subgroup.mem_zpowers g⟩ : ↥(Subgroup.zpowers g)) = 2 := by
    rw [Subgroup.orderOf_mk, hg]; exact dihedral_orderOf_r_half hm hm0
  exact congrArg Subtype.val (eq_of_orderOf_eq_two_of_isCyclic h1 h2)

private lemma rot_isCyclic (m : ℕ) [NeZero m] : IsCyclic ↥(Work.Dihedral.rot m) := by
  rw [Work.Dihedral.rot_eq_zpowers_r_one]
  exact Subgroup.isCyclic_zpowers _

/-- **The central element `r (m/2)` lies in every `2`-subgroup of `DihedralGroup m` of order
`≥ 4`** (`m` even, `m ≠ 0`). -/
private lemma dihedral_r_half_mem_of_two_subgroup {m : ℕ} (hm : Even m) (hm0 : m ≠ 0)
    (Q : Subgroup (DihedralGroup m)) (hQ : IsPGroup 2 Q) (hcard : 4 ≤ Nat.card Q) :
    DihedralGroup.r ((m / 2 : ℕ) : ZMod m) ∈ Q := by
  haveI : NeZero m := ⟨hm0⟩
  let f : ↥Q →* Multiplicative (ZMod 2) := (Work.RED.dihedralSign m).comp Q.subtype
  have hker : f.ker = (Q ⊓ Work.Dihedral.rot m).subgroupOf Q := by
    ext x
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    show Work.RED.dihedralSign m (x : DihedralGroup m) = 1 ↔ _
    rw [Work.RED.dihedralSign_eq_one_iff]
    exact ⟨fun h => ⟨x.2, h⟩, fun h => h.2⟩
  have hidx : (Q ⊓ Work.Dihedral.rot m).relIndex Q ≤ 2 := by
    have h1 : (Q ⊓ Work.Dihedral.rot m).relIndex Q =
        ((Q ⊓ Work.Dihedral.rot m).subgroupOf Q).index := rfl
    rw [h1, ← hker, Subgroup.index_ker]
    calc Nat.card ↥f.range ≤ Nat.card (Multiplicative (ZMod 2)) :=
          Nat.card_le_card_of_injective _ Subtype.val_injective
      _ = 2 := Work.RED.natCard_multiplicative_zmod_two
  have hcardA : 2 ≤ Nat.card ↥(Q ⊓ Work.Dihedral.rot m) := by
    have h := Subgroup.relIndex_mul_card (Q ⊓ Work.Dihedral.rot m) Q
    rw [inf_eq_left.mpr inf_le_left] at h
    have hle : Nat.card ↥Q ≤ 2 * Nat.card ↥(Q ⊓ Work.Dihedral.rot m) := by
      rw [← h]; exact Nat.mul_le_mul_right _ hidx
    omega
  have hA2 : IsPGroup 2 ↥(Q ⊓ Work.Dihedral.rot m) := hQ.to_le inf_le_left
  have h2dvd : 2 ∣ Nat.card ↥(Q ⊓ Work.Dihedral.rot m) := by
    rcases hA2.card_eq_or_dvd with h | h
    · omega
    · exact h
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' 2 h2dvd
  have hx2 : orderOf (x : DihedralGroup m) = 2 := by
    rw [Subgroup.orderOf_coe]; exact hx
  have hxrot : (x : DihedralGroup m) ∈ Work.Dihedral.rot m := x.2.2
  have hxQ : (x : DihedralGroup m) ∈ Q := x.2.1
  haveI : IsCyclic ↥(Work.Dihedral.rot m) := rot_isCyclic m
  have hr2 : orderOf (DihedralGroup.r ((m / 2 : ℕ) : ZMod m) : DihedralGroup m) = 2 :=
    dihedral_orderOf_r_half hm hm0
  have hrrot : (DihedralGroup.r ((m / 2 : ℕ) : ZMod m) : DihedralGroup m) ∈
      Work.Dihedral.rot m := Work.Dihedral.r_mem_rot _
  have heq : (⟨(x : DihedralGroup m), hxrot⟩ : ↥(Work.Dihedral.rot m)) =
      ⟨DihedralGroup.r ((m / 2 : ℕ) : ZMod m), hrrot⟩ :=
    eq_of_orderOf_eq_two_of_isCyclic
      (by rw [Subgroup.orderOf_mk]; exact hx2)
      (by rw [Subgroup.orderOf_mk]; exact hr2)
  have heq' : DihedralGroup.r ((m / 2 : ℕ) : ZMod m) = (x : DihedralGroup m) :=
    (congrArg Subtype.val heq).symm
  rw [heq']
  exact hxQ

/-! ## 3. `2`-subgroups of a dihedral group: which ones contain a given central involution -/

/-- Let `P` be a subgroup of a finite group `X` isomorphic to `DihedralGroup m` (`2 ≤ m`, `m`
even), and let `t ∈ Z(P)` be an involution.  Then `t` lies in every subgroup `Q ≤ P` with
`4 ≤ |Q|`. -/
private lemma center_mem_of_dihedral_iso {X : Type} [Group X] [Finite X] (P Q : Subgroup X)
    (m : ℕ) (hm2 : 2 ≤ m) (hmE : Even m) (e : ↥P ≃* DihedralGroup m) (hP2 : IsPGroup 2 P)
    (hQ : Q ≤ P) (hcard : 4 ≤ Nat.card Q)
    (t : X) (htP : t ∈ P) (ht2 : orderOf t = 2) (htz : ∀ x ∈ P, x * t = t * x) :
    t ∈ Q := by
  by_cases hm2' : m = 2
  · subst hm2'
    have hcardP : Nat.card ↥P = 4 := by
      rw [Nat.card_congr e.toEquiv, DihedralGroup.nat_card]
    have hle : Nat.card ↥Q ≤ 4 := by
      have h := Subgroup.card_le_of_le hQ
      rwa [hcardP] at h
    have hcardQ : Nat.card ↥Q = 4 := le_antisymm hle hcard
    have hQeq : Q = P := Subgroup.eq_of_le_of_card_ge hQ (by rw [hcardP, hcardQ])
    rw [hQeq]; exact htP
  · have hm0 : m ≠ 0 := by omega
    set u : DihedralGroup m := e ⟨t, htP⟩ with hu
    have hucent : u ∈ Subgroup.center (DihedralGroup m) := by
      rw [Subgroup.mem_center_iff]
      intro w
      obtain ⟨x, rfl⟩ := e.surjective w
      have hx : x * (⟨t, htP⟩ : ↥P) = (⟨t, htP⟩ : ↥P) * x :=
        Subtype.ext (htz x x.2)
      show e x * u = u * e x
      calc e x * u = e x * e ⟨t, htP⟩ := by rw [hu]
        _ = e (x * ⟨t, htP⟩) := (map_mul e _ _).symm
        _ = e (⟨t, htP⟩ * x) := by rw [hx]
        _ = e ⟨t, htP⟩ * e x := map_mul e _ _
        _ = u * e x := by rw [hu]
    have hu2 : orderOf u = 2 := by
      rw [hu, MulEquiv.orderOf_eq, Subgroup.orderOf_mk, ht2]
    have hueq : u = DihedralGroup.r ((m / 2 : ℕ) : ZMod m) :=
      dihedral_center_inv_eq_r_half hmE hm0 hm2' hucent hu2
    have hQ2 : IsPGroup 2 ↥(Q.subgroupOf P) :=
      (hP2.to_le hQ).of_equiv (Subgroup.subgroupOfEquivOfLe hQ).symm
    have hQ'2 : IsPGroup 2 ((Q.subgroupOf P).map (e : ↥P →* DihedralGroup m)) :=
      hQ2.map (e : ↥P →* DihedralGroup m)
    have hQ'card : 4 ≤ Nat.card ↥((Q.subgroupOf P).map (e : ↥P →* DihedralGroup m)) := by
      have h1 : Nat.card ↥((Q.subgroupOf P).map (e : ↥P →* DihedralGroup m)) =
          Nat.card ↥(Q.subgroupOf P) :=
        Subgroup.card_map_of_injective (f := (e : ↥P →* DihedralGroup m)) e.injective
      have h2 : Nat.card ↥(Q.subgroupOf P) = Nat.card ↥Q :=
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe hQ).toEquiv
      rw [h1, h2]; exact hcard
    have hmem : u ∈ (Q.subgroupOf P).map (e : ↥P →* DihedralGroup m) := by
      rw [hueq]
      exact dihedral_r_half_mem_of_two_subgroup hmE hm0 _ hQ'2 hQ'card
    rw [Subgroup.mem_map] at hmem
    obtain ⟨y, hy, hye⟩ := hmem
    have hyu : y = ⟨t, htP⟩ := e.injective (hye.trans hu)
    have hyQ : (y : X) ∈ Q := Subgroup.mem_subgroupOf.mp hy
    rw [hyu] at hyQ
    simpa using hyQ

/-! ## 4. A non-cyclic `2`-subgroup of a group with dihedral Sylow `2`-subgroups is dihedral -/

private lemma dihedral_of_two_subgroup {G : Type} [Group G] [Finite G] (S : Sylow 2 G) (n : ℕ)
    (hn : 2 ≤ n) (hS : Nonempty ((S : Subgroup G) ≃* DihedralGroup n))
    (X : Subgroup G) (hX2 : IsPGroup 2 X) (hnc : ¬ IsCyclic ↥X) :
    ∃ m : ℕ, 2 ≤ m ∧ Even m ∧ Nonempty (↥X ≃* DihedralGroup m) := by
  rcases Work.FUS.DihedralSylow.subgroup_cyclic_or_dihedral S n hn hS X hX2 with
    hcyc | ⟨m, hm2, ⟨e⟩⟩
  · exact absurd hcyc hnc
  · obtain ⟨hEv, -⟩ :=
      Work.RED.even_dihedral_param_of_isPGroup_two_not_isCyclic e hX2 hnc
    exact ⟨m, hm2, hEv, ⟨e⟩⟩

/-! ## 5. The size hypotheses: a Sylow `2`-subgroup of `M` centralised by `t` -/

/-- `4 ∣ q` from `4 ∣ r * q` and `r` odd. -/
private lemma four_dvd_of_not_two_dvd_mul {r q : ℕ} (hr : ¬ 2 ∣ r) (h : 4 ∣ r * q) :
    4 ∣ q := by
  have hp : Nat.Prime 2 := Nat.prime_two
  have h2 : 2 ∣ q := by
    have h2' : 2 ∣ r * q := dvd_trans (by norm_num : 2 ∣ 4) h
    rcases (hp.dvd_mul).1 h2' with h3 | h3
    · exact absurd h3 hr
    · exact h3
  obtain ⟨q', hq'⟩ := h2
  have h2'' : 2 ∣ r * q' := by
    obtain ⟨c, hc⟩ := h
    rw [hq'] at hc
    have h1 : 2 * (r * q') = 2 * (2 * c) := by
      rw [show 2 * (2 * c) = 4 * c from by ring, ← hc]; ring
    exact ⟨c, Nat.mul_left_cancel (by norm_num) h1⟩
  rcases (hp.dvd_mul).1 h2'' with h3 | h3
  · exact absurd h3 hr
  · obtain ⟨q'', hq''⟩ := h3
    exact ⟨q'', by rw [hq', hq'']; ring⟩

/-- **The case `|S| = 4`**: every Sylow 2-subgroup of `M` containing `t` centralises `t`. -/
private lemma card_four_centralizes {G : Type} [Group G] [Finite G] (S : Sylow 2 G) (t : G)
    (ht : orderOf t = 2) (hcard : Nat.card (S : Subgroup G) = 4) (M : Subgroup G)
    (htM : t ∈ M) (hnc : ∀ P : Sylow 2 M, ¬ IsCyclic P) :
    ∃ P : Sylow 2 M, ∀ x ∈ (P : Subgroup M), ((x : ↥M) : G) * t = t * ((x : ↥M) : G) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hgen : IsPGroup 2 ↥(Subgroup.zpowers (⟨t, htM⟩ : ↥M)) := by
    refine IsPGroup.of_card (n := 1) ?_
    rw [Nat.card_zpowers, Subgroup.orderOf_mk, ht]
    norm_num
  obtain ⟨P, hP⟩ := hgen.exists_le_sylow
  refine ⟨P, ?_⟩
  have hPcard : Nat.card ↥(P : Subgroup M) ≤ 4 := by
    obtain ⟨Q, hQ⟩ := (P.isPGroup'.map M.subtype).exists_le_sylow
    have hQS : Nat.card ↥(Q : Subgroup G) = 4 := by
      haveI : Finite (Sylow 2 G) := inferInstance
      rw [← hcard]
      exact Nat.card_congr (Sylow.equiv Q S).toEquiv
    calc Nat.card ↥(P : Subgroup M)
        = Nat.card ↥(((P : Subgroup M)).map M.subtype) :=
          (Subgroup.card_map_of_injective M.subtype_injective).symm
      _ ≤ Nat.card ↥(Q : Subgroup G) := Subgroup.card_le_of_le hQ
      _ = 4 := hQS
  haveI hcomm : IsMulCommutative ↥(P : Subgroup M) := isMulCommutative_of_card_le_four hPcard
  intro x hx
  have htP : (⟨t, htM⟩ : ↥M) ∈ (P : Subgroup M) := hP (Subgroup.mem_zpowers (⟨t, htM⟩ : ↥M))
  have hcommP : (⟨x, hx⟩ : ↥(P : Subgroup M)) * ⟨⟨t, htM⟩, htP⟩
      = ⟨⟨t, htM⟩, htP⟩ * ⟨x, hx⟩ := mul_comm' _ _
  exact congrArg (fun y : ↥(P : Subgroup M) => ((y : ↥M) : G)) hcommP

/-- **The case `t ∈ O²(M)`**: some Sylow 2-subgroup of `M` contains `t` in its centre. -/
private theorem twoResidual_centralizes {G : Type} [Group G] [Finite G] (S : Sylow 2 G)
    (n : ℕ) (hn : 2 ≤ n) (hS : Nonempty ((S : Subgroup G) ≃* DihedralGroup n)) (t : G)
    (ht : orderOf t = 2) (htS : t ∈ (S : Subgroup G))
    (htc : ∀ x ∈ (S : Subgroup G), x * t = t * x)
    (M : Subgroup G) (htM : t ∈ M) (hnc : ∀ P : Sylow 2 M, ¬ IsCyclic P)
    (hres : t ∈ Work.GW2.twoResidualIn M) :
    ∃ P : Sylow 2 M, ∀ x ∈ (P : Subgroup M), ((x : ↥M) : G) * t = t * ((x : ↥M) : G) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_contra hcon
  have hno : ∀ P : Sylow 2 M, ¬ (∀ x ∈ (P : Subgroup M),
      ((x : ↥M) : G) * t = t * ((x : ↥M) : G)) := fun P h => hcon ⟨P, h⟩
  set t₀ : ↥M := ⟨t, htM⟩ with ht₀def
  have ht₀ord : orderOf t₀ = 2 := by rw [ht₀def, Subgroup.orderOf_mk, ht]
  have hgen : IsPGroup 2 ↥(Subgroup.zpowers t₀) := by
    refine IsPGroup.of_card (n := 1) ?_
    rw [Nat.card_zpowers, ht₀ord]
    norm_num
  obtain ⟨P₀, hP₀⟩ := hgen.exists_le_sylow
  have htP₀ : t₀ ∈ (P₀ : Subgroup M) := hP₀ (Subgroup.mem_zpowers t₀)
  have hnoM : ∀ P : Sylow 2 M, ¬ (∀ x ∈ (P : Subgroup M), x * t₀ = t₀ * x) := fun P h =>
    hno P (fun x hx => by
      have h2 := congrArg (fun y : ↥M => (y : G)) (h x hx)
      simpa using h2)
  -- the isomorphism of `P₀` with a dihedral group
  have hP₀X2 : IsPGroup 2 ((P₀ : Subgroup M).map M.subtype) := P₀.isPGroup'.map M.subtype
  have hP₀Xnc : ¬ IsCyclic ↥((P₀ : Subgroup M).map M.subtype) := by
    intro hcyc
    exact hnc P₀ ((MulEquiv.isCyclic
      (Subgroup.equivMapOfInjective (P₀ : Subgroup M) M.subtype M.subtype_injective)).mpr hcyc)
  obtain ⟨k, hk2, hkE, ⟨eX⟩⟩ :=
    dihedral_of_two_subgroup S n hn hS ((P₀ : Subgroup M).map M.subtype) hP₀X2 hP₀Xnc
  have e : ↥(P₀ : Subgroup M) ≃* DihedralGroup k :=
    (Subgroup.equivMapOfInjective (P₀ : Subgroup M) M.subtype M.subtype_injective).trans eX
  have hk0 : k ≠ 0 := by omega
  haveI : NeZero k := ⟨hk0⟩
  have hk4 : 4 ≤ k := by
    rcases Nat.lt_or_ge k 4 with hlt | hge
    · exfalso
      have hk2' : k = 2 := by
        obtain ⟨j, hj⟩ := hkE
        omega
      have hcard : Nat.card ↥(P₀ : Subgroup M) = 4 := by
        rw [Nat.card_congr e.toEquiv, DihedralGroup.nat_card, hk2']
      haveI : IsMulCommutative ↥(P₀ : Subgroup M) :=
        isMulCommutative_of_card_le_four (le_of_eq hcard)
      exact hnoM P₀ (fun x hx => by
        have h2 : (⟨x, hx⟩ : ↥(P₀ : Subgroup M)) * ⟨t₀, htP₀⟩
            = ⟨t₀, htP₀⟩ * ⟨x, hx⟩ := mul_comm' _ _
        simpa using congrArg Subtype.val h2)
    · exact hge
  set t₁ : ↥(P₀ : Subgroup M) := ⟨t₀, htP₀⟩ with ht₁def
  have ht₁ord : orderOf t₁ = 2 := by rw [ht₁def, Subgroup.orderOf_mk, ht₀ord]
  have ht₁coe : (t₁ : ↥M) = t₀ := by rw [ht₁def]
  have hcent : DihedralGroup.r ((k / 2 : ℕ) : ZMod k) ∈ Subgroup.center (DihedralGroup k) := by
    rw [DihedralGroup.center_eq_closure_of_even_ne_two hkE (by omega : k ≠ 2)]
    exact Subgroup.mem_zpowers _
  have hznc : e t₁ ∉ Subgroup.center (DihedralGroup k) := by
    intro hc
    apply hnoM P₀
    intro x hx
    have h2 : (⟨x, hx⟩ : ↥(P₀ : Subgroup M)) * t₁ = t₁ * ⟨x, hx⟩ := by
      apply e.injective
      rw [map_mul, map_mul]
      exact Subgroup.mem_center_iff.mp hc _
    exact congrArg Subtype.val h2
  have hmemrot : e t₁ ∉ Work.Dihedral.rot k := by
    intro hrot
    apply hznc
    have hord : orderOf (e t₁) = 2 := by rw [MulEquiv.orderOf_eq, ht₁ord]
    have hr2 : orderOf (DihedralGroup.r ((k / 2 : ℕ) : ZMod k) : DihedralGroup k) = 2 :=
      dihedral_orderOf_r_half hkE hk0
    haveI : IsCyclic ↥(Work.Dihedral.rot k) := rot_isCyclic k
    have hrrot : (DihedralGroup.r ((k / 2 : ℕ) : ZMod k) : DihedralGroup k) ∈
        Work.Dihedral.rot k := Work.Dihedral.r_mem_rot _
    have heq : (⟨e t₁, hrot⟩ : ↥(Work.Dihedral.rot k)) =
        ⟨DihedralGroup.r ((k / 2 : ℕ) : ZMod k), hrrot⟩ :=
      eq_of_orderOf_eq_two_of_isCyclic
        (by rw [Subgroup.orderOf_mk]; exact hord)
        (by rw [Subgroup.orderOf_mk]; exact hr2)
    have hval : e t₁ = DihedralGroup.r ((k / 2 : ℕ) : ZMod k) := congrArg Subtype.val heq
    rw [hval]
    exact hcent
  let σ : ↥(P₀ : Subgroup M) →* Multiplicative (ZMod 2) :=
    (Work.RED.dihedralSign k).comp (e : ↥(P₀ : Subgroup M) →* DihedralGroup k)
  have hσt : σ t₁ ≠ 1 := fun h => hmemrot ((Work.RED.dihedralSign_eq_one_iff).mp h)
  have hodd : Odd (P₀ : Subgroup M).index :=
    Nat.not_even_iff_odd.mp (fun h => Sylow.not_dvd_index P₀ (even_iff_two_dvd.mp h))
  have hfus : ∀ g : ↥M, ∀ (hh : g * (t₁ : ↥M) * g⁻¹ ∈ (P₀ : Subgroup M)),
      σ ⟨g * (t₁ : ↥M) * g⁻¹, hh⟩ ≠ 1 := by
    intro g hh hσ
    set u : ↥(P₀ : Subgroup M) := ⟨g * (t₁ : ↥M) * g⁻¹, hh⟩ with hudef
    have huM : (u : ↥M) = g * (t₁ : ↥M) * g⁻¹ := by rw [hudef]
    have hsemi : SemiconjBy g (t₁ : ↥M) (g * (t₁ : ↥M) * g⁻¹) := by
      show g * (t₁ : ↥M) = g * (t₁ : ↥M) * g⁻¹ * g
      group
    have huord : orderOf u = 2 := by
      rw [← Subgroup.orderOf_coe, huM]
      exact (SemiconjBy.orderOf_eq g hsemi).symm.trans
        ((Subgroup.orderOf_coe (t₁ : ↥(P₀ : Subgroup M))).trans ht₁ord)
    have hσ' : Work.RED.dihedralSign k (e u) = 1 := hσ
    have heurot : e u ∈ Work.Dihedral.rot k := (Work.RED.dihedralSign_eq_one_iff).mp hσ'
    have heuord : orderOf (e u) = 2 := by rw [MulEquiv.orderOf_eq]; exact huord
    have heq : e u = DihedralGroup.r ((k / 2 : ℕ) : ZMod k) := by
      have hr2 : orderOf (DihedralGroup.r ((k / 2 : ℕ) : ZMod k) : DihedralGroup k) = 2 :=
        dihedral_orderOf_r_half hkE hk0
      haveI : IsCyclic ↥(Work.Dihedral.rot k) := rot_isCyclic k
      have hrrot : (DihedralGroup.r ((k / 2 : ℕ) : ZMod k) : DihedralGroup k) ∈
          Work.Dihedral.rot k := Work.Dihedral.r_mem_rot _
      exact congrArg Subtype.val (eq_of_orderOf_eq_two_of_isCyclic
        (H := ↥(Work.Dihedral.rot k))
        (a := ⟨e u, heurot⟩) (b := ⟨DihedralGroup.r ((k / 2 : ℕ) : ZMod k), hrrot⟩)
        (by rw [Subgroup.orderOf_mk]; exact heuord)
        (by rw [Subgroup.orderOf_mk]; exact hr2))
    have huc : ∀ x ∈ (P₀ : Subgroup M), x * (u : ↥M) = (u : ↥M) * x := by
      intro x hx
      have h2 : (⟨x, hx⟩ : ↥(P₀ : Subgroup M)) * u = u * ⟨x, hx⟩ := by
        apply e.injective
        rw [map_mul, map_mul, heq]
        exact Subgroup.mem_center_iff.mp hcent (e ⟨x, hx⟩)
      exact congrArg Subtype.val h2
    have ht₁eq : (t₁ : ↥M) = g⁻¹ * (u : ↥M) * g := by
      rw [huM]; group
    have ht₀eq : t₀ = g⁻¹ * (u : ↥M) * g := by rw [← ht₁coe, ht₁eq]
    refine hnoM (g⁻¹ • P₀) (fun y hy => ?_)
    have hyP : g * y * g⁻¹ ∈ (P₀ : Subgroup M) := by
      have h := (Subgroup.mem_pointwise_smul_iff_inv_smul_mem
        (a := MulAut.conj g⁻¹) (S := (P₀ : Subgroup M)) (x := y)).mp hy
      rw [map_inv, inv_inv, MulAut.smul_def, MulAut.conj_apply] at h
      exact h
    have hyeq : y = g⁻¹ * (g * y * g⁻¹) * g := by group
    have hcomm := huc (g * y * g⁻¹) hyP
    rw [hyeq, ht₀eq]
    calc g⁻¹ * (g * y * g⁻¹) * g * (g⁻¹ * (u : ↥M) * g)
        = g⁻¹ * ((g * y * g⁻¹) * (u : ↥M)) * g := by group
      _ = g⁻¹ * ((u : ↥M) * (g * y * g⁻¹)) * g := by rw [hcomm]
      _ = g⁻¹ * (u : ↥M) * g * (g⁻¹ * (g * y * g⁻¹) * g) := by group
  obtain ⟨N₀, hN₀norm, hN₀idx, ht₁notmem⟩ :=
    Work.FUS.thompson_transfer (G := ↥M) (P₀ : Subgroup M) hodd σ t₁ ht₁ord hσt hfus
  haveI : N₀.Normal := hN₀norm
  have hle : Work.GW2.twoResidual ↥M ≤ N₀ := by
    rw [Work.GW2.twoResidual, Subgroup.closure_le]
    intro x hx
    have h1 : orderOf (QuotientGroup.mk' N₀ x) ∣ orderOf x := by
      rw [orderOf_dvd_iff_pow_eq_one, ← map_pow, pow_orderOf_eq_one, map_one]
    have h2 : orderOf (QuotientGroup.mk' N₀ x) ∣ 2 := by
      have h3 := orderOf_dvd_natCard (QuotientGroup.mk' N₀ x)
      rw [← Subgroup.index_eq_card, hN₀idx] at h3
      exact h3
    have h4 : orderOf (QuotientGroup.mk' N₀ x) = 1 :=
      Nat.eq_one_of_dvd_coprimes ((Nat.coprime_two_right).mpr hx) h1 h2
    rw [← QuotientGroup.ker_mk' N₀]
    exact MonoidHom.mem_ker.mpr (orderOf_eq_one_iff.mp h4)
  obtain ⟨y, hy, hyval⟩ := Subgroup.mem_map.mp hres
  have hyeq : y = t₀ := Subtype.ext hyval
  rw [hyeq] at hy
  exact ht₁notmem (by rw [ht₁coe]; exact hle hy)

/-! ## 6. From a centralising Sylow to `t ∈ N` -/

/-- **`t ∈ Z(P)` forces `t ∈ N`** for every normal `N ▷ M` with `4 ∣ |N|`. -/
private theorem normal_contains_center {G : Type} [Group G] [Finite G]
    (hCtx : Work.GW2.BenderCtx G) (B : Work.GW2.BenderSetup G) (M : Subgroup G)
    (hD : L27Hyp B M) (P : Sylow 2 M)
    (hPc : ∀ x ∈ (P : Subgroup M), ((x : ↥M) : G) * B.t = B.t * ((x : ↥M) : G))
    (N : Subgroup G) (hNM : N ≤ M) (hNnorm : (N.subgroupOf M).Normal) (h4 : 4 ∣ Nat.card N) :
    B.t ∈ N := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hncS : ¬ IsCyclic ↥(B.S : Subgroup G) := BenderCtx_sylow_not_cyclic hCtx B.S
  obtain ⟨n, hn2, hSiso⟩ : ∃ n : ℕ, 2 ≤ n ∧ Nonempty ((B.S : Subgroup G) ≃* DihedralGroup n) := by
    rcases hCtx.sylow B.S with h | h
    · exact absurd h hncS
    · obtain ⟨n, ⟨e⟩⟩ := h
      obtain ⟨hEv, hNe⟩ :=
        Work.RED.even_dihedral_param_of_isPGroup_two_not_isCyclic e B.S.isPGroup' hncS
      refine ⟨n, ?_, ⟨e⟩⟩
      have hn0 : n ≠ 0 := NeZero.ne n
      obtain ⟨k, hk⟩ := hEv
      omega
  have htM : B.t ∈ M := hD.t_mem
  have htP' : ∀ x ∈ (P : Subgroup M), x * (⟨B.t, htM⟩ : ↥M) = (⟨B.t, htM⟩ : ↥M) * x := by
    intro x hx
    exact Subtype.ext (hPc x hx)
  have ht2' : orderOf (⟨B.t, htM⟩ : ↥M) = 2 := by
    rw [Subgroup.orderOf_mk, B.t_order]
  have htP : (⟨B.t, htM⟩ : ↥M) ∈ (P : Subgroup M) :=
    mem_sylow_of_centralizes P ⟨B.t, htM⟩ ht2' htP'
  have hPX2 : IsPGroup 2 ((P : Subgroup M).map M.subtype) := P.isPGroup'.map M.subtype
  have hPXnc : ¬ IsCyclic ↥((P : Subgroup M).map M.subtype) := by
    intro hcyc
    refine hD.sylow_nc P ?_
    exact (MulEquiv.isCyclic
      (Subgroup.equivMapOfInjective (P : Subgroup M) M.subtype M.subtype_injective)).mpr hcyc
  obtain ⟨m, hm2, hmE, ⟨eX⟩⟩ :=
    dihedral_of_two_subgroup B.S n hn2 hSiso ((P : Subgroup M).map M.subtype) hPX2 hPXnc
  have e : ↥(P : Subgroup M) ≃* DihedralGroup m :=
    (Subgroup.equivMapOfInjective (P : Subgroup M) M.subtype M.subtype_injective).trans eX
  have hcardQ : 4 ≤ Nat.card ↥((P : Subgroup M) ⊓ (N.subgroupOf M)) := by
    have hinf := Work.AUTA7.GroupTheory.SylowInfNormal P (N.subgroupOf M) hNnorm
    have hrel : ((P : Subgroup M) ⊓ (N.subgroupOf M)).relIndex (N.subgroupOf M)
        * Nat.card ↥((P : Subgroup M) ⊓ (N.subgroupOf M)) = Nat.card ↥(N.subgroupOf M) := by
      have h := Subgroup.relIndex_mul_card ((P : Subgroup M) ⊓ (N.subgroupOf M))
        (N.subgroupOf M)
      rwa [inf_eq_left.mpr inf_le_right] at h
    have hcardN' : Nat.card ↥(N.subgroupOf M) = Nat.card N :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hNM).toEquiv
    have h4' : 4 ∣ Nat.card ↥(N.subgroupOf M) := by rw [hcardN']; exact h4
    have hdvd : 4 ∣ Nat.card ↥((P : Subgroup M) ⊓ (N.subgroupOf M)) := by
      have hmul : 4 ∣ ((P : Subgroup M) ⊓ (N.subgroupOf M)).relIndex (N.subgroupOf M)
          * Nat.card ↥((P : Subgroup M) ⊓ (N.subgroupOf M)) := by
        rw [hrel]; exact h4'
      exact four_dvd_of_not_two_dvd_mul hinf.2 hmul
    exact Nat.le_of_dvd Nat.card_pos hdvd
  have hmem : (⟨B.t, htM⟩ : ↥M) ∈ ((P : Subgroup M) ⊓ (N.subgroupOf M)) :=
    center_mem_of_dihedral_iso (P : Subgroup M) ((P : Subgroup M) ⊓ (N.subgroupOf M)) m hm2 hmE
      e P.isPGroup' inf_le_left hcardQ (⟨B.t, htM⟩ : ↥M) htP ht2' htP'
  exact Subgroup.mem_subgroupOf.mp hmem.2

/-! ## 7. The leaf -/

theorem L27_step1_leaf : Work.CORE2B.L27_normal_contains_t := by
  intro T h23 h26 G _ _ hFT hCtx B M hD N hNM hNnorm h4
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hncS : ¬ IsCyclic ↥(B.S : Subgroup G) := BenderCtx_sylow_not_cyclic hCtx B.S
  obtain ⟨n, hn2, hSiso⟩ : ∃ n : ℕ, 2 ≤ n ∧ Nonempty ((B.S : Subgroup G) ≃* DihedralGroup n) := by
    rcases hCtx.sylow B.S with h | h
    · exact absurd h hncS
    · obtain ⟨n, ⟨e⟩⟩ := h
      obtain ⟨hEv, hNe⟩ :=
        Work.RED.even_dihedral_param_of_isPGroup_two_not_isCyclic e B.S.isPGroup' hncS
      refine ⟨n, ?_, ⟨e⟩⟩
      have hn0 : n ≠ 0 := NeZero.ne n
      obtain ⟨k, hk⟩ := hEv
      omega
  have htc : ∀ x ∈ (B.S : Subgroup G), x * B.t = B.t * x := t_central_in_S B
  have htS : B.t ∈ (B.S : Subgroup G) := mem_sylow_of_centralizes B.S B.t B.t_order htc
  obtain ⟨P, hPc⟩ : ∃ P : Sylow 2 M, ∀ x ∈ (P : Subgroup M),
      ((x : ↥M) : G) * B.t = B.t * ((x : ↥M) : G) := by
    rcases hD.size with h8 | h4S | hres
    · exact sylow_central_of_large_inter B.S n hSiso B.t B.t_order htc M hD.t_mem hD.sylow_nc h8
    · exact card_four_centralizes B.S B.t B.t_order h4S M hD.t_mem hD.sylow_nc
    · exact twoResidual_centralizes B.S n hn2 hSiso B.t B.t_order htS htc M hD.t_mem hD.sylow_nc hres
  exact normal_contains_center hCtx B M hD P hPc N hNM hNnorm h4

end Work.CORE2B
