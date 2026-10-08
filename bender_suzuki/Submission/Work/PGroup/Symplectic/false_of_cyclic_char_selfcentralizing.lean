import Mathlib
import Submission.Work.PGroup.Omega1
import Submission.Work.PGroup.omega_one_eq_omega1
import Submission.Work.PGroup.Symplectic.pow_eq_of_conj_eq
import Submission.Work.PGroup.Symplectic.false_of_three_le_of_allAbelianCharCyclic
import Submission.Work.PGroup.Symplectic.exists_centralizer_agemo_generator
import Submission.Work.PGroup.Symplectic.structure_of_cyclic_index_p
import Submission.Work.PGroup.omega_conj
import Submission.Work.PGroup.Symplectic.centralProduct_of_structure

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option maxHeartbeats 1000000

open scoped Classical Pointwise commutatorElement
open Subgroup

namespace Work.PGroup.Symplectic

/-- `℧ⁱ(H)` is characteristic whenever `H` is: an automorphism sends `p ^ i`-th powers to
`p ^ i`-th powers. -/
theorem agemo_characteristic {G : Type*} [Group G] {p i : ℕ} {H : Subgroup G}
    (hH : H.Characteristic) : (Work.PGroup.agemo p i H).Characteristic := by
  rw [Subgroup.characteristic_iff_map_eq]
  intro φ
  change Subgroup.map φ.toMonoidHom
      (Subgroup.closure {y : G | ∃ x ∈ H, x ^ (p ^ i) = y}) =
    Subgroup.closure {y : G | ∃ x ∈ H, x ^ (p ^ i) = y}
  rw [MonoidHom.map_closure]
  apply congrArg Subgroup.closure
  ext y
  rw [Set.mem_image]
  constructor
  · rintro ⟨w, ⟨x, hx, hxw⟩, rfl⟩
    rw [Set.mem_ofPred_eq]
    refine ⟨φ x, ?_, ?_⟩
    · have hmem : φ x ∈ H.map φ.toMonoidHom := ⟨x, hx, rfl⟩
      rwa [Subgroup.characteristic_iff_map_eq.mp hH φ] at hmem
    · rw [← map_pow]
      exact congrArg φ.toMonoidHom hxw
  · intro hy
    rw [Set.mem_ofPred_eq] at hy
    obtain ⟨x, hx, hxw⟩ := hy
    have hmem : x ∈ H.map φ.toMonoidHom := by
      rw [Subgroup.characteristic_iff_map_eq.mp hH φ]; exact hx
    obtain ⟨w, hw, hwx⟩ := hmem
    exact ⟨w ^ (p ^ i), ⟨w, hw, rfl⟩, by rw [map_pow, hwx, hxw]⟩

/-- `℧¹(⟨c⟩) = ⟨c ^ p⟩`. -/
theorem agemo_zpowers_eq {G : Type*} [Group G] (c : G) (p : ℕ) :
    Work.PGroup.agemo p 1 (Subgroup.zpowers c) = Subgroup.zpowers (c ^ p) := by
  apply le_antisymm
  · rw [Work.PGroup.agemo, Subgroup.closure_le]
    rintro y ⟨x, hx, hxy⟩
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hx
    refine Subgroup.mem_zpowers_iff.mpr ⟨k, ?_⟩
    rw [← hxy, ← hk]
    simp only [pow_one]
    rw [← zpow_natCast (c ^ k) p, ← zpow_natCast c p, ← zpow_mul c k (p : ℤ),
      ← zpow_mul c (p : ℤ) k, mul_comm]
  · rw [Subgroup.zpowers_le]
    simpa using Work.PGroup.pow_mem_agemo (p := p) (i := 1)
      (P := Subgroup.zpowers c) (Subgroup.mem_zpowers c)

/-- In the configuration `y⁻¹ * c * y = c ^ (1 + m * p ^ (n-1))` with `orderOf c = p ^ n`
(`p` prime, `n ≥ 2`), the element `c ^ (p ^ (n-1))` is centralized by `y`. -/
theorem commute_pow_pred_of_conj {X : Type*} [Group X] {p n m : ℕ} (_hp : p.Prime)
    (hn : 2 ≤ n) {c y : X} (hc : orderOf c = p ^ n)
    (hconj : y⁻¹ * c * y = c ^ (1 + m * p ^ (n - 1))) :
    Commute (c ^ p ^ (n - 1)) y := by
  have hn1 : 1 ≤ n := by omega
  have hcpn : c ^ (p ^ n) = 1 := by
    have := pow_orderOf_eq_one c
    rwa [hc] at this
  set z : X := c ^ p ^ (n - 1) with hzdef
  have hyzy : y⁻¹ * z * y = z := by
    have h1 : (y⁻¹ * c * y) ^ (p ^ (n - 1)) = y⁻¹ * z * y := by
      rw [hzdef]
      simpa using (conj_pow (a := y⁻¹) (b := c) (i := p ^ (n - 1)))
    rw [← h1, hconj, hzdef, ← pow_mul]
    have hpp : p ^ (n - 1) * p ^ (n - 1) = p ^ n * p ^ (n - 2) := by
      rw [← pow_add, ← pow_add]; congr 1; omega
    have hA : (1 + m * p ^ (n - 1)) * p ^ (n - 1) =
        p ^ (n - 1) + p ^ n * (m * p ^ (n - 2)) := by
      calc (1 + m * p ^ (n - 1)) * p ^ (n - 1)
          = p ^ (n - 1) + m * (p ^ (n - 1) * p ^ (n - 1)) := by ring
        _ = p ^ (n - 1) + m * (p ^ n * p ^ (n - 2)) := by rw [hpp]
        _ = p ^ (n - 1) + p ^ n * (m * p ^ (n - 2)) := by ring
    rw [hA, pow_add, pow_mul, hcpn, one_pow, mul_one]
  show z * y = y * z
  calc z * y = y * (y⁻¹ * z * y) := by group
    _ = y * z := by rw [hyzy]

/-- If `X` is a finite nonabelian `p`-group (`p` odd) all of whose abelian characteristic
subgroups are cyclic, there is no element `c` whose cyclic subgroup is characteristic of order
`p ^ n` (`n ≥ 1`) and whose centralizer is exactly that cyclic subgroup. -/
theorem false_of_cyclic_char_selfcentralizing {X : Type*} [Group X] [Finite X] {p n : ℕ}
    (hp : p.Prime) (hodd : p ≠ 2) (hX : IsPGroup p X) (hn : 1 ≤ n)
    (hnab : ¬ IsMulCommutative X)
    (hdc : ∀ A : Subgroup X, A.Characteristic → IsMulCommutative A → ∃ a : X, A = Subgroup.zpowers a)
    {c : X} (hc : orderOf c = p ^ n) (hcchar : (Subgroup.zpowers c).Characteristic)
    (hcent : Subgroup.centralizer ((Subgroup.zpowers c : Subgroup X) : Set X) = Subgroup.zpowers c) :
    False := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  haveI hntX : Nontrivial X := by
    by_contra h
    rw [not_nontrivial_iff_subsingleton] at h
    exact hnab (IsMulCommutative.of_comm fun a b => Subsingleton.elim _ _)
  have hZle : Subgroup.center X ≤ Subgroup.zpowers c :=
    (Subgroup.center_le_centralizer _).trans (le_of_eq hcent)
  have hcyc : IsMulCommutative ↥(Subgroup.zpowers c) := by
    refine isMulCommutative_iff.mpr fun u v => Subtype.ext ?_
    obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.mp u.2
    obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp v.2
    show (u : X) * (v : X) = (v : X) * (u : X)
    rw [← hi, ← hj, ← zpow_add, ← zpow_add, add_comm]
  have hne : ∃ r : X, r ∉ Subgroup.zpowers c := by
    by_contra h
    push_neg at h
    have htop : (Subgroup.zpowers c : Subgroup X) = ⊤ := (Subgroup.eq_top_iff' _).mpr h
    exact hnab (isMulCommutative_of_subgroup_eq_top htop hcyc)
  have hn2 : 2 ≤ n := by
    by_contra hcon
    have hn1 : n = 1 := by omega
    exfalso
    have hcentnt : Nontrivial (Subgroup.center X) := IsPGroup.center_nontrivial hX
    obtain ⟨w, hw1⟩ := exists_ne (1 : Subgroup.center X)
    have hwne : (w : X) ≠ 1 := fun hh => hw1 (Subtype.ext (by simpa using hh))
    have hwmem : (w : X) ∈ Subgroup.zpowers c := hZle w.2
    have hcord : orderOf c = p := by rw [hc, hn1, pow_one]
    have hwpow : (w : X) ^ p = 1 := by
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hwmem
      have hcp : c ^ p = 1 := by rw [← hcord]; exact pow_orderOf_eq_one c
      have hkey : (c ^ k) ^ p = (c ^ p) ^ k := by
        rw [← zpow_natCast (c ^ k) p, ← zpow_natCast c p, ← zpow_mul c k (p : ℤ),
          ← zpow_mul c (p : ℤ) k, mul_comm]
      rw [← hk, hkey, hcp, one_zpow]
    have hword : orderOf (w : X) = p := orderOf_eq_prime hwpow hwne
    have hzpeq : Subgroup.zpowers (w : X) = Subgroup.zpowers c :=
      zpowers_eq_of_mem_zpowers_of_orderOf_eq_prime hp hword hcord hwmem
        (Subgroup.mem_zpowers c)
    have hcZ : c ∈ Subgroup.center X := by
      have hle : Subgroup.zpowers (w : X) ≤ Subgroup.center X :=
        Subgroup.zpowers_le.mpr w.2
      exact hle (hzpeq.symm ▸ Subgroup.mem_zpowers c)
    have hXeq : (Subgroup.zpowers c : Subgroup X) = ⊤ := by
      rw [Subgroup.eq_top_iff']
      intro x
      have hxmem : x ∈ Subgroup.centralizer ((Subgroup.zpowers c : Subgroup X) : Set X) := by
        rw [Subgroup.mem_centralizer_iff]
        intro hhh hhh'
        obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hhh'
        have hcx : Commute c x := (Subgroup.mem_center_iff.mp hcZ x).symm
        exact (hcx.zpow_left j).eq
      rwa [hcent] at hxmem
    exact hnab (isMulCommutative_of_subgroup_eq_top hXeq hcyc)
  have hnormal : ∀ r ∈ (⊤ : Subgroup X), r⁻¹ * c * r ∈ Subgroup.zpowers c := by
    intro r _
    haveI hcc : (Subgroup.zpowers c).Characteristic := hcchar
    have h := Subgroup.Normal.conj_mem (H := Subgroup.zpowers c) inferInstance c
      (Subgroup.mem_zpowers c) r⁻¹
    simpa using h
  have hCen : ∀ r ∈ (⊤ : Subgroup X), r⁻¹ * c * r = c → r ∈ Subgroup.zpowers c := by
    intro r _ hr
    rw [← hcent, Subgroup.mem_centralizer_iff]
    intro hhh hhh'
    have hcrc : Commute c r := by
      calc c * r = r * (r⁻¹ * c * r) := by group
        _ = r * c := by rw [hr]
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hhh'
    exact (hcrc.zpow_left j).eq
  have hne' : ∃ r ∈ (⊤ : Subgroup X), r ∉ Subgroup.zpowers c :=
    hne.imp (fun r hr => ⟨trivial, hr⟩)
  obtain ⟨y, hyR, hyK, hyp, huy, hym⟩ :=
    exists_centralizer_agemo_generator hp hodd (⊤ : Subgroup X) (hX.to_subgroup ⊤)
      (c := c) trivial hn2 hc hnormal hCen hne'
  obtain ⟨m, hym'⟩ := hym
  set z0 : X := c ^ (p ^ (n - 1)) with hz0def
  have hpnn : p ^ (n - 1) * p = p ^ n := by rw [← pow_succ, Nat.sub_add_cancel hn]
  have hz0pow : z0 ^ p = 1 := by
    rw [hz0def, ← pow_mul, hpnn, ← hc]
    exact pow_orderOf_eq_one c
  have hz0ne : z0 ≠ 1 := by
    intro h1
    rw [hz0def] at h1
    have hd : p ^ n ∣ p ^ (n - 1) := by
      rw [← hc, orderOf_dvd_iff_pow_eq_one]; exact h1
    have hlt : p ^ (n - 1) < p ^ n := Nat.pow_lt_pow_right hp.one_lt (by omega)
    exact absurd (Nat.le_of_dvd (pow_pos hp.pos _) hd) (not_le.mpr hlt)
  have hz0ord : orderOf z0 = p := orderOf_eq_prime hz0pow hz0ne
  set P1 : Subgroup X := Subgroup.zpowers (c ^ p) with hP1def
  have hP1char : P1.Characteristic := by
    rw [hP1def, ← agemo_zpowers_eq c p]
    exact agemo_characteristic (p := p) (i := 1) hcchar
  set D : Subgroup X := Subgroup.centralizer (P1 : Set X) with hDdef
  have hDchar : D.Characteristic := by
    haveI : P1.Characteristic := hP1char
    rw [hDdef]
    exact Subgroup.characteristic_centralizer
  set A : Subgroup X := Work.PGroup.omega1 X p D with hAdef
  have hAchar : A.Characteristic := by
    rw [hAdef]
    exact Work.PGroup.omega1_characteristic p hDchar
  have hDmem : ∀ u : X, u ∈ D ↔ u⁻¹ * c ^ p * u = c ^ p := by
    intro u
    rw [hDdef, hP1def, Subgroup.mem_centralizer_iff]
    constructor
    · intro hu
      have h' := hu (c ^ p) (Subgroup.mem_zpowers (c ^ p))
      calc u⁻¹ * c ^ p * u = u⁻¹ * (c ^ p * u) := by group
        _ = u⁻¹ * (u * c ^ p) := by rw [h']
        _ = c ^ p := by group
    · intro hu hhh hhh'
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hhh'
      have hcr : Commute (c ^ p) u := by
        calc c ^ p * u = u * (u⁻¹ * c ^ p * u) := by group
          _ = u * c ^ p := by rw [hu]
      exact (hcr.zpow_left k).eq
  have hz0mem : z0 ∈ Subgroup.zpowers c := by
    rw [hz0def]
    exact Subgroup.pow_mem (Subgroup.zpowers c) (Subgroup.mem_zpowers c) (p ^ (n - 1))
  have hz0D : z0 ∈ D := by
    rw [hDmem]
    have hcomm : Commute z0 (c ^ p) := by
      rw [hz0def]
      exact ((Commute.refl c).pow_left (p ^ (n - 1))).pow_right p
    calc z0⁻¹ * c ^ p * z0 = z0⁻¹ * (c ^ p * z0) := by group
      _ = z0⁻¹ * (z0 * c ^ p) := by rw [hcomm.eq]
      _ = c ^ p := by group
  have hz0A : z0 ∈ A := by
    rw [hAdef]
    exact Work.PGroup.omega1_subset p hz0D hz0pow
  have hyD : y ∈ D := by
    rw [hDmem]
    have hconjp : y⁻¹ * c ^ p * y = (y⁻¹ * c * y) ^ p := by
      simpa using (conj_pow (a := y⁻¹) (b := c) (i := p)).symm
    rw [hconjp, hym', ← pow_mul]
    have he : (1 + m * p ^ (n - 1)) * p = p + m * p ^ n := by
      rw [add_mul, one_mul, mul_assoc, hpnn]
    rw [he, pow_add,
      show c ^ (m * p ^ n) = 1 by
        rw [mul_comm m (p^n), pow_mul, ← hc, pow_orderOf_eq_one, one_pow],
      mul_one]
  have hyA : y ∈ A := by
    rw [hAdef]
    exact Work.PGroup.omega1_subset p hyD hyp
  have hA_le : A ≤ Subgroup.zpowers z0 ⊔ Subgroup.zpowers y := by
    rw [hAdef, Work.PGroup.omega1, Subgroup.closure_le]
    rintro x ⟨hxD, hxp⟩
    have hxD' : x⁻¹ * c ^ p * x = c ^ p := (hDmem x).mp hxD
    obtain ⟨i, j, hxy⟩ := huy x trivial hxD'
    rw [hxy]
    have hyjp : y ^ (j * p) = 1 := by rw [mul_comm, pow_mul, hyp, one_pow]
    have hcpow : c ^ (i * p) = 1 := by
      have h := pow_eq_of_conj_eq hp hodd hn2 hc hym' i j
      rw [← hxy, hxp, hyjp, mul_one] at h
      exact h.symm
    have hdvd : p ^ (n - 1) ∣ i := by
      have h1 : p ^ n ∣ i * p := by
        rw [← hc, orderOf_dvd_iff_pow_eq_one]; exact hcpow
      rw [← hpnn] at h1
      exact (Nat.mul_dvd_mul_iff_right hp.pos).mp h1
    have hci : c ^ i ∈ Subgroup.zpowers z0 := by
      obtain ⟨t, ht⟩ := hdvd
      rw [ht, pow_mul, ← hz0def]
      exact Subgroup.pow_mem (Subgroup.zpowers z0) (Subgroup.mem_zpowers z0) t
    exact Subgroup.mul_mem_sup hci
      (Subgroup.pow_mem (Subgroup.zpowers y) (Subgroup.mem_zpowers y) j)
  have hsup_le : Subgroup.zpowers z0 ⊔ Subgroup.zpowers y ≤ A := by
    apply sup_le
    · rw [Subgroup.zpowers_le]; exact hz0A
    · rw [Subgroup.zpowers_le]; exact hyA
  have hAeq : A = Subgroup.zpowers z0 ⊔ Subgroup.zpowers y := le_antisymm hA_le hsup_le
  have hzy : z0 * y = y * z0 := commute_pow_pred_of_conj hp hn2 hc hym'
  have hAabel : IsMulCommutative A := by
    rw [hAeq]
    exact isMulCommutative_of_commute_zpowers_sup hzy
  obtain ⟨a, ha⟩ := hdc A hAchar hAabel
  have hz0a : z0 ∈ Subgroup.zpowers a := ha ▸ hz0A
  have hya : y ∈ Subgroup.zpowers a := ha ▸ hyA
  have hyne : y ≠ 1 := fun h1 => hyK (h1 ▸ Subgroup.one_mem _)
  have hyord : orderOf y = p := orderOf_eq_prime hyp hyne
  have hzpeq := zpowers_eq_of_mem_zpowers_of_orderOf_eq_prime hp hyord hz0ord hya hz0a
  have hz0lec : Subgroup.zpowers z0 ≤ Subgroup.zpowers c := Subgroup.zpowers_le.mpr hz0mem
  exact hyK (hz0lec (hzpeq ▸ Subgroup.mem_zpowers y))

end Work.PGroup.Symplectic
