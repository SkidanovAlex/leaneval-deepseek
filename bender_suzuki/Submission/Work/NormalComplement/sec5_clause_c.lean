import Mathlib
import Submission.Work.NormalComplement.Design.Extra
import Submission.Work.NormalComplement.Sections
import Submission.Work.NormalComplement.p3Normal_of_chIIFourP3Subnormal
import Submission.Work.NormalComplement.appI_five_b
import Submission.Work.NormalComplement.appIII
import Submission.Work.NormalComplement.appI_one
import Submission.Work.NormalComplement.sec4_one_c
import Submission.Work.NormalComplement.sec5c_kappa
import Submission.Work.ThmF.Bender.cardKsetEqInv
import Submission.Work.ThreePoints.Basic
import Submission.Work.ThreePoints.sec4_prop3_cd_ne_bot

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option autoImplicit false
set_option maxHeartbeats 800000

open Classical
open scoped Pointwise commutatorElement
open LeanEval.GroupTheory.Defs
open Submission.Blueprint

namespace Work.NormalComplement

variable {G : Type} [Group G] [Finite G]

/-! ## §5 Prop. 2 (c): the algebraic core

For involutions `u`, `t` and `M` the subgroup with underlying set
`Mset u t = {x ∈ C_G(u*t) | t x t⁻¹ = x⁻¹}`, we record

* `mset_abelian` — `M` is abelian (the source's "`M` is an abelian group");
* `mset_eq_invertedBy_u` — on `C_G(ut)` the elements inverted by `t` are exactly those inverted
  by `u`;
* `mset_normalizer_of_kappa` — the reduction of §5 Prop. 2 (c) to the existence of a subgroup
  `κ ⊆ M` containing `ut` and normalised by `H ⊓ N_G(P)` (with `H ⊓ N_G(P)` centralising `u`). -/

/-- **`M = Mset u t` is abelian.**  For `x, y ∈ M` one has `t (x*y) t⁻¹ = x⁻¹ y⁻¹` while
`x*y ∈ M` forces `t (x*y) t⁻¹ = (x*y)⁻¹`; so `(y*x)⁻¹ = (x*y)⁻¹`. -/
theorem mset_abelian {u t : G} (M : Subgroup G) (hM : (M : Set G) = Design.Mset u t) :
    ∀ x ∈ M, ∀ y ∈ M, x * y = y * x := by
  intro x hx y hy
  have hxM : x ∈ Design.Mset u t := hM ▸ hx
  have hyM : y ∈ Design.Mset u t := hM ▸ hy
  have hxyM : x * y ∈ Design.Mset u t := hM ▸ M.mul_mem hx hy
  have h2 : t * (x * y) * t⁻¹ = x⁻¹ * y⁻¹ := by
    calc t * (x * y) * t⁻¹ = (t * x * t⁻¹) * (t * y * t⁻¹) := by group
      _ = x⁻¹ * y⁻¹ := by rw [hxM.2, hyM.2]
  have h3 : (x * y)⁻¹ = (y * x)⁻¹ := by
    rw [← hxyM.2, h2]; group
  exact inv_injective h3

/-- **Inversion by `t` versus by `u` on `C_G(ut)`.**  With `u`, `t` involutions, the elements of
`C_G(u*t)` inverted by `t` are exactly the elements inverted by `u`: `t = u·(u*t)`, `u = (u*t)·t`
and `u*t` commutes with `x`. -/
theorem mset_eq_invertedBy_u {u t : G} (ht : orderOf t = 2) (hu : orderOf u = 2) :
    Design.Mset u t =
      {x : G | x ∈ Subgroup.centralizer ({u * t} : Set G) ∧ u * x * u⁻¹ = x⁻¹} := by
  have ht2 : t * t = 1 := by
    have h := pow_orderOf_eq_one t; rw [ht] at h; simpa [pow_two] using h
  have hu2 : u * u = 1 := by
    have h := pow_orderOf_eq_one u; rw [hu] at h; simpa [pow_two] using h
  ext x
  simp only [Design.Mset, Set.mem_setOf_eq, Subgroup.mem_centralizer_singleton_iff]
  constructor
  · rintro ⟨hcomm, hxt⟩
    refine ⟨hcomm, ?_⟩
    have hu_eq : u = (u * t) * t := by rw [mul_assoc, ht2, mul_one]
    have hwx : (u * t) * x * (u * t)⁻¹ = x := by rw [← hcomm]; group
    have hwx' : (u * t) * x⁻¹ * (u * t)⁻¹ = x⁻¹ := by
      rw [show (u * t) * x⁻¹ * (u * t)⁻¹ = ((u * t) * x * (u * t)⁻¹)⁻¹ from by group, hwx]
    calc u * x * u⁻¹ = ((u * t) * t) * x * ((u * t) * t)⁻¹ := by rw [← hu_eq]
      _ = (u * t) * (t * x * t⁻¹) * (u * t)⁻¹ := by rw [mul_inv_rev]; group
      _ = (u * t) * x⁻¹ * (u * t)⁻¹ := by rw [hxt]
      _ = x⁻¹ := hwx'
  · rintro ⟨hcomm, hxu⟩
    refine ⟨hcomm, ?_⟩
    have ht_eq : t = u * (u * t) := by rw [← mul_assoc, hu2, one_mul]
    have hwx : (u * t) * x * (u * t)⁻¹ = x := by rw [← hcomm]; group
    calc t * x * t⁻¹ = (u * (u * t)) * x * (u * (u * t))⁻¹ := by rw [← ht_eq]
      _ = u * ((u * t) * x * (u * t)⁻¹) * u⁻¹ := by rw [mul_inv_rev]; group
      _ = u * x * u⁻¹ := by rw [hwx]
      _ = x⁻¹ := hxu

/-- **The reduction step of §5 Prop. 2 (c).**  Let `M` have underlying set `Mset u t` and let
`κ ⊆ M` be a subgroup with `ut ∈ κ`, normalised by `M₀ := H ⊓ N_G(P)`, which we also assume to
centralise `u`.  Then `M₀ ≤ N_G(M)`.

Indeed, by `mset_eq_invertedBy_u` and `mset_abelian`,
`M = {x | x ∈ C_G(κ) ∧ u x u⁻¹ = x⁻¹}`: `⊆` since `κ ⊆ M` and `M` is abelian; `⊇` since `x`
commutes with `ut ∈ κ`.  This description is preserved by conjugation by `n ∈ M₀` (which
normalises `κ` and centralises `u`). -/
theorem mset_normalizer_of_kappa {u t : G} (ht : orderOf t = 2) (hu : orderOf u = 2)
    {H P : Subgroup G} {M κ : Subgroup G} (hM : (M : Set G) = Design.Mset u t)
    (hκM : (κ : Set G) ⊆ Design.Mset u t) (hut : u * t ∈ κ)
    (hκab : ∀ x ∈ κ, ∀ y ∈ M, x * y = y * x)
    (hcentu : ∀ n ∈ H ⊓ Subgroup.normalizer (P : Set G), u * n = n * u)
    (hκnorm : H ⊓ Subgroup.normalizer (P : Set G) ≤ Subgroup.normalizer (κ : Set G)) :
    H ⊓ Subgroup.normalizer (P : Set G) ≤ Subgroup.normalizer (M : Set G) := by
  have hMab : ∀ x ∈ M, ∀ y ∈ M, x * y = y * x := mset_abelian M hM
  have hequiv := mset_eq_invertedBy_u (u := u) (t := t) ht hu
  have hmemM : ∀ x : G, x ∈ M ↔ x ∈ Design.Mset u t :=
    fun x => ⟨fun h => hM ▸ h, fun h => by show x ∈ (M : Set G); rw [hM]; exact h⟩
  -- ## the description of `M` in terms of `κ` and `u`
  have hMset : (M : Set G) =
      {x : G | x ∈ Subgroup.centralizer (κ : Set G) ∧ u * x * u⁻¹ = x⁻¹} := by
    ext x
    constructor
    · intro hx
      refine ⟨?_, ?_⟩
      · rw [Subgroup.mem_centralizer_iff]
        intro y hy
        exact (hMab x hx y ((hmemM y).mpr (hκM hy))).symm
      · exact (hequiv ▸ (hmemM x).mp hx).2
    · rintro ⟨hxc, hxu⟩
      refine (hmemM x).mpr ?_
      rw [hequiv]
      refine ⟨?_, hxu⟩
      rw [Subgroup.mem_centralizer_iff] at hxc
      exact Subgroup.mem_centralizer_singleton_iff.mpr (hxc (u * t) hut).symm
  -- ## conjugation by `n ∈ M₀` preserves this description
  intro n hn
  rw [Subgroup.mem_normalizer_iff]
  intro x
  show x ∈ (M : Set G) ↔ n * x * n⁻¹ ∈ (M : Set G)
  rw [hMset]
  constructor
  · rintro ⟨hxc, hxu⟩
    rw [Subgroup.mem_centralizer_iff] at hxc
    refine ⟨?_, ?_⟩
    · rw [Subgroup.mem_centralizer_iff]
      intro z hz
      have hz' : n⁻¹ * z * n ∈ κ := (Subgroup.mem_normalizer_iff''.mp (hκnorm hn) z).mp hz
      have h1 : (n⁻¹ * z * n) * x = x * (n⁻¹ * z * n) := hxc _ hz'
      calc z * (n * x * n⁻¹) = n * ((n⁻¹ * z * n) * x) * n⁻¹ := by group
        _ = n * (x * (n⁻¹ * z * n)) * n⁻¹ := by rw [h1]
        _ = (n * x * n⁻¹) * z := by group
    · have hun : u * n = n * u := hcentu n hn
      have hc : Commute u n := hun
      have hun' : u⁻¹ * n⁻¹ = n⁻¹ * u⁻¹ := (hc.inv_inv).eq
      have h4 : u * (n * x * n⁻¹) * u⁻¹ = n * (u * x * u⁻¹) * n⁻¹ := by
        calc u * (n * x * n⁻¹) * u⁻¹ = u * n * x * (n⁻¹ * u⁻¹) := by group
          _ = n * u * x * (u⁻¹ * n⁻¹) := by rw [hun, hun']
          _ = n * (u * x * u⁻¹) * n⁻¹ := by group
      rw [h4, hxu]
      group
  · rintro ⟨hxc, hxu⟩
    rw [Subgroup.mem_centralizer_iff] at hxc
    have hun : u * n = n * u := hcentu n hn
    refine ⟨?_, ?_⟩
    · rw [Subgroup.mem_centralizer_iff]
      intro z hz
      have hz' : n * z * n⁻¹ ∈ κ := (Subgroup.mem_normalizer_iff.mp (hκnorm hn) z).mp hz
      have h1 : (n * z * n⁻¹) * (n * x * n⁻¹) = (n * x * n⁻¹) * (n * z * n⁻¹) := hxc _ hz'
      have h1' : n * (z * x) * n⁻¹ = n * (x * z) * n⁻¹ := by
        rw [show n * (z * x) * n⁻¹ = (n * z * n⁻¹) * (n * x * n⁻¹) from by group,
          show n * (x * z) * n⁻¹ = (n * x * n⁻¹) * (n * z * n⁻¹) from by group, h1]
      have h2 : z * x = x * z := by
        have := congrArg (fun w => n⁻¹ * w * n) h1'
        simpa using this
      exact h2
    · have hc : Commute u n := hun
      have h2 : n⁻¹ * u * n = u := by
        calc n⁻¹ * u * n = n⁻¹ * (u * n) := by rw [mul_assoc]
          _ = n⁻¹ * (n * u) := by rw [hun]
          _ = u := by group
      have h3 : n⁻¹ * u⁻¹ * n = u⁻¹ := by
        calc n⁻¹ * u⁻¹ * n = n⁻¹ * (u⁻¹ * n) := by rw [mul_assoc]
          _ = n⁻¹ * (n * u⁻¹) := by rw [(hc.inv_left).eq]
          _ = u⁻¹ := by group
      have h4 : u * x * u⁻¹ = n⁻¹ * (u * (n * x * n⁻¹) * u⁻¹) * n := by
        calc u * x * u⁻¹ = (n⁻¹ * u * n) * x * (n⁻¹ * u⁻¹ * n) := by rw [h2, h3]
          _ = n⁻¹ * (u * (n * x * n⁻¹) * u⁻¹) * n := by group
      rw [h4, hxu]
      group


/-! ## §5 Prop. 2 (c): `N_H(P)` has the unique involution `u`

Every involution of `M₀ := H ⊓ N_G(P)` is `u` (the involution of `C_H(V)`), so `M₀ ≤ C_G(u)`.
The proof copies that of `Work.NormalComplement.Sec5Fix.prop2c_inv_involutions_normalizer`:
`M₀` is strongly embedded in `M := N_G(P)` (Ch. II §4 Prop. 1 (b) with `X = P`), the `J`-set
`Kset (M₀.subgroupOf M) t` inside `M` is trivial (its elements lie in `D ⊓ N_G(P) = N_D(P) ≤ V`
by `sec4_one_c`, and `V ∩ Mset = 1`), and Ch. I §2 Prop. 2 (b) (`cardKsetEqInv`) identifies
`|Kset|` with the number of involutions of `M₀`. -/

section InvolutionOfNH

variable {H : Subgroup G} {t : G} {W : Subgroup G} {p : ℕ} {P A : Subgroup G} {r : ℕ}

/-- `p ≠ 2`: `p ∣ |E : E'|` divides `|E|`, which divides the odd number `|D|`. -/
lemma sec5c_Egrp_odd (h : Design.Setup5 G H t W p P A r) :
    Odd (Nat.card ↥(Design.Egrp H t W)) :=
  Odd.of_dvd_nat (h.se.2.2 t h.notMem) (Subgroup.card_dvd_of_le inf_le_right)

lemma sec5c_p_ne_two (h : Design.Setup5 G H t W p P A r) : p ≠ 2 := by
  intro hp
  have hdvd : p ∣ Nat.card ↥(Design.Egrp H t W) :=
    h.dvd.trans (Subgroup.relIndex_dvd_card _ _)
  have h2 : 2 ∣ Nat.card ↥(Design.Egrp H t W) := hp ▸ hdvd
  exact (Nat.not_even_iff_odd.mpr (sec5c_Egrp_odd h)) (even_iff_two_dvd.mpr h2)

/-- `orderOf` is invariant under conjugation. -/
lemma sec5c_orderOf_conj_eq (g x : G) : orderOf (MulAut.conj g x) = orderOf x := by
  refine Nat.dvd_antisymm (orderOf_map_dvd (MulAut.conj g).toMonoidHom x) ?_
  have h := orderOf_map_dvd (MulAut.conj g⁻¹).toMonoidHom (MulAut.conj g x)
  have hx : (MulAut.conj g⁻¹).toMonoidHom (MulAut.conj g x) = x := by
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    group
  rw [hx] at h
  exact h

/-- `t` commutes with every element of `P`: `P ≤ centD H t ≤ C_G(t)`. -/
lemma sec5c_commute_t_of_mem_P (h : Design.Setup5 G H t W p P A r) {x : G} (hx : x ∈ P) :
    t * x * t⁻¹ = x := by
  have hxV : x ∈ Submission.Blueprint.centD H t := (h.P_le hx).2
  have hxct : x ∈ Subgroup.centralizer ({t} : Set G) := hxV.2
  rw [Subgroup.mem_centralizer_singleton_iff] at hxct
  rw [← hxct]
  group

/-- `u` commutes with every element of `P`: `P ≤ centD H t ≤ C_G(u)`. -/
lemma sec5c_commute_u_of_mem_P (h : Design.Setup5 G H t W p P A r) {u : G}
    (hu : u ∈ H ∧ orderOf u = 2 ∧
      u ∈ Subgroup.centralizer (Submission.Blueprint.centD H t : Set G)) {x : G}
    (hx : x ∈ P) : u * x * u⁻¹ = x := by
  have hxV : x ∈ Submission.Blueprint.centD H t := (h.P_le hx).2
  have hux : x * u = u * x := (Subgroup.mem_centralizer_iff.mp hu.2.2) x hxV
  rw [← hux]
  group

/-- `t` lies in `N_G(P)`. -/
lemma sec5c_mem_normalizer_t (h : Design.Setup5 G H t W p P A r) :
    t ∈ Subgroup.normalizer (P : Set G) := by
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  refine le_antisymm ?_ ?_
  · rintro y ⟨x, hx, hxy⟩
    rw [← hxy]
    change t * x * t⁻¹ ∈ P
    rw [sec5c_commute_t_of_mem_P h hx]
    exact hx
  · intro y hy
    exact ⟨y, hy, by simp [MulAut.conj_apply, sec5c_commute_t_of_mem_P h hy]⟩

/-- `u` lies in `N_G(P)`. -/
lemma sec5c_mem_normalizer_u (h : Design.Setup5 G H t W p P A r) {u : G}
    (hu : u ∈ H ∧ orderOf u = 2 ∧
      u ∈ Subgroup.centralizer (Submission.Blueprint.centD H t : Set G)) :
    u ∈ Subgroup.normalizer (P : Set G) := by
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  refine le_antisymm ?_ ?_
  · rintro y ⟨x, hx, hxy⟩
    rw [← hxy]
    change u * x * u⁻¹ ∈ P
    rw [sec5c_commute_u_of_mem_P h hu hx]
    exact hx
  · intro y hy
    exact ⟨y, hy, by simp [MulAut.conj_apply, sec5c_commute_u_of_mem_P h hu hy]⟩

/-- Every element of `(A ⊓ C_G(P)) ⊔ P` of order dividing `2` is `1`: the group
`C_A(P) · P = C_A(P) × P` has odd order (`A ⊓ P = ⊥`). -/
lemma sec5c_eq_one_of_mem_sup_of_sq_eq_one (h : Design.Setup5 G H t W p P A r) {x : G}
    (hx : x ∈ (((A ⊓ Subgroup.centralizer (P : Set G)) ⊔ P : Subgroup G) : Set G))
    (hx2 : x * x = 1) : x = 1 := by
  classical
  set C : Subgroup G := A ⊓ Subgroup.centralizer (P : Set G) with hC
  have hCnorm : C ≤ Subgroup.normalizer (P : Set G) :=
    le_trans inf_le_right (Subgroup.centralizer_le_normalizer (P : Set G))
  have hprod : ((P : Set G) * (C : Set G)) = (((C ⊔ P : Subgroup G)) : Set G) := by
    rw [sup_comm]
    exact (Subgroup.coe_mul_of_right_le_normalizer_left P C hCnorm).symm
  have hx' : x ∈ (P : Set G) * (C : Set G) := by
    rw [hprod]; exact hx
  obtain ⟨q, hqP, a, haC, hqa⟩ := Set.mem_mul.mp hx'
  have haA : a ∈ A := (Subgroup.mem_inf.mp (hC ▸ haC)).1
  have haC : a ∈ Subgroup.centralizer (P : Set G) := (Subgroup.mem_inf.mp (hC ▸ haC)).2
  have hcomm : a * q = q * a := ((Subgroup.mem_centralizer_iff.mp haC) q hqP).symm
  have hsq : q * q * (a * a) = 1 := by
    have h6 : (q * a) * (q * a) = 1 := by rw [hqa]; exact hx2
    rw [show q * a * (q * a) = q * q * (a * a) from by
      rw [mul_assoc, ← mul_assoc a q a, hcomm]; group] at h6
    exact h6
  have hkey : q * q = (a * a)⁻¹ := mul_eq_one_iff_eq_inv.mp hsq
  have haaA : a * a ∈ A := A.mul_mem haA haA
  have hqqA : q * q ∈ A := by rw [hkey]; exact A.inv_mem haaA
  have hqqP : q * q ∈ P := P.mul_mem hqP hqP
  have hqq1 : q * q = 1 := by
    have h7 : q * q ∈ A ⊓ P := ⟨hqqA, hqqP⟩
    rw [h.A_inf] at h7
    simpa using h7
  have haa1 : a * a = 1 := by
    have h8 := hkey
    rw [hqq1] at h8
    exact inv_eq_one.mp h8.symm
  have hq1 : q = 1 := by
    have h1 : orderOf q ∣ 2 := orderOf_dvd_iff_pow_eq_one.mpr (by rwa [pow_two])
    have h2 : orderOf q ∣ Nat.card P := Subgroup.orderOf_dvd_natCard P hqP
    rw [h.P_card] at h2
    have hcop : Nat.Coprime 2 p :=
      Nat.coprime_two_left.mpr (h.prime.odd_of_ne_two (sec5c_p_ne_two h))
    have h3 : orderOf q ∣ 1 := by
      have := Nat.dvd_gcd h1 h2
      rwa [show Nat.gcd 2 p = 1 from hcop] at this
    exact orderOf_eq_one_iff.mp (Nat.dvd_one.mp h3)
  have ha1 : a = 1 := by
    have h1 : orderOf a ∣ 2 := orderOf_dvd_iff_pow_eq_one.mpr (by rwa [pow_two])
    have haT : a ∈ Submission.Blueprint.twoPoint H t :=
      (inf_le_left : Submission.Blueprint.centD H t ≤ Submission.Blueprint.twoPoint H t)
        (h.A_le haA)
    have h2 : orderOf a ∣ Nat.card ↥(Submission.Blueprint.twoPoint H t) :=
      Subgroup.orderOf_dvd_natCard _ haT
    have hodd : Odd (Nat.card ↥(Submission.Blueprint.twoPoint H t)) := h.se.2.2 t h.notMem
    have hgcd : Nat.gcd 2 (Nat.card ↥(Submission.Blueprint.twoPoint H t)) = 1 :=
      Nat.coprime_two_left.mpr hodd
    have h3 : orderOf a ∣ 1 := by
      have := Nat.dvd_gcd h1 h2
      rwa [hgcd] at this
    exact orderOf_eq_one_iff.mp (Nat.dvd_one.mp h3)
  rw [← hqa, hq1, ha1, one_mul]


/-- The involutions of `N_H(P) = H ⊓ N_G(P)` are exactly `u`; in particular `N_H(P) ≤ C_G(u)`. -/
theorem sec5c_inv_unique
    (hFT : Submission.Blueprint.FeitThompsonProp)
    (hC4 : Submission.Blueprint.ChIIFourProp)
    (h : Design.Setup5 G H t W p P A r) (u : G)
    (hu : u ∈ H ∧ orderOf u = 2 ∧
      u ∈ Subgroup.centralizer (Submission.Blueprint.centD H t : Set G)) :
    ∀ z ∈ H ⊓ Subgroup.normalizer (P : Set G), orderOf z = 2 → z = u := by
  classical
  set 𝒢 : Subgroup G := Subgroup.normalizer (P : Set G) with h𝒢
  set H₁ : Subgroup G := H ⊓ 𝒢 with hH₁
  have ht𝒢 : t ∈ 𝒢 := sec5c_mem_normalizer_t h
  have hu𝒢 : u ∈ 𝒢 := sec5c_mem_normalizer_u h hu
  have huH₁ : u ∈ H₁ := ⟨hu.1, hu𝒢⟩
  have ht2 : t * t = 1 := by
    have h' := pow_orderOf_eq_one t
    rw [h.invol] at h'
    simpa [pow_two] using h'
  -- ## `N_H(P)` is strongly embedded in `N_G(P)`
  obtain ⟨hP1b, -⟩ := hC4 G h.sit H h.se t h.invol h.notMem
  have hPleV : P ≤ Submission.Blueprint.centD H t := h.P_le.trans inf_le_right
  have hPleH : P ≤ H := hPleV.trans (inf_le_left.trans inf_le_left)
  have h3 : 3 ≤ (fixedPts H P).ncard := by
    have h3' : 3 ≤ (fixedPts H (Submission.Blueprint.centD H t)).ncard :=
      Work.ThreePoints.three_le_fixedPts_of_le_centD h.se h.invol h.notMem le_rfl
    exact le_trans h3'
      (Set.ncard_le_ncard (Work.ThreePoints.fixedPts_mono hPleV) (Set.toFinite _))
  have hinv : Submission.Blueprint.involutions
      (Subgroup.centralizer (P : Set G) : Set G) ⊆ 𝒢 := by
    intro x hx
    rw [Work.ThreePoints.mem_involutions] at hx
    exact Subgroup.centralizer_le_normalizer _ hx.1
  have hse : LeanEval.GroupTheory.Defs.IsStronglyEmbedded (H₁.subgroupOf 𝒢) := by
    have h1 := hP1b P 𝒢 h3 hinv (by rw [h𝒢]) (1 : G)
      (by rw [Work.DoubleTransitivity.conj_one]; exact hPleH)
    rw [Work.DoubleTransitivity.conj_one] at h1
    simpa [hH₁, h𝒢, inf_comm] using h1
  -- ## the `J`-set of the pair `(N_H(P), t)` inside `N_G(P)` is trivial
  have hDK : (Work.ThmF.Kset (H₁.subgroupOf 𝒢) (⟨t, ht𝒢⟩ : ↥𝒢)).ncard = 1 := by
    rw [Set.ncard_eq_one]
    refine ⟨1, Set.eq_singleton_iff_unique_mem.mpr ⟨?_, ?_⟩⟩
    · unfold Work.ThmF.Kset
      rw [Work.ThreePoints.mem_invertedBy]
      exact ⟨Subgroup.one_mem _, by simp⟩
    · intro x hx
      unfold Work.ThmF.Kset at hx
      rw [Work.ThreePoints.mem_invertedBy] at hx
      obtain ⟨hx1, hx2⟩ := hx
      obtain ⟨hxH1, hxH2⟩ := Subgroup.mem_inf.mp hx1
      have hxH₁ : (x : G) ∈ H₁ := Subgroup.mem_subgroupOf.mp hxH1
      have hxG : (x : G) ∈ 𝒢 := hxH₁.2
      have h2 : t * (x : G) * t⁻¹ = (x : G)⁻¹ := by
        have h4 := congrArg (fun y : ↥𝒢 => (y : G)) hx2
        simpa using h4
      have hxconj : (x : G) ∈ Submission.Blueprint.conj t H := by
        rw [Work.ThreePoints.mem_conj_iff]
        have h3' : (↑(⟨t, ht𝒢⟩⁻¹ * x * ⟨t, ht𝒢⟩) : G) ∈ H₁ :=
          Subgroup.mem_subgroupOf.mp ((Work.ThreePoints.mem_conj_iff).mp hxH2)
        have h1 : H₁ ≤ H := by rw [hH₁]; exact inf_le_left
        exact h1 (by simpa using h3')
      have hxD : (x : G) ∈ Submission.Blueprint.twoPoint H t := ⟨hxH₁.1, hxconj⟩
      have hxAP : (x : G) ∈ (((A ⊓ Subgroup.centralizer (P : Set G)) ⊔ P : Subgroup G) : Set G) := by
        rw [← (Work.NormalComplement.sec4_one_c hFT h.toSetup45A).1]
        exact ⟨hxD, hxG⟩
      have hx2' : (x : G) * (x : G) = 1 := by
        have hxct : (x : G) ∈ Subgroup.centralizer ({t} : Set G) := by
          have hle1 : (A ⊓ Subgroup.centralizer (P : Set G) : Subgroup G) ≤
              Subgroup.centralizer ({t} : Set G) := by
            refine le_trans inf_le_left ?_
            intro y hy
            exact (Subgroup.mem_inf.mp (h.A_le hy)).2
          have hsup : ((A ⊓ Subgroup.centralizer (P : Set G)) ⊔ P : Subgroup G) ≤
              Subgroup.centralizer ({t} : Set G) := by
            refine sup_le hle1 ?_
            intro y hy
            rw [Subgroup.mem_centralizer_singleton_iff]
            have hyc := sec5c_commute_t_of_mem_P h hy
            calc y * t = (t * y * t⁻¹) * t := by rw [hyc]
              _ = t * y := by group
          exact hsup hxAP
        rw [Subgroup.mem_centralizer_singleton_iff] at hxct
        rw [← hxct, mul_assoc, mul_inv_cancel, mul_one] at h2
        exact mul_eq_one_iff_eq_inv.mpr h2
      have hx1' : (x : G) = 1 := sec5c_eq_one_of_mem_sup_of_sq_eq_one h hxAP hx2'
      exact Subtype.ext (by simpa using hx1')
  -- ## `|Inv N_H(P)| = 1`
  have ht'H₁ : (⟨t, ht𝒢⟩ : ↥𝒢) ∉ H₁.subgroupOf 𝒢 := fun hmem =>
    h.notMem (Subgroup.mem_inf.mp (Subgroup.mem_subgroupOf.mp hmem)).1
  have hcard := Work.ThmF.Bender.cardKsetEqInv (H := H₁.subgroupOf 𝒢) hse
    (by rw [← Subgroup.orderOf_coe]; exact h.invol) ht'H₁
  have hInv : (Submission.Blueprint.involutions
      ((H₁.subgroupOf 𝒢 : Subgroup ↥𝒢) : Set ↥𝒢)).ncard = 1 := hcard ▸ hDK
  -- ## every involution of `N_H(P)` is `u`
  have huniq : ∀ z : G, z ∈ H₁ → orderOf z = 2 → z = u := by
    intro z hzH₁ hz2
    have hzmem : (⟨z, hzH₁.2⟩ : ↥𝒢) ∈ Submission.Blueprint.involutions
        ((H₁.subgroupOf 𝒢 : Subgroup ↥𝒢) : Set ↥𝒢) :=
      ⟨Subgroup.mem_subgroupOf.mpr hzH₁, by rw [← Subgroup.orderOf_coe]; exact hz2⟩
    have humem : (⟨u, hu𝒢⟩ : ↥𝒢) ∈ Submission.Blueprint.involutions
        ((H₁.subgroupOf 𝒢 : Subgroup ↥𝒢) : Set ↥𝒢) :=
      ⟨Subgroup.mem_subgroupOf.mpr huH₁, by rw [← Subgroup.orderOf_coe]; exact hu.2.1⟩
    obtain ⟨a, ha⟩ := Set.ncard_eq_one.mp hInv
    have h1 : (⟨z, hzH₁.2⟩ : ↥𝒢) = a := by
      have := ha ▸ hzmem
      simpa using this
    have h2 : (⟨u, hu𝒢⟩ : ↥𝒢) = a := by
      have := ha ▸ humem
      simpa using this
    exact Subtype.ext_iff.mp (h1.trans h2.symm)
  -- ## conclude
  exact fun z hz hz2 => huniq z (hH₁ ▸ hz) hz2

end InvolutionOfNH

section InvolutionOfNH2

variable {H : Subgroup G} {t : G} {W : Subgroup G} {p : ℕ} {P A : Subgroup G} {r : ℕ}

/-- `N_H(P) = H ⊓ N_G(P)` centralises `u`: every `z ∈ N_H(P)` conjugates the involution `u` to an
involution of `N_H(P)`, i.e. to `u` itself. -/
theorem sec5c_inv_involutions_normalizer
    (hFT : Submission.Blueprint.FeitThompsonProp)
    (hC4 : Submission.Blueprint.ChIIFourProp)
    (h : Design.Setup5 G H t W p P A r) (u : G)
    (hu : u ∈ H ∧ orderOf u = 2 ∧
      u ∈ Subgroup.centralizer (Submission.Blueprint.centD H t : Set G)) :
    H ⊓ Subgroup.normalizer (P : Set G) ≤ Subgroup.centralizer ({u} : Set G) := by
  classical
  have huniq := sec5c_inv_unique hFT hC4 h u hu
  have huM : u ∈ H ⊓ Subgroup.normalizer (P : Set G) :=
    ⟨hu.1, sec5c_mem_normalizer_u h hu⟩
  intro z hz
  rw [Subgroup.mem_centralizer_singleton_iff]
  have hzu_mem : z * u * z⁻¹ ∈ H ⊓ Subgroup.normalizer (P : Set G) :=
    (H ⊓ Subgroup.normalizer (P : Set G)).mul_mem
      ((H ⊓ Subgroup.normalizer (P : Set G)).mul_mem hz huM)
      ((H ⊓ Subgroup.normalizer (P : Set G)).inv_mem hz)
  have hzu_ord : orderOf (z * u * z⁻¹) = 2 := by
    rw [show z * u * z⁻¹ = MulAut.conj z u from by rw [MulAut.conj_apply]]
    rw [sec5c_orderOf_conj_eq]
    exact hu.2.1
  have hzu : z * u * z⁻¹ = u := huniq _ hzu_mem hzu_ord
  calc z * u = (z * u * z⁻¹) * z := by group
    _ = u * z := by rw [hzu]

end InvolutionOfNH2

theorem sec5_clause_c (hFT : Submission.Blueprint.FeitThompsonProp) (hA : Submission.Blueprint.ThmAProp)
    (hC : Submission.Blueprint.ThmCProp) (hC4 : Submission.Blueprint.ChIIFourProp)
    (hP3 : Submission.Blueprint.ChIIFourP3SubnormalProp)
    (hIII : Work.NormalComplement.AppIIIProp)
    (hMF2 : Submission.Blueprint.BenderModelFacts2Prop)
    (hCor1 : Work.NormalComplement.Design.ChISixCor1Prop) {G : Type} [Group G] [Finite G]
    {H : Subgroup G} {t : G} {W : Subgroup G} {p : ℕ} {P A : Subgroup G} {r : ℕ}
    (h : Work.NormalComplement.Design.Setup5 G H t W p P A r) (u : G)
    (hu : u ∈ H ∧ orderOf u = 2 ∧
      u ∈ Subgroup.centralizer (Submission.Blueprint.centD H t : Set G))
    (hL1 : ∀ X : Subgroup G, P ≤ X → X ≤ Submission.Blueprint.centD H t →
      H ⊓ Subgroup.normalizer (P : Set G) ≤ Subgroup.normalizer (X : Set G) → X = P)
    (M : Subgroup G) (hM : (M : Set G) = Work.NormalComplement.Design.Mset u t) :
    H ⊓ Subgroup.normalizer (P : Set G) ≤ Subgroup.normalizer (M : Set G) := by
  classical
  -- `N_H(P)` centralises `u`, the unique involution of `N_H(P)`
  have hCu : H ⊓ Subgroup.normalizer (P : Set G) ≤ Subgroup.centralizer ({u} : Set G) :=
    sec5c_inv_involutions_normalizer hFT hC4 h u hu
  -- the subgroup `κ` inside `Mset u t`, containing `ut`, normalised by `N_H(P)`
  obtain ⟨κ, hκM, hut, hκnorm⟩ :=
    sec5c_kappa hFT hA hC hC4 hP3 hIII hMF2 hCor1 h u hu hL1
      (sec5c_inv_unique hFT hC4 h u hu)
  -- `M = Mset u t` is abelian, hence centralised by its subgroup `κ`
  have hκab : ∀ x ∈ κ, ∀ y ∈ M, x * y = y * x := by
    intro x hx y hy
    have hxM : x ∈ M := by
      show x ∈ (M : Set G); rw [hM]; exact hκM hx
    exact mset_abelian M hM x hxM y hy
  refine mset_normalizer_of_kappa h.invol hu.2.1 hM hκM hut hκab ?_ ?_
  · intro n hn
    exact Subgroup.mem_centralizer_iff.mp (hCu hn) u (Set.mem_singleton u)
  · intro n hn
    exact hκnorm hn

end Work.NormalComplement
