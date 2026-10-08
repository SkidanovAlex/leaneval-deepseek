import Mathlib
import Submission.Work.CORE4.Defs
import Submission.Work.CORE4.Case2CountSetup
import Submission.Work.CORE4.Case2LayerOneInvClass
import Submission.Work.CORE4.Case2RelIndexMH

namespace Work.CORE4

open Subgroup

/-! ## Auxiliary lemmas

The proof of Bender's "`|M : C_M(t)|` is odd" (Bender 1981, §4, p. 224) has three independent
ingredients, isolated here:

* the index identity `|M : M ⊓ C_G(t)| = |E : E ⊓ C_G(t)|` for `E = E(M)` (`M = E·C_M(t)` plus the
  second isomorphism theorem) — `M_eq_layerIn_sup_gen`, `layerIn_subgroupOf_normal_gen`,
  `relIndex_inter_H_eq_gen`;
* the reduction of the right hand side to the index of a centralizer in the group `↥E` —
  `relIndex_inf_centralizer_eq_index`;
* the group-theoretic fact that in a finite group in which all involutions are conjugate, the
  index of the centralizer of an involution is odd — `not_two_dvd_index_centralizer_of_oneInvClass`
  (take a Sylow 2-subgroup `P`, an involution `z` of `Z(P)` (which exists because `Z(P)` is a
  nontrivial 2-group), and note that `C(z)` contains `P`, so `|G : C(z)|` divides the odd number
  `|G : P|`; since `t` is conjugate to `z`, `|G : C(t)| = |G : C(z)|`).
-/

/-- `OneInvClassIn` is insensitive to viewing a subgroup as a group of its own: `K` has one class
of involutions iff `⊤ : Subgroup ↥K` does. -/
theorem oneInvClassIn_top_of_subgroup_gen {G : Type} [Group G] {E : Subgroup G}
    (h : Work.GW2.OneInvClassIn E) : Work.GW2.OneInvClassIn (⊤ : Subgroup ↥E) := by
  intro x hx y hy
  obtain ⟨-, hx2⟩ := hx
  obtain ⟨-, hy2⟩ := hy
  obtain ⟨g, hgE, hg⟩ :=
    h (x : G) ⟨x.2, by simpa using hx2⟩ (y : G) ⟨y.2, by simpa using hy2⟩
  refine ⟨⟨g, hgE⟩, Subgroup.mem_top _, ?_⟩
  apply Subtype.ext
  simpa using hg

/-- Under a group isomorphism `φ`, the centralizer of `z` maps onto the centralizer of `φ z`. -/
theorem map_centralizer_singleton_of_mulEquiv {X Y : Type} [Group X] [Group Y] (φ : X ≃* Y)
    (z : X) :
    (Subgroup.centralizer ({z} : Set X)).map φ.toMonoidHom =
      Subgroup.centralizer ({φ z} : Set Y) := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    have hy' : y * z = z * y := Subgroup.mem_centralizer_singleton_iff.mp hy
    refine Subgroup.mem_centralizer_singleton_iff.mpr ?_
    change φ y * φ z = φ z * φ y
    rw [← map_mul, ← map_mul, hy']
  · intro hx
    have hx' : x * φ z = φ z * x := Subgroup.mem_centralizer_singleton_iff.mp hx
    refine Subgroup.mem_map.mpr ⟨φ.symm x, ?_, ?_⟩
    · refine Subgroup.mem_centralizer_singleton_iff.mpr ?_
      have h : φ ((φ.symm x) * z) = φ (z * (φ.symm x)) := by
        rw [map_mul, map_mul, φ.apply_symm_apply]
        exact hx'
      exact φ.injective h
    · exact φ.apply_symm_apply x

/-- **A finite group with one class of involutions has odd centralizer indices.**  If `t` is an
involution of a finite group `X` and every two involutions of `X` are conjugate, then the index
`|X : C_X(t)|` is odd. -/
theorem not_two_dvd_index_centralizer_of_oneInvClass {X : Type} [Group X] [Finite X] {t : X}
    (ht : orderOf t = 2) (hone : Work.GW2.OneInvClassIn (⊤ : Subgroup X)) :
    ¬ 2 ∣ (Subgroup.centralizer ({t} : Set X)).index := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  -- `2 ∣ |X|`, so a Sylow 2-subgroup `P` of `X` is nontrivial
  have h2X : 2 ∣ Nat.card X := by
    rw [← ht]
    exact orderOf_dvd_natCard t
  let P : Sylow 2 X := Classical.choice (Sylow.nonempty (p := 2) (G := X))
  have hP2 : 2 ∣ Nat.card ↥(P : Subgroup X) := by
    simpa using P.pow_dvd_card_of_pow_dvd_card (n := 1) (by simpa using h2X)
  haveI : Nontrivial ↥(P : Subgroup X) := by
    rw [← Finite.one_lt_card_iff_nontrivial]
    obtain ⟨m, hm⟩ := hP2
    have hpos : 0 < Nat.card ↥(P : Subgroup X) := Nat.card_pos
    omega
  -- the centre of `P` is a nontrivial `2`-group, hence contains an involution `z`
  have hZnt : Nontrivial ↥(Subgroup.center ↥(P : Subgroup X)) :=
    IsPGroup.center_nontrivial (p := 2) P.isPGroup'
  have hZ2 : 2 ∣ Nat.card ↥(Subgroup.center ↥(P : Subgroup X)) := by
    have hpg : IsPGroup 2 ↥(Subgroup.center ↥(P : Subgroup X)) :=
      P.isPGroup'.to_subgroup (Subgroup.center _)
    obtain ⟨n, hn, hcard⟩ := hpg.nontrivial_iff_card.mp hZnt
    rw [hcard]
    exact dvd_pow_self 2 hn.ne'
  obtain ⟨c, hc⟩ := exists_prime_orderOf_dvd_card' 2 hZ2
  set z : X := ((c : ↥(P : Subgroup X)) : X) with hzdef
  have hz2 : orderOf z = 2 := by
    rw [hzdef]
    have h1 : orderOf (c : ↥(P : Subgroup X)) = orderOf c :=
      orderOf_injective (Subgroup.subtype (Subgroup.center ↥(P : Subgroup X)))
        Subtype.coe_injective c
    have h2 : orderOf ((c : ↥(P : Subgroup X)) : X) = orderOf (c : ↥(P : Subgroup X)) :=
      orderOf_injective (Subgroup.subtype (P : Subgroup X)) Subtype.coe_injective _
    rw [h2, h1, hc]
  -- `P` centralizes `z`
  have hPle : (P : Subgroup X) ≤ Subgroup.centralizer ({z} : Set X) := by
    intro s hs
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hcomm := Subgroup.mem_center_iff.mp c.2 (⟨s, hs⟩ : ↥(P : Subgroup X))
    have hcoe := congrArg (fun u : ↥(P : Subgroup X) => (u : X)) hcomm
    simpa [hzdef, Subgroup.coe_mul] using hcoe
  -- `t` is conjugate to `z`, so their centralizers have the same cardinality
  have hzmem : z ∈ Work.GW2.involutionSet (⊤ : Subgroup X) := ⟨Subgroup.mem_top z, hz2⟩
  have htmem : t ∈ Work.GW2.involutionSet (⊤ : Subgroup X) := ⟨Subgroup.mem_top t, ht⟩
  obtain ⟨g, -, hg⟩ := hone z hzmem t htmem
  have hconj : (MulAut.conj g) z = t := by
    rw [MulAut.conj_apply]
    exact hg
  have hcard : Nat.card ↥(Subgroup.centralizer ({t} : Set X)) =
      Nat.card ↥(Subgroup.centralizer ({z} : Set X)) := by
    have hmap := map_centralizer_singleton_of_mulEquiv (MulAut.conj g) z
    rw [hconj] at hmap
    rw [← hmap, Subgroup.card_map_of_injective (MulAut.conj g).injective]
  -- `|P|` divides `|C(z)| = |C(t)|`
  have hdvdcard : Nat.card ↥(P : Subgroup X) ∣
      Nat.card ↥(Subgroup.centralizer ({t} : Set X)) := by
    rw [hcard]
    exact Subgroup.card_dvd_of_le hPle
  obtain ⟨k, hk⟩ := hdvdcard
  -- hence `|X : C(t)|` divides `|X : P|`, which is odd
  have hPpos : 0 < Nat.card ↥(P : Subgroup X) := Nat.card_pos
  have hkey : (Subgroup.centralizer ({t} : Set X)).index * k = (P : Subgroup X).index := by
    apply Nat.mul_right_cancel hPpos
    calc (Subgroup.centralizer ({t} : Set X)).index * k * Nat.card ↥(P : Subgroup X)
        = (Subgroup.centralizer ({t} : Set X)).index *
            Nat.card ↥(Subgroup.centralizer ({t} : Set X)) := by
          rw [hk, mul_assoc, mul_comm k]
      _ = Nat.card X := Subgroup.index_mul_card _
      _ = (P : Subgroup X).index * Nat.card ↥(P : Subgroup X) :=
          (Subgroup.index_mul_card _).symm
  intro h2dvd
  exact Sylow.not_dvd_index P (by rw [← hkey]; exact dvd_mul_of_dvd_left h2dvd k)

/-- **Bender §4, p. 224 (`M = E(M)·C_M(t)`), with only the hypotheses that are used.**  If the
involution `B.t` lies in the layer `E(M) = layerIn M` and `E(M)` has a single class of
involutions, then `M = E(M) ⊔ (M ⊓ C_G(t))`. -/
theorem M_eq_layerIn_sup_gen {G : Type} [Group G] [Finite G] (B : Work.GW2.BenderSetup G)
    (M : Subgroup G) (hone : Work.GW2.OneInvClassIn (Work.GW2.layerIn M))
    (ht : B.t ∈ Work.GW2.layerIn M) : M = Work.GW2.layerIn M ⊔ (M ⊓ B.H) := by
  set E : Subgroup G := Work.GW2.layerIn M with hE
  have hEM : E ≤ M := by rw [hE]; exact layerIn_le M
  have hnorm : M ≤ Subgroup.normalizer (E : Set G) := by
    rw [hE]; exact layerIn_le_normalizer M
  have htE : B.t ∈ E := by rw [hE]; exact ht
  refine le_antisymm ?_ (sup_le hEM inf_le_left)
  intro g hg
  have hconj : g * B.t * g⁻¹ ∈ E :=
    Subgroup.le_normalizer_iff.mp hnorm g hg B.t htE
  have horder : orderOf (g * B.t * g⁻¹) = 2 := by
    have hconj_eq : g * B.t * g⁻¹ = (MulAut.conj g) B.t := by simp [MulAut.conj_apply]
    rw [hconj_eq, ← B.t_order, orderOf_eq_orderOf_iff]
    intro n
    rw [← map_pow]
    exact (MulAut.conj g).map_eq_one_iff
  obtain ⟨d, hd, hconjd⟩ := hone (g * B.t * g⁻¹) ⟨hconj, horder⟩ B.t ⟨htE, B.t_order⟩
  have hdM : d ∈ M := hEM hd
  have hcen : d * g ∈ B.H := by
    show d * g ∈ Subgroup.centralizer ({B.t} : Set G)
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hX : (d * g) * B.t * (d * g)⁻¹ = B.t := by
      rw [show (d * g) * B.t * (d * g)⁻¹ = d * (g * B.t * g⁻¹) * d⁻¹ by group]
      exact hconjd
    calc (d * g) * B.t = ((d * g) * B.t * (d * g)⁻¹) * (d * g) := by group
      _ = B.t * (d * g) := by rw [hX]
  have hmem : d * g ∈ M ⊓ B.H := ⟨M.mul_mem hdM hg, hcen⟩
  have hgoal : g = d⁻¹ * (d * g) := by group
  rw [hgoal]
  exact Subgroup.mul_mem_sup (E.inv_mem hd) hmem

/-- `E(M) = layerIn M` is normal in `M`. -/
theorem layerIn_subgroupOf_normal_gen {G : Type} [Group G] (M : Subgroup G) :
    ((Work.GW2.layerIn M).subgroupOf M).Normal := by
  have h1 : (Work.GW2.layerIn M).subgroupOf M = Work.GW2.layer ↥M := by
    rw [Work.GW2.layerIn]
    exact Subgroup.comap_map_eq_self_of_injective (Subtype.val_injective) _
  rw [h1]
  exact layer_normal M

/-- **The second isomorphism theorem for `M = E(M)·C_M(t)`**: the index of `C_M(t)` in `M` is the
index of `C_{E(M)}(t)` in `E(M)`. -/
theorem relIndex_inter_H_eq_gen {G : Type} [Group G] [Finite G] (B : Work.GW2.BenderSetup G)
    (M : Subgroup G) (hone : Work.GW2.OneInvClassIn (Work.GW2.layerIn M))
    (ht : B.t ∈ Work.GW2.layerIn M) :
    (M ⊓ B.H).relIndex M = (Work.GW2.layerIn M ⊓ B.H).relIndex (Work.GW2.layerIn M) := by
  have hsup : M = Work.GW2.layerIn M ⊔ (M ⊓ B.H) := M_eq_layerIn_sup_gen B M hone ht
  have hnorm : ((Work.GW2.layerIn M).subgroupOf M).Normal := layerIn_subgroupOf_normal_gen M
  have hkey := relIndex_eq_relIndex_inf_of_normal_sup_eq (Work.GW2.layerIn M) (M ⊓ B.H) M
    (layerIn_le M) inf_le_left hsup.symm hnorm
  rwa [show Work.GW2.layerIn M ⊓ (M ⊓ B.H) = Work.GW2.layerIn M ⊓ B.H from by
    rw [← inf_assoc, inf_eq_left.mpr (layerIn_le M)]] at hkey

/-- For `E ≤ G` and `t ∈ E`, the index `|E : E ⊓ C_G(t)|` is the index of the centralizer of `t`
in the group `↥E`. -/
theorem relIndex_inf_centralizer_eq_index {G : Type} [Group G] (E : Subgroup G) {t : G}
    (ht : t ∈ E) :
    (E ⊓ Subgroup.centralizer ({t} : Set G)).relIndex E =
      (Subgroup.centralizer ({⟨t, ht⟩} : Set ↥E)).index := by
  rw [← subgroupOf_inf_centralizer E t ht, ← Subgroup.relIndex_top_right]
  rw [← Subgroup.subgroupOf_self E]
  exact (Subgroup.relIndex_subgroupOf
    (H := E ⊓ Subgroup.centralizer ({t} : Set G)) (K := E) (L := E) le_rfl).symm

/-- Bender §4, p. 224: for the maximal subgroup `M` of Theorem 2.10 (2) over a minimal
counterexample (`BenderCtx G`), the index `|M : C_M(t)|` is odd.

Here `t = B.t` is Bender's involution (`orderOf t = 2`) and `B.H = C_G(t)`, so the claim is
`¬ 2 ∣ (M ⊓ B.H).relIndex M`, i.e. `2 ∤ |M : M ⊓ C_G(t)|`.

Route (this is the "`E(M)` has one class of involutions, so `C_M(t)` contains a Sylow of `M`"
step of Bender's §4):
* `E := layerIn M` is quasisimple, normal in `M`, and `t ∈ E` is an involution; `E` has one class
  of involutions (`Submission.Work.CORE4.Case2LayerOneInvClass`), so `M = E · C_M(t)` — the
  argument is that of `Submission.Work.CORE4.CountSetup.M_eq_layerIn_sup`, which needs only
  `IsCoatom M`, `t ∈ layerIn M` and `OneInvClassIn (layerIn M)`.
* Hence, by the second isomorphism theorem, `|M : M ⊓ C_G(t)| = |E : E ⊓ C_G(t)|`
  (this is `Work.GW2.Case2Ctx.relIndex_M_inter_H`, whose proof again only uses the two facts
  just named plus `(layerIn M).subgroupOf M` being normal).
* For `E` quasisimple with `E/Z(E) ≅ A₇` or `E/Z(E) ≅ PSL(2, q)` (`I.toolkit.lay`) and `t ∈ E` an
  involution, `|E : C_E(t)| = |E/Z(E) : C_{E/Z(E)}(tZ(E))|` is odd:
  - `A₇`: `I.toolkit.a7` gives `|A₇| = 2520` and `|C_{A₇}(x)| = 24` for every involution `x`, and
    `2520 / 24 = 105` is odd;
  - `PSL(2,q)`: `I.toolkit.l2cent` gives `C_{PSL(2,q)}(x̄) ≅ DihedralGroup m` with
    `2 * m = q - 1 ∨ 2 * m = q + 1` for every involution `x̄`; `I.toolkit.l2syl` gives
    `Sylow 2 (PSL(2,q)) ≅ DihedralGroup n` with `n ≥ 2`, and `DihedralGroup n` with
    `2 * n ≥ 4` a power of two and `n` even contains a Klein four group `V`; take `x̄ ∈ V`; then
    `V ≤ C(x̄) ≅ DihedralGroup m`, and a Klein four inside `DihedralGroup m` forces `4 ∣ 2 * m`.
    As all involutions of `E` are conjugate (`I.layerOneInvClass`), the order of `C(x̄)` — hence
    `m` — is the same for every involution; so `2 * m` is the one of `q - 1`, `q + 1` that is
    divisible by `4`, and the index `q * (q + 1) / 2` or `q * (q - 1) / 2` is a product of two odd
    numbers. -/
theorem Case2Setup9Odd (I : Work.GW2.C4Inputs) :
    ∀ (G : Type) [Group G] [Finite G], Work.GW2.BenderCtx G →
      ∀ (B : Work.GW2.BenderSetup G) (M : Subgroup G),
        IsCoatom M → B.t ∈ Work.GW2.layerIn M → ¬ 2 ∣ (M ⊓ B.H).relIndex M := by
  intro G _ _ hbc B M hcoat ht
  have hone : Work.GW2.OneInvClassIn (Work.GW2.layerIn M) :=
    Case2LayerOneInvClass I G hbc B M hcoat ht
  rw [relIndex_inter_H_eq_gen B M hone ht]
  show ¬ 2 ∣ ((Work.GW2.layerIn M) ⊓ Subgroup.centralizer ({B.t} : Set G)).relIndex
    (Work.GW2.layerIn M)
  rw [relIndex_inf_centralizer_eq_index (Work.GW2.layerIn M) ht]
  have hone' : Work.GW2.OneInvClassIn (⊤ : Subgroup ↥(Work.GW2.layerIn M)) :=
    oneInvClassIn_top_of_subgroup_gen hone
  have hord : orderOf (⟨B.t, ht⟩ : ↥(Work.GW2.layerIn M)) = 2 := by
    rw [Subgroup.orderOf_mk, B.t_order]
  exact not_two_dvd_index_centralizer_of_oneInvClass hord hone'

end Work.CORE4
