import Mathlib
import Submission.Work.NormalComplement.Defs
import Submission.Work.NormalComplement.Prelim
import Submission.Work.NormalComplement.Sections
import Submission.Work.ThreePoints.Basic

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# Peterfalvi I Ch. II §4 Proposition 2 (b): `X ≤ D` fixing three points is `D`-conjugate into `V`

Peterfalvi, *Le théorème de Bender–Suzuki I*, Astérisque 142–143 (1986), Ch. II §4, Proposition 2
(p. 169):

> Let `D = H ∩ H^t`, `V = C_D(t)`.  If `X` is a subgroup of `D` with `|Ω_X| ≥ 3`, then `X` is
> conjugate in `D` to a subgroup of `V`.

(In the paper's notation `Ω_X` is the set of points of `Ω = G ⧸ H` fixed by `X`, i.e.
`fixedPts H X`, and "conjugate in `D`" means `d X d⁻¹ ⊆ V` for some `d ∈ D`.)

The paper proves this from Ch. II §4 Prop. 1 (b) plus two facts about `D`:

* **Prop. 1 (a)**: for `X ≤ G` fixing three points and `M ∈ Ω_X`, `|C_M(X)|` is even.  Here we
  only need the case `M = H`, which we obtain *from Prop. 1 (b)* applied with `F = C_G(X)` (the
  standing hypothesis `Inv C_G(X) ⊆ F ⊆ N_G(X)` is satisfied): `C_G(X) ⊓ H`, being strongly
  embedded in `C_G(X)`, has even order.  This is the route recorded in the header of
  `Submission/Work/NormalComplement/section2_prop1.lean`.
* **Prop. 2 (a)** (a clause of `Submission.Blueprint.ChIIFourProp`): `V = C_D(u)` for some
  involution `u ∈ H`, together with `BenderPrelimProp` (Ch. I §2 Prop. 2 (b)): `D` is transitive
  on the involutions of `H`.  Conjugating `v` to `u` by `d ∈ D` sends `X ≤ C_D(v)` into
  `C_D(u) = V`.

Hence the two hypotheses `hC4 : ChIIFourProp` and `hBP : BenderPrelimProp` of the statement are
exactly what the argument consumes.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

open Classical
open scoped Pointwise commutatorElement
open LeanEval.GroupTheory.Defs
open Submission.Blueprint

namespace Work.NormalComplement

variable {G : Type*} [Group G]

/-- An even-order subgroup contains an element of order `2` (Cauchy for `p = 2`). -/
theorem exists_orderOf_two_of_even_card_subgroup {G : Type} [Group G] [Finite G]
    {C : Subgroup G} (h : Even (Nat.card C)) :
    ∃ u ∈ C, orderOf u = 2 := by
  classical
  haveI : Fintype ↥C := Fintype.ofFinite ↥C
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h2 : 2 ∣ Fintype.card ↥C := by
    rw [Fintype.card_eq_nat_card]
    exact even_iff_two_dvd.mp h
  obtain ⟨u, hu⟩ := exists_prime_orderOf_dvd_card (G := ↥C) 2 h2
  exact ⟨(u : G), u.2, (orderOf_injective C.subtype C.subtype_injective u).trans hu⟩

/-- **Peterfalvi I Ch. II §4 Prop. 1(a), case `M = H`** (p. 168), in the form used by Prop. 2(b):
a subgroup `X ≤ D = H ∩ H^t` fixing at least three points of `Ω = G ⧸ H` is centralised by an
involution of `H`.

The proof uses only Prop. 1(b): applied with `F = C_G(X)` it says that `C_H(X) = C_G(X) ⊓ H` is a
strongly embedded subgroup of `C_G(X)`, hence has even order. -/
theorem exists_involution_centralizing_of_fixes_three {G : Type} [Group G] [Finite G]
    (hS : Situation G) (hC4 : ChIIFourProp)
    {H : Subgroup G} (hH : IsStronglyEmbedded H)
    {t : G} (ht : orderOf t = 2) (htH : t ∉ H)
    {X : Subgroup G} (hX : X ≤ twoPoint H t)
    (h3 : 3 ≤ (fixedPts H X).ncard) :
    ∃ v : G, v ∈ H ∧ orderOf v = 2 ∧ ∀ x ∈ X, x * v = v * x := by
  have hXH : X ≤ H := le_trans hX inf_le_left
  -- Prop. 1(b) with `F = C_G(X)` and `g = 1`: `C_G(X) ⊓ H` is strongly embedded in `C_G(X)`.
  have hse : IsStronglyEmbedded
      ((Subgroup.centralizer (X : Set G) ⊓ conj (1 : G) H).subgroupOf
        (Subgroup.centralizer (X : Set G))) :=
    (hC4 G hS H hH t ht htH).1 X (Subgroup.centralizer (X : Set G)) h3
      (fun x hx => (Work.ThreePoints.mem_involutions.mp hx).1)
      (Subgroup.centralizer_le_normalizer (X : Set G))
      1 (by simpa using hXH)
  -- Transport the even-order conclusion back to `C_G(X) ⊓ H` as a subgroup of `G`.
  have hle : Subgroup.centralizer (X : Set G) ⊓ conj (1 : G) H ≤
      Subgroup.centralizer (X : Set G) := inf_le_left
  have heven : Even (Nat.card (Subgroup.centralizer (X : Set G) ⊓ conj (1 : G) H : Subgroup G)) := by
    rw [← Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv]
    exact hse.2.1
  obtain ⟨v, hv_mem, hv2⟩ := exists_orderOf_two_of_even_card_subgroup heven
  have hvC : v ∈ Subgroup.centralizer (X : Set G) := (Subgroup.mem_inf.mp hv_mem).1
  have hvH : v ∈ H := by simpa using (Subgroup.mem_inf.mp hv_mem).2
  exact ⟨v, hvH, hv2, fun x hx => (Subgroup.mem_centralizer_iff.mp hvC x hx)⟩

/-- **Peterfalvi I Ch. II §4 Prop. 2 (b)** (p. 169).  In the situation (B0)–(B2), with `H` strongly
embedded, `t ∉ H` an involution, `D = H ∩ H^t` and `V = C_D(t) = centD H t`: every subgroup
`X ≤ D` fixing at least three points of `Ω = G ⧸ H` is `D`-conjugate into `V`, i.e. there is
`d ∈ D` with `d X d⁻¹ ≤ V`.

Proof: `exists_involution_centralizing_of_fixes_three` gives an involution `v ∈ H` centralising `X`;
`ChIIFourProp` P2(a) gives an involution `u ∈ H` with `V = C_D(u)`; `BenderPrelimProp` gives
`d ∈ D` with `d v d⁻¹ = u`; then `d x d⁻¹ ∈ D` and `d x d⁻¹` commutes with `u = d v d⁻¹` for every
`x ∈ X`, so `d X d⁻¹ ≤ D ⊓ C_G(u) = V`. -/
theorem prop2b_conj_into_centD (G : Type) [Group G] [Finite G]
    (hS : Submission.Blueprint.Situation G) (hBP : Work.NormalComplement.BenderPrelimProp)
    (hC4 : Submission.Blueprint.ChIIFourProp)
    {H : Subgroup G} (hH : LeanEval.GroupTheory.Defs.IsStronglyEmbedded H)
    {t : G} (ht : orderOf t = 2) (htH : t ∉ H)
    {X : Subgroup G} (hX : X ≤ Submission.Blueprint.twoPoint H t)
    (h3 : 3 ≤ (Submission.Blueprint.fixedPts H X).ncard) :
    ∃ d ∈ Submission.Blueprint.twoPoint H t,
      X.map (MulAut.conj d).toMonoidHom ≤ Submission.Blueprint.centD H t := by
  -- P2(a): `V = C_D(u)` for an involution `u ∈ H`.
  obtain ⟨u, hu_inv, hu_centD⟩ := (hC4 G hS H hH t ht htH).2.1
  obtain ⟨huH, hu2⟩ := Work.ThreePoints.mem_involutions.mp hu_inv
  -- an involution `v ∈ H` centralising `X`.
  obtain ⟨v, hvH, hv2, hv_comm⟩ :=
    exists_involution_centralizing_of_fixes_three hS hC4 hH ht htH hX h3
  -- `D` is transitive on the involutions of `H`: conjugate `v` to `u`.
  obtain ⟨d, hdD, hdvu⟩ := hBP G hS H hH t ht htH v ⟨hvH, hv2⟩ u ⟨huH, hu2⟩
  have hdx_eq : ∀ x : G, (MulAut.conj d).toMonoidHom x = d * x * d⁻¹ := fun x => by
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  refine ⟨d, hdD, ?_⟩
  intro y hy
  obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp hy
  -- `d x d⁻¹` lies in `D`
  have hdxD : (MulAut.conj d).toMonoidHom x ∈ twoPoint H t := by
    rw [hdx_eq x]
    exact (twoPoint H t).mul_mem ((twoPoint H t).mul_mem hdD (hX hx))
      ((twoPoint H t).inv_mem hdD)
  -- `d x d⁻¹` commutes with `u = d v d⁻¹`, because `x` commutes with `v`
  have hdxC : (MulAut.conj d).toMonoidHom x ∈ Subgroup.centralizer ({u} : Set G) := by
    rw [Subgroup.mem_centralizer_singleton_iff, hdx_eq x, ← hdvu]
    have hxv : x * v = v * x := hv_comm x hx
    calc (d * x * d⁻¹) * (d * v * d⁻¹) = d * (x * v) * d⁻¹ := by group
      _ = d * (v * x) * d⁻¹ := by rw [hxv]
      _ = (d * v * d⁻¹) * (d * x * d⁻¹) := by group
  rw [hu_centD]
  exact ⟨hdxD, hdxC⟩

end Work.NormalComplement
