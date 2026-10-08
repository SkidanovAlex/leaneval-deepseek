/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gorenstein–Walter formalisation team (area CORE4, `Work.CORE4`)

# AREA CORE4 — design pass 10: the A₇ exclusion and step (9), leaf layer

Every statement below is copied **verbatim** from `Submission/Work/_design_gw/Core10C4.lean`
(namespace `GW2.C10C4` there, `Work.GW2` here), which is checked against this area's
`CORE4/Defs.lean`.  It contains

* the common budget `Hyp9` of `Case2NotA7Impl9`/`Case2NineImpl9`;
* the leaf `SixEmbedProp` (Bender's (6) in full: "`F` is isomorphic to a subgroup of `K₀`"),
  which the in-flight `Case2Seven` needs — see `NOTES_TO_LEAD.md` and
  `NOTES_CASE2SEVEN_FROM_OWNER.md`;
* the `A₇` chain A1–A8 (`A7KProp` … `CoreIndexProp`), with the assembly `notA7_of_leaves` **proved**;
* the step-(9) chain N1–N5d (`NineShapeProp` … `NineRyProp`) with `DihFourConjProp` and
  `L2OuterInvolutionProp` (the new `L2F` input: the `C4Inputs10` bundle below adds it as `l2outer`),
  and the assembly `nine_of_leaves` **proved**;
* the arithmetic leaves `nine_seven_le` and `nine_sylow_arith`, **proved**.

`C4Inputs10` is `C4Inputs` plus the one missing field `l2outer : L2OuterInvolutionProp`; since the
`…Prop` bodies below do not mention the bundle, a proof of e.g. `NineRProp I.toC4Inputs` under
`I : C4Inputs10` has `I.l2outer` available *and* is literally a proof of `NineRProp I` for the old
bundle (no bridge is needed).
-/
import Submission.Work.CORE4.Defs

open scoped MatrixGroups

namespace Work.GW2

open Subgroup

section Defs

variable {G : Type} [Group G] [Finite G]

/-- The common hypothesis budget of `Case2NotA7Impl9` and `Case2NineImpl9` (design pass 9). -/
def Hyp9 (G : Type) [Group G] [Finite G] (B : BenderSetup G) (C : Case2Ctx6 B) : Prop :=
  BenderCtx G ∧ Case2 B ∧ Case2PrePlus B C.D ∧ Case2SevenFacts B C.D ∧ Case2EightAll B C.D

/-- `E/Z(E) ≅ A₇`, with `E = E(M) = layerIn D.M`. -/
def IsA7Case {B : BenderSetup G} (D : Case2Data B) : Prop :=
  Nonempty ((↥(layerIn D.M) ⧸ center ↥(layerIn D.M)) ≃* alternatingGroup (Fin 7))

end Defs

/-! ## 0. A general leaf: Bender's (6) in full, `F ↪ K₀`

Case2Ctx6 records only the *conclusion* "`F` is cyclic" of Bender's (6). The A₇ case needs
`|F| = 3`, and (9) needs `K₀ ≠ 1`. Both come from the printed (6), "`F` is isomorphic to a
subgroup of `K₀`", which IS derivable from `Case2Ctx6`. So it is not a missing hypothesis. -/

/-- **LEAF C10.0 `Case2SixEmbed`** (Bender p. 225, the line before (6)).

Route.
1. Find `g ∈ H ∖ M` normalizing `K₀F = F(U) ∩ M`. (`SixThree`, proved, gives
   `F(U) ∩ M = K₀ ⊔ F`.)
   * If `F(U) ≤ M`, then `F(U) = K₀F`, and any `g ∈ H ∖ M` works (`¬ H ≤ M` is in `Case2Pre`).
     `H` normalizes `F(U)`, since `F(U)` is characteristic in `U ⊴ H`.
   * Otherwise `K₀F < F(U)`. `F(U)` is nilpotent (`Work.BMAX.isNilpotent_fittingIn`), so
     normalizers grow: take `g ∈ N_{F(U)}(K₀F) ∖ K₀F`. Then `g ∉ M`, because
     `g ∈ F(U) ∩ M = K₀F` would be a contradiction.
2. `F^g ≤ K₀F` and `F ∩ F^g = 1` (the TI field `C.F_ti`). `F ⊴ K₀F` (as `N_G(F) = M`).
   `K₀ ⊴ K₀F` and `K₀ ∩ F = 1` are proved in `Case2Seven.lean`
   (`K0_normal_in_K0supF`, `K0_inf_F_eq_bot`).
3. Hence `F ≅ F^g ≅ F^gF/F ≤ K₀F/F ≅ K₀`, so `|F|` divides `|K₀|`.

Corollary: `K₀ ≠ ⊥` (since `F ≠ ⊥`), unconditionally. This refutes the "K = ⊥ configuration" of
`NOTES_CASE2SEVEN.md` §3–4. The witness that §4 asks to add is derivable (step 1). -/
def SixEmbedProp (I : C4Inputs) : Prop :=
  ∀ (G : Type) [Group G] [Finite G], BenderCtx G → ∀ (B : BenderSetup G) (C : Case2Ctx6 B),
    Nat.card C.D.F ∣ Nat.card C.D.K0

/-! ## 1. The A₇ exclusion (Bender p. 226, "Now we can eliminate the case `E/Z(E) ≃ A₇`") -/

section A7Facts

variable {G : Type} [Group G] [Finite G]

/-- "`|K| = 3`, hence `|F| = 3` by (6)", and `π = {3}`. -/
def A7Facts1 {B : BenderSetup G} (D : Case2Data B) : Prop :=
  Nat.card D.K = 3 ∧ Nat.card D.F = 3 ∧ D.K0 = D.K ∧ B.piFU = {3}

/-- "`V := O₂(H∩M) = O₂(H) = O₂(Ĥ)` is of type (2,2), whence `Ĥ/VU ≅ D₆` and `S` (having order 8)
lies in `E`". The last conjunct is "`N_E(V) = Ĥ ∩ E`", used in step 4. -/
def A7Facts2 (B : BenderSetup G) (D : Case2Data B) : Prop :=
  IsFourGroup (pCoreIn 2 (B.H ⊓ D.M)) ∧
  pCoreIn 2 B.Hhat = pCoreIn 2 (B.H ⊓ D.M) ∧
  (B.S : Subgroup G) ≤ layerIn D.M ∧ Nat.card (B.S : Subgroup G) = 8 ∧
  layerIn D.M ⊓ normalizer ((pCoreIn 2 (B.H ⊓ D.M) : Subgroup G) : Set G) ≤ B.Hhat

/-- "By (7) and (8), `U` is a 3-group. Then `O(M) = B = F` and `K = Z(U)`." The last conjunct
packages "`M/F ≅ A₇`, whose 2'-subgroups have order at most 21" in the form used by step 6. -/
def A7Facts3 (B : BenderSetup G) (D : Case2Data B) : Prop :=
  IsPGroup 3 B.U ∧ D.B0 = D.F ∧ oddCoreIn D.M = D.F ∧
  D.K = (center ↥B.U).map B.U.subtype ∧
  ∀ X : Subgroup G, X ≤ D.M → Odd (Nat.card X) →
    Nat.card X ≤ 21 * Nat.card (X ⊓ D.F : Subgroup G)

/-- "Suppose `I_U(s) ⊲ H̃` … a contradiction." -/
def A7Facts4 (B : BenderSetup G) (D : Case2Data B) : Prop :=
  ¬ Case2InvNormal B D

/-- "By (8), this proves `A ⊲ U`, hence `|H : H∩M| = |U : U∩M| = 3`." Here `A = F × K`. -/
def A7Facts5 (B : BenderSetup G) (D : Case2Data B) : Prop :=
  (B.H ⊓ D.M).relIndex B.H = 3 ∧ (B.U ⊓ D.M).relIndex B.U = 3 ∧
  ((D.F ⊔ D.K).subgroupOf B.U).Normal

/-- "`|J ∩ My| ≤ 21` for every involution `y ∈ G − M`". Here `J ∩ My = {x | x² = 1 ≠ x, x y⁻¹ ∈ M}`. -/
def A7Facts6 {B : BenderSetup G} (D : Case2Data B) : Prop :=
  ∀ y : G, orderOf y = 2 → y ∉ D.M → {x : G | orderOf x = 2 ∧ x * y⁻¹ ∈ D.M}.ncard ≤ 21

end A7Facts

/-- **LEAF C10.A1 `A7K`**: `|K| = 3`, `|F| = 3`, `K₀ = K`, `π = {3}`.

Route.
* `K = [S∩E, U∩M] ≤ E` (`Case2PrePlus`). `s ∈ E` centralizes `Z(E)` and inverts `K`, and `|K|` is
  odd, so `K ∩ Z(E) = 1`. Hence `K` embeds in an odd-order subgroup of `C_{E/Z(E)}(tZ)`
  (`t ∈ E`, `K ≤ H = C(t)`).
* In `A₇`, `|C(t)| = 24` (`I.toolkit.a7`), so `|K| ∣ 3`.
* `K₀ ≠ 1` by `SixEmbedProp` (`F ≠ 1`). So `|K| = 3` and `K₀ = K`.
* `π = π(K₀) = {3}` by `Case2SevenFacts` conjunct 2.
* `|F|` divides `|K₀| = 3` and `F ≠ 1`, so `|F| = 3`. -/
def A7KProp (I : C4Inputs) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (B : BenderSetup G) (C : Case2Ctx6 B),
    Hyp9 G B C → IsA7Case C.D → Nat.card C.D.F ∣ Nat.card C.D.K0 → A7Facts1 C.D

/-- **LEAF C10.A2 `A7V`**.

Route.
* `S ∩ M ∈ Syl₂(M)` (`Case2PrePlus`) and `E ⊴ M`, so `S ∩ E ∈ Syl₂(E)`. It has order 8: the
  Sylow 2-subgroup of `A₇` (`I.toolkit.a7`), lifted through the odd `Z(E)`.
* `O₂(C_E(t))` is a four-group (A₇ model, lifted), and it is `≤ O₂(H∩M)`.
* `O₂(H∩M) = O₂(H)` (Seven conjunct 1) is normal in `H`. By `I.thm26`, `O₂(Ĥ) = S ∩ C(U)` is
  either `≤ S₀` (cyclic) or a four-group with `|Ĥ : O₂(Ĥ)U| = 6`. It contains a four-group, so the
  second case holds, and `V := O₂(H∩M) = O₂(H) = O₂(Ĥ)`.
* `S/V ↪ Ĥ/VU`, which has order 6, so `|S| ≤ 8 = |S ∩ E|`, giving `S ≤ E`.
* `N_E(V) ≤ N_G(V) = Ĥ`: `V ⊴ Ĥ`, and `Ĥ` is a maximal subgroup with `V` not normal in `G`. -/
def A7VProp (I : C4Inputs) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (B : BenderSetup G) (C : Case2Ctx6 B),
    Hyp9 G B C → IsA7Case C.D → A7Facts1 C.D → A7Facts2 B C.D

/-- **LEAF C10.A3 `A7U`**.

Route.
* `B₀ = C_U(s)` (`Case2Pre`) centralizes `S = S ∩ E`. Odd-order automorphisms of `A₇` are inner,
  and `C_{A₇}(D₈) = Z(D₈)`. So `B₀` acts trivially on `E/Z(E)`, and hence centralizes `E`
  (three-subgroup lemma; `E` is perfect).
* `B₀` centralizes `K₀ = K ≤ E`. `B₀` also centralizes `F`, because `|F| = 3` and `B₀` is odd.
  So `B₀ ≤ C_U(K₀F)`, which is a `π = {3}`-group by Seven conjunct 3.
* `|U : B₀KF(U)| ≤ 3` (EightFacts, for `P = F`, `p = 3`), and `B₀`, `K`, `F(U)` are 3-groups.
  So `U` is a 3-group, `F(U) = U`, and `B₀ = B₀ ∩ F(U) = F`.
* `O(M)` centralizes `E` (`[O(M), E] ≤ O(M) ∩ E ≤ Z(E)`), hence `O(M) ≤ C_M(t) ∩ O = U ∩ M`
  centralizes `S ∩ E`, so `O(M) ≤ B₀ = F ≤ O(M)`.
* `K = Z(U)` is as printed. Its route is not re-derived (see the notes).
* `M = E F` (`M = E C_M(t)`, `C_M(t) = (U∩M)(S∩M) = KF·S`), and `E ∩ F = Z(E)`, so
  `M/F ≅ A₇`. A 2'-subgroup `X ≤ M` has `X/(X∩F)` odd in `A₇`, so `|X : X∩F| ≤ 21`
  (`I.toolkit.a7`, last conjunct). -/
def A7UProp (I : C4Inputs) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (B : BenderSetup G) (C : Case2Ctx6 B),
    Hyp9 G B C → IsA7Case C.D → A7Facts1 C.D → A7Facts2 B C.D → A7Facts3 B C.D

/-- **LEAF C10.A4 `A7InvNormal`**: `I_U(s)` is not normal in `Ĥ`.

Route (Bender p. 226). Suppose `I := I_U(s) ⊴ Ĥ`.
* Apply `I.a7s4` (`A7S4Prop`, PROVED) to `E/Z(E) ≅ A₇`, with `V̄`, `s̄` and `K̄`. This gives
  `K̄' ≠ K̄` of order 3 in `N_{E/Z}(V̄)`, inverted by `s̄`. Lift it: `K' := I_{preimage}(s)` has
  order 3 (coprime action, `I.toolkit.c15`). This lifting is needed because `E = 3.A₇` is not
  excluded here, since `Z(E) ≤ O(M) = F` is allowed.
* Then `K' ≤ N_E(V) ≤ Ĥ` (`A7Facts2`). Bender writes `K' = K^e`, `e ∈ E`: in `A₇` all subgroups
  of order 3 lying in `N(V)` and inverted by `s` are `E`-conjugate (order-3 subgroups
  of `N_{A₇}(V)`, order 72, are the 3-cycle subgroups).
* `K'` centralizes `I` (both are inverted by `s`, and `K'` normalizes the abelian `I`).
  `U = B₀ I = F I` (`I.toolkit.c15`: `U = C_U(s) I_U(s)`). `F` centralizes `E ⊇ K'`.
  So `⟨s⟩ K' U ≤ N_G(K') = Ĥ^e`. Here `N_G(K) = Ĥ`, because `K = Z(U)` is characteristic in
  `U = O(Ĥ) ⊴ Ĥ` (`I.thm26`) and `Ĥ` is maximal.
* `U ∩ U^e` is normal in `Ĥ` and in `Ĥ^e ≠ Ĥ`, so it is normal in `G` (`Ĥ` maximal), and it is
  `≠ 1` (`|U| ≥ |KF| = 9`). This contradicts `BenderCtx.simple`. -/
def A7InvNormalProp (I : C4Inputs) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (B : BenderSetup G) (C : Case2Ctx6 B),
    Hyp9 G B C → IsA7Case C.D → A7Facts1 C.D → A7Facts2 B C.D → A7Facts3 B C.D →
      A7Facts4 B C.D

/-- **LEAF C10.A5 `A7IndexH`**: `A ⊴ U` and `|H : H∩M| = |U : U∩M| = 3`.

Route. Apply `Case2EightAll` with `p = 3` and `P = F` (`|F| = 3`, A1). The exceptional clause is
refuted by A4, so `A ⊴ F(U) = U` (A3). `A` is the unique `(3,3)` subgroup of `F ⊔ K = F × K`,
so `A = F ⊔ K`.
* `N_U(A) = U`, hence `p₀ = |U : N_U(P)| = |U : U∩M|` (EightFacts: `N_U(P) = U ∩ M`).
* `p₀ ≤ p = 3`. Also `¬ U ≤ M`: `H = US`, `S ≤ E ≤ M` (A2) and `¬ H ≤ M`.
* So `3 ≤ p₀ ≤ 3` (EightFacts' conditional conjunct).
* `|H : H∩M| = |U : U∩M|` because `H = U S` with `S ≤ M` (`I.toolkit.split`). -/
def A7IndexHProp (I : C4Inputs) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (B : BenderSetup G) (C : Case2Ctx6 B),
    Hyp9 G B C → IsA7Case C.D → A7Facts1 C.D → A7Facts2 B C.D → A7Facts3 B C.D →
      A7Facts4 B C.D → A7Facts5 B C.D

/-- **LEAF C10.A6 `A7Coset`**: `|J ∩ My| ≤ 21` for every involution `y ∉ M`.

Route (Bender p. 226, last paragraph). By 1.4, `J ∩ My = I_M(y) y = I_{M∩M^y}(y) y`.
1. `|F g ∩ I_M(y)| ≤ 1` for `g ∈ M`. If `f g, g ∈ I_M(y)`, then `f ∈ I(gy)` with `gy` an
   involution outside `M`, so `f ∈ F ∩ F^{gy} = 1` (`C.F_ti`).
2. If `M ∩ M^y` is odd, then `|I_M(y)| ≤ |M∩M^y : (M∩M^y) ∩ F| ≤ 21` (A3, last conjunct).
3. Otherwise `M ∩ M^y` contains an involution. Conjugating inside `M` (one class of involutions
   in `M`), assume `y ∈ C_G(t)`. Then:
   * `AV ⊴ H` lies in `M ∩ M^y`;
   * `A ∩ Z(M∩M^y) ⊇ F` is normalized by `y`, so `M ∩ M^y ≤ C_M(A)`;
   * `|C_M(A)| ≤ 108`: `C_M(A) = C_M(K)` (`F` is central in `M = EF`), and a 3-element of
     `A₇` inverted by an involution has centralizer of order 36 (GAP: `A₇` and `3.A₇`, see
     the notes);
   * `V ∈ Syl₂(M∩M^y)`, so the involutions of `(M∩M^y) y` are `M∩M^y`-conjugate;
   * `|C_{AV}(y)| = 6`.
   So there are at most `108 / 6 = 18` of them. -/
def A7CosetProp (I : C4Inputs) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (B : BenderSetup G) (C : Case2Ctx6 B),
    Hyp9 G B C → IsA7Case C.D → A7Facts1 C.D → A7Facts2 B C.D → A7Facts3 B C.D →
      A7Facts4 B C.D → A7Facts5 B C.D → A7Facts6 C.D

/-- **LEAF C10.A7 `A7SmallIndex`**: `|G : M| ≤ 7` and `7 ∣ |M|`.

Route.
* `J ⊆ (J ∩ M) ∪ ⋃_{My ≠ M} (J ∩ My)`, and each coset `My ≠ M` containing an involution has one
  involution `y` as representative. A6 gives `|J| ≤ |J ∩ M| + 21 |G : M|`.
* `|J| = |G : H|`: one class of involutions, `I.toolkit.fus`.
* `|J ∩ M| = |M : H∩M| = 105`. `M = E C_M(t)` (`CountSetup.M_eq_layerIn_sup`). `S ≤ E` and `E`
  has one class of involutions, so all involutions of `M` are `M`-conjugate to `t`.
  `|E : C_E(t)| = |A₇ : C_{A₇}(t)| = 2520/24`.
* `|G : H| = |G : M| |M : H∩M| / |H : H∩M| = 35 |G : M|` (A5).
* So `35 i ≤ 105 + 21 i`, i.e. `i ≤ 7`.
* `7 ∣ |A₇| ∣ |E| ∣ |M|`. -/
def A7SmallIndexProp (I : C4Inputs) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (B : BenderSetup G) (C : Case2Ctx6 B),
    Hyp9 G B C → IsA7Case C.D → A7Facts1 C.D → A7Facts2 B C.D → A7Facts3 B C.D →
      A7Facts4 B C.D → A7Facts5 B C.D → A7Facts6 C.D →
        C.D.M.index ≤ 7 ∧ 7 ∣ Nat.card C.D.M

/-- **LEAF C10.A8 `CoreIndex`** (pure group theory): "each 7-subgroup of `M` lies in all
conjugates of `M`, a contradiction".

Proof. `G` acts on `G/M` (`n = |G:M| ≤ p` points) with trivial kernel `core_G(M)` (`G` simple,
`M ≠ ⊤`). So `|G| ∣ n!`. But `p² ∣ |G| = n |M|` needs `n = p` (`p ∣ n!`) and then `p² ∤ p!`. -/
def CoreIndexProp : Prop :=
  ∀ (G : Type) [Group G] [Finite G], IsSimpleGroup G → ∀ M : Subgroup G, M ≠ ⊤ →
    ∀ p : ℕ, p.Prime → p ∣ Nat.card M → M.index ≤ p → False

/-! ## 2. Step (9) (Bender pp. 226–227) -/

section NineDefs

variable {G : Type} [Group G] [Finite G]

/-- `E/Z(E) ≅ L₂(q)`, `q = p^e`. -/
def NineShape {B : BenderSetup G} (D : Case2Data B) (p e : ℕ) [Fact p.Prime] : Prop :=
  Odd p ∧ 5 ≤ p ^ e ∧
  Nonempty ((↥(layerIn D.M) ⧸ center ↥(layerIn D.M)) ≃* PSL(2, GaloisField p e)) ∧
  Odd (Nat.card (center ↥(layerIn D.M)))

/-- "Let `k` (even) and `k'` (odd) be `(q ± 1)/2`", with `|K|` odd, `|K| ≥ 3` and `|K| ∣ k`.
Bender has `k = |K| |O₂(H ∩ E)|`. Only `|K| ∣ k` is used. -/
def NineKData {B : BenderSetup G} (D : Case2Data B) (q k k' : ℕ) : Prop :=
  Even k ∧ Odd k' ∧ ((2 * k = q + 1 ∧ 2 * k' = q - 1) ∨ (2 * k = q - 1 ∧ 2 * k' = q + 1)) ∧
  Nat.card D.K ∣ k ∧ 3 ≤ Nat.card D.K ∧ Odd (Nat.card D.K)

end NineDefs

/-- **LEAF C10.N1 `NineShape`**: `E` is quasisimple with `E/Z(E) ≅ L₂(q)` and `|Z(E)|` odd.

This is `CORE4/LayerCtx6.lean` (proved; it needs `DihOrCycSylow ↥M`, which is inherited from
`BenderCtx.sylow`) with the `A₇` alternative removed. -/
def NineShapeProp (I : C4Inputs) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (B : BenderSetup G) (C : Case2Ctx6 B),
    Hyp9 G B C → ¬ IsA7Case C.D → ∃ p e : ℕ, ∃ _ : Fact p.Prime, NineShape C.D p e

/-- **LEAF C10.N2 `NineK`**.

Route.
* `I.toolkit.l2cent` gives `C_{L₂(q)}(t̄) ≅ D_{2k}` with `2k = q ± 1`. This `k` is even:
  `C(t̄)` contains a Sylow 2-subgroup, of order `≥ 4`.
* `K ≤ E`, and `K ∩ Z(E) = 1` (`s` centralizes `Z(E)` and inverts `K`). So `K` embeds in the odd
  part of `D_{2k}`, and `|K| ∣ k`.
* `K₀ ≠ 1` (`SixEmbedProp` and `F ≠ 1`), and `K ≤ U` is odd, so `|K| ≥ 3`.
* `k' := k ∓ 1` is odd. -/
def NineKProp (I : C4Inputs) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (B : BenderSetup G) (C : Case2Ctx6 B),
    Hyp9 G B C → Nat.card C.D.F ∣ Nat.card C.D.K0 →
      ∀ (p e : ℕ) [Fact p.Prime], NineShape C.D p e →
        ∃ k k' : ℕ, NineKData C.D (p ^ e) k k'

/-- **LEAF C10.N3 `NineCenter`**: "`|F(M)|` is prime to `q` by (7), whence `Z(E) = 1`:
`E ≃ L₂(q)`".

Route.
* `Z(E)` is an abelian normal subgroup of `M`, so `Z(E) ≤ F(M)`.
* `π(F(M)) ⊆ π = π(K₀) ⊆ π(K)` (Seven conjuncts 5 and 2, `K₀ ≤ K`).
* `|K| ∣ k`, and `2k = q ± 1` is prime to `p`. So `Nat.Coprime |Z(E)| p`.
* `I.toolkit.l19` gives `Z(E) = 1`; then `E ≅ E/1 ≅ L₂(q)`. -/
def NineCenterProp (I : C4Inputs) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (B : BenderSetup G) (C : Case2Ctx6 B),
    Hyp9 G B C → ∀ (p e : ℕ) [Fact p.Prime], NineShape C.D p e →
      ∀ k k' : ℕ, NineKData C.D (p ^ e) k k' →
        Nonempty (layerIn C.D.M ≃* PSL(2, GaloisField p e))

/-- **LEAF C10.N5a `NineOuterInv`**: "If `S ⊄ E`, then `S ∩ M ⊄ E` because `N_S(S∩E)` normalizes
`C_{F(U)}(S∩E) = F`", plus the choice of an involution `r ∈ (S ∩ M) ∖ E`.

Route.
* `C_{F(U)}(S∩E) = F` uses `Case2PrePlus` (the `B₀` clause) and `B₀ = C_U(s)` (`Case2Pre`).
* If `S ∩ M ≤ E`, then `S ∩ E = S ∩ M`. If moreover `S ≠ S ∩ E`, then
  `N_S(S∩E) > S∩E` normalizes `F`, so it lies in `N_G(F) = M`, so in `S ∩ M = S ∩ E`. That is a
  contradiction.
* In the dihedral `S ∩ M`, an elementwise check: the involutions outside the cyclic maximal
  subgroup generate, so one of them lies outside the proper normal subgroup `S ∩ E`. -/
def NineOuterInvProp (I : C4Inputs) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (B : BenderSetup G) (C : Case2Ctx6 B),
    Hyp9 G B C → ¬ (B.S : Subgroup G) ≤ layerIn C.D.M →
      ∃ r ∈ (B.S : Subgroup G) ⊓ C.D.M, orderOf r = 2 ∧ r ∉ layerIn C.D.M

/-- **NEW L2F INPUT `L2OuterInvolutionProp`** (not in `C4Inputs`; see the notes, §3.4).

Let `L ⊴ Q` with `L ≅ L₂(q)`, `Q` with dihedral or cyclic Sylow 2-subgroups, and `r ∈ Q` an
involution not in `L C_Q(L)`. Then `C_L(r)` contains a cyclic subgroup `R` of order `k'`, the odd
one of `(q ± 1)/2`, and every involution of `C_L(r)` inverts `R`. (By `I.toolkit.autL2`, `r` is
then a `PGL₂(q) ∖ L₂(q)` involution, and `C_L(r) ≅ D_{2k'}`.)

GAP: checked in `PGL(2,q)` for `q = 11, 13, 19, 23, 25, 27, 29, 37, 41, 49`, over all outer
involution classes. -/
def L2OuterInvolutionProp : Prop :=
  ∀ (Q : Type) [Group Q] [Finite Q] (L : Subgroup Q) (p e : ℕ) [Fact p.Prime], Odd p →
    5 ≤ p ^ e → L.Normal → Nonempty (L ≃* PSL(2, GaloisField p e)) → DihOrCycSylow Q →
    ∀ r : Q, orderOf r = 2 → r ∉ L ⊔ centralizer (L : Set Q) →
    ∀ k' : ℕ, Odd k' → (2 * k' = p ^ e + 1 ∨ 2 * k' = p ^ e - 1) →
      ∃ R : Subgroup Q, R ≤ L ∧ R ≤ centralizer ({r} : Set Q) ∧ Nat.card R = k' ∧
        IsCyclic R ∧ ∀ x ∈ L, orderOf x = 2 → x * r = r * x → Inverts x R

/-- **LEAF C10.N5b `NineR`**: "`R := O(C_E(r))` has order `k'` and is inverted by `t`".

Route.
* `C_M(E)` has odd order. `C_M(E) ∩ E = Z(E) = 1`, and `S∩M` (dihedral, 2-rank 2) cannot contain
  `(S∩E) × Ω₁(O₂(C_M(E)))`. So `r ∉ E C_M(E)`: if `r = e c` then `c² = 1`, so `c = 1`.
* Apply `L2OuterInvolutionProp` to `Q = M`, `L = E`. `t ∈ E` is an involution commuting with `r`
  (`t` is central in `S`).
* `NEEDS` the new input `L2OuterInvolutionProp`. `L2InvolutionCentralizerProp`, `L2TIProp`,
  `L2FourGroupProp` and `AutL2Prop` do not determine `C_{L₂(q)}(r)` for outer `r`. -/
def NineRProp (I : C4Inputs) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (B : BenderSetup G) (C : Case2Ctx6 B),
    Hyp9 G B C → ∀ (p e : ℕ) [Fact p.Prime], NineShape C.D p e →
      Nonempty (layerIn C.D.M ≃* PSL(2, GaloisField p e)) →
      ∀ k k' : ℕ, NineKData C.D (p ^ e) k k' →
      ∀ r ∈ (B.S : Subgroup G) ⊓ C.D.M, orderOf r = 2 → r ∉ layerIn C.D.M →
        ∃ R : Subgroup G, R ≤ layerIn C.D.M ∧ R ≤ centralizer ({r} : Set G) ∧
          Nat.card R = k' ∧ Inverts B.t R

/-- **General leaf `DihFourConj`** (pure group theory, used by N5c). With dihedral `S` of order at
least 8 and one class of involutions, `t ∈ Z(S)` and an involution `r ∈ S`, `r ≠ t`, are conjugate
under `C_G(tr)`.

Route.
* `tr ∼ t`, so `|C(tr)|_2 = |S| ≥ 8`. Let `T ∈ Syl₂(C(tr))` contain `⟨t, r⟩`.
* `tr ∈ Z(T)`. `t` and `r = t·(tr)` are non-central involutions of a four-subgroup of the
  dihedral `T` (order ≥ 8), so they are `T`-conjugate.

GAP: checked on `L₂(7)`, `L₂(9)`, `L₂(17)`, `L₂(31)`, `L₂(49)` and `A₇`, over all `r`. -/
def DihFourConjProp : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (S : Sylow 2 G) (n : ℕ), 4 ≤ n →
    Nonempty ((S : Subgroup G) ≃* DihedralGroup n) →
    (∀ x y : G, orderOf x = 2 → orderOf y = 2 → IsConj x y) →
    ∀ t ∈ (S : Subgroup G), orderOf t = 2 → (∀ x ∈ (S : Subgroup G), x * t = t * x) →
    ∀ r ∈ (S : Subgroup G), orderOf r = 2 → r ≠ t →
      ∃ y ∈ centralizer ({t * r} : Set G), y * r * y⁻¹ = t

/-- **LEAF C10.N5c `NineConj`**: "since 8 divides `|C_G(tr)|`, `r = t^y` for some `y ∈ C_G(tr)`".

Route.
* `DihFourConjProp`, with `S ≅ D_{2n}` (`BenderCtx.sylow`, `G` simple non-abelian) and one class
  of involutions (`I.toolkit.fus`).
* `|S| > |S ∩ E| ≥ 4`, since `S ⊄ E`, so `n ≥ 4`.
* `r ≠ t`, since `t ∈ E` and `r ∉ E`. -/
def NineConjProp (I : C4Inputs) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (B : BenderSetup G) (C : Case2Ctx6 B),
    Hyp9 G B C → ¬ (B.S : Subgroup G) ≤ layerIn C.D.M →
      ∀ r ∈ (B.S : Subgroup G) ⊓ C.D.M, orderOf r = 2 → r ∉ layerIn C.D.M →
        ∃ y ∈ centralizer ({B.t * r} : Set G), y * r * y⁻¹ = B.t

/-- **LEAF C10.N5d `NineRy`**: "`R^y` is a `π'`-subgroup of `U` inverted by `r`. Lying in
`[r,B]KF(U)`, `R^y ∩ BKF(U)` is trivial by (7), and this implies `|R^y| ≤ p` by (8)".

Route. Put `X := conjSub y R`.
* `X ≤ C(y r y⁻¹) = C(t) = H` and `X` is odd, so `X ≤ U` (`H = U S`, `I.toolkit.split`).
* `y t y⁻¹ = r` (from `y ∈ C(tr)` and `y r y⁻¹ = t`), so `r` inverts `X`.
* `π(X) = π(k')` is disjoint from `π`. We have `π = π(K₀) ⊆ π(K) ⊆ π(k)` and
  `gcd(k, k') = 1` (`|k − k'| = 1`).
* `N := B₀ K F(U)` is a subgroup (`K ⊴ U∩M = KB₀`, `F(U) ⊴ U`), and `r` normalizes `B₀`, `K` and
  `F(U)`. An element of `N` inverted by `r` lies in `[r, B₀] K F(U)` (`I.toolkit.c15` on
  `N/KF(U)`). That is a `π`-group (Seven conjuncts 4 and 6, and `π(F(U)) = π`). So `X ∩ N = 1`.
* `|X| |N| = |XN| ≤ |U|` (product of subgroups with trivial intersection), so `|X| ≤ |U : N|`.
* Pick `P ≤ F` of prime order `p` (Cauchy, `F ≠ 1`). `Case2EightAll` gives `|U : N| ≤ p` and
  `p ∣ |K₀|`. -/
def NineRyProp (I : C4Inputs) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (B : BenderSetup G) (C : Case2Ctx6 B),
    Hyp9 G B C → ∀ q k k' : ℕ, NineKData C.D q k k' →
      ∀ r ∈ (B.S : Subgroup G) ⊓ C.D.M, orderOf r = 2 → r ∉ layerIn C.D.M →
      ∀ R : Subgroup G, R ≤ layerIn C.D.M → R ≤ centralizer ({r} : Set G) →
        Nat.card R = k' → Inverts B.t R →
      ∀ y ∈ centralizer ({B.t * r} : Set G), y * r * y⁻¹ = B.t →
        ∃ p : ℕ, p.Prime ∧ p ∣ Nat.card C.D.K0 ∧ Nat.card R ≤ p

/-! ## 3. Arithmetic (proved) -/

/-- `q ≥ 7` from `K₀ ≠ 1` (indeed `q ≥ 11`). -/
theorem nine_seven_le {q k k' c : ℕ} (hk : Even k) (hc : Odd c) (h3 : 3 ≤ c) (hd : c ∣ k)
    (h5 : 5 ≤ q)
    (hq : (2 * k = q + 1 ∧ 2 * k' = q - 1) ∨ (2 * k = q - 1 ∧ 2 * k' = q + 1)) : 7 ≤ q := by
  obtain ⟨m, rfl⟩ := hd
  have hm : Even m := by
    rcases Nat.even_mul.mp hk with h | h
    · exact absurd h (Nat.not_even_iff_odd.mpr hc)
    · exact h
  obtain ⟨j, rfl⟩ := hm
  rcases Nat.eq_zero_or_pos j with hj | hj
  · subst hj
    simp at hq
    omega
  · have h6 : 6 ≤ c * (j + j) := by nlinarith
    omega

/-- The contradiction closing (9): `k' = |R^y| ≤ p ≤ |K| ≤ k/2`, while `k' ≥ k − 1` and `k ≥ 6`. -/
theorem nine_sylow_arith {q k k' c p : ℕ} (hk : Even k) (hc : Odd c) (h3 : 3 ≤ c) (hd : c ∣ k)
    (h5 : 5 ≤ q)
    (hq : (2 * k = q + 1 ∧ 2 * k' = q - 1) ∨ (2 * k = q - 1 ∧ 2 * k' = q + 1))
    (hpc : p ≤ c) (hkp : k' ≤ p) : False := by
  obtain ⟨m, rfl⟩ := hd
  have hm : Even m := by
    rcases Nat.even_mul.mp hk with h | h
    · exact absurd h (Nat.not_even_iff_odd.mpr hc)
    · exact h
  obtain ⟨j, rfl⟩ := hm
  rcases Nat.eq_zero_or_pos j with hj | hj
  · subst hj
    simp at hq
    omega
  · have h6 : 6 ≤ c * (j + j) := by nlinarith
    have h2c : 2 * c ≤ c * (j + j) := by nlinarith
    omega

/-! ## 4. Assemblies (proved) -/

/-- `Case2NotA7Impl9` from the A₇ chain. -/
theorem notA7_of_leaves (I : C4Inputs) (h0 : SixEmbedProp I) (h1 : A7KProp I)
    (h2 : A7VProp I) (h3 : A7UProp I) (h4 : A7InvNormalProp I) (h5 : A7IndexHProp I)
    (h6 : A7CosetProp I) (h7 : A7SmallIndexProp I) (h8 : CoreIndexProp) :
    Case2NotA7Impl9 I := by
  intro G _ _ hbc B hc2 C hplus hseven height
  refine ⟨fun e => ?_⟩
  have hA : IsA7Case C.D := ⟨e⟩
  have hH : Hyp9 G B C := ⟨hbc, hc2, hplus, hseven, height⟩
  have f1 := h1 G B C hH hA (h0 G hbc B C)
  have f2 := h2 G B C hH hA f1
  have f3 := h3 G B C hH hA f1 f2
  have f4 := h4 G B C hH hA f1 f2 f3
  have f5 := h5 G B C hH hA f1 f2 f3 f4
  have f6 := h6 G B C hH hA f1 f2 f3 f4 f5
  obtain ⟨hi, hd⟩ := h7 G B C hH hA f1 f2 f3 f4 f5 f6
  exact h8 G hbc.simple C.D.M C.D.M_coatom.1 7 (by norm_num) hd hi

/-- `Case2NineImpl9` from the (9) chain. -/
theorem nine_of_leaves (I : C4Inputs) (h0 : SixEmbedProp I) (hS : NineShapeProp I)
    (hK : NineKProp I) (hZ : NineCenterProp I) (hO : NineOuterInvProp I) (hR : NineRProp I)
    (hC : NineConjProp I) (hY : NineRyProp I) : Case2NineImpl9 I := by
  intro G _ _ hbc B hc2 C hplus hseven height hA7
  have hH : Hyp9 G B C := ⟨hbc, hc2, hplus, hseven, height⟩
  have hnA : ¬ IsA7Case C.D := fun ⟨e⟩ => hA7.elim e
  obtain ⟨p, e, hp, hsh⟩ := hS G B C hH hnA
  obtain ⟨k, k', hkd⟩ := hK G B C hH (h0 G hbc B C) p e hsh
  have hiso := hZ G B C hH p e hsh k k' hkd
  obtain ⟨hke, hk'o, hq, hdvd, h3, hodd⟩ := hkd
  refine ⟨p, e, hp, hsh.1, nine_seven_le hke hodd h3 hdvd hsh.2.1 hq, hiso, ?_⟩
  by_contra hSE
  obtain ⟨r, hr, hr2, hrE⟩ := hO G B C hH hSE
  have hkd' : NineKData C.D (p ^ e) k k' := ⟨hke, hk'o, hq, hdvd, h3, hodd⟩
  obtain ⟨R, hRE, hRc, hRk, hRt⟩ := hR G B C hH p e hsh hiso k k' hkd' r hr hr2 hrE
  obtain ⟨y, hy, hyr⟩ := hC G B C hH hSE r hr hr2 hrE
  obtain ⟨p', hp', hpK, hRp⟩ :=
    hY G B C hH (p ^ e) k k' hkd' r hr hr2 hrE R hRE hRc hRk hRt y hy hyr
  have hK0K : Nat.card C.D.K0 ∣ Nat.card C.D.K :=
    Subgroup.card_dvd_of_le (inf_le_right : C.D.K0 ≤ C.D.K)
  have hpc : p' ≤ Nat.card C.D.K := Nat.le_of_dvd Nat.card_pos (dvd_trans hpK hK0K)
  exact nine_sylow_arith hke hodd h3 hdvd hsh.2.1 hq hpc (hRk ▸ hRp)


/-- `C4Inputs` together with the `L2F` input `L2OuterInvolutionProp` (design pass 10 §3.4), which
step (9) needs for an outer involution `r` of `L₂(q)`. -/
structure C4Inputs10 : Prop extends C4Inputs where
  /-- `C_{L₂(q)}(r)` for an outer involution `r`: a cyclic `R` of order `k'` inverted by every
  involution of `C_L(r)`. -/
  l2outer : L2OuterInvolutionProp

end Work.GW2
