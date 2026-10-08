/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gorenstein–Walter formalisation team (area CORE4, `Work.CORE4`)

# AREA CORE4 — the `A₇` chain of §4, corrected interface

Bender 1981, §4, p. 226 ("Now we can eliminate the case `E/Z(E) ≅ A₇`").

The design-pass-10 chain `Defs10.lean` (leaves `A7KProp` … `CoreIndexProp`, assembly
`notA7_of_leaves`) has a circularity in the middle, reported by the prover of `CORE4/A7U.lean`
(`A7U.lean`, "Verdict"): leaf A3 `A7UProp` contains the conjunct `K = Z(U)`, which can only be
reached through `|U : U ∩ M| = 3` — i.e. through Bender's (8) *after* the exceptional case
`I_U(s) ⊴ Ĥ` has been excluded — while leaf A4 `A7InvNormalProp` (the exclusion of that case)
was designed to consume `A7Facts3 ⊇ (K = Z(U))`.

The circle is broken as follows. The only use of `K = Z(U)` in A4 is to obtain `N_G(K) = Ĥ`,
and that is available in the exceptional case without it:

* `U = O(Ĥ)` (Theorem 2.6) is normal in `Ĥ`, and `s ∈ Ĥ`;
* with `I := I_U(s) = invSet U s` (a subgroup, by (8), case 3 of its proof, where
  `I = F(C_U(Q))`), Bender's 1.5 (`I.toolkit.c15`) gives that `I` is **abelian** and normal in
  `U`; the cardinality clause `|I| · |U ⊓ C(s)| = |U|` together with `I ∩ C(s) = 1` gives
  `U = I · C_U(s)`;
* `K = I_{U∩M}(s) ⊆ I`, so `K` commutes with `I`; and `K ≤ E = layerIn M`, `B₀ = F ≤ C(E)`
  (Bender's (4), `Case2Pre.F_cent`) kills the `C_U(s)` factor (`C_U(s)` is a `3`-group and
  `Aut(K) ≅ C₂`, so it centralises `K`);
* hence `K ≤ Z(U)`, so `K ⊴ U ⊴ Ĥ`, so `N_G(K) = Ĥ` by maximality of `Ĥ` and simplicity of `G`
  (`K ≠ 1`, `K ≤ U ≤ Ĥ ≠ ⊤`).  Bender's `K*` argument then runs as printed.

So the leaves below take `A7UData` (the four honest conjuncts of `A7Facts3`, without `K = Z(U)`)
and produce `¬ Case2InvNormal` (`A7InvNormalFrom`), then `A7Facts5`, `A7Facts6` and finally
`|G : M| ≤ 7`, `7 ∣ |M|`; `CoreIndexProp` (proved here) closes the contradiction.

This file contains the interface (`A7UData`, `A7Mid`) and the proved leaf `CoreIndexProp`.
-/
import Mathlib
import Submission.Work.CORE4.Defs10

open scoped MatrixGroups

namespace Work.CORE4

open Work.GW2 Subgroup

set_option linter.style.haveILetI false

variable {G : Type} [Group G] [Finite G]

/-- **`A7Facts3` without the `K = Z(U)` conjunct.**  Bender p. 226: "by (7) and (8), `U` is a
`3`-group.  Then `O(M) = B = F`" — this is exactly the part of `A7Facts3` that the rest of the
p. 226 argument uses (the conjunct `K = Z(U)` is only a convenient way to see `N_G(K) = Ĥ`, and
`K ⊴ U ⊴ Ĥ` is available directly).

`A7UData B D` is:
* `IsPGroup 3 B.U` (`U` is a `3`-group);
* `D.B0 = D.F` (Bender's `B = F`);
* `oddCoreIn D.M = D.F` (Bender's `O(M) = F`);
* `∀ X ≤ D.M`, `|X|` odd → `|X| ≤ 21 · |X ⊓ F|` (the form of "`M/F ≅ A₇`" used in the coset
  estimate, `A7ModelProp`'s fourth clause). -/
def A7UData (B : BenderSetup G) (D : Case2Data B) : Prop :=
  IsPGroup 3 B.U ∧ D.B0 = D.F ∧ oddCoreIn D.M = D.F ∧
    ∀ X : Subgroup G, X ≤ D.M → Odd (Nat.card X) →
      Nat.card X ≤ 21 * Nat.card (X ⊓ D.F : Subgroup G)

/-- The bundle handed from the middle of the `A₇` chain to the counting (`A7Facts6`, `A7Facts5`):
`A7UData`, the exclusion of the exceptional case `I_U(s) ⊴ Ĥ`, and Bender's index `3`. -/
def A7Mid (B : BenderSetup G) (D : Case2Data B) : Prop :=
  A7UData B D ∧ ¬ Case2InvNormal B D ∧ A7Facts5 B D

/-! ## The corrected `A₄` chain (design pass 15 of the lead, copied here as `Work.CORE4.C15`)

The design files `_design_gw/Core15C4.lean` (namespace `Work.GW2.C15`) and
`NOTES_LEAD_gw_design15.md` §1 settle the `A₃ ↔ A₄` circle of design pass 10 by splitting Bender's
p. 226 paragraph "Suppose `I_U(s) ⊲ Ĥ`" into the pieces `A4i`, `A4a`, `A4s`, `A4b`, `A4c`.
The statements are copied here (area `CORE4`, namespace `Work.CORE4.C15`) so that the leaves can
be requested and the assembly written without importing a design file. -/

namespace C15

/-- **A3m**, the `A7Facts3`-without-`K = Z(U)` leaf in bundled form (the `A₇`-case version of
`A7UData`): from the §4 budget plus `A7Facts1` (`|K| = |F| = 3`) and `A7Facts2` (`V`, `S ≤ E`). -/
def A7UMinusProp (I : C4Inputs) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (B : BenderSetup G) (C : Case2Ctx6 B),
    Hyp9 G B C → IsA7Case C.D → A7Facts1 C.D → A7Facts2 B C.D → A7UData B C.D

/-- **A4i (pure group theory).** If an involution `s` inverts every element of a subgroup `I` and
of a subgroup `R` of odd order, and `R` normalizes `I`, then `R` centralizes `I`.

Proof: for `k ∈ R`, `x ∈ I`, put `y := k x⁻¹ k⁻¹ ∈ I` (as `R ≤ N(I)`).  Then
`s y s⁻¹ = y⁻¹ = k x k⁻¹`, while expanding the left side with `s k s⁻¹ = k⁻¹` and
`s x s⁻¹ = x⁻¹` gives `k⁻¹ x k`.  So `k²` centralizes `x`; since `|k|` is odd,
`k ∈ ⟨k²⟩`, hence `k` centralizes `x`. -/
def InvCentralizesProp : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (s : G) (I R : Subgroup G),
    Inverts s I → Inverts s R → R ≤ normalizer (I : Set G) → Odd (Nat.card R) →
      R ≤ centralizer (I : Set G)

/-- `InvCentralizesProp`, proved (see the proof sketch in the docstring above).  Available as a
backup / cross-check for the leaf `CORE4/NotA7/A4i`. -/
theorem inv_centralizes : InvCentralizesProp := by
  intro G _ _ s I R hI hR hRI hRodd k hk
  rw [Subgroup.mem_centralizer_iff]
  intro x hx
  have hkN : ∀ y : G, y ∈ I ↔ k * y * k⁻¹ ∈ I := (Subgroup.mem_normalizer_iff.mp (hRI hk))
  have hy : k * x⁻¹ * k⁻¹ ∈ I := (hkN x⁻¹).mp (I.inv_mem hx)
  have hx' : s * x⁻¹ * s⁻¹ = x := by
    rw [show s * x⁻¹ * s⁻¹ = (s * x * s⁻¹)⁻¹ by group, hI x hx, inv_inv]
  have hk' : s * k⁻¹ * s⁻¹ = k := by
    rw [show s * k⁻¹ * s⁻¹ = (s * k * s⁻¹)⁻¹ by group, hR k hk, inv_inv]
  have h2 : s * (k * x⁻¹ * k⁻¹) * s⁻¹ = k⁻¹ * x * k := by
    calc s * (k * x⁻¹ * k⁻¹) * s⁻¹
        = (s * k * s⁻¹) * (s * x⁻¹ * s⁻¹) * (s * k⁻¹ * s⁻¹) := by group
      _ = k⁻¹ * x * k := by rw [hR k hk, hx', hk']
  have h1 : s * (k * x⁻¹ * k⁻¹) * s⁻¹ = k * x * k⁻¹ := by
    rw [hI _ hy]
    group
  have hconj : x * k ^ 2 = k ^ 2 * x := by
    have h : k⁻¹ * x * k = k * x * k⁻¹ := h2.symm.trans h1
    calc x * k ^ 2 = k * (k⁻¹ * x * k) * k := by rw [pow_two]; group
      _ = k * (k * x * k⁻¹) * k := by rw [h]
      _ = k ^ 2 * x := by rw [pow_two]; group
  have hodd : Odd (orderOf k) :=
    Odd.of_dvd_nat hRodd (by
      have hz : Subgroup.zpowers k ≤ R := Subgroup.zpowers_le.mpr hk
      simpa [Nat.card_zpowers] using Subgroup.card_dvd_of_le hz)
  obtain ⟨m, hm⟩ := hodd
  have hpow : k ^ (2 * (m + 1)) = k := by
    rw [show 2 * (m + 1) = orderOf k + 1 by omega, pow_succ, pow_orderOf_eq_one, one_mul]
  have hcomm : ∀ n : ℕ, x * k ^ (2 * n) = k ^ (2 * n) * x := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [show 2 * (n + 1) = 2 * n + 2 by omega, pow_add]
      calc x * (k ^ (2 * n) * k ^ 2) = (x * k ^ (2 * n)) * k ^ 2 := by rw [← mul_assoc]
        _ = (k ^ (2 * n) * x) * k ^ 2 := by rw [ih]
        _ = k ^ (2 * n) * (x * k ^ 2) := by rw [mul_assoc]
        _ = k ^ (2 * n) * (k ^ 2 * x) := by rw [hconj]
        _ = (k ^ (2 * n) * k ^ 2) * x := by rw [← mul_assoc]
  calc x * k = x * k ^ (2 * (m + 1)) := by rw [hpow]
    _ = k ^ (2 * (m + 1)) * x := hcomm (m + 1)
    _ = k * x := by rw [hpow]

/-- **A4a.** In the exceptional case `I_U(s) ⊴ Ĥ`, `K = Z(U)`.

Route (Bender p. 226): `I := I_U(s)` is an abelian subgroup (every element is inverted by `s`);
`U = F·I` (the cardinality clause of `I.toolkit.c15`, `C_U(s) = B₀ = F`, `F ∩ I = 1`); and
`K = I_{U∩M}(s) ⊆ I`, so `I` centralizes `K`, while `F ≤ C(E)` (`Case2Pre`) and
`K ≤ E` (`Case2PrePlus`: `K = [S∩E, U∩M]`) give `K ≤ Z(U)`.  `U` is non-abelian (otherwise
`U ≤ C(F) ≤ N(F) = M` and `H = U S`, `S ≤ E ≤ M` would give `H ≤ M`, contradicting
`Case2Pre.not_H_le`).  Finally, for `z = f i ∈ Z(U) = ... ` with `f ∈ F`, `i ∈ I`:
`f ≠ 1` would force `F = ⟨f⟩` to centralize `I` and hence `U = F I` abelian; so `z ∈ I`, and
`z ∈ C(F) ≤ N(F) = M`, whence `z ∈ invSet (U ⊓ M) s = K`. -/
def A4aProp (I : C4Inputs) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (B : BenderSetup G) (C : Case2Ctx6 B),
    Hyp9 G B C → IsA7Case C.D → A7Facts1 C.D → A7Facts2 B C.D → A7UData B C.D →
      Case2InvNormal B C.D → C.D.K = (center ↥B.U).map B.U.subtype

/-- **A4s (pure `A₇` fact, GAP-verified: `_design_gw/gw15_a7conj.g`, also true verbatim in
`3.A₇`).**  For a four-group `V`, an involution `s ∈ N(V)`, and `K ≤ C(V)` of order `3` inverted
by `s`, some `e ∈ C(s)` moves `K` to a different subgroup of `N(V)`.

Model witness: `V = ⟨(12)(34),(13)(24)⟩`, `s = (12)(56)`, `K = ⟨(567)⟩`, `e = (15)(26)(374)`,
giving `K^e = ⟨(123)⟩`. -/
def A7S4ConjProp : Prop :=
  ∀ (E : Type) [Group E] [Finite E], Nonempty (E ≃* alternatingGroup (Fin 7)) →
    ∀ V : Subgroup E, IsFourGroup V → ∀ s ∈ normalizer (V : Set E), orderOf s = 2 →
      ∀ K : Subgroup E, K ≤ centralizer (V : Set E) → Nat.card K = 3 → Inverts s K →
        ∃ e : E, e * s = s * e ∧ conjSub e K ≤ normalizer (V : Set E) ∧ conjSub e K ≠ K

/-- **A4b (lift of A4s to `E = E(M)`, `E/Z(E) ≅ A₇`).**  There is `e ∈ E` with `e s = s e`,
`K^e ≤ Ĥ`, `K^e ≠ K`, and `s` inverts `K^e`.

Route: apply A4s in `Ē = E/Z(E)` to `V̄, s̄, K̄` (`V ∩ Z(E) = K ∩ Z(E) = 1`, because `Z(E) ≤ O(M)`
is odd and centralized by `s`; `K ≤ U ≤ C(V)` since `U, V ⊴ Ĥ` of coprime orders; `s ∈ S ≤ Ĥ`).
Lift `ē` to `e ∈ E`.  `s^e ∈ s Z(E)` and both are involutions, with `Z(E)` central of odd order,
so `s^e = s`; hence `s = s^e` inverts `K^e`.  The preimage of `N_Ē(V̄)` is `N_E(V Z(E)) = N_E(V)`
(`V` is the Sylow 2-subgroup of `V × Z(E)`), so `K^e ≤ N_E(V) ≤ Ĥ` (`A7Facts2`, last conjunct).
`K̄^ē ≠ K̄` gives `K^e ≠ K`. -/
def A4bProp (I : C4Inputs) : Prop :=
  A7S4ConjProp →
  ∀ (G : Type) [Group G] [Finite G] (B : BenderSetup G) (C : Case2Ctx6 B),
    Hyp9 G B C → IsA7Case C.D → A7Facts1 C.D → A7Facts2 B C.D → A7UData B C.D →
      ∃ e ∈ layerIn C.D.M, e * C.D.s = C.D.s * e ∧ conjSub e C.D.K ≤ B.Hhat ∧
        conjSub e C.D.K ≠ C.D.K ∧ Inverts C.D.s (conjSub e C.D.K)

/-- **A4c (Bender p. 226, "Suppose `I_U(s) ⊲ Ĥ` … a contradiction", corrected finish).**
With `K' := K^e`, `X := U ∩ U^e`, `V := O₂(Ĥ) = O₂(H ∩ M)`:

1. `K'` centralizes `I := I_U(s)` (A4i: `K' ≤ Ĥ` normalizes `I ⊴ Ĥ`) and `F` (`F ≤ C(E)`), so
   `K' ≤ C_G(U)` (as `U = F I`).
2. `N_G(K) = Ĥ` (`K = Z(U)` is characteristic in `U = O(Ĥ) ⊴ Ĥ`, `Ĥ` is a coatom, `G` simple),
   so `U ≤ C(K') ≤ N(K') = Ĥ^e`.  And `Ĥ^e ≠ Ĥ`, else `U^e = U` and `K' = Z(U) = K`.
3. `K' ⊄ U` (else `K' ⊆ invSet (U ⊓ M) s = K`); `s ∉ V U` and `s ∉ V^e U^e` (an involution of
   `V × U` lies in `V`, hence centralizes `U ⊇ K ≠ 1`, but `s` inverts `K`; similarly with `K'`);
   `|Ĥ : V U| = 6` (`I.thm26`, second case, since `V = O₂(Ĥ)` is a four-group).
4. `T := U U^e` is a 3-subgroup of `Ĥ^e`, so `|T| ≤ 3|U|`; hence `|U : X| ≤ 3`, `U ⊴ T`,
   `U^e ≤ N(U) = Ĥ`, and `|X| ≥ |U|/3 ≥ 3` (`|U| ≥ |K F| = 9`).
5. `N_Ĥ(X) ⊇ V U, K', s` (`V` centralizes `U`; `U ≤ Ĥ^e` normalizes `U^e`; `K' ≤ U^e ⊓ Ĥ`;
   `s = s^e ∈ Ĥ ⊓ Ĥ^e`): both `3` and `2` divide `|N_Ĥ(X) : V U|`, which divides `6`, so
   `X ⊴ Ĥ`.  Likewise `N_{Ĥ^e}(X) ⊇ V^e U^e, U, s` gives `X ⊴ Ĥ^e`.
6. `X ⊴ ⟨Ĥ, Ĥ^e⟩ = G` with `1 ≠ X ≤ U < G`: this contradicts `BenderCtx.simple`. -/
def A4cProp (I : C4Inputs) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (B : BenderSetup G) (C : Case2Ctx6 B),
    Hyp9 G B C → IsA7Case C.D → A7Facts1 C.D → A7Facts2 B C.D → A7UData B C.D →
      Case2InvNormal B C.D → C.D.K = (center ↥B.U).map B.U.subtype →
      ∀ e ∈ layerIn C.D.M, e * C.D.s = C.D.s * e → conjSub e C.D.K ≤ B.Hhat →
        conjSub e C.D.K ≠ C.D.K → Inverts C.D.s (conjSub e C.D.K) → False

/-- The corrected A4: `¬ Case2InvNormal` from `A7UData` (no `K = Z(U)` hypothesis). -/
def A7InvNormalFromProp (I : C4Inputs) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (B : BenderSetup G) (C : Case2Ctx6 B),
    Hyp9 G B C → IsA7Case C.D → A7Facts1 C.D → A7Facts2 B C.D → A7UData B C.D →
      ¬ Case2InvNormal B C.D

/-- Assembly of A4 from A4a, A4s, A4b, A4c (no cycle). -/
theorem invNormalFrom_of_parts (I : C4Inputs) (ha : A4aProp I) (hs : A7S4ConjProp)
    (hb : A4bProp I) (hc : A4cProp I) : A7InvNormalFromProp I := by
  intro G _ _ B C h9 hA f1 f2 hU hInv
  obtain ⟨e, he, hes, heH, hne, hinv⟩ := hb hs G B C h9 hA f1 f2 hU
  exact hc G B C h9 hA f1 f2 hU hInv (ha G B C h9 hA f1 f2 hU hInv) e he hes heH hne hinv

/-! ## The counting leaves, in the `A7Mid` interface -/

/-- **A5 (weak form)**: `|H : H ∩ M| = |U : U ∩ M| = 3` from `U` a `3`-group and the excluded
exceptional case.  Same statement as the proved `Work.CORE4.A7IndexH` with `A7Facts3` cut down
to its first conjunct (`B₀ = F` is then derivable: `F = B₀ ⊓ F(U)` and `F(U) = U`). -/
def A7IndexHWeakProp (I : C4Inputs) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (B : BenderSetup G) (C : Case2Ctx6 B),
    Hyp9 G B C → IsA7Case C.D → A7Facts1 C.D → A7Facts2 B C.D → IsPGroup 3 B.U →
      ¬ Case2InvNormal B C.D → A7Facts5 B C.D

/-- **A6 (weak form)**: Bender p. 226, "`|J ∩ My| ≤ 21` for every involution `y ∈ G − M`", from
`A7Mid` (which supplies `A7UData`, `¬ Case2InvNormal` and `A7Facts5`). -/
def A7CosetWeakProp (I : C4Inputs) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (B : BenderSetup G) (C : Case2Ctx6 B),
    Hyp9 G B C → IsA7Case C.D → A7Facts1 C.D → A7Facts2 B C.D → A7Mid B C.D →
      A7Facts6 C.D

/-- **A7 (weak form)**: Bender p. 226, "`|G : M| ≤ 7`", and `7 ∣ |M|`. -/
def A7SmallIndexWeakProp (I : C4Inputs) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (B : BenderSetup G) (C : Case2Ctx6 B),
    Hyp9 G B C → IsA7Case C.D → A7Facts1 C.D → A7Facts2 B C.D → A7Mid B C.D →
      A7Facts6 C.D → C.D.M.index ≤ 7 ∧ 7 ∣ Nat.card C.D.M

end C15

/-- `p² ∤ p!`. -/
private theorem not_sq_dvd_factorial {p : ℕ} (hp : p.Prime) : ¬ (p * p ∣ p.factorial) := by
  intro h
  obtain ⟨q, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hp.ne_zero
  have hq : 1 ≤ q := by have := hp.two_le; omega
  rw [Nat.factorial_succ] at h
  have h2 : (q + 1) ∣ q.factorial :=
    Nat.dvd_of_mul_dvd_mul_left (by omega : 0 < q + 1) h
  have h3 : q + 1 ≤ q := (hp.dvd_factorial).mp h2
  omega

/-- **LEAF C10.A8 `CoreIndex`** (Bender 1981, p. 226, last line: "whence each `7`-subgroup of `M`
lies in all the conjugates of `M`, a contradiction").

Pure group theory: a simple group `G` has no proper subgroup `M` with `p ∣ |M|` and
`|G : M| ≤ p` for a prime `p`.

Proof.  `core_G(M) = ⊥` (`G` simple, `M ≠ ⊤`).  The left action of `G` on the `n := |G : M|`
cosets is faithful, so by `Subgroup.index_normalCore_dvd_factorial_index`
`|G| = core_G(M).index ∣ n!`.  From `p ∣ |M|` and `|G| = n · |M|` we get `p ∣ |G|`, hence
`p ∣ n!`, hence `p ≤ n ≤ p`, so `n = p`; then `p² ∣ |G| = n · |M|`, so `p² ∣ p!`, which is false. -/
theorem coreIndexProp : CoreIndexProp := by
  intro G _ _ hsimple M hM p hp hpM hindex
  have hcore : M.normalCore = ⊥ := by
    rcases hsimple.eq_bot_or_eq_top_of_normal M.normalCore with h | h
    · exact h
    · exfalso
      apply hM
      rw [eq_top_iff]
      calc M ≥ M.normalCore := Subgroup.normalCore_le M
        _ = ⊤ := h
  have hGdvd : Nat.card G ∣ M.index.factorial := by
    have h := M.index_normalCore_dvd_factorial_index
    rwa [hcore, Subgroup.index_bot] at h
  have hpG : p ∣ Nat.card G := by
    rw [← Subgroup.card_mul_index M]
    exact dvd_mul_of_dvd_left hpM _
  have hpm : p ≤ M.index := (hp.dvd_factorial).mp (dvd_trans hpG hGdvd)
  have heq : M.index = p := le_antisymm hindex hpm
  have hp2 : p * p ∣ Nat.card G := by
    rw [← Subgroup.card_mul_index M, heq]
    exact mul_dvd_mul_right hpM p
  have hp2f : p * p ∣ p.factorial := by
    have h := dvd_trans hp2 hGdvd
    rwa [heq] at h
  exact not_sq_dvd_factorial hp hp2f

end Work.CORE4
