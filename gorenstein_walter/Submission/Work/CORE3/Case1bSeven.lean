import Mathlib
import Submission.Work.CORE3.Defs
import Submission.Work.CORE2A.Basic
import Submission.Work.CORE3.Case1bEightNineDefs
import Submission.Work.CORE3.VUInvSetTrivial
import Submission.Work.CORE3.InvSetVUSingleton
import Submission.Work.CORE3.CosetInvCountLeSix
import Submission.Work.CORE3.CosetInvCountNeFive
import Submission.Work.CORE3.Case1bDStructure
import Submission.Work.CORE3.SevenOddCentralizer
import Submission.Work.CORE3.J4.J4U3
import Submission.Work.CORE3.SevenConjK
import Submission.Work.CORE3.Case1bSevenInvInI
import Submission.Work.CORE3.J4U3V18
import Submission.Work.CORE3.Case1bSevenNeSix

namespace Work.CORE3

open Subgroup
open Work.GW2

/-! ## Assembly of Bender (7)

The two remaining inputs of Bender's (7) are supplied by the sibling modules

* `Work.CORE3.Case1bSevenU3OfConjK` (`|U| = 3`), fed by `Work.CORE3.SevenConjK_conj`
  ("`X` is conjugate into `K`, `N_G(X)` into `Ĥ`");
* `Work.CORE3.Case1bSevenLeFour` (`cosetInvCount Ĥ y ≤ 4`),

while the *fourth* involution of the coset, `4 ≤ cosetInvCount Ĥ y`, is
`Work.CORE3.Case1bSevenInvInI` (proved, from the factorisation `y = d * v`).

The two halves are assembled in `case1bSeven_of_le_four` below; the main theorem
`Work.CORE3.Case1bSeven` is then immediate. -/

/-- **Assembly of Bender (7)** from its two halves: with `|U| = 3` and `cosetInvCount Ĥ y ≤ 4`,
the `J₄`-count is pinned to `4` by `Work.CORE3.Case1bSevenInvInI` (`4 ≤ cosetInvCount Ĥ y`). -/
theorem case1bSeven_of_le_four {G : Type} [Group G] [Finite G]
    (I : Case1Inputs) (hBc : BenderCtx G) (B : BenderSetup G) (h1 : Case1 B)
    (D : Case1bData B) {y : G} (hy2 : orderOf y = 2) (hyH : y ∉ B.Hhat)
    {X : Subgroup G} (hXH : X ≤ B.Hhat) (hXne : X ≠ ⊥) (hXodd : Odd (Nat.card X))
    (hinv : ∀ x ∈ X, y * x * y⁻¹ = x⁻¹)
    (hC : Even (Nat.card (Subgroup.centralizer (X : Set G))))
    (hN : Even (Nat.card (Subgroup.normalizer (X : Set G))))
    (hU3 : Nat.card B.U = 3) (hle : cosetInvCount B.Hhat y ≤ 4) :
    Nat.card B.U = 3 ∧ cosetInvCount B.Hhat y = 4 :=
  ⟨hU3,
    le_antisymm hle
      (Work.CORE3.Case1bSevenInvInI G I hBc B h1 D hU3 hy2 hyH hXH hXne hXodd hinv hC)⟩

/-- **`4 ≤ |I_Ĥ(y)| = cosetInvCount Ĥ y` from the `J₃`-exclusion.**  `X` is a three-element subset
of the inverted set `I_Ĥ(y)` (because `|X| = 3`), and `n = 3` is excluded by hypothesis. -/
theorem four_le_cosetInvCount_of_ne_three {G : Type} [Group G] [Finite G]
    (I : Case1Inputs) (hBc : BenderCtx G) (B : BenderSetup G) (h1 : Case1 B)
    (D : Case1bData B) {y : G} (hy2 : orderOf y = 2)
    (hyH : y ∉ B.Hhat) {X : Subgroup G} (hXH : X ≤ B.Hhat) (hXne : X ≠ ⊥)
    (hXodd : Odd (Nat.card X)) (hinv : ∀ x ∈ X, y * x * y⁻¹ = x⁻¹)
    (hne3 : cosetInvCount B.Hhat y ≠ 3) :
    4 ≤ cosetInvCount B.Hhat y := by
  have hy : y * y = 1 := ((orderOf_eq_two_iff_mul_self y).mp hy2).1
  have hyi : y⁻¹ = y := inv_eq_of_mul_eq_one_right hy
  -- `|X| = 3`
  have hXcard : Nat.card X = 3 :=
    Work.CORE3.J4.card_X_eq_three I hBc B h1 D hy2 hyH hXH hXne hXodd hinv
  -- `X ⊆ I_Ĥ(y)`
  have hXI : (X : Set G) ⊆ invSetIn B.Hhat y := by
    intro x hx
    exact ⟨hXH hx, by simpa [hyi] using hinv x hx⟩
  -- `3 ≤ n`
  have hge3 : 3 ≤ cosetInvCount B.Hhat y := by
    rw [← ncard_invSetIn_eq_cosetInvCount B.Hhat y hy hyH]
    have hcoe : (X : Set G).ncard = Nat.card X := Nat.card_coe_set_eq (X : Set G)
    calc (3 : ℕ) = (X : Set G).ncard := by rw [hcoe, hXcard]
      _ ≤ (invSetIn B.Hhat y).ncard := Set.ncard_le_ncard hXI (Set.toFinite _)
  omega

/-- Bender 1981 §3, p. 224, item (7) (text in `Submission/Work/lead_gw_prior/_bender3.txt` and
`bender2_1981.txt`).  Setting: `G` a minimal counterexample (`BenderCtx`), `B` a Bender setup,
`Case1 B`, `V = O₂(Ĥ)` of type `(2,2)` (`Case1bData B`), `U = O(Ĥ)`, `VU = V ⊔ U`, `|Ĥ : VU| = 6`,
`Ĥ/U ≅ S₄`, `C_Ĥ(V) = VU`.

If an involution `y ∉ Ĥ` inverts a nontrivial odd-order subgroup `X ≤ Ĥ` whose **`G`-centralizer
and `G`-normalizer** have even order (Bender: "Suppose `y ∈ J_n` inverts some `2'`-subgroup
`X ≠ 1` of `Ĥ` such that `C(X)` and `N(X)` have even order"), then `|U| = 3` and the coset `yĤ`
carries exactly four involutions (Bender: "Then `|U| = k = 3`, `n = 4`").

Note `n ≥ |X| ≥ 3` is automatic (`1 ≠ X ⊆ invSetIn Ĥ y`), `n ≤ 6` holds by Bender (5)
(`Work.CORE3.CosetInvCountLeSix`), and `n ≠ 5` by `Work.CORE3.CosetInvCountNeFive`; the content
of the claim is `|U| = 3` together with the exclusion of `n = 3` and `n = 6`.

Route (Bender, verbatim): "For `X` must be conjugate to a subgroup of `K`, say `X ⊆ Ĥ^g`, and
satisfies `F(U) ⊆ C_Ĥ(X) ≤ N_Ĥ(X) ≤ Ĥ^g`; and since `V^g ≰ Ĥ`, it follows that
`C_{Ĥ^g}(V^g) = 1`, hence `|F(U)| = 3` and therefore `|U| = 3`.  Lying in
`Ĥ^g = (Ĥ ∩ Ĥ^g)V^g`, `y` centralizes some involution in `Ĥ ∩ Ĥ^g`, but does not normalize the
subgroup of order `9` in `Ĥ ∩ Ĥ^g = N_Ĥ(X)`."

Two derived hints available in the workspace: (i) `C_Ĥ(X)` has **no** involution: if `s ∈ C_Ĥ(X)`
is an involution then either `s ∉ V`, whence `X·U/U ≤ C_{Ĥ/U}(sU) ≤ C_{S₄}(s̄)` is an odd-order
subgroup of a 2-group (order `4` or `8`) and so `X ≤ U`, or `s ∈ V^♯`, whence
`X ≤ C_Ĥ(s) ⊆ VU` (as `C_{S₄}(V₄) = V₄`) and again `X ⊆ U`; both contradict Bender's (5)
(`Work.CORE3.VUInvSetTrivial`: no involution outside `Ĥ` inverts a nontrivial element of `VU`),
since `y ∉ Ĥ` inverts `1 ≠ X ⊆ U ⊆ VU`.  Hence the even-order witness of `|C_G(X)|` lies outside
`Ĥ`: `∃ s ∈ C_G(X)`, `s` an involution, `s ∉ Ĥ`.  (ii) Then `X ≤ C_G(s)` is an odd-order
subgroup of `C_G(s) ≅ H = U₀ ⋊ S₀` and `C_G(s)/U₀` is a 2-group, so `X ⊆ U₀ = O(C_G(s))`, a
conjugate of `U`.

Data from the concrete model `A₇` (`Ĥ = N(V)`, `|U| = 3`): for a `J₄`-coset exactly three of its
four involutions invert an order-`3` subgroup `X ≤ Ĥ` with `|C_G(X)| = 36` (even) and even
`|N_G(X)|`; the remaining involution inverts no odd-order element of `Ĥ`.

## Shape of the proof (skeleton)

Write `I = invSetIn B.Hhat y = I_Ĥ(y)`, whose cardinality is the number of involutions of the
coset `y Ĥ` (`Work.CORE3.ncard_invSetIn_eq_cosetInvCount`) and equals `cosetInvCount B.Hhat y`.
The claim splits into:

* **`|U| = 3`** (Bender (7), first half): Bender's §3 numerics (4) + (6) + (8) + (9) force
  `b₄ ≠ 0`, whence `|U| = |K| = 3` (`Work.CORE3.cardU_eq_three_of_case1b`, via the bounds
  `n ≤ 4` and `n ≠ 3` on coset involution counts, i.e. Bender (6)+(7));
* **`|I| ≥ 4`** (second half (a)): `X ⊆ I` contributes `|X| = 3` elements and
  `Work.CORE3.J4.J4Step7GStruct`-style structure (`X` is a conjugate of `U`, `y = d * v` with
  `d ∈ Ĥ ⊓ Ĥ^g` an involution centralized by `y`) contributes the fourth;
* **`|I| ≤ 4`** (second half (b)): `I ⊆ D := Ĥ ⊓ Ĥ^y` (`invSetIn_subset_inf_conjSub` below);
  `4 ≤ |I|` gives `D · VU = Ĥ` and `|D : D ⊓ VU| = 6` (`Work.CORE3.Case1bDStructure`), the
  triviality of the stabilizer (`D ⊓ VU = ⊥`, `Work.CORE3.J4.J4DTriv`) then forces `|D| = 6`,
  hence `D ≅ S₃`, and a finite count in `S₃` (`ncard_inverted_eq_four_of_cardSix`) gives
  `|I| ≤ 4`.

## Status

Proved (sorry-free, axiom-clean, in `Submission/Work/CORE3/`) and available to the assembly:

* `SevenOddCentralizer` — an odd-order element of `Ĥ` commuting with an involution of `Ĥ` lies in
  `U`.  Consequences: `C_Ĥ(X)` is odd, and as `X` lies in a Sylow `3`-subgroup `P ⧸ Ĥ` (abelian,
  order `9`) one gets `C_Ĥ(X) = P` and `|N_Ĥ(X)| ≤ 18`;
* `SevenNoInvolCentralizer` — hint (i): `C_Ĥ(X)` has no involution, so the even-order witness of
  `|C_G(X)|` lies outside `Ĥ`;
* `SevenConjU` — hint (ii), given `|U| = 3`: `X = conjSub g B.U`, hence `|X| = 3`,
  `N_G(X) = Ĥ^g`, `Ĥ^g = (Ĥ ⊓ Ĥ^g) ⊔ V^g` and `Ĥ ⊓ V^g = ⊥`;
* in the library: `Case1bDStructure`, `J4.J4DTriv`, `BenderSix`, `CosetInvCountLeSix`,
  `CosetInvCountNeFive`.

Delegated, in flight: `SevenInvInI` (the fourth involution `d ∈ I_Ĥ(y)`, i.e. `4 ≤ |I_Ĥ(y)|`).

Still missing, and both parts of the same Bender §3 cluster that the area is finishing in
parallel (`Work.CORE3.J4.J4SevenCore` already carries *this* statement, waiting for
`Work.CORE3.J4.J4SevenLeFour` and `Work.CORE3.J4.J4SevenNeThree`):

* `|U| = 3` — §3 numerics (4) + (6) + (8) + (9): `b₄ ≠ 0` is forced by (4) + (8), a `b₄`-coset
  yields (through `J4.J4CosetStep`) an involution with exactly the configuration of this lemma,
  and Bender (7) gives `|U| = 3` (`J4.J4U3`, `BenderSevenU3`; still `sorry`-dependent through
  `FourCosetForcesU`);
* `|I_Ĥ(y)| ≤ 4` — Bender (6) + (7): `n ≠ 6` for a coset with `4 ≤ n` carrying such an `X`.

With those, the file is a short assembly: the first conjunct comes from (`J4.J4U3`), and for the
second, `3 ≤ n` (from `1 ≠ X ⊆ I_Ĥ(y)`), `n ≠ 5`, `n ≤ 4` and `4 ≤ n` (`SevenInvInI`) give
`n = 4`. -/
theorem Case1bSeven (G : Type) [Group G] [Finite G] (I : Work.CORE3.Case1Inputs)
    (hBc : Work.GW2.BenderCtx G) (B : Work.GW2.BenderSetup G) (h1 : Work.GW2.Case1 B)
    (D : Work.GW2.Case1bData B) :
    ∀ y : G, orderOf y = 2 → y ∉ B.Hhat → ∀ X : Subgroup G, X ≠ ⊥ → Odd (Nat.card X) →
      X ≤ B.Hhat → (∀ x ∈ X, y * x * y⁻¹ = x⁻¹) →
      Even (Nat.card (Subgroup.centralizer (X : Set G))) →
      Even (Nat.card (Subgroup.normalizer (X : Set G))) →
      Nat.card B.U = 3 ∧ Work.GW2.cosetInvCount B.Hhat y = 4 := by
  intro y hy2 hyH X hXne hXodd hXH hinv hC hN
  -- ### The first half: `|U| = 3`
  -- Bender's (7) in the repaired form `Work.CORE3.J4U3V18` (design pass 23 plus the
  -- contradiction route through `Work.CORE3.J4U3V18Aux.LcFailsOfCardU`).
  have hU3 : Nat.card B.U = 3 :=
    Work.CORE3.J4U3V18 G I hBc B h1 D hy2 hyH X hXH hXne hXodd hinv hC hN
  -- ### The second half: `cosetInvCount Ĥ y = 4`
  have h5 : ∀ z : G, orderOf z = 2 → z ∉ B.Hhat →
      invSet (pCoreIn 2 B.Hhat ⊔ B.U) z = {1} :=
    VUInvSetTrivial G I hBc B h1 D
  have hle6 : cosetInvCount B.Hhat y ≤ 6 :=
    cosetInvCount_le_six G I hBc B h1 D h5 y hy2 hyH
  have hne5 : cosetInvCount B.Hhat y ≠ 5 :=
    CosetInvCountNeFive G I hBc B h1 D h5 y hy2 hyH
  have hne6 : cosetInvCount B.Hhat y ≠ 6 := by
    -- `Work.CORE3.Case1bSevenNeSix` (Bender (6) in the strong form, proved): no coset of `Ĥ`
    -- carrying an involution that inverts such an `X` carries six involutions.  See the route
    -- recorded in `J4/NOTES_J4SevenD6.md` §(1)-(2) and in `SevenHints.lean`; it needs neither
    -- `|U| = 3` nor `|Ĥ ⊓ Ĥ^y| = 6`.
    intro h6
    exact Case1bSevenNeSix G I hBc B h1 D hU3 hy2 hyH hXH hXne hXodd hinv hC h6
  have hge4 : 4 ≤ cosetInvCount B.Hhat y :=
    Case1bSevenInvInI G I hBc B h1 D hU3 hy2 hyH hXH hXne hXodd hinv hC
  exact ⟨hU3, by omega⟩

/-- **Auxiliary (proved).**  For an involution `y`, the inverted set `I_Ĥ(y) = invSetIn B.Hhat y`
is contained in `D = Ĥ ⊓ Ĥ^y`: if `h ∈ Ĥ` and `y * h * y⁻¹ = h⁻¹` then conjugating by `y` sends
`h` back into `Ĥ`.  This is the elementary half of Bender's `I_Ĥ(y) ⊆ Ĥ ⊓ Ĥ^y`, needed for the
`|I_Ĥ(y)| ≤ 4` bound. -/
theorem invSetIn_subset_inf_conjSub {G : Type} [Group G] [Finite G] (B : BenderSetup G) {y : G}
    (hy : y * y = 1) : invSetIn B.Hhat y ⊆ B.Hhat ⊓ conjSub y B.Hhat := by
  intro h hh
  obtain ⟨hhH, hhconj⟩ := hh
  refine ⟨hhH, ?_⟩
  show h ∈ B.Hhat.map (MulAut.conj y).toMonoidHom
  rw [Subgroup.mem_map]
  refine ⟨h⁻¹, B.Hhat.inv_mem hhH, ?_⟩
  show y * h⁻¹ * y⁻¹ = h
  have h3 : (y * h * y)⁻¹ = h := by rw [hhconj, inv_inv]
  have h4 : (y * h * y)⁻¹ = y⁻¹ * h⁻¹ * y⁻¹ := by group
  rw [h4] at h3
  simpa [inv_eq_of_mul_eq_one_right hy] using h3

/-- **Auxiliary (proved).**  If `s ∈ Ĥ` is an involution and `h ∈ Ĥ` has odd order and commutes
with `s`, then `h ∈ B.U`.  This is `Work.CORE3.SevenOddCentralizer`; the consequence used below
is that `C_Ĥ(X)` is odd (hence, `X` sitting in an abelian Sylow `3`-subgroup of order `9`,
`C_Ĥ(X)` is *that* Sylow `3`-subgroup and `|N_Ĥ(X)| ≤ 18`). -/
theorem odd_centralizer_is_U {G : Type} [Group G] [Finite G] (I : Case1Inputs)
    (hBc : BenderCtx G) (B : BenderSetup G) (h1 : Case1 B) (D : Case1bData B)
    {s h : G} (hs : s ∈ B.Hhat) (hs2 : orderOf s = 2) (hh : h ∈ B.Hhat)
    (hcomm : s * h = h * s) (hodd : Odd (orderOf h)) : h ∈ B.U :=
  Work.CORE3.SevenOddCentralizer G I hBc B h1 D hs hs2 hh hcomm hodd

end Work.CORE3
