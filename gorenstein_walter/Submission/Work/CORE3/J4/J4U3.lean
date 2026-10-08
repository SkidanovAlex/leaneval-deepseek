import Mathlib
import Submission.Work.CORE3.Defs
import Submission.Work.CORE3.VUInvSetTrivial
import Submission.Work.CORE3.Case1bDStructure
import Submission.Work.CORE3.InvSetVUSingleton
import Submission.Work.CORE3.CosetInvCountLeSix
import Submission.Work.CORE3.Case1bEightNineDefs
import Submission.Work.CORE3.J4.J4U3CentralizerOdd
import Submission.Work.CORE3.SylowDihedral
import Submission.Work.CORE3.H_eq_U_sup_S
import Submission.Work.CORE3.NormalizerPcoreEqHhat
import Submission.Work.CORE3.CentralizerPcoreEqVU
import Submission.Work.CORE3.SevenNoInvolCentralizer
import Submission.Work.CORE3.SevenConjU
import Submission.Work.CORE3.J4.J4U3ConjK
import Submission.Work.CORE2A.Basic
import Submission.Work.CORE3.J4.J4CosetStep

/-!
# `Work.CORE3.J4.J4U3`

Bender 1981 §3, p. 224, (7), first conclusion: in Case (1) of Bender's Theorem 2.10, subcase
`V = O₂(Ĥ)` of type `(2,2)`, an involution `y ∉ Ĥ` inverting a non-trivial odd-order subgroup
`X ≤ Ĥ` whose `G`-centralizer and `G`-normalizer both have even order should force `|U| = 3`
(`U = O(Ĥ) = O(H)`).

Note that `J_n` (Bender's notation) is *not* an extra hypothesis: `y ∈ J_n` merely names
`n = |I_Ĥ(y)|`; the printed statement's hypotheses are exactly the ones here (plus the evenness of
`|N_G(X)|`, which is used only for the second conclusion `n = 4`, not for `|U| = 3`).

The file collects the parts of the argument which follow from the *stated* hypotheses; the three
nontrivial inputs used below are proved in sibling modules:

* `X_le_invSetIn` — `X ⊆ I_Ĥ(y)` (immediate from `Inverts y X`);
* `X_inf_VU_eq_bot` — Bender's (5) (`Work.CORE3.VUInvSetTrivial`) gives `X ⊓ VU = ⊥`, where
  `VU = O₂(Ĥ) ⊔ O(Ĥ) ⊴ Ĥ` and `|Ĥ : VU| = 6`;
* `card_X_eq_three` — hence `|X|` divides `6`; as `|X|` is odd and `X ≠ ⊥`, `|X| = 3`
  (this injective-into-`Ĥ/VU` argument is also used by `Work.CORE3.BenderSeven_local`);
* `card_U_three_dvd` — `3 ∣ |U|` (`Work.CORE3.J4.J4U3ThreeDvd`, proved);
* `centralizer_inf_Hhat_odd` — `C_Ĥ(X)` has odd order (`Work.CORE3.J4.J4U3CentralizerOdd`,
  proved, via `C_Ĥ(x)` for `X = ⟨x⟩`).

## What this file now proves (session 2 additions)

Two new lemmas reduce the gap `J4U3_of_conj_K` to a pair of inclusions:

* `card_U_eq_three_of_le_conjSub` — **the counting reduction**: if `U ≤ Ĥ^g`, `U^g ≤ Ĥ`,
  `U ⊓ U^g = ⊥` and `|Ĥ ⊓ Ĥ^g| ≤ 6|U|`, then `|U| = 3` (the map `U × U^g → Ĥ ⊓ Ĥ^g`,
  `(u,v) ↦ uv`, is injective, so `|U|² ≤ 6|U|`, and `|U|` is odd with `3 ∣ |U|`).
* `conjSub_pCoreIn_inf_Hhat_eq_bot` — `V^g ⊓ Ĥ = ⊥` (`V^g` commutes with `U^g ⊇ X`, since
  `V ⊆ C_Ĥ(U)`; a nontrivial element of `V^g ⊓ Ĥ` would be an involution of `Ĥ` centralizing
  `X`), from which `|Ĥ ⊓ Ĥ^g| ≤ 6|U|` follows by `4·|Ĥ ⊓ Ĥ^g| = |V^g·(Ĥ ⊓ Ĥ^g)| ≤ |Ĥ^g|`
  (that bound is also available as the standalone `Work.CORE3.J4.HhatInfConjSubCardLe`).

The assembly of the reduction lives in `Submission/Work/CORE3/J4/J4U3Reduced.lean`
(`card_U_eq_three_of_le_conjSub'`, `le_conjSub_of_isMulCommutative_U`): Bender (7) follows from
`U ≤ Ĥ^g` and `U^g ≤ Ĥ` (plus `U ⊓ U^g = ⊥`), the first of which is implied by `U` abelian,
using `Work.CORE3.J4.centralizes_abelian_U` (`U` abelian ⟹ `X ≤ C_G(U)`, Bender's
`F(U) ⊆ C_Ĥ(X)`).

So the *only* remaining content is `U ≤ Ĥ^g` (equivalently `X ≤ C_G(U)`, i.e. Bender's
`F(U) ⊆ C_Ĥ(X)`, since `U` is odd and `|X| = 3`) together with `U^g ≤ Ĥ` (and `U ⊓ U^g = ⊥`,
which follows once `U = F(U)` is known).  See `NOTES_J4U3.md` for the GAP evidence that the
local (1b) structure alone admits `U` non-abelian with `X ≰ C_G(U)` (so the missing input is
global), and for the proof that `U` abelian would give `X ≤ C_G(U)` via `[Ĥ,s] ≤ C_Ĥ(U)`
(Bender's p. 223 parenthetical).

## What the hypotheses give (for the next worker)

1. `|X| = 3`, `X ⊓ VU = ⊥`, `X ⊆ I_Ĥ(y)`, `C_Ĥ(X)` odd.
2. Hence the even-order witness of `|C_G(X)|` is an involution `s ∈ C_G(X) ∖ Ĥ`
   (`Work.CORE3.SevenNoInvolCentralizer`), and `s` is conjugate to `B.t`, say `s = B.t ^ k`
   (all involutions of `G` are conjugate, `LocalToolkit.fus`); then `X^k ≤ C_G(t) = H = U ⊔ S`
   has odd order, so `X^k ≤ U` — i.e. `X ≤ U^{k⁻¹}` (`Work.CORE3.J4.J4U3ThreeDvd`).
3. Consequently `3 ∣ |U|`, and `X` is conjugate into the Hall subgroup `K = D.K = I_U(s)`
   of `F(U)`, with `N_G(X)` conjugate into `Ĥ`
   (`Work.CORE3.SevenConjK`, whose proof does not need `|U| = 3`);
   equivalently: `∃ g, X ≤ conjsSub g D.K ∧ N_G(X) ≤ conjsSub g B.Hhat`, `y ∈ N_G(X)`.
   In particular `3 ∣ |K|` and `3 ∣ |F(U)|`.

## The gap (state of the art, cross-referenced)

What remains is Bender's own final step.  With `g` as in (3) — so that `X ≤ K^g ≤ F(U)^g ⊆ U^g`,
`X ≤ Ĥ`, `N_G(X) ≤ Ĥ^g`, `y ∈ Ĥ^g` — one must show `|U| = 3`.  Bender's printed argument
("`F(U) ⊆ C_G(X) ≤ N_G(X) ≤ Ĥ^g`; and since `V^g ≰ Ĥ`, … hence `|F(U)| = 3` and therefore
`|U| = 3`") is a *sketch*: the displayed `C_{Ĥ^g}(V^g) = 1` is false as printed (that centralizer
is `(VU)^g ≠ 1`, as `V^g ≤ C(V^g)`); only `V^g ≰ Ĥ` survives verbatim (proved in
`Submission/Work/CORE3/Case1bSevenU3OfConjK.lean`, which cannot be imported here because it
imports this file).

Related facts proved elsewhere (importable or citable):

* **`U` is nilpotent**, i.e. `F(U) = U`: `U = O(Ĥ)` is the product of its normal Sylow subgroups
  `O_q(Ĥ)`, `q` odd (`Submission/Work/CORE3/C3six/NOTES_CardUThreeLocal.md`).  Hence Bender's
  "`|F(U)| = 3` and therefore `|U| = 3`" is a triviality, and local control (`h1.2`) applies to
  *every* subgroup of `U`.
* **`K ⊴ Ĥ`** (`Work.CORE3.J4.KNormalInHhat`) and the coprime decomposition
  `U = K ⊔ (U ⊓ C_G(s))` (`Work.CORE3.J4.UeqKsupCentralizer`, still a stub).
* Every involution of `C_G(X)` lies in `V^g = O₂(Ĥ)^g`
  (`Case1bSevenU3OfConjK.involution_mem_conjSub_pcore_of_mem_centralizer`, proved), so the 2-part
  of `C_G(X)` is inside `V^g` and `|C_G(X)|₂ ≤ 4`.
* The clean reduction of the whole step: `|U| ≠ 3 ⇒ ∃ Y ≠ ⊥, Y ≤ F(U), N_G(Y) ≰ Ĥ`
  (`Work.CORE3.SevenCardU_lcFails`); since `Ĥ` is a coatom, `N_G(Y) ≤ Ĥ` is *equivalent* to
  `N_G(Y) = G`, i.e. `Y ⊴ G` — impossible for the simple `G` of `BenderCtx`.
* Bender's local data alone **cannot** give `|U| = 3`: `Ĥ = C₃² ⋊ S₄` (with `S₄` acting through
  its sign quotient) satisfies every local structural requirement of (1b) with `|U| = 9` and
  `K = U` (`C3six/NOTES_CardUThreeLocal.md`, "shadow configuration").
* A GAP search over all groups of order `≤ 1000` with a valid (1b) structure (3762 groups, 160
  configurations, `|U| ∈ {3,5,7,9,11,13}`) shows that local control holds **only** for `|U| = 3`,
  and in every other case the violated subgroup is normal in `G` (`J4/NOTES_GDo_CardU3.md`).
  So `Case1bData` + local control appears to force `|U| = 3`, but the mechanism is *global*: one
  must derive, from `|U| > 3`, a nontrivial subgroup of `F(U) = U` which is normal in `G`.

The statement `J4U3_of_conj_K` below isolates precisely this remaining step; `J4U3` itself is
assembled from it and `J4U3ConjK`.  In the `A₇` model the configuration exists with `|U| = 3`
(`|C_G(X)| = 36`, `|N_G(X)| = 72`, `|I_Ĥ(y)| = 4`, `N_G(X) = Ĥ^g`, `U ≤ Ĥ^g`); a computational
search over all groups of order `≤ 1000` with a valid (1b) setup shows that the (7)-configuration
can occur with `|U| > 3` (`|U| = 5` of order `600`, `|U| = 7` of order `840`) *only* when Bender's
Case (1) fails, and then always through the second conjunct of Case (1) (local control).
-/

namespace Work.CORE3.J4

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

open Subgroup

variable {G : Type} [Group G] [Finite G]


/-- Every element of `X` lies in the inverted set `I_Ĥ(y)`. -/
theorem X_le_invSetIn (B : Work.GW2.BenderSetup G) {y : G} (hy2 : orderOf y = 2)
    {X : Subgroup G} (hXH : X ≤ B.Hhat) (hinv : Work.GW2.Inverts y X) :
    ∀ x ∈ X, x ∈ Work.CORE3.invSetIn B.Hhat y := by
  intro x hx
  refine ⟨hXH hx, ?_⟩
  show y * x * y = x⁻¹
  simpa [inv_eq_self_of_orderOf_two hy2] using hinv x hx

/-- **Bender (5) for `X`**: `X` meets `VU = O₂(Ĥ) ⊔ O(Ĥ)` trivially. -/
theorem X_inf_VU_eq_bot (I : Work.CORE3.Case1Inputs) (hBc : Work.GW2.BenderCtx G)
    (B : Work.GW2.BenderSetup G) (h1 : Work.GW2.Case1 B) (D : Work.GW2.Case1bData B)
    {y : G} (hy2 : orderOf y = 2) (hyH : y ∉ B.Hhat) {X : Subgroup G} (hXH : X ≤ B.Hhat)
    (hinv : Work.GW2.Inverts y X) :
    X ⊓ (Work.GW2.pCoreIn 2 B.Hhat ⊔ B.U) = ⊥ := by
  refine le_bot_iff.mp ?_
  intro x hx
  rw [Subgroup.mem_inf] at hx
  obtain ⟨hxX, hxVU⟩ := hx
  have h5 : Work.GW2.invSet (Work.GW2.pCoreIn 2 B.Hhat ⊔ B.U) y = {1} :=
    Work.CORE3.VUInvSetTrivial G I hBc B h1 D y hy2 hyH
  have hmem : x ∈ Work.GW2.invSet (Work.GW2.pCoreIn 2 B.Hhat ⊔ B.U) y := by
    refine ⟨hxVU, ?_⟩
    simpa [inv_eq_self_of_orderOf_two hy2] using hinv x hxX
  rw [h5] at hmem
  exact Subgroup.mem_bot.mpr (Set.mem_singleton_iff.mp hmem)

/-- **`|X| = 3`.**  `X` injects into `Ĥ/VU` (of order `6`), so `|X| ∣ 6`; `|X|` is odd and
`X ≠ ⊥`, so `|X| = 3`. -/
theorem card_X_eq_three (I : Work.CORE3.Case1Inputs) (hBc : Work.GW2.BenderCtx G)
    (B : Work.GW2.BenderSetup G) (h1 : Work.GW2.Case1 B) (D : Work.GW2.Case1bData B)
    {y : G} (hy2 : orderOf y = 2) (hyH : y ∉ B.Hhat) {X : Subgroup G} (hXH : X ≤ B.Hhat)
    (hX1 : X ≠ ⊥) (hXodd : Odd (Nat.card X)) (hinv : Work.GW2.Inverts y X) :
    Nat.card X = 3 := by
  classical
  have hdisj : X ⊓ (Work.GW2.pCoreIn 2 B.Hhat ⊔ B.U) = ⊥ :=
    X_inf_VU_eq_bot I hBc B h1 D hy2 hyH hXH hinv
  set W : Subgroup G := Work.GW2.pCoreIn 2 B.Hhat ⊔ B.U with hW
  have hWrel : W.relIndex B.Hhat = 6 := by
    rw [hW]; exact Work.CORE3.relIndex_VU_Hhat G I hBc B h1 D
  have hWn : (W.subgroupOf B.Hhat).Normal := by
    rw [hW]; exact Work.CORE3.normal_VU_subgroupOf G I hBc B h1 D
  let N : Subgroup ↥B.Hhat := W.subgroupOf B.Hhat
  haveI : N.Normal := hWn
  have hNcard : Nat.card (↥B.Hhat ⧸ N) = 6 := by
    rw [← Subgroup.index_eq_card N]
    exact hWrel
  set Xs : Subgroup ↥B.Hhat := X.subgroupOf B.Hhat with hXs
  have hXscard : Nat.card ↥Xs = Nat.card X :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hXH).toEquiv
  -- the composite `Xs → Ĥ/VU` is injective
  let f : ↥Xs →* (↥B.Hhat ⧸ N) := (QuotientGroup.mk' N).comp Xs.subtype
  have hfinj : Function.Injective f := by
    intro p q hpq
    have hmemN : ((p : ↥B.Hhat)⁻¹ * (q : ↥B.Hhat)) ∈ N := by
      have h1' : (QuotientGroup.mk' N) (Xs.subtype p) = (QuotientGroup.mk' N) (Xs.subtype q) := hpq
      exact QuotientGroup.eq.mp h1'
    have hmemG : ((((p : ↥B.Hhat))⁻¹ * (q : ↥B.Hhat) : ↥B.Hhat) : G) ∈ W :=
      Subgroup.mem_subgroupOf.mp hmemN
    have hpX : (((p : ↥B.Hhat)) : G) ∈ X := p.2
    have hqX : (((q : ↥B.Hhat)) : G) ∈ X := q.2
    have hxX : ((((p : ↥B.Hhat))⁻¹ * (q : ↥B.Hhat) : ↥B.Hhat) : G) ∈ X :=
      X.mul_mem (X.inv_mem hpX) hqX
    have hbot : ((((p : ↥B.Hhat))⁻¹ * (q : ↥B.Hhat) : ↥B.Hhat) : G) ∈ (⊥ : Subgroup G) := by
      rw [← hdisj]
      exact ⟨hxX, hmemG⟩
    have hone : ((((p : ↥B.Hhat))⁻¹ * (q : ↥B.Hhat) : ↥B.Hhat) : G) = 1 :=
      Subgroup.mem_bot.mp hbot
    have hpq' : (p : ↥B.Hhat) = (q : ↥B.Hhat) := by
      have h2' : ((p : ↥B.Hhat))⁻¹ * (q : ↥B.Hhat) = 1 := Subtype.ext hone
      exact inv_mul_eq_one.mp h2'
    exact Subtype.ext hpq'
  have hdvd : Nat.card X ∣ 6 := by
    have h1' : Nat.card ↥((⊤ : Subgroup ↥Xs).map f) = Nat.card ↥(⊤ : Subgroup ↥Xs) :=
      Subgroup.card_map_of_injective (K := (⊤ : Subgroup ↥Xs)) (f := f) hfinj
    have h1'' : Nat.card ↥(⊤ : Subgroup ↥Xs) = Nat.card ↥Xs := Subgroup.card_top
    have h2' : Nat.card ↥((⊤ : Subgroup ↥Xs).map f) ∣ Nat.card (↥B.Hhat ⧸ N) := by
      simpa using Subgroup.card_dvd_of_le (H := (⊤ : Subgroup ↥Xs).map f) (K := ⊤) le_top
    rw [hNcard] at h2'
    rwa [h1', h1'', hXscard] at h2'
  have hne1 : Nat.card X ≠ 1 := by
    intro h
    exact hX1 (Work.BSW.Cases.K4.eq_bot_of_card_eq_one h)
  have hcop : Nat.Coprime (Nat.card X) 2 := Nat.coprime_two_right.mpr hXodd
  have hdvd3 : Nat.card X ∣ 3 := by
    refine hcop.dvd_of_dvd_mul_left ?_
    norm_num at hdvd ⊢
    exact hdvd
  rcases (Nat.dvd_prime Nat.prime_three).mp hdvd3 with h | h
  · exact absurd h hne1
  · exact h

/-- **A generator of `X`.**  With `|X| = 3`, `X = ⟨x⟩` for some `x ∈ X` of order `3` lying
outside `VU`. -/
theorem exists_zpowers_eq (I : Work.CORE3.Case1Inputs) (hBc : Work.GW2.BenderCtx G)
    (B : Work.GW2.BenderSetup G) (h1 : Work.GW2.Case1 B) (D : Work.GW2.Case1bData B)
    {y : G} (hy2 : orderOf y = 2) (hyH : y ∉ B.Hhat) {X : Subgroup G} (hXH : X ≤ B.Hhat)
    (hX1 : X ≠ ⊥) (hXodd : Odd (Nat.card X)) (hinv : Work.GW2.Inverts y X) :
    ∃ x ∈ X, orderOf x = 3 ∧ X = Subgroup.zpowers x ∧
      x ∉ (Work.GW2.pCoreIn 2 B.Hhat ⊔ B.U) := by
  have hcard : Nat.card X = 3 := card_X_eq_three I hBc B h1 D hy2 hyH hXH hX1 hXodd hinv
  have hVU : X ⊓ (Work.GW2.pCoreIn 2 B.Hhat ⊔ B.U) = ⊥ :=
    X_inf_VU_eq_bot I hBc B h1 D hy2 hyH hXH hinv
  obtain ⟨x, hxX, hx1⟩ : ∃ x ∈ X, x ≠ 1 := by
    by_contra hcon
    apply hX1
    rw [Subgroup.eq_bot_iff_forall]
    intro z hz
    by_contra hz1
    exact hcon ⟨z, hz, hz1⟩
  have hx3 : orderOf x = 3 := by
    have hdvd : orderOf x ∣ 3 := by
      have h0 : orderOf x ∣ Nat.card X := Subgroup.orderOf_dvd_natCard X hxX
      rwa [hcard] at h0
    rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h | h
    · exact absurd (orderOf_eq_one_iff.mp h) hx1
    · exact h
  have hzp : X = Subgroup.zpowers x := by
    refine (Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hxX) ?_).symm
    rw [Nat.card_zpowers, hx3, hcard]
  refine ⟨x, hxX, hx3, hzp, ?_⟩
  intro hxVU
  have hmem : x ∈ X ⊓ (Work.GW2.pCoreIn 2 B.Hhat ⊔ B.U) := ⟨hxX, hxVU⟩
  rw [hVU] at hmem
  exact hx1 (Subgroup.mem_bot.mp hmem)

/-- **Divisibility half of Bender (7)**: the evenness of `|C_G(X)|` alone forces `3 ∣ |U|`.

(Proved in the sibling module `Work.CORE3.J4.J4U3ThreeDvd`; repeated here because that module
imports this one.) -/
theorem card_U_three_dvd (I : Work.CORE3.Case1Inputs) (hBc : Work.GW2.BenderCtx G)
    (B : Work.GW2.BenderSetup G) (h1 : Work.GW2.Case1 B) (D : Work.GW2.Case1bData B)
    {y : G} (hy2 : orderOf y = 2) (hyH : y ∉ B.Hhat) {X : Subgroup G} (hXH : X ≤ B.Hhat)
    (hX1 : X ≠ ⊥) (hXodd : Odd (Nat.card X)) (hinv : Work.GW2.Inverts y X)
    (hC : Even (Nat.card (Subgroup.centralizer (X : Set G)))) :
    3 ∣ Nat.card B.U := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  -- (1) an involution `s` centralizing `X` exists
  obtain ⟨s, hsC, hs2⟩ :=
    Work.CORE3.exists_involution_mem_of_even_card (Subgroup.centralizer (X : Set G)) hC
  -- (2) `s ∉ Ĥ`
  have hsH : s ∉ B.Hhat := by
    intro hsmem
    refine Work.CORE3.SevenNoInvolCentralizer G I hBc B h1 D hy2 hyH hXH hX1 hXodd hinv
      ⟨s, hsmem, hs2, ?_⟩
    intro x hx
    exact ((Subgroup.mem_centralizer_iff.mp hsC) x hx).symm
  -- (3) all involutions are conjugate: `s^k = t`
  obtain ⟨n, hn2, hdih⟩ := Work.CORE3.SylowDihedral G hBc B
  have hnoN : ∀ N : Subgroup G, N.Normal → N.index ≠ 2 :=
    Work.CORE2A.bender_no_index_two hBc B
  obtain ⟨k, hk⟩ := isConj_iff.mp ((I.T.fus G B.S n hn2 hdih hnoN).1 s B.t hs2 B.t_order)
  -- (4) `X^k ≤ B.H`
  have hconj_le : Work.GW2.conjSub k X ≤ B.H := by
    intro z hz
    rw [Work.CORE2A.conjSub_eq_map, Subgroup.mem_map] at hz
    obtain ⟨x, hx, rfl⟩ := hz
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hxs : s * x = x * s := ((Subgroup.mem_centralizer_iff.mp hsC) x hx).symm
    show MulAut.conj k x * B.t = B.t * MulAut.conj k x
    simp only [MulAut.conj_apply]
    rw [← hk]
    calc k * x * k⁻¹ * (k * s * k⁻¹) = k * (x * s) * k⁻¹ := by group
      _ = k * (s * x) * k⁻¹ := by rw [hxs]
      _ = (k * s * k⁻¹) * (k * x * k⁻¹) := by group
  -- (5) `X^k ≤ B.U` (an odd-order subgroup of `H = U ⊔ S` lies in `U`)
  have hBU : Work.GW2.conjSub k X ≤ B.U :=
    Work.CORE2A.odd_subgroup_le_oddCoreIn B.H B.U ((B.S : Subgroup G)) rfl
      (Work.CORE3.H_eq_U_sup_S G I.T hBc B) B.S.isPGroup' (Work.GW2.conjSub k X) hconj_le
      (by rw [Work.CORE2A.card_conjSub]; exact hXodd)
  -- (6) hence `|X| ∣ |B.U|`, and `|X| = 3`
  have hdvd : Nat.card X ∣ Nat.card B.U := by
    have h := Subgroup.card_dvd_of_le hBU
    rwa [Work.CORE2A.card_conjSub] at h
  have h3 : Nat.card X = 3 := card_X_eq_three I hBc B h1 D hy2 hyH hXH hX1 hXodd hinv
  rwa [h3] at hdvd

/-- The centralizer of a cyclic subgroup is the centralizer of a generator. -/
theorem centralizer_zpowers_eq {x : G} :
    Subgroup.centralizer ({x} : Set G) =
      Subgroup.centralizer ((Subgroup.zpowers x : Subgroup G) : Set G) := by
  refine le_antisymm ?_ ?_
  · intro g hg
    rw [Subgroup.mem_centralizer_iff] at hg ⊢
    intro y hy
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
    exact (Commute.zpow_right (show Commute g x from (hg x (Set.mem_singleton x)).symm) n).eq.symm
  · intro g hg
    rw [Subgroup.mem_centralizer_iff] at hg ⊢
    intro y hy
    rw [Set.mem_singleton_iff] at hy
    rw [hy]
    exact hg x (Subgroup.mem_zpowers x)

/-- **`C_Ĥ(X)` is odd** (proved in `Work.CORE3.J4.J4U3CentralizerOdd` for a generator `x`):
`C_Ĥ(X) = C_Ĥ(x) ⊓ Ĥ` with `|X| = 3` and `x ∉ VU`. -/
theorem centralizer_inf_Hhat_odd (I : Work.CORE3.Case1Inputs) (hBc : Work.GW2.BenderCtx G)
    (B : Work.GW2.BenderSetup G) (h1 : Work.GW2.Case1 B) (D : Work.GW2.Case1bData B)
    {y : G} (hy2 : orderOf y = 2) (hyH : y ∉ B.Hhat) {X : Subgroup G} (hXH : X ≤ B.Hhat)
    (hX1 : X ≠ ⊥) (hXodd : Odd (Nat.card X)) (hinv : Work.GW2.Inverts y X) :
    Odd (Nat.card ↥(Subgroup.centralizer (X : Set G) ⊓ B.Hhat)) := by
  obtain ⟨x, hxX, hx3, hzp, hxVU⟩ :=
    exists_zpowers_eq I hBc B h1 D hy2 hyH hXH hX1 hXodd hinv
  have hxH : x ∈ B.Hhat := hXH hxX
  have hK : Subgroup.centralizer ((X : Set G)) ⊓ B.Hhat =
      Subgroup.centralizer ({x} : Set G) ⊓ B.Hhat := by
    rw [hzp]
    exact congrArg (fun S => S ⊓ B.Hhat) (centralizer_zpowers_eq (x := x)).symm
  rw [hK]
  exact J4U3CentralizerOdd I hBc B h1 D hxH hx3 hxVU

/-- **Counting reduction of Bender (7)** (new here).  If both conjugates `U`, `U^g` of `U = O(Ĥ)`
lie in `Ĥ ⊓ Ĥ^g` (i.e. `U ≤ Ĥ^g` and `U^g ≤ Ĥ`), meet trivially, and `|Ĥ ⊓ Ĥ^g| ≤ 6·|U|`, then
`|U| = 3`.

The multiplication map `U × U^g → Ĥ ⊓ Ĥ^g` is injective (`U ⊓ U^g = ⊥`), so
`|U|² = |U|·|U^g| ≤ |Ĥ ⊓ Ĥ^g| ≤ 6|U|`, giving `|U| ≤ 6`; with `3 ∣ |U|` (`card_U_three_dvd`) and
`|U|` odd (`bSetup_U_odd`) this forces `|U| = 3`.  Thus the whole remaining content of Bender (7)
is the pair of statements `U ≤ Ĥ^g` (equivalently `X ≤ C_G(U)`, Bender's `F(U) ⊆ C_Ĥ(X)`) and
`U^g ≤ Ĥ`, which is exactly what `J4U3_of_conj_K` still owes. -/
theorem card_U_eq_three_of_le_conjSub (I : Work.CORE3.Case1Inputs) (hBc : Work.GW2.BenderCtx G)
    (B : Work.GW2.BenderSetup G) (h1 : Work.GW2.Case1 B) (D : Work.GW2.Case1bData B)
    {y : G} (hy2 : orderOf y = 2) (hyH : y ∉ B.Hhat) {X : Subgroup G} (hXH : X ≤ B.Hhat)
    (hX1 : X ≠ ⊥) (hXodd : Odd (Nat.card X)) (hinv : Work.GW2.Inverts y X)
    (hC : Even (Nat.card (Subgroup.centralizer (X : Set G))))
    (g : G) (hK : X ≤ Work.GW2.conjSub g D.K)
    (hU : B.U ≤ Work.GW2.conjSub g B.Hhat) (hUg : Work.GW2.conjSub g B.U ≤ B.Hhat)
    (hcard : Nat.card ↥(B.Hhat ⊓ Work.GW2.conjSub g B.Hhat) ≤ 6 * Nat.card ↥B.U)
    (hdisj : B.U ⊓ Work.GW2.conjSub g B.U = ⊥) :
    Nat.card B.U = 3 := by
  classical
  have h3 : 3 ∣ Nat.card B.U := card_U_three_dvd I hBc B h1 D hy2 hyH hXH hX1 hXodd hinv hC
  have hodd : Odd (Nat.card B.U) := Work.CORE2A.bSetup_U_odd B
  have hcardg : Nat.card ↥(Work.GW2.conjSub g B.U) = Nat.card ↥B.U :=
    Work.CORE2A.card_conjSub g B.U
  have hUgH : Work.GW2.conjSub g B.U ≤ Work.GW2.conjSub g B.Hhat := by
    intro x hx
    rw [Work.CORE2A.mem_conjSub_iff] at hx ⊢
    exact Work.CORE2A.bSetup_U_le_Hhat B hx
  have hmul : ∀ p : ↥B.U × ↥(Work.GW2.conjSub g B.U),
      (p.1 : G) * (p.2 : G) ∈ B.Hhat ⊓ Work.GW2.conjSub g B.Hhat := fun p =>
    Subgroup.mem_inf.mpr
      ⟨B.Hhat.mul_mem (Work.CORE2A.bSetup_U_le_Hhat B p.1.2) (hUg p.2.2),
        (Work.GW2.conjSub g B.Hhat).mul_mem (hU p.1.2) (hUgH p.2.2)⟩
  have hinj : Function.Injective (fun p : ↥B.U × ↥(Work.GW2.conjSub g B.U) =>
      (⟨(p.1 : G) * (p.2 : G), hmul p⟩ : ↥(B.Hhat ⊓ Work.GW2.conjSub g B.Hhat))) := by
    rintro ⟨u1, v1⟩ ⟨u2, v2⟩ heq
    have heq' : (u1 : G) * (v1 : G) = (u2 : G) * (v2 : G) := Subtype.ext_iff.mp heq
    have hmem : (u2 : G)⁻¹ * (u1 : G) ∈ B.U ⊓ Work.GW2.conjSub g B.U := by
      refine Subgroup.mem_inf.mpr ⟨B.U.mul_mem (B.U.inv_mem u2.2) u1.2, ?_⟩
      have hsplit : (u2 : G)⁻¹ * (u1 : G) = (v2 : G) * (v1 : G)⁻¹ := by
        calc (u2 : G)⁻¹ * (u1 : G)
            = (u2 : G)⁻¹ * ((u1 : G) * (v1 : G)) * (v1 : G)⁻¹ := by group
          _ = (u2 : G)⁻¹ * ((u2 : G) * (v2 : G)) * (v1 : G)⁻¹ := by rw [heq']
          _ = (v2 : G) * (v1 : G)⁻¹ := by group
      rw [hsplit]
      exact (Work.GW2.conjSub g B.U).mul_mem v2.2 ((Work.GW2.conjSub g B.U).inv_mem v1.2)
    have hone : (u2 : G)⁻¹ * (u1 : G) = 1 := by
      have hbot : (u2 : G)⁻¹ * (u1 : G) ∈ (⊥ : Subgroup G) := by rw [← hdisj]; exact hmem
      exact Subgroup.mem_bot.mp hbot
    have hu : u1 = u2 := Subtype.ext (inv_mul_eq_one.mp hone).symm
    have hv : v1 = v2 := by
      refine Subtype.ext ?_
      rw [hu] at heq'
      exact mul_left_cancel heq'
    exact Prod.ext hu hv
  have hle : Nat.card ↥B.U * Nat.card ↥B.U ≤ 6 * Nat.card ↥B.U := by
    calc Nat.card ↥B.U * Nat.card ↥B.U
        = Nat.card ↥B.U * Nat.card ↥(Work.GW2.conjSub g B.U) := by rw [hcardg]
      _ = Nat.card (↥B.U × ↥(Work.GW2.conjSub g B.U)) := (Nat.card_prod _ _).symm
      _ ≤ Nat.card ↥(B.Hhat ⊓ Work.GW2.conjSub g B.Hhat) := Nat.card_le_card_of_injective _ hinj
      _ ≤ 6 * Nat.card ↥B.U := hcard
  obtain ⟨m, hm⟩ := h3
  obtain ⟨k, hk⟩ := hodd
  have hpos : 0 < Nat.card ↥B.U := Nat.card_pos
  have hle' : Nat.card ↥B.U ≤ 6 := by
    have h6 : Nat.card ↥B.U * Nat.card ↥B.U ≤ Nat.card ↥B.U * 6 := by
      have h := hle
      rw [mul_comm 6 (Nat.card ↥B.U)] at h
      exact h
    exact Nat.le_of_mul_le_mul_left h6 hpos
  omega

/-- **New here.**  In the (7)-configuration the conjugate four-group `V^g = O₂(Ĥ^g)` meets `Ĥ`
trivially.

Indeed `X ≤ K^g ≤ U^g`, and `V ⊆ C_Ĥ(U)` (`CentralizerPcoreEqVU`), so every `z ∈ V^g`
centralizes `U^g ⊇ X` elementwise: conjugating back by `g`, `[g⁻¹zg, g⁻¹xg] = 1` because the two
arguments lie in `V` and `U`.  Were `1 ≠ z ∈ V^g ⊓ Ĥ` of order dividing `2` (`D.four`), it would
be an involution of `Ĥ` centralizing `X`, contradicting `SevenNoInvolCentralizer`. -/
theorem conjSub_pCoreIn_inf_Hhat_eq_bot (I : Work.CORE3.Case1Inputs) (hBc : Work.GW2.BenderCtx G)
    (B : Work.GW2.BenderSetup G) (h1 : Work.GW2.Case1 B) (D : Work.GW2.Case1bData B)
    {y : G} (hy2 : orderOf y = 2) (hyH : y ∉ B.Hhat) {X : Subgroup G} (hXH : X ≤ B.Hhat)
    (hX1 : X ≠ ⊥) (hXodd : Odd (Nat.card X)) (hinv : Work.GW2.Inverts y X)
    (g : G) (hK : X ≤ Work.GW2.conjSub g D.K) :
    Work.GW2.conjSub g (Work.GW2.pCoreIn 2 B.Hhat) ⊓ B.Hhat = ⊥ := by
  classical
  have hKU : D.K ≤ B.U :=
    (Work.CORE2A.isHallIn_le D.hall).trans (Subgroup.map_subtype_le _)
  have hXU : X ≤ Work.GW2.conjSub g B.U := by
    refine hK.trans (fun z hz => ?_)
    rw [Work.CORE2A.mem_conjSub_iff] at hz ⊢
    exact hKU hz
  -- `V` commutes elementwise with `U`
  have hCU : ∀ v ∈ Work.GW2.pCoreIn 2 B.Hhat, ∀ u ∈ B.U, v * u = u * v := by
    intro v hv u hu
    have hcent : u ∈ Subgroup.centralizer ((Work.GW2.pCoreIn 2 B.Hhat : Subgroup G) : Set G) := by
      have heq := Work.CORE3.CentralizerPcoreEqVU G I hBc B h1 D
      have hmem : u ∈ Subgroup.centralizer ((Work.GW2.pCoreIn 2 B.Hhat : Subgroup G) : Set G)
          ⊓ B.Hhat := by
        rw [heq]
        exact Subgroup.mem_sup_right hu
      exact hmem.1
    exact Subgroup.mem_centralizer_iff.mp hcent v hv
  refine le_bot_iff.mp (fun z hz => ?_)
  rw [Subgroup.mem_inf] at hz
  obtain ⟨hzV, hzH⟩ := hz
  by_contra hz1
  have hzsq : z * z = 1 := by
    have h := (Work.CORE2A.mem_conjSub_iff (g := g) (K := Work.GW2.pCoreIn 2 B.Hhat)
      (x := z)).mp hzV
    have h2 : (g⁻¹ * z * g) * (g⁻¹ * z * g) = 1 := by
      simpa [pow_two] using D.four.2 _ h
    calc z * z = g * ((g⁻¹ * z * g) * (g⁻¹ * z * g)) * g⁻¹ := by group
      _ = 1 := by rw [h2]; group
  have hz2 : orderOf z = 2 := (Work.CORE3.orderOf_eq_two_iff_mul_self z).mpr ⟨hzsq, hz1⟩
  have hzC : ∀ x ∈ X, z * x = x * z := by
    intro x hx
    have hxu : g⁻¹ * x * g ∈ B.U := (Work.CORE2A.mem_conjSub_iff).mp (hXU hx)
    have hzv : g⁻¹ * z * g ∈ Work.GW2.pCoreIn 2 B.Hhat :=
      (Work.CORE2A.mem_conjSub_iff).mp hzV
    have hcomm : (g⁻¹ * z * g) * (g⁻¹ * x * g) = (g⁻¹ * x * g) * (g⁻¹ * z * g) :=
      hCU _ hzv _ hxu
    calc z * x = g * ((g⁻¹ * z * g) * (g⁻¹ * x * g)) * g⁻¹ := by group
      _ = g * ((g⁻¹ * x * g) * (g⁻¹ * z * g)) * g⁻¹ := by rw [hcomm]
      _ = x * z := by group
  exact Work.CORE3.SevenNoInvolCentralizer G I hBc B h1 D hy2 hyH hXH hX1 hXodd hinv
    ⟨z, hzH, hz2, hzC⟩

/-- **The remaining gap of Bender (7).**  Under the hypotheses of `J4U3` together with the
derived reduction `X ≤ K^g`, `N_G(X) ≤ Ĥ^g` (see `Work.CORE3.SevenConjK`), the conclusion
`|U| = 3` still has to be proved: this is the mathematical content of Bender's sketch
("`F(U) ⊆ C_G(X) ≤ N_G(X) ≤ Ĥ^g` … hence `|F(U)| = 3` and therefore `|U| = 3`").

By `card_U_eq_three_of_le_conjSub` (above) it is enough to prove the two inclusions `U ≤ Ĥ^g` and
`U^g ≤ Ĥ` (plus `U ⊓ U^g = ⊥` and `|Ĥ ⊓ Ĥ^g| ≤ 6|U|`); `U ≤ Ĥ^g` is equivalent to `X ≤ C_G(U)`
(Bender's `F(U) ⊆ C_Ĥ(X)`), and `|Ĥ ⊓ Ĥ^g| ≤ 6|U|` follows from `V^g ⊓ Ĥ = ⊥`
(see `NOTES_J4U3.md`, §2).  See that file for the GAP evidence showing that the local (1b)
structure alone admits `U` non-abelian (whence `X ≰ C_G(U)`), so any proof needs the global
input. -/
theorem J4U3_of_conj_K (I : Work.CORE3.Case1Inputs) (hBc : Work.GW2.BenderCtx G)
    (B : Work.GW2.BenderSetup G) (h1 : Work.GW2.Case1 B) (D : Work.GW2.Case1bData B)
    {y : G} (hy2 : orderOf y = 2) (hyH : y ∉ B.Hhat) {X : Subgroup G} (hXH : X ≤ B.Hhat)
    (hX1 : X ≠ ⊥) (hXodd : Odd (Nat.card X)) (hinv : Work.GW2.Inverts y X)
    (hC : Even (Nat.card (Subgroup.centralizer (X : Set G))))
    (hN : Even (Nat.card (Subgroup.normalizer (X : Set G))))
    (g : G) (hK : X ≤ Work.GW2.conjSub g D.K)
    (hNg : Subgroup.normalizer (X : Set G) ≤ Work.GW2.conjSub g B.Hhat) :
    Nat.card B.U = 3 := by sorry

theorem J4U3 {G : Type} [Group G] [Finite G] (I : Work.CORE3.Case1Inputs)
    (hBc : Work.GW2.BenderCtx G) (B : Work.GW2.BenderSetup G) (h1 : Work.GW2.Case1 B)
    (D : Work.GW2.Case1bData B) {y : G} (hy2 : orderOf y = 2) (hyH : y ∉ B.Hhat)
    {X : Subgroup G} (hXH : X ≤ B.Hhat) (hX1 : X ≠ ⊥) (hXodd : Odd (Nat.card X))
    (hinv : Work.GW2.Inverts y X)
    (hC : Even (Nat.card (Subgroup.centralizer (X : Set G))))
    (hN : Even (Nat.card (Subgroup.normalizer (X : Set G)))) :
    Nat.card B.U = 3 := by
  -- the reduction `∃ g, X ≤ K^g ∧ N_G(X) ≤ Ĥ^g` (`Work.CORE3.J4.J4U3ConjK`, proved)
  obtain ⟨g, hK, hNg⟩ := J4U3ConjK I hBc B h1 D hy2 hyH hXH hX1 hXodd hinv hC
  exact J4U3_of_conj_K I hBc B h1 D hy2 hyH hXH hX1 hXodd hinv hC hN g hK hNg

end Work.CORE3.J4
