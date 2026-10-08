import Mathlib
import Submission.Work.CORE3.Defs
import Submission.Work.CORE3.Case1bEightNineDefs
import Submission.Work.CORE3.Case1bDStructure
import Submission.Work.CORE3.Case1bCount
import Submission.Work.CORE3.CentralizerPcoreEqVU
import Submission.Work.CORE3.NormalizerPcoreEqHhat
import Submission.Work.CORE3.RelIndexHHhat
import Submission.Work.CORE3.SevenOddCentralizer
import Submission.Work.CORE3.SevenNoInvolCentralizer
import Submission.Work.CORE3.SevenConjU
import Submission.Work.CORE3.VUInvSetTrivial
import Submission.Work.CORE3.InvSetVUSingleton
import Submission.Work.CORE3.CosetInvCountLeSix
import Submission.Work.CORE3.CosetInvCountNeFive
import Submission.Work.CORE3.CosetInvCountNeSixOf
import Submission.Work.CORE3.SixInvSetElements
import Submission.Work.CORE3.SixInvSetMulTable
import Submission.Work.CORE3.OrderSixNoFiveSubset
import Submission.Work.CORE3.FourGroupOddOrderFixed
import Submission.Work.CORE3.FourGroupOddOrderCommutingInvolution
import Submission.Work.CORE3.OddOrderMemOfMemSup
import Submission.Work.CORE3.J4.J4U3
import Submission.Work.CORE3.J4.J4CosetStep
import Submission.Work.CORE3.J4.J4DTriv
import Submission.Work.CORE3.J4.CardDvdSixOfDisjoint
import Submission.Work.CORE3.SevenConjK
import Submission.Work.CORE3.J4.J4U3ThreeDvd
import Submission.Work.CORE3.J4.J4U3CentralizerOdd

/-!
# Context for the `Case1bSeven` cluster (Bender 1981 §3, p. 224, item (7))

This module contains **no mathematics** — it is a reading guide for the lemmas

* `Work.CORE3.Case1bSevenU3`  (`|U| = 3`),
* `Work.CORE3.Case1bSevenTriv` (`VU ⊓ (Ĥ ⊓ Ĥ^y) = ⊥` from `4 ≤ |I_Ĥ(y)|` and `|U| = 3`),
* `Work.CORE3.Case1bSevenInvInI` (`4 ≤ |I_Ĥ(y)|` from `|U| = 3`),

which together give `Work.CORE3.Case1bSeven`.  Everything imported above is
`#print axioms`-clean (`propext`, `Classical.choice`, `Quot.sound`), except the three stubs
`J4.J4U3`, `BenderSeven*`; in particular `Work.CORE3.Case1bEightNine`,
`Work.CORE3.CosetInvCountNeSix`, `Work.CORE3.BenderSeven` are **sorry-dependent** and must not
be used.

## The setting

`B : BenderSetup G` gives `S : Sylow 2 G` (dihedral of order `8` in our case), the cyclic
`S₀ ≤ S` of index `2`, `t : G` the involution of `S₀`, and the maximal subgroup
`Ĥ = B.Hhat` (an `IsCoatom`).  Furthermore `H = B.H := C_G(t)`, `U = B.U := O(H) = O(Ĥ)`
(Theorem 2.6, `I.h26`), `B.t ∈ S₀` is central in `S`.

`D : Case1bData B` gives `V := pCoreIn 2 B.Hhat = O₂(Ĥ)` a Klein four group (`D.four`),
`|S| = 8` (`D.S8`), and a subgroup `K = D.K` which is a **Hall subgroup of `F(U)`**
(`D.hall`, with `fittingIn B.U`), `K ≠ ⊥` (`D.ne`), and which is *the inverted set of every
involution of `Ĥ` outside `V`*: for `s ∈ Ĥ`, `orderOf s = 2`, `s ∉ V` one has
`(D.K : Set G) = invSet B.U s` (`D.inv`).  Hence `|K| = |I_U(s)| = |U : C_U(s)|` for each such
`s`, `K ◁ U` (it is the `(-1)`-eigenspace of `s` on the `s`-invariant group `U`), `K` is abelian,
and `|U| = |K| · |C_U(s)|` with the two factors coprime.

Structural consequences (all axiom-clean, in the workspace):

* `Work.CORE3.CentralizerPcoreEqVU` : `C_Ĥ(V) = V ⊔ U`.
* `Work.CORE3.NormalizerPcoreEqHhat` : `N_G(V) = Ĥ` (so `Ĥ = N_G(V)`; likewise one shows
  `N_G(U) = Ĥ` and `N_G(F(U)) = Ĥ` from the maximality of `Ĥ` and the simplicity of `G`).
* `Work.CORE3.normal_VU_subgroupOf`, `Work.CORE3.relIndex_VU_Hhat` :
  `VU := V ⊔ U` is normal in `Ĥ` with `|Ĥ : VU| = 6`; hence `|VU| = 4|U|`,
  `|Ĥ| = 24|U|`, `|H| = 8|U|`, and `Ĥ/U ≅ S₄` (order `24`, normal Klein four `VU/U`, quotient
  `Ĥ/VU ≅ S₃` non-abelian, Sylow 2 equal to `S`).
* `Work.CORE3.VUInvSetTrivial` (= `Case1bFiveProp`, Bender's (5)) : for every involution
  `y ∉ Ĥ`, `invSet (V ⊔ U) y = {1}`.  Consequently for `I := invSetIn B.Hhat y
  = {x ∈ Ĥ | y * x * y = x⁻¹}` one has `I ⊓ VU = ⊥`, so `I` injects into `Ĥ/VU ≅ S₃`:
  **`|I_Ĥ(y)| = cosetInvCount B.Hhat y ≤ 6`**
  (`Work.CORE3.cosetInvCount_le_six`).
* `Work.CORE3.CosetInvCountNeFive` : `cosetInvCount B.Hhat y ≠ 5`.
* `Work.CORE3.SixInvSetElements`, `Work.CORE3.SixInvSetMulTable` : the structure of `I` when
  `|I| = 6` (`I` contains an element of order `3` and two distinct involutions; the six elements
  multiply like `S₃`).
* `Work.CORE3.cosetInvCount_ne_six_of` : `≠ 6` follows from Bender's (6) (`hSix`,
  `Work.CORE3.BenderSixNeSixAux`, axiom-clean) together with a hypothesis `hSeven` saying
  *for every configuration `(y', X')` as in `Case1bSeven`, `|U| = 3` and
  `|Ĥ ⊓ Ĥ^{y'}| = 6`*.  The latter is assembled below from `Case1bSevenU3`,
  `Case1bSevenInvInI` and `Case1bSevenTriv` together with `Case1bDStructure`.
* `Work.CORE3.Case1bDStructure` : if `4 ≤ cosetInvCount B.Hhat y` (for an involution
  `y ∉ Ĥ`), then `(Ĥ ⊓ Ĥ^y) · (V ⊔ U) = Ĥ` and `|(Ĥ ⊓ Ĥ^y) : (Ĥ ⊓ Ĥ^y) ⊓ (V ⊔ U)| = 6`.
* `Work.CORE3.J4.J4DTriv` (axiom-clean) : under `cosetInvCount Ĥ y = 4` (and the configuration,
  and `|U| = 3`) one has `(V ⊔ U) ⊓ (Ĥ ⊓ Ĥ^y) = ⊥`.  `Case1bSevenTriv` is the same statement
  with `4 ≤ cosetInvCount Ĥ y` in place of `= 4`.
* `Work.CORE3.card_inf_conjSubOfThree` (axiom-clean, in `BenderSevenD6.lean`) : given
  `4 ≤ cosetInvCount Ĥ y`, `|U| = 3` and `(V ⊔ U) ⊓ (Ĥ ⊓ Ĥ^y) = ⊥`, one gets
  `|Ĥ ⊓ Ĥ^y| = 6`.  (Proof: `Case1bDStructure` gives `D · VU = Ĥ` and `|D : D⊓VU| = 6`, and
  `D ⊓ VU = ⊥` gives `|D| = |Ĥ|/|VU| = 6`.)
* `Work.CORE3.J4.card_X_eq_three`, `Work.CORE3.J4.X_inf_VU_eq_bot` (axiom-clean) :
  under the configuration, `X ⊓ (V ⊔ U) = ⊥` and `|X| = 3`.
* `Work.CORE3.SevenNoInvolCentralizer` : under the configuration, no involution of `Ĥ`
  centralizes `X`; equivalently the even-order witness of `|C_G(X)|` is an involution
  `s ∈ C_G(X)` with `s ∉ Ĥ` (`Work.CORE3.exists_involution_mem_of_even_card`).
* `Work.CORE3.SevenOddCentralizer` : an odd-order element of `Ĥ` commuting with an involution of
  `Ĥ` lies in `U = O(Ĥ)`.
* `Work.CORE3.SevenConjU` : under the configuration with `|U| = 3`, `X` is a conjugate of `U`;
  its proof in fact produces `conjSub k X ≤ B.U` where `k` is any element with `s^k = B.t`,
  `s ∈ C_G(X)` an involution outside `Ĥ` (all involutions of `G` are conjugate, `I.T.fus`).
* `Work.CORE2A.odd_subgroup_le_oddCoreIn` : an odd-order subgroup of `H = U ⊔ S` lies in `U`
  (because `|H : U| = 8`).

## Bender's own proof of (7) (p. 224), verbatim

> Suppose `y ∈ J_n` inverts some `2'`-subgroup `X ≠ 1` of `Ĥ` such that `C_G(X)` and `N_G(X)`
> have even order.  Then `|U| = k = 3`, `n = 4`, and `Ĥ ∩ Ĥ^y ≅ D₆`.
>
> For `X` must be conjugate to a subgroup of `K`, say `X ⊆ Ĥ^g`, and satisfies
> `F(U) ⊆ C_Ĥ(X) ≤ N_Ĥ(X) ≤ Ĥ^g`; and since `V^g ≰ Ĥ`, it follows that `C_{Ĥ^g}(V^g) = 1`,
> hence `|F(U)| = 3` and therefore `|U| = 3`.  Lying in
> `Ĥ^g = (Ĥ ∩ Ĥ^g)V^g`, `y` centralizes some involution in `Ĥ ∩ Ĥ^g`, but does not normalize the
> subgroup of order `9` in `Ĥ ∩ Ĥ^g = N_Ĥ(X)`.

### Comments on that paragraph

* "`X` must be conjugate to a subgroup of `K`" is exactly: choose an involution
  `s ∈ C_G(X)` with `s ∉ Ĥ`, write `s = t^k`, and conjugate by `k`; then `X^k ≤ U = F(U)`, so
  `Case1 B` gives `N_G(X^k) ≤ Ĥ` whence `y^k ∈ Ĥ`; as `y^k` inverts the nontrivial
  `X^k ≤ U ⊓ Ĥ` and `V` centralizes `U`, `y^k ∉ V`, and `Case1bData.inv` gives
  `X^k ≤ D.K ⊆ F(U)`.  (In particular `3 ∣ |K|`.)
* The displayed "`C_{Ĥ^g}(V^g) = 1`" is false as printed: `C_{Ĥ^g}(V^g) = (VU)^g ≠ 1`
  (only `C_{Ĥ^g}(V^g) ≰ Ĥ` is true).  The sentence must be read as the argument for
  `|F(U)| = 3`: with `K = I_U(s)` a Hall subgroup of `F(U) = U` and `X^k ≤ K`, the shape of
  `Ĥ` forces `U = K ≅ C₃`.
* `F(U) = U` because `U = O(Ĥ)` is the product of its Sylow subgroups for odd primes, hence
  nilpotent; so `|F(U)| = 3` really is `|U| = 3`.
* `U ⊓ U^g = 1` whenever `V^g ≠ V` (i.e. `g ∉ Ĥ`) is a tempting intermediate statement —
  it holds in the `A₇` model, where `X = U^g` for a `g ∉ Ĥ`.  It would give
  `|U| = |U : U ⊓ U^g| ≥ |X| = 3` but not the reverse inequality.

## State of the reduction (read `Submission/Work/CORE3/J4/J4U3.lean`)

`J4/J4U3.lean`'s module docstring is the sharpest internal account.  Everything there is
axiom-clean (`#print axioms` = `propext, Classical.choice, Quot.sound`) and available:

* `Work.CORE3.J4.card_X_eq_three`, `X_inf_VU_eq_bot`, `exists_zpowers_eq` — `|X| = 3`,
  `X ⊓ VU = ⊥`, `X = ⟨x⟩` with `orderOf x = 3`, `x ∉ VU`;
* `Work.CORE3.J4.card_U_three_dvd` — `3 ∣ |U|`;
* `Work.CORE3.J4.centralizer_inf_Hhat_odd` — `|C_Ĥ(X)|` is odd;
* `Work.CORE3.SevenConjK` (sorry-free) —
  `∃ g, X ≤ conjSub g D.K ∧ normalizer (X : Set G) ≤ conjSub g B.Hhat`;
  this is Bender's "`X` must be conjugate to a subgroup of `K`".  Its docstring also records
  that `K = I_U(s)` is a Hall subgroup of `F(U) = U`, that `K ≤ Z(F(U))` (because `K`
  centralizes `F(U)`: this is the step of Bender's Theorem 2.10 proof that reads
  "`I_U(s)` centralizes `F(U)`, hence lies in `F(U)`"), and hence that
  `X ≤ K^g ≤ Z(F(U)^g)`, i.e. `F(U)^g = U^g ≤ C_G(X) = C_{Ĥ^g}(X)`.
* The remaining gap of `|U| = 3` is isolated as `Work.CORE3.J4.J4U3_of_conj_K`
  (`J4/J4U3.lean`) and is the task of `Work.CORE3.Case1bSevenU3OfConjK`: with `g` as above,
  `X ≤ K^g ≤ Z(U^g)`, `X ≤ Ĥ`, `N_G(X) ≤ Ĥ^g`, `y ∈ N_G(X)`, one must show `|U| = 3`,
  i.e. `K^g = U^g` and `C_{U^g}(y) = 1`.

Useful derived remarks (all elementary, all consistent, none of them yet sufficient):

* `X ⊓ U = ⊥`: `X ≤ U = F(U)` would give `y ∈ N_G(X) ≤ Ĥ` by local control.
* `X^g ≤ U` (from `K^g ≤ U^g` and `X ≤ K^g` conjugated) and `N_G(X^g) ≤ Ĥ`, so `y^g ∈ Ĥ`;
  `y^g ∉ V` (it inverts `X^g ≠ 1 ≤ U ⊓ C(V)`), whence `X^g ≤ K` (as `I_U(s) = K` for every
  involution `s ∈ Ĥ ∖ V`) and `3 ∣ |K|`.
* With `M := U^g ⊓ Ĥ`, one has `X ≤ M ≤ C_Ĥ(X)`, `M^g ≤ U`, `N_G(M) ≤ Ĥ ⊓ Ĥ^g`; and `y`
  does **not** normalize `M` (else `y ∈ N_G(M) ≤ Ĥ`).

## The third open piece: `Work.CORE3.Case1bSevenLeFour` (`n ≤ 4`)

Statement: for every involution `y ∉ Ĥ`, `cosetInvCount B.Hhat y ≤ 4` (the same conclusion as
`Work.CORE3.J4.J4SevenLeFour`; the delegated variant `Case1bSevenLeFour` carries the extra
hypothesis `|U| = 3`, hence is weaker).  Reduction (clean inputs):

* `n ≤ 6`: `Work.CORE3.cosetInvCount_le_six` (input: Bender (5), `Work.CORE3.VUInvSetTrivial`).
* `n ≠ 5`: `Work.CORE3.CosetInvCountNeFive`.
* Hence `5 ≤ n` forces `n = 6`, and only `n = 6` has to be excluded.

What `n = 6` looks like (`Work.CORE3.SixInvSetElements`, `Work.CORE3.SixInvSetMulTable`, both
clean): `I := invSetIn B.Hhat y` has six elements, contains `a` of order `3` and two distinct
involutions `b₁ ≠ b₂`, and `I = {1, a, a², b₁, b₂, c}` with `c = b₁ b₂ b₁ = b₂ b₁ b₂`,
`b₁ * a * b₁ = a⁻¹` and `(b₁ * b₂)^3 = 1`.  Every `x ∈ I` gives an involution `y * x` of the coset
`Ĥy`, and `x ↦ y * x` is a bijection from `I` onto the set of involutions of `Ĥy`.

What one wants instead: an involution `z ∈ Ĥy` of the coset together with `u ∈ B.U`, `u ≠ 1`,
such that `z * u * z⁻¹ = u⁻¹` — that is, Bender's (6) in the form producing an element of `U`,
not merely of `Ĥ`.  Local control (`h1.2`, applicable to `⟨u⟩` because `U = F(U)`, see
`C3six/CardUThreeLocal.lean`) then puts `z` in `Ĥ`, contradicting `Ĥy ∩ Ĥ = ∅` for `y ∉ Ĥ`.
This is independent of Bender (7) — in particular do **not** route through
`Work.CORE3.cosetInvCount_ne_six_of` with a `|D| = 6` hypothesis, nor through `BenderSeven`,
`J4.J4U3`, `J4.J4SevenCore` or `Case1bSeven`: all of those consume the statement being proved.

Two further remarks that may help.

* `n = 6` has a structural face: `I ⊆ D` with `D = Ĥ ⊓ Ĥ^y`, `|I| = 6`, `I ∩ VU = {1}`,
  `D · VU = Ĥ` and `|D : D ⊓ VU| = 6` (`Work.CORE3.Case1bDStructure`, which only needs
  `4 ≤ n`), so `I` is a transversal for `D ⊓ VU` in `D` and `D = I · (D ⊓ VU)`.
* For `x ∈ I`, the involution `z_x = y * x` of the coset satisfies
  `z_x * h * z_x⁻¹ = y * (x * h * x⁻¹) * y⁻¹` for `h ∈ Ĥ`; thus e.g. `z_{b₁}` centralises
  `⟨a⟩ =: X'` (because `b₁ a b₁ = a⁻¹` and `y a y = a⁻¹`), so `X'` has an even `G`-centralizer
  realised by an involution outside `Ĥ`.

## IMPORT CYCLE — read this before choosing imports

`Submission/Work/CORE3/BenderSevenD6.lean` imports `Submission.Work.CORE3.Case1bSeven` (the file
this cluster is meant to feed).  Consequently, any module that is imported *by* `Case1bSeven` must
not import any of

  `Case1bEightNine`, `BenderSeven`, `BenderSevenD6`, `BenderSevenU3`, `CosetInvCountNeSix`,
  `CosetInvCountNeThree`, `CosetInvCountLeFour`, `SevenInvInI`, `J4.J4SevenNeThree`,
  `J4.J4SevenNeFour`(if it appears), `J4.J4SevenCore`, `J4.J4SevenLeFour`, `Case1bIndex`,
  `Jthree/CardUThree`, `SevenCardU`, `SevenStep`, `J4.J4Step7`, `J4.J4Step7GStruct`

(those are exactly the modules whose closure reaches `BenderSevenD6`).  Including one of them in
a lemma that `Case1bSeven` consumes *breaks the build with a cycle*.

So the two lemmas
`Work.CORE3.Case1bSevenInvInI` (`4 ≤ cosetInvCount Ĥ y` from `|U| = 3`) and
`Work.CORE3.Case1bSevenLeFour` (`≤ 4`) must be proved from the cycle-free modules listed above
in this file, plus

* `Work.CORE3.J4.ExistsConjEqInvOrderThree` (clean), `Work.CORE3.OrderThreeLeCentralizer` (clean),
* `Work.BSW.Cases.K4.CardSup` (`card_sup_of_le_normalizer_of_inf_eq_bot`),
* `Work.CORE2A.*` (`normalizer_conjSub`, `card_conjSub`, `conjSub_eq_map`, `mem_conjSub_iff`,
  `thm26Concl_*`).

## Route for `Work.CORE3.Case1bSevenInvInI` (`4 ≤ cosetInvCount Ĥ y` from `|U| = 3`)

Use the *factorisation* route (do **not** use `J4.J4SevenNeThree`, which is cycle-blocked).
`X = ⟨x⟩` with `orderOf x = 3`, `x ∉ VU` (`J4.exists_zpowers_eq`).  `Work.CORE3.SevenConjU`
(clean; hypotheses: `|U| = 3` and `Even |C_G(X)|`) gives `X = conjSub g B.U` for some `g`; with
`N_G(U) = Ĥ` (from `B.Hhat_coatom` plus simplicity: `N_G(U) ≥ Ĥ` and `≠ ⊤` because `U ≠ ⊥` and
`U ≤ Ĥ ≠ ⊤`) this gives `N_G(X) = conjSub g B.Hhat =: Ĥ^g`, and `y ∈ Ĥ^g` because `y` inverts `X`.

Let `D := Ĥ ⊓ Ĥ^g`, `P := X ⊔ U`, `V^g := conjSub g (pCoreIn 2 B.Hhat)`.  Then:

* `|P| = 9`: `X ⊓ U = ⊥` (Bender (5)) and `U ≤ C_G(x)` (`OrderThreeLeCentralizer`: `U ≤ Ĥ`
  normalises `X` and `orderOf x = 3`, `|U| = 3`);
* `P ≤ D`: `U ≤ N_G(X) = Ĥ^g`, `X = U^g ≤ Ĥ^g`;
* `V^g ⊓ Ĥ = ⊥`: a nontrivial element of `V^g` has order `2` and centralises `X = U^g`, which
  `Work.CORE3.SevenNoInvolCentralizer` forbids;
* `9 ∣ |D|` and `4 · |D| = |V^g ⊔ D| ≤ |Ĥ^g| = 72`, so `|D| ∈ {9, 18}`;
* `|D| ≠ 9`: if `|D| = 9` then `D = P`; but `N_Ĥ(X) = Ĥ ⊓ N_G(X) = D` contains an element `h`
  of `Ĥ` inverting `x` (`Work.CORE3.J4.ExistsConjEqInvOrderThree`), and any such `h` lies in
  `D = P ≤ C_G(x)` — contradiction.
* Hence `|D| = 18`, `Ĥ^g = D · V^g` and `D ⊓ V^g = ⊥`.

Finally write `y = d · v` with `d ∈ D`, `v ∈ V^g` (unique, since `Ĥ^g = D · V^g` and
`D ⊓ V^g = ⊥`), so `d ≠ 1` (else `y = v ∈ V^g`, but `y ∉ V^g` as `V^g` centralises `x` and `y`
inverts `x`).  Then `y * d * y = d` (compute: `y d y = (d v) d (d v) = d` using `d² = v² = 1`),
so `d ∈ Ĥ` is an involution inverted... rather *centralised* by `y`, whence `d ∈ invSetIn Ĥ y`;
and `d ∉ X` since `X` has odd order.  So `{1} ∪ X ∪ {d} ⊆ invSetIn Ĥ y` has four elements, and
`ncard_invSetIn_eq_cosetInvCount` turns this into `4 ≤ cosetInvCount Ĥ y`.

The same computation without the last step gives `n ≠ 3` (indeed `n ≥ 4`); the `n = 3` case is
what `J4/J4SevenNeThree.lean` proves, by the same Steps 1–5 followed by a case analysis.

## Route for `Work.CORE3.Case1bSevenNeSix` (`n ≠ 6`)

`Submission/Work/CORE3/J4/NOTES_J4SevenD6.md` §(1) + §(2) contain a complete proof of `n ≠ 6`
from the (7)-configuration, using **neither `|U| = 3` nor `|D| = 6`** (and hence no (7)).  Sketch:

1. `I ⊓ VU = {1}` (Bender (5)), so `I → Ĥ/VU` is injective and order-preserving
   (`İ.T.c15`/`pow_mem_invSetIn`); with `|I| = 6 = |Ĥ/VU| = |S₃|` this makes `I` bijective onto
   `S₃`, so `I = {1, a, a², b₁, b₂, b₃}` with `orderOf a = 3` and the `bᵢ` involutions, and
   `X = ⟨a⟩` (as `|X| = 3` and `I` has exactly two elements of order `3`).
2. For `b ∈ I` an involution, `b I b⁻¹ = I`, so `b a b⁻¹ ∈ {a, a²}`; `b a b⁻¹ = a` would give `ab`
   of order `6`, impossible since `Ĥ/VU ≅ S₃` has no element of order `6`.  Hence `b a b = a⁻¹`,
   and then `b y` centralises `X`, is an involution, and lies outside `Ĥ`.
3. Global input (`J4/NOTES_J4SevenD6.md` §(2), formalised in `J4.J4ConjKAndNormalizer`, and also
   available from the clean `Work.CORE3.SevenConjK_conj`): there is `g` with `X ≤ K^g ≤ U^g` and
   `N_G(X) ≤ Ĥ^g`; then `N_G(X) = Ĥ^g`, `[N_G(X) : C_G(X)] = 2`, `|C_G(X)| = 12|U|`,
   `V^g = O₂(Ĥ^g) ≤ C_G(X)` is the unique Sylow 2-subgroup of `C_G(X)`, and
   `C_G(X) = V^g × O(C_G(X))` — so **every involution of `C_G(X)` lies in `V^g`**.
4. Thus `b₁y, b₂y, b₃y` are three distinct elements of `V^g ∖ {1}`, i.e. all of it; but
   `(b₁y)(b₂y) = b₁b₂ ∈ V^g` gives `b₁b₂ ∈ {b₁y, b₂y, b₃y}`, forcing `b₂ = y`, `b₁ = y` or
   `y = b₃b₁b₂ ∈ Ĥ` — all false.  Contradiction.

## Route for `Work.CORE3.Case1bSevenXCentU` (`X ≤ C_G(U)`)

`J4/NOTES_J4SevenD6.md` §(3)(D) shows `|U| = 3` is *equivalent* to `X ≤ C_G(U)`, and §(4)
sketches the proof; with §(3)(B), §(3)(C), §(3)(E) and `Work.CORE3.UInternalDirect` it reads:

1. pick an involution `s ∈ Ĥ ∖ V` (`Case1bData.inv` applies to it); then
   `K = I_U(s) = [U,s] ⊆ U` and `U = K × C_U(s)` (`Work.CORE3.UInternalDirect`);
2. `[X,U] ≤ K`: `Ĥ` acts on `K` through `Ĥ/VU ≅ S₃`, every transposition acting by inversion, so
   `A₃` acts trivially; and `Ĥ` acts trivially on `U/K` because every involution of `Ĥ ∖ V` acts
   trivially there, so the kernel contains `O²(Ĥ) ∋ x` (`X ≅ C₃`);
3. for `1 ≠ c ∈ C_U(s)`: `⟨c⟩ ≤ U = F(U)`, so local control plus `U ◁ Ĥ` gives
   `N_G(⟨c⟩) = Ĥ`; as `x ∈ Ĥ` we get `x c x⁻¹ ∈ ⟨c⟩ = {1, c, c²}`, and `x c x⁻¹ ∈ cK` by step 2,
   so `x c x⁻¹ = c` unless `c ∈ K ⊓ C_U(s) = 1`;
4. `X ≤ C_G(K) ∩ C_G(C_U(s)) = C_G(U)`, and `|U| = 3` follows by §(3)(D).
-/

namespace Work.CORE3

end Work.CORE3
