/-
# §4 of Peterfalvi I Ch. III: the intermediate conclusions, named

This module `sorry`-free: it contains only definitions.  It packages the conclusions of the four
mathematical steps that turn `Setup45A` into `Setup5` (`Submission.Work.NormalComplement.Design`):

* `Lemma1dConc` — Ch. III §4 Lemma 1 (d) (p.179): `P` is a `p`-Sylow of `D = H ⊓ H^t` and
  `E = W ⊓ D` is the semidirect product `E' ⋊ P`.
* `Prop1Conc` — Ch. III §4 Proposition 1 (p.180): `C_A(P)` is a Hall `π`-subgroup of `D`
  (π = `Design.piSec4 H t p`) and `⟨K⟩[A,P]P` is a normal complement of it in `D`.
* `Prop2aConc` — §4 Proposition 2 (a): `E = K[A,P]P`, `E' = K[A,P]`, `E' ⊓ V = [A,P]`.
* `Prop2bConc` — §4 Proposition 2 (b): `E'` is nilpotent, Hall in `G`, and has the primes of `|K|`.
* `Prop2cdConc` — §4 Proposition 2 (c),(d): `|K| = r^a (2^p - 1)` and `F(V) = E' ⊓ V` is a Sylow
  `r`-subgroup of `V`.

The statements are exactly those of `Submission/Work/NormalComplement/_design/Sec4.lean`
(`Setup45A` + the extra hypotheses), with the conclusions extracted as `def`s so that each step can
be proved and consumed independently: see `Submission/Work/NormalComplement/NOTES_LEAD_bs_normalcomplement.md`
§1.3, items 18–29, and `REFS/peterfalvi_I_ch3_4.md` §4 (pp.179–181) for the source.

Two inputs are worth recording for the proofs of these steps:

* `IsTwoTransitiveOn H` (= `MulAction.IsMultiplyPretransitive G (G ⧸ H) 2`, Theorem A of Ch. I) is
  **derivable** from the standing `hFT : FeitThompsonProp` in this workspace: Hering's/ZJ's and
  Brauer–Suzuki's inputs are available as the theorems
  `Work.ThmF.ChV12.glaubermanZJ_free : GlaubermanZJProp`,
  `Work.ThreePoints.brauerSuzukiProp_unconditional : BrauerSuzukiProp`, so
  `Work.DoubleTransitivity.Sec7.ThmA hFT glaubermanZJ_free brauerSuzukiProp_unconditional :
  ThmAProp`.  Ch. III §4 Prop. 1 step 3 (the only place needing it) uses it through App. II(5)
  `Work.DoubleTransitivity.App2.app2_5`.
* Ch. II §4 Prop. 3 with a *subnormal* `Y` (the `P3` clause of `Setup45A`) is the given
  `hP3 : ChIIFourP3SubnormalProp`, used as `p3Normal_of_chIIFourP3Subnormal` and
  `sec4_prop1_star` (already proved).
-/
import Mathlib
import Submission.Work.NormalComplement.Design.Extra
import Submission.Work.NormalComplement.Sections

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option autoImplicit false

open Classical
open scoped Pointwise commutatorElement
open LeanEval.GroupTheory.Defs
open Submission.Blueprint

namespace Work.NormalComplement.NC4

variable {G : Type*} [Group G] [Finite G]

/-- **Ch. III §4 Lemma 1 (d)** (p.179): `P` is a `p`-Sylow subgroup of `D = twoPoint H t` and
`E = W ⊓ D` satisfies `E' ⊓ P = ⊥`, `E' ⊔ P = E`, i.e. `E = E' ⋊ P`.

Source route: suppose `P` is not a `p`-Sylow of `D`; by Lemma 1 (c) a `p`-Sylow of `D` is not
cyclic; `Section2Prop` with `W = H` gives `D` `p`-control in `H` (the second alternative of
`Section2Prop` is impossible, it demands a *cyclic* Sylow); `TransferProp` with a `p`-element
`y ∈ E ∖ E'` (`exists_ppow_notMem_of_dvd_index` + `h.dvd`) gives `P ⊄ O^p(H)`, hence `P ⊄ O^p(W)`,
and `StrategyProp` contradicts the minimality of `W`.  For the second part, Lemma 1 (c) gives
`E = M ⋊ P`; if `E' ≠ M` some prime `q ≠ p` divides `|E : E'|`, (D1) gives `1 ≠ Q ≤ E ⊓ V` a
`q`-subgroup acting fixed-point-freely on `K`, but `Q ≤ A` centralises `C_K(A) ≠ 1`
(`Setup45A.A_CK`), contradicting App. I (1)(b). -/
def Lemma1dConc (H : Subgroup G) (t : G) (W : Subgroup G) (p : ℕ) (P A : Subgroup G) : Prop :=
  Work.NormalComplement.IsSylowIn p P (twoPoint H t) ∧
    Design.Ecomm H t W ⊓ P = ⊥ ∧
    Design.Ecomm H t W ⊔ P = Design.Egrp H t W

/-- **Ch. III §4 Proposition 1** (p.180): `C_A(P)` is a Hall `π`-subgroup of `D` (`π =
Design.piSec4 H t p`), `⟨K⟩ ⊓ V ≤ [A,P]`, and `⟨K⟩[A,P]P` is a normal complement of `C_A(P)` in
`D`.

Source route (steps 1–6 of the source; `_design/Sec4.lean` `sec4_prop1_step1`…`step5`):
1. `C_A(P)` is Hall in `N_H(P)` with a normal complement there: formula (∗) (`sec4_prop1_star`,
   proved) + `ControlCorollaryProp` (`hCC`) with `W = N_H(P)`, `E = C_A(P)`.
2. If `C_A(P) ≠ 1` then `P` is not a `p`-Sylow of `H`: Frattini + `Work.NPC.burnside_npc` on `W`,
   contradicting minimality.
3. Every Sylow `R` of `C_A(P)` has `|R| ∣ p - 1`: `AppII5` (needs `IsTwoTransitiveOn H`, see the
   header) applied to `G` acting on `Ω = G ⧸ H` with the Sylow `P` of the two-point stabiliser
   `D`, then `AppIIIProp` (`hIII`) clause (5) on `N_G(P)/N` (`N` the kernel on `Ω_P`) gives `P₁N/N`
   cyclic, so `P₁/P` is cyclic, and `R` acts fixed-point-freely on `Ω₁(P₁/P)` of order `p`.
4. `C_A(P)` is a `π`-group (`p ∤ |C_A(P)|` by Lemma 1 (d); if `r ∣ |A|` and `r ∣ |K|`, take an
   `r`-Sylow `R` of `A` normalised by `P`: orbit decomposition gives `r ∣ |C_K(R)| = 2^p - 1`
   (`Setup45A.A_B`), so `ord_r 2 = p`, `p ≤ r - 1`, and step 3 forbids `r ∣ |C_A(P)|`).
5. `C_A(P)` is Hall in `D` (App. VII `hVII` with `K = ⟨K⟩`, `Q = R`, `P`; then `C_V(K) = 1` by
   (D2) gives `[R,P] = 1`).
6. Conclusion: `appI_five_b` with `d = p` gives `[A,P]` a normal complement of `C_A(P)` in `A`. -/
def Prop1Conc (H : Subgroup G) (t : G) (W : Subgroup G) (p : ℕ) (P A : Subgroup G) : Prop :=
  (∀ r : ℕ, r.Prime → r ∣ Nat.card ↥(A ⊓ Subgroup.centralizer (P : Set G)) →
      Design.piSec4 H t p r) ∧
    (∀ r : ℕ, Design.piSec4 H t p r →
      ¬ r ∣ (A ⊓ Subgroup.centralizer (P : Set G)).relIndex (twoPoint H t)) ∧
    Work.NormalComplement.Kgrp (twoPoint H t) t ⊓ centD H t ≤ Design.commSub A P ∧
    Work.NormalComplement.IsNormalComplementOf
      ((Work.NormalComplement.Kgrp (twoPoint H t) t ⊔ Design.commSub A P) ⊔ P)
      (A ⊓ Subgroup.centralizer (P : Set G)) (twoPoint H t)

/-- **Ch. III §4 Proposition 2 (a)** (p.181): `E = K[A,P]P`, `E' = K[A,P]`, `E' ⊓ V = [A,P]`.

Source route: `E ⊴ D`, so Frattini with the `p`-Sylow `P` of `D` and Lemma 1 (c) give
`D = E N_D(P) = E C_A(P)`; hence `K[A,P]P ≤ E` by Prop. 1; by Lemma 1 (d) `E = K[A,P]P`,
`E' = K[A,P]` and `E' ⊓ V = [A,P]` (using `E ⊓ V = A ⋊ P` again). -/
def Prop2aConc (H : Subgroup G) (t : G) (W : Subgroup G) (p : ℕ) (P A : Subgroup G) : Prop :=
  Design.Egrp H t W =
      (Work.NormalComplement.Kgrp (twoPoint H t) t ⊔ Design.commSub A P) ⊔ P ∧
    Design.Ecomm H t W = Work.NormalComplement.Kgrp (twoPoint H t) t ⊔ Design.commSub A P ∧
    Design.Ecomm H t W ⊓ centD H t = Design.commSub A P

/-- **Ch. III §4 Proposition 2 (b)** (p.181): `E'` is nilpotent, `E'` is a Hall subgroup of `G`,
and `|E'|` has the same prime divisors as `|K|`.

Source route: by Prop. 1, `C_A(P) ⊓ E' = 1`, so `C_{E'}(P) = 1`; conjugation by a generator of `P`
is then a fixed-point-free automorphism of prime order `p` of the solvable (odd order, `hFT`) group
`E'`, so `E'` is nilpotent (`Work.Frobenius.Fpf.isNilpotent_of_fpf_prime`).  By (a) and Prop. 1,
`E'` is Hall in `D` and has the primes of `K`; `E'` is Hall in `G` by Ch. II §4 Prop. 2 (d)
(`sec4_P2d`): for every prime `r ∣ |K|`, `D` contains a Sylow `r`-subgroup of `G`. -/
def Prop2bConc (H : Subgroup G) (t : G) (W : Subgroup G) (p : ℕ) (P A : Subgroup G) : Prop :=
  Group.IsNilpotent ↥(Design.Ecomm H t W) ∧
    Nat.Coprime (Nat.card ↥(Design.Ecomm H t W)) (Design.Ecomm H t W).index ∧
    ∀ r : ℕ, r.Prime →
      (r ∣ Nat.card ↥(Design.Ecomm H t W) ↔ r ∣ (Kset (twoPoint H t) t).ncard)

/-- **Ch. III §4 Proposition 2 (c), (d)** (p.181): `|K| = r^a (2^p - 1)` with `a ≥ 1` and `r` a
prime divisor of `2^p - 1`; `F(V) = E' ⊓ V ≠ 1`, and `F(V)` is an `r`-Sylow of `V`.

Source route (c): by (D2) `E' ⊓ V ≠ 1`; let `r ∣ |E' ⊓ V|` and `R` the `r`-Sylow of `E' ⊓ V`.  By
(b), `E' = S₁ × S₂` with `S₁ = O_r(E')`, `S₂ = O_{r'}(E')`, `R ≤ S₁`; put `K_i = J(S_i,t)` and get
`K = K₁ × K₂` (`t` normalises `S_i`, `K ⊆ E'`).  Lemma 1 (b) gives `|C_K(R)| = 2^p - 1`; since
`C_K(R) = C_{K₁}(R) × K₂`, the ratio `|K|/(2^p - 1) = |K₁|/|C_{K₁}(R)|` is a power of `r`; by
`C_V(K) = 1` one has `Z(S₁) ⊓ V = 1`, so `1 ≠ Z(S₁) ≤ C_{K₁}(R)`, hence `r ∣ 2^p - 1`; and
`|K| = 2^p - 1` would make `R` centralise `K` (as `R ≤` … and `K₂ ⊆ C_K(R)`), contradicting
`C_V(K) = 1`, so `|K| > 2^p - 1`.  (d): `|E' ⊓ V|` has the single prime divisor `r`, so `R = E' ⊓ V`
is a Sylow `r` of `V` and is normal in `V`, hence `R ≤ F(V)`.  Write `F(V) = R × Q`; `Q ≤ A`
because `P ⊄ V` and `P ⊓ F(V) = 1`; then `Q` centralises `C_K(R) = C_K(A)`, hence
`C_{S₁}(R) = Z(S₁)C_{K₁}(R)` (App. I (1)) is centralised by `Q`, and App. IV Lemma 4 (Thompson–Bender,
available as `Work.Coprime.thompson_PxQ`, applied to the direct product `R × Q` acting on `S₁`)
makes `Q` centralise `S₁`; with `Q` centralising `K₂` too, `Q` centralises `K`, so `Q = 1` by
`C_V(K) = 1`. -/
def Prop2cdConc (H : Subgroup G) (t : G) (W : Subgroup G) (p : ℕ) (P A : Subgroup G) : Prop :=
  ∃ r a : ℕ, r.Prime ∧ 1 ≤ a ∧ r ∣ 2 ^ p - 1 ∧
    (Kset (twoPoint H t) t).ncard = r ^ a * (2 ^ p - 1) ∧
    Design.fitSub (centD H t) = Design.Ecomm H t W ⊓ centD H t ∧
    Design.fitSub (centD H t) ≠ ⊥ ∧
    Work.NormalComplement.IsSylowIn r (Design.fitSub (centD H t)) (centD H t)

end Work.NormalComplement.NC4
