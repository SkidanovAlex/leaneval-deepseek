import Submission.Work.ZJB.Step1.Assembly
import Submission.Work.ZJB.Subquotient
import Submission.Work.ZJB.AutLemma
import Submission.Work.GLUE.PcoreApi

/-!
# gorenstein_walter, ZJB2 — vocabulary and leaf statements (design pass 17, item B)

Companion to `Submission/Work/NOTES_LEAD_gw_design17.md` (Item B).  Glauberman 1968
(`REFS/vision/glauberman1968_zj/p0017`–`p0022`, `p0025`): Theorem 5.1 steps (II)–(IV),
Lemma 5.2, Theorem 5.2 and the induction proving Theorem B (p. 1125).

* Everything is stated *inside* the ambient group `G`, in the paper's convention
  (`W^g = g⁻¹ W g`), on top of the design-11 vocabulary of `ZJB/Step1/Defs.lean`
  (`pconj`, `IsSylowIn`, `CpIn`, `CpStarIn`, `HypA`, `Step1Prop`, …).
* Only three statements change the ambient type: `Lemma52Prop` (about an arbitrary `H`),
  `ZJMapProp` (a homomorphism), and the hypotheses of Theorem 5.2 about `G ⧸ O_p(G)` and the
  subquotients (supplied in the final induction).
* Each leaf is a `…Prop`; its file is `Submission/Work/ZJB2/<leaf>.lean` (statement + route).
  The assemblies (`ZJB2/Assembly.lean`) are proved from these `Prop`s with no `sorry`.

**IMPORTANT for provers.**  Do *not* import `Submission.Work.CORE2A.*` (in particular
`Submission.Work.CORE2A.map_ZJ_subtype`): it pulls in `Submission.Work.ASM.Defs`, a second copy of
the `Work.GW2` vocabulary whose declarations clash with `Submission.Work.GLUE.Defs`.  The two
transport facts that live there, and which several routes below refer to, must be reproved
locally if needed:

* `(thompsonJ P).map f = thompsonJ (P.map f)` for an injective `f` — `Work.GW2.thompsonJ` is
  `Subgroup.thompsonJAbelian` (`Work.GW2.thompsonJ_eq_thompsonJAbelian`), and the odd-order
  library has `Subgroup.thompsonJAbelian_map_of_injective`,
  `Subgroup.thompsonJAbelian_map_of_disjoint_ker`;
* `(T ⊓ C(T)).map f = T.map f ⊓ C(T.map f)` for an injective `f` —
  `Subgroup.map_centralizer_inf_of_disjoint_ker` (odd-order library).

Both are in the import closure of this module (`Submission.Work.GLUE.*` → `Submission.OddOrder.*`).
-/

namespace Work.ZJB

open Work.GW2
open Subgroup

/-- `O_π(H)` is normal (it is a `normalCore`). -/
instance piCore_normal' (π : Set ℕ) (H : Type*) [Group H] : (piCore π H).Normal :=
  Subgroup.normalCore_normal _

/-! ## 0. Vocabulary -/

/-- `O_{p'}(H)`. -/
abbrev OpPrime (p : ℕ) (H : Type*) [Group H] : Subgroup H := piCore {q | q ≠ p} H

/-- `O_{p',p}(H)`: the preimage of `O_p(H / O_{p'}(H))`. -/
def OppCore (p : ℕ) (H : Type*) [Group H] : Subgroup H :=
  (pCore p (H ⧸ OpPrime p H)).comap (QuotientGroup.mk' (OpPrime p H))

/-- `C_G(V̄)`, `V̄ = VP/P`: the preimage in `G` of `C_{G/P}(VP/P)`. -/
def Cbar {G : Type*} [Group G] (P : Subgroup G) [P.Normal] (V : Subgroup G) : Subgroup G :=
  (centralizer ((V.map (QuotientGroup.mk' P) : Subgroup (G ⧸ P)) : Set (G ⧸ P))).comap
    (QuotientGroup.mk' P)

/-- The paper's `(C_p)` for one subgroup `W` of `S` (convention `W^g = g⁻¹Wg`):
every `g` with `W^g ⊆ S` is `c n` with `c ∈ C(W)`, `n ∈ N(Z(J(S)))`. -/
def GoodFor {G : Type*} [Group G] (S W : Subgroup G) : Prop :=
  ∀ g : G, (∀ w ∈ W, g⁻¹ * w * g ∈ S) →
    ∃ c n : G, c ∈ centralizer (W : Set G) ∧ n ∈ normalizer (ZJ S : Set G) ∧ g = c * n

/-- Hypothesis (a) of Theorem 5.2, for every subquotient `Y ⧸ L` of `G`.  For the D-class this is
`Work.ZJB.zj_normal_of_subquotient` (from `ZJAProp` + `DihOrCycHeredProp`). -/
def SubquotA (p : ℕ) (G : Type) [Group G] : Prop :=
  ∀ (Y : Subgroup G) (L : Subgroup Y) [L.Normal],
    centralizer (pCore p (Y ⧸ L) : Set (Y ⧸ L)) ≤ pCore p (Y ⧸ L) →
    ∀ Q : Sylow p (Y ⧸ L), (ZJ (Q : Subgroup (Y ⧸ L))).Normal

/-- `R = P C(P) ∩ S`, `P = O_p(G)` (Theorem 5.2's proof, p. 1121). -/
noncomputable def Rsub (p : ℕ) (G : Type) [Group G] (S : Subgroup G) : Subgroup G :=
  (pCore p G ⊔ centralizer (pCore p G : Set G)) ⊓ S

/-- `M = O_{p'}(N(R))`, as a subgroup of `G`. -/
noncomputable def MR (p : ℕ) (G : Type) [Group G] (S : Subgroup G) : Subgroup G :=
  (OpPrime p ↥(normalizer (Rsub p G S : Set G))).map (normalizer (Rsub p G S : Set G)).subtype

/-! ## 1. Generic Sylow leaves (G1–G4) -/

/-- **G1.** Sylow conjugacy inside `M`: a `p`-subgroup `V ≤ M` is conjugated into a Sylow
subgroup `T` of `M` by an element of `M`. -/
def SylowInConjProp (p : ℕ) (G : Type) [Group G] [Finite G] : Prop :=
  ∀ T M V : Subgroup G, IsSylowIn p T M → V ≤ M → IsPGroup p V →
    ∃ m ∈ M, ∀ v ∈ V, m⁻¹ * v * m ∈ T

/-- **G2.** A Sylow subgroup of `M` meets a normal subgroup `L` of `M` in a Sylow subgroup
of `L`. -/
def SylowInInfNormalProp (p : ℕ) (G : Type) [Group G] [Finite G] : Prop :=
  ∀ T M L : Subgroup G, IsSylowIn p T M → L ≤ M → M ≤ normalizer (L : Set G) →
    IsSylowIn p (T ⊓ L) L

/-- **G3.** A Sylow subgroup of `G` inside `M` is Sylow in `M`. -/
def IsSylowInOfLeProp (p : ℕ) (G : Type) [Group G] [Finite G] : Prop :=
  ∀ (S : Sylow p G) (M : Subgroup G), (S : Subgroup G) ≤ M → IsSylowIn p S M

/-- **G4.** For a `p`-subgroup `U ≤ Y` there is a conjugate (`x U x⁻¹`) lying in `S` such that
`S` meets the conjugate `xYx⁻¹` in a Sylow subgroup of it. -/
def ExistsConjSylowInProp (p : ℕ) (G : Type) [Group G] [Finite G] : Prop :=
  ∀ (S : Sylow p G) (Y U : Subgroup G), U ≤ Y → IsPGroup p U →
    ∃ x : G, U.map (MulAut.conj x).toMonoidHom ≤ S ∧
      IsSylowIn p (Y.map (MulAut.conj x).toMonoidHom ⊓ S) (Y.map (MulAut.conj x).toMonoidHom)

/-! ## 2. Theorem 5.1, steps (II)–(IV) (pp. 1119–1120) -/

/-- **T51.II** (C_p) for `W = Z(S)`, from step (I)'s conclusion for `S`. -/
def Step2Prop (p : ℕ) (G : Type) [Group G] [Finite G] : Prop :=
  ∀ S : Sylow p G,
    (∀ g : G, pconj (ZS (S : Subgroup G)) g ≤ S →
      pconj (ZS (S : Subgroup G)) g ≤ ZJ (S : Subgroup G)) →
    GoodFor (S : Subgroup G) (ZS (S : Subgroup G))

/-- **T51.III** (C_p) for `W` with `C_S(W) ∈ Syl_p(C(W))`, from (II) and `(C_p*)` in
`N(Z(S))`. -/
def Step3Prop (p : ℕ) (G : Type) [Group G] [Finite G] : Prop :=
  ∀ S : Sylow p G, GoodFor (S : Subgroup G) (ZS (S : Subgroup G)) →
    CpStarIn p (normalizer (ZS (S : Subgroup G) : Set G)) →
    ∀ W : Subgroup G, W ≤ S →
      IsSylowIn p (centralizer (W : Set G) ⊓ S) (centralizer (W : Set G)) →
      GoodFor (S : Subgroup G) W

/-- **T51.IV-alg** (the "method of step (IV)", pure algebra, used twice: Theorem 5.1 (IV) and
the end of Theorem 5.2).  If `GoodFor S V` holds for all `V ≤ S` with `Cond V`, and `W ≤ S` has a
conjugate `V = xWx⁻¹ ≤ S` with `Cond V`, then `GoodFor S W`.  PROVED in `ZJB2/ivMethod.lean`. -/
def IVMethodProp (G : Type) [Group G] : Prop :=
  ∀ (S : Subgroup G) (Cond : Subgroup G → Prop),
    (∀ V : Subgroup G, V ≤ S → Cond V → GoodFor S V) →
    ∀ W : Subgroup G, W ≤ S →
      (∃ x : G, W.map (MulAut.conj x).toMonoidHom ≤ S ∧ Cond (W.map (MulAut.conj x).toMonoidHom)) →
      GoodFor S W

/-- **T51.IV-ex** Every `W ≤ S` has a conjugate `V ≤ S` with `C_S(V) ∈ Syl_p(C(V))`. -/
def CondExists51Prop (p : ℕ) (G : Type) [Group G] [Finite G] : Prop :=
  ∀ (S : Sylow p G) (W : Subgroup G), W ≤ S →
    ∃ x : G, W.map (MulAut.conj x).toMonoidHom ≤ S ∧
      IsSylowIn p (centralizer (W.map (MulAut.conj x).toMonoidHom : Set G) ⊓ S)
        (centralizer (W.map (MulAut.conj x).toMonoidHom : Set G))

/-! ## 3. Lemma 5.2 and Theorem 5.2 (pp. 1120–1122) -/

/-- **L52** Glauberman's Lemma 5.2: `P₁ = S ∩ O_{p',p}(H)`; if `C_S(P₁) ≤ P₁` then
`H / O_{p'}(H)` is `p`-constrained. -/
def Lemma52Prop (p : ℕ) [Fact p.Prime] : Prop :=
  ∀ (H : Type) [Group H] [Finite H] (S : Sylow p H),
    centralizer (((S : Subgroup H) ⊓ OppCore p H : Subgroup H) : Set H) ⊓ S ≤
        (S : Subgroup H) ⊓ OppCore p H →
      centralizer (pCore p (H ⧸ OpPrime p H) : Set (H ⧸ OpPrime p H)) ≤
        pCore p (H ⧸ OpPrime p H)

/-- **ZJMap** `Z(J(·))` commutes with a homomorphism that is injective on `S`
(the "characteristic functor" property (c), p. 1116, used for `K(SM/M) = K(S)M/M`). -/
def ZJMapProp (G : Type) [Group G] [Finite G] : Prop :=
  ∀ (H : Type) [Group H] [Finite H] (f : G →* H) (S : Subgroup G), f.ker ⊓ S = ⊥ →
    ZJ (S.map f) = (ZJ S).map f

/-- **Frat** The Frattini argument relative to `M`: `L ⊴ M`, `T ∈ Syl_p(L)` ⟹
`M = L·N_M(T)`. -/
def FrattiniInProp (p : ℕ) (G : Type) [Group G] [Finite G] : Prop :=
  ∀ M L T : Subgroup G, L ≤ M → M ≤ normalizer (L : Set G) → IsSylowIn p T L →
    ∀ g ∈ M, ∃ l ∈ L, ∃ n ∈ M ⊓ normalizer (T : Set G), g = l * n

/-- **NRc** Lemma 5.2 applied to `N(R)`: `N(R)/O_{p'}(N(R))` is `p`-constrained. -/
def NormRConstrainedProp (p : ℕ) [Fact p.Prime] (G : Type) [Group G] [Finite G] : Prop :=
  ∀ S : Sylow p G,
    centralizer (pCore p (↥(normalizer (Rsub p G S : Set G)) ⧸
        OpPrime p ↥(normalizer (Rsub p G S : Set G))) :
        Set (↥(normalizer (Rsub p G S : Set G)) ⧸ OpPrime p ↥(normalizer (Rsub p G S : Set G)))) ≤
      pCore p (↥(normalizer (Rsub p G S : Set G)) ⧸ OpPrime p ↥(normalizer (Rsub p G S : Set G)))

/-- **NRf** (5.5): `N(R) = O_{p'}(N(R))·N_{N(R)}(Z(J(S)))`, from hypothesis (a) at the
subquotient `N(R)/O_{p'}(N(R))`. -/
def NormRFactorProp (p : ℕ) [Fact p.Prime] (G : Type) [Group G] [Finite G] : Prop :=
  SubquotA p G → ∀ S : Sylow p G, ∀ r ∈ normalizer (Rsub p G S : Set G),
    ∃ m ∈ MR p G S, ∃ k ∈ normalizer (ZJ (S : Subgroup G) : Set G), r = m * k

/-- **MRc** `[P, O_{p'}(N(R))] = 1`. -/
def MRCentralizesProp (p : ℕ) [Fact p.Prime] (G : Type) [Group G] [Finite G] : Prop :=
  ∀ S : Sylow p G, MR p G S ≤ centralizer (pCore p G : Set G)

/-- **T52.lt** The case `C(P)S < G` (p. 1121): from `G = C(P)·N` and `(C_p*)` in `C(P)S`. -/
def Case52ProperProp (p : ℕ) [Fact p.Prime] (G : Type) [Group G] [Finite G] : Prop :=
  ∀ S : Sylow p G,
    (∀ g : G, ∃ c ∈ centralizer (pCore p G : Set G),
      ∃ n ∈ normalizer (ZJ (S : Subgroup G) : Set G), g = c * n) →
    CpStarIn p (centralizer (pCore p G : Set G) ⊔ S) →
    ControlsStrongFusionPaper (S : Subgroup G) (ZJ (S : Subgroup G))

/-- **T52.mod** (5.6)–(5.8): `(C_p)` in `G/P` and in the proper subgroup `N(T)`,
`T/P = Z(J(S/P))`, give `g ∈ C_G(V̄)·N`. -/
def ModPStepProp (p : ℕ) [Fact p.Prime] (G : Type) [Group G] [Finite G] : Prop :=
  (∀ M : Subgroup G, M ≠ ⊤ → CpIn p M) → SatisfiesCpPaper p (G ⧸ pCore p G) →
    ∀ S : Sylow p G, ∀ V : Subgroup G, V ≤ S → ¬ V ≤ pCore p G →
      ∀ g : G, (∀ v ∈ V, g⁻¹ * v * g ∈ S) →
        ∃ y ∈ Cbar (pCore p G) V, ∃ n ∈ normalizer (ZJ (S : Subgroup G) : Set G), g = y * n

/-- **T52.53** (Lemma 5.3 step, p. 1122): when `G = C(P)S`, a `p'`-element of `C_G(V̄)`
centralizes `VP`. -/
def PPrimeCentralizesProp (p : ℕ) [Fact p.Prime] (G : Type) [Group G] [Finite G] : Prop :=
  ∀ S : Sylow p G,
    (∀ g : G, ∃ c ∈ centralizer (pCore p G : Set G), ∃ s ∈ (S : Subgroup G), g = c * s) →
    ∀ V : Subgroup G, V ≤ S → ∀ y ∈ Cbar (pCore p G) V, (orderOf y).Coprime p →
      y ∈ centralizer ((V ⊔ pCore p G : Subgroup G) : Set G)

/-- **T52.fac** If `L ⊴ H` contains every `p'`-element of `H` and `Q ∈ Syl_p(H)`, then
`H = L·Q`. -/
def FactorPPrimeProp (p : ℕ) [Fact p.Prime] (G : Type) [Group G] [Finite G] : Prop :=
  ∀ H L Q : Subgroup G, L ≤ H → H ≤ normalizer (L : Set G) →
    (∀ y ∈ H, (orderOf y).Coprime p → y ∈ L) → IsSylowIn p Q H →
    ∀ y ∈ H, ∃ l ∈ L, ∃ q ∈ Q, y = l * q

/-- **T52.nrm** `C_G(V̄)` normalizes `C(VP) ∩ C_G(V̄)`. -/
def CbarNormalizesProp (p : ℕ) [Fact p.Prime] (G : Type) [Group G] [Finite G] : Prop :=
  ∀ V : Subgroup G,
    Cbar (pCore p G) V ≤
      normalizer ((centralizer ((V ⊔ pCore p G : Subgroup G) : Set G) ⊓
        Cbar (pCore p G) V : Subgroup G) : Set G)

/-- **T52.ex** Every `W ≤ S` has a conjugate `V ≤ S` with `V ≤ P` or
`C_S(V̄) ∈ Syl_p(C_G(V̄))`. -/
def CondExists52Prop (p : ℕ) [Fact p.Prime] (G : Type) [Group G] [Finite G] : Prop :=
  ∀ (S : Sylow p G) (W : Subgroup G), W ≤ S →
    ∃ x : G, W.map (MulAut.conj x).toMonoidHom ≤ S ∧
      (W.map (MulAut.conj x).toMonoidHom ≤ pCore p G ∨
        IsSylowIn p (Cbar (pCore p G) (W.map (MulAut.conj x).toMonoidHom) ⊓ S)
          (Cbar (pCore p G) (W.map (MulAut.conj x).toMonoidHom)))

/-! ## 4. The induction (p. 1125) -/

/-- **B.bot** `S = 1` (`p ∤ |G|`): `(C_p)` is trivial.  PROVED in `ZJB2/cpOfSylowBot.lean`. -/
def CpOfSylowBotProp (p : ℕ) (G : Type) [Group G] [Finite G] : Prop :=
  ∀ S : Sylow p G, (S : Subgroup G) = ⊥ →
    ControlsStrongFusionPaper (S : Subgroup G) (ZJ (S : Subgroup G))

/-- **B.hypA** `O_p(G) = 1`, `S ≠ 1`: every `N(H)`, `Z(S₂) ≤ H ≤ S₂`, is proper, so the
induction hypothesis gives hypothesis (a) of Theorem 5.1. -/
def HypAOfCoreBotProp (p : ℕ) [Fact p.Prime] (G : Type) [Group G] [Finite G] : Prop :=
  pCore p G = ⊥ → (∀ M : Subgroup G, M ≠ ⊤ → CpIn p M) →
    (∃ S : Sylow p G, (S : Subgroup G) ≠ ⊥) → HypA p G

/-! ## 5. All leaves, bundled -/

/-- The full leaf set of ZJB2 (each field quantified over every finite group and prime). -/
structure Leaves : Prop where
  step1 : ∀ (G : Type) [Group G] [Finite G] (p : ℕ) [Fact p.Prime], Step1Prop p G
  l51 : ∀ (G : Type) [Group G] [Finite G] (p : ℕ) [Fact p.Prime], CpStarInOfCpInProp p G
  br : ∀ (G : Type) [Group G] [Finite G] (p : ℕ) [Fact p.Prime], CpInOfSatisfiesProp p G
  g2 : ∀ (G : Type) [Group G] [Finite G] (p : ℕ) [Fact p.Prime], SylowInInfNormalProp p G
  g3 : ∀ (G : Type) [Group G] [Finite G] (p : ℕ) [Fact p.Prime], IsSylowInOfLeProp p G
  step2 : ∀ (G : Type) [Group G] [Finite G] (p : ℕ) [Fact p.Prime], Step2Prop p G
  step3 : ∀ (G : Type) [Group G] [Finite G] (p : ℕ) [Fact p.Prime], Step3Prop p G
  ivAlg : ∀ (G : Type) [Group G], IVMethodProp G
  ex51 : ∀ (G : Type) [Group G] [Finite G] (p : ℕ) [Fact p.Prime], CondExists51Prop p G
  frat : ∀ (G : Type) [Group G] [Finite G] (p : ℕ) [Fact p.Prime], FrattiniInProp p G
  nrf : ∀ (G : Type) [Group G] [Finite G] (p : ℕ) [Fact p.Prime], NormRFactorProp p G
  mrc : ∀ (G : Type) [Group G] [Finite G] (p : ℕ) [Fact p.Prime], MRCentralizesProp p G
  lt52 : ∀ (G : Type) [Group G] [Finite G] (p : ℕ) [Fact p.Prime], Case52ProperProp p G
  modp : ∀ (G : Type) [Group G] [Finite G] (p : ℕ) [Fact p.Prime], ModPStepProp p G
  ppc : ∀ (G : Type) [Group G] [Finite G] (p : ℕ) [Fact p.Prime], PPrimeCentralizesProp p G
  fac : ∀ (G : Type) [Group G] [Finite G] (p : ℕ) [Fact p.Prime], FactorPPrimeProp p G
  nrm : ∀ (G : Type) [Group G] [Finite G] (p : ℕ) [Fact p.Prime], CbarNormalizesProp p G
  ex52 : ∀ (G : Type) [Group G] [Finite G] (p : ℕ) [Fact p.Prime], CondExists52Prop p G
  bot : ∀ (G : Type) [Group G] [Finite G] (p : ℕ) [Fact p.Prime], CpOfSylowBotProp p G
  hypA : ∀ (G : Type) [Group G] [Finite G] (p : ℕ) [Fact p.Prime], HypAOfCoreBotProp p G

end Work.ZJB
