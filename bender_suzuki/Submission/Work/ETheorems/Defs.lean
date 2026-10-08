/-
# Area P2-08 `Work.ETheorems` — Feit–Thompson, *Solvability of groups of odd order*,
Pacific J. Math. **13** (1963), Chapter IV §18–§20.

This module fixes the vocabulary of FT §18 (configurations, `𝒞(p)`, `𝒰(p)`, `𝒮𝒞𝒩₃(p)`),
§19 (`p ~ q`, Hypotheses 19.1–19.2, the family `𝓕(p)`, `𝓛(p)`) and §20 (Hypothesis 20.1).

The source used is the faithful transcription `Submission/Work/ft1963/tex/ch4a.md`
(printed pages 855–870); the OCR `ft1963/ch4.txt` was **not** used.  The conventions are those of
`NOTES_LEAD_ft_phase2.md` §1; in particular

* subgroups live in an ambient group `G`; a maximal subgroup is `M : Subgroup G` with
  `IsCoatom M`; a "`p`-subgroup" is `IsPGroup p P` with `P : Subgroup G`;
* `A^#` is `A \ {1}`, `N(A)` is `Subgroup.normalizer (A : Set G)`, `C(A)` is
  `Subgroup.centralizer (A : Set G)`;
* conjugation is `MulAut.conj g • H` (`Work.PGroup.conjBy g H`).

## The objects of §18

FT's configuration `(𝔎,𝔓,𝔄;𝔙,𝔐,𝔚)` (Def. 18.1) is `Work.ETheorems.Config p K P A` — the three
extra entries are *determined* by `(𝔎,𝔓,𝔄)` and are provided as the derived definitions
`Config.V`, `Config.M`, `Config.Op'`, `Config.Op'p`, `Config.Op'pp'`, `Config.ZW`, `Config.Z2W`.

`𝔚 = O_{p',p}(𝔎)/O_{p'}(𝔎)` is a quotient group; we never form it.  Instead `Config.ZW` is the
*preimage* in `↥K` of `Z(𝔚)` (i.e. the centre of the factor `O_{p',p}(𝔎)/O_{p'}(𝔎)`) and
`Config.Z2W` is the preimage of `Z₂(𝔚)`; the condition "`𝔐` centralizes `Z(𝔚)`" is then
`⁅c.M, c.ZW⁆ ≤ c.Op'`, and "`𝔐` centralizes `Z₂(𝔚)/Z(𝔚)`" is `⁅c.M, c.Z2W⁆ ≤ c.ZW`.  These are
exactly the conditions used in the proof of Lemma 18.1 ("`O_{p',p}(𝔎)` centralizes both `Z(𝔚)` and
`Z₂(𝔚)/Z(𝔚)`", "some element of `𝔐` induces a non identity `p'`-automorphism of `Z(𝔚)` or of
`Z₂(𝔚)/Z(𝔚)`").

## Notation

`pSeriesIn p n K` is `O_{p',p,p',…}(K)` (`n` symbols), so
`OpPrimeIn p K` is `O_{p'}(𝔎)`, `OpPrimePIn p K` is `O_{p',p}(𝔎)` and
`OpPrimePPPrimeIn p K` is `O_{p',p,p'}(𝔎)`.
-/
import Mathlib
import Submission.Work.Spine.Defs
import Submission.Work.Transitivity.Defs
import Submission.Work.LocalPrelim.Defs
import Submission.Work.PGroup.Basic

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

open scoped Classical Pointwise
open commutatorElement

set_option linter.unusedVariables false

noncomputable section

namespace Work.ETheorems

variable {G : Type*} [Group G] [Finite G]

/-! ## The upper `p`-series of a subgroup (FT's `O_{p'}`, `O_{p',p}`, `O_{p',p,p'}`, …) -/

/-- The `n`-th term of the upper `p`-series of the subgroup `K`, transported to the ambient group:
`pSeriesIn p 0 K = ⊥`, `pSeriesIn p 1 K = O_{p'}(K)`, `pSeriesIn p 2 K = O_{p',p}(K)`,
`pSeriesIn p 3 K = O_{p',p,p'}(K)`, … -/
def pSeriesIn (p n : ℕ) (K : Subgroup G) : Subgroup G :=
  (Work.Fitting.pCoreSeries p ↥K n).map K.subtype

/-- FT's `O_{p'}(𝔎)` for a subgroup `𝔎 ≤ 𝔊`. -/
def OpPrimeIn (p : ℕ) (K : Subgroup G) : Subgroup G := pSeriesIn p 1 K

/-- FT's `O_{p',p}(𝔎)` for a subgroup `𝔎 ≤ 𝔊`. -/
def OpPrimePIn (p : ℕ) (K : Subgroup G) : Subgroup G := pSeriesIn p 2 K

/-- FT's `O_{p',p,p'}(𝔎)` for a subgroup `𝔎 ≤ 𝔊`. -/
def OpPrimePPPrimeIn (p : ℕ) (K : Subgroup G) : Subgroup G := pSeriesIn p 3 K

/-- `OpqPIn a b K` is FT's `O_{a,b}(𝔎)`: the `a`-core of `𝔎` followed by the `b`-core, i.e. the
preimage in `𝔎` of `O_b(𝔎/O_a(𝔎))`.  FT use this notation in §19 for `O_{q,p}`, `O_{p,q}` and
`O_{q,p,q}` (e.g. pp. 859 and 862).

**Reading.**  FT write `O_{q,p}(𝔎)` in §19 (pp. 859–862) in place of `O_{p',p}(𝔎)`; for a
`{p,q}`-group `𝔎` the two *coincide*, because every `p'`-subgroup of `𝔎` is a `q`-group and
conversely, so `O_{p'}(𝔎) = O_q(𝔎)` (see `OpqPIn_eq_OpPrimePIn`).  The definitions of this area
therefore use `OpPrimePIn p K = O_{p',p}(𝔎)` for FT's `O_{q,p}(𝔎)`, and `OpPrimePIn p K` (not
`OpPrimePIn q K`, which is `O_{q',q}(𝔎)`) throughout `calK`, `calFA`, `calLP` and the statements of
Lemmas 19.4–19.9.  This matters: for a `{2,3}`-group such as `S₃`, `O_{2',2}(S₃) = A₃` while
`O_{3',3}(S₃) = A₃` — equal here by accident, but `O_{3',2}(S₃) = 1 ≠ O_{2',2}(S₃)`, so the
distinction between the *second* symbol `p` and the first symbol's complement is essential. -/
def OpqPIn (a b : ℕ) (K : Subgroup G) : Subgroup G :=
  ((Work.Fitting.pCore b (↥K ⧸ Work.Fitting.pCore a ↥K)).comap
    (QuotientGroup.mk' (Work.Fitting.pCore a ↥K))).map K.subtype

/-! ## The centre of a factor `L/H` and `Z₂(L/H)`

These are the only two pieces of quotient-group vocabulary that §18 needs; they are given as
subgroups of the ambient group by taking preimages of `Z(L/H)` and `Z₂(L/H)`. -/

/-- The preimage in `L` of the centre of the factor `L/H` (i.e. of `Z(L/H)`), for subgroups
`H ⊴ L` of an ambient group.  For `H = O_{p'}(𝔎)` and `L = O_{p',p}(𝔎)` this is the preimage in
`𝔎` of `Z(𝔚)` of FT Def. 18.2. -/
def factorCenter {X : Type*} [Group X] (H L : Subgroup X) [H.Normal] : Subgroup X :=
  Work.Fitting.sectionCentralizer H L ⊓ L

/-- The preimage in `L` of the second centre `Z₂(L/H)` of the factor `L/H`, for `H ⊴ L`. -/
def factorSecondCenter {X : Type*} [Group X] (H L : Subgroup X) [H.Normal] : Subgroup X :=
  ((Subgroup.upperCentralSeries (↥L ⧸ (H.subgroupOf L)) 2).comap
    (QuotientGroup.mk' (H.subgroupOf L))).map L.subtype

/-- `Z(L/H)` is cyclic: the centre of the factor `L/H` is generated by one element modulo `H`. -/
def IsFactorCyclic {X : Type*} [Group X] (H L : Subgroup X) [H.Normal] : Prop :=
  ∃ x ∈ factorCenter H L, factorCenter H L ≤ H ⊔ Subgroup.zpowers x

/-! ## Configurations (FT Def. 18.1) and the class `𝒞(p)` (FT Def. 18.2) -/

/-- **FT, Def. 18.1**: the data (C) of a configuration `(𝔎,𝔓,𝔄;𝔙,𝔐,𝔚)` — the semicolon entries
`𝔙`, `𝔐`, `𝔚` are determined by `(𝔎,𝔓,𝔄)` (see `Config.V`, `Config.M`, `Config.ZW`). -/
structure Config (p : ℕ) (K P A : Subgroup G) : Prop where
  /-- `𝔎` is a proper subgroup of `𝔊`. -/
  lt_top : K < ⊤
  /-- `𝔓` is an `S_p`-subgroup of `𝔎`. -/
  sylow : Work.LocalPrelim.IsSylowIn p P K
  /-- `𝔄` is a `p`-subgroup of `𝔊`. -/
  isPGroup : IsPGroup p A

namespace Config

variable {p : ℕ} {K P A : Subgroup G}

/-- `𝔙 = V(ccl_𝔊(𝔄);𝔓)`, the weak closure of the conjugacy class of `𝔄` in `𝔓`. -/
def V (c : Config p K P A) : Subgroup G := Work.Transitivity.Vof A P

/-- `𝔙` viewed inside `↥𝔎`. -/
def Vk (c : Config p K P A) : Subgroup ↥K := c.V.subgroupOf K

/-- `O_{p'}(𝔎)`, viewed inside `↥𝔎`. -/
abbrev Op' (c : Config p K P A) : Subgroup ↥K := Work.Fitting.pCoreSeries p ↥K 1

/-- `O_{p',p}(𝔎)`, viewed inside `↥𝔎`.  (`𝔚 = O_{p',p}(𝔎)/O_{p'}(𝔎)` is the factor
`c.Op'p / c.Op'`.) -/
abbrev Op'p (c : Config p K P A) : Subgroup ↥K := Work.Fitting.pCoreSeries p ↥K 2

/-- `O_{p',p,p'}(𝔎)`, viewed inside `↥𝔎`. -/
abbrev Op'pp' (c : Config p K P A) : Subgroup ↥K := Work.Fitting.pCoreSeries p ↥K 3

/-- `𝔐 = [O_{p',p,p'}(𝔎), 𝔙]`. -/
def M (c : Config p K P A) : Subgroup ↥K := ⁅c.Op'pp', c.Vk⁆

/-- The preimage in `↥𝔎` of `Z(𝔚)`, `𝔚 = O_{p',p}(𝔎)/O_{p'}(𝔎)`. -/
def ZW (c : Config p K P A) : Subgroup ↥K := factorCenter c.Op' c.Op'p

/-- The preimage in `↥𝔎` of `Z₂(𝔚)`, `𝔚 = O_{p',p}(𝔎)/O_{p'}(𝔎)`. -/
def Z2W (c : Config p K P A) : Subgroup ↥K := factorSecondCenter c.Op' c.Op'p

/-- `Z(𝔚)` is cyclic. -/
def IsZcyclic (c : Config p K P A) : Prop := IsFactorCyclic c.Op' c.Op'p

/-- `𝔐` centralizes `Z(𝔚)`, i.e. `[𝔐, Z(𝔚)] = 1` in `𝔚`. -/
def centralizes_Z (c : Config p K P A) : Prop := ⁅c.M, c.ZW⁆ ≤ c.Op'

/-- `𝔐` centralizes `Z₂(𝔚)/Z(𝔚)`. -/
def centralizes_Z2 (c : Config p K P A) : Prop := ⁅c.M, c.Z2W⁆ ≤ c.ZW

/-- The two conditions (a), (b) of FT Def. 18.2 for this configuration. -/
def IsGood (c : Config p K P A) : Prop := c.centralizes_Z ∧ (c.IsZcyclic → c.centralizes_Z2)

end Config

/-- **FT, Def. 18.2**: `𝔄 ∈ 𝒞(p)`.  `𝔄` is a `p`-subgroup of `𝔊`, and for every configuration
`(𝔎,𝔓,𝔄;𝔙,𝔐,𝔚)`, `𝔐` centralizes `Z(𝔚)`, and if `Z(𝔚)` is cyclic then `𝔐` centralizes
`Z₂(𝔚)/Z(𝔚)`. -/
def calC (p : ℕ) (G : Type*) [Group G] [Finite G] : Set (Subgroup G) :=
  {A | IsPGroup p A ∧ ∀ (K P : Subgroup G) (c : Config p K P A), c.IsGood}

/-- **FT, Def. 18.3**: `𝒰(p) = ⋃_{𝔓 ∈ Syl_p(𝔊)} 𝒰(𝔓)` (the set `𝒰(𝔓)` is FT §16's,
`Work.Transitivity.IsUP`). -/
def calU (p : ℕ) (G : Type*) [Group G] [Finite G] : Set (Subgroup G) :=
  Work.Transitivity.UPUnion p G

/-- **FT, Def. 18.3**: `𝒮𝒞𝒩_m(p) = ⋃_{𝔓 ∈ Syl_p(𝔊)} 𝒮𝒞𝒩_m(𝔓)`. -/
def SCNp (m p : ℕ) (G : Type*) [Group G] [Finite G] : Set (Subgroup G) :=
  Work.Transitivity.SCNpUnion m p G

/-- `𝒮𝒞𝒩₃(𝔓)` for a fixed subgroup `𝔓` (FT §2). -/
def SCN3of (P : Subgroup G) : Set (Subgroup G) := {A | Work.LocalPrelim.IsSCN_m 3 P A}

/-! ## The relation `p ~ q` (FT §19, p. 857) -/

/-- **FT §19**: `p ~ q` — `𝔊` contains elementary subgroups `𝔈`, `𝔉` of orders `p³`, `q³` with
`⟨𝔈,𝔉⟩ ⊂ 𝔊` (`⟨𝔈,𝔉⟩` is `E ⊔ F`). -/
def Sim (p q : ℕ) (G : Type*) [Group G] [Finite G] : Prop :=
  ∃ E F : Subgroup G, Work.PGroup.IsElementaryAbelian p E ∧ Nat.card E = p ^ 3 ∧
    Work.PGroup.IsElementaryAbelian q F ∧ Nat.card F = q ^ 3 ∧ E ⊔ F ≠ ⊤

/-! ## `E_σ`, `E_σ^*` and `π(𝔊)` -/

/-- The set of primes dividing `|G|`: FT's `π(𝔊)`. -/
def piG (G : Type*) [Group G] [Finite G] : Set ℕ := {p | p.Prime ∧ p ∣ Nat.card G}

/-- FT's `π₁,…,π₄` are *subsets of* `π(𝔊)` ("we partition `π(𝔊)` into four subsets"), so their
elements are primes.  The library's `Work.Transitivity.pi3 G` is a set of natural numbers defined
by elementary-subgroup conditions alone (`HasElemAbelian p 3 G` does not by itself force `p` to be a
prime, since `PGroup.IsElementaryAbelian p E` only says that every element of `E` has order
dividing `p`); this predicate is the faithful reading of "`p ∈ π₃ ∪ π₄`" from §19 onwards. -/
def InPi0 (p : ℕ) (G : Type*) [Group G] [Finite G] : Prop :=
  p.Prime ∧ p ∈ Work.Transitivity.pi0 G

/-- FT's "`p ∈ π₃`", including primality (see `InPi0`). -/
def InPi3 (p : ℕ) (G : Type*) [Group G] [Finite G] : Prop :=
  p.Prime ∧ p ∈ Work.Transitivity.pi3 G

/-- FT's "`p ∈ π₄`", including primality (see `InPi0`). -/
def InPi4 (p : ℕ) (G : Type*) [Group G] [Finite G] : Prop :=
  p.Prime ∧ p ∈ Work.Transitivity.pi4 G

/-- `{p, q}` as a set of primes. -/
def pqSet (p q : ℕ) : Set ℕ := {r | r = p ∨ r = q}

/-- P. Hall's `E_σ`: `𝔊` contains an `S_σ`-subgroup (FT Chapter I, p. 779). -/
def HasHall (σ : Set ℕ) (G : Type*) [Group G] [Finite G] : Prop := ∃ H : Subgroup G, Work.Hall.IsHall (fun r => r ∈ σ) H

/-- P. Hall's `E_σ^*`: `𝔊` contains a nilpotent `S_σ`-subgroup. -/
def HasNilpotentHall (σ : Set ℕ) (G : Type*) [Group G] [Finite G] : Prop :=
  ∃ H : Subgroup G, Work.Hall.IsHall (fun r => r ∈ σ) H ∧ Group.IsNilpotent ↥H

/-- `E_{p,q}`: `𝔊` contains an `S_{p,q}`-subgroup. -/
def E_pq (p q : ℕ) (G : Type*) [Group G] [Finite G] : Prop := Work.LocalPrelim.Epi (fun r => r = p ∨ r = q) G

/-- `E_{p,q}^*`: `𝔊` contains a nilpotent `S_{p,q}`-subgroup (FT's `E_{p,q}^n` of §19, which is
`E_σ^*` of Chapter I p. 779 for `σ = {p,q}`). -/
def Estar_pq (p q : ℕ) (G : Type*) [Group G] [Finite G] : Prop := Work.LocalPrelim.EstarPi (fun r => r = p ∨ r = q) G

/-! ## Hypotheses 19.1, 19.2 and 20.1 -/

/-- `P` centralizes every element of `𝓜(P; q)` (Hypothesis 19.1 (ii), Hypothesis 19.2 (iii)). -/
def CentralizesMSetQ (p q : ℕ) (P : Subgroup G) : Prop :=
  ∀ Q : Subgroup G, Work.Transitivity.MSetQ P q Q → Q ≤ Subgroup.centralizer (P : Set G)

/-- **FT, Hypothesis 19.1.**  (i) `p ∈ π₃ ∪ π₄`, `q ∈ π(𝔊)` and `p ≠ q`; (ii) an `S_p`-subgroup
`𝔓` of `𝔊` centralizes every element of `𝓜(𝔓;q)`. -/
def Hyp19_1 (p q : ℕ) (G : Type*) [Group G] [Finite G] : Prop :=
  InPi0 p G ∧ q ∈ piG G ∧ p ≠ q ∧
    ∀ P : Sylow p G, CentralizesMSetQ p q (P : Subgroup G)

/-- **FT, Hypothesis 19.2.**  (i) `p, q ∈ π₃ ∪ π₄` and `p ≠ q`; (ii) `p ~ q`; (iii) an
`S_p`-subgroup `𝔓` centralizes every element of `𝓜(𝔓;q)` and an `S_q`-subgroup `𝔔` centralizes
every element of `𝓜(𝔔;p)`. -/
def Hyp19_2 (p q : ℕ) (G : Type*) [Group G] [Finite G] : Prop :=
  InPi0 p G ∧ InPi0 q G ∧ p ≠ q ∧ Sim p q G ∧
    (∀ P : Sylow p G, CentralizesMSetQ p q (P : Subgroup G)) ∧
    (∀ Q : Sylow q G, CentralizesMSetQ q p (Q : Subgroup G))

/-- **FT, Hypothesis 20.1.**  `p, q ∈ π₃`, `p ≠ q`, `p ~ q`. -/
def Hyp20_1 (p q : ℕ) (G : Type*) [Group G] [Finite G] : Prop :=
  InPi3 p G ∧ InPi3 q G ∧ p ≠ q ∧ Sim p q G

/-! ## The families `𝓚(𝔄,q)`, `𝓛(p)` and `𝓕(p)` of FT pp. 859–861 -/

/-- Every characteristic abelian subgroup of `X` is cyclic (condition (K3) of FT p. 859 and the
hypothesis of FT 3.5/8.4 (i) computing the structure of `X`). -/
def AllCharAbelianCyclic (X : Subgroup G) : Prop :=
  ∀ C : Subgroup G, C ≤ X → (C.subgroupOf X).Characteristic → IsMulCommutative ↥C → IsCyclic ↥C

/-- **FT p. 859**: the collection `𝓚(𝔄) = 𝓚(𝔄,q)` of `p,q`-subgroups `𝔎` of `𝔊` with
(K1) `𝔓 ⊆ 𝔎`, (K2) `V(𝔄) ⊆ O_{q,p}(𝔎)`, (K3) every characteristic abelian subgroup of
`𝔓 ∩ O_{q,p}(𝔎)` is cyclic.

FT's `O_{q,p}(𝔎)` is `O_{p',p}(𝔎)` for a `{p,q}`-group `𝔎` (see `OpqPIn`), and is written
`OpPrimePIn p K` here. -/
def calK (p q : ℕ) (P A : Subgroup G) : Set (Subgroup G) :=
  {K | P ≤ K ∧ Work.LocalPrelim.IsPiGroup (fun r => r = p ∨ r = q) K ∧
    Work.Transitivity.Vof A P ≤ OpPrimePIn p K ∧ AllCharAbelianCyclic (P ⊓ OpPrimePIn p K)}

/-- **FT p. 859**: the subfamily `𝓕(𝔄;𝔓)` attached to `𝔄 ∈ 𝒮𝒞𝒩₃(𝔓)`.
If `𝓚(𝔄) = ∅` it consists of the subgroups of `𝔄` of type `(p,p)`; if `𝓚(𝔄) ≠ ∅` it consists of
the subgroups of `𝔄` of type `(p,p)` together with the subgroups `𝔅` of `𝔓 ∩ O_{q,p}(𝔎)`
(`𝔎 ∈ 𝓚(𝔄)`) of type `(p,p)` containing `Ω₁(Z(𝔓 ∩ O_{q,p}(𝔎)))`.

The two clauses are recorded as a union so that the definition is total: when `𝓚(𝔄) = ∅` the second
clause is empty, and when `𝓚(𝔄) ≠ ∅` FT keep *both* clauses. -/
def calFA (p q : ℕ) (P A : Subgroup G) : Set (Subgroup G) :=
  {B | Work.LocalPrelim.IsTypePP p B ∧ B ≤ A} ∪
  {B | ∃ K ∈ calK p q P A, Work.LocalPrelim.IsTypePP p B ∧ B ≤ P ⊓ OpPrimePIn p K ∧
    Work.PGroup.omega p 1 (Work.PGroup.centerIn (P ⊓ OpPrimePIn p K)) ≤ B}

/-- **FT p. 859**: `𝓕(𝔓) = ⋃_{𝔄 ∈ 𝒮𝒞𝒩₃(𝔓)} 𝓕(𝔄;𝔓)`. -/
def calFP (p q : ℕ) (P : Subgroup G) : Set (Subgroup G) :=
  ⋃ A ∈ SCN3of P, calFA p q P A

/-- **FT p. 859**: `𝓕(p) = ⋃_{𝔓 ∈ Syl_p(𝔊)} 𝓕(𝔓)` (called `𝓕(p)` although it also depends on `q`). -/
def calF (p q : ℕ) (G : Type*) [Group G] [Finite G] : Set (Subgroup G) := ⋃ P : Sylow p G, calFP p q (P : Subgroup G)

/-- **FT p. 861**: `𝓛(𝔓)` is the set of subgroups of index `p` in `𝔓 ∩ O_{q,p}(𝔎)` with
`𝔎 ∈ 𝓚(𝔄)`, `𝔄 ∈ 𝒮𝒞𝒩₃(𝔓)`. -/
def calLP (p q : ℕ) (P : Subgroup G) : Set (Subgroup G) :=
  {L | ∃ A ∈ SCN3of P, ∃ K ∈ calK p q P A,
    L ≤ P ⊓ OpPrimePIn p K ∧ L.relIndex (P ⊓ OpPrimePIn p K) = p}

/-- **FT p. 861**: `𝓛(p) = ⋃_{𝔓 ∈ Syl_p(𝔊)} 𝓛(𝔓)`. -/
def calL (p q : ℕ) (G : Type*) [Group G] [Finite G] : Set (Subgroup G) :=
  {L | ∃ P : Sylow p G, L ∈ calLP p q P}

/-! ## The four main statements of §18–§20 (as `Prop`s) -/

/-- **FT, Lemma 18.1.**  If `p ≥ 5` then `𝒰(p) ∪ 𝒮𝒞𝒩₃(p) ⊆ 𝒞(p)`. -/
def FT18_1 (G : Type*) [Group G] [Finite G] : Prop :=
  ∀ p : ℕ, 5 ≤ p → calU p G ∪ SCNp 3 p G ⊆ calC p G

/-- **FT, Theorem 19.1.**  Under Hypothesis 19.2, `𝔊` satisfies `E_{p,q}^n = E_{p,q}^*`. -/
def FT19_1 (G : Type*) [Group G] [Finite G] : Prop :=
  ∀ (hG : Work.Skeleton.MinSimpleOdd G) (p q : ℕ), Hyp19_2 p q G → Estar_pq p q G

/-- **FT, Corollary 19.1.**  If `p,q ∈ π₃ ∪ π₄`, `p ≠ q` and `p ~ q`, then `p ∈ π₃` or `q ∈ π₃`. -/
def FT19_Cor1 (G : Type*) [Group G] [Finite G] : Prop :=
  ∀ p q : ℕ, InPi0 p G → InPi0 q G → p ≠ q → Sim p q G →
    p ∈ Work.Transitivity.pi3 G ∨ q ∈ Work.Transitivity.pi3 G

/-- **FT, Theorem 20.1.**  Under Hypothesis 20.1, `𝔊` satisfies `E_{p,q}`. -/
def FT20_1 (G : Type*) [Group G] [Finite G] : Prop :=
  ∀ (hG : Work.Skeleton.MinSimpleOdd G) (p q : ℕ), Hyp20_1 p q G → E_pq p q G

end Work.ETheorems
