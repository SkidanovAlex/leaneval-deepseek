/-
# Area P2-07 `Work.Transitivity` — Feit–Thompson, *Solvability of groups of odd order*,
Pacific J. Math. **13** (1963), Chapter IV §15–§17.

This module fixes the vocabulary of FT §15–§17.  The statements proved in this area are in the
sibling modules `Basic`, `FT16`, `FT17`, `Hyp17`; the source text is the lead's transcription
`Submission/Work/ft1963/tex/ch4a.md` (printed pages 845–855).

## Conventions (project-wide, see `NOTES_LEAD_ft_phase2.md` §1)

* Subgroups are subgroups of an *ambient* group `G`; `A ⊴ P` is `(A.subgroupOf P).Normal`;
  `A^#` is `A \ {1}`; conjugation of subgroups is `MulAut.conj g • A` (`Work.PGroup.conjBy`).
* `𝔊` of the paper is the ambient `G`; `𝔓` is a `Sylow p G`, `𝔄` an element of
  `𝒮𝒞𝒩(𝔓)` (`Work.LocalPrelim.IsSCN`), `𝓜(𝔄)` is `Work.LocalPrelim.MSet`.

## Main definitions

* `HasElemAbelian p k G` — `𝔊` contains an elementary subgroup of order `p ^ k` (FT §15).
* `pi1 G`, `pi2 G`, `pi3 G`, `pi4 G` — the partition of `π(𝔊)` of FT §15; `pi0 G = pi3 G ∪ pi4 G`
  (the set called `π₃ ∪ π₄` from §19 on).
* `IsMaxMSet A q Q` — `Q` is a maximal element of `𝓜(𝔄; q)` (FT §17).
* `IsUP p P A` / `UP p P` / `UPUnion p G` — FT §16's `𝒰(𝔓)` and Def. 18.3's `𝒰(p)`.
* `gammaComm n A B` — FT §16's iterated commutator `γ^n 𝔄𝔅^n`.
* `IsNormAbelianIn P A` — FT §16's `𝒩𝒜(𝔓)`: the normal abelian subgroups of `𝔓`.
* `Hyp17_1` — FT's Hypothesis 17.1 (with its notation `𝔙`, `𝔑`, `𝔑₁`).
-/
import Mathlib
import Submission.Work.Skeleton.Minimal
import Submission.Work.LocalPrelim.Defs
import Submission.Work.PGroup.Basic
import Submission.Work.Hall.Basic
import Submission.Work.Fitting.Defs
import Submission.Work.NPC.Defs

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

open scoped Classical Pointwise

noncomputable section

namespace Work.Transitivity

variable {G : Type*} [Group G]

/-! ### Elementary subgroups -/

/-- FT §15: "`𝔊` contains an elementary subgroup of order `p ^ k`".  An elementary subgroup of
order `p ^ 3` is a subgroup isomorphic to `(ℤ/p)³`; in our vocabulary an *elementary abelian*
`p`-subgroup of order `p ^ k` (`Work.PGroup.IsElementaryAbelian`). -/
def HasElemAbelian (p k : ℕ) (G : Type*) [Group G] : Prop :=
  ∃ E : Subgroup G, Work.PGroup.IsElementaryAbelian p E ∧ Nat.card E = p ^ k

/-- FT §16: `𝒩𝒜(𝔓)` is the set of normal abelian subgroups of `𝔓`. -/
def IsNormAbelianIn (P A : Subgroup G) : Prop :=
  A ≤ P ∧ (A.subgroupOf P).Normal ∧ IsMulCommutative A

/-! ### The partition of `π(𝔊)` (FT §15) -/

/-- FT §15, the first class `π₁`: a Sylow `p`-subgroup of `𝔊` is a non-identity cyclic group. -/
def pi1 (G : Type*) [Group G] : Set ℕ :=
  {p | ∀ P : Sylow p G, IsCyclic ↥(P : Subgroup G) ∧ (P : Subgroup G) ≠ ⊥}

/-- FT §15, the second class `π₂`: a Sylow `p`-subgroup of `𝔊` is non cyclic and `𝔊` contains no
elementary subgroup of order `p ^ 3`. -/
def pi2 (G : Type*) [Group G] : Set ℕ :=
  {p | (∀ P : Sylow p G, ¬ IsCyclic ↥(P : Subgroup G)) ∧ ¬ HasElemAbelian p 3 G}

/-- FT §15, the third class `π₃`: `𝔊` contains an elementary subgroup of order `p ^ 3` and
`𝓜(𝔓)` contains a non-identity subgroup. -/
def pi3 (G : Type*) [Group G] : Set ℕ :=
  {p | HasElemAbelian p 3 G ∧
    ∀ P : Sylow p G, ∃ B : Subgroup G, Work.LocalPrelim.MSet (P : Subgroup G) B ∧ B ≠ ⊥}

/-- FT §15, the fourth class `π₄`: `𝔊` contains an elementary subgroup of order `p ^ 3` and
`𝓜(𝔓)` contains only the identity subgroup. -/
def pi4 (G : Type*) [Group G] : Set ℕ :=
  {p | HasElemAbelian p 3 G ∧
    ∀ P : Sylow p G, ∀ B : Subgroup G, Work.LocalPrelim.MSet (P : Subgroup G) B → B = ⊥}

/-- FT §19: `π₃ ∪ π₄`, the set denoted `π₀` from §19 onwards. -/
def pi0 (G : Type*) [Group G] : Set ℕ := pi3 G ∪ pi4 G

/-! ### Maximal elements of `𝓜(𝔄; q)` -/

/-- FT §17: `Q` is a maximal element of `𝓜(𝔄; q)`, i.e. `Q ∈ 𝓜(𝔄)` (𝔄 normalizes `Q` and
`𝔄 ∩ Q = 1`), `Q` is a `q`-group, and no larger `q`-subgroup of `𝓜(𝔄)` contains it. -/
def IsMaxMSet (A : Subgroup G) (q : ℕ) (Q : Subgroup G) : Prop :=
  Work.LocalPrelim.MSet A Q ∧ IsPGroup q Q ∧
    ∀ Q' : Subgroup G, Work.LocalPrelim.MSet A Q' → IsPGroup q Q' → Q ≤ Q' → Q' = Q

/-- FT §17: the `q`-subgroups of `𝓜(𝔄)`. -/
def MSetQ (A : Subgroup G) (q : ℕ) (Q : Subgroup G) : Prop :=
  Work.LocalPrelim.MSet A Q ∧ IsPGroup q Q

/-! ### FT §16's `𝒰(𝔓)` -/

/-- FT §16: `A ∈ 𝒰(𝔓)`.  If `Z(𝔓)` is non cyclic, `𝒰(𝔓)` consists of the subgroups of `Z(𝔓)` of
type `(p,p)`; if `Z(𝔓)` is cyclic, it consists of the *normal abelian* subgroups of `𝔓` of
type `(p,p)`. -/
def IsUP (p : ℕ) (P A : Subgroup G) : Prop :=
  Work.LocalPrelim.IsTypePP p A ∧
    ((¬ IsCyclic ↥(Work.PGroup.centerIn P) ∧ A ≤ Work.PGroup.centerIn P) ∨
     (IsCyclic ↥(Work.PGroup.centerIn P) ∧ A ≤ P ∧ (A.subgroupOf P).Normal))

/-- FT §16: `𝒰(𝔓)` as a set of subgroups. -/
def UP (p : ℕ) (P : Subgroup G) : Set (Subgroup G) := {A | IsUP p P A}

/-- FT, Def. 18.3: `𝒰(p) = ⋃_{𝔓 ∈ Syl_p(𝔊)} 𝒰(𝔓)`. -/
def UPUnion (p : ℕ) (G : Type*) [Group G] : Set (Subgroup G) :=
  {A | ∃ P : Sylow p G, IsUP p (P : Subgroup G) A}

/-- FT, Def. 18.3: `𝒮𝒞𝒩_m(p) = ⋃_{𝔓 ∈ Syl_p(𝔊)} 𝒮𝒞𝒩_m(𝔓)`. -/
def SCNpUnion (m p : ℕ) (G : Type*) [Group G] [Finite G] : Set (Subgroup G) :=
  {A | ∃ P : Sylow p G, Work.LocalPrelim.IsSCN_m m (P : Subgroup G) A}

/-! ### FT §16's iterated commutators -/

/-- FT §16: `γ 𝔄𝔅 = [𝔄,𝔅]` and `γ^{n+1} 𝔄𝔅^{n+1} = [γ^n 𝔄𝔅^n, 𝔅]`, i.e.
`gammaComm n A B = [A, B, B, …, B]` with `n - 1` copies of `B` (so `γ¹𝔄𝔅¹ = [𝔄,𝔅]`,
`γ²𝔄𝔅² = [𝔄,𝔅,𝔅]`, `γ³𝔄𝔅³ = [𝔄,𝔅,𝔅,𝔅]`). -/
def gammaComm : ℕ → Subgroup G → Subgroup G → Subgroup G
  | 0, A, _ => A
  | n + 1, A, B => ⁅gammaComm n A B, B⁆

@[inherit_doc] scoped notation "γ[" n ", " A ", " B "]" => gammaComm n A B

/-! ### Hypothesis 17.1 -/

/-- FT §17, Hypothesis 17.1.  `p ∈ π₃`, `𝔓` is a Sylow `p`-subgroup, `𝔄 ∈ 𝒮𝒞𝒩₃(𝔓)`, `q ≠ p` is a
prime, `𝓜(𝔄; q)` is non trivial and `𝔔` is a maximal element of `𝓜(𝔄; q)` normalized by `𝔓`.

The notation of the remark following Hypothesis 17.1 is recorded as definitions below
(`Vof`, `Nof`, `N1of`). -/
structure Hyp17_1 (G : Type*) [Group G] [Finite G] (p : ℕ) (P : Sylow p G) (A : Subgroup G)
    (q : ℕ) (Q : Subgroup G) : Prop where
  /-- `p` is a prime (FT's `p ∈ π(𝔊)`). -/
  hpPrime : p.Prime
  /-- `p ∈ π₃`. -/
  hp : p ∈ pi3 G
  /-- `𝔄 ∈ 𝒮𝒞𝒩₃(𝔓)`. -/
  hA : Work.LocalPrelim.IsSCN_m 3 (P : Subgroup G) A
  /-- `q` is a prime different from `p`. -/
  hq : q.Prime
  hqp : q ≠ p
  /-- `𝔔` is a maximal element of `𝓜(𝔄; q)`. -/
  hQ : IsMaxMSet A q Q
  /-- `𝓜(𝔄; q)` is non trivial. -/
  hQne : Q ≠ ⊥
  /-- `𝔓` normalizes `𝔔`. -/
  hnorm : (P : Subgroup G) ≤ Subgroup.normalizer (Q : Set G)

/-- FT §17: `𝔙 = V(ccl_𝔊(𝔄); 𝔓)`, the weak closure of the conjugacy class of `𝔄` in `𝔓`. -/
def Vof (A P : Subgroup G) : Subgroup G := Work.LocalPrelim.weakClosure A P

/-- FT §17: `𝔑 = N(𝔔)`. -/
def Nof (Q : Subgroup G) : Subgroup G := Subgroup.normalizer (Q : Set G)

/-- FT §17, Lemma 17.1 (conclusion): `N(𝔙)`, the normalizer of `𝔙 = V(ccl_𝔊(𝔄); 𝔓)`. -/
def NofV (A P : Subgroup G) : Subgroup G :=
  Subgroup.normalizer ((Vof A P : Subgroup G) : Set G)

/-- FT §17, the remark after Hypothesis 17.1: `𝔑₁ = N(Z(𝔙))`.  (Note that `𝔑₁` is *not* `N(𝔙)`:
`N(𝔙)` is `NofV`.  FT use `𝔑₁` throughout Lemmas 17.2–17.6 and `N(𝔙)` in Lemma 17.1.) -/
def N1of (A P : Subgroup G) : Subgroup G :=
  Subgroup.normalizer (((Work.PGroup.centerIn (Vof A P) : Subgroup G)) : Set G)

/-- The four classes `π₁,…,π₄` of FT §15 indexed by `Fin 4` (`0 ↦ π₁`, …, `3 ↦ π₄`). -/
def piSet (G : Type*) [Group G] : Fin 4 → Set ℕ
  | 0 => pi1 G
  | 1 => pi2 G
  | 2 => pi3 G
  | 3 => pi4 G

/-- `P` is a Sylow `p`-subgroup of the subgroup `X` (of the ambient group), in FT's terminology an
`S_p`-subgroup of `𝔛`.  Stated in the ambient group so that it can be used for normalizers of
subsets, e.g. `N(𝔄)`. -/
def IsSylowIn (p : ℕ) (P X : Subgroup G) : Prop :=
  IsPGroup p P ∧ P ≤ X ∧ ¬ p ∣ P.relIndex X

/-- FT §17, Theorem 17.1 (Thompson's transitivity theorem), as a statement.  For a Sylow
`p`-subgroup `𝔓` of `𝔊` and `𝔄 ∈ 𝒮𝒞𝒩(𝔓)`, and any two maximal elements `𝔔`, `𝔔₁` of `𝓜(𝔄;q)`
(`q ≠ p` a prime):

(i) if `𝔔` is not conjugate to `𝔔₁` by any element of `C(𝔄)`, then for every `A ∈ 𝔄^#` either
`C_𝔔(A) = 1` or `C_{𝔔₁}(A) = 1`;
(ii) if `𝔄 ∈ 𝒮𝒞𝒩₃(𝔓)` then `𝔔` and `𝔔₁` are conjugate by an element of `C(𝔄)`. -/
def FT17_1Statement (p : ℕ) (G : Type*) [Group G] [Finite G] : Prop :=
  ∀ (P : Sylow p G) (A : Subgroup G), Work.LocalPrelim.IsSCN (P : Subgroup G) A →
  ∀ (q : ℕ), q.Prime → q ≠ p →
  ∀ (Q Q₁ : Subgroup G), IsMaxMSet A q Q → IsMaxMSet A q Q₁ →
    ((∀ c ∈ Subgroup.centralizer (A : Set G), Q₁ ≠ MulAut.conj c • Q) →
      ∀ a ∈ A, a ≠ 1 →
        Subgroup.centralizer ({a} : Set G) ⊓ Q = ⊥ ∨
        Subgroup.centralizer ({a} : Set G) ⊓ Q₁ = ⊥) ∧
    (3 ≤ Group.rank A → ∃ c ∈ Subgroup.centralizer (A : Set G), Q₁ = MulAut.conj c • Q)

end Work.Transitivity
