/-
# Area P2-01 `Work.LocalPrelim` : the local preliminaries of Feit–Thompson Chapter II

This is the base module of area **P2-01** of the Feit–Thompson (odd order theorem) drive.
It fixes the vocabulary of Feit & Thompson, *Solvability of groups of odd order*, Pacific J. Math.
**13** (1963), 775–1029 (cited below as FT), Chapter I §2 and Chapter II, in which the whole local
analysis (FT §14–§26) is phrased.

## Conventions

* Subgroups are always subgroups of an *ambient* group `G`.
* "`A` is normal in `P`" is `(A.subgroupOf P).Normal` (`Work.PGroup` convention).
* `𝔄^#` is `A \ {1}`; `A^g` is `Work.PGroup.conjBy g A` (definitionally `MulAut.conj g • A`).
* A `π`-set is a predicate `π : ℕ → Prop`; `n` is a `π`-number if every prime divisor of `n` lies
  in `π`.  `IsPiGroup π H` means `|H|` is a `π`-number (FT: "`H` is a `π`-group").
* `IsPPrimeGroup p H` means `H` is a `p'`-group.

## Main definitions

* `IsSCN P A` — FT §2: `A` is a self-centralizing normal abelian subgroup of `P`
  (`A ∈ SCN(P)`); `IsSCN_m m P A` — `A ∈ SCN_m(P)`; `SCNSet`.
* `MSet A B` — FT §2: `B ∈ 𝔐(A)`, i.e. `A` normalizes `B` and `A ∩ B = 1`; `MSetPi π A B`.
* `IsMetacyclic P`, `IsMetacyclicGroup X` — metacyclic groups (FT 3.8).
* `weakClosure A B` — FT §2: `V(ccl_G(A); B)`; `IsWeaklyClosed A B`.
* `StabilizesChain A C` — FT §2 / §8.1: `A` stabilizes the chain `C`.
* `autStabilizesChain`, `stabilityGroupAut` — the stability group of a chain (FT 8.1).
* `Covers L K M`, `Dominates L K` — FT §2 ("covers"/"dominates").
* `Epi`, `Cpi`, `Dpi`, `EstarPi` — P. Hall's propositions `E_π`, `C_π`, `D_π`, `E_π*` (FT §2).
* `IsFixedPointFree σ` — a fixed point free automorphism.
* `IsTypePP p A` — `A` is elementary abelian of order `p ^ 2` ("of type `(p,p)`").

Reference for every statement: FT 1963, as transcribed in `Submission/Work/ft1963/tex/ch1.md`
(Chapter I, pp. 775–788) and `ch2.md` (Chapter II, pp. 789–802).
-/
import Mathlib
import Submission.Work.PGroup.Basic
import Submission.Work.Hall.Basic
import Submission.Work.Fitting.Defs
import Submission.Work.HallHigman.Basic
import Submission.Work.Coprime.Defs

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

open scoped Classical Pointwise

noncomputable section

namespace Work.LocalPrelim

variable {G : Type*} [Group G]

/-! ### `π`-groups -/

/-- `n` is a `π`-number: every prime divisor of `n` lies in `π` (FT §2). -/
abbrev IsPiNat (π : ℕ → Prop) (n : ℕ) : Prop := Work.Hall.IsPiNat π n

/-- `H` is a `π`-group: `|H|` is a `π`-number (FT §2). -/
abbrev IsPiGroup (π : ℕ → Prop) (H : Subgroup G) : Prop := Work.Hall.IsPiSubgroup π H

/-- `H` is a `p'`-group (FT §2). -/
abbrev IsPPrimeGroup (p : ℕ) (H : Subgroup G) : Prop := Work.Hall.IsPiSubgroup (fun q => q ≠ p) H

/-- `H` is a Hall `π`-subgroup (an `S_π`-subgroup in FT's terminology). -/
abbrev IsHallPi (π : ℕ → Prop) (H : Subgroup G) : Prop := Work.Hall.IsHall π H

/-- `A` is elementary abelian of order `p ^ 2`, i.e. "of type `(p,p)`" (FT §2). -/
def IsTypePP (p : ℕ) (A : Subgroup G) : Prop :=
  Work.PGroup.IsElementaryAbelian p A ∧ Nat.card A = p ^ 2

/-! ### `SCN` -/

/-- FT §2: `A ∈ SCN(P)`, i.e. `A` is a *self centralizing normal* subgroup of `P`: `A ≤ P`,
`A` is normal in `P`, `A` is abelian, and `C_G(A) ∩ P ≤ A` (equivalently `C_P(A) = A`).
Since `A ≤ P` and `A` is abelian, `C_P(A) = A` is exactly `C_G(A) ∩ P = A`. -/
def IsSCN (P A : Subgroup G) : Prop :=
  A ≤ P ∧ (A.subgroupOf P).Normal ∧ IsMulCommutative A ∧
    Subgroup.centralizer (A : Set G) ⊓ P ≤ A

/-- FT §2: `SCN(P)`, the set of self centralizing normal subgroups of `P`. -/
def SCNSet (P : Subgroup G) : Set (Subgroup G) := {A | IsSCN P A}

/-- FT §2: `A ∈ SCN_m(P)`, i.e. `A ∈ SCN(P)` and `m(A) ≥ m`. -/
def IsSCN_m [Finite G] (m : ℕ) (P A : Subgroup G) : Prop :=
  IsSCN P A ∧ m ≤ Group.rank A

/-! ### FT's `𝔐(𝔄)` -/

/-- FT §2: `B ∈ 𝔐(A)`, the set of subgroups of the ambient group which `A` normalizes and which
intersect `A` in the identity only. -/
def MSet (A B : Subgroup G) : Prop :=
  A ≤ Subgroup.normalizer (B : Set G) ∧ A ⊓ B = ⊥

/-- FT §2: `𝔐(A; π)`, the `π`-subgroups in `𝔐(A)`. -/
def MSetPi (π : ℕ → Prop) (A B : Subgroup G) : Prop := MSet A B ∧ IsPiGroup π B

/-! ### Metacyclic groups -/

/-- A group is metacyclic if it has a cyclic normal subgroup `C` such that `X = C * ⟨x⟩`
(equivalently `X/C` is cyclic). -/
def IsMetacyclicGroup (X : Type*) [Group X] : Prop :=
  ∃ C : Subgroup X, C.Normal ∧ IsCyclic ↥C ∧ ∃ x : X, C ⊔ Subgroup.zpowers x = ⊤

/-- A subgroup `P` of the ambient group is metacyclic (FT 3.8). -/
def IsMetacyclic (P : Subgroup G) : Prop :=
  ∃ C : Subgroup G, C ≤ P ∧ (C.subgroupOf P).Normal ∧ IsCyclic ↥C ∧
    ∃ x : G, x ∈ P ∧ C ⊔ Subgroup.zpowers x = P

/-! ### Weak closure -/

/-- FT §2: `V(ccl_G(A); B)`, the weak closure of the conjugacy class of `A` in `B` with respect
to the ambient group: the subgroup generated by all conjugates of `A` that lie in `B`. -/
def weakClosure (A B : Subgroup G) : Subgroup G :=
  Subgroup.closure {x : G | ∃ g : G, MulAut.conj g • A ≤ B ∧ x ∈ MulAut.conj g • A}

/-- FT §2: `A` is weakly closed in `B` (with respect to the ambient group) if it equals its own
weak closure in `B`. -/
def IsWeaklyClosed (A B : Subgroup G) : Prop := weakClosure A B = A

/-! ### Stability groups of chains -/

/-- The stability group of a chain, element condition, in its `Aut` form.  If `C : Fin (n+1) →
Subgroup X` is a chain `X = C 0 ⊇ C 1 ⊇ ⋯ ⊇ C n`, then `autStabilizesChain α C` says that the
automorphism `α` fixes every member of the chain and every coset of the chain: for every `i < n`
and `x ∈ C i`, `α x * x⁻¹ ∈ C (i+1)` (i.e. `(C (i+1) * x)^α = C (i+1) * x`).

(Note that FT's condition `(𝔛_i X)^α = 𝔛_i X` for all `X ∈ 𝔛_{i-1}` with `X = 1` already gives
`𝔛_i^α = 𝔛_i`, so the first clause is implied by the second one when the chain is finite and
decreasing; it is recorded here because it is what makes the set a group without finiteness
hypotheses.) -/
def autStabilizesChain {X : Type*} [Group X] (α : MulAut X) {n : ℕ}
    (C : Fin (n + 1) → Subgroup X) : Prop :=
  (∀ i : Fin (n + 1), Subgroup.map α.toMonoidHom (C i) = C i) ∧
    ∀ i : Fin n, ∀ x : X, x ∈ C i.castSucc → α x * x⁻¹ ∈ C i.succ

section StabilityGroup

variable {X : Type*} [Group X]

theorem map_symm_eq_of_map_eq {D : Subgroup X} {α : MulAut X}
    (h : Subgroup.map α.toMonoidHom D = D) : Subgroup.map α.symm.toMonoidHom D = D := by
  have h1 : Subgroup.map α.symm.toMonoidHom (Subgroup.map α.toMonoidHom D) = D := by
    rw [Subgroup.map_map]
    have hcomp : α.symm.toMonoidHom.comp α.toMonoidHom = MonoidHom.id X := by
      ext x; simp
    rw [hcomp, Subgroup.map_id]
  rwa [h] at h1

theorem mem_map_iff_of_map_eq {D : Subgroup X} {α : MulAut X}
    (h : Subgroup.map α.toMonoidHom D = D) (x : X) : α x ∈ D ↔ x ∈ D := by
  constructor
  · intro hx
    have h2 : α.symm (α x) ∈ D := by
      have h3 : α.symm (α x) ∈ Subgroup.map α.symm.toMonoidHom D := ⟨α x, hx, rfl⟩
      rwa [map_symm_eq_of_map_eq h] at h3
    simpa using h2
  · intro hx
    have h2 : α x ∈ Subgroup.map α.toMonoidHom D := ⟨x, hx, rfl⟩
    rwa [h] at h2

theorem mul_toMonoidHom_eq (α β : MulAut X) :
    (α * β).toMonoidHom = α.toMonoidHom.comp β.toMonoidHom := by
  ext x; rfl

/-- FT §2 (after P. Hall [19]): the *stability group* of a chain `C : Fin (n+1) → Subgroup X`,
`X = C 0 ⊇ C 1 ⊇ ⋯ ⊇ C n`.  It is the group of all automorphisms `α` of `X` such that
`(C (i+1) * x)^α = C (i+1) * x` for all `x ∈ C i` and all `i < n`. -/
def stabilityGroupAut {n : ℕ} (C : Fin (n + 1) → Subgroup X) : Subgroup (MulAut X) where
  carrier := {α | autStabilizesChain α C}
  mul_mem' := by
    intro α β hα hβ
    refine ⟨?_, ?_⟩
    · intro i
      rw [mul_toMonoidHom_eq, ← Subgroup.map_map, hβ.1 i, hα.1 i]
    · intro i x hx
      have hβx : β x ∈ C i.castSucc := (mem_map_iff_of_map_eq (hβ.1 i.castSucc) x).2 hx
      have h3 : α (β x) * (β x)⁻¹ ∈ C i.succ := hα.2 i (β x) hβx
      have h4 : β x * x⁻¹ ∈ C i.succ := hβ.2 i x hx
      have hkey : (α * β) x * x⁻¹ = (α (β x) * (β x)⁻¹) * (β x * x⁻¹) := by
        simp only [MulAut.mul_apply]; group
      rw [hkey]
      exact (C i.succ).mul_mem h3 h4
  one_mem' := by
    refine ⟨?_, ?_⟩
    · intro i
      have h : (1 : MulAut X).toMonoidHom = MonoidHom.id X := rfl
      rw [h, Subgroup.map_id]
    · intro i x hx; simp
  inv_mem' := by
    intro α hα
    refine ⟨fun i => map_symm_eq_of_map_eq (hα.1 i), ?_⟩
    intro i x hx
    have hmem : α.symm x ∈ C i.castSucc :=
      (mem_map_iff_of_map_eq (map_symm_eq_of_map_eq (hα.1 i.castSucc)) x).2 hx
    have h1 : α (α.symm x) * (α.symm x)⁻¹ ∈ C i.succ := hα.2 i (α.symm x) hmem
    have h2 : x * (α.symm x)⁻¹ ∈ C i.succ := by simpa using h1
    have h3 : α.symm x * x⁻¹ ∈ C i.succ := by
      have h4 := (C i.succ).inv_mem h2
      simpa using h4
    simpa using h3

end StabilityGroup

/-- FT §2: a subgroup `A` of the ambient group stabilizes the chain `C` (in terms of conjugation
in the ambient group).  `A` must normalize every member of the chain, and every coset
`C (i+1) * x`, `x ∈ C i`, must be `A`-invariant. -/
def StabilizesChain (A : Subgroup G) {n : ℕ} (C : Fin (n + 1) → Subgroup G) : Prop :=
  (∀ i : Fin (n + 1), A ≤ Subgroup.normalizer (C i : Set G)) ∧
    ∀ a : G, a ∈ A → ∀ i : Fin n, ∀ x : G, x ∈ C i.castSucc →
      (a⁻¹ * x * a) * x⁻¹ ∈ C i.succ

/-! ### Covers and dominates -/

/-- FT §2: a subgroup `L` *covers* the section `K/M` if it contains at least one element of every
coset of `M` in `K`. -/
def Covers (L K M : Subgroup G) : Prop :=
  ∀ x ∈ K, ∃ y ∈ L, y ∈ K ∧ y * x⁻¹ ∈ M

/-- FT §2: `L` *dominates* `K` if `L` covers the section `N(K)/C(K)`. -/
def Dominates (L K : Subgroup G) : Prop :=
  Covers L (Subgroup.normalizer (K : Set G)) (Subgroup.centralizer (K : Set G))

/-! ### P. Hall's propositions `E_π`, `C_π`, `D_π`, `E_π*` -/

/-- FT §2, P. Hall's `E_π`: the group has an `S_π`-subgroup. -/
def Epi (π : ℕ → Prop) (X : Type*) [Group X] : Prop :=
  ∃ H : Subgroup X, Work.Hall.IsHall π H

/-- FT §2, P. Hall's `C_π`: `E_π` holds and any two `S_π`-subgroups are conjugate. -/
def Cpi (π : ℕ → Prop) (X : Type*) [Group X] : Prop :=
  Epi π X ∧ ∀ H K : Subgroup X, Work.Hall.IsHall π H → Work.Hall.IsHall π K →
    ∃ g : X, MulAut.conj g • K = H

/-- FT §2, P. Hall's `D_π`: `C_π` holds and every `π`-subgroup is contained in an
`S_π`-subgroup. -/
def Dpi (π : ℕ → Prop) (X : Type*) [Group X] : Prop :=
  Cpi π X ∧ ∀ H : Subgroup X, IsPiGroup π H → ∃ K : Subgroup X, Work.Hall.IsHall π K ∧ H ≤ K

/-- FT §2, P. Hall's `E_π*`: the group contains a nilpotent `S_π`-subgroup. -/
def EstarPi (π : ℕ → Prop) (X : Type*) [Group X] : Prop :=
  ∃ H : Subgroup X, Work.Hall.IsHall π H ∧ Group.IsNilpotent H

/-! ### Fixed point free automorphisms -/

/-- `σ` is a fixed point free automorphism of `X`. -/
def IsFixedPointFree {X : Type*} [Group X] (σ : MulAut X) : Prop :=
  ∀ x : X, σ x = x → x = 1


/-! ### `π`-cores of subgroups, as subgroups of the ambient group -/

/-- `O_p(H)` for a subgroup `H` of the ambient group, viewed as a subgroup of `G`. -/
def pCoreIn (p : ℕ) (H : Subgroup G) : Subgroup G := (Work.Fitting.pCore p ↥H).map H.subtype

/-- `O_{p'}(H)` for a subgroup `H` of the ambient group, viewed as a subgroup of `G`. -/
def pPrimeCoreIn (p : ℕ) (H : Subgroup G) : Subgroup G :=
  (Work.Fitting.pPrimeCore p ↥H).map H.subtype

/-- `O_{p',p}(H)` for a subgroup `H` of the ambient group, viewed as a subgroup of `G`. -/
def pPrimePCoreIn (p : ℕ) (H : Subgroup G) : Subgroup G :=
  (Work.Fitting.pPrimePCore p ↥H).map H.subtype

/-- `|H|` is not divisible by three distinct primes (FT §7, condition 4 defining `𝒮`). -/
def NotThreePrimes (H : Subgroup G) : Prop :=
  ¬ ∃ m n k : ℕ, m.Prime ∧ n.Prime ∧ k.Prime ∧ m ≠ n ∧ n ≠ k ∧ m ≠ k ∧
    m * n * k ∣ Nat.card H

/-- FT §7: the family `𝒮` attached to a `S_p`-subgroup `P` of `X`: the subgroups `H` of `X`
with `P ≤ H`, `p`-length at most two and `|H|` not divisible by three distinct primes. -/
def familyS (p : ℕ) (P : Subgroup G) : Set (Subgroup G) :=
  {H | P ≤ H ∧ Work.Fitting.pLength p ↥H ≤ 2 ∧ NotThreePrimes H}

/-- FT §8: `D` is *involved* in `X` if some section `𝔓/𝔑` of `X` is isomorphic to `D`. -/
def IsInvolved (D : Type*) [Group D] (X : Type*) [Group X] : Prop :=
  ∃ (P : Subgroup X) (N : Subgroup X) (hN : N.Normal) (hNP : N ≤ P),
    Nonempty (D ≃* (↥P ⧸ N.subgroupOf P))

/-- `S` centralizes the factor `K/H`, i.e. `[S,K] ≤ H` (FT §2: "`X` centralizes `𝔉`"). -/
def CentralizesFactor (S K H : Subgroup G) : Prop := ⁅S, K⁆ ≤ H

/-- The factor `K/H` is a `π`-factor: `[K : H]` is a `π`-number. -/
def IsPiFactor (π : ℕ → Prop) (H K : Subgroup G) : Prop :=
  H ≤ K ∧ IsPiNat π (H.subgroupOf K).index

/-- The factor `K/H` is a `p`-factor. -/
def IsPFactor (p : ℕ) (H K : Subgroup G) : Prop := IsPiFactor (fun q => q = p) H K

/-- FT §2: `O^p(X)`, the smallest normal subgroup `𝔇` of `X` such that `X/𝔇` is a `p`-group.
For a finite group this is the subgroup generated by the elements of order prime to `p`
(equivalently by the `p'`-elements): an element of `p'`-order maps to the identity in any
`p`-group quotient, and conversely the subgroup they generate is normal with `p`-group quotient.

Note: this is *not* the same as `Work.HallHigman.opSubgroup p X`, which is the subgroup generated
by the elements of `p`-power order (the `p'`-residual, FT's `O^{p'}`). -/
def opSubgroup (p : ℕ) (X : Type*) [Group X] : Subgroup X :=
  Subgroup.closure {x : X | ¬ p ∣ orderOf x}

/-- The pointwise product of two subsets of a group, spelled out so that statements do not depend
on the `Pointwise` scoped notation being open. -/
def SetMul (A B : Set G) : Set G := {x : G | ∃ a ∈ A, ∃ b ∈ B, a * b = x}

/-- `P` is a `S_p`-subgroup of the subgroup `H` of the ambient group. -/
def IsSylowIn (p : ℕ) (P H : Subgroup G) : Prop :=
  P ≤ H ∧ IsPGroup p P ∧ ¬ p ∣ (P.subgroupOf H).index

end Work.LocalPrelim

