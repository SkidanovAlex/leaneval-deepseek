/-
# Area P2-00 `Spine` of the Feit--Thompson (odd order theorem) drive

This is the **interface area**: it defines the vocabulary of Chapter IV--VI of

  W. Feit and J. G. Thompson, *Solvability of groups of odd order*,
  Pacific J. Math. **13** (1963), 775--1029,

as used in the paper, and states the four interface results (Theorems 14.1, 14.2,
27.1, 37.1) as `Prop`s.  Every other Phase-2 area imports this module.

Everything is transcribed from the page images / the lead's LaTeX transcription
(`Submission/Work/ft1963/tex/ch1.md`, `ch3a.md`, `ch4a.md`, `ch5a.md`, `ch6.md`);
the relevant passages are quoted in the doc-strings.  See `NOTES.md` for the
transcription log and for the design decisions (in particular the readings of
`C(A)` and of the "hat" sets).
-/
import Mathlib
import Submission.Work.Skeleton.Main
import Submission.Work.Hall.MainResults
import Submission.Work.Fitting.Main
import Submission.Work.PGroup.All
import Submission.Work.Clifford.All

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

@[expose] public section

noncomputable section

open Classical
open scoped Pointwise

namespace Work.FTSpine

universe u

variable {G : Type u} [Group G] [Finite G]

/-! ## Conjugation of subgroups

FT's conjugation notation is the pointwise `MulAut` action.  We record the two
facts about it that the definitions below need, and the two `Normal` instances
that make `N(P)/P·C(P)` usable as a quotient type. -/

/-- `x ∈ gHg⁻¹` in terms of the generator. -/
theorem mem_conj_smul_iff {H : Subgroup G} {k x : G} :
    (x ∈ MulAut.conj k • H) ↔ (MulAut.conj k)⁻¹ • x ∈ H := by
  simpa using Subgroup.mem_pointwise_smul_iff_inv_smul_mem (a := MulAut.conj k) (S := H) (x := x)

/-- An element of the normalizer fixes the subgroup under conjugation. -/
theorem conj_smul_eq_self_of_mem_normalizer {H : Subgroup G} {k : G}
    (hk : k ∈ Subgroup.normalizer (H : Set G)) : MulAut.conj k • H = H := by
  have hk' : k⁻¹ ∈ Subgroup.normalizer (H : Set G) := (Subgroup.normalizer _).inv_mem hk
  ext x
  rw [mem_conj_smul_iff, show (MulAut.conj k)⁻¹ = MulAut.conj k⁻¹ by simp, MulAut.smul_def,
    MulAut.conj_apply]
  exact (Subgroup.mem_normalizer_iff.mp hk' x).symm

/-- The normalizer of `P` normalizes `C(P)`. -/
theorem conj_smul_centralizer_eq_self {P : Subgroup G} {k : G}
    (hk : k ∈ Subgroup.normalizer (P : Set G)) :
    MulAut.conj k • Subgroup.centralizer (P : Set G) = Subgroup.centralizer (P : Set G) := by
  have hk' : k⁻¹ ∈ Subgroup.normalizer (P : Set G) := (Subgroup.normalizer _).inv_mem hk
  ext x
  rw [mem_conj_smul_iff, show (MulAut.conj k)⁻¹ = MulAut.conj k⁻¹ by simp, MulAut.smul_def,
    MulAut.conj_apply]
  constructor
  · intro hx
    simp only [Subgroup.mem_centralizer_iff] at hx ⊢
    intro q hq
    have hkq : k⁻¹ * q * (k⁻¹)⁻¹ ∈ P := (Subgroup.mem_normalizer_iff.mp hk' q).mp hq
    have key := hx _ hkq
    calc q * x = k * ((k⁻¹ * q * (k⁻¹)⁻¹) * (k⁻¹ * x * (k⁻¹)⁻¹)) * k⁻¹ := by group
      _ = k * ((k⁻¹ * x * (k⁻¹)⁻¹) * (k⁻¹ * q * (k⁻¹)⁻¹)) * k⁻¹ := by rw [key]
      _ = x * q := by group
  · intro hx
    simp only [Subgroup.mem_centralizer_iff] at hx ⊢
    intro q hq
    have hkq : k * q * k⁻¹ ∈ P := (Subgroup.mem_normalizer_iff.mp hk q).mp hq
    have key := hx _ hkq
    calc q * (k⁻¹ * x * (k⁻¹)⁻¹) = k⁻¹ * ((k * q * k⁻¹) * x) * k := by group
      _ = k⁻¹ * (x * (k * q * k⁻¹)) * k := by rw [key]
      _ = (k⁻¹ * x * (k⁻¹)⁻¹) * q := by group

/-- `C_G(U) ⊴ N_G(U)`: makes `N(U)/C(U)` a quotient type. -/
instance centralizerSubgroupOfNormalizerNormal (U : Subgroup G) :
    ((Subgroup.centralizer (U : Set G)).subgroupOf (Subgroup.normalizer (U : Set G))).Normal := by
  rw [Subgroup.normal_subgroupOf_iff_le_normalizer (Subgroup.centralizer_le_normalizer (U : Set G))]
  intro k hk
  simp only [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · intro hx
    have h := Subgroup.smul_mem_pointwise_smul x (MulAut.conj k) _ hx
    rw [conj_smul_centralizer_eq_self hk] at h
    have heq : (MulAut.conj k) • x = k * x * k⁻¹ := by simp [MulAut.smul_def, MulAut.conj_apply]
    rwa [heq] at h
  · intro hx
    have h := Subgroup.smul_mem_pointwise_smul (k * x * k⁻¹) (MulAut.conj k⁻¹)
        (Subgroup.centralizer (U : Set G)) hx
    rw [conj_smul_centralizer_eq_self ((Subgroup.normalizer _).inv_mem hk)] at h
    have heq : (MulAut.conj k⁻¹) • (k * x * k⁻¹) = x := by
      rw [MulAut.smul_def, MulAut.conj_apply]
      simp only [inv_inv]
      group
    rwa [heq] at h

/-- `P·C_G(P) ⊴ N_G(P)`: makes `N(P)/P·C(P)` a quotient type. -/
instance supCentralizerSubgroupOfNormalizerNormal (P : Subgroup G) :
    ((P ⊔ Subgroup.centralizer (P : Set G)).subgroupOf (Subgroup.normalizer (P : Set G))).Normal := by
  rw [Subgroup.normal_subgroupOf_iff_le_normalizer
      (sup_le Subgroup.le_normalizer (Subgroup.centralizer_le_normalizer (P : Set G)))]
  intro k hk
  simp only [Subgroup.mem_normalizer_iff]
  intro x
  have hsm : MulAut.conj k • (P ⊔ Subgroup.centralizer (P : Set G))
      = P ⊔ Subgroup.centralizer (P : Set G) := by
    rw [Subgroup.smul_sup, conj_smul_eq_self_of_mem_normalizer hk, conj_smul_centralizer_eq_self hk]
  have hsm' : MulAut.conj k⁻¹ • (P ⊔ Subgroup.centralizer (P : Set G))
      = P ⊔ Subgroup.centralizer (P : Set G) := by
    rw [Subgroup.smul_sup, conj_smul_eq_self_of_mem_normalizer ((Subgroup.normalizer _).inv_mem hk),
      conj_smul_centralizer_eq_self ((Subgroup.normalizer _).inv_mem hk)]
  constructor
  · intro hx
    have h := Subgroup.smul_mem_pointwise_smul x (MulAut.conj k) _ hx
    rw [hsm] at h
    have heq : (MulAut.conj k) • x = k * x * k⁻¹ := by simp [MulAut.smul_def, MulAut.conj_apply]
    rwa [heq] at h
  · intro hx
    have h := Subgroup.smul_mem_pointwise_smul (k * x * k⁻¹) (MulAut.conj k⁻¹) _ hx
    rw [hsm'] at h
    have heq : (MulAut.conj k⁻¹) • (k * x * k⁻¹) = x := by
      rw [MulAut.smul_def, MulAut.conj_apply]
      simp only [inv_inv]
      group
    rwa [heq] at h

/-! ## FT §2: `S`-subgroups, T.I. sets, the maximal normal nilpotent `S`-subgroup

FT, ch. I p. 777: an `S_π`-subgroup is a Hall π-subgroup; an "`S`-subgroup" is a
Hall subgroup.  p. 780: "A subset A of the group X is said to be a *trivial
intersection set in* X, or a *T.I. set in* X iff for every X in X, either
`X⁻¹AX ∩ A ⊆ {1}` or `X⁻¹AX = A`." -/

/-- FT's "`H` is an `S`-subgroup of `X`": `H` is a Hall subgroup of `X`, i.e.
`|H|` and `[X : H]` are coprime. -/
def IsHallIn (H X : Subgroup G) : Prop := H ≤ X ∧ (Nat.card H).Coprime (H.relIndex X)

theorem IsHallIn.le {H X : Subgroup G} (h : IsHallIn H X) : H ≤ X := h.1

theorem IsHallIn.coprime {H X : Subgroup G} (h : IsHallIn H X) :
    (Nat.card H).Coprime (H.relIndex X) := h.2

/-- The "maximal normal nilpotent `S`-subgroup" of `X` (FT writes `H(M)`;
§14: `H` is *the* maximal normal nilpotent `S`-subgroup of `X`). -/
def IsMaxNilHall (H X : Subgroup G) : Prop :=
  IsHallIn H X ∧ (H.subgroupOf X).Normal ∧ Group.IsNilpotent ↥H ∧
    ∀ K : Subgroup G, IsHallIn K X → (K.subgroupOf X).Normal → Group.IsNilpotent ↥K → K ≤ H

theorem IsMaxNilHall.hall {H X : Subgroup G} (h : IsMaxNilHall H X) : IsHallIn H X := h.1

theorem IsMaxNilHall.le {H X : Subgroup G} (h : IsMaxNilHall H X) : H ≤ X := h.1.le

theorem IsMaxNilHall.normal {H X : Subgroup G} (h : IsMaxNilHall H X) :
    (H.subgroupOf X).Normal := h.2.1

theorem IsMaxNilHall.nilpotent {H X : Subgroup G} (h : IsMaxNilHall H X) :
    Group.IsNilpotent ↥H := h.2.2.1

theorem IsMaxNilHall.maximal {H X : Subgroup G} (h : IsMaxNilHall H X) {K : Subgroup G}
    (hK : IsHallIn K X) (hKn : (K.subgroupOf X).Normal) (hKnil : Group.IsNilpotent ↥K) :
    K ≤ H := h.2.2.2 K hK hKn hKnil

/-- FT §2 (ch. I p. 780): `A` is a *T.I. set* in `G` if for every `x` either
`A^x ∩ A ⊆ {1}` or `A^x = A`. -/
def IsTISet (A : Set G) : Prop :=
  ∀ x : G, ((fun a => x⁻¹ * a * x) '' A) ∩ A ⊆ {1} ∨ (fun a => x⁻¹ * a * x) '' A = A

/-- `E` is a complement for `H` in `X` (`H ⊓ E = ⊥`, `H ⊔ E = X`). -/
structure IsComplementIn (H E X : Subgroup G) : Prop where
  sup_eq : H ⊔ E = X
  inf_eq : H ⊓ E = ⊥

theorem IsComplementIn.le_left {H E X : Subgroup G} (h : IsComplementIn H E X) : H ≤ X := by
  rw [← h.sup_eq]; exact le_sup_left

theorem IsComplementIn.le_right {H E X : Subgroup G} (h : IsComplementIn H E X) : E ≤ X := by
  rw [← h.sup_eq]; exact le_sup_right

/-! ## FT's `𝒮𝒞𝒩` (ch. I p. 778)

"A *self centralizing subgroup* of `X` is a subgroup `A` of `X` such that
`A = C(A)`"; `𝒮𝒞𝒩(X)` is the set of self centralizing normal subgroups of `X`,
`𝒮𝒞𝒩_m(X) = {A ∈ 𝒮𝒞𝒩(X) | m(A) ≥ m}`. -/

/-- FT's `𝒮𝒞𝒩(P)`: `A` is a normal self-centralizing subgroup of `P`. -/
def IsSCN (P A : Subgroup G) : Prop :=
  A ≤ P ∧ (A.subgroupOf P).Normal ∧ Subgroup.centralizer (A : Set G) ⊓ P = A

/-- FT's `𝒮𝒞𝒩_m(P)`. -/
def IsSCNm (m : ℕ) (P A : Subgroup G) : Prop := IsSCN P A ∧ m ≤ Group.rank ↥A

/-- FT's `𝒮𝒞𝒩₃(P)` is non-empty. -/
def HasSCN3 (P : Subgroup G) : Prop := ∃ A : Subgroup G, IsSCNm 3 P A

/-! ## Characters and the inertia group (FT §2, ch. I p. 780)

"If `H` is a normal subgroup of the group `X` and `θ` is a character of `H`,
`I(θ)` denotes the *inertial group of* `θ`, that is
`I(θ) = {X | X ∈ X, θ(X⁻¹ H X) = θ(H) for all H ∈ H}`."

We use the `FDRep` characterisation of irreducibility so that no `Fintype`
hypothesis is needed; `isIrrChar_iff_mem_Irr` bridges to `Work.CharCore.Irr`. -/

/-- `θ` is an irreducible character of the subgroup `H` (as a function on `↥H`). -/
def IsIrrChar (H : Subgroup G) (θ : ↥H → ℂ) : Prop :=
  ∃ V : FDRep ℂ ↥H, CategoryTheory.Simple V ∧ V.character = θ

/-- FT's inertial group `I(θ)`, for `θ` a character of `H ⊴ X`, as a subgroup of
the ambient group: the elements of `X` that fix `θ` under conjugation. -/
def inertiaIn (X H : Subgroup G) (hHX : H ≤ X) (hN : (H.subgroupOf X).Normal) (θ : ↥H → ℂ) :
    Subgroup G :=
  letI := hN
  (Work.Clifford.inertia (H.subgroupOf X)
    (fun y => θ (Subgroup.subgroupOfEquivOfLe hHX y))).map X.subtype

/-! ## FT §2: Frobenius groups, Frobenius type, three step groups (ch. I p. 780) -/

/-- FT: "A group `X` is a *Frobenius group* with *Frobenius kernel* `H` iff `H` is
a proper normal subgroup of `X` which contains the centralizer of every element
in `H^#`."  Here `X`, `H` are subgroups of the ambient `G`; the group is `X`. -/
structure IsFrobeniusIn (X K : Subgroup G) : Prop where
  le : K ≤ X
  normal : (K.subgroupOf X).Normal
  ne_bot : K ≠ ⊥
  ne : K ≠ X
  cent : ∀ h ∈ K, h ≠ 1 → Subgroup.centralizer ({h} : Set G) ⊓ X ≤ K

/-- FT: "`X` is of *Frobenius type* with Frobenius kernel `H`" (ch. I p. 780,
conditions (i)--(iii)).  The complement `E` is quantified over; `C` is the
ambient centralizer (ch. I p. 777). -/
structure IsFrobeniusType (X H : Subgroup G) : Prop where
  maxNil : IsMaxNilHall H X
  ne_bot : H ≠ ⊥
  ne : H ≠ X
  compl : ∀ E : Subgroup G, E ≤ X → IsComplementIn H E X →
    (∃ A : Subgroup G, A ≤ E ∧ (A.subgroupOf E).Normal ∧ IsMulCommutative ↥A ∧
      ∀ θ : ↥H → ℂ, IsIrrChar H θ → θ ≠ 1 →
        inertiaIn X H maxNil.le maxNil.normal θ ⊓ E ≤ A) ∧
    (∃ E₀ : Subgroup G, E₀ ≤ E ∧ Monoid.exponent ↥E₀ = Monoid.exponent ↥E ∧
      IsFrobeniusIn (E₀ ⊔ H) H)

/-- FT: "A group `S` is a *three step group* iff (i) `S = S'Q*` ...  (ii) `S`
contains a non cyclic normal `S`-subgroup `H` such that `S'' ⊆ H C(H) ⊆ S'`,
`H C(H)` is nilpotent and `H` is the maximal normal nilpotent `S`-subgroup of
`S`; (iii) `H` contains a cyclic subgroup `H* ≠ 1` such that for `Q ∈ Q*^#`,
`C_{S'}(Q) = H*`."  (`W₁` is FT's `Q*`.) -/
structure IsThreeStep (S W₁ H Hstar : Subgroup G) : Prop where
  sup_commutator : W₁ ⊔ ⁅S, S⁆ = S
  inf_commutator : W₁ ⊓ ⁅S, S⁆ = ⊥
  cyclic : IsCyclic ↥W₁
  hall : IsHallIn W₁ S
  ne_bot : W₁ ≠ ⊥
  noncyclic : ¬ IsCyclic ↥H
  maxNil : IsMaxNilHall H S
  comm_comm_le : ⁅⁅S, S⁆, ⁅S, S⁆⁆ ≤ H ⊔ (Subgroup.centralizer (H : Set G) ⊓ S)
  le_commutator : H ⊔ (Subgroup.centralizer (H : Set G) ⊓ S) ≤ ⁅S, S⁆
  hc_nilpotent : Group.IsNilpotent ↥(H ⊔ (Subgroup.centralizer (H : Set G) ⊓ S))
  hstar_le : Hstar ≤ H
  hstar_cyclic : IsCyclic ↥Hstar
  hstar_ne_bot : Hstar ≠ ⊥
  cent_eq : ∀ Q ∈ W₁, Q ≠ 1 → Subgroup.centralizer ({Q} : Set G) ⊓ ⁅S, S⁆ = Hstar

/-! ## FT §14, p. 845: the sets `π*` and `π₁*`

"Let `π*` be the subset of `π(G)` consisting of all primes `p` such that if `P` is
an `S_p`-subgroup of `G`, then either `𝒮𝒞𝒩₃(P)` is empty or `P` contains a
subgroup `A` of order `p` such that `C_P(A) = A × B` where `B` is cyclic.  Let
`π₁*` be the subset of `π*` consisting of those `p` such that if `P` is an `S_p`-
subgroup of `G` and `a` is the order of a cyclic subgroup of
`N(P)/P C(P)`, then one of the following possibilities occurs: (i) `a` divides
`p - 1`.  (ii) `P` is abelian and `a` divides `p + 1`.  (iii) `|P| = p³` and `a`
divides `p + 1`." -/

/-- FT's `π*` (§14, p. 845). -/
def piStar (G : Type u) [Group G] [Finite G] : Set ℕ :=
  {p | p.Prime ∧ p ∣ Nat.card G ∧
    ∀ P : Sylow p G, ¬ HasSCN3 (P : Subgroup G) ∨
      ∃ A : Subgroup G, A ≤ (P : Subgroup G) ∧ Nat.card A = p ∧
        ∃ B : Subgroup G, IsCyclic ↥B ∧
          Subgroup.centralizer (A : Set G) ⊓ (P : Subgroup G) = A ⊔ B ∧ A ⊓ B = ⊥}

/-- The orders of cyclic subgroups of `N(P)/P C(P)`, in a quotient-free form:
`a` is such an order iff there is `y ∈ N(P)` whose powers meet `P·C(P)` first at
`a`. -/
def cycQuotOrders (P : Subgroup G) : Set ℕ :=
  {a | ∃ y ∈ Subgroup.normalizer (P : Set G), 0 < a ∧ y ^ a ∈ (P ⊔ Subgroup.centralizer (P : Set G)) ∧
    ∀ m : ℕ, 0 < m → m < a → y ^ m ∉ (P ⊔ Subgroup.centralizer (P : Set G))}

/-- FT's `π₁*` (§14, p. 845). -/
def piOneStar (G : Type u) [Group G] [Finite G] : Set ℕ :=
  {p | p ∈ piStar G ∧
    ∀ P : Sylow p G, ∀ a ∈ cycQuotOrders (P : Subgroup G),
      a ∣ p - 1 ∨ (IsMulCommutative ↥(P : Subgroup G) ∧ a ∣ p + 1) ∨
        (Nat.card (P : Subgroup G) = p ^ 3 ∧ a ∣ p + 1)}

end Work.FTSpine
