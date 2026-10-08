/-
# Area P2-01 `Work.LocalPrelim` : the elementary API of the local vocabulary

This module collects the trivial (definitional) parts of the API of the notions defined in
`Submission/Work/LocalPrelim/Defs.lean`, together with Grün's first theorem (the focal subgroup
theorem, which is Mathlib's `Subgroup.commutator_inf_eq_focalSubgroup`).

Nothing here needs more than `Work.LocalPrelim.Defs`; the deeper results live in the individual
`ft*.lean` files of the area.
-/
import Submission.Work.LocalPrelim.Defs

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

open scoped Classical Pointwise

noncomputable section

namespace Work.LocalPrelim

variable {G : Type*} [Group G]

/-! ## `SCN` -/

theorem IsSCN.le {P A : Subgroup G} (h : IsSCN P A) : A ≤ P := h.1

theorem IsSCN.normal_subgroupOf {P A : Subgroup G} (h : IsSCN P A) :
    (A.subgroupOf P).Normal := h.2.1

theorem IsSCN.isMulCommutative {P A : Subgroup G} (h : IsSCN P A) : IsMulCommutative ↥A := h.2.2.1

theorem IsSCN.self_centralizing {P A : Subgroup G} (h : IsSCN P A) :
    Subgroup.centralizer (A : Set G) ⊓ P ≤ A := h.2.2.2

theorem mem_SCNSet {P A : Subgroup G} : A ∈ SCNSet P ↔ IsSCN P A := Iff.rfl

/-- A commutative subgroup is contained in its own centralizer. -/
theorem le_centralizer_self_of_isMulCommutative {A : Subgroup G} (h : IsMulCommutative ↥A) :
    A ≤ Subgroup.centralizer (A : Set G) := by
  intro a ha
  rw [Subgroup.mem_centralizer_iff]
  intro b hb
  have hc := isMulCommutative_iff.mp h (⟨b, hb⟩ : ↥A) (⟨a, ha⟩ : ↥A)
  simpa using hc

/-- For `A ∈ SCN(P)` the centralizer of `A` meets `P` exactly in `A`. -/
theorem IsSCN.centralizer_inf_eq {P A : Subgroup G} (h : IsSCN P A) :
    Subgroup.centralizer (A : Set G) ⊓ P = A :=
  le_antisymm h.self_centralizing
    (le_inf (le_centralizer_self_of_isMulCommutative h.isMulCommutative) h.le)

theorem IsSCN_m.isSCN {m : ℕ} {P A : Subgroup G} [Finite G] (h : IsSCN_m m P A) : IsSCN P A :=
  h.1

theorem IsSCN_m.le_rank {m : ℕ} {P A : Subgroup G} [Finite G] (h : IsSCN_m m P A) :
    m ≤ Group.rank A := h.2

theorem IsSCN_m.isMulCommutative {m : ℕ} {P A : Subgroup G} [Finite G] (h : IsSCN_m m P A) :
    IsMulCommutative ↥A := h.1.isMulCommutative

theorem IsSCN_m.le {m : ℕ} {P A : Subgroup G} [Finite G] (h : IsSCN_m m P A) : A ≤ P := h.1.le

/-! ## `𝔐(A)` -/

theorem MSet.le_normalizer {A B : Subgroup G} (h : MSet A B) :
    A ≤ Subgroup.normalizer (B : Set G) := h.1

theorem MSet.inf_eq_bot {A B : Subgroup G} (h : MSet A B) : A ⊓ B = ⊥ := h.2

theorem MSetPi.mset {π : ℕ → Prop} {A B : Subgroup G} (h : MSetPi π A B) : MSet A B := h.1

theorem MSetPi.isPiGroup {π : ℕ → Prop} {A B : Subgroup G} (h : MSetPi π A B) :
    IsPiGroup π B := h.2

/-! ## Weak closure -/

theorem weakClosure_le (A B : Subgroup G) : weakClosure A B ≤ B := by
  rw [weakClosure, Subgroup.closure_le]
  rintro x ⟨g, hg, hx⟩
  exact hg hx

theorem subset_weakClosure {A B : Subgroup G} {g : G} (hg : MulAut.conj g • A ≤ B) :
    MulAut.conj g • A ≤ weakClosure A B := by
  intro x hx
  exact Subgroup.subset_closure ⟨g, hg, hx⟩

theorem le_weakClosure {A B : Subgroup G} (h : A ≤ B) : A ≤ weakClosure A B := by
  have h1 : MulAut.conj (1 : G) • A ≤ B := by simpa using h
  have h2 : A ≤ MulAut.conj (1 : G) • A := by simp
  exact h2.trans (subset_weakClosure h1)

theorem IsWeaklyClosed.def {A B : Subgroup G} (h : IsWeaklyClosed A B) : weakClosure A B = A := h

theorem IsWeaklyClosed.le {A B : Subgroup G} (h : IsWeaklyClosed A B) : A ≤ B := by
  have h1 := weakClosure_le A B
  rwa [h.def] at h1

/-! ## `IsSylowIn`, factors and `familyS` -/

theorem IsSylowIn.le {p : ℕ} {P H : Subgroup G} (h : IsSylowIn p P H) : P ≤ H := h.1

theorem IsSylowIn.isPGroup {p : ℕ} {P H : Subgroup G} (h : IsSylowIn p P H) : IsPGroup p P := h.2.1

theorem IsSylowIn.not_dvd_index {p : ℕ} {P H : Subgroup G} (h : IsSylowIn p P H) :
    ¬ p ∣ (P.subgroupOf H).index := h.2.2

theorem IsPiFactor.le {π : ℕ → Prop} {H K : Subgroup G} (h : IsPiFactor π H K) : H ≤ K := h.1

theorem IsPiFactor.index {π : ℕ → Prop} {H K : Subgroup G} (h : IsPiFactor π H K) :
    IsPiNat π (H.subgroupOf K).index := h.2

theorem IsPFactor.le {p : ℕ} {H K : Subgroup G} (h : IsPFactor p H K) : H ≤ K := h.1

theorem IsPFactor.index {p : ℕ} {H K : Subgroup G} (h : IsPFactor p H K) :
    IsPiNat (fun q => q = p) (H.subgroupOf K).index := h.2

theorem mem_familyS {p : ℕ} {P H : Subgroup G} :
    H ∈ familyS p P ↔ P ≤ H ∧ Work.Fitting.pLength p ↥H ≤ 2 ∧ NotThreePrimes H := Iff.rfl

theorem CentralizesFactor.def {S K H : Subgroup G} (h : CentralizesFactor S K H) : ⁅S, K⁆ ≤ H := h

/-! ## `O_p`, `O_{p'}` and `O_{p',p}` of a subgroup, as subgroups of the ambient group -/

theorem pCoreIn_le (p : ℕ) (H : Subgroup G) : pCoreIn p H ≤ H := Subgroup.map_subtype_le _

theorem pPrimeCoreIn_le (p : ℕ) (H : Subgroup G) : pPrimeCoreIn p H ≤ H := Subgroup.map_subtype_le _

theorem pPrimePCoreIn_le (p : ℕ) (H : Subgroup G) : pPrimePCoreIn p H ≤ H :=
  Subgroup.map_subtype_le _

theorem mem_pCoreIn_iff {p : ℕ} {H : Subgroup G} {x : G} :
    x ∈ pCoreIn p H ↔ ∃ y : ↥H, y ∈ Work.Fitting.pCore p ↥H ∧ (y : G) = x := by
  rw [pCoreIn, Subgroup.mem_map]
  exact ⟨fun ⟨y, hy, h⟩ => ⟨y, hy, h⟩, fun ⟨y, hy, h⟩ => ⟨y, hy, h⟩⟩

theorem mem_pPrimeCoreIn_iff {p : ℕ} {H : Subgroup G} {x : G} :
    x ∈ pPrimeCoreIn p H ↔ ∃ y : ↥H, y ∈ Work.Fitting.pPrimeCore p ↥H ∧ (y : G) = x := by
  rw [pPrimeCoreIn, Subgroup.mem_map]
  exact ⟨fun ⟨y, hy, h⟩ => ⟨y, hy, h⟩, fun ⟨y, hy, h⟩ => ⟨y, hy, h⟩⟩

theorem mem_pPrimePCoreIn_iff {p : ℕ} {H : Subgroup G} {x : G} :
    x ∈ pPrimePCoreIn p H ↔ ∃ y : ↥H, y ∈ Work.Fitting.pPrimePCore p ↥H ∧ (y : G) = x := by
  rw [pPrimePCoreIn, Subgroup.mem_map]
  exact ⟨fun ⟨y, hy, h⟩ => ⟨y, hy, h⟩, fun ⟨y, hy, h⟩ => ⟨y, hy, h⟩⟩

/-! ## P. Hall's propositions -/

theorem Cpi.epi {π : ℕ → Prop} {X : Type*} [Group X] (h : Cpi π X) : Epi π X := h.1

theorem Dpi.cpi {π : ℕ → Prop} {X : Type*} [Group X] (h : Dpi π X) : Cpi π X := h.1

theorem Dpi.exists_isHall_ge {π : ℕ → Prop} {X : Type*} [Group X] (h : Dpi π X)
    {H : Subgroup X} (hH : IsPiGroup π H) :
    ∃ K : Subgroup X, Work.Hall.IsHall π K ∧ H ≤ K := h.2 H hH

theorem EstarPi.epi {π : ℕ → Prop} {X : Type*} [Group X] (h : EstarPi π X) : Epi π X :=
  let ⟨H, hH, _⟩ := h; ⟨H, hH⟩

theorem Epi.of_isHall {π : ℕ → Prop} {X : Type*} [Group X] {H : Subgroup X}
    (h : Work.Hall.IsHall π H) : Epi π X := ⟨H, h⟩

/-! ## The stability group of a chain -/

theorem mem_stabilityGroupAut {X : Type*} [Group X] {n : ℕ} {C : Fin (n + 1) → Subgroup X}
    {α : MulAut X} : α ∈ stabilityGroupAut C ↔ autStabilizesChain α C := Iff.rfl

theorem stabilityGroupAut_map_eq {X : Type*} [Group X] {n : ℕ} {C : Fin (n + 1) → Subgroup X}
    {α : MulAut X} (h : α ∈ stabilityGroupAut C) (i : Fin (n + 1)) :
    Subgroup.map α.toMonoidHom (C i) = C i := h.1 i

theorem stabilityGroupAut_coset {X : Type*} [Group X] {n : ℕ} {C : Fin (n + 1) → Subgroup X}
    {α : MulAut X} (h : α ∈ stabilityGroupAut C) (i : Fin n) {x : X} (hx : x ∈ C i.castSucc) :
    α x * x⁻¹ ∈ C i.succ := h.2 i x hx

/-! ## Grün's first theorem (the focal subgroup theorem) -/

/-- **M. Hall 14.4.1 / Grün's first theorem** (the focal subgroup theorem): for a Sylow
`p`-subgroup `P` of a finite group, `P ∩ X'` is the focal subgroup of `P`, generated by the
elements `x⁻¹ y` with `x, y ∈ P` conjugate in `X`.  (This is Mathlib's
`Subgroup.commutator_inf_eq_focalSubgroup`.) -/
theorem grun_first {X : Type*} [Group X] [Finite X] {p : ℕ} [Fact p.Prime] (P : Sylow p X) :
    (P : Subgroup X) ⊓ ⁅(⊤ : Subgroup X), (⊤ : Subgroup X)⁆ = (P : Subgroup X).focalSubgroup := by
  rw [inf_comm]
  exact Subgroup.commutator_inf_eq_focalSubgroup P

end Work.LocalPrelim
