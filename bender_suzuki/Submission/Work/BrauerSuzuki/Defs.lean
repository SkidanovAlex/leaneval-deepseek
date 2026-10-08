import Mathlib
import Submission.Blueprint.Interfaces

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# Area `BrauerSuzuki`: definitions

This is the base module of the area `BrauerSuzuki` of the Bender–Suzuki project: the theorem
`Submission.Blueprint.BrauerSuzukiProp` (a finite group of 2-rank `≤ 1` satisfies
`G = O(G) C_G(t)` for every involution `t`), proved by the route of `REFS/brauer_suzuki.md`
(Dade 1971 §5–6 for `|S| ≥ 16`, Glauberman 1974 for `Q₈`, then the glue §1.1–§1.2 and the
classification Huppert III.8.2).

## Group theory

* `Work.BrauerSuzuki.HasUniqueInvolution P` — `P` has exactly one element of order `2`.
* `Work.BrauerSuzuki.GenQuaternionData P` — the data of a generalized quaternion
  presentation in Dade's normal form (6.1): `n ≥ 2`, `τ, ρ ∈ P` with `orderOf τ = 2 ^ n`,
  `ρ τ ρ⁻¹ = τ⁻¹`, `ρ ^ 2 = τ ^ (2 ^ (n-1))`, `P = ⟨τ, ρ⟩`.  The associated predicate is
  `IsGenQuaternion P := Nonempty (GenQuaternionData P)`.
* `Work.BrauerSuzuki.IsCyclicOrGenQuaternion P` — the classification of 2-groups with a
  unique involution (Huppert III.8.2).

## The weak and strong forms of Brauer–Suzuki

* `Work.BrauerSuzuki.BrauerSuzukiWeak` — Brauer–Suzuki, Theorem 1 of the PNAS note: a finite
  group with generalized quaternion Sylow 2-subgroups has a proper normal subgroup containing
  every involution.  (Dade Thm 6.8 for `|S| ≥ 16`, Glauberman 1974 for `S ≅ Q₈`.)
  It is false for merely cyclic Sylow 2-subgroups (`S₃`), which is why the hypothesis is
  "generalized quaternion" and not "unique involution in a Sylow 2-subgroup".
* `BrauerSuzukiWeakLarge` (`n ≥ 3`, order `≥ 16`) and `BrauerSuzukiQ8Strong` (`n = 2`) are the
  two cases proved by Dade and Glauberman respectively; the second is stated in the strong
  form `|Z(G/O(G))| = 2`.
* `BrauerSuzukiQuaternion` — the strong form, quotient-free: every involution of a group with
  generalized quaternion Sylow 2-subgroups is central modulo `O(G)`.

## Character theory (Dade §5)

* `Work.BrauerSuzuki.sqrtSet σ = {τ : σ ∈ ⟨τ⟩}` — Dade's TI set `√σ` (5.12).
* `Work.BrauerSuzuki.IsTISet S H` — `S` is a TI (trivial intersection) set with normalizer `H`
  (Dade 5.10, set version).
* `Work.BrauerSuzuki.SupportLe f S` — the support of `f` is contained in `S`.
-/

set_option autoImplicit false

namespace Work.BrauerSuzuki

open Submission.Blueprint

variable {G : Type*} [Group G]

/-! ## Dade's TI sets -/

/-- Dade's set `√σ = {τ : σ ∈ ⟨τ⟩}` of roots of `σ` (Dade 1971, (5.11)). -/
def sqrtSet (σ : G) : Set G := {τ | σ ∈ Subgroup.zpowers τ}

@[simp] theorem mem_sqrtSet {σ τ : G} : τ ∈ sqrtSet σ ↔ σ ∈ Subgroup.zpowers τ := Iff.rfl

/-- A **TI set** (trivial intersection set) with normalizer `H`, in the set-theoretic form
used by Dade (1971, 5.10): `S` contains no `1`, lies in `H`, is closed under inversion, is
normalized by `H`, has normalizer contained in `H`, and distinct conjugates of `S` meet
trivially.  The principal example is `S = √σ`, `H = N_G(⟨σ⟩)` (`sqrtSet_isTISet`). -/
structure IsTISet (S : Set G) (H : Subgroup G) : Prop where
  /-- `1 ∉ S`. -/
  one_notMem : (1 : G) ∉ S
  /-- `S ⊆ H`. -/
  subset : ∀ ⦃x : G⦄, x ∈ S → x ∈ H
  /-- `S` is closed under inversion. -/
  inv_mem : ∀ ⦃x : G⦄, x ∈ S → x⁻¹ ∈ S
  /-- `H` normalizes `S`. -/
  mem_normalizer : ∀ ⦃h : G⦄, h ∈ H → ∀ ⦃x : G⦄, x ∈ S → h * x * h⁻¹ ∈ S
  /-- every element normalizing `S` lies in `H`. -/
  normalizer_le : ∀ ⦃g : G⦄, (∀ ⦃x : G⦄, x ∈ S → g * x * g⁻¹ ∈ S) → g ∈ H
  /-- distinct conjugates of `S` meet trivially. -/
  conj_disjoint : ∀ ⦃g : G⦄, g ∉ H → ∀ ⦃x y : G⦄, x ∈ S → y ∈ S → g * x * g⁻¹ ≠ y

/-- The support of a function on the ambient group is contained in a set. -/
def SupportLe (f : G → ℂ) (S : Set G) : Prop := ∀ ⦃g : G⦄, g ∉ S → f g = 0

/-- The support of a function on a subgroup is contained in a set of the ambient group. -/
def SupportLeSub {H : Subgroup G} (φ : H → ℂ) (S : Set G) : Prop :=
  ∀ h : H, (h : G) ∉ S → φ h = 0

/-! ## The largest normal odd order subgroup `O(G)` -/

/-- The supremum of a set of normal subgroups is normal. -/
theorem normal_sSup_of_normal {G : Type*} [Group G] {X : Set (Subgroup G)}
    (hX : ∀ N ∈ X, N.Normal) : (sSup X).Normal := by
  rw [Subgroup.normal_iff_map_conj_eq]
  intro g
  apply le_antisymm
  · rw [Subgroup.map_le_iff_le_comap, sSup_le_iff]
    intro N hN n hn
    exact le_sSup hN ((hX N hN).conj_mem n hn g)
  · rw [sSup_le_iff]
    intro N hN n hn
    have hmem : g⁻¹ * n * g ∈ sSup X := le_sSup hN ((hX N hN).conj_mem' n hn g)
    rw [Subgroup.mem_map]
    exact ⟨g⁻¹ * n * g, hmem, by simp [MulAut.conj_apply, mul_assoc]⟩

/-- `O(G)` is normal. -/
instance oddCore_normal (G : Type*) [Group G] : (Submission.Blueprint.oddCore G).Normal :=
  normal_sSup_of_normal (fun _ hN => hN.1)

/-! ## 2-groups with a unique involution -/

/-- `P` has exactly one involution. -/
def HasUniqueInvolution (P : Type*) [Group P] : Prop :=
  ∃ z : P, orderOf z = 2 ∧ ∀ w : P, orderOf w = 2 → w = z

/-- The data of a **generalized quaternion group**, in the normal form of Dade (1971), (6.1):
`P = ⟨τ, ρ⟩` with `orderOf τ = 2 ^ n`, `n ≥ 2`, `ρ τ ρ⁻¹ = τ⁻¹` and
`ρ ^ 2 = τ ^ (2 ^ (n-1))`.  Then `P` has order `2 ^ (n+1)` (Dade's `Q`), its unique involution
is `τ ^ (2 ^ (n-1))`, and for `n = 2` this is `Q₈`. -/
structure GenQuaternionData (P : Type*) [Group P] where
  /-- the integer `n` with `orderOf tau = 2 ^ n`. -/
  n : ℕ
  /-- `n ≥ 2`. -/
  hn : 2 ≤ n
  /-- a cyclic generator of index `2`. -/
  tau : P
  /-- the element of order `4` inverting `tau`. -/
  rho : P
  tau_order : orderOf tau = 2 ^ n
  rho_conj : rho * tau * rho⁻¹ = tau⁻¹
  rho_sq : rho ^ 2 = tau ^ (2 ^ (n - 1))
  closure_eq_top : Subgroup.closure ({tau, rho} : Set P) = ⊤

/-- `P` is a generalized quaternion group (Dade's (6.1)). -/
def IsGenQuaternion (P : Type*) [Group P] : Prop := Nonempty (GenQuaternionData P)

/-- The classification of 2-groups with a unique involution (Huppert, *Endliche Gruppen I*,
III.8.2; Gorenstein 5.4.10): such a group is cyclic or generalized quaternion. -/
def IsCyclicOrGenQuaternion (P : Type*) [Group P] : Prop :=
  IsCyclic P ∨ IsGenQuaternion P

/-! ## The weak and strong forms of Brauer–Suzuki -/

/-- **Brauer–Suzuki, weak form** (PNAS 1959 Thm 1).  A finite group with a generalized
quaternion Sylow 2-subgroup has a proper normal subgroup containing every involution
(the unique involution of a Sylow 2-subgroup and all its conjugates). -/
def BrauerSuzukiWeak : Prop :=
  ∀ (G : Type) [Group G] [Finite G], (∃ S : Sylow 2 G, IsGenQuaternion (S : Subgroup G)) →
    ∃ N : Subgroup G, N.Normal ∧ N ≠ ⊤ ∧ ∀ t : G, orderOf t = 2 → t ∈ N

/-- **Dade's Theorem 6.8** (`|S| ≥ 16`, i.e. `n ≥ 3` in the normal form): the weak form for
generalized quaternion Sylow 2-subgroups of order at least `16`. -/
def BrauerSuzukiWeakLarge : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (S : Sylow 2 G) (d : GenQuaternionData (S : Subgroup G)),
    3 ≤ d.n → ∃ N : Subgroup G, N.Normal ∧ N ≠ ⊤ ∧ ∀ t : G, orderOf t = 2 → t ∈ N

/-- **Glauberman 1974, the `Q₈` case** in its strong form: if the Sylow 2-subgroups of `G` are
generalized quaternion with `n = 2` (that is, `≅ Q₈`), then every involution of `G` is central
modulo `O(G)`. -/
def BrauerSuzukiQ8Strong : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (S : Sylow 2 G) (d : GenQuaternionData (S : Subgroup G)),
    d.n = 2 → ∀ t : G, orderOf t = 2 → ∀ g : G, t * g * t⁻¹ * g⁻¹ ∈ oddCore G

/-- **Brauer–Suzuki, strong form** (PNAS 1959 Thm 2; Glauberman 1974), in the quotient-free
shape used by the final argument: in a finite group with generalized quaternion Sylow
2-subgroups, every involution is central modulo `O(G)`. -/
def BrauerSuzukiQuaternion : Prop :=
  ∀ (G : Type) [Group G] [Finite G], (∃ S : Sylow 2 G, IsGenQuaternion (S : Subgroup G)) →
    ∀ t : G, orderOf t = 2 → ∀ g : G, t * g * t⁻¹ * g⁻¹ ∈ oddCore G

end Work.BrauerSuzuki
