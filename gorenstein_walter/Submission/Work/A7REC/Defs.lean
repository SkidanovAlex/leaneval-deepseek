/-
Area A7REC of the Gorenstein--Walter project: **recognition of `A₇`** (Bender 1.8 / Suzuki 1959 §8).

The area's deliverable is `A7RecProp`, verbatim from
`Submission/Work/_design_gw/Contracts2.lean`:

> a finite simple group `G` of order `2520` whose Sylow `2`-subgroup is dihedral of order `8`,
> with `z` the central involution of a Sylow `2`-subgroup, `C_G(z) = U ⊔ S` with `|U| = 3`,
> `V = O₂(C_G(z))` a four-group, `N_G(U) = N_G(V)` of order `72`, and a conjugate of `U`
> different from `U` inside `N_G(V)`, is isomorphic to `A₇`.

## Layout of the area

* `Submission/Work/A7REC/Defs.lean`      -- this file: the vocabulary, `A7RecProp`, and the
  hypothesis bundle `A7RecCtx` used by every other file of the area.
* `Submission/Work/A7REC/Basic/*.lean`   -- the structural consequences of `A7RecCtx`
  (orders of the local subgroups, `z ∈ V`, `|C_G(U)| = 36`, Sylow counts, ...).
* `Submission/Work/A7REC/Reduction.lean` -- `A7RecProp` follows from an index-`7` subgroup
  (via the proved `Work.A7.mulEquiv_A7_of_index_seven`), and from the two character-theoretic
  residual statements of the Suzuki route.
* `Submission/Work/A7REC/NOTES_*.md`     -- the transcription of Suzuki 1959 §5 (exceptional
  characters for `|U| = 3`), the leaf list, and the design of the recognition step.

## Namespace note

The contract's Props are copied **verbatim** below, but in the area's own namespace
`Work.A7REC` (and not in `Work.GW2`): several other areas of the workspace already declare
`Work.GW2.IsFourGroup`, `Work.GW2.pCore`, ... and importing two such files is a hard error.
All copies have the *same bodies* as the contract's, so `Work.A7REC.A7RecProp` is
definitionally equal to `GW2.A7RecProp` (and `Work.GW2.A7RecProp`) and a proof of one is a
proof of the other.  `Submission/Work/A7REC/GW2Bridge.lean` repeats the verbatim declaration in
namespace `Work.GW2` for callers that do not import another area's vocabulary.
-/
import Mathlib
import Submission.Work.A7.Defs

open scoped MatrixGroups

namespace Work.A7REC

open Subgroup

/-! ## 1. The contract's vocabulary, verbatim (from `_design_gw/Contracts2.lean`) -/

variable {G : Type*} [Group G]

/-- `O_p(G)`.  Verbatim from `Contracts2.lean`. -/
def pCore (p : ℕ) (G : Type*) [Group G] : Subgroup G :=
  (sSup {N : Subgroup G | N.Normal ∧ IsPGroup p N}).normalCore

instance pCore_normal (p : ℕ) (G : Type*) [Group G] : (pCore p G).Normal :=
  Subgroup.normalCore_normal _

/-- `O_p(K)` relative to a subgroup `K` of an ambient group.  Verbatim from `Contracts2.lean`. -/
def pCoreIn (p : ℕ) (K : Subgroup G) : Subgroup G := (pCore p K).map K.subtype

/-- Klein four-group (type `(2,2)`).  Verbatim from `Contracts2.lean`. -/
def IsFourGroup (V : Subgroup G) : Prop := Nat.card V = 4 ∧ ∀ v ∈ V, v ^ 2 = 1

/-- **The deliverable of this area**: `A₇` recognition, verbatim from `Contracts2.lean`.

A finite simple group of order `2520` whose Sylow `2`-subgroup is dihedral of order `8`, whose
involution `z` has `C_G(z) = U ⊔ S` with `|U| = 3` and `U ⊴ C_G(z)`, with
`V = O₂(U ⊔ S)` a four-group, `N_G(U) = N_G(V)` of order `72` and a conjugate `U^g ≠ U` of `U`
inside `N_G(V)`, is isomorphic to `A₇`. -/
def A7RecProp : Prop :=
  ∀ (G : Type) [Group G] [Finite G], IsSimpleGroup G → Nat.card G = 2520 →
    ∀ (S : Sylow 2 G), Nonempty ((S : Subgroup G) ≃* DihedralGroup 4) →
    ∀ (z : G) (U V : Subgroup G), z ∈ (S : Subgroup G) → orderOf z = 2 →
      (∀ x ∈ (S : Subgroup G), x * z = z * x) →
      centralizer ({z} : Set G) = U ⊔ (S : Subgroup G) → Nat.card U = 3 →
      (U.subgroupOf (centralizer ({z} : Set G))).Normal →
      V = pCoreIn 2 (U ⊔ (S : Subgroup G)) → IsFourGroup V →
      (∃ g : G, U.map (MulAut.conj g).toMonoidHom ≠ U ∧
        U.map (MulAut.conj g).toMonoidHom ≤ normalizer (V : Set G)) →
      normalizer (U : Set G) = normalizer (V : Set G) →
      Nat.card (normalizer (U : Set G)) = 72 →
      Nonempty (G ≃* alternatingGroup (Fin 7))

/-! ## 2. The hypothesis bundle

Every lemma of the area is stated for a single structure `A7RecCtx G`, whose fields are exactly
the hypotheses of `A7RecProp`.  Writing `ctx : A7RecCtx G`,
* `ctx.S`  is the Sylow `2`-subgroup of `G` (a `Sylow 2 G`),
* `ctx.z`  is its central involution,
* `ctx.U`  is the subgroup of order `3` with `C_G(z) = U ⊔ S`,
* `ctx.V`  is `V = O₂(U ⊔ S)`, a four-group.
-/

/-- The hypotheses of `A7RecProp`, as a structure. -/
structure A7RecCtx (G : Type*) [Group G] [Finite G] where
  /-- `G` is simple. -/
  simple : IsSimpleGroup G
  /-- `|G| = 2520`. -/
  hcard : Nat.card G = 2520
  /-- a Sylow `2`-subgroup. -/
  S : Sylow 2 G
  /-- it is dihedral of order `8`. -/
  hSdih : Nonempty ((S : Subgroup G) ≃* DihedralGroup 4)
  /-- the central involution. -/
  z : G
  /-- it lies in `S`. -/
  hzS : z ∈ (S : Subgroup G)
  /-- it has order `2`. -/
  hz2 : orderOf z = 2
  /-- it is central in `S`. -/
  hzcen : ∀ x ∈ (S : Subgroup G), x * z = z * x
  /-- the subgroup of order `3` with `C_G(z) = U ⊔ S`. -/
  U : Subgroup G
  /-- `C_G(z) = U ⊔ S`. -/
  hCz : centralizer ({z} : Set G) = U ⊔ (S : Subgroup G)
  /-- `|U| = 3`. -/
  hUcard : Nat.card U = 3
  /-- `U` is normal in `C_G(z)`. -/
  hUnorm : (U.subgroupOf (centralizer ({z} : Set G))).Normal
  /-- `V = O₂(U ⊔ S)`. -/
  V : Subgroup G
  /-- definition of `V`. -/
  hVdef : V = pCoreIn 2 (U ⊔ (S : Subgroup G))
  /-- `V` is a four-group. -/
  hV4 : IsFourGroup V
  /-- a conjugate of `U`, different from `U`, normalizing `V`. -/
  hcross : ∃ g : G, U.map (MulAut.conj g).toMonoidHom ≠ U ∧
    U.map (MulAut.conj g).toMonoidHom ≤ normalizer (V : Set G)
  /-- `N_G(U) = N_G(V)`. -/
  hNUV : normalizer (U : Set G) = normalizer (V : Set G)
  /-- `|N_G(U)| = 72`. -/
  hNUcard : Nat.card (normalizer (U : Set G)) = 72

namespace A7RecCtx

variable {G : Type*} [Group G] [Finite G] (ctx : A7RecCtx G)

/-- `C_G(z)`, the centralizer of the central involution. -/
abbrev C : Subgroup G := centralizer ({ctx.z} : Set G)

/-- The Sylow `2`-subgroup, as a subgroup. -/
abbrev Ssub : Subgroup G := (ctx.S : Subgroup G)

/-- `N_G(U)`, which equals `N_G(V)`. -/
abbrev NU : Subgroup G := normalizer (ctx.U : Set G)

/-- `N_G(V)`, which equals `N_G(U)`. -/
abbrev NV : Subgroup G := normalizer (ctx.V : Set G)

@[simp] theorem C_eq : ctx.C = ctx.U ⊔ ctx.Ssub := ctx.hCz

theorem U_le_C : ctx.U ≤ ctx.C := by rw [C_eq]; exact le_sup_left

theorem S_le_C : ctx.Ssub ≤ ctx.C := by rw [C_eq]; exact le_sup_right

theorem z_mem_S : ctx.z ∈ ctx.Ssub := ctx.hzS

theorem z_central_in_S {x : G} (hx : x ∈ ctx.Ssub) : x * ctx.z = ctx.z * x := ctx.hzcen x hx

theorem card_NU : Nat.card ctx.NU = 72 := ctx.hNUcard

theorem card_NV : Nat.card ctx.NV = 72 := by
  change Nat.card (normalizer (ctx.V : Set G)) = 72
  rw [← ctx.hNUV]
  exact ctx.hNUcard

theorem eq_NV : ctx.NU = ctx.NV := ctx.hNUV

end A7RecCtx

/-! ## 3. The residual statements of the area -/

/-- **Residual statement of the Suzuki route.**  For every group satisfying the `A₇` hypotheses
there is a subgroup of index `7`.  By `Work.A7.mulEquiv_A7_of_index_seven` this is equivalent to
`A7RecProp`. -/
def A7IndexSevenProp : Prop :=
  ∀ (G : Type) [Group G] [Finite G], A7RecCtx G → ∃ H : Subgroup G, H.index = 7

/-- **Residual statement, subgroup-of-order-360 form.**  `|G| = 2520`, so a subgroup of order
`360` has index `7`.  This is the shape in which the Suzuki 1959 §8 argument produces `H`: the
stabilizer of a vector in the degree-`6` representation. -/
def A7Subgroup360Prop : Prop :=
  ∀ (G : Type) [Group G] [Finite G], A7RecCtx G → ∃ H : Subgroup G, Nat.card H = 360

/-! ## 4. The design-pass-4 vocabulary, verbatim

`Submission/Work/_design_gw/Core4.lean` §3 restates the deliverable of this area as `A7Rec2Prop`
(the `A₇` hypotheses plus the minimal-counterexample premise `SmallerDGroups G`), routed through
the degree-`6` representation (`A7Char6Prop`, C1) and the Suzuki §8 stabilizer argument
(`A7IndexSevenFromCharProp`, C2+C3).  The statements are copied verbatim below, in this area's
namespace, so that the assembly of the area can be written and checked here; a theorem stated for
these copies is definitionally equal to one stated for `GW2`'s. -/

/-- `O(G) = O_{2'}(G)`.  Verbatim from `Contracts2.lean`. -/
def oddCore (G : Type*) [Group G] : Subgroup G :=
  (sSup {N : Subgroup G | N.Normal ∧ Odd (Nat.card N)}).normalCore

instance oddCore_normal (G : Type*) [Group G] : (oddCore G).Normal :=
  Subgroup.normalCore_normal _

/-- Sylow `2`-subgroups are cyclic or dihedral.  Verbatim from `Contracts2.lean`. -/
def DihOrCycSylow (G : Type*) [Group G] [Finite G] : Prop :=
  ∀ P : Sylow 2 G, IsCyclic P ∨ ∃ n : ℕ, Nonempty ((P : Subgroup G) ≃* DihedralGroup n)

/-- The four shapes of `G/O(G)` for a D-group.  Verbatim from `Contracts2.lean`. -/
def DShape (Q : Type*) [Group Q] [Finite Q] : Prop :=
  IsPGroup 2 Q ∨
  (∃ V : Subgroup Q, V.Normal ∧ IsFourGroup V ∧ centralizer (V : Set Q) = V) ∨
  Nonempty (Q ≃* alternatingGroup (Fin 7)) ∨
  ∃ L : Subgroup Q, L.Normal ∧ Odd L.index ∧ ∃ p k : ℕ, ∃ _ : Fact p.Prime, Odd p ∧ 5 ≤ p ^ k ∧
    (Nonempty (L ≃* PSL(2, GaloisField p k)) ∨ Nonempty (L ≃* PGL(2, GaloisField p k)))

/-- Bender's D-group.  Verbatim from `Contracts2.lean`. -/
def IsDGroup (G : Type*) [Group G] [Finite G] : Prop := DShape (G ⧸ oddCore G)

/-- The induction premise: every strictly smaller group of the class is a D-group.
Verbatim from `Contracts2.lean`. -/
def SmallerDGroups (G : Type*) [Group G] [Finite G] : Prop :=
  ∀ (X : Type) [Group X] [Finite X], Nat.card X < Nat.card G → DihOrCycSylow X → IsDGroup X

/-- The hypotheses of `A7RecProp`, bundled.  Verbatim from `Core4.lean` §3. -/
def A7RecHyps (G : Type) [Group G] [Finite G] (S : Sylow 2 G) (z : G) (U V : Subgroup G) :
    Prop :=
  IsSimpleGroup G ∧ Nat.card G = 2520 ∧ Nonempty ((S : Subgroup G) ≃* DihedralGroup 4) ∧
    z ∈ (S : Subgroup G) ∧ orderOf z = 2 ∧ (∀ x ∈ (S : Subgroup G), x * z = z * x) ∧
    centralizer ({z} : Set G) = U ⊔ (S : Subgroup G) ∧ Nat.card U = 3 ∧
    (U.subgroupOf (centralizer ({z} : Set G))).Normal ∧
    V = pCoreIn 2 (U ⊔ (S : Subgroup G)) ∧ IsFourGroup V ∧
    (∃ g : G, U.map (MulAut.conj g).toMonoidHom ≠ U ∧
      U.map (MulAut.conj g).toMonoidHom ≤ normalizer (V : Set G)) ∧
    normalizer (U : Set G) = normalizer (V : Set G) ∧ Nat.card (normalizer (U : Set G)) = 72

/-- **C1** (design pass 4 §2): an irreducible character of degree `6`, with value `2` at `z`, `3`
on `U#` and `-1` at elements of order `7`.  These are the values of the deleted permutation
character of `A₇`.  Verbatim from `Core4.lean` §3. -/
def A7Char6Prop : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (S : Sylow 2 G) (z : G) (U V : Subgroup G),
    A7RecHyps G S z U V →
    ∃ (W : Type) (_ : AddCommGroup W) (_ : Module ℂ W) (_ : FiniteDimensional ℂ W)
      (ρ : Representation ℂ G W),
      Module.finrank ℂ W = 6 ∧
      LinearMap.trace ℂ W (ρ z) = 2 ∧
      (∀ u ∈ U, u ≠ 1 → LinearMap.trace ℂ W (ρ u) = 3) ∧
      (∀ x : G, orderOf x = 7 → LinearMap.trace ℂ W (ρ x) = -1)

/-- **C2 + C3** (Suzuki §8, p. 270): from the degree-`6` representation, a vector fixed by `U`
and a suitable Sylow `2`-subgroup has stabilizer of index `7`.  Verbatim from `Core4.lean` §3. -/
def A7IndexSevenFromCharProp : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (S : Sylow 2 G) (z : G) (U V : Subgroup G),
    A7RecHyps G S z U V → SmallerDGroups G →
    (∃ (W : Type) (_ : AddCommGroup W) (_ : Module ℂ W) (_ : FiniteDimensional ℂ W)
      (ρ : Representation ℂ G W),
      Module.finrank ℂ W = 6 ∧ LinearMap.trace ℂ W (ρ z) = 2 ∧
      (∀ u ∈ U, u ≠ 1 → LinearMap.trace ℂ W (ρ u) = 3) ∧
      (∀ x : G, orderOf x = 7 → LinearMap.trace ℂ W (ρ x) = -1)) →
    ∃ H : Subgroup G, H.index = 7

/-- `A7RecProp` with the minimal-counterexample premise (amended contract).  Verbatim from
`Core4.lean` §3. -/
def A7Rec2Prop : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (S : Sylow 2 G) (z : G) (U V : Subgroup G),
    A7RecHyps G S z U V → SmallerDGroups G → Nonempty (G ≃* alternatingGroup (Fin 7))

/-! ## 5. The design-pass-6 leaves of C1, verbatim from `_design_gw/Core6.lean` §2

Design pass 6 replaces Suzuki's Brauer blocks by two *TI subsets*: `{π, π⁻¹} ⊆ S` (π of order
`4`, `C(π) = ⟨π⟩`) and `zU ⊆ N = C_G(z)`.  For both, the library's TI isometry applies; the
induced generalised characters give the values of the degree-`6` character, and every other
irreducible vanishes on the `2`-singular elements, so its degree is divisible by `8`. -/

/-- `{π, π⁻¹}` is a TI subset with normalizer bound `S`, for `π ∈ S` of order `4` with
`C(π) = ⟨π⟩` and `N(⟨π⟩) = S`.  Verbatim from `Core6.lean` §2. -/
def A7TIOrderFourProp : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (S : Sylow 2 G) (π : G), π ∈ (S : Subgroup G) →
    orderOf π = 4 → centralizer ({π} : Set G) = zpowers π →
    normalizer ((zpowers π : Subgroup G) : Set G) = S →
    ∀ g : G, (g * π * g⁻¹ = π ∨ g * π * g⁻¹ = π⁻¹) → g ∈ (S : Subgroup G)

/-- `zU = {zσ : σ ∈ U}` is a TI subset with normalizer bound `N = C(z)`.  Verbatim from
`Core6.lean` §2. -/
def A7TIzUProp : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (z : G) (U : Subgroup G), orderOf z = 2 →
    Odd (Nat.card U) → U ≤ centralizer ({z} : Set G) →
    ∀ (g : G) (σ σ' : G), σ ∈ U → σ' ∈ U → g * (z * σ) * g⁻¹ = z * σ' →
      g ∈ centralizer ({z} : Set G)

/-- The degree lemma ([CHECKED] by brute force: unique solution), in the sign convention of
design pass 6 §2.  Verbatim from `Core6.lean` §2. -/
def A7DegreeLemmaProp : Prop :=
  ∀ (y : Fin 4 → ℕ) (δ : Fin 4 → ℤ) (m : ℕ), (∀ i, δ i = 1 ∨ δ i = -1) → (∀ i, 3 ≤ y i) →
    (∀ i, ((y i : ℤ) - 2 * δ i) % 8 = 0) → ∑ i, δ i * (y i : ℤ) = 0 →
    ∑ i, ((δ i : ℚ) / (y i : ℚ)) = -4 / 105 → ∑ i, (y i) ^ 2 + 64 * m = 432 →
    m = 0 ∧ ∃ i, y i = 6 ∧ δ i = -1 ∧ ∀ j, j ≠ i → y j ≠ 6

/-! ## 6. The design-pass-7 leaves of C1, verbatim from `_design_gw/Core7.lean` §1

Design pass 7 (`NOTES_LEAD_gw_design7.md`) retires C1-H and C1d: Suzuki's §6 order formula is no
longer needed.  The degree-`6` character is obtained from the involution-pair counts `i(π) = 4`,
`i(z) = 8`, `i(zσ) = 6`, the class-multiplication bridge, the finite table lemma, and the value
lemma `A7Y6ValuesProp`. -/

/-- Number of ordered pairs of involutions with product `x`.  Verbatim from `Core7.lean` §1. -/
noncomputable def C7invPairCount {G : Type*} [Group G] (x : G) : ℕ :=
  {p : G × G | orderOf p.1 = 2 ∧ orderOf p.2 = 2 ∧ p.1 * p.2 = x}.ncard

/-- Local involution-pair counts (pure group theory from the `A₇` data and A1).  Verbatim from
`Core7.lean` §1. -/
def A7InvolutionCountsProp : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (S : Sylow 2 G) (z : G) (U : Subgroup G) (π σ : G),
    (IsSimpleGroup G ∧ Nat.card G = 2520) → z ∈ (S : Subgroup G) → orderOf z = 2 →
    centralizer ({z} : Set G) = U ⊔ (S : Subgroup G) → Nat.card U = 3 → σ ∈ U → σ ≠ 1 →
    π ∈ (S : Subgroup G) → orderOf π = 4 → centralizer ({π} : Set G) = zpowers π →
    Nonempty ((S : Subgroup G) ≃* DihedralGroup 4) →
    C7invPairCount π = 4 ∧ C7invPairCount z = 8 ∧ C7invPairCount (z * σ) = 6

/-- **The table lemma** (pure; [CHECKED] by exhaustive search: unique solution `A₇`).  Verbatim
from `Core7.lean` §1. -/
def A7TableLemmaProp : Prop :=
  ∀ (n : ℕ) (f : Fin n → ℕ) (e a b : Fin n → ℤ),
    (∀ i, e i ≠ 0 ∨ a i ≠ 0 ∨ b i ≠ 0) → (∀ i, 2 ≤ f i) → (∀ i, f i ∣ 2520) →
    ∑ i, e i ^ 2 = 3 → ∑ i, a i ^ 2 = 4 → ∑ i, b i ^ 2 = 7 →
    ∑ i, e i * a i = 0 → ∑ i, e i * b i = -1 → ∑ i, a i * b i = 0 →
    1 + ∑ i, e i * (f i : ℤ) = 0 → ∑ i, a i * (f i : ℤ) = 0 → 1 + ∑ i, b i * (f i : ℤ) = 0 →
    (∀ i, ((f i : ℤ) + 5 * (b i - 2 * a i) + 2 * e i) % 8 = 0) →
    1 + ∑ i, ((b i - 2 * a i) ^ 2 * e i : ℚ) / (f i : ℚ) = 32 / 35 →
    1 + ∑ i, ((b i - 2 * a i) ^ 3 : ℚ) / (f i : ℚ) = 64 / 35 →
    1 + ∑ i, ((b i - 2 * a i) ^ 2 * (a i + b i) : ℚ) / (f i : ℚ) = 48 / 35 →
    1 + ∑ i, (f i) ^ 2 ≤ 2520 →
    1 + ∑ i, (f i) ^ 2 = 2520 ∧
      ∃ i, f i = 6 ∧ e i = 0 ∧ a i = -1 ∧ b i = 0 ∧ ∀ j, j ≠ i → f j ≠ 6

/-- C1e: the value lemma for the degree-`6` irreducible.  Verbatim from `Core7.lean` §1. -/
def A7Y6ValuesProp : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (z σ : G) (W : Type) [AddCommGroup W] [Module ℂ W]
    [FiniteDimensional ℂ W] (ρ : Representation ℂ G W),
    IsSimpleGroup G → Nat.card G = 2520 → orderOf z = 2 → orderOf σ = 3 → z * σ = σ * z →
    Representation.IsIrreducible ρ → Module.finrank ℂ W = 6 → LinearMap.trace ℂ W (ρ z) = 2 →
    LinearMap.trace ℂ W (ρ (z * σ)) = -1 →
    (∃ τ' : G, orderOf τ' = 2 ∧ τ' * σ * τ'⁻¹ = σ⁻¹) →
    (∀ (W' : Type) [AddCommGroup W'] [Module ℂ W'] [FiniteDimensional ℂ W']
        (ρ' : Representation ℂ G W'), Representation.IsIrreducible ρ' → Module.finrank ℂ W' = 6 →
        ∀ g, LinearMap.trace ℂ W' (ρ' g) = LinearMap.trace ℂ W (ρ g)) →
    LinearMap.trace ℂ W (ρ σ) = 3 ∧ ∀ x : G, orderOf x = 7 → LinearMap.trace ℂ W (ρ x) = -1

/-! ## 7. The restated involution counts (design pass 13, `_design_gw/Core13.lean` §3)

`A7InvolutionCountsProp` above (copied from `Core7.lean`) quantifies over the bare hypotheses and
therefore lacks `U ⊴ C_G(z)`; its consumer (the C1 assembly) has the full `A7RecHyps`, i.e. an
`A7RecCtx`.  Design pass 13 restates it on the context, with leaves C1–C4 and the assembly
`c13_counts` proved from `c13_C3` and `c13_C4`. -/

/-- `A7InvolutionCountsProp` restated on `A7RecCtx` (design pass 13, `C5`).  Verbatim from
`Core13.lean` §3. -/
def A7InvolutionCounts2Prop : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (ctx : A7RecCtx G) (π σ : G),
    σ ∈ ctx.U → σ ≠ 1 → π ∈ ctx.Ssub → orderOf π = 4 →
    centralizer ({π} : Set G) = zpowers π →
    C7invPairCount π = 4 ∧ C7invPairCount ctx.z = 8 ∧ C7invPairCount (ctx.z * σ) = 6

end Work.A7REC
