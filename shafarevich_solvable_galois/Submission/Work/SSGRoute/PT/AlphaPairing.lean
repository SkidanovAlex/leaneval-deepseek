import Mathlib.Data.FunLike.IsApply
import Mathlib.GroupTheory.QuotientGroup.Defs
import Mathlib.Topology.Constructions.SumProd
import Mathlib.Algebra.Group.Subgroup.Basic
import Mathlib.Algebra.GroupWithZero.Action.Defs
import Submission.Work.AbsoluteKummer.Basic
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The `α`-pairings of the local class formation, in the coefficient (cochain) model

This module builds the two maps that Milne's class-formation theorem (*Arithmetic Duality
Theorems*, I.1.8) is about, in the workspace's continuous-cochain model
(`Work.AbsoluteKummer`), for an arbitrary topological group `G` and coefficient `G`-modules
`N`, `C`:

* `alphaZero` — `H⁰(G, Hom_ℤ(N,C)) →+ (H²(G,N) →+ H²(G,C))`, the map `f ↦ (x ↦ f ∘ x)` induced
  by an equivariant `f : N → C` (this is `mapH2` of the coefficient map, and it needs the
  conjugation action to make `H⁰(G, Hom_ℤ(N,C))` the *equivariant* homs);
* `alphaTwo` — `H²(G, Hom_ℤ(N,C)) →+ (H⁰(G,N) →+ H²(G,C))`, the map `c ↦ (n ↦ c ⌣ n)`, where
  `(c ⌣ n)(g,h) = c(g,h)(n)`.

They are the two ends of Milne's pairing `Ext^r_G(N, C) × H^{2-r}(G, N) → H²(G, C)`.  In the local
application the coefficient `C = \bar k_v^×` is divisible, so `Ext^r_G(N,C) = H^r(G, Hom_ℤ(N,C))`
(Milne (0.8)) and the class-formation theorem can be run entirely in *coefficient* cohomology,
with no abstract `Ext` needed.

## The coefficient module

`Hom_ℤ(N,C)` carries the **conjugation** action `(g • f)(n) = g • f (g⁻¹ • n)` (Milne §0).  Mathlib
puts the *pointwise* action on `N →+ C`, and a global re-registration of that instance would
silently change the meaning of `g • f` in every other file of this workspace; hence the module is
introduced as the structure `ConjHom N C` (a copy of `N →+ C`) carrying its own `AddCommGroup` and
`DistribMulAction` instances.  The underlying additive hom is `ConjHom.toHom`, so the existing
machinery for `AddMonoidHom` (`Work.AbsoluteKummer.mapH2`, `Work.GroupCohomology.IsEquivariant`, …)
applies to it.

## Relevance to the target

`Work.SSGRoute.PT.localTatePairing_deg02` is *exactly* the `r = 2` case of Milne's I.1.8(a) applied
to the finite module `N = M^∨(1) = DualMod p (M ⊗ T)`:

* `Ext²_G(N,C) = H²(G, Hom_ℤ(N,C)) ≅ H²(G, M)`, by the twist cancellation
  `Hom_ℤ(E^∨(1), Ωˣ) ≅ E` proved in this workspace (`hom_dualMod_local_units`,
  `hom_dualMod_units_equiv`);
* the target of `α²(G,N)` is `H⁰(G,N)^∨`, i.e. `Hom_{D_A}(M, μ_p)^∨`.

Consequently the target needs **only part (a) of Milne's I.1.8** — no Kummer duality
(I.1.8(b)/(c)) and no degree-`1` input.  `alphaTwo` is the map whose non-degeneracy carries that
statement; its compatibility with the connecting maps of a short exact sequence of coefficients is
what the five-lemma dévissage of Milne's proof consumes.

## What is here, and the road to `Milne18AtZero`

Proved in this file (no arithmetic input):

* `ConjHom N C` = `Hom_ℤ(N,C)` with the conjugation action, and the additive maps
  `ConjHom.precomp φ` (`f ↦ f ∘ φ`), `ConjHom.postcomp ψ` (`f ↦ ψ ∘ f`), `ConjHom.evalHom n`
  (`f ↦ f n`), with the equivariance lemmas `precomp_smul`, `postcomp_smul`, `evalHom_smul`, and
  `map_mem_invariants` / `invariantsHom` (the induced map on the invariants `N^G`);
* `cupCochain`, `cupCochainZ2`, `cupCochain_mem_Z2`, `cupCochain_mem_B2` — the cupping `c ⌣ n` on
  continuous `2`-cochains, well defined modulo coboundaries;
* `alphaZero` — `H⁰(G,Hom_ℤ(N,C)) →+ (H²(G,N) →+ H²(G,C))` (`= mapH2` of the coefficient map);
* `alphaTwo` — `H²(G,Hom_ℤ(N,C)) →+ (N^G →+ H²(G,C))`, with computation rule `alphaTwo_H2π`.

Delegated and proved (files in `Submission/Work/SSGRoute/PT/`):

* `isDiscreteModule_conjHom` — `Hom_ℤ(N,C)` is a discrete `G`-module for finite `N` and discrete
  `C` (needed for the long exact sequence);
* `alphaTwo_naturality` — the contravariance square in `N`: precomposition with an equivariant
  `φ : N₁ →+ N₂` on the `H²` side against `invariantsHom φ` on the `H⁰` side; this is the commuting
  square that the five-lemma dévissage reads off the long exact sequence;
* `alphaTwo_evalHom` — `alphaTwo x n = mapH2 (evalHom n) _ x`: cupping *is* applying the coefficient
  map `ev_n`.

Still to build for the target, in order:

1. `Work.SSGRoute.PT.shortExactSeq_conjHom` — the short exact sequence
   `0 → Hom_ℤ(N'',C) → Hom_ℤ(N,C) → Hom_ℤ(N',C) → 0` of coefficient modules for `C = Additive Ωˣ`
   (`Ω` algebraically closed), its exactness being the divisibility of `Ωˣ`
   (`Work.SSGRoute.PT.exists_addHom_extend_addUnits`);
2. the long exact sequence `… → H²(Hom(N',C)) → H²(Hom(N,C)) → H²(Hom(N'',C)) → H³(Hom(N',C))`
   from `Work.AbsoluteKummer.SES` (`deltaH2` and its exactness), together with `H³(G,M) = 0` for
   finite `M` ("`cd_p(G_{k_v}) ≤ 2`", available as hypotheses on `H3loc`);
3. the **five-lemma dévissage** comparing that sequence with the `H⁰(N)^∨` sequence through
   `alphaTwo_naturality`: with `Ext^r_G(N,C) = H^r(G, Hom_ℤ(N,C))` (Milne (0.8), valid because `C`
   is divisible), `α²` bijective for `N'` and `N''` and `H³(G,·) = 0` imply `α²(N)` bijective;
4. the **trivial-action base case** (`N` with trivial `G`-action), i.e. Milne's (1.7)/(1.1b): the
   invariant map `H²(U, \bar k_v^×) ≅ ℚ/ℤ` (the local Brauer group `= ℚ/ℤ`).  The workspace has the
   finite-level fundamental class (`NK.LocalCFT…`, `Commons.NumberTheory.NumberField.Completion…`)
   but not its limit over the open subgroups;
5. instantiate at `N = M^∨(1) = DualMod p (M ⊗ T)` using the twist cancellation
   `Hom_ℤ(E^∨(1), Ωˣ) ≅ E` (`Work.SSGRoute.hom_dualMod_local_units`) to obtain
   `Work.SSGRoute.PT.Milne18AtZero`, and conclude the target with
   `Work.SSGRoute.PT.localTatePairing_deg02_of_milne18`.

**Where the remaining obstruction actually lies.**  Steps 3 and 4 both need the *invariant map*
`inv_U : H²(U, \bar k_v^×) → ℚ/ℤ` even to *state* Milne's conclusion: the pairing delivered by `α²` is
`H²(G, Hom_ℤ(N,C)) × N^G → H²(G,C)`, and its perfectness means that the composite with
`inv_G` is an isomorphism `H²(G, Hom_ℤ(N,C)) ≅ (N^G)^∨`.  So the group-theoretic scaffolding —
this file, `alphaTwo_naturality`, `alphaTwo_evalHom`, `shortExactSeq_conjHom`, and the generic long
exact sequence of `Work.AbsoluteKummer.SES` applied to the latter — is complete up to the point at
which the arithmetic of the class formation `(G_{k_v}, \bar k_v^×)` enters.  Of the two class-formation
axioms, (1.1a) `H¹(U, \bar k_v^×) = 0` is *proved* here
(`Work.SSGRoute.PT.hilbert90_H1_eq_zero_openSubgroup`); (1.1b) — the invariant map, i.e.
`Br(k_v) = ℚ/ℤ` — is the one remaining external input.  The `M`-generic dimension form of the target
does not mention `ℚ/ℤ`, so an independent route to it is not excluded; what is available is the
finite-level fundamental class (`NK.LocalCFT…`, `Commons.NumberTheory.NumberField.Completion…`),
and what is missing is its limit over the open subgroups (Milne's Lemma 1.9 argument with the
*modified* direct system whose transition maps are `(U:V)·Inf`).
-/

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option maxHeartbeats 1000000

open Classical

namespace Work.SSGRoute.PT

universe u v w

/-! ## The coefficient module `Hom_ℤ(N,C)` with the conjugation action -/

/-- The additive group of additive homomorphisms `N →+ C`, as a *copy* of `N →+ C` so that it can
be endowed with the conjugation action of `G` (rather than the pointwise action that Mathlib gives
`N →+ C`). -/
structure ConjHom (N : Type v) (C : Type w) [AddCommGroup N] [AddCommGroup C] where
  /-- The underlying additive homomorphism. -/
  toHom : N →+ C

namespace ConjHom

variable {G : Type u} [Group G] {N : Type v} [AddCommGroup N] [DistribMulAction G N]
  {C : Type w} [AddCommGroup C] [DistribMulAction G C]

instance : FunLike (ConjHom N C) N C where
  coe f := f.toHom
  coe_injective := by
    intro f g h
    obtain ⟨f⟩ := f
    obtain ⟨g⟩ := g
    exact congrArg ConjHom.mk (AddMonoidHom.ext (funext_iff.mp h))

instance : AddMonoidHomClass (ConjHom N C) N C where
  map_add f := f.toHom.map_add
  map_zero f := f.toHom.map_zero

@[ext] theorem ext_apply {f g : ConjHom N C} (h : ∀ n, f n = g n) : f = g := by
  obtain ⟨f⟩ := f
  obtain ⟨g⟩ := g
  exact congrArg ConjHom.mk (AddMonoidHom.ext h)

instance : Zero (ConjHom N C) := ⟨⟨0⟩⟩
instance : Add (ConjHom N C) := ⟨fun f g => ⟨f.toHom + g.toHom⟩⟩
instance : Neg (ConjHom N C) := ⟨fun f => ⟨-f.toHom⟩⟩
instance : Sub (ConjHom N C) := ⟨fun f g => ⟨f.toHom - g.toHom⟩⟩
instance : SMul ℕ (ConjHom N C) := ⟨fun k f => ⟨k • f.toHom⟩⟩
instance : SMul ℤ (ConjHom N C) := ⟨fun k f => ⟨k • f.toHom⟩⟩

instance : AddCommGroup (ConjHom N C) :=
  Function.Injective.addCommGroup (fun f : ConjHom N C => f.toHom)
    (fun f g h => by
      obtain ⟨f⟩ := f
      obtain ⟨g⟩ := g
      exact congrArg ConjHom.mk h)
    rfl (fun _ _ => rfl) (fun _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)

@[simp] theorem toHom_zero : (0 : ConjHom N C).toHom = 0 := rfl
@[simp] theorem toHom_add (f g : ConjHom N C) : (f + g).toHom = f.toHom + g.toHom := rfl
@[simp] theorem toHom_neg (f : ConjHom N C) : (-f).toHom = -f.toHom := rfl
@[simp] theorem toHom_sub (f g : ConjHom N C) : (f - g).toHom = f.toHom - g.toHom := rfl
@[simp] theorem zero_apply (n : N) : (0 : ConjHom N C) n = 0 := rfl
@[simp] theorem add_apply (f g : ConjHom N C) (n : N) : (f + g) n = f n + g n := rfl
@[simp] theorem neg_apply (f : ConjHom N C) (n : N) : (-f) n = -(f n) := rfl
@[simp] theorem sub_apply (f g : ConjHom N C) (n : N) : (f - g) n = f n - g n := rfl

/-- The conjugation action of `G` on `Hom_ℤ(N,C)`: `(g • f)(n) = g • f (g⁻¹ • n)`. -/
def smul (g : G) (f : ConjHom N C) : ConjHom N C :=
  ⟨{ toFun := fun n => g • f (g⁻¹ • n)
     map_zero' := by simp
     map_add' m n := by simp only [map_add, smul_add] }⟩

instance : SMul G (ConjHom N C) := ⟨smul⟩

@[simp] theorem smul_apply (g : G) (f : ConjHom N C) (n : N) :
    (g • f) n = g • f (g⁻¹ • n) := rfl

instance : DistribMulAction G (ConjHom N C) where
  one_smul f := by ext n; simp [smul_apply]
  mul_smul g h f := by
    ext n
    simp only [smul_apply, mul_inv_rev]
    rw [mul_smul h⁻¹ g⁻¹ n, ← mul_smul g h]
  smul_zero g := by ext n; simp [smul_apply]
  smul_add g f f' := by ext n; simp [smul_apply, add_apply, smul_add]

end ConjHom

/-! ## The `α`-maps -/

section Pairing

variable {G : Type u} [TopologicalSpace G] [Group G]
  {N : Type v} [AddCommGroup N] [DistribMulAction G N]
  {C : Type w} [AddCommGroup C] [DistribMulAction G C]

/-- An invariant element of `Hom_ℤ(N,C)` is `G`-equivariant: the conjugation action has
`H⁰(G, Hom_ℤ(N,C)) = Hom_G(N,C)`. -/
theorem isEquivariant_toHom_of_mem_invariants (f : ConjHom N C)
    (hf : f ∈ Work.GroupCohomology.invariants G (ConjHom N C)) :
    Work.GroupCohomology.IsEquivariant G f.toHom := by
  intro g n
  have h := congrArg (fun φ : ConjHom N C => φ n) (hf g⁻¹)
  simp only [ConjHom.smul_apply, inv_inv] at h
  have h2 := congrArg (fun x : C => g • x) h
  rw [smul_inv_smul] at h2
  exact h2

/-- The `α⁰`-map: an invariant (i.e. `G`-equivariant) `f : Hom_ℤ(N,C)` acts on cohomology by
composition, `x ↦ f ∘ x`. -/
noncomputable def alphaZero (f : ↥(Work.GroupCohomology.invariants G (ConjHom N C))) :
    Work.AbsoluteKummer.H2 G N →+ Work.AbsoluteKummer.H2 G C :=
  Work.AbsoluteKummer.mapH2 f.1.toHom (isEquivariant_toHom_of_mem_invariants f.1 f.2)

/-- The `2`-cochain `c ⌣ n : G × G → C` attached to a `2`-cochain `c` with values in
`Hom_ℤ(N,C)` and an element `n : N`: `(c ⌣ n)(g,h) = c(g,h)(n)`. -/
def cupCochain (c : G × G → ConjHom N C) (n : N) : G × G → C := fun p => c p n

@[simp] theorem cupCochain_zero (n : N) :
    cupCochain (0 : G × G → ConjHom N C) n = 0 := by
  funext p; simp [cupCochain]

@[simp] theorem cupCochain_add_left (c d : G × G → ConjHom N C) (n : N) :
    cupCochain (c + d) n = cupCochain c n + cupCochain d n := by
  funext p; simp [cupCochain]

@[simp] theorem cupCochain_add_right (c : G × G → ConjHom N C) (n m : N) :
    cupCochain c (n + m) = cupCochain c n + cupCochain c m := by
  funext p; simp [cupCochain]

theorem isLocallyConstant_cupCochain {c : G × G → ConjHom N C}
    (hc : Work.AbsoluteKummer.IsLocallyConstant c) (n : N) :
    Work.AbsoluteKummer.IsLocallyConstant (cupCochain c n) :=
  hc.map (fun f => f n)

/-- **The cocycle identity for `c ⌣ n`.**  If `c` is a `2`-cocycle with values in `Hom_ℤ(N,C)`
(for the conjugation action) and `n ∈ N^G`, then `c ⌣ n` satisfies the `2`-cocycle identity with
values in `C`. -/
theorem cupCochain_add_eq (c : G × G → ConjHom N C)
    (hc : c ∈ Work.AbsoluteKummer.Z2 G (ConjHom N C)) (n : N)
    (hn : n ∈ Work.GroupCohomology.invariants G N) (g h k : G) :
    cupCochain c n (g * h, k) + cupCochain c n (g, h)
      = g • cupCochain c n (h, k) + cupCochain c n (g, h * k) := by
  have hcoc := congrArg (fun φ : ConjHom N C => φ n)
    (((Work.AbsoluteKummer.mem_Z2_iff c).mp hc).1 g h k)
  simp only [ConjHom.add_apply, map_add] at hcoc
  have hg : (g • c (h, k)) n = g • c (h, k) n := by
    rw [ConjHom.smul_apply, hn g⁻¹]
  simpa only [cupCochain, hg] using hcoc

/-- `c ⌣ n` is a continuous `2`-cocycle whenever `c` is one and `n ∈ N^G`. -/
theorem cupCochain_mem_Z2 {c : G × G → ConjHom N C}
    (hc : c ∈ Work.AbsoluteKummer.Z2 G (ConjHom N C))
    {n : N} (hn : n ∈ Work.GroupCohomology.invariants G N) :
    cupCochain c n ∈ Work.AbsoluteKummer.Z2 G C := by
  rw [Work.AbsoluteKummer.mem_Z2_iff]
  exact ⟨cupCochain_add_eq c hc n hn,
    isLocallyConstant_cupCochain ((Work.AbsoluteKummer.mem_Z2_iff c).mp hc).2 n⟩

/-- The coboundary of `b` cupped with `n` is the coboundary of `g ↦ b g n`: cupping descends to
cohomology. -/
theorem cupCochain_mem_B2 {c : G × G → ConjHom N C}
    (hc : c ∈ Work.AbsoluteKummer.B2 G (ConjHom N C))
    {n : N} (hn : n ∈ Work.GroupCohomology.invariants G N) :
    cupCochain c n ∈ Work.AbsoluteKummer.B2 G C := by
  obtain ⟨b, hb, rfl⟩ := (Work.AbsoluteKummer.mem_B2_iff c).mp hc
  have hb' : Work.AbsoluteKummer.IsLocallyConstant b :=
    (Work.AbsoluteKummer.mem_C1c_iff b).mp hb
  refine (Work.AbsoluteKummer.mem_B2_iff _).mpr
    ⟨fun g => b g n, (Work.AbsoluteKummer.mem_C1c_iff _).mpr (hb'.map (fun f => f n)), ?_⟩
  funext p
  obtain ⟨g, h⟩ := p
  have hg : (g • b h) n = g • b h n := by
    rw [ConjHom.smul_apply, hn g⁻¹]
  simp only [cupCochain, Work.GroupCohomology.d1_apply, ConjHom.sub_apply,
    ConjHom.add_apply, map_sub, map_add, hg]

/-- The cupped cocycle, packaged as an element of `Z²_c(G,C)`. -/
noncomputable def cupCochainZ2 (c : ↥(Work.AbsoluteKummer.Z2 G (ConjHom N C)))
    (n : ↥(Work.GroupCohomology.invariants G N)) : Work.AbsoluteKummer.Z2 G C :=
  ⟨cupCochain (c : G × G → ConjHom N C) (n : N), cupCochain_mem_Z2 c.2 n.2⟩

@[simp] theorem cupCochainZ2_zero (n : ↥(Work.GroupCohomology.invariants G N)) :
    cupCochainZ2 (0 : ↥(Work.AbsoluteKummer.Z2 G (ConjHom N C))) n = 0 :=
  Subtype.ext (cupCochain_zero (n : N))

theorem cupCochainZ2_add (c d : ↥(Work.AbsoluteKummer.Z2 G (ConjHom N C)))
    (n : ↥(Work.GroupCohomology.invariants G N)) :
    cupCochainZ2 (c + d) n = cupCochainZ2 c n + cupCochainZ2 d n :=
  Subtype.ext (by
    show cupCochain ((c : G × G → ConjHom N C) + (d : G × G → ConjHom N C)) (n : N) = _
    rw [cupCochain_add_left]
    rfl)

theorem cupCochainZ2_add_apply (c : ↥(Work.AbsoluteKummer.Z2 G (ConjHom N C)))
    (n m : ↥(Work.GroupCohomology.invariants G N)) :
    cupCochainZ2 c (n + m) = cupCochainZ2 c n + cupCochainZ2 c m :=
  Subtype.ext (by
    show cupCochain (c : G × G → ConjHom N C) ((n : N) + (m : N)) = _
    rw [cupCochain_add_right]
    rfl)

/-- The cupping `c ↦ (n ↦ c ⌣ n)` on cocycles. -/
noncomputable def alphaTwoFun (c : ↥(Work.AbsoluteKummer.Z2 G (ConjHom N C))) :
    ↥(Work.GroupCohomology.invariants G N) →+ Work.AbsoluteKummer.H2 G C :=
  AddMonoidHom.mk' (fun n => Work.AbsoluteKummer.H2π G C (cupCochainZ2 c n)) (by
    intro a b
    rw [← map_add, cupCochainZ2_add_apply])

/-- The cupping as an additive map in `c`. -/
noncomputable def alphaTwoZ :
    ↥(Work.AbsoluteKummer.Z2 G (ConjHom N C)) →+
      (↥(Work.GroupCohomology.invariants G N) →+ Work.AbsoluteKummer.H2 G C) where
  toFun := alphaTwoFun
  map_zero' := by
    ext n
    show Work.AbsoluteKummer.H2π G C
      (cupCochainZ2 (0 : ↥(Work.AbsoluteKummer.Z2 G (ConjHom N C))) n) = 0
    rw [cupCochainZ2_zero, map_zero]
  map_add' c d := by
    ext n
    show Work.AbsoluteKummer.H2π G C (cupCochainZ2 (c + d) n)
      = Work.AbsoluteKummer.H2π G C (cupCochainZ2 c n)
        + Work.AbsoluteKummer.H2π G C (cupCochainZ2 d n)
    rw [cupCochainZ2_add, map_add]

/-- **The `α²`-map**: cupping with the invariant elements of `N`,
`H²(G, Hom_ℤ(N,C)) →+ (N^G →+ H²(G,C))`. -/
noncomputable def alphaTwo :
    Work.AbsoluteKummer.H2 G (ConjHom N C) →+
      (↥(Work.GroupCohomology.invariants G N) →+ Work.AbsoluteKummer.H2 G C) :=
  QuotientAddGroup.lift
    ((Work.AbsoluteKummer.B2 G (ConjHom N C)).comap
      (Work.AbsoluteKummer.Z2 G (ConjHom N C)).subtype) alphaTwoZ (by
    intro x hx
    have hx' : ((x : ↥(Work.AbsoluteKummer.Z2 G (ConjHom N C))) : G × G → ConjHom N C)
        ∈ Work.AbsoluteKummer.B2 G (ConjHom N C) :=
      AddSubgroup.mem_comap.mp hx
    ext n
    show Work.AbsoluteKummer.H2π G C (cupCochainZ2 x n) = 0
    rw [Work.AbsoluteKummer.H2π_eq_zero_iff]
    exact cupCochain_mem_B2 hx' n.2)

/-- The computation rule for `alphaTwo` on cocycles. -/
theorem alphaTwo_H2π (c : ↥(Work.AbsoluteKummer.Z2 G (ConjHom N C))) :
    alphaTwo (Work.AbsoluteKummer.H2π G (ConjHom N C) c) = alphaTwoZ c :=
  QuotientAddGroup.lift_mk' _ _ c

end Pairing

/-! ## Coefficient maps: precomposition, postcomposition, evaluation -/

section CoeffDefs

universe v' w'

namespace ConjHom

variable {N₂ : Type v} [AddCommGroup N₂] {C : Type w} [AddCommGroup C]

/-- Precomposition `f ↦ f ∘ φ` on `Hom_ℤ(-,C)`. -/
def precomp {N₁ : Type v'} [AddCommGroup N₁] (φ : N₁ →+ N₂) :
    ConjHom N₂ C →+ ConjHom N₁ C where
  toFun f := ⟨f.toHom.comp φ⟩
  map_zero' := congrArg ConjHom.mk (by
    show (0 : ConjHom N₂ C).toHom.comp φ = (0 : N₁ →+ C)
    rw [ConjHom.toHom_zero, AddMonoidHom.zero_comp])
  map_add' f f' := congrArg ConjHom.mk (by
    show (f + f').toHom.comp φ = f.toHom.comp φ + f'.toHom.comp φ
    rw [ConjHom.toHom_add, AddMonoidHom.add_comp])

@[simp] theorem precomp_apply {N₁ : Type v'} [AddCommGroup N₁] (φ : N₁ →+ N₂)
    (f : ConjHom N₂ C) (n : N₁) : precomp φ f n = f (φ n) := rfl

/-- Postcomposition `f ↦ ψ ∘ f` on `Hom_ℤ(N,-)`. -/
def postcomp {C' : Type w'} [AddCommGroup C'] (ψ : C →+ C') :
    ConjHom N₂ C →+ ConjHom N₂ C' where
  toFun f := ⟨ψ.comp f.toHom⟩
  map_zero' := congrArg ConjHom.mk (by
    show ψ.comp (0 : ConjHom N₂ C).toHom = (0 : N₂ →+ C')
    rw [ConjHom.toHom_zero, AddMonoidHom.comp_zero])
  map_add' f f' := congrArg ConjHom.mk (by
    show ψ.comp (f + f').toHom = ψ.comp f.toHom + ψ.comp f'.toHom
    rw [ConjHom.toHom_add, AddMonoidHom.comp_add])

@[simp] theorem postcomp_apply {C' : Type w'} [AddCommGroup C'] (ψ : C →+ C')
    (f : ConjHom N₂ C) (n : N₂) : postcomp ψ f n = ψ (f n) := rfl

/-- Evaluation `f ↦ f n` at an element of `N₂`. -/
def evalHom (n : N₂) : ConjHom N₂ C →+ C where
  toFun f := f n
  map_zero' := by simp
  map_add' f f' := by simp

@[simp] theorem evalHom_apply (n : N₂) (f : ConjHom N₂ C) : evalHom n f = f n := rfl

end ConjHom

end CoeffDefs

section CoeffEquiv

universe v' w'

variable {G : Type u} [Group G]
  {N₁ : Type v'} [AddCommGroup N₁] [DistribMulAction G N₁]
  {N₂ : Type v} [AddCommGroup N₂] [DistribMulAction G N₂]
  {C : Type w} [AddCommGroup C] [DistribMulAction G C]

/-- Precomposition with an equivariant map is equivariant. -/
theorem precomp_smul (φ : N₁ →+ N₂) (hφ : Work.GroupCohomology.IsEquivariant G φ) (g : G)
    (f : ConjHom N₂ C) :
    ConjHom.precomp φ (g • f) = g • ConjHom.precomp φ f := by
  ext n
  simp only [ConjHom.precomp_apply, ConjHom.smul_apply]
  rw [← hφ g⁻¹ n]

/-- Postcomposition with an equivariant map is equivariant. -/
theorem postcomp_smul {C' : Type w'} [AddCommGroup C'] [DistribMulAction G C']
    (ψ : C →+ C') (hψ : Work.GroupCohomology.IsEquivariant G ψ) (g : G)
    (f : ConjHom N₂ C) :
    ConjHom.postcomp ψ (g • f) = g • ConjHom.postcomp ψ f := by
  ext n
  simp only [ConjHom.postcomp_apply, ConjHom.smul_apply]
  exact hψ g (f (g⁻¹ • n))

/-- Evaluation at an invariant element is equivariant. -/
theorem evalHom_smul (n : N₂) (hn : n ∈ Work.GroupCohomology.invariants G N₂)
    (g : G) (f : ConjHom N₂ C) :
    ConjHom.evalHom n (g • f) = g • ConjHom.evalHom n f := by
  show (g • f) n = g • f n
  rw [ConjHom.smul_apply, hn g⁻¹]

end CoeffEquiv

section InvariantsMap

universe v'

variable {G : Type u} [Group G]
  {N₁ : Type v'} [AddCommGroup N₁] [DistribMulAction G N₁]
  {N₂ : Type v} [AddCommGroup N₂] [DistribMulAction G N₂]

/-- An equivariant map sends invariants to invariants. -/
theorem map_mem_invariants (φ : N₁ →+ N₂)
    (hφ : Work.GroupCohomology.IsEquivariant G φ) {n : N₁}
    (hn : n ∈ Work.GroupCohomology.invariants G N₁) :
    φ n ∈ Work.GroupCohomology.invariants G N₂ := by
  intro g
  rw [← hφ]
  exact congrArg φ (hn g)

/-- The map on invariants induced by an equivariant map. -/
noncomputable def invariantsHom (φ : N₁ →+ N₂)
    (hφ : Work.GroupCohomology.IsEquivariant G φ) :
    ↥(Work.GroupCohomology.invariants G N₁) →+
      ↥(Work.GroupCohomology.invariants G N₂) where
  toFun n := ⟨φ (n : N₁), map_mem_invariants φ hφ n.2⟩
  map_zero' := Subtype.ext (map_zero φ)
  map_add' a b := Subtype.ext (map_add φ (a : N₁) (b : N₁))

end InvariantsMap

end Work.SSGRoute.PT
