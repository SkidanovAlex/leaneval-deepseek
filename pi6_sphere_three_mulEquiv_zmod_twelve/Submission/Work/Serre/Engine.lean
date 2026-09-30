import Submission.Work.Serre.Basic
import Submission.Work.Serre.Models
import Submission.Work.StemsB.WangSphere
import Submission.Work.Stems.Cubical.CubeFace
import Submission.Work.StemsB.SerreFiltration
import Submission.Work.RatHurewicz.RelHomotopy
import Submission.Work.Cohomology.cupH

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# SUBPROJECT SERRE — the engine: E0 … E4 of the blueprint

`Submission/Work/Drive/SERRE_BLUEPRINT.md` §1.  Everything is over `ℚ` and uses the vocabulary of
`Submission/Work/Serre/Defs.lean`; the two-disc geometry and the Wang sequence of E4 are STEMSB's
(`Work.StemsB`), imported here.

## What is *proved* in this file and what is a contract

| label | name | status |
|---|---|---|
| E0 | `Work.Serre.SerreE0` | **contract** (the contractible case is proved: `ratAcyclic_of_contractible`) |
| E1 | `Work.Serre.serreE1_simplicial` | **proved** (the blueprint's allowed simplicial variant) |
| E2 | `Work.Serre.SerreE2` | **contract** (triviality over a cube) |
| E3(a) | `Work.Serre.SerreE3a` | **contract** (mapping theorem) |
| E3(b) | `Work.Serre.SerreE3b` | **contract** (Gysin / Euler class of a rational spherical fibration) |
| E4 | `Work.Serre.SerreE4` | **MOVED** to `Submission/Work/Serre/serreE4.lean` and **PROVED** there (`Work.Serre.serreE4`, imported from area STEMSB's route-B `Work.StemsB.wangSphereE4Rat`).  The statement that used to be defined here (transgression of degree `+(m-1)`) is FALSE — see `Submission/Work/StemsB/E4_CORRECTION.md`; the corrected statement indexes the transgression by its source degree. |
-/

open CategoryTheory CategoryTheory.Limits AlgebraicTopology
open scoped Topology unitInterval

namespace Work.Serre

noncomputable section

/-! ## E0 — weakly contractible spaces are acyclic -/

/-- **E0 (blueprint §1).**  A weakly contractible space is acyclic: if every homotopy group
`π_i(X,x₀)` (`π₀` included) is trivial then the unique map `X → *` is a rational homology
isomorphism.

The proof is the blueprint's: a singular cycle is carried by a finite simplicial set, every map
from a finite complex to `X` is null-homotopic (extend over the cone skeleton by skeleton), so the
cycle is a boundary.  Cf. `Work.Cohomology.homologyContractible_ring` for the contractible case,
which *is* proved (and used in `Submission/Work/Serre/Basic.lean`). -/
def SerreE0 : Prop :=
  ∀ (X : Type) [TopologicalSpace X] (x₀ : X), WeaklyContractible X x₀ → RatAcyclic X

/-- **E0, range form (blueprint ADDENDUM 1 (C)).**  The singular-cone construction gives the
range-limited statement directly: if `π_i(X,x₀) = 0` for `i ≤ N` then `H̃_j(X;ℚ) = 0` for
`0 < j ≤ N`.  (Given a cycle `z`, take the finite set of simplices of `z` and their iterated faces;
cone each simplex of dimension `k ≤ N` using `π_k(X) = 0`; the result is a bounding chain.  No CW
structure and no subdivision are needed, because the *domains* of the singular simplices are
simplices.) -/
def SerreE0Range : Prop :=
  ∀ (X : Type) [TopologicalSpace X] (x₀ : X) (N : ℕ),
    (∀ i : ℕ, i ≤ N → Subsingleton (HomotopyGroup (Fin i) X x₀)) → RatVanishingBelow X (N + 1)

/-- The unrestricted E0 follows from the range form together with the degree-`0` statement that
the augmentation `H₀(X;ℚ) → H₀(*;ℚ)` is an isomorphism for connected `X` (the one place where the
reduced homology `RatAcyclic` needs more than the vanishing of `H_t` for `t > 0`). -/
def SerreE0OfRange : Prop := SerreE0Range →
  (∀ (X : Type) [TopologicalSpace X] (x₀ : X),
    Subsingleton (HomotopyGroup (Fin 0) X x₀) → IsIso (ratHomologyMap (toPoint X) 0)) → SerreE0

/-- The contractible case of E0 is immediate from homotopy invariance — this is
`Work.Serre.ratAcyclic_of_contractible`, restated in the shape of the contract. -/
theorem serreE0_of_contractible :
    ∀ (X : Type) [TopologicalSpace X] [ContractibleSpace X], RatAcyclic X :=
  fun X _ _ => ratAcyclic_of_contractible X

/-- **E0 gives the acyclicity of the homotopy fibre**, in the form used by E3(a). -/
theorem ratAcyclic_homotopyFibre_of_weaklyContractible (h : SerreE0)
    {E B : Type} [TopologicalSpace E] [TopologicalSpace B] (p : C(E, B)) (e₀ : E)
    (hX : WeaklyContractible (Work.RatHurewicz.homotopyFibre p e₀)
      (Work.RatHurewicz.homotopyFibreBasepoint p e₀)) :
    RatAcyclic (Work.RatHurewicz.homotopyFibre p e₀) :=
  h _ _ hX

/-! ## E1 — the Serre filtration in its simplicial form

The blueprint allows the *simplicial* variant of the filtration instead of the cubical one
("Alternative, if cheaper: do E2 with simplicial chains filtered by the 'base dimension' of
`p∘σ`").  The workspace's singular chains (`Work.Cohomology.singularChains`) are simplicial, so no
comparison theorem (cubical ≅ simplicial) is needed: the filtration is the one of
`Submission/Work/StemsB/SerreFiltration.lean`, and its content — exhaustiveness and monotonicity —
is proved there.  We record the exhaustiveness here as the E1 entry. -/

/-- **E1 (simplicial form).**  The Serre filtration of the singular simplicial complex of `E` along
`Sing p` is exhaustive: every simplex lies in some filtration level.  (This is
`Work.StemsB.iSup_serreSubcomplex`, together with `Work.StemsB.serreSubcomplex_mono`, the whole
filtration input of the degeneration argument.) -/
theorem serreE1_simplicial {X Y : SSet} (f : X ⟶ Y) :
    (⨆ P : ℕ, Work.StemsB.serreSubcomplex f P) = ⊤ :=
  Work.StemsB.iSup_serreSubcomplex f

/-- Monotonicity of the Serre filtration, the other half of E1. -/
theorem serreE1_mono {X Y : SSet} (f : X ⟶ Y) : Monotone (Work.StemsB.serreSubcomplex f) :=
  Work.StemsB.serreSubcomplex_mono f

/-! ## E2 — the `E¹` page, in the form prescribed by the lead's ADDENDUM 1

The blueprint's E2 asked for **fibre-homotopy triviality** of a Serre fibration over a cube
(`Work.StemsB.FibrewiseTrivial`, homotopies over the base).  *That statement is not the right
target*: it needs the HLP with respect to test spaces such as `F × I`, which a Serre fibration does
not provide (only cubes), and the fibres of a Serre fibration are in general only weakly
equivalent.  The lead's ADDENDUM 1 replaces it by the four statements below, all of which use cubes
only.  Everything downstream (E1, E3(a), E3(b), E4) consumes only *homology*.
-/

/-- The **hat** of the cube-cylinder, `Iⁿ × 0 ∪ ∂Iⁿ × I ⊆ Iⁿ × I`: the subcomplex on which the
partial lift of the relative HLP is prescribed. -/
def hatSet (n : ℕ) : Set (Work.Stems.Cubical.IC n × unitInterval) :=
  {x | x.2 = 0} ∪ {x | x.1 ∈ Cube.boundary (Fin n)}

/-- The inclusion `Iⁿ × 0 ∪ ∂Iⁿ × I → Iⁿ × I`. -/
def hatIncl (n : ℕ) : C(↥(hatSet n), Work.Stems.Cubical.IC n × unitInterval) :=
  ⟨Subtype.val, continuous_subtype_val⟩

/-- **E2(a): the relative cube HLP of a Serre fibration.**  A Serre fibration lifts homotopies of
the pair `(Iⁿ × I, Iⁿ × 0 ∪ ∂Iⁿ × I)`: a lift of the homotopy already given on
`Iⁿ × 0 ∪ ∂Iⁿ × I` extends to all of `Iⁿ × I`.  This is the statement whose proof is the standard
trick — the pair `(Iⁿ × I, Iⁿ × 0 ∪ ∂Iⁿ × I)` is homeomorphic to `(Iⁿ × I, Iⁿ × 0)` by radial
projection from `(½,…,½,2)`, after which the absolute cube HLP applies.

(`Iⁿ × 0` is part of the prescribed data: without it the statement is *false*, e.g. for the
constant map `S¹ → *`, where two lifts which disagree on the two ends of `I × 0` would exhibit a
homotopy between non-homotopic loops.  With `Iⁿ × 0` included, the case `n = 0` is the ordinary
path-lifting property, which Serre fibrations have.) -/
def SerreE2a : Prop :=
  ∀ (E B : Type) [TopologicalSpace E] [TopologicalSpace B] (p : C(E, B)) (n : ℕ),
    Work.StemsB.IsSerreFibration p →
      ∀ (H : C(Work.Stems.Cubical.IC n × unitInterval, B))
        (g : C(↥(hatSet n), E))
        (_hg : p.comp g = H.comp (hatIncl n)),
        ∃ G : C(Work.Stems.Cubical.IC n × unitInterval, E),
          p.comp G = H ∧ ∀ x : ↥(hatSet n), G (hatIncl n x) = g x

/-- **E2(b): compression implies vanishing of relative homology.**  If `A ⊆ X` and every map
`(Iⁿ, ∂Iⁿ) → (X, A)` is homotopic to a map into `A` relative to `∂Iⁿ` (for all `n ≤ N`), then
`H_n(X, A) = 0` for `n ≤ N`.  Proof: the *relative* singular cone construction of ADDENDUM 1 (C)
— deform singular simplices into `A` skeleton by skeleton, compatibly with faces.

`SerreE0Rel` is the same statement (it is the reusable cone step of E0); E0 is its special case
`A = {x₀}`. -/
def SerreE2b : Prop :=
  ∀ (X : Type) [TopologicalSpace X] (A : Set X) (N : ℕ),
    (∀ (n : ℕ), n ≤ N →
      ∀ f : C(Work.Stems.Cubical.IC n, X),
        (∀ t : Work.Stems.Cubical.IC n, t ∈ Cube.boundary (Fin n) → f t ∈ A) →
        ∃ g : C(Work.Stems.Cubical.IC n, X),
          (∀ t : Work.Stems.Cubical.IC n, g t ∈ A) ∧
            ContinuousMap.HomotopicRel f g (Cube.boundary (Fin n))) →
    ∀ n : ℕ, n ≤ N →
      IsZero ((Work.Cohomology.relChains (TopCat.of X) A).homology n)

/-- The relative form of E0 (ADDENDUM 1 (C)); equal to `SerreE2b` by definition. -/
def SerreE0Rel : Prop := SerreE2b

/-- **E2(c): the fibre of a Serre fibration over a cube is relatively acyclic.**  For
`τ : Iⁿ → B` and `d₀ : Iⁿ`, the pair `(τ^*E, F_{d₀})` has vanishing homology: `d₀` is a
deformation retract of `Iⁿ` by a straight-line contraction, which lifts (E2(a)) relative to the
boundary, and E2(b) applies. -/
def SerreE2c : Prop :=
  ∀ (E B : Type) [TopologicalSpace E] [TopologicalSpace B] (p : C(E, B)) (n : ℕ),
    Work.StemsB.IsSerreFibration p →
      ∀ (τ : C(Work.Stems.Cubical.IC n, B)) (d₀ : Work.Stems.Cubical.IC n),
        ∀ k : ℕ, IsZero ((Work.Cohomology.relChains (TopCat.of (Work.StemsB.Pullback p τ))
          {x | Work.StemsB.pullbackSnd p τ x = d₀}).homology k)

/-- **E2(d): the `E¹` page of the Serre filtration.**  `H_{k+n}(τ^*E, τ^*E|_{∂Iⁿ}) ≅ H_k(F_{d₀})`:
induction on `n`, using the triple `(τ^*E, τ^*E|_{∂Iⁿ}, τ^*E|_D)` for `D` the boundary minus the
open top face (a contractible closed `(n-1)`-disc), E2(c) for the two identifications with the
fibre, excision for a collar of the top face, and the `n-1` case. -/
def SerreE2d : Prop :=
  ∀ (E B : Type) [TopologicalSpace E] [TopologicalSpace B] (p : C(E, B)) (n : ℕ),
    Work.StemsB.IsSerreFibration p →
      ∀ (τ : C(Work.Stems.Cubical.IC n, B)) (d₀ : Work.Stems.Cubical.IC n),
        ∀ k : ℕ,
          Nonempty (((Work.Cohomology.relChains (TopCat.of (Work.StemsB.Pullback p τ))
            {x | Work.StemsB.pullbackSnd p τ x ∈ Cube.boundary (Fin n)}).homology (k + n)) ≅
            ((Work.Cohomology.singularChains ℤ
              (TopCat.of (Work.StemsB.fibre p (τ d₀)))).homology k))

/-! ## K2 — range-weak-equivalences induce homology isomorphisms (blueprint ADDENDUM 2)

This is the E2b cone construction with a range, applied to the mapping cylinder of a map.  It is the
tool that turns "the cell step is an isomorphism" into "`p` is a homology isomorphism in a range".
-/

/-- **`X` is rationally acyclic in degrees `≤ N`**: `H_t(X;ℚ) = 0` for `0 < t ≤ N` and
`H_0(X;ℚ) ≅ ℚ` (so `X` is rationally connected, which is what the cell step at `Γ₀ = pt` needs). -/
def RatAcyclicBelow (X : Type) [TopologicalSpace X] (N : ℕ) : Prop :=
  (∀ t : ℕ, 0 < t → t ≤ N → IsZero (ratH (TopCat.of X) t)) ∧
    IsIso (ratHomologyMap (toPoint X) 0)

/-- **K2 (blueprint ADDENDUM 2).**  An `N`-connected map induces an isomorphism on rational
homology in degrees `< N`: replace `f : X → Y` by the inclusion of `X` into its mapping cylinder
(a homotopy equivalence), observe that the relative homotopy groups `π_i(M_f, X)` vanish for
`i ≤ N`, apply `SerreE2b` (the relative cone construction, **proved** in this directory as
`Work.Serre.serreE2b`) to the pair `(M_f, X)`, and read off the conclusion from the long exact
sequence of the pair. -/
def SerreK2 : Prop :=
  ∀ (X Y : Type) [TopologicalSpace X] [TopologicalSpace Y] [Nonempty X] (f : C(X, Y)) (N : ℕ),
    (∀ (i : ℕ), i < N → ∀ x₀ : X, Function.Bijective (piMapN f i x₀)) →
      ∀ i : ℕ, i < N → IsIso (ratHomologyMap f i)

/-! ## E3(a) — the mapping theorem, in the range form of ADDENDUM 2 -/

/-- **E3(a) (blueprint §1, range form per ADDENDUM 2).**  If `p : E → B` is a Serre fibration and
the homotopy fibre over `e₀` is rationally acyclic in degrees `≤ N`, then `p` induces an
isomorphism on rational homology in degrees `< N`.

(Proof, per ADDENDUM 2: take a CW approximation `g : Γ → B` with `Γ` `N`-reduced
(RATHUREWICZ), pull `p` back along it, and induct on the skeleta of `Γ`: the cell step `K4` gives
`H_*(E|Γ_j, E|Γ_{j-1}) ≅ ⊕_α H_{*-j}(F_α)`, which maps isomorphically to `⊕_α H_{*-j}(pt)` in the
range because the fibres are rationally acyclic; the five lemma on the long exact sequences of the
pairs `(E|Γ_j, E|Γ_{j-1})` propagates the isomorphism from `Γ_{j-1}` to `Γ_j`, and `Γ_{<N}` is a
point.) -/
def SerreE3a : Prop :=
  ∀ (E B : Type) [TopologicalSpace E] [TopologicalSpace B] (p : C(E, B)) (e₀ : E) (N : ℕ),
    Work.StemsB.IsSerreFibration p → PathConnectedSpace B →
      RatAcyclicBelow (Work.RatHurewicz.homotopyFibre p e₀) N →
      ∀ i : ℕ, i < N → IsIso (ratHomologyMap p i)

/-- E3(a) in its absolute (range `= ∞`) shape: a fibration with a rationally acyclic homotopy
fibre over a path-connected base is a rational homology isomorphism.  Obtained from `SerreE3a` by
taking all `N` (and `RatAcyclic → RatAcyclicBelow N`). -/
def SerreE3aAll : Prop :=
  ∀ (E B : Type) [TopologicalSpace E] [TopologicalSpace B] (p : C(E, B)) (e₀ : E),
    Work.StemsB.IsSerreFibration p → PathConnectedSpace B →
      RatAcyclic (Work.RatHurewicz.homotopyFibre p e₀) → IsRatHomologyIso p

/-- `RatAcyclic X` implies `RatAcyclicBelow X N` for every `N`. -/
theorem RatAcyclic.ratAcyclicBelow {X : Type} [TopologicalSpace X] (h : RatAcyclic X) (N : ℕ) :
    RatAcyclicBelow X N :=
  ⟨fun _ ht _ => h.isZero_ratH ht, h 0⟩

/-- The range form of E3(a) implies the absolute form. -/
theorem serreE3aAll_of_range (h : SerreE3a) : SerreE3aAll :=
  fun E B _ _ p e₀ hp hB hacyc i =>
    h E B p e₀ (i + 1) hp hB (RatAcyclic.ratAcyclicBelow hacyc (i + 1)) i (by omega)

/-! ## Cohomology with rational coefficients, the cup product, and derivations -/

/-- Rational singular cohomology `H^n(X;ℚ)`, as the cohomology of the cochain complex of the
singular simplicial set of `X`. -/
abbrev ratCoh (X : TopCat) (n : ℕ) : ModuleCat ℚ :=
  (Work.Cohomology.SSetCochainComplex ℚ (TopCat.toSSet.obj X)).homology n

/-- The cup product on rational singular cohomology (`Work.Cohomology.cupH`). -/
noncomputable def ratCup (X : TopCat) (n m : ℕ) :
    ratCoh X n →ₗ[ℚ] ratCoh X m →ₗ[ℚ] ratCoh X (n + m) :=
  (Classical.choose (Work.Cohomology.cupH ℚ (TopCat.toSSet.obj X))) n m

/-- Cup product with a fixed class `e`. -/
noncomputable def cupWith (X : TopCat) (d : ℕ) (e : ratCoh X d) (n : ℕ) :
    ratCoh X n →ₗ[ℚ] ratCoh X (n + d) :=
  (ratCup X n d).flip e

/-- **The (Koszul-signed) derivation property** of a degree-`d` map of the graded rational
cohomology ring: `θ(a ⌣ b) = θ(a) ⌣ b + (-1)^{d·|a|} a ⌣ θ(b)`. -/
def IsDerivation (X : TopCat) (d : ℕ)
    (θ : ∀ q : ℕ, ratCoh X q →ₗ[ℚ] ratCoh X (q + d)) : Prop :=
  ∀ (q q' : ℕ) (a : ratCoh X q) (b : ratCoh X q'),
    θ (q + q') (ratCup X q q' a b) =
      cast (by rw [show (q + d) + q' = (q + q') + d from by omega]) (ratCup X (q + d) q' (θ q a) b) +
        ((-1 : ℚ) ^ (d * q)) • cast (by rw [show q + (q' + d) = (q + q') + d from by omega]) (ratCup X q (q' + d) a (θ q' b))

/-- **E3(b) (blueprint §1, in the range form of ADDENDUM 3).**  *Gysin / Euler class of a rational
spherical fibration.*  Let `p : E → B` be a Serre fibration with `E` rationally acyclic, `B` simply
connected, and the homotopy fibre over `e₀` rationally a sphere of dimension `r ≥ 1` **with vanishing
of the reduced homology only up to a range `N`** (`H̃_t(F;ℚ) = 0` for `0 < t ≤ N`, `t ≠ r`, and
`H_r(F;ℚ) ≅ ℚ`).  Then there is a class `e ∈ H^{r+1}(B;ℚ)` — the Euler class — such that
`x ↦ x ⌣ e` is an isomorphism `H^m(B;ℚ) ≅ H^{m+r+1}(B;ℚ)` for every `m` with `m + r + 1 ≤ N + 1`.

**The range is set by the fibre, not by the base** (ADDENDUM 3, correcting the earlier "`m < b`"):
the Gysin sequence is the long exact sequence of the pair `(M_p, E)` read through the Thom
identification, and both `H^{m}(B)` and `H^{m+r+1}(B)` are controlled by the cell step, whose input
is the fibre's vanishing up to `N`.  In the path–loop case this is
`⌣e : H^m(B) ≅ H^{m+r+1}(B)` for `m + r + 1 ≤ N + 1`, i.e. `H^*(B;ℚ) = ℚ[x]`, `|x| = r+1`, through
degree `N + 1`.

Simplicity of `B` is needed (with only path-connectedness the local system `H^r(F;ℚ)` can be
non-trivial — e.g. the `S²`-bundle over `ℝP^∞` with monodromy `-1` — and the Euler class then lives
in twisted cohomology). -/
def SerreE3b : Prop :=
  ∀ (E B : Type) [TopologicalSpace E] [TopologicalSpace B] (p : C(E, B)) (e₀ : E) (r N : ℕ),
    1 ≤ r → Work.StemsB.IsSerreFibration p → SimplyConnectedSpace B → RatAcyclic E →
      (∀ t : ℕ, 0 < t → t ≠ r → t ≤ N →
        IsZero (ratH (TopCat.of (Work.RatHurewicz.homotopyFibre p e₀)) t)) →
      Nonempty (ratH (TopCat.of (Work.RatHurewicz.homotopyFibre p e₀)) r ≅ ModuleCat.of ℚ ℚ) →
      ∀ m : ℕ, m + r + 1 ≤ N + 1 →
        ∃ e : ratCoh (TopCat.of B) (r + 1),
          IsIso (ModuleCat.ofHom (cupWith (TopCat.of B) (r + 1) e m))

/-! ## E4 — the Wang sequence and the derivation property

**E4 MOVED, AND ITS OLD STATEMENT HERE WAS FALSE.**  The statement that used to be declared in this
file asked for a transgression of degree `+(m-1)`, i.e. `θ q : H^q(F) → H^{q+(m-1)}(F)`, together
with the two exactness spots `im α_q = ker θ_q` and `im θ_q = ker β_q`.  It is refuted by the Hopf
fibration `S³ → S²`: `H⁰(S¹) = H¹(S¹) = ℚ` and `H^*(S³) = ℚ` in degrees `0, 3`, so the exactness
spots at `q = 0` and `q = 1` force `α_0 = 0` (from `im α_0 = ker θ_0 = 0`) *and* `ker θ_1 = 0`,
while `θ_1 : ℚ → H²(S¹) = 0` is zero.  Full computation:
`Submission/Work/StemsB/E4_CORRECTION.md`.

The corrected statement — the transgression indexed by its **source** degree,
`θ n : H^{n+m}(F) → H^{n+1}(F)`, which is the classical Wang sequence
`… → H^q(E) → H^q(F) --θ--> H^{q-m+1}(F) → H^{q+1}(E) → …` at `q = n + m` — is
`Work.Serre.SerreE4`, defined and **proved** in `Submission/Work/Serre/serreE4.lean` (module
`Submission.Work.Serre.serreE4`), by importing area STEMSB's route-B theorem
`Work.StemsB.wangSphereE4Rat` (the two-disc/collar Wang argument).  It is not declared in this
file because its conclusion is phrased in the *shifted* vocabulary of `Work.StemsB`
(`wangCohShiftθR`, `WangCohShiftDerivationR`, `wangCohFsp`) rather than in this file's unshifted
`ratCoh`/`IsDerivation` one.

`IsDerivation` above remains the generic degree-`+d` Koszul-derivation predicate (used by callers
who want to state a derivation in this chapter's vocabulary). -/

end

end Work.Serre
