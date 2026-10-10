import Mathlib.GroupTheory.QuotientGroup.Defs
import Mathlib.Topology.Defs.Basic
import Mathlib.Algebra.Group.Subgroup.Basic
import Mathlib.Algebra.GroupWithZero.Action.Defs
import Submission.Work.AbsoluteKummer.Functoriality
import Submission.Work.SSGRoute.PT.alphaTwo_naturality
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END
/-!
# Renamed copy of `PT/AlphaTwoDevissage.lean` (name collision with `PT/AlphaTwoKummer.lean`)

`PT/AlphaTwoDevissage.lean` and `PT/AlphaTwoKummer.lean` both declare
`Work.SSGRoute.PT.mapH2_comp`, so no module can import both; this file is the *verbatim* copy of
`PT/AlphaTwoDevissage.lean` with that one declaration (and its single use) renamed to
`mapH2_compAux`, so that the dévissage of Milne I.1.8 can be co-imported with the Kummer base case
(`PT/AlphaTwoTrivModSurj.lean`, `PT/alphaTwo_trivAction_of_trivMod.lean`).
-/


/-!
# The four-lemma dévissage of Milne I.1.8 for the `α²`-pairing

The abstract dévissage step of Milne's Theorem I.1.8 (*Arithmetic Duality Theorems*) in the
coefficient model of `PT/AlphaPairing.lean`.

Milne embeds a finite `G`-module `N` into the coinduced module `N* = Coind_U^G N` (for an open
normal `U ≤ G` acting trivially on `N`),

  `0 → N → N* → N₁ → 0`,

and compares the two sides of the pairing `α²(-,C): Ext²_G(-,C) → H⁰(G,-)^∨` by the four lemma.
Since `Hom_ℤ(-,C)` is exact (`C` divisible), `Ext²_G(N,C) = H²(G, Hom_ℤ(N,C))` and everything
happens in *coefficient* cohomology.

The two halves:

* **surjectivity** (`alphaTwo_surjective_of_precomp`): `α²(N*)` surjective implies `α²(N)`
  surjective — needs *no* extra input beyond the naturality square `alphaTwo_naturality` and the
  (free) surjectivity of the dual of `N^G ↪ (N*)^G`;
* **injectivity** (`alphaTwo_injective_of_precomp`): needs `Ext²(N*,C) → Ext²(N,C)` surjective,
  i.e. `Ext³_G(N₁,C) = 0`, and `α²(N₁)` surjective (the *second pass* of Milne's argument).

## Reference

Milne, *Arithmetic Duality Theorems*, Theorem I.1.8 (diagram (1.9.1) and its two passes).
-/

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option maxHeartbeats 1000000

open Classical

namespace Work.SSGRoute.PT

universe u v w w'

/-! ## Elementary diagram lemmas -/

/-- Composition as an additive homomorphism `(M →+ X) →+ (L →+ X)`, `ψ ↦ ψ ∘ f`. -/
def precompHom {L M X : Type*} [AddCommGroup L] [AddCommGroup M] [AddCommGroup X]
    (f : L →+ M) : (M →+ X) →+ (L →+ X) where
  toFun ψ := ψ.comp f
  map_zero' := by ext x; rfl
  map_add' ψ χ := by ext x; rfl

@[simp] theorem precompHom_apply {L M X : Type*} [AddCommGroup L] [AddCommGroup M]
    [AddCommGroup X] (f : L →+ M) (ψ : M →+ X) (x : L) :
    precompHom f ψ x = ψ (f x) := rfl

/-- **Four lemma, surjectivity half.**  In a commuting square whose rows are `A → B → C` and
`A' → B' → C'`, if the middle vertical map and the right-hand vertical map of the second row are
surjective, then the right-hand vertical map of the first row is surjective.  (No exactness.) -/
theorem four_lemma_surjective {A B C A' B' C' : Type*}
    [AddCommGroup A] [AddCommGroup B] [AddCommGroup C]
    [AddCommGroup A'] [AddCommGroup B'] [AddCommGroup C']
    (f : A →+ B) (g : B →+ C) (f' : A' →+ B') (g' : B' →+ C')
    (b : B →+ B') (c : C →+ C')
    (hbc : ∀ x, c (g x) = g' (b x))
    (hb : Function.Surjective b) (hg' : Function.Surjective g') :
    Function.Surjective c := by
  intro y
  obtain ⟨z, hz⟩ := hg' y
  obtain ⟨m, hm⟩ := hb z
  exact ⟨g m, by rw [hbc m, hm, hz]⟩

/-- **Three-column injectivity with the top map surjective.**  In a commutative ladder whose rows
are `A → B → C` and `A' → B' → C'`, if `g : B → C` is surjective, `g ∘ f = 0`,
`ker g' ≤ range f'`, `a` is surjective and `b` is injective, then `c` is injective.

The surjectivity of `g` is exactly what the vanishing of the next term of a long exact sequence
provides (`Ext³_G(N₁,C) = 0` in the `α²`-dévissage). -/
theorem three_lemma_injective {A B C A' B' C' : Type*}
    [AddCommGroup A] [AddCommGroup B] [AddCommGroup C]
    [AddCommGroup A'] [AddCommGroup B'] [AddCommGroup C']
    (f : A →+ B) (g : B →+ C) (f' : A' →+ B') (g' : B' →+ C')
    (a : A →+ A') (b : B →+ B') (c : C →+ C')
    (hfa : ∀ x, b (f x) = f' (a x)) (hgb : ∀ x, c (g x) = g' (b x))
    (hgf : g.comp f = 0) (hf'k' : g'.ker ≤ f'.range)
    (ha : Function.Surjective a) (hb : Function.Injective b) (hg : Function.Surjective g) :
    Function.Injective c := by
  intro x x' hxx'
  have h1 : c (x - x') = 0 := by rw [map_sub, hxx', sub_self]
  obtain ⟨y, hy⟩ := hg (x - x')
  have h5 : g' (b y) = 0 := by rw [← hgb y, hy]; exact h1
  have h6 : b y ∈ f'.range := hf'k' (AddMonoidHom.mem_ker.mpr h5)
  obtain ⟨z, hz⟩ := h6
  obtain ⟨w, hw⟩ := ha z
  have h7 : b y = b (f w) := by rw [hfa w, hw, hz]
  have h8 : y = f w := hb h7
  have h9 : g (f w) = 0 := by
    have := congrArg (fun (φ : A →+ C) => φ w) hgf
    simpa using this
  have h10 : x - x' = 0 := by rw [← hy, h8, h9]
  exact sub_eq_zero.mp h10

/-! ## The `α²`-dévissage -/

/-- Functoriality of `mapH2` at the level of cocycles, in general universes (the workspace's
`Work.AbsoluteKummer.mapH2_comp_H2π` restricts the target coefficient to the universe of `G`). -/
theorem mapH2_comp_H2π' {G : Type u} [TopologicalSpace G] [Group G]
    {M : Type v} [AddCommGroup M] [DistribMulAction G M]
    {N : Type w} [AddCommGroup N] [DistribMulAction G N]
    {P : Type w'} [AddCommGroup P] [DistribMulAction G P]
    (φ : M →+ N) (ψ : N →+ P) (hφ : Work.GroupCohomology.IsEquivariant G φ)
    (hψ : Work.GroupCohomology.IsEquivariant G ψ) (c : Work.AbsoluteKummer.Z2 G M) :
    Work.AbsoluteKummer.mapH2 (ψ.comp φ) (Work.GroupCohomology.IsEquivariant.comp hψ hφ)
        (Work.AbsoluteKummer.H2π G M c)
      = Work.AbsoluteKummer.mapH2 ψ hψ
          (Work.AbsoluteKummer.mapH2 φ hφ (Work.AbsoluteKummer.H2π G M c)) := by
  rw [Work.AbsoluteKummer.mapH2_H2π, Work.AbsoluteKummer.mapH2_H2π,
    Work.AbsoluteKummer.mapH2_H2π]
  exact congrArg (Work.AbsoluteKummer.H2π G P) (Subtype.ext rfl)

/-- Functoriality of `mapH2` on the nose: `H²` is a functor on coefficient modules. -/
theorem mapH2_compAux {G : Type u} [TopologicalSpace G] [Group G]
    {M : Type v} [AddCommGroup M] [DistribMulAction G M]
    {N : Type w} [AddCommGroup N] [DistribMulAction G N]
    {P : Type w'} [AddCommGroup P] [DistribMulAction G P]
    (φ : M →+ N) (ψ : N →+ P)
    (hφ : Work.GroupCohomology.IsEquivariant G φ)
    (hψ : Work.GroupCohomology.IsEquivariant G ψ) :
    (Work.AbsoluteKummer.mapH2 ψ hψ).comp (Work.AbsoluteKummer.mapH2 φ hφ)
      = Work.AbsoluteKummer.mapH2 (ψ.comp φ)
          (Work.GroupCohomology.IsEquivariant.comp hψ hφ) := by
  ext x
  show (Work.AbsoluteKummer.mapH2 ψ hψ) (Work.AbsoluteKummer.mapH2 φ hφ x)
      = Work.AbsoluteKummer.mapH2 (ψ.comp φ)
          (Work.GroupCohomology.IsEquivariant.comp hψ hφ) x
  obtain ⟨c, hc⟩ := QuotientAddGroup.mk'_surjective
    ((Work.AbsoluteKummer.B2 G M).comap (Work.AbsoluteKummer.Z2 G M).subtype) x
  rw [← hc]
  exact (mapH2_comp_H2π' φ ψ hφ hψ c).symm

section Devissage

variable {G : Type u} [TopologicalSpace G] [Group G]
  {N : Type v} [AddCommGroup N] [DistribMulAction G N]
  {C : Type w} [AddCommGroup C] [DistribMulAction G C]

/-- **Surjectivity half of the `α²`-dévissage.**  For an equivariant map `φ : N₁ →+ N₂`
(thought of as `N ↪ Coind_U^G N`), if `α²` is surjective for `N₂`, then it is surjective for
`N₁` — provided the induced map `Hom(N₂^G, X) → Hom(N₁^G, X)` (`X = H²(G,C)`) is surjective,
which holds whenever `φ` is injective because `𝔽_p`-vector spaces split. -/
theorem alphaTwo_surjective_of_precomp
    {N₁ : Type v} [AddCommGroup N₁] [DistribMulAction G N₁]
    {N₂ : Type v} [AddCommGroup N₂] [DistribMulAction G N₂]
    (φ : N₁ →+ N₂) (hφ : Work.GroupCohomology.IsEquivariant G φ)
    (hpre : Work.GroupCohomology.IsEquivariant G (ConjHom.precomp (C := C) φ))
    (hsurj : Function.Surjective (alphaTwo (G := G) (N := N₂) (C := C)))
    (hg' : Function.Surjective (precompHom (X := Work.AbsoluteKummer.H2 G C) (invariantsHom φ hφ))) :
    Function.Surjective (alphaTwo (G := G) (N := N₁) (C := C)) := by
  refine four_lemma_surjective (A := Work.AbsoluteKummer.H2 G (ConjHom N₁ C))
    (B := Work.AbsoluteKummer.H2 G (ConjHom N₂ C))
    (C := Work.AbsoluteKummer.H2 G (ConjHom N₁ C))
    (A' := ↥(Work.GroupCohomology.invariants G N₁) →+ Work.AbsoluteKummer.H2 G C)
    (B' := ↥(Work.GroupCohomology.invariants G N₂) →+ Work.AbsoluteKummer.H2 G C)
    (C' := ↥(Work.GroupCohomology.invariants G N₁) →+ Work.AbsoluteKummer.H2 G C)
    (0 : Work.AbsoluteKummer.H2 G (ConjHom N₁ C) →+ Work.AbsoluteKummer.H2 G (ConjHom N₂ C))
    (Work.AbsoluteKummer.mapH2 (ConjHom.precomp (C := C) φ) hpre)
    (0 : (↥(Work.GroupCohomology.invariants G N₁) →+ Work.AbsoluteKummer.H2 G C) →+
      (↥(Work.GroupCohomology.invariants G N₂) →+ Work.AbsoluteKummer.H2 G C))
    (precompHom (X := Work.AbsoluteKummer.H2 G C) (invariantsHom φ hφ))
    (alphaTwo (G := G) (N := N₂) (C := C)) (alphaTwo (G := G) (N := N₁) (C := C)) ?_ hsurj hg'
  intro x
  ext n
  exact alphaTwo_naturality φ hφ hpre x n

/-- **Injectivity half of the `α²`-dévissage** (Milne's second pass).  Let `φ : N →+ N₂` and
`ψ : N₂ →+ N₁` be the two maps of a short exact sequence of coefficients
`0 → N → N₂ → N₁ → 0`.  If

* `mapH2 (precomp φ)` is surjective (i.e. `Ext³_G(N₁,C) = 0`),
* `g' ∘ f' = 0` and `ker g' ≤ range f'` for the induced maps on `Hom(-^G, X)` (exactness of the
  dual of the coefficient sequence `0 → N^G → N₂^G → N₁^G`),
* `α²(N₁)` is surjective and `α²(N₂)` is injective,

then `α²(N)` is injective. -/
theorem alphaTwo_injective_of_precomp
    {N : Type v} [AddCommGroup N] [DistribMulAction G N]
    {N₁ : Type v} [AddCommGroup N₁] [DistribMulAction G N₁]
    {N₂ : Type v} [AddCommGroup N₂] [DistribMulAction G N₂]
    (φ : N →+ N₂) (hφ : Work.GroupCohomology.IsEquivariant G φ)
    (hpreφ : Work.GroupCohomology.IsEquivariant G (ConjHom.precomp (C := C) φ))
    (ψ : N₂ →+ N₁) (hψ : Work.GroupCohomology.IsEquivariant G ψ)
    (hpreψ : Work.GroupCohomology.IsEquivariant G (ConjHom.precomp (C := C) ψ))
    (hcomp : ∀ x : Work.AbsoluteKummer.H2 G (ConjHom N₁ C),
      Work.AbsoluteKummer.mapH2 (ConjHom.precomp (C := C) φ) hpreφ
        (Work.AbsoluteKummer.mapH2 (ConjHom.precomp (C := C) ψ) hpreψ x) = 0)
    (htop : Function.Surjective
      (Work.AbsoluteKummer.mapH2 (ConjHom.precomp (C := C) φ) hpreφ))
    (hbot : (precompHom (X := Work.AbsoluteKummer.H2 G C) (invariantsHom φ hφ)).ker
      ≤ (precompHom (X := Work.AbsoluteKummer.H2 G C) (invariantsHom ψ hψ)).range)
    (hN₁ : Function.Surjective (alphaTwo (G := G) (N := N₁) (C := C)))
    (hN₂ : Function.Injective (alphaTwo (G := G) (N := N₂) (C := C))) :
    Function.Injective (alphaTwo (G := G) (N := N) (C := C)) := by
  refine three_lemma_injective (A := Work.AbsoluteKummer.H2 G (ConjHom N₁ C))
    (B := Work.AbsoluteKummer.H2 G (ConjHom N₂ C))
    (C := Work.AbsoluteKummer.H2 G (ConjHom N C))
    (A' := ↥(Work.GroupCohomology.invariants G N₁) →+ Work.AbsoluteKummer.H2 G C)
    (B' := ↥(Work.GroupCohomology.invariants G N₂) →+ Work.AbsoluteKummer.H2 G C)
    (C' := ↥(Work.GroupCohomology.invariants G N) →+ Work.AbsoluteKummer.H2 G C)
    (Work.AbsoluteKummer.mapH2 (ConjHom.precomp (C := C) ψ) hpreψ)
    (Work.AbsoluteKummer.mapH2 (ConjHom.precomp (C := C) φ) hpreφ)
    (precompHom (X := Work.AbsoluteKummer.H2 G C) (invariantsHom ψ hψ)) (precompHom (X := Work.AbsoluteKummer.H2 G C) (invariantsHom φ hφ))
    (alphaTwo (G := G) (N := N₁) (C := C)) (alphaTwo (G := G) (N := N₂) (C := C))
    (alphaTwo (G := G) (N := N) (C := C)) ?_ ?_ (AddMonoidHom.ext hcomp) hbot hN₁ hN₂ htop
  · intro x
    ext n
    exact alphaTwo_naturality ψ hψ hpreψ x n
  · intro x
    ext n
    exact alphaTwo_naturality φ hφ hpreφ x n

/-- **`α²` for an `𝔽_p`-module of exponent `p` is p-torsion** in each variable: the cup product
of a p-torsion cocycle with a p-torsion invariant is p-torsion. -/
theorem nsmul_alphaTwo_eq_zero (p : ℕ) (x : Work.AbsoluteKummer.H2 G (ConjHom N C))
    (n : ↥(Work.GroupCohomology.invariants G N)) (hx : p • x = 0) :
    p • (alphaTwo (G := G) (N := N) (C := C) x n) = 0 := by
  have h1 : p • alphaTwo (G := G) (N := N) (C := C) x = alphaTwo (G := G) (N := N) (C := C) (p • x) :=
    (AddMonoidHom.map_nsmul (alphaTwo (G := G) (N := N) (C := C)) p x).symm
  have h2 : (p • alphaTwo (G := G) (N := N) (C := C) x) n
      = (0 : ↥(Work.GroupCohomology.invariants G N) →+ Work.AbsoluteKummer.H2 G C) n := by
    rw [h1, hx, map_zero]
  simpa using h2

/-! ## Functoriality of `mapH2`, and the combined dévissage statement -/

/-- **Milne's dévissage step for `α²` (both passes at once).**  Given the coefficient data
`φ : N →+ N₂` (`N ↪ Coind_U^G N`), `ψ : N₂ →+ N₁` (`N₂ ↠ N₁`), the exactness/commutativity
inputs `hcomp` (`mapH2 (precomp φ) ∘ mapH2 (precomp ψ) = 0`, i.e. the coefficient sequence is a
complex), `htop` (`mapH2 (precomp φ)` surjective, i.e. `Ext³_G(N₁,C) = 0`), `hbot` (exactness of
the dual invariants sequence) and `hg'` (surjectivity of the dual of `N^G ↪ N₂^G`), and given that
`α²` is bijective for `N₂` (the *base case*, `N₂` being induced) and surjective for `N₁`
(available by the first pass), the map `α²` is bijective for `N`. -/
theorem alphaTwo_bijective_of_devissage
    {N : Type v} [AddCommGroup N] [DistribMulAction G N]
    {N₁ : Type v} [AddCommGroup N₁] [DistribMulAction G N₁]
    {N₂ : Type v} [AddCommGroup N₂] [DistribMulAction G N₂]
    (φ : N →+ N₂) (hφ : Work.GroupCohomology.IsEquivariant G φ)
    (hpreφ : Work.GroupCohomology.IsEquivariant G (ConjHom.precomp (C := C) φ))
    (ψ : N₂ →+ N₁) (hψ : Work.GroupCohomology.IsEquivariant G ψ)
    (hpreψ : Work.GroupCohomology.IsEquivariant G (ConjHom.precomp (C := C) ψ))
    (hcomp : ∀ x : Work.AbsoluteKummer.H2 G (ConjHom N₁ C),
      Work.AbsoluteKummer.mapH2 (ConjHom.precomp (C := C) φ) hpreφ
        (Work.AbsoluteKummer.mapH2 (ConjHom.precomp (C := C) ψ) hpreψ x) = 0)
    (htop : Function.Surjective
      (Work.AbsoluteKummer.mapH2 (ConjHom.precomp (C := C) φ) hpreφ))
    (hbot : (precompHom (X := Work.AbsoluteKummer.H2 G C) (invariantsHom φ hφ)).ker
      ≤ (precompHom (X := Work.AbsoluteKummer.H2 G C) (invariantsHom ψ hψ)).range)
    (hg' : Function.Surjective
      (precompHom (X := Work.AbsoluteKummer.H2 G C) (invariantsHom φ hφ)))
    (hN₂ : Function.Bijective (alphaTwo (G := G) (N := N₂) (C := C)))
    (hN₁ : Function.Surjective (alphaTwo (G := G) (N := N₁) (C := C))) :
    Function.Bijective (alphaTwo (G := G) (N := N) (C := C)) :=
  ⟨alphaTwo_injective_of_precomp φ hφ hpreφ ψ hψ hpreψ hcomp htop hbot hN₁ hN₂.1,
   alphaTwo_surjective_of_precomp φ hφ hpreφ hN₂.2 hg'⟩

end Devissage

end Work.SSGRoute.PT
