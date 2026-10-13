import Mathlib
import Submission.Work.DSMap.Map
import Submission.Work.DSMap.Mix2
import Submission.Work.DSEQ0.Gamma
import Submission.Work.DSMX0U.cechZ_homology_finite
import Submission.Work.DSEQ0.boundedModelU_of_resolutions
import Submission.Work.DSREG.Main
import Submission.Work.DSEQ0.finFreeResolution_of_isRegularLocalRing
import Submission.Work.DSEQ0.exists_unitalModel
import Submission.Work.DSEQ0.exists_traceFunctional
import Submission.Work.DSEQ0.eulerChar_ne_zero

/-!
# `Work.DSEQ0`: the two inputs of area `EQ0` that are not in the library

This file isolates, in the shape in which the assembly `Work.DSEQ0.area_EQ0_proved` consumes
them, the two *mathematical* inputs of the equal-characteristic-zero area which are **not**
available in this workspace:

* `Work.DSEQ0.exists_finFreeResolution` — **input (3a)**, Serre's theorem `gl.dim A = dim A`
  (finite projective dimension over a regular local ring; the `ABS` fork of the proof map);
* `Work.DSEQ0.exists_modelFunctional` — **input (4)**, the trace functional on the bounded model
  (the Alexander–Whitney product, its supertrace, and the generic degree; Bhatt's remark after
  Theorem 5.2).

Both are stated here with `sorry` bodies, exactly as the frozen nodes of the proof map are.  The
*third* input of the area's original design, `Work.DSEQ0.exists_boundedFinFreeModelU` (**input
(3)**, the bounded finite free model with its coaugmentation), is now a **theorem** in this file:
it is derived from (3a), from the (frozen) finiteness and vanishing of the Čech cohomology, and
from the splicing lemma `Work.DSEQ0.boundedModelU_of_resolutions` (proved, axiom-clean) — see
below.  Consequently the assembly of `Work.DSEQ0.area_EQ0_proved` is `sorry`-free and the
remaining gap of the area is exactly the pair (3a)+(4).

**Correction (found by a delegated refutation).**  The model of input (3) may *not* be required
to vanish in negative degrees: `P.X i = 0` for `i < 0` forces `H⁰(Č) = H⁰(P) = ker (P.d 0 1) ↪
P.X 0` to be torsion-free over `A`, which fails e.g. for `A = k⟦x⟧` regular local and
`X = Spec k` with the trivial cover.  The refutation is formalized in
`Submission/Work/DSEQ0/boundedModel_of_resolutions.lean`
(`Work.DSEQ0.not_boundedModel_concl`, sorry-free, axiom-clean); the corrected statement — and
what the trace functional needs — is boundedness in *both* directions, which is what is proved.

## Why these two, and why they are not the claim

The area's theorem is `DSplit A X f` (a statement in `D(A)`).  What the workspace *does* have is
the chain-level bridge `DSMap.Mix2.area_MX0bU` (a frozen node, proved modulo `F1`):
an honest splitting `DSMap.Mix.ModSplit P ε (RingHom.id A) ⊥ 1` of a finite free model `P` of the
Čech complex gives `DSplit`.  Unfolding `ModSplit`, this is an `A`-linear `s : P⁰ → A` with
`s ∘ d⁻¹ = 0` and `s (ε 1) = 1` — i.e. `ε 1` must generate a *free direct summand* of
`coker (P⁻¹ → P⁰)`, not merely be nonzero.  Two things are missing for that:

* **(3) a *bounded* finite free model** `P` of the Čech complex (`i < 0 ∨ M < i → Pⁱ = 0`).
  The node `DSMap.Mix2.area_MX0U` produces a model which is only bounded *above*
  (its tower is infinite downwards), and an unbounded-below model cannot carry the trace
  functional `s` (the trace of an endomorphism of such a complex is an infinite sum), nor does
  the extension argument that produces `s` from a functional on `H⁰` apply.  Boundedness below is
  *finite projective dimension* of the cohomology modules `Hⁱ(Č)`, i.e. Serre's theorem
  `gl.dim A = dim A` for the regular local ring `A` (Auslander–Buchsbaum–Serre), for which the
  proof map records the fork `ABS-Criterion-Projection-new` (`Thmoas-Guan`) as the source.
  The *reduction* of (3) to finite free resolutions of the `Hⁱ` is already proved in this area
  (`Work.DSEQ0.exists_bounded_free_model`, `Work.DSEQ0.bounded_free_model_of_triangle`,
  `Work.DSEQ0.bounded_free_model_of_shortExact`).

* **(4) the trace functional with value a nonzero natural number** on the coaugmentation class,
  killing the differential.  Its construction is the trace on the perfect complex (Bhatt,
  *On the direct summand conjecture and its derived variant*, the remark after Theorem 5.2,
  TeX line 596 of `sources/dsmap/1608.08882/main.tex`):
  `RΓ(X,𝒪_X)` is perfect over the regular local `A`, carries a commutative algebra structure in
  `D(A)`, and composing the multiplication with the trace of a perfect complex gives
  `Tr : RΓ → A` whose composite with `A → RΓ` is multiplication by
  `χ = Σᵢ (-1)ⁱ rk Hⁱ(X_η, 𝒪) = [K(X) : K]` — a nonzero natural number, hence a *unit* of `A`
  because the residue field has characteristic zero
  (`Work.DSEQ0.isUnit_natCast_of_charZero_residueField`).
  The *linear algebra* of this step is already proved in this area (`Work.DSEQ0.SuperTrace`,
  `Work.DSEQ0.exists_functional_of_unitalProduct`, `Work.DSEQ0.sum_trace_leibniz_eq_zero`,
  `Work.DSEQ0.gradedCommutator_superTrace_eq_zero`); what is missing is the transport of the
  Alexander–Whitney product of the Čech complex to a strictly unital chain map
  `μ : P ⊗ P → P` on the bounded model (the "strictification"), plus the identification of
  `Σ (-1)ⁱ rk Pⁱ` with the generic degree `[K(X):K]` (which uses `F1` base change to
  `K = Frac A` and the generic finiteness of `f`).

## Why regularity is needed (and is assumed)

Without `[IsRegularLocalRing A]` the *conjunction* of (3) and (4) is **false**: by Kovács'
characterization of rational singularities (`[Kov00, Thm 3]` + `[Bha12, Thm 2.12]`, quoted in
`arXiv:2307.07906`; and `thm:der-spl` of Kovács, *Rational singularities*, arXiv:1703.02269),
the unit `𝒪_Y → Rf_*𝒪_X` does not split for the resolution `X = Tot(𝒪_E(-1)) → Y` of the vertex
of the cone over a smooth plane cubic `E` (there `Γ(X,𝒪_X) = A`, `H¹(X,𝒪_X) = ℚ ≠ 0` and `A` is
normal but not regular).  Accordingly both nodes below carry `[IsRegularLocalRing A]` (resp. the
hypotheses of the area), exactly as the frozen `DSMap.area_EQ0` does.  This was recorded in the
(refuted) statement `Submission/Work/DSEQ0/exists_finFreeModelU_with_modSplit.lean`, whose repair
is precisely the regularity hypothesis assumed here.
-/

open CategoryTheory AlgebraicGeometry

namespace Work.DSEQ0

universe a

/-- **Input (3a) of area `EQ0`: Serre's theorem for regular local rings (finite projective
dimension).**

Every finitely generated module `M` over a regular local ring `A` has a *bounded* finite free
resolution: for every degree `i : ℤ`, a bounded complex `G` of finitely generated free `A`-modules
with a quasi-isomorphism `G ⟶ M[i]` (the single-object complex in degree `i`; the case `i = 0` is
the statement "in degree zero", the other degrees are obtained from it by shifting).

This is the Auslander–Buchsbaum–Serre theorem `gl.dim A = dim A` (Serre, *Sur la dimension
homologique des anneaux locaux réguliers*), the single largest missing library item of the area
and of the whole proof map (see `sources/dsmap/direct_summand_proof_map.md`: "ABS fork
(gl.dim = dim)").  It is stated here in the general form in which the areas `EQ0` and `MIX`
consume it — for an arbitrary finitely generated module, not only the cohomology of the Čech
complex, and in the degree in which that cohomology sits — and everything *below* it is already
proved in this area: `Work.DSEQ0.boundedModelU_of_resolutions` (proved, axiom-clean) splices
finite free resolutions of the cohomology modules of `cechZ A X f U` into a bounded finite free
model with the coaugmentation, so that `Work.DSEQ0.exists_boundedFinFreeModelU` below is a
*theorem* whose only remaining input is this node. -/
theorem exists_finFreeResolution (A : Type a) [CommRing A] [IsRegularLocalRing A]
    (i : ℤ) {M : Type a} [AddCommGroup M] [Module A M] [Module.Finite A M] :
    ∃ (G : CochainComplex (ModuleCat.{a} A) ℤ),
      (∀ j, Module.Finite A (G.X j)) ∧ (∀ j, Module.Free A (G.X j)) ∧
      (∃ a b : ℤ, ∀ j, j < a ∨ b < j → CategoryTheory.Limits.IsZero (G.X j)) ∧
      ∃ g : G ⟶ (HomologicalComplex.single (ModuleCat.{a} A) (ComplexShape.up ℤ) i).obj
          (ModuleCat.of A M),
        QuasiIso g :=
  Work.DSEQ0.finFreeResolution_of_isRegularLocalRing (A := A) i

/-- **Input (3) of area `EQ0` (bounded finite free model).**

For `A` a regular local ring, `f : X ⟶ Spec A` proper and projective, and `U` a finite affine
cover of `X`, there is a finite free model of the Čech complex `cechZ A X f U` which is
*bounded* — a cochain complex `P` of finitely generated free `A`-modules concentrated in a window
`[a, b]`, `a` possibly negative — carrying the coaugmentation `ε`, a quasi-isomorphism to the
Čech complex, and the compatibility `ε ≫ q.f 0 ≫ extendXIso = coaug0` of
`DSMap.Mix2.IsFinFreeModelU` (which is what the bridge `area_MX0bU` consumes).

**Correction.**  The earlier form of this node required `P.X i = 0` for `i < 0`.  That is
*false*: it forces `H⁰(Č) = H⁰(P) = ker (P.d 0 1) ↪ P.X 0` with `P.X 0` free, hence
`H⁰(Č) ≅ Γ(X,⊤)` torsion-free over `A` — contradicted, for instance, by `A = k⟦x⟧` (regular
local) and `X = Spec k` with the trivial cover, where `Γ(X,⊤) = k = A/(x)`.  The refutation is
formalized, sorry-free and axiom-clean, in `Submission/Work/DSEQ0/boundedModel_of_resolutions.lean`
(`Work.DSEQ0.not_boundedModel_concl`).  Only boundedness in *both* directions is claimed, and
that is what the trace functional of input (4) needs.

Mathematically this is Serre's theorem `gl.dim A = dim A` for a regular local ring
(Auslander–Buchsbaum–Serre, input (3a) `exists_finFreeResolution`) applied to the finitely
generated cohomology modules `Hⁱ(Č)` (finite and bounded above by the frozen node
`DSMap.area_COH`), spliced into a bounded complex; see `Work.DSEQ0.exists_bounded_free_model` for
the splicing step, which is already proved in this area. -/
theorem exists_boundedFinFreeModelU (A : Type a) [CommRing A] [IsRegularLocalRing A]
    (X : Scheme.{a}) (f : X ⟶ Spec (.of A)) [IsProper f] (hp : DSMap.IsProjOver A f)
    {ι : Type a} [Finite ι] (U : ι → X.Opens) (hU : ∀ i, IsAffineOpen (U i))
    (hcov : ⨆ i, U i = ⊤) :
    ∃ (a b : ℤ) (P : CochainComplex (ModuleCat.{a} A) ℤ) (ε : ModuleCat.of A A ⟶ P.X 0),
      DSMap.Mix2.IsFinFreeModelU A X f U P ε ∧
        (∀ i : ℤ, i < a ∨ b < i → CategoryTheory.Limits.IsZero (P.X i)) := by
  -- the finiteness (and vanishing above `N`) of the Čech cohomology, from the frozen `COH`
  obtain ⟨N, hN⟩ := Work.DSMX0U.cechZ_homology_finite (A := A) f hp U hU hcov
  -- Serre's theorem (input (3a)): a bounded finite free resolution of each `Hⁱ(Č)`
  have hex : ∀ i : ℤ, ∃ (G : CochainComplex (ModuleCat.{a} A) ℤ),
      (∀ j, Module.Finite A (G.X j)) ∧ (∀ j, Module.Free A (G.X j)) ∧
      (∃ a b : ℤ, ∀ j, j < a ∨ b < j → CategoryTheory.Limits.IsZero (G.X j)) ∧
      ∃ g : G ⟶ (HomologicalComplex.single (ModuleCat.{a} A) (ComplexShape.up ℤ) i).obj
        ((DSMap.cechZ A X f U).homology i), QuasiIso g :=
    fun i => by
      haveI : Module.Finite A ↥((DSMap.cechZ A X f U).homology i) := (hN i).1
      exact exists_finFreeResolution (A := A) i (M := ↥((DSMap.cechZ A X f U).homology i))
  choose G hrest using hex
  -- splicing the resolutions into a bounded model, with the coaugmentation
  exact Work.DSEQ0.boundedModelU_of_resolutions A X f U hU hcov N (fun i hi => (hN i).2 hi) G
    (fun i j => (hrest i).1 j) (fun i j => (hrest i).2.1 j) (fun i => (hrest i).2.2.1)
    (fun i => (hrest i).2.2.2)

/-- **Input (4), restated against a model that is *chosen* rather than given.**

The trace argument of area `EQ0` produces the functional `φ₀` together with the model it lives on:
a *strictly unital* finite free model of the Čech complex.  It is therefore cleaner to ask for the
model and the functional simultaneously, which is the statement below.  It is proved from the
three nodes of `Submission/Work/DSEQ0/NEXT_input4.md`:

* `Work.DSEQ0.exists_unitalModel` — the finite free model `(P, ε)` with its strictly Leibniz
  product `μ` (unital up to homotopy);
* `Work.DSEQ0.exists_traceFunctional` — the functional `φ₀ x := Σᵢ (-1)ⁱ tr (μ x i)` on it,
  killing `im (d⁻¹)` and with `φ₀ (ε 1) = Σᵢ (-1)ⁱ rk (Pⁱ)`;
* `Work.DSEQ0.eulerChar_ne_zero` — that Euler characteristic is nonzero (the generic degree
  `[K(X) : K] ≥ 1`).

This is the *only* input of the area that is not yet in the library; it carries the regularity of
`A` (finite global dimension, used to make the model bounded and to resolve the kernel of the
surjective replacement), and no finiteness hypothesis on the Čech cohomology is needed any more
(the model is built from the Čech complex of the cover by a free replacement, not from free
resolutions of its cohomology). -/
theorem exists_traceModelFunctional (A : Type a) [CommRing A] [IsRegularLocalRing A]
    (X : Scheme.{a}) (f : X ⟶ Spec (.of A)) [IsProper f] (hs : Function.Surjective f)
    (hg : DSMap.IsGenFinite A f) (hp : DSMap.IsProjOver A f) {ι : Type a} [Finite ι]
    (U : ι → X.Opens) (hU : ∀ i, IsAffineOpen (U i)) (hcov : ⨆ i, U i = ⊤) :
    ∃ (P : CochainComplex (ModuleCat.{a} A) ℤ) (ε : ModuleCat.of A A ⟶ P.X 0)
      (φ₀ : ↥(P.X 0) →ₗ[A] A) (n : ℤ),
      n ≠ 0 ∧ DSMap.Mix2.IsFinFreeModelU A X f U P ε ∧
      (∀ y : ↥(P.X (-1)), φ₀ ((P.d (-1) 0).hom y) = 0) ∧ φ₀ (ε.hom 1) = (n : A) := by
  haveI : IsDomain A := DSMap.area_REG_proved A
  obtain ⟨F, ε, lo, hi, μ, hP, hbdd, hLeib, H, hunit⟩ :=
    Work.DSEQ0.exists_unitalModel A X f hp U hU hcov
  obtain ⟨φ₀, hker, hval⟩ :=
    Work.DSEQ0.exists_traceFunctional A F ε lo hi hbdd (fun i => (hP.1.1 i).2)
      (fun i => (hP.1.1 i).1) μ hLeib H hunit
  obtain ⟨q, hq, -⟩ := hP.2.2
  exact ⟨F, ε, φ₀,
    ∑ i ∈ Finset.Icc lo hi, (-1 : ℤ) ^ i.natAbs * (Module.finrank A ↥(F.X i) : ℤ),
    Work.DSEQ0.eulerChar_ne_zero A X f hs hg U hU hcov F lo hi hbdd
      (fun i => (hP.1.1 i).2) (fun i => (hP.1.1 i).1) q hq,
    hP, hker, hval⟩

end Work.DSEQ0
