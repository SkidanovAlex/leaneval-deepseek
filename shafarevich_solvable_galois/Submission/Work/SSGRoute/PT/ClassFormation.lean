import Mathlib.GroupTheory.Nilpotent
import Mathlib.RingTheory.Henselian
import Mathlib.Algebra.Field.ZMod
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.Valuation.ValuationSubring
import Submission.Work.SSGRoute.PT.HomFormReduction
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The local class formation `(D_A, \bar Ωˣ)`: the interface of Milne's Theorem I.1.8 at `r = 0`

`Work.SSGRoute.PT.localTatePairing_deg02` (Milne, *Arithmetic Duality Theorems*, Cor. I.2.3 at
`r = 0`) is reduced in its own file to the `Hom`-form

  `dim H²(D_A, M) = dim Hom_{D_A}(M, μ_p)`   for every finite `𝔽_p[Gal(K/k)]`-module `M`,

where `D_A = decomp k A` is the decomposition group of a finite place `A` of `Ω` over `k`.  This
file records the *pairing* form of that statement — the one that Milne's class-formation theorem
actually produces — and proves that it implies the target.

## Mathematical content

For the local class formation `(G_{k_v}, \bar k_v^×)`, Milne's Theorem I.1.8 at `r = 0` (Milne,
*ADT*, I.2.1) composed with the divisibility of `\bar k_v^×` says that the cup-product pairing

  `H⁰(G_{k_v}, Hom(M, μ_p)) × H²(G_{k_v}, M) → H²(G_{k_v}, \bar k_v^×) ≅ ℚ/ℤ`

is *perfect* for every finite `M` of exponent `p`.  Since both sides are finite, this is exactly
an additive isomorphism

  `Hom_G(M, μ_p) ≃+ Dual_{𝔽_p}(H²(G, M))`.

In the workspace's vocabulary this reads
`HomH p k Ω K M T (decomp k A) ≃ₗ[ZMod p] DualMod p (H2loc p k Ω K M (decomp k A))`
(`HomH` is the `D_A`-equivariant part of `M →ₗ DualMod p T`, and `DualMod p T ≅ μ_p` for a
cyclotomic dual `T`).  The two forms are equivalent: any additive map between `𝔽_p`-modules is
`𝔽_p`-linear, so an additive equivalence is one of `𝔽_p`-modules.

`Milne18AtZero` below is that statement, and `localTatePairing_deg02_of_milne18` shows that it
implies the target.  It is the *missing arithmetic input* of the whole lattice; the route to it is
Milne's class-formation chapter (ADT I.1), whose two axioms for `(D_A, \bar Ω^×)` are

* **(1.1a)** `H¹(U, \bar Ω^×) = 0` for every open `U ≤ D_A` — **proved** in this workspace:
  `Work.SSGRoute.PT.hilbert90_H1_eq_zero_openSubgroup`
  (`Submission/Work/SSGRoute/PT/KrullCorrespondence.lean`);
* **(1.1b)** a compatible family of isomorphisms `inv_U : H²(U, \bar Ω^×) ≅ ℚ/ℤ` (the local
  invariant map of `Br(k_v) = ℚ/ℤ`);

together with hypothesis **1.8(c)**: `α⁰(U, ℤ/m)` bijective for all open `U` and all `m`
(Kummer duality).

## Why the reduction below is unconditional

`Module.finrank` of the `𝔽_p`-dual equals that of the module itself by `Subspace.dual_finrank_eq`
(the evaluation-free statement `finrank (Module.Dual K V) = finrank K V`, valid *without*
finiteness hypotheses), and a linear equivalence preserves `finrank`
(`LinearEquiv.finrank_eq`).  Hence no hypothesis about the finiteness of `H²(D_A,M)` has to be
carried: the reduction
`H²(D_A,M) ≅ Dual(Hom(D_A, μ_p))` is a pure bookkeeping step once the pairing is in hand.

## Roadmap: how `Milne18AtZero` is to be proved, and what is missing

Milne, *ADT*, Theorem I.1.8 at `r = 0` for a class formation `(G, C)` (here `(D_A, \bar Ωˣ)`) is
proved by dévissage along

  `0 → M → M* → M₁ → 0`,   `M* = Ind^G_U M = ℤ[G/U] ⊗ M`,

for an open normal `U ≤ G` acting trivially on `M` (so that the pair `(U, M)` is a
*trivial-action* instance).  Since `C = \bar Ωˣ` is divisible, `Hom_ℤ(-,C)` is exact and
`Ext^r_G(N, C) = H^r(G, Hom_ℤ(N,C))` for all `r` (Milne (0.8)), so the whole proof can be run in
the *coefficient* cohomology `H^r(G, Hom_ℤ(-,C))` without building `Ext` in the category of
discrete `G`-modules.  The ingredients are:

1. **the long exact sequence in the coefficient** — available in the workspace:
   `Submission/Work/AbsoluteKummer/SES/*` (`δ`, `ker_deltaH2_le_range_mapH1`,
   `ker_mapH2_le_range_deltaH2`, …);
2. **exactness of `Hom_ℤ(-, \bar Ωˣ)`**, i.e. injectivity of the divisible group `Ωˣ` over `ℤ` —
   `Work.SSGRoute.PT.exists_addHom_extend_addUnits`
   (`Submission/Work/SSGRoute/PT/exists_addHom_extend_addUnits.lean`, proved);
3. **Shapiro's lemma**, `H*r(G, Coind^G_U N) ≅ H*r(U, N)` —
   `Work.SSGRoute.PT.shapiro_H0_coind` (proved), `…shapiro_H1_coind`, `…shapiro_H2_coind`, with
   the auxiliary `…isDiscreteModule_coind`;
4. **the trivial-action base case** `α⁰(G, M)` for `M` with trivial `G`-action.  By Milne's (1.7)
   this is exactly the two arithmetic inputs of local class field theory:
   `α⁰(G,ℤ) = rec_G` (local Artin reciprocity `D_A^{ab} ≅ k_v^×`) and
   `α²(G,ℤ) = inv_G` (`H²(D_A, \bar Ωˣ) ≅ ℚ/ℤ`, i.e. `Br(k_v) = ℚ/ℤ`), together with their
   compatibility with the cup product.  Axiom (1.1a) (`H¹(U, \bar Ωˣ) = 0`) is already available
   (`Work.SSGRoute.PT.hilbert90_H1_eq_zero_openSubgroup`).
5. **the five-lemma assembly** of the dévissage.

### The structural obstruction to be aware of

Milne's induction starts from the *high-degree* end: he uses `α^r` for `r ≥ 4`, where both sides
vanish (`Ext^r_G(N,C) = 0` for `r ≥ 4` by Lemma 1.9, and `H^{2-r}(G,N) = 0` for `r ≥ 4` by
`cd(G_{k_v}) ≤ 2`), then descends `r = 3, 2, 1, 0` by the five lemma.  The workspace's continuous
cohomology `Work.AbsoluteKummer` and the abstract `Work.GroupCohomology` provide only `H⁰`, `H¹`,
`H²` (the cochain maps stop at `d2`); `α³` and `α⁴` therefore have **no home in the current
library**.  Consequences:

* a *faithful* transcription of Milne's proof requires either building `H³`/`H⁴` for the
  continuous cohomology of a topological group, or replacing the descending induction by an
  argument that lives entirely in degrees `0`, `1`, `2`;
* an alternative that avoids the high degrees is the "Example 1.10" descent, which uses
  `Ext^r_G(M, ℤ) = H^{r-1}(G, Hom(M,ℤ))` and the `ℤ`-coefficient sequence; this again needs
  `H^3` and the `Tor`-free form of Tate–Nakayama (`Work.SSGRoute.PTembedding.tateNakayama_general`,
  still a `sorry`), and the `Tor₁`-correct form is *false* for the naive spelling (see the warning
  in `localTatePairing_deg02.lean`).

**UPDATE (why this is the `r = 2` case, and why `I.1.8(c)` is not needed).**  `Milne18AtZero`
below is the `r = 2` case of Milne's I.1.8(a) applied to the finite module `N = M^∨(1)`: there
`Ext²_G(N, C) = H²(G, Hom_ℤ(N,C)) ≅ H²(G,M)` (the twist cancellation
`Hom_ℤ(E^∨(1), Ωˣ) ≅ E`, `hom_dualMod_local_units`) and the target of `α²(G,N)` is
`H⁰(G,N)^∨`.  So the hypothesis `I.1.8(c)` (Kummer duality) is *not* part of what the target needs.
The coefficient-level maps `α⁰`, `α²` of that statement are built in
`Submission/Work/SSGRoute/PT/AlphaPairing.lean` (`Work.SSGRoute.PT.alphaZero`,
`Work.SSGRoute.PT.alphaTwo`), and the naturality squares needed by the five-lemma dévissage are
`Work.SSGRoute.PT.alphaTwo_naturality` and `Work.SSGRoute.PT.alphaTwo_evalHom`.

**Recommended next steps, in order.** (i) Build `H³` (and, if the five lemma is kept, `H⁴`) for
`Work.AbsoluteKummer` — the cochain maps `d3`, `d4` and the connecting maps of the long exact
sequence, mirroring `Submission/Work/AbsoluteKummer/SES/*`.  (ii) Prove the trivial-action base
case from local class field theory in the form `α⁰(G, ℤ/m)` and `α²(G, ℤ/m)` (Milne (1.7)).
(iii) Assemble the dévissage with the five lemma.  Only then should the arithmetic of the class
formation axioms (1.1b) be attacked; (1.1a) is done.
-/

set_option linter.unusedSectionVars false

open Classical

namespace Work.SSGRoute.PT

noncomputable section

/-- **The pairing form of Milne's Theorem I.1.8 at `r = 0` for the local class formation
`(D_A, \bar Ω^×)`.**  For every finite place `A` of `Ω` over `k` and every finite
`𝔽_p[Gal(K/k)]`-module `M`, the local Tate pairing is perfect, i.e. there is an additive
isomorphism

  `Hom_{D_A}(M, μ_p) ≃+ Dual_{𝔽_p}(H²(D_A, M))`

(`HomH` is the module of `D_A`-equivariant `𝔽_p`-linear maps `M → DualMod p T ≅ μ_p`, and
`DualMod p (H2loc …)` is the `𝔽_p`-dual of the continuous `H²`). -/
def Milne18AtZero
    (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
    [IsAlgClosure k Ω] (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    (T : Type) [AddCommGroup T] [Module (ZMod p) T] [DistribMulAction (K ≃ₐ[k] K) T]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) T] : Prop :=
  ∀ (A : ValuationSubring Ω) (hA : SSGRoute.IsFinPlace k A) (M : Type)
      [AddCommGroup M] [Module (ZMod p) M]
      [DistribMulAction (K ≃ₐ[k] K) M] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M] [Finite M],
    Nonempty (HomH p k Ω K M T (SSGRoute.decomp k A) ≃ₗ[ZMod p]
      Work.SSGRoute.DualMod p (Work.SSGRoute.H2loc p k Ω K M (SSGRoute.decomp k A)))


/-! ## Vocabulary needed below: the coinduced module `Coind^G_U M`

Shapiro's lemma (one of the two pillars of Milne's class-formation proof, used in the dévissage of
Theorem I.1.8) is the statement

  `Hⁿ(G, Coind^G_U M) ≅ Hⁿ(U, M)`,

where `Coind^G_U M = {f : G → M // ∀ g u, f (g * u) = u⁻¹ • f g}` is the coinduced module.  It is
the piece that converts the duality for `M` over the *open normal* subgroup `U` (where the action
on `M` is trivial) into the duality for the induced module `Ind^G_U M = ℤ[G/U] ⊗ M` over `G`,
which is the induction step of Milne's dévissage.  The definition and its module structure are
put here so that the statement of Shapiro's lemma can be written down precisely. -/

section Coind

variable (G : Type*) [Group G] (U : Subgroup G) (M : Type*) [AddCommGroup M] [DistribMulAction U M]

/-- The coinduced module `Coind^G_U M` as an additive subgroup of the function space `G → M`. -/
def coindSub : AddSubgroup (G → M) where
  carrier := {f | ∀ (g : G) (u : U), f (g * (u : G)) = u⁻¹ • f g}
  zero_mem' := by
    intro g u
    simp
  add_mem' := by
    intro f h hf hh g u
    simp only [Pi.add_apply, hf g u, hh g u, smul_add]
  neg_mem' := by
    intro f hf g u
    simp only [Pi.neg_apply, hf g u, smul_neg]

/-- The coinduced module `Coind^G_U M = {f : G → M // ∀ g u, f (g * u) = u⁻¹ • f g}`. -/
abbrev Coind : Type _ := ↥(coindSub G U M)

variable {G U M}

instance : CoeFun (Coind G U M) (fun _ => G → M) := ⟨Subtype.val⟩

@[simp] theorem Coind.coe_mul (f : Coind G U M) (g : G) (u : U) :
    f (g * (u : G)) = u⁻¹ • f g := f.2 g u

/-- The `G`-action on the coinduced module: `(g • f) x = f (g⁻¹ * x)`. -/
instance : SMul G (Coind G U M) :=
  ⟨fun g f => ⟨fun x => f (g⁻¹ * x), by
    intro x u
    show f (g⁻¹ * (x * (u : G))) = u⁻¹ • f (g⁻¹ * x)
    rw [← mul_assoc]
    exact f.2 (g⁻¹ * x) u⟩⟩

@[simp] theorem Coind.smul_apply (g : G) (f : Coind G U M) (x : G) :
    (g • f) x = f (g⁻¹ * x) := rfl

instance : DistribMulAction G (Coind G U M) where
  one_smul f := by
    ext x
    simp
  mul_smul g h f := by
    ext x
    simp [mul_inv_rev, mul_assoc]
  smul_zero g := by
    ext x
    simp
  smul_add g f h := by
    ext x
    simp [smul_add]

end Coind

/-- **The target follows from the pairing form of Milne I.1.8 at `r = 0`.**  Both sides are the
`𝔽_p`-dimension of the same finite module: the right-hand side of `localTatePairing_deg02` is
`Hom_{D_A}(M, μ_p)` (`h0loc_dualMod_tensor`), and the pairing identifies that with the `𝔽_p`-dual
of `H²(D_A, M)` (`Milne18AtZero`), whose `finrank` is that of `H²(D_A, M)`
(`Subspace.dual_finrank_eq`). -/
theorem localTatePairing_deg02_of_milne18
    (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
    [IsAlgClosure k Ω] (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    (ζ : Ω) (hζ : IsPrimitiveRoot ζ p) (hζK : ζ ∈ K)
    (T : Type) [AddCommGroup T] [Module (ZMod p) T] [DistribMulAction (K ≃ₐ[k] K) T]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) T]
    (hT : SSGRoute.IsCyclotomicDual p (T := T) (SSGRoute.res k K) ζ)
    (h : Milne18AtZero p k Ω K T) :
    ∀ (A : ValuationSubring Ω) (hA : SSGRoute.IsFinPlace k A) (M : Type)
        [AddCommGroup M] [Module (ZMod p) M]
        [DistribMulAction (K ≃ₐ[k] K) M] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M] [Finite M],
        Module.finrank (ZMod p) (Work.SSGRoute.H2loc p k Ω K M (SSGRoute.decomp k A)) =
          Module.finrank (ZMod p) (Work.SSGRoute.H0loc p k Ω K
            (Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T)) (SSGRoute.decomp k A)) := by
  intro A hA M _ _ _ _ _
  obtain ⟨e⟩ := h A hA M
  have h1 : Module.finrank (ZMod p) (HomH p k Ω K M T (SSGRoute.decomp k A)) =
      Module.finrank (ZMod p) (Work.SSGRoute.DualMod p
        (Work.SSGRoute.H2loc p k Ω K M (SSGRoute.decomp k A))) :=
    e.finrank_eq
  have h2 : Module.finrank (ZMod p) (Work.SSGRoute.DualMod p
        (Work.SSGRoute.H2loc p k Ω K M (SSGRoute.decomp k A))) =
      Module.finrank (ZMod p) (Work.SSGRoute.H2loc p k Ω K M (SSGRoute.decomp k A)) :=
    Subspace.dual_finrank_eq
  rw [(h0loc_dualMod_tensor p k Ω K M T (SSGRoute.decomp k A)).finrank_eq]
  exact h2.symm.trans h1.symm

end

end Work.SSGRoute.PT
