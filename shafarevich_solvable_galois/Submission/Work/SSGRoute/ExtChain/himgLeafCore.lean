import Mathlib.FieldTheory.KrullTopology
import Mathlib.GroupTheory.Nilpotent
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.TotallySplit
import Mathlib.Algebra.Field.ZMod
import Mathlib.Data.Int.Star
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.RepresentationTheory.Rep.Basic
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.Valuation.ValuationSubring
import Mathlib.Topology.Separation.Connected
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Homology.DerivedCategory.Ext.Basic
import Submission.Work.SSGRoute.ExtChain.extLoc_extToIdeles_e1aSyzShift_eq_zero_imp
import Submission.Work.SSGRoute.ExtChain.subsingletonH1_homCoind_of_trivial_action
import Submission.Work.SSGRoute.PT.sha2_range_iff
import Submission.Work.SSGRoute.PTdualControl.extExact
import Submission.Work.SSGRoute.SSGStage.e1aLandingFinCompat
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The `himg` half of the chain--localisation comparison `(C')` of the E1a node

This file contains the target clause

    extToIdeles y = 0  →  ∃ c ∈ Z2loc,  H2π (Z2ofZ2loc c) = e1aChainC y            (`himg`)

and, proved above it, the *assembly* half of that clause:

* `Work.SSGRoute.ExtChain.himg_reduction`: given `z ∈ Ext¹_G(R, Kˣ)` with
  `e1aSyzShift z = y` (`R = ker (freeCover (E^∨(1)))`) and the per-place hypotheses
  `resH1_{D_A}(e1cMap R z) = 0` at every finite place `A` of `Ω` and at `⟨σ⟩` for every involution
  `σ`, the conclusion `∃ c ∈ Z2loc, H2π (Z2ofZ2loc c) = e1aChainC y` follows.  This is pure
  assembly: `ExtChain.deltaH2_restriction` + `SSGStage.akRes_eq_resH2` + `akRes_mapH2` give
  `akRes_D (e1aChainC y) = 0`, and `SSGStage.isCoboundary2On_of_akRes_H2π_eq_zero` converts that
  into the last two clauses of `Z2loc` for a continuous representative of `e1aChainC y`.

The two per-place hypotheses of `himg_reduction` are what the input `extToIdeles y = 0` supplies:

* `Work.SSGRoute.ExtChain.extLoc_extToIdeles_e1aSyzShift_eq_zero_imp` (proved, own file) reads
  `extLoc_w (extToIdeles y) = 0` as `z_w = 0`, where `z_w = (extRes_{D_q} z) ∘ mk₀ (unitsToLocalUnits)`;
* the *missing* input is the local comparison square `(★')` of `PT/NOTE_e1a_square_session10.md` §1
  (and `ExtChain/NOTE_A1_A2_session_2026-10-01b.md` §4),

      Ξ (resH1_{D_A} (e1cMap X z)) = e1cMap^{local} (localExtTransport (z_w)),

  with `Ξ` the group transport along `Φ : D_A ≃* Gal(M/L)` followed by the coefficient change
  `Ωˣ → Mˣ` along the injective seam `Ω →+* M = localClosureAt k A hA`.  Instantiating (★') at
  `z = 0`-localisation gives `resH1_{D_A}(e1cMap X z) = 0` because the seam is injective.
  All the ingredients of (★') are on disk (`E1cGeneric.PhiE_surjective`,
  `PT.e1cMap_PhiE_eq_delta_gen`, `PT.PhiEgen_res_compat`, `PT.e1aE1c_step_coeff_generic`,
  `PT.e1a_deltaH1_natural`, `PT.delta_restrictSES`, the `hψ` clause of
  `PT.exists_localField_place_data`, the seam machinery of `PT/e1a_seam.lean` -- whose file does
  not currently build -- and the local Ext transport of `E1aClean/Transport.lean`); what is missing
  is only their assembly into (★'), for the *finite* places and for the *involutions*
  (`resH1_{⟨σ⟩}`), the latter needing the archimedean analogue of the local datum.

## ⚠ Correction (session 11), sharpened (session 13): the *per-place* form is FALSE

``Use only `z_w = 0` at the single place `q` below `A`'' is **not** enough: a class of
`Ext¹_{D_q}(res R, Kˣ)` whose localisation at the *one* place `q` vanishes under the coefficient
change `Kˣ → K_qˣ` need not be zero.  Equivalently (`e1cMap` commutes with restriction and is
injective at a closed subgroup, cf. `deltaH2_restrictSES_e1aSES_injective'`), the per-place
statement is exactly the injectivity of

    Ext¹_{D_q}(res R, Kˣ) ⟶ Ext¹_{D_q}(res R, K_qˣ),

a *one-place* Hasse principle, which fails: for `k = ℚ`, `K = ℚ(i)`, `q = (3)` (inert, so
`D_q = G`) and `N = ℤ` the chain `Ext¹_G(R,Kˣ) ≅ H²(G,Kˣ) = Br(ℚ(i))` converts it into the
localisation `Br(K) → Br(K_q)`, and the quaternion class `(−1,−1)` is non-trivial in `Br(ℚ(i))`
(ramified at the prime over `2`) but splits at `3`.  A colleague *proved this false* and returned
the verdict, so the statement `SSGRoute/PT/resH1_e1cEquiv_eq_zero_of_extRes_comp_eq_zero` (and its
archimedean analogue) must **not** be requested in the per-place form.

**Session 13 sharpens the mechanism** (see `NOTE_himg_extDelta_session13.md` §2).  For
`H := D_A ∩ G_K ◁ D_A` (it is normal because `G_K ◁ Γ`), `H¹(H, Hom(R.V,Ωˣ)) = 0`
(`subsingletonH1_homCoind_of_le_ker`), so the five-term sequence identifies
`H¹(D_A, Hom(R.V,Ωˣ)) ≅ H¹(D_q, Hom(R.V,(K·Ω^{D_A})ˣ))` with `Ω^H = K·Ω^{D_A}`.  Hence the *sharp*
per-place statement is

    (★)  resH1_{D_A}(e1cMap R z) = 0  ⟺  cc_{K·Ω^{D_A}}(res_{D_q} z) = 0,

whereas `z_w = 0` is `cc_{K_w}(res_{D_q} z) = 0` — coefficients in the **completion** `K_wˣ`.  The
coefficient change factors as `Kˣ → (K·Ω^{D_A})ˣ → K_wˣ`, so `(★)` is strictly stronger: the
kernel of `Ext¹_{D_q}(res R,(K·Ω^{D_A})ˣ) → Ext¹_{D_q}(res R,K_wˣ)` is the local `Ш²` (the ramified
part added by completion), and it is genuinely non-trivial — that is exactly the quaternion
example (`cc_{K_3}(res z) = 0`, `cc_{K·Ω^{D_A}}(res z) = z ≠ 0`).  In particular `z_w = 0` does
**not** determine `resH1_{D_A}(e1cMap R z)`: there is no per-place square, for the coefficient
field `K·Ω^{D_A}`, *not* because of a `K`-vs-`K·Ω^{D_A}` extension-problem mismatch.

**The honest remaining input is therefore global**: the implementation must use the vanishing of
`z_w` at *all* places `w` of `K`, i.e. a Hasse-principle-type statement

    (∀ w : NK.GlobalCFT.Place K, z_w = 0) → ∀ A, IsFinPlace k A → resH1_{decomp k A}(e1cMap R z) = 0,
    (∀ w : NK.GlobalCFT.Place K, z_w = 0) → ∀ σ, σ ^ 2 = 1 → resH1_{⟨σ⟩}(e1cMap R z) = 0.

These are exactly the hypotheses `hfin`, `hinf` of `himg_reduction` below, and the hypothesis
`∀ w, z_w = 0` is what `extLoc_extToIdeles_e1aSyzShift_eq_zero_imp` +
`extToIdeles_eq_zero_iff_extLoc` supply from `extToIdeles y = 0`.  The `extDelta`-form used by
`himg_of_extDelta_input` below is the *sharpest* spelling: by
`PTdualControl.exists_extDelta_eq_of_extToIdeles_eq_zero` one has
`extToIdeles y = 0 ⟺ ∃ x : Ext¹_G(E^∨(1),C_K), extDelta x = y`, so the input becomes an
*unconditional* statement about a composite of canonical maps, with no hypothesis left to carry.


Two further facts about the input (both *checked* in this stretch, one by a colleague's `Ext`
computation, one by a colleague's refutation):

* `z_w = 0 ↔ cc_w (extRes_{D_w} z) = 0`, `cc_w` the coefficient change `Kˣ → K_wˣ`
  (this is definitional, plus the two directions
  `SSGStage.extLoc_extToIdeles_e1aSyzShift_eq_zero` / `..._imp`).
* **`resH1_D (e1cMap R z) = 0` is *not* equivalent to `extRes_D z = 0`** (a colleague refuted the
  `↔`).  The correct descriptions (colleague's computation on `PhiE`-generators, where
  `z = PhiE y`, `y ∈ Hom_G(R₁,Kˣ)`, `R₁ = ker (freeCover R)`, `F = Rep.free Coeff G R.V`) are:

      resH1_D (e1cMap R z) = 0  ↔  y extends to a `D`-equivariant map F → (K·Ω^D)ˣ,
      extRes_D z = 0            ↔  y extends to a `D`-equivariant map F → Kˣ,

  which differ as soon as `D ∩ Gal(Ω/K) ≠ 1` and `D ⊄ Gal(Ω/K)` — exactly the case of the
  decomposition groups of the finite places.  (This is the same obstruction as the missing
  level-change square, which the workspace only has for levels `L ⊆ K`.)

So the target is **not** reducible to a statement about the restrictions `extRes_{D_q} z` alone;
the finite-place input has to be of the form

    (∀ w : NK.GlobalCFT.Place K, z_w = 0) → resH1_{decomp k A} (e1cMap R z) = 0,

i.e. a genuinely global comparison.  What *is* proved here (see below) is that this input is only
needed for the finite places with `decomp k A ⊄ ker (res k K)` and for the involutions with
`res k K σ ≠ 1`.
The partially-usable direction of the missing square is the one that *is* true per place:
`resH1_{D_A}(e1cMap R z) = 0 → z_w = 0` (`SSGRoute/PT/extRes_e1cEquiv_eq_zero_of_resH1_e1cEquiv_eq_zero`).

## What this file proves (sorry-free)

* `himg_reduction` — the assembly: `hfin` + `hinf` give the conclusion (this is the reduction of
  the target to the two families of subgroups).
* `resH1_e1cMap_eq_zero_of_le_ker` — **`resH1_D (e1cMap R z) = 0` for every closed `D ≤ ker (res k K)`**
  (Hilbert 90 at the closed subgroup `D`, via
  `Work.SSGRoute.ExtChain.subsingletonH1_homCoind_of_le_ker`).
* `resH1_zpowers_eq_zero_of_res_eq_one` — the `⟨σ⟩`-case of the same, i.e. every involution of
  `Gal(Ω/K) ≤ Gal(Ω/k)` is *free* for `himg`.
* `himg_reduction'` — `himg_reduction` with those two free families removed from the hypotheses:
  the finite places whose decomposition group already fixes `K` (completely split primes of `K`)
  and the involutions in `Gal(Ω/K)` need no input.  What is left — the finite places with
  `decomp k A ⊄ ker (res k K)` and the involutions with `res k K σ ≠ 1` — is exactly the
  arithmetic content of `himg`.

Auxiliary results landed in this directory in the same stretch:
`exists_primeUnder_hAq` (the prime of `𝒪_K` below a finite place of `Ω`, with the
`hAq`-characterisation: for every finite place `A` of `Ω` there is `q` with
`x ∈ q ↔ A.valuation x < 1`) and `subsingletonH1_homCoind_of_le_ker` (the Hilbert-90 vanishing).

Session 13 additions (all proved, sorry-free):

* `Work.SSGRoute.ExtChain.subsingletonH1_homCoind_of_trivial_action` (own module) —
  `Subsingleton (H¹(D, Hom_ℤ(R.V,Ωˣ)))` for every **closed** `D` acting *trivially on `R.V`*
  (this only needs Hilbert 90 at `D` plus the triviality of the action on the carrier; the
  previously used hypothesis `D ≤ ker (res k K)` is one way of ensuring it);
* `resH1_e1cMap_eq_zero_of_trivial_action` and `resH1_zpowers_eq_zero_of_rho_eq_one` — the two
  free families above with that weakened hypothesis, so the family of subgroups on which
  `e1cMap` restricts to `0` unconditionally is strictly larger;
* `himg_reduction''` — the final sharpening: the input is only needed for the finite places with
  `decomp k A ⊄ ker (res k K)` and for the involutions `σ` with `res k K σ ≠ 1` and
  `R.ρ (res k K σ) ≠ 1` (the maximal family the Hilbert-90 method can reach);
* `himg_of_extDelta_input` — the reduction of the target to the single unconditional input below;
* `himg_of_ideles_input` — the same wiring for the *hypothesis* form of the input: if the two
  clauses hold for every `z` with `extToIdeles (e1aSyzShift N z) = 0`, then the target follows.
  The two clauses are exactly the delegated statements `SSGRoute/ExtChain/himgIdelesInput_fin` and
  `SSGRoute/ExtChain/himgIdelesInput_inf`.  (The two forms of the input are equivalent, by
  `PTdualControl.exists_extDelta_eq_of_extToIdeles_eq_zero` and the fact that `e1aSyzShift N` is an
  additive equivalence.)

**Session 13c: the involution half is PROVED, and the remaining input is one clause.**
`Work.SSGRoute.ExtChain.himgIdelesInput_inf`
(`Submission/Work/SSGRoute/ExtChain/himgIdelesInput_inf.lean`) is proved, sorry-free and
axiom-clean, with the statement exactly as requested.  Instantiating `himg_of_ideles_input` at it
gives, in the module `Submission.Work.SSGRoute.ExtChain.himgFromIdelesInput`,

  `Work.SSGRoute.ExtChain.himg_of_ideles_input_fin` — **the target's content modulo the
  finite-place clause alone** (that clause being the delegated `SSGRoute/ExtChain/himgIdelesInput_fin`).

That instantiating module sits *above* this file, and it has to: the import cone of
`himgIdelesInput_inf` contains `ExtChain.freeCoverSES_lattice`, which imports the node
`SSGRoute.ext_sha2_bridge`, which imports *this* file — so this file cannot import the child
(build cycle).  Consequence: the target's `sorry` below is *derivable* (via
`himg_of_ideles_input_fin` + the finite-place clause) but cannot be discharged by an import from
here; closing the node `ext_sha2_bridge` is now a question of routing it through
`himgFromIdelesInput`.

The dévissage in the coefficient `E` (the alternative route to the same input) is designed in
`ExtChain/NOTE_devissage_E.md`; its base case is **proved**:
`Work.SSGRoute.ExtChain.subsingleton_ext_fpRegular` (`Ext²_G(𝔽_p[G], A) = 0` for the free
`𝔽_p[G]`-module, `ExtChain/subsingleton_ext_fpRegular.lean`), with the coefficient-level brick
`leftRegularReduceFun` in `ExtChain/ext_vanishing_fpRegular.lean`.

-/


namespace Work.SSGRoute.ExtChain

open CategoryTheory SSGRoute.PTExt
open scoped TensorProduct

set_option synthInstance.maxHeartbeats 4000000
set_option maxHeartbeats 2000000

attribute [local instance] Work.SSGRoute.freeCoverSES_finite

noncomputable section

variable {k : Type} [Field k] [NumberField k] {Ω : Type} [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω]
variable {K : IntermediateField k Ω} [FiniteDimensional k K] [IsGalois k K] [NumberField K]

/-- **The assembly half of `himg`.**  If `z ∈ Ext¹_{Gal(K/k)}(R,Kˣ)` (`R = ker (freeCover (E^∨(1)))`,
`E^∨(1) = DualMod p (E ⊗ T)`) satisfies `e1aSyzShift z = y` and the canonical `E1c` class
`e1cMap R z` restricts to `0` at the decomposition group of every finite place of `Ω` and at the
group generated by every involution, then `e1aChainC y` is the class of a locally trivial
continuous `2`-cocycle.

The two hypotheses are exactly the conclusion of the local comparison square `(★')` (see the module
doc). -/
theorem himg_reduction
    (p : ℕ) [Fact p.Prime]
    (ζ : Ω) (hζ : IsPrimitiveRoot ζ p) (hζK : ζ ∈ K)
    (T : Type) [AddCommGroup T] [Module (ZMod p) T] [DistribMulAction (K ≃ₐ[k] K) T]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) T]
    (hT : SSGRoute.IsCyclotomicDual p (T := T) (SSGRoute.res k K) ζ)
    (E : Type) [AddCommGroup E] [Module (ZMod p) E] [DistribMulAction (K ≃ₐ[k] K) E]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) E] [Finite E]
    (y : CategoryTheory.Abelian.Ext.{0}
      (Work.SSGRoute.SSGStage.e1aN0 p k Ω K T E) (SSGRoute.PTExt.unitsK k K) 2)
    (z : CategoryTheory.Abelian.Ext.{0}
      (CategoryTheory.Limits.kernel (Work.SSGRoute.freeCover (Work.SSGRoute.SSGStage.e1aN0 p k Ω K T E)))
      (SSGRoute.PTExt.unitsK k K) 1)
    [hRfin : Module.Finite ℤ ↥(CategoryTheory.Limits.kernel
      (Work.SSGRoute.freeCover (Work.SSGRoute.SSGStage.e1aN0 p k Ω K T E)))]
    (hz : Work.SSGRoute.ExtChain.e1aSyzShift (k := k) (K := K)
      (Work.SSGRoute.SSGStage.e1aN0 p k Ω K T E) z = y)
    (hfin : ∀ (A : ValuationSubring Ω), SSGRoute.IsFinPlace k A →
      Work.SSGRoute.PT.H2Fin.resH1 (SSGRoute.decomp k A)
        (Work.SSGRoute.homCoind k Ω K
          (CategoryTheory.Limits.kernel (Work.SSGRoute.freeCover (Work.SSGRoute.SSGStage.e1aN0 p k Ω K T E))))
        (Work.SSGRoute.ExtChain.e1cMap
          (CategoryTheory.Limits.kernel (Work.SSGRoute.freeCover (Work.SSGRoute.SSGStage.e1aN0 p k Ω K T E))) z) = 0)
    (hinf : ∀ (σ : Ω ≃ₐ[k] Ω), σ ^ 2 = 1 →
      Work.SSGRoute.PT.H2Fin.resH1 (Subgroup.zpowers σ)
        (Work.SSGRoute.homCoind k Ω K
          (CategoryTheory.Limits.kernel (Work.SSGRoute.freeCover (Work.SSGRoute.SSGStage.e1aN0 p k Ω K T E))))
        (Work.SSGRoute.ExtChain.e1cMap
          (CategoryTheory.Limits.kernel (Work.SSGRoute.freeCover (Work.SSGRoute.SSGStage.e1aN0 p k Ω K T E))) z) = 0) :
    ∃ c : ↥(SSGRoute.Z2loc p k Ω K E),
      @Work.AbsoluteKummer.H2π (Ω ≃ₐ[k] Ω) E _ _ _
        (DistribMulAction.compHom E (SSGRoute.res k K))
        (Work.SSGRoute.PT.Z2ofZ2loc p k Ω K E c) =
      Work.SSGRoute.PT.e1aChainC p k Ω K ζ hζ hζK T hT E y := by

  letI : DistribMulAction (Ω ≃ₐ[k] Ω) E := DistribMulAction.compHom E (SSGRoute.res k K)
  haveI hTfin : Finite T := Work.SSGRoute.ExtChain.e1aFiniteT p k Ω K ζ T hT
  haveI hNfin : Finite (Work.SSGRoute.SSGStage.e1aN0 p k Ω K T E).V :=
    Work.SSGRoute.PT.finite_dualMod_tensor p E T
  -- ### step 1
  have hstep : ∀ (D : Subgroup (Ω ≃ₐ[k] Ω)),
      Work.SSGRoute.PT.H2Fin.resH1 D (Work.SSGRoute.homCoind k Ω K (CategoryTheory.Limits.kernel (Work.SSGRoute.freeCover (Work.SSGRoute.SSGStage.e1aN0 p k Ω K T E)))) (Work.SSGRoute.ExtChain.e1cMap (CategoryTheory.Limits.kernel (Work.SSGRoute.freeCover (Work.SSGRoute.SSGStage.e1aN0 p k Ω K T E))) z) = 0 →
      @Work.AbsoluteKummer.akRes (Ω ≃ₐ[k] Ω) _ _ D E _ (DistribMulAction.compHom E (SSGRoute.res k K)) (Work.SSGRoute.PT.e1aChainC p k Ω K ζ hζ hζK T hT E y) = 0 := by
    intro D hD
    have hy : (Work.SSGRoute.ExtChain.e1aSyzShift (k := k) (K := K) (Work.SSGRoute.SSGStage.e1aN0 p k Ω K T E)).symm y = z :=
      (Work.SSGRoute.ExtChain.e1aSyzShift (k := k) (K := K) (Work.SSGRoute.SSGStage.e1aN0 p k Ω K T E)).symm_apply_eq.mpr hz.symm
    have hH : (Work.SSGRoute.PT.e1aChainH (k := k) (Ω := Ω) (K := K) (Work.SSGRoute.SSGStage.e1aN0 p k Ω K T E) y)
        = Work.SSGRoute.ExtChain.e1aDelta (k := k) (Ω := Ω) (K := K) (Work.SSGRoute.SSGStage.e1aN0 p k Ω K T E) (Work.SSGRoute.ExtChain.e1cEquiv (CategoryTheory.Limits.kernel (Work.SSGRoute.freeCover (Work.SSGRoute.SSGStage.e1aN0 p k Ω K T E))) z) := by
      rw [Work.SSGRoute.PT.e1aChainH_apply, hy]
    have hres : Work.SSGRoute.PT.resH2 D (Work.SSGRoute.PT.e1aChainH (k := k) (Ω := Ω) (K := K) (Work.SSGRoute.SSGStage.e1aN0 p k Ω K T E) y) = 0 := by
      rw [hH, show Work.SSGRoute.ExtChain.e1aDelta (k := k) (Ω := Ω) (K := K) (Work.SSGRoute.SSGStage.e1aN0 p k Ω K T E)
          = (Work.SSGRoute.ExtChain.e1aSES (k := k) (Ω := Ω) (K := K) (Work.SSGRoute.SSGStage.e1aN0 p k Ω K T E)).deltaH2 from rfl]
      rw [Work.SSGRoute.ExtChain.deltaH2_restriction
        (Work.SSGRoute.ExtChain.e1aSES (k := k) (Ω := Ω) (K := K) (Work.SSGRoute.SSGStage.e1aN0 p k Ω K T E)) D (Work.SSGRoute.ExtChain.e1cEquiv (CategoryTheory.Limits.kernel (Work.SSGRoute.freeCover (Work.SSGRoute.SSGStage.e1aN0 p k Ω K T E))) z)]
      rw [show (Work.SSGRoute.ExtChain.e1cEquiv (CategoryTheory.Limits.kernel (Work.SSGRoute.freeCover (Work.SSGRoute.SSGStage.e1aN0 p k Ω K T E))) z) = (Work.SSGRoute.ExtChain.e1cMap (CategoryTheory.Limits.kernel (Work.SSGRoute.freeCover (Work.SSGRoute.SSGStage.e1aN0 p k Ω K T E))) z) from rfl]
      rw [hD, map_zero]
    have hakH : @Work.AbsoluteKummer.akRes (Ω ≃ₐ[k] Ω) _ _ D (Work.SSGRoute.homCoind k Ω K (Work.SSGRoute.SSGStage.e1aN0 p k Ω K T E)) _
        (Work.SSGRoute.homCoind.instDistribMulActionAlgEquiv (Work.SSGRoute.SSGStage.e1aN0 p k Ω K T E)) (Work.SSGRoute.PT.e1aChainH (k := k) (Ω := Ω) (K := K) (Work.SSGRoute.SSGStage.e1aN0 p k Ω K T E) y) = 0 := by
      rw [Work.SSGRoute.SSGStage.akRes_eq_resH2 D (Work.SSGRoute.homCoind k Ω K (Work.SSGRoute.SSGStage.e1aN0 p k Ω K T E))]
      exact hres
    have hC : (Work.SSGRoute.PT.e1aChainC p k Ω K ζ hζ hζK T hT E y) = @Work.AbsoluteKummer.mapH2 (Ω ≃ₐ[k] Ω) (Work.SSGRoute.homCoind k Ω K (Work.SSGRoute.SSGStage.e1aN0 p k Ω K T E)) _ _
            (Work.SSGRoute.homCoind.instAddCommGroup (Work.SSGRoute.SSGStage.e1aN0 p k Ω K T E))
            (Work.SSGRoute.homCoind.instDistribMulActionAlgEquiv (Work.SSGRoute.SSGStage.e1aN0 p k Ω K T E)) E _
            (DistribMulAction.compHom E (SSGRoute.res k K))
            ((Work.SSGRoute.ExtChain.e1aCoeffNat p k Ω K ζ hζ hζK T hT E)).symm.toAddMonoidHom (fun σ n => Work.SSGRoute.ExtChain.e1aCoeffNat_symm_equivariant p k Ω K ζ hζ hζK T hT E σ n) (Work.SSGRoute.PT.e1aChainH (k := k) (Ω := Ω) (K := K) (Work.SSGRoute.SSGStage.e1aN0 p k Ω K T E) y) := rfl
    rw [hC, Work.AbsoluteKummer.akRes_mapH2 D ((Work.SSGRoute.ExtChain.e1aCoeffNat p k Ω K ζ hζ hζK T hT E)).symm.toAddMonoidHom (fun σ n => Work.SSGRoute.ExtChain.e1aCoeffNat_symm_equivariant p k Ω K ζ hζ hζK T hT E σ n) (Work.SSGRoute.PT.e1aChainH (k := k) (Ω := Ω) (K := K) (Work.SSGRoute.SSGStage.e1aN0 p k Ω K T E) y)]
    rw [hakH, map_zero]
  -- ### step 2
  obtain ⟨c₀, hc₀⟩ := Work.SSGRoute.ExtChain.h2π_surjective_aux
    (G := Ω ≃ₐ[k] Ω) (M := E) (Work.SSGRoute.PT.e1aChainC p k Ω K ζ hζ hζK T hT E y)
  have hc₀lc : Work.AbsoluteKummer.IsLocallyConstant c₀.1 := c₀.2.2
  have hc₀cyc : c₀.1 ∈
      @Work.GroupCohomology.Z2 (Ω ≃ₐ[k] Ω) E _ _ (DistribMulAction.compHom E (SSGRoute.res k K)) :=
    c₀.2.1
  have hloc : SSGRoute.IsLocConst2 (fun g h : Ω ≃ₐ[k] Ω => c₀.1 (g, h)) := by
    have hf : Work.AbsoluteKummer.IsLocallyConstant
        (fun p : ↥(⊤ : Subgroup (Ω ≃ₐ[k] Ω)) × ↥(⊤ : Subgroup (Ω ≃ₐ[k] Ω)) =>
          c₀.1 (p.1.1, p.2.1)) :=
      Work.SSGRoute.isLocallyConstant_comp_continuous hc₀lc (by fun_prop)
    obtain ⟨U, hUo, hU⟩ := Work.SSGRoute.exists_openSubgroup_pair_mul_eq_of_isLocallyConstant
      k Ω ⊤ isClosed_univ (f := fun p : ↥(⊤ : Subgroup (Ω ≃ₐ[k] Ω)) × ↥(⊤ : Subgroup (Ω ≃ₐ[k] Ω)) =>
        c₀.1 (p.1.1, p.2.1)) hf
    refine ⟨U, hUo, ?_⟩
    intro g h u v hu hv
    have h := hU ⟨g, trivial⟩ ⟨h, trivial⟩ u v trivial trivial hu hv
    simpa using h
  have hcl : ∀ (σ : Ω ≃ₐ[k] Ω), σ ^ 2 = 1 →
      IsClosed ((Subgroup.zpowers σ : Subgroup (Ω ≃ₐ[k] Ω)) : Set (Ω ≃ₐ[k] Ω)) := by
    intro σ hσ
    refine Set.Finite.isClosed (Set.Finite.subset
      (Set.Finite.insert σ (Set.finite_singleton (1 : Ω ≃ₐ[k] Ω))) ?_)
    intro x hx
    rw [Set.mem_insert_iff, Set.mem_singleton_iff]
    obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
    have h1 : σ ^ m = σ ^ (m % ((2 : ℕ) : ℤ)) :=
      zpow_eq_zpow_emod m (show σ ^ (((2 : ℕ) : ℤ)) = 1 by rw [zpow_natCast]; exact hσ)
    have h0 := Int.emod_nonneg m (by norm_num : (2 : ℤ) ≠ 0)
    have h2 := Int.emod_lt_of_pos m (by norm_num : (0 : ℤ) < 2)
    rw [h1]
    have h01 : m % ((2 : ℕ) : ℤ) = 0 ∨ m % ((2 : ℕ) : ℤ) = 1 := by omega
    rcases h01 with h | h
    · right; rw [h, zpow_zero]
    · left; rw [h, zpow_one]
  -- ### step 3
  have hfin' : ∀ (A : ValuationSubring Ω), SSGRoute.IsFinPlace k A →
      SSGRoute.IsCoboundary2On (SSGRoute.res k K) (SSGRoute.decomp k A)
        (fun g h => c₀.1 (g, h)) := by
    intro A hA
    refine Work.SSGRoute.SSGStage.isCoboundary2On_of_akRes_H2π_eq_zero p K ζ hζ hζK T hT E
      (SSGRoute.decomp k A) (Work.SSGRoute.HS.isClosed_decomp A) c₀ ?_
    rw [hc₀]
    exact hstep (SSGRoute.decomp k A) (hfin A hA)
  have hinf' : ∀ (σ : Ω ≃ₐ[k] Ω), σ ^ 2 = 1 →
      SSGRoute.IsCoboundary2On (SSGRoute.res k K) (Subgroup.zpowers σ)
        (fun g h => c₀.1 (g, h)) := by
    intro σ hσ
    refine Work.SSGRoute.SSGStage.isCoboundary2On_of_akRes_H2π_eq_zero p K ζ hζ hζK T hT E
      (Subgroup.zpowers σ) (hcl σ hσ) c₀ ?_
    rw [hc₀]
    exact hstep (Subgroup.zpowers σ) (hinf σ hσ)
  have hcyc : SSGRoute.IsCocycle2 (SSGRoute.res k K) (fun g h : Ω ≃ₐ[k] Ω => c₀.1 (g, h)) :=
    (Work.SSGRoute.bridge_isCocycle2_mem_Z2 (SSGRoute.res k K) c₀.1).mpr hc₀cyc
  refine ⟨⟨fun g h => c₀.1 (g, h), hcyc, hloc, hfin', hinf'⟩, ?_⟩
  have hsub : Work.SSGRoute.PT.Z2ofZ2loc p k Ω K E
      ⟨fun g h => c₀.1 (g, h), hcyc, hloc, hfin', hinf'⟩ = c₀ :=
    Subtype.ext (funext fun q => rfl)
  rw [hsub]
  exact hc₀


/-! ## The two classes of subgroups for which the required vanishing is *free*

`himg_reduction` above reduces the target to the two families of subgroups
`decomp k A` (finite places) and `⟨σ⟩` (involutions).  For two large subfamilies the vanishing
`resH1_D (e1cMap R z) = 0` is *unconditional*: whenever `D ≤ ker (res k K)`, i.e. whenever `D`
fixes `K` pointwise.  The reason is pure Hilbert 90: `D` then acts trivially on the carrier `R.V`,
so `homCoind k Ω K R = Hom_ℤ(R.V, Ωˣ)` is a finite product of copies of `Ωˣ` with the valuewise
`D`-action, and `H¹(D, Ωˣ) = 0` because `Ω / Ω^D` is a Galois extension
(`Work.SSGRoute.PT.bropenHilbert90ClosedSubgroup`).  This is the brick
`Work.SSGRoute.ExtChain.subsingletonH1_homCoind_of_le_ker`. -/

/-- **The `E1c` dictionary vanishes at every closed subgroup fixing `K`.** -/
theorem resH1_e1cMap_eq_zero_of_le_ker
    (R : Rep.{0} Coeff (K ≃ₐ[k] K)) [Module.Finite ℤ R.V] [Module.Free ℤ R.V]
    (z : CategoryTheory.Abelian.Ext.{0} R (SSGRoute.PTExt.unitsK k K) 1)
    (D : Subgroup (Ω ≃ₐ[k] Ω)) (hDcl : IsClosed ((D : Set (Ω ≃ₐ[k] Ω))))
    (hD : D ≤ (SSGRoute.res k K).ker) :
    Work.SSGRoute.PT.H2Fin.resH1 D (Work.SSGRoute.homCoind k Ω K R)
      (Work.SSGRoute.ExtChain.e1cMap R z) = 0 := by
  haveI := Work.SSGRoute.ExtChain.subsingletonH1_homCoind_of_le_ker
    (k := k) (Ω := Ω) (K := K) R D hDcl hD
  exact Subsingleton.elim _ _

/-- **The `E1c` class vanishes on `⟨σ⟩` for every involution `σ` fixing `K`.**  In particular for
every involution in the kernel of `res k K`, i.e. for every involution of `Gal(Ω/K) ≤ Gal(Ω/k)`;
these are "free" for `himg` (no arithmetic input needed). -/
theorem resH1_zpowers_eq_zero_of_res_eq_one
    (R : Rep.{0} Coeff (K ≃ₐ[k] K)) [Module.Finite ℤ R.V] [Module.Free ℤ R.V]
    (z : CategoryTheory.Abelian.Ext.{0} R (SSGRoute.PTExt.unitsK k K) 1)
    (σ : Ω ≃ₐ[k] Ω) (hσ : σ ^ 2 = 1) (h1 : SSGRoute.res k K σ = 1) :
    Work.SSGRoute.PT.H2Fin.resH1 (Subgroup.zpowers σ)
      (Work.SSGRoute.homCoind k Ω K R)
      (Work.SSGRoute.ExtChain.e1cMap R z) = 0 := by
  have hcl : IsClosed ((Subgroup.zpowers σ : Subgroup (Ω ≃ₐ[k] Ω)) : Set (Ω ≃ₐ[k] Ω)) := by
    refine Set.Finite.isClosed (Set.Finite.subset
      (Set.Finite.insert σ (Set.finite_singleton (1 : Ω ≃ₐ[k] Ω))) ?_)
    intro x hx
    rw [Set.mem_insert_iff, Set.mem_singleton_iff]
    obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
    have h1' : σ ^ m = σ ^ (m % ((2 : ℕ) : ℤ)) :=
      zpow_eq_zpow_emod m (show σ ^ (((2 : ℕ) : ℤ)) = 1 by rw [zpow_natCast]; exact hσ)
    have h0 := Int.emod_nonneg m (by norm_num : (2 : ℤ) ≠ 0)
    have h2 := Int.emod_lt_of_pos m (by norm_num : (0 : ℤ) < 2)
    rw [h1']
    rcases (by omega : m % ((2 : ℕ) : ℤ) = 0 ∨ m % ((2 : ℕ) : ℤ) = 1) with h | h
    · right; rw [h, zpow_zero]
    · left; rw [h, zpow_one]
  have hle : Subgroup.zpowers σ ≤ (SSGRoute.res k K).ker :=
    Subgroup.zpowers_le.mpr (by simpa using h1)
  exact resH1_e1cMap_eq_zero_of_le_ker (k := k) (Ω := Ω) (K := K) R z _ hcl hle


/-- **The `E1c` dictionary vanishes at every closed subgroup acting trivially on the carrier.**

This is `resH1_e1cMap_eq_zero_of_le_ker` with the hypothesis weakened: only the *effect* of
`D ≤ ker (res k K)` on the `D`-module `R.V` is used, namely that `D` acts on it trivially.  It
therefore applies to subgroups which do **not** fix `K` but happen to act trivially on `R.V` — e.g.
involutions `σ` with `res k K σ ≠ 1` which act trivially on the carrier (the underlying vanishing
`Subsingleton (H¹(D, homCoind k Ω K R))` is
`Work.SSGRoute.ExtChain.subsingletonH1_homCoind_of_trivial_action`, whose proof only needs
Hilbert 90 at the closed subgroup `D` together with the triviality of the action on `R.V`). -/
theorem resH1_e1cMap_eq_zero_of_trivial_action
    (R : Rep.{0} Coeff (K ≃ₐ[k] K)) [Module.Finite ℤ R.V] [Module.Free ℤ R.V]
    (z : CategoryTheory.Abelian.Ext.{0} R (SSGRoute.PTExt.unitsK k K) 1)
    (D : Subgroup (Ω ≃ₐ[k] Ω)) (hDcl : IsClosed ((D : Set (Ω ≃ₐ[k] Ω))))
    (hact : ∀ δ : ↥D, R.ρ (SSGRoute.res k K (δ : Ω ≃ₐ[k] Ω)) = 1) :
    Work.SSGRoute.PT.H2Fin.resH1 D (Work.SSGRoute.homCoind k Ω K R)
      (Work.SSGRoute.ExtChain.e1cMap R z) = 0 := by
  haveI := Work.SSGRoute.ExtChain.subsingletonH1_homCoind_of_trivial_action
    (k := k) (Ω := Ω) (K := K) R D hDcl hact
  exact Subsingleton.elim _ _

/-- **The `E1c` class vanishes on `⟨σ⟩` for every involution acting trivially on the carrier.**

`resH1_zpowers_eq_zero_of_res_eq_one` is the special case `R.ρ (res k K σ) = 1`; here the
hypothesis is only the triviality of `σ`'s action on `R.V`. -/
theorem resH1_zpowers_eq_zero_of_rho_eq_one
    (R : Rep.{0} Coeff (K ≃ₐ[k] K)) [Module.Finite ℤ R.V] [Module.Free ℤ R.V]
    (z : CategoryTheory.Abelian.Ext.{0} R (SSGRoute.PTExt.unitsK k K) 1)
    (σ : Ω ≃ₐ[k] Ω) (hσ : σ ^ 2 = 1) (hact : R.ρ (SSGRoute.res k K σ) = 1) :
    Work.SSGRoute.PT.H2Fin.resH1 (Subgroup.zpowers σ)
      (Work.SSGRoute.homCoind k Ω K R)
      (Work.SSGRoute.ExtChain.e1cMap R z) = 0 := by
  have hcl : IsClosed ((Subgroup.zpowers σ : Subgroup (Ω ≃ₐ[k] Ω)) : Set (Ω ≃ₐ[k] Ω)) := by
    refine Set.Finite.isClosed (Set.Finite.subset
      (Set.Finite.insert σ (Set.finite_singleton (1 : Ω ≃ₐ[k] Ω))) ?_)
    intro x hx
    rw [Set.mem_insert_iff, Set.mem_singleton_iff]
    obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
    have h1' : σ ^ m = σ ^ (m % ((2 : ℕ) : ℤ)) :=
      zpow_eq_zpow_emod m (show σ ^ (((2 : ℕ) : ℤ)) = 1 by rw [zpow_natCast]; exact hσ)
    have h0 := Int.emod_nonneg m (by norm_num : (2 : ℤ) ≠ 0)
    have h2 := Int.emod_lt_of_pos m (by norm_num : (0 : ℤ) < 2)
    rw [h1']
    rcases (by omega : m % ((2 : ℕ) : ℤ) = 0 ∨ m % ((2 : ℕ) : ℤ) = 1) with h | h
    · right; rw [h, zpow_zero]
    · left; rw [h, zpow_one]
  refine resH1_e1cMap_eq_zero_of_trivial_action (k := k) (Ω := Ω) (K := K) R z _
    hcl ?_
  intro δ
  obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp δ.2
  have h2 : (δ : Ω ≃ₐ[k] Ω) = σ ^ (m % ((2 : ℕ) : ℤ)) := by
    rw [← hm, zpow_eq_zpow_emod m (show σ ^ (((2 : ℕ) : ℤ)) = 1 by rw [zpow_natCast]; exact hσ)]
  rcases (by omega : m % ((2 : ℕ) : ℤ) = 0 ∨ m % ((2 : ℕ) : ℤ) = 1) with h | h
  · rw [h2, h, zpow_zero, map_one, map_one]
  · rw [h2, h, zpow_one, hact]


/-- **`himg` reduced to the *non-split* finite places and the involutions *not* fixing `K`.**

This is `himg_reduction` with two of its hypotheses weakened using the two free vanishings above:
the finite places `A` whose decomposition group already fixes `K` (`decomp k A ≤ ker (res k K)`,
i.e. primes of `K` that split completely) and the involutions of `Gal(Ω/K)` need no input at all.
What remains is exactly the arithmetic content of `himg`: the finite places with a nontrivial
residue/decomposition structure and the archimedean involutions with `res k K σ ≠ 1`. -/
theorem himg_reduction' (p : ℕ) [Fact p.Prime]
    (ζ : Ω) (hζ : IsPrimitiveRoot ζ p) (hζK : ζ ∈ K)
    (T : Type) [AddCommGroup T] [Module (ZMod p) T] [DistribMulAction (K ≃ₐ[k] K) T]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) T]
    (hT : SSGRoute.IsCyclotomicDual p (T := T) (SSGRoute.res k K) ζ)
    (E : Type) [AddCommGroup E] [Module (ZMod p) E] [DistribMulAction (K ≃ₐ[k] K) E]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) E] [Finite E]
    (y : CategoryTheory.Abelian.Ext.{0}
      (Work.SSGRoute.SSGStage.e1aN0 p k Ω K T E) (SSGRoute.PTExt.unitsK k K) 2)
    (z : CategoryTheory.Abelian.Ext.{0}
      (CategoryTheory.Limits.kernel (Work.SSGRoute.freeCover (Work.SSGRoute.SSGStage.e1aN0 p k Ω K T E)))
      (SSGRoute.PTExt.unitsK k K) 1)
    [hRfin : Module.Finite ℤ ↥(CategoryTheory.Limits.kernel
      (Work.SSGRoute.freeCover (Work.SSGRoute.SSGStage.e1aN0 p k Ω K T E)))]
    (hz : Work.SSGRoute.ExtChain.e1aSyzShift (k := k) (K := K)
      (Work.SSGRoute.SSGStage.e1aN0 p k Ω K T E) z = y)
    (hfin : ∀ (A : ValuationSubring Ω), SSGRoute.IsFinPlace k A →
      ¬ (SSGRoute.decomp k A ≤ (SSGRoute.res k K).ker) →
      Work.SSGRoute.PT.H2Fin.resH1 (SSGRoute.decomp k A)
        (Work.SSGRoute.homCoind k Ω K
          (CategoryTheory.Limits.kernel (Work.SSGRoute.freeCover (Work.SSGRoute.SSGStage.e1aN0 p k Ω K T E))))
        (Work.SSGRoute.ExtChain.e1cMap
          (CategoryTheory.Limits.kernel (Work.SSGRoute.freeCover (Work.SSGRoute.SSGStage.e1aN0 p k Ω K T E))) z) = 0)
    (hinf : ∀ (σ : Ω ≃ₐ[k] Ω), σ ^ 2 = 1 → SSGRoute.res k K σ ≠ 1 →
      Work.SSGRoute.PT.H2Fin.resH1 (Subgroup.zpowers σ)
        (Work.SSGRoute.homCoind k Ω K
          (CategoryTheory.Limits.kernel (Work.SSGRoute.freeCover (Work.SSGRoute.SSGStage.e1aN0 p k Ω K T E))))
        (Work.SSGRoute.ExtChain.e1cMap
          (CategoryTheory.Limits.kernel (Work.SSGRoute.freeCover (Work.SSGRoute.SSGStage.e1aN0 p k Ω K T E))) z) = 0) :
    ∃ c : ↥(SSGRoute.Z2loc p k Ω K E),
      @Work.AbsoluteKummer.H2π (Ω ≃ₐ[k] Ω) E _ _ _
        (DistribMulAction.compHom E (SSGRoute.res k K))
        (Work.SSGRoute.PT.Z2ofZ2loc p k Ω K E c) =
      Work.SSGRoute.PT.e1aChainC p k Ω K ζ hζ hζK T hT E y := by
  haveI hTfin : Finite T := Work.SSGRoute.ExtChain.e1aFiniteT p k Ω K ζ T hT
  haveI hNfin : Finite (Work.SSGRoute.SSGStage.e1aN0 p k Ω K T E).V :=
    Work.SSGRoute.PT.finite_dualMod_tensor p E T
  have hmono : Function.Injective
      (Work.SSGRoute.ExtChain.kappa (Work.SSGRoute.SSGStage.e1aN0 p k Ω K T E)) :=
    (Rep.mono_iff_injective
      (CategoryTheory.Limits.kernel.ι
        (Work.SSGRoute.freeCover (Work.SSGRoute.SSGStage.e1aN0 p k Ω K T E)))).mp inferInstance
  haveI htf : Module.IsTorsionFree ℤ ↥(CategoryTheory.Limits.kernel
      (Work.SSGRoute.freeCover (Work.SSGRoute.SSGStage.e1aN0 p k Ω K T E))) :=
    hmono.moduleIsTorsionFree
      (Work.SSGRoute.ExtChain.kappa (Work.SSGRoute.SSGStage.e1aN0 p k Ω K T E))
      (fun r m =>
        (Work.SSGRoute.ExtChain.kappa (Work.SSGRoute.SSGStage.e1aN0 p k Ω K T E)).map_zsmul r m)
  haveI hfree : Module.Free ℤ ↥(CategoryTheory.Limits.kernel
      (Work.SSGRoute.freeCover (Work.SSGRoute.SSGStage.e1aN0 p k Ω K T E))) :=
    Module.free_of_finite_type_torsion_free'
  refine Work.SSGRoute.ExtChain.himg_reduction (k := k) (Ω := Ω) (K := K) p ζ hζ hζK T hT E
    y z hz ?_ ?_
  · intro A hA
    by_cases hsplit : SSGRoute.decomp k A ≤ (SSGRoute.res k K).ker
    · exact resH1_e1cMap_eq_zero_of_le_ker (k := k) (Ω := Ω) (K := K) _ z _
        (Work.SSGRoute.HS.isClosed_decomp A) hsplit
    · exact hfin A hA hsplit
  · intro σ hσ
    by_cases htriv : SSGRoute.res k K σ = 1
    · exact resH1_zpowers_eq_zero_of_res_eq_one (k := k) (Ω := Ω) (K := K) _ z σ hσ htriv
    · exact hinf σ hσ htriv


/-- **`himg` reduced to the involutions that are *non-trivial on the carrier*.**

`himg_reduction'` already disposes of every involution with `res k K σ = 1`.  The new free family
`resH1_zpowers_eq_zero_of_rho_eq_one` (from `subsingletonH1_homCoind_of_trivial_action`) disposes of
every involution that acts trivially on `R.V` — which is a strictly weaker hypothesis, and is
exactly the maximal family this method can reach.  So the input is only needed for the finite places
with `decomp k A ⊄ ker (res k K)` and for the involutions with `R.ρ (res k K σ) ≠ 1`. -/
theorem himg_reduction'' (p : ℕ) [Fact p.Prime]
    (ζ : Ω) (hζ : IsPrimitiveRoot ζ p) (hζK : ζ ∈ K)
    (T : Type) [AddCommGroup T] [Module (ZMod p) T] [DistribMulAction (K ≃ₐ[k] K) T]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) T]
    (hT : SSGRoute.IsCyclotomicDual p (T := T) (SSGRoute.res k K) ζ)
    (E : Type) [AddCommGroup E] [Module (ZMod p) E] [DistribMulAction (K ≃ₐ[k] K) E]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) E] [Finite E]
    (y : CategoryTheory.Abelian.Ext.{0}
      (Work.SSGRoute.SSGStage.e1aN0 p k Ω K T E) (SSGRoute.PTExt.unitsK k K) 2)
    (z : CategoryTheory.Abelian.Ext.{0}
      (CategoryTheory.Limits.kernel (Work.SSGRoute.freeCover (Work.SSGRoute.SSGStage.e1aN0 p k Ω K T E)))
      (SSGRoute.PTExt.unitsK k K) 1)
    [hRfin : Module.Finite ℤ ↥(CategoryTheory.Limits.kernel
      (Work.SSGRoute.freeCover (Work.SSGRoute.SSGStage.e1aN0 p k Ω K T E)))]
    (hz : Work.SSGRoute.ExtChain.e1aSyzShift (k := k) (K := K)
      (Work.SSGRoute.SSGStage.e1aN0 p k Ω K T E) z = y)
    (hfin : ∀ (A : ValuationSubring Ω), SSGRoute.IsFinPlace k A →
      ¬ (SSGRoute.decomp k A ≤ (SSGRoute.res k K).ker) →
      Work.SSGRoute.PT.H2Fin.resH1 (SSGRoute.decomp k A)
        (Work.SSGRoute.homCoind k Ω K
          (CategoryTheory.Limits.kernel (Work.SSGRoute.freeCover (Work.SSGRoute.SSGStage.e1aN0 p k Ω K T E))))
        (Work.SSGRoute.ExtChain.e1cMap
          (CategoryTheory.Limits.kernel (Work.SSGRoute.freeCover (Work.SSGRoute.SSGStage.e1aN0 p k Ω K T E))) z) = 0)
    (hinf : ∀ (σ : Ω ≃ₐ[k] Ω), σ ^ 2 = 1 → SSGRoute.res k K σ ≠ 1 →
      (CategoryTheory.Limits.kernel
        (Work.SSGRoute.freeCover (Work.SSGRoute.SSGStage.e1aN0 p k Ω K T E))).ρ
          (SSGRoute.res k K σ) ≠ 1 →
      Work.SSGRoute.PT.H2Fin.resH1 (Subgroup.zpowers σ)
        (Work.SSGRoute.homCoind k Ω K
          (CategoryTheory.Limits.kernel (Work.SSGRoute.freeCover (Work.SSGRoute.SSGStage.e1aN0 p k Ω K T E))))
        (Work.SSGRoute.ExtChain.e1cMap
          (CategoryTheory.Limits.kernel (Work.SSGRoute.freeCover (Work.SSGRoute.SSGStage.e1aN0 p k Ω K T E))) z) = 0) :
    ∃ c : ↥(SSGRoute.Z2loc p k Ω K E),
      @Work.AbsoluteKummer.H2π (Ω ≃ₐ[k] Ω) E _ _ _
        (DistribMulAction.compHom E (SSGRoute.res k K))
        (Work.SSGRoute.PT.Z2ofZ2loc p k Ω K E c) =
      Work.SSGRoute.PT.e1aChainC p k Ω K ζ hζ hζK T hT E y := by
  haveI hTfin : Finite T := Work.SSGRoute.ExtChain.e1aFiniteT p k Ω K ζ T hT
  haveI hNfin : Finite (Work.SSGRoute.SSGStage.e1aN0 p k Ω K T E).V :=
    Work.SSGRoute.PT.finite_dualMod_tensor p E T
  have hmono : Function.Injective
      (Work.SSGRoute.ExtChain.kappa (Work.SSGRoute.SSGStage.e1aN0 p k Ω K T E)) :=
    (Rep.mono_iff_injective
      (CategoryTheory.Limits.kernel.ι
        (Work.SSGRoute.freeCover (Work.SSGRoute.SSGStage.e1aN0 p k Ω K T E)))).mp inferInstance
  haveI htf : Module.IsTorsionFree ℤ ↥(CategoryTheory.Limits.kernel
      (Work.SSGRoute.freeCover (Work.SSGRoute.SSGStage.e1aN0 p k Ω K T E))) :=
    hmono.moduleIsTorsionFree
      (Work.SSGRoute.ExtChain.kappa (Work.SSGRoute.SSGStage.e1aN0 p k Ω K T E))
      (fun r m =>
        (Work.SSGRoute.ExtChain.kappa (Work.SSGRoute.SSGStage.e1aN0 p k Ω K T E)).map_zsmul r m)
  haveI hfree : Module.Free ℤ ↥(CategoryTheory.Limits.kernel
      (Work.SSGRoute.freeCover (Work.SSGRoute.SSGStage.e1aN0 p k Ω K T E))) :=
    Module.free_of_finite_type_torsion_free'
  refine himg_reduction' (k := k) (Ω := Ω) (K := K) p ζ hζ hζK T hT E y z hz hfin ?_
  intro σ hσ hnt
  by_cases hact : (CategoryTheory.Limits.kernel
      (Work.SSGRoute.freeCover (Work.SSGRoute.SSGStage.e1aN0 p k Ω K T E))).ρ
        (SSGRoute.res k K σ) = 1
  · exact resH1_zpowers_eq_zero_of_rho_eq_one (k := k) (Ω := Ω) (K := K) _ z σ hσ hact
  · exact hinf σ hσ hnt hact


/-! ## The single unconditional input the target is equivalent to

`extToIdeles y = 0` for `y ∈ Ext²_G(E^∨(1),Kˣ)` is, by the long exact sequence of the class
formation `0 → Kˣ → 𝕀_K → C_K → 0`, exactly the statement that `y` lies in the image of the
connecting map `extDelta : Ext¹_G(E^∨(1), C_K) → Ext²_G(E^∨(1), Kˣ)`
(`Work.SSGRoute.PTdualControl.exists_extDelta_eq_of_extToIdeles_eq_zero`, an on-disk *formal*
consequence of the exactness of the long exact sequence — no arithmetic).

Consequently the whole arithmetic content of the target is the **unconditional** statement

  `∀ x ∈ Ext¹_G(E^∨(1), C_K),  resH1_D (e1cMap_R ((e1aSyzShift N)⁻¹ (extDelta x))) = 0`

for the decomposition groups `D = decomp k A` of the finite places of `Ω` that are *not* completely
split, and for `D = ⟨σ⟩`, `σ² = 1`, `res k K σ ≠ 1`.  There is no longer any hypothesis to use: the
input is the vanishing of an explicit composite of canonical maps, namely

`Ext¹_G(E^∨(1),C_K) --extDelta--> Ext²_G(E^∨(1),Kˣ) --(e1aSyzShift N)⁻¹--> Ext¹_G(R,Kˣ)`
`  --e1cMap--> H¹(Γ, Hom_ℤ(R.V,Ωˣ)) --resH1_D--> H¹(D, Hom_ℤ(R.V,Ωˣ))`.

This is the sharpest known reduction of the target: the theorem below is a pure assembly (the
`extDelta`-exactness and `himg_reduction'`), so the target's `sorry` is *equivalent* to the input of
this theorem.

## Why the input cannot be weakened to a *per-place* statement (session 11, redone)

Writing `z = (e1aSyzShift N)⁻¹ y`, the localisation at a place `w` of `K` is
`z_w = (extRes_{D_w} z) ∘ mk₀ (unitsToLocalUnits k K w) ∈ Ext¹_{D_w}(res R, K_wˣ)` — values in the
**completion** `K_wˣ`.  The `resH1_{D_A}`-vanishing at a finite place `A | w`, on the other hand, is
(by the five-term sequence of `G_K ⊴ D_A`, whose `H¹`-term vanishes by
`subsingletonH1_homCoind_of_le_ker`) equivalent to the vanishing of a class in
`Ext¹_{D_q}(res R, (K·Ω^{D_A})ˣ)` — values in the **algebraic** field `K·Ω^{D_A}`, a *much smaller*
coefficient group than `K_wˣ` (the completion adds the ramification/one-units).  So `z_w = 0` is the
image of the correct condition under a non-injective coefficient change
`Ext¹_{D_q}(res R, (K·Ω^{D_A})ˣ) → Ext¹_{D_q}(res R, K_wˣ)`: the kernel of this map is the local
`Ш²`, which is *nonzero* (`k = ℚ`, `K = ℚ(i)`, `w | 3` inert, `N = ℤ`: the quaternion class
`(−1,−1)` is locally trivial but not zero over the decomposition field).  Hence no per-place form of
the input can hold; the `extDelta`-form above is the honest one. -/

/-- **The `himg` clause from the unconditional `extDelta`-input** (see the section docstring). -/
theorem himg_of_extDelta_input (p : ℕ) [Fact p.Prime]
    (ζ : Ω) (hζ : IsPrimitiveRoot ζ p) (hζK : ζ ∈ K)
    (T : Type) [AddCommGroup T] [Module (ZMod p) T] [DistribMulAction (K ≃ₐ[k] K) T]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) T]
    (hT : SSGRoute.IsCyclotomicDual p (T := T) (SSGRoute.res k K) ζ)
    (E : Type) [AddCommGroup E] [Module (ZMod p) E] [DistribMulAction (K ≃ₐ[k] K) E]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) E] [Finite E]
    [hRfin : Module.Finite ℤ ↥(CategoryTheory.Limits.kernel
      (Work.SSGRoute.freeCover (Work.SSGRoute.SSGStage.e1aN0 p k Ω K T E)))]
    (hfin : ∀ x : CategoryTheory.Abelian.Ext.{0}
        (Work.SSGRoute.SSGStage.e1aN0 p k Ω K T E) (SSGRoute.PTExt.classesK k K) 1,
      ∀ (A : ValuationSubring Ω), SSGRoute.IsFinPlace k A →
        ¬ (SSGRoute.decomp k A ≤ (SSGRoute.res k K).ker) →
        Work.SSGRoute.PT.H2Fin.resH1 (SSGRoute.decomp k A)
          (Work.SSGRoute.homCoind k Ω K
            (CategoryTheory.Limits.kernel
              (Work.SSGRoute.freeCover (Work.SSGRoute.SSGStage.e1aN0 p k Ω K T E))))
          (Work.SSGRoute.ExtChain.e1cMap
            (CategoryTheory.Limits.kernel
              (Work.SSGRoute.freeCover (Work.SSGRoute.SSGStage.e1aN0 p k Ω K T E)))
            ((Work.SSGRoute.ExtChain.e1aSyzShift (k := k) (K := K)
                (Work.SSGRoute.SSGStage.e1aN0 p k Ω K T E)).symm
              (SSGRoute.PTExt.extDelta (k := k) (K := ↥K) x))) = 0)
    (hinf : ∀ x : CategoryTheory.Abelian.Ext.{0}
        (Work.SSGRoute.SSGStage.e1aN0 p k Ω K T E) (SSGRoute.PTExt.classesK k K) 1,
      ∀ (σ : Ω ≃ₐ[k] Ω), σ ^ 2 = 1 → SSGRoute.res k K σ ≠ 1 →
        Work.SSGRoute.PT.H2Fin.resH1 (Subgroup.zpowers σ)
          (Work.SSGRoute.homCoind k Ω K
            (CategoryTheory.Limits.kernel
              (Work.SSGRoute.freeCover (Work.SSGRoute.SSGStage.e1aN0 p k Ω K T E))))
          (Work.SSGRoute.ExtChain.e1cMap
            (CategoryTheory.Limits.kernel
              (Work.SSGRoute.freeCover (Work.SSGRoute.SSGStage.e1aN0 p k Ω K T E)))
            ((Work.SSGRoute.ExtChain.e1aSyzShift (k := k) (K := K)
                (Work.SSGRoute.SSGStage.e1aN0 p k Ω K T E)).symm
              (SSGRoute.PTExt.extDelta (k := k) (K := ↥K) x))) = 0) :
    ∀ y : CategoryTheory.Abelian.Ext.{0} (SSGRoute.PTExt.modRep (K ≃ₐ[k] K)
        (Work.SSGRoute.DualMod p (TensorProduct (ZMod p) E T))) (SSGRoute.PTExt.unitsK k K) 2,
      SSGRoute.PTExt.extToIdeles (k := k) y = 0 →
        ∃ c : ↥(SSGRoute.Z2loc p k Ω K E),
          @Work.AbsoluteKummer.H2π (Ω ≃ₐ[k] Ω) E _ _ _
            (DistribMulAction.compHom E (SSGRoute.res k K))
            (Work.SSGRoute.PT.Z2ofZ2loc p k Ω K E c) =
          Work.SSGRoute.PT.e1aChainC p k Ω K ζ hζ hζK T hT E y := by
  intro y hy
  obtain ⟨x, hx⟩ := Work.SSGRoute.PTdualControl.exists_extDelta_eq_of_extToIdeles_eq_zero
    (k := k) (K := ↥K) (M := Work.SSGRoute.SSGStage.e1aN0 p k Ω K T E) (r := 1) y hy
  rw [← hx]
  refine himg_reduction' (k := k) (Ω := Ω) (K := K) p ζ hζ hζK T hT E
    (SSGRoute.PTExt.extDelta (k := k) (K := ↥K) x)
    ((Work.SSGRoute.ExtChain.e1aSyzShift (k := k) (K := K)
      (Work.SSGRoute.SSGStage.e1aN0 p k Ω K T E)).symm
      (SSGRoute.PTExt.extDelta (k := k) (K := ↥K) x))
    (AddEquiv.apply_symm_apply _ _) ?_ ?_
  · intro A hA hns
    exact hfin x A hA hns
  · intro σ hσ hnt
    exact hinf x σ hσ hnt


/-- **The `himg` clause from the `himgIdelesInput` form of the input.**  This is the *wiring* of the
target to the two delegated statements `SSGRoute/ExtChain/himgIdelesInput_fin` and
`…_inf`, whose hypothesis is the idèle localisation `extToIdeles (e1aSyzShift N z) = 0` — i.e.
`extToIdeles y = 0` for `y := e1aSyzShift N z`, which is exactly what `himg_reduction'` consumes.

The two forms of the input are equivalent: by
`Work.SSGRoute.PTdualControl.exists_extDelta_eq_of_extToIdeles_eq_zero` a class `z` satisfies
`extToIdeles (e1aSyzShift N z) = 0` exactly when `z = (e1aSyzShift N)⁻¹ (extDelta x)` for some
`x ∈ Ext¹_G(N, C_K)` (using that `e1aSyzShift N` is an additive equivalence). -/
theorem himg_of_ideles_input (p : ℕ) [Fact p.Prime]
    (ζ : Ω) (hζ : IsPrimitiveRoot ζ p) (hζK : ζ ∈ K)
    (T : Type) [AddCommGroup T] [Module (ZMod p) T] [DistribMulAction (K ≃ₐ[k] K) T]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) T]
    (hT : SSGRoute.IsCyclotomicDual p (T := T) (SSGRoute.res k K) ζ)
    (E : Type) [AddCommGroup E] [Module (ZMod p) E] [DistribMulAction (K ≃ₐ[k] K) E]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) E] [Finite E]
    [hRfin : Module.Finite ℤ ↥(CategoryTheory.Limits.kernel
      (Work.SSGRoute.freeCover (Work.SSGRoute.SSGStage.e1aN0 p k Ω K T E)))]
    (hfin : ∀ z : CategoryTheory.Abelian.Ext.{0}
        (CategoryTheory.Limits.kernel
          (Work.SSGRoute.freeCover (Work.SSGRoute.SSGStage.e1aN0 p k Ω K T E)))
        (SSGRoute.PTExt.unitsK k K) 1,
      SSGRoute.PTExt.extToIdeles (k := k)
        (Work.SSGRoute.ExtChain.e1aSyzShift (k := k) (K := K)
          (Work.SSGRoute.SSGStage.e1aN0 p k Ω K T E) z) = 0 →
      ∀ (A : ValuationSubring Ω), SSGRoute.IsFinPlace k A →
        ¬ (SSGRoute.decomp k A ≤ (SSGRoute.res k K).ker) →
        Work.SSGRoute.PT.H2Fin.resH1 (SSGRoute.decomp k A)
          (Work.SSGRoute.homCoind k Ω K
            (CategoryTheory.Limits.kernel
              (Work.SSGRoute.freeCover (Work.SSGRoute.SSGStage.e1aN0 p k Ω K T E))))
          (Work.SSGRoute.ExtChain.e1cMap
            (CategoryTheory.Limits.kernel
              (Work.SSGRoute.freeCover (Work.SSGRoute.SSGStage.e1aN0 p k Ω K T E))) z) = 0)
    (hinf : ∀ z : CategoryTheory.Abelian.Ext.{0}
        (CategoryTheory.Limits.kernel
          (Work.SSGRoute.freeCover (Work.SSGRoute.SSGStage.e1aN0 p k Ω K T E)))
        (SSGRoute.PTExt.unitsK k K) 1,
      SSGRoute.PTExt.extToIdeles (k := k)
        (Work.SSGRoute.ExtChain.e1aSyzShift (k := k) (K := K)
          (Work.SSGRoute.SSGStage.e1aN0 p k Ω K T E) z) = 0 →
      ∀ (σ : Ω ≃ₐ[k] Ω), σ ^ 2 = 1 → SSGRoute.res k K σ ≠ 1 →
        Work.SSGRoute.PT.H2Fin.resH1 (Subgroup.zpowers σ)
          (Work.SSGRoute.homCoind k Ω K
            (CategoryTheory.Limits.kernel
              (Work.SSGRoute.freeCover (Work.SSGRoute.SSGStage.e1aN0 p k Ω K T E))))
          (Work.SSGRoute.ExtChain.e1cMap
            (CategoryTheory.Limits.kernel
              (Work.SSGRoute.freeCover (Work.SSGRoute.SSGStage.e1aN0 p k Ω K T E))) z) = 0) :
    ∀ y : CategoryTheory.Abelian.Ext.{0} (SSGRoute.PTExt.modRep (K ≃ₐ[k] K)
        (Work.SSGRoute.DualMod p (TensorProduct (ZMod p) E T))) (SSGRoute.PTExt.unitsK k K) 2,
      SSGRoute.PTExt.extToIdeles (k := k) y = 0 →
        ∃ c : ↥(SSGRoute.Z2loc p k Ω K E),
          @Work.AbsoluteKummer.H2π (Ω ≃ₐ[k] Ω) E _ _ _
            (DistribMulAction.compHom E (SSGRoute.res k K))
            (Work.SSGRoute.PT.Z2ofZ2loc p k Ω K E c) =
          Work.SSGRoute.PT.e1aChainC p k Ω K ζ hζ hζK T hT E y := by
  intro y hy
  refine himg_reduction' (k := k) (Ω := Ω) (K := K) p ζ hζ hζK T hT E y
    ((Work.SSGRoute.ExtChain.e1aSyzShift (k := k) (K := K)
      (Work.SSGRoute.SSGStage.e1aN0 p k Ω K T E)).symm y)
    (AddEquiv.apply_symm_apply _ _) ?_ ?_
  · intro A hA hns
    refine hfin _ ?_ A hA hns
    rw [AddEquiv.apply_symm_apply]
    exact hy
  · intro σ hσ hnt
    refine hinf _ ?_ σ hσ hnt
    rw [AddEquiv.apply_symm_apply]
    exact hy


/-! ## The extension criterion for `resH1_D (e1cMap R ·) = 0`

The colleague's computation quoted in the module doc ("Correction (session 11)") characterises the
vanishing `resH1_D (e1cMap R z) = 0` by an *extension problem*: writing `z = PhiE y`
(`y ∈ Ext⁰_G(E1cR1 R, Kˣ)`), one has

    resH1_D (e1cMap R z) = 0  ↔  ΨE y has a `D`-invariant lift `(E1cF R).V → Ωˣ` along `kappa`.

The direction proved below is the one a future proof of the missing *global* input needs: it turns
a `D`-equivariant lift of the `Kˣ`-valued data into the vanishing.  (It is *not* the same as
`extRes_D z = 0`: the lift may take values in `K·Ω^D`, which is exactly how the two descriptions
differ — see the module doc and `ExtChain/NOTE_himg_status_session11.md` §2(b).) -/

/-- **`resH1_D (e1cMap R (PhiE R y)) = 0` from a `D`-invariant lift of the coefficient data.**

If `Φ : (E1cF R).V →+ Ωˣ` is `D`-invariant and restricts along `kappa R` to the `Ωˣ`-valued map
attached to `y`, then the `E1c` class of `PhiE R y` restricts to `0` on `D`.

Proof: `e1cMap_PhiE_eq_delta_gen` exhibits the class as `δ_Γ (ΨE y)`; `delta_restrictSES` computes
its restriction as `δ_D ((ΨE y)|_D)`; and `(ΨE y)|_D` is the image of the `D`-invariant lift `Φ`
under the restricted projection, hence killed by `δ_D` (`ShortExactSeq.delta_mapH0`). -/
theorem resH1_e1cMap_eq_zero_of_extension
    (R : Rep.{0} Coeff (K ≃ₐ[k] K)) [Finite R.V] [Module.Finite ℤ R.V]
    (y : CategoryTheory.Abelian.Ext.{0}
        (Work.SSGRoute.ExtChain.E1cGeneric.E1cR1 R) (SSGRoute.PTExt.unitsK k K) 0)
    (D : Subgroup (Ω ≃ₐ[k] Ω))
    (Φ : Work.SSGRoute.ExtChain.E1cGeneric.E1cN R)
    (hΦ : Φ ∈ Work.AbsoluteKummer.H0 ↥D (Work.SSGRoute.ExtChain.E1cGeneric.E1cN R))
    (hκ : Φ.comp (Work.SSGRoute.ExtChain.kappa R)
      = (Work.SSGRoute.ExtChain.E1cGeneric.PsiEMap
          (Work.SSGRoute.ExtChain.E1cGeneric.E1cR1 R) y).1) :
    Work.SSGRoute.PT.H2Fin.resH1 D (Work.SSGRoute.homCoind k Ω K R)
      (Work.SSGRoute.ExtChain.E1cGeneric.e1cMap R
        (Work.SSGRoute.ExtChain.E1cGeneric.PhiE R y)) = 0 := by
  rw [Work.SSGRoute.PT.e1cMap_PhiE_eq_delta_gen R y]
  rw [Work.SSGRoute.PT.delta_restrictSES (Work.SSGRoute.PT.e1aSESgen R) D
    (Work.SSGRoute.ExtChain.E1cGeneric.PsiEMap (Work.SSGRoute.ExtChain.E1cGeneric.E1cR1 R) y)]
  have h1 : Work.GroupCohomology.mapH0 ↥D
        (Work.SSGRoute.ExtChain.restrictSES (Work.SSGRoute.PT.e1aSESgen R) D).pi
        (Work.SSGRoute.ExtChain.restrictSES (Work.SSGRoute.PT.e1aSESgen R) D).pi_equivariant
        ⟨Φ, hΦ⟩
      = ⟨(Work.SSGRoute.ExtChain.E1cGeneric.PsiEMap
            (Work.SSGRoute.ExtChain.E1cGeneric.E1cR1 R) y).1,
          fun d => (Work.SSGRoute.ExtChain.E1cGeneric.PsiEMap
            (Work.SSGRoute.ExtChain.E1cGeneric.E1cR1 R) y).2 (d : Ω ≃ₐ[k] Ω)⟩ := by
    refine Subtype.ext ?_
    show (Work.SSGRoute.ExtChain.restrictSES (Work.SSGRoute.PT.e1aSESgen R) D).pi Φ
      = (Work.SSGRoute.ExtChain.E1cGeneric.PsiEMap
          (Work.SSGRoute.ExtChain.E1cGeneric.E1cR1 R) y).1
    rw [Work.SSGRoute.ExtChain.restrictSES_pi, Work.SSGRoute.PT.e1aSESgen_pi]
    exact hκ
  rw [← h1]
  exact Work.AbsoluteKummer.ShortExactSeq.delta_mapH0
    (Work.SSGRoute.ExtChain.restrictSES (Work.SSGRoute.PT.e1aSESgen R) D) ⟨Φ, hΦ⟩



end

end Work.SSGRoute.ExtChain
