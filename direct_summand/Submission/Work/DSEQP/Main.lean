/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# DSEQP: equal characteristic `p` case of `#direct_summand` — area entry point

This is the entry point of the `DSEQP` area, which owns the equal characteristic `p` case
(frozen area statement `DSMap.area_EQP` in the lead's `Submission/Work/DSMap/Map.lean`).

## What is proved here

The **algebraic core** of the equal characteristic `p` proof, following
`direct_summand_proof_map_REVIEW.md` §4(a) (perfection + Frobenius trick + Kunz + Krull
descent instead of Bhatt 2012):

* `Work.DSEQP.frobeniusTwist` (`DSEQP/frobeniusTwist.lean`): the *Frobenius trick*.  If `S` is
  perfect of characteristic `p`, every `A`-linear map `s : B →ₗ[A] S` can be twisted into an
  `A`-linear map whose value at `1` is a `p^e`-th root of `s 1`.
* `Work.DSEQP.evalIdeal_baseChange` (`DSEQP/evalIdeal_baseChange.lean`): the evaluation ideal
  (the obstruction to splitting) commutes with flat base change along a Noetherian finite
  algebra: `I·S = {s 1 : s ∈ Hom_A(B, S)}`.
* `Work.DSEQP.exists_pthRoot_mem_map_evalIdeal` (`DSEQP/AlmostPurity.lean`): **almost purity in
  characteristic `p`**: every nonzero element of the obstruction ideal acquires all its
  `p^e`-th roots inside `I·S`.
* `Work.DSEQP.krull_descent`, `Work.DSEQP.one_mem_of_forall_pthRoot_mem`
  (`DSEQP/krull_descent.lean`, `DSEQP/Descent.lean`): **Krull descent**: an obstruction inside a
  proper ideal cannot be almost split after a faithfully flat base change
  (Krull's intersection theorem + contraction of ideals).
* `Work.DSEQP.evalIdeal_ne_bot` (`DSEQP/evalIdeal_ne_bot.lean`): the obstruction ideal of a
  finite faithful extension of a Noetherian domain is nonzero.
* `Work.DSEQP.isSplinter_of_flat_perfect` (`DSEQP/AffineCharP.lean`): **the affine equal
  characteristic `p` direct summand theorem**: a Noetherian local domain of characteristic `p`
  which has a faithfully flat *perfect* extension is a splinter.
* `Work.DSEQP.pPerfection` (`DSEQP/Perfection.lean`): the `p`-perfection `A^{1/p^∞}` as the
  filtered colimit of `A --F--> A --F--> ⋯`, with the root tower
  `pPerfection.rootTower g e = g^{1/p^e}`.
* `Work.DSEQP.coaugIdeal`, `Work.DSEQP.isSplitMono_of_one_mem_coaugIdeal`,
  `Work.DSEQP.one_mem_coaugIdeal_of_forall_pthRoot` (`DSEQP/CechReduction.lean`): the
  **reduction of the area statement to the Čech model**: the obstruction to splitting is the
  ideal of values of degree-`0` functionals on the coaugmentation class of the Čech complex,
  `1 ∈ coaugIdeal` implies the splitting of `rgUnit` (given the area-`F1` model data), and the
  descent step turns an "almost splitting" over a faithfully flat base into that membership.

## Road to the frozen statement `DSMap.area_EQP`

The area was later redirected by the lead to the seven-node route of
`sources/dsmap/direct_summand_gaps_1013.md` (review `..._REVIEW.md`), whose assembly
`area_EQP_gaps` is a compiled proof of `DSMap.area_EQP` from those nodes.  **That route is now
complete in this directory:**

| node | proof |
|---|---|
| `area_GOOD` | `Work.DSEQP.area_GOOD_proved` |
| `eqp_cech_torsion` | `Work.DSEQP.eqp_cech_torsion_proved` |
| `eqp_perfModel` | `Work.DSEQP.eqp_perfModel_proved` |
| `area_GAMMA` | `Work.DSEQP.area_GAMMA_proved` |
| `modSplit_twist` | `Work.DSEQP.modSplit_twist_proved` |
| `modSplit_one_of_roots` | `Work.DSEQP.modSplit_one_of_roots_proved` |
| `area_KUNZ` | `Work.DSEQP.area_KUNZ_proved` |

Each is rfl-type-identical to its frozen statement in `Submission/Work/DSMap/Gaps.lean` and each
is axiom-clean (`AxiomCheck.lean` records the audit).  The assembly `DSMap.area_EQP_proved` is
stated and proved at the end of this file, with the type check
`type_of% (@DSMap.area_EQP_proved.{a,b,c}) = type_of% (@DSMap.area_EQP.{a,b,c})`.

The finite free model of `RΓ` and its bridge to the derived statement are supplied, on the proved
side, by `Work.DSEQP.mx0U_of_chartCover` together with this area's own Čech-level coherence
`Work.DSEQP.cechZ_homology_chartCover_proved` (the algebraic bridge `(1b)` `chartCechTerm_iso`
plus the normalisation comparison `(1c)`), and by `Work.DSEQP.mx0bU_from_F1` together with the
proved area `F1` (`DSMap.area_F1_cech_proved`, subproject `DSF1`).  Hence
`#print axioms DSMap.area_EQP_proved` is exactly `[propext, Classical.choice, Quot.sound]`; the
frozen `DSMap.area_F1_cech` and `DSMap.area_COH` are *not* used.  See `AxiomCheck.lean`.
-/
import Mathlib
import Submission.Work.DSEQP.Basic
import Submission.Work.DSEQP.Perfection
import Submission.Work.DSEQP.frobeniusTwist
import Submission.Work.DSEQP.evalIdeal_baseChange
import Submission.Work.DSEQP.AlmostPurity
import Submission.Work.DSEQP.Descent
import Submission.Work.DSEQP.evalIdeal_ne_bot
import Submission.Work.DSEQP.AffineCharP
import Submission.Work.DSEQP.CechReduction
import Submission.Work.DSEQP.perfectRing_pPerfection
import Submission.Work.DSEQP.faithfullyFlat_pPerfection
import Submission.Work.DSEQP.almostZero_of_faithfullyFlat
import Submission.Work.DSEQP.modSplit_one_of_roots_proved
import Submission.Work.DSEQP.area_GOOD_proved
import Submission.Work.DSEQP.modSplit_twist_proved
import Submission.Work.DSEQP.eqp_cech_torsion_proved
import Submission.Work.DSEQP.area_KUNZ_proved
import Submission.Work.DSEQP.eqp_perfModel_proved
import Submission.Work.DSEQP.area_GAMMA_proved
import Submission.Work.DSMap.Gaps
import Submission.Work.DSREG.Main
import Submission.Work.DSCHART.Main
import Submission.Work.DSAMR.Main
import Submission.Work.DSMX0U.Main
import Submission.Work.DSMX0bU.Main
import Submission.Work.DSEQP.F1COHWire
import Submission.Work.DSEQP.cechZ_homology_chartCover_proved

open CategoryTheory AlgebraicGeometry Limits

namespace Work.DSEQP

universe u

/-- **Equal characteristic `p` direct summand theorem from Frobenius-flatness.**  Let `A` be a
Noetherian local domain of characteristic `p` whose Frobenius endomorphism is flat (Kunz's
criterion: this holds when `A` is regular).  Then `A` is a splinter.

The flat perfect extension required by `isSplinter_of_flat_perfect` is the perfection
`pPerfection A p = A^{1/p^∞}`, which is faithfully flat by `faithfullyFlat_pPerfection` and
perfect by `perfectRing_pPerfection`. -/
theorem isSplinter_of_frobenius_flat (A : Type u) [CommRing A] [IsDomain A] [IsLocalRing A]
    [IsNoetherianRing A] (p : ℕ) [Fact p.Prime] [CharP A p] (h : (frobenius A p).Flat) :
    IsSplinter A := by
  haveI := faithfullyFlat_pPerfection A p h
  haveI := perfectRing_pPerfection A p
  haveI : CharP (pPerfection A p) p :=
    charP_of_injective_algebraMap' A p
  exact isSplinter_of_flat_perfect A p (pPerfection A p)

/-- **Kunz-flavoured form, matching the hypotheses of `DSMap.area_EQP`.**  A complete regular
local ring `A` of characteristic `p` is a splinter, provided Kunz's theorem is available in the
form "the Frobenius of `A` is flat".  The hypotheses `[IsDomain A]` (area `REG` of the proof
map) and `[IsAdicComplete (maximalIdeal A) A]` (gonflement, area `G4b`) are carried along as
they are in the frozen statement. -/
theorem isSplinter_of_regular_of_kunz (A : Type u) [CommRing A] [IsDomain A] [IsLocalRing A]
    [IsNoetherianRing A] [IsRegularLocalRing A] [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
    (p : ℕ) [Fact p.Prime] [CharP A p] (hkunz : (frobenius A p).Flat) : IsSplinter A :=
  isSplinter_of_frobenius_flat A p hkunz

/-! ## The frozen area statement, reduced to the Čech model

The frozen statement `DSMap.area_EQP` is recovered from the following two inputs:

* the Čech model of `RΓ(X, 𝒪_X)` for a finite affine cover of `X` (the conclusion of the area
  `F1`, `DSMap.area_F1_cech`, whose four clauses are transcribed verbatim below); and
* the output of the Frobenius/perfection argument on that model over a faithfully flat perfect
  extension `S` of `A` (step 3 of the proof map's §4(a): some nonzero element of the obstruction
  ideal acquires all its `p^e`-th roots in `I·S`).

Both inputs are *weaker* than the conclusion, and the reduction itself is proved below. -/

section Reduction

variable {A : Type u} [CommRing A] {X : Scheme.{u}} {f : X ⟶ Spec (.of A)} {ι : Type u}

/-- **The frozen area statement `DSMap.area_EQP`, reduced to (F1) and the char-`p` almost
splitting.**  Assume the Čech model of `RΓ(X,𝒪_X)` exists (area `F1`) and that, over a
faithfully flat perfect extension `S` of `A`, some nonzero element `a` of the obstruction ideal
of the model acquires all its `p^e`-th roots inside `I·S` (the output of the Frobenius argument,
step 3 of §4(a), which uses area `COH`).  Then the challenge unit splits, i.e. `DSplit A X f`.

The mathematical hypotheses of the frozen statement are carried along so that this can be used
directly as a substitute; they are not used in the proof. -/
theorem area_EQP_of_charPSplitting.{a, b, c} (A : Type a) [CommRing A] [IsDomain A]
    [IsLocalRing A] [IsNoetherianRing A] [IsRegularLocalRing A]
    [IsAdicComplete (IsLocalRing.maximalIdeal A) A] [IsAlgClosed (IsLocalRing.ResidueField A)]
    (p : ℕ) [Fact p.Prime] [CharP A p] (X : Scheme.{a}) [IsIntegral X]
    (f : X ⟶ Spec (.of A)) [IsProper f] (hs : Function.Surjective f)
    (hg : DSMap.IsGenFinite A f) (hp : DSMap.IsProjOver A f)
    (S : Type a) [CommRing S] [Algebra A S] [Module.FaithfullyFlat A S] [CharP S p]
    [PerfectRing S p]
    (hF1 : ∀ (_ : HasDerivedCategory.{b} (ModuleCat.{a} A))
      (_ : HasDerivedCategory.{c} (SheafOfModules X.ringCatSheaf))
      (_ : EnoughInjectives (SheafOfModules X.ringCatSheaf)),
      ∃ (ι : Type a) (_ : Finite ι) (U : ι → X.Opens) (_ : ∀ i, IsAffineOpen (U i))
        (_ : ⨆ i, U i = ⊤)
        (cc : (CochainComplex.singleFunctor (ModuleCat.{a} A) 0).obj (ModuleCat.of A A) ⟶
          DSMap.cechZ A X f U)
        (e : DerivedCategory.Plus.ι.obj (DSMap.RG A X f) ≅
          DerivedCategory.Q.obj (DSMap.cechZ A X f U)),
        (DerivedCategory.Plus.ι.map (DSMap.rgUnit A X f) ≫ e.hom =
          (DerivedCategory.Plus.singleFunctorιIso (ModuleCat.{a} A) 0).hom.app (ModuleCat.of A A) ≫
            (DerivedCategory.singleFunctorIsoCompQ (ModuleCat.{a} A) 0).hom.app
              (ModuleCat.of A A) ≫ DerivedCategory.Q.map cc) ∧
          ∃ a' ∈ coaugIdeal A X f U cc, a' ≠ 0 ∧ ∀ e' : ℕ, ∃ t : S,
            t ∈ (coaugIdeal A X f U cc).map (algebraMap A S) ∧
              t ^ (p ^ e') = algebraMap A S a') :
    DSMap.DSplit.{a, b, c} A X f := by
  intro h₁ h₂ h₃
  obtain ⟨ι, hι, U, hU, hcov, cc, e, he, a', ha', ha'0, hroot⟩ := hF1 h₁ h₂ h₃
  exact isSplitMono_of_one_mem_coaugIdeal A h₁ X f h₂ h₃ U cc e he
    (one_mem_coaugIdeal_of_forall_pthRoot A S p X f U cc ⟨a', ha', ha'0, hroot⟩)

end Reduction

end Work.DSEQP

/-! ## The EQP assembly

The assembly of the frozen area statement `DSMap.area_EQP` from the seven nodes of
`sources/dsmap/direct_summand_gaps_1013.md`, all proved in this directory
(`Work.DSEQP.area_GOOD_proved`, `eqp_cech_torsion_proved`, `eqp_perfModel_proved`,
`area_GAMMA_proved`, `modSplit_twist_proved`, `area_KUNZ_proved`,
`modSplit_one_of_roots_proved`; each is rfl-type-identical to its frozen statement and
axiom-clean), together with the sibling interfaces:

* `DSMap.area_REG_proved` (`DSREG`), `DSMap.Mix2.chartCover_affine_proved` /
  `chartCover_iSup_proved` (`DSCHART`), `DSMap.Mix2.modSplit_of_almostAcyc_proved` (`DSAMR`):
  axiom-clean;
* the finite free model and its bridge to `DSplit`, via `Work.DSEQP.F1COHWire`
  (`Work.DSEQP.mx0U_of_chartCover` + this area's Čech-level coherence
  `Work.DSEQP.cechZ_homology_chartCover_proved`, and `Work.DSEQP.mx0bU_from_F1` + the proved
  `DSMap.area_F1_cech_proved`).  (The alternative composites `Work.DSEQP.mx0U_from_F1COH` /
  `f1Data_from_F1`/`cechZ_homology_finite_from_F1COH`, which cite the still-frozen
  `DSMap.area_COH` at a single marked `WIRE POINT`, are retained in `F1COHWire.lean` for the
  record but are *not* used by the assembly.)
-/

open CategoryTheory AlgebraicGeometry IsLocalRing Limits Opposite

namespace DSMap

universe a b c

/-- **The equal characteristic `p` area of the direct summand theorem**, in the exact form of the
frozen `DSMap.area_EQP`. -/
theorem area_EQP_proved (A : Type a) [CommRing A] [IsRegularLocalRing A]
    [IsAdicComplete (maximalIdeal A) A] [IsAlgClosed (ResidueField A)] (p : ℕ) [Fact p.Prime]
    [CharP A p] (X : Scheme.{a}) [IsIntegral X] (f : X ⟶ Spec (.of A))
    [IsProper f] (hs : Function.Surjective f) (hg : IsGenFinite A f) (hp : IsProjOver A f) :
    DSplit.{a, b, c} A X f := by
  have : IsDomain A := area_REG_proved A
  obtain ⟨g, N, i, j, hg0, hi, hif, hgood⟩ := Work.DSEQP.area_GOOD_proved A X f hs hg hp
  -- `MX0U` for the chart cover: the coherence input is this area's own Čech-level statement
  -- (the bridge `(1b)+(1c)`), so no frozen `area_COH` and no `F1` is involved here.
  obtain ⟨P, ε, hP⟩ := Work.DSEQP.mx0U_of_chartCover A N i hi f hif
    (Work.DSEQP.cechZ_homology_chartCover_proved A N i hi f hif)
  refine Work.DSEQP.mx0bU_from_F1 A X f (DSMap.Mix2.chartCover i)
    (DSMap.Mix2.chartCover_affine_proved i hi) (DSMap.Mix2.chartCover_iSup_proved i) P ε hP ?_
  have htors := fun q => Work.DSEQP.eqp_cech_torsion_proved A X f (DSMap.Mix2.chartCover i)
    (DSMap.Mix2.chartCover_affine_proved i hi) g ⟨j⟩ hgood P ε hP q
  obtain ⟨W, _, _, _, ψW, K, eK, ρ, hψW, hW, hAC, hρ⟩ :=
    Work.DSEQP.eqp_perfModel_proved A p X f (DSMap.Mix2.chartCover i)
      (DSMap.Mix2.chartCover_affine_proved i hi) (DSMap.Mix2.chartCover_iSup_proved i) g P ε hP
      htors
  have hroot : ∀ k, ((frobeniusEquiv W p).symm^[k + 1]) (ψW (phi A X f g)) ^ p =
      ((frobeniusEquiv W p).symm^[k]) (ψW (phi A X f g)) := fun k => by
    rw [Function.iterate_succ_apply', frobeniusEquiv_symm_pow_p]
  have hW' := DSMap.Mix2.modSplit_of_almostAcyc_proved p (ψW.comp (phi A X f)) _ hroot ⊥ K eK hAC P
    hP.1 ε hP.2.1 ρ hρ
  letI : Algebra A Γ(X, ⊤) := (phi A X f).toAlgebra
  obtain ⟨φ, hφ⟩ := Work.DSEQP.area_GAMMA_proved A X f hs hp
  haveI hFF := Work.DSEQP.faithfullyFlat_pPerfection A p (Work.DSEQP.area_KUNZ_proved A p)
  haveI := Work.DSEQP.perfectRing_pPerfection A p
  haveI : CharP (Work.DSEQP.pPerfection A p) p := charP_of_injective_algebraMap' A p
  refine Work.DSEQP.modSplit_one_of_roots_proved A (Work.DSEQP.pPerfection A p) p P hP.1 ε
    (g * φ 1) (mul_ne_zero hg0 hφ)
    (fun e => ((frobeniusEquiv (Work.DSEQP.pPerfection A p) p).symm^[e])
      (algebraMap A _ (g * φ 1)))
    (fun e => iterate_frobeniusEquiv_symm_pow_p_pow _ p _ e) (fun e => ?_)
  exact Work.DSEQP.modSplit_twist_proved p ψW hψW hW (algebraMap A (Work.DSEQP.pPerfection A p)) φ P
    hP.1 ε g e (hW' e)

/-- The type of `area_EQP_proved` is definitionally identical to the type of the frozen
`DSMap.area_EQP`. -/
example : type_of% (@area_EQP_proved.{a, b, c}) = type_of% (@area_EQP.{a, b, c}) := rfl

end DSMap
