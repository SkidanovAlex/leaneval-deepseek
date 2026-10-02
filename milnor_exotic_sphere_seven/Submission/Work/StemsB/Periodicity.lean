import Mathlib
import Submission.Work.Serre.Defs
import Submission.Work.Serre.csrDefs
import Submission.Work.StemsB.RelChainsR
import Submission.Work.StemsB.RelChainsBaseChangeRat
import Submission.Work.StemsB.SerreExact
import Submission.Work.StemsB.Fibrations
import Submission.Work.StemsB.SerreSphereCollar
import Submission.Work.RatHurewicz.RelHomotopy
import Submission.Work.Stems.product_ratH_vanishing
import Submission.Work.Serre.serreE0Range

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# The Gysin/periodicity engine over `ℚ` (area STEMS-B)

`Work.Serre.periodicity_of_serreFibration` (`Submission/Work/Serre/periodicity_of_serreFibration.lean`)
is the statement that a Serre fibration with rationally acyclic total space and rationally spherical
fibre `S^r` has periodic rational homology of period `r+1`.  It is the engine of the `C2` layer of
the blueprint (`Submission/Work/Drive/SERRE_BLUEPRINT.md` §1, E3(b)/C2-even) and hence of the
STEMS route to the drive's contract `Work.Drive.StableStemsTorsion`.

Its author reduces it (`Work.Serre.periodicity_of_pairComparison`) to

* `Work.Serre.serrePairComparison` — the pair comparison `H_i(E,F;ℤ) ≅ H_i(B,b₀;ℤ)` for `i < b+r`
  **together with** the boundary surjectivity in degree `b+r` (the cell-induction engine, i.e. the
  Serre exact sequence in the stable range);
* `Work.Serre.strictFibre_ratH_homotopyFibre` — the strict fibre over `b₀` and the homotopy fibre
  over `e₀` have the same rational homology;
* **the rational long exact sequence bookkeeping**: from the two pair long exact sequences over `ℚ`
  (the workspace's `Work.Cohomology.relChains` is integral; the rational relative chains are
  `Work.StemsB.relChainsR ℚ`, built in this directory) one obtains the additive content of the
  periodicity: `H_{r+1}(B;ℚ) ≅ ℚ` and `H_k(B;ℚ) = 0` for `r+1 < k ≤ b+r`.

This file discharges the third item: `periodicity_of_pairComparisonB` — the `Work.Serre`-spelled
statement `Work.Serre.periodicity_of_pairComparison` — is **proved here** from its hypotheses, over
`ℚ`, using the rational pair long exact sequence of this directory and the flat base change
`ℤ → ℚ` (`Work.StemsB.relChainsBaseChangeRat`).

The proof never needs the *map* of the rational pair comparison: only the induced isomorphism of
homology groups, which is obtained by base change of the integral one
(`relChainsR_pair_homology_iso_of_isIso`) together with the corresponding statement for the
boundary degree (`relChainsR_pair_target_isZero_of_surjective`).
-/

open CategoryTheory CategoryTheory.Limits
open scoped Topology

set_option maxHeartbeats 1000000
set_option autoImplicit false
set_option linter.unusedVariables false
set_option backward.isDefEq.respectTransparency false

namespace Work.StemsB

noncomputable section

/-! ## Elementary rational-homology facts -/

/-- **A rationally acyclic space has vanishing rational homology in positive degrees.** -/
theorem isZero_ratH_of_ratAcyclic {E : Type} [TopologicalSpace E] (hE : Work.Serre.RatAcyclic E)
    {j : ℕ} (hj : 0 < j) : IsZero (Work.Serre.ratH (TopCat.of E) j) := by
  haveI := hE j
  have h1 : Work.Serre.ratH (TopCat.of E) j ≅ Work.Serre.ratH (TopCat.of PUnit) j :=
    asIso (Work.Serre.ratHomologyMap (Work.Serre.toPoint E) j)
  have h2 : IsZero (Work.Serre.ratH (TopCat.of PUnit) j) :=
    (Work.Serre.ratAcyclic_of_contractible PUnit).isZero_ratH hj
  exact IsZero.of_iso h2 h1

/-- **Rational homology vanishes below the connectivity radius.**  If `B` is `(b-1)`-connected
(`π_i(B,b₀) = 0` for `i < b`) with `b ≥ 1`, then `H_j(B;ℚ) = 0` for `0 < j < b`.  This is the
*proved* Serre `E0` in range form (`Work.Serre.serreE0Range`, the singular-cone construction). -/
theorem isZero_ratH_of_connB {B : Type} [TopologicalSpace B] (b₀ : B) (b : ℕ) (hb : 1 ≤ b)
    (hconn : Work.Serre.Conn B b₀ b) (j : ℕ) (hj : 0 < j) (hjb : j < b) :
    IsZero (Work.Serre.ratH (TopCat.of B) j) := by
  have h := Work.Serre.serreE0Range B b₀ (b - 1) (fun i hi => hconn i (by omega))
  rw [Nat.sub_add_cancel hb] at h
  exact h j hj hjb

/-- A surjection whose source is a zero object has zero target. -/
theorem isZero_of_epi_of_isZero {R : Type} [CommRing R] {X Y : ModuleCat R} (h : IsZero X)
    (f : X ⟶ Y) [Epi f] : IsZero Y := by
  haveI : Subsingleton X := ModuleCat.isZero_iff_subsingleton.mp h
  have hf : Function.Surjective f.hom := (ModuleCat.epi_iff_surjective f).mp inferInstance
  refine ModuleCat.isZero_iff_subsingleton.mpr ⟨fun a b => ?_⟩
  obtain ⟨x, rfl⟩ := hf a
  obtain ⟨y, rfl⟩ := hf b
  rw [Subsingleton.elim x y]

/-! ## The long exact sequence of a pair over `ℚ`

All statements are phrased with `Work.StemsB.relChainsR ℚ`, the rational relative chain complex of
`Work.StemsB/RelChainsR.lean`, whose long exact sequence (`relChainsR_exact₁/₂/₃`) is available for
an arbitrary coefficient ring. -/

/-- **The relative term of the pair is the absolute term of the total space** when the subspace has
vanishing rational homology in the two relevant degrees: the long exact sequence of the pair
`H_n(A) → H_n(X) → H_n(X,A) → H_{n-1}(A)` degenerates. -/
theorem relChainsR_homology_iso_of_abs_succ (R : Type) [CommRing R] (X : TopCat) (A : Set X)
    (n : ℕ)
    (hA₁ : IsZero ((Work.Cohomology.singularChains R (TopCat.of A)).homology (n + 1)))
    (hA₂ : IsZero ((Work.Cohomology.singularChains R (TopCat.of A)).homology n)) :
    Nonempty ((Work.Cohomology.singularChains R X).homology (n + 1) ≅
      (Work.StemsB.relChainsR R X A).homology (n + 1)) := by
  have hS₂ := Work.StemsB.relChainsR_exact₂ R X A (n + 1)
  have hS₃ := Work.StemsB.relChainsR_exact₃ R X A n
  have hf0 : HomologicalComplex.homologyMap (Work.StemsB.relChainsRIncl R X A) (n + 1) = 0 :=
    hA₁.eq_zero_of_src (HomologicalComplex.homologyMap (Work.StemsB.relChainsRIncl R X A) (n + 1))
  have hg0 : Work.StemsB.relChainsRδ R X A n = 0 :=
    hA₂.eq_zero_of_tgt (Work.StemsB.relChainsRδ R X A n)
  haveI hmono : Mono (HomologicalComplex.homologyMap (cokernel.π (Work.StemsB.relChainsRIncl R X A))
      (n + 1)) := hS₂.mono_g_iff.mpr hf0
  haveI hepi : Epi (HomologicalComplex.homologyMap (cokernel.π (Work.StemsB.relChainsRIncl R X A))
      (n + 1)) := hS₃.epi_f_iff.mpr hg0
  haveI : IsIso (HomologicalComplex.homologyMap (cokernel.π (Work.StemsB.relChainsRIncl R X A))
      (n + 1)) := isIso_of_mono_of_epi _
  exact ⟨asIso (HomologicalComplex.homologyMap (cokernel.π (Work.StemsB.relChainsRIncl R X A))
    (n + 1))⟩

/-- **The connecting homomorphism of a pair is an isomorphism** when the total space has vanishing
rational homology in the two degrees around it. -/
theorem relChainsRδ_isIso_of_abs_zero (R : Type) [CommRing R] (X : TopCat) (A : Set X) (n : ℕ)
    (hXn : IsZero ((Work.Cohomology.singularChains R X).homology (n + 1)))
    (hXm : IsZero ((Work.Cohomology.singularChains R X).homology n)) :
    IsIso (Work.StemsB.relChainsRδ R X A n) := by
  have hf0 : HomologicalComplex.homologyMap (cokernel.π (Work.StemsB.relChainsRIncl R X A)) (n + 1)
      = 0 := hXn.eq_zero_of_src
        (HomologicalComplex.homologyMap (cokernel.π (Work.StemsB.relChainsRIncl R X A)) (n + 1))
  have hg0 : HomologicalComplex.homologyMap (Work.StemsB.relChainsRIncl R X A) n = 0 :=
    hXm.eq_zero_of_tgt (HomologicalComplex.homologyMap (Work.StemsB.relChainsRIncl R X A) n)
  haveI hmono : Mono (Work.StemsB.relChainsRδ R X A n) :=
    (Work.StemsB.relChainsR_exact₃ R X A n).mono_g_iff.mpr hf0
  haveI hepi : Epi (Work.StemsB.relChainsRδ R X A n) :=
    (Work.StemsB.relChainsR_exact₁ R X A n).epi_f_iff.mpr hg0
  exact isIso_of_mono_of_epi _

/-! ## Base change of the integral pair comparison -/

/-- The flat base change `ℤ → ℚ` of a chain complex of `ℤ`-modules has the same homology. -/
theorem relChainsR_pair_homology_iso_of_isIso {E B : Type} [TopologicalSpace E]
    [TopologicalSpace B] (p : C(E, B)) (b₀ : B) (j : ℕ)
    (hiso : IsIso (HomologicalComplex.homologyMap (Work.StemsB.relPairMap p b₀) j)) :
    Nonempty ((Work.StemsB.relChainsR ℚ (TopCat.of E) (p ⁻¹' {b₀})).homology j ≅
      (Work.StemsB.relChainsR ℚ (TopCat.of B) ({b₀} : Set B)).homology j) := by
  haveI hflat : (Int.castRingHom ℚ).Flat := by rw [RingHom.Flat]; infer_instance
  haveI : PreservesFiniteLimits Work.StemsB.IntRatF :=
    ModuleCat.preservesFiniteLimits_extendScalars_of_flat hflat
  haveI : PreservesFiniteColimits Work.StemsB.IntRatF := inferInstance
  haveI : Work.StemsB.IntRatF.PreservesHomology := inferInstance
  let K₁ := Work.Cohomology.relChains (TopCat.of E) (p ⁻¹' {b₀})
  let K₂ := Work.Cohomology.relChains (TopCat.of B) ({b₀} : Set B)
  obtain ⟨β₁⟩ := Work.StemsB.relChainsBaseChangeRat (TopCat.of E) (p ⁻¹' {b₀})
  obtain ⟨β₂⟩ := Work.StemsB.relChainsBaseChangeRat (TopCat.of B) ({b₀} : Set B)
  have α₁ : (Work.StemsB.relChainsR ℚ (TopCat.of E) (p ⁻¹' {b₀})).homology j ≅
      Work.StemsB.IntRatF.obj (K₁.homology j) :=
    (HomologicalComplex.homologyMapIso β₁ j).symm ≪≫
      (Work.StemsB.SphRat.homologyMapBaseChange Work.StemsB.IntRatF K₁ j).some
  have α₂ : (Work.StemsB.relChainsR ℚ (TopCat.of B) ({b₀} : Set B)).homology j ≅
      Work.StemsB.IntRatF.obj (K₂.homology j) :=
    (HomologicalComplex.homologyMapIso β₂ j).symm ≪≫
      (Work.StemsB.SphRat.homologyMapBaseChange Work.StemsB.IntRatF K₂ j).some
  haveI : IsIso (HomologicalComplex.homologyMap (Work.StemsB.relPairMap p b₀) j) := hiso
  exact ⟨α₁ ≪≫ Work.StemsB.IntRatF.mapIso
    (asIso (HomologicalComplex.homologyMap (Work.StemsB.relPairMap p b₀) j)) ≪≫ α₂.symm⟩

/-- **The boundary degree**: the rational relative homology of the *target* of a pair map vanishes
when it vanishes for the source and the integral pair map is surjective in that degree. -/
theorem relChainsR_pair_target_isZero_of_surjective {E B : Type} [TopologicalSpace E]
    [TopologicalSpace B] (p : C(E, B)) (b₀ : B) (j : ℕ)
    (hsurj : Function.Surjective
      (HomologicalComplex.homologyMap (Work.StemsB.relPairMap p b₀) j).hom)
    (hE : IsZero ((Work.StemsB.relChainsR ℚ (TopCat.of E) (p ⁻¹' {b₀})).homology j)) :
    IsZero ((Work.StemsB.relChainsR ℚ (TopCat.of B) ({b₀} : Set B)).homology j) := by
  haveI hflat : (Int.castRingHom ℚ).Flat := by rw [RingHom.Flat]; infer_instance
  haveI : PreservesFiniteLimits Work.StemsB.IntRatF :=
    ModuleCat.preservesFiniteLimits_extendScalars_of_flat hflat
  haveI : PreservesFiniteColimits Work.StemsB.IntRatF := inferInstance
  haveI : Work.StemsB.IntRatF.PreservesHomology := inferInstance
  let K₁ := Work.Cohomology.relChains (TopCat.of E) (p ⁻¹' {b₀})
  let K₂ := Work.Cohomology.relChains (TopCat.of B) ({b₀} : Set B)
  obtain ⟨β₁⟩ := Work.StemsB.relChainsBaseChangeRat (TopCat.of E) (p ⁻¹' {b₀})
  obtain ⟨β₂⟩ := Work.StemsB.relChainsBaseChangeRat (TopCat.of B) ({b₀} : Set B)
  have α₁ : (Work.StemsB.relChainsR ℚ (TopCat.of E) (p ⁻¹' {b₀})).homology j ≅
      Work.StemsB.IntRatF.obj (K₁.homology j) :=
    (HomologicalComplex.homologyMapIso β₁ j).symm ≪≫
      (Work.StemsB.SphRat.homologyMapBaseChange Work.StemsB.IntRatF K₁ j).some
  have α₂ : (Work.StemsB.relChainsR ℚ (TopCat.of B) ({b₀} : Set B)).homology j ≅
      Work.StemsB.IntRatF.obj (K₂.homology j) :=
    (HomologicalComplex.homologyMapIso β₂ j).symm ≪≫
      (Work.StemsB.SphRat.homologyMapBaseChange Work.StemsB.IntRatF K₂ j).some
  haveI : Epi (HomologicalComplex.homologyMap (Work.StemsB.relPairMap p b₀) j) :=
    (ModuleCat.epi_iff_surjective _).mpr hsurj
  have hzero₁ : IsZero (Work.StemsB.IntRatF.obj (K₁.homology j)) := IsZero.of_iso hE α₁.symm
  haveI hmapEpi : Epi (Work.StemsB.IntRatF.map
      (HomologicalComplex.homologyMap (Work.StemsB.relPairMap p b₀) j)) := inferInstance
  have hzero₂ : IsZero (Work.StemsB.IntRatF.obj (K₂.homology j)) :=
    isZero_of_epi_of_isZero (X := Work.StemsB.IntRatF.obj (K₁.homology j))
      (Y := Work.StemsB.IntRatF.obj (K₂.homology j)) hzero₁
      (Work.StemsB.IntRatF.map (HomologicalComplex.homologyMap (Work.StemsB.relPairMap p b₀) j))
  exact IsZero.of_iso hzero₂ α₂

/-! ## The main theorem -/

/-- **The reduction**: the pair comparison (stable range + boundary surjectivity) together with
the comparison of the strict and homotopy fibres gives the periodicity.  This is
`Work.Serre.periodicity_of_pairComparison` in this directory's spelling. -/
theorem periodicity_of_pairComparisonB {E B : Type} [TopologicalSpace E] [TopologicalSpace B]
    (p : C(E, B)) (hp : Work.StemsB.IsSerreFibration p) (e₀ : E) (b₀ : B)
    (hB : PathConnectedSpace B) (hE : Work.Serre.RatAcyclic E)
    (hsc : Subsingleton (HomotopyGroup (Fin 1) B b₀))
    (b r : ℕ) (hb : 2 ≤ b) (hr : 1 ≤ r) (hconn : Work.Serre.Conn B b₀ b)
    (hvan : ∀ t : ℕ, 0 < t → t ≠ r →
      CategoryTheory.Limits.IsZero (Work.Serre.ratH
        (TopCat.of (Work.RatHurewicz.homotopyFibre p e₀)) t))
    (hgen : Nonempty (Work.Serre.ratH
      (TopCat.of (Work.RatHurewicz.homotopyFibre p e₀)) r ≅ ModuleCat.of ℚ ℚ))
    (hpair : (∀ i : ℕ, i < b + r → CategoryTheory.IsIso
        (HomologicalComplex.homologyMap (Work.StemsB.relPairMap p b₀) i)) ∧
      Function.Surjective
        (HomologicalComplex.homologyMap (Work.StemsB.relPairMap p b₀) (b + r)).hom)
    (hbridge : ∀ j : ℕ, Nonempty (Work.Serre.ratH (TopCat.of (Work.StemsB.fibre p b₀)) j ≅
      Work.Serre.ratH (TopCat.of (Work.RatHurewicz.homotopyFibre p e₀)) j)) :
    (∀ s : ℕ, 1 ≤ s → s < b → Nonempty (Work.Serre.ratH (TopCat.of B) s ≅
        Work.Serre.ratH (TopCat.of B) (s + r + 1))) ∧
      Nonempty (Work.Serre.ratH (TopCat.of B) 0 ≅ Work.Serre.ratH (TopCat.of B) (r + 1)) := by
  -- the rational homology of the strict fibre
  have hfib : ∀ j : ℕ, j ≠ 0 → j ≠ r →
      IsZero (Work.Serre.ratH (TopCat.of (Work.StemsB.fibre p b₀)) j) := by
    intro j hj0 hjr
    exact IsZero.of_iso (hvan j (Nat.pos_of_ne_zero hj0) hjr) (hbridge j).some
  have hgenF : Nonempty (Work.Serre.ratH (TopCat.of (Work.StemsB.fibre p b₀)) r ≅
      ModuleCat.of ℚ ℚ) := ⟨(hbridge r).some ≪≫ hgen.some⟩
  -- the rational relative homology of the pair `(E, p⁻¹{b₀})`
  have hEFzero : ∀ j : ℕ, 2 ≤ j → j ≠ r + 1 →
      IsZero ((Work.StemsB.relChainsR ℚ (TopCat.of E) (p ⁻¹' {b₀})).homology j) := by
    intro j hj2 hjr1
    have h1 : IsZero ((Work.Cohomology.singularChains ℚ (TopCat.of E)).homology j) :=
      isZero_ratH_of_ratAcyclic hE (by omega)
    have h2 : IsZero ((Work.Cohomology.singularChains ℚ
        (TopCat.of ↥(p ⁻¹' {b₀}))).homology (j - 1)) := by
      have hne0 : j - 1 ≠ 0 := by omega
      have hner : j - 1 ≠ r := by omega
      exact hfib (j - 1) hne0 hner
    exact Work.Stems.isZero_relChainsR_homology_of_isZero_abs ℚ (TopCat.of E) (p ⁻¹' {b₀}) j
      (by omega) h1 (by simpa using h2)
  have hEFtop : Nonempty ((Work.StemsB.relChainsR ℚ (TopCat.of E) (p ⁻¹' {b₀})).homology
      (r + 1) ≅ ModuleCat.of ℚ ℚ) := by
    have hδ : IsIso (Work.StemsB.relChainsRδ ℚ (TopCat.of E) (p ⁻¹' {b₀}) r) :=
      relChainsRδ_isIso_of_abs_zero ℚ (TopCat.of E) (p ⁻¹' {b₀}) r
        (by simpa using isZero_ratH_of_ratAcyclic hE (j := r + 1) (by omega))
        (by simpa using isZero_ratH_of_ratAcyclic hE (j := r) (by omega))
    haveI := hδ
    exact ⟨(asIso (Work.StemsB.relChainsRδ ℚ (TopCat.of E) (p ⁻¹' {b₀}) r) ≪≫
      (hgenF.some))⟩
  -- the pair comparison over `ℚ`
  have hpairQ : ∀ j : ℕ, j < b + r → Nonempty
      ((Work.StemsB.relChainsR ℚ (TopCat.of E) (p ⁻¹' {b₀})).homology j ≅
        (Work.StemsB.relChainsR ℚ (TopCat.of B) ({b₀} : Set B)).homology j) :=
    fun j hj => relChainsR_pair_homology_iso_of_isIso p b₀ j (hpair.1 j hj)
  -- the relative homology of `(B, {b₀})`
  have hBrel : ∀ j : ℕ, 2 ≤ j → j ≤ b + r → j ≠ r + 1 →
      IsZero ((Work.StemsB.relChainsR ℚ (TopCat.of B) ({b₀} : Set B)).homology j) := by
    intro j hj2 hjb hjr1
    rcases lt_or_ge j (b + r) with hlt | hge
    · exact IsZero.of_iso (hEFzero j hj2 hjr1) (hpairQ j hlt).some.symm
    · have hjbd : j = b + r := by omega
      subst hjbd
      exact relChainsR_pair_target_isZero_of_surjective p b₀ (b + r) hpair.2
        (hEFzero (b + r) (by omega) (by omega))
  have hBreltop : Nonempty ((Work.StemsB.relChainsR ℚ (TopCat.of B) ({b₀} : Set B)).homology
      (r + 1) ≅ ModuleCat.of ℚ ℚ) :=
    ⟨(hpairQ (r + 1) (by omega)).some.symm ≪≫ hEFtop.some⟩
  -- absolute vs relative homology of `B` for `j ≥ 2`
  have hisoB : ∀ j : ℕ, 2 ≤ j → Nonempty (Work.Serre.ratH (TopCat.of B) j ≅
      (Work.StemsB.relChainsR ℚ (TopCat.of B) ({b₀} : Set B)).homology j) := by
    intro j hj2
    obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (show j ≠ 0 by omega)
    exact relChainsR_homology_iso_of_abs_succ ℚ (TopCat.of B) ({b₀} : Set B) n
      (Work.Stems.isZero_ratH_singleton B b₀ (by omega))
      (Work.Stems.isZero_ratH_singleton B b₀ (by omega))
  -- the additive content
  have hmain : ∀ j : ℕ, 1 ≤ j → j ≤ b + r → j ≠ r + 1 →
      IsZero (Work.Serre.ratH (TopCat.of B) j) := by
    intro j hj1 hjb hjr1
    rcases eq_or_lt_of_le hj1 with h1 | h2
    · -- `j = 1` : connectivity
      subst h1
      exact isZero_ratH_of_connB b₀ b (by omega) hconn 1 (by omega) (by omega)
    · -- `j ≥ 2` : relative vanishing plus the pair sequence
      exact IsZero.of_iso (hBrel j (by omega) hjb hjr1) (hisoB j (by omega)).some
  have htop : Nonempty (Work.Serre.ratH (TopCat.of B) (r + 1) ≅ ModuleCat.of ℚ ℚ) :=
    ⟨(hisoB (r + 1) (by omega)).some ≪≫ hBreltop.some⟩
  constructor
  · intro s hs1 hsb
    have h1 : IsZero (Work.Serre.ratH (TopCat.of B) s) :=
      isZero_ratH_of_connB b₀ b (by omega) hconn s (by omega) hsb
    have h2 : IsZero (Work.Serre.ratH (TopCat.of B) (s + r + 1)) :=
      hmain (s + r + 1) (by omega) (by omega) (by omega)
    haveI h1s : Subsingleton (Work.Serre.ratH (TopCat.of B) s) :=
      ModuleCat.isZero_iff_subsingleton.mp h1
    haveI h2s : Subsingleton (Work.Serre.ratH (TopCat.of B) (s + r + 1)) :=
      ModuleCat.isZero_iff_subsingleton.mp h2
    refine ⟨{ hom := 0, inv := 0, hom_inv_id := ?_, inv_hom_id := ?_ }⟩
    · ext x; exact Subsingleton.elim _ _
    · ext x; exact Subsingleton.elim _ _
  · -- `H_0(B;ℚ) ≅ ℚ ≅ H_{r+1}(B;ℚ)`
    haveI : PathConnectedSpace B := hB
    haveI hε : IsIso (TopCat.singularHomology₀ε (TopCat.of B) (ModuleCat.of ℚ ℚ)) := inferInstance
    have h0 : Work.Serre.ratH (TopCat.of B) 0 ≅ ModuleCat.of ℚ ℚ :=
      asIso (TopCat.singularHomology₀ε (TopCat.of B) (ModuleCat.of ℚ ℚ))
    exact ⟨h0.trans htop.some.symm⟩

end

end Work.StemsB
