import Mathlib
import Submission.Work.Stems.c2FreeClauses
import Submission.Work.Stems.c2EvenStepLocal
import Submission.Work.Stems.c2oddFree_of_c2evenFree
import Submission.Work.Stems.wangUptoBounded
import Submission.Work.Stems.mappingTheoremOfHomotopyFibreAcyclic
import Submission.Work.Stems.wangOddStepBottomCell
import Submission.Work.StemsB.sphRatHomology
import Submission.Work.Stems.exists_collapsingMap
import Submission.Work.Stems.homotopyFibre_conn
import Submission.Work.Stems.isEMSpace_change_basepoint
import Submission.Work.Stems.CollapseDefs
import Submission.Work.Stems.ratH_conn_piIso
import Submission.Work.Stems.Engine.C2EvenRange
import Submission.Work.Stems.Engine.DualVanishing
import Submission.Work.StemsB.C2_of_freeTop
import Submission.Work.Serre.serreC0Range
import Submission.Work.RatHurewicz.exists_bijective_piMapN_rangeModel
import Submission.Work.Serre.bijective_piMapN_of_joined
import Submission.Work.Serre.rwPiMapN_bijective_of_homotopyEquiv
import Submission.Work.RatHurewicz.PairFibre
import Submission.Work.Stems.fibreOfHomeomorphLoopSpace
import Submission.Work.Stems.product_ratH_vanishing
import Submission.Work.Serre.pathConnectedSpace_fibre_of_isSerreFibration
import Submission.Work.Stems.homotopyGroup_loop
import Submission.Work.Stems.sphereConnectivity
import Submission.Work.StemsB.PiMap
import Submission.Work.Serre.C1Rat

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# The odd step of the free-top `C2` interface, level by level

*(Area STEMS.  `Submission/Work/Stems/c2FreeClauses.lean` defines the level clauses;
`c2oddFree_of_c2evenFree.lean` proves the same step for the *uniform* interfaces.)*

`Work.Stems.oddStepLocal` is `c2oddFree_of_c2evenFree` with the hypothesis localised to the single
even level `j` that the proof uses: the even statement enters only through the *loop space*
`ΩX = Path pt pt` (a range model of `K(ℤ,2j)`), so `EvenClause c j` at the tops needed by
`loopKnowledge` is all that is consumed.  This is what lets the mutual induction be run level by
level (`Stems/c2FreeMain.lean`).  The two auxiliary lemmas `loopKnowledgeLocal` and
`oddVanishingOfEvenLocal` are the same proofs as their uniform counterparts, with the hypothesis
specialised.
-/

namespace Work.Stems

noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped Topology

set_option maxHeartbeats 1600000

theorem loopKnowledgeLocal (c : ℕ) {j : ℕ} (hj : 1 ≤ j) (h : ∀ M : ℕ, EvenClause c j hj M)
    {M : ℕ}
    {Y : Type} [TopologicalSpace Y] (pt : Y)
    (hY : Work.Serre.IsEMSpaceUpTo ℤ (2 * j + 1) (by omega) M Y pt) :
    (∀ k : ℕ, 2 * j * k < M →
        Nonempty (Work.Serre.ratH (TopCat.of (Path pt pt)) (2 * j * k) ≅
          ModuleCat.of ℚ ℚ)) ∧
    (∀ d : ℕ, 0 < d → d < M → (∀ k : ℕ, d ≠ 2 * j * k) →
        IsZero (Work.Serre.ratH (TopCat.of (Path pt pt)) d)) := by
  have hloop : Work.Serre.IsEMSpaceUpTo ℤ (2 * j) (by omega) (M - 1) (Path pt pt)
      (Path.refl pt) :=
    isEMSpaceUpTo_loop' (m := 2 * j + 1) (by omega) pt hY
  set M' : ℕ := M + c * (2 * j) + 2 * j + 1 with hM'
  obtain ⟨P, tP, p₀, hP⟩ := Work.Serre.serreC0Range ℤ (2 * j) M' (by omega) (by omega)
  letI : TopologicalSpace P := tP
  have hPmod := h M' P p₀ hP
  have hsub : M' - c * (2 * j) = M + 2 * j + 1 := by omega
  constructor
  · intro k hk
    obtain ⟨e⟩ := Work.StemsB.rangeModel_ratH_iso_le (k := 2 * j) (N := M - 1) (M := M')
      (by omega) (by omega) (Path.refl pt) p₀ hloop hP (2 * j * k) (by omega)
    obtain ⟨e'⟩ := hPmod.1 k (by omega)
    exact ⟨e ≪≫ e'⟩
  · intro d hd0 hdM hne
    obtain ⟨e⟩ := Work.StemsB.rangeModel_ratH_iso_le (k := 2 * j) (N := M - 1) (M := M')
      (by omega) (by omega) (Path.refl pt) p₀ hloop hP d (by omega)
    exact IsZero.of_iso (hPmod.2 d (by omega) hne) e

/-! ## The odd step for a range model -/

theorem oddVanishingOfEvenLocal (c : ℕ) {j : ℕ} (hj : 1 ≤ j) (h : ∀ M : ℕ, EvenClause c j hj M)
    (hE3a : Work.Serre.SerreE3a) {M : ℕ}
    {Y : Type} [TopologicalSpace Y] (pt : Y)
    (hY : Work.Serre.IsEMSpaceUpTo ℤ (2 * j + 1) (by omega) M Y pt) :
    ∀ d : ℕ, 0 < d → d < M - 1 → d ≠ 2 * j + 1 → IsZero (Work.Serre.ratH (TopCat.of Y) d) := by
  intro d hd0 hdM hdn
  by_cases hsmall : M - 1 ≤ 2 * j + 1
  · -- the range is inside the connectivity of `Y`
    refine Work.Serre.serreE0Range Y pt d ?_ d hd0 (by omega)
    intro i hi
    exact hY.2 i (by omega) (Or.inl (by omega))
  · have hMbig : 2 * j + 1 + 2 ≤ M := by omega
    have hn3 : 3 ≤ 2 * j + 1 := by omega
    have hodd : Odd (2 * j + 1) := ⟨j, rfl⟩
    have hpcY : PathConnectedSpace Y :=
      Work.RatHurewicz.pathConnectedSpace_of_subsingleton_pi_zero pt
        (hY.2 0 (by omega) (Or.inl (by omega)))
    -- the bottom cell
    obtain ⟨s₀, f, _hf0, hbij₀⟩ :=
      Work.RatHurewicz.exists_bijective_piMapN_rangeModel (2 * j + 1) M (by omega) Y pt hY
    -- transport to the one-point model of the sphere, in which the Wang machinery is available
    let Φ : Work.StemsB.SphModel (2 * j + 1) ≃ₜ Work.Serre.Sph (2 * j + 1) :=
      Work.Stems.onePointSphereHomeo (2 * j + 1)
    have hpcSph : PathConnectedSpace (Work.Serre.Sph (2 * j + 1)) :=
      Work.RatHurewicz.pathConnectedSpace_of_subsingleton_pi_zero s₀
        (Work.Stems.sphereConnectivity (2 * j + 1) 0 (by omega) s₀)
    let g : C(Work.StemsB.SphModel (2 * j + 1), Y) :=
      f.comp (⟨Φ, Φ.continuous_toFun⟩ : C(Work.StemsB.SphModel (2 * j + 1),
        Work.Serre.Sph (2 * j + 1)))
    have hjoin : Joined s₀ (Φ OnePoint.infty) := hpcSph.joined s₀ (Φ OnePoint.infty)
    have hbij₁ : Function.Bijective (Work.Serre.piMapN f (2 * j + 1) (Φ OnePoint.infty)) :=
      Work.Serre.bijective_piMapN_of_joined f hjoin (2 * j + 1) hbij₀
    have hbijΦ : Function.Bijective (Work.Serre.piMapN (⟨Φ, Φ.continuous_toFun⟩ :
        C(Work.StemsB.SphModel (2 * j + 1), Work.Serre.Sph (2 * j + 1)))
        (2 * j + 1) OnePoint.infty) :=
      Work.Serre.rwPiMapN_bijective_of_homotopyEquiv Φ.toHomotopyEquiv (2 * j + 1)
        OnePoint.infty
    have hbijg : Function.Bijective (Work.Serre.piMapN g (2 * j + 1) OnePoint.infty) := by
      have h1 : Work.Serre.piMapN g (2 * j + 1) OnePoint.infty =
          fun a => Work.Serre.piMapN f (2 * j + 1) (Φ OnePoint.infty)
            (Work.Serre.piMapN (⟨Φ, Φ.continuous_toFun⟩ : C(Work.StemsB.SphModel (2 * j + 1),
              Work.Serre.Sph (2 * j + 1))) (2 * j + 1) OnePoint.infty a) := by
        funext a
        exact Work.Serre.piMapN_comp (⟨Φ, Φ.continuous_toFun⟩ : C(Work.StemsB.SphModel
          (2 * j + 1), Work.Serre.Sph (2 * j + 1))) f (2 * j + 1) OnePoint.infty a
      rw [h1]
      exact hbij₁.comp hbijΦ
    -- `Y` as a range model at the new base point
    obtain ⟨γ⟩ := hpcY.joined pt (g OnePoint.infty)
    have hYg : Work.Serre.IsEMSpaceUpTo ℤ (2 * j + 1) (by omega) M Y (g OnePoint.infty) :=
      isEMSpaceUpTo_change_basepoint (by omega) γ hY
    -- the cover
    let E : Type := Work.RatHurewicz.homotopyFibre g OnePoint.infty
    let e₀ : E := Work.RatHurewicz.homotopyFibreBasepoint g OnePoint.infty
    let p : C(E, Work.StemsB.SphModel (2 * j + 1)) :=
      Work.RatHurewicz.homotopyFibreFst g OnePoint.infty
    have hp : Work.StemsB.IsHurewiczFibration p :=
      Work.Stems.isHurewiczFibration_homotopyFibreFst g OnePoint.infty
    have hsource : ∀ i : ℕ, i < 2 * j + 1 → Subsingleton (HomotopyGroup (Fin i)
        (Work.StemsB.SphModel (2 * j + 1)) OnePoint.infty) :=
      fun i hi => Work.Stems.subsingleton_homotopyGroup_fin_of_homeomorph Φ rfl i
        (Work.Stems.sphereConnectivity (2 * j + 1) i hi (Φ OnePoint.infty))
    have hconnE : ∀ k : ℕ, k ≤ 2 * j + 1 → Subsingleton (HomotopyGroup (Fin k) E e₀) :=
      homotopyFibre_conn_of_range hn3 g OnePoint.infty hsource hbijg
        (fun i _hi hin => hYg.2 i hin (by
          rcases lt_or_ge i (2 * j + 1) with hlt | hge
          · exact Or.inl hlt
          · exact Or.inr (by omega)))
    have hpcE : PathConnectedSpace E :=
      Work.RatHurewicz.pathConnectedSpace_of_subsingleton_pi_zero e₀ (hconnE 0 (by omega))
    have hpcSphM : PathConnectedSpace (Work.StemsB.SphModel (2 * j + 1)) :=
      Work.RatHurewicz.pathConnectedSpace_of_subsingleton_pi_zero OnePoint.infty
        (hsource 0 (by omega))
    have hpi1SphM : Subsingleton (HomotopyGroup (Fin 1) (Work.StemsB.SphModel (2 * j + 1))
        OnePoint.infty) :=
      Work.Stems.subsingleton_homotopyGroup_fin_of_homeomorph Φ rfl 1
        (Work.Stems.sphereConnectivity (2 * j + 1) 1 (by omega) (Φ OnePoint.infty))
    have hpcF : PathConnectedSpace ↥(p ⁻¹' {OnePoint.infty}) :=
      Work.Serre.pathConnectedSpace_fibre_of_isSerreFibration p hp.isSerreFibration
        OnePoint.infty hpcE hpcSphM hpi1SphM
    -- the fibre's homology knowledge and the homeomorphism with the loop space
    obtain ⟨hLgen, hLvan⟩ := loopKnowledgeLocal c hj h (g OnePoint.infty) hYg
    obtain ⟨hw⟩ := Work.Stems.fibreOfHomeomorphLoopSpace g OnePoint.infty
    -- the two hypotheses of the Wang step
    have hfib : ∀ t : ℕ, 0 < t → t ≤ M - 1 → (∀ k : ℕ, t ≠ 2 * j * k) →
        Subsingleton ↥(Work.Cohomology.singularCohomology ℚ t
          (Work.StemsB.wangCohFsp (2 * j + 1) p)) := by
      intro t ht0 htM hne
      have hz : IsZero (Work.Serre.ratH
          (TopCat.of (Path (g OnePoint.infty) (g OnePoint.infty))) t) :=
        hLvan t ht0 (by omega) hne
      have hzF : IsZero (Work.Serre.ratH (Work.StemsB.wangCohFsp (2 * j + 1) p) t) :=
        Work.Stems.isZero_ratH_of_homeomorph hw t hz
      exact ModuleCat.isZero_iff_subsingleton.mp (Work.Serre.isZero_ratCoh_of_isZero_ratH_dup hzF)
    have hgen : ∀ k : ℕ, 1 ≤ k → ((2 * j + 1) - 1) * k ≤ M - 1 →
        Nonempty (Work.Cohomology.singularCohomology ℚ (((2 * j + 1) - 1) * k)
          (Work.StemsB.wangCohFsp (2 * j + 1) p) ≅ ModuleCat.of ℚ ℚ) := by
      intro k hk hkM
      have h2 : ((2 * j + 1) - 1) * k = 2 * j * k := by
        rw [show (2 * j + 1) - 1 = 2 * j from by omega]
      rw [h2]
      have hg : Nonempty (Work.Serre.ratH
          (TopCat.of (Path (g OnePoint.infty) (g OnePoint.infty))) (2 * j * k) ≅
            ModuleCat.of ℚ ℚ) :=
        hLgen k (by omega)
      have hgF : Nonempty (Work.Serre.ratH (Work.StemsB.wangCohFsp (2 * j + 1) p)
          (2 * j * k) ≅ ModuleCat.of ℚ ℚ) :=
        Work.Stems.isoRat_of_homotopyEquiv hw.toHomotopyEquiv (2 * j * k) hg
      exact (Work.Serre.ratCoh_ratH_iso_rat (Work.StemsB.wangCohFsp (2 * j + 1) p)
        (2 * j * k)).mpr hgF
    -- a generator of the fibre's cohomology in the fibre's fundamental degree
    have hgen1 : Nonempty (Work.Cohomology.singularCohomology ℚ ((2 * j + 1) - 1)
        (Work.StemsB.wangCohFsp (2 * j + 1) p) ≅ ModuleCat.of ℚ ℚ) := by
      obtain ⟨ex⟩ := hgen 1 (le_refl 1) (by omega)
      exact ⟨(eqToIso (congrArg (fun m => Work.Cohomology.singularCohomology ℚ m
        (Work.StemsB.wangCohFsp (2 * j + 1) p)) (Nat.mul_one ((2 * j + 1) - 1)))).symm ≪≫ ex⟩
    -- a non-zero fundamental class of the fibre
    have hNontriv : ¬ IsZero (Work.Cohomology.singularCohomology ℚ ((2 * j + 1) - 1)
        (Work.StemsB.wangCohFsp (2 * j + 1) p)) := by
      intro hz
      obtain ⟨ex1⟩ := hgen1
      have hzq : IsZero (ModuleCat.of ℚ ℚ) := IsZero.of_iso hz ex1.symm
      haveI : Subsingleton ℚ := ModuleCat.isZero_iff_subsingleton.mp hzq
      exact one_ne_zero (Subsingleton.elim (1 : ℚ) 0)
    obtain ⟨x, hxne⟩ : ∃ x : Work.Thom.Coh ℚ ((2 * j + 1) - 1) ↥(p ⁻¹' {OnePoint.infty}),
        x ≠ 0 := by
      by_contra hcon
      push_neg at hcon
      exact hNontriv (ModuleCat.isZero_iff_subsingleton.mpr
        ⟨fun a b => (hcon a).trans (hcon b).symm⟩)
    -- the cover is `n`-connected, so its degree `2j` cohomology vanishes
    have hEvan : IsZero (Work.Serre.ratH (TopCat.of E) (2 * j)) :=
      Work.Serre.serreE0Range E e₀ (2 * j + 1) (fun i hi => hconnE i hi) (2 * j)
        (by omega) (by omega)
    have hEcoh : Subsingleton ↥(Work.Cohomology.singularCohomology ℚ ((2 * j + 1) - 1)
        (TopCat.of E)) := by
      rw [show (2 * j + 1) - 1 = 2 * j from by omega]
      exact ModuleCat.isZero_iff_subsingleton.mp (Work.Serre.isZero_ratCoh_of_isZero_ratH_dup hEvan)
    obtain ⟨d_G, hT_G⟩ := Work.Stems.fibrewiseTrivial_sphLoopBig (by omega : 1 ≤ 2 * j + 1) E p hp
    have hT_O : Work.StemsB.FibrewiseTrivial p (Work.StemsB.sphLoopOuter (2 * j + 1))
        (Work.StemsB.dOuter (2 * j + 1)) :=
      Work.Stems.fibrewiseTrivial_sphLoopOuter E p hp
    obtain ⟨hlow, _⟩ := Work.StemsB.Rat.c2OddInput (2 * j + 1) (by omega) hodd E p d_G hT_G hT_O
      hEcoh hxne
    -- the all-degree Wang step
    have hWang : ∀ t : ℕ, (2 * j + 1) + 1 ≤ t → t ≤ M - 1 →
        Subsingleton ↥(Work.Cohomology.singularCohomology ℚ t (TopCat.of E)) :=
      Work.Stems.wangUptoBounded (2 * j + 1) (by omega) hodd E p hp hT_O d_G hT_G x hpcF
        Work.Stems.Collar.wangPowFormula_of_wangTheta_pow hlow (M - 1) hfib hgen
    -- the cover is rationally acyclic below `M-1`
    have hEacyc : Work.Serre.RatAcyclicBelow E (M - 1) := by
      refine ⟨fun t ht0 htM => ?_, ?_⟩
      · by_cases htn : t ≤ 2 * j + 1
        · exact Work.Serre.serreE0Range E e₀ (2 * j + 1) (fun i hi => hconnE i hi) t ht0
            (by omega)
        · exact Work.Stems.isZero_ratH_of_isZero_ratCoh
            (ModuleCat.isZero_iff_subsingleton.mpr (hWang t (by omega) htM))
      · exact Work.Serre.isIso_ratHomologyMap_toPoint_zero_of_subsingleton_pi0 E e₀
          (hconnE 0 (by omega))
    -- the mapping theorem
    haveI : PathConnectedSpace Y := hpcY
    obtain ⟨e⟩ := Work.Stems.mappingTheoremOfHomotopyFibreAcyclic hE3a g OnePoint.infty (M - 1)
      hEacyc d (by omega)
    have hzero : IsZero (Work.Serre.ratH (TopCat.of (Work.StemsB.SphModel (2 * j + 1))) d) :=
      Work.Stems.isZero_ratH_of_homeomorph Φ d
        ((Work.StemsB.sphRatHomology (2 * j + 1) (by omega)).2 d (by omega) hdn)
    exact IsZero.of_iso hzero e.symm


/-- **The odd step, level-local.**  The even clause at level `j` (at every top) gives the odd clause
at level `2j+1` (at every top). -/
theorem oddStepLocal (c : ℕ) (hE3a : Work.Serre.SerreE3a) (j : ℕ) (hj : 1 ≤ j)
    (heven : ∀ M : ℕ, EvenClause c j hj M) :
    ∀ N : ℕ, OddClause c (2 * j + 1) (by omega) N := by
  intro N X tX pt hX
  haveI hne2j : Nonempty (Fin (2 * j + 1)) := ⟨⟨0, by omega⟩⟩
  have hmain : Nonempty (Work.Serre.ratH (TopCat.of X) (2 * j + 1) ≅ ModuleCat.of ℚ ℚ) ∧
      (∀ d : ℕ, 0 < d → d < N - c * (2 * j + 1) → d ≠ 2 * j + 1 →
        IsZero (Work.Serre.ratH (TopCat.of X) d)) := by
    constructor
    · exact Work.Stems.ratH_iso_rat_of_conn_piIso (n := 2 * j + 1) (by omega) pt hX.1
        (fun i hi => hX.2 i (by omega) (Or.inl (by omega)))
    · intro d hd0 hdN hdn
      obtain ⟨P, tP, p₀, hP⟩ := Work.Serre.serreC0Range ℤ (2 * j + 1) (N + (2 * j + 1) + 1)
        (by omega) (by omega)
      letI : TopologicalSpace P := tP
      have hPzero : IsZero (Work.Serre.ratH (TopCat.of P) d) :=
        oddVanishingOfEvenLocal c hj heven hE3a p₀ hP d hd0 (by omega) hdn
      obtain ⟨e⟩ := Work.StemsB.rangeModel_ratH_iso_le (k := 2 * j + 1) (N := N)
        (M := N + (2 * j + 1) + 1) (by omega) (by omega) pt p₀ hX hP d (by omega)
      exact IsZero.of_iso hPzero e
  exact hmain

end

end Work.Stems
