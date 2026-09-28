import Mathlib
import Submission.Work.Stems.c2evenFree_of_c2oddFree
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

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# The odd step of the free-top `C2` interface

*(Area STEMS.  See `Submission/Work/Stems/C2ODD_PLAN.md`, `C2ODD_STEP_STATE.md` §4.2 and
`Engine/C2FreeTop.lean`.)*

`Work.Stems.Engine.C2oddFree c` says that a **range model** of `K(ℤ,n)` (`n` odd) through degree
`N` has the rational homology of `Sⁿ` through degree `N - c·n`.  This file derives it from

* the *even* step of the same interface, `Work.Stems.Engine.C2evenFree c` (the rational homology of
  a range model of `K(ℤ,2j)` through `N` is that of `ℂP^∞`, rescaled by `2j`, through
  `N - c·2j`),
* the mapping theorem `Work.Serre.SerreE3a`,
* the base case `n = 1`, taken as a hypothesis (`hbase`).

## The odd step

Let `n = 2j+1` be odd, `j ≥ 1`, and `Y` a range model of `K(ℤ,n)` through `M`.  The bottom cell
`f : Sⁿ → Y` (`Work.RatHurewicz.exists_bijective_piMapN_rangeModel`) has an `n`-connected homotopy
fibre `E` (`Work.Stems.homotopyFibre_conn`, in the range form `homotopyFibre_conn_of_range`).  The
projection `E → Sⁿ` (in the one-point model of the sphere, so that the Wang machinery of area
STEMSB applies) is a Hurewicz fibration whose fibre is the loop space `ΩY`; the fibre is a range
model of `K(ℤ,2j)` through `M-1` (`Work.Stems.isEMSpaceUpTo_loop'`), so by the even step — applied
to a range model with a *huge* top and transported back along
`Work.StemsB.rangeModel_ratH_iso_le` — its rational homology is known as `ℚ[x_{2j}]` in every degree
`< M`.  The all-degree Wang step `Work.Stems.wangUptoBounded` (with the multiplicativity of the
transgression, `Work.Stems.Collar.wangPowFormula_of_wangTheta_pow`) then makes `E` rationally
acyclic below `M-1`; the mapping theorem turns that into `H_i(Sⁿ;ℚ) ≅ H_i(Y;ℚ)` for `i < M-1`, and
the rational homology of the sphere gives the claim.

The final statement `C2oddFree c` additionally transfers from a range model with a large top
(`N + (2j+1) + 1`) down to the given model through `N` (`Work.StemsB.rangeModel_ratH_iso_le`),
which absorbs the one degree lost by the mapping theorem's indexing.
-/

namespace Work.Stems

noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped Topology

set_option maxHeartbeats 1600000

/-! ## Base point change for range models -/

/-- **A range model of `K(A,m)` at a point is a range model at any point of the same component.** -/
theorem isEMSpaceUpTo_change_basepoint {A : Type} [AddCommGroup A] {m N : ℕ} (hm : 0 < m)
    {X : Type} [TopologicalSpace X] {pt x : X} (γ : Path pt x)
    (h : Work.Serre.IsEMSpaceUpTo A m hm N X pt) :
    Work.Serre.IsEMSpaceUpTo A m hm N X x := by
  have hne : Nonempty (Fin m) := ⟨⟨0, hm⟩⟩
  refine ⟨?_, ?_⟩
  · obtain ⟨e⟩ := h.1
    obtain ⟨e'⟩ := @basepoint_iso (Fin m) X _ _ hne pt x γ
    exact ⟨e'.symm.trans e⟩
  · intro i hi hc
    exact subsingleton_homotopyGroup_change_basepoint γ (h.2 i hi hc)

/-! ## Connectivity of the cover, in range form -/

/-- **The homotopy fibre of a `πₙ`-bijective map from a `(n-1)`-connected source into a space with
`π_i = 0` for `i ≤ n+1`, `i ≠ n`, is `n`-connected.**  Range version of
`Work.Stems.homotopyFibre_conn`: only the two degrees used by the argument are needed. -/
theorem homotopyFibre_conn_of_range {B X : Type} [TopologicalSpace B] [TopologicalSpace X] {n : ℕ}
    (hn : 3 ≤ n) (f : C(B, X)) (b₀ : B)
    (hsource : ∀ i : ℕ, i < n → Subsingleton (HomotopyGroup (Fin i) B b₀))
    (hbij : Function.Bijective (Work.Serre.piMapN f n b₀))
    (hX : ∀ i : ℕ, i ≤ n + 1 → i ≠ n → Subsingleton (HomotopyGroup (Fin i) X (f b₀))) :
    ∀ k : ℕ, k ≤ n → Subsingleton (HomotopyGroup (Fin k)
      (Work.RatHurewicz.homotopyFibre f b₀)
      (Work.RatHurewicz.homotopyFibreBasepoint f b₀)) := by
  refine Work.Stems.subsingleton_homotopyFibre_of_inj_surj f n (by omega) b₀ ?_ ?_
  · intro i hi
    by_cases hin : i = n
    · subst hin; exact hbij.1
    · haveI : Subsingleton (HomotopyGroup (Fin i) B b₀) := hsource i (by omega)
      exact fun a b _ => Subsingleton.elim a b
  · intro i hi
    by_cases hin : i = n
    · subst hin; exact hbij.2
    · haveI : Subsingleton (HomotopyGroup (Fin i) X (f b₀)) := hX i (by omega) hin
      exact fun y => ⟨Classical.choice (inferInstance : Nonempty (HomotopyGroup (Fin i) B b₀)),
        Subsingleton.elim _ y⟩

/-! ## The loop space of a range model, in the range of its own top -/

/-- **The even-model knowledge of the loop space, at every degree below the model's top.**  If `Y`
is a range model of `K(ℤ,2j+1)` through `M` (`j ≥ 1`), the loop space `ΩY` — a range model of
`K(ℤ,2j)` through `M-1` — has the rational homology of `ℂP^∞` rescaled by `2j` in every degree
`< M`: the knowledge always available from `C2evenFree c` is obtained by comparing with a range
model of `K(ℤ,2j)` with a top large enough to absorb the allowance `c·2j`
(`Work.StemsB.rangeModel_ratH_iso_le`). -/
theorem loopKnowledge (c : ℕ) (h : Work.Stems.Engine.C2evenFree c) {j M : ℕ} (hj : 1 ≤ j)
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
  have hPmod := h j hj M' P p₀ hP
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

theorem oddModelVanishingOfEven (c : ℕ) (h : Work.Stems.Engine.C2evenFree c)
    (hE3a : Work.Serre.SerreE3a) {j M : ℕ} (hj : 1 ≤ j)
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
    obtain ⟨hLgen, hLvan⟩ := loopKnowledge c h hj (g OnePoint.infty) hYg
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

/-! ## The `C2` odd interface -/

theorem c2oddFree_of_c2evenFree (c : ℕ) (h : Work.Stems.Engine.C2evenFree c)
    (hE3a : Work.Serre.SerreE3a)
    (hbase : ∀ (N : ℕ) (X : Type) [TopologicalSpace X] (pt : X),
      Work.Serre.IsEMSpaceUpTo ℤ 1 (by norm_num) N X pt →
      Nonempty (Work.Serre.ratH (TopCat.of X) 1 ≅ ModuleCat.of ℚ ℚ) ∧
      (∀ d : ℕ, 0 < d → d < N - c * 1 → d ≠ 1 →
        CategoryTheory.Limits.IsZero (Work.Serre.ratH (TopCat.of X) d))) :
    Work.Stems.Engine.C2oddFree c := by
  intro n hn hodd N X tX pt hX
  obtain ⟨j, hj⟩ := hodd
  haveI hneN : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  haveI hne2j : Nonempty (Fin (2 * j + 1)) := ⟨⟨0, by omega⟩⟩
  -- the range model structure at the index `2*j+1`
  have hX' : Work.Serre.IsEMSpaceUpTo ℤ (2 * j + 1) (by omega) N X pt := by
    refine ⟨?_, ?_⟩
    · obtain ⟨e⟩ := hX.1
      exact ⟨(Work.Stems.piMulEquivOfIndexEq hj).symm.trans e⟩
    · intro i hi hc
      refine hX.2 i (by omega) ?_
      rcases hc with h | h
      · exact Or.inl (by omega)
      · exact Or.inr h
  rcases Nat.eq_zero_or_pos j with hj0 | hj1
  · -- `n = 1`: the base case
    subst hj0
    have hj1' : n = 1 := hj.trans (show 2 * 0 + 1 = 1 from rfl)
    have hX'' : Work.Serre.IsEMSpaceUpTo ℤ 1 (by norm_num) N X pt := by simpa using hX'
    have hres := hbase N X pt hX''
    refine ⟨?_, ?_⟩
    · obtain ⟨e⟩ := hres.1
      exact ⟨eqToIso (congrArg (fun m => Work.Serre.ratH (TopCat.of X) m) hj1') ≪≫ e⟩
    · intro d hd0 hdN hdn
      exact hres.2 d hd0 (by rw [← hj1']; exact hdN) (by rw [← hj1']; exact hdn)
  · -- the odd step at index `2*j+1`
    have hmain : Nonempty (Work.Serre.ratH (TopCat.of X) (2 * j + 1) ≅ ModuleCat.of ℚ ℚ) ∧
        (∀ d : ℕ, 0 < d → d < N - c * (2 * j + 1) → d ≠ 2 * j + 1 →
          IsZero (Work.Serre.ratH (TopCat.of X) d)) := by
      constructor
      · exact Work.Stems.ratH_iso_rat_of_conn_piIso (n := 2 * j + 1) (by omega) pt hX'.1
          (fun i hi => hX'.2 i (by omega) (Or.inl (by omega)))
      · intro d hd0 hdN hdn
        obtain ⟨P, tP, p₀, hP⟩ := Work.Serre.serreC0Range ℤ (2 * j + 1) (N + (2 * j + 1) + 1)
          (by omega) (by omega)
        letI : TopologicalSpace P := tP
        have hPzero : IsZero (Work.Serre.ratH (TopCat.of P) d) :=
          oddModelVanishingOfEven c h hE3a hj1 p₀ hP d hd0 (by omega) hdn
        obtain ⟨e⟩ := Work.StemsB.rangeModel_ratH_iso_le (k := 2 * j + 1) (N := N)
          (M := N + (2 * j + 1) + 1) (by omega) (by omega) pt p₀ hX' hP d (by omega)
        exact IsZero.of_iso hPzero e
    refine ⟨?_, ?_⟩
    · obtain ⟨e⟩ := hmain.1
      exact ⟨eqToIso (congrArg (fun m => Work.Serre.ratH (TopCat.of X) m) hj) ≪≫ e⟩
    · intro d hd0 hdN hdn
      refine hmain.2 d hd0 ?_ ?_
      · rw [show c * (2 * j + 1) = c * n from by rw [hj]]
        exact hdN
      · rw [← hj]
        exact hdn

end

end Work.Stems
