import Mathlib
import Submission.Work.Stems.RankOneClauses
import Submission.Work.Stems.rankOne_hurewicz_rank
import Submission.Work.Stems.rankOne_hurewicz_torsion
import Submission.Work.Stems.wangLowDegree
import Submission.Work.Stems.wangUptoBounded
import Submission.Work.StemsB.Rat.WangThetaCupLow
import Submission.Work.Stems.fibreOfHomeomorphLoopSpace
import Submission.Work.Stems.isHurewiczFibration_homotopyFibreFst
import Submission.Work.Stems.wangOddStepSphere
import Submission.Work.Stems.StepI.SphereFibreTrivial
import Submission.Work.Serre.pathConnectedSpace_fibre_of_isSerreFibration
import Submission.Work.Stems.Engine.DualVanishing
import Submission.Work.Stems.Engine.Cohomology
import Submission.Work.Rat.homotopyFibre_ratAcyclicBelow_of_path
import Submission.Work.Rat.oddCoverAcyclicFull
import Submission.Work.Stems.mappingTheoremOfHomotopyFibreAcyclic
import Submission.Work.Stems.subsingleton_homotopyGroup_change_basepoint
import Submission.Work.Stems.sphereConnectivity
import Submission.Work.PiS.sphereIsometryHomeomorph
import Submission.Work.PiS.reflectionSphere

set_option synthInstance.maxHeartbeats 400000

/-!
# The rank-one cover of `S^{2j+1}` is rationally acyclic up to `M - 2j`

This is the "cover acyclicity" input of the rank-one odd step of the `C2` interface
(`Work.Stems.rankOne_oddStep`).  For a space `X` whose homotopy groups vanish up to degree `M`
except in degree `n = 2j+1`, and a map `f : Sⁿ → X`, the homotopy fibre `E = hofib f` — the cover
of `Sⁿ` — is rationally acyclic in degrees `0 < t ≤ M - 2j`.

The argument is Serre's Euler-class (Wang) argument, exactly as in the `K(ℤ,n)` layer
(`Work.Stems.c2OddStepLocal`), with the rational homology of the fibre `ΩX` supplied by the even
clause `Work.Stems.EvenClauseR`:

* degrees `t < 2j` come from the `(2j-1)`-connectivity of `E` (Serre's `E0`);
* degree `t = 2j` comes from the torsion of `π_{2j}(E)` (`Work.Stems.rankOne_hurewicz_torsion`);
* degrees `2j+1 ≤ t ≤ M - 2j` come from the Wang sequence of the sphere bundle
  `ΩX → E → Sⁿ` — `Work.Stems.wangLowDegree` for `t = 2j+1` and `Work.Stems.wangUptoBounded`
  above it — whose Euler class is non-zero by `Work.StemsB.Rat.c2OddInput`.

The Wang machinery is stated for the one-point model `SphModel (2j+1)` of the sphere; the reduction
from `Sph (2j+1)` to `SphModel (2j+1)` uses a homeomorphism of `SphModel (2j+1)` onto `Sph (2j+1)`
carrying `∞` to the prescribed base point `s₀` (built from a reflection of the sphere,
`Work.PiS.reflectionSphere`), so that the homotopy fibres of `f` and of the transported map are
identified on the nose.
-/

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

open CategoryTheory CategoryTheory.Limits
open scoped Topology

namespace Work.Stems

noncomputable section

/-- **The Wang argument, for a map out of the one-point sphere model.**  This is the direct
content of `rankOne_coverAcyclic`, with the source of the map taken to be `SphModel (2j+1)` over
its base point `∞` and the degree-`2j` vanishing of the cover taken as a hypothesis (it is the
torsion statement `Work.Stems.rankOne_hurewicz_torsion` in the application). -/
private theorem rankOne_coverAcyclic_model (j : ℕ) (hj : 1 ≤ j)
    {M : ℕ} {X : Type} [TopologicalSpace X] (x₀ : X)
    (hvan : ∀ i : ℕ, i ≤ M → i ≠ 2 * j + 1 → Subsingleton (HomotopyGroup (Fin i) X x₀))
    (hH : Nonempty (Work.Serre.ratH (TopCat.of X) (2 * j + 1) ≅ ModuleCat.of ℚ ℚ))
    (heven : ∀ N' : ℕ, Work.Stems.EvenClauseR j N')
    (g : C(Work.StemsB.SphModel (2 * j + 1), X))
    (hconn : ∀ i : ℕ, i ≤ 2 * j - 1 → Subsingleton (HomotopyGroup (Fin i)
      (Work.RatHurewicz.homotopyFibre g OnePoint.infty)
      (Work.RatHurewicz.homotopyFibreBasepoint g OnePoint.infty)))
    (h2j : CategoryTheory.Limits.IsZero (Work.Serre.ratH
      (TopCat.of (Work.RatHurewicz.homotopyFibre g OnePoint.infty)) (2 * j))) :
    Work.Serre.RatAcyclicBelow (Work.RatHurewicz.homotopyFibre g OnePoint.infty) (M - 2 * j) := by
  have hodd : Odd (2 * j + 1) := ⟨j, rfl⟩
  have hb : 2 ≤ 2 * j + 1 := by omega
  let E : Type := Work.RatHurewicz.homotopyFibre g OnePoint.infty
  let e₀ : E := Work.RatHurewicz.homotopyFibreBasepoint g OnePoint.infty
  let p : C(E, Work.StemsB.SphModel (2 * j + 1)) :=
    Work.RatHurewicz.homotopyFibreFst g OnePoint.infty
  have hp : Work.StemsB.IsHurewiczFibration p :=
    Work.Stems.isHurewiczFibration_homotopyFibreFst g OnePoint.infty
  -- low degrees: Serre's `E0` on the cover, which is `(2j-1)`-connected
  have hE0 : ∀ t : ℕ, 0 < t → t < 2 * j →
      CategoryTheory.Limits.IsZero (Work.Serre.ratH (TopCat.of E) t) :=
    fun t ht0 ht => Work.Serre.serreE0Range E e₀ (2 * j - 1)
      (fun i hi => hconn i hi) t ht0 (by omega)
  have h0iso : IsIso (Work.Serre.ratHomologyMap (Work.Serre.toPoint E) 0) :=
    Work.Serre.isIso_ratHomologyMap_toPoint_zero_of_subsingleton_pi0 E e₀ (hconn 0 (by omega))
  refine ⟨fun t ht0 htT => ?_, h0iso⟩
  rcases lt_trichotomy t (2 * j) with hlt | heq | hgt
  · exact hE0 t ht0 hlt
  · rw [heq]; exact h2j
  · -- the Wang range: `t ≥ 2j+1`
    have hT2j : 2 * j + 1 ≤ M - 2 * j := by omega
    -- the base point of `X`
    have hpcX : PathConnectedSpace X :=
      Work.RatHurewicz.pathConnectedSpace_of_subsingleton_pi_zero x₀
        (hvan 0 (Nat.zero_le M) (by omega))
    obtain ⟨γ⟩ := hpcX.joined x₀ (g OnePoint.infty)
    have hXvan : ∀ i : ℕ, i ≤ M → i ≠ 2 * j + 1 →
        Subsingleton (HomotopyGroup (Fin i) X (g OnePoint.infty)) :=
      fun i hi hin => Work.Stems.subsingleton_homotopyGroup_change_basepoint γ (hvan i hi hin)
    have hXconn : ∀ i : ℕ, i < 2 * j + 1 →
        Subsingleton (HomotopyGroup (Fin i) X (g OnePoint.infty)) :=
      fun i hi => hXvan i (by omega) (by omega)
    -- the loop space `ΩX` has a rank-one generator in degree `2j`
    have hloopgen : Nonempty (Work.Serre.ratH
        (TopCat.of (Path (g OnePoint.infty) (g OnePoint.infty))) (2 * j) ≅ ModuleCat.of ℚ ℚ) :=
      (Work.Stems.rankOne_hurewicz_rank (k := 2 * j + 1) (by omega) (g OnePoint.infty)
        hXconn hH).2
    -- connectivity of `ΩX` below degree `2j`
    have hloopvan : ∀ i : ℕ, i ≤ M - 1 → i ≠ 2 * j →
        Subsingleton (HomotopyGroup (Fin i) (Path (g OnePoint.infty) (g OnePoint.infty))
          (Path.refl (g OnePoint.infty))) := by
      intro i hi hne
      haveI : Subsingleton (HomotopyGroup (Fin (i + 1)) X (g OnePoint.infty)) :=
        hXvan (i + 1) (by omega) (by omega)
      exact (Work.Stems.curryEquivGroup (X := X) (x := g OnePoint.infty) i).symm.subsingleton
    have hM2j : 2 * j ≤ M - 1 := by omega
    -- the even clause computes the rational homology of the fibre `ΩX`
    obtain ⟨hgenLoop, hvanLoop⟩ := heven (M - 1) hM2j
      (X := Path (g OnePoint.infty) (g OnePoint.infty)) (Path.refl (g OnePoint.infty))
      hloopvan hloopgen
    -- the fibre of `p` is the loop space
    obtain ⟨hw⟩ := Work.Stems.fibreOfHomeomorphLoopSpace g OnePoint.infty
    have hfib : ∀ t : ℕ, 0 < t → t ≤ M - 2 * j → (∀ k : ℕ, t ≠ (2 * j + 1 - 1) * k) →
        Subsingleton ↥(Work.Cohomology.singularCohomology ℚ t (Work.StemsB.wangCohFsp (2 * j + 1) p)) := by
      intro t ht0 htT hne
      have hne' : ∀ k : ℕ, t ≠ 2 * j * k :=
        fun k hk => hne k (by rw [show (2 * j + 1 - 1) = 2 * j from rfl]; exact hk)
      have hz : CategoryTheory.Limits.IsZero (Work.Serre.ratH
          (TopCat.of (Path (g OnePoint.infty) (g OnePoint.infty))) t) :=
        hvanLoop t (by omega) hne'
      have hzF : CategoryTheory.Limits.IsZero (Work.Serre.ratH
          (TopCat.of (Work.RatHurewicz.fibreOf g OnePoint.infty)) t) :=
        Work.Stems.isZero_ratH_of_homeomorph hw t hz
      exact ModuleCat.isZero_iff_subsingleton.mp
        (Work.Serre.isZero_ratCoh_of_isZero_ratH hzF)
    have hgen : ∀ k : ℕ, 1 ≤ k → (2 * j + 1 - 1) * k ≤ M - 2 * j →
        Nonempty (Work.Cohomology.singularCohomology ℚ ((2 * j + 1 - 1) * k)
          (Work.StemsB.wangCohFsp (2 * j + 1) p) ≅ ModuleCat.of ℚ ℚ) := by
      intro k hk hkM
      have hkb : (2 * j + 1 - 1) * k = 2 * j * k :=
        congrArg (fun m => m * k) (show 2 * j + 1 - 1 = 2 * j from rfl)
      rw [hkb] at hkM
      have hk2 : 2 * j * k ≤ (M - 1) - 2 * j + 1 := by omega
      obtain ⟨e⟩ := hgenLoop k hk2
      have heF : Nonempty (Work.Serre.ratH
          (TopCat.of (Work.RatHurewicz.fibreOf g OnePoint.infty)) (2 * j * k) ≅
            ModuleCat.of ℚ ℚ) :=
        Work.Stems.isoRat_of_homotopyEquiv hw.toHomotopyEquiv (2 * j * k) ⟨e⟩
      obtain ⟨c⟩ := (Work.Serre.ratCoh_ratH_iso_rat
        (TopCat.of (Work.RatHurewicz.fibreOf g OnePoint.infty)) (2 * j * k)).mpr heF
      refine ⟨(eqToIso (congrArg (fun m => Work.Cohomology.singularCohomology ℚ m
        (Work.StemsB.wangCohFsp (2 * j + 1) p)) hkb.symm)).symm ≪≫ c⟩
    -- the cover is rationally acyclic in degree `2j`, so the low transgression is non-zero
    have hE : Subsingleton ↥(Work.Cohomology.singularCohomology ℚ ((2 * j + 1) - 1)
        (TopCat.of E)) :=
      ModuleCat.isZero_iff_subsingleton.mp (Work.Serre.isZero_ratCoh_of_isZero_ratH h2j)
    have hgen1 : Nonempty (Work.Cohomology.singularCohomology ℚ ((2 * j + 1) - 1)
        (Work.StemsB.wangCohFsp (2 * j + 1) p) ≅ ModuleCat.of ℚ ℚ) := by
      have h1 := hgen 1 le_rfl (by omega)
      rwa [Nat.mul_one] at h1
    have hNontriv : ¬ CategoryTheory.Limits.IsZero (Work.Cohomology.singularCohomology ℚ
        ((2 * j + 1) - 1) (Work.StemsB.wangCohFsp (2 * j + 1) p)) := by
      intro hz
      obtain ⟨ex1⟩ := hgen1
      have hzq : CategoryTheory.Limits.IsZero (ModuleCat.of ℚ ℚ) := IsZero.of_iso hz ex1.symm
      haveI : Subsingleton ℚ := ModuleCat.isZero_iff_subsingleton.mp hzq
      exact one_ne_zero (Subsingleton.elim (1 : ℚ) 0)
    obtain ⟨x, hxne⟩ : ∃ x : Work.Thom.Coh ℚ ((2 * j + 1) - 1)
        ↥((Work.RatHurewicz.homotopyFibreFst g OnePoint.infty) ⁻¹' {OnePoint.infty}), x ≠ 0 := by
      by_contra hcon
      push_neg at hcon
      exact hNontriv (ModuleCat.isZero_iff_subsingleton.mpr
        ⟨fun a b => (hcon a).trans (hcon b).symm⟩)
    -- fibrewise triviality of the sphere fibration
    obtain ⟨d_G, hT_G⟩ := Work.Stems.fibrewiseTrivial_sphLoopBig (by omega : 1 ≤ 2 * j + 1) E p hp
    have hT_O : Work.StemsB.FibrewiseTrivial p (Work.StemsB.sphLoopOuter (2 * j + 1))
        (Work.StemsB.dOuter (2 * j + 1)) :=
      Work.Stems.fibrewiseTrivial_sphLoopOuter E p hp
    -- path connectedness of the cover and of its fibre
    have hpcE : PathConnectedSpace E :=
      Work.RatHurewicz.pathConnectedSpace_of_subsingleton_pi_zero e₀ (hconn 0 (by omega))
    have hsource0 : Subsingleton (HomotopyGroup (Fin 0) (Work.StemsB.SphModel (2 * j + 1))
        OnePoint.infty) :=
      Work.Stems.subsingleton_homotopyGroup_fin_of_homeomorph
        (Work.Stems.onePointSphereHomeo (2 * j + 1)) rfl 0
        (Work.Stems.sphereConnectivity (2 * j + 1) 0 (by omega)
          ((Work.Stems.onePointSphereHomeo (2 * j + 1)) OnePoint.infty))
    have hpi1SphM : Subsingleton (HomotopyGroup (Fin 1) (Work.StemsB.SphModel (2 * j + 1))
        OnePoint.infty) :=
      Work.Stems.subsingleton_homotopyGroup_fin_of_homeomorph
        (Work.Stems.onePointSphereHomeo (2 * j + 1)) rfl 1
        (Work.Stems.sphereConnectivity (2 * j + 1) 1 (by omega)
          ((Work.Stems.onePointSphereHomeo (2 * j + 1)) OnePoint.infty))
    have hpcSphM : PathConnectedSpace (Work.StemsB.SphModel (2 * j + 1)) :=
      Work.RatHurewicz.pathConnectedSpace_of_subsingleton_pi_zero OnePoint.infty hsource0
    have hpcF : PathConnectedSpace ↥((Work.RatHurewicz.homotopyFibreFst g OnePoint.infty)
        ⁻¹' {OnePoint.infty}) :=
      Work.Serre.pathConnectedSpace_fibre_of_isSerreFibration p hp.isSerreFibration OnePoint.infty
        hpcE hpcSphM hpi1SphM
    -- the low-degree Wang class is non-zero
    obtain ⟨hlow, _⟩ := Work.StemsB.Rat.c2OddInput (2 * j + 1) hb hodd E p d_G hT_G hT_O hE hxne
    -- degree `2j+1` of the cover
    have hnot : ∀ k : ℕ, 2 * j + 1 ≠ (2 * j + 1 - 1) * k := by
      intro k hk
      rw [show 2 * j + 1 - 1 = 2 * j from rfl] at hk
      have h1 : 1 ≤ k := by
        by_contra h0
        rw [Nat.not_le] at h0
        have hk0 : k = 0 := by omega
        rw [hk0, Nat.mul_zero] at hk
        omega
      by_cases hk2 : 2 ≤ k
      · have hle : 2 * j * 2 ≤ 2 * j + 1 := by
          have h2 : 2 * j * 2 ≤ 2 * j * k := Nat.mul_le_mul_left _ hk2
          rwa [← hk] at h2
        have h4 : 4 * j ≤ 2 * j + 1 := by
          calc 4 * j = 2 * j * 2 := by ring
            _ ≤ 2 * j + 1 := hle
        omega
      · have hk1 : k = 1 := by omega
        rw [hk1, Nat.mul_one] at hk
        omega
    have hfib_n : Subsingleton ↥(Work.Cohomology.singularCohomology ℚ (2 * j + 1)
        (Work.StemsB.wangCohFsp (2 * j + 1) p)) :=
      hfib (2 * j + 1) (by omega) (by omega) hnot
    have hwanLow : Subsingleton ↥(Work.Cohomology.singularCohomology ℚ (2 * j + 1)
        (TopCat.of E)) :=
      Work.Stems.wangLowDegree (2 * j + 1) hb hodd E p hp hT_O d_G hT_G x hpcF hlow hfib_n
    have hwanUp : ∀ t : ℕ, 2 * j + 1 + 1 ≤ t → t ≤ M - 2 * j →
        Subsingleton ↥(Work.Cohomology.singularCohomology ℚ t (TopCat.of E)) :=
      Work.Stems.wangUptoBounded (2 * j + 1) hb hodd E p hp hT_O d_G hT_G x hpcF
        Work.Stems.Collar.wangPowFormula_of_wangTheta_pow hlow (M - 2 * j) hfib hgen
    rcases eq_or_lt_of_le (by omega : 2 * j + 1 ≤ t) with hEq | hLt
    · rw [← hEq]
      exact Work.Stems.isZero_ratH_of_isZero_ratCoh
        (ModuleCat.isZero_iff_subsingleton.mpr hwanLow)
    · exact Work.Stems.isZero_ratH_of_isZero_ratCoh
        (ModuleCat.isZero_iff_subsingleton.mpr (hwanUp t (by omega) htT))

/-- **There is a homeomorphism of `Sⁿ` (`n ≥ 1`) carrying any prescribed point to any other**: the
reflection in the hyperplane orthogonal to the difference. -/
private theorem sphere_homeo_point (n : ℕ) (x y : Work.Serre.Sph n) :
    ∃ Φ : Work.Serre.Sph n ≃ₜ Work.Serre.Sph n, Φ x = y := by
  obtain ⟨Φ, hΦ⟩ := Work.PiS.sphereIsometryHomeomorph n
    (((ℝ ∙ ((x : EuclideanSpace ℝ (Fin (n + 1)))
      - (y : EuclideanSpace ℝ (Fin (n + 1)))))ᗮ).reflection)
  exact ⟨Φ, Subtype.ext (by rw [hΦ]; exact Work.PiS.reflectionSphere n x y)⟩

theorem rankOne_coverAcyclic (j : ℕ) (hj : 1 ≤ j) [Nonempty (Fin (2 * j))] [Nonempty (Fin (2 * j + 1))]
    {M : ℕ} {X : Type} [TopologicalSpace X] (x₀ : X)
    (hvan : ∀ i : ℕ, i ≤ M → i ≠ 2 * j + 1 → Subsingleton (HomotopyGroup (Fin i) X x₀))
    (hH : Nonempty (Work.Serre.ratH (TopCat.of X) (2 * j + 1) ≅ ModuleCat.of ℚ ℚ))
    (heven : ∀ N' : ℕ, Work.Stems.EvenClauseR j N')
    (s₀ : Work.Serre.Sph (2 * j + 1)) (f : C(Work.Serre.Sph (2 * j + 1), X))
    (hconn : ∀ i : ℕ, i ≤ 2 * j - 1 → Subsingleton (HomotopyGroup (Fin i)
      (Work.RatHurewicz.homotopyFibre f s₀)
      (Work.RatHurewicz.homotopyFibreBasepoint f s₀)))
    (htors : ∀ α : HomotopyGroup (Fin (2 * j)) (Work.RatHurewicz.homotopyFibre f s₀)
      (Work.RatHurewicz.homotopyFibreBasepoint f s₀), ∃ m : ℕ, 0 < m ∧ α ^ m = 1)
    (hconn_n : Subsingleton (HomotopyGroup (Fin (2 * j + 1))
      (Work.RatHurewicz.homotopyFibre f s₀)
      (Work.RatHurewicz.homotopyFibreBasepoint f s₀))) :
    Work.Serre.RatAcyclicBelow (Work.RatHurewicz.homotopyFibre f s₀) (M - 2 * j) := by
  -- a homeomorphism `SphModel (2j+1) ≃ₜ Sph (2j+1)` carrying `∞` to `s₀`
  obtain ⟨ρ, hρ⟩ : ∃ ρ : Work.Serre.Sph (2 * j + 1) ≃ₜ Work.Serre.Sph (2 * j + 1),
      ρ ((Work.Stems.onePointSphereHomeo (2 * j + 1)) OnePoint.infty) = s₀ :=
    sphere_homeo_point (2 * j + 1) ((Work.Stems.onePointSphereHomeo (2 * j + 1)) OnePoint.infty) s₀
  let Ψ : Work.StemsB.SphModel (2 * j + 1) ≃ₜ Work.Serre.Sph (2 * j + 1) :=
    (Work.Stems.onePointSphereHomeo (2 * j + 1)).trans ρ
  have hΨinf : Ψ OnePoint.infty = s₀ := hρ
  let g : C(Work.StemsB.SphModel (2 * j + 1), X) :=
    f.comp { toFun := ⇑Ψ, continuous_toFun := Ψ.continuous_toFun }
  -- the connectivity hypothesis of the cover
  have hconn_g : ∀ i : ℕ, i ≤ 2 * j - 1 → Subsingleton (HomotopyGroup (Fin i)
      (Work.RatHurewicz.homotopyFibre g OnePoint.infty)
      (Work.RatHurewicz.homotopyFibreBasepoint g OnePoint.infty)) := by
    intro i hi
    refine Work.Stems.subsingleton_homotopyGroup_fin_of_homeomorph
      (Work.RatHurewicz.homotopyFibreHomeo f Ψ OnePoint.infty) rfl i ?_
    change Subsingleton (HomotopyGroup (Fin i)
      (Work.RatHurewicz.homotopyFibre f (Ψ OnePoint.infty))
      (Work.RatHurewicz.homotopyFibreBasepoint f (Ψ OnePoint.infty)))
    rw [hΨinf]
    exact hconn i hi
  -- the torsion of `π_{2j}` of the cover, giving its vanishing in degree `2j`
  have h2j_f : CategoryTheory.Limits.IsZero (Work.Serre.ratH
      (TopCat.of (Work.RatHurewicz.homotopyFibre f s₀)) (2 * j)) :=
    Work.Stems.rankOne_hurewicz_torsion (by omega)
      (Work.RatHurewicz.homotopyFibreBasepoint f s₀)
      (fun i hi => hconn i (by omega)) htors
  have h2j_g : CategoryTheory.Limits.IsZero (Work.Serre.ratH
      (TopCat.of (Work.RatHurewicz.homotopyFibre g OnePoint.infty)) (2 * j)) := by
    have h1 : CategoryTheory.Limits.IsZero (Work.Serre.ratH
        (TopCat.of (Work.RatHurewicz.homotopyFibre f (Ψ OnePoint.infty))) (2 * j)) := by
      rw [hΨinf]
      exact h2j_f
    exact Work.Stems.isZero_ratH_of_homeomorph
      (Work.RatHurewicz.homotopyFibreHomeo f Ψ OnePoint.infty) (2 * j) h1
  -- run the Wang argument on the one-point model and transport the conclusion back
  have hA : Work.Serre.RatAcyclicBelow
      (Work.RatHurewicz.homotopyFibre f (Ψ OnePoint.infty)) (M - 2 * j) :=
    Work.Rat.homotopyFibre_precomp_ratAcyclicBelow Ψ f OnePoint.infty (M - 2 * j)
      (rankOne_coverAcyclic_model j hj x₀ hvan hH heven g hconn_g h2j_g)
  refine Work.Stems.ratAcyclicBelow_of_ratH_iso hA (fun m => ?_)
  exact ⟨eqToIso (congrArg (fun a => Work.Serre.ratH
    (TopCat.of (Work.RatHurewicz.homotopyFibre f a)) m) hΨinf)⟩

end

end Work.Stems
