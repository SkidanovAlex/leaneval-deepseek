import Mathlib
import Submission.Work.Rat.c2FreeAssembly
import Submission.Work.Stems.c2OddStepLocal
import Submission.Work.Serre.serreE3a
import Submission.Work.RatHurewicz.Cofibre.BMHyp
import Submission.Work.Serre.serreRangeEMVanAll
import Submission.Work.Rat.homotopyFibre_ratAcyclicBelow_of_path
import Submission.Work.Serre.EulerFibreRoot

open CategoryTheory CategoryTheory.Limits
open scoped Topology

namespace Work.Rat

noncomputable section

set_option maxHeartbeats 1600000

/-! ## Inputs

* `evenClauseOne` — the even clause of the free-top `C2` interface at every level and top, from
  `SerreE3b` (via the already assembled `Work.Rat.c2Free_both`).
* `homotopyFibre_precomp_ratAcyclicBelow` — precomposition of the map by a homeomorphism of the
  source does not change the homotopy fibre up to homeomorphism.
* `Work.Rat.homotopyFibre_ratAcyclicBelow_of_path` — base point change along a path in the source.
-/

/-- The even clause at every level and top, from `SerreE3b`. -/
theorem evenClauseOne (hE3b : Work.Serre.SerreE3b) (hE3a : Work.Serre.SerreE3a) :
    ∀ (j : ℕ) (hj : 1 ≤ j) (N : ℕ), Work.Stems.EvenClause 1 j hj N :=
  (Work.Stems.c2evenFree_iff 1).mp (Work.Rat.c2Free_both 1 hE3b hE3a).1

/-- Precomposing the map with a homeomorphism of the source: the homotopy fibres are homeomorphic,
hence have the same rational homology. -/
theorem homotopyFibre_precomp_ratAcyclicBelow {A B : Type} [TopologicalSpace A]
    [TopologicalSpace B] {X : Type} [TopologicalSpace X] (e : A ≃ₜ B) (f : C(B, X)) (a : A)
    (N : ℕ)
    (h : Work.Serre.RatAcyclicBelow
      (Work.RatHurewicz.homotopyFibre (f.comp (⟨e, e.continuous_toFun⟩ : C(A, B))) a) N) :
    Work.Serre.RatAcyclicBelow (Work.RatHurewicz.homotopyFibre f (e a)) N :=
  Work.Serre.ratAcyclicBelow_of_homotopyEquiv
    (Work.RatHurewicz.homotopyFibreHomeo f e a).symm.toHomotopyEquiv h

/-! ## The case `M - 1 ≤ 2j+1`: the cover is `(M-1)`-connected

If the range model is only known through `M ≤ 2j+2`, the cover `E = hofib f` has vanishing
homotopy groups up to `M - 1` (`Work.Stems.subsingleton_homotopyFibre_of_inj_surj`), and Serre's
`E0` turns that into rational acyclicity. -/

theorem oddCoverAcyclicSmall {j : ℕ} (hj : 1 ≤ j) {M : ℕ} (hMle : M - 1 ≤ 2 * j + 1)
    {X : Type} [TopologicalSpace X] (pt : X)
    (hX : Work.Serre.IsEMSpaceUpTo ℤ (2 * j + 1) (by omega) M X pt)
    (s₀ : Work.Serre.Sph (2 * j + 1)) (f : C(Work.Serre.Sph (2 * j + 1), X))
    (hbij : Function.Bijective (Work.Serre.piMapN f (2 * j + 1) s₀)) :
    Work.Serre.RatAcyclicBelow (Work.RatHurewicz.homotopyFibre f s₀) (M - 1) := by
  have hpcX : PathConnectedSpace X :=
    Work.RatHurewicz.pathConnectedSpace_of_subsingleton_pi_zero pt
      (hX.2 0 (by omega) (Or.inl (by omega)))
  obtain ⟨γ⟩ := hpcX.joined pt (f s₀)
  have hX' : Work.Serre.IsEMSpaceUpTo ℤ (2 * j + 1) (by omega) M X (f s₀) :=
    Work.Stems.isEMSpaceUpTo_change_basepoint (by omega) γ hX
  set N : ℕ := max (M - 1) 1 with hN
  have hN1 : 1 ≤ N := by rw [hN]; exact le_max_right _ _
  have hNM : M - 1 ≤ N := by rw [hN]; exact le_max_left _ _
  have hNn : N ≤ 2 * j + 1 := by rw [hN]; exact max_le (by omega) (by omega)
  have hinj : ∀ i : ℕ, i ≤ N → Function.Injective (Work.Serre.piMapN f i s₀) := by
    intro i hi
    by_cases hin : i = 2 * j + 1
    · rw [hin]; exact hbij.1
    · haveI : Subsingleton (HomotopyGroup (Fin i) (Work.Serre.Sph (2 * j + 1)) s₀) :=
        Work.Stems.sphereConnectivity (2 * j + 1) i (by omega) s₀
      exact fun a b _ => Subsingleton.elim a b
  have hsurj : ∀ i : ℕ, i ≤ N + 1 → Function.Surjective (Work.Serre.piMapN f i s₀) := by
    intro i hi
    by_cases hin : i = 2 * j + 1
    · rw [hin]; exact hbij.2
    · haveI : Subsingleton (HomotopyGroup (Fin i) X (f s₀)) :=
        hX'.2 i hin (by
          rcases lt_or_ge i (2 * j + 1) with hlt | hge
          · exact Or.inl hlt
          · exact Or.inr (by omega))
      exact fun y => ⟨default, Subsingleton.elim _ y⟩
  have hconn : ∀ k : ℕ, k ≤ N → Subsingleton (HomotopyGroup (Fin k)
      (Work.RatHurewicz.homotopyFibre f s₀)
      (Work.RatHurewicz.homotopyFibreBasepoint f s₀)) :=
    Work.Stems.subsingleton_homotopyFibre_of_inj_surj f N hN1 s₀ hinj hsurj
  refine ⟨fun t ht0 htM => ?_, ?_⟩
  · exact Work.Serre.serreE0Range _ _ N (fun i hi => hconn i hi) t ht0 (by omega)
  · exact Work.Serre.isIso_ratHomologyMap_toPoint_zero_of_subsingleton_pi0 _ _
      (hconn 0 (by omega))

/-! ## The case `2j+3 ≤ M`: the Wang argument

This is the proof of `Work.Stems.oddModelVanishingOfEven`'s internal `hEacyc`, adapted to a
*bottom cell `f` given in advance* (rather than one produced by
`Work.RatHurewicz.exists_bijective_piMapN_rangeModel`): the Wang machinery is set up for a map out
of the one-point model `SphModel (2j+1)`, so we precompose with `Φ`, run the argument, and transfer
the conclusion back along `Φ`. -/

theorem oddCoverAcyclicBig (hE3b : Work.Serre.SerreE3b) (hE3a : Work.Serre.SerreE3a)
    {j : ℕ} (hj : 1 ≤ j) {M : ℕ} (hMbig : 2 * j + 1 + 2 ≤ M)
    {X : Type} [TopologicalSpace X] (pt : X)
    (hX : Work.Serre.IsEMSpaceUpTo ℤ (2 * j + 1) (by omega) M X pt)
    (s₀ : Work.Serre.Sph (2 * j + 1)) (f : C(Work.Serre.Sph (2 * j + 1), X))
    (hbij : Function.Bijective (Work.Serre.piMapN f (2 * j + 1) s₀)) :
    Work.Serre.RatAcyclicBelow (Work.RatHurewicz.homotopyFibre f s₀) (M - 1) := by
  have hEven : ∀ (M' : ℕ), Work.Stems.EvenClause 1 j hj M' :=
    fun M' => evenClauseOne hE3b hE3a j hj M'
  have hn3 : 3 ≤ 2 * j + 1 := by omega
  have hodd : Odd (2 * j + 1) := ⟨j, rfl⟩
  have hpcX : PathConnectedSpace X :=
    Work.RatHurewicz.pathConnectedSpace_of_subsingleton_pi_zero pt
      (hX.2 0 (by omega) (Or.inl (by omega)))
  let Φ : Work.StemsB.SphModel (2 * j + 1) ≃ₜ Work.Serre.Sph (2 * j + 1) :=
    Work.Stems.onePointSphereHomeo (2 * j + 1)
  have hpcSph : PathConnectedSpace (Work.Serre.Sph (2 * j + 1)) :=
    Work.RatHurewicz.pathConnectedSpace_of_subsingleton_pi_zero s₀
      (Work.Stems.sphereConnectivity (2 * j + 1) 0 (by omega) s₀)
  let g : C(Work.StemsB.SphModel (2 * j + 1), X) :=
    f.comp (⟨Φ, Φ.continuous_toFun⟩ : C(Work.StemsB.SphModel (2 * j + 1),
      Work.Serre.Sph (2 * j + 1)))
  have hjoin : Joined s₀ (Φ OnePoint.infty) := hpcSph.joined s₀ (Φ OnePoint.infty)
  have hbij₁ : Function.Bijective (Work.Serre.piMapN f (2 * j + 1) (Φ OnePoint.infty)) :=
    Work.Serre.bijective_piMapN_of_joined f hjoin (2 * j + 1) hbij
  have hbijΦ : Function.Bijective (Work.Serre.piMapN (⟨Φ, Φ.continuous_toFun⟩ :
      C(Work.StemsB.SphModel (2 * j + 1), Work.Serre.Sph (2 * j + 1)))
      (2 * j + 1) OnePoint.infty) :=
    Work.Serre.rwPiMapN_bijective_of_homotopyEquiv Φ.toHomotopyEquiv (2 * j + 1) OnePoint.infty
  have hbijg : Function.Bijective (Work.Serre.piMapN g (2 * j + 1) OnePoint.infty) := by
    have h1 : Work.Serre.piMapN g (2 * j + 1) OnePoint.infty =
        fun a => Work.Serre.piMapN f (2 * j + 1) (Φ OnePoint.infty)
          (Work.Serre.piMapN (⟨Φ, Φ.continuous_toFun⟩ : C(Work.StemsB.SphModel (2 * j + 1),
            Work.Serre.Sph (2 * j + 1))) (2 * j + 1) OnePoint.infty a) := by
      funext a
      exact Work.Serre.piMapN_comp (⟨Φ, Φ.continuous_toFun⟩ :
        C(Work.StemsB.SphModel (2 * j + 1), Work.Serre.Sph (2 * j + 1))) f
        (2 * j + 1) OnePoint.infty a
    rw [h1]
    exact hbij₁.comp hbijΦ
  obtain ⟨γ⟩ := hpcX.joined pt (g OnePoint.infty)
  have hXg : Work.Serre.IsEMSpaceUpTo ℤ (2 * j + 1) (by omega) M X (g OnePoint.infty) :=
    Work.Stems.isEMSpaceUpTo_change_basepoint (by omega) γ hX
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
    Work.Stems.homotopyFibre_conn_of_range hn3 g OnePoint.infty hsource hbijg
      (fun i _hi hin => hXg.2 i hin (by
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
  obtain ⟨hLgen, hLvan⟩ := Work.Stems.loopKnowledgeLocal 1 hj hEven (g OnePoint.infty) hXg
  obtain ⟨hw⟩ := Work.Stems.fibreOfHomeomorphLoopSpace g OnePoint.infty
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
  have hgen1 : Nonempty (Work.Cohomology.singularCohomology ℚ ((2 * j + 1) - 1)
      (Work.StemsB.wangCohFsp (2 * j + 1) p) ≅ ModuleCat.of ℚ ℚ) := by
    obtain ⟨ex⟩ := hgen 1 (le_refl 1) (by omega)
    exact ⟨(eqToIso (congrArg (fun m => Work.Cohomology.singularCohomology ℚ m
      (Work.StemsB.wangCohFsp (2 * j + 1) p)) (Nat.mul_one ((2 * j + 1) - 1)))).symm ≪≫ ex⟩
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
  have hWang : ∀ t : ℕ, (2 * j + 1) + 1 ≤ t → t ≤ M - 1 →
      Subsingleton ↥(Work.Cohomology.singularCohomology ℚ t (TopCat.of E)) :=
    Work.Stems.wangUptoBounded (2 * j + 1) (by omega) hodd E p hp hT_O d_G hT_G x hpcF
      Work.Stems.Collar.wangPowFormula_of_wangTheta_pow hlow (M - 1) hfib hgen
  have hEacyc : Work.Serre.RatAcyclicBelow E (M - 1) := by
    refine ⟨fun t ht0 htM => ?_, ?_⟩
    · by_cases htn : t ≤ 2 * j + 1
      · exact Work.Serre.serreE0Range E e₀ (2 * j + 1) (fun i hi => hconnE i hi) t ht0
          (by omega)
      · exact Work.Stems.isZero_ratH_of_isZero_ratCoh
          (ModuleCat.isZero_iff_subsingleton.mpr (hWang t (by omega) htM))
    · exact Work.Serre.isIso_ratHomologyMap_toPoint_zero_of_subsingleton_pi0 E e₀
        (hconnE 0 (by omega))
  -- transfer back from `SphModel` to `Sph`
  have hΦ : Work.Serre.RatAcyclicBelow
      (Work.RatHurewicz.homotopyFibre f (Φ OnePoint.infty)) (M - 1) :=
    homotopyFibre_precomp_ratAcyclicBelow Φ f OnePoint.infty (M - 1) hEacyc
  have hη : Path (Φ OnePoint.infty) s₀ :=
    (hpcSph.joined s₀ (Φ OnePoint.infty)).somePath.symm
  exact homotopyFibre_ratAcyclicBelow_of_path f hη hΦ

/-! ## The full statement -/

theorem oddCoverAcyclicFull (hE3b : Work.Serre.SerreE3b) (hE3a : Work.Serre.SerreE3a) :
    ∀ (j : ℕ) (hj : 1 ≤ j) (M : ℕ) (X : Type) [TopologicalSpace X] (pt : X),
      Work.Serre.IsEMSpaceUpTo ℤ (2 * j + 1) (by omega) M X pt →
      ∀ (s₀ : Work.Serre.Sph (2 * j + 1)) (f : C(Work.Serre.Sph (2 * j + 1), X)),
        Function.Bijective (Work.Serre.piMapN f (2 * j + 1) s₀) →
        Work.Serre.RatAcyclicBelow (Work.RatHurewicz.homotopyFibre f s₀) (M - 1) := by
  intro j hj M X tX pt hX s₀ f hbij
  by_cases hsmall : M - 1 ≤ 2 * j + 1
  · exact oddCoverAcyclicSmall hj hsmall pt hX s₀ f hbij
  · exact oddCoverAcyclicBig hE3b hE3a hj (by omega) pt hX s₀ f hbij

end

end Work.Rat
