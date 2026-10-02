import Mathlib
import Submission.Work.RatHurewicz.S3Inputs
import Submission.Work.StemsB.SerreExact
import Submission.Work.RatHurewicz.trackSetup
import Submission.Work.RatHurewicz.trackFibreHomeo
import Submission.Work.Cohomology.HomologyPairSequence
import Submission.Work.Cohomology.Pullback
import Submission.Work.Stems.Cone
import Submission.Work.Stems.mulEquiv_of_homotopyEquiv
import Submission.Work.RatHurewicz.isHurewiczFibration_trackMap
import Submission.Work.RatHurewicz.nat_smul_eq_zero_relChains_rangeModel
import Submission.Work.RatHurewicz.injective_homologyMap_trackProj
import Submission.Work.RatHurewicz.exists_hPairDelta_eq_of_homologyMap_eq_zero

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option maxHeartbeats 1000000

open scoped Topology unitInterval
open CategoryTheory

namespace Work.RatHurewicz

noncomputable section

variable {X Z : Type} [TopologicalSpace X] [TopologicalSpace Z]

/-! ## The mapping track of `inc` and the fibre of its track fibration -/

theorem hom_apply_congr {M N : ModuleCat ℤ} {f g : M ⟶ N} (h : f = g) (x : M) :
    f.hom x = g.hom x :=
  congrArg (fun (k : M ⟶ N) => k.hom x) h

/-- The map induced on `m`-th singular homology by a continuous map `f : A → B`. -/
abbrev homH (A B : TopCat) (f : A ⟶ B) (m : ℕ) :
    (Work.Cohomology.singularChains ℤ A).homology m ⟶
      (Work.Cohomology.singularChains ℤ B).homology m :=
  HomologicalComplex.homologyMap (Work.Cohomology.chainMap ℤ A B f) m

/-- The homeomorphism from the homotopy fibre of `inc` to the fibre of the mapping track of `inc`
(extracted from `Work.RatHurewicz.trackFibreHomeo`). -/
noncomputable def trackHomeo (inc : C(X, Z)) (x₀ : X) :
    homotopyFibre inc x₀ ≃ₜ ↥(trackFibre inc (inc x₀)) :=
  Classical.choose (trackFibreHomeo inc x₀)

theorem trackHomeo_base (inc : C(X, Z)) (x₀ : X) :
    trackHomeo inc x₀ (homotopyFibreBasepoint inc x₀)
      = ⟨trackBase inc x₀, trackBase_mem_trackFibre inc x₀⟩ :=
  (Classical.choose_spec (trackFibreHomeo inc x₀)).1

theorem trackHomeo_fst (inc : C(X, Z)) (x₀ : X) (y : homotopyFibre inc x₀) :
    (trackHomeo inc x₀ y).1.1.1 = homotopyFibreFst inc x₀ y :=
  (Classical.choose_spec (trackFibreHomeo inc x₀)).2 y

/-- The homeomorphism `F ≅ (track fibre)` as a continuous map. -/
def trackHomeoCM (inc : C(X, Z)) (x₀ : X) :
    C(homotopyFibre inc x₀, ↥(trackFibre inc (inc x₀))) :=
  (trackHomeo inc x₀ : C(homotopyFibre inc x₀, ↥(trackFibre inc (inc x₀))))

/-- The inverse homeomorphism as a continuous map. -/
def trackHomeoSymmCM (inc : C(X, Z)) (x₀ : X) :
    C(↥(trackFibre inc (inc x₀)), homotopyFibre inc x₀) :=
  ((trackHomeo inc x₀).symm : C(↥(trackFibre inc (inc x₀)), homotopyFibre inc x₀))

@[simp]
theorem trackHomeoCM_apply (inc : C(X, Z)) (x₀ : X) (y : homotopyFibre inc x₀) :
    trackHomeoCM inc x₀ y = trackHomeo inc x₀ y := rfl

@[simp]
theorem trackHomeoSymmCM_apply (inc : C(X, Z)) (x₀ : X) (y : ↥(trackFibre inc (inc x₀))) :
    trackHomeoSymmCM inc x₀ y = (trackHomeo inc x₀).symm y := rfl

/-- The inclusion of the track fibre into the mapping track. -/
def trackIncl (inc : C(X, Z)) (x₀ : X) :
    C(↥(trackFibre inc (inc x₀)), Track inc) :=
  ⟨Subtype.val, continuous_subtype_val⟩

/-- The composite `F ≅ (track fibre) ↪ Track` of the homeomorphism with the inclusion. -/
def trackPsi (inc : C(X, Z)) (x₀ : X) : C(homotopyFibre inc x₀, Track inc) :=
  (trackIncl inc x₀).comp (trackHomeoCM inc x₀)

theorem trackIncl_apply (inc : C(X, Z)) (x₀ : X) (p : ↥(trackFibre inc (inc x₀))) :
    trackIncl inc x₀ p = p.1 := rfl

/-- **The projection of the mapping track composed with the composite `F → Track` is the projection
of the homotopy fibre.** -/
theorem trackProj_comp_trackPsi (inc : C(X, Z)) (x₀ : X) :
    (trackProj inc).comp (trackPsi inc x₀) = homotopyFibreFst inc x₀ := by
  ext y
  show trackProj inc (trackPsi inc x₀ y) = homotopyFibreFst inc x₀ y
  rw [show trackPsi inc x₀ y = (trackHomeo inc x₀ y).1 from rfl]
  rw [show trackProj inc ((trackHomeo inc x₀ y).1) = (trackHomeo inc x₀ y).1.1.1 from rfl]
  exact trackHomeo_fst inc x₀ y

/-! ## The chain-level identities -/

/-- `inclChains` of the track fibre is the chain map induced by the inclusion `trackIncl`. -/
theorem inclChains_trackFibre (inc : C(X, Z)) (x₀ : X) :
    Work.Cohomology.inclChains (TopCat.of (Track inc)) (trackFibre inc (inc x₀))
      = Work.Cohomology.chainMap ℤ (TopCat.of ↥(trackFibre inc (inc x₀))) (TopCat.of (Track inc))
          (TopCat.ofHom (trackIncl inc x₀)) := rfl

/-- **The chain map induced by the projection of the homotopy fibre factors through the mapping
track.** -/
theorem chainMap_fst_eq (inc : C(X, Z)) (x₀ : X) :
    Work.Cohomology.chainMap ℤ (TopCat.of (homotopyFibre inc x₀)) (TopCat.of X)
        (TopCat.ofHom (homotopyFibreFst inc x₀))
      = Work.Cohomology.chainMap ℤ (TopCat.of (homotopyFibre inc x₀)) (TopCat.of (Track inc))
          (TopCat.ofHom (trackPsi inc x₀))
        ≫ Work.Cohomology.chainMap ℤ (TopCat.of (Track inc)) (TopCat.of X)
          (TopCat.ofHom (trackProj inc)) := by
  rw [← Work.Cohomology.chainMap_comp']
  congr 1
  rw [← TopCat.ofHom_comp (trackPsi inc x₀) (trackProj inc), trackProj_comp_trackPsi]

/-- **The chain map induced by the composite `F → Track` factors through the homeomorphism onto the
track fibre.** -/
theorem chainMap_psi_eq (inc : C(X, Z)) (x₀ : X) :
    Work.Cohomology.chainMap ℤ (TopCat.of (homotopyFibre inc x₀)) (TopCat.of (Track inc))
        (TopCat.ofHom (trackPsi inc x₀))
      = Work.Cohomology.chainMap ℤ (TopCat.of (homotopyFibre inc x₀))
          (TopCat.of ↥(trackFibre inc (inc x₀)))
          (TopCat.ofHom (trackHomeoCM inc x₀))
        ≫ Work.Cohomology.chainMap ℤ (TopCat.of ↥(trackFibre inc (inc x₀))) (TopCat.of (Track inc))
          (TopCat.ofHom (trackIncl inc x₀)) := by
  rw [← Work.Cohomology.chainMap_comp', ← TopCat.ofHom_comp]
  rfl

/-! ## Injectivity of the homeomorphism on homology -/

/-- The chain maps of the homeomorphism and of its inverse compose to the identity. -/
theorem trackHomeo_chainMap_comp (inc : C(X, Z)) (x₀ : X) :
    Work.Cohomology.chainMap ℤ (TopCat.of (homotopyFibre inc x₀))
        (TopCat.of ↥(trackFibre inc (inc x₀))) (TopCat.ofHom (trackHomeoCM inc x₀))
      ≫ Work.Cohomology.chainMap ℤ (TopCat.of ↥(trackFibre inc (inc x₀)))
          (TopCat.of (homotopyFibre inc x₀)) (TopCat.ofHom (trackHomeoSymmCM inc x₀))
      = 𝟙 (Work.Cohomology.singularChains ℤ (TopCat.of (homotopyFibre inc x₀))) := by
  rw [← Work.Cohomology.chainMap_comp', ← Work.Cohomology.chainMap_id']
  congr 1
  rw [← TopCat.ofHom_comp, ← TopCat.ofHom_id]
  congr 1
  ext y
  simp

/-- **The homeomorphism onto the track fibre induces an injective map on homology.** -/
theorem injective_homologyMap_trackHomeo (inc : C(X, Z)) (x₀ : X) (m : ℕ) :
    Function.Injective (HomologicalComplex.homologyMap
      (Work.Cohomology.chainMap ℤ (TopCat.of (homotopyFibre inc x₀))
        (TopCat.of ↥(trackFibre inc (inc x₀)))
        (TopCat.ofHom (trackHomeoCM inc x₀))) m) := by
  set φ : _ ⟶ _ := HomologicalComplex.homologyMap
    (Work.Cohomology.chainMap ℤ (TopCat.of (homotopyFibre inc x₀))
      (TopCat.of ↥(trackFibre inc (inc x₀)))
      (TopCat.ofHom (trackHomeoCM inc x₀))) m with hφ
  set ψ : _ ⟶ _ := HomologicalComplex.homologyMap
    (Work.Cohomology.chainMap ℤ (TopCat.of ↥(trackFibre inc (inc x₀)))
      (TopCat.of (homotopyFibre inc x₀))
      (TopCat.ofHom (trackHomeoSymmCM inc x₀))) m with hψ
  have hcomp : φ ≫ ψ = 𝟙 _ := by
    rw [hφ, hψ, ← HomologicalComplex.homologyMap_comp, trackHomeo_chainMap_comp,
      HomologicalComplex.homologyMap_id]
  have hfix : ∀ a, ψ.hom (φ.hom a) = a := by
    intro a
    simpa using hom_apply_congr hcomp a
  intro a b hab
  rw [← hfix a, ← hfix b, hab]

/-! ## Connectivity of the track fibre -/

/-- **The track fibre is as connected as the homotopy fibre** (they are homeomorphic). -/
theorem subsingleton_homotopyGroup_trackFibre (inc : C(X, Z)) (x₀ : X) {f : ℕ}
    (hf : ∀ j < f, Subsingleton (HomotopyGroup (Fin j) (homotopyFibre inc x₀)
      (homotopyFibreBasepoint inc x₀))) :
    ∀ j < f, Subsingleton (HomotopyGroup (Fin j) ↥(trackFibre inc (inc x₀))
      ⟨trackBase inc x₀, trackBase_mem_trackFibre inc x₀⟩) := by
  intro j hj
  have hsym : (trackHomeo inc x₀).symm ⟨trackBase inc x₀, trackBase_mem_trackFibre inc x₀⟩
      = homotopyFibreBasepoint inc x₀ := by
    rw [← trackHomeo_base (inc := inc) (x₀ := x₀)]
    exact (trackHomeo inc x₀).symm_apply_apply _
  have h1 : Subsingleton (HomotopyGroup (Fin j) (homotopyFibre inc x₀)
      ((trackHomeo inc x₀).symm ⟨trackBase inc x₀, trackBase_mem_trackFibre inc x₀⟩)) := by
    rw [hsym]
    exact hf j hj
  exact Work.Stems.subsingleton_of_retract (N := Fin j)
    (trackHomeoSymmCM inc x₀) (trackHomeoCM inc x₀) (by ext y; simp) h1

/-! ## Auxiliary algebra -/

/-- An injective additive homomorphism cannot kill `n • a` unless it kills `n • (φ a)`. -/
theorem nsmul_eq_zero_of_injective_addHom {A B : Type*} [AddCommGroup A] [AddCommGroup B]
    (φ : A →+ B) (hinj : Function.Injective φ) {M : ℕ} {a : A} (h : M • φ a = 0) :
    M • a = 0 := by
  apply hinj
  rw [map_nsmul, h, map_zero]

/-- The underlying linear map of an isomorphism of `ℤ`-modules is injective. -/
theorem injective_of_isIso_moduleCat {M N : ModuleCat ℤ} (f : M ⟶ N) [CategoryTheory.IsIso f] :
    Function.Injective f.hom := by
  have hfix : ∀ x : M, (CategoryTheory.inv f).hom (f.hom x) = x := by
    intro x
    have h := CategoryTheory.IsIso.hom_inv_id f
    have h2 := congrArg (fun (g : M ⟶ M) => g.hom x) h
    simpa using h2
  intro a b hab
  rw [← hfix a, ← hfix b, hab]



/-- The homology map of the projection of the homotopy fibre, abbreviated. -/
abbrev fstH (inc : C(X, Z)) (x₀ : X) (m : ℕ) :=
  homH (TopCat.of (homotopyFibre inc x₀)) (TopCat.of X)
    (TopCat.ofHom (homotopyFibreFst inc x₀)) m

/-- The homology map of the composite `F → Track`, abbreviated. -/
abbrev psiH (inc : C(X, Z)) (x₀ : X) (m : ℕ) :=
  homH (TopCat.of (homotopyFibre inc x₀)) (TopCat.of (Track inc))
    (TopCat.ofHom (trackPsi inc x₀)) m

/-- The homology map of the projection of the mapping track, abbreviated. -/
abbrev projH (inc : C(X, Z)) (x₀ : X) (m : ℕ) :=
  homH (TopCat.of (Track inc)) (TopCat.of X) (TopCat.ofHom (trackProj inc)) m

/-- The homology map of the homeomorphism onto the track fibre, abbreviated. -/
abbrev homeoH (inc : C(X, Z)) (x₀ : X) (m : ℕ) :=
  homH (TopCat.of (homotopyFibre inc x₀)) (TopCat.of ↥(trackFibre inc (inc x₀)))
    (TopCat.ofHom (trackHomeoCM inc x₀)) m

/-- The homology map of the inclusion of the track fibre, abbreviated. -/
abbrev inclH (inc : C(X, Z)) (x₀ : X) (m : ℕ) :=
  homH (TopCat.of ↥(trackFibre inc (inc x₀))) (TopCat.of (Track inc))
    (TopCat.ofHom (trackIncl inc x₀)) m

/-! ## Serre's exact sequence in the stable range for the track fibration -/

/-- The set-theoretic identity behind the fibre of the track fibration. -/
theorem trackFibre_eq_preimage (inc : C(X, Z)) (x₀ : X) :
    trackFibre inc (inc x₀) = trackMap inc ⁻¹' {inc x₀} := rfl

/-- **Serre's exact sequence in the stable range for the track fibration**: the map of pairs
`(Track inc, trackFibre inc (inc x₀)) → (Z, {inc x₀})` induces an isomorphism on homology in the
stable range, so that `H_{n+2}` of the pair is the relative homology of the range model `Z`. -/
theorem isIso_relPairMap_trackMap (h : Work.StemsB.SerreExactRange) (inc : C(X, Z)) (x₀ : X)
    (k n : ℕ) (hk : 2 ≤ k) (hmodel : IsRangeKModel k (2 * k - 1) (inc x₀))
    (hconn : ∀ j ≤ k, Subsingleton (HomotopyGroup (Fin j) (homotopyFibre inc x₀)
      (homotopyFibreBasepoint inc x₀)))
    (hrange : n + 1 ≤ 2 * k - 2) :
    IsIso (HomologicalComplex.homologyMap (Work.StemsB.relPairMap (trackMap inc) (inc x₀))
      (n + 2)) := by
  refine h (Track inc) Z (trackMap inc) (isHurewiczFibration_trackMap inc) (trackBase inc x₀)
    (inc x₀) (trackMap_trackBase inc x₀) k (k + 1) ?_ ?_ (n + 2) ?_
  · intro i hi
    exact hmodel i (by omega) (by omega)
  · intro i hi
    have hbase :
        (⟨trackBase inc x₀, trackMap_trackBase inc x₀⟩ :
          ↥{x : Track inc | trackMap inc x = inc x₀})
        = ⟨trackBase inc x₀, trackBase_mem_trackFibre inc x₀⟩ := rfl
    rw [hbase]
    exact subsingleton_homotopyGroup_trackFibre inc x₀ (f := k + 1)
      (fun j hj => hconn j (by omega)) i hi
  · omega

/-- **The relative homology of the track pair in the stable range is torsion**, because Serre's
exact sequence identifies it with the relative homology of the range model `Z`, whose rational
homology vanishes below `2k`. -/
theorem nat_smul_eq_zero_trackPair (h : Work.StemsB.SerreExactRange)
    (hem : Work.RatHurewicz.RangeModelRatAcyclic) (inc : C(X, Z)) (x₀ : X) (k n : ℕ) (hk : 2 ≤ k)
    (hmodel : IsRangeKModel k (2 * k - 1) (inc x₀))
    (hconn : ∀ j ≤ k, Subsingleton (HomotopyGroup (Fin j) (homotopyFibre inc x₀)
      (homotopyFibreBasepoint inc x₀)))
    (hkn : k < n + 1) (hrange : n + 1 ≤ 2 * k - 2) :
    ∀ b : ↥((Work.Cohomology.relChains (TopCat.of (Track inc))
      (trackFibre inc (inc x₀))).homology (n + 2)), ∃ N : ℕ, 0 < N ∧ N • b = 0 := by
  haveI hiso : IsIso (HomologicalComplex.homologyMap (Work.StemsB.relPairMap (trackMap inc)
      (inc x₀)) (n + 2)) := isIso_relPairMap_trackMap h inc x₀ k n hk hmodel hconn hrange
  have hinj : Function.Injective (HomologicalComplex.homologyMap
      (Work.StemsB.relPairMap (trackMap inc) (inc x₀)) (n + 2)).hom :=
    injective_of_isIso_moduleCat _
  have hQ : Subsingleton ↥((Work.Cohomology.singularChains ℚ (TopCat.of Z)).homology (n + 2)) :=
    ModuleCat.isZero_iff_subsingleton.mp (hem k hk Z (inc x₀) hmodel (n + 2) (by omega) (by omega))
  intro b
  obtain ⟨N, hN, hNb⟩ := nat_smul_eq_zero_relChains_rangeModel (z₀ := inc x₀) (j := n + 2)
    (by omega) hQ ((HomologicalComplex.homologyMap (Work.StemsB.relPairMap (trackMap inc)
      (inc x₀)) (n + 2)).hom b)
  refine ⟨N, hN, ?_⟩
  refine hinj ?_
  rw [map_nsmul, hNb, map_zero]

/-! ## The composite identities at the level of homology -/

/-- The homology map of the projection of the homotopy fibre factors through the mapping track. -/
theorem homologyMap_fst_eq (inc : C(X, Z)) (x₀ : X) (m : ℕ) :
    HomologicalComplex.homologyMap (Work.Cohomology.chainMap ℤ (TopCat.of (homotopyFibre inc x₀))
        (TopCat.of X) (TopCat.ofHom (homotopyFibreFst inc x₀))) m
      = HomologicalComplex.homologyMap (Work.Cohomology.chainMap ℤ
          (TopCat.of (homotopyFibre inc x₀)) (TopCat.of (Track inc))
          (TopCat.ofHom (trackPsi inc x₀))) m
        ≫ HomologicalComplex.homologyMap (Work.Cohomology.chainMap ℤ (TopCat.of (Track inc))
          (TopCat.of X) (TopCat.ofHom (trackProj inc))) m := by
  rw [← HomologicalComplex.homologyMap_comp, ← chainMap_fst_eq]

/-- The homology map of the composite `F → Track` factors through the track fibre. -/
theorem homologyMap_psi_eq (inc : C(X, Z)) (x₀ : X) (m : ℕ) :
    HomologicalComplex.homologyMap (Work.Cohomology.chainMap ℤ
        (TopCat.of (homotopyFibre inc x₀)) (TopCat.of (Track inc))
        (TopCat.ofHom (trackPsi inc x₀))) m
      = HomologicalComplex.homologyMap (Work.Cohomology.chainMap ℤ
          (TopCat.of (homotopyFibre inc x₀)) (TopCat.of ↥(trackFibre inc (inc x₀)))
          (TopCat.ofHom (trackHomeoCM inc x₀))) m
        ≫ HomologicalComplex.homologyMap (Work.Cohomology.chainMap ℤ
          (TopCat.of ↥(trackFibre inc (inc x₀))) (TopCat.of (Track inc))
          (TopCat.ofHom (trackIncl inc x₀))) m := by
  rw [← HomologicalComplex.homologyMap_comp, ← chainMap_psi_eq]

/-- The homology transfer of the truncation step follows from Serre's exact sequence in the stable range together with the rational acyclicity of the range models of `K(π_k X,k)` below `2k`. Indeed, the long exact sequence of the pair `(X, F)` identifies `ker(H_{n+1}(F) → H_{n+1}(X))` with the image of `H_{n+2}(X,F)`, which is `H̃_{n+2}(Z)` in the stable range by Serre's result and rationally zero by the range-model hypothesis. -/
theorem truncationHomologyTransfer_of_serre (h : Work.StemsB.SerreExactRange)
    (hem : Work.RatHurewicz.RangeModelRatAcyclic) :
    Work.RatHurewicz.TruncationHomologyTransfer := by
  intro k hk X Z hX hZ inc x₀ hconn hmodel n hkn hrange y hy
  obtain ⟨M, hM, hMy⟩ := hy
  -- the composite identities at the level of homology
  have hcomp1 : fstH inc x₀ (n + 1) = psiH inc x₀ (n + 1) ≫ projH inc x₀ (n + 1) :=
    homologyMap_fst_eq inc x₀ (n + 1)
  have hcomp2 : psiH inc x₀ (n + 1) = homeoH inc x₀ (n + 1) ≫ inclH inc x₀ (n + 1) :=
    homologyMap_psi_eq inc x₀ (n + 1)
  -- injectivities
  have hr_inj : Function.Injective (projH inc x₀ (n + 1)).hom := by
    simpa using injective_homologyMap_trackProj inc (n + 1)
  have he_inj : Function.Injective (homeoH inc x₀ (n + 1)).hom := by
    simpa using injective_homologyMap_trackHomeo inc x₀ (n + 1)
  -- the hypothesis, in the `.hom` form
  have hMy' : M • (fstH inc x₀ (n + 1)).hom y = 0 := hMy
  -- Step 1: `M • ψ_* y = 0`
  have hmiddle : (projH inc x₀ (n + 1)).hom ((psiH inc x₀ (n + 1)).hom y)
      = (fstH inc x₀ (n + 1)).hom y := by
    have hh := hom_apply_congr hcomp1 y
    simpa [ModuleCat.hom_comp, LinearMap.comp_apply] using hh.symm
  have hstep1 : M • (projH inc x₀ (n + 1)).hom ((psiH inc x₀ (n + 1)).hom y) = 0 := by
    rw [hmiddle]
    exact hMy'
  have hpsi : M • (psiH inc x₀ (n + 1)).hom y = 0 :=
    nsmul_eq_zero_of_injective_addHom (projH inc x₀ (n + 1)).hom.toAddMonoidHom hr_inj hstep1
  -- Step 2: `ı_* (M • e_* y) = 0`
  have hfactor : (psiH inc x₀ (n + 1)).hom y
      = (inclH inc x₀ (n + 1)).hom ((homeoH inc x₀ (n + 1)).hom y) := by
    have hh := hom_apply_congr hcomp2 y
    simpa [ModuleCat.hom_comp, LinearMap.comp_apply] using hh
  have hker : (inclH inc x₀ (n + 1)).hom (M • (homeoH inc x₀ (n + 1)).hom y) = 0 := by
    rw [map_nsmul, ← hfactor, hpsi]
  -- the same statement in the exact form of `inclChains`
  have hker' : HomologicalComplex.homologyMap
      (Work.Cohomology.inclChains (TopCat.of (Track inc)) (trackFibre inc (inc x₀))) (n + 1)
      (M • (homeoH inc x₀ (n + 1)).hom y) = 0 := by
    rw [inclChains_trackFibre]
    exact hker
  -- Step 3: the connecting homomorphism hits `M • e_* y`
  obtain ⟨a, ha⟩ := exists_hPairDelta_eq_of_homologyMap_eq_zero (TopCat.of (Track inc))
    (trackFibre inc (inc x₀)) (n + 1) (M • (homeoH inc x₀ (n + 1)).hom y) hker'
  -- Step 4: `a` is torsion (the relative homology of the track pair is torsion)
  obtain ⟨N, hN, hNa⟩ :=
    nat_smul_eq_zero_trackPair h hem inc x₀ k n hk hmodel hconn hkn hrange a
  have hNM : N • (M • (homeoH inc x₀ (n + 1)).hom y) = 0 := by
    rw [← ha]
    rw [show N • ((Work.Cohomology.hPairδ (TopCat.of (Track inc))
          (trackFibre inc (inc x₀)) (n + 1)) a)
        = ((Work.Cohomology.hPairδ (TopCat.of (Track inc))
          (trackFibre inc (inc x₀)) (n + 1)).hom) (N • a)
        from (map_nsmul _ N a).symm]
    rw [hNa, map_zero]
  -- Step 5: `N * M` kills `y`
  refine ⟨N * M, Nat.mul_pos hN hM, ?_⟩
  rw [mul_comm N M]
  apply he_inj
  rw [map_nsmul, mul_nsmul, hNM, map_zero]

end

end Work.RatHurewicz
