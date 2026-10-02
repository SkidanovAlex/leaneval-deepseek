import Mathlib
import Submission.Work.ThomBordism.Grassmann.IncidenceBandTriv

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 8000000
set_option linter.unusedVariables false

/-!
# The restrictions of the incidence band are isomorphisms

The trivialisation `bandTrivHomeo` of the equatorial band, together with the cohomological
isomorphism `H^i(fibreVec) ≅ H^i(fibreVec × bandSph)` of the product with a band of a sphere and the
homotopy equivalence `upSet ≃ fibreVec`, shows that the restriction

`H^i(upSet k m) → H^i(bandSet k m)`

is a bijection for `i + 2 ≤ k+m-1`.  The same holds for the lower half `downSet`, by the negation
symmetry `(P,w) ↦ (-P,-w)` of the incidence space (`restV_band_bijective`).
-/

open CategoryTheory AlgebraicTopology Simplicial Limits
open scoped Simplicial Topology

namespace Work.ThomBordism.Grassmann

noncomputable section

open Work.Cohomology

variable {k m : ℕ}

/-! ## The projection of `fibreVec × bandSph` -/

/-- The projection of `fibreVec × bandSph` onto `fibreVec`. -/
noncomputable def bandFstC (k m : ℕ) : C(↥(fibreVec k m) × ↥(bandSph k m), ↥(fibreVec k m)) :=
  ⟨fun p => p.1, continuous_fst⟩

/-- **The projection `fibreVec × bandSph → fibreVec` is a cohomology isomorphism** in degrees
`j + 2 ≤ k + m - 1`. -/
theorem bandSphProjection_bijective (k m j : ℕ) (hk : 1 ≤ k) (hj : j + 2 ≤ k + m - 1) :
    Function.Bijective ((singularCohomologyMap ℤ
      (TopCat.of (↥(fibreVec k m) × ↥(bandSph k m))) (TopCat.of ↥(fibreVec k m))
      (TopCat.ofHom (bandFstC k m)) j).hom) := by
  obtain ⟨e⟩ := bandSph_homeo k m hk
  let E : (↥(fibreVec k m) × ↥(bandStd (k+m-1))) ≃ₜ (↥(fibreVec k m) × ↥(bandSph k m)) :=
    Homeomorph.prodCongr (Homeomorph.refl ↥(fibreVec k m)) e
  let EC : C(↥(fibreVec k m) × ↥(bandStd (k+m-1)),
      ↥(fibreVec k m) × ↥(bandSph k m)) := E
  let pfC : C(↥(fibreVec k m) × ↥(bandStd (k+m-1)), ↥(fibreVec k m)) :=
    ⟨fun p => p.1, continuous_fst⟩
  let paC : C(↥(fibreVec k m) × ↥(bandSph k m), ↥(fibreVec k m)) := bandFstC k m
  have hfun : pfC = paC.comp EC := by
    apply ContinuousMap.ext
    intro p
    rfl
  haveI : IsIso (singularCohomologyMap ℤ
      (TopCat.of (↥(fibreVec k m) × ↥(bandStd (k+m-1))))
      (TopCat.of (↥(fibreVec k m) × ↥(bandSph k m))) (TopCat.ofHom EC) j) :=
    isIso_singularCohomologyMap_of_homeomorph E j
  have hE : Function.Bijective ((singularCohomologyMap ℤ
      (TopCat.of (↥(fibreVec k m) × ↥(bandStd (k+m-1))))
      (TopCat.of (↥(fibreVec k m) × ↥(bandSph k m))) (TopCat.ofHom EC) j).hom) :=
    bijective_of_isIso_moduleCat _
  have hpf : Function.Bijective ((singularCohomologyMap ℤ
      (TopCat.of (↥(fibreVec k m) × ↥(bandStd (k+m-1)))) (TopCat.of ↥(fibreVec k m))
      (TopCat.ofHom pfC) j).hom) := by
    show Function.Bijective ((singularCohomologyMap ℤ
      (TopCat.of (↥(fibreVec k m) × ↥(bandStd (k+m-1)))) (TopCat.of ↥(fibreVec k m))
      (TopCat.ofHom ⟨fun p => p.1, continuous_fst⟩) j).hom)
    exact bandProjection_bijective k m j hk hj
  have hcomp : (singularCohomologyMap ℤ
        (TopCat.of (↥(fibreVec k m) × ↥(bandStd (k+m-1)))) (TopCat.of ↥(fibreVec k m))
        (TopCat.ofHom pfC) j)
      = (singularCohomologyMap ℤ
          (TopCat.of (↥(fibreVec k m) × ↥(bandSph k m))) (TopCat.of ↥(fibreVec k m))
          (TopCat.ofHom paC) j)
        ≫ (singularCohomologyMap ℤ
          (TopCat.of (↥(fibreVec k m) × ↥(bandStd (k+m-1))))
          (TopCat.of (↥(fibreVec k m) × ↥(bandSph k m))) (TopCat.ofHom EC) j) := by
    rw [show TopCat.ofHom pfC = TopCat.ofHom EC ≫ TopCat.ofHom paC from by
      change TopCat.ofHom pfC = TopCat.ofHom (paC.comp EC)
      rw [hfun]]
    exact singularCohomologyMap_comp (R := ℤ) (TopCat.ofHom EC) (TopCat.ofHom paC) j
  have hmain : Function.Bijective
      (((singularCohomologyMap ℤ
          (TopCat.of (↥(fibreVec k m) × ↥(bandStd (k+m-1))))
          (TopCat.of (↥(fibreVec k m) × ↥(bandSph k m))) (TopCat.ofHom EC) j).hom).comp
        ((singularCohomologyMap ℤ
          (TopCat.of (↥(fibreVec k m) × ↥(bandSph k m))) (TopCat.of ↥(fibreVec k m))
          (TopCat.ofHom paC) j).hom)) := by
    rw [← ModuleCat.hom_comp, ← hcomp]
    exact hpf
  show Function.Bijective ((singularCohomologyMap ℤ
    (TopCat.of (↥(fibreVec k m) × ↥(bandSph k m))) (TopCat.of ↥(fibreVec k m))
    (TopCat.ofHom (bandFstC k m)) j).hom)
  exact ⟨fun x y hxy => hmain.1 (by rw [LinearMap.comp_apply, LinearMap.comp_apply, hxy]),
    fun z => by
      obtain ⟨w, hw⟩ := hmain.2 (((singularCohomologyMap ℤ
        (TopCat.of (↥(fibreVec k m) × ↥(bandStd (k+m-1))))
        (TopCat.of (↥(fibreVec k m) × ↥(bandSph k m))) (TopCat.ofHom EC) j).hom) z)
      exact ⟨w, hE.1 (by rw [LinearMap.comp_apply] at hw; exact hw)⟩⟩

end

end Work.ThomBordism.Grassmann

namespace Work.ThomBordism.Grassmann

noncomputable section

open Work.Cohomology

/-- **The restriction `H^i(upSet) → H^i(bandSet)` is a bijection** in degrees `i + 2 ≤ k+m-1`. -/
theorem restU_band_bijective (k m i : ℕ) (hk : 1 ≤ k) (hi : i + 2 ≤ k + m - 1) :
    Function.Bijective (restU (X := TopCat.of ↥(zeroComp k m)) (upSet k m) (downSet k m) i) := by
  have hproj : Function.Bijective ((singularCohomologyMap ℤ
      (TopCat.of (↥(fibreVec k m) × ↥(bandSph k m))) (TopCat.of ↥(fibreVec k m))
      (TopCat.ofHom (bandFstC k m)) i).hom) := bandSphProjection_bijective k m i hk hi
  let fC : C(↥(bandSet k m), ↥(fibreVec k m) × ↥(bandSph k m)) :=
    (↑(bandTrivHomeo k m hk) : C(↥(bandSet k m), ↥(fibreVec k m) × ↥(bandSph k m)))
  let gC : C(↥(fibreVec k m) × ↥(bandSph k m), ↥(fibreVec k m)) := bandFstC k m
  let ψC : C(↥(bandSet k m), ↥(fibreVec k m)) := (sPlusFibre hk).comp (bandInclUp k m)
  have hfg : ψC = gC.comp fC := by
    apply ContinuousMap.ext
    intro x
    rfl
  haveI : IsIso (singularCohomologyMap ℤ (TopCat.of ↥(bandSet k m))
      (TopCat.of (↥(fibreVec k m) × ↥(bandSph k m))) (TopCat.ofHom fC) i) :=
    isIso_singularCohomologyMap_of_homeomorph (bandTrivHomeo k m hk) i
  have hF : Function.Bijective ((singularCohomologyMap ℤ (TopCat.of ↥(bandSet k m))
      (TopCat.of (↥(fibreVec k m) × ↥(bandSph k m))) (TopCat.ofHom fC) i).hom) :=
    bijective_of_isIso_moduleCat _
  have hψ : Function.Bijective ((singularCohomologyMap ℤ (TopCat.of ↥(bandSet k m))
      (TopCat.of ↥(fibreVec k m)) (TopCat.ofHom ψC) i).hom) := by
    have hnat : (singularCohomologyMap ℤ (TopCat.of ↥(bandSet k m))
          (TopCat.of ↥(fibreVec k m)) (TopCat.ofHom ψC) i)
        = (singularCohomologyMap ℤ
            (TopCat.of (↥(fibreVec k m) × ↥(bandSph k m))) (TopCat.of ↥(fibreVec k m))
            (TopCat.ofHom gC) i)
          ≫ (singularCohomologyMap ℤ (TopCat.of ↥(bandSet k m))
            (TopCat.of (↥(fibreVec k m) × ↥(bandSph k m))) (TopCat.ofHom fC) i) := by
      rw [show TopCat.ofHom ψC = TopCat.ofHom fC ≫ TopCat.ofHom gC from by
        change TopCat.ofHom ψC = TopCat.ofHom (gC.comp fC)
        rw [hfg]]
      exact singularCohomologyMap_comp (R := ℤ) (TopCat.ofHom fC) (TopCat.ofHom gC) i
    rw [hnat, ModuleCat.hom_comp]
    exact ⟨fun x y hxy => hproj.1 (hF.1 hxy), fun z => by
      obtain ⟨w, hw⟩ := hF.2 z
      obtain ⟨v, hv⟩ := hproj.2 w
      exact ⟨v, by rw [LinearMap.comp_apply, hv, hw]⟩⟩
  have hsp : Function.Bijective ((singularCohomologyMap ℤ (TopCat.of ↥(upSet k m))
      (TopCat.of ↥(fibreVec k m)) (TopCat.ofHom (sPlusFibre hk)) i).hom) := by
    have h1 : TopCat.Homotopy
        (TopCat.ofHom (inclFibre (k := k) (m := m) hk) ≫
          TopCat.ofHom (sPlusFibre (k := k) (m := m) hk))
        (𝟙 (TopCat.of ↥(fibreVec k m))) :=
      (ContinuousMap.Homotopy.refl
        ((sPlusFibre (k := k) (m := m) hk).comp (inclFibre (k := k) (m := m) hk))).cast rfl
        (sPlusFibre_comp_inclFibre (k := k) (m := m) hk)
    have h2 : TopCat.Homotopy
        (TopCat.ofHom (sPlusFibre (k := k) (m := m) hk) ≫
          TopCat.ofHom (inclFibre (k := k) (m := m) hk))
        (𝟙 (TopCat.of ↥(upSet k m))) :=
      (homotopyUp (k := k) (m := m) hk).cast (sPlusMap_eq_comp (k := k) (m := m) hk) rfl
    haveI : IsIso (singularCohomologyMap ℤ (TopCat.of ↥(upSet k m))
        (TopCat.of ↥(fibreVec k m)) (TopCat.ofHom (sPlusFibre hk)) i) :=
      homotopyEquiv ℤ _ _ (TopCat.ofHom (sPlusFibre hk)) (TopCat.ofHom (inclFibre hk)) h2 h1 i
    exact bijective_of_isIso_moduleCat _
  have hnat2 : (singularCohomologyMap ℤ (TopCat.of ↥(bandSet k m)) (TopCat.of ↥(fibreVec k m))
        (TopCat.ofHom ψC) i)
      = (singularCohomologyMap ℤ (TopCat.of ↥(upSet k m)) (TopCat.of ↥(fibreVec k m))
          (TopCat.ofHom (sPlusFibre hk)) i)
        ≫ (singularCohomologyMap ℤ (TopCat.of ↥(bandSet k m)) (TopCat.of ↥(upSet k m))
          (TopCat.ofHom (bandInclUp k m)) i) := by
    rw [show TopCat.ofHom ψC
        = TopCat.ofHom (bandInclUp k m) ≫ TopCat.ofHom (sPlusFibre hk) from rfl]
    exact singularCohomologyMap_comp (R := ℤ) (TopCat.ofHom (bandInclUp k m))
      (TopCat.ofHom (sPlusFibre hk)) i
  have hband : Function.Bijective ((singularCohomologyMap ℤ (TopCat.of ↥(bandSet k m))
      (TopCat.of ↥(upSet k m)) (TopCat.ofHom (bandInclUp k m)) i).hom) := by
    have hcomp2 : Function.Bijective
        (((singularCohomologyMap ℤ (TopCat.of ↥(bandSet k m)) (TopCat.of ↥(upSet k m))
            (TopCat.ofHom (bandInclUp k m)) i).hom).comp
          ((singularCohomologyMap ℤ (TopCat.of ↥(upSet k m)) (TopCat.of ↥(fibreVec k m))
            (TopCat.ofHom (sPlusFibre hk)) i).hom)) := by
      rw [← ModuleCat.hom_comp, ← hnat2]
      exact hψ
    refine ⟨fun x y hxy => ?_, fun z => ?_⟩
    · obtain ⟨x', hx'⟩ := hsp.2 x
      obtain ⟨y', hy'⟩ := hsp.2 y
      have h1 : x' = y' := hcomp2.1 (by
        rw [LinearMap.comp_apply, LinearMap.comp_apply, hx', hy']
        exact hxy)
      rw [← hx', ← hy', h1]
    · obtain ⟨w, hw⟩ := hcomp2.2 z
      exact ⟨((singularCohomologyMap ℤ (TopCat.of ↥(upSet k m)) (TopCat.of ↥(fibreVec k m))
        (TopCat.ofHom (sPlusFibre hk)) i).hom) w, by
        rw [LinearMap.comp_apply] at hw
        exact hw⟩
  exact hband

/-! ## The negation symmetry -/

/-- The negation of the ambient space, as a linear isometry. -/
noncomputable def negLI (k m : ℕ) : Amb (k+m) →ₗᵢ[ℝ] Amb (k+m) where
  toLinearMap := -(1 : Amb (k+m) →ₗ[ℝ] Amb (k+m))
  norm_map' y := by simp

theorem negLI_apply (k m : ℕ) (y : Amb (k+m)) : negLI k m y = -y := by simp [negLI]

/-- The negation of the incidence space: `(P,w) ↦ (-P,-w)`. -/
noncomputable def negE (k m : ℕ) (x : ↥(incZero k m)) : ↥(incZero k m) := rotE (negLI k m) x

theorem dirVec_negE (k m : ℕ) (x : ↥(incZero k m)) : dirVec (negE k m x) = -dirVec x := by
  rw [negE, dirVec_rotE, negLI_apply]

theorem evalVec_negE (k m : ℕ) (x : ↥(incZero k m)) :
    evalVec (negE k m x).1 = -evalVec x.1 := by
  rw [negE, evalVec_rotE, negLI_apply]

theorem negE_negE (k m : ℕ) (x : ↥(incZero k m)) : negE k m (negE k m x) = x := by
  simp only [negE]
  rw [← rotE_liComp]
  refine (rotE_congr (fun y => ?_) x).trans (rotE_one x)
  show negLI k m (negLI k m y) = (1 : Amb (k+m) →ₗᵢ[ℝ] Amb (k+m)) y
  rw [negLI_apply, negLI_apply, neg_neg]
  exact (LinearIsometry.id_apply y).symm

theorem mem_upSet_negE_iff (k m : ℕ) (x : ↥(incZero k m)) :
    negE k m x ∈ upSet k m ↔ x ∈ downSet k m := by
  show 0 < 2 * heightVec k m (negE k m x).1 + ‖evalVec (negE k m x).1‖ ↔
    0 < ‖evalVec x.1‖ - 2 * heightVec k m x.1
  have h1 : heightVec k m (negE k m x).1 = - heightVec k m x.1 := by
    rw [heightVec, heightVec, evalVec_negE, inner_neg_left]
  have h2 : ‖evalVec (negE k m x).1‖ = ‖evalVec x.1‖ := by rw [evalVec_negE, norm_neg]
  rw [h1, h2]
  constructor <;> intro h <;> linarith

theorem mem_downSet_negE_iff (k m : ℕ) (x : ↥(incZero k m)) :
    negE k m x ∈ downSet k m ↔ x ∈ upSet k m := by
  show 0 < ‖evalVec (negE k m x).1‖ - 2 * heightVec k m (negE k m x).1 ↔
    0 < 2 * heightVec k m x.1 + ‖evalVec x.1‖
  have h1 : heightVec k m (negE k m x).1 = - heightVec k m x.1 := by
    rw [heightVec, heightVec, evalVec_negE, inner_neg_left]
  have h2 : ‖evalVec (negE k m x).1‖ = ‖evalVec x.1‖ := by rw [evalVec_negE, norm_neg]
  rw [h1, h2]
  constructor <;> intro h <;> linarith

theorem mem_bandSet_negE_iff (k m : ℕ) (x : ↥(incZero k m)) :
    negE k m x ∈ bandSet k m ↔ x ∈ bandSet k m := by
  rw [bandSet, Set.mem_inter_iff, Set.mem_inter_iff, mem_upSet_negE_iff, mem_downSet_negE_iff]
  exact and_comm

theorem continuous_negE (k m : ℕ) : Continuous (negE k m) :=
  continuous_rotE_comp' (k := k) (m := m) (ι := ↥(incZero k m))
    (R := fun _ : ↥(incZero k m) => negLI k m)
    (by
      show Continuous fun q : ↥(incZero k m) × Amb (k+m) => -(q.2 : Amb (k+m))
      exact continuous_snd.neg)
    (fun x : ↥(incZero k m) => x) continuous_id

/-- The negation homeomorphism of the incidence space. -/
noncomputable def negHomeo (k m : ℕ) : ↥(incZero k m) ≃ₜ ↥(incZero k m) where
  toFun := negE k m
  invFun := negE k m
  left_inv := negE_negE k m
  right_inv := negE_negE k m
  continuous_toFun := continuous_negE k m
  continuous_invFun := continuous_negE k m

/-- The negation as a homeomorphism from the upper half to the lower half. -/
noncomputable def negUpHomeo (k m : ℕ) : ↥(upSet k m) ≃ₜ ↥(downSet k m) :=
  Homeomorph.subtype (negHomeo k m) (fun x => ⟨
    fun hx => (mem_downSet_negE_iff k m x).mpr hx,
    fun hx => (mem_downSet_negE_iff k m x).mp hx⟩)

/-- The negation as a homeomorphism of the band. -/
noncomputable def negBandHomeo (k m : ℕ) : ↥(bandSet k m) ≃ₜ ↥(bandSet k m) :=
  Homeomorph.subtype (negHomeo k m) (fun x => (mem_bandSet_negE_iff k m x).symm)

/-- The commuting square of the two inclusions and the negation. -/
theorem neg_bandIncl (k m : ℕ) :
    (bandInclUp k m).comp
        ((↑(negBandHomeo k m) : C(↥(bandSet k m), ↥(bandSet k m))))
      = ((↑((negUpHomeo k m).symm) : C(↥(downSet k m), ↥(upSet k m)))).comp
        (bandInclDown k m) := by
  apply ContinuousMap.ext
  intro x
  exact Subtype.ext rfl

/-- **The restriction `H^i(downSet) → H^i(bandSet)` is a bijection** in degrees `i + 2 ≤ k+m-1`. -/
theorem restV_band_bijective (k m i : ℕ) (hk : 1 ≤ k) (hi : i + 2 ≤ k + m - 1) :
    Function.Bijective (restV (X := TopCat.of ↥(zeroComp k m)) (upSet k m) (downSet k m) i) := by
  have hU : Function.Bijective ((singularCohomologyMap ℤ (TopCat.of ↥(bandSet k m))
      (TopCat.of ↥(upSet k m)) (TopCat.ofHom (bandInclUp k m)) i).hom) :=
    restU_band_bijective k m i hk hi
  let nu : C(↥(downSet k m), ↥(upSet k m)) :=
    (↑((negUpHomeo k m).symm) : C(↥(downSet k m), ↥(upSet k m)))
  let nb : C(↥(bandSet k m), ↥(bandSet k m)) :=
    (↑(negBandHomeo k m) : C(↥(bandSet k m), ↥(bandSet k m)))
  haveI hnu : IsIso (singularCohomologyMap ℤ (TopCat.of ↥(downSet k m))
      (TopCat.of ↥(upSet k m)) (TopCat.ofHom nu) i) :=
    isIso_singularCohomologyMap_of_homeomorph (negUpHomeo k m).symm i
  haveI hnb : IsIso (singularCohomologyMap ℤ (TopCat.of ↥(bandSet k m))
      (TopCat.of ↥(bandSet k m)) (TopCat.ofHom nb) i) :=
    isIso_singularCohomologyMap_of_homeomorph (negBandHomeo k m) i
  have hnu' : Function.Bijective ((singularCohomologyMap ℤ (TopCat.of ↥(downSet k m))
      (TopCat.of ↥(upSet k m)) (TopCat.ofHom nu) i).hom) := bijective_of_isIso_moduleCat _
  have hnb : Function.Bijective ((singularCohomologyMap ℤ (TopCat.of ↥(bandSet k m))
      (TopCat.of ↥(bandSet k m)) (TopCat.ofHom nb) i).hom) := bijective_of_isIso_moduleCat _
  have hceq : TopCat.ofHom nb ≫ TopCat.ofHom (bandInclUp k m)
      = TopCat.ofHom (bandInclDown k m) ≫ TopCat.ofHom nu := by
    change TopCat.ofHom ((bandInclUp k m).comp nb)
      = TopCat.ofHom (nu.comp (bandInclDown k m))
    rw [neg_bandIncl k m]
  have hid : ((singularCohomologyMap ℤ (TopCat.of ↥(bandSet k m)) (TopCat.of ↥(bandSet k m))
        (TopCat.ofHom nb) i).hom).comp
      ((singularCohomologyMap ℤ (TopCat.of ↥(bandSet k m)) (TopCat.of ↥(upSet k m))
        (TopCat.ofHom (bandInclUp k m)) i).hom)
      = ((singularCohomologyMap ℤ (TopCat.of ↥(bandSet k m)) (TopCat.of ↥(downSet k m))
        (TopCat.ofHom (bandInclDown k m)) i).hom).comp
        ((singularCohomologyMap ℤ (TopCat.of ↥(downSet k m)) (TopCat.of ↥(upSet k m))
          (TopCat.ofHom nu) i).hom) := by
    rw [← ModuleCat.hom_comp, ← ModuleCat.hom_comp,
      ← singularCohomologyMap_comp (R := ℤ) (TopCat.ofHom nb) (TopCat.ofHom (bandInclUp k m)) i,
      ← singularCohomologyMap_comp (R := ℤ) (TopCat.ofHom (bandInclDown k m)) (TopCat.ofHom nu) i]
    exact congrArg (fun φ => (singularCohomologyMap ℤ (TopCat.of ↥(bandSet k m))
      (TopCat.of ↥(upSet k m)) φ i).hom) hceq
  have hM : Function.Bijective
      (((singularCohomologyMap ℤ (TopCat.of ↥(bandSet k m)) (TopCat.of ↥(bandSet k m))
          (TopCat.ofHom nb) i).hom).comp
        ((singularCohomologyMap ℤ (TopCat.of ↥(bandSet k m)) (TopCat.of ↥(upSet k m))
          (TopCat.ofHom (bandInclUp k m)) i).hom)) :=
    ⟨fun x y hxy => hU.1 (hnb.1 hxy), fun z => by
      obtain ⟨u, hu⟩ := hnb.2 z
      obtain ⟨v, hv⟩ := hU.2 u
      exact ⟨v, by rw [LinearMap.comp_apply, hv, hu]⟩⟩
  have hcomp : Function.Bijective
      (((singularCohomologyMap ℤ (TopCat.of ↥(bandSet k m)) (TopCat.of ↥(downSet k m))
          (TopCat.ofHom (bandInclDown k m)) i).hom).comp
        ((singularCohomologyMap ℤ (TopCat.of ↥(downSet k m)) (TopCat.of ↥(upSet k m))
          (TopCat.ofHom nu) i).hom)) := by
    rw [← hid]
    exact hM
  refine ⟨fun x y hxy => ?_, fun z => ?_⟩
  · obtain ⟨x', hx'⟩ := hnu'.2 x
    obtain ⟨y', hy'⟩ := hnu'.2 y
    have h1 : x' = y' := hcomp.1 (by
      rw [LinearMap.comp_apply, LinearMap.comp_apply, hx', hy']
      exact hxy)
    rw [← hx', ← hy', h1]
  · obtain ⟨y, hy⟩ := hcomp.2 z
    exact ⟨((singularCohomologyMap ℤ (TopCat.of ↥(downSet k m)) (TopCat.of ↥(upSet k m))
      (TopCat.ofHom nu) i).hom) y, by
      rw [LinearMap.comp_apply] at hy
      exact hy⟩

end

end Work.ThomBordism.Grassmann
