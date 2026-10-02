import Mathlib
import Submission.Work.ThomBordism.Grassmann.zStdSetup
import Submission.Work.ThomBordism.Grassmann.p1RatPuncture
import Submission.Work.ThomBordism.Grassmann.ZStdURSupport
import Submission.Work.Agree.mapFibreIso
import Submission.Work.Thom.LineGeom

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# `H⁴` of the piece `UR = {Re ≠ 0}` of the punctured total space of `W`

See `Submission/Work/ThomBordism/Grassmann/ZStdURSupport.lean` for the reusable input (the
continuity of the real-part projection `W → zStd` and of the inclusion `zStd → W`, and the
vanishing `H⁴(zStd∖0) = 0`).  Here we put these together:

* `Work.ThomBordism.Grassmann.rhoMap` — the retraction `UR → zStd∖0`, `(b,u,v) ↦ (b,u)`;
* `Work.ThomBordism.Grassmann.etaMap` — the section `zStd∖0 → UR`, `(b,u) ↦ (b,u,0)`;
* `Work.ThomBordism.Grassmann.homotopyFibre`, `homotopyTotal`, `homotopyFun`, `homotopyMap`,
  `URHomotopy` — the straight-line homotopy `(t,p) ↦ (1-t)·v + t·P(v)` (`P` = the fibrewise real
  part), which is continuous by `Work.Thom.continuous_smul_section` (twice) and
  `Work.Thom.continuous_add_section`;
* `Work.ThomBordism.Grassmann.URHomotopyEquiv` — the resulting homotopy equivalence `UR ≃ zStd∖0`;
* `Work.ThomBordism.Grassmann.zStd_UR_cohomology` — homotopy invariance.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

open Work.TangentClasses

namespace Work.ThomBordism.Grassmann

noncomputable section

/-! ## Reading the coordinates of a point of `UR` in the model fibre -/

/-- The base point of a point of `UR`. -/
def urBase (p : ↥UR) : Work.Projective.CP 2 := p.1.1.1

/-- The fibre coordinate of a point of `UR`, read in the model fibre `ℂ²`. -/
def urFibre (p : ↥UR) : EuclideanSpace ℂ (Fin 2) := p.1.1.2

/-- The base point of a point of `zStd∖0`. -/
def zdBase (q : ↥(Work.Thom.zeroComplement zStd)) : Work.Projective.CP 2 := q.1.1

/-- The fibre coordinate of a point of `zStd∖0`, read in the model fibre `ℝ²`. -/
def zdFibre (q : ↥(Work.Thom.zeroComplement zStd)) : EuclideanSpace ℝ (Fin 2) := q.1.2

/-- The real part of the fibre coordinate of a point of the total space of `W`, read in the model
fibre `ℝ²`. -/
def cxRePartOf (p : W.TotalSpace) : EuclideanSpace ℝ (Fin 2) := Work.Thom.cxRePart p.2

/-! ## The retraction onto `zStd∖0` and its section -/

/-- **The retraction of `UR` onto `zStd∖0`**: read the real part, forget the imaginary part. -/
noncomputable def rhoMap : C(↥UR, ↥(Work.Thom.zeroComplement zStd)) where
  toFun p := ⟨rhoTotal p.1.1, p.2⟩
  continuous_toFun := by
    have h1 : Continuous (fun p : ↥UR => (p.1.1 : W.TotalSpace)) :=
      (continuous_subtype_val (p := fun q : W.TotalSpace =>
          q ∈ Work.Thom.zeroComplement W)).comp
        (continuous_subtype_val (p := fun p : ↥(Work.Thom.zeroComplement W) => p ∈ UR))
    exact Continuous.subtype_mk (continuous_rhoTotal.comp h1) (fun p => p.2)

/-- A point of `zStd∖0`, included as the real part of `W`, lies in `UR`. -/
theorem etaFun_mem (q : ↥(Work.Thom.zeroComplement zStd)) :
    (⟨zdBase q, Work.Thom.cxOfReal (zdFibre q)⟩ : W.TotalSpace)
        ∈ Work.Thom.zeroComplement W :=
  fun h => q.2 (by
    change zdFibre q = 0
    have h2 : Work.Thom.cxOfReal (zdFibre q) = 0 := h
    rw [← Work.Thom.cxRePart_cxOfReal (zdFibre q), h2, map_zero])

/-- The real part of an included point of `zStd∖0` does not vanish. -/
theorem etaFun_memUR (q : ↥(Work.Thom.zeroComplement zStd)) :
    cxRePartOf ⟨zdBase q, Work.Thom.cxOfReal (zdFibre q)⟩ ≠ 0 := by
  have h : cxRePartOf ⟨zdBase q, Work.Thom.cxOfReal (zdFibre q)⟩ = zdFibre q :=
    Work.Thom.cxRePart_cxOfReal (zdFibre q)
  rw [h]
  exact q.2

/-- **The section of `rhoMap`**: include `zStd` as the real part of `W`. -/
noncomputable def etaMap : C(↥(Work.Thom.zeroComplement zStd), ↥UR) where
  toFun q := ⟨⟨⟨zdBase q, Work.Thom.cxOfReal (zdFibre q)⟩, etaFun_mem q⟩, etaFun_memUR q⟩
  continuous_toFun := Continuous.subtype_mk
    (Continuous.subtype_mk (continuous_etaTotal.comp continuous_subtype_val)
      (fun q => etaFun_mem q))
    (fun q => etaFun_memUR q)

/-! ## The straight-line homotopy -/

/-- The fibre component of the straight-line homotopy at time `t`:
`(1-t)·v + t·P(v)`, where `P` is the fibrewise real part. -/
noncomputable def homotopyFibre (x : ↑unitInterval × ↥UR) : EuclideanSpace ℂ (Fin 2) :=
  (1 - (x.1 : ℝ)) • urFibre x.2
    + (x.1 : ℝ) • Work.Thom.cxOfReal (Work.Thom.cxRePart (urFibre x.2))

/-- The real part of the interpolated vector is the real part of the original vector. -/
theorem cxRePart_homotopyFibre (x : ↑unitInterval × ↥UR) :
    Work.Thom.cxRePart (homotopyFibre x) = Work.Thom.cxRePart (urFibre x.2) := by
  rw [homotopyFibre, map_add, map_smul, map_smul, Work.Thom.cxRePart_cxOfReal,
    ← add_smul, sub_add_cancel, one_smul]

/-- The interpolated vector never vanishes. -/
theorem homotopyFibre_ne_zero (x : ↑unitInterval × ↥UR) : homotopyFibre x ≠ 0 := fun h =>
  x.2.2 (by
    change Work.Thom.cxRePart (urFibre x.2) = 0
    rw [← cxRePart_homotopyFibre x, h, map_zero])

/-- The interpolated vector has non-vanishing real part (so the homotopy stays inside `UR`). -/
theorem cxRePart_homotopyFibre_ne_zero (x : ↑unitInterval × ↥UR) :
    Work.Thom.cxRePart (homotopyFibre x) ≠ 0 := by
  rw [cxRePart_homotopyFibre]
  exact x.2.2

/-- The straight-line homotopy, as a map into the total space of `W`. -/
noncomputable def homotopyTotal : C(↑unitInterval × ↥UR, W.TotalSpace) where
  toFun x := ⟨urBase x.2, homotopyFibre x⟩
  continuous_toFun := by
    have hσ₀ : Continuous (fun x : ↑unitInterval × ↥UR => (x.2.1.1 : W.TotalSpace)) :=
      continuous_subtype_val.comp (continuous_subtype_val.comp continuous_snd)
    have hc₁ : Continuous (fun x : ↑unitInterval × ↥UR => 1 - (x.1 : ℝ)) :=
      continuous_const.sub (continuous_subtype_val.comp continuous_fst)
    have hc₂ : Continuous (fun x : ↑unitInterval × ↥UR => (x.1 : ℝ)) :=
      continuous_subtype_val.comp continuous_fst
    have hP : Continuous (fun x : ↑unitInterval × ↥UR =>
        (⟨urBase x.2, Work.Thom.cxOfReal
          (Work.Thom.cxRePart (urFibre x.2))⟩ : W.TotalSpace)) :=
      continuous_Ptot.comp hσ₀
    have hσ : Continuous (fun x : ↑unitInterval × ↥UR =>
        (⟨urBase x.2, (1 - (x.1 : ℝ)) • urFibre x.2⟩ : W.TotalSpace)) :=
      Work.Thom.continuous_smul_section W
        ⟨fun x : ↑unitInterval × ↥UR => x.2.1.1, hσ₀⟩
        ⟨fun x : ↑unitInterval × ↥UR => 1 - (x.1 : ℝ), hc₁⟩
    have hτ : Continuous (fun x : ↑unitInterval × ↥UR =>
        (⟨urBase x.2, (x.1 : ℝ) • Work.Thom.cxOfReal
          (Work.Thom.cxRePart (urFibre x.2))⟩ : W.TotalSpace)) :=
      Work.Thom.continuous_smul_section W
        ⟨fun x : ↑unitInterval × ↥UR => (⟨urBase x.2, Work.Thom.cxOfReal
          (Work.Thom.cxRePart (urFibre x.2))⟩ : W.TotalSpace), hP⟩
        ⟨fun x : ↑unitInterval × ↥UR => (x.1 : ℝ), hc₂⟩
    exact Work.Thom.continuous_add_section W
      ⟨fun x : ↑unitInterval × ↥UR => (⟨urBase x.2,
        (1 - (x.1 : ℝ)) • urFibre x.2⟩ : W.TotalSpace), hσ⟩
      ⟨fun x : ↑unitInterval × ↥UR => (⟨urBase x.2, (x.1 : ℝ) • Work.Thom.cxOfReal
        (Work.Thom.cxRePart (urFibre x.2))⟩ : W.TotalSpace), hτ⟩
      (fun _ => rfl)

/-- The straight-line homotopy, as a map into `UR`. -/
noncomputable def homotopyFun (x : ↑unitInterval × ↥UR) : ↥UR :=
  ⟨⟨⟨urBase x.2, homotopyFibre x⟩, homotopyFibre_ne_zero x⟩,
    cxRePart_homotopyFibre_ne_zero x⟩

/-- The straight-line homotopy, as a continuous map into `UR`. -/
noncomputable def homotopyMap : C(↑unitInterval × ↥UR, ↥UR) where
  toFun := homotopyFun
  continuous_toFun := Continuous.subtype_mk
    (Continuous.subtype_mk homotopyTotal.continuous (fun x => homotopyFibre_ne_zero x))
    (fun x => cxRePart_homotopyFibre_ne_zero x)

/-- **The straight-line homotopy from the identity of `UR` to the retraction followed by its
section** (`(t,p) ↦ (1-t)·v + t·P(v)`). -/
noncomputable def URHomotopy :
    ContinuousMap.Homotopy (ContinuousMap.id ↥UR) (etaMap.comp rhoMap) :=
  ContinuousMap.Homotopy.mk homotopyMap
    (by
      intro p
      apply Subtype.ext
      apply Subtype.ext
      show (⟨urBase p, homotopyFibre ((0 : ↑unitInterval), p)⟩ : W.TotalSpace) = p.1.1
      rw [homotopyFibre, Set.Icc.coe_zero]
      simp only [sub_zero, one_smul, zero_smul, add_zero]
      rfl)
    (by
      intro p
      apply Subtype.ext
      apply Subtype.ext
      change (⟨urBase p, homotopyFibre ((1 : ↑unitInterval), p)⟩ : W.TotalSpace) =
        ↑↑((etaMap.comp rhoMap) p)
      rw [homotopyFibre, Set.Icc.coe_one]
      simp only [sub_self, zero_smul, one_smul, zero_add]
      rfl)

/-! ## The homotopy equivalence and the vanishing of `H⁴` -/

/-- **`UR` is homotopy equivalent to the punctured total space of `zStd`** (the retraction
`(b,u,v) ↦ (b,u)` and the section `(b,u) ↦ (b,u,0)` are homotopy inverse to each other). -/
noncomputable def URHomotopyEquiv :
    ContinuousMap.HomotopyEquiv ↥UR ↥(Work.Thom.zeroComplement zStd) where
  toFun := rhoMap
  invFun := etaMap
  left_inv := ⟨URHomotopy.symm⟩
  right_inv := by
    have h : rhoMap.comp etaMap = ContinuousMap.id ↥(Work.Thom.zeroComplement zStd) := by
      apply ContinuousMap.ext
      intro q
      apply Subtype.ext
      change (⟨zdBase q, Work.Thom.cxRePart
        (Work.Thom.cxOfReal (zdFibre q))⟩ : zStd.TotalSpace) = ↑q
      rw [Work.Thom.cxRePart_cxOfReal]
      rfl
    exact h ▸ ContinuousMap.Homotopic.refl _

/-- **`H⁴` of the piece `UR = {Re ≠ 0}` of the punctured total space of `W` vanishes.**

`UR = {p : ↥(zeroComplement W) | cxRePart p.1.2 ≠ 0}` (`Submission/Work/ThomBordism/Grassmann/zStdSetup.lean`),
where `W = realification (complexificationCore zStd)` is the rank-`4` real bundle over `ℂP²` and
`zStd = (realification (tautDual 2)).mapFibre equivC1R2` is the realification of the tautological
dual line bundle.

Route: the complexification splits as `W ≅ zStd ⊕ zStd` on `Re ⊕ Im`; retracting the *imaginary*
coordinate to zero along the straight-line homotopy `(t,p) ↦ (1-t)·v + t·P(v)` (`P` = the fibrewise
real part) gives a homotopy equivalence `UR ≃ zeroComplement zStd` (continuity of the bundle
morphisms `W → zStd` by `Work.Thom.continuous_totalSpaceMap_clm_gen`, of the two scaled summands by
`Work.Thom.continuous_smul_section'` and of their sum by `Work.Thom.continuous_add_section`), and
`H⁴(zeroComplement zStd) = 0`: it is homeomorphic to
`zeroComplement (realification (tautDual 2))` (`BundleIso.punctHomeomorph` along a `mapFibre` bundle
isomorphism, cf. `Work.Agree.nonempty_bundleIso_mapFibre_of_iso` and
`Work.Thom.zeroComplementCore_eq_zeroComplement`) which has vanishing cohomology in all degrees
`≠ 0, 5` — this is the proved lemma
`Work.ThomBordism.Grassmann.puncturedTautDualTwoHZero` of
`Submission/Work/ThomBordism/Grassmann/p1Rat_ne_zero_via_probe.lean` (`Work.Gen.ChernGen.tautDualPunctHomeo 2`
identifies it with `ℂ³∖0 ≃ S⁵`).  Homotopy invariance:
`Work.Cohomology.cohomologyIso_of_homotopyEquiv`. -/
theorem zStd_UR_cohomology :
    Subsingleton (Work.Thom.Coh ℤ 4 ↥Work.ThomBordism.Grassmann.UR) := by
  obtain ⟨iso⟩ := Work.Cohomology.cohomologyIso_of_homotopyEquiv URHomotopyEquiv 4
  exact ModuleCat.subsingleton_of_isZero
    (CategoryTheory.Limits.IsZero.of_iso isZero_cohomology_four_zStd iso)

end

end Work.ThomBordism.Grassmann
