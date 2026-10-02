import Mathlib
import Submission.Work.Thom.naturalModelClass_punct
import Submission.Work.Thom.relCohMap_homotopic
import Submission.Work.Thom.Glue
import Submission.Work.Thom.localThom_full
import Submission.Work.Thom.ATools
import Submission.Work.Thom.localThom_line
import Submission.Work.Thom.step_natural
import Submission.Work.Thom.localThom_genFibre
import Submission.Work.TangentClasses.Bundle

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 1600000
set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false

/-!
# The explicit local Thom class over a chart, and its behaviour under restriction

For a real bundle `Z → B` with model fibre `F` of rank `n`, a chart index `i` and a set
`W ⊆ Z.baseSet i`, this module builds an *explicit* local Thom class
`Work.Thom.localThomOfChart` over `W`, by pulling the natural model class
`Work.Thom.Mpun n ↥W` of the punctured trivial bundle back along the chart homeomorphism
`↥(Z.proj ⁻¹' W) ≃ₜ ↥W × ℝⁿ`.

Because the construction is explicit (rather than an opaque `Nonempty` from
`Work.Thom.localThom_genFibre`), the classes over the pieces of a cover can be compared:
`Work.Thom.localThomOfChart_restrict` shows that the class over `W` is the restriction of the class
over `U ⊇ W` (naturality of the construction), which is the compatibility input of
`Work.Thom.IsOrientedOver`.
-/

open Work.TangentClasses

namespace Work.Thom

open CategoryTheory

noncomputable section

variable {B : Type} [TopologicalSpace B] {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F]
variable {ι : Type}

/-! ## The base inclusion of a product trivial bundle -/

/-- The inclusion `↥W × ℝⁿ → ↥U × ℝⁿ` for `W ⊆ U`. -/
def prodIncl {B : Type} [TopologicalSpace B] (W U : Set B) (hWU : W ⊆ U) (n : ℕ) :
    C(↥W × EuclideanSpace ℝ (Fin n), ↥U × EuclideanSpace ℝ (Fin n)) :=
  ⟨fun q => (⟨(q.1 : B), hWU q.1.2⟩, q.2), by
    refine Continuous.prodMk ?_ continuous_snd
    exact (continuous_subtype_val.comp continuous_fst).subtype_mk (fun q => hWU q.1.2)⟩

@[simp] theorem prodIncl_apply {B : Type} [TopologicalSpace B] (W U : Set B) (hWU : W ⊆ U)
    (n : ℕ) (q : ↥W × EuclideanSpace ℝ (Fin n)) :
    prodIncl W U hWU n q = (⟨(q.1 : B), hWU q.1.2⟩, q.2) := rfl

/-- The inclusion of products composed with the base inclusion of `U` is the base inclusion of
`W`. -/
theorem prodIncl_comp_baseIncl {B : Type} [TopologicalSpace B] (W U : Set B) (hWU : W ⊆ U)
    (n : ℕ) : (baseIncl B U n).comp (prodIncl W U hWU n) = baseIncl B W n := by
  apply ContinuousMap.ext
  intro q
  rfl

/-- Membership in the punctured part is preserved by `prodIncl`. -/
theorem prodIncl_mem (n : ℕ) {B : Type} [TopologicalSpace B] (W U : Set B) (hWU : W ⊆ U) :
    ∀ p ∈ Punct ↥W n, prodIncl W U hWU n p ∈ Punct ↥U n := by
  intro p hp
  show (prodIncl W U hWU n p).2 ≠ 0
  rw [prodIncl_apply]
  exact hp

/-- **Naturality of the punctured model class under the inclusion `↥W → ↥U`** (`W ⊆ U`). -/
theorem Mpun_subtype (n : ℕ) {B : Type} [TopologicalSpace B] (W U : Set B) (hWU : W ⊆ U) :
    Mpun n ↥W =
      (relCohMap (prodIncl W U hWU n)
        {p : ↥W × EuclideanSpace ℝ (Fin n) | p.2 ≠ 0}
        {p : ↥U × EuclideanSpace ℝ (Fin n) | p.2 ≠ 0}
        (prodIncl_mem n W U hWU) ℤ n).hom (Mpun n ↥U) := by
  have h0 : Mpun n ↥W =
      (relCohMap (prodIncl W U hWU n)
        {p : ↥W × EuclideanSpace ℝ (Fin n) | p.2 ≠ 0}
        {p : ↥U × EuclideanSpace ℝ (Fin n) | p.2 ≠ 0}
        (fun _ hp => hp) ℤ n).hom (Mpun n ↥U) := by
    rw [← Mpun_natural n B W, ← Mpun_natural n B U]
    rw [relCohMap_compA_apply (A := {p : ↥W × EuclideanSpace ℝ (Fin n) | p.2 ≠ 0})
      (B := {p : ↥U × EuclideanSpace ℝ (Fin n) | p.2 ≠ 0})
      (C := {p : B × EuclideanSpace ℝ (Fin n) | p.2 ≠ 0})
      (prodIncl W U hWU n) (baseIncl B U n) (fun _ hp => hp) (fun _ hp => hp)
      (fun _ hp => hp) ℤ n (Mpun n B)]
    simp only [prodIncl_comp_baseIncl W U hWU n]
  rw [h0]

/-! ## The inclusion of the pieces of the total space -/

/-- The inclusion of the piece over `W` into the piece over `U`, for `W ⊆ U`. -/
def pieceIncl (Z : RealBundle B F ι) (W U : Set B) (hWU : W ⊆ U) :
    C(↥(Z.proj ⁻¹' W), ↥(Z.proj ⁻¹' U)) :=
  ⟨fun y => ⟨(y : Z.TotalSpace), hWU y.2⟩,
    Continuous.subtype_mk (f := fun y : ↥(Z.proj ⁻¹' W) => (y : Z.TotalSpace))
      continuous_subtype_val (fun y => hWU y.2)⟩

@[simp] theorem pieceIncl_apply (Z : RealBundle B F ι) (W U : Set B) (hWU : W ⊆ U)
    (p : ↥(Z.proj ⁻¹' W)) : pieceIncl Z W U hWU p = ⟨p.1, hWU p.2⟩ := rfl

/-- The complement of the zero section, inside the piece of the total space over `W`. -/
abbrev pieceZero (Z : RealBundle B F ι) (W : Set B) : Set ↥(Z.proj ⁻¹' W) :=
  (Subtype.val : ↥(Z.proj ⁻¹' W) → Z.TotalSpace) ⁻¹' zeroComplement Z

/-- The inclusion of the pieces carries the complement of the zero section into itself. -/
theorem pieceIncl_mem (Z : RealBundle B F ι) (W U : Set B) (hWU : W ⊆ U) :
    ∀ p ∈ pieceZero Z W, pieceIncl Z W U hWU p ∈ pieceZero Z U := by
  intro p hp
  exact hp

/-- `Work.Cohomology.pdCohMap` between two pieces is the pullback of relative cohomology along the
inclusion of the pieces. -/
theorem pdCohMap_eq_relCohMap (Z : RealBundle B F ι) (W U : Set B) (hWU : W ⊆ U) (k : ℕ) :
    Work.Cohomology.pdCohMap (TopCat.of Z.TotalSpace) (zeroComplement Z)
        (Z.proj ⁻¹' U) (Z.proj ⁻¹' W) (Set.preimage_mono hWU) k
      = relCohMap (pieceIncl Z W U hWU) (pieceZero Z W) (pieceZero Z U) (pieceIncl_mem Z W U hWU)
          ℤ k := rfl

/-! ## The chart homeomorphism of a piece with `↥W × ℝⁿ` -/

/-- **The chart homeomorphism of the piece over `W ⊆ Z.baseSet i` with `↥W × ℝⁿ`**: the chart
`Z.localTriv i` composed with a continuous linear equivalence `e : F ≃L[ℝ] ℝⁿ`. -/
def chartHomeo (Z : RealBundle B F ι) (n : ℕ) (e : F ≃L[ℝ] EuclideanSpace ℝ (Fin n))
    (i : ι) (W : Set B) (hW : W ⊆ Z.baseSet i) :
    ↥(Z.proj ⁻¹' W) ≃ₜ (↥W × EuclideanSpace ℝ (Fin n)) :=
  (pieceChartA Z i W hW).trans (prodCLEHomeo ↥W e)

theorem chartHomeo_apply (Z : RealBundle B F ι) (n : ℕ)
    (e : F ≃L[ℝ] EuclideanSpace ℝ (Fin n)) (i : ι) (W : Set B) (hW : W ⊆ Z.baseSet i)
    (p : ↥(Z.proj ⁻¹' W)) :
    chartHomeo Z n e i W hW p =
      (⟨Z.proj p.1, p.2⟩, e (Z.coordChange (Z.indexAt p.1.1) i p.1.1 p.1.2)) := by
  rw [chartHomeo, Homeomorph.trans_apply, pieceChartA_apply, prodCLEHomeo_apply]

/-- **The chart homeomorphism carries the complement of the zero section onto the punctured part
of `↥W × ℝⁿ`.** -/
theorem chartHomeo_mem_punct (Z : RealBundle B F ι) (n : ℕ)
    (e : F ≃L[ℝ] EuclideanSpace ℝ (Fin n)) (i : ι) (W : Set B) (hW : W ⊆ Z.baseSet i)
    (p : ↥(Z.proj ⁻¹' W)) :
    p ∈ pieceZero Z W ↔ chartHomeo Z n e i W hW p ∈ Punct ↥W n := by
  rw [Set.mem_preimage, mem_zeroComplement]
  show (show F from p.1.2) ≠ 0 ↔ (chartHomeo Z n e i W hW p).2 ≠ 0
  rw [chartHomeo_apply]
  exact ((coordChange_indexAt_eq_zero_iffA Z i p.1.1 (hW p.2) p.1.2).not.symm).trans
    (ContinuousLinearEquiv.map_eq_zero_iff e).not.symm

/-- The chart homeomorphism carries the complement of the zero section into the punctured part. -/
theorem chartHomeo_mem (Z : RealBundle B F ι) (n : ℕ)
    (e : F ≃L[ℝ] EuclideanSpace ℝ (Fin n)) (i : ι) (W : Set B) (hW : W ⊆ Z.baseSet i) :
    ∀ p ∈ pieceZero Z W,
      (chartHomeo Z n e i W hW : C(↥(Z.proj ⁻¹' W), ↥W × EuclideanSpace ℝ (Fin n))) p
        ∈ Punct ↥W n :=
  fun p hp => (chartHomeo_mem_punct Z n e i W hW p).mp hp

/-- The chart homeomorphism commutes with the projections to the base. -/
theorem projFstA_comp_chartHomeo (Z : RealBundle B F ι) (n : ℕ)
    (e : F ≃L[ℝ] EuclideanSpace ℝ (Fin n)) (i : ι) (W : Set B) (hW : W ⊆ Z.baseSet i) :
    (projFstA ↥W n).comp (chartHomeo Z n e i W hW :
        C(↥(Z.proj ⁻¹' W), ↥W × EuclideanSpace ℝ (Fin n))) = pieceProj Z W := by
  apply ContinuousMap.ext
  intro p
  exact congrArg Prod.fst (chartHomeo_apply Z n e i W hW p)

/-! ## The explicit local Thom class over a chart -/

/-- **The explicit local Thom class over `W ⊆ Z.baseSet i`**: the pullback of the natural model
class `Mpun n ↥W` of the punctured trivial bundle of rank `n` along the chart homeomorphism. -/
def localThomOfChart (Z : RealBundle B F ι) (n : ℕ)
    (e : F ≃L[ℝ] EuclideanSpace ℝ (Fin n)) (i : ι) (W : Set B) (hW : W ⊆ Z.baseSet i) :
    LocalThom Z n W :=
  ⟨(relCohMap (chartHomeo Z n e i W hW :
      C(↥(Z.proj ⁻¹' W), ↥W × EuclideanSpace ℝ (Fin n)))
      (pieceZero Z W) (Punct ↥W n) (chartHomeo_mem Z n e i W hW) ℤ n).hom (Mpun n ↥W),
    cupMap_transfer_fwdA
      (chartHomeo Z n e i W hW :
        C(↥(Z.proj ⁻¹' W), ↥W × EuclideanSpace ℝ (Fin n)))
      (Punct ↥W n) (pieceZero Z W) (chartHomeo_mem Z n e i W hW)
      (fun m => bijective_relCohMap_of_homeomorphA (pieceZero Z W) (Punct ↥W n)
        (chartHomeo Z n e i W hW) (chartHomeo_mem_punct Z n e i W hW) ℤ m)
      (projFstA ↥W n) (pieceProj Z W)
      (projFstA_comp_chartHomeo Z n e i W hW) n (Mpun n ↥W)
      (Mpun_isModel n ↥W)⟩

/-- The defining formula of the class of `Work.Thom.localThomOfChart`. -/
theorem localThomOfChart_tau (Z : RealBundle B F ι) (n : ℕ)
    (e : F ≃L[ℝ] EuclideanSpace ℝ (Fin n)) (i : ι) (W : Set B) (hW : W ⊆ Z.baseSet i) :
    (localThomOfChart Z n e i W hW).τ =
      (relCohMap (chartHomeo Z n e i W hW :
        C(↥(Z.proj ⁻¹' W), ↥W × EuclideanSpace ℝ (Fin n)))
        (pieceZero Z W) (Punct ↥W n) (chartHomeo_mem Z n e i W hW) ℤ n).hom (Mpun n ↥W) := rfl

/-! ## Naturality of the chart class under restriction to a smaller piece -/

/-- The chart homeomorphism of the smaller piece is the chart homeomorphism of the larger piece
after the inclusion of the products. -/
theorem chartHomeo_comp_pieceIncl (Z : RealBundle B F ι) (n : ℕ)
    (e : F ≃L[ℝ] EuclideanSpace ℝ (Fin n)) (i : ι) (W U : Set B) (hW : W ⊆ Z.baseSet i)
    (hU : U ⊆ Z.baseSet i) (hWU : W ⊆ U) :
    (chartHomeo Z n e i U hU : C(↥(Z.proj ⁻¹' U), ↥U × EuclideanSpace ℝ (Fin n))).comp
        (pieceIncl Z W U hWU)
      = (prodIncl W U hWU n).comp (chartHomeo Z n e i W hW :
          C(↥(Z.proj ⁻¹' W), ↥W × EuclideanSpace ℝ (Fin n))) := by
  apply ContinuousMap.ext
  intro p
  show chartHomeo Z n e i U hU (pieceIncl Z W U hWU p)
    = prodIncl W U hWU n (chartHomeo Z n e i W hW p)
  rw [chartHomeo_apply, chartHomeo_apply, pieceIncl_apply, prodIncl_apply]

/-- The composite `↥(Z.proj ⁻¹' W) → ↥U × ℝⁿ` carries the zero complement into the punctured
part. -/
theorem prodIncl_chartHomeo_mem (Z : RealBundle B F ι) (n : ℕ)
    (e : F ≃L[ℝ] EuclideanSpace ℝ (Fin n)) (i : ι) (W U : Set B) (hW : W ⊆ Z.baseSet i)
    (hWU : W ⊆ U) :
    ∀ p ∈ pieceZero Z W,
      ((prodIncl W U hWU n).comp (chartHomeo Z n e i W hW :
        C(↥(Z.proj ⁻¹' W), ↥W × EuclideanSpace ℝ (Fin n)))) p ∈ Punct ↥U n := by
  intro p hp
  show (prodIncl W U hWU n (chartHomeo Z n e i W hW p)).2 ≠ 0
  rw [prodIncl_apply]
  exact (chartHomeo_mem_punct Z n e i W hW p).mp hp

/-- **Naturality of the explicit chart class under restriction.**  For `W ⊆ U ⊆ Z.baseSet i`, the
restriction of the class over `U` to the piece over `W` is the class over `W`. -/
theorem localThomOfChart_restrict (Z : RealBundle B F ι) (n : ℕ)
    (e : F ≃L[ℝ] EuclideanSpace ℝ (Fin n)) (i : ι) (W U : Set B) (hW : W ⊆ Z.baseSet i)
    (hU : U ⊆ Z.baseSet i) (hWU : W ⊆ U) :
    (Work.Cohomology.pdCohMap (TopCat.of Z.TotalSpace) (zeroComplement Z)
        (Z.proj ⁻¹' U) (Z.proj ⁻¹' W) (Set.preimage_mono hWU) n).hom
      (localThomOfChart Z n e i U hU).τ = (localThomOfChart Z n e i W hW).τ := by
  have hcomp : ((chartHomeo Z n e i U hU :
        C(↥(Z.proj ⁻¹' U), ↥U × EuclideanSpace ℝ (Fin n))).comp (pieceIncl Z W U hWU))
      = ((prodIncl W U hWU n).comp (chartHomeo Z n e i W hW :
          C(↥(Z.proj ⁻¹' W), ↥W × EuclideanSpace ℝ (Fin n)))) :=
    chartHomeo_comp_pieceIncl Z n e i W U hW hU hWU
  have hL : (Work.Cohomology.pdCohMap (TopCat.of Z.TotalSpace) (zeroComplement Z)
        (Z.proj ⁻¹' U) (Z.proj ⁻¹' W) (Set.preimage_mono hWU) n).hom
      (localThomOfChart Z n e i U hU).τ
      = (relCohMap ((prodIncl W U hWU n).comp (chartHomeo Z n e i W hW :
            C(↥(Z.proj ⁻¹' W), ↥W × EuclideanSpace ℝ (Fin n))))
          (pieceZero Z W) (Punct ↥U n) (prodIncl_chartHomeo_mem Z n e i W U hW hWU) ℤ n).hom
          (Mpun n ↥U) := by
    have hstart : (Work.Cohomology.pdCohMap (TopCat.of Z.TotalSpace) (zeroComplement Z)
          (Z.proj ⁻¹' U) (Z.proj ⁻¹' W) (Set.preimage_mono hWU) n).hom
        (localThomOfChart Z n e i U hU).τ
        = (relCohMap (pieceIncl Z W U hWU) (pieceZero Z W) (pieceZero Z U)
            (pieceIncl_mem Z W U hWU) ℤ n).hom
            ((relCohMap (chartHomeo Z n e i U hU :
                C(↥(Z.proj ⁻¹' U), ↥U × EuclideanSpace ℝ (Fin n)))
              (pieceZero Z U) (Punct ↥U n) (chartHomeo_mem Z n e i U hU) ℤ n).hom
              (Mpun n ↥U)) := rfl
    rw [hstart]
    have happ := relCohMap_compA_apply (A := pieceZero Z W) (B := pieceZero Z U)
      (C := Punct ↥U n)
      (pieceIncl Z W U hWU) (chartHomeo Z n e i U hU :
        C(↥(Z.proj ⁻¹' U), ↥U × EuclideanSpace ℝ (Fin n)))
      (pieceIncl_mem Z W U hWU) (chartHomeo_mem Z n e i U hU)
      (fun p hp => (chartHomeo_mem_punct Z n e i U hU (pieceIncl Z W U hWU p)).mp
        (pieceIncl_mem Z W U hWU p hp)) ℤ n (Mpun n ↥U)
    rw [happ]
    have hmor : relCohMap ((chartHomeo Z n e i U hU :
          C(↥(Z.proj ⁻¹' U), ↥U × EuclideanSpace ℝ (Fin n))).comp (pieceIncl Z W U hWU))
        (pieceZero Z W) (Punct ↥U n)
        (fun p hp => (chartHomeo_mem_punct Z n e i U hU (pieceIncl Z W U hWU p)).mp
          (pieceIncl_mem Z W U hWU p hp)) ℤ n
      = relCohMap ((prodIncl W U hWU n).comp (chartHomeo Z n e i W hW :
          C(↥(Z.proj ⁻¹' W), ↥W × EuclideanSpace ℝ (Fin n))))
        (pieceZero Z W) (Punct ↥U n) (prodIncl_chartHomeo_mem Z n e i W U hW hWU) ℤ n :=
      relCohMap_congrA (pieceZero Z W) (Punct ↥U n) hcomp _ _ ℤ n
    rw [hmor]
  have hR : (localThomOfChart Z n e i W hW).τ
      = (relCohMap ((prodIncl W U hWU n).comp (chartHomeo Z n e i W hW :
            C(↥(Z.proj ⁻¹' W), ↥W × EuclideanSpace ℝ (Fin n))))
          (pieceZero Z W) (Punct ↥U n) (prodIncl_chartHomeo_mem Z n e i W U hW hWU) ℤ n).hom
          (Mpun n ↥U) := by
    have hstart : (localThomOfChart Z n e i W hW).τ
        = (relCohMap (chartHomeo Z n e i W hW :
            C(↥(Z.proj ⁻¹' W), ↥W × EuclideanSpace ℝ (Fin n)))
          (pieceZero Z W) (Punct ↥W n) (chartHomeo_mem Z n e i W hW) ℤ n).hom (Mpun n ↥W) := rfl
    rw [hstart, Mpun_subtype n W U hWU]
    have happ := relCohMap_compA_apply (A := pieceZero Z W) (B := Punct ↥W n)
      (C := Punct ↥U n)
      (chartHomeo Z n e i W hW : C(↥(Z.proj ⁻¹' W), ↥W × EuclideanSpace ℝ (Fin n)))
      (prodIncl W U hWU n) (chartHomeo_mem Z n e i W hW) (prodIncl_mem n W U hWU)
      (prodIncl_chartHomeo_mem Z n e i W U hW hWU) ℤ n (Mpun n ↥U)
    rw [happ]
  rw [hL, hR]


/-! ## The gauge change of a chart, and the comparison of the chart classes -/

/-- `Z.coordChange i j x = 0 ↔ v = 0` for `x` in the two charts. -/
theorem coordChange_ij_eq_zero_iff (Z : RealBundle B F ι) (i j : ι) (x : B)
    (hx : x ∈ Z.baseSet i ∩ Z.baseSet j) (v : F) :
    Z.coordChange i j x v = 0 ↔ v = 0 := by
  constructor
  · intro h
    have h2 := Z.coordChange_comp i j i x ⟨⟨hx.1, hx.2⟩, hx.1⟩ v
    rw [h, map_zero, Z.coordChange_self i x hx.1 v] at h2
    exact h2.symm
  · intro h
    rw [h, map_zero]

/-- **The gauge change of a chart**: on `W ⊆ baseSet i ∩ baseSet j`, the `j`-chart and the
`i`-chart differ by the transition function `Z.coordChange i j`, transported to the model fibre
`ℝⁿ` by a continuous linear equivalence `e`. -/
def gaugeMap (Z : RealBundle B F ι) (n : ℕ) (e : F ≃L[ℝ] EuclideanSpace ℝ (Fin n))
    (i j : ι) (W : Set B) (hW : W ⊆ Z.baseSet i ∩ Z.baseSet j) :
    C(↥W × EuclideanSpace ℝ (Fin n), ↥W × EuclideanSpace ℝ (Fin n)) where
  toFun q := (q.1, e (Z.coordChange i j q.1.1 (e.symm q.2)))
  continuous_toFun := by
    have hval : Continuous fun q : ↥W × EuclideanSpace ℝ (Fin n) => (q.1 : B) :=
      continuous_subtype_val.comp continuous_fst
    refine Continuous.prodMk continuous_fst ?_
    exact e.continuous.comp
      ((isBoundedBilinearMap_apply (𝕜 := ℝ) (E := F) (F := F)).continuous.comp
        (Continuous.prodMk
          ((Z.continuousOn_coordChange i j).comp_continuous hval (fun q => hW q.1.2))
          (e.symm.continuous.comp continuous_snd)))

@[simp] theorem gaugeMap_apply (Z : RealBundle B F ι) (n : ℕ)
    (e : F ≃L[ℝ] EuclideanSpace ℝ (Fin n)) (i j : ι) (W : Set B)
    (hW : W ⊆ Z.baseSet i ∩ Z.baseSet j) (q : ↥W × EuclideanSpace ℝ (Fin n)) :
    gaugeMap Z n e i j W hW q = (q.1, e (Z.coordChange i j q.1.1 (e.symm q.2))) := rfl

/-- The gauge change carries the punctured part into itself. -/
theorem gaugeMap_mem_punct (Z : RealBundle B F ι) (n : ℕ)
    (e : F ≃L[ℝ] EuclideanSpace ℝ (Fin n)) (i j : ι) (W : Set B)
    (hW : W ⊆ Z.baseSet i ∩ Z.baseSet j) :
    ∀ q ∈ Punct ↥W n, gaugeMap Z n e i j W hW q ∈ Punct ↥W n := by
  intro q hq
  show e (Z.coordChange i j q.1.1 (e.symm q.2)) ≠ 0
  intro h0
  rw [ContinuousLinearEquiv.map_eq_zero_iff] at h0
  have h1 : e.symm q.2 = 0 :=
    (coordChange_ij_eq_zero_iff Z i j q.1.1 (hW q.1.2) (e.symm q.2)).mp h0
  exact hq (by rw [← e.apply_symm_apply q.2, h1, map_zero])

/-- **The `j`-chart of the piece over `W` is the gauge change applied to the `i`-chart.** -/
theorem chartHomeo_eq_gaugeMap (Z : RealBundle B F ι) (n : ℕ)
    (e : F ≃L[ℝ] EuclideanSpace ℝ (Fin n)) (i j : ι) (W : Set B)
    (hWi : W ⊆ Z.baseSet i) (hWj : W ⊆ Z.baseSet j) (hW : W ⊆ Z.baseSet i ∩ Z.baseSet j) :
    (chartHomeo Z n e j W hWj : C(↥(Z.proj ⁻¹' W), ↥W × EuclideanSpace ℝ (Fin n)))
      = (gaugeMap Z n e i j W hW).comp (chartHomeo Z n e i W hWi :
          C(↥(Z.proj ⁻¹' W), ↥W × EuclideanSpace ℝ (Fin n))) := by
  apply ContinuousMap.ext
  intro p
  show chartHomeo Z n e j W hWj p = gaugeMap Z n e i j W hW (chartHomeo Z n e i W hWi p)
  rw [chartHomeo_apply, chartHomeo_apply, gaugeMap_apply, ContinuousLinearEquiv.symm_apply_apply,
    Z.coordChange_comp (Z.indexAt p.1.1) i j p.1.1
      ⟨⟨Z.mem_baseSet_at p.1.1, hWi p.2⟩, hWj p.2⟩ p.1.2]

/-- **The homotopy of gauge changes** through invertible maps. -/
def gaugeHom (Z : RealBundle B F ι) (n : ℕ) (e : F ≃L[ℝ] EuclideanSpace ℝ (Fin n))
    (i j : ι) (W : Set B) (H : C(unitInterval × ↥W, F →L[ℝ] F)) :
    C(unitInterval × (↥W × EuclideanSpace ℝ (Fin n)), ↥W × EuclideanSpace ℝ (Fin n)) where
  toFun p := (p.2.1, e (H (p.1, p.2.1) (e.symm p.2.2)))
  continuous_toFun := by
    refine Continuous.prodMk (continuous_fst.comp continuous_snd) ?_
    exact e.continuous.comp
      ((isBoundedBilinearMap_apply (𝕜 := ℝ) (E := F) (F := F)).continuous.comp
        (Continuous.prodMk
          (H.continuous.comp (continuous_fst.prodMk (continuous_fst.comp continuous_snd)))
          (e.symm.continuous.comp (continuous_snd.comp continuous_snd))))

@[simp] theorem gaugeHom_apply (Z : RealBundle B F ι) (n : ℕ)
    (e : F ≃L[ℝ] EuclideanSpace ℝ (Fin n)) (i j : ι) (W : Set B)
    (H : C(unitInterval × ↥W, F →L[ℝ] F))
    (p : unitInterval × (↥W × EuclideanSpace ℝ (Fin n))) :
    gaugeHom Z n e i j W H p = (p.2.1, e (H (p.1, p.2.1) (e.symm p.2.2))) := rfl

/-- At `t = 0` the gauge homotopy is the gauge change. -/
theorem gaugeHom_zero (Z : RealBundle B F ι) (n : ℕ)
    (e : F ≃L[ℝ] EuclideanSpace ℝ (Fin n)) (i j : ι) (W : Set B)
    (H : C(unitInterval × ↥W, F →L[ℝ] F))
    (H0 : ∀ x : ↥W, H (0, x) = Z.coordChange i j (x : B))
    (hW : W ⊆ Z.baseSet i ∩ Z.baseSet j) (q : ↥W × EuclideanSpace ℝ (Fin n)) :
    gaugeHom Z n e i j W H (0, q) = gaugeMap Z n e i j W hW q := by
  rw [gaugeHom_apply, gaugeMap_apply, H0 q.1]

/-- At `t = 1` the gauge homotopy is the identity. -/
theorem gaugeHom_one (Z : RealBundle B F ι) (n : ℕ)
    (e : F ≃L[ℝ] EuclideanSpace ℝ (Fin n)) (i j : ι) (W : Set B)
    (H : C(unitInterval × ↥W, F →L[ℝ] F))
    (H1 : ∀ x : ↥W, H (1, x) = 1) (q : ↥W × EuclideanSpace ℝ (Fin n)) :
    gaugeHom Z n e i j W H (1, q) = q := by
  rw [gaugeHom_apply, H1 q.1]
  simp

/-- The gauge homotopy is a homotopy of maps of the punctured pair. -/
theorem gaugeHom_mem_punct (Z : RealBundle B F ι) (n : ℕ)
    (e : F ≃L[ℝ] EuclideanSpace ℝ (Fin n)) (i j : ι) (W : Set B)
    (H : C(unitInterval × ↥W, F →L[ℝ] F))
    (Hinv : ∀ t x, Function.Bijective (H (t, x))) :
    ∀ t (q : ↥W × EuclideanSpace ℝ (Fin n)), q ∈ Punct ↥W n →
      gaugeHom Z n e i j W H (t, q) ∈ Punct ↥W n := by
  intro t q hq
  show e (H (t, q.1) (e.symm q.2)) ≠ 0
  intro h0
  rw [ContinuousLinearEquiv.map_eq_zero_iff] at h0
  have h1 : e.symm q.2 = 0 := (Hinv t q.1).1 (by rw [h0, map_zero])
  exact hq (by rw [← e.apply_symm_apply q.2, h1, map_zero])

/-- **The gauge change acts trivially on the model class.** -/
theorem gaugeMap_Mpun (Z : RealBundle B F ι) (n : ℕ)
    (e : F ≃L[ℝ] EuclideanSpace ℝ (Fin n)) (i j : ι) (W : Set B)
    (hW : W ⊆ Z.baseSet i ∩ Z.baseSet j) (H : C(unitInterval × ↥W, F →L[ℝ] F))
    (H0 : ∀ x : ↥W, H (0, x) = Z.coordChange i j (x : B))
    (H1 : ∀ x : ↥W, H (1, x) = 1)
    (Hinv : ∀ t x, Function.Bijective (H (t, x))) :
    (relCohMap (gaugeMap Z n e i j W hW) (Punct ↥W n) (Punct ↥W n)
      (gaugeMap_mem_punct Z n e i j W hW) ℤ n).hom (Mpun n ↥W) = Mpun n ↥W := by
  let hhom : ContinuousMap.Homotopy (gaugeMap Z n e i j W hW)
      (ContinuousMap.id (↥W × EuclideanSpace ℝ (Fin n))) :=
    ContinuousMap.Homotopy.mk (gaugeHom Z n e i j W H)
      (fun q => gaugeHom_zero Z n e i j W H H0 hW q)
      (fun q => gaugeHom_one Z n e i j W H H1 q)
  have h := relCohMap_homotopic (Punct ↥W n) (Punct ↥W n)
    (gaugeMap_mem_punct Z n e i j W hW) (fun _ hp => hp) hhom
    (fun t q hq => gaugeHom_mem_punct Z n e i j W H Hinv t q hq) ℤ n
  rw [h, relCohMap_idA]
  rfl

/-- **The chart classes over `W` for the two charts `i`, `j` agree**, given a gauge homotopy
through invertible maps. -/
theorem localThomOfChart_eq_of_gauge (Z : RealBundle B F ι) (n : ℕ)
    (e : F ≃L[ℝ] EuclideanSpace ℝ (Fin n)) (i j : ι) (W : Set B)
    (hWi : W ⊆ Z.baseSet i) (hWj : W ⊆ Z.baseSet j) (hW : W ⊆ Z.baseSet i ∩ Z.baseSet j)
    (H : C(unitInterval × ↥W, F →L[ℝ] F))
    (H0 : ∀ x : ↥W, H (0, x) = Z.coordChange i j (x : B))
    (H1 : ∀ x : ↥W, H (1, x) = 1)
    (Hinv : ∀ t x, Function.Bijective (H (t, x))) :
    (localThomOfChart Z n e j W hWj).τ = (localThomOfChart Z n e i W hWi).τ := by
  have hcomp : (chartHomeo Z n e j W hWj :
        C(↥(Z.proj ⁻¹' W), ↥W × EuclideanSpace ℝ (Fin n)))
      = (gaugeMap Z n e i j W hW).comp (chartHomeo Z n e i W hWi :
          C(↥(Z.proj ⁻¹' W), ↥W × EuclideanSpace ℝ (Fin n))) :=
    chartHomeo_eq_gaugeMap Z n e i j W hWi hWj hW
  have hcj : ∀ p ∈ pieceZero Z W,
      (chartHomeo Z n e j W hWj : C(↥(Z.proj ⁻¹' W), ↥W × EuclideanSpace ℝ (Fin n))) p
        ∈ Punct ↥W n := chartHomeo_mem Z n e j W hWj
  have hc2 : ∀ p ∈ pieceZero Z W,
      ((gaugeMap Z n e i j W hW).comp (chartHomeo Z n e i W hWi :
        C(↥(Z.proj ⁻¹' W), ↥W × EuclideanSpace ℝ (Fin n)))) p ∈ Punct ↥W n :=
    fun p hp => gaugeMap_mem_punct Z n e i j W hW (chartHomeo Z n e i W hWi p)
      (chartHomeo_mem Z n e i W hWi p hp)
  have h1 : relCohMap (chartHomeo Z n e j W hWj :
        C(↥(Z.proj ⁻¹' W), ↥W × EuclideanSpace ℝ (Fin n)))
        (pieceZero Z W) (Punct ↥W n) hcj ℤ n
      = relCohMap ((gaugeMap Z n e i j W hW).comp (chartHomeo Z n e i W hWi :
            C(↥(Z.proj ⁻¹' W), ↥W × EuclideanSpace ℝ (Fin n))))
          (pieceZero Z W) (Punct ↥W n) hc2 ℤ n :=
    relCohMap_congrA (pieceZero Z W) (Punct ↥W n) hcomp hcj hc2 ℤ n
  have h2 := relCohMap_compA_apply (A := pieceZero Z W) (B := Punct ↥W n) (C := Punct ↥W n)
    (chartHomeo Z n e i W hWi : C(↥(Z.proj ⁻¹' W), ↥W × EuclideanSpace ℝ (Fin n)))
    (gaugeMap Z n e i j W hW) (chartHomeo_mem Z n e i W hWi)
    (gaugeMap_mem_punct Z n e i j W hW) hc2 ℤ n (Mpun n ↥W)
  have h3 : (relCohMap (chartHomeo Z n e i W hWi :
          C(↥(Z.proj ⁻¹' W), ↥W × EuclideanSpace ℝ (Fin n)))
          (pieceZero Z W) (Punct ↥W n) (chartHomeo_mem Z n e i W hWi) ℤ n).hom
          ((relCohMap (gaugeMap Z n e i j W hW) (Punct ↥W n) (Punct ↥W n)
            (gaugeMap_mem_punct Z n e i j W hW) ℤ n).hom (Mpun n ↥W))
      = (relCohMap (chartHomeo Z n e i W hWi :
            C(↥(Z.proj ⁻¹' W), ↥W × EuclideanSpace ℝ (Fin n)))
            (pieceZero Z W) (Punct ↥W n) (chartHomeo_mem Z n e i W hWi) ℤ n).hom
            (Mpun n ↥W) := by
    rw [gaugeMap_Mpun Z n e i j W hW H H0 H1 Hinv]
  have hstart : (localThomOfChart Z n e j W hWj).τ
      = (relCohMap (chartHomeo Z n e j W hWj :
            C(↥(Z.proj ⁻¹' W), ↥W × EuclideanSpace ℝ (Fin n)))
            (pieceZero Z W) (Punct ↥W n) hcj ℤ n).hom (Mpun n ↥W) := rfl
  have hend : (relCohMap (chartHomeo Z n e i W hWi :
          C(↥(Z.proj ⁻¹' W), ↥W × EuclideanSpace ℝ (Fin n)))
          (pieceZero Z W) (Punct ↥W n) (chartHomeo_mem Z n e i W hWi) ℤ n).hom
          (Mpun n ↥W) = (localThomOfChart Z n e i W hWi).τ := rfl
  rw [hstart, congrArg (fun φ => φ.hom (Mpun n ↥W)) h1, ← h2, h3, hend]

end

end Work.Thom
