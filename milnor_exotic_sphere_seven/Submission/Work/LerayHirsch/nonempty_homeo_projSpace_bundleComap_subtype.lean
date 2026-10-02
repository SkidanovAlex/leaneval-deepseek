import Mathlib
import Submission.Work.LerayHirsch.Punctum
import Submission.Work.Thom.complexPullback
import Submission.Work.Thom.Pair
import Submission.Work.Thom.comapAux

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option linter.unusedVariables false

/-!
# `P(E|_U) = π^{-1}(U)`: the projectivisation commutes with restriction to a subspace

For a complex gluing-data bundle `Z` over `B` and an **arbitrary** subset `U ⊆ B` (no openness
assumed), the projectivisation of the restricted bundle `Z|_U = bundleComap Z (subtypeMap U)` is
the part of `P(E)` lying over `U`:

  `Work.LerayHirsch.nonempty_homeo_projSpace_bundleComap_subtype`:
  `ProjSpace (Z|_U) ≃ₜ ↥(projMap Z ⁻¹' U)`.

This is the identification needed by the Mayer–Vietoris rung of Leray–Hirsch
(`Work.LerayHirsch.LerayHirschGlue`), where it is applied with `U` open.

## The route

`P(E) = (E∖0)/ℂˣ` is a quotient by a group action, so `mkProj Z` is an **open** quotient map
(`isOpenMap_mkProj`); the `ℂˣ`-action on the punctured total space is by homeomorphisms because
fibrewise scalar multiplication by a constant is continuous in the gluing-data model
(`continuous_smulPunct`).  Then:

* `Work.LerayHirsch.isQuotientMap_restrict_of_saturated` (general topology): the restriction of a
  continuous open map to a *saturated* subset `q ⁻¹' T` is a quotient map onto `T`.  Applied to
  `q = mkProj Z` and `A = {x | x.1.proj ∈ U}` this identifies `↥(projMap Z ⁻¹' U)` with the
  quotient of `A` by the `ℂˣ`-action;
* `Work.LerayHirsch.exists_homeo_zeroComplement_comap_subtype` identifies the punctured total space
  of `Z|_U` with that saturated set `A`, compatibly with the `ℂˣ`-action;
* comparing the two quotients (universal property, bijectivity, quotient map) gives the
  homeomorphism.
-/

namespace Work.LerayHirsch

open Work.TangentClasses Work.Thom

open scoped LinearAlgebra.Projectivization

open Filter Topology

noncomputable section

variable {B : Type} [TopologicalSpace B] {ι : Type} {m : ℕ}

/-! ## The `ℂˣ`-action on the punctured total space is continuous -/

/-- The transition functions of the realification of a complex bundle are compatible with the
scalar action of `ℂ`: they are the `ℝ`-linear maps underlying `ℂ`-linear ones. -/
theorem coordChange_realification_smul (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι)
    (i j : ι) (b : B) (c : ℂ) (v : EuclideanSpace ℂ (Fin m)) :
    (realification Z).coordChange i j b (c • v)
      = c • ((realification Z).coordChange i j b v) := by
  rw [realification_coordChange Z i j b]
  exact map_smul (Z.coordChange i j b) c v

/-- **Fibrewise scalar multiplication by a unit is continuous** on the punctured total space of a
complex gluing-data bundle.  This is proved chart by chart: in the trivialisation `i` the map is
`(b, v) ↦ (b, c • v)`, which is continuous, and the trivialisations are open partial
homeomorphisms. -/
theorem continuous_smulPunct (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι) (c : ℂˣ) :
    Continuous (fun p : ↥(zeroComplement (realification Z)) => smulPunct Z c p) := by
  let Θ : (realification Z).TotalSpace → (realification Z).TotalSpace :=
    fun q => ⟨q.1, (c : ℂ) • (show EuclideanSpace ℂ (Fin m) from q.2)⟩
  have hΘ : Continuous Θ := by
    rw [continuous_iff_continuousAt]
    intro p
    set i := (realification Z).indexAt p.1 with hi
    set e := ((realification Z).localTriv i).toOpenPartialHomeomorph with he
    have hmem : p ∈ e.source := by
      rw [he]
      exact (VectorBundleCore.mem_localTriv_source _ _ _).mpr
        ((realification Z).mem_baseSet_at p.1)
    have hsrc : Θ ⁻¹' e.source ∈ 𝓝 p := by
      have hpre : Θ ⁻¹' e.source = e.source := by
        rw [he]
        ext q
        rw [Set.mem_preimage]
        rfl
      rw [hpre]
      exact e.open_source.mem_nhds hmem
    rw [e.continuousAt_iff_continuousAt_comp_left hsrc]
    have hkey : ∀ q : (realification Z).TotalSpace,
        e (Θ q) = (⟨q.1, (c : ℂ) • (e q).2⟩ : B × EuclideanSpace ℂ (Fin m)) := by
      intro q
      show ((realification Z).localTriv i)
            ((⟨q.1, (c : ℂ) • (show EuclideanSpace ℂ (Fin m) from q.2)⟩ :
              (realification Z).TotalSpace))
          = (⟨q.1, (c : ℂ) • (((realification Z).localTriv i) q).2⟩ :
                B × EuclideanSpace ℂ (Fin m))
      rw [VectorBundleCore.localTriv_apply, VectorBundleCore.localTriv_apply]
      congr 1
      exact coordChange_realification_smul Z ((realification Z).indexAt q.1) i q.1 (c : ℂ) q.2
    have hψ : Continuous (fun w : B × EuclideanSpace ℂ (Fin m) =>
        (⟨w.1, (c : ℂ) • w.2⟩ : B × EuclideanSpace ℂ (Fin m))) :=
      continuous_fst.prodMk (continuous_snd.const_smul (c : ℂ))
    have h1 : ContinuousAt (fun q : (realification Z).TotalSpace =>
        (⟨q.1, (c : ℂ) • (e q).2⟩ : B × EuclideanSpace ℂ (Fin m))) p :=
      hψ.continuousAt.comp (e.continuousAt hmem)
    exact h1.congr (Filter.Eventually.of_forall fun q => (hkey q).symm)
  have h2 : Continuous (fun p : ↥(zeroComplement (realification Z)) =>
      (⟨Θ p.1, (smulPunct Z c p).2⟩ : ↥(zeroComplement (realification Z)))) :=
    Continuous.subtype_mk (hΘ.comp continuous_subtype_val) _
  exact h2.congr (fun _ => Subtype.ext rfl)

/-- Fibrewise scalar multiplication by `c : ℂˣ` as a homeomorphism of the punctured total
space. -/
def smulPunctHomeo (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι) (c : ℂˣ) :
    ↥(zeroComplement (realification Z)) ≃ₜ ↥(zeroComplement (realification Z)) where
  toFun := fun p => smulPunct Z c p
  invFun := fun p => smulPunct Z c⁻¹ p
  left_inv := fun p => by
    have h := smulPunct_mul Z c⁻¹ c p
    rw [inv_mul_cancel, smulPunct_one] at h
    exact h.symm
  right_inv := fun p => by
    have h := smulPunct_mul Z c c⁻¹ p
    rw [mul_inv_cancel, smulPunct_one] at h
    exact h.symm
  continuous_toFun := continuous_smulPunct Z c
  continuous_invFun := continuous_smulPunct Z c⁻¹

theorem isOpenMap_smulPunct (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι) (c : ℂˣ) :
    IsOpenMap (fun p : ↥(zeroComplement (realification Z)) => smulPunct Z c p) :=
  (smulPunctHomeo Z c).isOpenMap

/-! ## `E∖0 → P(E)` is an open map -/

/-- **The quotient map `mkProj Z : E∖0 → P(E)` is open.**  Its preimage of the image of an open set
`W` is the union of the `ℂˣ`-translates of `W`, each of which is open because the action is by
homeomorphisms; openness in the quotient topology is openness of the preimage. -/
theorem isOpenMap_mkProj (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι) :
    IsOpenMap (mkProj Z) := by
  intro W hW
  refine (isQuotientMap_quotient_mk' (s := projSetoid Z)).isCoinducing.isOpen_preimage.mp ?_
  change IsOpen (mkProj Z ⁻¹' (mkProj Z '' W))
  have hpre : (mkProj Z) ⁻¹' ((mkProj Z) '' W)
      = ⋃ c : ℂˣ, (fun p => smulPunct Z c p) '' W := by
    ext p
    rw [Set.mem_preimage, Set.mem_iUnion]
    constructor
    · rintro ⟨q, hq, hqp⟩
      obtain ⟨c, hc⟩ := (mkProj_eq_iff Z).mp hqp
      refine ⟨c⁻¹, q, hq, ?_⟩
      show smulPunct Z c⁻¹ q = p
      rw [← hc, ← smulPunct_mul, inv_mul_cancel, smulPunct_one]
    · rintro ⟨c, q, hq, hqp⟩
      refine ⟨q, hq, ?_⟩
      rw [← hqp]
      exact (mkProj_eq_iff Z).mpr
        ⟨c⁻¹, by rw [← smulPunct_mul, inv_mul_cancel, smulPunct_one]⟩
  rw [hpre]
  exact isOpen_iUnion fun c => isOpenMap_smulPunct Z c W hW

/-! ## A general topology lemma: restriction of an open map to a saturated set -/

/-- **A continuous open map restricted to a saturated subset is a quotient map.**  If `q : X → Y` is
continuous and open and `A = q ⁻¹' T`, then `q|_A : A → T` is a quotient map.  (The saturation is
what makes `q(A ∩ W₀) = q(A) ∩ q(W₀)`, hence `q|_A` open.) -/
theorem isQuotientMap_restrict_of_saturated {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {q : X → Y} (hc : Continuous q) (hopen : IsOpenMap q) {A : Set X} {T : Set Y}
    (hST : q '' A = T) (hA : q ⁻¹' T = A) :
    Topology.IsQuotientMap
      (fun a : A => (⟨q a.1, by rw [← hST]; exact Set.mem_image_of_mem q a.2⟩ : ↥T)) := by
  set f : ↥A → ↥T := fun a => ⟨q a.1, by rw [← hST]; exact Set.mem_image_of_mem q a.2⟩ with hf
  have hfcont : Continuous f := Continuous.subtype_mk (hc.comp continuous_subtype_val) _
  have hfsurj : Function.Surjective f := by
    rintro ⟨y, hy⟩
    rw [← hST] at hy
    obtain ⟨x, hxA, hxy⟩ := hy
    exact ⟨⟨x, hxA⟩, Subtype.ext hxy⟩
  refine IsOpenMap.isQuotientMap ?_ hfcont hfsurj
  intro s hs
  obtain ⟨W₀, hW₀, hWeq⟩ := isOpen_induced_iff.mp hs
  have hkey : f '' s = Subtype.val ⁻¹' (q '' W₀) := by
    ext y
    constructor
    · rintro ⟨a, ha, rfl⟩
      refine ⟨a.1, ?_, rfl⟩
      have h2 : a ∈ (Subtype.val : ↥A → X) ⁻¹' W₀ := by rw [hWeq]; exact ha
      exact h2
    · intro hy
      obtain ⟨x, hxW, hxq⟩ := hy
      have hxA : x ∈ A := by
        rw [← hA]
        change q x ∈ T
        rw [hxq]; exact y.2
      refine ⟨⟨x, hxA⟩, ?_, ?_⟩
      · rw [← hWeq]; exact hxW
      · exact Subtype.ext hxq
  rw [hkey]
  exact (hopen W₀ hW₀).preimage continuous_subtype_val

/-! ## The punctured total space of `Z|_U` is the saturated piece over `U` -/

theorem realification_comap_baseSet (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι)
    (U : Set B) (i : ι) :
    (realification (bundleComap Z (subtypeMap U))).baseSet i
      = (subtypeMap U) ⁻¹' (realification Z).baseSet i := by
  rw [realification_baseSet, bundleComap_baseSet, realification_baseSet]

theorem realification_comap_indexAt (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι)
    (U : Set B) (u : U) :
    (realification (bundleComap Z (subtypeMap U))).indexAt u = (realification Z).indexAt u.1 := by
  rw [realification_indexAt, bundleComap_indexAt, realification_indexAt]
  rfl

theorem realification_comap_coordChange (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι)
    (U : Set B) (i j : ι) (u : U) (v : EuclideanSpace ℂ (Fin m)) :
    (realification (bundleComap Z (subtypeMap U))).coordChange i j u v
      = (realification Z).coordChange i j u.1 v := by
  rw [realification_bundleComap]
  rfl

/-- The punctured total space of `Z|_U` identified with the fibre of `π` over `U`. -/
def comapZeroMap (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι) (U : Set B) :
    ↥(zeroComplement (realification (bundleComap Z (subtypeMap U)))) →
    ↥({x : ↥(zeroComplement (realification Z)) | x.1.proj ∈ U}) :=
  fun p => ⟨⟨⟨p.1.1.1, p.1.2⟩, p.2⟩, p.1.1.2⟩

/-- Its inverse. -/
def comapZeroInv (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι) (U : Set B) :
    ↥({x : ↥(zeroComplement (realification Z)) | x.1.proj ∈ U}) →
    ↥(zeroComplement (realification (bundleComap Z (subtypeMap U)))) :=
  fun x => ⟨⟨⟨x.1.1.1, x.2⟩, x.1.1.2⟩, x.1.2⟩

theorem continuous_comapZeroMap (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι)
    (U : Set B) : Continuous (comapZeroMap Z U) := by
  refine Continuous.subtype_mk (Continuous.subtype_mk ?_ (fun p => p.2)) (fun p => p.1.1.2)
  have hfin : (fun p : ↥(zeroComplement (realification (bundleComap Z (subtypeMap U)))) =>
      (⟨p.1.1.1, p.1.2⟩ : (realification Z).TotalSpace))
      = (⇑(totalMapR Z (subtypeMap U)) ∘ Subtype.val) := by
    funext p
    rw [Function.comp_apply, totalMapR_apply]
    rfl
  rw [hfin]
  exact (totalMapR Z (subtypeMap U)).continuous.comp continuous_subtype_val

theorem continuous_comapZeroInv (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι)
    (U : Set B) : Continuous (comapZeroInv Z U) := by
  have htot : Continuous (fun x : ↥({y : ↥(zeroComplement (realification Z)) | y.1.proj ∈ U}) =>
      (⟨⟨x.1.1.1, x.2⟩, x.1.1.2⟩ :
        (realification (bundleComap Z (subtypeMap U))).TotalSpace)) := by
    rw [continuous_iff_continuousAt]
    intro x
    set i := (realification Z).indexAt x.1.1.1 with hi
    set e₁ := ((realification (bundleComap Z (subtypeMap U))).localTriv i).toOpenPartialHomeomorph
      with he₁
    set e₂ := ((realification Z).localTriv i).toOpenPartialHomeomorph with he₂
    have hsrc : (fun y : ↥({z : ↥(zeroComplement (realification Z)) | z.1.proj ∈ U}) =>
        (⟨⟨y.1.1.1, y.2⟩, y.1.1.2⟩ :
          (realification (bundleComap Z (subtypeMap U))).TotalSpace)) ⁻¹' e₁.source ∈ 𝓝 x := by
      have hset : (fun y : ↥({z : ↥(zeroComplement (realification Z)) | z.1.proj ∈ U}) =>
          (⟨⟨y.1.1.1, y.2⟩, y.1.1.2⟩ :
            (realification (bundleComap Z (subtypeMap U))).TotalSpace)) ⁻¹' e₁.source
          = {y : ↥({z : ↥(zeroComplement (realification Z)) | z.1.proj ∈ U}) |
              y.1.1.1 ∈ (realification Z).baseSet i} := by
        ext y
        rw [he₁, Set.mem_preimage, VectorBundleCore.mem_localTriv_source]
        rw [realification_comap_baseSet]
        rfl
      rw [hset]
      exact (((realification Z).isOpen_baseSet i).preimage
        (((realification Z).continuous_proj.comp continuous_subtype_val).comp
          continuous_subtype_val)).mem_nhds ((realification Z).mem_baseSet_at x.1.1.1)
    rw [e₁.continuousAt_iff_continuousAt_comp_left hsrc]
    have hkey : ∀ y : ↥({z : ↥(zeroComplement (realification Z)) | z.1.proj ∈ U}),
        e₁ (⟨⟨y.1.1.1, y.2⟩, y.1.1.2⟩ :
            (realification (bundleComap Z (subtypeMap U))).TotalSpace)
          = (⟨⟨y.1.1.1, y.2⟩, (e₂ y.1.1).2⟩ : U × EuclideanSpace ℂ (Fin m)) := by
      intro y
      show ((realification (bundleComap Z (subtypeMap U))).localTriv i)
            (⟨⟨y.1.1.1, y.2⟩, y.1.1.2⟩ :
              (realification (bundleComap Z (subtypeMap U))).TotalSpace)
          = (⟨⟨y.1.1.1, y.2⟩, (((realification Z).localTriv i) y.1.1).2⟩ :
              U × EuclideanSpace ℂ (Fin m))
      rw [VectorBundleCore.localTriv_apply, VectorBundleCore.localTriv_apply]
      congr 1
      rw [realification_comap_indexAt, realification_comap_coordChange]
    have hga : Continuous (fun y : ↥({z : ↥(zeroComplement (realification Z)) | z.1.proj ∈ U}) =>
        (⟨y.1.1.1, y.2⟩ : U)) :=
      Continuous.subtype_mk (((realification Z).continuous_proj.comp continuous_subtype_val).comp
        continuous_subtype_val) (fun y => y.2)
    have hmem : x.1.1 ∈ e₂.source := by
      rw [he₂, VectorBundleCore.mem_localTriv_source, hi]
      exact (realification Z).mem_baseSet_at x.1.1.1
    have he₂at : ContinuousAt (fun y : ↥({z : ↥(zeroComplement (realification Z)) |
        z.1.proj ∈ U}) => e₂ y.1.1) x :=
      (e₂.continuousAt hmem).comp
        (f := fun y : ↥({z : ↥(zeroComplement (realification Z)) | z.1.proj ∈ U}) => y.1.1)
        (continuous_subtype_val.continuousAt.comp continuous_subtype_val.continuousAt)
    have hgb : ContinuousAt (fun y : ↥({z : ↥(zeroComplement (realification Z)) | z.1.proj ∈ U}) =>
        (e₂ y.1.1).2) x :=
      continuous_snd.continuousAt.comp
        (f := fun y : ↥({z : ↥(zeroComplement (realification Z)) | z.1.proj ∈ U}) => e₂ y.1.1) he₂at
    have h1 : ContinuousAt (fun y : ↥({z : ↥(zeroComplement (realification Z)) |
        z.1.proj ∈ U}) =>
        (⟨⟨y.1.1.1, y.2⟩, (e₂ y.1.1).2⟩ : U × EuclideanSpace ℂ (Fin m))) x :=
      (hga.continuousAt).prodMk hgb
    exact h1.congr (Filter.Eventually.of_forall fun y => (hkey y).symm)
  exact Continuous.subtype_mk htot (fun x => x.1.2)

/-- **The punctured total space of the restricted bundle is the part of the punctured total space
of `Z` lying over `U`**: the evident identification is a homeomorphism, and it is compatible with
the `ℂˣ`-action (`smulPunct`). -/
def punctHomeo (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι) (U : Set B) :
    ↥(zeroComplement (realification (bundleComap Z (subtypeMap U)))) ≃ₜ
    ↥({x : ↥(zeroComplement (realification Z)) | x.1.proj ∈ U}) where
  toFun := comapZeroMap Z U
  invFun := comapZeroInv Z U
  left_inv := fun _ => rfl
  right_inv := fun _ => rfl
  continuous_toFun := continuous_comapZeroMap Z U
  continuous_invFun := continuous_comapZeroInv Z U

theorem exists_homeo_zeroComplement_comap_subtype
    (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι) (U : Set B) :
    ∃ h : ↥(zeroComplement (realification (bundleComap Z (subtypeMap U)))) ≃ₜ
          ↥({x : ↥(zeroComplement (realification Z)) | x.1.proj ∈ U}),
      ∀ (c : ℂˣ) (x : ↥(zeroComplement (realification (bundleComap Z (subtypeMap U))))),
        h (smulPunct (bundleComap Z (subtypeMap U)) c x) = ⟨smulPunct Z c (h x).1, (h x).2⟩ :=
  ⟨punctHomeo Z U, fun _ _ => rfl⟩

/-! ## The main identification -/

theorem nonempty_homeo_projSpace_bundleComap_subtype {B : Type} [TopologicalSpace B]
    {ι : Type} {m : ℕ} (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι) (U : Set B) :
    Nonempty (Work.LerayHirsch.ProjSpace
        (Work.Thom.bundleComap Z (Work.Thom.subtypeMap U)) ≃ₜ
      ↥(Work.LerayHirsch.projMap Z ⁻¹' U)) := by
  obtain ⟨h, hsmul⟩ := exists_homeo_zeroComplement_comap_subtype Z U
  let A : Set ↥(zeroComplement (realification Z)) := {x | x.1.proj ∈ U}
  let T : Set (ProjSpace Z) := projMap Z ⁻¹' U
  have hT : (mkProj Z) '' A = T := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact hx
    · intro hy
      obtain ⟨x, hx⟩ := surjective_mkProj Z y
      refine ⟨x, ?_, hx⟩
      have h3 : (projMap Z) (mkProj Z x) ∈ U := by rw [hx]; exact hy
      exact h3
  let Φ : ↥A → ↥T := fun a => ⟨mkProj Z a.1, by rw [← hT]; exact Set.mem_image_of_mem (mkProj Z) a.2⟩
  have hΦq : Topology.IsQuotientMap Φ :=
    isQuotientMap_restrict_of_saturated (continuous_mkProj Z) (isOpenMap_mkProj Z) hT (by rfl)
  let f : ↥(zeroComplement (realification (bundleComap Z (subtypeMap U)))) → ↥T :=
    fun x => Φ (h x)
  have hfcont : Continuous f := hΦq.continuous.comp h.continuous
  have hfw : ∀ a b : ↥(zeroComplement (realification (bundleComap Z (subtypeMap U)))),
      projRel (bundleComap Z (subtypeMap U)) a b → f a = f b := by
    intro a b hab
    obtain ⟨c, hc⟩ := hab
    have h1 : h a = ⟨smulPunct Z c (h b).1, (h b).2⟩ := by
      rw [← hc]; exact hsmul c b
    show Φ (h a) = Φ (h b)
    rw [h1]
    apply Subtype.ext
    show mkProj Z (smulPunct Z c (h b).1) = mkProj Z (h b).1
    exact (mkProj_eq_iff Z).mpr ⟨c, rfl⟩
  let φ : ProjSpace (bundleComap Z (subtypeMap U)) → ↥T := Quotient.lift f hfw
  have hφcont : Continuous φ := Continuous.quotient_lift hfcont hfw
  have hφinj : Function.Injective φ := by
    intro p q hpq
    obtain ⟨a, rfl⟩ := surjective_mkProj (bundleComap Z (subtypeMap U)) p
    obtain ⟨b, rfl⟩ := surjective_mkProj (bundleComap Z (subtypeMap U)) q
    rw [mkProj_eq_iff]
    rw [show φ (mkProj (bundleComap Z (subtypeMap U)) a) = f a
          from Quotient.lift_mk (s := projSetoid (bundleComap Z (subtypeMap U))) f hfw a,
        show φ (mkProj (bundleComap Z (subtypeMap U)) b) = f b
          from Quotient.lift_mk (s := projSetoid (bundleComap Z (subtypeMap U))) f hfw b] at hpq
    have h1 : mkProj Z (h a).1 = mkProj Z (h b).1 := Subtype.ext_iff.mp hpq
    obtain ⟨c, hc⟩ := (mkProj_eq_iff Z).mp h1
    refine ⟨c, ?_⟩
    apply h.injective
    rw [hsmul c b]
    exact Subtype.ext hc
  have hφsurj : Function.Surjective φ := by
    rintro ⟨y, hy⟩
    obtain ⟨x, hx⟩ := surjective_mkProj Z y
    have hxA : x ∈ A := by
      show (projMap Z) (mkProj Z x) ∈ U
      rw [hx]; exact hy
    refine ⟨mkProj (bundleComap Z (subtypeMap U)) (h.symm ⟨x, hxA⟩), ?_⟩
    rw [show φ (mkProj (bundleComap Z (subtypeMap U)) (h.symm ⟨x, hxA⟩)) = f (h.symm ⟨x, hxA⟩)
          from Quotient.lift_mk (s := projSetoid (bundleComap Z (subtypeMap U))) f hfw _]
    apply Subtype.ext
    show mkProj Z (h (h.symm ⟨x, hxA⟩)).1 = y
    rw [Homeomorph.apply_symm_apply]
    exact hx
  have hφq : Topology.IsQuotientMap φ := by
    have h2 : Topology.IsQuotientMap (φ ∘ mkProj (bundleComap Z (subtypeMap U))) := by
      have heq : (φ ∘ mkProj (bundleComap Z (subtypeMap U))) = f := by
        funext x
        exact Quotient.lift_mk (s := projSetoid (bundleComap Z (subtypeMap U))) f hfw x
      rw [heq]
      exact hΦq.comp h.isQuotientMap
    exact Topology.IsQuotientMap.of_comp_isQuotientMap isQuotientMap_quotient_mk' h2
  exact ⟨(Equiv.ofBijective φ ⟨hφinj, hφsurj⟩).toHomeomorph
    (fun _ => hφq.isCoinducing.isOpen_preimage)⟩

end

end Work.LerayHirsch
