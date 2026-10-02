import Mathlib
import Submission.Work.LerayHirsch.Splitting

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option linter.unusedSectionVars false

/-!
# The tautological embedding `ℓ ↪ π^*E`: core definitions

Let `Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι` be a complex gluing-data bundle,
`P(E) = Work.LerayHirsch.ProjSpace Z` its projectivisation, `ℓ = Work.LerayHirsch.tautLine Z` the
tautological line bundle over `P(E)` and `π^*E` the pullback of `Z` along `π : P(E) → B`.

A bundle map `ℓ → π^*E` is a fibrewise linear family of maps `LineFibre = ℂ¹ → ℂ^m`, i.e. a function
`P(E) → (LineFibre →ₗ[ℂ] ℂ^m)`: the fibre coordinate is *not* attached to a chart, so the
fibrewise maps must be assembled from local data.  This module supplies

* `normFun` / `normLift` — the global vector `W x ∈ ℂ^m` defined from a representative `p` of
  `x = [p]` by normalising `p` in the preferred chart `(tautLine Z).indexAt x` of the tautological
  line bundle: `W x = (chartCoord Z i p k)⁻¹ • p`;
* `tautHomVec` — the resulting linear map `LineFibre →ₗ[ℂ] ℂ^m`, `t ↦ (t 0) • W x`, which is
  fibrewise injective (`tautHomVec_injective`);
* `chartRatioVec` — the local matrix of the bundle map in a chart `(i₁,k₁)` of `ℓ` and a chart `i`
  of `Z`, together with its continuity (`continuousOn_chartRatioVec`);
* `coordChange_normLift` / `tautEmbedTotal_localTriv` — the *key identity* identifying the
  trivialisation coordinates of the induced map of total spaces, which is what makes the
  continuity proof of `Work.LerayHirsch.tautologicalEmbedding` possible.
-/

namespace Work.LerayHirsch

open Work.TangentClasses Work.Thom
open Filter
open scoped Topology

/-! The declarations of this module live in their own namespace so that the names below cannot
clash with sibling files of the Leray–Hirsch area. -/

namespace TautEmbed

noncomputable section

variable {B : Type} [TopologicalSpace B] {ι : Type} {m : ℕ}

/-! ## Elementary lemmas -/

/-- The `k`-th coordinate of a `ℂ`-multiple of a vector of the Euclidean space. -/
theorem smul_apply_eucl {m : ℕ} (c : ℂ) (v : EuclideanSpace ℂ (Fin m)) (k : Fin m) :
    (c • v) k = c * v k := by simp

/-- A vector of `ℂ^m` with all coordinates zero is zero. -/
theorem eq_zero_of_forall_apply_eq_zero {m : ℕ} {v : EuclideanSpace ℂ (Fin m)}
    (h : ∀ k, v k = 0) : v = 0 := by
  ext k
  simpa using h k

/-- A nonzero vector of `ℂ^m` has a nonzero coordinate. -/
theorem exists_coord_ne_zero {m : ℕ} (v : EuclideanSpace ℂ (Fin m)) (hv : v ≠ 0) :
    ∃ k : Fin m, v k ≠ 0 := by
  by_contra h
  push Not at h
  exact hv (eq_zero_of_forall_apply_eq_zero h)

/-- Multiplication by a nonzero vector of `ℂ^m` is injective on scalars. -/
theorem smul_left_injective_of_ne_zero {m : ℕ} {w : EuclideanSpace ℂ (Fin m)} (hw : w ≠ 0) :
    Function.Injective (fun c : ℂ => c • w) := by
  intro c d hcd
  obtain ⟨k, hk⟩ := exists_coord_ne_zero w hw
  have h := congrArg (fun v : EuclideanSpace ℂ (Fin m) => v k) hcd
  rw [smul_apply_eucl, smul_apply_eucl] at h
  exact mul_right_cancel₀ hk h

/-- The chart coordinates of a point in its *preferred* chart are its raw coordinates. -/
theorem chartCoord_indexAt (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι)
    (p : ↥(zeroComplement (realification Z))) :
    chartCoord Z (Z.indexAt p.1.proj) p = (show EuclideanSpace ℂ (Fin m) from p.1.2) := by
  rw [chartCoord_def]
  exact Z.coordChange_self _ _ (Z.mem_baseSet_at _) _

/-! ## The normalisation of a representative of a point of `P(E)` -/

/-- The vector of `ℂ^m` obtained from a representative `p` of a point `x ∈ P(E)` by normalising in
the preferred chart `(tautLine Z).indexAt x` of the tautological line bundle: `p` is rescaled so
that its `i`-th chart `k`-th coordinate (in the preferred chart `(i,k)` of `ℓ` at `x`) becomes `1`.
The value is independent of the representative (`normFun_smulPunct`), hence descends to `P(E)`
(`normLift`). -/
noncomputable def normFun (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι)
    (p : ↥(zeroComplement (realification Z))) : EuclideanSpace ℂ (Fin m) :=
  let ik := (tautLine Z).indexAt (mkProj Z p)
  (chartCoord Z ik.1 p ik.2)⁻¹ • chartCoord Z (Z.indexAt p.1.proj) p

/-- The normalising coordinate of `normFun` is nonzero on `E∖0`. -/
theorem chartCoord_indexAt_ne_zero (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι)
    (p : ↥(zeroComplement (realification Z))) :
    chartCoord Z ((tautLine Z).indexAt (mkProj Z p)).1 p
      ((tautLine Z).indexAt (mkProj Z p)).2 ≠ 0 :=
  ((mem_tautBaseSetProj_mk Z ((tautLine Z).indexAt (mkProj Z p)) p).mp
    ((tautLine Z).mem_baseSet_at (mkProj Z p))).2

/-- Any nonzero multiple of the raw vector is nonzero; used for `normLift_ne_zero`. -/
theorem normFun_ne_zero (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι)
    (p : ↥(zeroComplement (realification Z))) : normFun Z p ≠ 0 := by
  simp only [normFun]
  refine smul_ne_zero ?_ ?_
  · exact inv_ne_zero (chartCoord_indexAt_ne_zero Z p)
  · intro h
    rw [chartCoord_indexAt] at h
    exact (mem_zeroComplement _).mp p.2 h

/-- **`normFun` is invariant under the `ℂˣ`-action** on `E∖0`. -/
theorem normFun_smulPunct (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι) (c : ℂˣ)
    (p : ↥(zeroComplement (realification Z))) :
    normFun Z (smulPunct Z c p) = normFun Z p := by
  have hx : mkProj Z (smulPunct Z c p) = mkProj Z p := by
    rw [mkProj_eq_iff]; exact ⟨c, rfl⟩
  have h2 : chartCoord Z (Z.indexAt (smulPunct Z c p).1.proj) (smulPunct Z c p)
      = (c : ℂ) • chartCoord Z (Z.indexAt p.1.proj) p := by
    rw [smulPunct_proj, chartCoord_smulPunct]
  have h1 : chartCoord Z ((tautLine Z).indexAt (mkProj Z p)).1 (smulPunct Z c p)
        ((tautLine Z).indexAt (mkProj Z p)).2
      = (c : ℂ) * chartCoord Z ((tautLine Z).indexAt (mkProj Z p)).1 p
          ((tautLine Z).indexAt (mkProj Z p)).2 := by
    rw [chartCoord_smulPunct, smul_apply_eucl]
  simp only [normFun, hx]
  rw [h1, h2, smul_smul]
  congr 1
  field_simp

/-- **The descended normalisation** `W : P(E) → ℂ^m`.  Over `x = [p]` its value spans the line that
the tautological line bundle parameterises. -/
noncomputable def normLift (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι) :
    ProjSpace Z → EuclideanSpace ℂ (Fin m) :=
  Quotient.lift (normFun Z) (fun a b h => by
    obtain ⟨c, hc⟩ := h
    rw [← hc, normFun_smulPunct Z c b])

@[simp] theorem normLift_mk (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι)
    (p : ↥(zeroComplement (realification Z))) :
    normLift Z (mkProj Z p) = normFun Z p := rfl

/-- **The descended normalisation is nowhere zero**. -/
theorem normLift_ne_zero (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι)
    (x : ProjSpace Z) : normLift Z x ≠ 0 := by
  obtain ⟨p, rfl⟩ := surjective_mkProj Z x
  rw [normLift_mk]
  exact normFun_ne_zero Z p

/-! ## The fibrewise linear maps -/

/-- The linear map `LineFibre →ₗ[ℂ] ℂ^m` determined by a vector `w ∈ ℂ^m`: `t ↦ (t 0) • w`
(the identification `LineFibre = ℂ¹ ≅ ℂ` followed by the inclusion of the line `ℂ·w`). -/
def tautHomVec {m : ℕ} (w : EuclideanSpace ℂ (Fin m)) :
    EuclideanSpace ℂ (Fin 1) →ₗ[ℂ] EuclideanSpace ℂ (Fin m) :=
  { toFun := fun t => (t 0) • w
    map_add' := fun a b => by
      rw [WithLp.ofLp_add, Pi.add_apply, add_smul]
    map_smul' := fun c a => by
      rw [WithLp.ofLp_smul, Pi.smul_apply, RingHom.id_apply, smul_assoc] }

@[simp] theorem tautHomVec_apply {m : ℕ} (w : EuclideanSpace ℂ (Fin m))
    (t : EuclideanSpace ℂ (Fin 1)) : tautHomVec w t = (t 0) • w := rfl

/-- The vector `t ↦ (t 0) • w` is injective as soon as `w ≠ 0`. -/
theorem tautHomVec_injective {m : ℕ} {w : EuclideanSpace ℂ (Fin m)} (hw : w ≠ 0) :
    Function.Injective (tautHomVec w) := by
  intro a b hab
  rw [tautHomVec_apply, tautHomVec_apply] at hab
  have h0 : a 0 = b 0 := smul_left_injective_of_ne_zero hw hab
  ext i
  fin_cases i
  exact h0

/-! ## The local matrix of the bundle map -/

/-- The local matrix of the tautological embedding in the source chart `(i₁,k₁)` of `ℓ` and the
target chart `i` of `Z`: the vector proportional to `chartCoord Z i p` whose `k₁`-th coordinate in
the chart `i₁` is `1`.  It descends to `P(E)` (`chartRatioVec`). -/
noncomputable def chartRatioRaw (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι)
    (i₁ : ι) (k₁ : Fin m) (i : ι) (p : ↥(zeroComplement (realification Z))) :
    EuclideanSpace ℂ (Fin m) :=
  if chartCoord Z i₁ p k₁ ≠ 0 then (chartCoord Z i₁ p k₁)⁻¹ • chartCoord Z i p else 0

/-- `chartRatioRaw` is invariant under the `ℂˣ`-action. -/
theorem chartRatioRaw_smulPunct (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι)
    (i₁ : ι) (k₁ : Fin m) (i : ι) (c : ℂˣ) (p : ↥(zeroComplement (realification Z))) :
    chartRatioRaw Z i₁ k₁ i (smulPunct Z c p) = chartRatioRaw Z i₁ k₁ i p := by
  have hiff : chartCoord Z i₁ (smulPunct Z c p) k₁ ≠ 0 ↔ chartCoord Z i₁ p k₁ ≠ 0 := by
    rw [chartCoord_smulPunct]
    constructor <;> intro h <;> simp only [smul_apply_eucl] at *
    · exact fun h0 => h (by rw [h0, mul_zero])
    · exact mul_ne_zero (Units.ne_zero c) h
  rw [chartRatioRaw, chartRatioRaw]
  by_cases h : chartCoord Z i₁ p k₁ = 0
  · rw [if_neg (by simpa [h] using hiff.not.mpr), if_neg (by simpa using h)]
  · rw [if_pos h, if_pos (hiff.mpr h), chartCoord_smulPunct, chartCoord_smulPunct]
    simp only [smul_apply_eucl]
    rw [smul_smul]
    congr 1
    field_simp

/-- **The local matrix of the tautological embedding**, as a function on `P(E)`. -/
noncomputable def chartRatioVec (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι)
    (i₁ : ι) (k₁ : Fin m) (i : ι) : ProjSpace Z → EuclideanSpace ℂ (Fin m) :=
  Quotient.lift (chartRatioRaw Z i₁ k₁ i) (fun a b h => by
    obtain ⟨c, hc⟩ := h
    rw [← hc, chartRatioRaw_smulPunct Z i₁ k₁ i c b])

@[simp] theorem chartRatioVec_mk (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι)
    (i₁ : ι) (k₁ : Fin m) (i : ι) (p : ↥(zeroComplement (realification Z))) :
    chartRatioVec Z i₁ k₁ i (mkProj Z p) = chartRatioRaw Z i₁ k₁ i p := rfl

/-- The preimage under `mkProj` of the preimage of `Z.baseSet i` under `π`. -/
theorem preimage_projMap (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι) (s : Set B) :
    mkProj Z ⁻¹' (projMap Z ⁻¹' s) = {p | p.1.proj ∈ s} := by
  ext p
  simp [projMap_mkProj]

/-- **Continuity of the local matrix**, on the chart `(i₁,k₁)` of `ℓ` intersected with the
preimage of the chart `i` of `Z`. -/
theorem continuousOn_chartRatioVec (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι)
    (i₁ : ι) (k₁ : Fin m) (i : ι) :
    ContinuousOn (chartRatioVec Z i₁ k₁ i)
      (tautBaseSetProj Z (i₁, k₁) ∩ projMap Z ⁻¹' Z.baseSet i) := by
  have hq : Topology.IsQuotientMap (mkProj Z) := isQuotientMap_quotient_mk'
  refine (Topology.IsQuotientMap.continuousOn_isOpen_iff hq ?_).mpr ?_
  · exact (isOpen_tautBaseSetProj Z (i₁, k₁)).inter
      ((Z.isOpen_baseSet i).preimage (projMap Z).continuous)
  · rw [Set.preimage_inter, preimage_tautBaseSetProj, preimage_projMap]
    have hc1 : ContinuousOn
        (fun p : ↥(zeroComplement (realification Z)) => (chartCoord Z i₁ p k₁)⁻¹)
        (tautBaseSet Z i₁ k₁ ∩ {p | p.1.proj ∈ Z.baseSet i}) := by
      refine (((by fun_prop : Continuous (fun v : EuclideanSpace ℂ (Fin m) => v k₁)).comp_continuousOn
        ((continuousOn_chartCoord Z i₁).mono (fun p hp => hp.1.1)))).inv₀ ?_
      intro p hp
      exact hp.1.2
    have hc2 : ContinuousOn (fun p : ↥(zeroComplement (realification Z)) => chartCoord Z i p)
        (tautBaseSet Z i₁ k₁ ∩ {p | p.1.proj ∈ Z.baseSet i}) :=
      (continuousOn_chartCoord Z i).mono (fun p hp => hp.2)
    refine (hc1.smul hc2).congr (fun p hp => ?_)
    rw [Function.comp_apply, chartRatioVec_mk, chartRatioRaw, if_pos hp.1.2]
    rfl

/-! ## The key identity -/

/-- **Key identity, on representatives**: the preferred-chart normalisation `normFun` and the local
matrix `chartRatioRaw` differ by the transition function of the tautological line bundle. -/
theorem coordChange_normFun (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι)
    (i₁ : ι) (k₁ : Fin m) (i : ι) (p : ↥(zeroComplement (realification Z)))
    (h1 : mkProj Z p ∈ tautBaseSetProj Z (i₁, k₁)) (_h2 : p.1.proj ∈ Z.baseSet i) :
    Z.coordChange (Z.indexAt p.1.proj) i p.1.proj (normFun Z p)
      = tautCoeffLift Z ((tautLine Z).indexAt (mkProj Z p)) (i₁, k₁) (mkProj Z p)
        • chartRatioRaw Z i₁ k₁ i p := by
  have hp : p ∈ tautBaseSet Z i₁ k₁ := (mem_tautBaseSetProj_mk Z (i₁, k₁) p).mp h1
  have hk₁ : chartCoord Z i₁ p k₁ ≠ 0 := hp.2
  simp only [normFun]
  rw [map_smul, chartCoord_indexAt, ← chartCoord_def]
  rw [tautLine_coordChange_eq_ratio Z _ _ p (chartCoord_indexAt_ne_zero Z p)]
  rw [chartRatioRaw, if_pos hk₁]
  rw [smul_smul]
  congr 1
  field_simp

/-- **The key identity**: the transition function of `ℓ` from the preferred chart at `x` to the
chart `(i₁,k₁)` is exactly the change of coordinates between the preferred-chart normalisation and
the local matrix of the bundle map. -/
theorem coordChange_normLift (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι)
    (i₁ : ι) (k₁ : Fin m) (i : ι) (x : ProjSpace Z)
    (h1 : x ∈ tautBaseSetProj Z (i₁, k₁)) (h2 : projMap Z x ∈ Z.baseSet i) :
    Z.coordChange (Z.indexAt (projMap Z x)) i (projMap Z x) (normLift Z x)
      = tautCoeffLift Z ((tautLine Z).indexAt x) (i₁, k₁) x • chartRatioVec Z i₁ k₁ i x := by
  obtain ⟨p, rfl⟩ := surjective_mkProj Z x
  rw [projMap_mkProj] at h2 ⊢
  exact coordChange_normFun Z i₁ k₁ i p h1 h2

/-! ## The induced map of total spaces -/

/-- **The induced map of total spaces** of the fibrewise linear family `x ↦ tautHomVec (normLift Z x)`. -/
def tautEmbedTotal (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι) :
    (tautLine Z).TotalSpace → (bundleComap Z (projMap Z)).TotalSpace :=
  fun q => ⟨q.1, tautHomVec (normLift Z q.1) q.2⟩

@[simp] theorem tautEmbedTotal_apply (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι)
    (q : (tautLine Z).TotalSpace) :
    tautEmbedTotal Z q = ⟨q.1, tautHomVec (normLift Z q.1) q.2⟩ := rfl

/-- **The local trivialisation coordinates of the induced map of total spaces**: in the source chart
`(i₁,k₁)` of `ℓ` and the target chart `i` of `Z`, the map is `(x,t) ↦ (x, (t 0) • M(x))` with `M`
the local matrix `chartRatioVec`. -/
theorem tautEmbedTotal_localTriv (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι)
    (i₁ : ι) (k₁ : Fin m) (i : ι) (q : (tautLine Z).TotalSpace)
    (h1 : q.1 ∈ tautBaseSetProj Z (i₁, k₁)) (h2 : projMap Z q.1 ∈ Z.baseSet i) :
    (bundleComap Z (projMap Z)).localTriv i (tautEmbedTotal Z q)
      = ⟨q.1, ((tautLine Z).localTriv (i₁, k₁) q).2 0 • chartRatioVec Z i₁ k₁ i q.1⟩ := by
  rw [VectorBundleCore.localTriv_apply, tautEmbedTotal_apply, tautHomVec_apply]
  rw [show (bundleComap Z (projMap Z)).indexAt q.1 = Z.indexAt (projMap Z q.1) from rfl]
  rw [show (bundleComap Z (projMap Z)).coordChange (Z.indexAt (projMap Z q.1)) i q.1
      = Z.coordChange (Z.indexAt (projMap Z q.1)) i (projMap Z q.1) from rfl]
  rw [map_smul, coordChange_normLift Z i₁ k₁ i q.1 h1 h2]
  rw [VectorBundleCore.localTriv_apply]
  rw [show (tautLine Z).coordChange ((tautLine Z).indexAt q.1) (i₁, k₁) q.1 q.2
      = tautCoeffLift Z ((tautLine Z).indexAt q.1) (i₁, k₁) q.1 • q.2 from
    tautLine_coordChange_apply Z _ _ _ _]
  rw [smul_smul]
  congr 1
  rw [smul_apply_eucl, mul_comm]

theorem continuous_tautEmbedTotal (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι) :
    Continuous (tautEmbedTotal Z) := by
  rw [continuous_iff_continuousAt]
  intro q
  set ik : ι × Fin m := (tautLine Z).indexAt q.1 with hik
  set i : ι := Z.indexAt (projMap Z q.1) with hi
  have hq1 : q.1 ∈ tautBaseSetProj Z ik := (tautLine Z).mem_baseSet_at q.1
  have hq2 : projMap Z q.1 ∈ Z.baseSet i := Z.mem_baseSet_at _
  refine ((bundleComap Z (projMap Z)).localTriv i).continuousAt_of_comp_left ?_ ?_ ?_
  · have hcomp : ((bundleComap Z (projMap Z)).proj ∘ tautEmbedTotal Z) = (tautLine Z).proj := rfl
    rw [hcomp]
    exact (tautLine Z).continuous_proj.continuousAt
  · rw [← VectorBundleCore.baseSet_at, bundleComap_baseSet]
    exact hq2
  · set src := (tautLine Z).localTriv ik with hsrc
    have hsrc_q : q ∈ src.source := by
      rw [hsrc, VectorBundleCore.mem_localTriv_source]
      exact hq1
    have hsrc_fst : (src q).1 = q.1 := src.coe_fst hsrc_q
    have hmem : tautBaseSetProj Z ik ∩ projMap Z ⁻¹' Z.baseSet i ∈ 𝓝 q.1 :=
      ((isOpen_tautBaseSetProj Z ik).inter
        ((Z.isOpen_baseSet i).preimage (projMap Z).continuous)).mem_nhds ⟨hq1, hq2⟩
    have hmem' : tautBaseSetProj Z ik ∩ projMap Z ⁻¹' Z.baseSet i ∈ 𝓝 (src q).1 := by
      rw [hsrc_fst]; exact hmem
    have hV : ContinuousAt (fun z : ProjSpace Z × EuclideanSpace ℂ (Fin 1) =>
        chartRatioVec Z ik.1 ik.2 i z.1) (src q) :=
      ((continuousOn_chartRatioVec Z ik.1 ik.2 i).continuousAt hmem').comp continuousAt_fst
    have hC : ContinuousAt (fun z : ProjSpace Z × EuclideanSpace ℂ (Fin 1) => z.2 0) (src q) :=
      ((by fun_prop : Continuous (fun t : EuclideanSpace ℂ (Fin 1) => t 0))).continuousAt.comp
        continuousAt_snd
    have hΨ : ContinuousAt (fun z : ProjSpace Z × EuclideanSpace ℂ (Fin 1) =>
        (z.1, (z.2 0) • chartRatioVec Z ik.1 ik.2 i z.1)) (src q) :=
      ContinuousAt.prodMk continuousAt_fst (hC.smul hV)
    have hsrcc : ContinuousAt src q := src.toOpenPartialHomeomorph.continuousAt hsrc_q
    refine ContinuousAt.congr (hΨ.comp hsrcc) ?_
    have hU : ∀ᶠ q' in 𝓝 q, q'.1 ∈ tautBaseSetProj Z ik :=
      (tautLine Z).continuous_proj.continuousAt.preimage_mem_nhds
        ((isOpen_tautBaseSetProj Z ik).mem_nhds hq1)
    have hW : ∀ᶠ q' in 𝓝 q, projMap Z q'.1 ∈ Z.baseSet i :=
      (tautLine Z).continuous_proj.continuousAt.preimage_mem_nhds
        (((Z.isOpen_baseSet i).preimage (projMap Z).continuous).mem_nhds hq2)
    filter_upwards [hU, hW] with q' h1 h2
    rw [Function.comp_apply, Function.comp_apply,
      tautEmbedTotal_localTriv Z ik.1 ik.2 i q' h1 h2]
    exact Prod.ext rfl rfl

/-! ## The bundle map and the tautological embedding -/

/-- **The tautological embedding, as a bundle map** `ℓ → π^*E`: the fibrewise linear map
`t ↦ (t 0) • W x`. -/
def tautEmbedMap (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι) :
    BundleMap (tautLine Z) (bundleComap Z (projMap Z)) where
  hom := fun x => tautHomVec (normLift Z x)
  continuous_hom := continuous_tautEmbedTotal Z

/-- **The requested statement**: the tautological line bundle embeds fibrewise injectively into
`π^*E`. -/
theorem tautEmbedMap_injective {ι : Type} [Fintype ι]
    (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι) :
    TautologicalEmbedding Z :=
  ⟨tautEmbedMap Z, fun x => tautHomVec_injective (normLift_ne_zero Z x)⟩

end

end TautEmbed

end Work.LerayHirsch