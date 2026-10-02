import Mathlib
import Submission.Work.LerayHirsch.Punctum
import Submission.Work.LerayHirsch.fibreMap_bijective

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

/-!
# The fibre of the projectivisation is `ℂP^{m-1}`: the homeomorphism

`Work.LerayHirsch.fibreMap_bijective` shows that the map
`fibreMap Z b : ℙ ℂ (ℂ^m) → ProjFibre Z b` is a bijection.  This module upgrades it to a
homeomorphism: the fibre `π^{-1}(b)` of `π : P(E) → B` carries the subspace topology of the
quotient `P(E) = (E∖0)/ℂˣ`, and that subspace topology is exactly the quotient topology of the
punctured fibre `ℂ^m∖0` by the `ℂˣ`-action — equivalently, of `ℙ ℂ (ℂ^m)`.

The two maps are

* `fibreMap Z b` (the class of the fibre vector `(b,v)`), whose continuity is reduced through the
  quotient map `{v : ℂ^m // v ≠ 0} → ℙ ℂ (ℂ^m)` to the continuity of the section
  `v ↦ (b,v)` of the bundle (Mathlib's `FiberBundleCore.continuous_totalSpaceMk`);
* `x ↦ projClass Z x.1` (`psi`), the class of the second coordinate of a lift.  Its continuity is
  the substantive point: for an open `V ⊆ ℙ ℂ (ℂ^m)` and a lift `p₀` of `x₀` we take a
  `ℂˣ`-saturated open `D ⊆ ℂ^m` with `[v] ∈ V ↔ v ∈ D` (`exists_saturated_open_class`), and the
  saturated open set
  `Ω = {p : (localTriv i p).2 ∈ D} ⊆ E∖0` (with `i = indexAt b`);  its image `mkProj Z '' Ω` is
  open in `P(E)` and its trace on the fibre is exactly `psi ⁻¹' V`.  This is where the `ℂˣ`-action
  on `E∖0` enters: `mkProj` is an open map because the action is by homeomorphisms
  (`isOpen_image_mkProj`), and `Ω` is saturated because the chart coordinate is
  `ℂˣ`-equivariant (`chartCoord_smulPunct`).
-/

namespace Work.LerayHirsch

open Work.TangentClasses Work.Thom

open scoped LinearAlgebra.Projectivization

noncomputable section

variable {B : Type} [TopologicalSpace B] {ι : Type} {m : ℕ}

/-! ## The chart coordinate of a complex bundle and of its realification -/

/-- The second component of the preferred trivialisation of the realification of `Z` is the chart
coordinate `chartCoord` of `Z`: the two bundles have the same transition functions. -/
theorem realification_localTriv_snd (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι) (i : ι)
    (p : ↥(zeroComplement (realification Z))) :
    ((realification Z).localTriv i p).2 = chartCoord Z i p := by
  rw [VectorBundleCore.localTriv_apply, chartCoord_def, realification_indexAt,
    realification_coordChange]

/-- Over the fibre of `π` at `b`, the chart coordinate for the chart `indexAt b` is the fibre
coordinate itself: the transition function is the identity there. -/
theorem chartCoord_indexAt_eq_snd (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι)
    (b : B) (p : ↥(zeroComplement (realification Z))) (hp : p.1.proj = b) :
    chartCoord Z ((realification Z).indexAt b) p = p.1.2 := by
  rw [chartCoord_def, hp, realification_indexAt]
  exact Z.coordChange_self (Z.indexAt b) b (Z.mem_baseSet_at b) p.1.2

/-! ## A `ℂˣ`-saturated open set of the model fibre -/

/-- Every open subset `V` of `ℙ ℂ (ℂ^m)` is, on the punctured model fibre, the saturation of an
open subset: there is an open **`ℂˣ`-saturated** `D ⊆ ℂ^m` with `[v] ∈ V ↔ v ∈ D` for every
`v ≠ 0`.  (`D` is the `ℂˣ`-saturation of an ambient open set representing `V`.) -/
theorem exists_saturated_open_class {m : ℕ}
    (V : Set (ℙ ℂ (EuclideanSpace ℂ (Fin m)))) (hV : IsOpen V) :
    ∃ D : Set (EuclideanSpace ℂ (Fin m)), IsOpen D ∧
      (∀ (c : ℂˣ) (v : EuclideanSpace ℂ (Fin m)), (c : ℂ) • v ∈ D ↔ v ∈ D) ∧
      (∀ (v : EuclideanSpace ℂ (Fin m)) (hv : v ≠ 0),
        Projectivization.mk ℂ v hv ∈ V ↔ v ∈ D) := by
  have hmk : Continuous (fun v : {v : EuclideanSpace ℂ (Fin m) // v ≠ 0} =>
      Projectivization.mk ℂ v.1 v.2) := by
    change Continuous (Quotient.mk'' : {v : EuclideanSpace ℂ (Fin m) // v ≠ 0} →
      Quotient (projectivizationSetoid ℂ (EuclideanSpace ℂ (Fin m))))
    exact continuous_quotient_mk'
  have hDsub : IsOpen ((fun v : {v : EuclideanSpace ℂ (Fin m) // v ≠ 0} =>
      Projectivization.mk ℂ v.1 v.2) ⁻¹' V) := hV.preimage hmk
  obtain ⟨D₀, hD₀open, hD₀⟩ := (isOpen_induced_iff (f := Subtype.val)).mp hDsub
  have hD₀' : ∀ (v : EuclideanSpace ℂ (Fin m)) (hv : v ≠ 0),
      v ∈ D₀ ↔ Projectivization.mk ℂ v hv ∈ V := by
    intro v hv
    have h := congrArg (fun s : Set {v : EuclideanSpace ℂ (Fin m) // v ≠ 0} =>
      (⟨v, hv⟩ ∈ s)) hD₀
    simpa using h
  refine ⟨⋃ c : ℂˣ, (fun v : EuclideanSpace ℂ (Fin m) => (c : ℂ) • v) ⁻¹' D₀, ?_, ?_, ?_⟩
  · exact isOpen_iUnion fun c => hD₀open.preimage (continuous_const_smul (c : ℂ))
  · intro c v
    simp only [Set.mem_iUnion, Set.mem_preimage]
    constructor
    · rintro ⟨d, hd⟩
      refine ⟨d * c, ?_⟩
      have h2 : ((d * c : ℂˣ) : ℂ) • v = (d : ℂ) • ((c : ℂ) • v) := by
        rw [Units.val_mul, smul_smul]
      rw [h2]
      exact hd
    · rintro ⟨d, hd⟩
      refine ⟨d * c⁻¹, ?_⟩
      have h2 : ((d * c⁻¹ : ℂˣ) : ℂ) • ((c : ℂ) • v) = (d : ℂ) • v := by
        rw [Units.val_mul, Units.val_inv_eq_inv_val, smul_smul, mul_assoc,
          inv_mul_cancel₀ (Units.ne_zero c), mul_one]
      rw [h2]
      exact hd
  · intro v hv
    simp only [Set.mem_iUnion, Set.mem_preimage]
    constructor
    · intro hm
      exact ⟨1, by simpa using (hD₀' v hv).mpr hm⟩
    · rintro ⟨c, hc⟩
      have h1 : Projectivization.mk ℂ ((c : ℂ) • v) (smul_ne_zero (Units.ne_zero c) hv) ∈ V :=
        (hD₀' ((c : ℂ) • v) (smul_ne_zero (Units.ne_zero c) hv)).mp hc
      have h2 : Projectivization.mk ℂ v hv = Projectivization.mk ℂ ((c : ℂ) • v)
          (smul_ne_zero (Units.ne_zero c) hv) := by
        rw [Projectivization.mk_eq_mk_iff']
        refine ⟨(c : ℂ)⁻¹, ?_⟩
        rw [smul_smul, inv_mul_cancel₀ (Units.ne_zero c), one_smul]
      rw [h2]
      exact h1

/-! ## The quotient map `E∖0 → P(E)` is open on saturated sets -/

/-- The image under the quotient map `E∖0 → P(E)` of a `ℂˣ`-invariant open set is open: the
preimage of that image is the set itself (the action is by homeomorphisms, so `mkProj Z` is an
open quotient map on invariant sets). -/
theorem isOpen_image_mkProj (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι)
    {Ω : Set ↥(zeroComplement (realification Z))} (hΩ : IsOpen Ω)
    (hsat : ∀ (c : ℂˣ) (p : ↥(zeroComplement (realification Z))), smulPunct Z c p ∈ Ω ↔ p ∈ Ω) :
    IsOpen (mkProj Z '' Ω) := by
  refine (isQuotientMap_quotient_mk' (s := projSetoid Z)).isCoinducing.isOpen_preimage.mp ?_
  have hpre : mkProj Z ⁻¹' (mkProj Z '' Ω) = Ω := by
    ext p
    constructor
    · intro hp
      obtain ⟨q, hqΩ, hq⟩ := hp
      obtain ⟨c, hc⟩ := (mkProj_eq_iff_smul Z).mp hq.symm
      rw [hc]
      exact (hsat c q).mpr hqΩ
    · intro hp
      exact ⟨p, hp, rfl⟩
  change IsOpen (mkProj Z ⁻¹' (mkProj Z '' Ω))
  rw [hpre]
  exact hΩ

/-! ## Continuity of the two maps -/

/-- `fibreMap Z b` is continuous: through the quotient `{v // v ≠ 0} → ℙ ℂ (ℂ^m)` it is the
composite of `mkProj Z` with the continuous section `v ↦ (b,v)` of the (realified) bundle. -/
theorem continuous_fibreMap (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι) (b : B) :
    Continuous (fibreMap Z b) := by
  rw [show fibreMap Z b = Quotient.lift (fun v : {v : EuclideanSpace ℂ (Fin m) // v ≠ 0} =>
      fibreOf Z b v) _ from rfl]
  change Continuous (Quotient.lift (fun v : {v : EuclideanSpace ℂ (Fin m) // v ≠ 0} =>
      fibreOf Z b v) _ : Quotient (projectivizationSetoid ℂ (EuclideanSpace ℂ (Fin m))) →
        ProjFibre Z b)
  rw [(isQuotientMap_quotient_mk' (s := projectivizationSetoid ℂ (EuclideanSpace ℂ (Fin m)))).continuous_iff]
  show Continuous (fun v : {v : EuclideanSpace ℂ (Fin m) // v ≠ 0} => fibreOf Z b v)
  refine Continuous.subtype_mk ?_ _
  show Continuous (fun v : {v : EuclideanSpace ℂ (Fin m) // v ≠ 0} =>
    mkProj Z ⟨(⟨b, v.1⟩ : (realification Z).TotalSpace), _⟩)
  refine (continuous_mkProj Z).comp ?_
  refine Continuous.subtype_mk ?_ _
  exact (((realification Z).toFiberBundleCore.continuous_totalSpaceMk b).comp continuous_subtype_val)

/-- The inverse of `fibreMap Z b` — the class of the second coordinate of a lift — is continuous.
This is the substance of the identification of the fibre: the fibre carries the quotient topology
of the punctured fibre, on which the chart coordinate is continuous. -/
theorem continuous_projClass_subtype (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι)
    (b : B) : Continuous (fun x : ProjFibre Z b => projClass Z x.1) := by
  rw [continuous_def]
  intro V hV
  rw [isOpen_iff_forall_mem_open]
  rintro x₀ hx₀
  obtain ⟨p₀, hp₀⟩ := surjective_mkProj Z x₀.1
  obtain ⟨D, hDopen, hDsat, hDcls⟩ := exists_saturated_open_class V hV
  have hp₀b : p₀.1.proj = b := by
    have h : projMap Z (mkProj Z p₀) = b := by rw [hp₀]; exact x₀.2
    rwa [projMap_mkProj] at h
  have hx₀'' : projClass Z (mkProj Z p₀) ∈ V := by rw [hp₀]; exact hx₀
  have hx₀' : Projectivization.mk ℂ (show EuclideanSpace ℂ (Fin m) from p₀.1.2)
      ((mem_zeroComplement p₀.1).mp p₀.2) ∈ V := by
    rw [← projClass_mkProj Z p₀]
    exact hx₀''
  let i := (realification Z).indexAt b
  let cc : (realification Z).TotalSpace → EuclideanSpace ℂ (Fin m) :=
    fun p => ((realification Z).localTriv i p).2
  let Ω₀ : Set (realification Z).TotalSpace := ((realification Z).localTriv i).source ∩ cc ⁻¹' D
  let Ω : Set ↥(zeroComplement (realification Z)) := Subtype.val ⁻¹' Ω₀
  have hΩ₀open : IsOpen Ω₀ := by
    have hcont : ContinuousOn cc ((realification Z).localTriv i).source :=
      continuous_snd.comp_continuousOn ((realification Z).localTriv i).continuousOn
    exact hcont.isOpen_inter_preimage ((realification Z).localTriv i).open_source hDopen
  have hsmul_mem : ∀ (c : ℂˣ) (x : ↥(zeroComplement (realification Z))),
      ((smulPunct Z c x : ↥(zeroComplement (realification Z))) : (realification Z).TotalSpace)
        ∈ Ω₀ ↔ (x : (realification Z).TotalSpace) ∈ Ω₀ := by
    intro c x
    have hcc : cc (smulPunct Z c x : (realification Z).TotalSpace) = (c : ℂ) • cc x := by
      dsimp only [cc]
      rw [realification_localTriv_snd, chartCoord_smulPunct, realification_localTriv_snd]
    have hsrc : (smulPunct Z c x : (realification Z).TotalSpace)
        ∈ ((realification Z).localTriv i).source ↔
        (x : (realification Z).TotalSpace) ∈ ((realification Z).localTriv i).source := by
      rw [VectorBundleCore.mem_localTriv_source, VectorBundleCore.mem_localTriv_source,
        smulPunct_proj]
    simp only [Ω₀, Set.mem_inter_iff, Set.mem_preimage, hcc, hsrc]
    exact ⟨fun h => ⟨h.1, (hDsat c (cc x)).mp h.2⟩,
      fun h => ⟨h.1, (hDsat c (cc x)).mpr h.2⟩⟩
  have hΩsat : ∀ (c : ℂˣ) (p : ↥(zeroComplement (realification Z))),
      smulPunct Z c p ∈ Ω ↔ p ∈ Ω := hsmul_mem
  have hΩimg : IsOpen (mkProj Z '' Ω) := isOpen_image_mkProj Z
    (hΩ₀open.preimage continuous_subtype_val) hΩsat
  refine ⟨Subtype.val ⁻¹' (mkProj Z '' Ω), ?_, ?_, ?_⟩
  · intro x hx
    obtain ⟨q, hqΩ, hq⟩ := hx
    have hqb : q.1.proj = b := by
      have h : projMap Z (mkProj Z q) = b := by rw [hq]; exact x.2
      rwa [projMap_mkProj] at h
    have hqD : q.1.2 ∈ D := by
      have h1 : cc (q : (realification Z).TotalSpace) ∈ D := by
        have h0 := hqΩ
        simp only [Ω, Ω₀, Set.mem_preimage, Set.mem_inter_iff] at h0
        exact h0.2
      have h2 : cc (q : (realification Z).TotalSpace) = chartCoord Z i q := by
        dsimp only [cc]; rw [realification_localTriv_snd]
      rw [h2, chartCoord_indexAt_eq_snd Z b q hqb] at h1
      exact h1
    have hpc : projClass Z x.1 = Projectivization.mk ℂ (show EuclideanSpace ℂ (Fin m) from q.1.2)
        ((mem_zeroComplement q.1).mp q.2) := by
      rw [← hq, projClass_mkProj Z q]
    show projClass Z x.1 ∈ V
    rw [hpc]
    exact (hDcls q.1.2 ((mem_zeroComplement q.1).mp q.2)).mpr hqD
  · exact hΩimg.preimage continuous_subtype_val
  · refine ⟨p₀, ?_, hp₀⟩
    refine ⟨?_, ?_⟩
    · rw [VectorBundleCore.mem_localTriv_source]
      dsimp only [i]
      rw [realification_baseSet, hp₀b, realification_indexAt]
      exact Z.mem_baseSet_at b
    · show ((realification Z).localTriv i (p₀ : (realification Z).TotalSpace)).2 ∈ D
      rw [realification_localTriv_snd, chartCoord_indexAt_eq_snd Z b p₀ hp₀b]
      exact (hDcls p₀.1.2 ((mem_zeroComplement p₀.1).mp p₀.2)).mp hx₀'

/-! ## The homeomorphism -/

/-- **The fibre of `π : P(E) → B` over `b` is `ℂP^{m-1}`**, as a homeomorphism: the bijection
`fibreMap Z b` of `fibreMap_bijective` is continuous, and so is its inverse `projClass`. -/
theorem nonempty_homeo_projFibre {B : Type} [TopologicalSpace B] {ι : Type} {m : ℕ}
    (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι) (b : B) :
    Nonempty (Work.LerayHirsch.ProjFibre Z b ≃ₜ
      Projectivization ℂ (EuclideanSpace ℂ (Fin m))) := by
  exact ⟨{ toEquiv :=
              { toFun := fun x => projClass Z x.1,
                invFun := fibreMap Z b,
                left_inv := fun x => by
                  rw [fibreMap_projClass Z b x.1 x.2],
                right_inv := fun y => projClass_fibreMap Z b y },
            continuous_toFun := continuous_projClass_subtype Z b,
            continuous_invFun := continuous_fibreMap Z b }⟩

end

end Work.LerayHirsch
