import Mathlib
import Submission.Work.LerayHirsch.Punctum
import Submission.Work.Thom.chernClass_comap

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option linter.unusedSectionVars false
set_option linter.unnecessarySimpa false

/-!
# The projectivisation of a complex gluing-data bundle (II): the tautological line bundle

Let `Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι` be a complex gluing-data bundle and
`P(E) = Work.LerayHirsch.ProjSpace Z` its projectivisation
(`Submission/Work/LerayHirsch/Punctum.lean`).  This module builds the **tautological line bundle**
`ℓ ⊆ π^*E` over `P(E)` as a gluing-data bundle

```lean
Work.LerayHirsch.tautLine Z :
  VectorBundleCore ℂ (ProjSpace Z) (EuclideanSpace ℂ (Fin 1)) (ι × Fin m)
```

with the defining equations `tautLine_baseSet`, `tautLine_indexAt`, `tautLine_coordChange`, and the
class

```lean
Work.LerayHirsch.zeta Z := chernClass 1 1 (tautLine Z) : Coh ℤ 2 (ProjSpace Z)
```

(the **hyperplane class** `ζ = c₁(ℓ)`).  The index `(i,k)` of the cover is a chart `i` of `Z`
together with a coordinate `k` which does not vanish on it; the frame over `(i,k)` is the
tautological point of `ℓ` whose `i`-th coordinate `k` equals `1`, so that the transition function
`(i,k) → (j,l)` is the *ratio* of the two chart coordinates

`λ_{ik,jl}(p) = (chartCoord j p)_l / (chartCoord i p)_k`,

a continuous function of the *class* `[p]` because both coordinates are scaled by the same unit.

The cover is open, covers `P(E)`, and the transition functions satisfy the cocycle condition; the
continuity is proved through the quotient universal property
`Topology.IsQuotientMap.continuousOn_isOpen_iff`.
-/

namespace Work.LerayHirsch

open Work.TangentClasses Work.Thom

open scoped LinearAlgebra.Projectivization

noncomputable section

variable {B : Type} [TopologicalSpace B] {ι : Type} {m : ℕ}

/-- The model fibre of the tautological line bundle. -/
abbrev LineFibre : Type := EuclideanSpace ℂ (Fin 1)

/-! ## The chart coordinates: continuity -/

/-- The second component of a local trivialisation of the realification is continuous on its
source.  (The `Work.Thom` version is stated for fibres `ℂ^{n+1}`; this is the version for an
arbitrary rank `m`.) -/
theorem continuousOn_localTriv_snd (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι) (j : ι) :
    ContinuousOn
      (fun q : (realification Z).TotalSpace => (((realification Z).localTriv j q)).2)
      (((realification Z).localTriv j)).source :=
  (continuous_snd.comp_continuousOn ((realification Z).localTriv j).continuousOn_toFun).congr
    (fun _ _ => rfl)

/-- `chartCoord` read in the trivialisation of the *realification*. -/
theorem chartCoord_eq_realification (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι) (i : ι)
    (p : ↥(zeroComplement (realification Z))) :
    chartCoord Z i p
      = (((realification Z).localTriv i (p : (realification Z).TotalSpace))).2 := by
  rw [chartCoord, VectorBundleCore.localTriv_apply, VectorBundleCore.localTriv_apply,
    realification_indexAt, realification_coordChange]

/-- The chart coordinates are continuous on the set where the chart is defined. -/
theorem continuousOn_chartCoord (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι) (i : ι) :
    ContinuousOn (fun p : ↥(zeroComplement (realification Z)) => chartCoord Z i p)
      {p | p.1.proj ∈ Z.baseSet i} := by
  refine ((continuousOn_localTriv_snd Z i).comp continuous_subtype_val.continuousOn ?_).congr
    (fun p hp => ?_)
  · intro p hp
    rw [VectorBundleCore.mem_localTriv_source, realification_baseSet]
    exact hp
  · simp only [Function.comp_apply, chartCoord_eq_realification]

/-! ## The charts of the tautological line bundle -/

/-- The chart `(i,k)` of the tautological line bundle: the points of `E∖0` which lie over
`Z.baseSet i` and whose `k`-th chart coordinate is nonzero. -/
def tautBaseSet (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι) (i : ι) (k : Fin m) :
    Set ↥(zeroComplement (realification Z)) :=
  {p | p.1.proj ∈ Z.baseSet i ∧ chartCoord Z i p k ≠ 0}

@[simp] theorem mem_tautBaseSet (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι) (i : ι)
    (k : Fin m) (p : ↥(zeroComplement (realification Z))) :
    p ∈ tautBaseSet Z i k ↔ p.1.proj ∈ Z.baseSet i ∧ chartCoord Z i p k ≠ 0 := Iff.rfl

/-- The charts are invariant under the `ℂˣ`-action. -/
theorem tautBaseSet_smul (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι) (i : ι)
    (k : Fin m) (c : ℂˣ) (p : ↥(zeroComplement (realification Z))) :
    smulPunct Z c p ∈ tautBaseSet Z i k ↔ p ∈ tautBaseSet Z i k := by
  rw [mem_tautBaseSet, mem_tautBaseSet, smulPunct_proj, chartCoord_smulPunct]
  simp

/-- Every point of `E∖0` lies in some chart of the tautological line bundle. -/
theorem exists_mem_tautBaseSet (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι)
    (p : ↥(zeroComplement (realification Z))) : ∃ ik : ι × Fin m, p ∈ tautBaseSet Z ik.1 ik.2 := by
  have hne : chartCoord Z (Z.indexAt p.1.proj) p ≠ 0 :=
    chartCoord_ne_zero_of_mem_baseSet Z _ p (Z.mem_baseSet_at p.1.proj)
  obtain ⟨k, hk⟩ : ∃ k : Fin m, chartCoord Z (Z.indexAt p.1.proj) p k ≠ 0 := by
    by_contra h
    exact hne (by ext k; simpa using not_not.mp (not_exists.mp h k))
  exact ⟨(Z.indexAt p.1.proj, k), Z.mem_baseSet_at p.1.proj, hk⟩

/-- The charts of the tautological line bundle are open in `E∖0`. -/
theorem isOpen_tautBaseSet (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι) (i : ι)
    (k : Fin m) : IsOpen (tautBaseSet Z i k) := by
  have hproj : Continuous (fun p : ↥(zeroComplement (realification Z)) => p.1.proj) :=
    ((bundleProj (realification Z)).comp (subtypeMap (zeroComplement (realification Z)))).continuous
  have hs : IsOpen {p : ↥(zeroComplement (realification Z)) | p.1.proj ∈ Z.baseSet i} :=
    (Z.isOpen_baseSet i).preimage hproj
  have hcoord : ContinuousOn
      (fun p : ↥(zeroComplement (realification Z)) => chartCoord Z i p k)
      {p : ↥(zeroComplement (realification Z)) | p.1.proj ∈ Z.baseSet i} :=
    ((by fun_prop : Continuous (fun v : EuclideanSpace ℂ (Fin m) => v k)).comp_continuousOn
      (continuousOn_chartCoord Z i))
  exact hcoord.isOpen_inter_preimage hs (isOpen_ne (x := (0 : ℂ)))

/-- The chart `(i,k)` of the tautological line bundle, as an open set of the projectivisation
`P(E)`: the *image* of `tautBaseSet`.  It is well defined because `tautBaseSet` is saturated. -/
def tautBaseSetProj (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι) (ik : ι × Fin m) :
    Set (ProjSpace Z) :=
  mkProj Z '' tautBaseSet Z ik.1 ik.2

theorem mem_tautBaseSetProj_mk (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι)
    (ik : ι × Fin m) (p : ↥(zeroComplement (realification Z))) :
    mkProj Z p ∈ tautBaseSetProj Z ik ↔ p ∈ tautBaseSet Z ik.1 ik.2 := by
  constructor
  · rintro ⟨q, hq, hqp⟩
    obtain ⟨c, hc⟩ := Quotient.eq''.mp hqp
    rw [← hc] at hq
    exact (tautBaseSet_smul Z ik.1 ik.2 c p).mp hq
  · exact fun hp => ⟨p, hp, rfl⟩

theorem preimage_tautBaseSetProj (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι)
    (ik : ι × Fin m) : mkProj Z ⁻¹' tautBaseSetProj Z ik = tautBaseSet Z ik.1 ik.2 := by
  ext p
  rw [Set.mem_preimage, mem_tautBaseSetProj_mk]

/-- Every point of `P(E)` lies in a chart. -/
theorem exists_mem_tautBaseSetProj (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι)
    (x : ProjSpace Z) : ∃ ik : ι × Fin m, x ∈ tautBaseSetProj Z ik := by
  obtain ⟨p, rfl⟩ := surjective_mkProj Z x
  obtain ⟨ik, hik⟩ := exists_mem_tautBaseSet Z p
  exact ⟨ik, by rwa [mem_tautBaseSetProj_mk]⟩

/-- The charts of the tautological line bundle are open in `P(E)`. -/
theorem isOpen_tautBaseSetProj (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι)
    (ik : ι × Fin m) : IsOpen (tautBaseSetProj Z ik) := by
  have hq : Topology.IsQuotientMap (mkProj Z) := isQuotientMap_quotient_mk'
  rw [← hq.isCoinducing.isOpen_preimage (s := tautBaseSetProj Z ik), preimage_tautBaseSetProj]
  exact isOpen_tautBaseSet Z ik.1 ik.2

/-! ## The transition functions of the tautological line bundle

The frame over the chart `(i,k)` is the tautological point whose `i`-th coordinate `k` equals `1`;
the transition function `(i,k) → (j,l)` is therefore the ratio of the two chart coordinates.  It is
invariant under the `ℂˣ`-action, hence descends to `P(E)`. -/

/-- The transition coefficient of the tautological line bundle between the charts `ik` and `jl`, as
a function on `E∖0` (made total by the `if`, so that it can be used in `Quotient.lift`). -/
def tautCoeff (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι) (ik jl : ι × Fin m)
    (p : ↥(zeroComplement (realification Z))) : ℂ :=
  if h : chartCoord Z ik.1 p ik.2 ≠ 0 then
    chartCoord Z jl.1 p jl.2 / chartCoord Z ik.1 p ik.2
  else 0

theorem tautCoeff_eq (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι) (ik jl : ι × Fin m)
    (p : ↥(zeroComplement (realification Z))) (h : chartCoord Z ik.1 p ik.2 ≠ 0) :
    tautCoeff Z ik jl p = chartCoord Z jl.1 p jl.2 / chartCoord Z ik.1 p ik.2 := by
  rw [tautCoeff, dif_pos h]

/-- The transition coefficient is invariant under the `ℂˣ`-action. -/
theorem tautCoeff_smul (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι) (ik jl : ι × Fin m)
    (c : ℂˣ) (p : ↥(zeroComplement (realification Z))) :
    tautCoeff Z ik jl (smulPunct Z c p) = tautCoeff Z ik jl p := by
  have hne : chartCoord Z ik.1 (smulPunct Z c p) ik.2 ≠ 0 ↔ chartCoord Z ik.1 p ik.2 ≠ 0 := by
    rw [chartCoord_smulPunct]; simp
  by_cases h : chartCoord Z ik.1 p ik.2 ≠ 0
  · rw [tautCoeff, tautCoeff, dif_pos h, dif_pos (hne.mpr h), chartCoord_smulPunct,
      chartCoord_smulPunct]
    simp only [WithLp.ofLp_smul, Pi.smul_apply, smul_eq_mul]
    exact mul_div_mul_left _ _ (Units.ne_zero c)
  · rw [tautCoeff, tautCoeff, dif_neg h, dif_neg (fun hh => h (hne.mp hh))]

/-- The transition coefficient descends to the projectivisation. -/
def tautCoeffLift (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι) (ik jl : ι × Fin m) :
    ProjSpace Z → ℂ :=
  Quotient.lift (tautCoeff Z ik jl) (fun a b h => by
    obtain ⟨c, hc⟩ := h
    rw [← hc, tautCoeff_smul Z ik jl c b])

@[simp] theorem tautCoeffLift_mk (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι)
    (ik jl : ι × Fin m) (p : ↥(zeroComplement (realification Z))) :
    tautCoeffLift Z ik jl (mkProj Z p) = tautCoeff Z ik jl p := rfl

theorem tautCoeffLift_self (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι) (ik : ι × Fin m)
    {x : ProjSpace Z} (hx : x ∈ tautBaseSetProj Z ik) : tautCoeffLift Z ik ik x = 1 := by
  obtain ⟨p, rfl⟩ := surjective_mkProj Z x
  rw [mem_tautBaseSetProj_mk] at hx
  rw [tautCoeffLift_mk, tautCoeff, dif_pos hx.2]
  exact div_self hx.2

theorem tautCoeffLift_comp (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι)
    (ik jm jl : ι × Fin m) {x : ProjSpace Z}
    (hx : x ∈ tautBaseSetProj Z ik ∩ tautBaseSetProj Z jm ∩ tautBaseSetProj Z jl) :
    tautCoeffLift Z jm jl x * tautCoeffLift Z ik jm x = tautCoeffLift Z ik jl x := by
  obtain ⟨p, rfl⟩ := surjective_mkProj Z x
  rw [Set.mem_inter_iff, Set.mem_inter_iff] at hx
  obtain ⟨⟨hik, hjm⟩, hjl⟩ := hx
  rw [mem_tautBaseSetProj_mk] at hik hjm hjl
  rw [tautCoeffLift_mk, tautCoeffLift_mk, tautCoeffLift_mk]
  rw [tautCoeff, tautCoeff, tautCoeff, dif_pos hjm.2, dif_pos hik.2, dif_pos hik.2]
  have hbm : (chartCoord Z jm.1 p).ofLp jm.2 ≠ 0 := hjm.2
  rw [div_mul_div_comm, mul_comm ((chartCoord Z jl.1 p).ofLp jl.2)
    ((chartCoord Z jm.1 p).ofLp jm.2)]
  exact mul_div_mul_left _ _ hbm

/-- The multiplication-by-the-transition-coefficient continuous linear map. -/
def tautCoeffCLM (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι) (ik jl : ι × Fin m)
    (x : ProjSpace Z) : LineFibre →L[ℂ] LineFibre :=
  tautCoeffLift Z ik jl x • ContinuousLinearMap.id ℂ LineFibre

@[simp] theorem tautCoeffCLM_apply (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι)
    (ik jl : ι × Fin m) (x : ProjSpace Z) (v : LineFibre) :
    tautCoeffCLM Z ik jl x v = tautCoeffLift Z ik jl x • v := by
  rw [tautCoeffCLM, ContinuousLinearMap.smul_apply, ContinuousLinearMap.id_apply]

/-- **Continuity of the transition functions** of the tautological line bundle, through the
quotient universal property. -/
theorem continuousOn_tautCoeffCLM (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι)
    (ik jl : ι × Fin m) :
    ContinuousOn (fun x : ProjSpace Z => tautCoeffCLM Z ik jl x)
      (tautBaseSetProj Z ik ∩ tautBaseSetProj Z jl) := by
  have hq : Topology.IsQuotientMap (mkProj Z) := isQuotientMap_quotient_mk'
  refine (Topology.IsQuotientMap.continuousOn_isOpen_iff hq
    ((isOpen_tautBaseSetProj Z ik).inter (isOpen_tautBaseSetProj Z jl))).mpr ?_
  have hpre : mkProj Z ⁻¹' (tautBaseSetProj Z ik ∩ tautBaseSetProj Z jl)
      = tautBaseSet Z ik.1 ik.2 ∩ tautBaseSet Z jl.1 jl.2 := by
    rw [Set.preimage_inter, preimage_tautBaseSetProj, preimage_tautBaseSetProj]
  rw [hpre]
  have hS : ContinuousOn (fun p : ↥(zeroComplement (realification Z)) =>
      chartCoord Z jl.1 p jl.2 / chartCoord Z ik.1 p ik.2)
      (tautBaseSet Z ik.1 ik.2 ∩ tautBaseSet Z jl.1 jl.2) := by
    have h1 : ContinuousOn (fun p : ↥(zeroComplement (realification Z)) =>
        chartCoord Z ik.1 p ik.2) (tautBaseSet Z ik.1 ik.2 ∩ tautBaseSet Z jl.1 jl.2) :=
      ((by fun_prop : Continuous (fun v : EuclideanSpace ℂ (Fin m) => v ik.2)).comp_continuousOn
        ((continuousOn_chartCoord Z ik.1).mono (fun p hp => hp.1.1)))
    have h2 : ContinuousOn (fun p : ↥(zeroComplement (realification Z)) =>
        chartCoord Z jl.1 p jl.2) (tautBaseSet Z ik.1 ik.2 ∩ tautBaseSet Z jl.1 jl.2) :=
      ((by fun_prop : Continuous (fun v : EuclideanSpace ℂ (Fin m) => v jl.2)).comp_continuousOn
        ((continuousOn_chartCoord Z jl.1).mono (fun p hp => hp.2.1)))
    exact h2.div h1 (fun p hp => hp.1.2)
  have hcoeff : ContinuousOn (fun p : ↥(zeroComplement (realification Z)) =>
      tautCoeff Z ik jl p) (tautBaseSet Z ik.1 ik.2 ∩ tautBaseSet Z jl.1 jl.2) :=
    hS.congr (fun p hp => tautCoeff_eq Z ik jl p hp.1.2)
  have := hcoeff.smul (continuousOn_const :
    ContinuousOn (fun _ : ↥(zeroComplement (realification Z)) =>
      (ContinuousLinearMap.id ℂ LineFibre)) _)
  refine this.congr (fun p hp => ?_)
  rfl

/-! ## The tautological line bundle -/

/-- **The tautological line bundle** `ℓ ⊆ π^*E` over `P(E)`, as a complex gluing-data bundle of
rank one.  Its cover is indexed by `ι × Fin m` (a chart of `Z` and a non-vanishing coordinate), and
its transition function between `(i,k)` and `(j,l)` is the ratio of the corresponding chart
coordinates (`tautLine_coordChange`). -/
def tautLine (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι) :
    VectorBundleCore ℂ (ProjSpace Z) LineFibre (ι × Fin m) where
  baseSet ik := tautBaseSetProj Z ik
  isOpen_baseSet ik := isOpen_tautBaseSetProj Z ik
  indexAt x := Classical.choose (exists_mem_tautBaseSetProj Z x)
  mem_baseSet_at x := Classical.choose_spec (exists_mem_tautBaseSetProj Z x)
  coordChange ik jl x := tautCoeffCLM Z ik jl x
  coordChange_self ik x hx v := by
    rw [tautCoeffCLM_apply, tautCoeffLift_self Z ik hx, one_smul]
  continuousOn_coordChange ik jl := continuousOn_tautCoeffCLM Z ik jl
  coordChange_comp ik jm jl x hx v := by
    rw [tautCoeffCLM_apply, tautCoeffCLM_apply, tautCoeffCLM_apply,
      ← tautCoeffLift_comp Z ik jm jl hx, mul_smul]

@[simp] theorem tautLine_baseSet (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι)
    (ik : ι × Fin m) : (tautLine Z).baseSet ik = tautBaseSetProj Z ik := rfl

@[simp] theorem tautLine_coordChange (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι)
    (ik jl : ι × Fin m) (x : ProjSpace Z) :
    (tautLine Z).coordChange ik jl x = tautCoeffCLM Z ik jl x := rfl

/-- The transition function of the tautological line bundle is multiplication by the ratio of the
chart coordinates; this is the equation a caller should use. -/
theorem tautLine_coordChange_apply (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι)
    (ik jl : ι × Fin m) (x : ProjSpace Z) (v : LineFibre) :
    (tautLine Z).coordChange ik jl x v = tautCoeffLift Z ik jl x • v :=
  tautCoeffCLM_apply Z ik jl x v

/-- On the chart `(i,k)`, the transition coefficient from `(i,k)` to `(j,l)` is
`(chartCoord j p)_l / (chartCoord i p)_k` for any representative `p`. -/
theorem tautLine_coordChange_eq_ratio (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι)
    (ik jl : ι × Fin m) (p : ↥(zeroComplement (realification Z)))
    (h : chartCoord Z ik.1 p ik.2 ≠ 0) :
    tautCoeffLift Z ik jl (mkProj Z p) = chartCoord Z jl.1 p jl.2 / chartCoord Z ik.1 p ik.2 := by
  rw [tautCoeffLift_mk, tautCoeff_eq Z ik jl p h]

/-! ## The hyperplane class `ζ = c₁(ℓ)` -/

/-- **The hyperplane class** `ζ = c₁(ℓ)` of the projectivisation, the first Chern class of the
tautological line bundle, in `H²(P(E);ℤ)`. -/
noncomputable def zeta (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι) [Fintype ι] :
    Coh ℤ 2 (ProjSpace Z) :=
  cohTransport rfl (chernClass 1 1 (tautLine Z))

theorem zeta_def (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι) [Fintype ι] :
    zeta Z = cohTransport rfl (chernClass 1 1 (tautLine Z)) := rfl

/-- **The fundamental property of `ζ`**: it is the first Chern class of the tautological line
bundle. -/
theorem zeta_eq_chernClass (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι) [Fintype ι] :
    zeta Z = cohTransport rfl (chernClass 1 1 (tautLine Z)) := rfl

theorem zeta_comap (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι) [Fintype ι]
    {B' : Type} [TopologicalSpace B'] (f : C(B', ProjSpace Z)) :
    (CohMap f ℤ 2).hom (zeta Z) = cohTransport rfl
      (chernClass 1 1 (bundleComap (tautLine Z) f)) := by
  rw [zeta, Work.Thom.chernClass_comap]
  rfl

end

end Work.LerayHirsch
