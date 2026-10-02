import Mathlib
import Submission.Work.Whitney.puncturedNorm
import Submission.Work.LerayHirsch.paracompactSpace_projSpace

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option linter.unusedSectionVars false

/-!
# The chartwise norm on a real bundle, and the dyadic shells

This module sets up the vocabulary for `Work.Whitney.shellParacompact`: the chartwise norm
`chartNorm Z φ i` on the product `B × F` (the fibrewise norm `fibNorm Z φ` read in the
trivialisation `Z.localTriv i`), the "shell" set `shellSet Z φ k` of the punctured total space, and
their elementary properties (continuity on the chart, homogeneity in the fibre, positivity, and the
dictionary between a point of the total space and its chart coordinate).
-/

namespace Work.Whitney

open Bundle Work.TangentClasses Filter Set
open scoped Topology

noncomputable section

variable {B : Type} [TopologicalSpace B] {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {ι : Type} [Fintype ι]

/-- The **chartwise norm**: the fibrewise norm `fibNorm Z φ`, read in the trivialisation
`Z.localTriv i`.  Concretely, on `B × F` it is
`y ↦ fibNorm Z φ ⟨y.1, (Z.coordChange i (Z.indexAt y.1) y.1) y.2⟩`. -/
def chartNorm (Z : VectorBundleCore ℝ B F ι) (φ : PartitionOfUnity ι B Set.univ) (i : ι)
    (y : B × F) : ℝ :=
  fibNorm Z (fun j => φ j) (⟨y.1, Z.coordChange i (Z.indexAt y.1) y.1 y.2⟩ : Z.TotalSpace)

/-- The chartwise norm is the fibrewise norm composed with the inverse of the trivialisation. -/
theorem chartNorm_eq_symm (Z : VectorBundleCore ℝ B F ι) (φ : PartitionOfUnity ι B Set.univ)
    (i : ι) (y : B × F) :
    chartNorm Z φ i y =
      fibNorm Z (fun j => φ j) ((Z.localTriv i).toOpenPartialHomeomorph.symm y) := by
  rw [chartNorm, VectorBundleCore.localTriv_symm_fst]

/-- The chartwise norm is continuous on the chart. -/
theorem continuousOn_chartNorm (Z : VectorBundleCore ℝ B F ι) (φ : PartitionOfUnity ι B Set.univ)
    (i : ι) (hφ : φ.IsSubordinate Z.baseSet) :
    ContinuousOn (chartNorm Z φ i) (Z.baseSet i ×ˢ (univ : Set F)) := by
  have hbase : (Z.localTriv i).baseSet = Z.baseSet i := (VectorBundleCore.baseSet_at Z i).symm
  have htarget : (Z.localTriv i).target = Z.baseSet i ×ˢ (univ : Set F) := by
    rw [Bundle.Trivialization.target_eq, hbase]
  have hinv : ContinuousOn (fun y : B × F => (Z.localTriv i).toOpenPartialHomeomorph.symm y)
      (Z.baseSet i ×ˢ (univ : Set F)) := by
    rw [← htarget]
    exact (Z.localTriv i).continuousOn_invFun
  have hcomp : ContinuousOn (fun y : B × F => fibNorm Z (fun j => φ j)
      ((Z.localTriv i).toOpenPartialHomeomorph.symm y)) (Z.baseSet i ×ˢ (univ : Set F)) :=
    (continuous_fibNorm Z (fun j => φ j) hφ).comp_continuousOn hinv
  refine hcomp.congr fun y _ => ?_
  exact (chartNorm_eq_symm Z φ i y).symm

/-- **Homogeneity** of the chartwise norm in the fibre coordinate. -/
theorem chartNorm_smul (Z : VectorBundleCore ℝ B F ι) (φ : PartitionOfUnity ι B Set.univ) (i : ι)
    (x : B) {c : ℝ} (hc : 0 ≤ c) (v : F) :
    chartNorm Z φ i (x, c • v) = c * chartNorm Z φ i (x, v) := by
  rw [chartNorm, chartNorm, map_smul]
  exact fibNorm_smul Z (fun j => φ j) x hc (Z.coordChange i (Z.indexAt x) x v)

/-- The chartwise norm vanishes on the zero vector. -/
theorem chartNorm_zero (Z : VectorBundleCore ℝ B F ι) (φ : PartitionOfUnity ι B Set.univ) (i : ι)
    (x : B) : chartNorm Z φ i (x, 0) = 0 := by
  rw [chartNorm, map_zero]
  simp only [fibNorm]
  refine Finset.sum_eq_zero fun j _ => ?_
  rw [VectorBundleCore.localTriv_apply]
  simp

/-- In the chart `i` at a point `x` of its base set, the coordinate vector vanishes only for the
zero vector. -/
theorem coordChange_symm_eq_zero_iff (Z : VectorBundleCore ℝ B F ι) {x : B} {i : ι}
    (hx : x ∈ Z.baseSet i) (v : F) :
    Z.coordChange i (Z.indexAt x) x v = 0 ↔ v = 0 := by
  constructor
  · intro hv
    have hx' : x ∈ Z.baseSet i ∩ Z.baseSet (Z.indexAt x) ∩ Z.baseSet i :=
      ⟨⟨hx, Z.mem_baseSet_at x⟩, hx⟩
    have h := Z.coordChange_comp i (Z.indexAt x) i x hx' v
    rw [hv, map_zero, Z.coordChange_self i x hx v] at h
    exact h.symm
  · intro hv
    rw [hv, map_zero]

/-- In the chart `i`, the coordinate map on the fibre is injective. -/
theorem coordChange_symm_injective (Z : VectorBundleCore ℝ B F ι) {x : B} {i : ι}
    (hx : x ∈ Z.baseSet i) : Function.Injective (Z.coordChange i (Z.indexAt x) x) := by
  intro v w hvw
  have hzero : Z.coordChange i (Z.indexAt x) x (v - w) = 0 := by
    rw [map_sub, hvw, sub_self]
  exact sub_eq_zero.mp ((coordChange_symm_eq_zero_iff Z hx (v - w)).mp hzero)

/-- **Positivity** of the chartwise norm: in the chart, `chartNorm` vanishes exactly on the zero
vector. -/
theorem chartNorm_pos_iff (Z : VectorBundleCore ℝ B F ι) (φ : PartitionOfUnity ι B Set.univ)
    (hφ : φ.IsSubordinate Z.baseSet) (i : ι) {x : B} (hx : x ∈ Z.baseSet i) (v : F) :
    0 < chartNorm Z φ i (x, v) ↔ v ≠ 0 := by
  constructor
  · intro h hv
    rw [hv, chartNorm_zero] at h
    exact lt_irrefl 0 h
  · intro hv
    have hne : Z.coordChange i (Z.indexAt x) x v ≠ 0 := fun h0 =>
      hv ((coordChange_symm_eq_zero_iff Z hx v).mp h0)
    have hmem : (⟨x, Z.coordChange i (Z.indexAt x) x v⟩ : Z.TotalSpace) ∈
        Work.Thom.zeroComplement Z := by
      rw [Work.Thom.mem_zeroComplement]
      exact hne
    exact fibNorm_pos Z hφ _ hmem

/-- In the preferred chart of a point, the chartwise norm is the fibrewise norm of the fibre
vector. -/
theorem chartNorm_indexAt (Z : VectorBundleCore ℝ B F ι) (φ : PartitionOfUnity ι B Set.univ)
    (b : B) (v : F) :
    chartNorm Z φ (Z.indexAt b) (b, v) = fibNorm Z (fun j => φ j) (⟨b, v⟩ : Z.TotalSpace) := by
  rw [chartNorm, Z.coordChange_self (Z.indexAt b) b (Z.mem_baseSet_at b) v]

/-- The chart coordinate of a point of the total space is its trivialisation coordinate. -/
theorem localTriv_snd_eq (Z : VectorBundleCore ℝ B F ι) (i : ι) (p : Z.TotalSpace) :
    (Z.localTriv i p).2 = Z.coordChange (Z.indexAt p.1) i p.1 p.2 :=
  fibNorm_aux Z i p

/-- The chartwise norm at the chart coordinate of a point of the chart is its fibrewise norm. -/
theorem chartNorm_apply_localTriv (Z : VectorBundleCore ℝ B F ι)
    (φ : PartitionOfUnity ι B Set.univ) (i : ι) (p : Z.TotalSpace) (hp : p.1 ∈ Z.baseSet i) :
    chartNorm Z φ i (p.1, (Z.localTriv i p).2) = fibNorm Z (fun j => φ j) p := by
  have hsrc : p ∈ (Z.localTriv i).source := by
    rwa [VectorBundleCore.mem_localTriv_source]
  have h : (p.1, (Z.localTriv i p).2) = Z.localTriv i p := by
    simpa using Bundle.Trivialization.mk_proj_snd (Z.localTriv i) hsrc
  rw [chartNorm_eq_symm, h, Bundle.Trivialization.symm_apply_apply (Z.localTriv i) hsrc]

/-! ## The dyadic shell -/

/-- The **dyadic shell** `{p : 2^k ≤ ν p ≤ 2^(k+1)}` of the punctured total space, as a set of the
total space. -/
def shellSet (Z : VectorBundleCore ℝ B F ι) (φ : PartitionOfUnity ι B Set.univ) (k : ℤ) :
    Set Z.TotalSpace :=
  {p | (show F from p.2) ≠ 0 ∧ (2 : ℝ) ^ k ≤ fibNorm Z (fun j => φ j) p ∧
    fibNorm Z (fun j => φ j) p ≤ (2 : ℝ) ^ (k + 1)}

@[simp] theorem mem_shellSet (Z : VectorBundleCore ℝ B F ι) (φ : PartitionOfUnity ι B Set.univ)
    (k : ℤ) (p : Z.TotalSpace) :
    p ∈ shellSet Z φ k ↔ (show F from p.2) ≠ 0 ∧ (2 : ℝ) ^ k ≤ fibNorm Z (fun j => φ j) p ∧
      fibNorm Z (fun j => φ j) p ≤ (2 : ℝ) ^ (k + 1) := Iff.rfl

variable (Z : VectorBundleCore ℝ B F ι) (φ : PartitionOfUnity ι B Set.univ) (k : ℤ)

/-- The fibre of the shell over the base point of the preferred chart, in chart coordinates: it is
the compact annulus `{v : 2^k ≤ chartNorm ... (b,v) ≤ 2^(k+1)}`. -/
def shellSlice (i : ι) (b : B) : Set F :=
  {v | (2 : ℝ) ^ k ≤ chartNorm Z φ i (b, v) ∧ chartNorm Z φ i (b, v) ≤ (2 : ℝ) ^ (k + 1)}

@[simp] theorem mem_shellSlice (i : ι) (b : B) (v : F) :
    v ∈ shellSlice Z φ k i b ↔
      (2 : ℝ) ^ k ≤ chartNorm Z φ i (b, v) ∧ chartNorm Z φ i (b, v) ≤ (2 : ℝ) ^ (k + 1) :=
  Iff.rfl

section Slice

variable (Z : VectorBundleCore ℝ B F ι) (φ : PartitionOfUnity ι B Set.univ) (k : ℤ) (i : ι)
  (b : B)

/-- Lower bound for the chartwise norm at a point of a shell slice. -/
theorem shellSlice_lower {v : F} (hv : v ∈ shellSlice Z φ k i b) :
    (2 : ℝ) ^ k ≤ chartNorm Z φ i (b, v) :=
  ((mem_shellSlice Z φ k i b v).mp hv).1

/-- Upper bound for the chartwise norm at a point of a shell slice. -/
theorem shellSlice_upper {v : F} (hv : v ∈ shellSlice Z φ k i b) :
    chartNorm Z φ i (b, v) ≤ (2 : ℝ) ^ (k + 1) :=
  ((mem_shellSlice Z φ k i b v).mp hv).2

end Slice

section Shell

variable (Z : VectorBundleCore ℝ B F ι) (φ : PartitionOfUnity ι B Set.univ) (k : ℤ)

/-- The fibre component of a point of the shell is nonzero. -/
theorem shellSet_snd_ne (p : ↥(shellSet Z φ k)) :
    (show F from ((p : Z.TotalSpace).2)) ≠ 0 :=
  ((mem_shellSet Z φ k (p : Z.TotalSpace)).mp p.2).1

/-- Lower bound for the fibrewise norm on the shell. -/
theorem shellSet_lower (p : ↥(shellSet Z φ k)) :
    (2 : ℝ) ^ k ≤ fibNorm Z (fun j => φ j) (p : Z.TotalSpace) :=
  ((mem_shellSet Z φ k (p : Z.TotalSpace)).mp p.2).2.1

/-- Upper bound for the fibrewise norm on the shell. -/
theorem shellSet_upper (p : ↥(shellSet Z φ k)) :
    fibNorm Z (fun j => φ j) (p : Z.TotalSpace) ≤ (2 : ℝ) ^ (k + 1) :=
  ((mem_shellSet Z φ k (p : Z.TotalSpace)).mp p.2).2.2

end Shell

/-- If the fibre component of a point of the total space vanishes, then so does the fibrewise
norm. -/
theorem fibNorm_eq_zero_of_snd_eq_zero (Z : VectorBundleCore ℝ B F ι)
    (φ : PartitionOfUnity ι B Set.univ) {p : Z.TotalSpace}
    (hp : (show F from p.2) = 0) : fibNorm Z (fun j => φ j) p = 0 := by
  have h2 : ∀ j, (Z.localTriv j p).2 = 0 := by
    intro j
    have h := congrArg (fun w : F => (Z.coordChange (Z.indexAt p.1) j p.1) w) hp
    simp only [map_zero] at h
    exact (localTriv_snd_eq Z j p).trans h
  simp only [fibNorm]
  exact Finset.sum_eq_zero fun j _ => by rw [h2 j, norm_zero, mul_zero]

end

end Work.Whitney
