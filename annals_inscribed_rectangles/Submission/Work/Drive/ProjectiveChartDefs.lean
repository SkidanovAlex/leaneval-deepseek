import Mathlib
import Submission.Work.Drive.ProjectiveDefs
import Submission.Work.Drive.ProjectiveTopology
import Submission.Work.Drive.sphere_quotient_projective

/-!
# The classical charts on real projective space

`ℝPⁿ`, modelled as `Projectivization ℝ (EuclideanSpace ℝ (Fin (n+1)))`, is covered by the `n + 1`
classical affine charts: on the open set `Uᵢ` of points that have a representative with non-zero
`i`-th coordinate, the chart is `[v] ↦ (v_j / v_i)_{j ≠ i}`, indexed by `Fin n` through
`Fin.succAbove i`.  This file fixes the vocabulary (the chart maps, their inverses, the "standard
sections" `x ↦ (x, 1)` and the changes of coordinates), and proves the purely algebraic identities
about them; the topology and the smoothness of the transitions are added on top.

* `projSection i x` is the representative `(x, 1)` of the point of the `i`-th chart with coordinates
  `x`;
* `projCoordFun i v` is the coordinate function `v ↦ (v_j/v_i)_{j ≠ i}` on non-zero vectors;
* `projChartMap i` is that function, descended to `ℝPⁿ` (with the junk value convention `0/0 = 0`);
* `projChartInv i` is `x ↦ [projSection i x]`, the inverse chart;
* `projChartSource i` is the source `Uᵢ` of the `i`-th chart;
* `projTransFun i i'` is the change of coordinates `Uᵢ → Uᵢ'` in the projectivised coordinates, and
  `projTransSource i i'` its domain.
-/

namespace Work.Drive

open scoped LinearAlgebra.Projectivization
open Set

noncomputable section

variable {n : ℕ}

/-! ## The standard section `x ↦ (x, 1)` -/

/-- The vector obtained from `x : ℝⁿ` by inserting a `1` in the `i`-th coordinate: the standard
representative of the point of the `i`-th projective chart with coordinates `x`. -/
def projSection (i : Fin (n + 1)) (x : EuclideanSpace ℝ (Fin n)) : Eucl n :=
  WithLp.toLp 2 (Fin.insertNth (α := fun _ => ℝ) i (1 : ℝ) x.ofLp)

@[simp] lemma projSection_ofLp (i : Fin (n + 1)) (x : EuclideanSpace ℝ (Fin n)) :
    (projSection i x).ofLp = Fin.insertNth (α := fun _ => ℝ) i (1 : ℝ) x.ofLp :=
  WithLp.ofLp_toLp 2 _

@[simp] lemma projSection_apply_same (i : Fin (n + 1)) (x : EuclideanSpace ℝ (Fin n)) :
    (projSection i x).ofLp i = 1 := by
  rw [projSection_ofLp, Fin.insertNth_apply_same]

@[simp] lemma projSection_apply_succAbove (i : Fin (n + 1)) (x : EuclideanSpace ℝ (Fin n))
    (j : Fin n) : (projSection i x).ofLp (i.succAbove j) = x.ofLp j := by
  rw [projSection_ofLp, Fin.insertNth_apply_succAbove]

lemma projSection_ne_zero (i : Fin (n + 1)) (x : EuclideanSpace ℝ (Fin n)) :
    projSection i x ≠ 0 := by
  intro h
  have h1 : (projSection i x).ofLp i = (0 : Eucl n).ofLp i := congrArg (fun v => v.ofLp i) h
  rw [projSection_apply_same] at h1
  simp at h1

/-! ## The coordinate function `v ↦ (v_j/v_i)_{j ≠ i}` -/

/-- The projective coordinates of a vector: `(v_j/v_i)_{j ≠ i}`, indexed by `Fin n` through
`Fin.succAbove i`.  Off the set where `v_i = 0` the value is the junk value coming from `0/0 = 0`. -/
def projCoordFun (i : Fin (n + 1)) (v : Eucl n) : EuclideanSpace ℝ (Fin n) :=
  WithLp.toLp 2 (fun j : Fin n => v.ofLp (i.succAbove j) / v.ofLp i)

@[simp] lemma projCoordFun_ofLp (i : Fin (n + 1)) (v : Eucl n) (j : Fin n) :
    (projCoordFun i v).ofLp j = v.ofLp (i.succAbove j) / v.ofLp i :=
  WithLp.ofLp_toLp 2 _

lemma projCoordFun_smul {i : Fin (n + 1)} {t : ℝ} (ht : t ≠ 0) (v : Eucl n) :
    projCoordFun i (t • v) = projCoordFun i v := by
  have h : (fun j : Fin n => (t • v).ofLp (i.succAbove j) / (t • v).ofLp i)
      = (fun j : Fin n => v.ofLp (i.succAbove j) / v.ofLp i) := by
    funext j
    rw [PiLp.smul_apply, PiLp.smul_apply, smul_eq_mul, smul_eq_mul, mul_div_mul_left _ _ ht]
  calc projCoordFun i (t • v)
      = WithLp.toLp 2 (fun j : Fin n => (t • v).ofLp (i.succAbove j) / (t • v).ofLp i) := rfl
    _ = WithLp.toLp 2 (fun j : Fin n => v.ofLp (i.succAbove j) / v.ofLp i) := by rw [h]
    _ = projCoordFun i v := rfl

lemma projCoordFun_projSection (i : Fin (n + 1)) (x : EuclideanSpace ℝ (Fin n)) :
    projCoordFun i (projSection i x) = x := by
  have h : (fun j : Fin n => (projSection i x).ofLp (i.succAbove j) / (projSection i x).ofLp i)
      = x.ofLp := by
    funext j
    rw [projSection_apply_succAbove, projSection_apply_same, div_one]
  calc projCoordFun i (projSection i x)
      = WithLp.toLp 2 (fun j : Fin n =>
          (projSection i x).ofLp (i.succAbove j) / (projSection i x).ofLp i) := rfl
    _ = WithLp.toLp 2 x.ofLp := by rw [h]
    _ = x := WithLp.toLp_ofLp 2 x

/-! ## The chart and its source -/

/-- The `i`-th projective chart map, as a total function on `ℝPⁿ` (with junk values off its
source): the projective coordinates `[v] ↦ (v_j/v_i)_{j ≠ i}` of a point. -/
def projChartMap (i : Fin (n + 1)) :
    Projectivization ℝ (Eucl n) → EuclideanSpace ℝ (Fin n) :=
  Projectivization.lift (fun v : {v : Eucl n // v ≠ 0} => projCoordFun i v.1) (by
    rintro ⟨a, ha⟩ ⟨b, hb⟩ t h
    have ht : t ≠ 0 := by
      rintro rfl
      simp only [zero_smul] at h
      exact ha h
    rw [h, projCoordFun_smul ht])

lemma projChartMap_mk (i : Fin (n + 1)) (v : Eucl n) (hv : v ≠ 0) :
    projChartMap i (Projectivization.mk ℝ v hv) = projCoordFun i v :=
  Projectivization.lift_mk _ _ v hv

/-- The canonical map from the non-zero vectors of `ℝ^{n+1}` onto `ℝPⁿ`. -/
def projQuot (n : ℕ) : {v : Eucl n // v ≠ 0} → Projectivization ℝ (Eucl n) :=
  fun v => Projectivization.mk ℝ v.1 v.2

/-- The source of the `i`-th projective chart: the points having a representative whose `i`-th
coordinate is non-zero. -/
def projChartSource (i : Fin (n + 1)) : Set (Projectivization ℝ (Eucl n)) :=
  projQuot n '' {v : {v : Eucl n // v ≠ 0} | v.1.ofLp i ≠ 0}

lemma mem_projChartSource_iff {i : Fin (n + 1)} {p : Projectivization ℝ (Eucl n)} :
    p ∈ projChartSource i ↔
      ∃ v : Eucl n, ∃ hv : v ≠ 0, p = Projectivization.mk ℝ v hv ∧ v.ofLp i ≠ 0 := by
  constructor
  · rintro ⟨⟨v, hv⟩, hv', rfl⟩
    exact ⟨v, hv, rfl, hv'⟩
  · rintro ⟨v, hv, rfl, hv'⟩
    exact ⟨⟨v, hv⟩, hv', rfl⟩

/-- The inverse of the `i`-th projective chart: the point represented by `projSection i x`. -/
def projChartInv (i : Fin (n + 1)) (x : EuclideanSpace ℝ (Fin n)) :
    Projectivization ℝ (Eucl n) :=
  Projectivization.mk ℝ (projSection i x) (projSection_ne_zero i x)

lemma projChartInv_mem_projChartSource (i : Fin (n + 1)) (x : EuclideanSpace ℝ (Fin n)) :
    projChartInv i x ∈ projChartSource i := by
  refine ⟨⟨projSection i x, projSection_ne_zero i x⟩, ?_, ?_⟩
  · simpa using projSection_apply_same i x
  · exact projectivizationMk_congr ℝ (Eucl n)

lemma projChartMap_projChartInv (i : Fin (n + 1)) (x : EuclideanSpace ℝ (Fin n)) :
    projChartMap i (projChartInv i x) = x := by
  rw [projChartInv, projChartMap_mk, projCoordFun_projSection]

lemma mem_projChartSource_iff' {i : Fin (n + 1)} {v : Eucl n} (hv : v ≠ 0) :
    Projectivization.mk ℝ v hv ∈ projChartSource i ↔ v.ofLp i ≠ 0 := by
  rw [mem_projChartSource_iff]
  constructor
  · rintro ⟨w, hw, h, hwi⟩
    obtain ⟨a, ha⟩ := (Projectivization.mk_eq_mk_iff ℝ v w hv hw).mp h
    have hva : v.ofLp i = (a : ℝ) * w.ofLp i := by
      rw [← ha, Units.smul_def, PiLp.smul_apply, smul_eq_mul]
    rw [hva]
    exact mul_ne_zero (Units.ne_zero a) hwi
  · exact fun h => ⟨v, hv, rfl, h⟩

lemma projChartInv_projChartMap {i : Fin (n + 1)} {p : Projectivization ℝ (Eucl n)}
    (hp : p ∈ projChartSource i) : projChartInv i (projChartMap i p) = p := by
  obtain ⟨v, hv, rfl, hvi⟩ := mem_projChartSource_iff.mp hp
  rw [projChartMap_mk, projChartInv]
  refine (Projectivization.mk_eq_mk_iff' ℝ _ v (projSection_ne_zero i _) hv).mpr
    ⟨(v.ofLp i)⁻¹, ?_⟩
  have hkey : Fin.insertNth (α := fun _ => ℝ) i (1 : ℝ) (projCoordFun i v).ofLp =
      ((v.ofLp i)⁻¹ • v).ofLp := by
    refine Fin.insertNth_eq_iff.mpr ⟨?_, ?_⟩
    · rw [PiLp.smul_apply, smul_eq_mul, inv_mul_cancel₀ hvi]
    · funext j
      rw [projCoordFun_ofLp, Fin.removeNth_apply, PiLp.smul_apply, smul_eq_mul, div_eq_inv_mul]
  calc (v.ofLp i)⁻¹ • v = WithLp.toLp 2 (((v.ofLp i)⁻¹ • v).ofLp) := (WithLp.toLp_ofLp 2 _).symm
    _ = WithLp.toLp 2 (Fin.insertNth (α := fun _ => ℝ) i (1 : ℝ) (projCoordFun i v).ofLp) := by
          rw [hkey]
    _ = projSection i (projCoordFun i v) := rfl

/-! ## The change of coordinates -/

/-- The change of coordinates from the `i`-th to the `i'`-th projective chart, in the
projectivised coordinates: `x ↦ (projSection i x)_{j'}/(projSection i x)_{i'}`. -/
def projTransFun (i i' : Fin (n + 1)) (x : EuclideanSpace ℝ (Fin n)) :
    EuclideanSpace ℝ (Fin n) :=
  WithLp.toLp 2 (fun j : Fin n => (projSection i x).ofLp (i'.succAbove j) / (projSection i x).ofLp i')

@[simp] lemma projTransFun_ofLp (i i' : Fin (n + 1)) (x : EuclideanSpace ℝ (Fin n)) (j : Fin n) :
    (projTransFun i i' x).ofLp j =
      (projSection i x).ofLp (i'.succAbove j) / (projSection i x).ofLp i' :=
  WithLp.ofLp_toLp 2 _

/-- The domain of the change of coordinates from the `i`-th to the `i'`-th chart: the points `x`
whose standard representative `projSection i x` has non-zero `i'`-th coordinate. -/
def projTransSource (i i' : Fin (n + 1)) : Set (EuclideanSpace ℝ (Fin n)) :=
  {x | (projSection i x).ofLp i' ≠ 0}

lemma projChartMap_projChartInv_eq_transFun (i i' : Fin (n + 1))
    (x : EuclideanSpace ℝ (Fin n)) :
    projChartMap i' (projChartInv i x) = projTransFun i i' x := by
  rw [projChartInv, projChartMap_mk]
  rfl

lemma projChartInv_mem_projChartSource_iff (i i' : Fin (n + 1))
    (x : EuclideanSpace ℝ (Fin n)) :
    projChartInv i x ∈ projChartSource i' ↔ x ∈ projTransSource i i' := by
  rw [mem_projChartSource_iff]
  constructor
  · rintro ⟨v, hv, h, hvi⟩
    have h2 : Projectivization.mk ℝ v hv =
        Projectivization.mk ℝ (projSection i x) (projSection_ne_zero i x) := by
      rw [← h, projChartInv]
    obtain ⟨a, ha⟩ := (Projectivization.mk_eq_mk_iff ℝ v (projSection i x) hv _).mp h2
    have hva : v.ofLp i' = (a : ℝ) * (projSection i x).ofLp i' := by
      rw [← ha, Units.smul_def, PiLp.smul_apply, smul_eq_mul]
    intro h0
    rw [hva, h0, mul_zero] at hvi
    exact hvi rfl
  · exact fun h =>
      ⟨projSection i x, projSection_ne_zero i x, by rw [projChartInv], h⟩

end

end Work.Drive
