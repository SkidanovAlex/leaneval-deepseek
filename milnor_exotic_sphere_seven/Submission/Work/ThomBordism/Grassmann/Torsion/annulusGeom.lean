import Mathlib
import Submission.Work.ThomBordism.Grassmann.Torsion.ModelGeom
import Submission.Work.ThomBordism.Grassmann.Torsion.RadialDefs
import Submission.Work.ThomBordism.Grassmann.Torsion.exists_fibreNormLike

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false

/-!
# The annulus piece of the tautological bundle over a chart

For `U ⊆ baseSet S` the part of the annulus `1 < fibN < 2` over `U` is homeomorphic to
`U × S^{k-1} × (1,2)`: the chart `S` trivialises the bundle over `U`, the chart coordinate can be
normalised fibrewise, and the radial coordinate `fibN` is the third factor.
-/

namespace Work.ThomBordism.Grassmann.Torsion

open Work.ThomBordism.Grassmann

noncomputable section

variable {k m : ℕ}

/-! ## Fibrewise scaling -/

/-- Fibrewise scaling `p ↦ ⟨p.1, t • p.2⟩` of the total space of the tautological bundle. -/
def fibScale (t : ℝ) (p : TM k m) : TM k m := ⟨p.1, t • p.2⟩

@[simp] theorem fibScale_fst (t : ℝ) (p : TM k m) : (fibScale t p).1 = p.1 := rfl

@[simp] theorem fibScale_snd (t : ℝ) (p : TM k m) : (fibScale t p).2 = t • p.2 := rfl

theorem fibScale_one (p : TM k m) : fibScale 1 p = p := by
  have h : (1 : ℝ) • p.2 = p.2 := one_smul ℝ p.2
  rw [fibScale, h]

theorem fibScale_fibScale (a b : ℝ) (p : TM k m) :
    fibScale a (fibScale b p) = fibScale (a * b) p := by
  rw [fibScale, fibScale, fibScale, smul_smul]

theorem fibN_fibScale {t : ℝ} (ht : 0 ≤ t) (p : TM k m) :
    fibN k m (fibScale t p) = t * fibN k m p :=
  fibN_smul k m ht p

theorem continuous_fibScale (t : ℝ) :
    Continuous (fibScale (k := k) (m := m) t) :=
  Work.Thom.continuous_smul_section (tautologicalBundle k m) (ContinuousMap.id (TM k m))
    (ContinuousMap.const (TM k m) t)

/-! ## Reading the chart coordinate -/

/-- The `S`-coordinate of a point of the form `⟨x, w⟩` is the linear map `linearMapAt` applied
to `w`. -/
theorem localTriv_snd_mk (S : ChartIdx k m) {x : OG k m} (hx : x ∈ baseSet S) (w : Amb k) :
    ((tautologicalBundle k m).localTriv S (⟨x, w⟩ : TM k m)).2
      = ((tautologicalBundle k m).localTriv S).linearMapAt ℝ x w := by
  have hxb : x ∈ ((tautologicalBundle k m).localTriv S).baseSet := by
    rw [← VectorBundleCore.baseSet_at]
    exact hx
  rw [Bundle.Trivialization.linearMapAt_apply, if_pos hxb]

/-- The chart coordinate is linear in the fibre element. -/
theorem localTriv_snd_fibScale (S : ChartIdx k m) {p : TM k m} (hp : p.1 ∈ baseSet S) (c : ℝ) :
    ((tautologicalBundle k m).localTriv S (fibScale c p)).2
      = c • ((tautologicalBundle k m).localTriv S p).2 := by
  have h1 : ((tautologicalBundle k m).localTriv S (fibScale c p)).2
      = ((tautologicalBundle k m).localTriv S).linearMapAt ℝ p.1 (c • p.2) := by
    rw [show fibScale c p = (⟨p.1, c • p.2⟩ : TM k m) from rfl, localTriv_snd_mk S hp]
  have h2 : ((tautologicalBundle k m).localTriv S p).2
      = ((tautologicalBundle k m).localTriv S).linearMapAt ℝ p.1 p.2 :=
    localTriv_snd_mk S hp p.2
  rw [h1, h2, map_smul]

/-- The chart coordinate vanishes exactly on the zero section. -/
theorem localTriv_snd_eq_zero_iff (S : ChartIdx k m) {p : TM k m} (hp : p.1 ∈ baseSet S) :
    ((tautologicalBundle k m).localTriv S p).2 = 0 ↔ p.2 = 0 := by
  have h2 : ((tautologicalBundle k m).localTriv S p).2
      = ((tautologicalBundle k m).localTriv S).linearMapAt ℝ p.1 p.2 :=
    localTriv_snd_mk S hp p.2
  rw [h2]
  constructor
  · intro h
    have h3 := Bundle.Trivialization.symmₗ_linearMapAt ((tautologicalBundle k m).localTriv S)
      (R := ℝ) hp p.2
    rw [h, map_zero] at h3
    exact h3.symm
  · intro h
    rw [h, map_zero]

/-! ## The chart coordinates -/

/-- The point of the tautological bundle over `x ∈ baseSet S` whose `S`-chart coordinate is `v`. -/
def chartPt (S : ChartIdx k m) (x : ↥(baseSet S)) (v : Amb k) : TM k m :=
  ⟨x.1, ((tautologicalBundle k m).localTriv S).symmₗ ℝ x.1 v⟩

@[simp] theorem chartPt_fst (S : ChartIdx k m) (x : ↥(baseSet S)) (v : Amb k) :
    (chartPt S x v).1 = x.1 := rfl

@[simp] theorem chartPt_snd (S : ChartIdx k m) (x : ↥(baseSet S)) (v : Amb k) :
    (chartPt S x v).2 = ((tautologicalBundle k m).localTriv S).symm x.1 v := by
  rw [chartPt, Bundle.Trivialization.symmₗ_apply _ x.2 v]

/-- The `S`-coordinate of `chartPt S x v` is `v`. -/
theorem chartPt_coord (S : ChartIdx k m) (x : ↥(baseSet S)) (v : Amb k) :
    ((tautologicalBundle k m).localTriv S (chartPt S x v)).2 = v := by
  rw [chartPt, localTriv_snd_mk S x.2,
    Bundle.Trivialization.linearMapAt_symmₗ ((tautologicalBundle k m).localTriv S)
      (R := ℝ) x.2 v]

/-- `chartPt` is linear in the coordinate. -/
theorem chartPt_smul (S : ChartIdx k m) (x : ↥(baseSet S)) (t : ℝ) (v : Amb k) :
    chartPt S x (t • v) = fibScale t (chartPt S x v) := by
  rw [chartPt, chartPt, fibScale, LinearMap.map_smul]

theorem chartPt_zero (S : ChartIdx k m) (x : ↥(baseSet S)) :
    chartPt S x 0 = (⟨x.1, 0⟩ : TM k m) := by
  rw [chartPt, LinearMap.map_zero]

/-- `chartPt` inverts the chart coordinate. -/
theorem chartPt_self (S : ChartIdx k m) {p : TM k m} (hp : p.1 ∈ baseSet S) :
    chartPt S ⟨p.1, hp⟩ (((tautologicalBundle k m).localTriv S) p).2 = p := by
  have h2 : ((tautologicalBundle k m).localTriv S p).2
      = ((tautologicalBundle k m).localTriv S).linearMapAt ℝ p.1 p.2 :=
    localTriv_snd_mk S hp p.2
  rw [h2, chartPt,
    Bundle.Trivialization.symmₗ_linearMapAt ((tautologicalBundle k m).localTriv S) (R := ℝ) hp p.2]

/-- `chartPt` is injective in the coordinate. -/
theorem chartPt_injective (S : ChartIdx k m) (x : ↥(baseSet S)) :
    Function.Injective (chartPt (k := k) (m := m) S x) := by
  intro v w h
  rw [← chartPt_coord S x v, ← chartPt_coord S x w, h]

theorem chartPt_fibN_eq_zero_iff (S : ChartIdx k m) (x : ↥(baseSet S)) (v : Amb k) :
    fibN k m (chartPt S x v) = 0 ↔ v = 0 := by
  rw [fibN_eq_zero_iff]
  constructor
  · intro h
    have h2 : ((tautologicalBundle k m).localTriv S (chartPt S x v)).2 = 0 :=
      (localTriv_snd_eq_zero_iff S x.2).mpr h
    rwa [chartPt_coord] at h2
  · intro h
    rw [h, chartPt_zero]

theorem chartPt_fibN_pos (S : ChartIdx k m) (x : ↥(baseSet S)) {v : Amb k} (hv : v ≠ 0) :
    0 < fibN k m (chartPt S x v) := by
  rcases lt_or_eq_of_le (fibN_nonneg k m (chartPt S x v)) with h | h
  · exact h
  · exact absurd ((chartPt_fibN_eq_zero_iff S x v).mp h.symm) hv

theorem fibN_chartPt_smul (S : ChartIdx k m) (x : ↥(baseSet S)) {t : ℝ} (ht : 0 ≤ t)
    (v : Amb k) :
    fibN k m (chartPt S x (t • v)) = t * fibN k m (chartPt S x v) := by
  rw [chartPt_smul, fibN_fibScale ht]

/-- **Continuity of the chart coordinates** on a chart: the inverse trivialisation is continuous. -/
theorem continuous_chartPt (S : ChartIdx k m) :
    Continuous (fun q : ↥(baseSet S) × Amb k => chartPt S q.1 q.2) := by
  have h := (tautologicalBundle k m).localTriv S |>.continuousOn_symm
  have hcont : Continuous (fun q : ↥(baseSet S) × Amb k => ((q.1 : OG k m), q.2)) :=
    (continuous_subtype_val.comp continuous_fst).prodMk continuous_snd
  have hmem : ∀ q : ↥(baseSet S) × Amb k,
      ((q.1 : OG k m), q.2) ∈ (baseSet S ×ˢ (Set.univ : Set (Amb k))) :=
    fun q => ⟨q.1.2, Set.mem_univ _⟩
  refine (h.comp_continuous hcont hmem).congr ?_
  intro q
  rw [Function.comp_apply]
  refine Bundle.TotalSpace.ext rfl (heq_of_eq ?_)
  rw [chartPt, Bundle.Trivialization.symmₗ_apply _ q.1.2]

/-! ## The annulus piece over a chart -/

/-- The annulus piece of the tautological bundle over `U`. -/
def annOver (k m : ℕ) (U : Set (OG k m)) : Set (TM k m) :=
  {p | 1 < fibN k m p ∧ fibN k m p < 2 ∧ p.1 ∈ U}

theorem annSet_inter_proj_eq (k m : ℕ) (U : Set (OG k m)) :
    annSet k m ∩ (tautologicalBundle k m).proj ⁻¹' U = annOver k m U := by
  ext p
  show (1 < fibN k m p ∧ fibN k m p < 2) ∧ (tautologicalBundle k m).proj p ∈ U ↔
    (1 < fibN k m p ∧ fibN k m p < 2 ∧ (tautologicalBundle k m).proj p ∈ U)
  tauto

/-- Normalisation of a vector (defined everywhere; continuous away from `0`). -/
def unitVec (c : Amb k) : Amb k := (‖c‖)⁻¹ • c

theorem norm_unitVec {c : Amb k} (hc : c ≠ 0) : ‖unitVec c‖ = 1 := by
  have hc' : ‖c‖ ≠ 0 := norm_ne_zero_iff.mpr hc
  rw [unitVec, norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr (norm_nonneg c)),
    inv_mul_cancel₀ hc']

theorem unitVec_ne_zero {c : Amb k} (hc : c ≠ 0) : unitVec c ≠ 0 := by
  intro h
  have h2 : ‖unitVec c‖ = 0 := by rw [h, norm_zero]
  rw [norm_unitVec hc] at h2
  exact one_ne_zero h2

theorem unitVec_smul {t : ℝ} (ht : 0 < t) (c : Amb k) : unitVec (t • c) = unitVec c := by
  have hnorm : ‖t • c‖ = t * ‖c‖ := by rw [norm_smul, Real.norm_of_nonneg ht.le]
  rw [unitVec, unitVec, hnorm, smul_smul]
  congr 1
  rw [mul_inv, mul_assoc, mul_comm ‖c‖⁻¹ t, ← mul_assoc, inv_mul_cancel₀ (ne_of_gt ht), one_mul]

theorem unitVec_eq_self {u : Amb k} (hu : ‖u‖ = 1) : unitVec u = u := by
  rw [unitVec, hu, inv_one, one_smul]

theorem norm_coe_sphere (u : ↥(Metric.sphere (0 : Amb k) 1)) : ‖(u : Amb k)‖ = 1 := by
  rw [← dist_zero_right]
  exact Metric.mem_sphere.mp u.2

/-- The chart coordinate of a point of the annulus piece is nonzero. -/
theorem annCoord_ne_zero (S : ChartIdx k m) {U : Set (OG k m)} (hU : U ⊆ baseSet S)
    (p : ↥(annOver k m U)) : ((tautologicalBundle k m).localTriv S p.1).2 ≠ 0 := by
  intro h0
  have h2 : p.1.2 = 0 := (localTriv_snd_eq_zero_iff S (hU p.2.2.2)).mp h0
  have h3 : fibN k m p.1 = 0 := (fibN_eq_zero_iff k m p.1).mpr h2
  linarith [p.2.1, h3]

/-- The forward map: the base point, the normalised chart coordinate, and `fibN`. -/
def annFwd (S : ChartIdx k m) {U : Set (OG k m)} (hU : U ⊆ baseSet S)
    (p : ↥(annOver k m U)) :
    ↥U × ↥(Metric.sphere (0 : Amb k) 1) × ↥(Set.Ioo (1 : ℝ) 2) :=
  (⟨p.1.1, p.2.2.2⟩,
   ⟨unitVec ((tautologicalBundle k m).localTriv S p.1).2,
     by
       rw [Metric.mem_sphere, dist_zero_right]
       exact norm_unitVec (annCoord_ne_zero S hU p)⟩,
   ⟨fibN k m p.1, p.2.1, p.2.2.1⟩)

/-- The chart coordinate on the annulus piece, as a continuous map. -/
theorem continuous_annCoord (S : ChartIdx k m) {U : Set (OG k m)} (hU : U ⊆ baseSet S) :
    Continuous (fun p : ↥(annOver k m U) => ((tautologicalBundle k m).localTriv S p.1).2) := by
  have h1 : Continuous ((tautologicalBundle k m).localTriv S ∘
      (fun p : ↥(annOver k m U) => p.1)) :=
    ContinuousOn.comp_continuous ((tautologicalBundle k m).localTriv S).continuousOn
      continuous_subtype_val (fun p => by
        rw [VectorBundleCore.mem_localTriv_source]
        exact hU p.2.2.2)
  exact continuous_snd.comp h1

theorem continuous_annFwd (S : ChartIdx k m) {U : Set (OG k m)} (hU : U ⊆ baseSet S) :
    Continuous (annFwd S hU) := by
  have hbase : Continuous (fun p : ↥(annOver k m U) => (tautologicalBundle k m).proj p.1) :=
    (tautologicalBundle k m).continuous_proj.comp continuous_subtype_val
  have hcoord := continuous_annCoord S hU
  have hfib : Continuous (fun p : ↥(annOver k m U) => fibN k m p.1) :=
    (fibN_continuous k m).comp continuous_subtype_val
  have hnorm : Continuous (fun p : ↥(annOver k m U) =>
      ‖((tautologicalBundle k m).localTriv S p.1).2‖) := continuous_norm.comp hcoord
  have hne : ∀ p : ↥(annOver k m U), ‖((tautologicalBundle k m).localTriv S p.1).2‖ ≠ 0 :=
    fun p => norm_ne_zero_iff.mpr (annCoord_ne_zero S hU p)
  have hunit : Continuous (fun p : ↥(annOver k m U) =>
      unitVec ((tautologicalBundle k m).localTriv S p.1).2) := by
    rw [show (fun p : ↥(annOver k m U) => unitVec ((tautologicalBundle k m).localTriv S p.1).2)
        = fun p => (‖((tautologicalBundle k m).localTriv S p.1).2‖)⁻¹ •
            ((tautologicalBundle k m).localTriv S p.1).2 from rfl]
    exact (hnorm.inv₀ hne).smul hcoord
  refine Continuous.prodMk (hbase.subtype_mk fun p => p.2.2.2) ?_
  refine Continuous.prodMk (hunit.subtype_mk fun p => ?_) ?_
  · rw [Metric.mem_sphere, dist_zero_right]
    exact norm_unitVec (annCoord_ne_zero S hU p)
  · exact hfib.subtype_mk fun p => ⟨p.2.1, p.2.2.1⟩

/-- The backward map: reconstruct the point from its base point, direction and radius. -/
def annBwd (S : ChartIdx k m) {U : Set (OG k m)} (hU : U ⊆ baseSet S)
    (q : ↥U × ↥(Metric.sphere (0 : Amb k) 1) × ↥(Set.Ioo (1 : ℝ) 2)) : ↥(annOver k m U) :=
  ⟨chartPt S ⟨q.1.1, hU q.1.2⟩
      ((q.2.2.1 * (fibN k m (chartPt S ⟨q.1.1, hU q.1.2⟩ q.2.1.1))⁻¹) • q.2.1.1),
    by
      set f := fibN k m (chartPt S ⟨q.1.1, hU q.1.2⟩ q.2.1.1)
      have hfne : f ≠ 0 := by
        rw [show f = fibN k m (chartPt S ⟨q.1.1, hU q.1.2⟩ q.2.1.1) from rfl,
          ne_eq, chartPt_fibN_eq_zero_iff]
        intro h0
        have h1 := norm_coe_sphere q.2.1
        rw [h0, norm_zero] at h1
        exact one_ne_zero h1.symm
      have hfpos : 0 < f := lt_of_le_of_ne (fibN_nonneg k m _) (Ne.symm hfne)
      have ht : 0 ≤ q.2.2.1 * f⁻¹ :=
        mul_nonneg (le_of_lt (lt_trans zero_lt_one q.2.2.2.1)) (le_of_lt (inv_pos.mpr hfpos))
      have hval : fibN k m (chartPt S ⟨q.1.1, hU q.1.2⟩ ((q.2.2.1 * f⁻¹) • q.2.1.1))
          = q.2.2.1 := by
        rw [fibN_chartPt_smul S ⟨q.1.1, hU q.1.2⟩ ht q.2.1.1]
        rw [show f = fibN k m (chartPt S ⟨q.1.1, hU q.1.2⟩ q.2.1.1) from rfl] at *
        rw [mul_assoc, inv_mul_cancel₀ hfne, mul_one]
      exact ⟨lt_of_lt_of_eq q.2.2.2.1 hval.symm, lt_of_eq_of_lt hval q.2.2.2.2,
        by rw [chartPt_fst]; exact q.1.2⟩⟩

/-- An arithmetic rearrangement used in the inverse laws. -/
theorem annKeyArith {A B C : ℝ} (hB : B = C⁻¹ * A) (hA : A ≠ 0) (hC : C ≠ 0) :
    (A * B⁻¹) * C⁻¹ = 1 := by
  subst hB
  field_simp

theorem annBwd_annFwd (S : ChartIdx k m) {U : Set (OG k m)} (hU : U ⊆ baseSet S)
    (p : ↥(annOver k m U)) : annBwd S hU (annFwd S hU p) = p := by
  refine Subtype.ext ?_
  have hxs : p.1.1 ∈ baseSet S := hU p.2.2.2
  have hcne : ((tautologicalBundle k m).localTriv S p.1).2 ≠ 0 := annCoord_ne_zero S hU p
  have hs0 : fibN k m p.1 ≠ 0 := ne_of_gt (lt_trans zero_lt_one p.2.1)
  have hf : fibN k m (chartPt S ⟨p.1.1, hxs⟩
      (‖((tautologicalBundle k m).localTriv S p.1).2‖⁻¹ •
        ((tautologicalBundle k m).localTriv S p.1).2)) =
      ‖((tautologicalBundle k m).localTriv S p.1).2‖⁻¹ * fibN k m p.1 := by
    rw [fibN_chartPt_smul S ⟨p.1.1, hxs⟩ (inv_nonneg.mpr (norm_nonneg _))
      ((tautologicalBundle k m).localTriv S p.1).2, chartPt_self S hxs]
  have hkey : (fibN k m p.1 * (fibN k m (chartPt S ⟨p.1.1, hxs⟩
      (‖((tautologicalBundle k m).localTriv S p.1).2‖⁻¹ •
        ((tautologicalBundle k m).localTriv S p.1).2)))⁻¹) *
      ‖((tautologicalBundle k m).localTriv S p.1).2‖⁻¹ = 1 := by
    exact annKeyArith (A := fibN k m p.1)
      (B := fibN k m (chartPt S ⟨p.1.1, hxs⟩ (‖((tautologicalBundle k m).localTriv S p.1).2‖⁻¹ •
        ((tautologicalBundle k m).localTriv S p.1).2)))
      (C := ‖((tautologicalBundle k m).localTriv S p.1).2‖) hf hs0 (norm_ne_zero_iff.mpr hcne)
  show chartPt S ⟨p.1.1, hxs⟩
      ((fibN k m p.1 * (fibN k m (chartPt S ⟨p.1.1, hxs⟩
        (unitVec ((tautologicalBundle k m).localTriv S p.1).2)))⁻¹) •
        unitVec ((tautologicalBundle k m).localTriv S p.1).2) = p.1
  rw [show unitVec ((tautologicalBundle k m).localTriv S p.1).2
      = ‖((tautologicalBundle k m).localTriv S p.1).2‖⁻¹ •
        ((tautologicalBundle k m).localTriv S p.1).2 from rfl, smul_smul]
  rw [show (fibN k m p.1 * (fibN k m (chartPt S ⟨p.1.1, hxs⟩
      (‖((tautologicalBundle k m).localTriv S p.1).2‖⁻¹ •
        ((tautologicalBundle k m).localTriv S p.1).2)))⁻¹) *
      ‖((tautologicalBundle k m).localTriv S p.1).2‖⁻¹ = 1 from hkey]
  rw [one_smul, chartPt_self S hxs]

theorem annFwd_annBwd (S : ChartIdx k m) {U : Set (OG k m)} (hU : U ⊆ baseSet S)
    (q : ↥U × ↥(Metric.sphere (0 : Amb k) 1) × ↥(Set.Ioo (1 : ℝ) 2)) :
    annFwd S hU (annBwd S hU q) = q := by
  set f : ℝ := fibN k m (chartPt S ⟨q.1.1, hU q.1.2⟩ (q.2.1 : Amb k))
  have hfne : f ≠ 0 := by
    rw [show f = fibN k m (chartPt S ⟨q.1.1, hU q.1.2⟩ (q.2.1 : Amb k)) from rfl,
      ne_eq, chartPt_fibN_eq_zero_iff]
    intro h0
    have h1 := norm_coe_sphere q.2.1
    rw [h0, norm_zero] at h1
    exact one_ne_zero h1.symm
  have hfpos : 0 < f := lt_of_le_of_ne (fibN_nonneg k m _) (Ne.symm hfne)
  have hs1 : 0 < q.2.2.1 := lt_trans zero_lt_one q.2.2.2.1
  have hkey : fibN k m (chartPt S ⟨q.1.1, hU q.1.2⟩ ((q.2.2.1 * f⁻¹) • (q.2.1 : Amb k)))
      = q.2.2.1 := by
    rw [fibN_chartPt_smul S ⟨q.1.1, hU q.1.2⟩
      (le_of_lt (mul_pos hs1 (inv_pos.mpr hfpos))) (q.2.1 : Amb k)]
    rw [show f = fibN k m (chartPt S ⟨q.1.1, hU q.1.2⟩ (q.2.1 : Amb k)) from rfl] at *
    rw [mul_assoc, inv_mul_cancel₀ hfne, mul_one]
  refine Prod.ext (Subtype.ext ?_) (Prod.ext (Subtype.ext ?_) (Subtype.ext ?_))
  · show (chartPt S ⟨q.1.1, hU q.1.2⟩ ((q.2.2.1 * f⁻¹) • (q.2.1 : Amb k))).1 = q.1.1
    rw [chartPt_fst]
  · show unitVec ((tautologicalBundle k m).localTriv S
        (chartPt S ⟨q.1.1, hU q.1.2⟩ ((q.2.2.1 * f⁻¹) • (q.2.1 : Amb k)))).2
        = (q.2.1 : Amb k)
    rw [chartPt_coord, unitVec_smul (mul_pos hs1 (inv_pos.mpr hfpos)) (q.2.1 : Amb k),
      unitVec_eq_self (norm_coe_sphere q.2.1)]
  · show fibN k m (chartPt S ⟨q.1.1, hU q.1.2⟩ ((q.2.2.1 * f⁻¹) • (q.2.1 : Amb k)))
        = q.2.2.1
    exact hkey

theorem continuous_annBwd (S : ChartIdx k m) {U : Set (OG k m)} (hU : U ⊆ baseSet S) :
    Continuous (annBwd S hU) := by
  have hsub : Continuous (fun q : ↥U × ↥(Metric.sphere (0 : Amb k) 1) × ↥(Set.Ioo (1 : ℝ) 2) =>
      (⟨q.1.1, hU q.1.2⟩ : ↥(baseSet S))) :=
    Continuous.subtype_mk (continuous_subtype_val.comp continuous_fst) _
  have hvec : Continuous (fun q : ↥U × ↥(Metric.sphere (0 : Amb k) 1) × ↥(Set.Ioo (1 : ℝ) 2) =>
      (q.2.1 : Amb k)) := continuous_subtype_val.comp (continuous_fst.comp continuous_snd)
  have hchart : Continuous (fun q : ↥U × ↥(Metric.sphere (0 : Amb k) 1) × ↥(Set.Ioo (1 : ℝ) 2) =>
      chartPt S (⟨q.1.1, hU q.1.2⟩ : ↥(baseSet S)) (q.2.1 : Amb k)) :=
    (continuous_chartPt S).comp (hsub.prodMk hvec)
  have hfib : Continuous (fun q : ↥U × ↥(Metric.sphere (0 : Amb k) 1) × ↥(Set.Ioo (1 : ℝ) 2) =>
      fibN k m (chartPt S (⟨q.1.1, hU q.1.2⟩ : ↥(baseSet S)) (q.2.1 : Amb k))) :=
    (fibN_continuous k m).comp hchart
  have hne : ∀ q : ↥U × ↥(Metric.sphere (0 : Amb k) 1) × ↥(Set.Ioo (1 : ℝ) 2),
      fibN k m (chartPt S (⟨q.1.1, hU q.1.2⟩ : ↥(baseSet S)) (q.2.1 : Amb k)) ≠ 0 := by
    intro q
    rw [ne_eq, chartPt_fibN_eq_zero_iff]
    intro h0
    have h1 := norm_coe_sphere q.2.1
    rw [h0, norm_zero] at h1
    exact one_ne_zero h1.symm
  have hscal : Continuous (fun q : ↥U × ↥(Metric.sphere (0 : Amb k) 1) × ↥(Set.Ioo (1 : ℝ) 2) =>
      q.2.2.1 * (fibN k m (chartPt S (⟨q.1.1, hU q.1.2⟩ : ↥(baseSet S))
        (q.2.1 : Amb k)))⁻¹) :=
    (continuous_subtype_val.comp (continuous_snd.comp continuous_snd)).mul (hfib.inv₀ hne)
  have hpair : Continuous (fun q : ↥U × ↥(Metric.sphere (0 : Amb k) 1) × ↥(Set.Ioo (1 : ℝ) 2) =>
      ((⟨q.1.1, hU q.1.2⟩ : ↥(baseSet S)),
        (q.2.2.1 * (fibN k m (chartPt S (⟨q.1.1, hU q.1.2⟩ : ↥(baseSet S))
          (q.2.1 : Amb k)))⁻¹) • (q.2.1 : Amb k))) :=
    hsub.prodMk (hscal.smul hvec)
  have hout : Continuous (fun q : ↥U × ↥(Metric.sphere (0 : Amb k) 1) × ↥(Set.Ioo (1 : ℝ) 2) =>
      chartPt S (⟨q.1.1, hU q.1.2⟩ : ↥(baseSet S))
        ((q.2.2.1 * (fibN k m (chartPt S (⟨q.1.1, hU q.1.2⟩ : ↥(baseSet S))
          (q.2.1 : Amb k)))⁻¹) • (q.2.1 : Amb k))) :=
    (continuous_chartPt S).comp hpair
  exact hout.subtype_mk _

/-- **The annulus piece over a chart is a product**: for `U ⊆ baseSet S`, the part of the
annulus `1 < fibN < 2` over `U` is homeomorphic to `U × S^{k-1} × (1,2)`. -/
noncomputable def annOverHomeomorph (S : ChartIdx k m) {U : Set (OG k m)}
    (hU : U ⊆ baseSet S) :
    ↥(annOver k m U) ≃ₜ ↥U × ↥(Metric.sphere (0 : Amb k) 1) × ↥(Set.Ioo (1 : ℝ) 2) where
  toFun := annFwd S hU
  invFun := annBwd S hU
  left_inv := annBwd_annFwd S hU
  right_inv := annFwd_annBwd S hU
  continuous_toFun := continuous_annFwd S hU
  continuous_invFun := continuous_annBwd S hU

end

end Work.ThomBordism.Grassmann.Torsion
