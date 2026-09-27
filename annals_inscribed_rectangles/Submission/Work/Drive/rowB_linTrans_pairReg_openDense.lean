import Mathlib
import Submission.Work.Drive.analyticDensity
import Submission.Work.Drive.classRowVocab
import Submission.Work.Drive.linShearCharts
import Submission.Work.Drive.pairReg_linPlaneCharts_of_incidence
import Submission.Work.Drive.linShearIncidence

namespace Work.Drive

open scoped Topology ContDiff

noncomputable section

set_option maxHeartbeats 2000000

/-! ## 0. The relative-density toolkit -/

/-- **A finite family of open conditions, dense at every point of the closed unit ball, has a common
point in every ball around any point of the open unit ball.**  (A copy of the workspace lemma
`Work.Drive.exists_mem_all_near_of_isOpen_dense_fintype`, reproduced here with a private name so that
this file does not have to import the design's genericity chain.) -/
theorem rb_exists_mem_all_near {n : ℕ} {ι : Type*} [Fintype ι]
    (P : ι → Set (EuclideanSpace ℝ (Fin n)))
    (hopen : ∀ i, IsOpen (P i))
    (hdense : ∀ i, DenseAtBall (P i))
    {x : EuclideanSpace ℝ (Fin n)} (hx : ‖x‖ < 1) (ε : ℝ) (hε : 0 < ε) :
    ∃ y, ‖y - x‖ < ε ∧ ∀ i, y ∈ P i := by
  classical
  set r : ℝ := (1 - ‖x‖) / 2 with hrdef
  have hrpos : 0 < r := by rw [hrdef]; linarith
  set ε₁ : ℝ := min ε r with hε₁def
  have hε₁pos : 0 < ε₁ := lt_min hε hrpos
  have hε₁ε : ε₁ ≤ ε := by rw [hε₁def]; exact min_le_left _ _
  have hε₁r : ε₁ ≤ r := by rw [hε₁def]; exact min_le_right _ _
  have key : ∀ S : Finset ι, ∃ y, ‖y - x‖ < ε₁ ∧ ∀ i ∈ S, y ∈ P i := by
    intro S
    induction S using Finset.induction_on with
    | empty => exact ⟨x, by simpa using hε₁pos, by simp⟩
    | insert i S hi ih =>
        obtain ⟨y, hyx, hyS⟩ := ih
        have hy1 : ‖y‖ ≤ 1 := by
          have h : ‖y‖ ≤ ‖y - x‖ + ‖x‖ := by
            have h2 := norm_add_le (y - x) x
            rwa [sub_add_cancel] at h2
          linarith
        have hOpenS : IsOpen (⋂ j ∈ S, P j) := isOpen_biInter_finset (fun j _ => hopen j)
        have hyMem : y ∈ ⋂ j ∈ S, P j := Set.mem_iInter₂.mpr hyS
        obtain ⟨δ₂, hδ₂pos, hδ₂sub⟩ := Metric.isOpen_iff.mp hOpenS y hyMem
        obtain ⟨y', hy'P, hy'y⟩ := hdense i y hy1 (min δ₂ (ε₁ - ‖y - x‖))
          (lt_min hδ₂pos (by linarith))
        refine ⟨y', ?_, ?_⟩
        · have h1 : ‖y' - y‖ < ε₁ - ‖y - x‖ := lt_of_lt_of_le hy'y (min_le_right _ _)
          have h2 : ‖y' - x‖ ≤ ‖y' - y‖ + ‖y - x‖ := by
            have h3 := norm_add_le (y' - y) (y - x)
            rwa [sub_add_sub_cancel] at h3
          linarith
        · intro j hj
          rcases Finset.mem_insert.mp hj with rfl | hjS
          · exact hy'P
          · have hmem : y' ∈ ⋂ j ∈ S, P j := hδ₂sub (by
              rw [Metric.mem_ball, dist_eq_norm]
              exact lt_of_lt_of_le hy'y (min_le_left _ _))
            exact Set.mem_iInter₂.mp hmem j hjS
  obtain ⟨y, hy, hyall⟩ := key Finset.univ
  exact ⟨y, lt_of_lt_of_le hy hε₁ε, fun i => hyall i (Finset.mem_univ i)⟩

/-- **A finite intersection of open sets dense at every point of the closed unit ball is again dense
at every such point.**  (The centre may lie on the boundary `‖x‖ = 1`; one first moves strictly
inside.) -/
theorem rb_denseAtBall_iInter {n : ℕ} {ι : Type*} [Fintype ι]
    {P : ι → Set (EuclideanSpace ℝ (Fin n))}
    (hopen : ∀ i, IsOpen (P i)) (hdense : ∀ i, DenseAtBall (P i)) :
    DenseAtBall (⋂ i, P i) := by
  intro x hx ε hε
  obtain ⟨x', hx'1, hx'd⟩ := exists_norm_lt_one_near x hx (by linarith : (0:ℝ) < ε / 2)
  obtain ⟨y, hyε, hyall⟩ := rb_exists_mem_all_near P hopen hdense hx'1 (ε / 2) (by linarith)
  refine ⟨y, Set.mem_iInter.mpr hyall, ?_⟩
  calc ‖y - x‖ ≤ ‖y - x'‖ + ‖x' - x‖ := by
        have h := norm_add_le (y - x') (x' - x)
        rwa [sub_add_sub_cancel] at h
    _ < ε / 2 + ε / 2 := by linarith
    _ = ε := by ring

theorem rb_denseAtBall_union {n : ℕ} {s t : Set (EuclideanSpace ℝ (Fin n))}
    (hs : DenseAtBall s) : DenseAtBall (s ∪ t) := by
  intro x hx ε hε
  obtain ⟨y, hy, hyd⟩ := hs x hx ε hε
  exact ⟨y, Or.inl hy, hyd⟩

/-- **A two-fold intersection of sets open and dense at every point of the closed unit ball.** -/
theorem rb_denseAtBall_inter {n : ℕ} {s t : Set (EuclideanSpace ℝ (Fin n))}
    (hso : IsOpen s) (hto : IsOpen t) (hs : DenseAtBall s) (ht : DenseAtBall t) :
    DenseAtBall (s ∩ t) := by
  have hopen : ∀ i : Fin 2, IsOpen (![s, t] i) := by
    intro i; fin_cases i
    · simpa using hso
    · simpa using hto
  have hdense : ∀ i : Fin 2, DenseAtBall (![s, t] i) := by
    intro i; fin_cases i
    · simpa using hs
    · simpa using ht
  have h := rb_denseAtBall_iInter (P := fun i : Fin 2 => ![s, t] i) hopen hdense
  have hset : (⋂ i : Fin 2, ![s, t] i) = s ∩ t := by
    ext x
    simp [Fin.forall_fin_two]
  rwa [hset] at h

/-- **The non-vanishing set of a finite disjunction of analytic functions, one of which is not
identically zero.** -/
theorem rb_open_dense_union {n : ℕ} {f g : EuclideanSpace ℝ (Fin n) → ℝ}
    (hf : ∀ x, AnalyticAt ℝ f x) (hg : ∀ x, AnalyticAt ℝ g x)
    (h : (∃ x, f x ≠ 0) ∨ (∃ x, g x ≠ 0)) :
    IsOpen {x | f x ≠ 0 ∨ g x ≠ 0} ∧ DenseAtBall {x | f x ≠ 0 ∨ g x ≠ 0} := by
  have hset : {x : EuclideanSpace ℝ (Fin n) | f x ≠ 0 ∨ g x ≠ 0}
      = {x | f x ≠ 0} ∪ {x | g x ≠ 0} := by
    ext x; simp only [Set.mem_setOf_eq, Set.mem_union]
  have hopenf : IsOpen {x : EuclideanSpace ℝ (Fin n) | f x ≠ 0} :=
    isOpen_ne_fun (continuous_iff_continuousAt.mpr fun x => (hf x).continuousAt) continuous_const
  have hopeng : IsOpen {x : EuclideanSpace ℝ (Fin n) | g x ≠ 0} :=
    isOpen_ne_fun (continuous_iff_continuousAt.mpr fun x => (hg x).continuousAt) continuous_const
  refine ⟨?_, ?_⟩
  · rw [hset]; exact hopenf.union hopeng
  · rw [hset]
    rcases h with ⟨x0, hx0⟩ | ⟨x0, hx0⟩
    · exact rb_denseAtBall_union (isOpen_denseAtBall_ne_zero hf ⟨x0, hx0⟩).2
    · rw [Set.union_comm]
      exact rb_denseAtBall_union (isOpen_denseAtBall_ne_zero hg ⟨x0, hx0⟩).2

/-! ## 1. The transported linear models of the row `PairReg lin₀ lin₁` -/

/-- **The transported `k`-th linear chart** at the design parameter `t`: the sheared linear chart
`L k = linBase A k` followed by the class transport `classEquiv (blk k t)`. -/
def rbPsi (A : Eucl 3 ≃L[ℝ] Eucl 3) (k : Fin 3) (t : EuclideanSpace ℝ (Fin 12)) :
    Eucl 3 ≃L[ℝ] Eucl 3 :=
  (linBase A k).trans (classEquiv (blk k t))

/-- The coordinate functional `v ↦ v j` of `Eucl 3 = ℝ⁴`. -/
def rbProj (j : Fin 4) : Eucl 3 →L[ℝ] ℝ :=
  PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 4 => ℝ) j

lemma rbProj_apply (j : Fin 4) (v : Eucl 3) : rbProj j v = v j := rfl

/-- The coordinate functional `v ↦ ((L k)⁻¹ v) j` of the `k`-th linear chart. -/
def rbCoord (A : Eucl 3 ≃L[ℝ] Eucl 3) (k : Fin 3) (j : Fin 4) : Eucl 3 →L[ℝ] ℝ :=
  LinearMap.toContinuousLinearMap
    ((rbProj j).toLinearMap.comp (linBase A k).symm.toLinearMap)

/-- The normal functional of the `k`-th linear chart, as a continuous linear functional. -/
def rbFun (A : Eucl 3 ≃L[ℝ] Eucl 3) (k : Fin 3) : Eucl 3 →L[ℝ] ℝ := rbCoord A k 3

lemma rbCoord_apply (A : Eucl 3 ≃L[ℝ] Eucl 3) (k : Fin 3) (j : Fin 4) (v : Eucl 3) :
    rbCoord A k j v = ((linBase A k).symm v) j := by
  simp [rbCoord, rbProj]

lemma rbFun_apply (A : Eucl 3 ≃L[ℝ] Eucl 3) (k : Fin 3) (v : Eucl 3) :
    rbFun A k v = linFun (linBase A k) v := by
  rw [linFun_apply, rbFun, rbCoord_apply]

/-- **The numerator of the transported normal functional.**  The transported normal functional of the
`k`-th chart evaluated at the class transport of the fixed vector `v` by the `u`-th class parameter
equals `(1 + ‖τ_k‖²)⁻¹` times `rbNum` (and `rbNum` is a polynomial in `t`). -/
def rbNum (B : Eucl 3 →L[ℝ] ℝ) (k u : Fin 3) (v : Eucl 3)
    (t : EuclideanSpace ℝ (Fin 12)) : ℝ :=
  B (classEquiv (blk u t) v - classGen (blk k t) (classEquiv (blk u t) v))

/-- The explicit inverse of the class equivalence, applied to a vector. -/
lemma rbClassEquiv_symm_apply (t w : Eucl 3) :
    (classEquiv t).symm w = (1 + classNormSq t)⁻¹ • (w - classGen t w) := by
  have hpos : (0 : ℝ) < 1 + classNormSq t := by linarith [classNormSq_nonneg t]
  have hco : ((classEquiv t : Eucl 3 →L[ℝ] Eucl 3)) = (1 + classGen t : Eucl 3 →L[ℝ] Eucl 3) := by
    refine ContinuousLinearMap.ext fun v => ?_
    rw [show ((classEquiv t : Eucl 3 →L[ℝ] Eucl 3)) v = v + classGen t v from classEquiv_apply t v]
    rfl
  have hkey : ((classEquiv t : Eucl 3 →L[ℝ] Eucl 3)) (w - classGen t w)
      = (1 + classNormSq t) • w := by
    rw [hco]
    have h3 : (w - classGen t w) = ((1 - classGen t : Eucl 3 →L[ℝ] Eucl 3)) w := rfl
    rw [h3, classGen_mul_sub]
  rw [ContinuousLinearEquiv.symm_apply_eq]
  change w = ((classEquiv t : Eucl 3 →L[ℝ] Eucl 3)) ((1 + classNormSq t)⁻¹ • (w - classGen t w))
  rw [ContinuousLinearMap.map_smul, hkey, smul_smul, inv_mul_cancel₀ (ne_of_gt hpos), one_smul]

/-- The normal functional of a composite chart. -/
lemma rbLinFun_trans (e₁ e₂ : Eucl 3 ≃L[ℝ] Eucl 3) (v : Eucl 3) :
    linFun (e₁.trans e₂) v = linFun e₁ (e₂.symm v) := by
  rw [linFun_apply, linFun_apply, ContinuousLinearEquiv.symm_trans_apply]

/-- **The key identity**: the transported normal functional at the class transport of a fixed vector
is a positive multiple of the polynomial numerator `rbNum`. -/
lemma linFun_rbPsi (A : Eucl 3 ≃L[ℝ] Eucl 3) (k u : Fin 3) (v : Eucl 3)
    (t : EuclideanSpace ℝ (Fin 12)) :
    linFun (rbPsi A k t) (classEquiv (blk u t) v)
      = (1 + classNormSq (blk k t))⁻¹ * rbNum (rbFun A k) k u v t := by
  rw [rbPsi, rbLinFun_trans, rbClassEquiv_symm_apply]
  rw [map_smul]
  simp only [smul_eq_mul]
  rfl

/-- **The non-vanishing equivalence**: the transported normal functional vanishes at the class
transport of `v` exactly when the polynomial numerator does. -/
lemma linFun_rbPsi_ne_zero_iff (A : Eucl 3 ≃L[ℝ] Eucl 3) (k u : Fin 3) (v : Eucl 3)
    (t : EuclideanSpace ℝ (Fin 12)) :
    linFun (rbPsi A k t) (classEquiv (blk u t) v) ≠ 0 ↔ rbNum (rbFun A k) k u v t ≠ 0 := by
  rw [linFun_rbPsi]
  have hpos : (0 : ℝ) < 1 + classNormSq (blk k t) := by
    linarith [classNormSq_nonneg (blk k t)]
  constructor
  · intro h hN
    exact h (by rw [hN, mul_zero])
  · intro hN h0
    exact hN ((mul_eq_zero.mp h0).resolve_left (inv_ne_zero (ne_of_gt hpos)))


/-- **Monotonicity of relative density.** -/
theorem rb_denseAtBall_mono {n : ℕ} {s t : Set (EuclideanSpace ℝ (Fin n))}
    (h : DenseAtBall s) (hst : s ⊆ t) : DenseAtBall t := by
  intro x hx ε hε
  obtain ⟨y, hy, hyd⟩ := h x hx ε hε
  exact ⟨y, hst hy, hyd⟩

/-! ## 2. The linear-algebra equivalences of the incidence criterion -/

/-- A vector of `Eucl 3 = ℝ⁴` lies in `span {e₀, e₁}` exactly when its last two coordinates
vanish. -/
lemma rb_mem_span_e0e1_iff (v : Eucl 3) :
    v ∈ Submodule.span ℝ ({linE0, linE1} : Set (Eucl 3)) ↔ v 2 = 0 ∧ v 3 = 0 := by
  constructor
  · intro hv
    have hle : Submodule.span ℝ ({linE0, linE1} : Set (Eucl 3))
        ≤ (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 4 => ℝ) 2).ker
          ⊓ (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 4 => ℝ) 3).ker := by
      rw [Submodule.span_le]
      intro w hw
      rw [Set.mem_insert_iff, Set.mem_singleton_iff] at hw
      rcases hw with rfl | rfl
      · refine ⟨?_, ?_⟩ <;> simp [linE0]
      · refine ⟨?_, ?_⟩ <;> simp [linE1]
    have h2 := hle hv
    rw [Submodule.mem_inf] at h2
    exact ⟨by simpa using h2.1, by simpa using h2.2⟩
  · rintro ⟨h2, h3⟩
    have hdecomp : v = (v 0) • linE0 + (v 1) • linE1 := by
      ext i; fin_cases i <;> simp [linE0, linE1, h2, h3]
    rw [hdecomp]
    exact Submodule.add_mem _ (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
      (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))

/-- **The boundary line `linBdry Φ = Φ (span {e₀,e₁})` in coordinates**: a vector lies on the
boundary line exactly when the last two coordinates of its `Φ`-preimage vanish. -/
lemma rb_mem_linBdry_iff (Φ : Eucl 3 ≃L[ℝ] Eucl 3) (w : Eucl 3) :
    w ∈ linBdry Φ ↔ (Φ.symm w) 2 = 0 ∧ (Φ.symm w) 3 = 0 := by
  constructor
  · intro hw
    obtain ⟨z, hz, hzw⟩ := Submodule.mem_map.mp
      (show w ∈ (Submodule.span ℝ ({linE0, linE1} : Set (Eucl 3))).map Φ.toLinearEquiv.toLinearMap
        from hw)
    have hsym : Φ.symm w = z := by rw [← hzw]; simp
    rw [hsym]
    exact rb_mem_span_e0e1_iff z |>.mp hz
  · intro h
    refine Submodule.mem_map.mpr ⟨Φ.symm w, (rb_mem_span_e0e1_iff _).mpr h, ?_⟩
    simp

/-- A hyperplane contains the boundary line of a chart exactly when it contains the two images of
`e₀` and `e₁`. -/
lemma rb_linBdry_le_ker_iff (ℓ : Eucl 3 →ₗ[ℝ] ℝ) (Φ : Eucl 3 ≃L[ℝ] Eucl 3) :
    linBdry Φ ≤ ℓ.ker ↔ ℓ (Φ linE0) = 0 ∧ ℓ (Φ linE1) = 0 := by
  constructor
  · intro h
    refine ⟨LinearMap.mem_ker.mp (h ?_), LinearMap.mem_ker.mp (h ?_)⟩
    · exact Submodule.mem_map.mpr ⟨linE0, Submodule.subset_span (by simp), rfl⟩
    · exact Submodule.mem_map.mpr ⟨linE1, Submodule.subset_span (by simp), rfl⟩
  · rintro ⟨h0, h1⟩ v hv
    rw [LinearMap.mem_ker]
    obtain ⟨z, hz, hzv⟩ := Submodule.mem_map.mp
      (show v ∈ (Submodule.span ℝ ({linE0, linE1} : Set (Eucl 3))).map Φ.toLinearEquiv.toLinearMap
        from hv)
    obtain ⟨a, b, hab⟩ := Submodule.mem_span_pair.mp hz
    rw [← hzv, ← hab]
    simp [map_add, map_smul, h0, h1]

/-- **The second incidence condition**: `linBdry Φ₀` is not contained in the plane of `Φ₁` exactly
when the normal functional of `Φ₁` is nonzero at one of the two images of the generators of `e₀`,
`e₁`. -/
lemma rb_not_linBdry_le_linSub_iff (Φ₀ Φ₁ : Eucl 3 ≃L[ℝ] Eucl 3) :
    ¬ linBdry Φ₀ ≤ linSub Φ₁ ↔ linFun Φ₁ (Φ₀ linE0) ≠ 0 ∨ linFun Φ₁ (Φ₀ linE1) ≠ 0 := by
  rw [← ker_linFun Φ₁, rb_linBdry_le_ker_iff]
  constructor
  · intro hh
    by_cases h0 : linFun Φ₁ (Φ₀ linE0) = 0
    · right; exact fun h1 => hh ⟨h0, h1⟩
    · left; exact h0
  · rintro (h0 | h1) ⟨ha, hb⟩
    · exact h0 ha
    · exact h1 hb

/-- **The fourth and fifth incidence conditions** in functional form. -/
lemma rb_not_mem_linSub_iff (Φ : Eucl 3 ≃L[ℝ] Eucl 3) (v : Eucl 3) :
    v ∉ linSub Φ ↔ linFun Φ v ≠ 0 := by
  rw [← ker_linFun Φ]
  simp

/-- **The sixth incidence condition, half of it**: the plane of `Φ₀` is not contained in the plane of
`Φ₁` exactly when the normal functional of `Φ₁` does not vanish on all of
`Φ₀ (span {linVecC 1, linVecC I, linVecC 0})`, which is `Φ₀` of the standard plane. -/
lemma rb_not_linSub_le_iff (Φ₀ Φ₁ : Eucl 3 ≃L[ℝ] Eucl 3) :
    ¬ linSub Φ₀ ≤ linSub Φ₁ ↔
      (linFun Φ₁ (Φ₀ (linVecC 1)) ≠ 0 ∨ linFun Φ₁ (Φ₀ (linVecC Complex.I)) ≠ 0 ∨
       linFun Φ₁ (Φ₀ (linVecC 0)) ≠ 0) := by
  constructor
  · intro h
    by_contra hc
    push Not at hc
    obtain ⟨hc1, hc2, hc3⟩ := hc
    refine h ?_
    intro v hv
    rw [← ker_linFun Φ₁, LinearMap.mem_ker]
    obtain ⟨z, hz, hzv⟩ := Submodule.mem_map.mp
      (show v ∈ linStd.map Φ₀.toLinearEquiv.toLinearMap from hv)
    have hz3 : z 3 = 0 := by
      have hmem : z ∈ LinearMap.ker linStdCoord := by rwa [← linStd_eq_ker_coord]
      simpa [linStdCoord_apply] using (LinearMap.mem_ker.mp hmem)
    have hdec := eq_smul_linVecC z hz3
    rw [← hzv, hdec]
    simp [map_add, map_smul, hc1, hc2, hc3]
  · rintro (h1 | h2 | h3) hle
    · have hmem : Φ₀ (linVecC 1) ∈ linSub Φ₁ :=
        hle (Submodule.mem_map.mpr ⟨linVecC 1, linVecC_mem_linStd 1, rfl⟩)
      exact h1 (LinearMap.mem_ker.mp (by rwa [ker_linFun Φ₁]))
    · have hmem : Φ₀ (linVecC Complex.I) ∈ linSub Φ₁ :=
        hle (Submodule.mem_map.mpr ⟨linVecC Complex.I, linVecC_mem_linStd Complex.I, rfl⟩)
      exact h2 (LinearMap.mem_ker.mp (by rwa [ker_linFun Φ₁]))
    · have hmem : Φ₀ (linVecC 0) ∈ linSub Φ₁ :=
        hle (Submodule.mem_map.mpr ⟨linVecC 0, linVecC_mem_linStd 0, rfl⟩)
      exact h3 (LinearMap.mem_ker.mp (by rwa [ker_linFun Φ₁]))

/-- **The sixth incidence condition**: the two planes differ exactly when one of the two contains a
point that the other's normal functional does not annihilate. -/
lemma rb_linSub_ne_iff (Φ₀ Φ₁ : Eucl 3 ≃L[ℝ] Eucl 3) :
    linSub Φ₀ ≠ linSub Φ₁ ↔
      ((linFun Φ₁ (Φ₀ (linVecC 1)) ≠ 0 ∨ linFun Φ₁ (Φ₀ (linVecC Complex.I)) ≠ 0 ∨
        linFun Φ₁ (Φ₀ (linVecC 0)) ≠ 0) ∨
       (linFun Φ₀ (Φ₁ (linVecC 1)) ≠ 0 ∨ linFun Φ₀ (Φ₁ (linVecC Complex.I)) ≠ 0 ∨
        linFun Φ₀ (Φ₁ (linVecC 0)) ≠ 0)) := by
  constructor
  · intro hne
    by_cases h : linSub Φ₀ ≤ linSub Φ₁
    · have h' : ¬ linSub Φ₁ ≤ linSub Φ₀ := fun h'' => hne (le_antisymm h h'')
      exact Or.inr ((rb_not_linSub_le_iff Φ₁ Φ₀).mp h')
    · exact Or.inl ((rb_not_linSub_le_iff Φ₀ Φ₁).mp h)
  · rintro (h | h)
    · intro heq
      exact ((rb_not_linSub_le_iff Φ₀ Φ₁).mpr h) (le_of_eq heq)
    · intro heq
      exact ((rb_not_linSub_le_iff Φ₁ Φ₀).mpr h) (le_of_eq heq.symm)

/-- **The first incidence condition**: the two boundary lines meet only in `0` exactly when the
`(2,3)`-minor of the composite `Φ₁⁻¹ ∘ Φ₀` on `span {e₀, e₁}` does not vanish. -/
lemma rb_linBdry_inf_eq_bot_iff (Φ₀ Φ₁ : Eucl 3 ≃L[ℝ] Eucl 3) :
    linBdry Φ₀ ⊓ linBdry Φ₁ = ⊥ ↔
      ((Φ₁.symm (Φ₀ linE0)) 2) * ((Φ₁.symm (Φ₀ linE1)) 3)
        - ((Φ₁.symm (Φ₀ linE0)) 3) * ((Φ₁.symm (Φ₀ linE1)) 2) ≠ 0 := by
  set a : ℝ := (Φ₁.symm (Φ₀ linE0)) 2 with ha
  set c : ℝ := (Φ₁.symm (Φ₀ linE0)) 3 with hc
  set b : ℝ := (Φ₁.symm (Φ₀ linE1)) 2 with hb
  set d : ℝ := (Φ₁.symm (Φ₀ linE1)) 3 with hd
  have hcoord : ∀ (i : Fin 4) (α β : ℝ),
      (Φ₁.symm (Φ₀ (α • linE0 + β • linE1))) i
        = α * ((Φ₁.symm (Φ₀ linE0)) i) + β * ((Φ₁.symm (Φ₀ linE1)) i) := by
    intro i α β
    rw [map_add, map_smul, map_smul]
    simp [map_add, map_smul, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
  have hE0ne : (linE0 : Eucl 3) ≠ 0 := by simp [linE0]
  constructor
  · intro hbot hD
    have huB : (d • linE0 - c • linE1 : Eucl 3)
        ∈ Submodule.span ℝ ({linE0, linE1} : Set (Eucl 3)) := by
      rw [rb_mem_span_e0e1_iff]
      constructor <;> simp [PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul, linE0, linE1]
    have hshape : (d • linE0 - c • linE1 : Eucl 3) = d • linE0 + (-c) • linE1 := by
      rw [sub_eq_add_neg, neg_smul]
    have hu2 : (Φ₁.symm (Φ₀ (d • linE0 - c • linE1))) 2 = 0 := by
      rw [hshape, hcoord 2 d (-c), ← ha, ← hb]
      linear_combination hD
    have hu3 : (Φ₁.symm (Φ₀ (d • linE0 - c • linE1))) 3 = 0 := by
      rw [hshape, hcoord 3 d (-c), ← hc, ← hd]
      ring
    have hu : Φ₀ (d • linE0 - c • linE1) ∈ linBdry Φ₀ ⊓ linBdry Φ₁ :=
      ⟨Submodule.mem_map.mpr ⟨_, huB, rfl⟩, (rb_mem_linBdry_iff Φ₁ _).mpr ⟨hu2, hu3⟩⟩
    have hu0 : Φ₀ (d • linE0 - c • linE1) = 0 := by
      have h := hu
      rw [hbot] at h
      simpa using h
    have hdc : (d • linE0 - c • linE1 : Eucl 3) = 0 := Φ₀.injective (by rw [hu0, map_zero])
    have hd0 : d = 0 := by
      have h := congrArg (fun v : Eucl 3 => v 0) hdc
      simpa [PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul, linE0, linE1] using h
    have hc0 : c = 0 := by
      have h := congrArg (fun v : Eucl 3 => v 1) hdc
      simpa [PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul, linE0, linE1] using h
    have hu'B : (b • linE0 - a • linE1 : Eucl 3)
        ∈ Submodule.span ℝ ({linE0, linE1} : Set (Eucl 3)) := by
      rw [rb_mem_span_e0e1_iff]
      constructor <;> simp [PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul, linE0, linE1]
    have hshape' : (b • linE0 - a • linE1 : Eucl 3) = b • linE0 + (-a) • linE1 := by
      rw [sub_eq_add_neg, neg_smul]
    have hu'2 : (Φ₁.symm (Φ₀ (b • linE0 - a • linE1))) 2 = 0 := by
      rw [hshape', hcoord 2 b (-a), ← ha, ← hb]
      ring
    have hu'3 : (Φ₁.symm (Φ₀ (b • linE0 - a • linE1))) 3 = 0 := by
      rw [hshape', hcoord 3 b (-a), ← hc, ← hd, hc0, hd0]
      ring
    have hu' : Φ₀ (b • linE0 - a • linE1) ∈ linBdry Φ₀ ⊓ linBdry Φ₁ :=
      ⟨Submodule.mem_map.mpr ⟨_, hu'B, rfl⟩, (rb_mem_linBdry_iff Φ₁ _).mpr ⟨hu'2, hu'3⟩⟩
    have hu'0 : Φ₀ (b • linE0 - a • linE1) = 0 := by
      have h := hu'
      rw [hbot] at h
      simpa using h
    have hba : (b • linE0 - a • linE1 : Eucl 3) = 0 := Φ₀.injective (by rw [hu'0, map_zero])
    have hb0 : b = 0 := by
      have h := congrArg (fun v : Eucl 3 => v 0) hba
      simpa [PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul, linE0, linE1] using h
    have ha0 : a = 0 := by
      have h := congrArg (fun v : Eucl 3 => v 1) hba
      simpa [PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul, linE0, linE1] using h
    have hz : Φ₀ linE0 ∈ linBdry Φ₀ ⊓ linBdry Φ₁ := by
      refine ⟨Submodule.mem_map.mpr ⟨linE0, Submodule.subset_span (by simp), rfl⟩, ?_⟩
      refine (rb_mem_linBdry_iff Φ₁ _).mpr ⟨?_, ?_⟩
      · rw [← ha]; exact ha0
      · rw [← hc]; exact hc0
    have hz0 : Φ₀ linE0 = 0 := by
      have h := hz
      rw [hbot] at h
      simpa using h
    exact hE0ne (Φ₀.injective (by rw [hz0, map_zero]))
  · intro hD
    have hdet : a * d - b * c ≠ 0 := fun h => hD (by rw [mul_comm c b]; exact h)
    rw [Submodule.eq_bot_iff]
    intro w hw
    rw [Submodule.mem_inf] at hw
    obtain ⟨hw0, hw1⟩ := hw
    obtain ⟨hz2, hz3⟩ := (rb_mem_linBdry_iff Φ₀ w).mp hw0
    obtain ⟨hf2, hf3⟩ := (rb_mem_linBdry_iff Φ₁ w).mp hw1
    have hzB : Φ₀.symm w ∈ Submodule.span ℝ ({linE0, linE1} : Set (Eucl 3)) :=
      (rb_mem_span_e0e1_iff _).mpr ⟨hz2, hz3⟩
    obtain ⟨α, β, hab⟩ := Submodule.mem_span_pair.mp hzB
    have hwΦ : w = Φ₀ (α • linE0 + β • linE1) := by
      rw [hab, ContinuousLinearEquiv.apply_symm_apply]
    have e2 : α * a + β * b = 0 := by
      have h := hf2
      rw [hwΦ, hcoord 2 α β, ← ha, ← hb] at h
      exact h
    have e3 : α * c + β * d = 0 := by
      have h := hf3
      rw [hwΦ, hcoord 3 α β, ← hc, ← hd] at h
      exact h
    have hα : α = 0 := by
      have hmul : α * (a * d - b * c) = 0 := by linear_combination d * e2 - b * e3
      exact (mul_eq_zero.mp hmul).resolve_right hdet
    have hβ : β = 0 := by
      have hbd : b ≠ 0 ∨ d ≠ 0 := by
        by_contra hcon
        push Not at hcon
        rw [hcon.1, hcon.2] at hdet
        simp at hdet
      rcases hbd with hb0 | hd0
      · have h : β * b = 0 := by simpa [hα] using e2
        exact (mul_eq_zero.mp h).resolve_right hb0
      · have h : β * d = 0 := by simpa [hα] using e3
        exact (mul_eq_zero.mp h).resolve_right hd0
    rw [hwΦ, hα, hβ, zero_smul, zero_smul, add_zero, map_zero]

/-! ## 3. The transported normal functionals -/

/-- The inverse of the transported chart, in coordinates. -/
lemma rb_outer_symm_coord (A : Eucl 3 ≃L[ℝ] Eucl 3) (k : Fin 3) (j : Fin 4) (u : Fin 3)
    (v : Eucl 3) (t : EuclideanSpace ℝ (Fin 12)) :
    ((rbPsi A k t).symm (classEquiv (blk u t) v)) j
      = (1 + classNormSq (blk k t))⁻¹ * rbNum (rbCoord A k j) k u v t := by
  rw [rbPsi, ContinuousLinearEquiv.symm_trans_apply, rbClassEquiv_symm_apply]
  simp only [map_smul, PiLp.smul_apply, smul_eq_mul]
  rfl

/-- The same, applied to the value of another transported chart. -/
lemma rb_outer_symm_coord' (A : Eucl 3 ≃L[ℝ] Eucl 3) (k l : Fin 3) (j : Fin 4) (v : Eucl 3)
    (t : EuclideanSpace ℝ (Fin 12)) :
    ((rbPsi A k t).symm (rbPsi A l t v)) j
      = (1 + classNormSq (blk k t))⁻¹ * rbNum (rbCoord A k j) k l (linBase A l v) t := by
  have h := rb_outer_symm_coord A k j l (linBase A l v) t
  simpa only [rbPsi, ContinuousLinearEquiv.trans_apply] using h

/-- **The transported normal functional at the value of another transported chart.** -/
lemma rb_linFun_rbPsi_apply (A : Eucl 3 ≃L[ℝ] Eucl 3) (k l : Fin 3) (v : Eucl 3)
    (t : EuclideanSpace ℝ (Fin 12)) :
    linFun (rbPsi A k t) (rbPsi A l t v) ≠ 0
      ↔ rbNum (rbFun A k) k l (linBase A l v) t ≠ 0 := by
  have h := linFun_rbPsi_ne_zero_iff A k l (linBase A l v) t
  simpa only [rbPsi, ContinuousLinearEquiv.trans_apply] using h

/-- At the diagonal parameter the numerator is the plain functional value. -/
lemma rbNum_zero (B : Eucl 3 →L[ℝ] ℝ) (k u : Fin 3) (v : Eucl 3) :
    rbNum B k u v 0 = B v := by
  simp [rbNum]

/-- The transported chart at the diagonal parameter is the linear chart. -/
lemma rbPsi_zero (A : Eucl 3 ≃L[ℝ] Eucl 3) (k : Fin 3) : rbPsi A k 0 = linBase A k := by
  have h0 : (blk k) (0 : EuclideanSpace ℝ (Fin 12)) = 0 := map_zero _
  have h : classEquiv (0 : Eucl 3) = 1 := by
    apply ContinuousLinearEquiv.ext
    funext v
    rw [classEquiv_zero]
    rfl
  rw [rbPsi, h0, h]
  apply ContinuousLinearEquiv.ext
  funext v
  simp only [ContinuousLinearEquiv.trans_apply]
  rfl

/-! ## 4. Analyticity of the numerators -/

lemma rb_contDiff_classGen_pair :
    ContDiff ℝ ω (fun p : Eucl 3 × Eucl 3 => classGen p.1 p.2) := by
  rw [show (fun p : Eucl 3 × Eucl 3 => classGen p.1 p.2)
      = fun p => p.1 1 • genI p.2 + p.1 2 • genJ p.2 + p.1 3 • genK p.2 from
    funext fun p => by simp [classGen]]
  fun_prop

lemma rb_contDiff_classGen_left (k : Fin 3) (v : Eucl 3) :
    ContDiff ℝ ω (fun t : EuclideanSpace ℝ (Fin 12) => classGen (blk k t) v) := by
  rw [show (fun t : EuclideanSpace ℝ (Fin 12) => classGen (blk k t) v)
      = fun t => (blk k t) 1 • genI v + (blk k t) 2 • genJ v + (blk k t) 3 • genK v from
    funext fun t => by simp [classGen]]
  fun_prop

lemma rb_contDiff_classEquiv_blk (u : Fin 3) (v : Eucl 3) :
    ContDiff ℝ ω (fun t : EuclideanSpace ℝ (Fin 12) => classEquiv (blk u t) v) := by
  rw [show (fun t : EuclideanSpace ℝ (Fin 12) => classEquiv (blk u t) v)
      = fun t => v + classGen (blk u t) v from funext fun t => classEquiv_apply _ _]
  exact contDiff_const.add (rb_contDiff_classGen_left u v)

lemma rb_contDiff_classGen_comp (k u : Fin 3) (v : Eucl 3) :
    ContDiff ℝ ω (fun t : EuclideanSpace ℝ (Fin 12) =>
      classGen (blk k t) (classEquiv (blk u t) v)) := by
  have hpair : ContDiff ℝ ω (fun t : EuclideanSpace ℝ (Fin 12) =>
      (blk k t, classEquiv (blk u t) v)) :=
    (blk k).contDiff.prodMk (rb_contDiff_classEquiv_blk u v)
  have hg : ContDiff ℝ ω (fun p : Eucl 3 × Eucl 3 => classGen p.1 p.2) :=
    rb_contDiff_classGen_pair
  have h := hg.comp hpair
  simpa only [Function.comp_def] using h

lemma rb_contDiff_rbNum (B : Eucl 3 →L[ℝ] ℝ) (k u : Fin 3) (v : Eucl 3) :
    ContDiff ℝ ω (fun t : EuclideanSpace ℝ (Fin 12) => rbNum B k u v t) :=
  B.contDiff.comp ((rb_contDiff_classEquiv_blk u v).sub (rb_contDiff_classGen_comp k u v))

lemma rb_analyticAt_rbNum (B : Eucl 3 →L[ℝ] ℝ) (k u : Fin 3) (v : Eucl 3)
    (t : EuclideanSpace ℝ (Fin 12)) :
    AnalyticAt ℝ (fun t : EuclideanSpace ℝ (Fin 12) => rbNum B k u v t) t :=
  (rb_contDiff_rbNum B k u v).contDiffAt.analyticAt

/-- Scaling four factors by the same nonzero scalar does not change the non-vanishing of the
`(2,2)`-determinant. -/
lemma rb_ne_zero_smul_sq {q a b c d : ℝ} (hq : q ≠ 0) :
    a * d - b * c ≠ 0 ↔ q * a * (q * d) - q * b * (q * c) ≠ 0 := by
  have hfac : q * a * (q * d) - q * b * (q * c) = (q * q) * (a * d - b * c) := by ring
  constructor
  · intro h h0
    rw [hfac] at h0
    exact h ((mul_eq_zero.mp h0).resolve_left (mul_ne_zero hq hq))
  · intro h h0
    exact h (by rw [hfac, h0, mul_zero])


/-! ## 5. The six cells -/

/-- Cell 1: the two boundary lines meet only in `0`. -/
def rbCell1 (A : Eucl 3 ≃L[ℝ] Eucl 3) : Set (EuclideanSpace ℝ (Fin 12)) :=
  {t | rbNum (rbCoord A 1 2) 1 0 (linBase A 0 linE0) t
        * rbNum (rbCoord A 1 3) 1 0 (linBase A 0 linE1) t
      - rbNum (rbCoord A 1 3) 1 0 (linBase A 0 linE0) t
        * rbNum (rbCoord A 1 2) 1 0 (linBase A 0 linE1) t ≠ 0}

/-- Cell 2: the first boundary line is not contained in the second plane. -/
def rbCell2 (A : Eucl 3 ≃L[ℝ] Eucl 3) : Set (EuclideanSpace ℝ (Fin 12)) :=
  {t | rbNum (rbFun A 1) 1 0 (linBase A 0 linE0) t ≠ 0
     ∨ rbNum (rbFun A 1) 1 0 (linBase A 0 linE1) t ≠ 0}

/-- Cell 3: the second boundary line is not contained in the first plane. -/
def rbCell3 (A : Eucl 3 ≃L[ℝ] Eucl 3) : Set (EuclideanSpace ℝ (Fin 12)) :=
  {t | rbNum (rbFun A 0) 0 1 (linBase A 1 linE0) t ≠ 0
     ∨ rbNum (rbFun A 0) 0 1 (linBase A 1 linE1) t ≠ 0}

/-- Cell 4: the two corner directions of the first chart avoid the second plane. -/
def rbCell4 (A : Eucl 3 ≃L[ℝ] Eucl 3) : Set (EuclideanSpace ℝ (Fin 12)) :=
  {t | rbNum (rbFun A 1) 1 0 (linBase A 0 (linE0 + (1 : ℝ) • linE1)) t ≠ 0
     ∧ rbNum (rbFun A 1) 1 0 (linBase A 0 (linE0 + (-1 : ℝ) • linE1)) t ≠ 0}

/-- Cell 5: the two corner directions of the second chart avoid the first plane. -/
def rbCell5 (A : Eucl 3 ≃L[ℝ] Eucl 3) : Set (EuclideanSpace ℝ (Fin 12)) :=
  {t | rbNum (rbFun A 0) 0 1 (linBase A 1 (linE0 + (1 : ℝ) • linE1)) t ≠ 0
     ∧ rbNum (rbFun A 0) 0 1 (linBase A 1 (linE0 + (-1 : ℝ) • linE1)) t ≠ 0}

/-- Cell 6: the two planes differ. -/
def rbCell6 (A : Eucl 3 ≃L[ℝ] Eucl 3) : Set (EuclideanSpace ℝ (Fin 12)) :=
  {t | (rbNum (rbFun A 1) 1 0 (linBase A 0 (linVecC 1)) t ≠ 0
      ∨ rbNum (rbFun A 1) 1 0 (linBase A 0 (linVecC Complex.I)) t ≠ 0
      ∨ rbNum (rbFun A 1) 1 0 (linBase A 0 (linVecC 0)) t ≠ 0)
     ∨ (rbNum (rbFun A 0) 0 1 (linBase A 1 (linVecC 1)) t ≠ 0
      ∨ rbNum (rbFun A 0) 0 1 (linBase A 1 (linVecC Complex.I)) t ≠ 0
      ∨ rbNum (rbFun A 0) 0 1 (linBase A 1 (linVecC 0)) t ≠ 0)}

/-! ### The cells mean the incidence conditions -/

lemma rbCell1_spec (A : Eucl 3 ≃L[ℝ] Eucl 3) (t : EuclideanSpace ℝ (Fin 12)) :
    t ∈ rbCell1 A ↔ linBdry (rbPsi A 0 t) ⊓ linBdry (rbPsi A 1 t) = ⊥ := by
  have hq : (0 : ℝ) < 1 + classNormSq (blk 1 t) := by
    linarith [classNormSq_nonneg (blk 1 t)]
  rw [rb_linBdry_inf_eq_bot_iff (rbPsi A 0 t) (rbPsi A 1 t)]
  rw [rb_outer_symm_coord' A 1 0 2 linE0 t, rb_outer_symm_coord' A 1 0 3 linE1 t,
    rb_outer_symm_coord' A 1 0 3 linE0 t, rb_outer_symm_coord' A 1 0 2 linE1 t]
  exact rb_ne_zero_smul_sq (q := (1 + classNormSq (blk 1 t))⁻¹) (inv_ne_zero (ne_of_gt hq))

lemma rbCell2_spec (A : Eucl 3 ≃L[ℝ] Eucl 3) (t : EuclideanSpace ℝ (Fin 12)) :
    t ∈ rbCell2 A ↔ ¬ linBdry (rbPsi A 0 t) ≤ linSub (rbPsi A 1 t) := by
  rw [rb_not_linBdry_le_linSub_iff (rbPsi A 0 t) (rbPsi A 1 t)]
  exact (or_congr (rb_linFun_rbPsi_apply A 1 0 linE0 t)
    (rb_linFun_rbPsi_apply A 1 0 linE1 t)).symm

lemma rbCell3_spec (A : Eucl 3 ≃L[ℝ] Eucl 3) (t : EuclideanSpace ℝ (Fin 12)) :
    t ∈ rbCell3 A ↔ ¬ linBdry (rbPsi A 1 t) ≤ linSub (rbPsi A 0 t) := by
  rw [rb_not_linBdry_le_linSub_iff (rbPsi A 1 t) (rbPsi A 0 t)]
  exact (or_congr (rb_linFun_rbPsi_apply A 0 1 linE0 t)
    (rb_linFun_rbPsi_apply A 0 1 linE1 t)).symm

lemma rbCell4_spec (A : Eucl 3 ≃L[ℝ] Eucl 3) (t : EuclideanSpace ℝ (Fin 12)) :
    t ∈ rbCell4 A ↔
      (rbPsi A 0 t (linE0 + (1 : ℝ) • linE1) ∉ linSub (rbPsi A 1 t)
        ∧ rbPsi A 0 t (linE0 + (-1 : ℝ) • linE1) ∉ linSub (rbPsi A 1 t)) := by
  have e1 : rbPsi A 0 t (linE0 + (1 : ℝ) • linE1) ∉ linSub (rbPsi A 1 t)
      ↔ rbNum (rbFun A 1) 1 0 (linBase A 0 (linE0 + (1 : ℝ) • linE1)) t ≠ 0 := by
    rw [rb_not_mem_linSub_iff]
    exact rb_linFun_rbPsi_apply A 1 0 (linE0 + (1 : ℝ) • linE1) t
  have e2 : rbPsi A 0 t (linE0 + (-1 : ℝ) • linE1) ∉ linSub (rbPsi A 1 t)
      ↔ rbNum (rbFun A 1) 1 0 (linBase A 0 (linE0 + (-1 : ℝ) • linE1)) t ≠ 0 := by
    rw [rb_not_mem_linSub_iff]
    exact rb_linFun_rbPsi_apply A 1 0 (linE0 + (-1 : ℝ) • linE1) t
  exact (and_congr e1 e2).symm

lemma rbCell5_spec (A : Eucl 3 ≃L[ℝ] Eucl 3) (t : EuclideanSpace ℝ (Fin 12)) :
    t ∈ rbCell5 A ↔
      (rbPsi A 1 t (linE0 + (1 : ℝ) • linE1) ∉ linSub (rbPsi A 0 t)
        ∧ rbPsi A 1 t (linE0 + (-1 : ℝ) • linE1) ∉ linSub (rbPsi A 0 t)) := by
  have e1 : rbPsi A 1 t (linE0 + (1 : ℝ) • linE1) ∉ linSub (rbPsi A 0 t)
      ↔ rbNum (rbFun A 0) 0 1 (linBase A 1 (linE0 + (1 : ℝ) • linE1)) t ≠ 0 := by
    rw [rb_not_mem_linSub_iff]
    exact rb_linFun_rbPsi_apply A 0 1 (linE0 + (1 : ℝ) • linE1) t
  have e2 : rbPsi A 1 t (linE0 + (-1 : ℝ) • linE1) ∉ linSub (rbPsi A 0 t)
      ↔ rbNum (rbFun A 0) 0 1 (linBase A 1 (linE0 + (-1 : ℝ) • linE1)) t ≠ 0 := by
    rw [rb_not_mem_linSub_iff]
    exact rb_linFun_rbPsi_apply A 0 1 (linE0 + (-1 : ℝ) • linE1) t
  exact (and_congr e1 e2).symm

lemma rbCell6_spec (A : Eucl 3 ≃L[ℝ] Eucl 3) (t : EuclideanSpace ℝ (Fin 12)) :
    t ∈ rbCell6 A ↔ linSub (rbPsi A 0 t) ≠ linSub (rbPsi A 1 t) := by
  rw [rb_linSub_ne_iff (rbPsi A 0 t) (rbPsi A 1 t)]
  refine (or_congr
    (or_congr (rb_linFun_rbPsi_apply A 1 0 (linVecC 1) t)
      (or_congr (rb_linFun_rbPsi_apply A 1 0 (linVecC Complex.I) t)
        (rb_linFun_rbPsi_apply A 1 0 (linVecC 0) t)))
    (or_congr (rb_linFun_rbPsi_apply A 0 1 (linVecC 1) t)
      (or_congr (rb_linFun_rbPsi_apply A 0 1 (linVecC Complex.I) t)
        (rb_linFun_rbPsi_apply A 0 1 (linVecC 0) t)))).symm

/-! ### The cells are open and dense at every point of the closed unit ball -/

lemma rbCell1_open_dense (A : Eucl 3 ≃L[ℝ] Eucl 3) :
    IsOpen (rbCell1 A) ∧ DenseAtBall (rbCell1 A) := by
  have hana : ∀ t : EuclideanSpace ℝ (Fin 12), AnalyticAt ℝ
      (fun t : EuclideanSpace ℝ (Fin 12) =>
        rbNum (rbCoord A 1 2) 1 0 (linBase A 0 linE0) t
          * rbNum (rbCoord A 1 3) 1 0 (linBase A 0 linE1) t
        - rbNum (rbCoord A 1 3) 1 0 (linBase A 0 linE0) t
          * rbNum (rbCoord A 1 2) 1 0 (linBase A 0 linE1) t) t := by
    intro t
    exact ((rb_analyticAt_rbNum (rbCoord A 1 2) 1 0 (linBase A 0 linE0) t).mul
      (rb_analyticAt_rbNum (rbCoord A 1 3) 1 0 (linBase A 0 linE1) t)).sub
      ((rb_analyticAt_rbNum (rbCoord A 1 3) 1 0 (linBase A 0 linE0) t).mul
      (rb_analyticAt_rbNum (rbCoord A 1 2) 1 0 (linBase A 0 linE1) t))
  have hwit : ∃ x, (fun t : EuclideanSpace ℝ (Fin 12) =>
        rbNum (rbCoord A 1 2) 1 0 (linBase A 0 linE0) t
          * rbNum (rbCoord A 1 3) 1 0 (linBase A 0 linE1) t
        - rbNum (rbCoord A 1 3) 1 0 (linBase A 0 linE0) t
          * rbNum (rbCoord A 1 2) 1 0 (linBase A 0 linE1) t) x ≠ 0 :=
    ⟨0, (rbCell1_spec A 0).mpr (by simpa [rbPsi_zero] using (linIncidence_linBase A).1)⟩
  have h := isOpen_denseAtBall_ne_zero hana hwit
  simpa only [rbCell1] using h

lemma rbCell2_open_dense (A : Eucl 3 ≃L[ℝ] Eucl 3) :
    IsOpen (rbCell2 A) ∧ DenseAtBall (rbCell2 A) := by
  have hf : ∀ x, AnalyticAt ℝ
      (fun t : EuclideanSpace ℝ (Fin 12) => rbNum (rbFun A 1) 1 0 (linBase A 0 linE0) t) x :=
    fun x => rb_analyticAt_rbNum (rbFun A 1) 1 0 (linBase A 0 linE0) x
  have hg : ∀ x, AnalyticAt ℝ
      (fun t : EuclideanSpace ℝ (Fin 12) => rbNum (rbFun A 1) 1 0 (linBase A 0 linE1) t) x :=
    fun x => rb_analyticAt_rbNum (rbFun A 1) 1 0 (linBase A 0 linE1) x
  have hopen : IsOpen (rbCell2 A) := by
    rw [show rbCell2 A
        = {x : EuclideanSpace ℝ (Fin 12) |
            (fun t : EuclideanSpace ℝ (Fin 12) =>
              rbNum (rbFun A 1) 1 0 (linBase A 0 linE0) t) x ≠ 0}
          ∪ {x : EuclideanSpace ℝ (Fin 12) |
            (fun t : EuclideanSpace ℝ (Fin 12) =>
              rbNum (rbFun A 1) 1 0 (linBase A 0 linE1) t) x ≠ 0} from by
      ext x; simp only [rbCell2, Set.mem_setOf_eq, Set.mem_union]]
    exact (isOpen_ne_fun (continuous_iff_continuousAt.mpr fun x => (hf x).continuousAt)
        continuous_const).union
      (isOpen_ne_fun (continuous_iff_continuousAt.mpr fun x => (hg x).continuousAt)
        continuous_const)
  have hw := (rbCell2_spec A 0).mpr (by simpa [rbPsi_zero] using (linIncidence_linBase A).2.1)
  have hd : DenseAtBall (rbCell2 A) := by
    rcases hw with hw | hw
    · refine rb_denseAtBall_mono (isOpen_denseAtBall_ne_zero hf ⟨0, hw⟩).2 ?_
      intro x hx
      simp only [rbCell2, Set.mem_setOf_eq] at hx ⊢
      tauto
    · refine rb_denseAtBall_mono (isOpen_denseAtBall_ne_zero hg ⟨0, hw⟩).2 ?_
      intro x hx
      simp only [rbCell2, Set.mem_setOf_eq] at hx ⊢
      tauto
  exact ⟨hopen, hd⟩

lemma rbCell3_open_dense (A : Eucl 3 ≃L[ℝ] Eucl 3) :
    IsOpen (rbCell3 A) ∧ DenseAtBall (rbCell3 A) := by
  have hf : ∀ x, AnalyticAt ℝ
      (fun t : EuclideanSpace ℝ (Fin 12) => rbNum (rbFun A 0) 0 1 (linBase A 1 linE0) t) x :=
    fun x => rb_analyticAt_rbNum (rbFun A 0) 0 1 (linBase A 1 linE0) x
  have hg : ∀ x, AnalyticAt ℝ
      (fun t : EuclideanSpace ℝ (Fin 12) => rbNum (rbFun A 0) 0 1 (linBase A 1 linE1) t) x :=
    fun x => rb_analyticAt_rbNum (rbFun A 0) 0 1 (linBase A 1 linE1) x
  have hopen : IsOpen (rbCell3 A) := by
    rw [show rbCell3 A
        = {x : EuclideanSpace ℝ (Fin 12) |
            (fun t : EuclideanSpace ℝ (Fin 12) =>
              rbNum (rbFun A 0) 0 1 (linBase A 1 linE0) t) x ≠ 0}
          ∪ {x : EuclideanSpace ℝ (Fin 12) |
            (fun t : EuclideanSpace ℝ (Fin 12) =>
              rbNum (rbFun A 0) 0 1 (linBase A 1 linE1) t) x ≠ 0} from by
      ext x; simp only [rbCell3, Set.mem_setOf_eq, Set.mem_union]]
    exact (isOpen_ne_fun (continuous_iff_continuousAt.mpr fun x => (hf x).continuousAt)
        continuous_const).union
      (isOpen_ne_fun (continuous_iff_continuousAt.mpr fun x => (hg x).continuousAt)
        continuous_const)
  have hw := (rbCell3_spec A 0).mpr (by simpa [rbPsi_zero] using (linIncidence_linBase A).2.2.1)
  have hd : DenseAtBall (rbCell3 A) := by
    rcases hw with hw | hw
    · refine rb_denseAtBall_mono (isOpen_denseAtBall_ne_zero hf ⟨0, hw⟩).2 ?_
      intro x hx
      simp only [rbCell3, Set.mem_setOf_eq] at hx ⊢
      tauto
    · refine rb_denseAtBall_mono (isOpen_denseAtBall_ne_zero hg ⟨0, hw⟩).2 ?_
      intro x hx
      simp only [rbCell3, Set.mem_setOf_eq] at hx ⊢
      tauto
  exact ⟨hopen, hd⟩

lemma rbCell4_open_dense (A : Eucl 3 ≃L[ℝ] Eucl 3) :
    IsOpen (rbCell4 A) ∧ DenseAtBall (rbCell4 A) := by
  have hf : ∀ x, AnalyticAt ℝ
      (fun t : EuclideanSpace ℝ (Fin 12) =>
        rbNum (rbFun A 1) 1 0 (linBase A 0 (linE0 + (1 : ℝ) • linE1)) t) x :=
    fun x => rb_analyticAt_rbNum (rbFun A 1) 1 0 (linBase A 0 (linE0 + (1 : ℝ) • linE1)) x
  have hg : ∀ x, AnalyticAt ℝ
      (fun t : EuclideanSpace ℝ (Fin 12) =>
        rbNum (rbFun A 1) 1 0 (linBase A 0 (linE0 + (-1 : ℝ) • linE1)) t) x :=
    fun x => rb_analyticAt_rbNum (rbFun A 1) 1 0 (linBase A 0 (linE0 + (-1 : ℝ) • linE1)) x
  have hw : (fun t : EuclideanSpace ℝ (Fin 12) =>
        rbNum (rbFun A 1) 1 0 (linBase A 0 (linE0 + (1 : ℝ) • linE1)) t) 0 ≠ 0
      ∧ (fun t : EuclideanSpace ℝ (Fin 12) =>
        rbNum (rbFun A 1) 1 0 (linBase A 0 (linE0 + (-1 : ℝ) • linE1)) t) 0 ≠ 0 :=
    (rbCell4_spec A 0).mpr (by
      constructor
      · simpa [rbPsi_zero] using (linIncidence_linBase A).2.2.2.1 1 (Or.inl rfl)
      · simpa [rbPsi_zero] using (linIncidence_linBase A).2.2.2.1 (-1) (Or.inr rfl))
  have hopen : IsOpen (rbCell4 A) := by
    rw [show rbCell4 A
        = {x : EuclideanSpace ℝ (Fin 12) |
            (fun t : EuclideanSpace ℝ (Fin 12) =>
              rbNum (rbFun A 1) 1 0 (linBase A 0 (linE0 + (1 : ℝ) • linE1)) t) x ≠ 0}
          ∩ {x : EuclideanSpace ℝ (Fin 12) |
            (fun t : EuclideanSpace ℝ (Fin 12) =>
              rbNum (rbFun A 1) 1 0 (linBase A 0 (linE0 + (-1 : ℝ) • linE1)) t) x ≠ 0} from by
      ext x; simp only [rbCell4, Set.mem_setOf_eq, Set.mem_inter_iff]]
    exact (isOpen_ne_fun (continuous_iff_continuousAt.mpr fun x => (hf x).continuousAt)
        continuous_const).inter
      (isOpen_ne_fun (continuous_iff_continuousAt.mpr fun x => (hg x).continuousAt)
        continuous_const)
  have hd : DenseAtBall (rbCell4 A) := by
    have h1 := (isOpen_denseAtBall_ne_zero hf ⟨0, hw.1⟩).2
    have h2 := (isOpen_denseAtBall_ne_zero hg ⟨0, hw.2⟩).2
    refine rb_denseAtBall_mono (rb_denseAtBall_inter
      (isOpen_ne_fun (continuous_iff_continuousAt.mpr fun x => (hf x).continuousAt)
        continuous_const)
      (isOpen_ne_fun (continuous_iff_continuousAt.mpr fun x => (hg x).continuousAt)
        continuous_const) h1 h2) ?_
    intro x hx
    simp only [rbCell4, Set.mem_setOf_eq, Set.mem_inter_iff] at hx ⊢
    exact hx
  exact ⟨hopen, hd⟩

lemma rbCell5_open_dense (A : Eucl 3 ≃L[ℝ] Eucl 3) :
    IsOpen (rbCell5 A) ∧ DenseAtBall (rbCell5 A) := by
  have hf : ∀ x, AnalyticAt ℝ
      (fun t : EuclideanSpace ℝ (Fin 12) =>
        rbNum (rbFun A 0) 0 1 (linBase A 1 (linE0 + (1 : ℝ) • linE1)) t) x :=
    fun x => rb_analyticAt_rbNum (rbFun A 0) 0 1 (linBase A 1 (linE0 + (1 : ℝ) • linE1)) x
  have hg : ∀ x, AnalyticAt ℝ
      (fun t : EuclideanSpace ℝ (Fin 12) =>
        rbNum (rbFun A 0) 0 1 (linBase A 1 (linE0 + (-1 : ℝ) • linE1)) t) x :=
    fun x => rb_analyticAt_rbNum (rbFun A 0) 0 1 (linBase A 1 (linE0 + (-1 : ℝ) • linE1)) x
  have hw : (fun t : EuclideanSpace ℝ (Fin 12) =>
        rbNum (rbFun A 0) 0 1 (linBase A 1 (linE0 + (1 : ℝ) • linE1)) t) 0 ≠ 0
      ∧ (fun t : EuclideanSpace ℝ (Fin 12) =>
        rbNum (rbFun A 0) 0 1 (linBase A 1 (linE0 + (-1 : ℝ) • linE1)) t) 0 ≠ 0 :=
    (rbCell5_spec A 0).mpr (by
      constructor
      · simpa [rbPsi_zero] using (linIncidence_linBase A).2.2.2.2.1 1 (Or.inl rfl)
      · simpa [rbPsi_zero] using (linIncidence_linBase A).2.2.2.2.1 (-1) (Or.inr rfl))
  have hopen : IsOpen (rbCell5 A) := by
    rw [show rbCell5 A
        = {x : EuclideanSpace ℝ (Fin 12) |
            (fun t : EuclideanSpace ℝ (Fin 12) =>
              rbNum (rbFun A 0) 0 1 (linBase A 1 (linE0 + (1 : ℝ) • linE1)) t) x ≠ 0}
          ∩ {x : EuclideanSpace ℝ (Fin 12) |
            (fun t : EuclideanSpace ℝ (Fin 12) =>
              rbNum (rbFun A 0) 0 1 (linBase A 1 (linE0 + (-1 : ℝ) • linE1)) t) x ≠ 0} from by
      ext x; simp only [rbCell5, Set.mem_setOf_eq, Set.mem_inter_iff]]
    exact (isOpen_ne_fun (continuous_iff_continuousAt.mpr fun x => (hf x).continuousAt)
        continuous_const).inter
      (isOpen_ne_fun (continuous_iff_continuousAt.mpr fun x => (hg x).continuousAt)
        continuous_const)
  have hd : DenseAtBall (rbCell5 A) := by
    have h1 := (isOpen_denseAtBall_ne_zero hf ⟨0, hw.1⟩).2
    have h2 := (isOpen_denseAtBall_ne_zero hg ⟨0, hw.2⟩).2
    refine rb_denseAtBall_mono (rb_denseAtBall_inter
      (isOpen_ne_fun (continuous_iff_continuousAt.mpr fun x => (hf x).continuousAt)
        continuous_const)
      (isOpen_ne_fun (continuous_iff_continuousAt.mpr fun x => (hg x).continuousAt)
        continuous_const) h1 h2) ?_
    intro x hx
    simp only [rbCell5, Set.mem_setOf_eq, Set.mem_inter_iff] at hx ⊢
    exact hx
  exact ⟨hopen, hd⟩

lemma rbCell6_open_dense (A : Eucl 3 ≃L[ℝ] Eucl 3) :
    IsOpen (rbCell6 A) ∧ DenseAtBall (rbCell6 A) := by
  have h1 : ∀ x, AnalyticAt ℝ
      (fun t : EuclideanSpace ℝ (Fin 12) => rbNum (rbFun A 1) 1 0 (linBase A 0 (linVecC 1)) t) x :=
    fun x => rb_analyticAt_rbNum (rbFun A 1) 1 0 (linBase A 0 (linVecC 1)) x
  have h2 : ∀ x, AnalyticAt ℝ
      (fun t : EuclideanSpace ℝ (Fin 12) =>
        rbNum (rbFun A 1) 1 0 (linBase A 0 (linVecC Complex.I)) t) x :=
    fun x => rb_analyticAt_rbNum (rbFun A 1) 1 0 (linBase A 0 (linVecC Complex.I)) x
  have h3 : ∀ x, AnalyticAt ℝ
      (fun t : EuclideanSpace ℝ (Fin 12) => rbNum (rbFun A 1) 1 0 (linBase A 0 (linVecC 0)) t) x :=
    fun x => rb_analyticAt_rbNum (rbFun A 1) 1 0 (linBase A 0 (linVecC 0)) x
  have h4 : ∀ x, AnalyticAt ℝ
      (fun t : EuclideanSpace ℝ (Fin 12) => rbNum (rbFun A 0) 0 1 (linBase A 1 (linVecC 1)) t) x :=
    fun x => rb_analyticAt_rbNum (rbFun A 0) 0 1 (linBase A 1 (linVecC 1)) x
  have h5 : ∀ x, AnalyticAt ℝ
      (fun t : EuclideanSpace ℝ (Fin 12) =>
        rbNum (rbFun A 0) 0 1 (linBase A 1 (linVecC Complex.I)) t) x :=
    fun x => rb_analyticAt_rbNum (rbFun A 0) 0 1 (linBase A 1 (linVecC Complex.I)) x
  have h6 : ∀ x, AnalyticAt ℝ
      (fun t : EuclideanSpace ℝ (Fin 12) => rbNum (rbFun A 0) 0 1 (linBase A 1 (linVecC 0)) t) x :=
    fun x => rb_analyticAt_rbNum (rbFun A 0) 0 1 (linBase A 1 (linVecC 0)) x
  have hopen : IsOpen (rbCell6 A) := by
    rw [show rbCell6 A
        = ({x : EuclideanSpace ℝ (Fin 12) |
              (fun t : EuclideanSpace ℝ (Fin 12) =>
                rbNum (rbFun A 1) 1 0 (linBase A 0 (linVecC 1)) t) x ≠ 0}
            ∪ {x : EuclideanSpace ℝ (Fin 12) |
              (fun t : EuclideanSpace ℝ (Fin 12) =>
                rbNum (rbFun A 1) 1 0 (linBase A 0 (linVecC Complex.I)) t) x ≠ 0}
            ∪ {x : EuclideanSpace ℝ (Fin 12) |
              (fun t : EuclideanSpace ℝ (Fin 12) =>
                rbNum (rbFun A 1) 1 0 (linBase A 0 (linVecC 0)) t) x ≠ 0})
          ∪ ({x : EuclideanSpace ℝ (Fin 12) |
              (fun t : EuclideanSpace ℝ (Fin 12) =>
                rbNum (rbFun A 0) 0 1 (linBase A 1 (linVecC 1)) t) x ≠ 0}
            ∪ {x : EuclideanSpace ℝ (Fin 12) |
              (fun t : EuclideanSpace ℝ (Fin 12) =>
                rbNum (rbFun A 0) 0 1 (linBase A 1 (linVecC Complex.I)) t) x ≠ 0}
            ∪ {x : EuclideanSpace ℝ (Fin 12) |
              (fun t : EuclideanSpace ℝ (Fin 12) =>
                rbNum (rbFun A 0) 0 1 (linBase A 1 (linVecC 0)) t) x ≠ 0}) from by
      ext x; simp only [rbCell6, Set.mem_setOf_eq, Set.mem_union]; tauto]
    have o1 : IsOpen {x : EuclideanSpace ℝ (Fin 12) |
        (fun t : EuclideanSpace ℝ (Fin 12) =>
          rbNum (rbFun A 1) 1 0 (linBase A 0 (linVecC 1)) t) x ≠ 0} :=
      isOpen_ne_fun (continuous_iff_continuousAt.mpr fun x => (h1 x).continuousAt) continuous_const
    have o2 : IsOpen {x : EuclideanSpace ℝ (Fin 12) |
        (fun t : EuclideanSpace ℝ (Fin 12) =>
          rbNum (rbFun A 1) 1 0 (linBase A 0 (linVecC Complex.I)) t) x ≠ 0} :=
      isOpen_ne_fun (continuous_iff_continuousAt.mpr fun x => (h2 x).continuousAt) continuous_const
    have o3 : IsOpen {x : EuclideanSpace ℝ (Fin 12) |
        (fun t : EuclideanSpace ℝ (Fin 12) =>
          rbNum (rbFun A 1) 1 0 (linBase A 0 (linVecC 0)) t) x ≠ 0} :=
      isOpen_ne_fun (continuous_iff_continuousAt.mpr fun x => (h3 x).continuousAt) continuous_const
    have o4 : IsOpen {x : EuclideanSpace ℝ (Fin 12) |
        (fun t : EuclideanSpace ℝ (Fin 12) =>
          rbNum (rbFun A 0) 0 1 (linBase A 1 (linVecC 1)) t) x ≠ 0} :=
      isOpen_ne_fun (continuous_iff_continuousAt.mpr fun x => (h4 x).continuousAt) continuous_const
    have o5 : IsOpen {x : EuclideanSpace ℝ (Fin 12) |
        (fun t : EuclideanSpace ℝ (Fin 12) =>
          rbNum (rbFun A 0) 0 1 (linBase A 1 (linVecC Complex.I)) t) x ≠ 0} :=
      isOpen_ne_fun (continuous_iff_continuousAt.mpr fun x => (h5 x).continuousAt) continuous_const
    have o6 : IsOpen {x : EuclideanSpace ℝ (Fin 12) |
        (fun t : EuclideanSpace ℝ (Fin 12) =>
          rbNum (rbFun A 0) 0 1 (linBase A 1 (linVecC 0)) t) x ≠ 0} :=
      isOpen_ne_fun (continuous_iff_continuousAt.mpr fun x => (h6 x).continuousAt) continuous_const
    exact ((o1.union o2).union o3).union ((o4.union o5).union o6)
  have hw := (rbCell6_spec A 0).mpr (by simpa [rbPsi_zero] using (linIncidence_linBase A).2.2.2.2.2)
  have hd : DenseAtBall (rbCell6 A) := by
    rcases hw with (h | h | h) | (h | h | h)
    · refine rb_denseAtBall_mono (isOpen_denseAtBall_ne_zero h1 ⟨0, h⟩).2 ?_
      intro x hx; simp only [rbCell6, Set.mem_setOf_eq] at hx ⊢; tauto
    · refine rb_denseAtBall_mono (isOpen_denseAtBall_ne_zero h2 ⟨0, h⟩).2 ?_
      intro x hx; simp only [rbCell6, Set.mem_setOf_eq] at hx ⊢; tauto
    · refine rb_denseAtBall_mono (isOpen_denseAtBall_ne_zero h3 ⟨0, h⟩).2 ?_
      intro x hx; simp only [rbCell6, Set.mem_setOf_eq] at hx ⊢; tauto
    · refine rb_denseAtBall_mono (isOpen_denseAtBall_ne_zero h4 ⟨0, h⟩).2 ?_
      intro x hx; simp only [rbCell6, Set.mem_setOf_eq] at hx ⊢; tauto
    · refine rb_denseAtBall_mono (isOpen_denseAtBall_ne_zero h5 ⟨0, h⟩).2 ?_
      intro x hx; simp only [rbCell6, Set.mem_setOf_eq] at hx ⊢; tauto
    · refine rb_denseAtBall_mono (isOpen_denseAtBall_ne_zero h6 ⟨0, h⟩).2 ?_
      intro x hx; simp only [rbCell6, Set.mem_setOf_eq] at hx ⊢; tauto
  exact ⟨hopen, hd⟩

/-! ## 6. The target theorem -/

/-- The transported linear class is the class map of the transported linear chart. -/
lemma rb_linTransClass_eq (A : Eucl 3 ≃L[ℝ] Eucl 3) (k : Fin 3) (cl : ℝ) (hcl : 0 < cl)
    (t : EuclideanSpace ℝ (Fin 12)) :
    linTransClass (linBase A k) (blk k t) cl hcl
      = planeClassMap (diskPlane (linPlaneChart (rbPsi A k t) cl hcl)) := rfl

/-- **Row B of `Work.Drive.classRowsLin_openDense`**: the pair row `PairReg lin₀ lin₁` of the two
*transported* linear models, on an open set of design parameters dense at every point of the closed
unit ball. -/
theorem rowB_linTrans_pairReg_openDense (A : Work.Drive.Eucl 3 ≃L[ℝ] Work.Drive.Eucl 3) (cl : ℝ)
    (hcl : 0 < cl) :
    ∃ R : Set (EuclideanSpace ℝ (Fin 12)), IsOpen R ∧ Work.Drive.DenseAtBall R ∧
      ∀ t ∈ R, Work.Drive.PairReg
        (Work.Drive.linTransClass (Work.Drive.linBase A 0) ((Work.Drive.blk 0) t) cl hcl)
        (Work.Drive.linTransClass (Work.Drive.linBase A 1) ((Work.Drive.blk 1) t) cl hcl) := by
  refine ⟨⋂ i : Fin 6,
    ![rbCell1 A, rbCell2 A, rbCell3 A, rbCell4 A, rbCell5 A, rbCell6 A] i, ?_, ?_, ?_⟩
  · refine isOpen_iInter_of_finite fun i => ?_
    fin_cases i
    · exact (rbCell1_open_dense A).1
    · exact (rbCell2_open_dense A).1
    · exact (rbCell3_open_dense A).1
    · exact (rbCell4_open_dense A).1
    · exact (rbCell5_open_dense A).1
    · exact (rbCell6_open_dense A).1
  · refine rb_denseAtBall_iInter (fun i => ?_) (fun i => ?_)
    · fin_cases i
      · exact (rbCell1_open_dense A).1
      · exact (rbCell2_open_dense A).1
      · exact (rbCell3_open_dense A).1
      · exact (rbCell4_open_dense A).1
      · exact (rbCell5_open_dense A).1
      · exact (rbCell6_open_dense A).1
    · fin_cases i
      · exact (rbCell1_open_dense A).2
      · exact (rbCell2_open_dense A).2
      · exact (rbCell3_open_dense A).2
      · exact (rbCell4_open_dense A).2
      · exact (rbCell5_open_dense A).2
      · exact (rbCell6_open_dense A).2
  · intro t ht
    have hmem : ∀ i : Fin 6,
        t ∈ ![rbCell1 A, rbCell2 A, rbCell3 A, rbCell4 A, rbCell5 A, rbCell6 A] i :=
      fun i => Set.mem_iInter.mp ht i
    have h1 : linBdry (rbPsi A 0 t) ⊓ linBdry (rbPsi A 1 t) = ⊥ :=
      (rbCell1_spec A t).mp (by simpa using hmem 0)
    have h2 : ¬ linBdry (rbPsi A 0 t) ≤ linSub (rbPsi A 1 t) :=
      (rbCell2_spec A t).mp (by simpa using hmem 1)
    have h3 : ¬ linBdry (rbPsi A 1 t) ≤ linSub (rbPsi A 0 t) :=
      (rbCell3_spec A t).mp (by simpa using hmem 2)
    have h4 : ∀ s : ℝ, (s = 1 ∨ s = -1) →
        rbPsi A 0 t (linE0 + s • linE1) ∉ linSub (rbPsi A 1 t) := by
      intro s hs
      have h := (rbCell4_spec A t).mp (by simpa using hmem 3)
      rcases hs with rfl | rfl
      · exact h.1
      · exact h.2
    have h5 : ∀ s : ℝ, (s = 1 ∨ s = -1) →
        rbPsi A 1 t (linE0 + s • linE1) ∉ linSub (rbPsi A 0 t) := by
      intro s hs
      have h := (rbCell5_spec A t).mp (by simpa using hmem 4)
      rcases hs with rfl | rfl
      · exact h.1
      · exact h.2
    have h6 : linSub (rbPsi A 0 t) ≠ linSub (rbPsi A 1 t) :=
      (rbCell6_spec A t).mp (by simpa using hmem 5)
    rw [rb_linTransClass_eq, rb_linTransClass_eq]
    exact pairReg_linPlaneCharts_of_incidence (rbPsi A 0 t) (rbPsi A 1 t) cl hcl h1 h2 h3 h4 h5 h6

end

end Work.Drive
