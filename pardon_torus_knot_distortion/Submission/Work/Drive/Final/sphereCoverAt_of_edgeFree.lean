import Mathlib
import Submission.Work.Drive.Final.AnyEventDefs
import Submission.Work.Drive.Mono.JunctionGenC
import Submission.Work.Drive.Mono.levelSphereDecomposition_of_data
import Submission.Work.Drive.Final.anyDentData_exists
import Submission.Work.Drive.Final.tls_window_dichotomy

namespace Work.Drive.Final

set_option maxHeartbeats 4000000
set_option maxRecDepth 8000

open LeanEval.KnotTheory.PardonDistortion Set

noncomputable section

variable {ψ : Submission.Diffeo} {s u h lam : ℝ} {c v : R3} {σ : Equiv.Perm (Fin 3)}
  {ℓ : R3 →L[ℝ] ℝ}

/-! ## Two directions increasing both `⟪v,·⟫` and `ℓ` -/

/-- A direction on which both `⟪v,·⟫` and `ℓ` increase. -/
theorem exists_dir_inner_pos_and_lpos {v : R3} {ℓ : R3 →L[ℝ] ℝ} (hv : v ≠ 0) (hℓv : ℓ v = 0)
    (hℓne : ℓ ≠ 0) : ∃ w : R3, 0 < inner ℝ v w ∧ 0 < ℓ w := by
  obtain ⟨w₀, hw₀, hvw₀⟩ := exists_dir_perp_pos hv hℓne hℓv
  refine ⟨w₀ + (1 / ‖v‖ ^ 2) • v, ?_, ?_⟩
  · rw [inner_add_right, inner_smul_right, hvw₀, zero_add, real_inner_self_eq_norm_sq]
    have hpos : (0 : ℝ) < ‖v‖ ^ 2 := by positivity
    have hc : (1 / ‖v‖ ^ 2) * ‖v‖ ^ 2 = 1 := by
      rw [one_div, inv_mul_cancel₀ (ne_of_gt hpos)]
    linarith
  · rw [map_add, map_smul, hℓv, smul_zero, add_zero]; exact hw₀

/-- A direction on which `⟪v,·⟫` decreases and `ℓ` increases. -/
theorem exists_dir_inner_neg_and_lpos {v : R3} {ℓ : R3 →L[ℝ] ℝ} (hv : v ≠ 0) (hℓv : ℓ v = 0)
    (hℓne : ℓ ≠ 0) : ∃ w : R3, inner ℝ v w < 0 ∧ 0 < ℓ w := by
  obtain ⟨w₀, hw₀, hvw₀⟩ := exists_dir_perp_pos hv hℓne hℓv
  refine ⟨w₀ - (1 / ‖v‖ ^ 2) • v, ?_, ?_⟩
  · rw [inner_sub_right, inner_smul_right, hvw₀, zero_sub, real_inner_self_eq_norm_sq]
    have hpos : (0 : ℝ) < ‖v‖ ^ 2 := by positivity
    have hc : (1 / ‖v‖ ^ 2) * ‖v‖ ^ 2 = 1 := by
      rw [one_div, inv_mul_cancel₀ (ne_of_gt hpos)]
    linarith
  · rw [map_sub, map_smul, hℓv, smul_zero, sub_zero]; exact hw₀

/-! ## The box: norm, closure, faces -/

/-- A point whose coordinates satisfy the closed box bounds lies in the closed box. -/
theorem boxNorm_le_of_abs_coord_le {z : R3}
    (hz : ∀ i : Fin 3, |z (σ i) - c (σ i)| ≤ Submission.boxSide i * s) :
    Submission.boxNorm c σ z ≤ s := by
  rw [Submission.boxNorm, max_le_iff, max_le_iff]
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · rw [div_le_iff₀ (Submission.boxSide_pos 0)]; simpa [mul_comm] using hz 0
  · rw [div_le_iff₀ (Submission.boxSide_pos 1)]; simpa [mul_comm] using hz 1
  · rw [div_le_iff₀ (Submission.boxSide_pos 2)]; simpa [mul_comm] using hz 2

/-- A point of the closed box satisfies the closed box bounds. -/
theorem abs_coord_le_of_mem_tlsBoxCl {z : R3} (hz : z ∈ tlsBoxCl s c σ) (i : Fin 3) :
    |z (σ i) - c (σ i)| ≤ Submission.boxSide i * s := by
  have hsub : Submission.PBox s c σ ⊆
      {y : R3 | ∀ i : Fin 3, |y (σ i) - c (σ i)| ≤ Submission.boxSide i * s} :=
    fun y hy i => le_of_lt (hy i)
  have hcl : IsClosed {y : R3 | ∀ i : Fin 3,
      |y (σ i) - c (σ i)| ≤ Submission.boxSide i * s} := by
    have hset : {y : R3 | ∀ i : Fin 3, |y (σ i) - c (σ i)| ≤ Submission.boxSide i * s} =
        ⋂ i, {y : R3 | |y (σ i) - c (σ i)| ≤ Submission.boxSide i * s} := by
      ext y; simp
    rw [hset]
    exact isClosed_iInter fun i => isClosed_le (continuous_abs.comp (by fun_prop)) continuous_const
  exact closure_minimal hsub hcl hz i

/-- The closed box is the sublevel set of the box norm. -/
theorem mem_tlsBoxCl_iff {z : R3} (hs : 0 < s) :
    z ∈ tlsBoxCl s c σ ↔ Submission.boxNorm c σ z ≤ s := by
  constructor
  · intro hz
    exact boxNorm_le_of_abs_coord_le (abs_coord_le_of_mem_tlsBoxCl hz)
  · intro hz
    exact Work.Drive.Mono.mem_closure_PBox_of_boxNorm_le hs c σ hz

/-- A point of the box sphere is extremal in some coordinate. -/
theorem exists_extremal_of_boxNorm_eq {z : R3} (hs : 0 < s)
    (hz : Submission.boxNorm c σ z = s) :
    ∃ i : Fin 3, |z (σ i) - c (σ i)| = Submission.boxSide i * s := by
  by_contra hcon
  push Not at hcon
  have hle : ∀ i : Fin 3, |z (σ i) - c (σ i)| ≤ Submission.boxSide i * s := by
    intro i
    have h1 : |z (σ i) - c (σ i)| / Submission.boxSide i ≤ Submission.boxNorm c σ z := by
      rw [Submission.boxNorm]
      fin_cases i <;> simp [le_max_left, le_max_right]
    rw [hz, div_le_iff₀ (Submission.boxSide_pos i)] at h1
    simpa [mul_comm] using h1
  have h2 : Submission.boxNorm c σ z < s := by
    rw [Submission.boxNorm, max_lt_iff, max_lt_iff]
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · rw [div_lt_iff₀ (Submission.boxSide_pos 0)]
      simpa [mul_comm] using (lt_of_le_of_ne (hle 0) (hcon 0) :
        |z (σ 0) - c (σ 0)| < Submission.boxSide 0 * s)
    · rw [div_lt_iff₀ (Submission.boxSide_pos 1)]
      simpa [mul_comm] using (lt_of_le_of_ne (hle 1) (hcon 1) :
        |z (σ 1) - c (σ 1)| < Submission.boxSide 1 * s)
    · rw [div_lt_iff₀ (Submission.boxSide_pos 2)]
      simpa [mul_comm] using (lt_of_le_of_ne (hle 2) (hcon 2) :
        |z (σ 2) - c (σ 2)| < Submission.boxSide 2 * s)
  rw [hz] at h2
  exact lt_irrefl s h2

/-! ## Moving a box point of the wall into a cap above the wall -/

/-- A point of the open box on or above the upper slab face, at the wall, can be moved into
`tlsUpCap ∩ tlsWallOpen`. -/
theorem exists_mem_upCap_inter_wallOpen {p : R3} (hv : v ≠ 0) (hℓv : ℓ v = 0) (hℓne : ℓ ≠ 0)
    (hpP : p ∈ Submission.PBox s c σ) (hf : inner ℝ v c + u + h ≤ inner ℝ v p)
    (hℓp : ℓ p = lam) :
    (tlsUpCap s c σ u h v ∩ tlsWallOpen s c σ ℓ lam).Nonempty := by
  obtain ⟨w, hvw, hℓw⟩ := exists_dir_inner_pos_and_lpos hv hℓv hℓne
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.mp
    ((Work.Topology.SphereSlicing.isOpen_PBox s c σ).mem_nhds hpP)
  set t : ℝ := min (δ / (2 * (‖w‖ + 1))) 1 with ht
  have htpos : 0 < t := lt_min (by positivity) one_pos
  have htw : t * ‖w‖ < δ := by
    have h1 : t ≤ δ / (2 * (‖w‖ + 1)) := le_of_eq_of_le ht (min_le_left _ _)
    have h2 : δ / (2 * (‖w‖ + 1)) * ‖w‖ < δ := by
      rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity : (0 : ℝ) < 2 * (‖w‖ + 1))]
      nlinarith [norm_nonneg w, hδ]
    nlinarith [mul_le_mul_of_nonneg_right h1 (norm_nonneg w)]
  have hmemP : p + t • w ∈ Submission.PBox s c σ := by
    refine hball ?_
    rw [Metric.mem_ball, dist_eq_norm]
    have hsub : p + t • w - p = t • w := by abel
    rw [hsub, norm_smul, Real.norm_eq_abs, abs_of_pos htpos]
    exact htw
  have hf' : inner ℝ v c + u + h < inner ℝ v (p + t • w) := by
    rw [inner_add_right, inner_smul_right]
    have := mul_pos htpos hvw
    linarith
  have hℓ' : lam < ℓ (p + t • w) := by
    rw [map_add, map_smul, smul_eq_mul, hℓp]
    have := mul_pos htpos hℓw
    linarith
  exact ⟨p + t • w, ⟨⟨hmemP, hf'⟩, ⟨hmemP, hℓ'⟩⟩⟩

/-- A point of the open box on or below the lower slab face, at the wall, can be moved into
`tlsDnCap ∩ tlsWallOpen`. -/
theorem exists_mem_dnCap_inter_wallOpen {p : R3} (hv : v ≠ 0) (hℓv : ℓ v = 0) (hℓne : ℓ ≠ 0)
    (hpP : p ∈ Submission.PBox s c σ) (hf : inner ℝ v p ≤ inner ℝ v c + u - h)
    (hℓp : ℓ p = lam) :
    (tlsDnCap s c σ u h v ∩ tlsWallOpen s c σ ℓ lam).Nonempty := by
  obtain ⟨w, hvw, hℓw⟩ := exists_dir_inner_neg_and_lpos hv hℓv hℓne
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.mp
    ((Work.Topology.SphereSlicing.isOpen_PBox s c σ).mem_nhds hpP)
  set t : ℝ := min (δ / (2 * (‖w‖ + 1))) 1 with ht
  have htpos : 0 < t := lt_min (by positivity) one_pos
  have htw : t * ‖w‖ < δ := by
    have h1 : t ≤ δ / (2 * (‖w‖ + 1)) := le_of_eq_of_le ht (min_le_left _ _)
    have h2 : δ / (2 * (‖w‖ + 1)) * ‖w‖ < δ := by
      rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity : (0 : ℝ) < 2 * (‖w‖ + 1))]
      nlinarith [norm_nonneg w, hδ]
    nlinarith [mul_le_mul_of_nonneg_right h1 (norm_nonneg w)]
  have hmemP : p + t • w ∈ Submission.PBox s c σ := by
    refine hball ?_
    rw [Metric.mem_ball, dist_eq_norm]
    have hsub : p + t • w - p = t • w := by abel
    rw [hsub, norm_smul, Real.norm_eq_abs, abs_of_pos htpos]
    exact htw
  have hf' : inner ℝ v (p + t • w) < inner ℝ v c + u - h := by
    rw [inner_add_right, inner_smul_right]
    have := mul_neg_of_pos_of_neg htpos hvw
    linarith
  have hℓ' : lam < ℓ (p + t • w) := by
    rw [map_add, map_smul, smul_eq_mul, hℓp]
    have := mul_pos htpos hℓw
    linarith
  exact ⟨p + t • w, ⟨⟨hmemP, hf'⟩, ⟨hmemP, hℓ'⟩⟩⟩

/-! ## The level functional is bounded by `lam` above the upper slab face -/

/-- **The maximiser argument for the upper cap.**  If the box contains no point above the wall
beyond the upper slab face, then `ℓ ≤ lam` on the whole upper part of the closed box. -/
theorem le_lam_of_mem_tlsBoxCl_ge_face (hs : 0 < s) (hh : 0 < h) (hv : v ≠ 0) (hℓv : ℓ v = 0)
    (hℓne : ℓ ≠ 0)
    (hXne : (tlsUpCap s c σ u h v).Nonempty)
    (hno : ¬ (tlsUpCap s c σ u h v ∩ tlsWallOpen s c σ ℓ lam).Nonempty) :
    ∀ z ∈ tlsBoxCl s c σ, inner ℝ v c + u + h ≤ inner ℝ v z → ℓ z ≤ lam := by
  intro z hz hzf
  set D : Set R3 := tlsBoxCl s c σ ∩ {y : R3 | inner ℝ v c + u + h ≤ inner ℝ v y} with hD
  have hDc : IsCompact D := by
    rw [hD]
    exact (tlsBoxCl_isCompact hs).inter_right
      (isClosed_le continuous_const (continuous_inner_fst v))
  have hDne : D.Nonempty := by
    obtain ⟨y, hy⟩ := hXne
    refine ⟨y, subset_closure hy.1, ?_⟩
    have hy2 : inner ℝ v c + u + h < inner ℝ v y := hy.2
    exact le_of_lt hy2
  obtain ⟨ŷ, hŷD, hŷmax⟩ := hDc.exists_isMaxOn hDne ℓ.continuous.continuousOn
  have hgoal : ℓ ŷ ≤ lam := by
    by_contra hcon
    have hlt : lam < ℓ ŷ := lt_of_not_ge hcon
    refine hno ?_
    have hŷf : inner ℝ v c + u + h ≤ inner ℝ v ŷ := hŷD.2
    rcases lt_or_eq_of_le hŷf with hfgt | hfeq
    · by_cases hŷP : ŷ ∈ Submission.PBox s c σ
      · exact ⟨ŷ, ⟨⟨hŷP, hfgt⟩, ⟨hŷP, hlt⟩⟩⟩
      · obtain ⟨y', hy'P, hy'f, hy'l⟩ :=
          exists_mem_of_mem_closure_of_lt₂ (continuous_inner_fst v) ℓ.continuous hŷD.1 hfgt hlt
        exact ⟨y', ⟨⟨hy'P, hy'f⟩, ⟨hy'P, hy'l⟩⟩⟩
    · obtain ⟨ξ, hξX⟩ := hXne
      have hξP : ξ ∈ Submission.PBox s c σ := hξX.1
      set t : ℝ := min (1 / 2) ((ℓ ŷ - lam) / (2 * (|ℓ ξ - ℓ ŷ| + 1))) with ht
      have htpos : 0 < t := lt_min (by norm_num) (by positivity)
      have htle : t ≤ 1 / 2 := min_le_left _ _
      have hDpos : 0 < ℓ ŷ - lam := by linarith
      have htbound : t * |ℓ ξ - ℓ ŷ| < (ℓ ŷ - lam) / 2 := by
        have h1 : t ≤ (ℓ ŷ - lam) / (2 * (|ℓ ξ - ℓ ŷ| + 1)) := min_le_right _ _
        have h3 : (ℓ ŷ - lam) / (2 * (|ℓ ξ - ℓ ŷ| + 1)) * |ℓ ξ - ℓ ŷ| < (ℓ ŷ - lam) / 2 := by
          rw [div_mul_eq_mul_div,
            div_lt_iff₀ (by positivity : (0 : ℝ) < 2 * (|ℓ ξ - ℓ ŷ| + 1))]
          have h4 : (ℓ ŷ - lam) / 2 * (2 * (|ℓ ξ - ℓ ŷ| + 1)) =
              (ℓ ŷ - lam) * (|ℓ ξ - ℓ ŷ| + 1) := by
            field_simp
          rw [h4]
          exact mul_lt_mul_of_pos_left
            (by linarith : |ℓ ξ - ℓ ŷ| < |ℓ ξ - ℓ ŷ| + 1) hDpos
        nlinarith [mul_le_mul_of_nonneg_right h1 (abs_nonneg (ℓ ξ - ℓ ŷ))]
      have hmemP : (1 - t) • ŷ + t • ξ ∈ Submission.PBox s c σ := by
        have h2 := (Work.Topology.SphereSlicing.convex_PBox s c σ).combo_closure_interior_mem_interior
          (x := ŷ) (y := ξ) (a := 1 - t) (b := t) hŷD.1
          (by rw [(Work.Topology.SphereSlicing.isOpen_PBox s c σ).interior_eq]; exact hξP)
          (by linarith) htpos (by ring)
        rwa [(Work.Topology.SphereSlicing.isOpen_PBox s c σ).interior_eq] at h2
      have hξf : inner ℝ v c + u + h < inner ℝ v ξ := hξX.2
      have hmemf : inner ℝ v c + u + h < inner ℝ v ((1 - t) • ŷ + t • ξ) := by
        rw [inner_add_right, inner_smul_right, inner_smul_right, ← hfeq]
        nlinarith [hξf, htpos, htle]
      have hmeml : lam < ℓ ((1 - t) • ŷ + t • ξ) := by
        rw [map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul]
        have h3 : ℓ ξ - ℓ ŷ ≤ |ℓ ξ - ℓ ŷ| := le_abs_self _
        have h4 : -(ℓ ξ - ℓ ŷ) ≤ |ℓ ξ - ℓ ŷ| := neg_le_abs _
        nlinarith [htbound, h3, h4, htpos, htle, hDpos]
      exact ⟨_, ⟨⟨hmemP, hmemf⟩, ⟨hmemP, hmeml⟩⟩⟩
  exact le_trans (hŷmax ⟨hz, hzf⟩) hgoal

/-- **The maximiser argument for the lower cap** (the mirror of
`le_lam_of_mem_tlsBoxCl_ge_face`). -/
theorem le_lam_of_mem_tlsBoxCl_le_face (hs : 0 < s) (hh : 0 < h) (hv : v ≠ 0) (hℓv : ℓ v = 0)
    (hℓne : ℓ ≠ 0)
    (hYne : (tlsDnCap s c σ u h v).Nonempty)
    (hno : ¬ (tlsDnCap s c σ u h v ∩ tlsWallOpen s c σ ℓ lam).Nonempty) :
    ∀ z ∈ tlsBoxCl s c σ, inner ℝ v z ≤ inner ℝ v c + u - h → ℓ z ≤ lam := by
  intro z hz hzf
  set D : Set R3 := tlsBoxCl s c σ ∩ {y : R3 | inner ℝ v y ≤ inner ℝ v c + u - h} with hD
  have hDc : IsCompact D := by
    rw [hD]
    exact (tlsBoxCl_isCompact hs).inter_right
      (isClosed_le (continuous_inner_fst v) continuous_const)
  have hDne : D.Nonempty := by
    obtain ⟨y, hy⟩ := hYne
    refine ⟨y, subset_closure hy.1, ?_⟩
    have hy2 : inner ℝ v y < inner ℝ v c + u - h := hy.2
    exact le_of_lt hy2
  obtain ⟨ŷ, hŷD, hŷmax⟩ := hDc.exists_isMaxOn hDne ℓ.continuous.continuousOn
  have hgoal : ℓ ŷ ≤ lam := by
    by_contra hcon
    have hlt : lam < ℓ ŷ := lt_of_not_ge hcon
    refine hno ?_
    have hŷf : inner ℝ v ŷ ≤ inner ℝ v c + u - h := hŷD.2
    rcases lt_or_eq_of_le hŷf with hflt | hfeq
    · by_cases hŷP : ŷ ∈ Submission.PBox s c σ
      · exact ⟨ŷ, ⟨⟨hŷP, hflt⟩, ⟨hŷP, hlt⟩⟩⟩
      · obtain ⟨y', hy'P, hy'f, hy'l⟩ :=
          exists_mem_of_mem_closure_of_gt₂ (continuous_inner_fst v) ℓ.continuous hŷD.1 hflt hlt
        exact ⟨y', ⟨⟨hy'P, hy'f⟩, ⟨hy'P, hy'l⟩⟩⟩
    · obtain ⟨ξ, hξY⟩ := hYne
      have hξP : ξ ∈ Submission.PBox s c σ := hξY.1
      set t : ℝ := min (1 / 2) ((ℓ ŷ - lam) / (2 * (|ℓ ξ - ℓ ŷ| + 1))) with ht
      have htpos : 0 < t := lt_min (by norm_num) (by positivity)
      have htle : t ≤ 1 / 2 := min_le_left _ _
      have hDpos : 0 < ℓ ŷ - lam := by linarith
      have htbound : t * |ℓ ξ - ℓ ŷ| < (ℓ ŷ - lam) / 2 := by
        have h1 : t ≤ (ℓ ŷ - lam) / (2 * (|ℓ ξ - ℓ ŷ| + 1)) := min_le_right _ _
        have h3 : (ℓ ŷ - lam) / (2 * (|ℓ ξ - ℓ ŷ| + 1)) * |ℓ ξ - ℓ ŷ| < (ℓ ŷ - lam) / 2 := by
          rw [div_mul_eq_mul_div,
            div_lt_iff₀ (by positivity : (0 : ℝ) < 2 * (|ℓ ξ - ℓ ŷ| + 1))]
          have h4 : (ℓ ŷ - lam) / 2 * (2 * (|ℓ ξ - ℓ ŷ| + 1)) =
              (ℓ ŷ - lam) * (|ℓ ξ - ℓ ŷ| + 1) := by
            field_simp
          rw [h4]
          exact mul_lt_mul_of_pos_left
            (by linarith : |ℓ ξ - ℓ ŷ| < |ℓ ξ - ℓ ŷ| + 1) hDpos
        nlinarith [mul_le_mul_of_nonneg_right h1 (abs_nonneg (ℓ ξ - ℓ ŷ))]
      have hmemP : (1 - t) • ŷ + t • ξ ∈ Submission.PBox s c σ := by
        have h2 := (Work.Topology.SphereSlicing.convex_PBox s c σ).combo_closure_interior_mem_interior
          (x := ŷ) (y := ξ) (a := 1 - t) (b := t) hŷD.1
          (by rw [(Work.Topology.SphereSlicing.isOpen_PBox s c σ).interior_eq]; exact hξP)
          (by linarith) htpos (by ring)
        rwa [(Work.Topology.SphereSlicing.isOpen_PBox s c σ).interior_eq] at h2
      have hξf : inner ℝ v ξ < inner ℝ v c + u - h := hξY.2
      have hmemf : inner ℝ v ((1 - t) • ŷ + t • ξ) < inner ℝ v c + u - h := by
        rw [inner_add_right, inner_smul_right, inner_smul_right, ← hfeq]
        nlinarith [hξf, htpos, htle]
      have hmeml : lam < ℓ ((1 - t) • ŷ + t • ξ) := by
        rw [map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul]
        have h3 : ℓ ξ - ℓ ŷ ≤ |ℓ ξ - ℓ ŷ| := le_abs_self _
        have h4 : -(ℓ ξ - ℓ ŷ) ≤ |ℓ ξ - ℓ ŷ| := neg_le_abs _
        nlinarith [htbound, h3, h4, htpos, htle, hDpos]
      exact ⟨_, ⟨⟨hmemP, hmemf⟩, ⟨hmemP, hmeml⟩⟩⟩
  exact le_trans (hŷmax ⟨hz, hzf⟩) hgoal

/-! ## Frontier of a union of two open sets whose traces meet only off the union -/

/-- **The frontier of a union of two sets** whose closure intersection misses the union. -/
theorem frontier_union_of_no_inter {A B : Set R3}
    (h : ∀ x : R3, x ∈ closure A → x ∈ closure B → x ∉ A ∪ B) :
    frontier (A ∪ B) = frontier A ∪ frontier B := by
  refine Set.Subset.antisymm ?_ ?_
  · intro x hx
    rw [(closure_sdiff_interior (A ∪ B)).symm, closure_union] at hx
    rcases hx with ⟨hxA | hxB, hxnot⟩
    · exact Or.inl ⟨hxA, fun hxi => hxnot (interior_mono Set.subset_union_left hxi)⟩
    · exact Or.inr ⟨hxB, fun hxi => hxnot (interior_mono Set.subset_union_right hxi)⟩
  · intro x hx
    rw [(closure_sdiff_interior (A ∪ B)).symm]
    rcases hx with hx | hx
    · refine ⟨closure_mono Set.subset_union_left hx.1, fun hxi => ?_⟩
      rcases interior_union_subset_closure A B hxi with h' | h'
      · exact hx.2 h'
      · exact (h x hx.1 h') (interior_subset hxi)
    · refine ⟨closure_mono Set.subset_union_right hx.1, fun hxi => ?_⟩
      rcases interior_union_subset_closure' A B hxi with h' | h'
      · exact (h x h' hx.1) (interior_subset hxi)
      · exact hx.2 h'

/-- If `ℓ ≤ lam` on the closed box, the wall region is empty. -/
theorem tlsWallClosed_eq_empty_of_le_lam (hℓne : ℓ ≠ 0)
    (hall : ∀ y ∈ tlsBoxCl s c σ, ℓ y ≤ lam) :
    tlsWallClosed s c σ ℓ lam = ∅ := by
  by_contra hne
  obtain ⟨z, hz⟩ := Set.nonempty_iff_ne_empty.mpr hne
  have hzp : z ∈ Submission.PBox s c σ := hz.1
  have hzl : lam ≤ ℓ z := hz.2
  have hzK : z ∈ tlsBoxCl s c σ := subset_closure hzp
  have hzlam : ℓ z = lam := le_antisymm (hall z hzK) hzl
  obtain ⟨w, hw⟩ := exists_pos_of_clm_ne hℓne
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.mp
    ((Work.Topology.SphereSlicing.isOpen_PBox s c σ).mem_nhds hzp)
  set t : ℝ := min (δ / (2 * (‖w‖ + 1))) 1 with ht
  have htpos : 0 < t := lt_min (by positivity) one_pos
  have htw : t * ‖w‖ < δ := by
    have h1 : t ≤ δ / (2 * (‖w‖ + 1)) := le_of_eq_of_le ht (min_le_left _ _)
    have h2 : δ / (2 * (‖w‖ + 1)) * ‖w‖ < δ := by
      rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity : (0 : ℝ) < 2 * (‖w‖ + 1))]
      nlinarith [norm_nonneg w, hδ]
    nlinarith [mul_le_mul_of_nonneg_right h1 (norm_nonneg w)]
  have hmem : z + t • w ∈ Submission.PBox s c σ := by
    refine hball ?_
    rw [Metric.mem_ball, dist_eq_norm]
    have hsub : z + t • w - z = t • w := by abel
    rw [hsub, norm_smul, Real.norm_eq_abs, abs_of_pos htpos]
    exact htw
  have hcontra := hall _ (subset_closure hmem)
  rw [map_add, map_smul, smul_eq_mul, hzlam] at hcontra
  have hpos : 0 < t * ℓ w := mul_pos htpos hw
  linarith

/-- **The ray argument**: a point of the closed box strictly above the upper slab face, at which `ℓ`
is bounded by `lam` on the part of the closed box above that face, bounds `ℓ` on the whole box. -/
theorem le_lam_of_mem_tlsBoxCl_of_strict {p : R3} (hpK : p ∈ tlsBoxCl s c σ)
    (hpgt : inner ℝ v c + u + h < inner ℝ v p)
    (hmax : ∀ z ∈ tlsBoxCl s c σ, inner ℝ v c + u + h ≤ inner ℝ v z → ℓ z ≤ lam)
    (hpl : ℓ p = lam) :
    ∀ y ∈ tlsBoxCl s c σ, ℓ y ≤ lam := by
  intro y hy
  set t : ℝ := min (1 / 2) ((inner ℝ v p - (inner ℝ v c + u + h)) /
    (2 * (|inner ℝ v y - inner ℝ v p| + 1))) with ht
  have htpos : 0 < t := lt_min (by norm_num) (by positivity)
  have htle : t ≤ 1 / 2 := min_le_left _ _
  have hD : 0 < inner ℝ v p - (inner ℝ v c + u + h) := by linarith
  have htbound : t * |inner ℝ v y - inner ℝ v p| <
      (inner ℝ v p - (inner ℝ v c + u + h)) / 2 := by
    have h1 : t ≤ (inner ℝ v p - (inner ℝ v c + u + h)) /
        (2 * (|inner ℝ v y - inner ℝ v p| + 1)) := min_le_right _ _
    have h3 : (inner ℝ v p - (inner ℝ v c + u + h)) /
        (2 * (|inner ℝ v y - inner ℝ v p| + 1)) * |inner ℝ v y - inner ℝ v p| <
        (inner ℝ v p - (inner ℝ v c + u + h)) / 2 := by
      rw [div_mul_eq_mul_div,
        div_lt_iff₀ (by positivity : (0 : ℝ) < 2 * (|inner ℝ v y - inner ℝ v p| + 1))]
      have h4 : (inner ℝ v p - (inner ℝ v c + u + h)) / 2 *
          (2 * (|inner ℝ v y - inner ℝ v p| + 1)) =
          (inner ℝ v p - (inner ℝ v c + u + h)) * (|inner ℝ v y - inner ℝ v p| + 1) := by
        field_simp
      rw [h4]
      exact mul_lt_mul_of_pos_left
        (by linarith : |inner ℝ v y - inner ℝ v p| < |inner ℝ v y - inner ℝ v p| + 1) hD
    nlinarith [mul_le_mul_of_nonneg_right h1 (abs_nonneg (inner ℝ v y - inner ℝ v p))]
  have hpt : (1 - t) • p + t • y ∈ tlsBoxCl s c σ :=
    tlsBoxCl_convex hpK hy (by linarith) (le_of_lt htpos) (by ring)
  have hptf : inner ℝ v c + u + h ≤ inner ℝ v ((1 - t) • p + t • y) := by
    rw [inner_add_right, inner_smul_right, inner_smul_right]
    have h3 : -(inner ℝ v y - inner ℝ v p) ≤ |inner ℝ v y - inner ℝ v p| := neg_le_abs _
    nlinarith [htbound, h3, htpos, htle]
  have hle := hmax _ hpt hptf
  rw [map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul, hpl] at hle
  nlinarith [hle, htpos]

/-! ## Moving along `crossDir` on a box face -/

/-- For `i₀ : Fin 3`, a positive lower bound for all the other coordinates. -/
lemma exists_pos_le_of_ne {i₀ : Fin 3} {f : Fin 3 → ℝ} (hf : ∀ i, i ≠ i₀ → 0 < f i) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ i : Fin 3, i ≠ i₀ → ε ≤ f i := by
  refine ⟨min (min (1 / 2) (f (i₀ + 1))) (f (i₀ + 2)), ?_, ?_⟩
  · refine lt_min (lt_min (by norm_num) ?_) ?_
    · exact hf _ (by fin_cases i₀ <;> decide)
    · exact hf _ (by fin_cases i₀ <;> decide)
  · intro i hi
    have hcases : i = i₀ + 1 ∨ i = i₀ + 2 := by
      revert hi
      fin_cases i <;> fin_cases i₀ <;> decide
    rcases hcases with h | h
    · rw [h]; exact le_trans (min_le_left _ _) (min_le_right _ _)
    · rw [h]; exact min_le_right _ _

/-- **Moving along `crossDir` on a face above the slab.**  At a point of the closed box with a
single extremal coordinate `σ i₀`, on which `ℓ` is bounded by `lam` above the upper slab face, the
move along `crossDir v (σ i₀)` is level-preserving for `ℓ`. -/
theorem l_crossDir_eq_zero_of_face (hs : 0 < s) {i₀ : Fin 3} {p : R3}
    (hpK : p ∈ tlsBoxCl s c σ)
    (hface : |p (σ i₀) - c (σ i₀)| = Submission.boxSide i₀ * s)
    (hstrict : ∀ i : Fin 3, i ≠ i₀ → |p (σ i) - c (σ i)| < Submission.boxSide i * s)
    (hpf : inner ℝ v c + u + h ≤ inner ℝ v p)
    (hmax : ∀ z ∈ tlsBoxCl s c σ, inner ℝ v c + u + h ≤ inner ℝ v z → ℓ z ≤ lam)
    (hpl : ℓ p = lam) :
    ℓ (crossDir v (σ i₀)) = 0 := by
  set w : R3 := crossDir v (σ i₀) with hw
  have hwi : w (σ i₀) = 0 := by rw [hw]; exact crossDir_apply_self v (σ i₀)
  have hwin : inner ℝ v w = 0 := by rw [hw]; exact inner_crossDir v (σ i₀)
  obtain ⟨ε, hεpos, hε⟩ := exists_pos_le_of_ne (i₀ := i₀)
    (f := fun i => (Submission.boxSide i * s - |p (σ i) - c (σ i)|) / (|w (σ i)| + 1))
    (fun i hi => div_pos (by linarith [hstrict i hi]) (by positivity))
  have hmove : ∀ μ : ℝ, |μ| ≤ ε → p + μ • w ∈ tlsBoxCl s c σ := by
    intro μ hμ
    rw [mem_tlsBoxCl_iff hs]
    apply boxNorm_le_of_abs_coord_le
    intro i
    by_cases hi : i = i₀
    · have hwi' : w (σ i) = 0 := by rw [hi]; exact hwi
      have hfaci : |p (σ i) - c (σ i)| = Submission.boxSide i * s := by rw [hi]; exact hface
      have hcoord : (p + μ • w) (σ i) = p (σ i) := by simp [hwi']
      rw [hcoord, hfaci]
    · have hcoord : (p + μ • w) (σ i) = p (σ i) + μ * w (σ i) := by simp
      rw [hcoord]
      have hle1 : |p (σ i) + μ * w (σ i) - c (σ i)| ≤
          |p (σ i) - c (σ i)| + ε * (|w (σ i)| + 1) := by
        have hcongr : p (σ i) + μ * w (σ i) - c (σ i) = (p (σ i) - c (σ i)) + μ * w (σ i) := by
          ring
        rw [hcongr]
        calc |(p (σ i) - c (σ i)) + μ * w (σ i)| ≤ |p (σ i) - c (σ i)| + |μ * w (σ i)| :=
              abs_add_le _ _
          _ = |p (σ i) - c (σ i)| + |μ| * |w (σ i)| := by rw [abs_mul]
          _ ≤ |p (σ i) - c (σ i)| + ε * (|w (σ i)| + 1) := by
              have h3 := mul_le_mul_of_nonneg_right hμ (abs_nonneg (w (σ i)))
              nlinarith [abs_nonneg (w (σ i))]
      have hle2 : |p (σ i) - c (σ i)| + ε * (|w (σ i)| + 1) ≤ Submission.boxSide i * s := by
        have h4 := mul_le_mul_of_nonneg_right (hε i hi) (by positivity : (0 : ℝ) ≤ |w (σ i)| + 1)
        rw [div_mul_cancel₀ _ (by positivity : (|w (σ i)| + 1) ≠ 0)] at h4
        linarith [h4]
      linarith [hle1, hle2]
  have hmem1 : p + ε • w ∈ tlsBoxCl s c σ := hmove ε (le_of_eq (abs_of_pos hεpos))
  have hmem2 : p + (-ε) • w ∈ tlsBoxCl s c σ := by
    refine hmove (-ε) ?_
    rw [abs_neg, abs_of_pos hεpos]
  have hf1 : inner ℝ v c + u + h ≤ inner ℝ v (p + ε • w) := by
    rw [inner_add_right, inner_smul_right, hwin, mul_zero, add_zero]; exact hpf
  have hf2 : inner ℝ v c + u + h ≤ inner ℝ v (p + (-ε) • w) := by
    rw [inner_add_right, inner_smul_right, hwin, mul_zero, add_zero]; exact hpf
  have hres1 := hmax _ hmem1 hf1
  have hres2 := hmax _ hmem2 hf2
  rw [map_add, map_smul, smul_eq_mul, hpl] at hres1 hres2
  have hzero : ε * ℓ w = 0 := by linarith
  rcases mul_eq_zero.mp hzero with h | h
  · exact absurd h (ne_of_gt hεpos)
  · exact h

/-- **Moving along `crossDir` on a face below the slab** (the mirror of
`l_crossDir_eq_zero_of_face`). -/
theorem l_crossDir_eq_zero_of_face_dn (hs : 0 < s) {i₀ : Fin 3} {p : R3}
    (hpK : p ∈ tlsBoxCl s c σ)
    (hface : |p (σ i₀) - c (σ i₀)| = Submission.boxSide i₀ * s)
    (hstrict : ∀ i : Fin 3, i ≠ i₀ → |p (σ i) - c (σ i)| < Submission.boxSide i * s)
    (hpf : inner ℝ v p ≤ inner ℝ v c + u - h)
    (hmax : ∀ z ∈ tlsBoxCl s c σ, inner ℝ v z ≤ inner ℝ v c + u - h → ℓ z ≤ lam)
    (hpl : ℓ p = lam) :
    ℓ (crossDir v (σ i₀)) = 0 := by
  set w : R3 := crossDir v (σ i₀) with hw
  have hwi : w (σ i₀) = 0 := by rw [hw]; exact crossDir_apply_self v (σ i₀)
  have hwin : inner ℝ v w = 0 := by rw [hw]; exact inner_crossDir v (σ i₀)
  obtain ⟨ε, hεpos, hε⟩ := exists_pos_le_of_ne (i₀ := i₀)
    (f := fun i => (Submission.boxSide i * s - |p (σ i) - c (σ i)|) / (|w (σ i)| + 1))
    (fun i hi => div_pos (by linarith [hstrict i hi]) (by positivity))
  have hmove : ∀ μ : ℝ, |μ| ≤ ε → p + μ • w ∈ tlsBoxCl s c σ := by
    intro μ hμ
    rw [mem_tlsBoxCl_iff hs]
    apply boxNorm_le_of_abs_coord_le
    intro i
    by_cases hi : i = i₀
    · have hwi' : w (σ i) = 0 := by rw [hi]; exact hwi
      have hfaci : |p (σ i) - c (σ i)| = Submission.boxSide i * s := by rw [hi]; exact hface
      have hcoord : (p + μ • w) (σ i) = p (σ i) := by simp [hwi']
      rw [hcoord, hfaci]
    · have hcoord : (p + μ • w) (σ i) = p (σ i) + μ * w (σ i) := by simp
      rw [hcoord]
      have hle1 : |p (σ i) + μ * w (σ i) - c (σ i)| ≤
          |p (σ i) - c (σ i)| + ε * (|w (σ i)| + 1) := by
        have hcongr : p (σ i) + μ * w (σ i) - c (σ i) = (p (σ i) - c (σ i)) + μ * w (σ i) := by
          ring
        rw [hcongr]
        calc |(p (σ i) - c (σ i)) + μ * w (σ i)| ≤ |p (σ i) - c (σ i)| + |μ * w (σ i)| :=
              abs_add_le _ _
          _ = |p (σ i) - c (σ i)| + |μ| * |w (σ i)| := by rw [abs_mul]
          _ ≤ |p (σ i) - c (σ i)| + ε * (|w (σ i)| + 1) := by
              have h3 := mul_le_mul_of_nonneg_right hμ (abs_nonneg (w (σ i)))
              nlinarith [abs_nonneg (w (σ i))]
      have hle2 : |p (σ i) - c (σ i)| + ε * (|w (σ i)| + 1) ≤ Submission.boxSide i * s := by
        have h4 := mul_le_mul_of_nonneg_right (hε i hi) (by positivity : (0 : ℝ) ≤ |w (σ i)| + 1)
        rw [div_mul_cancel₀ _ (by positivity : (|w (σ i)| + 1) ≠ 0)] at h4
        linarith [h4]
      linarith [hle1, hle2]
  have hmem1 : p + ε • w ∈ tlsBoxCl s c σ := hmove ε (le_of_eq (abs_of_pos hεpos))
  have hmem2 : p + (-ε) • w ∈ tlsBoxCl s c σ := by
    refine hmove (-ε) ?_
    rw [abs_neg, abs_of_pos hεpos]
  have hf1 : inner ℝ v (p + ε • w) ≤ inner ℝ v c + u - h := by
    rw [inner_add_right, inner_smul_right, hwin, mul_zero, add_zero]; exact hpf
  have hf2 : inner ℝ v (p + (-ε) • w) ≤ inner ℝ v c + u - h := by
    rw [inner_add_right, inner_smul_right, hwin, mul_zero, add_zero]; exact hpf
  have hres1 := hmax _ hmem1 hf1
  have hres2 := hmax _ hmem2 hf2
  rw [map_add, map_smul, smul_eq_mul, hpl] at hres1 hres2
  have hzero : ε * ℓ w = 0 := by linarith
  rcases mul_eq_zero.mp hzero with h | h
  · exact absurd h (ne_of_gt hεpos)
  · exact h

/-! ## The separation lemmas: the closures of a cap and of the wall region -/

/-- **The upper cap is separated from the wall region.**  If the box has no point above the wall
beyond the upper slab face, then no point of the removed set lies in both
`closure (tlsUpCap s c σ u h v)` and `closure (tlsWallClosed s c σ ℓ lam)`. -/
theorem not_mem_removed_of_mem_closure_upCap_wallClosed
    (hs : 0 < s) (hh : 0 < h) (hv : v ≠ 0) (hℓv : ℓ v = 0) (hℓne : ℓ ≠ 0)
    (hno : ¬ (tlsUpCap s c σ u h v ∩ tlsWallOpen s c σ ℓ lam).Nonempty)
    {p : R3} (hpX : p ∈ closure (tlsUpCap s c σ u h v))
    (hpZ : p ∈ closure (tlsWallClosed s c σ ℓ lam)) :
    p ∉ Work.Drive.Mono.tiltedLevelRemoved s c σ u v h ℓ lam := by
  intro hpR
  have hXne : (tlsUpCap s c σ u h v).Nonempty := by
    by_contra h
    rw [Set.not_nonempty_iff_eq_empty.mp h, closure_empty] at hpX
    exact hpX
  have hmax := le_lam_of_mem_tlsBoxCl_ge_face hs hh hv hℓv hℓne hXne hno
  have hpK : p ∈ tlsBoxCl s c σ := (closure_tlsUpCap_subset hpX).1
  have hpf : inner ℝ v c + u + h ≤ inner ℝ v p := (closure_tlsUpCap_subset hpX).2
  have hple : ℓ p = lam := le_antisymm (hmax p hpK hpf) (closure_tlsWallClosed_subset hpZ).2
  rw [tiltedLevelRemoved_eq_three] at hpR
  rcases hpR with hpR | hpR
  · rcases hpR with hpX' | hpY'
    · have hXf : inner ℝ v c + u + h < inner ℝ v p := hpX'.2
      exact hno (exists_mem_upCap_inter_wallOpen hv hℓv hℓne hpX'.1 (le_of_lt hXf) hple)
    · have hYf : inner ℝ v p < inner ℝ v c + u - h := hpY'.2
      linarith [hpf, hYf]
  · have hZp : p ∈ Submission.PBox s c σ := hpR.1
    by_cases hgt : inner ℝ v c + u + h < inner ℝ v p
    · exact hno (exists_mem_upCap_inter_wallOpen hv hℓv hℓne hZp (le_of_lt hgt) hple)
    · have hpeq : inner ℝ v p = inner ℝ v c + u + h := le_antisymm (le_of_not_gt hgt) hpf
      exact hno (exists_mem_upCap_inter_wallOpen hv hℓv hℓne hZp (le_of_eq hpeq.symm) hple)

/-- **The lower cap is separated from the wall region** (the mirror of
`not_mem_removed_of_mem_closure_upCap_wallClosed`). -/
theorem not_mem_removed_of_mem_closure_dnCap_wallClosed
    (hs : 0 < s) (hh : 0 < h) (hv : v ≠ 0) (hℓv : ℓ v = 0) (hℓne : ℓ ≠ 0)
    (hno : ¬ (tlsDnCap s c σ u h v ∩ tlsWallOpen s c σ ℓ lam).Nonempty)
    {p : R3} (hpY : p ∈ closure (tlsDnCap s c σ u h v))
    (hpZ : p ∈ closure (tlsWallClosed s c σ ℓ lam)) :
    p ∉ Work.Drive.Mono.tiltedLevelRemoved s c σ u v h ℓ lam := by
  intro hpR
  have hYne : (tlsDnCap s c σ u h v).Nonempty := by
    by_contra h
    rw [Set.not_nonempty_iff_eq_empty.mp h, closure_empty] at hpY
    exact hpY
  have hmax := le_lam_of_mem_tlsBoxCl_le_face hs hh hv hℓv hℓne hYne hno
  have hpK : p ∈ tlsBoxCl s c σ := (closure_tlsDnCap_subset hpY).1
  have hpf : inner ℝ v p ≤ inner ℝ v c + u - h := (closure_tlsDnCap_subset hpY).2
  have hple : ℓ p = lam := le_antisymm (hmax p hpK hpf) (closure_tlsWallClosed_subset hpZ).2
  rw [tiltedLevelRemoved_eq_three] at hpR
  rcases hpR with hpR | hpR
  · rcases hpR with hpX' | hpY'
    · have hXf : inner ℝ v c + u + h < inner ℝ v p := hpX'.2
      linarith [hpf, hXf]
    · have hYf : inner ℝ v p < inner ℝ v c + u - h := hpY'.2
      exact hno (exists_mem_dnCap_inter_wallOpen hv hℓv hℓne hpY'.1 (le_of_lt hYf) hple)
  · have hZp : p ∈ Submission.PBox s c σ := hpR.1
    by_cases hlt : inner ℝ v p < inner ℝ v c + u - h
    · exact hno (exists_mem_dnCap_inter_wallOpen hv hℓv hℓne hZp (le_of_lt hlt) hple)
    · have hpeq : inner ℝ v p = inner ℝ v c + u - h := le_antisymm hpf (le_of_not_gt hlt)
      exact hno (exists_mem_dnCap_inter_wallOpen hv hℓv hℓne hZp (le_of_eq hpeq) hple)

/-- **The ray argument below the slab** (the mirror of `le_lam_of_mem_tlsBoxCl_of_strict`). -/
theorem le_lam_of_mem_tlsBoxCl_of_strict_dn {p : R3} (hpK : p ∈ tlsBoxCl s c σ)
    (hplt : inner ℝ v p < inner ℝ v c + u - h)
    (hmax : ∀ z ∈ tlsBoxCl s c σ, inner ℝ v z ≤ inner ℝ v c + u - h → ℓ z ≤ lam)
    (hpl : ℓ p = lam) :
    ∀ y ∈ tlsBoxCl s c σ, ℓ y ≤ lam := by
  intro y hy
  set t : ℝ := min (1 / 2) (((inner ℝ v c + u - h) - inner ℝ v p) /
    (2 * (|inner ℝ v y - inner ℝ v p| + 1))) with ht
  have htpos : 0 < t := lt_min (by norm_num) (by positivity)
  have htle : t ≤ 1 / 2 := min_le_left _ _
  have hD : 0 < (inner ℝ v c + u - h) - inner ℝ v p := by linarith
  have htbound : t * |inner ℝ v y - inner ℝ v p| <
      ((inner ℝ v c + u - h) - inner ℝ v p) / 2 := by
    have h1 : t ≤ ((inner ℝ v c + u - h) - inner ℝ v p) /
        (2 * (|inner ℝ v y - inner ℝ v p| + 1)) := min_le_right _ _
    have h3 : ((inner ℝ v c + u - h) - inner ℝ v p) /
        (2 * (|inner ℝ v y - inner ℝ v p| + 1)) * |inner ℝ v y - inner ℝ v p| <
        ((inner ℝ v c + u - h) - inner ℝ v p) / 2 := by
      rw [div_mul_eq_mul_div,
        div_lt_iff₀ (by positivity : (0 : ℝ) < 2 * (|inner ℝ v y - inner ℝ v p| + 1))]
      have h4 : ((inner ℝ v c + u - h) - inner ℝ v p) / 2 *
          (2 * (|inner ℝ v y - inner ℝ v p| + 1)) =
          ((inner ℝ v c + u - h) - inner ℝ v p) * (|inner ℝ v y - inner ℝ v p| + 1) := by
        field_simp
      rw [h4]
      exact mul_lt_mul_of_pos_left
        (by linarith : |inner ℝ v y - inner ℝ v p| < |inner ℝ v y - inner ℝ v p| + 1) hD
    nlinarith [mul_le_mul_of_nonneg_right h1 (abs_nonneg (inner ℝ v y - inner ℝ v p))]
  have hpt : (1 - t) • p + t • y ∈ tlsBoxCl s c σ :=
    tlsBoxCl_convex hpK hy (by linarith) (le_of_lt htpos) (by ring)
  have hptf : inner ℝ v ((1 - t) • p + t • y) ≤ inner ℝ v c + u - h := by
    rw [inner_add_right, inner_smul_right, inner_smul_right]
    have h3 : inner ℝ v y - inner ℝ v p ≤ |inner ℝ v y - inner ℝ v p| := le_abs_self _
    nlinarith [htbound, h3, htpos, htle]
  have hle := hmax _ hpt hptf
  rw [map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul, hpl] at hle
  nlinarith [hle, htpos]

/-! ## The two frontier pieces meet only off the surface -/

/-- **The upper cap and the wall region meet only off the surface.** -/
theorem inter_closure_upCap_wallClosed_off_carrier
    (hs : 0 < s) (hh : 0 < h) (hv : v ≠ 0) (hℓv : ℓ v = 0) (hℓne : ℓ ≠ 0)
    (hcross : ∀ i : Fin 3, i ≠ 2 → ℓ (crossDir v (σ i)) ≠ 0)
    (hEF : Work.Drive.Mono.EdgeFree ψ s c σ u v h)
    (hbelt : ∀ z, z ∈ (Work.Drive.EpsSphere.torusOf ψ).carrier →
      z ∈ closure (Submission.PBox s c σ) → |slabFn c u v z| ≤ h →
      |z (σ 2) - c (σ 2)| < Submission.boxSide 2 * s)
    (hZne : (tlsWallClosed s c σ ℓ lam).Nonempty)
    (hno : ¬ (tlsUpCap s c σ u h v ∩ tlsWallOpen s c σ ℓ lam).Nonempty)
    {p : R3} (hpX : p ∈ closure (tlsUpCap s c σ u h v))
    (hpZ : p ∈ closure (tlsWallClosed s c σ ℓ lam))
    (hpR : p ∉ Work.Drive.Mono.tiltedLevelRemoved s c σ u v h ℓ lam)
    (hpc : p ∈ (Work.Drive.EpsSphere.torusOf ψ).carrier) : False := by
  have hXne : (tlsUpCap s c σ u h v).Nonempty := by
    by_contra h
    rw [Set.not_nonempty_iff_eq_empty.mp h, closure_empty] at hpX
    exact hpX
  have hmax := le_lam_of_mem_tlsBoxCl_ge_face hs hh hv hℓv hℓne hXne hno
  have hpK : p ∈ tlsBoxCl s c σ := (closure_tlsUpCap_subset hpX).1
  have hpf : inner ℝ v c + u + h ≤ inner ℝ v p := (closure_tlsUpCap_subset hpX).2
  have hpl : ℓ p = lam := le_antisymm (hmax p hpK hpf) (closure_tlsWallClosed_subset hpZ).2
  have hpP : p ∉ Submission.PBox s c σ := by
    intro hpP'
    by_cases hgt : inner ℝ v c + u + h < inner ℝ v p
    · exact hno (exists_mem_upCap_inter_wallOpen hv hℓv hℓne hpP' (le_of_lt hgt) hpl)
    · have hpeq : inner ℝ v p = inner ℝ v c + u + h := le_antisymm (le_of_not_gt hgt) hpf
      exact hno (exists_mem_upCap_inter_wallOpen hv hℓv hℓne hpP' (le_of_eq hpeq.symm) hpl)
  have hbN : Submission.boxNorm c σ p = s := by
    have h1 : Submission.boxNorm c σ p ≤ s := (mem_tlsBoxCl_iff hs).mp hpK
    have h2 : ¬ Submission.boxNorm c σ p < s :=
      fun hlt => hpP ((Submission.mem_PBox_iff s c σ p).mpr hlt)
    exact le_antisymm h1 (le_of_not_gt h2)
  by_cases hfgt : inner ℝ v c + u + h < inner ℝ v p
  · obtain ⟨z, hz⟩ := hZne
    rw [tlsWallClosed_eq_empty_of_le_lam hℓne
      (le_lam_of_mem_tlsBoxCl_of_strict hpK hfgt hmax hpl)] at hz
    exact hz
  · have hfeq : inner ℝ v p = inner ℝ v c + u + h := le_antisymm (le_of_not_gt hfgt) hpf
    have hext : ∃ i : Fin 3, |p (σ i) - c (σ i)| = Submission.boxSide i * s :=
      exists_extremal_of_boxNorm_eq hs hbN
    by_cases htwo : ∃ i j : Fin 3, i ≠ j ∧
        |p (σ i) - c (σ i)| = Submission.boxSide i * s ∧
        |p (σ j) - c (σ j)| = Submission.boxSide j * s
    · obtain ⟨i, j, hij, hi, hj⟩ := htwo
      have hcon := hEF p hpc hbN ⟨i, j, hij, hi, hj⟩
      have hval : inner ℝ v p - (inner ℝ v c + u) = h := by linarith
      rw [hval, abs_of_pos hh] at hcon
      exact absurd hcon (lt_irrefl h)
    · obtain ⟨i₀, hi₀⟩ := hext
      have huniq : ∀ i : Fin 3, |p (σ i) - c (σ i)| = Submission.boxSide i * s → i = i₀ := by
        intro i hi
        by_contra hne
        exact htwo ⟨i, i₀, hne, hi, hi₀⟩
      have hstrict : ∀ i : Fin 3, i ≠ i₀ → |p (σ i) - c (σ i)| < Submission.boxSide i * s := by
        intro i hi
        have h1 : |p (σ i) - c (σ i)| ≤ Submission.boxSide i * s :=
          abs_coord_le_of_mem_tlsBoxCl hpK i
        have h2 : |p (σ i) - c (σ i)| ≠ Submission.boxSide i * s := fun he => hi (huniq i he)
        exact lt_of_le_of_ne h1 h2
      by_cases hi₂ : i₀ = 2
      · have hslab : |slabFn c u v p| ≤ h := by
          rw [slabFn_apply]
          have hval : inner ℝ v p - (inner ℝ v c + u) = h := by linarith
          rw [hval, abs_of_pos hh]
        have hb := hbelt p hpc hpK hslab
        rw [hi₂] at hi₀
        linarith [hi₀, hb]
      · have hzero := l_crossDir_eq_zero_of_face (s := s) (c := c) (σ := σ) (u := u) (h := h)
          (v := v) (ℓ := ℓ) (lam := lam) hs hpK hi₀ hstrict hpf hmax hpl
        exact hcross i₀ hi₂ hzero

/-- **The lower cap and the wall region meet only off the surface** (the mirror of
`inter_closure_upCap_wallClosed_off_carrier`). -/
theorem inter_closure_dnCap_wallClosed_off_carrier
    (hs : 0 < s) (hh : 0 < h) (hv : v ≠ 0) (hℓv : ℓ v = 0) (hℓne : ℓ ≠ 0)
    (hcross : ∀ i : Fin 3, i ≠ 2 → ℓ (crossDir v (σ i)) ≠ 0)
    (hEF : Work.Drive.Mono.EdgeFree ψ s c σ u v h)
    (hbelt : ∀ z, z ∈ (Work.Drive.EpsSphere.torusOf ψ).carrier →
      z ∈ closure (Submission.PBox s c σ) → |slabFn c u v z| ≤ h →
      |z (σ 2) - c (σ 2)| < Submission.boxSide 2 * s)
    (hZne : (tlsWallClosed s c σ ℓ lam).Nonempty)
    (hno : ¬ (tlsDnCap s c σ u h v ∩ tlsWallOpen s c σ ℓ lam).Nonempty)
    {p : R3} (hpY : p ∈ closure (tlsDnCap s c σ u h v))
    (hpZ : p ∈ closure (tlsWallClosed s c σ ℓ lam))
    (hpR : p ∉ Work.Drive.Mono.tiltedLevelRemoved s c σ u v h ℓ lam)
    (hpc : p ∈ (Work.Drive.EpsSphere.torusOf ψ).carrier) : False := by
  have hYne : (tlsDnCap s c σ u h v).Nonempty := by
    by_contra h
    rw [Set.not_nonempty_iff_eq_empty.mp h, closure_empty] at hpY
    exact hpY
  have hmax := le_lam_of_mem_tlsBoxCl_le_face hs hh hv hℓv hℓne hYne hno
  have hpK : p ∈ tlsBoxCl s c σ := (closure_tlsDnCap_subset hpY).1
  have hpf : inner ℝ v p ≤ inner ℝ v c + u - h := (closure_tlsDnCap_subset hpY).2
  have hpl : ℓ p = lam := le_antisymm (hmax p hpK hpf) (closure_tlsWallClosed_subset hpZ).2
  have hpP : p ∉ Submission.PBox s c σ := by
    intro hpP'
    by_cases hlt : inner ℝ v p < inner ℝ v c + u - h
    · exact hpR (by
        rw [tiltedLevelRemoved_eq_three]
        exact Or.inl (Or.inr ⟨hpP', hlt⟩))
    · have hpeq : inner ℝ v p = inner ℝ v c + u - h := le_antisymm hpf (le_of_not_gt hlt)
      exact hno (exists_mem_dnCap_inter_wallOpen hv hℓv hℓne hpP' (le_of_eq hpeq) hpl)
  have hbN : Submission.boxNorm c σ p = s := by
    have h1 : Submission.boxNorm c σ p ≤ s := (mem_tlsBoxCl_iff hs).mp hpK
    have h2 : ¬ Submission.boxNorm c σ p < s :=
      fun hlt => hpP ((Submission.mem_PBox_iff s c σ p).mpr hlt)
    exact le_antisymm h1 (le_of_not_gt h2)
  by_cases hflt : inner ℝ v p < inner ℝ v c + u - h
  · obtain ⟨z, hz⟩ := hZne
    rw [tlsWallClosed_eq_empty_of_le_lam hℓne
      (le_lam_of_mem_tlsBoxCl_of_strict_dn hpK hflt hmax hpl)] at hz
    exact hz
  · have hfeq : inner ℝ v p = inner ℝ v c + u - h := le_antisymm hpf (le_of_not_gt hflt)
    have hext : ∃ i : Fin 3, |p (σ i) - c (σ i)| = Submission.boxSide i * s :=
      exists_extremal_of_boxNorm_eq hs hbN
    by_cases htwo : ∃ i j : Fin 3, i ≠ j ∧
        |p (σ i) - c (σ i)| = Submission.boxSide i * s ∧
        |p (σ j) - c (σ j)| = Submission.boxSide j * s
    · obtain ⟨i, j, hij, hi, hj⟩ := htwo
      have hcon := hEF p hpc hbN ⟨i, j, hij, hi, hj⟩
      have hval : inner ℝ v p - (inner ℝ v c + u) = -h := by linarith
      rw [hval, abs_neg, abs_of_pos hh] at hcon
      exact absurd hcon (lt_irrefl h)
    · obtain ⟨i₀, hi₀⟩ := hext
      have huniq : ∀ i : Fin 3, |p (σ i) - c (σ i)| = Submission.boxSide i * s → i = i₀ := by
        intro i hi
        by_contra hne
        exact htwo ⟨i, i₀, hne, hi, hi₀⟩
      have hstrict : ∀ i : Fin 3, i ≠ i₀ → |p (σ i) - c (σ i)| < Submission.boxSide i * s := by
        intro i hi
        have h1 : |p (σ i) - c (σ i)| ≤ Submission.boxSide i * s :=
          abs_coord_le_of_mem_tlsBoxCl hpK i
        have h2 : |p (σ i) - c (σ i)| ≠ Submission.boxSide i * s := fun he => hi (huniq i he)
        exact lt_of_le_of_ne h1 h2
      by_cases hi₂ : i₀ = 2
      · have hslab : |slabFn c u v p| ≤ h := by
          rw [slabFn_apply]
          have hval : inner ℝ v p - (inner ℝ v c + u) = -h := by linarith
          rw [hval, abs_neg, abs_of_pos hh]
        have hb := hbelt p hpc hpK hslab
        rw [hi₂] at hi₀
        linarith [hi₀, hb]
      · have hzero := l_crossDir_eq_zero_of_face_dn (s := s) (c := c) (σ := σ) (u := u) (h := h)
          (v := v) (ℓ := ℓ) (lam := lam) hs hpK hi₀ hstrict hpf hmax hpl
        exact hcross i₀ hi₂ hzero

/-! ## Assembling a carrier-disjoint union of spheres -/

/-- Two "empty or sphere" pieces give a family of spheres disjoint on `F`. -/
theorem sphere_decomposition_of_two_carrier (F A B : Set R3)
    (hA : A = ∅ ∨ Work.InnermostDisk.IsEmbeddedSphere A)
    (hB : B = ∅ ∨ Work.InnermostDisk.IsEmbeddedSphere B)
    (hd : Disjoint (A ∩ F) (B ∩ F)) :
    ∃ (n : ℕ) (S : Fin n → Set R3),
      (∀ i, Work.InnermostDisk.IsEmbeddedSphere (S i)) ∧
      (∀ i j : Fin n, i ≠ j → Disjoint (S i ∩ F) (S j ∩ F)) ∧ A ∪ B = ⋃ i, S i := by
  rcases hA with rfl | hA
  · rcases hB with rfl | hB
    · exact ⟨0, Fin.elim0, by intro i; exact Fin.elim0 i, by intro i; exact Fin.elim0 i, by simp⟩
    · rw [Set.empty_union]
      exact ⟨1, fun _ => B, fun i => hB, fun i j hij => absurd (Subsingleton.elim i j) hij,
        (Set.iUnion_const B).symm⟩
  · rcases hB with rfl | hB
    · rw [Set.union_empty]
      exact ⟨1, fun _ => A, fun i => hA, fun i j hij => absurd (Subsingleton.elim i j) hij,
        (Set.iUnion_const A).symm⟩
    · refine ⟨2, ![A, B], ?_, ?_, ?_⟩
      · intro i
        fin_cases i
        · simpa using hA
        · simpa using hB
      · intro i j hij
        fin_cases i <;> fin_cases j
        · exact absurd rfl hij
        · exact hd
        · exact hd.symm
        · exact absurd rfl hij
      · ext x
        constructor
        · rintro (h | h)
          · exact Set.mem_iUnion.mpr ⟨0, by simpa using h⟩
          · exact Set.mem_iUnion.mpr ⟨1, by simpa using h⟩
        · intro h
          rcases Set.mem_iUnion.mp h with ⟨i, hi⟩
          fin_cases i
          · exact Or.inl (by simpa using hi)
          · exact Or.inr (by simpa using hi)

/-- Three "empty or sphere" pieces give a family of spheres disjoint on `F`. -/
theorem sphere_decomposition_of_three_carrier (F A B C : Set R3)
    (hA : A = ∅ ∨ Work.InnermostDisk.IsEmbeddedSphere A)
    (hB : B = ∅ ∨ Work.InnermostDisk.IsEmbeddedSphere B)
    (hC : C = ∅ ∨ Work.InnermostDisk.IsEmbeddedSphere C)
    (hAB : Disjoint (A ∩ F) (B ∩ F)) (hAC : Disjoint (A ∩ F) (C ∩ F))
    (hBC : Disjoint (B ∩ F) (C ∩ F)) :
    ∃ (n : ℕ) (S : Fin n → Set R3),
      (∀ i, Work.InnermostDisk.IsEmbeddedSphere (S i)) ∧
      (∀ i j : Fin n, i ≠ j → Disjoint (S i ∩ F) (S j ∩ F)) ∧ A ∪ B ∪ C = ⋃ i, S i := by
  rcases hA with rfl | hA
  · rw [Set.empty_union]
    exact sphere_decomposition_of_two_carrier F B C hB hC hBC
  rcases hB with rfl | hB
  · rw [Set.union_empty]
    exact sphere_decomposition_of_two_carrier F A C (Or.inr hA) hC hAC
  rcases hC with rfl | hC
  · rw [Set.union_empty]
    exact sphere_decomposition_of_two_carrier F A B (Or.inr hA) (Or.inr hB) hAB
  refine ⟨3, ![A, B, C], ?_, ?_, ?_⟩
  · intro i
    fin_cases i
    · simpa using hA
    · simpa using hB
    · simpa using hC
  · intro i j hij
    fin_cases i <;> fin_cases j
    · exact absurd rfl hij
    · exact hAB
    · exact hAC
    · exact hAB.symm
    · exact absurd rfl hij
    · exact hBC
    · exact hAC.symm
    · exact hBC.symm
    · exact absurd rfl hij
  · ext x
    constructor
    · rintro ((h | h) | h)
      · exact Set.mem_iUnion.mpr ⟨0, by simpa using h⟩
      · exact Set.mem_iUnion.mpr ⟨1, by simpa using h⟩
      · exact Set.mem_iUnion.mpr ⟨2, by simpa using h⟩
    · intro h
      rcases Set.mem_iUnion.mp h with ⟨i, hi⟩
      fin_cases i
      · exact Or.inl (Or.inl (by simpa using hi))
      · exact Or.inl (Or.inr (by simpa using hi))
      · exact Or.inr (by simpa using hi)

/-! ## The target: `SphereCoverAt` at every level -/

/-- **`SphereCoverAt` at EVERY level, with no exceptional set.**  With a genuinely thin slab
(`0 < h`), a unit tilt `v` with `ℓ v = 0` and `ℓ ≠ 0`, the corner direction condition
`ℓ (crossDir v (σ i)) ≠ 0` for `i ≠ 2`, `Work.Drive.Mono.EdgeFree` and the belt condition
`SlabInBelt`, the frontier of the level's removed set is a finite union of embedded spheres, any two
of which meet at most off the surface (`Work.Drive.Final.SphereCoverAt`) — at **every** level, with no
exceptional set.  This is the `SphereCoverAt` clause of `Work.Drive.Final.GoodSweepData3`
(project lead, `Submission/Work/Drive/Mono/NOTES_LEAD_geom3Producers.md` §0.4 and §5): `EdgeFree`
keeps the two pieces of the level frontier apart at the box-edge vertices where `tls_rest_crux` and
`tls_window_oneSphere` meet, and moving along `±crossDir v (σ i)` replaces the withdrawn `hseam`
condition.  It also settles the pullback disjointness consumed by the (L) route at the event level. -/
theorem sphereCoverAt_of_edgeFree {ψ : Submission.Diffeo} {s u h : ℝ}
    {c : LeanEval.KnotTheory.PardonDistortion.R3}
    {v : LeanEval.KnotTheory.PardonDistortion.R3} {σ : Equiv.Perm (Fin 3)}
    {ℓ : LeanEval.KnotTheory.PardonDistortion.R3 →L[ℝ] ℝ}
    (hs : 0 < s) (hh : 0 < h) (hv : ‖v‖ = 1) (hℓv : ℓ v = 0) (hℓne : ℓ ≠ 0)
    (hcross : ∀ i : Fin 3, i ≠ 2 → ℓ (Work.Drive.Final.crossDir v (σ i)) ≠ 0)
    (hEF : Work.Drive.Mono.EdgeFree ψ s c σ u v h)
    (hbelt : ∀ z, z ∈ (Work.Drive.EpsSphere.torusOf ψ).carrier →
      z ∈ closure (Submission.PBox s c σ) →
      |Work.Drive.Final.slabFn c u v z| ≤ h →
      |z (σ 2) - c (σ 2)| < Submission.boxSide 2 * s)
    (lam : ℝ) : Work.Drive.Final.SphereCoverAt ψ s c σ u v h ℓ lam := by
  have hv0 : v ≠ 0 := by
    intro hzero
    rw [hzero, norm_zero] at hv
    exact absurd hv.symm (by norm_num)
  have hXA : frontier (tlsUpCap s c σ u h v) = ∅ ∨
      Work.InnermostDisk.IsEmbeddedSphere (frontier (tlsUpCap s c σ u h v)) := by
    by_cases hne : (tlsUpCap s c σ u h v).Nonempty
    · exact Or.inr (frontier_tlsUpCap_sphere hs hv0 hne)
    · exact Or.inl (by rw [Set.not_nonempty_iff_eq_empty.mp hne, frontier_empty])
  have hYA : frontier (tlsDnCap s c σ u h v) = ∅ ∨
      Work.InnermostDisk.IsEmbeddedSphere (frontier (tlsDnCap s c σ u h v)) := by
    by_cases hne : (tlsDnCap s c σ u h v).Nonempty
    · exact Or.inr (frontier_tlsDnCap_sphere hs hv0 hne)
    · exact Or.inl (by rw [Set.not_nonempty_iff_eq_empty.mp hne, frontier_empty])
  have hZA : frontier (tlsWallClosed s c σ ℓ lam) = ∅ ∨
      Work.InnermostDisk.IsEmbeddedSphere (frontier (tlsWallClosed s c σ ℓ lam)) := by
    by_cases hne : (tlsWallClosed s c σ ℓ lam).Nonempty
    · exact Or.inr (by
        rw [frontier_tlsWallClosed_eq hℓne]
        exact frontier_tlsWallOpen_sphere hs hℓne (tlsWallOpen_nonempty_of_closed hℓne hne))
    · exact Or.inl (by rw [Set.not_nonempty_iff_eq_empty.mp hne, frontier_empty])
  by_cases hwin : (tlsUpCap s c σ u h v ∩ tlsWallOpen s c σ ℓ lam).Nonempty ∧
      (tlsDnCap s c σ u h v ∩ tlsWallOpen s c σ ℓ lam).Nonempty
  · -- the one-sphere window: the frontier is a single embedded sphere
    obtain ⟨⟨y₁, hy₁X, hy₁W⟩, ⟨y₂, hy₂Y, hy₂W⟩⟩ := hwin
    have hwinP : ∃ y ∈ Submission.PBox s c σ, inner ℝ v c + u + h < inner ℝ v y :=
      ⟨y₁, hy₁X.1, hy₁X.2⟩
    have hwinM : ∃ y ∈ Submission.PBox s c σ, inner ℝ v y < inner ℝ v c + u - h :=
      ⟨y₂, hy₂Y.1, hy₂Y.2⟩
    have hwallP : ∃ y ∈ Submission.PBox s c σ,
        inner ℝ v c + u + h < inner ℝ v y ∧ lam < ℓ y := ⟨y₁, hy₁X.1, hy₁X.2, hy₁W.2⟩
    have hwallM : ∃ y ∈ Submission.PBox s c σ,
        inner ℝ v y < inner ℝ v c + u - h ∧ lam < ℓ y := ⟨y₂, hy₂Y.1, hy₂Y.2, hy₂W.2⟩
    have hsphere : Work.InnermostDisk.IsEmbeddedSphere
        (frontier (Work.Drive.Mono.tiltedLevelRemoved s c σ u v h ℓ lam)) :=
      Work.Drive.Mono.WindowCase.tls_of_planarDisc s hs c σ u h lam v ℓ hh hℓv hℓne hv0
        hwinP hwinM hwallP hwallM
        (Work.Drive.Mono.WindowCase.tls_planarDisc_of_window s hs c σ u h lam v ℓ hh hℓv hℓne hv0
          hwinP hwinM hwallP hwallM)
    exact ⟨1, fun _ => frontier (Work.Drive.Mono.tiltedLevelRemoved s c σ u v h ℓ lam),
      fun _ => hsphere, (fun i j hij => absurd (Subsingleton.elim i j) hij),
      (by rw [Set.iUnion_const])⟩
  · by_cases hZne : (tlsWallClosed s c σ ℓ lam).Nonempty
    · by_cases hXZ : (tlsUpCap s c σ u h v ∩ tlsWallOpen s c σ ℓ lam).Nonempty
      · -- `Y ∩ Zw = ∅`: the pieces are `∂Y` and `∂(X ∪ Z)`
        have hYZ : ¬ (tlsDnCap s c σ u h v ∩ tlsWallOpen s c σ ℓ lam).Nonempty :=
          fun hY => hwin ⟨hXZ, hY⟩
        have hsep : ∀ x : R3, x ∈ closure (tlsDnCap s c σ u h v) →
            x ∈ closure (tlsUpCap s c σ u h v ∪ tlsWallClosed s c σ ℓ lam) →
            x ∉ tlsDnCap s c σ u h v ∪
              (tlsUpCap s c σ u h v ∪ tlsWallClosed s c σ ℓ lam) := by
          intro x hxY hxB hxU
          have hxZ : x ∈ closure (tlsWallClosed s c σ ℓ lam) := by
            rw [closure_union] at hxB
            rcases hxB with h | h
            · exact absurd hxY ((Set.disjoint_left.mp (closure_tlsUpCap_disjoint_tlsDnCap hh)) h)
            · exact h
          have hxR : x ∈ Work.Drive.Mono.tiltedLevelRemoved s c σ u v h ℓ lam := by
            rw [tiltedLevelRemoved_eq_three]
            rcases hxU with h | h
            · exact Or.inl (Or.inr h)
            · rcases h with h | h
              · exact Or.inl (Or.inl h)
              · exact Or.inr h
          exact not_mem_removed_of_mem_closure_dnCap_wallClosed hs hh hv0 hℓv hℓne hYZ hxY hxZ hxR
        have h1 : Work.Drive.Mono.tiltedLevelRemoved s c σ u v h ℓ lam =
            tlsDnCap s c σ u h v ∪ (tlsUpCap s c σ u h v ∪ tlsWallClosed s c σ ℓ lam) := by
          rw [tiltedLevelRemoved_eq_three]
          ext x; simp only [Set.mem_union]; tauto
        have hfr : frontier (Work.Drive.Mono.tiltedLevelRemoved s c σ u v h ℓ lam) =
            frontier (tlsDnCap s c σ u h v) ∪
              frontier (tlsUpCap s c σ u h v ∪ tlsWallClosed s c σ ℓ lam) := by
          rw [h1, frontier_union_of_no_inter hsep]
        have hBsphere : Work.InnermostDisk.IsEmbeddedSphere
            (frontier (tlsUpCap s c σ u h v ∪ tlsWallClosed s c σ ℓ lam)) :=
          frontier_union_upCap_wallClosed_sphere hs hv0 hℓne hℓv hXZ
        have hdisj : Disjoint
            (frontier (tlsDnCap s c σ u h v) ∩ (Work.Drive.EpsSphere.torusOf ψ).carrier)
            (frontier (tlsUpCap s c σ u h v ∪ tlsWallClosed s c σ ℓ lam) ∩
              (Work.Drive.EpsSphere.torusOf ψ).carrier) := by
          rw [Set.disjoint_left]
          intro q hqA hqB
          have hqY : q ∈ closure (tlsDnCap s c σ u h v) := frontier_subset_closure hqA.1
          have hqB' : q ∈ closure (tlsUpCap s c σ u h v) ∪ closure (tlsWallClosed s c σ ℓ lam) := by
            have h := frontier_subset_closure hqB.1
            rwa [closure_union] at h
          have hqZ : q ∈ closure (tlsWallClosed s c σ ℓ lam) := by
            rcases hqB' with h | h
            · exact absurd hqY ((Set.disjoint_left.mp (closure_tlsUpCap_disjoint_tlsDnCap hh)) h)
            · exact h
          exact inter_closure_dnCap_wallClosed_off_carrier hs hh hv0 hℓv hℓne hcross hEF hbelt hZne
            hYZ hqY hqZ
            (not_mem_removed_of_mem_closure_dnCap_wallClosed hs hh hv0 hℓv hℓne hYZ hqY hqZ) hqB.2
        obtain ⟨n, S, hS, hd, hu⟩ := sphere_decomposition_of_two_carrier
          ((Work.Drive.EpsSphere.torusOf ψ).carrier)
          (frontier (tlsDnCap s c σ u h v))
          (frontier (tlsUpCap s c σ u h v ∪ tlsWallClosed s c σ ℓ lam))
          hYA (Or.inr hBsphere) hdisj
        exact ⟨n, S, hS, hd, by rw [hfr, hu]⟩
      · by_cases hYZ : (tlsDnCap s c σ u h v ∩ tlsWallOpen s c σ ℓ lam).Nonempty
        · -- `X ∩ Zw = ∅`: the pieces are `∂X` and `∂(Y ∪ Z)`
          have hsep : ∀ x : R3, x ∈ closure (tlsUpCap s c σ u h v) →
              x ∈ closure (tlsDnCap s c σ u h v ∪ tlsWallClosed s c σ ℓ lam) →
              x ∉ tlsUpCap s c σ u h v ∪
                (tlsDnCap s c σ u h v ∪ tlsWallClosed s c σ ℓ lam) := by
            intro x hxX hxB hxU
            have hxZ : x ∈ closure (tlsWallClosed s c σ ℓ lam) := by
              rw [closure_union] at hxB
              rcases hxB with h | h
              · exact absurd h ((Set.disjoint_left.mp (closure_tlsUpCap_disjoint_tlsDnCap hh)) hxX)
              · exact h
            have hxR : x ∈ Work.Drive.Mono.tiltedLevelRemoved s c σ u v h ℓ lam := by
              rw [tiltedLevelRemoved_eq_three]
              rcases hxU with h | h
              · exact Or.inl (Or.inl h)
              · rcases h with h | h
                · exact Or.inl (Or.inr h)
                · exact Or.inr h
            exact not_mem_removed_of_mem_closure_upCap_wallClosed hs hh hv0 hℓv hℓne hXZ hxX hxZ hxR
          have h1 : Work.Drive.Mono.tiltedLevelRemoved s c σ u v h ℓ lam =
              tlsUpCap s c σ u h v ∪ (tlsDnCap s c σ u h v ∪ tlsWallClosed s c σ ℓ lam) := by
            rw [tiltedLevelRemoved_eq_three]
            ext x; simp only [Set.mem_union]; tauto
          have hfr : frontier (Work.Drive.Mono.tiltedLevelRemoved s c σ u v h ℓ lam) =
              frontier (tlsUpCap s c σ u h v) ∪
                frontier (tlsDnCap s c σ u h v ∪ tlsWallClosed s c σ ℓ lam) := by
            rw [h1, frontier_union_of_no_inter hsep]
          have hCsphere : Work.InnermostDisk.IsEmbeddedSphere
              (frontier (tlsDnCap s c σ u h v ∪ tlsWallClosed s c σ ℓ lam)) :=
            frontier_union_dnCap_wallClosed_sphere hs hv0 hℓne hℓv hYZ
          have hdisj : Disjoint
              (frontier (tlsUpCap s c σ u h v) ∩ (Work.Drive.EpsSphere.torusOf ψ).carrier)
              (frontier (tlsDnCap s c σ u h v ∪ tlsWallClosed s c σ ℓ lam) ∩
                (Work.Drive.EpsSphere.torusOf ψ).carrier) := by
            rw [Set.disjoint_left]
            intro q hqA hqB
            have hqX : q ∈ closure (tlsUpCap s c σ u h v) := frontier_subset_closure hqA.1
            have hqB' : q ∈ closure (tlsDnCap s c σ u h v) ∪ closure (tlsWallClosed s c σ ℓ lam) := by
              have h := frontier_subset_closure hqB.1
              rwa [closure_union] at h
            have hqZ : q ∈ closure (tlsWallClosed s c σ ℓ lam) := by
              rcases hqB' with h | h
              · exact absurd h ((Set.disjoint_left.mp (closure_tlsUpCap_disjoint_tlsDnCap hh)) hqX)
              · exact h
            exact inter_closure_upCap_wallClosed_off_carrier hs hh hv0 hℓv hℓne hcross hEF hbelt
              hZne hXZ hqX hqZ
              (not_mem_removed_of_mem_closure_upCap_wallClosed hs hh hv0 hℓv hℓne hXZ hqX hqZ) hqB.2
          obtain ⟨n, S, hS, hd, hu⟩ := sphere_decomposition_of_two_carrier
            ((Work.Drive.EpsSphere.torusOf ψ).carrier)
            (frontier (tlsUpCap s c σ u h v))
            (frontier (tlsDnCap s c σ u h v ∪ tlsWallClosed s c σ ℓ lam))
            hXA (Or.inr hCsphere) hdisj
          exact ⟨n, S, hS, hd, by rw [hfr, hu]⟩
        · -- both caps miss the wall region above the slab: the three pieces
          have hsep : ∀ x : R3, x ∈ closure (tlsUpCap s c σ u h v) →
              x ∈ closure (tlsDnCap s c σ u h v ∪ tlsWallClosed s c σ ℓ lam) →
              x ∉ tlsUpCap s c σ u h v ∪
                (tlsDnCap s c σ u h v ∪ tlsWallClosed s c σ ℓ lam) := by
            intro x hxX hxB hxU
            have hxZ : x ∈ closure (tlsWallClosed s c σ ℓ lam) := by
              rw [closure_union] at hxB
              rcases hxB with h | h
              · exact absurd h ((Set.disjoint_left.mp (closure_tlsUpCap_disjoint_tlsDnCap hh)) hxX)
              · exact h
            have hxR : x ∈ Work.Drive.Mono.tiltedLevelRemoved s c σ u v h ℓ lam := by
              rw [tiltedLevelRemoved_eq_three]
              rcases hxU with h | h
              · exact Or.inl (Or.inl h)
              · rcases h with h | h
                · exact Or.inl (Or.inr h)
                · exact Or.inr h
            exact not_mem_removed_of_mem_closure_upCap_wallClosed hs hh hv0 hℓv hℓne hXZ hxX hxZ hxR
          have h1 : Work.Drive.Mono.tiltedLevelRemoved s c σ u v h ℓ lam =
              tlsUpCap s c σ u h v ∪ (tlsDnCap s c σ u h v ∪ tlsWallClosed s c σ ℓ lam) := by
            rw [tiltedLevelRemoved_eq_three]
            ext x; simp only [Set.mem_union]; tauto
          have hfr1 : frontier (Work.Drive.Mono.tiltedLevelRemoved s c σ u v h ℓ lam) =
              frontier (tlsUpCap s c σ u h v) ∪
                frontier (tlsDnCap s c σ u h v ∪ tlsWallClosed s c σ ℓ lam) := by
            rw [h1, frontier_union_of_no_inter hsep]
          have hfr2 : frontier (tlsDnCap s c σ u h v ∪ tlsWallClosed s c σ ℓ lam) =
              frontier (tlsDnCap s c σ u h v) ∪ frontier (tlsWallClosed s c σ ℓ lam) := by
            apply frontier_union_of_no_inter
            intro x hxY hxZ hxU
            exact not_mem_removed_of_mem_closure_dnCap_wallClosed hs hh hv0 hℓv hℓne hYZ hxY hxZ
              (by
                rw [tiltedLevelRemoved_eq_three]
                rcases hxU with h | h
                · exact Or.inl (Or.inr h)
                · exact Or.inr h)
          have hfr : frontier (Work.Drive.Mono.tiltedLevelRemoved s c σ u v h ℓ lam) =
              frontier (tlsUpCap s c σ u h v) ∪ frontier (tlsDnCap s c σ u h v) ∪
                frontier (tlsWallClosed s c σ ℓ lam) := by
            rw [hfr1, hfr2, Set.union_assoc]
          have hdXY : Disjoint
              (frontier (tlsUpCap s c σ u h v) ∩ (Work.Drive.EpsSphere.torusOf ψ).carrier)
              (frontier (tlsDnCap s c σ u h v) ∩ (Work.Drive.EpsSphere.torusOf ψ).carrier) := by
            rw [Set.disjoint_left]
            intro q hqX hqY
            exact (Set.disjoint_left.mp (closure_tlsUpCap_disjoint_tlsDnCap hh))
              (frontier_subset_closure hqX.1) (frontier_subset_closure hqY.1)
          have hdXZ : Disjoint
              (frontier (tlsUpCap s c σ u h v) ∩ (Work.Drive.EpsSphere.torusOf ψ).carrier)
              (frontier (tlsWallClosed s c σ ℓ lam) ∩ (Work.Drive.EpsSphere.torusOf ψ).carrier) := by
            rw [Set.disjoint_left]
            intro q hqX hqZ
            exact inter_closure_upCap_wallClosed_off_carrier hs hh hv0 hℓv hℓne hcross hEF hbelt
              hZne hXZ (frontier_subset_closure hqX.1) (frontier_subset_closure hqZ.1)
              (not_mem_removed_of_mem_closure_upCap_wallClosed hs hh hv0 hℓv hℓne hXZ
                (frontier_subset_closure hqX.1) (frontier_subset_closure hqZ.1)) hqX.2
          have hdYZ : Disjoint
              (frontier (tlsDnCap s c σ u h v) ∩ (Work.Drive.EpsSphere.torusOf ψ).carrier)
              (frontier (tlsWallClosed s c σ ℓ lam) ∩ (Work.Drive.EpsSphere.torusOf ψ).carrier) := by
            rw [Set.disjoint_left]
            intro q hqY hqZ
            exact inter_closure_dnCap_wallClosed_off_carrier hs hh hv0 hℓv hℓne hcross hEF hbelt
              hZne hYZ (frontier_subset_closure hqY.1) (frontier_subset_closure hqZ.1)
              (not_mem_removed_of_mem_closure_dnCap_wallClosed hs hh hv0 hℓv hℓne hYZ
                (frontier_subset_closure hqY.1) (frontier_subset_closure hqZ.1)) hqY.2
          obtain ⟨n, S, hS, hd, hu⟩ := sphere_decomposition_of_three_carrier
            ((Work.Drive.EpsSphere.torusOf ψ).carrier)
            (frontier (tlsUpCap s c σ u h v)) (frontier (tlsDnCap s c σ u h v))
            (frontier (tlsWallClosed s c σ ℓ lam)) hXA hYA hZA hdXY hdXZ hdYZ
          exact ⟨n, S, hS, hd, by rw [hfr, hu]⟩
    · -- `Z = ∅`: the two caps
      have hZ0 : tlsWallClosed s c σ ℓ lam = ∅ := Set.not_nonempty_iff_eq_empty.mp hZne
      have h1 : Work.Drive.Mono.tiltedLevelRemoved s c σ u v h ℓ lam =
          tlsUpCap s c σ u h v ∪ tlsDnCap s c σ u h v := by
        rw [tiltedLevelRemoved_eq_three, hZ0, Set.union_empty]
      have hfr : frontier (Work.Drive.Mono.tiltedLevelRemoved s c σ u v h ℓ lam) =
          frontier (tlsUpCap s c σ u h v) ∪ frontier (tlsDnCap s c σ u h v) := by
        rw [h1, frontier_union_of_disjoint_closure (closure_tlsUpCap_disjoint_tlsDnCap hh)]
      have hdisj : Disjoint
          (frontier (tlsUpCap s c σ u h v) ∩ (Work.Drive.EpsSphere.torusOf ψ).carrier)
          (frontier (tlsDnCap s c σ u h v) ∩ (Work.Drive.EpsSphere.torusOf ψ).carrier) := by
        rw [Set.disjoint_left]
        intro q hqX hqY
        exact (Set.disjoint_left.mp (closure_tlsUpCap_disjoint_tlsDnCap hh))
          (frontier_subset_closure hqX.1) (frontier_subset_closure hqY.1)
      obtain ⟨n, S, hS, hd, hu⟩ := sphere_decomposition_of_two_carrier
        ((Work.Drive.EpsSphere.torusOf ψ).carrier)
        (frontier (tlsUpCap s c σ u h v)) (frontier (tlsDnCap s c σ u h v)) hXA hYA hdisj
      exact ⟨n, S, hS, hd, by rw [hfr, hu]⟩

end

end Work.Drive.Final
