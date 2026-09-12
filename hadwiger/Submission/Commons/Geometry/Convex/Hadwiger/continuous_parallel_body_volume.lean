import Mathlib.Algebra.Order.Archimedean.Real.Hom
import Mathlib.Analysis.Convex.Body
import Mathlib.Analysis.Normed.Affine.AddTorsorBases
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.SimpleRing.Principal

open Metric Filter MeasureTheory
open MeasureTheory.Measure
open scoped InnerProductSpace RealInnerProductSpace
open scoped Pointwise

namespace Commons.Geometry.Convex.Hadwiger

lemma interior_mem_of_hausdorffDist_lt
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
    {K L : Set V} (hLconv : Convex ℝ L)
    (hLclosed : IsClosed L) (hLne : L.Nonempty)
    {p : V} {r : ℝ} (hr : 0 < r) (hp : Metric.ball p r ⊆ K)
    (hfin : Metric.hausdorffEDist K L ≠ ⊤)
    (hdist : Metric.hausdorffDist K L < r / 2) : p ∈ L := by
  by_contra hpL
  obtain ⟨q, hqL, hqmin⟩ :=
    exists_norm_eq_iInf_of_complete_convex hLne hLclosed.isComplete hLconv p
  let d : ℝ := ‖p - q‖
  have hpq_ne : p - q ≠ 0 := by
    intro h
    have : p = q := sub_eq_zero.mp h
    exact hpL (this ▸ hqL)
  have hd_pos : 0 < d := norm_pos_iff.mpr hpq_ne
  let u : V := d⁻¹ • (p - q)
  have hu_norm : ‖u‖ = 1 := by
    dsimp [u, d]
    rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.2 (norm_nonneg _)), inv_mul_cancel₀ (ne_of_gt hd_pos)]
  have hchar : ∀ y ∈ L, ⟪p - q, y - q⟫ ≤ 0 :=
    (norm_eq_iInf_iff_real_inner_le_zero hLconv hqL).1 hqmin
  have hinner_ge : ∀ y ∈ L, d ≤ ⟪u, p - y⟫ := by
    intro y hyL
    have hle : ⟪p - q, y - q⟫ ≤ 0 := hchar y hyL
    have h1 : ⟪u, p - y⟫ = d⁻¹ * ⟪p - q, p - y⟫ := by
      simp [u, real_inner_smul_left]
    have h2 : ⟪p - q, p - y⟫ = d * d + ⟪p - q, q - y⟫ := by
      have hpq : p - y = (p - q) + (q - y) := by abel
      rw [hpq, inner_add_right]
      have hself : ⟪p - q, p - q⟫ = d * d := by
        dsimp [d]
        rw [real_inner_self_eq_norm_mul_norm]
      rw [hself]
    have h3 : 0 ≤ ⟪p - q, q - y⟫ := by
      have : ⟪p - q, q - y⟫ = - ⟪p - q, y - q⟫ := by simp [inner_sub_right]
      rw [this]
      linarith
    rw [h1, h2]
    calc
      d⁻¹ * (d * d + ⟪p - q, q - y⟫) ≥ d⁻¹ * (d * d) := by
        exact mul_le_mul_of_nonneg_left (le_add_of_nonneg_right h3) (inv_nonneg.2 (le_of_lt hd_pos))
      _ = d := by
        field_simp [ne_of_gt hd_pos]
  let z : V := p + (r / 2) • u
  have hz_ball : z ∈ Metric.ball p r := by
    have hhalf : 0 < r / 2 := half_pos hr
    have hnorm : ‖(r / 2) • u‖ < r := by
      rw [norm_smul, Real.norm_of_nonneg (le_of_lt hhalf), hu_norm, mul_one]
      exact half_lt_self hr
    simpa [z, dist_eq_norm, sub_eq_add_neg, add_assoc] using hnorm
  have hzK : z ∈ K := hp hz_ball
  obtain ⟨y, hyL, hzy⟩ := Metric.exists_dist_lt_of_hausdorffDist_lt hzK hdist hfin
  have hzy_lt : dist z y < r / 2 := hzy
  have hinner_lt : ⟪u, z - y⟫ < r / 2 := by
    calc
      ⟪u, z - y⟫ ≤ ‖u‖ * ‖z - y‖ := real_inner_le_norm u (z - y)
      _ = dist z y := by simp [hu_norm, dist_eq_norm]
      _ < r / 2 := hzy_lt
  have hinner_le : ⟪u, z - y⟫ ≤ r / 2 := le_of_lt hinner_lt
  have hinner_ge_z : r / 2 ≤ ⟪u, z - y⟫ := by
    have hge := hinner_ge y hyL
    have hz : ⟪u, z - p⟫ = r / 2 := by
      simp [z, real_inner_smul_right, hu_norm]
    have hzy_eq : z - y = (p - y) + (z - p) := by abel
    calc
      r / 2 ≤ d + r / 2 := by linarith
      _ ≤ ⟪u, p - y⟫ + r / 2 := by gcongr
      _ = ⟪u, p - y⟫ + ⟪u, z - p⟫ := by rw [hz]
      _ = ⟪u, (p - y) + (z - p)⟫ := by rw [inner_add_right]
      _ = ⟪u, z - y⟫ := by rw [hzy_eq]
  linarith

lemma ball_subset_of_mem_homothety_image
    {V : Type*} [SeminormedAddCommGroup V] [NormedSpace ℝ V]
    {K : Set V} (hK : Convex ℝ K) {p : V} {r0 : ℝ} (hr0 : 0 < r0)
    (hp : Metric.ball p r0 ⊆ K) {a : ℝ} (ha0 : 0 ≤ a) (ha1 : a ≤ 1)
    {x : V} (hx : x ∈ (fun z => p + a • (z - p)) '' K) :
    Metric.ball x ((1 - a) * r0) ⊆ K := by
  rcases hx with ⟨y, hyK, rfl⟩
  intro z hz
  by_cases ha_eq : a = 1
  · have hball0 : (1 - a) * r0 = 0 := by simp [ha_eq]
    have hdist0 : dist z (p + a • (y - p)) < 0 := by simpa [hball0] using hz
    exfalso
    exact (not_lt_of_ge dist_nonneg) hdist0
  · have ha_lt : a < 1 := lt_of_le_of_ne ha1 ha_eq
    have h_one_minus_pos : 0 < 1 - a := sub_pos.mpr ha_lt
    let w : V := p + ((1 - a)⁻¹) • (z - (p + a • (y - p)))
    have hwp : w - p = ((1 - a)⁻¹) • (z - (p + a • (y - p))) := by
      simp [w]
    have hnorm : ‖((1 - a)⁻¹) • (z - (p + a • (y - p)))‖ < r0 := by
      rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.2 (le_of_lt h_one_minus_pos))]
      have hz' : ‖z - (p + a • (y - p))‖ < (1 - a) * r0 := by
        simpa [dist_eq_norm] using hz
      have hmul : (1 - a)⁻¹ * ‖z - (p + a • (y - p))‖ < (1 - a)⁻¹ * ((1 - a) * r0) :=
        mul_lt_mul_of_pos_left hz' (inv_pos.mpr h_one_minus_pos)
      calc
        (1 - a)⁻¹ * ‖z - (p + a • (y - p))‖ < (1 - a)⁻¹ * ((1 - a) * r0) := hmul
        _ = r0 := by field_simp [ne_of_gt h_one_minus_pos]
    have hw_ball : w ∈ Metric.ball p r0 := by
      rw [Metric.mem_ball, dist_eq_norm]
      simpa [hwp] using hnorm
    have hwK : w ∈ K := hp hw_ball
    have hz_eq : z = (1 - a) • w + a • y := by
      apply smul_right_injective V (ne_of_gt h_one_minus_pos)
      dsimp [w]
      simp only [smul_add, smul_smul]
      field_simp [ne_of_gt h_one_minus_pos]
      module
    rw [hz_eq]
    exact hK hwK hyK (sub_nonneg.mpr ha1) ha0 (by ring)

lemma exists_pos_lt_one_pow_gt {d : ℕ} {M ε : ℝ} (hM : 0 < M) (hε : 0 < ε) :
    ∃ a : ℝ, 0 < a ∧ a < 1 ∧ M - ε < a ^ d * M := by
  have hcont : ContinuousAt (fun a : ℝ => a ^ d) 1 := continuousAt_id.pow d
  have hεM : 0 < ε / M := div_pos hε hM
  rcases Metric.continuousAt_iff.mp hcont (ε / M) hεM with ⟨δ, hδ, hδ'⟩
  let a : ℝ := 1 - min (δ / 2) (1 / 2)
  have hmin_pos : 0 < min (δ / 2) (1 / 2) := lt_min (half_pos hδ) (by norm_num)
  have hmin_lt_one : min (δ / 2) (1 / 2) < 1 := lt_of_le_of_lt (min_le_right _ _) (by norm_num)
  have ha_pos : 0 < a := by dsimp [a]; linarith
  have ha_lt_one : a < 1 := by dsimp [a]; linarith
  have ha_dist : dist a 1 < δ := by
    dsimp [a, dist]
    rw [abs_of_nonpos]
    · have : min (δ / 2) (1 / 2) < δ := lt_of_le_of_lt (min_le_left _ _) (half_lt_self hδ)
      linarith
    · linarith
  have hpow_abs : |a ^ d - 1| < ε / M := by
    simpa [one_pow, dist_eq_norm, Real.norm_eq_abs] using hδ' ha_dist
  have hpow_gt : 1 - ε / M < a ^ d := by
    have := abs_lt.mp hpow_abs
    linarith
  have hmul : (1 - ε / M) * M < a ^ d * M :=
    mul_lt_mul_of_pos_right hpow_gt hM
  refine ⟨a, ha_pos, ha_lt_one, ?_⟩
  calc
    M - ε = (1 - ε / M) * M := by field_simp [ne_of_gt hM]
    _ < a ^ d * M := hmul

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [MeasurableSpace V] [BorelSpace V] [FiniteDimensional ℝ V] [ProperSpace V]

lemma exists_upper_delta (K : ConvexBody V) (μ : Measure V) [IsFiniteMeasureOnCompacts μ]
    {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, (μ (Metric.cthickening δ (K : Set V))).toReal < (μ (K : Set V)).toReal + ε := by
  have hK_fin : μ (K : Set V) ≠ ⊤ := (K.isCompact.measure_lt_top).ne
  let mK : ℝ := (μ (K : Set V)).toReal
  have htend : Tendsto (fun r : ℝ => (μ (Metric.cthickening r (K : Set V))).toReal)
      (nhds (0 : ℝ)) (nhds mK) := by
    have hmeas : Tendsto (fun r : ℝ => μ (Metric.cthickening r (K : Set V)))
        (nhds (0 : ℝ)) (nhds (μ (K : Set V))) :=
      tendsto_measure_cthickening_of_isCompact (μ := μ) (s := (K : Set V)) K.isCompact
    simpa [mK, Function.comp_def] using (ENNReal.tendsto_toReal hK_fin).comp hmeas
  have h_event : ∀ᶠ r in nhds (0 : ℝ),
      dist ((μ (Metric.cthickening r (K : Set V))).toReal) mK < ε :=
    (Metric.tendsto_nhds.mp htend) ε hε
  rcases (Metric.nhds_basis_ball (x := (0 : ℝ))).eventually_iff.mp h_event with
    ⟨δ0, hδ0_pos, hδ0⟩
  let δ : ℝ := δ0 / 2
  have hδ_pos : 0 < δ := half_pos hδ0_pos
  refine ⟨δ, hδ_pos, ?_⟩
  have hmem : δ ∈ Metric.ball (0 : ℝ) δ0 := by
    have hδ_lt : δ < δ0 := by dsimp [δ]; exact half_lt_self hδ0_pos
    rw [Metric.mem_ball, dist_comm]
    simpa [Real.norm_eq_abs, abs_of_pos hδ_pos] using hδ_lt
  have hlt_dist := hδ0 hmem
  have hlt_abs : |(μ (Metric.cthickening δ (K : Set V))).toReal - mK| < ε := by
    simpa [Real.dist_eq] using hlt_dist
  have hlt : (μ (Metric.cthickening δ (K : Set V))).toReal < mK + ε := by
    have := abs_lt.mp hlt_abs
    linarith
  exact hlt

lemma exists_lower_delta (K : ConvexBody V) (μ : Measure V) [μ.IsAddHaarMeasure]
    [IsFiniteMeasureOnCompacts μ]
    (hKpos : 0 < μ (K : Set V)) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ L : ConvexBody V, dist L K < δ →
      (μ (K : Set V)).toReal - ε < (μ (L : Set V)).toReal := by
  classical
  have hspan : affineSpan ℝ (K : Set V) = ⊤ := by
    by_contra hspan_ne
    have hzero : μ (K : Set V) = 0 := by
      exact measure_mono_null (subset_affineSpan ℝ (K : Set V))
        (Measure.addHaar_affineSubspace μ (affineSpan ℝ (K : Set V)) hspan_ne)
    exact (ne_of_gt hKpos) hzero
  have h_int : (interior (K : Set V)).Nonempty :=
    (K.convex.interior_nonempty_iff_affineSpan_eq_top).2 hspan
  rcases h_int with ⟨p, hp_int⟩
  rcases Metric.mem_nhds_iff.mp (isOpen_interior.mem_nhds hp_int) with ⟨r0, hr0, hp_ball_int⟩
  have hp_ball : Metric.ball p r0 ⊆ (K : Set V) := hp_ball_int.trans interior_subset
  let mK : ℝ := (μ (K : Set V)).toReal
  have hK_fin : μ (K : Set V) ≠ ⊤ := (K.isCompact.measure_lt_top).ne
  have hmK_pos : 0 < mK := by
    exact ENNReal.toReal_pos_iff.mpr ⟨hKpos, lt_top_iff_ne_top.mpr hK_fin⟩
  rcases exists_pos_lt_one_pow_gt (d := Module.finrank ℝ V) (M := mK) (ε := ε / 2) hmK_pos (half_pos hε) with ⟨a, ha_pos, ha_lt, ha_pow⟩
  let C : Set V := (fun z => p + a • (z - p)) '' (K : Set V)
  have hC_meas : μ C = ENNReal.ofReal (a ^ Module.finrank ℝ V) * μ (K : Set V) := by
    have h_image : C = AffineMap.homothety p a '' (K : Set V) := by
      ext z
      simp only [Set.mem_image, AffineMap.homothety_apply, C]
      constructor
      · rintro ⟨y, hy, rfl⟩
        refine ⟨y, hy, ?_⟩
        simp
        abel
      · rintro ⟨y, hy, hz⟩
        refine ⟨y, hy, ?_⟩
        rw [← hz]
        simp
        abel
    rw [h_image, Measure.addHaar_image_homothety]
    rw [abs_of_nonneg (pow_nonneg (le_of_lt ha_pos) _)]
  have hC_toReal : (μ C).toReal = a ^ Module.finrank ℝ V * mK := by
    rw [hC_meas]
    exact ENNReal.toReal_ofReal_mul (a ^ Module.finrank ℝ V) (μ (K : Set V)) (pow_nonneg (le_of_lt ha_pos) _)
  have hC_gt : mK - ε / 2 < (μ C).toReal := by
    rw [hC_toReal]
    exact ha_pow
  let radius : ℝ := (1 - a) * r0
  have hradius_pos : 0 < radius := mul_pos (sub_pos.mpr ha_lt) hr0
  let δ : ℝ := radius / 2
  have hδ_pos : 0 < δ := half_pos hradius_pos
  refine ⟨δ, hδ_pos, ?_⟩
  intro L hLK
  have hKL : Metric.hausdorffDist (K : Set V) L < δ := by
    rw [← Metric.hausdorffDist_comm]
    simpa [ConvexBody.hausdorffDist_coe] using hLK
  have hC_sub_L : C ⊆ (L : Set V) := by
    intro x hx
    have hball_x : Metric.ball x radius ⊆ (K : Set V) :=
      ball_subset_of_mem_homothety_image K.convex hr0 hp_ball (le_of_lt ha_pos) (le_of_lt ha_lt) hx
    have hfinKL : Metric.hausdorffEDist (K : Set V) L ≠ ⊤ :=
      ConvexBody.hausdorffEDist_ne_top (K := K) (L := L)
    exact interior_mem_of_hausdorffDist_lt (hLconv := L.convex) (hLclosed := L.isClosed)
      (hLne := L.nonempty) (hr := hradius_pos) (hp := hball_x) (hfin := hfinKL)
      (hdist := by simpa [δ] using hKL)
  have hC_le_L : μ C ≤ μ (L : Set V) := measure_mono hC_sub_L
  have h_toReal_C_le_L : (μ C).toReal ≤ (μ (L : Set V)).toReal :=
    ENNReal.toReal_mono (L.isCompact.measure_lt_top).ne hC_le_L
  have hL_gt : mK - ε < (μ (L : Set V)).toReal := by
    have : mK - ε / 2 < (μ (L : Set V)).toReal := lt_of_lt_of_le hC_gt h_toReal_C_le_L
    linarith
  exact hL_gt

lemma convexBody_subset_cthickening_of_dist_lt (K L : ConvexBody V) {δ : ℝ} (hLK : dist L K < δ) :
    (L : Set V) ⊆ Metric.cthickening δ (K : Set V) := by
  intro x hx
  have hfin : Metric.hausdorffEDist (L : Set V) K ≠ ⊤ :=
    ConvexBody.hausdorffEDist_ne_top (K := L) (L := K)
  have hdist : Metric.hausdorffDist (L : Set V) K < δ := by
    simpa [ConvexBody.hausdorffDist_coe] using hLK
  rcases Metric.exists_dist_lt_of_hausdorffDist_lt hx hdist hfin with ⟨y, hyK, hxy⟩
  exact Metric.thickening_subset_cthickening δ (K : Set V)
    (Metric.mem_thickening_iff.mpr ⟨y, hyK, hxy⟩)

lemma continuousAt_volume_convexBody_real
    (n : ℕ) (K : ConvexBody (EuclideanSpace ℝ (Fin n))) :
    ContinuousAt (fun C : ConvexBody (EuclideanSpace ℝ (Fin n)) =>
      (volume (C : Set (EuclideanSpace ℝ (Fin n)))).toReal) K := by
  classical
  let V := EuclideanSpace ℝ (Fin n)
  let f : ConvexBody V → ℝ := fun C => (volume (C : Set V)).toReal
  refine Metric.continuousAt_iff.mpr ?_
  intro ε hε
  let mK : ℝ := (volume (K : Set V)).toReal
  have hK_fin : volume (K : Set V) ≠ ⊤ := (K.isCompact.measure_lt_top).ne
  rcases exists_upper_delta (V := V) K (μ := volume) (ε := ε / 2) (half_pos hε) with ⟨δup, hδup_pos, hδup⟩
  by_cases hKpos : 0 < volume (K : Set V)
  · rcases exists_lower_delta (V := V) K (μ := volume) hKpos (ε := ε / 2) (half_pos hε) with ⟨δlow, hδlow_pos, hδlow⟩
    let δ : ℝ := min δup δlow
    have hδ_pos : 0 < δ := lt_min hδup_pos hδlow_pos
    refine ⟨δ, hδ_pos, ?_⟩
    intro L hLK
    have hLK_up : dist L K < δup := lt_of_lt_of_le hLK (min_le_left _ _)
    have hLK_low : dist L K < δlow := lt_of_lt_of_le hLK (min_le_right _ _)
    have h_subset : (L : Set V) ⊆ Metric.cthickening δup (K : Set V) :=
      convexBody_subset_cthickening_of_dist_lt K L hLK_up
    have hct_fin : volume (Metric.cthickening δup (K : Set V)) ≠ ⊤ :=
      (K.isCompact.cthickening.measure_lt_top).ne
    have hL_le_ct : (volume (L : Set V)).toReal ≤ (volume (Metric.cthickening δup (K : Set V))).toReal :=
      ENNReal.toReal_mono hct_fin (measure_mono h_subset)
    have hL_upper : f L < mK + ε / 2 := lt_of_le_of_lt hL_le_ct hδup
    have hL_lower : mK - ε / 2 < f L := by
      have h := hδlow L hLK_low
      simpa [f, mK] using h
    have h_abs : |f L - mK| < ε := by
      rw [abs_sub_lt_iff]
      constructor <;> linarith
    simpa [f, mK, Real.dist_eq] using h_abs
  · have hKzero : volume (K : Set V) = 0 := by
      exact le_zero_iff.mp (not_lt.mp hKpos)
    have hmK_zero : mK = 0 := by simp [mK, hKzero]
    refine ⟨δup, hδup_pos, ?_⟩
    intro L hLK
    have h_subset : (L : Set V) ⊆ Metric.cthickening δup (K : Set V) :=
      convexBody_subset_cthickening_of_dist_lt K L hLK
    have hct_fin : volume (Metric.cthickening δup (K : Set V)) ≠ ⊤ :=
      (K.isCompact.cthickening.measure_lt_top).ne
    have hL_le_ct : (volume (L : Set V)).toReal ≤ (volume (Metric.cthickening δup (K : Set V))).toReal :=
      ENNReal.toReal_mono hct_fin (measure_mono h_subset)
    have hL_upper : f L < ε := by
      have hlt := lt_of_le_of_lt hL_le_ct hδup
      have hlt' : (volume (L : Set V)).toReal < ε / 2 := by
        simpa [f, mK, hmK_zero] using hlt
      linarith
    have hL_nonneg : 0 ≤ f L := ENNReal.toReal_nonneg
    have h_abs : |f L - mK| < ε := by
      rw [abs_sub_lt_iff]
      constructor
      · linarith
      · linarith
    simpa [f, mK, hmK_zero, Real.dist_eq] using h_abs

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

lemma lipschitzWith_add_left (L : ConvexBody V) :
    LipschitzWith 1 (fun K : ConvexBody V => K + L) := by
  refine LipschitzWith.mk_one fun K₁ K₂ => ?_
  have h₁ : Metric.hausdorffDist ((K₁ + L : ConvexBody V) : Set V) ((K₂ + L : ConvexBody V) : Set V) ≤
      Metric.hausdorffDist (K₁ : Set V) K₂ := by
    rw [ConvexBody.coe_add, ConvexBody.coe_add]
    apply Metric.hausdorffDist_le_of_mem_dist Metric.hausdorffDist_nonneg
    · intro x hx
      rcases hx with ⟨a, haK, b, hbL, rfl⟩
      have hfin : Metric.hausdorffEDist (K₁ : Set V) K₂ ≠ ⊤ := by
        exact ConvexBody.hausdorffEDist_ne_top (K := K₁) (L := K₂)
      have hle := Metric.infDist_le_hausdorffDist_of_mem haK hfin
      rcases (K₂.isCompact.exists_infDist_eq_dist K₂.nonempty a) with ⟨a', ha'K, hdist⟩
      refine ⟨a' + b, ⟨a', ha'K, b, hbL, rfl⟩, ?_⟩
      have hdistle : dist a a' ≤ Metric.hausdorffDist (K₁ : Set V) K₂ := by
        rw [← hdist]; exact hle
      simpa [dist_eq_norm] using hdistle
    · intro x hx
      rcases hx with ⟨a, haK, b, hbL, rfl⟩
      have hfin : Metric.hausdorffEDist (K₂ : Set V) K₁ ≠ ⊤ := by
        exact ConvexBody.hausdorffEDist_ne_top (K := K₂) (L := K₁)
      have hle := Metric.infDist_le_hausdorffDist_of_mem haK hfin
      rcases (K₁.isCompact.exists_infDist_eq_dist K₁.nonempty a) with ⟨a', ha'K, hdist⟩
      refine ⟨a' + b, ⟨a', ha'K, b, hbL, rfl⟩, ?_⟩
      have hcomm : Metric.hausdorffDist (K₂ : Set V) K₁ = Metric.hausdorffDist (K₁ : Set V) K₂ := by
        exact Metric.hausdorffDist_comm
      have hdistle : dist a a' ≤ Metric.hausdorffDist (K₂ : Set V) K₁ := by
        rw [← hdist]; exact hle
      have hdistle' : dist a a' ≤ Metric.hausdorffDist (K₁ : Set V) K₂ := hdistle.trans_eq hcomm
      simpa [dist_eq_norm] using hdistle'
  rw [← ConvexBody.hausdorffDist_coe (K := K₁ + L) (L := K₂ + L),
    ← ConvexBody.hausdorffDist_coe (K := K₁) (L := K₂),
    ConvexBody.coe_add, ConvexBody.coe_add]
  exact h₁

lemma continuous_add_left (L : ConvexBody V) :
    Continuous (fun K : ConvexBody V => K + L) :=
  (lipschitzWith_add_left L).continuous

lemma continuous_volume_convexBody (n : ℕ) :
    Continuous (fun K : ConvexBody (EuclideanSpace ℝ (Fin n)) =>
      (volume (K : Set (EuclideanSpace ℝ (Fin n)))).toReal) := by
  refine continuous_iff_continuousAt.mpr (fun K => ?_)
  simpa using continuousAt_volume_convexBody_real n K

theorem continuous_parallel_body_volume (n : ℕ) (L : ConvexBody (EuclideanSpace ℝ (Fin n))) :
    Continuous (fun K : ConvexBody (EuclideanSpace ℝ (Fin n)) =>
      (volume ((K + L : ConvexBody (EuclideanSpace ℝ (Fin n))) : Set (EuclideanSpace ℝ (Fin n)))).toReal) := by
  have hvol := continuous_volume_convexBody n
  have hadd : Continuous (fun K : ConvexBody (EuclideanSpace ℝ (Fin n)) => K + L) :=
    continuous_add_left L
  simpa [Function.comp_def, ConvexBody.coe_add] using hvol.comp hadd

end Commons.Geometry.Convex.Hadwiger