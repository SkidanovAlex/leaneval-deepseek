import Submission.FUP.HSFup

open FractalUncertainty MeasureTheory FourierTransform Metric Filter Set Pointwise
open scoped ENNReal BigOperators Topology ContDiff

set_option autoImplicit false
variable {d : ℕ}
local notation "ℝᵈ" => EuclideanSpace ℝ (Fin d)

/-!
# Han–Schlag's §5, step 1: the sets `S_n`, `S_n^*`, the holes `U_{n+1}` and the cut-off `Ψ_n`

This module continues `Submission.FUP.HSFup` (the cut-off layer of Han–Schlag's induction on
scales) with the *sets* of the induction:

* `Sset L X n` — the union of the depth-`n` grid cells meeting `X` (Han–Schlag's `S_n`);
* `StarS L X n` — its `L^{-n}/10`-neighbourhood `S_n^*` (taken in the `ℓ^∞` metric, which only
  improves the constants);
* `halfCube L n k` — the concentric half-cube `Q^*` of a grid cell `Q`;
* `Ustar L X n` — the union of the half-cubes of those depth-`n` children of nonempty cells that
  miss `X` (Han–Schlag's `U_n`);
* `Psi Φ L T X n` — the cut-off `Ψ_n = φ_{n+T} * 1_{S_{n+1}^*}` of the induction.

The two estimates are, for `x ∈ S_{n+1}`,
`1 - ∫_{L^{T-1}/10 < ‖z‖} φ ≤ Ψ_n x`, and for `x ∈ U_{n+1}`,
`Ψ_n x ≤ ∫_{2 L^{T-1}/5 ≤ ‖z‖} φ` — the uniform gain of the induction.
-/

namespace Submission.FUP

/-- Han–Schlag's `S_n`: the union of the depth-`n` grid cells that meet `X`. -/
def Sset (L : ℕ) (X : Set ℝᵈ) (n : ℕ) : Set ℝᵈ :=
  {z : ℝᵈ | ∃ k : Fin d → ℕ, (X ∩ gridBox L n k).Nonempty ∧ z ∈ gridBox L n k}

lemma mem_Sset {L n : ℕ} {X : Set ℝᵈ} {z : ℝᵈ} :
    z ∈ Sset L X n ↔ ∃ k : Fin d → ℕ, (X ∩ gridBox L n k).Nonempty ∧ z ∈ gridBox L n k :=
  Iff.rfl

lemma Sset_mono {L n : ℕ} {X Y : Set ℝᵈ} (h : X ⊆ Y) : Sset L X n ⊆ Sset L Y n := by
  rintro z ⟨k, hk, hz⟩
  exact ⟨k, hk.mono (Set.inter_subset_inter_left _ h), hz⟩

lemma Sset_eq_iUnion (L : ℕ) (X : Set ℝᵈ) (n : ℕ) :
    Sset L X n = ⋃ k : Fin d → ℕ, ⋃ (_ : (X ∩ gridBox L n k).Nonempty), gridBox L n k := by
  ext z
  simp only [mem_Sset, Set.mem_iUnion, exists_prop]

lemma measurableSet_box (a b : Fin d → ℝ) : MeasurableSet (box a b) := by
  rw [box]
  exact (MeasurableSet.univ_pi fun i => measurableSet_Icc).preimage (WithLp.measurable_ofLp 2 (Fin d → ℝ))

lemma measurableSet_gridBox (L n : ℕ) (k : Fin d → ℕ) : MeasurableSet (gridBox L n k) :=
  measurableSet_box _ _

lemma measurableSet_Sset (L : ℕ) (X : Set ℝᵈ) (n : ℕ) : MeasurableSet (Sset L X n) := by
  rw [Sset_eq_iUnion]
  exact MeasurableSet.iUnion fun k => MeasurableSet.iUnion fun _ => measurableSet_gridBox L n k

/-- Every point of `X` is covered by `S_n` (for `X ⊆ [-1,1]^d`, the depth-`0` cell). -/
lemma subset_Sset {L n : ℕ} (hL : 0 < L) {X : Set ℝᵈ} (hX : X ⊆ cube (-1) 1) :
    X ⊆ Sset L X n := by
  intro x hx
  induction n with
  | zero =>
      refine ⟨fun _ => 0, ⟨x, hx, ?_⟩, ?_⟩ <;> · rw [gridBox_zero]; exact hX hx
  | succ n ih =>
      obtain ⟨k, hkne, hk⟩ := ih
      obtain ⟨j, hj⟩ := gridBox_cover_children hL k hk
      exact ⟨childIndex L k j, ⟨x, hx, hj⟩, hj⟩

/-- The `r`-fattened grid cell (in the `ℓ^∞` sense). -/
noncomputable def fattenBox (L n : ℕ) (k : Fin d → ℕ) (r : ℝ) : Set ℝᵈ :=
  box (fun i => -1 + 2 * (k i : ℝ) * hss L n - r)
      (fun i => -1 + 2 * ((k i : ℝ) + 1) * hss L n + r)

lemma measurableSet_fattenBox (L n : ℕ) (k : Fin d → ℕ) (r : ℝ) :
    MeasurableSet (fattenBox L n k r) := measurableSet_box _ _

lemma gridBox_subset_fattenBox {L n : ℕ} (k : Fin d → ℕ) {r : ℝ} (hr : 0 ≤ r) :
    gridBox L n k ⊆ fattenBox L n k r := by
  refine box_subset_box ?_ ?_ <;> intro i
  · show -1 + 2 * (k i : ℝ) * hss L n - r ≤ -1 + 2 * (k i : ℝ) * hss L n
    linarith
  · show -1 + 2 * ((k i : ℝ) + 1) * hss L n ≤ -1 + 2 * ((k i : ℝ) + 1) * hss L n + r
    linarith

/-- Han–Schlag's `S_n^* = S_n + [-L^{-n}/10, L^{-n}/10]^d`, i.e. the cells meeting `X` fattened
by `L^{-n}/10` in the `ℓ^∞` sense. -/
noncomputable def StarS (L : ℕ) (X : Set ℝᵈ) (n : ℕ) : Set ℝᵈ :=
  {y : ℝᵈ | ∃ k : Fin d → ℕ, (X ∩ gridBox L n k).Nonempty ∧ y ∈ fattenBox L n k (hss L n / 10)}

lemma mem_StarS {L n : ℕ} {X : Set ℝᵈ} {y : ℝᵈ} :
    y ∈ StarS L X n ↔ ∃ k : Fin d → ℕ, (X ∩ gridBox L n k).Nonempty ∧
      y ∈ fattenBox L n k (hss L n / 10) := Iff.rfl

lemma measurableSet_StarS (L : ℕ) (X : Set ℝᵈ) (n : ℕ) : MeasurableSet (StarS L X n) := by
  have h : StarS L X n = ⋃ k : Fin d → ℕ, ⋃ (_ : (X ∩ gridBox L n k).Nonempty),
      fattenBox L n k (hss L n / 10) := by
    ext y
    simp only [mem_StarS, Set.mem_iUnion, exists_prop]
  rw [h]
  exact MeasurableSet.iUnion fun k => MeasurableSet.iUnion fun _ => measurableSet_fattenBox _ _ _ _

lemma Sset_subset_StarS (L n : ℕ) (X : Set ℝᵈ) : Sset L X n ⊆ StarS L X n := by
  rintro z ⟨k, hk, hz⟩
  exact ⟨k, hk, gridBox_subset_fattenBox k (by have := hss_nonneg L n; linarith) hz⟩

/-- The concentric half-cube `Q^*` of a grid cell (same centre, half the side length). -/
noncomputable def halfCube (L n : ℕ) (k : Fin d → ℕ) : Set ℝᵈ :=
  box (fun i => -1 + 2 * (k i : ℝ) * hss L n + hss L n / 2)
      (fun i => -1 + 2 * ((k i : ℝ) + 1) * hss L n - hss L n / 2)

lemma halfCube_subset_gridBox (L n : ℕ) (k : Fin d → ℕ) :
    halfCube L n k ⊆ gridBox L n k := by
  refine box_subset_box ?_ ?_
  · intro i
    show -1 + 2 * (k i : ℝ) * hss L n ≤ -1 + 2 * (k i : ℝ) * hss L n + hss L n / 2
    have := hss_nonneg L n; linarith
  · intro i
    show -1 + 2 * ((k i : ℝ) + 1) * hss L n - hss L n / 2 ≤ -1 + 2 * ((k i : ℝ) + 1) * hss L n
    have := hss_nonneg L n; linarith

/-- A point of a half-cube of a cell `Q` has a coordinate at distance at least half the side
length from any point of any other cell at the same depth. -/
lemma exists_coord_hss_half_le_of_mem_halfCube_of_mem_gridBox {L n : ℕ} (hL : 0 < L)
    {k k' : Fin d → ℕ} (hne : k' ≠ k) {z s : ℝᵈ} (hz : z ∈ halfCube L n k)
    (hs : s ∈ gridBox L n k') :
    ∃ i : Fin d, hss L n / 2 ≤ |z i - s i| := by
  have hLn0 : (0:ℝ) < hss L n := hss_pos hL n
  obtain ⟨i, hi⟩ : ∃ i, k' i ≠ k i := by
    by_contra h
    push Not at h
    exact hne (funext h)
  refine ⟨i, ?_⟩
  rw [halfCube, mem_box] at hz
  rw [gridBox, mem_box] at hs
  rcases lt_or_gt_of_ne hi with hlt | hgt
  · have hki : (k' i : ℝ) + 1 ≤ (k i : ℝ) := by
      exact_mod_cast Nat.succ_le_of_lt hlt
    have hsle : s i ≤ -1 + 2 * (k i : ℝ) * hss L n := by
      have h := (hs i).2
      nlinarith [hLn0, hki, h]
    have hzge : -1 + 2 * (k i : ℝ) * hss L n + hss L n / 2 ≤ z i := (hz i).1
    rw [abs_of_nonneg (by linarith)]
    linarith
  · have hki : (k i : ℝ) + 1 ≤ (k' i : ℝ) := by
      exact_mod_cast Nat.succ_le_of_lt hgt
    have hsge : -1 + 2 * (k i : ℝ) * hss L n + 2 * hss L n ≤ s i := by
      have h := (hs i).1
      nlinarith [hLn0, hki, h]
    have hzle : z i ≤ -1 + 2 * ((k i : ℝ) + 1) * hss L n - hss L n / 2 := (hz i).2
    rw [abs_of_nonpos (by linarith)]
    linarith

/-- A point of a half-cube of a cell `Q` is at distance at least half the side length from any
point of any other cell at the same depth. -/
lemma hss_half_le_dist_of_mem_halfCube_of_mem_gridBox {L n : ℕ} (hL : 0 < L) {k k' : Fin d → ℕ}
    (hne : k' ≠ k) {z s : ℝᵈ} (hz : z ∈ halfCube L n k) (hs : s ∈ gridBox L n k') :
    hss L n / 2 ≤ dist z s := by
  obtain ⟨i, hi⟩ := exists_coord_hss_half_le_of_mem_halfCube_of_mem_gridBox hL hne hz hs
  rw [dist_eq_norm]
  calc hss L n / 2 ≤ |z i - s i| := hi
    _ = ‖(z - s) i‖ := by rw [Real.norm_eq_abs]; rfl
    _ ≤ ‖z - s‖ := PiLp.norm_apply_le _ i

/-- Han–Schlag's `U_{n+1}`: the union of the half-cubes of the depth-`(n+1)` cells that are
children of a cell meeting `X` and miss `X`. -/
noncomputable def Ustar (L : ℕ) (X : Set ℝᵈ) (n : ℕ) : Set ℝᵈ :=
  {z : ℝᵈ | ∃ k : Fin d → ℕ, (X ∩ gridBox L n k).Nonempty ∧
      ∃ j : Fin d → Fin L, X ∩ gridBox L (n+1) (childIndex L k j) = ∅ ∧
        z ∈ halfCube L (n+1) (childIndex L k j)}

lemma mem_Ustar {L n : ℕ} {X : Set ℝᵈ} {z : ℝᵈ} :
    z ∈ Ustar L X n ↔ ∃ k : Fin d → ℕ, (X ∩ gridBox L n k).Nonempty ∧
      ∃ j : Fin d → Fin L, X ∩ gridBox L (n+1) (childIndex L k j) = ∅ ∧
        z ∈ halfCube L (n+1) (childIndex L k j) := Iff.rfl

/-- A point of the hole-set `U_{n+1}` has a coordinate at distance at least half the side length
of the depth-`(n+1)` cells from every point of `S_{n+1}`. -/
lemma exists_coord_hss_half_le_of_mem_Ustar_mem_Sset {L n : ℕ} (hL : 0 < L) {X : Set ℝᵈ}
    {z s : ℝᵈ} (hz : z ∈ Ustar L X n) (hs : s ∈ Sset L X (n+1)) :
    ∃ i : Fin d, hss L (n+1) / 2 ≤ |z i - s i| := by
  obtain ⟨k, -, j, hj, hzc⟩ := hz
  obtain ⟨k', hk'ne, hs'⟩ := hs
  have hne : k' ≠ childIndex L k j := by
    intro h
    rw [h] at hk'ne
    obtain ⟨y, hy⟩ := hk'ne
    rw [hj] at hy
    exact hy
  exact exists_coord_hss_half_le_of_mem_halfCube_of_mem_gridBox hL hne hzc hs'

/-- A point of the hole-set `U_{n+1}` is at distance at least half the side length of the
depth-`(n+1)` cells from `S_{n+1}`. -/
lemma hss_half_le_dist_of_mem_Ustar_mem_Sset {L n : ℕ} (hL : 0 < L) {X : Set ℝᵈ} {z s : ℝᵈ}
    (hz : z ∈ Ustar L X n) (hs : s ∈ Sset L X (n+1)) :
    hss L (n+1) / 2 ≤ dist z s := by
  obtain ⟨i, hi⟩ := exists_coord_hss_half_le_of_mem_Ustar_mem_Sset hL hz hs
  rw [dist_eq_norm]
  calc hss L (n+1) / 2 ≤ |z i - s i| := hi
    _ = ‖(z - s) i‖ := by rw [Real.norm_eq_abs]; rfl
    _ ≤ ‖z - s‖ := PiLp.norm_apply_le _ i

/-- `(L:ℝ)^(n+T) * L^{-(n+1)} = (L:ℝ)^(T-1)`. -/
lemma pow_mul_hss {L : ℕ} (hL : 1 ≤ L) {n T : ℕ} (hT : 1 ≤ T) :
    (L : ℝ) ^ (n + T) * hss L (n+1) = (L : ℝ) ^ (T - 1) := by
  have hLr : (0:ℝ) < (L:ℝ) := by exact_mod_cast (lt_of_lt_of_le one_pos hL)
  have hpow : (L : ℝ) ^ (n + T) = (L : ℝ) ^ (n + 1) * (L : ℝ) ^ (T - 1) := by
    rw [← pow_add]
    congr 1
    omega
  rw [hss, hpow, mul_comm ((L:ℝ)^(n+1)) ((L:ℝ)^(T-1)), mul_assoc,
    mul_inv_cancel₀ (pow_ne_zero _ hLr.ne'), mul_one]


/-! ## The cut-off `Ψ_n` of the induction -/

/-- Han–Schlag's `Ψ_n = φ_{n+T} * 1_{S_{n+1}^*}`. -/
noncomputable def Psi (Φ : FupCutoff d) (L T : ℕ) (X : Set ℝᵈ) (n : ℕ) : ℝᵈ → ℝ :=
  fun x => ∫ z, scaleFun Φ.reFun ((L : ℝ) ^ (n + T)) z *
    (StarS L X (n+1)).indicator (fun _ => (1 : ℝ)) (x - z)

/-- The same cut-off with values in `ℂ` (the form in which it is a Fourier multiplier). -/
noncomputable def PsiC (Φ : FupCutoff d) (L T : ℕ) (X : Set ℝᵈ) (n : ℕ) : ℝᵈ → ℂ :=
  fun x => ∫ z, ((scaleFun Φ.reFun ((L : ℝ) ^ (n + T)) z : ℝ) : ℂ) *
    (StarS L X (n+1)).indicator (fun _ => (1 : ℂ)) (x - z)

lemma continuous_scaleFun {φ : ℝᵈ → ℝ} (hφ : Continuous φ) (c : ℝ) :
    Continuous (scaleFun φ c) :=
  continuous_const.mul (hφ.comp (continuous_const_smul c))

lemma indicator_one_mul {S : Set ℝᵈ} (f : ℝᵈ → ℝ) (z : ℝᵈ) :
    S.indicator (fun _ => (1 : ℝ)) z * f z = S.indicator f z := by
  classical
  by_cases hz : z ∈ S <;> simp [Set.indicator_of_mem, Set.indicator_of_notMem, hz]

lemma measurable_indicator_one (L n : ℕ) (X : Set ℝᵈ) (x : ℝᵈ) :
    Measurable (fun z : ℝᵈ => (StarS L X n).indicator (fun _ => (1 : ℝ)) (x - z)) :=
  (Measurable.indicator measurable_const (measurableSet_StarS L X n)).comp
    (measurable_const.sub measurable_id)

lemma norm_indicator_one_le (S : Set ℝᵈ) (y : ℝᵈ) :
    |S.indicator (fun _ => (1 : ℝ)) y| ≤ 1 := by
  classical
  rw [Set.indicator_apply]
  split_ifs <;> norm_num

lemma indicator_one_le_one (S : Set ℝᵈ) (y : ℝᵈ) :
    S.indicator (fun _ => (1 : ℝ)) y ≤ 1 := by
  classical
  rw [Set.indicator_apply]
  split_ifs <;> norm_num

lemma indicator_one_nonneg (S : Set ℝᵈ) (y : ℝᵈ) :
    0 ≤ S.indicator (fun _ => (1 : ℝ)) y := by
  classical
  rw [Set.indicator_apply]
  split_ifs <;> norm_num

/-- Integrability of `scaleFun φ c * 1_S`. -/
lemma integrable_scaleFun_indicator (Φ : FupCutoff d) {c : ℝ} (hc : 0 < c) {S : Set ℝᵈ}
    (hS : MeasurableSet S) :
    Integrable (fun z => scaleFun Φ.reFun c z * S.indicator (fun _ => (1 : ℝ)) z) := by
  refine Integrable.mono' (integrable_scaleFun Φ.integrable_reFun hc)
    ((continuous_scaleFun Φ.continuous_reFun c).measurable.aestronglyMeasurable.mul
      (Measurable.indicator measurable_const hS).aestronglyMeasurable) ?_
  refine Filter.Eventually.of_forall fun z => ?_
  have h2 : 0 ≤ scaleFun Φ.reFun c z := scaleFun_nonneg Φ.reFun_nonneg hc.le z
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg h2]
  calc scaleFun Φ.reFun c z * |S.indicator (fun _ => (1 : ℝ)) z|
      ≤ scaleFun Φ.reFun c z * 1 := mul_le_mul_of_nonneg_left (norm_indicator_one_le _ _) h2
    _ = scaleFun Φ.reFun c z := mul_one _

/-- The mass of the dilated cut-off in a measurable set, as the mass of `φ` in the dilated set. -/
lemma integral_scaleFun_indicator (Φ : FupCutoff d) {c : ℝ} (hc : 0 < c) {S : Set ℝᵈ}
    (hS : MeasurableSet S) :
    ∫ z, scaleFun Φ.reFun c z * S.indicator (fun _ => (1 : ℝ)) z = ∫ w in c • S, Φ.reFun w := by
  have h1 : ∀ z : ℝᵈ, scaleFun Φ.reFun c z * S.indicator (fun _ => (1 : ℝ)) z
      = S.indicator (scaleFun Φ.reFun c) z := by
    intro z
    rw [mul_comm, indicator_one_mul]
  simp only [h1]
  rw [integral_indicator hS]
  have hcv := Measure.setIntegral_comp_smul_of_pos (μ := (volume : Measure ℝᵈ)) Φ.reFun S hc
  rw [finrank_euclideanSpace, Fintype.card_fin] at hcv
  calc ∫ z in S, scaleFun Φ.reFun c z
      = ∫ z in S, c ^ d * Φ.reFun (c • z) := rfl
    _ = c ^ d * ∫ z in S, Φ.reFun (c • z) := by rw [integral_const_mul]
    _ = c ^ d * ((c ^ d)⁻¹ * ∫ w in c • S, Φ.reFun w) := by rw [hcv, smul_eq_mul]
    _ = ∫ w in c • S, Φ.reFun w := by
        rw [← mul_assoc, mul_inv_cancel₀ (pow_ne_zero d hc.ne'), one_mul]

/-- The integrand of `Ψ_n` is integrable. -/
lemma integrable_Psi_integrand {L : ℕ} (hL : 1 ≤ L) (Φ : FupCutoff d) (T n : ℕ) (X : Set ℝᵈ)
    (x : ℝᵈ) :
    Integrable (fun z => scaleFun Φ.reFun ((L : ℝ) ^ (n + T)) z *
      (StarS L X (n+1)).indicator (fun _ => (1 : ℝ)) (x - z)) := by
  have hLr : (0:ℝ) < (L:ℝ) := by exact_mod_cast (lt_of_lt_of_le one_pos hL)
  have hc : (0:ℝ) < (L : ℝ) ^ (n + T) := pow_pos hLr _
  refine Integrable.mono' (integrable_scaleFun Φ.integrable_reFun hc)
    ((continuous_scaleFun Φ.continuous_reFun _).measurable.aestronglyMeasurable.mul
      (measurable_indicator_one L (n+1) X x).aestronglyMeasurable) ?_
  refine Filter.Eventually.of_forall fun z => ?_
  have h2 : 0 ≤ scaleFun Φ.reFun ((L : ℝ) ^ (n + T)) z :=
    scaleFun_nonneg Φ.reFun_nonneg hc.le z
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg h2]
  calc scaleFun Φ.reFun ((L : ℝ) ^ (n + T)) z *
        |(StarS L X (n+1)).indicator (fun _ => (1 : ℝ)) (x - z)|
      ≤ scaleFun Φ.reFun ((L : ℝ) ^ (n + T)) z * 1 :=
        mul_le_mul_of_nonneg_left (norm_indicator_one_le _ _) h2
    _ = scaleFun Φ.reFun ((L : ℝ) ^ (n + T)) z := mul_one _

lemma Psi_nonneg {L : ℕ} (hL : 1 ≤ L) (Φ : FupCutoff d) (T n : ℕ) (X : Set ℝᵈ) :
    ∀ x, 0 ≤ Psi Φ L T X n x := by
  have hLr : (0:ℝ) < (L:ℝ) := by exact_mod_cast (lt_of_lt_of_le one_pos hL)
  intro x
  refine integral_nonneg_of_ae (Filter.Eventually.of_forall fun z => ?_)
  exact mul_nonneg (scaleFun_nonneg Φ.reFun_nonneg (pow_nonneg hLr.le _) z)
    (indicator_one_nonneg _ _)

lemma Psi_le_one {L : ℕ} (hL : 1 ≤ L) (Φ : FupCutoff d) (T n : ℕ) (X : Set ℝᵈ) :
    ∀ x, Psi Φ L T X n x ≤ 1 := by
  have hLr : (0:ℝ) < (L:ℝ) := by exact_mod_cast (lt_of_lt_of_le one_pos hL)
  have hc : (0:ℝ) < (L : ℝ) ^ (n + T) := pow_pos hLr _
  intro x
  have hmono : ∀ z : ℝᵈ, scaleFun Φ.reFun ((L : ℝ) ^ (n + T)) z *
        (StarS L X (n+1)).indicator (fun _ => (1 : ℝ)) (x - z)
      ≤ scaleFun Φ.reFun ((L : ℝ) ^ (n + T)) z := by
    intro z
    have h2 : 0 ≤ scaleFun Φ.reFun ((L : ℝ) ^ (n + T)) z :=
      scaleFun_nonneg Φ.reFun_nonneg hc.le z
    calc scaleFun Φ.reFun ((L : ℝ) ^ (n + T)) z *
          (StarS L X (n+1)).indicator (fun _ => (1 : ℝ)) (x - z)
        ≤ scaleFun Φ.reFun ((L : ℝ) ^ (n + T)) z * 1 :=
          mul_le_mul_of_nonneg_left (indicator_one_le_one _ _) h2
      _ = scaleFun Φ.reFun ((L : ℝ) ^ (n + T)) z := mul_one _
  calc Psi Φ L T X n x ≤ ∫ z, scaleFun Φ.reFun ((L : ℝ) ^ (n + T)) z :=
        integral_mono (integrable_Psi_integrand hL Φ T n X x)
          (integrable_scaleFun Φ.integrable_reFun hc) hmono
    _ = 1 := scaleFun_integral_eq_one Φ.integral_reFun hc

/-- **Lower bound on `Ψ_n` at points of `S_{n+1}`** (Han–Schlag (5-4)). -/
theorem Psi_lower_aux {L T n : ℕ} (hL : 1 ≤ L) (Φ : FupCutoff d) (X : Set ℝᵈ)
    {x : ℝᵈ} (hx : x ∈ Sset L X (n+1)) :
    1 - ∫ z in {z : ℝᵈ | (L : ℝ) ^ (n + T) * (hss L (n+1) / 10) ≤ ‖z‖}, Φ.reFun z
      ≤ Psi Φ L T X n x := by
  classical
  have hLr : (0:ℝ) < (L:ℝ) := by exact_mod_cast (lt_of_lt_of_le one_pos hL)
  have hc : (0:ℝ) < (L : ℝ) ^ (n + T) := pow_pos hLr _
  obtain ⟨k, hkne, hkx⟩ := hx
  have hball : ∀ z : ℝᵈ, ‖z‖ ≤ hss L (n+1) / 10 →
      (StarS L X (n+1)).indicator (fun _ => (1 : ℝ)) (x - z) = 1 := by
    intro z hz
    have hmem : x - z ∈ StarS L X (n+1) := by
      refine ⟨k, hkne, ?_⟩
      rw [fattenBox, mem_box]
      have hkx' := hkx
      rw [gridBox, mem_box] at hkx'
      intro i
      have hzi : |z i| ≤ hss L (n+1) / 10 := by
        have h := PiLp.norm_apply_le z i
        rw [Real.norm_eq_abs] at h
        exact le_trans h hz
      have hsub : (x - z) i = x i - z i := rfl
      constructor
      · rw [hsub]; linarith [abs_le.mp hzi, (hkx' i).1, (hkx' i).2]
      · rw [hsub]; linarith [abs_le.mp hzi, (hkx' i).1, (hkx' i).2]
    exact Set.indicator_of_mem (f := fun _ => (1 : ℝ)) hmem
  have hmono : ∀ z : ℝᵈ, scaleFun Φ.reFun ((L : ℝ) ^ (n + T)) z *
        (ball (0:ℝᵈ) (hss L (n+1) / 10)).indicator (fun _ => (1 : ℝ)) z
      ≤ scaleFun Φ.reFun ((L : ℝ) ^ (n + T)) z *
        (StarS L X (n+1)).indicator (fun _ => (1 : ℝ)) (x - z) := by
    intro z
    have h2 : 0 ≤ scaleFun Φ.reFun ((L : ℝ) ^ (n + T)) z :=
      scaleFun_nonneg Φ.reFun_nonneg hc.le z
    by_cases hz : z ∈ ball (0:ℝᵈ) (hss L (n+1) / 10)
    · have hbm : ‖z‖ ≤ hss L (n+1) / 10 :=
        le_of_lt (by simpa only [Metric.mem_ball, dist_zero_right] using hz)
      rw [Set.indicator_of_mem hz, hball z hbm]
    · have hz0 : (ball (0:ℝᵈ) (hss L (n+1) / 10)).indicator (fun _ => (1 : ℝ)) z = 0 :=
        Set.indicator_of_notMem (f := fun _ => (1 : ℝ)) hz
      rw [hz0, mul_zero]
      exact mul_nonneg h2 (indicator_one_nonneg _ _)
  have hstep : ∫ z, scaleFun Φ.reFun ((L : ℝ) ^ (n + T)) z *
        (ball (0:ℝᵈ) (hss L (n+1) / 10)).indicator (fun _ => (1 : ℝ)) z
      ≤ Psi Φ L T X n x :=
    integral_mono (integrable_scaleFun_indicator Φ hc measurableSet_ball)
      (integrable_Psi_integrand hL Φ T n X x) hmono
  have hchange := integral_scaleFun_indicator Φ hc
    (S := ball (0:ℝᵈ) (hss L (n+1) / 10)) measurableSet_ball
  have hset : (L : ℝ) ^ (n + T) • ball (0:ℝᵈ) (hss L (n+1) / 10)
      = {w : ℝᵈ | ‖w‖ < (L : ℝ) ^ (n + T) * (hss L (n+1) / 10)} := by
    ext w
    simp only [Set.mem_smul_set, Metric.mem_ball, dist_zero_right, Set.mem_setOf_eq]
    constructor
    · rintro ⟨z, hz, rfl⟩
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos hc]
      exact mul_lt_mul_of_pos_left hz hc
    · intro hw
      refine ⟨((L:ℝ)^(n+T))⁻¹ • w, ?_, by rw [smul_inv_smul₀ hc.ne']⟩
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hc), inv_mul_lt_iff₀ hc]
      exact hw
  rw [hset] at hchange
  have htail : ∫ w in {w : ℝᵈ | ‖w‖ < (L : ℝ) ^ (n + T) * (hss L (n+1) / 10)}, Φ.reFun w
      = 1 - ∫ z in {z : ℝᵈ | (L : ℝ) ^ (n + T) * (hss L (n+1) / 10) ≤ ‖z‖}, Φ.reFun z := by
    have hms : MeasurableSet {w : ℝᵈ | ‖w‖ < (L : ℝ) ^ (n + T) * (hss L (n+1) / 10)} :=
      measurableSet_lt measurable_norm measurable_const
    have hcompl : {w : ℝᵈ | ‖w‖ < (L : ℝ) ^ (n + T) * (hss L (n+1) / 10)}ᶜ
        = {z : ℝᵈ | (L : ℝ) ^ (n + T) * (hss L (n+1) / 10) ≤ ‖z‖} := by
      ext z
      simp only [Set.mem_compl_iff, Set.mem_setOf_eq, not_lt]
    have hadd := integral_add_compl hms Φ.integrable_reFun (μ := (volume : Measure ℝᵈ))
    rw [hcompl] at hadd
    linarith [hadd, Φ.integral_reFun]
  linarith [hstep, hchange, htail]

/-- **Lower bound on `Ψ_n` at points of `S_{n+1}`**, with the threshold `L^{T-1}/10`. -/
theorem Psi_lower {L T n : ℕ} (hL : 1 ≤ L) (hT : 1 ≤ T) (Φ : FupCutoff d) (X : Set ℝᵈ)
    {x : ℝᵈ} (hx : x ∈ Sset L X (n+1)) :
    1 - ∫ z in {z : ℝᵈ | (L : ℝ) ^ (T - 1) / 10 ≤ ‖z‖}, Φ.reFun z ≤ Psi Φ L T X n x := by
  have h := Psi_lower_aux (T := T) (n := n) hL Φ X hx
  rwa [show (L : ℝ) ^ (n + T) * (hss L (n+1) / 10) = (L : ℝ) ^ (T - 1) / 10 from by
    rw [← pow_mul_hss hL hT]; ring] at h

/-- **Upper bound on `Ψ_n` at points of the holes `U_{n+1}`** (Han–Schlag (5-5)). -/
theorem Psi_upper_aux {L T n : ℕ} (hL : 1 ≤ L) (Φ : FupCutoff d) {X : Set ℝᵈ}
    {x : ℝᵈ} (hx : x ∈ Ustar L X n) :
    Psi Φ L T X n x ≤
      ∫ w in {w : ℝᵈ | (L : ℝ) ^ (n + T) * (2 * hss L (n+1) / 5) ≤ ‖w‖}, Φ.reFun w := by
  classical
  have hLpos : 0 < L := lt_of_lt_of_le one_pos hL
  have hLr : (0:ℝ) < (L:ℝ) := by exact_mod_cast hLpos
  have hc : (0:ℝ) < (L : ℝ) ^ (n + T) := pow_pos hLr _
  have hLn0 : (0:ℝ) < hss L (n+1) := hss_pos hLpos (n+1)
  obtain ⟨k₀, -, j, hj, hxc⟩ := hx
  -- a point within `ℓ^∞`-distance `L^{-(n+1)}/10` of a cell meeting `X` is far from every hole
  have hfar : ∀ z : ℝᵈ, x - z ∈ StarS L X (n+1) → 2 * hss L (n+1) / 5 ≤ ‖z‖ := by
    intro z hz
    obtain ⟨k, hkne, hzk⟩ := hz
    rw [fattenBox, mem_box] at hzk
    set Q : Fin d → ℕ := childIndex L k₀ j
    have hQne : Q ≠ k := by
      intro h
      rw [h] at hj
      obtain ⟨y, hy⟩ := hkne
      rw [hj] at hy
      exact hy
    obtain ⟨i, hi⟩ : ∃ i, Q i ≠ k i := by
      by_contra h
      push Not at h
      exact hQne (funext h)
    rw [halfCube, mem_box] at hxc
    have hcoord : 2 * hss L (n+1) / 5 ≤ |z i| := by
      rcases lt_or_gt_of_ne hi with hlt | hgt
      · have hki : (Q i : ℝ) + 1 ≤ (k i : ℝ) := by
          exact_mod_cast Nat.succ_le_of_lt hlt
        have hlo : -1 + 2 * (k i : ℝ) * hss L (n+1) - hss L (n+1) / 10 ≤ (x - z) i := (hzk i).1
        have hxu : x i ≤ -1 + 2 * ((Q i : ℝ) + 1) * hss L (n+1) - hss L (n+1) / 2 := (hxc i).2
        have hzsub : z i = x i - (x - z) i := by rw [sub_apply']; ring
        have hzle : z i ≤ -(2 * hss L (n+1) / 5) := by
          rw [hzsub]; nlinarith [hLn0, hlo, hxu, hki]
        rw [abs_of_nonpos (by linarith), hzsub]
        linarith
      · have hki : (k i : ℝ) + 1 ≤ (Q i : ℝ) := by
          exact_mod_cast Nat.succ_le_of_lt hgt
        have hhi : (x - z) i ≤ -1 + 2 * (Q i : ℝ) * hss L (n+1) + hss L (n+1) / 10 := by
          have h := (hzk i).2
          nlinarith [hLn0, hki, h]
        have hxl : -1 + 2 * (Q i : ℝ) * hss L (n+1) + hss L (n+1) / 2 ≤ x i := (hxc i).1
        have hzsub : z i = x i - (x - z) i := by rw [sub_apply']; ring
        have hzge : 2 * hss L (n+1) / 5 ≤ z i := by
          rw [hzsub]; nlinarith [hhi, hxl]
        rw [abs_of_nonneg (by linarith), hzsub]
        linarith
    calc 2 * hss L (n+1) / 5 ≤ |z i| := hcoord
      _ = ‖z i‖ := by rw [Real.norm_eq_abs]
      _ ≤ ‖z‖ := PiLp.norm_apply_le z i
  have hmono : ∀ z : ℝᵈ, scaleFun Φ.reFun ((L : ℝ) ^ (n + T)) z *
        (StarS L X (n+1)).indicator (fun _ => (1 : ℝ)) (x - z)
      ≤ scaleFun Φ.reFun ((L : ℝ) ^ (n + T)) z *
        ({w : ℝᵈ | 2 * hss L (n+1) / 5 ≤ ‖w‖}).indicator (fun _ => (1 : ℝ)) z := by
    intro z
    have h2 : 0 ≤ scaleFun Φ.reFun ((L : ℝ) ^ (n + T)) z :=
      scaleFun_nonneg Φ.reFun_nonneg hc.le z
    by_cases hz : z ∈ ({w : ℝᵈ | 2 * hss L (n+1) / 5 ≤ ‖w‖} : Set ℝᵈ)
    · have hz1 : ({w : ℝᵈ | 2 * hss L (n+1) / 5 ≤ ‖w‖} : Set ℝᵈ).indicator
          (fun _ => (1 : ℝ)) z = 1 := Set.indicator_of_mem (f := fun _ => (1 : ℝ)) hz
      rw [hz1]
      exact mul_le_mul_of_nonneg_left (indicator_one_le_one _ _) h2
    · have hz0 : ({w : ℝᵈ | 2 * hss L (n+1) / 5 ≤ ‖w‖} : Set ℝᵈ).indicator
          (fun _ => (1 : ℝ)) z = 0 := Set.indicator_of_notMem (f := fun _ => (1 : ℝ)) hz
      have hzind : (StarS L X (n+1)).indicator (fun _ => (1 : ℝ)) (x - z) = 0 :=
        Set.indicator_of_notMem (f := fun _ => (1 : ℝ)) (fun hmem => hz (hfar z hmem))
      rw [hzind, hz0]
  have hstep : Psi Φ L T X n x ≤ ∫ z, scaleFun Φ.reFun ((L : ℝ) ^ (n + T)) z *
        ({w : ℝᵈ | 2 * hss L (n+1) / 5 ≤ ‖w‖}).indicator (fun _ => (1 : ℝ)) z :=
    integral_mono (integrable_Psi_integrand hL Φ T n X x)
      (integrable_scaleFun_indicator Φ hc (measurableSet_le measurable_const measurable_norm)) hmono
  have hchange := integral_scaleFun_indicator Φ hc
    (S := {w : ℝᵈ | 2 * hss L (n+1) / 5 ≤ ‖w‖}) (measurableSet_le measurable_const measurable_norm)
  have hset : (L : ℝ) ^ (n + T) • {w : ℝᵈ | 2 * hss L (n+1) / 5 ≤ ‖w‖}
      = {w : ℝᵈ | (L : ℝ) ^ (n + T) * (2 * hss L (n+1) / 5) ≤ ‖w‖} := by
    ext w
    simp only [Set.mem_smul_set, Set.mem_setOf_eq]
    constructor
    · rintro ⟨z, hz, rfl⟩
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos hc]
      exact mul_le_mul_of_nonneg_left hz hc.le
    · intro hw
      refine ⟨((L:ℝ)^(n+T))⁻¹ • w, ?_, by rw [smul_inv_smul₀ hc.ne']⟩
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hc)]
      have h2 : ((L:ℝ)^(n+T))⁻¹ * ((L:ℝ)^(n+T) * (2 * hss L (n+1) / 5))
          = 2 * hss L (n+1) / 5 := by
        rw [← mul_assoc, inv_mul_cancel₀ hc.ne', one_mul]
      calc 2 * hss L (n+1) / 5 = ((L:ℝ)^(n+T))⁻¹ * ((L:ℝ)^(n+T) * (2*hss L (n+1)/5)) := h2.symm
        _ ≤ ((L:ℝ)^(n+T))⁻¹ * ‖w‖ := mul_le_mul_of_nonneg_left hw (by positivity)
  rw [hset] at hchange
  linarith [hstep, hchange]

/-- **Upper bound on `Ψ_n` at points of the holes `U_{n+1}`**, with the threshold
`2 L^{T-1}/5`. -/
theorem Psi_upper {L T n : ℕ} (hL : 1 ≤ L) (hT : 1 ≤ T) (Φ : FupCutoff d) {X : Set ℝᵈ}
    {x : ℝᵈ} (hx : x ∈ Ustar L X n) :
    Psi Φ L T X n x ≤ ∫ w in {w : ℝᵈ | 2 * (L : ℝ) ^ (T - 1) / 5 ≤ ‖w‖}, Φ.reFun w := by
  have h := Psi_upper_aux (T := T) (n := n) hL Φ hx
  rwa [show (L : ℝ) ^ (n + T) * (2 * hss L (n+1) / 5) = 2 * (L : ℝ) ^ (T - 1) / 5 from by
    rw [← pow_mul_hss hL hT]; ring] at h

/-- **Off-support decay of `Ψ_n`.**  If every `z` with `x - z ∈ S_{n+1}^*` satisfies
`δ ≤ ‖z‖` (i.e. `x` is at `ℓ²`-distance at least `δ` from the fattened set `S_{n+1}^*`), then
`Ψ_n x` is bounded by the tail of `Φ.reFun` beyond `L^{n+T}δ`.

This is the quantitative form of Han–Schlag's `(5-5)` (of which `Psi_upper` is the special case
that the holes `U_{n+1}` are at distance `2·hss L (n+1)/5`); it is what makes the iterated
cut-offs `∏ Ψ_{nT}` small *away from* the cells meeting `X`, which is the missing ingredient in
`LocalizationStatement` (see `Submission/FUP/ROADMAP.md`, Session 51, §2). -/
theorem Psi_le_tail_of_far {L T n : ℕ} (hL : 1 ≤ L) (Φ : FupCutoff d) (X : Set ℝᵈ) {x : ℝᵈ}
    {δ : ℝ} (hδ : ∀ z : ℝᵈ, x - z ∈ StarS L X (n+1) → δ ≤ ‖z‖) :
    Psi Φ L T X n x ≤ ∫ w in {w : ℝᵈ | (L : ℝ) ^ (n + T) * δ ≤ ‖w‖}, Φ.reFun w := by
  classical
  have hLpos : 0 < L := lt_of_lt_of_le one_pos hL
  have hLr : (0:ℝ) < (L:ℝ) := by exact_mod_cast hLpos
  have hc : (0:ℝ) < (L : ℝ) ^ (n + T) := pow_pos hLr _
  have hmono : ∀ z : ℝᵈ, scaleFun Φ.reFun ((L : ℝ) ^ (n + T)) z *
        (StarS L X (n+1)).indicator (fun _ => (1 : ℝ)) (x - z)
      ≤ scaleFun Φ.reFun ((L : ℝ) ^ (n + T)) z *
        ({w : ℝᵈ | δ ≤ ‖w‖}).indicator (fun _ => (1 : ℝ)) z := by
    intro z
    have h2 : 0 ≤ scaleFun Φ.reFun ((L : ℝ) ^ (n + T)) z :=
      scaleFun_nonneg Φ.reFun_nonneg hc.le z
    by_cases hz : z ∈ ({w : ℝᵈ | δ ≤ ‖w‖} : Set ℝᵈ)
    · have hz1 : ({w : ℝᵈ | δ ≤ ‖w‖} : Set ℝᵈ).indicator (fun _ => (1 : ℝ)) z = 1 :=
        Set.indicator_of_mem (f := fun _ => (1 : ℝ)) hz
      rw [hz1]
      exact mul_le_mul_of_nonneg_left (indicator_one_le_one _ _) h2
    · have hz0 : ({w : ℝᵈ | δ ≤ ‖w‖} : Set ℝᵈ).indicator (fun _ => (1 : ℝ)) z = 0 :=
        Set.indicator_of_notMem (f := fun _ => (1 : ℝ)) hz
      have hzind : (StarS L X (n+1)).indicator (fun _ => (1 : ℝ)) (x - z) = 0 :=
        Set.indicator_of_notMem (f := fun _ => (1 : ℝ)) (fun hmem => hz (hδ z hmem))
      rw [hzind, hz0]
  have hstep : Psi Φ L T X n x ≤ ∫ z, scaleFun Φ.reFun ((L : ℝ) ^ (n + T)) z *
        ({w : ℝᵈ | δ ≤ ‖w‖}).indicator (fun _ => (1 : ℝ)) z :=
    integral_mono (integrable_Psi_integrand hL Φ T n X x)
      (integrable_scaleFun_indicator Φ hc (measurableSet_le measurable_const measurable_norm)) hmono
  have hchange := integral_scaleFun_indicator Φ hc
    (S := {w : ℝᵈ | δ ≤ ‖w‖}) (measurableSet_le measurable_const measurable_norm)
  have hset : (L : ℝ) ^ (n + T) • {w : ℝᵈ | δ ≤ ‖w‖}
      = {w : ℝᵈ | (L : ℝ) ^ (n + T) * δ ≤ ‖w‖} := by
    ext w
    simp only [Set.mem_smul_set, Set.mem_setOf_eq]
    constructor
    · rintro ⟨z, hz, rfl⟩
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos hc]
      exact mul_le_mul_of_nonneg_left hz hc.le
    · intro hw
      refine ⟨((L:ℝ)^(n+T))⁻¹ • w, ?_, by rw [smul_inv_smul₀ hc.ne']⟩
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hc)]
      have h2 : ((L:ℝ)^(n+T))⁻¹ * ((L:ℝ)^(n+T) * δ) = δ := by
        rw [← mul_assoc, inv_mul_cancel₀ hc.ne', one_mul]
      calc δ = ((L:ℝ)^(n+T))⁻¹ * ((L:ℝ)^(n+T) * δ) := h2.symm
        _ ≤ ((L:ℝ)^(n+T))⁻¹ * ‖w‖ := mul_le_mul_of_nonneg_left hw (by positivity)
  rw [hset] at hchange
  linarith [hstep, hchange]

/-- `S_n^*` is bounded (in the ball of radius `4`) as soon as `X ⊆ [-1,1]^d`. -/
lemma StarS_subset_cube {L n : ℕ} (hL : 1 ≤ L) {X : Set ℝᵈ} (hX : X ⊆ cube (-1) 1) :
    StarS L X n ⊆ cube (-4) 4 := by
  intro y hy
  obtain ⟨k, hkne, hyk⟩ := hy
  obtain ⟨x, hxX, hxk⟩ := hkne
  rw [fattenBox, mem_box] at hyk
  rw [gridBox, mem_box] at hxk
  have hXc := hX hxX
  rw [mem_cube] at hXc
  rw [mem_cube]
  intro i
  have hh : hss L n ≤ 1 := by
    rw [hss]
    exact inv_le_one_of_one_le₀ (one_le_pow₀ (by exact_mod_cast hL : (1:ℝ) ≤ (L:ℝ)))
  have hr : hss L n / 10 ≤ 1 := by linarith
  constructor <;> linarith [(hyk i).1, (hyk i).2, (hxk i).1, (hxk i).2, hXc i]

lemma volume_StarS_lt_top {L n : ℕ} (hL : 1 ≤ L) {X : Set ℝᵈ} (hX : X ⊆ cube (-1) 1) :
    volume (StarS L X n) < ⊤ := by
  refine lt_of_le_of_lt (measure_mono (StarS_subset_cube hL hX)) ?_
  rw [cube_eq_box, volume_box]
  exact ENNReal.prod_lt_top fun i _ => ENNReal.ofReal_lt_top

/-- Integrability of the complexified dilated cut-off. -/
lemma integrable_scaleFun_ofReal (Φ : FupCutoff d) {c : ℝ} (hc : 0 < c) :
    Integrable (fun x : ℝᵈ => (scaleFun Φ.reFun c x : ℂ)) := by
  refine Integrable.mono' (integrable_scaleFun Φ.integrable_reFun hc)
    (Complex.continuous_ofReal.comp (continuous_scaleFun Φ.continuous_reFun _)).aestronglyMeasurable ?_
  refine Filter.Eventually.of_forall fun x => ?_
  rw [Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (scaleFun_nonneg Φ.reFun_nonneg hc.le x)]

/-- Integrability of the indicator of `S_n^*`. -/
lemma integrable_indicator_one_complex {L : ℕ} (hL : 1 ≤ L) {X : Set ℝᵈ}
    (hX : X ⊆ cube (-1) 1) (n : ℕ) :
    Integrable ((StarS L X n).indicator (fun _ => (1 : ℂ))) :=
  (integrable_indicator_iff (measurableSet_StarS L X n)).mpr
    (integrableOn_const (by exact ne_of_lt (volume_StarS_lt_top hL hX)) (by simp))

/-- `Ψ_n` as a convolution. -/
lemma PsiC_eq_convolution (Φ : FupCutoff d) (L T : ℕ) (X : Set ℝᵈ) (n : ℕ) :
    PsiC Φ L T X n = convolution (fun x : ℝᵈ => (scaleFun Φ.reFun ((L : ℝ) ^ (n + T)) x : ℂ))
      ((StarS L X (n+1)).indicator (fun _ => (1 : ℂ)))
      (ContinuousLinearMap.mul ℂ ℂ) volume := by
  funext x
  rw [convolution_def]
  rfl

/-- `Ψ_n` is integrable (it is the convolution of an `L¹` and an `L¹` function). -/
lemma integrable_PsiC {L : ℕ} (hL : 1 ≤ L) (Φ : FupCutoff d) (T n : ℕ) {X : Set ℝᵈ}
    (hX : X ⊆ cube (-1) 1) : Integrable (PsiC Φ L T X n) := by
  have hLr : (0:ℝ) < (L:ℝ) := by exact_mod_cast (lt_of_lt_of_le one_pos hL)
  have hc : (0:ℝ) < (L : ℝ) ^ (n + T) := pow_pos hLr _
  rw [PsiC_eq_convolution]
  exact Integrable.integrable_convolution (ContinuousLinearMap.mul ℂ ℂ)
    (integrable_scaleFun_ofReal Φ hc) (integrable_indicator_one_complex (L := L) (X := X) hL hX (n+1))

/-- **The Fourier support of `Ψ_n`**: it is contained in the ball of radius
`L^{n+T} · radius(φ)`. -/
theorem fourier_PsiC_eq_zero {L : ℕ} (hL : 1 ≤ L) (Φ : FupCutoff d) (T n : ℕ) {X : Set ℝᵈ}
    (hX : X ⊆ cube (-1) 1) {ξ : ℝᵈ} (hξ : (L : ℝ) ^ (n + T) * Φ.radius < ‖ξ‖) :
    FourierTransform.fourier (fun x => PsiC Φ L T X n x) ξ = 0 := by
  have hLr : (0:ℝ) < (L:ℝ) := by exact_mod_cast (lt_of_lt_of_le one_pos hL)
  have hc : (0:ℝ) < (L : ℝ) ^ (n + T) := pow_pos hLr _
  have hmeas : MeasurableSet (StarS L X (n+1)) := measurableSet_StarS L X (n+1)
  have hint1 := integrable_scaleFun_ofReal Φ hc
  have hint2 := integrable_indicator_one_complex (L := L) (X := X) hL hX (n := n+1)
  have hconv := Real.fourier_mul_convolution_eq
    (f₁ := fun x : ℝᵈ => (scaleFun Φ.reFun ((L : ℝ) ^ (n + T)) x : ℂ))
    (f₂ := (StarS L X (n+1)).indicator (fun _ => (1 : ℂ))) (R := ℂ) hint1 hint2 ξ
  rw [show (fun x => PsiC Φ L T X n x) = PsiC Φ L T X n from rfl, PsiC_eq_convolution, hconv,
    Φ.dilate_fourier_eq_zero hc hξ, zero_mul]

lemma PsiC_eq_ofReal {L : ℕ} (hL : 1 ≤ L) (Φ : FupCutoff d) (T n : ℕ) (X : Set ℝᵈ) :
    ∀ x, PsiC Φ L T X n x = ((Psi Φ L T X n x : ℝ) : ℂ) := by
  have hLr : (0:ℝ) < (L:ℝ) := by exact_mod_cast (lt_of_lt_of_le one_pos hL)
  have hc : (0:ℝ) < (L : ℝ) ^ (n + T) := pow_pos hLr _
  intro x
  have h1 : ∀ z : ℝᵈ, ((scaleFun Φ.reFun ((L:ℝ)^(n+T)) z *
        (StarS L X (n+1)).indicator (fun _ => (1 : ℝ)) (x - z) : ℝ) : ℂ)
      = ((scaleFun Φ.reFun ((L:ℝ)^(n+T)) z : ℝ) : ℂ) *
        (StarS L X (n+1)).indicator (fun _ => (1 : ℂ)) (x - z) := by
    intro z
    rw [Complex.ofReal_mul]
    congr 1
    by_cases hz : x - z ∈ StarS L X (n+1) <;>
      simp [Set.indicator_of_mem, Set.indicator_of_notMem, hz]
  have hPsi : Psi Φ L T X n x = ∫ z, scaleFun Φ.reFun ((L:ℝ)^(n+T)) z *
      (StarS L X (n+1)).indicator (fun _ => (1 : ℝ)) (x - z) := rfl
  rw [hPsi]
  trans ∫ z, ((scaleFun Φ.reFun ((L:ℝ)^(n+T)) z *
      (StarS L X (n+1)).indicator (fun _ => (1 : ℝ)) (x - z) : ℝ) : ℂ)
  · exact integral_congr_ae (Filter.Eventually.of_forall fun z => (h1 z).symm)
  · exact integral_ofReal

/-- **The Fourier support of `Ψ_n`** (real cut-off form). -/
lemma fourier_Psi_eq_zero {L : ℕ} (hL : 1 ≤ L) (Φ : FupCutoff d) (T n : ℕ) {X : Set ℝᵈ}
    (hX : X ⊆ cube (-1) 1) {ξ : ℝᵈ} (hξ : (L : ℝ) ^ (n + T) * Φ.radius < ‖ξ‖) :
    FourierTransform.fourier (fun x => (Psi Φ L T X n x : ℂ)) ξ = 0 := by
  have hfun : (fun x : ℝᵈ => (Psi Φ L T X n x : ℂ)) = fun x : ℝᵈ => PsiC Φ L T X n x := by
    funext x
    exact (PsiC_eq_ofReal hL Φ T n X x).symm
  rw [← fourier_PsiC_eq_zero hL Φ T n hX hξ, hfun]

lemma scaleFun_scaleFun {φ : ℝᵈ → ℝ} (c c' : ℝ) :
    scaleFun (scaleFun φ c) c' = scaleFun φ (c * c') := by
  funext x
  simp only [scaleFun, smul_smul]
  rw [mul_pow]
  ring

/-- **The cut-off can be normalised so that its Fourier transform has radius at most `1`**
(Han–Schlag's `supp φ̂ ⊆ [-1,1]^d`, which is exactly what makes the growth of the Fourier support
in the induction on scales compatible with the `[-4,4]^d` of the damping hypothesis). -/
theorem exists_fupCutoff_radius_le_one (d : ℕ) : ∃ Φ : FupCutoff d, Φ.radius ≤ 1 := by
  obtain ⟨Φ₀⟩ := hasFupCutoff d
  set c : ℝ := min 1 Φ₀.radius⁻¹
  have hcpos : 0 < c := lt_min one_pos (inv_pos.mpr Φ₀.radius_pos)
  have hcle : c * Φ₀.radius ≤ 1 := by
    have h1 : c ≤ Φ₀.radius⁻¹ := min_le_right _ _
    calc c * Φ₀.radius ≤ Φ₀.radius⁻¹ * Φ₀.radius :=
          mul_le_mul_of_nonneg_right h1 Φ₀.radius_pos.le
      _ = 1 := inv_mul_cancel₀ Φ₀.radius_pos.ne'
  refine ⟨{ fn := scaleFun Φ₀.fn c,
            continuous := continuous_scaleFun Φ₀.continuous c,
            integrable := integrable_scaleFun Φ₀.integrable hcpos,
            nonneg := scaleFun_nonneg Φ₀.nonneg hcpos.le,
            integral_one := by rw [integral_scaleFun hcpos, Φ₀.integral_one],
            radius := c * Φ₀.radius,
            radius_pos := mul_pos hcpos Φ₀.radius_pos,
            support := fun c' hc' ξ hξ => by
              rw [scaleFun_scaleFun]
              have h : c' * (c * Φ₀.radius) = (c * c') * Φ₀.radius := by ring
              rw [h] at hξ
              exact Φ₀.support (c * c') (mul_pos hcpos hc') ξ hξ }, hcle⟩

end Submission.FUP
