import Mathlib.MeasureTheory.Group.LIntegral
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseBoxFock.LatFourierDefs
import Submission.Work.BoseFixR.farLatFoldCell
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.lintegral_tsum_translate_boxL_le`

The basic lattice-periodisation bound for the corpus box `Λ(a) = a • [-1/2,1/2]³`:
for `l > 0`, `k : ℕ` and any measurable `g : ℝ³ → ℝ≥0∞`,

    ∫⁻ z, 1_{Λ(k l)}(z) · (Σ_m g (z + l • m)) ≤ (k+1)³ · ∫⁻ z, g z .

## Route

Write `Λ = boxL` and `H z = Σ'_m g (z + l • latVec m)` (the `lℤ³`-periodisation of `g`).

* the box `Λ(k l)` is covered by the `(k+1)³` lattice translates `Λ(l) + l • c`
  (`c` running over the integer box `∏_i [-k/2, k/2]`): coordinatewise, an interval of length
  `k l` centred at the origin is covered by the `k+1` intervals of length `l` centred at the
  lattice points, because `⌊k/2⌋ + 1/2 ≥ k/2`;
* hence the integrand at a point of `Λ(k l)` is dominated by `(Σ_c 1_{Λ(l) + l•c}) · H`;
* each term `∫⁻ z, 1_{Λ(l) + l•c}(z) · H z` equals `∫⁻ z, 1_{Λ(l)}(z) · H z`: `H` is invariant
  under translation by lattice vectors, so translating the integrand back by `l • c` (translation
  invariance of Lebesgue measure) and using `z + l•c ∈ Λ(l) + l•c ↔ z ∈ Λ(l)` identifies them;
* finally `∫⁻ z, 1_{Λ(l)}(z) · H z = ∫⁻ z, g z`, which is the tiling/periodisation identity
  `Work.BoseFixR.FarFold.tileLatticeLintegralAdd` together with Tonelli for `∑'`
  (`MeasureTheory.lintegral_tsum`) and `ENNReal.tsum_mul_left`.

Everything is `ℝ≥0∞`-valued, so no integrability hypotheses are needed.
-/

noncomputable section

open scoped BigOperators Pointwise

open MeasureTheory

namespace Work.BoseBoxFock

local notation "E3" => EuclideanSpace ℝ (Fin 3)

set_option maxHeartbeats 800000

/-! ## 0. Measurability of the closed cubes -/

lemma measurableSet_cell_bfr (a : ℝ) : MeasurableSet (Work.BoseFixR.cell a) := by
  rw [Work.BoseFixR.cell_eq_boxL]
  exact Work.BoseFixR.measurableSet_boxL a

lemma measurableSet_cell_add_singleton (l : ℝ) (a : E3) :
    MeasurableSet (Work.BoseFixR.cell l + ({a} : Set E3)) := by
  rw [Set.add_singleton, Set.image_add_right]
  exact MeasurableSet.preimage (measurableSet_cell_bfr l)
    ((continuous_id.add continuous_const).measurable)

/-! ## 1. The corpus box is the closed cube (also for the degenerate side `0`) -/

lemma corpusBox_boxL_eq_cell_of_nonneg {a : ℝ} (ha : 0 ≤ a) :
    Work.BoseK15.corpusBox.boxL a = Work.BoseFixR.cell a := by
  ext x
  rw [Work.BoseFixR.mem_cell]
  constructor
  · intro hx i
    rw [Work.BoseB4.BoxData.boxL, Set.mem_smul_set] at hx
    obtain ⟨y, hy, hyx⟩ := hx
    have hyi : |y i| ≤ 1 / 2 := by simpa [Work.BoseB4.unitCell] using hy i
    have hxeq : x i = a * y i := by
      rw [← hyx]
      simp [PiLp.smul_apply]
    rw [hxeq, abs_mul, abs_of_nonneg ha]
    calc a * |y i| ≤ a * (1 / 2) := mul_le_mul_of_nonneg_left hyi ha
      _ = a / 2 := by ring
  · intro hx
    rw [Work.BoseB4.BoxData.boxL, Set.mem_smul_set]
    rcases eq_or_lt_of_le ha with h0 | hpos
    · rw [← h0] at hx ⊢
      have hx0 : x = 0 := by
        ext i
        have hi : |x i| ≤ 0 := by simpa using hx i
        exact abs_eq_zero.mp (le_antisymm hi (abs_nonneg _))
      refine ⟨0, ?_, ?_⟩
      · change (0 : E3) ∈ Work.BoseB4.unitCell
        simp [Work.BoseB4.unitCell]
      · rw [hx0]
        simp
    · refine ⟨a⁻¹ • x, ?_, ?_⟩
      · change ∀ i, |(a⁻¹ • x) i| ≤ 1 / 2
        intro i
        have h1 : (a⁻¹ • x) i = a⁻¹ * x i := by simp [PiLp.smul_apply]
        rw [h1, abs_mul, abs_of_pos (inv_pos.mpr hpos)]
        have h2 : a⁻¹ * |x i| ≤ a⁻¹ * (a / 2) :=
          mul_le_mul_of_nonneg_left (hx i) (le_of_lt (inv_pos.mpr hpos))
        have h3 : a⁻¹ * (a / 2) = 1 / 2 := by field_simp
        linarith
      · show a • (a⁻¹ • x) = x
        exact smul_inv_smul₀ (ne_of_gt hpos) x

/-! ## 2. The lattice tiling identity for the closed cube -/

lemma farLat_lat_eq (l : ℝ) (n : Fin 3 → ℤ) : Work.BoseFixR.lat l n = l • latVec n := by
  ext i
  simp [Work.BoseFixR.lat, latVec, PiLp.smul_apply]

/-- The lattice tiling identity `∫⁻ g = Σ_m ∫⁻_{Λ(l)} g(· + l•m)` for the closed cube
`Λ(l) = Work.BoseFixR.cell l`. -/
lemma lintegral_tiling_cell {l : ℝ} (hl : 0 < l) (g : E3 → ENNReal) :
    ∫⁻ u, g u = ∑' n : Fin 3 → ℤ, ∫⁻ x in Work.BoseFixR.cell l, g (x + l • latVec n) := by
  rw [Work.BoseFixR.FarFold.tileLatticeLintegralAdd hl g]
  exact tsum_congr fun n => by rw [farLat_lat_eq]

/-! ## 3. The one-dimensional integer-window lemma -/

/-- **The integer window.**  For `|ξ| ≤ k/2` there is an integer `n` with `|n| ≤ ⌊k/2⌋` and
`|ξ - n| ≤ 1/2`. -/
lemma exists_int_close_half (k : ℕ) {ξ : ℝ} (hξ : |ξ| ≤ (k : ℝ) / 2) :
    ∃ n : ℤ, -(((k / 2 : ℕ) : ℤ)) ≤ n ∧ n ≤ (((k / 2 : ℕ) : ℤ)) ∧
      |ξ - (n : ℝ)| ≤ 1 / 2 := by
  obtain ⟨s, hs | hs⟩ := Nat.even_or_odd' k
  · -- `k = 2 * s`
    rw [hs] at hξ ⊢
    have hT : (2 * s) / 2 = s := Nat.mul_div_cancel_left s (by norm_num : 0 < 2)
    rw [hT]
    have hξ' : |ξ| ≤ (s : ℝ) := by
      push_cast at hξ
      linarith
    refine ⟨⌊ξ + 1 / 2⌋, ?_, ?_, ?_⟩
    · by_contra hcon
      push_neg at hcon
      have hle : (⌊ξ + 1 / 2⌋ : ℤ) ≤ -(s : ℤ) - 1 := by omega
      have hle' : ((⌊ξ + 1 / 2⌋ : ℤ) : ℝ) ≤ -(s : ℝ) - 1 := by exact_mod_cast hle
      have h1 : ξ - 1 / 2 < ((⌊ξ + 1 / 2⌋ : ℤ) : ℝ) := by
        have h := Int.lt_floor_add_one (ξ + 1 / 2)
        linarith
      have h2 : -(s : ℝ) ≤ ξ := (abs_le.mp hξ').1
      linarith
    · by_contra hcon
      push_neg at hcon
      have hle : (s : ℤ) + 1 ≤ ⌊ξ + 1 / 2⌋ := by omega
      have hle' : (s : ℝ) + 1 ≤ ((⌊ξ + 1 / 2⌋ : ℤ) : ℝ) := by exact_mod_cast hle
      have h3 : ((⌊ξ + 1 / 2⌋ : ℤ) : ℝ) ≤ ξ + 1 / 2 := Int.floor_le _
      have h4 : ξ ≤ (s : ℝ) := (abs_le.mp hξ').2
      linarith
    · rw [abs_le]
      constructor
      · have h3 : ((⌊ξ + 1 / 2⌋ : ℤ) : ℝ) ≤ ξ + 1 / 2 := Int.floor_le _
        linarith
      · have h1 : ξ - 1 / 2 < ((⌊ξ + 1 / 2⌋ : ℤ) : ℝ) := by
          have h := Int.lt_floor_add_one (ξ + 1 / 2)
          linarith
        linarith
  · -- `k = 2 * s + 1`
    rw [hs] at hξ ⊢
    have hT : (2 * s + 1) / 2 = s := by
      have h1 : 2 * s + 1 = 1 + 2 * s := by omega
      have h2 : (1 + 2 * s) / 2 = 1 / 2 + s := Nat.add_mul_div_left 1 s (by norm_num : 0 < 2)
      have h3 : (1 : ℕ) / 2 = 0 := Nat.div_eq_of_lt (by norm_num : 1 < 2)
      rw [h1, h2, h3, Nat.zero_add]
    rw [hT]
    have hξ' : |ξ| ≤ (s : ℝ) + 1 / 2 := by
      push_cast at hξ
      linarith
    refine ⟨min (s : ℤ) ⌊ξ + 1 / 2⌋, ?_, ?_, ?_⟩
    · refine le_min (by omega) ?_
      by_contra hcon
      push_neg at hcon
      have hle : (⌊ξ + 1 / 2⌋ : ℤ) ≤ -(s : ℤ) - 1 := by omega
      have hle' : ((⌊ξ + 1 / 2⌋ : ℤ) : ℝ) ≤ -(s : ℝ) - 1 := by exact_mod_cast hle
      have h1 : ξ - 1 / 2 < ((⌊ξ + 1 / 2⌋ : ℤ) : ℝ) := by
        have h := Int.lt_floor_add_one (ξ + 1 / 2)
        linarith
      have h2 : -(s : ℝ) - 1 / 2 ≤ ξ := by linarith [(abs_le.mp hξ').1]
      linarith
    · exact min_le_left _ _
    · rcases le_or_gt ⌊ξ + 1 / 2⌋ (s : ℤ) with hm | hm
      · rw [min_eq_right hm]
        rw [abs_le]
        constructor
        · have h3 : ((⌊ξ + 1 / 2⌋ : ℤ) : ℝ) ≤ ξ + 1 / 2 := Int.floor_le _
          linarith
        · have h1 : ξ - 1 / 2 < ((⌊ξ + 1 / 2⌋ : ℤ) : ℝ) := by
            have h := Int.lt_floor_add_one (ξ + 1 / 2)
            linarith
          linarith
      · rw [min_eq_left hm.le]
        have h1 : (s : ℝ) + 1 / 2 ≤ ξ := by
          have h2 : (s : ℤ) + 1 ≤ ⌊ξ + 1 / 2⌋ := by omega
          have h3 : (s : ℝ) + 1 ≤ ((⌊ξ + 1 / 2⌋ : ℤ) : ℝ) := by exact_mod_cast h2
          have h4 : ((⌊ξ + 1 / 2⌋ : ℤ) : ℝ) ≤ ξ + 1 / 2 := Int.floor_le _
          linarith
        rw [abs_le]
        push_cast
        constructor <;> linarith [(abs_le.mp hξ').2, h1]

/-- **The one-dimensional cover.**  For `|t| ≤ k l / 2` there is an integer `n` with
`|n| ≤ ⌊k/2⌋` and `|t - l n| ≤ l/2`. -/
lemma exists_int_close {l : ℝ} (hl : 0 < l) (k : ℕ) {t : ℝ}
    (ht : |t| ≤ (k : ℝ) * l / 2) :
    ∃ n : ℤ, -(((k / 2 : ℕ) : ℤ)) ≤ n ∧ n ≤ (((k / 2 : ℕ) : ℤ)) ∧
      |t - l * (n : ℝ)| ≤ l / 2 := by
  have hξ : |t / l| ≤ (k : ℝ) / 2 := by
    rw [abs_div, abs_of_pos hl]
    have h1 : |t| / l ≤ ((k : ℝ) * l / 2) / l := div_le_div_of_nonneg_right ht hl.le
    have h2 : ((k : ℝ) * l / 2) / l = (k : ℝ) / 2 := by
      rw [div_eq_iff (ne_of_gt hl)]
      ring
    rwa [h2] at h1
  obtain ⟨n, h1, h2, h3⟩ := exists_int_close_half k hξ
  refine ⟨n, h1, h2, ?_⟩
  have hkey : t - l * (n : ℝ) = l * (t / l - (n : ℝ)) := by
    rw [mul_sub, mul_div_cancel₀ t (ne_of_gt hl)]
  rw [hkey, abs_mul, abs_of_pos hl]
  have h4 := mul_le_mul_of_nonneg_left h3 hl.le
  linarith

/-! ## 4. The covering of `Λ(k l)` by `(k+1)³` translates of `Λ(l)` -/

lemma exists_cover_cell {l : ℝ} (hl : 0 < l) (k : ℕ) :
    ∃ C : Finset (Fin 3 → ℤ), C.card ≤ (k + 1) ^ 3 ∧
      ∀ x ∈ Work.BoseFixR.cell ((k : ℝ) * l),
        ∃ c ∈ C, x - l • latVec c ∈ Work.BoseFixR.cell l := by
  refine ⟨Fintype.piFinset
    (fun _ : Fin 3 => Finset.Icc (-(((k / 2 : ℕ) : ℤ))) (((k / 2 : ℕ) : ℤ))), ?_, ?_⟩
  · rw [Fintype.card_piFinset]
    have hcard : ∀ i : Fin 3,
        (Finset.Icc (-(((k / 2 : ℕ) : ℤ))) (((k / 2 : ℕ) : ℤ))).card = 2 * (k / 2) + 1 := by
      intro i
      rw [Int.card_Icc]
      have hz : (((k / 2 : ℕ) : ℤ) + 1 - (-(((k / 2 : ℕ) : ℤ))))
          = ((2 * (k / 2) + 1 : ℕ) : ℤ) := by
        push_cast
        ring
      rw [hz, Int.toNat_natCast]
    rw [Finset.prod_congr rfl (fun i _ => hcard i)]
    rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    exact Nat.pow_le_pow_left (by omega) 3
  · intro x hx
    have hx' : ∀ i, |x i| ≤ ((k : ℝ) * l) / 2 := Work.BoseFixR.mem_cell.mp hx
    choose n hn using fun i : Fin 3 => exists_int_close hl k (hx' i)
    refine ⟨n, ?_, ?_⟩
    · rw [Fintype.mem_piFinset]
      intro i
      exact Finset.mem_Icc.mpr ⟨(hn i).1, (hn i).2.1⟩
    · rw [Work.BoseFixR.mem_cell]
      intro i
      have h := (hn i).2.2
      simpa only [PiLp.sub_apply, PiLp.smul_apply, latVec_apply, smul_eq_mul] using h

/-! ## 5. Translating the indicator of a box by a lattice vector -/

lemma mem_cell_add_singleton_iff (s : Set E3) (a z : E3) :
    z + a ∈ s + ({a} : Set E3) ↔ z ∈ s := by
  rw [Set.add_singleton, Set.image_add_right, Set.mem_preimage, add_assoc, add_neg_cancel, add_zero]

lemma indicator_add_singleton_apply (s : Set E3) (a z : E3) :
    (s + ({a} : Set E3)).indicator (fun _ => (1 : ENNReal)) (z + a)
      = s.indicator (fun _ => (1 : ENNReal)) z := by
  have key : z + a ∈ s + ({a} : Set E3) ↔ z ∈ s := mem_cell_add_singleton_iff s a z
  by_cases h : z ∈ s
  · rw [Set.indicator_of_mem (key.mpr h), Set.indicator_of_mem h]
  · rw [Set.indicator_of_notMem (fun hh => h (key.mp hh)), Set.indicator_of_notMem h]

/-! ## 6. Periodicity of the lattice sum -/

lemma measurable_tsum_latVec {g : E3 → ENNReal} (hgm : Measurable g) (l : ℝ) :
    Measurable fun z : E3 => ∑' m : Fin 3 → ℤ, g (z + l • latVec m) :=
  Measurable.ennreal_tsum fun m =>
    hgm.comp (continuous_id.add continuous_const).measurable

lemma tsum_latVec_translate (g : E3 → ENNReal) (l : ℝ) (c : Fin 3 → ℤ) (z : E3) :
    (∑' m : Fin 3 → ℤ, g ((z + l • latVec c) + l • latVec m))
      = ∑' m : Fin 3 → ℤ, g (z + l • latVec m) := by
  have h1 : ∀ m : Fin 3 → ℤ,
      (z + l • latVec c) + l • latVec m = z + l • latVec (m + c) := by
    intro m
    rw [LatFourier.latVec_add, smul_add, add_assoc,
      add_comm (l • latVec c) (l • latVec m)]
  rw [tsum_congr fun m => congrArg g (h1 m)]
  simpa only [Equiv.coe_addRight] using
    (Equiv.tsum_eq (Equiv.addRight c) fun m : Fin 3 → ℤ => g (z + l • latVec m))

/-! ## 7. The shift of the box integral -/

lemma lintegral_indicator_shift_cell {l : ℝ} (g : E3 → ENNReal) (c : Fin 3 → ℤ) :
    ∫⁻ z, (Work.BoseFixR.cell l + ({(l • latVec c)} : Set E3)).indicator (fun _ => 1) z
        * (∑' m : Fin 3 → ℤ, g (z + l • latVec m))
      = ∫⁻ z, (Work.BoseFixR.cell l).indicator (fun _ => 1) z
        * (∑' m : Fin 3 → ℤ, g (z + l • latVec m)) := by
  -- the periodisation is invariant under translation by `l • latVec c`
  have hper : ∀ z : E3, (∑' m : Fin 3 → ℤ, g (z + l • latVec m))
      = ∑' m : Fin 3 → ℤ, g (z - l • latVec c + l • latVec m) := by
    intro z
    have h := tsum_latVec_translate g l c (z - l • latVec c)
    rw [sub_add_cancel] at h
    exact h
  have step1 : ∫⁻ z, (Work.BoseFixR.cell l + ({(l • latVec c)} : Set E3)).indicator
        (fun _ => 1) z * (∑' m : Fin 3 → ℤ, g (z + l • latVec m))
      = ∫⁻ z, (Work.BoseFixR.cell l + ({(l • latVec c)} : Set E3)).indicator
        (fun _ => 1) z * (∑' m : Fin 3 → ℤ, g (z - l • latVec c + l • latVec m)) :=
    lintegral_congr fun z => by rw [hper z]
  have step2 : ∫⁻ z, (Work.BoseFixR.cell l + ({(l • latVec c)} : Set E3)).indicator
        (fun _ => 1) z * (∑' m : Fin 3 → ℤ, g (z - l • latVec c + l • latVec m))
      = ∫⁻ z, (Work.BoseFixR.cell l + ({(l • latVec c)} : Set E3)).indicator
        (fun _ => 1) (z + l • latVec c)
        * (∑' m : Fin 3 → ℤ, g ((z + l • latVec c) - l • latVec c + l • latVec m)) :=
    (MeasureTheory.lintegral_add_right_eq_self
      (fun z : E3 => (Work.BoseFixR.cell l + ({(l • latVec c)} : Set E3)).indicator
        (fun _ => 1) z * (∑' m : Fin 3 → ℤ, g (z - l • latVec c + l • latVec m)))
      (l • latVec c)).symm
  have step3 : ∫⁻ z, (Work.BoseFixR.cell l + ({(l • latVec c)} : Set E3)).indicator
        (fun _ => 1) (z + l • latVec c)
        * (∑' m : Fin 3 → ℤ, g ((z + l • latVec c) - l • latVec c + l • latVec m))
      = ∫⁻ z, (Work.BoseFixR.cell l).indicator (fun _ => 1) z
        * (∑' m : Fin 3 → ℤ, g (z + l • latVec m)) := by
    refine lintegral_congr fun z => ?_
    rw [add_sub_cancel_right, indicator_add_singleton_apply]
  exact step1.trans (step2.trans step3)

/-! ## 8. The periodisation identity over `Λ(l)` -/

lemma integral_cell_periodisation {l : ℝ} (hl : 0 < l) {g : E3 → ENNReal} (hgm : Measurable g) :
    ∫⁻ z, (Work.BoseFixR.cell l).indicator (fun _ => 1) z
        * (∑' m : Fin 3 → ℤ, g (z + l • latVec m))
      = ∫⁻ z, g z := by
  have hfun : (fun z : E3 => (Work.BoseFixR.cell l).indicator (fun _ => 1) z
        * (∑' m : Fin 3 → ℤ, g (z + l • latVec m)))
      = (fun z : E3 => ∑' m : Fin 3 → ℤ,
          (Work.BoseFixR.cell l).indicator (fun _ => 1) z * g (z + l • latVec m)) :=
    funext fun z => (ENNReal.tsum_mul_left).symm
  rw [hfun]
  have key := MeasureTheory.lintegral_tsum (μ := (volume : Measure E3))
    (f := fun (m : Fin 3 → ℤ) (z : E3) =>
      (Work.BoseFixR.cell l).indicator (fun _ => 1) z * g (z + l • latVec m))
    (fun m => ((measurable_const.indicator (measurableSet_cell_bfr l)).mul
      (hgm.comp (continuous_id.add continuous_const).measurable)).aemeasurable)
  rw [key, lintegral_tiling_cell hl g]
  exact tsum_congr fun m => by
    rw [← MeasureTheory.lintegral_indicator (measurableSet_cell_bfr l)
      (fun z => g (z + l • latVec m))]
    refine lintegral_congr fun z => ?_
    by_cases hz : z ∈ Work.BoseFixR.cell l <;> simp [Set.indicator_apply, hz]

/-! ## 9. The target -/

theorem lintegral_tsum_translate_boxL_le {l : ℝ} (hl : 0 < l) (k : ℕ)
    {g : EuclideanSpace ℝ (Fin 3) → ENNReal} (hgm : Measurable g) :
    ∫⁻ z, (Work.BoseK15.corpusBox.boxL ((k : ℝ) * l)).indicator (fun _ => 1) z
        * (∑' m : Fin 3 → ℤ, g (z + l • Work.BoseBoxFock.latVec m))
      ≤ ((k + 1 : ℕ) : ENNReal) ^ 3 * ∫⁻ z, g z := by
  obtain ⟨C, hCcard, hCcov⟩ := exists_cover_cell hl k
  have hkl : (0 : ℝ) ≤ (k : ℝ) * l := by positivity
  rw [corpusBox_boxL_eq_cell_of_nonneg hkl]
  -- the lattice translates of `Λ(l)` dominate `Λ(k l)` pointwise
  have hpt : ∀ z : E3,
      (Work.BoseFixR.cell ((k : ℝ) * l)).indicator (fun _ => 1) z
          * (∑' m : Fin 3 → ℤ, g (z + l • latVec m))
        ≤ (∑ c ∈ C, (Work.BoseFixR.cell l + ({(l • latVec c)} : Set E3)).indicator
              (fun _ => 1) z) * (∑' m : Fin 3 → ℤ, g (z + l • latVec m)) := by
    intro z
    by_cases hz : z ∈ Work.BoseFixR.cell ((k : ℝ) * l)
    · obtain ⟨c, hcC, hcz⟩ := hCcov z hz
      have hmem : z ∈ Work.BoseFixR.cell l + ({(l • latVec c)} : Set E3) := by
        have h := (mem_cell_add_singleton_iff (Work.BoseFixR.cell l) (l • latVec c)
          (z - l • latVec c)).mpr hcz
        rwa [sub_add_cancel] at h
      have hone : (Work.BoseFixR.cell l + ({(l • latVec c)} : Set E3)).indicator
          (fun _ => (1 : ENNReal)) z = (1 : ENNReal) := by
        rw [Set.indicator_of_mem hmem]
      have hsingle : (Work.BoseFixR.cell l + ({(l • latVec c)} : Set E3)).indicator
            (fun _ => (1 : ENNReal)) z
          ≤ ∑ c' ∈ C, (Work.BoseFixR.cell l + ({(l • latVec c')} : Set E3)).indicator
              (fun _ => (1 : ENNReal)) z :=
        Finset.single_le_sum
          (f := fun c' => (Work.BoseFixR.cell l + ({(l • latVec c')} : Set E3)).indicator
            (fun _ => (1 : ENNReal)) z)
          (fun c' _ => (bot_le : (⊥ : ENNReal) ≤ _)) hcC
      rw [hone] at hsingle
      rw [Set.indicator_of_mem hz]
      exact mul_le_mul' hsingle le_rfl
    · rw [Set.indicator_of_notMem hz, zero_mul]
      exact (bot_le : (⊥ : ENNReal) ≤ _)
  calc ∫⁻ z, (Work.BoseFixR.cell ((k : ℝ) * l)).indicator (fun _ => 1) z
          * (∑' m : Fin 3 → ℤ, g (z + l • latVec m))
      ≤ ∫⁻ z, (∑ c ∈ C, (Work.BoseFixR.cell l + ({(l • latVec c)} : Set E3)).indicator
            (fun _ => 1) z) * (∑' m : Fin 3 → ℤ, g (z + l • latVec m)) :=
        lintegral_mono hpt
    _ = ∑ c ∈ C, ∫⁻ z, (Work.BoseFixR.cell l + ({(l • latVec c)} : Set E3)).indicator
            (fun _ => 1) z * (∑' m : Fin 3 → ℤ, g (z + l • latVec m)) := by
        rw [show (fun z : E3 => (∑ c ∈ C, (Work.BoseFixR.cell l +
              ({(l • latVec c)} : Set E3)).indicator (fun _ => 1) z)
              * (∑' m : Fin 3 → ℤ, g (z + l • latVec m)))
            = (fun z : E3 => ∑ c ∈ C, (Work.BoseFixR.cell l +
              ({(l • latVec c)} : Set E3)).indicator (fun _ => 1) z
              * (∑' m : Fin 3 → ℤ, g (z + l • latVec m))) from
            funext fun z => Finset.sum_mul ..]
        exact MeasureTheory.lintegral_finsetSum' C (fun c _ =>
          ((measurable_const.indicator (measurableSet_cell_add_singleton l (l • latVec c))).mul
            (measurable_tsum_latVec hgm l)).aemeasurable)
    _ = ∑ c ∈ C, ∫⁻ z, (Work.BoseFixR.cell l).indicator (fun _ => 1) z
            * (∑' m : Fin 3 → ℤ, g (z + l • latVec m)) :=
        Finset.sum_congr rfl fun c _ => lintegral_indicator_shift_cell g c
    _ = ((C.card : ℕ) : ENNReal) * ∫⁻ z, g z := by
        rw [Finset.sum_const, nsmul_eq_mul, integral_cell_periodisation hl hgm]
    _ ≤ ((k + 1 : ℕ) : ENNReal) ^ 3 * ∫⁻ z, g z := by
        rw [← Nat.cast_pow]
        refine mul_le_mul' ?_ le_rfl
        exact_mod_cast hCcard

end Work.BoseBoxFock
