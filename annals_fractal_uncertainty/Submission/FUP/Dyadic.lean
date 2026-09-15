import ChallengeDeps
import Submission.FUP.Nbhd
import Submission.FUP.SegmentMeasure
import Submission.FUP.BoxPorosity
import Submission.Commons.Measure.Real.porous_interval_measure_bound_uniform_set

open FractalUncertainty MeasureTheory FourierTransform Metric
open scoped ENNReal BigOperators RealInnerProductSpace

set_option autoImplicit false
variable {d : ℕ}
local notation "ℝᵈ" => EuclideanSpace ℝ (Fin d)

namespace Submission.FUP

/-- The closed annulus `{x | a ≤ ‖x‖ ≤ b}`. -/
def annulus (a b : ℝ) : Set ℝᵈ := {x | a ≤ ‖x‖ ∧ ‖x‖ ≤ b}

lemma mem_annulus {a b : ℝ} {x : ℝᵈ} : x ∈ annulus a b ↔ a ≤ ‖x‖ ∧ ‖x‖ ≤ b := Iff.rfl

/-- The parameter set of a unit-speed line meeting an annulus is contained in an interval of
length `2b` centred at the parameter of the closest point of the line to the origin. -/
lemma pullback_annulus_subset (p v : ℝᵈ) (hv : ‖v‖ = 1) {a b : ℝ} (hb : 0 ≤ b) :
    (fun t : ℝ => p + t • v) ⁻¹' annulus a b ⊆
      Set.Icc (-(⟪p, v⟫) - b) (-(⟪p, v⟫) + b) := by
  intro t ht
  rw [Set.mem_preimage, mem_annulus] at ht
  have h1 : ‖p + t • v‖ ^ 2 ≤ b ^ 2 := by
    nlinarith [norm_nonneg (p + t • v), ht.2, hb]
  have hexp : ‖p + t • v‖ ^ 2
      = (t + ⟪p, v⟫) ^ 2 + (‖p‖ ^ 2 - ⟪p, v⟫ ^ 2) := by
    rw [norm_add_sq_real, real_inner_smul_right]
    simp only [norm_smul, Real.norm_eq_abs, hv, mul_one, sq_abs]
    ring
  have hcauchy : ⟪p, v⟫ ^ 2 ≤ ‖p‖ ^ 2 := by
    have h := abs_real_inner_le_norm p v
    rw [hv, mul_one] at h
    rwa [sq_le_sq, abs_of_nonneg (norm_nonneg p)]
  have h2 : (t + ⟪p, v⟫) ^ 2 ≤ b ^ 2 := by nlinarith [hexp, h1, hcauchy]
  have h3 : |t + ⟪p, v⟫| ≤ b := by
    have := sq_le_sq.mp h2
    rwa [abs_of_nonneg hb] at this
  rw [Set.mem_Icc]
  have := abs_le.mp h3
  constructor <;> linarith

/-- An interval of length `2d` is covered by `M` consecutive intervals of length `L` whenever
`2d ≤ M·L`. -/
lemma Icc_subset_iUnion_Icc {c d L : ℝ} (hd : 0 < d) (hL : 0 < L) {M : ℕ}
    (hM : 2 * d ≤ (M : ℝ) * L) :
    Set.Icc (c - d) (c + d) ⊆
      ⋃ j : Fin M, Set.Icc (c - d + (j : ℝ) * L) (c - d + ((j : ℝ) + 1) * L) := by
  have hMpos : 0 < M := by
    by_contra h
    simp only [Nat.not_lt, Nat.le_zero] at h
    subst h
    simp at hM
    linarith
  intro t ht
  rw [Set.mem_Icc] at ht
  have hlo : (0 : ℝ) ≤ t - (c - d) := by linarith [ht.1]
  have hhi : t - (c - d) ≤ 0 + (M : ℝ) * L := by linarith [ht.2, hM]
  rcases exists_child_coord hL hMpos hlo hhi with ⟨j, hjM, hj1, hj2⟩
  refine Set.mem_iUnion.mpr ⟨⟨j, hjM⟩, ?_⟩
  rw [Set.mem_Icc]
  constructor <;> linarith

/-- **The §6.1 intersection estimate.**  A set `Z` which is `ν`-porous on lines from scale `ρ`
and which is contained in the annulus `{a ≤ ‖x‖ ≤ b}` intersects every (unit-speed) line in
one-dimensional measure at most `C · b · (ρ/L)^γ`, where `L = a/√d` is the length of the
`≲ √d` line segments on which the annulus has to be cut.  This is the estimate
`|Y_k ∩ ℓ| ≲ 2^k k^{-sγ}` of §6.1 of Cohen's paper. -/
theorem porous_annulus_line_measure {ν ρ α₁ a b : ℝ} {Z : Set ℝᵈ}
    (hν : 0 < ν) (hρ : 0 < ρ) (ha : 0 < a) (hab : a ≤ b)
    (hd : 1 ≤ d) (hZmeas : MeasurableSet Z) (hZ : PorousOnLines ν ρ α₁ Z)
    (hZsub : Z ⊆ annulus a b)
    (hρL : ρ < a / Real.sqrt (d : ℝ)) (hLα : a / Real.sqrt (d : ℝ) < α₁) :
    ∃ γ C : ℝ, 0 < γ ∧ 0 < C ∧
      ∀ (p v : ℝᵈ), ‖v‖ = 1 →
        (volume ((fun t : ℝ => p + t • v) ⁻¹' Z) : ℝ≥0∞) ≤
          ENNReal.ofReal (C * b * (ρ / (a / Real.sqrt (d : ℝ))) ^ γ) := by
  obtain ⟨γ, hγ, hbd⟩ :=
    Commons.Measure.Real.porous_interval_measure_bound_uniform_set (ν := ν) (α₀ := ρ) (α₁ := α₁)
      hν hρ
  refine ⟨γ, 3, hγ, by norm_num, ?_⟩
  intro p v hv
  set L : ℝ := a / Real.sqrt (d : ℝ) with hLdef
  have hsqd : 0 < Real.sqrt (d : ℝ) := Real.sqrt_pos.mpr (by exact_mod_cast (by omega : 0 < d))
  have hLpos : 0 < L := div_pos ha hsqd
  have hbpos : 0 < b := lt_of_lt_of_le ha hab
  set M : ℕ := ⌈2 * b / L⌉₊ with hMdef
  have hM2 : 2 * b ≤ (M : ℝ) * L := by
    have h := Nat.le_ceil (2 * b / L)
    rw [div_le_iff₀ hLpos] at h
    linarith [h]
  have hLb : L ≤ b := by
    have h1 : (Real.sqrt (d : ℝ))⁻¹ ≤ 1 :=
      inv_le_one_of_one_le₀ (by rw [← Real.sqrt_one]; exact Real.sqrt_le_sqrt (by exact_mod_cast hd))
    have h2 : L ≤ a := by
      rw [hLdef, div_eq_mul_inv]
      calc a * (Real.sqrt (d : ℝ))⁻¹ ≤ a * 1 := mul_le_mul_of_nonneg_left h1 (le_of_lt ha)
        _ = a := mul_one a
    linarith [hab]
  have hM3 : (M : ℝ) * L ≤ 3 * b := by
    have h := Nat.ceil_lt_add_one (show (0:ℝ) ≤ 2 * b / L by positivity)
    rw [hMdef]
    have hmul : (⌈2 * b / L⌉₊ : ℝ) * L < (2 * b / L + 1) * L :=
      mul_lt_mul_of_pos_right h hLpos
    have hexp : (2 * b / L + 1) * L = 2 * b + L := by field_simp
    linarith [hmul, hexp]
  -- the pullback of the annulus is contained in an interval of length `2b`
  set c : ℝ := -(⟪p, v⟫) with hcdef
  have hsub : (fun t : ℝ => p + t • v) ⁻¹' Z ⊆ Set.Icc (c - b) (c + b) := by
    intro t ht
    have := pullback_annulus_subset p v hv (le_of_lt hbpos) (hZsub ht)
    simpa [c] using this
  -- pullback porosity and measurability
  have hγcont : Continuous (fun t : ℝ => p + t • v) :=
    continuous_const.add (continuous_id.smul continuous_const)
  have hXmeas : MeasurableSet ((fun t : ℝ => p + t • v) ⁻¹' Z) :=
    hZmeas.preimage hγcont.measurable
  have hpor : PorousIntervals ν ρ α₁ ((fun t : ℝ => p + t • v) ⁻¹' Z) :=
    pullback_porous_of_unitSpeed p v hv hρ hZ
  -- the per-segment bound
  have hseg : ∀ j : Fin M, volume ((fun t : ℝ => p + t • v) ⁻¹' Z ∩
      Set.Icc (c - b + (j : ℝ) * L) (c - b + ((j : ℝ) + 1) * L))
      ≤ ENNReal.ofReal (L * (ρ / L) ^ γ) := by
    intro j
    have hdiff : (c - b + ((j : ℝ) + 1) * L) - (c - b + (j : ℝ) * L) = L := by ring
    have h1 := hbd ((fun t : ℝ => p + t • v) ⁻¹' Z) hXmeas
      (fun y R hR => hpor y R hR) (c - b + (j : ℝ) * L) (c - b + ((j : ℝ) + 1) * L)
      (by rw [hdiff]; exact ⟨hρL, hLα⟩)
    simpa [hdiff] using h1
  have hcover : Set.Icc (c - b) (c + b) ⊆
      ⋃ j : Fin M, Set.Icc (c - b + (j : ℝ) * L) (c - b + ((j : ℝ) + 1) * L) :=
    Icc_subset_iUnion_Icc hbpos hLpos hM2
  calc (volume ((fun t : ℝ => p + t • v) ⁻¹' Z) : ℝ≥0∞)
      = volume ((fun t : ℝ => p + t • v) ⁻¹' Z ∩ Set.Icc (c - b) (c + b)) := by
        rw [Set.inter_eq_left.mpr hsub]
    _ ≤ volume (⋃ j : Fin M, (fun t : ℝ => p + t • v) ⁻¹' Z ∩
          Set.Icc (c - b + (j : ℝ) * L) (c - b + ((j : ℝ) + 1) * L)) := by
        refine measure_mono (fun t ht => ?_)
        rcases Set.mem_iUnion.mp (hcover ht.2) with ⟨j, hj⟩
        exact Set.mem_iUnion.mpr ⟨j, ⟨ht.1, hj⟩⟩
    _ ≤ ∑ j : Fin M, volume ((fun t : ℝ => p + t • v) ⁻¹' Z ∩
          Set.Icc (c - b + (j : ℝ) * L) (c - b + ((j : ℝ) + 1) * L)) :=
        measure_iUnion_fintype_le _ _
    _ ≤ ∑ _j : Fin M, ENNReal.ofReal (L * (ρ / L) ^ γ) := Finset.sum_le_sum (fun j _ => hseg j)
    _ = (M : ℝ≥0∞) * ENNReal.ofReal (L * (ρ / L) ^ γ) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    _ = ENNReal.ofReal ((M : ℝ) * (L * (ρ / L) ^ γ)) := by
        rw [← ENNReal.ofReal_natCast M, ← ENNReal.ofReal_mul (by positivity)]
    _ ≤ ENNReal.ofReal (3 * b * (ρ / L) ^ γ) := by
        refine ENNReal.ofReal_le_ofReal ?_
        have hpow : 0 ≤ (ρ / L) ^ γ := Real.rpow_nonneg (by positivity) γ
        have : (M : ℝ) * (L * (ρ / L) ^ γ) = ((M : ℝ) * L) * (ρ / L) ^ γ := by ring
        rw [this]
        exact mul_le_mul_of_nonneg_right hM3 hpow

lemma isClosed_annulus (a b : ℝ) : IsClosed (annulus a b : Set ℝᵈ) := by
  have h1 : IsClosed {x : ℝᵈ | a ≤ ‖x‖} := isClosed_le continuous_const continuous_norm
  have h2 : IsClosed {x : ℝᵈ | ‖x‖ ≤ b} := isClosed_le continuous_norm continuous_const
  have : annulus a b = {x : ℝᵈ | a ≤ ‖x‖} ∩ {x : ℝᵈ | ‖x‖ ≤ b} := rfl
  rw [this]
  exact h1.inter h2

/-- A closed `r`-neighbourhood of a set inside an annulus stays inside a (slightly larger)
annulus. -/
lemma addSet_closedBall_subset_annulus {A : Set ℝᵈ} {r a b : ℝ} (hA : A ⊆ annulus a b)
    (hr : 0 ≤ r) : addSet A (closedBall 0 r) ⊆ annulus (a - r) (b + r) := by
  rintro z ⟨y, hy, w, hw, rfl⟩
  have hy' := hA hy
  have hw' : ‖w‖ ≤ r := by
    simpa using (Metric.mem_closedBall.mp hw : dist w 0 ≤ r)
  rw [mem_annulus] at hy' ⊢
  constructor
  · calc a - r ≤ ‖y‖ - ‖w‖ := by linarith [hy'.1]
      _ ≤ ‖y + w‖ := by
          have h := norm_add_le (y + w) (-w)
          rw [add_neg_cancel_right, norm_neg] at h
          linarith
  · calc ‖y + w‖ ≤ ‖y‖ + ‖w‖ := norm_add_le y w
      _ ≤ b + r := by linarith [hy'.2]

/-- **The §6.1 growth estimate.**  For `Y` porous on lines from scale `μ` and
`W_k = 2^k/k^s`, the closed `2√d W_k`-neighbourhood of `Y ∩ A_k` (which contains the
"combinatorial" piece `Y_k` of Cohen's §6.1) meets every unit-speed line in one-dimensional
measure at most `C · 2^k · k^{-sγ}`. -/
theorem line_porous_annulus_growth_bound {ν μ α₁ s : ℝ} {Y : Set ℝᵈ}
    (hν : 0 < ν) (hμ : 0 < μ) (hd : 1 ≤ d) (hY : PorousOnLines ν μ α₁ Y)
    (k : ℕ) (hk : 1 ≤ k)
    (hμr : μ ≤ 8 * Real.sqrt (d : ℝ) * ((2:ℝ)^k / (k:ℝ)^s) / ν)
    (hr : 2 * Real.sqrt (d : ℝ) * ((2:ℝ)^k / (k:ℝ)^s) ≤ (2:ℝ)^k / 2)
    (hLα : (2:ℝ)^k / (2 * Real.sqrt (d : ℝ)) < α₁)
    (hk16 : 16 * (d : ℝ) / (ν * (k:ℝ)^s) < 1) :
    ∃ γ C : ℝ, 0 < γ ∧ 0 < C ∧
      ∀ (p v : ℝᵈ), ‖v‖ = 1 →
        (volume ((fun t : ℝ => p + t • v) ⁻¹'
          (nbhd (Y ∩ annulus ((2:ℝ)^k) ((2:ℝ)^(k+1)))
            (2 * Real.sqrt (d : ℝ) * ((2:ℝ)^k / (k:ℝ)^s)))) : ℝ≥0∞) ≤
          ENNReal.ofReal (C * (2:ℝ)^k * (k:ℝ)^(-(s * γ))) := by
  have hsqd : 0 < Real.sqrt (d : ℝ) := Real.sqrt_pos.mpr (by exact_mod_cast (by omega : 0 < d))
  have h2k : 0 < (2:ℝ)^k := pow_pos (by norm_num) k
  have hks : 0 < (k:ℝ) := by exact_mod_cast (by omega : 0 < k)
  have hWpos : 0 < (2:ℝ)^k / (k:ℝ)^s := div_pos h2k (Real.rpow_pos_of_pos hks s)
  set r : ℝ := 2 * Real.sqrt (d : ℝ) * ((2:ℝ)^k / (k:ℝ)^s) with hrdef
  have hrpos : 0 < r := by rw [hrdef]; positivity
  have hY' : PorousOnLines ν μ α₁ (Y ∩ annulus ((2:ℝ)^k) ((2:ℝ)^(k+1))) :=
    PorousOnLines.mono_set hY Set.inter_subset_left
  have hρeq : 4 * r / ν = 8 * Real.sqrt (d : ℝ) * ((2:ℝ)^k / (k:ℝ)^s) / ν := by
    rw [hrdef]; ring
  have hZpor : PorousOnLines (ν / 2) (4 * r / ν) α₁
      (nbhd (Y ∩ annulus ((2:ℝ)^k) ((2:ℝ)^(k+1))) r) :=
    PorousOnLines_nbhd hμ hν (by rw [hρeq]; exact hμr) hY'
  have hZsub : nbhd (Y ∩ annulus ((2:ℝ)^k) ((2:ℝ)^(k+1))) r ⊆
      annulus ((2:ℝ)^k / 2) ((2:ℝ)^(k+2)) := by
    refine closure_minimal ?_ (isClosed_annulus _ _)
    refine (addSet_closedBall_subset_annulus (A := Y ∩ annulus ((2:ℝ)^k) ((2:ℝ)^(k+1)))
      Set.inter_subset_right (le_of_lt hrpos)).trans ?_
    intro x hx
    rw [mem_annulus] at hx ⊢
    constructor
    · linarith [hx.1, hr]
    · have h4 : (2:ℝ)^(k+2) = 2 * (2:ℝ)^(k+1) := by
        rw [show k + 2 = (k + 1) + 1 from rfl, pow_succ]
        ring
      have h2 : r ≤ (2:ℝ)^(k+1) := by
        have h3 : (2:ℝ)^k / 2 ≤ (2:ℝ)^(k+1) := by
          rw [pow_succ]; linarith [h2k]
        linarith [hr]
      linarith [hx.2, h2, h4]
  have hρL : 4 * r / ν < ((2:ℝ)^k / 2) / Real.sqrt (d : ℝ) := by
    have heq : 4 * r / ν
        = (16 * (d : ℝ) / (ν * (k:ℝ)^s)) * ((2:ℝ)^k / (2 * Real.sqrt (d : ℝ))) := by
      rw [hrdef]; field_simp
      rw [Real.sq_sqrt (by positivity : (0:ℝ) ≤ (d:ℝ))]
      ring
    have heq2 : ((2:ℝ)^k / 2) / Real.sqrt (d : ℝ) = (2:ℝ)^k / (2 * Real.sqrt (d : ℝ)) :=
      div_div _ _ _
    rw [heq, heq2]
    calc (16 * (d : ℝ) / (ν * (k:ℝ)^s)) * ((2:ℝ)^k / (2 * Real.sqrt (d : ℝ)))
        < 1 * ((2:ℝ)^k / (2 * Real.sqrt (d : ℝ))) :=
          mul_lt_mul_of_pos_right hk16 (by positivity)
      _ = (2:ℝ)^k / (2 * Real.sqrt (d : ℝ)) := one_mul _
  obtain ⟨γ, C₀, hγ, hC₀, hbd⟩ := porous_annulus_line_measure
    (ν := ν / 2) (ρ := 4 * r / ν) (α₁ := α₁) (a := (2:ℝ)^k / 2) (b := (2:ℝ)^(k+2))
    (Z := nbhd (Y ∩ annulus ((2:ℝ)^k) ((2:ℝ)^(k+1))) r)
    (by positivity) (by positivity)
    (by positivity : (0:ℝ) < (2:ℝ)^k / 2)
    (by have h : (2:ℝ)^k ≤ (2:ℝ)^(k+2) := pow_le_pow_right₀ (by norm_num) (by omega)
        linarith [h2k])
    hd (measurableSet_nbhd _ _) hZpor hZsub hρL (by rw [div_div]; exact hLα)
  refine ⟨γ, C₀ * 4 * (16 * (d : ℝ) / ν)^γ, hγ, by positivity, ?_⟩
  intro p v hv
  refine le_trans (hbd p v hv) ?_
  refine ENNReal.ofReal_le_ofReal ?_
  have hb : (2:ℝ)^(k+2) = 4 * (2:ℝ)^k := by rw [pow_succ, pow_succ]; ring
  have hratio : (4 * r / ν) / (((2:ℝ)^k / 2) / Real.sqrt (d : ℝ))
      = 16 * (d : ℝ) / (ν * (k:ℝ)^s) := by
    rw [div_div, hrdef]
    field_simp
    rw [Real.sq_sqrt (by positivity : (0:ℝ) ≤ (d:ℝ))]
    ring
  have hrpow : (16 * (d : ℝ) / (ν * (k:ℝ)^s))^γ
      = (16 * (d : ℝ) / ν)^γ * (k:ℝ)^(-(s * γ)) := by
    have hνk : 0 < ν * (k:ℝ)^s := mul_pos hν (Real.rpow_pos_of_pos hks s)
    have hA : 0 < (16:ℝ) * (d : ℝ) := by positivity
    rw [Real.div_rpow (le_of_lt hA) (le_of_lt hνk)]
    rw [Real.div_rpow (le_of_lt hA) (le_of_lt hν)]
    rw [Real.mul_rpow (le_of_lt hν) (Real.rpow_nonneg (le_of_lt hks) s)]
    rw [← Real.rpow_mul (le_of_lt hks) s γ]
    rw [Real.rpow_neg (le_of_lt hks)]
    field_simp
  rw [hb, hratio, hrpow]
  exact le_of_eq (by ring)

end Submission.FUP
