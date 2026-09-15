import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Order.CompletePartialOrder
import Submission.Commons.Measure.Real.porous_power_bound

open MeasureTheory Set Metric
open scoped ENNReal BigOperators NNReal Topology

namespace Commons.Measure.Real

noncomputable section

/-- `(t + j·w) + w = t + (j+1)·w` (cast helper). -/
private lemma cell_upper (t w : ℝ) (j : ℕ) : (t + (j : ℝ) * w) + w = t + ((j + 1 : ℕ) : ℝ) * w := by
  rw [Nat.cast_add, Nat.cast_one]
  ring

/-- The maximum (over all positions) of the Lebesgue measure of `X` inside a closed
interval of length `δ`.  Used to prove one-dimensional regularity of porous sets. -/
private def porMass (X : Set ℝ) (δ : ℝ) : ℝ≥0∞ :=
  ⨆ t : ℝ, MeasureTheory.volume (X ∩ Set.Icc t (t + δ))

private lemma porMass_ge (X : Set ℝ) (t δ : ℝ) :
    MeasureTheory.volume (X ∩ Set.Icc t (t + δ)) ≤ porMass X δ := by
  exact le_iSup (fun t : ℝ => MeasureTheory.volume (X ∩ Set.Icc t (t + δ))) t

private lemma porMass_le_ofReal (X : Set ℝ) (δ : ℝ) (_hδ : 0 ≤ δ) :
    porMass X δ ≤ ENNReal.ofReal δ := by
  apply iSup_le
  intro t
  calc
    MeasureTheory.volume (X ∩ Set.Icc t (t + δ)) ≤
        MeasureTheory.volume (Set.Icc t (t + δ)) :=
          measure_mono (fun z hz => hz.2)
    _ = ENNReal.ofReal ((t + δ) - t) := by rw [Real.volume_Icc]
    _ = ENNReal.ofReal δ := by congr 1; ring

/-- A closed interval of length `L·w` is covered by `L` consecutive closed subintervals
of length `w`, i.e. `[u + j·w, u + (j+1)·w]` for `j < L`. -/
private lemma exists_step_mem (u w x : ℝ) :
    ∀ L : ℕ, 0 < L → x ∈ Set.Icc u (u + (L : ℝ) * w) →
      ∃ j : ℕ, j < L ∧ x ∈ Set.Icc (u + (j : ℝ) * w) (u + ((j + 1 : ℕ) : ℝ) * w) := by
  intro L
  induction L with
  | zero =>
      intro hL
      omega
  | succ L ih =>
      intro hL hx
      by_cases hL0 : L = 0
      · subst L
        refine ⟨0, by norm_num, ?_⟩
        simpa using hx
      · have hLpos : 0 < L := Nat.pos_of_ne_zero hL0
        by_cases hxL : x ≤ u + (L : ℝ) * w
        · have hx' : x ∈ Set.Icc u (u + (L : ℝ) * w) := ⟨hx.1, hxL⟩
          rcases ih hLpos hx' with ⟨j, hjL, hxcell⟩
          exact ⟨j, by omega, hxcell⟩
        · refine ⟨L, by omega, ?_⟩
          constructor
          · exact le_of_not_ge hxL
          · simpa [Nat.cast_add] using hx.2

/-- A subinterval of length `w` containing `x` lies in the ball `closedBall x w`. -/
private lemma Icc_subset_closedBall {u x w : ℝ} (_hw : 0 ≤ w) (hx : x ∈ Set.Icc u (u + w)) :
    Set.Icc u (u + w) ⊆ Metric.closedBall x w := by
  intro y hy
  rw [Metric.mem_closedBall, Real.dist_eq]
  rw [abs_le]
  constructor
  · linarith [hy.1, hx.2]
  · linarith [hy.2, hx.1]

/-- Core recursion: if `X` is `ν`-porous at scale `δ ∈ (α₀, α₁)`, then its `δ`-mass is at
most `(L-1)` times its `δ/L`-mass, provided the ball of radius `ν·δ` contains a sub-piece of
length `δ/L` (`(1/L) ≤ ν`). -/
private lemma porMass_rec {ν α₀ α₁ : ℝ} {X : Set ℝ}
    (hpor : ∀ (y : ℝ), ∀ R ∈ Set.Ioo α₀ α₁, ∃ x ∈ Metric.closedBall y (R / 2),
      Metric.closedBall x (ν * R) ∩ X = ∅)
    (hα₀ : 0 < α₀) {δ : ℝ} (hδ : δ ∈ Set.Ioo α₀ α₁) {L : ℕ} (hL : 0 < L)
    (hνL : (L : ℝ)⁻¹ ≤ ν) :
    porMass X δ ≤ (((L - 1 : ℕ) : ℝ≥0∞) : ℝ≥0∞) * porMass X (δ / (L : ℝ)) := by
  have hδpos : 0 < δ := lt_trans hα₀ (Set.mem_Ioo.mp hδ).1
  have hLposℝ : (0 : ℝ) < (L : ℝ) := by exact_mod_cast hL
  have hLnz : (L : ℝ) ≠ 0 := ne_of_gt hLposℝ
  let w : ℝ := δ / (L : ℝ)
  have hwpos : 0 < w := div_pos hδpos hLposℝ
  have hwpos0 : 0 ≤ w := le_of_lt hwpos
  have hLw : (L : ℝ) * w = δ := by
    dsimp [w]
    field_simp [hLnz]
  apply iSup_le
  intro t
  rcases hpor (t + δ / 2) δ hδ with ⟨x, hxball, hxempty⟩
  have hxI : x ∈ Set.Icc t (t + δ) := by
    rw [Real.closedBall_eq_Icc] at hxball
    convert hxball using 1 <;> ring
  have hxw : x ∈ Set.Icc t (t + (L : ℝ) * w) := by
    rw [hLw]
    exact hxI
  rcases exists_step_mem t w x L hL hxw with ⟨j₀, hj₀L, hxcell⟩
  let child : ℕ → Set ℝ := fun j => Set.Icc (t + (j : ℝ) * w) ((t + (j : ℝ) * w) + w)
  have hxcell₀ : x ∈ child j₀ := by
    dsimp [child]
    rw [cell_upper]
    exact hxcell
  have hsub₀ : child j₀ ⊆ closedBall x w := by
    exact Icc_subset_closedBall hwpos0 hxcell₀
  have hνw : w ≤ ν * δ := by
    have h₁ : (L : ℝ)⁻¹ * δ ≤ ν * δ := mul_le_mul_of_nonneg_right hνL (le_of_lt hδpos)
    calc
      w = δ * (L : ℝ)⁻¹ := by dsimp [w]; rw [div_eq_mul_inv]
      _ ≤ ν * δ := by
        simpa [mul_comm, mul_left_comm, mul_assoc] using h₁
  have hXcell₀ : X ∩ child j₀ = ∅ := by
    apply Set.subset_empty_iff.mp
    intro z hz
    have hzball₀ : z ∈ closedBall x w := hsub₀ hz.2
    have hzball : z ∈ closedBall x (ν * δ) :=
      (closedBall_subset_closedBall hνw) hzball₀
    have hzmem : z ∈ closedBall x (ν * δ) ∩ X := ⟨hzball, hz.1⟩
    simpa [hxempty] using hzmem
  have hcov : X ∩ Set.Icc t (t + δ) ⊆
      ⋃ j ∈ (Finset.range L).erase j₀, X ∩ child j := by
    intro z hz
    have hzI : z ∈ Set.Icc t (t + δ) := hz.2
    have hzIw : z ∈ Set.Icc t (t + (L : ℝ) * w) := by
      rw [hLw]
      exact hzI
    rcases exists_step_mem t w z L hL hzIw with ⟨j, hjL, hzcell⟩
    have hzcell' : z ∈ child j := by
      dsimp [child]
      rw [cell_upper]
      exact hzcell
    have hjne : j ≠ j₀ := by
      intro hjeq
      have hmem : z ∈ X ∩ child j₀ := ⟨hz.1, by simpa [hjeq] using hzcell'⟩
      simpa [hXcell₀] using hmem
    simp only [Set.mem_iUnion, Finset.mem_erase]
    exact ⟨j, ⟨hjne, Finset.mem_range.mpr hjL⟩, ⟨hz.1, hzcell'⟩⟩
  calc
    MeasureTheory.volume (X ∩ Set.Icc t (t + δ))
        ≤ MeasureTheory.volume (⋃ j ∈ Finset.range L, X ∩ child j) := measure_mono (by
            intro z hz
            have hzI : z ∈ Set.Icc t (t + δ) := hz.2
            have hzIw : z ∈ Set.Icc t (t + (L : ℝ) * w) := by
              rw [hLw]
              exact hzI
            rcases exists_step_mem t w z L hL hzIw with ⟨j, hjL, hzcell⟩
            have hzcell' : z ∈ child j := by
              dsimp [child]
              rw [cell_upper]
              exact hzcell
            simp only [Set.mem_iUnion, Finset.mem_range]
            exact ⟨j, hjL, ⟨hz.1, hzcell'⟩⟩)
    _ ≤ ∑ j ∈ Finset.range L, MeasureTheory.volume (X ∩ child j) := by
          exact MeasureTheory.measure_biUnion_finset_le _ _
    _ = ∑ j ∈ (Finset.range L).erase j₀, MeasureTheory.volume (X ∩ child j) := by
          rw [← Finset.sum_erase_add (Finset.range L)
              (fun j => MeasureTheory.volume (X ∩ child j)) (Finset.mem_range.mpr hj₀L)]
          rw [hXcell₀]
          simp
    _ ≤ ∑ j ∈ (Finset.range L).erase j₀, porMass X w := by
          apply Finset.sum_le_sum
          intro j hj
          have hv := porMass_ge X (t + (j : ℝ) * w) w
          have hjcell : X ∩ child j = X ∩ Set.Icc (t + (j : ℝ) * w) ((t + (j : ℝ) * w) + w) := rfl
          rw [hjcell]
          simpa using hv
    _ = ((Finset.range L).erase j₀).card • porMass X w := by rw [Finset.sum_const]
    _ = (((L - 1 : ℕ) : ℝ≥0∞) : ℝ≥0∞) * porMass X w := by
          rw [Finset.card_erase_of_mem (Finset.mem_range.mpr hj₀L), Finset.card_range]
          rw [nsmul_eq_mul]

end


/-- Iterating `porMass_rec` over `n` levels: the mass at scale `R` is at most
`(L-1)^n` times the mass at scale `R/L^n`, as long as porosity applies at all the
intermediate scales. -/
private lemma porMass_iter {ν α₀ α₁ : ℝ} {X : Set ℝ}
    (hpor : ∀ (y : ℝ), ∀ R ∈ Set.Ioo α₀ α₁, ∃ x ∈ Metric.closedBall y (R / 2),
      Metric.closedBall x (ν * R) ∩ X = ∅)
    (hα₀ : 0 < α₀) (R : ℝ) {L : ℕ} (hL : 0 < L) (hνL : (L : ℝ)⁻¹ ≤ ν) :
    ∀ n : ℕ, (∀ j : ℕ, j < n → R / (L : ℝ) ^ j ∈ Set.Ioo α₀ α₁) →
      porMass X R ≤ ((((L - 1 : ℕ) : ℝ≥0∞) : ℝ≥0∞) ^ n) *
        porMass X (R / (L : ℝ) ^ n) := by
  have hLnz : (L : ℝ) ≠ 0 := by
    have : (0 : ℝ) < (L : ℝ) := by exact_mod_cast hL
    exact ne_of_gt this
  intro n
  induction n with
  | zero =>
      intro hvalid
      simp
  | succ n ih =>
      intro hvalid
      have hvalid_n : R / (L : ℝ) ^ n ∈ Set.Ioo α₀ α₁ := hvalid n (by omega)
      have hrec := porMass_rec (ν := ν) (α₀ := α₀) (α₁ := α₁) (X := X) hpor hα₀
        (δ := R / (L : ℝ) ^ n) (hδ := hvalid_n) (L := L) (hL := hL) (hνL := hνL)
      have hrew : (R / (L : ℝ) ^ n) / (L : ℝ) = R / (L : ℝ) ^ (n + 1) := by
        rw [pow_succ]
        field_simp [hLnz]
      have hrec' : porMass X (R / (L : ℝ) ^ n) ≤
          (((L - 1 : ℕ) : ℝ≥0∞) : ℝ≥0∞) * porMass X (R / (L : ℝ) ^ (n + 1)) := by
        simpa [hrew] using hrec
      have hih := ih (fun j hj => hvalid j (by omega))
      calc
        porMass X R ≤ ((((L - 1 : ℕ) : ℝ≥0∞) : ℝ≥0∞) ^ n) * porMass X (R / (L : ℝ) ^ n) := hih
        _ ≤ ((((L - 1 : ℕ) : ℝ≥0∞) : ℝ≥0∞) ^ n) *
            ((((L - 1 : ℕ) : ℝ≥0∞) : ℝ≥0∞) * porMass X (R / (L : ℝ) ^ (n + 1))) := by
          exact mul_le_mul_of_nonneg_left hrec' zero_le
        _ = (((L - 1 : ℕ) : ℝ≥0∞) : ℝ≥0∞) ^ (n + 1) * porMass X (R / (L : ℝ) ^ (n + 1)) := by
          simp [pow_succ, mul_assoc]

/-- A natural number power inside `ℝ≥0∞`: `(n : ℝ≥0∞)^N = ((n^N) : ℝ≥0∞)`. -/
private lemma enn_natCast_pow (n N : ℕ) :
    (((n : ℝ≥0∞) : ℝ≥0∞) ^ N) = (((n ^ N : ℕ) : ℝ≥0∞) : ℝ≥0∞) := by
  induction N with
  | zero => simp
  | succ N ih =>
      rw [pow_succ, ih]
      rw [pow_succ]
      simp

/-- In the one-dimensional regularity estimate for porous sets the exponent `γ` (and even the
constant `1`) can be taken *uniform in the set* `X` and in the position and length of the
interval: `γ` depends only on `ν`.  This is what the proof actually produces, since
`γ = log(L/(L-1))/log L` for `L = ⌈ν⁻¹⌉`. -/
theorem porous_interval_measure_bound_uniform_set {ν α₀ α₁ : ℝ} (hν : 0 < ν) (hα₀ : 0 < α₀) :
    ∃ γ : ℝ, 0 < γ ∧
      ∀ (X : Set ℝ), MeasurableSet X →
        (∀ (y : ℝ), ∀ R ∈ Set.Ioo α₀ α₁, ∃ x ∈ Metric.closedBall y (R / 2),
          Metric.closedBall x (ν * R) ∩ X = ∅) →
        ∀ a b : ℝ, b - a ∈ Set.Ioo α₀ α₁ →
          (MeasureTheory.volume (X ∩ Set.Icc a b) : ENNReal) ≤
            ENNReal.ofReal ((b - a) * ((α₀ / (b - a)) ^ γ)) := by
  obtain ⟨L, hLge2, hνL⟩ : ∃ L : ℕ, 2 ≤ L ∧ (L : ℝ)⁻¹ ≤ ν := by
    by_cases hν12 : (1 / 2 : ℝ) ≤ ν
    · refine ⟨2, by norm_num, ?_⟩
      norm_num
      exact hν12
    · have hνlt : ν < 1 / 2 := lt_of_not_ge hν12
      obtain ⟨L, hL⟩ := exists_nat_ge (ν⁻¹)
      have h2inv : (2 : ℝ) ≤ ν⁻¹ := by
        have hνne : ν ≠ 0 := ne_of_gt hν
        field_simp [hνne]
        nlinarith
      have hL2 : (2 : ℝ) ≤ (L : ℝ) := le_trans h2inv hL
      refine ⟨L, ?_, ?_⟩
      · exact_mod_cast hL2
      · have hLpos : (0 : ℝ) < (L : ℝ) := lt_of_lt_of_le (by norm_num) hL2
        have hνinvpos : (0 : ℝ) < ν⁻¹ := inv_pos.mpr hν
        have := (inv_le_inv₀ hLpos hνinvpos).mpr hL
        simpa using this
  have hLpos : 0 < L := by omega
  have hLposℝ : (0 : ℝ) < (L : ℝ) := by exact_mod_cast hLpos
  have hL1 : (1 : ℝ) < (L : ℝ) := by
    have : (1 : ℕ) < L := by omega
    exact_mod_cast this
  let γ : ℝ := Real.log ((L : ℝ) / ((L : ℝ) - 1)) / Real.log (L : ℝ)
  have hγpos : 0 < γ := by
    dsimp only [γ]
    have hfrac : 1 < (L : ℝ) / ((L : ℝ) - 1) := by
      rw [lt_div_iff₀ (by linarith : (0 : ℝ) < (L : ℝ) - 1)]
      linarith
    exact div_pos (Real.log_pos hfrac) (Real.log_pos hL1)
  refine ⟨γ, hγpos, ?_⟩
  intro X _hX hpor a b hR
  let R : ℝ := b - a
  have hRα0 : α₀ < R := (Set.mem_Ioo.mp hR).1
  have hRα1 : R < α₁ := (Set.mem_Ioo.mp hR).2
  have hRpos : 0 < R := lt_trans hα₀ hRα0
  have hLnz : (L : ℝ) ≠ 0 := ne_of_gt hLposℝ
  have hex : ∃ j : ℕ, R / (L : ℝ) ^ j ≤ α₀ := by
    obtain ⟨j, hj⟩ : ∃ j : ℕ, (R / α₀ : ℝ) ≤ (L : ℝ) ^ j :=
      (tendsto_pow_atTop_atTop_of_one_lt hL1).eventually_ge_atTop (R / α₀) |> Filter.Eventually.exists
    refine ⟨j, ?_⟩
    have hLNpos : (0 : ℝ) < (L : ℝ) ^ j := pow_pos hLposℝ j
    have hmain : R ≤ α₀ * (L : ℝ) ^ j := by
      have hmul := mul_le_mul_of_nonneg_right hj (le_of_lt hα₀)
      field_simp [hα₀.ne'] at hmul
      simpa [mul_comm] using hmul
    exact (div_le_iff₀ hLNpos).mpr hmain
  let N : ℕ := Nat.find hex
  have hN : R / (L : ℝ) ^ N ≤ α₀ := Nat.find_spec hex
  have hNmin : ∀ j : ℕ, j < N → α₀ < R / (L : ℝ) ^ j := by
    intro j hj
    by_contra hnot
    have hle : R / (L : ℝ) ^ j ≤ α₀ := le_of_not_gt hnot
    have hNle : N ≤ j := Nat.find_min' hex hle
    omega
  have hvalid : ∀ j : ℕ, j < N → R / (L : ℝ) ^ j ∈ Set.Ioo α₀ α₁ := by
    intro j hj
    constructor
    · exact hNmin j hj
    · have hge1 : (1 : ℝ) ≤ (L : ℝ) ^ j := one_le_pow₀ (le_of_lt hL1)
      have hleR : R / (L : ℝ) ^ j ≤ R := by
        rw [div_le_iff₀ (pow_pos hLposℝ j)]
        have hle : R * 1 ≤ R * (L : ℝ) ^ j := mul_le_mul_of_nonneg_left hge1 (le_of_lt hRpos)
        simpa using hle
      exact lt_of_le_of_lt hleR hRα1
  have hδNpos : 0 ≤ R / (L : ℝ) ^ N := le_of_lt (div_pos hRpos (pow_pos hLposℝ N))
  have hboundReal : ((((L - 1 : ℕ) : ℝ) ^ N) * (R / (L : ℝ) ^ N)) ≤ R * (α₀ / R) ^ γ := by
    dsimp only [γ]
    exact porous_power_bound L hLge2 N R α₀ hRpos hα₀ hN
  have hb : b = a + R := by
    dsimp [R]
    ring
  have hvol : MeasureTheory.volume (X ∩ Set.Icc a b) ≤ ENNReal.ofReal (R * (α₀ / R) ^ γ) := by
    calc
      MeasureTheory.volume (X ∩ Set.Icc a b)
          = MeasureTheory.volume (X ∩ Set.Icc a (a + R)) := by rw [hb]
      _ ≤ porMass X R := porMass_ge X a R
      _ ≤ ((((L - 1 : ℕ) : ℝ≥0∞) : ℝ≥0∞) ^ N) * porMass X (R / (L : ℝ) ^ N) := by
            exact porMass_iter hpor hα₀ R hLpos hνL N hvalid
      _ ≤ ((((L - 1 : ℕ) : ℝ≥0∞) : ℝ≥0∞) ^ N) *
            ENNReal.ofReal (R / (L : ℝ) ^ N) := by
            exact mul_le_mul_of_nonneg_left
              (porMass_le_ofReal X (R / (L : ℝ) ^ N) hδNpos) zero_le
      _ = ENNReal.ofReal ((((L - 1 : ℕ) : ℝ) ^ N) * (R / (L : ℝ) ^ N)) := by
            have hpow := enn_natCast_pow (L - 1) N
            rw [hpow]
            rw [← ENNReal.ofReal_natCast ((L - 1) ^ N : ℕ)]
            rw [ENNReal.ofReal_mul' hδNpos]
            congr 1
            rw [Nat.cast_pow]
      _ ≤ ENNReal.ofReal (R * (α₀ / R) ^ γ) := by
            exact ENNReal.ofReal_le_ofReal hboundReal
  calc
    MeasureTheory.volume (X ∩ Set.Icc a b) ≤ ENNReal.ofReal (R * (α₀ / R) ^ γ) := hvol
    _ = ENNReal.ofReal ((b - a) * ((α₀ / (b - a)) ^ γ)) := by
          simp only [R]

end Commons.Measure.Real
