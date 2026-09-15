import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Order.CompletePartialOrder
import Submission.Commons.Measure.Real.exists_cell_Icc

namespace Commons.Measure.EuclideanSpace

open MeasureTheory Set Metric
open scoped ENNReal BigOperators Topology RealInnerProductSpace

variable {d : ℕ}

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

/-- The real power inequality used in the conclusion. -/
private lemma power_bound (L : ℕ) (hL : 2 ≤ L) (N : ℕ) (R α₀ : ℝ) (hR : 0 < R)
    (hα₀ : 0 < α₀) (hN : R / (L : ℝ) ^ N ≤ α₀) :
    (((L - 1 : ℕ) : ℝ) ^ N) * (R / (L : ℝ) ^ N) ≤
      R * (α₀ / R) ^ (Real.log ((L : ℝ) / ((L : ℝ) - 1)) / Real.log (L : ℝ)) := by
  have hLposR : (0 : ℝ) < (L : ℝ) := by
    have : (0 : ℕ) < L := by omega
    exact_mod_cast this
  have hLne : (L : ℝ) ≠ 0 := ne_of_gt hLposR
  have hL1 : (1 : ℝ) < (L : ℝ) := by
    have : (1 : ℕ) < L := by omega
    exact_mod_cast this
  have hLm1 : ((L - 1 : ℕ) : ℝ) = (L : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega : (1 : ℕ) ≤ L)]
    norm_num
  let m1 : ℝ := (L : ℝ) - 1
  have hm1pos : 0 < m1 := by
    dsimp [m1]
    have : (1 : ℝ) ≤ (L : ℝ) := le_of_lt hL1
    linarith
  let γ : ℝ := Real.log ((L : ℝ) / m1) / Real.log (L : ℝ)
  let q : ℝ := m1 / (L : ℝ)
  let s : ℝ := α₀ / R
  have hs : 0 < s := div_pos hα₀ hR
  have hq : 0 < q := by
    dsimp [q]
    exact div_pos hm1pos hLposR
  have hlogL : 0 < Real.log (L : ℝ) := Real.log_pos hL1
  have hγpos : 0 < γ := by
    dsimp [γ]
    have h1 : 1 < (L : ℝ) / m1 := by
      dsimp [m1]
      rw [lt_div_iff₀]
      · nlinarith
      · have : (0 : ℝ) ≤ (L : ℝ) - 1 := by linarith
        linarith
    exact div_pos (Real.log_pos h1) hlogL
  have hgl : Real.log ((L : ℝ) / m1) = Real.log (L : ℝ) - Real.log m1 := by
    rw [Real.log_div hLne (ne_of_gt hm1pos)]
  have hγL : γ * Real.log (L : ℝ) = Real.log ((L : ℝ) / m1) := by
    dsimp [γ]
    field_simp [ne_of_gt hlogL]
  have hlogq : Real.log q = -(γ * Real.log (L : ℝ)) := by
    calc
      Real.log q = Real.log m1 - Real.log (L : ℝ) := by
        dsimp [q]
        exact Real.log_div (ne_of_gt hm1pos) hLne
      _ = -(Real.log (L : ℝ) - Real.log m1) := by ring
      _ = -(Real.log ((L : ℝ) / m1)) := by rw [hgl]
      _ = -(γ * Real.log (L : ℝ)) := by rw [hγL]
  have hLN : 0 < (L : ℝ) ^ N := pow_pos hLposR N
  have h1s : ((L : ℝ) ^ N)⁻¹ ≤ s := by
    dsimp [s]
    rw [le_div_iff₀ hR]
    have hNrw : R * ((L : ℝ) ^ N)⁻¹ ≤ α₀ := by
      simpa [div_eq_mul_inv] using hN
    simpa [mul_comm] using hNrw
  have hlogs : Real.log (((L : ℝ) ^ N)⁻¹) ≤ Real.log s := by
    exact Real.log_le_log (inv_pos.mpr hLN) h1s
  have hlogLN : Real.log (((L : ℝ) ^ N)⁻¹) = -((N : ℝ) * Real.log (L : ℝ)) := by
    rw [Real.log_inv]
    rw [Real.log_pow]
  have hlogineq : -((N : ℝ) * Real.log (L : ℝ)) ≤ Real.log s := by
    simpa [hlogLN] using hlogs
  have hineq : (N : ℝ) * Real.log q ≤ γ * Real.log s := by
    have h₂ : γ * (-((N : ℝ) * Real.log (L : ℝ))) ≤ γ * Real.log s :=
      mul_le_mul_of_nonneg_left hlogineq (le_of_lt hγpos)
    calc
      (N : ℝ) * Real.log q = (N : ℝ) * (-(γ * Real.log (L : ℝ))) := by rw [hlogq]
      _ = γ * (-((N : ℝ) * Real.log (L : ℝ))) := by ring
      _ ≤ γ * Real.log s := h₂
  have hqpow : (((L - 1 : ℕ) : ℝ) ^ N) / ((L : ℝ) ^ N) ≤ (α₀ / R) ^ γ := by
    calc
      (((L - 1 : ℕ) : ℝ) ^ N) / ((L : ℝ) ^ N)
          = q ^ N := by
            rw [hLm1]
            rw [← div_pow]
      _ ≤ s ^ γ := by
            calc
              q ^ N = Real.exp ((N : ℝ) * Real.log q) := by
                rw [← Real.rpow_natCast q N]
                rw [Real.rpow_def_of_pos hq]
                ring_nf
              _ ≤ Real.exp (γ * Real.log s) := Real.exp_le_exp.mpr hineq
              _ = s ^ γ := by
                rw [Real.rpow_def_of_pos hs]
                congr 1
                ring
      _ = (α₀ / R) ^ γ := by rfl
  calc
    (((L - 1 : ℕ) : ℝ) ^ N) * (R / (L : ℝ) ^ N)
        = R * ((((L - 1 : ℕ) : ℝ) ^ N) / ((L : ℝ) ^ N)) := by
          field_simp [hR.ne', (ne_of_gt hLN)]
    _ ≤ R * (α₀ / R) ^ γ := mul_le_mul_of_nonneg_left hqpow (le_of_lt hR)

/-- A natural number power inside `ℝ≥0∞`: `(n : ℝ≥0∞)^N = ((n^N) : ℝ≥0∞)`. -/
private lemma enn_natCast_pow (n N : ℕ) :
    (((n : ℝ≥0∞) : ℝ≥0∞) ^ N) = (((n ^ N : ℕ) : ℝ≥0∞) : ℝ≥0∞) := by
  induction N with
  | zero => simp
  | succ N ih =>
      rw [pow_succ, ih]
      rw [pow_succ]
      simp

/-- One-dimensional regularity of porous sets with the exponent made explicit in terms of an
`L ≥ 2` with `L⁻¹ ≤ ν`. -/
private theorem porous_interval_bound_explicit {ν α₀ α₁ : ℝ} (hν : 0 < ν) {L : ℕ}
    (hL : 2 ≤ L) (hνL : ((L : ℝ))⁻¹ ≤ ν) (hα₀ : 0 < α₀) {X : Set ℝ} (hX : MeasurableSet X)
    (hpor : ∀ (y : ℝ), ∀ R ∈ Set.Ioo α₀ α₁, ∃ x ∈ Metric.closedBall y (R / 2),
      Metric.closedBall x (ν * R) ∩ X = ∅)
    (a b : ℝ) (hR : b - a ∈ Set.Ioo α₀ α₁) :
    (MeasureTheory.volume (X ∩ Set.Icc a b) : ENNReal) ≤
      ENNReal.ofReal ((b - a) * ((α₀ / (b - a)) ^
        (Real.log ((L : ℝ) / ((L : ℝ) - 1)) / Real.log (L : ℝ)))) := by
  have hLpos : 0 < L := by omega
  have hLposℝ : (0 : ℝ) < (L : ℝ) := by exact_mod_cast hLpos
  have hL1 : (1 : ℝ) < (L : ℝ) := by
    have : (1 : ℕ) < L := by omega
    exact_mod_cast this
  let γ : ℝ := Real.log ((L : ℝ) / ((L : ℝ) - 1)) / Real.log (L : ℝ)
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
    exact power_bound L hL N R α₀ hRpos hα₀ hN
  have hb : b = a + R := by dsimp [R]; ring
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
  have hfin : (b - a) * ((α₀ / (b - a)) ^
        (Real.log ((L : ℝ) / ((L : ℝ) - 1)) / Real.log (L : ℝ))) = R * (α₀ / R) ^ γ := by
    dsimp only [R, γ]
  rw [hfin]
  exact hvol

/-- Distance between two points on an affine line `t ↦ p + t • v`. -/
private lemma dist_add_smul (p v : EuclideanSpace ℝ (Fin d)) (a b : ℝ) :
    dist (p + a • v) (p + b • v) = ‖v‖ * |a - b| := by
  rw [dist_eq_norm]
  calc
    ‖(p + a • v) - (p + b • v)‖ = ‖(a - b) • v‖ := by
      congr 1
      calc
        (p + a • v) - (p + b • v) = a • v - b • v := by abel
        _ = (a - b) • v := by rw [sub_smul]
    _ = ‖a - b‖ * ‖v‖ := by rw [norm_smul]
    _ = |a - b| * ‖v‖ := by rw [Real.norm_eq_abs]
    _ = ‖v‖ * |a - b| := by rw [mul_comm]

private lemma pullback_dist {p v : EuclideanSpace ℝ (Fin d)} (hv : ‖v‖ = 1) (s t : ℝ) :
    dist (p + s • v) (p + t • v) = |s - t| := by
  rw [dist_add_smul, hv]; simp

/-- The segment between `p + a•v` and `p + b•v` (with `a ≤ b`) is contained in the image of
`[a,b]` under `t ↦ p + t • v`. -/
private lemma mem_segment_affine {p v : EuclideanSpace ℝ (Fin d)} {a b : ℝ} (hab : a ≤ b)
    {x' : EuclideanSpace ℝ (Fin d)} (hx' : x' ∈ segment ℝ (p + a • v) (p + b • v)) :
    ∃ t : ℝ, t ∈ Set.Icc a b ∧ x' = p + t • v := by
  rw [segment_eq_image] at hx'
  rcases hx' with ⟨θ, hθ, hEq⟩
  refine ⟨(1 - θ) * a + θ * b, ?_, ?_⟩
  · constructor
    · have hpos : 0 ≤ θ * (b - a) := mul_nonneg hθ.1 (sub_nonneg.mpr hab)
      nlinarith
    · have hpos : 0 ≤ (1 - θ) * (b - a) := mul_nonneg (sub_nonneg.mpr hθ.2) (sub_nonneg.mpr hab)
      nlinarith
  · rw [← hEq]
    module

/-- If `Y` is porous on lines, then the pullback of `Y` by a unit-speed affine line
`t ↦ p + t • v` is interval-porous in `ℝ` with the same parameters. -/
private lemma pullback_porous_of_unitSpeed {ν α₀ α₁ : ℝ} {Y : Set (EuclideanSpace ℝ (Fin d))}
    (p v : EuclideanSpace ℝ (Fin d)) (hv : ‖v‖ = 1) (hα₀ : 0 < α₀)
    (hY : ∀ R ∈ Set.Ioo α₀ α₁, ∀ y₁ y₂ : EuclideanSpace ℝ (Fin d), dist y₁ y₂ = R →
      ∃ x ∈ segment ℝ y₁ y₂, closedBall x (ν * R) ∩ Y = ∅) :
    ∀ y : ℝ, ∀ R ∈ Set.Ioo α₀ α₁, ∃ x ∈ closedBall y (R / 2),
      closedBall x (ν * R) ∩ ((fun t : ℝ => p + t • v) ⁻¹' Y) = ∅ := by
  intro y R hR
  have hRpos : 0 < R := lt_trans hα₀ (Set.mem_Ioo.mp hR).1
  have hab : y - R / 2 ≤ y + R / 2 := by linarith
  have hd : dist (p + (y - R / 2) • v) (p + (y + R / 2) • v) = R := by
    rw [pullback_dist hv]
    rw [abs_of_neg (by linarith)]
    ring
  rcases hY R hR (p + (y - R / 2) • v) (p + (y + R / 2) • v) hd with ⟨x', hx', hball⟩
  rcases mem_segment_affine hab hx' with ⟨x, hxI, hxeq⟩
  refine ⟨x, ?_, ?_⟩
  · rw [Metric.mem_closedBall, Real.dist_eq, abs_le]
    rw [Set.mem_Icc] at hxI
    constructor <;> linarith
  · apply Set.subset_empty_iff.mp
    intro u hu
    have hmem : p + u • v ∈ closedBall x' (ν * R) := by
      rw [Metric.mem_closedBall]
      have hu1 : dist (p + u • v) (p + x • v) ≤ ν * R := by
        have hux : dist u x ≤ ν * R := Metric.mem_closedBall.mp hu.1
        calc
          dist (p + u • v) (p + x • v) = |u - x| := by rw [pullback_dist hv]
          _ = dist u x := by rw [Real.dist_eq]
          _ ≤ ν * R := hux
      rwa [hxeq]
    have hc : p + u • v ∈ closedBall x' (ν * R) ∩ Y := ⟨hmem, hu.2⟩
    simpa [hball] using hc

/-- The parameter set of a unit-speed line meeting an annulus is contained in an interval of
length `2b` centred at the parameter of the closest point of the line to the origin. -/
private lemma pullback_annulus_subset (p v : EuclideanSpace ℝ (Fin d)) (hv : ‖v‖ = 1)
    {a b : ℝ} (hb : 0 ≤ b) :
    (fun t : ℝ => p + t • v) ⁻¹' {x : EuclideanSpace ℝ (Fin d) | a ≤ ‖x‖ ∧ ‖x‖ ≤ b} ⊆
      Set.Icc (-(⟪p, v⟫) - b) (-(⟪p, v⟫) + b) := by
  intro t ht
  rw [Set.mem_preimage] at ht
  have h1 : ‖p + t • v‖ ^ 2 ≤ b ^ 2 := by
    nlinarith [norm_nonneg (p + t • v), ht.2, hb]
  have hexp : ‖p + t • v‖ ^ 2 = (t + ⟪p, v⟫) ^ 2 + (‖p‖ ^ 2 - ⟪p, v⟫ ^ 2) := by
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
private lemma Icc_subset_iUnion_Icc {c d L : ℝ} (hd : 0 < d) (hL : 0 < L) {M : ℕ}
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
  have hsub : t ∈ Set.Icc (c - d) (c - d + (M : ℝ) * L) := ⟨ht.1, by linarith [ht.2, hM]⟩
  rcases Commons.Measure.Real.exists_cell_Icc M hMpos hsub with ⟨k, hkM, hk⟩
  refine Set.mem_iUnion.mpr ⟨⟨k, hkM⟩, ?_⟩
  simpa using hk

/-- A measurable set `Z ⊆ ℝᵈ` which is `ν`-porous on lines from scales `α₀` to `α₁` and is
contained in the closed annulus `{a ≤ ‖x‖ ≤ b}` meets every unit-speed line in one-dimensional
measure at most `C·b·(α₀ / min(α₁/2, 2b))^γ`.

The exponent `γ` and the constant `C` depend only on `ν` and `d` (uniformly in `α₀, α₁, a, b, Z`).
Proof idea: let `L := min (α₁/2) (2b)`.  If `L ≤ α₀` use the trivial bound `2b ≤ C·b` (the
factor `(α₀/L)^γ` is then `≥ 1`).  If `α₀ < L`, the intersection of the line with the ball of
radius `b` has length `≤ 2b`, so it splits into at most `2b/L + 1` segments of length `L`; on
each segment the one-dimensional regularity of `ν`-porous sets gives the bound `L·(α₀/L)^γ`;
summing over the `≤ 3b/L` segments gives `3b(α₀/L)^γ`. -/
theorem porous_line_measure_annulus (d : ℕ) {ν : ℝ} (hν : 0 < ν) :
    ∃ γ C : ℝ, 0 < γ ∧ 0 < C ∧
      ∀ (α₀ α₁ a b : ℝ) (Z : Set (EuclideanSpace ℝ (Fin d))),
        0 < α₀ → 0 < α₁ → 0 < a → a ≤ b → MeasurableSet Z →
        (∀ R ∈ Set.Ioo α₀ α₁, ∀ y₁ y₂ : EuclideanSpace ℝ (Fin d),
            dist y₁ y₂ = R → ∃ x ∈ segment ℝ y₁ y₂, closedBall x (ν * R) ∩ Z = ∅) →
        Z ⊆ {x : EuclideanSpace ℝ (Fin d) | a ≤ ‖x‖ ∧ ‖x‖ ≤ b} →
        ∀ (p v : EuclideanSpace ℝ (Fin d)), ‖v‖ = 1 →
          (volume ((fun t : ℝ => p + t • v) ⁻¹' Z) : ℝ≥0∞) ≤
            ENNReal.ofReal (C * b * (α₀ / min (α₁ / 2) (2 * b)) ^ γ) := by
  obtain ⟨L, hL2, hνL⟩ : ∃ L : ℕ, 2 ≤ L ∧ ((L : ℝ))⁻¹ ≤ ν := by
    by_cases h : (1 / 2 : ℝ) ≤ ν
    · exact ⟨2, by norm_num, by norm_num; linarith⟩
    · push_neg at h
      obtain ⟨L, hL⟩ := exists_nat_ge (ν⁻¹)
      have h2inv : (2 : ℝ) ≤ ν⁻¹ := by
        have hνne : ν ≠ 0 := ne_of_gt hν
        field_simp [hνne]
        nlinarith
      have hL2' : (2 : ℝ) ≤ (L : ℝ) := le_trans h2inv hL
      refine ⟨L, ?_, ?_⟩
      · exact_mod_cast hL2'
      · have hLpos : (0 : ℝ) < (L : ℝ) := lt_of_lt_of_le (by norm_num) hL2'
        have hνinvpos : (0 : ℝ) < ν⁻¹ := inv_pos.mpr hν
        have := (inv_le_inv₀ hLpos hνinvpos).mpr hL
        simpa using this
  let γ : ℝ := Real.log ((L : ℝ) / ((L : ℝ) - 1)) / Real.log (L : ℝ)
  have hL1 : (1 : ℝ) < (L : ℝ) := by
    have : (1 : ℕ) < L := by omega
    exact_mod_cast this
  have hγpos : 0 < γ := by
    dsimp only [γ]
    have hfrac : 1 < (L : ℝ) / ((L : ℝ) - 1) := by
      rw [lt_div_iff₀ (by linarith : (0 : ℝ) < (L : ℝ) - 1)]
      linarith
    exact div_pos (Real.log_pos hfrac) (Real.log_pos hL1)
  refine ⟨γ, 4, hγpos, by norm_num, ?_⟩
  intro α₀ α₁ a b Z hα₀ hα₁ ha hab hZmeas hpor hZsub p v hv
  have hbpos : 0 < b := lt_of_lt_of_le ha hab
  let Lc : ℝ := min (α₁ / 2) (2 * b)
  have hLcpos : 0 < Lc := by
    dsimp only [Lc]
    exact lt_min (by linarith) (by linarith)
  have hcont : Continuous (fun t : ℝ => p + t • v) :=
    continuous_const.add (continuous_id.smul continuous_const)
  have hXmeas : MeasurableSet ((fun t : ℝ => p + t • v) ⁻¹' Z) :=
    hZmeas.preimage hcont.measurable
  have hsub : (fun t : ℝ => p + t • v) ⁻¹' Z ⊆
      Set.Icc (-(⟪p, v⟫) - b) (-(⟪p, v⟫) + b) :=
    fun t ht => pullback_annulus_subset p v hv (le_of_lt hbpos) (hZsub ht)
  have hvol2b : (volume ((fun t : ℝ => p + t • v) ⁻¹' Z) : ℝ≥0∞) ≤
      ENNReal.ofReal (2 * b) := by
    calc volume ((fun t : ℝ => p + t • v) ⁻¹' Z)
        ≤ volume (Set.Icc (-(⟪p, v⟫) - b) (-(⟪p, v⟫) + b)) := measure_mono hsub
      _ = ENNReal.ofReal ((-(⟪p, v⟫) + b) - (-(⟪p, v⟫) - b)) := by rw [Real.volume_Icc]
      _ = ENNReal.ofReal (2 * b) := by congr 1; ring
  have hmain : (volume ((fun t : ℝ => p + t • v) ⁻¹' Z) : ℝ≥0∞) ≤
      ENNReal.ofReal (4 * b * (α₀ / Lc) ^ γ) := by
    by_cases hcase : Lc ≤ α₀
    · have h1 : (1 : ℝ) ≤ α₀ / Lc := (one_le_div hLcpos).mpr hcase
      have h2 : (1 : ℝ) ≤ (α₀ / Lc) ^ γ := Real.one_le_rpow h1 (le_of_lt hγpos)
      refine le_trans hvol2b (ENNReal.ofReal_le_ofReal ?_)
      calc (2 : ℝ) * b ≤ (4 * b) * 1 := by linarith
        _ ≤ (4 * b) * (α₀ / Lc) ^ γ := mul_le_mul_of_nonneg_left h2 (by positivity)
        _ = 4 * b * (α₀ / Lc) ^ γ := by ring
    · push_neg at hcase
      have hLc_lt_α₁ : Lc < α₁ := lt_of_le_of_lt (min_le_left _ _) (by linarith)
      have hmem : Lc ∈ Set.Ioo α₀ α₁ := ⟨hcase, hLc_lt_α₁⟩
      set M : ℕ := ⌈2 * b / Lc⌉₊ with hMdef
      have hM2 : 2 * b ≤ (M : ℝ) * Lc := by
        have h := Nat.le_ceil (2 * b / Lc)
        rw [div_le_iff₀ hLcpos] at h
        linarith [h]
      have hM3 : (M : ℝ) * Lc ≤ 4 * b := by
        have h := Nat.ceil_lt_add_one (show (0 : ℝ) ≤ 2 * b / Lc by positivity)
        have h2 : (M : ℝ) * Lc < (2 * b / Lc + 1) * Lc := by
          rw [hMdef]
          exact mul_lt_mul_of_pos_right h hLcpos
        have hexp : (2 * b / Lc + 1) * Lc = 2 * b + Lc := by field_simp
        have hLcle : Lc ≤ 2 * b := min_le_right _ _
        linarith
      have hseg : ∀ j : Fin M, volume ((fun t : ℝ => p + t • v) ⁻¹' Z ∩
          Set.Icc (-(⟪p, v⟫) - b + (j : ℝ) * Lc)
            (-(⟪p, v⟫) - b + ((j : ℝ) + 1) * Lc)) ≤
          ENNReal.ofReal (Lc * (α₀ / Lc) ^ γ) := by
        intro j
        have hdiff : (-(⟪p, v⟫) - b + ((j : ℝ) + 1) * Lc)
            - (-(⟪p, v⟫) - b + (j : ℝ) * Lc) = Lc := by ring
        have h1 := porous_interval_bound_explicit (ν := ν) hν hL2 hνL hα₀ hXmeas
          (pullback_porous_of_unitSpeed p v hv hα₀ hpor)
          (-(⟪p, v⟫) - b + (j : ℝ) * Lc) (-(⟪p, v⟫) - b + ((j : ℝ) + 1) * Lc)
          (by rw [hdiff]; exact hmem)
        simpa [hdiff] using h1
      have hcover : Set.Icc (-(⟪p, v⟫) - b) (-(⟪p, v⟫) + b) ⊆
          ⋃ j : Fin M, Set.Icc (-(⟪p, v⟫) - b + (j : ℝ) * Lc)
            (-(⟪p, v⟫) - b + ((j : ℝ) + 1) * Lc) :=
        Icc_subset_iUnion_Icc hbpos hLcpos hM2
      calc (volume ((fun t : ℝ => p + t • v) ⁻¹' Z) : ℝ≥0∞)
          = volume ((fun t : ℝ => p + t • v) ⁻¹' Z ∩
              Set.Icc (-(⟪p, v⟫) - b) (-(⟪p, v⟫) + b)) := by
              rw [Set.inter_eq_left.mpr hsub]
        _ ≤ volume (⋃ j : Fin M, (fun t : ℝ => p + t • v) ⁻¹' Z ∩
              Set.Icc (-(⟪p, v⟫) - b + (j : ℝ) * Lc)
                (-(⟪p, v⟫) - b + ((j : ℝ) + 1) * Lc)) := by
              refine measure_mono (fun t ht => ?_)
              rcases Set.mem_iUnion.mp (hcover ht.2) with ⟨j, hj⟩
              exact Set.mem_iUnion.mpr ⟨j, ⟨ht.1, hj⟩⟩
        _ ≤ ∑ j : Fin M, volume ((fun t : ℝ => p + t • v) ⁻¹' Z ∩
              Set.Icc (-(⟪p, v⟫) - b + (j : ℝ) * Lc)
                (-(⟪p, v⟫) - b + ((j : ℝ) + 1) * Lc)) :=
              measure_iUnion_fintype_le _ _
        _ ≤ ∑ _j : Fin M, ENNReal.ofReal (Lc * (α₀ / Lc) ^ γ) :=
              Finset.sum_le_sum (fun j _ => hseg j)
        _ = (M : ℝ≥0∞) * ENNReal.ofReal (Lc * (α₀ / Lc) ^ γ) := by
              rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        _ = ENNReal.ofReal ((M : ℝ) * (Lc * (α₀ / Lc) ^ γ)) := by
              rw [← ENNReal.ofReal_natCast M, ← ENNReal.ofReal_mul (by positivity)]
        _ ≤ ENNReal.ofReal (4 * b * (α₀ / Lc) ^ γ) := by
              refine ENNReal.ofReal_le_ofReal ?_
              have hpow : 0 ≤ (α₀ / Lc) ^ γ := Real.rpow_nonneg (by positivity) γ
              have : (M : ℝ) * (Lc * (α₀ / Lc) ^ γ) = ((M : ℝ) * Lc) * (α₀ / Lc) ^ γ := by
                ring
              rw [this]
              exact mul_le_mul_of_nonneg_right hM3 hpow
  have hfin : 4 * b * (α₀ / min (α₁ / 2) (2 * b)) ^ γ = 4 * b * (α₀ / Lc) ^ γ := by
    dsimp only [Lc]
  rw [hfin]
  exact hmain

end

end Commons.Measure.EuclideanSpace