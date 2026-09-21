import Mathlib
import Submission.Work.OddCurve.LowSlope.RadialLogDefs
import Submission.Work.OddCurve.LowSlope.radInv_contDiffOn

/-!
# The normalised solution of the two-power radial system

Given the deviations `A`, `B` of the data from the ball's data `(2,0)`, this file constructs the
radial functions `R`, `r` of the two-power system

  `R^m + r^m = 2 + A`,   `R^k - r^k = B`,     `m = 2n+2`, `k = 2n+1`,

by the normalised first `m`-th power `x = R^m/(2+A)`: setting `θ = k/m` and `u = 2 + A`, the
second equation is equivalent to the scalar equation `radH n x = B/u^θ`, solved by
`x = radInv n (B/u^θ)`.  One then sets `R = (x u)^{1/m}`, `r = ((1-x) u)^{1/m}`.

Under the standing hypotheses `|A| ≤ σ ≤ 1/2`, `|B| ≤ σ` on `[0,π/2]` the construction gives
`x ∈ (1/4,3/4)`, hence the box bounds `3/8 ≤ R^m, r^m ≤ 15/8` and `3/2 ≤ R^m + r^m ≤ 5/2`.
-/

noncomputable section

open Set Filter
open scoped Topology ContDiff

namespace Work.OddCurve.LowSlope

/-! ## Elementary `rpow` normalisations -/

lemma rpow_nat_pow_quarter (b : ℝ) (hb : 0 ≤ b) :
    (b ^ (3 : ℕ)) ^ (1 / 4 : ℝ) = b ^ (3 / 4 : ℝ) := by
  rw [← Real.rpow_natCast b 3, ← Real.rpow_mul hb]
  congr 1
  norm_num

lemma pow_four_rpow_quarter (b : ℝ) (hb : 0 ≤ b) : (b ^ 4) ^ (1 / 4 : ℝ) = b := by
  rw [← Real.rpow_natCast b 4, ← Real.rpow_mul hb]
  have : ((4 : ℕ) : ℝ) * (1 / 4 : ℝ) = 1 := by norm_num
  rw [this, Real.rpow_one]

lemma le_rpow_quarter {a q : ℝ} (ha : 0 ≤ a) (hq : a ^ 4 ≤ q) : a ≤ q ^ (1 / 4 : ℝ) := by
  have h1 : (a ^ 4) ^ (1 / 4 : ℝ) ≤ q ^ (1 / 4 : ℝ) :=
    Real.rpow_le_rpow (by positivity) hq (by norm_num)
  rwa [pow_four_rpow_quarter a ha] at h1

lemma rpow_quarter_le {q b : ℝ} (hq0 : 0 ≤ q) (hb : 0 ≤ b) (hq : q ≤ b ^ 4) :
    q ^ (1 / 4 : ℝ) ≤ b := by
  have h1 : q ^ (1 / 4 : ℝ) ≤ (b ^ 4) ^ (1 / 4 : ℝ) :=
    Real.rpow_le_rpow hq0 hq (by norm_num)
  rwa [pow_four_rpow_quarter b hb] at h1

/-! ## The two numerical facts about `θ` -/

lemma eleven_tenths_le_three_halves_rpow (n : ℕ) (hn : 1 ≤ n) :
    (11 : ℝ) / 10 ≤ (3 / 2 : ℝ) ^ (radTh n) := by
  have hθ := radTh_ge_three_quarters n hn
  have h1 : (3 / 2 : ℝ) ^ (3 / 4 : ℝ) ≤ (3 / 2 : ℝ) ^ (radTh n) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num) hθ
  have h3 : (11 : ℝ) / 10 ≤ ((3 / 2 : ℝ) ^ (3 : ℕ)) ^ (1 / 4 : ℝ) :=
    le_rpow_quarter (by norm_num) (by norm_num)
  rw [rpow_nat_pow_quarter (3 / 2) (by norm_num)] at h3
  linarith

lemma three_fifths_le_rpow_diff (n : ℕ) (hn : 1 ≤ n) :
    (3 : ℝ) / 5 ≤ (9 / 8 : ℝ) ^ (radTh n) - (3 / 8 : ℝ) ^ (radTh n) := by
  have hθ := radTh_ge_three_quarters n hn
  have h1 : (9 / 8 : ℝ) ^ (3 / 4 : ℝ) ≤ (9 / 8 : ℝ) ^ (radTh n) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num) hθ
  have h2 : (3 / 8 : ℝ) ^ (radTh n) ≤ (3 / 8 : ℝ) ^ (3 / 4 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_ge (by norm_num) (by norm_num) hθ
  have hlow : (109 : ℝ) / 100 ≤ (9 / 8 : ℝ) ^ (3 / 4 : ℝ) := by
    have h3 : (109 : ℝ) / 100 ≤ ((9 / 8 : ℝ) ^ (3 : ℕ)) ^ (1 / 4 : ℝ) :=
      le_rpow_quarter (by norm_num) (by norm_num)
    rwa [rpow_nat_pow_quarter (9 / 8) (by norm_num)] at h3
  have hup : (3 / 8 : ℝ) ^ (3 / 4 : ℝ) ≤ (12 : ℝ) / 25 := by
    have h3 : ((3 / 8 : ℝ) ^ (3 : ℕ)) ^ (1 / 4 : ℝ) ≤ (12 : ℝ) / 25 :=
      rpow_quarter_le (by norm_num) (by norm_num) (by norm_num)
    rwa [rpow_nat_pow_quarter (3 / 8) (by norm_num)] at h3
  linarith

/-- `radH n (3/4) ≥ (3/5)/(3/2)^θ`. -/
lemma solH_three_quarters (n : ℕ) (hn : 1 ≤ n) :
    (3 : ℝ) / 5 / (3 / 2 : ℝ) ^ (radTh n) ≤ radH n (3 / 4) := by
  have h := three_fifths_le_rpow_diff n hn
  have hbase : (0 : ℝ) < (3 / 2 : ℝ) ^ (radTh n) := Real.rpow_pos_of_pos (by norm_num) _
  have e1 : ((9 / 8 : ℝ) / (3 / 2)) ^ (radTh n) =
      (9 / 8 : ℝ) ^ (radTh n) / (3 / 2 : ℝ) ^ (radTh n) :=
    Real.div_rpow (by norm_num) (by norm_num) _
  have e2 : ((3 / 8 : ℝ) / (3 / 2)) ^ (radTh n) =
      (3 / 8 : ℝ) ^ (radTh n) / (3 / 2 : ℝ) ^ (radTh n) :=
    Real.div_rpow (by norm_num) (by norm_num) _
  have hkey : radH n (3 / 4) = ((9 / 8 : ℝ) ^ (radTh n) - (3 / 8 : ℝ) ^ (radTh n))
      / (3 / 2 : ℝ) ^ (radTh n) := by
    have h34 : (3 / 4 : ℝ) = (9 / 8) / (3 / 2) := by norm_num
    have h14 : (1 : ℝ) - (9 / 8) / (3 / 2) = (3 / 8) / (3 / 2) := by norm_num
    rw [radH_apply, h34, h14, e1, e2]
    ring
  rw [hkey, div_le_div_iff_of_pos_right hbase]
  linarith

/-! ## The construction -/

/-- The perturbed data `u = 2 + A`. -/
def solU (A : ℝ → ℝ) (α : ℝ) : ℝ := 2 + A α

/-- The normalised second datum `w = B / u^θ`. -/
def solW (n : ℕ) (A B : ℝ → ℝ) (α : ℝ) : ℝ := B α / (solU A α) ^ (radTh n)

/-- The normalised first `m`-th power `x`, solving `radH n x = w`. -/
def solX (n : ℕ) (A B : ℝ → ℝ) (α : ℝ) : ℝ := radInv n (solW n A B α)

/-- The upper radial function `R = (x u)^{1/m}`. -/
def solR (n : ℕ) (A B : ℝ → ℝ) (α : ℝ) : ℝ :=
  (solX n A B α * solU A α) ^ (((2 * n + 2 : ℕ) : ℝ)⁻¹)

/-- The lower radial function `r = ((1-x) u)^{1/m}`. -/
def solr (n : ℕ) (A B : ℝ → ℝ) (α : ℝ) : ℝ :=
  ((1 - solX n A B α) * solU A α) ^ (((2 * n + 2 : ℕ) : ℝ)⁻¹)

@[simp] lemma solU_apply (A : ℝ → ℝ) (α : ℝ) : solU A α = 2 + A α := rfl

@[simp] lemma solW_apply (n : ℕ) (A B : ℝ → ℝ) (α : ℝ) :
    solW n A B α = B α / (2 + A α) ^ (radTh n) := rfl

@[simp] lemma solX_apply (n : ℕ) (A B : ℝ → ℝ) (α : ℝ) :
    solX n A B α = radInv n (solW n A B α) := rfl

@[simp] lemma solR_apply (n : ℕ) (A B : ℝ → ℝ) (α : ℝ) :
    solR n A B α = (solX n A B α * solU A α) ^ (((2 * n + 2 : ℕ) : ℝ)⁻¹) := rfl

@[simp] lemma solr_apply (n : ℕ) (A B : ℝ → ℝ) (α : ℝ) :
    solr n A B α = ((1 - solX n A B α) * solU A α) ^ (((2 * n + 2 : ℕ) : ℝ)⁻¹) := rfl

/-! ## Pointwise bounds on `[0, π/2]` -/

lemma solU_mem {A : ℝ → ℝ} {σ α : ℝ} (hσ' : σ ≤ 1 / 2)
    (hA : ∀ β ∈ Set.Icc (0 : ℝ) (Real.pi / 2), |A β| ≤ σ)
    (hα : α ∈ Set.Icc (0 : ℝ) (Real.pi / 2)) :
    (3 / 2 : ℝ) ≤ solU A α ∧ solU A α ≤ 5 / 2 := by
  have h := hA α hα
  have h1 : -(1 / 2 : ℝ) ≤ A α := by linarith [neg_le_of_abs_le h]
  have h2 : A α ≤ 1 / 2 := by linarith [le_of_abs_le h]
  rw [solU_apply]
  constructor <;> linarith

/-- `|w| ≤ (1/2)/(3/2)^θ` on `[0,π/2]`. -/
lemma solW_abs_le_half (n : ℕ) {A B : ℝ → ℝ} {σ α : ℝ} (hσ' : σ ≤ 1 / 2)
    (hA : ∀ β ∈ Set.Icc (0 : ℝ) (Real.pi / 2), |A β| ≤ σ)
    (hB : ∀ β ∈ Set.Icc (0 : ℝ) (Real.pi / 2), |B β| ≤ σ)
    (hα : α ∈ Set.Icc (0 : ℝ) (Real.pi / 2)) :
    |solW n A B α| ≤ (1 / 2 : ℝ) / (3 / 2 : ℝ) ^ (radTh n) := by
  have hu := solU_mem hσ' hA hα
  have hθp := radTh_pos n
  have hupos : (0 : ℝ) < solU A α := by linarith [hu.1]
  have hpowpos : (0 : ℝ) < (solU A α) ^ (radTh n) := Real.rpow_pos_of_pos hupos _
  have hpowpos' : (0 : ℝ) < (2 + A α) ^ (radTh n) := hpowpos
  have hbase : (0 : ℝ) < (3 / 2 : ℝ) ^ (radTh n) := Real.rpow_pos_of_pos (by norm_num) _
  have hpowge : (3 / 2 : ℝ) ^ (radTh n) ≤ (solU A α) ^ (radTh n) :=
    Real.rpow_le_rpow (by norm_num) hu.1 hθp.le
  have h3 : |B α| ≤ (1 / 2 : ℝ) := le_trans (hB α hα) hσ'
  have h1 : |B α| / (solU A α) ^ (radTh n) ≤ (1 / 2 : ℝ) / (solU A α) ^ (radTh n) :=
    div_le_div_of_nonneg_right h3 hpowpos.le
  have h2 : (1 / 2 : ℝ) / (solU A α) ^ (radTh n) ≤ (1 / 2 : ℝ) / (3 / 2 : ℝ) ^ (radTh n) := by
    have key : (1 : ℝ) / (solU A α) ^ (radTh n) ≤ 1 / (3 / 2 : ℝ) ^ (radTh n) :=
      one_div_le_one_div_of_le hbase hpowge
    calc (1 / 2 : ℝ) / (solU A α) ^ (radTh n)
        = (1 / 2 : ℝ) * (1 / (solU A α) ^ (radTh n)) := by rw [div_eq_mul_one_div]
      _ ≤ (1 / 2 : ℝ) * (1 / (3 / 2 : ℝ) ^ (radTh n)) :=
            mul_le_mul_of_nonneg_left key (by norm_num)
      _ = (1 / 2 : ℝ) / (3 / 2 : ℝ) ^ (radTh n) := by ring
  rw [solW_apply, abs_div]
  rw [abs_of_pos hpowpos']
  exact le_trans h1 h2

lemma solW_abs_le {n : ℕ} (hn : 1 ≤ n) {A B : ℝ → ℝ} {σ α : ℝ} (hσ' : σ ≤ 1 / 2)
    (hA : ∀ β ∈ Set.Icc (0 : ℝ) (Real.pi / 2), |A β| ≤ σ)
    (hB : ∀ β ∈ Set.Icc (0 : ℝ) (Real.pi / 2), |B β| ≤ σ)
    (hα : α ∈ Set.Icc (0 : ℝ) (Real.pi / 2)) :
    |solW n A B α| ≤ 3 / 5 := by
  have h := solW_abs_le_half n hσ' hA hB hα
  have hbase : (1 : ℝ) < (3 / 2 : ℝ) ^ (radTh n) := by
    have h := Real.rpow_lt_rpow (by norm_num : (0:ℝ) ≤ 1) (by norm_num : (1:ℝ) < 3/2) (radTh_pos n)
    rwa [Real.one_rpow] at h
  refine le_trans h ?_
  rw [div_le_iff₀ (by positivity : (0:ℝ) < (3/2:ℝ) ^ (radTh n))]
  have : (1 / 2 : ℝ) ≤ (3 / 5) * (3 / 2 : ℝ) ^ (radTh n) := by
    nlinarith [hbase]
  linarith

lemma solX_mem {n : ℕ} (hn : 1 ≤ n) {A B : ℝ → ℝ} {σ α : ℝ} (hσ' : σ ≤ 1 / 2)
    (hA : ∀ β ∈ Set.Icc (0 : ℝ) (Real.pi / 2), |A β| ≤ σ)
    (hB : ∀ β ∈ Set.Icc (0 : ℝ) (Real.pi / 2), |B β| ≤ σ)
    (hα : α ∈ Set.Icc (0 : ℝ) (Real.pi / 2)) :
    solX n A B α ∈ Set.Ioo (1 / 4 : ℝ) (3 / 4) := by
  have hwle := solW_abs_le_half n hσ' hA hB hα
  have hH := solH_three_quarters n hn
  have hbase : (0 : ℝ) < (3 / 2 : ℝ) ^ (radTh n) := Real.rpow_pos_of_pos (by norm_num) _
  have hlt : |solW n A B α| < radH n (3 / 4) := by
    have h52 : (1 / 2 : ℝ) / (3 / 2 : ℝ) ^ (radTh n) < (3 / 5 : ℝ) / (3 / 2 : ℝ) ^ (radTh n) := by
      apply div_lt_div_of_pos_right _ hbase
      norm_num
    exact lt_of_le_of_lt hwle (lt_of_lt_of_le h52 hH)
  have hH1 : radH n (3 / 4) ≤ 1 := by
    rw [radH_apply]
    have h1 : (3 / 4 : ℝ) ^ (radTh n) ≤ 1 :=
      Real.rpow_le_one (by norm_num) (by norm_num) (radTh_nonneg n)
    have h2 : (0 : ℝ) ≤ (1 / 4 : ℝ) ^ (radTh n) := Real.rpow_nonneg (by norm_num) _
    linarith
  have habs : |solW n A B α| < 1 := lt_of_lt_of_le hlt hH1
  have hmem : solX n A B α ∈ Set.Ioo (0 : ℝ) 1 := radInv_mem habs
  have hHx : radH n (solX n A B α) = solW n A B α := radH_radInv habs
  have hhalf : radH n (1 / 4 : ℝ) = -radH n (3 / 4) := by
    rw [radH_apply, radH_apply,
      show (1 : ℝ) - 1 / 4 = 3 / 4 by norm_num,
      show (1 : ℝ) - 3 / 4 = 1 / 4 by norm_num]
    ring
  have hmono := radH_strictMonoOn n
  have e1 : (1 / 4 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := ⟨by norm_num, by norm_num⟩
  have e2 : (3 / 4 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := ⟨by norm_num, by norm_num⟩
  have e3 : solX n A B α ∈ Set.Icc (0 : ℝ) 1 := ⟨le_of_lt hmem.1, le_of_lt hmem.2⟩
  constructor
  · -- 1/4 < x, since radH(1/4) < radH(x)
    have h1 : radH n (1 / 4 : ℝ) < radH n (solX n A B α) := by
      rw [hhalf, hHx]
      have := hlt
      rw [abs_lt] at this
      linarith [this.1]
    exact (StrictMonoOn.lt_iff_lt hmono e1 e3).mp h1
  · -- x < 3/4
    have h1 : radH n (solX n A B α) < radH n (3 / 4 : ℝ) := by
      rw [hHx]
      exact lt_of_le_of_lt (le_abs_self _) hlt
    exact (StrictMonoOn.lt_iff_lt hmono e3 e2).mp h1

lemma solX_pos {n : ℕ} (hn : 1 ≤ n) {A B : ℝ → ℝ} {σ α : ℝ} (hσ' : σ ≤ 1 / 2)
    (hA : ∀ β ∈ Set.Icc (0 : ℝ) (Real.pi / 2), |A β| ≤ σ)
    (hB : ∀ β ∈ Set.Icc (0 : ℝ) (Real.pi / 2), |B β| ≤ σ)
    (hα : α ∈ Set.Icc (0 : ℝ) (Real.pi / 2)) : 0 < solX n A B α :=
  lt_trans (by norm_num) (solX_mem hn hσ' hA hB hα).1

lemma solX_lt_one {n : ℕ} (hn : 1 ≤ n) {A B : ℝ → ℝ} {σ α : ℝ} (hσ' : σ ≤ 1 / 2)
    (hA : ∀ β ∈ Set.Icc (0 : ℝ) (Real.pi / 2), |A β| ≤ σ)
    (hB : ∀ β ∈ Set.Icc (0 : ℝ) (Real.pi / 2), |B β| ≤ σ)
    (hα : α ∈ Set.Icc (0 : ℝ) (Real.pi / 2)) : solX n A B α < 1 :=
  lt_trans (solX_mem hn hσ' hA hB hα).2 (by norm_num)

/-! ## The two equations of the system -/

lemma radTh_eq_mul_inv (n : ℕ) :
    radTh n = ((2 * n + 1 : ℕ) : ℝ) * (((2 * n + 2 : ℕ) : ℝ)⁻¹) := by
  rw [radTh, div_eq_mul_inv]

lemma rpow_inv_mul_eq (n k : ℕ) (x : ℝ) (hx : 0 ≤ x) :
    ((x ^ (((2 * n + 2 : ℕ) : ℝ)⁻¹)) ^ k)
      = x ^ (((k : ℝ)) * (((2 * n + 2 : ℕ) : ℝ)⁻¹)) := by
  rw [← Real.rpow_natCast _ k, ← Real.rpow_mul hx]
  congr 1
  ring

/-- `(R α)^m = x α · u α`. -/
lemma solR_pow_m (n : ℕ) {A B : ℝ → ℝ} {α : ℝ} (hx : 0 ≤ solX n A B α)
    (hu : 0 ≤ solU A α) :
    (solR n A B α) ^ (2 * n + 2) = solX n A B α * solU A α := by
  rw [solR_apply]
  exact Real.rpow_inv_natCast_pow (mul_nonneg hx hu) (by omega)

/-- `(r α)^m = (1 - x α) · u α`. -/
lemma solr_pow_m (n : ℕ) {A B : ℝ → ℝ} {α : ℝ} (hx : 0 ≤ 1 - solX n A B α)
    (hu : 0 ≤ solU A α) :
    (solr n A B α) ^ (2 * n + 2) = (1 - solX n A B α) * solU A α := by
  rw [solr_apply]
  exact Real.rpow_inv_natCast_pow (mul_nonneg hx hu) (by omega)

/-- `(R α)^k = (x α · u α)^θ`. -/
lemma solR_pow_k (n : ℕ) {A B : ℝ → ℝ} {α : ℝ} (hx : 0 ≤ solX n A B α)
    (hu : 0 ≤ solU A α) :
    (solR n A B α) ^ (2 * n + 1) = (solX n A B α * solU A α) ^ (radTh n) := by
  rw [solR_apply, rpow_inv_mul_eq n (2 * n + 1) _ (mul_nonneg hx hu), ← radTh_eq_mul_inv n]

/-- `(r α)^k = ((1 - x α) · u α)^θ`. -/
lemma solr_pow_k (n : ℕ) {A B : ℝ → ℝ} {α : ℝ} (hx : 0 ≤ 1 - solX n A B α)
    (hu : 0 ≤ solU A α) :
    (solr n A B α) ^ (2 * n + 1)
      = ((1 - solX n A B α) * solU A α) ^ (radTh n) := by
  rw [solr_apply, rpow_inv_mul_eq n (2 * n + 1) _ (mul_nonneg hx hu), ← radTh_eq_mul_inv n]

/-- **The two equations of the radial system**, under the standing pointwise hypotheses. -/
lemma sol_system (n : ℕ) {A B : ℝ → ℝ} {α : ℝ} (habs : |solW n A B α| < 1)
    (hu : 0 < solU A α) :
    (solR n A B α) ^ (2 * n + 2) + (solr n A B α) ^ (2 * n + 2) = 2 + A α ∧
      (solR n A B α) ^ (2 * n + 1) - (solr n A B α) ^ (2 * n + 1) = B α := by
  have hxpos : (0 : ℝ) < solX n A B α := (radInv_mem habs).1
  have hxlt : solX n A B α < 1 := (radInv_mem habs).2
  have hx0 : 0 ≤ solX n A B α := le_of_lt hxpos
  have hx1 : 0 ≤ 1 - solX n A B α := by linarith
  have hu0 : 0 ≤ solU A α := le_of_lt hu
  have hH : radH n (solX n A B α) = solW n A B α := radH_radInv habs
  have hupow : (0 : ℝ) < (solU A α) ^ (radTh n) := Real.rpow_pos_of_pos hu _
  constructor
  · rw [solR_pow_m n hx0 hu0, solr_pow_m n hx1 hu0]
    rw [solU_apply]; ring
  · rw [solR_pow_k n hx0 hu0, solr_pow_k n hx1 hu0, Real.mul_rpow hx0 hu0,
      Real.mul_rpow hx1 hu0]
    have hw : (solX n A B α) ^ (radTh n) - (1 - solX n A B α) ^ (radTh n)
        = B α / (solU A α) ^ (radTh n) := by
      have := hH
      rwa [radH_apply, solW_apply] at this
    have : (solU A α) ^ (radTh n)
        * ((solX n A B α) ^ (radTh n) - (1 - solX n A B α) ^ (radTh n)) = B α := by
      rw [hw]
      field_simp
    linarith [this]

/-- The system holds on a neighbourhood of every point of `[0,π/2]`. -/
lemma sol_system_eventually (n : ℕ) (hn : 1 ≤ n) {A B : ℝ → ℝ} {σ α : ℝ}
    (hσ' : σ ≤ 1 / 2)
    (hAc : ContDiffOn ℝ (((⊤ : ℕ∞) : WithTop ℕ∞)) A (Set.Ioo (-1) (Real.pi / 2 + 1)))
    (hBc : ContDiffOn ℝ (((⊤ : ℕ∞) : WithTop ℕ∞)) B (Set.Ioo (-1) (Real.pi / 2 + 1)))
    (hA : ∀ β ∈ Set.Icc (0 : ℝ) (Real.pi / 2), |A β| ≤ σ)
    (hB : ∀ β ∈ Set.Icc (0 : ℝ) (Real.pi / 2), |B β| ≤ σ)
    (hα : α ∈ Set.Icc (0 : ℝ) (Real.pi / 2)) :
    ∀ᶠ β in 𝓝 α,
      (solR n A B β) ^ (2 * n + 2) + (solr n A B β) ^ (2 * n + 2) = 2 + A β ∧
        (solR n A B β) ^ (2 * n + 1) - (solr n A B β) ^ (2 * n + 1) = B β := by
  have hmem : α ∈ Set.Ioo (-1 : ℝ) (Real.pi / 2 + 1) :=
    ⟨by linarith [hα.1], by linarith [hα.2, Real.pi_pos]⟩
  have hAcont : ContinuousAt A α :=
    (hAc.contDiffAt (Ioo_mem_nhds hmem.1 hmem.2)).continuousAt
  have hBcont : ContinuousAt B α :=
    (hBc.contDiffAt (Ioo_mem_nhds hmem.1 hmem.2)).continuousAt
  have huw := solW_abs_le hn hσ' hA hB hα
  have hupos : 0 < solU A α := by
    have h := solU_mem hσ' hA hα
    linarith [h.1]
  have hUcont : ContinuousAt (solU A) α :=
    (continuousAt_const : ContinuousAt (fun _ : ℝ => (2 : ℝ)) α).add hAcont
  have hpowcont : ContinuousAt (fun β => (solU A β) ^ (radTh n)) α :=
    hUcont.rpow_const (Or.inl (ne_of_gt hupos))
  have hWcont : ContinuousAt (solW n A B) α :=
    hBcont.div hpowcont (ne_of_gt (Real.rpow_pos_of_pos hupos _))
  have h1 : ∀ᶠ β in 𝓝 α, |solW n A B β| < 1 := by
    have habs : |solW n A B α| < 1 := by linarith
    have hmem1 : solW n A B α ∈ Set.Ioo (-1 : ℝ) 1 := abs_lt.mp habs
    have h2 : Set.Ioo (-1 : ℝ) 1 ∈ 𝓝 (solW n A B α) := IsOpen.mem_nhds isOpen_Ioo hmem1
    filter_upwards [hWcont.eventually h2] with β hβ
    exact abs_lt.mpr hβ
  have h2 : ∀ᶠ β in 𝓝 α, 0 < solU A β :=
    hUcont.eventually (IsOpen.mem_nhds isOpen_Ioi hupos)
  filter_upwards [h1, h2] with β hβ1 hβ2
  exact sol_system n hβ1 hβ2

/-! ## Smoothness -/

lemma solX_contDiffAt (n : ℕ) (hn : 1 ≤ n) {A B : ℝ → ℝ} {σ α : ℝ} (hσ' : σ ≤ 1 / 2)
    (hAc : ContDiffOn ℝ (((⊤ : ℕ∞) : WithTop ℕ∞)) A (Set.Ioo (-1) (Real.pi / 2 + 1)))
    (hBc : ContDiffOn ℝ (((⊤ : ℕ∞) : WithTop ℕ∞)) B (Set.Ioo (-1) (Real.pi / 2 + 1)))
    (hA : ∀ β ∈ Set.Icc (0 : ℝ) (Real.pi / 2), |A β| ≤ σ)
    (hB : ∀ β ∈ Set.Icc (0 : ℝ) (Real.pi / 2), |B β| ≤ σ)
    (hα : α ∈ Set.Icc (0 : ℝ) (Real.pi / 2)) :
    ContDiffAt ℝ (((⊤ : ℕ∞) : WithTop ℕ∞)) (solX n A B) α := by
  have hmem : α ∈ Set.Ioo (-1 : ℝ) (Real.pi / 2 + 1) :=
    ⟨by linarith [hα.1], by linarith [hα.2, Real.pi_pos]⟩
  have hAcd : ContDiffAt ℝ (((⊤ : ℕ∞) : WithTop ℕ∞)) A α :=
    hAc.contDiffAt (Ioo_mem_nhds hmem.1 hmem.2)
  have hBcd : ContDiffAt ℝ (((⊤ : ℕ∞) : WithTop ℕ∞)) B α :=
    hBc.contDiffAt (Ioo_mem_nhds hmem.1 hmem.2)
  have hupos : 0 < solU A α := by
    have h := solU_mem hσ' hA hα
    linarith [h.1]
  have hUcd : ContDiffAt ℝ (((⊤ : ℕ∞) : WithTop ℕ∞)) (solU A) α :=
    (contDiffAt_const (c := (2 : ℝ))).add hAcd
  have hpowcd : ContDiffAt ℝ (((⊤ : ℕ∞) : WithTop ℕ∞))
      (fun β => (solU A β) ^ (radTh n)) α :=
    hUcd.rpow (contDiffAt_const) (ne_of_gt hupos)
  have hWcd : ContDiffAt ℝ (((⊤ : ℕ∞) : WithTop ℕ∞)) (solW n A B) α :=
    hBcd.div hpowcd (ne_of_gt (Real.rpow_pos_of_pos hupos _))
  have hwabs : |solW n A B α| < 1 := by
    have h := solW_abs_le hn hσ' hA hB hα
    linarith
  have hcomp : ContDiffAt ℝ (((⊤ : ℕ∞) : WithTop ℕ∞))
      (fun β => radInv n (solW n A B β)) α :=
    (contDiffAt_radInv (n := n) hwabs).comp α hWcd
  exact hcomp

lemma solR_contDiffAt (n : ℕ) (hn : 1 ≤ n) {A B : ℝ → ℝ} {σ α : ℝ} (hσ' : σ ≤ 1 / 2)
    (hAc : ContDiffOn ℝ (((⊤ : ℕ∞) : WithTop ℕ∞)) A (Set.Ioo (-1) (Real.pi / 2 + 1)))
    (hBc : ContDiffOn ℝ (((⊤ : ℕ∞) : WithTop ℕ∞)) B (Set.Ioo (-1) (Real.pi / 2 + 1)))
    (hA : ∀ β ∈ Set.Icc (0 : ℝ) (Real.pi / 2), |A β| ≤ σ)
    (hB : ∀ β ∈ Set.Icc (0 : ℝ) (Real.pi / 2), |B β| ≤ σ)
    (hα : α ∈ Set.Icc (0 : ℝ) (Real.pi / 2)) :
    ContDiffAt ℝ (((⊤ : ℕ∞) : WithTop ℕ∞)) (solR n A B) α := by
  have hmem : α ∈ Set.Ioo (-1 : ℝ) (Real.pi / 2 + 1) :=
    ⟨by linarith [hα.1], by linarith [hα.2, Real.pi_pos]⟩
  have hX : ContDiffAt ℝ (((⊤ : ℕ∞) : WithTop ℕ∞)) (solX n A B) α :=
    solX_contDiffAt n hn hσ' hAc hBc hA hB hα
  have hU : ContDiffAt ℝ (((⊤ : ℕ∞) : WithTop ℕ∞)) (solU A) α :=
    (contDiffAt_const (c := (2 : ℝ))).add (hAc.contDiffAt (Ioo_mem_nhds hmem.1 hmem.2))
  have hXpos : 0 < solX n A B α := solX_pos hn hσ' hA hB hα
  have hUpos : 0 < solU A α := by
    have h := solU_mem hσ' hA hα
    linarith [h.1]
  have hbase : ContDiffAt ℝ (((⊤ : ℕ∞) : WithTop ℕ∞))
      (fun β => solX n A B β * solU A β) α := hX.mul hU
  have hne : solX n A B α * solU A α ≠ 0 := ne_of_gt (mul_pos hXpos hUpos)
  exact hbase.rpow (contDiffAt_const (c := (((2 * n + 2 : ℕ) : ℝ)⁻¹))) hne

lemma solr_contDiffAt (n : ℕ) (hn : 1 ≤ n) {A B : ℝ → ℝ} {σ α : ℝ} (hσ' : σ ≤ 1 / 2)
    (hAc : ContDiffOn ℝ (((⊤ : ℕ∞) : WithTop ℕ∞)) A (Set.Ioo (-1) (Real.pi / 2 + 1)))
    (hBc : ContDiffOn ℝ (((⊤ : ℕ∞) : WithTop ℕ∞)) B (Set.Ioo (-1) (Real.pi / 2 + 1)))
    (hA : ∀ β ∈ Set.Icc (0 : ℝ) (Real.pi / 2), |A β| ≤ σ)
    (hB : ∀ β ∈ Set.Icc (0 : ℝ) (Real.pi / 2), |B β| ≤ σ)
    (hα : α ∈ Set.Icc (0 : ℝ) (Real.pi / 2)) :
    ContDiffAt ℝ (((⊤ : ℕ∞) : WithTop ℕ∞)) (solr n A B) α := by
  have hmem : α ∈ Set.Ioo (-1 : ℝ) (Real.pi / 2 + 1) :=
    ⟨by linarith [hα.1], by linarith [hα.2, Real.pi_pos]⟩
  have hX : ContDiffAt ℝ (((⊤ : ℕ∞) : WithTop ℕ∞)) (solX n A B) α :=
    solX_contDiffAt n hn hσ' hAc hBc hA hB hα
  have hU : ContDiffAt ℝ (((⊤ : ℕ∞) : WithTop ℕ∞)) (solU A) α :=
    (contDiffAt_const (c := (2 : ℝ))).add (hAc.contDiffAt (Ioo_mem_nhds hmem.1 hmem.2))
  have hX1 : solX n A B α < 1 := solX_lt_one hn hσ' hA hB hα
  have hUpos : 0 < solU A α := by
    have h := solU_mem hσ' hA hα
    linarith [h.1]
  have hbase : ContDiffAt ℝ (((⊤ : ℕ∞) : WithTop ℕ∞))
      (fun β => (1 - solX n A B β) * solU A β) α :=
    (contDiffAt_const.sub hX).mul hU
  have hne : (1 - solX n A B α) * solU A α ≠ 0 :=
    ne_of_gt (mul_pos (by linarith) hUpos)
  exact hbase.rpow (contDiffAt_const (c := (((2 * n + 2 : ℕ) : ℝ)⁻¹))) hne

lemma solR_contDiffOn (n : ℕ) (hn : 1 ≤ n) {A B : ℝ → ℝ} {σ : ℝ} (hσ' : σ ≤ 1 / 2)
    (hAc : ContDiffOn ℝ (((⊤ : ℕ∞) : WithTop ℕ∞)) A (Set.Ioo (-1) (Real.pi / 2 + 1)))
    (hBc : ContDiffOn ℝ (((⊤ : ℕ∞) : WithTop ℕ∞)) B (Set.Ioo (-1) (Real.pi / 2 + 1)))
    (hA : ∀ β ∈ Set.Icc (0 : ℝ) (Real.pi / 2), |A β| ≤ σ)
    (hB : ∀ β ∈ Set.Icc (0 : ℝ) (Real.pi / 2), |B β| ≤ σ) :
    ContDiffOn ℝ (((⊤ : ℕ∞) : WithTop ℕ∞)) (solR n A B) (Set.Icc 0 (Real.pi / 2)) :=
  fun α hα => (solR_contDiffAt n hn hσ' hAc hBc hA hB hα).contDiffWithinAt

lemma solr_contDiffOn (n : ℕ) (hn : 1 ≤ n) {A B : ℝ → ℝ} {σ : ℝ} (hσ' : σ ≤ 1 / 2)
    (hAc : ContDiffOn ℝ (((⊤ : ℕ∞) : WithTop ℕ∞)) A (Set.Ioo (-1) (Real.pi / 2 + 1)))
    (hBc : ContDiffOn ℝ (((⊤ : ℕ∞) : WithTop ℕ∞)) B (Set.Ioo (-1) (Real.pi / 2 + 1)))
    (hA : ∀ β ∈ Set.Icc (0 : ℝ) (Real.pi / 2), |A β| ≤ σ)
    (hB : ∀ β ∈ Set.Icc (0 : ℝ) (Real.pi / 2), |B β| ≤ σ) :
    ContDiffOn ℝ (((⊤ : ℕ∞) : WithTop ℕ∞)) (solr n A B) (Set.Icc 0 (Real.pi / 2)) :=
  fun α hα => (solr_contDiffAt n hn hσ' hAc hBc hA hB hα).contDiffWithinAt

/-! ## Endpoint values -/

lemma radInv_zero (n : ℕ) : radInv n 0 = 1 / 2 := by
  have h : |(0 : ℝ)| < 1 := by norm_num
  symm
  refine radInv_eq_of h ⟨by norm_num, by norm_num⟩ ?_
  rw [radH_half]

lemma solW_end (n : ℕ) {A B : ℝ → ℝ} (hAend : A (Real.pi / 2) = 0)
    (hBend : B (Real.pi / 2) = 0) : solW n A B (Real.pi / 2) = 0 := by
  rw [solW_apply, hAend, hBend]
  norm_num

lemma solX_end (n : ℕ) {A B : ℝ → ℝ} (hAend : A (Real.pi / 2) = 0)
    (hBend : B (Real.pi / 2) = 0) : solX n A B (Real.pi / 2) = 1 / 2 := by
  rw [solX_apply, solW_end n hAend hBend, radInv_zero]

lemma solR_end (n : ℕ) {A B : ℝ → ℝ} (hAend : A (Real.pi / 2) = 0)
    (hBend : B (Real.pi / 2) = 0) : solR n A B (Real.pi / 2) = 1 := by
  rw [solR_apply, solX_end n hAend hBend, solU_apply, hAend]
  rw [show (1 / 2 : ℝ) * (2 + 0) = 1 by norm_num, Real.one_rpow]

lemma solr_end (n : ℕ) {A B : ℝ → ℝ} (hAend : A (Real.pi / 2) = 0)
    (hBend : B (Real.pi / 2) = 0) : solr n A B (Real.pi / 2) = 1 := by
  rw [solr_apply, solX_end n hAend hBend, solU_apply, hAend]
  rw [show (1 - 1 / 2 : ℝ) * (2 + 0) = 1 by norm_num, Real.one_rpow]

/-! ## The value bound -/

/-- For `a ∈ [3/8, 15/8]` the `m`-th root is within `2/m` of `1`. -/
lemma rpow_inv_sub_one_abs_le {a : ℝ} (ha : 3 / 8 ≤ a) (ha' : a ≤ 15 / 8) {m : ℕ}
    (hm : 0 < m) : |a ^ (((m : ℝ))⁻¹) - 1| ≤ 2 / m := by
  have ha0 : 0 < a := by linarith
  have hmpos : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  set R : ℝ := a ^ (((m : ℝ))⁻¹) with hRdef
  have hRpos : 0 < R := Real.rpow_pos_of_pos ha0 _
  have hRm : R ^ m = a := Real.rpow_inv_natCast_pow (le_of_lt ha0) (by omega)
  by_cases ha1 : a ≤ 1
  · -- `a ≤ 1`
    have hR1 : R ≤ 1 := by
      rw [hRdef]
      calc a ^ (((m : ℝ))⁻¹) ≤ 1 ^ (((m : ℝ))⁻¹) :=
            Real.rpow_le_rpow ha0.le ha1 (by positivity)
        _ = 1 := Real.one_rpow _
    have hR0 : 0 ≤ 1 - R := by linarith
    have hgeo := mul_geom_sum R m
    rw [hRm] at hgeo
    have hsum : (m : ℝ) * (3 / 8) ≤ ∑ i ∈ Finset.range m, R ^ i := by
      have hterm : ∀ i ∈ Finset.range m, (3 / 8 : ℝ) ≤ R ^ i := by
        intro i hi
        have hi' : i ≤ m := le_of_lt (Finset.mem_range.mp hi)
        calc (3 / 8 : ℝ) ≤ a := ha
          _ = R ^ m := hRm.symm
          _ ≤ R ^ i := pow_le_pow_of_le_one hRpos.le hR1 hi'
      calc (m : ℝ) * (3 / 8) = ∑ _i ∈ Finset.range m, (3 / 8 : ℝ) := by
            rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        _ ≤ ∑ i ∈ Finset.range m, R ^ i := Finset.sum_le_sum hterm
    have h1a : 1 - a = (1 - R) * (∑ i ∈ Finset.range m, R ^ i) := by linarith [hgeo]
    have hdown : (1 - R) * ((m : ℝ) * (3 / 8)) ≤ 1 - a := by
      rw [h1a]
      exact mul_le_mul_of_nonneg_left hsum hR0
    have h1a' : 1 - a ≤ 5 / 8 := by linarith
    have h2 : (1 - R) * ((m : ℝ) * (3 / 8)) ≤ 5 / 8 := le_trans hdown h1a'
    have hm38 : 0 < (m : ℝ) * (3 / 8) := by positivity
    have h3 : 1 - R ≤ (5 / 8) / ((m : ℝ) * (3 / 8)) := by
      rw [le_div_iff₀ hm38]
      linarith
    have h4 : (5 : ℝ) / 8 / ((m : ℝ) * (3 / 8)) = 5 / (3 * (m : ℝ)) := by
      field_simp
    rw [h4] at h3
    have h5 : (5 : ℝ) / (3 * (m : ℝ)) ≤ 2 / m := by
      have h6 : (2 : ℝ) / m = 6 / (3 * (m : ℝ)) := by
        field_simp
        norm_num
      rw [h6, div_le_div_iff_of_pos_right (by positivity : (0 : ℝ) < 3 * (m : ℝ))]
      norm_num
    rw [abs_sub_le_iff]
    constructor
    · linarith
    · linarith
  · -- `a > 1`, so `R ≥ 1`
    have ha1' : 1 < a := not_le.mp ha1
    have hR1 : 1 ≤ R := by
      rw [hRdef]
      calc (1 : ℝ) = 1 ^ (((m : ℝ))⁻¹) := (Real.one_rpow _).symm
        _ ≤ a ^ (((m : ℝ))⁻¹) := Real.rpow_le_rpow (by norm_num) (le_of_lt ha1') (by positivity)
    have hbern : 1 + (m : ℝ) * ((a - 1) / m) ≤ (1 + (a - 1) / m) ^ m := by
      refine one_add_mul_le_pow ?_ m
      have : (-2 : ℝ) ≤ (a - 1) / m := by
        rw [le_div_iff₀ hmpos]
        linarith [ha, hmpos]
      linarith
    rw [show (m : ℝ) * ((a - 1) / m) = a - 1 by field_simp] at hbern
    have h2 : a ≤ (1 + (a - 1) / m) ^ m := by linarith [hbern]
    have h3 : (0 : ℝ) ≤ 1 + (a - 1) / m := by
      have heq : (1 : ℝ) + (a - 1) / m = ((m : ℝ) + a - 1) / m := by
        field_simp
        ring
      rw [heq]
      exact div_nonneg (by linarith [ha, hmpos]) hmpos.le
    have h4 : R ≤ 1 + (a - 1) / m :=
      (pow_le_pow_iff_left₀ hRpos.le h3 (Nat.pos_iff_ne_zero.mp hm)).mp (by rw [hRm]; exact h2)
    have h5 : (a - 1) / m ≤ 7 / 8 / m := by
      apply div_le_div_of_nonneg_right _ hmpos.le
      linarith
    have h6 : (7 : ℝ) / 8 / m ≤ 2 / m := by
      apply div_le_div_of_nonneg_right _ hmpos.le
      norm_num
    have h7 : 1 - R ≤ 0 := by linarith
    rw [abs_sub_le_iff]
    exact ⟨by linarith, by linarith⟩

/-- **The value bound**: `|R - 1| ≤ (log(1+σ)+1)/(n+1)`. -/
lemma solR_sub_one_bound (n : ℕ) (hn : 1 ≤ n) {A B : ℝ → ℝ} {σ α : ℝ} (hσ : 0 < σ)
    (hσ' : σ ≤ 1 / 2) (hA : ∀ β ∈ Set.Icc (0 : ℝ) (Real.pi / 2), |A β| ≤ σ)
    (hB : ∀ β ∈ Set.Icc (0 : ℝ) (Real.pi / 2), |B β| ≤ σ)
    (hα : α ∈ Set.Icc (0 : ℝ) (Real.pi / 2)) :
    |solR n A B α - 1| ≤ (Real.log (1 + σ) + 1) / ((n : ℝ) + 1) := by
  have hxm := solX_mem hn hσ' hA hB hα
  have hu := solU_mem hσ' hA hα
  have hx0 : 0 < solX n A B α := lt_trans (by norm_num) hxm.1
  have hx1 : solX n A B α < 1 := lt_trans hxm.2 (by norm_num)
  have hu0 : 0 < solU A α := by linarith [hu.1]
  have hm : 0 < 2 * n + 2 := by omega
  have hR : solR n A B α = (solX n A B α * solU A α) ^ (((2 * n + 2 : ℕ) : ℝ))⁻¹ := by
    rw [solR_apply]
  have hbounds : (3 / 8 : ℝ) ≤ solX n A B α * solU A α ∧
      solX n A B α * solU A α ≤ 15 / 8 := by
    constructor
    · have h1 : (1 / 4 : ℝ) ≤ solX n A B α := le_of_lt hxm.1
      nlinarith [hu.1]
    · have h1 : solX n A B α ≤ 3 / 4 := le_of_lt hxm.2
      nlinarith [hu.2]
  have hnum : |solR n A B α - 1| ≤ 2 / (((2 * n + 2 : ℕ)) : ℝ) := by
    rw [hR]
    exact rpow_inv_sub_one_abs_le hbounds.1 hbounds.2 hm
  have hstep : (2 : ℝ) / (((2 * n + 2 : ℕ)) : ℝ) ≤
      (Real.log (1 + σ) + 1) / ((n : ℝ) + 1) := by
    have hlog : 0 ≤ Real.log (1 + σ) := Real.log_nonneg (by linarith)
    have hd : (2 : ℝ) / (((2 * n + 2 : ℕ)) : ℝ) = 1 / ((n : ℝ) + 1) := by
      push_cast
      field_simp
    rw [hd, div_le_div_iff_of_pos_right (by positivity : (0 : ℝ) < (n : ℝ) + 1)]
    linarith
  exact le_trans hnum hstep

/-- The same bound for `r`. -/
lemma solr_sub_one_bound (n : ℕ) (hn : 1 ≤ n) {A B : ℝ → ℝ} {σ α : ℝ} (hσ : 0 < σ)
    (hσ' : σ ≤ 1 / 2) (hA : ∀ β ∈ Set.Icc (0 : ℝ) (Real.pi / 2), |A β| ≤ σ)
    (hB : ∀ β ∈ Set.Icc (0 : ℝ) (Real.pi / 2), |B β| ≤ σ)
    (hα : α ∈ Set.Icc (0 : ℝ) (Real.pi / 2)) :
    |solr n A B α - 1| ≤ (Real.log (1 + σ) + 1) / ((n : ℝ) + 1) := by
  have hxm := solX_mem hn hσ' hA hB hα
  have hu := solU_mem hσ' hA hα
  have hx0 : 0 < 1 - solX n A B α := by linarith [hxm.2]
  have hx1 : 1 - solX n A B α < 1 := by linarith [hxm.1]
  have hu0 : 0 < solU A α := by linarith [hu.1]
  have hm : 0 < 2 * n + 2 := by omega
  have hr : solr n A B α = ((1 - solX n A B α) * solU A α) ^ (((2 * n + 2 : ℕ) : ℝ))⁻¹ := by
    rw [solr_apply]
  have hbounds : (3 / 8 : ℝ) ≤ (1 - solX n A B α) * solU A α ∧
      (1 - solX n A B α) * solU A α ≤ 15 / 8 := by
    constructor
    · have h1 : (1 / 4 : ℝ) ≤ 1 - solX n A B α := by linarith [hxm.2]
      nlinarith [hu.1]
    · have h1 : 1 - solX n A B α ≤ 3 / 4 := by linarith [hxm.1]
      nlinarith [hu.2]
  have hnum : |solr n A B α - 1| ≤ 2 / (((2 * n + 2 : ℕ)) : ℝ) := by
    rw [hr]
    exact rpow_inv_sub_one_abs_le hbounds.1 hbounds.2 hm
  have hstep : (2 : ℝ) / (((2 * n + 2 : ℕ)) : ℝ) ≤
      (Real.log (1 + σ) + 1) / ((n : ℝ) + 1) := by
    have hlog : 0 ≤ Real.log (1 + σ) := Real.log_nonneg (by linarith)
    have hd : (2 : ℝ) / (((2 * n + 2 : ℕ)) : ℝ) = 1 / ((n : ℝ) + 1) := by
      push_cast
      field_simp
    rw [hd, div_le_div_iff_of_pos_right (by positivity : (0 : ℝ) < (n : ℝ) + 1)]
    linarith
  exact le_trans hnum hstep

/-- `R > 0` on the interval. -/
lemma solR_pos (n : ℕ) (hn : 1 ≤ n) {A B : ℝ → ℝ} {σ α : ℝ} (hσ' : σ ≤ 1 / 2)
    (hA : ∀ β ∈ Set.Icc (0 : ℝ) (Real.pi / 2), |A β| ≤ σ)
    (hB : ∀ β ∈ Set.Icc (0 : ℝ) (Real.pi / 2), |B β| ≤ σ)
    (hα : α ∈ Set.Icc (0 : ℝ) (Real.pi / 2)) : 0 < solR n A B α := by
  have hxm := solX_mem hn hσ' hA hB hα
  have hu := solU_mem hσ' hA hα
  rw [solR_apply]
  exact Real.rpow_pos_of_pos (mul_pos (lt_trans (by norm_num) hxm.1) (by linarith [hu.1])) _

/-- `r > 0` on the interval. -/
lemma solr_pos (n : ℕ) (hn : 1 ≤ n) {A B : ℝ → ℝ} {σ α : ℝ} (hσ' : σ ≤ 1 / 2)
    (hA : ∀ β ∈ Set.Icc (0 : ℝ) (Real.pi / 2), |A β| ≤ σ)
    (hB : ∀ β ∈ Set.Icc (0 : ℝ) (Real.pi / 2), |B β| ≤ σ)
    (hα : α ∈ Set.Icc (0 : ℝ) (Real.pi / 2)) : 0 < solr n A B α := by
  have hxm := solX_mem hn hσ' hA hB hα
  have hu := solU_mem hσ' hA hα
  rw [solr_apply]
  exact Real.rpow_pos_of_pos (mul_pos (by linarith [hxm.2]) (by linarith [hu.1])) _

/-- The box bounds for `R^m`. -/
lemma solR_box (n : ℕ) (hn : 1 ≤ n) {A B : ℝ → ℝ} {σ α : ℝ} (hσ' : σ ≤ 1 / 2)
    (hA : ∀ β ∈ Set.Icc (0 : ℝ) (Real.pi / 2), |A β| ≤ σ)
    (hB : ∀ β ∈ Set.Icc (0 : ℝ) (Real.pi / 2), |B β| ≤ σ)
    (hα : α ∈ Set.Icc (0 : ℝ) (Real.pi / 2)) :
    3 / 8 ≤ (solR n A B α) ^ (2 * n + 2) ∧ (solR n A B α) ^ (2 * n + 2) ≤ 15 / 8 := by
  have hxm := solX_mem hn hσ' hA hB hα
  have hu := solU_mem hσ' hA hα
  have hx0 : 0 < solX n A B α := lt_trans (by norm_num) hxm.1
  have hu0 : 0 ≤ solU A α := le_of_lt (by linarith [hu.1] : (0:ℝ) < solU A α)
  rw [solR_pow_m n (le_of_lt hx0) hu0]
  constructor <;> nlinarith [hxm.1, hxm.2, hu.1, hu.2]

/-- The box bounds for `r^m`. -/
lemma solr_box (n : ℕ) (hn : 1 ≤ n) {A B : ℝ → ℝ} {σ α : ℝ} (hσ' : σ ≤ 1 / 2)
    (hA : ∀ β ∈ Set.Icc (0 : ℝ) (Real.pi / 2), |A β| ≤ σ)
    (hB : ∀ β ∈ Set.Icc (0 : ℝ) (Real.pi / 2), |B β| ≤ σ)
    (hα : α ∈ Set.Icc (0 : ℝ) (Real.pi / 2)) :
    3 / 8 ≤ (solr n A B α) ^ (2 * n + 2) ∧ (solr n A B α) ^ (2 * n + 2) ≤ 15 / 8 := by
  have hxm := solX_mem hn hσ' hA hB hα
  have hu := solU_mem hσ' hA hα
  have hx1 : 0 < 1 - solX n A B α := by linarith [hxm.2]
  have hu0 : 0 ≤ solU A α := le_of_lt (by linarith [hu.1] : (0:ℝ) < solU A α)
  rw [solr_pow_m n (le_of_lt hx1) hu0]
  constructor <;> nlinarith [hxm.1, hxm.2, hu.1, hu.2]

end Work.OddCurve.LowSlope
