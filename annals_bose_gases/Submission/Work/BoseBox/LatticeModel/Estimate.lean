import Mathlib.Order.CompletePartialOrder
import Mathlib.Data.Int.Star
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseBox.LatticeModel.abs_lhyProfile_sub_le
import Submission.Work.BoseBox.LatticeModel.integrable_lhyProfile
import Submission.Work.BoseBox.LatticeModel.integral_ball_abs_lhyProfile_le
import Submission.Work.BoseBox.LatticeModel.integral_tail_abs_lhyProfile_le
import Submission.Work.BoseBox.LatticeModel.latticeCell_geometry
import Submission.Work.BoseBox.LatticeModel.latticeCells_card_mul_le
import Submission.Work.BoseBox.LatticeModel.lhyProfile_basic
import Submission.Work.BoseBox.LatticeModel.sum_sub_setIntegral_eq
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The lattice-sum Riemann limit: the main estimate

`mesh n = 2π/(n+1)` is the mesh of the FS lattice, `gridN n = (n+1)²` the number
of grid points per coordinate.  This module proves, with all constants explicit:

* `far_part`   — the discrepancy on the cells whose centre is outside the ball of
  radius `2h√3` is at most `128π√3 c² h log N` (MVT bound `|φ'| ≤ 8c²/r³`,
  converted into an integral over the far shell);
* `near_part`  — the discrepancy on the remaining (at most `256π√3`-many) cells is
  at most `512π√3ch³ + 520π√3c²h`;
* `cell_error_le` — combining via the cell identity `sum_sub_setIntegral_eq`;
* `tail_le`    — the integral over the enclosing cube differs from `∫_{ℝ³}` by at
  most `4c³/(n+1)`;
* `tendsto_latticeErr` — the resulting majorant tends to `0`.
-/

open MeasureTheory Filter
open scoped Real BigOperators

namespace Work.BoseBox

noncomputable section

def mesh (n : ℕ) : ℝ := 2 * Real.pi / ((n : ℝ) + 1)

/-- The number `(n+1)²` of grid points per coordinate. -/
def gridN (n : ℕ) : ℕ := (n + 1) * (n + 1)

lemma mesh_eq (n : ℕ) : mesh n = 2 * Real.pi / ((n : ℝ) + 1) := rfl

lemma mesh_pos (n : ℕ) : 0 < mesh n := by
  have h : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  exact div_pos (by positivity) h

lemma gridN_pos (n : ℕ) : 0 < gridN n := by
  have : (0 : ℕ) < n + 1 := Nat.succ_pos n
  exact Nat.mul_pos this this

/-- The explicit error majorant of the lattice approximation. -/
def latticeErr (c : ℝ) (n : ℕ) : ℝ :=
  512 * Real.pi * Real.sqrt 3 * c * (mesh n) ^ 3
    + 520 * Real.pi * Real.sqrt 3 * c ^ 2 * (mesh n)
    + 128 * Real.pi * Real.sqrt 3 * c ^ 2 * (mesh n) * Real.log (gridN n)
    + 4 * c ^ 3 / ((n : ℝ) + 1)

lemma sqrt3_cube : Real.sqrt 3 ^ 3 = 3 * Real.sqrt 3 := by
  have h : Real.sqrt 3 * Real.sqrt 3 = 3 := by
    rw [← pow_two, Real.sq_sqrt (by norm_num)]
  calc Real.sqrt 3 ^ 3 = Real.sqrt 3 * (Real.sqrt 3 * Real.sqrt 3) := by ring
    _ = Real.sqrt 3 * 3 := by rw [h]
    _ = 3 * Real.sqrt 3 := by ring

lemma cube_four_h_sqrt3 (h : ℝ) : (4 * h * Real.sqrt 3) ^ 3 = 192 * Real.sqrt 3 * h ^ 3 := by
  rw [mul_pow, mul_pow, sqrt3_cube]
  ring

-- ============================================================
-- Helper lemmas for the main argument
-- ============================================================

/-- The norm of a set integral is at most the integral of the norm. -/
lemma norm_setIntegral_le {s : Set (Fin 3 → ℝ)} (f : (Fin 3 → ℝ) → ℝ) :
    ‖∫ x in s, f x‖ ≤ ∫ x in s, ‖f x‖ := by
  calc ‖∫ x in s, f x‖ = ‖∫ x, f x ∂(volume.restrict s)‖ := rfl
    _ ≤ ∫ x, ‖f x‖ ∂(volume.restrict s) := norm_integral_le_integral_norm _
    _ = ∫ x in s, ‖f x‖ := rfl

/-- `F = lhyProfile c ∘ eucNorm3` is integrable. -/
lemma integrable_F {c : ℝ} (hc : 0 < c) :
    MeasureTheory.Integrable
      (fun x : Fin 3 → ℝ => lhyProfile c (Submission.BoseGases.eucNorm3 x))
      MeasureTheory.volume :=
  LatticeModel.integrable_lhyProfile hc (LatticeModel.lhyProfile_basic hc).2.1 (LatticeModel.lhyProfile_basic hc).2.2

/-- `x ↦ 1/‖x‖³` is integrable on any finite-measure set on which `‖x‖ ≥ A > 0`. -/
lemma integrableOn_inv_cube {A : ℝ} (hA : 0 < A) {s : Set (Fin 3 → ℝ)}
    (hsm : MeasurableSet s) (hμ : MeasureTheory.volume s < ⊤)
    (hbd : ∀ x ∈ s, A ≤ Submission.BoseGases.eucNorm3 x) :
    MeasureTheory.IntegrableOn
      (fun x : Fin 3 → ℝ => (1 : ℝ) / (Submission.BoseGases.eucNorm3 x) ^ 3) s
      MeasureTheory.volume := by
  refine MeasureTheory.IntegrableOn.of_bound hμ ?_ (1 / A ^ 3) ?_
  · exact ((Measurable.const_div (measurable_eucNorm3.pow_const 3) 1)).aestronglyMeasurable
  · filter_upwards [MeasureTheory.self_mem_ae_restrict hsm] with x hx
    have hxbd : A ≤ Submission.BoseGases.eucNorm3 x := hbd x hx
    rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg zero_le_one
      (pow_nonneg (Submission.BoseGases.eucNorm3_nonneg x) 3))]
    exact one_div_le_one_div_of_le (pow_pos hA 3) (pow_le_pow_left₀ hA.le hxbd 3)

/-- `IntegrableOn` is stable under `|·|`. -/
lemma IntegrableOn.abs' {s : Set (Fin 3 → ℝ)} (hsm : MeasurableSet s)
    {g : (Fin 3 → ℝ) → ℝ}
    (h : MeasureTheory.IntegrableOn g s MeasureTheory.volume) :
    MeasureTheory.IntegrableOn (fun x => |g x|) s MeasureTheory.volume := by
  have hind : MeasureTheory.Integrable (s.indicator g) volume :=
    (MeasureTheory.integrable_indicator_iff hsm).mpr h
  have h2 := hind.abs
  have heq : (fun x => |s.indicator g x|) = s.indicator (fun x => |g x|) := by
    funext x
    by_cases hx : x ∈ s
    · rw [Set.indicator_of_mem hx, Set.indicator_of_mem hx]
    · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem hx, abs_zero]
  rw [heq] at h2
  exact (MeasureTheory.integrable_indicator_iff hsm).mp h2

/-- `eucNorm3` is bounded by `√3 R` when every coordinate is bounded by `R`. -/
lemma eucNorm3_le_sqrt_three_mul {x : Fin 3 → ℝ} {R : ℝ} (hR : 0 ≤ R)
    (h : ∀ j, |x j| ≤ R) :
    Submission.BoseGases.eucNorm3 x ≤ Real.sqrt 3 * R := by
  rw [show Submission.BoseGases.eucNorm3 x
      = Real.sqrt (∑ j : Fin 3, x j ^ 2) from rfl]
  have h3 : Real.sqrt 3 * R = Real.sqrt (3 * R ^ 2) := by
    rw [Real.sqrt_mul (by norm_num), Real.sqrt_sq hR]
  rw [h3]
  apply Real.sqrt_le_sqrt
  calc ∑ j : Fin 3, x j ^ 2 ≤ ∑ _j : Fin 3, R ^ 2 :=
        Finset.sum_le_sum (fun j _ => by
          rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) (h j) 2)
    _ = 3 * R ^ 2 := by simp [Finset.sum_const]

/-- **Pointwise bound on a far cell.** -/
lemma far_cell_pointwise {c h : ℝ} (hc : 0 < c) (hh : 0 < h) {N : ℕ} {k : Fin 3 → Fin N}
    {x : Fin 3 → ℝ}
    (hfar : 2 * h * Real.sqrt 3 ≤ Submission.BoseGases.eucNorm3 (latticeCenter h N k))
    (hdist : |Submission.BoseGases.eucNorm3 x
        - Submission.BoseGases.eucNorm3 (latticeCenter h N k)| ≤ h * Real.sqrt 3 / 2) :
    |lhyProfile c (Submission.BoseGases.eucNorm3 (latticeCenter h N k))
        - lhyProfile c (Submission.BoseGases.eucNorm3 x)|
      ≤ 32 * c ^ 2 * h * Real.sqrt 3 / (Submission.BoseGases.eucNorm3 x) ^ 3 := by
  set ρ := Submission.BoseGases.eucNorm3 (latticeCenter h N k) with hρ
  set σ := Submission.BoseGases.eucNorm3 x with hσ
  have hsqrt3 : (0 : ℝ) < Real.sqrt 3 := Real.sqrt_pos.mpr (by norm_num)
  have hh3pos : 0 < h * Real.sqrt 3 := mul_pos hh hsqrt3
  have hρ0 : 0 < ρ := by linarith [hfar]
  have hab := abs_le.mp hdist
  have hσlower : ρ - h * Real.sqrt 3 / 2 ≤ σ := by linarith [hab.1]
  have hσge : h * Real.sqrt 3 ≤ σ := by nlinarith [hσlower, hfar]
  have hσ0 : 0 < σ := lt_of_lt_of_le hh3pos hσge
  have hσρ_le : σ - ρ ≤ h * Real.sqrt 3 / 2 := hab.2
  have hρσ_le : ρ - σ ≤ h * Real.sqrt 3 / 2 := by linarith [hab.1]
  have hσle2ρ : σ ≤ 2 * ρ := by
    have h2 : h * Real.sqrt 3 / 2 ≤ σ / 2 := by linarith [hσge]
    linarith [hσlower, h2]
  rcases le_total σ ρ with hcase | hcase
  · have hb := LatticeModel.abs_lhyProfile_sub_le hc σ ρ hσ0 hcase
    have h1 : |lhyProfile c ρ - lhyProfile c σ| ≤ 8 * c ^ 2 * (ρ - σ) / σ ^ 3 := hb
    have hmul : 8 * c ^ 2 * (ρ - σ) ≤ 8 * c ^ 2 * (h * Real.sqrt 3 / 2) :=
      mul_le_mul_of_nonneg_left hρσ_le (by positivity)
    have hfin : 8 * c ^ 2 * (h * Real.sqrt 3 / 2) ≤ 32 * c ^ 2 * h * Real.sqrt 3 := by
      have hprod : 0 ≤ c ^ 2 * (h * Real.sqrt 3) := by positivity
      nlinarith [hprod]
    have hnum : 8 * c ^ 2 * (ρ - σ) / σ ^ 3 ≤ 32 * c ^ 2 * h * Real.sqrt 3 / σ ^ 3 := by
      apply div_le_div_of_nonneg_right _ (by positivity)
      linarith [hmul, hfin]
    calc |lhyProfile c ρ - lhyProfile c σ|
        ≤ 8 * c ^ 2 * (ρ - σ) / σ ^ 3 := h1
      _ ≤ 32 * c ^ 2 * h * Real.sqrt 3 / σ ^ 3 := hnum
  · have hb := LatticeModel.abs_lhyProfile_sub_le hc ρ σ hρ0 hcase
    have h1 : |lhyProfile c ρ - lhyProfile c σ| ≤ 8 * c ^ 2 * (σ - ρ) / ρ ^ 3 := by
      rw [abs_sub_comm]; exact hb
    have hσ3 : σ ^ 3 ≤ 8 * ρ ^ 3 := by
      have := pow_le_pow_left₀ (le_of_lt hσ0) hσle2ρ 3
      nlinarith [this, pow_pos hρ0 3]
    have hmul : 8 * c ^ 2 * (σ - ρ) ≤ 8 * c ^ 2 * (h * Real.sqrt 3 / 2) :=
      mul_le_mul_of_nonneg_left hσρ_le (by positivity)
    have hnum : 8 * c ^ 2 * (σ - ρ) / ρ ^ 3 ≤ 32 * c ^ 2 * h * Real.sqrt 3 / σ ^ 3 := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      calc 8 * c ^ 2 * (σ - ρ) * σ ^ 3
          ≤ (8 * c ^ 2 * (h * Real.sqrt 3 / 2)) * (8 * ρ ^ 3) := by
            apply mul_le_mul hmul hσ3 (by positivity) (by positivity)
        _ = 32 * c ^ 2 * h * Real.sqrt 3 * ρ ^ 3 := by ring
    calc |lhyProfile c ρ - lhyProfile c σ|
        ≤ 8 * c ^ 2 * (σ - ρ) / ρ ^ 3 := h1
      _ ≤ 32 * c ^ 2 * h * Real.sqrt 3 / σ ^ 3 := hnum

/-- **Far-region estimate**: the discrepancy of the Riemann sum on the cells whose
centre lies outside the ball of radius `2h√3`. -/
lemma far_part {c h : ℝ} (hc : 0 < c) (hh : 0 < h) {N : ℕ} (hN : 0 < N)
    (hdisp : ∀ k k' : Fin 3 → Fin N, k ≠ k' →
      Disjoint (latticeCell h N k) (latticeCell h N k'))
    (hmeas : ∀ k : Fin 3 → Fin N, MeasurableSet (latticeCell h N k))
    (hvol : ∀ k : Fin 3 → Fin N,
      MeasureTheory.volume (latticeCell h N k) = ENNReal.ofReal (h ^ 3))
    (hdist : ∀ k : Fin 3 → Fin N, ∀ x : Fin 3 → ℝ, x ∈ latticeCell h N k →
      |Submission.BoseGases.eucNorm3 x - Submission.BoseGases.eucNorm3 (latticeCenter h N k)|
        ≤ h * Real.sqrt 3 / 2)
    (hsubbox : ∀ k : Fin 3 → Fin N, latticeCell h N k ⊆ latticeBox h N)
    (hintF : MeasureTheory.IntegrableOn
      (fun x : Fin 3 → ℝ => lhyProfile c (Submission.BoseGases.eucNorm3 x))
      (latticeBox h N)) :
    (∑ k ∈ Finset.univ.filter (fun k : Fin 3 → Fin N =>
        2 * h * Real.sqrt 3 ≤ Submission.BoseGases.eucNorm3 (latticeCenter h N k)),
      ∫ x in latticeCell h N k,
        |lhyProfile c (Submission.BoseGases.eucNorm3 (latticeCenter h N k))
          - lhyProfile c (Submission.BoseGases.eucNorm3 x)|)
      ≤ 128 * Real.pi * Real.sqrt 3 * c ^ 2 * h * Real.log (N : ℝ) := by
  classical
  set s : Finset (Fin 3 → Fin N) := Finset.univ.filter (fun k : Fin 3 → Fin N =>
    2 * h * Real.sqrt 3 ≤ Submission.BoseGases.eucNorm3 (latticeCenter h N k)) with hs
  have hmem : ∀ k ∈ s,
      2 * h * Real.sqrt 3 ≤ Submission.BoseGases.eucNorm3 (latticeCenter h N k) := by
    intro k hk
    rw [hs] at hk
    exact (Finset.mem_filter.mp hk).2
  have hh3 : 0 < h * Real.sqrt 3 := mul_pos hh (Real.sqrt_pos.mpr (by norm_num))
  -- integrability of the comparison function on each far cell
  have hψcell : ∀ k ∈ s, MeasureTheory.IntegrableOn
      (fun x : Fin 3 → ℝ => 32 * c ^ 2 * h * Real.sqrt 3 / (Submission.BoseGases.eucNorm3 x) ^ 3)
      (latticeCell h N k) MeasureTheory.volume := by
    intro k hk
    have hbase := integrableOn_inv_cube hh3 (hmeas k)
      (by rw [hvol k]; exact ENNReal.ofReal_lt_top)
      (fun x hx => by
        have hb := (abs_le.mp (hdist k x hx)).1
        have hh2 := hmem k hk
        nlinarith [hb, hh2, hh3])
    refine (hbase.const_mul (32 * c ^ 2 * h * Real.sqrt 3)).congr ?_
    filter_upwards with x
    ring
  -- cellwise comparison
  have hcellle : ∀ k ∈ s,
      (∫ x in latticeCell h N k,
        |lhyProfile c (Submission.BoseGases.eucNorm3 (latticeCenter h N k))
          - lhyProfile c (Submission.BoseGases.eucNorm3 x)|)
      ≤ ∫ x in latticeCell h N k,
          32 * c ^ 2 * h * Real.sqrt 3 / (Submission.BoseGases.eucNorm3 x) ^ 3 := by
    intro k hk
    have hpt : ∀ x ∈ latticeCell h N k,
        |lhyProfile c (Submission.BoseGases.eucNorm3 (latticeCenter h N k))
          - lhyProfile c (Submission.BoseGases.eucNorm3 x)|
        ≤ 32 * c ^ 2 * h * Real.sqrt 3 / (Submission.BoseGases.eucNorm3 x) ^ 3 :=
      fun x hx => far_cell_pointwise hc hh (hmem k hk) (hdist k x hx)
    have hintL : MeasureTheory.IntegrableOn (fun x : Fin 3 → ℝ =>
        |lhyProfile c (Submission.BoseGases.eucNorm3 (latticeCenter h N k))
          - lhyProfile c (Submission.BoseGases.eucNorm3 x)|)
        (latticeCell h N k) MeasureTheory.volume :=
      IntegrableOn.abs' (hmeas k)
        ((MeasureTheory.integrableOn_const
          (by rw [hvol k]; exact ENNReal.ofReal_ne_top)).sub (hintF.mono_set (hsubbox k)))
    exact MeasureTheory.setIntegral_mono_on hintL (hψcell k hk) (hmeas k) hpt
  -- the sum of the cell integrals is the integral over the union
  have hdisj : (↑s : Set (Fin 3 → Fin N)).Pairwise
      (Function.onFun Disjoint (fun k : Fin 3 → Fin N => latticeCell h N k)) :=
    fun k _ k' _ hne => hdisp k k' hne
  have hunion : (∑ k ∈ s, ∫ x in latticeCell h N k,
        32 * c ^ 2 * h * Real.sqrt 3 / (Submission.BoseGases.eucNorm3 x) ^ 3)
      = ∫ x in (⋃ k ∈ s, latticeCell h N k),
          32 * c ^ 2 * h * Real.sqrt 3 / (Submission.BoseGases.eucNorm3 x) ^ 3 :=
    (MeasureTheory.integral_biUnion_finset s (fun k _ => hmeas k) hdisj
      (fun k hk => hψcell k hk)).symm
  -- the union is contained in the far shell
  set T : Set (Fin 3 → ℝ) := {x : Fin 3 → ℝ |
      h * Real.sqrt 3 ≤ Submission.BoseGases.eucNorm3 x ∧
      Submission.BoseGases.eucNorm3 x ≤ Real.sqrt 3 * (h * (N : ℝ) / 2 + h / 2)} with hT
  have hTmeas : MeasurableSet T := by
    rw [hT]
    exact (measurableSet_le measurable_const measurable_eucNorm3).inter
      (measurableSet_le measurable_eucNorm3 measurable_const)
  have hTtop : MeasureTheory.volume T < ⊤ :=
    lt_of_le_of_lt (MeasureTheory.measure_mono (fun x hx => hx.2)) volume_eucNorm3_ball_lt_top
  have hψT : MeasureTheory.IntegrableOn
      (fun x : Fin 3 → ℝ => 32 * c ^ 2 * h * Real.sqrt 3 / (Submission.BoseGases.eucNorm3 x) ^ 3)
      T MeasureTheory.volume := by
    have hbase := integrableOn_inv_cube hh3 hTmeas hTtop (fun x hx => hx.1)
    refine (hbase.const_mul (32 * c ^ 2 * h * Real.sqrt 3)).congr ?_
    filter_upwards with x
    ring
  have hUsub : (⋃ k ∈ s, latticeCell h N k) ⊆ T := by
    intro x hx
    rw [Set.mem_iUnion] at hx
    obtain ⟨k, hx⟩ := hx
    rw [Set.mem_iUnion] at hx
    obtain ⟨hk, hxk⟩ := hx
    have hbx : x ∈ latticeBox h N := hsubbox k hxk
    rw [hT, Set.mem_setOf_eq]
    refine ⟨?_, ?_⟩
    · have hb := (abs_le.mp (hdist k x hxk)).1
      have hh2 := hmem k hk
      nlinarith [hb, hh2, hh3]
    · rw [latticeBox] at hbx
      have hcoord : ∀ j : Fin 3, |x j| ≤ h * (N : ℝ) / 2 + h / 2 := by
        intro j
        have hji := Set.mem_univ_pi.mp hbx j
        rw [Set.mem_Ico] at hji
        rw [abs_le]
        exact ⟨by linarith [hji.1], by linarith [hji.2]⟩
      have := eucNorm3_le_sqrt_three_mul (x := x) (R := h * (N : ℝ) / 2 + h / 2)
        (by positivity) hcoord
      linarith [this]
  have hmono : (∫ x in (⋃ k ∈ s, latticeCell h N k),
        32 * c ^ 2 * h * Real.sqrt 3 / (Submission.BoseGases.eucNorm3 x) ^ 3)
      ≤ ∫ x in T,
          32 * c ^ 2 * h * Real.sqrt 3 / (Submission.BoseGases.eucNorm3 x) ^ 3 := by
    refine MeasureTheory.setIntegral_mono_set hψT ?_ ?_
    · filter_upwards with x
      exact div_nonneg (by positivity)
        (pow_nonneg (Submission.BoseGases.eucNorm3_nonneg x) 3)
    · filter_upwards with x hx
      exact hUsub hx
  -- evaluation
  have hAB : h * Real.sqrt 3 ≤ Real.sqrt 3 * (h * (N : ℝ) / 2 + h / 2) := by
    have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
    nlinarith [hh, Real.sqrt_pos.mpr (by norm_num : (0:ℝ) < 3)]
  have hshell := (LatticeModel.radial_integral_corollaries).2.2.1 (h * Real.sqrt 3)
    (Real.sqrt 3 * (h * (N : ℝ) / 2 + h / 2)) hh3 hAB
  have hBA : Real.sqrt 3 * (h * (N : ℝ) / 2 + h / 2) / (h * Real.sqrt 3)
      = (N : ℝ) / 2 + 1 / 2 := by
    have hne : h * Real.sqrt 3 ≠ 0 := ne_of_gt hh3
    field_simp
  have hTval : (∫ x in T,
        32 * c ^ 2 * h * Real.sqrt 3 / (Submission.BoseGases.eucNorm3 x) ^ 3)
      = 32 * c ^ 2 * h * Real.sqrt 3 * (4 * Real.pi * Real.log ((N : ℝ) / 2 + 1 / 2)) := by
    have h1 : (∫ x in T,
          32 * c ^ 2 * h * Real.sqrt 3 / (Submission.BoseGases.eucNorm3 x) ^ 3)
        = 32 * c ^ 2 * h * Real.sqrt 3 *
            (∫ x in T, (1 : ℝ) / (Submission.BoseGases.eucNorm3 x) ^ 3) := by
      rw [← MeasureTheory.integral_const_mul]
      apply MeasureTheory.setIntegral_congr_fun hTmeas
      intro x _
      ring
    rw [h1, hT, hshell, hBA]
  have hlog : Real.log ((N : ℝ) / 2 + 1 / 2) ≤ Real.log (N : ℝ) := by
    apply Real.log_le_log (by positivity)
    have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
    linarith
  have hfinal : 32 * c ^ 2 * h * Real.sqrt 3 * (4 * Real.pi * Real.log ((N : ℝ) / 2 + 1 / 2))
      ≤ 128 * Real.pi * Real.sqrt 3 * c ^ 2 * h * Real.log (N : ℝ) := by
    have hcoef : 0 ≤ 32 * c ^ 2 * h * Real.sqrt 3 * (4 * Real.pi) := by positivity
    have := mul_le_mul_of_nonneg_left hlog hcoef
    linarith [this]
  calc (∑ k ∈ s, ∫ x in latticeCell h N k,
        |lhyProfile c (Submission.BoseGases.eucNorm3 (latticeCenter h N k))
          - lhyProfile c (Submission.BoseGases.eucNorm3 x)|)
      ≤ ∑ k ∈ s, ∫ x in latticeCell h N k,
          32 * c ^ 2 * h * Real.sqrt 3 / (Submission.BoseGases.eucNorm3 x) ^ 3 :=
        Finset.sum_le_sum hcellle
    _ = ∫ x in (⋃ k ∈ s, latticeCell h N k),
          32 * c ^ 2 * h * Real.sqrt 3 / (Submission.BoseGases.eucNorm3 x) ^ 3 := hunion
    _ ≤ ∫ x in T,
          32 * c ^ 2 * h * Real.sqrt 3 / (Submission.BoseGases.eucNorm3 x) ^ 3 := hmono
    _ = 32 * c ^ 2 * h * Real.sqrt 3 * (4 * Real.pi * Real.log ((N : ℝ) / 2 + 1 / 2)) := hTval
    _ ≤ 128 * Real.pi * Real.sqrt 3 * c ^ 2 * h * Real.log (N : ℝ) := hfinal

/-- **Near-region estimate**: the discrepancy of the Riemann sum on the cells whose
centre lies inside the ball of radius `2h√3`. -/
lemma near_part {c h : ℝ} (hc : 0 < c) (hh : 0 < h) {N : ℕ}
    (hdisp : ∀ k k' : Fin 3 → Fin N, k ≠ k' →
      Disjoint (latticeCell h N k) (latticeCell h N k'))
    (hmeas : ∀ k : Fin 3 → Fin N, MeasurableSet (latticeCell h N k))
    (hvol : ∀ k : Fin 3 → Fin N,
      MeasureTheory.volume (latticeCell h N k) = ENNReal.ofReal (h ^ 3))
    (hdist : ∀ k : Fin 3 → Fin N, ∀ x : Fin 3 → ℝ, x ∈ latticeCell h N k →
      |Submission.BoseGases.eucNorm3 x - Submission.BoseGases.eucNorm3 (latticeCenter h N k)|
        ≤ h * Real.sqrt 3 / 2)
    (hhalf : ∀ k : Fin 3 → Fin N,
      Submission.BoseGases.eucNorm3 (latticeCenter h N k) = 0 ∨
        h / 2 ≤ Submission.BoseGases.eucNorm3 (latticeCenter h N k))
    (hsubbox : ∀ k : Fin 3 → Fin N, latticeCell h N k ⊆ latticeBox h N)
    (hintF : MeasureTheory.IntegrableOn
      (fun x : Fin 3 → ℝ => lhyProfile c (Submission.BoseGases.eucNorm3 x))
      (latticeBox h N))
    (hcard : (Finset.univ.filter (fun k : Fin 3 → Fin N =>
        ¬ (2 * h * Real.sqrt 3 ≤ Submission.BoseGases.eucNorm3 (latticeCenter h N k)))).card
          * h ^ 3 ≤ 4 * Real.pi * (4 * h * Real.sqrt 3) ^ 3 / 3)
    (h1 : ∀ r : ℝ, 0 ≤ r → |lhyProfile c r| ≤ c + c ^ 2 / (2 * r ^ 2))
    (hintabs : MeasureTheory.Integrable
      (fun x : Fin 3 → ℝ => |lhyProfile c (Submission.BoseGases.eucNorm3 x)|)
      MeasureTheory.volume) :
    (∑ k ∈ Finset.univ.filter (fun k : Fin 3 → Fin N =>
        ¬ (2 * h * Real.sqrt 3 ≤ Submission.BoseGases.eucNorm3 (latticeCenter h N k))),
      ∫ x in latticeCell h N k,
        |lhyProfile c (Submission.BoseGases.eucNorm3 (latticeCenter h N k))
          - lhyProfile c (Submission.BoseGases.eucNorm3 x)|)
      ≤ 256 * Real.pi * Real.sqrt 3 * c * h ^ 3 + 512 * Real.pi * Real.sqrt 3 * c ^ 2 * h
        + (256 * Real.pi * Real.sqrt 3 * c * h ^ 3 + 8 * Real.pi * Real.sqrt 3 * c ^ 2 * h) := by
  classical
  set s : Finset (Fin 3 → Fin N) := Finset.univ.filter (fun k : Fin 3 → Fin N =>
    ¬ (2 * h * Real.sqrt 3 ≤ Submission.BoseGases.eucNorm3 (latticeCenter h N k))) with hs
  have hmem : ∀ k ∈ s, Submission.BoseGases.eucNorm3 (latticeCenter h N k) < 2 * h * Real.sqrt 3 := by
    intro k hk
    rw [hs] at hk
    exact not_le.mp (Finset.mem_filter.mp hk).2
  -- (A) the value part
  have hterm : ∀ k ∈ s, h ^ 3 * |lhyProfile c (Submission.BoseGases.eucNorm3 (latticeCenter h N k))|
      ≤ c * h ^ 3 + 2 * c ^ 2 * h := by
    intro k hk
    have hbound := h1 (Submission.BoseGases.eucNorm3 (latticeCenter h N k))
      (Submission.BoseGases.eucNorm3_nonneg _)
    rcases hhalf k with h0 | hhalf'
    · rw [h0] at hbound ⊢
      have hval : lhyProfile c 0 = c := by
        simpa using (LatticeModel.lhyProfile_basic hc).1 0 le_rfl
      rw [hval, abs_of_pos hc]
      nlinarith [hh.le, sq_nonneg c]
    · have hρpos : 0 < Submission.BoseGases.eucNorm3 (latticeCenter h N k) :=
        lt_of_lt_of_le (by positivity : (0 : ℝ) < h / 2) hhalf'
      have hρ2 : c ^ 2 / (2 * (Submission.BoseGases.eucNorm3 (latticeCenter h N k)) ^ 2)
          ≤ 2 * c ^ 2 / h ^ 2 := by
        rw [div_le_div_iff₀ (by positivity) (by positivity)]
        have hsq : h ^ 2 ≤ 4 * (Submission.BoseGases.eucNorm3 (latticeCenter h N k)) ^ 2 := by
          nlinarith [hhalf', hh]
        nlinarith [hsq, sq_nonneg c]
      have hb2 : |lhyProfile c (Submission.BoseGases.eucNorm3 (latticeCenter h N k))|
          ≤ c + 2 * c ^ 2 / h ^ 2 := by linarith [hbound, hρ2]
      have hmul := mul_le_mul_of_nonneg_left hb2 (show (0 : ℝ) ≤ h ^ 3 by positivity)
      have hsimp : h ^ 3 * (c + 2 * c ^ 2 / h ^ 2) = c * h ^ 3 + 2 * c ^ 2 * h := by
        field_simp
      linarith [hmul, hsimp.le]
  have hval : (∑ k ∈ s, h ^ 3 * |lhyProfile c (Submission.BoseGases.eucNorm3 (latticeCenter h N k))|)
      ≤ 256 * Real.pi * Real.sqrt 3 * c * h ^ 3 + 512 * Real.pi * Real.sqrt 3 * c ^ 2 * h := by
    have hcard' : (s.card : ℝ) ≤ 256 * Real.pi * Real.sqrt 3 := by
      have hcube : 4 * Real.pi * (4 * h * Real.sqrt 3) ^ 3 / 3
          = 256 * Real.pi * Real.sqrt 3 * h ^ 3 := by
        rw [cube_four_h_sqrt3]
        ring
      have := hcard
      rw [hs] at this
      rw [hcube] at this
      exact le_of_mul_le_mul_right this (by positivity)
    calc (∑ k ∈ s, h ^ 3 * |lhyProfile c (Submission.BoseGases.eucNorm3 (latticeCenter h N k))|)
        ≤ ∑ _k ∈ s, (c * h ^ 3 + 2 * c ^ 2 * h) := Finset.sum_le_sum hterm
      _ = (s.card : ℝ) * (c * h ^ 3 + 2 * c ^ 2 * h) := by
            rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ 256 * Real.pi * Real.sqrt 3 * (c * h ^ 3 + 2 * c ^ 2 * h) :=
            mul_le_mul_of_nonneg_right hcard' (by positivity)
      _ = 256 * Real.pi * Real.sqrt 3 * c * h ^ 3 + 512 * Real.pi * Real.sqrt 3 * c ^ 2 * h :=
            by ring
  -- (B) the integral part
  have hint : (∑ k ∈ s, ∫ x in latticeCell h N k,
        |lhyProfile c (Submission.BoseGases.eucNorm3 x)|)
      ≤ 256 * Real.pi * Real.sqrt 3 * c * h ^ 3 + 8 * Real.pi * Real.sqrt 3 * c ^ 2 * h := by
    have hdisj : (↑s : Set (Fin 3 → Fin N)).Pairwise
        (Function.onFun Disjoint (fun k : Fin 3 → Fin N => latticeCell h N k)) :=
      fun k _ k' _ hne => hdisp k k' hne
    have hintc : ∀ k ∈ s, MeasureTheory.IntegrableOn
        (fun x : Fin 3 → ℝ => |lhyProfile c (Submission.BoseGases.eucNorm3 x)|)
        (latticeCell h N k) MeasureTheory.volume := fun k _ => hintabs.integrableOn
    have hunion : (∑ k ∈ s, ∫ x in latticeCell h N k,
          |lhyProfile c (Submission.BoseGases.eucNorm3 x)|)
        = ∫ x in (⋃ k ∈ s, latticeCell h N k),
          |lhyProfile c (Submission.BoseGases.eucNorm3 x)| :=
      (MeasureTheory.integral_biUnion_finset s (fun k _ => hmeas k) hdisj hintc).symm
    have hsub_ball : (⋃ k ∈ s, latticeCell h N k) ⊆
        {x : Fin 3 → ℝ | Submission.BoseGases.eucNorm3 x ≤ 4 * h * Real.sqrt 3} := by
      intro x hx
      rw [Set.mem_iUnion] at hx
      obtain ⟨k, hx⟩ := hx
      rw [Set.mem_iUnion] at hx
      obtain ⟨hk, hxk⟩ := hx
      have hb := (abs_le.mp (hdist k x hxk)).2
      have hh2 := hmem k hk
      have hρnn := Submission.BoseGases.eucNorm3_nonneg (latticeCenter h N k)
      have h3 : 0 < Real.sqrt 3 := Real.sqrt_pos.mpr (by norm_num)
      simp only [Set.mem_setOf_eq]
      nlinarith [hb, hh2, hh, h3, hρnn]
    calc (∑ k ∈ s, ∫ x in latticeCell h N k,
          |lhyProfile c (Submission.BoseGases.eucNorm3 x)|)
        = ∫ x in (⋃ k ∈ s, latticeCell h N k),
          |lhyProfile c (Submission.BoseGases.eucNorm3 x)| := hunion
      _ ≤ ∫ x in {x : Fin 3 → ℝ | Submission.BoseGases.eucNorm3 x ≤ 4 * h * Real.sqrt 3},
          |lhyProfile c (Submission.BoseGases.eucNorm3 x)| := by
          refine MeasureTheory.setIntegral_mono_set hintabs.integrableOn ?_ ?_
          · filter_upwards with x
            exact abs_nonneg _
          · filter_upwards with x hx
            exact hsub_ball hx
      _ ≤ 4 * Real.pi * (c * (4 * h * Real.sqrt 3) ^ 3 / 3 + c ^ 2 * (4 * h * Real.sqrt 3) / 2) :=
          LatticeModel.integral_ball_abs_lhyProfile_le hc (by positivity) h1
      _ = 256 * Real.pi * Real.sqrt 3 * c * h ^ 3 + 8 * Real.pi * Real.sqrt 3 * c ^ 2 * h := by
          rw [cube_four_h_sqrt3]
          ring
  -- (C) combine
  have hsplit : ∀ k ∈ s, (∫ x in latticeCell h N k,
        |lhyProfile c (Submission.BoseGases.eucNorm3 (latticeCenter h N k))
          - lhyProfile c (Submission.BoseGases.eucNorm3 x)|)
      ≤ h ^ 3 * |lhyProfile c (Submission.BoseGases.eucNorm3 (latticeCenter h N k))|
        + ∫ x in latticeCell h N k, |lhyProfile c (Submission.BoseGases.eucNorm3 x)| := by
    intro k hk
    have hpt : ∀ x ∈ latticeCell h N k,
        |lhyProfile c (Submission.BoseGases.eucNorm3 (latticeCenter h N k))
          - lhyProfile c (Submission.BoseGases.eucNorm3 x)|
        ≤ |lhyProfile c (Submission.BoseGases.eucNorm3 (latticeCenter h N k))|
          + |lhyProfile c (Submission.BoseGases.eucNorm3 x)| := by
      intro x _
      exact abs_sub_le_iff.mpr
        ⟨by linarith [le_abs_self (lhyProfile c (Submission.BoseGases.eucNorm3 (latticeCenter h N k))),
                      neg_le_abs (lhyProfile c (Submission.BoseGases.eucNorm3 x))],
         by linarith [le_abs_self (lhyProfile c (Submission.BoseGases.eucNorm3 x)),
                      neg_le_abs (lhyProfile c (Submission.BoseGases.eucNorm3 (latticeCenter h N k)))]⟩
    have hintL : MeasureTheory.IntegrableOn (fun x : Fin 3 → ℝ =>
        |lhyProfile c (Submission.BoseGases.eucNorm3 (latticeCenter h N k))
          - lhyProfile c (Submission.BoseGases.eucNorm3 x)|) (latticeCell h N k) :=
      IntegrableOn.abs' (hmeas k) ((MeasureTheory.integrableOn_const
        (by rw [hvol k]; exact ENNReal.ofReal_ne_top)).sub (hintF.mono_set (hsubbox k)))
    have hconst : MeasureTheory.IntegrableOn
        (fun _x : Fin 3 → ℝ => |lhyProfile c (Submission.BoseGases.eucNorm3 (latticeCenter h N k))|)
        (latticeCell h N k) :=
      MeasureTheory.integrableOn_const (by rw [hvol k]; exact ENNReal.ofReal_ne_top)
    have hR : MeasureTheory.IntegrableOn (fun x : Fin 3 → ℝ =>
        |lhyProfile c (Submission.BoseGases.eucNorm3 (latticeCenter h N k))|
          + |lhyProfile c (Submission.BoseGases.eucNorm3 x)|) (latticeCell h N k) :=
      hconst.add hintabs.integrableOn
    calc (∫ x in latticeCell h N k,
          |lhyProfile c (Submission.BoseGases.eucNorm3 (latticeCenter h N k))
            - lhyProfile c (Submission.BoseGases.eucNorm3 x)|)
        ≤ ∫ x in latticeCell h N k,
            (|lhyProfile c (Submission.BoseGases.eucNorm3 (latticeCenter h N k))|
              + |lhyProfile c (Submission.BoseGases.eucNorm3 x)|) :=
          MeasureTheory.setIntegral_mono_on hintL hR (hmeas k) hpt
      _ = (∫ x in latticeCell h N k,
              |lhyProfile c (Submission.BoseGases.eucNorm3 (latticeCenter h N k))|)
            + ∫ x in latticeCell h N k,
              |lhyProfile c (Submission.BoseGases.eucNorm3 x)| :=
          MeasureTheory.integral_add hconst hintabs.integrableOn
      _ = h ^ 3 * |lhyProfile c (Submission.BoseGases.eucNorm3 (latticeCenter h N k))|
            + ∫ x in latticeCell h N k,
              |lhyProfile c (Submission.BoseGases.eucNorm3 x)| := by
          rw [MeasureTheory.setIntegral_const, smul_eq_mul]
          have hvr : MeasureTheory.Measure.real MeasureTheory.volume (latticeCell h N k) = h ^ 3 := by
            rw [show MeasureTheory.Measure.real MeasureTheory.volume (latticeCell h N k)
                = (MeasureTheory.volume (latticeCell h N k)).toReal from rfl, hvol k,
              ENNReal.toReal_ofReal (by positivity)]
          rw [hvr]
  calc (∑ k ∈ s, ∫ x in latticeCell h N k,
        |lhyProfile c (Submission.BoseGases.eucNorm3 (latticeCenter h N k))
          - lhyProfile c (Submission.BoseGases.eucNorm3 x)|)
      ≤ ∑ k ∈ s, (h ^ 3 * |lhyProfile c (Submission.BoseGases.eucNorm3 (latticeCenter h N k))|
          + ∫ x in latticeCell h N k, |lhyProfile c (Submission.BoseGases.eucNorm3 x)|) :=
        Finset.sum_le_sum hsplit
    _ = (∑ k ∈ s, h ^ 3 * |lhyProfile c (Submission.BoseGases.eucNorm3 (latticeCenter h N k))|)
          + ∑ k ∈ s, ∫ x in latticeCell h N k,
              |lhyProfile c (Submission.BoseGases.eucNorm3 x)| :=
        Finset.sum_add_distrib
    _ ≤ (256 * Real.pi * Real.sqrt 3 * c * h ^ 3 + 512 * Real.pi * Real.sqrt 3 * c ^ 2 * h)
          + (256 * Real.pi * Real.sqrt 3 * c * h ^ 3 + 8 * Real.pi * Real.sqrt 3 * c ^ 2 * h) :=
        add_le_add hval hint

/-- **The lattice-versus-box estimate**: the Riemann sum over the whole grid differs
from the integral over the enclosing cube by at most the far plus the near contribution. -/
theorem cell_error_le {c : ℝ} (hc : 0 < c) {n : ℕ} (hn : 1 ≤ n) :
    ‖(mesh n) ^ 3 * (∑ k : Fin 3 → Fin (gridN n),
        lhyProfile c (Submission.BoseGases.eucNorm3 (latticeCenter (mesh n) (gridN n) k)))
      - ∫ x in latticeBox (mesh n) (gridN n),
          lhyProfile c (Submission.BoseGases.eucNorm3 x)‖
    ≤ 512 * Real.pi * Real.sqrt 3 * c * (mesh n) ^ 3
      + 520 * Real.pi * Real.sqrt 3 * c ^ 2 * (mesh n)
      + 128 * Real.pi * Real.sqrt 3 * c ^ 2 * (mesh n) * Real.log (gridN n) := by
  classical
  set h := mesh n with hhdef
  set N := gridN n with hNdef
  have hh : 0 < h := mesh_pos n
  have hN : 0 < N := gridN_pos n
  obtain ⟨hmeas, hdisp, hvol, hcover, hdist, hhalf⟩ := LatticeModel.latticeCell_geometry hh hN
  have hsubbox : ∀ k : Fin 3 → Fin N, latticeCell h N k ⊆ latticeBox h N := by
    intro k
    rw [← hcover]
    exact Set.subset_iUnion _ k
  have hglob := integrable_F hc
  have hintF : MeasureTheory.IntegrableOn
      (fun x : Fin 3 → ℝ => lhyProfile c (Submission.BoseGases.eucNorm3 x))
      (latticeBox h N) := hglob.integrableOn
  have hintabs : MeasureTheory.Integrable
      (fun x : Fin 3 → ℝ => |lhyProfile c (Submission.BoseGases.eucNorm3 x)|) := hglob.abs
  have hpb := LatticeModel.lhyProfile_basic hc
  have hid := LatticeModel.sum_sub_setIntegral_eq hh hN hdisp hvol hcover hintF
  have hfar := far_part hc hh hN hdisp hmeas hvol hdist hsubbox hintF
  have hcard : (Finset.univ.filter (fun k : Fin 3 → Fin N =>
      ¬ (2 * h * Real.sqrt 3 ≤ Submission.BoseGases.eucNorm3 (latticeCenter h N k)))).card
        * h ^ 3 ≤ 4 * Real.pi * (4 * h * Real.sqrt 3) ^ 3 / 3 := by
    refine LatticeModel.latticeCells_card_mul_le hh ?_
    intro k hk
    exact not_le.mp (Finset.mem_filter.mp hk).2
  have hnear := near_part hc hh hdisp hmeas hvol hdist hhalf hsubbox hintF hcard hpb.2.1 hintabs
  have hsplit : (∑ k : Fin 3 → Fin N, ∫ x in latticeCell h N k,
        |lhyProfile c (Submission.BoseGases.eucNorm3 (latticeCenter h N k))
          - lhyProfile c (Submission.BoseGases.eucNorm3 x)|)
      = (∑ k ∈ Finset.univ.filter (fun k : Fin 3 → Fin N =>
            2 * h * Real.sqrt 3 ≤ Submission.BoseGases.eucNorm3 (latticeCenter h N k)),
          ∫ x in latticeCell h N k,
            |lhyProfile c (Submission.BoseGases.eucNorm3 (latticeCenter h N k))
              - lhyProfile c (Submission.BoseGases.eucNorm3 x)|)
        + ∑ k ∈ Finset.univ.filter (fun k : Fin 3 → Fin N =>
            ¬ (2 * h * Real.sqrt 3 ≤ Submission.BoseGases.eucNorm3 (latticeCenter h N k))),
          ∫ x in latticeCell h N k,
            |lhyProfile c (Submission.BoseGases.eucNorm3 (latticeCenter h N k))
              - lhyProfile c (Submission.BoseGases.eucNorm3 x)| :=
    (Finset.sum_filter_add_sum_filter_not Finset.univ
      (fun k : Fin 3 → Fin N =>
        2 * h * Real.sqrt 3 ≤ Submission.BoseGases.eucNorm3 (latticeCenter h N k))
      (fun k : Fin 3 → Fin N => ∫ x in latticeCell h N k,
        |lhyProfile c (Submission.BoseGases.eucNorm3 (latticeCenter h N k))
          - lhyProfile c (Submission.BoseGases.eucNorm3 x)|)).symm
  have hsum : (∑ k ∈ Finset.univ.filter (fun k : Fin 3 → Fin N =>
          2 * h * Real.sqrt 3 ≤ Submission.BoseGases.eucNorm3 (latticeCenter h N k)),
        ∫ x in latticeCell h N k,
          |lhyProfile c (Submission.BoseGases.eucNorm3 (latticeCenter h N k))
            - lhyProfile c (Submission.BoseGases.eucNorm3 x)|)
      + ∑ k ∈ Finset.univ.filter (fun k : Fin 3 → Fin N =>
          ¬ (2 * h * Real.sqrt 3 ≤ Submission.BoseGases.eucNorm3 (latticeCenter h N k))),
        ∫ x in latticeCell h N k,
          |lhyProfile c (Submission.BoseGases.eucNorm3 (latticeCenter h N k))
            - lhyProfile c (Submission.BoseGases.eucNorm3 x)|
      ≤ 512 * Real.pi * Real.sqrt 3 * c * h ^ 3 + 520 * Real.pi * Real.sqrt 3 * c ^ 2 * h
        + 128 * Real.pi * Real.sqrt 3 * c ^ 2 * h * Real.log (N : ℝ) := by
    have h1 := hnear
    have h2 := hfar
    linarith [h1, h2]
  calc ‖h ^ 3 * (∑ k : Fin 3 → Fin N,
        lhyProfile c (Submission.BoseGases.eucNorm3 (latticeCenter h N k)))
      - ∫ x in latticeBox h N, lhyProfile c (Submission.BoseGases.eucNorm3 x)‖
      = ‖∑ k : Fin 3 → Fin N, ∫ x in latticeCell h N k,
          (lhyProfile c (Submission.BoseGases.eucNorm3 (latticeCenter h N k))
            - lhyProfile c (Submission.BoseGases.eucNorm3 x))‖ := by rw [hid]
    _ ≤ ∑ k : Fin 3 → Fin N, ‖∫ x in latticeCell h N k,
          (lhyProfile c (Submission.BoseGases.eucNorm3 (latticeCenter h N k))
            - lhyProfile c (Submission.BoseGases.eucNorm3 x))‖ := norm_sum_le _ _
    _ ≤ ∑ k : Fin 3 → Fin N, ∫ x in latticeCell h N k,
          |lhyProfile c (Submission.BoseGases.eucNorm3 (latticeCenter h N k))
            - lhyProfile c (Submission.BoseGases.eucNorm3 x)| :=
        Finset.sum_le_sum (fun k _ => norm_setIntegral_le _)
    _ = _ := hsplit
    _ ≤ 512 * Real.pi * Real.sqrt 3 * c * h ^ 3 + 520 * Real.pi * Real.sqrt 3 * c ^ 2 * h
        + 128 * Real.pi * Real.sqrt 3 * c ^ 2 * h * Real.log (N : ℝ) := hsum

/-- **Tail estimate**: the difference between the integral over the enclosing cube and
the full-space integral. -/
lemma tail_le {c : ℝ} (hc : 0 < c) {n : ℕ} (hn : 1 ≤ n) :
    ‖(∫ x in latticeBox (mesh n) (gridN n),
        lhyProfile c (Submission.BoseGases.eucNorm3 x))
      - ∫ x : Fin 3 → ℝ, lhyProfile c (Submission.BoseGases.eucNorm3 x)‖
      ≤ 4 * c ^ 3 / ((n : ℝ) + 1) := by
  set h := mesh n with hhdef
  set N := gridN n with hNdef
  have hh : 0 < h := mesh_pos n
  have hglob := integrable_F hc
  have hboxmeas : MeasurableSet (latticeBox h N) := by
    rw [latticeBox]
    exact MeasurableSet.pi Set.countable_univ (fun j _ => measurableSet_Ico)
  have hcompl := MeasureTheory.integral_add_compl hboxmeas hglob
  have hkey : ‖(∫ x in latticeBox h N, lhyProfile c (Submission.BoseGases.eucNorm3 x))
      - ∫ x : Fin 3 → ℝ, lhyProfile c (Submission.BoseGases.eucNorm3 x)‖
      = ‖∫ x in (latticeBox h N)ᶜ, lhyProfile c (Submission.BoseGases.eucNorm3 x)‖ := by
    rw [show (∫ x in latticeBox h N, lhyProfile c (Submission.BoseGases.eucNorm3 x))
        - ∫ x : Fin 3 → ℝ, lhyProfile c (Submission.BoseGases.eucNorm3 x)
        = -∫ x in (latticeBox h N)ᶜ, lhyProfile c (Submission.BoseGases.eucNorm3 x) by linarith]
    rw [norm_neg]
  rw [hkey]
  have hN2 : (2 : ℝ) ≤ N := by
    rw [hNdef, gridN]
    have : (2 : ℕ) ≤ (n + 1) * (n + 1) := by nlinarith
    exact_mod_cast this
  have hRpos : 0 < h * (N : ℝ) / 2 - h / 2 := by nlinarith [hh, hN2]
  have hsub : (latticeBox h N)ᶜ ⊆
      {x : Fin 3 → ℝ | h * (N : ℝ) / 2 - h / 2 ≤ Submission.BoseGases.eucNorm3 x} := by
    intro x hx
    rw [Set.mem_compl_iff, latticeBox, Set.mem_univ_pi] at hx
    push_neg at hx
    obtain ⟨j, hj⟩ := hx
    rw [Set.mem_Ico, not_and_or] at hj
    have hcoord : h * (N : ℝ) / 2 - h / 2 ≤ |x j| := by
      rcases hj with hj | hj
      · rw [abs_of_neg (by linarith)]
        linarith
      · rw [abs_of_nonneg (by linarith)]
        linarith
    exact hcoord.trans (abs_apply_le_eucNorm3 x j)
  have hNv : (N : ℝ) = ((n : ℝ) + 1) ^ 2 := by
    rw [hNdef, gridN]
    push_cast
    ring
  have hmv : h = 2 * Real.pi / ((n : ℝ) + 1) := rfl
  have hden : Real.pi * ((n : ℝ) + 1) ≤ 2 * (h * (N : ℝ) / 2 - h / 2) := by
    rw [hNv, hmv]
    have hnp : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    field_simp
    nlinarith [Real.pi_pos, hnp]
  have hle : (n : ℝ) + 1 ≤ 2 * (h * (N : ℝ) / 2 - h / 2) := by
    have hnp : (1 : ℝ) ≤ (n : ℝ) + 1 := by
      have : (0:ℝ) ≤ (n:ℝ) := Nat.cast_nonneg n
      linarith
    nlinarith [hden, Real.pi_gt_three, hnp]
  calc ‖∫ x in (latticeBox h N)ᶜ, lhyProfile c (Submission.BoseGases.eucNorm3 x)‖
      ≤ ∫ x in (latticeBox h N)ᶜ, |lhyProfile c (Submission.BoseGases.eucNorm3 x)| := by
        simpa only [Real.norm_eq_abs] using norm_setIntegral_le _
    _ ≤ ∫ x in {x : Fin 3 → ℝ | h * (N : ℝ) / 2 - h / 2 ≤ Submission.BoseGases.eucNorm3 x},
          |lhyProfile c (Submission.BoseGases.eucNorm3 x)| := by
        refine MeasureTheory.setIntegral_mono_set hglob.abs.integrableOn ?_ ?_
        · filter_upwards with x
          exact abs_nonneg _
        · filter_upwards with x hx
          exact hsub hx
    _ ≤ 4 * Real.pi * (c ^ 3 / (2 * (h * (N : ℝ) / 2 - h / 2))) :=
        LatticeModel.integral_tail_abs_lhyProfile_le hc hRpos (LatticeModel.lhyProfile_basic hc).2.2
    _ ≤ 4 * c ^ 3 / ((n : ℝ) + 1) := by
        have hL : 4 * Real.pi * (c ^ 3 / (2 * (h * (N : ℝ) / 2 - h / 2)))
            = 4 * Real.pi * c ^ 3 / (2 * (h * (N : ℝ) / 2 - h / 2)) := by ring
        rw [hL, div_le_div_iff₀ (by positivity) (by positivity)]
        have hnn : (0 : ℝ) ≤ 4 * c ^ 3 := by positivity
        have := mul_le_mul_of_nonneg_left hden hnn
        nlinarith [this]

-- ============================================================
-- Asymptotics of the error majorant
-- ============================================================

lemma tendsto_shift : Tendsto (fun n : ℕ => n + 1) atTop atTop :=
  tendsto_atTop_mono (fun n => Nat.le_succ n) tendsto_id

lemma tendsto_mesh : Tendsto mesh atTop (nhds 0) := by
  have hcomp : Tendsto (fun n : ℕ => (2 * Real.pi) / (((n + 1 : ℕ)) : ℝ)) atTop (nhds 0) :=
    (tendsto_const_div_atTop_nhds_zero_nat (2 * Real.pi)).comp
      (tendsto_natCast_atTop_atTop.comp tendsto_shift)
  have heq : mesh = fun n : ℕ => (2 * Real.pi) / (((n + 1 : ℕ)) : ℝ) := by
    funext n
    rw [mesh]
    push_cast
    ring
  rw [heq]
  exact hcomp

lemma tendsto_mesh_cube : Tendsto (fun n : ℕ => (mesh n) ^ 3) atTop (nhds 0) := by
  simpa using tendsto_mesh.pow 3

lemma tendsto_mesh_mul_log :
    Tendsto (fun n : ℕ => (mesh n) * Real.log (gridN n)) atTop (nhds 0) := by
  have hlog : Tendsto (fun m : ℕ => Real.log (m : ℝ) / (m : ℝ)) atTop (nhds 0) :=
    Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp tendsto_natCast_atTop_atTop
  have h2 := hlog.comp tendsto_shift
  have heq : (fun n : ℕ => (mesh n) * Real.log (gridN n))
      = fun n : ℕ => 4 * Real.pi *
          (Real.log (((n + 1 : ℕ)) : ℝ) / (((n + 1 : ℕ)) : ℝ)) := by
    funext n
    have hgrid : ((gridN n : ℕ) : ℝ) = ((n + 1 : ℕ) : ℝ) ^ 2 := by
      simp only [gridN]
      push_cast
      ring
    have hmesh : mesh n = 2 * Real.pi / ((n + 1 : ℕ) : ℝ) := by
      rw [mesh]
      push_cast
      ring
    rw [hmesh, hgrid, Real.log_pow]
    push_cast
    have hnp : ((n : ℝ) + 1) ≠ 0 := by positivity
    field_simp
    ring
  rw [heq]
  simpa using h2.const_mul (4 * Real.pi)

/-- The error majorant tends to zero. -/
lemma tendsto_latticeErr {c : ℝ} : Tendsto (latticeErr c) atTop (nhds 0) := by
  have hcast : Tendsto (fun n : ℕ => ((n + 1 : ℕ) : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp tendsto_shift
  have h1 : Tendsto (fun n : ℕ => 512 * Real.pi * Real.sqrt 3 * c * (mesh n) ^ 3)
      atTop (nhds 0) := by
    simpa using tendsto_mesh_cube.const_mul (512 * Real.pi * Real.sqrt 3 * c)
  have h2 : Tendsto (fun n : ℕ => 520 * Real.pi * Real.sqrt 3 * c ^ 2 * (mesh n))
      atTop (nhds 0) := by
    simpa using tendsto_mesh.const_mul (520 * Real.pi * Real.sqrt 3 * c ^ 2)
  have h3 : Tendsto (fun n : ℕ =>
      128 * Real.pi * Real.sqrt 3 * c ^ 2 * ((mesh n) * Real.log (gridN n)))
      atTop (nhds 0) := by
    simpa using tendsto_mesh_mul_log.const_mul (128 * Real.pi * Real.sqrt 3 * c ^ 2)
  have h4 : Tendsto (fun n : ℕ => 4 * c ^ 3 / ((n : ℝ) + 1)) atTop (nhds 0) := by
    have hcomp : Tendsto (fun n : ℕ => 4 * c ^ 3 / (((n + 1 : ℕ)) : ℝ)) atTop (nhds 0) :=
      (tendsto_const_div_atTop_nhds_zero_nat (4 * c ^ 3)).comp
        (tendsto_natCast_atTop_atTop.comp tendsto_shift)
    have heq : (fun n : ℕ => 4 * c ^ 3 / ((n : ℝ) + 1))
        = fun n : ℕ => 4 * c ^ 3 / (((n + 1 : ℕ)) : ℝ) := by
      funext n
      push_cast
      ring
    rw [heq]
    exact hcomp
  have hsum : Tendsto (fun n : ℕ => 512 * Real.pi * Real.sqrt 3 * c * (mesh n) ^ 3
      + 520 * Real.pi * Real.sqrt 3 * c ^ 2 * (mesh n)
      + 128 * Real.pi * Real.sqrt 3 * c ^ 2 * ((mesh n) * Real.log (gridN n))
      + 4 * c ^ 3 / ((n : ℝ) + 1)) atTop (nhds 0) := by
    simpa only [add_zero] using ((h1.add h2).add h3).add h4
  have heq : latticeErr c = fun n : ℕ => 512 * Real.pi * Real.sqrt 3 * c * (mesh n) ^ 3
      + 520 * Real.pi * Real.sqrt 3 * c ^ 2 * (mesh n)
      + 128 * Real.pi * Real.sqrt 3 * c ^ 2 * ((mesh n) * Real.log (gridN n))
      + 4 * c ^ 3 / ((n : ℝ) + 1) := by
    funext n
    simp only [latticeErr]
    ring
  rw [heq]
  exact hsum

end

end Work.BoseBox
