import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Submission.Work.FTS.EllSol.ShiftFT.ShiftPrimDefs
import Submission.Work.FTS.EllSol.ShiftFT.AtwoAux.Defs
import Submission.Work.FTS.EllSol.ShiftFT.Aux2.gcTail
import Submission.Work.RPFresh.integral_mul_sq_le_sq_mul_sq

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllSol.ShiftFT

open MeasureTheory Set Filter
open scoped Real Topology

noncomputable section

set_option autoImplicit false


/-- A definite integral over an interval is the set integral over the closed interval. -/
theorem intervalIntegral_eq_setIntegral_Icc (a b : ℝ) (hab : a ≤ b) (f : ℝ → ℝ) :
    (∫ s in a..b, f s) = ∫ s in Set.Icc a b, f s := by
  rw [intervalIntegral.integral_of_le hab, MeasureTheory.integral_Icc_eq_integral_Ioc]

/-- The restricted product measure on the half-strip `ℝ × Iθ` is the product of the line
measure with the (restricted) angular measure. -/
theorem uTrAtwo_prodRestrict_Iθ :
    ((volume : Measure (ℝ × ℝ))).restrict (Set.univ ×ˢ Work.Spaces.Iθ)
      = (volume : Measure ℝ).prod ((volume : Measure ℝ).restrict Work.Spaces.Iθ) := by
  rw [MeasureTheory.Measure.volume_eq_prod, ← MeasureTheory.Measure.prod_restrict,
    MeasureTheory.Measure.restrict_univ]

/-- The coefficient `phiTr' · chi + 2 · phiTr · chi'` of `L_b u` in `W` is bounded by
`Kd/N + 2·Kd/(4096·N)`. -/
theorem abs_coeff_L1_le (N : ℝ) {Kd : ℝ} (hKd : ∀ t : ℝ, |deriv Trunc.tk t| ≤ Kd)
    (hN : 0 < N) (t : ℝ) :
    |phiTr N t * deriv (Trunc.chi N) t + 2 * deriv (phiTr N) t * Trunc.chi N t|
      ≤ Kd / N + 2 * (Kd / (4096 * N)) := by
  have h1 : |deriv (Trunc.chi N) t| ≤ Kd / N := Trunc.abs_deriv_chi_le hKd hN t
  have h2 : |deriv (phiTr N) t| ≤ Kd / (4096 * N) := abs_deriv_phiTr_le N hKd hN
  have h3 : |Trunc.chi N t| ≤ 1 := by
    rw [abs_of_nonneg (Trunc.chi_nonneg N t)]; exact Trunc.chi_le_one N t
  have h4 : |phiTr N t| ≤ 1 := by
    rw [abs_of_nonneg (phiTr_nonneg N t)]; exact phiTr_le_one N t
  have hKd0 : 0 ≤ Kd := le_trans (abs_nonneg _) (hKd 0)
  have hN4 : 0 < 4096 * N := by linarith
  have hb0 : 0 ≤ Kd / (4096 * N) := div_nonneg hKd0 (le_of_lt hN4)
  have hm1 : |phiTr N t * deriv (Trunc.chi N) t| ≤ 1 * (Kd / N) := by
    rw [abs_mul]
    exact mul_le_mul h4 h1 (abs_nonneg _) (by norm_num)
  have hm2 : |2 * deriv (phiTr N) t * Trunc.chi N t| ≤ 2 * (Kd / (4096 * N)) := by
    rw [abs_mul, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
    have h5 : |deriv (phiTr N) t| * |Trunc.chi N t| ≤ (Kd / (4096 * N)) * 1 :=
      mul_le_mul h2 h3 (abs_nonneg _) hb0
    linarith
  calc |phiTr N t * deriv (Trunc.chi N) t + 2 * deriv (phiTr N) t * Trunc.chi N t|
      ≤ |phiTr N t * deriv (Trunc.chi N) t| + |2 * deriv (phiTr N) t * Trunc.chi N t| :=
        abs_add_le _ _
    _ ≤ 1 * (Kd / N) + 2 * (Kd / (4096 * N)) := add_le_add hm1 hm2
    _ = Kd / N + 2 * (Kd / (4096 * N)) := by ring

/-- Cauchy–Schwarz on a window `Icc a b` of length `b - a ≤ 4N`: the square of the `L¹`-norm
of a continuous function is bounded by `4N` times its `L²`-norm. -/
theorem window_l1_sq_le (N : ℝ) (hN : 0 < N) {g : ℝ → ℝ}
    (hg : Continuous g) {a b : ℝ} (ha : a ≤ b) (hlen : b - a ≤ 4 * N) :
    (∫ s in Set.Icc a b, |g s|) ^ 2 ≤ 4 * N * ∫ s in Set.Icc a b, (g s) ^ 2 := by
  obtain ⟨C, hC⟩ := (isCompact_Icc (a := a) (b := b)).exists_bound_of_continuousOn
    hg.continuousOn
  have hfin : volume (Set.Icc a b) ≠ ⊤ := by
    rw [Real.volume_Icc]
    exact ENNReal.ofReal_ne_top
  have hconst : Integrable (fun s : ℝ => g s ^ 2) (volume.restrict (Set.Icc a b)) := by
    refine Integrable.mono' (g := fun _ : ℝ => C ^ 2)
      (integrableOn_const (C := C ^ 2) hfin) (hg.aestronglyMeasurable.pow 2) ?_
    filter_upwards [ae_restrict_mem measurableSet_Icc] with s hs
    rw [Real.norm_of_nonneg (sq_nonneg _)]
    have h1 : |g s| ≤ C := by simpa [Real.norm_eq_abs] using hC s hs
    have h2 : |g s| ^ 2 ≤ C ^ 2 := pow_le_pow_left₀ (abs_nonneg _) h1 2
    rwa [sq_abs] at h2
  have hint_abs : Integrable (fun s : ℝ => |g s| ^ 2) (volume.restrict (Set.Icc a b)) :=
    hconst.congr (by filter_upwards with s; rw [sq_abs])
  have hint_one : Integrable (fun s : ℝ => (1 : ℝ) ^ 2) (volume.restrict (Set.Icc a b)) :=
    integrableOn_const (C := (1 : ℝ) ^ 2) hfin
  have hcs := Work.RPFresh.integral_mul_sq_le_sq_mul_sq (volume.restrict (Set.Icc a b))
    (f := fun s => |g s|) (h := fun _ => (1 : ℝ)) hg.abs.aestronglyMeasurable
    aestronglyMeasurable_const hint_abs hint_one
  have hsq : (∫ s in Set.Icc a b, |g s| ^ 2) = ∫ s in Set.Icc a b, (g s) ^ 2 :=
    MeasureTheory.integral_congr_ae (by filter_upwards with s; rw [sq_abs])
  have hone : (∫ _ in Set.Icc a b, (1 : ℝ) ^ 2) = b - a := by
    rw [show (fun _ : ℝ => (1 : ℝ) ^ 2) = (fun _ => (1 : ℝ)) from by funext s; norm_num]
    rw [MeasureTheory.setIntegral_const, Real.volume_real_Icc_of_le ha]
    simp
  rw [hsq, hone] at hcs
  have hnn : 0 ≤ ∫ s in Set.Icc a b, (g s) ^ 2 :=
    MeasureTheory.integral_nonneg (fun s => sq_nonneg _)
  calc (∫ s in Set.Icc a b, |g s|) ^ 2
      ≤ (∫ s in Set.Icc a b, (g s) ^ 2) * (b - a) := by simpa [one_mul] using hcs
    _ ≤ (∫ s in Set.Icc a b, (g s) ^ 2) * (4 * N) := mul_le_mul_of_nonneg_left hlen hnn
    _ = 4 * N * ∫ s in Set.Icc a b, (g s) ^ 2 := by ring

/-- The dominating function of the estimate: the three pointwise bounds for the three pieces
of `W`, each carrying the weight `wE`. -/
def uTrAtwo_D (N b : ℝ) (u : ℝ → ℝ → ℝ) (Kd : ℝ) (p : ℝ × ℝ) : ℝ :=
  3 * ((uTrAtwo_L2 b u p.1 p.2) ^ 2 * Work.FTS.EllSol.FlatFT.wE p.2)
    + 3 * (Kd / N + 2 * (Kd / (4096 * N))) ^ 2
        * ((uTrAtwo_L1 b u p.1 p.2) ^ 2 * Work.FTS.EllSol.FlatFT.wE p.2)
    + 3 * (deriv (deriv (phiTr N)) p.1) ^ 2
        * (4 * N * ((∫ s in Set.Icc (-(2 * N)) (2 * N), (uTrAtwo_L1 b u s p.2) ^ 2)
            * Work.FTS.EllSol.FlatFT.wE p.2))

/-- The tail bound for the third piece of `W`: `(phiTr'' · Gc)²` is dominated by
`(phiTr'')²` times the window `L²`-norm of `L_b u`.  This is where the truncation is used:
`phiTr''` vanishes on `|t| < 4096N` and `Gc` vanishes (a.e.) beyond the window `|t| ≥ 2N`. -/
theorem uTrAtwo_phiTr_Gc_sq_le (N b : ℝ) (u : ℝ → ℝ → ℝ) (hb : 0 ≤ b) (hN : 0 < N)
    (hu : ContDiffOn ℝ 2 (Function.uncurry u) (Set.univ ×ˢ Set.Ioo 0 (Real.pi / 2))) :
    ∀ t θ, θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) →
      (deriv (deriv (phiTr N)) t * Gc N b u t θ) ^ 2
        ≤ (deriv (deriv (phiTr N)) t) ^ 2 *
          (4 * N * ∫ s in Set.Icc (-(2 * N)) (2 * N), (uTrAtwo_L1 b u s θ) ^ 2) := by
  intro t θ hθ
  have hnn : 0 ≤ 4 * N * ∫ s in Set.Icc (-(2 * N)) (2 * N), (uTrAtwo_L1 b u s θ) ^ 2 :=
    mul_nonneg (by linarith) (MeasureTheory.integral_nonneg (fun s => sq_nonneg _))
  rcases lt_or_ge |t| (4096 * N) with hlt | hge
  · rw [deriv2_phiTr_eq_zero_of_abs_lt hN hlt]
    nlinarith [sq_nonneg (deriv (deriv (phiTr N)) t), hnn]
  · have h2N : 2 * N ≤ |t| := by linarith
    rcases le_or_gt 0 t with ht0 | ht0
    · rw [abs_of_nonneg ht0] at hge
      have hz : Gc N b u t θ = 0 := (Aux2.gcTail N b u hb hN hu).2.2 t θ hθ (by linarith)
      rw [hz]
      nlinarith [sq_nonneg (deriv (deriv (phiTr N)) t), hnn]
    · have htle : t ≤ -(2 * N) := by
        rw [abs_of_neg ht0] at hge
        linarith
      have hb2 := (Aux2.gcTail N b u hb hN hu).2.1 t θ hθ htle
      rw [intervalIntegral_eq_setIntegral_Icc (-(2 * N)) (2 * N) (by linarith)] at hb2
      simp only [uTrAtwo_L1] at hb2 ⊢
      calc (deriv (deriv (phiTr N)) t * Gc N b u t θ) ^ 2
          = (deriv (deriv (phiTr N)) t) ^ 2 * (Gc N b u t θ) ^ 2 := by ring
        _ ≤ (deriv (deriv (phiTr N)) t) ^ 2 *
              (4 * N * ∫ s in Set.Icc (-(2 * N)) (2 * N),
                (Work.Spaces.pz u s θ - b * u s θ) ^ 2) :=
            mul_le_mul_of_nonneg_left hb2 (sq_nonneg _)

/-- The pointwise bound `W² · wE ≤ D` on the open strip. -/
theorem uTrAtwo_W_sq_le_D (N b : ℝ) (u : ℝ → ℝ → ℝ) (hb : 0 ≤ b) (hN : 0 < N)
    (hu : ContDiffOn ℝ 2 (Function.uncurry u) (Set.univ ×ˢ Set.Ioo 0 (Real.pi / 2)))
    {Kd : ℝ} (hKd : ∀ t : ℝ, |deriv Trunc.tk t| ≤ Kd) (hKd0 : 0 ≤ Kd) :
    ∀ p : ℝ × ℝ, p.2 ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) →
      (uTrAtwo_W N b u p) ^ 2 * Work.FTS.EllSol.FlatFT.wE p.2 ≤ uTrAtwo_D N b u Kd p := by
  intro p hp
  obtain ⟨t, θ⟩ := p
  have hθI : θ ∈ Work.Spaces.Iθ := Set.Ioo_subset_Icc_self hp
  have hwE : 0 ≤ Work.FTS.EllSol.FlatFT.wE θ := Work.FTS.EllSol.FlatFT.wE_nonneg hθI
  set P : ℝ := uTrAtwo_L2 b u t θ with hP
  set Q : ℝ := uTrAtwo_L1 b u t θ with hQ
  set Rr : ℝ := deriv (deriv (phiTr N)) t with hR
  set Wv : ℝ := ∫ s in Set.Icc (-(2 * N)) (2 * N), uTrAtwo_L1 b u s θ ^ 2 with hW
  set cc : ℝ := Kd / N + 2 * (Kd / (4096 * N)) with hcc
  have hA : (phiTr N t * Work.FTS.EllSol.Trunc.chi N t * P) ^ 2 ≤ P ^ 2 := by
    have h1 : |phiTr N t * Work.FTS.EllSol.Trunc.chi N t| ≤ 1 := by
      rw [abs_mul]
      refine mul_le_one₀ ?_ (abs_nonneg _) ?_
      · rw [abs_of_nonneg (phiTr_nonneg N t)]; exact phiTr_le_one N t
      · rw [abs_of_nonneg (Trunc.chi_nonneg N t)]; exact Trunc.chi_le_one N t
    have h2 : (phiTr N t * Work.FTS.EllSol.Trunc.chi N t) ^ 2 ≤ 1 := by
      nlinarith [h1, abs_nonneg (phiTr N t * Work.FTS.EllSol.Trunc.chi N t),
        sq_abs (phiTr N t * Work.FTS.EllSol.Trunc.chi N t)]
    nlinarith [h2, sq_nonneg P]
  have hB : ((phiTr N t * deriv (Trunc.chi N) t + 2 * deriv (phiTr N) t * Trunc.chi N t)
        * Q) ^ 2 ≤ cc ^ 2 * Q ^ 2 := by
    have h1 := abs_coeff_L1_le N hKd hN t
    have h2 : (phiTr N t * deriv (Trunc.chi N) t + 2 * deriv (phiTr N) t * Trunc.chi N t) ^ 2
        ≤ cc ^ 2 := by
      rw [hcc]
      nlinarith [h1, abs_nonneg (phiTr N t * deriv (Trunc.chi N) t
        + 2 * deriv (phiTr N) t * Trunc.chi N t),
        sq_abs (phiTr N t * deriv (Trunc.chi N) t + 2 * deriv (phiTr N) t * Trunc.chi N t)]
    nlinarith [h2, sq_nonneg Q]
  have hC : (Rr * Gc N b u t θ) ^ 2 ≤ Rr ^ 2 * (4 * N * Wv) := by
    rw [hR, hW]
    exact uTrAtwo_phiTr_Gc_sq_le N b u hb hN hu t θ hp
  have hkey : (phiTr N t * Work.FTS.EllSol.Trunc.chi N t * P
        + (phiTr N t * deriv (Trunc.chi N) t + 2 * deriv (phiTr N) t * Trunc.chi N t) * Q
        + Rr * Gc N b u t θ) ^ 2 ≤ 3 * (P ^ 2 + cc ^ 2 * Q ^ 2 + Rr ^ 2 * (4 * N * Wv)) := by
    have h3 := Work.FTS.EllSol.Trunc.three_sq_le
      (phiTr N t * Work.FTS.EllSol.Trunc.chi N t * P)
      ((phiTr N t * deriv (Trunc.chi N) t + 2 * deriv (phiTr N) t * Trunc.chi N t) * Q)
      (Rr * Gc N b u t θ)
    nlinarith [h3, hA, hB, hC]
  rw [uTrAtwo_W, uTrAtwo_D]
  nlinarith [hkey, hwE]

end

end Work.FTS.EllSol.ShiftFT
