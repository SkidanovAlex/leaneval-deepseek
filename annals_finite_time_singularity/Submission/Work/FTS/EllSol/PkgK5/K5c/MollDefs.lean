/-
Work module for the Elgindi project: the *trace-class* open-quadrant interpolation.

Vocabulary for the mollification transfer proving the open-quadrant (trace-vanishing)
version of the paper's §7 interpolation estimate.  Ingredients:

* `sBump` / `sMass` / `sKer` : a smooth even bump supported in `[-1,1]` and its normalised
  rescaling of total mass `1`;
* `Qext` : the doubly-odd (about `0` and `π/2`) extension of a slice (valid on `(-π/2, π)`);
* `thMoll` : the angular mollification `∫ ρ_ε(θ - s) Qext u z s ds` of the datum `u`;
* `zmoll` : the logarithmic-radial mollification of the angular mollification.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.EllipticEst.ThetaPoincareDefs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllSol.PkgK5.K5c

/-! ## The smooth bump -/

/-- The standard smooth bump `T(1 - t²)`, supported in `[-1,1]`. -/
def sBump (t : ℝ) : ℝ := Real.smoothTransition (1 - t ^ 2)

theorem sBump_nonneg (t : ℝ) : 0 ≤ sBump t := by
  unfold sBump
  by_cases h : 1 - t ^ 2 ≤ 0
  · rw [Real.smoothTransition.zero_of_nonpos h]
  · exact (Real.smoothTransition.pos_of_pos (not_le.mp h)).le

theorem sBump_pos_of_abs_lt_one {t : ℝ} (ht : |t| < 1) : 0 < sBump t := by
  unfold sBump
  refine Real.smoothTransition.pos_of_pos ?_
  rw [abs_lt] at ht
  nlinarith [ht.1, ht.2]

theorem sBump_eq_zero_of_one_le_abs {t : ℝ} (ht : 1 ≤ |t|) : sBump t = 0 := by
  unfold sBump
  refine Real.smoothTransition.zero_of_nonpos ?_
  have h : (1 : ℝ) ≤ t ^ 2 := by
    have h2 : |t| ^ 2 = t ^ 2 := sq_abs t
    nlinarith [abs_nonneg t, ht]
  linarith

theorem sBump_even (t : ℝ) : sBump (-t) = sBump t := by
  unfold sBump
  rw [neg_sq]

theorem sBump_le_one (t : ℝ) : sBump t ≤ 1 := by
  unfold sBump
  by_cases h : 1 - t ^ 2 ≤ 0
  · rw [Real.smoothTransition.zero_of_nonpos h]; norm_num
  · by_cases h1 : 1 ≤ 1 - t ^ 2
    · rw [Real.smoothTransition.one_of_one_le h1]
    · exact Real.smoothTransition.le_one _

theorem sBump_continuous : Continuous sBump :=
  Real.smoothTransition.continuous.comp (by fun_prop)

/-- The total mass of the bump. -/
def sMass : ℝ := ∫ t in (-1 : ℝ)..1, sBump t

theorem sMass_pos : 0 < sMass := by
  rw [sMass]
  refine (intervalIntegral.integral_pos_iff_support_of_nonneg_ae
    (μ := MeasureTheory.volume) (a := (-1 : ℝ)) (b := 1)
    (Filter.Eventually.of_forall fun t => sBump_nonneg t)
    (sBump_continuous.intervalIntegrable (-1) 1)).mpr ⟨by norm_num, ?_⟩
  have hsub : Set.Ioo (0 : ℝ) 1 ⊆ Function.support sBump ∩ Set.Ioc (-1 : ℝ) 1 := by
    intro t ht
    refine ⟨Function.mem_support.mpr (ne_of_gt (sBump_pos_of_abs_lt_one ?_)),
      ⟨by linarith [ht.1], le_of_lt ht.2⟩⟩
    rw [abs_lt]
    exact ⟨by linarith [ht.1], by linarith [ht.2]⟩
  have hmono : MeasureTheory.volume (Set.Ioo (0 : ℝ) 1)
      ≤ MeasureTheory.volume (Function.support sBump ∩ Set.Ioc (-1 : ℝ) 1) :=
    measure_mono hsub
  have hpos : (0 : ENNReal) < MeasureTheory.volume (Set.Ioo (0 : ℝ) 1) := by
    rw [Real.volume_Ioo]; norm_num
  exact lt_of_lt_of_le hpos hmono

theorem sBump_eq_indicator : sBump = Set.indicator (Set.Ioc (-1 : ℝ) 1) sBump := by
  funext t
  by_cases ht : t ∈ Set.Ioc (-1 : ℝ) 1
  · rw [Set.indicator_of_mem ht]
  · rw [Set.indicator_of_notMem ht]
    rw [Set.mem_Ioc, not_and_or] at ht
    rcases ht with h | h
    · exact sBump_eq_zero_of_one_le_abs (le_trans (by linarith) (neg_le_abs t))
    · exact sBump_eq_zero_of_one_le_abs (le_trans (by linarith) (le_abs_self t))

theorem sMass_eq_integral : (∫ t : ℝ, sBump t) = sMass := by
  rw [sMass, intervalIntegral.integral_of_le (show (-1 : ℝ) ≤ 1 by norm_num)]
  conv_lhs => rw [sBump_eq_indicator]
  exact MeasureTheory.integral_indicator (μ := MeasureTheory.volume)
    (f := (sBump : ℝ → ℝ)) (s := Set.Ioc (-1 : ℝ) 1) measurableSet_Ioc

/-- The normalised bump of radius `ε`. -/
def sKer (ε t : ℝ) : ℝ := (ε * sMass)⁻¹ * sBump (t / ε)

theorem sKer_nonneg {ε : ℝ} (hε : 0 < ε) (t : ℝ) : 0 ≤ sKer ε t := by
  rw [sKer]
  exact mul_nonneg (inv_nonneg.mpr (mul_nonneg hε.le sMass_pos.le)) (sBump_nonneg _)

theorem sKer_eq_zero_of_le_abs {ε : ℝ} (hε : 0 < ε) {t : ℝ} (ht : ε ≤ |t|) :
    sKer ε t = 0 := by
  rw [sKer, sBump_eq_zero_of_one_le_abs ?_, mul_zero]
  rw [abs_div, abs_of_pos hε, le_div_iff₀ hε, one_mul]
  exact ht

theorem sKer_even (ε t : ℝ) : sKer ε (-t) = sKer ε t := by
  simp only [sKer, neg_div, sBump_even]

theorem sKer_integral_eq_one {ε : ℝ} (hε : 0 < ε) : (∫ t : ℝ, sKer ε t) = 1 := by
  have h1 : (∫ t : ℝ, sBump (t / ε)) = ε * sMass := by
    have h3 : (∫ t : ℝ, sBump (t / ε)) = ∫ t : ℝ, sBump (ε⁻¹ * t) := by
      refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
      show sBump (t / ε) = sBump (ε⁻¹ * t)
      rw [div_eq_inv_mul, mul_comm]
    rw [h3, MeasureTheory.Measure.integral_comp_mul_left (g := sBump) (a := ε⁻¹), inv_inv,
      abs_of_pos hε, sMass_eq_integral, smul_eq_mul, mul_comm]
  unfold sKer
  rw [MeasureTheory.integral_const_mul, h1, inv_mul_cancel₀ (mul_pos hε sMass_pos).ne']

/-! ## The doubly-odd extension and the mollifications -/

/-- The extension of the slice `s ↦ u z s` odd about both `0` and `π/2` (on the range
`(-π/2, π)` relevant for the angular mollification at scales `ε ≤ 1/2`). -/
def Qext (u : ℝ → ℝ → ℝ) (z s : ℝ) : ℝ :=
  if 0 ≤ s ∧ s ≤ Real.pi / 2 then u z s
  else if s < 0 then -u z (-s) else -u z (Real.pi - s)

theorem Qext_of_mem (u : ℝ → ℝ → ℝ) (z s : ℝ) (hs : s ∈ Set.Icc (0 : ℝ) (Real.pi / 2)) :
    Qext u z s = u z s := by
  rw [Qext, if_pos (Set.mem_Icc.mp hs)]

theorem Qext_neg_of_pos (u : ℝ → ℝ → ℝ) (z s : ℝ) (hs : 0 < s) :
    Qext u z (-s) = -u z s := by
  rw [Qext, if_neg (fun h => by linarith [h.1, hs]), if_pos (by linarith [hs]), neg_neg]

theorem Qext_pihalf_odd (u : ℝ → ℝ → ℝ) (z s : ℝ) (hs : 0 < s) (hs' : s ≤ Real.pi / 2) :
    Qext u z (Real.pi / 2 - s) = -Qext u z (Real.pi / 2 + s) := by
  rw [Qext, if_pos ⟨by linarith [hs], by linarith [hs']⟩]
  rw [Qext, if_neg (fun h => by linarith [h.2, hs]), if_neg (by linarith [Real.pi_pos, hs]),
    show Real.pi - (Real.pi / 2 + s) = Real.pi / 2 - s by ring, neg_neg]

/-- The angular mollification of the datum `u` at scale `ε`. -/
def thMoll (u : ℝ → ℝ → ℝ) (ε z θ : ℝ) : ℝ :=
  ∫ s : ℝ, sKer ε (θ - s) * Qext u z s

/-- The logarithmic-radial mollification of the angular mollification. -/
def zmoll (u : ℝ → ℝ → ℝ) (δ ε z θ : ℝ) : ℝ :=
  ∫ t : ℝ, sKer δ (Real.log z - t) * thMoll u ε (Real.exp t) θ

end Work.FTS.EllSol.PkgK5.K5c
