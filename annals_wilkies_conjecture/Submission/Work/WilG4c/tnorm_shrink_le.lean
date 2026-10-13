import Mathlib
import Submission.Work.WilG4c.StepHigherDefs
import Submission.Work.WilG4c.norm_iteratedFDeriv_rescale_le
import Submission.Work.WilG4c.Engine
import Submission.Work.WilG4c.LipDefs
import Submission.Work.WilG4c.iteratedFDeriv_const_smul
import Submission.Work.WilG4c.iteratedFDeriv_fun_add_const

namespace Work.WilG4c

open WilkiesDesign WilkiesDesign.CG

/-- An affine (in the target) transform of a function: the iterated derivative of
`y ↦ a * f y - b` in order `m ≥ 1` is `a` times the iterated derivative of `f`; the additive
constant is killed by the first derivative (`Work.WilG4c.iteratedFDeriv_fun_add_const`), and
`iteratedFDeriv` commutes with constant scalar multiplication
(`Work.WilG4c.iteratedFDeriv_const_smul`) because `fderiv_const_smul_field` holds without
differentiability hypotheses. -/
theorem itD_mul_sub {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {m : ℕ} (hm : 1 ≤ m) (a b : ℝ) (f : E → ℝ) (x : E) :
    iteratedFDeriv ℝ m (fun y => a * f y - b) x = a • iteratedFDeriv ℝ m f x := by
  rw [show (fun y : E => a * f y - b) = (fun y : E => (fun z => a * f z) y + (-b)) from rfl]
  rw [iteratedFDeriv_fun_add_const hm (fun y : E => a * f y) (-b) x]
  rw [show (fun y : E => a * f y) = (a : ℝ) • f from rfl]
  rw [iteratedFDeriv_const_smul a m f x]

/-- The base hypothesis `hbase` of BNZ's engine (`Work.WilkG4c.curve_bound`) for the *shrunk*
chart: if `J` is the composite of the surrogate `(∂_M f + 2)/4` with the Corollary 19 chart `φ`
(so `‖D^m J‖ ≤ 1` on the cube for `m ≤ r+1`, by `h1 : F1Affine`), and
`uM u = 4·J(c + u 0/4) - 2` is the corresponding composite with the shrunk chart `φ(c + ·/4)`,
and `|uM| ≤ 1`, then the jet norm of `uM` at any point of the cube is at most `e`.

The chain rule `‖D^m(J ∘ shrink)‖ ≤ 4^{-m}‖D^m J‖` is
`Work.WilG4c.norm_iteratedFDeriv_rescale_le` (`N := 1`, `lam := 4`), giving `‖D^m uM‖ ≤ 4^{1-m}`
for `m ≥ 1` and `|uM| ≤ 1` for `m = 0`; summing the geometric series gives
`1 + Σ_{1≤m} 4^{1-m} = 7/3 ≤ e` (no factorial estimates needed). -/
theorem tnorm_shrink_le {r : ℕ} (hr : 1 ≤ r) (J uM : (Fin 1 → ℝ) → ℝ)
    (c : ℝ) (hc0 : 0 ≤ c) (hc3 : c ≤ 3 / 4)
    (hJ : ∀ m, m ≤ r + 1 → ∀ t ∈ WilkiesDesign.openCube 1, ‖iteratedFDeriv ℝ m J t‖ ≤ 1)
    (h0 : ∀ u, |uM u| ≤ 1)
    (h4 : ∀ u, uM u = 4 * J (fun _ => c + u 0 / 4) - 2)
    {x : Fin 1 → ℝ} (hx : x ∈ WilkiesDesign.openCube 1) :
    WilkiesDesign.CG.tnorm r uM x ≤ Real.exp 1 := by
  -- Abbreviate the shrunk chart composite.
  set G : (Fin 1 → ℝ) → ℝ := fun u => J (fun i => c + u i / 4) with hG
  have huM : uM = fun u => 4 * G u - 2 := by
    funext u
    have hfun : (fun _ : Fin 1 => c + u 0 / 4) = (fun i : Fin 1 => c + u i / 4) := by
      funext i
      have : i = 0 := Subsingleton.elim i 0
      rw [this]
    rw [h4 u, hfun]
  -- The shrunk chart point `c + x/4` lies in the open cube.
  have hpt : (fun i : Fin 1 => (4 * c + x i) / 4) ∈ WilkiesDesign.openCube 1 := by
    intro i
    change (4 * c + x i) / 4 ∈ Set.Ioo (0 : ℝ) 1
    have h1 : (4 * c + x i) / 4 = c + x i / 4 := by ring
    rw [h1]
    constructor
    · have hxi := hx i
      linarith [hxi.1, hc0]
    · have hxi := hx i
      linarith [hxi.2, hc3]
  -- The pointwise derivative bound `‖D^m uM(x)‖ ≤ 1` for `m ≤ r`.
  have hbound : ∀ m ≤ r, ‖iteratedFDeriv ℝ m uM x‖ ≤ 1 := by
    intro m hm
    rcases Nat.eq_zero_or_pos m with hm0 | hpos
    · rw [hm0, norm_iteratedFDeriv_zero, Real.norm_eq_abs]
      exact h0 x
    · -- `m ≥ 1`: `uM = 4 • G - 2`, and `G` is `J` composed with the shrunk chart.
      rw [huM, itD_mul_sub hpos 4 2 G x, norm_smul,
        Real.norm_of_nonneg (by norm_num : (0 : ℝ) ≤ 4)]
      -- `‖D^m G(x)‖ ≤ 4^{-m} ≤ 1/4` by the affine rescaling chain rule.
      have hGresc : ‖iteratedFDeriv ℝ m G x‖ ≤ 1 / 4 := by
        have hres := Work.WilG4c.norm_iteratedFDeriv_rescale_le (N := 1) (4 : ℝ) (by norm_num)
          J (fun _ : Fin 1 => 4 * c) x m
        have hGeq : G = (fun y : Fin 1 → ℝ => J (fun i => (4 * c + y i) / 4)) := by
          funext y
          simp only [hG]
          congr 1
          ext i
          ring
        rw [hGeq]
        calc ‖iteratedFDeriv ℝ m (fun y : Fin 1 → ℝ => J fun i => (4 * c + y i) / 4) x‖
            ≤ ‖iteratedFDeriv ℝ m J (fun i => (4 * c + x i) / 4)‖ * (4 : ℝ)⁻¹ ^ m := hres
          _ ≤ 1 * (4 : ℝ)⁻¹ := by
              refine mul_le_mul (hJ m (by omega) _ hpt) ?_ (by positivity) (by norm_num)
              exact pow_le_of_le_one (by norm_num) (by norm_num) (by omega)
          _ = 1 / 4 := by norm_num
      nlinarith [hGresc]
  -- Sum the pointwise bounds against the exponential series.
  have hsum : WilkiesDesign.CG.tnorm r uM x ≤
      ∑ k ∈ Finset.range (r + 1), (1 : ℝ) / (k.factorial : ℝ) := by
    rw [WilkiesDesign.CG.tnorm]
    refine Finset.sum_le_sum fun k hk => ?_
    have hk' : k ≤ r := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
    exact div_le_div_of_nonneg_right (hbound k hk') (Nat.cast_nonneg _)
  refine hsum.trans ?_
  have h := Real.sum_le_exp_of_nonneg (x := (1 : ℝ)) (by norm_num) (r + 1)
  simpa using h

end Work.WilG4c
