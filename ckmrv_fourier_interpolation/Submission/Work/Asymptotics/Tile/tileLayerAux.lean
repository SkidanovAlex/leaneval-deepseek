/-
# Auxiliary estimates for the tile `layerLow` seminorm bound

Auxiliary results used by `Work.Asymptotics.Tile.layerLow_tile_seminorm`:

* `gaussPoly_monomial_expansion` (with the two-variable polynomial `gaussPolyP`);
* `poleIntegral_monomial_weight`: `|r|^m ‖∫ 1/(it-w) t^e e^{-πr²t}‖ ≤ C (scale w)^N`;
* the layer-derivative decomposition `Dl_eq` and its estimates.
-/
import Mathlib
import Submission.Work.Asymptotics.Tile.tileLayerDefs
import Submission.Work.Asymptotics.Kaxis_tile_flat_below_pole
import Submission.Work.Asymptotics.tile_pole_integral_decay
import Submission.Work.Asymptotics.layerLow_seminorm
import Submission.Work.Asymptotics.Tile.tileIntervalDeriv
import Submission.Work.Asymptotics.Tile.layerDeriv_gauss_decomp

noncomputable section

open MeasureTheory Filter Topology UpperHalfPlane
open Work.Kernels
open scoped Topology ContDiff

namespace Work.Asymptotics.Tile

/-! ## The bivariate monomial expansion of `gaussPoly` -/

/-- The two-variable polynomial associated with the recursion of `gaussPoly`, with the parameter
`a` promoted to the coefficient variable: the polynomial in `X` over `ℂ[A]` defined by
`P 0 = 1`, `P (m+1) = P m' - 2A·X·(P m)`. -/
noncomputable def gaussPolyP : ℕ → Polynomial (Polynomial ℂ)
  | 0 => 1
  | (m+1) => (gaussPolyP m).derivative - Polynomial.C (2 * Polynomial.X) * (Polynomial.X * gaussPolyP m)

lemma natCast_add_one_poly (n : ℕ) : (↑n + 1 : Polynomial ℂ) = Polynomial.C ((n:ℂ)+1) := by
  have h1 : (↑n : Polynomial ℂ) = Polynomial.C ((n:ℂ)) := (Polynomial.C_eq_natCast n).symm
  have h2 : (1 : Polynomial ℂ) = Polynomial.C 1 := Polynomial.C_1.symm
  rw [h1, h2, ← Polynomial.C_add]

lemma gaussPolyP_deg (l : ℕ) : (gaussPolyP l).natDegree ≤ l := by
  induction l with
  | zero => rw [gaussPolyP]; simp
  | succ m ih =>
    rw [gaussPolyP]
    refine le_trans (Polynomial.natDegree_sub_le _ _) (max_le ?_ ?_)
    · exact le_trans (Polynomial.natDegree_derivative_le _) (by omega)
    · refine le_trans Polynomial.natDegree_mul_le ?_
      have h : (Polynomial.C (2 * Polynomial.X) : Polynomial (Polynomial ℂ)).natDegree = 0 :=
        Polynomial.natDegree_C _
      rw [h, zero_add]
      refine le_trans Polynomial.natDegree_mul_le ?_
      rw [Polynomial.natDegree_X]
      omega

lemma gaussPolyP_coeff_deg (l i : ℕ) : ((gaussPolyP l).coeff i).natDegree ≤ l := by
  induction l generalizing i with
  | zero =>
    rw [gaussPolyP]
    rcases Nat.eq_zero_or_pos i with h | h
    · subst h; simp
    · rw [Polynomial.coeff_one, if_neg (by omega)]; simp
  | succ m ih =>
    rw [gaussPolyP, Polynomial.coeff_sub]
    refine le_trans (Polynomial.natDegree_sub_le _ _) (max_le ?_ ?_)
    · rw [Polynomial.coeff_derivative]
      refine le_trans Polynomial.natDegree_mul_le ?_
      rw [natCast_add_one_poly, Polynomial.natDegree_C, add_zero]
      exact le_trans (ih (i+1)) (by omega)
    · rw [Polynomial.coeff_C_mul]
      rcases Nat.eq_zero_or_pos i with h | h
      · subst h
        rw [Polynomial.coeff_X_mul_zero, mul_zero]; simp
      · obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : i ≠ 0)
        rw [Polynomial.coeff_X_mul]
        refine le_trans Polynomial.natDegree_mul_le ?_
        have h2 : (2 * Polynomial.X : Polynomial ℂ).natDegree ≤ 1 := by
          refine le_trans Polynomial.natDegree_mul_le ?_
          have h : (2 : Polynomial ℂ).natDegree = 0 := by simp
          rw [h, Polynomial.natDegree_X]
        have h3 := ih j
        omega

lemma gaussPolyP_map (l : ℕ) (a : ℂ) :
    (gaussPolyP l).map (Polynomial.evalRingHom a) = Work.Asymptotics.gaussPoly a l := by
  induction l with
  | zero => rw [gaussPolyP]; simp [Work.Asymptotics.gaussPoly]
  | succ m ih =>
    rw [gaussPolyP, Work.Asymptotics.gaussPoly_succ]
    simp only [Polynomial.map_sub, Polynomial.map_mul, Polynomial.map_C, Polynomial.map_X]
    rw [← Polynomial.derivative_map, ih]
    simp

/-- **The bivariate monomial expansion of `gaussPoly`**: `(gaussPoly a l).eval r` is a finite
`ℂ`-linear combination of the monomials `a^s r^i`, `i,s ≤ l`. -/
theorem gaussPoly_monomial_expansion (l : ℕ) :
    ∃ coef : ℕ → ℕ → ℂ, ∀ (r : ℝ) (a : ℂ),
      (Work.Asymptotics.gaussPoly a l).eval (r : ℂ)
        = ∑ i ∈ Finset.range (l + 1), ∑ s ∈ Finset.range (l + 1),
            coef i s * a ^ s * (r : ℂ) ^ i := by
  refine ⟨fun i s => ((gaussPolyP l).coeff i).coeff s, ?_⟩
  intro r a
  rw [← gaussPolyP_map l a]
  have hdeg : ((gaussPolyP l).map (Polynomial.evalRingHom a)).natDegree < l+1 :=
    lt_of_le_of_lt (le_trans Polynomial.natDegree_map_le (gaussPolyP_deg l)) (by omega)
  rw [Polynomial.eval_eq_sum_range' (n := l+1) hdeg]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [Polynomial.coeff_map]
  have hdeg2 : ((gaussPolyP l).coeff i).natDegree < l+1 :=
    lt_of_le_of_lt (gaussPolyP_coeff_deg l i) (by omega)
  rw [show (Polynomial.evalRingHom a) ((gaussPolyP l).coeff i)
        = Polynomial.eval a ((gaussPolyP l).coeff i) from rfl]
  rw [Polynomial.eval_eq_sum_range' (n := l+1) hdeg2, Finset.sum_mul]

/-- The complex polynomial `a ↦ (gaussPoly a l).eval r` is continuous (from the monomial
expansion). -/
lemma continuous_gaussPoly_eval (l : ℕ) (r : ℝ) :
    Continuous (fun a : ℂ => (Work.Asymptotics.gaussPoly a l).eval (r : ℂ)) := by
  obtain ⟨coef, hcoef⟩ := gaussPoly_monomial_expansion l
  rw [funext (fun a => hcoef r a)]
  refine continuous_finset_sum _ (fun i _ => ?_)
  refine continuous_finset_sum _ (fun s _ => ?_)
  exact ((continuous_const.mul (continuous_id.pow s)).mul_const _)

/-! ## The signed pole integral with a monomial weight -/

/-- **Signed pole integral with a monomial weight.**  For every monomial weight `t^e` and every
weight `|r|^m`, the signed integral of `1/(it-w) t^e e^{-πr²t}` over the window `[Im w/2, 1]` is
bounded by a power of `scale w` — the logarithmic divergence of `∫ |1/(it-w)|` cancels. -/
theorem poleIntegral_monomial_weight (m e : ℕ) :
    ∃ C N : ℝ, 0 ≤ C ∧ 0 ≤ N ∧ ∀ (w : UpperHalfPlane), w ∈ KEpsilon → w.re ≠ 0 → ∀ r : ℝ,
      |r| ^ m * ‖∫ t in (w.im / 2)..1, (1 : ℂ) / ((t : ℂ) * Complex.I - (w : ℂ)) * (t : ℂ) ^ e *
        Complex.exp (-(Real.pi * (r : ℂ) ^ 2 * (t : ℂ)))‖ ≤ C * (scale w) ^ N := by
  obtain ⟨C₀, N₀, hC₀, hN₀, hb⟩ := tile_pole_integral_decay e (m+1)
  refine ⟨C₀, N₀ + (m+1), hC₀, by positivity, ?_⟩
  intro w hw hre r
  have hy : 0 < w.im := w.im_pos
  have hy1 : w.im ≤ 1 := le_trans (tile_im_le_half hw) (by norm_num)
  have hsc1 : (1:ℝ) ≤ scale w := one_le_scale w
  have hsc0 : (0:ℝ) < scale w := scale_pos w
  have hinvle : (w.im)⁻¹ ≤ scale w := inv_im_le_scale w
  have hb' := hb w hw (Real.pi * r^2) (by positivity)
  have hfun : (fun t : ℝ => (1:ℂ)/((t:ℂ)*Complex.I - (w:ℂ)) * (t:ℂ)^e *
        Complex.exp (-(Real.pi * (r:ℂ)^2 * (t:ℂ))))
      = fun t : ℝ => (1:ℂ)/((t:ℂ)*Complex.I - (w:ℂ)) * (t:ℂ)^e *
        Complex.exp ((-(((Real.pi * r^2 : ℝ) : ℂ))) * (t:ℂ)) := by
    funext t
    rw [show -(((Real.pi * r^2 : ℝ) : ℂ)) * (t:ℂ) = -(Real.pi * (r:ℂ)^2 * (t:ℂ)) by
      push_cast; ring]
  rw [hfun]
  have hpi1 : (1:ℝ) ≤ Real.pi := le_trans (by norm_num) (le_of_lt Real.pi_gt_three)
  have hfact : |r| ^ m * ((1 + Real.pi * r^2 * w.im)⁻¹) ^ (m+1) ≤ (scale w) ^ (m+1) := by
    have hρ1 : (1:ℝ) ≤ 1 + Real.pi * r^2 * w.im := by
      nlinarith [show (0:ℝ) ≤ Real.pi * r^2 * w.im from by positivity]
    have hρpos : (0:ℝ) < 1 + Real.pi * r^2 * w.im := lt_of_lt_of_le one_pos hρ1
    rw [inv_pow]
    rcases le_or_gt (|r| * w.im) 1 with hc | hc
    · have hu : |r| ≤ (w.im)⁻¹ := by
        rw [inv_eq_one_div, le_div_iff₀ hy]
        simpa [mul_comm] using hc
      have hu1 : |r| ^ m ≤ ((w.im)⁻¹) ^ m := pow_le_pow_left₀ (abs_nonneg r) hu m
      have hinv : ((1 + Real.pi * r^2 * w.im) ^ (m+1))⁻¹ ≤ 1 := by
        rw [inv_le_one₀ (pow_pos hρpos _)]; exact one_le_pow₀ hρ1
      calc |r| ^ m * ((1 + Real.pi * r^2 * w.im) ^ (m+1))⁻¹ ≤ ((w.im)⁻¹) ^ m * 1 :=
            mul_le_mul hu1 hinv (by positivity) (by positivity)
        _ = ((w.im)⁻¹) ^ m := by ring
        _ ≤ (scale w) ^ m := pow_le_pow_left₀ (by positivity) hinvle m
        _ ≤ (scale w) ^ (m+1) := pow_le_pow_right₀ hsc1 (by omega)
    · have hu1 : (1:ℝ) < |r| := by
        refine lt_of_lt_of_le hc ?_
        nlinarith [abs_nonneg r, hy1]
      have hρge : Real.pi * |r|^2 * w.im ≤ 1 + Real.pi * r^2 * w.im := by
        rw [sq_abs]; nlinarith [show (0:ℝ) ≤ 1 from by norm_num]
      have hstep : ((1 + Real.pi * r^2 * w.im) ^ (m+1))⁻¹ ≤
          ((Real.pi * |r|^2 * w.im) ^ (m+1))⁻¹ := by
        rw [inv_le_inv₀ (pow_pos hρpos _) (by positivity)]
        exact pow_le_pow_left₀ (by positivity) hρge (m+1)
      have hfin : |r| ^ m * ((Real.pi * |r|^2 * w.im) ^ (m+1))⁻¹ ≤ (scale w) ^ (m+1) := by
        have hEq : |r| ^ m * ((Real.pi * |r|^2 * w.im) ^ (m+1))⁻¹
            = (|r|^m / |r|^(2*(m+1))) * ((Real.pi^(m+1) * w.im^(m+1))⁻¹) := by
          rw [mul_pow, mul_pow]
          rw [show ((|r|^2)^(m+1)) = |r|^(2*(m+1)) by rw [pow_mul]]
          field_simp
        rw [hEq]
        have hA : |r|^m / |r|^(2*(m+1)) ≤ 1 := by
          rw [div_le_one (by positivity)]
          exact pow_le_pow_right₀ (le_of_lt hu1) (by omega)
        have hB : (Real.pi^(m+1) * w.im^(m+1))⁻¹ ≤ (w.im^(m+1))⁻¹ := by
          rw [inv_le_inv₀ (by positivity) (by positivity)]
          have h2 : (1:ℝ) ≤ Real.pi^(m+1) := one_le_pow₀ hpi1
          nlinarith [pow_pos hy (m+1), h2]
        have hC : (w.im^(m+1))⁻¹ ≤ (scale w)^(m+1) := by
          rw [← inv_pow]
          exact pow_le_pow_left₀ (by positivity) hinvle (m+1)
        calc (|r|^m / |r|^(2*(m+1))) * ((Real.pi^(m+1) * w.im^(m+1))⁻¹)
            ≤ 1 * ((Real.pi^(m+1) * w.im^(m+1))⁻¹) :=
              mul_le_mul_of_nonneg_right hA (by positivity)
          _ ≤ (w.im^(m+1))⁻¹ := by rw [one_mul]; exact hB
          _ ≤ (scale w)^(m+1) := hC
      calc |r|^m * ((1 + Real.pi * r^2 * w.im) ^ (m+1))⁻¹
          ≤ |r|^m * ((Real.pi * |r|^2 * w.im) ^ (m+1))⁻¹ :=
            mul_le_mul_of_nonneg_left hstep (by positivity)
        _ ≤ (scale w)^(m+1) := hfin
  calc |r| ^ m * ‖∫ t in (w.im/2)..1, (1:ℂ)/((t:ℂ)*Complex.I - (w:ℂ)) * (t:ℂ)^e *
          Complex.exp ((-(((Real.pi * r^2 : ℝ):ℂ))) * (t:ℂ))‖
      ≤ |r| ^ m * (C₀ * (scale w) ^ N₀ * ((1 + Real.pi * r^2 * w.im)⁻¹) ^ (m+1)) :=
        mul_le_mul_of_nonneg_left hb' (by positivity)
    _ = C₀ * (scale w) ^ N₀ * (|r| ^ m * ((1 + Real.pi * r^2 * w.im)⁻¹) ^ (m+1)) := by ring
    _ ≤ C₀ * (scale w) ^ N₀ * (scale w) ^ (m+1) :=
        mul_le_mul_of_nonneg_left hfact (by positivity)
    _ = C₀ * (scale w) ^ (N₀ + (↑m + 1)) := by
        rw [Real.rpow_add hsc0, show (↑m + 1 : ℝ) = ((m+1:ℕ):ℝ) by push_cast; ring,
          Real.rpow_natCast]
        ring

/-! ## The explicit three-Gaussian decomposition of `∂_r^l (sinSq · e^{-π·²t})` -/

/-- The `l`-th `r`-derivative of the layer integrand, written as an explicit combination of the
three shifted Gaussians `e^{-(πt+δ)r²}` with `δ ∈ {0, -iπ, iπ}` and polynomial prefactors
`gaussPoly (πt+δ) l`. -/
lemma Dl_eq (l : ℕ) (r t : ℝ) :
    iteratedDeriv l (fun x : ℝ => Work.Asymptotics.sinSq x * Complex.exp (-(Real.pi * (x:ℂ)^2 * (t:ℂ)))) r
    = 2 * ((Work.Asymptotics.gaussPoly ((Real.pi:ℂ)*(t:ℂ)) l).eval (r:ℂ)
            * Complex.exp (-(((Real.pi:ℂ)*(t:ℂ)) * (r:ℂ)^2)))
      - (Work.Asymptotics.gaussPoly ((Real.pi:ℂ)*(t:ℂ) - (Real.pi:ℂ)*Complex.I) l).eval (r:ℂ)
            * Complex.exp (-((((Real.pi:ℂ)*(t:ℂ)) - (Real.pi:ℂ)*Complex.I) * (r:ℂ)^2))
      - (Work.Asymptotics.gaussPoly ((Real.pi:ℂ)*(t:ℂ) + (Real.pi:ℂ)*Complex.I) l).eval (r:ℂ)
            * Complex.exp (-((((Real.pi:ℂ)*(t:ℂ)) + (Real.pi:ℂ)*Complex.I) * (r:ℂ)^2)) := by
  rw [sinSq_mul_exp_decomp t]
  set A : ℂ := (Real.pi : ℂ) * (t : ℂ) with hA
  set B : ℂ := A - (Real.pi : ℂ) * Complex.I with hB
  set C : ℂ := A + (Real.pi : ℂ) * Complex.I with hC
  have hc1 : ContDiffAt ℝ (↑l : ℕ∞) (fun s : ℝ => Complex.exp (-(A * (s : ℂ) ^ 2))) r :=
    contDiffAt_gaussExp l A r
  have hc2 : ContDiffAt ℝ (↑l : ℕ∞) (fun s : ℝ => Complex.exp (-(B * (s : ℂ) ^ 2))) r :=
    contDiffAt_gaussExp l B r
  have hc3 : ContDiffAt ℝ (↑l : ℕ∞) (fun s : ℝ => Complex.exp (-(C * (s : ℂ) ^ 2))) r :=
    contDiffAt_gaussExp l C r
  have hc4 : ContDiffAt ℝ (↑l : ℕ∞) (fun s : ℝ => 2 * Complex.exp (-(A * (s : ℂ) ^ 2))) r :=
    contDiffAt_gaussExp_mul l 2 A r
  have step1 : iteratedDeriv l (((fun s : ℝ => 2 * Complex.exp (-(A * (s : ℂ) ^ 2)))
        - (fun s : ℝ => Complex.exp (-(B * (s : ℂ) ^ 2))))
        - (fun s : ℝ => Complex.exp (-(C * (s : ℂ) ^ 2)))) r
      = iteratedDeriv l ((fun s : ℝ => 2 * Complex.exp (-(A * (s : ℂ) ^ 2)))
          - (fun s : ℝ => Complex.exp (-(B * (s : ℂ) ^ 2)))) r
        - iteratedDeriv l (fun s : ℝ => Complex.exp (-(C * (s : ℂ) ^ 2))) r :=
    iteratedDeriv_sub (hc4.sub hc2) hc3
  have step2 : iteratedDeriv l ((fun s : ℝ => 2 * Complex.exp (-(A * (s : ℂ) ^ 2)))
          - (fun s : ℝ => Complex.exp (-(B * (s : ℂ) ^ 2)))) r
      = iteratedDeriv l (fun s : ℝ => 2 * Complex.exp (-(A * (s : ℂ) ^ 2))) r
        - iteratedDeriv l (fun s : ℝ => Complex.exp (-(B * (s : ℂ) ^ 2))) r :=
    iteratedDeriv_sub hc4 hc2
  have step3 : iteratedDeriv l (fun s : ℝ => 2 * Complex.exp (-(A * (s : ℂ) ^ 2))) r
      = 2 * iteratedDeriv l (fun s : ℝ => Complex.exp (-(A * (s : ℂ) ^ 2))) r :=
    iteratedDeriv_const_mul 2 hc1
  change iteratedDeriv l (((fun s : ℝ => 2 * Complex.exp (-(A * (s : ℂ) ^ 2)))
        - (fun s : ℝ => Complex.exp (-(B * (s : ℂ) ^ 2))))
        - (fun s : ℝ => Complex.exp (-(C * (s : ℂ) ^ 2)))) r = _
  rw [step1, step2, step3]
  rw [Work.Asymptotics.iteratedDeriv_gaussPoly A l,
      Work.Asymptotics.iteratedDeriv_gaussPoly B l,
      Work.Asymptotics.iteratedDeriv_gaussPoly C l]
  all_goals rw [hA, hB, hC]
  all_goals ring

/-! ## Norm bounds for `gaussPoly` evaluations -/

/-- `‖(r : ℂ)‖ = |r|`. -/
lemma norm_ofReal_complex (r : ℝ) : ‖(r : ℂ)‖ = |r| := by simp

/-- The monomial expansion bounds `(gaussPoly a l).eval r` by
`(Σ_{i,s} ‖coef i s‖) (1+‖a‖)^l (1+|r|)^l`. -/
lemma gaussPoly_eval_norm_bound (l : ℕ) (coef : ℕ → ℕ → ℂ)
    (hcoef : ∀ (r : ℝ) (a : ℂ), (Work.Asymptotics.gaussPoly a l).eval (r : ℂ)
        = ∑ i ∈ Finset.range (l + 1), ∑ s ∈ Finset.range (l + 1), coef i s * a ^ s * (r : ℂ) ^ i)
    (a : ℂ) (r : ℝ) :
    ‖(Work.Asymptotics.gaussPoly a l).eval (r : ℂ)‖
      ≤ (∑ i ∈ Finset.range (l + 1), ∑ s ∈ Finset.range (l + 1), ‖coef i s‖)
        * (1 + ‖a‖) ^ l * (1 + |r|) ^ l := by
  rw [hcoef r a]
  have hsum : ∀ i ∈ Finset.range (l+1), ‖∑ s ∈ Finset.range (l+1), coef i s * a^s * (r:ℂ)^i‖
      ≤ ∑ s ∈ Finset.range (l+1), ‖coef i s * a^s * (r:ℂ)^i‖ := fun i _ => norm_sum_le _ _
  have hbound : ∀ i ∈ Finset.range (l+1), ∀ s ∈ Finset.range (l+1),
      ‖coef i s * a^s * (r:ℂ)^i‖ ≤ ‖coef i s‖ * ((1 + ‖a‖)^l * (1 + |r|)^l) := by
    intro i hi s hs
    have hs' : s ≤ l := by have := Finset.mem_range.mp hs; omega
    have hi' : i ≤ l := by have := Finset.mem_range.mp hi; omega
    have ha1 : (1:ℝ) ≤ 1 + ‖a‖ := by linarith [norm_nonneg a]
    have ha2 : ‖a‖ ≤ 1 + ‖a‖ := by linarith [norm_nonneg a]
    have hr1 : (1:ℝ) ≤ 1 + |r| := by linarith [abs_nonneg r]
    have hr2 : |r| ≤ 1 + |r| := by linarith [abs_nonneg r]
    have h2 : ‖a‖^s ≤ (1+‖a‖)^l :=
      le_trans (pow_le_pow_left₀ (norm_nonneg a) ha2 s) (pow_le_pow_right₀ ha1 hs')
    have h3 : |r|^i ≤ (1+|r|)^l :=
      le_trans (pow_le_pow_left₀ (abs_nonneg r) hr2 i) (pow_le_pow_right₀ hr1 hi')
    rw [norm_mul, norm_mul, Complex.norm_pow, Complex.norm_pow, norm_ofReal_complex]
    calc ‖coef i s‖ * ‖a‖^s * |r|^i = ‖coef i s‖ * (‖a‖^s * |r|^i) := by ring
      _ ≤ ‖coef i s‖ * ((1 + ‖a‖)^l * (1 + |r|)^l) :=
          mul_le_mul_of_nonneg_left (mul_le_mul h2 h3 (by positivity) (by positivity))
            (norm_nonneg (coef i s))
  calc ‖∑ i ∈ Finset.range (l+1), ∑ s ∈ Finset.range (l+1), coef i s * a^s * (r:ℂ)^i‖
      ≤ ∑ i ∈ Finset.range (l+1), ‖∑ s ∈ Finset.range (l+1), coef i s * a^s * (r:ℂ)^i‖ :=
        norm_sum_le _ _
    _ ≤ ∑ i ∈ Finset.range (l+1), ∑ s ∈ Finset.range (l+1), ‖coef i s * a^s * (r:ℂ)^i‖ :=
        Finset.sum_le_sum hsum
    _ ≤ ∑ i ∈ Finset.range (l+1), ∑ s ∈ Finset.range (l+1), ‖coef i s‖ * ((1 + ‖a‖)^l * (1 + |r|)^l) :=
        Finset.sum_le_sum (fun i hi => Finset.sum_le_sum (fun s hs => hbound i hi s hs))
    _ = (∑ i ∈ Finset.range (l+1), ∑ s ∈ Finset.range (l+1), ‖coef i s‖)
          * ((1 + ‖a‖)^l * (1 + |r|)^l) := by
        rw [Finset.sum_mul]
        refine Finset.sum_congr rfl (fun i _ => ?_)
        rw [Finset.sum_mul]
    _ = (∑ i ∈ Finset.range (l+1), ∑ s ∈ Finset.range (l+1), ‖coef i s‖)
          * (1 + ‖a‖)^l * (1 + |r|)^l := by ring

/-- `‖exp(-(a r²))‖ = exp(-(Re a) r²)`. -/
lemma norm_exp_neg_mul_sq (a : ℂ) (r : ℝ) :
    ‖Complex.exp (-(a * (r:ℂ)^2))‖ = Real.exp (-(a.re) * r^2) := by
  rw [Complex.norm_exp]
  congr 1
  rw [Complex.neg_re, Complex.mul_re]
  have h2 : ((r:ℂ)^2).re = r^2 := by
    rw [pow_two, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im]; ring
  have h2' : ((r:ℂ)^2).im = 0 := by
    rw [pow_two, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im]; ring
  rw [h2, h2', mul_zero, sub_zero]
  ring

/-- `‖exp(-((πt+δ) r²))‖ ≤ 1` when `Re δ = 0` and `t ≥ 0`. -/
lemma norm_exp_shift_le (δ : ℂ) (hδ : δ.re = 0) (t : ℝ) (ht : 0 ≤ t) (r : ℝ) :
    ‖Complex.exp (-(((Real.pi:ℂ)*(t:ℂ) + δ) * (r:ℂ)^2))‖ ≤ 1 := by
  rw [norm_exp_neg_mul_sq]
  rw [Real.exp_le_one_iff]
  have hre : (((Real.pi:ℂ)*(t:ℂ) + δ)).re = Real.pi * t := by
    have h1 : ((Real.pi:ℂ)*(t:ℂ)) = ((Real.pi * t : ℝ) : ℂ) := by push_cast; ring
    rw [Complex.add_re, h1, hδ]; simp
  rw [hre]
  have h1 : (0:ℝ) ≤ Real.pi * t := mul_nonneg (le_of_lt Real.pi_pos) ht
  have h2 : (0:ℝ) ≤ r^2 := sq_nonneg r
  nlinarith [h1, h2]

/-- Continuity in `t` of the shifted Gaussian term `(gaussPoly (πt+δ) l).eval r · e^{-(πt+δ)r²}`. -/
lemma continuous_Dterm (l : ℕ) (r : ℝ) (δ : ℂ) :
    Continuous (fun t : ℝ => (Work.Asymptotics.gaussPoly ((Real.pi:ℂ)*(t:ℂ) + δ) l).eval (r:ℂ)
      * Complex.exp (-(((Real.pi:ℂ)*(t:ℂ) + δ) * (r:ℂ)^2))) := by
  have ha : Continuous (fun t : ℝ => (Real.pi:ℂ)*(t:ℂ) + δ) :=
    (continuous_const.mul Complex.continuous_ofReal).add continuous_const
  refine ((continuous_gaussPoly_eval l r).comp ha).mul ?_
  exact Complex.continuous_exp.comp ((ha.mul continuous_const).neg)

/-- The `l`-th `r`-derivative of the layer integrand is measurable in `t` and bounded by
`C (1+|r|)^l` on `t ∈ (0,1]`. -/
theorem layerDeriv_gauss_bound (l : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ r : ℝ,
      Measurable (fun t : ℝ => iteratedDeriv l (fun x : ℝ => Work.Asymptotics.sinSq x *
        Complex.exp (-(Real.pi * (x : ℂ) ^ 2 * (t : ℂ)))) r) ∧
      (∀ (t : ℝ), 0 < t → t ≤ 1 → ‖iteratedDeriv l (fun x : ℝ => Work.Asymptotics.sinSq x *
        Complex.exp (-(Real.pi * (x : ℂ) ^ 2 * (t : ℂ)))) r‖ ≤ C * (1 + |r|) ^ l) := by
  obtain ⟨coef, hcoef⟩ := gaussPoly_monomial_expansion l
  set K : ℝ := ∑ i ∈ Finset.range (l+1), ∑ s ∈ Finset.range (l+1), ‖coef i s‖ with hK
  have hK0 : 0 ≤ K := by rw [hK]; positivity
  have hdec : ∀ (r : ℝ) (t : ℝ), iteratedDeriv l (fun x : ℝ => Work.Asymptotics.sinSq x *
        Complex.exp (-(Real.pi * (x : ℂ) ^ 2 * (t : ℂ)))) r
      = 2 * ((Work.Asymptotics.gaussPoly ((Real.pi:ℂ)*(t:ℂ)) l).eval (r:ℂ)
              * Complex.exp (-(((Real.pi:ℂ)*(t:ℂ)) * (r:ℂ)^2)))
            - ((Work.Asymptotics.gaussPoly ((Real.pi:ℂ)*(t:ℂ) - (Real.pi:ℂ)*Complex.I) l).eval (r:ℂ)
              * Complex.exp (-((((Real.pi:ℂ)*(t:ℂ)) - (Real.pi:ℂ)*Complex.I) * (r:ℂ)^2)))
            - ((Work.Asymptotics.gaussPoly ((Real.pi:ℂ)*(t:ℂ) + (Real.pi:ℂ)*Complex.I) l).eval (r:ℂ)
              * Complex.exp (-((((Real.pi:ℂ)*(t:ℂ)) + (Real.pi:ℂ)*Complex.I) * (r:ℂ)^2))) :=
    fun r t => Dl_eq l r t
  refine ⟨4 * (K * (1 + 2*Real.pi)^l), by positivity, fun r => ⟨?_, ?_⟩⟩
  · have hm0 : Measurable (fun t : ℝ => (Work.Asymptotics.gaussPoly ((Real.pi:ℂ)*(t:ℂ)) l).eval (r:ℂ)
        * Complex.exp (-(((Real.pi:ℂ)*(t:ℂ)) * (r:ℂ)^2))) := by
      simpa using (continuous_Dterm l r 0).measurable
    have hm1 : Measurable (fun t : ℝ => (Work.Asymptotics.gaussPoly ((Real.pi:ℂ)*(t:ℂ) - (Real.pi:ℂ)*Complex.I) l).eval (r:ℂ)
        * Complex.exp (-((((Real.pi:ℂ)*(t:ℂ)) - (Real.pi:ℂ)*Complex.I) * (r:ℂ)^2))) :=
      (continuous_Dterm l r (-((Real.pi:ℂ)*Complex.I))).measurable
    have hm2 : Measurable (fun t : ℝ => (Work.Asymptotics.gaussPoly ((Real.pi:ℂ)*(t:ℂ) + (Real.pi:ℂ)*Complex.I) l).eval (r:ℂ)
        * Complex.exp (-((((Real.pi:ℂ)*(t:ℂ)) + (Real.pi:ℂ)*Complex.I) * (r:ℂ)^2))) :=
      (continuous_Dterm l r ((Real.pi:ℂ)*Complex.I)).measurable
    rw [show (fun t : ℝ => iteratedDeriv l (fun x : ℝ => Work.Asymptotics.sinSq x *
        Complex.exp (-(Real.pi * (x : ℂ) ^ 2 * (t : ℂ)))) r)
        = fun t : ℝ => 2 * ((Work.Asymptotics.gaussPoly ((Real.pi:ℂ)*(t:ℂ)) l).eval (r:ℂ)
              * Complex.exp (-(((Real.pi:ℂ)*(t:ℂ)) * (r:ℂ)^2)))
            - ((Work.Asymptotics.gaussPoly ((Real.pi:ℂ)*(t:ℂ) - (Real.pi:ℂ)*Complex.I) l).eval (r:ℂ)
              * Complex.exp (-((((Real.pi:ℂ)*(t:ℂ)) - (Real.pi:ℂ)*Complex.I) * (r:ℂ)^2)))
            - ((Work.Asymptotics.gaussPoly ((Real.pi:ℂ)*(t:ℂ) + (Real.pi:ℂ)*Complex.I) l).eval (r:ℂ)
              * Complex.exp (-((((Real.pi:ℂ)*(t:ℂ)) + (Real.pi:ℂ)*Complex.I) * (r:ℂ)^2)))
        from funext (hdec r)]
    exact (hm0.const_mul 2).sub hm1 |>.sub hm2
  · intro t ht0 ht1
    have ht : (0:ℝ) ≤ t := le_of_lt ht0
    have hkey : ∀ δ : ℂ, δ.re = 0 → ‖δ‖ ≤ Real.pi →
        ‖(Work.Asymptotics.gaussPoly ((Real.pi:ℂ)*(t:ℂ) + δ) l).eval (r:ℂ)
          * Complex.exp (-(((Real.pi:ℂ)*(t:ℂ) + δ) * (r:ℂ)^2))‖ ≤ K * (1 + 2*Real.pi)^l * (1 + |r|)^l := by
      intro δ hδ hδnorm
      have hexp : ‖Complex.exp (-(((Real.pi:ℂ)*(t:ℂ) + δ) * (r:ℂ)^2))‖ ≤ 1 :=
        norm_exp_shift_le δ hδ t ht r
      have hnormmu : ‖(Real.pi:ℂ)*(t:ℂ) + δ‖ ≤ 2 * Real.pi := by
        refine le_trans (norm_add_le _ _) ?_
        rw [Complex.norm_mul, norm_ofReal_complex, norm_ofReal_complex,
          abs_of_nonneg (le_of_lt Real.pi_pos), abs_of_nonneg ht]
        have hπt : Real.pi * t ≤ Real.pi := by nlinarith [Real.pi_pos, ht1]
        linarith
      have h1 : ‖(Work.Asymptotics.gaussPoly ((Real.pi:ℂ)*(t:ℂ) + δ) l).eval (r:ℂ)‖
          ≤ K * (1 + ‖(Real.pi:ℂ)*(t:ℂ) + δ‖)^l * (1 + |r|)^l :=
        gaussPoly_eval_norm_bound l coef hcoef _ r
      have h2 : (1 + ‖(Real.pi:ℂ)*(t:ℂ) + δ‖) ≤ 1 + 2 * Real.pi := by linarith
      have h3 : (1 + ‖(Real.pi:ℂ)*(t:ℂ) + δ‖)^l ≤ (1 + 2*Real.pi)^l :=
        pow_le_pow_left₀ (by positivity) h2 l
      have h4 : (0:ℝ) ≤ (1 + |r|)^l := by positivity
      have h5 : K * (1 + ‖(Real.pi:ℂ)*(t:ℂ) + δ‖)^l * (1 + |r|)^l
          ≤ K * (1 + 2*Real.pi)^l * (1 + |r|)^l := by
        refine mul_le_mul_of_nonneg_right ?_ h4
        exact mul_le_mul_of_nonneg_left h3 hK0
      rw [norm_mul]
      calc ‖(Work.Asymptotics.gaussPoly ((Real.pi:ℂ)*(t:ℂ) + δ) l).eval (r:ℂ)‖
              * ‖Complex.exp (-(((Real.pi:ℂ)*(t:ℂ) + δ) * (r:ℂ)^2))‖
          ≤ (K * (1 + ‖(Real.pi:ℂ)*(t:ℂ) + δ‖)^l * (1 + |r|)^l) * 1 :=
            mul_le_mul h1 hexp (norm_nonneg _) (by positivity)
        _ ≤ (K * (1 + 2*Real.pi)^l * (1 + |r|)^l) * 1 := mul_le_mul_of_nonneg_right h5 (by norm_num)
        _ = K * (1 + 2*Real.pi)^l * (1 + |r|)^l := by ring
    have h0 : ‖(Work.Asymptotics.gaussPoly ((Real.pi:ℂ)*(t:ℂ)) l).eval (r:ℂ)
          * Complex.exp (-(((Real.pi:ℂ)*(t:ℂ)) * (r:ℂ)^2))‖ ≤ K * (1+2*Real.pi)^l * (1+|r|)^l := by
      have := hkey 0 (by simp) (by simpa using Real.pi_pos.le)
      simpa using this
    have h1 : ‖(Work.Asymptotics.gaussPoly ((Real.pi:ℂ)*(t:ℂ) - (Real.pi:ℂ)*Complex.I) l).eval (r:ℂ)
          * Complex.exp (-((((Real.pi:ℂ)*(t:ℂ)) - (Real.pi:ℂ)*Complex.I) * (r:ℂ)^2))‖
        ≤ K * (1+2*Real.pi)^l * (1+|r|)^l := by
      refine hkey (-((Real.pi:ℂ)*Complex.I)) (by simp) (le_of_eq ?_)
      rw [norm_neg, Complex.norm_mul, Complex.norm_I, mul_one, norm_ofReal_complex,
        abs_of_nonneg (le_of_lt Real.pi_pos)]
    have h2 : ‖(Work.Asymptotics.gaussPoly ((Real.pi:ℂ)*(t:ℂ) + (Real.pi:ℂ)*Complex.I) l).eval (r:ℂ)
          * Complex.exp (-((((Real.pi:ℂ)*(t:ℂ)) + (Real.pi:ℂ)*Complex.I) * (r:ℂ)^2))‖
        ≤ K * (1+2*Real.pi)^l * (1+|r|)^l := by
      refine hkey ((Real.pi:ℂ)*Complex.I) (by simp) (le_of_eq ?_)
      rw [Complex.norm_mul, Complex.norm_I, mul_one, norm_ofReal_complex,
        abs_of_nonneg (le_of_lt Real.pi_pos)]
    rw [hdec r t]
    calc ‖2 * ((Work.Asymptotics.gaussPoly ((Real.pi:ℂ)*(t:ℂ)) l).eval (r:ℂ)
              * Complex.exp (-(((Real.pi:ℂ)*(t:ℂ)) * (r:ℂ)^2)))
            - ((Work.Asymptotics.gaussPoly ((Real.pi:ℂ)*(t:ℂ) - (Real.pi:ℂ)*Complex.I) l).eval (r:ℂ)
              * Complex.exp (-((((Real.pi:ℂ)*(t:ℂ)) - (Real.pi:ℂ)*Complex.I) * (r:ℂ)^2)))
            - ((Work.Asymptotics.gaussPoly ((Real.pi:ℂ)*(t:ℂ) + (Real.pi:ℂ)*Complex.I) l).eval (r:ℂ)
              * Complex.exp (-((((Real.pi:ℂ)*(t:ℂ)) + (Real.pi:ℂ)*Complex.I) * (r:ℂ)^2)))‖
        ≤ ‖2 * ((Work.Asymptotics.gaussPoly ((Real.pi:ℂ)*(t:ℂ)) l).eval (r:ℂ)
              * Complex.exp (-(((Real.pi:ℂ)*(t:ℂ)) * (r:ℂ)^2)))‖
          + ‖((Work.Asymptotics.gaussPoly ((Real.pi:ℂ)*(t:ℂ) - (Real.pi:ℂ)*Complex.I) l).eval (r:ℂ)
              * Complex.exp (-((((Real.pi:ℂ)*(t:ℂ)) - (Real.pi:ℂ)*Complex.I) * (r:ℂ)^2)))‖
          + ‖((Work.Asymptotics.gaussPoly ((Real.pi:ℂ)*(t:ℂ) + (Real.pi:ℂ)*Complex.I) l).eval (r:ℂ)
              * Complex.exp (-((((Real.pi:ℂ)*(t:ℂ)) + (Real.pi:ℂ)*Complex.I) * (r:ℂ)^2)))‖ := by
          refine le_trans (norm_sub_le _ _) ?_
          exact add_le_add (norm_sub_le _ _) le_rfl
      _ = 2 * ‖(Work.Asymptotics.gaussPoly ((Real.pi:ℂ)*(t:ℂ)) l).eval (r:ℂ)
              * Complex.exp (-(((Real.pi:ℂ)*(t:ℂ)) * (r:ℂ)^2))‖
          + ‖((Work.Asymptotics.gaussPoly ((Real.pi:ℂ)*(t:ℂ) - (Real.pi:ℂ)*Complex.I) l).eval (r:ℂ)
              * Complex.exp (-((((Real.pi:ℂ)*(t:ℂ)) - (Real.pi:ℂ)*Complex.I) * (r:ℂ)^2)))‖
          + ‖((Work.Asymptotics.gaussPoly ((Real.pi:ℂ)*(t:ℂ) + (Real.pi:ℂ)*Complex.I) l).eval (r:ℂ)
              * Complex.exp (-((((Real.pi:ℂ)*(t:ℂ)) + (Real.pi:ℂ)*Complex.I) * (r:ℂ)^2)))‖ := by
          rw [norm_mul]; norm_num
      _ ≤ 2 * (K * (1+2*Real.pi)^l * (1+|r|)^l) + (K * (1+2*Real.pi)^l * (1+|r|)^l)
            + (K * (1+2*Real.pi)^l * (1+|r|)^l) := by
          linarith [h0, h1, h2]
      _ = 4 * (K * (1 + 2*Real.pi)^l) * (1 + |r|)^l := by ring

end Work.Asymptotics.Tile

namespace Work.Asymptotics.Tile

/-! ## The signed pole integral with a polynomial weight -/

/-- **Signed pole integral with the polynomial weight `(πt+δ)^s`.** -/
theorem poleIntegral_poly_weight (s m : ℕ) :
    ∃ C N : ℝ, 0 ≤ C ∧ 0 ≤ N ∧ ∀ (w : UpperHalfPlane), w ∈ KEpsilon → w.re ≠ 0 →
      ∀ (δ : ℂ) (r : ℝ),
      |r| ^ m * ‖∫ t in (w.im / 2)..1, (1 : ℂ) / ((t : ℂ) * Complex.I - (w : ℂ)) *
        (((Real.pi : ℂ) * (t : ℂ) + δ) ^ s) * Complex.exp (-(Real.pi * (r : ℂ) ^ 2 * (t : ℂ)))‖
        ≤ C * (1 + ‖δ‖) ^ s * (scale w) ^ N := by
  have hmono : ∀ u : ℕ, ∃ C N : ℝ, 0 ≤ C ∧ 0 ≤ N ∧ ∀ (w : UpperHalfPlane), w ∈ KEpsilon → w.re ≠ 0 → ∀ r : ℝ,
      |r| ^ m * ‖∫ t in (w.im / 2)..1, (1 : ℂ) / ((t : ℂ) * Complex.I - (w : ℂ)) * (t : ℂ) ^ u *
        Complex.exp (-(Real.pi * (r : ℂ) ^ 2 * (t : ℂ)))‖ ≤ C * (scale w) ^ N :=
    fun u => poleIntegral_monomial_weight m u
  let Cf : ℕ → ℝ := fun u => Classical.choose (hmono u)
  let Nf : ℕ → ℝ := fun u => Classical.choose (Classical.choose_spec (hmono u))
  have hspec : ∀ u, 0 ≤ Cf u ∧ 0 ≤ Nf u ∧ ∀ (w : UpperHalfPlane), w ∈ KEpsilon → w.re ≠ 0 → ∀ r : ℝ,
      |r| ^ m * ‖∫ t in (w.im / 2)..1, (1 : ℂ) / ((t : ℂ) * Complex.I - (w : ℂ)) * (t : ℂ) ^ u *
        Complex.exp (-(Real.pi * (r : ℂ) ^ 2 * (t : ℂ)))‖ ≤ Cf u * (scale w) ^ (Nf u) :=
    fun u => Classical.choose_spec (Classical.choose_spec (hmono u))
  refine ⟨(1 + Real.pi) ^ s * (∑ u ∈ Finset.range (s+1), Cf u),
    ∑ u ∈ Finset.range (s+1), Nf u,
    mul_nonneg (by positivity) (Finset.sum_nonneg (fun u _ => (hspec u).1)),
    Finset.sum_nonneg (fun u _ => (hspec u).2.1), ?_⟩
  intro w hw hre δ r
  have hpow : ∀ t : ℝ, ((Real.pi : ℂ) * (t : ℂ) + δ) ^ s
      = ∑ u ∈ Finset.range (s+1), ((Real.pi : ℂ) ^ u * δ ^ (s-u) * (s.choose u : ℂ)) * (t : ℂ) ^ u := by
    intro t
    rw [add_pow]
    refine Finset.sum_congr rfl (fun u hu => ?_)
    rw [mul_pow]; ring
  have hfun : (fun t : ℝ => (1 : ℂ) / ((t : ℂ) * Complex.I - (w : ℂ)) *
        (((Real.pi : ℂ) * (t : ℂ) + δ) ^ s) * Complex.exp (-(Real.pi * (r : ℂ) ^ 2 * (t : ℂ))))
      = fun t : ℝ => ∑ u ∈ Finset.range (s+1),
          ((Real.pi : ℂ) ^ u * δ ^ (s-u) * (s.choose u : ℂ)) *
          ((1 : ℂ) / ((t : ℂ) * Complex.I - (w : ℂ)) * (t : ℂ) ^ u *
            Complex.exp (-(Real.pi * (r : ℂ) ^ 2 * (t : ℂ)))) := by
    funext t
    rw [hpow t, Finset.mul_sum, Finset.sum_mul]
    exact Finset.sum_congr rfl (fun u hu => by ring)
  have hX : Continuous (fun t : ℝ => (1 : ℂ) / ((t : ℂ) * Complex.I - (w : ℂ))) := by
    refine Continuous.div continuous_const ?_ ?_
    · exact (Complex.continuous_ofReal.mul continuous_const).sub continuous_const
    · intro t h
      have hre' : ((t : ℂ) * Complex.I - (w : ℂ)).re = -w.re := by
        simp [Complex.sub_re, Complex.mul_re]
      rw [h] at hre'; simp at hre'
      exact hre (by linarith)
  have hint : ∀ u : ℕ, IntervalIntegrable (fun t : ℝ =>
      ((Real.pi : ℂ) ^ u * δ ^ (s-u) * (s.choose u : ℂ)) *
      ((1 : ℂ) / ((t : ℂ) * Complex.I - (w : ℂ)) * (t : ℂ) ^ u *
        Complex.exp (-(Real.pi * (r : ℂ) ^ 2 * (t : ℂ))))) volume (w.im / 2) 1 := by
    intro u
    exact (continuous_const.mul ((hX.mul (Complex.continuous_ofReal.pow u)).mul
      (Complex.continuous_exp.comp ((continuous_const.mul Complex.continuous_ofReal).neg)))).intervalIntegrable _ _
  rw [hfun, intervalIntegral.integral_finset_sum (fun u _ => hint u)]
  simp_rw [intervalIntegral.integral_const_mul]
  set Ntot : ℝ := ∑ u ∈ Finset.range (s+1), Nf u with hNtot
  have hsc1 : (1:ℝ) ≤ scale w := one_le_scale w
  have hNle : ∀ u ∈ Finset.range (s+1), Nf u ≤ Ntot := by
    intro u hu
    rw [hNtot]
    exact Finset.single_le_sum (fun i _ => (hspec i).2.1) hu
  have hCf0 : ∀ u, (0:ℝ) ≤ Cf u := fun u => (hspec u).1
  have hnormA : ∀ u : ℕ, ‖((Real.pi : ℂ) ^ u * δ ^ (s-u) * (s.choose u : ℂ))‖
      = Real.pi ^ u * ‖δ‖ ^ (s-u) * (s.choose u : ℝ) := by
    intro u
    rw [norm_mul, norm_mul, Complex.norm_pow, Complex.norm_pow, norm_ofReal_complex,
      abs_of_nonneg (le_of_lt Real.pi_pos), Complex.norm_natCast]
  calc |r| ^ m * ‖∑ u ∈ Finset.range (s+1),
          ((Real.pi : ℂ) ^ u * δ ^ (s-u) * (s.choose u : ℂ)) *
          (∫ t in (w.im / 2)..1, (1 : ℂ) / ((t : ℂ) * Complex.I - (w : ℂ)) * (t : ℂ) ^ u *
            Complex.exp (-(Real.pi * (r : ℂ) ^ 2 * (t : ℂ))))‖
      ≤ |r| ^ m * ∑ u ∈ Finset.range (s+1),
          ‖((Real.pi : ℂ) ^ u * δ ^ (s-u) * (s.choose u : ℂ))‖ *
          ‖∫ t in (w.im / 2)..1, (1 : ℂ) / ((t : ℂ) * Complex.I - (w : ℂ)) * (t : ℂ) ^ u *
            Complex.exp (-(Real.pi * (r : ℂ) ^ 2 * (t : ℂ)))‖ := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        refine le_trans (norm_sum_le _ _) ?_
        exact Finset.sum_le_sum (fun u _ => le_of_eq (norm_mul _ _))
      _ = ∑ u ∈ Finset.range (s+1),
          ‖((Real.pi : ℂ) ^ u * δ ^ (s-u) * (s.choose u : ℂ))‖ *
          (|r| ^ m * ‖∫ t in (w.im / 2)..1, (1 : ℂ) / ((t : ℂ) * Complex.I - (w : ℂ)) * (t : ℂ) ^ u *
            Complex.exp (-(Real.pi * (r : ℂ) ^ 2 * (t : ℂ)))‖) := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl (fun u _ => by ring)
      _ ≤ ∑ u ∈ Finset.range (s+1),
          (Real.pi ^ u * (1 + ‖δ‖) ^ (s-u) * (s.choose u : ℝ)) * (Cf u * (scale w) ^ Ntot) := by
        refine Finset.sum_le_sum (fun u hu => ?_)
        rw [hnormA u]
        have h1 : (scale w) ^ (Nf u) ≤ (scale w) ^ Ntot :=
          Real.rpow_le_rpow_of_exponent_le hsc1 (hNle u hu)
        have h2 : ‖δ‖ ^ (s-u) ≤ (1 + ‖δ‖) ^ (s-u) :=
          pow_le_pow_left₀ (norm_nonneg δ) (by linarith [norm_nonneg δ]) (s-u)
        have h3 : (0:ℝ) ≤ Real.pi ^ u := by positivity
        have h4 : (0:ℝ) ≤ (s.choose u : ℝ) := by positivity
        have hπu0 : (0:ℝ) ≤ Real.pi ^ u * ‖δ‖ ^ (s-u) * (s.choose u : ℝ) := by positivity
        have hAB : Real.pi ^ u * ‖δ‖ ^ (s-u) * (s.choose u : ℝ)
            ≤ Real.pi ^ u * (1 + ‖δ‖) ^ (s-u) * (s.choose u : ℝ) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h2 h3) h4
        calc Real.pi ^ u * ‖δ‖ ^ (s-u) * (s.choose u : ℝ) * (|r| ^ m * ‖∫ t in (w.im / 2)..1,
                (1 : ℂ) / ((t : ℂ) * Complex.I - (w : ℂ)) * (t : ℂ) ^ u *
                  Complex.exp (-(Real.pi * (r : ℂ) ^ 2 * (t : ℂ)))‖)
            ≤ Real.pi ^ u * ‖δ‖ ^ (s-u) * (s.choose u : ℝ) * (Cf u * (scale w) ^ (Nf u)) :=
              mul_le_mul_of_nonneg_left ((hspec u).2.2 w hw hre r) hπu0
          _ ≤ Real.pi ^ u * (1 + ‖δ‖) ^ (s-u) * (s.choose u : ℝ) * (Cf u * (scale w) ^ Ntot) :=
              mul_le_mul hAB (mul_le_mul_of_nonneg_left h1 (hCf0 u))
                (mul_nonneg (hCf0 u) (by positivity)) (by positivity)
      _ = (∑ u ∈ Finset.range (s+1), Real.pi ^ u * (1 + ‖δ‖) ^ (s-u) * (s.choose u : ℝ) * Cf u)
            * (scale w) ^ Ntot := by
        rw [Finset.sum_mul]
        exact Finset.sum_congr rfl (fun u _ => by rw [← mul_assoc])
      _ ≤ ((1 + Real.pi) ^ s * (∑ u ∈ Finset.range (s+1), Cf u)) * (1 + ‖δ‖) ^ s * (scale w) ^ Ntot := by
        refine mul_le_mul_of_nonneg_right ?_ (by positivity)
        have hX0 : ∀ i : ℕ, (0:ℝ) ≤ Real.pi ^ i * (1 + ‖δ‖) ^ (s-i) * (s.choose i : ℝ) :=
          fun i => by positivity
        have hbin : ∑ u ∈ Finset.range (s+1), Real.pi ^ u * (1 + ‖δ‖) ^ (s-u) * (s.choose u : ℝ)
            = (Real.pi + (1 + ‖δ‖)) ^ s :=
          (add_pow Real.pi (1 + ‖δ‖) s).symm
        have h₁ : ∑ u ∈ Finset.range (s+1), Real.pi ^ u * (1 + ‖δ‖) ^ (s-u) * (s.choose u : ℝ) * Cf u
            ≤ (∑ u ∈ Finset.range (s+1), Real.pi ^ u * (1 + ‖δ‖) ^ (s-u) * (s.choose u : ℝ))
              * (∑ u ∈ Finset.range (s+1), Cf u) := by
          rw [Finset.sum_mul]
          exact Finset.sum_le_sum (fun u hu => mul_le_mul_of_nonneg_left
            (Finset.single_le_sum (fun i _ => hCf0 i) hu) (hX0 u))
        rw [hbin] at h₁
        refine le_trans h₁ ?_
        have hsumC : (0:ℝ) ≤ ∑ u ∈ Finset.range (s+1), Cf u :=
          Finset.sum_nonneg (fun u _ => hCf0 u)
        have hle : Real.pi + (1 + ‖δ‖) ≤ (1 + Real.pi) * (1 + ‖δ‖) := by
          nlinarith [norm_nonneg δ, Real.pi_pos]
        have hpow : (Real.pi + (1 + ‖δ‖)) ^ s ≤ (1 + Real.pi) ^ s * (1 + ‖δ‖) ^ s := by
          calc (Real.pi + (1 + ‖δ‖)) ^ s ≤ ((1 + Real.pi) * (1 + ‖δ‖)) ^ s :=
                pow_le_pow_left₀ (by positivity) hle s
            _ = (1 + Real.pi) ^ s * (1 + ‖δ‖) ^ s := by rw [mul_pow]
        calc (Real.pi + (1 + ‖δ‖)) ^ s * (∑ u ∈ Finset.range (s+1), Cf u)
            ≤ ((1 + Real.pi) ^ s * (1 + ‖δ‖) ^ s) * (∑ u ∈ Finset.range (s+1), Cf u) :=
              mul_le_mul_of_nonneg_right hpow hsumC
          _ = ((1 + Real.pi) ^ s * (∑ u ∈ Finset.range (s+1), Cf u)) * (1 + ‖δ‖) ^ s := by ring

end Work.Asymptotics.Tile

namespace Work.Asymptotics.Tile

/-! ## The principal-part contribution of one shifted Gaussian term -/

/-- **The signed pole integral against `∂^l` of one shifted Gaussian term.**  For a shift `δ` with
`Re δ = 0`, the monomial expansion of `gaussPoly (πt+δ) l` and the polynomial bound
`poleIntegral_poly_weight` give a uniform power bound in `scale w`. -/
theorem ppDterm_bound (k l : ℕ) (δ : ℂ) (hδ : δ.re = 0) :
    ∃ C N : ℝ, 0 ≤ C ∧ 0 ≤ N ∧ ∀ (w : UpperHalfPlane), w ∈ KEpsilon → w.re ≠ 0 → ∀ r : ℝ,
      |r| ^ k * ‖∫ t in (w.im / 2)..1, (1 : ℂ) / ((t : ℂ) * Complex.I - (w : ℂ)) *
        ((Work.Asymptotics.gaussPoly ((Real.pi:ℂ)*(t:ℂ) + δ) l).eval (r:ℂ) *
          Complex.exp (-(((Real.pi:ℂ)*(t:ℂ) + δ) * (r:ℂ)^2)))‖ ≤ C * (scale w) ^ N := by
  obtain ⟨coef, hcoef⟩ := gaussPoly_monomial_expansion l
  have h4 : ∀ s' m' : ℕ, ∃ C N : ℝ, 0 ≤ C ∧ 0 ≤ N ∧ ∀ (w : UpperHalfPlane), w ∈ KEpsilon → w.re ≠ 0 → ∀ r : ℝ,
      |r| ^ m' * ‖∫ t in (w.im / 2)..1, (1 : ℂ) / ((t : ℂ) * Complex.I - (w : ℂ)) *
        (((Real.pi:ℂ)*(t:ℂ) + δ) ^ s') * Complex.exp (-(Real.pi * (r:ℂ) ^ 2 * (t:ℂ)))‖
        ≤ C * (scale w) ^ N := fun s' m' => by
      obtain ⟨C, N, hC, hN, hb⟩ := poleIntegral_poly_weight s' m'
      refine ⟨C * (1 + ‖δ‖)^s', N, mul_nonneg hC (pow_nonneg (by positivity) _), hN, ?_⟩
      intro w hw hre r
      refine le_trans (hb w hw hre δ r) (le_of_eq ?_)
      ring
  let Cf : ℕ → ℕ → ℝ := fun s' m' => Classical.choose (h4 s' m')
  let Nf : ℕ → ℕ → ℝ := fun s' m' => Classical.choose (Classical.choose_spec (h4 s' m'))
  have hspec : ∀ s' m', 0 ≤ Cf s' m' ∧ 0 ≤ Nf s' m' ∧ ∀ (w : UpperHalfPlane), w ∈ KEpsilon → w.re ≠ 0 → ∀ r : ℝ,
      |r| ^ m' * ‖∫ t in (w.im / 2)..1, (1 : ℂ) / ((t : ℂ) * Complex.I - (w : ℂ)) *
        (((Real.pi:ℂ)*(t:ℂ) + δ) ^ s') * Complex.exp (-(Real.pi * (r:ℂ) ^ 2 * (t:ℂ)))‖
        ≤ Cf s' m' * (scale w) ^ (Nf s' m') :=
    fun s' m' => Classical.choose_spec (Classical.choose_spec (h4 s' m'))
  refine ⟨∑ i ∈ Finset.range (l+1), ∑ s' ∈ Finset.range (l+1), ‖coef i s'‖ * Cf s' (k+i),
    ∑ i ∈ Finset.range (l+1), ∑ s' ∈ Finset.range (l+1), Nf s' (k+i),
    Finset.sum_nonneg (fun i _ => Finset.sum_nonneg
      (fun s' _ => mul_nonneg (norm_nonneg _) (hspec s' (k+i)).1)),
    Finset.sum_nonneg (fun i _ => Finset.sum_nonneg
      (fun s' _ => (hspec s' (k+i)).2.1)), ?_⟩
  intro w hw hre r
  have hcontX : Continuous (fun t : ℝ => (1 : ℂ) / ((t : ℂ) * Complex.I - (w : ℂ))) := by
    refine Continuous.div continuous_const ?_ ?_
    · exact (Complex.continuous_ofReal.mul continuous_const).sub continuous_const
    · intro t h
      have hre' : ((t : ℂ) * Complex.I - (w : ℂ)).re = -w.re := by
        simp [Complex.sub_re, Complex.mul_re]
      rw [h] at hre'; simp at hre'
      exact hre (by linarith)
  have hcontA : Continuous (fun t : ℝ => (Real.pi:ℂ)*(t:ℂ) + δ) :=
    (continuous_const.mul Complex.continuous_ofReal).add continuous_const
  have hcontg : ∀ i s' : ℕ, Continuous (fun t : ℝ =>
      ((coef i s' : ℂ) * (r:ℂ)^i * Complex.exp (-(δ * (r:ℂ)^2))) *
      ((1 : ℂ) / ((t : ℂ) * Complex.I - (w : ℂ)) * (((Real.pi:ℂ)*(t:ℂ) + δ) ^ s') *
        Complex.exp (-(Real.pi * (r:ℂ) ^ 2 * (t:ℂ))))) := by
    intro i s'
    exact continuous_const.mul ((hcontX.mul (hcontA.pow s')).mul
      (Complex.continuous_exp.comp ((continuous_const.mul Complex.continuous_ofReal).neg)))
  have hfun : (fun t : ℝ => (1 : ℂ) / ((t : ℂ) * Complex.I - (w : ℂ)) *
        ((Work.Asymptotics.gaussPoly ((Real.pi:ℂ)*(t:ℂ) + δ) l).eval (r:ℂ) *
          Complex.exp (-(((Real.pi:ℂ)*(t:ℂ) + δ) * (r:ℂ)^2))))
      = fun t : ℝ => ∑ i ∈ Finset.range (l+1), ∑ s' ∈ Finset.range (l+1),
          ((coef i s' : ℂ) * (r:ℂ)^i * Complex.exp (-(δ * (r:ℂ)^2))) *
          ((1 : ℂ) / ((t : ℂ) * Complex.I - (w : ℂ)) * (((Real.pi:ℂ)*(t:ℂ) + δ) ^ s') *
            Complex.exp (-(Real.pi * (r:ℂ) ^ 2 * (t:ℂ)))) := by
    funext t
    rw [hcoef r ((Real.pi:ℂ)*(t:ℂ) + δ)]
    rw [show Complex.exp (-(((Real.pi:ℂ)*(t:ℂ) + δ) * (r:ℂ)^2))
        = Complex.exp (-(Real.pi * (r:ℂ)^2 * (t:ℂ))) * Complex.exp (-(δ * (r:ℂ)^2)) by
      rw [← Complex.exp_add]; congr 1; push_cast; ring]
    rw [Finset.sum_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [Finset.sum_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun s' _ => ?_)
    ring
  rw [hfun]
  rw [intervalIntegral.integral_finset_sum (fun i _ =>
    (continuous_finsetSum _ (fun s' _ => hcontg i s')).intervalIntegrable _ _)]
  have hInt : ∀ i : ℕ, (∫ t in (w.im / 2)..1, ∑ s' ∈ Finset.range (l+1),
        ((coef i s' : ℂ) * (r:ℂ)^i * Complex.exp (-(δ * (r:ℂ)^2))) *
        ((1 : ℂ) / ((t : ℂ) * Complex.I - (w : ℂ)) * (((Real.pi:ℂ)*(t:ℂ) + δ) ^ s') *
          Complex.exp (-(Real.pi * (r:ℂ) ^ 2 * (t:ℂ)))))
      = ∑ s' ∈ Finset.range (l+1), ((coef i s' : ℂ) * (r:ℂ)^i * Complex.exp (-(δ * (r:ℂ)^2))) *
        (∫ t in (w.im / 2)..1, (1 : ℂ) / ((t : ℂ) * Complex.I - (w : ℂ)) *
          (((Real.pi:ℂ)*(t:ℂ) + δ) ^ s') *
          Complex.exp (-(Real.pi * (r:ℂ) ^ 2 * (t:ℂ)))) := by
    intro i
    rw [intervalIntegral.integral_finset_sum (fun s' _ => (hcontg i s').intervalIntegrable _ _)]
    simp only [intervalIntegral.integral_const_mul]
  simp_rw [hInt]
  set Ntot : ℝ := ∑ i ∈ Finset.range (l+1), ∑ s' ∈ Finset.range (l+1), Nf s' (k+i) with hNtot
  have hsc1 : (1:ℝ) ≤ scale w := one_le_scale w
  have hCc : ∀ i s' : ℕ, ‖(coef i s' : ℂ) * (r:ℂ)^i * Complex.exp (-(δ * (r:ℂ)^2))‖
      = ‖coef i s'‖ * |r|^i := by
    intro i s'
    rw [norm_mul, norm_mul, Complex.norm_pow, norm_ofReal_complex, norm_exp_neg_mul_sq, hδ]
    simp
  have hNle : ∀ i ∈ Finset.range (l+1), ∀ s' ∈ Finset.range (l+1), Nf s' (k+i) ≤ Ntot := by
    intro i hi s' hs'
    rw [hNtot]
    refine le_trans (Finset.single_le_sum (fun s'' _ => (hspec s'' (k+i)).2.1) hs') ?_
    exact Finset.single_le_sum (fun i' _ => Finset.sum_nonneg
      (fun s'' _ => (hspec s'' (k+i')).2.1)) hi
  calc |r| ^ k * ‖∑ i ∈ Finset.range (l+1), ∑ s' ∈ Finset.range (l+1),
          ((coef i s' : ℂ) * (r:ℂ)^i * Complex.exp (-(δ * (r:ℂ)^2))) *
          (∫ t in (w.im / 2)..1, (1 : ℂ) / ((t : ℂ) * Complex.I - (w : ℂ)) *
            (((Real.pi:ℂ)*(t:ℂ) + δ) ^ s') *
            Complex.exp (-(Real.pi * (r:ℂ) ^ 2 * (t:ℂ))))‖
      ≤ |r| ^ k * ∑ i ∈ Finset.range (l+1), ∑ s' ∈ Finset.range (l+1),
          ‖(coef i s' : ℂ) * (r:ℂ)^i * Complex.exp (-(δ * (r:ℂ)^2))‖ *
          ‖∫ t in (w.im / 2)..1, (1 : ℂ) / ((t : ℂ) * Complex.I - (w : ℂ)) *
            (((Real.pi:ℂ)*(t:ℂ) + δ) ^ s') *
            Complex.exp (-(Real.pi * (r:ℂ) ^ 2 * (t:ℂ)))‖ := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        refine le_trans (norm_sum_le _ _) ?_
        refine Finset.sum_le_sum (fun i _ => ?_)
        refine le_trans (norm_sum_le _ _) ?_
        exact Finset.sum_le_sum (fun s' _ => le_of_eq (norm_mul _ _))
      _ = ∑ i ∈ Finset.range (l+1), ∑ s' ∈ Finset.range (l+1),
          ‖coef i s'‖ * (|r|^(k+i) * ‖∫ t in (w.im / 2)..1, (1 : ℂ) / ((t : ℂ) * Complex.I - (w : ℂ)) *
            (((Real.pi:ℂ)*(t:ℂ) + δ) ^ s') *
            Complex.exp (-(Real.pi * (r:ℂ) ^ 2 * (t:ℂ)))‖) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl (fun i _ => ?_)
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl (fun s' _ => ?_)
        rw [hCc i s']
        ring
      _ ≤ ∑ i ∈ Finset.range (l+1), ∑ s' ∈ Finset.range (l+1),
          ‖coef i s'‖ * (Cf s' (k+i) * (scale w) ^ Ntot) := by
        refine Finset.sum_le_sum (fun i hi => Finset.sum_le_sum (fun s' hs' => ?_))
        have h1 : (scale w) ^ (Nf s' (k+i)) ≤ (scale w) ^ Ntot :=
          Real.rpow_le_rpow_of_exponent_le hsc1 (hNle i hi s' hs')
        refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
        calc |r|^(k+i) * ‖∫ t in (w.im / 2)..1, (1 : ℂ) / ((t : ℂ) * Complex.I - (w : ℂ)) *
              (((Real.pi:ℂ)*(t:ℂ) + δ) ^ s') *
              Complex.exp (-(Real.pi * (r:ℂ) ^ 2 * (t:ℂ)))‖
            ≤ Cf s' (k+i) * (scale w) ^ (Nf s' (k+i)) := (hspec s' (k+i)).2.2 w hw hre r
          _ ≤ Cf s' (k+i) * (scale w) ^ Ntot := mul_le_mul_of_nonneg_left h1 (hspec s' (k+i)).1
      _ = (∑ i ∈ Finset.range (l+1), ∑ s' ∈ Finset.range (l+1), ‖coef i s'‖ * Cf s' (k+i))
            * (scale w) ^ Ntot := by
        rw [Finset.sum_mul]
        refine Finset.sum_congr rfl (fun i _ => ?_)
        rw [Finset.sum_mul]
        refine Finset.sum_congr rfl (fun s' _ => by ring)

end Work.Asymptotics.Tile

namespace Work.Asymptotics.Tile

/-- **The principal-part contribution `|r|^k ‖∫ 1/(it-w) ∂_r^l (sinSq · e^{-π·²t})‖`** on the
window `[Im w/2, 1]`. -/
theorem ppLayerDeriv_bound (k l : ℕ) :
    ∃ C N : ℝ, 0 ≤ C ∧ 0 ≤ N ∧ ∀ (w : UpperHalfPlane), w ∈ KEpsilon → w.re ≠ 0 → ∀ r : ℝ,
      |r| ^ k * ‖∫ t in (w.im / 2)..1, (1 : ℂ) / ((t : ℂ) * Complex.I - (w : ℂ)) *
        iteratedDeriv l (fun x : ℝ => Work.Asymptotics.sinSq x *
          Complex.exp (-(Real.pi * (x : ℂ) ^ 2 * (t : ℂ)))) r‖ ≤ C * (scale w) ^ N := by
  obtain ⟨C0, N0, hC0, hN0, hb0⟩ := ppDterm_bound k l 0 (by simp)
  obtain ⟨C1, N1, hC1, hN1, hb1⟩ := ppDterm_bound k l (-((Real.pi:ℂ)*Complex.I)) (by simp)
  obtain ⟨C2, N2, hC2, hN2, hb2⟩ := ppDterm_bound k l ((Real.pi:ℂ)*Complex.I) (by simp)
  refine ⟨2*C0 + C1 + C2, N0 + N1 + N2, by positivity, by positivity, ?_⟩
  intro w hw hre r
  have hcontX : Continuous (fun t : ℝ => (1 : ℂ) / ((t : ℂ) * Complex.I - (w : ℂ))) := by
    refine Continuous.div continuous_const ?_ ?_
    · exact (Complex.continuous_ofReal.mul continuous_const).sub continuous_const
    · intro t h
      have hre' : ((t : ℂ) * Complex.I - (w : ℂ)).re = -w.re := by
        simp [Complex.sub_re, Complex.mul_re]
      rw [h] at hre'; simp at hre'
      exact hre (by linarith)
  have hcontShift : ∀ δ : ℂ, Continuous (fun t : ℝ => (Real.pi:ℂ)*(t:ℂ) + δ) := fun δ =>
    (continuous_const.mul Complex.continuous_ofReal).add continuous_const
  have hcontG : ∀ δ : ℂ, Continuous (fun t : ℝ =>
      (Work.Asymptotics.gaussPoly ((Real.pi:ℂ)*(t:ℂ) + δ) l).eval (r:ℂ)
        * Complex.exp (-(((Real.pi:ℂ)*(t:ℂ) + δ) * (r:ℂ)^2))) := fun δ =>
    ((continuous_gaussPoly_eval l r).comp (hcontShift δ)).mul
      (Complex.continuous_exp.comp (((hcontShift δ).mul continuous_const).neg))
  have hcontA0 : Continuous (fun t : ℝ => (1 : ℂ) / ((t : ℂ) * Complex.I - (w : ℂ)) *
      ((Work.Asymptotics.gaussPoly ((Real.pi:ℂ)*(t:ℂ)) l).eval (r:ℂ)
        * Complex.exp (-(((Real.pi:ℂ)*(t:ℂ)) * (r:ℂ)^2)))) := by
    have h1 : Continuous (fun t : ℝ => (Work.Asymptotics.gaussPoly ((Real.pi:ℂ)*(t:ℂ)) l).eval (r:ℂ)) :=
      (continuous_gaussPoly_eval l r).comp
        (show Continuous (fun t : ℝ => (Real.pi:ℂ)*(t:ℂ)) from
          continuous_const.mul Complex.continuous_ofReal)
    have h2 : Continuous (fun t : ℝ => Complex.exp (-(((Real.pi:ℂ)*(t:ℂ)) * (r:ℂ)^2))) :=
      Complex.continuous_exp.comp (((continuous_const.mul Complex.continuous_ofReal).mul
        continuous_const).neg)
    exact hcontX.mul (h1.mul h2)
  have hcontA1 : Continuous (fun t : ℝ => (1 : ℂ) / ((t : ℂ) * Complex.I - (w : ℂ)) *
      ((Work.Asymptotics.gaussPoly ((Real.pi:ℂ)*(t:ℂ) - (Real.pi:ℂ)*Complex.I) l).eval (r:ℂ)
        * Complex.exp (-((((Real.pi:ℂ)*(t:ℂ)) - (Real.pi:ℂ)*Complex.I) * (r:ℂ)^2)))) :=
    hcontX.mul (hcontG (-((Real.pi:ℂ)*Complex.I)))
  have hcontA2 : Continuous (fun t : ℝ => (1 : ℂ) / ((t : ℂ) * Complex.I - (w : ℂ)) *
      ((Work.Asymptotics.gaussPoly ((Real.pi:ℂ)*(t:ℂ) + (Real.pi:ℂ)*Complex.I) l).eval (r:ℂ)
        * Complex.exp (-((((Real.pi:ℂ)*(t:ℂ)) + (Real.pi:ℂ)*Complex.I) * (r:ℂ)^2)))) :=
    hcontX.mul (hcontG ((Real.pi:ℂ)*Complex.I))
  have hIA0 : IntervalIntegrable (fun t : ℝ => (1 : ℂ) / ((t : ℂ) * Complex.I - (w : ℂ)) *
      ((Work.Asymptotics.gaussPoly ((Real.pi:ℂ)*(t:ℂ)) l).eval (r:ℂ)
        * Complex.exp (-(((Real.pi:ℂ)*(t:ℂ)) * (r:ℂ)^2)))) volume (w.im / 2) 1 :=
    hcontA0.intervalIntegrable (w.im / 2) 1
  have hIA1 : IntervalIntegrable (fun t : ℝ => (1 : ℂ) / ((t : ℂ) * Complex.I - (w : ℂ)) *
      ((Work.Asymptotics.gaussPoly ((Real.pi:ℂ)*(t:ℂ) - (Real.pi:ℂ)*Complex.I) l).eval (r:ℂ)
        * Complex.exp (-((((Real.pi:ℂ)*(t:ℂ)) - (Real.pi:ℂ)*Complex.I) * (r:ℂ)^2)))) volume (w.im / 2) 1 :=
    hcontA1.intervalIntegrable (w.im / 2) 1
  have hIA2 : IntervalIntegrable (fun t : ℝ => (1 : ℂ) / ((t : ℂ) * Complex.I - (w : ℂ)) *
      ((Work.Asymptotics.gaussPoly ((Real.pi:ℂ)*(t:ℂ) + (Real.pi:ℂ)*Complex.I) l).eval (r:ℂ)
        * Complex.exp (-((((Real.pi:ℂ)*(t:ℂ)) + (Real.pi:ℂ)*Complex.I) * (r:ℂ)^2)))) volume (w.im / 2) 1 :=
    hcontA2.intervalIntegrable (w.im / 2) 1
  have hI2A0 : IntervalIntegrable (fun t : ℝ =>
      2 * ((1 : ℂ) / ((t : ℂ) * Complex.I - (w : ℂ)) *
          ((Work.Asymptotics.gaussPoly ((Real.pi:ℂ)*(t:ℂ)) l).eval (r:ℂ)
            * Complex.exp (-(((Real.pi:ℂ)*(t:ℂ)) * (r:ℂ)^2))))) volume (w.im / 2) 1 :=
    (hcontA0.const_mul 2).intervalIntegrable (w.im / 2) 1
  have hI012 : IntervalIntegrable (fun t : ℝ =>
      2 * ((1 : ℂ) / ((t : ℂ) * Complex.I - (w : ℂ)) *
          ((Work.Asymptotics.gaussPoly ((Real.pi:ℂ)*(t:ℂ)) l).eval (r:ℂ)
            * Complex.exp (-(((Real.pi:ℂ)*(t:ℂ)) * (r:ℂ)^2))))
        - ((1 : ℂ) / ((t : ℂ) * Complex.I - (w : ℂ)) *
          ((Work.Asymptotics.gaussPoly ((Real.pi:ℂ)*(t:ℂ) - (Real.pi:ℂ)*Complex.I) l).eval (r:ℂ)
            * Complex.exp (-((((Real.pi:ℂ)*(t:ℂ)) - (Real.pi:ℂ)*Complex.I) * (r:ℂ)^2))))
        - ((1 : ℂ) / ((t : ℂ) * Complex.I - (w : ℂ)) *
          ((Work.Asymptotics.gaussPoly ((Real.pi:ℂ)*(t:ℂ) + (Real.pi:ℂ)*Complex.I) l).eval (r:ℂ)
            * Complex.exp (-((((Real.pi:ℂ)*(t:ℂ)) + (Real.pi:ℂ)*Complex.I) * (r:ℂ)^2))))) volume (w.im / 2) 1 :=
    (((hcontA0.const_mul 2).sub hcontA1).sub hcontA2).intervalIntegrable (w.im / 2) 1
  have hI01 : IntervalIntegrable (fun t : ℝ =>
      2 * ((1 : ℂ) / ((t : ℂ) * Complex.I - (w : ℂ)) *
          ((Work.Asymptotics.gaussPoly ((Real.pi:ℂ)*(t:ℂ)) l).eval (r:ℂ)
            * Complex.exp (-(((Real.pi:ℂ)*(t:ℂ)) * (r:ℂ)^2))))
        - ((1 : ℂ) / ((t : ℂ) * Complex.I - (w : ℂ)) *
          ((Work.Asymptotics.gaussPoly ((Real.pi:ℂ)*(t:ℂ) - (Real.pi:ℂ)*Complex.I) l).eval (r:ℂ)
            * Complex.exp (-((((Real.pi:ℂ)*(t:ℂ)) - (Real.pi:ℂ)*Complex.I) * (r:ℂ)^2))))) volume (w.im / 2) 1 :=
    ((hcontA0.const_mul 2).sub hcontA1).intervalIntegrable (w.im / 2) 1
  have hdec : ∀ t : ℝ, (1 : ℂ) / ((t : ℂ) * Complex.I - (w : ℂ)) *
        iteratedDeriv l (fun x : ℝ => Work.Asymptotics.sinSq x *
          Complex.exp (-(Real.pi * (x : ℂ) ^ 2 * (t : ℂ)))) r
      = 2 * ((1 : ℂ) / ((t : ℂ) * Complex.I - (w : ℂ)) *
          ((Work.Asymptotics.gaussPoly ((Real.pi:ℂ)*(t:ℂ)) l).eval (r:ℂ)
            * Complex.exp (-(((Real.pi:ℂ)*(t:ℂ)) * (r:ℂ)^2))))
        - ((1 : ℂ) / ((t : ℂ) * Complex.I - (w : ℂ)) *
          ((Work.Asymptotics.gaussPoly ((Real.pi:ℂ)*(t:ℂ) - (Real.pi:ℂ)*Complex.I) l).eval (r:ℂ)
            * Complex.exp (-((((Real.pi:ℂ)*(t:ℂ)) - (Real.pi:ℂ)*Complex.I) * (r:ℂ)^2))))
        - ((1 : ℂ) / ((t : ℂ) * Complex.I - (w : ℂ)) *
          ((Work.Asymptotics.gaussPoly ((Real.pi:ℂ)*(t:ℂ) + (Real.pi:ℂ)*Complex.I) l).eval (r:ℂ)
            * Complex.exp (-((((Real.pi:ℂ)*(t:ℂ)) + (Real.pi:ℂ)*Complex.I) * (r:ℂ)^2)))) := by
    intro t
    rw [Dl_eq l r t]; ring
  have hsplit : (∫ t in (w.im / 2)..1, (1 : ℂ) / ((t : ℂ) * Complex.I - (w : ℂ)) *
        iteratedDeriv l (fun x : ℝ => Work.Asymptotics.sinSq x *
          Complex.exp (-(Real.pi * (x : ℂ) ^ 2 * (t : ℂ)))) r)
      = 2 * (∫ t in (w.im / 2)..1, (1 : ℂ) / ((t : ℂ) * Complex.I - (w : ℂ)) *
          ((Work.Asymptotics.gaussPoly ((Real.pi:ℂ)*(t:ℂ)) l).eval (r:ℂ)
            * Complex.exp (-(((Real.pi:ℂ)*(t:ℂ)) * (r:ℂ)^2))))
        - (∫ t in (w.im / 2)..1, (1 : ℂ) / ((t : ℂ) * Complex.I - (w : ℂ)) *
          ((Work.Asymptotics.gaussPoly ((Real.pi:ℂ)*(t:ℂ) - (Real.pi:ℂ)*Complex.I) l).eval (r:ℂ)
            * Complex.exp (-((((Real.pi:ℂ)*(t:ℂ)) - (Real.pi:ℂ)*Complex.I) * (r:ℂ)^2))))
        - (∫ t in (w.im / 2)..1, (1 : ℂ) / ((t : ℂ) * Complex.I - (w : ℂ)) *
          ((Work.Asymptotics.gaussPoly ((Real.pi:ℂ)*(t:ℂ) + (Real.pi:ℂ)*Complex.I) l).eval (r:ℂ)
            * Complex.exp (-((((Real.pi:ℂ)*(t:ℂ)) + (Real.pi:ℂ)*Complex.I) * (r:ℂ)^2)))) := by
    rw [show (fun t : ℝ => (1 : ℂ) / ((t : ℂ) * Complex.I - (w : ℂ)) *
        iteratedDeriv l (fun x : ℝ => Work.Asymptotics.sinSq x *
          Complex.exp (-(Real.pi * (x : ℂ) ^ 2 * (t : ℂ)))) r)
      = fun t : ℝ => 2 * ((1 : ℂ) / ((t : ℂ) * Complex.I - (w : ℂ)) *
          ((Work.Asymptotics.gaussPoly ((Real.pi:ℂ)*(t:ℂ)) l).eval (r:ℂ)
            * Complex.exp (-(((Real.pi:ℂ)*(t:ℂ)) * (r:ℂ)^2))))
        - ((1 : ℂ) / ((t : ℂ) * Complex.I - (w : ℂ)) *
          ((Work.Asymptotics.gaussPoly ((Real.pi:ℂ)*(t:ℂ) - (Real.pi:ℂ)*Complex.I) l).eval (r:ℂ)
            * Complex.exp (-((((Real.pi:ℂ)*(t:ℂ)) - (Real.pi:ℂ)*Complex.I) * (r:ℂ)^2))))
        - ((1 : ℂ) / ((t : ℂ) * Complex.I - (w : ℂ)) *
          ((Work.Asymptotics.gaussPoly ((Real.pi:ℂ)*(t:ℂ) + (Real.pi:ℂ)*Complex.I) l).eval (r:ℂ)
            * Complex.exp (-((((Real.pi:ℂ)*(t:ℂ)) + (Real.pi:ℂ)*Complex.I) * (r:ℂ)^2))))
      from funext hdec]
    rw [intervalIntegral.integral_sub hI01 hIA2, intervalIntegral.integral_sub hI2A0 hIA1,
        intervalIntegral.integral_const_mul]
  have hb0' : |r| ^ k * ‖∫ t in (w.im / 2)..1, (1 : ℂ) / ((t : ℂ) * Complex.I - (w : ℂ)) *
      ((Work.Asymptotics.gaussPoly ((Real.pi:ℂ)*(t:ℂ)) l).eval (r:ℂ)
        * Complex.exp (-(((Real.pi:ℂ)*(t:ℂ)) * (r:ℂ)^2)))‖ ≤ C0 * (scale w) ^ N0 := by
    have := hb0 w hw hre r
    simpa using this
  have hb1' : |r| ^ k * ‖∫ t in (w.im / 2)..1, (1 : ℂ) / ((t : ℂ) * Complex.I - (w : ℂ)) *
      ((Work.Asymptotics.gaussPoly ((Real.pi:ℂ)*(t:ℂ) - (Real.pi:ℂ)*Complex.I) l).eval (r:ℂ)
        * Complex.exp (-((((Real.pi:ℂ)*(t:ℂ)) - (Real.pi:ℂ)*Complex.I) * (r:ℂ)^2)))‖ ≤ C1 * (scale w) ^ N1 :=
    hb1 w hw hre r
  have hb2' : |r| ^ k * ‖∫ t in (w.im / 2)..1, (1 : ℂ) / ((t : ℂ) * Complex.I - (w : ℂ)) *
      ((Work.Asymptotics.gaussPoly ((Real.pi:ℂ)*(t:ℂ) + (Real.pi:ℂ)*Complex.I) l).eval (r:ℂ)
        * Complex.exp (-((((Real.pi:ℂ)*(t:ℂ)) + (Real.pi:ℂ)*Complex.I) * (r:ℂ)^2)))‖ ≤ C2 * (scale w) ^ N2 :=
    hb2 w hw hre r
  calc |r| ^ k * ‖∫ t in (w.im / 2)..1, (1 : ℂ) / ((t : ℂ) * Complex.I - (w : ℂ)) *
        iteratedDeriv l (fun x : ℝ => Work.Asymptotics.sinSq x *
          Complex.exp (-(Real.pi * (x : ℂ) ^ 2 * (t : ℂ)))) r‖
      = |r| ^ k * ‖2 * (∫ t in (w.im / 2)..1, (1 : ℂ) / ((t : ℂ) * Complex.I - (w : ℂ)) *
            ((Work.Asymptotics.gaussPoly ((Real.pi:ℂ)*(t:ℂ)) l).eval (r:ℂ)
              * Complex.exp (-(((Real.pi:ℂ)*(t:ℂ)) * (r:ℂ)^2))))
          - (∫ t in (w.im / 2)..1, (1 : ℂ) / ((t : ℂ) * Complex.I - (w : ℂ)) *
            ((Work.Asymptotics.gaussPoly ((Real.pi:ℂ)*(t:ℂ) - (Real.pi:ℂ)*Complex.I) l).eval (r:ℂ)
              * Complex.exp (-((((Real.pi:ℂ)*(t:ℂ)) - (Real.pi:ℂ)*Complex.I) * (r:ℂ)^2))))
          - (∫ t in (w.im / 2)..1, (1 : ℂ) / ((t : ℂ) * Complex.I - (w : ℂ)) *
            ((Work.Asymptotics.gaussPoly ((Real.pi:ℂ)*(t:ℂ) + (Real.pi:ℂ)*Complex.I) l).eval (r:ℂ)
              * Complex.exp (-((((Real.pi:ℂ)*(t:ℂ)) + (Real.pi:ℂ)*Complex.I) * (r:ℂ)^2))))‖ := by
        rw [hsplit]
      _ ≤ |r| ^ k * (‖2 * (∫ t in (w.im / 2)..1, (1 : ℂ) / ((t : ℂ) * Complex.I - (w : ℂ)) *
              ((Work.Asymptotics.gaussPoly ((Real.pi:ℂ)*(t:ℂ)) l).eval (r:ℂ)
                * Complex.exp (-(((Real.pi:ℂ)*(t:ℂ)) * (r:ℂ)^2))))‖
            + ‖(∫ t in (w.im / 2)..1, (1 : ℂ) / ((t : ℂ) * Complex.I - (w : ℂ)) *
              ((Work.Asymptotics.gaussPoly ((Real.pi:ℂ)*(t:ℂ) - (Real.pi:ℂ)*Complex.I) l).eval (r:ℂ)
                * Complex.exp (-((((Real.pi:ℂ)*(t:ℂ)) - (Real.pi:ℂ)*Complex.I) * (r:ℂ)^2))))‖
            + ‖(∫ t in (w.im / 2)..1, (1 : ℂ) / ((t : ℂ) * Complex.I - (w : ℂ)) *
              ((Work.Asymptotics.gaussPoly ((Real.pi:ℂ)*(t:ℂ) + (Real.pi:ℂ)*Complex.I) l).eval (r:ℂ)
                * Complex.exp (-((((Real.pi:ℂ)*(t:ℂ)) + (Real.pi:ℂ)*Complex.I) * (r:ℂ)^2))))‖) := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        refine le_trans (norm_sub_le _ _) ?_
        exact add_le_add (norm_sub_le _ _) le_rfl
      _ = 2 * (|r| ^ k * ‖∫ t in (w.im / 2)..1, (1 : ℂ) / ((t : ℂ) * Complex.I - (w : ℂ)) *
              ((Work.Asymptotics.gaussPoly ((Real.pi:ℂ)*(t:ℂ)) l).eval (r:ℂ)
                * Complex.exp (-(((Real.pi:ℂ)*(t:ℂ)) * (r:ℂ)^2)))‖)
            + |r| ^ k * ‖∫ t in (w.im / 2)..1, (1 : ℂ) / ((t : ℂ) * Complex.I - (w : ℂ)) *
              ((Work.Asymptotics.gaussPoly ((Real.pi:ℂ)*(t:ℂ) - (Real.pi:ℂ)*Complex.I) l).eval (r:ℂ)
                * Complex.exp (-((((Real.pi:ℂ)*(t:ℂ)) - (Real.pi:ℂ)*Complex.I) * (r:ℂ)^2)))‖
            + |r| ^ k * ‖∫ t in (w.im / 2)..1, (1 : ℂ) / ((t : ℂ) * Complex.I - (w : ℂ)) *
              ((Work.Asymptotics.gaussPoly ((Real.pi:ℂ)*(t:ℂ) + (Real.pi:ℂ)*Complex.I) l).eval (r:ℂ)
                * Complex.exp (-((((Real.pi:ℂ)*(t:ℂ)) + (Real.pi:ℂ)*Complex.I) * (r:ℂ)^2)))‖ := by
        rw [norm_mul, Complex.norm_ofNat]; ring
      _ ≤ 2 * (C0 * (scale w) ^ N0) + C1 * (scale w) ^ N1 + C2 * (scale w) ^ N2 := by
        linarith [hb0', hb1', hb2']
      _ ≤ (2*C0 + C1 + C2) * (scale w) ^ (N0 + N1 + N2) := by
        have hsc1 : (1:ℝ) ≤ scale w := one_le_scale w
        have hT0 : (scale w)^N0 ≤ (scale w)^(N0+N1+N2) :=
          Real.rpow_le_rpow_of_exponent_le hsc1 (by linarith)
        have hT1 : (scale w)^N1 ≤ (scale w)^(N0+N1+N2) :=
          Real.rpow_le_rpow_of_exponent_le hsc1 (by linarith)
        have hT2 : (scale w)^N2 ≤ (scale w)^(N0+N1+N2) :=
          Real.rpow_le_rpow_of_exponent_le hsc1 (by linarith)
        have hnn : (0:ℝ) ≤ (scale w)^(N0+N1+N2) := Real.rpow_nonneg (le_of_lt (scale_pos w)) _
        calc 2 * (C0 * (scale w)^N0) + C1 * (scale w)^N1 + C2 * (scale w)^N2
            ≤ 2 * (C0 * (scale w)^(N0+N1+N2)) + C1 * (scale w)^(N0+N1+N2)
              + C2 * (scale w)^(N0+N1+N2) := by
              gcongr
          _ = (2*C0 + C1 + C2) * (scale w)^(N0 + N1 + N2) := by ring

end Work.Asymptotics.Tile
