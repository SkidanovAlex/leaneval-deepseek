import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Submission.Work.FTS.StrongEps.E5Aux2.MuHGlue
import Submission.Work.FTS.StrongEps.E5Aux2.PTgadgets
import Submission.Work.FTS.StrongEps.E5Aux2.AbsL12densLe
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.FTS.EllipticEst.alphaDzW_Hk_le
import Submission.Work.FTS.LocData.SmoothQuad_Fstar
import Submission.Work.FTS.OpenPkg.Basic
import Submission.Work.FTS_RegExport.RXR5L.L12fAux.L12f_C1Jet_hsupp_unsat
import Submission.Work.FTS.StrongEps.E5Aux2.PT.Fstar_quad_bounds
import Submission.Work.FTS.StrongEps.E5Aux2.PT.L12dens_hasDerivAt_of_strip

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.E5Aux2.PT

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

set_option maxHeartbeats 1600000

/-!
# The `x`-derivative of `L₁₂dens (F_* + w)` and its two growth bounds

`L₁₂dens f x = ∫_θ K(θ) f(x,θ)/x dθ` is the angular density of Elgindi's `L₁₂`.  For the
modulated profile `f = F_* + w` of the construction, with `w` smooth on the open quadrant
and bounded by `C₁` (`D_z w` bounded by `C₂`), the three classical facts hold:

* the derivative at every `x > 0` is the integral of the derivative of the integrand,
  `∂_x L₁₂dens f (x) = ∫_θ (K θ ∂_z f(x,θ)/x − K θ f(x,θ)/x²)`
  (`PT.L12dens_hasDerivAt_of_strip`, with the strip bounds produced below from the
  uniform bounds on `F_*` (`PT.Fstar_quad_bounds`) and on `w`);
* `|∂_x L₁₂dens f| ≤ C (1 + 1/x²)`;
* `|L₁₂dens f| ≤ C (1 + 1/x)`
  (`E5Aux2.AbsL12densLe` with the majorant `(3/2)·sup|f|·cos θ`).

The proof is short because the two hard ingredients are separate lemmas: the generic
differentiation under the angular integral (`PT.L12dens_hasDerivAt_of_strip`) and the sharp
bounds for the reference profile (`PT.Fstar_quad_bounds`).  The only thing that has to be
supplied here is the arithmetic: on the strip `(x/2, 2x)` the datum `F_* + w` and its
`z`-derivative are bounded by the single constant `(α/c + C₁) + (2α/c + 2C₂/x)`, and the
resulting integral bound is reorganised with `1/x ≤ 1 + 1/x²`, `1/x² ≤ 1 + 1/x²`.

Everything rests on `[propext, Classical.choice, Quot.sound]`.
-/

/-! ## Elementary helper lemmas -/

/-- `K θ ≤ (3/2) cos θ` on `Iθ`. -/
private lemma K_le_three_halves_cos {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) :
    Work.Spaces.K θ ≤ (3 / 2) * Real.cos θ := by
  have hcos : 0 ≤ Real.cos θ :=
    Real.cos_nonneg_of_mem_Icc ⟨by linarith [hθ.1, Real.pi_pos],
      by linarith [hθ.2, Real.pi_pos]⟩
  have h1 : Work.Spaces.K θ = (3 / 2) * Real.cos θ * Real.sin (2 * θ) := by
    rw [Work.Spaces.K, Real.sin_two_mul]; ring
  rw [h1]
  have h2 : (3 / 2) * Real.cos θ * Real.sin (2 * θ) ≤ (3 / 2) * Real.cos θ * 1 :=
    mul_le_mul_of_nonneg_left (Real.sin_le_one _) (by linarith)
  linarith

/-- `|K θ| ≤ 3` for every real `θ`. -/
private lemma abs_K_le_three (θ : ℝ) : |Work.Spaces.K θ| ≤ 3 := by
  have h1 : |Real.sin θ| ≤ 1 := Real.abs_sin_le_one θ
  have h2 : Real.cos θ ^ 2 ≤ 1 := by
    have := Real.abs_cos_le_one θ
    nlinarith [abs_nonneg (Real.cos θ), sq_abs (Real.cos θ)]
  have h4 : |Real.sin θ| * Real.cos θ ^ 2 ≤ 1 := by
    calc |Real.sin θ| * Real.cos θ ^ 2 ≤ 1 * 1 :=
          mul_le_mul h1 h2 (sq_nonneg _) (by norm_num)
      _ = 1 := by norm_num
  have hK : |Work.Spaces.K θ| = 3 * |Real.sin θ| * Real.cos θ ^ 2 := by
    rw [Work.Spaces.K, abs_mul, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 3),
      abs_of_nonneg (sq_nonneg (Real.cos θ))]
  rw [hK]
  calc 3 * |Real.sin θ| * Real.cos θ ^ 2 = 3 * (|Real.sin θ| * Real.cos θ ^ 2) := by ring
    _ ≤ 3 * 1 := mul_le_mul_of_nonneg_left h4 (by norm_num)
    _ = 3 := by norm_num

/-- `1/x ≤ 1 + 1/x²` for `x > 0`. -/
private lemma inv_le_one_add_inv_sq {x : ℝ} (hx : 0 < x) : 1 / x ≤ 1 + 1 / x ^ 2 := by
  rcases le_or_gt 1 x with h | h
  · have h2 : 1 / x ≤ 1 := by
      rw [div_le_one hx]; linarith
    nlinarith [one_div_pos.mpr (pow_pos hx 2)]
  · have h2 : 1 / x ≤ 1 / x ^ 2 := by
      have hle : x ^ 2 ≤ x := by nlinarith
      exact one_div_le_one_div_of_le (by positivity) hle
    nlinarith [one_div_pos.mpr (pow_pos hx 2)]

/-- `1/x² ≤ 1 + 1/x²`. -/
private lemma inv_sq_le_one_add_inv_sq {x : ℝ} (hx : 0 < x) : 1 / x ^ 2 ≤ 1 + 1 / x ^ 2 := by
  nlinarith [one_div_pos.mpr (pow_pos hx 2)]

/-! ## The main theorem -/

theorem L12densFstar_deriv {α C₁ C₂ : ℝ} (hα : 0 < α) {w : ℝ → ℝ → ℝ}
    (hsm : Work.FTS.EllipticEst.SmoothOpen w)
    (hbd0 : ∀ z θ : ℝ, (z, θ) ∈ Work.Construction.Qd → |w z θ| ≤ C₁)
    (hbd1 : ∀ z θ : ℝ, (z, θ) ∈ Work.Construction.Qd → |Work.Spaces.Dz w z θ| ≤ C₂) :
    (∀ x ∈ Set.Ioi (0 : ℝ), HasDerivAt
        (fun x => Work.Construction.L12dens
          (fun z θ => Work.Construction.Fstar α z θ + w z θ) x)
        (∫ θ in Work.Spaces.Iθ, (Work.Spaces.K θ * Work.Spaces.pz
              (fun z θ => Work.Construction.Fstar α z θ + w z θ) x θ / x
            - Work.Spaces.K θ * (Work.Construction.Fstar α x θ + w x θ) / x ^ 2)) x) ∧
    (∃ C : ℝ, 0 < C ∧ ∀ x ∈ Set.Ioi (0 : ℝ),
        |deriv (fun x => Work.Construction.L12dens
          (fun z θ => Work.Construction.Fstar α z θ + w z θ) x) x| ≤ C * (1 + 1 / x ^ 2)) ∧
    (∃ C : ℝ, 0 < C ∧ ∀ x ∈ Set.Ioi (0 : ℝ),
        |Work.Construction.L12dens
          (fun z θ => Work.Construction.Fstar α z θ + w z θ) x| ≤ C * (1 + 1 / x)) := by
  -- the two ingredients: the bounds for `F_*` and the generic derivative formula
  obtain ⟨_, hFb0, hFb1⟩ := Fstar_quad_bounds hα
  have hcpos : 0 < Work.Spaces.c α := Work.FTS_RegExport.RXR5L.L12fAux.c_pos hα
  have hFso : Work.FTS.EllipticEst.SmoothOpen (Work.Construction.Fstar α) :=
    Work.FTS.EllipticEst.smoothOpen_of_smoothQuad (Work.FTS.LocData.SmoothQuad_Fstar α)
  -- the datum `f = F_* + w`
  set f : ℝ → ℝ → ℝ := fun z θ => Work.Construction.Fstar α z θ + w z θ with hf
  have hfso : Work.FTS.EllipticEst.SmoothOpen f := by
    rw [hf]; exact Work.FTS.EllipticEst.SmoothOpen.add hFso hsm
  have hf2 : ContDiffOn ℝ 2 (Function.uncurry f) Work.FTS.EllipticEst.Q0 := hfso.forall 2
  -- the constants of the statement, and the two (positive) safe reals
  set K0 : ℝ := α / Work.Spaces.c α with hK0
  set K1 : ℝ := 2 * α / Work.Spaces.c α with hK1
  set E₁ : ℝ := max C₁ 0 with hE₁
  set E₂ : ℝ := max C₂ 0 with hE₂
  have hE₁0 : 0 ≤ E₁ := by rw [hE₁]; exact le_max_right _ _
  have hE₂0 : 0 ≤ E₂ := by rw [hE₂]; exact le_max_right _ _
  have hC₁E : C₁ ≤ E₁ := by rw [hE₁]; exact le_max_left _ _
  have hC₂E : C₂ ≤ E₂ := by rw [hE₂]; exact le_max_left _ _
  have hK00 : 0 ≤ K0 := by rw [hK0]; exact div_nonneg hα.le hcpos.le
  have hK10 : 0 ≤ K1 := by rw [hK1]; exact div_nonneg (by linarith) hcpos.le
  have hFb0' : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < π / 2 →
      |Work.Construction.Fstar α z θ| ≤ K0 := by
    intro z θ hz h1 h2; rw [hK0]; exact hFb0 z θ hz h1 h2
  have hFb1' : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < π / 2 →
      |Work.Spaces.pz (Work.Construction.Fstar α) z θ| ≤ K1 := by
    intro z θ hz h1 h2; rw [hK1]; exact hFb1 z θ hz h1 h2
  have hQd : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < π / 2 → (z, θ) ∈ Work.Construction.Qd := by
    intro z θ hz h1 h2
    simp only [Work.Construction.Qd, Set.mem_prod, Set.mem_Ioi, Set.mem_Ioo]
    exact ⟨hz, h1, h2⟩
  -- pointwise bounds for `w`, hence for `f`
  have hw0 : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < π / 2 → |w z θ| ≤ E₁ := by
    intro z θ hz h1 h2
    exact le_trans (hbd0 z θ (hQd z θ hz h1 h2)) hC₁E
  have hw1 : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < π / 2 → |Work.Spaces.pz w z θ| ≤ E₂ / z := by
    intro z θ hz h1 h2
    have hpz : Work.Spaces.pz w z θ = Work.Spaces.Dz w z θ / z := by
      show Work.Spaces.pz w z θ = z * Work.Spaces.pz w z θ / z
      rw [mul_div_cancel_left₀ _ (ne_of_gt hz)]
    rw [hpz, abs_div, abs_of_pos hz]
    exact div_le_div_of_nonneg_right (le_trans (hbd1 z θ (hQd z θ hz h1 h2)) hC₂E) hz.le
  have hf0 : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < π / 2 → |f z θ| ≤ K0 + E₁ := by
    intro z θ hz h1 h2
    calc |f z θ| = |Work.Construction.Fstar α z θ + w z θ| := by rw [hf]
      _ ≤ |Work.Construction.Fstar α z θ| + |w z θ| := abs_add_le _ _
      _ ≤ K0 + E₁ := add_le_add (hFb0' z θ hz h1 h2) (hw0 z θ hz h1 h2)
  have hf1 : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < π / 2 →
      |Work.Spaces.pz f z θ| ≤ K1 + E₂ / z := by
    intro z θ hz h1 h2
    have hpz : Work.Spaces.pz f z θ = Work.Spaces.pz (Work.Construction.Fstar α) z θ
        + Work.Spaces.pz w z θ := by
      rw [hf]; exact Work.FTS.EllipticEst.pz_add hFso hsm hz h1 h2
    rw [hpz]
    exact le_trans (abs_add_le _ _) (add_le_add (hFb1' z θ hz h1 h2) (hw1 z θ hz h1 h2))
  -- **conjunct 1**: the derivative formula at every `x > 0`
  have hderiv : ∀ x ∈ Set.Ioi (0 : ℝ), HasDerivAt (fun x => Work.Construction.L12dens f x)
      (∫ θ in Work.Spaces.Iθ, (Work.Spaces.K θ * Work.Spaces.pz f x θ / x
        - Work.Spaces.K θ * f x θ / x ^ 2)) x := by
    intro x hx
    have hx0 : 0 < x := hx
    have h2E : 0 ≤ 2 * E₂ / x := div_nonneg (mul_nonneg (by norm_num) hE₂0) hx0.le
    refine L12dens_hasDerivAt_of_strip (f := f) hx0
      (C := (K0 + E₁) + (K1 + 2 * E₂ / x)) ?_ hf2 ?_ ?_
    · linarith
    · intro y hy θ hθ
      have hy0 : 0 < y := by linarith [hy.1, hx0]
      have h := hf0 y θ hy0 hθ.1 hθ.2
      have hK1E : 0 ≤ K1 + 2 * E₂ / x := by linarith
      linarith
    · intro y hy θ hθ
      have hy0 : 0 < y := by linarith [hy.1, hx0]
      have h := hf1 y θ hy0 hθ.1 hθ.2
      have hyx : x / 2 ≤ y := hy.1.le
      have hinv : 1 / y ≤ 2 / x := by
        have h1 : 1 / y ≤ 1 / (x / 2) := one_div_le_one_div_of_le (by linarith) hyx
        have h2 : 1 / (x / 2) = 2 / x := by field_simp
        linarith [h2]
      have hEE : E₂ / y ≤ 2 * E₂ / x := by
        calc E₂ / y = E₂ * (1 / y) := by ring
          _ ≤ E₂ * (2 / x) := mul_le_mul_of_nonneg_left hinv hE₂0
          _ = 2 * E₂ / x := by ring
      have hK1E : 0 ≤ K1 + 2 * E₂ / x := by linarith
      linarith
  -- **conjunct 2**: the bound on the derivative
  have hderiv_bound : ∃ C : ℝ, 0 < C ∧ ∀ x ∈ Set.Ioi (0 : ℝ),
      |deriv (fun x => Work.Construction.L12dens f x) x| ≤ C * (1 + 1 / x ^ 2) := by
    refine ⟨Real.pi / 2 * (|3 * K1| + |3 * E₂ + 3 * (K0 + E₁)|) + 1, ?_, ?_⟩
    · nlinarith [Real.pi_pos, abs_nonneg (3 * K1), abs_nonneg (3 * E₂ + 3 * (K0 + E₁))]
    · intro x hx
      have hx0 : 0 < x := hx
      rw [(hderiv x hx).deriv]
      have hvol : (MeasureTheory.volume.restrict Work.Spaces.Iθ).real Set.univ = Real.pi / 2 := by
        rw [MeasureTheory.Measure.real_def, Measure.restrict_apply_univ, Work.Spaces.Iθ,
          Real.volume_Icc]
        rw [ENNReal.toReal_ofReal (by linarith [Real.pi_pos])]
        ring
      -- the pointwise bound on the integrand
      have hbd : ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ),
          ‖Work.Spaces.K θ * Work.Spaces.pz f x θ / x
            - Work.Spaces.K θ * f x θ / x ^ 2‖
          ≤ 3 * (K1 + E₂ / x) / x + 3 * (K0 + E₁) / x ^ 2 := by
        rw [Work.FTS_RegExport.RXT.Slots.restrict_Iθ_eq_restrict_Ioo]
        refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioo (fun θ hθ => ?_)
        rw [Real.norm_eq_abs]
        have hK3 : |Work.Spaces.K θ| ≤ 3 := abs_K_le_three θ
        have hpz : |Work.Spaces.pz f x θ| ≤ K1 + E₂ / x := hf1 x θ hx0 hθ.1 hθ.2
        have hfM : |f x θ| ≤ K0 + E₁ := hf0 x θ hx0 hθ.1 hθ.2
        have h1 : |Work.Spaces.K θ * Work.Spaces.pz f x θ / x|
            ≤ 3 * (K1 + E₂ / x) / x := by
          have := mul_le_mul hK3 hpz (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 3)
          rw [abs_div, abs_mul, abs_of_pos hx0]
          exact div_le_div_of_nonneg_right this hx0.le
        have h2 : |Work.Spaces.K θ * f x θ / x ^ 2| ≤ 3 * (K0 + E₁) / x ^ 2 := by
          have := mul_le_mul hK3 hfM (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 3)
          rw [abs_div, abs_mul, abs_of_pos (pow_pos hx0 2)]
          exact div_le_div_of_nonneg_right this (by positivity)
        calc |Work.Spaces.K θ * Work.Spaces.pz f x θ / x
              - Work.Spaces.K θ * f x θ / x ^ 2|
            ≤ |Work.Spaces.K θ * Work.Spaces.pz f x θ / x|
              + |Work.Spaces.K θ * f x θ / x ^ 2| := abs_sub _ _
          _ ≤ 3 * (K1 + E₂ / x) / x + 3 * (K0 + E₁) / x ^ 2 := add_le_add h1 h2
      have hInt := MeasureTheory.norm_integral_le_of_norm_le_const
        (μ := MeasureTheory.volume.restrict Work.Spaces.Iθ) hbd
      rw [hvol] at hInt
      rw [Real.norm_eq_abs] at hInt
      have hR : 3 * (K1 + E₂ / x) / x + 3 * (K0 + E₁) / x ^ 2
          = 3 * K1 / x + (3 * E₂ + 3 * (K0 + E₁)) / x ^ 2 := by
        field_simp
        ring
      have hstep : 3 * K1 / x + (3 * E₂ + 3 * (K0 + E₁)) / x ^ 2
          ≤ (|3 * K1| + |3 * E₂ + 3 * (K0 + E₁)|) * (1 + 1 / x ^ 2) := by
        have h3 : 1 / x ≤ 1 + 1 / x ^ 2 := inv_le_one_add_inv_sq hx0
        have h4 : 1 / x ^ 2 ≤ 1 + 1 / x ^ 2 := inv_sq_le_one_add_inv_sq hx0
        have hA : 3 * K1 / x ≤ |3 * K1| * (1 + 1 / x ^ 2) := by
          calc 3 * K1 / x = 3 * K1 * (1 / x) := by ring
            _ ≤ |3 * K1| * (1 / x) := mul_le_mul_of_nonneg_right (le_abs_self _) (by positivity)
            _ ≤ |3 * K1| * (1 + 1 / x ^ 2) := mul_le_mul_of_nonneg_left h3 (abs_nonneg _)
        have hB : (3 * E₂ + 3 * (K0 + E₁)) / x ^ 2
            ≤ |3 * E₂ + 3 * (K0 + E₁)| * (1 + 1 / x ^ 2) := by
          calc (3 * E₂ + 3 * (K0 + E₁)) / x ^ 2
              = (3 * E₂ + 3 * (K0 + E₁)) * (1 / x ^ 2) := by ring
            _ ≤ |3 * E₂ + 3 * (K0 + E₁)| * (1 / x ^ 2) :=
                mul_le_mul_of_nonneg_right (le_abs_self _) (by positivity)
            _ ≤ |3 * E₂ + 3 * (K0 + E₁)| * (1 + 1 / x ^ 2) :=
                mul_le_mul_of_nonneg_left h4 (abs_nonneg _)
        linarith
      calc |∫ θ in Work.Spaces.Iθ, (Work.Spaces.K θ * Work.Spaces.pz f x θ / x
              - Work.Spaces.K θ * f x θ / x ^ 2)|
          ≤ (3 * (K1 + E₂ / x) / x + 3 * (K0 + E₁) / x ^ 2) * (Real.pi / 2) := hInt
        _ = Real.pi / 2 * (3 * K1 / x + (3 * E₂ + 3 * (K0 + E₁)) / x ^ 2) := by
            rw [hR]; ring
        _ ≤ Real.pi / 2 * ((|3 * K1| + |3 * E₂ + 3 * (K0 + E₁)|) * (1 + 1 / x ^ 2)) :=
            mul_le_mul_of_nonneg_left hstep (by positivity)
        _ ≤ (Real.pi / 2 * (|3 * K1| + |3 * E₂ + 3 * (K0 + E₁)|) + 1) * (1 + 1 / x ^ 2) := by
            have h5 : (0 : ℝ) ≤ 1 + 1 / x ^ 2 := by positivity
            have h6 : Real.pi / 2 * (|3 * K1| + |3 * E₂ + 3 * (K0 + E₁)|)
                ≤ Real.pi / 2 * (|3 * K1| + |3 * E₂ + 3 * (K0 + E₁)|) + 1 := by linarith
            have h7 := mul_le_mul_of_nonneg_right h6 h5
            linarith [h7]
  -- **conjunct 3**: the bound on the density
  have hdens_bound : ∃ C : ℝ, 0 < C ∧ ∀ x ∈ Set.Ioi (0 : ℝ),
      |Work.Construction.L12dens f x| ≤ C * (1 + 1 / x) := by
    have hM0 : 0 ≤ (3 / 2) * (K0 + E₁) := by
      have : 0 ≤ K0 + E₁ := by linarith
      positivity
    refine ⟨(3 / 2) * (K0 + E₁) + 1, by linarith, ?_⟩
    intro x hx
    have hx0 : 0 < x := hx
    have hkey : |Work.Construction.L12dens f x| ≤ (3 / 2) * (K0 + E₁) / x := by
      refine Work.FTS.StrongEps.E5Aux2.AbsL12densLe hx0 hM0 (fun θ hθ => ?_)
      rcases eq_or_lt_of_le hθ.1 with h0 | hθ1
      · have hK0' : Work.Spaces.K 0 = 0 := by simp [Work.Spaces.K]
        rw [← h0, hK0', zero_mul]
        simpa using hM0
      · rcases eq_or_lt_of_le hθ.2 with hπ | hθ2
        · have hKπ : Work.Spaces.K (Real.pi / 2) = 0 := by
            rw [Work.Spaces.K, Real.cos_pi_div_two]; ring
          rw [hπ, hKπ, Real.cos_pi_div_two, zero_mul, mul_zero]
        · have hfM : |f x θ| ≤ K0 + E₁ := hf0 x θ hx0 hθ1 hθ2
          have hK3 : Work.Spaces.K θ ≤ (3 / 2) * Real.cos θ := K_le_three_halves_cos hθ
          have hK0' : 0 ≤ Work.Spaces.K θ := K_nonneg_of_mem_Iθ hθ
          have hsum : 0 ≤ K0 + E₁ := by linarith
          calc Work.Spaces.K θ * |f x θ| ≤ Work.Spaces.K θ * (K0 + E₁) :=
                mul_le_mul_of_nonneg_left hfM hK0'
            _ ≤ (3 / 2) * Real.cos θ * (K0 + E₁) := mul_le_mul_of_nonneg_right hK3 hsum
            _ = (3 / 2) * (K0 + E₁) * Real.cos θ := by ring
    have hfin : (3 / 2) * (K0 + E₁) / x ≤ ((3 / 2) * (K0 + E₁) + 1) * (1 + 1 / x) := by
      have h3 : 1 / x ≤ 1 + 1 / x := by linarith [one_div_pos.mpr hx0]
      calc (3 / 2) * (K0 + E₁) / x = (3 / 2) * (K0 + E₁) * (1 / x) := by ring
        _ ≤ (3 / 2) * (K0 + E₁) * (1 + 1 / x) := mul_le_mul_of_nonneg_left h3 hM0
        _ ≤ ((3 / 2) * (K0 + E₁) + 1) * (1 + 1 / x) :=
            mul_le_mul_of_nonneg_right (by linarith) (by positivity)
    linarith
  have hmain : (∀ x ∈ Set.Ioi (0 : ℝ), HasDerivAt (fun x => Work.Construction.L12dens f x)
        (∫ θ in Work.Spaces.Iθ, (Work.Spaces.K θ * Work.Spaces.pz f x θ / x
          - Work.Spaces.K θ * f x θ / x ^ 2)) x) ∧
      (∃ C : ℝ, 0 < C ∧ ∀ x ∈ Set.Ioi (0 : ℝ),
        |deriv (fun x => Work.Construction.L12dens f x) x| ≤ C * (1 + 1 / x ^ 2)) ∧
      (∃ C : ℝ, 0 < C ∧ ∀ x ∈ Set.Ioi (0 : ℝ),
        |Work.Construction.L12dens f x| ≤ C * (1 + 1 / x)) :=
    ⟨hderiv, hderiv_bound, hdens_bound⟩
  rw [hf] at hmain
  exact hmain

end

end Work.FTS.StrongEps.E5Aux2.PT
