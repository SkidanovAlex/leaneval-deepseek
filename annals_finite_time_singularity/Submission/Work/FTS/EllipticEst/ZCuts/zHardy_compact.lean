import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.FDeriv.Measurable
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Order.Group.Lattice
import Mathlib.Order.CompletePartialOrder
import Mathlib.Order.Interval.Basic
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.MinImports
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Mathlib.Topology.GDelta.MetrizableSpace
import Submission.Work.Coercivity.wip_L_self
import Submission.Work.FTS.EllipticEst.OpenFTC.absFtcLeIntegralAbsDeriv
import Submission.Work.FTS.EllipticEst.SliceAux
import Submission.Work.FTS.EllipticEst.integrableOn_HkIntegrand_terms
import Submission.Work.FTS.EllipticEst.remov.slice_gprime_ident
import Submission.Work.FTS.H2.STBasic
import Submission.Work.FTS.H2.STFacts
import Submission.Work.FTS.H2.hard_sq_prod_z
import Submission.Work.FTS.PhiStar.Gegenbauer.eFam_norm_fts
import Submission.Work.FTS.PhiStar.Honesty.rgG2_sq_div_z4_Ioo
import Submission.Work.FTS.PhiStar.Series.Weil.integrableOn_prod_mul
import Submission.Work.FTS_EllLimOK.EGap.integrableOn_PhiD
import Submission.Work.FTS_RegExport.RXT.contDiffOn_two_integral_Itheta
import Submission.Work.H2W.PsiSlices.weakPos2_dilate
import Submission.Work.RPFresh.slice_sq_le
import Submission.Work.Spaces.HProductRule_bad_term
import Submission.Work.Spaces.HkSq_terms
import Submission.Work.Spaces.SmoothCompact_HkMem
import Submission.Work.Spaces.bt_f_bound
import Submission.Work.Spaces.bt_integral_weight_id
import Submission.Work.Spaces.mixed_mul_le
import Submission.Work.Spaces.pz_mixed_mul_le_4
import Submission.Work.Spaces.sin_two_rpow
import Submission.Work.Spaces.sq_mul_div_rpow
import Submission.Work.Spaces.uncurry_partial_c1
import Submission.Work.StabilityFar.Profile.exists_Fstar_add_ge
-- ===== merged: Submission.Work.Blocks.interpol_mixed_box_proof =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.Blocks

set_option autoImplicit false
set_option maxHeartbeats 4000000

/-! ## Elementary one-dimensional tools -/

/-- `√(a+b) ≤ √a + √b` for `a,b ≥ 0`. -/
private theorem sqrt_add_le' {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    Real.sqrt (a + b) ≤ Real.sqrt a + Real.sqrt b := by
  have h1 : (Real.sqrt a + Real.sqrt b) ^ 2 = a + b + 2 * (Real.sqrt a * Real.sqrt b) := by
    rw [add_sq, Real.sq_sqrt ha, Real.sq_sqrt hb]
    ring
  have h2 : 0 ≤ 2 * (Real.sqrt a * Real.sqrt b) := by positivity
  have h3 : a + b ≤ (Real.sqrt a + Real.sqrt b) ^ 2 := by rw [h1]; linarith
  calc Real.sqrt (a + b) ≤ Real.sqrt ((Real.sqrt a + Real.sqrt b) ^ 2) := Real.sqrt_le_sqrt h3
    _ = |Real.sqrt a + Real.sqrt b| := Real.sqrt_sq_eq_abs _
    _ = Real.sqrt a + Real.sqrt b := abs_of_nonneg (by positivity)

/-- Weighted AM–GM: `2√(xy) ≤ c x + y/c` for `x,y ≥ 0`, `c > 0`. -/
private theorem two_sqrt_mul_le {x y c : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) (hc : 0 < c) :
    2 * Real.sqrt (x * y) ≤ c * x + y / c := by
  have hcx : 0 ≤ c * x := mul_nonneg hc.le hx
  have hyc : 0 ≤ y / c := div_nonneg hy hc.le
  have hxy : c * x * (y / c) = x * y := by field_simp
  have h2 : 2 * (Real.sqrt (c * x) * Real.sqrt (y / c)) = 2 * Real.sqrt (x * y) := by
    rw [← Real.sqrt_mul hcx, hxy]
  have := sq_nonneg (Real.sqrt (c * x) - Real.sqrt (y / c))
  rw [sub_sq, Real.sq_sqrt hcx, Real.sq_sqrt hyc] at this
  linarith [this, h2]

/-- AM–GM in the form `2 a √(xy) ≤ a² x + y` for `a,x,y ≥ 0`. -/
private theorem two_mul_sqrt_mul_le {a x y : ℝ} (ha : 0 ≤ a) (hx : 0 ≤ x) (hy : 0 ≤ y) :
    2 * (a * Real.sqrt (x * y)) ≤ a ^ 2 * x + y := by
  have h1 : Real.sqrt (x * y) = Real.sqrt x * Real.sqrt y := Real.sqrt_mul hx y
  rw [h1]
  have := sq_nonneg (a * Real.sqrt x - Real.sqrt y)
  rw [sub_sq, mul_pow, Real.sq_sqrt hx, Real.sq_sqrt hy] at this
  linarith [this]

/-! ## The main theorem -/


/-! ## The requested form -/


end Work.Blocks
end
end
-- ===== merged: Submission.Work.Coercivity.zQuad =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.Coercivity

set_option autoImplicit false

/-- The product of the two restricted measures on the quadrant. -/
def quadMeasure : Measure (ℝ × ℝ) :=
  (volume.restrict Spaces.Iz).prod (volume.restrict Spaces.Iθ)


/-- `IntegrableOn` over the quadrant is integrability with respect to the product of the
two restricted measures. -/
theorem integrableOn_quadrant_iff (F : ℝ × ℝ → ℝ) :
    IntegrableOn F (Spaces.Iz ×ˢ Spaces.Iθ) ↔ Integrable F quadMeasure := by
  rw [quadMeasure, IntegrableOn, Measure.prod_restrict, ← Measure.volume_eq_prod ℝ ℝ]




/-- Additivity of `wip` in its first argument, whenever both integrands are honest. -/
theorem wip_add (ρ A B g : ℝ → ℝ → ℝ)
    (hA : IntegrableOn
      (Function.uncurry (fun z θ => A z θ * g z θ * ρ z θ)) (Spaces.Iz ×ˢ Spaces.Iθ))
    (hB : IntegrableOn
      (Function.uncurry (fun z θ => B z θ * g z θ * ρ z θ)) (Spaces.Iz ×ˢ Spaces.Iθ)) :
    wip ρ (fun z θ => A z θ + B z θ) g = wip ρ A g + wip ρ B g := by
  have hA' : Integrable (fun p : ℝ × ℝ => A p.1 p.2 * g p.1 p.2 * ρ p.1 p.2)
      quadMeasure := (integrableOn_quadrant_iff _).mp hA
  have hB' : Integrable (fun p : ℝ × ℝ => B p.1 p.2 * g p.1 p.2 * ρ p.1 p.2)
      quadMeasure := (integrableOn_quadrant_iff _).mp hB
  have hsum : Integrable (fun p : ℝ × ℝ =>
      (A p.1 p.2 + B p.1 p.2) * g p.1 p.2 * ρ p.1 p.2) quadMeasure := by
    refine (hA'.add hB').congr (Filter.Eventually.of_forall (fun p => ?_))
    simp only [Pi.add_apply]
    ring
  rw [wip_eq_integral_prod ρ (fun z θ => A z θ + B z θ) g
        ((integrableOn_quadrant_iff _).mpr hsum),
      wip_eq_integral_prod ρ A g hA, wip_eq_integral_prod ρ B g hB]
  change (∫ p, (A p.1 p.2 + B p.1 p.2) * g p.1 p.2 * ρ p.1 p.2 ∂quadMeasure)
      = (∫ p, A p.1 p.2 * g p.1 p.2 * ρ p.1 p.2 ∂quadMeasure)
        + (∫ p, B p.1 p.2 * g p.1 p.2 * ρ p.1 p.2 ∂quadMeasure)
  rw [← MeasureTheory.integral_add hA' hB']
  apply integral_congr_ae
  filter_upwards with p
  ring




end Work.Coercivity
end
end
-- ===== merged: Submission.Work.Elliptic.DivSinIterUnif =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.Elliptic

set_option autoImplicit false
set_option maxHeartbeats 4000000

/-! ## 1. Elementary properties of the weight `σ(θ) = sin(2θ)` on `Iθ` -/

/-- `σ = sin(2θ)` is nonnegative on `Iθ = [0, π/2]`. -/
private lemma sin_two_nonneg {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) : 0 ≤ Real.sin (2 * θ) := by
  rw [Work.Spaces.Iθ, Set.mem_Icc] at hθ
  exact Real.sin_nonneg_of_nonneg_of_le_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])

/-- `σ = sin(2θ)` is positive on the open interval `(0, π/2)`. -/
private lemma dsi_sin2_pos {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) : 0 < Real.sin (2 * θ) :=
  Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])

/-- `σ ≤ 1`. -/
private lemma sin_two_le_one (θ : ℝ) : Real.sin (2 * θ) ≤ 1 := Real.sin_le_one _

/-- `σ ^ 2 ≤ 1`. -/
private lemma sin_two_sq_le_one (θ : ℝ) : Real.sin (2 * θ) ^ 2 ≤ 1 := by
  nlinarith [Real.sin_le_one (2 * θ), Real.neg_one_le_sin (2 * θ), sq_nonneg (Real.sin (2 * θ))]

/-- `x ^ 2 / x ^ r = x ^ (2 - r)` for `0 ≤ x` and `r ≠ 2`. -/
private lemma sq_div_rpow {x : ℝ} (hx : 0 ≤ x) (r : ℝ) (hr : r ≠ 2) :
    x ^ 2 / x ^ r = x ^ (2 - r) := by
  rcases eq_or_lt_of_le hx with h | h
  · subst h
    rw [Real.zero_rpow (sub_ne_zero.mpr hr.symm)]
    norm_num
  · rw [Real.rpow_sub h (2 : ℝ) r]
    norm_num

/-- For `0 ≤ x ≤ 1` the map `r ↦ x ^ r` is antitone. -/
private lemma rpow_le_rpow_of_le_one {x a b : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) (ha : 0 < a)
    (hab : a ≤ b) : x ^ b ≤ x ^ a := by
  rcases eq_or_lt_of_le hx0 with h | h
  · subst h
    rw [Real.zero_rpow (ne_of_gt ha), Real.zero_rpow (ne_of_gt (lt_of_lt_of_le ha hab))]
  · exact Real.rpow_le_rpow_of_exponent_ge h hx1 hab

/-- `0 < 2 - γ`. -/
private lemma two_sub_gam_pos {α : ℝ} (hα1 : α ≤ 1) : 0 < 2 - Work.Spaces.gam α := by
  rw [Work.Spaces.gam]; linarith

/-- `0 < γ`. -/
private lemma gam_pos {α : ℝ} (hα : 0 < α) : 0 < Work.Spaces.gam α :=
  lt_trans zero_lt_one (Work.Spaces.one_lt_gam hα)

/-- `σ ^ (2 - γ) ≤ 1` on `Iθ`. -/
private lemma sin_two_rpow_le_one {α θ : ℝ} (hα1 : α ≤ 1) (hθ : θ ∈ Work.Spaces.Iθ) :
    Real.sin (2 * θ) ^ (2 - Work.Spaces.gam α) ≤ 1 :=
  Real.rpow_le_one (sin_two_nonneg hθ) (sin_two_le_one θ) (le_of_lt (two_sub_gam_pos hα1))


/-! ## 2. The two functionals of the statement -/


/-- The right hand side of `DivSinIter`
(`∫ (h')²/sin(2θ)^η + ∑_{m=1}^{i} ∫ (D_θ^m h')² / sin(2θ)^γ`). -/
private def RHS (α : ℝ) (i : ℕ) (h : ℝ → ℝ) : ℝ :=
  (∫ θ in Work.Spaces.Iθ, (deriv h θ) ^ 2 / (Real.sin (2 * θ)) ^ Work.Spaces.eta)
    + ∑ m ∈ Finset.Icc 1 i,
        ∫ θ in Work.Spaces.Iθ,
          (Dth1Iter m (deriv h) θ) ^ 2 / (Real.sin (2 * θ)) ^ (Work.Spaces.gam α)




private lemma Iθ_measurable : MeasurableSet Work.Spaces.Iθ := measurableSet_Icc






/-! ## 4. The iterated `D_θ`-derivatives of `SinQ h` are `O(σ)` -/



/-! ## 5. Algebraic helpers for the induction step -/


/-- `σ ^ 4 * (h/σ)² = h² σ²` (both sides vanish at `σ = 0`). -/
private lemma sin_two_pow4_mul_sinq_sq (h : ℝ → ℝ) (θ : ℝ) :
    (Real.sin (2 * θ)) ^ 4 * (SinQ h θ) ^ 2 = (h θ) ^ 2 * (Real.sin (2 * θ)) ^ 2 := by
  by_cases hs : Real.sin (2 * θ) = 0
  · simp [hs, SinQ]
  · rw [SinQ, div_pow]
    field_simp



/-! ## 6. The pointwise bound of the induction step -/

private lemma step_pointwise (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) (M : ℝ) (hM : 0 < M)
    (hM0 : ∀ θ : ℝ, |2 * Real.cos (2 * θ)| ≤ M)
    (hMk : ∀ k ∈ Finset.Icc 1 3, ∀ θ : ℝ,
        |Dth1Iter k (fun t : ℝ => 2 * Real.cos (2 * t)) θ| ≤ M * (Real.sin (2 * θ)) ^ 2)
    (n : ℕ) (hn2 : 2 ≤ n) (hn4 : n ≤ 4) (h : ℝ → ℝ) (hsm : SmoothSlice h)
    (h0 : h 0 = 0) (hp : h (Real.pi / 2) = 0) :
    ∀ θ ∈ Work.Spaces.Iθ,
      (Dth1Iter n (SinQ h) θ) ^ 2 / (Real.sin (2 * θ)) ^ (Work.Spaces.gam α)
        ≤ 2 * ((Dth1Iter (n - 1) (deriv h) θ) ^ 2 / (Real.sin (2 * θ)) ^ (Work.Spaces.gam α))
          + 2 * (n : ℝ) * M ^ 2 * ((h θ) ^ 2 * (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α))
          + 2 * (n : ℝ) * ∑ k ∈ Finset.Icc 1 (n - 1),
              ((Nat.choose (n - 1) k : ℝ) * M) ^ 2
                * ((Dth1Iter k (SinQ h) θ) ^ 2 / (Real.sin (2 * θ)) ^ (Work.Spaces.gam α)) := by
  have hgam2 : Work.Spaces.gam α ≠ 2 := by have := two_sub_gam_pos hα1; linarith
  have hphi : ∀ j ∈ Finset.Icc 0 3, ∀ θ : ℝ,
      |Dth1Iter j (fun t : ℝ => 2 * Real.cos (2 * t)) θ| ≤ M := by
    intro j hj θ
    rcases eq_or_lt_of_le (Finset.mem_Icc.mp hj).1 with h0j | h1j
    · rw [← h0j]
      simp only [Dth1Iter_zero]
      exact hM0 θ
    · have hmem : j ∈ Finset.Icc 1 3 := Finset.mem_Icc.mpr ⟨h1j, (Finset.mem_Icc.mp hj).2⟩
      have hh := hMk j hmem θ
      have hσ2 : (Real.sin (2 * θ)) ^ 2 ≤ 1 := sin_two_sq_le_one θ
      have hMnn : 0 ≤ M := hM.le
      have habs : 0 ≤ |Dth1Iter j (fun t : ℝ => 2 * Real.cos (2 * t)) θ| := abs_nonneg _
      nlinarith [hh, hσ2, hMnn, habs]
  intro θ hθ
  by_cases hσ0 : Real.sin (2 * θ) = 0
  · have hz : (Real.sin (2 * θ)) ^ (Work.Spaces.gam α) = 0 := by
      rw [hσ0, Real.zero_rpow (ne_of_gt (gam_pos hα))]
    have hz2 : (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α) = 0 := by
      rw [hσ0, Real.zero_rpow (ne_of_gt (two_sub_gam_pos hα1))]
    rw [hz, hz2]
    simp only [div_zero, mul_zero, Finset.sum_const_zero, add_zero]
    norm_num
  · have hθ' : θ ∈ Set.Ioo 0 (Real.pi / 2) := by
      refine ⟨?_, ?_⟩
      · rcases eq_or_lt_of_le hθ.1 with hh | hh
        · exfalso
          apply hσ0
          rw [← hh]
          show Real.sin (2 * 0) = 0
          rw [mul_zero, Real.sin_zero]
        · exact hh
      · rcases eq_or_lt_of_le hθ.2 with hh | hh
        · exfalso
          apply hσ0
          rw [hh]
          show Real.sin (2 * (Real.pi / 2)) = 0
          rw [show (2:ℝ) * (Real.pi / 2) = Real.pi by ring, Real.sin_pi]
        · exact hh
    have hσp : 0 < Real.sin (2 * θ) := dsi_sin2_pos hθ'
    have hσnn : 0 ≤ Real.sin (2 * θ) := hσp.le
    have hrec := DivSinRec n h (by omega) hsm h0 hp θ hθ'
    set sg : ℝ := (Real.sin (2 * θ)) ^ (Work.Spaces.gam α) with hsg
    set sg2 : ℝ := (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α) with hsg2
    set f : ℕ → ℝ := fun k => (Nat.choose (n - 1) k : ℝ)
        * Dth1Iter (n - 1 - k) (fun t : ℝ => 2 * Real.cos (2 * t)) θ
        * Dth1Iter k (SinQ h) θ with hf
    set S : ℝ := ∑ k ∈ Finset.range n, f k with hS
    have hsg_nn : 0 ≤ sg := by rw [hsg]; exact Real.rpow_nonneg hσnn _
    have hrec' : Dth1Iter n (SinQ h) θ = Dth1Iter (n - 1) (deriv h) θ - S := by
      rw [hS, hf]
      exact hrec
    have hsq : (Dth1Iter n (SinQ h) θ) ^ 2
        ≤ 2 * (Dth1Iter (n - 1) (deriv h) θ) ^ 2 + 2 * S ^ 2 := by
      rw [hrec']
      nlinarith [sq_nonneg (Dth1Iter (n - 1) (deriv h) θ + S)]
    have hcs : S ^ 2 ≤ (n : ℝ) * ∑ k ∈ Finset.range n, (f k) ^ 2 := by
      rw [hS]
      have h := Finset.sum_mul_sq_le_sq_mul_sq (Finset.range n) (fun k => f k) (fun _ => (1 : ℝ))
      simp only [mul_one, one_pow] at h
      have hcard : (∑ _k ∈ Finset.range n, (1 : ℝ)) = (n : ℝ) := by
        simp [Finset.sum_const, Finset.card_range]
      rw [hcard] at h
      simpa only [mul_comm] using h
    have hstep1 : (Dth1Iter n (SinQ h) θ) ^ 2 / sg
        ≤ 2 * ((Dth1Iter (n - 1) (deriv h) θ) ^ 2 / sg)
          + 2 * (n : ℝ) * (∑ k ∈ Finset.range n, (f k) ^ 2 / sg) := by
      have h1 : (Dth1Iter n (SinQ h) θ) ^ 2 / sg
          ≤ (2 * (Dth1Iter (n - 1) (deriv h) θ) ^ 2 + 2 * S ^ 2) / sg :=
        div_le_div_of_nonneg_right hsq hsg_nn
      have h2 : (2 * (Dth1Iter (n - 1) (deriv h) θ) ^ 2 + 2 * S ^ 2) / sg
          = 2 * ((Dth1Iter (n - 1) (deriv h) θ) ^ 2 / sg) + 2 * (S ^ 2 / sg) := by ring
      have h3 : S ^ 2 / sg ≤ (n : ℝ) * (∑ k ∈ Finset.range n, (f k) ^ 2 / sg) := by
        have h4 : S ^ 2 / sg ≤ ((n : ℝ) * ∑ k ∈ Finset.range n, (f k) ^ 2) / sg :=
          div_le_div_of_nonneg_right hcs hsg_nn
        rw [mul_div_assoc, Finset.sum_div] at h4
        exact h4
      calc (Dth1Iter n (SinQ h) θ) ^ 2 / sg
          ≤ (2 * (Dth1Iter (n - 1) (deriv h) θ) ^ 2 + 2 * S ^ 2) / sg := h1
        _ = 2 * ((Dth1Iter (n - 1) (deriv h) θ) ^ 2 / sg) + 2 * (S ^ 2 / sg) := h2
        _ ≤ 2 * ((Dth1Iter (n - 1) (deriv h) θ) ^ 2 / sg)
            + 2 * ((n : ℝ) * (∑ k ∈ Finset.range n, (f k) ^ 2 / sg)) := by linarith [h3]
        _ = 2 * ((Dth1Iter (n - 1) (deriv h) θ) ^ 2 / sg)
            + 2 * (n : ℝ) * (∑ k ∈ Finset.range n, (f k) ^ 2 / sg) := by ring
    have hsplit : (∑ k ∈ Finset.range n, (f k) ^ 2 / sg)
        = (∑ k ∈ Finset.range (n - 1), (f (k + 1)) ^ 2 / sg) + (f 0) ^ 2 / sg := by
      have hn : n = (n - 1) + 1 := by omega
      conv_lhs => rw [hn]
      rw [Finset.sum_range_succ']
    have hterm0 : (f 0) ^ 2 / sg ≤ M ^ 2 * ((h θ) ^ 2 * sg2) := by
      have hch : (Nat.choose (n - 1) 0 : ℝ) = 1 := by simp
      have hφ : |Dth1Iter (n - 1) (fun t : ℝ => 2 * Real.cos (2 * t)) θ|
          ≤ M * (Real.sin (2 * θ)) ^ 2 :=
        hMk (n - 1) (Finset.mem_Icc.mpr ⟨by omega, by omega⟩) θ
      have hφ2 : (Dth1Iter (n - 1) (fun t : ℝ => 2 * Real.cos (2 * t)) θ) ^ 2
          ≤ M ^ 2 * (Real.sin (2 * θ)) ^ 4 := by
        have hsq2 : (M * (Real.sin (2 * θ)) ^ 2) ^ 2 = M ^ 2 * (Real.sin (2 * θ)) ^ 4 := by ring
        calc (Dth1Iter (n - 1) (fun t : ℝ => 2 * Real.cos (2 * t)) θ) ^ 2
            = |Dth1Iter (n - 1) (fun t : ℝ => 2 * Real.cos (2 * t)) θ| ^ 2 := (sq_abs _).symm
          _ ≤ (M * (Real.sin (2 * θ)) ^ 2) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) hφ 2
          _ = M ^ 2 * (Real.sin (2 * θ)) ^ 4 := hsq2
      have hmul : (Dth1Iter (n - 1) (fun t : ℝ => 2 * Real.cos (2 * t)) θ) ^ 2
            * (SinQ h θ) ^ 2
          ≤ M ^ 2 * ((h θ) ^ 2 * (Real.sin (2 * θ)) ^ 2) := by
        calc (Dth1Iter (n - 1) (fun t : ℝ => 2 * Real.cos (2 * t)) θ) ^ 2 * (SinQ h θ) ^ 2
            ≤ (M ^ 2 * (Real.sin (2 * θ)) ^ 4) * (SinQ h θ) ^ 2 :=
              mul_le_mul_of_nonneg_right hφ2 (sq_nonneg _)
          _ = M ^ 2 * ((Real.sin (2 * θ)) ^ 4 * (SinQ h θ) ^ 2) := by ring
          _ = M ^ 2 * ((h θ) ^ 2 * (Real.sin (2 * θ)) ^ 2) := by rw [sin_two_pow4_mul_sinq_sq]
      have heq1 : (Dth1Iter (n - 1) (fun t : ℝ => 2 * Real.cos (2 * t)) θ * SinQ h θ) ^ 2
          = (Dth1Iter (n - 1) (fun t : ℝ => 2 * Real.cos (2 * t)) θ) ^ 2 * (SinQ h θ) ^ 2 :=
        mul_pow _ _ 2
      have hdiv : (Dth1Iter (n - 1) (fun t : ℝ => 2 * Real.cos (2 * t)) θ * SinQ h θ) ^ 2 / sg
          ≤ M ^ 2 * ((h θ) ^ 2 * (Real.sin (2 * θ)) ^ 2) / sg := by
        rw [heq1]
        exact div_le_div_of_nonneg_right hmul hsg_nn
      have heq2 : M ^ 2 * ((h θ) ^ 2 * (Real.sin (2 * θ)) ^ 2) / sg
          = M ^ 2 * ((h θ) ^ 2 * ((Real.sin (2 * θ)) ^ 2 / sg)) := by ring
      have heq3 : (Real.sin (2 * θ)) ^ 2 / sg = (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α) := by
        rw [hsg]; exact sq_div_rpow hσnn (Work.Spaces.gam α) hgam2
      rw [heq2, heq3] at hdiv
      rw [hf]
      simp only [Dth1Iter_zero, hch, one_mul]
      rw [hsg2]
      exact hdiv
    have htermk : ∀ k ∈ Finset.range (n - 1),
        (f (k + 1)) ^ 2 / sg ≤ ((Nat.choose (n - 1) (k + 1) : ℝ) * M) ^ 2
          * ((Dth1Iter (k + 1) (SinQ h) θ) ^ 2 / sg) := by
      intro k hk
      rw [Finset.mem_range] at hk
      have hj : n - 1 - (k + 1) = n - 2 - k := by omega
      have hφ : |Dth1Iter (n - 2 - k) (fun t : ℝ => 2 * Real.cos (2 * t)) θ| ≤ M :=
        hphi (n - 2 - k) (Finset.mem_Icc.mpr ⟨by omega, by omega⟩) θ
      have hc : (0 : ℝ) ≤ (Nat.choose (n - 1) (k + 1) : ℝ) := Nat.cast_nonneg _
      have h1 : |(Nat.choose (n - 1) (k + 1) : ℝ)
            * Dth1Iter (n - 2 - k) (fun t : ℝ => 2 * Real.cos (2 * t)) θ
            * Dth1Iter (k + 1) (SinQ h) θ|
          ≤ (Nat.choose (n - 1) (k + 1) : ℝ) * M * |Dth1Iter (k + 1) (SinQ h) θ| := by
        rw [abs_mul, abs_mul, abs_of_nonneg hc]
        exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hφ hc) (abs_nonneg _)
      have h2 : ((Nat.choose (n - 1) (k + 1) : ℝ)
            * Dth1Iter (n - 2 - k) (fun t : ℝ => 2 * Real.cos (2 * t)) θ
            * Dth1Iter (k + 1) (SinQ h) θ) ^ 2
          ≤ ((Nat.choose (n - 1) (k + 1) : ℝ) * M * |Dth1Iter (k + 1) (SinQ h) θ|) ^ 2 := by
        rw [← sq_abs ((Nat.choose (n - 1) (k + 1) : ℝ)
            * Dth1Iter (n - 2 - k) (fun t : ℝ => 2 * Real.cos (2 * t)) θ
            * Dth1Iter (k + 1) (SinQ h) θ)]
        exact pow_le_pow_left₀ (abs_nonneg _) h1 2
      have h3 : ((Nat.choose (n - 1) (k + 1) : ℝ) * M * |Dth1Iter (k + 1) (SinQ h) θ|) ^ 2
          = ((Nat.choose (n - 1) (k + 1) : ℝ) * M) ^ 2
              * (Dth1Iter (k + 1) (SinQ h) θ) ^ 2 := by
        rw [mul_pow, sq_abs]
      have hmain : ((Nat.choose (n - 1) (k + 1) : ℝ)
            * Dth1Iter (n - 2 - k) (fun t : ℝ => 2 * Real.cos (2 * t)) θ
            * Dth1Iter (k + 1) (SinQ h) θ) ^ 2 / sg
          ≤ (((Nat.choose (n - 1) (k + 1) : ℝ) * M) ^ 2
              * (Dth1Iter (k + 1) (SinQ h) θ) ^ 2) / sg :=
        div_le_div_of_nonneg_right (h2.trans (le_of_eq h3)) hsg_nn
      rw [hf]
      simp only [hj]
      simpa only [mul_div_assoc] using hmain
    have hreindex : (∑ k ∈ Finset.range (n - 1),
          ((Nat.choose (n - 1) (k + 1) : ℝ) * M) ^ 2 * ((Dth1Iter (k + 1) (SinQ h) θ) ^ 2 / sg))
        = ∑ k ∈ Finset.Icc 1 (n - 1),
            ((Nat.choose (n - 1) k : ℝ) * M) ^ 2 * ((Dth1Iter k (SinQ h) θ) ^ 2 / sg) := by
      have hIcc : Finset.Icc 1 (n - 1) = Finset.Ico 1 n := by
        ext k; simp only [Finset.mem_Icc, Finset.mem_Ico]; omega
      rw [hIcc, Finset.sum_Ico_eq_sum_range]
      exact Finset.sum_congr rfl fun k _ => by rw [add_comm]
    have hnn : (0 : ℝ) ≤ 2 * (n : ℝ) := by positivity
    have hb2 : (∑ k ∈ Finset.range (n - 1), (f (k + 1)) ^ 2 / sg)
        ≤ ∑ k ∈ Finset.Icc 1 (n - 1),
            ((Nat.choose (n - 1) k : ℝ) * M) ^ 2 * ((Dth1Iter k (SinQ h) θ) ^ 2 / sg) :=
      (Finset.sum_le_sum htermk).trans (le_of_eq hreindex)
    have hcomb : 2 * (n : ℝ) * ((∑ k ∈ Finset.range (n - 1), (f (k + 1)) ^ 2 / sg)
          + (f 0) ^ 2 / sg)
        ≤ 2 * (n : ℝ) * (M ^ 2 * ((h θ) ^ 2 * sg2)
          + ∑ k ∈ Finset.Icc 1 (n - 1),
              ((Nat.choose (n - 1) k : ℝ) * M) ^ 2
                * ((Dth1Iter k (SinQ h) θ) ^ 2 / sg)) :=
      mul_le_mul_of_nonneg_left
        (by simpa [add_comm] using add_le_add hb2 hterm0) hnn
    calc (Dth1Iter n (SinQ h) θ) ^ 2 / (Real.sin (2 * θ)) ^ (Work.Spaces.gam α)
        = (Dth1Iter n (SinQ h) θ) ^ 2 / sg := by rw [hsg]
      _ ≤ 2 * ((Dth1Iter (n - 1) (deriv h) θ) ^ 2 / sg)
            + 2 * (n : ℝ) * (∑ k ∈ Finset.range n, (f k) ^ 2 / sg) := hstep1
      _ = 2 * ((Dth1Iter (n - 1) (deriv h) θ) ^ 2 / sg)
            + 2 * (n : ℝ) * ((∑ k ∈ Finset.range (n - 1), (f (k + 1)) ^ 2 / sg)
              + (f 0) ^ 2 / sg) := by rw [hsplit]
      _ ≤ 2 * ((Dth1Iter (n - 1) (deriv h) θ) ^ 2 / sg)
            + 2 * (n : ℝ) * (M ^ 2 * ((h θ) ^ 2 * sg2)
              + ∑ k ∈ Finset.Icc 1 (n - 1),
                  ((Nat.choose (n - 1) k : ℝ) * M) ^ 2
                    * ((Dth1Iter k (SinQ h) θ) ^ 2 / sg)) :=
          add_le_add_right hcomb _
      _ = 2 * ((Dth1Iter (n - 1) (deriv h) θ) ^ 2 / sg)
            + 2 * (n : ℝ) * M ^ 2 * ((h θ) ^ 2 * sg2)
            + 2 * (n : ℝ) * ∑ k ∈ Finset.Icc 1 (n - 1),
                ((Nat.choose (n - 1) k : ℝ) * M) ^ 2
                  * ((Dth1Iter k (SinQ h) θ) ^ 2 / sg) := by ring
      _ = 2 * ((Dth1Iter (n - 1) (deriv h) θ) ^ 2 / (Real.sin (2 * θ)) ^ (Work.Spaces.gam α))
            + 2 * (n : ℝ) * M ^ 2 * ((h θ) ^ 2 * (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α))
            + 2 * (n : ℝ) * ∑ k ∈ Finset.Icc 1 (n - 1),
                ((Nat.choose (n - 1) k : ℝ) * M) ^ 2
                  * ((Dth1Iter k (SinQ h) θ) ^ 2 / (Real.sin (2 * θ)) ^ (Work.Spaces.gam α)) := by
          rw [hsg, hsg2]

/-! ## 7. Measurability helpers -/

private lemma measurable_sin_two_rpow (r : ℝ) (hr : 0 ≤ r) :
    Measurable (fun θ : ℝ => (Real.sin (2 * θ)) ^ r) := by
  have hc : Continuous (fun x : ℝ => x ^ r) := by
    rw [continuous_iff_continuousAt]
    intro x
    rcases eq_or_ne x 0 with h | h
    · subst h; exact Real.continuousAt_rpow_const 0 r (Or.inr hr)
    · exact Real.continuousAt_rpow_const x r (Or.inl h)
  exact hc.measurable.comp (by fun_prop)





private lemma ae_mem_Ioo : ∀ᵐ θ ∂(volume.restrict Work.Spaces.Iθ),
    θ ∈ Set.Ioo 0 (Real.pi / 2) := by
  have hnull : (volume : Measure ℝ) ({0, Real.pi / 2} : Set ℝ) = 0 := by
    have hset2 : ({0, Real.pi / 2} : Set ℝ) = {0} ∪ {Real.pi / 2} := by
      ext x; simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_union]
    simpa only [hset2] using MeasureTheory.measure_union_null
      (MeasureTheory.measure_singleton (0 : ℝ)) (MeasureTheory.measure_singleton (Real.pi / 2))
  have hset : {a : ℝ | ¬ a ∉ ({0, Real.pi / 2} : Set ℝ)} = ({0, Real.pi / 2} : Set ℝ) := by
    ext x
    simp only [Set.mem_setOf_eq, not_not, Set.mem_insert_iff, Set.mem_singleton_iff]
  have h1 : ∀ᵐ θ ∂(volume : Measure ℝ), θ ∉ ({0, Real.pi / 2} : Set ℝ) := by
    rw [MeasureTheory.ae_iff, hset]; exact hnull
  rw [MeasureTheory.ae_restrict_iff' Iθ_measurable]
  filter_upwards [h1] with θ hθ hI
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at hθ
  exact ⟨lt_of_le_of_ne hI.1 (Ne.symm hθ.1), lt_of_le_of_ne hI.2 hθ.2⟩

private lemma integral_three (f g h : ℝ → ℝ) (μ : Measure ℝ) (hf : Integrable f μ)
    (hg : Integrable g μ) (hh : Integrable h μ) :
    ∫ x, f x + g x + h x ∂μ = (∫ x, f x ∂μ) + (∫ x, g x ∂μ) + (∫ x, h x ∂μ) := by
  have h1 : ∫ x, f x + g x ∂μ = (∫ x, f x ∂μ) + (∫ x, g x ∂μ) := integral_add hf hg
  have h2 : ∫ x, (f x + g x) + h x ∂μ = (∫ x, f x + g x ∂μ) + (∫ x, h x ∂μ) :=
    integral_add (hf.add hg) hh
  rw [h2, h1]

/-! ## 8. The induction step -/





private lemma arith_key (p a b j : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hj : 0 ≤ j) (hp1 : p ≤ 1)
    (hcs : ((p+1)*a - b)^2 ≤ a*j) : 4*(a+b) ≤ j + 8*(1-p)*a + 16*b := by
  rcases eq_or_lt_of_le ha with ha' | ha'
  · subst ha'
    have hb' : b = 0 := by nlinarith [hcs, sq_nonneg b]
    subst hb'
    linarith
  · have hdiv : ((p+1)*a - b)^2 / a ≤ j := by
      rw [div_le_iff₀ ha']; linarith [hcs]
    have hmain : 4*(a+b) ≤ ((p+1)*a - b)^2/a + 8*(1-p)*a + 16*b := by
      have h2 : (((p+1)*a - b)^2/a + 8*(1-p)*a + 16*b) - 4*(a+b)
          = (b^2 + (1-p)*(5-p)*a^2 + (10-2*p)*a*b)/a := by
        field_simp
        ring
      have h3 : 0 ≤ (b^2 + (1-p)*(5-p)*a^2 + (10-2*p)*a*b)/a := by
        refine div_nonneg ?_ ha'.le
        have h4 : 0 ≤ (1-p)*(5-p)*a^2 :=
          mul_nonneg (mul_nonneg (by linarith) (by linarith)) (sq_nonneg a)
        have h5 : 0 ≤ (10-2*p)*(a*b) := mul_nonneg (by linarith) (mul_nonneg ha hb)
        nlinarith [sq_nonneg b, h4, h5]
      linarith
    linarith [hmain, hdiv]




/-! ## 9b. The induction constants (independent of `α`) and the assembly -/

/-- The four constants of the induction.  They are explicit expressions in the uniform base
constant `Cb`, the `L²`-constant `CL` and the angular bound `M`, hence independent of `α`. -/
private def KC1 (Cb : ℝ) : ℝ := Cb








end Work.Elliptic
end
end
-- ===== merged: Submission.Work.Elliptic.L12TermHigh =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.Elliptic

set_option autoImplicit false
set_option linter.unusedVariables false


end Work.Elliptic
end
end
-- ===== merged: Submission.Work.EllipticEst.Core.i0Aux.TVRed.surrIntegrableFull =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.EllipticEst.Core.i0Aux.TVRed

open scoped Real Topology
open MeasureTheory Set Filter

set_option autoImplicit false
set_option maxHeartbeats 1000000

noncomputable section

variable {ψ : ℝ → ℝ} {C F₀ F₁ L : ℝ}

/-! ## 1. The bump's derivative vanishes on the closed outer half-lines -/

/-- `deriv ψ = 0` on the closed left half-line `(-∞, 1/4]`.  (`IsBump.deriv_eq_zero_left`
gives the open version; `deriv ψ` is continuous, so the endpoint follows.) -/
lemma tvh_deriv_eq_zero_le (hψ : IsBump ψ C) {x : ℝ} (hx : x ≤ 1 / 4) : deriv ψ x = 0 := by
  have hcont : Continuous (deriv ψ) := hψ.contDiff.continuous_deriv (by norm_num)
  have hne : Filter.NeBot (nhdsWithin x (Set.Iio x)) := nhdsWithin_Iio_neBot (le_refl x)
  have h2 : Filter.Tendsto (deriv ψ) (nhdsWithin x (Set.Iio x)) (nhds 0) := by
    refine Filter.Tendsto.congr' (f₁ := fun _ : ℝ => (0 : ℝ)) ?_ tendsto_const_nhds
    filter_upwards [self_mem_nhdsWithin] with y hy
    exact (hψ.deriv_eq_zero_left y (lt_of_lt_of_le hy hx)).symm
  exact tendsto_nhds_unique (hcont.continuousAt.tendsto.mono_left nhdsWithin_le_nhds) h2


/-! ## 2. The surrogate's derivative vanishes on the closed outer intervals -/

/-- `ℓ' = 0` on `[0, L/4]`. -/
lemma tvh_deriv_surr_eq_zero_of_le (hψ : IsBump ψ C) (hL : 0 < L)
    (hLp : L ≤ Real.pi / 4) {θ : ℝ} (hθ : θ ≤ L / 4) :
    deriv (surrFun ψ F₀ F₁ L) θ = 0 := by
  rw [deriv_surr_eq hψ (ne_of_gt hL) θ]
  have h1 : deriv ψ (θ / L) = 0 := by
    apply tvh_deriv_eq_zero_le hψ
    rw [div_le_iff₀ hL]; linarith
  have h2 : deriv ψ ((Real.pi / 2 - θ) / L) = 0 := by
    apply hψ.deriv_eq_zero_right
    rw [lt_div_iff₀ hL]
    linarith [hθ, hLp, Real.pi_pos]
  rw [h1, h2]
  ring

/-- `ℓ' = 0` on `[π/2 - L/4, π/2]`. -/
lemma tvh_deriv_surr_eq_zero_of_ge (hψ : IsBump ψ C) (hL : 0 < L)
    (hLp : L ≤ Real.pi / 4) {θ : ℝ} (hθ : Real.pi / 2 - L / 4 ≤ θ) :
    deriv (surrFun ψ F₀ F₁ L) θ = 0 := by
  rw [deriv_surr_eq hψ (ne_of_gt hL) θ]
  have h1 : deriv ψ (θ / L) = 0 := by
    apply hψ.deriv_eq_zero_right
    rw [lt_div_iff₀ hL]
    linarith [hθ, hLp, Real.pi_pos]
  have h2 : deriv ψ ((Real.pi / 2 - θ) / L) = 0 := by
    apply tvh_deriv_eq_zero_le hψ
    rw [div_le_iff₀ hL]
    linarith [hθ]
  rw [h1, h2]
  ring

/-! ## 3. The lower bound on `sin 2θ` on the shells -/

/-- On the shell `(L/4, π/2 - L/4)` with `L ≤ π/4`, one has `sin(L/2) ≤ sin 2θ`.
(Both `2θ` and `π - 2θ` lie in `[L/2, π/2]`, and `sin` is increasing there.) -/
lemma tvh_sin_two_ge_sin (hL : 0 < L) (hLp : L ≤ Real.pi / 4) {θ : ℝ}
    (h1 : L / 4 < θ) (h2 : θ < Real.pi / 2 - L / 4) :
    Real.sin (L / 2) ≤ Real.sin (2 * θ) := by
  rcases le_or_gt (2 * θ) (Real.pi / 2) with hc | hc
  · exact le_of_lt (Real.sin_lt_sin_of_lt_of_le_pi_div_two
      (x := L / 2) (y := 2 * θ) (by linarith [Real.pi_pos]) hc (by linarith))
  · have hlt : L / 2 < Real.pi - 2 * θ := by linarith
    have hle : Real.pi - 2 * θ ≤ Real.pi / 2 := by linarith
    have h := Real.sin_lt_sin_of_lt_of_le_pi_div_two
      (x := L / 2) (y := Real.pi - 2 * θ) (by linarith [Real.pi_pos]) hle hlt
    rw [Real.sin_pi_sub] at h
    exact le_of_lt h

/-! ## 4. The bound `q² thEta ≤ (2η)² sin(L/2)^{-(2+η)}` -/

/-- On the shell, `qTh θ ^ 2 * thEta θ ≤ (2η)² sin(L/2)^{-(2+η)}`: the exploding factor `cot`
is dominated by `sin(L/2)^{-1}` and the weight by `sin(L/2)^{-η}`. -/
lemma tvh_cot_sq_mul_thEta_le (hL : 0 < L) (hLp : L ≤ Real.pi / 4) {θ : ℝ}
    (h1 : L / 4 < θ) (h2 : θ < Real.pi / 2 - L / 4) :
    (Real.cot (2 * θ)) ^ 2 * Work.FTS.EllipticEst.thEta θ
      ≤ (Real.sin (L / 2)) ^ (-(2 + Work.Spaces.eta)) := by
  have hspos : 0 < Real.sin (2 * θ) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith)
      (by linarith [h2, Real.pi_pos])
  have hLsinpos : 0 < Real.sin (L / 2) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [hLp, Real.pi_pos])
  have hle : Real.sin (L / 2) ≤ Real.sin (2 * θ) := tvh_sin_two_ge_sin hL hLp h1 h2
  have hexp : (-(2 + Work.Spaces.eta) : ℝ)
      = (-(2 : ℝ)) + (-(Work.Spaces.eta)) := by ring
  have hrp : (Real.sin (2 * θ)) ^ (-(2 + Work.Spaces.eta))
      = (Real.sin (2 * θ) ^ 2)⁻¹ * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) := by
    rw [hexp, Real.rpow_add hspos, Real.rpow_neg hspos.le (2 : ℝ),
      Real.rpow_two (Real.sin (2 * θ))]
  have hcot1 : Real.cot (2 * θ) ^ 2 = Real.cos (2 * θ) ^ 2 * (Real.sin (2 * θ) ^ 2)⁻¹ := by
    rw [Real.cot_eq_cos_div_sin, div_pow, div_eq_mul_inv]
  have key : Real.cot (2 * θ) ^ 2 * Work.FTS.EllipticEst.thEta θ
      = Real.cos (2 * θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(2 + Work.Spaces.eta)) := by
    rw [hcot1, hrp]
    simp only [Work.FTS.EllipticEst.thEta]
    ring
  rw [key]
  have hnn : 0 ≤ (Real.sin (2 * θ)) ^ (-(2 + Work.Spaces.eta)) :=
    Real.rpow_nonneg hspos.le _
  calc Real.cos (2 * θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(2 + Work.Spaces.eta))
      ≤ 1 * (Real.sin (2 * θ)) ^ (-(2 + Work.Spaces.eta)) :=
        mul_le_mul_of_nonneg_right (Real.cos_sq_le_one (2 * θ)) hnn
    _ = (Real.sin (2 * θ)) ^ (-(2 + Work.Spaces.eta)) := one_mul _
    _ ≤ (Real.sin (L / 2)) ^ (-(2 + Work.Spaces.eta)) :=
        Real.rpow_le_rpow_of_nonpos hLsinpos hle (by linarith [Work.Spaces.eta_pos])

/-! ## 5. Continuity of `qTh` on the open interval -/

/-- `qTh θ = 2 η cot(2θ)` is continuous on `(0, π/2)`, where `sin(2θ) ≠ 0`. -/
lemma tvh_continuousOn_qTh : ContinuousOn qTh (Set.Ioo 0 (Real.pi / 2)) := by
  have hq : qTh = fun θ : ℝ => 2 * Work.Spaces.eta * (Real.cos (2 * θ) / Real.sin (2 * θ)) := by
    funext θ
    rw [show qTh θ = 2 * Work.Spaces.eta * Real.cot (2 * θ) from rfl, Real.cot_eq_cos_div_sin]
  rw [hq]
  have hc : ContinuousOn (fun θ : ℝ => Real.cos (2 * θ)) (Set.Ioo 0 (Real.pi / 2)) :=
    (Real.continuous_cos.comp (continuous_const.mul continuous_id)).continuousOn
  have hs : ContinuousOn (fun θ : ℝ => Real.sin (2 * θ)) (Set.Ioo 0 (Real.pi / 2)) :=
    (Real.continuous_sin.comp (continuous_const.mul continuous_id)).continuousOn
  have hne : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2), Real.sin (2 * θ) ≠ 0 := by
    intro θ hθ
    exact ne_of_gt (Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1])
      (by linarith [hθ.2, Real.pi_pos]))
  have hdiv : ContinuousOn (fun θ : ℝ => Real.cos (2 * θ) / Real.sin (2 * θ))
      (Set.Ioo 0 (Real.pi / 2)) := hc.div hs hne
  exact continuousOn_const.mul hdiv

/-! ## 6. The fourth conjunct -/

/-- `(ℓ')² q² thEta` is integrable on `Iθ` for `0 < L ≤ π/4`. -/
theorem tvh_surr_deriv_qTh_integrable (hψ : IsBump ψ C) (hL : 0 < L)
    (hLp : L ≤ Real.pi / 4) :
    MeasureTheory.IntegrableOn
        (fun θ : ℝ => (deriv (surrFun ψ F₀ F₁ L) θ) ^ 2 * (qTh θ) ^ 2 *
          Work.FTS.EllipticEst.thEta θ) Work.Spaces.Iθ := by
  have hsL : 0 < Real.sin (L / 2) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [hLp, Real.pi_pos])
  obtain ⟨Q, hQdef⟩ : ∃ Q : ℝ, Q = (C * (|F₀| + |F₁|) / L) ^ 2
      * (2 * Work.Spaces.eta) ^ 2 * (Real.sin (L / 2)) ^ (-(2 + Work.Spaces.eta)) :=
    ⟨_, rfl⟩
  have hQnn : 0 ≤ Q := by
    rw [hQdef]
    exact mul_nonneg (mul_nonneg (sq_nonneg _) (sq_nonneg _))
      (Real.rpow_nonneg (le_of_lt hsL) _)
  have haesm : MeasureTheory.AEStronglyMeasurable
      (fun θ : ℝ => (deriv (surrFun ψ F₀ F₁ L) θ) ^ 2 * (qTh θ) ^ 2 *
        Work.FTS.EllipticEst.thEta θ) (MeasureTheory.volume.restrict Work.Spaces.Iθ) :=
    (((tvh_aesm_of_continuousOn
        (tvh_continuous_deriv_surr hψ (ne_of_gt hL)).continuousOn).pow 2).mul
      ((tvh_aesm_of_continuousOn tvh_continuousOn_qTh).pow 2)).mul tvh_aesm_thEta
  refine tvh_integrableOn_of_abs_le (tvh_integrableOn_const_mul_thEta Q) haesm ?_
  intro θ hθ
  have hσ : 0 ≤ Work.FTS.EllipticEst.thEta θ := Work.FTS.EllipticEst.thEta_nonneg hθ
  have hfac : 0 ≤ (deriv (surrFun ψ F₀ F₁ L) θ) ^ 2 * (qTh θ) ^ 2 :=
    mul_nonneg (sq_nonneg _) (sq_nonneg _)
  rw [abs_of_nonneg (mul_nonneg hfac hσ)]
  refine mul_le_mul_of_nonneg_right ?_ hσ
  have hderiv : (deriv (surrFun ψ F₀ F₁ L) θ) ^ 2 ≤ (C * (|F₀| + |F₁|) / L) ^ 2 := by
    rw [← sq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) (deriv_surr_bound hψ hL θ) 2
  have hb2nn : 0 ≤ (C * (|F₀| + |F₁|) / L) ^ 2 := sq_nonneg _
  rcases le_or_gt θ (L / 4) with hle1 | hlt
  · rw [tvh_deriv_surr_eq_zero_of_le hψ hL hLp hle1]
    simpa using hQnn
  · rcases le_or_gt (Real.pi / 2 - L / 4) θ with hle2 | hgt
    · rw [tvh_deriv_surr_eq_zero_of_ge hψ hL hLp hle2]
      simpa using hQnn
    · have hL4 : 0 < L / 4 := by positivity
      have hL2 : 0 < L / 2 := by positivity
      have hone : (1 : ℝ) ≤ Work.FTS.EllipticEst.thEta θ := by
        have h := Real.rpow_le_rpow_of_nonpos
          (x := Real.sin (2 * θ)) (y := 1) (z := -(Work.Spaces.eta))
          (Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [hgt, hL, Real.pi_pos]))
          (Real.sin_le_one (2 * θ)) (by linarith [Work.Spaces.eta_pos])
        simpa only [Work.FTS.EllipticEst.thEta, Real.one_rpow] using h
      have hcot : (Real.cot (2 * θ)) ^ 2
          ≤ (Real.sin (L / 2)) ^ (-(2 + Work.Spaces.eta)) :=
        calc (Real.cot (2 * θ)) ^ 2 = (Real.cot (2 * θ)) ^ 2 * 1 := (mul_one _).symm
          _ ≤ (Real.cot (2 * θ)) ^ 2 * Work.FTS.EllipticEst.thEta θ :=
              mul_le_mul_of_nonneg_left hone (sq_nonneg _)
          _ ≤ (Real.sin (L / 2)) ^ (-(2 + Work.Spaces.eta)) :=
              tvh_cot_sq_mul_thEta_le hL hLp hlt hgt
      have hq2 : (qTh θ) ^ 2 = (2 * Work.Spaces.eta) ^ 2 * (Real.cot (2 * θ)) ^ 2 := by
        rw [show qTh θ = 2 * Work.Spaces.eta * Real.cot (2 * θ) from rfl, mul_pow]
      calc (deriv (surrFun ψ F₀ F₁ L) θ) ^ 2 * (qTh θ) ^ 2
          = (deriv (surrFun ψ F₀ F₁ L) θ) ^ 2 *
              ((2 * Work.Spaces.eta) ^ 2 * (Real.cot (2 * θ)) ^ 2) := by rw [hq2]
        _ = ((deriv (surrFun ψ F₀ F₁ L) θ) ^ 2 * (2 * Work.Spaces.eta) ^ 2)
              * (Real.cot (2 * θ)) ^ 2 := by ring
        _ ≤ Q := by
            rw [hQdef]
            exact mul_le_mul
              (mul_le_mul_of_nonneg_right hderiv (sq_nonneg (2 * Work.Spaces.eta)))
              hcot (sq_nonneg (Real.cot (2 * θ)))
              (mul_nonneg hb2nn (sq_nonneg (2 * Work.Spaces.eta)))

/-! ## 7. The four-conjunct statement -/

/-- All four conjuncts of `surrIntegrable`: the first three are global bounds
(`TVRed.tvh_surr_integrable`), the fourth is `tvh_surr_deriv_qTh_integrable`. -/
theorem tvh_surr_integrable4 (hψ : IsBump ψ C) (hL : 0 < L) (hLp : L ≤ Real.pi / 4) :
    MeasureTheory.IntegrableOn
        (fun θ : ℝ => (surrFun ψ F₀ F₁ L θ) ^ 2 *
          Work.FTS.EllipticEst.thEta θ) Work.Spaces.Iθ ∧
    MeasureTheory.IntegrableOn
        (fun θ : ℝ => (deriv (surrFun ψ F₀ F₁ L) θ) ^ 2 *
          Work.FTS.EllipticEst.thEta θ) Work.Spaces.Iθ ∧
    MeasureTheory.IntegrableOn
        (fun θ : ℝ => (deriv (deriv (surrFun ψ F₀ F₁ L)) θ) ^ 2 *
          Work.FTS.EllipticEst.thEta θ) Work.Spaces.Iθ ∧
    MeasureTheory.IntegrableOn
        (fun θ : ℝ => (deriv (surrFun ψ F₀ F₁ L) θ) ^ 2 * (qTh θ) ^ 2 *
          Work.FTS.EllipticEst.thEta θ) Work.Spaces.Iθ := by
  obtain ⟨h1, h2, h3⟩ := tvh_surr_integrable (ψ := ψ) (C := C) (F₀ := F₀) (F₁ := F₁)
    (L := L) hψ hL
  exact ⟨h1, h2, h3, tvh_surr_deriv_qTh_integrable (ψ := ψ) (C := C) (F₀ := F₀) (F₁ := F₁)
    (L := L) hψ hL hLp⟩

end

end Work.EllipticEst.Core.i0Aux.TVRed
end
-- ===== merged: Submission.Work.EllipticEst.ModalSolution.eFamParsevalAux =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology ENNReal
open MeasureTheory Set Filter

namespace Work.EllipticEst.ModalSolution

local notation "Iθ" => Work.Spaces.Iθ
local notation "angMeasure" => Work.FTS.EllipticEst.LevelOneAsm.angMeasure

/-- The inner product of two mode classes is the weighted integral of the two modes. -/
theorem inner_eFamLp_eFamLp (n m : ℕ) :
    inner ℝ (eFamLp n) (eFamLp m) = ∫ θ in Iθ, eM n θ * eM m θ * Real.cos θ :=
  inner_toLp_eFamLp (eFam_memLp n) m

/-- The normalised modes form an orthonormal family of `L²(Iθ, cos θ dθ)`. -/
theorem eFamE_orthonormal_aux : Orthonormal ℝ eFamE := by
  rw [orthonormal_iff_ite]
  intro n m
  have hinner : inner ℝ (eFamE n) (eFamE m)
      = (Real.sqrt (eFamD n))⁻¹ * (Real.sqrt (eFamD m))⁻¹ *
        ∫ θ in Iθ, eM n θ * eM m θ * Real.cos θ := by
    rw [eFamE, eFamE, real_inner_smul_left, inner_smul_right, inner_eFamLp_eFamLp]
    ring
  rw [hinner]
  rcases eq_or_ne n m with hnm | hnm
  · subst hnm
    rw [ite_eq_left rfl]
    have hd := eFamD_pos n
    have hI : (∫ θ in Iθ, eM n θ * eM n θ * Real.cos θ) = eFamD n := by
      rw [eFamD]
      exact setIntegral_congr_fun measurableSet_Icc (fun θ _ => by ring)
    rw [hI, ← mul_inv, ← sq, Real.sq_sqrt (le_of_lt hd), inv_mul_cancel₀ (ne_of_gt hd)]
  · rw [ite_eq_right hnm]
    have hzero : (∫ θ in Iθ, eM n θ * eM m θ * Real.cos θ) = 0 := by
      rw [integral_Iθ_eq_intervalIntegral]
      exact Work.FTS.PhiStar.Gegenbauer.eFam_orthogonal n m hnm
    rw [hzero, mul_zero]

/-- **Totality of the modes**: the orthogonal complement of the span of `eFamE` is trivial.
This is `eFam_complete` transported to `Lp ℝ 2 angMeasure`. -/
theorem eFamE_span_orthogonal_eq_bot_aux :
    Submodule.orthogonal (Submodule.span ℝ (Set.range eFamE)) = ⊥ := by
  rw [Submodule.eq_bot_iff]
  intro y hy
  -- `y` is orthogonal to every normalised mode
  have hmem : ∀ n : ℕ, inner ℝ (eFamE n) y = 0 := fun n =>
    (Submodule.mem_orthogonal _ y).mp hy (eFamE n) (Submodule.subset_span (Set.mem_range_self n))
  -- hence orthogonal to every raw mode class (the normalising scalar is nonzero)
  have hLp : ∀ n : ℕ, inner ℝ (eFamLp n) y = 0 := by
    intro n
    have h := hmem n
    simp only [eFamE, real_inner_smul_left] at h
    rcases mul_eq_zero.mp h with h' | h'
    · exact absurd h' (inv_ne_zero (ne_of_gt (Real.sqrt_pos.mpr (eFamD_pos n))))
    · exact h'
  -- the mode moments of the representative of `y` vanish, in the order used by `eFam_complete`
  have hint : ∀ n : ℕ,
      (∫ θ in Iθ, (y : ℝ → ℝ) θ * eM n θ * Real.cos θ) = 0 := by
    intro n
    rw [show (∫ θ in Iθ, (y : ℝ → ℝ) θ * eM n θ * Real.cos θ)
          = ∫ θ in Iθ, eM n θ * (y : ℝ → ℝ) θ * Real.cos θ from
        setIntegral_congr_fun measurableSet_Icc (fun θ _ => by ring)]
    rw [← inner_eFamLp_any n y]
    exact hLp n
  -- a.e. strong measurability and square integrability for the unweighted measure
  have hy_aesm_L : AEStronglyMeasurable (y : ℝ → ℝ) (volume.restrict Iθ) :=
    AEStronglyMeasurable.mono_ac
      Work.FTS.EllipticEst.LevelOneAsm.restrict_absolutelyContinuous_angMeasure
      (MeasureTheory.Lp.memLp y).aestronglyMeasurable
  have hy_int_sq : Integrable (fun a => ((y : ℝ → ℝ) a) ^ 2) angMeasure :=
    (MeasureTheory.memLp_two_iff_integrable_sq
      (MeasureTheory.Lp.memLp y).aestronglyMeasurable).mp (MeasureTheory.Lp.memLp y)
  have hy_int : IntegrableOn (fun θ => ((y : ℝ → ℝ) θ) ^ 2 * Real.cos θ) Iθ := by
    show Integrable (fun θ => ((y : ℝ → ℝ) θ) ^ 2 * Real.cos θ) (volume.restrict Iθ)
    have h := (MeasureTheory.integrable_withDensity_iff_integrable_smul'
      (μ := volume.restrict Iθ)
      (f := fun θ => ENNReal.ofReal (Real.cos θ))
      (Real.measurable_cos.ennreal_ofReal)
      (Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))
      (g := fun a => ((y : ℝ → ℝ) a) ^ 2)).mp hy_int_sq
    refine h.congr ?_
    filter_upwards [ae_restrict_mem (s := Iθ) measurableSet_Icc] with θ hθ
    simp only [smul_eq_mul]
    rw [ENNReal.toReal_ofReal (Work.FTS.EllipticEst.LevelOneAsm.cos_nonneg_of_mem_Iθ hθ)]
    ring
  -- completeness of the mode system
  have hae := Work.FTS.PhiStar.Gegenbauer.eFam_complete (y : ℝ → ℝ) hy_aesm_L hy_int
    (fun m => hint m)
  have hae2 : (y : ℝ → ℝ) =ᵐ[angMeasure] 0 :=
    Work.FTS.EllipticEst.LevelOneAsm.angMeasure_absolutelyContinuous.ae_eq hae
  exact (MeasureTheory.Lp.eq_zero_iff_ae_eq_zero).mpr hae2

/-- `cmode` (interval integrals on `(0, π/2)`) in terms of the set integral over `Iθ` and the
norm `eFamD` used by the `L²` inner products. -/
theorem cmode_eq_setIntegral_aux (F : ℝ → ℝ → ℝ) (z : ℝ) (m : ℕ) :
    Work.FTS.PhiStar.Series.cmode m F z
      = (∫ θ in Iθ, F z θ * eM m θ * Real.cos θ) / eFamD m := by
  show (∫ θ in (0 : ℝ)..(Real.pi / 2),
        F z θ * Work.FTS.PhiStar.Gegenbauer.eFam m θ * Real.cos θ)
      / (∫ θ in (0 : ℝ)..(Real.pi / 2),
        Work.FTS.PhiStar.Gegenbauer.eFam m θ ^ 2 * Real.cos θ)
    = (∫ θ in Iθ, F z θ * eM m θ * Real.cos θ) / eFamD m
  have h1 : (∫ θ in (0 : ℝ)..(Real.pi / 2),
        F z θ * Work.FTS.PhiStar.Gegenbauer.eFam m θ * Real.cos θ)
      = ∫ θ in Iθ, F z θ * eM m θ * Real.cos θ := by
    rw [← integral_Iθ_eq_intervalIntegral
      (f := fun θ => F z θ * Work.FTS.PhiStar.Gegenbauer.eFam m θ * Real.cos θ)]
    try exact setIntegral_congr_fun measurableSet_Icc (fun θ _ => by simp only [eM])
  have h2 : (∫ θ in (0 : ℝ)..(Real.pi / 2),
        Work.FTS.PhiStar.Gegenbauer.eFam m θ ^ 2 * Real.cos θ) = eFamD m := by
    rw [← integral_Iθ_eq_intervalIntegral
      (f := fun θ => Work.FTS.PhiStar.Gegenbauer.eFam m θ ^ 2 * Real.cos θ)]
    try rw [eFamD]
    try exact setIntegral_congr_fun measurableSet_Icc (fun θ _ => by simp only [eM])
  rw [h1, h2]

end Work.EllipticEst.ModalSolution
end
end
-- ===== merged: Submission.Work.FTS.ClassCHon.CmpSupp.coeff_le_decay =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.ClassCHon.CmpSupp



end Work.FTS.ClassCHon.CmpSupp
end
-- ===== merged: Submission.Work.FTS.ClassCHon.HcoefSplit.hcoef_Bterm_le =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.ClassCHon.HcoefSplit

theorem hcoef_Bterm_le {α β : ℝ} (hα : 0 < α) (hα4 : α ≤ 1 / 4) (hβ : 0 ≤ β) {m : ℕ}
    (hm : 1 ≤ m) :
    ((m : ℝ) + 1) * (Work.FTS.EllExist.rgK α m
        * ((β / Real.sqrt (Work.EllipticEst.ModalSolution.eNorm m))
          * ((2 : ℝ) ^ (-(Work.FTS.EllExist.rgQ α m))
                / Real.sqrt (2 * Work.FTS.EllExist.rgQ α m - 1)
              + (2 : ℝ) ^ (-(Work.FTS.EllExist.rgP α m))
                / Real.sqrt (2 * Work.FTS.EllExist.rgP α m - 3))))
      ≤ (β / α) * (1 / 2 : ℝ) ^ m := by
  -- Throughout, `P = rgP α m = 2m/α` is the growing exponent, `Q = rgQ α m = (2m+5)/α`
  -- the decaying one, `K = rgK α m = 1/(α(4m+5))` the normalisation, and `E = eNorm m ≥ 1`.
  -- The two exponential coefficients are estimated by `2^{-Q} ≤ 2^{-P} ≤ 2^{-m} = (1/2)^m`,
  -- the two square-root factors by `1/√(2Q-1) ≤ 1`, `1/√(2P-3) ≤ 1`, and the algebraic
  -- prefactor by `(m+1)/(α(4m+5)) ≤ (1/2)(1/α)`.
  have hm0 : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
  have hm1 : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have hE : 1 ≤ Work.EllipticEst.ModalSolution.eNorm m :=
    (Work.FTS.ClassCHon.CmpSupp.eNorm_bounds m).1
  -- `P ≥ 8m`: since `α ≤ 1/4`, `2m/α ≥ 8m`.
  have hP8 : 8 * (m : ℝ) ≤ Work.FTS.EllExist.rgP α m := by
    rw [Work.FTS.EllExist.rgP, le_div_iff₀ hα]
    nlinarith [mul_le_mul_of_nonneg_left hα4 hm0]
  have hPm : (m : ℝ) ≤ Work.FTS.EllExist.rgP α m := by
    have : (m : ℝ) ≤ 8 * (m : ℝ) := by linarith
    linarith
  -- `Q ≥ 20`: since `α ≤ 1/4`, `(2m+5)/α ≥ 5/α ≥ 20`.
  have hQ20 : 20 ≤ Work.FTS.EllExist.rgQ α m := by
    rw [Work.FTS.EllExist.rgQ, le_div_iff₀ hα]
    linarith
  have hPQ : Work.FTS.EllExist.rgP α m ≤ Work.FTS.EllExist.rgQ α m := by
    rw [Work.FTS.EllExist.rgP, Work.FTS.EllExist.rgQ]
    exact div_le_div_of_nonneg_right (by linarith) hα.le
  have hQmono : (2 : ℝ) ^ (-(Work.FTS.EllExist.rgQ α m))
      ≤ (2 : ℝ) ^ (-(Work.FTS.EllExist.rgP α m)) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
  have hPhalf : (2 : ℝ) ^ (-(Work.FTS.EllExist.rgP α m)) ≤ (1 / 2 : ℝ) ^ m := by
    calc (2 : ℝ) ^ (-(Work.FTS.EllExist.rgP α m)) ≤ (2 : ℝ) ^ (-(m : ℝ)) :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
      _ = (1 / 2 : ℝ) ^ m := by
          rw [Real.rpow_neg (by norm_num), Real.rpow_natCast, one_div, inv_pow]
  have ht1 : (2 : ℝ) ^ (-(Work.FTS.EllExist.rgQ α m))
      / Real.sqrt (2 * Work.FTS.EllExist.rgQ α m - 1) ≤ (1 / 2 : ℝ) ^ m :=
    le_trans (div_le_self (Real.rpow_nonneg (by norm_num) _)
      (Real.one_le_sqrt.mpr (by linarith))) (le_trans hQmono hPhalf)
  have ht2 : (2 : ℝ) ^ (-(Work.FTS.EllExist.rgP α m))
      / Real.sqrt (2 * Work.FTS.EllExist.rgP α m - 3) ≤ (1 / 2 : ℝ) ^ m :=
    le_trans (div_le_self (Real.rpow_nonneg (by norm_num) _)
      (Real.one_le_sqrt.mpr (by linarith))) hPhalf
  have hbr : (2 : ℝ) ^ (-(Work.FTS.EllExist.rgQ α m))
        / Real.sqrt (2 * Work.FTS.EllExist.rgQ α m - 1)
      + (2 : ℝ) ^ (-(Work.FTS.EllExist.rgP α m))
        / Real.sqrt (2 * Work.FTS.EllExist.rgP α m - 3) ≤ 2 * (1 / 2 : ℝ) ^ m := by
    have h := add_le_add ht1 ht2
    linarith
  have hbrnn : 0 ≤ (2 : ℝ) ^ (-(Work.FTS.EllExist.rgQ α m))
        / Real.sqrt (2 * Work.FTS.EllExist.rgQ α m - 1)
      + (2 : ℝ) ^ (-(Work.FTS.EllExist.rgP α m))
        / Real.sqrt (2 * Work.FTS.EllExist.rgP α m - 3) := by positivity
  have hA : ((m : ℝ) + 1) * Work.FTS.EllExist.rgK α m ≤ (1 / 2) * (1 / α) := by
    rw [Work.FTS.EllExist.rgK]
    field_simp
    nlinarith [hm1]
  have hB : β / Real.sqrt (Work.EllipticEst.ModalSolution.eNorm m) ≤ β :=
    div_le_self hβ (Real.one_le_sqrt.mpr hE)
  have hAnn : (0 : ℝ) ≤ ((m : ℝ) + 1) * Work.FTS.EllExist.rgK α m := by
    rw [Work.FTS.EllExist.rgK]; positivity
  have hBnn : (0 : ℝ) ≤ β / Real.sqrt (Work.EllipticEst.ModalSolution.eNorm m) := by
    positivity
  have hBC : (β / Real.sqrt (Work.EllipticEst.ModalSolution.eNorm m))
      * ((2 : ℝ) ^ (-(Work.FTS.EllExist.rgQ α m))
          / Real.sqrt (2 * Work.FTS.EllExist.rgQ α m - 1)
        + (2 : ℝ) ^ (-(Work.FTS.EllExist.rgP α m))
          / Real.sqrt (2 * Work.FTS.EllExist.rgP α m - 3))
      ≤ β * (2 * (1 / 2 : ℝ) ^ m) := mul_le_mul hB hbr hbrnn hβ
  have hBCleft : (0 : ℝ) ≤ (β / Real.sqrt (Work.EllipticEst.ModalSolution.eNorm m))
      * ((2 : ℝ) ^ (-(Work.FTS.EllExist.rgQ α m))
          / Real.sqrt (2 * Work.FTS.EllExist.rgQ α m - 1)
        + (2 : ℝ) ^ (-(Work.FTS.EllExist.rgP α m))
          / Real.sqrt (2 * Work.FTS.EllExist.rgP α m - 3)) := mul_nonneg hBnn hbrnn
  have hAnn2 : (0 : ℝ) ≤ (1 / 2) * (1 / α) := by positivity
  rw [show ((m : ℝ) + 1) * (Work.FTS.EllExist.rgK α m
        * ((β / Real.sqrt (Work.EllipticEst.ModalSolution.eNorm m))
          * ((2 : ℝ) ^ (-(Work.FTS.EllExist.rgQ α m))
                / Real.sqrt (2 * Work.FTS.EllExist.rgQ α m - 1)
              + (2 : ℝ) ^ (-(Work.FTS.EllExist.rgP α m))
                / Real.sqrt (2 * Work.FTS.EllExist.rgP α m - 3))))
      = (((m : ℝ) + 1) * Work.FTS.EllExist.rgK α m)
        * ((β / Real.sqrt (Work.EllipticEst.ModalSolution.eNorm m))
          * ((2 : ℝ) ^ (-(Work.FTS.EllExist.rgQ α m))
                / Real.sqrt (2 * Work.FTS.EllExist.rgQ α m - 1)
              + (2 : ℝ) ^ (-(Work.FTS.EllExist.rgP α m))
                / Real.sqrt (2 * Work.FTS.EllExist.rgP α m - 3))) from by ring]
  calc (((m : ℝ) + 1) * Work.FTS.EllExist.rgK α m)
        * ((β / Real.sqrt (Work.EllipticEst.ModalSolution.eNorm m))
          * ((2 : ℝ) ^ (-(Work.FTS.EllExist.rgQ α m))
                / Real.sqrt (2 * Work.FTS.EllExist.rgQ α m - 1)
              + (2 : ℝ) ^ (-(Work.FTS.EllExist.rgP α m))
                / Real.sqrt (2 * Work.FTS.EllExist.rgP α m - 3)))
      ≤ ((1 / 2) * (1 / α)) * (β * (2 * (1 / 2 : ℝ) ^ m)) := mul_le_mul hA hBC hBCleft hAnn2
    _ = (β / α) * (1 / 2 : ℝ) ^ m := by ring

end Work.FTS.ClassCHon.HcoefSplit
end
-- ===== merged: Submission.Work.FTS.ClassCHon.HcoefSplit.hcoef_Lterm_le =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.ClassCHon.HcoefSplit

theorem hcoef_Lterm_le {α L : ℝ} (hα : 0 < α) (hα4 : α ≤ 1 / 4) (hL : 0 ≤ L) {m : ℕ}
    (hm : 1 ≤ m) :
    ((m : ℝ) + 1) * (Work.FTS.EllExist.rgK α m
        * ((L / Real.sqrt (Work.EllipticEst.ModalSolution.eNorm m))
          * (1 / Work.FTS.EllExist.rgQ α m + 1 / Work.FTS.EllExist.rgP α m)))
      ≤ L * (m : ℝ) ^ (-(3 / 2 : ℝ)) := by
  -- `α` cancels between `rgK` and `1/rgQ + 1/rgP`; what remains is
  -- `(m+1)/((2m+5)·2m) · 1/√(eNorm m) ≤ m^{-3/2}`, since `eNorm m ≥ m`.
  have hαne : α ≠ 0 := ne_of_gt hα
  have hm0 : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  have hmne : (m : ℝ) ≠ 0 := ne_of_gt hm0
  -- the cancellation of `α`
  have hkey : Work.FTS.EllExist.rgK α m * (1 / Work.FTS.EllExist.rgQ α m
        + 1 / Work.FTS.EllExist.rgP α m)
      = 1 / ((2 * (m : ℝ) + 5) * (2 * (m : ℝ))) := by
    rw [Work.FTS.EllExist.rgK, Work.FTS.EllExist.rgQ, Work.FTS.EllExist.rgP]
    field_simp
    ring
  -- `(m+1)/((2m+5)·2m) ≤ 1/m`, since `m(m+1) ≤ (2m+5)·2m`
  have hcoef : ((m : ℝ) + 1) / ((2 * (m : ℝ) + 5) * (2 * (m : ℝ))) ≤ 1 / (m : ℝ) := by
    have hpos : (0 : ℝ) < (2 * (m : ℝ) + 5) * (2 * (m : ℝ)) := by positivity
    rw [div_le_iff₀ hpos]
    have h1 : 1 / (m : ℝ) * ((2 * (m : ℝ) + 5) * (2 * (m : ℝ))) = 2 * (2 * (m : ℝ) + 5) := by
      field_simp
    rw [h1]
    linarith
  -- `1/√(eNorm m) ≤ 1/√m`, from `eNorm m ≥ m`
  have hsqrtinv :
      1 / Real.sqrt (Work.EllipticEst.ModalSolution.eNorm m) ≤ 1 / Real.sqrt (m : ℝ) := by
    have hge : (m : ℝ) ≤ Work.EllipticEst.ModalSolution.eNorm m :=
      (Work.FTS.ClassCHon.CmpSupp.eNorm_bounds m).2
    have hsq : Real.sqrt (m : ℝ) ≤ Real.sqrt (Work.EllipticEst.ModalSolution.eNorm m) :=
      Real.sqrt_le_sqrt hge
    exact one_div_le_one_div_of_le (Real.sqrt_pos.2 hm0) hsq
  -- `m^{-3/2} = 1/(m·√m)`
  have hrpow : (m : ℝ) ^ (-(3 / 2 : ℝ)) = 1 / ((m : ℝ) * Real.sqrt (m : ℝ)) := by
    have hmul : (m : ℝ) * Real.sqrt (m : ℝ) = (m : ℝ) ^ (3 / 2 : ℝ) := by
      have h := Real.rpow_add hm0 (1 : ℝ) (1 / 2 : ℝ)
      rw [Real.rpow_one, show (1 : ℝ) + 1 / 2 = 3 / 2 from by norm_num,
        ← Real.sqrt_eq_rpow] at h
      exact h.symm
    rw [Real.rpow_neg (le_of_lt hm0), hmul, one_div]
  have hright : (1 / (m : ℝ)) * (1 / Real.sqrt (m : ℝ)) = (m : ℝ) ^ (-(3 / 2 : ℝ)) := by
    rw [hrpow]
    field_simp
  have step1 : ((m : ℝ) + 1) * (Work.FTS.EllExist.rgK α m
        * ((L / Real.sqrt (Work.EllipticEst.ModalSolution.eNorm m))
          * (1 / Work.FTS.EllExist.rgQ α m + 1 / Work.FTS.EllExist.rgP α m)))
      = L * (((m : ℝ) + 1) * (1 / Real.sqrt (Work.EllipticEst.ModalSolution.eNorm m))
          * (1 / ((2 * (m : ℝ) + 5) * (2 * (m : ℝ))))) := by
    rw [show ((m : ℝ) + 1) * (Work.FTS.EllExist.rgK α m
        * ((L / Real.sqrt (Work.EllipticEst.ModalSolution.eNorm m))
          * (1 / Work.FTS.EllExist.rgQ α m + 1 / Work.FTS.EllExist.rgP α m)))
        = ((m : ℝ) + 1) * ((L / Real.sqrt (Work.EllipticEst.ModalSolution.eNorm m))
          * (Work.FTS.EllExist.rgK α m * (1 / Work.FTS.EllExist.rgQ α m
              + 1 / Work.FTS.EllExist.rgP α m))) from by ring,
      hkey]
    ring
  have step2 : ((m : ℝ) + 1) * (1 / Real.sqrt (Work.EllipticEst.ModalSolution.eNorm m))
      * (1 / ((2 * (m : ℝ) + 5) * (2 * (m : ℝ)))) ≤ (m : ℝ) ^ (-(3 / 2 : ℝ)) := by
    have hval : ((m : ℝ) + 1) * (1 / Real.sqrt (Work.EllipticEst.ModalSolution.eNorm m))
        * (1 / ((2 * (m : ℝ) + 5) * (2 * (m : ℝ))))
        = (((m : ℝ) + 1) / ((2 * (m : ℝ) + 5) * (2 * (m : ℝ))))
            * (1 / Real.sqrt (Work.EllipticEst.ModalSolution.eNorm m)) := by ring
    rw [hval, ← hright]
    exact mul_le_mul hcoef hsqrtinv (by positivity) (by positivity)
  calc ((m : ℝ) + 1) * (Work.FTS.EllExist.rgK α m
        * ((L / Real.sqrt (Work.EllipticEst.ModalSolution.eNorm m))
          * (1 / Work.FTS.EllExist.rgQ α m + 1 / Work.FTS.EllExist.rgP α m)))
      = L * (((m : ℝ) + 1) * (1 / Real.sqrt (Work.EllipticEst.ModalSolution.eNorm m))
          * (1 / ((2 * (m : ℝ) + 5) * (2 * (m : ℝ))))) := step1
    _ ≤ L * (m : ℝ) ^ (-(3 / 2 : ℝ)) := mul_le_mul_of_nonneg_left step2 hL

end Work.FTS.ClassCHon.HcoefSplit
end
-- ===== merged: Submission.Work.FTS.CoercivityFix.Assembly.L2Sq_blocks_le_HkSq =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.CoercivityFix.Assembly

/-! ## The two null endpoints of `Iθ`

`sin(2θ)` vanishes exactly at `θ = 0` and `θ = π/2`, where the `η`-weighted block
`f·w/√(sin 2θ^η)` degenerates.  Off these two points the plain block `f·w` is
dominated by it, which is enough because `(0,π/2)` is co-null in `Iθ`. -/

/-- The open interval `(0,π/2)` is co-null in `Iθ`, so the two restricted measures agree. -/
private lemma restrict_Ioo_eq_restrict_Iθ :
    volume.restrict (Set.Ioo (0 : ℝ) (π / 2)) = volume.restrict Work.Spaces.Iθ :=
  Measure.restrict_congr_set (by rw [Work.Spaces.Iθ]; exact MeasureTheory.Ioo_ae_eq_Icc)

/-- Off the two null endpoints of `Iθ`, the plain block `Xw f = f·w` is dominated by the
`ℋ¹`-integrand, because the `D_z⁰`-summand of the latter is `(f·w/√(sin 2θ^η))²` and
`√(sin 2θ^η) ≤ 1` there. -/
private theorem sq_Xw_le_HkIntegrand_ae_prv (α : ℝ) (f : ℝ → ℝ → ℝ) (z : ℝ) :
    ∀ᵐ θ ∂(volume.restrict Work.Spaces.Iθ),
      (Work.Coercivity.Xw f z θ) ^ 2 ≤ Work.Spaces.HkIntegrand α 1 f z θ := by
  rw [← restrict_Ioo_eq_restrict_Iθ]
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with θ hθ
  have hs0 : 0 < Real.sin (2 * θ) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])
  have hs1 : Real.sin (2 * θ) ≤ 1 := Real.sin_le_one _
  have ht0 : 0 < (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2) := Real.rpow_pos_of_pos hs0 _
  have ht1 : (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2) ≤ 1 := by
    calc (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2)
        ≤ (1 : ℝ) ^ (Work.Spaces.eta / 2) :=
          Real.rpow_le_rpow (le_of_lt hs0) hs1
            (div_nonneg (le_of_lt Work.Spaces.eta_pos) (by norm_num))
      _ = 1 := by simp
  have hkey : (f z θ * Work.Spaces.w z) ^ 2
      ≤ ((f z θ * Work.Spaces.w z) / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2)) ^ 2 := by
    rw [div_pow, le_div_iff₀ (pow_pos ht0 2)]
    have ht2 : (Real.sin (2 * θ) ^ (Work.Spaces.eta / 2)) ^ 2 ≤ 1 := by
      nlinarith [ht0, ht1]
    simpa using mul_le_mul_of_nonneg_left ht2 (sq_nonneg (f z θ * Work.Spaces.w z))
  have hterm : (Work.Coercivity.Xw f z θ) ^ 2
      ≤ (Work.Spaces.DzIter 0 f z θ
          * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2 := by
    simp only [Work.Coercivity.Xw, Work.Spaces.DzIter_zero]
    rw [← mul_div_assoc]
    exact hkey
  exact le_trans hterm
    (Work.Spaces.sq_le_HkIntegrand_z α 1 f z θ 0 (by norm_num))



end Work.FTS.CoercivityFix.Assembly
end
end
-- ===== merged: Submission.Work.FTS.CoercivityFix.Transfer.E2pkg.rB_iter =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open Set Filter

namespace Work.FTS.CoercivityFix.Transfer.E2pkg

set_option maxHeartbeats 800000

/-! ## The one-dimensional recursion -/

/-- The recursion step for the `(z∂_z)`-iterates of a rational function
`w ↦ w²·P(w)/(1+w)^{m+1}`: for `z ≠ -1`,

  `z · d/dz [ w²·P(w)/(1+w)^{m+1} ] = z²·( (1+z)(2P(z)+zP'(z)) - (m+1)·z·P(z) ) / (1+z)^{m+2}`. -/
theorem z_mul_deriv_rat (P : ℝ → ℝ) (P' : ℝ) (m : ℕ) (z : ℝ)
    (hP : HasDerivAt P P' z) (hz : 1 + z ≠ 0) :
    z * deriv (fun w : ℝ => w ^ 2 * P w / (1 + w) ^ (m + 1)) z
      = z ^ 2 * ((1 + z) * (2 * P z + z * P') - (m + 1) * z * P z) / (1 + z) ^ (m + 2) := by
  have h2 : HasDerivAt (fun w : ℝ => w ^ 2) (2 * z) z := by
    simpa using hasDerivAt_pow 2 z
  have hnum : HasDerivAt (fun w : ℝ => w ^ 2 * P w) (2 * z * P z + z ^ 2 * P') z := by
    convert (h2.mul hP) using 1
  have h1z : HasDerivAt (fun w : ℝ => 1 + w) 1 z := by
    simpa using (hasDerivAt_id z).const_add 1
  have hden : HasDerivAt (fun w : ℝ => (1 + w) ^ (m + 1)) ((m + 1 : ℕ) * (1 + z) ^ m) z := by
    convert h1z.pow (m + 1) using 1
    simp
  have hden0 : (1 + z) ^ (m + 1) ≠ 0 := pow_ne_zero _ hz
  have hres := hnum.div hden hden0
  have hfun : (fun w : ℝ => w ^ 2 * P w / (1 + w) ^ (m + 1))
      = (fun w : ℝ => w ^ 2 * P w) / (fun w : ℝ => (1 + w) ^ (m + 1)) := rfl
  rw [hfun, hres.deriv]
  have hsq : ((1 + z) ^ (m + 1)) ^ 2 = (1 + z) ^ (m + 2) * (1 + z) ^ m := by
    rw [← pow_mul, ← pow_add]
    congr 1
    ring
  rw [hsq]
  simp only [pow_succ]
  field_simp
  push_cast
  ring

/-! ## The four instances (`Dzd` of the `rB`-profiles) -/

/-- `z ∂_z` of `w²/(1+w)³` is `rB 1`. -/
theorem z_mul_deriv_rB_zero (z : ℝ) (hz : 1 + z ≠ 0) :
    z * deriv (fun w : ℝ => w ^ 2 / (1 + w) ^ 3) z = rB 1 z := by
  have h := z_mul_deriv_rat (fun _ : ℝ => (1 : ℝ)) 0 2 z (hasDerivAt_const z 1) hz
  have heq : (fun w : ℝ => w ^ 2 / (1 + w) ^ 3)
      = (fun w : ℝ => w ^ 2 * 1 / (1 + w) ^ 3) := by
    funext w
    rw [mul_one]
  rw [heq]
  refine h.trans ?_
  simp only [rB_one]
  ring_nf

/-- `z ∂_z` of `w²(2-w)/(1+w)⁴` is `rB 2`. -/
theorem z_mul_deriv_rB_one (z : ℝ) (hz : 1 + z ≠ 0) :
    z * deriv (fun w : ℝ => w ^ 2 * (2 - w) / (1 + w) ^ 4) z = rB 2 z := by
  have hlin : HasDerivAt (fun w : ℝ => w) (1 : ℝ) z := by simpa using hasDerivAt_pow 1 z
  have hP : HasDerivAt (fun w : ℝ => 2 - w) (-1) z := by
    have h0 := (hasDerivAt_const z (2 : ℝ)).sub hlin
    convert h0 using 1 <;> first | ring | (ext w; ring)
  refine (z_mul_deriv_rat (fun w : ℝ => 2 - w) (-1) 3 z hP hz).trans ?_
  simp only [rB_two]
  ring_nf

/-- `z ∂_z` of `w²(4-7w+w²)/(1+w)⁵` is `rB 3`. -/
theorem z_mul_deriv_rB_two (z : ℝ) (hz : 1 + z ≠ 0) :
    z * deriv (fun w : ℝ => w ^ 2 * (4 - 7 * w + w ^ 2) / (1 + w) ^ 5) z = rB 3 z := by
  have hlin : HasDerivAt (fun w : ℝ => w) (1 : ℝ) z := by simpa using hasDerivAt_pow 1 z
  have h2 : HasDerivAt (fun w : ℝ => w ^ 2) (2 * z) z := by
    simpa using hasDerivAt_pow 2 z
  have hP : HasDerivAt (fun w : ℝ => 4 - 7 * w + w ^ 2) (-7 + 2 * z) z := by
    have h0 := ((hasDerivAt_const z (4 : ℝ)).sub (hlin.const_mul 7)).add h2
    convert h0 using 1 <;> first | ring | (ext w; ring)
  refine (z_mul_deriv_rat (fun w : ℝ => 4 - 7 * w + w ^ 2) (-7 + 2 * z) 4 z hP hz).trans ?_
  simp only [rB_three]
  ring_nf

/-- `z ∂_z` of `w²(8-33w+18w²-w³)/(1+w)⁶` is `rB 4`. -/
theorem z_mul_deriv_rB_three (z : ℝ) (hz : 1 + z ≠ 0) :
    z * deriv (fun w : ℝ => w ^ 2 * (8 - 33 * w + 18 * w ^ 2 - w ^ 3) / (1 + w) ^ 6) z
      = rB 4 z := by
  have hlin : HasDerivAt (fun w : ℝ => w) (1 : ℝ) z := by simpa using hasDerivAt_pow 1 z
  have h2 : HasDerivAt (fun w : ℝ => w ^ 2) (2 * z) z := by
    simpa using hasDerivAt_pow 2 z
  have h3 : HasDerivAt (fun w : ℝ => w ^ 3) (3 * z ^ 2) z := by
    simpa using hasDerivAt_pow 3 z
  have hP : HasDerivAt (fun w : ℝ => 8 - 33 * w + 18 * w ^ 2 - w ^ 3)
      (-33 + 36 * z - 3 * z ^ 2) z := by
    have h0 := (((hasDerivAt_const z (8 : ℝ)).sub (hlin.const_mul 33)).add (h2.const_mul 18)).sub h3
    convert h0 using 1 <;> first | ring | (ext w; ring)
  refine (z_mul_deriv_rat (fun w : ℝ => 8 - 33 * w + 18 * w ^ 2 - w ^ 3)
    (-33 + 36 * z - 3 * z ^ 2) 5 z hP hz).trans ?_
  simp only [rB_four]
  ring_nf

/-! ## The iterates, level by level -/

/-- `DzdIter 1 fB = rB 1` away from the pole. -/
theorem dzdIter_fB_one (z : ℝ) (hz : 1 + z ≠ 0) :
    Work.Elliptic.DzdIter 1 fB z = rB 1 z :=
  z_mul_deriv_rB_zero z hz

/-- `DzdIter 2 fB = rB 2` away from the pole. -/
theorem dzdIter_fB_two (z : ℝ) (hz : 1 + z ≠ 0) :
    Work.Elliptic.DzdIter 2 fB z = rB 2 z := by
  have hzne : z ≠ -1 := by
    intro h
    exact hz (by linarith)
  have hev : Work.Elliptic.DzdIter 1 fB =ᶠ[𝓝 z] rB 1 :=
    (eventually_ne_nhds hzne).mono
      (fun w hw => dzdIter_fB_one w (by intro h; exact hw (by linarith)))
  have key : z * deriv (Work.Elliptic.DzdIter 1 fB) z = rB 2 z := by
    rw [hev.deriv_eq, rB_one]
    exact z_mul_deriv_rB_one z hz
  exact key

/-- `DzdIter 3 fB = rB 3` away from the pole. -/
theorem dzdIter_fB_three (z : ℝ) (hz : 1 + z ≠ 0) :
    Work.Elliptic.DzdIter 3 fB z = rB 3 z := by
  have hzne : z ≠ -1 := by
    intro h
    exact hz (by linarith)
  have hev : Work.Elliptic.DzdIter 2 fB =ᶠ[𝓝 z] rB 2 :=
    (eventually_ne_nhds hzne).mono
      (fun w hw => dzdIter_fB_two w (by intro h; exact hw (by linarith)))
  have key : z * deriv (Work.Elliptic.DzdIter 2 fB) z = rB 3 z := by
    rw [hev.deriv_eq, rB_two]
    exact z_mul_deriv_rB_two z hz
  exact key

/-- `DzdIter 4 fB = rB 4` away from the pole. -/
theorem dzdIter_fB_four (z : ℝ) (hz : 1 + z ≠ 0) :
    Work.Elliptic.DzdIter 4 fB z = rB 4 z := by
  have hzne : z ≠ -1 := by
    intro h
    exact hz (by linarith)
  have hev : Work.Elliptic.DzdIter 3 fB =ᶠ[𝓝 z] rB 3 :=
    (eventually_ne_nhds hzne).mono
      (fun w hw => dzdIter_fB_three w (by intro h; exact hw (by linarith)))
  have key : z * deriv (Work.Elliptic.DzdIter 3 fB) z = rB 4 z := by
    rw [hev.deriv_eq, rB_three]
    exact z_mul_deriv_rB_three z hz
  exact key

/-! ## The target -/

theorem rB_iter : ∀ j ≤ 4, ∀ z ∈ Set.Ioi (0 : ℝ),
    Work.Elliptic.DzdIter j (fun z : ℝ => z ^ 2 / (1 + z) ^ 3) z = rB j z := by
  intro j hj z hz
  have hz1 : 1 + z ≠ 0 := by
    have hzpos : (0 : ℝ) < z := hz
    intro h
    linarith
  interval_cases j
  · rfl
  · exact dzdIter_fB_one z hz1
  · exact dzdIter_fB_two z hz1
  · exact dzdIter_fB_three z hz1
  · exact dzdIter_fB_four z hz1

end Work.FTS.CoercivityFix.Transfer.E2pkg
end
end
-- ===== merged: Submission.Work.FTS.EllExist.Honesty.radGreen_l2_far =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open MeasureTheory Set
open scoped Real Topology

namespace Work.FTS.EllExist.Honesty

/-- On `[1, ∞)` the weight `w z = (1+z)^2 / z^2` of `Work.Spaces.w` satisfies
`w z ^ 2 ≤ 16` (indeed `w z ≤ (1 + 1/z)^2 ≤ 4`). -/
lemma w_sq_le_sixteen_of_one_le {z : ℝ} (hz : 1 ≤ z) : (Work.Spaces.w z) ^ 2 ≤ 16 := by
  have hz0 : 0 < z := by linarith
  have hw0 : 0 ≤ Work.Spaces.w z := by
    rw [Work.Spaces.w]; positivity
  have hw4 : Work.Spaces.w z ≤ 4 := by
    rw [Work.Spaces.w, div_le_iff₀ (by positivity : (0 : ℝ) < z ^ 2)]
    nlinarith [mul_nonpos_of_nonpos_of_nonneg (show 1 - z ≤ 0 by linarith)
      (show 0 ≤ 1 + 3 * z by linarith)]
  have h := pow_le_pow_left₀ hw0 hw4 2
  norm_num at h
  exact h


-- The **far-field** half of the weighted `L²`-honesty of the mode-`m` Green function
-- `Work.FTS.PhiStar.Radial.radGreen α m c` (decaying solution of the mode-`m` radial Euler
-- equation `-α²z²a'' - α(5+α)z a' + λ_m a = c`, λ_m = 2m(2m+5)).  Companion of
-- `FTS/EllExist/Honesty/radGreen_l2_near_zero` (the `z → 0` half); together they give the full
-- `∫_{Iz} (radGreen α m c)² w² < ∞` that discharges the one-dimensional hypotheses `hza` of
-- `psiTrunc_hkMem_fts`/`psiTrunc_hkMem_third_slot`.
--
-- ROUTE (`s⁻ = -(2m+5)/α ≤ -20`, `s⁺ = 2m/α ≥ 8`, `K = 1/(α(4m+5))`; `w z = (1+z)²/z²`, so
-- `w(z)² = (1+1/z)⁴ ≤ 16` for `z ≥ 1`).  Write `radGreen = K(G₁ + G₂)` with
-- `G₁(z) = z^{s⁻}∫_0^zc t^{-1-s⁻}dt`, `G₂(z) = z^{s⁺}∫_z^∞c t^{-1-s⁺}dt`.
-- * `G₂`: `|G₂(z)| ≤ z^{s⁺}·M∫_z^∞t^{-s⁺-2}t^{-1-s⁺}dt = M z^{-s⁺-2}/(2s⁺+2)`, so
--   `G₂(z)² ≤ C z^{-2s⁺-4}` with `2s⁺+4 ≥ 20`.
-- * `G₁`: for `z ≥ 1` split `∫_0^z = ∫_0^1 + ∫_1^z` (`integral_add_adjacent_intervals`); on
--   `(1,z)` use `|c t| ≤ M t^{-s⁺-2}` and `-1-s⁻ = (2m+5)/α - 1` to get
--   `|∫_1^zc t^{-1-s⁻}dt| ≤ M∫_1^z t^{-s⁺-s⁻-3}dt ≤ M/(s⁺+s⁻+2)` (bounded); the `∫_0^1` piece is
--   bounded when `t ↦ c t·t^{-1-s⁻}` is interval-integrable on `[0,1]` (continuity gives it when
--   `c` is bounded there; otherwise Lean's `integral` is the junk value `0`, so one must case-split
--   on `IntervalIntegrable`).  So `|G₁(z)| ≤ C z^{s⁻}` **up to** the extra decaying contribution
--   `M z^{-s⁺-2}/(s⁺+s⁻+2)` of the `(1,z)` piece; both `z^{2s⁻}` (`≤ z^{-56}`) and `z^{-2s⁺-4}`
--   are integrable against `w² ≤ 16` on `(1,∞)`.  Use `(G₁+G₂)² ≤ 2G₁² + 2G₂²`.-
--
-- PROOF.  The four far-field ingredients are separate lemmas in this directory:
-- * `Work.FTS.EllExist.Honesty.G1_far_bound`, `G1_far_measurable` — the `z^{s⁻}` term,
--   `|G1 α m c z| ≤ A z^{s⁻} + B z^{-s⁺-2}` on `Ioi 1` with `A, B ≥ 0` (case-split on whether
--   `t ↦ c t t^{s⁻-1}` is integrable on `(0,1]`; when it is not, `G1` vanishes on `Ioi 1` by
--   `intervalIntegral.integral_undef`), and measurability of `G1` on `Ioi 1`;
-- * `Work.FTS.EllExist.Honesty.G2_far_bound`, `G2_far_measurable` — the `z^{s⁺}` term,
--   `|G2 α m c z| ≤ (M/(2s⁺+2)) z^{-s⁺-2}` on `Ioi 1`, and measurability of `G2` on `Ioi 1`.
-- Assembly (`radGreen_l2_far_assembly` below): `|radGreen|² w² = K² (G₁+G₂)² w²`, the pointwise
-- bound `|G₁+G₂| ≤ A z^{s⁻} + (B + M/(2s⁺+2)) z^{-s⁺-2}` gives
-- `(G₁+G₂)² ≤ 2(A² + (B + M/(2s⁺+2))²) z^{-2s⁺-4}` since `2s⁻ ≤ -2s⁺-4` (i.e. `s⁺ - s⁻ = 5/α ≥ 2`),
-- and `w² ≤ 16`; so `radGreen² w²` is dominated by a constant multiple of the integrable
-- `z^{-2s⁺-4}` (`2s⁺+4 ≥ 20 > 1`).  Measurability of `radGreen² w²` follows from that of `G₁`, `G₂`
-- and continuity of `w`.  Then `Integrable.mono'` finishes.


end Work.FTS.EllExist.Honesty
end
end
-- ===== merged: Submission.Work.FTS.EllSol.EllPkgAux.KernelAux =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllSol.EllPkgAux

set_option autoImplicit false
set_option maxHeartbeats 1000000

open Work.FTS.EllSol.PkgK5.K5c

local notation "Iθ" => Work.Spaces.Iθ
local notation "σθ" => Work.FTS.EllipticEst.thEta

theorem restrict_Iθ_eq_restrict_Ioo :
    volume.restrict Iθ = volume.restrict (Set.Ioo 0 (Real.pi / 2)) := by
  refine MeasureTheory.Measure.restrict_congr_set ?_
  show Set.Icc (0 : ℝ) (Real.pi / 2) =ᵐ[volume] Set.Ioo (0 : ℝ) (Real.pi / 2)
  exact MeasureTheory.Ioo_ae_eq_Icc.symm

theorem thEta_pos_of_mem_Ioo {s : ℝ} (hs : s ∈ Set.Ioo 0 (Real.pi / 2)) : 0 < σθ s := by
  have h : 0 < Real.sin (2 * s) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith [hs.1]) (by linarith [hs.2, Real.pi_pos])
  simpa only [Work.FTS.EllipticEst.thEta] using
    Real.rpow_pos_of_pos h (-(Work.Spaces.eta))

theorem one_le_thEta_of_mem_Ioo {s : ℝ} (hs : s ∈ Set.Ioo 0 (Real.pi / 2)) : 1 ≤ σθ s := by
  have hpos : 0 < Real.sin (2 * s) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith [hs.1]) (by linarith [hs.2, Real.pi_pos])
  have hle : Real.sin (2 * s) ≤ 1 := Real.sin_le_one _
  have hne : -(Work.Spaces.eta) ≤ 0 := by rw [Work.Spaces.eta]; norm_num
  simpa only [Work.FTS.EllipticEst.thEta] using
    Real.one_le_rpow_of_pos_of_le_one_of_nonpos hpos hle hne

/-- **Domination criterion.**  A nonnegative a.e.-strongly-measurable function dominated a.e. by an
integrable nonnegative function is integrable.  (This is `Integrable.mono'` routed through the
Lebesgue integral, which avoids the expensive second-order unification of `mono'`.) -/
theorem integrable_of_le {f h : ℝ → ℝ}
    (hf : AEStronglyMeasurable f (volume.restrict Iθ))
    (hfnn : 0 ≤ᵐ[volume.restrict Iθ] f) (hh : Integrable h (volume.restrict Iθ))
    (hh0 : 0 ≤ᵐ[volume.restrict Iθ] h) (hle : f ≤ᵐ[volume.restrict Iθ] h) :
    Integrable f (volume.restrict Iθ) := by
  refine ⟨hf, ?_⟩
  rw [MeasureTheory.hasFiniteIntegral_iff_ofReal hfnn]
  calc ∫⁻ s in Iθ, ENNReal.ofReal (f s)
      ≤ ∫⁻ s in Iθ, ENNReal.ofReal (h s) := by
        refine MeasureTheory.lintegral_mono_ae ?_
        filter_upwards [hle] with s hs
        exact ENNReal.ofReal_le_ofReal hs
    _ = ENNReal.ofReal (∫ s in Iθ, h s) :=
        (MeasureTheory.ofReal_integral_eq_lintegral_ofReal hh hh0).symm
    _ < ⊤ := ENNReal.ofReal_lt_top

theorem ae_le_of_forall_mem_Ioo {f h' : ℝ → ℝ}
    (hh : ∀ s ∈ Set.Ioo 0 (Real.pi / 2), f s ≤ h' s) : f ≤ᵐ[volume.restrict Iθ] h' := by
  have hμ : volume.restrict Iθ = volume.restrict (Set.Ioo 0 (Real.pi / 2)) :=
    restrict_Iθ_eq_restrict_Ioo
  rw [hμ]
  exact MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioo hh

theorem aesm_sq_of_integrableOn {g : ℝ → ℝ}
    (hg : IntegrableOn (fun s : ℝ => g s ^ 2 * σθ s) Iθ) :
    AEStronglyMeasurable (fun s : ℝ => g s ^ 2) (volume.restrict Iθ) := by
  have haeth : AEMeasurable σθ (volume.restrict Iθ) :=
    (Work.FTS.EllipticEst.integrableOn_thEta.1).aemeasurable
  have hinv : AEMeasurable (fun s : ℝ => (σθ s)⁻¹) (volume.restrict Iθ) := haeth.inv
  have hne : ∀ᵐ s ∂(volume.restrict Iθ), σθ s ≠ 0 := by
    have h1 : ∀ᵐ s ∂(volume.restrict (Set.Ioo 0 (Real.pi / 2))), σθ s ≠ 0 :=
      MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioo
        (fun s hs => ne_of_gt (thEta_pos_of_mem_Ioo hs))
    have hμ : volume.restrict Iθ = volume.restrict (Set.Ioo 0 (Real.pi / 2)) :=
      restrict_Iθ_eq_restrict_Ioo
    rw [hμ]
    exact h1
  have hcongr : (fun s : ℝ => g s ^ 2)
      =ᵐ[volume.restrict Iθ] (fun s : ℝ => (g s ^ 2 * σθ s) * (σθ s)⁻¹) := by
    filter_upwards [hne] with s hs
    rw [mul_assoc, mul_inv_cancel₀ hs, mul_one]
  exact ((hg.1.aemeasurable.mul hinv).congr hcongr.symm).aestronglyMeasurable

theorem integrableOn_sq_of_integrableOn {g : ℝ → ℝ}
    (hg : IntegrableOn (fun s : ℝ => g s ^ 2 * σθ s) Iθ) :
    IntegrableOn (fun s : ℝ => g s ^ 2) Iθ := by
  refine integrable_of_le (aesm_sq_of_integrableOn hg)
    (Filter.Eventually.of_forall (fun s => sq_nonneg (g s))) hg ?_ ?_
  · exact MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc
      (fun s hs => mul_nonneg (sq_nonneg _) (Work.FTS.EllipticEst.thEta_nonneg hs))
  · refine ae_le_of_forall_mem_Ioo (fun s hs => ?_)
    exact le_mul_of_one_le_right (sq_nonneg (g s)) (one_le_thEta_of_mem_Ioo hs)

theorem KJ_pointwise {g : ℝ → ℝ} {ε θ : ℝ} (hε : 0 < ε)
    (hg : IntegrableOn (fun s : ℝ => g s ^ 2 * σθ s) Iθ) (hθ : θ ∈ Iθ) :
    (∫ s in Iθ, KJ ε θ s * g s) ^ 2 ≤ 3 * ∫ s in Iθ, KJ ε θ s * g s ^ 2 := by
  have hg2aesm := aesm_sq_of_integrableOn hg
  have hGsm : AEStronglyMeasurable (fun s : ℝ => Real.sqrt (g s ^ 2)) (volume.restrict Iθ) :=
    Real.continuous_sqrt.comp_aestronglyMeasurable hg2aesm
  have hG2 : ∀ s : ℝ, Real.sqrt (g s ^ 2) ^ 2 = g s ^ 2 := fun s =>
    Real.sq_sqrt (sq_nonneg (g s))
  have hGabs : ∀ s : ℝ, Real.sqrt (g s ^ 2) = |g s| := fun s => Real.sqrt_sq_eq_abs (g s)
  have hKJint : IntegrableOn (fun s : ℝ => KJ ε θ s) Iθ := by
    have hc : Continuous (fun t : ℝ => sKer ε t) := Work.FTS.EllSol.K5cAux.continuous_sKer ε
    have h1 : Continuous (fun s : ℝ => sKer ε (θ - s)) :=
      hc.comp (continuous_const.sub continuous_id)
    have h2 : Continuous (fun s : ℝ => sKer ε (θ + s)) :=
      hc.comp (continuous_const.add continuous_id)
    have h3 : Continuous (fun s : ℝ => sKer ε (θ + s - Real.pi)) :=
      hc.comp ((continuous_const.add continuous_id).sub continuous_const)
    have hcont : Continuous (fun s : ℝ => KJ ε θ s) := by
      simp only [KJ]
      exact (h1.add h2).add h3
    have h := hcont.integrableOn_Icc (μ := volume) (a := (0 : ℝ)) (b := Real.pi / 2)
    simpa only [Work.Spaces.Iθ] using h
  have hKJsm : AEStronglyMeasurable (fun s : ℝ => KJ ε θ s) (volume.restrict Iθ) := hKJint.1
  have hKg2 : IntegrableOn (fun s : ℝ => KJ ε θ s * g s ^ 2) Iθ := by
    have hc : (0:ℝ) ≤ 3 * (ε * sMass)⁻¹ :=
      mul_nonneg (by norm_num) (inv_nonneg.mpr (mul_nonneg hε.le sMass_pos.le))
    refine integrable_of_le (hKJsm.mul hg2aesm)
      (Filter.Eventually.of_forall (fun s => mul_nonneg (KJ_nonneg hε θ s) (sq_nonneg (g s))))
      ((hg.const_mul (3 * (ε * sMass)⁻¹))) ?_ ?_
    · exact MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc (fun s hs =>
        mul_nonneg hc (mul_nonneg (sq_nonneg _) (Work.FTS.EllipticEst.thEta_nonneg hs)))
    · refine ae_le_of_forall_mem_Ioo (fun s hs => ?_)
      have h1 : KJ ε θ s ≤ 3 * (ε * sMass)⁻¹ := KJ_le hε θ s
      have h2 : 1 ≤ σθ s := one_le_thEta_of_mem_Ioo hs
      have h3 : 0 ≤ g s ^ 2 := sq_nonneg _
      calc KJ ε θ s * g s ^ 2 ≤ (3 * (ε * sMass)⁻¹) * g s ^ 2 :=
            mul_le_mul_of_nonneg_right h1 h3
        _ ≤ (3 * (ε * sMass)⁻¹) * (g s ^ 2 * σθ s) :=
            mul_le_mul_of_nonneg_left (le_mul_of_one_le_right h3 h2) hc
  have hKJGs : IntegrableOn (fun s : ℝ => KJ ε θ s * Real.sqrt (g s ^ 2) ^ 2) Iθ :=
    MeasureTheory.Integrable.congr hKg2
      (Filter.Eventually.of_forall (fun s => by
        show KJ ε θ s * g s ^ 2 = KJ ε θ s * Real.sqrt (g s ^ 2) ^ 2
        rw [hG2 s]))
  have hstep1 : |∫ s in Iθ, KJ ε θ s * g s|
      ≤ ∫ s in Iθ, KJ ε θ s * Real.sqrt (g s ^ 2) := by
    have h1 := MeasureTheory.norm_integral_le_integral_norm
      (μ := volume.restrict Iθ) (fun s : ℝ => KJ ε θ s * g s)
    rw [Real.norm_eq_abs] at h1
    refine h1.trans (le_of_eq ?_)
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun s => ?_))
    show ‖KJ ε θ s * g s‖ = KJ ε θ s * Real.sqrt (g s ^ 2)
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (KJ_nonneg hε θ s), hGabs]
  have hu_mem : MemLp (fun s : ℝ => Real.sqrt (KJ ε θ s)) 2 (volume.restrict Iθ) :=
    (MeasureTheory.memLp_two_iff_integrable_sq (f := fun s : ℝ => Real.sqrt (KJ ε θ s))
      (Real.continuous_sqrt.comp_aestronglyMeasurable hKJsm)).mpr
      (MeasureTheory.Integrable.congr hKJint (Filter.Eventually.of_forall (fun s => by
        show KJ ε θ s = Real.sqrt (KJ ε θ s) ^ 2
        rw [Real.sq_sqrt (KJ_nonneg hε θ s)])))
  have hG_mem : MemLp (fun s : ℝ => Real.sqrt (g s ^ 2)) 2 (volume.restrict Iθ) :=
    (MeasureTheory.memLp_two_iff_integrable_sq (f := fun s : ℝ => Real.sqrt (g s ^ 2))
      hGsm).mpr
      (MeasureTheory.Integrable.congr (integrableOn_sq_of_integrableOn hg)
        (Filter.Eventually.of_forall (fun s => by
          show g s ^ 2 = Real.sqrt (g s ^ 2) ^ 2
          rw [Real.sq_sqrt (sq_nonneg (g s))])))
  have hv_mem : MemLp (fun s : ℝ => Real.sqrt (KJ ε θ s) * Real.sqrt (g s ^ 2)) 2
      (volume.restrict Iθ) :=
    (MeasureTheory.memLp_two_iff_integrable_sq
      (f := fun s : ℝ => Real.sqrt (KJ ε θ s) * Real.sqrt (g s ^ 2))
      ((Real.continuous_sqrt.comp_aestronglyMeasurable hKJsm).mul hGsm)).mpr
      (MeasureTheory.Integrable.congr hKg2 (Filter.Eventually.of_forall (fun s => by
        show KJ ε θ s * g s ^ 2 = (Real.sqrt (KJ ε θ s) * Real.sqrt (g s ^ 2)) ^ 2
        rw [mul_pow, Real.sq_sqrt (KJ_nonneg hε θ s), Real.sq_sqrt (sq_nonneg (g s))])))
  have hcs : (∫ s in Iθ, Real.sqrt (KJ ε θ s) * (Real.sqrt (KJ ε θ s) * Real.sqrt (g s ^ 2))) ^ 2
      ≤ (∫ s in Iθ, Real.sqrt (KJ ε θ s) ^ 2)
        * (∫ s in Iθ, (Real.sqrt (KJ ε θ s) * Real.sqrt (g s ^ 2)) ^ 2) :=
    Work.Spaces.cs_integral (s := Iθ) hu_mem hv_mem
  have e1 : (∫ s in Iθ, Real.sqrt (KJ ε θ s) * (Real.sqrt (KJ ε θ s) * Real.sqrt (g s ^ 2)))
      = ∫ s in Iθ, KJ ε θ s * Real.sqrt (g s ^ 2) :=
    MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun s => by
      show Real.sqrt (KJ ε θ s) * (Real.sqrt (KJ ε θ s) * Real.sqrt (g s ^ 2))
        = KJ ε θ s * Real.sqrt (g s ^ 2)
      rw [← mul_assoc, ← sq, Real.sq_sqrt (KJ_nonneg hε θ s)]))
  have e2 : (∫ s in Iθ, Real.sqrt (KJ ε θ s) ^ 2) = ∫ s in Iθ, KJ ε θ s :=
    MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun s => by
      show Real.sqrt (KJ ε θ s) ^ 2 = KJ ε θ s
      rw [Real.sq_sqrt (KJ_nonneg hε θ s)]))
  have e3 : (∫ s in Iθ, (Real.sqrt (KJ ε θ s) * Real.sqrt (g s ^ 2)) ^ 2)
      = ∫ s in Iθ, KJ ε θ s * g s ^ 2 :=
    MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun s => by
      show (Real.sqrt (KJ ε θ s) * Real.sqrt (g s ^ 2)) ^ 2 = KJ ε θ s * g s ^ 2
      rw [mul_pow, Real.sq_sqrt (KJ_nonneg hε θ s), Real.sq_sqrt (sq_nonneg (g s))]))
  rw [e1, e2, e3] at hcs
  have hQnn : 0 ≤ ∫ s in Iθ, KJ ε θ s * Real.sqrt (g s ^ 2) :=
    MeasureTheory.integral_nonneg_of_ae
      (Filter.Eventually.of_forall (fun s =>
        mul_nonneg (KJ_nonneg hε θ s) (Real.sqrt_nonneg _)))
  have hPnn : 0 ≤ (∫ s in Iθ, KJ ε θ s * g s ^ 2) :=
    MeasureTheory.integral_nonneg_of_ae
      (Filter.Eventually.of_forall (fun s =>
        mul_nonneg (KJ_nonneg hε θ s) (sq_nonneg _)))
  have hmass : (∫ s in Iθ, KJ ε θ s) ≤ 3 := KJ_mass hε hθ
  have hArith : (∫ s in Iθ, KJ ε θ s * Real.sqrt (g s ^ 2)) ^ 2
      ≤ 3 * (∫ s in Iθ, KJ ε θ s * g s ^ 2) := by
    have h3 : (∫ s in Iθ, KJ ε θ s) * (∫ s in Iθ, KJ ε θ s * g s ^ 2)
        ≤ 3 * (∫ s in Iθ, KJ ε θ s * g s ^ 2) := by
      have h4 := mul_le_mul_of_nonneg_right hmass hPnn
      linarith
    linarith [hcs, h3]
  have hstep2 : (∫ s in Iθ, KJ ε θ s * g s) ^ 2
      ≤ (∫ s in Iθ, KJ ε θ s * Real.sqrt (g s ^ 2)) ^ 2 := by
    have h := abs_le.mp hstep1
    have h1 : 0 ≤ (∫ s in Iθ, KJ ε θ s * Real.sqrt (g s ^ 2))
        + (∫ s in Iθ, KJ ε θ s * g s) := by linarith [h.1]
    have h2 : 0 ≤ (∫ s in Iθ, KJ ε θ s * Real.sqrt (g s ^ 2))
        - (∫ s in Iθ, KJ ε θ s * g s) := by linarith [h.2]
    have h3 : 0 ≤ ((∫ s in Iθ, KJ ε θ s * Real.sqrt (g s ^ 2))
          - (∫ s in Iθ, KJ ε θ s * g s))
        * ((∫ s in Iθ, KJ ε θ s * Real.sqrt (g s ^ 2))
          + (∫ s in Iθ, KJ ε θ s * g s)) :=
      mul_nonneg h2 h1
    have h4 : ((∫ s in Iθ, KJ ε θ s * Real.sqrt (g s ^ 2))
          - (∫ s in Iθ, KJ ε θ s * g s))
        * ((∫ s in Iθ, KJ ε θ s * Real.sqrt (g s ^ 2))
          + (∫ s in Iθ, KJ ε θ s * g s))
        = (∫ s in Iθ, KJ ε θ s * Real.sqrt (g s ^ 2)) ^ 2
          - (∫ s in Iθ, KJ ε θ s * g s) ^ 2 := by ring_nf
    linarith [h3, h4]
  linarith [hstep2, hArith]

end Work.FTS.EllSol.EllPkgAux
end
end
-- ===== merged: Submission.Work.FTS.EllSol.EllPkgAux.kernelSwap =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllSol.EllPkgAux

open MeasureTheory Filter


/-- The double integrand of `kernelSwap` is integrable on the product `Iθ × Iθ`. -/
theorem integrable_uncurry_kernel {g : ℝ → ℝ} {ε : ℝ} (hε : 0 < ε)
    (hgi : MeasureTheory.IntegrableOn (fun s : ℝ => g s ^ 2) Work.Spaces.Iθ) :
    Integrable (Function.uncurry (fun θ s : ℝ =>
        Work.FTS.EllipticEst.thEta θ * (KJ ε θ s * g s ^ 2)))
      ((volume.restrict Work.Spaces.Iθ).prod (volume.restrict Work.Spaces.Iθ)) := by
  have hgi' : Integrable (fun s : ℝ => g s ^ 2) (volume.restrict Work.Spaces.Iθ) := hgi
  have hσ : Integrable (fun θ : ℝ => Work.FTS.EllipticEst.thEta θ)
      (volume.restrict Work.Spaces.Iθ) :=
    Work.FTS.EllipticEst.integrableOn_thEta.1
  -- the dominating function, a product of two integrable factors
  have hdom : Integrable (fun p : ℝ × ℝ =>
      (3 * (ε * Work.FTS.EllSol.PkgK5.K5c.sMass)⁻¹ * Work.FTS.EllipticEst.thEta p.1)
        * g p.2 ^ 2)
      ((volume.restrict Work.Spaces.Iθ).prod (volume.restrict Work.Spaces.Iθ)) :=
    (hσ.const_mul _).mul_prod hgi'
  -- almost everywhere strong measurability of the integrand
  have hmeas : AEStronglyMeasurable (fun p : ℝ × ℝ =>
      Work.FTS.EllipticEst.thEta p.1 * (KJ ε p.1 p.2 * g p.2 ^ 2))
      ((volume.restrict Work.Spaces.Iθ).prod (volume.restrict Work.Spaces.Iθ)) := by
    have h1 : AEStronglyMeasurable (fun p : ℝ × ℝ => Work.FTS.EllipticEst.thEta p.1)
        ((volume.restrict Work.Spaces.Iθ).prod (volume.restrict Work.Spaces.Iθ)) :=
      hσ.aestronglyMeasurable.comp_fst
    have h2 : AEStronglyMeasurable (fun p : ℝ × ℝ => KJ ε p.1 p.2)
        ((volume.restrict Work.Spaces.Iθ).prod (volume.restrict Work.Spaces.Iθ)) :=
      (continuous_KJ ε).aestronglyMeasurable
    have h3 : AEStronglyMeasurable (fun p : ℝ × ℝ => g p.2 ^ 2)
        ((volume.restrict Work.Spaces.Iθ).prod (volume.restrict Work.Spaces.Iθ)) :=
      hgi'.aestronglyMeasurable.comp_snd
    exact h1.mul (h2.mul h3)
  refine Integrable.mono' hdom hmeas ?_
  rw [MeasureTheory.Measure.prod_restrict]
  refine MeasureTheory.ae_restrict_of_forall_mem
    ((measurableSet_Icc : MeasurableSet (Set.Icc (0 : ℝ) (Real.pi / 2))).prod
      (measurableSet_Icc : MeasurableSet (Set.Icc (0 : ℝ) (Real.pi / 2)))) ?_
  intro p hp
  obtain ⟨hp1, hp2⟩ := hp
  have hσnn : 0 ≤ Work.FTS.EllipticEst.thEta p.1 :=
    Work.FTS.EllipticEst.thEta_nonneg hp1
  have hKJnn : 0 ≤ KJ ε p.1 p.2 := KJ_nonneg hε p.1 p.2
  have hKJle : KJ ε p.1 p.2 ≤ 3 * (ε * Work.FTS.EllSol.PkgK5.K5c.sMass)⁻¹ :=
    KJ_le hε p.1 p.2
  have hgnn : 0 ≤ g p.2 ^ 2 := sq_nonneg _
  rw [show Function.uncurry (fun θ s : ℝ =>
        Work.FTS.EllipticEst.thEta θ * (KJ ε θ s * g s ^ 2)) p
      = Work.FTS.EllipticEst.thEta p.1 * (KJ ε p.1 p.2 * g p.2 ^ 2) from rfl]
  rw [Real.norm_of_nonneg (mul_nonneg hσnn (mul_nonneg hKJnn hgnn))]
  calc Work.FTS.EllipticEst.thEta p.1 * (KJ ε p.1 p.2 * g p.2 ^ 2)
      ≤ Work.FTS.EllipticEst.thEta p.1
          * ((3 * (ε * Work.FTS.EllSol.PkgK5.K5c.sMass)⁻¹) * g p.2 ^ 2) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hKJle hgnn) hσnn
    _ = (3 * (ε * Work.FTS.EllSol.PkgK5.K5c.sMass)⁻¹
          * Work.FTS.EllipticEst.thEta p.1) * g p.2 ^ 2 := by
        ring

theorem kernelSwap {g : ℝ → ℝ} {ε : ℝ} (hε : 0 < ε)
    (hgi : MeasureTheory.IntegrableOn (fun s : ℝ => g s ^ 2) Work.Spaces.Iθ) :
    (∫ θ in Work.Spaces.Iθ, Work.FTS.EllipticEst.thEta θ *
        (∫ s in Work.Spaces.Iθ, Work.FTS.EllSol.EllPkgAux.KJ ε θ s * g s ^ 2))
      = ∫ s in Work.Spaces.Iθ, g s ^ 2 *
          (∫ θ in Work.Spaces.Iθ, Work.FTS.EllipticEst.thEta θ * Work.FTS.EllSol.EllPkgAux.KJ ε θ s)
    ∧ MeasureTheory.IntegrableOn
        (fun θ : ℝ => Work.FTS.EllipticEst.thEta θ *
          (∫ s in Work.Spaces.Iθ, Work.FTS.EllSol.EllPkgAux.KJ ε θ s * g s ^ 2))
        Work.Spaces.Iθ
    ∧ MeasureTheory.IntegrableOn
        (fun s : ℝ => g s ^ 2 *
          (∫ θ in Work.Spaces.Iθ, Work.FTS.EllipticEst.thEta θ * Work.FTS.EllSol.EllPkgAux.KJ ε θ s))
        Work.Spaces.Iθ := by
  have hInt := integrable_uncurry_kernel (g := g) hε hgi
  have hswap := integral_integral_swap hInt
  -- the two one-variable factorisations of the integrand
  have keyA : ∀ θ : ℝ, (∫ s in Work.Spaces.Iθ,
        Work.FTS.EllipticEst.thEta θ * (KJ ε θ s * g s ^ 2))
      = Work.FTS.EllipticEst.thEta θ * ∫ s in Work.Spaces.Iθ, KJ ε θ s * g s ^ 2 :=
    fun θ => integral_const_mul _ _
  have keyB : ∀ s : ℝ, (∫ θ in Work.Spaces.Iθ,
        Work.FTS.EllipticEst.thEta θ * (KJ ε θ s * g s ^ 2))
      = g s ^ 2 * (∫ θ in Work.Spaces.Iθ, Work.FTS.EllipticEst.thEta θ * KJ ε θ s) := by
    intro s
    have h1 : (∫ θ in Work.Spaces.Iθ,
          Work.FTS.EllipticEst.thEta θ * (KJ ε θ s * g s ^ 2))
        = ∫ θ in Work.Spaces.Iθ,
            (Work.FTS.EllipticEst.thEta θ * KJ ε θ s) * g s ^ 2 := by
      refine integral_congr_ae (Filter.Eventually.of_forall fun θ => ?_)
      ring
    rw [h1, integral_mul_const (g s ^ 2)
      (fun θ => Work.FTS.EllipticEst.thEta θ * KJ ε θ s)]
    exact mul_comm _ _
  refine ⟨?_, ?_, ?_⟩
  · calc (∫ θ in Work.Spaces.Iθ, Work.FTS.EllipticEst.thEta θ *
          (∫ s in Work.Spaces.Iθ, KJ ε θ s * g s ^ 2))
        = ∫ θ in Work.Spaces.Iθ, ∫ s in Work.Spaces.Iθ,
            Work.FTS.EllipticEst.thEta θ * (KJ ε θ s * g s ^ 2) := by
          refine integral_congr_ae (Filter.Eventually.of_forall fun θ => ?_)
          exact (keyA θ).symm
      _ = ∫ s in Work.Spaces.Iθ, ∫ θ in Work.Spaces.Iθ,
            Work.FTS.EllipticEst.thEta θ * (KJ ε θ s * g s ^ 2) := hswap
      _ = ∫ s in Work.Spaces.Iθ, g s ^ 2 *
            (∫ θ in Work.Spaces.Iθ, Work.FTS.EllipticEst.thEta θ * KJ ε θ s) := by
          refine integral_congr_ae (Filter.Eventually.of_forall fun s => ?_)
          exact keyB s
  · have h := hInt.integral_prod_left
    refine h.congr (Filter.Eventually.of_forall fun θ => ?_)
    exact keyA θ
  · have h := hInt.integral_prod_right
    refine h.congr (Filter.Eventually.of_forall fun s => ?_)
    exact keyB s

end Work.FTS.EllSol.EllPkgAux
end
-- ===== merged: Submission.Work.FTS.EllipticEst.Blocks.slice_d_bound =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.Blocks

open scoped Real Topology
open MeasureTheory Set Filter

/-! ## Two bookkeeping lemmas about the dominating function `slicePhi` -/




end Work.FTS.EllipticEst.Blocks
end
-- ===== merged: Submission.Work.FTS.EllipticEst.H2W.tendsto_subinterval_integral =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.H2W


end Work.FTS.EllipticEst.H2W
end
-- ===== merged: Submission.Work.FTS.EllipticEst.LevelOneAsm.ParsevalZIntAux =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology ENNReal
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.LevelOneAsm

local notation "Iθ" => Work.Spaces.Iθ
local notation "μz" => (volume.restrict (Set.Ioi 0) : Measure ℝ)
local notation "μθ" => (volume.restrict Iθ : Measure ℝ)



/-- The product measure used in the hypotheses of `parseval_zInt`, written as a product of the
two restricted Lebesgue measures. -/
theorem volume_restrict_prod_Ioi_Iθ :
    (volume.restrict (Set.prod (Set.Ioi 0) Iθ) : Measure (ℝ × ℝ)) = Measure.prod μz μθ := by
  rw [Measure.volume_eq_prod (α := ℝ) (β := ℝ), Measure.prod_restrict]
  congr 1


/-- The `z`-slices of `F` are a.e. strongly measurable on `Iθ`. -/
def SliceSM (F : ℝ → ℝ → ℝ) : Prop :=
  ∀ᵐ z ∂μz, AEStronglyMeasurable (fun θ => F z θ) μθ

/-- The `z`-slices of `F` are a.e. integrable against the weight `cos θ` on `Iθ`, for the square
of `F`. -/
def SliceSqInt (F : ℝ → ℝ → ℝ) : Prop :=
  ∀ᵐ z ∂μz, IntegrableOn (fun θ => F z θ ^ 2 * Real.cos θ) Iθ


theorem sliceSM_of_hyp {F : ℝ → ℝ → ℝ}
    (hm : AEStronglyMeasurable (Function.uncurry F)
      (volume.restrict (Set.prod (Set.Ioi 0) Iθ))) : SliceSM F := by
  rw [volume_restrict_prod_Ioi_Iθ] at hm
  exact hm.prodMk_left

theorem sliceSqInt_of_hyp {F : ℝ → ℝ → ℝ}
    (hi : IntegrableOn (fun p : ℝ × ℝ => (F p.1 p.2) ^ 2 * Real.cos p.2)
      (Set.prod (Set.Ioi 0) Iθ)) : SliceSqInt F := by
  rw [IntegrableOn] at hi
  rw [volume_restrict_prod_Ioi_Iθ] at hi
  filter_upwards [hi.prod_right_ae] with z hz
  exact hz




end Work.FTS.EllipticEst.LevelOneAsm
end
end
-- ===== merged: Submission.Work.FTS.EllipticEst.Prop.TraceLeftPieces.traceCore =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end
end
-- ===== merged: Submission.Work.FTS.EllipticEst.Prop.TraceValueRight =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The right-endpoint trace value, controlled by the two weighted energies

For `f` of class `C²` on `(0, π/2)` whose one-sided limit `F₁` at `(π/2)⁻` exists and whose
weighted `L²`-energies `A = ∫_{Iθ} f² · σ`, `B = ∫_{Iθ} (f'')² · σ` are finite
(`σ = thEta θ = sin(2θ)^{-η}`, `η = 99/100`), one has `F₁² ≤ 100 (A + √(A B))`.

The proof is the right-endpoint half of `EndpointValues.endpointValuesCore`.  The two-scale
estimate `EndpointValues.endpointParamRight` gives, at every scale `t ∈ (0, π/2)`,
`F₁² ≤ (2/3) t³ ∫ (f'')² + 72 t⁻¹ ∫ f²` for the *unweighted* integrals over `(0, π/2)`; the
one-dimensional optimisation `EndpointValues.endpointSqBound` turns this into
`F₁² ≤ 100 (X + √(X Y))` with `X = ∫ f²`, `Y = ∫ (f'')²`, and finally `σ ≥ 1` on `Iθ`
(`Work.EllipticEst.Core.one_le_thEta`) gives `X ≤ A`, `Y ≤ B`, hence the claim with `C = 100`.
-/

namespace Work.FTS.EllipticEst.Prop

open scoped Real Topology
open MeasureTheory Set Filter

set_option autoImplicit false


end Work.FTS.EllipticEst.Prop
end
-- ===== merged: Submission.Work.FTS.EllipticEst.TT.SliceIbpLightAux =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.TT

set_option autoImplicit false

/-! ## Trigonometric endpoint bounds -/

/-- `sin(2θ) ≤ 2θ` for `θ ≥ 0`. -/
lemma sin_two_le_two_mul {θ : ℝ} (hθ : 0 ≤ θ) : Real.sin (2 * θ) ≤ 2 * θ :=
  Real.sin_le (by linarith)

/-- Reflection symmetry: `sin(2θ) = sin(2(π/2 - θ))`. -/
lemma sin_two_eq_sin_two_sub (θ : ℝ) : Real.sin (2 * θ) = Real.sin (2 * (Real.pi / 2 - θ)) := by
  rw [show 2 * (Real.pi / 2 - θ) = Real.pi - 2 * θ by ring, Real.sin_pi_sub]

/-- Jordan's inequality in the form `(4/π)·θ ≤ sin(2θ)` for `θ ∈ [0, π/4]`. -/
lemma four_div_pi_mul_le_sin_two {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ Real.pi / 4) :
    (4 / Real.pi) * θ ≤ Real.sin (2 * θ) := by
  have h := Real.mul_le_sin (x := 2 * θ) (by linarith) (by linarith [Real.pi_pos])
  have h2 : 2 / Real.pi * (2 * θ) = (4 / Real.pi) * θ := by ring
  linarith [h, h2]

/-- Jordan's inequality at the right endpoint: `(4/π)(π/2 - θ) ≤ sin(2θ)` for
`θ ∈ [π/4, π/2]`. -/
lemma four_div_pi_mul_sub_le_sin_two {θ : ℝ} (hθ0 : Real.pi / 4 ≤ θ)
    (hθ1 : θ ≤ Real.pi / 2) :
    (4 / Real.pi) * (Real.pi / 2 - θ) ≤ Real.sin (2 * θ) := by
  rw [sin_two_eq_sin_two_sub]
  exact four_div_pi_mul_le_sin_two (by linarith [Real.pi_pos]) (by linarith)

/-- The combined endpoint lower bound `(4/π)·min θ (π/2-θ) ≤ sin(2θ)` on `Iθ`. -/
lemma four_div_pi_mul_min_le_sin_two {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) :
    (4 / Real.pi) * min θ (Real.pi / 2 - θ) ≤ Real.sin (2 * θ) := by
  rcases le_total θ (Real.pi / 4) with h | h
  · rw [min_eq_left (by linarith [Real.pi_pos])]
    exact four_div_pi_mul_le_sin_two hθ.1 h
  · rw [min_eq_right (by linarith [Real.pi_pos])]
    exact four_div_pi_mul_sub_le_sin_two h hθ.2

/-! ## The limits `x^r → 0`, `r > 0`, at `0⁺` and of `(π/2 - θ)^r` at `(π/2)⁻` -/

/-- `x^r → 0` as `x → 0` within `[0,∞)`, for `r > 0`. -/
lemma tendsto_rpow_nhdsIci_zero {r : ℝ} (hr : 0 < r) :
    Tendsto (fun x : ℝ => x ^ r) (nhdsWithin (0 : ℝ) (Ici 0)) (nhds 0) := by
  have hcont : ContinuousWithinAt (fun x : ℝ => x ^ r) (Ici (0 : ℝ)) 0 :=
    ContinuousWithinAt.rpow continuousWithinAt_id continuousWithinAt_const (Or.inr hr)
  have h0 : (0 : ℝ) ^ r = 0 := Real.zero_rpow (ne_of_gt hr)
  have h := hcont.tendsto
  rwa [h0] at h

/-- `x^r → 0` as `x → 0⁺`, for `r > 0`. -/
lemma tendsto_rpow_nhdsGT_zero {r : ℝ} (hr : 0 < r) :
    Tendsto (fun x : ℝ => x ^ r) (nhdsWithin (0 : ℝ) (Ioi 0)) (nhds 0) :=
  (tendsto_rpow_nhdsIci_zero hr).mono_left (nhdsWithin_mono 0 Ioi_subset_Ici_self)



/-! ## Generic squeeze lemmas -/



/-! ## The measure identification and the integrability criterion -/

/-- `volume.restrict (Ioo 0 (π/2)) = volume.restrict Iθ`: the two sets differ by the null
set `{0, π/2}`. -/
lemma restrict_Ioo_eq_restrict_Iθ :
    volume.restrict (Set.Ioo (0 : ℝ) (Real.pi / 2)) = volume.restrict Work.Spaces.Iθ := by
  rw [Work.Spaces.Iθ]
  refine MeasureTheory.Measure.restrict_congr_set ?_
  rw [MeasureTheory.ae_eq_set]
  refine ⟨?_, ?_⟩
  · refine measure_mono_null ?_ measure_empty
    intro x hx
    exact absurd ⟨le_of_lt hx.1.1, le_of_lt hx.1.2⟩ hx.2
  · have hsub : Set.Icc (0 : ℝ) (Real.pi / 2) \ Set.Ioo (0 : ℝ) (Real.pi / 2)
        ⊆ ({0, Real.pi / 2} : Set ℝ) := by
      intro x hx
      rw [Set.mem_sdiff] at hx
      rw [Set.mem_Icc] at hx
      rw [Set.mem_Ioo] at hx
      rw [Set.mem_insert_iff, Set.mem_singleton_iff]
      rcases lt_or_eq_of_le hx.1.1 with h | h
      · rcases lt_or_eq_of_le hx.1.2 with h2 | h2
        · exact absurd ⟨h, h2⟩ hx.2
        · exact Or.inr h2
      · exact Or.inl h.symm
    refine measure_mono_null hsub ?_
    exact Set.Finite.measure_zero (by simp) volume

/-- Almost every point of `Iθ` lies in the open interval. -/
lemma ae_mem_Ioo_of_Iθ :
    ∀ᵐ θ ∂(volume.restrict Work.Spaces.Iθ), θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) := by
  rw [← restrict_Ioo_eq_restrict_Iθ]
  exact MeasureTheory.ae_restrict_mem measurableSet_Ioo


end Work.FTS.EllipticEst.TT
end
end
-- ===== merged: Submission.Work.FTS.EllipticEst.ZCuts.zHardy_compact =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.ZCuts

open scoped Real Topology Interval
open MeasureTheory Set Filter

noncomputable section

/-! ## Auxiliary facts about the weight `w` and the function `zA`

These are the ingredients of the compactly supported weighted Hardy inequality
`zHardy_compact`: smoothness of `w` and of `zA` on `(0,∞)`, and the fact that a
function vanishing on a neighbourhood of a point has vanishing derivative there. -/





end

end Work.FTS.EllipticEst.ZCuts
end
