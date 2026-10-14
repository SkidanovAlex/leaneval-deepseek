import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Analysis.Calculus.Deriv.ZPow
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.RCLike.Basic
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Tactic.IntervalCases
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.FTS.EllipticEst.integrableOn_HkIntegrand_terms
import Submission.Work.FTS.StrongPersist.SupZ.swap_abs
import Submission.Work.Spaces.DerivLikeBasic
import Submission.Work.Spaces.HkSq_terms
import Submission.Work.Spaces.continuousOn_HkIntegrand_Qd
import Submission.Work.Spaces.dthU_Gam
import Submission.Work.Spaces.factor_bound
import Submission.Work.Spaces.mixed_mul_le
import Submission.Work.Spaces.pz_DthIter_mul_eq
import Submission.Work.Spaces.scoef_sum_shift
import Submission.Work.Spaces.sin_two_rpow
import Submission.Work.Stability.CutFactorFderivZero
import Submission.Work.Stability.Cutoff
-- ===== merged: Submission.Work.FTS.GalBasis.cc.Defs =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.GalBasis.cc

set_option autoImplicit false

/-! ## The objects -/

/-- `Sw θ = sin(2θ)^{η/2}`: the angular factor of the weighted datum
`g = h·w/Sw`, whose square is the `D_z^0`-summand of `HkIntegrand`. -/
def Sw (θ : ℝ) : ℝ := Real.sin (2 * θ) ^ (Work.Spaces.eta / 2)

/-- `Wlam s = s/(1+s)²`: the sublinear radial weight (equal to `1/(s·w s)` for `s ≠ 0`). -/
def Wlam (s : ℝ) : ℝ := s / (1 + s) ^ 2

/-- The weighted datum `g = h·w/Sw` of the Cauchy–Schwarz argument. -/
def Gaz (h : ℝ → ℝ → ℝ) (z θ : ℝ) : ℝ := h z θ * (Work.Spaces.w z / Sw θ)

/-- `BK = √(∫_θ (K(θ)·Sw θ)² dθ)`, the (finite, `α`-free) `L²`-norm of the angular profile
`K·Sw`. -/
def BK : ℝ := Real.sqrt (∫ θ in Work.Spaces.Iθ, (Work.Spaces.K θ * Sw θ) ^ 2)

/-- `W2 = ∫_{(0,∞)} Wlam² `, the (finite) `L²`-norm of the radial weight. -/
def W2 : ℝ := ∫ s in Set.Ioi 0, Wlam s ^ 2

@[simp] lemma Sw_apply (θ : ℝ) : Sw θ = Real.sin (2 * θ) ^ (Work.Spaces.eta / 2) := rfl
@[simp] lemma Wlam_apply (s : ℝ) : Wlam s = s / (1 + s) ^ 2 := rfl
@[simp] lemma Gaz_apply (h : ℝ → ℝ → ℝ) (z θ : ℝ) :
    Gaz h z θ = h z θ * (Work.Spaces.w z / Sw θ) := rfl

/-! ## Elementary facts about `Sw` -/

lemma two_mul_mem_Icc_pi {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) : 2 * θ ∈ Set.Icc 0 π := by
  have h : θ ≤ π / 2 := hθ.2
  have h0 : 0 ≤ θ := hθ.1
  exact ⟨by linarith, by linarith [Real.pi_pos]⟩

/-- On the angular interval, `sin(2θ) ≥ 0`. -/
lemma sin_two_nonneg_of_mem_Iθ {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) : 0 ≤ Real.sin (2 * θ) :=
  Real.sin_nonneg_of_mem_Icc (two_mul_mem_Icc_pi hθ)

/-- `Sw ≥ 0` on the angular interval. -/
lemma Sw_nonneg_of_mem_Iθ {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) : 0 ≤ Sw θ :=
  Real.rpow_nonneg (sin_two_nonneg_of_mem_Iθ hθ) _


/-- `Sw` is continuous (globally: it is `Real.continuous_rpow_const` composed with `sin`). -/
lemma continuous_sw : Continuous Sw :=
  (Real.continuous_rpow_const (by norm_num [Work.Spaces.eta] : (0:ℝ) ≤ Work.Spaces.eta / 2)).comp
    (Real.continuous_sin.comp (continuous_const.mul continuous_id))

/-- `K(θ) = 3 sin θ cos²θ ≥ 0` on the angular interval. -/
lemma K_nonneg_of_mem_Iθ {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) : 0 ≤ Work.Spaces.K θ := by
  have hs : 0 ≤ Real.sin θ :=
    Real.sin_nonneg_of_mem_Icc ⟨hθ.1, by linarith [hθ.2, Real.pi_pos]⟩
  have hc : 0 ≤ Real.cos θ :=
    Real.cos_nonneg_of_mem_Icc ⟨by linarith [Real.pi_pos, hθ.1], by linarith [hθ.2]⟩
  rw [Work.Spaces.K]
  positivity

/-- `K(θ) ≤ 3` on the angular interval. -/
lemma K_le_three_of_mem_Iθ {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) : Work.Spaces.K θ ≤ 3 := by
  have hs : Real.sin θ ≤ 1 := Real.sin_le_one θ
  have hc : Real.cos θ ^ 2 ≤ 1 := by
    have h := Real.cos_sq_le_one θ
    linarith
  have hs0 : 0 ≤ Real.sin θ :=
    Real.sin_nonneg_of_mem_Icc ⟨hθ.1, by linarith [hθ.2, Real.pi_pos]⟩
  have hc0 : 0 ≤ Real.cos θ ^ 2 := sq_nonneg _
  rw [Work.Spaces.K]
  nlinarith

/-- Where `Sw` vanishes on the angular interval, so does `K`. -/
lemma sw_eq_zero_imp_K_eq_zero {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) (h : Sw θ = 0) :
    Work.Spaces.K θ = 0 := by
  have hsin := sin_two_nonneg_of_mem_Iθ hθ
  have hη : Work.Spaces.eta / 2 ≠ 0 := by norm_num [Work.Spaces.eta]
  have hzero : Real.sin (2 * θ) = 0 :=
    ((Real.rpow_eq_zero_iff_of_nonneg hsin).mp h).1
  rw [Real.sin_two_mul] at hzero
  have : Real.sin θ = 0 ∨ Real.cos θ = 0 := by
    rcases mul_eq_zero.mp hzero with h' | h'
    · exact Or.inl (by linarith [h'])
    · exact Or.inr h'
  rw [Work.Spaces.K]
  rcases this with h' | h' <;> simp [h']

/-! ## The weighted datum and the `ℋ⁴`-integrand -/

/-- The square of the weighted datum is the `D_z^0`-summand of the `ℋ⁴`-integrand. -/
lemma Gaz_sq_le_HkIntegrand (α : ℝ) (h : ℝ → ℝ → ℝ) (z θ : ℝ) :
    (Gaz h z θ) ^ 2 ≤ Work.Spaces.HkIntegrand α 4 h z θ := by
  simpa only [Gaz, Sw, Work.Spaces.DzIter_zero] using
    Work.Spaces.sq_le_HkIntegrand_z α 4 h z θ 0 (by norm_num)

/-- On the angular interval, `|Gaz|` is dominated by the square root of the `ℋ⁴`-integrand. -/
lemma abs_Gaz_le_sqrt_HkIntegrand (α : ℝ) (h : ℝ → ℝ → ℝ) (z θ : ℝ) :
    |Gaz h z θ| ≤ Real.sqrt (Work.Spaces.HkIntegrand α 4 h z θ) := by
  rw [← Real.sqrt_sq_eq_abs]
  exact Real.sqrt_le_sqrt (Gaz_sq_le_HkIntegrand α h z θ)

/-! ## Elementary facts about `Wlam` -/


lemma Wlam_nonneg {s : ℝ} (hs : 0 ≤ s) : 0 ≤ Wlam s := by
  rw [Wlam]
  exact div_nonneg hs (sq_nonneg _)



/-- `w s · Wlam s = 1/s` for `s > 0`: the radial weight is exactly what absorbs the `1/s` of
the `L₁₂`-density. -/
lemma w_mul_Wlam {s : ℝ} (hs : 0 < s) : Work.Spaces.w s * Wlam s = 1 / s := by
  rw [Wlam, Work.Spaces.w]
  field_simp

/-! ## The two constants -/

lemma BK_nonneg : 0 ≤ BK := Real.sqrt_nonneg _

lemma W2_nonneg : 0 ≤ W2 := integral_nonneg fun _ => sq_nonneg _

end Work.FTS.GalBasis.cc
end
end
-- ===== merged: Submission.Work.FTS.Galerkin.Basic =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.Galerkin

set_option autoImplicit false

/-! ## `slice` -/




/-- Two families with the same pointwise values have the same slices. -/
theorem slice_eq {g g' : Fam} (h : ∀ τ z θ, g z θ τ = g' z θ τ) (τ : ℝ) : slice g τ = slice g' τ :=
  funext fun z => funext fun θ => h τ z θ

/-- Pointwise values from a slice equality. -/
theorem val_of_slice_eq {g g' : Fam} (h : ∀ τ, slice g τ = slice g' τ) (τ z θ : ℝ) :
    g z θ τ = g' z θ τ := by
  have h1 := congrFun (congrFun (h τ) z) θ
  simpa [slice] using h1

/-- The family of the `τ`-slices of `F_* + g`, at `α`. -/
theorem Ftau_congr {α : ℝ} {g g' : Fam} (h : ∀ τ, slice g τ = slice g' τ) (τ : ℝ) :
    Construction.Ftau α g τ = Construction.Ftau α g' τ := by
  funext z θ
  have hv := val_of_slice_eq h τ z θ
  simp only [Construction.Ftau]
  rw [hv]

/-! ## The right hand side depends only on the slices -/

theorem muDyn_congr {α : ℝ} {Φ Φ' g g' : Fam} (hg : ∀ τ, slice g τ = slice g' τ)
    (hΦ : ∀ τ, slice Φ τ = slice Φ' τ) (τ : ℝ) : muDyn α Φ g τ = muDyn α Φ' g' τ := by
  have h3 : Construction.Ftau α g τ = Construction.Ftau α g' τ := Ftau_congr hg τ
  simp only [muDyn, h3, hg τ, hΦ τ]

theorem lamDyn_congr {α : ℝ} {Φ Φ' g g' : Fam} (hg : ∀ τ, slice g τ = slice g' τ)
    (hΦ : ∀ τ, slice Φ τ = slice Φ' τ) (τ : ℝ) : lamDyn α Φ g τ = lamDyn α Φ' g' τ := by
  have h1 : muDyn α Φ g τ = muDyn α Φ' g' τ := muDyn_congr hg hΦ τ
  simp only [lamDyn, h1]

theorem dynLin_congr {α : ℝ} {g g' : Fam} (hg : ∀ τ, slice g τ = slice g' τ) (τ : ℝ) :
    dynLin α g τ = dynLin α g' τ := by
  funext z θ
  simp only [dynLin, hg τ]

theorem dynRHS_congr {α : ℝ} {Φ Φ' g g' : Fam} (hg : ∀ τ, slice g τ = slice g' τ)
    (hΦ : ∀ τ, slice Φ τ = slice Φ' τ) (τ : ℝ) : dynRHS α Φ g τ = dynRHS α Φ' g' τ := by
  have h1 : muDyn α Φ g τ = muDyn α Φ' g' τ := muDyn_congr hg hΦ τ
  have h2 : lamDyn α Φ g τ = lamDyn α Φ' g' τ := lamDyn_congr hg hΦ τ
  have h3 : Construction.Ftau α g τ = Construction.Ftau α g' τ := Ftau_congr hg τ
  simp only [dynRHS, h1, h2, h3, hg τ, hΦ τ]







/-! ## The elliptic law -/


/-! ## Degenerate computations -/



end Work.FTS.Galerkin
end
end
-- ===== merged: Submission.Work.FTS.Galerkin.Hilbert.HkIntegrand_add_le =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology

namespace Work.FTS.Galerkin.Hilbert

/-- **Pointwise subadditivity of the `ℋ^k` integrand.**  For `f`, `g` smooth on an open
neighbourhood of the closed quadrant `[0,∞) × [0,π/2]`, the weighted `ℋ^k` integrand of
`f + g` is pointwise bounded by twice the sum of the integrands of `f` and `g` at every point
of the closed quadrant.

Intended proof: on `nbhU = (-1,∞) × (-1,π/2+1)` the iterated operators are additive,
`DzIter i (f+g) = DzIter i f + DzIter i g` and `mixed j i (f+g) = mixed j i f + mixed j i g`
(`Work.Coercivity.E2Mixed.DzIter_add_of_isOpen`, `...DthIter_add_of_isOpen`,
`...mixed_add_of_isOpen`, with `V = nbhU`); then each summand of the integrand satisfies
`(a + b)^2 ≤ 2 a^2 + 2 b^2`, and summing (including the `if`-filtered double sum, rewritten as
a sum over `((range (k+1)) ×ˢ (range (k+1))).filter (fun p => 1 ≤ p.1 ∧ p.1 + p.2 ≤ k)`)
gives the claim.  Every point of `Iz × Iθ` lies in `nbhU` (`Work.Spaces.mem_nbhU`). -/
theorem HkIntegrand_add_le {α : ℝ} {k : ℕ} {f g : Work.FTS.Galerkin.Fn}
    (hf : Work.Spaces.SmoothNbhd f) (hg : Work.Spaces.SmoothNbhd g) :
    ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ,
      Work.Spaces.HkIntegrand α k (fun z θ => f z θ + g z θ) z θ
        ≤ 2 * (Work.Spaces.HkIntegrand α k f z θ + Work.Spaces.HkIntegrand α k g z θ) := by
  intro z hz θ hθ
  -- every point of the closed quadrant lies in the open neighbourhood on which `SmoothNbhd` lives
  have hy : (z, θ) ∈ Work.Spaces.nbhU := Work.Spaces.mem_nbhU hz hθ
  -- the iterated operators are additive at `(z,θ)`
  have hDz : ∀ i : ℕ, Work.Spaces.DzIter i (fun z θ => f z θ + g z θ) z θ
      = Work.Spaces.DzIter i f z θ + Work.Spaces.DzIter i g z θ := fun i =>
    Work.Coercivity.E2Mixed.DzIter_add_of_isOpen Work.Spaces.isOpen_nbhU hf hg i hy
  have hMixed : ∀ j i : ℕ, Work.Spaces.mixed j i (fun z θ => f z θ + g z θ) z θ
      = Work.Spaces.mixed j i f z θ + Work.Spaces.mixed j i g z θ := fun j i =>
    Work.Coercivity.E2Mixed.mixed_add_of_isOpen Work.Spaces.isOpen_nbhU hf hg j i hy
  simp only [Work.Spaces.HkIntegrand]
  -- the pure `D_z` sum
  have hZ : (∑ i ∈ Finset.range (k + 1),
      (Work.Spaces.DzIter i (fun z θ => f z θ + g z θ) z θ
        * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2)
      ≤ 2 * (∑ i ∈ Finset.range (k + 1),
          (Work.Spaces.DzIter i f z θ
            * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2)
        + 2 * (∑ i ∈ Finset.range (k + 1),
          (Work.Spaces.DzIter i g z θ
            * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2) := by
    calc (∑ i ∈ Finset.range (k + 1),
          (Work.Spaces.DzIter i (fun z θ => f z θ + g z θ) z θ
            * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2)
        ≤ ∑ i ∈ Finset.range (k + 1),
            (2 * (Work.Spaces.DzIter i f z θ
                * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2
              + 2 * (Work.Spaces.DzIter i g z θ
                * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2) := by
          apply Finset.sum_le_sum
          intro i hi
          rw [hDz i]
          nlinarith [sq_nonneg (Work.Spaces.DzIter i f z θ
              * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))
            - Work.Spaces.DzIter i g z θ
              * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2)))]
      _ = 2 * (∑ i ∈ Finset.range (k + 1),
            (Work.Spaces.DzIter i f z θ
              * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2)
          + 2 * (∑ i ∈ Finset.range (k + 1),
            (Work.Spaces.DzIter i g z θ
              * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2) := by
          rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]
  -- the `if`-filtered mixed double sum, bounded summand by summand
  have hM : (∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1),
        if 1 ≤ i ∧ i + j ≤ k then
          (Work.Spaces.mixed j i (fun z θ => f z θ + g z θ) z θ * Work.Spaces.Wt α z θ) ^ 2
        else 0)
      ≤ 2 * (∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1),
          if 1 ≤ i ∧ i + j ≤ k then
            (Work.Spaces.mixed j i f z θ * Work.Spaces.Wt α z θ) ^ 2 else 0)
        + 2 * (∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1),
          if 1 ≤ i ∧ i + j ≤ k then
            (Work.Spaces.mixed j i g z θ * Work.Spaces.Wt α z θ) ^ 2 else 0) := by
    calc (∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1),
          if 1 ≤ i ∧ i + j ≤ k then
            (Work.Spaces.mixed j i (fun z θ => f z θ + g z θ) z θ * Work.Spaces.Wt α z θ) ^ 2
          else 0)
        ≤ ∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1),
            (2 * (if 1 ≤ i ∧ i + j ≤ k then
                (Work.Spaces.mixed j i f z θ * Work.Spaces.Wt α z θ) ^ 2 else 0)
              + 2 * (if 1 ≤ i ∧ i + j ≤ k then
                (Work.Spaces.mixed j i g z θ * Work.Spaces.Wt α z θ) ^ 2 else 0)) := by
          apply Finset.sum_le_sum; intro i hi
          apply Finset.sum_le_sum; intro j hj
          by_cases hc : 1 ≤ i ∧ i + j ≤ k
          · rw [ite_eq_left hc, ite_eq_left hc, ite_eq_left hc, hMixed j i]
            nlinarith [sq_nonneg (Work.Spaces.mixed j i f z θ * Work.Spaces.Wt α z θ
              - Work.Spaces.mixed j i g z θ * Work.Spaces.Wt α z θ)]
          · rw [ite_eq_right hc, ite_eq_right hc, ite_eq_right hc]
            norm_num
      _ = 2 * (∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1),
            if 1 ≤ i ∧ i + j ≤ k then
              (Work.Spaces.mixed j i f z θ * Work.Spaces.Wt α z θ) ^ 2 else 0)
          + 2 * (∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1),
            if 1 ≤ i ∧ i + j ≤ k then
              (Work.Spaces.mixed j i g z θ * Work.Spaces.Wt α z θ) ^ 2 else 0) := by
          simp only [Finset.sum_add_distrib, Finset.mul_sum]
  linarith [hZ, hM]

end Work.FTS.Galerkin.Hilbert
end
end
-- ===== merged: Submission.Work.FTS.LocData.BumpZ_contDiff =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.LocData

/-- The radial factor `bumpZ z = χ(4z - 5)` of the bump is `C^∞` on all of `ℝ`: it is the
composition of the globally `C^∞` cut-off `χ` (`Work.Stability.chi_contDiff`) with the affine
map `z ↦ 4z - 5`. -/
theorem BumpZ_contDiff : ContDiff ℝ (⊤ : ℕ∞) Work.FTS.LocData.bumpZ := by
  unfold bumpZ
  exact Work.Stability.chi_contDiff.comp
    ((contDiff_const.mul contDiff_id).sub contDiff_const)

end Work.FTS.LocData
end
-- ===== merged: Submission.Work.FTS.LocData.DthIter_Gam_abs_le =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.LocData

set_option autoImplicit false

/-! ## `DthIter` on functions of `θ` alone -/

/-- On a function of `θ` alone, the two-variable operator `D_θ` agrees with the
one-variable operator `Spaces.dthU`. -/
theorem DthIter_rad_eq (i : ℕ) (g : ℝ → ℝ) (z θ : ℝ) :
    Work.Spaces.DthIter i (fun _ θ' => g θ') z θ = Work.Spaces.dthU^[i] g θ := by
  have h : (fun (_ : ℝ) (θ : ℝ) => g θ) = (fun (z : ℝ) (θ : ℝ) => g θ * (1 : ℝ)) := by
    funext z θ; ring
  rw [h, Work.Spaces.DthIter_decomp]
  ring

/-! ## The polynomial majorant of `Tfun` -/

/-- The `j`-th coefficient polynomial of the angular jet of `Γ`, as a polynomial in
`v = cos 2θ`; the recursion is `Q_{j+1}(v) = -2(1 - v²)Q_j'(v) + α(v - 1/3)Q_j(v)`. -/
noncomputable def Qp : ℕ → ℝ → Polynomial ℝ
  | 0, _ => Polynomial.X - Polynomial.C (1 / 3)
  | (j + 1), α => Polynomial.C (-2) * (1 - Polynomial.X ^ 2) * (Qp j α).derivative
      + Polynomial.C α * (Polynomial.X - Polynomial.C (1 / 3)) * (Qp j α)

/-- One step of the recursion, evaluated. -/
theorem Qp_succ_eval (j : ℕ) (α v : ℝ) :
    (Qp (j + 1) α).eval v
      = -2 * (1 - v ^ 2) * (Qp j α).derivative.eval v + α * (v - 1 / 3) * (Qp j α).eval v := by
  rw [Qp]; simp

/-- The chain rule for `θ ↦ (Qp j α).eval (cos 2θ)`. -/
theorem deriv_Qp_cos (j : ℕ) (α θ : ℝ) :
    deriv (fun t : ℝ => (Qp j α).eval (Real.cos (2 * t))) θ
      = (Qp j α).derivative.eval (Real.cos (2 * θ)) * (-(2 * Real.sin (2 * θ))) := by
  rw [show (fun t : ℝ => (Qp j α).eval (Real.cos (2 * t)))
      = ((fun v : ℝ => (Qp j α).eval v) ∘ (fun t : ℝ => Real.cos (2 * t))) from rfl,
    deriv_comp]
  · rw [Polynomial.deriv]
    congr 1
    rw [show (fun t : ℝ => Real.cos (2 * t)) = (Real.cos ∘ (fun t : ℝ => 2 * t)) from rfl,
      deriv_comp]
    · rw [Real.deriv_cos]; simp; ring
    · exact Real.differentiableAt_cos
    · fun_prop
  · exact (Polynomial.hasDerivAt (Qp j α) _).differentiableAt
  · fun_prop

/-- **`Tfun j α` is the polynomial `Qp j α` evaluated at `v = cos 2θ`.** -/
theorem Tfun_eq_Qp (j : ℕ) (α : ℝ) :
    Work.Spaces.Tfun j α = fun θ => (Qp j α).eval (Real.cos (2 * θ)) := by
  induction j with
  | zero =>
      funext θ
      simp [Qp, Work.Spaces.qfun_apply]
  | succ j ih =>
      have hfun : (fun t : ℝ => Work.Spaces.Tfun j α t)
          = (fun t : ℝ => (Qp j α).eval (Real.cos (2 * t))) := by
        rw [ih]
      funext θ
      rw [Work.Spaces.Tfun_succ, hfun, deriv_Qp_cos, ih, Work.Spaces.qfun_apply, Qp_succ_eval]
      dsimp only []
      have hD : (Qp j α).derivative.eval (Real.cos (2 * θ))
          * (Real.sin (2 * θ) ^ 2 + Real.cos (2 * θ) ^ 2 - 1) = 0 := by
        rw [Real.sin_sq_add_cos_sq]; ring
      nlinarith [hD]

/-! ## Elementary absolute-value facts -/

/-- Product bound from bounds on the two factors. -/
theorem abs_mul_le_of {a b A B : ℝ} (ha : |a| ≤ A) (hb : |b| ≤ B) (hA : 0 ≤ A) :
    |a * b| ≤ A * B := by
  rw [abs_mul]
  exact mul_le_mul ha hb (abs_nonneg b) hA

theorem abs_one_sub_sq_le_one {v : ℝ} (hv : |v| ≤ 1) : |1 - v ^ 2| ≤ 1 := by
  have hv1 : -1 ≤ v := (abs_le.mp hv).1
  have hv2 : v ≤ 1 := (abs_le.mp hv).2
  rw [abs_le]; constructor <;> nlinarith [sq_nonneg v]

theorem abs_sub_third_le {v : ℝ} (hv : |v| ≤ 1) : |v - 1 / 3| ≤ 4 / 3 := by
  have hv1 : -1 ≤ v := (abs_le.mp hv).1
  have hv2 : v ≤ 1 := (abs_le.mp hv).2
  rw [abs_le]; constructor <;> linarith

theorem abs_two_mul_le_two {α : ℝ} (hα0 : 0 ≤ α) (hα1 : α ≤ 1) : |2 * α| ≤ 2 := by
  rw [abs_mul, show |(2 : ℝ)| = 2 from by norm_num, abs_of_nonneg hα0]
  simpa using mul_le_mul_of_nonneg_left hα1 (by norm_num : (0 : ℝ) ≤ 2)

theorem abs_four_add_two_mul_le {α : ℝ} (hα0 : 0 ≤ α) (hα1 : α ≤ 1) : |4 + 2 * α| ≤ 6 := by
  rw [abs_le]; constructor <;> linarith

/-! ## The four polynomials, evaluated -/

theorem Qp0_eval (α v : ℝ) : (Qp 0 α).eval v = v - 1 / 3 := by
  simp [Qp]

theorem Qp1_eval (α v : ℝ) :
    (Qp 1 α).eval v = (-2 : ℝ) * (1 - v ^ 2) + α * (v - 1 / 3) ^ 2 := by
  simp [Qp]; ring

theorem Qp1_deriv_eval (α v : ℝ) :
    (Qp 1 α).derivative.eval v = 4 * v + 2 * α * (v - 1 / 3) := by
  simp [Qp]; ring

theorem Qp2_eval (α v : ℝ) :
    (Qp 2 α).eval v = (-2 : ℝ) * (1 - v ^ 2) * (4 * v + 2 * α * (v - 1 / 3))
      + α * (v - 1 / 3) * ((-2 : ℝ) * (1 - v ^ 2) + α * (v - 1 / 3) ^ 2) := by
  simp [Qp]; ring

theorem Qp2_deriv_eval (α v : ℝ) :
    (Qp 2 α).derivative.eval v
      = 4 * v * (4 * v + 2 * α * (v - 1 / 3)) + ((-2 : ℝ) * (1 - v ^ 2)) * (4 + 2 * α)
        + α * ((-2 : ℝ) * (1 - v ^ 2) + α * (v - 1 / 3) ^ 2)
        + α * (v - 1 / 3) * (4 * v + 2 * α * (v - 1 / 3)) := by
  simp [Qp]; ring

theorem Qp3_eval (α v : ℝ) :
    (Qp 3 α).eval v
      = (-2 : ℝ) * (1 - v ^ 2)
          * (4 * v * (4 * v + 2 * α * (v - 1 / 3)) + ((-2 : ℝ) * (1 - v ^ 2)) * (4 + 2 * α)
              + α * ((-2 : ℝ) * (1 - v ^ 2) + α * (v - 1 / 3) ^ 2)
              + α * (v - 1 / 3) * (4 * v + 2 * α * (v - 1 / 3)))
        + α * (v - 1 / 3)
          * ((-2 : ℝ) * (1 - v ^ 2) * (4 * v + 2 * α * (v - 1 / 3))
              + α * (v - 1 / 3) * ((-2 : ℝ) * (1 - v ^ 2) + α * (v - 1 / 3) ^ 2)) := by
  simp [Qp]; ring

/-! ## Explicit bounds for `j ≤ 3` -/

theorem Qp0_eval_bound {α v : ℝ} (hv : |v| ≤ 1) : |(Qp 0 α).eval v| ≤ 4 / 3 := by
  rw [Qp0_eval]
  exact (abs_sub_third_le hv).trans (by norm_num)

theorem Qp1_eval_bound {α v : ℝ} (hα0 : 0 ≤ α) (hα1 : α ≤ 1) (hv : |v| ≤ 1) :
    |(Qp 1 α).eval v| ≤ 34 / 9 := by
  rw [Qp1_eval]
  have h1 : |1 - v ^ 2| ≤ 1 := abs_one_sub_sq_le_one hv
  have h2 : |v - 1 / 3| ≤ 4 / 3 := abs_sub_third_le hv
  have h3 : |(v - 1 / 3) ^ 2| ≤ (16 / 9 : ℝ) := by
    rw [abs_pow]
    exact (pow_le_pow_left₀ (abs_nonneg _) h2 2).trans_eq (by norm_num)
  have hA : |(-2 : ℝ) * (1 - v ^ 2)| ≤ 2 * 1 := by
    refine abs_mul_le_of (A := 2) (B := 1) ?_ h1 (by norm_num)
    rw [show |(-2 : ℝ)| = 2 from by norm_num]
  have hB : |α * (v - 1 / 3) ^ 2| ≤ 1 * (16 / 9) :=
    abs_mul_le_of (A := 1) (B := 16 / 9) (by rwa [abs_of_nonneg hα0]) h3 (by norm_num)
  calc |(-2 : ℝ) * (1 - v ^ 2) + α * (v - 1 / 3) ^ 2|
      ≤ |(-2 : ℝ) * (1 - v ^ 2)| + |α * (v - 1 / 3) ^ 2| := abs_add_le _ _
    _ ≤ 2 * 1 + 1 * (16 / 9) := add_le_add hA hB
    _ = 34 / 9 := by norm_num

theorem Qp1_deriv_bound {α v : ℝ} (hα0 : 0 ≤ α) (hα1 : α ≤ 1) (hv : |v| ≤ 1) :
    |(Qp 1 α).derivative.eval v| ≤ 20 / 3 := by
  rw [Qp1_deriv_eval]
  have h2 : |v - 1 / 3| ≤ 4 / 3 := abs_sub_third_le hv
  have hA : |(4 : ℝ) * v| ≤ 4 * 1 :=
    abs_mul_le_of (A := 4) (B := 1) (by norm_num) hv (by norm_num)
  have hB : |2 * α * (v - 1 / 3)| ≤ 2 * (4 / 3) := by
    rw [show (2 : ℝ) * α * (v - 1 / 3) = (2 * α) * (v - 1 / 3) by ring]
    exact abs_mul_le_of (A := 2) (B := 4 / 3) (abs_two_mul_le_two hα0 hα1) h2 (by norm_num)
  calc |4 * v + 2 * α * (v - 1 / 3)| ≤ |(4 : ℝ) * v| + |2 * α * (v - 1 / 3)| := abs_add_le _ _
    _ ≤ 4 * 1 + 2 * (4 / 3) := add_le_add hA hB
    _ = 20 / 3 := by norm_num

theorem Qp2_eval_bound {α v : ℝ} (hα0 : 0 ≤ α) (hα1 : α ≤ 1) (hv : |v| ≤ 1) :
    |(Qp 2 α).eval v| ≤ 496 / 27 := by
  rw [Qp2_eval]
  have h1 : |1 - v ^ 2| ≤ 1 := abs_one_sub_sq_le_one hv
  have h2 : |v - 1 / 3| ≤ 4 / 3 := abs_sub_third_le hv
  have hR : |4 * v + 2 * α * (v - 1 / 3)| ≤ 20 / 3 := by
    rw [← Qp1_deriv_eval]; exact Qp1_deriv_bound hα0 hα1 hv
  have hQ : |(-2 : ℝ) * (1 - v ^ 2) + α * (v - 1 / 3) ^ 2| ≤ 34 / 9 := by
    rw [← Qp1_eval]; exact Qp1_eval_bound hα0 hα1 hv
  have hA : |(-2 : ℝ) * (1 - v ^ 2) * (4 * v + 2 * α * (v - 1 / 3))| ≤ 2 * 1 * (20 / 3) := by
    rw [show (-2 : ℝ) * (1 - v ^ 2) * (4 * v + 2 * α * (v - 1 / 3))
        = ((-2 : ℝ) * (1 - v ^ 2)) * (4 * v + 2 * α * (v - 1 / 3)) by ring]
    exact abs_mul_le_of (A := 2 * 1) (B := 20 / 3)
      (by rw [abs_mul]; norm_num; exact h1) hR (by norm_num)
  have hB : |α * (v - 1 / 3) * ((-2 : ℝ) * (1 - v ^ 2) + α * (v - 1 / 3) ^ 2)|
      ≤ 1 * (4 / 3) * (34 / 9) := by
    rw [show α * (v - 1 / 3) * ((-2 : ℝ) * (1 - v ^ 2) + α * (v - 1 / 3) ^ 2)
        = (α * (v - 1 / 3)) * ((-2 : ℝ) * (1 - v ^ 2) + α * (v - 1 / 3) ^ 2) by ring]
    exact abs_mul_le_of (A := 1 * (4 / 3)) (B := 34 / 9)
      (abs_mul_le_of (A := 1) (B := 4 / 3) (by rwa [abs_of_nonneg hα0]) h2 (by norm_num))
      hQ (by norm_num)
  calc |(-2 : ℝ) * (1 - v ^ 2) * (4 * v + 2 * α * (v - 1 / 3))
        + α * (v - 1 / 3) * ((-2 : ℝ) * (1 - v ^ 2) + α * (v - 1 / 3) ^ 2)|
      ≤ _ + _ := abs_add_le _ _
    _ ≤ 2 * 1 * (20 / 3) + 1 * (4 / 3) * (34 / 9) := add_le_add hA hB
    _ = 496 / 27 := by norm_num

theorem Qp2_deriv_bound {α v : ℝ} (hα0 : 0 ≤ α) (hα1 : α ≤ 1) (hv : |v| ≤ 1) :
    |(Qp 2 α).derivative.eval v| ≤ 154 / 3 := by
  rw [Qp2_deriv_eval]
  have h1 : |1 - v ^ 2| ≤ 1 := abs_one_sub_sq_le_one hv
  have h2 : |v - 1 / 3| ≤ 4 / 3 := abs_sub_third_le hv
  have hR : |4 * v + 2 * α * (v - 1 / 3)| ≤ 20 / 3 := by
    rw [← Qp1_deriv_eval]; exact Qp1_deriv_bound hα0 hα1 hv
  have hQ : |(-2 : ℝ) * (1 - v ^ 2) + α * (v - 1 / 3) ^ 2| ≤ 34 / 9 := by
    rw [← Qp1_eval]; exact Qp1_eval_bound hα0 hα1 hv
  have h4 : |4 + 2 * α| ≤ 6 := abs_four_add_two_mul_le hα0 hα1
  have hA : |4 * v * (4 * v + 2 * α * (v - 1 / 3))| ≤ 4 * 1 * (20 / 3) := by
    rw [show 4 * v * (4 * v + 2 * α * (v - 1 / 3))
        = (4 * v) * (4 * v + 2 * α * (v - 1 / 3)) by ring]
    exact abs_mul_le_of (A := 4 * 1) (B := 20 / 3)
      (by rw [abs_mul]; norm_num; exact hv) hR (by norm_num)
  have hB : |((-2 : ℝ) * (1 - v ^ 2)) * (4 + 2 * α)| ≤ 2 * 1 * 6 :=
    abs_mul_le_of (A := 2 * 1) (B := 6) (by rw [abs_mul]; norm_num; exact h1) h4 (by norm_num)
  have hC : |α * ((-2 : ℝ) * (1 - v ^ 2) + α * (v - 1 / 3) ^ 2)| ≤ 1 * (34 / 9) :=
    abs_mul_le_of (A := 1) (B := 34 / 9) (by rwa [abs_of_nonneg hα0]) hQ (by norm_num)
  have hD : |α * (v - 1 / 3) * (4 * v + 2 * α * (v - 1 / 3))| ≤ 1 * (4 / 3) * (20 / 3) := by
    rw [show α * (v - 1 / 3) * (4 * v + 2 * α * (v - 1 / 3))
        = (α * (v - 1 / 3)) * (4 * v + 2 * α * (v - 1 / 3)) by ring]
    exact abs_mul_le_of (A := 1 * (4 / 3)) (B := 20 / 3)
      (abs_mul_le_of (A := 1) (B := 4 / 3) (by rwa [abs_of_nonneg hα0]) h2 (by norm_num))
      hR (by norm_num)
  have hsplit := abs_add_le (4 * v * (4 * v + 2 * α * (v - 1 / 3)) + (-2 * (1 - v ^ 2)) * (4 + 2 * α)
      + α * (-2 * (1 - v ^ 2) + α * (v - 1 / 3) ^ 2))
      (α * (v - 1 / 3) * (4 * v + 2 * α * (v - 1 / 3)))
  have hsplit2 := abs_add_le (4 * v * (4 * v + 2 * α * (v - 1 / 3))
      + (-2 * (1 - v ^ 2)) * (4 + 2 * α))
      (α * (-2 * (1 - v ^ 2) + α * (v - 1 / 3) ^ 2))
  have hsplit3 := abs_add_le (4 * v * (4 * v + 2 * α * (v - 1 / 3)))
      ((-2 * (1 - v ^ 2)) * (4 + 2 * α))
  calc |4 * v * (4 * v + 2 * α * (v - 1 / 3)) + (-2 * (1 - v ^ 2)) * (4 + 2 * α)
        + α * (-2 * (1 - v ^ 2) + α * (v - 1 / 3) ^ 2)
        + α * (v - 1 / 3) * (4 * v + 2 * α * (v - 1 / 3))|
      = |(4 * v * (4 * v + 2 * α * (v - 1 / 3)) + (-2 * (1 - v ^ 2)) * (4 + 2 * α)
          + α * (-2 * (1 - v ^ 2) + α * (v - 1 / 3) ^ 2))
          + α * (v - 1 / 3) * (4 * v + 2 * α * (v - 1 / 3))| := by ring_nf
    _ ≤ |4 * v * (4 * v + 2 * α * (v - 1 / 3)) + (-2 * (1 - v ^ 2)) * (4 + 2 * α)
          + α * (-2 * (1 - v ^ 2) + α * (v - 1 / 3) ^ 2)|
        + |α * (v - 1 / 3) * (4 * v + 2 * α * (v - 1 / 3))| := hsplit
    _ = |(4 * v * (4 * v + 2 * α * (v - 1 / 3)) + (-2 * (1 - v ^ 2)) * (4 + 2 * α))
          + α * (-2 * (1 - v ^ 2) + α * (v - 1 / 3) ^ 2)|
        + |α * (v - 1 / 3) * (4 * v + 2 * α * (v - 1 / 3))| := by ring_nf
    _ ≤ (|4 * v * (4 * v + 2 * α * (v - 1 / 3)) + (-2 * (1 - v ^ 2)) * (4 + 2 * α)|
          + |α * (-2 * (1 - v ^ 2) + α * (v - 1 / 3) ^ 2)|)
        + |α * (v - 1 / 3) * (4 * v + 2 * α * (v - 1 / 3))| := by
        linarith [hsplit2, abs_nonneg (α * (v - 1 / 3) * (4 * v + 2 * α * (v - 1 / 3)))]
    _ = (|(4 * v * (4 * v + 2 * α * (v - 1 / 3))) + (-2 * (1 - v ^ 2)) * (4 + 2 * α)|
          + |α * (-2 * (1 - v ^ 2) + α * (v - 1 / 3) ^ 2)|)
        + |α * (v - 1 / 3) * (4 * v + 2 * α * (v - 1 / 3))| := by ring_nf
    _ ≤ (|4 * v * (4 * v + 2 * α * (v - 1 / 3))| + |(-2 * (1 - v ^ 2)) * (4 + 2 * α)|
          + |α * (-2 * (1 - v ^ 2) + α * (v - 1 / 3) ^ 2)|)
        + |α * (v - 1 / 3) * (4 * v + 2 * α * (v - 1 / 3))| := by
        linarith [hsplit3]
    _ ≤ (4 * 1 * (20 / 3) + 2 * 1 * 6 + 1 * (34 / 9)) + 1 * (4 / 3) * (20 / 3) := by
        linarith [hA, hB, hC, hD]
    _ = 154 / 3 := by norm_num

set_option maxHeartbeats 1600000 in
theorem Qp3_eval_bound {α v : ℝ} (hα0 : 0 ≤ α) (hα1 : α ≤ 1) (hv : |v| ≤ 1) :
    |(Qp 3 α).eval v| ≤ 10300 / 81 := by
  rw [Qp3_eval]
  have h1 : |1 - v ^ 2| ≤ 1 := abs_one_sub_sq_le_one hv
  have h2 : |v - 1 / 3| ≤ 4 / 3 := abs_sub_third_le hv
  have hQ2 : |(-2 : ℝ) * (1 - v ^ 2) * (4 * v + 2 * α * (v - 1 / 3))
      + α * (v - 1 / 3) * ((-2 : ℝ) * (1 - v ^ 2) + α * (v - 1 / 3) ^ 2)| ≤ 496 / 27 := by
    rw [← Qp2_eval]; exact Qp2_eval_bound hα0 hα1 hv
  have hR2 : |4 * v * (4 * v + 2 * α * (v - 1 / 3)) + ((-2 : ℝ) * (1 - v ^ 2)) * (4 + 2 * α)
      + α * ((-2 : ℝ) * (1 - v ^ 2) + α * (v - 1 / 3) ^ 2)
      + α * (v - 1 / 3) * (4 * v + 2 * α * (v - 1 / 3))| ≤ 154 / 3 := by
    rw [← Qp2_deriv_eval]; exact Qp2_deriv_bound hα0 hα1 hv
  have hA : |(-2 : ℝ) * (1 - v ^ 2)
      * (4 * v * (4 * v + 2 * α * (v - 1 / 3)) + ((-2 : ℝ) * (1 - v ^ 2)) * (4 + 2 * α)
          + α * ((-2 : ℝ) * (1 - v ^ 2) + α * (v - 1 / 3) ^ 2)
          + α * (v - 1 / 3) * (4 * v + 2 * α * (v - 1 / 3)))| ≤ 2 * 1 * (154 / 3) := by
    rw [show (-2 : ℝ) * (1 - v ^ 2)
        * (4 * v * (4 * v + 2 * α * (v - 1 / 3)) + ((-2 : ℝ) * (1 - v ^ 2)) * (4 + 2 * α)
            + α * ((-2 : ℝ) * (1 - v ^ 2) + α * (v - 1 / 3) ^ 2)
            + α * (v - 1 / 3) * (4 * v + 2 * α * (v - 1 / 3)))
        = ((-2 : ℝ) * (1 - v ^ 2))
          * (4 * v * (4 * v + 2 * α * (v - 1 / 3)) + ((-2 : ℝ) * (1 - v ^ 2)) * (4 + 2 * α)
            + α * ((-2 : ℝ) * (1 - v ^ 2) + α * (v - 1 / 3) ^ 2)
            + α * (v - 1 / 3) * (4 * v + 2 * α * (v - 1 / 3))) by ring]
    exact abs_mul_le_of (A := 2 * 1) (B := 154 / 3)
      (by rw [abs_mul]; norm_num; exact h1) hR2 (by norm_num)
  have hB : |α * (v - 1 / 3)
      * ((-2 : ℝ) * (1 - v ^ 2) * (4 * v + 2 * α * (v - 1 / 3))
          + α * (v - 1 / 3) * ((-2 : ℝ) * (1 - v ^ 2) + α * (v - 1 / 3) ^ 2))|
      ≤ 1 * (4 / 3) * (496 / 27) := by
    rw [show α * (v - 1 / 3)
        * ((-2 : ℝ) * (1 - v ^ 2) * (4 * v + 2 * α * (v - 1 / 3))
            + α * (v - 1 / 3) * ((-2 : ℝ) * (1 - v ^ 2) + α * (v - 1 / 3) ^ 2))
        = (α * (v - 1 / 3))
          * ((-2 : ℝ) * (1 - v ^ 2) * (4 * v + 2 * α * (v - 1 / 3))
            + α * (v - 1 / 3) * ((-2 : ℝ) * (1 - v ^ 2) + α * (v - 1 / 3) ^ 2)) by ring]
    exact abs_mul_le_of (A := 1 * (4 / 3)) (B := 496 / 27)
      (abs_mul_le_of (A := 1) (B := 4 / 3) (by rwa [abs_of_nonneg hα0]) h2 (by norm_num))
      hQ2 (by norm_num)
  calc |(-2 : ℝ) * (1 - v ^ 2)
        * (4 * v * (4 * v + 2 * α * (v - 1 / 3)) + ((-2 : ℝ) * (1 - v ^ 2)) * (4 + 2 * α)
            + α * ((-2 : ℝ) * (1 - v ^ 2) + α * (v - 1 / 3) ^ 2)
            + α * (v - 1 / 3) * (4 * v + 2 * α * (v - 1 / 3)))
        + α * (v - 1 / 3)
          * ((-2 : ℝ) * (1 - v ^ 2) * (4 * v + 2 * α * (v - 1 / 3))
              + α * (v - 1 / 3) * ((-2 : ℝ) * (1 - v ^ 2) + α * (v - 1 / 3) ^ 2))|
      ≤ _ + _ := abs_add_le _ _
    _ ≤ 2 * 1 * (154 / 3) + 1 * (4 / 3) * (496 / 27) := add_le_add hA hB
    _ = 10300 / 81 := by norm_num

/-- **The bound for the coefficient polynomials.** -/
theorem Qp_eval_bound (j : ℕ) (hj : j ≤ 3) (α v : ℝ) (hα0 : 0 ≤ α) (hα1 : α ≤ 1)
    (hv : |v| ≤ 1) : |(Qp j α).eval v| ≤ 100000 := by
  interval_cases j
  · exact (Qp0_eval_bound (α := α) hv).trans (by norm_num)
  · exact (Qp1_eval_bound hα0 hα1 hv).trans (by norm_num)
  · exact (Qp2_eval_bound hα0 hα1 hv).trans (by norm_num)
  · exact (Qp3_eval_bound hα0 hα1 hv).trans (by norm_num)

/-- **The bound `|Tfun j α θ| ≤ 100000` for `j ≤ 3`.** -/
theorem Tfun_abs_le (j : ℕ) (hj : j ≤ 3) (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) (θ : ℝ) :
    |Work.Spaces.Tfun j α θ| ≤ 100000 := by
  rw [Tfun_eq_Qp j α]
  exact Qp_eval_bound j hj α (Real.cos (2 * θ)) (le_of_lt hα) hα1
    (abs_le.mpr ⟨Real.neg_one_le_cos _, Real.cos_le_one _⟩)

/-! ## The main statement -/

theorem DthIter_Gam_abs_le (i : ℕ) (hi : i ≤ 4) (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1)
    {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) :
    |Work.Spaces.DthIter i (fun _ θ' => Work.Spaces.Gam α θ') 0 θ|
      ≤ 100000 * Work.Spaces.Gam α θ := by
  have hG0 : 0 ≤ Work.Spaces.Gam α θ := (Work.Spaces.Gam_bounds α θ hα hθ).1
  rcases Nat.eq_zero_or_pos i with h | h
  · subst h
    rw [Work.Spaces.DthIter_zero, abs_of_nonneg hG0]
    linarith
  · have hT : ∀ θ' ∈ Work.Spaces.Iθ, |Work.Spaces.Tfun (i - 1) α θ'| ≤ 100000 :=
      fun θ' _ => Tfun_abs_le (i - 1) (by omega) α hα hα1 θ'
    have hkey := Work.Spaces.dthU_iter_Gam_abs_bound i h α hα 100000 hT θ hθ
    rw [DthIter_rad_eq i (fun t => Work.Spaces.Gam α t) 0 θ]
    calc |Work.Spaces.dthU^[i] (fun t => Work.Spaces.Gam α t) θ|
        ≤ α * 100000 * Work.Spaces.Gam α θ := hkey
      _ ≤ 100000 * Work.Spaces.Gam α θ := by nlinarith [hα, hα1, hG0]

end Work.FTS.LocData
end
end
-- ===== merged: Submission.Work.FTS.LocData.DthIter_mul_smoothQuad =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open Filter

namespace Work.FTS.LocData

set_option autoImplicit false

/-- `smoothOrder` is a fixed point of `n ↦ n + 1`: the derivative of a `C^∞` function is
again `C^∞`. -/
theorem smoothOrder_add_one : Work.Stability.smoothOrder + 1 = Work.Stability.smoothOrder := rfl

/-- Iterating the one-dimensional operator `Lop u θ = sin(2θ)·u'(θ)` preserves the genuine
`C^∞` order at a point.  (The analytic counterpart is the anonymous step inside
`Work.Spaces.Lop_iter_contDiffAt`, which uses `ContDiffAt.derivWithin` at `⊤ = ω`.) -/
theorem Lop_iter_contDiffAt_smooth (u : ℝ → ℝ) (θ : ℝ)
    (hu : ContDiffAt ℝ Work.Stability.smoothOrder u θ) (j : ℕ) :
    ContDiffAt ℝ Work.Stability.smoothOrder (Work.Spaces.Lop^[j] u) θ := by
  induction j with
  | zero => simpa using hu
  | succ j ih =>
      rw [Function.iterate_succ_apply']
      have hsin : ContDiffAt ℝ Work.Stability.smoothOrder
          (fun θ : ℝ => Real.sin (2 * θ)) θ := by
        fun_prop
      have hd : ContDiffAt ℝ Work.Stability.smoothOrder
          (deriv (Work.Spaces.Lop^[j] u)) θ :=
        ih.derivWithin smoothOrder_add_one.le
      have heq : Work.Spaces.Lop (Work.Spaces.Lop^[j] u)
          = (fun θ : ℝ => Real.sin (2 * θ)) * deriv (Work.Spaces.Lop^[j] u) := rfl
      rw [heq]
      exact hsin.mul hd

/-- **Iterated Leibniz rule for `Lop`, genuine smooth order.**  On an open set `U` where
`u` and `v` are `C^∞` (in the genuine sense `smoothOrder`), the `j`-fold iterate of `Lop`
applied to the pointwise product agrees on `U` with the binomial convolution. -/
theorem Lop_iter_mul_eqOn_smooth (u v : ℝ → ℝ) (U : Set ℝ) (hU : IsOpen U)
    (hu : ContDiffOn ℝ Work.Stability.smoothOrder u U)
    (hv : ContDiffOn ℝ Work.Stability.smoothOrder v U) (j : ℕ) :
    Set.EqOn (Work.Spaces.Lop^[j] (u * v))
      (fun θ => ∑ a ∈ Finset.range (j + 1),
        (j.choose a : ℝ) * (Work.Spaces.Lop^[a] u θ * Work.Spaces.Lop^[j - a] v θ)) U := by
  induction j with
  | zero =>
      intro θ hθ
      simp [Function.iterate_zero_apply]
  | succ j ih =>
      intro θ hθ
      rw [Function.iterate_succ_apply']
      have hFa : ∀ a, ContDiffAt ℝ Work.Stability.smoothOrder (Work.Spaces.Lop^[a] u) θ :=
        fun a => Lop_iter_contDiffAt_smooth u θ (hu.contDiffAt (hU.mem_nhds hθ)) a
      have hGb : ∀ b, ContDiffAt ℝ Work.Stability.smoothOrder (Work.Spaces.Lop^[b] v) θ :=
        fun b => Lop_iter_contDiffAt_smooth v θ (hv.contDiffAt (hU.mem_nhds hθ)) b
      have hmem : ∀ a ∈ Finset.range (j + 1), DifferentiableAt ℝ
          (fun θ' => (j.choose a : ℝ)
            * (Work.Spaces.Lop^[a] u θ' * Work.Spaces.Lop^[j - a] v θ')) θ := by
        intro a ha
        exact (((hFa a).differentiableAt (by simp)).mul
          ((hGb (j - a)).differentiableAt (by simp))).const_mul _
      have hfun : (fun θ' => ∑ a ∈ Finset.range (j + 1),
            (j.choose a : ℝ) * (Work.Spaces.Lop^[a] u θ' * Work.Spaces.Lop^[j - a] v θ'))
          = ∑ a ∈ Finset.range (j + 1),
            (fun θ' => (j.choose a : ℝ)
              * (Work.Spaces.Lop^[a] u θ' * Work.Spaces.Lop^[j - a] v θ')) := by
        funext θ'
        rw [Finset.sum_apply]
      have hderiv : deriv (Work.Spaces.Lop^[j] (u * v)) θ
          = deriv (fun θ' => ∑ a ∈ Finset.range (j + 1),
              (j.choose a : ℝ)
                * (Work.Spaces.Lop^[a] u θ' * Work.Spaces.Lop^[j - a] v θ')) θ :=
        (ih.deriv hU) hθ
      have hkey : Work.Spaces.Lop (Work.Spaces.Lop^[j] (u * v)) θ
          = ∑ a ∈ Finset.range (j + 1), Real.sin (2 * θ)
              * deriv (fun θ' => (j.choose a : ℝ)
                * (Work.Spaces.Lop^[a] u θ' * Work.Spaces.Lop^[j - a] v θ')) θ := by
        show Real.sin (2 * θ) * deriv (Work.Spaces.Lop^[j] (u * v)) θ
          = ∑ a ∈ Finset.range (j + 1), Real.sin (2 * θ)
              * deriv (fun θ' => (j.choose a : ℝ)
                * (Work.Spaces.Lop^[a] u θ' * Work.Spaces.Lop^[j - a] v θ')) θ
        rw [hderiv, hfun, deriv_sum hmem, Finset.mul_sum]
      rw [hkey]
      rw [Finset.sum_congr rfl
        (fun a _ => Work.Spaces.sin_deriv_term u v θ j a ((hFa a).differentiableAt (by simp))
          ((hGb (j - a)).differentiableAt (by simp)))]
      exact Work.Spaces.leibniz_step j (fun b => Work.Spaces.Lop^[b] u θ)
        (fun b => Work.Spaces.Lop^[b] v θ)

/-- **Leibniz rule for `D_θ^j`, genuine smooth order.**  On an open set `U` where the
`θ`-slices of `f` and `g` (at the fixed `z`) are `C^∞`, the `j`-th iterate of `D_θ` applied
to the pointwise product satisfies the binomial expansion. -/
theorem DthIter_mul_smooth (j : ℕ) (f g : ℝ → ℝ → ℝ) (z : ℝ) (U : Set ℝ) (hU : IsOpen U)
    (hf : ContDiffOn ℝ Work.Stability.smoothOrder (fun θ => f z θ) U)
    (hg : ContDiffOn ℝ Work.Stability.smoothOrder (fun θ => g z θ) U) :
    ∀ θ ∈ U, Work.Spaces.DthIter j (fun z θ => f z θ * g z θ) z θ =
      ∑ a ∈ Finset.range (j + 1),
        (j.choose a : ℝ) * (Work.Spaces.DthIter a f z θ * Work.Spaces.DthIter (j - a) g z θ) := by
  intro θ hθ
  have hmain := Lop_iter_mul_eqOn_smooth (fun θ' => f z θ') (fun θ' => g z θ') U hU hf hg j hθ
  have hstep : Work.Spaces.DthIter j (fun z θ => f z θ * g z θ) z θ
      = ∑ a ∈ Finset.range (j + 1), (j.choose a : ℝ)
          * (Work.Spaces.Lop^[a] (fun θ' => f z θ') θ
            * Work.Spaces.Lop^[j - a] (fun θ' => g z θ') θ) := by
    rw [show (fun θ' => f z θ') * (fun θ' => g z θ') = (fun θ' => f z θ' * g z θ')
        from rfl] at hmain
    simp only [] at hmain
    rw [← hmain]
    exact congrFun (Work.Spaces.DthIter_eq_iterate_Lop j (fun z θ => f z θ * g z θ) z) θ
  rw [hstep]
  apply Finset.sum_congr rfl
  intro a ha
  rw [Work.Spaces.DthIter_eq_iterate_Lop a f z,
    Work.Spaces.DthIter_eq_iterate_Lop (j - a) g z]

/-- **The Leibniz rule of the localisation chapter.**  For `C^∞` (genuine, order
`smoothOrder`) `θ`-slices at the fixed `z` on the angular interval `(0,π/2)`, the `j`-th
iterate of `D_θ` applied to a pointwise product expands into the binomial convolution. -/
theorem DthIter_mul_smoothQuad (j : ℕ) (f g : ℝ → ℝ → ℝ) {z θ : ℝ}
    (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2))
    (hf : ContDiffOn ℝ Work.Stability.smoothOrder (fun θ' => f z θ') (Set.Ioo 0 (Real.pi / 2)))
    (hg : ContDiffOn ℝ Work.Stability.smoothOrder (fun θ' => g z θ') (Set.Ioo 0 (Real.pi / 2))) :
    Work.Spaces.DthIter j (fun z θ => f z θ * g z θ) z θ =
      ∑ a ∈ Finset.range (j + 1),
        (j.choose a : ℝ) * (Work.Spaces.DthIter a f z θ * Work.Spaces.DthIter (j - a) g z θ) :=
  DthIter_mul_smooth j f g z (Set.Ioo 0 (Real.pi / 2)) isOpen_Ioo hf hg θ hθ

end Work.FTS.LocData
end
end
-- ===== merged: Submission.Work.FTS.LocData.DzIter_mul_smoothQuad =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open Set Filter

namespace Work.FTS.LocData

set_option autoImplicit false
set_option maxHeartbeats 1600000

/-! ## The class of smooth (non-analytic) functions of `z` -/

/-- The functions of the single variable `z` which are `C^∞` on `(-1,∞)` in the genuine
smooth order `Work.Stability.smoothOrder = ((⊤ : ℕ∞) : ℕ∞ω)` — *not* in the analytic
order `⊤ : ℕ∞ω` of `Work.Spaces.SmoothZ`.  A cut-off `χ(z/L)` belongs to this class but
not to the analytic one. -/
def SmoothZsm (u : ℝ → ℝ) : Prop :=
  ContDiffOn ℝ Work.Stability.smoothOrder u (Set.Ioi (-1))

/-- `SmoothZsm` is closed under `+`, `*` and scalar multiples. -/
theorem SmoothZsm_FunClass : Work.Spaces.FunClass SmoothZsm where
  add := fun A B hA hB => hA.add hB
  mul := fun A B hA hB => hA.mul hB
  smul := fun c A hA => by
    show ContDiffOn ℝ Work.Stability.smoothOrder (fun p => c * A p) (Set.Ioi (-1))
    exact ContDiffOn.const_smul c hA

/-! ## `Zop = z ∂_z` is a derivation on the smooth functions of `(-1,∞)` -/

/-- **`Zop u = fun z => z · u'(z)`** (the action of `D_z` on the `z`-slice) is a
derivation-like operator on the functions `C^∞` on `(-1,∞)`, in the exact sense of
`Work.Spaces.DerivLike`: this is `Work.Spaces.Zop_DerivLike` with the analytic class
`Work.Spaces.SmoothZ` replaced by the smooth class `SmoothZsm`. -/
theorem Zop_DerivLike_smoothZd :
    Work.Spaces.DerivLike (Set.Ioi (-1)) SmoothZsm Work.Spaces.Zop where
  add := fun A B hA hB => by
    intro z hz
    have hA' : DifferentiableAt ℝ A z :=
      (hA.contDiffAt (isOpen_Ioi.mem_nhds hz)).differentiableAt (by simp)
    have hB' : DifferentiableAt ℝ B z :=
      (hB.contDiffAt (isOpen_Ioi.mem_nhds hz)).differentiableAt (by simp)
    show Work.Spaces.Zop (A + B) z = Work.Spaces.Zop A z + Work.Spaces.Zop B z
    simp only [Work.Spaces.Zop]
    rw [deriv_add hA' hB']
    ring
  mul := fun A B hA hB => by
    intro z hz
    have hA' : DifferentiableAt ℝ A z :=
      (hA.contDiffAt (isOpen_Ioi.mem_nhds hz)).differentiableAt (by simp)
    have hB' : DifferentiableAt ℝ B z :=
      (hB.contDiffAt (isOpen_Ioi.mem_nhds hz)).differentiableAt (by simp)
    show Work.Spaces.Zop (A * B) z = Work.Spaces.Zop A z * B z + A z * Work.Spaces.Zop B z
    simp only [Work.Spaces.Zop]
    rw [deriv_mul hA' hB']
    ring
  congr := fun A B h => by
    intro z hz
    show Work.Spaces.Zop A z = Work.Spaces.Zop B z
    simp only [Work.Spaces.Zop]
    rw [h.deriv isOpen_Ioi hz]
  preserve := fun A hA => by
    have hfd : ContDiffOn ℝ Work.Stability.smoothOrder (fderiv ℝ A) (Set.Ioi (-1)) :=
      hA.fderiv_of_isOpen isOpen_Ioi (by simp)
    have hev : ContDiffOn ℝ Work.Stability.smoothOrder (fun z : ℝ => (fderiv ℝ A z) 1)
        (Set.Ioi (-1)) :=
      hfd.clm_apply contDiffOn_const
    have hfun : ContDiffOn ℝ Work.Stability.smoothOrder
        (fun z : ℝ => z * (fderiv ℝ A z) 1) (Set.Ioi (-1)) :=
      (contDiff_id.contDiffOn).mul hev
    refine hfun.congr (fun z hz => ?_)
    show Work.Spaces.Zop A z = z * (fderiv ℝ A z) 1
    simp only [Work.Spaces.Zop]
    rw [fderiv_apply_one_eq_deriv]
  smul := fun c A hA => by
    intro z hz
    have hA' : DifferentiableAt ℝ A z :=
      (hA.contDiffAt (isOpen_Ioi.mem_nhds hz)).differentiableAt (by simp)
    show Work.Spaces.Zop (fun p => c * A p) z = c * Work.Spaces.Zop A z
    simp only [Work.Spaces.Zop]
    rw [deriv_const_mul c hA']
    ring

/-! ## `DzIter` on a slice is the iterate of `Zop` -/

/-- For fixed `θ`, the iterated operator `D_z^n` on the `z`-slice is the `n`-fold iterate
of `Zop`. -/
theorem Zop_iterate_slice (n : ℕ) (f : ℝ → ℝ → ℝ) (θ : ℝ) :
    (fun z => Work.Spaces.DzIter n f z θ) = Work.Spaces.Zop^[n] (fun z => f z θ) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      funext z
      rw [Function.iterate_succ_apply']
      show Work.Spaces.Dz (Work.Spaces.DzIter n f) z θ
          = Work.Spaces.Zop (Work.Spaces.Zop^[n] (fun z => f z θ)) z
      simp only [Work.Spaces.Dz, Work.Spaces.pz, Work.Spaces.Zop]
      rw [ih]

/-! ## The Leibniz rule -/

theorem DzIter_mul_smoothQuad (j : ℕ) (f g : ℝ → ℝ → ℝ) {z θ : ℝ} (hz : z ∈ Work.Spaces.Iz)
    (hf : ContDiffOn ℝ Work.Stability.smoothOrder (fun z' => f z' θ) (Set.Ioi (-1)))
    (hg : ContDiffOn ℝ Work.Stability.smoothOrder (fun z' => g z' θ) (Set.Ioi (-1))) :
    Work.Spaces.DzIter j (fun z θ => f z θ * g z θ) z θ =
      ∑ b ∈ Finset.range (j + 1),
        (j.choose b : ℝ) * (Work.Spaces.DzIter b f z θ * Work.Spaces.DzIter (j - b) g z θ) := by
  have hz1 : z ∈ Set.Ioi (-1) := by
    rw [Work.Spaces.Iz, Set.mem_Ici] at hz
    exact Set.mem_Ioi.mpr (by linarith)
  have key := (Work.Spaces.DerivLike.iterate_mul Zop_DerivLike_smoothZd SmoothZsm_FunClass
    j hf hg) hz1
  rw [show (fun z => f z θ) * (fun z => g z θ) = (fun z => f z θ * g z θ) from rfl] at key
  have htr : Work.Spaces.Zop^[j] (fun z => (fun z θ => f z θ * g z θ) z θ) z =
      Work.Spaces.Zop^[j] (fun z => f z θ * g z θ) z := rfl
  rw [congrFun (Zop_iterate_slice j (fun z θ => f z θ * g z θ) θ) z, htr, key]
  apply Finset.sum_congr rfl
  intro b hb
  rw [← congrFun (Zop_iterate_slice b f θ) z,
    ← congrFun (Zop_iterate_slice (j - b) g θ) z]

end Work.FTS.LocData
end
end
-- ===== merged: Submission.Work.FTS.LocData.DzIter_oneSubChi_bound =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.LocData

set_option linter.unusedVariables false

/-! ## 1. The chain rule for a dilation -/

/-- **The iterated derivative of a dilation.**  For a smooth `m` and `L ≠ 0`,
`(∂^k (m(·/L)))(z) = (L⁻¹)^k (∂^k m)(z/L)`: differentiating `m (L⁻¹ ·)` `k` times pulls
out `k` factors of `L⁻¹`. -/
theorem IteratedDeriv_comp_div (m : ℝ → ℝ) (hm : ContDiff ℝ Work.Stability.smoothOrder m)
    {L : ℝ} (hL : L ≠ 0) (k : ℕ) (x : ℝ) :
    iteratedDeriv k (fun x => m (x / L)) x = (L⁻¹) ^ k * iteratedDeriv k m (x / L) := by
  have h1 : ContDiff ℝ ((k : ℕ∞) : WithTop ℕ∞) m := hm.of_le (by simp)
  have h2 := iteratedDeriv_comp_const_mul (f := m) (c := L⁻¹) (n := k) h1
  have h3 : iteratedDeriv k (fun x => m (x / L))
      = fun x => (L⁻¹) ^ k * iteratedDeriv k m (x / L) := by
    simpa only [div_eq_mul_inv, mul_comm] using h2
  exact congrFun h3 x

/-! ## 2. The Stirling expansion of the iterated operator `D_z = z ∂_z`

The algebra of one step of the induction: multiplying by `z` converts `k z^{k-1} A + z^k B`
(the derivative of `z^k A`) into `k z^k A + z^{k+1} B`.  This is the identity underlying the
Pascal recursion of the Stirling numbers. -/

private theorem z_mul_weighted (k : ℕ) (z A B : ℝ) :
    z * ((k : ℝ) * z ^ (k - 1) * A + z ^ k * B) = (k : ℝ) * z ^ k * A + z ^ (k + 1) * B := by
  rcases k with _ | n
  · ring
  · rw [pow_succ]; push_cast; ring

/-- `∂_z (z^k) = k z^{k-1}`. -/
private theorem deriv_zpow (k : ℕ) (z : ℝ) :
    deriv (fun z' : ℝ => z' ^ k) z = (k : ℝ) * z ^ (k - 1) :=
  (hasDerivAt_pow k z).deriv

/-- **The expansion of `D_z^j` in terms of the Stirling numbers of the second kind.**
For a smooth `m : ℝ → ℝ`, `DzIterZ j m = ∑_{k≤j} S(j,k) · z^k · ∂^k m`, with
`S(j,k) = Work.Spaces.scoef j k`.

This is the one-variable counterpart of `Work.Spaces.DzIter_eq_sum_scoef`, which is phrased
with the (unusable for a cut-off) analyticity hypothesis `ContDiffOn ℝ ⊤`; here
`Work.Stability.smoothOrder` — genuine `C^∞`-smoothness on all of `ℝ` — is enough. -/
theorem DzIterZ_eq_sum_scoef (m : ℝ → ℝ) (hm : ContDiff ℝ Work.Stability.smoothOrder m) :
    ∀ j : ℕ, Work.Coercivity.CommutZ.DzIterZ j m =
      fun z => ∑ k ∈ Finset.range (j + 1),
        (Work.Spaces.scoef j k : ℝ) * (z ^ k * iteratedDeriv k m z) := by
  intro j
  induction j with
  | zero =>
    funext z
    show m z = ∑ k ∈ Finset.range (0 + 1),
      (Work.Spaces.scoef 0 k : ℝ) * (z ^ k * iteratedDeriv k m z)
    simp [Work.Spaces.scoef]
  | succ j ih =>
    rw [Work.Coercivity.CommutZ.DzIterZ_succ, ih]
    funext z
    have hdiff : ∀ k : ℕ, DifferentiableAt ℝ (iteratedDeriv k m) z := fun k => by
      have h₁ : ContDiff ℝ ((k + 1 : ℕ∞) : WithTop ℕ∞) m := hm.of_le (by simp)
      exact (h₁.differentiable_iteratedDeriv' k).differentiableAt
    -- the derivative of the `j`-th sum, term by term
    have hsumfun : (fun z' : ℝ => ∑ k ∈ Finset.range (j + 1),
          (Work.Spaces.scoef j k : ℝ) * (z' ^ k * iteratedDeriv k m z'))
        = (∑ k ∈ Finset.range (j + 1),
            fun z' : ℝ => (Work.Spaces.scoef j k : ℝ) * (z' ^ k * iteratedDeriv k m z')) := by
      funext z'
      simp [Finset.sum_apply]
    have hderiv : deriv (fun z' : ℝ => ∑ k ∈ Finset.range (j + 1),
          (Work.Spaces.scoef j k : ℝ) * (z' ^ k * iteratedDeriv k m z')) z
        = ∑ k ∈ Finset.range (j + 1), (Work.Spaces.scoef j k : ℝ) *
            ((k : ℝ) * z ^ (k - 1) * iteratedDeriv k m z + z ^ k * iteratedDeriv (k + 1) m z) := by
      rw [hsumfun, deriv_sum (fun k hk => ?_)]
      · refine Finset.sum_congr rfl fun k hk => ?_
        rw [deriv_const_mul_field (Work.Spaces.scoef j k : ℝ)]
        congr 1
        have hmul := deriv_mul (c := fun z' : ℝ => z' ^ k)
          (d := fun z' : ℝ => iteratedDeriv k m z') (differentiableAt_pow k) (hdiff k)
        have hmul' : deriv (fun z' : ℝ => z' ^ k * iteratedDeriv k m z') z
            = deriv (fun z' : ℝ => z' ^ k) z * iteratedDeriv k m z
              + z ^ k * deriv (fun z' : ℝ => iteratedDeriv k m z') z := hmul
        rw [hmul', deriv_zpow,
          show deriv (fun z' : ℝ => iteratedDeriv k m z') z = iteratedDeriv (k + 1) m z from
            (congrFun (iteratedDeriv_succ (n := k) (f := m)) z).symm]
        try ring
      · exact ((differentiableAt_pow k).mul (hdiff k)).const_mul (Work.Spaces.scoef j k : ℝ)
    -- multiply by `z` and collect the terms
    have hzeq : z * deriv (fun z' : ℝ => ∑ k ∈ Finset.range (j + 1),
          (Work.Spaces.scoef j k : ℝ) * (z' ^ k * iteratedDeriv k m z')) z
        = ∑ k ∈ Finset.range (j + 1), (Work.Spaces.scoef j k : ℝ) *
            ((k : ℝ) * z ^ k * iteratedDeriv k m z + z ^ (k + 1) * iteratedDeriv (k + 1) m z) := by
      rw [hderiv, Finset.mul_sum]
      refine Finset.sum_congr rfl fun k hk => ?_
      rw [show z * ((Work.Spaces.scoef j k : ℝ) *
            ((k : ℝ) * z ^ (k - 1) * iteratedDeriv k m z + z ^ k * iteratedDeriv (k + 1) m z))
          = (Work.Spaces.scoef j k : ℝ) * (z *
            ((k : ℝ) * z ^ (k - 1) * iteratedDeriv k m z + z ^ k * iteratedDeriv (k + 1) m z))
          from by ring, z_mul_weighted]
    rw [hzeq]
    have hshift := Work.Spaces.scoef_sum_shift j (fun k => iteratedDeriv k m z) z
    simpa only [] using hshift

/-! ## 3. The weighted derivatives of `1 - χ` are bounded -/

/-- **The weighted derivatives of `1 - χ` are bounded.**  There is a constant `M` dominating
`|x^k ∂_x^k (1 - χ)(x)|` for all `k ≤ 4` and all `x : ℝ`.

For `k = 0` this is `0 ≤ 1 - χ x ≤ 1`.  For `k ≥ 1` the function
`x ↦ x^k (1 - χ)^{(k)}(x) = -x^k χ^{(k)}(x)` is continuous (χ is `C^∞`) and supported in
`|x| ≤ 2` (χ is `1` on `[-1,1]` and `0` off `(-2,2)`), hence bounded. -/
theorem OneSubChi_deriv_bound :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ k ≤ 4, ∀ x : ℝ,
      |x ^ k * iteratedDeriv k (fun x => (1 : ℝ) - Work.Stability.chi x) x| ≤ M := by
  have hsm : ContDiff ℝ Work.Stability.smoothOrder (fun x : ℝ => (1 : ℝ) - Work.Stability.chi x) :=
    contDiff_const.sub Work.Stability.chi_contDiff
  have key : ∀ k ≤ 4, ∃ Mk : ℝ, 0 ≤ Mk ∧
      ∀ x : ℝ, |x ^ k * iteratedDeriv k (fun x : ℝ => (1 : ℝ) - Work.Stability.chi x) x| ≤ Mk := by
    intro k hk4
    rcases Nat.eq_zero_or_pos k with h0 | hpos
    · -- `k = 0`: the bound `|1 - χ x| ≤ 1`
      subst h0
      refine ⟨1, zero_le_one, fun x => ?_⟩
      have hxg : iteratedDeriv 0 (fun x : ℝ => (1 : ℝ) - Work.Stability.chi x) x
          = 1 - Work.Stability.chi x :=
        congrFun (iteratedDeriv_zero (f := fun x : ℝ => (1 : ℝ) - Work.Stability.chi x)) x
      rw [hxg]
      simp only [pow_zero, one_mul]
      rw [abs_le]
      constructor
      · linarith [Work.Stability.chi_le_one x]
      · linarith [Work.Stability.chi_nonneg x]
    · -- `k ≥ 1`: continuity on the compact set `[-2,2]` plus vanishing off `(-2,2)`
      have hcont : Continuous (fun x : ℝ =>
          x ^ k * iteratedDeriv k (fun x : ℝ => (1 : ℝ) - Work.Stability.chi x) x) :=
        (continuous_id.pow k).mul (hsm.continuous_iteratedDeriv k (by simp))
      obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn
        (f := fun x : ℝ => x ^ k * iteratedDeriv k (fun x : ℝ => (1 : ℝ) - Work.Stability.chi x) x)
        hcont.continuousOn
      refine ⟨max C 0, le_max_right _ _, fun x => ?_⟩
      by_cases hx : |x| ≤ 2
      · have hxmem : x ∈ Set.Icc (-2 : ℝ) 2 := by
          rw [Set.mem_Icc, ← abs_le]; exact hx
        have hbound := hC x hxmem
        rw [Real.norm_eq_abs] at hbound
        exact le_trans hbound (le_max_left _ _)
      · -- `|x| > 2`: `χ ≡ 0` on a neighbourhood of `x`, so all its derivatives vanish there
        have hx2 : 2 < |x| := not_le.mp hx
        have hvan : iteratedDeriv k Work.Stability.chi x = 0 := by
          have hev : Work.Stability.chi =ᶠ[𝓝 x] (fun _ => (0 : ℝ)) := by
            have hmem : ∀ᶠ y in 𝓝 x, 2 < |y| :=
              (isOpen_lt continuous_const continuous_abs).mem_nhds (by simpa using hx2)
            filter_upwards [hmem] with y hy
            exact Work.Stability.chi_eq_zero (le_of_lt hy)
          rw [hev.iteratedDeriv_eq k, Work.Spaces.iteratedDeriv_zero_fun k x]
        have hgk : iteratedDeriv k (fun x : ℝ => (1 : ℝ) - Work.Stability.chi x) x
            = - iteratedDeriv k Work.Stability.chi x := by
          rw [iteratedDeriv_const_sub hpos (1 : ℝ)]
          simp
        rw [hgk, hvan]
        simp
  obtain ⟨M0, hM00, hM0⟩ := key 0 (by norm_num)
  obtain ⟨M1, hM10, hM1⟩ := key 1 (by norm_num)
  obtain ⟨M2, hM20, hM2⟩ := key 2 (by norm_num)
  obtain ⟨M3, hM30, hM3⟩ := key 3 (by norm_num)
  obtain ⟨M4, hM40, hM4⟩ := key 4 (by norm_num)
  refine ⟨M0 + M1 + M2 + M3 + M4, by linarith, fun k hk4 x => ?_⟩
  interval_cases k
  · exact le_trans (hM0 x) (by linarith)
  · exact le_trans (hM1 x) (by linarith)
  · exact le_trans (hM2 x) (by linarith)
  · exact le_trans (hM3 x) (by linarith)
  · exact le_trans (hM4 x) (by linarith)

/-! ## 4. The target estimate -/


end Work.FTS.LocData
end
end
-- ===== merged: Submission.Work.FTS.LocData.Gam_le_sin_two_rpow =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The angular weight bound `Γ(θ) ≤ sin(2θ)^{α/5}` on `Iθ`

`Γ(θ) = (sin θ cos²θ)^{α/3}` and, on `Iθ = [0,π/2]`, `sin(2θ) = 2 sin θ cos θ`.  The
pointwise estimate of this file is the elementary angular inequality used to absorb the
factor `Γ` into the weight `sin(2θ)^{-γ/2}` of the `ℋ^k`-integrand (Elgindi, Annals 194(3)
2021, §Notation and §H2).

## Mathematics

Write `A = sin θ · cos²θ` and `b = sin(2θ)`.  On `Iθ` both are nonnegative and `b ≤ 1`.
Since `0 ≤ cos θ ≤ 1`,

* `A = b·cos θ / 2 ≤ b / 2`, hence `A ^ 5 ≤ (b/2) ^ 5 ≤ b ^ 5`;
* `b ^ 5 ≤ b ^ 3` because `0 ≤ b ≤ 1`.

So `A ^ 5 ≤ b ^ 3`.  Raising to the nonnegative power `α/15` and using
`(A ^ 5) ^ (α/15) = A ^ (5·α/15) = A ^ (α/3)`, `(b ^ 3) ^ (α/15) = b ^ (3·α/15) = b ^ (α/5)`
gives `Γ(θ) = A ^ (α/3) ≤ b ^ (α/5) = sin(2θ) ^ (α/5)`.
-/
open scoped Real

namespace Work.FTS.LocData

theorem Gam_le_sin_two_rpow (α : ℝ) (hα : 0 < α) {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) :
    Work.Spaces.Gam α θ ≤ (Real.sin (2 * θ)) ^ (α / 5) := by
  obtain ⟨hθ0, hθ1⟩ := hθ
  have hs0 : 0 ≤ Real.sin θ :=
    Real.sin_nonneg_of_mem_Icc ⟨hθ0, by linarith [hθ1, Real.pi_pos]⟩
  have hc0 : 0 ≤ Real.cos θ :=
    Real.cos_nonneg_of_mem_Icc ⟨by linarith [hθ0, Real.pi_pos], hθ1⟩
  have hc1 : Real.cos θ ≤ 1 := Real.cos_le_one θ
  have hb0 : 0 ≤ Real.sin (2 * θ) := by rw [Real.sin_two_mul]; positivity
  have hb1 : Real.sin (2 * θ) ≤ 1 := Real.sin_le_one _
  have hA0 : 0 ≤ Real.sin θ * Real.cos θ ^ 2 := mul_nonneg hs0 (sq_nonneg _)
  -- `A ≤ sin(2θ)/2`
  have hAs : Real.sin θ * Real.cos θ ^ 2 ≤ Real.sin (2 * θ) / 2 := by
    rw [Real.sin_two_mul]
    have hcs : Real.cos θ ^ 2 ≤ Real.cos θ := by nlinarith [hc0, hc1, sq_nonneg (Real.cos θ)]
    nlinarith [mul_le_mul_of_nonneg_left hcs hs0]
  -- the numerical core: `A ^ 5 ≤ sin(2θ) ^ 3`
  have hA5 : (Real.sin θ * Real.cos θ ^ 2) ^ 5 ≤ (Real.sin (2 * θ)) ^ 3 := by
    have h1 : (Real.sin θ * Real.cos θ ^ 2) ^ 5 ≤ (Real.sin (2 * θ) / 2) ^ 5 :=
      pow_le_pow_left₀ hA0 hAs 5
    have h2 : (Real.sin (2 * θ) / 2) ^ 5 ≤ (Real.sin (2 * θ)) ^ 5 := by
      apply pow_le_pow_left₀ (by positivity)
      linarith
    have h3 : (Real.sin (2 * θ)) ^ 5 ≤ (Real.sin (2 * θ)) ^ 3 :=
      pow_le_pow_of_le_one hb0 hb1 (by norm_num)
    linarith
  have hA5r : (Real.sin θ * Real.cos θ ^ 2) ^ (5:ℝ) ≤ (Real.sin (2 * θ)) ^ (3:ℝ) := by
    simpa using hA5
  -- raise to the power `α/15 ≥ 0`
  have h1 : (Real.sin θ * Real.cos θ ^ 2) ^ (α / 3)
      = ((Real.sin θ * Real.cos θ ^ 2) ^ (5:ℝ)) ^ (α / 15) := by
    rw [← Real.rpow_mul hA0 5 (α / 15), show (5:ℝ) * (α / 15) = α / 3 by ring]
  have h2 : ((Real.sin (2 * θ)) ^ (3:ℝ)) ^ (α / 15) = (Real.sin (2 * θ)) ^ (α / 5) := by
    rw [← Real.rpow_mul hb0 3 (α / 15), show (3:ℝ) * (α / 15) = α / 5 by ring]
  have h3 : ((Real.sin θ * Real.cos θ ^ 2) ^ (5:ℝ)) ^ (α / 15)
      ≤ ((Real.sin (2 * θ)) ^ (3:ℝ)) ^ (α / 15) :=
    Real.rpow_le_rpow (Real.rpow_nonneg hA0 5) hA5r (by linarith)
  rw [← h1, h2] at h3
  simp only [Work.Spaces.Gam]
  exact h3

end Work.FTS.LocData
end
-- ===== merged: Submission.Work.FTS.LocData.HkFstarDefs =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.LocData

set_option autoImplicit false

/-- **The angular polynomials of the `F_*` estimate.**  `Qf i u a` is the polynomial with

  `DthIter i (fun _ θ' => Gam α θ') z θ = Gam α θ * (a * Qf i (cos (2θ)) a)`

for `i ≥ 1` (and `= Gam α θ` for `i = 0`), where `a = α` and `u = cos(2θ)`.
Concretely

* `Qf 0 u a = 1`
* `Qf 1 u a = (3u-1)/3`
* `Qf 2 u a = -2(1-u²) + a(3u-1)²/9`
* `Qf 3 u a = -8u(1-u²) - 6a(u-1/3)(1-u²) + a²(u-1/3)³`
* `Qf 4 u a = 16(1-u²)(1-3u²) + 12a(1-u²)² - 32au(u-1/3)(1-u²)
              - 12a²(u-1/3)²(1-u²) + a³(u-1/3)⁴`. -/
noncomputable def Qf : ℕ → ℝ → ℝ → ℝ
  | 0, u, a => 1
  | 1, u, a => (3 * u - 1) / 3
  | 2, u, a => -2 * (1 - u ^ 2) + a * (3 * u - 1) ^ 2 / 9
  | 3, u, a => -8 * u * (1 - u ^ 2) - 6 * a * (u - 1 / 3) * (1 - u ^ 2)
      + a ^ 2 * (u - 1 / 3) ^ 3
  | 4, u, a => 16 * (1 - u ^ 2) * (1 - 3 * u ^ 2) + 12 * a * (1 - u ^ 2) ^ 2
      - 32 * a * u * (u - 1 / 3) * (1 - u ^ 2) - 12 * a ^ 2 * (u - 1 / 3) ^ 2 * (1 - u ^ 2)
      + a ^ 3 * (u - 1 / 3) ^ 4
  | _, u, a => 0

/-- **The formal `u`-derivative of `Qf`**: `dQf i u a = ∂_u (Qf i · a)`.  It is chosen so that

  `HasDerivAt (fun u => Qf i u a) (dQf i u a) u`

and the recursion `Qf (i+1) u a = -2(1-u²)·dQf i u a + a·Qf 1 u a·Qf i u a` holds. -/
noncomputable def dQf : ℕ → ℝ → ℝ → ℝ
  | 0, u, a => 0
  | 1, u, a => 1
  | 2, u, a => 4 * u + 2 * a * (u - 1 / 3)
  | 3, u, a => 24 * u ^ 2 - 8 + a * (18 * u ^ 2 - 4 * u - 6)
      + 3 * a ^ 2 * (u - 1 / 3) ^ 2
  | 4, u, a => 192 * u ^ 3 - 128 * u
      + a * (176 * u ^ 3 - 32 * u ^ 2 - 112 * u + 32 / 3)
      + a ^ 2 * (-24 * (u - 1 / 3) * (1 + u / 3 - 2 * u ^ 2))
      + 4 * a ^ 3 * (u - 1 / 3) ^ 3
  | _, u, a => 0

@[simp] theorem Qf_zero (u a : ℝ) : Qf 0 u a = 1 := rfl
@[simp] theorem Qf_one (u a : ℝ) : Qf 1 u a = (3 * u - 1) / 3 := rfl
@[simp] theorem Qf_two (u a : ℝ) : Qf 2 u a = -2 * (1 - u ^ 2) + a * (3 * u - 1) ^ 2 / 9 := rfl
@[simp] theorem Qf_three (u a : ℝ) :
    Qf 3 u a = -8 * u * (1 - u ^ 2) - 6 * a * (u - 1 / 3) * (1 - u ^ 2)
      + a ^ 2 * (u - 1 / 3) ^ 3 := rfl
@[simp] theorem Qf_four (u a : ℝ) :
    Qf 4 u a = 16 * (1 - u ^ 2) * (1 - 3 * u ^ 2) + 12 * a * (1 - u ^ 2) ^ 2
      - 32 * a * u * (u - 1 / 3) * (1 - u ^ 2) - 12 * a ^ 2 * (u - 1 / 3) ^ 2 * (1 - u ^ 2)
      + a ^ 3 * (u - 1 / 3) ^ 4 := rfl

@[simp] theorem dQf_zero (u a : ℝ) : dQf 0 u a = 0 := rfl
@[simp] theorem dQf_one (u a : ℝ) : dQf 1 u a = 1 := rfl
@[simp] theorem dQf_two (u a : ℝ) : dQf 2 u a = 4 * u + 2 * a * (u - 1 / 3) := rfl
@[simp] theorem dQf_three (u a : ℝ) :
    dQf 3 u a = 24 * u ^ 2 - 8 + a * (18 * u ^ 2 - 4 * u - 6)
      + 3 * a ^ 2 * (u - 1 / 3) ^ 2 := rfl
@[simp] theorem dQf_four (u a : ℝ) :
    dQf 4 u a = 192 * u ^ 3 - 128 * u
      + a * (176 * u ^ 3 - 32 * u ^ 2 - 112 * u + 32 / 3)
      + a ^ 2 * (-24 * (u - 1 / 3) * (1 + u / 3 - 2 * u ^ 2))
      + 4 * a ^ 3 * (u - 1 / 3) ^ 3 := rfl





/-- `Pf i u a = a · Qf i u a` for `i ≥ 1`, and `Pf 0 = 1`: this is the function such that

  `DthIter i (fun _ θ' => Gam α θ') z θ = Gam α θ * Pf i (cos (2θ)) α`

for every `i ≤ 4`. -/
noncomputable def Pf : ℕ → ℝ → ℝ → ℝ := fun i u a => if i = 0 then 1 else a * Qf i u a

@[simp] theorem Pf_zero (u a : ℝ) : Pf 0 u a = 1 := rfl
theorem Pf_one (u a : ℝ) : Pf 1 u a = a * ((3 * u - 1) / 3) := by
  simp only [Pf, Qf_one, one_ne_zero, ↓reduceIte]
theorem Pf_two (u a : ℝ) : Pf 2 u a = a * (-2 * (1 - u ^ 2) + a * (3 * u - 1) ^ 2 / 9) := by
  simp only [Pf, Qf_two, (by norm_num : (2:ℕ) ≠ 0), ↓reduceIte]
theorem Pf_three (u a : ℝ) : Pf 3 u a = a * (-8 * u * (1 - u ^ 2) - 6 * a * (u - 1 / 3) * (1 - u ^ 2)
      + a ^ 2 * (u - 1 / 3) ^ 3) := by
  simp only [Pf, Qf_three, (by norm_num : (3:ℕ) ≠ 0), ↓reduceIte]
theorem Pf_four (u a : ℝ) : Pf 4 u a = a * (16 * (1 - u ^ 2) * (1 - 3 * u ^ 2) + 12 * a * (1 - u ^ 2) ^ 2
      - 32 * a * u * (u - 1 / 3) * (1 - u ^ 2) - 12 * a ^ 2 * (u - 1 / 3) ^ 2 * (1 - u ^ 2)
      + a ^ 3 * (u - 1 / 3) ^ 4) := by
  simp only [Pf, Qf_four, (by norm_num : (4:ℕ) ≠ 0), ↓reduceIte]

/-- `DzIter` of a function of the form `(z,θ) ↦ A θ * B z` (the `θ`-factor is a constant
for `∂_z`): this is where the product structure of `F_* = α(Γ(θ)/c)·φ(z)` is used. -/
theorem DzIter_mul_theta_factor (j : ℕ) (A : ℝ → ℝ) (B : ℝ → ℝ → ℝ) :
    Work.Spaces.DzIter j (fun z θ => A θ * B z θ) = fun z θ => A θ * Work.Spaces.DzIter j B z θ := by
  induction j with
  | zero => rfl
  | succ j ih =>
      rw [Work.Spaces.DzIter_succ, ih, Work.Spaces.DzIter_succ]
      funext z θ
      simp only [Work.Spaces.Dz, Work.Spaces.pz]
      rw [deriv_const_mul_field]
      ring

/-- **The radial factor** `PhiR i z`: the `z`-part of the `i`-th iterated `D_z`-derivative of
`F_* = α(Γ(θ)/c)·φ(z)`, where `φ = FM.Fstar = 2z/(1+z)²`.  Namely

  `D_z^i φ(z) = PhiR i z / (1+z)^{i+2}`,

with `PhiR i z = 2z·R_i(z)` for the palindromic polynomials
`R_0 = 1`, `R_1 = 1-z`, `R_2 = 1-4z+z²`, `R_3 = 1-11z+11z²-z³`, `R_4 = 1-26z+66z²-26z³+z⁴`. -/
noncomputable def PhiR : ℕ → ℝ → ℝ
  | 0, z => 2 * z
  | 1, z => 2 * z * (1 - z)
  | 2, z => 2 * z * (1 - 4 * z + z ^ 2)
  | 3, z => 2 * z * (1 - 11 * z + 11 * z ^ 2 - z ^ 3)
  | 4, z => 2 * z * (1 - 26 * z + 66 * z ^ 2 - 26 * z ^ 3 + z ^ 4)
  | _, _ => 0

/-- `Phi i z = DzIter i (fun z _ => FM.Fstar z) z θ`, the (θ-independent) `z`-derivative in
normalised form. -/
noncomputable def Phi (i : ℕ) (z θ : ℝ) : ℝ := PhiR i z / (1 + z) ^ (i + 2)

@[simp] theorem PhiR_zero (z : ℝ) : PhiR 0 z = 2 * z := rfl
@[simp] theorem PhiR_one (z : ℝ) : PhiR 1 z = 2 * z * (1 - z) := rfl
@[simp] theorem PhiR_two (z : ℝ) : PhiR 2 z = 2 * z * (1 - 4 * z + z ^ 2) := rfl
@[simp] theorem PhiR_three (z : ℝ) : PhiR 3 z = 2 * z * (1 - 11 * z + 11 * z ^ 2 - z ^ 3) := rfl
@[simp] theorem PhiR_four (z : ℝ) :
    PhiR 4 z = 2 * z * (1 - 26 * z + 66 * z ^ 2 - 26 * z ^ 3 + z ^ 4) := rfl

end Work.FTS.LocData
end
end
-- ===== merged: Submission.Work.FTS.LocData.HkIntegrand_const_mul =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology

namespace Work.FTS.LocData

set_option autoImplicit false

/-! ## Unconditional `deriv`-linearity -/

/-- `deriv` is scalar homogeneous **unconditionally**, unlike Mathlib's `deriv_const_mul`,
which needs differentiability: if `f` is not differentiable at `x` then neither is `c * f`
for `c ≠ 0`, so both sides are `0`. -/
private theorem deriv_const_mul_uncond (c x : ℝ) (f : ℝ → ℝ) :
    deriv (fun y => c * f y) x = c * deriv f x := by
  rcases eq_or_ne c 0 with h | h
  · subst h; simp
  · rcases em (DifferentiableAt ℝ f x) with hf | hf
    · exact deriv_const_mul c hf
    · have h2 : ¬ DifferentiableAt ℝ (fun y => c * f y) x := by
        intro hh
        apply hf
        have he : f = fun y => c⁻¹ * (c * f y) := by
          funext y; rw [← mul_assoc, inv_mul_cancel₀ h, one_mul]
        rw [he]
        exact hh.const_mul c⁻¹
      rw [deriv_zero_of_not_differentiableAt hf,
        deriv_zero_of_not_differentiableAt h2, mul_zero]

/-! ## Pointwise linearity of the differential operators -/

private theorem pz_const_mul (c : ℝ) (f : ℝ → ℝ → ℝ) :
    Work.Spaces.pz (fun z θ => c * f z θ) = fun z θ => c * Work.Spaces.pz f z θ := by
  funext z θ
  simp only [Work.Spaces.pz]
  rw [deriv_const_mul_uncond]

private theorem Dz_const_mul_prv (c : ℝ) (g : ℝ → ℝ → ℝ) :
    Work.Spaces.Dz (fun z θ => c * g z θ) = fun z θ => c * Work.Spaces.Dz g z θ := by
  funext z θ
  simp only [Work.Spaces.Dz]
  rw [pz_const_mul]
  ring

private theorem pth_const_mul (c : ℝ) (f : ℝ → ℝ → ℝ) :
    Work.Spaces.pth (fun z θ => c * f z θ) = fun z θ => c * Work.Spaces.pth f z θ := by
  funext z θ
  simp only [Work.Spaces.pth]
  rw [deriv_const_mul_uncond]

private theorem Dth_const_mul_prv (c : ℝ) (g : ℝ → ℝ → ℝ) :
    Work.Spaces.Dth (fun z θ => c * g z θ) = fun z θ => c * Work.Spaces.Dth g z θ := by
  funext z θ
  simp only [Work.Spaces.Dth]
  rw [pth_const_mul]
  ring

private theorem DzIter_const_mul_prv (i : ℕ) (c : ℝ) (f : ℝ → ℝ → ℝ) :
    Work.Spaces.DzIter i (fun z θ => c * f z θ)
      = fun z θ => c * Work.Spaces.DzIter i f z θ := by
  induction i with
  | zero => rfl
  | succ i ih => simp only [Work.Spaces.DzIter_succ, ih, Dz_const_mul_prv]

private theorem DthIter_const_mul_prv (i : ℕ) (c : ℝ) (f : ℝ → ℝ → ℝ) :
    Work.Spaces.DthIter i (fun z θ => c * f z θ)
      = fun z θ => c * Work.Spaces.DthIter i f z θ := by
  induction i with
  | zero => rfl
  | succ i ih => simp only [Work.Spaces.DthIter_succ, ih, Dth_const_mul_prv]

private theorem mixed_const_mul_prv (j i : ℕ) (c : ℝ) (f : ℝ → ℝ → ℝ) :
    Work.Spaces.mixed j i (fun z θ => c * f z θ)
      = fun z θ => c * Work.Spaces.mixed j i f z θ := by
  simp only [Work.Spaces.mixed, DthIter_const_mul_prv, DzIter_const_mul_prv]

/-! ## The requested pointwise homogeneity -/

theorem HkIntegrand_const_mul (α : ℝ) (k : ℕ) (β : ℝ) (f : ℝ → ℝ → ℝ) (z θ : ℝ) :
    Work.Spaces.HkIntegrand α k (fun z θ => β * f z θ) z θ
      = β ^ 2 * Work.Spaces.HkIntegrand α k f z θ := by
  simp only [Work.Spaces.HkIntegrand, DzIter_const_mul_prv, mixed_const_mul_prv]
  have h1 : (∑ i ∈ Finset.range (k + 1),
        (β * Work.Spaces.DzIter i f z θ
          * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2)
      = β ^ 2 * ∑ i ∈ Finset.range (k + 1),
        (Work.Spaces.DzIter i f z θ
          * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2 := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by ring
  have h2 : (∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1),
        if 1 ≤ i ∧ i + j ≤ k
          then (β * Work.Spaces.mixed j i f z θ * Work.Spaces.Wt α z θ) ^ 2 else 0)
      = β ^ 2 * ∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1),
        if 1 ≤ i ∧ i + j ≤ k
          then (Work.Spaces.mixed j i f z θ * Work.Spaces.Wt α z θ) ^ 2 else 0 := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by split_ifs with h <;> ring
  rw [h1, h2, mul_add]

end Work.FTS.LocData
end
end
-- ===== merged: Submission.Work.FTS.LocData.HkIntegrand_neg =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.LocData

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

/-! ## The calculus of pointwise negation

`deriv` is odd, hence so is each of the operators `pz`, `pth`, `Dz`, `Dth` and each of their
iterates; `mixed j i = D_z^j D_θ^i` then inherits the property. -/


private lemma pz_neg_fun (f : ℝ → ℝ → ℝ) :
    Work.Spaces.pz (fun z θ => -f z θ) = fun z θ => -(Work.Spaces.pz f z θ) := by
  funext z θ
  simp only [Work.Spaces.pz]
  exact deriv.neg

private lemma pth_neg_fun (f : ℝ → ℝ → ℝ) :
    Work.Spaces.pth (fun z θ => -f z θ) = fun z θ => -(Work.Spaces.pth f z θ) := by
  funext z θ
  simp only [Work.Spaces.pth]
  exact deriv.neg

private lemma Dz_neg_fun (f : ℝ → ℝ → ℝ) :
    Work.Spaces.Dz (fun z θ => -f z θ) = fun z θ => -(Work.Spaces.Dz f z θ) := by
  funext z θ
  simp only [Work.Spaces.Dz, pz_neg_fun]
  ring

private lemma Dth_neg_fun (f : ℝ → ℝ → ℝ) :
    Work.Spaces.Dth (fun z θ => -f z θ) = fun z θ => -(Work.Spaces.Dth f z θ) := by
  funext z θ
  simp only [Work.Spaces.Dth, pth_neg_fun]
  ring

private lemma DzIter_neg_fun (f : ℝ → ℝ → ℝ) (n : ℕ) :
    Work.Spaces.DzIter n (fun z θ => -f z θ)
      = fun z θ => -(Work.Spaces.DzIter n f z θ) := by
  induction n with
  | zero => funext z θ; simp
  | succ n ih =>
      rw [Work.Spaces.DzIter_succ, ih, Work.Spaces.DzIter_succ]
      exact Dz_neg_fun (Work.Spaces.DzIter n f)

private lemma DthIter_neg_fun (f : ℝ → ℝ → ℝ) (n : ℕ) :
    Work.Spaces.DthIter n (fun z θ => -f z θ)
      = fun z θ => -(Work.Spaces.DthIter n f z θ) := by
  induction n with
  | zero => funext z θ; simp
  | succ n ih =>
      rw [Work.Spaces.DthIter_succ, ih, Work.Spaces.DthIter_succ]
      exact Dth_neg_fun (Work.Spaces.DthIter n f)

private lemma mixed_neg_fun (f : ℝ → ℝ → ℝ) (j i : ℕ) :
    Work.Spaces.mixed j i (fun z θ => -f z θ)
      = fun z θ => -(Work.Spaces.mixed j i f z θ) := by
  have h1 := DthIter_neg_fun f i
  have h2 := DzIter_neg_fun (Work.Spaces.DthIter i f) j
  simp only [Work.Spaces.mixed]
  rw [h1]
  exact h2

/-! ## The integrand -/

/-- **Sign invariance of the `ℋ^k`-integrand**: replacing `f` by `-f` changes none of the
squares of weighted derivatives out of which `HkIntegrand` is built. -/
theorem HkIntegrand_neg (α : ℝ) (k : ℕ) (f : ℝ → ℝ → ℝ) (z θ : ℝ) :
    Work.Spaces.HkIntegrand α k (fun z θ => -f z θ) z θ
      = Work.Spaces.HkIntegrand α k f z θ := by
  simp only [Work.Spaces.HkIntegrand]
  refine congrArg₂ (· + ·) (Finset.sum_congr rfl fun i _ => ?_)
    (Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_)
  · rw [DzIter_neg_fun]
    ring
  · split_ifs
    · simp only [mixed_neg_fun]; ring
    · ring

end

end Work.FTS.LocData
end
-- ===== merged: Submission.Work.FTS.LocData.HkMem_of_majorant =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.LocData

set_option autoImplicit false

/-- The `θ`-slice of a function continuous on the open quadrant is continuous on `(0,π/2)`.

Stated for a *variable* curried function `G`, so that the composition `G ∘ (z, ·)` is performed
in the abstract (where the reduction `((z,θ)).1 = z` is all that is needed); instantiating `G` at
a concrete partially applied integrand such as `Work.Spaces.HkIntegrand α k f` then costs
nothing, whereas inlining the composition at the concrete integrand forces the elaborator to
unfold the (large) definition of the integrand. -/
theorem continuousOn_slice_theta {G : ℝ → ℝ → ℝ}
    (hG : ContinuousOn (fun p : ℝ × ℝ => G p.1 p.2) (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)))
    {z : ℝ} (hz : 0 < z) : ContinuousOn (fun θ => G z θ) (Set.Ioo 0 (π / 2)) := by
  have h2 : ContinuousOn (fun θ : ℝ => ((z, θ) : ℝ × ℝ)) (Set.Ioo 0 (π / 2)) :=
    continuousOn_const.prodMk
      (continuousOn_id : ContinuousOn (fun θ : ℝ => θ) (Set.Ioo 0 (π / 2)))
  refine hG.comp h2 ?_
  intro θ hθ
  exact ⟨hz, hθ⟩

/-- **The `ℋ^k`-integrand vanishes on the axis `z = 0`** (the radial weight `w z = (1+z)²/z²`
is `0` there, by the junk value of Lean's division, and every term of the integrand carries a
factor `w z`). -/
theorem HkIntegrand_zero_fst (α : ℝ) (k : ℕ) (f : ℝ → ℝ → ℝ) (θ : ℝ) :
    Work.Spaces.HkIntegrand α k f 0 θ = 0 := by
  simp [Work.Spaces.HkIntegrand, Work.Spaces.Wt, Work.Spaces.w]

/-- **Membership in `ℋ^k` by domination.**  If the `ℋ^k`-integrand of `f` is continuous on the
open quadrant, is dominated by `M` on the closed quadrant, and `M` has integrable `θ`-slices and
integrable slice-integral, then `f ∈ ℋ^k`. -/
theorem HkMem_of_majorant (α : ℝ) (k : ℕ) {f M : ℝ → ℝ → ℝ}
    (hcont : ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.HkIntegrand α k f p.1 p.2)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)))
    (hMslice : ∀ z ∈ Work.Spaces.Iz, MeasureTheory.IntegrableOn (fun θ => M z θ) Work.Spaces.Iθ)
    (hMz : MeasureTheory.IntegrableOn (fun z => ∫ θ in Work.Spaces.Iθ, M z θ) Work.Spaces.Iz)
    (hle : ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ,
      Work.Spaces.HkIntegrand α k f z θ ≤ M z θ) :
    Work.Spaces.HkMem α k f := by
  have hIoo : Set.Ioo 0 (π / 2) =ᵐ[volume] Set.Icc 0 (π / 2) :=
    MeasureTheory.Ioo_ae_eq_Icc
  -- Step 1: the `θ`-slices of the integrand are integrable on `Iθ`.
  have hslice : ∀ z ∈ Work.Spaces.Iz,
      IntegrableOn (fun θ => Work.Spaces.HkIntegrand α k f z θ) Work.Spaces.Iθ := by
    intro z hz
    show IntegrableOn (fun θ => Work.Spaces.HkIntegrand α k f z θ) (Set.Icc 0 (π / 2))
    rcases eq_or_lt_of_le (show (0 : ℝ) ≤ z from hz) with h0 | hz0
    · -- `z = 0`: the integrand vanishes identically
      subst h0
      refine IntegrableOn.congr_fun integrableOn_zero (fun θ _ => ?_) measurableSet_Icc
      exact (HkIntegrand_zero_fst α k f θ).symm
    · -- `z > 0`: domination by the (integrable) slice of `M`, plus continuity of the slice
      refine MeasureTheory.IntegrableOn.congr_set_ae ?_ hIoo.symm
      have hMioo : IntegrableOn (fun θ => M z θ) (Set.Ioo 0 (π / 2)) :=
        (hMslice z hz).congr_set_ae hIoo
      have hsl : ContinuousOn (fun θ : ℝ => Work.Spaces.HkIntegrand α k f z θ)
          (Set.Ioo 0 (π / 2)) :=
        continuousOn_slice_theta (G := Work.Spaces.HkIntegrand α k f) hcont hz0
      refine MeasureTheory.Integrable.mono' hMioo
        (hsl.aestronglyMeasurable measurableSet_Ioo) ?_
      have hbnd : ∀ᵐ θ ∂(volume.restrict (Set.Ioo 0 (π / 2))),
          ‖Work.Spaces.HkIntegrand α k f z θ‖ ≤ M z θ := by
        rw [MeasureTheory.ae_restrict_iff' (s := Set.Ioo 0 (π / 2)) measurableSet_Ioo]
        refine Filter.Eventually.of_forall fun θ hθ => ?_
        rw [Real.norm_eq_abs, abs_of_nonneg (Work.Spaces.HkIntegrand_nonneg α k f z θ)]
        exact hle z hz θ ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩
      exact hbnd
  -- Step 2: the `z`-integral of the slices is integrable on `Iz`.
  have houter : IntegrableOn
      (fun z => ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k f z θ) Work.Spaces.Iz := by
    have hKnn : ∀ z ∈ Work.Spaces.Iz,
        0 ≤ (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k f z θ) :=
      fun z _ => integral_nonneg fun θ => Work.Spaces.HkIntegrand_nonneg α k f z θ
    have hKle : ∀ z ∈ Work.Spaces.Iz,
        (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k f z θ)
          ≤ ∫ θ in Work.Spaces.Iθ, M z θ := by
      intro z hz
      have hle_ae : ∀ᵐ θ ∂(volume.restrict Work.Spaces.Iθ),
          Work.Spaces.HkIntegrand α k f z θ ≤ M z θ := by
        rw [MeasureTheory.ae_restrict_iff' (s := Work.Spaces.Iθ) measurableSet_Icc]
        exact Filter.Eventually.of_forall fun θ hθ => hle z hz θ hθ
      exact MeasureTheory.integral_mono_of_nonneg
        (Filter.Eventually.of_forall fun θ => Work.Spaces.HkIntegrand_nonneg α k f z θ)
        (hMslice z hz) hle_ae
    refine MeasureTheory.Integrable.mono' hMz ?_ ?_
    · -- measurability of the slice-integral, by Fubini on the open quadrant
      have hprod : AEStronglyMeasurable
          (fun p : ℝ × ℝ => Work.Spaces.HkIntegrand α k f p.1 p.2)
          ((volume.restrict (Set.Ioi 0)).prod (volume.restrict (Set.Ioo 0 (π / 2)))) := by
        rw [MeasureTheory.Measure.prod_restrict, ← MeasureTheory.Measure.volume_eq_prod ℝ ℝ]
        exact hcont.aestronglyMeasurable (isOpen_Ioi.prod isOpen_Ioo).measurableSet
      have h1 : AEStronglyMeasurable (fun z => ∫ θ in Set.Ioo 0 (π / 2),
          Work.Spaces.HkIntegrand α k f z θ) (volume.restrict (Set.Ioi 0)) :=
        hprod.integral_prod_right'
      have h2 : AEStronglyMeasurable (fun z => ∫ θ in Set.Ioo 0 (π / 2),
          Work.Spaces.HkIntegrand α k f z θ) (volume.restrict Work.Spaces.Iz) := by
        rw [Work.Spaces.Iz, ← MeasureTheory.restrict_Ioi_eq_restrict_Ici (a := (0 : ℝ))]
        exact h1
      have hfun : (fun z => ∫ θ in Set.Ioo 0 (π / 2), Work.Spaces.HkIntegrand α k f z θ)
          = fun z => ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k f z θ := by
        funext z
        exact MeasureTheory.setIntegral_congr_set hIoo
      rw [← hfun]
      exact h2
    · -- the a.e. domination by `∫_θ M z θ`
      have hbnd : ∀ᵐ z ∂(volume.restrict Work.Spaces.Iz),
          ‖∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k f z θ‖
            ≤ ∫ θ in Work.Spaces.Iθ, M z θ := by
        rw [MeasureTheory.ae_restrict_iff' (s := Work.Spaces.Iz) measurableSet_Ici]
        refine Filter.Eventually.of_forall fun z hz => ?_
        rw [Real.norm_eq_abs, abs_of_nonneg (hKnn z hz)]
        exact hKle z hz
      exact hbnd
  exact ⟨hslice, houter⟩

end Work.FTS.LocData
end
end
-- ===== merged: Submission.Work.FTS.LocData.L12_add_mul =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.LocData

set_option autoImplicit false

/-- **Additivity of the angular density of `L₁₂`.**  For an arbitrary angular profile `K`, if the
two `θ`-slices `θ ↦ K θ f(s,θ)/s` are integrable on `Iθ = [0,π/2]`, then the density of the sum
is the sum of the densities (the integrands are pointwise equal by distributivity). -/
theorem L12dens_add_of_integrableOn (K : ℝ → ℝ) {a b : ℝ → ℝ → ℝ} {s : ℝ}
    (ha : MeasureTheory.IntegrableOn (fun θ => K θ * a s θ / s) Work.Spaces.Iθ)
    (hb : MeasureTheory.IntegrableOn (fun θ => K θ * b s θ / s) Work.Spaces.Iθ) :
    Work.FM.L12dens K (fun z θ => a z θ + b z θ) s
      = Work.FM.L12dens K a s + Work.FM.L12dens K b s := by
  have hpt : (fun θ => K θ * (a s θ + b s θ) / s)
      = fun θ => K θ * a s θ / s + K θ * b s θ / s := by
    funext θ
    ring
  simp only [Work.FM.L12dens]
  rw [hpt]
  exact MeasureTheory.integral_add ha hb

/-- **Homogeneity of the angular density of `L₁₂`.**  For an arbitrary angular profile `K` and
constant `c` the density of `c·a` is `c` times the density of `a`, with no integrability
hypothesis at all: both sides are the integral of the pointwise-equal integrands, and
`MeasureTheory.integral_const_mul` is unconditional. -/
theorem L12dens_const_mul (K : ℝ → ℝ) (c : ℝ) (a : ℝ → ℝ → ℝ) (s : ℝ) :
    Work.FM.L12dens K (fun z θ => c * a z θ) s = c * Work.FM.L12dens K a s := by
  have hpt : (fun θ => K θ * (c * a s θ) / s) = fun θ => c * (K θ * a s θ / s) := by
    funext θ
    ring
  simp only [Work.FM.L12dens]
  rw [hpt]
  exact MeasureTheory.integral_const_mul c _

/-- **Linearity of `L₁₂` on the localised data:** it is additive, and homogeneous in a constant.

`h1`, `h2` are the integrability of the two angular slices on `Iθ` for every `s > z` (this is
what makes the inner integrals split), and `h3`, `h4` the integrability of the two densities on
`(z,∞)` (this is what makes the outer integrals split; the additive identity of the densities
holds merely pointwise on `(z,∞)`, no integrability of the density of the sum is needed).  The
homogeneity statement needs no hypothesis beyond `h1`'s shape of the integrand. -/
theorem L12_add_mul (c : ℝ) {a b : ℝ → ℝ → ℝ} {z : ℝ}
    (h1 : ∀ s ∈ Set.Ioi z, MeasureTheory.IntegrableOn
      (fun θ => Work.Spaces.K θ * a s θ / s) Work.Spaces.Iθ)
    (h2 : ∀ s ∈ Set.Ioi z, MeasureTheory.IntegrableOn
      (fun θ => Work.Spaces.K θ * b s θ / s) Work.Spaces.Iθ)
    (h3 : MeasureTheory.IntegrableOn (Work.FM.L12dens Work.Spaces.K a) (Set.Ioi z))
    (h4 : MeasureTheory.IntegrableOn (Work.FM.L12dens Work.Spaces.K b) (Set.Ioi z)) :
    Work.Construction.L12 (fun z θ => a z θ + b z θ) z
        = Work.Construction.L12 a z + Work.Construction.L12 b z ∧
      Work.Construction.L12 (fun z θ => c * a z θ) z = c * Work.Construction.L12 a z := by
  constructor
  · -- additivity: split the inner integral pointwise, then the outer one by integrability
    simp only [Work.Construction.L12, Work.FM.L12]
    rw [MeasureTheory.setIntegral_congr_fun measurableSet_Ioi
      (fun s hs => L12dens_add_of_integrableOn Work.Spaces.K (h1 s hs) (h2 s hs))]
    exact MeasureTheory.integral_add h3 h4
  · -- homogeneity: pull the constant out of the inner and then the outer integral
    simp only [Work.Construction.L12, Work.FM.L12]
    rw [MeasureTheory.setIntegral_congr_fun measurableSet_Ioi
      (fun s _ => L12dens_const_mul Work.Spaces.K c a s)]
    exact MeasureTheory.integral_const_mul c _

end Work.FTS.LocData
end
-- ===== merged: Submission.Work.FTS.LocData.L12_hLoc =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.LocData

set_option autoImplicit false

/-! ## The two support facts for `bumpZ = χ(4·-5)` -/

/-- `bumpZ` vanishes off the interval `(3/4, 7/4)`, i.e. outside the set where `|4s - 5| < 2`. -/
theorem bumpZ_eq_zero_of_notMem {s : ℝ} (hs : s ∉ Set.Icc (3/4) (7/4)) : bumpZ s = 0 := by
  rw [bumpZ_apply]
  apply Work.Stability.chi_eq_zero
  have hs' : ¬(3/4 ≤ s ∧ s ≤ 7/4) := hs
  rcases not_and_or.mp hs' with h | h
  · rw [not_le] at h
    have h2 : 4 * s - 5 < -2 := by linarith
    rw [abs_of_neg (by linarith)]
    linarith
  · rw [not_le] at h
    have h2 : 2 < 4 * s - 5 := by linarith
    rw [abs_of_pos (by linarith)]
    linarith

/-- `bumpZ = 1` on `[1, 3/2]`, the flat top of the bump. -/
theorem bumpZ_eq_one_of_mem {s : ℝ} (hs : s ∈ Set.Icc (1 : ℝ) (3/2)) : bumpZ s = 1 := by
  rw [bumpZ_apply]
  apply Work.Stability.chi_eq_one
  rw [abs_le]
  exact ⟨by linarith [hs.1], by linarith [hs.2]⟩

/-- `bumpZ` is continuous. -/
theorem continuous_bumpZ : Continuous bumpZ :=
  Work.Stability.chi_continuous.comp (by fun_prop)

/-! ## Positivity of the radial integral -/

/-- **The radial normalisation integral is positive**: `∫_0^∞ bumpZ(s)/s ds > 0`.

The integrand is nonnegative, compactly supported (in `(3/4, 7/4)`) and equals `1/s ≥ 2/3` on
the interval `[1, 3/2]`, so the integral is at least `(2/3)·(1/2) = 1/3 > 0`. -/
theorem bumpInt_pos : 0 < ∫ s in Set.Ioi (0 : ℝ), bumpZ s / s := by
  set f : ℝ → ℝ := fun s => bumpZ s / s with hf
  -- the integrand is integrable on `(3/4, 7/4)`, where it is continuous
  have hf_int_Icc : IntegrableOn f (Set.Icc (3/4) (7/4)) := by
    refine ContinuousOn.integrableOn_Icc ?_
    rw [hf]
    exact continuous_bumpZ.continuousOn.div continuousOn_id
      (fun s hs => ne_of_gt (by linarith [hs.1]))
  -- ... and vanishes off that interval, hence is integrable on `ℝ`
  have hf_ind : f = (Set.Icc (3/4) (7/4)).indicator f := by
    funext s
    by_cases hs : s ∈ Set.Icc (3/4) (7/4)
    · rw [Set.indicator_of_mem hs]
    · rw [Set.indicator_of_notMem hs]
      show f s = 0
      simp only [hf]
      rw [bumpZ_eq_zero_of_notMem hs, zero_div]
  have hf_int : Integrable f volume := by
    rw [hf_ind]
    exact (integrable_indicator_iff measurableSet_Icc).mpr hf_int_Icc
  have hf_int_on : IntegrableOn f (Set.Ioi (0 : ℝ)) := hf_int.integrableOn
  have hf_nn : 0 ≤ᵐ[volume.restrict (Set.Ioi (0 : ℝ))] f := by
    rw [Filter.EventuallyLE, ae_restrict_iff' measurableSet_Ioi]
    exact Filter.Eventually.of_forall (fun s hs => by
      simp only [hf, bumpZ_apply, Pi.zero_apply]
      exact div_nonneg (Work.Stability.chi_nonneg _) (le_of_lt hs))
  rw [setIntegral_pos_iff_support_of_nonneg_ae hf_nn hf_int_on]
  -- the support of `f` meets `(0,∞)` in the set of positive measure `[1, 3/2]`
  have hsub : Set.Icc (1 : ℝ) (3/2) ⊆ Function.support f ∩ Set.Ioi 0 := by
    intro s hs
    refine ⟨?_, ?_⟩
    · rw [Function.mem_support]
      simp only [hf]
      rw [bumpZ_eq_one_of_mem hs, one_div]
      exact inv_ne_zero (ne_of_gt (by linarith [hs.1]))
    · simp only [Set.mem_Ioi]; linarith [hs.1]
  have hvol : 0 < volume (Set.Icc (1 : ℝ) (3/2)) := by
    rw [Real.volume_Icc]
    rw [show (3 : ℝ)/2 - 1 = 1/2 by norm_num]
    exact ENNReal.ofReal_pos.mpr (by norm_num)
  exact lt_of_lt_of_le hvol (measure_mono hsub)

/-! ## The angular density of `hLoc` -/

/-- **The angular density of the bump is the radial factor times `c(α)`**:
`L₁₂dens(hLoc α)(s) = (bumpZ(s)/s)·c(α)`.  This is separability of the integrand
`K(θ)·bumpZ(s)Γ(θ)/s` plus the definition of `c(α)`. -/
theorem L12dens_hLoc (α s : ℝ) :
    Work.FM.L12dens Work.Spaces.K (hLoc α) s = (bumpZ s / s) * Work.Spaces.c α := by
  simp only [Work.FM.L12dens, Work.Spaces.c, Work.Spaces.Iθ]
  rw [show (∫ θ in Set.Icc (0 : ℝ) (π/2), Work.Spaces.K θ * hLoc α s θ / s)
      = ∫ θ in Set.Icc (0 : ℝ) (π/2),
          (bumpZ s / s) * (Work.Spaces.K θ * Work.Spaces.Gam α θ) from
    setIntegral_congr_fun measurableSet_Icc
      (fun θ _ => by rw [hLoc_apply, div_eq_mul_inv]; ring)]
  rw [MeasureTheory.integral_const_mul]
  congr 1
  exact setIntegral_congr_fun measurableSet_Icc (fun θ _ => by ring)

/-! ## The target -/

theorem L12_hLoc (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) :
    Work.Construction.L12 (hLoc α) 0
        = Work.Spaces.c α * (∫ s in Set.Ioi (0 : ℝ), bumpZ s / s) ∧
      0 < Work.Construction.L12 (hLoc α) 0 := by
  have hI : 0 < ∫ s in Set.Ioi (0 : ℝ), bumpZ s / s := bumpInt_pos
  have hc : 0 < Work.Spaces.c α := by
    have h := (Work.Spaces.c_bounds α hα hα1).1
    linarith
  have hEq : Work.Construction.L12 (hLoc α) 0
      = Work.Spaces.c α * (∫ s in Set.Ioi (0 : ℝ), bumpZ s / s) := by
    simp only [Work.Construction.L12, Work.FM.L12]
    rw [show (∫ s in Set.Ioi (0 : ℝ), Work.FM.L12dens Work.Spaces.K (hLoc α) s)
        = ∫ s in Set.Ioi (0 : ℝ), (bumpZ s / s) * Work.Spaces.c α from
      setIntegral_congr_fun measurableSet_Ioi (fun s _ => L12dens_hLoc α s)]
    rw [MeasureTheory.integral_mul_const]
    exact mul_comm _ _
  exact ⟨hEq, by rw [hEq]; exact mul_pos hc hI⟩

end Work.FTS.LocData
end
end
-- ===== merged: Submission.Work.FTS.LocData.L12_zfar_Fstar_abs_le =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.LocData

set_option autoImplicit false

/-! ## The `L₁₂`-density of the far part -/

/-- The angular density of `L₁₂` at the far part `zfar L F_*`: the radial factor
`1 - χ(s/L)` of the cut-off comes out of the angular integral, so that the density of the far
part is that of `F_*` multiplied by that factor. -/
theorem L12dens_zfar_Fstar (α : ℝ) (L s : ℝ) :
    Work.FM.L12dens Work.Spaces.K (Work.Stability.zfar L (Work.Construction.Fstar α)) s
      = (1 - Work.Stability.chi (s / L)) *
          Work.Construction.L12dens (Work.Construction.Fstar α) s := by
  rw [Work.Construction.L12dens, Work.FM.L12dens, Work.FM.L12dens]
  have hpoint : Set.EqOn
      (fun θ => Work.Spaces.K θ * (Work.Stability.zfar L (Work.Construction.Fstar α)) s θ / s)
      (fun θ => (1 - Work.Stability.chi (s / L)) *
        (Work.Spaces.K θ * Work.Construction.Fstar α s θ / s))
      (Set.Icc 0 (Real.pi / 2)) := by
    intro θ _
    show Work.Spaces.K θ * Work.Stability.zfar L (Work.Construction.Fstar α) s θ / s
      = (1 - Work.Stability.chi (s / L)) *
          (Work.Spaces.K θ * Work.Construction.Fstar α s θ / s)
    rw [Work.Stability.zfar_apply]
    ring
  rw [MeasureTheory.setIntegral_congr_fun measurableSet_Icc hpoint]
  rw [MeasureTheory.integral_const_mul]

/-- **`L₁₂` of the far part of the profile at `z = 0`.**  Using
`L₁₂dens (F_*) = α·F_*(s)/s` (`Work.Construction.L12dens_Fstar`) the whole operator collapses
to the elementary integral `α ∫_0^∞ (1 - χ(s/L))·F_*(s)/s ds`. -/
theorem L12_zfar_Fstar_eq (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) (L : ℝ) :
    Work.Construction.L12 (Work.Stability.zfar L (Work.Construction.Fstar α)) 0
      = α * ∫ s in Set.Ioi (0 : ℝ),
          (1 - Work.Stability.chi (s / L)) * (Work.FM.Fstar s / s) := by
  rw [Work.Construction.L12, Work.FM.L12]
  rw [MeasureTheory.setIntegral_congr_fun measurableSet_Ioi
    (fun s _ => L12dens_zfar_Fstar α L s)]
  rw [MeasureTheory.setIntegral_congr_fun measurableSet_Ioi
    (fun s _ => by rw [Work.Construction.L12dens_Fstar hα hα1 s])]
  rw [show (fun s : ℝ => (1 - Work.Stability.chi (s / L)) * (α * (Work.FM.Fstar s / s)))
      = (fun s : ℝ => α * ((1 - Work.Stability.chi (s / L)) * (Work.FM.Fstar s / s)))
      from funext fun s => by ring]
  rw [MeasureTheory.integral_const_mul]

/-! ## The cut-off integral estimate -/

/-- **The far-part integral is of order `1/L`.**  For `1 ≤ L` the integral
`∫_0^∞ (1 - χ(s/L))·F_*(s)/s ds` is nonnegative and at most `2/(1+L)`: the integrand vanishes
for `s ≤ L` (`χ(s/L) = 1` there) and is dominated by `F_*(s)/s = 2/(1+s)²` for `s ≥ L`, whose
tail integral is `2/(1+L)`. -/
theorem zfar_cut_integral_bounds {L : ℝ} (hL : 1 ≤ L) :
    0 ≤ ∫ s in Set.Ioi (0 : ℝ), (1 - Work.Stability.chi (s / L)) * (Work.FM.Fstar s / s) ∧
      ∫ s in Set.Ioi (0 : ℝ), (1 - Work.Stability.chi (s / L)) * (Work.FM.Fstar s / s)
        ≤ 2 / (1 + L) := by
  have hL0 : (0 : ℝ) < L := by linarith
  -- the elementary form of the density on `s > 0`
  have hFstar : ∀ s ∈ Set.Ioi (0 : ℝ), Work.FM.Fstar s / s = 2 / (s + 1) ^ 2 := by
    intro s hs
    have hs0 : (0 : ℝ) < s := hs
    rw [Work.FM.Fstar]
    field_simp
    ring_nf
  constructor
  · -- nonnegativity of the integrand
    refine MeasureTheory.setIntegral_nonneg measurableSet_Ioi (fun s hs => ?_)
    have h1 : 0 ≤ 1 - Work.Stability.chi (s / L) := by
      linarith [Work.Stability.chi_le_one (s / L)]
    have h2 : 0 ≤ Work.FM.Fstar s / s := by
      rw [hFstar s hs]
      positivity
    exact mul_nonneg h1 h2
  · -- the integrand is supported on `(L, ∞)` and dominated there by `2/(1+s)²`
    have hsupp : ∀ s ∈ Set.Ioi (0 : ℝ),
        (1 - Work.Stability.chi (s / L)) * (2 / (s + 1) ^ 2)
          = (Set.Ioi L).indicator
              (fun s : ℝ => (1 - Work.Stability.chi (s / L)) * (2 / (s + 1) ^ 2)) s := by
      intro s hs
      by_cases hmem : s ∈ Set.Ioi L
      · rw [Set.indicator_of_mem hmem]
      · rw [Set.indicator_of_notMem hmem]
        have hsL : s ≤ L := le_of_not_gt hmem
        have h1 : s / L ≤ 1 := by
          rw [div_le_one hL0]
          exact hsL
        have h2 : -(1 : ℝ) ≤ s / L := by
          have : (0 : ℝ) ≤ s / L := div_nonneg (le_of_lt (show (0 : ℝ) < s from hs)) hL0.le
          linarith
        have hchi : Work.Stability.chi (s / L) = 1 :=
          Work.Stability.chi_eq_one (abs_le.mpr ⟨h2, h1⟩)
        rw [hchi]
        ring
    have step1 : ∫ s in Set.Ioi (0 : ℝ),
          (1 - Work.Stability.chi (s / L)) * (Work.FM.Fstar s / s)
        = ∫ s in Set.Ioi (0 : ℝ), (Set.Ioi L).indicator
            (fun s : ℝ => (1 - Work.Stability.chi (s / L)) * (2 / (s + 1) ^ 2)) s := by
      refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioi (fun s hs => ?_)
      rw [hFstar s hs]
      exact hsupp s hs
    have step2 : ∫ s in Set.Ioi (0 : ℝ), (Set.Ioi L).indicator
          (fun s : ℝ => (1 - Work.Stability.chi (s / L)) * (2 / (s + 1) ^ 2)) s
        = ∫ s in Set.Ioi L, (1 - Work.Stability.chi (s / L)) * (2 / (s + 1) ^ 2) := by
      rw [MeasureTheory.setIntegral_indicator measurableSet_Ioi]
      rw [show Set.Ioi (0 : ℝ) ∩ Set.Ioi L = Set.Ioi L from
        Set.inter_eq_right.mpr (Set.Ioi_subset_Ioi hL0.le)]
    have hint : MeasureTheory.IntegrableOn (fun s : ℝ => 2 / (s + 1) ^ 2) (Set.Ioi L) := by
      have h1 : MeasureTheory.IntegrableOn (fun s : ℝ => 2 * (s + 1) ^ (-2 : ℝ)) (Set.Ioi L) :=
        (integrableOn_add_rpow_Ioi_of_lt (a := -2) (c := L) (m := 1) (by norm_num)
          (by linarith)).integrable.const_mul 2
      refine h1.congr_fun (fun s hs => ?_) measurableSet_Ioi
      have hs1 : (0 : ℝ) < s + 1 := by
        have hsL : L < s := hs
        linarith
      have h : (s + 1) ^ (-2 : ℝ) = 1 / (s + 1) ^ 2 := by
        simp only [Real.rpow_neg hs1.le, Real.rpow_ofNat, one_div]
      show 2 * (s + 1) ^ (-2 : ℝ) = 2 / (s + 1) ^ 2
      rw [h]
      ring_nf
    have step3 : ∫ s in Set.Ioi L, (1 - Work.Stability.chi (s / L)) * (2 / (s + 1) ^ 2)
        ≤ ∫ s in Set.Ioi L, 2 / (s + 1) ^ 2 := by
      refine MeasureTheory.setIntegral_mono_of_nonneg (fun s _ => ?_) (fun s _ => ?_) hint
      · have h1 : 0 ≤ 1 - Work.Stability.chi (s / L) := by
          linarith [Work.Stability.chi_le_one (s / L)]
        exact mul_nonneg h1 (by positivity)
      · have h1 : 1 - Work.Stability.chi (s / L) ≤ 1 := by
          linarith [Work.Stability.chi_nonneg (s / L)]
        exact mul_le_of_le_one_left (by positivity) h1
    have step4 : ∫ s in Set.Ioi L, 2 / (s + 1) ^ 2 = 2 / (1 + L) := by
      rw [← Work.FM.integral_Ioi_Fstar_div L hL0.le]
      refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioi (fun s hs => ?_)
      have hs0 : (0 : ℝ) < s := by
        have hsL : L < s := hs
        linarith
      rw [hFstar s (show s ∈ Set.Ioi (0 : ℝ) from hs0)]
    calc ∫ s in Set.Ioi (0 : ℝ), (1 - Work.Stability.chi (s / L)) * (Work.FM.Fstar s / s)
        = ∫ s in Set.Ioi (0 : ℝ), (Set.Ioi L).indicator
            (fun s : ℝ => (1 - Work.Stability.chi (s / L)) * (2 / (s + 1) ^ 2)) s := step1
      _ = ∫ s in Set.Ioi L, (1 - Work.Stability.chi (s / L)) * (2 / (s + 1) ^ 2) := step2
      _ ≤ ∫ s in Set.Ioi L, 2 / (s + 1) ^ 2 := step3
      _ = 2 / (1 + L) := step4

/-! ## The bound -/

theorem L12_zfar_Fstar_abs_le (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) {L : ℝ} (hL : 1 ≤ L) :
    |Work.Construction.L12 (Work.Stability.zfar L (Work.Construction.Fstar α)) 0| ≤ 4 * α / L := by
  obtain ⟨h0, hle⟩ := zfar_cut_integral_bounds hL
  rw [L12_zfar_Fstar_eq α hα hα1 L, abs_mul, abs_of_pos hα, abs_of_nonneg h0]
  have h1 : α * (∫ s in Set.Ioi (0 : ℝ),
        (1 - Work.Stability.chi (s / L)) * (Work.FM.Fstar s / s)) ≤ α * (2 / (1 + L)) :=
    mul_le_mul_of_nonneg_left hle hα.le
  have h2 : α * (2 / (1 + L)) ≤ 4 * α / L := by
    rw [show α * (2 / (1 + L)) = 2 * α / (1 + L) by ring]
    exact div_le_div₀ (by linarith : (0 : ℝ) ≤ 4 * α) (by linarith : 2 * α ≤ 4 * α)
      (by linarith : (0 : ℝ) < L) (by linarith : L ≤ 1 + L)
  linarith

end Work.FTS.LocData
end
end
-- ===== merged: Submission.Work.FTS.LocData.SmoothChain =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.LocData

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 800000

/-- The open quadrant `(0,∞) × (0,π/2)`, on which the `ℋ^k`-weights are continuous. -/
abbrev Qd : Set (ℝ × ℝ) := Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)

theorem isOpen_quadU : IsOpen Work.Spaces.quadU := Work.Spaces.isOpen_quadU

/-! ## `D_z` and `D_θ` preserve `C^∞`-smoothness -/

/-- `Work.Spaces.pz` preserves `C^∞`-smoothness on an open set.  (The `⊤`-statement is
`Work.Spaces.contDiffOn_uncurry_pz`; this is the genuine smooth order.) -/
theorem contDiffOn_pz {G : ℝ → ℝ → ℝ} {V : Set (ℝ × ℝ)} (hV : IsOpen V)
    (h : ContDiffOn ℝ Work.Stability.smoothOrder (Function.uncurry G) V) :
    ContDiffOn ℝ Work.Stability.smoothOrder (Function.uncurry (Work.Spaces.pz G)) V := by
  have hchain : ∀ p ∈ V, Work.Spaces.pz G p.1 p.2
      = fderiv ℝ (Function.uncurry G) p (1, 0) := fun p hp =>
    Work.Spaces.pz_eq_fderiv ((h.differentiableOn (n := Work.Stability.smoothOrder)
      (by simp)).differentiableAt (hV.mem_nhds hp))
  have hfd : ContDiffOn ℝ Work.Stability.smoothOrder
      (fun (p : ℝ × ℝ) => fderiv ℝ (Function.uncurry G) p) V := by
    have h' := h.fderivWithin (m := Work.Stability.smoothOrder) hV.uniqueDiffOn le_rfl
    refine h'.congr ?_
    intro p hp
    rw [fderivWithin_of_isOpen hV hp]
  have hcomp : ContDiffOn ℝ Work.Stability.smoothOrder
      (fun (p : ℝ × ℝ) => (fderiv ℝ (Function.uncurry G) p) (1, 0)) V := by
    simpa using hfd.clm_apply contDiffOn_const
  exact hcomp.congr hchain

/-- `Work.Spaces.pth` preserves `C^∞`-smoothness on an open set, with the genuine smooth order. -/
theorem contDiffOn_pth {G : ℝ → ℝ → ℝ} {V : Set (ℝ × ℝ)} (hV : IsOpen V)
    (h : ContDiffOn ℝ Work.Stability.smoothOrder (Function.uncurry G) V) :
    ContDiffOn ℝ Work.Stability.smoothOrder (Function.uncurry (Work.Spaces.pth G)) V := by
  have hchain : ∀ p ∈ V, Work.Spaces.pth G p.1 p.2
      = fderiv ℝ (Function.uncurry G) p (0, 1) := fun p hp =>
    Work.Spaces.pth_eq_fderiv ((h.differentiableOn (n := Work.Stability.smoothOrder)
      (by simp)).differentiableAt (hV.mem_nhds hp))
  have hfd : ContDiffOn ℝ Work.Stability.smoothOrder
      (fun (p : ℝ × ℝ) => fderiv ℝ (Function.uncurry G) p) V := by
    have h' := h.fderivWithin (m := Work.Stability.smoothOrder) hV.uniqueDiffOn le_rfl
    refine h'.congr ?_
    intro p hp
    rw [fderivWithin_of_isOpen hV hp]
  have hcomp : ContDiffOn ℝ Work.Stability.smoothOrder
      (fun (p : ℝ × ℝ) => (fderiv ℝ (Function.uncurry G) p) (0, 1)) V := by
    simpa using hfd.clm_apply contDiffOn_const
  exact hcomp.congr hchain

/-- `Work.Spaces.Dz` preserves `C^∞`-smoothness on an open set. -/
theorem contDiffOn_Dz {G : ℝ → ℝ → ℝ} {V : Set (ℝ × ℝ)} (hV : IsOpen V)
    (h : ContDiffOn ℝ Work.Stability.smoothOrder (Function.uncurry G) V) :
    ContDiffOn ℝ Work.Stability.smoothOrder (Function.uncurry (Work.Spaces.Dz G)) V := by
  have hfun : Function.uncurry (Work.Spaces.Dz G)
      = fun p : ℝ × ℝ => p.1 * Function.uncurry (Work.Spaces.pz G) p := by
    funext p; rcases p with ⟨z, θ⟩; rfl
  rw [hfun]
  exact contDiffOn_fst.mul (contDiffOn_pz hV h)

/-- `Work.Spaces.Dth` preserves `C^∞`-smoothness on an open set. -/
theorem contDiffOn_Dth {G : ℝ → ℝ → ℝ} {V : Set (ℝ × ℝ)} (hV : IsOpen V)
    (h : ContDiffOn ℝ Work.Stability.smoothOrder (Function.uncurry G) V) :
    ContDiffOn ℝ Work.Stability.smoothOrder (Function.uncurry (Work.Spaces.Dth G)) V := by
  have hfun : Function.uncurry (Work.Spaces.Dth G)
      = fun p : ℝ × ℝ => Real.sin (2 * p.2) * Function.uncurry (Work.Spaces.pth G) p := by
    funext p; rcases p with ⟨z, θ⟩; rfl
  rw [hfun]
  have hsin : ContDiffOn ℝ Work.Stability.smoothOrder
      (fun p : ℝ × ℝ => Real.sin (2 * p.2)) V :=
    (Real.contDiff_sin.comp (contDiff_const.mul contDiff_snd)).contDiffOn
  exact hsin.mul (contDiffOn_pth hV h)

/-- `D_z^i` preserves `C^∞`-smoothness on an open set. -/
theorem contDiffOn_DzIter {G : ℝ → ℝ → ℝ} {V : Set (ℝ × ℝ)} (hV : IsOpen V)
    (h : ContDiffOn ℝ Work.Stability.smoothOrder (Function.uncurry G) V) (i : ℕ) :
    ContDiffOn ℝ Work.Stability.smoothOrder (Function.uncurry (Work.Spaces.DzIter i G)) V := by
  induction i with
  | zero => simpa using h
  | succ i ih =>
      rw [Work.Spaces.DzIter_succ]
      exact contDiffOn_Dz hV ih

/-- `D_θ^i` preserves `C^∞`-smoothness on an open set. -/
theorem contDiffOn_DthIter {G : ℝ → ℝ → ℝ} {V : Set (ℝ × ℝ)} (hV : IsOpen V)
    (h : ContDiffOn ℝ Work.Stability.smoothOrder (Function.uncurry G) V) (i : ℕ) :
    ContDiffOn ℝ Work.Stability.smoothOrder (Function.uncurry (Work.Spaces.DthIter i G)) V := by
  induction i with
  | zero => simpa using h
  | succ i ih =>
      rw [Work.Spaces.DthIter_succ]
      exact contDiffOn_Dth hV ih

/-- `D_z^j D_θ^i` preserves `C^∞`-smoothness on an open set. -/
theorem contDiffOn_mixed {G : ℝ → ℝ → ℝ} {V : Set (ℝ × ℝ)} (hV : IsOpen V)
    (h : ContDiffOn ℝ Work.Stability.smoothOrder (Function.uncurry G) V) (j i : ℕ) :
    ContDiffOn ℝ Work.Stability.smoothOrder (Function.uncurry (Work.Spaces.mixed j i G)) V :=
  contDiffOn_DzIter hV (contDiffOn_DthIter hV h i) j

/-! ## The closure of `SmoothQuad` -/

theorem smoothQuad_of_contDiffOn_uncurry {f : ℝ → ℝ → ℝ}
    (h : ContDiffOn ℝ Work.Stability.smoothOrder (Function.uncurry f) Work.Spaces.quadU) :
    SmoothQuad f := h

theorem smoothQuad_add {a b : ℝ → ℝ → ℝ} (ha : SmoothQuad a) (hb : SmoothQuad b) :
    SmoothQuad (fun z θ => a z θ + b z θ) := by
  have hfun : Function.uncurry (fun z θ => a z θ + b z θ)
      = fun p : ℝ × ℝ => Function.uncurry a p + Function.uncurry b p := by
    funext p; rcases p with ⟨z, θ⟩; rfl
  rw [SmoothQuad, hfun]
  exact ContDiffOn.add ha hb

theorem smoothQuad_neg {a : ℝ → ℝ → ℝ} (ha : SmoothQuad a) :
    SmoothQuad (fun z θ => -a z θ) := by
  have hfun : Function.uncurry (fun z θ => -a z θ)
      = fun p : ℝ × ℝ => -Function.uncurry a p := by
    funext p; rcases p with ⟨z, θ⟩; rfl
  rw [SmoothQuad, hfun]
  exact ContDiffOn.neg ha

theorem smoothQuad_sub {a b : ℝ → ℝ → ℝ} (ha : SmoothQuad a) (hb : SmoothQuad b) :
    SmoothQuad (fun z θ => a z θ - b z θ) := by
  simpa only [sub_eq_add_neg] using smoothQuad_add ha (smoothQuad_neg hb)

theorem smoothQuad_const_mul (c : ℝ) {a : ℝ → ℝ → ℝ} (ha : SmoothQuad a) :
    SmoothQuad (fun z θ => c * a z θ) := by
  have hfun : Function.uncurry (fun z θ => c * a z θ)
      = fun p : ℝ × ℝ => c * Function.uncurry a p := by
    funext p; rcases p with ⟨z, θ⟩; rfl
  rw [SmoothQuad, hfun]
  exact ((contDiffOn_const : ContDiffOn ℝ Work.Stability.smoothOrder (fun _ : ℝ × ℝ => c)
    Work.Spaces.quadU)).mul ha

theorem smoothQuad_mul {a b : ℝ → ℝ → ℝ} (ha : SmoothQuad a) (hb : SmoothQuad b) :
    SmoothQuad (fun z θ => a z θ * b z θ) := by
  have hfun : Function.uncurry (fun z θ => a z θ * b z θ)
      = fun p : ℝ × ℝ => Function.uncurry a p * Function.uncurry b p := by
    funext p; rcases p with ⟨z, θ⟩; rfl
  rw [SmoothQuad, hfun]
  exact ContDiffOn.mul ha hb

theorem SmoothQuad.DzIter {G : ℝ → ℝ → ℝ} (hG : SmoothQuad G) (i : ℕ) :
    SmoothQuad (Work.Spaces.DzIter i G) :=
  contDiffOn_DzIter isOpen_quadU hG i

theorem SmoothQuad.DthIter {G : ℝ → ℝ → ℝ} (hG : SmoothQuad G) (i : ℕ) :
    SmoothQuad (Work.Spaces.DthIter i G) :=
  contDiffOn_DthIter isOpen_quadU hG i

theorem SmoothQuad.mixed {G : ℝ → ℝ → ℝ} (hG : SmoothQuad G) (j i : ℕ) :
    SmoothQuad (Work.Spaces.mixed j i G) :=
  contDiffOn_mixed isOpen_quadU hG j i

/-! ## Slices and differentiability on the open quadrant -/

/-- The `z`-slice of a `C^∞` function on a product of sets is `C^∞`. -/
theorem contDiffOn_slice_z {G : ℝ → ℝ → ℝ} {s t : Set ℝ}
    (hG : ContDiffOn ℝ Work.Stability.smoothOrder (Function.uncurry G) (s ×ˢ t))
    {θ : ℝ} (hθ : θ ∈ t) :
    ContDiffOn ℝ Work.Stability.smoothOrder (fun z => G z θ) s :=
  (hG.comp (((contDiffOn_id : ContDiffOn ℝ Work.Stability.smoothOrder (fun z : ℝ => z) s)).prodMk
    (contDiffOn_const (c := θ))) (fun z hz => ⟨hz, hθ⟩)).congr (fun z _ => rfl)

/-- The `θ`-slice of a `C^∞` function on a product of sets is `C^∞`. -/
theorem contDiffOn_slice_θ {G : ℝ → ℝ → ℝ} {s t : Set ℝ}
    (hG : ContDiffOn ℝ Work.Stability.smoothOrder (Function.uncurry G) (s ×ˢ t))
    {z : ℝ} (hz : z ∈ s) :
    ContDiffOn ℝ Work.Stability.smoothOrder (fun θ => G z θ) t :=
  (hG.comp ((contDiffOn_const (c := z)).prodMk
    ((contDiffOn_id : ContDiffOn ℝ Work.Stability.smoothOrder (fun θ : ℝ => θ) t)))
    (fun θ hθ => ⟨hz, hθ⟩)).congr (fun θ _ => rfl)

/-- The `z`-slice of a `SmoothQuad` function at `θ ∈ (0,π/2)` is `C^∞` on `Ioi (-1)`. -/
theorem SmoothQuad.curry_z {G : ℝ → ℝ → ℝ} (hG : SmoothQuad G) {θ : ℝ}
    (hθ : θ ∈ Set.Ioo 0 (π / 2)) :
    ContDiffOn ℝ Work.Stability.smoothOrder (fun z => G z θ) (Set.Ioi (-1)) :=
  contDiffOn_slice_z hG hθ

/-- The `θ`-slice of a `SmoothQuad` function at `z > -1` is `C^∞` on `(0,π/2)`. -/
theorem SmoothQuad.curry_θ {G : ℝ → ℝ → ℝ} (hG : SmoothQuad G) {z : ℝ}
    (hz : z ∈ Set.Ioi (-1)) :
    ContDiffOn ℝ Work.Stability.smoothOrder (fun θ => G z θ) (Set.Ioo 0 (π / 2)) :=
  contDiffOn_slice_θ hG hz

theorem smoothOrder_ne_zero : Work.Stability.smoothOrder ≠ 0 := by simp

/-- The `z`-slice of any mixed derivative of a `SmoothQuad` function is differentiable at
every `z > -1`, for every `θ ∈ (0,π/2)`. -/
theorem SmoothQuad.differentiableAt_slice_mixed {G : ℝ → ℝ → ℝ} (hG : SmoothQuad G) (b i : ℕ)
    {z : ℝ} (hz : z ∈ Set.Ioi (-1)) {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (π / 2)) :
    DifferentiableAt ℝ (fun z' => Work.Spaces.mixed b i G z' θ) z :=
  (((hG.mixed b i).curry_z hθ).differentiableOn smoothOrder_ne_zero).differentiableAt
    (isOpen_Ioi.mem_nhds hz)

/-- The `z`-slice of any `D_z`-iterate of a `SmoothQuad` function is differentiable at every
`z > -1`, for every `θ ∈ (0,π/2)`. -/
theorem SmoothQuad.differentiableAt_slice_DzIter {G : ℝ → ℝ → ℝ} (hG : SmoothQuad G) (b : ℕ)
    {z : ℝ} (hz : z ∈ Set.Ioi (-1)) {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (π / 2)) :
    DifferentiableAt ℝ (fun z' => Work.Spaces.DzIter b G z' θ) z :=
  (((hG.DzIter b).curry_z hθ).differentiableOn smoothOrder_ne_zero).differentiableAt
    (isOpen_Ioi.mem_nhds hz)

/-- The `θ`-slice of any `D_θ`-iterate of a `SmoothQuad` function is differentiable at every
`θ ∈ (0,π/2)`, for every `z > -1`. -/
theorem SmoothQuad.differentiableAt_slice_DthIter {G : ℝ → ℝ → ℝ} (hG : SmoothQuad G) (b : ℕ)
    {z : ℝ} (hz : z ∈ Set.Ioi (-1)) {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (π / 2)) :
    DifferentiableAt ℝ (fun θ' => Work.Spaces.DthIter b G z θ') θ :=
  (((hG.DthIter b).curry_θ hz).differentiableOn smoothOrder_ne_zero).differentiableAt
    (isOpen_Ioo.mem_nhds hθ)

/-! ## Continuity of the `ℋ^k`-integrand -/

/-- The uncurried `ℋ^k`-integrand of a `SmoothQuad` function is continuous on the open
quadrant `(0,∞) × (0,π/2)`.  (The `⊤`-version is `Work.Spaces.continuousOn_HkIntegrand_Qd`.) -/
theorem continuousOn_HkIntegrand_smoothQuad (α : ℝ) (k : ℕ) (F : ℝ → ℝ → ℝ)
    (hF : SmoothQuad F) :
    ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.HkIntegrand α k F p.1 p.2) Qd := by
  have hq : ∀ p ∈ Qd, p ∈ Work.Spaces.quadU := by
    intro p hp
    simp only [Qd, Work.Spaces.quadU, Set.mem_prod, Set.mem_Ioi, Set.mem_Ioo] at hp ⊢
    exact ⟨by linarith [hp.1], hp.2.1, hp.2.2⟩
  have hsinpos : ∀ p ∈ Qd, 0 < Real.sin (2 * p.2) :=
    fun p hp =>
      Real.sin_pos_of_pos_of_lt_pi (by linarith [hp.2.1]) (by linarith [hp.2.2, Real.pi_pos])
  have hw : ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.w p.1) Qd := by
    have hfun : (fun p : ℝ × ℝ => Work.Spaces.w p.1)
        = fun p : ℝ × ℝ => (1 + p.1) ^ 2 / p.1 ^ 2 := by
      funext p; rfl
    rw [hfun]
    refine ContinuousOn.div ((continuousOn_const.add continuousOn_fst).pow 2)
      (continuousOn_fst.pow 2) (fun p hp => pow_ne_zero 2 (ne_of_gt hp.1))
  have hsinpow : ∀ c : ℝ, ContinuousOn (fun p : ℝ × ℝ => (Real.sin (2 * p.2)) ^ c) Qd :=
    fun c => ((Real.continuous_sin.comp (continuous_const.mul continuous_snd)).continuousOn)
      |>.rpow_const (fun p hp => Or.inl (ne_of_gt (hsinpos p hp)))
  have hWt : ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.Wt α p.1 p.2) Qd := by
    have hfun : (fun p : ℝ × ℝ => Work.Spaces.Wt α p.1 p.2)
        = fun p : ℝ × ℝ => Work.Spaces.w p.1
            * (Real.sin (2 * p.2)) ^ (-(Work.Spaces.gam α / 2)) := by
      funext p; rfl
    rw [hfun]
    exact hw.mul (hsinpow _)
  have hwdiv : ContinuousOn (fun p : ℝ × ℝ =>
      Work.Spaces.w p.1 / (Real.sin (2 * p.2)) ^ (Work.Spaces.eta / 2)) Qd :=
    hw.div (hsinpow _) (fun p hp => ne_of_gt (Real.rpow_pos_of_pos (hsinpos p hp) _))
  have hDzC : ∀ i : ℕ, ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.DzIter i F p.1 p.2) Qd :=
    fun i => ((contDiffOn_DzIter isOpen_quadU hF i).continuousOn).mono hq
  have hmC : ∀ j i : ℕ, ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.mixed j i F p.1 p.2) Qd :=
    fun j i => ((contDiffOn_mixed isOpen_quadU hF j i).continuousOn).mono hq
  have hHk : (fun p : ℝ × ℝ => Work.Spaces.HkIntegrand α k F p.1 p.2)
      = fun p : ℝ × ℝ =>
          (∑ i ∈ Finset.range (k + 1),
              (Work.Spaces.DzIter i F p.1 p.2
                * (Work.Spaces.w p.1 / (Real.sin (2 * p.2)) ^ (Work.Spaces.eta / 2))) ^ 2)
            + ∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1),
                if 1 ≤ i ∧ i + j ≤ k
                then (Work.Spaces.mixed j i F p.1 p.2 * Work.Spaces.Wt α p.1 p.2) ^ 2
                else 0 := by
    funext p; rfl
  rw [hHk]
  refine ContinuousOn.add ?_ ?_
  · refine continuousOn_finsetSum (Finset.range (k + 1)) (fun i _ => ?_)
    exact ((hDzC i).mul hwdiv).pow 2
  · refine continuousOn_finsetSum (Finset.range (k + 1)) (fun i _ =>
      continuousOn_finsetSum (Finset.range (k + 1)) (fun j _ => ?_))
    split_ifs with h
    · exact ((hmC j i).mul hWt).pow 2
    · exact continuousOn_const

end Work.FTS.LocData
end
end
-- ===== merged: Submission.Work.FTS.LocData.SmoothQuad_locG =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

set_option autoImplicit false

open Set
open scoped Real Topology

namespace Work.FTS.LocData

noncomputable section

/-! ## The class `SmoothQuad` is closed under the pointwise operations

Each of these is the corresponding `ContDiffOn` closure rule read through the definition of
`SmoothQuad` (`Function.uncurry` commutes with the pointwise operations up to definitional
equality). -/





theorem SmoothQuad_const_mul (c : ℝ) {f : ℝ → ℝ → ℝ} (hf : SmoothQuad f) :
    SmoothQuad (fun z θ => c * f z θ) := by
  unfold SmoothQuad at *
  have hc : ContDiffOn ℝ Work.Stability.smoothOrder (fun _ : ℝ × ℝ => c)
      (Set.Ioi (-1) ×ˢ Set.Ioo 0 (π / 2)) := contDiffOn_const
  exact hc.mul hf

/-! ## The two basic `C^∞` profiles of the chapter -/

/-- The cut-off factor `(z,θ) ↦ χ(z/L)` is `C^∞` on the quadrant, for every real `L` (for
`L = 0` the function is the constant `χ 0`, since Lean's division by zero is `0`). -/
theorem SmoothQuad_chi_div (L : ℝ) :
    SmoothQuad (fun z θ : ℝ => Work.Stability.chi (z / L)) := by
  unfold SmoothQuad
  have hchi : ContDiff ℝ Work.Stability.smoothOrder Work.Stability.chi :=
    Work.Stability.chi_contDiff
  have hdiv : ContDiffOn ℝ Work.Stability.smoothOrder (fun p : ℝ × ℝ => p.1 / L)
      (Set.Ioi (-1) ×ˢ Set.Ioo 0 (π / 2)) :=
    contDiffOn_fst.div_const L
  exact hchi.comp_contDiffOn hdiv

/-- **The model profile `F_*` is `C^∞` on the quadrant.**  It is the product of the angular
factor `Γ(θ)/c` — smooth because the base `sinθ·cos²θ` is strictly positive on `0 < θ < π/2` —
with the rational radial factor `2z/(1+z)²`, whose only pole `z = -1` lies outside `z > -1`.
No hypothesis on `α` is needed. -/
theorem Fstar_smoothQuad (α : ℝ) : SmoothQuad (Work.Construction.Fstar α) := by
  unfold SmoothQuad
  -- the angular factor `Γ(θ)`
  have hGam : ContDiffOn ℝ Work.Stability.smoothOrder
      (fun p : ℝ × ℝ => Work.Spaces.Gam α p.2) (Set.Ioi (-1) ×ˢ Set.Ioo 0 (π / 2)) := by
    have hbase : ContDiffOn ℝ Work.Stability.smoothOrder
        (fun p : ℝ × ℝ => Real.sin p.2 * Real.cos p.2 ^ 2)
        (Set.Ioi (-1) ×ˢ Set.Ioo 0 (π / 2)) := by
      have h : ContDiffOn ℝ Work.Stability.smoothOrder
          (fun p : ℝ × ℝ => Real.sin (Prod.snd p) * Real.cos (Prod.snd p) ^ 2)
          (Set.Ioi (-1) ×ˢ Set.Ioo 0 (π / 2)) :=
        (Real.contDiff_sin.mul (Real.contDiff_cos.pow 2)).comp_contDiffOn
          (contDiffOn_snd (E := ℝ) (F := ℝ))
      simpa using h
    have hne : ∀ p : ℝ × ℝ, p ∈ Set.Ioi (-1) ×ˢ Set.Ioo 0 (π / 2) →
        Real.sin p.2 * Real.cos p.2 ^ 2 ≠ 0 := by
      rintro ⟨z, θ⟩ hp
      have hθ := hp.2
      have h1 : 0 < Real.sin θ :=
        Real.sin_pos_of_pos_of_lt_pi hθ.1 (by linarith [hθ.2, Real.pi_pos])
      have h2 : 0 < Real.cos θ :=
        Real.cos_pos_of_mem_Ioo ⟨by linarith [hθ.1, Real.pi_pos], hθ.2⟩
      positivity
    have hexp : ContDiffOn ℝ Work.Stability.smoothOrder (fun _ : ℝ × ℝ => α / 3)
        (Set.Ioi (-1) ×ˢ Set.Ioo 0 (π / 2)) := contDiffOn_const
    have hrpow : ContDiffOn ℝ Work.Stability.smoothOrder
        (fun p : ℝ × ℝ => (Real.sin p.2 * Real.cos p.2 ^ 2) ^ (α / 3))
        (Set.Ioi (-1) ×ˢ Set.Ioo 0 (π / 2)) :=
      hbase.rpow hexp hne
    simpa only [Work.Spaces.Gam] using hrpow
  -- the radial factor `2z/(1+z)²`
  have hrad : ContDiffOn ℝ Work.Stability.smoothOrder
      (fun p : ℝ × ℝ => Work.FM.Fstar p.1) (Set.Ioi (-1) ×ˢ Set.Ioo 0 (π / 2)) := by
    have hz : ContDiffOn ℝ Work.Stability.smoothOrder
        (fun z : ℝ => 2 * z / (1 + z) ^ 2) (Set.Ioi (-1)) := by
      have hnum : ContDiffOn ℝ Work.Stability.smoothOrder (fun z : ℝ => 2 * z) (Set.Ioi (-1)) :=
        contDiffOn_const.mul contDiffOn_id
      have hden : ContDiffOn ℝ Work.Stability.smoothOrder
          (fun z : ℝ => (1 + z) ^ 2) (Set.Ioi (-1)) :=
        (contDiffOn_const.add contDiffOn_id).pow 2
      exact hnum.div hden (fun z hz =>
        pow_ne_zero 2 (by have hz' : (-1 : ℝ) < z := hz; linarith))
    exact hz.comp contDiffOn_fst (fun p hp => hp.1)
  -- the product `α·(Γ(θ)/c)·F_*(z)`
  have h1 : ContDiffOn ℝ Work.Stability.smoothOrder
      (fun p : ℝ × ℝ => α * (Work.Spaces.Gam α p.2 / Work.Spaces.c α))
      (Set.Ioi (-1) ×ˢ Set.Ioo 0 (π / 2)) := by
    have hc : ContDiffOn ℝ Work.Stability.smoothOrder (fun _ : ℝ × ℝ => α)
        (Set.Ioi (-1) ×ˢ Set.Ioo 0 (π / 2)) := contDiffOn_const
    exact hc.mul (hGam.div_const _)
  have h2 : ContDiffOn ℝ Work.Stability.smoothOrder
      (fun p : ℝ × ℝ =>
        α * (Work.Spaces.Gam α p.2 / Work.Spaces.c α) * Work.FM.Fstar p.1)
      (Set.Ioi (-1) ×ˢ Set.Ioo 0 (π / 2)) :=
    h1.mul hrad
  simpa only [Function.uncurry_def, Work.Construction.Fstar] using h2

/-! ## The target -/

/-- **The localised perturbation is `C^∞` on the quadrant whenever the bump is**, i.e.
`locG α L β h = -zfar L F_* + β h = F_*·χ(z/L) + β h - F_*` is a combination of the two
`C^∞` profiles of the chapter.  The hypotheses `0 < α`, `α ≤ 1` of the route are not used. -/
theorem SmoothQuad_locG (α L β : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) {h : ℝ → ℝ → ℝ}
    (hsh : SmoothQuad h) : SmoothQuad (locG α L β h) := by
  have hchi := SmoothQuad_chi_div L
  have hF := Fstar_smoothQuad α
  have hβ : SmoothQuad (fun z θ => β * h z θ) := SmoothQuad_const_mul β hsh
  have hmain : SmoothQuad (fun z θ => Work.Construction.Fstar α z θ * Work.Stability.chi (z / L)
      + β * h z θ - Work.Construction.Fstar α z θ) :=
    ((hF.mul hchi).add hβ).sub hF
  unfold SmoothQuad at hmain ⊢
  refine hmain.congr (fun p hp => ?_)
  simp only [Function.uncurry_def, locG_apply, locData_apply]

end

end Work.FTS.LocData
end
-- ===== merged: Submission.Work.FTS.LocData.angMaj_mem =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.LocData

set_option autoImplicit false

/-! ## Elementary `rpow` helper -/

/-- `(X/2)^a = 2^{-a} X^a` for `X ≥ 0`. -/
theorem angMaj_div_two_rpow (X : ℝ) (hX : 0 ≤ X) (a : ℝ) :
    (X / 2) ^ a = 2 ^ (-a) * X ^ a := by
  rw [Real.div_rpow hX (by norm_num : (0 : ℝ) ≤ 2),
    Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2)]
  ring

/-! ## The two pointwise bounds -/

/-- **The first angular term is dominated by `X^{17α/30-1}`**, `X = sin(2θ)`:

`Γ(θ)² · sin(2θ)^{-γ(α)} ≤ 2^{-2α/3} · sin(2θ)^{17α/30-1}`  on `Iθ`.

`17α/30 - 1 = 2α/3 - γ(α)` lies in `(-1, 0]` for `0 < α ≤ 1`, so the majorant
is integrable with integral at most `2^{-2α/3}·3000/(17α)`. -/
theorem GamSq_sin_neg_gam_le (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) {θ : ℝ}
    (hθ : θ ∈ Work.Spaces.Iθ) :
    Work.Spaces.Gam α θ ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
      ≤ 2 ^ (-(2 * α / 3)) * (Real.sin (2 * θ)) ^ (17 * α / 30 - 1) := by
  have hs0 : 0 ≤ Real.sin θ :=
    Real.sin_nonneg_of_mem_Icc ⟨hθ.1, by linarith [hθ.2, Real.pi_pos]⟩
  have hc0 : 0 ≤ Real.cos θ :=
    Real.cos_nonneg_of_mem_Icc
      ⟨by linarith [hθ.1, Real.pi_pos], by linarith [hθ.2, Real.pi_pos]⟩
  have hc1 : Real.cos θ ≤ 1 := Real.cos_le_one θ
  have hX0 : 0 ≤ Real.sin (2 * θ) := by
    rw [Real.sin_two_mul]; positivity
  have hexp : 2 * α / 3 + -(Work.Spaces.gam α) = 17 * α / 30 - 1 := by
    simp only [Work.Spaces.gam]; ring
  have hne : 2 * α / 3 + -(Work.Spaces.gam α) ≠ 0 := by
    rw [hexp]; intro h; linarith
  -- `Γ² = (sin θ cos²θ)^{2α/3}`
  have hΓ2 : Work.Spaces.Gam α θ ^ 2 = (Real.sin θ * Real.cos θ ^ 2) ^ (2 * α / 3) := by
    rw [Work.Spaces.Gam]
    rw [← Real.rpow_natCast,
      ← Real.rpow_mul (by positivity : (0 : ℝ) ≤ Real.sin θ * Real.cos θ ^ 2)]
    congr 1
    ring
  -- `Γ² ≤ (sin θ cos θ)^{2α/3}`, because `cos²θ ≤ cos θ`
  have hc2 : Real.cos θ ^ 2 ≤ Real.cos θ := by nlinarith [hc0, hc1]
  have hYle : Real.sin θ * Real.cos θ ^ 2 ≤ Real.sin θ * Real.cos θ :=
    mul_le_mul_of_nonneg_left hc2 hs0
  have hstat : Work.Spaces.Gam α θ ^ 2 ≤ (Real.sin θ * Real.cos θ) ^ (2 * α / 3) := by
    rw [hΓ2]
    exact Real.rpow_le_rpow (by positivity) hYle (by linarith : (0 : ℝ) ≤ 2 * α / 3)
  -- `(sin θ cos θ)^{2α/3} X^{-γ} = 2^{-2α/3} X^{2α/3-γ}`
  have hstep2 : (Real.sin θ * Real.cos θ) ^ (2 * α / 3)
        * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
      = 2 ^ (-(2 * α / 3)) * (Real.sin (2 * θ)) ^ (17 * α / 30 - 1) := by
    have hY : Real.sin θ * Real.cos θ = Real.sin (2 * θ) / 2 := by
      rw [Real.sin_two_mul]; ring
    rw [hY, angMaj_div_two_rpow _ hX0, mul_assoc, ← Real.rpow_add' hX0 hne, hexp]
  calc Work.Spaces.Gam α θ ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
      ≤ (Real.sin θ * Real.cos θ) ^ (2 * α / 3)
          * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) :=
        mul_le_mul_of_nonneg_right hstat (Real.rpow_nonneg hX0 _)
    _ = 2 ^ (-(2 * α / 3)) * (Real.sin (2 * θ)) ^ (17 * α / 30 - 1) := hstep2

/-- **The second angular term is dominated by `sin(2θ)^{-η}`**: `Γ ≤ 1` on `Iθ`. -/
theorem GamSq_sin_neg_eta_le (α : ℝ) (hα : 0 < α) {θ : ℝ}
    (hθ : θ ∈ Work.Spaces.Iθ) :
    Work.Spaces.Gam α θ ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))
      ≤ (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) := by
  have hX0 : 0 ≤ Real.sin (2 * θ) := by
    rw [Real.sin_two_mul]
    exact mul_nonneg (mul_nonneg (by norm_num)
      (Real.sin_nonneg_of_mem_Icc ⟨hθ.1, by linarith [hθ.2, Real.pi_pos]⟩))
      (Real.cos_nonneg_of_mem_Icc
        ⟨by linarith [hθ.1, Real.pi_pos], by linarith [hθ.2, Real.pi_pos]⟩)
  obtain ⟨hG0, hG1⟩ := Work.Spaces.Gam_bounds α θ hα hθ
  have hG2 : Work.Spaces.Gam α θ ^ 2 ≤ 1 := by nlinarith
  exact mul_le_of_le_one_left (Real.rpow_nonneg hX0 _) hG2

/-! ## The closing arithmetic -/

/-- The numerical inequality that closes the estimate.  It follows from
`2^{-2α/3} ≤ 1`, `π ≤ 4` and `α ≤ 1`. -/
theorem angMaj_arith (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) :
    2 ^ (-(2 * α / 3)) * (3000 / (17 * α)) + 10000 + Real.pi / 2
      ≤ 1000 / (3 * α) + 10001 := by
  have hpow1 : (2 : ℝ) ^ (-(2 * α / 3)) ≤ 1 := by
    have h := Real.rpow_le_rpow_of_exponent_le (x := (2 : ℝ))
      (by norm_num : (1 : ℝ) ≤ 2) (by linarith : -(2 * α / 3) ≤ 0)
    simpa using h
  have hd : (0 : ℝ) ≤ 3000 / (17 * α) := by positivity
  have h1 : 2 ^ (-(2 * α / 3)) * (3000 / (17 * α)) ≤ 3000 / (17 * α) := by
    have hm := mul_le_mul_of_nonneg_right hpow1 hd
    simpa using hm
  -- `π/2 - 1 ≤ 8000/(51α)`, which is the exact slack in the claim
  have h817 : (1 : ℝ) ≤ 8000 / (51 * α) := by
    rw [le_div_iff₀ (by linarith : (0 : ℝ) < 51 * α)]
    nlinarith [hα, hα1]
  have hkey : Real.pi / 2 - 1 ≤ 8000 / (51 * α) :=
    le_trans (by linarith [Real.pi_le_four]) h817
  have hsub : 1000 / (3 * α) - 3000 / (17 * α) = 8000 / (51 * α) := by
    field_simp
    ring
  linarith [h1, hkey, hsub]

/-! ## The main lemma -/

theorem angMaj_mem (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) :
    MeasureTheory.IntegrableOn (fun θ => angMaj α θ) Work.Spaces.Iθ ∧
      ∫ θ in Work.Spaces.Iθ, angMaj α θ ≤ 1000 / (3 * α) + 10001 := by
  have hmeasIθ : MeasurableSet Work.Spaces.Iθ := measurableSet_Icc
  -- nonnegativity of `sin(2θ)` on `Iθ`
  have hsin2 : ∀ θ ∈ Work.Spaces.Iθ, 0 ≤ Real.sin (2 * θ) := by
    intro θ hθ
    rw [Real.sin_two_mul]
    exact mul_nonneg (mul_nonneg (by norm_num)
      (Real.sin_nonneg_of_mem_Icc ⟨hθ.1, by linarith [hθ.2, Real.pi_pos]⟩))
      (Real.cos_nonneg_of_mem_Icc
        ⟨by linarith [hθ.1, Real.pi_pos], by linarith [hθ.2, Real.pi_pos]⟩)
  -- exponents
  have hp1 : -1 < 17 * α / 30 - 1 := by linarith
  have hp2 : 17 * α / 30 - 1 ≤ 0 := by linarith
  have he1 : -1 < -(Work.Spaces.eta) := by simp only [Work.Spaces.eta]; norm_num
  have he2 : -(Work.Spaces.eta) ≤ 0 := by simp only [Work.Spaces.eta]; norm_num
  obtain ⟨hIntS1, hBdS1⟩ := Work.Spaces.sin_two_rpow (17 * α / 30 - 1) hp1 hp2
  obtain ⟨hIntS2, hBdS2⟩ := Work.Spaces.sin_two_rpow (-(Work.Spaces.eta)) he1 he2
  -- the integrals of the two trigonometric majorants
  have hBdS1' : ∫ θ in Work.Spaces.Iθ, (Real.sin (2 * θ)) ^ (17 * α / 30 - 1)
      ≤ 3000 / (17 * α) := by
    have heq : 100 / ((17 * α / 30 - 1) + 1) = 3000 / (17 * α) := by
      field_simp
      ring
    rwa [heq] at hBdS1
  have hBdS2' : ∫ θ in Work.Spaces.Iθ, (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))
      ≤ 10000 := by
    have heq : 100 / (-(Work.Spaces.eta) + 1) = 10000 := by
      simp only [Work.Spaces.eta]; norm_num
    rwa [heq] at hBdS2
  -- the first majorant is integrable
  have hM1 : MeasureTheory.IntegrableOn
      (fun θ : ℝ => 2 ^ (-(2 * α / 3)) * (Real.sin (2 * θ)) ^ (17 * α / 30 - 1))
      Work.Spaces.Iθ := hIntS1.const_mul _
  -- the a.e. pointwise bounds
  have hpt1 : ∀ᵐ θ ∂(volume.restrict Work.Spaces.Iθ),
      Work.Spaces.Gam α θ ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
        ≤ 2 ^ (-(2 * α / 3)) * (Real.sin (2 * θ)) ^ (17 * α / 30 - 1) := by
    filter_upwards [MeasureTheory.ae_restrict_mem hmeasIθ] with θ hθ
    exact GamSq_sin_neg_gam_le α hα hα1 hθ
  have hpt2 : ∀ᵐ θ ∂(volume.restrict Work.Spaces.Iθ),
      Work.Spaces.Gam α θ ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))
        ≤ (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) := by
    filter_upwards [MeasureTheory.ae_restrict_mem hmeasIθ] with θ hθ
    exact GamSq_sin_neg_eta_le α hα hθ
  -- measurability
  have hmeas1 : AEStronglyMeasurable
      (fun θ : ℝ => Work.Spaces.Gam α θ ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)))
      (volume.restrict Work.Spaces.Iθ) := by
    apply Measurable.aestronglyMeasurable
    simp only [Work.Spaces.Gam]
    fun_prop
  have hmeas2 : AEStronglyMeasurable
      (fun θ : ℝ => Work.Spaces.Gam α θ ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))
      (volume.restrict Work.Spaces.Iθ) := by
    apply Measurable.aestronglyMeasurable
    simp only [Work.Spaces.Gam]
    fun_prop
  -- integrability of the two terms
  have hf1 : MeasureTheory.IntegrableOn
      (fun θ : ℝ => Work.Spaces.Gam α θ ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)))
      Work.Spaces.Iθ :=
    hM1.mono' hmeas1 (by
      filter_upwards [hpt1, MeasureTheory.ae_restrict_mem hmeasIθ] with θ h1 h2
      rw [Real.norm_of_nonneg
        (mul_nonneg (sq_nonneg _) (Real.rpow_nonneg (hsin2 θ h2) _))]
      exact h1)
  have hf2 : MeasureTheory.IntegrableOn
      (fun θ : ℝ => Work.Spaces.Gam α θ ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))
      Work.Spaces.Iθ :=
    hIntS2.mono' hmeas2 (by
      filter_upwards [hpt2, MeasureTheory.ae_restrict_mem hmeasIθ] with θ h1 h2
      rw [Real.norm_of_nonneg
        (mul_nonneg (sq_nonneg _) (Real.rpow_nonneg (hsin2 θ h2) _))]
      exact h1)
  -- integral bounds for the two terms
  have hint1 : ∫ θ in Work.Spaces.Iθ,
        Work.Spaces.Gam α θ ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
      ≤ 2 ^ (-(2 * α / 3)) * (3000 / (17 * α)) := by
    have hmono := MeasureTheory.integral_mono_ae hf1 hM1 hpt1
    refine le_trans hmono ?_
    rw [MeasureTheory.integral_const_mul]
    exact mul_le_mul_of_nonneg_left hBdS1' (Real.rpow_nonneg (by norm_num) _)
  have hint2 : ∫ θ in Work.Spaces.Iθ,
        Work.Spaces.Gam α θ ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))
      ≤ 10000 := by
    have hmono := MeasureTheory.integral_mono_ae hf2 hIntS2 hpt2
    exact le_trans hmono hBdS2'
  -- the constant function
  have hInt0 : MeasureTheory.IntegrableOn (fun _ : ℝ => (1 : ℝ)) Work.Spaces.Iθ :=
    MeasureTheory.integrableOn_const (μ := volume) (s := Work.Spaces.Iθ) (C := (1 : ℝ))
      (by rw [Work.Spaces.Iθ, Real.volume_Icc]; exact ENNReal.ofReal_ne_top)
  have hvol : ∫ θ in Work.Spaces.Iθ, (1 : ℝ) = Real.pi / 2 := by
    rw [MeasureTheory.setIntegral_const, smul_eq_mul, mul_one, MeasureTheory.measureReal_def,
      Work.Spaces.Iθ, Real.volume_Icc]
    rw [ENNReal.toReal_ofReal (by linarith [Real.pi_pos] : (0 : ℝ) ≤ Real.pi / 2 - 0)]
    ring
  -- the sum
  have hSum : MeasureTheory.IntegrableOn
      (fun θ : ℝ => Work.Spaces.Gam α θ ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
        + Work.Spaces.Gam α θ ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))
      Work.Spaces.Iθ := hf1.add hf2
  have hangMaj : (fun θ : ℝ => angMaj α θ)
      = fun θ : ℝ => (Work.Spaces.Gam α θ ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
          + Work.Spaces.Gam α θ ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))) + 1 := by
    funext θ
    rw [angMaj_apply]
  have hintSum : ∫ θ in Work.Spaces.Iθ, angMaj α θ
      = (∫ θ in Work.Spaces.Iθ,
            Work.Spaces.Gam α θ ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)))
        + (∫ θ in Work.Spaces.Iθ,
            Work.Spaces.Gam α θ ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))
        + (∫ θ in Work.Spaces.Iθ, (1 : ℝ)) := by
    rw [hangMaj, MeasureTheory.integral_add hSum hInt0, MeasureTheory.integral_add hf1 hf2]
  constructor
  · rw [hangMaj]; exact hSum.add hInt0
  · rw [hintSum]
    have h12 : (∫ θ in Work.Spaces.Iθ,
            Work.Spaces.Gam α θ ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)))
        + (∫ θ in Work.Spaces.Iθ,
            Work.Spaces.Gam α θ ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))
        ≤ 2 ^ (-(2 * α / 3)) * (3000 / (17 * α)) + 10000 :=
      add_le_add hint1 hint2
    rw [hvol]
    linarith [h12, angMaj_arith α hα hα1]

end Work.FTS.LocData
end
end
-- ===== merged: Submission.Work.FTS.LocData.bumpZ_eq_zero_of_notMem_Icc =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.LocData

/-- **The radial bump vanishes off `[3/4, 7/4]`.**  If `z ∉ [3/4, 7/4]` then `z < 3/4` or
`z > 7/4`; in the first case `4z - 5 < -2` and in the second `4z - 5 > 2`, so in either case
`|4z - 5| ≥ 2` and `χ(4z - 5) = 0` (`Work.Stability.chi_eq_zero`). -/
theorem bumpZ_eq_zero_of_notMem_Icc (z : ℝ) (hz : z ∉ Set.Icc (3 / 4 : ℝ) (7 / 4)) :
    Work.FTS.LocData.bumpZ z = 0 := by
  rw [bumpZ_apply, Work.Stability.chi_eq_zero]
  have h : z < 3 / 4 ∨ 7 / 4 < z := by
    by_contra hc
    exact hz ⟨not_lt.mp (fun h => hc (Or.inl h)),
      not_lt.mp (fun h => hc (Or.inr h))⟩
  rcases h with h | h
  · have hneg : 4 * z - 5 < 0 := by linarith
    rw [abs_of_neg hneg]
    linarith
  · have hpos : 0 < 4 * z - 5 := by linarith
    rw [abs_of_pos hpos]
    linarith

end Work.FTS.LocData
end
