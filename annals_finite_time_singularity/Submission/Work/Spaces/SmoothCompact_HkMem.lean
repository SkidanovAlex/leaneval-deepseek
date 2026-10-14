import Mathlib.Algebra.EuclideanDomain.Basic
import Mathlib.Algebra.EuclideanDomain.Field
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Polynomial.Degree.Defs
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.ContDiff.WithLp
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.FDeriv.Measurable
import Mathlib.Analysis.Calculus.FDeriv.Pow
import Mathlib.Analysis.Calculus.FDeriv.Prod
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Analysis.Calculus.LocalExtr.Rolle
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.Normed.Group.AddTorsor
import Mathlib.Analysis.Normed.Operator.NormedSpace
import Mathlib.Analysis.Normed.Order.Lattice
import Mathlib.Analysis.RCLike.Basic
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Integrability.Basic
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Basic.Real.Basic
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Order.CompletePartialOrder
import Mathlib.Order.Interval.Basic
import Mathlib.Tactic.Have
import Mathlib.Tactic.MinImports
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Mathlib.Topology.GDelta.MetrizableSpace
import Mathlib.Topology.Separation.CompletelyRegular
import Submission.Work.Elliptic.WtoHAux
import Submission.Work.FTS.EllipticEst.OpenFTC.absFtcLeIntegralAbsDeriv
import Submission.Work.FTS.EllipticEst.integrableOn_HkIntegrand_terms
import Submission.Work.FTS.EllipticEst.remov.slice_gprime_ident
import Submission.Work.FTS.PhiStar.Series.Weil.integrableOn_prod_mul
import Submission.Work.Spaces.DerivLikeBasic
import Submission.Work.Spaces.HkSq_terms
import Submission.Work.Spaces.bt_integral_weight_id
import Submission.Work.Spaces.dthU_Gam
import Submission.Work.Spaces.factor_bound
import Submission.Work.Spaces.mixed_mul_le
import Submission.Work.Spaces.pz_DthIter_mul_eq
import Submission.Work.Spaces.scoef_sum_shift
import Submission.Work.Spaces.sin_two_rpow
import Submission.Work.Spaces.sq_mul_div_rpow
import Submission.Work.Spaces.uncurry_partial_c1
-- ===== merged: Submission.Work.Coercivity.C0Defs =====
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

/-- `h(θ) = 3 K(θ) sin(2θ)`: the angular factor of the density of `L₁₂(Transport f)`.
It vanishes at `θ = 0` and `θ = π/2`. -/
def C0h (θ : ℝ) : ℝ := 3 * Spaces.K θ * Real.sin (2 * θ)

/-- `h'(θ) = 18 sin θ cos²θ (2 cos²θ - 3 sin²θ)`, the derivative of `C0h`. -/
def C0g (θ : ℝ) : ℝ :=
  18 * Real.sin θ * Real.cos θ ^ 2 * (2 * Real.cos θ ^ 2 - 3 * Real.sin θ ^ 2)

/-- `Ih = ∫_{Iθ} h'(θ)² dθ`. -/
def C0Ih : ℝ := ∫ θ in Spaces.Iθ, (C0g θ) ^ 2

/-- `D = ∫_0^∞ (z(1+z)w(z))^{-2} dz`; it equals `1/30`. -/
def C0D : ℝ := ∫ s in Set.Ioi (0 : ℝ), (1 / (s * (1 + s) * Spaces.w s)) ^ 2


end Work.Coercivity
end
end
-- ===== merged: Submission.Work.Coercivity.CommutZQuadQDerivLike =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open Set Filter

namespace Work.Coercivity



end Work.Coercivity
end
end
-- ===== merged: Submission.Work.Coercivity.CommutZ_HkIntegrand_congr_pt =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.Coercivity

open scoped Real Topology
open MeasureTheory Set Filter

open Work.Spaces

/-- If `a` and `b` agree on `(0,∞) × [0,π/2]`, then `D_z a` and `D_z b` agree there. -/
private lemma Dz_congr_Iθ {a b : ℝ → ℝ → ℝ}
    (h : ∀ z ∈ Set.Ioi 0, ∀ θ ∈ Iθ, a z θ = b z θ) :
    ∀ z ∈ Set.Ioi 0, ∀ θ ∈ Iθ, Dz a z θ = Dz b z θ := by
  intro z hz θ hθ
  have hev : (fun z' => a z' θ) =ᶠ[𝓝 z] (fun z' => b z' θ) := by
    filter_upwards [isOpen_Ioi.mem_nhds hz] with z' hz'
    exact h z' hz' θ hθ
  simp only [Dz, pz]
  rw [hev.deriv_eq]

/-- If `a` and `b` agree on `(0,∞) × (0,π/2)`, then `D_z a` and `D_z b` agree there. -/
private lemma Dz_congr_Ioo {a b : ℝ → ℝ → ℝ}
    (h : ∀ z ∈ Set.Ioi 0, ∀ θ ∈ Set.Ioo 0 (π / 2), a z θ = b z θ) :
    ∀ z ∈ Set.Ioi 0, ∀ θ ∈ Set.Ioo 0 (π / 2), Dz a z θ = Dz b z θ := by
  intro z hz θ hθ
  have hev : (fun z' => a z' θ) =ᶠ[𝓝 z] (fun z' => b z' θ) := by
    filter_upwards [isOpen_Ioi.mem_nhds hz] with z' hz'
    exact h z' hz' θ hθ
  simp only [Dz, pz]
  rw [hev.deriv_eq]

/-- If `a` and `b` agree on `(0,∞) × (0,π/2)`, then `D_θ a` and `D_θ b` agree there. -/
private lemma Dth_congr_Ioo {a b : ℝ → ℝ → ℝ}
    (h : ∀ z ∈ Set.Ioi 0, ∀ θ ∈ Set.Ioo 0 (π / 2), a z θ = b z θ) :
    ∀ z ∈ Set.Ioi 0, ∀ θ ∈ Set.Ioo 0 (π / 2), Dth a z θ = Dth b z θ := by
  intro z hz θ hθ
  have hev : (fun θ' => a z θ') =ᶠ[𝓝 θ] (fun θ' => b z θ') := by
    filter_upwards [isOpen_Ioo.mem_nhds hθ] with θ' hθ'
    exact h z hz θ' hθ'
  simp only [Dth, pth]
  rw [hev.deriv_eq]

/-- Iterated `D_z` congruence on `(0,∞) × [0,π/2]`. -/
private lemma DzIter_congr_Iθ {u v : ℝ → ℝ → ℝ}
    (h : ∀ z ∈ Set.Ioi 0, ∀ θ ∈ Iθ, u z θ = v z θ) :
    ∀ i, ∀ z ∈ Set.Ioi 0, ∀ θ ∈ Iθ, DzIter i u z θ = DzIter i v z θ := by
  intro i
  induction i with
  | zero => intro z hz θ hθ; simpa using h z hz θ hθ
  | succ i ih =>
      intro z hz θ hθ
      simp only [DzIter_succ]
      exact Dz_congr_Iθ ih z hz θ hθ

/-- Iterated `D_θ` congruence on `(0,∞) × (0,π/2)`. -/
private lemma DthIter_congr_Ioo {u v : ℝ → ℝ → ℝ}
    (h : ∀ z ∈ Set.Ioi 0, ∀ θ ∈ Set.Ioo 0 (π / 2), u z θ = v z θ) :
    ∀ i, ∀ z ∈ Set.Ioi 0, ∀ θ ∈ Set.Ioo 0 (π / 2), DthIter i u z θ = DthIter i v z θ := by
  intro i
  induction i with
  | zero => intro z hz θ hθ; simpa using h z hz θ hθ
  | succ i ih =>
      intro z hz θ hθ
      simp only [DthIter_succ]
      exact Dth_congr_Ioo ih z hz θ hθ

/-- Mixed iterated derivatives agree on `(0,∞) × (0,π/2)`. -/
private lemma mixed_congr_Ioo {u v : ℝ → ℝ → ℝ}
    (h : ∀ z ∈ Set.Ioi 0, ∀ θ ∈ Set.Ioo 0 (π / 2), u z θ = v z θ) :
    ∀ j i, ∀ z ∈ Set.Ioi 0, ∀ θ ∈ Set.Ioo 0 (π / 2),
      mixed j i u z θ = mixed j i v z θ := by
  intro j
  induction j with
  | zero =>
      intro i z hz θ hθ
      simpa only [mixed_zero_left] using DthIter_congr_Ioo h i z hz θ hθ
  | succ j ih =>
      intro i z hz θ hθ
      have hD := Dz_congr_Ioo (ih i) z hz θ hθ
      simpa only [mixed, DzIter_succ] using hD

theorem CommutZ_HkIntegrand_congr_pt (α : ℝ) (n : ℕ) (u v : ℝ → ℝ → ℝ)
    (h : ∀ z ∈ Set.Ioi 0, ∀ θ ∈ Work.Spaces.Iθ, u z θ = v z θ) :
    ∀ z ∈ Set.Ioi 0, ∀ θ ∈ Set.Ioo 0 (π / 2),
      Work.Spaces.HkIntegrand α n u z θ = Work.Spaces.HkIntegrand α n v z θ := by
  intro z hz θ hθ
  have hθIθ : θ ∈ Iθ := ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩
  have hIoo : ∀ z' ∈ Set.Ioi 0, ∀ θ' ∈ Set.Ioo 0 (π / 2), u z' θ' = v z' θ' :=
    fun z' hz' θ' hθ' => h z' hz' θ' ⟨le_of_lt hθ'.1, le_of_lt hθ'.2⟩
  have hDz : ∀ i, DzIter i u z θ = DzIter i v z θ :=
    fun i => DzIter_congr_Iθ h i z hz θ hθIθ
  have hmx : ∀ j i, mixed j i u z θ = mixed j i v z θ :=
    fun j i => mixed_congr_Ioo hIoo j i z hz θ hθ
  simp only [HkIntegrand]
  congr 1
  · exact Finset.sum_congr rfl (fun i _ => by rw [hDz i])
  · exact Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => by
      split_ifs with hc
      · rw [hmx j i]
      · rfl))

end Work.Coercivity
end
-- ===== merged: Submission.Work.Coercivity.CommutZ_mult_Msum_le =====
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
set_option maxHeartbeats 2000000

/-- At an angle with `sin (2θ) = 0`, all mixed derivatives of `θ`-order `≥ 1` vanish. -/
private theorem mixed_eq_zero_of_sin_eq_zero_prv {H : ℝ → ℝ → ℝ} {z θ : ℝ}
    (hθ : Real.sin (2 * θ) = 0) {j i : ℕ} (hi : 1 ≤ i) : Spaces.mixed j i H z θ = 0 := by
  have h1 : ∀ z' : ℝ, Spaces.DthIter i H z' θ = 0 :=
    fun z' => Spaces.DthIter_eq_zero_of_sin hθ i hi z'
  rw [Spaces.mixed]
  exact Spaces.DzIter_eq_zero_of_slice_zero (u := Spaces.DthIter i H) (θ := θ) h1 j z


end Work.Coercivity
end
end
-- ===== merged: Submission.Work.Coercivity.CommutZ_mult_Zsum_le =====
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
set_option maxHeartbeats 2000000


end Work.Coercivity
end
end
-- ===== merged: Submission.Work.Coercivity.Dth_gam_prod_facts =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.Coercivity

open MeasureTheory Set Filter
open scoped Real Topology


end Work.Coercivity
end
-- ===== merged: Submission.Work.Coercivity.DzRIter_mul =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open Set Filter

namespace Work.Coercivity

set_option maxHeartbeats 1000000

/-! ## `D_z = z ∂_z` as a derivation on the `C^∞` functions of `(0,∞)`

The operator `DzR R = fun z => z * deriv R z` is a derivation for the pointwise
product, so its iterates obey the binomial (Leibniz) rule.  The combinatorial
part of that induction (the Pascal reindexing and the induction itself) is the
general `Work.Spaces.DerivLike.iterate_mul`; here we only have to observe that
`DzR` is `DerivLike` for the class of functions `C^∞` on `(0,∞)`, and that
`DzRIter` is the corresponding iterate. -/






end Work.Coercivity
end
end
-- ===== merged: Submission.Work.Coercivity.Dz_LGammaT_decomp =====
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
set_option maxHeartbeats 4000000

/-- `∂_z (L₁₂ f)(z) = - Kavg f z / z` for `z > 0` (from `HardyHyp`). -/
theorem L12f_zDeriv (f : ℝ → ℝ → ℝ) (hf : HardyHyp f) {z : ℝ} (hz : 0 < z) :
    HasDerivAt (fun z' => L12f f z') (-(Kavg f z / z)) z := by
  have hcont : ContinuousAt (FM.L12dens Spaces.K f) z := hf.hcont z (by simpa using hz)
  have h := FM.hasDerivAt_L12 (K := Spaces.K) (f := f) hf.hint hcont hz
  have hden : FM.L12dens Spaces.K f z = Kavg f z / z := by
    rw [FM.L12dens_eq (K := Spaces.K) (f := f) (s := z) (ne_of_gt hz), Kavg, Spaces.Iθ]
  rw [hden] at h
  simpa only [L12f] using h



end Work.Coercivity
end
end
-- ===== merged: Submission.Work.Coercivity.Dz_bound_near_zero =====
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

theorem Dz_bound_near_zero (f : ℝ → ℝ → ℝ) (hsm : Spaces.SmoothNbhd f)
    (h0 : ∀ θ ∈ Spaces.Iθ, Spaces.pz f 0 θ = 0) :
    ∃ M δ : ℝ, 0 < δ ∧ δ ≤ 1 ∧ 0 ≤ M ∧
      ∀ z ∈ Set.Ioo 0 δ, ∀ θ ∈ Spaces.Iθ,
        |Spaces.pz f z θ| ≤ M * z ∧ |Spaces.pz (Spaces.pz f) z θ| ≤ M := by
  -- `∂_z² f` is smooth on a neighbourhood of the closed quadrant.
  have hsm2 : Spaces.SmoothNbhd (Spaces.pz (Spaces.pz f)) :=
    (Spaces.SmoothNbhd.pz hsm).pz
  -- hence it is bounded on the box `[0,1] × [0,π/2]`.
  have hbdd : BddAbove (Spaces.boxSet 1 (Spaces.pz (Spaces.pz f))) :=
    Spaces.bddAbove_boxSup_of_continuousOn (Spaces.continuousOn_box_of_contDiffOn hsm2)
  refine ⟨Spaces.boxSup 1 (Spaces.pz (Spaces.pz f)), 1, one_pos, le_refl 1,
    Spaces.boxSup_nonneg zero_le_one hbdd, ?_⟩
  intro z hz θ hθ
  have hz01 : z ∈ Set.Icc (0:ℝ) 1 := ⟨le_of_lt hz.1, le_of_lt hz.2⟩
  refine ⟨?_, Spaces.le_boxSup hbdd hz01 hθ⟩
  -- Fundamental theorem of calculus for the `θ`-slice of `∂_z f`.
  have hInt := Spaces.hardyZ_integral_pz_eq_sub (Spaces.pz f) (Spaces.SmoothNbhd.pz hsm) hθ
    (le_refl (0:ℝ)) (le_of_lt hz.1)
  have hkey : Spaces.pz f z θ = ∫ s in (0:ℝ)..z, Spaces.pz (Spaces.pz f) s θ := by
    rw [hInt, h0 θ hθ, sub_zero]
  rw [hkey]
  -- Bound the integral by `M * z`.
  have hb := intervalIntegral.norm_integral_le_of_norm_le_const
    (f := fun s => Spaces.pz (Spaces.pz f) s θ) (a := (0:ℝ)) (b := z)
    (C := Spaces.boxSup 1 (Spaces.pz (Spaces.pz f))) ?_
  · rw [Real.norm_eq_abs] at hb
    rwa [sub_zero, abs_of_pos hz.1] at hb
  · intro x hx
    rw [Set.uIoc_of_le (le_of_lt hz.1)] at hx
    have hxI : x ∈ Set.Icc (0:ℝ) 1 :=
      ⟨le_of_lt hx.1, le_trans hx.2 (le_of_lt hz.2)⟩
    rw [Real.norm_eq_abs]
    exact Spaces.le_boxSup hbdd hxI hθ

end Work.Coercivity
end
end
-- ===== merged: Submission.Work.Coercivity.EL12z_le =====
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

/-- **The Hardy inequality of the paper's `Lemma HardyWeight` in the form used by the
coercivity chain**: `|z⁻¹ L₁₂(f)|²_{L²_z} ≤ 16 |f w|²_{L²}`.

The chain of estimates is
`∫ (L₁₂ f)²/z² ≤ 4 ∫ (L₁₂dens)² ≤ 4·3 ∫ (∫_θ f²)/z² ≤ 12 |f w|²_{L²}`,
where the first step is the Hardy inequality (integration by parts, using that
`∂_z L₁₂(f) = -L₁₂dens(f)` and that the boundary terms `(L₁₂ f)²/z` vanish at `0⁺` and at
`∞`), the second is Cauchy–Schwarz in `θ` against `∫_θ K² ≤ 3`, and the last one uses
`1/z² ≤ w z²`. -/
theorem EL12z_le (f : ℝ → ℝ → ℝ) (hf : HardyHyp f)
    (hfw : MeasureTheory.IntegrableOn
      (Function.uncurry (fun z θ => (f z θ * Spaces.w z) ^ 2)) (Spaces.Iz ×ˢ Spaces.Iθ)) :
    EL12z f ≤ 16 * Ef f := by
  -- almost everywhere integrability of the angular slices of `f²`, from `hfw`
  have hsl := EL12z_ae_slice f hfw
  -- finiteness of `∫ (L₁₂dens)²` and its `L¹` bound by `∫ (∫_θ f²)/z²`
  have hKd := EL12z_Kd f hf hsl
  -- the plain `1/z²` piece of `|f w|²` is bounded by `Ef f`
  have hw := EL12z_weight f hfw hsl
  -- the Hardy inequality `∫ (L₁₂ f)²/z² ≤ 4 ∫ (L₁₂dens)²`
  have hh := EL12z_hardy f hf hKd.1
  -- `Ef f ≥ 0`
  have hEf : 0 ≤ Ef f := by
    rw [Ef, Spaces.L2Sq]
    exact integral_nonneg (fun z => integral_nonneg (fun θ => sq_nonneg _))
  -- `EL12z f = ∫_0^∞ (L₁₂ f)²/z²` (`{0}` is null and `(a/b)² = a²/b²`)
  have h1 : EL12z f = ∫ z in Set.Ioi (0 : ℝ), (L12f f z) ^ 2 / z ^ 2 := by
    rw [EL12z, L2Sqz, Spaces.Iz, MeasureTheory.integral_Ici_eq_integral_Ioi]
    refine integral_congr_ae ?_
    filter_upwards with z
    exact div_pow (L12f f z) z 2
  rw [h1]
  linarith [hh, hKd.2, hw, hEf]

end Work.Coercivity
end
end
-- ===== merged: Submission.Work.Coercivity.F1F2_smooth =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology Interval
open MeasureTheory Set Filter

namespace Work.Coercivity

set_option autoImplicit false

/-! ## The boxes on which `SmoothNbhd` is tested -/





/-! ## `D_θ f` is again smooth on a neighbourhood of the quadrant -/




/-! ## Analyticity of the angular density `z ↦ L12dens K g z` -/



/-! ## The primitive of an analytic function is analytic -/



/-! ## Analyticity of `L₁₂^K(g)` -/


/-! ## The two rational coefficients -/



/-! ## The main statement -/


end Work.Coercivity
end
end
-- ===== merged: Submission.Work.Coercivity.H1IPAddDefs =====
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

/-! ## The weights of the four pairings -/

/-- The weight `w(z)² · sin(2θ)^{-η}` of the three `η`-pairings of `H1IP`. -/
def lamEta (z θ : ℝ) : ℝ := Spaces.w z ^ 2 * (Real.sin (2 * θ)) ^ (-Spaces.eta)

/-- The weight `w(z)² · sin(2θ)^{-γ}` of the `D_θ`-pairing of `H1IP`. -/
def lamGam (α : ℝ) (z θ : ℝ) : ℝ := Spaces.w z ^ 2 * (Real.sin (2 * θ)) ^ (-(Spaces.gam α))

/-- The plain weight `w(z)²` of the third pairing of `H1IP`. -/
def lamW (z θ : ℝ) : ℝ := Spaces.w z ^ 2


/-! ## The honest-pairing predicate -/

/-- `PairHonest ρ A B` says that the pairing integrand `A·B·ρ` has an honest iterated
integral over the quadrant `[0,∞) × [0,π/2]`: every angular slice is integrable, and the
resulting function of `z` is integrable.  Under this hypothesis `wip ρ A B` is a genuine
Lebesgue integral and `wip` is additive in `A`. -/
def PairHonest (ρ A B : ℝ → ℝ → ℝ) : Prop :=
  I2Mem (fun z θ => A z θ * B z θ * ρ z θ)

/-! ## The four weighted blocks -/

/-- `f · w/√(sin 2θ^η)`, the `D_z⁰`-block of the `ℋ¹` integrand (`= U0 f`). -/
def Xeta (f : ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ :=
  fun z θ => f z θ * (Spaces.w z / (Real.sin (2 * θ)) ^ (Spaces.eta / 2))

/-- `D_z f · w/√(sin 2θ^η)`, the `D_z¹`-block (`= U1 f`). -/
def XetaDz (f : ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ :=
  fun z θ => Spaces.Dz f z θ * (Spaces.w z / (Real.sin (2 * θ)) ^ (Spaces.eta / 2))

/-- `D_θ f · W`, the `D_θ`-block (`= U2 α f`). -/
def XgamDth (α : ℝ) (f : ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ :=
  fun z θ => Spaces.Dth f z θ * Spaces.Wt α z θ

/-- `f · w`, the block of the plain `w²`-pairing. -/
def Xw (f : ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ := fun z θ => f z θ * Spaces.w z

end Work.Coercivity
end
end
-- ===== merged: Submission.Work.Coercivity.KC0_eq_double =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.Coercivity


end Work.Coercivity
end
-- ===== merged: Submission.Work.Coercivity.L12_facts_n =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology ContDiff ENNReal
open MeasureTheory Set Filter

namespace Work.Coercivity

set_option autoImplicit false

/-! ## Bridges to the `Work.Elliptic` vocabulary -/


/-- `Coercivity.L12f g` is `Elliptic.L12 g` (`Spaces.K = FM.Kpaper`). -/
theorem L12f_eq_Elliptic_L12 (g : ℝ → ℝ → ℝ) :
    L12f g = Work.Elliptic.L12 g := by
  funext z
  rw [L12f, Work.Elliptic.L12_eq_FM]
  rfl



/-! ## Joint analyticity of the density integrand -/


/-! ## Analyticity of the tail integral from analyticity of the density -/




/-! ## The main theorem -/


end Work.Coercivity
end
end
-- ===== merged: Submission.Work.Coercivity.L12_z_byparts =====
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

/-- Under the Hardy hypotheses on `f`, the radial weight `(1+z)/z³` times the square of
`L₁₂(f)` is integrable on `(0,∞)`: `(1+z)/z³ = 1/z³ + 1/z²`, and on `(0,∞)` one has
`1/z³ ≤ 1/z⁴ + 1/z²` (for `z ≤ 1` use the first summand, for `z ≥ 1` the second), so
`HardyHyp.intA` for `j = 2` and `j = 1` provides an integrable dominating function. -/
theorem L12_z_byparts_rhs_integrable (f : ℝ → ℝ → ℝ) (hf : HardyHyp f) :
    IntegrableOn (fun z : ℝ => (1 + z) / z ^ 3 * (L12f f z) ^ 2) (Set.Ioi (0:ℝ)) := by
  -- `L₁₂(f)` is differentiable, hence continuous, on `(0,∞)`.
  have hdL : ∀ z ∈ Set.Ioi (0:ℝ), HasDerivAt (fun x => L12f f x)
      (-(FM.L12dens Spaces.K f z)) z := by
    intro z hz
    exact Work.FM.hasDerivAt_L12 (K := Spaces.K) (f := f) (a := 0) (ρ := z)
      hf.hint (hf.hcont z hz) hz
  have hLcont : ContinuousOn (fun z => L12f f z) (Set.Ioi (0:ℝ)) := by
    have hd : DifferentiableOn ℝ (fun z => L12f f z) (Set.Ioi (0:ℝ)) := by
      intro z hz
      exact (hdL z hz).differentiableAt.differentiableWithinAt
    exact hd.continuousOn
  -- measurability of the integrand
  have hmeas : AEStronglyMeasurable (fun z => (1 + z) / z ^ 3 * (L12f f z) ^ 2)
      (volume.restrict (Set.Ioi (0:ℝ))) := by
    have hc : ContinuousOn (fun z : ℝ => (1 + z) / z ^ 3) (Set.Ioi (0:ℝ)) := by
      have hnum : ContinuousOn (fun z : ℝ => 1 + z) (Set.Ioi (0:ℝ)) :=
        (continuous_const.add continuous_id).continuousOn
      have hden : ContinuousOn (fun z : ℝ => z ^ 3) (Set.Ioi (0:ℝ)) :=
        (continuous_id.pow 3).continuousOn
      exact hnum.div hden (fun z hz => pow_ne_zero 3 (ne_of_gt hz))
    have hsq : ContinuousOn (fun z : ℝ => (L12f f z) ^ 2) (Set.Ioi (0:ℝ)) := hLcont.pow 2
    exact (hc.mul hsq).aestronglyMeasurable measurableSet_Ioi
  -- the two integrable comparison functions supplied by `HardyHyp.intA`
  have h1 : IntegrableOn (fun z => (L12f f z) ^ 2 / z ^ 2) (Set.Ioi (0:ℝ)) := by
    refine IntegrableOn.congr_fun (hf.intA 1 (by norm_num)) (fun z _ => ?_) measurableSet_Ioi
    norm_num
  have h2 : IntegrableOn (fun z => (L12f f z) ^ 2 / z ^ 4) (Set.Ioi (0:ℝ)) := by
    refine IntegrableOn.congr_fun (hf.intA 2 (by norm_num)) (fun z _ => ?_) measurableSet_Ioi
    norm_num
  have hdom : Integrable
      (fun z => 2 * ((L12f f z) ^ 2 / z ^ 2) + 2 * ((L12f f z) ^ 2 / z ^ 4))
      (volume.restrict (Set.Ioi (0:ℝ))) := (h1.const_mul 2).add (h2.const_mul 2)
  refine hdom.mono hmeas ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with z hz
  have hz0 : 0 < z := hz
  have hLnn : 0 ≤ (L12f f z) ^ 2 := sq_nonneg _
  -- the pointwise bound on the coefficient `(1+z)/z³`
  have hcoef : (1 + z) / z ^ 3 ≤ 2 / z ^ 2 + 2 / z ^ 4 := by
    rw [← sub_nonneg]
    have key : 2 / z ^ 2 + 2 / z ^ 4 - (1 + z) / z ^ 3 = (z ^ 2 - z + 2) / z ^ 4 := by
      field_simp
      ring
    rw [key]
    exact div_nonneg (by nlinarith [sq_nonneg (z - 1 / 2)]) (by positivity)
  rw [Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_nonneg (by positivity : (0:ℝ) ≤ (1 + z) / z ^ 3 * (L12f f z) ^ 2),
    abs_of_nonneg (by positivity :
      (0:ℝ) ≤ 2 * ((L12f f z) ^ 2 / z ^ 2) + 2 * ((L12f f z) ^ 2 / z ^ 4))]
  calc (1 + z) / z ^ 3 * (L12f f z) ^ 2 ≤ (2 / z ^ 2 + 2 / z ^ 4) * (L12f f z) ^ 2 :=
        mul_le_mul_of_nonneg_right hcoef hLnn
    _ = 2 * ((L12f f z) ^ 2 / z ^ 2) + 2 * ((L12f f z) ^ 2 / z ^ 4) := by ring

/-- **The `z`-integration by parts of the weighted Hardy identity.**  With
`w(z) = (1+z)²/z²`, `L₁₂(f)(z) = ∫_z^∞ ∫_0^{π/2} K(θ)f(s,θ)/s dθ ds` and `K(θ) = 3 sinθ cos²θ`:
`∫_0^∞ w/z · L₁₂(f) · (∫_θ K f) = - ∫_0^∞ (1+z)/z³ · L₁₂(f)²`. -/
theorem L12_z_byparts (f : ℝ → ℝ → ℝ) (hf : HardyHyp f)
    (hint : MeasureTheory.IntegrableOn
      (Function.uncurry (fun z θ => Spaces.w z / z * L12f f z * (Spaces.K θ * f z θ)))
      (Spaces.Iz ×ˢ Spaces.Iθ)) :
    (∫ z in Set.Ioi (0:ℝ),
        Spaces.w z / z * L12f f z * (∫ θ in Spaces.Iθ, Spaces.K θ * f z θ))
      = - ∫ z in Set.Ioi (0:ℝ), (1 + z) / z ^ 3 * (L12f f z) ^ 2 := by
  -- ### Step 1: the angular integral is `z · L12dens(f)(z)`
  have hmoment : ∀ z ∈ Set.Ioi (0:ℝ),
      (∫ θ in Spaces.Iθ, Spaces.K θ * f z θ) = z * FM.L12dens Spaces.K f z := by
    intro z hz
    rw [FM.L12dens_eq (K := Spaces.K) (f := f) (ne_of_gt hz)]
    simp only [Spaces.Iθ]
    rw [mul_comm, div_mul_cancel₀ _ (ne_of_gt hz)]
  -- ### Step 2: pointwise identification of the integrand of the left-hand side
  have hcongr_on : Set.EqOn
      (fun z => Spaces.w z / z * L12f f z * (∫ θ in Spaces.Iθ, Spaces.K θ * f z θ))
      (fun z => Spaces.w z * L12f f z * FM.L12dens Spaces.K f z) (Set.Ioi (0:ℝ)) := by
    intro z hz
    show Spaces.w z / z * L12f f z * (∫ θ in Spaces.Iθ, Spaces.K θ * f z θ)
      = Spaces.w z * L12f f z * FM.L12dens Spaces.K f z
    rw [hmoment z hz]
    have hz0 : z ≠ 0 := ne_of_gt hz
    field_simp
  -- ### Step 3: integrability of the left-hand side, from Fubini applied to `hint`
  have hΨ : IntegrableOn
      (fun z => Spaces.w z / z * L12f f z * (∫ θ in Spaces.Iθ, Spaces.K θ * f z θ))
      (Set.Ioi (0:ℝ)) := by
    have hprod : Integrable
        (Function.uncurry (fun z θ => Spaces.w z / z * L12f f z * (Spaces.K θ * f z θ)))
        ((volume.restrict Spaces.Iz).prod (volume.restrict Spaces.Iθ)) := by
      have h := hint
      rw [IntegrableOn, Measure.volume_eq_prod, ← Measure.prod_restrict] at h
      exact h
    have hslice := hprod.integral_prod_left
    have hslice' : IntegrableOn
        (fun z => ∫ θ in Spaces.Iθ, Spaces.w z / z * L12f f z * (Spaces.K θ * f z θ))
        Spaces.Iz := hslice
    have hpull : Set.EqOn
        (fun z => ∫ θ in Spaces.Iθ, Spaces.w z / z * L12f f z * (Spaces.K θ * f z θ))
        (fun z => Spaces.w z / z * L12f f z * (∫ θ in Spaces.Iθ, Spaces.K θ * f z θ))
        Spaces.Iz := by
      intro z hz
      show (∫ θ in Spaces.Iθ, Spaces.w z / z * L12f f z * (Spaces.K θ * f z θ))
        = Spaces.w z / z * L12f f z * (∫ θ in Spaces.Iθ, Spaces.K θ * f z θ)
      rw [integral_const_mul]
    exact (hslice'.congr_fun hpull measurableSet_Ici).mono_set Set.Ioi_subset_Ici_self
  have hWLD : IntegrableOn (fun z => Spaces.w z * L12f f z * FM.L12dens Spaces.K f z)
      (Set.Ioi (0:ℝ)) := hΨ.congr_fun hcongr_on measurableSet_Ioi
  -- ### Step 4: the derivative data
  have hdL : ∀ z ∈ Set.Ioi (0:ℝ), HasDerivAt (fun x => L12f f x)
      (-(FM.L12dens Spaces.K f z)) z := by
    intro z hz
    exact Work.FM.hasDerivAt_L12 (K := Spaces.K) (f := f) (a := 0) (ρ := z)
      hf.hint (hf.hcont z hz) hz
  have hdW : ∀ z ∈ Set.Ioi (0:ℝ), HasDerivAt Spaces.w (-2 * (1 + z) / z ^ 3) z :=
    fun z hz => hasDerivAt_w (ne_of_gt hz)
  have hdV : ∀ z ∈ Set.Ioi (0:ℝ), HasDerivAt (fun x => (L12f f x) ^ 2)
      (2 * L12f f z * (-(FM.L12dens Spaces.K f z))) z := by
    intro z hz
    have h := (hdL z hz).pow 2
    have hd : (↑2 * L12f f z ^ (2 - 1) * (-(FM.L12dens Spaces.K f z)))
        = 2 * L12f f z * (-(FM.L12dens Spaces.K f z)) := by norm_num
    exact h.congr_deriv hd
  -- ### Step 5: integrability of the two pieces of the derivative of `w · L₁₂(f)²`
  have hG : IntegrableOn (fun z => (1 + z) / z ^ 3 * (L12f f z) ^ 2) (Set.Ioi (0:ℝ)) :=
    L12_z_byparts_rhs_integrable f hf
  have hG' : IntegrableOn (fun z => (-2 * (1 + z) / z ^ 3) * (L12f f z) ^ 2)
      (Set.Ioi (0:ℝ)) := by
    refine IntegrableOn.congr_fun (hG.const_mul (-2)) (fun z _ => ?_) measurableSet_Ioi
    show -2 * ((1 + z) / z ^ 3 * (L12f f z) ^ 2) = (-2 * (1 + z) / z ^ 3) * (L12f f z) ^ 2
    ring
  have hWLD' : IntegrableOn
      (fun z => Spaces.w z * (2 * L12f f z * (-(FM.L12dens Spaces.K f z))))
      (Set.Ioi (0:ℝ)) := by
    refine IntegrableOn.congr_fun (hWLD.const_mul (-2)) (fun z _ => ?_) measurableSet_Ioi
    show -2 * (Spaces.w z * L12f f z * FM.L12dens Spaces.K f z)
      = Spaces.w z * (2 * L12f f z * (-(FM.L12dens Spaces.K f z)))
    ring
  -- ### Step 6: integration by parts, with vanishing boundary terms from `HardyHyp`
  have hIBP := MeasureTheory.integral_Ioi_mul_deriv_eq_deriv_mul
    (a := (0:ℝ)) (a' := (0:ℝ)) (b' := (0:ℝ))
    (u := Spaces.w) (u' := fun z => -2 * (1 + z) / z ^ 3)
    (v := fun z => (L12f f z) ^ 2)
    (v' := fun z => 2 * L12f f z * (-(FM.L12dens Spaces.K f z)))
    hdW hdV hWLD' hG'
    (by
      show Tendsto (fun z => Spaces.w z * (L12f f z) ^ 2) (𝓝[>] (0:ℝ)) (𝓝 0)
      exact (hf.bd0 0 (by norm_num)).2)
    (by
      show Tendsto (fun z => Spaces.w z * (L12f f z) ^ 2) atTop (𝓝 0)
      exact (hf.bdTop 0 (by norm_num)).2)
  -- ### Step 7: rewrite both integrals of the identity in the required form
  have h1 : (∫ x in Set.Ioi (0:ℝ), Spaces.w x * (2 * L12f f x * (-(FM.L12dens Spaces.K f x))))
      = -2 * ∫ x in Set.Ioi (0:ℝ), Spaces.w x * L12f f x * FM.L12dens Spaces.K f x := by
    rw [show (fun x => Spaces.w x * (2 * L12f f x * (-(FM.L12dens Spaces.K f x))))
        = fun x => -2 * (Spaces.w x * L12f f x * FM.L12dens Spaces.K f x) from by
      funext x; ring]
    rw [integral_const_mul]
  have h2 : (∫ x in Set.Ioi (0:ℝ), (-2 * (1 + x) / x ^ 3) * (L12f f x) ^ 2)
      = -2 * ∫ x in Set.Ioi (0:ℝ), (1 + x) / x ^ 3 * (L12f f x) ^ 2 := by
    rw [show (fun x => (-2 * (1 + x) / x ^ 3) * (L12f f x) ^ 2)
        = fun x => -2 * ((1 + x) / x ^ 3 * (L12f f x) ^ 2) from by
      funext x; ring]
    rw [integral_const_mul]
  have hkey : (∫ x in Set.Ioi (0:ℝ), Spaces.w x * L12f f x * FM.L12dens Spaces.K f x)
      = - ∫ x in Set.Ioi (0:ℝ), (1 + x) / x ^ 3 * (L12f f x) ^ 2 := by
    rw [h1, h2] at hIBP
    linarith
  rw [setIntegral_congr_fun measurableSet_Ioi hcongr_on]
  exact hkey

end Work.Coercivity
end
end
-- ===== merged: Submission.Work.Coercivity.L_mul_w_deriv =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.Coercivity

theorem L_mul_w_deriv {f : ℝ → ℝ → ℝ} {z θ : ℝ} (hz : 0 < z)
    (hf : HasDerivAt (fun z' => f z' θ) (Spaces.pz f z θ) z) :
    L f z θ * Spaces.w z
      = f z θ * Spaces.w z + z * Spaces.pz (fun z θ => f z θ * Spaces.w z) z θ := by
  rw [pz_mul_w (ne_of_gt hz) hf, L_mul_w f z θ hz]

end Work.Coercivity
end
-- ===== merged: Submission.Work.Coercivity.angRad_mixed =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open scoped Real Topology
open Set Filter MeasureTheory

namespace Work.Coercivity





end Work.Coercivity
end
-- ===== merged: Submission.Work.Coercivity.bound_Z2 =====
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

/-! ## The pointwise arithmetic behind the `Z₂` bound

`Z₂ f z θ = 2z/(1+z)² · f z θ`, so the integrand of `wip Weta (Z2 f) (Dz f)` is
`c(z)·f·D_z f·W` with `c(z) = 2z/(1+z)²`.  For `z ≥ 0` one has `0 ≤ c(z) ≤ 1/2`, and the
elementary inequality
`|c·u·v·X| ≤ 4u²X + (1/64)v²X` (AM-GM, using `c ≤ 1/2`) for `X ≥ 0` gives both the
integrability (by domination) and the lower bound of the statement. -/






end Work.Coercivity
end
end
-- ===== merged: Submission.Work.Coercivity.box_joint_bound =====
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

/-- If `∂_z (z (D_z f(z,θ) w(z))²)` is bounded by `C` on `(0,δ) × Iθ`, then it is
bounded by some `M > 0` on all of `(0,R) × Iθ`. -/
theorem box_joint_bound (f : ℝ → ℝ → ℝ) (hsm : Spaces.SmoothNbhd f)
    (hC : ∃ C δ : ℝ, 0 < C ∧ 0 < δ ∧ ∀ z ∈ Set.Ioo 0 δ, ∀ θ ∈ Spaces.Iθ,
      |deriv (fun z' => z' * (Spaces.Dz f z' θ * Spaces.w z') ^ 2) z| ≤ C)
    {R : ℝ} (hR : 0 < R) :
    ∃ M : ℝ, 0 < M ∧ ∀ z ∈ Set.Ioo 0 R, ∀ θ ∈ Spaces.Iθ,
      |deriv (fun z' => z' * (Spaces.Dz f z' θ * Spaces.w z') ^ 2) z| ≤ M := by
  obtain ⟨C, δ, hCpos, hδpos, hCbd⟩ := hC
  -- `∂_z (z (D_z f · w)²)` is the partial derivative `pz` of `BoxG f`.
  have hpz : ∀ z θ : ℝ, deriv (fun z' => z' * (Spaces.Dz f z' θ * Spaces.w z') ^ 2) z
      = Spaces.pz (BoxG f) z θ := fun z _ => rfl
  by_cases hRδ : R ≤ δ
  · -- The whole interval `(0,R)` lies in the range of the assumed bound.
    refine ⟨max C 1, lt_of_lt_of_le zero_lt_one (le_max_right _ _), ?_⟩
    intro z hz θ hθ
    rw [hpz]
    exact le_trans (hCbd z ⟨hz.1, lt_of_lt_of_le hz.2 hRδ⟩ θ hθ) (le_max_left _ _)
  · -- Otherwise `δ < R` and the compact box `[δ,R] × Iθ` lies in the smoothness range.
    simp only [not_le] at hRδ
    have hcont : ContinuousOn (Function.uncurry (Spaces.pz (BoxG f)))
        (Set.Icc δ R ×ˢ Spaces.Iθ) := by
      refine (contDiffOn_uncurry_pz_BoxG f hsm).continuousOn.mono ?_
      rintro ⟨z, θ⟩ ⟨hz, hθ⟩
      simp only [Set.mem_prod, Set.mem_Ioi, Set.mem_Ioo, Spaces.Iθ, Set.mem_Icc] at hθ ⊢
      exact ⟨lt_of_lt_of_le hδpos hz.1, by linarith [hθ.1], by linarith [hθ.2, Real.pi_pos]⟩
    obtain ⟨M2, hM2⟩ := (isCompact_Icc.prod isCompact_Icc).exists_bound_of_continuousOn hcont
    refine ⟨max (max C M2) 1, lt_of_lt_of_le zero_lt_one (le_max_right _ _), ?_⟩
    intro z hz θ hθ
    rw [hpz]
    rcases lt_or_ge z δ with hzlt | hzge
    · have h2 := hCbd z ⟨hz.1, hzlt⟩ θ hθ
      rw [hpz] at h2
      exact le_trans h2 (le_trans (le_max_left C M2) (le_max_left _ _))
    · have h1 := hM2 (z, θ) ⟨⟨hzge, le_of_lt hz.2⟩, hθ⟩
      rw [Real.norm_eq_abs] at h1
      exact le_trans h1 (le_trans (le_max_right C M2) (le_max_left _ _))

end Work.Coercivity
end
end
-- ===== merged: Submission.Work.Coercivity.contDiffOn_infty_integral_Itheta =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology ENNReal
open MeasureTheory Set Filter

namespace Work.Coercivity

set_option autoImplicit false

/-! ## The angular interval `Iθ = [0,π/2]` -/

theorem measurableSet_Itheta : MeasurableSet Work.Spaces.Iθ := by
  rw [Work.Spaces.Iθ]; exact measurableSet_Icc

theorem isCompact_Itheta : IsCompact Work.Spaces.Iθ := by
  rw [Work.Spaces.Iθ]; exact isCompact_Icc

theorem isFiniteMeasure_restrict_Itheta : IsFiniteMeasure (volume.restrict Work.Spaces.Iθ) := by
  rw [isFiniteMeasure_restrict]
  exact isCompact_Itheta.measure_ne_top

/-- The `θ`-slice of a function that is jointly continuous on `V ×ˢ Iθ` is continuous in `θ`
on `Iθ`. -/
theorem continuousOn_slice_of_continuousOn_uncurry {g : ℝ → ℝ → ℝ} {V : Set ℝ}
    (hg : ContinuousOn (Function.uncurry g) (V ×ˢ Work.Spaces.Iθ)) {s : ℝ} (hs : s ∈ V) :
    ContinuousOn (fun θ => g s θ) Work.Spaces.Iθ := by
  have h2 : ContinuousOn (fun θ : ℝ => (s, θ)) Work.Spaces.Iθ :=
    continuousOn_const.prodMk continuousOn_id
  have h3 := hg.comp h2 (fun θ hθ => ⟨hs, hθ⟩)
  simpa [Function.comp_def, Function.uncurry] using h3

/-- **Continuity of the parametric integral over `Iθ`.**  If `g` is jointly continuous on
`V ×ˢ Iθ` with `V` open, then `s ↦ ∫_θ g s θ` is continuous on `V`.  (Dominated convergence,
the dominating constant being the sup of `|g|` on a compact neighbourhood of the point crossed
with `Iθ`.) -/
theorem continuousOn_integral_Itheta_of_continuousOn {g : ℝ → ℝ → ℝ} {V : Set ℝ}
    (hV : IsOpen V) (hg : ContinuousOn (Function.uncurry g) (V ×ˢ Work.Spaces.Iθ)) :
    ContinuousOn (fun s => ∫ θ in Work.Spaces.Iθ, g s θ) V := by
  have hslice : ∀ s ∈ V, ContinuousOn (fun θ => g s θ) Work.Spaces.Iθ :=
    fun s hs => continuousOn_slice_of_continuousOn_uncurry hg hs
  intro s₀ hs₀
  have hscont : ∀ θ ∈ Work.Spaces.Iθ, ContinuousAt (fun s => g s θ) s₀ := by
    intro θ hθ
    have h1 : ContinuousWithinAt (Function.uncurry g) (V ×ˢ Work.Spaces.Iθ) (s₀, θ) :=
      hg _ ⟨hs₀, hθ⟩
    have h2 : ContinuousWithinAt (fun s : ℝ => (s, θ)) V s₀ :=
      continuousWithinAt_id.prodMk continuousWithinAt_const
    have h3 := h1.comp (f := fun s : ℝ => (s, θ)) (s := V) (t := V ×ˢ Work.Spaces.Iθ)
      (x := s₀) h2 (fun s hs => ⟨hs, hθ⟩)
    have h4 : ContinuousWithinAt (fun s => g s θ) V s₀ := by
      simpa [Function.comp_def, Function.uncurry] using h3
    exact h4.continuousAt (hV.mem_nhds hs₀)
  obtain ⟨δ, hδpos, hδV⟩ := Metric.mem_nhds_iff.1 (hV.mem_nhds hs₀)
  set K : Set ℝ := Set.Icc (s₀ - δ / 2) (s₀ + δ / 2) with hKdef
  have hKc : IsCompact K := by rw [hKdef]; exact isCompact_Icc
  have hKV : K ⊆ V := by
    intro x hx
    apply hδV
    rw [Metric.mem_ball, Real.dist_eq, abs_lt]
    refine ⟨?_, ?_⟩ <;> linarith [hx.1, hx.2, hδpos]
  have hcontK : ContinuousOn (Function.uncurry g) (K ×ˢ Work.Spaces.Iθ) :=
    hg.mono (Set.prod_mono hKV (subset_refl _))
  obtain ⟨C, hC⟩ := (hKc.prod isCompact_Itheta).exists_bound_of_continuousOn hcontK
  have hfin := isFiniteMeasure_restrict_Itheta
  have key : ContinuousAt (fun s => ∫ θ in Work.Spaces.Iθ, g s θ) s₀ := by
    refine tendsto_integral_filter_of_norm_le_const (F := fun s θ => g s θ)
      (f := fun θ => g s₀ θ) ?_ ?_ ?_
    · filter_upwards [hV.mem_nhds hs₀] with s hs
      exact (hslice s hs).aestronglyMeasurable measurableSet_Itheta
    · refine ⟨C, ?_⟩
      have hmem : s₀ ∈ Set.Ioo (s₀ - δ / 2) (s₀ + δ / 2) := ⟨by linarith, by linarith⟩
      filter_upwards [isOpen_Ioo.mem_nhds hmem] with s hs
      rw [ae_restrict_iff' measurableSet_Itheta]
      refine Eventually.of_forall fun ω hω => ?_
      simpa [Function.uncurry] using hC (s, ω) ⟨Set.Ioo_subset_Icc_self hs, hω⟩
    · rw [ae_restrict_iff' measurableSet_Itheta]
      exact Eventually.of_forall fun ω hω => (hscont ω hω).tendsto
  exact key.continuousWithinAt

/-- **Differentiation under the integral sign over `Iθ`.**  If `g` and the candidate
`s`-derivative `g'` are jointly continuous on `V ×ˢ Iθ` (`V` open) and `s ↦ g s θ` has
derivative `s ↦ g' s θ` at every `s ∈ V`, for every `θ ∈ Iθ`, then the parametric integral
has derivative the integral of `g'`. -/
theorem hasDerivAt_integral_Itheta_of_hasDerivAt {g g' : ℝ → ℝ → ℝ} {V : Set ℝ}
    (hV : IsOpen V) {s₀ : ℝ} (hs₀ : s₀ ∈ V)
    (hg : ContinuousOn (Function.uncurry g) (V ×ˢ Work.Spaces.Iθ))
    (hg' : ContinuousOn (Function.uncurry g') (V ×ˢ Work.Spaces.Iθ))
    (hdiff : ∀ θ ∈ Work.Spaces.Iθ, ∀ s ∈ V, HasDerivAt (fun s => g s θ) (g' s θ) s) :
    HasDerivAt (fun s => ∫ θ in Work.Spaces.Iθ, g s θ) (∫ θ in Work.Spaces.Iθ, g' s₀ θ) s₀ := by
  have hslice : ∀ s ∈ V, ContinuousOn (fun θ => g s θ) Work.Spaces.Iθ :=
    fun s hs => continuousOn_slice_of_continuousOn_uncurry hg hs
  have hslice' : ∀ s ∈ V, ContinuousOn (fun θ => g' s θ) Work.Spaces.Iθ :=
    fun s hs => continuousOn_slice_of_continuousOn_uncurry hg' hs
  obtain ⟨δ, hδpos, hδV⟩ := Metric.mem_nhds_iff.1 (hV.mem_nhds hs₀)
  set K : Set ℝ := Set.Icc (s₀ - δ / 2) (s₀ + δ / 2) with hKdef
  have hKc : IsCompact K := by rw [hKdef]; exact isCompact_Icc
  have hKV : K ⊆ V := by
    intro x hx
    apply hδV
    rw [Metric.mem_ball, Real.dist_eq, abs_lt]
    refine ⟨?_, ?_⟩ <;> linarith [hx.1, hx.2, hδpos]
  have hcontK : ContinuousOn (Function.uncurry g') (K ×ˢ Work.Spaces.Iθ) :=
    hg'.mono (Set.prod_mono hKV (subset_refl _))
  obtain ⟨C, hC⟩ := (hKc.prod isCompact_Itheta).exists_bound_of_continuousOn hcontK
  have hfin := isFiniteMeasure_restrict_Itheta
  have hmem : s₀ ∈ Set.Ioo (s₀ - δ / 2) (s₀ + δ / 2) := ⟨by linarith, by linarith⟩
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := volume.restrict Work.Spaces.Iθ) (𝕜 := ℝ)
    (F := fun s θ => g s θ) (F' := fun s θ => g' s θ) (bound := fun _ => C)
    (x₀ := s₀) (s := Set.Ioo (s₀ - δ / 2) (s₀ + δ / 2))
    (isOpen_Ioo.mem_nhds hmem) ?_ ?_ ?_ ?_ ?_ ?_
  · exact key.2
  · filter_upwards [isOpen_Ioo.mem_nhds hmem, hV.mem_nhds hs₀] with x hxW hxV
    exact (hslice x hxV).aestronglyMeasurable measurableSet_Itheta
  · exact (hslice s₀ hs₀).integrableOn_compact isCompact_Itheta
  · exact (hslice' s₀ hs₀).aestronglyMeasurable measurableSet_Itheta
  · rw [ae_restrict_iff' measurableSet_Itheta]
    refine Eventually.of_forall fun a ha x hx => ?_
    have hxs : x ∈ K := Set.Ioo_subset_Icc_self hx
    simpa [Function.uncurry] using hC (x, a) ⟨hxs, ha⟩
  · exact integrable_const C
  · rw [ae_restrict_iff' measurableSet_Itheta]
    refine Eventually.of_forall fun a ha x hx => ?_
    exact hdiff a ha x (hKV (Set.Ioo_subset_Icc_self hx))


end Work.Coercivity
end
end
-- ===== merged: Submission.Work.Coercivity.deriv_zw_sq_eq =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.Coercivity


end Work.Coercivity
end
-- ===== merged: Submission.Work.Coercivity.deriv_zw_sq_integral =====
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



end Work.Coercivity
end
end
-- ===== merged: Submission.Work.Coercivity.slice_Z16_integrable =====
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

/-! ## Slice integrability of the four terms of the `Z₁₆`-identity

The pointwise identity `slice_Z16` expresses the slice integrand
`Z₁₆ f z θ · D_z f z θ · Weta z θ` as a sum of three terms, each of which is a
*bounded* continuous function of `θ` multiplied by the angular weight
`sin(2θ)^{-η}`.  Since the two endpoint singularities of `sin(2θ)^{-η}` are
integrable (`0 < η < 1`), every one of the four integrands below is integrable
on `Iθ`.

The only structural input is that `f` is smooth on an open neighbourhood of the
closed quadrant, so that for `z > 0` every `θ`-slice of `f`, of `D_z f`, of
`D_θ(D_z f)` and of the auxiliary `z ↦ z (D_z f(z,θ) w(z))²` is continuous (hence
bounded) on the compact interval `Iθ`. -/

/-- The angular factor `sin(2θ)^{-η}` is integrable over `Iθ`: its endpoint
singularities are integrable because `0 < η < 1`. -/
private lemma sin_neg_eta_integrableOn :
    IntegrableOn (fun θ : ℝ => (Real.sin (2 * θ)) ^ (-Spaces.eta)) Spaces.Iθ :=
  (Spaces.sin_two_rpow (-Spaces.eta) (by norm_num [Spaces.eta])
    (by norm_num [Spaces.eta])).1

/-- The `θ`-slice `θ ↦ g z θ` of a function smooth on an open neighbourhood of the
closed quadrant is continuous on `Iθ`, for every `z > 0`. -/
private lemma continuousOn_slice_of_smoothNbhd {g : ℝ → ℝ → ℝ} (hg : Spaces.SmoothNbhd g)
    {z : ℝ} (hz : 0 < z) : ContinuousOn (fun θ => g z θ) Spaces.Iθ := by
  have hz' : z ∈ Set.Ioi (-1:ℝ) := by simp only [Set.mem_Ioi]; linarith
  have hmap : Set.MapsTo (fun θ : ℝ => (z, θ)) Spaces.Iθ Spaces.nbhU := by
    intro θ hθ
    rw [Spaces.nbhU, Set.mem_prod]
    exact ⟨hz', by rw [Set.mem_Ioo]; exact ⟨by linarith [hθ.1], by linarith [hθ.2, Real.pi_pos]⟩⟩
  have hcont : ContinuousOn (Function.uncurry g) Spaces.nbhU := hg.continuousOn
  have hiota : ContinuousOn (fun θ : ℝ => (z, θ)) Spaces.Iθ :=
    (continuous_const.prodMk continuous_id).continuousOn
  simpa [Function.comp_def, Function.uncurry] using hcont.comp hiota hmap

/-- The open set `(0,∞) × (-1, π/2+1)` on which the radial weight `w` is smooth (it
is only singular at `z = 0`). -/
private def Vw : Set (ℝ × ℝ) := Set.Ioi (0:ℝ) ×ˢ Set.Ioo (-1:ℝ) (Real.pi / 2 + 1)

private lemma isOpen_Vw : IsOpen Vw := isOpen_Ioi.prod isOpen_Ioo

private lemma Vw_subset_nbhU : Vw ⊆ Spaces.nbhU := by
  intro p hp
  have hp' : p.1 ∈ Set.Ioi (0:ℝ) ∧ p.2 ∈ Set.Ioo (-1:ℝ) (Real.pi/2+1) := hp
  exact ⟨by simp only [Set.mem_Ioi] at hp' ⊢; linarith [hp'.1], hp'.2⟩

/-- `w(z) = (1+z)²/z²` is smooth on `(0,∞) × (-1,π/2+1)`. -/
private lemma contDiffOn_w_Vw :
    ContDiffOn ℝ ⊤ (fun p : ℝ × ℝ => Spaces.w p.1) Vw := by
  have hnum : ContDiffOn ℝ ⊤ (fun p : ℝ × ℝ => (1 + p.1) ^ 2) Vw :=
    ((contDiff_const.add contDiff_fst).pow 2).contDiffOn
  have hden : ContDiffOn ℝ ⊤ (fun p : ℝ × ℝ => p.1 ^ 2) Vw :=
    (contDiff_fst.pow 2).contDiffOn
  have hne : ∀ p ∈ Vw, p.1 ^ 2 ≠ 0 := fun p hp => pow_ne_zero 2 (ne_of_gt hp.1)
  refine (hnum.div hden hne).congr (fun p hp => ?_)
  simp [Spaces.w]

/-- The `z`-derivative `θ ↦ ∂_z (z ↦ z (D_z f(z,θ) · w(z))²)(z)` is continuous in `θ`
on `Iθ`: it is the `z`-partial of the smooth function `(z,θ) ↦ z (D_z f(z,θ) w(z))²`,
which is smooth on `Vw` because `D_z f` is smooth on `nbhU ⊇ Vw` and `w` is smooth
on `Vw`. -/
private lemma continuousOn_deriv_zw_Dz_sq (f : ℝ → ℝ → ℝ) (hsm : Spaces.SmoothNbhd f)
    {z : ℝ} (hz : 0 < z) :
    ContinuousOn (fun θ => deriv (fun z' => z' * (Spaces.Dz f z' θ * Spaces.w z') ^ 2) z)
      Spaces.Iθ := by
  have hB : ContDiffOn ℝ ⊤ (fun p : ℝ × ℝ => Spaces.Dz f p.1 p.2) Vw := by
    convert ContDiffOn.mono (Spaces.SmoothNbhd.Dz hsm) Vw_subset_nbhU using 1
    ext p; rfl
  have hW : ContDiffOn ℝ ⊤ (fun p : ℝ × ℝ => Spaces.w p.1) Vw := contDiffOn_w_Vw
  have hG : ContDiffOn ℝ ⊤
      (Function.uncurry (fun z θ => z * (Spaces.Dz f z θ * Spaces.w z) ^ 2)) Vw := by
    have h1 : ContDiffOn ℝ ⊤ (fun p : ℝ × ℝ => Spaces.Dz f p.1 p.2 * Spaces.w p.1) Vw :=
      hB.mul hW
    have h2 : ContDiffOn ℝ ⊤
        (fun p : ℝ × ℝ => (Spaces.Dz f p.1 p.2 * Spaces.w p.1) ^ 2) Vw := h1.pow 2
    have h3 : ContDiffOn ℝ ⊤
        (fun p : ℝ × ℝ => p.1 * (Spaces.Dz f p.1 p.2 * Spaces.w p.1) ^ 2) Vw :=
      (contDiff_fst.contDiffOn).mul h2
    convert h3 using 1
    ext p; rfl
  have hd : ContDiffOn ℝ ⊤
      (Function.uncurry (Spaces.pz (fun z θ => z * (Spaces.Dz f z θ * Spaces.w z) ^ 2))) Vw :=
    Spaces.contDiffOn_uncurry_pz isOpen_Vw hG
  have hcont : ContinuousOn
      (fun θ => Spaces.pz (fun z θ => z * (Spaces.Dz f z θ * Spaces.w z) ^ 2) z θ)
      Spaces.Iθ := by
    have hmap : Set.MapsTo (fun θ : ℝ => (z, θ)) Spaces.Iθ Vw := by
      intro θ hθ
      exact ⟨by simp only [Set.mem_Ioi]; exact hz,
        by rw [Set.mem_Ioo]; exact ⟨by linarith [hθ.1], by linarith [hθ.2, Real.pi_pos]⟩⟩
    have hiota : ContinuousOn (fun θ : ℝ => (z, θ)) Spaces.Iθ :=
      (continuous_const.prodMk continuous_id).continuousOn
    simpa [Function.comp_def, Function.uncurry] using hd.continuousOn.comp hiota hmap
  simpa [Spaces.pz] using hcont

theorem slice_Z16_integrable (f : ℝ → ℝ → ℝ) (hsm : Spaces.SmoothNbhd f) {z : ℝ} (hz : 0 < z) :
    MeasureTheory.IntegrableOn (fun θ => L (Spaces.Dz f) z θ * Spaces.Dz f z θ * Weta z θ) Spaces.Iθ
    ∧ MeasureTheory.IntegrableOn (fun θ => Spaces.Dth (Spaces.Dz f) z θ * Spaces.Dz f z θ * Weta z θ) Spaces.Iθ
    ∧ MeasureTheory.IntegrableOn (fun θ => (Spaces.Dz f z θ) ^ 2 * Weta z θ) Spaces.Iθ
    ∧ MeasureTheory.IntegrableOn (fun θ => deriv (fun z' => z' * (Spaces.Dz f z' θ * Spaces.w z') ^ 2) z
        * (Real.sin (2 * θ)) ^ (-Spaces.eta)) Spaces.Iθ := by
  have hsin : MeasureTheory.IntegrableOn
      (fun θ : ℝ => (Real.sin (2 * θ)) ^ (-Spaces.eta)) Spaces.Iθ := sin_neg_eta_integrableOn
  have hDz : ContinuousOn (fun θ => Spaces.Dz f z θ) Spaces.Iθ :=
    continuousOn_slice_of_smoothNbhd (Spaces.SmoothNbhd.Dz hsm) hz
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- the `𝓛(D_z f) · D_z f · Weta` term
    have hDzDz : ContinuousOn (fun θ => Spaces.Dz (Spaces.Dz f) z θ) Spaces.Iθ :=
      continuousOn_slice_of_smoothNbhd (Spaces.SmoothNbhd.Dz (Spaces.SmoothNbhd.Dz hsm)) hz
    have hL : ContinuousOn (fun θ => L (Spaces.Dz f) z θ) Spaces.Iθ := by
      unfold L
      exact (hDz.add hDzDz).sub ((hDz.const_mul 2).div_const (1 + z))
    have hcont : ContinuousOn
        (fun θ => L (Spaces.Dz f) z θ * Spaces.Dz f z θ * Spaces.w z ^ 2) Spaces.Iθ :=
      (hL.mul hDz).mul continuousOn_const
    refine (IntegrableOn.continuousOn_mul hcont hsin isCompact_Icc).congr_fun
      (fun θ _ => ?_) measurableSet_Icc
    rw [Weta]; ring
  · -- the `D_θ(D_z f) · D_z f · Weta` term
    have hDthDz : ContinuousOn (fun θ => Spaces.Dth (Spaces.Dz f) z θ) Spaces.Iθ :=
      continuousOn_slice_of_smoothNbhd (Spaces.SmoothNbhd.Dth (Spaces.SmoothNbhd.Dz hsm)) hz
    have hcont : ContinuousOn
        (fun θ => Spaces.Dth (Spaces.Dz f) z θ * Spaces.Dz f z θ * Spaces.w z ^ 2) Spaces.Iθ :=
      (hDthDz.mul hDz).mul continuousOn_const
    refine (IntegrableOn.continuousOn_mul hcont hsin isCompact_Icc).congr_fun
      (fun θ _ => ?_) measurableSet_Icc
    rw [Weta]; ring
  · -- the coercive `(D_z f)² · Weta` term
    have hcont : ContinuousOn (fun θ => (Spaces.Dz f z θ) ^ 2 * Spaces.w z ^ 2) Spaces.Iθ :=
      (hDz.pow 2).mul continuousOn_const
    refine (IntegrableOn.continuousOn_mul hcont hsin isCompact_Icc).congr_fun
      (fun θ _ => ?_) measurableSet_Icc
    rw [Weta]; ring
  · -- the boundary term `∂_z(z (D_z f · w)²) · sin(2θ)^{-η}`
    exact IntegrableOn.continuousOn_mul (continuousOn_deriv_zw_Dz_sq f hsm hz) hsin isCompact_Icc

end Work.Coercivity
end
end
-- ===== merged: Submission.Work.Coercivity.thetaAux =====
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

/-- The angular weight `ρ = w(z)²·sin(2θ)^{-γ}`, `γ = gam α`, appearing in the target
`thetaDerivative` (it is the weight against which `D_θ f` is squared in `EDth`). -/
def thetaW (α : ℝ) (z θ : ℝ) : ℝ :=
  Spaces.w z ^ 2 * (Real.sin (2 * θ)) ^ (-(Spaces.gam α))

/-- `D_θΓ = sin(2θ) ∂_θΓ`, shown as a function of `z` (it does not depend on `z`). -/
def DthGam (α : ℝ) (z θ : ℝ) : ℝ :=
  Spaces.Dth (fun _ θ' => Spaces.Gam α θ') z θ


/-- The first `D_θΓ`-term of `D_θ(𝓛_Γ^T f)`:
`-D_θΓ · (2z/(c(1+z)²)) · L₁₂(f)`. -/
def T2 (α : ℝ) (f : ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ :=
  fun z θ => -(DthGam α z θ) * (2 * z / (Spaces.c α * (1 + z) ^ 2)) * L12f f z

/-- The projector `D_θΓ`-term of `D_θ(𝓛_Γ^T f)`:
`(D_θΓ/c) · (2z²/(1+z)³) · L₁₂(Transport f)(0)`. -/
def T4 (α : ℝ) (f : ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ :=
  fun z θ => (DthGam α z θ / Spaces.c α) * (2 * z ^ 2 / (1 + z) ^ 3) * C0 f



theorem DthGam_eq (α z θ : ℝ) :
    DthGam α z θ = Real.sin (2 * θ) * deriv (fun θ' => Spaces.Gam α θ') θ := rfl

end Work.Coercivity
end
end
-- ===== merged: Submission.Work.Coercivity.theta_integral_lower =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# Angular coercivity lower bound for the `H^k` integrand

This is the elementary "single term" lower bound used when the `H^k` norm is compared
with a pointwise lower bound for one weighted derivative.  The `H^k` integrand is a sum
of squares (`Work.Spaces.HkIntegrand`), the summand with `i = 0` in its first (pure `D_z`)
part being `(g z θ · w(z)/sin(2θ)^{η/2})²`.  On the interval `(θ₁,θ₂) ⊆ (0,π/2)` the
factor `1/sin(2θ)^{η/2}` is at least `1`, so a pointwise lower bound
`Aref²/16 · z² ≤ g(z,θ)²` propagates to a lower bound for the whole integral over `Iθ`.
-/

namespace Work.Coercivity

set_option autoImplicit false

theorem theta_integral_lower (α : ℝ) (n : ℕ) (g : ℝ → ℝ → ℝ) (z : ℝ) (hz : 0 < z)
    {θ₁ θ₂ Aref : ℝ} (hθ₁ : 0 ≤ θ₁) (hlt : θ₁ < θ₂) (hθ₂ : θ₂ ≤ Real.pi / 2)
    (hint : MeasureTheory.Integrable
      (fun θ => Work.Spaces.HkIntegrand α n g z θ)
        (MeasureTheory.volume.restrict Work.Spaces.Iθ))
    (hlow : ∀ θ ∈ Set.Ioo θ₁ θ₂, Aref ^ 2 / 16 * z ^ 2 ≤ (g z θ) ^ 2) :
    Aref ^ 2 * (θ₂ - θ₁) / 16 * ((Work.Spaces.w z) ^ 2 * z ^ 2)
      ≤ ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α n g z θ := by
  -- `(θ₁,θ₂) ⊆ Iθ`
  have hsub : Set.Ioo θ₁ θ₂ ⊆ Work.Spaces.Iθ := fun θ hθ =>
    ⟨le_of_lt (lt_of_le_of_lt hθ₁ hθ.1), le_trans (le_of_lt hθ.2) hθ₂⟩
  -- Pointwise lower bound for the full integrand on `(θ₁,θ₂)`.
  have hpt : ∀ θ ∈ Set.Ioo θ₁ θ₂,
      Aref ^ 2 / 16 * z ^ 2 * (Work.Spaces.w z) ^ 2
        ≤ Work.Spaces.HkIntegrand α n g z θ := by
    intro θ hθ
    -- `θ ∈ (0, π/2)`, so `0 < sin(2θ) ≤ 1`
    have hsinpos : 0 < Real.sin (2 * θ) :=
      Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1, hθ₁])
        (by linarith [hθ.2, hθ₂, Real.pi_pos])
    have hsinle : Real.sin (2 * θ) ≤ 1 := Real.sin_le_one _
    have heta : 0 ≤ Work.Spaces.eta / 2 := by
      have := Work.Spaces.eta_pos; linarith
    have hspos : 0 < Real.sin (2 * θ) ^ (Work.Spaces.eta / 2) := Real.rpow_pos_of_pos hsinpos _
    have hsle : Real.sin (2 * θ) ^ (Work.Spaces.eta / 2) ≤ 1 :=
      Real.rpow_le_one (le_of_lt hsinpos) hsinle heta
    -- `w(z) ≤ w(z)/sin(2θ)^{η/2}`, hence the same for the squares
    have hwz : 0 ≤ Work.Spaces.w z := div_nonneg (sq_nonneg _) (sq_nonneg _)
    have hdiv : Work.Spaces.w z ≤ Work.Spaces.w z / Real.sin (2 * θ) ^ (Work.Spaces.eta / 2) := by
      rw [div_eq_mul_one_div]
      calc Work.Spaces.w z = Work.Spaces.w z * 1 := by ring
        _ ≤ Work.Spaces.w z * (1 / Real.sin (2 * θ) ^ (Work.Spaces.eta / 2)) :=
            mul_le_mul_of_nonneg_left (one_le_one_div hspos hsle) hwz
    have hsq : (Work.Spaces.w z) ^ 2
        ≤ (Work.Spaces.w z / Real.sin (2 * θ) ^ (Work.Spaces.eta / 2)) ^ 2 :=
      pow_le_pow_left₀ hwz hdiv 2
    -- Multiply by the pointwise bound `Aref²/16 · z² ≤ g²`
    have h1 : Aref ^ 2 / 16 * z ^ 2 * (Work.Spaces.w z) ^ 2
        ≤ (g z θ) ^ 2 * (Work.Spaces.w z / Real.sin (2 * θ) ^ (Work.Spaces.eta / 2)) ^ 2 :=
      mul_le_mul (hlow θ hθ) hsq (sq_nonneg _) (sq_nonneg _)
    -- The `i = 0` summand of the `H^k` integrand is dominated by the whole sum
    have h3 : (g z θ * (Work.Spaces.w z / Real.sin (2 * θ) ^ (Work.Spaces.eta / 2))) ^ 2
        ≤ Work.Spaces.HkIntegrand α n g z θ := by
      have h4 := Work.Spaces.sq_le_HkIntegrand_z α n g z θ 0 (Nat.zero_le n)
      simpa using h4
    calc Aref ^ 2 / 16 * z ^ 2 * (Work.Spaces.w z) ^ 2
        ≤ (g z θ) ^ 2 * (Work.Spaces.w z / Real.sin (2 * θ) ^ (Work.Spaces.eta / 2)) ^ 2 := h1
      _ = (g z θ * (Work.Spaces.w z / Real.sin (2 * θ) ^ (Work.Spaces.eta / 2))) ^ 2 := by
            rw [mul_pow]
      _ ≤ Work.Spaces.HkIntegrand α n g z θ := h3
  have hIntOn : MeasureTheory.IntegrableOn
      (fun θ => Work.Spaces.HkIntegrand α n g z θ) Work.Spaces.Iθ := hint
  have hIntSub : MeasureTheory.IntegrableOn
      (fun θ => Work.Spaces.HkIntegrand α n g z θ) (Set.Ioo θ₁ θ₂) :=
    hIntOn.mono_set hsub
  -- The integral of the constant `Aref²/16 · z² · w(z)²` over `(θ₁,θ₂)`
  have hCint : ∫ θ in Set.Ioo θ₁ θ₂, Aref ^ 2 / 16 * z ^ 2 * (Work.Spaces.w z) ^ 2
      = Aref ^ 2 * (θ₂ - θ₁) / 16 * ((Work.Spaces.w z) ^ 2 * z ^ 2) := by
    rw [MeasureTheory.setIntegral_const, MeasureTheory.measureReal_def, Real.volume_Ioo,
      ENNReal.toReal_ofReal (by linarith), smul_eq_mul]
    ring
  have hIntC : MeasureTheory.IntegrableOn
      (fun _ : ℝ => Aref ^ 2 / 16 * z ^ 2 * (Work.Spaces.w z) ^ 2) (Set.Ioo θ₁ θ₂) :=
    MeasureTheory.integrableOn_const (by rw [Real.volume_Ioo]; exact ENNReal.ofReal_ne_top)
  have hmono1 : ∫ θ in Set.Ioo θ₁ θ₂, Aref ^ 2 / 16 * z ^ 2 * (Work.Spaces.w z) ^ 2
      ≤ ∫ θ in Set.Ioo θ₁ θ₂, Work.Spaces.HkIntegrand α n g z θ :=
    MeasureTheory.setIntegral_mono_on hIntC hIntSub measurableSet_Ioo hpt
  have hmono2 : ∫ θ in Set.Ioo θ₁ θ₂, Work.Spaces.HkIntegrand α n g z θ
      ≤ ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α n g z θ :=
    MeasureTheory.setIntegral_mono_set hIntOn
      (Filter.Eventually.of_forall (fun θ => Work.Spaces.HkIntegrand_nonneg α n g z θ))
      hsub.eventuallySubset
  calc Aref ^ 2 * (θ₂ - θ₁) / 16 * ((Work.Spaces.w z) ^ 2 * z ^ 2)
      = ∫ θ in Set.Ioo θ₁ θ₂, Aref ^ 2 / 16 * z ^ 2 * (Work.Spaces.w z) ^ 2 := hCint.symm
    _ ≤ ∫ θ in Set.Ioo θ₁ θ₂, Work.Spaces.HkIntegrand α n g z θ := hmono1
    _ ≤ ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α n g z θ := hmono2

end Work.Coercivity
end
-- ===== merged: Submission.Work.Coercivity.wip_G_bound =====
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

/-! ## Auxiliary lemmas

The estimate `|∫∫ 2 (Γ/c - K) f w (L₁₂f/z)| ≤ (7/5)√(Ef f)√(EL12z f)` is a single
Cauchy–Schwarz in the product space `Iz ×ˢ Iθ`, applied to the two functions
`(z,θ) ↦ g(θ)·ψ(z)` and `(z,θ) ↦ f(z,θ)w(z)`; the first one has a product structure,
so its `L²`-norm factorises as `‖g‖_{L²(dθ)}·‖ψ‖_{L²(dz)}` with **no** angular
factor.  Everything is organised through `∫⁻` (`ENNReal`) so that no junk values of
Bochner integrals enter.
-/

/-- `z ↦ L₁₂(f)(z)/z` is a.e. strongly measurable on `[0,∞)`: `L₁₂(f)` is continuous on
`(0,∞)` (`L12f_continuousOn`) and `Ioi 0`, `Ici 0` differ by the null set `{0}`. -/
private theorem aemeasurable_L12f_div (f : ℝ → ℝ → ℝ) (hfH : HardyHyp f) :
    AEMeasurable (fun z : ℝ => L12f f z / z) (volume.restrict Spaces.Iz) := by
  have hcont : ContinuousOn (fun z : ℝ => L12f f z / z) (Set.Ioi (0 : ℝ)) :=
    (L12f_continuousOn f hfH).div continuousOn_id (fun z hz => ne_of_gt hz)
  have h1 : AEStronglyMeasurable (fun z : ℝ => L12f f z / z)
      (volume.restrict (Set.Ioi (0 : ℝ))) :=
    hcont.aestronglyMeasurable measurableSet_Ioi
  have h2 : volume.restrict Spaces.Iz = volume.restrict (Set.Ioi (0 : ℝ)) := by
    rw [Spaces.Iz]
    exact (Measure.restrict_congr_set (Ioi_ae_eq_Ici (a := (0 : ℝ)))).symm
  rw [h2]
  exact h1.aemeasurable

/-- `(z,θ) ↦ ENNReal.ofReal ‖f(z,θ)w(z)‖` is a.e. measurable on the quadrant, from the
integrability of `(f w)²`: the latter makes `|f w| = √((f w)²)` a.e. measurable. -/
private theorem aemeasurable_ofReal_abs_mul_w (f : ℝ → ℝ → ℝ)
    (hf2 : MeasureTheory.IntegrableOn
      (Function.uncurry (fun z θ => f z θ * f z θ * Spaces.w z ^ 2))
      (Spaces.Iz ×ˢ Spaces.Iθ)) :
    AEMeasurable (fun p : ℝ × ℝ => ENNReal.ofReal |f p.1 p.2 * Spaces.w p.1|)
      ((volume.restrict Spaces.Iz).prod (volume.restrict Spaces.Iθ)) := by
  set P : Measure (ℝ × ℝ) := (volume.restrict Spaces.Iz).prod (volume.restrict Spaces.Iθ) with hP
  have hInt : Integrable (fun p : ℝ × ℝ => f p.1 p.2 * f p.1 p.2 * Spaces.w p.1 ^ 2) P := by
    rw [hP, Measure.prod_restrict]
    exact hf2
  have hInt2 : Integrable (fun p : ℝ × ℝ => (f p.1 p.2 * Spaces.w p.1) ^ 2) P :=
    hInt.congr (Eventually.of_forall fun p => by ring)
  have h2 : AEMeasurable (fun p : ℝ × ℝ => Real.sqrt ((f p.1 p.2 * Spaces.w p.1) ^ 2)) P :=
    hInt2.aestronglyMeasurable.aemeasurable.sqrt
  have h3 : AEMeasurable (fun p : ℝ × ℝ => |f p.1 p.2 * Spaces.w p.1|) P := by
    refine h2.congr ?_
    filter_upwards with p
    exact Real.sqrt_sq_eq_abs _
  exact ENNReal.measurable_ofReal.comp_aemeasurable h3

/-- **Tensor Cauchy–Schwarz.**  For `σ`-finite measures `μ` on `α` and `ν` on `β` and
measurable functions `Ge : β → ℝ≥0∞`, `Φf : α × β → ℝ≥0∞`, `Ψf : α → ℝ≥0∞` (with `Ψf`
and `∫⁻Ge²` finite),

`∫∫ Ge(θ) Φf(z,θ) Ψf(z) ≤ (∫Ge²)^{1/2} · (∫∫Φf²)^{1/2} · (∫Ψf²)^{1/2}`.

Note there is **no** angular factor: because `Ge(θ)Ψf(z)` is a product of a function of
`θ` alone and a function of `z` alone, Hölder in the product measure factorises. -/
private theorem tensor_holder_ennreal {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {μ : MeasureTheory.Measure α} {ν : MeasureTheory.Measure β}
    [MeasureTheory.SFinite μ] [MeasureTheory.SFinite ν]
    (Ge : β → ENNReal) (Φf : α × β → ENNReal) (Ψf : α → ENNReal)
    (hΨfin : ∀ z, Ψf z ≠ ⊤) (hGeA : (∫⁻ θ, Ge θ ^ 2 ∂ν) ≠ ⊤)
    (hGe : AEMeasurable Ge ν) (hΦ : AEMeasurable Φf (μ.prod ν)) (hΨ : AEMeasurable Ψf μ) :
    ∫⁻ p, Ge p.2 * Φf p * Ψf p.1 ∂(μ.prod ν)
      ≤ (∫⁻ θ, Ge θ ^ 2 ∂ν) ^ ((1 : ℝ) / 2) * (∫⁻ p, Φf p ^ 2 ∂(μ.prod ν)) ^ ((1 : ℝ) / 2)
        * (∫⁻ z, Ψf z ^ 2 ∂μ) ^ ((1 : ℝ) / 2) := by
  have hpq : (2 : ℝ).HolderConjugate 2 :=
    Real.holderConjugate_iff.mpr ⟨by norm_num, by norm_num⟩
  have hm : AEMeasurable (fun p : α × β => Ge p.2 * Ψf p.1) (μ.prod ν) :=
    (AEMeasurable.comp_snd hGe).mul (AEMeasurable.comp_fst hΨ)
  -- Hölder in the product measure
  have hholder := ENNReal.lintegral_mul_le_Lp_mul_Lq (μ.prod ν) hpq hm hΦ
  set A : ENNReal := ∫⁻ θ, Ge θ ^ 2 ∂ν with hA
  set B : ENNReal := ∫⁻ z, Ψf z ^ 2 ∂μ with hB
  set C : ENNReal := ∫⁻ p, Φf p ^ 2 ∂(μ.prod ν) with hC
  -- the squares
  have hsq : ∀ p : α × β, (Ge p.2 * Ψf p.1) ^ (2 : ℝ) = Ge p.2 ^ 2 * Ψf p.1 ^ 2 := by
    intro p
    rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, ENNReal.rpow_natCast, mul_pow]
  have hCeq : (∫⁻ p, Φf p ^ (2 : ℝ) ∂(μ.prod ν)) = C := by
    rw [hC]
    exact lintegral_congr fun p => by
      rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, ENNReal.rpow_natCast]
  -- `∫ (Ge∘snd · Ψ∘fst)² = A * B`
  have hAB : (∫⁻ p, (Ge p.2 * Ψf p.1) ^ (2 : ℝ) ∂(μ.prod ν)) = A * B := by
    rw [lintegral_congr hsq]
    have hm2 : AEMeasurable (fun p : α × β => Ge p.2 ^ 2 * Ψf p.1 ^ 2) (μ.prod ν) :=
      ((AEMeasurable.comp_snd hGe).pow_const 2).mul ((AEMeasurable.comp_fst hΨ).pow_const 2)
    rw [MeasureTheory.lintegral_prod _ hm2]
    have hinner : ∀ z : α, ∫⁻ θ, Ge θ ^ 2 * Ψf z ^ 2 ∂ν = A * Ψf z ^ 2 := by
      intro z
      rw [MeasureTheory.lintegral_mul_const' (Ψf z ^ 2) (fun θ => Ge θ ^ 2) ?_, hA]
      rw [pow_two]
      exact ENNReal.mul_ne_top (hΨfin z) (hΨfin z)
    rw [lintegral_congr hinner, hB]
    exact MeasureTheory.lintegral_const_mul' A (fun z => Ψf z ^ 2) hGeA
  rw [hAB] at hholder
  have hholder' : (∫⁻ p, (Ge p.2 * Ψf p.1) * Φf p ∂(μ.prod ν))
      ≤ (A * B) ^ ((1 : ℝ) / 2) * C ^ ((1 : ℝ) / 2) := by
    rw [← hCeq]
    exact hholder
  calc ∫⁻ p, Ge p.2 * Φf p * Ψf p.1 ∂(μ.prod ν)
      = ∫⁻ p, (Ge p.2 * Ψf p.1) * Φf p ∂(μ.prod ν) := by
        refine lintegral_congr fun p => ?_
        ac_rfl
    _ ≤ (A * B) ^ ((1 : ℝ) / 2) * C ^ ((1 : ℝ) / 2) := hholder'
    _ = (A ^ ((1 : ℝ) / 2) * B ^ ((1 : ℝ) / 2)) * C ^ ((1 : ℝ) / 2) := by
        rw [ENNReal.mul_rpow_of_nonneg A B (by norm_num)]
    _ = A ^ ((1 : ℝ) / 2) * C ^ ((1 : ℝ) / 2) * B ^ ((1 : ℝ) / 2) := by
        ac_rfl

/-- The `∫⁻`-version of `EL12z f`: `∫⁻ (ofReal ‖L₁₂(f)(z)/z‖)² = ofReal (EL12z f)`,
using the integrability of `(L₁₂ f)²/z²` supplied by `HardyHyp.intA` at `j = 1`. -/
private theorem lintegral_ofReal_L12z_sq (f : ℝ → ℝ → ℝ) (hfH : HardyHyp f) :
    (∫⁻ z, (ENNReal.ofReal |L12f f z / z|) ^ 2
        ∂(volume.restrict Spaces.Iz)) = ENNReal.ofReal (EL12z f) := by
  -- integrability of `(L₁₂(f)(z)/z)²` on `(0,∞)`, from `HardyHyp.intA 1`
  have hIoi : IntegrableOn (fun z : ℝ => (L12f f z / z) ^ 2) (Set.Ioi (0 : ℝ)) := by
    refine IntegrableOn.congr_fun (hfH.intA 1 (by norm_num)) (fun z hz => ?_) measurableSet_Ioi
    rw [div_pow]
    congr 1
    norm_num
  have hIz : Integrable (fun z : ℝ => (L12f f z / z) ^ 2) (volume.restrict Spaces.Iz) := by
    rw [Spaces.Iz, ← Measure.restrict_congr_set (Ioi_ae_eq_Ici (a := (0 : ℝ)))]
    exact hIoi
  have hpt : ∀ z : ℝ, (ENNReal.ofReal |L12f f z / z|) ^ 2
      = ENNReal.ofReal ((L12f f z / z) ^ 2) := by
    intro z
    rw [← ENNReal.ofReal_pow (abs_nonneg _), sq_abs]
  rw [lintegral_congr hpt]
  rw [← MeasureTheory.ofReal_integral_eq_lintegral_ofReal hIz
        (Eventually.of_forall fun z => sq_nonneg _)]
  congr 1

/-- The `∫⁻`-version of `Ef f`: `∫⁻ (ofReal ‖f w‖)² = ofReal (Ef f)`, using the joint
integrability of `(f w)²` together with Tonelli/Fubini. -/
private theorem lintegral_ofReal_fw_sq (f : ℝ → ℝ → ℝ)
    (hf2 : MeasureTheory.IntegrableOn
      (Function.uncurry (fun z θ => f z θ * f z θ * Spaces.w z ^ 2))
      (Spaces.Iz ×ˢ Spaces.Iθ)) :
    (∫⁻ p : ℝ × ℝ, (ENNReal.ofReal |f p.1 p.2 * Spaces.w p.1|) ^ 2
        ∂((volume.restrict Spaces.Iz).prod (volume.restrict Spaces.Iθ)))
      = ENNReal.ofReal (Ef f) := by
  set P : Measure (ℝ × ℝ) := (volume.restrict Spaces.Iz).prod (volume.restrict Spaces.Iθ) with hP
  have hInt : Integrable (fun p : ℝ × ℝ => (f p.1 p.2 * Spaces.w p.1) ^ 2) P := by
    have h0 : Integrable (fun p : ℝ × ℝ => f p.1 p.2 * f p.1 p.2 * Spaces.w p.1 ^ 2) P := by
      rw [hP, Measure.prod_restrict]
      exact hf2
    exact h0.congr (Eventually.of_forall fun p => by ring)
  have hpt : ∀ p : ℝ × ℝ, (ENNReal.ofReal |f p.1 p.2 * Spaces.w p.1|) ^ 2
      = ENNReal.ofReal ((f p.1 p.2 * Spaces.w p.1) ^ 2) := by
    intro p
    rw [← ENNReal.ofReal_pow (abs_nonneg _), sq_abs]
  rw [lintegral_congr hpt]
  rw [← MeasureTheory.ofReal_integral_eq_lintegral_ofReal hInt
        (Eventually.of_forall fun p => sq_nonneg _)]
  congr 1
  rw [hP, MeasureTheory.integral_prod _ hInt]
  simp only [Ef, Spaces.L2Sq]

/-- The angular part: `∫⁻ (ofReal ‖g θ‖)² = ofReal (∫ g²)`, from the integrability of
`g²` on the angular interval. -/
private theorem lintegral_ofReal_sq_Iθ (g : ℝ → ℝ)
    (hB : MeasureTheory.IntegrableOn (fun θ : ℝ => g θ ^ 2) Spaces.Iθ) :
    (∫⁻ θ, (ENNReal.ofReal |g θ|) ^ 2 ∂(volume.restrict Spaces.Iθ))
      = ENNReal.ofReal (∫ θ in Spaces.Iθ, g θ ^ 2) := by
  have hpt : ∀ θ : ℝ, (ENNReal.ofReal |g θ|) ^ 2 = ENNReal.ofReal (g θ ^ 2) := by
    intro θ
    rw [← ENNReal.ofReal_pow (abs_nonneg _), sq_abs]
  rw [lintegral_congr hpt]
  exact (MeasureTheory.ofReal_integral_eq_lintegral_ofReal hB
    (Eventually.of_forall fun θ => sq_nonneg _)).symm

/-! ## The main estimate -/

theorem wip_G_bound (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) (f : ℝ → ℝ → ℝ)
    (hfH : HardyHyp f)
    (hf2 : MeasureTheory.IntegrableOn
      (Function.uncurry (fun z θ => f z θ * f z θ * Spaces.w z ^ 2))
      (Spaces.Iz ×ˢ Spaces.Iθ))
    (hΓ : GammaL2Bnd α)
    (hB : MeasureTheory.IntegrableOn
      (fun θ : ℝ => (Spaces.Gam α θ / Spaces.c α - Spaces.K θ) ^ 2) Spaces.Iθ)
    (hint : MeasureTheory.IntegrableOn
      (Function.uncurry (fun z θ =>
        2 * (Spaces.Gam α θ / Spaces.c α - Spaces.K θ) * f z θ * Spaces.w z * (L12f f z / z)))
      (Spaces.Iz ×ˢ Spaces.Iθ)) :
    |∫ p : ℝ × ℝ, 2 * (Spaces.Gam α p.2 / Spaces.c α - Spaces.K p.2) * f p.1 p.2 * Spaces.w p.1
        * (L12f f p.1 / p.1)
        ∂((MeasureTheory.volume.restrict Spaces.Iz).prod (MeasureTheory.volume.restrict Spaces.Iθ))|
      ≤ (7 / 5) * Real.sqrt (Ef f) * Real.sqrt (EL12z f) := by
  set P : Measure (ℝ × ℝ) := (volume.restrict Spaces.Iz).prod (volume.restrict Spaces.Iθ) with hP
  set g : ℝ → ℝ := fun θ => Spaces.Gam α θ / Spaces.c α - Spaces.K θ with hg
  set ψ : ℝ → ℝ := fun z => L12f f z / z with hψ
  set G : ℝ × ℝ → ℝ := fun p => (2 * g p.2) * (f p.1 p.2 * Spaces.w p.1) * ψ p.1 with hG
  -- the integrand of the statement, regrouped
  have hGeq : (fun p : ℝ × ℝ => 2 * (Spaces.Gam α p.2 / Spaces.c α - Spaces.K p.2) * f p.1 p.2
      * Spaces.w p.1 * (L12f f p.1 / p.1)) = G := by
    funext p
    simp only [hG, hg, hψ]
    ring
  -- integrability of `g²` and a.e. measurability of `|g|`
  have hB_g : MeasureTheory.IntegrableOn (fun θ : ℝ => g θ ^ 2) Spaces.Iθ := by
    rw [hg]; exact hB
  have hgmeas : AEMeasurable (fun θ : ℝ => |g θ|) (volume.restrict Spaces.Iθ) := by
    have h2 : AEMeasurable (fun θ : ℝ => Real.sqrt (g θ ^ 2)) (volume.restrict Spaces.Iθ) :=
      (hB_g.aestronglyMeasurable.aemeasurable).sqrt
    refine h2.congr ?_
    filter_upwards with θ
    exact Real.sqrt_sq_eq_abs _
  -- joint integrability of `G`
  have hGint : Integrable G P := by
    have h : Integrable (Function.uncurry (fun z θ =>
        2 * (Spaces.Gam α θ / Spaces.c α - Spaces.K θ) * f z θ * Spaces.w z * (L12f f z / z)))
        ((volume.restrict Spaces.Iz).prod (volume.restrict Spaces.Iθ)) := by
      rw [Measure.prod_restrict]
      exact hint
    rw [hP]
    refine h.congr (Eventually.of_forall fun p => ?_)
    simp only [Function.uncurry, hG, hg, hψ]
    ring
  -- the `ENNReal` integrands
  set Ge : ℝ → ENNReal := fun θ => ENNReal.ofReal |g θ| with hGeD
  set Phi : ℝ × ℝ → ENNReal := fun p => ENNReal.ofReal |f p.1 p.2 * Spaces.w p.1| with hPhiD
  set Psi : ℝ → ENNReal := fun z => ENNReal.ofReal |ψ z| with hPsiD
  have hPsi_aem : AEMeasurable Psi (volume.restrict Spaces.Iz) := by
    have h1 : AEMeasurable (fun z : ℝ => |ψ z|) (volume.restrict Spaces.Iz) := by
      rw [hψ]
      simpa only [Real.norm_eq_abs] using (aemeasurable_L12f_div f hfH).norm
    rw [hPsiD]
    exact ENNReal.measurable_ofReal.comp_aemeasurable h1
  have hPhi_aem : AEMeasurable Phi P := by
    rw [hPhiD, hP]
    exact aemeasurable_ofReal_abs_mul_w f hf2
  have hGe_aem : AEMeasurable Ge (volume.restrict Spaces.Iθ) := by
    rw [hGeD]
    exact ENNReal.measurable_ofReal.comp_aemeasurable hgmeas
  -- values of the three `∫⁻`
  have hAval : (∫⁻ θ, Ge θ ^ 2 ∂(volume.restrict Spaces.Iθ))
      = ENNReal.ofReal (∫ θ in Spaces.Iθ, g θ ^ 2) := by
    rw [hGeD]
    exact lintegral_ofReal_sq_Iθ g hB_g
  have hBval : (∫⁻ z, Psi z ^ 2 ∂(volume.restrict Spaces.Iz)) = ENNReal.ofReal (EL12z f) := by
    rw [hPsiD]
    exact lintegral_ofReal_L12z_sq f hfH
  have hCval : (∫⁻ p : ℝ × ℝ, Phi p ^ 2 ∂P) = ENNReal.ofReal (Ef f) := by
    rw [hP, hPhiD]
    exact lintegral_ofReal_fw_sq f hf2
  have hGeA : (∫⁻ θ, Ge θ ^ 2 ∂(volume.restrict Spaces.Iθ)) ≠ ⊤ := by
    rw [hAval]; exact ENNReal.ofReal_ne_top
  have hPsinf : ∀ z : ℝ, Psi z ≠ ⊤ := fun z => by rw [hPsiD]; exact ENNReal.ofReal_ne_top
  -- tensor Cauchy–Schwarz
  have hHolder := tensor_holder_ennreal (μ := volume.restrict Spaces.Iz)
    (ν := volume.restrict Spaces.Iθ) Ge Phi Psi hPsinf hGeA hGe_aem hPhi_aem hPsi_aem
  -- the pointwise identity of the `ℝ≥0∞` integrand
  have hptG : ∀ p : ℝ × ℝ, ENNReal.ofReal |G p| = 2 * Ge p.2 * Phi p * Psi p.1 := by
    intro p
    rw [hG, hGeD, hPhiD, hPsiD]
    rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
    rw [ENNReal.ofReal_mul
          (by positivity : (0 : ℝ) ≤ (2 * |g p.2|) * |f p.1 p.2 * Spaces.w p.1|),
        ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ 2 * |g p.2|),
        ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)]
    norm_num
  have hENN : ∫⁻ p, ENNReal.ofReal |G p| ∂P
      ≤ 2 * ((∫⁻ θ, Ge θ ^ 2 ∂(volume.restrict Spaces.Iθ)) ^ ((1 : ℝ) / 2)
          * (∫⁻ p, Phi p ^ 2 ∂P) ^ ((1 : ℝ) / 2)
          * (∫⁻ z, Psi z ^ 2 ∂(volume.restrict Spaces.Iz)) ^ ((1 : ℝ) / 2)) := by
    have h1 : (∫⁻ p, ENNReal.ofReal |G p| ∂P)
        = 2 * ∫⁻ p, Ge p.2 * Phi p * Psi p.1 ∂P := by
      rw [lintegral_congr hptG]
      rw [show (fun p : ℝ × ℝ => 2 * Ge p.2 * Phi p * Psi p.1)
          = fun p => 2 * (Ge p.2 * Phi p * Psi p.1) from by funext p; ac_rfl]
      rw [MeasureTheory.lintegral_const_mul' 2 _ (by norm_num)]
    rw [h1]
    exact mul_le_mul_of_nonneg_left hHolder (by norm_num)
  -- the same bound, with the three integrals evaluated
  have hENN' : ∫⁻ p, ENNReal.ofReal |G p| ∂P
      ≤ 2 * (ENNReal.ofReal (Real.sqrt (∫ θ in Spaces.Iθ, g θ ^ 2))
              * ENNReal.ofReal (Real.sqrt (Ef f))
              * ENNReal.ofReal (Real.sqrt (EL12z f))) := by
    refine hENN.trans (le_of_eq ?_)
    have ha0 : 0 ≤ ∫ θ in Spaces.Iθ, g θ ^ 2 := integral_nonneg fun θ => sq_nonneg _
    have hc0 : 0 ≤ Ef f := by
      rw [Ef, Spaces.L2Sq]
      exact integral_nonneg fun z => integral_nonneg fun θ => sq_nonneg _
    have hb0 : 0 ≤ EL12z f := by
      rw [EL12z, L2Sqz]
      exact integral_nonneg fun z => sq_nonneg _
    rw [hAval, hCval, hBval]
    rw [ENNReal.ofReal_rpow_of_nonneg ha0 (by norm_num : (0 : ℝ) ≤ 1 / 2),
        ENNReal.ofReal_rpow_of_nonneg hc0 (by norm_num : (0 : ℝ) ≤ 1 / 2),
        ENNReal.ofReal_rpow_of_nonneg hb0 (by norm_num : (0 : ℝ) ≤ 1 / 2)]
    rw [← Real.sqrt_eq_rpow (∫ θ in Spaces.Iθ, g θ ^ 2),
        ← Real.sqrt_eq_rpow (Ef f), ← Real.sqrt_eq_rpow (EL12z f)]
  -- the non-finiteness needed for `toReal_mono`
  have hne_top : 2 * (ENNReal.ofReal (Real.sqrt (∫ θ in Spaces.Iθ, g θ ^ 2))
              * ENNReal.ofReal (Real.sqrt (Ef f))
              * ENNReal.ofReal (Real.sqrt (EL12z f))) ≠ ⊤ :=
    ENNReal.mul_ne_top (by norm_num)
      (ENNReal.mul_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top)
        ENNReal.ofReal_ne_top)
  -- the value of the LHS integral
  have hAbs : |∫ p, G p ∂P| ≤ (∫⁻ p, ENNReal.ofReal |G p| ∂P).toReal := by
    have h1 : |∫ p, G p ∂P| ≤ ∫ p, |G p| ∂P := abs_integral_le_integral_abs
    have h2 : (∫⁻ p, ENNReal.ofReal |G p| ∂P).toReal = ∫ p, |G p| ∂P := by
      rw [← MeasureTheory.ofReal_integral_eq_lintegral_ofReal hGint.abs
            (Eventually.of_forall fun p => abs_nonneg _)]
      exact ENNReal.toReal_ofReal (integral_nonneg fun p => abs_nonneg _)
    linarith
  -- the integral of the statement is that of `G`
  have hIntEq : (∫ p : ℝ × ℝ, 2 * (Spaces.Gam α p.2 / Spaces.c α - Spaces.K p.2) * f p.1 p.2
        * Spaces.w p.1 * (L12f f p.1 / p.1) ∂P) = ∫ p, G p ∂P :=
    integral_congr_ae (Eventually.of_forall (congrFun hGeq))
  -- the numerical conclusion
  have hsqrt : Real.sqrt (∫ θ in Spaces.Iθ, g θ ^ 2) ≤ 7 / 10 := by
    have hΓ' : ∫ θ in Spaces.Iθ, g θ ^ 2 ≤ ((7 : ℝ) / 10) ^ 2 := by
      rw [hg]; exact hΓ
    calc Real.sqrt (∫ θ in Spaces.Iθ, g θ ^ 2) ≤ Real.sqrt (((7 : ℝ) / 10) ^ 2) :=
          Real.sqrt_le_sqrt hΓ'
      _ = 7 / 10 := Real.sqrt_sq (by norm_num)
  have hEfnn : 0 ≤ Real.sqrt (Ef f) := Real.sqrt_nonneg _
  have hELnn : 0 ≤ Real.sqrt (EL12z f) := Real.sqrt_nonneg _
  calc |∫ p : ℝ × ℝ, 2 * (Spaces.Gam α p.2 / Spaces.c α - Spaces.K p.2) * f p.1 p.2
        * Spaces.w p.1 * (L12f f p.1 / p.1) ∂P|
      = |∫ p, G p ∂P| := by rw [hIntEq]
    _ ≤ (∫⁻ p, ENNReal.ofReal |G p| ∂P).toReal := hAbs
    _ ≤ (2 * (ENNReal.ofReal (Real.sqrt (∫ θ in Spaces.Iθ, g θ ^ 2))
              * ENNReal.ofReal (Real.sqrt (Ef f))
              * ENNReal.ofReal (Real.sqrt (EL12z f)))).toReal :=
          ENNReal.toReal_mono hne_top hENN'
    _ = 2 * Real.sqrt (∫ θ in Spaces.Iθ, g θ ^ 2) * Real.sqrt (Ef f)
          * Real.sqrt (EL12z f) := by
        rw [ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_mul,
            ENNReal.toReal_ofReal (Real.sqrt_nonneg _),
            ENNReal.toReal_ofReal (Real.sqrt_nonneg _),
            ENNReal.toReal_ofReal (Real.sqrt_nonneg _),
            show ENNReal.toReal (2 : ENNReal) = 2 by norm_num]
        ring
    _ ≤ (7 / 5) * Real.sqrt (Ef f) * Real.sqrt (EL12z f) := by
        have h1 : 2 * Real.sqrt (∫ θ in Spaces.Iθ, g θ ^ 2) ≤ 2 * (7 / 10) := by linarith
        have h2 : 2 * Real.sqrt (∫ θ in Spaces.Iθ, g θ ^ 2) * Real.sqrt (Ef f)
            ≤ 2 * (7 / 10) * Real.sqrt (Ef f) :=
          mul_le_mul_of_nonneg_right h1 hEfnn
        have h3 : 2 * Real.sqrt (∫ θ in Spaces.Iθ, g θ ^ 2) * Real.sqrt (Ef f)
              * Real.sqrt (EL12z f)
            ≤ 2 * (7 / 10) * Real.sqrt (Ef f) * Real.sqrt (EL12z f) :=
          mul_le_mul_of_nonneg_right h2 hELnn
        linarith

end Work.Coercivity
end
end
-- ===== merged: Submission.Work.Construction.Ansatz =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.Construction

set_option autoImplicit false


end Work.Construction
end
end
-- ===== merged: Submission.Work.Construction.Equation =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.Construction

set_option autoImplicit false

/-! ## Unfolding the projector and the transport term -/

theorem LGammaT_eq (α : ℝ) (f : ℝ → ℝ → ℝ) (z θ : ℝ) :
    Work.Coercivity.LGammaT α f z θ
      = Work.Coercivity.LGamma α f z θ - Work.Coercivity.Transport f z θ
        + AK α z θ * L12 (Work.Coercivity.Transport f) 0 := by
  rw [Work.Coercivity.LGammaT, Work.Coercivity.Proj, Work.Coercivity.Transport]
  simp only [AK, Work.Coercivity.L12f, L12]
  ring

theorem Transport_eq (f : ℝ → ℝ → ℝ) (z θ : ℝ) :
    Work.Coercivity.Transport f z θ
      = 3 * s2 θ * Work.Spaces.pth f z θ / (1 + z) := by
  rw [Work.Coercivity.Transport, Work.Spaces.Dth, s2]
  ring

/-! ## The substitution `Φ = Φ̃ + Θ` (tex 1338-1344) -/

/-- **The substitution lemma** (tex 1338-1344): writing `Φ = Φ̃ + Θ` with
`Θ = (1/(4α)) sin(2θ) L₁₂(F)` and using the two evaluations
`U(Θ) = -3Θ + (1/4) sin(2θ)(F,K)`, `V(Θ) = (1/(2α))c2m(θ)L₁₂(F)`,
`ℛ(Θ) = (1/(2α))L₁₂(F) - (1/2)sin²θ (F,K)` (the paper's `U, V, ℛ` evaluations, with
`z∂_z L₁₂(F) = -(F,K)` and `∂_θ Θ = (1/(2α))cos(2θ)L₁₂(F)`), the quadratic form splits as
`UVR(F,Φ) = UVR(F,Φ̃) - (1/α)L₁₂(F)F - (3/(2α))sin2θ L₁₂(F)∂_θF + c2m(θ)L₁₂(F)D_zF
   + (1/2)sin2θ (F,K)∂_θF + sin²θ (F,K)F`.

The last two terms are the two angular-moment terms of `N` (tex `\eqref{N}`); the paper
displays them with coefficients `-α` and `-2α`, which differ from the exact `-1/2` and `-1`
by the factor `2α`. -/
theorem UVR_sub (α : ℝ) (hα : 0 < α) {F Φ Φt Θ : ℝ → ℝ → ℝ} (z θ : ℝ)
    (hcos : Real.cos θ ≠ 0)
    (h1 : Φ z θ = Φt z θ + Θ z θ)
    (h2 : Work.Spaces.pz Φ z θ = Work.Spaces.pz Φt z θ + Work.Spaces.pz Θ z θ)
    (h3 : Work.Spaces.pth Φ z θ = Work.Spaces.pth Φt z θ + Work.Spaces.pth Θ z θ)
    (h4 : Θ z θ = (1 / (4 * α)) * s2 θ * L12 F z)
    (h5 : z * Work.Spaces.pz Θ z θ = -(1 / (4 * α)) * s2 θ * FK F z)
    (h6 : Work.Spaces.pth Θ z θ = (1 / (2 * α)) * Real.cos (2 * θ) * L12 F z) :
    UVR α F Φ z θ = UVR α F Φt z θ - (1 / α) * L12 F z * F z θ
      - (3 / (2 * α)) * s2 θ * L12 F z * Work.Spaces.pth F z θ
      + c2m θ * L12 F z * Work.Spaces.Dz F z θ
      + (1 / 2) * s2 θ * FK F z * Work.Spaces.pth F z θ
      + Real.sin θ ^ 2 * FK F z * F z θ := by
  have hz' : α * z * Work.Spaces.pz Θ z θ = α * (z * Work.Spaces.pz Θ z θ) := by ring
  have hs' : α * Real.sin θ * z * Work.Spaces.pz Θ z θ
      = α * Real.sin θ * (z * Work.Spaces.pz Θ z θ) := by ring
  have hsincos : Real.sin θ ^ 2 = 1 - Real.cos θ ^ 2 := by
    have := Real.sin_sq_add_cos_sq θ; linarith
  have key : UVR α F Φ z θ = UVR α F Φt z θ + UVR α F Θ z θ := by
    simp only [UVR, Uop, Vop, Rop]
    rw [h1, h2, h3]
    ring
  have key2 : UVR α F Θ z θ
      = -(1 / α) * L12 F z * F z θ
        - (3 / (2 * α)) * s2 θ * L12 F z * Work.Spaces.pth F z θ
        + c2m θ * L12 F z * Work.Spaces.Dz F z θ
        + (1 / 2) * s2 θ * FK F z * Work.Spaces.pth F z θ
        + Real.sin θ ^ 2 * FK F z * F z θ := by
    simp only [UVR, Uop, Vop, Rop]
    rw [hz', hs', h5, h6, h4]
    rw [s2, c2m, Real.sin_two_mul, Real.cos_two_mul, Real.tan_eq_sin_div_cos]
    field_simp
    rw [hsincos]
    ring
  rw [key, key2]
  ring

/-! ## The expansion of the left hand side of tex 1345 -/

theorem MainLHS_explicit {α μ lam : ℝ} (hα : 0 < α) {F g : ℝ → ℝ → ℝ} (z θ : ℝ)
    (hz : (1 : ℝ) + z ≠ 0)
    (hF : F z θ = Fstar α z θ + g z θ)
    (hDz : Work.Spaces.Dz F z θ
      = Work.Spaces.Dz (Fstar α) z θ + Work.Spaces.Dz g z θ)
    (hpth : Work.Spaces.pth F z θ
      = Work.Spaces.pth (Fstar α) z θ + Work.Spaces.pth g z θ)
    (hL : L12 F z = L12 (Fstar α) z + L12 g z)
    (hLstar : L12 (Fstar α) z = 2 * α / (1 + z))
    (hstat : Fstar α z θ + Work.Spaces.Dz (Fstar α) z θ
      - (1 / α) * L12 (Fstar α) z * Fstar α z θ = 0) :
    MainLHS α μ lam F z θ
      = μ * Fstar α z θ + (μ + lam + μ * lam) * Work.Spaces.Dz (Fstar α) z θ
        + Work.Coercivity.LGamma α g z θ
        - (3 / (2 * α)) * s2 θ * L12 (Fstar α) z * Work.Spaces.pth g z θ
        + μ * g z θ + (μ + lam + μ * lam) * Work.Spaces.Dz g z θ
        - N0 α F g z θ := by
  have key : MainLHS α μ lam F z θ
      - (μ * Fstar α z θ + (μ + lam + μ * lam) * Work.Spaces.Dz (Fstar α) z θ
        + Work.Coercivity.LGamma α g z θ
        - (3 / (2 * α)) * s2 θ * L12 (Fstar α) z * Work.Spaces.pth g z θ
        + μ * g z θ + (μ + lam + μ * lam) * Work.Spaces.Dz g z θ
        - N0 α F g z θ)
      = Fstar α z θ + Work.Spaces.Dz (Fstar α) z θ
        - (1 / α) * L12 (Fstar α) z * Fstar α z θ := by
    rw [MainLHS, N0, Work.Coercivity.LGamma, Work.Coercivity.L]
    rw [show Work.Coercivity.L12f g z = L12 g z from rfl]
    rw [hF, hDz, hpth, hL, hLstar, Fstar, Work.FM.Fstar]
    field_simp
    ring_nf
  linarith [key, hstat]

/-! ## `MainLHS(F,Φ) = N(F,Φ)` (tex 1345) -/


/-! ## The intermediate equation (tex 1349) -/


/-! ## The `g`-equation `\eqref{gEquationFinal}` -/


end Work.Construction
end
end
-- ===== merged: Submission.Work.Construction.GammaN0 =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.Construction

set_option autoImplicit false

/-- `3 sin(2θ) ∂_θΓ = 2αΓ(cos²θ - 2sin²θ)` for `θ ∈ [0,π/2]`: the differentiated form of
`Γ = (sinθcos²θ)^{α/3}` (paper line 1400).  At the endpoints both sides vanish (as
`Γ(0) = Γ(π/2) = 0` and `sin(2θ) = 0`), so the closed interval causes no problem. -/
theorem Gamma_deriv_id {α θ : ℝ} (hα : 0 < α) (hθ : θ ∈ Work.Spaces.Iθ) :
    3 * s2 θ * deriv (fun t : ℝ => Work.Spaces.Gam α t) θ
      = 2 * α * Work.Spaces.Gam α θ * (Real.cos θ ^ 2 - 2 * Real.sin θ ^ 2) := by
  obtain ⟨hθ0, hθ1⟩ := hθ
  rcases lt_or_eq_of_le hθ0 with h0 | h0
  · rcases lt_or_eq_of_le hθ1 with h1 | h1
    · -- interior of the interval
      have hsin : 0 < Real.sin θ :=
        Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [Real.pi_pos])
      have hcos : 0 < Real.cos θ := Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], h1⟩
      have hu : 0 < Real.sin θ * Real.cos θ ^ 2 := by positivity
      have hsincos : Real.sin θ ^ 2 = 1 - Real.cos θ ^ 2 := by
        have := Real.sin_sq_add_cos_sq θ; linarith
      have hu' : HasDerivAt (fun t : ℝ => Real.sin t * Real.cos t ^ 2)
          (Real.cos θ * Real.cos θ ^ 2 + Real.sin θ * (2 * Real.cos θ ^ (2 - 1) * (-Real.sin θ))) θ :=
        (Real.hasDerivAt_sin θ).mul ((Real.hasDerivAt_cos θ).pow 2)
      have hGam : HasDerivAt (fun t : ℝ => Work.Spaces.Gam α t)
          ((Real.cos θ * Real.cos θ ^ 2 + Real.sin θ * (2 * Real.cos θ ^ (2 - 1) * (-Real.sin θ)))
            * (α / 3) * (Real.sin θ * Real.cos θ ^ 2) ^ (α / 3 - 1)) θ := by
        have h := hu'.rpow_const (p := α / 3) (Or.inl (ne_of_gt hu))
        simpa [Work.Spaces.Gam] using h
      have hpow : (Real.sin θ * Real.cos θ ^ 2) ^ (α / 3 - 1) * (Real.sin θ * Real.cos θ ^ 2)
          = (Real.sin θ * Real.cos θ ^ 2) ^ (α / 3) := by
        have h1 : (Real.sin θ * Real.cos θ ^ 2) ^ (α / 3 - 1)
              * (Real.sin θ * Real.cos θ ^ 2) ^ (1 : ℝ)
            = (Real.sin θ * Real.cos θ ^ 2) ^ (α / 3) := by
          rw [← Real.rpow_add hu, show α / 3 - 1 + 1 = α / 3 by ring]
        rwa [Real.rpow_one] at h1
      rw [hGam.deriv, s2, Real.sin_two_mul, Work.Spaces.Gam, ← hpow]
      ring_nf
      try nlinarith [Real.sin_sq_add_cos_sq θ]
    · -- θ = π/2
      subst h1
      have hL : s2 (Real.pi / 2) = 0 := by
        rw [s2, show 2 * (Real.pi / 2) = Real.pi by ring, Real.sin_pi]
      have hR : Work.Spaces.Gam α (Real.pi / 2) = 0 := by
        rw [Work.Spaces.Gam, Real.sin_pi_div_two, Real.cos_pi_div_two, one_mul]
        rw [show ((0 : ℝ) ^ 2) = 0 by norm_num]
        exact Real.zero_rpow (ne_of_gt (by positivity : (0 : ℝ) < α / 3))
      rw [hL, hR]
      ring
  · -- θ = 0
    subst h0
    have hL : s2 0 = 0 := by rw [s2, mul_zero, Real.sin_zero]
    have hR : Work.Spaces.Gam α 0 = 0 := by
      rw [Work.Spaces.Gam, Real.sin_zero, Real.cos_zero, one_pow, mul_one,
        Real.zero_rpow (ne_of_gt (by positivity : (0 : ℝ) < α / 3))]
    rw [hL, hR]
    ring

/-- The two `F_*`-quadratic terms of `\eqref{N0}` collapse (tex 1398-1402). -/
theorem N0_first_two_eq {α z θ : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) (hz : 0 ≤ z)
    (hθ : θ ∈ Work.Spaces.Iθ)
    (hΓ : 3 * s2 θ * deriv (fun t : ℝ => Work.Spaces.Gam α t) θ
      = 2 * α * Work.Spaces.Gam α θ * (Real.cos θ ^ 2 - 2 * Real.sin θ ^ 2)) :
    (3 / (2 * α)) * s2 θ * L12 (Fstar α) z * Work.Spaces.pth (Fstar α) z θ
      - c2m θ * L12 (Fstar α) z * Work.Spaces.Dz (Fstar α) z θ
      = 8 * α ^ 2 * c2m θ * z ^ 2 * Work.Spaces.Gam α θ
        / (Work.Spaces.c α * (1 + z) ^ 4) := by
  have hz' : (-1 : ℝ) < z := by linarith
  have h1z : (1 : ℝ) + z ≠ 0 := ne_of_gt (by linarith)
  have hc : Work.Spaces.c α ≠ 0 := by
    have h := (Work.Spaces.c_bounds α hα hα1).1
    intro h0; rw [h0] at h; norm_num at h
  have ha : α ≠ 0 := ne_of_gt hα
  have h1 : (3 / (2 * α)) * s2 θ * L12 (Fstar α) z * Work.Spaces.pth (Fstar α) z θ
      = (2 * α * z / (Work.Spaces.c α * (1 + z) ^ 3))
        * (3 * s2 θ * deriv (fun t : ℝ => Work.Spaces.Gam α t) θ) := by
    rw [pth_Fstar_eq hα, L12_Fstar_eq hα hα1 hz, Work.FM.Fstar]
    field_simp
    try ring
  have h2 : c2m θ * L12 (Fstar α) z * Work.Spaces.Dz (Fstar α) z θ
      = 4 * α ^ 2 * c2m θ * z * (1 - z) * Work.Spaces.Gam α θ
        / (Work.Spaces.c α * (1 + z) ^ 4) := by
    rw [Dz_Fstar_eq hα hz', L12_Fstar_eq hα hα1 hz]
    field_simp
    try ring
  rw [h1, h2, hΓ]
  rw [c2m, Real.cos_two_mul]
  field_simp
  linear_combination (norm := ring_nf)
    (-4 * z * Work.Spaces.Gam α θ * (1 + z)) * Real.sin_sq_add_cos_sq θ

/-- `N0_first_two_eq` with the Γ-derivative identity supplied by `Gamma_deriv_id`. -/
theorem N0_first_two_eq' {α z θ : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) (hz : 0 ≤ z)
    (hθ : θ ∈ Work.Spaces.Iθ) :
    (3 / (2 * α)) * s2 θ * L12 (Fstar α) z * Work.Spaces.pth (Fstar α) z θ
      - c2m θ * L12 (Fstar α) z * Work.Spaces.Dz (Fstar α) z θ
      = 8 * α ^ 2 * c2m θ * z ^ 2 * Work.Spaces.Gam α θ
        / (Work.Spaces.c α * (1 + z) ^ 4) :=
  N0_first_two_eq hα hα1 hz hθ (Gamma_deriv_id hα hθ)

end Work.Construction
end
end
-- ===== merged: Submission.Work.Construction.GammaTermAux =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.Construction

set_option autoImplicit false

/-! ## The separated shape of the term -/

/-- The radial factor `ρ(z) = z²/(1+z)⁴` of the `Γ`-term. -/
def rhoR (z : ℝ) : ℝ := z ^ 2 / (1 + z) ^ 4

/-- The angular factor `ψ(θ) = c2m(θ)·Γ(θ)` of the `Γ`-term. -/
def psiA (α : ℝ) (θ : ℝ) : ℝ := c2m θ * Work.Spaces.Gam α θ

/-- The `α`-dependent constant `8α²/c(α)` multiplying `ρ·ψ`. -/
def Kfac (α : ℝ) : ℝ := 8 * α ^ 2 / Work.Spaces.c α

/-- A separated function `(z,θ) ↦ a z · b θ`. -/
def sepF (a b : ℝ → ℝ) : ℝ → ℝ → ℝ := fun z θ => a z * b θ

/-! ## Separability of the iterated derivatives -/

theorem Zop_apply (u : ℝ → ℝ) (z : ℝ) :
    Work.Spaces.Zop u z = z * deriv u z := rfl

theorem Lop_apply (u : ℝ → ℝ) (θ : ℝ) :
    Work.Spaces.Lop u θ = Real.sin (2 * θ) * deriv u θ := rfl

theorem Zop_const_mul (c : ℝ) (u : ℝ → ℝ) :
    Work.Spaces.Zop (fun z => c * u z) = fun z => c * Work.Spaces.Zop u z := by
  funext z
  rw [Zop_apply, Zop_apply, deriv_const_mul_fun (a := c) (b := u) z]
  ring

theorem Zop_iter_const_mul (j : ℕ) (c : ℝ) (u : ℝ → ℝ) :
    Work.Spaces.Zop^[j] (fun z => c * u z) = fun z => c * (Work.Spaces.Zop^[j] u) z := by
  induction j with
  | zero => rfl
  | succ n ih =>
      rw [Function.iterate_succ_apply', ih, Zop_const_mul]
      funext z
      rw [Function.iterate_succ_apply']

theorem sepF_DzIter (i : ℕ) (a b : ℝ → ℝ) :
    Work.Spaces.DzIter i (sepF a b) = sepF (Work.Spaces.Zop^[i] a) b := by
  induction i with
  | zero => rfl
  | succ n ih =>
      rw [Work.Spaces.DzIter_succ, ih]
      funext z θ
      show z * deriv (fun z' => (Work.Spaces.Zop^[n] a) z' * b θ) z
          = (Work.Spaces.Zop^[n + 1] a) z * b θ
      rw [Function.iterate_succ_apply', Zop_apply,
          deriv_mul_const_fun (a := b θ) (b := Work.Spaces.Zop^[n] a) z]
      ring

theorem sepF_DthIter (i : ℕ) (a b : ℝ → ℝ) :
    Work.Spaces.DthIter i (sepF a b) = sepF a (Work.Spaces.Lop^[i] b) := by
  induction i with
  | zero => rfl
  | succ n ih =>
      rw [Work.Spaces.DthIter_succ, ih]
      funext z θ
      show Real.sin (2 * θ) * deriv (fun θ' => a z * (Work.Spaces.Lop^[n] b) θ') θ
          = a z * (Work.Spaces.Lop^[n + 1] b) θ
      rw [Function.iterate_succ_apply', Lop_apply,
          deriv_const_mul_fun (a := a z) (b := Work.Spaces.Lop^[n] b) θ]
      ring

theorem sepF_mixed (j i : ℕ) (a b : ℝ → ℝ) :
    Work.Spaces.mixed j i (sepF a b)
      = sepF (Work.Spaces.Zop^[j] a) (Work.Spaces.Lop^[i] b) := by
  rw [Work.Spaces.mixed, sepF_DthIter, sepF_DzIter]

/-! ## The angular coefficient `c2m` -/

/-- `c2m θ = (3cos(2θ) - 1)/2`: the form used for the angular derivatives. -/
theorem c2m_eq_half (θ : ℝ) : c2m θ = (3 * Real.cos (2 * θ) - 1) / 2 := by
  rw [c2m, Real.cos_two_mul]
  have h := Real.sin_sq_add_cos_sq θ
  ring_nf at h ⊢
  linarith

/-! ## The measure of the closed intervals is the measure of the open ones -/

theorem restrict_Iθ_eq_Ioo :
    volume.restrict Work.Spaces.Iθ = volume.restrict (Set.Ioo 0 (π / 2)) := by
  apply Measure.restrict_congr_set
  rw [ae_eq_set]
  refine ⟨?_, ?_⟩
  · rw [show Work.Spaces.Iθ = Set.Icc (0 : ℝ) (π / 2) from rfl,
      Set.Icc_sdiff_Ioo_same (by linarith [Real.pi_pos] : (0 : ℝ) ≤ π / 2)]
    rw [Set.insert_eq]
    exact measure_union_null (measure_singleton 0) (measure_singleton _)
  · rw [show Work.Spaces.Iθ = Set.Icc (0 : ℝ) (π / 2) from rfl,
      Set.sdiff_eq_empty.mpr Set.Ioo_subset_Icc_self, measure_empty]

theorem restrict_Iz_eq_Ioi :
    volume.restrict Work.Spaces.Iz = volume.restrict (Set.Ioi (0 : ℝ)) := by
  apply Measure.restrict_congr_set
  rw [ae_eq_set]
  refine ⟨?_, ?_⟩
  · rw [show Work.Spaces.Iz = Set.Ici (0 : ℝ) from rfl, Set.Ici_sdiff_Ioi, Set.Icc_self]
    exact measure_singleton 0
  · rw [show Work.Spaces.Iz = Set.Ici (0 : ℝ) from rfl,
      Set.sdiff_eq_empty.mpr Set.Ioi_subset_Ici_self, measure_empty]

/-! ## Elementary angular bounds -/

theorem sin_two_nonneg_of_mem_Iθ {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) :
    0 ≤ Real.sin (2 * θ) :=
  Real.sin_nonneg_of_mem_Icc
    ⟨by linarith [hθ.1], by linarith [hθ.2, Real.pi_pos]⟩

theorem Gam_nonneg_of_Iθ {α θ : ℝ} (hα : 0 < α) (hθ : θ ∈ Work.Spaces.Iθ) :
    0 ≤ Work.Spaces.Gam α θ := (Work.Spaces.Gam_bounds α θ hα hθ).1

theorem Gam_le_one_of_Iθ {α θ : ℝ} (hα : 0 < α) (hθ : θ ∈ Work.Spaces.Iθ) :
    Work.Spaces.Gam α θ ≤ 1 := (Work.Spaces.Gam_bounds α θ hα hθ).2

/-- `Γ(θ) ≤ sin(2θ)^{α/3}`: since `sin θ cos²θ ≤ sin θ cos θ = sin(2θ)/2 ≤ sin(2θ)` and
both sides are obtained by raising to the nonnegative power `α/3`. -/
theorem Gam_le_sin_two_rpow {α θ : ℝ} (hα : 0 < α) (hθ : θ ∈ Work.Spaces.Iθ) :
    Work.Spaces.Gam α θ ≤ (Real.sin (2 * θ)) ^ (α / 3) := by
  have hs0 : 0 ≤ Real.sin θ := Real.sin_nonneg_of_mem_Icc ⟨hθ.1, by linarith [hθ.2, Real.pi_pos]⟩
  have hc0 : 0 ≤ Real.cos θ :=
    Real.cos_nonneg_of_mem_Icc ⟨by linarith [hθ.1, Real.pi_pos], hθ.2⟩
  have hc1 : Real.cos θ ≤ 1 := Real.cos_le_one θ
  have hbase : Real.sin θ * Real.cos θ ^ 2 ≤ Real.sin (2 * θ) := by
    rw [Real.sin_two_mul]
    nlinarith [mul_nonneg hs0 hc0, hc0, hc1, sq_nonneg (Real.cos θ),
      Real.cos_sq_le_one θ]
  rw [Work.Spaces.Gam]
  exact Real.rpow_le_rpow (mul_nonneg hs0 (sq_nonneg _)) hbase (by linarith)

/-- `∫_0^{π/2} sin(2θ)^{-p} ≤ 100/(1-p)` for `0 < p < 1`, uniformly in `p`. -/
theorem integral_sin_two_rpow_neg (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1) :
    ∫ θ in Work.Spaces.Iθ, (Real.sin (2 * θ)) ^ (-p) ≤ 100 / (1 - p) := by
  have hGint : Integrable
      (fun θ : ℝ => (Real.pi / 4) ^ p * (θ ^ (-p) + (Real.pi / 2 - θ) ^ (-p)))
      (volume.restrict Work.Spaces.Iθ) :=
    Work.Spaces.integrableOn_majorant_rpow p hp0 hp1
  have hGval : ∫ θ in Work.Spaces.Iθ,
        ((Real.pi / 4) ^ p * (θ ^ (-p) + (Real.pi / 2 - θ) ^ (-p)))
      = Real.pi * (1 / 2) ^ p / (1 - p) := Work.Spaces.integral_majorant_rpow p hp0 hp1
  have hnonneg : 0 ≤ᵐ[volume.restrict Work.Spaces.Iθ]
      (fun θ : ℝ => (Real.sin (2 * θ)) ^ (-p)) := by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with θ hθ
    exact Real.rpow_nonneg (sin_two_nonneg_of_mem_Iθ hθ) _
  have hle : (fun θ : ℝ => (Real.sin (2 * θ)) ^ (-p))
      ≤ᵐ[volume.restrict Work.Spaces.Iθ]
      (fun θ : ℝ => (Real.pi / 4) ^ p * (θ ^ (-p) + (Real.pi / 2 - θ) ^ (-p))) := by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with θ hθ
    exact Work.Spaces.sin_rpow_le_majorant p θ hp0 hθ
  have hmono := MeasureTheory.integral_mono_of_nonneg hnonneg hGint hle
  calc ∫ θ in Work.Spaces.Iθ, (Real.sin (2 * θ)) ^ (-p)
      ≤ ∫ θ in Work.Spaces.Iθ,
          ((Real.pi / 4) ^ p * (θ ^ (-p) + (Real.pi / 2 - θ) ^ (-p))) := hmono
    _ = Real.pi * (1 / 2) ^ p / (1 - p) := hGval
    _ ≤ 100 / (1 - p) := by
        refine div_le_div_of_nonneg_right ?_ (by linarith)
        calc Real.pi * (1 / 2) ^ p
            ≤ 4 * 1 := mul_le_mul (le_of_lt Real.pi_lt_four)
                (Real.rpow_le_one (by norm_num) (by norm_num) (le_of_lt hp0))
                (by positivity) (by norm_num)
          _ ≤ 100 := by norm_num

end Work.Construction
end
end
-- ===== merged: Submission.Work.Construction.Terms =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.Construction

set_option autoImplicit false

/-! ## The terms of `N₀` -/

/-- `I^{N₀}_1 = (3/(2α)) sin(2θ) L₁₂(F_*) ∂_θF_*` (first half of tex 1398). -/
def N01 (α : ℝ) (F g : ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ := fun z θ =>
  (3 / (2 * α)) * s2 θ * L12 (Fstar α) z * Work.Spaces.pth (Fstar α) z θ

/-- `I^{N₀}_2 = -(cos2θ - sin²θ) L₁₂(F_*) z∂_zF_*` (second half of tex 1398). -/
def N02 (α : ℝ) (F g : ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ := fun z θ =>
  -c2m θ * L12 (Fstar α) z * Work.Spaces.Dz (Fstar α) z θ

/-- `I^{N₀}_3 = (1/α) L₁₂(g) g`. -/
def N03 (α : ℝ) (F g : ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ := fun z θ =>
  (1 / α) * L12 g z * g z θ

/-- `I^{N₀}_4 = (3/(2α))sin(2θ)L₁₂(g)∂_θF` (with the full `F = F_* + g`). -/
def N04 (α : ℝ) (F g : ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ := fun z θ =>
  (3 / (2 * α)) * s2 θ * L12 g z * Work.Spaces.pth F z θ

/-- First half of `I^{N₀}_4`: `(3/(2α))sin(2θ)L₁₂(g)∂_θF_*`. -/
def N04a (α : ℝ) (F g : ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ := fun z θ =>
  (3 / (2 * α)) * s2 θ * L12 g z * Work.Spaces.pth (Fstar α) z θ

/-- Second half of `I^{N₀}_4`: `(3/(2α))sin(2θ)L₁₂(g)∂_θg`. -/
def N04b (α : ℝ) (F g : ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ := fun z θ =>
  (3 / (2 * α)) * s2 θ * L12 g z * Work.Spaces.pth g z θ

/-- `I^{N₀}_5 = -(cos2θ-sin²θ)L₁₂(g)z∂_zF` (with the full `F = F_* + g`). -/
def N05 (α : ℝ) (F g : ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ := fun z θ =>
  -c2m θ * L12 g z * Work.Spaces.Dz F z θ

/-- First half of `I^{N₀}_5`: `-(cos2θ-sin²θ)L₁₂(g)z∂_zF_*`. -/
def N05a (α : ℝ) (F g : ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ := fun z θ =>
  -c2m θ * L12 g z * Work.Spaces.Dz (Fstar α) z θ

/-- Second half of `I^{N₀}_5`: `-(cos2θ-sin²θ)L₁₂(g)z∂_zg`. -/
def N05b (α : ℝ) (F g : ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ := fun z θ =>
  -c2m θ * L12 g z * Work.Spaces.Dz g z θ

/-- `I^{N₀}_6 = -(cos2θ-sin²θ)L₁₂(F_*)z∂_zg`. -/
def N06 (α : ℝ) (F g : ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ := fun z θ =>
  -c2m θ * L12 (Fstar α) z * Work.Spaces.Dz g z θ

theorem N0_eq_sum (α : ℝ) (F g : ℝ → ℝ → ℝ) :
    N0 α F g = N01 α F g + N02 α F g + N03 α F g + N04 α F g + N05 α F g + N06 α F g := by
  funext z θ
  simp only [N0, N01, N02, N03, N04, N05, N06, Pi.add_apply]
  ring



/-! ## The terms of `N` -/

/-- `I^{N}_1 = 2ℛ(Φ - (1/4α)sin2θL₁₂(F)) F`. -/
def N1 (α : ℝ) (F Φ : ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ := fun z θ =>
  2 * Rop α (PhiTil α F Φ) z θ * F z θ

/-- `I^{N}_2 = -2U(Φ - (1/4α)sin2θL₁₂(F)) ∂_θF`. -/
def N2 (α : ℝ) (F Φ : ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ := fun z θ =>
  -2 * Uop α (PhiTil α F Φ) z θ * Work.Spaces.pth F z θ

/-- `I^{N}_3 = -2αV(Φ - (1/4α)sin2θL₁₂(F)) z∂_zF`. -/
def N3 (α : ℝ) (F Φ : ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ := fun z θ =>
  -2 * α * Vop (PhiTil α F Φ) z θ * Work.Spaces.Dz F z θ

/-- `I^{N}_4 = -(1/2)sin(2θ)(F,K)_{L²_θ}∂_θF` (the angular-moment term; the paper writes the
coefficient `-α`, see the module docstring of `Defs.lean`). -/
def N4 (α : ℝ) (F Φ : ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ := fun z θ =>
  -(1 / 2) * s2 θ * FK F z * Work.Spaces.pth F z θ

/-- `I^{N}_5 = -sin²θ (F,K)_{L²_θ} F` (the second angular-moment term). -/
def N5 (α : ℝ) (F Φ : ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ := fun z θ =>
  -Real.sin θ ^ 2 * FK F z * F z θ

theorem N_eq_sum (α : ℝ) (F Φ : ℝ → ℝ → ℝ) :
    N α F Φ = N1 α F Φ + N2 α F Φ + N3 α F Φ + N4 α F Φ + N5 α F Φ := by
  funext z θ
  simp only [N, N1, N2, N3, N4, N5, Pi.add_apply]
  ring

/-! ## The terms of `N_*` -/




end Work.Construction
end
end
-- ===== merged: Submission.Work.ConstructionInstance.psiField_of_potential =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

set_option autoImplicit false

namespace Work.ConstructionInstance


end Work.ConstructionInstance
end
-- ===== merged: Submission.Work.CoreResiduals.VorticityEquation.fderiv_eTheta =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The Fréchet derivative of the angular unit vector `e_θ`

`e_θ = (1/r) • angularVec` with `r = radial x = √(x₀² + x₁²)` and `angularVec x = (-x₁, x₀, 0)`,
so off the axis (`0 < radial x`) the product rule gives

`fderiv ℝ e_θ x v = -(x₀v₀ + x₁v₁)/r³ • angularVec x + (1/r) • angularVec v`,

the first term being the derivative of the factor `1/r` (whose derivative in direction `v` is
`-(x₀v₀+x₁v₁)/r³`) and the second the derivative of the linear map `angularVec` (which is itself).
-/

namespace Work.CoreResiduals.VorticityEquation

open Work.Cyl

theorem fderiv_eTheta (x v : Work.Cyl.R3) (hr : 0 < Work.Cyl.radial x) :
    fderiv ℝ (fun y : Work.Cyl.R3 => Work.Cyl.eTheta y) x v
      = (-(x 0 * v 0 + x 1 * v 1) / (Work.Cyl.radial x) ^ 3) • Work.Cyl.angularVec x
        + ((Work.Cyl.radial x)⁻¹) • Work.Cyl.angularVec v := by
  have hrne : radial x ≠ 0 := ne_of_gt hr
  -- `e_θ = (1/r) • angularVec`
  have hfun : eTheta = (fun y : R3 => (radial y)⁻¹) • angularVec := by
    funext y
    show (1 / radial y) • angularVec y = (radial y)⁻¹ • angularVec y
    rw [one_div]
  have hdiffInv : DifferentiableAt ℝ (fun y : R3 => (radial y)⁻¹) x :=
    (differentiableAt_radial x hrne).inv hrne
  have hdiffAng : DifferentiableAt ℝ angularVec x := by
    have h : angularVec = fun y : R3 => (-(y 1)) • e0 + (y 0) • e1 := by
      funext y
      apply ext_coord <;>
        simp [angularVec, e0, e1, FiniteTimeSingularity.e]
    rw [h]; fun_prop
  -- derivative of the radial weight
  have hrad : fderiv ℝ radial x v = (x 0 * v 0 + x 1 * v 1) / radial x :=
    Work.Cyl.fderiv_radial_apply x v hr
  -- derivative of the linear map `angularVec` is `angularVec` itself
  have hang : fderiv ℝ angularVec x v = angularVec v :=
    Work.Cyl.fderiv_angularVec_apply x v
  -- derivative of `y ↦ (radial y)⁻¹`, by the chain rule through `s ↦ s⁻¹`
  have hderivInv : fderiv ℝ (fun y : R3 => (radial y)⁻¹) x v
      = -(x 0 * v 0 + x 1 * v 1) / (radial x) ^ 3 := by
    have hcomp : fderiv ℝ (fun y : R3 => (radial y)⁻¹) x
        = (fderiv ℝ (fun s : ℝ => s⁻¹) (radial x)).comp (fderiv ℝ radial x) := by
      have h := fderiv_comp (𝕜 := ℝ) x (f := radial) (g := fun s : ℝ => s⁻¹)
        (differentiableAt_inv hrne) (differentiableAt_radial x hrne)
      simpa [Function.comp_def] using h
    rw [hcomp, fderiv_inv]
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.toSpanSingleton_apply,
      smul_eq_mul]
    rw [hrad]
    field_simp
  -- product rule
  rw [hfun, fderiv_smul (𝕜 := ℝ) hdiffInv hdiffAng]
  simp only [add_apply, smul_apply, ContinuousLinearMap.smulRight_apply, hderivInv, hang]
  abel

end Work.CoreResiduals.VorticityEquation
end
-- ===== merged: Submission.Work.Cyl.Transfer =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The transfer lemmas for the polar change of variables `(r, x₃) ↦ (ρ, θ)`, `R = ρ^α`

This module collects the chain-rule dictionary of §Setup (paper line 258):

* `Work.Cyl.pdR_comp_polar` : `∂_r [F(ρ^α, θ)] = (cos θ/ρ)·αR·∂_R F − (sin θ/ρ)·∂_θ F`
* `Work.Cyl.pdZ_comp_polar` : `∂_{x₃} [F(ρ^α, θ)] = (sin θ/ρ)·αR·∂_R F + (cos θ/ρ)·∂_θ F`
* `Work.Cyl.pdR_comp_polar_rho`, `Work.Cyl.pdZ_comp_polar_rho` : the same with `G(ρ, θ)`
  (`α = 0` form, `∂_ρ` instead of `R ∂_R`)
* `Work.Cyl.alpha_mul_pow_mul_pdR` : `α R ∂_R = ρ ∂_ρ`, i.e.
  `α · ρ^α · ∂_R F(ρ^α, θ) = ρ · ∂_ρ (F(ρ^α, θ))`
* the same dictionary read on `ℝ³` itself (the direction `e_r` is `∂_r`, the direction `e₃` is
  `∂_{x₃}`): `Work.Cyl.fderiv_rho_theta_eR`, `Work.Cyl.fderiv_rho_theta_eZ`,
  `Work.Cyl.fderiv_R_theta_eR`, `Work.Cyl.fderiv_R_theta_eZ`
  (e.g. `fderiv ℝ (fun y ↦ F (ρ y ^ α) (θ y)) x (e_r x)
   = (cos θ/ρ)·αR·∂_R F − (sin θ/ρ)·∂_θ F` with `ρ = rho x`, `θ = theta x`).

Here `Work.Cyl.rhoP r z = √(r²+z²)`, `Work.Cyl.thetaP r z = arctan(z/r)`,
`Work.Cyl.pdR`, `Work.Cyl.pdZ` are the partial derivatives `∂_r`, `∂_{x₃}`, and
`Real.cos (thetaP r z) = r/ρ`, `Real.sin (thetaP r z) = z/ρ` (see `Work.Cyl.cos_thetaP`,
`Work.Cyl.sin_thetaP`).
-/
end
-- ===== merged: Submission.Work.Cyl.hasDerivAt_rhoP_rpow_div_snd =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.Cyl

/-- The axial derivative of `z' ↦ ρ(r,z')^α / c`, obtained from
`hasDerivAt_rhoP_rpow_polar` (which gives the derivative `α ρ^{α-1} · (z/ρ)` of
`z' ↦ ρ(r,z')^α`) after dividing by the constant `c` and rewriting
`ρ^{α-1} · (z/ρ) = ρ^α · (z/ρ^2)`. -/
theorem hasDerivAt_rhoP_rpow_div_snd (r α z c : ℝ) (hr : 0 < r) :
    HasDerivAt (fun z' : ℝ => Work.Cyl.rhoP r z' ^ α / c)
      (α * (Work.Cyl.rhoP r z ^ α / c) * (z / Work.Cyl.rhoP r z ^ 2)) z := by
  have h := (Work.Cyl.hasDerivAt_rhoP_rpow_polar r α z hr).div_const c
  have hne : rhoP r z ≠ 0 := rhoP_ne_zero hr z
  convert h using 1
  rw [Real.rpow_sub_one hne, div_eq_mul_inv, div_eq_mul_inv]
  field_simp

end Work.Cyl
end
-- ===== merged: Submission.Work.Cyl.isOdd_cylField =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

set_option autoImplicit false
set_option linter.unusedSimpArgs false

open Work.Cyl

namespace Work.Cyl

/-!
# Parity of the no-swirl field `cylField ur uz`

`cylField ur uz x = (u_r(r,x₃)/r) • (x₀,x₁,0) + u_z(r,x₃) • e₃` with `r = √(x₀²+x₁²)`.

Since `cylField ur uz = axiField (fun s z => u_r(√s,z)/√s) (fun s z => u_z(√s,z))` the parity
criterion is exactly the one proved for `axiField`, transported across `s = r²` (`√(r²) = r`
for `r ≥ 0`).  The result is

* `u_r` is even in `x₃`, only forced for `r > 0` (on the axis the factor `x₀ = x₁ = 0` makes the
  first two components vanish identically);
* `u_z` is odd in `x₃`, forced for `r ≥ 0`, including the axis.
-/


end Work.Cyl
end
-- ===== merged: Submission.Work.Cyl.vorticity_psiField =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The vorticity of the stream-function field `psiField ψ`

If `ψ` is a `C²` stream function then the vorticity of the axisymmetric no-swirl field
`psiField ψ = u_r e_r + u_z e_θ` (paper (PsiTou)) has only the angular component, equal to
`ω^θ = -Lψ` where `L = cylOp` is the axisymmetric elliptic operator of (3dBSL):

  `∇ × (psiField ψ) x = -cylOp ψ (radial x) (axial x) • eTheta x`.

This combines the coordinate description of the curl of `cylField` (`vorticity_cylField`)
with the stream-function identity `vortTheta_psiField`.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

open scoped Matrix Topology
open Work.Cyl

namespace Work.Cyl

/-- If `ψ : ℝ × ℝ → ℝ` is `C²` at `(r,z)`, then its radial partial derivative
`p ↦ pdR ψ p.1 p.2` is differentiable at `(r,z)`.

Indeed, `pdR ψ p.1 p.2 = fderiv ℝ (uncurry ψ) p (1,0)` at every point `p` where `ψ` is
differentiable, and `fderiv ℝ (uncurry ψ)` is `C¹` (hence differentiable) at `(r,z)` because
`uncurry ψ` is `C²` there. -/
lemma differentiableAt_pdR (ψ : ℝ → ℝ → ℝ) (r z : ℝ)
    (hψ : ContDiffAt ℝ 2 (fun p : ℝ × ℝ => ψ p.1 p.2) (r, z)) :
    DifferentiableAt ℝ (fun p : ℝ × ℝ => pdR ψ p.1 p.2) (r, z) := by
  -- `ψ` is differentiable on a neighbourhood of `(r,z)`.
  have hev : ∀ᶠ p : ℝ × ℝ in 𝓝 (r, z),
      DifferentiableAt ℝ (fun q : ℝ × ℝ => ψ q.1 q.2) p :=
    (hψ.eventually (by norm_num)).mono fun p hp => hp.differentiableAt (by norm_num)
  -- `fderiv ℝ (uncurry ψ)` is `C¹`, hence differentiable, at `(r,z)`.
  have hfd : ContDiffAt ℝ 1 (fderiv ℝ (fun p : ℝ × ℝ => ψ p.1 p.2)) (r, z) :=
    hψ.fderiv_right (m := 1) (by norm_num)
  have hfdd : DifferentiableAt ℝ (fderiv ℝ (fun p : ℝ × ℝ => ψ p.1 p.2)) (r, z) :=
    hfd.differentiableAt_one
  -- evaluating the derivative at the fixed direction `(1,0)` preserves differentiability.
  have hΦ : DifferentiableAt ℝ
      (fun p : ℝ × ℝ => (fderiv ℝ (fun q : ℝ × ℝ => ψ q.1 q.2) p) (1, 0)) (r, z) :=
    ((ContinuousLinearMap.apply ℝ ℝ ((1, 0) : ℝ × ℝ)).differentiableAt).comp (r, z) hfdd
  refine hΦ.congr_of_eventuallyEq ?_
  filter_upwards [hev] with p hp
  exact (fderiv_prod_apply_fst ψ p.1 p.2 hp).symm

/-- If `ψ : ℝ × ℝ → ℝ` is `C²` at `(r,z)`, then its axial partial derivative
`p ↦ pdZ ψ p.1 p.2` is differentiable at `(r,z)`. -/
lemma differentiableAt_pdZ (ψ : ℝ → ℝ → ℝ) (r z : ℝ)
    (hψ : ContDiffAt ℝ 2 (fun p : ℝ × ℝ => ψ p.1 p.2) (r, z)) :
    DifferentiableAt ℝ (fun p : ℝ × ℝ => pdZ ψ p.1 p.2) (r, z) := by
  have hev : ∀ᶠ p : ℝ × ℝ in 𝓝 (r, z),
      DifferentiableAt ℝ (fun q : ℝ × ℝ => ψ q.1 q.2) p :=
    (hψ.eventually (by norm_num)).mono fun p hp => hp.differentiableAt (by norm_num)
  have hfd : ContDiffAt ℝ 1 (fderiv ℝ (fun p : ℝ × ℝ => ψ p.1 p.2)) (r, z) :=
    hψ.fderiv_right (m := 1) (by norm_num)
  have hfdd : DifferentiableAt ℝ (fderiv ℝ (fun p : ℝ × ℝ => ψ p.1 p.2)) (r, z) :=
    hfd.differentiableAt_one
  have hΦ : DifferentiableAt ℝ
      (fun p : ℝ × ℝ => (fderiv ℝ (fun q : ℝ × ℝ => ψ q.1 q.2) p) (0, 1)) (r, z) :=
    ((ContinuousLinearMap.apply ℝ ℝ ((0, 1) : ℝ × ℝ)).differentiableAt).comp (r, z) hfdd
  refine hΦ.congr_of_eventuallyEq ?_
  filter_upwards [hev] with p hp
  exact (fderiv_prod_apply_snd ψ p.1 p.2 hp).symm

/-- The vorticity of the stream-function field `psiField ψ` off the axis is `-cylOp ψ` times the
angular vector `e_θ`. -/
theorem vorticity_psiField (ψ : ℝ → ℝ → ℝ) (x : Work.Cyl.R3)
    (hψ : ContDiffAt ℝ 2 (fun p : ℝ × ℝ => ψ p.1 p.2) (Work.Cyl.radial x, Work.Cyl.axial x))
    (hr : 0 < Work.Cyl.radial x) :
    FiniteTimeSingularity.vorticity (Work.Cyl.psiField ψ) x =
      -Work.Cyl.cylOp ψ (Work.Cyl.radial x) (Work.Cyl.axial x) • Work.Cyl.eTheta x := by
  have hR : radial x ≠ 0 := ne_of_gt hr
  have hF : DifferentiableAt ℝ (fun p : ℝ × ℝ => ψ p.1 p.2) (radial x, axial x) :=
    hψ.differentiableAt (by norm_num)
  have hpdR : DifferentiableAt ℝ (fun p : ℝ × ℝ => pdR ψ p.1 p.2) (radial x, axial x) :=
    differentiableAt_pdR ψ (radial x) (axial x) hψ
  -- the two components of `psiField ψ` are differentiable at `(radial x, axial x)`
  have hur : DiffAt2 (pdZ ψ) (radial x) (axial x) :=
    differentiableAt_pdZ ψ (radial x) (axial x) hψ
  have huz : DiffAt2 (fun r z => -(ψ r z / r) - pdR ψ r z) (radial x) (axial x) := by
    show DifferentiableAt ℝ
      (fun p : ℝ × ℝ => -(ψ p.1 p.2 / p.1) - pdR ψ p.1 p.2) (radial x, axial x)
    fun_prop
  -- the coordinate form of the curl, and the stream-function identity
  have hcurl := vorticity_cylField (pdZ ψ) (fun r z => -(ψ r z / r) - pdR ψ r z) x hur huz hr
  have hvt := vortTheta_psiField ψ (radial x) (axial x) hψ hR
  rw [show psiField ψ = cylField (pdZ ψ) (fun r z => -(ψ r z / r) - pdR ψ r z) from rfl]
  rw [hcurl, hvt]

end Work.Cyl
end
-- ===== merged: Submission.Work.Elliptic.DivSinIdentityA =====
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





/-- `HasDerivAt` of `fun x => Real.sin (2 * x)` at `θ`. -/
theorem hasDerivAt_sin_two (θ : ℝ) :
    HasDerivAt (fun x : ℝ => Real.sin (2 * x)) (2 * Real.cos (2 * θ)) θ := by
  have h2 : HasDerivAt (fun x : ℝ => 2 * x) 2 θ := by
    simpa using (hasDerivAt_id θ).const_mul (2 : ℝ)
  simpa [mul_comm] using h2.sin

/-- `HasDerivAt` of `fun x => Real.cos (2 * x)` at `θ`. -/
theorem hasDerivAt_cos_two (θ : ℝ) :
    HasDerivAt (fun x : ℝ => Real.cos (2 * x)) (-2 * Real.sin (2 * θ)) θ := by
  have h2 : HasDerivAt (fun x : ℝ => 2 * x) 2 θ := by
    simpa using (hasDerivAt_id θ).const_mul (2 : ℝ)
  simpa [mul_comm] using h2.cos









/-- `θ ↦ sin(2θ)^p` is continuous on `(0, π/2)` for every real exponent `p`. -/
theorem continuousOn_sin_two_rpow (p : ℝ) :
    ContinuousOn (fun θ : ℝ => (Real.sin (2 * θ)) ^ p) (Set.Ioo 0 (Real.pi / 2)) :=
  ((Real.continuous_sin.comp
      (continuous_const.mul continuous_id : Continuous fun x : ℝ => (2 : ℝ) * x)).continuousOn).rpow_const
    (fun x hx => Or.inl (Work.Elliptic.sin_two_ne_zero' hx))






end Work.Elliptic
end
end
-- ===== merged: Submission.Work.Elliptic.DivSinSliceBddEst =====
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






end Work.Elliptic
end
end
-- ===== merged: Submission.Work.Elliptic.DivSinSmoothBounds =====
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

/-- For `t ∈ [0, π/4]`, `t ≤ (π/4) sin(2t)` (the linear lower bound for `sin` on a quarter
period). -/
private lemma le_quarter_pi_mul_sin_two (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) (Real.pi / 4)) :
    t ≤ (Real.pi / 4) * Real.sin (2 * t) := by
  obtain ⟨ht0, ht1⟩ := ht
  have h2t0 : 0 ≤ 2 * t := by linarith
  have h2t1 : 2 * t ≤ Real.pi / 2 := by linarith [Real.pi_pos]
  have h3 : 2 / Real.pi * (2 * t) ≤ Real.sin (2 * t) := Real.mul_le_sin h2t0 h2t1
  have h3' : (4 / Real.pi) * t ≤ Real.sin (2 * t) := by
    have : 2 / Real.pi * (2 * t) = (4 / Real.pi) * t := by ring
    linarith [h3, this]
  have h4 : (Real.pi / 4) * ((4 / Real.pi) * t) ≤ (Real.pi / 4) * Real.sin (2 * t) :=
    mul_le_mul_of_nonneg_left h3' (by positivity)
  have h5 : (Real.pi / 4) * ((4 / Real.pi) * t) = t := by
    have hπ : Real.pi ≠ 0 := ne_of_gt Real.pi_pos
    field_simp
  linarith [h4, h5]

/-- `min θ (π/2 - θ) ≤ (π/4) sin(2θ)` on `[0, π/2]`: the two-variable form of the linear
lower bound for `sin`. -/
private lemma min_le_quarter_pi_mul_sin_two (θ : ℝ) (hθ : θ ∈ Set.Icc (0 : ℝ) (Real.pi / 2)) :
    min θ (Real.pi / 2 - θ) ≤ (Real.pi / 4) * Real.sin (2 * θ) := by
  rcases le_total θ (Real.pi / 2 - θ) with hle | hle
  · rw [min_eq_left hle]
    exact le_quarter_pi_mul_sin_two θ ⟨hθ.1, by linarith [hle, hθ.2]⟩
  · rw [min_eq_right hle]
    have ht : Real.pi / 2 - θ ∈ Set.Icc (0 : ℝ) (Real.pi / 4) :=
      ⟨by linarith [hθ.2], by linarith [hle]⟩
    have h := le_quarter_pi_mul_sin_two (Real.pi / 2 - θ) ht
    have hsin : Real.sin (2 * (Real.pi / 2 - θ)) = Real.sin (2 * θ) := by
      rw [show 2 * (Real.pi / 2 - θ) = Real.pi - 2 * θ by ring, Real.sin_pi_sub]
    rwa [hsin] at h




end Work.Elliptic
end
end
-- ===== merged: Submission.Work.Elliptic.SinSliceBounds =====
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

/-! ## Elementary angular bounds -/

/-- The closed interval `[0, π/2]` lies in the open set on which a `SmoothSlice` is smooth. -/
private lemma ssb_Icc_subset : Set.Icc 0 (Real.pi / 2) ⊆ Set.Ioo (-1 : ℝ) (Real.pi / 2 + 1) :=
  Set.Icc_subset_Ioo (by norm_num) (by linarith [Real.pi_pos])

private lemma ssb_one_le_half_pi : (1 : ℝ) ≤ Real.pi / 2 := by
  have h := Real.pi_gt_three
  linarith

private lemma ssb_arith (θ : ℝ) : Real.pi / 2 * (2 / Real.pi * (2 * θ)) = 2 * θ := by
  field_simp

/-- On `(0, π/2)`, `sin (2θ)` is positive and dominates `min θ (π/2 - θ)`: both `θ` and
`π/2 - θ` are at most `(π/2) sin (2θ)`, by Jordan's inequality `sin x ≥ 2x/π`. -/
private lemma ssb_min_le_sin {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    0 < Real.sin (2 * θ) ∧ min θ (Real.pi / 2 - θ) ≤ Real.pi / 2 * Real.sin (2 * θ) := by
  have hsinpos : 0 < Real.sin (2 * θ) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2])
  refine ⟨hsinpos, ?_⟩
  rcases le_total θ (Real.pi / 4) with hle | hle
  · rw [min_eq_left (by linarith)]
    have h4 : 2 / Real.pi * (2 * θ) ≤ Real.sin (2 * θ) :=
      Real.mul_le_sin (show (0 : ℝ) ≤ 2 * θ by linarith [hθ.1])
        (show 2 * θ ≤ Real.pi / 2 by linarith [hle])
    have hstep : Real.pi / 2 * (2 / Real.pi * (2 * θ)) ≤ Real.pi / 2 * Real.sin (2 * θ) :=
      mul_le_mul_of_nonneg_left h4 (by positivity)
    rw [ssb_arith] at hstep
    linarith [hθ.1]
  · rw [min_eq_right (by linarith)]
    have ht : Real.sin (2 * θ) = Real.sin (2 * (Real.pi / 2 - θ)) := by
      rw [show 2 * θ = Real.pi - 2 * (Real.pi / 2 - θ) by ring, Real.sin_pi_sub]
    rw [ht]
    have h4 : 2 / Real.pi * (2 * (Real.pi / 2 - θ)) ≤ Real.sin (2 * (Real.pi / 2 - θ)) :=
      Real.mul_le_sin (show (0 : ℝ) ≤ 2 * (Real.pi / 2 - θ) by linarith [hθ.2])
        (show 2 * (Real.pi / 2 - θ) ≤ Real.pi / 2 by linarith [hle])
    have hstep : Real.pi / 2 * (2 / Real.pi * (2 * (Real.pi / 2 - θ)))
        ≤ Real.pi / 2 * Real.sin (2 * (Real.pi / 2 - θ)) :=
      mul_le_mul_of_nonneg_left h4 (by positivity)
    rw [ssb_arith] at hstep
    linarith [hθ.2]

/-! ## The numerator of the derivative of the quotient -/

/-- `W h θ = sin(2θ) h'(θ) - 2 cos(2θ) h(θ)`: the numerator of the derivative of
`SinQ h = h / sin(2θ)`. -/
private def ssbW (h : ℝ → ℝ) : ℝ → ℝ :=
  fun θ => deriv h θ * Real.sin (2 * θ) - 2 * Real.cos (2 * θ) * h θ

private lemma ssb_hasDerivAt_sin_two (θ : ℝ) :
    HasDerivAt (fun x : ℝ => Real.sin (2 * x)) (2 * Real.cos (2 * θ)) θ := by
  have h1 : HasDerivAt (fun x : ℝ => 2 * x) 2 θ := by
    simpa using (hasDerivAt_id θ).const_mul (2 : ℝ)
  have h2 := h1.sin
  rw [show Real.cos (2 * θ) * 2 = 2 * Real.cos (2 * θ) by ring] at h2
  exact h2

private lemma ssb_hasDerivAt_cos_two (θ : ℝ) :
    HasDerivAt (fun x : ℝ => Real.cos (2 * x)) (-2 * Real.sin (2 * θ)) θ := by
  have h1 : HasDerivAt (fun x : ℝ => 2 * x) 2 θ := by
    simpa using (hasDerivAt_id θ).const_mul (2 : ℝ)
  have h2 := h1.cos
  rw [show -Real.sin (2 * θ) * 2 = -2 * Real.sin (2 * θ) by ring] at h2
  exact h2

/-- The derivative of `W h`: `(W h)' θ = sin(2θ) (h''(θ) + 4 h(θ))`. -/
private lemma ssb_hasDerivAt_W (h : ℝ → ℝ) (hsm : SmoothSlice h) (θ : ℝ)
    (hθ : θ ∈ Set.Ioo (-1 : ℝ) (Real.pi / 2 + 1)) :
    HasDerivAt (ssbW h) (Real.sin (2 * θ) * (deriv (deriv h) θ + 4 * h θ)) θ := by
  have hU : Set.Ioo (-1 : ℝ) (Real.pi / 2 + 1) ∈ 𝓝 θ := isOpen_Ioo.mem_nhds hθ
  have h2 : ContDiffOn ℝ 2 h (Set.Ioo (-1 : ℝ) (Real.pi / 2 + 1)) := hsm.of_le le_top
  have hC2 : ContDiffAt ℝ 2 h θ := h2.contDiffAt hU
  have hdh : HasDerivAt h (deriv h θ) θ := (hC2.differentiableAt (by norm_num)).hasDerivAt
  have hd1 : ContDiffOn ℝ 1 (deriv h) (Set.Ioo (-1 : ℝ) (Real.pi / 2 + 1)) :=
    h2.deriv_of_isOpen isOpen_Ioo (m := 1) (by norm_num)
  have hddh : HasDerivAt (deriv h) (deriv (deriv h) θ) θ :=
    ((hd1.contDiffAt hU).differentiableAt (by norm_num)).hasDerivAt
  have hA : HasDerivAt (fun x : ℝ => deriv h x * Real.sin (2 * x))
      (deriv (deriv h) θ * Real.sin (2 * θ) + deriv h θ * (2 * Real.cos (2 * θ))) θ :=
    hddh.mul (ssb_hasDerivAt_sin_two θ)
  have hB : HasDerivAt (fun x : ℝ => 2 * Real.cos (2 * x) * h x)
      ((2 * (-2 * Real.sin (2 * θ))) * h θ + (2 * Real.cos (2 * θ)) * deriv h θ) θ :=
    ((ssb_hasDerivAt_cos_two θ).const_mul 2).mul hdh
  have hAB : HasDerivAt (ssbW h)
      ((deriv (deriv h) θ * Real.sin (2 * θ) + deriv h θ * (2 * Real.cos (2 * θ)))
        - ((2 * (-2 * Real.sin (2 * θ))) * h θ + (2 * Real.cos (2 * θ)) * deriv h θ)) θ :=
    hA.sub hB
  have key : (deriv (deriv h) θ * Real.sin (2 * θ) + deriv h θ * (2 * Real.cos (2 * θ)))
      - ((2 * (-2 * Real.sin (2 * θ))) * h θ + (2 * Real.cos (2 * θ)) * deriv h θ)
      = Real.sin (2 * θ) * (deriv (deriv h) θ + 4 * h θ) := by ring
  rw [key] at hAB
  exact hAB

/-- A uniform bound for `|h'' + 4h|` on the closed angular interval. -/
private lemma ssb_C2_bound (h : ℝ → ℝ) (hsm : SmoothSlice h) :
    ∃ M₀ : ℝ, 0 ≤ M₀ ∧ ∀ x ∈ Set.Icc 0 (Real.pi / 2),
      |deriv (deriv h) x + 4 * h x| ≤ M₀ := by
  have h2 : ContDiffOn ℝ 2 h (Set.Ioo (-1 : ℝ) (Real.pi / 2 + 1)) := hsm.of_le le_top
  have hdd : ContDiffOn ℝ 0 (deriv (deriv h)) (Set.Ioo (-1 : ℝ) (Real.pi / 2 + 1)) :=
    (h2.deriv_of_isOpen isOpen_Ioo (m := 1) (by norm_num)).deriv_of_isOpen isOpen_Ioo
      (m := 0) (by norm_num)
  have hcont : ContinuousOn (fun x : ℝ => deriv (deriv h) x + 4 * h x)
      (Set.Icc 0 (Real.pi / 2)) :=
    ((hdd.continuousOn).mono ssb_Icc_subset).add
      (((h2.continuousOn).mono ssb_Icc_subset).const_mul 4)
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hcont
  refine ⟨max C 0, le_max_right _ _, ?_⟩
  intro x hx
  simpa only [Real.norm_eq_abs] using le_trans (hC x hx) (le_max_left _ _)

/-- Second order vanishing of `W h = sin(2θ) h' - 2 cos(2θ) h` at both endpoints. -/
private lemma ssb_W_snd (h : ℝ → ℝ) (hsm : SmoothSlice h) (h0 : h 0 = 0)
    (hp : h (Real.pi / 2) = 0) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ θ ∈ Set.Ioo 0 (Real.pi / 2),
      |ssbW h θ| ≤ M * (min θ (Real.pi / 2 - θ)) ^ 2 := by
  obtain ⟨M₀, hM₀0, hM₀⟩ := ssb_C2_bound h hsm
  have hWderiv : ∀ x ∈ Set.Icc 0 (Real.pi / 2),
      HasDerivWithinAt (ssbW h) (Real.sin (2 * x) * (deriv (deriv h) x + 4 * h x))
        (Set.Icc 0 (Real.pi / 2)) x := by
    intro x hx
    have hx' : x ∈ Set.Ioo (-1 : ℝ) (Real.pi / 2 + 1) := ssb_Icc_subset hx
    have h' : HasDerivAt (ssbW h) (Real.sin (2 * x) * (deriv (deriv h) x + 4 * h x)) x :=
      ssb_hasDerivAt_W h hsm x hx'
    exact h'.hasDerivWithinAt
  have hWbnd : ∀ x ∈ Set.Icc 0 (Real.pi / 2),
      ‖Real.sin (2 * x) * (deriv (deriv h) x + 4 * h x)‖ ≤ (2 * M₀) * x := by
    intro x hx
    have hx1 : x ≤ Real.pi / 2 := hx.2
    have hsin0 : 0 ≤ Real.sin (2 * x) :=
      Real.sin_nonneg_of_nonneg_of_le_pi (by linarith [hx.1]) (by linarith [hx1])
    have hsinle : Real.sin (2 * x) ≤ 2 * x := Real.sin_le (by linarith [hx.1])
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hsin0]
    calc Real.sin (2 * x) * |deriv (deriv h) x + 4 * h x| ≤ (2 * x) * M₀ :=
          mul_le_mul hsinle (hM₀ x hx) (abs_nonneg _) (by linarith [hx.1])
      _ = 2 * M₀ * x := by ring
  have hhalf1 : ∀ x ∈ Set.Icc 0 (Real.pi / 2), ‖ssbW h x - ssbW h 0‖ ≤ (2 * M₀) * x ^ 2 :=
    seg_second_order_bound (ssbW h)
      (fun x => Real.sin (2 * x) * (deriv (deriv h) x + 4 * h x)) (2 * M₀) (Real.pi / 2)
      (by positivity) (by linarith [Real.pi_pos]) hWderiv hWbnd
  have hW0 : ssbW h 0 = 0 := by simp [ssbW, h0]
  have hfirst : ∀ x ∈ Set.Icc 0 (Real.pi / 2), |ssbW h x| ≤ (2 * M₀) * x ^ 2 := by
    intro x hx
    have hval1 := hhalf1 x hx
    rw [hW0, sub_zero, Real.norm_eq_abs] at hval1
    exact hval1
  have hWpi : ssbW h (Real.pi / 2) = 0 := by
    have h1 : Real.sin (2 * (Real.pi / 2)) = 0 := by
      rw [show 2 * (Real.pi / 2) = Real.pi by ring, Real.sin_pi]
    have h2 : Real.cos (2 * (Real.pi / 2)) = -1 := by
      rw [show 2 * (Real.pi / 2) = Real.pi by ring, Real.cos_pi]
    simp [ssbW, hp, h1, h2]
  have hWref : ∀ t ∈ Set.Icc 0 (Real.pi / 2),
      HasDerivWithinAt (fun s : ℝ => ssbW h (Real.pi / 2 - s))
        (-(Real.sin (2 * t) * (deriv (deriv h) (Real.pi / 2 - t) + 4 * h (Real.pi / 2 - t))))
        (Set.Icc 0 (Real.pi / 2)) t := by
    intro t ht
    have hy : Real.pi / 2 - t ∈ Set.Ioo (-1 : ℝ) (Real.pi / 2 + 1) :=
      ssb_Icc_subset ⟨by linarith [ht.2], by linarith [ht.1]⟩
    have hWy := ssb_hasDerivAt_W h hsm (Real.pi / 2 - t) hy
    have hg : HasDerivAt (fun s : ℝ => Real.pi / 2 - s) (-1) t :=
      (hasDerivAt_id t).const_sub (Real.pi / 2)
    have hcomp : HasDerivAt (fun s : ℝ => ssbW h (Real.pi / 2 - s))
        (Real.sin (2 * (Real.pi / 2 - t))
          * (deriv (deriv h) (Real.pi / 2 - t) + 4 * h (Real.pi / 2 - t)) * (-1)) t :=
      hWy.comp t hg
    have hsin' : Real.sin (2 * (Real.pi / 2 - t)) = Real.sin (2 * t) := by
      rw [show 2 * (Real.pi / 2 - t) = Real.pi - 2 * t by ring, Real.sin_pi_sub]
    have hval : Real.sin (2 * (Real.pi / 2 - t))
          * (deriv (deriv h) (Real.pi / 2 - t) + 4 * h (Real.pi / 2 - t)) * (-1)
        = -(Real.sin (2 * t) * (deriv (deriv h) (Real.pi / 2 - t) + 4 * h (Real.pi / 2 - t))) := by
      rw [hsin']; ring
    rw [hval] at hcomp
    exact hcomp.hasDerivWithinAt
  have hbref : ∀ t ∈ Set.Icc 0 (Real.pi / 2),
      ‖-(Real.sin (2 * t) * (deriv (deriv h) (Real.pi / 2 - t) + 4 * h (Real.pi / 2 - t)))‖
        ≤ (2 * M₀) * t := by
    intro t ht
    have ht1 : t ≤ Real.pi / 2 := ht.2
    have hy : Real.pi / 2 - t ∈ Set.Icc 0 (Real.pi / 2) :=
      ⟨by linarith [ht.2], by linarith [ht.1]⟩
    have hsin0 : 0 ≤ Real.sin (2 * t) :=
      Real.sin_nonneg_of_nonneg_of_le_pi (by linarith [ht.1]) (by linarith [ht1])
    have hsinle : Real.sin (2 * t) ≤ 2 * t := Real.sin_le (by linarith [ht.1])
    have hb := hM₀ (Real.pi / 2 - t) hy
    rw [Real.norm_eq_abs, abs_neg, abs_mul, abs_of_nonneg hsin0]
    calc Real.sin (2 * t) * |deriv (deriv h) (Real.pi / 2 - t) + 4 * h (Real.pi / 2 - t)|
        ≤ (2 * t) * M₀ := mul_le_mul hsinle hb (abs_nonneg _) (by linarith [ht.1])
      _ = 2 * M₀ * t := by ring
  have hhalf2 : ∀ t ∈ Set.Icc 0 (Real.pi / 2),
      ‖(fun s : ℝ => ssbW h (Real.pi / 2 - s)) t - (fun s : ℝ => ssbW h (Real.pi / 2 - s)) 0‖
        ≤ (2 * M₀) * t ^ 2 :=
    seg_second_order_bound (fun s : ℝ => ssbW h (Real.pi / 2 - s))
      (fun t => -(Real.sin (2 * t) * (deriv (deriv h) (Real.pi / 2 - t) + 4 * h (Real.pi / 2 - t))))
      (2 * M₀) (Real.pi / 2) (by positivity) (by linarith [Real.pi_pos]) hWref hbref
  have hsecond : ∀ x ∈ Set.Icc 0 (Real.pi / 2), |ssbW h x| ≤ (2 * M₀) * (Real.pi / 2 - x) ^ 2 := by
    intro x hx
    have ht : Real.pi / 2 - x ∈ Set.Icc 0 (Real.pi / 2) :=
      ⟨by linarith [hx.2], by linarith [hx.1]⟩
    have hval2 := hhalf2 (Real.pi / 2 - x) ht
    have harg : Real.pi / 2 - (Real.pi / 2 - x) = x := by ring
    simp only [harg, Real.norm_eq_abs, sub_zero] at hval2
    rw [hWpi] at hval2
    simpa using hval2
  refine ⟨2 * M₀, by positivity, ?_⟩
  intro θ hθ
  have hθIcc : θ ∈ Set.Icc 0 (Real.pi / 2) := ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩
  rcases le_total θ (Real.pi / 2 - θ) with hle | hle
  · rw [min_eq_left hle]
    exact hfirst θ hθIcc
  · rw [min_eq_right hle]
    exact hsecond θ hθIcc

/-! ## The quotient rule -/

/-- The quotient rule for `SinQ h = h / sin(2θ)`, in the form needed below: on `(0, π/2)`,
`deriv (SinQ h) θ = W h θ / sin²(2θ)`. -/
private lemma ssb_derivSinQ (h : ℝ → ℝ) (hC : ContDiffOn ℝ 2 h (Set.Icc 0 (Real.pi / 2)))
    {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    deriv (SinQ h) θ = ssbW h θ / (Real.sin (2 * θ)) ^ 2 := by
  have hsin : 0 < Real.sin (2 * θ) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2])
  have hs2 : (Real.sin (2 * θ)) ^ 2 ≠ 0 := by positivity
  have hid := (htU_interior_facts h hC).2.2.2.1 θ hθ
  have hSinQ : SinQ h = htU h := rfl
  rw [hSinQ, eq_div_iff hs2]
  simp only [ssbW]
  rw [mul_comm]
  exact hid

/-! ## The bounds on `h` and on `h'` -/

private lemma ssb_pointwise (h : ℝ → ℝ) (hsm : SmoothSlice h) (h0 : h 0 = 0)
    (hp : h (Real.pi / 2) = 0) :
    ∃ C : ℝ, 0 ≤ C ∧
      (∀ θ ∈ Set.Ioo 0 (Real.pi / 2), |h θ| ≤ C * Real.sin (2 * θ)) ∧
      (∀ θ ∈ Set.Ioo 0 (Real.pi / 2), |deriv h θ| ≤ C) := by
  have hC1 : ContDiffOn ℝ 1 h (Set.Icc 0 (Real.pi / 2)) := (hsm.of_le le_top).mono ssb_Icc_subset
  obtain ⟨C₀, hC₀0, hC₀min, hC₀d⟩ := contDiffOn_one_bounds hC1 h0 hp
  refine ⟨C₀ * (Real.pi / 2), by positivity, ?_, ?_⟩
  · intro θ hθ
    have hmin := (ssb_min_le_sin hθ).2
    calc |h θ| ≤ C₀ * min θ (Real.pi / 2 - θ) := hC₀min θ ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩
      _ ≤ C₀ * (Real.pi / 2 * Real.sin (2 * θ)) := mul_le_mul_of_nonneg_left hmin hC₀0
      _ = C₀ * (Real.pi / 2) * Real.sin (2 * θ) := by ring
  · intro θ hθ
    have h := hC₀d θ hθ
    rw [Real.norm_eq_abs] at h
    exact le_trans h (le_mul_of_one_le_right hC₀0 ssb_one_le_half_pi)

/-! ## The main statement -/

theorem SinSliceBounds (h : ℝ → ℝ) (hsm : Work.Elliptic.SmoothSlice h) (h0 : h 0 = 0)
    (hp : h (Real.pi / 2) = 0) :
    ∃ C : ℝ, 0 < C ∧
      (∀ θ ∈ Set.Ioo 0 (Real.pi / 2), |h θ| ≤ C * Real.sin (2 * θ)) ∧
      (∀ θ ∈ Set.Ioo 0 (Real.pi / 2), |deriv h θ| ≤ C) ∧
      (∀ θ ∈ Set.Ioo 0 (Real.pi / 2), |Work.Elliptic.SinQ h θ| ≤ C) ∧
      (∀ θ ∈ Set.Ioo 0 (Real.pi / 2), |deriv (Work.Elliptic.SinQ h) θ| ≤ C) := by
  obtain ⟨C₁, hC₁0, hC₁h, hC₁d⟩ := ssb_pointwise h hsm h0 hp
  obtain ⟨M, hM0, hMW⟩ := ssb_W_snd h hsm h0 hp
  have hC2 : ContDiffOn ℝ 2 h (Set.Icc 0 (Real.pi / 2)) := (hsm.of_le le_top).mono ssb_Icc_subset
  set Cm : ℝ := max 1 (max (C₁ * (Real.pi / 2)) (M * Real.pi ^ 2 / 4)) with hCm
  have hC₁le : C₁ ≤ Cm := by
    rw [hCm]
    calc C₁ ≤ C₁ * (Real.pi / 2) := le_mul_of_one_le_right hC₁0 ssb_one_le_half_pi
      _ ≤ max (C₁ * (Real.pi / 2)) (M * Real.pi ^ 2 / 4) := le_max_left _ _
      _ ≤ max 1 (max (C₁ * (Real.pi / 2)) (M * Real.pi ^ 2 / 4)) := le_max_right _ _
  have hMle : M * Real.pi ^ 2 / 4 ≤ Cm := by
    rw [hCm]
    exact le_trans (le_max_right _ _) (le_max_right _ _)
  refine ⟨Cm, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hCm]
    exact lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  · intro θ hθ
    have hsin := (ssb_min_le_sin hθ).1
    calc |h θ| ≤ C₁ * Real.sin (2 * θ) := hC₁h θ hθ
      _ ≤ Cm * Real.sin (2 * θ) := mul_le_mul_of_nonneg_right hC₁le hsin.le
  · intro θ hθ
    exact le_trans (hC₁d θ hθ) hC₁le
  · intro θ hθ
    have hsin := (ssb_min_le_sin hθ).1
    have hdiv : |SinQ h θ| = |h θ| / Real.sin (2 * θ) := by
      simp only [SinQ, abs_div, abs_of_pos hsin]
    rw [hdiv, div_le_iff₀ hsin]
    calc |h θ| ≤ C₁ * Real.sin (2 * θ) := hC₁h θ hθ
      _ ≤ Cm * Real.sin (2 * θ) := mul_le_mul_of_nonneg_right hC₁le hsin.le
  · intro θ hθ
    have hsin := (ssb_min_le_sin hθ).1
    have hs2 : 0 < (Real.sin (2 * θ)) ^ 2 := by positivity
    have hkey := ssb_derivSinQ h hC2 hθ
    have hmin0 : 0 ≤ min θ (Real.pi / 2 - θ) :=
      le_min (le_of_lt hθ.1) (by linarith [hθ.2])
    have hmin2 : (min θ (Real.pi / 2 - θ)) ^ 2 ≤ (Real.pi / 2 * Real.sin (2 * θ)) ^ 2 :=
      pow_le_pow_left₀ hmin0 (ssb_min_le_sin hθ).2 2
    have hb : |ssbW h θ| ≤ M * (Real.pi / 2 * Real.sin (2 * θ)) ^ 2 :=
      le_trans (hMW θ hθ) (mul_le_mul_of_nonneg_left hmin2 hM0)
    have hdiv : |ssbW h θ / (Real.sin (2 * θ)) ^ 2| = |ssbW h θ| / (Real.sin (2 * θ)) ^ 2 := by
      rw [abs_div, abs_of_pos hs2]
    rw [hkey, hdiv]
    calc |ssbW h θ| / (Real.sin (2 * θ)) ^ 2
        ≤ (M * (Real.pi / 2 * Real.sin (2 * θ)) ^ 2) / (Real.sin (2 * θ)) ^ 2 :=
          div_le_div_of_nonneg_right hb hs2.le
      _ = M * Real.pi ^ 2 / 4 := by
          rw [show M * (Real.pi / 2 * Real.sin (2 * θ)) ^ 2
                = (M * (Real.pi ^ 2 / 4)) * (Real.sin (2 * θ)) ^ 2 by ring]
          rw [mul_div_cancel_right₀ _ (ne_of_gt hs2)]
          ring
      _ ≤ Cm := hMle

end Work.Elliptic
end
end
-- ===== merged: Submission.Work.Elliptic.SliceBddBounds =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology Interval
open MeasureTheory Set Filter

namespace Work.Elliptic

set_option autoImplicit false


private lemma abs_add_sub_le (a b c : ℝ) : |a + b - c| ≤ |a| + |b| + |c| := by
  calc |a + b - c| = |(a + b) + (-c)| := by ring_nf
    _ ≤ |a + b| + |-c| := abs_add_le _ _
    _ = |a + b| + |c| := by rw [abs_neg]
    _ ≤ (|a| + |b|) + |c| := by linarith [abs_add_le a b]
    _ = |a| + |b| + |c| := by ring


end Work.Elliptic
end
end
-- ===== merged: Submission.Work.Elliptic.WtoH_Angular =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.Elliptic

open MeasureTheory

set_option autoImplicit false

/-- The angular part of the transfer estimate: on `Iθ` the sum of the two
weighted profiles with nonnegative coefficients is bounded by `A · 10^4 + B · 700`,
uniformly in `α ∈ (0,1]`. -/
theorem WtoH_Angular {α A B : ℝ} (hα : 0 < α) (hα1 : α ≤ 1)
    (hA : 0 ≤ A) (hB : 0 ≤ B) :
    ∫ θ in Work.Spaces.Iθ, (A * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))
        + B * ((α + Real.sin (2 * θ)) ^ 2
            * (Real.sin (2 * θ)) ^ (2 * α / 5 - Work.Spaces.gam α)))
      ≤ A * 10 ^ 4 + B * 700 := by
  -- The exponent `-η` lies in `(-1, 0)`, so `sin(2θ)^{-η}` is integrable on `Iθ`.
  have hpe : (-1 : ℝ) < -(Work.Spaces.eta) := by rw [Work.Spaces.eta]; norm_num
  have hpe0 : -(Work.Spaces.eta) ≤ 0 := by rw [Work.Spaces.eta]; norm_num
  obtain ⟨hfint, hfb⟩ := Work.Spaces.sin_two_rpow (-(Work.Spaces.eta)) hpe hpe0
  -- Integrability of the two summands of the integrand.
  have hfint' : IntegrableOn (fun θ : ℝ => A * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))
      Work.Spaces.Iθ := hfint.const_mul A
  have hgint : IntegrableOn (fun θ : ℝ => B * ((α + Real.sin (2 * θ)) ^ 2
      * (Real.sin (2 * θ)) ^ (2 * α / 5 - Work.Spaces.gam α))) Work.Spaces.Iθ :=
    (Work.Spaces.integrableOn_angular_weight' hα hα1).const_mul B
  -- The two `α`-free quadrature bounds: `100 / (-η + 1) = 10^4` and `700`.
  have hfb' : ∫ θ in Work.Spaces.Iθ, (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) ≤ 10 ^ 4 := by
    refine le_trans hfb ?_
    rw [Work.Spaces.eta]
    norm_num
  have hgb : ∫ θ in Work.Spaces.Iθ, ((α + Real.sin (2 * θ)) ^ 2
      * (Real.sin (2 * θ)) ^ (2 * α / 5 - Work.Spaces.gam α)) ≤ 700 :=
    Work.Spaces.angular_weight_integral_bound' hα hα1
  calc ∫ θ in Work.Spaces.Iθ, (A * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))
        + B * ((α + Real.sin (2 * θ)) ^ 2
            * (Real.sin (2 * θ)) ^ (2 * α / 5 - Work.Spaces.gam α)))
      = A * (∫ θ in Work.Spaces.Iθ, (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))
        + B * (∫ θ in Work.Spaces.Iθ, ((α + Real.sin (2 * θ)) ^ 2
            * (Real.sin (2 * θ)) ^ (2 * α / 5 - Work.Spaces.gam α))) := by
        rw [integral_add hfint' hgint, integral_const_mul, integral_const_mul]
    _ ≤ A * 10 ^ 4 + B * 700 := by
        have h1 := mul_le_mul_of_nonneg_left hfb' hA
        have h2 := mul_le_mul_of_nonneg_left hgb hB
        linarith

end Work.Elliptic
end
-- ===== merged: Submission.Work.Elliptic.WtoH_IntZ =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.Elliptic

open MeasureTheory Filter
open scoped Real Topology

/-- The derivative of `z ↦ -(1+z)⁻¹` is the integrand `z ↦ 1/(1+z)²`, which is
nonnegative, so `1/(1+z)²` is integrable on `Iz = [0,∞)` and its integral is `1 ≤ 2`. -/
theorem WtoH_IntZ :
    MeasureTheory.IntegrableOn (fun z : ℝ => 1 / (1 + z) ^ 2) Work.Spaces.Iz ∧
      ∫ z in Work.Spaces.Iz, 1 / (1 + z) ^ 2 ≤ 2 := by
  have hderiv : ∀ x ∈ Set.Ici (0:ℝ),
      HasDerivAt (fun x : ℝ => -((1 + x)⁻¹)) (1/(1+x)^2 : ℝ) x := by
    intro x hx
    have h1 : HasDerivAt (fun x : ℝ => 1 + x) 1 x := by
      simpa using (hasDerivAt_id x).const_add 1
    have hx0 : (1 + x) ≠ 0 := by have : (0:ℝ) ≤ x := hx; linarith
    have h2 := (h1.inv hx0).neg
    convert h2 using 1
    ring
  have hpos : ∀ x ∈ Set.Ioi (0:ℝ), 0 ≤ (1/(1+x)^2 : ℝ) := by
    intro x hx
    apply div_nonneg (by norm_num)
    positivity
  have htend : Tendsto (fun x : ℝ => -((1 + x)⁻¹)) atTop (𝓝 0) := by
    have h : Tendsto (fun x : ℝ => 1 + x) atTop atTop :=
      tendsto_atTop_add_const_left _ (1:ℝ) tendsto_id
    simpa using (tendsto_inv_atTop_zero (𝕜 := ℝ)).comp h |>.neg
  have hIntIoi : IntegrableOn (fun x : ℝ => 1/(1+x)^2) (Set.Ioi (0:ℝ)) :=
    integrableOn_Ioi_deriv_of_nonneg' hderiv hpos htend
  have hValIoi : ∫ x in Set.Ioi (0:ℝ), (1/(1+x)^2 : ℝ) = 1 := by
    have := integral_Ioi_of_hasDerivAt_of_nonneg' (a := (0:ℝ)) hderiv hpos htend
    simpa using this
  constructor
  · rw [Work.Spaces.Iz]
    exact (integrableOn_Ici_iff_integrableOn_Ioi
      (f := fun z : ℝ => 1/(1+z)^2) (b := (0:ℝ))).mpr hIntIoi
  · rw [Work.Spaces.Iz, integral_Ici_eq_integral_Ioi, hValIoi]
    norm_num

end Work.Elliptic
end
-- ===== merged: Submission.Work.Elliptic.WtoH_Mixed_g_eq =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.Elliptic

set_option linter.unusedVariables false

/-- `D_θ^i` of `g · f` equals `g · D_θ^i f` for the factor `g(z) = (z+1)³/z²`, which is
`(z+1)³ · divZ2 f` as a function of `(z,θ)`; the factor is constant in `θ`, so it pulls out
of `D_θ^i`. -/
theorem WtoH_Mixed_g_eq {f : ℝ → ℝ → ℝ} (i : ℕ) {z θ : ℝ} (hz : z ≠ 0) :
    Work.Spaces.DthIter i (fun z θ => (z + 1) ^ 3 / z ^ 2 * f z θ) z θ
      = (z + 1) ^ 3 * Work.Spaces.DthIter i (Work.Elliptic.divZ2 f) z θ := by
  rw [g_divZ2_eq, DthIter_const_mul]

end Work.Elliptic
end
-- ===== merged: Submission.Work.Elliptic.WtoH_Radial =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.Elliptic

open Work.Spaces

/-! ## A helper: expansion of `∂_z^m f` through `f = z² · divZ2 f`

For `SmoothNbhd f`, `z > 0` and `m ≤ 4`, the `m`-th plain `z`-derivative of `f` is obtained
from `f = z² · (f/z²)` (valid near `z ≠ 0`) and Leibniz; only `z²`, `2z`, `2` contribute. -/


end Work.Elliptic
end
-- ===== merged: Submission.Work.Elliptic.WtoW_f_zero =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.Elliptic

set_option autoImplicit false


end Work.Elliptic
end
-- ===== merged: Submission.Work.Elliptic.division_by_z =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology ContDiff
open MeasureTheory Set Filter

namespace Work.Elliptic

set_option autoImplicit false
set_option maxHeartbeats 1000000

/-! ## The `z`-slice calculus -/


/-! ## The Taylor quotient of a function of one variable -/







/-! ## The jump lemma -/



/-! ## The main estimate -/




/-! ## The main theorem -/




end Work.Elliptic
end
end
-- ===== merged: Submission.Work.Elliptic.hardy_two_regular =====
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

/-- If `|a| ≤ C` with `0 ≤ C` then `a ^ 2 ≤ C ^ 2`. -/
private lemma sq_le_sq_of_abs_le {a C : ℝ} (hC : 0 ≤ C) (h : |a| ≤ C) : a ^ 2 ≤ C ^ 2 := by
  rw [sq_le_sq, abs_of_nonneg hC]
  exact h


end Work.Elliptic
end
end
-- ===== merged: Submission.Work.Elliptic.pdRR_add_pdZZ_comp_polar =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

set_option autoImplicit false
set_option linter.unusedSimpArgs false

/-!
# The polar Laplacian identity for `G(r,z) = F(ρ(r,z), θ(r,z))`

With `ρ(r,z) = √(r²+z²)` and `θ(r,z) = arctan(z/r)` (`r > 0`), the Cartesian Laplacian of the
composite `G = F ∘ (ρ,θ)` is the "polar" Laplacian of `F`:

`∂_rr G + ∂_zz G = F_{ρρ} + F_ρ/ρ + F_{θθ}/ρ²`.

The proof expands the two second derivatives by the chain rule.  Every occurrence of `cos θ` and
`sin θ` is rewritten as `r/ρ` and `z/ρ`, and the two expansions are added; the mixed terms
`F_{ρθ}, F_{θρ}` and the first order term `F_θ` cancel, while `ρ_r² + ρ_z² = 1`,
`θ_r² + θ_z² = 1/ρ²` and `ρ_rr + ρ_zz = 1/ρ` give the remaining coefficients.
-/

namespace Work.Elliptic

open Work.Cyl
open Filter
open scoped Topology

/-! ## Derivatives of the polar coordinate functions in the radial variable -/

/-- `r ↦ ρ(r,z) = √(r²+z²)` has derivative `r/ρ` in the radial variable. -/
theorem hasDerivAt_rhoP_fst' (r z : ℝ) (hr : 0 < r) :
    HasDerivAt (fun r' : ℝ => rhoP r' z) (r / rhoP r z) r := by
  have hsq : HasDerivAt (fun r' : ℝ => r' ^ 2 + z ^ 2) (2 * r) r := by
    simpa using ((hasDerivAt_pow 2 r).add_const (z ^ 2))
  have hne : r ^ 2 + z ^ 2 ≠ 0 := by positivity
  have h := hsq.sqrt hne
  have hval : (2 * r) / (2 * Real.sqrt (r ^ 2 + z ^ 2)) = r / rhoP r z := by
    rw [rhoP]; field_simp
  rw [hval] at h
  exact h

/-- `r ↦ θ(r,z) = arctan(z/r)` has derivative `-z/ρ²` in the radial variable. -/
theorem hasDerivAt_thetaP_fst' (r z : ℝ) (hr : 0 < r) :
    HasDerivAt (fun r' : ℝ => thetaP r' z) (-z / rhoP r z ^ 2) r := by
  have hdiv : HasDerivAt (fun r' : ℝ => z / r') (-z / r ^ 2) r := by
    have h := (hasDerivAt_const (x := r) z).div (hasDerivAt_id r) (ne_of_gt hr)
    have hfun : ((fun x : ℝ => z) / id : ℝ → ℝ) = fun r' => z / r' := by
      funext x; simp [Pi.div_apply]
    rw [hfun] at h
    convert h using 1
    simp
  have h := hdiv.arctan
  have hfun : (fun r' : ℝ => thetaP r' z) = fun r' => Real.arctan (z / r') := by
    funext r'; rw [thetaP]
  rw [hfun]
  convert h using 1
  rw [rhoP]
  field_simp
  rw [Real.sq_sqrt (by positivity)]

/-! ## Eventual differentiability of `F` along a continuous curve -/

/-- If `F` is `C²` at `(R t₀, Z t₀)` and `R, Z` are continuous at `t₀`, then `F` is differentiable
at `(R s, Z s)` for all `s` near `t₀`. -/
theorem eventually_diffAt2_comp (F : ℝ → ℝ → ℝ) (R Z : ℝ → ℝ) (t₀ : ℝ)
    (hF : ContDiffAt ℝ 2 (Function.uncurry F) (R t₀, Z t₀))
    (hR : ContinuousAt R t₀) (hZ : ContinuousAt Z t₀) :
    ∀ᶠ s in 𝓝 t₀, DiffAt2 F (R s) (Z s) := by
  have h1 : ∀ᶠ p : ℝ × ℝ in 𝓝 (R t₀, Z t₀), DifferentiableAt ℝ (Function.uncurry F) p := by
    obtain ⟨u, hu_open, hu_mem, hu⟩ := hF.contDiffOn' le_rfl (fun h => by simp at h)
    have hu' : ContDiffOn ℝ 2 (Function.uncurry F) u := by simpa using hu
    filter_upwards [hu_open.mem_nhds hu_mem] with p hp
    exact (hu'.differentiableOn (by norm_num)).differentiableAt (hu_open.mem_nhds hp)
  have hcont : ContinuousAt (fun s : ℝ => (R s, Z s)) t₀ := hR.prodMk hZ
  exact hcont.eventually h1

/-! ## The two second-order chain rules -/

/-- Chain rule in the radial variable: differentiating
`r ↦ cos θ(r,z) · F_ρ - (sin θ(r,z)/ρ(r,z)) · F_θ`
(the expression for `∂_r (F ∘ (ρ,θ))` given by `pdR_comp_polar_rho`). -/
theorem deriv_pdR_comp_polar (F : ℝ → ℝ → ℝ) (r z : ℝ) (hr : 0 < r)
    (hpdR : DiffAt2 (pdR F) (rhoP r z) (thetaP r z))
    (hpdZ : DiffAt2 (pdZ F) (rhoP r z) (thetaP r z)) :
    deriv (fun s => Real.cos (thetaP s z) * pdR F (rhoP s z) (thetaP s z)
             - Real.sin (thetaP s z) / rhoP s z * pdZ F (rhoP s z) (thetaP s z)) r
      = z^2/(rhoP r z)^3 * pdR F (rhoP r z) (thetaP r z)
        + r^2/(rhoP r z)^2 * pdRR F (rhoP r z) (thetaP r z)
        - r*z/(rhoP r z)^3 * pdZR F (rhoP r z) (thetaP r z)
        + 2*r*z/(rhoP r z)^4 * pdZ F (rhoP r z) (thetaP r z)
        - r*z/(rhoP r z)^3 * pdRZ F (rhoP r z) (thetaP r z)
        + z^2/(rhoP r z)^4 * pdZZ F (rhoP r z) (thetaP r z) := by
  have hρne : rhoP r z ≠ 0 := rhoP_ne_zero hr z
  have hρ : HasDerivAt (fun s : ℝ => rhoP s z) (r / rhoP r z) r :=
    hasDerivAt_rhoP_fst' r z hr
  have hθ : HasDerivAt (fun s : ℝ => thetaP s z) (-z / rhoP r z ^ 2) r :=
    hasDerivAt_thetaP_fst' r z hr
  have hc : HasDerivAt (fun s : ℝ => Real.cos (thetaP s z))
      (Real.sin (thetaP r z) * (z / rhoP r z ^ 2)) r := by
    have h := (Real.hasDerivAt_cos (thetaP r z)).comp r hθ
    convert h using 1
    · rfl
    · ring
  have hs : HasDerivAt (fun s : ℝ => Real.sin (thetaP s z))
      (-Real.cos (thetaP r z) * (z / rhoP r z ^ 2)) r := by
    have h := (Real.hasDerivAt_sin (thetaP r z)).comp r hθ
    convert h using 1
    · rfl
    · ring
  have hP : HasDerivAt (fun s : ℝ => pdR F (rhoP s z) (thetaP s z))
      (pdRR F (rhoP r z) (thetaP r z) * (r / rhoP r z)
        + pdZR F (rhoP r z) (thetaP r z) * (-z / rhoP r z ^ 2)) r :=
    hasDerivAt_comp_two (pdR F) (fun s : ℝ => rhoP s z) (fun s : ℝ => thetaP s z)
      (r / rhoP r z) (-z / rhoP r z ^ 2) r hpdR hρ hθ
  have hQ : HasDerivAt (fun s : ℝ => pdZ F (rhoP s z) (thetaP s z))
      (pdRZ F (rhoP r z) (thetaP r z) * (r / rhoP r z)
        + pdZZ F (rhoP r z) (thetaP r z) * (-z / rhoP r z ^ 2)) r :=
    hasDerivAt_comp_two (pdZ F) (fun s : ℝ => rhoP s z) (fun s : ℝ => thetaP s z)
      (r / rhoP r z) (-z / rhoP r z ^ 2) r hpdZ hρ hθ
  have hΦ : HasDerivAt (fun s => Real.cos (thetaP s z) * pdR F (rhoP s z) (thetaP s z)
             - Real.sin (thetaP s z) / rhoP s z * pdZ F (rhoP s z) (thetaP s z)) _ r :=
    (hc.mul hP).sub ((hs.div hρ hρne).mul hQ)
  rw [hΦ.deriv]
  simp only [Pi.div_apply, Function.comp_apply]
  rw [cos_thetaP hr z, sin_thetaP hr z]
  field_simp
  ring

/-- Chain rule in the axial variable: differentiating
`z ↦ sin θ(r,z) · F_ρ + (cos θ(r,z)/ρ(r,z)) · F_θ`
(the expression for `∂_z (F ∘ (ρ,θ))` given by `pdZ_comp_polar_rho`). -/
theorem deriv_pdZ_comp_polar (F : ℝ → ℝ → ℝ) (r z : ℝ) (hr : 0 < r)
    (hpdR : DiffAt2 (pdR F) (rhoP r z) (thetaP r z))
    (hpdZ : DiffAt2 (pdZ F) (rhoP r z) (thetaP r z)) :
    deriv (fun t => Real.sin (thetaP r t) * pdR F (rhoP r t) (thetaP r t)
             + Real.cos (thetaP r t) / rhoP r t * pdZ F (rhoP r t) (thetaP r t)) z
      = r^2/(rhoP r z)^3 * pdR F (rhoP r z) (thetaP r z)
        + z^2/(rhoP r z)^2 * pdRR F (rhoP r z) (thetaP r z)
        + r*z/(rhoP r z)^3 * pdZR F (rhoP r z) (thetaP r z)
        - 2*r*z/(rhoP r z)^4 * pdZ F (rhoP r z) (thetaP r z)
        + r*z/(rhoP r z)^3 * pdRZ F (rhoP r z) (thetaP r z)
        + r^2/(rhoP r z)^4 * pdZZ F (rhoP r z) (thetaP r z) := by
  have hρne : rhoP r z ≠ 0 := rhoP_ne_zero hr z
  have hρ : HasDerivAt (fun t : ℝ => rhoP r t) (z / rhoP r z) z := hasDerivAt_rhoP_snd r z hr
  have hθ : HasDerivAt (fun t : ℝ => thetaP r t) (r / rhoP r z ^ 2) z :=
    hasDerivAt_thetaP_snd r z hr
  have hs := (Real.hasDerivAt_sin (thetaP r z)).comp z hθ
  have hc := (Real.hasDerivAt_cos (thetaP r z)).comp z hθ
  have hP : HasDerivAt (fun t : ℝ => pdR F (rhoP r t) (thetaP r t))
      (pdRR F (rhoP r z) (thetaP r z) * (z / rhoP r z)
        + pdZR F (rhoP r z) (thetaP r z) * (r / rhoP r z ^ 2)) z :=
    hasDerivAt_comp_two (pdR F) (fun t : ℝ => rhoP r t) (fun t : ℝ => thetaP r t)
      (z / rhoP r z) (r / rhoP r z ^ 2) z hpdR hρ hθ
  have hQ : HasDerivAt (fun t : ℝ => pdZ F (rhoP r t) (thetaP r t))
      (pdRZ F (rhoP r z) (thetaP r z) * (z / rhoP r z)
        + pdZZ F (rhoP r z) (thetaP r z) * (r / rhoP r z ^ 2)) z :=
    hasDerivAt_comp_two (pdZ F) (fun t : ℝ => rhoP r t) (fun t : ℝ => thetaP r t)
      (z / rhoP r z) (r / rhoP r z ^ 2) z hpdZ hρ hθ
  have hΦ : HasDerivAt (fun t => Real.sin (thetaP r t) * pdR F (rhoP r t) (thetaP r t)
             + Real.cos (thetaP r t) / rhoP r t * pdZ F (rhoP r t) (thetaP r t)) _ z :=
    (hs.mul hP).add ((hc.div hρ hρne).mul hQ)
  rw [hΦ.deriv]
  simp only [Pi.div_apply, Function.comp_apply]
  rw [cos_thetaP hr z, sin_thetaP hr z]
  field_simp
  ring

/-! ## The second derivatives of `G = F ∘ (ρ,θ)` -/

/-- `∂_rr (F ∘ (ρ,θ))` expanded by the chain rule. -/
theorem pdRR_comp_polar (F : ℝ → ℝ → ℝ) (r z : ℝ) (hr : 0 < r)
    (hF : ContDiffAt ℝ 2 (Function.uncurry F) (rhoP r z, thetaP r z))
    (hpdR : DiffAt2 (pdR F) (rhoP r z) (thetaP r z))
    (hpdZ : DiffAt2 (pdZ F) (rhoP r z) (thetaP r z)) :
    pdRR (fun r' z' => F (rhoP r' z') (thetaP r' z')) r z
      = z^2/(rhoP r z)^3 * pdR F (rhoP r z) (thetaP r z)
        + r^2/(rhoP r z)^2 * pdRR F (rhoP r z) (thetaP r z)
        - r*z/(rhoP r z)^3 * pdZR F (rhoP r z) (thetaP r z)
        + 2*r*z/(rhoP r z)^4 * pdZ F (rhoP r z) (thetaP r z)
        - r*z/(rhoP r z)^3 * pdRZ F (rhoP r z) (thetaP r z)
        + z^2/(rhoP r z)^4 * pdZZ F (rhoP r z) (thetaP r z) := by
  have hev : (fun s => pdR (fun r' z' => F (rhoP r' z') (thetaP r' z')) s z)
      =ᶠ[𝓝 r] (fun s => Real.cos (thetaP s z) * pdR F (rhoP s z) (thetaP s z)
             - Real.sin (thetaP s z) / rhoP s z * pdZ F (rhoP s z) (thetaP s z)) := by
    filter_upwards [eventually_diffAt2_comp F (fun s => rhoP s z) (fun s => thetaP s z) r hF
        (hasDerivAt_rhoP_fst' r z hr).continuousAt
        (hasDerivAt_thetaP_fst' r z hr).continuousAt,
      eventually_gt_nhds hr] with s hsF hsr
    exact pdR_comp_polar_rho F s z hsr hsF
  show deriv (fun r' => pdR (fun r' z' => F (rhoP r' z') (thetaP r' z')) r' z) r = _
  rw [hev.deriv_eq]
  exact deriv_pdR_comp_polar F r z hr hpdR hpdZ

/-- `∂_zz (F ∘ (ρ,θ))` expanded by the chain rule. -/
theorem pdZZ_comp_polar (F : ℝ → ℝ → ℝ) (r z : ℝ) (hr : 0 < r)
    (hF : ContDiffAt ℝ 2 (Function.uncurry F) (rhoP r z, thetaP r z))
    (hpdR : DiffAt2 (pdR F) (rhoP r z) (thetaP r z))
    (hpdZ : DiffAt2 (pdZ F) (rhoP r z) (thetaP r z)) :
    pdZZ (fun r' z' => F (rhoP r' z') (thetaP r' z')) r z
      = r^2/(rhoP r z)^3 * pdR F (rhoP r z) (thetaP r z)
        + z^2/(rhoP r z)^2 * pdRR F (rhoP r z) (thetaP r z)
        + r*z/(rhoP r z)^3 * pdZR F (rhoP r z) (thetaP r z)
        - 2*r*z/(rhoP r z)^4 * pdZ F (rhoP r z) (thetaP r z)
        + r*z/(rhoP r z)^3 * pdRZ F (rhoP r z) (thetaP r z)
        + r^2/(rhoP r z)^4 * pdZZ F (rhoP r z) (thetaP r z) := by
  have hev : (fun s => pdZ (fun r' z' => F (rhoP r' z') (thetaP r' z')) r s)
      =ᶠ[𝓝 z] (fun t => Real.sin (thetaP r t) * pdR F (rhoP r t) (thetaP r t)
             + Real.cos (thetaP r t) / rhoP r t * pdZ F (rhoP r t) (thetaP r t)) := by
    filter_upwards [eventually_diffAt2_comp F (fun t => rhoP r t) (fun t => thetaP r t) z hF
        (hasDerivAt_rhoP_snd r z hr).continuousAt
        (hasDerivAt_thetaP_snd r z hr).continuousAt] with t htF
    exact pdZ_comp_polar_rho F r t hr htF
  show deriv (fun z' => pdZ (fun r' z' => F (rhoP r' z') (thetaP r' z')) r z') z = _
  rw [hev.deriv_eq]
  exact deriv_pdZ_comp_polar F r z hr hpdR hpdZ

/-! ## The algebraic step -/

/-- The two second-order expansions add up to the polar Laplacian of `F`. -/
theorem pdRR_add_pdZZ_expansions (A B C D E G r z ρ : ℝ) (hρ : ρ ≠ 0) (h2 : ρ ^ 2 = r ^ 2 + z ^ 2) :
    (z^2/ρ^3 * A + r^2/ρ^2 * B - r*z/ρ^3 * C + 2*r*z/ρ^4 * D - r*z/ρ^3 * E + z^2/ρ^4 * G)
      + (r^2/ρ^3 * A + z^2/ρ^2 * B + r*z/ρ^3 * C - 2*r*z/ρ^4 * D + r*z/ρ^3 * E + r^2/ρ^4 * G)
      = B + A/ρ + G/ρ^2 := by
  field_simp
  rw [h2]
  ring

theorem pdRR_add_pdZZ_comp_polar (F : ℝ → ℝ → ℝ) (r z : ℝ) (hr : 0 < r)
    (hF : ContDiffAt ℝ 2 (Function.uncurry F) (Work.Cyl.rhoP r z, Work.Cyl.thetaP r z))
    (hpdR : Work.Cyl.DiffAt2 (Work.Cyl.pdR F) (Work.Cyl.rhoP r z) (Work.Cyl.thetaP r z))
    (hpdZ : Work.Cyl.DiffAt2 (Work.Cyl.pdZ F) (Work.Cyl.rhoP r z) (Work.Cyl.thetaP r z)) :
    Work.Cyl.pdRR (fun r' z' => F (Work.Cyl.rhoP r' z') (Work.Cyl.thetaP r' z')) r z
      + Work.Cyl.pdZZ (fun r' z' => F (Work.Cyl.rhoP r' z') (Work.Cyl.thetaP r' z')) r z
      = Work.Cyl.pdRR F (Work.Cyl.rhoP r z) (Work.Cyl.thetaP r z)
        + Work.Cyl.pdR F (Work.Cyl.rhoP r z) (Work.Cyl.thetaP r z) / Work.Cyl.rhoP r z
        + Work.Cyl.pdZZ F (Work.Cyl.rhoP r z) (Work.Cyl.thetaP r z) / (Work.Cyl.rhoP r z) ^ 2 := by
  rw [pdRR_comp_polar F r z hr hF hpdR hpdZ, pdZZ_comp_polar F r z hr hF hpdR hpdZ]
  exact pdRR_add_pdZZ_expansions (pdR F (rhoP r z) (thetaP r z)) (pdRR F (rhoP r z) (thetaP r z))
    (pdZR F (rhoP r z) (thetaP r z)) (pdZ F (rhoP r z) (thetaP r z))
    (pdRZ F (rhoP r z) (thetaP r z)) (pdZZ F (rhoP r z) (thetaP r z)) r z (rhoP r z)
    (rhoP_ne_zero hr z) (rhoP_sq r z)

end Work.Elliptic
end
-- ===== merged: Submission.Work.Elliptic.pdRR_mul_pow_rpow =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The second radial derivative of `r ↦ r² Ψ (r^α, θ)`

This is the second-order companion of `Work.Elliptic.first_derivs_mul_pow_rpow`: whereas that
lemma computes `∂_r` and `∂_{x₃}` (first and second axial) of `(r,z) ↦ r² Ψ(r^α,z)`, here we
compute its *second radial derivative* at a point `(ρ, θ)` with `ρ > 0`:

`∂_rr [r² Ψ(r^α,θ)] = 2 Ψ(ρ^α,θ) + α(α+3) ρ^α ∂_RΨ(ρ^α,θ) + α² ρ^{2α} ∂_RRΨ(ρ^α,θ)`.

The formula is the `∂_rr` analogue of the polar chain rule: with `R = ρ^α`, `r = ρ`, one has
`∂_rr [r²Ψ] = 2Ψ + 2r·(αR/r)∂_RΨ + ...`, and the coefficient of `∂_RΨ` collects to `α(α+3)ρ^α`
while that of `∂_RRΨ` is `α²ρ^{2α}`.

## Strategy

The proof follows exactly the pattern of `Work.Elliptic.pdRR_comp_polar`:

* `pdRR F ρ θ = deriv (fun s ↦ pdR F s θ) ρ` by definition;
* on a neighbourhood of `ρ` the first radial derivative is given by the *first-order*
  formula of `first_derivs_mul_pow_rpow` (which only needs `ContDiffAt ℝ 2` of `uncurry Ψ`
  at the moving point `(s^α, θ)`; this holds eventually because `ContDiffAt` is a local
  property and `s ↦ s^α` is continuous at `ρ > 0`);
* the derivative of the resulting explicit expression is computed with the chain rule for
  `s ↦ Ψ(s^α)θ` and `s ↦ ∂_RΨ(s^α)θ`, which requires `DiffAt2 Ψ` resp. `DiffAt2 (pdR Ψ)`
  at `(ρ^α, θ)` (the latter is the hypothesis `hpdR`);
* the resulting value is matched to the target with the `rpow` identities
  `ρ = ρ^1`, `ρ^{α+1} = ρ^α·ρ`, `ρ^{α-1} = ρ^α/ρ`, `ρ^{2α} = ρ^α·ρ^α`.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

open Filter

namespace Work.Elliptic

/-- If `F` is `C²` at `(R t₀, Z t₀)` and `R, Z` are continuous at `t₀`, then `F` is `C²` at
`(R s, Z s)` for all `s` near `t₀`.  (The `ContDiffAt` companion of
`Work.Elliptic.eventually_diffAt2_comp`.) -/
theorem eventually_contDiffAt_comp (F : ℝ × ℝ → ℝ) (R Z : ℝ → ℝ) (t₀ : ℝ)
    (hF : ContDiffAt ℝ 2 F (R t₀, Z t₀)) (hR : ContinuousAt R t₀) (hZ : ContinuousAt Z t₀) :
    ∀ᶠ s in nhds t₀, ContDiffAt ℝ 2 F (R s, Z s) := by
  obtain ⟨u, hu, huF⟩ := hF.contDiffOn le_rfl (by norm_num)
  obtain ⟨v, hvsub, hvopen, hvmem⟩ := mem_nhds_iff.mp hu
  have hcont : ContinuousAt (fun s : ℝ => (R s, Z s)) t₀ := hR.prodMk hZ
  filter_upwards [hcont.preimage_mem_nhds (hvopen.mem_nhds hvmem)] with s hs
  exact (huF.mono hvsub).contDiffAt (hvopen.mem_nhds hs)

theorem pdRR_mul_pow_rpow (Ψ : ℝ → ℝ → ℝ) (α ρ θ : ℝ) (hρ : 0 < ρ)
    (hΨ : ContDiffAt ℝ 2 (Function.uncurry Ψ) (ρ ^ α, θ))
    (hpdR : Work.Cyl.DiffAt2 (Work.Cyl.pdR Ψ) (ρ ^ α) θ) :
    Work.Cyl.pdRR (fun p q => p ^ 2 * Ψ (p ^ α) q) ρ θ
      = 2 * Ψ (ρ ^ α) θ + α * (α + 3) * ρ ^ α * Work.Cyl.pdR Ψ (ρ ^ α) θ
        + α ^ 2 * ρ ^ (2 * α) * Work.Cyl.pdRR Ψ (ρ ^ α) θ := by
  have hρne : ρ ≠ 0 := ne_of_gt hρ
  -- `uncurry Ψ` is `C²` at `(s^α, θ)` for all `s` near `ρ`
  have hΨev : ∀ᶠ s in nhds ρ, ContDiffAt ℝ 2 (Function.uncurry Ψ) (s ^ α, θ) :=
    eventually_contDiffAt_comp (Function.uncurry Ψ) (fun s => s ^ α) (fun _ => θ) ρ hΨ
      (Real.continuousAt_rpow_const ρ α (Or.inl hρne)) continuousAt_const
  -- the first radial derivative is given by `first_derivs_mul_pow_rpow` near `ρ`
  have hev : (fun s => Work.Cyl.pdR (fun p q => p ^ 2 * Ψ (p ^ α) q) s θ)
      =ᶠ[nhds ρ] (fun s => 2 * s * Ψ (s ^ α) θ
        + α * s ^ (α + 1) * Work.Cyl.pdR Ψ (s ^ α) θ) := by
    filter_upwards [hΨev, eventually_gt_nhds hρ] with s hsF hs
    exact (first_derivs_mul_pow_rpow Ψ α s θ hs hsF).1
  rw [Work.Cyl.pdRR, hev.deriv_eq]
  -- first derivatives of the two slices `u ↦ Ψ u θ` and `u ↦ ∂_RΨ u θ` at `ρ^α`
  have hH : HasDerivAt (fun u : ℝ => Ψ u θ) (Work.Cyl.pdR Ψ (ρ ^ α) θ) (ρ ^ α) := by
    have hd : DifferentiableAt ℝ (fun u : ℝ => Ψ u θ) (ρ ^ α) :=
      Work.Cyl.differentiableAt_slice_fst Ψ (ρ ^ α) θ (hΨ.differentiableAt (by decide))
    simpa only [Work.Cyl.pdR] using hd.hasDerivAt
  have hK : HasDerivAt (fun u : ℝ => Work.Cyl.pdR Ψ u θ) (Work.Cyl.pdRR Ψ (ρ ^ α) θ) (ρ ^ α) := by
    have hd : DifferentiableAt ℝ (fun u : ℝ => Work.Cyl.pdR Ψ u θ) (ρ ^ α) :=
      Work.Cyl.differentiableAt_slice_fst (Work.Cyl.pdR Ψ) (ρ ^ α) θ hpdR
    simpa only [Work.Cyl.pdRR] using hd.hasDerivAt
  -- derivatives of the powers `s ↦ s^α`, `s ↦ s^{α+1}` at `ρ`
  have hpow₁ : HasDerivAt (fun s : ℝ => s ^ α) (α * ρ ^ (α - 1)) ρ :=
    Real.hasDerivAt_rpow_const (Or.inl hρne)
  have hpow₂ : HasDerivAt (fun s : ℝ => s ^ (α + 1)) ((α + 1) * ρ ^ α) ρ := by
    have h := Real.hasDerivAt_rpow_const (x := ρ) (p := α + 1) (Or.inl hρne)
    rw [show α + 1 - 1 = α by ring] at h
    exact h
  -- chain rule for the two composed slices
  have hHA : HasDerivAt (fun s : ℝ => Ψ (s ^ α) θ)
      (Work.Cyl.pdR Ψ (ρ ^ α) θ * (α * ρ ^ (α - 1))) ρ := by
    have h := hH.comp ρ hpow₁
    exact h
  have hKA : HasDerivAt (fun s : ℝ => Work.Cyl.pdR Ψ (s ^ α) θ)
      (Work.Cyl.pdRR Ψ (ρ ^ α) θ * (α * ρ ^ (α - 1))) ρ := by
    have h := hK.comp ρ hpow₁
    exact h
  -- the two summands of the explicit expression
  have hA : HasDerivAt (fun s : ℝ => 2 * s * Ψ (s ^ α) θ)
      ((2 * 1) * Ψ (ρ ^ α) θ
        + (2 * ρ) * (Work.Cyl.pdR Ψ (ρ ^ α) θ * (α * ρ ^ (α - 1)))) ρ := by
    have h := ((hasDerivAt_id ρ).const_mul 2).mul hHA
    convert h using 1 <;> (try funext s) <;> simp only [Pi.mul_apply, id] <;> ring
  have hB : HasDerivAt (fun s : ℝ => α * s ^ (α + 1) * Work.Cyl.pdR Ψ (s ^ α) θ)
      ((α * ((α + 1) * ρ ^ α)) * Work.Cyl.pdR Ψ (ρ ^ α) θ
        + (α * ρ ^ (α + 1)) * (Work.Cyl.pdRR Ψ (ρ ^ α) θ * (α * ρ ^ (α - 1)))) ρ := by
    have h := (hpow₂.const_mul α).mul hKA
    convert h using 1 <;> (try funext s) <;> simp only [Pi.mul_apply, id] <;> ring
  -- combine and read off the derivative
  have hg : HasDerivAt (fun s : ℝ => 2 * s * Ψ (s ^ α) θ
        + α * s ^ (α + 1) * Work.Cyl.pdR Ψ (s ^ α) θ) _ ρ := hA.add hB
  rw [hg.deriv]
  -- algebra: rewrite the remaining `rpow`s in terms of `ρ` and `ρ^α`
  have hsub : ρ ^ (α - 1) = ρ ^ α / ρ := by rw [Real.rpow_sub hρ, Real.rpow_one]
  have hadd1 : ρ ^ (α + 1) = ρ ^ α * ρ := by rw [Real.rpow_add hρ, Real.rpow_one]
  have hadd2 : ρ ^ (2 * α) = ρ ^ α * ρ ^ α := by
    rw [show (2 : ℝ) * α = α + α by ring, Real.rpow_add hρ]
  rw [hsub, hadd1, hadd2]
  field_simp
  ring

end Work.Elliptic
end
-- ===== merged: Submission.Work.FM.Core6 =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open MeasureTheory Set Filter
open scoped Topology

namespace Work.FM




/-- Convenience wrapper: `∂_ρ L₁₂^K(f) = -L12dens K f` from integrability of the
density on `(a,∞)` and its continuity on `(a,∞)`. -/
theorem hasDerivAt_L12_of_integrable {K : ℝ → ℝ} {f : ℝ → ℝ → ℝ} {a ρ : ℝ}
    (hint : IntegrableOn (L12dens K f) (Ioi a))
    (hcont : ∀ s, a < s → ContinuousAt (L12dens K f) s) (ha : a < ρ) :
    HasDerivAt (fun σ => L12 K f σ) (-(L12dens K f ρ)) ρ :=
  hasDerivAt_L12 hint (hcont ρ ha) ha



end Work.FM
end
end
-- ===== merged: Submission.Work.FTS.Apriori.ZeroMode.ZM_Main =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.Apriori.ZeroMode

set_option autoImplicit false

/-- **The main computation of the `L₁₂` zero-mode identity.** -/
theorem zm_main {α : ℝ} {f : ℝ → ℝ → ℝ} (H : L12Hyp α f)
    (hslice : ∀ r : ℝ, 0 < r →
      MeasureTheory.IntegrableOn (fun θ : ℝ => Work.Spaces.K θ * f r θ) Work.Spaces.Iθ)
    (hrel : ∀ r : ℝ, 0 < r → r * uOf f r = - NOf f r)
    (hNcont : ContinuousOn (NOf f) (Set.Ici 0))
    (hNtop : Filter.Tendsto (NOf f) Filter.atTop (𝓝 0))
    (hR0 : Filter.Tendsto (ROf f) (𝓝[>] (0:ℝ)) (𝓝 (ROf f 0)))
    (hRtop : Filter.Tendsto (fun r : ℝ => ROf f r / (1 + r)) Filter.atTop (𝓝 0))
    (hN0 : NOf f 0 = 0)
    (hmdInt : MeasureTheory.IntegrableOn (mdOf f) (Set.Ioi 0))
    (hmdIoc : ∀ ε ρ : ℝ, 0 < ε → ε < ρ →
      ∫ r in Set.Ioc ε ρ, mdOf f r = NOf f ε - NOf f ρ)
    (hibp : ∀ ε ρ : ℝ, 0 < ε → ε < ρ →
      ∫ r in Set.Ioc ε ρ, ROf f r / (1 + r) ^ 2
        = -(ROf f ρ / (1 + ρ)) + ROf f ε / (1 + ε)
          - ∫ r in Set.Ioc ε ρ, uOf f r / (1 + r))
    (hae : ∀ᵐ r ∂(MeasureTheory.volume.restrict (Set.Ioi 0)),
      GOf α f r - uOf f r = mdOf f r - 2 * uOf f r / (1 + r) - 2 * ROf f r / (1 + r) ^ 2)
    (hGint : MeasureTheory.IntegrableOn (GOf α f) (Set.Ioi 0))
    (huint : MeasureTheory.IntegrableOn (uOf f) (Set.Ioi 0)) :
    Work.Construction.L12 (Work.Coercivity.LGamma α f) 0 = - Work.Construction.L12 f 0 := by
  have hL12G : Work.Construction.L12 (Work.Coercivity.LGamma α f) 0
      = ∫ r in Set.Ioi 0, GOf α f r := rfl
  have hL12f : Work.Construction.L12 f 0 = ∫ r in Set.Ioi 0, uOf f r := rfl
  rw [hL12G, hL12f]
  have hdiffint : IntegrableOn (fun r : ℝ => GOf α f r - uOf f r) (Set.Ioi 0) :=
    hGint.sub huint
  -- ### integrability of the pieces on `(ε,ρ]`
  have hI_md : ∀ ε ρ : ℝ, 0 < ε → IntegrableOn (mdOf f) (Set.Ioc ε ρ) :=
    fun ε ρ hε => hmdInt.mono_set fun _ hx => lt_trans hε hx.1
  have hI_u : ∀ ε ρ : ℝ, 0 < ε →
      IntegrableOn (fun r : ℝ => uOf f r / (1 + r)) (Set.Ioc ε ρ) := by
    intro ε ρ hε
    have hsub : Set.Ioc ε ρ ⊆ Set.Ioi 0 := fun x hx => lt_trans hε hx.1
    have hg : Integrable (fun r : ℝ => ‖uOf f r‖) (volume.restrict (Set.Ioc ε ρ)) :=
      (huint.mono_set hsub).norm
    have hmeas : AEStronglyMeasurable (fun r : ℝ => uOf f r / (1 + r))
        (volume.restrict (Set.Ioc ε ρ)) := by
      have h1 : AEStronglyMeasurable (fun r : ℝ => uOf f r)
          (volume.restrict (Set.Ioc ε ρ)) := (huint.mono_set hsub).aestronglyMeasurable
      have h2 : AEStronglyMeasurable (fun r : ℝ => (1:ℝ) / (1 + r))
          (volume.restrict (Set.Ioc ε ρ)) :=
        (continuousOn_const.div (continuousOn_const.add continuousOn_id)
          (fun x hx => by
            have hx0 := hx.1
            simp only [Pi.add_apply, id_eq]
            linarith)).aestronglyMeasurable measurableSet_Ioc
      refine AEStronglyMeasurable.congr (h1.mul h2) ?_
      filter_upwards with r
      rw [Pi.mul_apply, one_div, div_eq_mul_inv]
    refine hg.mono' hmeas ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with r hr
    have hr1 : (0:ℝ) < 1 + r := by have := hr.1; linarith
    have h1r : (1:ℝ) ≤ 1 + r := by have := hr.1; linarith
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_div, abs_of_pos hr1]
    exact div_le_self (abs_nonneg _) h1r
  have hI_2u : ∀ ε ρ : ℝ, 0 < ε →
      IntegrableOn (fun r : ℝ => 2 * (uOf f r / (1 + r))) (Set.Ioc ε ρ) :=
    fun ε ρ hε =>
      (show Integrable (fun r : ℝ => uOf f r / (1 + r)) (volume.restrict (Set.Ioc ε ρ)) from
        hI_u ε ρ hε).const_mul 2
  have hI_2u' : ∀ ε ρ : ℝ, 0 < ε →
      IntegrableOn (fun r : ℝ => 2 * uOf f r / (1 + r)) (Set.Ioc ε ρ) :=
    fun ε ρ hε => (hI_2u ε ρ hε).congr (Eventually.of_forall fun r => by ring)
  -- the whole right-hand side is integrable on `(ε,ρ]` because it is a.e. `G - u`
  have hI_A : ∀ ε ρ : ℝ, 0 < ε → ε < ρ →
      IntegrableOn (fun r : ℝ => mdOf f r - 2 * uOf f r / (1 + r)
        - 2 * ROf f r / (1 + r) ^ 2) (Set.Ioc ε ρ) :=
    fun ε ρ hε _ => (hdiffint.mono_set (fun x hx => lt_trans hε hx.1)).congr
      (ae_restrict_of_ae_restrict_of_subset (fun x hx => lt_trans hε hx.1) hae)
  have hI_B : ∀ ε ρ : ℝ, 0 < ε →
      IntegrableOn (fun r : ℝ => mdOf f r - 2 * uOf f r / (1 + r)) (Set.Ioc ε ρ) :=
    fun ε ρ hε => (hI_md ε ρ hε).sub (hI_2u' ε ρ hε)
  have hI_R : ∀ ε ρ : ℝ, 0 < ε → ε < ρ →
      IntegrableOn (fun r : ℝ => 2 * ROf f r / (1 + r) ^ 2) (Set.Ioc ε ρ) := by
    intro ε ρ hε hερ
    have h := (hI_A ε ρ hε hερ).sub (hI_B ε ρ hε)
    refine h.neg.congr ?_
    filter_upwards with r
    simp only [Pi.neg_apply, Pi.sub_apply]
    ring
  -- ### the strip identity
  have hstrip : ∀ ε ρ : ℝ, 0 < ε → ε < ρ →
      ∫ r in Set.Ioc ε ρ, (GOf α f r - uOf f r)
        = (NOf f ε - 2 * ROf f ε / (1 + ε)) - (NOf f ρ - 2 * ROf f ρ / (1 + ρ)) := by
    intro ε ρ hε hερ
    have hae' : ∀ᵐ r ∂(volume.restrict (Set.Ioc ε ρ)),
        GOf α f r - uOf f r
          = mdOf f r - 2 * uOf f r / (1 + r) - 2 * ROf f r / (1 + r) ^ 2 :=
      ae_restrict_of_ae_restrict_of_subset (fun x hx => lt_trans hε hx.1) hae
    rw [integral_congr_ae hae']
    rw [integral_sub (hI_B ε ρ hε) (hI_R ε ρ hε hερ), integral_sub (hI_md ε ρ hε) (hI_2u' ε ρ hε)]
    rw [show (∫ r in Set.Ioc ε ρ, 2 * uOf f r / (1 + r))
          = 2 * ∫ r in Set.Ioc ε ρ, uOf f r / (1 + r) from by
        rw [← integral_const_mul]; exact MeasureTheory.integral_congr_ae (Eventually.of_forall fun r => by ring),
      show (∫ r in Set.Ioc ε ρ, 2 * ROf f r / (1 + r) ^ 2)
          = 2 * ∫ r in Set.Ioc ε ρ, ROf f r / (1 + r) ^ 2 from by
        rw [← integral_const_mul]; exact MeasureTheory.integral_congr_ae (Eventually.of_forall fun r => by ring)]
    rw [hmdIoc ε ρ hε hερ, hibp ε ρ hε hερ]
    ring
  -- ### the limit `ρ → ∞`
  have hlim_rho : ∀ ε : ℝ, 0 < ε →
      ∫ r in Set.Ioi ε, (GOf α f r - uOf f r) = NOf f ε - 2 * ROf f ε / (1 + ε) := by
    intro ε hε
    have hg : IntegrableOn (fun r : ℝ => GOf α f r - uOf f r) (Set.Ioi ε) :=
      hdiffint.mono_set (Set.Ioi_subset_Ioi (le_of_lt hε))
    have h1 : Tendsto (fun ρ : ℝ => ∫ r in Set.Ioc ε ρ, (GOf α f r - uOf f r)) atTop
        (𝓝 (∫ r in Set.Ioi ε, (GOf α f r - uOf f r))) := zm_tendsto_Ioc_atTop hg
    have h2 : Tendsto (fun ρ : ℝ => (NOf f ε - 2 * ROf f ε / (1 + ε))
        - (NOf f ρ - 2 * ROf f ρ / (1 + ρ))) atTop
        (𝓝 (NOf f ε - 2 * ROf f ε / (1 + ε))) := by
      have h4 : Tendsto (fun ρ : ℝ => 2 * ROf f ρ / (1 + ρ)) atTop (𝓝 0) := by
        have h5 : Tendsto (fun ρ : ℝ => 2 * (ROf f ρ / (1 + ρ))) atTop (𝓝 (2 * (0:ℝ))) :=
          hRtop.const_mul 2
        rw [mul_zero] at h5
        refine h5.congr' ?_
        filter_upwards with ρ
        ring
      have h3 : Tendsto (fun ρ : ℝ => NOf f ρ - 2 * ROf f ρ / (1 + ρ)) atTop (𝓝 0) := by
        have h6 := hNtop.sub h4
        simpa using h6
      simpa using (tendsto_const_nhds.sub h3)
    have h3 : Tendsto (fun ρ : ℝ => ∫ r in Set.Ioc ε ρ, (GOf α f r - uOf f r)) atTop
        (𝓝 (NOf f ε - 2 * ROf f ε / (1 + ε))) := by
      refine h2.congr' ?_
      filter_upwards [Ioi_mem_atTop ε] with ρ hρ
      exact (hstrip ε ρ hε hρ).symm
    exact tendsto_nhds_unique h1 h3
  -- ### the limit `ε → 0⁺` of the tails
  have hlim_eps : Tendsto (fun ε : ℝ => ∫ r in Set.Ioi ε, (GOf α f r - uOf f r))
      (𝓝[>] (0:ℝ)) (𝓝 (∫ r in Set.Ioi 0, (GOf α f r - uOf f r))) := by
    have h1 : Tendsto (fun ε : ℝ => (∫ r in Set.Ioi 0, (GOf α f r - uOf f r))
        - (∫ r in Set.Ioc 0 ε, (GOf α f r - uOf f r))) (𝓝[>] (0:ℝ))
        (𝓝 ((∫ r in Set.Ioi 0, (GOf α f r - uOf f r)) - 0)) :=
      tendsto_const_nhds.sub (zm_tendsto_Ioc_zero hdiffint)
    have h1' : Tendsto (fun ε : ℝ => (∫ r in Set.Ioi 0, (GOf α f r - uOf f r))
        - (∫ r in Set.Ioc 0 ε, (GOf α f r - uOf f r))) (𝓝[>] (0:ℝ))
        (𝓝 (∫ r in Set.Ioi 0, (GOf α f r - uOf f r))) := by
      simpa using h1
    refine h1'.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with ε hε
    have h2 : (∫ r in Set.Ioc 0 ε, (GOf α f r - uOf f r))
        + (∫ r in Set.Ioi ε, (GOf α f r - uOf f r))
        = ∫ r in Set.Ioi 0, (GOf α f r - uOf f r) := by
      have h3 := intervalIntegral.integral_interval_add_Ioi
        (f := fun r : ℝ => GOf α f r - uOf f r) (a := 0) (b := ε) hdiffint
        (hdiffint.mono_set (Set.Ioi_subset_Ioi (le_of_lt hε)))
      rwa [intervalIntegral.integral_of_le (le_of_lt hε)] at h3
    linarith
  -- ### the limit `ε → 0⁺` of the boundary terms
  have hlim_w : Tendsto (fun ε : ℝ => NOf f ε - 2 * ROf f ε / (1 + ε)) (𝓝[>] (0:ℝ))
      (𝓝 (-2 * ∫ r in Set.Ioi 0, uOf f r)) := by
    have hc : ContinuousWithinAt (NOf f) (Set.Ioi 0) 0 :=
      (hNcont.continuousWithinAt (by simp)).mono (Set.Ioi_subset_Ici_self)
    have h1 : Tendsto (NOf f) (𝓝[>] (0:ℝ)) (𝓝 0) := by
      have h := hc.tendsto
      rw [hN0] at h
      exact h
    have h2 : Tendsto (fun ε : ℝ => 2 * ROf f ε / (1 + ε)) (𝓝[>] (0:ℝ))
        (𝓝 (2 * ∫ r in Set.Ioi 0, uOf f r)) := by
      have hROf0 : ROf f 0 = ∫ r in Set.Ioi 0, uOf f r := rfl
      have h5 : Tendsto (fun ε : ℝ => 2 * (ROf f ε / (1 + ε))) (𝓝[>] (0:ℝ))
          (𝓝 (2 * ROf f 0)) := by
        have hden : Tendsto (fun ε : ℝ => 1 + ε) (𝓝[>] (0:ℝ)) (𝓝 (1 + (0:ℝ))) :=
          tendsto_const_nhds.add
            ((tendsto_id : Tendsto (fun x : ℝ => x) (𝓝 (0:ℝ)) (𝓝 0)).mono_left
              nhdsWithin_le_nhds)
        have h := (hR0.div hden (by norm_num)).const_mul 2
        simpa using h
      rw [hROf0] at h5
      refine h5.congr' ?_
      filter_upwards with ε
      ring
    have h3 := h1.sub h2
    simpa using h3
  -- ### conclusion
  have hfinal : ∫ r in Set.Ioi 0, (GOf α f r - uOf f r) = -2 * ∫ r in Set.Ioi 0, uOf f r := by
    have h1 : Tendsto (fun ε : ℝ => NOf f ε - 2 * ROf f ε / (1 + ε)) (𝓝[>] (0:ℝ))
        (𝓝 (∫ r in Set.Ioi 0, (GOf α f r - uOf f r))) := by
      refine hlim_eps.congr' ?_
      filter_upwards [self_mem_nhdsWithin] with ε hε
      exact hlim_rho ε hε
    exact tendsto_nhds_unique h1 hlim_w
  have hsub : (∫ r in Set.Ioi 0, (GOf α f r - uOf f r))
      = (∫ r in Set.Ioi 0, GOf α f r) - (∫ r in Set.Ioi 0, uOf f r) :=
    integral_sub hGint huint
  rw [hsub] at hfinal
  linarith

end Work.FTS.Apriori.ZeroMode
end
end
-- ===== merged: Submission.Work.FTS.BSIdent.Cyl.DecayAux.hasDerivAt_rhoP_rpow_div_fst =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.BSIdent.Cyl.DecayAux

/-- `r ↦ ρ(r,z) = √(r²+z²)` has radial derivative `r/ρ`.  Radial counterpart of
`Work.Cyl.hasDerivAt_rhoP_polar`. -/
private lemma hasDerivAt_rhoP_fst_polar (r z : ℝ) (hr : 0 < r) :
    HasDerivAt (fun r' : ℝ => Work.Cyl.rhoP r' z) (r / Work.Cyl.rhoP r z) r := by
  have hsq : HasDerivAt (fun r' : ℝ => r' ^ 2 + z ^ 2) (2 * r) r := by
    have h : HasDerivAt (fun r' : ℝ => r' ^ 2) (2 * r) r := by
      simpa using (hasDerivAt_pow 2 r)
    simpa using h.add_const (z ^ 2)
  have hne : r ^ 2 + z ^ 2 ≠ 0 := by positivity
  have h := hsq.sqrt hne
  have hval : (2 * r) / (2 * Real.sqrt (r ^ 2 + z ^ 2)) = r / Work.Cyl.rhoP r z := by
    have hs : Real.sqrt (r ^ 2 + z ^ 2) ≠ 0 := by positivity
    rw [Work.Cyl.rhoP]; field_simp
  rw [hval] at h
  exact h

/-- `r ↦ ρ(r,z)^α` has radial derivative `α ρ^{α-1} · (r/ρ)`.  Radial counterpart of
`Work.Cyl.hasDerivAt_rhoP_rpow_polar`. -/
private lemma hasDerivAt_rhoP_fst_rpow (r α z : ℝ) (hr : 0 < r) :
    HasDerivAt (fun r' : ℝ => Work.Cyl.rhoP r' z ^ α)
      (α * Work.Cyl.rhoP r z ^ (α - 1) * (r / Work.Cyl.rhoP r z)) r := by
  have hbase := hasDerivAt_rhoP_fst_polar r z hr
  have h := hbase.rpow_const (p := α) (Or.inl (ne_of_gt (Work.Cyl.rhoP_pos hr z)))
  simpa only [mul_comm, mul_left_comm, mul_assoc] using h

/-- The radial derivative of `r' ↦ ρ(r',z)^p / b`, obtained from
`hasDerivAt_rhoP_fst_rpow` (which gives the derivative `p ρ^{p-1} · (r/ρ)` of
`r' ↦ ρ(r',z)^p`) after dividing by the constant `b` and rewriting
`ρ^{p-1} · (r/ρ) = ρ^p · (r/ρ^2)`. -/
theorem hasDerivAt_rhoP_rpow_div_fst (r p z b : ℝ) (hr : 0 < r) :
    HasDerivAt (fun r' : ℝ => Work.Cyl.rhoP r' z ^ p / b)
      (p * (Work.Cyl.rhoP r z ^ p / b) * (r / Work.Cyl.rhoP r z ^ 2)) r := by
  have h := (hasDerivAt_rhoP_fst_rpow r p z hr).div_const b
  have hne : Work.Cyl.rhoP r z ≠ 0 := Work.Cyl.rhoP_ne_zero hr z
  convert h using 1
  rw [Real.rpow_sub_one hne, div_eq_mul_inv, div_eq_mul_inv]
  field_simp

end Work.FTS.BSIdent.Cyl.DecayAux
end
-- ===== merged: Submission.Work.FTS.ClassCHon.Hcoef.far_cs =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `FTS/ClassCHon/Hcoef/far_cs` — the far-field Cauchy–Schwarz bound

For a source `c` with `∫_{t>0} (c t · w t)² < ∞` and `p > 3/2`, `a > 0`,

  `∫_{t>a} c t · t^{-p-1}` is absolutely convergent and
  `|∫_{t>a} c t · t^{-p-1}| ≤ B · a^{-p}/√(2p-3)`,  where `B ≥ √(∫_{t>0} (c t · w t)²)`.

The kernel is split against the weight `w(t) = (1+t)²/t²`:

  `c t · t^{-p-1} = (c t · w t) · (t^{-p-1}/w t)`,

so Cauchy–Schwarz (`Work.Coercivity.holder_two_mul`) reduces the claim to the source norm and the
explicit weight integral `∫_{t>a} t^{-2p-2}/w(t)² ≤ a^{-2p}/(2p-3)`
(`WeightIntegrals.far_weight_integral_le`).
-/

noncomputable section

open MeasureTheory Set Filter
open scoped Real Topology

namespace Work.FTS.ClassCHon.Hcoef

local notation "w" => Work.Spaces.w

/-- The square of the far-field kernel factor, in the form consumed by
`WeightIntegrals.far_weight_integral_le`. -/
theorem far_cs_kernel_sq_eq {P t : ℝ} (ht : 0 < t) :
    (t ^ (-P - 1) / w t) ^ 2 = t ^ (-2 * P - 2) / (w t) ^ 2 := by
  rw [div_pow]
  congr 1
  rw [← Real.rpow_ofNat (t ^ (-P - 1)) 2, ← Real.rpow_mul ht.le]
  ring_nf

/-- Pointwise domination of the far-field kernel square by the pure power `t^{-2P+2}`. -/
theorem far_cs_kernel_sq_le {P t : ℝ} (ht : 0 < t) (hP : 3 / 2 < P) :
    (t ^ (-P - 1) / w t) ^ 2 ≤ t ^ (-2 * P + 2) := by
  rw [far_cs_kernel_sq_eq ht]
  exact Work.FTS.ClassCHon.far_div_w_sq_le_rpow ht hP

/-- Integrability of the squared far-field kernel factor on `(a,∞)`. -/
theorem far_cs_kernel_sq_integrable {P a : ℝ} (ha : 0 < a) (hP : 3 / 2 < P) :
    MeasureTheory.IntegrableOn (fun t : ℝ => (t ^ (-P - 1) / w t) ^ 2) (Set.Ioi a) := by
  have hbase : MeasureTheory.IntegrableOn (fun t : ℝ => t ^ (-2 * P + 2)) (Set.Ioi a) :=
    integrableOn_Ioi_rpow_of_lt (by linarith : -2 * P + 2 < -1) ha
  have hmeas : MeasureTheory.AEStronglyMeasurable (fun t : ℝ => (t ^ (-P - 1) / w t) ^ 2)
      (MeasureTheory.volume.restrict (Set.Ioi a)) := by
    have h0 : MeasureTheory.AEStronglyMeasurable (fun t : ℝ => t ^ (-P - 1) / w t)
        (MeasureTheory.volume.restrict (Set.Ioi a)) :=
      (Work.FTS.ClassCHon.aestronglyMeasurable_div_w' (e := -P - 1)).mono_measure
        (Measure.restrict_mono (fun t ht => lt_trans ha ht) le_rfl)
    convert h0.mul h0 using 1
    funext t
    rw [Pi.mul_apply, pow_two]
  refine hbase.mono' hmeas ?_
  filter_upwards [MeasureTheory.self_mem_ae_restrict measurableSet_Ioi] with t ht
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  exact far_cs_kernel_sq_le (lt_trans ha ht) hP

theorem far_cs {p B a : ℝ} (hp : 3 / 2 < p) (ha : 0 < a) {c : ℝ → ℝ}
    (hc : MeasureTheory.IntegrableOn (fun t : ℝ => (c t * Work.Spaces.w t) ^ 2) (Set.Ioi 0))
    (hcm : MeasureTheory.AEStronglyMeasurable (fun t : ℝ => c t * Work.Spaces.w t)
      (MeasureTheory.volume.restrict (Set.Ioi 0)))
    (hB : Real.sqrt (∫ t in Set.Ioi (0 : ℝ), (c t * Work.Spaces.w t) ^ 2) ≤ B) :
    MeasureTheory.IntegrableOn (fun t : ℝ => c t * t ^ (-p - 1)) (Set.Ioi a) ∧
      |∫ t in Set.Ioi a, c t * t ^ (-p - 1)|
        ≤ B * (a ^ (-p) / Real.sqrt (2 * p - 3)) := by
  have hsub : Set.Ioi a ⊆ Set.Ioi (0 : ℝ) := fun t ht => lt_trans ha ht
  -- the two `L²` factors, restricted to `(a,∞)`
  have hu : MeasureTheory.AEStronglyMeasurable (fun t : ℝ => c t * w t)
      (MeasureTheory.volume.restrict (Set.Ioi a)) :=
    hcm.mono_measure (Measure.restrict_mono hsub le_rfl)
  have hv : MeasureTheory.AEStronglyMeasurable (fun t : ℝ => t ^ (-p - 1) / w t)
      (MeasureTheory.volume.restrict (Set.Ioi a)) :=
    (Work.FTS.ClassCHon.aestronglyMeasurable_div_w' (e := -p - 1)).mono_measure
      (Measure.restrict_mono hsub le_rfl)
  have hu2 : MeasureTheory.Integrable (fun t : ℝ => (c t * w t) ^ 2)
      (MeasureTheory.volume.restrict (Set.Ioi a)) := hc.mono_set hsub
  have hv2 : MeasureTheory.Integrable (fun t : ℝ => (t ^ (-p - 1) / w t) ^ 2)
      (MeasureTheory.volume.restrict (Set.Ioi a)) :=
    far_cs_kernel_sq_integrable ha hp
  obtain ⟨hint, hcs⟩ := Work.Coercivity.holder_two_mul
    (MeasureTheory.volume.restrict (Set.Ioi a))
    (fun t : ℝ => c t * w t) (fun t : ℝ => t ^ (-p - 1) / w t) hu hv hu2 hv2
  -- the pointwise identification of the product with the requested integrand
  have hae : (fun x : ℝ => (fun t : ℝ => c t * w t) x * (fun t : ℝ => t ^ (-p - 1) / w t) x)
      =ᵐ[MeasureTheory.volume.restrict (Set.Ioi a)] (fun t : ℝ => c t * t ^ (-p - 1)) := by
    filter_upwards [MeasureTheory.self_mem_ae_restrict measurableSet_Ioi] with t ht
    have hw : w t ≠ 0 := ne_of_gt (Work.FTS.ClassCHon.w_pos_of_pos (lt_trans ha ht))
    field_simp
  have hprod : ∫ t in Set.Ioi a,
        (fun t : ℝ => c t * w t) t * (fun t : ℝ => t ^ (-p - 1) / w t) t
      = ∫ t in Set.Ioi a, c t * t ^ (-p - 1) := by
    refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
    have hw : w t ≠ 0 := ne_of_gt (Work.FTS.ClassCHon.w_pos_of_pos (lt_trans ha ht))
    field_simp
  have hcs' : |∫ t in Set.Ioi a, c t * t ^ (-p - 1)|
      ≤ Real.sqrt (∫ t in Set.Ioi a, (c t * w t) ^ 2)
        * Real.sqrt (∫ t in Set.Ioi a, (t ^ (-p - 1) / w t) ^ 2) := by
    rw [← hprod]; exact hcs
  -- the weight integral and its square root
  have hker : ∫ t in Set.Ioi a, (t ^ (-p - 1) / w t) ^ 2 ≤ a ^ (-2 * p) / (2 * p - 3) := by
    rw [show (∫ t in Set.Ioi a, (t ^ (-p - 1) / w t) ^ 2)
        = ∫ t in Set.Ioi a, t ^ (-2 * p - 2) / (w t) ^ 2 from
      MeasureTheory.setIntegral_congr_fun measurableSet_Ioi
        (fun t ht => far_cs_kernel_sq_eq (lt_trans ha ht))]
    exact Work.FTS.ClassCHon.WeightIntegrals.far_weight_integral_le ha hp
  have hsq : Real.sqrt (∫ t in Set.Ioi a, (t ^ (-p - 1) / w t) ^ 2)
      ≤ a ^ (-p) / Real.sqrt (2 * p - 3) := by
    refine (Real.sqrt_le_sqrt hker).trans ?_
    rw [Real.sqrt_div (Real.rpow_nonneg ha.le _) (2 * p - 3),
      show a ^ (-2 * p) = (a ^ (-p)) ^ 2 by rw [sq, ← Real.rpow_add ha]; ring_nf,
      Real.sqrt_sq (Real.rpow_nonneg ha.le _)]
  -- the source norm is dominated by `B`
  have hmono : ∫ t in Set.Ioi a, (c t * w t) ^ 2 ≤ ∫ t in Set.Ioi (0 : ℝ), (c t * w t) ^ 2 :=
    MeasureTheory.setIntegral_mono_set hc (Eventually.of_forall fun t => sq_nonneg _)
      (Eventually.of_forall fun t ht => lt_trans ha ht)
  have hsq2 : Real.sqrt (∫ t in Set.Ioi a, (c t * w t) ^ 2) ≤ B :=
    (Real.sqrt_le_sqrt hmono).trans hB
  have hB0 : 0 ≤ B := (Real.sqrt_nonneg _).trans hsq2
  refine ⟨hint.congr hae, ?_⟩
  calc |∫ t in Set.Ioi a, c t * t ^ (-p - 1)|
      = |∫ t in Set.Ioi a,
          (fun t : ℝ => c t * w t) t * (fun t : ℝ => t ^ (-p - 1) / w t) t| := by rw [hprod]
    _ ≤ Real.sqrt (∫ t in Set.Ioi a, (c t * w t) ^ 2)
        * Real.sqrt (∫ t in Set.Ioi a, (t ^ (-p - 1) / w t) ^ 2) := hcs
    _ ≤ B * (a ^ (-p) / Real.sqrt (2 * p - 3)) :=
        mul_le_mul hsq2 hsq (Real.sqrt_nonneg _) hB0

end Work.FTS.ClassCHon.Hcoef
end
end
-- ===== merged: Submission.Work.FTS.ClassCHon.Hcoef.near_cs =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `FTS/ClassCHon/Hcoef/near_cs` — the near (small `t`) Cauchy–Schwarz coefficient bound

For a source `c` whose `w`-weighted square `(c·w)²` is integrable on `(0,∞)` with
`√(∫_{(0,∞)} (c·w)²) ≤ B`, the "near" kernel `t ↦ c t · t^{q-1}` is integrable on `(0,a]` and

  `|∫_{(0,a]} c t · t^{q-1}| ≤ B · a^q / √(2q-1)`   (`q > 1`, `a > 0`).

This is the pointwise coefficient bound used by the `ℋ^k`-membership argument for the
class-`C^α` datum: the mode coefficients are exactly of this shape (`HkMemOuter`/`Hcoef`),
with `B = ‖c‖_{w²}`.

The proof is Cauchy–Schwarz on `(0,a]` against the weight `w(t) = (1+t)²/t²`:
`c t · t^{q-1} = (c t · w t) · (t^{q-1}/w t)`, so

  `|∫_{(0,a]} c t t^{q-1}| ≤ √(∫_{(0,a]}(c·w)²) · √(∫_{(0,a]} t^{2q-2}/w²)`

and the second factor is `≤ a^q/√(2q-1)` by `WeightIntegrals.near_weight_integral_le`
(the elementary weight identity `t^{2Q-2}/w² = t^{2Q+2}/(1+t)⁴ ≤ (2Q/(2Q-1))·t^{2Q-1}`).
The reduction of the statement to the `L²`-pair is `Work.Coercivity.holder_two_mul`.
-/

namespace Work.FTS.ClassCHon.Hcoef

open MeasureTheory Set

/-- **Integrability of the near kernel.**  For `Q > 1` and `z > 0` the function
`t ↦ (t^{Q-1}/w(t))²` is integrable on `(0,z]`.

By `near_div_w_sq_le_self` it is dominated pointwise (on `t > 0`) by `t^{2Q-2}`, which is
integrable on `(0,z]` because `2Q - 2 > -1`. -/
theorem integrableOn_div_w_sq {Q z : ℝ} (hz : 0 < z) (hQ : 1 < Q) :
    MeasureTheory.IntegrableOn (fun t : ℝ => (t ^ (Q - 1) / Work.Spaces.w t) ^ 2)
      (Set.Ioc 0 z) := by
  have hsub : Set.Ioc (0 : ℝ) z ⊆ Set.Ioi 0 := fun t ht => ht.1
  have hbase : MeasureTheory.IntegrableOn (fun t : ℝ => t ^ (2 * Q - 2)) (Set.Ioc 0 z) :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hz.le).mp
      (intervalIntegral.intervalIntegrable_rpow' (r := 2 * Q - 2) (by linarith))
  have hmeas : MeasureTheory.AEStronglyMeasurable
      (fun t : ℝ => (t ^ (Q - 1) / Work.Spaces.w t) ^ 2) (volume.restrict (Set.Ioc 0 z)) :=
    ((Work.FTS.ClassCHon.aestronglyMeasurable_div_w hQ).mono_measure
      (Measure.restrict_mono hsub le_rfl)).pow 2
  refine hbase.mono' hmeas ?_
  filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioc] with t ht
  have ht0 : 0 < t := ht.1
  have h1 : (t ^ (Q - 1)) ^ 2 = t ^ (2 * Q - 2) := by
    rw [← Real.rpow_ofNat (t ^ (Q - 1)) 2, ← Real.rpow_mul ht0.le (Q - 1) 2]
    ring_nf
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), div_pow, h1]
  exact Work.FTS.ClassCHon.near_div_w_sq_le_self ht0 hQ

theorem near_cs {q B a : ℝ} (hq : 1 < q) (ha : 0 < a) {c : ℝ → ℝ}
    (hc : MeasureTheory.IntegrableOn (fun t : ℝ => (c t * Work.Spaces.w t) ^ 2) (Set.Ioi 0))
    (hcm : MeasureTheory.AEStronglyMeasurable (fun t : ℝ => c t * Work.Spaces.w t)
      (MeasureTheory.volume.restrict (Set.Ioi 0)))
    (hB : Real.sqrt (∫ t in Set.Ioi (0 : ℝ), (c t * Work.Spaces.w t) ^ 2) ≤ B) :
    MeasureTheory.IntegrableOn (fun t : ℝ => c t * t ^ (q - 1)) (Set.Ioc 0 a) ∧
      |∫ t in Set.Ioc (0 : ℝ) a, c t * t ^ (q - 1)|
        ≤ B * (a ^ q / Real.sqrt (2 * q - 1)) := by
  have hsub : Set.Ioc (0 : ℝ) a ⊆ Set.Ioi 0 := fun t ht => ht.1
  -- the two Cauchy–Schwarz factors, restricted to `(0,a]`
  have huz : MeasureTheory.AEStronglyMeasurable (fun t : ℝ => c t * Work.Spaces.w t)
      (volume.restrict (Set.Ioc 0 a)) :=
    hcm.mono_measure (Measure.restrict_mono hsub le_rfl)
  have hvz : MeasureTheory.AEStronglyMeasurable (fun t : ℝ => t ^ (q - 1) / Work.Spaces.w t)
      (volume.restrict (Set.Ioc 0 a)) :=
    (Work.FTS.ClassCHon.aestronglyMeasurable_div_w hq).mono_measure
      (Measure.restrict_mono hsub le_rfl)
  have hu2 : MeasureTheory.Integrable (fun t : ℝ => (c t * Work.Spaces.w t) ^ 2)
      (volume.restrict (Set.Ioc 0 a)) := hc.mono_set hsub
  have hv2 : MeasureTheory.Integrable (fun t : ℝ => (t ^ (q - 1) / Work.Spaces.w t) ^ 2)
      (volume.restrict (Set.Ioc 0 a)) := integrableOn_div_w_sq ha hq
  obtain ⟨hUVint, hcs⟩ := Work.Coercivity.holder_two_mul (volume.restrict (Set.Ioc 0 a))
    (fun t : ℝ => c t * Work.Spaces.w t) (fun t : ℝ => t ^ (q - 1) / Work.Spaces.w t)
    huz hvz hu2 hv2
  -- the product is the near kernel, on `(0,a]` where `w ≠ 0`
  have hpt : ∀ t ∈ Set.Ioc (0 : ℝ) a,
      (fun t : ℝ => c t * Work.Spaces.w t) t * (fun t : ℝ => t ^ (q - 1) / Work.Spaces.w t) t
        = c t * t ^ (q - 1) := by
    intro t ht
    have hwt : Work.Spaces.w t ≠ 0 := ne_of_gt (Work.FTS.ClassCHon.w_pos_of_pos ht.1)
    field_simp
  have hprod : ∫ t in Set.Ioc (0 : ℝ) a,
        (fun t : ℝ => c t * Work.Spaces.w t) t * (fun t : ℝ => t ^ (q - 1) / Work.Spaces.w t) t
      = ∫ t in Set.Ioc (0 : ℝ) a, c t * t ^ (q - 1) :=
    setIntegral_congr_fun measurableSet_Ioc hpt
  -- the weight integral
  have hker : ∫ t in Set.Ioc (0 : ℝ) a, (t ^ (q - 1) / Work.Spaces.w t) ^ 2
      ≤ a ^ (2 * q) / (2 * q - 1) := by
    rw [show (∫ t in Set.Ioc (0 : ℝ) a, (t ^ (q - 1) / Work.Spaces.w t) ^ 2)
        = ∫ t in Set.Ioc (0 : ℝ) a, t ^ (2 * q - 2) / (Work.Spaces.w t) ^ 2 from
      setIntegral_congr_fun measurableSet_Ioc fun t ht => by
        have ht0 : 0 < t := ht.1
        have h1 : (t ^ (q - 1)) ^ 2 = t ^ (2 * q - 2) := by
          rw [← Real.rpow_ofNat (t ^ (q - 1)) 2, ← Real.rpow_mul ht0.le (q - 1) 2]
          ring_nf
        rw [div_pow, h1]]
    exact Work.FTS.ClassCHon.WeightIntegrals.near_weight_integral_le ha hq
  have hsqV : Real.sqrt (∫ t in Set.Ioc (0 : ℝ) a, (t ^ (q - 1) / Work.Spaces.w t) ^ 2)
      ≤ a ^ q / Real.sqrt (2 * q - 1) := by
    refine (Real.sqrt_le_sqrt hker).trans ?_
    rw [Real.sqrt_div (x := a ^ (2 * q)) (Real.rpow_nonneg ha.le _) (2 * q - 1),
      show a ^ (2 * q) = (a ^ q) ^ 2 by rw [sq, ← Real.rpow_add ha]; ring_nf,
      Real.sqrt_sq (Real.rpow_nonneg ha.le q)]
  -- the source `L²`-norm, on `(0,a]` and on `(0,∞)`
  have hmono : ∫ t in Set.Ioc (0 : ℝ) a, (c t * Work.Spaces.w t) ^ 2
      ≤ ∫ t in Set.Ioi 0, (c t * Work.Spaces.w t) ^ 2 :=
    setIntegral_mono_set hc (Filter.Eventually.of_forall fun t => sq_nonneg _)
      (Filter.Eventually.of_forall fun t ht => ht.1)
  have hsqU : Real.sqrt (∫ t in Set.Ioc (0 : ℝ) a, (c t * Work.Spaces.w t) ^ 2) ≤ B :=
    (Real.sqrt_le_sqrt hmono).trans hB
  refine ⟨?_, ?_⟩
  · exact hUVint.congr (by
      filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioc] with t ht
      exact hpt t ht)
  · have hcs' : |∫ t in Set.Ioc (0 : ℝ) a, c t * t ^ (q - 1)|
        ≤ Real.sqrt (∫ t in Set.Ioc (0 : ℝ) a, (c t * Work.Spaces.w t) ^ 2)
          * Real.sqrt (∫ t in Set.Ioc (0 : ℝ) a, (t ^ (q - 1) / Work.Spaces.w t) ^ 2) := by
      rw [← hprod]; exact hcs
    have hBnn : (0 : ℝ) ≤ B := le_trans (Real.sqrt_nonneg _) hB
    exact hcs'.trans (mul_le_mul hsqU hsqV (Real.sqrt_nonneg _) hBnn)

end Work.FTS.ClassCHon.Hcoef
end
-- ===== merged: Submission.Work.FTS.CoercivityFix.Coer1T.GamL2.Core =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The two main estimates for `GammaL2Bnd`

* `int_F`: `∫_{Iθ}(Γ − K)² ≤ 25π/32 − 2 + 6p(π/2)` (`p = α/3`), the `α = 0` value
  `∫(1 − K)² = π/2 − 2 + 9π/32` corrected by the pointwise bound
  `(u^p − 3u)² ≤ (1 − 3u)² + 6p(1 − u)`;
* `c_le_one`, `one_sub_c_le`: the two one-sided bounds for the normalisation
  constant `c = ∫_{Iθ} Γ K`, namely `c ≤ 1` and `1 − c ≤ 3p(π/2)`.
-/

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.CoercivityFix.Coer1T.GamL2

/-- The elementary inequality `(a+b)² ≤ a² + 2|a||b| + b²`. -/
lemma sq_abs_add_le (a b : ℝ) : (a + b) ^ 2 ≤ a ^ 2 + 2 * |a| * |b| + b ^ 2 := by
  have h : a * b ≤ |a| * |b| := by rw [← abs_mul]; exact le_abs_self _
  nlinarith [h]

/-- `∫_{Iθ} c = c·(π/2)` for a constant `c`. -/
lemma int_const (c : ℝ) : (∫ θ in Work.Spaces.Iθ, c) = c * (Real.pi / 2) := by
  rw [MeasureTheory.setIntegral_const, smul_eq_mul, MeasureTheory.measureReal_def,
      Work.Spaces.Iθ, Real.volume_Icc, ENNReal.toReal_ofReal (by linarith [Real.pi_pos])]
  ring

/-- `K` is continuous. -/
lemma cont_K : Continuous Work.Spaces.K := by
  change Continuous fun θ : ℝ => 3 * Real.sin θ * Real.cos θ ^ 2
  fun_prop

/-- `Γ` is continuous for `α > 0`. -/
lemma continuous_Gam (α : ℝ) (hα : 0 < α) : Continuous (fun θ : ℝ => Work.Spaces.Gam α θ) := by
  simpa only [Work.Spaces.Gam] using
    (Continuous.rpow_const (f := fun θ : ℝ => Real.sin θ * Real.cos θ ^ 2) (by fun_prop)
      (fun _ => Or.inr (le_of_lt (by positivity : (0 : ℝ) < α / 3))))

/-- `K ≥ 0` on `Iθ`. -/
lemma K_nonneg {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) : 0 ≤ Work.Spaces.K θ := by
  have h := (Work.Spaces.sin_mul_cos_sq_mem_Icc θ hθ).1
  have hK : Work.Spaces.K θ = 3 * (Real.sin θ * Real.cos θ ^ 2) := by
    rw [Work.Spaces.K]; ring
  rw [hK]; linarith

/-- `K ≤ 3` on `Iθ`. -/
lemma K_le_three {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) : Work.Spaces.K θ ≤ 3 := by
  have h := (Work.Spaces.sin_mul_cos_sq_mem_Icc θ hθ).2
  have hK : Work.Spaces.K θ = 3 * (Real.sin θ * Real.cos θ ^ 2) := by
    rw [Work.Spaces.K]; ring
  rw [hK]; linarith

/-- The `F`-part of the estimate: `∫(Γ − K)² ≤ 25π/32 − 2 + 6p(π/2)`, `p = α/3`. -/
lemma int_F (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) :
    (∫ θ in Work.Spaces.Iθ, (Work.Spaces.Gam α θ - Work.Spaces.K θ) ^ 2)
      ≤ 25 * Real.pi / 32 - 2 + 6 * (α / 3) * (Real.pi / 2) := by
  set p : ℝ := α / 3 with hp
  have hp0 : 0 < p := by rw [hp]; linarith
  have hp1 : p ≤ 1 := by rw [hp]; linarith
  have hpt : ∀ θ ∈ Work.Spaces.Iθ, (Work.Spaces.Gam α θ - Work.Spaces.K θ) ^ 2
      ≤ 1 - 6 * (Real.sin θ * Real.cos θ ^ 2) + 6 * p * (1 - (Real.sin θ * Real.cos θ ^ 2))
        + 9 * (Real.sin θ * Real.cos θ ^ 2) ^ 2 := by
    intro θ hθ
    have hu := Work.Spaces.sin_mul_cos_sq_mem_Icc θ hθ
    have hcore := pow_sub_three_mul_sq_le (Real.sin θ * Real.cos θ ^ 2) p hu.1 hu.2 hp0 hp1
    have hG : Work.Spaces.Gam α θ = (Real.sin θ * Real.cos θ ^ 2) ^ p := by
      rw [Work.Spaces.Gam, hp]
    have hK : Work.Spaces.K θ = 3 * (Real.sin θ * Real.cos θ ^ 2) := by
      rw [Work.Spaces.K]; ring
    rw [hG, hK]
    exact hcore
  have hcontG : Continuous (fun θ : ℝ => Work.Spaces.Gam α θ) := continuous_Gam α hα
  have hintL : IntegrableOn (fun θ : ℝ => (Work.Spaces.Gam α θ - Work.Spaces.K θ) ^ 2)
      Work.Spaces.Iθ := ((hcontG.sub cont_K).pow 2).integrableOn_Icc
  have hintR : IntegrableOn (fun θ : ℝ => 1 - 6 * (Real.sin θ * Real.cos θ ^ 2)
      + 6 * p * (1 - (Real.sin θ * Real.cos θ ^ 2))
      + 9 * (Real.sin θ * Real.cos θ ^ 2) ^ 2) Work.Spaces.Iθ :=
    (by fun_prop : Continuous fun θ : ℝ => 1 - 6 * (Real.sin θ * Real.cos θ ^ 2)
      + 6 * p * (1 - (Real.sin θ * Real.cos θ ^ 2))
      + 9 * (Real.sin θ * Real.cos θ ^ 2) ^ 2).integrableOn_Icc
  have hmono : (∫ θ in Work.Spaces.Iθ, (Work.Spaces.Gam α θ - Work.Spaces.K θ) ^ 2)
      ≤ ∫ θ in Work.Spaces.Iθ, (1 - 6 * (Real.sin θ * Real.cos θ ^ 2)
          + 6 * p * (1 - (Real.sin θ * Real.cos θ ^ 2))
          + 9 * (Real.sin θ * Real.cos θ ^ 2) ^ 2) :=
    integral_mono_ae hintL hintR
      (by filter_upwards [ae_restrict_mem measurableSet_Icc] with θ hθ; exact hpt θ hθ)
  have h1 : IntegrableOn (fun _ : ℝ => (1 : ℝ)) Work.Spaces.Iθ := continuous_const.integrableOn_Icc
  have h2 : IntegrableOn (fun θ : ℝ => Real.sin θ * Real.cos θ ^ 2) Work.Spaces.Iθ :=
    (by fun_prop : Continuous fun θ : ℝ => Real.sin θ * Real.cos θ ^ 2).integrableOn_Icc
  have h3 : IntegrableOn (fun θ : ℝ => (Real.sin θ * Real.cos θ ^ 2) ^ 2) Work.Spaces.Iθ :=
    (by fun_prop : Continuous fun θ : ℝ => (Real.sin θ * Real.cos θ ^ 2) ^ 2).integrableOn_Icc
  have hA : (∫ θ in Work.Spaces.Iθ, (1 - 3 * (Real.sin θ * Real.cos θ ^ 2)) ^ 2)
      = Real.pi / 2 - 2 + 9 * (Real.pi / 32) := by
    have h6 : IntegrableOn (fun θ : ℝ => 6 * (Real.sin θ * Real.cos θ ^ 2)) Work.Spaces.Iθ :=
      (by fun_prop : Continuous fun θ : ℝ => 6 * (Real.sin θ * Real.cos θ ^ 2)).integrableOn_Icc
    have hA1 : IntegrableOn (fun θ : ℝ => 1 - 6 * (Real.sin θ * Real.cos θ ^ 2)) Work.Spaces.Iθ :=
      (by fun_prop : Continuous fun θ : ℝ => 1 - 6 * (Real.sin θ * Real.cos θ ^ 2)).integrableOn_Icc
    have hA2 : IntegrableOn (fun θ : ℝ => 9 * (Real.sin θ * Real.cos θ ^ 2) ^ 2) Work.Spaces.Iθ :=
      (by fun_prop : Continuous fun θ : ℝ => 9 * (Real.sin θ * Real.cos θ ^ 2) ^ 2).integrableOn_Icc
    rw [show (fun θ : ℝ => (1 - 3 * (Real.sin θ * Real.cos θ ^ 2)) ^ 2)
        = fun θ => (1 - 6 * (Real.sin θ * Real.cos θ ^ 2))
          + 9 * (Real.sin θ * Real.cos θ ^ 2) ^ 2 from by funext θ; ring]
    rw [integral_add hA1 hA2, integral_sub h1 h6, integral_const_mul, integral_const_mul,
        int_Iθ_one, int_Iθ_sinCos2, int_Iθ_sinCos2_sq]
    ring
  have hB : (∫ θ in Work.Spaces.Iθ, (1 - (Real.sin θ * Real.cos θ ^ 2)))
      = Real.pi / 2 - 1 / 3 := by
    rw [integral_sub h1 h2, int_Iθ_one, int_Iθ_sinCos2]
  have hval : (∫ θ in Work.Spaces.Iθ, (1 - 6 * (Real.sin θ * Real.cos θ ^ 2)
          + 6 * p * (1 - (Real.sin θ * Real.cos θ ^ 2))
          + 9 * (Real.sin θ * Real.cos θ ^ 2) ^ 2))
      = Real.pi / 2 - 2 + 9 * (Real.pi / 32) + 6 * p * (Real.pi / 2 - 1 / 3) := by
    have h6 : IntegrableOn (fun θ : ℝ => 6 * p * (1 - (Real.sin θ * Real.cos θ ^ 2)))
        Work.Spaces.Iθ :=
      (by fun_prop : Continuous fun θ : ℝ =>
        6 * p * (1 - (Real.sin θ * Real.cos θ ^ 2))).integrableOn_Icc
    have hA1 : IntegrableOn (fun θ : ℝ => (1 - 3 * (Real.sin θ * Real.cos θ ^ 2)) ^ 2)
        Work.Spaces.Iθ :=
      (by fun_prop : Continuous fun θ : ℝ =>
        (1 - 3 * (Real.sin θ * Real.cos θ ^ 2)) ^ 2).integrableOn_Icc
    rw [show (fun θ : ℝ => 1 - 6 * (Real.sin θ * Real.cos θ ^ 2)
          + 6 * p * (1 - (Real.sin θ * Real.cos θ ^ 2))
          + 9 * (Real.sin θ * Real.cos θ ^ 2) ^ 2)
        = fun θ => (1 - 3 * (Real.sin θ * Real.cos θ ^ 2)) ^ 2
          + 6 * p * (1 - (Real.sin θ * Real.cos θ ^ 2)) from by funext θ; ring]
    rw [integral_add hA1 h6, integral_const_mul, hA, hB]
  rw [hval] at hmono
  have hπ : Real.pi / 2 - 2 + 9 * (Real.pi / 32) = 25 * Real.pi / 32 - 2 := by ring
  have hcorr : 6 * p * (Real.pi / 2 - 1 / 3) ≤ 6 * p * (Real.pi / 2) := by
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    linarith
  linarith

/-- The normalisation constant is `≤ 1`. -/
lemma c_le_one (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) : Work.Spaces.c α ≤ 1 := by
  have hK : IntegrableOn Work.Spaces.K Work.Spaces.Iθ := cont_K.integrableOn_Icc
  have hGK : IntegrableOn (fun θ => Work.Spaces.Gam α θ * Work.Spaces.K θ) Work.Spaces.Iθ :=
    Work.Spaces.CAux.integrableOn_GamK α hα
  have hpt : ∀ θ ∈ Work.Spaces.Iθ, Work.Spaces.Gam α θ * Work.Spaces.K θ ≤ Work.Spaces.K θ := by
    intro θ hθ
    have hG := (Work.Spaces.Gam_bounds α θ hα hθ).2
    have hK0 := K_nonneg hθ
    nlinarith
  calc Work.Spaces.c α = ∫ θ in Work.Spaces.Iθ, Work.Spaces.Gam α θ * Work.Spaces.K θ := rfl
    _ ≤ ∫ θ in Work.Spaces.Iθ, Work.Spaces.K θ :=
        integral_mono_ae hGK hK
          (by filter_upwards [ae_restrict_mem measurableSet_Icc] with θ hθ; exact hpt θ hθ)
    _ = 1 := Work.Coercivity.integral_Itheta_K

/-- The normalisation defect: `1 − c ≤ 3p(π/2)`, `p = α/3`. -/
lemma one_sub_c_le (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1 / 10 ^ 14) :
    1 - Work.Spaces.c α ≤ 3 * (α / 3) * (Real.pi / 2) := by
  set p : ℝ := α / 3 with hp
  have hp0 : 0 < p := by rw [hp]; linarith
  have hα1' : α ≤ 1 := by
    have : (1 : ℝ) / 10 ^ 14 ≤ 1 := by norm_num
    linarith
  have hK : IntegrableOn Work.Spaces.K Work.Spaces.Iθ := cont_K.integrableOn_Icc
  have hGK : IntegrableOn (fun θ => Work.Spaces.Gam α θ * Work.Spaces.K θ) Work.Spaces.Iθ :=
    Work.Spaces.CAux.integrableOn_GamK α hα
  have hpt : ∀ θ ∈ Work.Spaces.Iθ, Work.Spaces.K θ - Work.Spaces.Gam α θ * Work.Spaces.K θ
      ≤ 3 * p := by
    intro θ hθ
    have hu := Work.Spaces.sin_mul_cos_sq_mem_Icc θ hθ
    have hG : Work.Spaces.Gam α θ = (Real.sin θ * Real.cos θ ^ 2) ^ p := by
      rw [Work.Spaces.Gam, hp]
    have hK' : Work.Spaces.K θ = 3 * (Real.sin θ * Real.cos θ ^ 2) := by
      rw [Work.Spaces.K]; ring
    rw [hG, hK']
    have hb := unit_sub_pow_le' (Real.sin θ * Real.cos θ ^ 2) p hu.1 hu.2 (le_of_lt hp0)
    have h3 : 3 * (Real.sin θ * Real.cos θ ^ 2)
          - (Real.sin θ * Real.cos θ ^ 2) ^ p * (3 * (Real.sin θ * Real.cos θ ^ 2))
        = 3 * ((Real.sin θ * Real.cos θ ^ 2) * (1 - (Real.sin θ * Real.cos θ ^ 2) ^ p)) := by
      ring
    rw [h3]
    have h4 : (Real.sin θ * Real.cos θ ^ 2) * (1 - (Real.sin θ * Real.cos θ ^ 2) ^ p) ≤ p := by
      nlinarith [hb, hu.1]
    linarith
  have hInt : IntegrableOn (fun θ => Work.Spaces.K θ - Work.Spaces.Gam α θ * Work.Spaces.K θ)
      Work.Spaces.Iθ := hK.sub hGK
  have hconst : IntegrableOn (fun _ : ℝ => 3 * p) Work.Spaces.Iθ :=
    continuous_const.integrableOn_Icc
  have hstep : (∫ θ in Work.Spaces.Iθ, (Work.Spaces.K θ - Work.Spaces.Gam α θ * Work.Spaces.K θ))
      ≤ 3 * p * (Real.pi / 2) := by
    have h := integral_mono_ae hInt hconst
      (by filter_upwards [ae_restrict_mem measurableSet_Icc] with θ hθ; exact hpt θ hθ)
    rwa [int_const] at h
  have hsub : 1 - Work.Spaces.c α
      = ∫ θ in Work.Spaces.Iθ, (Work.Spaces.K θ - Work.Spaces.Gam α θ * Work.Spaces.K θ) := by
    rw [show Work.Spaces.c α = ∫ θ in Work.Spaces.Iθ, Work.Spaces.Gam α θ * Work.Spaces.K θ from rfl,
        ← Work.Coercivity.integral_Itheta_K]
    exact (integral_sub hK hGK).symm
  rw [hsub]
  exact hstep

end Work.FTS.CoercivityFix.Coer1T.GamL2
end
end
-- ===== merged: Submission.Work.FTS.CoercivityFix.E2Bound.SlotMul.Zop_iterate_phiZ_bound =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open Set Filter Polynomial

namespace Work.FTS.CoercivityFix.E2Bound.SlotMul

open Work.FTS.CoercivityFix.E2Bound (zchart gpoly Tmul Pphi)

set_option autoImplicit false

/-- Chart algebra: for `z ≠ -1`, `1 - zchart z ^ 2 = 4 z / (1 + z) ^ 2`. -/
lemma phiZ_one_sub_zchart_sq {z : ℝ} (hz : 1 + z ≠ 0) :
    1 - zchart z ^ 2 = 4 * z / (1 + z) ^ 2 := by
  have hz' : z + 1 ≠ 0 := by intro h; exact hz (by linarith)
  rw [zchart, div_pow]
  field_simp
  ring

/-- `gpoly Pphi` is the profile `φ z = z / (1 + z) ^ 2` (away from the pole `z = -1`). -/
lemma phiZ_gpoly_eq {z : ℝ} (hz : 1 + z ≠ 0) : gpoly Pphi z = z / (1 + z) ^ 2 := by
  rw [gpoly_apply, Pphi_eq]
  simp only [Polynomial.eval_mul, Polynomial.eval_sub, Polynomial.eval_one,
    Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_C]
  rw [phiZ_one_sub_zchart_sq hz]
  ring

/-- For each `n` there is a common bound for the first `n` `Zop`-iterates of the profile
`φ(z) = z/(1+z)²` on the positive half-line. -/
theorem Zop_iterate_phiZ_bound (n : ℕ) : ∃ K : ℝ, 0 ≤ K ∧
    ∀ b ≤ n, ∀ z ∈ Set.Ioi (0 : ℝ),
      |Work.Spaces.Zop^[b] (fun z : ℝ => z / (1 + z) ^ 2) z| ≤ K := by
  refine ⟨∑ b ∈ Finset.range (n + 1),
    ∑ k ∈ Finset.range ((Tmul^[b] Pphi).natDegree + 1), |(Tmul^[b] Pphi).coeff k|, ?_, ?_⟩
  · exact Finset.sum_nonneg fun b _ => Finset.sum_nonneg fun k _ => abs_nonneg _
  · intro b hb z hz
    have hmem : b ∈ Finset.range (n + 1) := Finset.mem_range.mpr (Nat.lt_succ_of_le hb)
    -- transport the profile `φ` to the chart polynomial `gpoly Pphi`
    have hbase : Set.EqOn (fun y : ℝ => y / (1 + y) ^ 2) (gpoly Pphi) (Set.Ioi (0 : ℝ)) := by
      intro y hy
      have hy' : (0 : ℝ) < y := hy
      have hy1 : 1 + y ≠ 0 := by intro h; linarith
      exact (phiZ_gpoly_eq hy1).symm
    have h1 : (Work.Spaces.Zop^[b] (fun y : ℝ => y / (1 + y) ^ 2)) z
        = gpoly (Tmul^[b] Pphi) z := by
      rw [Zop_iterate_eqOn_of_eqOn b isOpen_Ioi hbase hz,
        Zop_gpoly_iterate Pphi b z hz]
    rw [h1]
    -- the chart variable lies in `(-1,1)`, so the polynomial evaluation is bounded by the
    -- sum of the absolute values of the coefficients
    have h2 : |gpoly (Tmul^[b] Pphi) z| ≤
        ∑ k ∈ Finset.range ((Tmul^[b] Pphi).natDegree + 1), |(Tmul^[b] Pphi).coeff k| := by
      have := Polynomial_abs_eval_le_sum_abs_coeff (Tmul^[b] Pphi)
        (Work.FTS.CoercivityFix.E2Bound.abs_zchart_le_one hz)
      simpa [Work.FTS.CoercivityFix.E2Bound.gpoly] using this
    -- one term of a sum of nonnegative terms
    have h3 : (∑ k ∈ Finset.range ((Tmul^[b] Pphi).natDegree + 1), |(Tmul^[b] Pphi).coeff k|)
        ≤ ∑ b' ∈ Finset.range (n + 1),
            ∑ k ∈ Finset.range ((Tmul^[b'] Pphi).natDegree + 1), |(Tmul^[b'] Pphi).coeff k| :=
      Finset.single_le_sum (f := fun b' =>
          ∑ k ∈ Finset.range ((Tmul^[b'] Pphi).natDegree + 1), |(Tmul^[b'] Pphi).coeff k|)
        (fun i _ => Finset.sum_nonneg fun k _ => abs_nonneg _) hmem
    linarith

end Work.FTS.CoercivityFix.E2Bound.SlotMul
end
end
-- ===== merged: Submission.Work.FTS.CoercivityFix.Transfer.E2norm.C0_eq_density =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.CoercivityFix.Transfer.E2norm

theorem C0_eq_density (f : ℝ → ℝ → ℝ) :
    Work.Coercivity.C0 f
      = ∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
          3 * Work.Spaces.K θ * Work.Spaces.Dth f z θ / (z * (1 + z)) := by
  simp only [Work.Coercivity.C0, Work.Coercivity.L12f, Work.FM.L12, Work.FM.L12dens,
    Work.Coercivity.Transport, Work.Spaces.Iz, Work.Spaces.Iθ]
  rw [MeasureTheory.integral_Ici_eq_integral_Ioi]
  congr 1 with z
  congr 1 with θ
  rw [div_eq_mul_inv, div_eq_mul_inv, div_eq_mul_inv, mul_inv]
  ring

end Work.FTS.CoercivityFix.Transfer.E2norm
end
-- ===== merged: Submission.Work.FTS.CoercivityStep.Base.H1IP_congr_qd =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open MeasureTheory Set

namespace Work.FTS.CoercivityStep.Base

/-! ## Congruence of `wip` on the open quadrant

The pairing `wip ρ A B = ∫_{z ∈ [0,∞)} ∫_{θ ∈ [0,π/2]} A z θ · B z θ · ρ z θ` is an
iterated Bochner integral, so it only sees the values of `A` almost everywhere.  The open
quadrant `Qd = (0,∞) × (0,π/2)` is co-null in the domain `[0,∞) × [0,π/2]` (the difference
is contained in the two lines `θ = 0`, `θ = π/2` and the point `z = 0`), so `wip` is
invariant under changing the first argument on `Qd`.

The two ingredients are the two "reduce to the open interval" identities

* `∫_{[0,∞)} = ∫_{(0,∞)}`  (`MeasureTheory.integral_Ici_eq_integral_Ioi`),
* `∫_{[0,π/2]} = ∫_{(0,π/2)}` (`MeasureTheory.integral_Icc_eq_integral_Ioo`),

both of which hold for the total Bochner integral without any measurability or
integrability hypothesis. -/

/-- The iterated integral `∫_{z∈[0,∞)} ∫_{θ∈[0,π/2]} F z θ` equals the iterated integral
over the open quadrant `∫_{z∈(0,∞)} ∫_{θ∈(0,π/2)} F z θ`.  No regularity is needed: the
Bochner integral is insensitive to null sets. -/
lemma wip_eq_Ioi_Ioo (F : ℝ → ℝ → ℝ) :
    (∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ, F z θ)
      = ∫ z in Set.Ioi (0 : ℝ), ∫ θ in Set.Ioo (0 : ℝ) (Real.pi / 2), F z θ := by
  have h1 : (∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ, F z θ)
      = ∫ z in Work.Spaces.Iz, ∫ θ in Set.Ioo (0 : ℝ) (Real.pi / 2), F z θ := by
    refine MeasureTheory.setIntegral_congr_fun measurableSet_Ici (fun z _ => ?_)
    exact MeasureTheory.integral_Icc_eq_integral_Ioo
  rw [h1]
  exact MeasureTheory.integral_Ici_eq_integral_Ioi

/-- `wip ρ A B` only depends on the first argument `A` through its values on the open
quadrant `Qd`: if `A = A'` on `Qd`, then `wip ρ A B = wip ρ A' B`.  No measurability,
integrability or smoothness hypothesis is required. -/
lemma wip_congr_Qd {ρ A A' B : ℝ → ℝ → ℝ}
    (h : ∀ z θ, (z, θ) ∈ Qd → A z θ = A' z θ) :
    Work.Coercivity.wip ρ A B = Work.Coercivity.wip ρ A' B := by
  simp only [Work.Coercivity.wip]
  rw [wip_eq_Ioi_Ioo (fun z θ => A z θ * B z θ * ρ z θ),
    wip_eq_Ioi_Ioo (fun z θ => A' z θ * B z θ * ρ z θ)]
  refine MeasureTheory.setIntegral_congr_fun
    (isOpen_Ioi (a := (0 : ℝ))).measurableSet (fun z hz => ?_)
  refine MeasureTheory.setIntegral_congr_fun
    (isOpen_Ioo (a := (0 : ℝ)) (b := Real.pi / 2)).measurableSet (fun θ hθ => ?_)
  rw [h z θ ⟨hz, hθ⟩]

/-! ## The derivative congruence

If `f` and `f'` agree on the open quadrant, then so do `D_z f` and `D_z f'` (resp.
`D_θ f` and `D_θ f'`): at a point of the open quadrant the two functions agree on a whole
neighbourhood, so the partial derivatives coincide there.  This is `Set.EqOn.deriv`
applied on the open sets `(0,∞)` and `(0,π/2)` of the two coordinate lines through the
point. -/

/-- `D_z f = D_z f'` on the open quadrant whenever `f = f'` there. -/
lemma Dz_congr_Qd {f f' : ℝ → ℝ → ℝ}
    (h : ∀ z θ, (z, θ) ∈ Qd → f z θ = f' z θ) :
    ∀ z θ, (z, θ) ∈ Qd → Work.Spaces.Dz f z θ = Work.Spaces.Dz f' z θ := by
  intro z θ hzθ
  have hz : (0 : ℝ) < z := hzθ.1
  have heq : Set.EqOn (fun t => f t θ) (fun t => f' t θ) (Set.Ioi 0) :=
    fun t ht => h t θ ⟨ht, hzθ.2⟩
  have hd := (heq.deriv isOpen_Ioi) hz
  simp only [Work.Spaces.Dz, Work.Spaces.pz]
  rw [hd]

/-- `D_θ f = D_θ f'` on the open quadrant whenever `f = f'` there. -/
lemma Dth_congr_Qd {f f' : ℝ → ℝ → ℝ}
    (h : ∀ z θ, (z, θ) ∈ Qd → f z θ = f' z θ) :
    ∀ z θ, (z, θ) ∈ Qd → Work.Spaces.Dth f z θ = Work.Spaces.Dth f' z θ := by
  intro z θ hzθ
  have hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) := hzθ.2
  have heq : Set.EqOn (fun t => f z t) (fun t => f' z t) (Set.Ioo 0 (Real.pi / 2)) :=
    fun t ht => h z t ⟨hzθ.1, ht⟩
  have hd := (heq.deriv isOpen_Ioo) hθ
  simp only [Work.Spaces.Dth, Work.Spaces.pth]
  rw [hd]

/-! ## The congruence of the `ℋ¹` inner product in its first argument -/

/-- **`H1IP α` only depends on its first argument through the values on the open
quadrant.**  `H1IP α` is the sum of four weighted pairings `wip`, applied to `f`, `D_z f`,
`f` and `D_θ f`; on `Qd` these agree with the corresponding functions built from `f'`
(the pointwise hypothesis `h` for `f` itself, and `Dz_congr_Qd`/`Dth_congr_Qd` for the
derivatives — derivatives are local and `Qd` is open, so the hypotheses `hf`, `hf'`, `hg`
are not needed).  `wip_congr_Qd` then identifies the four pairings. -/
theorem H1IP_congr_qd (α : ℝ) {f f' g : ℝ → ℝ → ℝ}
    (hf : Work.FTS.CoercivityStep.HkReg α 1 f)
    (hf' : Work.FTS.CoercivityStep.HkReg α 1 f')
    (hg : Work.FTS.CoercivityStep.HkReg α 1 g)
    (h : ∀ z θ : ℝ, (z, θ) ∈ Work.FTS.CoercivityStep.Qd → f z θ = f' z θ) :
    Work.Coercivity.H1IP α f g = Work.Coercivity.H1IP α f' g := by
  have hDz := Dz_congr_Qd h
  have hDth := Dth_congr_Qd h
  simp only [Work.Coercivity.H1IP]
  have h1 := wip_congr_Qd
    (ρ := (fun z θ => Work.Spaces.w z ^ 2 * (Real.sin (2 * θ)) ^ (-Work.Spaces.eta)))
    (A := Work.Spaces.Dz f) (A' := Work.Spaces.Dz f') (B := Work.Spaces.Dz g) hDz
  have h2 := wip_congr_Qd
    (ρ := (fun z θ => Work.Spaces.w z ^ 2 * (Real.sin (2 * θ)) ^ (-Work.Spaces.eta)))
    (A := f) (A' := f') (B := g) h
  have h3 := wip_congr_Qd
    (ρ := (fun z _ => Work.Spaces.w z ^ 2)) (A := f) (A' := f') (B := g) h
  have h4 := wip_congr_Qd
    (ρ := (fun z θ => Work.Spaces.w z ^ 2 * (Real.sin (2 * θ)) ^ (-Work.Spaces.gam α)))
    (A := Work.Spaces.Dth f) (A' := Work.Spaces.Dth f') (B := Work.Spaces.Dth g) hDth
  rw [h1, h2, h3, h4]

end Work.FTS.CoercivityStep.Base

end
end
-- ===== merged: Submission.Work.FTS.CoercivityStep.Base.H1IP_symm =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open MeasureTheory Set Filter

namespace Work.FTS.CoercivityStep.Base

/-! ## A helper: `wip` is symmetric in its two function arguments

`wip ρ A B = ∫_z ∫_θ A(z,θ) * B(z,θ) * ρ(z,θ)` is a *set integral* (over `Iz × Iθ`):
the two slices are integrals over the sets `Iz = [0,∞)` and `Iθ = [0,π/2]`, so the
pointwise identity `(A*B)*ρ = (B*A)*ρ` has to be pushed through the two nested set
integrals with `setIntegral_congr_fun` (no integrability is needed — both sides are
the same integral of equal integrands, including the junk-value case). -/

theorem wip_comm (ρ A B : ℝ → ℝ → ℝ) : Work.Coercivity.wip ρ A B = Work.Coercivity.wip ρ B A := by
  unfold Work.Coercivity.wip
  refine MeasureTheory.setIntegral_congr_fun (s := Work.Spaces.Iz) measurableSet_Ici
    (fun z _ => ?_)
  refine MeasureTheory.setIntegral_congr_fun (s := Work.Spaces.Iθ) measurableSet_Icc
    (fun θ _ => ?_)
  ring


end Work.FTS.CoercivityStep.Base
end
end
-- ===== merged: Submission.Work.FTS.CoercivityStep.Norm.HkSq_mono_le =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.CoercivityStep.Norm

set_option autoImplicit false

/-- The `H^k`-integrand is monotone in the exponent: for `k ≤ l` every summand of
`HkIntegrand α k f` occurs in `HkIntegrand α l f` with the same value, and all summands
are squares, hence nonnegative.  This is `Work.Spaces.HkIntegrand_mono` iterated. -/
private theorem HkIntegrand_mono_le (α : ℝ) {k l : ℕ} (hkl : k ≤ l) (f : ℝ → ℝ → ℝ)
    (z θ : ℝ) :
    Work.Spaces.HkIntegrand α k f z θ ≤ Work.Spaces.HkIntegrand α l f z θ :=
  Nat.le_induction (le_refl _)
    (fun n _ ih => le_trans ih (Work.Spaces.HkIntegrand_mono α n f z θ)) l hkl

theorem HkSq_mono_le (α : ℝ) {k l : ℕ} (hkl : k ≤ l) {f : ℝ → ℝ → ℝ}
    (h : Work.Spaces.HkMem α l f) : Work.Spaces.HkSq α k f ≤ Work.Spaces.HkSq α l f := by
  rw [Work.Spaces.HkSq, Work.Spaces.HkSq]
  refine MeasureTheory.integral_mono_of_nonneg
    (Eventually.of_forall fun z =>
      MeasureTheory.integral_nonneg fun θ => Work.Spaces.HkIntegrand_nonneg α k f z θ)
    h.2 ?_
  show ∀ᵐ z ∂(volume.restrict Work.Spaces.Iz),
    (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k f z θ)
      ≤ ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α l f z θ
  refine MeasureTheory.ae_restrict_of_forall_mem
    (show MeasurableSet Work.Spaces.Iz from measurableSet_Ici) fun z hz =>
    MeasureTheory.integral_mono_of_nonneg
      (Eventually.of_forall fun θ => Work.Spaces.HkIntegrand_nonneg α k f z θ)
      (h.1 z hz)
      (Eventually.of_forall fun θ => HkIntegrand_mono_le α hkl f z θ)

end Work.FTS.CoercivityStep.Norm
end
end
-- ===== merged: Submission.Work.FTS.EllExist.Honesty.G1_energy_identity =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllExist.Honesty

open MeasureTheory Set

set_option autoImplicit false

theorem G1_energy_identity {α : ℝ} (hα : 0 < α) (m : ℕ) {c : ℝ → ℝ}
    (hc : ContinuousOn c (Set.Ioi 0))
    (h0 : MeasureTheory.IntegrableOn (fun z => c z ^ 2 / z ^ 4) (Set.Ioo 0 1)) :
    ∀ x y : ℝ, 0 < x → x < y → y < 1 →
      (3 + 2 * Work.FTS.EllExist.Honesty.G1a α m)
          * (∫ z in x..y, Work.FTS.EllExist.Honesty.G1 α m c z ^ 2 / z ^ 4)
        = 2 * (∫ z in x..y, c z * Work.FTS.EllExist.Honesty.G1 α m c z / z ^ 4)
          + Work.FTS.EllExist.Honesty.G1 α m c x ^ 2 / x ^ 3
          - Work.FTS.EllExist.Honesty.G1 α m c y ^ 2 / y ^ 3 := by
  intro x y hx hxy hy1
  -- the pointwise ODE for `G1`
  have hG1d : ∀ z ∈ Set.Ioi (0 : ℝ),
      HasDerivAt (G1 α m c) ((-(G1a α m) * G1 α m c z + c z) / z) z :=
    G1_hasDerivAt hα m hc h0
  -- the derivative of `u z = G1 z ^ 2 / z ^ 3`
  have hF : ∀ z ∈ Set.uIcc x y,
      HasDerivAt (fun w : ℝ => G1 α m c w ^ 2 / w ^ 3)
        ((2 * c z * G1 α m c z - (3 + 2 * G1a α m) * G1 α m c z ^ 2) / z ^ 4) z := by
    intro z hz
    rw [Set.uIcc_of_le hxy.le] at hz
    have hz0 : 0 < z := lt_of_lt_of_le hx hz.1
    exact hasDerivAt_sq_div_cube hz0 (hG1d z hz0)
  -- continuity of the ingredients on the closed interval `[x,y] ⊆ (0,1)`
  have hmem : ∀ z ∈ Set.Icc x y, 0 < z ∧ z < 1 := fun z hz =>
    ⟨lt_of_lt_of_le hx hz.1, lt_of_le_of_lt hz.2 hy1⟩
  have hcc : ContinuousOn c (Set.Icc x y) :=
    hc.mono (fun z hz => (hmem z hz).1)
  have hgc : ContinuousOn (G1 α m c) (Set.Icc x y) :=
    (G1_continuousOn hα m hc h0).mono (fun z hz => ⟨(hmem z hz).1, (hmem z hz).2⟩)
  have hden : ContinuousOn (fun z : ℝ => z ^ 4) (Set.Icc x y) := continuousOn_id.pow 4
  have hne4 : ∀ z ∈ Set.Icc x y, z ^ 4 ≠ 0 := fun z hz =>
    pow_ne_zero 4 (ne_of_gt (hmem z hz).1)
  -- the integrands of the desired identity are interval integrable
  have hintA : IntervalIntegrable (fun z : ℝ => c z * G1 α m c z / z ^ 4) volume x y :=
    ((hcc.mul hgc).div hden hne4).intervalIntegrable_of_Icc hxy.le
  have hintB : IntervalIntegrable (fun z : ℝ => G1 α m c z ^ 2 / z ^ 4) volume x y :=
    ((hgc.pow 2).div hden hne4).intervalIntegrable_of_Icc hxy.le
  have hcontD : ContinuousOn
      (fun z : ℝ => (2 * c z * G1 α m c z - (3 + 2 * G1a α m) * G1 α m c z ^ 2) / z ^ 4)
      (Set.Icc x y) :=
    (((continuousOn_const.mul hcc).mul hgc).sub (continuousOn_const.mul (hgc.pow 2))).div
      hden hne4
  have hintD : IntervalIntegrable
      (fun z : ℝ => (2 * c z * G1 α m c z - (3 + 2 * G1a α m) * G1 α m c z ^ 2) / z ^ 4)
      volume x y := hcontD.intervalIntegrable_of_Icc hxy.le
  -- the fundamental theorem of calculus
  have hftc : (∫ z in x..y,
        (2 * c z * G1 α m c z - (3 + 2 * G1a α m) * G1 α m c z ^ 2) / z ^ 4)
      = G1 α m c y ^ 2 / y ^ 3 - G1 α m c x ^ 2 / x ^ 3 :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt
      (f := fun w : ℝ => G1 α m c w ^ 2 / w ^ 3) hF hintD
  -- split the integrand
  have hcongr : (∫ z in x..y,
        (2 * c z * G1 α m c z - (3 + 2 * G1a α m) * G1 α m c z ^ 2) / z ^ 4)
      = ∫ z in x..y,
          (2 * (c z * G1 α m c z / z ^ 4) - (3 + 2 * G1a α m) * (G1 α m c z ^ 2 / z ^ 4)) := by
    refine intervalIntegral.integral_congr (fun z hz => ?_)
    rw [Set.uIcc_of_le hxy.le] at hz
    have hz0 : z ≠ 0 := ne_of_gt (hmem z hz).1
    field_simp
  have hsplit : (∫ z in x..y,
          (2 * (c z * G1 α m c z / z ^ 4) - (3 + 2 * G1a α m) * (G1 α m c z ^ 2 / z ^ 4)))
      = 2 * (∫ z in x..y, c z * G1 α m c z / z ^ 4)
        - (3 + 2 * G1a α m) * (∫ z in x..y, G1 α m c z ^ 2 / z ^ 4) := by
    rw [intervalIntegral.integral_sub (hintA.const_mul 2) (hintB.const_mul (3 + 2 * G1a α m)),
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
  linarith [hftc, hcongr, hsplit]

end Work.FTS.EllExist.Honesty
end
-- ===== merged: Submission.Work.FTS.EllipticEst.AeMom.Defs =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.AeMom

/-- **The weak elliptic class with a.e. angular moment conditions.**  Same fields as
`Work.FTS.EllipticEst.TT.EllWeakPos`, except that the two moment conditions
`Fstar F ≡ 0`, `Fstar Ψ ≡ 0` are required only almost everywhere on `(0,∞)`. -/
def EllWeakPosAe (α : ℝ) (k : ℕ) (F Ψ : ℝ → ℝ → ℝ) : Prop :=
  (∀ z, 0 < z → ∀ θ, 0 < θ → θ < Real.pi / 2 → Work.Elliptic.bslOp α Ψ z θ = F z θ) ∧
  (∀ z, Ψ z 0 = 0) ∧ (∀ z, Ψ z (Real.pi / 2) = 0) ∧
  (∀ᵐ z ∂(volume.restrict (Set.Ioi 0)), Work.Elliptic.Fstar F z = 0) ∧
  (∀ᵐ z ∂(volume.restrict (Set.Ioi 0)), Work.Elliptic.Fstar Ψ z = 0) ∧
  (∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry Ψ) (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2))) ∧
  Work.Spaces.HkMem α k F ∧
  Work.Spaces.HkMem α k (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) ∧
  Work.Spaces.HkMem α k (Work.Spaces.pthIter 2 Ψ)




/-! ## Accessors, mirroring `TT.EllWeakPos`'s

These are named exactly as the ones of `TT.EllWeakPos` (`TT/WeakDefs.lean`), so that a proof
written for `TT.EllWeakPos` can be re-pointed at `EllWeakPosAe` by replacing the class name: the
only two fields whose *shape* differs are `orthF`/`orthPsi` (the a.e. moment conditions). -/

theorem EllWeakPosAe.eq {α : ℝ} {k : ℕ} {F Ψ : ℝ → ℝ → ℝ} (h : EllWeakPosAe α k F Ψ) :
    ∀ z, 0 < z → ∀ θ, 0 < θ → θ < Real.pi / 2 → Work.Elliptic.bslOp α Ψ z θ = F z θ := h.1

theorem EllWeakPosAe.zero {α : ℝ} {k : ℕ} {F Ψ : ℝ → ℝ → ℝ} (h : EllWeakPosAe α k F Ψ) :
    ∀ z, Ψ z 0 = 0 := h.2.1

theorem EllWeakPosAe.pi_half {α : ℝ} {k : ℕ} {F Ψ : ℝ → ℝ → ℝ} (h : EllWeakPosAe α k F Ψ) :
    ∀ z, Ψ z (Real.pi / 2) = 0 := h.2.2.1

theorem EllWeakPosAe.orthF {α : ℝ} {k : ℕ} {F Ψ : ℝ → ℝ → ℝ} (h : EllWeakPosAe α k F Ψ) :
    ∀ᵐ z ∂(volume.restrict (Set.Ioi 0)), Work.Elliptic.Fstar F z = 0 := h.2.2.2.1

theorem EllWeakPosAe.orthPsi {α : ℝ} {k : ℕ} {F Ψ : ℝ → ℝ → ℝ} (h : EllWeakPosAe α k F Ψ) :
    ∀ᵐ z ∂(volume.restrict (Set.Ioi 0)), Work.Elliptic.Fstar Ψ z = 0 := h.2.2.2.2.1

theorem EllWeakPosAe.smooth {α : ℝ} {k : ℕ} {F Ψ : ℝ → ℝ → ℝ} (h : EllWeakPosAe α k F Ψ) :
    ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry Ψ)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) := h.2.2.2.2.2.1

theorem EllWeakPosAe.memF {α : ℝ} {k : ℕ} {F Ψ : ℝ → ℝ → ℝ} (h : EllWeakPosAe α k F Ψ) :
    Work.Spaces.HkMem α k F := h.2.2.2.2.2.2.1

theorem EllWeakPosAe.memA {α : ℝ} {k : ℕ} {F Ψ : ℝ → ℝ → ℝ} (h : EllWeakPosAe α k F Ψ) :
    Work.Spaces.HkMem α k (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) :=
  h.2.2.2.2.2.2.2.1

theorem EllWeakPosAe.memB {α : ℝ} {k : ℕ} {F Ψ : ℝ → ℝ → ℝ} (h : EllWeakPosAe α k F Ψ) :
    Work.Spaces.HkMem α k (Work.Spaces.pthIter 2 Ψ) := h.2.2.2.2.2.2.2.2


end Work.FTS.EllipticEst.AeMom
end
end
-- ===== merged: Submission.Work.FTS.EllipticEst.AngAWeak.AeTruncWDefs =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `AngAWeak.AeTruncWDefs` — the vocabulary of the truncated `w²`-energy identity

This module fixes the objects used by the proof of

`Work.FTS.EllipticEst.AngAWeak.aeTruncIdentW`:

for `AeData α u G` (the almost-everywhere class of the level-`0` elliptic estimate), the
truncated `w²`-energy identity

`∫_z W w² (∫_θ G u) = α² ∫_z W w² z² (∫_θ (∂_zu)²) + ∫_z W w² (∫_θ (L₀u) u)
   - (α²/2) ∫_z (W w² z²)'' (∫_θ u²) + (α(5+α)/2) ∫_z (W w² z)' (∫_θ u²)`

holds for every `W ∈ C²` with compact support vanishing near `0`.

## The weight

* `sigW W z = W z · w z²` is the radial weight `σ` multiplying the solutions `u`;
* `sigW2 W z = z²·σ z` is the weight of `∂_zzu` (the `z²σ` of the integration by parts
  `∫ σ z² φ'' φ = ½∫ (σ z²)'' φ² - ∫ σ (z φ')²`);
* `sigW1 W z = z·σ z` is the weight of `∂_zu` (the `zσ` of `∫ σ z φ' φ = -½∫ (zσ)' φ²`).

## Getting rid of the irrelevant `z ≤ 0` and `z ≤ δ`

All the integrals of the identity are over `Set.Ioi 0`, while the norms of `Work.Spaces` are
stated over `Iz = [0,∞)`.  The two measures agree (`restrict_Iz_eq_restrict_Ioi`), and the
weight `σ` is supported in the region where `W ≠ 0`, which is why the whole identity can be
proved on a compact interval `[a,b]` containing the support of `W` in its interior
(`exists_bound_W` produces the upper end of that support).
-/

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.AngAWeak

set_option autoImplicit false

/-- The radial weight of the truncated identity: `σ(z) = W(z)·w(z)²`. -/
def sigW (W : ℝ → ℝ) : ℝ → ℝ := fun z => W z * (Work.Spaces.w z) ^ 2

/-- `σ(z)·z²`, the weight multiplying `∂_zzu` (the weight of `ibpZZ`). -/
def sigW2 (W : ℝ → ℝ) : ℝ → ℝ := fun z => z ^ 2 * sigW W z

/-- `σ(z)·z`, the weight multiplying `∂_zu` (the weight of `ibpZ`). -/
def sigW1 (W : ℝ → ℝ) : ℝ → ℝ := fun z => z * sigW W z

@[simp] theorem sigW_apply (W : ℝ → ℝ) (z : ℝ) :
    sigW W z = W z * (Work.Spaces.w z) ^ 2 := rfl

@[simp] theorem sigW2_apply (W : ℝ → ℝ) (z : ℝ) : sigW2 W z = z ^ 2 * sigW W z := rfl

@[simp] theorem sigW1_apply (W : ℝ → ℝ) (z : ℝ) : sigW1 W z = z * sigW W z := rfl

/-- The restricted Lebesgue measure on `Iz = [0,∞)` is the restricted Lebesgue measure on
`(0,∞)`: the two differ by the null set `{0}`. -/
theorem restrict_Iz_eq_restrict_Ioi :
    MeasureTheory.volume.restrict Work.Spaces.Iz
      = MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ)) := by
  have h : Set.Ioi (0 : ℝ) =ᵐ[MeasureTheory.volume] Set.Ici (0 : ℝ) :=
    MeasureTheory.Ioi_ae_eq_Ici
  have h2 := MeasureTheory.Measure.restrict_congr_set h
  exact h2.symm

/-- `z`-set integrals over `Iz = [0,∞)` and over `(0,∞)` agree. -/
theorem setIntegral_Iz_eq_Ioi (f : ℝ → ℝ) :
    (∫ z in Work.Spaces.Iz, f z) = ∫ z in Set.Ioi (0 : ℝ), f z := by
  rw [← restrict_Iz_eq_restrict_Ioi]

/-- A `C²` function with compact support on `ℝ` is supported in `(-∞,R]` for some `R > 0`. -/
theorem exists_bound_W (W : ℝ → ℝ) (hcpt : HasCompactSupport W) :
    ∃ R : ℝ, 0 < R ∧ ∀ z : ℝ, R ≤ z → W z = 0 := by
  obtain ⟨b, hb⟩ := hcpt.bddAbove
  refine ⟨max b 0 + 1, by positivity, fun z hz => ?_⟩
  by_contra hne
  have hmem : z ∈ tsupport W := subset_tsupport W (Function.mem_support.mpr hne)
  have h1 : z ≤ b := hb hmem
  have h2 : b ≤ max b 0 := le_max_left b 0
  linarith

end Work.FTS.EllipticEst.AngAWeak
end
end
-- ===== merged: Submission.Work.FTS.EllipticEst.AngAWeak.CorrPieces.EndDecayAux =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.AngAWeak.CorrPieces

set_option autoImplicit false




end Work.FTS.EllipticEst.AngAWeak.CorrPieces
end
end
-- ===== merged: Submission.Work.FTS.EllipticEst.AngAWeak.SRSAux.BfluxDeriv =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology

namespace Work.FTS.EllipticEst.AngAWeak.SRSAux


end Work.FTS.EllipticEst.AngAWeak.SRSAux
end
end
-- ===== merged: Submission.Work.FTS.EllipticEst.AngAWeak.SRSAux.WnDeriv =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.AngAWeak.SRSAux


end Work.FTS.EllipticEst.AngAWeak.SRSAux
end
-- ===== merged: Submission.Work.FTS.EllipticEst.AngAWeak.aeTruncAux =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# Auxiliary quantities for `aeTruncIdent`

The radial `z`-integration by parts of the truncated energy identity is carried out slice by
slice in `θ`; the analytic inputs of the weak class (`AeData`) are three weighted angular
masses of a slice and their pointwise bounds.

* `AAA u z = ∫_θ (∂_θθu(z,·))² · sin(2θ)^{-η}` — the angular `H²`-mass of the slice
  (`HkIntegrand α 0 (pthIter 2 u) = w z ^ 2 * AAA u z` on `Iθ`, so the `AeData`-hypothesis
  `HkMem α 0 (pthIter 2 u)` says exactly that `z ↦ (w z)^2 * AAA u z` is integrable on `Iz`);
* `BBB u z = ∫_θ (z²∂_zzu(z,·))² · sin(2θ)^{-η}` — the same for the radial second derivative;
* `GGG G z = ∫_θ (G(z,·))² · sin(2θ)^{-η}` — the angular mass of the source.

The two `AeData`-hypotheses `HkMem α 0 (fun z θ => z^2 * pzIter 2 u z θ)` and
`HkMem α 0 G` are the corresponding `z`-integrability statements for `(w z)^2 * BBB u z` and
`(w z)^2 * GGG G z`.
-/

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.AngAWeak

set_option autoImplicit false





end Work.FTS.EllipticEst.AngAWeak
end
end
-- ===== merged: Submission.Work.FTS.EllipticEst.AngAWeak.sliceGronwallInterface =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.AngAWeak


end Work.FTS.EllipticEst.AngAWeak
end
-- ===== merged: Submission.Work.FTS.EllipticEst.AngAWeak.sliceGronwallPointwise =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open Set Filter Topology

namespace Work.FTS.EllipticEst.AngAWeak


end Work.FTS.EllipticEst.AngAWeak
end
-- ===== merged: Submission.Work.FTS.EllipticEst.AngAWeak.sliceSecondNonpos =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.AngAWeak

set_option autoImplicit false
set_option maxHeartbeats 1600000

/-! ## The mirror change of variables -/



/-! ## The right half, by reflection -/


/-! ## The dichotomy -/


end Work.FTS.EllipticEst.AngAWeak
end
end
-- ===== merged: Submission.Work.FTS.EllipticEst.AngClean.HkMem_zero_IPMem =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.AngClean

open MeasureTheory Set Filter
open scoped Real Topology

/-- At `k = 0` the `H^k`-integrand collapses to the single square
`(g z θ · w z / sin(2θ)^{η/2})²`: the `D_z`-sum has the one term `i = 0` and the mixed
double sum is empty. -/
private lemma HkIntegrand_zero_eq (α : ℝ) (g : ℝ → ℝ → ℝ) (z θ : ℝ) :
    Work.Spaces.HkIntegrand α 0 g z θ
      = (g z θ * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2 := by
  simp [Work.Spaces.HkIntegrand]

/-- **The bridge `HkMem α 0 g ⟹ IPMem g g`.**

`Work.Spaces.HkMem α 0 g` is the honesty of `HkIntegrand α 0 g`, whose only summand is
`(g z θ · w z / sin(2θ)^(η/2))²`; `AngSecond.IPMem g g` is the honesty of
`g z θ · g z θ · w z² · σ θ`.  The bridge is the pointwise identity `AngSecond.sq_mul_W`,
valid for every `θ ∈ Iθ` (its endpoint case `sin(2θ) = 0` is handled by `Real.zero_rpow`), so
both conjuncts transfer by `IntegrableOn.congr`. -/
theorem HkMem_zero_IPMem {α : ℝ} {g : ℝ → ℝ → ℝ} (h : Work.Spaces.HkMem α 0 g) :
    Work.FTS.EllipticEst.AngSecond.IPMem g g := by
  -- `HkMem α 0 g` is the honesty of `(g z θ · w z / sin(2θ)^{η/2})²`.
  have hsq : ∀ z θ, θ ∈ Work.Spaces.Iθ → Work.Spaces.HkIntegrand α 0 g z θ
      = g z θ * g z θ * Work.FTS.EllipticEst.AngSecond.w2 z
          * Work.FTS.EllipticEst.AngSecond.sig θ :=
    fun z θ hθ => by rw [HkIntegrand_zero_eq α g z θ,
      Work.FTS.EllipticEst.AngSecond.sq_mul_W g hθ]
  -- The `θ`-slice of `IP g g` at a fixed `z`, written as the iterated integral of the
  -- `HkIntegrand`.
  have hslice : ∀ z, (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 0 g z θ)
      = ∫ θ in Work.Spaces.Iθ, g z θ * g z θ * Work.FTS.EllipticEst.AngSecond.w2 z
          * Work.FTS.EllipticEst.AngSecond.sig θ :=
    fun z => setIntegral_congr_fun measurableSet_Icc (fun θ hθ => hsq z θ hθ)
  constructor
  · -- Slicewise honesty, transferred by `IntegrableOn.congr_fun`.
    intro z hz
    exact MeasureTheory.IntegrableOn.congr_fun (h.1 z hz)
      (fun θ hθ => hsq z θ hθ) measurableSet_Icc
  · -- Outer honesty, transferred by `IntegrableOn.congr_fun` and the slice identity.
    exact MeasureTheory.IntegrableOn.congr_fun h.2 (fun z _ => hslice z) measurableSet_Ici

end Work.FTS.EllipticEst.AngClean
end
-- ===== merged: Submission.Work.FTS.EllipticEst.AngClean.step2_collection =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.AngClean



end Work.FTS.EllipticEst.AngClean
end
-- ===== merged: Submission.Work.FTS.EllipticEst.AngSecond.I4_aux_defs =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.AngSecond

set_option autoImplicit false
set_option linter.unusedSimpArgs false

/-- The coefficient `A(θ) = ((1-η)/2)·cos 2θ + 2 sin²θ` of the `I₄`-identity. -/
def acoef (θ : ℝ) : ℝ := ((1 - Work.Spaces.eta) / 2) * Real.cos (2 * θ) + 2 * (Real.sin θ) ^ 2

/-- The primitive `G(θ) = (1/2)·sin θ cos θ·σ(θ)·((u/cos)'(θ)² - (u/cos)(θ)²)` of the
`I₄`-identity, where `σ = sig`. -/
def Gprim (u : ℝ → ℝ) (θ : ℝ) : ℝ :=
  (1 / 2) * (Real.sin θ * Real.cos θ * sig θ)
    * ((deriv (fun θ' => u θ' / Real.cos θ') θ) ^ 2 - (u θ / Real.cos θ) ^ 2)

/-- The derivative of `Gprim u` on `(0, π/2)`: the integrand of the `I₄`-identity. -/
def Hintegrand (u : ℝ → ℝ) (θ : ℝ) : ℝ :=
  acoef θ * (deriv (fun θ' => u θ' / Real.cos θ') θ) ^ 2 * sig θ
    + Real.sin θ * deriv (fun θ' => u θ' / Real.cos θ') θ * deriv (deriv u) θ * sig θ
    - ((1 - Work.Spaces.eta) / 2) * Real.cos (2 * θ) * (u θ / Real.cos θ) ^ 2 * sig θ

/-- `1 - η > 0`, where `η = 99/100`. -/
theorem one_sub_eta_pos : 0 < 1 - Work.Spaces.eta := by
  rw [Work.Spaces.eta]; norm_num

/-- `A(θ) = (1-η)/2 + (1+η)·sin²θ`, the form in which nonnegativity is visible. -/
theorem acoef_eq (θ : ℝ) :
    acoef θ = (1 - Work.Spaces.eta) / 2 + (1 + Work.Spaces.eta) * (Real.sin θ) ^ 2 := by
  have hc : Real.cos θ ^ 2 = 1 - Real.sin θ ^ 2 := by
    linarith [Real.cos_sq_add_sin_sq θ]
  rw [acoef, Real.cos_two_mul, hc]; ring

theorem acoef_nonneg (θ : ℝ) : 0 ≤ acoef θ := by
  rw [acoef_eq]
  have h2 : (0:ℝ) ≤ (Real.sin θ) ^ 2 := sq_nonneg _
  have h4 : (0:ℝ) ≤ 1 + Work.Spaces.eta := by rw [Work.Spaces.eta]; norm_num
  have h3 : (0:ℝ) < 1 - Work.Spaces.eta := one_sub_eta_pos
  nlinarith



end Work.FTS.EllipticEst.AngSecond
end
end
-- ===== merged: Submission.Work.FTS.EllipticEst.AngSecond.I4_psi_bounds_alt =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.AngSecond

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option linter.unusedSimpArgs false

/-! ## Trigonometric helpers -/

theorem sin_quarter_pos : (0 : ℝ) < Real.sin (1 / 4) :=
  Real.sin_pos_of_pos_of_lt_pi (by norm_num) (by linarith [Real.pi_gt_three])

theorem cos_quarter_pos : (0 : ℝ) < Real.cos (1 / 4) :=
  Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], by linarith [Real.pi_gt_three]⟩

/-- `sin t ≥ t·cos(1/4)` for `0 < t ≤ 1/4`. -/
theorem sin_ge_mul_cos_quarter {t : ℝ} (h0 : 0 < t) (h1 : t ≤ 1 / 4) :
    t * Real.cos (1 / 4) ≤ Real.sin t := by
  obtain ⟨c, hc, hcval⟩ := exists_deriv_eq_slope Real.sin h0
    Real.continuous_sin.continuousOn Real.differentiable_sin.differentiableOn
  have hcos : Real.cos (1 / 4) ≤ Real.cos c :=
    Real.cos_le_cos_of_nonneg_of_le_pi (le_of_lt hc.1) (by linarith [Real.pi_gt_three])
      (by linarith [hc.2, h1])
  have hval : Real.sin t = t * Real.cos c := by
    have ht : t ≠ 0 := ne_of_gt h0
    rw [Real.deriv_sin, Real.sin_zero, sub_zero] at hcval
    rw [hcval, mul_div_assoc', mul_comm t (Real.sin t), sub_zero]
    field_simp
  rw [hval]
  exact mul_le_mul_of_nonneg_left hcos (le_of_lt h0)

/-- `|sin t - t cos t| ≤ t²` for `0 ≤ t`. -/
theorem abs_sin_sub_mul_cos_le {t : ℝ} (h0 : 0 ≤ t) :
    |Real.sin t - t * Real.cos t| ≤ t ^ 2 := by
  have hInt : (∫ s in (0 : ℝ)..t, s * Real.sin s) = Real.sin t - t * Real.cos t := by
    have hd : ∀ s ∈ Set.uIcc (0 : ℝ) t,
        HasDerivAt (fun s : ℝ => Real.sin s - s * Real.cos s) (s * Real.sin s) s := by
      intro s _
      have h1 : HasDerivAt (fun s : ℝ => Real.sin s) (Real.cos s) s := Real.hasDerivAt_sin s
      have h2 : HasDerivAt (fun s : ℝ => s * Real.cos s) (Real.cos s - s * Real.sin s) s := by
        have h := (hasDerivAt_id s).mul (Real.hasDerivAt_cos s)
        convert h using 1
        · ext x; simp [Pi.mul_apply]
        · simp only [id_eq]; ring
      have h3 := h1.sub h2
      convert h3 using 1
      ring
    have h := intervalIntegral.integral_eq_sub_of_hasDerivAt hd
      ((continuous_id.mul Real.continuous_sin).intervalIntegrable 0 t)
    simpa using h
  have hsin1 : ∀ s : ℝ, |Real.sin s| ≤ 1 := fun s =>
    abs_le.mpr ⟨Real.neg_one_le_sin s, Real.sin_le_one s⟩
  rw [← hInt]
  calc |∫ s in (0 : ℝ)..t, s * Real.sin s|
      ≤ ∫ s in (0 : ℝ)..t, |s * Real.sin s| := by
        simpa [Real.norm_eq_abs] using
          intervalIntegral.norm_integral_le_integral_norm (f := fun s => s * Real.sin s) h0
    _ ≤ ∫ s in (0 : ℝ)..t, s := by
        refine intervalIntegral.integral_mono_on h0 ?_ ?_ ?_
        · exact (continuous_abs.comp (continuous_id.mul Real.continuous_sin)).intervalIntegrable 0 t
        · exact continuous_id.intervalIntegrable 0 t
        · intro s hs
          calc |s * Real.sin s| = s * |Real.sin s| := by rw [abs_mul, abs_of_nonneg hs.1]
            _ ≤ s * 1 := mul_le_mul_of_nonneg_left (hsin1 s) hs.1
            _ = s := mul_one s
    _ = t ^ 2 / 2 := by rw [integral_id]; ring
    _ ≤ t ^ 2 := by nlinarith [h0]

/-- `sin(1/4) ≤ cos θ` for `0 ≤ θ ≤ π/2 - 1/4`. -/
theorem sin_quarter_le_cos {θ : ℝ} (h0 : 0 ≤ θ) (h1 : θ ≤ Real.pi / 2 - 1 / 4) :
    Real.sin (1 / 4) ≤ Real.cos θ := by
  have h := Real.cos_le_cos_of_nonneg_of_le_pi (x := θ) (y := Real.pi / 2 - 1 / 4) h0
    (by linarith [Real.pi_gt_three]) h1
  rwa [Real.cos_pi_div_two_sub] at h

/-- Mean value bound: `|f y - f x| ≤ M (y - x)` when `|f'| ≤ M` on `(x,y)`. -/
theorem abs_sub_le_of_abs_deriv_le {f : ℝ → ℝ} {x y M : ℝ} (hxy : x ≤ y)
    (hcont : ContinuousOn f (Set.Icc x y)) (hdiff : DifferentiableOn ℝ f (Set.Ioo x y))
    (hM : ∀ t ∈ Set.Ioo x y, |deriv f t| ≤ M) :
    |f y - f x| ≤ M * (y - x) := by
  rcases eq_or_lt_of_le hxy with h | h
  · subst h; simp
  · obtain ⟨c, hc, hcval⟩ := exists_deriv_eq_slope f h hcont hdiff
    have hpos : (0 : ℝ) < y - x := by linarith
    have key : f y - f x = deriv f c * (y - x) := by
      rw [hcval]; field_simp
    calc |f y - f x| = |deriv f c| * (y - x) := by rw [key, abs_mul, abs_of_pos hpos]
      _ ≤ M * (y - x) := mul_le_mul_of_nonneg_right (hM c hc) (le_of_lt hpos)

/-- The derivative of `θ ↦ u θ / cos θ` on the open quadrant. -/
theorem deriv_div_cos_eq (u : ℝ → ℝ) {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2))
    (hd : DifferentiableAt ℝ u θ) :
    deriv (fun θ' => u θ' / Real.cos θ') θ
      = (deriv u θ * Real.cos θ + u θ * Real.sin θ) / Real.cos θ ^ 2 := by
  have hcos : Real.cos θ ≠ 0 :=
    ne_of_gt (Real.cos_pos_of_mem_Ioo ⟨by linarith [hθ.1, Real.pi_pos], hθ.2⟩)
  rw [show (fun θ' => u θ' / Real.cos θ') = u / Real.cos by funext x; rfl]
  rw [deriv_div hd Real.differentiableAt_cos hcos, Real.deriv_cos]
  ring

/-- Fallback proof of the endpoint bounds for `Ψ̄ = u / cos θ`. -/
theorem I4_psi_bounds_alt (u : ℝ → ℝ) (hu : ContDiffOn ℝ 2 u (Set.Ioo (-1) (Real.pi / 2 + 1)))
    (hu1 : u (Real.pi / 2) = 0) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ θ ∈ Set.Ioo 0 (Real.pi / 2),
      |u θ / Real.cos θ| ≤ C ∧ |deriv (fun θ' => u θ' / Real.cos θ') θ| ≤ C := by
  have hπ : (0 : ℝ) < Real.pi / 2 := by linarith [Real.pi_pos]
  set s : Set ℝ := Set.Ioo (-1 : ℝ) (Real.pi / 2 + 1) with hs
  have hsopen : IsOpen s := isOpen_Ioo
  have hsub : Set.Icc (0 : ℝ) (Real.pi / 2) ⊆ s := fun x hx =>
    ⟨by linarith [hx.1], by linarith [hx.2, Real.pi_pos]⟩
  have hcu : ContinuousOn u (Set.Icc 0 (Real.pi / 2)) := hu.continuousOn.mono hsub
  have hcu1 : ContinuousOn (deriv u) (Set.Icc 0 (Real.pi / 2)) :=
    (hu.continuousOn_deriv_of_isOpen hsopen (by norm_num)).mono hsub
  have hcu2 : ContinuousOn (deriv (deriv u)) (Set.Icc 0 (Real.pi / 2)) :=
    ((hu.deriv_of_isOpen (m := 1) hsopen (by norm_num)).continuousOn_deriv_of_isOpen hsopen
      (by norm_num)).mono hsub
  obtain ⟨M0, hM0⟩ := isCompact_Icc.exists_bound_of_continuousOn hcu
  obtain ⟨M1, hM1⟩ := isCompact_Icc.exists_bound_of_continuousOn hcu1
  obtain ⟨M2, hM2⟩ := isCompact_Icc.exists_bound_of_continuousOn hcu2
  have hM0' : ∀ x ∈ Set.Icc (0 : ℝ) (Real.pi / 2), |u x| ≤ M0 := fun x hx => by
    simpa [Real.norm_eq_abs] using hM0 x hx
  have hM1' : ∀ x ∈ Set.Icc (0 : ℝ) (Real.pi / 2), |deriv u x| ≤ M1 := fun x hx => by
    simpa [Real.norm_eq_abs] using hM1 x hx
  have hM2' : ∀ x ∈ Set.Icc (0 : ℝ) (Real.pi / 2), |deriv (deriv u) x| ≤ M2 := fun x hx => by
    simpa [Real.norm_eq_abs] using hM2 x hx
  have hIcc0 : (0 : ℝ) ∈ Set.Icc (0 : ℝ) (Real.pi / 2) := ⟨le_refl 0, le_of_lt hπ⟩
  have hM0nn : 0 ≤ M0 := le_trans (abs_nonneg (u 0)) (hM0' 0 hIcc0)
  have hM1nn : 0 ≤ M1 := le_trans (abs_nonneg (deriv u 0)) (hM1' 0 hIcc0)
  have hM2nn : 0 ≤ M2 := le_trans (abs_nonneg (deriv (deriv u) 0)) (hM2' 0 hIcc0)
  have hdiffu : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2), DifferentiableAt ℝ u θ := fun θ hθ =>
    (hu.contDiffAt (Ioo_mem_nhds (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos]))).differentiableAt
      (by simp)
  -- ## (A) first order bound at `π/2`
  have hA : ∀ θ ∈ Set.Icc (0 : ℝ) (Real.pi / 2), |u θ| ≤ M1 * (Real.pi / 2 - θ) := by
    intro θ hθ
    have hcont : ContinuousOn u (Set.Icc θ (Real.pi / 2)) :=
      hcu.mono fun x hx => ⟨le_trans hθ.1 hx.1, hx.2⟩
    have hdiff : DifferentiableOn ℝ u (Set.Ioo θ (Real.pi / 2)) :=
      (hu.differentiableOn (by simp)).mono fun x hx =>
        ⟨by linarith [hx.1, hθ.1], by linarith [hx.2, Real.pi_pos]⟩
    have hle := abs_sub_le_of_abs_deriv_le hθ.2 hcont hdiff
      (fun t ht => hM1' t ⟨by linarith [ht.1, hθ.1], le_of_lt ht.2⟩)
    rw [hu1] at hle
    simpa using hle
  -- ## (C) Lipschitz bound for `deriv u` at `π/2`
  have hCb : ∀ θ ∈ Set.Icc (0 : ℝ) (Real.pi / 2),
      |deriv u θ - deriv u (Real.pi / 2)| ≤ M2 * (Real.pi / 2 - θ) := by
    intro θ hθ
    have hcont : ContinuousOn (deriv u) (Set.Icc θ (Real.pi / 2)) :=
      hcu1.mono fun x hx => ⟨le_trans hθ.1 hx.1, hx.2⟩
    have hdiff : DifferentiableOn ℝ (deriv u) (Set.Ioo θ (Real.pi / 2)) :=
      ((hu.deriv_of_isOpen (m := 1) hsopen (by norm_num)).differentiableOn (by simp)).mono
        fun x hx => ⟨by linarith [hx.1, hθ.1], by linarith [hx.2, Real.pi_pos]⟩
    have hle := abs_sub_le_of_abs_deriv_le hθ.2 hcont hdiff
      (fun t ht => hM2' t ⟨by linarith [ht.1, hθ.1], le_of_lt ht.2⟩)
    rwa [abs_sub_comm] at hle
  -- ## (B) second order bound at `π/2`
  have hdg : ∀ t ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      deriv (fun s => u s - deriv u (Real.pi / 2) * (s - Real.pi / 2)) t
        = deriv u t - deriv u (Real.pi / 2) := by
    intro t ht
    have h1 : HasDerivAt u (deriv u t) t := (hdiffu t ht).hasDerivAt
    have h2 : HasDerivAt (fun s : ℝ => deriv u (Real.pi / 2) * (s - Real.pi / 2))
        (deriv u (Real.pi / 2)) t := by
      have h := ((hasDerivAt_id t).sub_const (Real.pi / 2)).const_mul (deriv u (Real.pi / 2))
      simpa using h
    have h3 := (h1.sub h2).deriv
    have h4 : (fun s : ℝ => u s - deriv u (Real.pi / 2) * (s - Real.pi / 2))
        = (u - fun s : ℝ => deriv u (Real.pi / 2) * (s - Real.pi / 2)) := by
      ext x; rfl
    rw [h4]
    exact h3
  have hB : ∀ θ ∈ Set.Icc (0 : ℝ) (Real.pi / 2),
      |u θ - deriv u (Real.pi / 2) * (θ - Real.pi / 2)| ≤ M2 * (Real.pi / 2 - θ) ^ 2 := by
    intro θ hθ
    have hcont : ContinuousOn (fun s => u s - deriv u (Real.pi / 2) * (s - Real.pi / 2))
        (Set.Icc θ (Real.pi / 2)) :=
      (hcu.sub (continuousOn_const.mul (continuousOn_id.sub continuousOn_const))).mono
        (fun x hx => ⟨le_trans hθ.1 hx.1, hx.2⟩)
    have hdiff : DifferentiableOn ℝ (fun s => u s - deriv u (Real.pi / 2) * (s - Real.pi / 2))
        (Set.Ioo θ (Real.pi / 2)) :=
      ((hu.differentiableOn (by simp)).mono (fun x hx =>
          ⟨by linarith [hx.1, hθ.1], by linarith [hx.2, Real.pi_pos]⟩)).sub
        ((DifferentiableOn.mul (differentiableOn_const (deriv u (Real.pi / 2)))
            (differentiableOn_id.sub (differentiableOn_const (Real.pi / 2)))).mono
          (fun x _ => trivial))
    have hMg : ∀ t ∈ Set.Ioo θ (Real.pi / 2),
        |deriv (fun s => u s - deriv u (Real.pi / 2) * (s - Real.pi / 2)) t|
          ≤ M2 * (Real.pi / 2 - θ) := by
      intro t ht
      rw [hdg t ⟨by linarith [ht.1, hθ.1], by linarith [ht.2, Real.pi_pos]⟩]
      have h1 := hCb t ⟨by linarith [ht.1, hθ.1], le_of_lt ht.2⟩
      have h2 : Real.pi / 2 - t ≤ Real.pi / 2 - θ := by linarith [ht.1]
      exact le_trans h1 (mul_le_mul_of_nonneg_left h2 hM2nn)
    have hle := abs_sub_le_of_abs_deriv_le hθ.2 hcont hdiff hMg
    have hg0 : u (Real.pi / 2) - deriv u (Real.pi / 2) * (Real.pi / 2 - Real.pi / 2) = 0 := by
      rw [hu1]; ring
    rw [hg0, zero_sub] at hle
    simp only [abs_neg] at hle
    have : (M2 * (Real.pi / 2 - θ)) * (Real.pi / 2 - θ) = M2 * (Real.pi / 2 - θ) ^ 2 := by ring
    rw [this] at hle
    simpa using hle
  -- ## the two bounds
  refine ⟨max (max (M0 / Real.sin (1 / 4)) ((M1 + M0) / Real.sin (1 / 4) ^ 2))
      (max (M1 / Real.cos (1 / 4)) ((M1 + 2 * M2) / Real.cos (1 / 4) ^ 2)), ?_, ?_⟩
  · have h1 : 0 ≤ Real.sin (1 / 4) := le_of_lt sin_quarter_pos
    exact le_max_of_le_left (le_max_of_le_left (div_nonneg hM0nn h1))
  · intro θ hθ
    have hθI : θ ∈ Set.Icc (0 : ℝ) (Real.pi / 2) := ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩
    have hdθ : DifferentiableAt ℝ u θ := hdiffu θ hθ
    rcases le_or_gt θ (Real.pi / 2 - 1 / 4) with hle | hlt
    · -- case 1 : θ ≤ π/2 - 1/4
      have hc1 : (0 : ℝ) < Real.sin (1 / 4) := sin_quarter_pos
      have hcos_ge : Real.sin (1 / 4) ≤ Real.cos θ := sin_quarter_le_cos (le_of_lt hθ.1) hle
      have hcos_pos : 0 < Real.cos θ := lt_of_lt_of_le hc1 hcos_ge
      have hb1 : |u θ / Real.cos θ| ≤ M0 / Real.sin (1 / 4) := by
        rw [abs_div, abs_of_pos hcos_pos, div_le_div_iff₀ hcos_pos hc1]
        have h2 : |u θ| * Real.sin (1 / 4) ≤ M0 * Real.sin (1 / 4) :=
          mul_le_mul_of_nonneg_right (hM0' θ hθI) (le_of_lt hc1)
        have h3 : M0 * Real.sin (1 / 4) ≤ M0 * Real.cos θ :=
          mul_le_mul_of_nonneg_left hcos_ge hM0nn
        linarith
      have hb2 : |deriv (fun θ' => u θ' / Real.cos θ') θ| ≤ (M1 + M0) / Real.sin (1 / 4) ^ 2 := by
        rw [deriv_div_cos_eq u hθ hdθ]
        have hnum : |deriv u θ * Real.cos θ + u θ * Real.sin θ| ≤ M1 + M0 := by
          have h1 : |deriv u θ * Real.cos θ| ≤ M1 := by
            rw [abs_mul]
            calc |deriv u θ| * |Real.cos θ| ≤ M1 * |Real.cos θ| :=
                  mul_le_mul_of_nonneg_right (hM1' θ hθI) (abs_nonneg _)
              _ ≤ M1 * 1 := mul_le_mul_of_nonneg_left
                  (abs_le.mpr ⟨Real.neg_one_le_cos θ, Real.cos_le_one θ⟩) hM1nn
              _ = M1 := mul_one M1
          have h2 : |u θ * Real.sin θ| ≤ M0 := by
            rw [abs_mul]
            calc |u θ| * |Real.sin θ| ≤ M0 * |Real.sin θ| :=
                  mul_le_mul_of_nonneg_right (hM0' θ hθI) (abs_nonneg _)
              _ ≤ M0 * 1 := mul_le_mul_of_nonneg_left
                  (abs_le.mpr ⟨Real.neg_one_le_sin θ, Real.sin_le_one θ⟩) hM0nn
              _ = M0 := mul_one M0
          calc |deriv u θ * Real.cos θ + u θ * Real.sin θ|
              ≤ |deriv u θ * Real.cos θ| + |u θ * Real.sin θ| := abs_add_le _ _
            _ ≤ M1 + M0 := add_le_add h1 h2
        rw [abs_div, abs_of_pos (pow_pos hcos_pos 2), div_le_div_iff₀ (pow_pos hcos_pos 2) (pow_pos hc1 2)]
        have h4 : Real.sin (1 / 4) ^ 2 ≤ Real.cos θ ^ 2 := by nlinarith [hcos_ge, hc1]
        calc |deriv u θ * Real.cos θ + u θ * Real.sin θ| * Real.sin (1 / 4) ^ 2
            ≤ (M1 + M0) * Real.sin (1 / 4) ^ 2 :=
              mul_le_mul_of_nonneg_right hnum (sq_nonneg _)
          _ ≤ (M1 + M0) * Real.cos θ ^ 2 :=
              mul_le_mul_of_nonneg_left h4 (by linarith [hM1nn, hM0nn])
      exact ⟨le_trans hb1 (le_trans (le_max_left _ _) (le_max_left _ _)),
        le_trans hb2 (le_trans (le_max_right _ _) (le_max_left _ _))⟩
    · -- case 2 : θ > π/2 - 1/4
      have ht0 : 0 < Real.pi / 2 - θ := by linarith [hθ.2]
      have ht1 : Real.pi / 2 - θ ≤ 1 / 4 := by linarith [hlt]
      have hsin_ge : (Real.pi / 2 - θ) * Real.cos (1 / 4) ≤ Real.sin (Real.pi / 2 - θ) :=
        sin_ge_mul_cos_quarter ht0 ht1
      have hcos_eq : Real.cos θ = Real.sin (Real.pi / 2 - θ) := (Real.sin_pi_div_two_sub θ).symm
      have hsin_eq : Real.sin θ = Real.cos (Real.pi / 2 - θ) := by
        have h := Real.sin_pi_div_two_sub (Real.pi / 2 - θ)
        rwa [show Real.pi / 2 - (Real.pi / 2 - θ) = θ by ring] at h
      have hcos_pos : 0 < Real.cos θ := by
        rw [hcos_eq]
        exact lt_of_lt_of_le (mul_pos ht0 cos_quarter_pos) hsin_ge
      have htrig : |Real.cos θ - (Real.pi / 2 - θ) * Real.sin θ| ≤ (Real.pi / 2 - θ) ^ 2 := by
        rw [hcos_eq, hsin_eq]
        exact abs_sin_sub_mul_cos_le (le_of_lt ht0)
      have hb1 : |u θ / Real.cos θ| ≤ M1 / Real.cos (1 / 4) := by
        rw [abs_div, abs_of_pos hcos_pos, div_le_div_iff₀ hcos_pos cos_quarter_pos, hcos_eq]
        calc |u θ| * Real.cos (1 / 4)
            ≤ (M1 * (Real.pi / 2 - θ)) * Real.cos (1 / 4) :=
              mul_le_mul_of_nonneg_right (hA θ hθI) (le_of_lt cos_quarter_pos)
          _ = M1 * ((Real.pi / 2 - θ) * Real.cos (1 / 4)) := by ring
          _ ≤ M1 * Real.sin (Real.pi / 2 - θ) := mul_le_mul_of_nonneg_left hsin_ge hM1nn
      have hnum : |deriv u θ * Real.cos θ + u θ * Real.sin θ|
          ≤ (M1 + 2 * M2) * (Real.pi / 2 - θ) ^ 2 := by
        have hcos_le_t : |Real.cos θ| ≤ Real.pi / 2 - θ := by
          rw [abs_of_nonneg (le_of_lt hcos_pos), hcos_eq]
          exact Real.sin_le (le_of_lt ht0)
        have hdecomp : deriv u θ * Real.cos θ + u θ * Real.sin θ
            = deriv u (Real.pi / 2) * (Real.cos θ - (Real.pi / 2 - θ) * Real.sin θ)
              + (deriv u θ - deriv u (Real.pi / 2)) * Real.cos θ
              + (u θ - deriv u (Real.pi / 2) * (θ - Real.pi / 2)) * Real.sin θ := by ring
        have hT1 : |deriv u (Real.pi / 2) * (Real.cos θ - (Real.pi / 2 - θ) * Real.sin θ)|
            ≤ M1 * (Real.pi / 2 - θ) ^ 2 := by
          rw [abs_mul]
          exact mul_le_mul (hM1' (Real.pi / 2) ⟨by linarith [Real.pi_pos], le_refl _⟩) htrig
            (abs_nonneg _) hM1nn
        have hT2 : |(deriv u θ - deriv u (Real.pi / 2)) * Real.cos θ|
            ≤ M2 * (Real.pi / 2 - θ) ^ 2 := by
          rw [abs_mul]
          calc |deriv u θ - deriv u (Real.pi / 2)| * |Real.cos θ|
              ≤ (M2 * (Real.pi / 2 - θ)) * (Real.pi / 2 - θ) :=
                mul_le_mul (hCb θ hθI) hcos_le_t (abs_nonneg _) (mul_nonneg hM2nn (le_of_lt ht0))
            _ = M2 * (Real.pi / 2 - θ) ^ 2 := by ring
        have hT3 : |(u θ - deriv u (Real.pi / 2) * (θ - Real.pi / 2)) * Real.sin θ|
            ≤ M2 * (Real.pi / 2 - θ) ^ 2 := by
          rw [abs_mul]
          calc |u θ - deriv u (Real.pi / 2) * (θ - Real.pi / 2)| * |Real.sin θ|
              ≤ (M2 * (Real.pi / 2 - θ) ^ 2) * 1 :=
                mul_le_mul (hB θ hθI)
                  (abs_le.mpr ⟨Real.neg_one_le_sin θ, Real.sin_le_one θ⟩) (abs_nonneg _)
                  (mul_nonneg hM2nn (sq_nonneg _))
            _ = M2 * (Real.pi / 2 - θ) ^ 2 := by ring
        rw [hdecomp]
        calc |deriv u (Real.pi / 2) * (Real.cos θ - (Real.pi / 2 - θ) * Real.sin θ)
              + (deriv u θ - deriv u (Real.pi / 2)) * Real.cos θ
              + (u θ - deriv u (Real.pi / 2) * (θ - Real.pi / 2)) * Real.sin θ|
            ≤ |deriv u (Real.pi / 2) * (Real.cos θ - (Real.pi / 2 - θ) * Real.sin θ)
                + (deriv u θ - deriv u (Real.pi / 2)) * Real.cos θ|
              + |(u θ - deriv u (Real.pi / 2) * (θ - Real.pi / 2)) * Real.sin θ| := abs_add_le _ _
          _ ≤ (|deriv u (Real.pi / 2) * (Real.cos θ - (Real.pi / 2 - θ) * Real.sin θ)|
                + |(deriv u θ - deriv u (Real.pi / 2)) * Real.cos θ|) + M2 * (Real.pi / 2 - θ) ^ 2 :=
              add_le_add (abs_add_le _ _) hT3
          _ ≤ (M1 * (Real.pi / 2 - θ) ^ 2 + M2 * (Real.pi / 2 - θ) ^ 2)
                + M2 * (Real.pi / 2 - θ) ^ 2 := by linarith [hT1, hT2, hT3]
          _ = (M1 + 2 * M2) * (Real.pi / 2 - θ) ^ 2 := by ring
      have hb2 : |deriv (fun θ' => u θ' / Real.cos θ') θ| ≤ (M1 + 2 * M2) / Real.cos (1 / 4) ^ 2 := by
        rw [deriv_div_cos_eq u hθ hdθ, abs_div, abs_of_pos (pow_pos hcos_pos 2),
          div_le_div_iff₀ (pow_pos hcos_pos 2) (pow_pos cos_quarter_pos 2)]
        have hsq : (Real.pi / 2 - θ) ^ 2 * Real.cos (1 / 4) ^ 2 ≤ (Real.cos θ) ^ 2 := by
          rw [hcos_eq]
          have h := pow_le_pow_left₀ (mul_nonneg (le_of_lt ht0) (le_of_lt cos_quarter_pos)) hsin_ge 2
          rwa [show ((Real.pi / 2 - θ) * Real.cos (1 / 4)) ^ 2
            = (Real.pi / 2 - θ) ^ 2 * Real.cos (1 / 4) ^ 2 by ring] at h
        calc |deriv u θ * Real.cos θ + u θ * Real.sin θ| * Real.cos (1 / 4) ^ 2
            ≤ ((M1 + 2 * M2) * (Real.pi / 2 - θ) ^ 2) * Real.cos (1 / 4) ^ 2 :=
              mul_le_mul_of_nonneg_right hnum (sq_nonneg _)
          _ = (M1 + 2 * M2) * ((Real.pi / 2 - θ) ^ 2 * Real.cos (1 / 4) ^ 2) := by ring
          _ ≤ (M1 + 2 * M2) * (Real.cos θ) ^ 2 :=
              mul_le_mul_of_nonneg_left hsq (by linarith [hM1nn, hM2nn])
      exact ⟨le_trans hb1 (le_trans (le_max_left _ _) (le_max_right _ _)),
        le_trans hb2 (le_trans (le_max_right _ _) (le_max_right _ _))⟩
end Work.FTS.EllipticEst.AngSecond
end
end
-- ===== merged: Submission.Work.FTS.EllipticEst.AngSecond.I4_tan_mul_sub_deriv =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.AngSecond

/-- The pointwise identity of the `I₄` computation (Elgindi, Annals 194 (3) 2021, Step 2 of
`prop:H2`): on the open quadrant `0 < θ < π/2`,
`∂_θ(tan θ · u) - u = sin θ · ∂_θ(u / cos θ)`.
Continuity of the two sides on the closed quadrant is *not* asserted (the identity is used
only inside the open interval). -/
theorem I4_tan_mul_sub_deriv (u : ℝ → ℝ) {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2))
    (hu : DifferentiableAt ℝ u θ) :
    deriv (fun θ' => Real.tan θ' * u θ') θ - u θ
      = Real.sin θ * deriv (fun θ' => u θ' / Real.cos θ') θ := by
  have hcos : Real.cos θ ≠ 0 := by
    have h : θ ∈ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2) :=
      ⟨by linarith [hθ.1, Real.pi_pos], hθ.2⟩
    exact ne_of_gt (Real.cos_pos_of_mem_Ioo h)
  have htan : DifferentiableAt ℝ Real.tan θ := Real.differentiableAt_tan.mpr hcos
  rw [show deriv (fun θ' => Real.tan θ' * u θ') θ = deriv (Real.tan * u) θ from rfl,
    deriv_mul htan hu,
    show deriv (fun θ' => u θ' / Real.cos θ') θ = deriv (u / Real.cos) θ from rfl,
    deriv_div hu Real.differentiableAt_cos hcos,
    Real.deriv_tan θ, Real.deriv_cos, Real.tan_eq_sin_div_cos]
  field_simp
  linear_combination -(u θ) * Real.sin_sq_add_cos_sq θ

end Work.FTS.EllipticEst.AngSecond
end
-- ===== merged: Submission.Work.FTS.EllipticEst.AngSecond.I_identity =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.AngSecond

set_option autoImplicit false
set_option linter.unusedSimpArgs false

/-! ## Two bookkeeping lemmas for the weighted pairing `IP`

`IP g h = ∫_z ∫_θ g z θ * h z θ * w z² * σ θ` is the honest iterated integral of the
angular-weight pairing of `AngSecond/Defs.lean`, and `IPMem g h` is its honesty.  The Step 2
identity `I_identity` below reassembles the five pieces of the paper's computation into the
pairing of the elliptic equation, and needs exactly two facts about `IP`: that it is linear in
its first slot (in finite-sum form), and that it vanishes on functions vanishing in the open
quadrant. -/




end Work.FTS.EllipticEst.AngSecond
end
end
-- ===== merged: Submission.Work.FTS.EllipticEst.AngSecond.SliceIBPDefs =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.AngSecond

set_option autoImplicit false

/-- `s2 θ = sin(2θ)`. -/
def s2 (θ : ℝ) : ℝ := Real.sin (2 * θ)

/-- `c2 θ = cos(2θ)`. -/
def c2 (θ : ℝ) : ℝ := Real.cos (2 * θ)

/-- The angular weight `sigE η θ = sin(2θ)^{-η}` of `slice_ibp_sigma`. -/
def sigE (η θ : ℝ) : ℝ := Real.sin (2 * θ) ^ (-η)

/-- The derivative of `sigE η` on the open interval:
`sigD η θ = -2η cos(2θ) sin(2θ)^{-(1+η)}`. -/
def sigD (η θ : ℝ) : ℝ := -2 * η * Real.cos (2 * θ) * Real.sin (2 * θ) ^ (-(1 + η))

/-- The second derivative of `sigE η` on the open interval:
`sigDD η θ = 4η sin(2θ)^{-η} + 4η(1+η) cos²(2θ) sin(2θ)^{-(2+η)}`. -/
def sigDD (η θ : ℝ) : ℝ :=
  4 * η * sigE η θ
    + 4 * η * (1 + η) * Real.cos (2 * θ) ^ 2 * Real.sin (2 * θ) ^ (-(2 + η))

@[simp] theorem s2_apply (θ : ℝ) : s2 θ = Real.sin (2 * θ) := rfl
@[simp] theorem c2_apply (θ : ℝ) : c2 θ = Real.cos (2 * θ) := rfl
@[simp] theorem sigE_apply (η θ : ℝ) : sigE η θ = Real.sin (2 * θ) ^ (-η) := rfl
@[simp] theorem sigD_apply (η θ : ℝ) :
    sigD η θ = -2 * η * Real.cos (2 * θ) * Real.sin (2 * θ) ^ (-(1 + η)) := rfl
@[simp] theorem sigDD_apply (η θ : ℝ) :
    sigDD η θ = 4 * η * sigE η θ
      + 4 * η * (1 + η) * Real.cos (2 * θ) ^ 2 * Real.sin (2 * θ) ^ (-(2 + η)) := rfl


/-- The set integral over `Work.Spaces.Iθ = [0,π/2]` is the interval integral `0..π/2`. -/
theorem setIntegral_Iθ_eq_interval (g : ℝ → ℝ) :
    (∫ θ in Work.Spaces.Iθ, g θ) = ∫ θ in (0 : ℝ)..(Real.pi / 2), g θ := by
  have hpi2 : (0 : ℝ) ≤ Real.pi / 2 := by positivity
  rw [Work.Spaces.Iθ]
  exact ((intervalIntegral.integral_of_le hpi2).trans
    (MeasureTheory.setIntegral_congr_set (MeasureTheory.Ioc_ae_eq_Icc (μ := volume)))).symm

end Work.FTS.EllipticEst.AngSecond
end
end
-- ===== merged: Submission.Work.FTS.EllipticEst.AngSecond.hardy_slice_cos2 =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.AngSecond

set_option autoImplicit false
set_option linter.unusedSimpArgs false


end Work.FTS.EllipticEst.AngSecond
end
end
-- ===== merged: Submission.Work.FTS.EllipticEst.AngSecond.slice_sq_integral_mul_le =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.AngSecond

open MeasureTheory

/-- **Nonnegativity of a set integral without measurability of the set.**

If `f` is a.e. measurable for `volume.restrict s` and `f ≥ 0` pointwise on `s`, then
`0 ≤ ∫ x in s, f x`.  No measurability of `s` is assumed, which is what the weighted
Cauchy–Schwarz inequality below needs: the slice integrands are only known to be integrable.

Route: if `g` is a measurable function with `f =ᵐ[volume.restrict s] g`, then
`{x | f x < 0} ⊆ {x | f x ≠ g x} ∪ {x | g x < 0}`; the first piece is null by the a.e. equality,
and the second is a *measurable* set, so `Measure.restrict_apply` computes its measure as
`volume ({g < 0} ∩ s)`, which vanishes since `{g < 0} ∩ s ⊆ {f ≠ g} ∩ s` (here `f ≥ 0` on `s` is
used) and `volume ({f ≠ g} ∩ s) ≤ (volume.restrict s) {f ≠ g} = 0`. -/
private lemma setIntegral_nonneg_of_forall_mem {s : Set ℝ} {f : ℝ → ℝ}
    (hf : AEMeasurable f (MeasureTheory.volume.restrict s)) (h : ∀ x ∈ s, 0 ≤ f x) :
    0 ≤ ∫ x in s, f x := by
  obtain ⟨g, hgm, hfg⟩ := hf
  refine MeasureTheory.setIntegral_nonneg_of_ae_restrict ?_
  have hne : (MeasureTheory.volume.restrict s) {x : ℝ | f x ≠ g x} = 0 :=
    (MeasureTheory.ae_iff).mp hfg
  have hmeas : MeasurableSet {x : ℝ | g x < 0} := by
    simpa using measurableSet_lt hgm measurable_const
  have hg0 : (MeasureTheory.volume.restrict s) {x : ℝ | g x < 0} = 0 := by
    rw [MeasureTheory.Measure.restrict_apply hmeas]
    refine MeasureTheory.measure_mono_null ?_
      (MeasureTheory.Measure.measure_inter_eq_zero_of_restrict hne)
    intro x hx
    refine ⟨?_, hx.2⟩
    intro hc
    have h1 : 0 ≤ g x := hc ▸ h x hx.2
    exact absurd h1 (not_le.mpr hx.1)
  have hsub : {x : ℝ | ¬ 0 ≤ f x} ⊆ {x : ℝ | f x ≠ g x} ∪ {x : ℝ | g x < 0} := by
    intro x hx
    by_cases h1 : f x = g x
    · refine Or.inr ?_
      show g x < 0
      rw [← h1]
      exact not_le.mp hx
    · exact Or.inl h1
  have h0 : (MeasureTheory.volume.restrict s) {x : ℝ | ¬ 0 ≤ f x} = 0 := by
    refine MeasureTheory.measure_mono_null hsub ?_
    rw [MeasureTheory.measure_union_null_iff]
    exact ⟨hne, hg0⟩
  exact (MeasureTheory.ae_iff).mpr h0

/-- A real quadratic `t ↦ a - 2 b t + c t²` that is nonnegative for every real `t` has
nonnegative discriminant: `b ^ 2 ≤ a * c`. -/
private lemma quad_nonneg_discr {a b c : ℝ} (h : ∀ t : ℝ, 0 ≤ a - 2 * t * b + t ^ 2 * c) :
    b ^ 2 ≤ a * c := by
  have ha : 0 ≤ a := by simpa using h 0
  -- adding the inequality at `u` and at `-u` kills the linear term
  have hsum : ∀ u : ℝ, 0 ≤ a + u ^ 2 * c := by
    intro u
    nlinarith [h u, h (-u)]
  have hc : 0 ≤ c := by
    by_contra hneg
    simp only [not_le] at hneg
    have hpos : (0 : ℝ) < -c := by linarith
    have hsq : a / (-c) < (a / (-c) + 1) ^ 2 := by
      have hK : 0 ≤ a / (-c) := div_nonneg ha (le_of_lt hpos)
      nlinarith
    have h2 : a < (a / (-c) + 1) ^ 2 * (-c) := (div_lt_iff₀ hpos).mp hsq
    have hbad := hsum (a / (-c) + 1)
    have hfin : a + (a / (-c) + 1) ^ 2 * c < 0 := by nlinarith [h2]
    linarith
  rcases eq_or_lt_of_le hc with hc0 | hcpos
  · -- `c = 0`: the hypothesis forces `b = 0`
    have hb : b = 0 := by
      by_contra hb
      have h' := h ((a + |a| + 1) / (2 * b))
      have h2 : 2 * ((a + |a| + 1) / (2 * b)) * b = a + |a| + 1 := by
        field_simp
      rw [hc0] at h'
      nlinarith [h', h2, abs_nonneg a]
    rw [hb, hc0.symm]
    norm_num
  · -- `c > 0`: evaluate at `t = b / c`
    have hcne : c ≠ 0 := ne_of_gt hcpos
    have h' := h (b / c)
    have h2 : 2 * (b / c) * b = 2 * (b ^ 2 / c) := by ring
    have h3 : (b / c) ^ 2 * c = b ^ 2 / c := by
      rw [div_pow]; field_simp
    rw [h2, h3] at h'
    have h4 : b ^ 2 / c ≤ a := by linarith
    rw [div_le_iff₀ hcpos] at h4
    exact h4

/-- **Weighted Cauchy–Schwarz on a single angular slice.**

For integrable `F²κ`, `G²κ`, `FGκ` with `κ ≥ 0` on `s`, the square of `∫_s FGκ` is bounded by
the product of the integrals of `F²κ` and `G²κ`.  No measurability of `F`, `G` themselves is
assumed (only the three weight products are integrable), which is exactly the form needed by
`IP_cauchy_schwarz`: the slice integrands there are `g²·w²σ`, `h²·w²σ`, `gh·w²σ` and nothing
is known about the measurability of the slices of `g`, `h`.

Route: for every real `t`, the function `(F - t·G)²·κ ≥ 0` is integrable and a.e. strongly
measurable (it is a.e. equal to `F²κ - 2t·FGκ + t²·G²κ`), so `0 ≤ ∫_s (F-tG)²κ`, and by
linearity this is `a - 2bt + ct²` with `a = ∫_s F²κ`, `b = ∫_s FGκ`, `c = ∫_s G²κ`.  A
quadratic that is everywhere nonnegative has nonnegative discriminant, i.e. `b² ≤ ac`: if
`c > 0` evaluate at `t = b/c`; if `c = 0` the inequality at `t = (a + |a| + 1)/(2b)` (for
`b ≠ 0`) reads `0 ≤ -|a| - 1`, a contradiction, so `b = 0`. -/
theorem slice_sq_integral_mul_le {s : Set ℝ} {F G κ : ℝ → ℝ} (hκ : ∀ θ ∈ s, 0 ≤ κ θ)
    (hF : MeasureTheory.IntegrableOn (fun θ => F θ * F θ * κ θ) s)
    (hG : MeasureTheory.IntegrableOn (fun θ => G θ * G θ * κ θ) s)
    (hFG : MeasureTheory.IntegrableOn (fun θ => F θ * G θ * κ θ) s) :
    (∫ θ in s, F θ * G θ * κ θ) ^ 2
      ≤ (∫ θ in s, F θ * F θ * κ θ) * (∫ θ in s, G θ * G θ * κ θ) := by
  have hkey : ∀ t : ℝ,
      0 ≤ (∫ θ in s, F θ * F θ * κ θ) - 2 * t * (∫ θ in s, F θ * G θ * κ θ)
        + t ^ 2 * (∫ θ in s, G θ * G θ * κ θ) := by
    intro t
    -- integrability of the three pieces of the quadratic form
    have hA : MeasureTheory.Integrable (fun θ => F θ * F θ * κ θ)
        (MeasureTheory.volume.restrict s) := hF
    have hB : MeasureTheory.Integrable (fun θ => F θ * G θ * κ θ)
        (MeasureTheory.volume.restrict s) := hFG
    have hC : MeasureTheory.Integrable (fun θ => G θ * G θ * κ θ)
        (MeasureTheory.volume.restrict s) := hG
    have hB' : MeasureTheory.Integrable (fun θ => (2 * t) * (F θ * G θ * κ θ))
        (MeasureTheory.volume.restrict s) := hB.const_mul (2 * t)
    have hC' : MeasureTheory.Integrable (fun θ => t ^ 2 * (G θ * G θ * κ θ))
        (MeasureTheory.volume.restrict s) := hC.const_mul (t ^ 2)
    have hAB : MeasureTheory.Integrable
        (fun θ => F θ * F θ * κ θ - (2 * t) * (F θ * G θ * κ θ))
        (MeasureTheory.volume.restrict s) := hA.sub hB'
    -- the pointwise expansion of `(F - t·G)²·κ`
    have hpt : ∀ θ : ℝ, (F θ - t * G θ) * (F θ - t * G θ) * κ θ
        = F θ * F θ * κ θ - (2 * t) * (F θ * G θ * κ θ) + t ^ 2 * (G θ * G θ * κ θ) := by
      intro θ; ring
    have hint : MeasureTheory.IntegrableOn
        (fun θ => (F θ - t * G θ) * (F θ - t * G θ) * κ θ) s := by
      rw [show (fun θ => (F θ - t * G θ) * (F θ - t * G θ) * κ θ)
          = fun θ => F θ * F θ * κ θ - (2 * t) * (F θ * G θ * κ θ)
            + t ^ 2 * (G θ * G θ * κ θ) from funext fun θ => hpt θ]
      exact hAB.add hC'
    -- nonnegativity of the integral
    have hnn : 0 ≤ ∫ θ in s, (F θ - t * G θ) * (F θ - t * G θ) * κ θ :=
      setIntegral_nonneg_of_forall_mem hint.aemeasurable
        (fun θ hθ => mul_nonneg (mul_self_nonneg (F θ - t * G θ)) (hκ θ hθ))
    -- linearity of the integral
    have e0 : ∫ θ in s, (F θ - t * G θ) * (F θ - t * G θ) * κ θ
        = ∫ θ in s, (F θ * F θ * κ θ - (2 * t) * (F θ * G θ * κ θ)
            + t ^ 2 * (G θ * G θ * κ θ)) :=
      MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall hpt)
    have e1 : ∫ θ in s, (F θ * F θ * κ θ - (2 * t) * (F θ * G θ * κ θ)
            + t ^ 2 * (G θ * G θ * κ θ))
        = (∫ θ in s, (F θ * F θ * κ θ - (2 * t) * (F θ * G θ * κ θ)))
          + ∫ θ in s, t ^ 2 * (G θ * G θ * κ θ) :=
      MeasureTheory.integral_add hAB hC'
    have e2 : ∫ θ in s, (F θ * F θ * κ θ - (2 * t) * (F θ * G θ * κ θ))
        = (∫ θ in s, F θ * F θ * κ θ) - (2 * t) * (∫ θ in s, F θ * G θ * κ θ) := by
      rw [MeasureTheory.integral_sub hA hB', MeasureTheory.integral_const_mul]
    have e3 : ∫ θ in s, t ^ 2 * (G θ * G θ * κ θ)
        = t ^ 2 * (∫ θ in s, G θ * G θ * κ θ) :=
      MeasureTheory.integral_const_mul (t ^ 2) (fun θ => G θ * G θ * κ θ)
    have hlin : ∫ θ in s, (F θ - t * G θ) * (F θ - t * G θ) * κ θ
        = (∫ θ in s, F θ * F θ * κ θ) - 2 * t * (∫ θ in s, F θ * G θ * κ θ)
          + t ^ 2 * (∫ θ in s, G θ * G θ * κ θ) := by
      rw [e0, e1, e2, e3]
    rwa [hlin] at hnn
  exact quad_nonneg_discr hkey

end Work.FTS.EllipticEst.AngSecond
end
-- ===== merged: Submission.Work.FTS.EllipticEst.Auxiliary.Slice9PoincareMain =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.P9

set_option autoImplicit false

/-- **The reduction of the constrained slice Poincaré inequality to the gap inequality.**

Let `f` be `C²` on `[0,π/2]`, vanishing at `0` and `π/2`, with `∫_{Iθ} f · sinθcos²θ = 0`.
Write `f = a·sin 2θ + g` with `a = coeffA f` and `g = residG f` orthogonal to `sin 2θ`; then

* `∫ f² = (π/4) a² + ∫ g²` and `∫ (f')² = π a² + ∫ (g')²`;
* the constraint gives `∫ g · sinθcos²θ = -(4/15) a`, and Cauchy–Schwarz against
  `∫ sin²θcos⁴θ = π/32` gives `a² ≤ (225π/512) ∫ g²`;
* the gap inequality `16 ∫ g² ≤ ∫ (g')²` (hypothesis `hgap`) closes, because
  `(5π/4)·(225π/512) < 7 < 16 - 9`.

Consequently `9 ∫ f² ≤ ∫ (f')²`. -/
theorem slicePoincare9_of_gap
    (hgap : ∀ h : ℝ → ℝ, ContDiffOn ℝ 2 h (Set.Icc 0 (π / 2)) → h 0 = 0 → h (π / 2) = 0 →
      (∫ θ in Work.Spaces.Iθ, h θ * Real.sin (2 * θ)) = 0 →
      16 * (∫ θ in Work.Spaces.Iθ, (h θ) ^ 2) ≤ ∫ θ in Work.Spaces.Iθ, (deriv h θ) ^ 2)
    (f : ℝ → ℝ) (hf : ContDiffOn ℝ 2 f (Set.Icc 0 (π / 2))) (h0 : f 0 = 0) (h1 : f (π / 2) = 0)
    (horth : (∫ θ in Work.Spaces.Iθ, f θ * Work.Elliptic.sinCos2 θ) = 0) :
    9 * (∫ θ in Work.Spaces.Iθ, (f θ) ^ 2) ≤ ∫ θ in Work.Spaces.Iθ, (deriv f θ) ^ 2 := by
  haveI : IsFiniteMeasure (volume.restrict Work.Spaces.Iθ) :=
    Real.isFiniteMeasure_restrict_Icc 0 (π / 2)
  set a : ℝ := coeffA f with hadef
  set g : ℝ → ℝ := residG f with hgdef
  have hgfun : g = fun θ : ℝ => f θ - a * s2 θ := by rw [hgdef, hadef]; rfl
  -- ## basic facts about `g`
  have hfCO : ContinuousOn f (Set.Icc 0 (π / 2)) := hf.continuousOn
  have hgCO : ContinuousOn g (Set.Icc 0 (π / 2)) := by
    rw [hgfun]
    exact hfCO.sub (continuous_s2.continuousOn.const_mul a)
  have hgC2 : ContDiffOn ℝ 2 g (Set.Icc 0 (π / 2)) := by
    have hlin : ContDiffOn ℝ 2 (fun θ : ℝ => a * s2 θ) (Set.Icc 0 (π / 2)) :=
      (contDiff_const.mul contDiff_s2).contDiffOn
    rw [hgfun]
    exact hf.sub hlin
  have hg0 : g 0 = 0 := by rw [hgfun]; simp [h0, s2]
  have hg1 : g (π / 2) = 0 := by
    rw [hgfun]
    show f (π / 2) - a * s2 (π / 2) = 0
    rw [h1]
    simp only [s2]
    rw [show 2 * (π / 2) = π by ring, Real.sin_pi]
    ring
  -- ## `∫ g · sin 2θ = 0`
  have hcoeff : (∫ θ in Work.Spaces.Iθ, f θ * s2 θ) = (π / 4) * a := by
    rw [hadef, coeffA]
    have hcancel : (π / 4 : ℝ) * (4 / π) = 1 := by field_simp
    rw [← mul_assoc, hcancel, one_mul]
  have hgs2 : (∫ θ in Work.Spaces.Iθ, g θ * s2 θ) = 0 := by
    have hcongr : (∫ θ in Work.Spaces.Iθ, g θ * s2 θ)
        = ∫ θ in Work.Spaces.Iθ, (f θ * s2 θ - a * (s2 θ) ^ 2) :=
      setIntegral_Iθ_congr (fun θ _ => by rw [hgfun]; ring)
    rw [hcongr]
    have hi1 : IntegrableOn (fun θ : ℝ => f θ * s2 θ) Work.Spaces.Iθ :=
      integrableOn_Iθ_of_continuousOn (hfCO.mul continuous_s2.continuousOn)
    have hi2 : IntegrableOn (fun θ : ℝ => a * (s2 θ) ^ 2) Work.Spaces.Iθ :=
      integrableOn_Iθ_of_continuousOn (continuousOn_const.mul (continuous_s2.continuousOn.pow 2))
    rw [MeasureTheory.integral_sub (f := fun θ : ℝ => f θ * s2 θ)
        (g := fun θ : ℝ => a * (s2 θ) ^ 2) hi1 hi2,
      MeasureTheory.integral_const_mul, hcoeff, integral_s2_sq]
    ring
  -- ## the decomposition of `∫ f²`
  have hF2 : (∫ θ in Work.Spaces.Iθ, (f θ) ^ 2)
      = (π / 4) * a ^ 2 + ∫ θ in Work.Spaces.Iθ, (g θ) ^ 2 := by
    have hcongr : (∫ θ in Work.Spaces.Iθ, (f θ) ^ 2)
        = ∫ θ in Work.Spaces.Iθ, ((a * s2 θ) ^ 2 + 2 * a * (s2 θ * g θ)) + (g θ) ^ 2 :=
      setIntegral_Iθ_congr (fun θ _ => by rw [hgfun]; ring)
    rw [hcongr]
    have hA : IntegrableOn (fun θ : ℝ => (a * s2 θ) ^ 2) Work.Spaces.Iθ :=
      integrableOn_Iθ_of_continuousOn ((continuous_s2.continuousOn.const_mul a).pow 2)
    have hB : IntegrableOn (fun θ : ℝ => 2 * a * (s2 θ * g θ)) Work.Spaces.Iθ :=
      integrableOn_Iθ_of_continuousOn
        (continuousOn_const.mul (continuous_s2.continuousOn.mul hgCO))
    have hC : IntegrableOn (fun θ : ℝ => (g θ) ^ 2) Work.Spaces.Iθ :=
      integrableOn_Iθ_of_continuousOn (hgCO.pow 2)
    have hAB : IntegrableOn
        (fun θ : ℝ => (a * s2 θ) ^ 2 + 2 * a * (s2 θ * g θ)) Work.Spaces.Iθ :=
      integrableOn_Iθ_of_continuousOn
        (((continuous_s2.continuousOn.const_mul a).pow 2).add
          (continuousOn_const.mul (continuous_s2.continuousOn.mul hgCO)))
    have h1' : (∫ θ in Work.Spaces.Iθ, ((a * s2 θ) ^ 2 + 2 * a * (s2 θ * g θ)) + (g θ) ^ 2)
        = (∫ θ in Work.Spaces.Iθ, ((a * s2 θ) ^ 2 + 2 * a * (s2 θ * g θ)))
          + ∫ θ in Work.Spaces.Iθ, (g θ) ^ 2 :=
      MeasureTheory.integral_add
        (f := fun θ : ℝ => (a * s2 θ) ^ 2 + 2 * a * (s2 θ * g θ))
        (g := fun θ : ℝ => (g θ) ^ 2) hAB hC
    have h2' : (∫ θ in Work.Spaces.Iθ, ((a * s2 θ) ^ 2 + 2 * a * (s2 θ * g θ)))
        = (∫ θ in Work.Spaces.Iθ, (a * s2 θ) ^ 2)
          + ∫ θ in Work.Spaces.Iθ, 2 * a * (s2 θ * g θ) :=
      MeasureTheory.integral_add (f := fun θ : ℝ => (a * s2 θ) ^ 2)
        (g := fun θ : ℝ => 2 * a * (s2 θ * g θ)) hA hB
    have h3' : (∫ θ in Work.Spaces.Iθ, (a * s2 θ) ^ 2) = a ^ 2 * (π / 4) := by
      rw [setIntegral_Iθ_congr (fun θ _ => by ring :
        ∀ θ ∈ Work.Spaces.Iθ, (a * s2 θ) ^ 2 = a ^ 2 * (s2 θ) ^ 2)]
      rw [MeasureTheory.integral_const_mul, integral_s2_sq]
    have h4' : (∫ θ in Work.Spaces.Iθ, 2 * a * (s2 θ * g θ)) = 0 := by
      rw [MeasureTheory.integral_const_mul]
      have hz : (∫ θ in Work.Spaces.Iθ, s2 θ * g θ) = 0 := by
        rw [show (∫ θ in Work.Spaces.Iθ, s2 θ * g θ)
            = ∫ θ in Work.Spaces.Iθ, g θ * s2 θ from
          setIntegral_Iθ_congr (fun θ _ => mul_comm _ _)]
        exact hgs2
      rw [hz]; ring
    rw [h1', h2', h3', h4']
    ring
  -- ## the decomposition of `∫ (f')²`
  have hwg : ∀ θ ∈ Set.Icc 0 (π / 2), w g θ = w f θ - a * w s2 θ := by
    intro θ hθ
    rw [hgfun]
    exact w_sub_const_mul hf a θ hθ
  have hwpt : ∀ θ ∈ Work.Spaces.Iθ,
      (w f θ) ^ 2 = (a * w s2 θ) ^ 2 + 2 * a * (w s2 θ * w g θ) + (w g θ) ^ 2 := by
    intro θ hθ
    rw [hwg θ hθ]
    ring
  have hws2 : ContinuousOn (w s2) (Set.Icc 0 (π / 2)) :=
    continuousOn_w contDiff_s2.contDiffOn
  have hwg' : ContinuousOn (w g) (Set.Icc 0 (π / 2)) := continuousOn_w hgC2
  have hF1 : (∫ θ in Work.Spaces.Iθ, (deriv f θ) ^ 2)
      = π * a ^ 2 + ∫ θ in Work.Spaces.Iθ, (deriv g θ) ^ 2 := by
    rw [← integral_w_sq_eq_integral_deriv_sq f, ← integral_w_sq_eq_integral_deriv_sq g,
      setIntegral_Iθ_congr hwpt]
    have hA : IntegrableOn (fun θ : ℝ => (a * w s2 θ) ^ 2) Work.Spaces.Iθ :=
      integrableOn_Iθ_of_continuousOn ((hws2.const_mul a).pow 2)
    have hB : IntegrableOn (fun θ : ℝ => 2 * a * (w s2 θ * w g θ)) Work.Spaces.Iθ :=
      integrableOn_Iθ_of_continuousOn (continuousOn_const.mul (hws2.mul hwg'))
    have hC : IntegrableOn (fun θ : ℝ => (w g θ) ^ 2) Work.Spaces.Iθ :=
      integrableOn_Iθ_of_continuousOn (hwg'.pow 2)
    have hAB : IntegrableOn
        (fun θ : ℝ => (a * w s2 θ) ^ 2 + 2 * a * (w s2 θ * w g θ)) Work.Spaces.Iθ :=
      integrableOn_Iθ_of_continuousOn (((hws2.const_mul a).pow 2).add
        (continuousOn_const.mul (hws2.mul hwg')))
    have h1' : (∫ θ in Work.Spaces.Iθ, ((a * w s2 θ) ^ 2 + 2 * a * (w s2 θ * w g θ))
          + (w g θ) ^ 2)
        = (∫ θ in Work.Spaces.Iθ, ((a * w s2 θ) ^ 2 + 2 * a * (w s2 θ * w g θ)))
          + ∫ θ in Work.Spaces.Iθ, (w g θ) ^ 2 :=
      MeasureTheory.integral_add
        (f := fun θ : ℝ => (a * w s2 θ) ^ 2 + 2 * a * (w s2 θ * w g θ))
        (g := fun θ : ℝ => (w g θ) ^ 2) hAB hC
    have h2' : (∫ θ in Work.Spaces.Iθ, ((a * w s2 θ) ^ 2 + 2 * a * (w s2 θ * w g θ)))
        = (∫ θ in Work.Spaces.Iθ, (a * w s2 θ) ^ 2)
          + ∫ θ in Work.Spaces.Iθ, 2 * a * (w s2 θ * w g θ) :=
      MeasureTheory.integral_add (f := fun θ : ℝ => (a * w s2 θ) ^ 2)
        (g := fun θ : ℝ => 2 * a * (w s2 θ * w g θ)) hA hB
    have h3' : (∫ θ in Work.Spaces.Iθ, (a * w s2 θ) ^ 2) = a ^ 2 * π := by
      rw [setIntegral_Iθ_congr (fun θ _ => by ring :
        ∀ θ ∈ Work.Spaces.Iθ, (a * w s2 θ) ^ 2 = a ^ 2 * (w s2 θ) ^ 2)]
      rw [MeasureTheory.integral_const_mul, integral_w_sq_eq_integral_deriv_sq s2,
        integral_deriv_s2_sq]
    have h4' : (∫ θ in Work.Spaces.Iθ, 2 * a * (w s2 θ * w g θ)) = 0 := by
      rw [MeasureTheory.integral_const_mul]
      have hz : (∫ θ in Work.Spaces.Iθ, w s2 θ * w g θ) = 0 := by
        rw [integral_w_mul_eq s2 g]
        rw [show (∫ θ in Work.Spaces.Iθ, deriv s2 θ * deriv g θ)
            = ∫ θ in Work.Spaces.Iθ, deriv g θ * deriv s2 θ from
          setIntegral_Iθ_congr (fun θ _ => mul_comm _ _)]
        rw [show (∫ θ in Work.Spaces.Iθ, deriv g θ * deriv s2 θ)
            = 4 * (∫ θ in Work.Spaces.Iθ, g θ * s2 θ) from
          Work.FTS.EllipticEst.Auxiliary.pIBP_fts g hgC2 hg0 hg1]
        rw [hgs2]; ring
      rw [hz]; ring
    have h5' : (∫ θ in Work.Spaces.Iθ, (w g θ) ^ 2)
        = ∫ θ in Work.Spaces.Iθ, (deriv g θ) ^ 2 := integral_w_sq_eq_integral_deriv_sq g
    rw [h1', h2', h3', h4', h5']
    ring
  -- ## the gap inequality on the residual
  have hgapg : 16 * (∫ θ in Work.Spaces.Iθ, (g θ) ^ 2)
      ≤ ∫ θ in Work.Spaces.Iθ, (deriv g θ) ^ 2 :=
    hgap g hgC2 hg0 hg1 (by simpa [s2] using hgs2)
  -- ## the constraint bounds the coefficient by the residual
  have hmom_g : (∫ θ in Work.Spaces.Iθ, g θ * Work.Elliptic.sinCos2 θ) = -(4 / 15) * a := by
    have hcongr : (∫ θ in Work.Spaces.Iθ, g θ * Work.Elliptic.sinCos2 θ)
        = ∫ θ in Work.Spaces.Iθ, (f θ * Work.Elliptic.sinCos2 θ
            - a * (s2 θ * Work.Elliptic.sinCos2 θ)) :=
      setIntegral_Iθ_congr (fun θ _ => by rw [hgfun]; ring)
    rw [hcongr]
    have hi1 : IntegrableOn (fun θ : ℝ => f θ * Work.Elliptic.sinCos2 θ) Work.Spaces.Iθ :=
      integrableOn_Iθ_of_continuousOn (hfCO.mul continuous_sinCos2.continuousOn)
    have hi2 : IntegrableOn
        (fun θ : ℝ => a * (s2 θ * Work.Elliptic.sinCos2 θ)) Work.Spaces.Iθ :=
      integrableOn_Iθ_of_continuousOn
        (continuousOn_const.mul (continuous_s2.continuousOn.mul continuous_sinCos2.continuousOn))
    rw [MeasureTheory.integral_sub (f := fun θ : ℝ => f θ * Work.Elliptic.sinCos2 θ)
        (g := fun θ : ℝ => a * (s2 θ * Work.Elliptic.sinCos2 θ)) hi1 hi2,
      MeasureTheory.integral_const_mul, horth]
    have hs2φ : (∫ θ in Work.Spaces.Iθ, s2 θ * Work.Elliptic.sinCos2 θ) = 4 / 15 := by
      rw [show (∫ θ in Work.Spaces.Iθ, s2 θ * Work.Elliptic.sinCos2 θ)
          = ∫ θ in Work.Spaces.Iθ, Work.Elliptic.sinCos2 θ * s2 θ from
        setIntegral_Iθ_congr (fun θ _ => mul_comm _ _)]
      exact integral_sinCos2_mul_s2
    rw [hs2φ]
    ring
  have hgm : MemLp g 2 (volume.restrict Work.Spaces.Iθ) := by
    obtain ⟨C, hC⟩ := IsCompact.exists_bound_of_continuousOn isCompact_Icc hgCO
    exact MemLp.of_bound (hgCO.aestronglyMeasurable measurableSet_Icc) C
      (ae_restrict_of_forall_mem measurableSet_Icc hC)
  have hφm : MemLp Work.Elliptic.sinCos2 2 (volume.restrict Work.Spaces.Iθ) :=
    MemLp.of_bound (continuous_sinCos2.continuousOn.aestronglyMeasurable measurableSet_Icc) 1
      (ae_restrict_of_forall_mem measurableSet_Icc (fun θ _ => by
        simpa [Real.norm_eq_abs] using abs_sinCos2_le_one θ))
  have hcs := Work.Spaces.cs_integral (u := g) (v := Work.Elliptic.sinCos2)
    (s := Work.Spaces.Iθ) hgm hφm
  have ha2 : a ^ 2 ≤ (225 * π / 512) * (∫ θ in Work.Spaces.Iθ, (g θ) ^ 2) := by
    have h1' : (-(4 / 15) * a) ^ 2
        ≤ (∫ θ in Work.Spaces.Iθ, (g θ) ^ 2) * (π / 32) := by
      rw [← hmom_g]
      simpa [integral_sinCos2_sq] using hcs
    nlinarith [h1']
  -- ## arithmetic
  have hSnn : 0 ≤ ∫ θ in Work.Spaces.Iθ, (g θ) ^ 2 := integral_nonneg (fun θ => sq_nonneg _)
  have hpi : 1125 * π ^ 2 ≤ 14336 := by nlinarith [Real.pi_lt_d2, Real.pi_pos]
  rw [hF2, hF1]
  have h5π7 : (5 * π / 4) * a ^ 2 ≤ 7 * (∫ θ in Work.Spaces.Iθ, (g θ) ^ 2) := by
    have h1 : (5 * π / 4) * a ^ 2
        ≤ (5 * π / 4) * ((225 * π / 512) * (∫ θ in Work.Spaces.Iθ, (g θ) ^ 2)) :=
      mul_le_mul_of_nonneg_left ha2 (by linarith [Real.pi_pos])
    have h2 : (5 * π / 4) * ((225 * π / 512) * (∫ θ in Work.Spaces.Iθ, (g θ) ^ 2))
        ≤ 7 * (∫ θ in Work.Spaces.Iθ, (g θ) ^ 2) := by
      have h3 : (5 * π / 4) * ((225 * π / 512) * (∫ θ in Work.Spaces.Iθ, (g θ) ^ 2))
          = (1125 * π ^ 2 / 2048) * (∫ θ in Work.Spaces.Iθ, (g θ) ^ 2) := by ring
      rw [h3]
      have h4 : (1125 * π ^ 2 / 2048 : ℝ) ≤ 7 := by
        rw [div_le_iff₀ (by norm_num : (0 : ℝ) < 2048)]
        linarith [hpi]
      exact mul_le_mul_of_nonneg_right h4 hSnn
    linarith [h1, h2]
  nlinarith [h5π7, hgapg, hSnn]

end Work.FTS.EllipticEst.P9
end
end
-- ===== merged: Submission.Work.FTS.EllipticEst.Auxiliary.divCosSq_integrable_fts =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.Auxiliary

set_option autoImplicit false
set_option linter.unusedSimpArgs false


end Work.FTS.EllipticEst.Auxiliary
end
-- ===== merged: Submission.Work.FTS.EllipticEst.Blocks.SliceSwapLintegral =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.Blocks

open MeasureTheory Set

/-- If `Function.uncurry G` is `C^{n+1}` on an *open* set `U`, then the uncurried `z`-partial
`(z,θ) ↦ ∂_z G (z,θ)` is `C^n` on `U`.  The point is that on the open set `U` the `z`-partial
coincides with the Fréchet derivative of `Function.uncurry G` evaluated in the constant
direction `(1,0)`, and that composition is smooth. -/
theorem contDiffOn_uncurry_pz_of_succ {G : ℝ → ℝ → ℝ} {U : Set (ℝ × ℝ)} (hU : IsOpen U)
    {n : ℕ} (h : ContDiffOn ℝ (n + 1) (Function.uncurry G) U) :
    ContDiffOn ℝ n (Function.uncurry (Work.Spaces.pz G)) U := by
  have hchain : ∀ p ∈ U,
      Work.Spaces.pz G p.1 p.2 = fderiv ℝ (Function.uncurry G) p (1, 0) := by
    intro p hp
    exact Work.Spaces.pz_eq_fderiv
      ((h.differentiableOn (by simp)).differentiableAt (hU.mem_nhds hp))
  have hfd : ContDiffOn ℝ n (fun p : ℝ × ℝ => fderiv ℝ (Function.uncurry G) p) U := by
    have h' := h.fderivWithin hU.uniqueDiffOn (m := n) le_rfl
    refine h'.congr ?_
    intro p hp
    rw [fderivWithin_of_isOpen hU hp]
  have hcomp : ContDiffOn ℝ n
      (fun p : ℝ × ℝ => (fderiv ℝ (Function.uncurry G) p) (1, 0)) U := by
    simpa using hfd.clm_apply (contDiffOn_const (c := ((1 : ℝ), (0 : ℝ))))
  exact hcomp.congr hchain

/-- **Tonelli plus translation of the radial variable** for the weighted square of the second
radial partial.  For `V` which is `C²` on the open quadrant `(0,∞) × (0,π/2)` and `wth`
measurable, `z₀ > 0`, `δ > 0`, the iterated `lintegral` of
`(θ,t) ↦ ofReal ((∂_z²V (z₀+t,θ) · wth θ)²)` over `(0,π/2) × (0,δ]` equals the iterated
`lintegral` over the rectangle `(z₀, z₀+δ) × (0,π/2)` in the other order.

Suggested sorry-free route: use the *clean* `DzAmgm.lintegralSwapTranslate_of_aem` (Tonelli,
translation invariance of Lebesgue measure, `Ioc = Ioo` a.e.) together with
`DzAmgm.aem_uncurry_translate`, which needs only joint continuity of
`(z,θ) ↦ ∂_z²V z θ` on the quadrant — prove that yourself, e.g. by the route described in
`FTS/EllipticEst/Blocks/PzIterTwoContinuousOn` (do NOT route through the still-`sorry`
`DzAmgm.LintegralSwapTranslate` / `DzAmgm.ContinuousOnUncurryPzIterTwo` /
`DzAmgm.SliceIteratedDerivFDeriv`). -/
theorem SliceSwapLintegral (V : ℝ → ℝ → ℝ) (wth : ℝ → ℝ) (hwthmeas : Measurable wth)
    (hV : ContDiffOn ℝ 2 (Function.uncurry V) (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)))
    {z₀ δ : ℝ} (hz₀ : 0 < z₀) (hδ : 0 < δ) :
    (∫⁻ θ in Set.Ioo 0 (Real.pi / 2),
        ∫⁻ t in Set.Ioc 0 δ,
          ENNReal.ofReal ((Work.Spaces.pzIter 2 V (z₀ + t) θ * wth θ) ^ 2))
      = ∫⁻ z in Set.Ioo z₀ (z₀ + δ),
          ∫⁻ θ in Set.Ioo 0 (Real.pi / 2),
            ENNReal.ofReal ((Work.Spaces.pzIter 2 V z θ * wth θ) ^ 2) := by
  -- The open quadrant.
  have hU : IsOpen (Set.Ioi (0 : ℝ) ×ˢ Set.Ioo 0 (Real.pi / 2)) :=
    isOpen_Ioi.prod isOpen_Ioo
  -- `∂_z V` is `C¹` on the quadrant.
  have h1 : ContDiffOn ℝ (1 : ℕ) (Function.uncurry (Work.Spaces.pz V))
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) :=
    contDiffOn_uncurry_pz_of_succ hU (n := 1) (by norm_num; exact hV)
  -- `∂_z²V` is continuous (i.e. `C⁰`) on the quadrant.
  have h2 : ContDiffOn ℝ (0 : ℕ) (Function.uncurry (Work.Spaces.pz (Work.Spaces.pz V)))
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) :=
    contDiffOn_uncurry_pz_of_succ hU (n := 0) (by norm_num; exact h1)
  have hcont : ContinuousOn (Function.uncurry (Work.Spaces.pzIter 2 V))
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) := by
    have := contDiffOn_zero.mp h2
    simpa [Work.Spaces.pzIter_succ] using this
  -- Tonelli, translation invariance of Lebesgue measure, `Ioc = Ioo` a.e.
  exact Work.FTS.EllipticEst.DzAmgm.lintegralSwapTranslate_of_aem V wth
    (Work.FTS.EllipticEst.DzAmgm.aem_uncurry_translate V wth hwthmeas hcont hz₀ hδ)

end Work.FTS.EllipticEst.Blocks
end
-- ===== merged: Submission.Work.FTS.EllipticEst.Cert.Gsing_smooth_ode_of_facts =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.Cert

open scoped Real Topology ContDiff
open MeasureTheory Set Filter

/-! ## Two analytic ingredients

The self-similar singular term `Gsing α F = Gstar α F + Gbar α F` is built from the two radial
functions

* `L12 F z = 3 ∫_z^∞ F_*(r)/r dr` (the tail integral), and
* `Jfun α F z = ∫_0^z s^{(5-α)/α} F_*(s) ds` (the primitive appearing in `Gbar`),

and the hypotheses of the theorem prescribe the derivatives of both on `(0,∞)`: `hL12` gives
`(L12 F)' = -3F_*(z)/z` and `hasDerivAt_integral_rpow_mul_Fstar` below gives
`(Jfun α F)' = z^{(5-α)/α}F_*(z)`.  Both prescribed derivatives are smooth on `(0,∞)` as soon
as `F_*` is (`hFsm`), so smoothness of `L12 F` and of `Jfun α F` — hence of `Gsing α F` —
follows from the elementary "smooth primitive" lemma below.  The second order ODE is then
`Work.Elliptic.Gsing_ode`. -/

/-- A function which is differentiable on `(0,∞)` with derivative prescribed by a `C^∞`
function `g` on `(0,∞)` is itself `C^∞` on `(0,∞)`.

This is `contDiffOn_infty_iff_deriv_of_isOpen` applied on the open set `(0,∞)`: the derivative
`deriv f` agrees there with `g` (by `HasDerivAt.deriv`), and `ContDiffOn` is a local property. -/
private theorem contDiffOn_infty_of_hasDerivAt_prv {f g : ℝ → ℝ}
    (hderiv : ∀ z ∈ Set.Ioi (0 : ℝ), HasDerivAt f (g z) z)
    (hg : ∀ m : ℕ, ContDiffOn ℝ m g (Set.Ioi 0)) :
    ∀ m : ℕ, ContDiffOn ℝ m f (Set.Ioi 0) := by
  have hgTop : ContDiffOn ℝ ∞ g (Set.Ioi 0) := contDiffOn_infty.mpr hg
  have hfTop : ContDiffOn ℝ ∞ f (Set.Ioi 0) := by
    rw [contDiffOn_infty_iff_deriv_of_isOpen isOpen_Ioi]
    refine ⟨fun z hz => (hderiv z hz).differentiableAt.differentiableWithinAt, ?_⟩
    exact hgTop.congr (fun z hz => (hderiv z hz).deriv)
  exact contDiffOn_infty.mp hfTop

/-- **FTC for the inner integral of `Gbar`.**  If `F_*` is continuous on `(0,∞)` and
`r ↦ F_*(r)/r` is integrable on `(0,∞)`, then `z ↦ ∫_0^z s^{(5-α)/α} F_*(s) ds` has derivative
`z^{(5-α)/α} F_*(z)` at every `z > 0`.

The point is the interval integrability of the integrand on `(0,z]`: for `0 < s ≤ z` the
identity `s^{(5-α)/α+1} = s^{(5-α)/α}·s` (and `(5-α)/α + 1 = 5/α > 0` independently of `α`)
writes the integrand as the integrable function `F_*(s)/s` times the factor `s^{5/α}`, which is
continuous on the compact `[0,z]`. -/
private theorem hasDerivAt_integral_rpow_mul_Fstar (α : ℝ) (F : ℝ → ℝ → ℝ) (hα : 0 < α)
    (hFsm : ∀ m : ℕ, ContDiffOn ℝ m (Work.Elliptic.Fstar F) (Set.Ioi 0))
    (hFint : MeasureTheory.IntegrableOn (fun r : ℝ => Work.Elliptic.Fstar F r / r) (Set.Ioi 0)) :
    ∀ z ∈ Set.Ioi (0 : ℝ),
      HasDerivAt (fun z' : ℝ => ∫ s in (0 : ℝ)..z', s ^ ((5 - α) / α) * Work.Elliptic.Fstar F s)
        (z ^ ((5 - α) / α) * Work.Elliptic.Fstar F z) z := by
  intro z hz
  have hzpos : (0 : ℝ) < z := hz
  -- `F_*` is continuous on `(0,∞)`, hence so is the integrand
  have hFcont : ContinuousOn (Work.Elliptic.Fstar F) (Set.Ioi (0 : ℝ)) := (hFsm 0).continuousOn
  have hfcontOn : ContinuousOn
      (fun s : ℝ => s ^ ((5 - α) / α) * Work.Elliptic.Fstar F s) (Set.Ioi (0 : ℝ)) := by
    intro x hx
    exact ((Real.continuousAt_rpow_const x ((5 - α) / α)
      (Or.inl (ne_of_gt hx))).continuousWithinAt).mul (hFcont x hx)
  have hcont : ContinuousAt (fun s : ℝ => s ^ ((5 - α) / α) * Work.Elliptic.Fstar F s) z :=
    (Real.continuousAt_rpow_const z ((5 - α) / α) (Or.inl (ne_of_gt hzpos))).mul
      (hFcont.continuousAt (isOpen_Ioi.mem_nhds hz))
  have hmeas : StronglyMeasurableAtFilter
      (fun s : ℝ => s ^ ((5 - α) / α) * Work.Elliptic.Fstar F s) (𝓝 z) MeasureTheory.volume :=
    hfcontOn.stronglyMeasurableAtFilter isOpen_Ioi z hz
  -- integrability of the integrand on the interval `(0,z]`
  have hint : IntegrableOn (fun s : ℝ => s ^ ((5 - α) / α) * Work.Elliptic.Fstar F s)
      (Set.Ioc (0 : ℝ) z) := by
    have hgIoc : IntegrableOn (fun x : ℝ => Work.Elliptic.Fstar F x / x) (Set.Ioc (0 : ℝ) z) :=
      hFint.mono_set (fun x hx => hx.1)
    have hIcc : IntegrableOn (fun x : ℝ => Work.Elliptic.Fstar F x / x) (Set.Icc (0 : ℝ) z) :=
      (integrableOn_Icc_iff_integrableOn_Ioc).mpr hgIoc
    -- the factor `x^((5-α)/α+1) = x^(5/α)` is continuous on the compact `[0,z]`
    have hp5 : (0 : ℝ) ≤ (5 - α) / α + 1 := by
      have h : (5 - α) / α + 1 = 5 / α := by field_simp; ring
      rw [h]; positivity
    have hcont' : ContinuousOn (fun x : ℝ => x ^ ((5 - α) / α + 1)) (Set.Icc (0 : ℝ) z) :=
      (Real.continuous_rpow_const hp5).continuousOn
    have hmul : IntegrableOn
        (fun x : ℝ => (Work.Elliptic.Fstar F x / x) * x ^ ((5 - α) / α + 1))
        (Set.Icc (0 : ℝ) z) := hIcc.mul_continuousOn hcont' isCompact_Icc
    have hmul' : IntegrableOn
        (fun x : ℝ => (Work.Elliptic.Fstar F x / x) * x ^ ((5 - α) / α + 1))
        (Set.Ioc (0 : ℝ) z) := hmul.mono_set Set.Ioc_subset_Icc_self
    refine hmul'.congr_fun ?_ measurableSet_Ioc
    intro x hx
    have hxpos : 0 < x := hx.1
    have hrw : x ^ ((5 - α) / α + 1) = x ^ ((5 - α) / α) * x := by
      rw [Real.rpow_add hxpos, Real.rpow_one]
    show Work.Elliptic.Fstar F x / x * x ^ ((5 - α) / α + 1)
      = x ^ ((5 - α) / α) * Work.Elliptic.Fstar F x
    rw [hrw]
    field_simp
  have hInt : IntervalIntegrable
      (fun s : ℝ => s ^ ((5 - α) / α) * Work.Elliptic.Fstar F s) MeasureTheory.volume 0 z :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hzpos.le).mpr hint
  exact intervalIntegral.integral_hasDerivAt_right hInt hmeas hcont

theorem Gsing_smooth_ode_of_facts (α : ℝ) (F : ℝ → ℝ → ℝ) (hα : 0 < α)
    (hFsm : ∀ m : ℕ, ContDiffOn ℝ m (Work.Elliptic.Fstar F) (Set.Ioi 0))
    (hFint : MeasureTheory.IntegrableOn (fun r : ℝ => Work.Elliptic.Fstar F r / r) (Set.Ioi 0))
    (hL12 : ∀ z ∈ Set.Ioi (0 : ℝ),
      HasDerivAt (Work.Elliptic.L12 F) (-(3 * Work.Elliptic.Fstar F z / z)) z) :
    (∀ m : ℕ, ContDiffOn ℝ m (Work.Elliptic.Gsing α F) (Set.Ioi 0)) ∧
      ∀ z ∈ Set.Ioi (0 : ℝ),
        α ^ 2 * z ^ 2 * deriv (fun z' => deriv (Work.Elliptic.Gsing α F) z') z
          + α * (5 + α) * z * deriv (Work.Elliptic.Gsing α F) z
        = (15 / 4) * Work.Elliptic.Fstar F z := by
  -- the derivative of `F_*` itself
  have hFc : ∀ z ∈ Set.Ioi (0 : ℝ),
      HasDerivAt (Work.Elliptic.Fstar F) (deriv (Work.Elliptic.Fstar F) z) z := by
    intro z hz
    exact (((hFsm 1).differentiableOn (by decide)).differentiableAt
      (isOpen_Ioi.mem_nhds hz)).hasDerivAt
  -- the two prescribed derivatives are smooth on `(0,∞)`
  have hdivsm : ∀ m : ℕ, ContDiffOn ℝ m (fun z : ℝ => -(3 * Work.Elliptic.Fstar F z / z))
      (Set.Ioi 0) := by
    intro m
    have h2 : ContDiffOn ℝ m (fun z : ℝ => 3 * Work.Elliptic.Fstar F z / z) (Set.Ioi 0) :=
      (contDiffOn_const.mul (hFsm m)).div contDiffOn_id (fun z hz => ne_of_gt hz)
    exact h2.neg
  have hrpwsm : ∀ m : ℕ,
      ContDiffOn ℝ m (fun z : ℝ => z ^ ((5 - α) / α) * Work.Elliptic.Fstar F z) (Set.Ioi 0) := by
    intro m
    exact (contDiffOn_id.rpow_const_of_ne (fun z hz => ne_of_gt hz)).mul (hFsm m)
  -- hence `L12 F` and `Jfun α F` are smooth, and so are `Gstar`, `Gbar` and `Gsing`
  have hL12sm : ∀ m : ℕ, ContDiffOn ℝ m (Work.Elliptic.L12 F) (Set.Ioi 0) :=
    contDiffOn_infty_of_hasDerivAt_prv hL12 hdivsm
  have hJ := hasDerivAt_integral_rpow_mul_Fstar α F hα hFsm hFint
  have hJsm : ∀ m : ℕ, ContDiffOn ℝ m (Work.Elliptic.Jfun α F) (Set.Ioi 0) :=
    contDiffOn_infty_of_hasDerivAt_prv hJ hrpwsm
  have hGstar : ∀ m : ℕ, ContDiffOn ℝ m (Work.Elliptic.Gstar α F) (Set.Ioi 0) := by
    intro m
    exact (contDiffOn_const (c := -(1 / (4 * α)))).mul (hL12sm m)
  have hGbar : ∀ m : ℕ, ContDiffOn ℝ m (Work.Elliptic.Gbar α F) (Set.Ioi 0) := by
    intro m
    have h1 : ContDiffOn ℝ m (fun z : ℝ => z ^ (-(5 / α))) (Set.Ioi 0) :=
      contDiffOn_id.rpow_const_of_ne (fun z hz => ne_of_gt hz)
    exact (contDiffOn_const.mul h1).mul (hJsm m)
  constructor
  · intro m
    exact (hGstar m).add (hGbar m)
  · intro z hz
    exact Work.Elliptic.Gsing_ode α F hα hL12 hFc hJ z hz

end Work.FTS.EllipticEst.Cert
end
-- ===== merged: Submission.Work.FTS.EllipticEst.Cert.Jfun_hasDerivAt_of_Fstar =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.Cert

open MeasureTheory Set Filter
open scoped Topology

theorem Jfun_hasDerivAt_of_Fstar (α : ℝ) (F : ℝ → ℝ → ℝ)
    (hFsm : ∀ m : ℕ, ContDiffOn ℝ m (Work.Elliptic.Fstar F) (Set.Ioi 0))
    (hFint : MeasureTheory.IntegrableOn (fun r : ℝ => Work.Elliptic.Fstar F r / r) (Set.Ioi 0))
    (hα : 0 < α) (hα1 : α ≤ 1) :
    ∀ z ∈ Set.Ioi (0 : ℝ),
      HasDerivAt (fun z' => ∫ s in (0 : ℝ)..z', s ^ ((5 - α) / α) * Work.Elliptic.Fstar F s)
        (z ^ ((5 - α) / α) * Work.Elliptic.Fstar F z) z := by
  intro z hz
  have hzpos : (0 : ℝ) < z := hz
  -- the exponent `(5-α)/α` is nonnegative (indeed positive)
  have hcpos : (0 : ℝ) < (5 - α) / α := div_pos (by linarith) hα
  have hcnonneg : (0 : ℝ) ≤ (5 - α) / α := le_of_lt hcpos
  -- `F_*` is continuous on `(0,∞)`, hence so is the integrand
  have hFcont : ContinuousOn (Work.Elliptic.Fstar F) (Set.Ioi (0 : ℝ)) := (hFsm 0).continuousOn
  have hfcontOn : ContinuousOn
      (fun s : ℝ => s ^ ((5 - α) / α) * Work.Elliptic.Fstar F s) (Set.Ioi (0 : ℝ)) := by
    intro x hx
    exact ((Real.continuous_rpow_const hcnonneg).continuousAt).continuousWithinAt.mul
      (hFcont x hx)
  have hcont : ContinuousAt (fun s : ℝ => s ^ ((5 - α) / α) * Work.Elliptic.Fstar F s) z :=
    (Real.continuousAt_rpow_const z ((5 - α) / α) (Or.inl (ne_of_gt hzpos))).mul
      (hFcont.continuousAt (isOpen_Ioi.mem_nhds hz))
  have hmeas : StronglyMeasurableAtFilter
      (fun s : ℝ => s ^ ((5 - α) / α) * Work.Elliptic.Fstar F s) (𝓝 z) MeasureTheory.volume :=
    hfcontOn.stronglyMeasurableAtFilter isOpen_Ioi z hz
  -- integrability of the integrand on the interval `(0,z]`
  have hint : IntegrableOn (fun s : ℝ => s ^ ((5 - α) / α) * Work.Elliptic.Fstar F s)
      (Set.Ioc (0 : ℝ) z) := by
    -- `F_*(x)/x` is integrable on `(0,z]`, hence (a null set apart) on `[0,z]`
    have hgIoc : IntegrableOn (fun x : ℝ => Work.Elliptic.Fstar F x / x) (Set.Ioc (0 : ℝ) z) :=
      hFint.mono_set (fun x hx => hx.1)
    have hIcc : IntegrableOn (fun x : ℝ => Work.Elliptic.Fstar F x / x) (Set.Icc (0 : ℝ) z) :=
      (integrableOn_Icc_iff_integrableOn_Ioc).mpr hgIoc
    -- multiply by the continuous bounded factor `x^((5-α)/α+1) = x^{5/α}`
    have hcont' : ContinuousOn (fun x : ℝ => x ^ ((5 - α) / α + 1)) (Set.Icc (0 : ℝ) z) :=
      (Real.continuous_rpow_const (by linarith)).continuousOn
    have hmul : IntegrableOn
        (fun x : ℝ => (Work.Elliptic.Fstar F x / x) * x ^ ((5 - α) / α + 1))
        (Set.Icc (0 : ℝ) z) := hIcc.mul_continuousOn hcont' isCompact_Icc
    have hmul' : IntegrableOn
        (fun x : ℝ => (Work.Elliptic.Fstar F x / x) * x ^ ((5 - α) / α + 1))
        (Set.Ioc (0 : ℝ) z) := hmul.mono_set Set.Ioc_subset_Icc_self
    refine hmul'.congr_fun ?_ measurableSet_Ioc
    intro x hx
    have hxpos : 0 < x := hx.1
    have hrw : x ^ ((5 - α) / α + 1) = x ^ ((5 - α) / α) * x := by
      rw [Real.rpow_add hxpos, Real.rpow_one]
    show Work.Elliptic.Fstar F x / x * x ^ ((5 - α) / α + 1)
      = x ^ ((5 - α) / α) * Work.Elliptic.Fstar F x
    rw [hrw]
    field_simp
  have hInt : IntervalIntegrable
      (fun s : ℝ => s ^ ((5 - α) / α) * Work.Elliptic.Fstar F s) MeasureTheory.volume 0 z :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hzpos.le).mpr hint
  exact intervalIntegral.integral_hasDerivAt_right hInt hmeas hcont

end Work.FTS.EllipticEst.Cert
end
-- ===== merged: Submission.Work.FTS.EllipticEst.Cores.AeStep2Aux.I1Wk.sliceThetaIbpSep =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.Cores.AeStep2Aux.I1Wk

set_option autoImplicit false

/-- **The θ-slice identity `S2` with a θ-cutoff `ψ`** (`η = Work.Spaces.eta = 99/100`,
`v ∈ C²((0,π/2))`, `ψ ∈ C²(ℝ)` with `tsupport ψ ⊆ (a,b) ⊂ (0,π/2)`):

`∫_θ sin(2θ)^{-η} ψ v v'' = -2η∫σψv² - κ∫σψ(v')² - (2η/(1+η))∫σψ(v' - (1+η)v cos2θ/sin2θ)² + (1/2)∫σψ''v²`

(`σ = sin(2θ)^{-η}`, `κ = (1-η)/(1+η)`), all integrals over `(0,π/2)`.

This is the exact angular IBP underlying `I1Wk.truncThetaIbp` (there in the integrated, 2-D form
against `χ z · w z ^ 2`).  Note that **the statement is only true with the `tsupport` hypothesis**:
with mere `Function.support ψ ⊆ Ioo 0 (π/2)` (or without any separation of `ψ` from the corners)
the angular boundary bracket `B θ = σθ ψθ vθ v'θ - η σθ cos2θ/sin2θ ψθ vθ² - (1/2)σθ ψ'θ vθ²`
need not vanish and the identity fails (see `I1Wk/NOTES_truncThetaIbp_FALSE.md`).

Route.  (i) `S2` is a *slice-level* consequence of the pointwise identity already proved in
`Submission.Work.FTS.EllipticEst.Cores.AeStep2Aux.slice_second_identity` (or its sibling
`sst_hasDerivAt_Phi` in `slice_second_trunc.lean`): with
`Φ v = σ v v' - cos(2θ)·σ₁ v²`, `Ψ v = 2σ v² + (1-η²)cos²(2θ) σ₂ v² + σ₂ (v' sin2θ - (1+η) cos2θ v)²`
and `σ_k = sin(2θ)^{-k}` one has `σ θ (v θ v'' θ) = (Φ v)' θ - Ψ v θ`, so that
`σ v v'' = (Φ v)' - Ψ v` pointwise on `(0,π/2)`.
(ii) Multiply by `ψ` and integrate over `[a,b]` by the FTC (`ψ` is `C²`, `v` is `C²` on a
neighbourhood of `[a,b]`); `[ψ Φ v]_a^b = 0` because `ψ` vanishes *on a neighbourhood* of `a` and
`b` (that is what `tsupport ψ ⊆ (a,b)` gives: `tsupport` is closed).
(iii) Integrate `-∫_a^b ψ' Φ v` by parts twice: `∫ψ' σ v v' = (1/2)∫(ψ'σ)'v²` and
`∫ψ' c σ₁ v² = -∫(cσ₁)' ψ v² - 2∫cσ₁ ψ v v'`, all boundary terms vanishing because `ψ` and `ψ'`
are `0` near `a` and `b`.  Use `σ' = -2η (cos2θ) σ₁`, `(cσ₁)' = -2(1+η)cos²(2θ)σ₂ - 2σ`,
`σ₂ = σ/sin²(2θ)`.
(iv) Expand `Ψ` and finish with `field_simp; ring` (the `sin(2θ)^{-k}` relations are best
rewritten with `← Real.rpow_add`/`Real.rpow_sub` first, cf. `ssi_sig1_eq_div`, `ssi_sig2_eq_div`
in `slice_second_identity.lean`).
No integrability hypothesis is needed: every integrand is supported in `[a,b]`, where `σ`, `σ₂`,
`v`, `v'`, `v''`, `ψ`, `ψ'`, `ψ''` are all continuous.

The implementation follows the plan above with *one* total derivative instead of three partial
integrations by parts: the boundary primitive
`Gfun v ψ θ = ψ θ · (σ θ v θ v' θ - η (cos2θ σ₁ θ) v θ²) - (1/2) ψ' θ σ θ v θ²`
has `(Gfun v ψ)' = Lfun v ψ - RHSfun v ψ` on `(0,π/2)` (that is `hasDerivAt_Gfun`, whose proof
is a product-rule computation reducing to the algebraic identity `theta_alg` of
`SliceThetaIbpDefs`), and `Gfun v ψ` vanishes at `a` and `b` because `ψ` and `ψ'` do.  The
Fundamental Theorem of Calculus over `[a,b]` then gives `∫_a^b (Lfun - RHSfun) = 0`, and all five
integrals over `(0,π/2)` are equal to the corresponding integrals over `[a,b]` because every
integrand is supported there. -/
theorem sliceThetaIbpSep (v ψ : ℝ → ℝ)
    (hv : ContDiffOn ℝ 2 v (Set.Ioo 0 (Real.pi / 2)))
    (hψ : ContDiff ℝ 2 ψ)
    (hsep : ∃ a b : ℝ, 0 < a ∧ a < b ∧ b < Real.pi / 2 ∧ tsupport ψ ⊆ Set.Ioo a b) :
    (∫ θ in Set.Ioo 0 (Real.pi / 2),
        (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) * ψ θ * (v θ * deriv (deriv v) θ))
      = -2 * Work.Spaces.eta * (∫ θ in Set.Ioo 0 (Real.pi / 2),
            (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) * ψ θ * (v θ) ^ 2)
        - ((1 - Work.Spaces.eta) / (1 + Work.Spaces.eta)) * (∫ θ in Set.Ioo 0 (Real.pi / 2),
            (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) * ψ θ * (deriv v θ) ^ 2)
        - (2 * Work.Spaces.eta / (1 + Work.Spaces.eta)) * (∫ θ in Set.Ioo 0 (Real.pi / 2),
            (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) * ψ θ
              * (deriv v θ - (1 + Work.Spaces.eta) * v θ * Real.cos (2 * θ)
                  * (Real.sin (2 * θ)) ^ (-(1 : ℝ))) ^ 2)
        + (1 / 2) * (∫ θ in Set.Ioo 0 (Real.pi / 2),
            (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) * deriv (deriv ψ) θ * (v θ) ^ 2) := by
  obtain ⟨a, b, ha, hab, hb, hsupp⟩ := hsep
  have hab' : a ≤ b := le_of_lt hab
  -- `[a,b]` sits inside the open interval
  have hsub : Set.uIcc a b ⊆ Set.Ioo 0 (Real.pi / 2) := by
    rw [Set.uIcc_of_le hab']
    intro θ hθ
    exact ⟨lt_of_lt_of_le ha hθ.1, lt_of_le_of_lt hθ.2 hb⟩
  -- `ψ` and its derivatives vanish at and beyond the ends of `[a,b]`
  have hnotmem : ∀ {θ : ℝ}, θ ∉ Set.Ioo a b → θ ∉ tsupport ψ := fun hx h => hx (hsupp h)
  have hψa : ψ a = 0 := image_eq_zero_of_notMem_tsupport (hnotmem (by simp))
  have hψb : ψ b = 0 := image_eq_zero_of_notMem_tsupport (hnotmem (by simp))
  have hdψa : deriv ψ a = 0 := deriv_eq_zero_of_notMem_tsupport (hnotmem (by simp))
  have hdψb : deriv ψ b = 0 := deriv_eq_zero_of_notMem_tsupport (hnotmem (by simp))
  have key : ∀ θ, 0 < θ → θ < Real.pi / 2 → (θ < a ∨ b < θ) → θ ∉ tsupport ψ := by
    intro θ _ _ h3 h
    have h4 := hsupp h
    rcases h3 with h3 | h3 <;> linarith [h4.1, h4.2]
  -- support facts for the five integrands
  have hL0 : ∀ θ, 0 < θ → θ < Real.pi / 2 → (θ < a ∨ b < θ) → Lfun v ψ θ = 0 := by
    intro θ h1 h2 h3
    have hz := image_eq_zero_of_notMem_tsupport (key θ h1 h2 h3)
    simp only [Lfun]
    rw [hz]
    ring
  have hA0 : ∀ θ, 0 < θ → θ < Real.pi / 2 → (θ < a ∨ b < θ) → Afun v ψ θ = 0 := by
    intro θ h1 h2 h3
    have hz := image_eq_zero_of_notMem_tsupport (key θ h1 h2 h3)
    simp only [Afun]
    rw [hz]
    ring
  have hB0 : ∀ θ, 0 < θ → θ < Real.pi / 2 → (θ < a ∨ b < θ) → Bfun v ψ θ = 0 := by
    intro θ h1 h2 h3
    have hz := image_eq_zero_of_notMem_tsupport (key θ h1 h2 h3)
    simp only [Bfun]
    rw [hz]
    ring
  have hC0 : ∀ θ, 0 < θ → θ < Real.pi / 2 → (θ < a ∨ b < θ) → Cfun v ψ θ = 0 := by
    intro θ h1 h2 h3
    have hz := image_eq_zero_of_notMem_tsupport (key θ h1 h2 h3)
    simp only [Cfun]
    rw [hz]
    ring
  have hD0 : ∀ θ, 0 < θ → θ < Real.pi / 2 → (θ < a ∨ b < θ) → Dfun v ψ θ = 0 := by
    intro θ h1 h2 h3
    have hz := deriv_deriv_eq_zero_of_notMem_tsupport (key θ h1 h2 h3)
    simp only [Dfun]
    rw [hz]
    ring
  -- convert every integral to an interval integral over `[a,b]`
  have hLc := setIntegral_Ioo_eq_intervalIntegral_of_support (f := Lfun v ψ) ha hb hab' hL0
  have hAc := setIntegral_Ioo_eq_intervalIntegral_of_support (f := Afun v ψ) ha hb hab' hA0
  have hBc := setIntegral_Ioo_eq_intervalIntegral_of_support (f := Bfun v ψ) ha hb hab' hB0
  have hCc := setIntegral_Ioo_eq_intervalIntegral_of_support (f := Cfun v ψ) ha hb hab' hC0
  have hDc := setIntegral_Ioo_eq_intervalIntegral_of_support (f := Dfun v ψ) ha hb hab' hD0
  -- integrability
  obtain ⟨iL, iA, iB, iC, iD, iRHS, iGd⟩ := intervalIntegrable_pieces v ψ hv hψ ha hb hab'
  -- the FTC identity for `Gfun`
  have hFTC : (∫ θ in a..b, (Lfun v ψ θ - RHSfun v ψ θ)) = Gfun v ψ b - Gfun v ψ a :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun θ hθ => hasDerivAt_Gfun v ψ hv hψ (hsub hθ)) iGd
  have hGa : Gfun v ψ a = 0 := by simp [Gfun, hψa, hdψa]
  have hGb : Gfun v ψ b = 0 := by simp [Gfun, hψb, hdψb]
  have hzero : (∫ θ in a..b, (Lfun v ψ θ - RHSfun v ψ θ)) = 0 := by
    rw [hFTC, hGb, hGa, sub_zero]
  have hEq : (∫ θ in a..b, Lfun v ψ θ) = ∫ θ in a..b, RHSfun v ψ θ := by
    have hsplit : (∫ θ in a..b, (Lfun v ψ θ - RHSfun v ψ θ))
        = (∫ θ in a..b, Lfun v ψ θ) - ∫ θ in a..b, RHSfun v ψ θ :=
      intervalIntegral.integral_sub iL iRHS
    linarith [hsplit, hzero]
  -- decompose the RHS integrand into its four pieces
  have hA' : IntervalIntegrable (fun θ => -2 * Work.Spaces.eta * Afun v ψ θ) volume a b :=
    iA.const_mul (-2 * Work.Spaces.eta)
  have hB' : IntervalIntegrable
      (fun θ => ((1 - Work.Spaces.eta) / (1 + Work.Spaces.eta)) * Bfun v ψ θ) volume a b :=
    iB.const_mul _
  have hC' : IntervalIntegrable
      (fun θ => (2 * Work.Spaces.eta / (1 + Work.Spaces.eta)) * Cfun v ψ θ) volume a b :=
    iC.const_mul _
  have hD' : IntervalIntegrable (fun θ => (1 / 2) * Dfun v ψ θ) volume a b :=
    iD.const_mul (1 / 2)
  have hAB : IntervalIntegrable (fun θ => -2 * Work.Spaces.eta * Afun v ψ θ
      - ((1 - Work.Spaces.eta) / (1 + Work.Spaces.eta)) * Bfun v ψ θ) volume a b :=
    hA'.sub hB'
  have hABC : IntervalIntegrable (fun θ => -2 * Work.Spaces.eta * Afun v ψ θ
      - ((1 - Work.Spaces.eta) / (1 + Work.Spaces.eta)) * Bfun v ψ θ
      - (2 * Work.Spaces.eta / (1 + Work.Spaces.eta)) * Cfun v ψ θ) volume a b :=
    hAB.sub hC'
  have hcombine : (∫ θ in a..b, RHSfun v ψ θ)
      = -2 * Work.Spaces.eta * (∫ θ in a..b, Afun v ψ θ)
        - ((1 - Work.Spaces.eta) / (1 + Work.Spaces.eta)) * (∫ θ in a..b, Bfun v ψ θ)
        - (2 * Work.Spaces.eta / (1 + Work.Spaces.eta)) * (∫ θ in a..b, Cfun v ψ θ)
        + (1 / 2) * (∫ θ in a..b, Dfun v ψ θ) := by
    simp only [RHSfun]
    rw [intervalIntegral.integral_add hABC hD', intervalIntegral.integral_sub hAB hC',
      intervalIntegral.integral_sub hA' hB', intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const_mul]
  have hmain := hEq
  rw [hcombine] at hmain
  rw [← hLc, ← hAc, ← hBc, ← hCc, ← hDc] at hmain
  simpa only [Lfun, Afun, Bfun, Cfun, Dfun, sig] using hmain

end Work.FTS.EllipticEst.Cores.AeStep2Aux.I1Wk
end
end
-- ===== merged: Submission.Work.FTS.EllipticEst.Cores.Pieces.AeGradRho.AeCutEnergyClean =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

namespace Work.FTS.EllipticEst.Cores.Pieces.AeGradRho

open scoped Real Topology ENNReal
open MeasureTheory Set Filter

set_option autoImplicit false

/-- The radial cut weight `W = φ w²` of the truncated energy inequality. -/
def cutW (φ : ℝ → ℝ) (z : ℝ) : ℝ := φ z * (Work.Spaces.w z) ^ 2

/-- **The statement of the truncated `w²`-weighted energy inequality** of Step 1 of `prop:H2` in
the `AeData` class, as a `Prop`.  For a `C²` cut-off `φ` with `0 ≤ φ ≤ 1`, compact support and
`φ = 0` near `z = 0`,

`α²∫⁻ (φw²z²)(∫⁻ (∂_zu)²) + ∫⁻ (φw²)(∫⁻ (∂_θu)²)
   ≤ K ∫⁻ (φw²)(∫⁻ u²) + ½∫⁻ (φw²)(∫⁻ G²σ) + err`,

where `K = 13/2 + 3α² + (3/2)α(5+α)` and `err` is the explicit truncation error.  Same statement
as `H2W.AeProof.AeCutEnergyV2`, minus the (unused) a.e.-continuity hypothesis. -/
def AeCutEnergyProp (α : ℝ) (u G : ℝ → ℝ → ℝ) : Prop :=
  Work.FTS.EllipticEst.H2W.Ae.AeData α u G →
  (∀ᵐ z ∂(MeasureTheory.volume.restrict (Set.Ioi 0)),
    Filter.Tendsto (fun θ => u z θ) (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0)) →
  (∀ᵐ z ∂(MeasureTheory.volume.restrict (Set.Ioi 0)),
    Filter.Tendsto (fun θ => u z θ) (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds 0)) →
  ∀ (φ : ℝ → ℝ),
    ContDiff ℝ 2 φ → HasCompactSupport φ → (∀ z : ℝ, z ≤ 0 → φ z = 0) →
    (∀ z : ℝ, 0 ≤ φ z) → (∀ z : ℝ, φ z ≤ 1) →
    (∃ δ : ℝ, 0 < δ ∧ ∀ z : ℝ, z ≤ δ → φ z = 0) →
    ((∫⁻ z in Work.Spaces.Iz, ENNReal.ofReal (φ z * (Work.Spaces.w z) ^ 2)
        * (∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal ((u z θ) ^ 2))) ≠ ⊤) →
    ENNReal.ofReal (α ^ 2) * (∫⁻ z in Work.Spaces.Iz,
        ENNReal.ofReal (φ z * (Work.Spaces.w z) ^ 2 * z ^ 2)
          * (∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal ((Work.Spaces.pz u z θ) ^ 2)))
      + (∫⁻ z in Work.Spaces.Iz, ENNReal.ofReal (φ z * (Work.Spaces.w z) ^ 2)
          * (∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal ((Work.Spaces.pth u z θ) ^ 2)))
    ≤ ENNReal.ofReal (13 / 2 + (3 * α ^ 2 + (3 / 2) * α * (5 + α)))
        * (∫⁻ z in Work.Spaces.Iz, ENNReal.ofReal (φ z * (Work.Spaces.w z) ^ 2)
            * (∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal ((u z θ) ^ 2)))
      + ENNReal.ofReal (1 / 2)
        * (∫⁻ z in Work.Spaces.Iz, ENNReal.ofReal (φ z * (Work.Spaces.w z) ^ 2)
            * (∫⁻ θ in Work.Spaces.Iθ,
                ENNReal.ofReal ((G z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)))
      + ENNReal.ofReal ((α ^ 2 / 2) * (∫ z in Work.Spaces.Iz,
            (2 * |deriv φ z| * |deriv (fun z => z ^ 2 * (Work.Spaces.w z) ^ 2) z|
              + |deriv (deriv φ) z| * (z ^ 2 * (Work.Spaces.w z) ^ 2))
              * (∫ θ in Work.Spaces.Iθ, (u z θ) ^ 2))
          + (α * (5 + α) / 2) * (∫ z in Work.Spaces.Iz,
              |deriv φ z| * (z * (Work.Spaces.w z) ^ 2)
                * (∫ θ in Work.Spaces.Iθ, (u z θ) ^ 2)))

end Work.FTS.EllipticEst.Cores.Pieces.AeGradRho
end
end
-- ===== merged: Submission.Work.FTS.EllipticEst.GbarSetup =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

/-! ## The Hardy operator of `Ḡ` -/

/-- `β = 5/α`, the exponent of `Ḡ` (the larger indicial root of the associated Euler
equation). -/
def bet (α : ℝ) : ℝ := 5 / α

/-- The weighted Hardy operator `HarOp β g z = z^{-β} ∫_0^z s^{β-1} g(s) ds`, of which
`Gbar α F` is `-(3/(4α)) · HarOp (5/α) (F_*)`. -/
def HarOp (β : ℝ) (g : ℝ → ℝ) (z : ℝ) : ℝ :=
  z ^ (-β) * ∫ s in (0 : ℝ)..z, s ^ (β - 1) * g s

/-- `Gbar α F` is `-(3/(4α))` times the Hardy operator applied to `F_*(F)`. -/
theorem Gbar_eq_HarOp (α : ℝ) (hα : α ≠ 0) (F : ℝ → ℝ → ℝ) (z : ℝ) :
    Work.Elliptic.Gbar α F z
      = -(3 / (4 * α)) * HarOp (bet α) (fun s => Work.Elliptic.Fstar F s) z := by
  have hexp : (5 - α) / α = 5 / α - 1 := (div_sub_one hα).symm
  simp only [Work.Elliptic.Gbar, bet, HarOp]
  rw [intervalIntegral.integral_congr (fun s _ => by rw [hexp])]
  ring

/-! ## The one-variable `D_z`-operator and its iterates -/

/-- The one-variable version `g ↦ z ∂_z g` of the paper's `D_z`. -/
def rDz (g : ℝ → ℝ) : ℝ → ℝ := fun z => z * deriv g z

/-- Iterated `rDz`. -/
def rDzIter : ℕ → (ℝ → ℝ) → (ℝ → ℝ)
  | 0, g => g
  | n + 1, g => rDz (rDzIter n g)

@[simp] theorem rDzIter_zero (g : ℝ → ℝ) : rDzIter 0 g = g := rfl

@[simp] theorem rDzIter_succ (n : ℕ) (g : ℝ → ℝ) :
    rDzIter (n + 1) g = rDz (rDzIter n g) := rfl


/-! ## The angular profile of `D_θ^i (sin 2θ)` -/

/-- `D_θ^i (sin 2θ)`, as a function of the angle.  This is the angular profile of
`D_z^j D_θ^i (Ḡ(z) sin 2θ)`. -/
def sinIter (i : ℕ) (θ : ℝ) : ℝ :=
  Work.Spaces.DthIter i (fun _ θ' => Real.sin (2 * θ')) 0 θ


end Work.FTS.EllipticEst
end
end
-- ===== merged: Submission.Work.FTS.EllipticEst.H2W.PropH2Base =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst

set_option autoImplicit false





/-! ## The two weak classes

`WeakPos2` is the hypothesis list of the target, bundled; `WeakPos0` is the level-`0` analogue,
the class of the pair `(G, Φ)` that the level-`0` estimate is applied to.  Both differ from
`TT.EllWeakPos` in that the honesty of the two *left-hand side* quantities is **not** demanded —
only the source is honest.  (The moment conditions are demanded for `z > 0` only, which is the
form in which the estimate is applied to the radially differentiated data; in `WeakPos0` they
are demanded only **a.e.** in `z`, because that is what the shift `D_z^j` of the moment condition
delivers: the pointwise-in-`z` form for the shifted data is *not* a consequence of the level-`2`
hypotheses — see `H2W/Fstar_DzIter_two_F.lean` and `remov/NOTES_Fstar_DzIter_one_eq_zero.md`,
and since the estimate is an inequality between integrals, a.e. information suffices.) -/




/-! ## `weakPureFts`: the pure components, from the level-`0` estimate and the shift

The pure components of the two level-`2` integrands are the level-`0` quantities of the
radially differentiated data `(D_z^j F, D_z^j Ψ)`, `j ≤ 2`; the paper's Step 3 is exactly the
statement that those data are again admissible, and the level-`0` estimate applied to them gives
the pure bound. -/


/-! ## The three weak-class pieces, and the assembly

`PA`, `PB` below are the *pure* (`D_z`-only) components of the two left-hand side integrands at
level `2`: `PA = ∑_{j≤2} |z²∂_zz(D_z^jΨ)·w·sin(2θ)^{-η/2}|²_{L²}` and
`PB = ∑_{j≤2} |∂_θθ(D_z^jΨ)·w·sin(2θ)^{-η/2}|²_{L²}`.  They are the quantities controlled by the
level-`0` estimate applied to the shifted data `(D_z^jF, D_z^jΨ)`, `j ≤ 2`. -/


end Work.FTS.EllipticEst
end
-- ===== merged: Submission.Work.FTS.EllipticEst.H2W.SlotA.weightedNLePp =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.H2W.SlotA



end Work.FTS.EllipticEst.H2W.SlotA
end
-- ===== merged: Submission.Work.FTS.EllipticEst.H2W.mixedABasic =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
Copyright: work module for the Elgindi finite-time singularity project.

# `H2W/mixedABasic`: the elementary structural layer of `mixedA`

`mixedA`'s right-hand side is the *pure* (`z`-only) part of `HkSq α 2 (z²∂_z²Ψ)`; this module
proves the calculus facts that identify it as such, and nothing else, so that it can be imported
freely (the module carrying the target itself, `H2W/mixedA`, still contains the open `sorry`).

* `DzIter_add`, `pzIter_add` — the `D_z`/`∂_z` iterates compose;
* `z2_mul_deriv_deriv` — pointwise `z² g'' = z(z g')' − z g'` for a one-variable function;
* `z2_pzIter2_eq` — pointwise `z²∂_z² = D_z² − D_z` in the `(z,θ)` variables.

From these, `z²∂_z²` commutes with every `D_z^j` (both are polynomials in `D_z`), which is the
identity used by `H2W/mixedA` and by `H2W/hksqSplitMixed`.
-/

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.H2W

set_option autoImplicit false

/-! ## The iterates compose -/

theorem DzIter_add (a b : ℕ) (f : ℝ → ℝ → ℝ) :
    Work.Spaces.DzIter (a + b) f = Work.Spaces.DzIter a (Work.Spaces.DzIter b f) := by
  induction a with
  | zero => simp
  | succ a ih => rw [Nat.succ_add, Work.Spaces.DzIter_succ, ih, Work.Spaces.DzIter_succ]

theorem pzIter_add (a b : ℕ) (f : ℝ → ℝ → ℝ) :
    Work.Spaces.pzIter (a + b) f = Work.Spaces.pzIter a (Work.Spaces.pzIter b f) := by
  induction a with
  | zero => simp
  | succ a ih => rw [Nat.succ_add, Work.Spaces.pzIter_succ, ih, Work.Spaces.pzIter_succ]

/-! ## The operator identity `z²∂_z² = D_z² − D_z` -/



end Work.FTS.EllipticEst.H2W
end
end
-- ===== merged: Submission.Work.FTS.EllipticEst.Honest.I4SliceDefs =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The slice objects of the honest `I₄` upper bound

This module owns the vocabulary of the single-slice estimate
`Work.FTS.EllipticEst.Honest.I4SliceBound`: the angular slice `Φ` of a stream function,
`ψ = Φ / cos θ`, `b = Φ''`, `u = ∂_θ(tan θ · Φ)`, `P = cos²θ · ψ'`, the angular weight
`σ = sin(2θ)^{-99/100}`, the coefficient `Σ = (1-η)cos²θ + (3+η)sin²θ` (`η = 99/100`) and the
boundary primitive `G = ½ (sin θ / cos³θ) · σ · P²` together with its un-halved version `H`
(the quantity whose vanishing at `π/2⁻` is the hypothesis `hBound` of the target).

Everything is defined with the *literal* expressions of the target statement, so that
`simp only [I4sig, I4Σ, ...]` unfolds these abbreviations to the text of
`Work.FTS.EllipticEst.Honest.I4SliceBound`.
-/

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.Honest

set_option autoImplicit false

/-- The angular weight `σ θ = sin(2θ)^{-99/100}` of the `I₄` slice estimate. -/
def I4sig (θ : ℝ) : ℝ := (Real.sin (2 * θ)) ^ (-(99 / 100 : ℝ))

/-- The angle coefficient `Σ θ = (1-η)cos²θ + (3+η)sin²θ`, `η = 99/100`. -/
def I4Sig (θ : ℝ) : ℝ := (1 - 99 / 100) * (Real.cos θ) ^ 2 + (3 + 99 / 100) * (Real.sin θ) ^ 2

/-- `ψ = Φ / cos θ`. -/
def I4psi (Φ : ℝ → ℝ) : ℝ → ℝ := fun θ => Φ θ / Real.cos θ

/-- `b = Φ''`. -/
def I4b (Φ : ℝ → ℝ) : ℝ → ℝ := fun θ => deriv (deriv Φ) θ

/-- `u = ∂_θ(tan θ · Φ)`. -/
def I4u (Φ : ℝ → ℝ) : ℝ → ℝ := fun θ => deriv (fun θ' => Real.tan θ' * Φ θ') θ

/-- `P = cos²θ · ψ'`. -/
def I4P (Φ : ℝ → ℝ) : ℝ → ℝ := fun θ => (Real.cos θ) ^ 2 * deriv (I4psi Φ) θ

/-- `G θ = ½ · (sin θ / cos³θ) · σ θ · P θ²`, the primitive of the `I₄` boundary term. -/
def I4G (Φ : ℝ → ℝ) : ℝ → ℝ :=
  fun θ => (1 / 2) * (Real.sin θ / (Real.cos θ) ^ 3) * I4sig θ * (I4P Φ θ) ^ 2

/-- The boundary quantity of `hBound`: `H = (sin θ / cos³θ) · (cos²θ · ψ')² · σ`. -/
def I4H (Φ : ℝ → ℝ) : ℝ → ℝ :=
  fun θ => Real.sin θ / (Real.cos θ) ^ 3 * ((Real.cos θ) ^ 2 * deriv (I4psi Φ) θ) ^ 2
    * I4sig θ

/-! ## Elementary pointwise facts -/

theorem I4sig_nonneg {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) : 0 ≤ I4sig θ := by
  rw [I4sig]
  refine Real.rpow_nonneg ?_ _
  exact Real.sin_nonneg_of_nonneg_of_le_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])

theorem I4sig_pos {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) : 0 < I4sig θ := by
  rw [I4sig]
  exact Real.rpow_pos_of_pos
    (Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])) _

theorem I4Sig_ge (θ : ℝ) : 1 / 100 ≤ I4Sig θ := by
  have hs := Real.sin_sq_add_cos_sq θ
  rw [I4Sig]
  nlinarith [sq_nonneg (Real.cos θ), sq_nonneg (Real.sin θ)]

theorem I4Sig_pos (θ : ℝ) : 0 < I4Sig θ := lt_of_lt_of_le (by norm_num) (I4Sig_ge θ)

theorem I4H_eq_two_mul_I4G (Φ : ℝ → ℝ) (θ : ℝ) :
    I4H Φ θ = 2 * I4G Φ θ := by
  simp only [I4H, I4G, I4P]
  ring

theorem I4G_nonneg (Φ : ℝ → ℝ) {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    0 ≤ I4G Φ θ := by
  have hc : 0 < Real.cos θ :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith [hθ.1, Real.pi_pos], hθ.2⟩
  have hs : 0 < Real.sin θ :=
    Real.sin_pos_of_mem_Ioo ⟨hθ.1, by linarith [hθ.2, Real.pi_pos]⟩
  simp only [I4G]
  have hσ : 0 ≤ I4sig θ := le_of_lt (I4sig_pos hθ)
  have h1 : 0 ≤ Real.sin θ / (Real.cos θ) ^ 3 :=
    div_nonneg (le_of_lt hs) (by positivity)
  have h2 : 0 ≤ (I4P Φ θ) ^ 2 := sq_nonneg _
  have h3 : (0:ℝ) ≤ 1 / 2 := by norm_num
  exact mul_nonneg (mul_nonneg (mul_nonneg h3 h1) hσ) h2


end Work.FTS.EllipticEst.Honest
end
end
-- ===== merged: Submission.Work.FTS.EllipticEst.Honest.SelfAux.SliceDerivBound =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.Honest.SelfAux

open MeasureTheory Set Filter
open scoped Topology

/-! ## Boundedness of `u'` on `(0, π/2)`

We prove the two auxiliary estimates on which `SliceDerivBound` rests:

* `abs_deriv_sub_pi_div_four_le` — Newton–Leibniz on `[θ, π/4]` for `θ ≤ π/4` and on
  `[π/4, θ]` for `π/4 ≤ θ`, i.e. `|u' θ - u' (π/4)| ≤ ∫_{(0,π/2)} |u''|`;
* `abs_deriv_le_integral` — the triangle inequality `|u' θ| ≤ |u' (π/4)| + |u' θ - u' (π/4)|`.

The template for the sub-integral estimate is
`Work.FTS.EllipticEst.sliceLim_abs_deriv_le_of_second_deriv_integrableOn`, which treats only
`θ ∈ (0, π/4)`; here the *symmetric* half `θ ∈ [π/4, π/2)` is handled as well, which is what
turns an upper bound near `0` into a bound on the whole open interval. -/

/-- **Newton–Leibniz across `π/4`.**  If `u'' = deriv (fun t => deriv u t)` is the derivative of
`u'` on `(0, π/2)` and `|u''|` is integrable there, then for every `θ ∈ (0, π/2)` the increment
of `u'` between `θ` and `π/4` is bounded by the total mass of `|u''|` on `(0, π/2)`.

The two sides of `π/4` are handled by Newton–Leibniz on `[θ, π/4]` (for `θ ≤ π/4`) respectively
on `[π/4, θ]` (for `π/4 ≤ θ`). -/
lemma abs_deriv_sub_pi_div_four_le {u : ℝ → ℝ}
    (hderiv : ∀ x ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      HasDerivAt (deriv u) (deriv (fun t : ℝ => deriv u t) x) x)
    (hg : MeasureTheory.IntegrableOn (fun θ : ℝ => |deriv (fun t : ℝ => deriv u t) θ|)
      (Set.Ioo (0 : ℝ) (Real.pi / 2)))
    {θ : ℝ} (hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)) :
    |deriv u θ - deriv u (Real.pi / 4)|
      ≤ ∫ s in Set.Ioo (0 : ℝ) (Real.pi / 2),
          |deriv (fun t : ℝ => deriv u t) s| := by
  have hc0 : (0 : ℝ) < Real.pi / 4 := by linarith [Real.pi_pos]
  have hclt : Real.pi / 4 < Real.pi / 2 := by linarith [Real.pi_pos]
  rcases le_total θ (Real.pi / 4) with hle | hle
  · -- `θ ≤ π/4`: Newton–Leibniz on `[θ, π/4]`
    have hsub : Set.Icc θ (Real.pi / 4) ⊆ Set.Ioo (0 : ℝ) (Real.pi / 2) :=
      fun x hx => ⟨lt_of_lt_of_le hθ.1 hx.1, lt_of_le_of_lt hx.2 hclt⟩
    have hIcc : MeasureTheory.IntegrableOn
        (fun x : ℝ => |deriv (fun t : ℝ => deriv u t) x|) (Set.Icc θ (Real.pi / 4)) :=
      hg.mono_set hsub
    have hint : MeasureTheory.IntegrableOn (deriv (fun t : ℝ => deriv u t))
        (Set.Icc θ (Real.pi / 4)) :=
      MeasureTheory.Integrable.mono' hIcc
        (measurable_deriv (fun t : ℝ => deriv u t)).aestronglyMeasurable
        (Filter.Eventually.of_forall fun x => by rw [Real.norm_eq_abs])
    have hmain :=
      Work.FTS.EllipticEst.sliceLim_abs_sub_le_setIntegral (f := deriv u)
        (f' := fun t : ℝ => deriv (fun t' : ℝ => deriv u t') t)
        (a := θ) (b := Real.pi / 4) (c := Real.pi / 4) hle le_rfl
        (fun x hx => hderiv x (hsub hx)) hint
    have hmono : ∫ x in Set.Ioc θ (Real.pi / 4),
          |deriv (fun t : ℝ => deriv u t) x|
        ≤ ∫ s in Set.Ioo (0 : ℝ) (Real.pi / 2),
            |deriv (fun t : ℝ => deriv u t) s| :=
      MeasureTheory.setIntegral_mono_set hg
        (Filter.Eventually.of_forall fun x => abs_nonneg _)
        (Filter.Eventually.of_forall fun x hx =>
          ⟨lt_trans hθ.1 hx.1, lt_of_le_of_lt hx.2 hclt⟩)
    rw [abs_sub_comm]
    exact hmain.trans hmono
  · -- `π/4 ≤ θ`: Newton–Leibniz on `[π/4, θ]`
    have hsub : Set.Icc (Real.pi / 4) θ ⊆ Set.Ioo (0 : ℝ) (Real.pi / 2) :=
      fun x hx => ⟨lt_of_lt_of_le hc0 hx.1, lt_of_le_of_lt hx.2 hθ.2⟩
    have hIcc : MeasureTheory.IntegrableOn
        (fun x : ℝ => |deriv (fun t : ℝ => deriv u t) x|) (Set.Icc (Real.pi / 4) θ) :=
      hg.mono_set hsub
    have hint : MeasureTheory.IntegrableOn (deriv (fun t : ℝ => deriv u t))
        (Set.Icc (Real.pi / 4) θ) :=
      MeasureTheory.Integrable.mono' hIcc
        (measurable_deriv (fun t : ℝ => deriv u t)).aestronglyMeasurable
        (Filter.Eventually.of_forall fun x => by rw [Real.norm_eq_abs])
    have hmain :=
      Work.FTS.EllipticEst.sliceLim_abs_sub_le_setIntegral (f := deriv u)
        (f' := fun t : ℝ => deriv (fun t' : ℝ => deriv u t') t)
        (a := Real.pi / 4) (b := θ) (c := θ) hle le_rfl
        (fun x hx => hderiv x (hsub hx)) hint
    have hmono : ∫ x in Set.Ioc (Real.pi / 4) θ,
          |deriv (fun t : ℝ => deriv u t) x|
        ≤ ∫ s in Set.Ioo (0 : ℝ) (Real.pi / 2),
            |deriv (fun t : ℝ => deriv u t) s| :=
      MeasureTheory.setIntegral_mono_set hg
        (Filter.Eventually.of_forall fun x => abs_nonneg _)
        (Filter.Eventually.of_forall fun x hx =>
          ⟨lt_trans hc0 hx.1, lt_of_le_of_lt hx.2 hθ.2⟩)
    exact hmain.trans hmono

/-- **`u'` is bounded on `(0, π/2)` by its value at `π/4` plus the mass of `|u''|`.** -/
lemma abs_deriv_le_of_second_deriv_integrableOn {u : ℝ → ℝ}
    (hderiv : ∀ x ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      HasDerivAt (deriv u) (deriv (fun t : ℝ => deriv u t) x) x)
    (hg : MeasureTheory.IntegrableOn (fun θ : ℝ => |deriv (fun t : ℝ => deriv u t) θ|)
      (Set.Ioo (0 : ℝ) (Real.pi / 2))) :
    ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      |deriv u θ| ≤ |deriv u (Real.pi / 4)|
        + ∫ s in Set.Ioo (0 : ℝ) (Real.pi / 2),
            |deriv (fun t : ℝ => deriv u t) s| := by
  intro θ hθ
  have hdiff := abs_deriv_sub_pi_div_four_le hderiv hg hθ
  have hsum : |deriv u θ| ≤ |deriv u (Real.pi / 4)|
      + |deriv u θ - deriv u (Real.pi / 4)| := by
    have hid : deriv u θ = deriv u (Real.pi / 4)
        + (deriv u θ - deriv u (Real.pi / 4)) := by ring
    rw [abs_le]
    constructor
    · linarith [neg_abs_le (deriv u (Real.pi / 4)),
        le_abs_self (deriv u (Real.pi / 4)),
        neg_abs_le (deriv u θ - deriv u (Real.pi / 4)),
        le_abs_self (deriv u θ - deriv u (Real.pi / 4)), hid]
    · linarith [neg_abs_le (deriv u (Real.pi / 4)),
        le_abs_self (deriv u (Real.pi / 4)),
        neg_abs_le (deriv u θ - deriv u (Real.pi / 4)),
        le_abs_self (deriv u θ - deriv u (Real.pi / 4)), hid]
  linarith

/-- **Boundedness of `u'` on `(0,π/2)` from the integrability of `u''`.**  For `u : ℝ → ℝ` of
class `C²` on the open interval `(0, π/2)` whose second derivative
`u'' = deriv (fun θ' => deriv u θ')` is integrable there, `u' = deriv u` is bounded on `(0, π/2)`.

Proof route: for `θ ∈ (0, π/4]`, Newton–Leibniz on `[θ, π/4]` gives
`|u' θ| ≤ |u' (π/4)| + ∫_{Ioo 0 (π/2)} |u''|` (the template is
`Work.FTS.EllipticEst.sliceLim_abs_deriv_le_of_second_deriv_integrableOn`, already proved in
`Submission/Work/FTS/EllipticEst/sliceLimitLeftExists.lean`); for `θ ∈ [π/4, π/2)` use the mirror
image on `[π/4, θ]`; combine the two bounds with `max`.  `u'` is differentiable on the open
interval with derivative `u''` because `u` is `C²` there (`ContDiffAt.derivWithin`).

Please declare it at the ROOT namespace (no `namespace` wrapper), so that its name is exactly
`SliceDerivBound`. -/
theorem SliceDerivBound (u : ℝ → ℝ)
    (hsm : ContDiffOn ℝ 2 u (Set.Ioo 0 (Real.pi / 2)))
    (hint : MeasureTheory.IntegrableOn (fun θ => deriv (fun θ' => deriv u θ') θ)
      (Set.Ioo 0 (Real.pi / 2))) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ θ ∈ Set.Ioo 0 (Real.pi / 2), |deriv u θ| ≤ M := by
  -- `u'` is differentiable on the open interval with derivative `u''`
  have hderiv : ∀ x ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      HasDerivAt (deriv u) (deriv (fun t : ℝ => deriv u t) x) x := by
    intro x hx
    have h2 : ContDiffAt ℝ 2 u x := hsm.contDiffAt (isOpen_Ioo.mem_nhds hx)
    have hd1 : ContDiffAt ℝ 1 (deriv u) x := h2.derivWithin (by norm_num)
    exact (hd1.differentiableAt (by norm_num)).hasDerivAt
  -- integrability of `|u''|` from integrability of `u''`
  have habs : MeasureTheory.IntegrableOn
      (fun θ : ℝ => |deriv (fun t : ℝ => deriv u t) θ|) (Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
    hint.abs
  refine ⟨max 0 (|deriv u (Real.pi / 4)|
      + ∫ s in Set.Ioo (0 : ℝ) (Real.pi / 2), |deriv (fun t : ℝ => deriv u t) s|),
    le_max_left _ _, fun θ hθ => ?_⟩
  exact (abs_deriv_le_of_second_deriv_integrableOn hderiv habs θ hθ).trans (le_max_right _ _)

end Work.FTS.EllipticEst.Honest.SelfAux
end
-- ===== merged: Submission.Work.FTS.EllipticEst.Honest.SliceHyp =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set

namespace Work.FTS.EllipticEst.Honest

/-- **The single-slice inequality of the honest `I₄` upper bound** (hypothesis of
`I4GlobalAssembly`): for every `Φ : ℝ → ℝ` of class `C²` on `(0, π/2)` whose weighted squares
`∫_θ (Φ/cos θ)²σ` and `∫_θ (Φ'')²σ` are integrable (`σ = sin(2θ)^{-η}`, `η = 99/100`),

`∫_θ ∂_θ(tan θ·Φ)·Φ''·σ ≤ 50∫_θ (Φ/cos θ)²σ + √(∫_θ(Φ/cos θ)²σ)·√(∫_θ(Φ'')²σ)`. -/
def SliceIneq : Prop :=
  ∀ (Φ : ℝ → ℝ), ContDiffOn ℝ 2 Φ (Set.Ioo 0 (Real.pi / 2)) →
      MeasureTheory.IntegrableOn
        (fun θ => (Φ θ / Real.cos θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(99 / 100 : ℝ)))
        (Set.Icc 0 (Real.pi / 2)) →
      MeasureTheory.IntegrableOn
        (fun θ => (deriv (deriv Φ) θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(99 / 100 : ℝ)))
        (Set.Icc 0 (Real.pi / 2)) →
      (∫ θ in Set.Icc 0 (Real.pi / 2),
          deriv (fun θ' => Real.tan θ' * Φ θ') θ * deriv (deriv Φ) θ
            * (Real.sin (2 * θ)) ^ (-(99 / 100 : ℝ)))
        ≤ 50 * (∫ θ in Set.Icc 0 (Real.pi / 2),
              (Φ θ / Real.cos θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(99 / 100 : ℝ)))
          + Real.sqrt (∫ θ in Set.Icc 0 (Real.pi / 2),
              (Φ θ / Real.cos θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(99 / 100 : ℝ)))
            * Real.sqrt (∫ θ in Set.Icc 0 (Real.pi / 2),
              (deriv (deriv Φ) θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(99 / 100 : ℝ)))

end Work.FTS.EllipticEst.Honest
end
end
-- ===== merged: Submission.Work.FTS.EllipticEst.Honest.integrableOn_wrho_mul_psiDeriv_mul_psiSecond =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.Honest

set_option autoImplicit false
set_option linter.unusedSimpArgs false

/-! ## Two helpers

The first is `L² · L² ⊆ L¹` for the angular weight written in the `sig`-form used by the
honest slice class; the second is the pointwise elimination of `ψ''` by the chain rule for
`u = cos θ · ψ`. -/

/-- **`L² · L² ⊆ L¹` for the angular weight `σ = sig`.**  If `f` and `g` are a.e. measurable
and `f² σ`, `g² σ` are integrable on `(0, π/2)`, then so is `f g σ`.

This is the `sig`-form of
`Work.FTS.EllipticEst.TanTheta.integrable_mul_of_sq_weight_of_aemeasurable`
(`σ θ = sin(2θ)^{-η}`). -/
private lemma integrable_mul_sig_of_sq_sig {f g : ℝ → ℝ}
    (hf : AEMeasurable f (MeasureTheory.volume.restrict (Set.Ioo 0 (Real.pi / 2))))
    (hg : AEMeasurable g (MeasureTheory.volume.restrict (Set.Ioo 0 (Real.pi / 2))))
    (hfsq : MeasureTheory.IntegrableOn
      (fun θ => f θ ^ 2 * Work.FTS.EllipticEst.AngSecond.sig θ)
      (Set.Ioo 0 (Real.pi / 2)))
    (hgsq : MeasureTheory.IntegrableOn
      (fun θ => g θ ^ 2 * Work.FTS.EllipticEst.AngSecond.sig θ)
      (Set.Ioo 0 (Real.pi / 2))) :
    MeasureTheory.IntegrableOn
      (fun θ => f θ * g θ * Work.FTS.EllipticEst.AngSecond.sig θ)
      (Set.Ioo 0 (Real.pi / 2)) := by
  refine (Work.FTS.EllipticEst.TanTheta.integrable_mul_of_sq_weight_of_aemeasurable
    Work.Spaces.eta hf hg ?_ ?_).congr_fun ?_ measurableSet_Ioo
  · exact hfsq.congr_fun (fun θ _ => by simp [Work.FTS.EllipticEst.AngSecond.sig])
      measurableSet_Ioo
  · exact hgsq.congr_fun (fun θ _ => by simp [Work.FTS.EllipticEst.AngSecond.sig])
      measurableSet_Ioo
  · intro θ _
    simp [Work.FTS.EllipticEst.AngSecond.sig]

/-- **The pointwise elimination of `ψ''`.**  With `ψ = u / cos` and `σ = sig`, at every point
`θ` with `cos θ ≠ 0`,

  `ρ θ · ψ'(θ) · ψ''(θ) = sin θ · σ θ · ψ'(θ) · u''(θ) + cos θ · (ψ(θ) · sin θ · ψ'(θ) · σ θ)
      + 2 · (sin θ · ψ'(θ)) · (sin θ · ψ'(θ)) · σ θ`

(`ρ = wrho η`).  It is the chain-rule identity
`Work.FTS.EllipticEst.Honest.cos_mul_derivDeriv_divCos`, multiplied by `sin θ · σ θ · ψ'(θ)`. -/
private lemma wrho_mul_deriv_mul_deriv_divCos (u : ℝ → ℝ) {θ : ℝ}
    (hu : ContDiffAt ℝ 2 u θ) (hcos : Real.cos θ ≠ 0) :
    Work.FTS.EllipticEst.TanTheta.wrho Work.Spaces.eta θ * deriv (fun t => u t / Real.cos t) θ
        * deriv (deriv (fun t => u t / Real.cos t)) θ
      = (Real.sin θ * deriv (fun t => u t / Real.cos t) θ) * deriv (deriv u) θ
          * Work.FTS.EllipticEst.AngSecond.sig θ
        + Real.cos θ * ((u θ / Real.cos θ)
            * (Real.sin θ * deriv (fun t => u t / Real.cos t) θ)
            * Work.FTS.EllipticEst.AngSecond.sig θ)
        + 2 * ((Real.sin θ * deriv (fun t => u t / Real.cos t) θ)
            * (Real.sin θ * deriv (fun t => u t / Real.cos t) θ)
            * Work.FTS.EllipticEst.AngSecond.sig θ) := by
  have h := cos_mul_derivDeriv_divCos u hu hcos
  have key := congrArg (fun x => Real.sin θ * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))
      * deriv (fun t => u t / Real.cos t) θ * x) h
  rw [mul_add, mul_add] at key
  simp only [Work.FTS.EllipticEst.TanTheta.wrho, Work.FTS.EllipticEst.AngSecond.sig]
  linear_combination key

/-- **Integrability of `ρ ψ' ψ''` on the angular slice, in the honest open-interval class.**

With `ψ = u / cos`, `σ = sin(2θ)^{-η}` (`η = Work.Spaces.eta`) and
`ρ = sin θ cos θ σ = Work.FTS.EllipticEst.TanTheta.wrho Work.Spaces.eta`, this says that
`∫_0^{π/2} ρ ψ' ψ''` is an honest integral, given the three integrabilities
`∫ (u'')² σ`, `∫ sin²θ (ψ')² σ`, `∫ ψ² σ` of the honest slice class.

It is the second integration-by-parts input (`hint2` of
`Work.FTS.EllipticEst.Honest.integral_Ioo_mul_deriv_eq_neg_half` with `f = ψ'`) of the proof of
`Work.FTS.EllipticEst.Honest.slice_ident_honest`, in which no integrability of `ρ ψ' ψ''` is
hypothesised and the second derivative `ψ''` must therefore be eliminated.

Hints (a full proof is expected):

* On `(0, π/2)` one has `cos θ ≠ 0`, so
  `Work.FTS.EllipticEst.Honest.cos_mul_derivDeriv_divCos` (from
  `Submission.Work.FTS.EllipticEst.Honest.derivDeriv_divCos`) turns the integrand, at every
  `θ ∈ Ioo 0 (π/2)`, into the sum of the three integrable pieces
  `sin θ · σ · ψ' · u''`, `sin θ · cos θ · σ · ψ · ψ' = (cos θ · ψ)·(sin θ · ψ')·σ` and
  `2 · sin²θ · σ · (ψ')²`.
* The first and the last follow from the `L² · L² ⊆ L¹` lemma
  `Work.FTS.EllipticEst.TanTheta.integrable_mul_of_sq_weight_of_aemeasurable`
  (`Submission/Work/FTS/EllipticEst/TanTheta/integrable_mul_of_sq_weight_of_aemeasurable.lean`,
  which also gives the `AEMeasurable` caveat) together with `hY` (for `sin²θ (ψ')² σ`) and `hX`
  (for `(u'')² σ`) -- the middle one uses `hA` (for `(cos θ · ψ)² σ`, via the bounded factor
  `cos²θ ≤ 1`) and `hY`.
* Conclude by `IntegrableOn.congr_fun` on the measurable set `Ioo 0 (π/2)` (note: no
  measurability of `ρ ψ' ψ''` itself is needed). -/
theorem integrableOn_wrho_mul_psiDeriv_mul_psiSecond (u : ℝ → ℝ)
    (hu : ContDiffOn ℝ 2 u (Set.Ioo 0 (Real.pi / 2)))
    (hX : MeasureTheory.IntegrableOn (fun θ => (deriv (deriv u) θ) ^ 2
      * Work.FTS.EllipticEst.AngSecond.sig θ) (Set.Ioo 0 (Real.pi / 2)))
    (hY : MeasureTheory.IntegrableOn (fun θ => (Real.sin θ) ^ 2
      * (deriv (fun θ => u θ / Real.cos θ) θ) ^ 2
      * Work.FTS.EllipticEst.AngSecond.sig θ) (Set.Ioo 0 (Real.pi / 2)))
    (hA : MeasureTheory.IntegrableOn (fun θ => (u θ / Real.cos θ) ^ 2
        * Work.FTS.EllipticEst.AngSecond.sig θ) (Set.Ioo 0 (Real.pi / 2))) :
    MeasureTheory.IntegrableOn (fun θ => Work.FTS.EllipticEst.TanTheta.wrho Work.Spaces.eta θ
      * deriv (fun θ => u θ / Real.cos θ) θ
      * deriv (deriv (fun θ => u θ / Real.cos θ)) θ)
      (Set.Ioo 0 (Real.pi / 2)) := by
  set ψ : ℝ → ℝ := fun θ => u θ / Real.cos θ with hψ_def
  set A : ℝ → ℝ := fun θ => Real.sin θ * deriv ψ θ with hA_def
  -- `cos` does not vanish on the open interval
  have hcos : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2), Real.cos θ ≠ 0 := by
    intro θ hθ
    exact ne_of_gt (Real.cos_pos_of_mem_Ioo
      ⟨by linarith [hθ.1, Real.pi_pos], by linarith [hθ.2]⟩)
  -- a.e. measurability of the three factors
  have hψ_meas : AEMeasurable ψ (MeasureTheory.volume.restrict (Set.Ioo 0 (Real.pi / 2))) :=
    (hu.continuousOn.aemeasurable measurableSet_Ioo).div Real.measurable_cos.aemeasurable
  have hA_meas : AEMeasurable A (MeasureTheory.volume.restrict (Set.Ioo 0 (Real.pi / 2))) :=
    Real.measurable_sin.aemeasurable.mul (aemeasurable_deriv ψ _)
  have hu''_meas : AEMeasurable (fun θ => deriv (deriv u) θ)
      (MeasureTheory.volume.restrict (Set.Ioo 0 (Real.pi / 2))) :=
    aemeasurable_deriv (deriv u) _
  -- the three squared-weighted integrabilities, in the `sig`-form
  have hψsq : MeasureTheory.IntegrableOn (fun θ => ψ θ ^ 2
      * Work.FTS.EllipticEst.AngSecond.sig θ) (Set.Ioo 0 (Real.pi / 2)) := hA
  have hX' : MeasureTheory.IntegrableOn (fun θ => (deriv (deriv u) θ) ^ 2
      * Work.FTS.EllipticEst.AngSecond.sig θ) (Set.Ioo 0 (Real.pi / 2)) := hX
  have hY' : MeasureTheory.IntegrableOn (fun θ => A θ ^ 2
      * Work.FTS.EllipticEst.AngSecond.sig θ) (Set.Ioo 0 (Real.pi / 2)) := by
    refine hY.congr_fun (fun θ _ => ?_) measurableSet_Ioo
    show (Real.sin θ) ^ 2 * (deriv ψ θ) ^ 2
        * Work.FTS.EllipticEst.AngSecond.sig θ
      = (Real.sin θ * deriv ψ θ) ^ 2 * Work.FTS.EllipticEst.AngSecond.sig θ
    ring
  -- the three integrable pieces of the decomposition
  have hAA : MeasureTheory.IntegrableOn
      (fun θ => A θ * A θ * Work.FTS.EllipticEst.AngSecond.sig θ)
      (Set.Ioo 0 (Real.pi / 2)) :=
    integrable_mul_sig_of_sq_sig hA_meas hA_meas hY' hY'
  have hAu'' : MeasureTheory.IntegrableOn
      (fun θ => A θ * deriv (deriv u) θ * Work.FTS.EllipticEst.AngSecond.sig θ)
      (Set.Ioo 0 (Real.pi / 2)) :=
    integrable_mul_sig_of_sq_sig hA_meas hu''_meas hY' hX'
  have hψA : MeasureTheory.IntegrableOn
      (fun θ => ψ θ * A θ * Work.FTS.EllipticEst.AngSecond.sig θ)
      (Set.Ioo 0 (Real.pi / 2)) :=
    integrable_mul_sig_of_sq_sig hψ_meas hA_meas hψsq hY'
  have hP2 : MeasureTheory.IntegrableOn
      (fun θ => Real.cos θ * (ψ θ * A θ * Work.FTS.EllipticEst.AngSecond.sig θ))
      (Set.Ioo 0 (Real.pi / 2)) :=
    (show MeasureTheory.Integrable
        (fun θ => ψ θ * A θ * Work.FTS.EllipticEst.AngSecond.sig θ)
        (MeasureTheory.volume.restrict (Set.Ioo 0 (Real.pi / 2))) from hψA).bdd_mul
      (c := 1) Real.continuous_cos.aestronglyMeasurable (by
        filter_upwards with θ
        rw [Real.norm_eq_abs]
        exact Real.abs_cos_le_one θ)
  have h3 : MeasureTheory.IntegrableOn
      (fun θ => 2 * (A θ * A θ * Work.FTS.EllipticEst.AngSecond.sig θ))
      (Set.Ioo 0 (Real.pi / 2)) :=
    (show MeasureTheory.Integrable
        (fun θ => A θ * A θ * Work.FTS.EllipticEst.AngSecond.sig θ)
        (MeasureTheory.volume.restrict (Set.Ioo 0 (Real.pi / 2))) from hAA).const_mul 2
  -- assemble
  have hsum : MeasureTheory.IntegrableOn
      (fun θ => A θ * deriv (deriv u) θ * Work.FTS.EllipticEst.AngSecond.sig θ
        + Real.cos θ * (ψ θ * A θ * Work.FTS.EllipticEst.AngSecond.sig θ)
        + 2 * (A θ * A θ * Work.FTS.EllipticEst.AngSecond.sig θ))
      (Set.Ioo 0 (Real.pi / 2)) :=
    (hAu''.add hP2).add h3
  refine hsum.congr_fun (fun θ hθ => ?_) measurableSet_Ioo
  exact (wrho_mul_deriv_mul_deriv_divCos u
    (hu.contDiffAt (isOpen_Ioo.mem_nhds hθ)) (hcos θ hθ)).symm

end Work.FTS.EllipticEst.Honest
end
end
-- ===== merged: Submission.Work.FTS.EllipticEst.Honest.omegaW_deriv_bounds =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# Derivative bounds for the truncated vorticity profile `z ↦ z w(z)² χ(z)`

`Work.Spaces.w z = (1+z)²/z²` is the radial weight of the paper.  This file proves the two
pointwise bounds needed for the *far field* of the truncated vorticity profile
`z ↦ z w(z)² χ(z)` and of the second `z`-derivative of `z ↦ z² w(z)² χ(z)`:

* `|d/dz (z w(z)² χ(z))| ≤ (3 + C₁) w(z)²`,
* `|d²/dz² (z² w(z)² χ(z))| ≤ (6 + 4C₁ + C₂) w(z)²`,

under the hypotheses `|z χ'(z)| ≤ C₁`, `|z² χ''(z)| ≤ C₂`, `|χ| ≤ 1` (so `χ` is a bounded
cutoff with bounded logarithmic derivatives, as produced by a smooth truncation).

The proof is an exact computation with the rational forms `w(z)² = (1+z)⁴/z⁴`,
`z w(z)² = (1+z)⁴/z³`, `z² w(z)² = (1+z)⁴/z²` and their derivatives (all available in
`Work.FTS.EllipticEst.weight_derivs_explicit`), followed by the elementary bounds
`|(z-3)/(1+z)| ≤ 3`, `|(2z²-4z+6)/(1+z)²| ≤ 6` and `|4(z-1)/(1+z)| ≤ 4` valid for `z > 0`.
-/

noncomputable section

open scoped Real Topology
open Filter

namespace Work.FTS.EllipticEst.Honest

/-! ## Elementary algebra of the weight `w` -/

/-- `w(z)² = (1+z)⁴/z⁴` for `z ≠ 0`. -/
private lemma w_sq_eq {z : ℝ} (hz : z ≠ 0) :
    (Work.Spaces.w z) ^ 2 = (1 + z) ^ 4 / z ^ 4 := by
  rw [Work.Spaces.w]
  field_simp

/-- `z · w(z)² = (1+z)⁴/z³` for `z ≠ 0`. -/
private lemma mul_w_sq_eq {z : ℝ} (hz : z ≠ 0) :
    z * (Work.Spaces.w z) ^ 2 = (1 + z) ^ 4 / z ^ 3 := by
  rw [Work.Spaces.w]
  field_simp

/-- `z² · w(z)² = (1+z)⁴/z²` for `z ≠ 0`. -/
private lemma sq_mul_w_sq_eq {z : ℝ} (hz : z ≠ 0) :
    z ^ 2 * (Work.Spaces.w z) ^ 2 = (1 + z) ^ 4 / z ^ 2 := by
  rw [Work.Spaces.w]
  field_simp

/-! ## Elementary bounds valid on `z > 0` -/

/-- `|(z-3)/(1+z)| ≤ 3` for `z > 0` (the supremum `3` is approached as `z → 0⁺`). -/
private lemma abs_coef1 {z : ℝ} (hz : 0 < z) : |(z - 3) / (1 + z)| ≤ 3 := by
  have h1z : (0 : ℝ) < 1 + z := by linarith
  rw [abs_div, abs_of_pos h1z, div_le_iff₀ h1z, abs_le]
  constructor <;> linarith

/-- `|(2z²-4z+6)/(1+z)²| ≤ 6` for `z > 0` (the supremum `6` is attained at `z = 0`). -/
private lemma abs_coef2 {z : ℝ} (hz : 0 < z) : |(2 * z ^ 2 - 4 * z + 6) / (1 + z) ^ 2| ≤ 6 := by
  have hnum : 0 < 2 * z ^ 2 - 4 * z + 6 := by nlinarith [sq_nonneg (z - 1)]
  have hden : (0 : ℝ) < (1 + z) ^ 2 := by positivity
  rw [abs_div, abs_of_pos hnum, abs_of_pos hden, div_le_iff₀ hden]
  nlinarith [sq_nonneg z, hz]

/-- `|4(z-1)/(1+z)| ≤ 4` for `z > 0` (the supremum `4` is attained at `z = 0`). -/
private lemma abs_coef3 {z : ℝ} (hz : 0 < z) : |4 * (z - 1) / (1 + z)| ≤ 4 := by
  have h1z : (0 : ℝ) < 1 + z := by linarith
  rw [abs_div, abs_of_pos h1z, div_le_iff₀ h1z]
  have h : |z - 1| ≤ 1 + z := by rw [abs_le]; constructor <;> linarith
  rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 4)]
  linarith

/-! ## The two derivative bounds -/

theorem omegaW_deriv_bounds {χ : ℝ → ℝ} {C₁ C₂ : ℝ}
    (hχ : ContDiff ℝ 2 χ) (hχ1 : ∀ z, |z * deriv χ z| ≤ C₁)
    (hχ2 : ∀ z, |z ^ 2 * deriv (deriv χ) z| ≤ C₂) (hχb : ∀ z, |χ z| ≤ 1)
    (hC₁ : 0 ≤ C₁) (hC₂ : 0 ≤ C₂) :
    (∀ z, 0 < z → |deriv (fun y => y * ((Work.Spaces.w y) ^ 2 * χ y)) z|
        ≤ (3 + C₁) * (Work.Spaces.w z) ^ 2) ∧
    (∀ z, 0 < z → |deriv (fun y => deriv (fun x => x ^ 2 * ((Work.Spaces.w x) ^ 2 * χ x)) y) z|
        ≤ (6 + 4 * C₁ + C₂) * (Work.Spaces.w z) ^ 2) := by
  have hχd : Differentiable ℝ χ := hχ.differentiable (by norm_num)
  have hχ'd : Differentiable ℝ (deriv χ) := hχ.differentiable_deriv_two
  have hχat : ∀ y : ℝ, HasDerivAt χ (deriv χ y) y := fun y => (hχd y).hasDerivAt
  have hχ'at : ∀ y : ℝ, HasDerivAt (deriv χ) (deriv (deriv χ) y) y := fun y =>
    (hχ'd y).hasDerivAt
  constructor
  · -- first derivative of `y ↦ y w(y)² χ(y)`
    intro z hz
    have hz0 : z ≠ 0 := ne_of_gt hz
    -- the `y ↦ y w(y)²` part
    have h1 : HasDerivAt (fun y : ℝ => y * (Work.Spaces.w y) ^ 2)
        ((z - 3) * (1 + z) ^ 3 / z ^ 4) z := by
      have hev : (fun y : ℝ => y * (Work.Spaces.w y) ^ 2) =ᶠ[𝓝 z]
          (fun y : ℝ => (1 + y) ^ 4 / y ^ 3) := by
        filter_upwards [isOpen_ne.mem_nhds hz0] with y hy
        exact mul_w_sq_eq hy
      exact (hev.hasDerivAt_iff).mpr (weight_derivs_explicit.2.2.1 z hz0)
    have hderiv : HasDerivAt (fun y : ℝ => y * (Work.Spaces.w y) ^ 2 * χ y)
        ((z - 3) * (1 + z) ^ 3 / z ^ 4 * χ z + z * (Work.Spaces.w z) ^ 2 * deriv χ z) z :=
      h1.mul (hχat z)
    -- move to the parenthesisation of the statement
    have hev0 : (fun y : ℝ => y * ((Work.Spaces.w y) ^ 2 * χ y)) =ᶠ[𝓝 z]
        (fun y : ℝ => y * (Work.Spaces.w y) ^ 2 * χ y) := by
      filter_upwards with y
      ring
    rw [hev0.deriv_eq, hderiv.deriv]
    have hw : (0 : ℝ) ≤ (Work.Spaces.w z) ^ 2 := sq_nonneg _
    -- factor out `w(z)²`
    have hfac : (z - 3) * (1 + z) ^ 3 / z ^ 4 * χ z + z * (Work.Spaces.w z) ^ 2 * deriv χ z
        = (Work.Spaces.w z) ^ 2 * (z * deriv χ z + (z - 3) / (1 + z) * χ z) := by
      have h1z : (1 + z) ≠ 0 := by linarith
      rw [mul_w_sq_eq hz0, w_sq_eq hz0]
      field_simp
      ring
    rw [hfac, abs_mul, abs_of_nonneg hw]
    calc (Work.Spaces.w z) ^ 2 * |z * deriv χ z + (z - 3) / (1 + z) * χ z|
        ≤ (Work.Spaces.w z) ^ 2 * (C₁ + 3) := by
          apply mul_le_mul_of_nonneg_left _ hw
          have h2 : |(z - 3) / (1 + z) * χ z| ≤ 3 := by
            rw [abs_mul]
            calc |(z - 3) / (1 + z)| * |χ z| ≤ |(z - 3) / (1 + z)| * 1 :=
                  mul_le_mul_of_nonneg_left (hχb z) (abs_nonneg _)
              _ = |(z - 3) / (1 + z)| := mul_one _
              _ ≤ 3 := abs_coef1 hz
          calc |z * deriv χ z + (z - 3) / (1 + z) * χ z|
              ≤ |z * deriv χ z| + |(z - 3) / (1 + z) * χ z| := abs_add_le _ _
            _ ≤ C₁ + 3 := add_le_add (hχ1 z) h2
      _ = (3 + C₁) * (Work.Spaces.w z) ^ 2 := by ring
  · -- second derivative of `y ↦ y² w(y)² χ(y)`
    intro z hz
    have hz0 : z ≠ 0 := ne_of_gt hz
    -- step A: the first derivative, on the punctured line
    have hA : ∀ y : ℝ, y ≠ 0 →
        deriv (fun x : ℝ => x ^ 2 * ((Work.Spaces.w x) ^ 2 * χ x)) y
          = 2 * (y - 1) * (1 + y) ^ 3 / y ^ 3 * χ y + (1 + y) ^ 4 / y ^ 2 * deriv χ y := by
      intro y hy
      have hev : (fun x : ℝ => x ^ 2 * ((Work.Spaces.w x) ^ 2 * χ x)) =ᶠ[𝓝 y]
          (fun x : ℝ => (1 + x) ^ 4 / x ^ 2 * χ x) := by
        filter_upwards [isOpen_ne.mem_nhds hy] with x hx
        rw [← mul_assoc, sq_mul_w_sq_eq hx]
      rw [hev.deriv_eq]
      have h1 : HasDerivAt (fun x : ℝ => (1 + x) ^ 4 / x ^ 2)
          (2 * (y - 1) * (1 + y) ^ 3 / y ^ 3) y := weight_derivs_explicit.1 y hy
      have hprod : HasDerivAt (fun x : ℝ => (1 + x) ^ 4 / x ^ 2 * χ x)
          (2 * (y - 1) * (1 + y) ^ 3 / y ^ 3 * χ y + (1 + y) ^ 4 / y ^ 2 * deriv χ y) y :=
        h1.mul (hχat y)
      exact hprod.deriv
    -- step B: transfer the outer derivative to the explicit expression
    have hev2 : (fun y : ℝ => deriv (fun x : ℝ => x ^ 2 * ((Work.Spaces.w x) ^ 2 * χ x)) y)
        =ᶠ[𝓝 z] (fun y : ℝ =>
          2 * (y - 1) * (1 + y) ^ 3 / y ^ 3 * χ y + (1 + y) ^ 4 / y ^ 2 * deriv χ y) := by
      filter_upwards [isOpen_ne.mem_nhds hz0] with y hy
      exact hA y hy
    rw [hev2.deriv_eq]
    -- step C: differentiate the two products
    have h1 : HasDerivAt (fun y : ℝ => 2 * (y - 1) * (1 + y) ^ 3 / y ^ 3 * χ y)
        ((1 + z) ^ 2 * (2 * z ^ 2 - 4 * z + 6) / z ^ 4 * χ z
          + 2 * (z - 1) * (1 + z) ^ 3 / z ^ 3 * deriv χ z) z :=
      (weight_derivs_explicit.2.1 z hz0).mul (hχat z)
    have h2 : HasDerivAt (fun y : ℝ => (1 + y) ^ 4 / y ^ 2 * deriv χ y)
        (2 * (z - 1) * (1 + z) ^ 3 / z ^ 3 * deriv χ z
          + (1 + z) ^ 4 / z ^ 2 * deriv (deriv χ) z) z :=
      (weight_derivs_explicit.1 z hz0).mul (hχ'at z)
    have hsum : deriv (fun y : ℝ =>
          2 * (y - 1) * (1 + y) ^ 3 / y ^ 3 * χ y + (1 + y) ^ 4 / y ^ 2 * deriv χ y) z
        = (1 + z) ^ 2 * (2 * z ^ 2 - 4 * z + 6) / z ^ 4 * χ z
          + 4 * (z - 1) * (1 + z) ^ 3 / z ^ 3 * deriv χ z
          + (1 + z) ^ 4 / z ^ 2 * deriv (deriv χ) z := by
      have hprod : HasDerivAt (fun y : ℝ =>
            2 * (y - 1) * (1 + y) ^ 3 / y ^ 3 * χ y + (1 + y) ^ 4 / y ^ 2 * deriv χ y)
          ((1 + z) ^ 2 * (2 * z ^ 2 - 4 * z + 6) / z ^ 4 * χ z
            + 2 * (z - 1) * (1 + z) ^ 3 / z ^ 3 * deriv χ z
            + (2 * (z - 1) * (1 + z) ^ 3 / z ^ 3 * deriv χ z
              + (1 + z) ^ 4 / z ^ 2 * deriv (deriv χ) z)) z :=
        h1.add h2
      rw [hprod.deriv]
      ring
    rw [hsum]
    have hw : (0 : ℝ) ≤ (Work.Spaces.w z) ^ 2 := sq_nonneg _
    -- factor out `w(z)²`
    have hfac : (1 + z) ^ 2 * (2 * z ^ 2 - 4 * z + 6) / z ^ 4 * χ z
          + 4 * (z - 1) * (1 + z) ^ 3 / z ^ 3 * deriv χ z
          + (1 + z) ^ 4 / z ^ 2 * deriv (deriv χ) z
        = (Work.Spaces.w z) ^ 2 * ((2 * z ^ 2 - 4 * z + 6) / (1 + z) ^ 2 * χ z
            + 4 * (z - 1) / (1 + z) * (z * deriv χ z)
            + z ^ 2 * deriv (deriv χ) z) := by
      have h1z : (1 + z) ≠ 0 := by linarith
      rw [w_sq_eq hz0]
      field_simp
    rw [hfac, abs_mul, abs_of_nonneg hw]
    calc (Work.Spaces.w z) ^ 2 * |(2 * z ^ 2 - 4 * z + 6) / (1 + z) ^ 2 * χ z
            + 4 * (z - 1) / (1 + z) * (z * deriv χ z) + z ^ 2 * deriv (deriv χ) z|
        ≤ (Work.Spaces.w z) ^ 2 * (6 + 4 * C₁ + C₂) := by
          apply mul_le_mul_of_nonneg_left _ hw
          have hA2 : |(2 * z ^ 2 - 4 * z + 6) / (1 + z) ^ 2 * χ z| ≤ 6 := by
            rw [abs_mul]
            calc |(2 * z ^ 2 - 4 * z + 6) / (1 + z) ^ 2| * |χ z|
                ≤ |(2 * z ^ 2 - 4 * z + 6) / (1 + z) ^ 2| * 1 :=
                  mul_le_mul_of_nonneg_left (hχb z) (abs_nonneg _)
              _ = |(2 * z ^ 2 - 4 * z + 6) / (1 + z) ^ 2| := mul_one _
              _ ≤ 6 := abs_coef2 hz
          have hB2 : |4 * (z - 1) / (1 + z) * (z * deriv χ z)| ≤ 4 * C₁ := by
            rw [abs_mul]
            calc |4 * (z - 1) / (1 + z)| * |z * deriv χ z|
                ≤ |4 * (z - 1) / (1 + z)| * C₁ :=
                  mul_le_mul_of_nonneg_left (hχ1 z) (abs_nonneg _)
              _ ≤ 4 * C₁ := mul_le_mul_of_nonneg_right (abs_coef3 hz) hC₁
          have h5 := hχ2 z
          calc |(2 * z ^ 2 - 4 * z + 6) / (1 + z) ^ 2 * χ z
                + 4 * (z - 1) / (1 + z) * (z * deriv χ z) + z ^ 2 * deriv (deriv χ) z|
              ≤ |(2 * z ^ 2 - 4 * z + 6) / (1 + z) ^ 2 * χ z
                  + 4 * (z - 1) / (1 + z) * (z * deriv χ z)|
                + |z ^ 2 * deriv (deriv χ) z| := abs_add_le _ _
            _ ≤ (|(2 * z ^ 2 - 4 * z + 6) / (1 + z) ^ 2 * χ z|
                  + |4 * (z - 1) / (1 + z) * (z * deriv χ z)|)
                + |z ^ 2 * deriv (deriv χ) z| := by
                exact add_le_add (abs_add_le _ _) le_rfl
            _ ≤ 6 + 4 * C₁ + C₂ := by linarith
      _ = (6 + 4 * C₁ + C₂) * (Work.Spaces.w z) ^ 2 := by ring

end Work.FTS.EllipticEst.Honest
end
end
-- ===== merged: Submission.Work.FTS.EllipticEst.LevelOneAsm.EigParsevalDefs =====
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

set_option autoImplicit false

local notation "Iθ" => Work.Spaces.Iθ

/-! ## Elementary facts about `Iθ = [0, π/2]` -/

lemma cos_nonneg_of_mem_Iθ {θ : ℝ} (hθ : θ ∈ Iθ) : 0 ≤ Real.cos θ :=
  Real.cos_nonneg_of_mem_Icc ⟨by linarith [hθ.1, Real.pi_pos], by linarith [hθ.2]⟩

/-! ## The measure `cos θ dθ` on `Iθ` -/

/-- The measure `cos θ dθ` restricted to `Iθ`: the weight for which the angular eigenfunctions
`Θ_n` are orthogonal. -/
def angMeasure : Measure ℝ :=
  (volume.restrict Iθ).withDensity (fun θ => ENNReal.ofReal (Real.cos θ))

/-- **The integral against `angMeasure` is the weighted integral on `Iθ`.**  The identity holds
for *every* `F : ℝ → ℝ` (no integrability hypothesis), thanks to
`integral_withDensity_eq_integral_toReal_smul`. -/
theorem integral_angMeasure (F : ℝ → ℝ) :
    ∫ θ, F θ ∂angMeasure = ∫ θ in Iθ, Real.cos θ * F θ := by
  rw [angMeasure, integral_withDensity_eq_integral_toReal_smul
    (Real.measurable_cos.ennreal_ofReal) (Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))]
  simp only [smul_eq_mul]
  refine integral_congr_ae ?_
  filter_upwards [ae_restrict_mem (s := Iθ) measurableSet_Icc] with θ hθ
  rw [ENNReal.toReal_ofReal (cos_nonneg_of_mem_Iθ hθ)]

theorem angMeasure_absolutelyContinuous : angMeasure ≪ volume.restrict Iθ :=
  MeasureTheory.withDensity_absolutelyContinuous _ _

theorem angMeasure_Iθ_compl : angMeasure Iθᶜ = 0 := by
  refine angMeasure_absolutelyContinuous ?_
  rw [Work.Spaces.Iθ,
    Measure.restrict_apply (s := Set.Icc (0 : ℝ) (Real.pi / 2))
      (t := (Set.Icc (0 : ℝ) (Real.pi / 2))ᶜ) measurableSet_Icc.compl]
  simp

theorem ae_mem_Iθ_angMeasure : ∀ᵐ θ ∂angMeasure, θ ∈ Iθ := by
  rw [MeasureTheory.ae_iff]
  have h : {a : ℝ | ¬ a ∈ Iθ} = Iθᶜ := rfl
  rw [h]
  exact angMeasure_Iθ_compl

instance instIsFiniteMeasureAngMeasure : IsFiniteMeasure angMeasure := by
  rw [angMeasure]
  refine MeasureTheory.isFiniteMeasure_withDensity ?_
  have hle : ∫⁻ (a : ℝ), ENNReal.ofReal (Real.cos a) ∂(volume.restrict Iθ)
      ≤ ∫⁻ (_ : ℝ), (1 : ENNReal) ∂(volume.restrict Iθ) := by
    refine MeasureTheory.lintegral_mono (fun a => ?_)
    rw [ENNReal.ofReal_le_one]
    exact Real.cos_le_one a
  have htop : ∫⁻ (_ : ℝ), (1 : ENNReal) ∂(volume.restrict Iθ) ≠ ⊤ := by
    rw [lintegral_one, Measure.restrict_apply (s := Iθ) (t := Set.univ) MeasurableSet.univ,
      Set.univ_inter, Work.Spaces.Iθ, Real.volume_Icc]
    exact ENNReal.ofReal_ne_top
  exact ne_top_of_le_ne_top htop hle

/-- The only zero of `cos` in `Iθ` is `π/2`, so `{θ ∈ Iθ | cos θ = 0}` is null. -/
theorem volume_cos_eq_zero_inter_Iθ :
    volume ({θ : ℝ | Real.cos θ = 0} ∩ Iθ) = 0 := by
  refine measure_mono_null ?_ (measure_singleton (Real.pi / 2))
  rintro x ⟨hc, hxI⟩
  rcases lt_or_eq_of_le hxI.2 with h | h
  · exact absurd hc (ne_of_gt (Real.cos_pos_of_mem_Ioo
      ⟨by linarith [hxI.1, Real.pi_pos], h⟩))
  · exact h


/-- **The unweighted measure and `angMeasure` have the same null sets** (the direction that is
not automatic): a set of `angMeasure`-measure zero is Lebesgue-null on `Iθ`. -/
theorem restrict_absolutelyContinuous_angMeasure : volume.restrict Iθ ≪ angMeasure := by
  refine Measure.AbsolutelyContinuous.mk (fun s hs h0 => ?_)
  have h1 : ∫⁻ θ in s, ENNReal.ofReal (Real.cos θ) ∂(volume.restrict Iθ) = 0 := by
    rw [← MeasureTheory.withDensity_apply (μ := volume.restrict Iθ)
      (f := fun θ => ENNReal.ofReal (Real.cos θ)) hs]
    exact h0
  have h2 : ∀ᵐ θ ∂(volume.restrict Iθ).restrict s, Real.cos θ = 0 := by
    have h2a : ∀ᵐ θ ∂(volume.restrict Iθ).restrict s, ENNReal.ofReal (Real.cos θ) = 0 :=
      (MeasureTheory.lintegral_eq_zero_iff' (μ := (volume.restrict Iθ).restrict s)
        (Real.measurable_cos.ennreal_ofReal.aemeasurable)).mp h1
    filter_upwards [h2a, Filter.Eventually.filter_mono
      (MeasureTheory.ae_mono (Measure.restrict_le_self))
      (ae_restrict_mem (s := Iθ) measurableSet_Icc)] with θ hθ hIθ
    rw [ENNReal.ofReal_eq_zero] at hθ
    exact le_antisymm hθ (cos_nonneg_of_mem_Iθ hIθ)
  have h3 : ∀ᵐ θ ∂(volume.restrict Iθ), θ ∈ s → Real.cos θ = 0 := by
    rw [← MeasureTheory.ae_restrict_iff' (s := s) hs]
    exact h2
  have h4 : (volume.restrict Iθ) s ≤ (volume.restrict Iθ) {θ : ℝ | Real.cos θ = 0} := by
    rw [MeasureTheory.ae_iff] at h3
    have hsub : s ⊆ {θ : ℝ | Real.cos θ = 0} ∪ {θ : ℝ | ¬ (θ ∈ s → Real.cos θ = 0)} := by
      intro x hx
      by_cases hx' : Real.cos x = 0
      · exact Or.inl hx'
      · exact Or.inr (by simp [hx, hx'])
    calc (volume.restrict Iθ) s
        ≤ (volume.restrict Iθ)
            ({θ : ℝ | Real.cos θ = 0} ∪ {θ : ℝ | ¬ (θ ∈ s → Real.cos θ = 0)}) :=
          measure_mono hsub
      _ ≤ (volume.restrict Iθ) {θ : ℝ | Real.cos θ = 0}
            + (volume.restrict Iθ) {θ : ℝ | ¬ (θ ∈ s → Real.cos θ = 0)} :=
          measure_union_le _ _
      _ = (volume.restrict Iθ) {θ : ℝ | Real.cos θ = 0} := by rw [h3, add_zero]
  have hZ : (volume.restrict Iθ) {θ : ℝ | Real.cos θ = 0} = 0 := by
    rw [Measure.restrict_apply (s := Iθ) (t := {θ : ℝ | Real.cos θ = 0})
      (measurableSet_eq_fun Real.measurable_cos measurable_const)]
    exact volume_cos_eq_zero_inter_Iθ
  exact le_antisymm (hZ ▸ h4) zero_le

/-! ## The eigenfunctions as elements of `L²(angMeasure)` -/





/-- **The `L²(angMeasure)` inner product of two classes with explicit representatives is the
weighted integral on `Iθ`.** -/
theorem inner_toLp_toLp {f g : ℝ → ℝ} (hf : MemLp f 2 angMeasure) (hg : MemLp g 2 angMeasure) :
    inner ℝ (MeasureTheory.MemLp.toLp f hf) (MeasureTheory.MemLp.toLp g hg)
      = ∫ θ in Iθ, f θ * g θ * Real.cos θ := by
  rw [MeasureTheory.L2.inner_def]
  have h1 : (fun a => inner ℝ ((MeasureTheory.MemLp.toLp f hf : ℝ → ℝ) a)
        ((MeasureTheory.MemLp.toLp g hg : ℝ → ℝ) a))
      =ᵐ[angMeasure] fun a => f a * g a := by
    filter_upwards [MeasureTheory.MemLp.coeFn_toLp hf,
      MeasureTheory.MemLp.coeFn_toLp hg] with a ha hb
    rw [ha, hb, Real.inner_apply]
  rw [integral_congr_ae h1, integral_angMeasure]
  refine MeasureTheory.setIntegral_congr_fun measurableSet_Icc (fun θ _ => by ring)






/-! ## Inner products of a class with the normalised eigenfunctions -/




/-! ## `L²(angMeasure)` membership from the hypotheses of the Parseval statement -/

theorem memLp_of_hyps {f : ℝ → ℝ}
    (hm : AEMeasurable f (volume.restrict Iθ))
    (hf : IntegrableOn (fun θ => f θ ^ 2 * Real.cos θ) Iθ) : MemLp f 2 angMeasure := by
  have haesm : AEStronglyMeasurable f angMeasure :=
    hm.aestronglyMeasurable.mono_ac angMeasure_absolutelyContinuous
  rw [MeasureTheory.memLp_two_iff_integrable_sq haesm]
  rw [angMeasure,
    MeasureTheory.integrable_withDensity_iff_integrable_smul'
      (Real.measurable_cos.ennreal_ofReal) (Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))]
  refine hf.congr ?_
  filter_upwards [ae_restrict_mem (s := Iθ) measurableSet_Icc] with θ hθ
  simp only [smul_eq_mul]
  rw [ENNReal.toReal_ofReal (cos_nonneg_of_mem_Iθ hθ)]
  ring

end Work.FTS.EllipticEst.LevelOneAsm
end
end
-- ===== merged: Submission.Work.FTS.EllipticEst.LevelOneFts.CF.bslOp_smul =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.LevelOneFts.CF

set_option autoImplicit false

/-!
# Homogeneity of the elliptic operator `bslOp` under multiplication by a constant

`bslOp α Ψ = -α²z²∂_zzΨ - α(5+α)z∂_zΨ + L₀Ψ` with
`L₀Ψ = -∂_θθΨ + ∂_θ(tan θ · Ψ) - 6Ψ` is a linear differential operator, so
`bslOp α (c • Ψ) = c • bslOp α Ψ` pointwise.  No differentiability hypothesis is needed here
(unlike additivity): Mathlib's `deriv` is totalised, but it still commutes with multiplication
by a constant *unconditionally* (`deriv_const_mul_field`), because at a non-differentiable point
both sides vanish.

The homogeneity of the individual first-order operators `pz`, `pth` and of their iterates is
already available as `Work.FTS.EllipticEst.{pz,pth,pzIter,pthIter}_smul`; here we only need to
transport those to the pointwise form and handle the composite operator `Lzero` (whose
`tan θ · ·` slot forces one function-level reassociation), and then `bslOp` is immediate.
-/

/-! ## Pointwise form of the homogeneity of the derivatives -/

theorem pz_smul_apply (c : ℝ) (f : ℝ → ℝ → ℝ) (z θ : ℝ) :
    Work.Spaces.pz (c • f) z θ = c * Work.Spaces.pz f z θ := by
  have h := congrFun (congrFun (Work.FTS.EllipticEst.pz_smul c f) z) θ
  simpa only [Pi.smul_apply, smul_eq_mul] using h


theorem pzIter_smul_apply (c : ℝ) (f : ℝ → ℝ → ℝ) (n : ℕ) (z θ : ℝ) :
    Work.Spaces.pzIter n (c • f) z θ = c * Work.Spaces.pzIter n f z θ := by
  have h := congrFun (congrFun (Work.FTS.EllipticEst.pzIter_smul c f n) z) θ
  simpa only [Pi.smul_apply, smul_eq_mul] using h

theorem pthIter_smul_apply (c : ℝ) (f : ℝ → ℝ → ℝ) (n : ℕ) (z θ : ℝ) :
    Work.Spaces.pthIter n (c • f) z θ = c * Work.Spaces.pthIter n f z θ := by
  have h := congrFun (congrFun (Work.FTS.EllipticEst.pthIter_smul c f n) z) θ
  simpa only [Pi.smul_apply, smul_eq_mul] using h

/-! ## Homogeneity of `L₀` -/

/-- The `tan θ · ·` slot of `L₀` commutes with constants, after the (pointwise) reassociation
`tan θ · (c · f) = c · (tan θ · f)`. -/
theorem pth_tan_mul_smul_apply (c : ℝ) (f : ℝ → ℝ → ℝ) (z θ : ℝ) :
    Work.Spaces.pth (fun z' θ' => Real.tan θ' * (c • f) z' θ') z θ
      = c * Work.Spaces.pth (fun z' θ' => Real.tan θ' * f z' θ') z θ := by
  have hfun : (fun z' θ' : ℝ => Real.tan θ' * (c • f) z' θ')
      = c • (fun z' θ' : ℝ => Real.tan θ' * f z' θ') := by
    funext z' θ'
    simp only [Pi.smul_apply, smul_eq_mul]
    ring
  rw [hfun, Work.FTS.EllipticEst.pth_smul]
  simp only [Pi.smul_apply, smul_eq_mul]

theorem Lzero_smul_apply (c : ℝ) (f : ℝ → ℝ → ℝ) (z θ : ℝ) :
    Work.Elliptic.Lzero (c • f) z θ = c * Work.Elliptic.Lzero f z θ := by
  have h2 := pthIter_smul_apply c f 2 z θ
  have ht := pth_tan_mul_smul_apply c f z θ
  rw [Work.Elliptic.Lzero, Work.Elliptic.Lzero]
  rw [h2, ht]
  simp only [Pi.smul_apply, smul_eq_mul]
  ring

/-! ## Homogeneity of `bslOp` -/

theorem bslOp_smul (α c : ℝ) (f : ℝ → ℝ → ℝ) (z θ : ℝ) :
    Work.Elliptic.bslOp α (c • f) z θ = c * Work.Elliptic.bslOp α f z θ := by
  have h2 := pzIter_smul_apply c f 2 z θ
  have h1 := pz_smul_apply c f z θ
  have hL := Lzero_smul_apply c f z θ
  simp only [Work.Elliptic.bslOp_apply, h2, h1, hL]
  ring

end Work.FTS.EllipticEst.LevelOneFts.CF
end
-- ===== merged: Submission.Work.FTS.EllipticEst.LzeroSingAuxDeriv2 =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst



end Work.FTS.EllipticEst
end
end
-- ===== merged: Submission.Work.FTS.EllipticEst.Mine.AgmonThetaSup =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The Agmon-style sup-interpolation estimate on the angular slice

For `v : ℝ → ℝ` of class `C²` on the angular interval `[0, π/2]` with `v 0 = v (π/2) = 0`,
weighted interpolation of `(v')²` between the two weighted `L²` quantities
`∫ (v')² sin(2θ)^{2-γ}` and `∫ (v'')² sin(2θ)^{-99/100}` holds with constant
`(π/2)·∫ sin(2θ)^{2-γ}`.

The route is the classical "Agmon" one:

* `v` vanishes at both endpoints, so by Rolle's theorem `v'` has a zero `ξ ∈ (0, π/2)`;
* hence `v'(θ) = ∫_ξ^θ v''` (fundamental theorem of calculus), and therefore, for *every*
  `θ ∈ [0, π/2]`, `(v'(θ))² ≤ (∫_{[0,π/2]} |v''|)²`;
* Cauchy–Schwarz with the reciprocal weights `u = sin(2θ)^{-99/100}` and `v = sin(2θ)^{99/100}`
  bounds the right-hand side by `(∫ (v'')² u)·(∫ v) ≤ (∫ (v'')² u)·(π/2)`;
* integrating the pointwise bound against `sin(2θ)^{2-γ} ≤ 1` (whose integral is `≤ π/2`)
  gives the claim.

The only non-elementary ingredient is that `v''`, namely `deriv (deriv v)`, is a.e. measurable:
this is Mathlib's `measurable_deriv`, and it is used to deduce integrability of `v''` from the
weighted `L²` hypothesis `hint2` by an AM–GM (i.e. `2|g| ≤ g²u + 1/u`) argument.
-/

noncomputable section

open MeasureTheory Filter

namespace Work.FTS.EllipticEst.Mine





end Work.FTS.EllipticEst.Mine
end
end
-- ===== merged: Submission.Work.FTS.EllipticEst.Mine.SlotDefs =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.Mine

set_option autoImplicit false

/-- **The angular source.**  The function `G` for which the equation `bslOp α Ψ = F` reads
`Lzero1 (Ψ z ·) = G z ·`, namely `G = F + α²z²∂_z²Ψ + α(5+α)z∂_zΨ` (the radial part of `bslOp`
moved to the right hand side). -/
def Gsrc (α : ℝ) (F Ψ : ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ :=
  fun z θ => F z θ + α ^ 2 * (z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ)
    + α * (5 + α) * (z * Work.Spaces.pz Ψ z θ)

/-- The angular weight `sin(2θ)^{4-γ}` of the paper's Step 5. -/
def sig4 (γ : ℝ) (θ : ℝ) : ℝ := Real.rpow (Real.sin (2 * θ)) (4 - γ)

/-- The angular weight `sin(2θ)^{2-γ}` of the paper's Step 4. -/
def sig2 (γ : ℝ) (θ : ℝ) : ℝ := Real.rpow (Real.sin (2 * θ)) (2 - γ)

/-- `pthIter n f z θ` is the iterated `∂_θ`-derivative of the slice `θ ↦ f z θ`. -/
theorem pthIter_eq_iteratedDeriv (n : ℕ) (f : ℝ → ℝ → ℝ) :
    Work.Spaces.pthIter n f = fun z θ => iteratedDeriv n (fun t => f z t) θ := by
  induction n with
  | zero => funext z θ; simp
  | succ k ih =>
      rw [Work.Spaces.pthIter_succ, ih]
      funext z θ
      rw [iteratedDeriv_succ]
      rfl

/-- **The equation in `Lzero1` form.**  If `bslOp α Ψ = F` on the open quadrant then the
angular profile `θ ↦ Ψ z θ` solves `Lzero1 u = (Gsrc α F Ψ) z ·` for every `z > 0`. -/
theorem Lzero1_slice_eq_Gsrc {α : ℝ} {F Ψ : ℝ → ℝ → ℝ}
    (heq : ∀ z, 0 < z → ∀ θ, 0 < θ → θ < Real.pi / 2 →
      Work.Elliptic.bslOp α Ψ z θ = F z θ)
    {z : ℝ} (hz : 0 < z) {θ : ℝ} (hθ : 0 < θ) (hθ' : θ < Real.pi / 2) :
    Work.FTS.EllipticEst.Lzero1 (fun t => Ψ z t) θ = Gsrc α F Ψ z θ := by
  have h := heq z hz θ hθ hθ'
  simp only [Work.Elliptic.bslOp_apply, Work.Elliptic.Lzero] at h
  have hpth2 : Work.Spaces.pthIter 2 Ψ z θ =
      deriv (fun t => deriv (fun t => Ψ z t) t) θ := by
    rw [show (2:ℕ) = 1 + 1 from rfl, Work.Spaces.pthIter_succ, Work.Spaces.pthIter_succ]
    rfl
  have hpth1 : Work.Spaces.pth (fun x t => Real.tan t * Ψ x t) z θ =
      deriv (fun t => Real.tan t * Ψ z t) θ := rfl
  rw [hpth2, hpth1] at h
  simp only [Work.FTS.EllipticEst.Lzero1, Gsrc] at h ⊢
  linarith [h]

end Work.FTS.EllipticEst.Mine
end
end
-- ===== merged: Submission.Work.FTS.EllipticEst.Prop.l0_bridge =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.Prop

set_option autoImplicit false

/-- **The weak class `TT.EllWeakPos` is (a datum of) the a.e. class `H2W.Ae.AeData`.**

The only difference between the two classes is the two moment conditions: `EllWeakPos` demands
`F_*F z = 0` and `F_*Ψ z = 0` for every `z > 0` (pointwise), while `AeData` demands the same
only almost everywhere in `z`.  The pointwise conditions imply the a.e. ones, and every other
field of `AeData α Ψ F` is a field of `EllWeakPos α 0 F Ψ` up to the order of the two functions
(the `α`-bounds are the hypotheses `0 < α`, `α ≤ 1/4` supplied by the caller). -/
theorem aeData_of_ellWeakPos {α : ℝ} {F Ψ : ℝ → ℝ → ℝ} (hα : 0 < α) (hα4 : α ≤ 1 / 4)
    (h : Work.FTS.EllipticEst.TT.EllWeakPos α 0 F Ψ) :
    Work.FTS.EllipticEst.H2W.Ae.AeData α Ψ F := by
  rcases h with ⟨heq, hzero, hpi, horthF, horthPsi, hsmooth, hmemF, hmemA, hmemB, _hmemC⟩
  refine ⟨hα, hα4, heq, hzero, hpi, hsmooth, hmemF, hmemA, hmemB, ?_, ?_⟩
  · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with z hz
    exact horthPsi z hz
  · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with z hz
    exact horthF z hz

end Work.FTS.EllipticEst.Prop
end
-- ===== merged: Submission.Work.FTS.EllipticEst.Prop.l2etaL0Aux =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

set_option maxHeartbeats 1000000

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.Prop.L0

set_option autoImplicit false

/-- **The `k = 0` shape of `HkSq`.**  At level `0` the mixed-derivative sum of `HkIntegrand` is
empty, so `HkSq α 0 g` is exactly the square of the `L²`-norm of
`g·w(z)/sin(2θ)^{η/2}`; this is the norm in which the `ℋ⁰`-integrals of the target are stated. -/
theorem HkSq_zero_eq (α : ℝ) (g : ℝ → ℝ → ℝ) :
    Work.Spaces.HkSq α 0 g
      = ∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
          (g z θ * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2 := by
  rw [Work.Spaces.HkSq]
  refine MeasureTheory.setIntegral_congr_fun measurableSet_Ici fun z _ => ?_
  refine MeasureTheory.setIntegral_congr_fun measurableSet_Icc fun θ _ => ?_
  simp only [Work.Spaces.HkIntegrand, Work.Spaces.pzIter_zero, Finset.range_one,
    Finset.sum_singleton]
  norm_num

/-- The same identity in `HkIntegrand` form, for rewriting integrands pointwise. -/
theorem HkIntegrand_zero_eq (α : ℝ) (g : ℝ → ℝ → ℝ) (z θ : ℝ) :
    Work.Spaces.HkIntegrand α 0 g z θ
      = (g z θ * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2 := by
  simp only [Work.Spaces.HkIntegrand, Work.Spaces.pzIter_zero, Finset.range_one,
    Finset.sum_singleton]
  norm_num

/-- **The level-`0` integrand vanishes on the boundary of the domain**: at `z = 0` (where
`w 0 = 0`) and at `θ = 0`, `θ = π/2` (where `sin(2θ) = 0`, so the weight `1/0 = 0`). -/
theorem HkIntegrand_zero_boundary (α : ℝ) (g : ℝ → ℝ → ℝ) {z θ : ℝ}
    (h : z = 0 ∨ θ = 0 ∨ θ = Real.pi / 2) : Work.Spaces.HkIntegrand α 0 g z θ = 0 := by
  rcases h with h | h | h
  · subst h
    rw [HkIntegrand_zero_eq]
    have hw : Work.Spaces.w 0 = 0 := by norm_num [Work.Spaces.w]
    rw [hw, zero_div, mul_zero, zero_pow (by norm_num : (2 : ℕ) ≠ 0)]
  · subst h
    rw [HkIntegrand_zero_eq]
    have h2 : 2 * (0 : ℝ) = 0 := by norm_num
    rw [h2, Real.sin_zero]
    have hz : (0 : ℝ) ^ (Work.Spaces.eta / 2) = 0 :=
      Real.zero_rpow (by norm_num [Work.Spaces.eta] : Work.Spaces.eta / 2 ≠ 0)
    rw [hz, div_zero, mul_zero, zero_pow (by norm_num : (2 : ℕ) ≠ 0)]
  · subst h
    rw [HkIntegrand_zero_eq]
    have h2 : 2 * (Real.pi / 2) = Real.pi := by ring
    rw [h2, Real.sin_pi]
    have hz : (0 : ℝ) ^ (Work.Spaces.eta / 2) = 0 :=
      Real.zero_rpow (by norm_num [Work.Spaces.eta] : Work.Spaces.eta / 2 ≠ 0)
    rw [hz, div_zero, mul_zero, zero_pow (by norm_num : (2 : ℕ) ≠ 0)]

/-- **Homogeneity of the level-`0` integrand** under multiplication by a constant. -/
theorem HkIntegrand_zero_const_mul (α c : ℝ) (g : ℝ → ℝ → ℝ) (z θ : ℝ) :
    Work.Spaces.HkIntegrand α 0 (fun z θ => c * g z θ) z θ
      = c ^ 2 * Work.Spaces.HkIntegrand α 0 g z θ := by
  rw [HkIntegrand_zero_eq, HkIntegrand_zero_eq]
  ring

/-- **Homogeneity of `HkSq α 0`** under multiplication by a constant. -/
theorem HkSq_zero_const_mul (α c : ℝ) (g : ℝ → ℝ → ℝ) :
    Work.Spaces.HkSq α 0 (fun z θ => c * g z θ) = c ^ 2 * Work.Spaces.HkSq α 0 g := by
  rw [HkSq_zero_eq, HkSq_zero_eq]
  rw [show (fun z => ∫ θ in Work.Spaces.Iθ, (c * g z θ
        * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2)
      = fun z => c ^ 2 * ∫ θ in Work.Spaces.Iθ,
          (g z θ * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2 from by
    funext z
    rw [← MeasureTheory.integral_const_mul]
    exact MeasureTheory.setIntegral_congr_fun measurableSet_Icc (fun θ _ => by ring)]
  rw [← MeasureTheory.integral_const_mul]

/-- **`HkMem` is closed under multiplication by a constant** at level `0`. -/
theorem HkMem_zero_const_mul (α c : ℝ) {f : ℝ → ℝ → ℝ} (h : Work.Spaces.HkMem α 0 f) :
    Work.Spaces.HkMem α 0 (fun z θ => c * f z θ) := by
  have hpt : ∀ z θ, Work.Spaces.HkIntegrand α 0 (fun z θ => c * f z θ) z θ
      = c ^ 2 * Work.Spaces.HkIntegrand α 0 f z θ := HkIntegrand_zero_const_mul α c f
  constructor
  · intro z hz
    refine MeasureTheory.IntegrableOn.congr_fun ((h.1 z hz).const_mul (c ^ 2)) ?_
      measurableSet_Icc
    exact fun θ _ => (hpt z θ).symm
  · have h2 : MeasureTheory.IntegrableOn
        (fun z => c ^ 2 * (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 0 f z θ))
        Work.Spaces.Iz := h.2.const_mul (c ^ 2)
    refine MeasureTheory.IntegrableOn.congr_fun h2 ?_ measurableSet_Ici
    intro z _
    show c ^ 2 * (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 0 f z θ)
      = ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 0 (fun z θ => c * f z θ) z θ
    rw [← MeasureTheory.integral_const_mul]
    exact (MeasureTheory.setIntegral_congr_fun measurableSet_Icc
      (fun θ _ => hpt z θ)).symm

/-- **Monotonicity of `HkSq α 0` under a pointwise domination of its integrand** by an arbitrary
majorant `M` (the majorant need not itself be an `HkIntegrand`); only the honesty of the majorant
is required. -/
theorem HkSq_zero_le_of_integrand_le (α : ℝ) {f M : ℝ → ℝ → ℝ}
    (hf : Work.Spaces.HkMem α 0 f)
    (hMθ : ∀ z ∈ Work.Spaces.Iz, MeasureTheory.IntegrableOn (fun θ => M z θ) Work.Spaces.Iθ)
    (hMz : MeasureTheory.IntegrableOn (fun z => ∫ θ in Work.Spaces.Iθ, M z θ) Work.Spaces.Iz)
    (h : ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ,
      Work.Spaces.HkIntegrand α 0 f z θ ≤ M z θ) :
    Work.Spaces.HkSq α 0 f ≤ ∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ, M z θ := by
  rw [Work.Spaces.HkSq]
  refine MeasureTheory.setIntegral_mono_on hf.2 hMz measurableSet_Ici fun z hz => ?_
  exact MeasureTheory.setIntegral_mono_on (hf.1 z hz) (hMθ z hz) measurableSet_Icc
    (fun θ hθ => h z hz θ hθ)

/-- The elementary five-term Cauchy–Schwarz bound. -/
theorem sum_five_sq_le (x1 x2 x3 x4 x5 : ℝ) :
    (x1 + x2 + x3 + x4 + x5) ^ 2 ≤ 5 * (x1 ^ 2 + x2 ^ 2 + x3 ^ 2 + x4 ^ 2 + x5 ^ 2) := by
  nlinarith [sq_nonneg (x1 - x2), sq_nonneg (x1 - x3), sq_nonneg (x1 - x4), sq_nonneg (x1 - x5),
    sq_nonneg (x2 - x3), sq_nonneg (x2 - x4), sq_nonneg (x2 - x5), sq_nonneg (x3 - x4),
    sq_nonneg (x3 - x5), sq_nonneg (x4 - x5)]


/-- Linearity of the set integral over a five-term sum of integrable functions. -/
theorem integral_five_eq {s : Set ℝ} {f1 f2 f3 f4 f5 : ℝ → ℝ}
    (h1 : MeasureTheory.IntegrableOn f1 s)
    (h2 : MeasureTheory.IntegrableOn f2 s)
    (h3 : MeasureTheory.IntegrableOn f3 s)
    (h4 : MeasureTheory.IntegrableOn f4 s)
    (h5 : MeasureTheory.IntegrableOn f5 s) :
    (∫ θ in s, f1 θ + f2 θ + f3 θ + f4 θ + f5 θ)
      = ((∫ θ in s, f1 θ) + (∫ θ in s, f2 θ)
          + (∫ θ in s, f3 θ) + (∫ θ in s, f4 θ)
          + (∫ θ in s, f5 θ)) := by
  rw [MeasureTheory.integral_add (f := fun θ => f1 θ + f2 θ + f3 θ + f4 θ) (g := f5)
    (((h1.add h2).add h3).add h4) h5]
  rw [MeasureTheory.integral_add (f := fun θ => f1 θ + f2 θ + f3 θ) (g := f4)
    ((h1.add h2).add h3) h4]
  rw [MeasureTheory.integral_add (f := fun θ => f1 θ + f2 θ) (g := f3) (h1.add h2) h3]
  rw [MeasureTheory.integral_add (f := f1) (g := f2) h1 h2]

end Work.FTS.EllipticEst.Prop.L0
end
end
-- ===== merged: Submission.Work.FTS.EllipticEst.RPFresh.RadialIBP =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.RPFresh




end Work.FTS.EllipticEst.RPFresh
end
end
-- ===== merged: Submission.Work.FTS.EllipticEst.SliceLocal.PhiGKernel =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology Interval
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.SliceLocal

set_option autoImplicit false

/-- The kernel `sin θ cos²θ` of the `PhiG` integral. -/
def Kkern (θ : ℝ) : ℝ := Real.sin θ * (Real.cos θ) ^ 2

/-- The prefactor `(2 cos³θ)⁻¹` of `PhiG`, so that `PhiG g θ = Kcoef θ * Qg g θ`. -/
def Kcoef (θ : ℝ) : ℝ := (2 * (Real.cos θ) ^ 3)⁻¹

/-- The cumulative integral `∫_θ^{π/2} sin σ cos²σ · g σ dσ` of the data. -/
def Qg (g : ℝ → ℝ) (θ : ℝ) : ℝ :=
  ∫ σ in θ..(Real.pi / 2), Kkern σ * g σ

/-- The `L²`-weight of the kernel over the angular tail `[θ, π/2]`. -/
def Wg (θ : ℝ) : ℝ :=
  ∫ σ in θ..(Real.pi / 2), (Kkern σ) ^ 2 / Work.FTS.EllipticEst.sEta σ





/-- `sEta` is nonnegative on `Iθ`. -/
theorem sEta_nonneg {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) :
    0 ≤ Work.FTS.EllipticEst.sEta θ :=
  Real.rpow_nonneg (Work.FTS.EllipticEst.TT.sin_two_nonneg hθ) _





end Work.FTS.EllipticEst.SliceLocal
end
end
-- ===== merged: Submission.Work.FTS.EllipticEst.TT.iter_le_of_lower_u =====
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

/-- The open neighbourhood `(-1, π/2 + 1)` of the closed interval `Iθ = [0, π/2]`; it is
exactly the domain of `Work.Elliptic.SmoothSlice`. -/
private def SU : Set ℝ := Set.Ioo (-1) (Real.pi / 2 + 1)



private theorem isOpen_SU : IsOpen SU := isOpen_Ioo

/-! ## Smoothness of the auxiliary functions -/

private theorem contDiffOn_deriv {u : ℝ → ℝ} (hu : Work.Elliptic.SmoothSlice u) :
    ContDiffOn ℝ ⊤ (deriv u) SU :=
  hu.deriv_of_isOpen isOpen_Ioo le_top

/-- `u''` is smooth on `SU` when `u` is. -/
private theorem smoothSlice_D2 {u : ℝ → ℝ} (hu : Work.Elliptic.SmoothSlice u) :
    Work.Elliptic.SmoothSlice (D2 u) :=
  (contDiffOn_deriv hu).deriv_of_isOpen isOpen_Ioo le_top

private theorem contDiffOn_sin_two : ContDiffOn ℝ ⊤ (fun θ : ℝ => Real.sin (2 * θ)) SU := by
  have h : ContDiff ℝ ⊤ (fun θ : ℝ => Real.sin (2 * θ)) :=
    Real.contDiff_sin.comp (contDiff_const.mul contDiff_id)
  exact h.contDiffOn

private theorem contDiffOn_two_cos : ContDiffOn ℝ ⊤ (fun θ : ℝ => 2 * Real.cos (2 * θ)) SU := by
  have h : ContDiff ℝ ⊤ (fun θ : ℝ => 2 * Real.cos (2 * θ)) :=
    contDiff_const.mul (Real.contDiff_cos.comp (contDiff_const.mul contDiff_id))
  exact h.contDiffOn

/-- `D_θ u = sin(2θ) u'` is smooth on `SU` when `u` is. -/
private theorem smoothSlice_Dth1 {u : ℝ → ℝ} (hu : Work.Elliptic.SmoothSlice u) :
    Work.Elliptic.SmoothSlice (Work.Elliptic.Dth1 u) := by
  have h := contDiffOn_sin_two.mul (contDiffOn_deriv hu)
  exact h

private theorem smoothSlice_mul {F G : ℝ → ℝ} (hF : Work.Elliptic.SmoothSlice F)
    (hG : Work.Elliptic.SmoothSlice G) :
    Work.Elliptic.SmoothSlice (fun θ => F θ * G θ) := hF.mul hG


private theorem smoothSlice_sin_sq :
    Work.Elliptic.SmoothSlice (fun θ : ℝ => Real.sin (2 * θ) ^ 2) := by
  have h : ContDiff ℝ ⊤ (fun θ : ℝ => Real.sin (2 * θ) ^ 2) := by fun_prop
  exact h.contDiffOn

private theorem smoothSlice_two_cos :
    Work.Elliptic.SmoothSlice (fun θ : ℝ => 2 * Real.cos (2 * θ)) :=
  contDiffOn_two_cos

private theorem contDiffAt_deriv_of_mem {u : ℝ → ℝ} (hu : Work.Elliptic.SmoothSlice u)
    {θ : ℝ} (hθ : θ ∈ SU) : DifferentiableAt ℝ (deriv u) θ :=
  ((contDiffOn_deriv hu).contDiffAt (isOpen_SU.mem_nhds hθ)).differentiableAt (by simp)

/-! ## The second order identity `D_θ² u = sin(2θ)² u'' + 2 cos(2θ) D_θ u` -/

private theorem Dth1Iter_two_eq (u : ℝ → ℝ) (hu : Work.Elliptic.SmoothSlice u) {θ : ℝ}
    (hθ : θ ∈ SU) :
    Work.Elliptic.Dth1Iter 2 u θ
      = (Real.sin (2 * θ)) ^ 2 * D2 u θ + 2 * Real.cos (2 * θ) * Work.Elliptic.Dth1 u θ := by
  have hdu : DifferentiableAt ℝ (deriv u) θ := contDiffAt_deriv_of_mem hu hθ
  have hderiv : deriv (Work.Elliptic.Dth1 u) θ
      = 2 * Real.cos (2 * θ) * deriv u θ + Real.sin (2 * θ) * D2 u θ := by
    have h1 : HasDerivAt (fun τ : ℝ => 2 * τ) 2 θ := by
      simpa using (hasDerivAt_id θ).const_mul (2 : ℝ)
    have h2 : HasDerivAt (fun τ : ℝ => Real.sin (2 * τ)) (Real.cos (2 * θ) * 2) θ :=
      (Real.hasDerivAt_sin (2 * θ)).comp θ h1
    have h3 := h2.mul hdu.hasDerivAt
    have h4 : deriv (fun τ : ℝ => Real.sin (2 * τ) * deriv u τ) θ
        = (Real.cos (2 * θ) * 2) * deriv u θ + Real.sin (2 * θ) * deriv (deriv u) θ :=
      h3.deriv
    rw [show deriv (Work.Elliptic.Dth1 u) θ
        = deriv (fun τ : ℝ => Real.sin (2 * τ) * deriv u τ) θ from rfl, h4]
    simp only [D2]
    ring
  simp only [Work.Elliptic.Dth1Iter_succ, Work.Elliptic.Dth1Iter_zero, Work.Elliptic.Dth1]
  rw [hderiv]
  ring

/-! ## Composition of the iterates -/

private theorem Dth1Iter_add_index (m n : ℕ) (f : ℝ → ℝ) :
    Work.Elliptic.Dth1Iter (m + n) f = Work.Elliptic.Dth1Iter m (Work.Elliptic.Dth1Iter n f) := by
  induction m with
  | zero => simp
  | succ m ih =>
    simp only [Nat.succ_add, Work.Elliptic.Dth1Iter_succ, ih]

/-! ## The weights `sEta` and `sGam` -/



/-! ## Reindexing a sum over `Icc 1 n` as a sum over `range n` -/

private theorem sum_Icc_one_eq_sum_range (n : ℕ) (f : ℕ → ℝ) :
    ∑ k ∈ Finset.Icc 1 n, f k = ∑ k ∈ Finset.range n, f (k + 1) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ n + 1), ih, Finset.sum_range_succ]

/-! ## The constant -/

/-- The constant of the pointwise (and hence integral) estimate, as a function of the
coefficient families `cA` (for `D_θ^j (sin(2θ)²)`) and `cB` (for `D_θ^j (2 cos 2θ)`). -/
private noncomputable def Kc (i : ℕ) (cA cB : ℕ → ℝ) : ℝ :=
  2 * (((i - 2 : ℕ) : ℝ) + 1) *
    ((∑ j ∈ Finset.range (i - 2 + 1), (4 : ℝ) ^ (i - 2) * cA j)
      + (∑ j ∈ Finset.range (i - 2 + 1), (4 : ℝ) ^ (i - 2) * cB j) + 1)


private theorem Kc_eq (i : ℕ) {cA cB : ℕ → ℝ} {CA CB : ℝ}
    (hCA : CA = ∑ j ∈ Finset.range (i - 2 + 1), (4 : ℝ) ^ (i - 2) * cA j)
    (hCB : CB = ∑ j ∈ Finset.range (i - 2 + 1), (4 : ℝ) ^ (i - 2) * cB j) :
    Kc i cA cB = 2 * (((i - 2 : ℕ) : ℝ) + 1) * (CA + CB + 1) := by
  rw [Kc, ← hCA, ← hCB]

/-! ## The pointwise bound

For `θ` in the open interval `(0, π/2)` the iterate `D_θ^i u` splits as
`D_θ^{i-2}(sin(2θ)² u'') + D_θ^{i-2}(2 cos(2θ) D_θ u)`; Leibniz plus Cauchy–Schwarz bounds the
square of each piece by a finite sum, and the coefficient bounds for the iterates of
`sin(2θ)²` and of `2 cos(2θ)` (together with the weight comparisons
`sin(2θ)⁴ sin(2θ)^{-γ} ≤ sin(2θ)^{-η}` and `sin(2θ)⁴ sin(2θ)^{-γ} ≤ sin(2θ)^{-γ}`) turn the
result into the bracket of the theorem. -/

private theorem pointwise_bound {cA cB : ℕ → ℝ}
    (hcA : ∀ j θ, (Work.Elliptic.Dth1Iter j (fun τ : ℝ => Real.sin (2 * τ) ^ 2) θ) ^ 2
      ≤ cA j * (Real.sin (2 * θ)) ^ 4)
    (hcB : ∀ j θ, (Work.Elliptic.Dth1Iter j (fun τ : ℝ => 2 * Real.cos (2 * τ)) θ) ^ 2 ≤ cB j)
    (hcApos : ∀ j, 0 ≤ cA j) (hcBpos : ∀ j, 0 ≤ cB j)
    (i : ℕ) (hi : 2 ≤ i) (α : ℝ) (hα : 0 < α) (hα4 : α ≤ 1 / 4) (u : ℝ → ℝ)
    (hu : Work.Elliptic.SmoothSlice u) :
    ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      (Work.Elliptic.Dth1Iter i u θ) ^ 2 * sGam α θ ≤ Kc i cA cB *
        ((D2 u θ) ^ 2 * sEta θ
          + ∑ k ∈ Finset.range (i - 2),
              (Work.Elliptic.Dth1Iter (k + 1) (D2 u) θ) ^ 2 * sGam α θ
          + ∑ k ∈ Finset.range (i - 1),
              (Work.Elliptic.Dth1Iter (k + 1) u θ) ^ 2 * sGam α θ) := by
  intro θ hθ
  have hθI : θ ∈ Work.Spaces.Iθ := ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩
  have hθU : θ ∈ SU := ⟨by linarith [hθ.1], by linarith [hθ.2, Real.pi_pos]⟩
  have hsGam_nn : 0 ≤ sGam α θ := sGam_nonneg α hθI
  have hsEta_nn : 0 ≤ sEta θ := sEta_nonneg hθI
  -- the building blocks
  set Asq : ℝ → ℝ := fun τ : ℝ => Real.sin (2 * τ) ^ 2 with hAsq
  set Bc : ℝ → ℝ := fun τ : ℝ => 2 * Real.cos (2 * τ) with hBc
  set g : ℝ → ℝ := D2 u with hg
  set hh : ℝ → ℝ := Work.Elliptic.Dth1 u with hhh
  have hAsm : Work.Elliptic.SmoothSlice Asq := by rw [hAsq]; exact smoothSlice_sin_sq
  have hBsm : Work.Elliptic.SmoothSlice Bc := by rw [hBc]; exact smoothSlice_two_cos
  have hgsm : Work.Elliptic.SmoothSlice g := by rw [hg]; exact smoothSlice_D2 hu
  have hhsm : Work.Elliptic.SmoothSlice hh := by rw [hhh]; exact smoothSlice_Dth1 hu
  -- the second order identity, propagated through `D_θ^{i-2}`
  have hi_eq : i = (i - 2) + 2 := by omega
  have hev : Work.Elliptic.Dth1Iter 2 u =ᶠ[𝓝 θ] (fun τ : ℝ => Asq τ * g τ + Bc τ * hh τ) := by
    filter_upwards [isOpen_SU.mem_nhds hθU] with τ hτ
    rw [hAsq, hBc, hg, hhh]
    exact Dth1Iter_two_eq u hu hτ
  have hX : Work.Elliptic.Dth1Iter i u θ
      = Work.Elliptic.Dth1Iter (i - 2) (fun τ : ℝ => Asq τ * g τ) θ
        + Work.Elliptic.Dth1Iter (i - 2) (fun τ : ℝ => Bc τ * hh τ) θ := by
    have h1 : Work.Elliptic.Dth1Iter i u
        = Work.Elliptic.Dth1Iter (i - 2) (Work.Elliptic.Dth1Iter 2 u) := by
      conv_lhs => rw [show i = (i - 2) + 2 by omega]
      exact Dth1Iter_add_index (i - 2) 2 u
    rw [h1, Dth1Iter_eventuallyEq (i - 2) hev,
      Dth1Iter_add_of_smooth (i - 2) (smoothSlice_mul hAsm hgsm) (smoothSlice_mul hBsm hhsm) hθU]
  set X : ℝ := Work.Elliptic.Dth1Iter (i - 2) (fun τ : ℝ => Asq τ * g τ) θ with hXdef
  set Y : ℝ := Work.Elliptic.Dth1Iter (i - 2) (fun τ : ℝ => Bc τ * hh τ) θ with hYdef
  have hsq : (Work.Elliptic.Dth1Iter i u θ) ^ 2 ≤ 2 * X ^ 2 + 2 * Y ^ 2 := by
    rw [hX]
    nlinarith [sq_nonneg (X - Y)]
  -- the Leibniz + Cauchy–Schwarz bound for the two pieces
  set SA : ℝ := ∑ j ∈ Finset.range (i - 2 + 1), ((i - 2).choose j : ℝ) ^ 2 *
      ((Work.Elliptic.Dth1Iter j Asq θ) ^ 2 * (Work.Elliptic.Dth1Iter ((i - 2) - j) g θ) ^ 2)
    with hSA
  set SB : ℝ := ∑ j ∈ Finset.range (i - 2 + 1), ((i - 2).choose j : ℝ) ^ 2 *
      ((Work.Elliptic.Dth1Iter j Bc θ) ^ 2 * (Work.Elliptic.Dth1Iter ((i - 2) - j) hh θ) ^ 2)
    with hSB
  have hX2 : X ^ 2 ≤ (((i - 2 : ℕ) : ℝ) + 1) * SA := by
    rw [hXdef, hSA]
    exact Dth1Iter_mul_sq_le (i - 2) hAsm hgsm hθU
  have hY2 : Y ^ 2 ≤ (((i - 2 : ℕ) : ℝ) + 1) * SB := by
    rw [hYdef, hSB]
    exact Dth1Iter_mul_sq_le (i - 2) hBsm hhsm hθU
  -- the coefficient collections
  set CA : ℝ := ∑ j ∈ Finset.range (i - 2 + 1), (4 : ℝ) ^ (i - 2) * cA j with hCAdef
  set CB : ℝ := ∑ j ∈ Finset.range (i - 2 + 1), (4 : ℝ) ^ (i - 2) * cB j with hCBdef
  have hCAnn : 0 ≤ CA := by
    rw [hCAdef]
    exact Finset.sum_nonneg fun j _ => mul_nonneg (pow_nonneg (by norm_num) _) (hcApos j)
  have hCBnn : 0 ≤ CB := by
    rw [hCBdef]
    exact Finset.sum_nonneg fun j _ => mul_nonneg (pow_nonneg (by norm_num) _) (hcBpos j)
  -- the two families of terms
  set brA : ℝ := (g θ) ^ 2 * sEta θ
      + ∑ k ∈ Finset.range (i - 2), (Work.Elliptic.Dth1Iter (k + 1) g θ) ^ 2 * sGam α θ
    with hbrA
  set brB : ℝ := ∑ k ∈ Finset.range (i - 2 + 1),
      (Work.Elliptic.Dth1Iter k hh θ) ^ 2 * sGam α θ with hbrB
  have hbrAnn : 0 ≤ brA := by
    rw [hbrA]
    exact add_nonneg (mul_nonneg (sq_nonneg _) hsEta_nn)
      (Finset.sum_nonneg fun k _ => mul_nonneg (sq_nonneg _) hsGam_nn)
  have hbrBnn : 0 ≤ brB := by
    rw [hbrB]
    exact Finset.sum_nonneg fun k _ => mul_nonneg (sq_nonneg _) hsGam_nn
  have hSAb : SA * sGam α θ ≤ CA * brA := by
    rw [hSA, hCAdef, hbrA]
    exact iterFamilyA_le (cA := cA) hcA hcApos (i - 2) α hα hα4 g hθ
  have hSBb : SB * sGam α θ ≤ CB * brB := by
    rw [hSB, hCBdef, hbrB]
    exact iterFamilyB_le (cB := cB) hcB hcBpos (i - 2) α hθ hh
  -- `D_θ^k (D_θ u) = D_θ^{k+1} u`
  have hbrB_eq : brB = ∑ k ∈ Finset.range (i - 1),
      (Work.Elliptic.Dth1Iter (k + 1) u θ) ^ 2 * sGam α θ := by
    rw [hbrB, show i - 2 + 1 = i - 1 by omega]
    refine Finset.sum_congr rfl fun k _ => ?_
    have hcomp : Work.Elliptic.Dth1Iter k hh = Work.Elliptic.Dth1Iter (k + 1) u := by
      rw [hhh]
      exact (Dth1Iter_add_index k 1 u).symm
    rw [hcomp]
  -- the assembly
  have hXb : X ^ 2 * sGam α θ ≤ (((i - 2 : ℕ) : ℝ) + 1) * (CA * brA) := by
    calc X ^ 2 * sGam α θ ≤ ((((i - 2 : ℕ) : ℝ) + 1) * SA) * sGam α θ :=
          mul_le_mul_of_nonneg_right hX2 hsGam_nn
      _ = (((i - 2 : ℕ) : ℝ) + 1) * (SA * sGam α θ) := by ring
      _ ≤ (((i - 2 : ℕ) : ℝ) + 1) * (CA * brA) :=
          mul_le_mul_of_nonneg_left hSAb (by positivity)
  have hYb : Y ^ 2 * sGam α θ ≤ (((i - 2 : ℕ) : ℝ) + 1) * (CB * brB) := by
    calc Y ^ 2 * sGam α θ ≤ ((((i - 2 : ℕ) : ℝ) + 1) * SB) * sGam α θ :=
          mul_le_mul_of_nonneg_right hY2 hsGam_nn
      _ = (((i - 2 : ℕ) : ℝ) + 1) * (SB * sGam α θ) := by ring
      _ ≤ (((i - 2 : ℕ) : ℝ) + 1) * (CB * brB) :=
          mul_le_mul_of_nonneg_left hSBb (by positivity)
  have hstep : (Work.Elliptic.Dth1Iter i u θ) ^ 2 * sGam α θ
      ≤ 2 * (((i - 2 : ℕ) : ℝ) + 1) * (CA * brA + CB * brB) := by
    calc (Work.Elliptic.Dth1Iter i u θ) ^ 2 * sGam α θ
        ≤ (2 * X ^ 2 + 2 * Y ^ 2) * sGam α θ := mul_le_mul_of_nonneg_right hsq hsGam_nn
      _ = 2 * (X ^ 2 * sGam α θ) + 2 * (Y ^ 2 * sGam α θ) := by ring
      _ ≤ 2 * ((((i - 2 : ℕ) : ℝ) + 1) * (CA * brA))
            + 2 * ((((i - 2 : ℕ) : ℝ) + 1) * (CB * brB)) := by linarith [hXb, hYb]
      _ = 2 * (((i - 2 : ℕ) : ℝ) + 1) * (CA * brA + CB * brB) := by ring
  have hfin : 2 * (((i - 2 : ℕ) : ℝ) + 1) * (CA * brA + CB * brB)
      ≤ 2 * (((i - 2 : ℕ) : ℝ) + 1) * (CA + CB + 1) * (brA + brB) := by
    have h1 : 0 ≤ 2 * (((i - 2 : ℕ) : ℝ) + 1) := by positivity
    have h2 : CA * brA + CB * brB ≤ (CA + CB + 1) * (brA + brB) := by
      nlinarith [hCAnn, hCBnn, hbrAnn, hbrBnn]
    nlinarith [h1, h2]
  have hK : Kc i cA cB = 2 * (((i - 2 : ℕ) : ℝ) + 1) * (CA + CB + 1) :=
    Kc_eq i hCAdef hCBdef
  rw [hK]
  calc (Work.Elliptic.Dth1Iter i u θ) ^ 2 * sGam α θ
      ≤ 2 * (((i - 2 : ℕ) : ℝ) + 1) * (CA * brA + CB * brB) := hstep
    _ ≤ 2 * (((i - 2 : ℕ) : ℝ) + 1) * (CA + CB + 1) * (brA + brB) := hfin
    _ = 2 * (((i - 2 : ℕ) : ℝ) + 1) * (CA + CB + 1) *
          ((D2 u θ) ^ 2 * sEta θ
            + ∑ k ∈ Finset.range (i - 2),
                (Work.Elliptic.Dth1Iter (k + 1) (D2 u) θ) ^ 2 * sGam α θ
            + ∑ k ∈ Finset.range (i - 1),
                (Work.Elliptic.Dth1Iter (k + 1) u θ) ^ 2 * sGam α θ) := by
        rw [hbrB_eq, hbrA, hg]


end Work.FTS.EllipticEst.TT
end
end
-- ===== merged: Submission.Work.FTS.EllipticEst.ThetaU.OpenAux =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.ThetaU

set_option autoImplicit false
set_option maxHeartbeats 800000

/-! ## The coefficient `b` -/

/-- `b z = (z-3)/(1+z)`, the logarithmic derivative of `z * (w z)^2`: `(z w²)' = b · w²`. -/
def bcoef (z : ℝ) : ℝ := (z - 3) / (1 + z)

theorem bcoef_abs_le {z : ℝ} (hz : 0 ≤ z) : |bcoef z| ≤ 3 := by
  rw [bcoef, abs_div, abs_of_pos (by linarith : (0 : ℝ) < 1 + z)]
  rw [div_le_iff₀ (by linarith : (0 : ℝ) < 1 + z)]
  rcases le_or_gt z 3 with h | h
  · rw [abs_of_nonpos (by linarith)]; linarith
  · rw [abs_of_pos (by linarith)]; linarith

/-- The derivative of `z ↦ z * (w z)^2`, in terms of `bcoef`. -/
theorem deriv_mul_w_sq {z : ℝ} (hz : 0 < z) :
    deriv (fun y : ℝ => y * (Work.Spaces.w y) ^ 2) z
      = bcoef z * (Work.Spaces.w z) ^ 2 := by
  obtain ⟨_, _, _, hG, _, _, _, _, _, _, _⟩ := Work.FTS.EllipticEst.weight_algebra_fts
  rw [hG z (ne_of_gt hz), bcoef, Work.Spaces.w]
  field_simp

/-- `z ↦ z * (w z)^2` is differentiable at every `z > 0`, with derivative `b z · w z ²`. -/
theorem hasDerivAt_mul_w_sq (z : ℝ) (hz : 0 < z) :
    HasDerivAt (fun y : ℝ => y * (Work.Spaces.w y) ^ 2) (bcoef z * (Work.Spaces.w z) ^ 2) z := by
  have hd : DifferentiableAt ℝ (fun y : ℝ => y * (Work.Spaces.w y) ^ 2) z := by
    have heq : (fun y : ℝ => y * (Work.Spaces.w y) ^ 2)
        =ᶠ[𝓝 z] (fun y : ℝ => (1 + y) ^ 4 / y ^ 3) := by
      filter_upwards [isOpen_ne.mem_nhds (ne_of_gt hz)] with y hy
      rw [Work.Spaces.w]
      field_simp
    rw [heq.differentiableAt_iff]
    exact DifferentiableAt.div (by fun_prop) (by fun_prop) (pow_ne_zero 3 (ne_of_gt hz))
  rw [← deriv_mul_w_sq hz]
  exact hd.hasDerivAt

/-- `b · w²` as a rational function. -/
theorem bcoef_mul_w_sq (z : ℝ) (hz : z ≠ 0) :
    bcoef z * (Work.Spaces.w z) ^ 2 = (z - 3) * (1 + z) ^ 3 / z ^ 4 := by
  rw [bcoef, Work.Spaces.w]
  field_simp

/-- `w² · z` as a rational function. -/
theorem w_sq_mul_self (z : ℝ) (hz : z ≠ 0) :
    (Work.Spaces.w z) ^ 2 * z = (1 + z) ^ 4 / z ^ 3 := by
  rw [Work.Spaces.w]
  field_simp

/-! ## Radial integration by parts against `w² dz` -/

/-- **Radial integration by parts for the weight `w²`**, for functions vanishing off `[δ,R]`
with `0 < δ < R`:
`∫_{Iz} w² φ (z ∂_z ψ) = ∫_{Iz} w² (-(z ∂_z φ) - b φ) ψ`, `b z = (z-3)/(1+z)`.

The boundary terms vanish: `φ ψ` is supported in `[δ,R]`. -/
theorem radial_ibp_eta {δ R : ℝ} (hδ : 0 < δ) (hδR : δ < R) {φ ψ : ℝ → ℝ}
    (hφ : ContDiffOn ℝ 1 φ (Set.Ioi 0)) (hψ : ContDiffOn ℝ 1 ψ (Set.Ioi 0))
    (hsφ : ∀ z, (0 < z ∧ z < δ) ∨ R < z → φ z = 0)
    (hsψ : ∀ z, (0 < z ∧ z < δ) ∨ R < z → ψ z = 0) :
    (∫ z in Work.Spaces.Iz, (Work.Spaces.w z) ^ 2 * φ z * (z * deriv ψ z))
      = ∫ z in Work.Spaces.Iz, (Work.Spaces.w z) ^ 2
          * (-(z * deriv φ z) - (z - 3) / (1 + z) * φ z) * ψ z := by
  set u : ℝ → ℝ := fun y => (Work.Spaces.w y) ^ 2 * y * φ y with hu
  set u' : ℝ → ℝ := fun y => bcoef y * (Work.Spaces.w y) ^ 2 * φ y
      + (Work.Spaces.w y) ^ 2 * y * deriv φ y with hu'
  -- first derivatives of the two factors
  have hderiv_φ : ∀ z ∈ Set.Ioi (0 : ℝ), HasDerivAt φ (deriv φ z) z := by
    intro z hz
    have hd : DifferentiableAt ℝ φ z :=
      (hφ.differentiableOn_one).differentiableAt (isOpen_Ioi.mem_nhds hz)
    exact DifferentiableAt.hasDerivAt hd
  have hderiv_ψ : ∀ z ∈ Set.Ioi (0 : ℝ), HasDerivAt ψ (deriv ψ z) z := by
    intro z hz
    have hd : DifferentiableAt ℝ ψ z :=
      (hψ.differentiableOn_one).differentiableAt (isOpen_Ioi.mem_nhds hz)
    exact DifferentiableAt.hasDerivAt hd
  have hderiv_u : ∀ z ∈ Set.Ioi (0 : ℝ), HasDerivAt u (u' z) z := by
    intro z hz
    have hz0 : 0 < z := hz
    have h1 : HasDerivAt (fun y : ℝ => (Work.Spaces.w y) ^ 2 * y)
        (bcoef z * (Work.Spaces.w z) ^ 2) z := by
      have heq : (fun y : ℝ => (Work.Spaces.w y) ^ 2 * y)
          =ᶠ[𝓝 z] (fun y : ℝ => y * (Work.Spaces.w y) ^ 2) := by
        filter_upwards with y
        ring
      rw [heq.hasDerivAt_iff]
      exact hasDerivAt_mul_w_sq z hz0
    exact h1.mul (hderiv_φ z hz)
  -- continuity of the pieces on the compact interval
  have hcont_w : ContinuousOn (fun z : ℝ => (Work.Spaces.w z) ^ 2 * z) (Set.Icc δ R) := by
    have hrat : ContinuousOn (fun z : ℝ => (1 + z) ^ 4 / z ^ 3) (Set.Icc δ R) := by
      refine ContinuousOn.div (by fun_prop) (by fun_prop) ?_
      intro z hz
      have hz0 : 0 < z := lt_of_lt_of_le hδ hz.1
      positivity
    refine hrat.congr (fun z hz => ?_)
    exact w_sq_mul_self z (ne_of_gt (lt_of_lt_of_le hδ hz.1))
  have hcont_bw : ContinuousOn (fun z : ℝ => bcoef z * (Work.Spaces.w z) ^ 2) (Set.Icc δ R) := by
    have hrat : ContinuousOn (fun z : ℝ => (z - 3) * (1 + z) ^ 3 / z ^ 4) (Set.Icc δ R) := by
      refine ContinuousOn.div (by fun_prop) (by fun_prop) ?_
      intro z hz
      have hz0 : 0 < z := lt_of_lt_of_le hδ hz.1
      positivity
    refine hrat.congr (fun z hz => ?_)
    exact bcoef_mul_w_sq z (ne_of_gt (lt_of_lt_of_le hδ hz.1))
  have hcont_φ : ContinuousOn φ (Set.Icc δ R) :=
    hφ.continuousOn.mono (fun z hz => lt_of_lt_of_le hδ hz.1)
  have hcont_ψ : ContinuousOn ψ (Set.Icc δ R) :=
    hψ.continuousOn.mono (fun z hz => lt_of_lt_of_le hδ hz.1)
  have hcont_ψ' : ContinuousOn (deriv ψ) (Set.Icc δ R) :=
    (hψ.continuousOn_deriv_of_isOpen isOpen_Ioi (le_refl 1)).mono
      (fun z hz => lt_of_lt_of_le hδ hz.1)
  have hcont_φ' : ContinuousOn (deriv φ) (Set.Icc δ R) :=
    (hφ.continuousOn_deriv_of_isOpen isOpen_Ioi (le_refl 1)).mono
      (fun z hz => lt_of_lt_of_le hδ hz.1)
  -- integrability of `u * ψ'` on `(0,∞)`
  have hIntF : IntegrableOn (fun z => u z * deriv ψ z) (Set.Ioi 0) := by
    have h1 : IntegrableOn (fun z => u z * deriv ψ z) (Set.Ioo 0 δ) := by
      refine MeasureTheory.integrableOn_zero.congr_fun (fun z hz => ?_) measurableSet_Ioo
      rw [show u z = (Work.Spaces.w z) ^ 2 * z * φ z from rfl, hsφ z (Or.inl hz)]
      ring
    have h2 : IntegrableOn (fun z => u z * deriv ψ z) (Set.Icc δ R) := by
      refine ContinuousOn.integrableOn_compact isCompact_Icc ?_
      rw [show (fun z => u z * deriv ψ z)
          = fun z => ((Work.Spaces.w z) ^ 2 * z) * (φ z * deriv ψ z) from by
        funext z; simp only [u]; ring]
      exact hcont_w.mul (hcont_φ.mul hcont_ψ')
    have h3 : IntegrableOn (fun z => u z * deriv ψ z) (Set.Ioi R) := by
      refine MeasureTheory.integrableOn_zero.congr_fun (fun z hz => ?_) measurableSet_Ioi
      rw [show u z = (Work.Spaces.w z) ^ 2 * z * φ z from rfl, hsφ z (Or.inr hz)]
      ring
    have h4 := h1.union (h2.union h3)
    rwa [show Set.Ioo (0 : ℝ) δ ∪ (Set.Icc δ R ∪ Set.Ioi R) = Set.Ioi 0 from ?_] at h4
    ext z
    simp only [Set.mem_union, Set.mem_Ioo, Set.mem_Icc, Set.mem_Ioi]
    constructor
    · rintro (⟨h1, -⟩ | ⟨h2, -⟩ | h3) <;> linarith
    · intro hz
      rcases lt_or_ge z δ with h | h
      · exact Or.inl ⟨hz, h⟩
      · rcases le_or_gt z R with h' | h'
        · exact Or.inr (Or.inl ⟨h, h'⟩)
        · exact Or.inr (Or.inr h')
  -- integrability of `u' * ψ` on `(0,∞)`
  have hIntG : IntegrableOn (fun z => u' z * ψ z) (Set.Ioi 0) := by
    have h1 : IntegrableOn (fun z => u' z * ψ z) (Set.Ioo 0 δ) := by
      refine MeasureTheory.integrableOn_zero.congr_fun (fun z hz => ?_) measurableSet_Ioo
      rw [show u' z = bcoef z * (Work.Spaces.w z) ^ 2 * φ z
          + (Work.Spaces.w z) ^ 2 * z * deriv φ z from rfl,
        hsφ z (Or.inl hz), hsψ z (Or.inl hz)]
      ring
    have h2 : IntegrableOn (fun z => u' z * ψ z) (Set.Icc δ R) := by
      refine ContinuousOn.integrableOn_compact isCompact_Icc ?_
      rw [show (fun z => u' z * ψ z)
          = fun z => (bcoef z * (Work.Spaces.w z) ^ 2) * (φ z * ψ z)
              + ((Work.Spaces.w z) ^ 2 * z) * (deriv φ z * ψ z) from by
        funext z; simp only [u']; ring]
      exact (hcont_bw.mul (hcont_φ.mul hcont_ψ)).add (hcont_w.mul (hcont_φ'.mul hcont_ψ))
    have h3 : IntegrableOn (fun z => u' z * ψ z) (Set.Ioi R) := by
      refine MeasureTheory.integrableOn_zero.congr_fun (fun z hz => ?_) measurableSet_Ioi
      rw [show u' z = bcoef z * (Work.Spaces.w z) ^ 2 * φ z
          + (Work.Spaces.w z) ^ 2 * z * deriv φ z from rfl,
        hsφ z (Or.inr hz), hsψ z (Or.inr hz)]
      ring
    have h4 := h1.union (h2.union h3)
    rwa [show Set.Ioo (0 : ℝ) δ ∪ (Set.Icc δ R ∪ Set.Ioi R) = Set.Ioi 0 from ?_] at h4
    ext z
    simp only [Set.mem_union, Set.mem_Ioo, Set.mem_Icc, Set.mem_Ioi]
    constructor
    · rintro (⟨h1, -⟩ | ⟨h2, -⟩ | h3) <;> linarith
    · intro hz
      rcases lt_or_ge z δ with h | h
      · exact Or.inl ⟨hz, h⟩
      · rcases le_or_gt z R with h' | h'
        · exact Or.inr (Or.inl ⟨h, h'⟩)
        · exact Or.inr (Or.inr h')
  -- the two boundary limits
  have hzero : Tendsto (fun z => u z * ψ z) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    have hev : (fun z => u z * ψ z) =ᶠ[𝓝[>] (0 : ℝ)] (fun _ => (0 : ℝ)) := by
      filter_upwards [Ioo_mem_nhdsGT hδ] with z hz
      have hz0 : 0 < z := hz.1
      rw [show u z = (Work.Spaces.w z) ^ 2 * z * φ z from rfl, hsφ z (Or.inl ⟨hz0, hz.2⟩)]
      ring
    exact tendsto_const_nhds.congr' hev.symm
  have hinfty : Tendsto (fun z => u z * ψ z) atTop (𝓝 0) := by
    have hev : (fun z => u z * ψ z) =ᶠ[atTop] (fun _ => (0 : ℝ)) := by
      filter_upwards [eventually_gt_atTop R] with z hz
      rw [show u z = (Work.Spaces.w z) ^ 2 * z * φ z from rfl, hsφ z (Or.inr hz),
        hsψ z (Or.inr hz)]
      ring
    exact tendsto_const_nhds.congr' hev.symm
  -- integration by parts on `(0,∞)`
  have hIBP : (∫ z in Set.Ioi (0 : ℝ), u z * deriv ψ z)
      = - ∫ z in Set.Ioi (0 : ℝ), u' z * ψ z := by
    have h := MeasureTheory.integral_Ioi_mul_deriv_eq_deriv_mul (a := (0 : ℝ)) (a' := 0) (b' := 0)
      (u := u) (u' := u') (v := ψ) (v' := deriv ψ) hderiv_u hderiv_ψ hIntF hIntG hzero hinfty
    simpa using h
  -- back to set integrals over `Iz`
  have hIz : Work.Spaces.Iz = Set.Ici (0 : ℝ) := rfl
  rw [hIz, MeasureTheory.integral_Ici_eq_integral_Ioi,
    MeasureTheory.integral_Ici_eq_integral_Ioi]
  have hleft : (∫ z in Set.Ioi (0 : ℝ), (Work.Spaces.w z) ^ 2 * φ z * (z * deriv ψ z))
      = ∫ z in Set.Ioi (0 : ℝ), u z * deriv ψ z := by
    refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioi (fun z hz => ?_)
    simp only [u]
    ring
  have hright : (∫ z in Set.Ioi (0 : ℝ), (Work.Spaces.w z) ^ 2
        * (-(z * deriv φ z) - (z - 3) / (1 + z) * φ z) * ψ z)
      = - ∫ z in Set.Ioi (0 : ℝ), u' z * ψ z := by
    rw [← MeasureTheory.integral_neg]
    refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioi (fun z hz => ?_)
    simp only [u', bcoef]
    ring
  rw [hleft, hright, hIBP]

end Work.FTS.EllipticEst.ThetaU
end
end
-- ===== merged: Submission.Work.FTS.EllipticEst.WeakMoment.Open.DerivLeIntegralAbsD2 =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.WeakMoment.Open

open scoped Real Topology Interval
open MeasureTheory Set Filter

/-- **Rolle's theorem in the form needed here**: a function which is continuous on `Iθ = [0, π/2]`
and vanishes at both endpoints has a zero of its derivative in the open interval. -/
private theorem exists_deriv_eq_zero_on_Iθ {u : ℝ → ℝ}
    (hcont : ContinuousOn u Work.Spaces.Iθ) (h0 : u 0 = 0) (hpi : u (Real.pi / 2) = 0) :
    ∃ θ₀ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2), deriv u θ₀ = 0 := by
  have hpi2 : (0 : ℝ) < Real.pi / 2 := by positivity
  have hcont' : ContinuousOn u (Set.Icc (0 : ℝ) (Real.pi / 2)) := by
    simpa only [Work.Spaces.Iθ] using hcont
  have hfI : u 0 = u (Real.pi / 2) := by rw [h0, hpi]
  exact exists_deriv_eq_zero hpi2 hcont' hfI

theorem DerivLeIntegralAbsD2 {u : ℝ → ℝ}
    (hsm : ∀ n : ℕ, ContDiffOn ℝ n u (Set.Ioo (0 : ℝ) (Real.pi / 2)))
    (hcont : ContinuousOn u Work.Spaces.Iθ) (h0 : u 0 = 0) (hpi : u (Real.pi / 2) = 0)
    (habs : MeasureTheory.IntegrableOn
      (fun θ : ℝ => |Work.FTS.EllipticEst.TT.D2 u θ|) Work.Spaces.Iθ) :
    ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      |deriv u θ| ≤ ∫ x in Work.Spaces.Iθ, |Work.FTS.EllipticEst.TT.D2 u x| := by
  -- Rolle: the derivative has an interior zero because `u` vanishes at both endpoints.
  obtain ⟨θ₀, hθ₀, hzero⟩ := exists_deriv_eq_zero_on_Iθ hcont h0 hpi
  intro θ hθ
  -- The fundamental theorem of calculus on the segment `[θ₀, θ]` and the triangle
  -- inequality for the integral.
  have h := Work.FTS.EllipticEst.SgamBound.abs_deriv_sub_le_integral_abs_D2 hsm habs hθ hθ₀
  simpa only [hzero, sub_zero] using h

end Work.FTS.EllipticEst.WeakMoment.Open
end
-- ===== merged: Submission.Work.FTS.EllipticEst.remov.SourceBound.sliceTendstoZeroOfMoment =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.remov.SourceBound

set_option autoImplicit false

/-! ## Auxiliary facts

The proof of `sliceTendstoZeroOfMoment` goes through the exact derivative
`(Lzero1 u θ) · sinθcos²θ = d/dθ [ -u'(θ) sinθcos²θ + u(θ) cosθcos2θ ]`
(`Work.Elliptic.hasDerivAt_Lzero_antideriv`), whose boundary values are `lim_{0⁺} u` at `0` and
`0` at `π/2`.  Hence `∫_{Iθ} Lzero1 u · sinCos2 = -lim_{0⁺} u`, and the assumed moment condition
forces the limit to vanish.  The two lemmas below supply the control of `u'` (from the weighted
square-integrability of `u''`) and the existence of the left endpoint limit. -/

/-- **`u'` is bounded on the open quadrant.**  Since `sEta θ = sin(2θ)^{-η} ≥ 1` on `(0,π/2)`,
the hypothesis makes `|u''|` integrable on `Iθ` (`integrableAbsOfSqSeta`), and the fundamental
theorem of calculus based at `π/4` bounds `u'` by `|u'(π/4)| + ∫_{Iθ}|u''|`. -/
lemma auxDerivBound {u : ℝ → ℝ}
    (hu : ContDiffOn ℝ 2 u (Set.Ioo 0 (Real.pi / 2)))
    (hint : MeasureTheory.IntegrableOn
      (fun θ => (deriv (fun t => deriv u t) θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)
      Work.Spaces.Iθ) :
    ∃ M : ℝ, ∀ θ ∈ Set.Ioo 0 (Real.pi / 2), |deriv u θ| ≤ M := by
  have hIoo : IsOpen (Set.Ioo (0 : ℝ) (Real.pi / 2)) := isOpen_Ioo
  have hd1 : ContDiffOn ℝ 1 (deriv u) (Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
    hu.deriv_of_isOpen hIoo (m := 1) (by norm_num)
  have hd2 : ContinuousOn (deriv (fun t => deriv u t)) (Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
    contDiffOn_zero.1 (hd1.deriv_of_isOpen hIoo (m := 0) (by norm_num))
  have hdc : ContinuousOn (deriv u) (Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
    hu.continuousOn_deriv_of_isOpen hIoo (by norm_num)
  have hdiff1 : DifferentiableOn ℝ (deriv u) (Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
    hd1.differentiableOn (by norm_num)
  have habs : MeasureTheory.IntegrableOn
      (fun θ : ℝ => |deriv (fun t => deriv u t) θ|) Work.Spaces.Iθ :=
    Work.FTS.EllipticEst.integrableAbsOfSqSeta hd2 hint
  have hpi4 : (0 : ℝ) < Real.pi / 4 := by linarith [Real.pi_pos]
  have hpi4lt : Real.pi / 4 < Real.pi / 2 := by linarith [Real.pi_pos]
  -- increment estimate on any subinterval `[a,b] ⊆ (0,π/2)`
  have hkey : ∀ a b : ℝ, a ≤ b → 0 < a → b < Real.pi / 2 →
      |deriv u b - deriv u a|
        ≤ ∫ x in Work.Spaces.Iθ, |deriv (fun t => deriv u t) x| := by
    intro a b hab ha hb
    have hsub : Set.uIcc a b ⊆ Set.Ioo (0 : ℝ) (Real.pi / 2) := by
      rw [Set.uIcc_of_le hab]
      intro x hx
      exact ⟨lt_of_lt_of_le ha hx.1, lt_of_le_of_lt hx.2 hb⟩
    have hcont : ContinuousOn (deriv u) (Set.uIcc a b) := hdc.mono hsub
    have hdder : ∀ x ∈ Set.uIoo a b, DifferentiableAt ℝ (deriv u) x := by
      intro x hx
      rw [Set.uIoo_of_le hab] at hx
      exact hdiff1.differentiableAt (isOpen_Ioo.mem_nhds
        ⟨lt_trans ha hx.1, lt_trans hx.2 hb⟩)
    have hintI : IntervalIntegrable (deriv (fun t => deriv u t)) volume a b :=
      (hd2.mono hsub).intervalIntegrable
    have hftc : ∫ y in a..b, deriv (fun t => deriv u t) y = deriv u b - deriv u a :=
      intervalIntegral.integral_deriv_eq_sub_uIoo hcont hdder hintI
    have hle : ∫ y in a..b, |deriv (fun t => deriv u t) y|
        ≤ ∫ x in Work.Spaces.Iθ, |deriv (fun t => deriv u t) x| := by
      rw [intervalIntegral.integral_of_le hab]
      refine setIntegral_mono_set habs (Eventually.of_forall (fun x => abs_nonneg _)) ?_
      exact Eventually.of_forall (fun x hx =>
        ⟨le_of_lt (lt_trans ha hx.1), le_of_lt (lt_of_le_of_lt hx.2 hb)⟩)
    calc |deriv u b - deriv u a|
        = |∫ y in a..b, deriv (fun t => deriv u t) y| := by rw [hftc]
      _ ≤ ∫ y in a..b, |deriv (fun t => deriv u t) y| :=
          intervalIntegral.abs_integral_le_integral_abs
            (f := fun y => deriv (fun t => deriv u t) y) hab
      _ ≤ _ := hle
  refine ⟨|deriv u (Real.pi / 4)|
      + ∫ x in Work.Spaces.Iθ, |deriv (fun t => deriv u t) x|, ?_⟩
  intro θ hθ
  have hsum : |deriv u θ| ≤ |deriv u θ - deriv u (Real.pi / 4)|
      + |deriv u (Real.pi / 4)| := by
    have h := abs_add_le (deriv u θ - deriv u (Real.pi / 4)) (deriv u (Real.pi / 4))
    rwa [sub_add_cancel] at h
  have hstep : |deriv u θ - deriv u (Real.pi / 4)|
      ≤ ∫ x in Work.Spaces.Iθ, |deriv (fun t => deriv u t) x| := by
    rcases le_total θ (Real.pi / 4) with hle | hge
    · rw [abs_sub_comm]
      exact hkey θ (Real.pi / 4) hle hθ.1 hpi4lt
    · exact hkey (Real.pi / 4) θ hge hpi4 hθ.2
  calc |deriv u θ| ≤ |deriv u θ - deriv u (Real.pi / 4)| + |deriv u (Real.pi / 4)| := hsum
    _ ≤ (∫ x in Work.Spaces.Iθ, |deriv (fun t => deriv u t) x|) + |deriv u (Real.pi / 4)| :=
        add_le_add hstep le_rfl
    _ = |deriv u (Real.pi / 4)|
        + ∫ x in Work.Spaces.Iθ, |deriv (fun t => deriv u t) x| := by ring

/-- **The left endpoint limit exists.**  A `C²` function on `(0,π/2)` whose second derivative
satisfies the weighted square-integrability hypothesis has a finite limit at `0⁺`: the weight
forces `|u''| ∈ L¹`, hence `u'` is bounded on `(0,π/4)` and therefore integrable there, and
`exists_tendsto_nhdsGT_zero_of_integrableOn_deriv` applies. -/
lemma auxLimitAtZero {u : ℝ → ℝ}
    (hu : ContDiffOn ℝ 2 u (Set.Ioo 0 (Real.pi / 2)))
    (hint : MeasureTheory.IntegrableOn
      (fun θ => (deriv (fun t => deriv u t) θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)
      Work.Spaces.Iθ) :
    ∃ α : ℝ, Filter.Tendsto u (nhdsWithin 0 (Set.Ioi 0)) (nhds α) := by
  obtain ⟨M, hM⟩ := auxDerivBound hu hint
  have hpi4 : (0 : ℝ) < Real.pi / 4 := by linarith [Real.pi_pos]
  have hpi4lt : Real.pi / 4 < Real.pi / 2 := by linarith [Real.pi_pos]
  refine Work.FTS.EllipticEst.exists_tendsto_nhdsGT_zero_of_integrableOn_deriv
    (f := u) (f' := deriv u) (δ := Real.pi / 4) hpi4 ?_ ?_
  · intro x hx
    have hx' : x ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) := ⟨hx.1, lt_of_lt_of_le hx.2 hpi4lt.le⟩
    exact ((hu.contDiffAt (isOpen_Ioo.mem_nhds hx')).differentiableAt (by norm_num)).hasDerivAt
  · refine MeasureTheory.IntegrableOn.of_bound ?_ (measurable_deriv u).aestronglyMeasurable M ?_
    · rw [Real.volume_Ioo]; exact ENNReal.ofReal_lt_top
    · exact MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioo (fun x hx => by
        rw [Real.norm_eq_abs]
        exact hM x ⟨hx.1, lt_of_lt_of_le hx.2 hpi4lt.le⟩)

/-- **The angular moment identity.**  Under the hypotheses of
`sliceTendstoZeroOfMoment` (except the moment condition) one has
`∫_{Iθ} Lzero1 u · sinθcos²θ = -lim_{0⁺} u`. -/
lemma auxMoment {u : ℝ → ℝ} {α : ℝ}
    (hu : ContDiffOn ℝ 2 u (Set.Ioo 0 (Real.pi / 2)))
    (hint : MeasureTheory.IntegrableOn
      (fun θ => (deriv (fun t => deriv u t) θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)
      Work.Spaces.Iθ)
    (hg : MeasureTheory.IntegrableOn
      (fun θ => (Work.FTS.EllipticEst.Lzero1 u θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)
      Work.Spaces.Iθ)
    (hlim : Filter.Tendsto u (nhdsWithin 0 (Set.Ioi 0)) (nhds α)) :
    (∫ θ in Work.Spaces.Iθ,
      Work.FTS.EllipticEst.Lzero1 u θ * Work.Elliptic.sinCos2 θ) = -α := by
  obtain ⟨M, hM⟩ := auxDerivBound hu hint
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  have hpi4 : (0 : ℝ) < Real.pi / 4 := by linarith [Real.pi_pos]
  have hpi4lt : Real.pi / 4 < Real.pi / 2 := by linarith [Real.pi_pos]
  have hle_pi : (0 : ℝ) ≤ Real.pi / 2 := by linarith
  -- ## the exact derivative
  have hderiv : ∀ x ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      HasDerivAt (fun θ : ℝ => -(deriv u θ) * Work.Elliptic.sinCos2 θ
          + u θ * (Real.cos θ * Real.cos (2 * θ)))
        (Work.FTS.EllipticEst.Lzero1 u x * Work.Elliptic.sinCos2 x) x := by
    intro x hx
    have h2 : ContDiffAt ℝ 2 u x := hu.contDiffAt (isOpen_Ioo.mem_nhds hx)
    have h3 := Work.Elliptic.hasDerivAt_Lzero_antideriv (fun _ θ' => u θ') 0 x hx h2
    have hL : Work.Elliptic.Lzero (fun _ θ' => u θ') 0 x
        = Work.FTS.EllipticEst.Lzero1 u x := by
      simpa using (congrFun (Work.FTS.EllipticEst.Lzero1_eq_Lzero u 0) x).symm
    rw [hL] at h3
    simpa using h3
  -- ## integrability of the integrand
  have hgint : MeasureTheory.IntegrableOn
      (fun θ : ℝ => Work.FTS.EllipticEst.Lzero1 u θ * Work.Elliptic.sinCos2 θ)
      Work.Spaces.Iθ := by
    have h0 := Work.FTS.EllipticEst.SliceLocal.integrableOn_sinCos2_Lzero1 u hu hg
    rw [MeasureTheory.IntegrableOn] at h0 ⊢
    refine h0.congr (Eventually.of_forall (fun θ => ?_))
    simp only [Work.Elliptic.sinCos2]
    ring
  have hint' : IntervalIntegrable
      (fun θ : ℝ => Work.FTS.EllipticEst.Lzero1 u θ * Work.Elliptic.sinCos2 θ)
      volume 0 (Real.pi / 2) :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hle_pi).mpr
      (hgint.mono_set (fun x hx => ⟨le_of_lt hx.1, hx.2⟩))
  -- ## continuity facts for the boundary terms
  have hScont : Continuous (fun θ : ℝ => Work.Elliptic.sinCos2 θ) := by
    have hfun : (fun θ : ℝ => Work.Elliptic.sinCos2 θ)
        = fun θ : ℝ => Real.sin θ * Real.cos θ ^ 2 := rfl
    rw [hfun]
    exact Real.continuous_sin.mul (Real.continuous_cos.pow 2)
  have hcoscont : Continuous (fun θ : ℝ => Real.cos θ * Real.cos (2 * θ)) := by fun_prop
  -- ## the left endpoint limit of the antiderivative
  have hA0 : Tendsto (fun θ : ℝ => -(deriv u θ) * Work.Elliptic.sinCos2 θ)
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) := by
    have hmaj : Tendsto (fun θ : ℝ => M * |Work.Elliptic.sinCos2 θ|)
        (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) := by
      have h0 : (fun θ : ℝ => Work.Elliptic.sinCos2 θ) 0 = 0 := by
        simp only [Work.Elliptic.sinCos2]
        norm_num
      have hS : Tendsto (fun θ : ℝ => Work.Elliptic.sinCos2 θ)
          (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) := by
        simpa [h0] using ((hScont.continuousAt (x := 0)).tendsto).mono_left nhdsWithin_le_nhds
      simpa using hS.abs.const_mul M
    have hsqueeze : Tendsto (fun θ : ℝ => ‖-(deriv u θ) * Work.Elliptic.sinCos2 θ‖)
        (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) := by
      refine squeeze_zero' (Eventually.of_forall (fun θ => norm_nonneg _)) ?_ hmaj
      rw [eventually_nhdsWithin_iff]
      filter_upwards [Iio_mem_nhds (show (0 : ℝ) < Real.pi / 2 by linarith)] with θ hθ hθmem
      rw [Real.norm_eq_abs, abs_mul, abs_neg]
      exact mul_le_mul_of_nonneg_right (hM θ ⟨hθmem, hθ⟩) (abs_nonneg _)
    rwa [tendsto_zero_iff_norm_tendsto_zero]
  have hB0 : Tendsto (fun θ : ℝ => u θ * (Real.cos θ * Real.cos (2 * θ)))
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds α) := by
    have hc : Tendsto (fun θ : ℝ => Real.cos θ * Real.cos (2 * θ))
        (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 1) := by
      have h0 : (fun θ : ℝ => Real.cos θ * Real.cos (2 * θ)) 0 = 1 := by norm_num
      simpa [h0] using ((hcoscont.continuousAt (x := 0)).tendsto).mono_left nhdsWithin_le_nhds
    simpa using hlim.mul hc
  have hQ0 : Tendsto (fun θ : ℝ => -(deriv u θ) * Work.Elliptic.sinCos2 θ
      + u θ * (Real.cos θ * Real.cos (2 * θ)))
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds α) := by
    simpa using hA0.add hB0
  -- ## `u` is bounded near `π/2`
  have hu_bound : ∀ θ ∈ Set.Ioo (Real.pi / 4) (Real.pi / 2),
      |u θ| ≤ |u (Real.pi / 4)| + M * (Real.pi / 2 - Real.pi / 4) := by
    intro θ hθ
    have hsub : Set.uIcc (Real.pi / 4) θ ⊆ Set.Ioo (0 : ℝ) (Real.pi / 2) := by
      rw [Set.uIcc_of_le hθ.1.le]
      intro x hx
      exact ⟨by linarith [hx.1, Real.pi_pos], by linarith [hx.2, hθ.2]⟩
    have hcont : ContinuousOn u (Set.uIcc (Real.pi / 4) θ) := hu.continuousOn.mono hsub
    have hdder : ∀ x ∈ Set.uIoo (Real.pi / 4) θ, DifferentiableAt ℝ u x := by
      intro x hx
      rw [Set.uIoo_of_le hθ.1.le] at hx
      have hx' : x ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) :=
        ⟨by linarith [hx.1, Real.pi_pos], by linarith [hx.2, hθ.2]⟩
      exact (hu.contDiffAt (isOpen_Ioo.mem_nhds hx')).differentiableAt (by norm_num)
    have hdc1 : ContinuousOn (deriv u) (Set.uIcc (Real.pi / 4) θ) :=
      (hu.continuousOn_deriv_of_isOpen isOpen_Ioo (by norm_num)).mono hsub
    have hftc : ∫ y in (Real.pi / 4)..θ, deriv u y = u θ - u (Real.pi / 4) :=
      intervalIntegral.integral_deriv_eq_sub_uIoo hcont hdder hdc1.intervalIntegrable
    have h1 : |u θ - u (Real.pi / 4)| ≤ M * (θ - Real.pi / 4) := by
      have hb : ∀ x ∈ Set.uIoc (Real.pi / 4) θ, ‖deriv u x‖ ≤ M := by
        intro x hx
        rw [Set.uIoc_of_le hθ.1.le] at hx
        rw [Real.norm_eq_abs]
        exact hM x ⟨by linarith [hx.1, Real.pi_pos], by linarith [hx.2, hθ.2]⟩
      have hkey := intervalIntegral.norm_integral_le_of_norm_le_const
        (f := deriv u) (a := Real.pi / 4) (b := θ) hb
      rw [hftc, Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr hθ.1.le)] at hkey
      exact hkey
    have h2 : |u θ| ≤ |u (Real.pi / 4)| + |u θ - u (Real.pi / 4)| := by
      have h := abs_add_le (u (Real.pi / 4)) (u θ - u (Real.pi / 4))
      rwa [add_sub_cancel] at h
    have hMnn : 0 ≤ M := by
      have h := hM (Real.pi / 4) ⟨hpi4, hpi4lt⟩
      linarith [abs_nonneg (deriv u (Real.pi / 4))]
    have h3 : M * (θ - Real.pi / 4) ≤ M * (Real.pi / 2 - Real.pi / 4) :=
      mul_le_mul_of_nonneg_left (by linarith [hθ.2]) hMnn
    linarith [h1, h2, h3]
  have hA1 : Tendsto (fun θ : ℝ => -(deriv u θ) * Work.Elliptic.sinCos2 θ)
      (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds 0) := by
    have hmaj : Tendsto (fun θ : ℝ => M * |Work.Elliptic.sinCos2 θ|)
        (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds 0) := by
      have h0 : (fun θ : ℝ => Work.Elliptic.sinCos2 θ) (Real.pi / 2) = 0 := by
        simp only [Work.Elliptic.sinCos2, Real.sin_pi_div_two, Real.cos_pi_div_two]
        norm_num
      have hS : Tendsto (fun θ : ℝ => Work.Elliptic.sinCos2 θ)
          (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds 0) := by
        simpa [h0] using
          ((hScont.continuousAt (x := Real.pi / 2)).tendsto).mono_left nhdsWithin_le_nhds
      simpa using hS.abs.const_mul M
    have hsqueeze : Tendsto (fun θ : ℝ => ‖-(deriv u θ) * Work.Elliptic.sinCos2 θ‖)
        (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds 0) := by
      refine squeeze_zero' (Eventually.of_forall (fun θ => norm_nonneg _)) ?_ hmaj
      rw [eventually_nhdsWithin_iff]
      filter_upwards [Ioi_mem_nhds (show Real.pi / 4 < Real.pi / 2 by linarith)]
        with θ hθ hθmem
      rw [Real.norm_eq_abs, abs_mul, abs_neg]
      exact mul_le_mul_of_nonneg_right (hM θ ⟨lt_trans hpi4 hθ, hθmem⟩) (abs_nonneg _)
    rwa [tendsto_zero_iff_norm_tendsto_zero]
  have hB1 : Tendsto (fun θ : ℝ => u θ * (Real.cos θ * Real.cos (2 * θ)))
      (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds 0) := by
    have hc : Tendsto (fun θ : ℝ => Real.cos θ * Real.cos (2 * θ))
        (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds 0) := by
      have h0 : (fun θ : ℝ => Real.cos θ * Real.cos (2 * θ)) (Real.pi / 2) = 0 := by
        simp only [Real.cos_pi_div_two]
        norm_num
      simpa [h0] using
        ((hcoscont.continuousAt (x := Real.pi / 2)).tendsto).mono_left nhdsWithin_le_nhds
    have hmaj : Tendsto (fun θ : ℝ => (|u (Real.pi / 4)|
        + M * (Real.pi / 2 - Real.pi / 4)) * |Real.cos θ * Real.cos (2 * θ)|)
        (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds 0) := by
      simpa using hc.abs.const_mul (|u (Real.pi / 4)| + M * (Real.pi / 2 - Real.pi / 4))
    have hsqueeze : Tendsto (fun θ : ℝ => ‖u θ * (Real.cos θ * Real.cos (2 * θ))‖)
        (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds 0) := by
      refine squeeze_zero' (Eventually.of_forall (fun θ => norm_nonneg _)) ?_ hmaj
      rw [eventually_nhdsWithin_iff]
      filter_upwards [Ioi_mem_nhds (show Real.pi / 4 < Real.pi / 2 by linarith)]
        with θ hθ hθmem
      rw [Real.norm_eq_abs, abs_mul]
      exact mul_le_mul_of_nonneg_right (hu_bound θ ⟨hθ, hθmem⟩) (abs_nonneg _)
    rwa [tendsto_zero_iff_norm_tendsto_zero]
  have hQpi : Tendsto (fun θ : ℝ => -(deriv u θ) * Work.Elliptic.sinCos2 θ
      + u θ * (Real.cos θ * Real.cos (2 * θ)))
      (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds 0) := by
    simpa using hA1.add hB1
  -- ## the fundamental theorem of calculus on the whole interval
  have hFTC : ∫ y in (0 : ℝ)..(Real.pi / 2),
      Work.FTS.EllipticEst.Lzero1 u y * Work.Elliptic.sinCos2 y = 0 - α :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt_of_tendsto
      (f := fun θ : ℝ => -(deriv u θ) * Work.Elliptic.sinCos2 θ
        + u θ * (Real.cos θ * Real.cos (2 * θ)))
      (f' := fun θ : ℝ => Work.FTS.EllipticEst.Lzero1 u θ * Work.Elliptic.sinCos2 θ)
      (fa := α) (fb := 0) (by linarith) hderiv hint' hQ0 hQpi
  change (∫ θ in Set.Icc (0 : ℝ) (Real.pi / 2),
      Work.FTS.EllipticEst.Lzero1 u θ * Work.Elliptic.sinCos2 θ) = -α
  rw [MeasureTheory.integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hle_pi,
    hFTC]
  ring

theorem sliceTendstoZeroOfMoment :
    ∀ u : ℝ → ℝ,
      ContDiffOn ℝ 2 u (Set.Ioo 0 (Real.pi / 2)) →
      MeasureTheory.IntegrableOn
        (fun θ => (deriv (fun t => deriv u t) θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)
        Work.Spaces.Iθ →
      MeasureTheory.IntegrableOn
        (fun θ => (Work.FTS.EllipticEst.Lzero1 u θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)
        Work.Spaces.Iθ →
      MeasureTheory.IntegrableOn (fun θ => (u θ) ^ 2) Work.Spaces.Iθ →
      (∫ θ in Work.Spaces.Iθ,
        Work.FTS.EllipticEst.Lzero1 u θ * Work.Elliptic.sinCos2 θ) = 0 →
      Filter.Tendsto u (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
  intro u hu h1 h2 _h3 hmom
  obtain ⟨α, hα⟩ := auxLimitAtZero hu h1
  have hid := auxMoment hu h1 h2 hα
  have hα0 : α = 0 := by linarith
  simpa [hα0] using hα

end Work.FTS.EllipticEst.remov.SourceBound
end
end
-- ===== merged: Submission.Work.FTS.EllipticEst.remov.Step4.slice_Xt_T_bound =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.remov.Step4

set_option autoImplicit false

/-
# Step 4 (Elgindi §H2, tex 931-953): the weighted bound for `(tan θ·u)''·T`

With `v = u / cos θ`, `X = (tan θ·u)''`, `σ = sin(2θ)^{2-γ}` and
`T := sin θ·v'' - 4 cos θ·v' + 5 sin θ·v` (the right-hand side of the differentiated equation),
this proves `∫ X·T·σ ≤ 4 ∫(v'')²σ + 7 ∫(v')²σ + 7 ∫v²σ`, together with the integrability of
`X·T·σ`.

Route: `slice_v_identities` gives on `(0, π/2)` that
`X = sin θ·v'' + 2 cos θ·v' - sin θ·v`, so `X·T` is the product of the two linear forms
`(sinθ, 2cosθ, -sinθ)·(v'',v',v)` and `(sinθ, -4cosθ, 5sinθ)·(v'',v',v)`, and
`Work.FTS.EllipticEst.remov.slice_Q_pointwise` gives pointwise
`X·T ≤ 4 sin²θ(v'')² + 7(v')² + 7v² ≤ 4(v'')² + 7(v')² + 7v²`.
For integrability use the absolute-value domination
`|X·T| ≤ (X² + T²)/2 ≤ 3(v'')² + 30(v')² + 39v²` (from `(a+b+c)² ≤ 3(a²+b²+c²)`), then
`Integrable.mono'`.  As usual the pointwise identities hold on `(0, π/2)`, which equals
`Iθ = [0, π/2]` up to the null set `{0, π/2}`.
-/

/-! ### The null set `{0, π/2}` -/

/-- `[0, π/2]` and `(0, π/2)` agree up to a null set. -/
private lemma sliceXTB_ae_eq_Icc_Ioo :
    (Set.Icc 0 (Real.pi / 2) : Set ℝ) =ᵐ[volume] Set.Ioo 0 (Real.pi / 2) := by
  rw [MeasureTheory.ae_eq_set]
  refine ⟨?_, ?_⟩
  · have hsub : Set.Icc 0 (Real.pi / 2) \ Set.Ioo 0 (Real.pi / 2) ⊆
        ({0, Real.pi / 2} : Set ℝ) := by
      intro x hx
      simp only [Set.mem_sdiff, Set.mem_Icc, Set.mem_Ioo, Set.mem_insert_iff,
        Set.mem_singleton_iff] at hx ⊢
      rcases eq_or_lt_of_le hx.1.1 with h | h
      · exact Or.inl h.symm
      · refine Or.inr ?_
        by_contra hne
        exact hx.2 ⟨h, lt_of_le_of_ne hx.1.2 hne⟩
    have hnull : volume ({0, Real.pi / 2} : Set ℝ) = 0 :=
      (Set.Finite.insert (0 : ℝ) (Set.finite_singleton (Real.pi / 2))).measure_zero _
    exact MeasureTheory.measure_mono_null hsub hnull
  · have h0 : Set.Ioo 0 (Real.pi / 2) \ Set.Icc 0 (Real.pi / 2) = ∅ :=
      Set.sdiff_eq_empty.mpr Set.Ioo_subset_Icc_self
    rw [h0, MeasureTheory.measure_empty]

/-- Consequently `volume.restrict Iθ = volume.restrict (0, π/2)`. -/
private lemma sliceXTB_restrict_Iθ_eq_Ioo :
    (volume.restrict Work.Spaces.Iθ : Measure ℝ)
      = volume.restrict (Set.Ioo 0 (Real.pi / 2)) := by
  simpa [Work.Spaces.Iθ] using
    MeasureTheory.Measure.restrict_congr_set sliceXTB_ae_eq_Icc_Ioo

/-! ### Elementary pointwise bounds for the two linear forms

`X = s a + 2 t b - s c` and `T = s a - 4 t b + 5 s c` with `s = sin θ`, `t = cos θ` and
`s² + t² = 1`: Cauchy–Schwarz for three terms gives `X² ≤ 3(a² + 4b² + c²)` and
`T² ≤ 3(a² + 16b² + 25c²)`, whence `|X·T| ≤ (X² + T²)/2 ≤ 3a² + 30b² + 39c²`. -/

private lemma Xsq_le (θ a b c : ℝ) :
    (Real.sin θ * a + 2 * Real.cos θ * b - Real.sin θ * c) ^ 2
      ≤ 3 * (a ^ 2 + 4 * b ^ 2 + c ^ 2) := by
  have h := Real.sin_sq_add_cos_sq θ
  have hs : Real.sin θ ^ 2 ≤ 1 := Real.sin_sq_le_one θ
  have hc : Real.cos θ ^ 2 ≤ 1 := by
    nlinarith [Real.sin_sq_add_cos_sq θ, sq_nonneg (Real.sin θ)]
  nlinarith [sq_nonneg (Real.sin θ * a - 2 * Real.cos θ * b),
             sq_nonneg (2 * Real.cos θ * b + Real.sin θ * c),
             sq_nonneg (Real.sin θ * c + Real.sin θ * a)]

private lemma Tsq_le (θ a b c : ℝ) :
    (Real.sin θ * a - 4 * Real.cos θ * b + 5 * Real.sin θ * c) ^ 2
      ≤ 3 * (a ^ 2 + 16 * b ^ 2 + 25 * c ^ 2) := by
  have h := Real.sin_sq_add_cos_sq θ
  have hs : Real.sin θ ^ 2 ≤ 1 := Real.sin_sq_le_one θ
  have hc : Real.cos θ ^ 2 ≤ 1 := by
    nlinarith [Real.sin_sq_add_cos_sq θ, sq_nonneg (Real.sin θ)]
  nlinarith [sq_nonneg (Real.sin θ * a + 4 * Real.cos θ * b),
             sq_nonneg (4 * Real.cos θ * b + 5 * Real.sin θ * c),
             sq_nonneg (5 * Real.sin θ * c - Real.sin θ * a)]

private lemma abs_XT_le (θ a b c : ℝ) :
    |(Real.sin θ * a + 2 * Real.cos θ * b - Real.sin θ * c)
      * (Real.sin θ * a - 4 * Real.cos θ * b + 5 * Real.sin θ * c)|
      ≤ 3 * a ^ 2 + 30 * b ^ 2 + 39 * c ^ 2 := by
  set A := Real.sin θ * a + 2 * Real.cos θ * b - Real.sin θ * c with hA
  set B := Real.sin θ * a - 4 * Real.cos θ * b + 5 * Real.sin θ * c with hB
  have h2 : |A * B| ≤ (A ^ 2 + B ^ 2) / 2 := by
    rw [abs_mul]
    nlinarith [sq_nonneg (|A| - |B|), sq_abs A, sq_abs B]
  have h3a : A ^ 2 ≤ 3 * (a ^ 2 + 4 * b ^ 2 + c ^ 2) := by
    rw [hA]; exact Xsq_le θ a b c
  have h3b : B ^ 2 ≤ 3 * (a ^ 2 + 16 * b ^ 2 + 25 * c ^ 2) := by
    rw [hB]; exact Tsq_le θ a b c
  linarith

/-! ### Splitting a sum of three weighted integrals -/

private lemma integral_three {μ : Measure ℝ} {F G H : ℝ → ℝ}
    (hF : Integrable F μ) (hG : Integrable G μ) (hH : Integrable H μ) (c d e : ℝ) :
    ∫ θ, (c * F θ + d * G θ + e * H θ) ∂μ
      = c * (∫ θ, F θ ∂μ) + d * (∫ θ, G θ ∂μ) + e * (∫ θ, H θ ∂μ) := by
  rw [integral_add (f := fun θ => c * F θ + d * G θ) (g := fun θ => e * H θ)
        ((hF.const_mul c).add (hG.const_mul d)) (hH.const_mul e),
      integral_add (f := fun θ => c * F θ) (g := fun θ => d * G θ)
        (hF.const_mul c) (hG.const_mul d),
      integral_const_mul, integral_const_mul, integral_const_mul]

private lemma setIntegral_three (s : Set ℝ) {F G H : ℝ → ℝ}
    (hF : IntegrableOn F s) (hG : IntegrableOn G s) (hH : IntegrableOn H s) (c d e : ℝ) :
    ∫ θ in s, c * F θ + d * G θ + e * H θ
      = c * (∫ θ in s, F θ) + d * (∫ θ in s, G θ) + e * (∫ θ in s, H θ) :=
  integral_three (μ := volume.restrict s) hF hG hH c d e

/-! ### The main statement -/

theorem slice_Xt_T_bound (γ : ℝ) {u : ℝ → ℝ}
    (hu : ContDiffOn ℝ 3 u (Set.Ioo 0 (Real.pi / 2)))
    (hV2 : MeasureTheory.IntegrableOn (fun θ =>
        (deriv (fun t => deriv (fun s => u s / Real.cos s) t) θ) ^ 2 *
        Real.rpow (Real.sin (2 * θ)) (2 - γ)) Work.Spaces.Iθ)
    (hY2 : MeasureTheory.IntegrableOn (fun θ =>
        (deriv (fun t => u t / Real.cos t) θ) ^ 2 *
        Real.rpow (Real.sin (2 * θ)) (2 - γ)) Work.Spaces.Iθ)
    (hY3 : MeasureTheory.IntegrableOn (fun θ =>
        (u θ / Real.cos θ) ^ 2 *
        Real.rpow (Real.sin (2 * θ)) (2 - γ)) Work.Spaces.Iθ) :
    MeasureTheory.IntegrableOn (fun θ =>
        deriv (deriv (fun t => Real.tan t * u t)) θ *
        (Real.sin θ * deriv (fun t => deriv (fun s => u s / Real.cos s) t) θ
          - 4 * Real.cos θ * deriv (fun t => u t / Real.cos t) θ
          + 5 * Real.sin θ * (u θ / Real.cos θ)) *
        Real.rpow (Real.sin (2 * θ)) (2 - γ)) Work.Spaces.Iθ
      ∧ (∫ θ in Work.Spaces.Iθ,
          deriv (deriv (fun t => Real.tan t * u t)) θ *
          (Real.sin θ * deriv (fun t => deriv (fun s => u s / Real.cos s) t) θ
            - 4 * Real.cos θ * deriv (fun t => u t / Real.cos t) θ
            + 5 * Real.sin θ * (u θ / Real.cos θ)) *
          Real.rpow (Real.sin (2 * θ)) (2 - γ))
        ≤ 4 * (∫ θ in Work.Spaces.Iθ,
                (deriv (fun t => deriv (fun s => u s / Real.cos s) t) θ) ^ 2 *
                Real.rpow (Real.sin (2 * θ)) (2 - γ))
          + 7 * (∫ θ in Work.Spaces.Iθ,
                (deriv (fun t => u t / Real.cos t) θ) ^ 2 *
                Real.rpow (Real.sin (2 * θ)) (2 - γ))
          + 7 * (∫ θ in Work.Spaces.Iθ, (u θ / Real.cos θ) ^ 2 *
                Real.rpow (Real.sin (2 * θ)) (2 - γ)) := by
  classical
  -- the open interval and the null-set identification
  set s : Set ℝ := Set.Ioo 0 (Real.pi / 2) with hs_def
  have hsopen : IsOpen s := by rw [hs_def]; exact isOpen_Ioo
  have hsmeas : MeasurableSet s := hsopen.measurableSet
  have hrestrict : (volume.restrict Work.Spaces.Iθ : Measure ℝ) = volume.restrict s := by
    rw [hs_def]; exact sliceXTB_restrict_Iθ_eq_Ioo
  -- abbreviations for `v`, `v'`, `v''`, `X`, `T`, `σ`
  let v0 : ℝ → ℝ := fun θ => u θ / Real.cos θ
  let v1 : ℝ → ℝ := deriv v0
  let v2 : ℝ → ℝ := deriv v1
  let X : ℝ → ℝ := deriv (deriv (fun t => Real.tan t * u t))
  let T : ℝ → ℝ := fun θ => Real.sin θ * v2 θ - 4 * Real.cos θ * v1 θ + 5 * Real.sin θ * v0 θ
  let σ : ℝ → ℝ := fun θ => Real.rpow (Real.sin (2 * θ)) (2 - γ)
  change MeasureTheory.IntegrableOn (fun θ => X θ * T θ * σ θ) Work.Spaces.Iθ
      ∧ (∫ θ in Work.Spaces.Iθ, X θ * T θ * σ θ)
        ≤ 4 * (∫ θ in Work.Spaces.Iθ, (v2 θ) ^ 2 * σ θ)
          + 7 * (∫ θ in Work.Spaces.Iθ, (v1 θ) ^ 2 * σ θ)
          + 7 * (∫ θ in Work.Spaces.Iθ, (v0 θ) ^ 2 * σ θ)
  -- the three weighted square integrability hypotheses, on `s`
  have hV2s : Integrable (fun θ => (v2 θ) ^ 2 * σ θ) (volume.restrict s) := by
    rw [← hrestrict]; exact hV2
  have hY2s : Integrable (fun θ => (v1 θ) ^ 2 * σ θ) (volume.restrict s) := by
    rw [← hrestrict]; exact hY2
  have hY3s : Integrable (fun θ => (v0 θ) ^ 2 * σ θ) (volume.restrict s) := by
    rw [← hrestrict]; exact hY3
  -- elementary facts on `s`
  have hcos_ne : ∀ θ ∈ s, Real.cos θ ≠ 0 := by
    intro θ hθ
    rw [hs_def] at hθ
    exact ne_of_gt (Real.cos_pos_of_mem_Ioo ⟨by linarith [hθ.1, Real.pi_pos],
      by linarith [hθ.2, Real.pi_pos]⟩)
  have hsinpos : ∀ θ ∈ s, 0 < Real.sin (2 * θ) := by
    intro θ hθ
    rw [hs_def] at hθ
    exact Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])
  have hσ0 : ∀ θ ∈ s, 0 ≤ σ θ := fun θ hθ =>
    Real.rpow_nonneg (le_of_lt (hsinpos θ hθ)) _
  -- regularity
  have htu : ContDiffOn ℝ 3 (fun t => Real.tan t * u t) s := by
    intro θ hθ
    exact ((Real.contDiffAt_tan.mpr (hcos_ne θ hθ)).mul
      (hu.contDiffAt (hsopen.mem_nhds hθ))).contDiffWithinAt
  have hv0C : ContDiffOn ℝ 3 v0 s := hu.div Real.contDiff_cos.contDiffOn hcos_ne
  have hv1C : ContDiffOn ℝ 2 v1 s := hv0C.deriv_of_isOpen hsopen (by norm_num)
  have hv2C : ContDiffOn ℝ 1 v2 s := hv1C.deriv_of_isOpen hsopen (by norm_num)
  have hXC : ContDiffOn ℝ 1 X s := by
    have h1 : ContDiffOn ℝ 2 (deriv (fun t => Real.tan t * u t)) s :=
      htu.deriv_of_isOpen hsopen (by norm_num)
    exact h1.deriv_of_isOpen hsopen (by norm_num)
  -- a.e. strong measurability of the pieces
  have hm0 : AEStronglyMeasurable v0 (volume.restrict s) :=
    hv0C.continuousOn.aestronglyMeasurable hsmeas
  have hm1 : AEStronglyMeasurable v1 (volume.restrict s) :=
    hv1C.continuousOn.aestronglyMeasurable hsmeas
  have hm2 : AEStronglyMeasurable v2 (volume.restrict s) :=
    hv2C.continuousOn.aestronglyMeasurable hsmeas
  have hmX : AEStronglyMeasurable X (volume.restrict s) :=
    hXC.continuousOn.aestronglyMeasurable hsmeas
  have hmsin : AEStronglyMeasurable (fun θ : ℝ => Real.sin θ) (volume.restrict s) :=
    Real.continuous_sin.continuousOn.aestronglyMeasurable hsmeas
  have hmcos : AEStronglyMeasurable (fun θ : ℝ => Real.cos θ) (volume.restrict s) :=
    Real.continuous_cos.continuousOn.aestronglyMeasurable hsmeas
  have hmT : AEStronglyMeasurable T (volume.restrict s) := by
    have h1 : AEStronglyMeasurable (fun θ : ℝ => Real.sin θ * v2 θ) (volume.restrict s) :=
      hmsin.mul hm2
    have h2 : AEStronglyMeasurable (fun θ : ℝ => 4 * Real.cos θ * v1 θ) (volume.restrict s) :=
      (hmcos.const_mul 4).mul hm1
    have h3 : AEStronglyMeasurable (fun θ : ℝ => 5 * Real.sin θ * v0 θ) (volume.restrict s) :=
      (hmsin.const_mul 5).mul hm0
    exact (h1.sub h2).add h3
  have hmσ : AEStronglyMeasurable σ (volume.restrict s) := by
    refine (ContinuousOn.rpow_const ?_ ?_).aestronglyMeasurable hsmeas
    · exact (Real.continuous_sin.comp (continuous_const.mul continuous_id)).continuousOn
    · intro θ hθ
      exact Or.inl (ne_of_gt (hsinpos θ hθ))
  -- the pointwise identity for `X`
  have hXeq : ∀ θ ∈ s, X θ = Real.sin θ * v2 θ + 2 * Real.cos θ * v1 θ - Real.sin θ * v0 θ :=
    fun θ hθ => (slice_v_identities u hu θ (by rw [hs_def] at hθ; exact hθ)).2.2.1
  -- `X·T ≤ 4 (v'')² + 7 (v')² + 7 v²`
  have hQT : ∀ θ ∈ s, X θ * T θ ≤ 4 * (v2 θ) ^ 2 + 7 * (v1 θ) ^ 2 + 7 * (v0 θ) ^ 2 := by
    intro θ hθ
    have hX := hXeq θ hθ
    have hT : T θ = Real.sin θ * v2 θ - 4 * Real.cos θ * v1 θ + 5 * Real.sin θ * v0 θ := rfl
    have hQ := slice_Q_pointwise θ (v2 θ) (v1 θ) (v0 θ)
    rw [hX, hT]
    nlinarith [hQ, Real.sin_sq_le_one θ, sq_nonneg (v2 θ)]
  -- `|X·T| ≤ 3 (v'')² + 30 (v')² + 39 v²`
  have hXT : ∀ θ ∈ s, |X θ * T θ| ≤ 3 * (v2 θ) ^ 2 + 30 * (v1 θ) ^ 2 + 39 * (v0 θ) ^ 2 := by
    intro θ hθ
    have hX := hXeq θ hθ
    have hT : T θ = Real.sin θ * v2 θ - 4 * Real.cos θ * v1 θ + 5 * Real.sin θ * v0 θ := rfl
    rw [hX, hT]
    exact abs_XT_le θ (v2 θ) (v1 θ) (v0 θ)
  -- integrability of `X·T·σ`
  have hdom : Integrable (fun θ => 3 * ((v2 θ) ^ 2 * σ θ) + 30 * ((v1 θ) ^ 2 * σ θ)
      + 39 * ((v0 θ) ^ 2 * σ θ)) (volume.restrict s) :=
    ((hV2s.const_mul 3).add (hY2s.const_mul 30)).add (hY3s.const_mul 39)
  have hmain : Integrable (fun θ => X θ * T θ * σ θ) (volume.restrict s) := by
    refine Integrable.mono' hdom ((hmX.mul hmT).mul hmσ) ?_
    filter_upwards [ae_restrict_mem hsmeas] with θ hθ
    have hσ := hσ0 θ hθ
    have h1 := mul_le_mul_of_nonneg_right (hXT θ hθ) hσ
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hσ]
    calc |X θ * T θ| * σ θ
        ≤ (3 * (v2 θ) ^ 2 + 30 * (v1 θ) ^ 2 + 39 * (v0 θ) ^ 2) * σ θ := h1
      _ = 3 * ((v2 θ) ^ 2 * σ θ) + 30 * ((v1 θ) ^ 2 * σ θ) + 39 * ((v0 θ) ^ 2 * σ θ) := by
          ring
  -- the integral comparison
  have hgint : Integrable (fun θ => 4 * ((v2 θ) ^ 2 * σ θ) + 7 * ((v1 θ) ^ 2 * σ θ)
      + 7 * ((v0 θ) ^ 2 * σ θ)) (volume.restrict s) :=
    ((hV2s.const_mul 4).add (hY2s.const_mul 7)).add (hY3s.const_mul 7)
  have hmono : (∫ θ in s, X θ * T θ * σ θ)
      ≤ ∫ θ in s, 4 * ((v2 θ) ^ 2 * σ θ) + 7 * ((v1 θ) ^ 2 * σ θ)
          + 7 * ((v0 θ) ^ 2 * σ θ) := by
    refine setIntegral_mono_ae_restrict hmain hgint ?_
    filter_upwards [ae_restrict_mem hsmeas] with θ hθ
    have hσ := hσ0 θ hθ
    have h1 := mul_le_mul_of_nonneg_right (hQT θ hθ) hσ
    calc X θ * T θ * σ θ = (X θ * T θ) * σ θ := by ring
      _ ≤ (4 * (v2 θ) ^ 2 + 7 * (v1 θ) ^ 2 + 7 * (v0 θ) ^ 2) * σ θ := h1
      _ = 4 * ((v2 θ) ^ 2 * σ θ) + 7 * ((v1 θ) ^ 2 * σ θ) + 7 * ((v0 θ) ^ 2 * σ θ) := by
          ring
  have hsplit : (∫ θ in s, 4 * ((v2 θ) ^ 2 * σ θ) + 7 * ((v1 θ) ^ 2 * σ θ)
        + 7 * ((v0 θ) ^ 2 * σ θ))
      = 4 * (∫ θ in s, (v2 θ) ^ 2 * σ θ) + 7 * (∫ θ in s, (v1 θ) ^ 2 * σ θ)
        + 7 * (∫ θ in s, (v0 θ) ^ 2 * σ θ) :=
    setIntegral_three s hV2s hY2s hY3s 4 7 7
  refine ⟨?_, ?_⟩
  · rw [MeasureTheory.IntegrableOn, hrestrict]
    exact hmain
  · rw [hrestrict]
    exact le_trans hmono (le_of_eq hsplit)

end Work.FTS.EllipticEst.remov.Step4
end
end
-- ===== merged: Submission.Work.FTS.EllipticEst.remov.Step4.slice_Xt_sq_bound =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.remov.Step4

set_option autoImplicit false
set_option maxHeartbeats 1000000

/-! ### Continuity of `(tan θ·u)''` on the open angular interval

`u` is `C³` on `(0, π/2)` and `tan` is smooth there (`cos θ > 0`), so `θ ↦ tan θ · u θ` is
`C²`, whence `(tan θ·u)''` is continuous.  This supplies the a.e. strong measurability of the
left-hand side of the estimate. -/
private lemma contDiffOn_Xt_second {u : ℝ → ℝ}
    (hu : ContDiffOn ℝ 3 u (Set.Ioo 0 (Real.pi / 2))) :
    ContDiffOn ℝ 0 (fun θ => deriv (deriv (fun t => Real.tan t * u t)) θ)
      (Set.Ioo 0 (Real.pi / 2)) := by
  have hI : IsOpen (Set.Ioo (0 : ℝ) (Real.pi / 2)) := isOpen_Ioo
  have htu : ContDiffOn ℝ 2 (fun t => Real.tan t * u t) (Set.Ioo 0 (Real.pi / 2)) := by
    intro θ hθ
    have hcos : Real.cos θ ≠ 0 :=
      ne_of_gt (Real.cos_pos_of_mem_Ioo ⟨by linarith [hθ.1, Real.pi_pos],
        by linarith [hθ.2, Real.pi_pos]⟩)
    exact ((Real.contDiffAt_tan.mpr hcos).mul
      ((hu.contDiffAt (hI.mem_nhds hθ)).of_le (by norm_num))).contDiffWithinAt
  have h1 : ContDiffOn ℝ 1 (deriv (fun t => Real.tan t * u t)) (Set.Ioo 0 (Real.pi / 2)) :=
    htu.deriv_of_isOpen hI (by norm_num)
  exact h1.deriv_of_isOpen hI (by norm_num)

/-
# Step 4 (Elgindi §H2, tex 931-953): the weighted square bound for `(tan θ·u)''`

Writing `v = u / cos θ`, `X = (tan θ·u)''` and `σ = sin(2θ)^{2-γ}` on `Iθ = [0, π/2]`, this
proves `∫ X² σ ≤ 3 (∫ (v'')²σ + 4 ∫ (v')²σ + ∫ v²σ)`, together with the integrability of
`X²σ` that goes with it.

Route: `Work.FTS.EllipticEst.remov.slice_v_identities` gives, for `θ ∈ (0, π/2)`,
`(tan θ·u)''θ = sin θ·v''θ + 2 cos θ·v'θ - sin θ·vθ`, so pointwise on `(0, π/2)`
`X² ≤ 3((v'')² + 4(v')² + v²)` (Cauchy–Schwarz `(a+b+c)² ≤ 3(a²+b²+c²)` and `sin²θ,cos²θ ≤ 1`).
Then bound `∫ X²σ` by the integral of an integrable function and compare
(`MeasureTheory.setIntegral_mono_ae_restrict`), using
`volume.restrict Iθ = volume.restrict (0, π/2)` to pass the pointwise facts from `(0,π/2)` to
`Iθ`, and continuity of `v, v', v'', X` on `(0,π/2)` for the strong measurability.
-/
theorem slice_Xt_sq_bound (γ : ℝ) {u : ℝ → ℝ}
    (hu : ContDiffOn ℝ 3 u (Set.Ioo 0 (Real.pi / 2)))
    (hV2 : MeasureTheory.IntegrableOn (fun θ =>
        (deriv (fun t => deriv (fun s => u s / Real.cos s) t) θ) ^ 2 *
        Real.rpow (Real.sin (2 * θ)) (2 - γ)) Work.Spaces.Iθ)
    (hY2 : MeasureTheory.IntegrableOn (fun θ =>
        (deriv (fun t => u t / Real.cos t) θ) ^ 2 *
        Real.rpow (Real.sin (2 * θ)) (2 - γ)) Work.Spaces.Iθ)
    (hY3 : MeasureTheory.IntegrableOn (fun θ =>
        (u θ / Real.cos θ) ^ 2 *
        Real.rpow (Real.sin (2 * θ)) (2 - γ)) Work.Spaces.Iθ) :
    MeasureTheory.IntegrableOn (fun θ =>
        (deriv (deriv (fun t => Real.tan t * u t)) θ) ^ 2 *
        Real.rpow (Real.sin (2 * θ)) (2 - γ)) Work.Spaces.Iθ
      ∧ (∫ θ in Work.Spaces.Iθ,
          (deriv (deriv (fun t => Real.tan t * u t)) θ) ^ 2 *
          Real.rpow (Real.sin (2 * θ)) (2 - γ))
        ≤ 3 * ((∫ θ in Work.Spaces.Iθ,
                (deriv (fun t => deriv (fun s => u s / Real.cos s) t) θ) ^ 2 *
                Real.rpow (Real.sin (2 * θ)) (2 - γ))
            + 4 * (∫ θ in Work.Spaces.Iθ,
                (deriv (fun t => u t / Real.cos t) θ) ^ 2 *
                Real.rpow (Real.sin (2 * θ)) (2 - γ))
            + (∫ θ in Work.Spaces.Iθ, (u θ / Real.cos θ) ^ 2 *
                Real.rpow (Real.sin (2 * θ)) (2 - γ))) := by
  set S : Set ℝ := Set.Ioo 0 (Real.pi / 2) with hSdef
  set σ : ℝ → ℝ := fun θ => Real.rpow (Real.sin (2 * θ)) (2 - γ) with hσdef
  set X : ℝ → ℝ := fun θ => deriv (deriv (fun t => Real.tan t * u t)) θ with hXdef
  set A : ℝ → ℝ := fun θ => deriv (fun t => deriv (fun s => u s / Real.cos s) t) θ with hAdef
  set B : ℝ → ℝ := fun θ => deriv (fun t => u t / Real.cos t) θ with hBdef
  set C : ℝ → ℝ := fun θ => u θ / Real.cos θ with hCdef
  have hSmeas : MeasurableSet S := by rw [hSdef]; exact measurableSet_Ioo
  have hset : (Work.Spaces.Iθ : Set ℝ) =ᵐ[volume] S := by
    simp only [Work.Spaces.Iθ, hSdef]
    exact (MeasureTheory.Ioo_ae_eq_Icc (a := (0 : ℝ)) (b := Real.pi / 2)).symm
  have hrestrict : (volume.restrict Work.Spaces.Iθ : Measure ℝ) = volume.restrict S :=
    Measure.restrict_congr_set hset
  have hmem : ∀ θ ∈ S, θ ∈ Set.Ioo 0 (Real.pi / 2) := by
    intro θ hθ
    rwa [hSdef] at hθ
  -- the pointwise identity of `slice_v_identities`
  have hrel : ∀ θ ∈ S, X θ = Real.sin θ * A θ + 2 * Real.cos θ * B θ - Real.sin θ * C θ := by
    intro θ hθ
    have h := (slice_v_identities u hu θ (hmem θ hθ)).2.2.1
    simp only [hXdef, hAdef, hBdef, hCdef]
    exact h
  have hσ0 : ∀ θ ∈ S, 0 ≤ σ θ := by
    intro θ hθ
    have hsin : 0 < Real.sin (2 * θ) :=
      Real.sin_pos_of_pos_of_lt_pi (by linarith [(hmem θ hθ).1])
        (by linarith [(hmem θ hθ).2, Real.pi_pos])
    simp only [hσdef]
    exact Real.rpow_nonneg hsin.le _
  have hσm : AEStronglyMeasurable σ (volume.restrict S) := by
    rw [hσdef]
    exact (by measurability : Measurable
      (fun θ : ℝ => Real.rpow (Real.sin (2 * θ)) (2 - γ))).aestronglyMeasurable
  have hXcont : ContinuousOn X S := by
    rw [hXdef, hSdef]
    exact (contDiffOn_Xt_second hu).continuousOn
  have hXm : AEStronglyMeasurable X (volume.restrict S) :=
    hXcont.aestronglyMeasurable hSmeas
  have hA : IntegrableOn (fun θ => (A θ) ^ 2 * σ θ) S := by
    show MeasureTheory.Integrable _ (volume.restrict S)
    rw [← hrestrict]
    rw [hAdef, hσdef]
    exact hV2
  have hB : IntegrableOn (fun θ => (B θ) ^ 2 * σ θ) S := by
    show MeasureTheory.Integrable _ (volume.restrict S)
    rw [← hrestrict]
    rw [hBdef, hσdef]
    exact hY2
  have hC : IntegrableOn (fun θ => (C θ) ^ 2 * σ θ) S := by
    show MeasureTheory.Integrable _ (volume.restrict S)
    rw [← hrestrict]
    rw [hCdef, hσdef]
    exact hY3
  obtain ⟨hInt, hineq⟩ :=
    integrableOn_sq_sin_cos_rel (s := S) (σ := σ) (X := X) (A := A) (B := B) (C := C)
      hσ0 hrel hXm hσm hA hB hC
  refine ⟨?_, ?_⟩
  · show MeasureTheory.Integrable _ (volume.restrict Work.Spaces.Iθ)
    rw [hrestrict]
    exact hInt
  · rw [MeasureTheory.setIntegral_congr_set hset, MeasureTheory.setIntegral_congr_set hset,
      MeasureTheory.setIntegral_congr_set hset, MeasureTheory.setIntegral_congr_set hset]
    simpa only [hXdef, hσdef, hAdef, hBdef, hCdef] using hineq

end Work.FTS.EllipticEst.remov.Step4
end
end
-- ===== merged: Submission.Work.FTS.EllipticEst.remov.TopCoreB.FarGDefs =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# Reflected-variable toolkit for the `g`-slot finiteness on the far window

The far window `farSet = [3π/8, π/2]` of the angular estimate is mapped to `[0, π/8]` by
`x ↦ π/2 - x`.  In the reflected variable `x`

* `gsqU u x = u (π/2 - x)` (the reflected solution slice),
* `gsqG g x = g (π/2 - x)` (the reflected source slice),
* `gsqSec x = x / sin x`, `gsqKap x = gsqSec x * cos x = x * cot x` (smooth bounded quotient),
* `gsqW u x = gsqU u x / x` (the *divided* reflected slice),

so that in the reflected variable the pointwise angular identity `g = -u'' + (tan θ·u)' - 6u`
reads

`gsqG g = -(gsqU u)'' - (gsqKap · gsqW u)' - 6 · gsqU u`,

and the derivative of the product `gsqKap · gsqW u` is controlled by the divided derivatives
`gsqW u^{(j)}` with the *bounded* coefficients `gsqKap^{(i)}`.

This file contains only the definitions and the elementary reflected-variable facts
(substitution, integrability transfer by the measure-preserving reflection, the pointwise
integrand identity, the weight comparisons and the two smoothness/limit inputs for the
division lemmas).
-/

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.remov.TopCoreB

set_option autoImplicit false
set_option maxHeartbeats 1000000

/-! ## The reflected window -/








/-! ## The reflected functions -/








/-! ## The reflection and the iterated derivative -/






/-! ## Substitution and integrability transfer -/










/-! ## Weight comparisons on the reflected window -/






/-! ## Smoothness and the limit at `0⁺` of the reflected slice -/




end Work.FTS.EllipticEst.remov.TopCoreB
end
end
-- ===== merged: Submission.Work.FTS.EllipticEst.remov.TopCoreB.FarSlots =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# Elementary consequences of `FarHyp`: the `u`-slots are dominated by `FarR`

For every `j ≤ k+1` the far-window integral of the `j`-th `u`-slot against the *top* weight
`qW k γ` is bounded by `FarR k γ u g`: this is a monotone comparison between `rpow`s, plus the
observation that every summand of `FarR` is nonnegative.
-/

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.remov.TopCoreB

set_option autoImplicit false

theorem sin_two_nonneg_Iθ {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) : 0 ≤ Real.sin (2 * θ) :=
  Real.sin_nonneg_of_mem_Icc ⟨by linarith [hθ.1, Real.pi_pos], by
    linarith [hθ.2, Real.pi_pos]⟩

/-- The top weight is nonnegative on `Iθ`. -/
theorem qW_nonneg {k : ℕ} {γ θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) : 0 ≤ qW k γ θ :=
  Real.rpow_nonneg (sin_two_nonneg_Iθ hθ) _

/-- The `j`-th slot weight `sin(2θ)^{2j-4-γ}` is nonnegative on `Iθ`. -/
theorem slotWeight_nonneg {j : ℕ} {γ θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) :
    0 ≤ Real.rpow (Real.sin (2 * θ)) (2 * (j : ℝ) - 4 - γ) :=
  Real.rpow_nonneg (sin_two_nonneg_Iθ hθ) _






/-- Every summand of `FarR` is nonnegative. -/
theorem FarR_nonneg {k : ℕ} (hk : 2 ≤ k) {γ : ℝ} {u g : ℝ → ℝ} (h : FarHyp k γ u g) :
    0 ≤ FarR k γ u g := by
  have h2 : 0 ≤ ∫ θ in Work.Spaces.Iθ, (iteratedDeriv k g θ) ^ 2
      * Real.rpow (Real.sin (2 * θ)) (2 * (k : ℝ) - γ) :=
    MeasureTheory.setIntegral_nonneg measurableSet_Icc
      (fun θ hθ => mul_nonneg (sq_nonneg _)
        (Real.rpow_nonneg (sin_two_nonneg_Iθ hθ) _))
  have h3 : 0 ≤ ∑ j ∈ Finset.Icc 3 (k + 1), ∫ θ in Work.Spaces.Iθ,
      (iteratedDeriv j u θ) ^ 2 * Real.rpow (Real.sin (2 * θ)) (2 * (j : ℝ) - 4 - γ) :=
    Finset.sum_nonneg (fun j _ => MeasureTheory.setIntegral_nonneg measurableSet_Icc
      (fun θ hθ => mul_nonneg (sq_nonneg _) (slotWeight_nonneg hθ)))
  have h4 : 0 ≤ ∫ θ in Work.Spaces.Iθ, (deriv (deriv u) θ) ^ 2
      * Real.rpow (Real.sin (2 * θ)) (-(Work.Spaces.eta)) :=
    MeasureTheory.setIntegral_nonneg measurableSet_Icc
      (fun θ hθ => mul_nonneg (sq_nonneg _)
        (Real.rpow_nonneg (sin_two_nonneg_Iθ hθ) _))
  have h5 : 0 ≤ ∫ θ in Work.Spaces.Iθ, (deriv u θ) ^ 2 :=
    MeasureTheory.setIntegral_nonneg measurableSet_Icc (fun θ _ => sq_nonneg _)
  have h6 : 0 ≤ ∫ θ in Work.Spaces.Iθ, (u θ) ^ 2 :=
    MeasureTheory.setIntegral_nonneg measurableSet_Icc (fun θ _ => sq_nonneg _)
  simp only [FarR]
  linarith


end Work.FTS.EllipticEst.remov.TopCoreB
end
end
-- ===== merged: Submission.Work.FTS.EllipticEst.remov.ibpZZ =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.remov

open MeasureTheory Set Filter
open scoped Topology

theorem ibpZZ (σ φ : ℝ → ℝ) (hσ : ContDiffOn ℝ 2 σ (Set.Ioi 0)) (hφ : ContDiffOn ℝ 2 φ (Set.Ioi 0)) (hi1 : MeasureTheory.IntegrableOn (fun z => z ^ 2 * σ z * φ z * deriv (deriv φ) z) (Set.Ioi 0)) (hi2 : MeasureTheory.IntegrableOn (fun z => deriv (fun z => z ^ 2 * σ z) z * φ z * deriv φ z) (Set.Ioi 0)) (hi3 : MeasureTheory.IntegrableOn (fun z => σ z * (z * deriv φ z) ^ 2) (Set.Ioi 0)) (hi4 : MeasureTheory.IntegrableOn (fun z => deriv (deriv (fun z => z ^ 2 * σ z)) z * (φ z) ^ 2) (Set.Ioi 0)) (h0 : Filter.Tendsto (fun z => z ^ 2 * σ z * φ z * deriv φ z) (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0)) (hT : Filter.Tendsto (fun z => z ^ 2 * σ z * φ z * deriv φ z) Filter.atTop (nhds 0)) (hb0 : Filter.Tendsto (fun z => deriv (fun z => z ^ 2 * σ z) z * (φ z) ^ 2) (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0)) (hbT : Filter.Tendsto (fun z => deriv (fun z => z ^ 2 * σ z) z * (φ z) ^ 2) Filter.atTop (nhds 0)) : (∫ z in Set.Ioi 0, σ z * z ^ 2 * deriv (deriv φ) z * φ z) = (1 / 2) * (∫ z in Set.Ioi 0, deriv (deriv (fun z => z ^ 2 * σ z)) z * (φ z) ^ 2) - (∫ z in Set.Ioi 0, σ z * (z * deriv φ z) ^ 2) := by
  -- ### Differentiability of the weight `w = z²σ` and of `φ`
  have hw2 : ContDiffOn ℝ 2 (fun z : ℝ => z ^ 2 * σ z) (Set.Ioi 0) :=
    ContDiffOn.mul (by fun_prop) hσ
  have hw1 : ContDiffOn ℝ 1 (deriv (fun z : ℝ => z ^ 2 * σ z)) (Set.Ioi 0) :=
    hw2.deriv_of_isOpen isOpen_Ioi (by norm_num)
  have hF : ∀ z ∈ Set.Ioi (0 : ℝ),
      HasDerivAt (fun z : ℝ => z ^ 2 * σ z) (deriv (fun z : ℝ => z ^ 2 * σ z) z) z := by
    intro z hz
    exact (hw2.differentiableOn (by norm_num)).hasDerivAt (isOpen_Ioi.mem_nhds hz)
  have hF' : ∀ z ∈ Set.Ioi (0 : ℝ),
      HasDerivAt (deriv (fun z : ℝ => z ^ 2 * σ z))
        (deriv (deriv (fun z : ℝ => z ^ 2 * σ z)) z) z := by
    intro z hz
    exact (hw1.differentiableOn (by norm_num)).hasDerivAt (isOpen_Ioi.mem_nhds hz)
  have hφd : ∀ z ∈ Set.Ioi (0 : ℝ), HasDerivAt φ (deriv φ z) z := by
    intro z hz
    exact (hφ.differentiableOn (by norm_num)).hasDerivAt (isOpen_Ioi.mem_nhds hz)
  have hφd' : ∀ z ∈ Set.Ioi (0 : ℝ), HasDerivAt (deriv φ) (deriv (deriv φ) z) z := by
    have h1 : ContDiffOn ℝ 1 (deriv φ) (Set.Ioi 0) := hφ.deriv_of_isOpen isOpen_Ioi (by norm_num)
    intro z hz
    exact (h1.differentiableOn (by norm_num)).hasDerivAt (isOpen_Ioi.mem_nhds hz)
  have hH : ∀ z ∈ Set.Ioi (0 : ℝ), HasDerivAt (fun z => (φ z) ^ 2) (2 * φ z * deriv φ z) z := by
    intro z hz
    convert (hφd z hz).pow 2 using 1
    simp [pow_one, mul_assoc]
  have hH' : ∀ z ∈ Set.Ioi (0 : ℝ),
      HasDerivAt (fun z => 2 * φ z * deriv φ z)
        (2 * (deriv φ z * deriv φ z + φ z * deriv (deriv φ) z)) z := by
    intro z hz
    convert ((hφd z hz).mul (hφd' z hz)).const_mul 2 using 1; simp [mul_assoc]
  -- ### Integrability and boundary conditions
  have hI1 : IntegrableOn
      (fun z => (z ^ 2 * σ z) * (2 * (deriv φ z * deriv φ z + φ z * deriv (deriv φ) z)))
      (Set.Ioi 0) := by
    have hA : IntegrableOn (fun z => 2 * (σ z * (z * deriv φ z) ^ 2)) (Set.Ioi 0) := hi3.const_mul 2
    have hB : IntegrableOn (fun z => 2 * (z ^ 2 * σ z * φ z * deriv (deriv φ) z)) (Set.Ioi 0) :=
      hi1.const_mul 2
    refine (hA.add hB).congr_fun ?_ measurableSet_Ioi
    intro z _
    simp only [Pi.add_apply]; ring
  have hI2 : IntegrableOn (fun z => deriv (fun z => z ^ 2 * σ z) z * (2 * φ z * deriv φ z))
      (Set.Ioi 0) := by
    have hB : IntegrableOn (fun z => 2 * (deriv (fun z => z ^ 2 * σ z) z * φ z * deriv φ z))
        (Set.Ioi 0) := hi2.const_mul 2
    refine hB.congr_fun ?_ measurableSet_Ioi
    intro z _
    ring
  have h0' : Tendsto (fun z => 2 * (z ^ 2 * σ z * φ z * deriv φ z))
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) := by
    simpa using h0.const_mul 2
  have hT' : Tendsto (fun z => 2 * (z ^ 2 * σ z * φ z * deriv φ z)) atTop (nhds 0) := by
    simpa using hT.const_mul 2
  have hb1 : Tendsto (fun z => (fun z : ℝ => z ^ 2 * σ z) z * (fun z : ℝ => 2 * φ z * deriv φ z) z)
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) :=
    h0'.congr' (Eventually.of_forall (fun z => by ring))
  have hb2 : Tendsto (fun z => (fun z : ℝ => z ^ 2 * σ z) z * (fun z : ℝ => 2 * φ z * deriv φ z) z)
      atTop (nhds 0) :=
    hT'.congr' (Eventually.of_forall (fun z => by ring))
  -- ### The integration by parts `∫ w·(φ²)'' = ∫ w''·φ²`
  obtain ⟨e1, _⟩ := Work.FTS.EllipticEst.moment_ibp
      (fun z : ℝ => z ^ 2 * σ z) (deriv (fun z : ℝ => z ^ 2 * σ z))
      (deriv (deriv (fun z : ℝ => z ^ 2 * σ z)))
      (fun _ : ℝ => (0 : ℝ)) (fun _ : ℝ => (0 : ℝ))
      (fun z : ℝ => (φ z) ^ 2) (fun z : ℝ => 2 * φ z * deriv φ z)
      (fun z : ℝ => 2 * (deriv φ z * deriv φ z + φ z * deriv (deriv φ) z))
      hF hF' (fun z _ => by simpa using hasDerivAt_const (c := (0 : ℝ)) z)
      hH hH' hI1 hI2 hi4 (by simp) (by simp)
      hb1 hb2 hb0 hbT (by simp) (by simp)
  have hkey : (∫ z in Set.Ioi 0,
        (z ^ 2 * σ z) * (2 * (deriv φ z * deriv φ z + φ z * deriv (deriv φ) z)))
      = ∫ z in Set.Ioi 0, deriv (deriv (fun z : ℝ => z ^ 2 * σ z)) z * (φ z) ^ 2 := by
    simpa only [] using e1
  -- ### Splitting the left-hand side of the identity into the two pieces of the statement
  have hA : IntegrableOn (fun z => 2 * (σ z * (z * deriv φ z) ^ 2)) (Set.Ioi 0) := hi3.const_mul 2
  have hB : IntegrableOn (fun z => 2 * (z ^ 2 * σ z * φ z * deriv (deriv φ) z)) (Set.Ioi 0) :=
    hi1.const_mul 2
  have hfun : (∫ z in Set.Ioi 0,
        (z ^ 2 * σ z) * (2 * (deriv φ z * deriv φ z + φ z * deriv (deriv φ) z)))
      = ∫ z in Set.Ioi 0,
          2 * (σ z * (z * deriv φ z) ^ 2) + 2 * (z ^ 2 * σ z * φ z * deriv (deriv φ) z) :=
    setIntegral_congr_fun measurableSet_Ioi (fun z _ => by ring)
  have hsplit : (∫ z in Set.Ioi 0,
        2 * (σ z * (z * deriv φ z) ^ 2) + 2 * (z ^ 2 * σ z * φ z * deriv (deriv φ) z))
      = 2 * (∫ z in Set.Ioi 0, σ z * (z * deriv φ z) ^ 2)
        + 2 * (∫ z in Set.Ioi 0, z ^ 2 * σ z * φ z * deriv (deriv φ) z) := by
    rw [integral_add hA hB, integral_const_mul, integral_const_mul]
  have hsum : 2 * (∫ z in Set.Ioi 0, σ z * (z * deriv φ z) ^ 2)
        + 2 * (∫ z in Set.Ioi 0, z ^ 2 * σ z * φ z * deriv (deriv φ) z)
      = ∫ z in Set.Ioi 0, deriv (deriv (fun z : ℝ => z ^ 2 * σ z)) z * (φ z) ^ 2 :=
    hsplit.symm.trans (hfun.symm.trans hkey)
  -- ### Conclusion
  have htarget : (∫ z in Set.Ioi 0, σ z * z ^ 2 * deriv (deriv φ) z * φ z)
      = ∫ z in Set.Ioi 0, z ^ 2 * σ z * φ z * deriv (deriv φ) z :=
    setIntegral_congr_fun measurableSet_Ioi (fun z _ => by ring)
  rw [htarget]
  linarith [hsum]

end Work.FTS.EllipticEst.remov
end
-- ===== merged: Submission.Work.FTS.EllipticEst.remov.slice5_rel =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.remov

set_option autoImplicit false



lemma cos_pos_of_mem_Ioo {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) : 0 < Real.cos θ :=
  Real.cos_pos_of_mem_Ioo
    ⟨by linarith [hθ.1, Real.pi_pos], by linarith [hθ.2, Real.pi_pos]⟩

/-- `cos θ * (u θ / cos θ) = u θ` on `(0, π/2)`. -/
lemma cos_mul_cbV {u : ℝ → ℝ} {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    Real.cos θ * (u θ / Real.cos θ) = u θ := by
  field_simp [(cos_pos_of_mem_Ioo hθ).ne']

/-- `(cos θ · v)' = -sin θ · v + cos θ · v'`, i.e. `u' = -S v + C v'`. -/
lemma slice5_v_rel_one (u : ℝ → ℝ) (hu : ContDiffOn ℝ 4 u (Set.Ioo 0 (Real.pi / 2))) :
    ∀ θ ∈ Set.Ioo 0 (Real.pi / 2),
      deriv u θ
        = -Real.sin θ * (u θ / Real.cos θ)
          + Real.cos θ * deriv (fun θ' => u θ' / Real.cos θ') θ := by
  intro θ hθ
  have hIoo : Set.Ioo (0 : ℝ) (Real.pi / 2) ∈ 𝓝 θ := isOpen_Ioo.mem_nhds hθ
  have hcos_ne : ∀ t ∈ Set.Ioo (0 : ℝ) (Real.pi / 2), Real.cos t ≠ 0 :=
    fun t ht => (cos_pos_of_mem_Ioo ht).ne'
  have hψC : ContDiffOn ℝ 4 (fun θ' => u θ' / Real.cos θ') (Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
    hu.div Real.contDiff_cos.contDiffOn hcos_ne
  have hV : HasDerivAt (fun θ' => u θ' / Real.cos θ')
      (deriv (fun θ' => u θ' / Real.cos θ') θ) θ :=
    ((hψC.contDiffAt hIoo).differentiableAt (by norm_num)).hasDerivAt
  have hev : u =ᶠ[𝓝 θ] fun t => Real.cos t * (u t / Real.cos t) := by
    filter_upwards [hIoo] with t ht
    exact (cos_mul_cbV ht).symm
  have hd : HasDerivAt (fun t => Real.cos t * (u t / Real.cos t))
      (-Real.sin θ * (u θ / Real.cos θ) + Real.cos θ * deriv (fun θ' => u θ' / Real.cos θ') θ) θ :=
    (Real.hasDerivAt_cos θ).mul hV
  rw [hev.deriv_eq, hd.deriv]

/-- `sin θ · v = tan θ · u`. -/
lemma slice5_v_rel_tan (u : ℝ → ℝ) {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    Real.sin θ * (u θ / Real.cos θ) = Real.tan θ * u θ := by
  have hcos : Real.cos θ ≠ 0 := (cos_pos_of_mem_Ioo hθ).ne'
  simp only [Real.tan_eq_sin_div_cos]
  field_simp

/-- **Pure-algebra expansions.**  On `(0, π/2)`, `u = cos θ · v` with `v = u / cos θ`,
so the second, third and fourth derivatives of `u` are the corresponding Leibniz
combinations of `cos` and `v`. -/
theorem slice5_v_rel_pure (u : ℝ → ℝ) (hu : ContDiffOn ℝ 4 u (Set.Ioo 0 (Real.pi / 2))) :
    ∀ θ ∈ Set.Ioo 0 (Real.pi / 2),
      (deriv (deriv u) θ
          = -Real.cos θ * (u θ / Real.cos θ)
            - 2 * Real.sin θ * deriv (fun θ' => u θ' / Real.cos θ') θ
            + Real.cos θ * deriv (deriv (fun θ' => u θ' / Real.cos θ')) θ) ∧
      (deriv (deriv (deriv u)) θ
          = Real.sin θ * (u θ / Real.cos θ)
            - 3 * Real.cos θ * deriv (fun θ' => u θ' / Real.cos θ') θ
            - 3 * Real.sin θ * deriv (deriv (fun θ' => u θ' / Real.cos θ')) θ
            + Real.cos θ * deriv (deriv (deriv (fun θ' => u θ' / Real.cos θ'))) θ) ∧
      (deriv (deriv (deriv (deriv u))) θ
          = Real.cos θ * (u θ / Real.cos θ)
            + 4 * Real.sin θ * deriv (fun θ' => u θ' / Real.cos θ') θ
            - 6 * Real.cos θ * deriv (deriv (fun θ' => u θ' / Real.cos θ')) θ
            - 4 * Real.sin θ * deriv (deriv (deriv (fun θ' => u θ' / Real.cos θ'))) θ
            + Real.cos θ * deriv (deriv (deriv (deriv (fun θ' => u θ' / Real.cos θ')))) θ) := by
  intro θ hθ
  have hIoo : Set.Ioo (0 : ℝ) (Real.pi / 2) ∈ 𝓝 θ := isOpen_Ioo.mem_nhds hθ
  have hcos_ne : ∀ t ∈ Set.Ioo (0 : ℝ) (Real.pi / 2), Real.cos t ≠ 0 :=
    fun t ht => (cos_pos_of_mem_Ioo ht).ne'
  set ψ : ℝ → ℝ := fun θ' => u θ' / Real.cos θ' with hψ
  have hψC : ContDiffOn ℝ 4 ψ (Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
    hu.div Real.contDiff_cos.contDiffOn hcos_ne
  have hψAt : ContDiffAt ℝ 4 ψ θ := hψC.contDiffAt hIoo
  have hev : u =ᶠ[𝓝 θ] fun t => Real.cos t * ψ t := by
    filter_upwards [hIoo] with t ht
    exact (cos_mul_cbV ht).symm
  have h2 : iteratedDeriv 2 u θ
      = -Real.cos θ * ψ θ - 2 * Real.sin θ * iteratedDeriv 1 ψ θ
        + Real.cos θ * iteratedDeriv 2 ψ θ := by
    rw [hev.iteratedDeriv_eq 2]
    exact itd_cos_two ψ θ (hψAt.of_le (by norm_num))
  have h3 : iteratedDeriv 3 u θ
      = Real.sin θ * ψ θ - 3 * Real.cos θ * iteratedDeriv 1 ψ θ
        - 3 * Real.sin θ * iteratedDeriv 2 ψ θ
        + Real.cos θ * iteratedDeriv 3 ψ θ := by
    rw [hev.iteratedDeriv_eq 3]
    exact itd_cos_three ψ θ (hψAt.of_le (by norm_num))
  have h4 : iteratedDeriv 4 u θ
      = Real.cos θ * ψ θ + 4 * Real.sin θ * iteratedDeriv 1 ψ θ
        - 6 * Real.cos θ * iteratedDeriv 2 ψ θ
        - 4 * Real.sin θ * iteratedDeriv 3 ψ θ
        + Real.cos θ * iteratedDeriv 4 ψ θ := by
    rw [hev.iteratedDeriv_eq 4]
    exact itd_cos_four ψ θ hψAt
  refine ⟨?_, ?_, ?_⟩
  · rw [← itd_two_val u θ, h2, iteratedDeriv_one, itd_two_val ψ θ]
  · rw [← itd_three_val u θ, h3, iteratedDeriv_one, itd_two_val ψ θ, itd_three_val ψ θ]
  · rw [← itd_four_val u θ, h4, iteratedDeriv_one, itd_two_val ψ θ, itd_three_val ψ θ,
      itd_four_val ψ θ]

/-- The full set of `u`-`v` relations used by the Step-5 computation. -/
theorem slice5_v_rel (u g : ℝ → ℝ)
    (hu : ContDiffOn ℝ 4 u (Set.Ioo 0 (Real.pi / 2)))
    (hode : ∀ θ ∈ Set.Ioo 0 (Real.pi / 2), Work.FTS.EllipticEst.Lzero1 u θ = g θ) :
    ∀ θ ∈ Set.Ioo 0 (Real.pi / 2),
      (deriv u θ = -Real.sin θ * (u θ / Real.cos θ)
          + Real.cos θ * deriv (fun θ' => u θ' / Real.cos θ') θ) ∧
      (Real.sin θ * (u θ / Real.cos θ) = Real.tan θ * u θ) ∧
      (Real.sin θ * deriv (fun θ' => u θ' / Real.cos θ') θ
        = deriv (deriv u) θ + 5 * u θ + g θ) ∧
      (Real.sin θ * deriv (deriv (fun θ' => u θ' / Real.cos θ')) θ
        = deriv (deriv (deriv u)) θ
          + 4 * Real.cos θ * deriv (fun θ' => u θ' / Real.cos θ') θ
          - 5 * Real.sin θ * (u θ / Real.cos θ) + deriv g θ) ∧
      (Real.cos θ * deriv (deriv (fun θ' => u θ' / Real.cos θ')) θ
        = deriv (deriv u) θ + u θ
          + 2 * Real.sin θ * deriv (fun θ' => u θ' / Real.cos θ') θ) ∧
      (Real.cos θ * deriv (deriv (fun θ' => u θ' / Real.cos θ')) θ
        = 3 * deriv (deriv u) θ + 11 * u θ + 2 * g θ) ∧
      (Real.cos θ * deriv (deriv (deriv (fun θ' => u θ' / Real.cos θ'))) θ
        = deriv (deriv (deriv u)) θ - Real.sin θ * (u θ / Real.cos θ)
          + 3 * Real.cos θ * deriv (fun θ' => u θ' / Real.cos θ') θ
          + 3 * Real.sin θ * deriv (deriv (fun θ' => u θ' / Real.cos θ')) θ) ∧
      (Real.cos θ * deriv (deriv (deriv (fun θ' => u θ' / Real.cos θ'))) θ
        = 4 * deriv (deriv (deriv u)) θ
          + 15 * Real.cos θ * deriv (fun θ' => u θ' / Real.cos θ') θ
          - 16 * Real.sin θ * (u θ / Real.cos θ) + 3 * deriv g θ) ∧
      (Real.cos θ * deriv (deriv (deriv (fun θ' => u θ' / Real.cos θ'))) θ
        = 4 * deriv (deriv (deriv u)) θ + 15 * deriv u θ
          - Real.sin θ * (u θ / Real.cos θ) + 3 * deriv g θ) := by
  intro θ hθ
  have hid := slice5_idents u g hu hode
  have hrel := slice5_v_rel_pure u hu θ hθ
  have hone := slice5_v_rel_one u hu θ hθ
  have htan := slice5_v_rel_tan u hθ
  have hCV : Real.cos θ * (u θ / Real.cos θ) = u θ := cos_mul_cbV hθ
  have h1 := hid.2.1 θ hθ
  have h2 := hid.2.2.1 θ hθ
  have hp2 := hrel.1
  have hp3 := hrel.2.1
  have hS1 : Real.sin θ * deriv (fun θ' => u θ' / Real.cos θ') θ
      = deriv (deriv u) θ + 5 * u θ + g θ := by
    linear_combination -h1 + 5 * hCV
  have hS2 : Real.sin θ * deriv (deriv (fun θ' => u θ' / Real.cos θ')) θ
      = deriv (deriv (deriv u)) θ
        + 4 * Real.cos θ * deriv (fun θ' => u θ' / Real.cos θ') θ
        - 5 * Real.sin θ * (u θ / Real.cos θ) + deriv g θ := by
    linear_combination -h2
  have hC2 : Real.cos θ * deriv (deriv (fun θ' => u θ' / Real.cos θ')) θ
      = deriv (deriv u) θ + u θ
        + 2 * Real.sin θ * deriv (fun θ' => u θ' / Real.cos θ') θ := by
    linear_combination -hp2 + hCV
  have hC2' : Real.cos θ * deriv (deriv (fun θ' => u θ' / Real.cos θ')) θ
      = 3 * deriv (deriv u) θ + 11 * u θ + 2 * g θ := by
    linear_combination hC2 + 2 * hS1
  have hC3 : Real.cos θ * deriv (deriv (deriv (fun θ' => u θ' / Real.cos θ'))) θ
      = deriv (deriv (deriv u)) θ - Real.sin θ * (u θ / Real.cos θ)
        + 3 * Real.cos θ * deriv (fun θ' => u θ' / Real.cos θ') θ
        + 3 * Real.sin θ * deriv (deriv (fun θ' => u θ' / Real.cos θ')) θ := by
    linear_combination -hp3
  have hC3' : Real.cos θ * deriv (deriv (deriv (fun θ' => u θ' / Real.cos θ'))) θ
      = 4 * deriv (deriv (deriv u)) θ
        + 15 * Real.cos θ * deriv (fun θ' => u θ' / Real.cos θ') θ
        - 16 * Real.sin θ * (u θ / Real.cos θ) + 3 * deriv g θ := by
    linear_combination hC3 + 3 * hS2
  have hC3'' : Real.cos θ * deriv (deriv (deriv (fun θ' => u θ' / Real.cos θ'))) θ
      = 4 * deriv (deriv (deriv u)) θ + 15 * deriv u θ
        - Real.sin θ * (u θ / Real.cos θ) + 3 * deriv g θ := by
    have hCV1 : Real.cos θ * deriv (fun θ' => u θ' / Real.cos θ') θ
        = deriv u θ + Real.sin θ * (u θ / Real.cos θ) := by
      linear_combination -hone
    linear_combination hC3' + 15 * hCV1
  exact ⟨hone, htan, hS1, hS2, hC2, hC2', hC3, hC3', hC3''⟩

/-! ## Extractions -/



lemma slice5_v_CV2 (u g : ℝ → ℝ) (hu : ContDiffOn ℝ 4 u (Set.Ioo 0 (Real.pi / 2)))
    (hode : ∀ θ ∈ Set.Ioo 0 (Real.pi / 2), Work.FTS.EllipticEst.Lzero1 u θ = g θ) :
    ∀ θ ∈ Set.Ioo 0 (Real.pi / 2),
      Real.cos θ * deriv (deriv (fun θ' => u θ' / Real.cos θ')) θ
        = deriv (deriv u) θ + u θ
          + 2 * Real.sin θ * deriv (fun θ' => u θ' / Real.cos θ') θ :=
  fun θ hθ => (slice5_v_rel u g hu hode θ hθ).2.2.2.2.1




lemma slice5_v_CV3'' (u g : ℝ → ℝ) (hu : ContDiffOn ℝ 4 u (Set.Ioo 0 (Real.pi / 2)))
    (hode : ∀ θ ∈ Set.Ioo 0 (Real.pi / 2), Work.FTS.EllipticEst.Lzero1 u θ = g θ) :
    ∀ θ ∈ Set.Ioo 0 (Real.pi / 2),
      Real.cos θ * deriv (deriv (deriv (fun θ' => u θ' / Real.cos θ'))) θ
        = 4 * deriv (deriv (deriv u)) θ + 15 * deriv u θ
          - Real.sin θ * (u θ / Real.cos θ) + 3 * deriv g θ :=
  fun θ hθ => (slice5_v_rel u g hu hode θ hθ).2.2.2.2.2.2.2.2

/-- **Expansion of the third derivative of `tan θ · u`.**  Since `tan θ · u = sin θ · v`
with `v = u / cos θ`, the third derivative expands as
`S v_3 + 3 C v_2 - 3 S v_1 - C v` (where `v_j` is the `j`-th derivative of `v`). -/
lemma slice5_tanu3_weak (u : ℝ → ℝ) (hu : ContDiffOn ℝ 4 u (Set.Ioo 0 (Real.pi / 2))) :
    ∀ θ ∈ Set.Ioo 0 (Real.pi / 2),
      deriv (deriv (deriv (fun t => Real.tan t * u t))) θ
        = Real.sin θ * deriv (deriv (deriv (fun t => u t / Real.cos t))) θ
          + 3 * Real.cos θ * deriv (deriv (fun t => u t / Real.cos t)) θ
          - 3 * Real.sin θ * deriv (fun t => u t / Real.cos t) θ
          - Real.cos θ * (u θ / Real.cos θ) := by
  intro θ hθ
  have hIoo : Set.Ioo (0 : ℝ) (Real.pi / 2) ∈ 𝓝 θ := isOpen_Ioo.mem_nhds hθ
  have hcos_ne : ∀ t ∈ Set.Ioo (0 : ℝ) (Real.pi / 2), Real.cos t ≠ 0 :=
    fun t ht => (cos_pos_of_mem_Ioo ht).ne'
  have hψC : ContDiffOn ℝ 4 (fun t => u t / Real.cos t) (Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
    hu.div Real.contDiff_cos.contDiffOn hcos_ne
  have hψAt : ContDiffAt ℝ 3 (fun t => u t / Real.cos t) θ :=
    (hψC.contDiffAt hIoo).of_le (by norm_num)
  have hev : (fun t => Real.tan t * u t) =ᶠ[𝓝 θ] fun t => Real.sin t * (u t / Real.cos t) := by
    filter_upwards [hIoo] with t ht
    have hc : Real.cos t ≠ 0 := hcos_ne t ht
    simp only [Real.tan_eq_sin_div_cos]
    field_simp
  have h2 : iteratedDeriv 3 (fun t => Real.tan t * u t) θ
      = -Real.cos θ * (u θ / Real.cos θ)
        - 3 * Real.sin θ * iteratedDeriv 1 (fun t => u t / Real.cos t) θ
        + 3 * Real.cos θ * iteratedDeriv 2 (fun t => u t / Real.cos t) θ
        + Real.sin θ * iteratedDeriv 3 (fun t => u t / Real.cos t) θ := by
    rw [hev.iteratedDeriv_eq 3]
    exact itd_sin_three (fun t => u t / Real.cos t) θ hψAt
  rw [← itd_three_val (fun t => Real.tan t * u t) θ, h2, iteratedDeriv_one,
    itd_two_val (fun t => u t / Real.cos t) θ, itd_three_val (fun t => u t / Real.cos t) θ]
  ring

end Work.FTS.EllipticEst.remov
end
end
-- ===== merged: Submission.Work.FTS.EllipticEst.remov.slice_ang_outer =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `slice_ang_outer`: the outer (away from `π/2`) half of the angular coercivity

This file proves `Work.FTS.EllipticEst.remov.slice_ang_outer`: on the *outer* angular window
`[0, 3π/8]` — where `tan` and all its derivatives are bounded — the top angular derivative of a
solution of the slice ODE `Lzero1 u = g` is dominated by the right-hand side of the `ℋ^k`
induction step, i.e.

`∫_{[0,3π/8]} (u^{(k+2)})² sin(2θ)^{2k-γ} ≤ C · RHS`,

where `RHS` collects `∫ (g^{(k)})² sin(2θ)^{2k-γ}`, the slots `∫ (u^{(j)})² sin(2θ)^{2j-4-γ}`
for `3 ≤ j ≤ k+1`, and the three low-order terms `∫ (u'')² sin(2θ)^{-η}`, `∫ (u')²`, `∫ (u)²`.

The argument is the *pointwise* route, which is legitimate here precisely because the window
avoids the singular endpoint `θ = π/2`:

* `Work.FTS.EllipticEst.remov.Lzero1_iteratedDeriv_eq` rewrites the `k`-fold differentiated ODE
  as `u^{(k+2)} = ∑_{i ≤ k+1} C(k+1,i)(tan)^{(i)} u^{(k+1-i)} - 6u^{(k)} - g^{(k)}`;
* on `(0, π/8)` and on `[π/8, 3π/8]` the finitely many coefficients `(tan)^{(i)}`, `i ≤ k+1`,
  are bounded (`near_pointwise_bound`, `mid_pointwise_bound`), so

  `(u^{(k+2)})² ≤ K · (∑_{m ≤ k+1} (u^{(m)})² + (g^{(k)})²)`;
* multiplying by `sin(2θ)^{2k-γ} ≤ 1` and comparing the exponents
  (`2k - γ ≥ 2m - 4 - γ` for `m ≤ k + 2`, `2k - γ ≥ -η`, `2k - γ ≥ 0`) bounds each slot by one
  of the integrals in `RHS`; this is `slot_le_angPsi` / `sum_mul_le_angPsi`;
* the resulting pointwise domination on `[0, 3π/8]` is integrated against the honest (integrable)
  dominating density `angPsi`, giving the constant `C = K · (k+3)`.

The *singular* endpoint `θ = π/2` is not touched: `[0, 3π/8]` stays a positive distance away
from it, which is exactly why no cancellation/IBP argument is needed here.
-/

noncomputable section

open MeasureTheory Set Filter
open scoped Real Topology

namespace Work.FTS.EllipticEst.remov

set_option autoImplicit false
set_option maxHeartbeats 2000000







end Work.FTS.EllipticEst.remov
end
end
-- ===== merged: Submission.Work.FTS.EllipticEst.remov.slice_gprime_v_ident =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.remov

theorem slice_gprime_v_ident (u g : ℝ → ℝ)
    (hu : ContDiffOn ℝ 3 u (Set.Ioo 0 (Real.pi / 2)))
    (hg : ∀ θ ∈ Set.Ioo 0 (Real.pi / 2), Work.FTS.EllipticEst.Lzero1 u θ = g θ) :
    ∀ θ ∈ Set.Ioo 0 (Real.pi / 2),
      deriv g θ
        = - Real.cos θ * deriv (fun t => deriv (fun s => deriv (fun r => u r / Real.cos r) s) t) θ
          + 4 * Real.sin θ * deriv (fun t => deriv (fun s => u s / Real.cos s) t) θ
          - Real.cos θ * deriv (fun s => u s / Real.cos s) θ
          + 4 * Real.sin θ * (u θ / Real.cos θ) := by
  intro θ hθ
  -- `deriv g θ = deriv (Lzero1 u) θ`, expanded in terms of `u` (proved in
  -- `slice_gprime_ident`)
  have hg' := slice_gprime_ident u g hu hg θ hθ
  -- the three `u`-derivatives in terms of `v = u / cos θ` (`slice_v_identities`)
  obtain ⟨-, hu3, htu2, hu1⟩ := slice_v_identities u hu θ hθ
  rw [hg', hu3, htu2, hu1]
  ring

end Work.FTS.EllipticEst.remov
end
-- ===== merged: Submission.Work.FTS.EllipticEst.remov.slice_ibp_w =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.remov

open scoped Real Topology Interval
open MeasureTheory Set Filter

set_option maxHeartbeats 800000

/-- The `k`-th iterated derivative of a `C^n` function is `C^{n-k}`, pointwise.

Proved via `ContDiffWithinAt.derivWithin` on `Set.univ`, where `derivWithin f univ = deriv f`. -/
lemma contDiffAt_deriv_of_le_w {f : ℝ → ℝ} {x : ℝ} {n m : WithTop ℕ∞} (h : ContDiffAt ℝ n f x)
    (hm : m + 1 ≤ n) : ContDiffAt ℝ m (deriv f) x := by
  have h1 := h.contDiffWithinAt.derivWithin (𝕜 := ℝ) (s := Set.univ) (x := x) (m := m)
    uniqueDiffOn_univ hm (Set.mem_univ x)
  rwa [derivWithin_univ, contDiffWithinAt_univ] at h1

/-- The differentiated equation in `v`-form: with `v = u/cos θ` on `(0, π/2)`,

`g' = -cos θ · v''' + 4 sin θ · v'' - cos θ · v' + 4 sin θ · v`.

Combination of `slice_gprime_ident` (`g' = -u''' + (tan θ·u)'' - 6u'`) with the three
`v`-identities of `slice_v_identities` for `u'''`, `(tan θ·u)''` and `u'`. -/
theorem gprime_v_form (u g : ℝ → ℝ)
    (hu : ContDiffOn ℝ 3 u (Set.Ioo 0 (Real.pi / 2)))
    (hg : ∀ θ ∈ Set.Ioo 0 (Real.pi / 2), Work.FTS.EllipticEst.Lzero1 u θ = g θ) :
    ∀ θ ∈ Set.Ioo 0 (Real.pi / 2),
      deriv g θ
        = - Real.cos θ * deriv (fun t => deriv (fun s => deriv (fun r => u r / Real.cos r) s) t) θ
          + 4 * Real.sin θ * deriv (fun t => deriv (fun s => u s / Real.cos s) t) θ
          - Real.cos θ * deriv (fun s => u s / Real.cos s) θ
          + 4 * Real.sin θ * (u θ / Real.cos θ) := by
  intro θ hθ
  rw [slice_gprime_ident u g hu hg θ hθ, (slice_v_identities u hu θ hθ).2.1,
    (slice_v_identities u hu θ hθ).2.2.1, (slice_v_identities u hu θ hθ).2.2.2]
  ring

/-- **The abstract weighted interval integration-by-parts identity.**  For functions
`v, g, Φ, Ψ` of class `C³, C¹, C², C⁰` on `[a,b]` (`a < b`) with `Φ = cos·Ψ` on `[a,b]` and
satisfying the differentiated equation `g' = -cos θ v''' + 4 sin θ v'' - cos θ v' + 4 sin θ v`,

`∫_a^b [4 sin θ Ψ + ½Φ'] (v'')² + ½ ∫_a^b Φ' (v')² + 4 ∫_a^b sin θ Ψ v v''
  = ∫_a^b Ψ g' v'' + ½ [ Φ ((v'')² + (v')²) ]_a^b`.

Proof: `K x = ½ Φ x ((v''x)² + (v'x)²)` has derivative equal to the difference of the two
integrands (pointwise, using `Φ = cos·Ψ` and the equation), so the fundamental theorem of
calculus gives the two `a`-`b` integral forms of the identity. -/
lemma slice_ibp_aux_w {v g Φ Ψ : ℝ → ℝ} {a b : ℝ} (hab : a < b)
    (hv1 : ∀ x ∈ Set.Icc a b, HasDerivAt v (deriv v x) x)
    (hv2 : ∀ x ∈ Set.Icc a b, HasDerivAt (deriv v) (deriv (deriv v) x) x)
    (hv3 : ∀ x ∈ Set.Icc a b, HasDerivAt (deriv (deriv v)) (deriv (deriv (deriv v)) x) x)
    (hΦ1 : ∀ x ∈ Set.Icc a b, HasDerivAt Φ (deriv Φ x) x)
    (hΦ2 : ∀ x ∈ Set.Icc a b, HasDerivAt (deriv Φ) (deriv (deriv Φ) x) x)
    (hΦΨ : ∀ x ∈ Set.Icc a b, Φ x = Real.cos x * Ψ x)
    (heq : ∀ x ∈ Set.Icc a b, deriv g x
        = -Real.cos x * deriv (deriv (deriv v)) x + 4 * Real.sin x * deriv (deriv v) x
          - Real.cos x * deriv v x + 4 * Real.sin x * v x)
    (hc3 : ContinuousOn (deriv (deriv (deriv v))) (Set.Icc a b))
    (hcΨ : ContinuousOn Ψ (Set.Icc a b)) :
    (∫ x in a..b, (4 * Real.sin x * Ψ x + (1 / 2) * deriv Φ x) * (deriv (deriv v) x) ^ 2)
      + (1 / 2) * (∫ x in a..b, deriv Φ x * (deriv v x) ^ 2)
      + 4 * (∫ x in a..b, Real.sin x * Ψ x * v x * deriv (deriv v) x)
    = (∫ x in a..b, Ψ x * deriv g x * deriv (deriv v) x)
      + (1 / 2) * (Φ b * ((deriv (deriv v) b) ^ 2 + (deriv v b) ^ 2)
          - Φ a * ((deriv (deriv v) a) ^ 2 + (deriv v a) ^ 2)) := by
  have hab' : a ≤ b := le_of_lt hab
  have hc1 : ContinuousOn (deriv v) (Set.Icc a b) :=
    fun x hx => (hv2 x hx).continuousAt.continuousWithinAt
  have hc2 : ContinuousOn (deriv (deriv v)) (Set.Icc a b) :=
    fun x hx => (hv3 x hx).continuousAt.continuousWithinAt
  have hcv : ContinuousOn v (Set.Icc a b) :=
    fun x hx => (hv1 x hx).continuousAt.continuousWithinAt
  have hcΦ : ContinuousOn Φ (Set.Icc a b) :=
    fun x hx => (hΦ1 x hx).continuousAt.continuousWithinAt
  have hcΦ' : ContinuousOn (deriv Φ) (Set.Icc a b) :=
    fun x hx => (hΦ2 x hx).continuousAt.continuousWithinAt
  have hdg : ContinuousOn (deriv g) (Set.Icc a b) := by
    have hR : ContinuousOn (fun x => -Real.cos x * deriv (deriv (deriv v)) x
        + 4 * Real.sin x * deriv (deriv v) x - Real.cos x * deriv v x
        + 4 * Real.sin x * v x) (Set.Icc a b) := by fun_prop
    exact hR.congr heq
  set K : ℝ → ℝ := fun x =>
    (1/2) * (Φ x * (deriv (deriv v) x * deriv (deriv v) x + deriv v x * deriv v x)) with hK
  set Q : ℝ → ℝ := fun x => (1/2) * (deriv Φ x * (deriv (deriv v) x * deriv (deriv v) x
      + deriv v x * deriv v x)
      + Φ x * ((deriv (deriv (deriv v)) x * deriv (deriv v) x
          + deriv (deriv v) x * deriv (deriv (deriv v)) x)
        + (deriv (deriv v) x * deriv v x + deriv v x * deriv (deriv v) x))) with hQ
  have hQcont : ContinuousOn Q (Set.Icc a b) := by rw [hQ]; fun_prop
  have hQint : IntervalIntegrable Q volume a b := ContinuousOn.intervalIntegrable_of_Icc hab' hQcont
  have hKder : ∀ x ∈ Set.uIcc a b, HasDerivAt K (Q x) x := by
    intro x hx
    rw [Set.uIcc_of_le hab'] at hx
    rw [hK, hQ]
    have h1 : HasDerivAt (fun y => deriv v y * deriv v y)
        (deriv (deriv v) x * deriv v x + deriv v x * deriv (deriv v) x) x :=
      (hv2 x hx).mul (hv2 x hx)
    have h2 : HasDerivAt (fun y => deriv (deriv v) y * deriv (deriv v) y)
        (deriv (deriv (deriv v)) x * deriv (deriv v) x
          + deriv (deriv v) x * deriv (deriv (deriv v)) x) x :=
      (hv3 x hx).mul (hv3 x hx)
    have hG := h2.add h1
    exact ((hΦ1 x hx).mul hG).const_mul (1/2)
  have hFTCK : ∫ x in a..b, Q x = K b - K a :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt hKder hQint
  have hKval : K b - K a = (1/2) * (Φ b * ((deriv (deriv v) b) ^ 2 + (deriv v b) ^ 2)
      - Φ a * ((deriv (deriv v) a) ^ 2 + (deriv v a) ^ 2)) := by
    rw [hK]; ring
  have hpt : ∀ x ∈ Set.Icc a b,
      (4 * Real.sin x * Ψ x + (1/2) * deriv Φ x) * (deriv (deriv v) x) ^ 2
        + (1/2) * (deriv Φ x * (deriv v x) ^ 2)
        + 4 * (Real.sin x * Ψ x * v x * deriv (deriv v) x)
      = Ψ x * deriv g x * deriv (deriv v) x + Q x := by
    intro x hx
    simp only [hQ]
    rw [heq x hx, hΦΨ x hx]
    ring
  have hint1 : IntervalIntegrable
      (fun x => (4 * Real.sin x * Ψ x + (1/2) * deriv Φ x) * (deriv (deriv v) x) ^ 2)
      volume a b := by
    have h : ContinuousOn
        (fun x => (4 * Real.sin x * Ψ x + (1/2) * deriv Φ x) * (deriv (deriv v) x) ^ 2)
        (Set.Icc a b) := by fun_prop
    exact ContinuousOn.intervalIntegrable_of_Icc hab' h
  have hint2 : IntervalIntegrable (fun x => (1/2) * (deriv Φ x * (deriv v x) ^ 2)) volume a b := by
    have h : ContinuousOn (fun x => (1/2) * (deriv Φ x * (deriv v x) ^ 2)) (Set.Icc a b) := by
      fun_prop
    exact ContinuousOn.intervalIntegrable_of_Icc hab' h
  have hint3 : IntervalIntegrable (fun x => 4 * (Real.sin x * Ψ x * v x * deriv (deriv v) x))
      volume a b := by
    have h : ContinuousOn (fun x => 4 * (Real.sin x * Ψ x * v x * deriv (deriv v) x))
        (Set.Icc a b) := by fun_prop
    exact ContinuousOn.intervalIntegrable_of_Icc hab' h
  have hintR : IntervalIntegrable (fun x => Ψ x * deriv g x * deriv (deriv v) x) volume a b := by
    have h : ContinuousOn (fun x => Ψ x * deriv g x * deriv (deriv v) x) (Set.Icc a b) := by
      fun_prop
    exact ContinuousOn.intervalIntegrable_of_Icc hab' h
  have hInt : (∫ x in a..b, ((4 * Real.sin x * Ψ x + (1/2) * deriv Φ x) * (deriv (deriv v) x) ^ 2
        + (1/2) * (deriv Φ x * (deriv v x) ^ 2)
        + 4 * (Real.sin x * Ψ x * v x * deriv (deriv v) x)))
      = (∫ x in a..b, (4 * Real.sin x * Ψ x + (1/2) * deriv Φ x) * (deriv (deriv v) x) ^ 2)
        + (1/2) * (∫ x in a..b, deriv Φ x * (deriv v x) ^ 2)
        + 4 * (∫ x in a..b, Real.sin x * Ψ x * v x * deriv (deriv v) x) := by
    rw [intervalIntegral.integral_add (hint1.add hint2) hint3, intervalIntegral.integral_add hint1 hint2,
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
  have hcongr : (∫ x in a..b, ((4 * Real.sin x * Ψ x + (1/2) * deriv Φ x) * (deriv (deriv v) x) ^ 2
        + (1/2) * (deriv Φ x * (deriv v x) ^ 2)
        + 4 * (Real.sin x * Ψ x * v x * deriv (deriv v) x)))
      = ∫ x in a..b, (Ψ x * deriv g x * deriv (deriv v) x + Q x) := by
    apply intervalIntegral.integral_congr
    intro x hx
    rw [Set.uIcc_of_le hab'] at hx
    exact hpt x hx
  have hmain : (∫ x in a..b, ((4 * Real.sin x * Ψ x + (1/2) * deriv Φ x) * (deriv (deriv v) x) ^ 2
        + (1/2) * (deriv Φ x * (deriv v x) ^ 2)
        + 4 * (Real.sin x * Ψ x * v x * deriv (deriv v) x)))
      = (∫ x in a..b, Ψ x * deriv g x * deriv (deriv v) x)
        + (1/2) * (Φ b * ((deriv (deriv v) b) ^ 2 + (deriv v b) ^ 2)
          - Φ a * ((deriv (deriv v) a) ^ 2 + (deriv v a) ^ 2)) := by
    rw [hcongr, intervalIntegral.integral_add hintR hQint, hFTCK, hKval]
  rw [← hInt, hmain]

/-- The weighted interval integration-by-parts identity with weight `σ(θ) = sin(2θ)^{2-γ}`.
With `v := u/cos`, `a < b` in `(0,π/2)`:
`∫_a^b [4 sin θ · σ + ½(σ cos)'] (v'')² + ½ ∫_a^b (σ cos)' (v')² + 4 ∫_a^b sin θ σ v v''
  = ∫_a^b σ g' v''  +  ½ [ σ cos θ ((v'')² + (v')²) ]_a^b`.
From `Lzero1 u = g` in `v`-form (`-cos θ v'' + 3 sin θ v' - 4 cos θ v = g`), differentiate to get
`g' = -cos θ v''' + 4 sin θ v'' - cos θ v' + 4 sin θ v`, multiply by `-σ v''`, integrate by parts
twice.  No endpoint analysis: everything is on `[a,b] ⊂ (0,π/2)`.

Useful ingredients already in the workspace: `Work.FTS.EllipticEst.remov.slice_v_identities`
gives `Lzero1 u = -cos θ v'' + 3 sin θ v' - 4 cos θ v`, `u''' = cos θ v''' - 3 sin θ v'' - 3 cos θ v' + sin θ v`
and `u' = cos θ v' - sin θ v` on `(0,π/2)`; `Work.FTS.EllipticEst.remov.slice_gprime_ident`
gives `deriv g θ = -deriv(deriv(deriv u)) θ + ...` in the `u`-form.  Combining the two gives
the `v`-form of `g'` used above. -/
theorem slice_ibp_w (γ : ℝ) (a b : ℝ) (hab : a < b) (ha : 0 < a) (hb : b < Real.pi / 2)
    {u g : ℝ → ℝ} (hu : ContDiffOn ℝ 3 u (Set.Ioo 0 (Real.pi / 2)))
    (hg : ∀ θ ∈ Set.Ioo 0 (Real.pi / 2), Work.FTS.EllipticEst.Lzero1 u θ = g θ) :
    (∫ θ in a..b, (4 * Real.sin θ * Real.rpow (Real.sin (2 * θ)) (2 - γ)
          + (1 / 2) * deriv (fun t => Real.cos t * Real.rpow (Real.sin (2 * t)) (2 - γ)) θ)
        * (deriv (fun t => deriv (fun s => u s / Real.cos s) t) θ) ^ 2)
      + (1 / 2) * (∫ θ in a..b,
            deriv (fun t => Real.cos t * Real.rpow (Real.sin (2 * t)) (2 - γ)) θ
          * (deriv (fun t => u t / Real.cos t) θ) ^ 2)
      + 4 * (∫ θ in a..b, Real.sin θ * Real.rpow (Real.sin (2 * θ)) (2 - γ)
          * (u θ / Real.cos θ)
          * deriv (fun t => deriv (fun s => u s / Real.cos s) t) θ)
      = (∫ θ in a..b, Real.rpow (Real.sin (2 * θ)) (2 - γ) * deriv g θ
          * deriv (fun t => deriv (fun s => u s / Real.cos s) t) θ)
        + (1 / 2) * (Real.cos b * Real.rpow (Real.sin (2 * b)) (2 - γ)
              * ((deriv (fun t => deriv (fun s => u s / Real.cos s) t) b) ^ 2
                + (deriv (fun t => u t / Real.cos t) b) ^ 2)
            - Real.cos a * Real.rpow (Real.sin (2 * a)) (2 - γ)
              * ((deriv (fun t => deriv (fun s => u s / Real.cos s) t) a) ^ 2
                + (deriv (fun t => u t / Real.cos t) a) ^ 2)) := by
  have hab' : a ≤ b := le_of_lt hab
  have hmem : ∀ x ∈ Set.Icc a b, x ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) := by
    intro x hx
    exact ⟨by linarith [ha, hx.1], by linarith [hx.2, hb]⟩
  have hcos_ne : ∀ t ∈ Set.Ioo (0 : ℝ) (Real.pi / 2), Real.cos t ≠ 0 := by
    intro t ht
    exact ne_of_gt (Real.cos_pos_of_mem_Ioo ⟨by linarith [ht.1, Real.pi_pos], by linarith [ht.2]⟩)
  have hvcd : ContDiffOn ℝ 3 (fun s => u s / Real.cos s) (Set.Ioo 0 (Real.pi / 2)) :=
    hu.div Real.contDiff_cos.contDiffOn hcos_ne
  have hv3 : ∀ x ∈ Set.Icc a b, ContDiffAt ℝ 3 (fun s => u s / Real.cos s) x :=
    fun x hx => hvcd.contDiffAt (isOpen_Ioo.mem_nhds (hmem x hx))
  have hv1 : ∀ x ∈ Set.Icc a b, HasDerivAt (fun s => u s / Real.cos s)
      (deriv (fun s => u s / Real.cos s) x) x :=
    fun x hx => ((hv3 x hx).differentiableAt (by norm_num)).hasDerivAt
  have hdv2 : ∀ x ∈ Set.Icc a b, ContDiffAt ℝ 2 (deriv (fun s => u s / Real.cos s)) x :=
    fun x hx => contDiffAt_deriv_of_le_w (m := 2) (hv3 x hx) (by norm_num)
  have hv2 : ∀ x ∈ Set.Icc a b, HasDerivAt (deriv (fun s => u s / Real.cos s))
      (deriv (deriv (fun s => u s / Real.cos s)) x) x :=
    fun x hx => ((hdv2 x hx).differentiableAt (by norm_num)).hasDerivAt
  have hdv3 : ∀ x ∈ Set.Icc a b, ContDiffAt ℝ 1 (deriv (deriv (fun s => u s / Real.cos s))) x :=
    fun x hx => contDiffAt_deriv_of_le_w (m := 1) (hdv2 x hx) (by norm_num)
  have hv3' : ∀ x ∈ Set.Icc a b, HasDerivAt (deriv (deriv (fun s => u s / Real.cos s)))
      (deriv (deriv (deriv (fun s => u s / Real.cos s))) x) x :=
    fun x hx => ((hdv3 x hx).differentiableAt (by norm_num)).hasDerivAt
  have hc3 : ContinuousOn (deriv (deriv (deriv (fun s => u s / Real.cos s)))) (Set.Icc a b) := by
    intro x hx
    have h0 : ContDiffAt ℝ 0 (deriv (deriv (deriv (fun s => u s / Real.cos s)))) x :=
      contDiffAt_deriv_of_le_w (m := 0) (hdv3 x hx) (by norm_num)
    exact (continuousWithinAt_univ _ x).mp h0.continuousWithinAt |>.continuousWithinAt
  have hsin2pos : ∀ x ∈ Set.Icc a b, 0 < Real.sin (2 * x) := by
    intro x hx
    have hxi := hmem x hx
    exact Real.sin_pos_of_mem_Ioo ⟨by linarith [hxi.1], by linarith [hxi.2]⟩
  have hsin2cd : ∀ x ∈ Set.Icc a b, ContDiffAt ℝ 2 (fun t => Real.sin (2 * t)) x := by
    intro x hx
    exact (Real.contDiff_sin.contDiffAt).comp x (contDiffAt_const.mul contDiffAt_id)
  have hΨcd : ∀ x ∈ Set.Icc a b,
      ContDiffAt ℝ 2 (fun t => Real.rpow (Real.sin (2 * t)) (2 - γ)) x := by
    intro x hx
    exact (hsin2cd x hx).rpow contDiffAt_const (ne_of_gt (hsin2pos x hx))
  have hΦcd : ∀ x ∈ Set.Icc a b,
      ContDiffAt ℝ 2 (fun t => Real.cos t * Real.rpow (Real.sin (2 * t)) (2 - γ)) x := by
    intro x hx
    exact (Real.contDiff_cos.contDiffAt).mul (hΨcd x hx)
  have hΦ1 : ∀ x ∈ Set.Icc a b,
      HasDerivAt (fun t => Real.cos t * Real.rpow (Real.sin (2 * t)) (2 - γ))
        (deriv (fun t => Real.cos t * Real.rpow (Real.sin (2 * t)) (2 - γ)) x) x :=
    fun x hx => ((hΦcd x hx).differentiableAt (by norm_num)).hasDerivAt
  have hΦ2 : ∀ x ∈ Set.Icc a b,
      HasDerivAt (deriv (fun t => Real.cos t * Real.rpow (Real.sin (2 * t)) (2 - γ)))
        (deriv (deriv (fun t => Real.cos t * Real.rpow (Real.sin (2 * t)) (2 - γ))) x) x :=
    fun x hx => ((contDiffAt_deriv_of_le_w (m := 1) (hΦcd x hx) (by norm_num)).differentiableAt
      (by norm_num)).hasDerivAt
  have hcΨ : ContinuousOn (fun t => Real.rpow (Real.sin (2 * t)) (2 - γ)) (Set.Icc a b) := by
    intro x hx
    exact ((hΨcd x hx).continuousAt).continuousWithinAt
  have heq : ∀ x ∈ Set.Icc a b, deriv g x
      = -Real.cos x * deriv (deriv (deriv (fun s => u s / Real.cos s))) x
        + 4 * Real.sin x * deriv (deriv (fun s => u s / Real.cos s)) x
        - Real.cos x * deriv (fun s => u s / Real.cos s) x
        + 4 * Real.sin x * (u x / Real.cos x) :=
    fun x hx => gprime_v_form u g hu hg x (hmem x hx)
  exact slice_ibp_aux_w (v := fun s => u s / Real.cos s)
    (g := g)
    (Φ := fun t => Real.cos t * Real.rpow (Real.sin (2 * t)) (2 - γ))
    (Ψ := fun t => Real.rpow (Real.sin (2 * t)) (2 - γ))
    hab hv1 hv2 hv3' hΦ1 hΦ2 (fun x hx => rfl) heq hc3 hcΨ

end Work.FTS.EllipticEst.remov
end
-- ===== merged: Submission.Work.FTS.H2.T2SliceAux =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.H2

set_option autoImplicit false

/-! ## The angular slice of a smooth function -/

/-- For a function which is smooth on an open neighbourhood of the closed quadrant
(`Work.Spaces.SmoothNbhd`), the angular slice `θ ↦ h z θ` is continuous on `Iθ` for
every `z ∈ Iz`. -/
theorem continuousOn_slice {h : ℝ → ℝ → ℝ} (hsm : Work.Spaces.SmoothNbhd h) {z : ℝ}
    (hz : z ∈ Work.Spaces.Iz) :
    ContinuousOn (fun θ => h z θ) Work.Spaces.Iθ := by
  intro θ hθ
  have hcd : ContDiffAt ℝ ⊤ (Function.uncurry h) (z, θ) :=
    hsm.contDiffAt (Work.Spaces.isOpen_nbhU.mem_nhds (Work.Spaces.mem_nbhU hz hθ))
  exact (hcd.continuousAt.comp (Continuous.prodMk_right z).continuousAt).continuousWithinAt


/-! ## The factor `sin(2θ)` survives the `D_z`-iterates -/

/-- A function of `θ` alone may be pulled out of the iterates of `D_z = z ∂_z`. -/
theorem DzIter_const_mul (j : ℕ) (c : ℝ → ℝ) (K : ℝ → ℝ → ℝ) :
    Work.Spaces.DzIter j (fun z θ => c θ * K z θ)
      = fun z θ => c θ * Work.Spaces.DzIter j K z θ := by
  induction j with
  | zero => rfl
  | succ j ih =>
      rw [Work.Spaces.DzIter_succ, ih, Work.Spaces.DzIter_succ]
      funext z θ
      show z * deriv (fun z' => c θ * Work.Spaces.DzIter j K z' θ) z
        = c θ * (z * deriv (fun z' => Work.Spaces.DzIter j K z' θ) z)
      rw [deriv_const_mul_field]
      ring

/-- The `sin(2θ)` produced by the outermost `D_θ` of `D_θ^{i+1}` survives the
`D_z`-iterates. -/
theorem mixed_sin_factor (j i : ℕ) (g : ℝ → ℝ → ℝ) :
    Work.Spaces.mixed j (i + 1) g
      = fun z θ => Real.sin (2 * θ)
          * Work.Spaces.DzIter j (Work.Spaces.pth (Work.Spaces.DthIter i g)) z θ := by
  have h : Work.Spaces.DthIter (i + 1) g
      = fun z θ => Real.sin (2 * θ) * Work.Spaces.pth (Work.Spaces.DthIter i g) z θ := rfl
  show Work.Spaces.DzIter j (Work.Spaces.DthIter (i + 1) g) = _
  rw [h]
  exact DzIter_const_mul j (fun θ => Real.sin (2 * θ))
    (Work.Spaces.pth (Work.Spaces.DthIter i g))

/-- The `z`-derivative of the same factorisation: `∂_z (mixed j (i+1) g)` also carries the
factor `sin(2θ)`, since the factor is independent of `z`. -/
theorem pz_mixed_sin_factor (j i : ℕ) (g : ℝ → ℝ → ℝ) (z θ : ℝ) :
    Work.Spaces.pz (Work.Spaces.mixed j (i + 1) g) z θ
      = Real.sin (2 * θ)
          * Work.Spaces.pz (Work.Spaces.DzIter j (Work.Spaces.pth (Work.Spaces.DthIter i g)))
              z θ := by
  rw [mixed_sin_factor j i g]
  show deriv (fun z' => Real.sin (2 * θ)
        * Work.Spaces.DzIter j (Work.Spaces.pth (Work.Spaces.DthIter i g)) z' θ) z
      = Real.sin (2 * θ)
        * deriv (fun z' => Work.Spaces.DzIter j (Work.Spaces.pth (Work.Spaces.DthIter i g))
            z' θ) z
  rw [deriv_const_mul_field]

/-! ## Weight algebra at the angular endpoints -/

/-- `s² · s^{-γ} = s^{2-γ}` for `s ≥ 0` and `γ < 2`. -/
theorem sq_mul_rpow_neg (s γ : ℝ) (hs : 0 ≤ s) (hγ : γ < 2) :
    s ^ 2 * s ^ (-γ) = s ^ (2 - γ) := by
  have hne : (2 : ℝ) + (-γ) ≠ 0 := by linarith
  have h2 : s ^ (2 : ℝ) = s ^ 2 := Real.rpow_natCast s 2
  calc s ^ 2 * s ^ (-γ) = s ^ (2 : ℝ) * s ^ (-γ) := by rw [h2]
    _ = s ^ ((2 : ℝ) + -γ) :=
        (Real.rpow_add' (x := s) (y := (2 : ℝ)) (z := -γ) hs hne).symm
    _ = s ^ (2 - γ) := by rw [show (2 : ℝ) + -γ = 2 - γ by ring]

/-- `s² · s^{-γ} ≤ 1` for `0 ≤ s ≤ 1` and `0 ≤ 2 - γ`.  This is the pointwise bound which
makes `sin(2θ)^{2-γ}` (the effective weight of a "hard" mixed summand) bounded on `Iθ`. -/
theorem sq_mul_rpow_neg_le_one (s γ : ℝ) (hs0 : 0 ≤ s) (hs1 : s ≤ 1) (hγ : γ < 2)
    (hγ2 : 0 ≤ 2 - γ) : s ^ 2 * s ^ (-γ) ≤ 1 := by
  rw [sq_mul_rpow_neg s γ hs0 hγ]
  exact Real.rpow_le_one hs0 hs1 hγ2

end Work.FTS.H2
end
end
-- ===== merged: Submission.Work.FTS.H2.mixed_sin_bound =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.H2

set_option autoImplicit false

/-! ## Pulling a `z`-independent factor out of the iterated operators -/

/-- A factor which does not depend on `z` passes through `∂_z`. -/
theorem pz_const_mul (c : ℝ → ℝ) (K : ℝ → ℝ → ℝ) (z θ : ℝ) :
    Work.Spaces.pz (fun z θ => c θ * K z θ) z θ = c θ * Work.Spaces.pz K z θ := by
  rw [Work.Spaces.pz, Work.Spaces.pz]
  exact deriv_const_mul_field _

/-- A factor which does not depend on `z` passes through `D_z^j`. -/
theorem DzIter_const_mul_apply (c : ℝ → ℝ) (K : ℝ → ℝ → ℝ) (j : ℕ) (z θ : ℝ) :
    Work.Spaces.DzIter j (fun z θ => c θ * K z θ) z θ = c θ * Work.Spaces.DzIter j K z θ := by
  induction j generalizing z θ with
  | zero => rfl
  | succ j ih =>
    rw [Work.Spaces.DzIter_succ, Work.Spaces.Dz, Work.Spaces.DzIter_succ, Work.Spaces.Dz]
    have heq : Work.Spaces.DzIter j (fun z θ => c θ * K z θ)
        = fun z θ => c θ * Work.Spaces.DzIter j K z θ :=
      funext fun z => funext fun θ => ih z θ
    rw [heq, pz_const_mul]
    ring

/-! ## The explicit factor `sin(2θ)` in the mixed derivatives -/


/-! ## The main bound -/


end Work.FTS.H2
end
end
-- ===== merged: Submission.Work.FTS.Nonlinear.FstarPkg.c2mInv_radial =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The radial weighted `z`-derivative bound for `2α/(1+z)`

T. M. Elgindi, *Finite-time singularity formation for `C^{1,α}` solutions to the
incompressible Euler equations on `ℝ³`*, Annals of Math. **194** (2021).

For the rational function `B(z) = 2α/(1+z) = 2α·(1+z)⁻¹` one has the closed form

`deriv^[k] B z = (-1)^k k! · 2α · (1+z)^{-(k+1)}`   (`z > -1`),

so that the weight `(z+1)^k` cancels all but one power of `(1+z)⁻¹`:

`(z+1)^k deriv^[k] B z = (-1)^k k! · 2α · (1+z)⁻¹`,  hence `|…| ≤ 2α k!` for `z ≥ 0`.

The machinery for the closed form (`nInvClosed`, `iter_deriv_nInvClosed`,
`deriv_iter_const_mul`, `nInvClosed_weighted`) is proved in the sibling module
`Submission.Work.FTS.Nonlinear.FstarPkg.c2mInv_points` and reused here.
-/

noncomputable section

namespace Work.FTS.Nonlinear.FstarPkg

set_option autoImplicit false

theorem c2mInv_radial (α : ℝ) (hα : 0 < α) (k : ℕ) (z : ℝ) (hz : 0 ≤ z) :
    |(z + 1) ^ k * deriv^[k] (fun z : ℝ => 2 * α / (1 + z)) z| ≤ 2 * α * (k.factorial : ℝ) := by
  have hz1 : -1 < z := by linarith
  have hα2 : (0 : ℝ) ≤ 2 * α := by linarith
  -- closed form of the `k`-th derivative of `2α/(1+z)`
  have hB : deriv^[k] (fun z : ℝ => 2 * α / (1 + z)) z = 2 * α * nInvClosed k z := by
    have h1 : (fun z : ℝ => 2 * α / (1 + z)) = fun z : ℝ => (2 * α) * ((1 + z)⁻¹) := by
      funext z; rw [div_eq_mul_inv]
    rw [h1, congrFun (deriv_iter_const_mul (2 * α) (fun z : ℝ => (1 + z)⁻¹) k) z,
      iter_deriv_nInvClosed k z hz1]
  rw [hB, show (z + 1) ^ k * (2 * α * nInvClosed k z)
        = 2 * α * ((z + 1) ^ k * nInvClosed k z) by ring,
    abs_mul, abs_of_nonneg hα2]
  exact mul_le_mul_of_nonneg_left (nInvClosed_weighted k z hz) hα2

end Work.FTS.Nonlinear.FstarPkg
end
end
-- ===== merged: Submission.Work.FTS.Nonlinear.Pieces.RNP.row15aux.Gseq_iter_bounded =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# All `D_θ`-iterates of `Gseq α d` are bounded on `Iθ`, uniformly in `α ∈ (0,1]`

The sequence `Gseq α d` is defined by `Gseq α 0 = q/2` and
`Gseq α (d+1) = D_θ (Gseq α d) + g · Gseq α d`,  `g = gfun α = (α-2)q - 2/3`.

Since `D_θ = sin(2θ)∂_θ` is a vector field it satisfies the Leibniz rule
(`Work.Spaces.dthU_iter_mul`), so an induction on `d` bounds every iterate:
if `|D_θ^m (Gseq α d) θ| ≤ M m` then

  `D_θ^m (Gseq α (d+1)) = D_θ^{m+1}(Gseq α d) + ∑_{i≤m} C(m,i) (D_θ^i g)(D_θ^{m-i}(Gseq α d))`,

and both factors are bounded uniformly in `α ∈ (0,1]`: the first by the induction
hypothesis, the second because `|D_θ^i (gfun α) θ| ≤ gBnd i` for `0 < α ≤ 1` and
`θ ∈ Iθ` (`dthU_gfun_le`).  Mirroring `Work.Spaces.Tfun_iter_bounded`.
-/

open scoped Real Topology

namespace Work.FTS.Nonlinear.Pieces.RNP.row15aux

set_option autoImplicit false

local notation "C∞" => (⊤ : ℕ∞)



end Work.FTS.Nonlinear.Pieces.RNP.row15aux
end
-- ===== merged: Submission.Work.FTS.Nonlinear.Pieces.RNP.row15aux.mixedSepDecomp =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.Nonlinear.Pieces.RNP.row15aux

/-!
# Separation of variables for the mixed operators `D_z^l D_θ^m`

For a product of a `θ`-only function and a `z`-only function, the mixed operator
`D_z^l D_θ^m` acts on the two factors separately:

`D_z^l D_θ^m (θ ↦ C θ · z ↦ B z) z θ = (dthU^[m] C) θ · (OpZ^[l] B) z`,

where `OpZ B z = z · B'(z)` and `dthU C θ = sin(2θ) · C'(θ)` are the one-dimensional
`D_z`- and `D_θ`-operators.

The angular half is the existing `Work.Spaces.DthIter_decomp`; the radial half is proved
here by induction, from the slice identity `Work.Spaces.sliceZ_DzIter` and the elementary
fact that `OpZ` commutes with multiplication by a constant (`deriv_const_mul_field`, which
needs no differentiability hypothesis).
-/

/-- `OpZ` commutes with multiplication by a constant. -/
private lemma OpZ_const_mul (c : ℝ) (f : ℝ → ℝ) :
    Work.Spaces.OpZ (fun x => c * f x) = fun x => c * Work.Spaces.OpZ f x := by
  funext x
  simp only [Work.Spaces.OpZ, deriv_const_mul_field]
  ring

/-- Iterated version of `OpZ_const_mul`. -/
private lemma OpZ_iterate_const_mul (l : ℕ) (c : ℝ) (f : ℝ → ℝ) :
    (Work.Spaces.OpZ^[l]) (fun x => c * f x) = fun x => c * (Work.Spaces.OpZ^[l] f) x := by
  induction l with
  | zero => rfl
  | succ n ih =>
      rw [Function.iterate_succ_apply', ih, OpZ_const_mul]
      rw [Function.iterate_succ_apply']

/-- The radial half of the separation of variables: if the `θ`-factor `A θ` is held fixed,
then `D_z^l` acts only on the `z`-factor `B`. -/
private lemma DzIter_theta_factor (l : ℕ) (A B : ℝ → ℝ) (z θ : ℝ) :
    Work.Spaces.DzIter l (fun z θ => A θ * B z) z θ = A θ * (Work.Spaces.OpZ^[l] B) z := by
  have h := congrFun (Work.Spaces.sliceZ_DzIter l (fun z θ => A θ * B z) θ) z
  rw [h]
  exact congrFun (OpZ_iterate_const_mul l (A θ) B) z

theorem mixedSepDecomp (l m : ℕ) (C B : ℝ → ℝ) (z θ : ℝ) :
    Work.Spaces.mixed l m (fun z θ => C θ * B z) z θ
      = (Work.Spaces.dthU^[m] C) θ * (Work.Spaces.OpZ^[l] B) z := by
  unfold Work.Spaces.mixed
  have hDth : Work.Spaces.DthIter m (fun z θ => C θ * B z)
      = fun z θ => (Work.Spaces.dthU^[m] C) θ * B z := by
    funext z θ
    exact Work.Spaces.DthIter_decomp m C B z θ
  rw [hDth]
  exact DzIter_theta_factor l (Work.Spaces.dthU^[m] C) B z θ

end Work.FTS.Nonlinear.Pieces.RNP.row15aux
end
-- ===== merged: Submission.Work.FTS.PhiStar.At_linear_deriv_bound =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.PhiStar

set_option autoImplicit false

/-- The coefficient of the `At N k` slot in `deriv^[k+1] ((1+z)·At N 0 z)`:
`(-1)^k·(k+1)!·(k+1)`. -/
def AtLinC1 (k : ℕ) : ℝ := (-1) ^ k * ((k + 1).factorial : ℝ) * (k + 1)

/-- The coefficient of the `(1+z)·At N (k+1)` slot in `deriv^[k+1] ((1+z)·At N 0 z)`:
`(-1)^(k+1)·(k+2)!`. -/
def AtLinC2 (k : ℕ) : ℝ := (-1) ^ (k + 1) * ((k + 2).factorial : ℝ)

/-- The two-term combination which equals the `(k+1)`-st derivative of `(1+z)·At N 0 z`. -/
def AtLinComb (N : ℝ) (k : ℕ) : ℝ → ℝ :=
  fun z => AtLinC1 k * Work.FTS.H2.PhiStarE.At N k z
    + AtLinC2 k * ((1 + z) * Work.FTS.H2.PhiStarE.At N (k + 1) z)

/-- The recursion for the first coefficient. -/
lemma AtLinC1_succ (k : ℕ) :
    AtLinC1 (k + 1) = -((k : ℝ) + 2) * AtLinC1 k + AtLinC2 k := by
  simp only [AtLinC1, AtLinC2, Nat.factorial_succ]
  push_cast
  rw [pow_succ]
  ring

/-- The recursion for the second coefficient. -/
lemma AtLinC2_succ (k : ℕ) : AtLinC2 (k + 1) = -((k : ℝ) + 3) * AtLinC2 k := by
  simp only [AtLinC2, Nat.factorial_succ]
  push_cast
  rw [pow_succ]
  ring

/-- `|AtLinC1 k| = (k+1)!·(k+1) ≤ 7·7! = 35280` for `k ≤ 6`. -/
lemma AtLin_absC1_le (k : ℕ) (hk : k ≤ 6) : |AtLinC1 k| ≤ 35280 := by
  interval_cases k <;> norm_num [AtLinC1, Nat.factorial]

/-- `|AtLinC2 k| = (k+2)! ≤ 8! = 40320` for `k ≤ 6`. -/
lemma AtLin_absC2_le (k : ℕ) (hk : k ≤ 6) : |AtLinC2 k| ≤ 40320 := by
  interval_cases k <;> norm_num [AtLinC2, Nat.factorial]

/-- The library's `shift_bound` in the `e = 0` shape used below:
`|(1+z)^c·At N j z| ≤ 2^(c+1)/N` when `c ≤ j+1`. -/
lemma AtLin_shift_bound (N : ℝ) (hN : 2 ≤ N) (c j : ℕ) (hc : c ≤ j + 1) {z : ℝ}
    (hz : 0 ≤ z) :
    |(1 + z) ^ c * Work.FTS.H2.PhiStarE.At N j z| ≤ 2 ^ (c + 1) / N := by
  have h := Work.FTS.H2.PhiStarE.shift_bound N hN c j 0 (by omega) hz
  simpa using h

/-- The derivative of `At N (j+1)`, with the cast `((j+1 : ℕ) : ℝ) + 2 = (j:ℝ) + 3`
normalised away. -/
lemma AtLin_hasDerivAt_At_succ (N : ℝ) (hN : 0 ≤ N) (j : ℕ) {z : ℝ} (hz : 0 ≤ z) :
    HasDerivAt (Work.FTS.H2.PhiStarE.At N (j + 1))
      (-((j : ℝ) + 3) * Work.FTS.H2.PhiStarE.At N (j + 2) z) z := by
  have h := Work.FTS.H2.PhiStarE.At_hasDerivAt N hN (j + 1) hz
  convert h using 1
  push_cast
  ring

/-- Product rule for the basic pair `(1+z)·At N (j+1)`. -/
lemma AtLin_hasDerivAt_one_add_mul (N : ℝ) (hN : 0 ≤ N) (j : ℕ) {z : ℝ} (hz : 0 ≤ z) :
    HasDerivAt (fun y : ℝ => (1 + y) * Work.FTS.H2.PhiStarE.At N (j + 1) y)
      (Work.FTS.H2.PhiStarE.At N (j + 1) z
        - ((j : ℝ) + 3) * ((1 + z) * Work.FTS.H2.PhiStarE.At N (j + 2) z)) z := by
  have h1 : HasDerivAt (fun y : ℝ => 1 + y) 1 z := by
    simpa using (hasDerivAt_id z).const_add 1
  have h' : HasDerivAt (fun y : ℝ => (1 + y) * Work.FTS.H2.PhiStarE.At N (j + 1) y)
      (1 * Work.FTS.H2.PhiStarE.At N (j + 1) z
        + (1 + z) * (-((j : ℝ) + 3) * Work.FTS.H2.PhiStarE.At N (j + 2) z)) z :=
    h1.mul (AtLin_hasDerivAt_At_succ N hN j hz)
  convert h' using 1
  ring

/-- The derivative of the two-term combination `AtLinComb N j`. -/
lemma AtLin_hasDerivAt_comb (N : ℝ) (hN : 0 ≤ N) (j : ℕ) {z : ℝ} (hz : 0 ≤ z) :
    HasDerivAt (AtLinComb N j)
      (AtLinC1 j * (-((j : ℝ) + 2) * Work.FTS.H2.PhiStarE.At N (j + 1) z)
        + AtLinC2 j * (Work.FTS.H2.PhiStarE.At N (j + 1) z
          - ((j : ℝ) + 3) * ((1 + z) * Work.FTS.H2.PhiStarE.At N (j + 2) z))) z := by
  have h1 : HasDerivAt (fun y : ℝ => AtLinC1 j * Work.FTS.H2.PhiStarE.At N j y)
      (AtLinC1 j * (-((j : ℝ) + 2) * Work.FTS.H2.PhiStarE.At N (j + 1) z)) z :=
    (Work.FTS.H2.PhiStarE.At_hasDerivAt N hN j hz).const_mul (AtLinC1 j)
  have h2 : HasDerivAt
      (fun y : ℝ => AtLinC2 j * ((1 + y) * Work.FTS.H2.PhiStarE.At N (j + 1) y))
      (AtLinC2 j * (Work.FTS.H2.PhiStarE.At N (j + 1) z
        - ((j : ℝ) + 3) * ((1 + z) * Work.FTS.H2.PhiStarE.At N (j + 2) z))) z :=
    (AtLin_hasDerivAt_one_add_mul N hN j hz).const_mul (AtLinC2 j)
  have h' : HasDerivAt
      (fun y : ℝ => AtLinC1 j * Work.FTS.H2.PhiStarE.At N j y
        + AtLinC2 j * ((1 + y) * Work.FTS.H2.PhiStarE.At N (j + 1) y))
      (AtLinC1 j * (-((j : ℝ) + 2) * Work.FTS.H2.PhiStarE.At N (j + 1) z)
        + AtLinC2 j * (Work.FTS.H2.PhiStarE.At N (j + 1) z
          - ((j : ℝ) + 3) * ((1 + z) * Work.FTS.H2.PhiStarE.At N (j + 2) z))) z :=
    h1.add h2
  exact h'

/-- The base case `k = 1`: `deriv ((1+z)·At N 0 z) = At N 0 z - 2·(1+z)·At N 1 z`. -/
lemma AtLin_hasDerivAt_base (N : ℝ) (hN : 0 ≤ N) {z : ℝ} (hz : 0 ≤ z) :
    HasDerivAt (fun w : ℝ => (1 + w) * Work.FTS.H2.PhiStarE.At N 0 w)
      (Work.FTS.H2.PhiStarE.At N 0 z
        - 2 * ((1 + z) * Work.FTS.H2.PhiStarE.At N 1 z)) z := by
  have h1 : HasDerivAt (fun y : ℝ => 1 + y) 1 z := by
    simpa using (hasDerivAt_id z).const_add 1
  have h2 : HasDerivAt (Work.FTS.H2.PhiStarE.At N 0)
      (-2 * Work.FTS.H2.PhiStarE.At N 1 z) z := by
    have h := Work.FTS.H2.PhiStarE.At_hasDerivAt N hN 0 hz
    convert h using 1
    norm_num
  have h' : HasDerivAt (fun y : ℝ => (1 + y) * Work.FTS.H2.PhiStarE.At N 0 y)
      (1 * Work.FTS.H2.PhiStarE.At N 0 z + (1 + z) * (-2 * Work.FTS.H2.PhiStarE.At N 1 z)) z :=
    h1.mul h2
  convert h' using 1
  ring

/-- **The explicit formula for the iterated derivatives.**  For `N ≥ 0` and every `j`,
on `(0,∞)` the `(j+1)`-st derivative of `w ↦ (1+w)·At N 0 w` is `AtLinComb N j`, i.e.
`(-1)^j (j+1)! (j+1)·At N j + (-1)^(j+1) (j+2)!·(1+z)·At N (j+1)`. -/
theorem AtLin_iter_formula (N : ℝ) (hN : 0 ≤ N) (j : ℕ) :
    EqOn ((deriv^[j + 1]) (fun w => (1 + w) * Work.FTS.H2.PhiStarE.At N 0 w))
      (AtLinComb N j) (Set.Ioi 0) := by
  induction j with
  | zero =>
      intro z hz
      have hz0 : 0 ≤ z := le_of_lt hz
      rw [Function.iterate_one, (AtLin_hasDerivAt_base N hN hz0).deriv, AtLinComb]
      have h1 : AtLinC1 0 = 1 := by norm_num [AtLinC1, Nat.factorial]
      have h2 : AtLinC2 0 = -2 := by norm_num [AtLinC2, Nat.factorial]
      rw [h1, h2]
      ring
  | succ j ih =>
      intro z hz
      have hz0 : 0 ≤ z := le_of_lt hz
      rw [Function.iterate_succ_apply']
      have hev : (deriv^[j + 1]) (fun w => (1 + w) * Work.FTS.H2.PhiStarE.At N 0 w)
          =ᶠ[𝓝 z] AtLinComb N j := by
        filter_upwards [isOpen_Ioi.mem_nhds hz] with y hy
        exact ih hy
      rw [hev.deriv_eq, (AtLin_hasDerivAt_comb N hN j hz0).deriv]
      simp only [AtLinComb]
      rw [AtLinC1_succ, AtLinC2_succ]
      ring

/-- **The target estimate.**  There is a universal constant `C` with
`|(1+z)^k · (deriv^[k]) (w ↦ (1+w)·At N 0 w) z| ≤ C/N` for all `N ≥ 2`, `z > 0`, `k ≤ 7`.
The constant `3·10^7` is (very) far from optimal: the sharp bound for `k ≤ 7` is
`7·7!·2^8 + 8!·2^9 = 29675520`. -/
theorem At_linear_deriv_bound : ∃ C : ℝ, 0 < C ∧
    ∀ (N z : ℝ) (k : ℕ), 2 ≤ N → 0 < z → k ≤ 7 →
      |(1 + z) ^ k * (deriv^[k]) (fun w => (1 + w) * Work.FTS.H2.PhiStarE.At N 0 w) z| ≤ C / N := by
  refine ⟨30000000, by norm_num, fun N z k hN hz hk => ?_⟩
  have hNpos : (0 : ℝ) < N := by linarith
  have hN0 : (0 : ℝ) ≤ N := le_of_lt hNpos
  have hz0 : (0 : ℝ) ≤ z := le_of_lt hz
  rcases k with _ | j
  · rw [Function.iterate_zero_apply, pow_zero, one_mul]
    have h := AtLin_shift_bound N hN 1 0 (by norm_num) hz0
    have h4 : (2 : ℝ) ^ (1 + 1) / N = 4 / N := by norm_num
    rw [pow_one, h4] at h
    exact h.trans (div_le_div_of_nonneg_right (by norm_num) hN0)
  · have hk6 : j ≤ 6 := by omega
    rw [AtLin_iter_formula N hN0 j hz]
    have heq : (1 + z) ^ (j + 1) * AtLinComb N j z
        = AtLinC1 j * ((1 + z) ^ (j + 1) * Work.FTS.H2.PhiStarE.At N j z)
          + AtLinC2 j * ((1 + z) ^ (j + 2) * Work.FTS.H2.PhiStarE.At N (j + 1) z) := by
      rw [AtLinComb, pow_succ]
      ring
    rw [heq]
    have hb1 := AtLin_shift_bound N hN (j + 1) j (le_refl _) hz0
    have hb2 := AtLin_shift_bound N hN (j + 2) (j + 1) (by omega) hz0
    have hp1 : (2 : ℝ) ^ (j + 1 + 1) / N ≤ 256 / N := by
      apply div_le_div_of_nonneg_right _ hN0
      have h8 : j + 1 + 1 ≤ 8 := by omega
      calc (2 : ℝ) ^ (j + 1 + 1) ≤ 2 ^ 8 := pow_le_pow_right₀ (by norm_num) h8
        _ = 256 := by norm_num
    have hp2 : (2 : ℝ) ^ (j + 2 + 1) / N ≤ 512 / N := by
      apply div_le_div_of_nonneg_right _ hN0
      have h9 : j + 2 + 1 ≤ 9 := by omega
      calc (2 : ℝ) ^ (j + 2 + 1) ≤ 2 ^ 9 := pow_le_pow_right₀ (by norm_num) h9
        _ = 512 := by norm_num
    calc |AtLinC1 j * ((1 + z) ^ (j + 1) * Work.FTS.H2.PhiStarE.At N j z)
            + AtLinC2 j * ((1 + z) ^ (j + 2) * Work.FTS.H2.PhiStarE.At N (j + 1) z)|
        ≤ |AtLinC1 j * ((1 + z) ^ (j + 1) * Work.FTS.H2.PhiStarE.At N j z)|
            + |AtLinC2 j * ((1 + z) ^ (j + 2) * Work.FTS.H2.PhiStarE.At N (j + 1) z)| :=
          abs_add_le _ _
      _ = |AtLinC1 j| * |(1 + z) ^ (j + 1) * Work.FTS.H2.PhiStarE.At N j z|
            + |AtLinC2 j| * |(1 + z) ^ (j + 2) * Work.FTS.H2.PhiStarE.At N (j + 1) z| := by
          simp only [abs_mul]
      _ ≤ 35280 * (256 / N) + 40320 * (512 / N) := by
          refine add_le_add ?_ ?_
          · exact mul_le_mul (AtLin_absC1_le j hk6) (hb1.trans hp1) (abs_nonneg _) (by norm_num)
          · exact mul_le_mul (AtLin_absC2_le j hk6) (hb2.trans hp2) (abs_nonneg _) (by norm_num)
      _ = 29675520 / N := by ring
      _ ≤ 30000000 / N := div_le_div_of_nonneg_right (by norm_num) hN0

end Work.FTS.PhiStar
end
end
-- ===== merged: Submission.Work.FTS.PhiStar.FlatWAux.TsumLopDerivAux.Lop_iter_deriv_bound =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open Filter

namespace Work.FTS.PhiStar.FlatWAux.TsumLopDerivAux

/-- **Value bound.**  For `r + j ≤ 8` the `j`-th `Lop`-iterate of the `r`-th `θ`-derivative of
`q m` is bounded on `[a,b]` by a constant (independent of `m`) times `B m`. -/
private theorem value_bound (q : ℕ → ℝ → ℝ) (B : ℕ → ℝ)
    (hq : ∀ m : ℕ, ContDiffOn ℝ 8 (q m) (Set.Ioo 0 (Real.pi / 2)))
    (hqb : ∀ (m r : ℕ), r ≤ 8 → ∀ θ : ℝ, θ ∈ Set.Ioo 0 (Real.pi / 2) →
      |iteratedDeriv r (q m) θ| ≤ B m)
    {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) (hb : b < Real.pi / 2) :
    ∀ (j r : ℕ), r + j ≤ 8 → ∃ K : ℝ, 0 ≤ K ∧
      ∀ (m : ℕ) (θ : ℝ), θ ∈ Set.Icc a b →
        |(Work.Spaces.Lop^[j]) (iteratedDeriv r (q m)) θ| ≤ K * B m := by
  have hUopen : IsOpen (Set.Ioo 0 (Real.pi / 2)) := isOpen_Ioo
  have hsub : Set.Icc a b ⊆ Set.Ioo 0 (Real.pi / 2) := fun θ hθ =>
    ⟨lt_of_lt_of_le ha hθ.1, lt_of_le_of_lt hθ.2 hb⟩
  intro j
  induction j using Nat.strong_induction_on with
  | h j ih =>
    intro r hr
    rcases Nat.eq_zero_or_pos j with hj | hj
    · subst hj
      refine ⟨1, zero_le_one, fun m θ hθ => ?_⟩
      rw [Function.iterate_zero_apply, one_mul]
      exact hqb m r (by omega) θ (hsub hθ)
    · obtain ⟨n, rfl⟩ : ∃ n, j = n + 1 := ⟨j - 1, by omega⟩
      -- the Leibniz recursion for the level `n+1`
      have hstep : ∀ (m : ℕ) (θ : ℝ), θ ∈ Set.Ioo 0 (Real.pi / 2) →
          (Work.Spaces.Lop^[n + 1]) (iteratedDeriv r (q m)) θ
            = ∑ k ∈ Finset.range (n + 1), (n.choose k : ℝ) *
                (Asf k θ * (Work.Spaces.Lop^[n - k]) (iteratedDeriv (r + 1) (q m)) θ) := by
        intro m θ hθ
        have hg : ContDiffOn ℝ (((n + 1 : ℕ)) : WithTop ℕ∞) (iteratedDeriv r (q m))
            (Set.Ioo 0 (Real.pi / 2)) := by
          refine contDiffOn_iteratedDeriv hUopen r (n + 1) ?_
          exact (hq m).of_le (by exact_mod_cast (show (n + 1) + r ≤ 8 by omega))
        have hrec := Lop_iter_succ_eq_sum n hUopen hg θ hθ
        rw [hrec]
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [← iteratedDeriv_succ]
      -- the induction hypotheses, one for each summand
      have hIH : ∀ k : ℕ, ∃ K : ℝ, 0 ≤ K ∧ (k ∈ Finset.range (n + 1) →
          ∀ (m : ℕ) (θ : ℝ), θ ∈ Set.Icc a b →
            |(Work.Spaces.Lop^[n - k]) (iteratedDeriv (r + 1) (q m)) θ| ≤ K * B m) := by
        intro k
        by_cases hk : k ∈ Finset.range (n + 1)
        · obtain ⟨K, hK0, hKb⟩ :=
            ih (n - k) (by have := Finset.mem_range.mp hk; omega) (r + 1) (by omega)
          exact ⟨K, hK0, fun _ => hKb⟩
        · exact ⟨0, le_rfl, fun hk' => absurd hk' hk⟩
      choose Kf hKf0 hKfb using hIH
      obtain ⟨C, _, hC0, _, hCb, _⟩ := Asf_bound_le n hab
      refine ⟨∑ k ∈ Finset.range (n + 1), (n.choose k : ℝ) * C * Kf k, ?_, ?_⟩
      · exact Finset.sum_nonneg fun k hk =>
          mul_nonneg (mul_nonneg (Nat.cast_nonneg _) hC0) (hKf0 k)
      · intro m θ hθ
        rw [hstep m θ (hsub hθ)]
        calc |∑ k ∈ Finset.range (n + 1), (n.choose k : ℝ) *
                (Asf k θ * (Work.Spaces.Lop^[n - k]) (iteratedDeriv (r + 1) (q m)) θ)|
            ≤ ∑ k ∈ Finset.range (n + 1), |(n.choose k : ℝ) *
                (Asf k θ * (Work.Spaces.Lop^[n - k]) (iteratedDeriv (r + 1) (q m)) θ)| :=
              Finset.abs_sum_le_sum_abs _ _
          _ ≤ ∑ k ∈ Finset.range (n + 1), ((n.choose k : ℝ) * C * Kf k) * B m := by
              refine Finset.sum_le_sum fun k hk => ?_
              have hA : |Asf k θ| ≤ C :=
                hCb k (Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)) θ hθ
              have hX : |(Work.Spaces.Lop^[n - k]) (iteratedDeriv (r + 1) (q m)) θ|
                  ≤ Kf k * B m := hKfb k hk m θ hθ
              calc |(n.choose k : ℝ) * (Asf k θ *
                      (Work.Spaces.Lop^[n - k]) (iteratedDeriv (r + 1) (q m)) θ)|
                  = (n.choose k : ℝ) * (|Asf k θ| *
                      |(Work.Spaces.Lop^[n - k]) (iteratedDeriv (r + 1) (q m)) θ|) := by
                    rw [abs_mul, abs_mul, abs_of_nonneg (Nat.cast_nonneg (n.choose k))]
                _ ≤ (n.choose k : ℝ) * (C * (Kf k * B m)) := by
                    refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _)
                    exact mul_le_mul hA hX (abs_nonneg _) hC0
                _ = ((n.choose k : ℝ) * C * Kf k) * B m := by ring
          _ = (∑ k ∈ Finset.range (n + 1), (n.choose k : ℝ) * C * Kf k) * B m :=
              (Finset.sum_mul _ _ _).symm

theorem Lop_iter_deriv_bound (q : ℕ → ℝ → ℝ) (B : ℕ → ℝ)
    (hq : ∀ m : ℕ, ContDiffOn ℝ 8 (q m) (Set.Ioo 0 (Real.pi / 2)))
    (hqb : ∀ (m r : ℕ), r ≤ 8 → ∀ θ : ℝ, θ ∈ Set.Ioo 0 (Real.pi / 2) →
      |iteratedDeriv r (q m) θ| ≤ B m) :
    ∀ (i r : ℕ), r + i ≤ 8 → r + i + 1 ≤ 8 → ∀ {a b : ℝ}, 0 < a → a ≤ b →
      b < Real.pi / 2 →
      ∃ K K' : ℝ, 0 ≤ K ∧ 0 ≤ K' ∧
        ∀ (m : ℕ) (θ : ℝ), θ ∈ Set.Icc a b →
          |(Work.Spaces.Lop^[i]) (iteratedDeriv r (q m)) θ| ≤ K * B m ∧
          |deriv ((Work.Spaces.Lop^[i]) (iteratedDeriv r (q m))) θ| ≤ K' * B m := by
  intro i r hri hri' a b ha hab hb
  obtain ⟨K, hK0, hKb⟩ := value_bound q B hq hqb ha hab hb i r hri
  obtain ⟨K₂, hK₂0, hK₂b⟩ := value_bound q B hq hqb ha hab hb (i + 1) r (by omega)
  -- a positive lower bound for `sin (2θ)` on `[a,b]`
  obtain ⟨θ₀, hθ₀, hmin⟩ := isCompact_Icc.exists_isMinOn
    (⟨a, le_rfl, hab⟩ : (Set.Icc a b).Nonempty)
    (by fun_prop : ContinuousOn (fun θ : ℝ => Real.sin (2 * θ)) (Set.Icc a b))
  have hc0 : 0 < Real.sin (2 * θ₀) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith [ha, hθ₀.1]) (by linarith [hθ₀.2, hb])
  refine ⟨K, K₂ / Real.sin (2 * θ₀), hK0, div_nonneg hK₂0 (le_of_lt hc0), ?_⟩
  intro m θ hθ
  refine ⟨hKb m θ hθ, ?_⟩
  have hs0 : 0 < Real.sin (2 * θ) := lt_of_lt_of_le hc0 (hmin hθ)
  have hsne : Real.sin (2 * θ) ≠ 0 := ne_of_gt hs0
  -- `Lop` is `sin (2·)` times the derivative, whence the division identity
  have hkey : (Work.Spaces.Lop^[i + 1]) (iteratedDeriv r (q m)) θ
      = Real.sin (2 * θ) * deriv ((Work.Spaces.Lop^[i]) (iteratedDeriv r (q m))) θ := by
    rw [Function.iterate_succ_apply' Work.Spaces.Lop i (iteratedDeriv r (q m))]
    rfl
  have hdiv : deriv ((Work.Spaces.Lop^[i]) (iteratedDeriv r (q m))) θ
      = (Work.Spaces.Lop^[i + 1]) (iteratedDeriv r (q m)) θ / Real.sin (2 * θ) := by
    rw [eq_div_iff hsne, mul_comm]
    exact hkey.symm
  have hprod : |deriv ((Work.Spaces.Lop^[i]) (iteratedDeriv r (q m))) θ| * Real.sin (2 * θ)
      = |(Work.Spaces.Lop^[i + 1]) (iteratedDeriv r (q m)) θ| := by
    rw [hdiv, abs_div, abs_of_pos hs0, div_mul_cancel₀ _ hsne]
  have hA : |deriv ((Work.Spaces.Lop^[i]) (iteratedDeriv r (q m))) θ| * Real.sin (2 * θ₀)
      ≤ K₂ * B m := by
    refine le_trans (mul_le_mul_of_nonneg_left (hmin hθ) (abs_nonneg _)) ?_
    rw [hprod]
    exact hK₂b m θ hθ
  calc |deriv ((Work.Spaces.Lop^[i]) (iteratedDeriv r (q m))) θ|
      ≤ (K₂ * B m) / Real.sin (2 * θ₀) := (le_div_iff₀ hc0).mpr hA
    _ = (K₂ / Real.sin (2 * θ₀)) * B m := by ring

end Work.FTS.PhiStar.FlatWAux.TsumLopDerivAux
end
end
-- ===== merged: Submission.Work.FTS.PhiStar.FlatWAux.TsumLopDerivAux.tsum_Lop_iter_deriv_hasDerivAt =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open scoped Real Topology
open Filter

namespace Work.FTS.PhiStar.FlatWAux.TsumLopDerivAux

/-- Smoothness input in `HasDerivAt` form: if `q` is `C^8` on an open set `U` and `i ≤ 6`,
then `(Lop^[i]) (deriv q)` is differentiable at every point of `U`.

Indeed `deriv q = iteratedDeriv 1 q` is `C^7` on `U` (`contDiffOn_iteratedDeriv`) and
`Lop^[i]` costs `i` orders, so `(Lop^[i]) (deriv q)` is `C^{7-i} ⊆ C^1` on `U`. -/
theorem differentiableAt_Lop_iter_deriv {U : Set ℝ} (hU : IsOpen U) {q : ℝ → ℝ}
    (hq : ContDiffOn ℝ 8 q U) {i : ℕ} (hi : i ≤ 6) {y : ℝ} (hy : y ∈ U) :
    DifferentiableAt ℝ ((Work.Spaces.Lop^[i]) (deriv q)) y := by
  have h1 : ContDiffOn ℝ (((7 : ℕ)) : WithTop ℕ∞) (iteratedDeriv 1 q) U :=
    Work.FTS.PhiStar.FlatWAux.contDiffOn_iteratedDeriv hU 1 7 (by simpa using hq)
  have hsub : 7 - i + i = 7 := Nat.sub_add_cancel (by omega)
  have h3 : ContDiffOn ℝ (((7 - i : ℕ)) : WithTop ℕ∞)
      ((Work.Spaces.Lop^[i]) (iteratedDeriv 1 q)) U :=
    Work.FTS.PhiStar.FlatWAux.contDiffOn_Lop_iter i hU (7 - i) (by
      have hcast : (((7 - i + i : ℕ)) : WithTop ℕ∞) = (((7 : ℕ)) : WithTop ℕ∞) := by
        rw [hsub]
      rw [hcast]; exact h1)
  have h2 : ContDiffOn ℝ (((7 - i : ℕ)) : WithTop ℕ∞) ((Work.Spaces.Lop^[i]) (deriv q)) U := by
    simpa only [iteratedDeriv_one] using h3
  refine (h2.contDiffAt (hU.mem_nhds hy)).differentiableAt ?_
  have h : (1 : ℕ) ≤ 7 - i := by omega
  have h' : ((1 : ℕ) : WithTop ℕ∞) ≤ ((7 - i : ℕ) : WithTop ℕ∞) := Nat.cast_le.mpr h
  exact ne_of_gt (lt_of_lt_of_le (zero_lt_one : (0 : WithTop ℕ∞) < 1) h')

theorem tsum_Lop_iter_deriv_hasDerivAt (c : ℕ → ℝ) (q : ℕ → ℝ → ℝ) (B : ℕ → ℝ)
    (hcB : Summable fun m : ℕ => |c m| * B m)
    (hq : ∀ m : ℕ, ContDiffOn ℝ 8 (q m) (Set.Ioo 0 (Real.pi / 2)))
    (i : ℕ) (hi : i ≤ 6)
    {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) (hb : b < Real.pi / 2)
    (K' Kv : ℝ) (hK' : 0 ≤ K') (hKv : 0 ≤ Kv)
    (hbnd : ∀ (m : ℕ) (θ : ℝ), θ ∈ Set.Icc a b →
      |deriv ((Work.Spaces.Lop^[i]) (deriv (q m))) θ| ≤ K' * B m)
    (hbval : ∀ (m : ℕ) (θ : ℝ), θ ∈ Set.Icc a b →
      |(Work.Spaces.Lop^[i]) (deriv (q m)) θ| ≤ Kv * B m)
    (θ : ℝ) (hθ : θ ∈ Set.Ioo a b) :
    HasDerivAt (fun y : ℝ => ∑' m : ℕ, c m * (Work.Spaces.Lop^[i]) (deriv (q m)) y)
      (∑' m : ℕ, c m * deriv ((Work.Spaces.Lop^[i]) (deriv (q m))) θ) θ := by
  -- the interval `(a,b)` is an open neighbourhood of `θ` and sits inside the domain of `q m`
  have hsub : ∀ y ∈ Set.Ioo a b, y ∈ Set.Ioo 0 (Real.pi / 2) := fun y hy =>
    ⟨by linarith [hy.1, ha], by linarith [hy.2, hb]⟩
  refine hasDerivAt_tsum_of_isPreconnected
    (u := fun m : ℕ => |c m| * (K' * B m))
    (g := fun m (y : ℝ) => c m * (Work.Spaces.Lop^[i]) (deriv (q m)) y)
    (g' := fun m (y : ℝ) => c m * deriv ((Work.Spaces.Lop^[i]) (deriv (q m))) y)
    (t := Set.Ioo a b) (y₀ := θ) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · -- the dominating family `m ↦ |c m| * (K' * B m)` is summable
    exact (hcB.mul_left K').congr (fun m => by ring)
  · exact isOpen_Ioo
  · exact isPreconnected_Ioo
  · -- each summand is differentiable on `(a,b)`, with the announced derivative
    intro m y hy
    exact (differentiableAt_Lop_iter_deriv isOpen_Ioo (hq m) hi (hsub y hy)).hasDerivAt.const_mul
      (c m)
  · -- bound on the derivatives
    intro m y hy
    rw [Real.norm_eq_abs, abs_mul]
    exact mul_le_mul_of_nonneg_left (hbnd m y ⟨le_of_lt hy.1, le_of_lt hy.2⟩) (abs_nonneg _)
  · exact ⟨hθ.1, hθ.2⟩
  · -- convergence of the series of values at `θ`
    refine Summable.of_norm_bounded (hcB.mul_left Kv) (fun m => ?_)
    rw [Real.norm_eq_abs, abs_mul]
    calc |c m| * |(Work.Spaces.Lop^[i]) (deriv (q m)) θ|
        ≤ |c m| * (Kv * B m) :=
          mul_le_mul_of_nonneg_left (hbval m θ ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩) (abs_nonneg _)
      _ = Kv * (|c m| * B m) := by ring
  · exact hθ

end Work.FTS.PhiStar.FlatWAux.TsumLopDerivAux
end
-- ===== merged: Submission.Work.FTS.PhiStar.Honesty.IPMemOfHkMem =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `HkMem α 0 F ⟹ IPMem F F`

At level `k = 0` the `H^k`-integrand `Work.Spaces.HkIntegrand α 0 F` collapses to the single
square `(F z θ · w z / sin(2θ)^{η/2})²` (the `D_z`-sum has the one term `i = 0` and the mixed
double sum is empty), while the weighted pairing integrand of `AngSecond.IPMem F F` is
`F z θ · F z θ · w z² · σ θ` with `σ θ = sin(2θ)^{-η}`.  The two agree pointwise on `Iθ`
(`AngSecond.sq_mul_W`, whose endpoint case `sin(2θ) = 0` is handled by `Real.zero_rpow`), so the
honesty of the first transfers verbatim to the honesty of the second, both slicewise in `θ` and
then in `z`.

This is the level-`0` bridge `HkMem α 0 F → IPMem F F` used by the `PhiStar/Honesty` layer; a
sibling statement `Work.FTS.EllipticEst.AngClean.HkMem_zero_IPMem` proves the same fact in the
`AngClean` namespace.
-/

namespace Work.FTS.PhiStar.Honesty

open MeasureTheory

/-- At `k = 0` the `H^k`-integrand collapses to a single square: the `D_z`-sum has the one term
`i = 0` and the mixed double sum is empty. -/
private lemma HkIntegrand_zero_eq_prv (α : ℝ) (F : ℝ → ℝ → ℝ) (z θ : ℝ) :
    Work.Spaces.HkIntegrand α 0 F z θ
      = (F z θ * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2 := by
  simp [Work.Spaces.HkIntegrand]


end Work.FTS.PhiStar.Honesty
end
-- ===== merged: Submission.Work.FTS.PhiStar.Honesty.RadGreenAll.radGreen_abs_le_all =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

set_option autoImplicit false

open MeasureTheory Set

namespace Work.FTS.PhiStar.Honesty.RadGreenAll

/-- **Tail piece, valid for `0 ≤ p`.**

For `p ≥ 0`, `z > 0` and `c` with `∫_0^∞ c² < ∞`,

  `|z ^ p · ∫_{Ioi z} c t · t ^ (-p-1)| ≤ √(∫_{Ioi 0} c²) · z ^ (-1/2) / √(2p+1)`.

This is `Work.EllipticEst.ModalSolution.radGreen_tail_bound` with the hypothesis `0 < p` relaxed
to `0 ≤ p` (the case `p = 0`, i.e. `m = 0`, is exactly what `radGreen_abs_le_all` needs).  The
proof is unchanged: Cauchy–Schwarz for `√(c²)` against `t ^ (-p-1)` on `Ioi z`, using
`∫_z^∞ t ^ (-2p-2) = z ^ (-2p-1)/(2p+1)`. -/
theorem radGreen_tail_bound_nonneg (c : ℝ → ℝ)
    (hc : MeasureTheory.IntegrableOn (fun t => c t ^ 2) (Set.Ioi 0))
    {p z : ℝ} (hp : 0 ≤ p) (hz : 0 < z) :
    |z ^ p * (∫ t in Set.Ioi z, c t * t ^ (-p - 1))| ≤
      Real.sqrt (∫ t in Set.Ioi 0, c t ^ 2) * z ^ (-(1 / 2) : ℝ) / Real.sqrt (2 * p + 1) := by
  have hz0 : 0 ≤ z := le_of_lt hz
  have h2p1 : 0 < 2 * p + 1 := by linarith
  have hsub : Set.Ioi z ⊆ Set.Ioi (0 : ℝ) := Set.Ioi_subset_Ioi hz0
  -- ## the factor `u t = |c t| = √(c t ^ 2)`
  have hu_ae : AEStronglyMeasurable (fun t => Real.sqrt (c t ^ 2)) (volume.restrict (Set.Ioi 0)) :=
    Real.continuous_sqrt.comp_aestronglyMeasurable hc.1
  have hu_m : AEStronglyMeasurable (fun t => Real.sqrt (c t ^ 2)) (volume.restrict (Set.Ioi z)) :=
    hu_ae.mono_set hsub
  have hu_int : Integrable (fun t => (Real.sqrt (c t ^ 2)) ^ 2) (volume.restrict (Set.Ioi z)) := by
    refine (hc.mono_set hsub).congr (Filter.Eventually.of_forall (fun t => ?_))
    exact (Real.sq_sqrt (sq_nonneg (c t))).symm
  have hu : MemLp (fun t => Real.sqrt (c t ^ 2)) 2 (volume.restrict (Set.Ioi z)) :=
    (memLp_two_iff_integrable_sq hu_m).mpr hu_int
  -- ## the weight `v t = t ^ (-p-1)`
  have hcont_v : ContinuousOn (fun t : ℝ => t ^ (-p - 1)) (Set.Ioi z) :=
    continuousOn_id.rpow_const (fun t ht => Or.inl (ne_of_gt (lt_trans hz ht)))
  have hv_m : AEStronglyMeasurable (fun t : ℝ => t ^ (-p - 1)) (volume.restrict (Set.Ioi z)) :=
    hcont_v.aestronglyMeasurable measurableSet_Ioi
  have hptv : ∀ t : ℝ, 0 < t → t ^ (-2 * p - 2) = (t ^ (-p - 1)) ^ 2 := by
    intro t ht
    rw [pow_two, ← Real.rpow_add ht]
    congr 1
    ring
  have hv_int : Integrable (fun t => (t ^ (-p - 1)) ^ 2) (volume.restrict (Set.Ioi z)) := by
    refine (integrableOn_Ioi_rpow_of_lt (a := -2 * p - 2) (by linarith) hz).congr ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact hptv t (lt_trans hz ht)
  have hv : MemLp (fun t => t ^ (-p - 1)) 2 (volume.restrict (Set.Ioi z)) :=
    (memLp_two_iff_integrable_sq hv_m).mpr hv_int
  -- ## the value of `∫_z^∞ t ^ (-2p-2)`
  have hVval : (∫ t in Set.Ioi z, t ^ (-2 * p - 2)) = z ^ (-2 * p - 1) / (2 * p + 1) := by
    have h := integral_Ioi_rpow_of_lt (a := -2 * p - 2) (c := z) (by linarith) hz
    have h' : -z ^ ((-2 * p - 2 : ℝ) + 1) / ((-2 * p - 2 : ℝ) + 1)
        = z ^ (-2 * p - 1) / (2 * p + 1) := by
      rw [show ((-2 * p - 2 : ℝ) + 1) = -(2 * p + 1) by ring]
      rw [neg_div_neg_eq]
      rw [show -(2 * p + 1 : ℝ) = -2 * p - 1 by ring]
    rw [h, h']
  have hIntV : (∫ t in Set.Ioi z, (t ^ (-p - 1)) ^ 2) = z ^ (-2 * p - 1) / (2 * p + 1) := by
    rw [show (∫ t in Set.Ioi z, (t ^ (-p - 1)) ^ 2) = ∫ t in Set.Ioi z, t ^ (-2 * p - 2) from
      integral_congr_ae (by
        filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
        exact (hptv t (lt_trans hz ht)).symm)]
    exact hVval
  have hIntU : (∫ t in Set.Ioi z, (Real.sqrt (c t ^ 2)) ^ 2) = ∫ t in Set.Ioi z, c t ^ 2 :=
    integral_congr_ae (Filter.Eventually.of_forall (fun t => Real.sq_sqrt (sq_nonneg (c t))))
  -- ## Cauchy–Schwarz
  have hCS := Work.FTS.EllipticEst.remov.Ebs.abs_integral_mul_le_sqrt hu hv
  have hCS' : (∫ t in Set.Ioi z, Real.sqrt (c t ^ 2) * t ^ (-p - 1)) ≤
      Real.sqrt (∫ t in Set.Ioi z, c t ^ 2) * Real.sqrt (z ^ (-2 * p - 1) / (2 * p + 1)) := by
    refine le_trans (le_abs_self _) (le_trans hCS ?_)
    rw [hIntU, hIntV]
  -- ## the tail integral itself, bounded by the `L²` pairing
  have hJ : |∫ t in Set.Ioi z, c t * t ^ (-p - 1)| ≤
      ∫ t in Set.Ioi z, Real.sqrt (c t ^ 2) * t ^ (-p - 1) := by
    have h1 : |∫ t in Set.Ioi z, c t * t ^ (-p - 1)| ≤
        ∫ t in Set.Ioi z, ‖c t * t ^ (-p - 1)‖ := by
      simpa only [Real.norm_eq_abs] using
        (norm_integral_le_integral_norm (μ := volume.restrict (Set.Ioi z))
          (f := fun t => c t * t ^ (-p - 1)))
    refine le_trans h1 (le_of_eq ?_)
    refine integral_congr_ae ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have ht0 : 0 < t := lt_trans hz ht
    rw [Real.norm_eq_abs, abs_mul, Real.sqrt_sq_eq_abs,
      abs_of_pos (Real.rpow_pos_of_pos ht0 (-p - 1))]
  have hmain : |∫ t in Set.Ioi z, c t * t ^ (-p - 1)| ≤
      Real.sqrt (∫ t in Set.Ioi z, c t ^ 2) * Real.sqrt (z ^ (-2 * p - 1) / (2 * p + 1)) :=
    le_trans hJ hCS'
  -- ## monotonicity of the `L²` mass in the domain
  have hUQ : (∫ t in Set.Ioi z, c t ^ 2) ≤ ∫ t in Set.Ioi 0, c t ^ 2 := by
    refine setIntegral_mono_set (μ := volume) (s := Set.Ioi z) (t := Set.Ioi 0) hc ?_ ?_
    · exact Filter.Eventually.of_forall (fun t => sq_nonneg (c t))
    · exact Filter.Eventually.of_forall (fun t ht => lt_trans hz ht)
  have hsqrtUQ : Real.sqrt (∫ t in Set.Ioi z, c t ^ 2) ≤ Real.sqrt (∫ t in Set.Ioi 0, c t ^ 2) :=
    Real.sqrt_le_sqrt hUQ
  -- ## the weight computation
  have hW : z ^ p * Real.sqrt (z ^ (-2 * p - 1) / (2 * p + 1)) =
      z ^ (-(1 / 2) : ℝ) / Real.sqrt (2 * p + 1) := by
    have hzW : 0 ≤ z ^ (-2 * p - 1) := le_of_lt (Real.rpow_pos_of_pos hz _)
    have hsq : Real.sqrt (z ^ (-2 * p - 1)) = z ^ (-p - (1 / 2)) := by
      rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hz0]
      rw [show (-2 * p - 1) * (1 / 2) = -p - (1 / 2) by ring]
    rw [Real.sqrt_div hzW (2 * p + 1), hsq]
    rw [← mul_div_assoc, ← Real.rpow_add hz]
    rw [show p + (-p - (1 / 2)) = -(1 / 2 : ℝ) by ring]
  have hzp : 0 < z ^ p := Real.rpow_pos_of_pos hz p
  calc |z ^ p * (∫ t in Set.Ioi z, c t * t ^ (-p - 1))|
      = z ^ p * |∫ t in Set.Ioi z, c t * t ^ (-p - 1)| := by
        rw [abs_mul, abs_of_pos hzp]
    _ ≤ z ^ p * (Real.sqrt (∫ t in Set.Ioi z, c t ^ 2) *
          Real.sqrt (z ^ (-2 * p - 1) / (2 * p + 1))) :=
        mul_le_mul_of_nonneg_left hmain (le_of_lt hzp)
    _ = Real.sqrt (∫ t in Set.Ioi z, c t ^ 2) *
          (z ^ p * Real.sqrt (z ^ (-2 * p - 1) / (2 * p + 1))) := by ring
    _ = Real.sqrt (∫ t in Set.Ioi z, c t ^ 2) *
          (z ^ (-(1 / 2) : ℝ) / Real.sqrt (2 * p + 1)) := by rw [hW]
    _ ≤ Real.sqrt (∫ t in Set.Ioi 0, c t ^ 2) *
          (z ^ (-(1 / 2) : ℝ) / Real.sqrt (2 * p + 1)) :=
        mul_le_mul_of_nonneg_right hsqrtUQ
          (div_nonneg (le_of_lt (Real.rpow_pos_of_pos hz _)) (Real.sqrt_nonneg _))
    _ = Real.sqrt (∫ t in Set.Ioi 0, c t ^ 2) * z ^ (-(1 / 2) : ℝ) / Real.sqrt (2 * p + 1) := by
        rw [mul_div_assoc]

/-- **Tail piece without the denominator.**  Since `2p + 1 ≥ 1` for `p ≥ 0`, the previous bound
gives the cleaner estimate `|z ^ p ∫_{Ioi z} c t ^ (-p-1)| ≤ √(∫ c²) · z ^ (-1/2)`. -/
theorem radGreen_tail_le_nonneg (c : ℝ → ℝ)
    (hc : MeasureTheory.IntegrableOn (fun t => c t ^ 2) (Set.Ioi 0))
    {p z : ℝ} (hp : 0 ≤ p) (hz : 0 < z) :
    |z ^ p * (∫ t in Set.Ioi z, c t * t ^ (-p - 1))| ≤
      Real.sqrt (∫ t in Set.Ioi 0, c t ^ 2) * z ^ (-(1 / 2) : ℝ) := by
  have h := radGreen_tail_bound_nonneg c hc hp hz
  have h1 : 1 ≤ Real.sqrt (2 * p + 1) := by
    have hs : Real.sqrt (1 : ℝ) ≤ Real.sqrt (2 * p + 1) :=
      Real.sqrt_le_sqrt (by linarith)
    rwa [Real.sqrt_one] at hs
  have hpos : 0 < Real.sqrt (2 * p + 1) := lt_of_lt_of_le zero_lt_one h1
  have hA : 0 ≤ Real.sqrt (∫ t in Set.Ioi 0, c t ^ 2) * z ^ (-(1 / 2) : ℝ) :=
    mul_nonneg (Real.sqrt_nonneg _) (le_of_lt (Real.rpow_pos_of_pos hz _))
  calc |z ^ p * (∫ t in Set.Ioi z, c t * t ^ (-p - 1))|
      ≤ Real.sqrt (∫ t in Set.Ioi 0, c t ^ 2) * z ^ (-(1 / 2) : ℝ) / Real.sqrt (2 * p + 1) := h
    _ ≤ Real.sqrt (∫ t in Set.Ioi 0, c t ^ 2) * z ^ (-(1 / 2) : ℝ) := by
        rw [div_le_iff₀ hpos]
        exact le_mul_of_one_le_right hA h1

/-- **The `m`-uniform Green bound.**  For `0 < α ≤ 1`, every `m : ℕ`, `z > 0` and `c` with
`∫_{Ioi 0} c² < ∞`,

  `|radGreen α m c z| ≤ 2 · rgK α m · √(∫_{Ioi 0} c²) · z ^ (-1/2)`.

Both Green pieces are bounded by `√(∫ c²) · z ^ (-1/2)` — the head via `radGreen_head_shaped`
(with `r = rgQ α m ≥ 1`, using `α ≤ 1`) together with `√(2·rgQ α m - 1) ≥ 1`, the tail via
`radGreen_tail_le_nonneg` (with `rgP α m ≥ 0`) together with `√(2·rgP α m + 1) ≥ 1` — and the
factor `rgK α m` is pulled out of the absolute value.  No case distinction on `m` is needed:
`m = 0` corresponds to `rgP α 0 = 0`, which is exactly the borderline case covered by the
relaxed tail bound. -/
theorem radGreen_abs_le_all {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) (m : ℕ) {c : ℝ → ℝ}
    (hc : MeasureTheory.IntegrableOn (fun t => c t ^ 2) (Set.Ioi 0)) {z : ℝ} (hz : 0 < z) :
    |Work.FTS.PhiStar.Radial.radGreen α m c z| ≤
      2 * Work.FTS.EllExist.rgK α m * Real.sqrt (∫ t in Set.Ioi 0, c t ^ 2) * z ^ (-(1 / 2) : ℝ) := by
  have hK : 0 ≤ Work.FTS.EllExist.rgK α m := le_of_lt (Work.FTS.EllExist.rgK_pos hα m)
  have hS : 0 ≤ Real.sqrt (∫ t in Set.Ioi 0, c t ^ 2) := Real.sqrt_nonneg _
  have hzp : 0 ≤ z ^ (-(1 / 2) : ℝ) := le_of_lt (Real.rpow_pos_of_pos hz _)
  have hA : 0 ≤ Real.sqrt (∫ t in Set.Ioi 0, c t ^ 2) * z ^ (-(1 / 2) : ℝ) := mul_nonneg hS hzp
  -- ## the head piece
  have hq1 : 1 ≤ Work.FTS.EllExist.rgQ α m := by
    rw [Work.FTS.EllExist.rgQ, le_div_iff₀ hα]
    have hm : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
    nlinarith
  have hhead : |z ^ (-(Work.FTS.EllExist.rgQ α m)) * Work.FTS.EllExist.rgA α m c z| ≤
      Real.sqrt (∫ t in Set.Ioi 0, c t ^ 2) * z ^ (-(1 / 2) : ℝ) := by
    have h := Work.FTS.PhiStar.Honesty.radGreen_head_shaped c hc
      (r := Work.FTS.EllExist.rgQ α m) hq1 hz
    have hrg : Work.FTS.EllExist.rgA α m c z
        = ∫ t in (0 : ℝ)..z, c t * t ^ (Work.FTS.EllExist.rgQ α m - 1) := by
      simp [Work.FTS.EllExist.rgA, Work.FTS.EllExist.rgF1]
    rw [hrg]
    have h1 : 1 ≤ Real.sqrt (2 * Work.FTS.EllExist.rgQ α m - 1) := by
      have hs : Real.sqrt (1 : ℝ) ≤ Real.sqrt (2 * Work.FTS.EllExist.rgQ α m - 1) :=
        Real.sqrt_le_sqrt (by linarith)
      rwa [Real.sqrt_one] at hs
    have hpos : 0 < Real.sqrt (2 * Work.FTS.EllExist.rgQ α m - 1) := lt_of_lt_of_le zero_lt_one h1
    refine le_trans h ?_
    rw [div_le_iff₀ hpos]
    exact le_mul_of_one_le_right hA h1
  -- ## the tail piece
  have htail : |z ^ (Work.FTS.EllExist.rgP α m) * Work.FTS.EllExist.rgB α m c z| ≤
      Real.sqrt (∫ t in Set.Ioi 0, c t ^ 2) * z ^ (-(1 / 2) : ℝ) := by
    have h := radGreen_tail_le_nonneg c hc (p := Work.FTS.EllExist.rgP α m)
      (Work.FTS.EllExist.rgP_nonneg hα m) hz
    have hrg : Work.FTS.EllExist.rgB α m c z
        = ∫ t in Set.Ioi z, c t * t ^ (-(Work.FTS.EllExist.rgP α m) - 1) := by
      simp [Work.FTS.EllExist.rgB, Work.FTS.EllExist.rgF2]
    rwa [hrg]
  -- ## assembly
  calc |Work.FTS.PhiStar.Radial.radGreen α m c z|
      = Work.FTS.EllExist.rgK α m *
          |z ^ (-(Work.FTS.EllExist.rgQ α m)) * Work.FTS.EllExist.rgA α m c z
            + z ^ (Work.FTS.EllExist.rgP α m) * Work.FTS.EllExist.rgB α m c z| := by
        rw [Work.FTS.EllExist.radGreen_eq, abs_mul, abs_of_nonneg hK]
    _ ≤ Work.FTS.EllExist.rgK α m *
          (|z ^ (-(Work.FTS.EllExist.rgQ α m)) * Work.FTS.EllExist.rgA α m c z|
            + |z ^ (Work.FTS.EllExist.rgP α m) * Work.FTS.EllExist.rgB α m c z|) :=
        mul_le_mul_of_nonneg_left (abs_add_le _ _) hK
    _ ≤ Work.FTS.EllExist.rgK α m *
          (Real.sqrt (∫ t in Set.Ioi 0, c t ^ 2) * z ^ (-(1 / 2) : ℝ)
            + Real.sqrt (∫ t in Set.Ioi 0, c t ^ 2) * z ^ (-(1 / 2) : ℝ)) :=
        mul_le_mul_of_nonneg_left (add_le_add hhead htail) hK
    _ = 2 * Work.FTS.EllExist.rgK α m * Real.sqrt (∫ t in Set.Ioi 0, c t ^ 2)
          * z ^ (-(1 / 2) : ℝ) := by
        ring

end Work.FTS.PhiStar.Honesty.RadGreenAll
end
-- ===== merged: Submission.Work.FTS.PhiStar.Honesty.integrableOn_sq_sEta_of_HkMem =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# Per-slice honesty of the `η`-weighted slice mass, from `HkMem α 0 F`

For `F` in `H^0` (weighted `L²`-membership, `Work.Spaces.HkMem α 0 F`) and every `z > 0`, the
slice mass `θ ↦ F z θ ^ 2 · sin(2θ)^{-η}` is integrable on `Iθ`.

This is exactly the per-slice integrability that `Honesty/cmode_sq_le_slice` consumes as its
hypothesis `hint`.  The point is the `k = 0` collapse of the `H^k` integrand,

  `HkIntegrand α 0 F z θ = (F z θ * w z / sin(2θ)^{η/2})²`  (`simp`), and on `Iθ` this is
  `w₂ z · F z θ ^ 2 · σ θ`  with `w₂ z = w z ^ 2`, `σ θ = sin(2θ)^{-η}` (`AngSecond.sq_mul_W`),

so on each slice the target integrand is the constant `(w₂ z)^{-1}` times the slice integrand of
`HkMem`, which is integrable by hypothesis.  The case `z = 0` is genuinely unavailable: `w 0 = 0`
and `HkMem` constrains nothing at `z = 0`.
-/

namespace Work.FTS.PhiStar.Honesty

open MeasureTheory

/-- The `k = 0` collapse of the `H^k` integrand: for `k = 0` the sum of squares reduces to the
single `D_z^0`-term `(f · w / sin(2θ)^{η/2})²`. -/
private lemma HkIntegrand_zero (α : ℝ) (F : ℝ → ℝ → ℝ) (z θ : ℝ) :
    Work.Spaces.HkIntegrand α 0 F z θ
      = (F z θ * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2 := by
  simp [Work.Spaces.HkIntegrand]

theorem integrableOn_sq_sEta_of_HkMem {α : ℝ} {F : ℝ → ℝ → ℝ}
    (hF : Work.Spaces.HkMem α 0 F) {z : ℝ} (hz : 0 < z) :
    MeasureTheory.IntegrableOn
      (fun θ : ℝ => (F z θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))
      Work.Spaces.Iθ := by
  have hz0 : z ≠ 0 := ne_of_gt hz
  have hw0 : Work.FTS.EllipticEst.AngSecond.w2 z ≠ 0 := by
    have hwz : Work.Spaces.w z ≠ 0 :=
      div_ne_zero (pow_ne_zero 2 (by linarith : (1 : ℝ) + z ≠ 0)) (pow_ne_zero 2 hz0)
    simpa [Work.FTS.EllipticEst.AngSecond.w2] using pow_ne_zero 2 hwz
  -- on `Iθ`, the target integrand is `(w₂ z)^{-1}` times the slice integrand of `HkMem`
  have hEq : ∀ θ ∈ Work.Spaces.Iθ,
      (Work.FTS.EllipticEst.AngSecond.w2 z)⁻¹ * Work.Spaces.HkIntegrand α 0 F z θ
        = (F z θ) ^ 2 * Work.FTS.EllipticEst.AngSecond.sig θ := by
    intro θ hθ
    rw [HkIntegrand_zero α F z θ, Work.FTS.EllipticEst.AngSecond.sq_mul_W F hθ]
    field_simp
  exact MeasureTheory.IntegrableOn.congr_fun
    ((hF.1 z (le_of_lt hz)).const_mul ((Work.FTS.EllipticEst.AngSecond.w2 z)⁻¹))
    hEq measurableSet_Icc

end Work.FTS.PhiStar.Honesty
end
-- ===== merged: Submission.Work.FTS.PhiStar.LopIterRecursion =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The recursion of the iterated angular operator `Lop`

`Work.Spaces.Lop u θ = sin(2θ) · u'(θ)` is the action of `D_θ = sin(2θ) ∂_θ` on functions of
`θ` alone, and it is a derivation for the pointwise product.  If `f`, `A`, `g` solve the
inhomogeneous linear equation `Lop f = A·f - g` on `Ioo 0 (π/2)`, then the iterates of `Lop`
satisfy the binomial (Leibniz) expansion

`Lop^[i+1] f = ∑_{j ≤ i} C(i,j) · (Lop^[i-j] A) · (Lop^[j] f) - Lop^[i] g`.

The proof combines the pointwise Leibniz rule `LopLeibnizPoint` (finite-order smoothness at a
point) with the pointwise calculus of `Lop`-iterates (`Lop_iter_congr_at`, `Lop_iter_sub_at`,
in `Work.FTS.EllipticEst.remov.Baux`) and the reflection of the binomial index range
(`sum_range_choose_reflect'` below).
-/

namespace Work.FTS.PhiStar

open scoped Topology
open Filter

/-- Reflection of the binomial convolution sum over `range (k+1)`: the index map `j ↦ k - j`
permutes the range `{0, …, k}` and `k.choose (k-j) = k.choose j`, so summing
`C(k,j) · X j · Y (k-j)` is the same as summing `C(k,j) · X (k-j) · Y j`. -/
theorem sum_range_choose_reflect' (k : ℕ) (X Y : ℕ → ℝ) :
    (∑ a ∈ Finset.range (k + 1), (k.choose a : ℝ) * (X a * Y (k - a)))
      = ∑ j ∈ Finset.range (k + 1), (k.choose j : ℝ) * (X (k - j) * Y j) := by
  rw [← Finset.sum_range_reflect (fun j => (k.choose j : ℝ) * (X (k - j) * Y j)) (k + 1)]
  refine Finset.sum_congr rfl fun a ha => ?_
  have ha' : a ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp ha)
  rw [Nat.add_sub_cancel, Nat.sub_sub_self ha', ← Nat.choose_symm ha']

theorem LopIterRecursion {f A g : ℝ → ℝ}
    (hf : ∀ n : ℕ, ContDiffOn ℝ n f (Set.Ioo 0 (Real.pi / 2)))
    (hA : ∀ n : ℕ, ContDiffOn ℝ n A (Set.Ioo 0 (Real.pi / 2)))
    (hg : ∀ n : ℕ, ContDiffOn ℝ n g (Set.Ioo 0 (Real.pi / 2)))
    (hrec : ∀ θ ∈ Set.Ioo 0 (Real.pi / 2), Work.Spaces.Lop f θ = A θ * f θ - g θ) :
    ∀ i : ℕ, ∀ θ ∈ Set.Ioo 0 (Real.pi / 2),
      (Work.Spaces.Lop^[i + 1]) f θ
        = (∑ j ∈ Finset.range (i + 1),
            (i.choose j : ℝ) * ((Work.Spaces.Lop^[i - j]) A θ * (Work.Spaces.Lop^[j]) f θ))
          - (Work.Spaces.Lop^[i]) g θ := by
  intro i θ hθ
  have hU : IsOpen (Set.Ioo 0 (Real.pi / 2)) := isOpen_Ioo
  have hθU : Set.Ioo 0 (Real.pi / 2) ∈ 𝓝 θ := hU.mem_nhds hθ
  -- smoothness of the data at `θ`, and of the product `A * f`
  have hAf : ContDiffAt ℝ (Work.FTS.EllipticEst.remov.Baux.DmrOrd i) (A * f) θ :=
    ((hA (i + 1)).mul (hf (i + 1))).contDiffAt hθU |>.of_le
      (Work.FTS.EllipticEst.remov.Baux.Dmr.DmrOrd_le (Nat.le_succ i))
  have hg' : ContDiffAt ℝ (Work.FTS.EllipticEst.remov.Baux.DmrOrd i) g θ :=
    (hg (i + 1)).contDiffAt hθU |>.of_le
      (Work.FTS.EllipticEst.remov.Baux.Dmr.DmrOrd_le (Nat.le_succ i))
  have hA' : ContDiffAt ℝ (Work.FTS.EllipticEst.remov.Baux.DmrOrd i) A θ :=
    (hA (i + 1)).contDiffAt hθU |>.of_le
      (Work.FTS.EllipticEst.remov.Baux.Dmr.DmrOrd_le (Nat.le_succ i))
  have hf' : ContDiffAt ℝ (Work.FTS.EllipticEst.remov.Baux.DmrOrd i) f θ :=
    (hf (i + 1)).contDiffAt hθU |>.of_le
      (Work.FTS.EllipticEst.remov.Baux.Dmr.DmrOrd_le (Nat.le_succ i))
  -- the recursion, as an eventual equality at `θ`
  have hev : Work.Spaces.Lop f =ᶠ[𝓝 θ] (A * f - g) := by
    filter_upwards [hθU] with θ' hθ'
    exact hrec θ' hθ'
  -- the three ingredients: congruence, subtractivity, Leibniz
  have hcongr := Work.FTS.EllipticEst.remov.Baux.Dmr.Lop_iter_congr_at hev i
  have hsub := Work.FTS.EllipticEst.remov.Baux.Dmr.Lop_iter_sub_at i hAf hg'
  have hleib := Work.FTS.EllipticEst.RPFresh.DivSinOpen.LopLeibnizPoint i hA' hf'
  rw [show i + 1 = i.succ from rfl, Function.iterate_succ_apply, hcongr, hsub, hleib,
    sum_range_choose_reflect' i (fun a => (Work.Spaces.Lop^[a]) A θ)
      (fun a => (Work.Spaces.Lop^[a]) f θ)]

end Work.FTS.PhiStar
end
-- ===== merged: Submission.Work.FTS.StrongEps.E5Aux.slotIdents.pz_pz_eq =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.E5Aux.slotIdents


end Work.FTS.StrongEps.E5Aux.slotIdents
end
-- ===== merged: Submission.Work.FTS.StrongEps.E5Aux2.Helpers =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.E5Aux2

set_option autoImplicit false

/-! ## Splitting `|·|` of a product -/

/-- `|a * b * c * d| ≤ |a| * |b| * |c| * |d|`. -/
lemma abs_mul4_le (a b c d : ℝ) : |a * b * c * d| ≤ |a| * |b| * |c| * |d| :=
  le_of_eq (by rw [abs_mul, abs_mul, abs_mul])

/-- `|a * b * c| ≤ |a| * |b| * |c|`. -/
lemma abs_mul3_le (a b c : ℝ) : |a * b * c| ≤ |a| * |b| * |c| :=
  le_of_eq (by rw [abs_mul, abs_mul])

/-- `|a + b + c + d + e + f| ≤ |a| + |b| + |c| + |d| + |e| + |f|`. -/
lemma abs_six_le (a b c d e f : ℝ) :
    |a + b + c + d + e + f| ≤ |a| + |b| + |c| + |d| + |e| + |f| := by
  have h1 : |a + b + c + d + e + f| ≤ |a + b + c + d + e| + |f| := abs_add_le _ _
  have h2 : |a + b + c + d + e| ≤ |a + b + c + d| + |e| := abs_add_le _ _
  have h3 : |a + b + c + d| ≤ |a + b + c| + |d| := abs_add_le _ _
  have h4 : |a + b + c| ≤ |a + b| + |c| := abs_add_le _ _
  have h5 : |a + b| ≤ |a| + |b| := abs_add_le _ _
  linarith

/-- `|a + b + c + d + e| ≤ |a| + |b| + |c| + |d| + |e|`. -/
lemma abs_five_le (a b c d e : ℝ) :
    |a + b + c + d + e| ≤ |a| + |b| + |c| + |d| + |e| := by
  have h1 : |a + b + c + d + e| ≤ |a + b + c + d| + |e| := abs_add_le _ _
  have h2 : |a + b + c + d| ≤ |a + b + c| + |d| := abs_add_le _ _
  have h3 : |a + b + c| ≤ |a + b| + |c| := abs_add_le _ _
  have h4 : |a + b| ≤ |a| + |b| := abs_add_le _ _
  linarith

/-! ## The additivity defect of `deriv` -/

/-- **The additivity defect of `deriv` is bounded by `|deriv v|`.**  For functions
`u v : ℝ → ℝ` with `v` differentiable at `x`,
`|deriv (u+v) x - deriv u x| ≤ |deriv v x|`.

Both cases are uniform: if `u` is differentiable at `x` this is `deriv_add` (and the left side
is `deriv v x`); if not, neither `u` nor `u + v` is differentiable at `x` (`v` is), so both
`deriv`s are `0` and the left side vanishes. -/
lemma abs_deriv_add_sub_le (u v : ℝ → ℝ) {x : ℝ} (hv : DifferentiableAt ℝ v x) :
    |deriv (fun t => u t + v t) x - deriv u x| ≤ |deriv v x| := by
  by_cases hu : DifferentiableAt ℝ u x
  · have hfun : (fun t => u t + v t) = u + v := rfl
    rw [hfun, deriv_add hu hv, add_sub_cancel_left]
  · have hsum : ¬ DifferentiableAt ℝ (fun t => u t + v t) x := by
      intro h
      apply hu
      have h2 : DifferentiableAt ℝ (fun t => (u t + v t) + (-v t)) x := h.add hv.neg
      refine h2.congr_of_eventuallyEq ?_
      filter_upwards with t
      ring
    rw [deriv_zero_of_not_differentiableAt hsum, deriv_zero_of_not_differentiableAt hu,
      sub_zero, abs_zero]
    exact abs_nonneg _

/-! ## The difference profile `-sin(2θ)/(2(1+z))` -/

/-- The difference of the `Theta`-parts of `f` and `F_* + f`,
`dProf z θ = -sin(2θ)/(2(1+z))` (`Work.FTS.StrongEps.E5Aux2.ThetaDiff`). -/
def dProf (z θ : ℝ) : ℝ := -Real.sin (2 * θ) / (2 * (1 + z))

@[simp] lemma dProf_apply (z θ : ℝ) : dProf z θ = -Real.sin (2 * θ) / (2 * (1 + z)) := rfl





/-! ## Two elementary two-factor bounds -/



end Work.FTS.StrongEps.E5Aux2
end
end
-- ===== merged: Submission.Work.FTS.StrongEps.EpsE4Thr.BarrierIco =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.EpsE4Thr

set_option autoImplicit false
set_option linter.unusedVariables false





end Work.FTS.StrongEps.EpsE4Thr
end
end
-- ===== merged: Submission.Work.FTS.StrongEps.EpsE4Thr.BarrierLevel =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.EpsE4Thr

set_option autoImplicit false
set_option linter.unusedVariables false




/-! ## The trap with **left** derivatives

The producer of the energy identity at the *right endpoint* `τ` of a horizon (module
`EnergyDerivLeft.lean`, delegated) delivers a left (within-`Icc 0 τ`) derivative: at the *first*
time at which the energy exceeds the level, the small ball is available on `[0,τ]` and only there.
The trap below uses exactly that one-sided information, and it consumes the level-point data in the
form "given the level at `τ` and the level bound on `[0,τ)`, the left derivative at `τ` exists and
is negative" — which is what the endpoint energy identity plus the `hneg` split provide. -/

/-- **One-sided descent to the left.**

If `f` has within-`[0,p]`-derivative `f' < 0` at `p`, then `f` is strictly above `f p` just to the
left of `p`.  This is the mirror image of
`Work.Construction.barrier_exists_right_lt_of_hasDerivAt_neg`; it is proved from
`HasDerivWithinAt.limsup_slope_le` and the basis `nhdsLT_basis p` of `𝓝[<] p`. -/
theorem exists_gt_of_hasDerivWithinAt_Icc_left {f : ℝ → ℝ} {f' p : ℝ} (hp : 0 ≤ p)
    (h : HasDerivWithinAt f f' (Set.Icc 0 p) p) (hf' : f' < 0) :
    ∃ δ > 0, ∀ t ∈ Set.Icc 0 p, p - δ < t → t < p → f p < f t := by
  rcases eq_or_lt_of_le hp with rfl | hp0
  · exact ⟨1, one_pos, fun t ht _ h2 => absurd h2 (not_lt.mpr ht.1)⟩
  · set r : ℝ := f' / 2 with hr
    have hrlt : f' < r := by rw [hr]; linarith
    have hev : ∀ᶠ z in 𝓝[Set.Ico 0 p] p, slope f p z < r := by
      have h1 : ∀ᶠ z in 𝓝[(Set.Icc 0 p) \ {p}] p, slope f p z < r := h.limsup_slope_le hrlt
      have hset : (Set.Icc 0 p) \ {p} = Set.Ico 0 p := by
        ext z
        simp only [Set.mem_diff, Set.mem_Icc, Set.mem_singleton_iff, Set.mem_Ico]
        constructor
        · rintro ⟨⟨h1, h2⟩, h3⟩; exact ⟨h1, lt_of_le_of_ne h2 h3⟩
        · rintro ⟨h1, h2⟩; exact ⟨⟨h1, h2.le⟩, ne_of_lt h2⟩
      rwa [hset] at h1
    have heq : 𝓝[Set.Ico 0 p] p = 𝓝[<] p := by
      refine le_antisymm (inf_le_inf_left _ (principal_mono.mpr fun z hz => hz.2)) ?_
      refine le_inf inf_le_left ?_
      rw [le_principal_iff]
      exact mem_of_superset (Ioo_mem_nhdsLT (by linarith : p / 2 < p))
        (fun z hz => ⟨by linarith [hz.1], hz.2⟩)
    rw [heq] at hev
    rw [(nhdsLT_basis p).eventually_iff] at hev
    obtain ⟨ε, hε, hε'⟩ := hev
    refine ⟨p - ε, sub_pos.mpr hε, fun t _ h1 h2 => ?_⟩
    have htε : t ∈ Set.Ioo ε p := ⟨by linarith, h2⟩
    have hd := hε' htε
    have hsl : slope f p t < 0 := lt_trans hd (show r < 0 by rw [hr]; linarith)
    rw [slope_def_field] at hsl
    have htp : t - p < 0 := by linarith
    have hpos : 0 < (f t - f p) / (t - p) * (t - p) := mul_pos_of_neg_of_neg hsl htp
    rw [div_mul_cancel₀ _ (ne_of_lt htp)] at hpos
    linarith

/-- **The trap barrier with left derivatives.**

Let `E` be continuous on `Ico 0 T` with `E 0 < Y`, and suppose that at every **interior**
`τ ∈ Ioo 0 T` at which the level is met (`E τ = Y`) *and* the level bound holds on `[0,τ)`, the
function `E` has a strictly negative within-`Icc 0 τ`-derivative at `τ` (the hypothesis is
restricted to interior `τ` because the crossing point of the proof is interior, and because at
`τ = 0` a within-`Icc 0 0`-derivative forces `E' 0 = 0`).  Then `E τ ≤ Y` on `Ico 0 T`.

Proof: let `A := {t ∈ Icc 0 τ₁ : E t > Y}` be nonempty and `t₀ := sInf A`.  Then `t₀ ∈ Ico 0 T`,
`E ≤ Y` on `[0,t₀)` (minimality of `t₀`), `t₀ > 0` (continuity at `0`), `E t₀ = Y` (two continuity
arguments), so the level-point hypothesis applies at `t₀` and the left descent of
`exists_gt_of_hasDerivWithinAt_Icc_left` contradicts `E ≤ Y` on `[0,t₀)`. -/
theorem barrier_within_level_left {E E' : ℝ → ℝ} {Y T : ℝ} (hT : 0 < T)
    (hcont : ContinuousOn E (Set.Ico 0 T))
    (h0 : E 0 < Y)
    (hlev : ∀ τ ∈ Set.Ioo 0 T, (∀ t ∈ Set.Ico 0 τ, E t ≤ Y) → E τ = Y →
      HasDerivWithinAt E (E' τ) (Set.Icc 0 τ) τ ∧ E' τ < 0) :
    ∀ τ ∈ Set.Ico 0 T, E τ ≤ Y := by
  by_contra hcon
  push_neg at hcon
  obtain ⟨τ₁, hτ₁, hgt⟩ := hcon
  have hcontIcc : ContinuousOn E (Set.Icc 0 τ₁) :=
    hcont.mono fun x hx => ⟨hx.1, lt_of_le_of_lt hx.2 hτ₁.2⟩
  set A : Set ℝ := {t : ℝ | t ∈ Set.Icc 0 τ₁ ∧ Y < E t} with hA
  have hAne : A.Nonempty := ⟨τ₁, ⟨⟨hτ₁.1, le_rfl⟩, hgt⟩⟩
  have hAbdd : BddBelow A := ⟨0, fun x hx => hx.1.1⟩
  set t₀ : ℝ := sInf A with ht₀
  have ht₀le : t₀ ≤ τ₁ := csInf_le hAbdd ⟨⟨hτ₁.1, le_rfl⟩, hgt⟩
  have ht₀ge : 0 ≤ t₀ := le_csInf hAne fun y hy => hy.1.1
  have ht₀lt : t₀ < T := lt_of_le_of_lt ht₀le hτ₁.2
  have ht₀mem : t₀ ∈ Set.Ico 0 T := ⟨ht₀ge, ht₀lt⟩
  -- the level bound on `[0,t₀)` from the minimality of `t₀`
  have hbelow : ∀ t ∈ Set.Ico 0 t₀, E t ≤ Y := by
    intro t ht
    by_contra hty
    have hty' : Y < E t := not_le.mp hty
    have htmem : t ∈ A := ⟨⟨ht.1, le_trans ht.2.le ht₀le⟩, hty'⟩
    have h2 : t₀ ≤ t := csInf_le hAbdd htmem
    linarith [ht.2]
  -- `t₀ > 0`: `E < Y` on a right neighbourhood of `0`
  have ht₀pos : 0 < t₀ := by
    have hEv : {t : ℝ | E t < Y} ∈ 𝓝[Set.Icc 0 τ₁] 0 :=
      (hcontIcc.continuousWithinAt ⟨le_rfl, hτ₁.1⟩).preimage_mem_nhdsWithin
        (isOpen_Iio.mem_nhds h0)
    have hEv' : {x : ℝ | x ∈ Set.Icc 0 τ₁ → E x < Y} ∈ 𝓝 (0 : ℝ) :=
      Filter.mem_inf_principal.mp hEv
    obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp hEv'
    have hle : ε ≤ t₀ := by
      refine le_csInf hAne fun y hy => ?_
      by_contra hyy
      have hdist : dist y 0 < ε := by
        rw [Real.dist_eq, sub_zero, abs_of_nonneg hy.1.1]
        exact not_le.mp hyy
      exact absurd (hball hdist hy.1) (not_lt.mpr hy.2.le)
    linarith
  -- `E t₀ ≤ Y`, by continuity from the left
  have ht₀leY : E t₀ ≤ Y := by
    have hclosed : IsClosed (Set.Icc 0 τ₁ ∩ E ⁻¹' Set.Iic Y) :=
      hcontIcc.preimage_isClosed_of_isClosed isClosed_Icc isClosed_Iic
    have hsub : Set.Ioo 0 t₀ ⊆ Set.Icc 0 τ₁ ∩ E ⁻¹' Set.Iic Y := fun x hx =>
      ⟨⟨hx.1.le, le_trans hx.2.le ht₀le⟩, hbelow x ⟨hx.1.le, hx.2⟩⟩
    have hcl : Set.Icc 0 t₀ ⊆ Set.Icc 0 τ₁ ∩ E ⁻¹' Set.Iic Y := by
      rw [← closure_Ioo (ne_of_lt ht₀pos)]
      exact closure_minimal hsub hclosed
    exact (hcl ⟨ht₀ge, le_rfl⟩).2
  -- `Y ≤ E t₀`, else a right neighbourhood of `t₀` misses `A`
  have ht₀geY : Y ≤ E t₀ := by
    by_contra hlt
    have hlt' : E t₀ < Y := not_le.mp hlt
    have hEv : {t : ℝ | E t < Y} ∈ 𝓝[Set.Icc 0 τ₁] t₀ :=
      (hcontIcc.continuousWithinAt ⟨ht₀ge, ht₀le⟩).preimage_mem_nhdsWithin
        (isOpen_Iio.mem_nhds hlt')
    have hEv' : {x : ℝ | x ∈ Set.Icc 0 τ₁ → E x < Y} ∈ 𝓝 t₀ :=
      Filter.mem_inf_principal.mp hEv
    obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp hEv'
    have hbound : ∀ y ∈ A, t₀ + min ε 1 ≤ y := by
      intro y hy
      by_contra hyy
      have hyge : t₀ ≤ y := csInf_le hAbdd hy
      have hdist : dist y t₀ < ε := by
        rw [Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr hyge)]
        linarith [min_le_left ε 1]
      exact absurd (hball hdist hy.1) (not_lt.mpr hy.2.le)
    have hle : t₀ + min ε 1 ≤ t₀ := by
      have h1 : t₀ + min ε 1 ≤ sInf A := le_csInf hAne hbound
      simpa only [ht₀] using h1
    have h2 : 0 < min ε 1 := lt_min hε zero_lt_one
    linarith
  have ht₀Y : E t₀ = Y := le_antisymm ht₀leY ht₀geY
  obtain ⟨hderiv, hneg⟩ := hlev t₀ ⟨ht₀pos, ht₀lt⟩ hbelow ht₀Y
  obtain ⟨δ, hδpos, hδ⟩ := exists_gt_of_hasDerivWithinAt_Icc_left ht₀ge hderiv hneg
  set z : ℝ := t₀ - min δ t₀ / 2 with hzdef
  have hzlt : z < t₀ := by
    rw [hzdef]; have := lt_min hδpos ht₀pos; linarith
  have hzge : 0 ≤ z := by
    rw [hzdef]; have := min_le_right δ t₀; linarith
  have hzδ : t₀ - δ < z := by
    rw [hzdef]; have := min_le_left δ t₀; linarith
  have hgt' : E t₀ < E z := hδ z ⟨hzge, hzlt.le⟩ hzδ hzlt
  have hb := hbelow z ⟨hzge, hzlt⟩
  rw [ht₀Y] at hgt'
  linarith

end Work.FTS.StrongEps.EpsE4Thr
end
end
-- ===== merged: Submission.Work.FTS.StrongEps.ScalarBounds =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps

set_option autoImplicit false

/-- **`L₁₂(F_*)` is bounded by `2` on `[0,∞)`**: the identity `L₁₂(F_*)(z) = 2α/(1+z)`. -/
theorem L12_Fstar_abs_le :
    ∃ B : ℝ, 0 < B ∧ ∀ α ∈ Set.Ioc 0 1, ∀ z ∈ Work.Spaces.Iz,
      |Work.Construction.L12 (Work.Construction.Fstar α) z| ≤ B := by
  refine ⟨2, by norm_num, ?_⟩
  intro α hα z hz
  have hz0 : 0 ≤ z := hz
  rw [Work.Construction.L12_Fstar_eq hα.1 hα.2 hz0]
  have h1 : (0 : ℝ) < 1 + z := by linarith
  rw [abs_div, abs_of_pos h1, abs_of_pos (by linarith [hα.1] : (0 : ℝ) < 2 * α)]
  rw [div_le_iff₀ h1]
  nlinarith [hα.1, hα.2, hz0]


/-- **The two coefficients of `𝓛_Γ^T` are bounded by `10`** (the `hcoef`/`hcoef2` hypotheses of
the `G7` chain), for `α ∈ (0,1]` and `1/10 ≤ c α`. -/
theorem coef_abs_le {α : ℝ} (hα : α ∈ Set.Ioc 0 1) (hc : 1 / 10 ≤ Work.Spaces.c α) :
    ∀ z θ : ℝ, 0 ≤ z → θ ∈ Work.Spaces.Iθ →
      |2 * z * Work.Spaces.Gam α θ / (Work.Spaces.c α * (1 + z) ^ 2)| ≤ 10 ∧
      |Work.Spaces.Gam α θ / Work.Spaces.c α * (2 * z ^ 2 / (1 + z) ^ 3)| ≤ 10 := by
  intro z θ hz hθ
  have hc0 : (0 : ℝ) < Work.Spaces.c α := lt_of_lt_of_le (by norm_num) hc
  obtain ⟨hGam0, hGam1⟩ := Work.Spaces.Gam_bounds α θ hα.1 hθ
  have h1 : (0 : ℝ) < 1 + z := by linarith
  have hquot : Work.Spaces.Gam α θ / Work.Spaces.c α ≤ 10 := by
    rw [div_le_iff₀ hc0]
    nlinarith [hGam1, hc]
  have hquot0 : 0 ≤ Work.Spaces.Gam α θ / Work.Spaces.c α := div_nonneg hGam0 hc0.le
  constructor
  · -- first coefficient: `2z/(1+z)² · (Γ/c)`
    have hfac : 2 * z / (1 + z) ^ 2 ≤ 1 := by
      rw [div_le_iff₀ (by positivity : (0 : ℝ) < (1 + z) ^ 2)]
      nlinarith [sq_nonneg (z - 1), hz]
    have hrw : 2 * z * Work.Spaces.Gam α θ / (Work.Spaces.c α * (1 + z) ^ 2)
        = (Work.Spaces.Gam α θ / Work.Spaces.c α) * (2 * z / (1 + z) ^ 2) := by
      field_simp
    rw [hrw, abs_mul, abs_of_nonneg hquot0, abs_of_nonneg (by positivity : 0 ≤ 2 * z / (1 + z) ^ 2)]
    nlinarith [hquot, hfac]
  · rw [abs_mul, abs_of_nonneg hquot0,
      abs_of_nonneg (by positivity : 0 ≤ 2 * z ^ 2 / (1 + z) ^ 3)]
    have hfrac : 2 * z ^ 2 / (1 + z) ^ 3 ≤ 1 := by
      rw [div_le_iff₀ (by positivity : (0 : ℝ) < (1 + z) ^ 3)]
      nlinarith [show (0 : ℝ) ≤ z ^ 2 * (1 + z) by positivity, hz]
    nlinarith [hquot, hfrac]

end Work.FTS.StrongEps
end
end
-- ===== merged: Submission.Work.FTS.StrongEps.blocks.Fstar_AK_bnd =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.blocks

theorem Fstar_AK_bnd {α c d : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) (hc : 0 < c) (hcd : c ≤ d)
    (hd : d < Real.pi / 2) :
    ∃ C : ℝ, 0 < C ∧ ∀ z θ : ℝ, 0 < z → c ≤ θ → θ ≤ d →
      |Work.Construction.Fstar α z θ| + |Work.Spaces.pth (Work.Construction.Fstar α) z θ|
        + |Work.Spaces.Dz (Work.Construction.Fstar α) z θ| + |Work.Construction.AK α z θ| ≤ C := by
  -- `m = 2 sin c cos d` is the uniform lower bound for `sin(2θ)` on the angular box.
  set m : ℝ := 2 * Real.sin c * Real.cos d with hm
  have hsin_c : 0 < Real.sin c :=
    Real.sin_pos_of_pos_of_lt_pi hc (by linarith [hcd, hd, Real.pi_pos])
  have hcos_d : 0 < Real.cos d := Real.cos_pos_of_mem_Ioo ⟨by linarith [hc, hcd], hd⟩
  have hm_pos : 0 < m := by rw [hm]; positivity
  have hα2 : α ^ 2 ≤ 1 := by nlinarith [hα.le, hα1]
  have hsin2 : ∀ θ : ℝ, c ≤ θ → θ ≤ d → m ≤ Real.sin (2 * θ) := by
    intro θ hθc hθd
    rw [hm]
    have h1 : Real.sin c ≤ Real.sin θ :=
      Real.sin_le_sin_of_le_of_le_pi_div_two (by linarith [Real.pi_pos])
        (by linarith [hθd, hd]) hθc
    have h2 : Real.cos d ≤ Real.cos θ :=
      Real.cos_le_cos_of_nonneg_of_le_pi (by linarith) (by linarith [hd, Real.pi_pos]) hθd
    have hsθ : 0 ≤ Real.sin θ := le_trans hsin_c.le h1
    have hmul : Real.sin c * Real.cos d ≤ Real.sin θ * Real.cos θ :=
      mul_le_mul h1 h2 hcos_d.le hsθ
    rw [Real.sin_two_mul]
    linarith
  have hc10 : (1 : ℝ) / 10 ≤ Work.Spaces.c α := (Work.Spaces.c_bounds α hα hα1).1
  have hc0 : 0 < Work.Spaces.c α := by linarith
  -- The three explicit rational factors in `z` are bounded by `2` on `z ≥ 0`.
  have hFz : ∀ z : ℝ, 0 ≤ z → |Work.FM.Fstar z| ≤ 2 := by
    intro z hz
    have hnn : 0 ≤ 2 * z / (1 + z) ^ 2 := by positivity
    have hle : 2 * z / (1 + z) ^ 2 ≤ 2 := by
      rw [div_le_iff₀ (by positivity : (0 : ℝ) < (1 + z) ^ 2)]
      nlinarith [sq_nonneg z]
    rw [show Work.FM.Fstar z = 2 * z / (1 + z) ^ 2 from rfl, abs_of_nonneg hnn]
    exact hle
  have hDzfrac : ∀ z : ℝ, 0 ≤ z → |2 * z * (1 - z) / (1 + z) ^ 3| ≤ 2 := by
    intro z hz
    have h1z : (0 : ℝ) < 1 + z := by linarith
    have hden : (0 : ℝ) < (1 + z) ^ 3 := by positivity
    have h1 : |1 - z| ≤ 1 + z := abs_le.mpr ⟨by linarith, by linarith⟩
    rw [abs_div, abs_mul, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2), abs_of_nonneg hz,
      abs_of_pos hden]
    have h2 : 2 * z * |1 - z| / (1 + z) ^ 3 ≤ 2 * z * (1 + z) / (1 + z) ^ 3 := by
      apply div_le_div_of_nonneg_right _ hden.le
      exact mul_le_mul_of_nonneg_left h1 (by positivity)
    have h3 : 2 * z * (1 + z) / (1 + z) ^ 3 ≤ 2 := by
      rw [div_le_iff₀ hden]
      nlinarith [sq_nonneg z, hz, sq_nonneg (1 + z)]
    linarith
  have hAKfrac : ∀ z : ℝ, 0 ≤ z → |2 * z ^ 2 / (1 + z) ^ 3| ≤ 2 := by
    intro z hz
    have hnn : 0 ≤ 2 * z ^ 2 / (1 + z) ^ 3 := by positivity
    rw [abs_of_nonneg hnn]
    rw [div_le_iff₀ (by positivity : (0 : ℝ) < (1 + z) ^ 3)]
    nlinarith [sq_nonneg z, hz, sq_nonneg (1 + z)]
  refine ⟨61 + 40 / m, ?_, ?_⟩
  · have : 0 < 40 / m := div_pos (by norm_num) hm_pos
    linarith
  · intro z θ hz hθc hθd
    have hθI : θ ∈ Work.Spaces.Iθ :=
      ⟨le_trans hc.le hθc, le_of_lt (lt_of_le_of_lt hθd hd)⟩
    have hθIoo : θ ∈ Set.Ioo 0 (Real.pi / 2) := ⟨by linarith, by linarith⟩
    obtain ⟨hGam0, hGam1⟩ := Work.Spaces.Gam_bounds α θ hα hθI
    have hq0 : 0 ≤ Work.Spaces.Gam α θ / Work.Spaces.c α := div_nonneg hGam0 hc0.le
    have hq10 : Work.Spaces.Gam α θ / Work.Spaces.c α ≤ 10 := by
      rw [div_le_iff₀ hc0]; nlinarith [hGam1, hc10]
    have hm_le : m ≤ Real.sin (2 * θ) := hsin2 θ hθc hθd
    have hsinpos : 0 < Real.sin (2 * θ) := lt_of_lt_of_le hm_pos hm_le
    -- The angular derivative of `Γ`, through `D_θΓ = α q Γ` and `D_θ = sin(2θ)∂_θ`.
    have hderiv : |deriv (fun t => Work.Spaces.Gam α t) θ| ≤ 2 * α / m := by
      have hdth := Work.Spaces.dthU_Gam α θ hα hθIoo
      rw [Work.Spaces.dthU_apply] at hdth
      have hdeq : deriv (fun t => Work.Spaces.Gam α t) θ
          = α * Work.Spaces.qfun θ * Work.Spaces.Gam α θ / Real.sin (2 * θ) := by
        rw [eq_div_iff (ne_of_gt hsinpos), mul_comm]
        exact hdth
      rw [hdeq, abs_div, abs_mul, abs_mul, abs_of_pos hα, abs_of_pos hsinpos,
        abs_of_nonneg hGam0]
      have hq : |Work.Spaces.qfun θ| ≤ 4 / 3 := by
        rw [Work.Spaces.qfun_apply, abs_le]
        constructor <;> nlinarith [Real.neg_one_le_cos (2 * θ), Real.cos_le_one (2 * θ)]
      have hnum : α * |Work.Spaces.qfun θ| * Work.Spaces.Gam α θ ≤ 4 * α / 3 := by
        have h1 : α * |Work.Spaces.qfun θ| ≤ α * (4 / 3) :=
          mul_le_mul_of_nonneg_left hq hα.le
        have h2 := mul_le_mul h1 hGam1 hGam0 (by positivity : (0 : ℝ) ≤ α * (4 / 3))
        linarith
      rw [div_le_div_iff₀ hsinpos hm_pos]
      have hs1 : α * |Work.Spaces.qfun θ| * Work.Spaces.Gam α θ * m ≤ (4 * α / 3) * m :=
        mul_le_mul_of_nonneg_right hnum hm_pos.le
      have hs2 : (4 * α / 3) * m ≤ (4 * α / 3) * Real.sin (2 * θ) :=
        mul_le_mul_of_nonneg_left hm_le (by positivity)
      have hs3 : (4 * α / 3) * Real.sin (2 * θ) ≤ 2 * α * Real.sin (2 * θ) := by
        have : (4 : ℝ) * α / 3 ≤ 2 * α := by linarith
        exact mul_le_mul_of_nonneg_right this hsinpos.le
      linarith
    have hpth : |Work.Spaces.pth (Work.Construction.Fstar α) z θ| ≤ 40 / m := by
      rw [Work.Construction.pth_Fstar_eq hα]
      rw [abs_mul, abs_mul, abs_of_pos hα, abs_div, abs_of_pos hc0]
      have hcv : |deriv (fun t => Work.Spaces.Gam α t) θ| / Work.Spaces.c α
          ≤ 10 * |deriv (fun t => Work.Spaces.Gam α t) θ| := by
        rw [div_le_iff₀ hc0]
        nlinarith [abs_nonneg (deriv (fun t => Work.Spaces.Gam α t) θ), hc10]
      have hstep : α * (|deriv (fun t => Work.Spaces.Gam α t) θ| / Work.Spaces.c α)
            * |Work.FM.Fstar z| ≤ α * (10 * |deriv (fun t => Work.Spaces.Gam α t) θ|) * 2 :=
        mul_le_mul (mul_le_mul_of_nonneg_left hcv hα.le) (hFz z (le_of_lt hz))
          (abs_nonneg _) (by positivity)
      have hb : α * (10 * |deriv (fun t => Work.Spaces.Gam α t) θ|) * 2 ≤ 40 / m := by
        have h2 : α * (10 * |deriv (fun t => Work.Spaces.Gam α t) θ|) * 2
            = 20 * (α * |deriv (fun t => Work.Spaces.Gam α t) θ|) := by ring
        rw [h2]
        have h3 : α * |deriv (fun t => Work.Spaces.Gam α t) θ| ≤ 2 * α ^ 2 / m := by
          calc α * |deriv (fun t => Work.Spaces.Gam α t) θ| ≤ α * (2 * α / m) :=
                mul_le_mul_of_nonneg_left hderiv hα.le
            _ = 2 * α ^ 2 / m := by ring
        have h4 : 2 * α ^ 2 / m ≤ 2 / m := by
          rw [div_le_div_iff₀ hm_pos hm_pos]
          nlinarith [hα2, hm_pos]
        calc 20 * (α * |deriv (fun t => Work.Spaces.Gam α t) θ|)
            ≤ 20 * (2 * α ^ 2 / m) := mul_le_mul_of_nonneg_left h3 (by norm_num)
          _ ≤ 20 * (2 / m) := mul_le_mul_of_nonneg_left h4 (by norm_num)
          _ = 40 / m := by ring
      linarith
    have hF : |Work.Construction.Fstar α z θ| ≤ 20 := by
      rw [Work.Construction.Fstar, abs_mul, abs_mul, abs_of_pos hα, abs_of_nonneg hq0]
      calc α * (Work.Spaces.Gam α θ / Work.Spaces.c α) * |Work.FM.Fstar z|
          ≤ 1 * 10 * 2 :=
            mul_le_mul (mul_le_mul hα1 hq10 hq0 (by norm_num)) (hFz z (le_of_lt hz))
              (abs_nonneg _) (by norm_num)
        _ = 20 := by norm_num
    have hDz : |Work.Spaces.Dz (Work.Construction.Fstar α) z θ| ≤ 20 := by
      rw [Work.Construction.Dz_Fstar_eq hα (by linarith : (-1 : ℝ) < z)]
      rw [abs_mul, abs_mul, abs_of_pos hα, abs_of_nonneg hq0]
      calc α * (Work.Spaces.Gam α θ / Work.Spaces.c α) * |2 * z * (1 - z) / (1 + z) ^ 3|
          ≤ 1 * 10 * 2 :=
            mul_le_mul (mul_le_mul hα1 hq10 hq0 (by norm_num)) (hDzfrac z (le_of_lt hz))
              (abs_nonneg _) (by norm_num)
        _ = 20 := by norm_num
    have hAK : |Work.Construction.AK α z θ| ≤ 20 := by
      rw [Work.Construction.AK, abs_mul, abs_of_nonneg hq0]
      calc Work.Spaces.Gam α θ / Work.Spaces.c α * |2 * z ^ 2 / (1 + z) ^ 3|
          ≤ 10 * 2 := mul_le_mul hq10 (hAKfrac z (le_of_lt hz)) (abs_nonneg _) (by norm_num)
        _ = 20 := by norm_num
    linarith [hF, hpth, hDz, hAK]

end Work.FTS.StrongEps.blocks
end
-- ===== merged: Submission.Work.FTS.StrongLWP.Sobolev.EqcBasic =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongLWP.Sobolev

set_option autoImplicit false

/-- The operator norm of a continuous linear map on `ℝ × ℝ` is bounded by the sum of the norms
of its values on the standard basis. -/
lemma eqc_opNorm_le_basis_sum {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (L : (ℝ × ℝ) →L[ℝ] F) : ‖L‖ ≤ ‖L (1, 0)‖ + ‖L (0, 1)‖ := by
  rw [ContinuousLinearMap.opNorm_le_iff (by positivity)]
  intro h
  have hL : L h = h.1 • L ((1 : ℝ), (0 : ℝ)) + h.2 • L ((0 : ℝ), (1 : ℝ)) := by
    conv_lhs => rw [show h = h.1 • ((1 : ℝ), (0 : ℝ)) + h.2 • ((0 : ℝ), (1 : ℝ)) by
      ext <;> simp]
    rw [map_add, map_smul, map_smul]
  rw [hL]
  calc ‖h.1 • L (1, 0) + h.2 • L (0, 1)‖
      ≤ ‖h.1 • L (1, 0)‖ + ‖h.2 • L (0, 1)‖ := norm_add_le _ _
    _ = ‖h.1‖ * ‖L (1, 0)‖ + ‖h.2‖ * ‖L (0, 1)‖ := by rw [norm_smul, norm_smul]
    _ ≤ ‖h‖ * ‖L (1, 0)‖ + ‖h‖ * ‖L (0, 1)‖ :=
        add_le_add (mul_le_mul_of_nonneg_right (by simpa using norm_fst_le h) (norm_nonneg _))
          (mul_le_mul_of_nonneg_right (by simpa using norm_snd_le h) (norm_nonneg _))
    _ = (‖L (1, 0)‖ + ‖L (0, 1)‖) * ‖h‖ := by ring

/-- The same for the second derivative: a continuous linear map into `(ℝ × ℝ) →L[ℝ] ℝ` is
bounded by the sum of the absolute values of its four matrix entries. -/
lemma eqc_opNorm_le_basis_sum₂ (L : (ℝ × ℝ) →L[ℝ] ((ℝ × ℝ) →L[ℝ] ℝ)) :
    ‖L‖ ≤ |L (1, 0) (1, 0)| + |L (1, 0) (0, 1)| + |L (0, 1) (1, 0)| + |L (0, 1) (0, 1)| := by
  have h1 := eqc_opNorm_le_basis_sum L
  have h2 : ‖L (1, 0)‖ ≤ |L (1, 0) (1, 0)| + |L (1, 0) (0, 1)| := by
    simpa only [Real.norm_eq_abs] using eqc_opNorm_le_basis_sum (L (1, 0))
  have h3 : ‖L (0, 1)‖ ≤ |L (0, 1) (1, 0)| + |L (0, 1) (0, 1)| := by
    simpa only [Real.norm_eq_abs] using eqc_opNorm_le_basis_sum (L (0, 1))
  linarith

/-- `(a+b)² ≤ 2(a²+b²)`. -/
lemma eqc_sq_add2_le (a b : ℝ) : (a + b) ^ 2 ≤ 2 * (a ^ 2 + b ^ 2) := by
  nlinarith [sq_nonneg (a - b)]

/-- `(a+b+c)² ≤ 3(a²+b²+c²)`. -/
lemma eqc_sq_add3_le (a b c : ℝ) : (a + b + c) ^ 2 ≤ 3 * (a ^ 2 + b ^ 2 + c ^ 2) := by
  nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (a - c)]

/-- `(a+b+c+d)² ≤ 4(a²+b²+c²+d²)`. -/
lemma eqc_sq_add4_le (a b c d : ℝ) :
    (a + b + c + d) ^ 2 ≤ 4 * (a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2) := by
  nlinarith [sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (a - d), sq_nonneg (b - c),
    sq_nonneg (b - d), sq_nonneg (c - d)]

/-- If a function vanishes on a neighbourhood of `x`, its derivative vanishes at `x`. -/
lemma eqc_fderiv_eq_zero_of_eqOn_nhds {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] {v : E → F} {s : Set E} {x : E}
    (hs : s ∈ 𝓝 x) (hv : ∀ y ∈ s, v y = 0) : fderiv ℝ v x = 0 := by
  have hev : v =ᶠ[𝓝 x] (fun _ => (0 : F)) := Filter.eventuallyEq_iff_exists_mem.mpr ⟨s, hs, hv⟩
  rw [hev.fderiv_eq]
  simp

/-- If a function vanishes on an *open* set, so do its first and second derivatives. -/
lemma eqc_fderiv_fderiv_eq_zero_of_open {v : ℝ × ℝ → ℝ} {s : Set (ℝ × ℝ)}
    (hs : IsOpen s) (hv : ∀ y ∈ s, v y = 0) {x : ℝ × ℝ} (hx : x ∈ s) :
    fderiv ℝ v x = 0 ∧ fderiv ℝ (fderiv ℝ v) x = 0 := by
  have h1 : ∀ y ∈ s, fderiv ℝ v y = 0 :=
    fun y hy => eqc_fderiv_eq_zero_of_eqOn_nhds (hs.mem_nhds hy) hv
  exact ⟨h1 x hx, eqc_fderiv_eq_zero_of_eqOn_nhds (hs.mem_nhds hx) h1⟩




/-- The `pth`-analogue of `Work.Spaces.pz_congr_of_isOpen`. -/
lemma eqc_pth_congr_of_isOpen {f f' : ℝ → ℝ → ℝ} {V : Set (ℝ × ℝ)} (hV : IsOpen V)
    (h : Set.EqOn (Function.uncurry f) (Function.uncurry f') V) {z θ : ℝ} (hx : (z, θ) ∈ V) :
    Work.Spaces.pth f z θ = Work.Spaces.pth f' z θ := by
  have htend : Tendsto (fun θ' : ℝ => (z, θ')) (𝓝 θ) (𝓝 (z, θ)) :=
    (continuous_const.prodMk continuous_id).continuousAt
  have hev : (fun θ' => f z θ') =ᶠ[𝓝 θ] (fun θ' => f' z θ') := by
    filter_upwards [htend.eventually (hV.mem_nhds hx)] with θ' hθ'
    exact h hθ'
  exact hev.deriv_eq

end Work.FTS.StrongLWP.Sobolev
end
end
-- ===== merged: Submission.Work.FTS.StrongPersist.H6Pair6Aux.WlInfAngRadial =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongPersist.H6Pair6Aux

/-- Elementary product bound used for the mixed angular-radial terms: if `|dA| * ww ≤ Kc`
with `ww ≥ 0`, and `|X| ≤ Bk`, then `|D * (dA * ww) * X| ≤ |D| * (Bk * Kc)`. -/
private lemma abs_four_le {D dA ww X Kc Bk : ℝ} (hw : 0 ≤ ww) (hKc : 0 ≤ Kc)
    (h1 : |dA| * ww ≤ Kc) (h2 : |X| ≤ Bk) :
    |D * (dA * ww) * X| ≤ |D| * (Bk * Kc) := by
  calc |D * (dA * ww) * X| = |D * (dA * ww)| * |X| := abs_mul _ _
    _ = (|D| * |dA * ww|) * |X| := by rw [abs_mul D (dA * ww)]
    _ = (|D| * (|dA| * ww)) * |X| := by rw [abs_mul dA ww, abs_of_nonneg hw]
    _ ≤ (|D| * Kc) * Bk := by
        refine mul_le_mul (mul_le_mul_of_nonneg_left h1 (abs_nonneg D)) h2 (abs_nonneg X) ?_
        exact mul_nonneg (abs_nonneg D) hKc
    _ = |D| * (Bk * Kc) := by ring

theorem WlInfAngRadial {l : ℕ} {A : ℝ → ℝ} {Hc : ℝ → ℝ} {B : ℕ → ℝ} {D α KA Kc : ℝ}
    (hα : 0 < α)
    (hA : ∀ θ ∈ Work.Spaces.Iθ, |A θ| ≤ KA)
    (hK : ∀ j : ℕ, 1 ≤ j → j ≤ l → ∀ θ ∈ Work.Spaces.Iθ,
      |(Work.Spaces.dthU^[j]) A θ|
        * ((Real.sin (2 * θ)) ^ (-(α / 5)) / (α + Real.sin (2 * θ))) ≤ Kc)
    (hB : ∀ k : ℕ, k ≤ l → ∀ z : ℝ, 0 ≤ z → |(z + 1) ^ k * deriv^[k] Hc z| ≤ B k) :
    Work.Spaces.WlInfMem α l (fun z θ => D * (A θ * Hc z)) ∧
      Work.Spaces.WlInf α l (fun z θ => D * (A θ * Hc z)) ≤
        |D| * ((∑ k ∈ Finset.range (l + 1), KA * B k)
          + ∑ j ∈ Finset.range (l + 1), ∑ k ∈ Finset.range (l + 1),
              (if 1 ≤ j ∧ k + j ≤ l then B k * Kc else 0)) := by
  classical
  have hf : (fun z θ => D * (A θ * Hc z)) = fun z θ => (D * A θ) * Hc z := by
    funext z θ; ring
  have hDthF : ∀ j : ℕ, Work.Spaces.DthIter j (fun z θ => (D * A θ) * Hc z)
      = fun z θ => Work.Spaces.dthU^[j] (fun t => D * A t) θ * Hc z := by
    intro j
    funext z θ
    exact Work.Spaces.DthIter_decomp j (fun t => D * A t) Hc z θ
  have hdthD : ∀ j : ℕ, Work.Spaces.dthU^[j] (fun t => D * A t)
      = fun t => D * Work.Spaces.dthU^[j] A t := by
    intro j
    exact Work.Spaces.dthU_iter_const_mul j D A
  have hBnn : ∀ k, k ≤ l → 0 ≤ B k := by
    intro k hk
    exact le_trans (abs_nonneg _) (hB k hk 0 (le_refl 0))
  have hKa : 0 ≤ KA := by
    have h0 : (0 : ℝ) ∈ Work.Spaces.Iθ := by
      refine ⟨le_refl 0, ?_⟩
      linarith [Real.pi_pos]
    exact le_trans (abs_nonneg _) (hA 0 h0)
  -- The two pointwise estimates.
  have hpt1 : ∀ k, k ≤ l → ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ,
      |(z + 1) ^ k * Work.Spaces.pzIter k (fun z θ => (D * A θ) * Hc z) z θ|
        ≤ |D| * (KA * B k) := by
    intro k hk z hz θ hθ
    rw [Work.Spaces.pzIter_decomp k (fun θ => D * A θ) Hc z θ]
    rw [show (z + 1) ^ k * ((D * A θ) * deriv^[k] Hc z)
          = (D * A θ) * ((z + 1) ^ k * deriv^[k] Hc z) by ring]
    have hAB : |D * A θ| ≤ |D| * KA := by
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left (hA θ hθ) (abs_nonneg D)
    have hDz := hB k hk z hz
    calc |(D * A θ) * ((z + 1) ^ k * deriv^[k] Hc z)|
        = |D * A θ| * |(z + 1) ^ k * deriv^[k] Hc z| := abs_mul _ _
      _ ≤ (|D| * KA) * B k :=
          mul_le_mul hAB hDz (abs_nonneg _) (mul_nonneg (abs_nonneg D) hKa)
      _ = |D| * (KA * B k) := by ring
  have hpt2 : ∀ j, 1 ≤ j → ∀ k, k + j ≤ l → ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ,
      |(z + 1) ^ k * Work.Spaces.pzIter k
          (Work.Spaces.DthIter j (fun z θ => (D * A θ) * Hc z)) z θ
        * (Real.sin (2 * θ)) ^ (-(α / 5)) / (α + Real.sin (2 * θ))|
        ≤ |D| * (B k * Kc) := by
    intro j hj1 k hkj z hz θ hθ
    have hkl : k ≤ l := by omega
    have hjl : j ≤ l := by omega
    rw [hDthF j]
    rw [Work.Spaces.pzIter_decomp k
      (fun θ => Work.Spaces.dthU^[j] (fun t => D * A t) θ) Hc]
    rw [hdthD j]
    dsimp only
    rw [mul_div_assoc]
    have hsin : 0 ≤ Real.sin (2 * θ) :=
      Real.sin_nonneg_of_mem_Icc (by
        constructor <;> linarith [hθ.1, hθ.2, Real.pi_pos])
    have hden : 0 < α + Real.sin (2 * θ) := by linarith
    have hw : 0 ≤ (Real.sin (2 * θ)) ^ (-(α / 5)) / (α + Real.sin (2 * θ)) :=
      div_nonneg (Real.rpow_nonneg hsin _) (le_of_lt hden)
    have hKc : 0 ≤ Kc := by
      have h1l : 1 ≤ l := le_trans hj1 hjl
      have h0mem : (0 : ℝ) ∈ Work.Spaces.Iθ := by
        refine ⟨le_refl 0, ?_⟩
        linarith [Real.pi_pos]
      have h := hK 1 le_rfl h1l 0 h0mem
      have hzero : |(Work.Spaces.dthU^[1]) A 0|
          * ((Real.sin (2 * (0 : ℝ))) ^ (-(α / 5))
              / (α + Real.sin (2 * (0 : ℝ)))) = 0 := by
        have hne : -(α / 5) ≠ 0 := by
          intro hc
          have : α = 0 := by linarith
          linarith
        have hs : Real.sin (2 * (0 : ℝ)) = 0 := by simp
        rw [hs, Real.zero_rpow hne, zero_div, mul_zero]
      rw [hzero] at h
      exact h
    have hEq : (z + 1) ^ k * ((D * Work.Spaces.dthU^[j] A θ) * deriv^[k] Hc z)
          * ((Real.sin (2 * θ)) ^ (-(α / 5)) / (α + Real.sin (2 * θ)))
        = D * (Work.Spaces.dthU^[j] A θ
            * ((Real.sin (2 * θ)) ^ (-(α / 5)) / (α + Real.sin (2 * θ))))
          * ((z + 1) ^ k * deriv^[k] Hc z) := by ring
    rw [hEq]
    exact abs_four_le hw hKc (hK j hj1 hjl θ hθ) (hB k hkl z hz)
  constructor
  · rw [Work.Spaces.WlInfMem, hf]
    refine ⟨?_, ?_⟩
    · intro k hk
      exact Work.FTS.Nonlinear.FstarPkg.supFinite_of_pointwise_bound
        (fun z hz θ hθ => hpt1 k hk z hz θ hθ)
    · intro j hj k hk hj1 hjk
      exact Work.FTS.Nonlinear.FstarPkg.supFinite_of_pointwise_bound
        (fun z hz θ hθ => hpt2 j hj1 k hjk z hz θ hθ)
  · rw [Work.Spaces.WlInf, hf]
    have hterm1 : ∀ k ∈ Finset.range (l + 1),
        Work.Spaces.supAbs (fun z θ => (z + 1) ^ k
            * Work.Spaces.pzIter k (fun z θ => (D * A θ) * Hc z) z θ)
          ≤ |D| * (KA * B k) := by
      intro k hk
      exact Work.Spaces.supAbs_le (fun z hz θ hθ =>
        hpt1 k (by simpa using Finset.mem_range.mp hk) z hz θ hθ)
    have hterm2 : ∀ j ∈ Finset.range (l + 1), ∀ k ∈ Finset.range (l + 1),
        (if 1 ≤ j ∧ k + j ≤ l then
          Work.Spaces.supAbs (fun z θ => (z + 1) ^ k
            * Work.Spaces.pzIter k
                (Work.Spaces.DthIter j (fun z θ => (D * A θ) * Hc z)) z θ
            * Real.sin (2 * θ) ^ (-(α / 5)) / (α + Real.sin (2 * θ)))
          else 0)
        ≤ (if 1 ≤ j ∧ k + j ≤ l then |D| * (B k * Kc) else 0) := by
      intro j hj k hk
      split_ifs with hcond
      · exact Work.Spaces.supAbs_le (fun z hz θ hθ =>
          hpt2 j hcond.1 k hcond.2 z hz θ hθ)
      · exact le_refl 0
    have hsum1 : (∑ k ∈ Finset.range (l + 1), Work.Spaces.supAbs (fun z θ => (z + 1) ^ k
            * Work.Spaces.pzIter k (fun z θ => (D * A θ) * Hc z) z θ))
        ≤ ∑ k ∈ Finset.range (l + 1), |D| * (KA * B k) := Finset.sum_le_sum hterm1
    have hsum2 : (∑ j ∈ Finset.range (l + 1), ∑ k ∈ Finset.range (l + 1),
          (if 1 ≤ j ∧ k + j ≤ l then
            Work.Spaces.supAbs (fun z θ => (z + 1) ^ k
              * Work.Spaces.pzIter k
                  (Work.Spaces.DthIter j (fun z θ => (D * A θ) * Hc z)) z θ
              * Real.sin (2 * θ) ^ (-(α / 5)) / (α + Real.sin (2 * θ)))
            else 0))
        ≤ ∑ j ∈ Finset.range (l + 1), ∑ k ∈ Finset.range (l + 1),
            (if 1 ≤ j ∧ k + j ≤ l then |D| * (B k * Kc) else 0) :=
      Finset.sum_le_sum (fun j hj => Finset.sum_le_sum (fun k hk => hterm2 j hj k hk))
    have hsum2eq : (∑ j ∈ Finset.range (l + 1), ∑ k ∈ Finset.range (l + 1),
          (if 1 ≤ j ∧ k + j ≤ l then |D| * (B k * Kc) else 0))
        = |D| * (∑ j ∈ Finset.range (l + 1), ∑ k ∈ Finset.range (l + 1),
            (if 1 ≤ j ∧ k + j ≤ l then B k * Kc else 0)) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun j hj => ?_)
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun k hk => ?_)
      by_cases h : 1 ≤ j ∧ k + j ≤ l <;> simp [h]
    have hsum1eq : (∑ k ∈ Finset.range (l + 1), |D| * (KA * B k))
        = |D| * (∑ k ∈ Finset.range (l + 1), KA * B k) :=
      (Finset.mul_sum (s := Finset.range (l + 1)) (f := fun k => KA * B k)
        (a := |D|)).symm
    calc (∑ k ∈ Finset.range (l + 1), Work.Spaces.supAbs (fun z θ => (z + 1) ^ k
            * Work.Spaces.pzIter k (fun z θ => (D * A θ) * Hc z) z θ))
          + ∑ j ∈ Finset.range (l + 1), ∑ k ∈ Finset.range (l + 1),
              (if 1 ≤ j ∧ k + j ≤ l then
                Work.Spaces.supAbs (fun z θ => (z + 1) ^ k
                  * Work.Spaces.pzIter k
                      (Work.Spaces.DthIter j (fun z θ => (D * A θ) * Hc z)) z θ
                  * Real.sin (2 * θ) ^ (-(α / 5)) / (α + Real.sin (2 * θ)))
                else 0)
        ≤ (∑ k ∈ Finset.range (l + 1), |D| * (KA * B k))
          + (∑ j ∈ Finset.range (l + 1), ∑ k ∈ Finset.range (l + 1),
              (if 1 ≤ j ∧ k + j ≤ l then |D| * (B k * Kc) else 0)) :=
          add_le_add hsum1 hsum2
      _ = |D| * ((∑ k ∈ Finset.range (l + 1), KA * B k)
          + ∑ j ∈ Finset.range (l + 1), ∑ k ∈ Finset.range (l + 1),
              (if 1 ≤ j ∧ k + j ≤ l then B k * Kc else 0)) := by
          rw [hsum1eq, hsum2eq, mul_add]

end Work.FTS.StrongPersist.H6Pair6Aux
end
-- ===== merged: Submission.Work.FTS.StrongPersist.H6Row6.radial_inv_wlInf6 =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `c/(1+z) ∈ 𝒲^{6,∞}`

The radial profile `z ↦ c/(1+z)` (a pure function of `z`, with no angular dependence)
belongs to `𝒲^{6,∞}` for every constant `c` and every exponent `α`; indeed the weight
`(1+z)^k` exactly cancels all but one power of `(1+z)` in the `k`-th `z`-derivative:

  `∂_z^k (c/(1+z)) = (-1)^k k! c (1+z)^{-(k+1)}`,  hence
  `|(1+z)^k ∂_z^k (c/(1+z))| ≤ k! |c|`.

The angular half of `WlInfMem` is trivial: the function does not depend on `θ`, so
`D_θ^j (c/(1+z)) = 0` for every `j ≥ 1` and each of the mixed suprema is that of the
zero function.

The closed form of `∂_z^k (1+z)^{-1}` is reused from
`Work.FTS.Nonlinear.FstarPkg` (`nInvClosed`, `iter_deriv_nInvClosed`,
`nInvClosed_weighted`), where it was developed for the profile `c2m(θ)·2α/(1+z)`.
-/

namespace Work.FTS.StrongPersist.H6Row6

/-- The `k`-th plain `z`-derivative of `z ↦ c/(1+z)` in closed form, for `z > -1`:
`(−1)^k k! c (1+z)^{−(k+1)}`, written through `FstarPkg.nInvClosed`. -/
private lemma pzIter_radialInv (c : ℝ) (k : ℕ) (z θ : ℝ) (hz : -1 < z) :
    Work.Spaces.pzIter k (fun z θ : ℝ => c / (1 + z)) z θ
      = c * Work.FTS.Nonlinear.FstarPkg.nInvClosed k z := by
  have hfun : (fun z θ : ℝ => c / (1 + z))
      = (fun z θ : ℝ => (fun _ : ℝ => c) θ * (fun z : ℝ => (1 + z)⁻¹) z) := by
    funext z θ
    simp [div_eq_mul_inv]
  rw [hfun]
  rw [Work.Spaces.pzIter_decomp]
  rw [Work.FTS.Nonlinear.FstarPkg.iter_deriv_nInvClosed k z hz]

/-- The weighted `z`-bound: `|(1+z)^k ∂_z^k (c/(1+z))| ≤ k! · |c|` on the half-line `z ≥ 0`. -/
private lemma radialInv_z_bound (c : ℝ) (k : ℕ) (z θ : ℝ) (hz : z ∈ Work.Spaces.Iz) :
    |(z + 1) ^ k * Work.Spaces.pzIter k (fun z θ : ℝ => c / (1 + z)) z θ|
      ≤ |c| * (k.factorial : ℝ) := by
  have hz0 : (0 : ℝ) ≤ z := hz
  have hz1 : -1 < z := by linarith
  rw [pzIter_radialInv c k z θ hz1]
  rw [show (z + 1) ^ k * (c * Work.FTS.Nonlinear.FstarPkg.nInvClosed k z)
      = c * ((z + 1) ^ k * Work.FTS.Nonlinear.FstarPkg.nInvClosed k z) by ring]
  rw [abs_mul]
  exact mul_le_mul_of_nonneg_left
    (Work.FTS.Nonlinear.FstarPkg.nInvClosed_weighted k z hz0) (abs_nonneg c)

/-- Every `z`-iterate of the zero function is the zero function. -/
private lemma pzIter_zero_fun (k : ℕ) :
    Work.Spaces.pzIter k (fun _ _ : ℝ => (0 : ℝ)) = fun _ _ => (0 : ℝ) := by
  induction k with
  | zero => rfl
  | succ k ih =>
      rw [Work.Spaces.pzIter_succ, ih]
      funext z θ
      simp [Work.Spaces.pz]

/-- The angular content of `z ↦ c/(1+z)` is empty: `D_θ^j (c/(1+z)) = 0` for every `j ≥ 1`. -/
private lemma DthIter_radial_eq_zero (c : ℝ) : ∀ j : ℕ, 1 ≤ j →
    Work.Spaces.DthIter j (fun z θ : ℝ => c / (1 + z)) = fun _ _ => (0 : ℝ) := by
  intro j
  induction j with
  | zero => intro hj; exact absurd hj (by omega)
  | succ j ih =>
    intro hj
    cases j with
    | zero =>
      funext z θ
      simp [Work.Spaces.Dth, Work.Spaces.pth]
    | succ j =>
      have hih : Work.Spaces.DthIter (j + 1) (fun z θ : ℝ => c / (1 + z))
          = fun _ _ => (0 : ℝ) := ih (by omega)
      rw [Work.Spaces.DthIter_succ, hih]
      funext z θ
      simp [Work.Spaces.Dth, Work.Spaces.pth]

theorem radial_inv_wlInf6 (c : ℝ) : ∀ α : ℝ, 0 < α → α ≤ 1 →
    Work.Spaces.WlInfMem α 6 (fun z θ : ℝ => c / (1 + z)) := by
  intro α hα hα1
  constructor
  · intro k hk
    refine ⟨|c| * (k.factorial : ℝ), ?_⟩
    rintro y ⟨z, hz, θ, hθ, rfl⟩
    exact radialInv_z_bound c k z θ hz
  · intro j hj k hk hj1 hjk
    refine ⟨0, ?_⟩
    rintro y ⟨z, hz, θ, hθ, rfl⟩
    have hzero : (z + 1) ^ k * Work.Spaces.pzIter k
        (Work.Spaces.DthIter j (fun z θ : ℝ => c / (1 + z))) z θ
        * Real.sin (2 * θ) ^ (-(α / 5)) / (α + Real.sin (2 * θ)) = 0 := by
      rw [DthIter_radial_eq_zero c j hj1, pzIter_zero_fun]
      simp
    have hbeta : (fun z θ => (z + 1) ^ k * Work.Spaces.pzIter k
          (Work.Spaces.DthIter j (fun z θ : ℝ => c / (1 + z))) z θ
          * Real.sin (2 * θ) ^ (-(α / 5)) / (α + Real.sin (2 * θ))) z θ
        = (z + 1) ^ k * Work.Spaces.pzIter k
          (Work.Spaces.DthIter j (fun z θ : ℝ => c / (1 + z))) z θ
          * Real.sin (2 * θ) ^ (-(α / 5)) / (α + Real.sin (2 * θ)) := rfl
    rw [hbeta, hzero, abs_zero]

end Work.FTS.StrongPersist.H6Row6
end
-- ===== merged: Submission.Work.FTS_EllLimOK.BoxRegAux.Defs =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS_EllLimOK

set_option autoImplicit false

/-! ## The linear functional with two given slopes -/

/-- The continuous linear functional `(u,v) ↦ u * x + v * y` on `ℝ × ℝ`: the Fréchet derivative
of a function whose two partial derivatives are `x` and `y`. -/
def ellCop (x y : ℝ) : ℝ × ℝ →L[ℝ] ℝ :=
  (ContinuousLinearMap.toSpanSingleton ℝ x).coprod (ContinuousLinearMap.toSpanSingleton ℝ y)

theorem ellCop_apply (x y : ℝ) (v : ℝ × ℝ) : ellCop x y v = v.1 * x + v.2 * y := by
  simp only [ellCop, ContinuousLinearMap.coprod_apply, ContinuousLinearMap.toSpanSingleton_apply]
  ring

@[simp] theorem ellCop_zero_zero : ellCop 0 0 = 0 :=
  ContinuousLinearMap.ext fun v => by simp [ellCop_apply]

/-! ## The `(x,y) ↦ ellCop x y` continuous linear map -/

/-- The continuous linear map `(x,y) ↦ ellCop x y`, from `ℝ × ℝ` to the space of continuous
linear functionals on `ℝ × ℝ`.  It is the "curried" version of the second derivative: composing
it with `(dA, dB)` (the two partials of the two first partials of a function) produces the second
Fréchet derivative. -/
def copBilin : (ℝ × ℝ) →L[ℝ] ((ℝ × ℝ) →L[ℝ] ℝ) :=
  (ContinuousLinearMap.fst ℝ ℝ ℝ).smulRight (ContinuousLinearMap.fst ℝ ℝ ℝ) +
    (ContinuousLinearMap.snd ℝ ℝ ℝ).smulRight (ContinuousLinearMap.snd ℝ ℝ ℝ)

theorem copBilin_apply (a b : ℝ) : copBilin (a, b) = ellCop a b := by
  refine ContinuousLinearMap.ext fun v => ?_
  rw [show ellCop a b v = v.1 * a + v.2 * b from by
    simp only [ellCop, ContinuousLinearMap.coprod_apply,
      ContinuousLinearMap.toSpanSingleton_apply]
    ring]
  simp only [copBilin, add_apply, ContinuousLinearMap.smulRight_apply, smul_apply, smul_eq_mul]
  have h1 : (ContinuousLinearMap.fst ℝ ℝ ℝ) (a, b) = a := rfl
  have h2 : (ContinuousLinearMap.snd ℝ ℝ ℝ) (a, b) = b := rfl
  have h3 : (ContinuousLinearMap.fst ℝ ℝ ℝ) v = v.1 := rfl
  have h4 : (ContinuousLinearMap.snd ℝ ℝ ℝ) v = v.2 := rfl
  rw [h1, h2, h3, h4]
  ring


/-- Continuity of `y ↦ ellCop (A y) (B y)` from continuity of `A` and `B`. -/
theorem continuousWithinAt_ellCop {A B : (ℝ × ℝ) → ℝ} {s : Set (ℝ × ℝ)} {p : ℝ × ℝ}
    (hA : ContinuousWithinAt A s p) (hB : ContinuousWithinAt B s p) :
    ContinuousWithinAt (fun y => ellCop (A y) (B y)) s p := by
  have h1 : ContinuousWithinAt (fun y => copBilin (A y, B y)) s p :=
    (ContinuousLinearMap.continuous copBilin).continuousAt.comp_continuousWithinAt
      (hA.prodMk hB)
  exact h1.congr (fun y _ => (copBilin_apply (A y) (B y)).symm)
    (copBilin_apply (A p) (B p)).symm

/-! ## The clamping of the angle -/

/-- The `1`-Lipschitz retraction of the angle onto `[0,π/2]`: the identity on the closed
quadrant. -/
def clampθ (θ : ℝ) : ℝ := max 0 (min θ (Real.pi / 2))

theorem clampθ_nonneg (θ : ℝ) : 0 ≤ clampθ θ := le_max_left _ _

theorem clampθ_le (θ : ℝ) : clampθ θ ≤ Real.pi / 2 :=
  max_le (by linarith [Real.pi_pos]) (min_le_right _ _)

theorem clampθ_eq_of_mem {θ : ℝ} (h : θ ∈ Set.Icc 0 (Real.pi / 2)) : clampθ θ = θ := by
  rw [clampθ, min_eq_left h.2, max_eq_right h.1]

theorem abs_clampθ_sub_clampθ_le (x y : ℝ) : |clampθ x - clampθ y| ≤ |x - y| := by
  have h1 : |min x (Real.pi / 2) - min y (Real.pi / 2)| ≤ |x - y| := by
    refine le_trans (abs_min_sub_min_le_max x (Real.pi / 2) y (Real.pi / 2)) ?_
    rw [max_le_iff]
    exact ⟨le_rfl, by simp⟩
  have h2 : |max 0 (min x (Real.pi / 2)) - max 0 (min y (Real.pi / 2))| ≤
      |min x (Real.pi / 2) - min y (Real.pi / 2)| := by
    refine le_trans (abs_max_sub_max_le_max 0 (min x (Real.pi / 2)) 0 (min y (Real.pi / 2))) ?_
    rw [max_le_iff]
    exact ⟨by simp, le_rfl⟩
  calc |clampθ x - clampθ y| = |max 0 (min x (Real.pi / 2)) - max 0 (min y (Real.pi / 2))| := rfl
    _ ≤ |min x (Real.pi / 2) - min y (Real.pi / 2)| := h2
    _ ≤ |x - y| := h1

/-- The retraction of `ℝ × ℝ` onto the closed right half plane in the second variable, fixing
the closed quadrant `[0,∞) × [0,π/2]` (and in particular every box `cbox a b`). -/
def boxClamp (p : ℝ × ℝ) : ℝ × ℝ := (p.1, clampθ p.2)

@[simp] theorem boxClamp_fst (p : ℝ × ℝ) : (boxClamp p).1 = p.1 := rfl

@[simp] theorem boxClamp_snd (p : ℝ × ℝ) : (boxClamp p).2 = clampθ p.2 := rfl





/-! ## The order-`≤ 2` jet vector -/








/-- Componentwise extraction of uniform convergence from uniform convergence of the jet family. -/
theorem tendstoUniformlyOn_jetVec_component {F : ℕ → ℝ × ℝ → (Fin 6 → ℝ)}
    {g : ℝ × ℝ → (Fin 6 → ℝ)} {s : Set (ℝ × ℝ)}
    (h : TendstoUniformlyOn F g Filter.atTop s) (m : Fin 6) :
    TendstoUniformlyOn (fun n p => F n p m) (fun p => g p m) Filter.atTop s := by
  rw [Metric.tendstoUniformlyOn_iff] at h ⊢
  intro ε hε
  filter_upwards [h ε hε] with n hn p hp
  exact lt_of_le_of_lt (dist_le_pi_dist (g p) (F n p) m) (hn p hp)



end Work.FTS_EllLimOK
end
end
-- ===== merged: Submission.Work.FTS_EllLimOK.BoxRegAux.jet_partials_facts =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS_EllLimOK.BoxRegAux

open Set Filter
open scoped Real Topology

/-! ## Auxiliary objects and lemmas

The six partials of `f` of order `≤ 2` are identified with the `iteratedFDeriv` of
`F = Function.uncurry f` evaluated on the coordinate directions `(1,0)`, `(0,1)`; continuity, the
bounds and the Lipschitz bounds are all read off from the operator norms of
`iteratedFDeriv ℝ k F` (and its derivative).  The key structural facts used are

* `iteratedFDeriv_one_apply` / `iteratedFDeriv_succ_apply_left`, which express the evaluations of
  `iteratedFDeriv` on a `Fin n`-tuple of directions;
* `fderiv_continuousMultilinear_apply_const`, which computes the derivative of
  `p ↦ iteratedFDeriv ℝ n F p m` at fixed `m` as `(fderiv (iteratedFDeriv ℝ n F) p).flipMultilinear m`;
* `norm_fderiv_iteratedFDeriv`, giving `‖fderiv (iteratedFDeriv ℝ n F) p‖ = ‖iteratedFDeriv ℝ (n+1) F p‖`;
* the mean value inequality `Convex.norm_image_sub_le_of_norm_hasFDerivWithin_le` on the convex box.

Everything here is `sorry`-free. -/

/-- The open smoothness set `(-1,∞) × (-1, π/2+1)` of the hypothesis. -/
abbrev nbhU : Set (ℝ × ℝ) := Set.Ioi (-1) ×ˢ Set.Ioo (-1) (Real.pi / 2 + 1)

/-- The coordinate direction `e_z = (1,0)`. -/
def dz : ℝ × ℝ := (1, 0)

/-- The coordinate direction `e_θ = (0,1)`. -/
def dth : ℝ × ℝ := (0, 1)

/-- The constant family `Fin 1 → ℝ × ℝ` with value `u`. -/
def dir1 (u : ℝ × ℝ) : Fin 1 → ℝ × ℝ := fun _ => u

/-- Prepending `u` to a family `m : Fin n → ℝ × ℝ`. -/
def consD {n : ℕ} (u : ℝ × ℝ) (m : Fin n → ℝ × ℝ) : Fin (n + 1) → ℝ × ℝ := Fin.cases u m

theorem nbhU_open : IsOpen nbhU := isOpen_Ioi.prod isOpen_Ioo

theorem norm_dz_le_one : ‖dz‖ ≤ 1 := by simp [dz, Prod.norm_def]

theorem norm_dth_le_one : ‖dth‖ ≤ 1 := by simp [dth, Prod.norm_def]

/-- The product of the norms of a constant `Fin 1`-family. -/
theorem prod_dir1_le_one (u : ℝ × ℝ) (hu : ‖u‖ ≤ 1) : ∏ i : Fin 1, ‖dir1 u i‖ ≤ 1 := by
  rw [Fin.prod_univ_succ]; simpa [dir1] using hu

/-- The product of the norms of `Fin.cons w (fun _ => u)`. -/
theorem prod_consD_dir1_le_one (u w : ℝ × ℝ) (hu : ‖u‖ ≤ 1) (hw : ‖w‖ ≤ 1) :
    ∏ i : Fin 2, ‖consD w (dir1 u) i‖ ≤ 1 := by
  rw [Fin.prod_univ_succ, Fin.prod_univ_succ]
  simp only [Fin.prod_univ_zero, mul_one, consD, dir1, Fin.cases_zero, Fin.cases_succ]
  nlinarith [norm_nonneg u, norm_nonneg w]




/-- Differentiability of `iteratedFDeriv ℝ n F` (`n ≤ 3`) inside the smoothness set. -/
theorem differentiableAt_iterDF {F : ℝ × ℝ → ℝ} {n : ℕ} (hsm : ContDiffOn ℝ 4 F nbhU)
    (hn : n ≤ 3) {p : ℝ × ℝ} (hp : p ∈ nbhU) : DifferentiableAt ℝ (iteratedFDeriv ℝ n F) p := by
  have hcd : ContDiffAt ℝ 4 F p := hsm.contDiffAt (nbhU_open.mem_nhds hp)
  have h : ContDiffAt ℝ (1 : WithTop ℕ∞) (iteratedFDeriv ℝ n F) p :=
    hcd.iteratedFDeriv_right (m := (1 : WithTop ℕ∞)) (i := n)
      (by exact_mod_cast (by omega : 1 + n ≤ 4))
  exact h.differentiableAt (by norm_num)




/-! ## The identification of the partials with `iteratedFDeriv` -/

/-- The `z`-partial is `iteratedFDeriv ℝ 1 F` on the direction family `dir1 dz`. -/
theorem pz_eq_iterDF1 {f : ℝ → ℝ → ℝ} (hsm : ContDiffOn ℝ 4 (Function.uncurry f) nbhU) :
    ∀ p ∈ nbhU, Work.Spaces.pz f p.1 p.2
      = iteratedFDeriv ℝ 1 (Function.uncurry f) p (dir1 dz) := by
  intro p hp
  rw [Work.Spaces.pz_eq_fderiv
    ((hsm.contDiffAt (nbhU_open.mem_nhds hp)).differentiableAt (by norm_num))]
  simp [iteratedFDeriv_one_apply, dir1, dz]

/-- The `θ`-partial is `iteratedFDeriv ℝ 1 F` on the direction family `dir1 dth`. -/
theorem pth_eq_iterDF1 {f : ℝ → ℝ → ℝ} (hsm : ContDiffOn ℝ 4 (Function.uncurry f) nbhU) :
    ∀ p ∈ nbhU, Work.Spaces.pth f p.1 p.2
      = iteratedFDeriv ℝ 1 (Function.uncurry f) p (dir1 dth) := by
  intro p hp
  rw [Work.Spaces.pth_eq_fderiv
    ((hsm.contDiffAt (nbhU_open.mem_nhds hp)).differentiableAt (by norm_num))]
  simp [iteratedFDeriv_one_apply, dir1, dth]

/-- The eventual-equality form of `pz_eq_iterDF1`. -/
theorem evEq_uncurry_pz {f : ℝ → ℝ → ℝ} (hsm : ContDiffOn ℝ 4 (Function.uncurry f) nbhU) :
    EqOn (Function.uncurry (Work.Spaces.pz f))
      (fun p => iteratedFDeriv ℝ 1 (Function.uncurry f) p (dir1 dz)) nbhU := by
  intro p hp
  change Work.Spaces.pz f p.1 p.2 = _
  exact pz_eq_iterDF1 hsm p hp

/-- The eventual-equality form of `pth_eq_iterDF1`. -/
theorem evEq_uncurry_pth {f : ℝ → ℝ → ℝ} (hsm : ContDiffOn ℝ 4 (Function.uncurry f) nbhU) :
    EqOn (Function.uncurry (Work.Spaces.pth f))
      (fun p => iteratedFDeriv ℝ 1 (Function.uncurry f) p (dir1 dth)) nbhU := by
  intro p hp
  change Work.Spaces.pth f p.1 p.2 = _
  exact pth_eq_iterDF1 hsm p hp

/-- **The Fréchet derivative of the first partial in an arbitrary direction `w`**: for a function
`g` whose uncurried form agrees with `q ↦ iteratedFDeriv ℝ 1 F q (dir1 u)` near `p`, the
derivative in the direction `w` is the `iteratedFDeriv ℝ 2` evaluated on the two directions `w`
and `u`. -/
theorem fderiv_uncurry_eq_iterDF2 {f g : ℝ → ℝ → ℝ}
    (hsm : ContDiffOn ℝ 4 (Function.uncurry f) nbhU) {p : ℝ × ℝ} (hp : p ∈ nbhU)
    {u : ℝ × ℝ}
    (hg : Function.uncurry g =ᶠ[𝓝 p]
      (fun q => iteratedFDeriv ℝ 1 (Function.uncurry f) q (dir1 u)))
    (w : ℝ × ℝ) :
    fderiv ℝ (Function.uncurry g) p w
      = iteratedFDeriv ℝ 2 (Function.uncurry f) p (consD w (dir1 u)) := by
  have hK1diff : DifferentiableAt ℝ (iteratedFDeriv ℝ 1 (Function.uncurry f)) p :=
    differentiableAt_iterDF hsm (by norm_num) hp
  rw [hg.fderiv_eq, fderiv_continuousMultilinear_apply_const hK1diff,
    ContinuousLinearMap.flipMultilinear_apply_apply, iteratedFDeriv_succ_apply_left]
  rfl

/-- The eventual-equality form of `evEq_uncurry_pz`. -/
theorem evEqAt_uncurry_pz {f : ℝ → ℝ → ℝ} (hsm : ContDiffOn ℝ 4 (Function.uncurry f) nbhU)
    {p : ℝ × ℝ} (hp : p ∈ nbhU) :
    Function.uncurry (Work.Spaces.pz f) =ᶠ[𝓝 p]
      (fun q => iteratedFDeriv ℝ 1 (Function.uncurry f) q (dir1 dz)) := by
  filter_upwards [nbhU_open.mem_nhds hp] with q hq
  exact evEq_uncurry_pz hsm hq

/-- The eventual-equality form of `evEq_uncurry_pth`. -/
theorem evEqAt_uncurry_pth {f : ℝ → ℝ → ℝ} (hsm : ContDiffOn ℝ 4 (Function.uncurry f) nbhU)
    {p : ℝ × ℝ} (hp : p ∈ nbhU) :
    Function.uncurry (Work.Spaces.pth f) =ᶠ[𝓝 p]
      (fun q => iteratedFDeriv ℝ 1 (Function.uncurry f) q (dir1 dth)) := by
  filter_upwards [nbhU_open.mem_nhds hp] with q hq
  exact evEq_uncurry_pth hsm hq


/-- `∂_θ∂_z f` as an `iteratedFDeriv ℝ 2`. -/
theorem pth_pz_eq {f : ℝ → ℝ → ℝ} (hsm : ContDiffOn ℝ 4 (Function.uncurry f) nbhU)
    {p : ℝ × ℝ} (hp : p ∈ nbhU) :
    Work.Spaces.pth (Work.Spaces.pz f) p.1 p.2
      = iteratedFDeriv ℝ 2 (Function.uncurry f) p (consD dth (dir1 dz)) := by
  have hdiff : DifferentiableAt ℝ (Function.uncurry (Work.Spaces.pz f)) p :=
    DifferentiableAt.congr_of_eventuallyEq
      ((differentiableAt_iterDF hsm (by norm_num) hp).continuousMultilinear_apply_const (dir1 dz))
      (evEqAt_uncurry_pz hsm hp)
  rw [Work.Spaces.pth_eq_fderiv hdiff]
  change fderiv ℝ (Function.uncurry (Work.Spaces.pz f)) p dth = _
  rw [fderiv_uncurry_eq_iterDF2 hsm hp (evEqAt_uncurry_pz hsm hp) dth]

/-- `∂_z∂_θ f` as an `iteratedFDeriv ℝ 2`. -/
theorem pz_pth_eq {f : ℝ → ℝ → ℝ} (hsm : ContDiffOn ℝ 4 (Function.uncurry f) nbhU)
    {p : ℝ × ℝ} (hp : p ∈ nbhU) :
    Work.Spaces.pz (Work.Spaces.pth f) p.1 p.2
      = iteratedFDeriv ℝ 2 (Function.uncurry f) p (consD dz (dir1 dth)) := by
  have hdiff : DifferentiableAt ℝ (Function.uncurry (Work.Spaces.pth f)) p :=
    DifferentiableAt.congr_of_eventuallyEq
      ((differentiableAt_iterDF hsm (by norm_num) hp).continuousMultilinear_apply_const (dir1 dth))
      (evEqAt_uncurry_pth hsm hp)
  rw [Work.Spaces.pz_eq_fderiv hdiff]
  change fderiv ℝ (Function.uncurry (Work.Spaces.pth f)) p dz = _
  rw [fderiv_uncurry_eq_iterDF2 hsm hp (evEqAt_uncurry_pth hsm hp) dz]



end Work.FTS_EllLimOK.BoxRegAux
end
-- ===== merged: Submission.Work.FTS_EllLimOK.EGap.aemeasurable_uncurry_of_boxReg =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS_EllLimOK.EGap

/-- `BoxReg δ` knows `δ` is jointly `C²` on every closed box `[a,b] × [0,π/2]` with `0 < a ≤ b`;
these boxes cover the region `(0,∞) × [0,π/2]` *locally* (a neighbourhood of any of its points
meets the region only inside one box), so `δ` is continuous on the region.  Hence it is Borel
measurable viewed as a function on the subtype, and `AEMeasurable` for the measure
`volume|_{(0,∞)} ⊗ volume|_{[0,π/2]}`, which is `(volume ⊗ volume)` restricted to the region. -/
theorem aemeasurable_uncurry_of_boxReg {δ : ℝ → ℝ → ℝ} (hbox : Work.FTS_EllLimOK.BoxReg δ) :
    AEMeasurable (Function.uncurry δ)
      ((MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)) := by
  have hms : MeasurableSet (Set.Ioi (0 : ℝ) ×ˢ Work.Spaces.Iθ) :=
    measurableSet_Ioi.prod measurableSet_Icc
  rw [MeasureTheory.Measure.prod_restrict]
  refine aemeasurable_restrict_of_measurable_subtype hms ?_
  -- `δ` is `C²` (hence continuous) on the region `s = (0,∞) × [0,π/2]`.
  have hcd : ContDiffOn ℝ 2 (Function.uncurry δ) (Set.Ioi (0 : ℝ) ×ˢ Work.Spaces.Iθ) := by
    apply contDiffOn_of_locally_contDiffOn
    rintro ⟨z, θ⟩ ⟨hz, hθ⟩
    change 0 < z at hz
    -- the open set `(z/2, 2z) × (-1, π/2+1)` meets `s` inside the closed box `[z/2, 2z] × [0,π/2]`
    refine ⟨Set.Ioo (z / 2) (2 * z) ×ˢ Set.Ioo (-1) (π / 2 + 1), ?_, ?_, ?_⟩
    · exact isOpen_Ioo.prod isOpen_Ioo
    · exact ⟨⟨by linarith, by linarith⟩, ⟨by linarith [hθ.1], by linarith [hθ.2]⟩⟩
    · refine (hbox (z / 2) (2 * z) (by linarith) (by linarith)).mono ?_
      rintro ⟨p, q⟩ ⟨⟨hpz, hpq⟩, hu⟩
      exact ⟨⟨le_of_lt hu.1.1, le_of_lt hu.1.2⟩, hpq⟩
  have hcont : ContinuousOn (Function.uncurry δ) (Set.Ioi (0 : ℝ) ×ˢ Work.Spaces.Iθ) :=
    ContDiffOn.continuousOn hcd
  have : Continuous
      (fun x : (Set.Ioi (0 : ℝ) ×ˢ Work.Spaces.Iθ : Set (ℝ × ℝ)) => Function.uncurry δ x) :=
    continuousOn_iff_continuous_domRestrict.mp hcont
  exact this.measurable

end Work.FTS_EllLimOK.EGap
end
-- ===== merged: Submission.Work.FTS_EllLimOK.FstarOde.Fstar_sq_HkIntegrand_le =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS_EllLimOK.FstarOde

set_option autoImplicit false

/-! ## The level-`0` integrand and the pointwise weight bookkeeping

At level `k = 0` the `H^k`-integrand is a *single* square (`Work.Spaces.HkIntegrand` has the
one `D_z`-term `i = 0` and an empty mixed double sum),

`HkIntegrand α 0 F z θ = (F z θ · w(z) / sin(2θ)^{η/2})²`,  `w(z) = (1+z)²/z²`,

so that for `z > 0` the factor `z⁴` of the estimate below is exactly the reciprocal of the
angular weight of `F`:

`z⁴ · HkIntegrand α 0 F z θ = (F z θ · (1+z)² / sin(2θ)^{η/2})²`.

Since `(1+z)² ≥ 1` and `sin(2θ)^{η/2} ≤ 1` in the *interior* `θ ∈ (0,π/2)`, the bracket is at
least `1` there, and hence `F(z,θ)² ≤ z⁴ · HkIntegrand α 0 F z θ`.  This fails only at the two
endpoints `θ = 0, π/2` (where `sin(2θ) = 0` and the totalised division makes both `w/s^{η/2}`
and the integrand vanish) — a null set, which is why the comparison of the two integrals is
taken almost everywhere. -/

/-- At level `k = 0` the `H^k`-integrand is the single square
`(F z θ · w(z) / sin(2θ)^{η/2})²`. -/
private lemma HkIntegrand_zero_eq (α : ℝ) (F : ℝ → ℝ → ℝ) (z θ : ℝ) :
    Work.Spaces.HkIntegrand α 0 F z θ
      = (F z θ * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2 := by
  simp [Work.Spaces.HkIntegrand]

/-- **Pointwise weight bookkeeping.**  For `z > 0` and `θ ∈ (0,π/2)`,
`F(z,θ)² ≤ z⁴ · HkIntegrand α 0 F z θ`: the right hand side is
`(F(z,θ) · (1+z)²/sin(2θ)^{η/2})²` and the bracket is `≥ 1`. -/
private lemma fstar_sq_pointwise_le {α z θ : ℝ} (hz : 0 < z)
    (hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)) (δ : ℝ → ℝ → ℝ) :
    (δ z θ) ^ 2 ≤ z ^ 4 * Work.Spaces.HkIntegrand α 0 δ z θ := by
  have hz0 : z ≠ 0 := ne_of_gt hz
  have hspos : 0 < Real.sin (2 * θ) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2])
  have hspow_pos : 0 < Real.sin (2 * θ) ^ (Work.Spaces.eta / 2) :=
    Real.rpow_pos_of_pos hspos _
  have hspow_le : Real.sin (2 * θ) ^ (Work.Spaces.eta / 2) ≤ 1 :=
    Real.rpow_le_one hspos.le (Real.sin_le_one _) (by linarith [Work.Spaces.eta_nonneg])
  have hge : 1 ≤ (1 + z) ^ 2 / Real.sin (2 * θ) ^ (Work.Spaces.eta / 2) := by
    rw [le_div_iff₀ hspow_pos]
    have h1z : (1 : ℝ) ≤ (1 + z) ^ 2 := one_le_pow₀ (by linarith)
    linarith
  -- the `z⁴`-weighted integrand is the square `(δ z θ · (1+z)²/sin(2θ)^{η/2})²`
  rw [HkIntegrand_zero_eq,
    show z ^ 4 = (z ^ 2) ^ 2 by ring, ← mul_pow,
    show z ^ 2 * (δ z θ * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2)))
        = δ z θ * ((z ^ 2 * Work.Spaces.w z) / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))
      from by ring,
    show z ^ 2 * Work.Spaces.w z = (1 + z) ^ 2 from by rw [Work.Spaces.w]; field_simp]
  -- whose bracket is at least `1`
  have hc2 : (1 : ℝ) ≤ ((1 + z) ^ 2 / Real.sin (2 * θ) ^ (Work.Spaces.eta / 2)) ^ 2 := by
    nlinarith [hge, sq_nonneg ((1 + z) ^ 2 / Real.sin (2 * θ) ^ (Work.Spaces.eta / 2) - 1)]
  calc (δ z θ) ^ 2 = (δ z θ) ^ 2 * 1 := by ring
    _ ≤ (δ z θ) ^ 2 * ((1 + z) ^ 2 / Real.sin (2 * θ) ^ (Work.Spaces.eta / 2)) ^ 2 :=
        mul_le_mul_of_nonneg_left hc2 (sq_nonneg _)
    _ = (δ z θ * ((1 + z) ^ 2 / Real.sin (2 * θ) ^ (Work.Spaces.eta / 2))) ^ 2 := by ring

/-- The pointwise comparison of the previous lemma holds almost everywhere on `Iθ`: the only
angles of `Iθ` at which `sin(2θ)` vanishes are the two endpoints `θ = 0, π/2` (in the interior
`sin(2θ) > 0`), a null set. -/
private lemma ae_fstar_sq_le_HkIntegrand {δ : ℝ → ℝ → ℝ} {α z : ℝ} (hz : 0 < z) :
    (fun θ : ℝ => (δ z θ) ^ 2) ≤ᵐ[volume.restrict Work.Spaces.Iθ]
      (fun θ : ℝ => z ^ 4 * Work.Spaces.HkIntegrand α 0 δ z θ) := by
  have hIθ : MeasurableSet Work.Spaces.Iθ := measurableSet_Icc
  have hsub : {θ : ℝ | θ ∈ Work.Spaces.Iθ ∧ Real.sin (2 * θ) = 0}
      ⊆ ({0} ∪ {Real.pi / 2} : Set ℝ) := by
    intro θ hθ
    simp only [Set.mem_ofPred_eq] at hθ
    obtain ⟨hθI, hsin⟩ := hθ
    rw [Set.mem_union, Set.mem_singleton_iff, Set.mem_singleton_iff]
    by_contra hcon
    rw [not_or] at hcon
    obtain ⟨hne0, hne2⟩ := hcon
    have hθ1 : 0 < θ := lt_of_le_of_ne hθI.1 (Ne.symm hne0)
    have hθ2 : θ < Real.pi / 2 := lt_of_le_of_ne hθI.2 hne2
    have hpos : 0 < Real.sin (2 * θ) :=
      Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith)
    linarith
  have hnull : volume {θ : ℝ | θ ∈ Work.Spaces.Iθ ∧ Real.sin (2 * θ) = 0} = 0 :=
    measure_mono_null hsub (measure_union_null (measure_singleton (0 : ℝ)) (measure_singleton _))
  change ∀ᵐ θ ∂(volume.restrict Work.Spaces.Iθ),
    (δ z θ) ^ 2 ≤ z ^ 4 * Work.Spaces.HkIntegrand α 0 δ z θ
  rw [MeasureTheory.ae_restrict_iff' hIθ, MeasureTheory.ae_iff]
  refine measure_mono_null ?_ hnull
  intro θ hθ
  simp only [Set.mem_ofPred_eq] at hθ ⊢
  obtain ⟨hθI, hne⟩ := Classical.not_imp.mp hθ
  refine ⟨hθI, ?_⟩
  by_contra hsin
  have hθ1 : 0 < θ := lt_of_le_of_ne hθI.1 (fun h0 => hsin (by rw [← h0]; norm_num))
  have hθ2 : θ < Real.pi / 2 := lt_of_le_of_ne hθI.2
    (fun h2 => hsin (by rw [h2, show 2 * (Real.pi / 2) = Real.pi by ring, Real.sin_pi]))
  exact (not_lt.mpr (fstar_sq_pointwise_le hz ⟨hθ1, hθ2⟩ δ)) (not_le.mp hne)

/-- **The angular-`L²` bound for the moment `F_*` against the level-`0` `H`-integrand.**

`BoxReg` makes the slices of `δ` continuous on the compact interval `Iθ`, so `θ ↦ δ(z,θ)²` is
integrable there and Cauchy–Schwarz in its discriminant form
(`Work.Elliptic.Fstar_sq_le`) gives

`F_*(z)² ≤ (π/2) ∫_θ δ(z,θ)² dθ`.

The pointwise weight bookkeeping (`ae_fstar_sq_le_HkIntegrand`) upgrades the right hand side
to the level-`0` `H`-integrand: `δ(z,θ)² ≤ z⁴ · HkIntegrand α 0 δ z θ` for a.e. `θ`, whence

`F_*(z)² ≤ (π/2) z⁴ ∫_θ HkIntegrand α 0 δ z θ`. -/
theorem Fstar_sq_HkIntegrand_le {α : ℝ} {δ : ℝ → ℝ → ℝ}
    (hbox : Work.FTS_EllLimOK.BoxReg δ)
    (hHk : Work.Spaces.HkMem α 0 δ) :
    ∀ z ∈ Set.Ioi (0 : ℝ),
      (Work.Elliptic.Fstar δ z) ^ 2
        ≤ (π / 2) * z ^ 4 * (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 0 δ z θ) := by
  intro z hz
  have hz0 : (0 : ℝ) < z := hz
  have hzI : z ∈ Work.Spaces.Iz := le_of_lt hz0
  -- the slice of `δ` is continuous on the compact interval, so its square is integrable there
  have hslice : ContinuousOn (fun θ => δ z θ) (Set.Icc 0 (Real.pi / 2)) :=
    (hbox.slice hz).continuousOn
  have hIntδ : IntegrableOn (fun θ => (δ z θ) ^ 2) Work.Spaces.Iθ :=
    (hslice.pow 2).integrableOn_compact isCompact_Icc
  have hIntHk : IntegrableOn (fun θ => Work.Spaces.HkIntegrand α 0 δ z θ) Work.Spaces.Iθ :=
    hHk.1 z hzI
  -- comparison of the two slice integrals, almost everywhere
  have hmono : ∫ θ in Work.Spaces.Iθ, (δ z θ) ^ 2
      ≤ ∫ θ in Work.Spaces.Iθ, z ^ 4 * Work.Spaces.HkIntegrand α 0 δ z θ :=
    integral_mono_ae hIntδ (hIntHk.const_mul (z ^ 4)) (ae_fstar_sq_le_HkIntegrand hz0)
  have hmono' : ∫ θ in Work.Spaces.Iθ, (δ z θ) ^ 2
      ≤ z ^ 4 * ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 0 δ z θ := by
    calc ∫ θ in Work.Spaces.Iθ, (δ z θ) ^ 2
        ≤ ∫ θ in Work.Spaces.Iθ, z ^ 4 * Work.Spaces.HkIntegrand α 0 δ z θ := hmono
      _ = z ^ 4 * ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 0 δ z θ :=
          MeasureTheory.integral_const_mul _ _
  -- Cauchy–Schwarz for the angular moment, then the weight bookkeeping
  have hCS := Work.Elliptic.Fstar_sq_le δ z hIntδ
  calc (Work.Elliptic.Fstar δ z) ^ 2
      ≤ (π / 2) * ∫ θ in Work.Spaces.Iθ, (δ z θ) ^ 2 := hCS
    _ ≤ (π / 2) * (z ^ 4 * ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 0 δ z θ) :=
        mul_le_mul_of_nonneg_left hmono' (by linarith [Real.pi_pos])
    _ = (π / 2) * z ^ 4 * (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 0 δ z θ) := by ring

end Work.FTS_EllLimOK.FstarOde
end
end
-- ===== merged: Submission.Work.FTS_EllLimOK.UniqDefs =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS_EllLimOK

set_option autoImplicit false

/-- The **difference of two profiles** — the solution of the homogeneous elliptic problem in the
uniqueness argument. -/
def diff (Ψ Ψ' : ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ := fun z θ => Ψ z θ - Ψ' z θ

@[simp] theorem diff_apply (Ψ Ψ' : ℝ → ℝ → ℝ) (z θ : ℝ) :
    diff Ψ Ψ' z θ = Ψ z θ - Ψ' z θ := rfl

/-- The **angular `L²` mass of the difference of two profiles**: `Φ(z) = ∫_θ δ(z,θ)² dθ`. -/
def PhiD (Ψ Ψ' : ℝ → ℝ → ℝ) : ℝ → ℝ :=
  fun z => ∫ θ in Work.Spaces.Iθ, (diff Ψ Ψ' z θ) ^ 2

@[simp] theorem PhiD_apply (Ψ Ψ' : ℝ → ℝ → ℝ) (z : ℝ) :
    PhiD Ψ Ψ' z = ∫ θ in Work.Spaces.Iθ, (diff Ψ Ψ' z θ) ^ 2 := rfl

theorem PhiD_nonneg (Ψ Ψ' : ℝ → ℝ → ℝ) (z : ℝ) : 0 ≤ PhiD Ψ Ψ' z :=
  integral_nonneg fun θ => sq_nonneg _

/-- `BoxReg` of the difference of two box-regular profiles. -/
theorem BoxReg.diff {Ψ Ψ' : ℝ → ℝ → ℝ} (hΨ : BoxReg Ψ) (hΨ' : BoxReg Ψ') :
    BoxReg (diff Ψ Ψ') := by
  change BoxReg (fun z θ => Ψ z θ - Ψ' z θ)
  exact hΨ.sub hΨ'

end Work.FTS_EllLimOK
end
end
-- ===== merged: Submission.Work.H2W.slot01Aux =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.H2W

open scoped Real Topology
open MeasureTheory Set Filter

set_option autoImplicit false

noncomputable section

local notation "Iθ" => Work.Spaces.Iθ
local notation "sEta" => Work.FTS.EllipticEst.sEta

/-- `sin(2θ) ≥ 0` on `Iθ = [0, π/2]`. -/
theorem sin_two_nonneg_Iθ' {θ : ℝ} (hθ : θ ∈ Iθ) : 0 ≤ Real.sin (2 * θ) :=
  Real.sin_nonneg_of_nonneg_of_le_pi (by linarith [hθ.1])
    (by linarith [hθ.2, Real.pi_pos])

/-- The angular weight `σ_γ(θ) = sin(2θ)^{2-γ}` is nonnegative on `Iθ`. -/
theorem sig_nonneg (α : ℝ) {θ : ℝ} (hθ : θ ∈ Iθ) :
    0 ≤ (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α) :=
  Real.rpow_nonneg (sin_two_nonneg_Iθ' hθ) _


/-- `s^2 * (s^(-(γ/2)))^2 = s^(2-γ)` for `0 ≤ s` and `0 < γ < 2`. -/
theorem sq_mul_sq_rpow_neg {s γ : ℝ} (hs : 0 ≤ s) (hγ0 : 0 < γ) (hγ2 : γ < 2) :
    s ^ 2 * (s ^ (-(γ / 2))) ^ 2 = s ^ (2 - γ) := by
  rw [show s ^ 2 = s ^ (2 : ℝ) from (Real.rpow_natCast s 2).symm,
    show (s ^ (-(γ / 2))) ^ 2 = (s ^ (-(γ / 2))) ^ (2 : ℝ) from
      (Real.rpow_natCast (s ^ (-(γ / 2))) 2).symm]
  rcases eq_or_lt_of_le hs with h | h
  · subst h
    rw [Real.zero_rpow (by linarith : (-(γ / 2)) ≠ 0),
      Real.zero_rpow (by norm_num : (2 : ℝ) ≠ 0),
      Real.zero_rpow (by linarith : (2 : ℝ) - γ ≠ 0)]
    ring
  · rw [← Real.rpow_mul h.le (-(γ / 2)) 2, ← Real.rpow_add h]
    congr 1
    ring

/-- **The squared weight identity of the `(0,1)`-slot.**
On `Iθ`, `(D_θ f · Wt α)² = w(z)² · ((∂_θ f)² · sin(2θ)^{2-γ})`. -/
theorem wt_mixed_sq {α : ℝ} (hα : 0 < α) (hα4 : α ≤ 1 / 4) (f : ℝ → ℝ → ℝ) (z : ℝ)
    {θ : ℝ} (hθ : θ ∈ Iθ) :
    (Work.Spaces.mixed 0 1 f z θ * Work.Spaces.Wt α z θ) ^ 2
      = (Work.Spaces.w z) ^ 2 * ((Work.Spaces.pth f z θ) ^ 2
          * (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α)) := by
  have hs : 0 ≤ Real.sin (2 * θ) := sin_two_nonneg_Iθ' hθ
  have hγ0 : 0 < Work.Spaces.gam α := by rw [Work.Spaces.gam]; linarith
  have hγ2 : Work.Spaces.gam α < 2 := by rw [Work.Spaces.gam]; linarith
  have key := sq_mul_sq_rpow_neg (s := Real.sin (2 * θ)) hs hγ0 hγ2
  show (Real.sin (2 * θ) * Work.Spaces.pth f z θ
      * (Work.Spaces.w z * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α / 2)))) ^ 2
      = (Work.Spaces.w z) ^ 2 * ((Work.Spaces.pth f z θ) ^ 2
          * (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α))
  linear_combination (Work.Spaces.pth f z θ ^ 2 * (Work.Spaces.w z) ^ 2) * key

/-- `Wt α z ·` is measurable. -/
theorem measurable_Wt (α z : ℝ) : Measurable (fun θ : ℝ => Work.Spaces.Wt α z θ) := by
  rw [show (fun θ : ℝ => Work.Spaces.Wt α z θ)
      = fun θ => Work.Spaces.w z * ((Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α / 2)))
      from rfl]
  exact measurable_const.mul
    ((Real.continuous_sin.measurable.comp (measurable_const.mul measurable_id)).pow_const _)

/-- A.e. strong measurability of the `(0,1)`-summand of `HkIntegrand`. -/
theorem aesm_mixed01_sq (α : ℝ) (f : ℝ → ℝ → ℝ) (z : ℝ) :
    AEStronglyMeasurable
      (fun θ : ℝ => (Work.Spaces.mixed 0 1 f z θ * Work.Spaces.Wt α z θ) ^ 2)
      (MeasureTheory.volume.restrict Iθ) := by
  have hsin : Measurable (fun θ : ℝ => Real.sin (2 * θ)) :=
    Real.continuous_sin.measurable.comp (measurable_const.mul measurable_id)
  rw [show (fun θ : ℝ => (Work.Spaces.mixed 0 1 f z θ * Work.Spaces.Wt α z θ) ^ 2)
      = fun θ => (Real.sin (2 * θ) * Work.Spaces.pth f z θ * Work.Spaces.Wt α z θ) ^ 2
      from rfl]
  exact ((((hsin.mul (measurable_deriv _)).mul (measurable_Wt α z)).pow_const 2)).aestronglyMeasurable

/-- **The `(0,1)`-slot extractor.**  From the honesty of the full `ℋ²`-integrand of `f` on every
angular slice one gets, for every `z > 0`, the integrability of the single `(0,1)`-summand
`θ ↦ (∂_θ f(z,θ))² · sin(2θ)^{2-γ}` of the `ℋ²`-norm of `f`. -/
theorem integrableOn_pth_mixed01 {α : ℝ} (hα : 0 < α) (hα4 : α ≤ 1 / 4) {f : ℝ → ℝ → ℝ}
    (hmem : Work.Spaces.HkMem α 2 f) {z : ℝ} (hz : 0 < z) :
    MeasureTheory.IntegrableOn (fun θ => (Work.Spaces.pth f z θ) ^ 2
        * (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α)) Iθ := by
  have hzI : z ∈ Work.Spaces.Iz := le_of_lt hz
  have hsum : MeasureTheory.IntegrableOn
      (fun θ => (Work.Spaces.mixed 0 1 f z θ * Work.Spaces.Wt α z θ) ^ 2) Iθ := by
    refine Integrable.mono' (hmem.1 z hzI) (aesm_mixed01_sq α f z) ?_
    filter_upwards with θ
    rw [Real.norm_of_nonneg (sq_nonneg _)]
    exact Work.Spaces.sq_le_HkIntegrand_mixed α 2 f z θ 1 0 (by norm_num) (by norm_num)
  have hw : ((Work.Spaces.w z) ^ 2) ≠ 0 := by
    rw [Work.Spaces.w]; positivity
  refine (hsum.const_mul (((Work.Spaces.w z) ^ 2)⁻¹)).congr ?_
  filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Icc] with θ hθ
  rw [wt_mixed_sq hα hα4 f z hθ, inv_mul_cancel_left₀ hw]

end

end Work.H2W
end
-- ===== merged: Submission.Work.Spaces.MixedSqPointwiseBound =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.Spaces

set_option autoImplicit false
set_option maxHeartbeats 1000000

/-- `D_θ g = sin(2θ) ∂_θ g` vanishes on both angular boundaries, because `sin(2θ)`
does.  Hence `VanishTheta` is preserved by any *positive* iterate of `D_θ` regardless of
the behaviour of `g`. -/
private theorem Dth_vanish (g : ℝ → ℝ → ℝ) : VanishTheta (Dth g) := by
  constructor
  · intro z
    show Real.sin (2 * 0) * pth g z 0 = 0
    simp
  · intro z
    show Real.sin (2 * (π / 2)) * pth g z (π / 2) = 0
    rw [show 2 * (π / 2) = π by ring, Real.sin_pi, zero_mul]

/-- Any positive iterate of `D_θ` vanishes on the two angular boundaries. -/
private theorem DthIter_vanish_of_pos (f : ℝ → ℝ → ℝ) {a : ℕ} (ha : 1 ≤ a) :
    VanishTheta (DthIter a f) := by
  obtain ⟨a', rfl⟩ : ∃ a', a = a' + 1 := ⟨a - 1, by omega⟩
  rw [DthIter_succ]
  exact Dth_vanish (DthIter a' f)



end Work.Spaces
end
end
-- ===== merged: Submission.Work.Spaces.Slots.lintegral_DzIter_le_HkSq_smooth =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology ENNReal
open MeasureTheory Set Filter

namespace Work.Spaces.Slots

set_option autoImplicit false

/-- The open quadrant `(0,∞) × (0,π/2)`. -/
def Qd : Set (ℝ × ℝ) := Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (0 : ℝ) (π / 2)

theorem Qd_subset_nbhU : Qd ⊆ Work.Spaces.nbhU := by
  intro p hp
  obtain ⟨hz, hθ⟩ := hp
  rw [Set.mem_Ioi] at hz
  rw [Set.mem_Ioo] at hθ
  simp only [Work.Spaces.nbhU, Set.mem_prod, Set.mem_Ioi, Set.mem_Ioo]
  exact ⟨by linarith, by linarith, by linarith [Real.pi_pos]⟩

theorem Iθ_subset_Ioo : Work.Spaces.Iθ ⊆ Set.Ioo (-1) (π / 2 + 1) := by
  intro θ hθ
  rw [Work.Spaces.Iθ, Set.mem_Icc] at hθ
  exact ⟨by linarith [hθ.1], by linarith [hθ.2, Real.pi_pos]⟩


/-- A.e. statement for the restricted measure on `Iθ`: it suffices to prove the statement on
the open interval, where the angular weight `sin(2θ)` does not vanish. -/
theorem ae_restrict_Iθ_of_Ioo {p : ℝ → Prop} (h : ∀ θ, 0 < θ → θ < π / 2 → p θ) :
    ∀ᵐ θ ∂(volume.restrict Work.Spaces.Iθ), p θ := by
  rw [Work.Spaces.Iθ, ← MeasureTheory.Measure.restrict_congr_set
    (MeasureTheory.Ioo_ae_eq_Icc (μ := volume) (a := (0 : ℝ)) (b := π / 2))]
  exact MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioo
    (fun θ hθ => h θ hθ.1 hθ.2)

/-- `sin(2θ)^{-η} ≥ 1` for `θ` in the open interval. -/
theorem one_le_sin_two_rpow_neg_eta {θ : ℝ} (h0 : 0 < θ) (h1 : θ < π / 2) :
    (1 : ℝ) ≤ (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) := by
  have hsin : 0 < Real.sin (2 * θ) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [Real.pi_pos])
  have hle : Real.sin (2 * θ) ≤ 1 := Real.sin_le_one _
  have := Real.rpow_le_rpow_of_nonpos hsin hle
    (by linarith [Work.Spaces.eta_pos] : -(Work.Spaces.eta) ≤ 0)
  rwa [Real.one_rpow] at this


end Work.Spaces.Slots
end
end
-- ===== merged: Submission.Work.Spaces.SmoothCompact_HkMem =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.Spaces

set_option autoImplicit false

theorem null_pair : (volume : Measure ℝ) ({0, π / 2} : Set ℝ) = 0 :=
  Set.Finite.measure_zero (Set.toFinite _) volume


theorem Iθ_ae_eq_Ioo : Iθ =ᵐ[(volume : Measure ℝ)] Set.Ioo 0 (π / 2) := by
  rw [MeasureTheory.ae_eq_set]
  constructor
  · have hsub : Iθ \ Set.Ioo 0 (π / 2) ⊆ ({0, π / 2} : Set ℝ) := by
      intro x hx
      rw [Set.mem_diff, Iθ, Set.mem_Icc, Set.mem_Ioo] at hx
      obtain ⟨⟨hx1, hx2⟩, hx3⟩ := hx
      have hcase : x = 0 ∨ x = π / 2 := by
        by_cases h : 0 < x
        · by_cases h' : x < π / 2
          · exact absurd ⟨h, h'⟩ hx3
          · exact Or.inr (le_antisymm hx2 (not_lt.mp h'))
        · exact Or.inl (le_antisymm (not_lt.mp h) hx1)
      rcases hcase with h | h
      · rw [Set.mem_insert_iff]; exact Or.inl h
      · rw [Set.mem_insert_iff]; exact Or.inr (Set.mem_singleton_iff.mpr h)
    exact measure_mono_null hsub null_pair
  · have hsub : Set.Ioo 0 (π / 2) \ Iθ ⊆ (∅ : Set ℝ) := by
      intro x hx
      rw [Set.mem_diff, Set.mem_Ioo, Iθ, Set.mem_Icc] at hx
      exact absurd ⟨le_of_lt hx.1.1, le_of_lt hx.1.2⟩ hx.2
    exact measure_mono_null hsub (by simp)


/-- Continuity of the uncurried integrand on the open box. -/
theorem continuousOn_uncurry_HkIntegrand (α : ℝ) (k : ℕ) (f : ℝ → ℝ → ℝ) (R : ℝ)
    (hsm : SmoothNbhd f) :
    ContinuousOn (Function.uncurry (HkIntegrand α k f)) (Set.Ioo 0 R ×ˢ Set.Ioo 0 (π / 2)) := by
  have hfun : Function.uncurry (HkIntegrand α k f)
      = fun p : ℝ × ℝ =>
          (∑ i ∈ Finset.range (k + 1),
              (DzIter i f p.1 p.2 * (w p.1 / (Real.sin (2 * p.2)) ^ (eta / 2))) ^ 2)
            + ∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1),
                if 1 ≤ i ∧ i + j ≤ k
                then (mixed j i f p.1 p.2 * Wt α p.1 p.2) ^ 2 else 0 := by
    funext p
    rfl
  rw [hfun]
  set box := Set.Ioo 0 R ×ˢ Set.Ioo 0 (π / 2) with hbox
  have hsinpos : ∀ p ∈ box, 0 < Real.sin (2 * p.2) := fun p hp =>
    Real.sin_pos_of_pos_of_lt_pi (by linarith [hp.2.1]) (by linarith [hp.2.2])
  have hcont : ∀ G : ℝ → ℝ → ℝ, ContDiffOn ℝ ⊤ (Function.uncurry G) U →
      ContinuousOn (Function.uncurry G) box := fun G hG =>
    hG.continuousOn.mono fun p hp =>
      mem_U (by linarith [hp.1.1]) (by linarith [hp.2.1]) (by linarith [hp.2.2])
  have hw : ContinuousOn (fun p : ℝ × ℝ => w p.1) box := by
    rw [show (fun p : ℝ × ℝ => w p.1) = fun p => (1 + p.1) ^ 2 / p.1 ^ 2 from rfl]
    refine ContinuousOn.div ((continuousOn_const.add continuousOn_fst).pow 2)
      (continuousOn_fst.pow 2) fun p hp => pow_ne_zero 2 (ne_of_gt hp.1.1)
  have hsinC : ContinuousOn (fun p : ℝ × ℝ => Real.sin (2 * p.2)) box := by
    fun_prop
  have hsin : ContinuousOn (fun p : ℝ × ℝ => (Real.sin (2 * p.2)) ^ (eta / 2)) box :=
    ContinuousOn.rpow_const hsinC fun p hp => Or.inl (ne_of_gt (hsinpos p hp))
  have hsin' : ContinuousOn (fun p : ℝ × ℝ => (Real.sin (2 * p.2)) ^ (-(gam α / 2))) box :=
    ContinuousOn.rpow_const hsinC fun p hp => Or.inl (ne_of_gt (hsinpos p hp))
  have hzterm : ∀ i : ℕ, ContinuousOn (fun p : ℝ × ℝ =>
      (DzIter i f p.1 p.2 * (w p.1 / (Real.sin (2 * p.2)) ^ (eta / 2))) ^ 2) box := by
    intro i
    refine (((hcont _ (smoothNbhd_DzIter hsm i)).mul ?_).pow 2)
    exact hw.div hsin fun p hp => ne_of_gt (Real.rpow_pos_of_pos (hsinpos p hp) _)
  have hmterm : ∀ j i : ℕ, ContinuousOn (fun p : ℝ × ℝ =>
      (mixed j i f p.1 p.2 * Wt α p.1 p.2) ^ 2) box := by
    intro j i
    refine (((hcont _ (smoothNbhd_mixed hsm j i)).mul ?_).pow 2)
    rw [show (fun p : ℝ × ℝ => Wt α p.1 p.2)
      = fun p => w p.1 * (Real.sin (2 * p.2)) ^ (-(gam α / 2)) from rfl]
    exact hw.mul hsin'
  refine ContinuousOn.add ?_ ?_
  · exact continuousOn_finsetSum _ fun i _ => hzterm i
  · refine continuousOn_finsetSum _ fun i _ => ?_
    refine continuousOn_finsetSum _ fun j _ => ?_
    by_cases hc : 1 ≤ i ∧ i + j ≤ k
    · have hiff : (fun p : ℝ × ℝ =>
          if 1 ≤ i ∧ i + j ≤ k then (mixed j i f p.1 p.2 * Wt α p.1 p.2) ^ 2 else 0)
          = fun p : ℝ × ℝ => (mixed j i f p.1 p.2 * Wt α p.1 p.2) ^ 2 := by
        funext p
        exact if_pos hc
      rw [hiff]
      exact hmterm j i
    · have hiff : (fun p : ℝ × ℝ =>
          if 1 ≤ i ∧ i + j ≤ k then (mixed j i f p.1 p.2 * Wt α p.1 p.2) ^ 2 else 0)
          = fun _ : ℝ × ℝ => (0 : ℝ) := by
        funext p
        exact if_neg hc
      rw [hiff]
      exact continuousOn_const



end Work.Spaces
end
end
