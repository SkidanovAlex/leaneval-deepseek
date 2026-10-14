import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.FDeriv.Measurable
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.Order.Interval.Basic
import Mathlib.Tactic.Have
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Mathlib.Topology.MetricSpace.Pseudo.Defs
import Mathlib.Topology.Metrizable.Uniformity
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Sequences
import Mathlib.Topology.UniformSpace.UniformConvergence
import Submission.Work.Coercivity.L2CoercivityTransportEta
import Submission.Work.FTS.ClassCHon.CmodeDefs
import Submission.Work.FTS.EllipticEst.HarOp_pointwise_sq
import Submission.Work.FTS.EllipticEst.OpenFTC.absFtcLeIntegralAbsDeriv
import Submission.Work.FTS.EllipticEst.integrableOn_HkIntegrand_terms
import Submission.Work.FTS.EllipticEst.remov.slice_gprime_ident
import Submission.Work.FTS.H2.hard_sq_prod_z
import Submission.Work.FTS.PhiStar.Series.Weil.integrableOn_prod_mul
import Submission.Work.Spaces.factor_bound
import Submission.Work.Spaces.mixed_mul_le
import Submission.Work.Spaces.pz_DthIter_mul_eq
import Submission.Work.Spaces.sin_two_rpow
import Submission.Work.Spaces.sq_mul_div_rpow
import Submission.Work.Stability.CutFactorFderivZero
import Submission.Work.Stability.Cutoff
import Submission.Work.Stability.OmegaCutSupport
import Submission.Work.StabilityFar.Profile.exists_Fstar_add_ge
-- ===== merged: Submission.Work.ConstructionInstance.Defs =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open FiniteTimeSingularity Set Gradient Matrix Filter Topology MeasureTheory
open scoped Topology Matrix NNReal ENNReal

namespace Work.ConstructionInstance

/-- `ℝ³` (definitionally `Work.Cyl.R3`, `Work.LWP.R3` and `Work.SolutionDelivery.R3`). -/
abbrev R3 : Type := EuclideanSpace ℝ (Fin 3)

/-! ## The two exponents -/

/-- The **profile exponent** attached to the interface's Hölder exponent `α`: `p = 3α`.

The construction is invoked with this exponent, so that the angular factor is
`Γ(θ) = (sinθcos²θ)^α` and the physical vorticity is `α`-Hölder (rather than `α/3`-Hölder, which
is what invoking the construction at `p = α` would give). -/
def profExp (α : NNReal) : ℝ := 3 * (α : ℝ)

theorem profExp_pos {α : NNReal} (hα : 0 < (α : ℝ)) : 0 < profExp α := by
  rw [profExp]; linarith

theorem profExp_div_three (α : NNReal) : profExp α / 3 = (α : ℝ) := by
  rw [profExp]; ring

theorem profExp_nonneg (α : NNReal) : 0 ≤ profExp α := by
  rw [profExp]; positivity

/-! ## The angular factor

`Γ(θ) = (sinθ·cos²θ)^β`.  For `β = α` this is the paper's `Γ` (with the interface's exponent);
it vanishes at both ends of the angular interval and is the source of the vorticity's vanishing
on the axis `r = 0` and on the plane `x₃ = 0`.  Note that `Γ` is only used on `θ ∈ [0,π/2]`,
where its base `sinθ·cos²θ` is in `[0,1]`; the definition is total (Lean's `Real.rpow`) and the
odd extension of the profile takes care of `θ < 0`. -/

/-- The angular factor `Γ(θ) = (sinθ·cos²θ)^β`. -/
def Gamma (β θ : ℝ) : ℝ := (Real.sin θ * Real.cos θ ^ 2) ^ β

/-- `Γ(p/3)` is `Work.Spaces.Gam p`, definitionally. -/
theorem Gamma_div_three (p θ : ℝ) : Gamma (p / 3) θ = Work.Spaces.Gam p θ := rfl

theorem Gamma_nonneg {β θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) : 0 ≤ Gamma β θ :=
  Real.rpow_nonneg (by
    have h1 : 0 ≤ Real.sin θ := Real.sin_nonneg_of_nonneg_of_le_pi hθ.1 (by linarith [hθ.2, Real.pi_pos])
    positivity) _

theorem Gamma_le_one {β θ : ℝ} (hβ : 0 ≤ β) (hθ : θ ∈ Work.Spaces.Iθ) : Gamma β θ ≤ 1 :=
  Real.rpow_le_one (by
    have h1 : 0 ≤ Real.sin θ := Real.sin_nonneg_of_nonneg_of_le_pi hθ.1 (by linarith [hθ.2, Real.pi_pos])
    positivity)
    (by
      have h1 : Real.sin θ ≤ 1 := Real.sin_le_one θ
      have h2 : Real.cos θ ^ 2 ≤ 1 := by
        nlinarith [Real.cos_sq_le_one θ, sq_nonneg (Real.cos θ)]
      nlinarith) hβ

/-- `F_*(z,0) = 0` (for `p ≠ 0`): `Γ(0) = 0`. -/
theorem Fstar_zero_theta {p : ℝ} (hp : p ≠ 0) (z : ℝ) : Work.Construction.Fstar p z 0 = 0 := by
  rw [Work.Construction.Fstar, Work.Spaces.Gam, show Real.sin 0 * Real.cos 0 ^ 2 = 0 by simp,
    Real.zero_rpow (by positivity : p / 3 ≠ 0), zero_div]
  ring

/-- **The bound `|F_*(z,θ)| ≤ 20·p·Γ(θ)`** for `0 < p ≤ 1`, `z ≥ 0`, `θ ∈ [0,π/2]`, from
`c(p) ≥ 1/10` (`Work.Spaces.c_bounds`) and `2z/(1+z)² ≤ 1/2`. -/
theorem Fstar_abs_le {p : ℝ} (hp : 0 < p) (hp1 : p ≤ 1) {z : ℝ} (hz : 0 ≤ z)
    {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) :
    |Work.Construction.Fstar p z θ| ≤ 20 * p * Gamma (p / 3) θ := by
  have hc := (Work.Spaces.c_bounds p hp hp1).1
  have hcpos : 0 < Work.Spaces.c p := by linarith
  have hGam0 : 0 ≤ Work.Spaces.Gam p θ := Gamma_nonneg hθ
  have hGam1 : Work.Spaces.Gam p θ ≤ 1 := by
    rw [← Gamma_div_three]; exact Gamma_le_one (by positivity) hθ
  have hF0 : 0 ≤ Work.FM.Fstar z := by rw [Work.FM.Fstar]; positivity
  have hF1 : Work.FM.Fstar z ≤ 1 / 2 := by
    rw [Work.FM.Fstar, div_le_iff₀ (by positivity : (0:ℝ) < (1 + z) ^ 2)]
    nlinarith [sq_nonneg (1 - z)]
  have hpos : 0 ≤ Work.Construction.Fstar p z θ := by
    rw [Work.Construction.Fstar]
    exact mul_nonneg (mul_nonneg hp.le (div_nonneg hGam0 hcpos.le)) hF0
  rw [abs_of_nonneg hpos, Work.Construction.Fstar, ← Gamma_div_three]
  have h1 : Work.Spaces.Gam p θ / Work.Spaces.c p ≤ 10 * Gamma (p / 3) θ := by
    rw [Gamma_div_three, div_le_iff₀ hcpos]
    nlinarith [hc, hGam0]
  calc p * (Work.Spaces.Gam p θ / Work.Spaces.c p) * Work.FM.Fstar z
      ≤ p * (10 * Gamma (p / 3) θ) * (1 / 2) := by
        apply mul_le_mul
        · exact mul_le_mul_of_nonneg_left h1 hp.le
        · exact hF1
        · exact hF0
        · exact mul_nonneg hp.le (mul_nonneg (by norm_num) (Gamma_nonneg hθ))
    _ = 5 * p * Gamma (p / 3) θ := by ring
    _ ≤ 20 * p * Gamma (p / 3) θ := by
        have hG : 0 ≤ Gamma (p / 3) θ := Gamma_nonneg hθ
        nlinarith [hp.le, hG]

/-! ## The profile and the self-similar vorticity -/

/-- **The profile `F = F_* + g` extended oddly in `θ`.**

`Work.Construction.Fstar` is evaluated by Lean's total `Real.rpow`, whose values for `θ < 0` are
not the physically relevant ones; the odd extension is therefore written out explicitly.  The
physically relevant branch is `0 ≤ θ ≤ π/2`. -/
def profile (p : ℝ) (g : ℝ → ℝ → ℝ) (z θ : ℝ) : ℝ :=
  if 0 ≤ θ then Work.Construction.Fstar p z θ + g z θ
  else -(Work.Construction.Fstar p z (-θ) + g z (-θ))

theorem profile_of_nonneg {p : ℝ} {g : ℝ → ℝ → ℝ} {z θ : ℝ} (h : 0 ≤ θ) :
    profile p g z θ = Work.Construction.Fstar p z θ + g z θ := ite_eq_left h

theorem profile_of_neg {p : ℝ} {g : ℝ → ℝ → ℝ} {z θ : ℝ} (h : ¬ 0 ≤ θ) :
    profile p g z θ = -(Work.Construction.Fstar p z (-θ) + g z (-θ)) := ite_eq_right h

theorem profile_zero {p : ℝ} (hp : p ≠ 0) {g : ℝ → ℝ → ℝ} (hg : ∀ z : ℝ, g z 0 = 0) (z : ℝ) :
    profile p g z 0 = 0 := by
  rw [profile_of_nonneg le_rfl, hg z, Fstar_zero_theta hp, add_zero]

/-- **The profile is odd in `θ`** whenever `g` vanishes on `θ = 0` (which is
`Work.Spaces.VanishTheta` for the modulation) and `p ≠ 0` (so that `F_*(z,0) = Γ(0)·… = 0`). -/
theorem profile_odd {p : ℝ} (hp : p ≠ 0) {g : ℝ → ℝ → ℝ} (hg : ∀ z : ℝ, g z 0 = 0)
    (z θ : ℝ) : profile p g z (-θ) = - profile p g z θ := by
  by_cases h : 0 ≤ θ
  · by_cases h' : 0 ≤ -θ
    · have hθ0 : θ = 0 := le_antisymm (by linarith) h
      rw [hθ0, neg_zero, profile_zero hp hg z, neg_zero]
    · rw [profile_of_neg h', profile_of_nonneg h]; simp
  · have hpos : 0 ≤ -θ := by linarith
    rw [profile_of_neg h, profile_of_nonneg hpos]; simp

/-- **The self-similar vorticity in physical variables** (the paper's `ω^θ` as an `e_θ`-field):

  `omegaS p g x = F(ρ(x)^p, θ(x)) • e_θ(x)`,  `ρ = ‖x‖`, `θ = arctan(x₃/r)`.

On the symmetry axis (`r = 0`) both `e_θ` and the `Γ`-factor of the profile vanish, so the field
is `0` there: the Lean-junk values of `Work.Cyl.theta` (`arctan(0) = 0`) and of
`Work.Cyl.eTheta` (the zero vector) are exactly the right ones. -/
def omegaS (p : ℝ) (g : ℝ → ℝ → ℝ) (x : R3) : R3 :=
  profile p g (Work.Cyl.Rc p x) (Work.Cyl.theta x) • Work.Cyl.eTheta x

/-- **The self-similar vorticity at a prescribed self-similar variable** `z`: the same field with
`F` evaluated at `z` instead of `ρ(x)^p`.  This is the form in which the *time-dependent* ansatz
of `St0`–`St3` reads, `ω(x,t) = λ̄(t)^{-1}·omegaSz p g (ρ(x)^p/λ̄(t)) x` (the rescaling of the
self-similar variable is what makes the vorticity blow up while the profile stays bounded); see
`Boxes.lean`. -/
def omegaSz (p : ℝ) (g : ℝ → ℝ → ℝ) (z : ℝ) (x : R3) : R3 :=
  profile p g z (Work.Cyl.theta x) • Work.Cyl.eTheta x


theorem omegaS_apply' (p : ℝ) (g : ℝ → ℝ → ℝ) (x : R3) :
    omegaS p g x
      = profile p g (Work.Cyl.rho x ^ p) (Work.Cyl.theta x) • Work.Cyl.eTheta x := rfl

theorem omegaSz_apply (p : ℝ) (g : ℝ → ℝ → ℝ) (z : ℝ) (x : R3) :
    omegaSz p g z x = profile p g z (Work.Cyl.theta x) • Work.Cyl.eTheta x := rfl

/-- `omegaS p g` is `omegaSz` at the self-similar variable `z = ρ(x)^p`. -/
theorem omegaS_eq_omegaSz (p : ℝ) (g : ℝ → ℝ → ℝ) (x : R3) :
    omegaS p g x = omegaSz p g (Work.Cyl.rho x ^ p) x := rfl

/-- **The model field** `x ↦ Γ(θ(x))·F_*(ρ(x)^{3β})·e_θ(x)` (`F_*` here the *radial* profile
`z ↦ 2z/(1+z)²` of the fundamental model, `Work.FM.Fstar`): the leading part of `omegaS (3β) g`,
with the angular factor `Γ = (sinθcos²θ)^β` and all constants dropped.  `Holder.lean` proves its
`β`-Hölder regularity, which is the analytic core of the corresponding statement for `omegaS`. -/
def omegaStar (β : ℝ) (x : R3) : R3 :=
  (Gamma β (Work.Cyl.theta x) * Work.FM.Fstar (Work.Cyl.rho x ^ (3 * β))) • Work.Cyl.eTheta x

theorem omegaStar_apply (β : ℝ) (x : R3) :
    omegaStar β x
      = (Gamma β (Work.Cyl.theta x) * Work.FM.Fstar (Work.Cyl.rho x ^ (3 * β)))
        • Work.Cyl.eTheta x := rfl

/-! ## The datum of the construction

`Work.SolutionDelivery.cutDatum L ω = χ(ρ/L) • ω` is the compactly supported `St1` cut-off; the
datum of the constructed solution is its Biot–Savart field. -/

/-- The cut-off datum vorticity of the construction: `χ(ρ/L) • omegaS p g`. -/
abbrev omega₀ (p : ℝ) (g : ℝ → ℝ → ℝ) (L : ℝ) : R3 → R3 :=
  Work.SolutionDelivery.cutDatum L (omegaS p g)

theorem omega₀_apply (p : ℝ) (g : ℝ → ℝ → ℝ) (L : ℝ) (x : R3) :
    omega₀ p g L x = Work.Stability.chi (Work.Cyl.rho x / L) • omegaS p g x := rfl


/-- **The times before the maximal time `T`**, where the self-similar description of the solution
is meaningful: `preWindow T = Ioo (-2) T`.  It is the part of the extended window
`extWindow T = Ioo (-2) (T+2)` on which the modulation `λ̄` is positive — see
`not_lam_pos_extWindow` for why the remaining times `[T, T+2)` cannot support the fields below:
the combination `λ̄ > 0` at `T`, `λ̄` differentiable at `T` and `λ̄(t) ≤ 2(T-t)` for `t ∈ [0,T)`
is empty. -/
abbrev preWindow (T : ℝ) : Set ℝ := Set.Ioo (-2) T


end Work.ConstructionInstance
end
end
-- ===== merged: Submission.Work.FTS.Apriori.Coord =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.Apriori

open Work.FTS.Galerkin (Fam slice ConvLocUnif Slab)

set_option autoImplicit false


end Work.FTS.Apriori
end
end
-- ===== merged: Submission.Work.FTS.ClassCHon.Lop_good =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Topology

namespace Work.FTS.ClassCHon

/-- A function which is eventually `0` at `θ` has derivative `0` there. -/
private lemma deriv_eq_zero_of_eventuallyEq_zero {u : ℝ → ℝ} {θ : ℝ} (hu : u =ᶠ[𝓝 θ] 0) :
    deriv u θ = 0 := by
  rw [Filter.EventuallyEq.deriv_eq hu]
  simp

/-- `Lzero1 u` vanishes away from the support of `u`: at a point `θ ∉ [a,b]` the function
`u` — and hence `deriv u` and `θ' ↦ tan θ' * u θ'` — is eventually zero. -/
lemma Lzero1_eq_zero_of_not_mem {u : ℝ → ℝ} {a b : ℝ}
    (hu : ∀ θ : ℝ, θ ∉ Set.Icc a b → u θ = 0) {θ : ℝ} (hθ : θ ∉ Set.Icc a b) :
    Work.FTS.EllipticEst.Lzero1 u θ = 0 := by
  have hopen : (Set.Icc a b)ᶜ ∈ 𝓝 θ :=
    IsOpen.mem_nhds isClosed_Icc.isOpen_compl hθ
  have hdu : deriv u =ᶠ[𝓝 θ] 0 := by
    filter_upwards [hopen] with t ht
    refine deriv_eq_zero_of_eventuallyEq_zero ?_
    filter_upwards [IsOpen.mem_nhds isClosed_Icc.isOpen_compl ht] with s hs using hu s hs
  have htanu : (fun t : ℝ => Real.tan t * u t) =ᶠ[𝓝 θ] 0 := by
    filter_upwards [hopen] with t ht
    simp [hu t ht]
  simp only [Work.FTS.EllipticEst.Lzero1]
  rw [deriv_eq_zero_of_eventuallyEq_zero hdu, deriv_eq_zero_of_eventuallyEq_zero htanu,
    hu θ hθ]
  ring

/-- If `u` is `C^∞` and supported in `[a,b]` with `0 < a`, `b < π/2`, then
`θ ↦ tan θ * u θ` is `C^∞`: on `[a,b]` (which lies inside `(-π/2, π/2)`) the tangent is
smooth, and off `[a,b]` the product vanishes in a neighbourhood. -/
lemma contDiff_tan_mul_of_support {u : ℝ → ℝ} {a b : ℝ} (ha : 0 < a)
    (hb : b < Real.pi / 2) (hu : ContDiff ℝ Work.Stability.smoothOrder u)
    (hsup : ∀ θ : ℝ, θ ∉ Set.Icc a b → u θ = 0) :
    ContDiff ℝ Work.Stability.smoothOrder (fun θ : ℝ => Real.tan θ * u θ) := by
  rw [contDiff_iff_contDiffAt]
  intro θ
  by_cases hθ : θ ∈ Set.Icc a b
  · have hpos : 0 < θ := lt_of_lt_of_le ha hθ.1
    have hlt : θ < Real.pi / 2 := lt_of_le_of_lt hθ.2 hb
    have hcos : Real.cos θ ≠ 0 := by
      refine ne_of_gt (Real.cos_pos_of_mem_Ioo ⟨?_, hlt⟩)
      linarith [Real.pi_pos, hpos]
    exact (Real.contDiffAt_tan.2 hcos).mul ((contDiff_iff_contDiffAt.mp hu) θ)
  · have hnhds : (Set.Icc a b)ᶜ ∈ 𝓝 θ := IsOpen.mem_nhds isClosed_Icc.isOpen_compl hθ
    refine ContDiffAt.congr_of_eventuallyEq (contDiffAt_const (c := (0 : ℝ))) ?_
    filter_upwards [hnhds] with t ht
    simp [hsup t ht]

/-- `Lzero1` preserves the class `Good a b` (for `0 < a`, `b < π/2`). -/
lemma good_Lzero1 {g : ℝ → ℝ} {a b : ℝ} (ha : 0 < a) (hb : b < Real.pi / 2)
    (hg : Work.FTS.ClassCHon.Good a b g) :
    Work.FTS.ClassCHon.Good a b (Work.FTS.EllipticEst.Lzero1 g) := by
  refine ⟨?_, fun θ hθ => Lzero1_eq_zero_of_not_mem hg.2 hθ⟩
  have hu := hg.1
  have hdu : ContDiff ℝ Work.Stability.smoothOrder (deriv g) :=
    (contDiff_infty_iff_deriv.mp hu).2
  have hddu : ContDiff ℝ Work.Stability.smoothOrder (deriv (deriv g)) :=
    (contDiff_infty_iff_deriv.mp hdu).2
  have hw : ContDiff ℝ Work.Stability.smoothOrder (fun θ : ℝ => Real.tan θ * g θ) :=
    contDiff_tan_mul_of_support ha hb hu hg.2
  have hdw : ContDiff ℝ Work.Stability.smoothOrder
      (deriv (fun θ : ℝ => Real.tan θ * g θ)) :=
    (contDiff_infty_iff_deriv.mp hw).2
  have hsum : ContDiff ℝ Work.Stability.smoothOrder
      (fun θ : ℝ => -(deriv (deriv g) θ) + deriv (fun t : ℝ => Real.tan t * g t) θ
        - 6 * g θ) :=
    (hddu.neg.add hdw).sub (contDiff_const.mul hu)
  exact hsum

theorem Lop_good {g : ℝ → ℝ} {a b : ℝ} (ha : 0 < a) (hb : b < Real.pi / 2)
    (hg : Work.FTS.ClassCHon.Good a b g) :
    ∀ k : ℕ, Work.FTS.ClassCHon.Good a b (Work.FTS.ClassCHon.Lop g k) := by
  intro k
  induction k with
  | zero => simpa using hg
  | succ k ih =>
      rw [Work.FTS.ClassCHon.Lop_succ]
      exact good_Lzero1 ha hb ih

end Work.FTS.ClassCHon
end
end
-- ===== merged: Submission.Work.FTS.CoercivityFix.Coer1T.gPsi_eta_abs_le_Q =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.CoercivityFix.Coer1T

set_option autoImplicit false
set_option maxHeartbeats 2000000

/-!
# The projector-correction pairing `⟨T4fun α f, f⟩_{w² sin^{-η}}` in the interior class

`T4fun α f = (Γ(θ)/c)·(2z²/(1+z)³)·C₀(f)`, where `C₀(f) = L₁₂(Transport f)(0)` is a *constant*.
Hence the pairing `wip (w² sin^{-η}) (T4fun α f) f` is `C₀(f)` times the pairing of the fixed
function `(Γ/c)(2z²/(1+z)³)` against `f`, and Cauchy–Schwarz in `L²(dz dθ)` bounds the latter by
`√(∫∫(Γ/c)²(2z²/(1+z)³)²w² sin^{-η})·√(EfEta f)`.  The first factor is
`√(4·∫_θ (Γ/c)² sin^{-η}) ≤ √(4·12100) = 220`, using `(2z²/(1+z)³)²w(z)² = 4/(1+z)²`
(so `∫_z · = 4`) and `Work.Coercivity.Gam_div_c_sq_eta_integral_le_12100`.

The file `Submission/Work/Coercivity/L2CoercivityTransportEta.lean` proves this for the
*analytic* class `IBP`/`CoerciveData` (`Work.Coercivity.gPsi_eta_abs_le`).  The present file
repeats the proof for the **interior** class of the route: the only two ingredients really used
are the joint integrability `hF` of `f² w² sin^{-η}` and the a.e. strong measurability of `f`,
which is supplied here by `SmoothQuad`.
-/


/-- The joint integrability of `(Γ/c)(2z²/(1+z)³)·f·w²·sin(2θ)^{-η}` from the joint
integrability of `f² w² sin(2θ)^{-η}`: the pointwise bound `2|ab| ≤ a² + b²` with
`a = (Γ/c)(2z²/(1+z)³)w sin(2θ)^{-η/2}` reduces it to the separated product
`a(z,θ)² = [(Γ/c)² sin^{-η}]·[(2z²/(1+z)³)² w²]` (integrable: `∫_θ (Γ/c)² sin^{-η} < ∞` and
`∫_z (2z²/(1+z)³)² w² = ∫_z 4/(1+z)² = 4`) plus the given `f² w² sin^{-η}`. -/
theorem etaW_gPsi_integrable_Q (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) (f : ℝ → ℝ → ℝ)
    (haesm : MeasureTheory.AEStronglyMeasurable (fun p : ℝ × ℝ => f p.1 p.2)
      (MeasureTheory.volume.restrict (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ)))
    (hF : MeasureTheory.IntegrableOn
      (Function.uncurry (fun z θ => f z θ * f z θ * Work.Spaces.w z ^ 2
        * (Real.sin (2 * θ)) ^ (-Work.Spaces.eta))) (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ)) :
    MeasureTheory.IntegrableOn
      (Function.uncurry (fun z θ => (Work.Spaces.Gam α θ / Work.Spaces.c α)
        * (2 * z ^ 2 / (1 + z) ^ 3) * f z θ
        * Work.Spaces.w z ^ 2 * (Real.sin (2 * θ)) ^ (-Work.Spaces.eta)))
      (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ) := by
  have hmem : ∀ᵐ p ∂(volume.restrict (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ)),
      p ∈ Work.Spaces.Iz ×ˢ Work.Spaces.Iθ :=
    ae_restrict_mem (measurableSet_Ici.prod measurableSet_Icc)
  have hc : (1 : ℝ) / 10 ≤ Work.Spaces.c α := (Work.Spaces.c_bounds α hα hα1).1
  have hEta : MeasureTheory.IntegrableOn
      (fun θ : ℝ => (Real.sin (2 * θ)) ^ (-Work.Spaces.eta)) Work.Spaces.Iθ :=
    (Work.Spaces.sin_two_rpow (-Work.Spaces.eta) (by rw [Work.Spaces.eta]; norm_num)
      (by rw [Work.Spaces.eta]; norm_num)).1
  have hθ2 : MeasureTheory.IntegrableOn
      (fun θ : ℝ => (Work.Spaces.Gam α θ / Work.Spaces.c α) ^ 2
        * (Real.sin (2 * θ)) ^ (-Work.Spaces.eta)) Work.Spaces.Iθ := by
    refine Integrable.mono' (Integrable.const_mul hEta 100) ?_ ?_
    · unfold Work.Spaces.Gam
      fun_prop
    · filter_upwards [ae_restrict_mem measurableSet_Icc] with θ hθ
      have hs0 : 0 ≤ Real.sin (2 * θ) :=
        Real.sin_nonneg_of_nonneg_of_le_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])
      rw [Real.norm_of_nonneg (mul_nonneg (sq_nonneg _) (Real.rpow_nonneg hs0 _))]
      have hG1 : Work.Spaces.Gam α θ ≤ 1 := by
        rw [Work.Spaces.Gam]
        exact Real.rpow_le_one (mul_nonneg (Real.sin_nonneg_of_nonneg_of_le_pi hθ.1
          (by linarith [hθ.2, Real.pi_pos])) (sq_nonneg _))
          (Work.Coercivity.sin_mul_cos_sq_le_one hθ) (le_of_lt (by positivity : (0:ℝ) < α / 3))
      have hG0 : 0 ≤ Work.Spaces.Gam α θ := by
        rw [Work.Spaces.Gam]
        exact Real.rpow_nonneg (mul_nonneg (Real.sin_nonneg_of_nonneg_of_le_pi hθ.1
          (by linarith [hθ.2, Real.pi_pos])) (sq_nonneg _)) _
      have hsq : (Work.Spaces.Gam α θ / Work.Spaces.c α) ^ 2 ≤ 100 := by
        rw [div_pow, div_le_iff₀ (by positivity : (0:ℝ) < (Work.Spaces.c α) ^ 2)]
        have h1 : Work.Spaces.Gam α θ ^ 2 ≤ 1 := by
          have := mul_self_le_mul_self hG0 hG1
          nlinarith [this]
        have h2 : (1:ℝ) ≤ 100 * (Work.Spaces.c α) ^ 2 := by
          have := mul_self_le_mul_self (by norm_num : (0:ℝ) ≤ 1/10) hc
          nlinarith [this]
        linarith
      exact mul_le_mul_of_nonneg_right hsq (Real.rpow_nonneg hs0 _)
  have hz2 : MeasureTheory.IntegrableOn
      (fun z : ℝ => (2 * z ^ 2 / (1 + z) ^ 3) ^ 2 * Work.Spaces.w z ^ 2) Work.Spaces.Iz := by
    refine Integrable.mono' (Integrable.const_mul Work.Coercivity.integrable_Iz_one_div_sq 4) ?_ ?_
    · unfold Work.Spaces.w
      fun_prop
    · filter_upwards [ae_restrict_mem measurableSet_Ici] with z hz
      have hz0 : (0:ℝ) ≤ z := Set.mem_Ici.mp hz
      rw [Real.norm_of_nonneg (mul_nonneg (sq_nonneg _) (sq_nonneg _))]
      rcases eq_or_ne z 0 with h | h
      · rw [h]
        norm_num
      · have hkey : (2 * z ^ 2 / (1 + z) ^ 3) ^ 2 * Work.Spaces.w z ^ 2
            = 4 * (1 / (1 + z) ^ 2) := by
          rw [Work.Spaces.w]
          field_simp
          ring
        rw [hkey]
  have hprod : MeasureTheory.IntegrableOn (fun p : ℝ × ℝ =>
      ((Work.Spaces.Gam α p.2 / Work.Spaces.c α) ^ 2
          * (Real.sin (2 * p.2)) ^ (-Work.Spaces.eta))
        * ((2 * p.1 ^ 2 / (1 + p.1) ^ 3) ^ 2 * Work.Spaces.w p.1 ^ 2))
      (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ) := by
    have h := hz2.mul_prod hθ2
    rw [Work.Coercivity.prod_restrict_eq] at h
    refine h.congr (Filter.Eventually.of_forall fun p => ?_)
    ring
  have hdom : MeasureTheory.IntegrableOn (fun p : ℝ × ℝ =>
      (1 / 2) * (((Work.Spaces.Gam α p.2 / Work.Spaces.c α) ^ 2
          * (Real.sin (2 * p.2)) ^ (-Work.Spaces.eta))
        * ((2 * p.1 ^ 2 / (1 + p.1) ^ 3) ^ 2 * Work.Spaces.w p.1 ^ 2)
        + f p.1 p.2 * f p.1 p.2 * Work.Spaces.w p.1 ^ 2
          * (Real.sin (2 * p.2)) ^ (-Work.Spaces.eta)))
      (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ) := Integrable.const_mul (hprod.add hF) (1 / 2)
  refine Integrable.mono' hdom ?_ ?_
  · have hfac : (Function.uncurry (fun z θ =>
        (Work.Spaces.Gam α θ / Work.Spaces.c α) * (2 * z ^ 2 / (1 + z) ^ 3) * f z θ
          * Work.Spaces.w z ^ 2 * (Real.sin (2 * θ)) ^ (-Work.Spaces.eta)))
        = (fun p : ℝ × ℝ => (Work.Spaces.Gam α p.2 / Work.Spaces.c α)
            * (2 * p.1 ^ 2 / (1 + p.1) ^ 3)
            * (Work.Spaces.w p.1 ^ 2 * (Real.sin (2 * p.2)) ^ (-Work.Spaces.eta)))
          * (fun p : ℝ × ℝ => f p.1 p.2) := by
      funext p
      obtain ⟨z, θ⟩ := p
      simp only [Function.uncurry_apply_pair, Pi.mul_apply]
      ring
    rw [hfac]
    have hw : Measurable (fun p : ℝ × ℝ => (Work.Spaces.Gam α p.2 / Work.Spaces.c α)
        * (2 * p.1 ^ 2 / (1 + p.1) ^ 3) * (Work.Spaces.w p.1 ^ 2
          * (Real.sin (2 * p.2)) ^ (-Work.Spaces.eta))) := by
      unfold Work.Spaces.Gam Work.Spaces.w
      fun_prop
    exact hw.aestronglyMeasurable.mul haesm
  · filter_upwards [hmem] with p hp
    obtain ⟨z, θ⟩ := p
    obtain ⟨hz, hθ⟩ := hp
    simp only [Function.uncurry_apply_pair]
    have hs0 : 0 ≤ Real.sin (2 * θ) :=
      Real.sin_nonneg_of_nonneg_of_le_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])
    have hρ : 0 ≤ Work.Spaces.w z ^ 2 * (Real.sin (2 * θ)) ^ (-Work.Spaces.eta) :=
      mul_nonneg (sq_nonneg _) (Real.rpow_nonneg hs0 _)
    have hkey := Work.Coercivity.gPsi_pointwise
      ((Work.Spaces.Gam α θ / Work.Spaces.c α) * (2 * z ^ 2 / (1 + z) ^ 3)) (f z θ)
    have h2 := mul_le_mul_of_nonneg_right hkey hρ
    rw [Real.norm_eq_abs,
      show (Work.Spaces.Gam α θ / Work.Spaces.c α) * (2 * z ^ 2 / (1 + z) ^ 3) * f z θ
            * Work.Spaces.w z ^ 2 * (Real.sin (2 * θ)) ^ (-Work.Spaces.eta)
          = ((Work.Spaces.Gam α θ / Work.Spaces.c α) * (2 * z ^ 2 / (1 + z) ^ 3) * f z θ)
            * (Work.Spaces.w z ^ 2 * (Real.sin (2 * θ)) ^ (-Work.Spaces.eta)) from by ring,
      abs_mul, abs_of_nonneg hρ]
    refine h2.trans (le_of_eq ?_)
    ring

/-- **The Cauchy–Schwarz bound of the projector pairing in the interior class.**  For `Λ = C₀ f`
this is the bound needed for the `η`-slot of `𝓛_Γ^T`; the general `Λ` makes the statement
usable for a constant factor. -/
theorem wip_gPsi_eta_le_aux (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) (f : ℝ → ℝ → ℝ) (Λ : ℝ)
    (haesm : MeasureTheory.AEStronglyMeasurable (fun p : ℝ × ℝ => f p.1 p.2)
      ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)))
    (hFη : MeasureTheory.IntegrableOn
      (Function.uncurry (fun z θ => f z θ * f z θ * Work.Spaces.w z ^ 2
        * (Real.sin (2 * θ)) ^ (-Work.Spaces.eta))) (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ)) :
    |Work.Coercivity.wip
        (fun z θ => Work.Spaces.w z ^ 2 * (Real.sin (2 * θ)) ^ (-Work.Spaces.eta))
        (fun z θ => (Work.Spaces.Gam α θ / Work.Spaces.c α)
          * (2 * z ^ 2 / (1 + z) ^ 3) * Λ) f|
      ≤ 220 * |Λ| * Real.sqrt (Work.Coercivity.EfEta f) := by
  set P : MeasureTheory.Measure (ℝ × ℝ) :=
    (MeasureTheory.volume.restrict Work.Spaces.Iz).prod
      (MeasureTheory.volume.restrict Work.Spaces.Iθ) with hP
  set A : ℝ × ℝ → ℝ := fun p => (Work.Spaces.Gam α p.2 / Work.Spaces.c α)
      * (2 * p.1 ^ 2 / (1 + p.1) ^ 3)
      * Work.Spaces.w p.1 * (Real.sin (2 * p.2)) ^ (-Work.Spaces.eta / 2) with hA
  set B : ℝ × ℝ → ℝ := fun p => f p.1 p.2 * Work.Spaces.w p.1
      * (Real.sin (2 * p.2)) ^ (-Work.Spaces.eta / 2) with hB
  have hsin0 : ∀ θ ∈ Work.Spaces.Iθ, 0 ≤ Real.sin (2 * θ) := fun θ hθ =>
    Real.sin_nonneg_of_nonneg_of_le_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])
  have haesm' : MeasureTheory.AEStronglyMeasurable (fun p : ℝ × ℝ => f p.1 p.2)
      (MeasureTheory.volume.restrict (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ)) := by
    rw [Work.Coercivity.volume_restrict_prod]; exact haesm
  have hsinesm : AEStronglyMeasurable
      (fun p : ℝ × ℝ => (Real.sin (2 * p.2)) ^ (-Work.Spaces.eta / 2)) P := by
    apply Measurable.aestronglyMeasurable
    fun_prop
  -- ### Step 1: the weighted pairing as a product-measure integral of `Λ * (A * B)`
  have hgint : MeasureTheory.IntegrableOn (Function.uncurry (fun z θ =>
      (Work.Spaces.Gam α θ / Work.Spaces.c α) * (2 * z ^ 2 / (1 + z) ^ 3) * f z θ
        * Work.Spaces.w z ^ 2 * (Real.sin (2 * θ)) ^ (-Work.Spaces.eta)))
      (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ) :=
    etaW_gPsi_integrable_Q α hα hα1 f haesm' hFη
  have hIntOn : MeasureTheory.IntegrableOn (Function.uncurry (fun z θ =>
      (Work.Spaces.Gam α θ / Work.Spaces.c α) * (2 * z ^ 2 / (1 + z) ^ 3) * Λ * f z θ
        * Work.Spaces.w z ^ 2 * (Real.sin (2 * θ)) ^ (-Work.Spaces.eta)))
      (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ) :=
    IntegrableOn.congr_fun (Integrable.const_mul hgint Λ) (fun p hp => by
      obtain ⟨z, θ⟩ := p
      simp only [Function.uncurry_apply_pair]
      ring) (measurableSet_Ici.prod measurableSet_Icc)
  have hIntOn' : MeasureTheory.IntegrableOn (Function.uncurry (fun z θ =>
      ((Work.Spaces.Gam α θ / Work.Spaces.c α) * (2 * z ^ 2 / (1 + z) ^ 3) * Λ) * f z θ
        * (Work.Spaces.w z ^ 2 * (Real.sin (2 * θ)) ^ (-Work.Spaces.eta))))
      (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ) :=
    IntegrableOn.congr_fun hIntOn (fun p hp => by
      obtain ⟨z, θ⟩ := p
      simp only [Function.uncurry_apply_pair]
      ring) (measurableSet_Ici.prod measurableSet_Icc)
  have hwip : Work.Coercivity.wip
      (fun z θ => Work.Spaces.w z ^ 2 * (Real.sin (2 * θ)) ^ (-Work.Spaces.eta))
      (fun z θ => (Work.Spaces.Gam α θ / Work.Spaces.c α) * (2 * z ^ 2 / (1 + z) ^ 3) * Λ) f
      = ∫ p, Λ * (A p * B p) ∂P := by
    rw [Work.Coercivity.wip_eq_integral_prod
      (fun z θ => Work.Spaces.w z ^ 2 * (Real.sin (2 * θ)) ^ (-Work.Spaces.eta))
      (fun z θ => (Work.Spaces.Gam α θ / Work.Spaces.c α) * (2 * z ^ 2 / (1 + z) ^ 3) * Λ) f
      hIntOn', ← hP]
    refine integral_congr_ae ?_
    filter_upwards [Work.Coercivity.ae_prod_quadrant] with p hp
    obtain ⟨z, θ⟩ := p
    obtain ⟨hz, hθ⟩ := hp
    have hs0 := hsin0 θ hθ
    simp only [hA, hB]
    have hss : (Real.sin (2 * θ)) ^ (-Work.Spaces.eta / 2)
        * (Real.sin (2 * θ)) ^ (-Work.Spaces.eta / 2)
        = (Real.sin (2 * θ)) ^ (-Work.Spaces.eta) := by
      rw [← Work.Coercivity.rpow_half_sq _ hs0]; ring
    rw [← hss]
    ring
  -- ### Step 2: a.e. strong measurability of `A` and `B`
  have hAesm : AEStronglyMeasurable A P := by
    rw [hA]
    have h1 : AEStronglyMeasurable (fun p : ℝ × ℝ => (Work.Spaces.Gam α p.2 / Work.Spaces.c α)
        * (2 * p.1 ^ 2 / (1 + p.1) ^ 3) * Work.Spaces.w p.1) P := by
      apply Measurable.aestronglyMeasurable
      unfold Work.Spaces.Gam Work.Spaces.w
      fun_prop
    exact h1.mul hsinesm
  have hBesm : AEStronglyMeasurable B P := by
    rw [hB]
    have hfmw : AEStronglyMeasurable
        (fun p : ℝ × ℝ => f p.1 p.2 * Work.Spaces.w p.1) P := by
      have hwmeas : AEStronglyMeasurable (fun p : ℝ × ℝ => Work.Spaces.w p.1) P := by
        apply Measurable.aestronglyMeasurable
        unfold Work.Spaces.w
        fun_prop
      exact haesm.mul hwmeas
    exact hfmw.mul hsinesm
  -- ### Step 3: square-integrability of `A` and `B`
  have ha : IntegrableOn (fun z : ℝ => (2 * z ^ 2 / (1 + z) ^ 3) ^ 2 * Work.Spaces.w z ^ 2)
      Work.Spaces.Iz := by
    refine Integrable.mono' (Integrable.const_mul Work.Coercivity.integrable_Iz_one_div_sq 4) ?_ ?_
    · unfold Work.Spaces.w
      fun_prop
    · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ici] with z hz
      rw [Real.norm_of_nonneg (mul_nonneg (sq_nonneg _) (sq_nonneg _))]
      rcases eq_or_ne z 0 with h | h
      · rw [h]; norm_num
      · have h1z : (1 : ℝ) + z ≠ 0 := by linarith [Set.mem_Ici.mp hz]
        have hkey : (2 * z ^ 2 / (1 + z) ^ 3) ^ 2 * Work.Spaces.w z ^ 2
            = 4 * (1 / (1 + z) ^ 2) := by
          rw [Work.Spaces.w]; field_simp; ring
        rw [hkey]
  have hb : IntegrableOn (fun θ : ℝ => (Work.Spaces.Gam α θ / Work.Spaces.c α) ^ 2
      * (Real.sin (2 * θ)) ^ (-Work.Spaces.eta)) Work.Spaces.Iθ := by
    refine Integrable.mono' (Integrable.const_mul (Work.Spaces.sin_two_rpow (-Work.Spaces.eta)
      (by linarith [Work.Spaces.eta_lt_one]) (by linarith [Work.Spaces.eta_pos])).1 100) ?_ ?_
    · unfold Work.Spaces.Gam
      fun_prop
    · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Icc] with θ hθ
      have hs0 := hsin0 θ hθ
      rw [Real.norm_of_nonneg (mul_nonneg (sq_nonneg _) (Real.rpow_nonneg hs0 _))]
      have hG : |Work.Spaces.Gam α θ / Work.Spaces.c α| ≤ 10 :=
        Work.Coercivity.Gam_div_c_bound hα hα1 hθ
      have hsq : (Work.Spaces.Gam α θ / Work.Spaces.c α) ^ 2 ≤ 100 := by
        nlinarith [hG, abs_nonneg (Work.Spaces.Gam α θ / Work.Spaces.c α),
          sq_abs (Work.Spaces.Gam α θ / Work.Spaces.c α)]
      exact mul_le_mul_of_nonneg_right hsq (Real.rpow_nonneg hs0 _)
  have hA2 : Integrable (fun p => A p ^ 2) P := by
    rw [hP]
    refine ((ha.mul_prod hb).congr ?_)
    filter_upwards [Work.Coercivity.ae_prod_quadrant] with p hp
    obtain ⟨z, θ⟩ := p
    obtain ⟨hz, hθ⟩ := hp
    have hs0 := hsin0 θ hθ
    simp only [hA]
    rw [mul_pow, mul_pow, mul_pow, Work.Coercivity.rpow_half_sq _ hs0]
    ring
  have hB2 : Integrable (fun p => B p ^ 2) P := by
    rw [hP]
    refine ((Work.Coercivity.integrableOn_prod hFη).congr ?_)
    filter_upwards [Work.Coercivity.ae_prod_quadrant] with p hp
    obtain ⟨z, θ⟩ := p
    obtain ⟨hz, hθ⟩ := hp
    have hs0 := hsin0 θ hθ
    simp only [hB]
    rw [mul_pow, mul_pow, Work.Coercivity.rpow_half_sq _ hs0]
    ring
  -- ### Step 4: the Cauchy–Schwarz bound
  have hCS := Work.Coercivity.sq_integral_mul_le P A B hAesm hBesm hA2 hB2
  have hA2nn : 0 ≤ ∫ p, A p ^ 2 ∂P := integral_nonneg fun p => sq_nonneg _
  have habs : |∫ p, A p * B p ∂P|
      ≤ Real.sqrt (∫ p, A p ^ 2 ∂P) * Real.sqrt (∫ p, B p ^ 2 ∂P) := by
    rw [← Real.sqrt_sq_eq_abs, ← Real.sqrt_mul hA2nn]
    exact Real.sqrt_le_sqrt hCS
  -- ### Step 5: the values of the two square-integrals
  have hzsq : ∫ z in Work.Spaces.Iz, (2 * z ^ 2 / (1 + z) ^ 3) ^ 2 * Work.Spaces.w z ^ 2 = 4 := by
    have hI : (∫ z in Work.Spaces.Iz, (2 * z ^ 2 / (1 + z) ^ 3) ^ 2 * Work.Spaces.w z ^ 2)
        = ∫ z in Set.Ioi (0 : ℝ), (2 * z ^ 2 / (1 + z) ^ 3) ^ 2 * Work.Spaces.w z ^ 2 := by
      rw [show Work.Spaces.Iz = Set.Ici (0 : ℝ) from rfl]
      exact (MeasureTheory.setIntegral_congr_set
        (MeasureTheory.Ioi_ae_eq_Ici (a := (0 : ℝ)))).symm
    rw [hI]
    have hcongr : (fun z : ℝ => (2 * z ^ 2 / (1 + z) ^ 3) ^ 2 * Work.Spaces.w z ^ 2)
        =ᵐ[volume.restrict (Set.Ioi (0 : ℝ))] (fun z => 4 * (1 / (1 + z) ^ 2)) := by
      filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with z hz
      have hz0 : z ≠ 0 := ne_of_gt (Set.mem_Ioi.mp hz)
      have h1z : (1 : ℝ) + z ≠ 0 := by have := Set.mem_Ioi.mp hz; linarith
      have hkey : (2 * z ^ 2 / (1 + z) ^ 3) ^ 2 * Work.Spaces.w z ^ 2
          = 4 * (1 / (1 + z) ^ 2) := by
        rw [Work.Spaces.w]; field_simp; ring
      rw [hkey]
    rw [MeasureTheory.integral_congr_ae hcongr, MeasureTheory.integral_const_mul]
    have h1 : (∫ z in Set.Ioi (0 : ℝ), 1 / (1 + z) ^ 2) = 1 := by
      rw [MeasureTheory.setIntegral_congr_set (MeasureTheory.Ioi_ae_eq_Ici (a := (0 : ℝ)))]
      exact Work.Coercivity.integral_Iz_one_div_sq
    rw [h1]
    norm_num
  have hBval : ∫ p, B p ^ 2 ∂P = Work.Coercivity.EfEta f := by
    have hF : IntegrableOn (Function.uncurry (fun z θ => f z θ * f z θ
        * (Work.Spaces.w z ^ 2 * (Real.sin (2 * θ)) ^ (-Work.Spaces.eta))))
        (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ) :=
      IntegrableOn.congr_fun hFη (fun p hp => by
        obtain ⟨z, θ⟩ := p
        simp only [Function.uncurry_apply_pair]
        ring) (measurableSet_Ici.prod measurableSet_Icc)
    rw [Work.Coercivity.EfEta_eq_wip, Work.Coercivity.wip_eq_integral_prod
      (fun z θ => Work.Spaces.w z ^ 2 * (Real.sin (2 * θ)) ^ (-Work.Spaces.eta)) f f hF, ← hP]
    refine integral_congr_ae ?_
    filter_upwards [Work.Coercivity.ae_prod_quadrant] with p hp
    obtain ⟨z, θ⟩ := p
    obtain ⟨hz, hθ⟩ := hp
    have hs0 := hsin0 θ hθ
    simp only [hB]
    rw [mul_pow, mul_pow, Work.Coercivity.rpow_half_sq _ hs0]
    ring
  have hAval : ∫ p, A p ^ 2 ∂P
      = (∫ z in Work.Spaces.Iz, (2 * z ^ 2 / (1 + z) ^ 3) ^ 2 * Work.Spaces.w z ^ 2)
        * (∫ θ in Work.Spaces.Iθ, (Work.Spaces.Gam α θ / Work.Spaces.c α) ^ 2
          * (Real.sin (2 * θ)) ^ (-Work.Spaces.eta)) := by
    have hcongr : (fun p : ℝ × ℝ => A p ^ 2)
        =ᵐ[P] (fun p : ℝ × ℝ => ((2 * p.1 ^ 2 / (1 + p.1) ^ 3) ^ 2
            * Work.Spaces.w p.1 ^ 2)
          * ((Work.Spaces.Gam α p.2 / Work.Spaces.c α) ^ 2
            * (Real.sin (2 * p.2)) ^ (-Work.Spaces.eta))) := by
      filter_upwards [Work.Coercivity.ae_prod_quadrant] with p hp
      obtain ⟨z, θ⟩ := p
      obtain ⟨hz, hθ⟩ := hp
      have hs0 := hsin0 θ hθ
      simp only [hA]
      rw [mul_pow, mul_pow, mul_pow, Work.Coercivity.rpow_half_sq _ hs0]
      ring
    rw [MeasureTheory.integral_congr_ae hcongr, hP]
    rw [Work.Coercivity.integral_prod_sep
      (a := fun z : ℝ => (2 * z ^ 2 / (1 + z) ^ 3) ^ 2 * Work.Spaces.w z ^ 2)
      (b := fun θ : ℝ => (Work.Spaces.Gam α θ / Work.Spaces.c α) ^ 2
        * (Real.sin (2 * θ)) ^ (-Work.Spaces.eta)) ha hb]
  -- ### Step 6: numerical conclusion
  have hX := Work.Coercivity.Gam_div_c_sq_eta_integral_le_12100 α hα hα1
  have hXnn : 0 ≤ ∫ θ in Work.Spaces.Iθ, (Work.Spaces.Gam α θ / Work.Spaces.c α) ^ 2
      * (Real.sin (2 * θ)) ^ (-Work.Spaces.eta) := by
    refine integral_nonneg_of_ae ?_
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Icc] with θ hθ
    exact mul_nonneg (sq_nonneg _) (Real.rpow_nonneg (hsin0 θ hθ) _)
  have hsq_le : Real.sqrt (4 * (∫ θ in Work.Spaces.Iθ,
      (Work.Spaces.Gam α θ / Work.Spaces.c α) ^ 2
      * (Real.sin (2 * θ)) ^ (-Work.Spaces.eta))) ≤ 220 := by
    have h110 : Real.sqrt (∫ θ in Work.Spaces.Iθ, (Work.Spaces.Gam α θ / Work.Spaces.c α) ^ 2
        * (Real.sin (2 * θ)) ^ (-Work.Spaces.eta)) ≤ 110 := by
      rw [show (110 : ℝ) = Real.sqrt 12100 by
        rw [show (12100 : ℝ) = 110^2 by norm_num, Real.sqrt_sq (by norm_num)]]
      exact Real.sqrt_le_sqrt hX
    have h4 : Real.sqrt (4 : ℝ) = 2 := by
      rw [show (4 : ℝ) = 2^2 by norm_num, Real.sqrt_sq (by norm_num)]
    rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 4), h4]
    nlinarith [h110, Real.sqrt_nonneg (∫ θ in Work.Spaces.Iθ,
      (Work.Spaces.Gam α θ / Work.Spaces.c α) ^ 2 * (Real.sin (2 * θ)) ^ (-Work.Spaces.eta))]
  calc |Work.Coercivity.wip
        (fun z θ => Work.Spaces.w z ^ 2 * (Real.sin (2 * θ)) ^ (-Work.Spaces.eta))
        (fun z θ => (Work.Spaces.Gam α θ / Work.Spaces.c α) * (2 * z ^ 2 / (1 + z) ^ 3) * Λ) f|
      = |∫ p, Λ * (A p * B p) ∂P| := by rw [hwip]
    _ = |Λ| * |∫ p, A p * B p ∂P| := by
        rw [MeasureTheory.integral_const_mul, abs_mul]
    _ ≤ |Λ| * (Real.sqrt (∫ p, A p ^ 2 ∂P) * Real.sqrt (∫ p, B p ^ 2 ∂P)) :=
        mul_le_mul_of_nonneg_left habs (abs_nonneg _)
    _ = |Λ| * (Real.sqrt ((∫ z in Work.Spaces.Iz, (2 * z ^ 2 / (1 + z) ^ 3) ^ 2
            * Work.Spaces.w z ^ 2)
          * (∫ θ in Work.Spaces.Iθ, (Work.Spaces.Gam α θ / Work.Spaces.c α) ^ 2
            * (Real.sin (2 * θ)) ^ (-Work.Spaces.eta))) * Real.sqrt (Work.Coercivity.EfEta f)) := by
        rw [hAval, hBval]
    _ = |Λ| * (Real.sqrt (4 * (∫ θ in Work.Spaces.Iθ,
            (Work.Spaces.Gam α θ / Work.Spaces.c α) ^ 2
            * (Real.sin (2 * θ)) ^ (-Work.Spaces.eta)))
          * Real.sqrt (Work.Coercivity.EfEta f)) := by
        rw [hzsq]
    _ ≤ |Λ| * (220 * Real.sqrt (Work.Coercivity.EfEta f)) := by
        refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
        exact mul_le_mul_of_nonneg_right hsq_le (Real.sqrt_nonneg _)
    _ = 220 * |Λ| * Real.sqrt (Work.Coercivity.EfEta f) := by ring


end Work.FTS.CoercivityFix.Coer1T
end
end
-- ===== merged: Submission.Work.FTS.CoercivityFix.Coer1T.psiA_eta_abs_le_Q =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.CoercivityFix.Coer1T

set_option autoImplicit false
set_option maxHeartbeats 2000000

/-!
# The `L₁₂`-correction pairing `⟨T1fun α f, f⟩_{w² sin^{-η}}` in the interior class

`T1fun α f = (2 z Γ(θ)/(c(1+z)²))·L₁₂(f)(z)` is the `L₁₂`-term of `𝓛_Γ`, and this file proves
the two facts about its `η`-weighted pairing against `f` that the `η`-slot of the level-1
coercivity of `𝓛_Γ^T` needs, **in the interior class** `SmoothQuad` (genuine `C^∞` on the open
quadrant) rather than the analytic class `IBP`/`CoerciveData` of
`Submission/Work/Coercivity/L2CoercivityTransportEta.lean` (see `Work.Coercivity.psiA_eta_abs_le`):

* the integrand `T1fun α f · f · w² sin(2θ)^{-η}` is jointly integrable on the quadrant;
* the pairing obeys `|⟨T1fun α f, f⟩_{w² sin^{-η}}| ≤ 220 √(EL12z f) √(EfEta f)`.

The proof is Cauchy–Schwarz in `L²(P)` (`P` the product of the restrictions of Lebesgue measure
to `Iz` and `Iθ`) after the pointwise split
`(2zΓ/(c(1+z)²))Λ f w² s^{-η} = 2·[(Γ/c)(Λ/z)s^{-η/2}]·[f w s^{-η/2}]`
(valid because `w = z²w²/(1+z)²`, i.e. `z·w²/(1+z)² = w/z`), which is the *only* place the weight
`w` enters.  The two `L²` norms are `√(EL12z f · ∫_θ (Γ/c)²s^{-η})` and `√(EfEta f)`, and
`∫_θ (Γ/c)²s^{-η} ≤ 12100 = 110²` (`Work.Coercivity.Gam_div_c_sq_eta_integral_le_12100`), giving
`2·110 = 220`.

The two ingredients really used are `HardyHyp f` (which supplies `∫ (L₁₂(f)/z)² < ∞` and the
continuity of `L₁₂(f)` on `(0,∞)`) and the joint integrability `hF` of `f²w² sin^{-η}`; the
a.e. strong measurability of `f` comes from `SmoothQuad`.
-/



end Work.FTS.CoercivityFix.Coer1T
end
end
-- ===== merged: Submission.Work.FTS.EllSol.EllPkgAux.MollAssem.Defs =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology Interval
open MeasureTheory Set Filter

namespace Work.FTS.EllSol.EllPkgAux

set_option autoImplicit false
set_option maxHeartbeats 800000

namespace MollAssem

/-! ## The measure-theoretic Fatou device -/

/-- **Fatou's lemma** (lower semicontinuity of the lower Lebesgue integral), stated at the
`ℝ≥0∞` level so that no integrability hypothesis is needed: if `ofReal (f x) ≤ liminf_n
ofReal (G n x)` almost everywhere, then `∫⁻ ofReal f ≤ liminf_n ∫⁻ ofReal (G n)`. -/
theorem fatou_lintegral_le_liminf {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {G : ℕ → α → ℝ} {f : α → ℝ}
    (hG : ∀ n, AEMeasurable (fun x => ENNReal.ofReal (G n x)) μ)
    (h : ∀ᵐ x ∂μ, ENNReal.ofReal (f x) ≤
      Filter.liminf (fun n => ENNReal.ofReal (G n x)) Filter.atTop) :
    ∫⁻ x, ENNReal.ofReal (f x) ∂μ ≤
      Filter.liminf (fun n => ∫⁻ x, ENNReal.ofReal (G n x) ∂μ) Filter.atTop :=
  (MeasureTheory.lintegral_mono_ae h).trans (MeasureTheory.lintegral_liminf_le' hG)

/-- `ENNReal.ofReal` of an a.e. strongly measurable real function is a.e. measurable. -/
theorem aemeasurable_ofReal_of_aestronglyMeasurable {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {f : α → ℝ} (h : AEStronglyMeasurable f μ) :
    AEMeasurable (fun x => ENNReal.ofReal (f x)) μ :=
  ENNReal.measurable_ofReal.comp_aemeasurable h.aemeasurable

/-- `mixIntS` is pointwise nonnegative (the `θ`-integrand is a square times `thEta ≥ 0`). -/
theorem mixIntS_nonneg_mfa (u : ℝ → ℝ → ℝ) (z : ℝ) :
    0 ≤ Work.EllipticEst.Core.mixIntS u z := by
  rw [Work.EllipticEst.Core.mixIntS]
  refine mul_nonneg (sq_nonneg _) ?_
  refine MeasureTheory.integral_nonneg_of_ae ?_
  refine ae_restrict_of_forall_mem measurableSet_Icc (fun θ hθ => ?_)
  exact mul_nonneg (sq_nonneg _) (Work.FTS.EllipticEst.thEta_nonneg hθ)

/-! ## The interval estimate of the slice domination -/

/-- On `(0, π/2)` the weight `thEta θ = sin(2θ)^{-η}` is at least `1`. -/
theorem one_le_thEta {θ : ℝ} (hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)) :
    1 ≤ Work.FTS.EllipticEst.thEta θ := by
  have hsinpos : 0 < Real.sin (2 * θ) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])
  have h := Real.rpow_le_rpow_of_nonpos hsinpos (Real.sin_le_one (2 * θ))
    (show -(Work.Spaces.eta) ≤ 0 by rw [Work.Spaces.eta]; norm_num)
  rw [Real.one_rpow] at h
  simpa only [Work.FTS.EllipticEst.thEta] using h

/-- **The interval estimate of the slice domination.**  Weighted Cauchy--Schwarz with the
constant weight `1` on the interval `[l,u]` (length at most `π/4`) against the angular weight
`thEta ≥ 1` on `(0,π/2)`:
`|∫_l^u (c-t)D t| ≤ (π/4)·√(π/4)·√(∫_{Iθ} D²thEta)`. -/
theorem sliceIntBoundMFA {D : ℝ → ℝ} {c l u : ℝ} (hlu : l ≤ u) (hl : 0 < l)
    (hu : u < Real.pi / 2) (hul : u - l ≤ Real.pi / 4) (hcont : ContinuousOn D (Set.uIcc l u))
    (hc : ∀ t ∈ Set.Icc l u, |c - t| ≤ Real.pi / 4)
    (hint : MeasureTheory.IntegrableOn (fun θ : ℝ => D θ ^ 2 * Work.FTS.EllipticEst.thEta θ)
      Work.Spaces.Iθ) :
    |∫ t in l..u, (c - t) * D t| ≤ (Real.pi / 4) * Real.sqrt (Real.pi / 4) *
      Real.sqrt (∫ θ in Work.Spaces.Iθ, D θ ^ 2 * Work.FTS.EllipticEst.thEta θ) := by
  have hpi4 : (0 : ℝ) < Real.pi / 4 := by linarith [Real.pi_pos]
  have hth : ∀ t ∈ Set.Icc l u, 1 ≤ Work.FTS.EllipticEst.thEta t := fun t ht =>
    one_le_thEta ⟨lt_of_lt_of_le hl ht.1, lt_of_le_of_lt ht.2 hu⟩
  have hIntAbs : IntervalIntegrable (fun t : ℝ => |D t|) volume l u :=
    hcont.abs.intervalIntegrable
  have h12 : |∫ t in l..u, (c - t) * D t| ≤ ∫ t in l..u, |(c - t) * D t| :=
    intervalIntegral.abs_integral_le_integral_abs hlu
  have h23 : ∫ t in l..u, |(c - t) * D t| ≤ (Real.pi / 4) * ∫ t in l..u, |D t| := by
    rw [← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_mono_on hlu
      (((continuousOn_const.sub continuousOn_id).mul hcont).abs.intervalIntegrable)
      (hIntAbs.const_mul _) ?_
    intro t ht
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_right (hc t ht) (abs_nonneg _)
  have hD2int : MeasureTheory.IntegrableOn (fun t : ℝ => D t ^ 2) (Set.Ioc l u) := by
    have h1 : MeasureTheory.IntegrableOn (fun t : ℝ => D t ^ 2) (Set.uIcc l u) :=
      (hcont.pow 2).integrableOn_compact isCompact_uIcc
    rw [Set.uIcc_of_le hlu] at h1
    exact h1.mono_set Set.Ioc_subset_Icc_self
  have h1int : MeasureTheory.IntegrableOn (fun _ : ℝ => (1 : ℝ)) (Set.Ioc l u) := by
    refine MeasureTheory.integrableOn_const (s := Set.Ioc l u) (C := (1 : ℝ)) ?_ ?_
    · rw [Real.volume_Ioc]; exact ENNReal.ofReal_ne_top
    · simp
  have hcs : (∫ t in l..u, |D t|) ^ 2 ≤ (u - l) * (∫ t in l..u, D t ^ 2) := by
    have h := Work.FTS.EllipticEst.remov.interval_integral_sq_le_mul (f := fun t : ℝ => |D t|)
      (σ := fun _ : ℝ => (1 : ℝ)) hlu (fun s _ => by norm_num)
      (hD2int.congr_fun (fun s _ => by rw [mul_one, sq_abs]) measurableSet_Ioc)
      (by simpa using h1int)
    have hs1 : (∫ s in l..u, |D s| ^ 2 * (1 : ℝ)) = ∫ s in l..u, D s ^ 2 :=
      intervalIntegral.integral_congr (fun s _ => by rw [mul_one, sq_abs])
    have hs2 : (∫ s in l..u, ((1 : ℝ))⁻¹) = u - l := by
      rw [inv_one, intervalIntegral.integral_const, smul_eq_mul, mul_one]
    rw [hs1, hs2] at h
    exact h.trans_eq (mul_comm _ _)
  have hmono : ∫ t in l..u, D t ^ 2 ≤
      ∫ θ in Work.Spaces.Iθ, D θ ^ 2 * Work.FTS.EllipticEst.thEta θ := by
    have hsub1 : Set.Ioc l u ⊆ Work.Spaces.Iθ := by
      intro t ht
      exact ⟨le_trans (le_of_lt hl) (le_of_lt ht.1), le_trans ht.2 (le_of_lt hu)⟩
    have h2int : MeasureTheory.IntegrableOn
        (fun t : ℝ => D t ^ 2 * Work.FTS.EllipticEst.thEta t) (Set.Ioc l u) :=
      hint.mono_set hsub1
    have hpoint : ∀ t ∈ Set.Ioc l u, D t ^ 2 ≤ D t ^ 2 * Work.FTS.EllipticEst.thEta t := by
      intro t ht
      have := hth t (Set.Ioc_subset_Icc_self ht)
      calc D t ^ 2 = D t ^ 2 * 1 := by ring
        _ ≤ D t ^ 2 * Work.FTS.EllipticEst.thEta t :=
            mul_le_mul_of_nonneg_left this (sq_nonneg _)
    have hA : ∫ t in l..u, D t ^ 2 ≤
        ∫ t in l..u, D t ^ 2 * Work.FTS.EllipticEst.thEta t := by
      rw [intervalIntegral.integral_of_le hlu, intervalIntegral.integral_of_le hlu]
      exact MeasureTheory.setIntegral_mono_on hD2int h2int measurableSet_Ioc hpoint
    have hB : ∫ t in l..u, D t ^ 2 * Work.FTS.EllipticEst.thEta t ≤
        ∫ θ in Work.Spaces.Iθ, D θ ^ 2 * Work.FTS.EllipticEst.thEta θ := by
      rw [intervalIntegral.integral_of_le hlu]
      refine MeasureTheory.setIntegral_mono_set hint ?_ ?_
      · refine ae_restrict_of_forall_mem measurableSet_Icc (fun θ hθ => ?_)
        exact mul_nonneg (sq_nonneg _) (Work.FTS.EllipticEst.thEta_nonneg hθ)
      · refine Filter.Eventually.of_forall (fun x hx => ?_)
        exact ⟨le_trans (le_of_lt hl) (le_of_lt hx.1), le_trans hx.2 (le_of_lt hu)⟩
    exact hA.trans hB
  have hsq : (∫ t in l..u, |D t|) ^ 2 ≤ (Real.pi / 4) *
      (∫ θ in Work.Spaces.Iθ, D θ ^ 2 * Work.FTS.EllipticEst.thEta θ) := by
    refine hcs.trans ?_
    refine mul_le_mul hul hmono ?_ (le_of_lt hpi4)
    exact intervalIntegral.integral_nonneg_of_ae hlu (ae_of_all _ (fun t => sq_nonneg (D t)))
  have hIabs_nn : 0 ≤ ∫ t in l..u, |D t| :=
    intervalIntegral.integral_nonneg_of_ae hlu (ae_of_all _ (fun t => abs_nonneg _))
  have hRnn : 0 ≤ ∫ θ in Work.Spaces.Iθ, D θ ^ 2 * Work.FTS.EllipticEst.thEta θ :=
    MeasureTheory.integral_nonneg_of_ae (ae_restrict_of_forall_mem measurableSet_Icc
      (fun θ hθ => mul_nonneg (sq_nonneg _) (Work.FTS.EllipticEst.thEta_nonneg hθ)))
  have hbound : ∫ t in l..u, |D t| ≤ Real.sqrt (Real.pi / 4) *
      Real.sqrt (∫ θ in Work.Spaces.Iθ, D θ ^ 2 * Work.FTS.EllipticEst.thEta θ) := by
    have h1 : ∫ t in l..u, |D t| ≤ Real.sqrt ((Real.pi / 4) *
        (∫ θ in Work.Spaces.Iθ, D θ ^ 2 * Work.FTS.EllipticEst.thEta θ)) :=
      (Real.le_sqrt hIabs_nn (mul_nonneg (le_of_lt hpi4) hRnn)).mpr hsq
    rwa [Real.sqrt_mul (le_of_lt hpi4)] at h1
  calc |∫ t in l..u, (c - t) * D t| ≤ ∫ t in l..u, |(c - t) * D t| := h12
    _ ≤ (Real.pi / 4) * ∫ t in l..u, |D t| := h23
    _ ≤ (Real.pi / 4) * (Real.sqrt (Real.pi / 4) *
        Real.sqrt (∫ θ in Work.Spaces.Iθ, D θ ^ 2 * Work.FTS.EllipticEst.thEta θ)) :=
        mul_le_mul_of_nonneg_left hbound (le_of_lt hpi4)
    _ = (Real.pi / 4) * Real.sqrt (Real.pi / 4) *
        Real.sqrt (∫ θ in Work.Spaces.Iθ, D θ ^ 2 * Work.FTS.EllipticEst.thEta θ) := by ring

end MollAssem

end Work.FTS.EllSol.EllPkgAux
end
end
-- ===== merged: Submission.Work.FTS.EllipticEst.Blocks.AgmonIBP =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.Blocks

open scoped Real Topology ContDiff
open MeasureTheory Set Filter

noncomputable section

/-- **The integration by parts underlying the compactly supported weighted Agmon inequality.**
For `h` of class `C^∞` on `(0,∞)` vanishing off `[a,b]` with `0 < a`,

  `∫_0^∞ ρ(z)(z h')² = - ∫_0^∞ (d/dz)(ρ z² h') · h`,   `ρ = W2 z = w(z)²`,

both boundary terms `ρ z² h' h` at `0` and at `∞` vanishing because `h` is compactly supported
inside `(0,∞)`.  This is `integral_Ioi_mul_deriv_eq_deriv_mul` with `u = ρ z² h'` and `v = h`. -/
theorem AgmonIBP {h : ℝ → ℝ} {a b : ℝ} (ha : 0 < a)
    (hsupp : ∀ z, z ∉ Set.Icc a b → h z = 0)
    (hcd : ContDiffOn ℝ Work.Stability.smoothOrder h (Set.Ioi (0 : ℝ))) :
    (∫ z in Set.Ioi (0 : ℝ), Work.FTS.EllipticEst.Blocks.W2 z * (z * deriv h z) ^ 2)
      = - ∫ z in Set.Ioi (0 : ℝ),
          deriv (fun y : ℝ => Work.FTS.EllipticEst.Blocks.W2 y * y ^ 2 * deriv h y) z
            * h z := by
  have hne : Work.Stability.smoothOrder ≠ 0 := by simp [Work.Stability.smoothOrder]
  -- `ρ` is `C^∞` on `(0,∞)` (closed form `(1+z)⁴/z⁴`)
  have hW2inf : ContDiffOn ℝ Work.Stability.smoothOrder W2 (Set.Ioi (0:ℝ)) := by
    have hform : ContDiffOn ℝ Work.Stability.smoothOrder
        (fun z : ℝ => (1 + z) ^ 4 / z ^ 4) (Set.Ioi (0:ℝ)) := by
      apply ContDiffOn.div
      · fun_prop
      · fun_prop
      · intro z hz; exact pow_ne_zero 4 (ne_of_gt hz)
    exact hform.congr (fun z _ => W2_eq z)
  -- `h` is `C^∞`, so is `h'`, so is the coefficient `u := ρ z² h'`
  have hdhinf : ContDiffOn ℝ Work.Stability.smoothOrder (deriv h) (Set.Ioi (0:ℝ)) :=
    hcd.deriv_of_isOpen isOpen_Ioi (by simp [Work.Stability.smoothOrder])
  have hUinf : ContDiffOn ℝ Work.Stability.smoothOrder
      (fun y : ℝ => W2 y * y ^ 2 * deriv h y) (Set.Ioi (0:ℝ)) :=
    (hW2inf.mul (by fun_prop)).mul hdhinf
  have hU1 : ContDiffOn ℝ 1 (fun y : ℝ => W2 y * y ^ 2 * deriv h y) (Set.Ioi (0:ℝ)) :=
    hUinf.of_le (by simp [Work.Stability.smoothOrder])
  -- differentiability of `h` and of `u` on `(0,∞)`
  have hderivAt : ∀ z : ℝ, 0 < z → HasDerivAt h (deriv h z) z := fun z hz =>
    ((hcd.differentiableOn hne).differentiableAt (isOpen_Ioi.mem_nhds hz)).hasDerivAt
  have huDerivAt : ∀ z : ℝ, 0 < z →
      HasDerivAt (fun y : ℝ => W2 y * y ^ 2 * deriv h y)
        (deriv (fun y : ℝ => W2 y * y ^ 2 * deriv h y) z) z := fun z hz =>
    ((hUinf.differentiableOn hne).differentiableAt (isOpen_Ioi.mem_nhds hz)).hasDerivAt
  -- off the support, `h` vanishes on a neighbourhood, hence so does `h'`
  have hderiv_zero : ∀ z : ℝ, z ∉ Set.Icc a b → deriv h z = 0 := by
    intro z hz
    have hz' : z < a ∨ b < z := by
      simpa only [Set.mem_Icc, not_and_or, not_le] using hz
    rcases hz' with hlt | hgt
    · have hev : h =ᶠ[𝓝 z] fun _ : ℝ => (0:ℝ) := by
        filter_upwards [isOpen_Iio.mem_nhds hlt] with y hy
        exact hsupp y (by
          simp only [Set.mem_Icc, not_and_or, not_le]; exact Or.inl hy)
      rw [hev.deriv_eq]; simp
    · have hev : h =ᶠ[𝓝 z] fun _ : ℝ => (0:ℝ) := by
        filter_upwards [isOpen_Ioi.mem_nhds hgt] with y hy
        exact hsupp y (by
          simp only [Set.mem_Icc, not_and_or, not_le]; exact Or.inr hy)
      rw [hev.deriv_eq]; simp
  have hsub : Set.Icc a b ⊆ Set.Ioi (0:ℝ) := fun x hx => by
    simp only [Set.mem_Ioi]; linarith [hx.1, ha]
  have hcontW : ContinuousOn W2 (Set.Icc a b) := hW2inf.continuousOn.mono hsub
  have hcontDh : ContinuousOn (deriv h) (Set.Icc a b) := hdhinf.continuousOn.mono hsub
  have hcontH : ContinuousOn h (Set.Icc a b) := hcd.continuousOn.mono hsub
  have hcontDU : ContinuousOn (deriv (fun y : ℝ => W2 y * y ^ 2 * deriv h y)) (Set.Icc a b) :=
    (hU1.continuousOn_deriv_of_isOpen isOpen_Ioi le_rfl).mono hsub
  -- integrability of the two products over `(0,∞)` (both are supported in `[a,b]`)
  have hInt1 : IntegrableOn (fun z : ℝ => (W2 z * z ^ 2 * deriv h z) * deriv h z) (Set.Ioi 0) := by
    refine integrableOn_Ioi_of_continuousOn_Icc_of_eq_zero_off (a := a) (b := b) ?_ ?_
    · exact ((hcontW.mul (continuousOn_id.pow 2)).mul hcontDh).mul hcontDh
    · intro z hz
      rw [hderiv_zero z hz]; ring
  have hInt2 : IntegrableOn (fun z : ℝ =>
      deriv (fun y : ℝ => W2 y * y ^ 2 * deriv h y) z * h z) (Set.Ioi 0) := by
    refine integrableOn_Ioi_of_continuousOn_Icc_of_eq_zero_off (a := a) (b := b) ?_ ?_
    · exact hcontDU.mul hcontH
    · intro z hz; rw [hsupp z hz]; ring
  -- the boundary term `u * h = ρ z² h' h` vanishes at both ends
  have hTend0 : Tendsto (fun z : ℝ => (W2 z * z ^ 2 * deriv h z) * h z) (𝓝[>] (0:ℝ)) (𝓝 0) := by
    have hev : (fun _ : ℝ => (0:ℝ)) =ᶠ[𝓝[>] (0:ℝ)]
        (fun z : ℝ => (W2 z * z ^ 2 * deriv h z) * h z) := by
      filter_upwards [Ioo_mem_nhdsGT ha] with z hz
      rw [hsupp z (by
        simp only [Set.mem_Icc, not_and_or, not_le]; exact Or.inl hz.2)]
      ring
    exact tendsto_const_nhds.congr' hev
  have hTendTop : Tendsto (fun z : ℝ => (W2 z * z ^ 2 * deriv h z) * h z) atTop (𝓝 0) := by
    have hev : (fun _ : ℝ => (0:ℝ)) =ᶠ[atTop]
        (fun z : ℝ => (W2 z * z ^ 2 * deriv h z) * h z) := by
      filter_upwards [eventually_gt_atTop b] with z hz
      rw [hsupp z (by
        simp only [Set.mem_Icc, not_and_or, not_le]; exact Or.inr hz)]
      ring
    exact tendsto_const_nhds.congr' hev
  -- integration by parts on `(0,∞)` with `u = ρ z² h'`, `v = h`
  have hkey := MeasureTheory.integral_Ioi_mul_deriv_eq_deriv_mul
      (a := (0:ℝ)) (a' := (0:ℝ)) (b' := (0:ℝ))
      (u := fun y : ℝ => W2 y * y ^ 2 * deriv h y)
      (u' := deriv (fun y : ℝ => W2 y * y ^ 2 * deriv h y))
      (v := h) (v' := deriv h)
      huDerivAt hderivAt hInt1 hInt2 hTend0 hTendTop
  rw [show (fun z : ℝ => W2 z * (z * deriv h z) ^ 2)
      = fun z : ℝ => (W2 z * z ^ 2 * deriv h z) * deriv h z from funext fun z => by ring,
    hkey]
  ring

end

end Work.FTS.EllipticEst.Blocks
end
-- ===== merged: Submission.Work.FTS.EllipticEst.PropL2CutKids.Wc_deriv_bdd =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.PropL2CutKids

open scoped Real Topology ContDiff
open MeasureTheory Set Filter

set_option linter.unusedVariables false

/-! ## Boundedness of the derivatives of the cutoff `Wc`

`Wc n z = ψ((n+1)z)·χ(z/(n+1))` where `ψ = Real.smoothTransition` and `χ = Work.Stability.chi`.
We prove that the derivatives of `z * (Wc n z)^2` and of `z^2 * (Wc n z)^2` are bounded
*uniformly in `n` and `z`*.

The reason this is true (although the sup-norm of the second derivative of `Wc n` grows like
`n^2`) is the two-scale structure: the `ψ`-part is differentiated with respect to the variable
`u = (n+1)z` and the `χ`-part with respect to `v = z/(n+1)`, and the combinations
`u·ψ'(u)`, `u^2·ψ''(u)`, `v·χ'(v)`, `v^2·χ''(v)` are all uniformly bounded (each derivative of
`ψ` is supported in `[0,1]` and each derivative of `χ` in `[-2,2]`).

The auxiliary finite bound is provided by `Wc_aux_bounds`; the two derivative formulas by
`deriv_Wc`/`deriv_deriv_Wc`; the uniform bounds on `z·(Wc n)'` and `z^2·(Wc n)''` by
`Wc_z_mul_deriv_bound`/`Wc_zsq_mul_deriv2_bound`; and the final passage to the derivatives of
`z·(Wc n)^2` and `z^2·(Wc n)^2` by `mul_sq_deriv_bound`/`sq_mul_sq_deriv_bound`. -/

/-! ### A generic sup-bound for a continuous function vanishing off a compact interval -/

lemma exists_bound_of_continuous_zero_off (f : ℝ → ℝ) (hf : Continuous f) {a b : ℝ}
    (hsupp : ∀ x, x < a ∨ b < x → f x = 0) : ∃ M : ℝ, 0 ≤ M ∧ ∀ x, |f x| ≤ M := by
  obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn (s := Set.Icc a b) hf.continuousOn
  exact ⟨max M 0, le_max_right _ _, fun x => by
    rcases lt_or_ge x a with h | h
    · rw [hsupp x (Or.inl h), abs_zero]; exact le_max_right _ _
    · rcases lt_or_ge b x with h1 | h1
      · rw [hsupp x (Or.inr h1), abs_zero]; exact le_max_right _ _
      · have hx : x ∈ Set.Icc a b := ⟨h, h1⟩
        have h2 := hM x hx
        rw [Real.norm_eq_abs] at h2
        exact le_trans h2 (le_max_left _ _)⟩

/-! ### The supports of the derivatives of `ψ` and `χ` -/

lemma deriv_smoothTransition_eq_zero_of_lt {x : ℝ} (hx : x < 0) :
    deriv Real.smoothTransition x = 0 := by
  have hmem : ∀ᶠ y in 𝓝 x, y < 0 := IsOpen.mem_nhds isOpen_Iio hx
  have heq : Real.smoothTransition =ᶠ[𝓝 x] (fun _ : ℝ => (0 : ℝ)) :=
    hmem.mono fun y hy => Real.smoothTransition.zero_of_nonpos hy.le
  rw [Filter.EventuallyEq.deriv_eq heq, deriv_const]

lemma deriv_smoothTransition_eq_zero_of_gt {x : ℝ} (hx : 1 < x) :
    deriv Real.smoothTransition x = 0 := by
  have hmem : ∀ᶠ y in 𝓝 x, 1 < y := IsOpen.mem_nhds isOpen_Ioi hx
  have heq : Real.smoothTransition =ᶠ[𝓝 x] (fun _ : ℝ => (1 : ℝ)) :=
    hmem.mono fun y hy => Real.smoothTransition.one_of_one_le hy.le
  rw [Filter.EventuallyEq.deriv_eq heq, deriv_const]

lemma deriv2_smoothTransition_eq_zero_of_lt {x : ℝ} (hx : x < 0) :
    deriv (deriv Real.smoothTransition) x = 0 := by
  have hmem : ∀ᶠ y in 𝓝 x, y < 0 := IsOpen.mem_nhds isOpen_Iio hx
  have heq : (deriv Real.smoothTransition) =ᶠ[𝓝 x] (fun _ : ℝ => (0 : ℝ)) :=
    hmem.mono fun y hy => deriv_smoothTransition_eq_zero_of_lt hy
  rw [Filter.EventuallyEq.deriv_eq heq, deriv_const]

lemma deriv2_smoothTransition_eq_zero_of_gt {x : ℝ} (hx : 1 < x) :
    deriv (deriv Real.smoothTransition) x = 0 := by
  have hmem : ∀ᶠ y in 𝓝 x, 1 < y := IsOpen.mem_nhds isOpen_Ioi hx
  have heq : (deriv Real.smoothTransition) =ᶠ[𝓝 x] (fun _ : ℝ => (0 : ℝ)) :=
    hmem.mono fun y hy => deriv_smoothTransition_eq_zero_of_gt hy
  rw [Filter.EventuallyEq.deriv_eq heq, deriv_const]




/-! ### The common finite bound -/


/-! ### Derivatives of an affinely rescaled function -/



/-! ### The two derivative formulas for `Wc` -/



/-! ### The two scaled bounds for `Wc` -/



/-! ### Derivatives of `y ↦ y (W y)^2` and `y ↦ y^2 (W y)^2` -/




/-! ### The two final bounds, for an abstract function `W` -/



/-! ### The result -/




end Work.FTS.EllipticEst.PropL2CutKids
end
-- ===== merged: Submission.Work.FTS.EllipticEst.TT.logChi_contDiffOn =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.TT

/-- `logChi n` is `C^∞` (genuine smoothness, `Work.Stability.smoothOrder = ((⊤ : ℕ∞) : ℕ∞ω)`,
NOT analyticity) on the open half-line `(0,∞)`: it is the composition of the globally `C^∞` bump
`Work.ChiExplicit.chi` with `z ↦ Real.log z / Real.log ((n:ℝ)+2)`, which is smooth on `(0,∞)`
and whose denominator `log ((n:ℝ)+2)` is positive because `(n:ℝ)+2 ≥ 2 > 1`. -/
theorem logChi_contDiffOn (n : ℕ) :
    ContDiffOn ℝ Work.Stability.smoothOrder (Work.FTS.EllipticEst.TT.logChi n) (Set.Ioi 0) := by
  -- The rescaling `g z = log z / log ((n:ℝ)+2)` is smooth on `(0,∞)`: `Real.log` is smooth off
  -- `0`, and dividing by the *constant* `log ((n:ℝ)+2)` preserves smoothness.
  have hg : ContDiffOn ℝ Work.Stability.smoothOrder
      (fun z : ℝ => Real.log z / Real.log ((n : ℝ) + 2)) (Set.Ioi 0) :=
    (Real.contDiffOn_log.mono (by
      intro x hx
      simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
      exact ne_of_gt hx)).div_const _
  -- `chi` is globally `C^∞`, hence `C^∞` on every set; compose with `g`.
  have hcomp : ContDiffOn ℝ Work.Stability.smoothOrder
      (Work.ChiExplicit.chi ∘ fun z : ℝ => Real.log z / Real.log ((n : ℝ) + 2))
      (Set.Ioi 0) :=
    (Work.ChiExplicit.chi_contDiff (⊤ : ℕ∞)).comp_contDiffOn hg
  -- Unfold `logChi` and `Function.comp`.
  exact hcomp.congr (fun z _ => rfl)

end Work.FTS.EllipticEst.TT
end
-- ===== merged: Submission.Work.FTS.EpsEngine.ThetaFromEpsLeafA.StripDefs =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `ThetaFromEpsLeafA/StripDefs` — the two angular truncations `stripLo`/`stripHi`

The two truncations used by sub-leaves **(A)** (`sinpow_mixed_Jeps_le_strip`) and **(B)**
(`tendsto_EpsSq_strip`) of the θ-uniformity chapter, with the **same qualified names**
(`Work.FTS.EpsEngine.ThetaFromEps.stripLo`, `Work.FTS.EpsEngine.ThetaFromEps.stripHi`) and the
same bodies as the original declarations inside `EpsEngine/ThetaFromEps.lean`.

## Why this module exists

`EpsEngine/ThetaFromEps.lean` currently *imports* the two sub-leaf modules
(`ThetaFromEpsLeafB.tendsto_EpsSq_strip`, and it is meant to import
`ThetaFromEpsLeafA.sinpow_mixed_Jeps_le_strip` as well), while those leaf modules need the
truncations — which until now were declared only inside `ThetaFromEps.lean`.  That is an import
cycle, and Lake refuses to build any module of the cone.

Declaring the truncations here breaks the cycle in the only consistent way: the leaf modules (and
everything else) get the definitions from this module, and `EpsEngine/ThetaFromEps.lean` must
**drop its own `stripLo`/`stripHi` declarations and import this module instead** (otherwise the
same name would be declared twice in one environment).  The definitions are byte-for-byte the
originals, so nothing changes mathematically.

This is the same workaround as the `Aux/` twin modules of `Work.FTS.EllipticEst` documented in
`HANDOFF.md` ("keep a buildable twin with the same namespace and declaration name, which is the
copy consumers import").
-/

noncomputable section

namespace Work.FTS.EpsEngine.ThetaFromEps

set_option autoImplicit false
set_option linter.unusedVariables false

open Work.FTS.Galerkin (Fn)

/-- truncation of `g` to the angular strip `θ ≤ φ`. -/
def stripLo (φ : ℝ) (g : Fn) : Fn := fun z θ => if θ ≤ φ then g z θ else 0

/-- truncation of `g` to the angular strip `θ ≥ π/2 - φ`. -/
def stripHi (φ : ℝ) (g : Fn) : Fn := fun z θ => if Real.pi / 2 - φ ≤ θ then g z θ else 0

end Work.FTS.EpsEngine.ThetaFromEps
end
end
-- ===== merged: Submission.Work.FTS.GalBasis.cc.CutDefs =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology

namespace Work.FTS.GalBasis.cc

open Work.FTS.Galerkin (Fn)

/-- The radial step of mesh `1/(N+1)`: `0` for `z ≤ 1/(N+1)`, `1` on `[2/(N+1), N+1]`, `0`
again for `z ≥ 2(N+1)`. -/
def cutA (N : ℕ) : ℝ → ℝ := fun z =>
  Real.smoothTransition (((N : ℝ) + 1) * z - 1) * Real.smoothTransition (2 - z / ((N : ℝ) + 1))

/-- The angular step of mesh `1/(N+1)`: `0` for `θ ≤ 1/(N+1)` or `θ ≥ π/2 - 1/(N+1)`, and `1`
on `[2/(N+1), π/2 - 2/(N+1)]`. -/
def cutB (N : ℕ) : ℝ → ℝ := fun θ =>
  Real.smoothTransition (((N : ℝ) + 1) * θ - 1)
    * Real.smoothTransition (((N : ℝ) + 1) * (Real.pi / 2 - θ) - 1)

/-- **The cutoff family** of the density lemma. -/
def psiCut (N : ℕ) : Fn := fun z θ => cutA N z * cutB N θ

/-- The lower end of the outer box in the `z`-variable: `1/(N+1)`. -/
def zlo (N : ℕ) : ℝ := 1 / ((N : ℝ) + 1)

/-- The upper end of the outer box in the `z`-variable: `2(N+1)`. -/
def zhi (N : ℕ) : ℝ := 2 * ((N : ℝ) + 1)

/-- The lower end of the outer box in the `θ`-variable: `1/(N+1)`. -/
def tlo (N : ℕ) : ℝ := 1 / ((N : ℝ) + 1)

/-- The upper end of the outer box in the `θ`-variable: `π/2 - 1/(N+1)`. -/
def thi (N : ℕ) : ℝ := Real.pi / 2 - 1 / ((N : ℝ) + 1)

/-- The lower end of the plateau in the `z`-variable: `2/(N+1)`. -/
def plo (N : ℕ) : ℝ := 2 / ((N : ℝ) + 1)

/-- The upper end of the plateau in the `z`-variable: `N+1`. -/
def phiN (N : ℕ) : ℝ := (N : ℝ) + 1

/-- The lower end of the plateau in the `θ`-variable: `2/(N+1)`. -/
def qlo (N : ℕ) : ℝ := 2 / ((N : ℝ) + 1)

/-- The upper end of the plateau in the `θ`-variable: `π/2 - 2/(N+1)`. -/
def qhi (N : ℕ) : ℝ := Real.pi / 2 - 2 / ((N : ℝ) + 1)

/-- `(z,θ)` lies in the *plateau* of `psiCut N`, where it equals `1`. -/
def InPlateau (N : ℕ) (z θ : ℝ) : Prop := z ∈ Set.Icc (plo N) (phiN N) ∧ θ ∈ Set.Icc (qlo N) (qhi N)

/-- `(z,θ)` lies outside the *outer box* of `psiCut N`, where it vanishes. -/
def OffBox (N : ℕ) (z θ : ℝ) : Prop :=
  z ∉ Set.Icc (zlo N) (zhi N) ∨ θ ∉ Set.Icc (tlo N) (thi N)

/-- `θ` lies outside the two *layers* of the angular step `cutB N` (the intervals
`[1/(N+1), 2/(N+1)]` and `[π/2 - 2/(N+1), π/2 - 1/(N+1)]`), i.e. in the region where `cutB N` is
constant and its iterated `D_θ`-derivatives vanish. -/
def NotInThetaLayer (N : ℕ) (θ : ℝ) : Prop :=
  θ ∉ Set.Icc (tlo N) (2 / ((N : ℝ) + 1)) ∧ θ ∉ Set.Icc (Real.pi / 2 - 2 / ((N : ℝ) + 1)) (thi N)



end Work.FTS.GalBasis.cc
end
end
-- ===== merged: Submission.Work.FTS.GalBasis.cc.ShrinkDefs =====
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

open Work.FTS.Galerkin (Fn)




end Work.FTS.GalBasis.cc
end
end
-- ===== merged: Submission.Work.FTS.GalBasis.cc.SlotDefs =====
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

open Work.FTS.Galerkin (Fn)

/-- The pure weight `w z / sin(2θ)^{η/2}` of the `D_z`-family slots (as it appears in
`Work.Spaces.HkIntegrand`). -/
def pw (z θ : ℝ) : ℝ := Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2)



/-- The `D_z`-family slot density with the **mixed** weight, `D_z^a f · Wt α`: this is the
quantity produced by the terms of the Leibniz expansion of `mixed j i (χ f)` in which all the
`θ`-derivatives fall on the multiplier `χ` (`i - a = 0`). -/
def zslotW (α : ℝ) (a : ℕ) (f : Fn) (z θ : ℝ) : ℝ :=
  Work.Spaces.DzIter a f z θ * Work.Spaces.Wt α z θ


end Work.FTS.GalBasis.cc
end
end
-- ===== merged: Submission.Work.FTS.Galerkin.Compactness.convLocUnif_convPoint =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.Galerkin.Compactness


end Work.FTS.Galerkin.Compactness
end
-- ===== merged: Submission.Work.FTS.Galerkin.Compactness.exists_seq_dense_slab =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.Galerkin.Compactness

open scoped Real Topology
open Set Metric

set_option autoImplicit false

/-! ## Rational approximation in the two closed intervals

Two elementary one-dimensional approximation lemmas: points of `[0,∞)` and of `[0,π/2]` can be
approximated to any accuracy by *rational* points of the same interval.  Both are proved from
`exists_rat_btwn` (density of `ℚ` in `ℝ`) by exhibiting two explicit strict bounds between which we
interpolate.  The upper endpoint `π/2` is handled by keeping the rational strictly below it. -/



/-! ## The dense sequence -/




end Work.FTS.Galerkin.Compactness
end
-- ===== merged: Submission.Work.FTS.Galerkin.Compactness.exists_strictMono_forall_tendsto_of_bounded =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.Galerkin.Compactness


end Work.FTS.Galerkin.Compactness
end
-- ===== merged: Submission.Work.FTS.Galerkin.Compactness.tendsto_of_norm_derivWithin_le =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.Galerkin.Compactness


end Work.FTS.Galerkin.Compactness
end
-- ===== merged: Submission.Work.FTS.Galerkin.Hilbert.HkMem_const_mul =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.Galerkin.Hilbert

set_option autoImplicit false
set_option linter.unusedVariables false

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

/-! ## Scalar homogeneity of the weighted `ℋ^k`-integrand

The whole content is that `HkIntegrand` is a sum of squares of expressions that are *linear* in
`f`, so it is homogeneous of degree two: `HkIntegrand α k (c·f) = c² · HkIntegrand α k f`.
The operators appearing in `HkIntegrand` (`pz`, `pth`, `Dz`, `Dth`, their iterates, and
`mixed = D_z^j ∘ D_θ^i`) all commute with multiplication by a constant, and this commutation is
**unconditional**: `deriv` is scalar homogeneous with no differentiability hypothesis (if `f` is
not differentiable at `x` then neither is `c * f` for `c ≠ 0`, and both sides are `0`).  In
particular the smoothness hypothesis `SmoothNbhd f` of the main theorem is not needed here.
-/

/-- `deriv` is scalar homogeneous **unconditionally**, unlike Mathlib's `deriv_const_mul`
(which assumes `DifferentiableAt`). -/
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

private theorem pz_const_mul (c : ℝ) (f : ℝ → ℝ → ℝ) :
    Work.Spaces.pz (fun z θ => c * f z θ) = fun z θ => c * Work.Spaces.pz f z θ := by
  funext z θ
  simp only [Work.Spaces.pz]
  rw [deriv_const_mul_uncond]

private theorem pth_const_mul (c : ℝ) (f : ℝ → ℝ → ℝ) :
    Work.Spaces.pth (fun z θ => c * f z θ) = fun z θ => c * Work.Spaces.pth f z θ := by
  funext z θ
  simp only [Work.Spaces.pth]
  rw [deriv_const_mul_uncond]

private theorem Dz_const_mul (c : ℝ) (f : ℝ → ℝ → ℝ) :
    Work.Spaces.Dz (fun z θ => c * f z θ) = fun z θ => c * Work.Spaces.Dz f z θ := by
  funext z θ
  simp only [Work.Spaces.Dz, pz_const_mul]
  ring

private theorem Dth_const_mul (c : ℝ) (f : ℝ → ℝ → ℝ) :
    Work.Spaces.Dth (fun z θ => c * f z θ) = fun z θ => c * Work.Spaces.Dth f z θ := by
  funext z θ
  simp only [Work.Spaces.Dth, pth_const_mul]
  ring

private theorem DzIter_const_mul (c : ℝ) (f : ℝ → ℝ → ℝ) (i : ℕ) :
    Work.Spaces.DzIter i (fun z θ => c * f z θ) = fun z θ => c * Work.Spaces.DzIter i f z θ := by
  induction i with
  | zero => rfl
  | succ n ih => rw [Work.Spaces.DzIter_succ, Work.Spaces.DzIter_succ, ih, Dz_const_mul]

private theorem DthIter_const_mul (c : ℝ) (f : ℝ → ℝ → ℝ) (i : ℕ) :
    Work.Spaces.DthIter i (fun z θ => c * f z θ)
      = fun z θ => c * Work.Spaces.DthIter i f z θ := by
  induction i with
  | zero => rfl
  | succ n ih => rw [Work.Spaces.DthIter_succ, Work.Spaces.DthIter_succ, ih, Dth_const_mul]

private theorem mixed_const_mul (c : ℝ) (f : ℝ → ℝ → ℝ) (j i : ℕ) :
    Work.Spaces.mixed j i (fun z θ => c * f z θ)
      = fun z θ => c * Work.Spaces.mixed j i f z θ := by
  simp only [Work.Spaces.mixed, DthIter_const_mul, DzIter_const_mul]

/-- **The weighted `ℋ^k`-integrand is homogeneous of degree two in the amplitude:**
`HkIntegrand α k (c·f) z θ = c² · HkIntegrand α k f z θ`, for every `c : ℝ` and every `f`
(no regularity on `f` is needed). -/
theorem HkIntegrand_const_mul (α : ℝ) (k : ℕ) (c : ℝ) (f : ℝ → ℝ → ℝ) (z θ : ℝ) :
    Work.Spaces.HkIntegrand α k (fun z θ => c * f z θ) z θ
      = c ^ 2 * Work.Spaces.HkIntegrand α k f z θ := by
  rw [Work.Spaces.HkIntegrand, Work.Spaces.HkIntegrand, mul_add, Finset.mul_sum, Finset.mul_sum]
  congr 1
  · refine Finset.sum_congr rfl fun i _ => ?_
    rw [DzIter_const_mul]
    ring
  · refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [mixed_const_mul]
    split_ifs with h <;> ring

/-- **`ℋ^k` is closed under scalar multiplication.** If `f` is smooth on a neighbourhood of the
closed quadrant and in `ℋ^k`, then so is `c * f` for every `c : ℝ`.

Intended proof: for smooth `f` one has `DzIter i (c*f) = c * DzIter i f` and
`mixed j i (c*f) = c * mixed j i f`, whence `HkIntegrand α k (c*f) z θ = c^2 * HkIntegrand α k f z θ`
pointwise; the integral of `c^2 * ·` is `c^2 * ∫ ·`, giving the two membership clauses of `HkMem`. -/
theorem HkMem_const_mul {α : ℝ} {k : ℕ} (c : ℝ) {f : Work.FTS.Galerkin.Fn}
    (hf : Work.Spaces.SmoothNbhd f) (hmf : Work.Spaces.HkMem α k f) :
    Work.Spaces.HkMem α k (fun z θ => c * f z θ) := by
  obtain ⟨h1, h2⟩ := hmf
  constructor
  · -- the `θ`-slices of the integrand are integrable, being `c²` times the slices of `f`
    intro z hz
    have hfun : (fun θ => Work.Spaces.HkIntegrand α k (fun z θ => c * f z θ) z θ)
        = fun θ => c ^ 2 * Work.Spaces.HkIntegrand α k f z θ :=
      funext fun θ => HkIntegrand_const_mul α k c f z θ
    rw [hfun]
    exact (h1 z hz).const_mul _
  · -- the `z`-slices of the iterated integral are integrable, being `c²` times those of `f`
    have hfun : (fun z => ∫ θ in Work.Spaces.Iθ,
          Work.Spaces.HkIntegrand α k (fun z θ => c * f z θ) z θ)
        = fun z => c ^ 2 * ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k f z θ := by
      funext z
      rw [show (fun θ => Work.Spaces.HkIntegrand α k (fun z θ => c * f z θ) z θ)
            = fun θ => c ^ 2 * Work.Spaces.HkIntegrand α k f z θ from
          funext fun θ => HkIntegrand_const_mul α k c f z θ]
      rw [MeasureTheory.integral_const_mul]
    rw [hfun]
    exact h2.const_mul _

end

end Work.FTS.Galerkin.Hilbert
end
-- ===== merged: Submission.Work.FTS.Galerkin.Hilbert.sq_le_HkSq_two =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.Galerkin.Hilbert

set_option autoImplicit false
set_option maxHeartbeats 1000000

open Work.Spaces


end Work.FTS.Galerkin.Hilbert
end
end
-- ===== merged: Submission.Work.FTS.Galerkin.Inhabit.isDynEqOn_zero_alpha =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.Galerkin.Inhabit

/-!
## Inhabitation of the dynamic modulated equation at `α = 0`

Everything in the right hand side of the fake-time equation degenerates at `α = 0` for the
identically zero family: `Fstar 0 = 0`, `L₁₂` of the zero profile vanishes, the nonlinear terms
`N₀`, `N`, `N_*` vanish on `F = F_* + g = 0`, `Φ = 0`, `g = 0`, the modulation constants
`μ̄ = (1/2α)(…)`, `λ = -2μ̄/(1+μ̄)` and the singular part `Θ = (1/4α)sin(2θ)L₁₂(F)` are all
killed by the factors `1/α` (junk value `0` at `α = 0`), and the linear operator
`𝓛_Γ^T = 𝓛_Γ - 𝕡∘Transport` is zero on the zero profile.  The helper lemmas below record this
degeneration pointwise; the final theorem is then immediate.
-/





/-- `L₁₂` of the identically zero profile vanishes. -/
private theorem L12_zero : Work.Construction.L12 (fun _ _ => (0 : ℝ)) = fun _ => 0 := by
  funext z
  simp [Work.Construction.L12, Work.FM.L12, Work.FM.L12dens]













end Work.FTS.Galerkin.Inhabit
end
-- ===== merged: Submission.Work.FTS.Galerkin.Inhabit.regPkg_zero =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.Galerkin.Inhabit

set_option autoImplicit false

/-! ## The zero function under the operators of `ℋ^k`

All the weighted derivatives occurring in `Work.Spaces.HkIntegrand` are built from `∂_z`, `∂_θ`
and the multiplications by `z` resp. `sin (2θ)`; each of them maps the zero function to itself, so
the integrand of the zero function vanishes identically and the zero function lies in `ℋ^k`. -/

/-- `∂_z 0 = 0`. -/
private theorem pz_zeroF : Work.Spaces.pz (fun _ _ : ℝ => (0 : ℝ)) = fun _ _ => 0 := by
  funext z θ; simp [Work.Spaces.pz]

/-- `∂_θ 0 = 0`. -/
private theorem pth_zeroF : Work.Spaces.pth (fun _ _ : ℝ => (0 : ℝ)) = fun _ _ => 0 := by
  funext z θ; simp [Work.Spaces.pth]

/-- Every iterated `D_z`-derivative of the zero function vanishes. -/
private theorem DzIter_zeroF (i : ℕ) :
    Work.Spaces.DzIter i (fun _ _ : ℝ => (0 : ℝ)) = fun _ _ => 0 := by
  induction i with
  | zero => rfl
  | succ i ih =>
      rw [Work.Spaces.DzIter_succ, ih]
      funext z θ
      simp [Work.Spaces.Dz, pz_zeroF]

/-- Every iterated `D_θ`-derivative of the zero function vanishes. -/
private theorem DthIter_zeroF (i : ℕ) :
    Work.Spaces.DthIter i (fun _ _ : ℝ => (0 : ℝ)) = fun _ _ => 0 := by
  induction i with
  | zero => rfl
  | succ i ih =>
      rw [Work.Spaces.DthIter_succ, ih]
      funext z θ
      simp [Work.Spaces.Dth, pth_zeroF]

/-- Every mixed `D`-derivative of the zero function vanishes. -/
private theorem mixed_zeroF (j i : ℕ) :
    Work.Spaces.mixed j i (fun _ _ : ℝ => (0 : ℝ)) = fun _ _ => 0 := by
  simp only [Work.Spaces.mixed, DthIter_zeroF, DzIter_zeroF]

/-- The `ℋ^k`-integrand of the zero function vanishes identically. -/
theorem HkIntegrand_zeroF (α : ℝ) (k : ℕ) (z θ : ℝ) :
    Work.Spaces.HkIntegrand α k (fun _ _ : ℝ => (0 : ℝ)) z θ = 0 := by
  rw [Work.Spaces.HkIntegrand]
  simp [DzIter_zeroF, mixed_zeroF]

/-- The zero function lies in `ℋ^k` for every `k`: its integrand is the zero function, which is
integrable on every set. -/
theorem HkMem_zeroF (α : ℝ) (k : ℕ) : Work.Spaces.HkMem α k (fun _ _ : ℝ => (0 : ℝ)) := by
  constructor
  · intro z hz
    refine IntegrableOn.congr_fun integrableOn_zero (fun θ _ => ?_) measurableSet_Icc
    exact (HkIntegrand_zeroF α k z θ).symm
  · refine IntegrableOn.congr_fun integrableOn_zero (fun z _ => ?_) measurableSet_Ici
    rw [funext (fun θ => HkIntegrand_zeroF α k z θ), MeasureTheory.integral_zero]



end Work.FTS.Galerkin.Inhabit
end
end
