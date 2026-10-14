import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Basic.Real.Basic
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Order.CompletePartialOrder
import Mathlib.Order.Filter.Defs
import Mathlib.Tactic.IntervalCases
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Mathlib.Topology.Separation.CompletelyRegular
import Submission.Work.Coercivity.HkMem_mono
import Submission.Work.Coercivity.wip_L_self
import Submission.Work.FTS.EllipticEst.HarOp_pointwise_sq
import Submission.Work.FTS.EllipticEst.OpenFTC.absFtcLeIntegralAbsDeriv
import Submission.Work.FTS.EllipticEst.integrableOn_HkIntegrand_terms
import Submission.Work.FTS.EllipticEst.remov.slice_gprime_ident
import Submission.Work.FTS.H2.hard_sq_prod_z
import Submission.Work.FTS.PhiStar.Series.Weil.integrableOn_prod_mul
import Submission.Work.Spaces.HkSq_terms
import Submission.Work.Spaces.SmoothCompact_HkMem
import Submission.Work.Spaces.bt_integral_weight_id
import Submission.Work.Spaces.bt_prod_integrable
import Submission.Work.Spaces.factor_bound
import Submission.Work.Spaces.mixed_mul_le
import Submission.Work.Spaces.pz_DthIter_mul_eq
import Submission.Work.Spaces.sin_two_rpow
import Submission.Work.Spaces.sq_mul_div_rpow
import Submission.Work.Spaces.uncurry_partial_c1
-- ===== merged: Submission.Work.Coercivity.C0_sq_le_Ef =====
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


private lemma continuousOn_w_Ioi : ContinuousOn Spaces.w (Set.Ioi (0 : ℝ)) := by
  unfold Spaces.w
  exact ((continuous_const.add continuous_id).pow 2).continuousOn.div
    (continuous_id.pow 2).continuousOn (fun x hx => pow_ne_zero 2 (ne_of_gt hx))



end Work.Coercivity
end
end
-- ===== merged: Submission.Work.Coercivity.E2Slice.E2SliceDefs =====
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

/-! ## The model of the defect -/



/-- The *smooth part* of the defect `E₂`: `A(z,θ) = mm(z)·f(z,θ) + (3/2)·mm(z)·D_θ f(z,θ)`. -/
def E2smooth (f : ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ :=
  fun z θ => CommutZ.mm z * f z θ + (3 / 2) * (CommutZ.mm z * Spaces.Dth f z θ)

/-- The `Γ`-part of the defect: `(Γ(θ)/c(α))·Gfun f z`. -/
def E2gamma (α : ℝ) (f : ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ :=
  fun z θ => (CommutZ.Gfun f z / Spaces.c α) * Spaces.Gam α θ

/-- The model of the defect: `E2smooth f + E2gamma α f`. -/
def E2model (α : ℝ) (f : ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ :=
  fun z θ => E2smooth f z θ + E2gamma α f z θ

@[simp] theorem E2model_eq (α : ℝ) (f : ℝ → ℝ → ℝ) (z θ : ℝ) :
    E2model α f z θ = E2smooth f z θ + E2gamma α f z θ := rfl



/-! ## Smoothness of the smooth part on the box -/



/-! ## The `θ`-jets of the smooth part at the two endpoints -/



end Work.Coercivity
end
end
-- ===== merged: Submission.Work.Coercivity.H1IP_le_self =====
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
-- ===== merged: Submission.Work.Coercivity.HkAdm_dth =====
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

/-! ## `L₁₂(f)(0)` only depends on the values of `f` on the quadrant -/


/-- `H^k`-membership only depends on the values of the function on `(0,∞) × Iθ`: the
`H^k`-integrand is a local functional of the iterated derivatives, so it agrees at every
interior point of the quadrant, and on the null slice `z = 0` it vanishes identically
for every function. -/
theorem HkMem_congr_of_eqOn_Ioi (α : ℝ) (k : ℕ) {u v : ℝ → ℝ → ℝ}
    (hu : Spaces.HkMem α k u)
    (h : ∀ z ∈ Set.Ioi (0 : ℝ), ∀ θ ∈ Spaces.Iθ, u z θ = v z θ) :
    Spaces.HkMem α k v := by
  -- interior points of the quadrant: the integrands agree (local functional, `u = v`)
  have hpt : ∀ z ∈ Set.Ioi (0 : ℝ), ∀ θ ∈ Set.Ioo (0 : ℝ) (π / 2),
      Spaces.HkIntegrand α k u z θ = Spaces.HkIntegrand α k v z θ :=
    CommutZ_HkIntegrand_congr_pt α k u v h
  -- hence the `θ`-slices agree a.e. on `Iθ` (the two endpoints of `Iθ` are null)
  have hslice_eq : ∀ z ∈ Spaces.Iz,
      (fun θ => Spaces.HkIntegrand α k u z θ) =ᵐ[volume.restrict Spaces.Iθ]
        (fun θ => Spaces.HkIntegrand α k v z θ) := by
    intro z hz
    rcases eq_or_lt_of_le (Set.mem_Ici.mp hz) with hz0 | hz0
    · -- at `z = 0` both integrands vanish identically
      rw [← hz0]
      filter_upwards with θ
      simp only [Spaces.HkIntegrand_zero_z]
    · have hmeas : volume.restrict Spaces.Iθ
          = volume.restrict (Set.Ioo (0 : ℝ) (π / 2)) :=
        (MeasureTheory.Measure.restrict_congr_set MeasureTheory.Ioo_ae_eq_Icc).symm
      rw [hmeas]
      refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioo (fun θ hθ => ?_)
      exact hpt z hz0 θ hθ
  constructor
  · intro z hz
    exact Integrable.congr (hu.1 z hz) (hslice_eq z hz)
  · refine Integrable.congr hu.2 ?_
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ici] with z hz
    exact MeasureTheory.integral_congr_ae (hslice_eq z hz)

/-! ## The operator identities -/

/-- `D_θ^i (D_θ f) = D_θ^{i+1} f`, as functions. -/
theorem DthIter_Dth_eq (f : ℝ → ℝ → ℝ) (i : ℕ) :
    Spaces.DthIter i (Spaces.Dth f) = Spaces.DthIter (i + 1) f :=
  Spaces.DthIter_add_right i 1 f

/-- `D_z^b D_θ^a (D_θ f) = D_z^b D_θ^{a+1} f`, as functions. -/
theorem mixed_Dth_eq (f : ℝ → ℝ → ℝ) (b a : ℕ) :
    Spaces.mixed b a (Spaces.Dth f) = Spaces.mixed b (a + 1) f := by
  simp only [Spaces.mixed]
  rw [DthIter_Dth_eq]

/-- On the quadrant, `D_z^b D_θ^a (D_z f) = D_z^{b+1} D_θ^a f`: the operators `D_z` and
`D_θ` commute on the open set of `SmoothNbhd` (`Spaces.mixed_comm`).  Note that this is
an identity on the quadrant only; the two functions differ in general off it. -/
theorem mixed_Dz_eq {f : ℝ → ℝ → ℝ} (hf : Spaces.SmoothNbhd f) (b a : ℕ) {z θ : ℝ}
    (hz : z ∈ Spaces.Iz) (hθ : θ ∈ Spaces.Iθ) :
    Spaces.mixed b a (Spaces.Dz f) z θ = Spaces.mixed (b + 1) a f z θ := by
  have h := Spaces.mixed_comm f hf b a 1 0 z θ hz hθ
  simpa only [Spaces.mixed_zero_right, Spaces.DzIter_succ, Spaces.DzIter_zero,
    Nat.add_zero] using h


/-! ## The closure of `HkAdm` under `D_θ` and `D_z` -/


end Work.Coercivity
end
end
-- ===== merged: Submission.Work.Coercivity.HkIntegrand_EcommT_le_Bound =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology ContDiff
open MeasureTheory Set Filter

namespace Work.Coercivity

set_option autoImplicit false

/-! ## Elementary helpers -/

/-- `sin(2θ) > 0` on the open angular interval. -/
lemma sin_two_pos_of_mem_Ioo {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (π / 2)) :
    0 < Real.sin (2 * θ) :=
  Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1, Real.pi_pos])
    (by linarith [hθ.2, Real.pi_pos])

/-- `Γ(θ) = (sinθ cos²θ)^{α/3}` is `C^∞` on `(0,π/2)`. -/
lemma contDiffOn_Gam (α : ℝ) : ContDiffOn ℝ ⊤ (Spaces.Gam α) (Set.Ioo 0 (π / 2)) := by
  unfold Spaces.Gam
  apply ContDiffOn.rpow
  · fun_prop
  · fun_prop
  · intro θ hθ
    have hs : 0 < Real.sin θ :=
      Real.sin_pos_of_pos_of_lt_pi hθ.1 (by linarith [hθ.2, Real.pi_pos])
    have hc : 0 < Real.cos θ :=
      Real.cos_pos_of_mem_Ioo ⟨by linarith [hθ.1, Real.pi_pos],
        by linarith [hθ.2, Real.pi_pos]⟩
    positivity






/-! ## Transfer of iterated derivatives across a local equality -/



/-! ## The algebraic core -/


/-! ## `C^∞`-regularity of the radial factors and the main theorem -/





end Work.Coercivity
end
end
-- ===== merged: Submission.Work.Coercivity.HkMem_terms =====
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

/-! ## The elementary `rpow` identity and the pointwise extraction -/

/-- `(x^{-e/2})² = x^{-e}` for `x ≥ 0`.  Both sides vanish at `x = 0` when `e ≠ 0`, and
are `1` when `e = 0`; the statement is uniform in `e`. -/
private lemma rpow_neg_half_sq {s e : ℝ} (hs : 0 ≤ s) : (s ^ (-(e / 2))) ^ 2 = s ^ (-e) := by
  rw [← Real.rpow_natCast (s ^ (-(e / 2))) 2, ← Real.rpow_mul hs (-(e / 2)) ((2 : ℕ) : ℝ)]
  congr 1
  push_cast
  ring






/-! ## The four conclusions -/


end Work.Coercivity
end
end
-- ===== merged: Submission.Work.Coercivity.KC1_eq_double =====
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
-- ===== merged: Submission.Work.Coercivity.L12_w_sq_le =====
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
-- ===== merged: Submission.Work.Coercivity.L12f_w_hardy =====
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


end Work.Coercivity
end
end
-- ===== merged: Submission.Work.Coercivity.L2Mem_Xw =====
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

/-! ## The elementary comparison -/

/-- For `0 < t ≤ 1` and any `a`, dividing by `t` does not decrease the square:
`a ^ 2 ≤ (a / t) ^ 2`. -/
private lemma sq_le_div_sq {a t : ℝ} (ht0 : 0 < t) (ht1 : t ≤ 1) : a ^ 2 ≤ (a / t) ^ 2 := by
  have ht2 : 0 < t ^ 2 := pow_pos ht0 2
  have ht2le : t ^ 2 ≤ 1 := by nlinarith [ht0, ht1]
  rw [div_pow, le_div_iff₀ ht2]
  simpa using mul_le_mul_of_nonneg_left ht2le (sq_nonneg a)

/-! ## Continuity of the integrand on the open quadrant -/

/-- The open quadrant `(0,∞) × (0,π/2)`. -/
private def Qd : Set (ℝ × ℝ) := Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)

private lemma Qd_subset_nbhU : Qd ⊆ Spaces.nbhU := by
  rintro ⟨z, θ⟩ ⟨hz, hθ⟩
  exact Spaces.mem_nbhU (Set.mem_Ici.mpr (le_of_lt hz))
    (Set.mem_Icc.mpr ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩)



/-! ## The a.e. comparison with the `H¹`-integrand -/

/-- Off the two null endpoints of `Iθ`, `(f · w)²` is bounded by the `H¹`-integrand,
because the `D_z⁰`-summand of the latter is `(f · w / sin(2θ)^{η/2})²` and
`0 < sin(2θ) ≤ 1` there. -/
private lemma sq_Xw_le_HkIntegrand_ae (α : ℝ) (f : ℝ → ℝ → ℝ) (z : ℝ) :
    ∀ᵐ θ ∂(volume.restrict Spaces.Iθ),
      (Xw f z θ) ^ 2 ≤ Spaces.HkIntegrand α 1 f z θ := by
  have hmeas : volume.restrict (Set.Ioo 0 (π / 2)) = volume.restrict Spaces.Iθ :=
    Measure.restrict_congr_set MeasureTheory.Ioo_ae_eq_Icc
  rw [← hmeas]
  filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioo] with θ hθ
  have hs0 : 0 < Real.sin (2 * θ) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])
  have hs1 : Real.sin (2 * θ) ≤ 1 := Real.sin_le_one _
  have ht0 : 0 < (Real.sin (2 * θ)) ^ (Spaces.eta / 2) := Real.rpow_pos_of_pos hs0 _
  have ht1 : (Real.sin (2 * θ)) ^ (Spaces.eta / 2) ≤ 1 := by
    calc (Real.sin (2 * θ)) ^ (Spaces.eta / 2)
        ≤ (1 : ℝ) ^ (Spaces.eta / 2) := Real.rpow_le_rpow (le_of_lt hs0) hs1
          (div_nonneg (le_of_lt Spaces.eta_pos) (by norm_num))
      _ = 1 := by simp
  have hkey : (f z θ * Spaces.w z) ^ 2
      ≤ ((f z θ * Spaces.w z) / (Real.sin (2 * θ)) ^ (Spaces.eta / 2)) ^ 2 :=
    sq_le_div_sq ht0 ht1
  have hterm : (Xw f z θ) ^ 2
      ≤ (Spaces.DzIter 0 f z θ
          * (Spaces.w z / (Real.sin (2 * θ)) ^ (Spaces.eta / 2))) ^ 2 := by
    simp only [Xw, Spaces.DzIter_zero]
    rw [← mul_div_assoc]
    exact hkey
  exact le_trans hterm (Spaces.sq_le_HkIntegrand_z α 1 f z θ 0 (by norm_num))

/-! ## The main statement -/


end Work.Coercivity
end
end
-- ===== merged: Submission.Work.Coercivity.aesm_blocks =====
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

/-! ## The weights of the four blocks -/

/-- The radial–angular weight `w(z)/sin(2θ)^{η/2}` multiplying the two `η`-blocks. -/
private def Weta_prv (z θ : ℝ) : ℝ := Spaces.w z / (Real.sin (2 * θ)) ^ (Spaces.eta / 2)



/-! ## The open quadrant lies in the neighbourhood on which `SmoothNbhd` is stated -/


/-- `sin (2θ) > 0` for `θ ∈ (0,π/2)`. -/
private lemma sin_two_pos_of_mem {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (π / 2)) : 0 < Real.sin (2 * θ) := by
  apply Real.sin_pos_of_pos_of_lt_pi
  · linarith [hθ.1]
  · linarith [hθ.2, Real.pi_pos]

/-! ## Continuity on the open quadrant -/












/-! ## Continuity of the slices on the open interval `(0,π/2)` -/










/-! ## The open interval `(0,π/2)` is co-null in `Iθ` -/

lemma restrict_Ioo_eq_restrict_Iθ :
    volume.restrict (Set.Ioo (0 : ℝ) (π / 2)) = volume.restrict Spaces.Iθ := by
  apply Measure.restrict_congr_set
  rw [Spaces.Iθ]
  exact MeasureTheory.Ioo_ae_eq_Icc

/-! ## From continuity to a.e. strong measurability -/


end Work.Coercivity

namespace Work.Coercivity


end Work.Coercivity
end
end
-- ===== merged: Submission.Work.Coercivity.dth_slice_theta_ibp =====
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

/-! ## Pointwise `rpow` algebra

`D_θ g = sin(2θ) · ∂_θ g`, so every `D_θ`-factor contributes a `sin(2θ)` which cancels
one unit of the negative exponent `-(gam α)`.  These identities are the algebraic
content of both the boundary vanishing and the integrability. -/




/-! ## Continuity of the angular slices of `∂_θ f` -/


/-! ## Vanishing of the boundary term `sin(2θ)^{-(γ-1)}·(D_θ f)²` at the two endpoints -/



/-! ## Integrability of the two angular integrands -/

private theorem sin_two_nonneg_of_Iθ {θ : ℝ} (hθ : θ ∈ Spaces.Iθ) : 0 ≤ Real.sin (2 * θ) :=
  Real.sin_nonneg_of_mem_Icc ⟨by linarith [hθ.1], by linarith [hθ.2, Real.pi_pos]⟩



/-! ## The angular integration by parts for `D_θ f` -/


end Work.Coercivity
end
end
-- ===== merged: Submission.Work.Coercivity.dth_slice_z_ibp =====
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

/-! ## The pointwise identity `𝓛u · u · w² = (u w)² + ½ z ∂_z((u w)²)` -/



/-! ## The derivative of the boundary term `G(z) = z (u w)²` -/




/-! ## The finite-interval integration by parts -/


end Work.Coercivity
end
end
-- ===== merged: Submission.Work.Coercivity.wip_Aop_ge =====
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


theorem wip_add_left {ρ g h k : ℝ → ℝ → ℝ}
    (hg : IntegrableOn (Function.uncurry (fun z θ => g z θ * k z θ * ρ z θ)) (Spaces.Iz ×ˢ Spaces.Iθ))
    (hh : IntegrableOn (Function.uncurry (fun z θ => h z θ * k z θ * ρ z θ)) (Spaces.Iz ×ˢ Spaces.Iθ)) :
    wip ρ (fun z θ => g z θ + h z θ) k = wip ρ g k + wip ρ h k := by
  have hvol : MeasureTheory.volume.restrict (Spaces.Iz ×ˢ Spaces.Iθ)
      = (MeasureTheory.volume.restrict Spaces.Iz).prod (MeasureTheory.volume.restrict Spaces.Iθ) := by
    rw [MeasureTheory.Measure.volume_eq_prod]
    exact (MeasureTheory.Measure.prod_restrict _ _).symm
  have hG : MeasureTheory.Integrable
      (fun p : ℝ × ℝ => g p.1 p.2 * k p.1 p.2 * ρ p.1 p.2)
      ((MeasureTheory.volume.restrict Spaces.Iz).prod (MeasureTheory.volume.restrict Spaces.Iθ)) := by
    rw [← hvol]; exact hg
  have hH : MeasureTheory.Integrable
      (fun p : ℝ × ℝ => h p.1 p.2 * k p.1 p.2 * ρ p.1 p.2)
      ((MeasureTheory.volume.restrict Spaces.Iz).prod (MeasureTheory.volume.restrict Spaces.Iθ)) := by
    rw [← hvol]; exact hh
  have hGH : MeasureTheory.Integrable
      (fun p : ℝ × ℝ => (g p.1 p.2 + h p.1 p.2) * k p.1 p.2 * ρ p.1 p.2)
      ((MeasureTheory.volume.restrict Spaces.Iz).prod (MeasureTheory.volume.restrict Spaces.Iθ)) := by
    refine (hG.add hH).congr ?_
    filter_upwards with p
    simp only [Pi.add_apply]
    ring
  have hGHo : IntegrableOn
      (Function.uncurry (fun z θ => (g z θ + h z θ) * k z θ * ρ z θ)) (Spaces.Iz ×ˢ Spaces.Iθ) := by
    unfold MeasureTheory.IntegrableOn
    rw [hvol]; exact hGH
  rw [wip_eq_integral_prod ρ (fun z θ => g z θ + h z θ) k hGHo,
      wip_eq_integral_prod ρ g k hg, wip_eq_integral_prod ρ h k hh,
      ← MeasureTheory.integral_add hG hH]
  apply MeasureTheory.integral_congr_ae
  filter_upwards with p
  ring


end Work.Coercivity
end
end
-- ===== merged: Submission.Work.Construction.H4N_GammaTerm_rho_bound =====
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

/-! ## The five cases `j = 0,1,2,3,4`

For `z = 0` the weight `w` vanishes (`w 0 = 0`), so the bound is trivial; for `z > 0`
we substitute the closed form of the iterate and reduce to the polynomial bound of
`H4N_rhoR_numbound`. -/

private lemma rhoR_w_bound_0 :
    ∀ z : ℝ, 0 ≤ z → |(Work.Spaces.Zop^[0] rhoR) z * Work.Spaces.w z| ≤ 840 / (1 + z) ^ 2 := by
  intro z hz
  rcases eq_or_lt_of_le hz with h0 | hpos
  · subst h0
    rw [Function.iterate_zero_apply]
    norm_num [rhoR, Work.Spaces.w]
  · have h1z : (0 : ℝ) < 1 + z := by linarith
    rw [Function.iterate_zero_apply, show rhoR = (fun z : ℝ => z^2/(1+z)^4) from rfl,
      Work.Spaces.w]
    have key : (z^2/(1+z)^4) * ((1+z)^2/z^2) = 1/(1+z)^2 := by field_simp
    rw [key, abs_of_pos (by positivity : (0:ℝ) < 1/(1+z)^2)]
    gcongr
    norm_num

private lemma rhoR_w_bound_1 :
    ∀ z : ℝ, 0 ≤ z → |(Work.Spaces.Zop^[1] rhoR) z * Work.Spaces.w z| ≤ 840 / (1 + z) ^ 2 := by
  intro z hz
  rcases eq_or_lt_of_le hz with h0 | hpos
  · subst h0
    rw [H4N_rhoR_shape12.1 0 (by norm_num)]
    norm_num [Work.Spaces.w]
  · have hz0 : z ≠ 0 := ne_of_gt hpos
    have h1z : (0 : ℝ) < 1 + z := by linarith
    rw [H4N_rhoR_shape12.1 z (by linarith), Work.Spaces.w]
    have key : (z^2*(2-2*z)/(1+z)^5) * ((1+z)^2/z^2) = (2-2*z)/(1+z)^3 := by field_simp
    rw [key, abs_div, abs_of_pos (by positivity : (0:ℝ) < (1+z)^3)]
    have key2 : |2 - 2*z| / (1+z)^3 = (|2 - 2*z|/(1+z))/(1+z)^2 := by field_simp
    rw [key2]
    apply div_le_div_of_nonneg_right _ (by positivity)
    rw [div_le_iff₀ h1z]
    linarith [H4N_rhoR_numbound.2.1 z hz]

private lemma rhoR_w_bound_2 :
    ∀ z : ℝ, 0 ≤ z → |(Work.Spaces.Zop^[2] rhoR) z * Work.Spaces.w z| ≤ 840 / (1 + z) ^ 2 := by
  intro z hz
  rcases eq_or_lt_of_le hz with h0 | hpos
  · subst h0
    rw [H4N_rhoR_shape12.2 0 (by norm_num)]
    norm_num [Work.Spaces.w]
  · have hz0 : z ≠ 0 := ne_of_gt hpos
    have h1z : (0 : ℝ) < 1 + z := by linarith
    rw [H4N_rhoR_shape12.2 z (by linarith), Work.Spaces.w]
    have key : (z^2*(4-12*z+4*z^2)/(1+z)^6) * ((1+z)^2/z^2)
        = (4-12*z+4*z^2)/(1+z)^4 := by field_simp
    rw [key, abs_div, abs_of_pos (by positivity : (0:ℝ) < (1+z)^4)]
    have key2 : |4 - 12*z + 4*z^2| / (1+z)^4
        = (|4 - 12*z + 4*z^2|/(1+z)^2)/(1+z)^2 := by field_simp
    rw [key2]
    apply div_le_div_of_nonneg_right _ (by positivity)
    rw [div_le_iff₀ (by positivity : (0:ℝ) < (1+z)^2)]
    linarith [H4N_rhoR_numbound.2.2.1 z hz]

private lemma rhoR_w_bound_3 :
    ∀ z : ℝ, 0 ≤ z → |(Work.Spaces.Zop^[3] rhoR) z * Work.Spaces.w z| ≤ 840 / (1 + z) ^ 2 := by
  intro z hz
  rcases eq_or_lt_of_le hz with h0 | hpos
  · subst h0
    rw [H4N_rhoR_shape3 0 (by norm_num)]
    norm_num [Work.Spaces.w]
  · have hz0 : z ≠ 0 := ne_of_gt hpos
    have h1z : (0 : ℝ) < 1 + z := by linarith
    rw [H4N_rhoR_shape3 z (by linarith), Work.Spaces.w]
    have key : (z^2*(8-52*z+52*z^2-8*z^3)/(1+z)^7) * ((1+z)^2/z^2)
        = (8-52*z+52*z^2-8*z^3)/(1+z)^5 := by field_simp
    rw [key, abs_div, abs_of_pos (by positivity : (0:ℝ) < (1+z)^5)]
    have key2 : |8 - 52*z + 52*z^2 - 8*z^3| / (1+z)^5
        = (|8 - 52*z + 52*z^2 - 8*z^3|/(1+z)^3)/(1+z)^2 := by field_simp
    rw [key2]
    apply div_le_div_of_nonneg_right _ (by positivity)
    rw [div_le_iff₀ (by positivity : (0:ℝ) < (1+z)^3)]
    linarith [H4N_rhoR_numbound.2.2.2.1 z hz]

private lemma rhoR_w_bound_4 :
    ∀ z : ℝ, 0 ≤ z → |(Work.Spaces.Zop^[4] rhoR) z * Work.Spaces.w z| ≤ 840 / (1 + z) ^ 2 := by
  intro z hz
  rcases eq_or_lt_of_le hz with h0 | hpos
  · subst h0
    rw [H4N_rhoR_shape4 0 (by norm_num)]
    norm_num [Work.Spaces.w]
  · have hz0 : z ≠ 0 := ne_of_gt hpos
    have h1z : (0 : ℝ) < 1 + z := by linarith
    rw [H4N_rhoR_shape4 z (by linarith), Work.Spaces.w]
    have key : (z^2*(16-196*z+416*z^2-196*z^3+16*z^4)/(1+z)^8) * ((1+z)^2/z^2)
        = (16-196*z+416*z^2-196*z^3+16*z^4)/(1+z)^6 := by field_simp
    rw [key, abs_div, abs_of_pos (by positivity : (0:ℝ) < (1+z)^6)]
    have key2 : |16 - 196*z + 416*z^2 - 196*z^3 + 16*z^4| / (1+z)^6
        = (|16 - 196*z + 416*z^2 - 196*z^3 + 16*z^4|/(1+z)^4)/(1+z)^2 := by field_simp
    rw [key2]
    apply div_le_div_of_nonneg_right _ (by positivity)
    rw [div_le_iff₀ (by positivity : (0:ℝ) < (1+z)^4)]
    linarith [H4N_rhoR_numbound.2.2.2.2 z hz]

/-! ## The stated bound -/

theorem H4N_GammaTerm_rho_bound :
    ∃ M : ℝ, 0 < M ∧ ∀ j : ℕ, j ≤ 4 → ∀ z : ℝ, 0 ≤ z →
      |(Work.Spaces.Zop^[j] Work.Construction.rhoR) z * Work.Spaces.w z| ≤ M / (1 + z) ^ 2 := by
  refine ⟨840, by norm_num, ?_⟩
  intro j hj z hz
  interval_cases j
  · exact rhoR_w_bound_0 z hz
  · exact rhoR_w_bound_1 z hz
  · exact rhoR_w_bound_2 z hz
  · exact rhoR_w_bound_3 z hz
  · exact rhoR_w_bound_4 z hz

end Work.Construction
end
end
-- ===== merged: Submission.Work.Elliptic.L12Iterate =====
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
set_option maxHeartbeats 800000

/-- `SmoothNbhd` is inherited by the iterated `D_z`-derivatives. -/
lemma smoothNbhd_DzIter {g : ℝ → ℝ → ℝ} (hsm : Work.Spaces.SmoothNbhd g) (j : ℕ) :
    Work.Spaces.SmoothNbhd (Work.Spaces.DzIter j g) := by
  simpa [Work.Spaces.SmoothNbhd, Work.Spaces.nbhU] using contDiffOn_uncurry_DzIter_nbhU hsm j



end Work.Elliptic
end
end
-- ===== merged: Submission.Work.Elliptic.L12k0 =====
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

/-- The two halves of the split of the half-line: `(0,1) ∪ (1,∞)` agrees with `[0,∞)` up to
the null set `{0,1}`. -/
lemma Ioo_union_Ioi_ae_eq_Iz : (Set.Ioo (0:ℝ) 1 ∪ Set.Ioi 1) =ᵐ[volume] Work.Spaces.Iz := by
  have hsing : ∀ s : Set ℝ, ∀ a : ℝ, s \ {a} =ᵐ[volume] s :=
    fun s a => MeasureTheory.sdiff_null_ae_eq_self (MeasureTheory.measure_singleton (a))
  have e1 : Set.Ioo (0:ℝ) 1 ∪ Set.Ioi 1 = Set.Ioi (0:ℝ) \ {1} := by
    ext z
    simp only [Set.mem_union, Set.mem_Ioo, Set.mem_Ioi, Set.mem_sdiff, Set.mem_singleton_iff]
    constructor
    · rintro (⟨hz1, hz2⟩ | hz1)
      · exact ⟨hz1, ne_of_lt hz2⟩
      · exact ⟨lt_trans one_pos hz1, ne_of_gt hz1⟩
    · rintro ⟨hz1, hz2⟩
      rcases lt_trichotomy z 1 with h | h | h
      · exact Or.inl ⟨hz1, h⟩
      · exact absurd h hz2
      · exact Or.inr h
  have e2 : Set.Ici (0:ℝ) \ {0} = Set.Ioi (0:ℝ) := by
    ext z
    simp only [Set.mem_sdiff, Set.mem_singleton_iff, Set.mem_Ici, Set.mem_Ioi]
    exact ⟨fun h => lt_of_le_of_ne h.1 (Ne.symm h.2), fun h => ⟨le_of_lt h, ne_of_gt h⟩⟩
  have hIoIci : Set.Ioi (0:ℝ) =ᵐ[volume] Set.Ici 0 := by
    rw [← e2]; exact hsing (Set.Ici (0:ℝ)) 0
  rw [e1]
  exact (hsing (Set.Ioi (0:ℝ)) 1).trans (hIoIci.trans (by rfl))


end Work.Elliptic
end
end
-- ===== merged: Submission.Work.FTS.CoercivityStep.Norm.HkAdm_mono =====
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

/-- **`HkMem` descends in the order.**  For a function `g` smooth on a neighbourhood of
the closed quadrant, membership `HkMem α l g` at order `l` implies membership
`HkMem α k g` at every lower order `k ≤ l`.

This is the iteration of the one-step monotonicity `Work.Coercivity.HkMem_mono`
(`HkMem α (m+1) g → HkMem α m g`), which is available because `g` is smooth. -/
theorem HkMem_descend (α : ℝ) {g : ℝ → ℝ → ℝ} (hsm : Work.Spaces.SmoothNbhd g) :
    ∀ {k l : ℕ}, k ≤ l → Work.Spaces.HkMem α l g → Work.Spaces.HkMem α k g := by
  intro k l
  induction l with
  | zero =>
      intro hkl h
      have hk : k = 0 := Nat.eq_zero_of_le_zero hkl
      subst hk
      exact h
  | succ m ih =>
      intro hkl h
      rcases eq_or_lt_of_le hkl with h_eq | h_lt
      · subst h_eq
        exact h
      · exact ih (Nat.lt_succ_iff.mp h_lt) (Work.Coercivity.HkMem_mono α m hsm h)

/-- **`HkAdm` is monotone in the order.**  A function admissible at order `l` is
admissible at every lower order `k ≤ l`. -/
theorem HkAdm_mono (α : ℝ) {k l : ℕ} (hkl : k ≤ l) {f : ℝ → ℝ → ℝ}
    (h : Work.Coercivity.HkAdm α l f) : Work.Coercivity.HkAdm α k f := by
  obtain ⟨hsm, hmem, hL12⟩ := h
  refine ⟨hsm, ?_, ?_⟩
  · -- membership of every lower mixed derivative, handed down from order `l`
    intro a b hab
    have hsmab : Work.Spaces.SmoothNbhd (Work.Spaces.mixed b a f) :=
      Work.Spaces.SmoothNbhd.DzIter (Work.Spaces.SmoothNbhd.DthIter hsm a) b
    exact HkMem_descend α hsmab hkl (hmem a b (le_trans hab hkl))
  · -- the `L₁₂`-zero-mode clause does not mention `k`
    intro a b hab
    exact hL12 a b (le_trans hab hkl)

end Work.FTS.CoercivityStep.Norm
end
end
-- ===== merged: Submission.Work.FTS.CoercivityStep.Norm.HkMem_const_mul =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `ℋ^k` is closed under scalar multiplication

`Work.Spaces.HkMem α k f` says that the weighted `H^k`-integrand of `f` has honest
iterated integrals over `[0,∞) × [0,π/2]`.  Here we prove that the class is closed under
`f ↦ c · f` for every `c : ℝ`.

The point is that every weighted derivative appearing in `Work.Spaces.HkIntegrand` is
`ℝ`-linear in `f` (`D_z^i` and `D_z^j D_θ^i` are built from `deriv`, which is scalar
homogeneous *unconditionally*, see `deriv_const_mul_field`), so that

  `HkIntegrand α k (c·f) z θ = c^2 * HkIntegrand α k f z θ`.

Both membership clauses are then immediate from the corresponding clauses for `f`
(pulling `c^2` out of the angular integral with `MeasureTheory.integral_const_mul`).

In particular no smoothness hypothesis is needed for this statement; the `SmoothNbhd`
hypothesis of the requested signature is simply not used.
-/

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.CoercivityStep.Norm

set_option autoImplicit false

/-! ## Scalar homogeneity of the weighted derivatives -/

/-- `∂_z` is scalar homogeneous: unconditional, since `deriv` is. -/
private theorem pz_const_mul (c : ℝ) (f : ℝ → ℝ → ℝ) :
    Work.Spaces.pz (fun z θ => c * f z θ) = fun z θ => c * Work.Spaces.pz f z θ := by
  funext z θ
  simp only [Work.Spaces.pz]
  exact deriv_const_mul_field c

/-- `∂_θ` is scalar homogeneous. -/
private theorem pth_const_mul (c : ℝ) (f : ℝ → ℝ → ℝ) :
    Work.Spaces.pth (fun z θ => c * f z θ) = fun z θ => c * Work.Spaces.pth f z θ := by
  funext z θ
  simp only [Work.Spaces.pth]
  exact deriv_const_mul_field c

/-- `D_z = z ∂_z` is scalar homogeneous. -/
private theorem Dz_const_mul (c : ℝ) (f : ℝ → ℝ → ℝ) :
    Work.Spaces.Dz (fun z θ => c * f z θ) = fun z θ => c * Work.Spaces.Dz f z θ := by
  funext z θ
  simp only [Work.Spaces.Dz, pz_const_mul]
  ring

/-- `D_θ = sin(2θ) ∂_θ` is scalar homogeneous. -/
private theorem Dth_const_mul (c : ℝ) (f : ℝ → ℝ → ℝ) :
    Work.Spaces.Dth (fun z θ => c * f z θ) = fun z θ => c * Work.Spaces.Dth f z θ := by
  funext z θ
  simp only [Work.Spaces.Dth, pth_const_mul]
  ring

/-- Iterated `D_z` is scalar homogeneous. -/
private theorem DzIter_const_mul (c : ℝ) (j : ℕ) (f : ℝ → ℝ → ℝ) :
    Work.Spaces.DzIter j (fun z θ => c * f z θ)
      = fun z θ => c * Work.Spaces.DzIter j f z θ := by
  induction j with
  | zero => rfl
  | succ n ih => simp only [Work.Spaces.DzIter_succ, ih, Dz_const_mul]

/-- Iterated `D_θ` is scalar homogeneous. -/
private theorem DthIter_const_mul (c : ℝ) (i : ℕ) (f : ℝ → ℝ → ℝ) :
    Work.Spaces.DthIter i (fun z θ => c * f z θ)
      = fun z θ => c * Work.Spaces.DthIter i f z θ := by
  induction i with
  | zero => rfl
  | succ n ih => simp only [Work.Spaces.DthIter_succ, ih, Dth_const_mul]

/-- The mixed derivative `D_z^j D_θ^i` is scalar homogeneous. -/
private theorem mixed_const_mul (c : ℝ) (j i : ℕ) (f : ℝ → ℝ → ℝ) :
    Work.Spaces.mixed j i (fun z θ => c * f z θ)
      = fun z θ => c * Work.Spaces.mixed j i f z θ := by
  simp only [Work.Spaces.mixed, DthIter_const_mul, DzIter_const_mul]

/-! ## Homogeneity of the weighted `H^k`-integrand -/

/-- The weighted `H^k`-integrand is homogeneous of degree `2` in the amplitude. -/
private theorem HkIntegrand_const_mul (A : ℝ) (c : ℝ) (k : ℕ) (f : ℝ → ℝ → ℝ) (z θ : ℝ) :
    Work.Spaces.HkIntegrand A k (fun z θ => c * f z θ) z θ
      = c ^ 2 * Work.Spaces.HkIntegrand A k f z θ := by
  rw [Work.Spaces.HkIntegrand, Work.Spaces.HkIntegrand]
  have h1 : (∑ i ∈ Finset.range (k + 1),
        (Work.Spaces.DzIter i (fun z θ => c * f z θ) z θ
          * (Work.Spaces.w z / Real.sin (2 * θ) ^ (Work.Spaces.eta / 2))) ^ 2)
      = c ^ 2 * ∑ i ∈ Finset.range (k + 1),
        (Work.Spaces.DzIter i f z θ
          * (Work.Spaces.w z / Real.sin (2 * θ) ^ (Work.Spaces.eta / 2))) ^ 2 := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [DzIter_const_mul]
    ring
  have h2 : (∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1),
        if 1 ≤ i ∧ i + j ≤ k
          then (Work.Spaces.mixed j i (fun z θ => c * f z θ) z θ * Work.Spaces.Wt A z θ) ^ 2
          else 0)
      = c ^ 2 * ∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1),
        if 1 ≤ i ∧ i + j ≤ k
          then (Work.Spaces.mixed j i f z θ * Work.Spaces.Wt A z θ) ^ 2 else 0 := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    by_cases h : 1 ≤ i ∧ i + j ≤ k
    · rw [ite_eq_left h, ite_eq_left h, mixed_const_mul]
      ring
    · rw [ite_eq_right h, ite_eq_right h, mul_zero]
  rw [h1, h2]
  ring

/-! ## Closure of `ℋ^k` under scalar multiplication -/

theorem HkMem_const_mul (α : ℝ) (k : ℕ) (c : ℝ) {f : ℝ → ℝ → ℝ} (hf : Work.Spaces.SmoothNbhd f)
    (hmf : Work.Spaces.HkMem α k f) :
    Work.Spaces.HkMem α k (fun z θ => c * f z θ) := by
  -- the smoothness of `f` is not needed: `deriv` is scalar homogeneous unconditionally
  have _hf : Work.Spaces.SmoothNbhd f := hf
  refine ⟨fun z hz => ?_, ?_⟩
  · -- angular slice: pull the constant `c^2` out of the integrand
    have h := (hmf.1 z hz).const_mul (c ^ 2)
    simpa only [HkIntegrand_const_mul, IntegrableOn] using h
  · -- radial integral: the inner integral is `c^2` times the inner integral for `f`
    have h := (hmf.2).const_mul (c ^ 2)
    simpa only [HkIntegrand_const_mul, integral_const_mul, IntegrableOn] using h

end Work.FTS.CoercivityStep.Norm
end
end
-- ===== merged: Submission.Work.FTS.CoercivityStep.Norm.HkMem_of_add_dominated =====
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


end Work.FTS.CoercivityStep.Norm
end
end
-- ===== merged: Submission.Work.FTS.EllipticEst.AngClean.I4_lower_bound_slice =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.AngClean

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

open Work.FTS.EllipticEst.AngSecond
open Work.Spaces

/-! ## Integrability of the angular weight and of bounded functions against it -/

/-- `σ ∈ L¹(Iθ)`, from `Work.Spaces.sin_two_rpow` with `p = -η ∈ (-1, 0]`. -/
theorem integrableOn_sig : IntegrableOn sig Iθ := by
  have h : IntegrableOn (fun θ : ℝ => Real.sin (2 * θ) ^ (-(Work.Spaces.eta))) Iθ volume :=
    (Work.Spaces.sin_two_rpow (-(Work.Spaces.eta))
      (by linarith [Work.Spaces.eta_lt_one])
      (by linarith [Work.Spaces.eta_pos])).1
  exact h

/-- `σ` is measurable. -/
theorem measurable_sig : Measurable sig := by
  show Measurable (fun θ : ℝ => (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))
  exact (Real.measurable_sin.comp (measurable_const.mul measurable_id)).pow_const _



/-! ## The slicewise inequality without the `Ψ/cos θ`-honesty hypotheses -/



end Work.FTS.EllipticEst.AngClean
end
end
-- ===== merged: Submission.Work.FTS.EllipticEst.H2W.Lzb.WronDerivs =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open scoped Real Topology
open Filter

namespace Work.FTS.EllipticEst.H2W.Lzb

/-! ## Elementary derivative facts used below -/




/-- The product rule for `θ ↦ tan θ * f θ` at a point where `cos θ ≠ 0`. -/
private theorem deriv_tan_mul {f : ℝ → ℝ} {θ : ℝ} (hc : Real.cos θ ≠ 0)
    (hf : HasDerivAt f (deriv f θ) θ) :
    deriv (fun t : ℝ => Real.tan t * f t) θ
      = deriv Real.tan θ * f θ + Real.tan θ * deriv f θ := by
  have h := ((Real.hasDerivAt_tan hc).mul hf).deriv
  rw [Real.deriv_tan]
  exact h

private theorem sin_two_hasDerivAt (t : ℝ) :
    HasDerivAt (fun s : ℝ => Real.sin (2 * s)) (2 * Real.cos (2 * t)) t := by
  have h2 : HasDerivAt (fun s : ℝ => (2 : ℝ) * s) 2 t := by
    simpa only [id_eq, mul_one] using (hasDerivAt_id t).const_mul (2 : ℝ)
  exact ((Real.hasDerivAt_sin (2 * t)).comp t h2).congr_deriv (by ring)


private theorem deriv_sin_two :
    deriv (fun s : ℝ => Real.sin (2 * s)) = fun s => 2 * Real.cos (2 * s) :=
  funext fun s => (sin_two_hasDerivAt s).deriv




end Work.FTS.EllipticEst.H2W.Lzb
end
-- ===== merged: Submission.Work.FTS.EllipticEst.H2W.lzeroGrowthSlice =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.H2W

set_option autoImplicit false

namespace LzeroGrowth

/-! ## The two auxiliary functionals -/

/-- The Wronskian-type functional `D u θ = cos θ · (u θ · (sin 2θ)' - u' θ · sin 2θ)`; its
derivative is `2 · Lzero1 u θ · sinθcos²θ`. -/
def Dfun (u : ℝ → ℝ) : ℝ → ℝ :=
  fun θ => Real.cos θ * (u θ * (2 * Real.cos (2 * θ)) - deriv u θ * Real.sin (2 * θ))

/-- The quotient `R u θ = u θ / sin(2θ)`, whose derivative is `- D u θ /(cos θ · sin²2θ)`. -/
def Rfun (u : ℝ → ℝ) : ℝ → ℝ := fun θ => u θ / Real.sin (2 * θ)

/-- The weighted `L¹`-size `M u = ∫_0^{π/2} sinθcos²θ · |Lzero1 u θ| dθ` of the source. -/
def Mfun (u : ℝ → ℝ) : ℝ :=
  ∫ θ in Work.Spaces.Iθ, Work.Elliptic.sinCos2 θ * |Work.FTS.EllipticEst.Lzero1 u θ|

/-- The constant `B u = |D u (π/4)| + 2 M u` bounding the oscillation of `D u`. -/
def Bfun (u : ℝ → ℝ) : ℝ := |Dfun u (Real.pi / 4)| + 2 * Mfun u

/-! ## Elementary facts about the weight and the interval -/

theorem cos_ne_zero {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) : Real.cos θ ≠ 0 :=
  ne_of_gt (Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos, hθ.1], hθ.2⟩)

theorem sin_two_pos {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    0 < Real.sin (2 * θ) :=
  Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])

theorem continuous_sinCos2 : Continuous Work.Elliptic.sinCos2 := by
  unfold Work.Elliptic.sinCos2; fun_prop

theorem sinCos2_nonneg {s : ℝ} (hs : s ∈ Work.Spaces.Iθ) : 0 ≤ Work.Elliptic.sinCos2 s := by
  rw [Work.Elliptic.sinCos2]
  have h1 : 0 ≤ Real.sin s :=
    Real.sin_nonneg_of_nonneg_of_le_pi hs.1 (by linarith [hs.2, Real.pi_pos])
  positivity

theorem sinCos2_nonneg_of_mem {s : ℝ} (hs : s ∈ Set.Ioo 0 (Real.pi / 2)) :
    0 ≤ Work.Elliptic.sinCos2 s :=
  sinCos2_nonneg ⟨le_of_lt hs.1, le_of_lt hs.2⟩

theorem mem_Iθ_of_mem_Ioo {s : ℝ} (hs : s ∈ Set.Ioo 0 (Real.pi / 2)) : s ∈ Work.Spaces.Iθ :=
  ⟨le_of_lt hs.1, le_of_lt hs.2⟩



/-! ## Differentiability and continuity of the data on the open interval -/

theorem hasDerivAt_u {u : ℝ → ℝ} (hu : ContDiffOn ℝ ⊤ u (Set.Ioo 0 (Real.pi / 2))) {θ : ℝ}
    (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) : HasDerivAt u (deriv u θ) θ :=
  ((hu.contDiffAt (isOpen_Ioo.mem_nhds hθ)).differentiableAt (by simp)).hasDerivAt

theorem contDiffAt_deriv_of_contDiffOn {u : ℝ → ℝ} (hu : ContDiffOn ℝ ⊤ u (Set.Ioo 0 (Real.pi / 2)))
    {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) : ContDiffAt ℝ ⊤ (deriv u) θ :=
  (hu.contDiffAt (isOpen_Ioo.mem_nhds hθ)).derivWithin (m := ⊤) (by simp)

theorem continuousOn_deriv1 {u : ℝ → ℝ} (hu : ContDiffOn ℝ ⊤ u (Set.Ioo 0 (Real.pi / 2))) :
    ContinuousOn (deriv u) (Set.Ioo 0 (Real.pi / 2)) :=
  fun θ hθ => (contDiffAt_deriv_of_contDiffOn hu hθ).continuousAt.continuousWithinAt

theorem continuousOn_deriv2 {u : ℝ → ℝ} (hu : ContDiffOn ℝ ⊤ u (Set.Ioo 0 (Real.pi / 2))) :
    ContinuousOn (fun θ => deriv (deriv u) θ) (Set.Ioo 0 (Real.pi / 2)) :=
  fun θ hθ =>
    ((contDiffAt_deriv_of_contDiffOn hu hθ).derivWithin (m := ⊤) (by simp)).continuousAt.continuousWithinAt

/-- `Lzero1 u` is continuous on the open interval. -/
theorem continuousOn_Lzero1 {u : ℝ → ℝ} (hu : ContDiffOn ℝ ⊤ u (Set.Ioo 0 (Real.pi / 2))) :
    ContinuousOn (Work.FTS.EllipticEst.Lzero1 u) (Set.Ioo 0 (Real.pi / 2)) := by
  have hc0 : ContinuousOn u (Set.Ioo 0 (Real.pi / 2)) := hu.continuousOn
  have hc1 : ContinuousOn (deriv u) (Set.Ioo 0 (Real.pi / 2)) := continuousOn_deriv1 hu
  have hc2 : ContinuousOn (fun θ => deriv (deriv u) θ) (Set.Ioo 0 (Real.pi / 2)) :=
    continuousOn_deriv2 hu
  have hm : ContinuousOn (fun θ => deriv (fun t => Real.tan t * u t) θ)
      (Set.Ioo 0 (Real.pi / 2)) := by
    have hg : ContinuousOn
        (fun θ : ℝ => (1 / Real.cos θ ^ 2) * u θ + Real.tan θ * deriv u θ)
        (Set.Ioo 0 (Real.pi / 2)) := by
      have h1 : ContinuousOn (fun θ : ℝ => 1 / Real.cos θ ^ 2) (Set.Ioo 0 (Real.pi / 2)) := by
        refine ContinuousOn.div continuousOn_const (Real.continuous_cos.continuousOn.pow 2) ?_
        intro θ hθ
        exact pow_ne_zero 2 (cos_ne_zero hθ)
      have h2 : ContinuousOn (fun θ : ℝ => Real.tan θ * deriv u θ)
          (Set.Ioo 0 (Real.pi / 2)) := by
        have ht : ContinuousOn Real.tan (Set.Ioo 0 (Real.pi / 2)) :=
          Real.continuousOn_tan.mono (fun x hx => cos_ne_zero hx)
        rw [show (fun θ : ℝ => Real.tan θ * deriv u θ) = Real.tan * deriv u from rfl]
        exact ht.mul hc1
      exact (h1.mul hc0).add h2
    refine ContinuousOn.congr hg ?_
    intro θ hθ
    show deriv (fun t => Real.tan t * u t) θ
      = (1 / Real.cos θ ^ 2) * u θ + Real.tan θ * deriv u θ
    have hm' : HasDerivAt (fun t => Real.tan t * u t)
        ((1 / Real.cos θ ^ 2) * u θ + Real.tan θ * deriv u θ) θ :=
      (Real.hasDerivAt_tan (cos_ne_zero hθ)).mul (hasDerivAt_u hu hθ)
    rw [hm'.deriv]
  refine ContinuousOn.congr (f := fun θ =>
    -(deriv (deriv u) θ) + deriv (fun t => Real.tan t * u t) θ - 6 * u θ) ?_ ?_
  · exact ((hc2.neg).add hm).sub (hc0.const_mul 6)
  · intro θ hθ
    simp only [Work.FTS.EllipticEst.Lzero1]



/-! ## Interval integrability of the source term `2 g sinθcos²θ` -/



/-! ## Trigonometry and the two exact derivative identities -/

theorem hasDerivAt_sin_two (θ : ℝ) :
    HasDerivAt (fun x : ℝ => Real.sin (2 * x)) (2 * Real.cos (2 * θ)) θ := by
  have h2 : HasDerivAt (fun x : ℝ => (2 : ℝ) * x) 2 θ := by
    simpa only [id_eq, mul_one] using (hasDerivAt_id θ).const_mul 2
  exact ((Real.hasDerivAt_sin (2 * θ)).comp θ h2).congr_deriv (by ring)

theorem hasDerivAt_cos_two (θ : ℝ) :
    HasDerivAt (fun x : ℝ => Real.cos (2 * x)) (-2 * Real.sin (2 * θ)) θ := by
  have h2 : HasDerivAt (fun x : ℝ => (2 : ℝ) * x) 2 θ := by
    simpa only [id_eq, mul_one] using (hasDerivAt_id θ).const_mul 2
  exact ((Real.hasDerivAt_cos (2 * θ)).comp θ h2).congr_deriv (by ring)






/-! ## The bound on `Dfun` and the two growth bounds for `Rfun` -/






/-! ## The pointwise bounds on the weight -/




/-! ## The two integrability statements on the half-intervals -/



end LzeroGrowth


end Work.FTS.EllipticEst.H2W
end
end
-- ===== merged: Submission.Work.FTS.EllipticEst.Honest.I4CrossTermBound =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.Honest

open scoped Real Topology
open MeasureTheory Set Filter

/-- **The cross term of the honest `I₄` slice estimate, integrated.**

With `ψ = I4psi Φ = Φ/cos θ`, `σ = I4sig` and `Σ = I4Sig`, the pointwise AM–GM bound `hpt`
(read with `q = ψ'` and `Ψv = Φ`) says
`|sin θ · σ · ψ' · Φ| ≤ ½ Σ σ (ψ')² + 50 σ (Φ/cos θ)²`
on `(0, π/2)`.  Integrating it over the sub-interval `[δ, θ₁] ⊂ (0, π/2)` gives the crossed-out
term of `I4SliceBound`; the second term is upgraded from `∫_δ^{θ₁}` to `∫_{Iθ}` because `I4sig`
is nonnegative on `Iθ = [0, π/2]` and `I4psi Φ ^ 2 * I4sig` is integrable there (`hA`). -/
theorem I4CrossTermBound (Φ : ℝ → ℝ) (hsm : ContDiffOn ℝ 2 Φ (Set.Ioo 0 (Real.pi / 2)))
    (hA : MeasureTheory.IntegrableOn (fun θ => I4psi Φ θ ^ 2 * I4sig θ) Work.Spaces.Iθ)
    (hpt : ∀ θ ∈ Set.Ioo 0 (Real.pi / 2), ∀ q Ψv : ℝ,
        |Real.sin θ * I4sig θ * q * Ψv|
          ≤ (1 / 2) * I4Sig θ * I4sig θ * q ^ 2
            + 50 * I4sig θ * (Ψv / Real.cos θ) ^ 2)
    {δ θ₁ : ℝ} (hδ : 0 < δ) (hδθ : δ ≤ θ₁) (hθ₁ : θ₁ < Real.pi / 2) :
    |∫ θ in δ..θ₁, Real.sin θ * I4sig θ * deriv (I4psi Φ) θ * Φ θ|
      ≤ (1 / 2) * (∫ θ in δ..θ₁, I4Sig θ * I4sig θ * (deriv (I4psi Φ) θ) ^ 2)
        + 50 * (∫ θ in Work.Spaces.Iθ, I4psi Φ θ ^ 2 * I4sig θ) := by
  obtain ⟨hΦc, hψc, hqc, hσc, hSc⟩ := I4CrossCont Φ hsm hδ hδθ hθ₁
  -- continuity of the three integrands on `[δ, θ₁]`
  have hfc : ContinuousOn (fun θ => Real.sin θ * I4sig θ * deriv (I4psi Φ) θ * Φ θ)
      (Set.Icc δ θ₁) :=
    ((Real.continuous_sin.continuousOn.mul hσc).mul hqc).mul hΦc
  have hg1c : ContinuousOn (fun θ => I4Sig θ * I4sig θ * (deriv (I4psi Φ) θ) ^ 2)
      (Set.Icc δ θ₁) := (hSc.mul hσc).mul (hqc.pow 2)
  have hg2c : ContinuousOn (fun θ => I4psi Φ θ ^ 2 * I4sig θ) (Set.Icc δ θ₁) :=
    (hψc.pow 2).mul hσc
  have hfI : IntervalIntegrable (fun θ => Real.sin θ * I4sig θ * deriv (I4psi Φ) θ * Φ θ)
      volume δ θ₁ := hfc.intervalIntegrable_of_Icc hδθ
  have hg1I : IntervalIntegrable (fun θ => I4Sig θ * I4sig θ * (deriv (I4psi Φ) θ) ^ 2)
      volume δ θ₁ := hg1c.intervalIntegrable_of_Icc hδθ
  have hg2I : IntervalIntegrable (fun θ => I4psi Φ θ ^ 2 * I4sig θ) volume δ θ₁ :=
    hg2c.intervalIntegrable_of_Icc hδθ
  have hgI : IntervalIntegrable
      (fun θ => (1 / 2) * (I4Sig θ * I4sig θ * (deriv (I4psi Φ) θ) ^ 2)
        + 50 * (I4psi Φ θ ^ 2 * I4sig θ)) volume δ θ₁ :=
    (hg1I.const_mul (1 / 2)).add (hg2I.const_mul 50)
  -- the pointwise AM–GM bound, on the open interval `(δ, θ₁)`
  have hpt' : ∀ θ ∈ Set.Ioo δ θ₁,
      |Real.sin θ * I4sig θ * deriv (I4psi Φ) θ * Φ θ|
        ≤ (1 / 2) * (I4Sig θ * I4sig θ * (deriv (I4psi Φ) θ) ^ 2)
          + 50 * (I4psi Φ θ ^ 2 * I4sig θ) := by
    intro θ hθ
    have hθ' : θ ∈ Set.Ioo 0 (Real.pi / 2) :=
      ⟨lt_of_lt_of_le hδ (le_of_lt hθ.1), lt_of_le_of_lt (le_of_lt hθ.2) hθ₁⟩
    have h := hpt θ hθ' (deriv (I4psi Φ) θ) (Φ θ)
    calc |Real.sin θ * I4sig θ * deriv (I4psi Φ) θ * Φ θ|
        ≤ (1 / 2) * I4Sig θ * I4sig θ * (deriv (I4psi Φ) θ) ^ 2
          + 50 * I4sig θ * (Φ θ / Real.cos θ) ^ 2 := h
      _ = (1 / 2) * (I4Sig θ * I4sig θ * (deriv (I4psi Φ) θ) ^ 2)
          + 50 * (I4psi Φ θ ^ 2 * I4sig θ) := by rw [I4psi]; ring
  -- the `∫_θ`-integral over the sub-interval is at most the one over all of `Iθ`
  have hsub : (∫ θ in δ..θ₁, I4psi Φ θ ^ 2 * I4sig θ)
      ≤ (∫ θ in Work.Spaces.Iθ, I4psi Φ θ ^ 2 * I4sig θ) :=
    I4SubInterval (fun θ => I4psi Φ θ ^ 2 * I4sig θ) hA
      (fun θ hθ => mul_nonneg (sq_nonneg _) (I4sig_nonneg hθ)) (le_of_lt hδ) hδθ (le_of_lt hθ₁)
  calc |∫ θ in δ..θ₁, Real.sin θ * I4sig θ * deriv (I4psi Φ) θ * Φ θ|
      ≤ ∫ θ in δ..θ₁, |Real.sin θ * I4sig θ * deriv (I4psi Φ) θ * Φ θ| :=
        intervalIntegral.abs_integral_le_integral_abs
          (f := fun θ => Real.sin θ * I4sig θ * deriv (I4psi Φ) θ * Φ θ) hδθ
    _ ≤ ∫ θ in δ..θ₁, ((1 / 2) * (I4Sig θ * I4sig θ * (deriv (I4psi Φ) θ) ^ 2)
          + 50 * (I4psi Φ θ ^ 2 * I4sig θ)) :=
        intervalIntegral.integral_mono_on_of_le_Ioo
          (f := fun θ => |Real.sin θ * I4sig θ * deriv (I4psi Φ) θ * Φ θ|)
          (g := fun θ => (1 / 2) * (I4Sig θ * I4sig θ * (deriv (I4psi Φ) θ) ^ 2)
            + 50 * (I4psi Φ θ ^ 2 * I4sig θ))
          hδθ hfI.abs hgI (fun θ hθ => hpt' θ hθ)
    _ = (1 / 2) * (∫ θ in δ..θ₁, I4Sig θ * I4sig θ * (deriv (I4psi Φ) θ) ^ 2)
          + 50 * (∫ θ in δ..θ₁, I4psi Φ θ ^ 2 * I4sig θ) := by
        rw [intervalIntegral.integral_add (hg1I.const_mul (1 / 2)) (hg2I.const_mul 50),
          intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
    _ ≤ (1 / 2) * (∫ θ in δ..θ₁, I4Sig θ * I4sig θ * (deriv (I4psi Φ) θ) ^ 2)
          + 50 * (∫ θ in Work.Spaces.Iθ, I4psi Φ θ ^ 2 * I4sig θ) :=
        add_le_add le_rfl (mul_le_mul_of_nonneg_left hsub (by norm_num))

end Work.FTS.EllipticEst.Honest
end
-- ===== merged: Submission.Work.FTS.EllipticEst.vorticity_psiField_bslOp_fts =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The vorticity of a self-similar stream-function field is `bslOp`

For a stream function of the self-similar no-swirl form
`ψ(r,z) = ρ² Ψ(ρ^α,θ)`, `ρ = √(r²+z²)`, `θ = arctan(z/r)`, the delivered curl identity
`Work.Cyl.vorticity_psiField` and the polar reduction `Work.Elliptic.cylOp_polar` compose to

  `vorticity (psiField (ρ² Ψ(ρ^α,θ))) x = -(bslOp α Ψ (ρ x ^ α) (θ x)) • e_θ(x)`.

This is the sign convention recorded in `Submission/Work/FTS/EllipticEst/Defs.lean`:
the `e_θ`-coefficient `Ω` of the vorticity and the source `F` of (PolarBSL) satisfy `F = -Ω`.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

open scoped Real Topology

namespace Work.FTS.EllipticEst

/-! ## Two `C²` calculus helpers

These are the (private) calculus inputs of `Work.Elliptic.cylOp_polar` and of
`Work.Cyl.vorticity_psiField`, reproduced here because both consumers need the *composite*
`C²` statement for `(r,z) ↦ ρ(r,z)² Ψ(ρ(r,z)^α, θ(r,z))` at the point `(radial x, axial x)`. -/





/-- At a point off the axis, `ρ(radial x, axial x) = rho x`. -/
private theorem rhoP_radial_axial (x : Work.Cyl.R3) :
    Work.Cyl.rhoP (Work.Cyl.radial x) (Work.Cyl.axial x) = Work.Cyl.rho x := by
  simp only [Work.Cyl.rhoP, Work.Cyl.rho, Work.Cyl.radSq, Work.Cyl.radial]
  rw [Real.sq_sqrt (by positivity : (0 : ℝ) ≤ x 0 ^ 2 + x 1 ^ 2)]

/-- At a point off the axis, `θ(radial x, axial x) = theta x`. -/
private theorem thetaP_radial_axial (x : Work.Cyl.R3) :
    Work.Cyl.thetaP (Work.Cyl.radial x) (Work.Cyl.axial x) = Work.Cyl.theta x := rfl


end Work.FTS.EllipticEst
end
-- ===== merged: Submission.Work.FTS.H2.HkSqSwap =====
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

/-- **Tonelli for a nonnegative integrand, with the two iterated integrals swapped.**

Let `g : α → β → ℝ` be nonnegative, a.e. strongly measurable on the product of the
`σ`-finite measures `μ` and `ν`, with `ν`-integrable slices and `μ`-integrable partially
integrated function `a ↦ ∫ b, g a b ∂ν`.  Then the iterated integral in the opposite
order exists, equals the original one, and its two ingredients are integrable:

* `∫ b, ∫ a, g a b ∂μ ∂ν = ∫ a, ∫ b, g a b ∂ν ∂μ`;
* the partially integrated function `b ↦ ∫ a, g a b ∂μ` is integrable for `ν`;
* for `ν`-almost every `b`, the slice `a ↦ g a b` is integrable for `μ`.

The proof is `Work.Spaces.integrable_prod_of_iterated` (which produces the integrability
of the uncurried `g` on the product measure from the two iterated-integral hypotheses),
followed by Fubini for the integrable function `g` in the swapped order. -/
theorem swap_iterated_integral_of_nonneg {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {μ : MeasureTheory.Measure α} {ν : MeasureTheory.Measure β} [MeasureTheory.SFinite μ]
    [MeasureTheory.SFinite ν] {g : α → β → ℝ} (hnn : ∀ a b, 0 ≤ g a b)
    (haesm : MeasureTheory.AEStronglyMeasurable (Function.uncurry g) (μ.prod ν))
    (hslice : ∀ᵐ a ∂μ, MeasureTheory.Integrable (fun b => g a b) ν)
    (houter : MeasureTheory.Integrable (fun a => ∫ b, g a b ∂ν) μ) :
    (∫ b, ∫ a, g a b ∂μ ∂ν = ∫ a, ∫ b, g a b ∂ν ∂μ) ∧
      MeasureTheory.Integrable (fun b => ∫ a, g a b ∂μ) ν ∧
      (∀ᵐ b ∂ν, MeasureTheory.Integrable (fun a => g a b) μ) := by
  obtain ⟨hint, hprod⟩ :=
    Work.Spaces.integrable_prod_of_iterated (μ := μ) (ν := ν) hnn haesm hslice houter
  -- the uncurried integrand of the swapped order is integrable on the swapped product
  have hswap : MeasureTheory.Integrable (Function.uncurry fun b a => g a b) (ν.prod μ) :=
    hint.swap
  refine ⟨?_, hswap.integral_prod_left, hswap.prod_right_ae⟩
  calc (∫ b, ∫ a, g a b ∂μ ∂ν)
      = ∫ p : β × α, g p.2 p.1 ∂(ν.prod μ) := MeasureTheory.integral_integral hswap
    _ = ∫ p : α × β, g p.1 p.2 ∂(μ.prod ν) :=
          MeasureTheory.integral_prod_swap (Function.uncurry g)
    _ = ∫ a, ∫ b, g a b ∂ν ∂μ := hprod


end Work.FTS.H2
end
end
-- ===== merged: Submission.Work.FTS.H2.T1HardIntMixed =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.H2

open MeasureTheory Set Filter
open scoped Real Topology


end Work.FTS.H2
end
-- ===== merged: Submission.Work.FTS.StrongPersist.H6Rows.Npair6SupAux.RadAux.radial_mslot_le_cd6 =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongPersist.H6Rows.Npair6SupAux.RadAux

set_option linter.unusedVariables false

/-- `x² ≤ y²` from `|x| ≤ y` (with `y` allowed to be any real number). -/
private theorem sq_le_sq_of_abs_le {x y : ℝ} (h : |x| ≤ y) : x ^ 2 ≤ y ^ 2 :=
  calc x ^ 2 = |x| ^ 2 := (sq_abs x).symm
    _ ≤ y ^ 2 := pow_le_pow_left₀ (abs_nonneg x) h 2

/-- Every binomial coefficient `n.choose k` with `n ≤ 6` is at most `2 ^ 6 = 64`. -/
private theorem choose_le_64 {n k : ℕ} (hn : n ≤ 6) : (n.choose k : ℝ) ≤ 64 := by
  have h2 : 2 ^ n ≤ 64 := by
    calc 2 ^ n ≤ 2 ^ 6 := Nat.pow_le_pow_right (by norm_num) hn
      _ = 64 := by norm_num
  exact_mod_cast le_trans (Nat.choose_le_two_pow n k) h2

theorem radial_mslot_le_cd6 {α K : ℝ} {r : ℝ → ℝ} {g : ℝ → ℝ → ℝ} {z θ : ℝ}
    (hMx : ∀ j i : ℕ, 1 ≤ i → i + j ≤ 6 →
      Work.Spaces.mixed j i (fun z θ => r z * g z θ) z θ
        = ∑ b ∈ Finset.range (j + 1), (j.choose b : ℝ)
            * (Work.Elliptic.DzdIter b r z * Work.Spaces.mixed (j - b) i g z θ))
    (hKb : ∀ b : ℕ, b ≤ 6 → |Work.Elliptic.DzdIter b r z| ≤ K)
    (i j : ℕ) (hi : 1 ≤ i) (hij : i + j ≤ 6) :
    (Work.Spaces.mixed j i (fun z θ => r z * g z θ) z θ * Work.Spaces.Wt α z θ) ^ 2
      ≤ 200704 * K ^ 2 * Work.Spaces.HkIntegrand α 6 g z θ := by
  have hj6 : j ≤ 6 := by omega
  -- the summands of the Leibniz expansion, with the weight already distributed
  set Y : ℕ → ℝ := fun b => (j.choose b : ℝ) * (Work.Elliptic.DzdIter b r z
    * (Work.Spaces.mixed (j - b) i g z θ * Work.Spaces.Wt α z θ)) with hY
  have hsplit : Work.Spaces.mixed j i (fun z θ => r z * g z θ) z θ
        * Work.Spaces.Wt α z θ = ∑ b ∈ Finset.range (j + 1), Y b := by
    rw [hMx j i hi hij, Finset.sum_mul]
    exact Finset.sum_congr rfl fun b _ => by simp only [hY]; ring
  rw [hsplit]
  have hHk : (0 : ℝ) ≤ Work.Spaces.HkIntegrand α 6 g z θ :=
    Work.Spaces.HkIntegrand_nonneg α 6 g z θ
  have hcard : ((Finset.range (j + 1)).card : ℝ) = (j : ℝ) + 1 := by
    rw [Finset.card_range]; push_cast; ring
  -- Cauchy–Schwarz on the `j+1` summands
  have hcs : (∑ b ∈ Finset.range (j + 1), Y b) ^ 2
      ≤ ((j : ℝ) + 1) * ∑ b ∈ Finset.range (j + 1), (Y b) ^ 2 := by
    have h := Finset.sum_mul_sq_le_sq_mul_sq (Finset.range (j + 1))
      (fun _ : ℕ => (1 : ℝ)) Y
    simpa [hcard] using h
  -- each summand: binomial coefficient, radial factor, surviving `g`-slot
  have hper : ∀ b ∈ Finset.range (j + 1), (Y b) ^ 2
      ≤ 4096 * K ^ 2 * Work.Spaces.HkIntegrand α 6 g z θ := by
    intro b hb
    have hbj : b ≤ j := Nat.le_of_lt_succ (Finset.mem_range.mp hb)
    have hb6 : b ≤ 6 := by omega
    have hsub : i + (j - b) ≤ 6 := by omega
    have hch : (j.choose b : ℝ) ≤ 64 := choose_le_64 hj6
    have hch2 : (j.choose b : ℝ) ^ 2 ≤ 64 ^ 2 :=
      pow_le_pow_left₀ (by positivity) hch 2
    have hD : (Work.Elliptic.DzdIter b r z) ^ 2 ≤ K ^ 2 :=
      sq_le_sq_of_abs_le (hKb b hb6)
    have hYg : (Work.Spaces.mixed (j - b) i g z θ * Work.Spaces.Wt α z θ) ^ 2
        ≤ Work.Spaces.HkIntegrand α 6 g z θ :=
      Work.Spaces.sq_le_HkIntegrand_mixed α 6 g z θ i (j - b) hi hsub
    have hYsq : (Y b) ^ 2 = (j.choose b : ℝ) ^ 2 * (Work.Elliptic.DzdIter b r z) ^ 2
        * (Work.Spaces.mixed (j - b) i g z θ * Work.Spaces.Wt α z θ) ^ 2 := by
      simp only [hY]; ring
    rw [hYsq]
    calc (j.choose b : ℝ) ^ 2 * (Work.Elliptic.DzdIter b r z) ^ 2
          * (Work.Spaces.mixed (j - b) i g z θ * Work.Spaces.Wt α z θ) ^ 2
        ≤ (64 ^ 2 * K ^ 2) * Work.Spaces.HkIntegrand α 6 g z θ :=
          mul_le_mul (mul_le_mul hch2 hD (sq_nonneg _) (sq_nonneg _)) hYg
            (sq_nonneg _) (by positivity)
      _ = 4096 * K ^ 2 * Work.Spaces.HkIntegrand α 6 g z θ := by norm_num
  have hsum2 : ∑ b ∈ Finset.range (j + 1), (Y b) ^ 2
      ≤ ∑ _b ∈ Finset.range (j + 1),
          (4096 * K ^ 2 * Work.Spaces.HkIntegrand α 6 g z θ) :=
    Finset.sum_le_sum hper
  have hsum3 : ∑ _b ∈ Finset.range (j + 1),
        (4096 * K ^ 2 * Work.Spaces.HkIntegrand α 6 g z θ)
      = ((j : ℝ) + 1) * (4096 * K ^ 2 * Work.Spaces.HkIntegrand α 6 g z θ) := by
    rw [Finset.sum_const, nsmul_eq_mul, hcard]
  have hj1 : (j : ℝ) + 1 ≤ 7 := by
    have : (j : ℝ) ≤ 6 := by exact_mod_cast hj6
    linarith
  have hjj : ((j : ℝ) + 1) * ((j : ℝ) + 1) ≤ 49 := by nlinarith [hj1]
  have h4096 : (0 : ℝ) ≤ 4096 * K ^ 2 * Work.Spaces.HkIntegrand α 6 g z θ :=
    mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg K)) hHk
  calc (∑ b ∈ Finset.range (j + 1), Y b) ^ 2
      ≤ ((j : ℝ) + 1) * ∑ b ∈ Finset.range (j + 1), (Y b) ^ 2 := hcs
    _ ≤ ((j : ℝ) + 1) * ∑ _b ∈ Finset.range (j + 1),
          (4096 * K ^ 2 * Work.Spaces.HkIntegrand α 6 g z θ) :=
        mul_le_mul_of_nonneg_left hsum2 (by positivity)
    _ = ((j : ℝ) + 1)
          * (((j : ℝ) + 1) * (4096 * K ^ 2 * Work.Spaces.HkIntegrand α 6 g z θ)) := by
        rw [hsum3]
    _ = (((j : ℝ) + 1) * ((j : ℝ) + 1))
          * (4096 * K ^ 2 * Work.Spaces.HkIntegrand α 6 g z θ) := by ring
    _ ≤ 49 * (4096 * K ^ 2 * Work.Spaces.HkIntegrand α 6 g z θ) :=
        mul_le_mul_of_nonneg_right hjj h4096
    _ = 200704 * K ^ 2 * Work.Spaces.HkIntegrand α 6 g z θ := by ring

end Work.FTS.StrongPersist.H6Rows.Npair6SupAux.RadAux
end
-- ===== merged: Submission.Work.FTS.StrongPersist.H6Rows.Npair6SupAux.RadAux.radial_zslot_le_cd6 =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongPersist.H6Rows.Npair6SupAux.RadAux

open scoped Real Topology

/-- The Leibniz expansion of `D_z^i (r · g)` (a hypothesis of the main statement) bounds
`|D_z^i (r · g) · w / sin(2θ)^{η/2}|` by `(i+1) · 64 · K · √(HkIntegrand α 6 g)`:
there are at most `i + 1 ≤ 7` terms, each carrying a binomial coefficient `≤ 2^i ≤ 64`,
a radial factor bounded by `K`, and one `D_z`-slot `D_z^{i-b} g` of the `H^6` integrand. -/
theorem abs_DzIter_mul_w_le {K : ℝ} {r : ℝ → ℝ} {g : ℝ → ℝ → ℝ} {α z θ : ℝ}
    (hDz : ∀ j : ℕ, j ≤ 6 →
      Work.Spaces.DzIter j (fun z θ => r z * g z θ) z θ
        = ∑ b ∈ Finset.range (j + 1), (j.choose b : ℝ)
            * (Work.Elliptic.DzdIter b r z * Work.Spaces.DzIter (j - b) g z θ))
    (hKb : ∀ b : ℕ, b ≤ 6 → |Work.Elliptic.DzdIter b r z| ≤ K)
    (i : ℕ) (hi : i ≤ 6) :
    |Work.Spaces.DzIter i (fun z θ => r z * g z θ) z θ
        * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))|
      ≤ 448 * K * Real.sqrt (Work.Spaces.HkIntegrand α 6 g z θ) := by
  have hKnn : 0 ≤ K := le_trans (abs_nonneg (r z)) (by simpa using hKb 0 (by norm_num))
  have hHnn : 0 ≤ Work.Spaces.HkIntegrand α 6 g z θ :=
    Work.Spaces.HkIntegrand_nonneg α 6 g z θ
  have hchoose : ∀ b : ℕ, |((i.choose b : ℕ) : ℝ)| ≤ 64 := by
    intro b
    rw [abs_of_nonneg (Nat.cast_nonneg _)]
    have h1 : i.choose b ≤ 2 ^ i := Nat.choose_le_two_pow i b
    have h2 : (2 : ℕ) ^ i ≤ 2 ^ 6 := Nat.pow_le_pow_right (by norm_num) (by omega)
    have h3 : (2 : ℕ) ^ 6 = 64 := by norm_num
    have h4 : i.choose b ≤ 64 := by omega
    exact_mod_cast h4
  have hexp : Work.Spaces.DzIter i (fun z θ => r z * g z θ) z θ
        * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))
      = ∑ b ∈ Finset.range (i + 1), (i.choose b : ℝ)
          * (Work.Elliptic.DzdIter b r z
              * (Work.Spaces.DzIter (i - b) g z θ
                  * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2)))) := by
    rw [hDz i hi, Finset.sum_mul]
    exact Finset.sum_congr rfl fun b _ => by ring
  have hbound : |Work.Spaces.DzIter i (fun z θ => r z * g z θ) z θ
        * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))|
      ≤ ∑ b ∈ Finset.range (i + 1), 64 * K
          * |Work.Spaces.DzIter (i - b) g z θ
              * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))| := by
    rw [hexp]
    refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
    refine Finset.sum_le_sum fun b hb => ?_
    rw [Finset.mem_range] at hb
    have hbK : |Work.Elliptic.DzdIter b r z| ≤ K := hKb b (by omega)
    have h1 : |((i.choose b : ℕ) : ℝ)| * |Work.Elliptic.DzdIter b r z| ≤ 64 * K :=
      mul_le_mul (hchoose b) hbK (abs_nonneg _) (by norm_num)
    calc |((i.choose b : ℕ) : ℝ)
            * (Work.Elliptic.DzdIter b r z
              * (Work.Spaces.DzIter (i - b) g z θ
                  * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))))|
        = |((i.choose b : ℕ) : ℝ)| * |Work.Elliptic.DzdIter b r z|
          * |Work.Spaces.DzIter (i - b) g z θ
              * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))| := by
          rw [abs_mul, abs_mul]; ring
      _ ≤ 64 * K * |Work.Spaces.DzIter (i - b) g z θ
              * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))| :=
          mul_le_mul_of_nonneg_right h1 (abs_nonneg _)
  have hsum : ∑ b ∈ Finset.range (i + 1), 64 * K
        * |Work.Spaces.DzIter (i - b) g z θ
            * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))|
      ≤ 448 * K * Real.sqrt (Work.Spaces.HkIntegrand α 6 g z θ) := by
    have hstep : ∀ b ∈ Finset.range (i + 1),
        64 * K * |Work.Spaces.DzIter (i - b) g z θ
            * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))|
        ≤ 64 * K * Real.sqrt (Work.Spaces.HkIntegrand α 6 g z θ) := by
      intro b hb
      rw [Finset.mem_range] at hb
      refine mul_le_mul_of_nonneg_left ?_ (mul_nonneg (by norm_num) hKnn)
      rw [← Real.sqrt_sq_eq_abs]
      exact Real.sqrt_le_sqrt (Work.Spaces.sq_le_HkIntegrand_z α 6 g z θ (i - b) (by omega))
    calc ∑ b ∈ Finset.range (i + 1), 64 * K
          * |Work.Spaces.DzIter (i - b) g z θ
              * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))|
        ≤ ∑ _b ∈ Finset.range (i + 1),
            64 * K * Real.sqrt (Work.Spaces.HkIntegrand α 6 g z θ) :=
          Finset.sum_le_sum hstep
      _ = ((i + 1 : ℕ) : ℝ) * (64 * K * Real.sqrt (Work.Spaces.HkIntegrand α 6 g z θ)) := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      _ ≤ 7 * (64 * K * Real.sqrt (Work.Spaces.HkIntegrand α 6 g z θ)) := by
          refine mul_le_mul_of_nonneg_right ?_
            (mul_nonneg (mul_nonneg (by norm_num) hKnn) (Real.sqrt_nonneg _))
          exact_mod_cast (show i + 1 ≤ 7 by omega)
      _ = 448 * K * Real.sqrt (Work.Spaces.HkIntegrand α 6 g z θ) := by ring
  exact le_trans hbound hsum

theorem radial_zslot_le_cd6 {K : ℝ} {r : ℝ → ℝ} {g : ℝ → ℝ → ℝ} {α z θ : ℝ}
    (hDz : ∀ j : ℕ, j ≤ 6 →
      Work.Spaces.DzIter j (fun z θ => r z * g z θ) z θ
        = ∑ b ∈ Finset.range (j + 1), (j.choose b : ℝ)
            * (Work.Elliptic.DzdIter b r z * Work.Spaces.DzIter (j - b) g z θ))
    (hKb : ∀ b : ℕ, b ≤ 6 → |Work.Elliptic.DzdIter b r z| ≤ K)
    (i : ℕ) (hi : i ≤ 6) :
    (Work.Spaces.DzIter i (fun z θ => r z * g z θ) z θ
        * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2
      ≤ 200704 * K ^ 2 * Work.Spaces.HkIntegrand α 6 g z θ := by
  have hHnn : 0 ≤ Work.Spaces.HkIntegrand α 6 g z θ :=
    Work.Spaces.HkIntegrand_nonneg α 6 g z θ
  have hfinal := abs_DzIter_mul_w_le (α := α) (θ := θ) hDz hKb i hi
  have hsq : (Work.Spaces.DzIter i (fun z θ => r z * g z θ) z θ
        * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2
      ≤ (448 * K * Real.sqrt (Work.Spaces.HkIntegrand α 6 g z θ)) ^ 2 := by
    have h1 : |Work.Spaces.DzIter i (fun z θ => r z * g z θ) z θ
        * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))| ^ 2
        ≤ (448 * K * Real.sqrt (Work.Spaces.HkIntegrand α 6 g z θ)) ^ 2 :=
      pow_le_pow_left₀ (abs_nonneg _) hfinal 2
    rwa [sq_abs] at h1
  calc (Work.Spaces.DzIter i (fun z θ => r z * g z θ) z θ
        * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2
      ≤ (448 * K * Real.sqrt (Work.Spaces.HkIntegrand α 6 g z θ)) ^ 2 := hsq
    _ = 200704 * K ^ 2 * Work.Spaces.HkIntegrand α 6 g z θ := by
        rw [mul_pow, mul_pow, Real.sq_sqrt hHnn]
        ring

end Work.FTS.StrongPersist.H6Rows.Npair6SupAux.RadAux
end
-- ===== merged: Submission.Work.FTS_RegExport.RXT.Sys.continuousAt_Qang_of_bounds =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS_RegExport.RXT.Sys

/-- Continuity at `s₀ > 0` of the angular moment `s ↦ ∫ θ in Iθ, Ktheta θ * f s θ` of a function
`f` which is continuous on the open quadrant and locally bounded on a neighbourhood of `s₀`.

PROOF RECIPE.  Apply the existing engine
`Work.FTS_RegExport.RXT.continuousAt_integral_Itheta_of_bound` with `G := fun z θ => f z θ`,
`φ := Work.Elliptic.Ktheta`, `z₀ := s₀`, `K := max A 0`; its conclusion is continuity of the
integral over `volume.restrict (Set.Ioo 0 (π/2))`, and
`MeasureTheory.setIntegral_congr_set (MeasureTheory.Ioo_ae_eq_Icc ..)` transfers it to `Iθ`.
The hypotheses: `ContinuousOn Ktheta Iθ` (it is `3*sin θ*cos θ ^ 2`); the eventual a.e. strong
measurability of `θ ↦ f z θ * Ktheta θ` from `Work.Spaces.aesm_slice_of_continuousOn_Qd` applied to
`(p : ℝ × ℝ) ↦ f p.1 p.2 * Ktheta p.2` (continuous on the open quadrant by `hcont`); the eventual
a.e. bound `‖f z θ‖ ≤ max A 0` from `hbd` on the open neighbourhood `Ioo (s₀/2) (2*s₀) ∋ s₀` of
`hs₀`; and the a.e. continuity of `z ↦ f z θ` at `s₀` from `hcont` at the interior point
`(s₀,θ)`, `θ ∈ (0,π/2)`. -/
theorem continuousAt_Qang_of_bounds {f : ℝ → ℝ → ℝ} {s₀ A : ℝ} (hs₀ : 0 < s₀)
    (hcont : ContinuousOn (Function.uncurry f)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)))
    (hbd : ∀ z θ : ℝ, z ∈ Set.Ioo (s₀ / 2) (2 * s₀) → 0 < θ → θ < Real.pi / 2 →
      |f z θ| ≤ A) :
    ContinuousAt (fun s => ∫ θ in Work.Spaces.Iθ, Work.Elliptic.Ktheta θ * f s θ) s₀ := by
  -- `s₀` has a neighbourhood on which the hypothesis `hbd` applies.
  have hU : Set.Ioo (s₀ / 2) (2 * s₀) ∈ nhds s₀ :=
    Ioo_mem_nhds (by linarith) (by linarith)
  have hKtheta : Continuous Work.Elliptic.Ktheta := by
    unfold Work.Elliptic.Ktheta; fun_prop
  -- Eventual a.e. strong measurability of the slices.
  have hmeas : ∀ᶠ z in nhds s₀,
      MeasureTheory.AEStronglyMeasurable (fun θ => f z θ * Work.Elliptic.Ktheta θ)
        (MeasureTheory.volume.restrict (Set.Ioo 0 (Real.pi / 2))) := by
    filter_upwards [hU] with z hz
    have hzpos : 0 < z := by linarith [hz.1]
    have h1 : ContinuousOn (fun θ : ℝ => f z θ) (Set.Ioo 0 (Real.pi / 2)) :=
      hcont.comp (continuous_const.prodMk continuous_id).continuousOn
        (fun θ hθ => ⟨hzpos, hθ⟩)
    exact (h1.mul hKtheta.continuousOn).aestronglyMeasurable measurableSet_Ioo
  -- Eventual a.e. bound by `max A 0`.
  have hbound : ∀ᶠ z in nhds s₀,
      ∀ᵐ θ ∂(MeasureTheory.volume.restrict (Set.Ioo 0 (Real.pi / 2))), ‖f z θ‖ ≤ max A 0 := by
    filter_upwards [hU] with z hz
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioo] with θ hθ
    rw [Real.norm_eq_abs]
    exact le_trans (hbd z θ hz hθ.1 hθ.2) (le_max_left _ _)
  -- A.e. continuity of the slices at `s₀`.
  have haecont : ∀ᵐ θ ∂(MeasureTheory.volume.restrict (Set.Ioo 0 (Real.pi / 2))),
      ContinuousAt (fun z => f z θ) s₀ := by
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioo] with θ hθ
    have hpt : (s₀, θ) ∈ Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (0 : ℝ) (Real.pi / 2) := ⟨hs₀, hθ⟩
    have hca : ContinuousAt (Function.uncurry f) (s₀, θ) :=
      hcont.continuousAt ((isOpen_Ioi.prod isOpen_Ioo).mem_nhds hpt)
    have hcomp := hca.comp (x := s₀) (continuousAt_id.prodMk continuousAt_const)
    simpa [Function.comp_def, Function.uncurry] using hcomp
  -- The engine, on the open interval `(0, π/2)`.
  have hmain := Work.FTS_RegExport.RXT.continuousAt_integral_Itheta_of_bound
    (G := fun z θ => f z θ) (φ := Work.Elliptic.Ktheta) (z₀ := s₀) (K := max A 0)
    (le_max_right _ _) hKtheta.continuousOn hmeas hbound haecont
  -- Transfer from `(0, π/2)` to `Iθ = [0, π/2]`: the two differ by a null set.
  refine hmain.congr ?_
  filter_upwards with s
  simp only [Work.Spaces.Iθ]
  rw [MeasureTheory.setIntegral_congr_set
    (MeasureTheory.Ioo_ae_eq_Icc (μ := MeasureTheory.volume) (a := (0 : ℝ))
      (b := Real.pi / 2)).symm]
  exact MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun θ => mul_comm _ _)

end Work.FTS_RegExport.RXT.Sys
end
