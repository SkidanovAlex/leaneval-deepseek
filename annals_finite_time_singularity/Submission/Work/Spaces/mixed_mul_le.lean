import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.Normed.Operator.Bilinear
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Basic.Real.Basic
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Order.CompletePartialOrder
import Mathlib.Order.Filter.Defs
import Mathlib.Order.Interval.Basic
import Mathlib.Tactic.NormNum.Ineq
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Mathlib.Topology.GDelta.MetrizableSpace
import Submission.Work.FTS.EllipticEst.OpenFTC.absFtcLeIntegralAbsDeriv
import Submission.Work.Spaces.factor_bound
import Submission.Work.Spaces.sin_two_rpow
import Submission.Work.Spaces.sq_mul_div_rpow
import Submission.Work.Spaces.uncurry_partial_c1
-- ===== merged: Submission.Work.Coercivity.BoxAux =====
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

/-- The radial function `z ↦ z (D_z f(z,θ) w(z))²` whose `z`-derivative is integrated
in `box_deriv_ftc`. -/
def BoxG (f : ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ :=
  fun z θ => z * (Spaces.Dz f z θ * Spaces.w z) ^ 2

@[simp]
theorem BoxG_apply (f : ℝ → ℝ → ℝ) (z θ : ℝ) :
    BoxG f z θ = z * (Spaces.Dz f z θ * Spaces.w z) ^ 2 := rfl

@[simp]
theorem BoxG_zero_left (f : ℝ → ℝ → ℝ) (θ : ℝ) : BoxG f 0 θ = 0 := by
  simp [BoxG]

/-- The radial weight `w(z) = (1+z)²/z²` is smooth on the open half-line `(0,∞)`. -/
theorem contDiffOn_w : ContDiffOn ℝ ⊤ Spaces.w (Set.Ioi (0 : ℝ)) := by
  have hnum : ContDiffOn ℝ ⊤ (fun z : ℝ => (1 + z) ^ 2) (Set.Ioi (0 : ℝ)) := by
    have h : ContDiffOn ℝ ⊤ (fun z : ℝ => (1 : ℝ) + z) (Set.Ioi (0 : ℝ)) :=
      contDiffOn_const.add contDiffOn_id
    exact h.pow 2
  have hden : ContDiffOn ℝ ⊤ (fun z : ℝ => z ^ 2) (Set.Ioi (0 : ℝ)) := contDiffOn_id.pow 2
  have hne : ∀ z ∈ Set.Ioi (0 : ℝ), z ^ 2 ≠ 0 := fun z hz => pow_ne_zero 2 (ne_of_gt hz)
  exact hnum.div hden hne

/-- `BoxG f` is smooth on `(0,∞) × (-1, π/2+1)` whenever `f` is `SmoothNbhd`. -/
theorem contDiffOn_uncurry_BoxG (f : ℝ → ℝ → ℝ) (hsm : Spaces.SmoothNbhd f) :
    ContDiffOn ℝ ⊤ (Function.uncurry (BoxG f))
      (Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (-1) (π / 2 + 1)) := by
  set V : Set (ℝ × ℝ) := Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (-1) (π / 2 + 1) with hV
  have hDzbox : ContDiffOn ℝ ⊤ (Function.uncurry (Spaces.Dz f))
      (Set.Ioi (-1) ×ˢ Set.Ioo (-1) (π / 2 + 1)) :=
    Spaces.contDiffOn_uncurry_Dz (isOpen_Ioi.prod isOpen_Ioo) hsm
  have hsub : V ⊆ Set.Ioi (-1) ×ˢ Set.Ioo (-1) (π / 2 + 1) := by
    rintro ⟨z, θ⟩ hp
    rw [hV] at hp
    simp only [Set.mem_prod, Set.mem_Ioi, Set.mem_Ioo] at hp ⊢
    exact ⟨by linarith [hp.1], hp.2⟩
  have hDz : ContDiffOn ℝ ⊤ (Function.uncurry (Spaces.Dz f)) V := hDzbox.mono hsub
  have hw : ContDiffOn ℝ ⊤ (fun p : ℝ × ℝ => Spaces.w p.1) V :=
    contDiffOn_w.comp contDiffOn_fst (fun p hp => hp.1)
  have hz : ContDiffOn ℝ ⊤ (fun p : ℝ × ℝ => p.1) V := contDiffOn_fst
  have h : ContDiffOn ℝ ⊤
      (fun p : ℝ × ℝ => p.1 * (Function.uncurry (Spaces.Dz f) p * Spaces.w p.1) ^ 2) V :=
    hz.mul ((hDz.mul hw).pow 2)
  refine h.congr (fun p _ => ?_)
  simp only [Function.uncurry, BoxG]

/-- The radial slice `z ↦ BoxG f z θ` is smooth on `(0,∞)`, for every `θ ∈ Iθ`. -/
theorem contDiffOn_BoxG_slice (f : ℝ → ℝ → ℝ) (hsm : Spaces.SmoothNbhd f) {θ : ℝ}
    (hθ : θ ∈ Spaces.Iθ) :
    ContDiffOn ℝ ⊤ (fun z => BoxG f z θ) (Set.Ioi (0 : ℝ)) := by
  have hmap : Set.MapsTo (fun z : ℝ => (z, θ)) (Set.Ioi (0 : ℝ))
      (Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (-1) (π / 2 + 1)) := fun z hz =>
    ⟨hz, ⟨by linarith [hθ.1], by linarith [hθ.2]⟩⟩
  have h := (contDiffOn_uncurry_BoxG f hsm).comp
    (contDiffOn_id.prodMk contDiffOn_const) hmap
  exact h.congr (fun z _ => rfl)

/-- The radial derivative `∂_z BoxG f` is smooth on `(0,∞) × (-1, π/2+1)`. -/
theorem contDiffOn_uncurry_pz_BoxG (f : ℝ → ℝ → ℝ) (hsm : Spaces.SmoothNbhd f) :
    ContDiffOn ℝ ⊤ (Function.uncurry (Spaces.pz (BoxG f)))
      (Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (-1) (π / 2 + 1)) :=
  Spaces.contDiffOn_uncurry_pz (isOpen_Ioi.prod isOpen_Ioo) (contDiffOn_uncurry_BoxG f hsm)


end Work.Coercivity
end
end
-- ===== merged: Submission.Work.Coercivity.CTDefs =====
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

namespace CT

set_option autoImplicit false

/-! ## Lifting angular and radial functions to the quadrant -/

/-- A function of the angle alone, viewed as a function of `(z,θ)`. -/
def ang (g : ℝ → ℝ) : ℝ → ℝ → ℝ := fun _ θ => g θ

/-- A function of `z` alone, viewed as a function of `(z,θ)`. -/
def rad (R : ℝ → ℝ) : ℝ → ℝ → ℝ := fun z _ => R z


/-! ## `D_z` on radial functions -/

/-- `D_z = z ∂_z` acting on functions of `z` alone. -/
def DzR (R : ℝ → ℝ) : ℝ → ℝ := fun z => z * deriv R z

/-- Iterated `D_z` on functions of `z` alone. -/
def DzRIter : ℕ → (ℝ → ℝ) → ℝ → ℝ
  | 0, R => R
  | n + 1, R => DzR (DzRIter n R)

@[simp] theorem DzRIter_zero (R : ℝ → ℝ) : DzRIter 0 R = R := rfl
@[simp] theorem DzRIter_succ (n : ℕ) (R : ℝ → ℝ) :
    DzRIter (n + 1) R = DzR (DzRIter n R) := rfl

/-- Iterated `D_θ = sin(2θ) ∂_θ` on functions of the angle alone. -/
def DthIterAng : ℕ → (ℝ → ℝ) → ℝ → ℝ
  | 0, g => g
  | n + 1, g => fun θ => Real.sin (2 * θ) * deriv (DthIterAng n g) θ

@[simp] theorem DthIterAng_zero (g : ℝ → ℝ) : DthIterAng 0 g = g := rfl
theorem DthIterAng_succ (n : ℕ) (g : ℝ → ℝ) :
    DthIterAng (n + 1) g = fun θ => Real.sin (2 * θ) * deriv (DthIterAng n g) θ := rfl

/-! ## The angular data as functions of `(z,θ)` -/

/-- `Γ(θ)` as a function of `(z,θ)`. -/
def GamF (α : ℝ) : ℝ → ℝ → ℝ := ang (Spaces.Gam α)


theorem GamF_apply (α z θ : ℝ) : GamF α z θ = Spaces.Gam α θ := rfl


/-! ## The radial factors of the commutator defect -/

/-- `L₁₂(D_θ f)`. -/
def A1 (f : ℝ → ℝ → ℝ) : ℝ → ℝ := fun z => L12f (Spaces.Dth f) z

/-- `L₁₂(f)`. -/
def A2 (f : ℝ → ℝ → ℝ) : ℝ → ℝ := fun z => L12f f z

/-- The constant `L₁₂(Transport f)(0)` of the projector term. -/
def KC0 (f : ℝ → ℝ → ℝ) : ℝ := L12f (Transport f) 0

/-- The constant `L₁₂(Transport(D_θ f))(0)`. -/
def KC1 (f : ℝ → ℝ → ℝ) : ℝ := L12f (Transport (Spaces.Dth f)) 0

/-- The radial factor multiplying `Γ(θ)` in the commutator defect. -/
def F1 (α : ℝ) (f : ℝ → ℝ → ℝ) : ℝ → ℝ :=
  fun z => (2 * z / (Spaces.c α * (1 + z) ^ 2)) * A1 f z
    - (2 * z ^ 2 / (Spaces.c α * (1 + z) ^ 3)) * KC1 f

/-- The radial factor multiplying `D_θΓ(θ)` in the commutator defect. -/
def F2 (α : ℝ) (f : ℝ → ℝ → ℝ) : ℝ → ℝ :=
  fun z => (2 * z ^ 2 / (Spaces.c α * (1 + z) ^ 3)) * KC0 f
    - (2 * z / (Spaces.c α * (1 + z) ^ 2)) * A2 f z




/-! ## The weighted energies and angular integrals occurring in the estimate -/



/-- The angular integral `∫_θ (D_θ^iΓ)² sin(2θ)^{-γ}`. -/
def AngGam (α : ℝ) (i : ℕ) : ℝ :=
  ∫ θ in Spaces.Iθ,
    (DthIterAng i (Spaces.Gam α) θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Spaces.gam α))


end CT

end Work.Coercivity

namespace Work.Coercivity

namespace CT

set_option autoImplicit false



end CT

end Work.Coercivity
end
end
-- ===== merged: Submission.Work.Coercivity.CommutZBase =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.Coercivity.CommutZ

open Work.Coercivity Work.Spaces

set_option autoImplicit false

/-! ## `z`-only multiplier functions -/

/-- A function of `z` alone, viewed as a function of `(z,θ)`. -/
def mulZ (m : ℝ → ℝ) : ℝ → ℝ → ℝ := fun z _ => m z

@[simp] theorem mulZ_apply (m : ℝ → ℝ) (z θ : ℝ) : mulZ m z θ = m z := rfl


/-- The one-variable version of the iterated operator `D_z = z ∂_z`. -/
def DzIterZ : ℕ → (ℝ → ℝ) → (ℝ → ℝ)
  | 0, m => m
  | n + 1, m => fun z => z * deriv (DzIterZ n m) z

@[simp] theorem DzIterZ_zero (m : ℝ → ℝ) : DzIterZ 0 m = m := rfl

theorem DzIterZ_succ (n : ℕ) (m : ℝ → ℝ) :
    DzIterZ (n + 1) m = fun z => z * deriv (DzIterZ n m) z := rfl

/-- The iterated `D_z` applied to a `z`-only multiplier agrees with the one-variable
version. -/
theorem DzIter_mulZ (j : ℕ) (m : ℝ → ℝ) : DzIter j (mulZ m) = mulZ (DzIterZ j m) := by
  induction j with
  | zero => rfl
  | succ j ih =>
      rw [DzIter_succ, ih]
      funext z θ
      simp only [Dz, mulZ, DzIterZ_succ]
      congr 1

/-! ## The `K`-average -/

/-- The `K`-average in `θ` of a function of `(z,θ)`: `∫_θ K(θ) g(z,θ)`. -/
def Kav (g : ℝ → ℝ → ℝ) (z : ℝ) : ℝ := ∫ θ in Iθ, K θ * g z θ

/-! ## The explicit profiles -/

/-- The multiplier `2z/(1+z)²` of the commutator (it is the profile `F_*`). -/
def mm (z : ℝ) : ℝ := 2 * z / (1 + z) ^ 2

/-- `q(z) = 2z²/(1+z)³`, the `z`-profile of the projector correction. -/
def qfun (z : ℝ) : ℝ := 2 * z ^ 2 / (1 + z) ^ 3

/-- `z q'(z)` for `q(z) = 2z²/(1+z)³`. -/
def zdq (z : ℝ) : ℝ := 2 * z ^ 2 * (2 - z) / (1 + z) ^ 4

/-- The coefficient of `L₁₂(f)` in the `D_z`-commutator: `-2z(1-z)/(1+z)³`. -/
def cfac (z : ℝ) : ℝ := -(2 * z * (1 - z)) / (1 + z) ^ 3



/-! ## The `L₁₂`-constants and the `z`-profile `G` -/

/-- `Λ₁ = L₁₂(3 D_θ f/(1+z))(0)`, the constant produced by the projector applied to
the transport term. -/
def Lam1 (f : ℝ → ℝ → ℝ) : ℝ := L12f (Transport f) 0

/-- `Λ₂ = L₁₂(3 D_θ(D_z f)/(1+z))(0)`. -/
def Lam2 (f : ℝ → ℝ → ℝ) : ℝ := L12f (Transport (Dz f)) 0

/-- The `z`-profile `G` of the `Γ`-part of the `D_z`-commutator `E₂`:
`G(z) = -(2z(1-z)/(1+z)³)L₁₂(f)(z) + z q'(z) Λ₁ - q(z) Λ₂`. -/
def Gfun (f : ℝ → ℝ → ℝ) (z : ℝ) : ℝ :=
  cfac z * L12f f z + zdq z * Lam1 f - qfun z * Lam2 f

/-! ## The analytic hypothesis behind the pointwise identity

The pointwise expansion of the defect `E₂` uses the fundamental theorem of calculus on the
tail integral `L₁₂(f)(z) = ∫_z^∞ L₁₂-density` (which needs the density to be integrable) and
the identity `L₁₂(D_z f)(z) = -(K,f)_{L²_θ}(z)`, which needs in addition that the
`K`-average of `f` vanishes at `z = ∞`.  These are the only analytic inputs; they are
discharged from `SmoothNbhd f` and `HkMem α n f` (`1 ≤ n`) in the companion file. -/

/-- The analytic hypotheses used by the pointwise `D_z`-commutator identity at the level of
`z`-functions: the `L₁₂`-densities of `f` and of `D_z f` are integrable on the half-line
and the `K`-average of `f` vanishes at infinity. -/
structure TailHyp (f : ℝ → ℝ → ℝ) : Prop where
  /-- the `L₁₂`-density of `f` is integrable on `(0,∞)`. -/
  hint : IntegrableOn (FM.L12dens Spaces.K f) (Set.Ioi 0)
  /-- the `L₁₂`-density of `D_z f` is integrable on `(0,∞)`. -/
  hintDz : IntegrableOn (FM.L12dens Spaces.K (Spaces.Dz f)) (Set.Ioi 0)
  /-- the `K`-average `∫_θ K(θ) f(z,θ)` vanishes as `z → ∞`. -/
  hlim : Tendsto (fun s => Kav f s) atTop (𝓝 0)





end Work.Coercivity.CommutZ
end
end
-- ===== merged: Submission.Work.Coercivity.EDth_eq_wip =====
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

/-- The weight identity behind `EDth_eq_wip`, pointwise: with `s = sin(2θ) ≥ 0` the
square of the angular weight `w·s^(-γ/2)` is `w²·s^(-γ)`. -/
private theorem sq_mul_rpow_neg_half (a w s γ : ℝ) (hs : 0 ≤ s) :
    (a * (w * s ^ (-(γ / 2)))) ^ 2 = a * a * (w ^ 2 * s ^ (-γ)) := by
  have h : (s ^ (-(γ / 2))) ^ 2 = s ^ (-γ) := by
    rw [← Real.rpow_natCast (s ^ (-(γ / 2))) 2]
    calc (s ^ (-(γ / 2))) ^ (2 : ℝ) = s ^ ((-(γ / 2)) * 2) :=
          (Real.rpow_mul hs (-(γ / 2)) (2 : ℝ)).symm
      _ = s ^ (-γ) := by rw [show (-(γ / 2)) * 2 = -γ by ring]
  calc (a * (w * s ^ (-(γ / 2)))) ^ 2 = a ^ 2 * (w ^ 2 * (s ^ (-(γ / 2))) ^ 2) := by ring
    _ = a ^ 2 * (w ^ 2 * s ^ (-γ)) := by rw [h]
    _ = a * a * (w ^ 2 * s ^ (-γ)) := by ring

/-- `|D_θ f · w/√(sin(2θ)^γ)|²_{L²}` written in weighted inner-product form. -/
theorem EDth_eq_wip (α : ℝ) (f : ℝ → ℝ → ℝ) :
    EDth α f = wip (fun z θ => Spaces.w z ^ 2 * (Real.sin (2 * θ)) ^ (-(Spaces.gam α)))
      (Spaces.Dth f) (Spaces.Dth f) := by
  simp only [EDth, wtGam, Spaces.L2Sq, wip, Spaces.Iz, Spaces.Iθ]
  refine MeasureTheory.integral_congr_ae (Eventually.of_forall fun z => ?_)
  refine MeasureTheory.setIntegral_congr_fun measurableSet_Icc fun θ hθ => ?_
  have hs : 0 ≤ Real.sin (2 * θ) :=
    Real.sin_nonneg_of_nonneg_of_le_pi (by linarith [hθ.1])
      (by linarith [hθ.2, Real.pi_pos])
  exact sq_mul_rpow_neg_half (Spaces.Dth f z θ) (Spaces.w z) (Real.sin (2 * θ))
    (Spaces.gam α) hs

end Work.Coercivity
end
end
-- ===== merged: Submission.Work.Coercivity.EDz_eq_wip =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.Coercivity

theorem EDz_eq_wip (f : ℝ → ℝ → ℝ) :
    EDz f = wip (fun z θ => Spaces.w z ^ 2 * (Real.sin (2 * θ)) ^ (-Spaces.eta))
      (Spaces.Dz f) (Spaces.Dz f) := by
  simp only [EDz, Spaces.L2Sq, wip, wtEta, wtGam]
  refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
  refine MeasureTheory.integral_congr_ae ?_
  filter_upwards [MeasureTheory.self_mem_ae_restrict (s := Spaces.Iθ) measurableSet_Icc] with θ hθ
  have hsin : 0 ≤ Real.sin (2 * θ) := by
    apply Real.sin_nonneg_of_nonneg_of_le_pi
    · linarith [hθ.1]
    · have := Real.pi_pos; linarith [hθ.2]
  have hr : (Real.sin (2 * θ) ^ (-(Spaces.eta / 2))) ^ 2 = Real.sin (2 * θ) ^ (-Spaces.eta) := by
    rw [← Real.rpow_natCast (Real.sin (2 * θ) ^ (-(Spaces.eta / 2))) 2]
    calc (Real.sin (2 * θ) ^ (-(Spaces.eta / 2))) ^ (2 : ℝ)
        = Real.sin (2 * θ) ^ ((-(Spaces.eta / 2)) * 2) :=
          (Real.rpow_mul hsin (-(Spaces.eta / 2)) (2 : ℝ)).symm
      _ = Real.sin (2 * θ) ^ (-Spaces.eta) := by
          rw [show (-(Spaces.eta / 2)) * 2 = -Spaces.eta by ring]
  rw [mul_pow, mul_pow, hr]
  ring

end Work.Coercivity
end
-- ===== merged: Submission.Work.Coercivity.EfEta_eq_wip =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.Coercivity

theorem EfEta_eq_wip (f : ℝ → ℝ → ℝ) :
    EfEta f = wip (fun z θ => Spaces.w z ^ 2 * (Real.sin (2 * θ)) ^ (-Spaces.eta)) f f := by
  simp only [EfEta, wtEta, wtGam, Spaces.L2Sq, wip]
  apply MeasureTheory.setIntegral_congr_fun measurableSet_Ici
  intro z hz
  apply MeasureTheory.setIntegral_congr_fun measurableSet_Icc
  intro θ hθ
  dsimp only
  have hsin : 0 ≤ Real.sin (2 * θ) := by
    apply Real.sin_nonneg_of_mem_Icc
    constructor <;> linarith [hθ.1, hθ.2, Real.pi_pos]
  have hs : ((Real.sin (2 * θ)) ^ (-(Spaces.eta / 2))) ^ 2
      = (Real.sin (2 * θ)) ^ (-Spaces.eta) := by
    rw [← Real.rpow_natCast ((Real.sin (2 * θ)) ^ (-(Spaces.eta / 2))) 2,
      ← Real.rpow_mul hsin]
    rw [show (-(Spaces.eta / 2)) * ((2 : ℕ) : ℝ) = -Spaces.eta by push_cast; ring]
  rw [mul_pow, mul_pow, hs]
  ring

end Work.Coercivity
end
-- ===== merged: Submission.Work.Coercivity.EzDefs =====
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

/-- Honesty of an iterated integral over the quadrant `[0,∞) × [0,π/2]`: every angular
slice is integrable and the resulting function of `z` is integrable on `[0,∞)`. -/
def I2Mem (A : ℝ → ℝ → ℝ) : Prop :=
  (∀ z ∈ Spaces.Iz, IntegrableOn (fun θ => A z θ) Spaces.Iθ) ∧
    IntegrableOn (fun z => ∫ θ in Spaces.Iθ, A z θ) Spaces.Iz


/-- The `D_z⁰f` summand of `HkIntegrand α 1 f`. -/
def U0 (f : ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ :=
  fun z θ => Spaces.DzIter 0 f z θ * (Spaces.w z / (Real.sin (2 * θ)) ^ (Spaces.eta / 2))

/-- The `D_z¹f` summand of `HkIntegrand α 1 f`. -/
def U1 (f : ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ :=
  fun z θ => Spaces.DzIter 1 f z θ * (Spaces.w z / (Real.sin (2 * θ)) ^ (Spaces.eta / 2))

/-- The `D_θf` summand of `HkIntegrand α 1 f`. -/
def U2 (α : ℝ) (f : ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ :=
  fun z θ => Spaces.mixed 0 1 f z θ * Spaces.Wt α z θ

end Work.Coercivity
end
end
-- ===== merged: Submission.Work.Coercivity.HkShape =====
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



/-- The coercivity clause of `IsHkIP`, unpacked for a caller. -/
theorem IsHkIP.coercive {α : ℝ} {k : ℕ} {IP : (ℝ → ℝ → ℝ) → (ℝ → ℝ → ℝ) → ℝ}
    (h : IsHkIP α k IP) :
    ∃ c : ℝ, 0 < c ∧ ∀ f : ℝ → ℝ → ℝ, HkAdm α k f →
      c * Spaces.HkSq α k f ≤ IP (LGammaT α f) f :=
  h.2.2.2.2.2

/-- The comparison clause of `IsHkIP`, unpacked for a caller. -/
theorem IsHkIP.le_self {α : ℝ} {k : ℕ} {IP : (ℝ → ℝ → ℝ) → (ℝ → ℝ → ℝ) → ℝ}
    (h : IsHkIP α k IP) {f : ℝ → ℝ → ℝ} (ha : HkAdm α k f) : Spaces.HkSq α k f ≤ IP f f :=
  h.2.2.2.1 f ha

/-- The nonnegativity clause of `IsHkIP`, unpacked for a caller. -/
theorem IsHkIP.nonneg {α : ℝ} {k : ℕ} {IP : (ℝ → ℝ → ℝ) → (ℝ → ℝ → ℝ) → ℝ}
    (h : IsHkIP α k IP) (u : ℝ → ℝ → ℝ) : 0 ≤ IP u u :=
  h.2.2.1 u

/-- The additivity clause of `IsHkIP`, unpacked for a caller. -/
theorem IsHkIP.add {α : ℝ} {k : ℕ} {IP : (ℝ → ℝ → ℝ) → (ℝ → ℝ → ℝ) → ℝ}
    (h : IsHkIP α k IP) (f₁ f₂ g : ℝ → ℝ → ℝ)
    (hs₁ : Spaces.SmoothNbhd f₁) (hs₂ : Spaces.SmoothNbhd f₂) (hsg : Spaces.SmoothNbhd g)
    (h₁ : Spaces.HkMem α k f₁) (h₂ : Spaces.HkMem α k f₂) (hg : Spaces.HkMem α k g) :
    IP (f₁ + f₂) g = IP f₁ g + IP f₂ g :=
  h.1 f₁ f₂ g hs₁ hs₂ hsg h₁ h₂ hg

end Work.Coercivity
end
end
-- ===== merged: Submission.Work.Coercivity.HkSq_mono =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

/-- Monotonicity of the `H^k`-integrand in `k`: every summand occurring in
`HkIntegrand α k f` also occurs in `HkIntegrand α (k+1) f` (with the same value), and
all summands are squares, hence nonnegative. -/
theorem Work.Spaces.HkIntegrand_mono (α : ℝ) (k : ℕ) (f : ℝ → ℝ → ℝ) (z θ : ℝ) :
    Work.Spaces.HkIntegrand α k f z θ ≤ Work.Spaces.HkIntegrand α (k + 1) f z θ := by
  set Z : ℕ → ℝ := fun i =>
    (Work.Spaces.DzIter i f z θ * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2
    with hZdef
  set ψ : ℕ → ℕ → ℝ := fun i j =>
    (if 1 ≤ i ∧ i + j ≤ k + 1 then (Work.Spaces.mixed j i f z θ * Work.Spaces.Wt α z θ) ^ 2 else 0)
    with hψdef
  have key : ∀ i j : ℕ,
      (if 1 ≤ i ∧ i + j ≤ k then
          (Work.Spaces.mixed j i f z θ * Work.Spaces.Wt α z θ) ^ 2 else 0) ≤ ψ i j := by
    intro i j
    show (if 1 ≤ i ∧ i + j ≤ k then
        (Work.Spaces.mixed j i f z θ * Work.Spaces.Wt α z θ) ^ 2 else 0)
      ≤ (if 1 ≤ i ∧ i + j ≤ k + 1 then
        (Work.Spaces.mixed j i f z θ * Work.Spaces.Wt α z θ) ^ 2 else 0)
    by_cases h : 1 ≤ i ∧ i + j ≤ k
    · rw [ite_eq_left h, ite_eq_left ⟨h.1, by omega⟩]
    · rw [ite_eq_right h]
      split_ifs with h2
      · exact sq_nonneg _
      · exact le_refl 0
  have hψnn : ∀ i j, 0 ≤ ψ i j := by
    intro i j
    show 0 ≤ (if 1 ≤ i ∧ i + j ≤ k + 1 then
      (Work.Spaces.mixed j i f z θ * Work.Spaces.Wt α z θ) ^ 2 else 0)
    split_ifs with h2
    · exact sq_nonneg _
    · exact le_refl 0
  have hA : (∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1),
        (if 1 ≤ i ∧ i + j ≤ k then
          (Work.Spaces.mixed j i f z θ * Work.Spaces.Wt α z θ) ^ 2 else 0))
      ≤ (∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1), ψ i j) :=
    Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => key i j
  have hB : (∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1), ψ i j)
      ≤ (∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1 + 1), ψ i j) :=
    Finset.sum_le_sum fun i _ =>
      Finset.sum_le_sum_of_subset_of_nonneg
        (fun x hx => by rw [Finset.mem_range] at hx ⊢; omega)
        (fun j _ _ => hψnn i j)
  have hC : (∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1 + 1), ψ i j)
      ≤ (∑ i ∈ Finset.range (k + 1 + 1), ∑ j ∈ Finset.range (k + 1 + 1), ψ i j) :=
    Finset.sum_le_sum_of_subset_of_nonneg
      (fun x hx => by rw [Finset.mem_range] at hx ⊢; omega)
      (fun i _ _ => Finset.sum_nonneg fun j _ => hψnn i j)
  have hM : (∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1),
        (if 1 ≤ i ∧ i + j ≤ k then
          (Work.Spaces.mixed j i f z θ * Work.Spaces.Wt α z θ) ^ 2 else 0))
      ≤ (∑ i ∈ Finset.range (k + 1 + 1), ∑ j ∈ Finset.range (k + 1 + 1), ψ i j) :=
    le_trans hA (le_trans hB hC)
  have hZ : (∑ i ∈ Finset.range (k + 1), Z i) ≤ (∑ i ∈ Finset.range (k + 1 + 1), Z i) :=
    Finset.sum_le_sum_of_subset_of_nonneg
      (fun x hx => by rw [Finset.mem_range] at hx ⊢; omega)
      (fun i _ _ => by
        show 0 ≤ (Work.Spaces.DzIter i f z θ *
          (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2
        exact sq_nonneg _)
  rw [Work.Spaces.HkIntegrand, Work.Spaces.HkIntegrand]
  exact add_le_add hZ hM

namespace Work.Coercivity

theorem HkSq_mono (α : ℝ) (k : ℕ) {f : ℝ → ℝ → ℝ} (h : Spaces.HkMem α (k + 1) f) :
    Spaces.HkSq α k f ≤ Spaces.HkSq α (k + 1) f := by
  rw [Spaces.HkSq, Spaces.HkSq]
  refine MeasureTheory.integral_mono_of_nonneg
    (Eventually.of_forall fun z =>
      MeasureTheory.integral_nonneg fun θ => Spaces.HkIntegrand_nonneg α k f z θ)
    h.2 ?_
  show ∀ᵐ z ∂(volume.restrict Spaces.Iz),
    (∫ θ in Spaces.Iθ, Spaces.HkIntegrand α k f z θ)
      ≤ ∫ θ in Spaces.Iθ, Spaces.HkIntegrand α (k + 1) f z θ
  exact MeasureTheory.ae_restrict_of_forall_mem
    (show MeasurableSet Spaces.Iz from measurableSet_Ici)
    fun z hz => MeasureTheory.integral_mono_of_nonneg
      (Eventually.of_forall fun θ => Spaces.HkIntegrand_nonneg α k f z θ)
      (h.1 z hz)
      (Eventually.of_forall fun θ => Spaces.HkIntegrand_mono α k f z θ)

end Work.Coercivity
end
end
-- ===== merged: Submission.Work.Coercivity.Proj_L12f_zero =====
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

/-! ## The angular data -/

/-- The angular interval `Iθ` is measurable (it is `Icc 0 (π/2)`). -/
private theorem measurableSet_Iθ : MeasurableSet Work.Spaces.Iθ := measurableSet_Icc

/-- The angular average of the projector's angular profile is `1`:
`∫_{Iθ} K(θ)Γ(θ)/c = c/c = 1`. -/
theorem integral_KGam_div_c (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) :
    (∫ θ in Work.Spaces.Iθ, Work.Spaces.K θ * Work.Spaces.Gam α θ / Work.Spaces.c α) = 1 := by
  have hc : Work.Spaces.c α ≠ 0 := c_ne_zero hα hα1
  rw [MeasureTheory.integral_div]
  have hcint : (∫ θ in Work.Spaces.Iθ, Work.Spaces.K θ * Work.Spaces.Gam α θ)
      = Work.Spaces.c α := by
    rw [Work.Spaces.c]
    exact MeasureTheory.setIntegral_congr_fun measurableSet_Iθ (fun θ _ => mul_comm _ _)
  rw [hcint, div_self hc]

/-! ## The density identity -/

/-- **The angular density of the projected profile.**  For `s > 0`,
`L₁₂dens(𝕡 f)(s) = L₁₂dens(f)(s) - L₁₂(f)(0)·2s/(1+s)³`.

Indeed `𝕡 f = f - L₁₂(f)(0)·AK α` pointwise, with
`AK α z θ = (Γ(θ)/c) 2z²/(1+z)³`; integrating the correction against `K(θ)/s` gives
`L₁₂(f)(0)·(2s²/(1+s)³)/s · ∫_{Iθ} K(θ)Γ(θ)/c = L₁₂(f)(0)·2s/(1+s)³`. -/
theorem Proj_L12dens (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) (f : ℝ → ℝ → ℝ)
    (h2 : ∀ s ∈ Set.Ioi (0:ℝ),
      MeasureTheory.IntegrableOn (fun θ => Work.Spaces.K θ * f s θ / s) Work.Spaces.Iθ)
    {s : ℝ} (hs : s ∈ Set.Ioi (0:ℝ)) :
    Work.FM.L12dens Work.Spaces.K (Work.Coercivity.Proj α f) s
      = Work.FM.L12dens Work.Spaces.K f s
        - Work.Coercivity.L12f f 0 * (2 * s / (1 + s) ^ 3) := by
  have hspos : (0 : ℝ) < s := hs
  have hs0 : s ≠ 0 := ne_of_gt hspos
  have h1s : (1 : ℝ) + s ≠ 0 := by positivity
  have hc : Work.Spaces.c α ≠ 0 := c_ne_zero hα hα1
  -- the correction slice is integrable (it is a constant multiple of `ΓK`)
  have hcorr : MeasureTheory.IntegrableOn
      (fun θ : ℝ => (Work.Coercivity.L12f f 0 * (2 * s / (1 + s) ^ 3))
        * (Work.Spaces.K θ * Work.Spaces.Gam α θ / Work.Spaces.c α)) Work.Spaces.Iθ :=
    MeasureTheory.IntegrableOn.congr_fun
      ((Work.Spaces.CAux.integrableOn_GamK α hα).const_mul
        (Work.Coercivity.L12f f 0 * (2 * s / (1 + s) ^ 3) / Work.Spaces.c α))
      (fun θ _ => by first | (field_simp; ring) | field_simp | ring)
      measurableSet_Iθ
  have hGval := integral_KGam_div_c α hα hα1
  change ∫ θ in Work.Spaces.Iθ, Work.Spaces.K θ * Work.Coercivity.Proj α f s θ / s
      = (∫ θ in Work.Spaces.Iθ, Work.Spaces.K θ * f s θ / s)
        - Work.Coercivity.L12f f 0 * (2 * s / (1 + s) ^ 3)
  rw [MeasureTheory.setIntegral_congr_fun measurableSet_Iθ (show Set.EqOn
      (fun θ => Work.Spaces.K θ * Work.Coercivity.Proj α f s θ / s)
      (fun θ => Work.Spaces.K θ * f s θ / s
        - (Work.Coercivity.L12f f 0 * (2 * s / (1 + s) ^ 3))
          * (Work.Spaces.K θ * Work.Spaces.Gam α θ / Work.Spaces.c α))
      Work.Spaces.Iθ from fun θ _ => by
        simp only [Proj_eq]
        first | (field_simp; ring) | field_simp | ring)]
  rw [MeasureTheory.integral_sub (h2 s hs) hcorr, MeasureTheory.integral_const_mul, hGval,
    mul_one]

/-! ## The improper integral `∫_0^∞ 2s/(1+s)³ ds = 1` -/

/-- `d/ds (-2/(1+s) + 1/(1+s)²) = 2s/(1+s)³` for `s ≥ 0`. -/
theorem hasDerivAt_frac (x : ℝ) (hx : 0 ≤ x) :
    HasDerivAt (fun t : ℝ => -2 / (1 + t) + 1 / (1 + t) ^ 2) (2 * x / (1 + x) ^ 3) x := by
  have hx1 : (1 : ℝ) + x ≠ 0 := by positivity
  have h1 : HasDerivAt (fun t : ℝ => -2 / (1 + t)) (2 / (1 + x) ^ 2) x := by
    simpa using Work.FM.hasDerivAt_div_add_const (-2) 1 x hx1
  have h2 : HasDerivAt (fun t : ℝ => 1 / (1 + t) ^ 2) (-2 / (1 + x) ^ 3) x := by
    have hnum : HasDerivAt (fun _ : ℝ => (1 : ℝ)) 0 x := hasDerivAt_const x 1
    have hden : HasDerivAt (fun t : ℝ => (1 + t) ^ 2) (2 * (1 + x)) x :=
      Work.FM.hasDerivAt_one_add_sq x
    have h := hnum.div hden (pow_ne_zero 2 hx1)
    convert h using 1
    first | (field_simp; ring) | field_simp | ring
  have h3 : HasDerivAt (fun t : ℝ => -2 / (1 + t) + 1 / (1 + t) ^ 2)
      (2 / (1 + x) ^ 2 + -2 / (1 + x) ^ 3) x := h1.add h2
  have hve : 2 / (1 + x) ^ 2 + -2 / (1 + x) ^ 3 = 2 * x / (1 + x) ^ 3 := by
    first | (field_simp; ring) | field_simp | ring
  rw [hve] at h3
  exact h3

/-- The antiderivative `-2/(1+s) + 1/(1+s)²` tends to `0` at `+∞`. -/
theorem tendsto_frac :
    Tendsto (fun t : ℝ => -2 / (1 + t) + 1 / (1 + t) ^ 2) atTop (𝓝 0) := by
  have h1 : Tendsto (fun t : ℝ => (1 : ℝ) + t) atTop atTop :=
    tendsto_atTop_add_const_left atTop (1 : ℝ) tendsto_id
  have h2 : Tendsto (fun t : ℝ => ((1 : ℝ) + t)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp h1
  have h3 : Tendsto (fun t : ℝ => ((1 : ℝ) + t)⁻¹ ^ 2) atTop (𝓝 0) := by
    simpa using h2.pow 2
  have h4 := (h2.const_mul (-2 : ℝ)).add h3
  simpa [div_eq_mul_inv, inv_pow] using h4

/-- `2s/(1+s)³` is nonnegative on `(0,∞)`. -/
theorem two_mul_div_cube_nonneg {x : ℝ} (hx : x ∈ Set.Ioi (0:ℝ)) :
    0 ≤ 2 * x / (1 + x) ^ 3 := by
  have hx' : (0 : ℝ) < x := hx
  have hx1 : (0 : ℝ) < 1 + x := by linarith
  positivity

/-- The improper integral `∫_0^∞ 2s/(1+s)³ ds = 1`. -/
theorem integral_Ioi_two_mul_div_cube :
    ∫ s in Set.Ioi (0 : ℝ), 2 * s / (1 + s) ^ 3 = 1 := by
  have key := MeasureTheory.integral_Ioi_of_hasDerivAt_of_nonneg'
    (g := fun t : ℝ => -2 / (1 + t) + 1 / (1 + t) ^ 2)
    (g' := fun t : ℝ => 2 * t / (1 + t) ^ 3) (a := 0) (l := 0)
    (fun x hx => hasDerivAt_frac x hx) (fun x hx => two_mul_div_cube_nonneg hx) tendsto_frac
  rw [key]
  norm_num

/-- The correction profile `s ↦ 2s/(1+s)³` is integrable on `(0,∞)` (its integral is `1`,
see `integral_Ioi_two_mul_div_cube`). -/
theorem integrableOn_two_mul_div_cube :
    MeasureTheory.IntegrableOn (fun s : ℝ => 2 * s / (1 + s) ^ 3) (Set.Ioi 0) := by
  have key := MeasureTheory.integrableOn_Ioi_deriv_of_nonneg'
    (g := fun t : ℝ => -2 / (1 + t) + 1 / (1 + t) ^ 2)
    (g' := fun t : ℝ => 2 * t / (1 + t) ^ 3) (a := 0) (l := 0)
    (fun x hx => hasDerivAt_frac x hx) (fun x hx => two_mul_div_cube_nonneg hx) tendsto_frac
  exact MeasureTheory.IntegrableOn.congr_fun key (fun x _ => rfl) measurableSet_Ioi

/-! ## The main theorem -/

/-- **The projector removes the value of `L₁₂` at the origin**:
`L₁₂(𝕡 f)(0) = 0`. -/
theorem Proj_L12f_zero (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) (f : ℝ → ℝ → ℝ)
    (h1 : MeasureTheory.IntegrableOn (Work.FM.L12dens Work.Spaces.K f) (Set.Ioi 0))
    (h2 : ∀ s ∈ Set.Ioi (0:ℝ),
      MeasureTheory.IntegrableOn (fun θ => Work.Spaces.K θ * f s θ / s) Work.Spaces.Iθ)
    (h3 : MeasureTheory.IntegrableOn
      (Work.FM.L12dens Work.Spaces.K (Work.Coercivity.Proj α f)) (Set.Ioi 0)) :
    Work.Coercivity.L12f (Work.Coercivity.Proj α f) 0 = 0 := by
  have hdens : ∀ s ∈ Set.Ioi (0:ℝ),
      Work.FM.L12dens Work.Spaces.K (Work.Coercivity.Proj α f) s
        = Work.FM.L12dens Work.Spaces.K f s
          - Work.Coercivity.L12f f 0 * (2 * s / (1 + s) ^ 3) :=
    fun s hs => Proj_L12dens α hα hα1 f h2 hs
  have hcorr : MeasureTheory.IntegrableOn
      (fun s : ℝ => Work.Coercivity.L12f f 0 * (2 * s / (1 + s) ^ 3)) (Set.Ioi 0) :=
    (integrableOn_two_mul_div_cube.const_mul _)
  have hmain : (∫ s in Set.Ioi (0:ℝ),
        Work.FM.L12dens Work.Spaces.K (Work.Coercivity.Proj α f) s)
      = ∫ s in Set.Ioi (0:ℝ), (Work.FM.L12dens Work.Spaces.K f s
          - Work.Coercivity.L12f f 0 * (2 * s / (1 + s) ^ 3)) :=
    MeasureTheory.setIntegral_congr_fun measurableSet_Ioi hdens
  change ∫ s in Set.Ioi (0:ℝ), Work.FM.L12dens Work.Spaces.K (Work.Coercivity.Proj α f) s
    = 0
  rw [hmain, MeasureTheory.integral_sub h1 hcorr, MeasureTheory.integral_const_mul,
    integral_Ioi_two_mul_div_cube, mul_one]
  change Work.Coercivity.L12f f 0 - Work.Coercivity.L12f f 0 = 0
  ring

end Work.Coercivity
end
end
-- ===== merged: Submission.Work.Coercivity.f_sq_w_sq_integrable =====
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

/-! ## The null set `{sin(2θ) = 0}` -/



/-! ## The pointwise facts at `θ ∈ Iθ` -/


/-! ## The a.e. statements on the quadrant -/


/-! ## The main statement -/


end Work.Coercivity
end
end
-- ===== merged: Submission.Work.Coercivity.integrableOn_GammaK_sq =====
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

/-- `Γ(θ)` is continuous on the angular interval `Iθ`: its base
`sin θ · cos²θ` is continuous and nonnegative there while `α/3 ≥ 0`. -/
theorem continuousOn_Gam (α : ℝ) (hα : 0 < α) :
    ContinuousOn (fun θ : ℝ => Spaces.Gam α θ) Spaces.Iθ := by
  have hα3 : (0 : ℝ) ≤ α / 3 := by linarith
  have hu : ContinuousOn (fun θ : ℝ => Real.sin θ * Real.cos θ ^ 2) Spaces.Iθ :=
    (Real.continuous_sin.mul (Real.continuous_cos.pow 2)).continuousOn
  have h := hu.rpow_const (fun θ _ => Or.inr hα3)
  simpa [Spaces.Gam] using h

/-- `K(θ) = 3 sin θ cos²θ` is continuous on the angular interval `Iθ`. -/
theorem continuousOn_K :
    ContinuousOn (fun θ : ℝ => Spaces.K θ) Spaces.Iθ := by
  have h : Continuous (fun θ : ℝ => 3 * Real.sin θ * Real.cos θ ^ 2) :=
    (continuous_const.mul Real.continuous_sin).mul (Real.continuous_cos.pow 2)
  simpa [Spaces.K] using h.continuousOn

/-- The angular function `Γ(θ)/c - K(θ)` is continuous on the compact interval `Iθ`,
hence its square is integrable there. -/
theorem integrableOn_GammaK_sq (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) :
    MeasureTheory.IntegrableOn
      (fun θ : ℝ => (Spaces.Gam α θ / Spaces.c α - Spaces.K θ) ^ 2) Spaces.Iθ := by
  have h : ContinuousOn
      (fun θ : ℝ => (Spaces.Gam α θ / Spaces.c α - Spaces.K θ) ^ 2) Spaces.Iθ :=
    (((continuousOn_Gam α hα).div_const _).sub continuousOn_K).pow 2
  simpa [Spaces.Iθ] using h.integrableOn_Icc

end Work.Coercivity
end
end
-- ===== merged: Submission.Work.Coercivity.pz_mul_w =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.Coercivity

/-- The radial weight `w(z) = (1+z)²/z²` has derivative `-2(1+z)/z³` away from `z = 0`.
This is the `z`-derivative appearing in the identity `𝓛(g)·w = g·w + z∂_z(g·w)`. -/
theorem hasDerivAt_w {z : ℝ} (hz : z ≠ 0) :
    HasDerivAt Spaces.w (-2 * (1 + z) / z ^ 3) z := by
  have hnum : HasDerivAt (fun z : ℝ => (1 + z) ^ 2) (2 * (1 + z)) z := by
    convert ((hasDerivAt_id z).const_add 1).pow 2 using 1 <;> (first | rfl | simp)
  have hden : HasDerivAt (fun z : ℝ => z ^ 2) (2 * z) z := by
    convert (hasDerivAt_id z).pow 2 using 1 <;> (first | rfl | simp)
  have hne : z ^ 2 ≠ 0 := pow_ne_zero 2 hz
  have h := hnum.div hden hne
  convert h using 1
  · rfl
  · field_simp
    ring

/-- **Leibniz rule for `∂_z` against the radial weight `w`**: the `z`-derivative of
`f(z,θ)·w(z)` is `∂_z f · w - f · 2(1+z)/z³`. -/
theorem pz_mul_w {f : ℝ → ℝ → ℝ} {z θ : ℝ} (hz : z ≠ 0)
    (hf : HasDerivAt (fun z' => f z' θ) (Spaces.pz f z θ) z) :
    Spaces.pz (fun z θ => f z θ * Spaces.w z) z θ
      = Spaces.pz f z θ * Spaces.w z - f z θ * (2 * (1 + z) / z ^ 3) := by
  have hw := hasDerivAt_w hz
  have hmul := hf.mul hw
  simp only [Spaces.pz]
  have h2 : deriv (fun z' => f z' θ * Spaces.w z') z
      = Spaces.pz f z θ * Spaces.w z + f z θ * (-2 * (1 + z) / z ^ 3) := by
    convert hmul.deriv using 1
  rw [h2, hf.deriv]
  ring

end Work.Coercivity
end
-- ===== merged: Submission.Work.Coercivity.zAux =====
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

/-- The angular weight of the `D_z`-estimate: `w(z)² · sin(2θ)^{-η}`, `η = 99/100`.
This is the weight against which `D_z f` is squared in `EDz`. -/
def Weta (z θ : ℝ) : ℝ := Spaces.w z ^ 2 * (Real.sin (2 * θ)) ^ (-Spaces.eta)

/-- The angular average `(K, f)_{L²_θ}(z) = ∫_θ K(θ) f(z,θ) dθ`; it equals
`z · L12dens K f z`. -/
def Kavg (f : ℝ → ℝ → ℝ) (z : ℝ) : ℝ := ∫ θ in Spaces.Iθ, Spaces.K θ * f z θ

/-- The constant `L₁₂(Transport f)(0)` appearing in the projector term of `𝓛_Γ^T`. -/
def C0 (f : ℝ → ℝ → ℝ) : ℝ := L12f (Transport f) 0

/-- The `𝓛(D_z f)` term (the coercive one). -/
def Z1 (f : ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ := L (Spaces.Dz f)


/-- The `(2zΓ)/(c(1+z)²) · (K,f)_{L²_θ}` term. -/
def Z3 (α : ℝ) (f : ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ :=
  fun z θ => (2 * z * Spaces.Gam α θ / (Spaces.c α * (1 + z) ^ 2)) * Kavg f z

/-- The `-(2z(1-z)Γ)/(c(1+z)³) · L₁₂(f)` term. -/
def Z4 (α : ℝ) (f : ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ :=
  fun z θ => -(2 * z * (1 - z) * Spaces.Gam α θ / (Spaces.c α * (1 + z) ^ 3)) * L12f f z


/-- The `-3(1+z)^{-1} D_θ(D_z f)` transport term. -/
def Z6 (f : ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ :=
  fun z θ => -(3 / (1 + z)) * Spaces.Dth (Spaces.Dz f) z θ

/-- The projector-derivative term `(Γ/c)·L₁₂(Transport f)(0)·2z²(2-z)/(1+z)^4`. -/
def Z7 (α : ℝ) (f : ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ :=
  fun z θ => (Spaces.Gam α θ / Spaces.c α) * C0 f * (2 * z ^ 2 * (2 - z) / (1 + z) ^ 4)


/-- The combined coercive term `Z1 + Z6 = 𝓛(D_z f) - 3(1+z)^{-1} D_θ(D_z f)`. -/
def Z16 (f : ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ := fun z θ => Z1 f z θ + Z6 f z θ


end Work.Coercivity
end
end
-- ===== merged: Submission.Work.Elliptic.DivSinMixedExpansion =====
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

/-! ## Congruence of the slice derivatives on an open set

`pz`, `pth`, `Dz`, `Dth` are local operators, so functions that agree on an open set `V`
have equal images under them at every point of `V`.  The analogues for the fixed set
`nbhU` of `SmoothNbhd` live in `Submission.Work.Spaces.mixed_comm`. -/

/-- Congruence of `pz` under `EqOn` on an open set. -/
private lemma pz_congrOn {g g' : ℝ → ℝ → ℝ} {V : Set (ℝ × ℝ)} (hV : IsOpen V)
    (h : Set.EqOn (Function.uncurry g) (Function.uncurry g') V) {p : ℝ × ℝ} (hp : p ∈ V) :
    pz g p.1 p.2 = pz g' p.1 p.2 := by
  have hnb : ∀ᶠ z' in 𝓝 p.1, (z', p.2) ∈ V :=
    (Continuous.prodMk_left p.2).continuousAt.eventually (hV.mem_nhds hp)
  have hslice : (fun z' => Function.uncurry g (z', p.2)) =ᶠ[𝓝 p.1]
      (fun z' => Function.uncurry g' (z', p.2)) := by
    filter_upwards [hnb] with z' hz'
    exact h hz'
  have := hslice.deriv_eq
  simpa only [pz, Function.uncurry] using this

/-- Congruence of `Dz` under `EqOn` on an open set. -/
private lemma Dz_congrOn {g g' : ℝ → ℝ → ℝ} {V : Set (ℝ × ℝ)} (hV : IsOpen V)
    (h : Set.EqOn (Function.uncurry g) (Function.uncurry g') V) :
    Set.EqOn (Function.uncurry (Dz g)) (Function.uncurry (Dz g')) V := by
  intro p hp
  have hpz := pz_congrOn hV h hp
  show p.1 * pz g p.1 p.2 = p.1 * pz g' p.1 p.2
  rw [hpz]

/-- Congruence of `Dth` under `EqOn` on an open set. -/
private lemma Dth_congrOn {g g' : ℝ → ℝ → ℝ} {V : Set (ℝ × ℝ)} (hV : IsOpen V)
    (h : Set.EqOn (Function.uncurry g) (Function.uncurry g') V) :
    Set.EqOn (Function.uncurry (Dth g)) (Function.uncurry (Dth g')) V := by
  intro p hp
  have hnb : ∀ᶠ θ' in 𝓝 p.2, (p.1, θ') ∈ V :=
    (Continuous.prodMk_right p.1).continuousAt.eventually (hV.mem_nhds hp)
  have hslice : (fun θ' => Function.uncurry g (p.1, θ')) =ᶠ[𝓝 p.2]
      (fun θ' => Function.uncurry g' (p.1, θ')) := by
    filter_upwards [hnb] with θ' hθ'
    exact h hθ'
  have hd := hslice.deriv_eq
  exact congrArg (fun t => Real.sin (2 * p.2) * t) hd

/-- Congruence of `DthIter` under `EqOn` on an open set. -/
private lemma DthIter_congrOn {g g' : ℝ → ℝ → ℝ} {V : Set (ℝ × ℝ)} (hV : IsOpen V)
    (h : Set.EqOn (Function.uncurry g) (Function.uncurry g') V) (i : ℕ) :
    Set.EqOn (Function.uncurry (DthIter i g)) (Function.uncurry (DthIter i g')) V := by
  induction i with
  | zero => exact h
  | succ i ih => simpa only [DthIter_succ] using Dth_congrOn hV ih

/-! ## The main commutation -/


end Work.Spaces

namespace Work.Elliptic

set_option autoImplicit false






end Work.Elliptic
end
end
-- ===== merged: Submission.Work.Elliptic.DivSinSliceFacts =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.Elliptic

open Set


/-- Iterated `D_z = z ∂_z` preserves the vanishing of a function on the angular boundary. -/
theorem vanish_DzIter {f : ℝ → ℝ → ℝ} (hf : Work.Spaces.VanishTheta f) (n : ℕ) :
    Work.Spaces.VanishTheta (Work.Spaces.DzIter n f) := by
  induction n with
  | zero => exact hf
  | succ m ih =>
    refine ⟨fun z => ?_, fun z => ?_⟩
    · have hc : (fun z' : ℝ => Work.Spaces.DzIter m f z' 0) = fun _ => 0 :=
        funext fun z' => ih.1 z'
      simp only [Work.Spaces.DzIter_succ, Work.Spaces.Dz, Work.Spaces.pz, hc, deriv_const,
        mul_zero]
    · have hc : (fun z' : ℝ => Work.Spaces.DzIter m f z' (Real.pi / 2)) = fun _ => 0 :=
        funext fun z' => ih.2 z'
      simp only [Work.Spaces.DzIter_succ, Work.Spaces.Dz, Work.Spaces.pz, hc, deriv_const,
        mul_zero]


end Work.Elliptic
end
-- ===== merged: Submission.Work.FTS.CoercivityStep.Defs =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.CoercivityStep

set_option autoImplicit false

/-! ## The domain and the regularity class -/

/-- The open quadrant `(0,∞) × (0,π/2)` of the self-similar variables.  It is co-null in
`Iz × Iθ`, so it is the correct set on which to impose *pointwise* congruence of the
pairing (`wip`-integrals only see the values a.e.). -/
def Qd : Set (ℝ × ℝ) := Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)

/-- **The linearity class of the `ℋ^k` inner product.**  `f` is smooth on a neighbourhood
of the closed quadrant and its `ℋ^k`-integrand is honest (`HkMem`).

This is the class on which all *constructive* clauses of `IsHkIPCore_fts` are stated.  It
is forced by `Work.Coercivity.not_IsHkIP_H1IP`: an unrestricted additivity clause is
false, because `deriv` is totalised and `HkMem` does not imply a.e. strong measurability.
The class is closed under `+`, `-`, scalar multiples, `D_z` and `D_θ`. -/
def HkReg (α : ℝ) (k : ℕ) (f : ℝ → ℝ → ℝ) : Prop :=
  Work.Spaces.SmoothNbhd f ∧ Work.Spaces.HkMem α k f

/-! ## The specification of an inner product on `ℋ^k`

The paper's §"Higher order derivatives and the inner product on `ℋ^k`" (tex 661–707)
constructs, by induction on `k`, an inner product `(·,·)_{ℋ^k}` together with two
properties: comparability with `|·|_{ℋ^k}` and coercivity of `𝓛_Γ^T`.  The specification
below is that construction's interface, corrected by findings 2 and 3 above.  It is split
into a *core* (the constructive clauses, which are inherited by the inductive step) and
the coercivity clause (which is what the step has to produce). -/

/-- **The constructive part of an admissible inner product on `ℋ^k`.**

* clauses 1–6 are the bilinear/symmetric/positive/congruence part, stated on the class
  `HkReg α k` (see `HkReg` for why the restriction is forced);
* clause 7 is the Cauchy–Schwarz bound, needed by the induction step to pair the
  commutator defect `E₁` with `D_θ f`;
* clauses 8–9 are the paper's upper and lower comparability with `|·|_{ℋ^k}`, stated on
  the admissible class `HkAdm α k` (`Work.Coercivity.HkAdm`), which carries the
  smoothness, the `HkMem` certificates and the `L₁₂`-zero-mode conditions that make the
  paper's projector honest. -/
structure IsHkIPCore_fts (α : ℝ) (k : ℕ) (IP : (ℝ → ℝ → ℝ) → (ℝ → ℝ → ℝ) → ℝ) : Prop where
  /-- Additivity in the first argument. -/
  add_fst : ∀ f₁ f₂ g : ℝ → ℝ → ℝ, HkReg α k f₁ → HkReg α k f₂ → HkReg α k g →
    HkReg α k (f₁ + f₂) → IP (f₁ + f₂) g = IP f₁ g + IP f₂ g
  /-- `ℝ`-homogeneity in the first argument. -/
  smul_fst : ∀ (c : ℝ) (f g : ℝ → ℝ → ℝ), HkReg α k f → HkReg α k g →
    IP (fun z θ => c * f z θ) g = c * IP f g
  /-- Additivity in the second argument. -/
  add_snd : ∀ f g₁ g₂ : ℝ → ℝ → ℝ, HkReg α k f → HkReg α k g₁ → HkReg α k g₂ →
    HkReg α k (g₁ + g₂) → IP f (g₁ + g₂) = IP f g₁ + IP f g₂
  /-- `ℝ`-homogeneity in the second argument. -/
  smul_snd : ∀ (c : ℝ) (f g : ℝ → ℝ → ℝ), HkReg α k f → HkReg α k g →
    IP f (fun z θ => c * g z θ) = c * IP f g
  /-- Symmetry (the paper's `(·,·)_{ℋ^k}` is an inner product). -/
  symm : ∀ f g : ℝ → ℝ → ℝ, IP f g = IP g f
  /-- The pairing only depends on its first argument through the values on the open
  quadrant `Qd`, which is co-null in the domain of integration. -/
  congr_qd : ∀ f f' g : ℝ → ℝ → ℝ, HkReg α k f → HkReg α k f' → HkReg α k g →
    (∀ z θ : ℝ, (z, θ) ∈ Qd → f z θ = f' z θ) → IP f g = IP f' g
  /-- Nonnegativity of the diagonal. -/
  nonneg : ∀ h : ℝ → ℝ → ℝ, 0 ≤ IP h h
  /-- Cauchy–Schwarz for the pairing against the honest `ℋ^k` norm. -/
  cs : ∃ C : ℝ, 0 < C ∧ ∀ f g : ℝ → ℝ → ℝ, HkReg α k f → HkReg α k g →
    |IP f g| ≤ C * Work.Spaces.HkNorm α k f * Work.Spaces.HkNorm α k g
  /-- Lower comparability: the pairing dominates the `ℋ^k` norm squared. -/
  le_self : ∀ f : ℝ → ℝ → ℝ, Work.Coercivity.HkAdm α k f →
    Work.Spaces.HkSq α k f ≤ IP f f
  /-- Upper comparability with a constant depending on `k` only. -/
  upper : ∃ C : ℝ, 0 < C ∧ ∀ f : ℝ → ℝ → ℝ, Work.Coercivity.HkAdm α k f →
    IP f f ≤ C * Work.Spaces.HkSq α k f

/-- **An admissible inner product on `ℋ^k`** (the paper's `(·,·)_{ℋ^k}`): the
constructive clauses `IsHkIPCore_fts` together with the paper's Proposition
`prop:HkCoercivity`, i.e. coercivity of `𝓛_Γ^T` on the admissible class. -/
structure IsHkIP_fts (α : ℝ) (k : ℕ) (IP : (ℝ → ℝ → ℝ) → (ℝ → ℝ → ℝ) → ℝ) : Prop where
  core : IsHkIPCore_fts α k IP
  /-- **Coercivity of `𝓛_Γ^T`** (the paper's Proposition `prop:HkCoercivity`). -/
  coercive : ∃ c : ℝ, 0 < c ∧ ∀ f : ℝ → ℝ → ℝ, Work.Coercivity.HkAdm α k f →
    c * Work.Spaces.HkSq α k f ≤ IP (Work.Coercivity.LGammaT α f) f

/-- **An admissible inner product on `ℋ^k` together with a *named* coercivity
constant.**  This is the form in which the paper's induction is stated: at each level one
must know the coercivity constant explicitly, because the next step's constant
bookkeeping compares it with the Cauchy–Schwarz constant of the level. -/
structure IsHkIPc_fts (α : ℝ) (k : ℕ) (IP : (ℝ → ℝ → ℝ) → (ℝ → ℝ → ℝ) → ℝ) (c : ℝ) : Prop where
  hc : 0 < c
  prop : IsHkIP_fts α k IP
  coercive : ∀ f : ℝ → ℝ → ℝ, Work.Coercivity.HkAdm α k f →
    c * Work.Spaces.HkSq α k f ≤ IP (Work.Coercivity.LGammaT α f) f

/-- **The `ℋ⁴` interface consumed by the a-priori estimate of §Modulation**, restated.

`Work.Construction.IsH4IP` requires its Cauchy–Schwarz, additivity and homogeneity clauses
for *arbitrary* functions; by finding 2 above those clauses are false for the concrete
inner product, so this is the honest version: the same field names, with the constructive
clauses restricted to `HkReg α 4`.  A caller that discharges the a-priori estimate only
ever applies these clauses to the concrete functions `N₀, N, N_*`, which lie in `HkReg α 4`
under the a-priori hypotheses, so the restriction is harmless in use. -/
structure IsH4IP_fts (α : ℝ) (IP : (ℝ → ℝ → ℝ) → (ℝ → ℝ → ℝ) → ℝ) : Prop where
  /-- An admissible inner product on `ℋ⁴`. -/
  hIP : IsHkIP_fts α 4 IP

/-! ## The paper's induction step

`HkIPStep` is `Work.Coercivity.HkIPStep`, the paper's recursion (tex 686)
`(f,g)_{ℋ^k} = (f,g)_{ℋ^{k-1}} + c₁(D_θf,D_θg)_{ℋ^{k-1}} + c₂(D_zf,D_zg)_{ℋ^{k-1}}`.
Its coercivity chain needs two inputs beyond `IsHkIP_fts`: the regularity of the four
participants (`StepReg`) and the two commutator norm bounds (`CommutBounds`), together
with the constant balance named in `StepInputs`. -/

/-- The `D_θ` commutator defect `E₁ = D_θ𝓛_Γ^T f − 𝓛_Γ^T(D_θ f)` of the paper (tex 693). -/
def E₁ (α : ℝ) (f : ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ :=
  Work.Spaces.Dth (Work.Coercivity.LGammaT α f) - Work.Coercivity.LGammaT α (Work.Spaces.Dth f)

/-- The `D_z` commutator defect `E₂ = D_z𝓛_Γ^T f − 𝓛_Γ^T(D_z f)` of the paper (tex 700). -/
def E₂ (α : ℝ) (f : ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ :=
  Work.Spaces.Dz (Work.Coercivity.LGammaT α f) - Work.Coercivity.LGammaT α (Work.Spaces.Dz f)




/-! ## Elementary API -/


theorem IsHkIP_fts.cs {α : ℝ} {k : ℕ}
    {IP : (ℝ → ℝ → ℝ) → (ℝ → ℝ → ℝ) → ℝ} (h : IsHkIP_fts α k IP) :
    ∃ C : ℝ, 0 < C ∧ ∀ f g : ℝ → ℝ → ℝ, HkReg α k f → HkReg α k g →
      |IP f g| ≤ C * Work.Spaces.HkNorm α k f * Work.Spaces.HkNorm α k g := h.core.cs

theorem IsHkIP_fts.le_self {α : ℝ} {k : ℕ}
    {IP : (ℝ → ℝ → ℝ) → (ℝ → ℝ → ℝ) → ℝ} (h : IsHkIP_fts α k IP) {f : ℝ → ℝ → ℝ}
    (hf : Work.Coercivity.HkAdm α k f) : Work.Spaces.HkSq α k f ≤ IP f f :=
  h.core.le_self f hf

theorem IsHkIP_fts.upper {α : ℝ} {k : ℕ}
    {IP : (ℝ → ℝ → ℝ) → (ℝ → ℝ → ℝ) → ℝ} (h : IsHkIP_fts α k IP) :
    ∃ C : ℝ, 0 < C ∧ ∀ f : ℝ → ℝ → ℝ, Work.Coercivity.HkAdm α k f →
      IP f f ≤ C * Work.Spaces.HkSq α k f := h.core.upper

theorem IsHkIP_fts.nonneg {α : ℝ} {k : ℕ}
    {IP : (ℝ → ℝ → ℝ) → (ℝ → ℝ → ℝ) → ℝ} (h : IsHkIP_fts α k IP)
    (u : ℝ → ℝ → ℝ) : 0 ≤ IP u u := h.core.nonneg u

theorem IsH4IP_fts.coercive (α : ℝ) {IP : (ℝ → ℝ → ℝ) → (ℝ → ℝ → ℝ) → ℝ}
    (h : IsH4IP_fts α IP) :
    ∃ c : ℝ, 0 < c ∧ ∀ f : ℝ → ℝ → ℝ, Work.Coercivity.HkAdm α 4 f →
      c * Work.Spaces.HkSq α 4 f ≤ IP (Work.Coercivity.LGammaT α f) f :=
  h.hIP.coercive

theorem IsH4IP_fts.le_self (α : ℝ) {IP : (ℝ → ℝ → ℝ) → (ℝ → ℝ → ℝ) → ℝ}
    (h : IsH4IP_fts α IP) {f : ℝ → ℝ → ℝ} (hf : Work.Coercivity.HkAdm α 4 f) :
    Work.Spaces.HkSq α 4 f ≤ IP f f :=
  h.hIP.le_self hf

theorem IsH4IP_fts.upper (α : ℝ) {IP : (ℝ → ℝ → ℝ) → (ℝ → ℝ → ℝ) → ℝ}
    (h : IsH4IP_fts α IP) :
    ∃ C : ℝ, 0 < C ∧ ∀ f : ℝ → ℝ → ℝ, Work.Coercivity.HkAdm α 4 f →
      IP f f ≤ C * Work.Spaces.HkSq α 4 f :=
  h.hIP.upper

theorem IsH4IP_fts.cs (α : ℝ) {IP : (ℝ → ℝ → ℝ) → (ℝ → ℝ → ℝ) → ℝ}
    (h : IsH4IP_fts α IP) :
    ∃ C : ℝ, 0 < C ∧ ∀ f g : ℝ → ℝ → ℝ, HkReg α 4 f → HkReg α 4 g →
      |IP f g| ≤ C * Work.Spaces.HkNorm α 4 f * Work.Spaces.HkNorm α 4 g :=
  h.hIP.cs

end Work.FTS.CoercivityStep
end
end
-- ===== merged: Submission.Work.FTS.EllSol.FlatFT.pz_contDiffOn_succ =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllSol.FlatFT

/-- The curried `z`-partial derivative `∂_z G` of a function which is `C^{n+1}` on an open
set is `C^n` on that set.  (The `⊤`-version is `Work.Spaces.contDiffOn_uncurry_pz`.) -/
theorem pz_contDiffOn_succ {G : ℝ → ℝ → ℝ} {V : Set (ℝ × ℝ)} (hV : IsOpen V) {n : ℕ}
    (h : ContDiffOn ℝ (n + 1 : ℕ) (Function.uncurry G) V) :
    ContDiffOn ℝ n (Function.uncurry (Work.Spaces.pz G)) V := by
  -- the Fréchet derivative of `uncurry G` is `C^n` on `V`
  have hfd : ContDiffOn ℝ n (fun p : ℝ × ℝ => fderiv ℝ (Function.uncurry G) p) V := by
    have h' := h.fderivWithin (m := (n : WithTop ℕ∞)) hV.uniqueDiffOn (by simp)
    refine h'.congr fun p hp => ?_
    rw [fderivWithin_of_isOpen hV hp]
  -- evaluate it in the direction `(1,0)`
  have hcomp : ContDiffOn ℝ n
      (fun p : ℝ × ℝ => (fderiv ℝ (Function.uncurry G) p) (1, 0)) V := by
    simpa using hfd.clm_apply
      (contDiffOn_const : ContDiffOn ℝ n (fun _ : ℝ × ℝ => ((1, 0) : ℝ × ℝ)) V)
  -- identify `∂_z G` with that evaluation of the Fréchet derivative
  refine hcomp.congr fun p hp => ?_
  have hdiff : DifferentiableAt ℝ (Function.uncurry G) p :=
    (h.differentiableOn (by simp)).differentiableAt (hV.mem_nhds hp)
  simp only [Function.uncurry]
  exact Work.Spaces.pz_eq_fderiv hdiff

end Work.FTS.EllSol.FlatFT
end
-- ===== merged: Submission.Work.FTS.EllipticEst.AngAWeak.difQuotSubDerivBound =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.AngAWeak

open scoped Real Topology
open MeasureTheory Set Filter

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option linter.unusedVariables false

/-! ## The open quadrant and slice facts for `C^n`-functions -/



/-- `z`-slices of a `C^n`-function on an open subset of `ℝ × ℝ`, restricted to a subset of
that open set. -/
private theorem contDiffOn_slice_Icc' {G : ℝ → ℝ → ℝ} {U : Set (ℝ × ℝ)} {n : WithTop ℕ∞}
    (hG : ContDiffOn ℝ n (Function.uncurry G) U) {a b θ : ℝ}
    (hmaps : ∀ s ∈ Set.Icc a b, (s, θ) ∈ U) :
    ContDiffOn ℝ n (fun s => G s θ) (Set.Icc a b) :=
  hG.comp (by fun_prop) hmaps

/-- A `C¹`-function on an open subset of `ℝ × ℝ` has differentiable `z`-slices on that set,
with derivative the `z`-partial `pz`. -/
private theorem hasDerivAt_slice_of_contDiffOn' {G : ℝ → ℝ → ℝ} {U : Set (ℝ × ℝ)}
    (hU : IsOpen U) (hG : ContDiffOn ℝ 1 (Function.uncurry G) U) {u θ : ℝ}
    (hmem : (u, θ) ∈ U) :
    HasDerivAt (fun u' => G u' θ) (Work.Spaces.pz G u θ) u := by
  have hd : DifferentiableAt ℝ (Function.uncurry G) (u, θ) :=
    (hG.differentiableOn (by norm_num)).differentiableAt (hU.mem_nhds hmem)
  have hcur : DifferentiableAt ℝ (fun u' => G u' θ) u :=
    Work.Spaces.differentiableAt_curry_left hd
  simpa [Work.Spaces.pz] using hcur.hasDerivAt

/-- **Second-order Taylor bound for a backward difference quotient.**  If `g` is the
derivative of `f` on `[a,b]`, `g'` the derivative of `g` there, and `a ≤ b - hh` with
`hh > 0`, then the backward difference quotient of `f` at `b` approximates `g b` up to the
integral of `|g'|` over the whole interval `[a,b]`. -/
private theorem abs_difquot_sub_deriv_le' {f g g' : ℝ → ℝ} {a b hh : ℝ}
    (hh_pos : 0 < hh) (ha : a ≤ b - hh)
    (hfcont : ContinuousOn f (Set.Icc (b - hh) b))
    (hfdiff : DifferentiableOn ℝ f (Set.Ioo (b - hh) b))
    (hfderiv : ∀ x ∈ Set.Icc a b, HasDerivAt f (g x) x)
    (hgderiv : ∀ x ∈ Set.Icc a b, HasDerivAt g (g' x) x)
    (hgi : IntervalIntegrable g' volume a b) :
    |(f b - f (b - hh)) / hh - g b| ≤ ∫ x in a..b, |g' x| := by
  have hbhh : b - hh < b := by linarith
  have hab : a ≤ b := le_trans ha (le_of_lt hbhh)
  -- Lagrange's mean value theorem on the slice
  obtain ⟨ξ, hξ, hξderiv⟩ := exists_deriv_eq_slope f hbhh hfcont hfdiff
  have hξle : ξ ≤ b := le_of_lt hξ.2
  have haξ : a ≤ ξ := le_trans ha (le_of_lt hξ.1)
  have hξmem : ξ ∈ Set.Icc a b := ⟨haξ, hξle⟩
  -- the slope is the derivative of `f`, which is `g`
  have hgξ : deriv f ξ = g ξ := (hfderiv ξ hξmem).deriv
  have hslope : (f b - f (b - hh)) / hh = g ξ := by
    have h1 : b - (b - hh) = hh := by ring
    have h2 : (f b - f (b - hh)) / (b - (b - hh)) = g ξ := hξderiv.symm.trans hgξ
    rwa [h1] at h2
  -- the fundamental theorem of calculus for `g` on `[ξ,b]`
  have hftc : ∫ x in ξ..b, g' x = g b - g ξ := by
    refine intervalIntegral.integral_eq_sub_of_hasDerivAt (f := g) (f' := g') ?_ ?_
    · intro x hx
      rw [Set.uIcc_of_le hξle] at hx
      exact hgderiv x ⟨le_trans haξ hx.1, hx.2⟩
    · refine hgi.mono_set ?_
      rw [Set.uIcc_of_le hξle, Set.uIcc_of_le hab]
      exact Set.Icc_subset_Icc_left haξ
  rw [hslope]
  calc |g ξ - g b| = |∫ x in ξ..b, g' x| := by rw [hftc]; exact abs_sub_comm _ _
    _ ≤ ∫ x in ξ..b, |g' x| := intervalIntegral.abs_integral_le_integral_abs hξle
    _ ≤ ∫ x in a..b, |g' x| :=
        intervalIntegral.integral_mono_interval haξ hξle le_rfl
          (Eventually.of_forall fun x => abs_nonneg _) hgi.abs

/-! ## The pointwise mean-value bound on a slice -/

private theorem sliceDifQuotBound' {u : ℝ → ℝ → ℝ}
    (hsm : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry u)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)))
    {z hh : ℝ} (hh0 : 0 < hh) (hhz : hh < z / 2)
    {θ : ℝ} (hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)) :
    |(u z θ - u (z - hh) θ) / hh - Work.Spaces.pz u z θ|
      ≤ ∫ x in (z - hh)..z, |Work.Spaces.pzIter 2 u x θ| := by
  have hz : 0 < z := by linarith
  have hz2 : 0 < z - hh := by linarith
  have hle : z - hh ≤ z := by linarith
  have hmem : ∀ s ∈ Set.Icc (z - hh) z, (s, θ) ∈ Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2) :=
    fun s hs => ⟨Set.mem_Ioi.mpr (by linarith [hs.1]), hθ.1, hθ.2⟩
  have hslice2 : ContDiffOn ℝ 2 (fun s : ℝ => u s θ) (Set.Icc (z - hh) z) :=
    contDiffOn_slice_Icc' (hsm 2) hmem
  have hfcont : ContinuousOn (fun s : ℝ => u s θ) (Set.Icc (z - hh) z) := hslice2.continuousOn
  have hfdiff : DifferentiableOn ℝ (fun s : ℝ => u s θ) (Set.Ioo (z - hh) z) :=
    (hslice2.differentiableOn (by norm_num)).mono Set.Ioo_subset_Icc_self
  have hfderiv : ∀ x ∈ Set.Icc (z - hh) z,
      HasDerivAt (fun s : ℝ => u s θ) (Work.Spaces.pz u x θ) x := fun x hx =>
    hasDerivAt_slice_of_contDiffOn' (isOpen_Ioi.prod isOpen_Ioo) (hsm 1) (hmem x hx)
  have hpz1 : ContDiffOn ℝ 1 (Function.uncurry (Work.Spaces.pz u))
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) :=
    Work.FTS.EllipticEst.Blocks.contDiffOn_uncurry_pz_succ
      (isOpen_Ioi.prod isOpen_Ioo) (n := 1) (hsm 2)
  have hgderiv : ∀ x ∈ Set.Icc (z - hh) z,
      HasDerivAt (fun s : ℝ => Work.Spaces.pz u s θ) (Work.Spaces.pzIter 2 u x θ) x := by
    intro x hx
    have h' := hasDerivAt_slice_of_contDiffOn' (isOpen_Ioi.prod isOpen_Ioo) hpz1 (hmem x hx)
    simpa [Work.Spaces.pzIter_succ] using h'
  have hcs : ContinuousOn (fun s : ℝ => Work.Spaces.pzIter 2 u s θ) (Set.Icc (z - hh) z) :=
    (Work.FTS.EllipticEst.Blocks.PzIterTwoContinuousOn
      (isOpen_Ioi.prod isOpen_Ioo) (hsm 2)).comp (by fun_prop) hmem
  have hgi : IntervalIntegrable (fun s : ℝ => Work.Spaces.pzIter 2 u s θ) volume (z - hh) z := by
    refine ContinuousOn.intervalIntegrable ?_
    rw [Set.uIcc_of_le hle]
    exact hcs
  exact abs_difquot_sub_deriv_le' (f := fun s : ℝ => u s θ)
    (g := fun s : ℝ => Work.Spaces.pz u s θ) (g' := fun s : ℝ => Work.Spaces.pzIter 2 u s θ)
    (a := z - hh) (b := z) (hh := hh) hh0 le_rfl hfcont hfdiff hfderiv hgderiv hgi

/-! ## The Fubini step: integrability of the angular function -/

private theorem integrableOn_integral_abs_pzIter2' {u : ℝ → ℝ → ℝ} {z hh : ℝ} (hh0 : 0 < hh)
    (hbox : MeasureTheory.IntegrableOn
      (Function.uncurry (fun x θ : ℝ =>
        |Work.Spaces.pzIter 2 u x θ| * |Work.Elliptic.sinCos2 θ|))
      (Set.Icc (z - hh) z ×ˢ Work.Spaces.Iθ)) :
    MeasureTheory.IntegrableOn
      (fun θ : ℝ =>
        (∫ x in (z - hh)..z, |Work.Spaces.pzIter 2 u x θ|) * |Work.Elliptic.sinCos2 θ|)
      Work.Spaces.Iθ := by
  have hle : z - hh ≤ z := by linarith
  have hprod : MeasureTheory.Integrable
      (fun p : ℝ × ℝ => |Work.Spaces.pzIter 2 u p.1 p.2| * |Work.Elliptic.sinCos2 p.2|)
      ((MeasureTheory.volume.restrict (Set.Icc (z - hh) z)).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)) := by
    have h := hbox
    rw [MeasureTheory.IntegrableOn, MeasureTheory.Measure.volume_eq_prod,
      ← MeasureTheory.Measure.prod_restrict] at h
    exact h
  have hout := hprod.integral_prod_right
  refine hout.congr ?_
  filter_upwards with θ
  rw [MeasureTheory.integral_mul_const]
  rw [intervalIntegral.integral_of_le hle]
  rw [MeasureTheory.Measure.restrict_congr_set MeasureTheory.Ioc_ae_eq_Icc]

/-! ## The linearity identity for the difference quotient of `F_*` -/

private theorem fstar_sub_difQuot_eq_integral' {u : ℝ → ℝ → ℝ}
    (hψ : ∀ z : ℝ, 0 < z → MeasureTheory.IntegrableOn
      (fun θ : ℝ => u z θ * Work.Elliptic.sinCos2 θ) Work.Spaces.Iθ)
    (hp1 : ∀ z : ℝ, 0 < z → MeasureTheory.IntegrableOn
      (fun θ : ℝ => Work.Spaces.pz u z θ * Work.Elliptic.sinCos2 θ) Work.Spaces.Iθ)
    {z hh : ℝ} (hz : 0 < z) (hh0 : 0 < hh) (hhz : hh < z / 2) :
    (Work.Elliptic.Fstar u z - Work.Elliptic.Fstar u (z - hh)) / hh
        - Work.Elliptic.Fstar (Work.Spaces.pz u) z
      = ∫ θ in Work.Spaces.Iθ,
          ((u z θ - u (z - hh) θ) / hh - Work.Spaces.pz u z θ)
            * Work.Elliptic.sinCos2 θ := by
  have hzhh : 0 < z - hh := by linarith
  have hI1 := hψ z hz
  have hI2 := hψ (z - hh) hzhh
  have hI3 := hp1 z hz
  have hdiv : MeasureTheory.IntegrableOn
      (fun θ => ((u z θ - u (z - hh) θ) / hh) * Work.Elliptic.sinCos2 θ) Work.Spaces.Iθ :=
    MeasureTheory.IntegrableOn.congr_fun ((hI1.sub hI2).div_const hh)
      (fun θ _ => by simp only [Pi.sub_apply]; ring) measurableSet_Icc
  have h1 : Work.Elliptic.Fstar u z - Work.Elliptic.Fstar u (z - hh)
      = ∫ θ in Work.Spaces.Iθ, (u z θ - u (z - hh) θ) * Work.Elliptic.sinCos2 θ := by
    rw [Work.Elliptic.Fstar, Work.Elliptic.Fstar, ← MeasureTheory.integral_sub hI1 hI2]
    exact MeasureTheory.setIntegral_congr_fun measurableSet_Icc (fun θ _ => by ring)
  have h2 : (∫ θ in Work.Spaces.Iθ,
        (u z θ - u (z - hh) θ) * Work.Elliptic.sinCos2 θ) / hh
      = ∫ θ in Work.Spaces.Iθ, ((u z θ - u (z - hh) θ) / hh) * Work.Elliptic.sinCos2 θ := by
    rw [← MeasureTheory.integral_div]
    exact MeasureTheory.setIntegral_congr_fun measurableSet_Icc (fun θ _ => by ring)
  rw [h1, h2, Work.Elliptic.Fstar, ← MeasureTheory.integral_sub hdiv hI3]
  exact MeasureTheory.setIntegral_congr_fun measurableSet_Icc (fun θ _ => by ring)

/-! ## The target -/

theorem difQuotSubDerivBound {u : ℝ → ℝ → ℝ}
    (hsm : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry u)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)))
    (hψ : ∀ z : ℝ, 0 < z → MeasureTheory.IntegrableOn
      (fun θ : ℝ => u z θ * Work.Elliptic.sinCos2 θ) Work.Spaces.Iθ)
    (hp1 : ∀ z : ℝ, 0 < z → MeasureTheory.IntegrableOn
      (fun θ : ℝ => Work.Spaces.pz u z θ * Work.Elliptic.sinCos2 θ) Work.Spaces.Iθ)
    {z hh : ℝ} (hz : 0 < z) (hh0 : 0 < hh) (hhz : hh < z / 2)
    (hbox : MeasureTheory.IntegrableOn
      (Function.uncurry (fun x θ : ℝ =>
        |Work.Spaces.pzIter 2 u x θ| * |Work.Elliptic.sinCos2 θ|))
      (Set.Icc (z - hh) z ×ˢ Work.Spaces.Iθ)) :
    |(Work.Elliptic.Fstar u z - Work.Elliptic.Fstar u (z - hh)) / hh
        - Work.Elliptic.Fstar (Work.Spaces.pz u) z|
      ≤ ∫ θ in Work.Spaces.Iθ,
          (∫ x in (z - hh)..z, |Work.Spaces.pzIter 2 u x θ|)
            * |Work.Elliptic.sinCos2 θ| := by
  have hzhh : 0 < z - hh := by linarith
  have hI3 := hp1 z hz
  -- the pointwise integrand and its two dominating functions
  have hdiv : MeasureTheory.IntegrableOn
      (fun θ => ((u z θ - u (z - hh) θ) / hh) * Work.Elliptic.sinCos2 θ) Work.Spaces.Iθ :=
    MeasureTheory.IntegrableOn.congr_fun (((hψ z hz).sub (hψ (z - hh) hzhh)).div_const hh)
      (fun θ _ => by simp only [Pi.sub_apply]; ring) measurableSet_Icc
  have hφ : MeasureTheory.IntegrableOn
      (fun θ => ((u z θ - u (z - hh) θ) / hh - Work.Spaces.pz u z θ)
        * Work.Elliptic.sinCos2 θ) Work.Spaces.Iθ :=
    MeasureTheory.IntegrableOn.congr_fun (hdiv.sub hI3)
      (fun θ _ => by simp only [Pi.sub_apply]; ring) measurableSet_Icc
  have hTint : MeasureTheory.IntegrableOn
      (fun θ : ℝ =>
        (∫ x in (z - hh)..z, |Work.Spaces.pzIter 2 u x θ|) * |Work.Elliptic.sinCos2 θ|)
      Work.Spaces.Iθ :=
    integrableOn_integral_abs_pzIter2' hh0 hbox
  -- almost-everywhere pointwise domination
  have hae : ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ),
      |((u z θ - u (z - hh) θ) / hh - Work.Spaces.pz u z θ) * Work.Elliptic.sinCos2 θ|
        ≤ (∫ x in (z - hh)..z, |Work.Spaces.pzIter 2 u x θ|)
            * |Work.Elliptic.sinCos2 θ| := by
    have h1 : ∀ᵐ θ ∂(MeasureTheory.volume.restrict (Set.Ioo (0 : ℝ) (Real.pi / 2))),
        |((u z θ - u (z - hh) θ) / hh - Work.Spaces.pz u z θ) * Work.Elliptic.sinCos2 θ|
          ≤ (∫ x in (z - hh)..z, |Work.Spaces.pzIter 2 u x θ|)
              * |Work.Elliptic.sinCos2 θ| :=
      MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioo (fun θ hθ => by
        rw [abs_mul]
        exact mul_le_mul_of_nonneg_right (sliceDifQuotBound' hsm hh0 hhz hθ) (abs_nonneg _))
    exact (MeasureTheory.ae_restrict_congr_set
      (MeasureTheory.Ioo_ae_eq_Icc (a := (0 : ℝ)) (b := Real.pi / 2))).1 h1
  rw [fstar_sub_difQuot_eq_integral' hψ hp1 hz hh0 hhz]
  refine le_trans MeasureTheory.abs_integral_le_integral_abs ?_
  exact MeasureTheory.integral_mono_ae hφ.abs hTint hae

end Work.FTS.EllipticEst.AngAWeak
end
-- ===== merged: Submission.Work.FTS.EllipticEst.AngSecond.Defs =====
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

/-! ## The angular weight and the weighted pairing -/

/-- The angular weight `σ θ = sin(2θ)^{-η}`, `η = Work.Spaces.eta = 99/100`. -/
def sig (θ : ℝ) : ℝ := (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))

/-- The radial factor `w z²` of the weight `W²`. -/
def w2 (z : ℝ) : ℝ := (Work.Spaces.w z) ^ 2

/-- The weighted `L²` pairing `IP g h = ∫_z ∫_θ g z θ * h z θ * w z² * σ θ`. -/
def IP (g h : ℝ → ℝ → ℝ) : ℝ :=
  ∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ, g z θ * h z θ * w2 z * sig θ

/-- Honesty of the pairing `IP g h`: the integrand is integrable, slicewise in `θ` and then in
`z`.  Under this hypothesis the iterated integral of `IP` is the honest value of the pairing. -/
def IPMem (g h : ℝ → ℝ → ℝ) : Prop :=
  (∀ z ∈ Work.Spaces.Iz,
      IntegrableOn (fun θ => g z θ * h z θ * w2 z * sig θ) Work.Spaces.Iθ) ∧
    IntegrableOn
      (fun z => ∫ θ in Work.Spaces.Iθ, g z θ * h z θ * w2 z * sig θ) Work.Spaces.Iz

/-! ## Elementary pointwise facts -/

theorem w_nonneg (z : ℝ) : 0 ≤ Work.Spaces.w z := by
  rw [Work.Spaces.w]; positivity

theorem w_pos {z : ℝ} (hz : 0 < z) : 0 < Work.Spaces.w z := by
  rw [Work.Spaces.w]; positivity

theorem w2_nonneg (z : ℝ) : 0 ≤ w2 z := by rw [w2]; positivity

theorem sin_two_nonneg {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) : 0 ≤ Real.sin (2 * θ) :=
  Real.sin_nonneg_of_nonneg_of_le_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])

theorem sig_nonneg {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) : 0 ≤ sig θ := by
  rw [sig]
  exact Real.rpow_nonneg (sin_two_nonneg hθ) _

/-- On the *open* angular interval the angular weight is at least `1` (so `W ≥ w`). -/
theorem one_le_sig {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) : 1 ≤ sig θ := by
  have hs0 : 0 < Real.sin (2 * θ) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])
  have hs1 : Real.sin (2 * θ) ≤ 1 := Real.sin_le_one _
  have hpos : 0 < (Real.sin (2 * θ)) ^ Work.Spaces.eta := Real.rpow_pos_of_pos hs0 _
  have hle : (Real.sin (2 * θ)) ^ Work.Spaces.eta ≤ 1 :=
    Real.rpow_le_one (le_of_lt hs0) hs1 Work.Spaces.eta_nonneg
  rw [sig, Real.rpow_neg (le_of_lt hs0)]
  rw [← inv_mul_cancel₀ (ne_of_gt hpos)]
  simpa using mul_le_mul_of_nonneg_left hle (le_of_lt (inv_pos.mpr hpos))

/-! ## The pairing of `g` with itself is the square of the weighted `L²`-norm -/

/-- **Pointwise identity.**  `(g · W)² = g² · w² · σ` where `W = w / sin(2θ)^{η/2}`. -/
theorem sq_mul_W (g : ℝ → ℝ → ℝ) {z θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) :
    (g z θ * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2
      = g z θ * g z θ * w2 z * sig θ := by
  rcases eq_or_lt_of_le (sin_two_nonneg hθ) with hs | hs
  · -- endpoint of `Iθ`: both sides vanish
    have hzero : (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2) = 0 := by
      rw [← hs]; exact Real.zero_rpow (by rw [Work.Spaces.eta]; norm_num)
    have hne : -(Work.Spaces.eta) ≠ 0 := by rw [Work.Spaces.eta]; norm_num
    rw [hzero, div_zero, mul_zero, zero_pow (by norm_num)]
    rw [sig, ← hs, Real.zero_rpow hne]
    ring
  · have hw : Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2)
        = Work.Spaces.w z * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta / 2)) := by
      rw [div_eq_mul_inv, Real.rpow_neg (le_of_lt hs)]
    rw [hw, mul_pow, mul_pow]
    have hsq : ((Real.sin (2 * θ)) ^ (-(Work.Spaces.eta / 2))) ^ 2
        = (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) := by
      rw [sq, ← Real.rpow_add hs]
      congr 1
      rw [Work.Spaces.eta]; ring
    rw [hsq]
    simp only [w2, sig, sq]
    ring

theorem L2Sq_mul_W (g : ℝ → ℝ → ℝ) :
    Work.Spaces.L2Sq
        (fun z θ => g z θ * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2)))
      = IP g g := by
  rw [Work.Spaces.L2Sq, IP]
  refine setIntegral_congr_fun measurableSet_Ici fun z _ => ?_
  exact setIntegral_congr_fun measurableSet_Icc fun θ hθ => sq_mul_W g hθ


/-! ## The bilinear form is symmetric, and monotone in the pointwise sense -/


theorem IP_congr {g g' h h' : ℝ → ℝ → ℝ} (hg : ∀ z θ, g z θ = g' z θ)
    (hh : ∀ z θ, h z θ = h' z θ) : IP g h = IP g' h' := by
  rw [IP, IP]
  refine setIntegral_congr_fun measurableSet_Ici fun z _ => ?_
  refine setIntegral_congr_fun measurableSet_Icc fun θ _ => ?_
  rw [hg z θ, hh z θ]

theorem IP_self_nonneg (g : ℝ → ℝ → ℝ) : 0 ≤ IP g g := by
  rw [← L2Sq_mul_W g, Work.Spaces.L2Sq]
  refine setIntegral_nonneg measurableSet_Ici fun z _ => ?_
  exact setIntegral_nonneg measurableSet_Icc fun θ _ => sq_nonneg _


end Work.FTS.EllipticEst.AngSecond
end
end
-- ===== merged: Submission.Work.FTS.EllipticEst.Auxiliary.exists_bound_divCos_box =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open MeasureTheory

namespace Work.FTS.EllipticEst.Auxiliary


end Work.FTS.EllipticEst.Auxiliary
end
-- ===== merged: Submission.Work.FTS.EllipticEst.DzAmgm.LintegralSwapTranslate =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real ENNReal
open MeasureTheory Set

namespace Work.FTS.EllipticEst.DzAmgm

set_option autoImplicit false

/-- **The measure-theoretic core.**  Once the uncurried integrand is a.e. measurable for
the product of the two restricted Lebesgue measures, the iterated integral written with the
translated radial variable `z = z₀ + t` equals the iterated integral with the radial variable
first.  No hypothesis on `V` or `wth` is needed here. -/
theorem lintegralSwapTranslate_of_aem (V : ℝ → ℝ → ℝ) (wth : ℝ → ℝ)
    {z₀ δ : ℝ} (hAEM : AEMeasurable
      (Function.uncurry (fun θ t => ENNReal.ofReal ((Work.Spaces.pzIter 2 V (z₀ + t) θ * wth θ) ^ 2)))
      ((MeasureTheory.volume.restrict (Set.Ioo 0 (Real.pi / 2))).prod
        (MeasureTheory.volume.restrict (Set.Ioo 0 δ)))) :
    (∫⁻ θ in Set.Ioo 0 (Real.pi / 2),
        ∫⁻ t in Set.Ioc 0 δ,
          ENNReal.ofReal ((Work.Spaces.pzIter 2 V (z₀ + t) θ * wth θ) ^ 2))
      = ∫⁻ z in Set.Ioo z₀ (z₀ + δ),
          ∫⁻ θ in Set.Ioo 0 (Real.pi / 2),
            ENNReal.ofReal ((Work.Spaces.pzIter 2 V z θ * wth θ) ^ 2) := by
  -- `Ioc 0 δ` and `Ioo 0 δ` differ by the null set `{δ}`.
  have hIoc : (MeasureTheory.volume.restrict (Set.Ioc 0 δ))
      = MeasureTheory.volume.restrict (Set.Ioo 0 δ) :=
    MeasureTheory.Measure.restrict_congr_set MeasureTheory.Ioo_ae_eq_Ioc.symm
  rw [hIoc]
  -- Tonelli: interchange the two integrals.
  rw [MeasureTheory.lintegral_lintegral_swap hAEM]
  -- Translation invariance of Lebesgue measure: `t ↦ z₀ + t` maps `Ioo 0 δ` onto `Ioo z₀ (z₀+δ)`.
  have hpre : (fun t : ℝ => z₀ + t) ⁻¹' (Set.Ioo z₀ (z₀ + δ)) = Set.Ioo 0 δ := by
    ext t
    simp only [Set.mem_preimage, Set.mem_Ioo]
    constructor <;> intro h <;> constructor <;> linarith
  have key := (MeasureTheory.measurePreserving_add_left MeasureTheory.volume z₀).setLIntegral_comp_preimage_emb
    ((Homeomorph.addLeft z₀).isClosedEmbedding.measurableEmbedding)
    (fun z => ∫⁻ θ in Set.Ioo 0 (Real.pi / 2),
      ENNReal.ofReal ((Work.Spaces.pzIter 2 V z θ * wth θ) ^ 2))
    (Set.Ioo z₀ (z₀ + δ))
  rw [hpre] at key
  exact key

/-- **Measurability of the uncurried integrand.**  Using that the second `z`-partial of `V`
is jointly continuous on the quadrant, and that `wth` is measurable, the integrand
`(θ,t) ↦ ofReal ((∂_z²V (z₀+t) θ · wth θ)²)` is a.e. measurable for the product of the
restricted Lebesgue measures on `(0,π/2)` and `(0,δ)`. -/
theorem aem_uncurry_translate (V : ℝ → ℝ → ℝ) (wth : ℝ → ℝ) (hwthmeas : Measurable wth)
    (hcont : ContinuousOn (Function.uncurry (Work.Spaces.pzIter 2 V))
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)))
    {z₀ δ : ℝ} (hz₀ : 0 < z₀) (hδ : 0 < δ) :
    AEMeasurable
      (Function.uncurry (fun θ t => ENNReal.ofReal ((Work.Spaces.pzIter 2 V (z₀ + t) θ * wth θ) ^ 2)))
      ((MeasureTheory.volume.restrict (Set.Ioo 0 (Real.pi / 2))).prod
        (MeasureTheory.volume.restrict (Set.Ioo 0 δ))) := by
  -- View the product of restricted measures as a restriction of the product measure.
  rw [MeasureTheory.Measure.prod_restrict]
  have hAB : MeasurableSet (Set.Ioo (0 : ℝ) (Real.pi / 2) ×ˢ Set.Ioo (0 : ℝ) δ) :=
    measurableSet_Ioo.prod measurableSet_Ioo
  -- The affine map `(θ,t) ↦ (z₀+t, θ)` sends the box into the quadrant.
  have hmaps : MapsTo (fun p : ℝ × ℝ => (z₀ + p.2, p.1))
      (Set.Ioo (0 : ℝ) (Real.pi / 2) ×ˢ Set.Ioo (0 : ℝ) δ)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) := by
    rintro ⟨θ, t⟩ ⟨hθ, ht⟩
    simp only [Set.mem_prod, Set.mem_Ioo, Set.mem_Ioi] at hθ ht ⊢
    exact ⟨by linarith, ⟨hθ.1, hθ.2⟩⟩
  have hcont' : ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.pzIter 2 V (z₀ + p.2) p.1)
      (Set.Ioo (0 : ℝ) (Real.pi / 2) ×ˢ Set.Ioo (0 : ℝ) δ) :=
    (hcont.comp (((continuous_const.add continuous_snd).prodMk continuous_fst).continuousOn)
      hmaps).congr (fun p _ => rfl)
  have h1 : AEMeasurable (fun p : ℝ × ℝ => Work.Spaces.pzIter 2 V (z₀ + p.2) p.1)
      ((MeasureTheory.volume.prod MeasureTheory.volume).restrict
        (Set.Ioo (0 : ℝ) (Real.pi / 2) ×ˢ Set.Ioo (0 : ℝ) δ)) :=
    hcont'.aemeasurable hAB
  have h2 : AEMeasurable (fun p : ℝ × ℝ => wth p.1)
      ((MeasureTheory.volume.prod MeasureTheory.volume).restrict
        (Set.Ioo (0 : ℝ) (Real.pi / 2) ×ˢ Set.Ioo (0 : ℝ) δ)) :=
    (hwthmeas.comp measurable_fst).aemeasurable
  have h3 : AEMeasurable
      (fun p : ℝ × ℝ => Work.Spaces.pzIter 2 V (z₀ + p.2) p.1 * wth p.1)
      ((MeasureTheory.volume.prod MeasureTheory.volume).restrict
        (Set.Ioo (0 : ℝ) (Real.pi / 2) ×ˢ Set.Ioo (0 : ℝ) δ)) :=
    h1.mul h2
  have h4 : AEMeasurable
      (fun p : ℝ × ℝ => (Work.Spaces.pzIter 2 V (z₀ + p.2) p.1 * wth p.1) ^ 2)
      ((MeasureTheory.volume.prod MeasureTheory.volume).restrict
        (Set.Ioo (0 : ℝ) (Real.pi / 2) ×ˢ Set.Ioo (0 : ℝ) δ)) :=
    (h3.mul h3).congr (Filter.Eventually.of_forall fun p => by simp [Pi.mul_apply, pow_two])
  refine ((ENNReal.measurable_ofReal.comp_aemeasurable h4)).congr ?_
  filter_upwards with p
  simp only [Function.uncurry, Function.comp_apply]



end Work.FTS.EllipticEst.DzAmgm
end
end
-- ===== merged: Submission.Work.FTS.EllipticEst.FstarHkAux =====
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
set_option linter.unusedVariables false

/-! ## The angular profile `D_θ^i (sin 2θ)` -/

/-- `D_θ^i (sin 2θ)`: the angular profile of `D_z^j D_θ^i (φ(z)·sin 2θ)`. -/
def sinProf (i : ℕ) (θ : ℝ) : ℝ :=
  Work.Spaces.DthIter i (fun _ θ' => Real.sin (2 * θ')) 0 θ

@[simp] theorem sinProf_zero (θ : ℝ) : sinProf 0 θ = Real.sin (2 * θ) := by
  simp [sinProf]

/-! ## `D_θ` ignores a radial factor -/

/-- `D_θ (φ(z)·χ(z,θ)) = φ(z)·D_θ χ(z,θ)`: the operator `D_θ` sees only the angular
variable, and a factor depending on `z` alone passes through unchanged. -/
theorem Dth_radial_mul (φ : ℝ → ℝ) (χ : ℝ → ℝ → ℝ) :
    Work.Spaces.Dth (fun z θ => φ z * χ z θ) = fun z θ => φ z * Work.Spaces.Dth χ z θ := by
  funext z θ
  have h : deriv (fun θ' => φ z * χ z θ') θ = φ z * deriv (fun θ' => χ z θ') θ :=
    deriv_const_mul_field (φ z) (v := fun θ' => χ z θ')
  simp only [Work.Spaces.Dth, Work.Spaces.pth]
  rw [h]
  ring

/-- Iterated form of `Dth_radial_mul`. -/
theorem DthIter_radial_mul (φ : ℝ → ℝ) (χ : ℝ → ℝ → ℝ) (i : ℕ) :
    Work.Spaces.DthIter i (fun z θ => φ z * χ z θ)
      = fun z θ => φ z * Work.Spaces.DthIter i χ z θ := by
  induction i with
  | zero => rfl
  | succ n ih =>
      rw [Work.Spaces.DthIter_succ, ih, Work.Spaces.DthIter_succ]
      exact Dth_radial_mul φ (Work.Spaces.DthIter n χ)

/-- A function of the angle alone has a `D_θ`-iterate which does not depend on `z`. -/
theorem DthIter_z_indep (h : ℝ → ℝ) (i : ℕ) :
    ∀ z θ : ℝ, Work.Spaces.DthIter i (fun _ θ' => h θ') z θ
      = Work.Spaces.DthIter i (fun _ θ' => h θ') 0 θ := by
  induction i with
  | zero => intro z θ; rfl
  | succ n ih =>
      intro z θ
      simp only [Work.Spaces.DthIter_succ, Work.Spaces.Dth, Work.Spaces.pth]
      have hfun : (fun θ' => Work.Spaces.DthIter n (fun _ θ' => h θ') z θ')
          = (fun θ' => Work.Spaces.DthIter n (fun _ θ' => h θ') 0 θ') :=
        funext (fun θ' => ih z θ')
      rw [hfun]

/-- The angular profile of the concrete function `fun z θ => Real.sin (2*θ)` is
`sinProf i`. -/
theorem DthIter_sin_eq_sinProf (i : ℕ) (z θ : ℝ) :
    Work.Spaces.DthIter i (fun z θ => Real.sin (2 * θ)) z θ = sinProf i θ := by
  have h := DthIter_z_indep (fun θ => Real.sin (2 * θ)) i z θ
  simpa [sinProf] using h

/-! ## The radial moment `∫_θ D_z^j u z θ · sinθcos²θ dθ` -/

/-- The `j`-th radial moment of `u`: `PsiInt u j z = ∫_θ D_z^j u z θ · sinθcos²θ dθ`.
For `j = 0` this is the angular moment `F_*` (`PsiInt_eq_Fstar`); for `j ≥ 1` it is the
radial coefficient of `D_z^j (F_*·χ)` (`DzIter_PsiInt_mul`). -/
def PsiInt (u : ℝ → ℝ → ℝ) (j : ℕ) (z : ℝ) : ℝ :=
  ∫ θ in Work.Spaces.Iθ, Work.Spaces.DzIter j u z θ * Work.Elliptic.sinCos2 θ

theorem PsiInt_eq_Fstar (u : ℝ → ℝ → ℝ) (z : ℝ) :
    PsiInt u 0 z = Work.Elliptic.Fstar u z := rfl

end Work.FTS.EllipticEst
end
end
-- ===== merged: Submission.Work.FTS.EllipticEst.H2W.Ae.Defs =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.H2W.Ae

set_option autoImplicit false

/-- **The almost-everywhere class of the level-`0` elliptic estimate** (the hypotheses of
`Work.FTS.EllipticEst.H2W.level0Ae`). -/
def AeData (α : ℝ) (u G : ℝ → ℝ → ℝ) : Prop :=
  0 < α ∧ α ≤ 1 / 4 ∧
    (∀ z, 0 < z → ∀ θ, 0 < θ → θ < Real.pi / 2 → Work.Elliptic.bslOp α u z θ = G z θ) ∧
    (∀ z, u z 0 = 0) ∧ (∀ z, u z (Real.pi / 2) = 0) ∧
    (∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry u)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2))) ∧
    Work.Spaces.HkMem α 0 G ∧
    Work.Spaces.HkMem α 0 (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 u z θ) ∧
    Work.Spaces.HkMem α 0 (Work.Spaces.pthIter 2 u) ∧
    (∀ᵐ z ∂(MeasureTheory.volume.restrict (Set.Ioi 0)), Work.Elliptic.Fstar u z = 0) ∧
    (∀ᵐ z ∂(MeasureTheory.volume.restrict (Set.Ioi 0)), Work.Elliptic.Fstar G z = 0)

/-- The open quadrant `(0,∞) × (0,π/2)`. -/
def quad : Set (ℝ × ℝ) := Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)

/-- The radial first derivative `z ∂_z u` (`D_z u`). -/
def grad (u : ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ := fun z θ => z * Work.Spaces.pz u z θ

/-- The radial second derivative `z^2 ∂_zz u`. -/
def rad2 (u : ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ := fun z θ => z ^ 2 * Work.Spaces.pzIter 2 u z θ

/-- The angular first order term `∂_θ (tan θ · u)`. -/
def ang1 (u : ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ :=
  fun z θ => Work.Spaces.pth (fun z θ => Real.tan θ * u z θ) z θ

/-- The angular second derivative `∂_θθ u`. -/
def ang2 (u : ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ := Work.Spaces.pthIter 2 u

/-- The `ρ`-norm of `g`, i.e. the square root of `HkSq α 0 g`. -/
def nrm (α : ℝ) (g : ℝ → ℝ → ℝ) : ℝ := Real.sqrt (Work.Spaces.HkSq α 0 g)

theorem AeData.hα {α : ℝ} {u G : ℝ → ℝ → ℝ} (h : AeData α u G) : 0 < α := h.1

theorem AeData.hα4 {α : ℝ} {u G : ℝ → ℝ → ℝ} (h : AeData α u G) : α ≤ 1 / 4 := h.2.1

theorem AeData.eq {α : ℝ} {u G : ℝ → ℝ → ℝ} (h : AeData α u G) :
    ∀ z, 0 < z → ∀ θ, 0 < θ → θ < Real.pi / 2 → Work.Elliptic.bslOp α u z θ = G z θ :=
  h.2.2.1

theorem AeData.dirZero {α : ℝ} {u G : ℝ → ℝ → ℝ} (h : AeData α u G) : ∀ z, u z 0 = 0 :=
  h.2.2.2.1

theorem AeData.dirPi {α : ℝ} {u G : ℝ → ℝ → ℝ} (h : AeData α u G) :
    ∀ z, u z (Real.pi / 2) = 0 := h.2.2.2.2.1

theorem AeData.smooth {α : ℝ} {u G : ℝ → ℝ → ℝ} (h : AeData α u G) :
    ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry u)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) :=
  h.2.2.2.2.2.1

theorem AeData.memG {α : ℝ} {u G : ℝ → ℝ → ℝ} (h : AeData α u G) :
    Work.Spaces.HkMem α 0 G := h.2.2.2.2.2.2.1

theorem AeData.memRad2 {α : ℝ} {u G : ℝ → ℝ → ℝ} (h : AeData α u G) :
    Work.Spaces.HkMem α 0 (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 u z θ) :=
  h.2.2.2.2.2.2.2.1

theorem AeData.memAng2 {α : ℝ} {u G : ℝ → ℝ → ℝ} (h : AeData α u G) :
    Work.Spaces.HkMem α 0 (Work.Spaces.pthIter 2 u) := h.2.2.2.2.2.2.2.2.1

theorem AeData.momU {α : ℝ} {u G : ℝ → ℝ → ℝ} (h : AeData α u G) :
    ∀ᵐ z ∂(MeasureTheory.volume.restrict (Set.Ioi 0)), Work.Elliptic.Fstar u z = 0 :=
  h.2.2.2.2.2.2.2.2.2.1

theorem AeData.momG {α : ℝ} {u G : ℝ → ℝ → ℝ} (h : AeData α u G) :
    ∀ᵐ z ∂(MeasureTheory.volume.restrict (Set.Ioi 0)), Work.Elliptic.Fstar G z = 0 :=
  h.2.2.2.2.2.2.2.2.2.2

end Work.FTS.EllipticEst.H2W.Ae
end
end
-- ===== merged: Submission.Work.FTS.EllipticEst.ScaleAPI =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology Interval
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst

set_option autoImplicit false
set_option linter.unusedSimpArgs false

/-! ## The derivative operators commute with scalar multiplication -/

theorem pz_smul (c : ℝ) (f : ℝ → ℝ → ℝ) : Work.Spaces.pz (c • f) = c • Work.Spaces.pz f := by
  funext z θ
  simp only [Work.Spaces.pz, Pi.smul_apply, smul_eq_mul]
  exact deriv_const_mul_field c

theorem pth_smul (c : ℝ) (f : ℝ → ℝ → ℝ) : Work.Spaces.pth (c • f) = c • Work.Spaces.pth f := by
  funext z θ
  simp only [Work.Spaces.pth, Pi.smul_apply, smul_eq_mul]
  exact deriv_const_mul_field c

theorem pzIter_smul (c : ℝ) (f : ℝ → ℝ → ℝ) (n : ℕ) :
    Work.Spaces.pzIter n (c • f) = c • Work.Spaces.pzIter n f := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [Work.Spaces.pzIter_succ, ih, pz_smul, Work.Spaces.pzIter_succ]

theorem pthIter_smul (c : ℝ) (f : ℝ → ℝ → ℝ) (n : ℕ) :
    Work.Spaces.pthIter n (c • f) = c • Work.Spaces.pthIter n f := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [Work.Spaces.pthIter_succ, ih, pth_smul, Work.Spaces.pthIter_succ]

theorem Dz_smul (c : ℝ) (f : ℝ → ℝ → ℝ) : Work.Spaces.Dz (c • f) = c • Work.Spaces.Dz f := by
  funext z θ
  simp only [Work.Spaces.Dz, pz_smul, Pi.smul_apply, smul_eq_mul]
  ring

theorem Dth_smul (c : ℝ) (f : ℝ → ℝ → ℝ) : Work.Spaces.Dth (c • f) = c • Work.Spaces.Dth f := by
  funext z θ
  simp only [Work.Spaces.Dth, pth_smul, Pi.smul_apply, smul_eq_mul]
  ring

theorem DzIter_smul (c : ℝ) (f : ℝ → ℝ → ℝ) (n : ℕ) :
    Work.Spaces.DzIter n (c • f) = c • Work.Spaces.DzIter n f := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [Work.Spaces.DzIter_succ, ih, Dz_smul, Work.Spaces.DzIter_succ]

theorem DthIter_smul (c : ℝ) (f : ℝ → ℝ → ℝ) (n : ℕ) :
    Work.Spaces.DthIter n (c • f) = c • Work.Spaces.DthIter n f := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [Work.Spaces.DthIter_succ, ih, Dth_smul, Work.Spaces.DthIter_succ]

theorem mixed_smul (c : ℝ) (f : ℝ → ℝ → ℝ) (j i : ℕ) :
    Work.Spaces.mixed j i (c • f) = c • Work.Spaces.mixed j i f := by
  simp only [Work.Spaces.mixed, DzIter_smul, DthIter_smul]

/-! ## The norm functionals are homogeneous -/

theorem HkIntegrand_smul (c : ℝ) (α : ℝ) (k : ℕ) (f : ℝ → ℝ → ℝ) (z θ : ℝ) :
    Work.Spaces.HkIntegrand α k (c • f) z θ = c ^ 2 * Work.Spaces.HkIntegrand α k f z θ := by
  simp only [Work.Spaces.HkIntegrand, DzIter_smul, mixed_smul, Pi.smul_apply, smul_eq_mul]
  rw [mul_add]
  congr 1
  · rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by ring
  · rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    by_cases h : (1 ≤ i ∧ i + j ≤ k)
    · simp only [if_pos h]
      ring
    · simp only [if_neg h]
      ring

theorem HkSq_smul (c : ℝ) (α : ℝ) (k : ℕ) (f : ℝ → ℝ → ℝ) :
    Work.Spaces.HkSq α k (c • f) = c ^ 2 * Work.Spaces.HkSq α k f := by
  have hfun : (fun z => ∫ θ in Work.Spaces.Iθ,
        Work.Spaces.HkIntegrand α k (c • f) z θ)
      = fun z => c ^ 2 * ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k f z θ := by
    funext z
    rw [show (fun θ => Work.Spaces.HkIntegrand α k (c • f) z θ)
        = fun θ => c ^ 2 * Work.Spaces.HkIntegrand α k f z θ from
      funext fun θ => HkIntegrand_smul c α k f z θ]
    exact integral_const_mul _ _
  simp only [Work.Spaces.HkSq]
  rw [hfun]
  exact integral_const_mul _ _

theorem HkNorm_smul (c : ℝ) (α : ℝ) (k : ℕ) (f : ℝ → ℝ → ℝ) :
    Work.Spaces.HkNorm α k (c • f) = |c| * Work.Spaces.HkNorm α k f := by
  rw [Work.Spaces.HkNorm, HkSq_smul, Work.Spaces.HkNorm]
  rw [Real.sqrt_mul (sq_nonneg c), Real.sqrt_sq_eq_abs]



/-! ## Honesty is invariant under a nonzero scalar -/

theorem HkMem_smul {c : ℝ} (_hc : c ≠ 0) (α : ℝ) (k : ℕ) {f : ℝ → ℝ → ℝ}
    (h : Work.Spaces.HkMem α k f) : Work.Spaces.HkMem α k (c • f) := by
  constructor
  · intro z hz
    have h1 : (fun θ : ℝ => Work.Spaces.HkIntegrand α k (c • f) z θ)
        = fun θ => c ^ 2 * Work.Spaces.HkIntegrand α k f z θ :=
      funext fun θ => HkIntegrand_smul c α k f z θ
    rw [h1]
    exact (h.1 z hz).const_mul _
  · have h1 : (fun z : ℝ => ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k (c • f) z θ)
        = fun z => c ^ 2 * ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k f z θ := by
      funext z
      rw [show (fun θ => Work.Spaces.HkIntegrand α k (c • f) z θ)
          = fun θ => c ^ 2 * Work.Spaces.HkIntegrand α k f z θ from
        funext fun θ => HkIntegrand_smul c α k f z θ]
      exact integral_const_mul _ _
    rw [h1]
    exact h.2.const_mul _


/-! ## `prop:H2` is `prop:Hk` at `k = 2` -/


end Work.FTS.EllipticEst
end
end
-- ===== merged: Submission.Work.FTS.EllipticEst.TT.WeakDefs =====
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

/-- **The weak hypothesis class of the elliptic `ℋ^k` estimate.**

The only difference with respect to the hypotheses written out in `propHk_core` is that the two
moment conditions (`OrthCond`) are demanded only for `z > 0`: the full `OrthCond` holds for every
real `z` and implies this version. -/
def EllWeakPos (α : ℝ) (k : ℕ) (F Ψ : ℝ → ℝ → ℝ) : Prop :=
  (∀ z, 0 < z → ∀ θ, 0 < θ → θ < Real.pi / 2 → Work.Elliptic.bslOp α Ψ z θ = F z θ) ∧
  (∀ z, Ψ z 0 = 0) ∧ (∀ z, Ψ z (Real.pi / 2) = 0) ∧
  (∀ z, 0 < z → Work.Elliptic.Fstar F z = 0) ∧
  (∀ z, 0 < z → Work.Elliptic.Fstar Ψ z = 0) ∧
  (∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry Ψ) (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2))) ∧
  Work.Spaces.HkMem α k F ∧
  Work.Spaces.HkMem α k (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) ∧
  Work.Spaces.HkMem α k (Work.Spaces.pthIter 2 Ψ) ∧
  -- the *diagonal second-order honesty* `HkMem α k (∂_θθ(z∂_zΨ))`: the clause Step 2 of
  -- `prop:H2` consumes (`AeI1Paper_repair.md`), not implied by the other fields
  -- (`H2W/AeWAux/NOTES_aeI1Data_FALSE.md`).
  Work.Spaces.HkMem α k (fun z θ => z * Work.Spaces.pz (Work.Spaces.pthIter 2 Ψ) z θ)

/-- **The level-`0` estimate** (Elgindi, Proposition `prop:L2` with the weights
`w²/sin^η`, i.e. Steps 1 and 2 of the proof of Proposition `prop:H2`), in the form in which the
slices `D_z^jΨ` consume it: with `C` universal, for `0 < α ≤ 1/4` and every datum of the weak
class,

  `α⁴|z²∂_zzΨ|²_{ℋ⁰} + |∂_θθΨ|²_{ℋ⁰} ≤ C |F|²_{ℋ⁰}`,

where `|·|_{ℋ⁰}` is the `η`-weighted `L²`-norm `w/sin(2θ)^{η/2}`. -/
def EllWeak0 (C : ℝ) : Prop :=
  ∀ (α : ℝ) (F Ψ : ℝ → ℝ → ℝ), 0 < α → α ≤ 1 / 4 → EllWeakPos α 0 F Ψ →
    α ^ 4 * Work.Spaces.HkSq α 0 (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ)
      + Work.Spaces.HkSq α 0 (Work.Spaces.pthIter 2 Ψ) ≤ C * Work.Spaces.HkSq α 0 F

/-- **The estimate at level `k`** (the conclusion of `prop:Hk`, with a named constant). -/
def EllEstUnif (k : ℕ) (C : ℝ) : Prop :=
  ∀ (α : ℝ) (F Ψ : ℝ → ℝ → ℝ), 0 < α → α ≤ 1 / 4 → EllWeakPos α k F Ψ →
    α ^ 2 * Work.Spaces.HkNorm α k (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ)
      + Work.Spaces.HkNorm α k (Work.Spaces.pthIter 2 Ψ) ≤ C * Work.Spaces.HkNorm α k F

/-! ## Elementary API of the hypothesis bundle -/

theorem EllWeakPos.eq {α : ℝ} {k : ℕ} {F Ψ : ℝ → ℝ → ℝ} (h : EllWeakPos α k F Ψ) :
    ∀ z, 0 < z → ∀ θ, 0 < θ → θ < Real.pi / 2 → Work.Elliptic.bslOp α Ψ z θ = F z θ :=
  h.1

theorem EllWeakPos.zero {α : ℝ} {k : ℕ} {F Ψ : ℝ → ℝ → ℝ} (h : EllWeakPos α k F Ψ) :
    ∀ z, Ψ z 0 = 0 := h.2.1

theorem EllWeakPos.pi_half {α : ℝ} {k : ℕ} {F Ψ : ℝ → ℝ → ℝ} (h : EllWeakPos α k F Ψ) :
    ∀ z, Ψ z (Real.pi / 2) = 0 := h.2.2.1

theorem EllWeakPos.orthF {α : ℝ} {k : ℕ} {F Ψ : ℝ → ℝ → ℝ} (h : EllWeakPos α k F Ψ) :
    ∀ z, 0 < z → Work.Elliptic.Fstar F z = 0 := h.2.2.2.1

theorem EllWeakPos.orthPsi {α : ℝ} {k : ℕ} {F Ψ : ℝ → ℝ → ℝ} (h : EllWeakPos α k F Ψ) :
    ∀ z, 0 < z → Work.Elliptic.Fstar Ψ z = 0 := h.2.2.2.2.1

theorem EllWeakPos.smooth {α : ℝ} {k : ℕ} {F Ψ : ℝ → ℝ → ℝ} (h : EllWeakPos α k F Ψ) :
    ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry Ψ)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) := h.2.2.2.2.2.1

theorem EllWeakPos.memF {α : ℝ} {k : ℕ} {F Ψ : ℝ → ℝ → ℝ} (h : EllWeakPos α k F Ψ) :
    Work.Spaces.HkMem α k F := h.2.2.2.2.2.2.1

theorem EllWeakPos.memA {α : ℝ} {k : ℕ} {F Ψ : ℝ → ℝ → ℝ} (h : EllWeakPos α k F Ψ) :
    Work.Spaces.HkMem α k (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) :=
  h.2.2.2.2.2.2.2.1

theorem EllWeakPos.memB {α : ℝ} {k : ℕ} {F Ψ : ℝ → ℝ → ℝ} (h : EllWeakPos α k F Ψ) :
    Work.Spaces.HkMem α k (Work.Spaces.pthIter 2 Ψ) := h.2.2.2.2.2.2.2.2.1


/-- **The diagonal second-order honesty** of the weak class: `HkMem α k (∂_θθ(z∂_zΨ))`, i.e. the
honesty of `fun z θ => z * ∂_z∂_θθΨ`.  This is the conjunct Step 2 of `prop:H2` consumes; see
`AeI1Paper_repair.md`. -/
theorem EllWeakPos.memZPth2 {α : ℝ} {k : ℕ} {F Ψ : ℝ → ℝ → ℝ} (h : EllWeakPos α k F Ψ) :
    Work.Spaces.HkMem α k (fun z θ => z * Work.Spaces.pz (Work.Spaces.pthIter 2 Ψ) z θ) :=
  h.2.2.2.2.2.2.2.2.2


/-! ## The assembly

The three analytic inputs listed in the module docstring give the target.  The proof is the
induction on `k`: level `2` is the paper's Proposition `prop:H2`, and the passage from `k-1` to
`k` (`k ≥ 3`) is the paper's §"General `ℋ^k` Case".  Both are stated with a constant that is
*uniform in `α ∈ (0,1/4]`*, which is what makes the induction produce the `α`-uniform constant
demanded by `prop:Hk`. -/

theorem propHk_core_of (h0 : ∃ C : ℝ, 0 < C ∧ EllWeak0 C)
    (h2 : ∃ C : ℝ, 0 < C ∧ EllEstUnif 2 C)
    (hstep : ∀ k : ℕ, 3 ≤ k → (∃ C : ℝ, 0 < C ∧ EllEstUnif (k - 1) C) →
      ∃ C : ℝ, 0 < C ∧ EllEstUnif k C) :
    ∀ k : ℕ, 2 ≤ k → ∃ C : ℝ, 0 < C ∧ EllEstUnif k C := by
  obtain ⟨C2, hC2pos, hC2⟩ := h2
  intro k hk
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    rcases Nat.lt_or_eq_of_le hk with hlt | heq
    · exact hstep k hlt (ih (k - 1) (by omega) (by omega))
    · subst heq
      exact ⟨C2, hC2pos, hC2⟩

end Work.FTS.EllipticEst.TT
end
end
-- ===== merged: Submission.Work.FTS.EllipticEst.ThetaU.Defs =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# Local vocabulary of the `∂_θ U`-transfer estimate (`ThetaU`)

This small module collects the definitions shared by the pieces of the proof of

  `Work.FTS.EllipticEst.ThetaU.pthU_EllResid_le`:

`| -3 ∂_θW - α z ∂_θ∂_zW |_{ℋ^k} ≤ C ( |F|_{ℋ^k} + |∂_θ∂_θW|_{ℋ^k} + α² |z²∂_zzΨ|_{ℋ^k} )`

for `W = EllResid α F Ψ` and elliptic data `EllHyp α k F Ψ`.  Nothing else lives here, so that
the pieces can import it without importing each other.
-/

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.ThetaU

set_option autoImplicit false

/-- **The smoothness class of the transfer estimates.**  `G` is `C^n` for every `n` on the
product of the open half-line `(0,∞)` in `z` with an open neighbourhood of the closed angular
interval `[0,π/2]`.

This is deliberately *weaker* than `Work.Spaces.SmoothNbhd`, which asks for `ContDiffOn ℝ ⊤` on
`Ioi (-1) ×ˢ Ioo (-1) (π/2+1)`; in this Mathlib `⊤ : ℕ∞` is analyticity, so `SmoothNbhd` forces
analyticity in `z` down to `z = -1`, which the residual `Ψ + G_{\rm star}(z) sin 2θ` cannot
satisfy (`G_{\rm star} = -(1/(4α))L₁₂(F)` is only known to be smooth on `(0,∞)`).  The
`θ`-slices of the residual *are* analytic (a constant in `θ` times `sin 2θ` plus the analytic
`Ψ`), which is what the slice estimates need. -/
def SmoothOpenθ (G : ℝ → ℝ → ℝ) : Prop :=
  ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry G)
    (Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (-1 : ℝ) (Real.pi / 2 + 1))

theorem SmoothOpenθ.mono {G : ℝ → ℝ → ℝ} (h : SmoothOpenθ G) (n : ℕ) :
    ContDiffOn ℝ n (Function.uncurry G)
      (Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (-1 : ℝ) (Real.pi / 2 + 1)) := h n

/-- The uncurried form of a `SmoothOpenθ` function is `C^n` at every point of
`(0,∞) × (-1, π/2+1)`. -/
theorem SmoothOpenθ.contDiffAt {G : ℝ → ℝ → ℝ} (h : SmoothOpenθ G) (n : ℕ) {z θ : ℝ}
    (hz : 0 < z) (hθ : θ ∈ Set.Ioo (-1 : ℝ) (Real.pi / 2 + 1)) :
    ContDiffAt ℝ n (Function.uncurry G) (z, θ) :=
  (h n).contDiffAt ((isOpen_Ioi.prod isOpen_Ioo).mem_nhds ⟨hz, hθ⟩)

/-- Each `θ`-slice of a `SmoothOpenθ` function is differentiable at every interior angle. -/
theorem SmoothOpenθ.differentiableAt_slice {G : ℝ → ℝ → ℝ} (h : SmoothOpenθ G) {z θ : ℝ}
    (hz : 0 < z) (hθ : θ ∈ Set.Ioo (-1 : ℝ) (Real.pi / 2 + 1)) :
    DifferentiableAt ℝ (fun θ' : ℝ => G z θ') θ :=
  ((h.contDiffAt 2 hz hθ).comp θ (contDiffAt_const.prodMk contDiffAt_id)).differentiableAt
    (by norm_num)

/-- The two iterated slice derivatives of a `SmoothOpenθ` function agree: Clairaut. -/
theorem SmoothOpenθ.pz_pth_comm {G : ℝ → ℝ → ℝ} (h : SmoothOpenθ G) {z θ : ℝ}
    (hz : 0 < z) (hθ : θ ∈ Set.Ioo (-1 : ℝ) (Real.pi / 2 + 1)) :
    Work.Spaces.pz (Work.Spaces.pth G) z θ = Work.Spaces.pth (Work.Spaces.pz G) z θ :=
  Work.Spaces.pz_pth_comm (h.contDiffAt 2 hz hθ)


end Work.FTS.EllipticEst.ThetaU
end
end
-- ===== merged: Submission.Work.FTS.EllipticEst.moment_ibp =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst

/-- **The two integrations by parts on `(0,∞)` behind the radial energy identity.**  `∫F·H'' = ∫F''·H` and `∫G·H' = -∫G'·H`, with the boundary terms `F·H'`, `F'·H` and `G·H` vanishing at `0⁺` and at `+∞`, integrability of the six products, and differentiability of `F, F', G, H, H'` on `(0,∞)`.  Proof: `MeasureTheory.integral_Ioi_mul_deriv_eq_deriv_mul` twice (with `(u,v) = (F,H')` and `(u,v) = (F',H)`) for the first identity, once (with `(u,v) = (G,H)`) for the second. -/
theorem moment_ibp (F F' F'' G G' H H' H'' : ℝ → ℝ)
    (hF : ∀ z ∈ Set.Ioi (0 : ℝ), HasDerivAt F (F' z) z)
    (hF' : ∀ z ∈ Set.Ioi (0 : ℝ), HasDerivAt F' (F'' z) z)
    (hG : ∀ z ∈ Set.Ioi (0 : ℝ), HasDerivAt G (G' z) z)
    (hH : ∀ z ∈ Set.Ioi (0 : ℝ), HasDerivAt H (H' z) z)
    (hH' : ∀ z ∈ Set.Ioi (0 : ℝ), HasDerivAt H' (H'' z) z)
    (h1 : MeasureTheory.IntegrableOn (fun z => F z * H'' z) (Set.Ioi (0 : ℝ)))
    (h2 : MeasureTheory.IntegrableOn (fun z => F' z * H' z) (Set.Ioi (0 : ℝ)))
    (h3 : MeasureTheory.IntegrableOn (fun z => F'' z * H z) (Set.Ioi (0 : ℝ)))
    (h4 : MeasureTheory.IntegrableOn (fun z => G z * H' z) (Set.Ioi (0 : ℝ)))
    (h5 : MeasureTheory.IntegrableOn (fun z => G' z * H z) (Set.Ioi (0 : ℝ)))
    (hb1 : Filter.Tendsto (fun z => F z * H' z) (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0))
    (hb2 : Filter.Tendsto (fun z => F z * H' z) Filter.atTop (nhds 0))
    (hb3 : Filter.Tendsto (fun z => F' z * H z) (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0))
    (hb4 : Filter.Tendsto (fun z => F' z * H z) Filter.atTop (nhds 0))
    (hb5 : Filter.Tendsto (fun z => G z * H z) (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0))
    (hb6 : Filter.Tendsto (fun z => G z * H z) Filter.atTop (nhds 0)) :
    (∫ z in Set.Ioi (0 : ℝ), F z * H'' z = ∫ z in Set.Ioi (0 : ℝ), F'' z * H z) ∧
      (∫ z in Set.Ioi (0 : ℝ), G z * H' z = - ∫ z in Set.Ioi (0 : ℝ), G' z * H z) := by
  -- First integration by parts: `(u, v) = (F, H')`, so that `u·v' = F·H''` and `u'·v = F'·H'`.
  have e1 := MeasureTheory.integral_Ioi_mul_deriv_eq_deriv_mul
    (a := (0 : ℝ)) (a' := (0 : ℝ)) (b' := (0 : ℝ))
    (u := F) (u' := F') (v := H') (v' := H'') hF hH' h1 h2 hb1 hb2
  -- Second integration by parts: `(u, v) = (F', H)`, so that `u·v' = F'·H'` and `u'·v = F''·H`.
  have e2 := MeasureTheory.integral_Ioi_mul_deriv_eq_deriv_mul
    (a := (0 : ℝ)) (a' := (0 : ℝ)) (b' := (0 : ℝ))
    (u := F') (u' := F'') (v := H) (v' := H') hF' hH h2 h3 hb3 hb4
  -- Third integration by parts: `(u, v) = (G, H)`, so that `u·v' = G·H'` and `u'·v = G'·H`.
  have e3 := MeasureTheory.integral_Ioi_mul_deriv_eq_deriv_mul
    (a := (0 : ℝ)) (a' := (0 : ℝ)) (b' := (0 : ℝ))
    (u := G) (u' := G') (v := H) (v' := H') hG hH h4 h5 hb5 hb6
  refine ⟨?_, ?_⟩
  · linarith
  · linarith

end Work.FTS.EllipticEst
end
-- ===== merged: Submission.Work.FTS.EllipticEst.weight_algebra_fts =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst

open Filter

/-! ## Helper lemmas: the two derived weights and their derivatives

Throughout, the two derived weights are the rational functions

* `F z = z ^ 2 * w z ^ 2 = (1+z)^4 / z^2`,
* `G z = z * w z ^ 2 = (1+z)^4 / z^3`,

and all derivatives are computed by comparing with the rational functions
`(1+y)^4 / y^2`, `(1+y)^4 / y^3` and `2*(y-1)*(1+y)^3/y^3`, which agree with the
derived weights in a *neighbourhood* of every `z ≠ 0` (the punctured line is a
neighbourhood of `z`), so that `Filter.EventuallyEq.deriv_eq` transfers the
derivative. -/

/-- The first derived weight as a rational function: `z ^ 2 * w z ^ 2 = (1+z)^4/z^2`. -/
private lemma sq_mul_w_sq (z : ℝ) (hz : z ≠ 0) :
    z ^ 2 * (Work.Spaces.w z) ^ 2 = (1 + z) ^ 4 / z ^ 2 := by
  rw [Work.Spaces.w]
  field_simp

/-- The second derived weight as a rational function: `z * w z ^ 2 = (1+z)^4/z^3`. -/
private lemma mul_w_sq (z : ℝ) (hz : z ≠ 0) :
    z * (Work.Spaces.w z) ^ 2 = (1 + z) ^ 4 / z ^ 3 := by
  rw [Work.Spaces.w]
  field_simp

/-- The derivative of the rational function `(1+y)^4/y^2`. -/
private lemma deriv_rational_4_2 (z : ℝ) (hz : z ≠ 0) :
    deriv (fun y : ℝ => (1 + y) ^ 4 / y ^ 2) z = 2 * (z - 1) * (1 + z) ^ 3 / z ^ 3 := by
  rw [deriv_fun_div (c := fun y : ℝ => (1 + y) ^ 4) (d := fun y : ℝ => y ^ 2)
        (by fun_prop) (by fun_prop) (pow_ne_zero 2 hz),
      deriv_fun_pow (f := fun y : ℝ => 1 + y) (by fun_prop) 4,
      deriv_fun_pow (f := fun y : ℝ => y) (by fun_prop) 2,
      deriv_const_add (f := fun y : ℝ => y) (1 : ℝ), congr_fun deriv_id'' z]
  field_simp
  ring

/-- The derivative of the rational function `(1+y)^4/y^3`. -/
private lemma deriv_rational_4_3 (z : ℝ) (hz : z ≠ 0) :
    deriv (fun y : ℝ => (1 + y) ^ 4 / y ^ 3) z = (z - 3) * (1 + z) ^ 3 / z ^ 4 := by
  rw [deriv_fun_div (c := fun y : ℝ => (1 + y) ^ 4) (d := fun y : ℝ => y ^ 3)
        (by fun_prop) (by fun_prop) (pow_ne_zero 3 hz),
      deriv_fun_pow (f := fun y : ℝ => 1 + y) (by fun_prop) 4,
      deriv_fun_pow (f := fun y : ℝ => y) (by fun_prop) 3,
      deriv_const_add (f := fun y : ℝ => y) (1 : ℝ), congr_fun deriv_id'' z]
  field_simp
  ring

/-- The derivative of the rational function `2*(y-1)*(1+y)^3/y^3`. -/
private lemma deriv_rational_second (z : ℝ) (hz : z ≠ 0) :
    deriv (fun y : ℝ => 2 * (y - 1) * (1 + y) ^ 3 / y ^ 3) z
      = (1 + z) ^ 2 * (2 * z ^ 2 - 4 * z + 6) / z ^ 4 := by
  rw [deriv_fun_div (c := fun y : ℝ => 2 * (y - 1) * (1 + y) ^ 3) (d := fun y : ℝ => y ^ 3)
        (by fun_prop) (by fun_prop) (pow_ne_zero 3 hz)]
  rw [deriv_fun_mul (c := fun y : ℝ => 2 * (y - 1)) (d := fun y : ℝ => (1 + y) ^ 3)
        (by fun_prop) (by fun_prop)]
  rw [deriv_const_mul (c := (2 : ℝ)) (d := fun y : ℝ => y - 1) (by fun_prop)]
  rw [deriv_sub_const (f := fun y : ℝ => y) (1 : ℝ)]
  rw [deriv_fun_pow (f := fun y : ℝ => 1 + y) (by fun_prop) 3,
      deriv_fun_pow (f := fun y : ℝ => y) (by fun_prop) 3,
      deriv_const_add (f := fun y : ℝ => y) (1 : ℝ), congr_fun deriv_id'' z]
  field_simp
  ring

/-- `F = fun z => z ^ 2 * w z ^ 2` agrees with `(1+y)^4/y^2` near every `z ≠ 0`. -/
private lemma eventuallyEq_F (z : ℝ) (hz : z ≠ 0) :
    (fun y : ℝ => y ^ 2 * (Work.Spaces.w y) ^ 2) =ᶠ[nhds z] (fun y : ℝ => (1 + y) ^ 4 / y ^ 2) := by
  filter_upwards [isOpen_ne.mem_nhds hz] with y hy
  exact sq_mul_w_sq y hy

/-- `G = fun z => z * w z ^ 2` agrees with `(1+y)^4/y^3` near every `z ≠ 0`. -/
private lemma eventuallyEq_G (z : ℝ) (hz : z ≠ 0) :
    (fun y : ℝ => y * (Work.Spaces.w y) ^ 2) =ᶠ[nhds z] (fun y : ℝ => (1 + y) ^ 4 / y ^ 3) := by
  filter_upwards [isOpen_ne.mem_nhds hz] with y hy
  exact mul_w_sq y hy

/-- The first derivative of the derived weight `F`. -/
private lemma deriv_F (z : ℝ) (hz : z ≠ 0) :
    deriv (fun y : ℝ => y ^ 2 * (Work.Spaces.w y) ^ 2) z
      = 2 * (z - 1) * (1 + z) ^ 3 / z ^ 3 := by
  rw [(eventuallyEq_F z hz).deriv_eq]
  exact deriv_rational_4_2 z hz

/-- The first derivative of the derived weight `G`. -/
private lemma deriv_G (z : ℝ) (hz : z ≠ 0) :
    deriv (fun y : ℝ => y * (Work.Spaces.w y) ^ 2) z = (z - 3) * (1 + z) ^ 3 / z ^ 4 := by
  rw [(eventuallyEq_G z hz).deriv_eq]
  exact deriv_rational_4_3 z hz

/-- The second derivative of the derived weight `F`. -/
private lemma deriv2_F (z : ℝ) (hz : z ≠ 0) :
    deriv (deriv (fun y : ℝ => y ^ 2 * (Work.Spaces.w y) ^ 2)) z
      = (1 + z) ^ 2 * (2 * z ^ 2 - 4 * z + 6) / z ^ 4 := by
  have h2 : deriv (fun y : ℝ => (1 + y) ^ 4 / y ^ 2)
      =ᶠ[nhds z] (fun y : ℝ => 2 * (y - 1) * (1 + y) ^ 3 / y ^ 3) := by
    filter_upwards [isOpen_ne.mem_nhds hz] with y hy
    exact deriv_rational_4_2 y hy
  rw [((eventuallyEq_F z hz).deriv.trans h2).deriv_eq]
  exact deriv_rational_second z hz

/-- **The algebra of the radial weight `w z = (1+z)²/z²` and its two derived weights** `z²w²` (the coefficient of `-α²∂_zzΦ·Φ` after one integration by parts) and `z w²` (the coefficient of `-α(5+α)∂_zΦ·Φ`).  All identities hold for `z ≠ 0`; the two-sided bounds hold for `z > 0`, and the cruder bounds on the half-line `z ≥ 1` are the ones used to control the truncation error terms.

`z²w² = (1+z)^4/z^2 =: F`, `z w² = (1+z)^4/z^3 =: G`, `F' = 2(z-1)(1+z)^3/z^3`, `F'' = (1+z)^2(2z²-4z+6)/z^4`, `G' = (z-3)(1+z)^3/z^4`; `F'' ≤ 6w²`, `G' ≥ -3w²`, `F'' ≥ 0`; and for `z ≥ 1`: `|F'| ≤ 12z`, `F ≤ 16z²`, `G ≤ 16z`. -/
theorem weight_algebra_fts :
    (∀ z : ℝ, z ≠ 0 → z ^ 2 * (Work.Spaces.w z) ^ 2 = (1 + z) ^ 4 / z ^ 2) ∧
    (∀ z : ℝ, z ≠ 0 → z * (Work.Spaces.w z) ^ 2 = (1 + z) ^ 4 / z ^ 3) ∧
    (∀ z : ℝ, z ≠ 0 →
      deriv (fun z => z ^ 2 * (Work.Spaces.w z) ^ 2) z = 2 * (z - 1) * (1 + z) ^ 3 / z ^ 3) ∧
    (∀ z : ℝ, z ≠ 0 →
      deriv (fun z => z * (Work.Spaces.w z) ^ 2) z = (z - 3) * (1 + z) ^ 3 / z ^ 4) ∧
    (∀ z : ℝ, z ≠ 0 →
      deriv (deriv (fun z => z ^ 2 * (Work.Spaces.w z) ^ 2)) z
        = (1 + z) ^ 2 * (2 * z ^ 2 - 4 * z + 6) / z ^ 4) ∧
    (∀ z : ℝ, 0 < z →
      deriv (deriv (fun z => z ^ 2 * (Work.Spaces.w z) ^ 2)) z ≤ 6 * (Work.Spaces.w z) ^ 2) ∧
    (∀ z : ℝ, 0 < z →
      -3 * (Work.Spaces.w z) ^ 2 ≤ deriv (fun z => z * (Work.Spaces.w z) ^ 2) z) ∧
    (∀ z : ℝ, 0 < z → 0 ≤ deriv (deriv (fun z => z ^ 2 * (Work.Spaces.w z) ^ 2)) z) ∧
    (∀ z : ℝ, 1 ≤ z → |deriv (fun z => z ^ 2 * (Work.Spaces.w z) ^ 2) z| ≤ 12 * z) ∧
    (∀ z : ℝ, 1 ≤ z → z ^ 2 * (Work.Spaces.w z) ^ 2 ≤ 16 * z ^ 2) ∧
    (∀ z : ℝ, 1 ≤ z → z * (Work.Spaces.w z) ^ 2 ≤ 16 * z) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro z hz
    exact sq_mul_w_sq z hz
  · intro z hz
    exact mul_w_sq z hz
  · intro z hz
    exact deriv_F z hz
  · intro z hz
    exact deriv_G z hz
  · intro z hz
    exact deriv2_F z hz
  · -- `F'' ≤ 6 w²`
    intro z hz
    rw [deriv2_F z (ne_of_gt hz)]
    have hkey : 0 ≤ 6 * (Work.Spaces.w z) ^ 2
        - (1 + z) ^ 2 * (2 * z ^ 2 - 4 * z + 6) / z ^ 4 := by
      rw [Work.Spaces.w]
      rw [show 6 * ((1 + z) ^ 2 / z ^ 2) ^ 2 - (1 + z) ^ 2 * (2 * z ^ 2 - 4 * z + 6) / z ^ 4
          = (1 + z) ^ 2 * (4 * z ^ 2 + 16 * z) / z ^ 4 by
        field_simp
        ring]
      positivity
    linarith
  · -- `G' ≥ -3 w²`
    intro z hz
    rw [deriv_G z (ne_of_gt hz)]
    have hkey : 0 ≤ (z - 3) * (1 + z) ^ 3 / z ^ 4 + 3 * (Work.Spaces.w z) ^ 2 := by
      rw [Work.Spaces.w]
      rw [show (z - 3) * (1 + z) ^ 3 / z ^ 4 + 3 * ((1 + z) ^ 2 / z ^ 2) ^ 2
          = 4 * z * (1 + z) ^ 3 / z ^ 4 by
        field_simp
        ring]
      positivity
    linarith
  · -- `F'' ≥ 0`
    intro z hz
    rw [deriv2_F z (ne_of_gt hz)]
    have h1 : 0 < 2 * z ^ 2 - 4 * z + 6 := by nlinarith [sq_nonneg (z - 1)]
    positivity
  · -- `|F'| ≤ 12 z` for `z ≥ 1`
    intro z hz
    have hz0 : 0 < z := by linarith
    rw [deriv_F z (ne_of_gt hz0), abs_of_nonneg (by positivity)]
    rw [div_le_iff₀ (by positivity : (0 : ℝ) < z ^ 3)]
    nlinarith [sq_nonneg (z - 1), hz, sq_nonneg z, pow_pos hz0 3]
  · -- `F ≤ 16 z²` for `z ≥ 1`
    intro z hz
    have hz0 : 0 < z := by linarith
    rw [sq_mul_w_sq z (ne_of_gt hz0)]
    rw [div_le_iff₀ (by positivity : (0 : ℝ) < z ^ 2)]
    have h : (1 + z) ^ 4 ≤ (2 * z) ^ 4 :=
      pow_le_pow_left₀ (by positivity) (by linarith : 1 + z ≤ 2 * z) 4
    nlinarith [h]
  · -- `G ≤ 16 z` for `z ≥ 1`
    intro z hz
    have hz0 : 0 < z := by linarith
    rw [mul_w_sq z (ne_of_gt hz0)]
    rw [div_le_iff₀ (by positivity : (0 : ℝ) < z ^ 3)]
    have h : (1 + z) ^ 4 ≤ (2 * z) ^ 4 :=
      pow_le_pow_left₀ (by positivity) (by linarith : 1 + z ≤ 2 * z) 4
    nlinarith [h]

end Work.FTS.EllipticEst
end
-- ===== merged: Submission.Work.FTS.H2.T2Easy.QuadrantCS =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.H2.T2Easy


end Work.FTS.H2.T2Easy
end
-- ===== merged: Submission.Work.FTS.StrongEps.E5Aux.C1LocUnifAux =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.E5Aux

set_option autoImplicit false

/-- Precomposition with the second projection, as a continuous linear map in the first
argument: `L ↦ L.comp (Prod.snd)`. -/
noncomputable def clmPre (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] :
    (E →L[ℝ] ℝ) →L[ℝ] ((ℝ × E) →L[ℝ] ℝ) :=
  (ContinuousLinearMap.compL ℝ (ℝ × E) E ℝ).flip (ContinuousLinearMap.snd ℝ ℝ E)


/-- The continuous linear map `(a, L) ↦ ((x,y) ↦ a * x + L y)`. -/
noncomputable def clmHeadL (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] :
    (ℝ × (E →L[ℝ] ℝ)) →L[ℝ] ((ℝ × E) →L[ℝ] ℝ) :=
  ((ContinuousLinearMap.smulRightL ℝ (ℝ × E) ℝ (ContinuousLinearMap.fst ℝ ℝ E)).comp
      (ContinuousLinearMap.fst ℝ ℝ (E →L[ℝ] ℝ)))
    + ((clmPre E).comp (ContinuousLinearMap.snd ℝ ℝ (E →L[ℝ] ℝ)))

/-- The continuous linear map `(x, y) ↦ a * x + L y`. -/
noncomputable def clmHead (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]
    (a : ℝ) (L : E →L[ℝ] ℝ) : (ℝ × E) →L[ℝ] ℝ := clmHeadL E (a, L)

theorem clmHead_apply (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]
    (a x : ℝ) (L : E →L[ℝ] ℝ) (y : E) :
    clmHead E a L (x, y) = a * x + L y := by
  simp only [clmHead, clmHeadL, ContinuousLinearMap.add_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.smulRightL_apply_apply, ContinuousLinearMap.smulRight_apply, smul_eq_mul,
    clmPre]
  show x * a + L y = a * x + L y
  ring


/-- In the one-dimensional case `clmHead` is the pair-API `clmPair`. -/
theorem clmHead_eq_clmPair (a b : ℝ) :
    clmHead ℝ a (b • (1 : ℝ →L[ℝ] ℝ)) = clmPair (a, b) := by
  refine clm_eq_of_fst_snd ?_ ?_
  · rw [clmHead_apply, clmPair_fst]
    simp
  · rw [clmHead_apply, clmPair_snd]
    simp

end Work.FTS.StrongEps.E5Aux
end
end
-- ===== merged: Submission.Work.Spaces.SmoothCompact_Aux =====
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

/-! ## Smoothness of the iterated operators on the neighbourhood `U` -/

theorem SmoothNbhd.pz {f : ℝ → ℝ → ℝ} (h : SmoothNbhd f) : SmoothNbhd (pz f) :=
  contDiffOn_uncurry_pz isOpen_U h

theorem SmoothNbhd.pth {f : ℝ → ℝ → ℝ} (h : SmoothNbhd f) : SmoothNbhd (pth f) :=
  contDiffOn_uncurry_pth isOpen_U h

theorem smoothNbhd_pzIter {f : ℝ → ℝ → ℝ} (h : SmoothNbhd f) :
    ∀ k : ℕ, SmoothNbhd (pzIter k f)
  | 0 => h
  | k + 1 => (smoothNbhd_pzIter h k).pz

theorem smoothNbhd_DthIter {f : ℝ → ℝ → ℝ} (h : SmoothNbhd f) :
    ∀ k : ℕ, SmoothNbhd (DthIter k f)
  | 0 => h
  | k + 1 => SmoothNbhd.Dth (smoothNbhd_DthIter h k)

theorem smoothNbhd_DzIter {f : ℝ → ℝ → ℝ} (h : SmoothNbhd f) :
    ∀ k : ℕ, SmoothNbhd (DzIter k f)
  | 0 => h
  | k + 1 => SmoothNbhd.Dz (smoothNbhd_DzIter h k)

theorem smoothNbhd_mixed {f : ℝ → ℝ → ℝ} (h : SmoothNbhd f) (j i : ℕ) :
    SmoothNbhd (mixed j i f) :=
  smoothNbhd_DzIter (smoothNbhd_DthIter h i) j


/-! ## Vanishing at `z = 0` -/



/-- The derivative in `z` of `D_z G` at the origin equals `∂_z G` evaluated there. -/
theorem pz_Dz_eq (G : ℝ → ℝ → ℝ) {z θ : ℝ}
    (h : DifferentiableAt ℝ (fun t => pz G t θ) z) :
    pz (Dz G) z θ = pz G z θ + z * pz (pz G) z θ := by
  have h1 : HasDerivAt (fun t : ℝ => t * pz G t θ)
      (1 * pz G z θ + z * pz (pz G) z θ) z :=
    (hasDerivAt_id z).mul h.hasDerivAt
  rw [show pz (Dz G) z θ = deriv (fun t : ℝ => t * pz G t θ) z from rfl, h1.deriv]
  ring


/-! ## Vanishing on the angular boundary -/











/-! ## Absorbing the radial weight `w` into a `z²` bound -/



/-! ## Vanishing above `R` for the iterated operators -/


/-- A function vanishing above `R` has all its `D_θ`-iterates vanishing above `R`. -/
theorem DthIter_eq_zero_of_gt (f : ℝ → ℝ → ℝ) (R : ℝ)
    (h : ∀ z θ : ℝ, R < z → f z θ = 0) :
    ∀ k : ℕ, ∀ z θ : ℝ, R < z → DthIter k f z θ = 0 := by
  intro k
  induction k with
  | zero => exact h
  | succ k ih =>
    intro z θ hz
    rw [DthIter_succ, Dth]
    have hp : pth (DthIter k f) z θ = 0 := by
      rw [pth]
      have hev : (fun θ' => DthIter k f z θ') =ᶠ[𝓝 θ] (fun _ => (0 : ℝ)) := by
        filter_upwards with θ'
        exact ih z θ' hz
      rw [hev.deriv_eq, deriv_const]
    rw [hp, mul_zero]

/-- A function vanishing above `R` has all its `D_z`-iterates vanishing above `R`. -/
theorem DzIter_eq_zero_of_gt (f : ℝ → ℝ → ℝ) (R : ℝ)
    (h : ∀ z θ : ℝ, R < z → f z θ = 0) :
    ∀ k : ℕ, ∀ z θ : ℝ, R < z → DzIter k f z θ = 0 := by
  intro k
  induction k with
  | zero => exact h
  | succ k ih =>
    intro z θ hz
    rw [DzIter_succ, Dz]
    have hp : pz (DzIter k f) z θ = 0 := by
      rw [pz]
      have hev : (fun z' => DzIter k f z' θ) =ᶠ[𝓝 z] (fun _ => (0 : ℝ)) := by
        filter_upwards [isOpen_Ioi.mem_nhds hz] with z' hz'
        exact ih z' θ hz'
      rw [hev.deriv_eq, deriv_const]
    rw [hp, mul_zero]

/-- A function vanishing above `R` has all its mixed derivatives vanishing above `R`. -/
theorem mixed_eq_zero_of_gt (f : ℝ → ℝ → ℝ) (R : ℝ)
    (h : ∀ z θ : ℝ, R < z → f z θ = 0) :
    ∀ j i : ℕ, ∀ z θ : ℝ, R < z → mixed j i f z θ = 0 :=
  fun j i => DzIter_eq_zero_of_gt (DthIter i f) R (DthIter_eq_zero_of_gt f R h i) j


/-! ## The weighted pointwise bounds -/

theorem sin_two_nonneg_of_Iθ {θ : ℝ} (hθ : θ ∈ Iθ) : 0 ≤ Real.sin (2 * θ) := by
  apply Real.sin_nonneg_of_nonneg_of_le_pi <;> linarith [hθ.1, hθ.2]



/-! ## The pointwise bound for `HkIntegrand` -/



/-! ## Membership in `𝒲^{l,∞}` -/




/-! ## Measurability and integrability of the `ℋ^k`-integrand -/

theorem volume_Iθ_lt_top : (volume : Measure ℝ) Iθ < ⊤ := by
  rw [Iθ, Real.volume_Icc]
  exact ENNReal.ofReal_lt_top

theorem volume_real_Iθ : (volume : Measure ℝ).real Iθ = π / 2 := by
  rw [MeasureTheory.measureReal_def, Iθ, Real.volume_Icc,
    ENNReal.toReal_ofReal (by linarith [Real.pi_pos])]
  ring

/-- The integrand vanishes identically at `z = 0`. -/
theorem HkIntegrand_apply_zero (α : ℝ) (k : ℕ) (f : ℝ → ℝ → ℝ) (θ : ℝ) :
    HkIntegrand α k f 0 θ = 0 := by
  have hw0 : w 0 = 0 := by norm_num [w]
  have hWt0 : Wt α 0 θ = 0 := by simp [Wt, w]
  rw [HkIntegrand]
  have h1 : (∑ i ∈ Finset.range (k + 1),
      (DzIter i f 0 θ * (w 0 / (Real.sin (2 * θ)) ^ (eta / 2))) ^ 2) = 0 :=
    Finset.sum_eq_zero fun i _ => by rw [hw0]; ring
  have h2 : (∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1),
      if 1 ≤ i ∧ i + j ≤ k then (mixed j i f 0 θ * Wt α 0 θ) ^ 2 else 0) = 0 :=
    Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun j _ => by
      by_cases h : 1 ≤ i ∧ i + j ≤ k
      · rw [if_pos h, hWt0]; ring
      · rw [if_neg h]
  rw [h1, h2, add_zero]

/-- The integrand vanishes above `R`. -/
theorem HkIntegrand_eq_zero_of_gt (α : ℝ) (k : ℕ) (f : ℝ → ℝ → ℝ) (R z θ : ℝ)
    (h : ∀ z θ : ℝ, R < z → f z θ = 0) (hz : R < z) : HkIntegrand α k f z θ = 0 := by
  have hDz := DzIter_eq_zero_of_gt f R h
  have hmix := mixed_eq_zero_of_gt f R h
  rw [HkIntegrand]
  have h1 : (∑ i ∈ Finset.range (k + 1),
      (DzIter i f z θ * (w z / (Real.sin (2 * θ)) ^ (eta / 2))) ^ 2) = 0 :=
    Finset.sum_eq_zero fun i _ => by rw [hDz i z θ hz]; ring
  have h2 : (∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1),
      if 1 ≤ i ∧ i + j ≤ k then (mixed j i f z θ * Wt α z θ) ^ 2 else 0) = 0 :=
    Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun j _ => by
      by_cases hc : 1 ≤ i ∧ i + j ≤ k
      · rw [if_pos hc, hmix j i z θ hz]; ring
      · rw [if_neg hc]
  rw [h1, h2, add_zero]

end Work.Spaces
end
end
-- ===== merged: Submission.Work.Spaces.mixed_mul_le =====
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

/-! ## The operators acting on functions of the pair `(z, θ)` -/



/-- The one-variable operator `φ ↦ (x ↦ x φ'(x))`: the `z`-operator on a `θ`-slice. -/
def OpZ (φ : ℝ → ℝ) : ℝ → ℝ := fun x => x * deriv φ x

/-- The one-variable operator `φ ↦ (θ ↦ sin(2θ) φ'(θ))`: the `θ`-operator on a `z`-slice. -/
def OpT (φ : ℝ → ℝ) : ℝ → ℝ := fun θ => Real.sin (2 * θ) * deriv φ θ

/-! ## Compatibility with the curried definitions of `Defs.lean` -/







/-! ## Slices of the operators -/

theorem sliceZ_DzIter (b : ℕ) (H : ℝ → ℝ → ℝ) (θ : ℝ) :
    (fun z => DzIter b H z θ) = (OpZ^[b]) (fun z => H z θ) := by
  induction b with
  | zero => rfl
  | succ n ih =>
      rw [Function.iterate_succ_apply']
      show (fun z => z * deriv (fun z' => DzIter n H z' θ) z) = OpZ ((OpZ^[n]) fun z => H z θ)
      rw [ih]
      rfl

theorem sliceTh_DthIter (i : ℕ) (H : ℝ → ℝ → ℝ) (z : ℝ) :
    (fun θ => DthIter i H z θ) = (OpT^[i]) (fun θ => H z θ) := by
  induction i with
  | zero => rfl
  | succ n ih =>
      rw [Function.iterate_succ_apply']
      show (fun θ => Real.sin (2 * θ) * deriv (fun θ' => DthIter n H z θ') θ) =
        OpT ((OpT^[n]) fun θ => H z θ)
      rw [ih]
      rfl

/-! ## Slices of functions: `HasFDerivAt` gives the one-variable derivatives -/

theorem hasDerivAt_slice_fst {F : ℝ × ℝ → ℝ} {F' : ℝ × ℝ →L[ℝ] ℝ} {p : ℝ × ℝ}
    (h : HasFDerivAt F F' p) : HasDerivAt (fun z => F (z, p.2)) (F' (1, 0)) p.1 := by
  have hc : HasDerivAt (fun t : ℝ => (t, p.2)) (1, 0) p.1 :=
    HasDerivAt.prodMk (hasDerivAt_id p.1) (hasDerivAt_const p.1 p.2)
  exact h.comp_hasDerivAt _ hc

theorem hasDerivAt_slice_snd {F : ℝ × ℝ → ℝ} {F' : ℝ × ℝ →L[ℝ] ℝ} {p : ℝ × ℝ}
    (h : HasFDerivAt F F' p) : HasDerivAt (fun θ => F (p.1, θ)) (F' (0, 1)) p.2 := by
  have hc : HasDerivAt (fun t : ℝ => (p.1, t)) (0, 1) p.2 :=
    HasDerivAt.prodMk (hasDerivAt_const p.2 p.1) (hasDerivAt_id p.2)
  exact h.comp_hasDerivAt _ hc

/-! ## Smoothness of the partial derivative maps (via `fderiv`) -/






/-! ## The operator identities on an open set -/













/-! ## Iterated Leibniz rules, deduced from the abstract two-operator rule -/



/-! ## Vanishing of the `θ`-derivatives at the angular boundary -/

theorem OpZ_apply_zero (x : ℝ) : OpZ (fun _ : ℝ => (0 : ℝ)) x = 0 := by simp [OpZ]

theorem OpZ_iterate_zero (j : ℕ) :
    (OpZ^[j]) (fun _ : ℝ => (0 : ℝ)) = fun _ => 0 := by
  induction j with
  | zero => rfl
  | succ n ih => rw [Function.iterate_succ_apply', ih]; funext x; exact OpZ_apply_zero x

theorem OpT_apply_eq_zero {φ : ℝ → ℝ} {θ : ℝ} (hθ : Real.sin (2 * θ) = 0) :
    OpT φ θ = 0 := by
  simp only [OpT, hθ, zero_mul]

theorem OpT_iterate_apply_eq_zero {φ : ℝ → ℝ} {θ : ℝ} (hθ : Real.sin (2 * θ) = 0) :
    ∀ i : ℕ, 1 ≤ i → (OpT^[i] φ) θ = 0 := by
  intro i hi
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : i ≠ 0)
  rw [Function.iterate_succ_apply']
  exact OpT_apply_eq_zero hθ

/-- At an angle `θ` with `sin(2θ) = 0`, all mixed derivatives of `θ`-order `≥ 1` vanish. -/
theorem mixed_eq_zero_of_sin_eq_zero {H : ℝ → ℝ → ℝ} {z θ : ℝ}
    (hθ : Real.sin (2 * θ) = 0) {j i : ℕ} (hi : 1 ≤ i) : mixed j i H z θ = 0 := by
  have h1 : (fun z' => DthIter i H z' θ) = fun _ => (0 : ℝ) := by
    funext z'
    rw [show DthIter i H z' θ = (OpT^[i]) (fun θ' => H z' θ') θ
      from congrFun (sliceTh_DthIter i H z') θ]
    exact OpT_iterate_apply_eq_zero hθ i hi
  have h2 : mixed j i H z θ = (OpZ^[j]) (fun z' => DthIter i H z' θ) z :=
    congrFun (sliceZ_DzIter j (DthIter i H) θ) z
  rw [h2, h1, OpZ_iterate_zero j]

/-! ## A summation bound -/


/-! ## The main estimate -/


end Work.Spaces
end
end
