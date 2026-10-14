import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Submission.Work.FTS.EllipticEst.HkMem_FstarSin_open
import Submission.Work.FTS.EllipticEst.UopHk.GsingFactsInterior
import Submission.Work.FTS.H2.HQ.Glue
import Submission.Work.FTS.H2.Transport1Aux
import Submission.Work.FTS.H2.hard_sq_prod_z
import Submission.Work.FTS.PhiStar.RadGreenSupport.ibp_upper
import Submission.Work.FTS.TransportS.Defs
import Submission.Work.FTS.TransportS.SupDzAux.sup_dz_ang_le
import Submission.Work.FTS.Vocab
import Submission.Work.FTS_EllLimOK.Decay.DecayTools
import Submission.Work.FTS_RegExport.RXT.Sys.continuousAt_Qang_of_bounds
import Submission.Work.GalerkinFix.RegQ.HkMem_mono_Q
import Submission.Work.H2.T1Q.IbpCutoff
import Submission.Work.H2.T1Q.PwBdQ
import Submission.Work.SolutionDelivery.Scaling.Main
import Submission.Work.SolutionDelivery.Scaling.vorticityDecay_rescaleDatum
import Submission.Work.Spaces.bt_f_bound
import Submission.Work.Spaces.pz_DthIter_mul_eq
import Submission.Work.Spaces.sin_two_rpow
import Submission.Work.Spaces.uncurry_partial_c1
import Submission.Work.StabilityFar.Decay.timeDeriv_eq_zero_of_notMem_closedBall
-- ===== merged: Submission.Work.FTS.EllipticEst.UopHk.L12_w_sq_integrable =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.UopHk

open scoped Real Topology
open MeasureTheory Set Filter

set_option maxHeartbeats 1000000

/-!
# Integrability of `w²·L₁₂(F)²` for a source of the interior class

For `0 < α ≤ 1`, a source `F` which is `C^∞` on the open quadrant
(`Work.FTS.EllipticEst.SmoothOpen F`) and lies in the weighted space `ℋ^k`
(`Work.Spaces.HkMem α k F`, `k ≥ 2`), whose associated singular term vanishes at the origin
(`Work.Elliptic.L12 F 0 = 0`), the function `z ↦ w(z)²·L₁₂(F)(z)²` is integrable on
`Iz = [0,∞)`.

## The route

Write `U := L₁₂(F)` and `f := 3 F_*(F)` (the angular moment, so that
`L₁₂dens F z = f z / z`, `Work.Elliptic.L12dens_eq_three_Fstar_div`).

* `Work.FTS.EllipticEst.integrableOn_Fstar_div_of_smoothOpen_Hk` makes the density
  `L₁₂dens F` integrable on `(0,∞)`; hence `Work.Elliptic.L12_values` gives the decay
  `U → 0` at `+∞` and the continuity of `U` on `[0,1]`, while
  `Work.FTS.EllipticEst.contDiffOn_L12_of_smoothOpen_Hk` gives
  `U' = -f z/z` at every `z > 0`.
* The numerator is controlled by `ℋ^k`-membership: `(f z)² w(z)² ≤ 9·(π/2)·A_0(z)`, where
  `A_0 = AjF F 0` is the `θ = 0` weighted slice of the `ℋ^k`-integrand of `F`
  (`Work.FTS.EllipticEst.FstarDzIter_sq_mul_w_le_open`), and `A_0` is integrable
  (`Work.FTS.EllipticEst.AjF_integrableOn`).
* The two weighted Hardy inequalities `Work.Elliptic.HardyLeftW` (on `(0,1)`, using `U 0 = 0`)
  and `Work.Elliptic.HardyRightW` (on `(1,∞)`, using the decay) then bound `∫ U² w²` on each
  half by the integrable `∫ f² w²`, and the two halves reassemble to `Iz`.
-/


end Work.FTS.EllipticEst.UopHk
end
-- ===== merged: Submission.Work.FTS.H2.T2Qaux.SupQ =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.H2.T2Qaux

set_option autoImplicit false

open Work.Spaces


end Work.FTS.H2.T2Qaux
end
end
-- ===== merged: Submission.Work.FTS.TransportS.flat_mixed_le =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.TransportS

set_option autoImplicit false
set_option maxHeartbeats 2000000

/-! ## The multiplier `sin(2·)` and the shift identity for the `D_θ`-iterates -/

/-- The angular multiplier `θ ↦ sin(2θ)`, viewed as a function on `(z,θ)`. -/
def Sfun : ℝ → ℝ → ℝ := fun _ θ => Real.sin (2 * θ)

/-- `sin(2θ) ≥ 0` on the open angular interval. -/
theorem sin_two_nonneg_of_Ioo {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (π / 2)) :
    0 ≤ Real.sin (2 * θ) :=
  Real.sin_nonneg_of_mem_Icc ⟨by linarith [hθ.1], by linarith [hθ.2, Real.pi_pos]⟩

/-- The multiplier is smooth on the open quadrant. -/
theorem Sfun_smoothOpen : Work.FTS.EllipticEst.SmoothOpen Sfun := by
  show ContDiffOn ℝ Work.Stability.smoothOrder
    (Function.uncurry (fun _ (θ : ℝ) => Real.sin (2 * θ))) Work.FTS.EllipticEst.Q0
  fun_prop

/-- Shifting the iteration of `D_θ`: `D_θ^{n+1} g = D_θ^{n}(D_θ g)`. -/
theorem DthIter_shift (n : ℕ) (g : ℝ → ℝ → ℝ) :
    Work.Spaces.DthIter (n + 1) g = Work.Spaces.DthIter n (Work.Spaces.Dth g) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [Work.Spaces.DthIter_succ, ih, ← Work.Spaces.DthIter_succ]

/-- `D_θ = sin(2θ) · ∂_θ`, in the shape used below. -/
theorem Dth_eq_Sfun_mul_pth (f : ℝ → ℝ → ℝ) :
    Work.Spaces.Dth f = fun z θ => Sfun z θ * Work.Spaces.pth f z θ := rfl

/-- `D_θ^r` of the multiplier `sin(2·)` is the corresponding iterate of `Lop` applied to the
one-variable function `sin(2·)` (it is independent of `z`). -/
theorem DthIter_Sfun_eq_LopIter (r : ℕ) (z θ : ℝ) :
    Work.Spaces.DthIter r Sfun z θ
      = Work.FTS.EllipticEst.LopIter r (fun t : ℝ => Real.sin (2 * t)) θ := by
  rw [congrFun (Work.Spaces.DthIter_eq_iterate_Lop r Sfun z) θ]
  rfl

/-! ## Leibniz for `D_θ^i` with differentiability hypotheses on the slices -/

/-- **The iterated Leibniz rule for `D_θ`** with only *differentiability* of the `θ`-slices of
the iterates of the two factors.  This is the form that applies to `SmoothOpen` data, for
which no analyticity (or finite-order `C^n`-arithmetic) is available. -/
theorem DthIter_mul_eq_of_diffOn (i : ℕ) (f g : ℝ → ℝ → ℝ) {z θ : ℝ}
    (hθ : θ ∈ Set.Ioo 0 (π / 2))
    (hf : ∀ a ≤ i, DifferentiableOn ℝ (fun θ' => Work.Spaces.DthIter a f z θ')
      (Set.Ioo 0 (π / 2)))
    (hg : ∀ a ≤ i, DifferentiableOn ℝ (fun θ' => Work.Spaces.DthIter a g z θ')
      (Set.Ioo 0 (π / 2))) :
    Work.Spaces.DthIter i (fun a b => f a b * g a b) z θ
      = ∑ a ∈ Finset.range (i + 1), (i.choose a : ℝ)
          * (Work.Spaces.DthIter a f z θ * Work.Spaces.DthIter (i - a) g z θ) := by
  induction i generalizing θ with
  | zero =>
      simp
  | succ i ih =>
      -- the two `θ`-slices of the iterate `D_θ^i (f·g)` agree with the binomial sum near `θ`
      have hev : (fun θ' => Work.Spaces.DthIter i (fun a b : ℝ => f a b * g a b) z θ')
          =ᶠ[𝓝 θ] (fun θ' => ∑ a ∈ Finset.range (i + 1), (i.choose a : ℝ)
              * (Work.Spaces.DthIter a f z θ' * Work.Spaces.DthIter (i - a) g z θ')) := by
        filter_upwards [isOpen_Ioo.mem_nhds hθ] with θ' hθ'
        exact ih hθ' (fun a ha => hf a (by omega)) (fun a ha => hg a (by omega))
      have hderiv : deriv (fun θ' => Work.Spaces.DthIter i
            (fun a b : ℝ => f a b * g a b) z θ') θ
          = deriv (fun θ' => ∑ a ∈ Finset.range (i + 1), (i.choose a : ℝ)
              * (Work.Spaces.DthIter a f z θ' * Work.Spaces.DthIter (i - a) g z θ')) θ :=
        hev.deriv_eq
      have hsummand : ∀ a ∈ Finset.range (i + 1), DifferentiableAt ℝ
          (fun θ' => (i.choose a : ℝ)
            * (Work.Spaces.DthIter a f z θ' * Work.Spaces.DthIter (i - a) g z θ')) θ := by
        intro a ha
        exact (((hf a (by have := Finset.mem_range.mp ha; omega)).differentiableAt
            (isOpen_Ioo.mem_nhds hθ)).mul
          ((hg (i - a) (by omega)).differentiableAt (isOpen_Ioo.mem_nhds hθ))).const_mul _
      have hfunsum : (fun θ' => ∑ a ∈ Finset.range (i + 1), (i.choose a : ℝ)
              * (Work.Spaces.DthIter a f z θ' * Work.Spaces.DthIter (i - a) g z θ'))
          = ∑ a ∈ Finset.range (i + 1), (fun θ' => (i.choose a : ℝ)
              * (Work.Spaces.DthIter a f z θ' * Work.Spaces.DthIter (i - a) g z θ')) := by
        funext θ'
        rw [Finset.sum_apply]
      have hkey : Work.Spaces.DthIter (i + 1) (fun a b : ℝ => f a b * g a b) z θ
          = ∑ a ∈ Finset.range (i + 1), Real.sin (2 * θ)
              * deriv (fun θ' => (i.choose a : ℝ)
                  * (Work.Spaces.DthIter a f z θ' * Work.Spaces.DthIter (i - a) g z θ')) θ := by
        show Real.sin (2 * θ) * deriv (fun θ' => Work.Spaces.DthIter i
              (fun a b : ℝ => f a b * g a b) z θ') θ = _
        rw [hderiv, hfunsum, deriv_sum hsummand, Finset.mul_sum]
      rw [hkey]
      have hterm : ∀ a ∈ Finset.range (i + 1),
          Real.sin (2 * θ) * deriv (fun θ' => (i.choose a : ℝ)
              * (Work.Spaces.DthIter a f z θ' * Work.Spaces.DthIter (i - a) g z θ')) θ
          = (i.choose a : ℝ)
              * (Work.Spaces.DthIter (a + 1) f z θ * Work.Spaces.DthIter (i - a) g z θ
                + Work.Spaces.DthIter a f z θ * Work.Spaces.DthIter (i - a + 1) g z θ) := by
        intro a ha
        have h1 : DifferentiableAt ℝ (fun θ' => Work.Spaces.DthIter a f z θ') θ :=
          (hf a (by have := Finset.mem_range.mp ha; omega)).differentiableAt
            (isOpen_Ioo.mem_nhds hθ)
        have h2 : DifferentiableAt ℝ (fun θ' => Work.Spaces.DthIter (i - a) g z θ') θ :=
          (hg (i - a) (by omega)).differentiableAt (isOpen_Ioo.mem_nhds hθ)
        have hder : deriv (fun θ' => (i.choose a : ℝ)
              * (Work.Spaces.DthIter a f z θ' * Work.Spaces.DthIter (i - a) g z θ')) θ
            = (i.choose a : ℝ)
                * (deriv (fun θ' => Work.Spaces.DthIter a f z θ') θ
                    * Work.Spaces.DthIter (i - a) g z θ
                  + Work.Spaces.DthIter a f z θ
                    * deriv (fun θ' => Work.Spaces.DthIter (i - a) g z θ') θ) :=
          ((h1.hasDerivAt.mul h2.hasDerivAt).const_mul ((i.choose a : ℝ))).deriv
        rw [hder,
          show Work.Spaces.DthIter (a + 1) f z θ
              = Real.sin (2 * θ) * deriv (fun θ' => Work.Spaces.DthIter a f z θ') θ from rfl,
          show Work.Spaces.DthIter (i - a + 1) g z θ
              = Real.sin (2 * θ) * deriv (fun θ' => Work.Spaces.DthIter (i - a) g z θ') θ
            from rfl]
        ring
      rw [Finset.sum_congr rfl hterm]
      exact Work.Spaces.leibniz_step i (fun a => Work.Spaces.DthIter a f z θ)
        (fun b => Work.Spaces.DthIter b g z θ)

/-! ## `D_z^j` acts termwise on sums with `θ`-only coefficients -/

/-- `D_z^j` of a finite sum of products `cᵢ(θ) · Hᵢ(z,θ)`, with `θ`-only coefficients and
`SmoothOpen` summands, is the sum of `cᵢ(θ) · D_z^j Hᵢ`. -/
theorem DzIter_sum_const_mul {ι : Type*} (s : Finset ι) (c : ι → ℝ → ℝ) (H : ι → ℝ → ℝ → ℝ)
    (hH : ∀ i ∈ s, Work.FTS.EllipticEst.SmoothOpen (H i)) (j : ℕ) {z θ : ℝ}
    (hz : 0 < z) (hθ : 0 < θ) (hθ1 : θ < π / 2) :
    Work.Spaces.DzIter j (fun z θ => ∑ i ∈ s, c i θ * H i z θ) z θ
      = ∑ i ∈ s, c i θ * Work.Spaces.DzIter j (H i) z θ := by
  induction j generalizing z θ with
  | zero => rfl
  | succ j ih =>
      have hEq : Set.EqOn
          (Function.uncurry (Work.Spaces.DzIter j (fun z θ => ∑ i ∈ s, c i θ * H i z θ)))
          (Function.uncurry (fun z θ => ∑ i ∈ s, c i θ * Work.Spaces.DzIter j (H i) z θ))
          Work.FTS.EllipticEst.Q0 := by
        intro p hp
        obtain ⟨z', θ'⟩ := p
        obtain ⟨hz', hθ', hθ'1⟩ := Work.FTS.EllipticEst.mem_Q0.mp hp
        exact ih hz' hθ' hθ'1
      have hpz : Work.Spaces.pz
            (Work.Spaces.DzIter j (fun z θ => ∑ i ∈ s, c i θ * H i z θ)) z θ
          = Work.Spaces.pz
            (fun z θ => ∑ i ∈ s, c i θ * Work.Spaces.DzIter j (H i) z θ) z θ :=
        Work.Spaces.pz_congr_of_isOpen Work.FTS.EllipticEst.isOpen_Q0 hEq
          (Work.FTS.EllipticEst.mem_Q0.mpr ⟨hz, hθ, hθ1⟩)
      have hdiff : ∀ i ∈ s, DifferentiableAt ℝ
          (fun z' => Work.Spaces.DzIter j (H i) z' θ) z := by
        intro i hi
        have h1 : Work.FTS.EllipticEst.SmoothOpen (Work.Spaces.DzIter j (H i)) :=
          (hH i hi).DzIter j
        exact ((h1.curry_z ⟨hθ, hθ1⟩).differentiableOn (by simp)).differentiableAt
          (isOpen_Ioi.mem_nhds hz)
      have hpz2 : Work.Spaces.pz
            (fun z θ => ∑ i ∈ s, c i θ * Work.Spaces.DzIter j (H i) z θ) z θ
          = ∑ i ∈ s, c i θ * Work.Spaces.pz (Work.Spaces.DzIter j (H i)) z θ := by
        show deriv (fun z' => ∑ i ∈ s, c i θ * Work.Spaces.DzIter j (H i) z' θ) z = _
        rw [show (fun z' => ∑ i ∈ s, c i θ * Work.Spaces.DzIter j (H i) z' θ)
              = ∑ i ∈ s, (fun z' => c i θ * Work.Spaces.DzIter j (H i) z' θ) from by
            funext z'
            rw [Finset.sum_apply]]
        rw [deriv_sum (fun i hi => (hdiff i hi).const_mul (c i θ))]
        exact Finset.sum_congr rfl fun i hi => deriv_const_mul_field (c i θ)
      show z * Work.Spaces.pz
            (Work.Spaces.DzIter j (fun z θ => ∑ i ∈ s, c i θ * H i z θ)) z θ
          = ∑ i ∈ s, c i θ * Work.Spaces.DzIter (j + 1) (H i) z θ
      rw [hpz, hpz2, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i hi => ?_
      rw [show Work.Spaces.DzIter (j + 1) (H i) z θ
            = z * Work.Spaces.pz (Work.Spaces.DzIter j (H i)) z θ from rfl]
      ring

/-! ## The main estimate -/

theorem flat_mixed_le (l : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (f : ℝ → ℝ → ℝ), Work.FTS.EllipticEst.SmoothOpen f →
      ∀ (K : ℝ), 0 ≤ K →
      (∀ b i : ℕ, b + i ≤ l → ∀ z θ : ℝ, 0 < z → 0 < θ → θ < π / 2 →
        |Work.Spaces.mixed b i (Work.Spaces.pth f) z θ| ≤ K) →
      ∀ a b : ℕ, 1 ≤ a → a + b ≤ l + 1 → ∀ z θ : ℝ, 0 < z → 0 < θ → θ < π / 2 →
        |Work.Spaces.mixed b a f z θ| ≤ C * Real.sin (2 * θ) * K := by
  classical
  obtain ⟨A, hApos, hAbound⟩ := Work.FTS.EllipticEst.Lop_iter_sin_bound l
  refine ⟨(1 + (2 : ℝ) ^ l) * (A + 1) + 1, by positivity, ?_⟩
  intro f hsm K hK hHyp a b ha hab z θ hz hθ hθ1
  obtain ⟨i, hi⟩ : ∃ i : ℕ, a = i + 1 :=
    ⟨a - 1, (Nat.succ_pred_eq_of_pos (by omega)).symm⟩
  subst hi
  have hsin : 0 ≤ Real.sin (2 * θ) := sin_two_nonneg_of_Ioo ⟨hθ, hθ1⟩
  have hsK : 0 ≤ Real.sin (2 * θ) * K := mul_nonneg hsin hK
  have hil : i ≤ l := by omega
  have hbi : b + i ≤ l := by omega
  -- the angular coefficients
  have hcoef : ∀ r : ℕ, r ≤ l →
      |Work.FTS.EllipticEst.LopIter r (fun t : ℝ => Real.sin (2 * t)) θ|
      ≤ A * Real.sin (2 * θ) := fun r hr => hAbound r hr θ ⟨hθ.le, hθ1.le⟩
  -- the Leibniz expansion, as a joint statement on the open quadrant
  have hLeib : ∀ z' θ' : ℝ, 0 < z' → 0 < θ' → θ' < π / 2 →
      Work.Spaces.DthIter i (fun z θ => Sfun z θ * Work.Spaces.pth f z θ) z' θ'
        = ∑ r ∈ Finset.range (i + 1),
            ((i.choose r : ℝ)
                * Work.FTS.EllipticEst.LopIter r (fun t : ℝ => Real.sin (2 * t)) θ')
              * Work.Spaces.DthIter (i - r) (Work.Spaces.pth f) z' θ' := by
    intro z' θ' hz' hθ' hθ'1
    have hf : ∀ c ≤ i, DifferentiableOn ℝ
        (fun θ'' => Work.Spaces.DthIter c Sfun z' θ'') (Set.Ioo 0 (π / 2)) := fun c _ =>
      ((Sfun_smoothOpen.DthIter c).curry_θ hz').differentiableOn (by simp)
    have hg : ∀ c ≤ i, DifferentiableOn ℝ
        (fun θ'' => Work.Spaces.DthIter c (Work.Spaces.pth f) z' θ'')
        (Set.Ioo 0 (π / 2)) := fun c _ =>
      (((hsm.pth).DthIter c).curry_θ hz').differentiableOn (by simp)
    rw [DthIter_mul_eq_of_diffOn i Sfun (Work.Spaces.pth f) ⟨hθ', hθ'1⟩ hf hg]
    refine Finset.sum_congr rfl fun r hr => ?_
    rw [DthIter_Sfun_eq_LopIter r z' θ']
    ring
  -- the mixed derivative rewritten as `D_z^b` of that sum
  have hmixed : Work.Spaces.mixed b (i + 1) f z θ
      = Work.Spaces.DzIter b (fun z θ => ∑ r ∈ Finset.range (i + 1),
            ((i.choose r : ℝ)
                * Work.FTS.EllipticEst.LopIter r (fun t : ℝ => Real.sin (2 * t)) θ)
              * Work.Spaces.DthIter (i - r) (Work.Spaces.pth f) z θ) z θ := by
    rw [show Work.Spaces.mixed b (i + 1) f
          = Work.Spaces.DzIter b (Work.Spaces.DthIter (i + 1) f) from rfl, DthIter_shift,
      Dth_eq_Sfun_mul_pth]
    exact Work.FTS.EllipticEst.SmoothOpen.DzIter_congr
      (F := Work.Spaces.DthIter i (fun z θ => Sfun z θ * Work.Spaces.pth f z θ))
      (G := fun z θ => ∑ r ∈ Finset.range (i + 1),
          ((i.choose r : ℝ)
              * Work.FTS.EllipticEst.LopIter r (fun t : ℝ => Real.sin (2 * t)) θ)
            * Work.Spaces.DthIter (i - r) (Work.Spaces.pth f) z θ) hLeib b z θ hz hθ hθ1
  -- the termwise distribution of `D_z^b`
  have hstep3 : Work.Spaces.DzIter b (fun z θ => ∑ r ∈ Finset.range (i + 1),
        ((i.choose r : ℝ)
            * Work.FTS.EllipticEst.LopIter r (fun t : ℝ => Real.sin (2 * t)) θ)
          * Work.Spaces.DthIter (i - r) (Work.Spaces.pth f) z θ) z θ
      = ∑ r ∈ Finset.range (i + 1),
          ((i.choose r : ℝ)
              * Work.FTS.EllipticEst.LopIter r (fun t : ℝ => Real.sin (2 * t)) θ)
            * Work.Spaces.mixed b (i - r) (Work.Spaces.pth f) z θ :=
    DzIter_sum_const_mul (Finset.range (i + 1))
      (fun r θ => (i.choose r : ℝ)
        * Work.FTS.EllipticEst.LopIter r (fun t : ℝ => Real.sin (2 * t)) θ)
      (fun r => Work.Spaces.DthIter (i - r) (Work.Spaces.pth f))
      (fun r _ => (hsm.pth).DthIter (i - r)) b hz hθ hθ1
  -- the per-term bound
  have hbd : ∀ r ∈ Finset.range (i + 1),
      |((i.choose r : ℝ)
          * Work.FTS.EllipticEst.LopIter r (fun t : ℝ => Real.sin (2 * t)) θ)
        * Work.Spaces.mixed b (i - r) (Work.Spaces.pth f) z θ|
        ≤ (i.choose r : ℝ) * (A * Real.sin (2 * θ)) * K := by
    intro r hr
    have hr' : r < i + 1 := Finset.mem_range.mp hr
    have hrl : r ≤ l := le_trans (Nat.lt_succ_iff.mp hr') hil
    have h1 : |Work.FTS.EllipticEst.LopIter r (fun t : ℝ => Real.sin (2 * t)) θ|
        ≤ A * Real.sin (2 * θ) := hcoef r hrl
    have h2 : |Work.Spaces.mixed b (i - r) (Work.Spaces.pth f) z θ| ≤ K :=
      hHyp b (i - r) (by omega) z θ hz hθ hθ1
    have hC : (0 : ℝ) ≤ (i.choose r : ℝ) := Nat.cast_nonneg _
    have hAs : 0 ≤ A * Real.sin (2 * θ) := mul_nonneg hApos.le hsin
    rw [abs_mul, abs_mul, abs_of_nonneg hC]
    exact mul_le_mul (mul_le_mul_of_nonneg_left h1 hC) h2 (abs_nonneg _)
      (mul_nonneg hC hAs)
  calc |Work.Spaces.mixed b (i + 1) f z θ|
      = |∑ r ∈ Finset.range (i + 1),
          ((i.choose r : ℝ)
              * Work.FTS.EllipticEst.LopIter r (fun t : ℝ => Real.sin (2 * t)) θ)
            * Work.Spaces.mixed b (i - r) (Work.Spaces.pth f) z θ| := by
        rw [hmixed, hstep3]
    _ ≤ ∑ r ∈ Finset.range (i + 1),
          |((i.choose r : ℝ)
              * Work.FTS.EllipticEst.LopIter r (fun t : ℝ => Real.sin (2 * t)) θ)
            * Work.Spaces.mixed b (i - r) (Work.Spaces.pth f) z θ| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ r ∈ Finset.range (i + 1),
          (i.choose r : ℝ) * (A * Real.sin (2 * θ)) * K :=
        Finset.sum_le_sum hbd
    _ = ((2 : ℝ) ^ i * A) * (Real.sin (2 * θ) * K) := by
        have hchoose : (∑ r ∈ Finset.range (i + 1), (i.choose r : ℝ)) = (2 : ℝ) ^ i := by
          rw [← Nat.cast_sum, Nat.sum_range_choose, Nat.cast_pow]
          norm_num
        rw [← Finset.sum_mul, ← Finset.sum_mul, hchoose]
        ring
    _ ≤ ((1 + (2 : ℝ) ^ l) * (A + 1) + 1) * (Real.sin (2 * θ) * K) := by
        refine mul_le_mul_of_nonneg_right ?_ hsK
        have h2i : (0 : ℝ) ≤ (2 : ℝ) ^ i := pow_nonneg (by norm_num) i
        have h2l : (0 : ℝ) ≤ (2 : ℝ) ^ l := pow_nonneg (by norm_num) l
        have hpow : (2 : ℝ) ^ i ≤ (2 : ℝ) ^ l := pow_le_pow_right₀ (by norm_num) hil
        nlinarith [mul_le_mul_of_nonneg_right hpow hApos.le]
    _ = ((1 + (2 : ℝ) ^ l) * (A + 1) + 1) * Real.sin (2 * θ) * K := by ring

end Work.FTS.TransportS
end
end
-- ===== merged: Submission.Work.FTS.TransportS.sup_dz_le_hk =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.TransportS

set_option autoImplicit false
set_option maxHeartbeats 1000000

/-! ## Helpers for the assembly -/

/-- `D_z^b (c(θ) · g) = c(θ) · D_z^b g` for a factor `c` depending on `θ` only. -/
theorem DzIter_const_mul (b : ℕ) (c : ℝ → ℝ) (g : ℝ → ℝ → ℝ) (z θ : ℝ) :
    Work.Spaces.DzIter b (fun z θ' => c θ' * g z θ') z θ
      = c θ * Work.Spaces.DzIter b g z θ := by
  induction b generalizing z θ with
  | zero => rfl
  | succ b ih =>
      show z * deriv (fun z' => Work.Spaces.DzIter b (fun z θ' => c θ' * g z θ') z' θ) z
        = c θ * (z * deriv (fun z' => Work.Spaces.DzIter b g z' θ) z)
      have hev : (fun z' => Work.Spaces.DzIter b (fun z θ' => c θ' * g z θ') z' θ)
          = fun z' => c θ * Work.Spaces.DzIter b g z' θ := by
        funext z'
        exact ih z' θ
      rw [hev]
      have hder : deriv (fun z' => c θ * Work.Spaces.DzIter b g z' θ) z
          = c θ * deriv (fun z' => Work.Spaces.DzIter b g z' θ) z :=
        deriv_const_mul_field (c θ)
      rw [hder]
      ring

/-- `mixed b 1 f = sin(2θ) · ∂_θ (D_z^b f)` on the open quadrant, for a `SmoothOpen` datum. -/
theorem mixed_one_eq_sin_mul_pth {f : ℝ → ℝ → ℝ} (hF : Work.FTS.EllipticEst.SmoothOpen f)
    (b : ℕ) {z θ : ℝ} (hz : 0 < z) (hθ : θ ∈ Set.Ioo (0 : ℝ) (π / 2)) :
    Work.Spaces.mixed b 1 f z θ
      = Real.sin (2 * θ) * Work.Spaces.pth (Work.Spaces.DzIter b f) z θ := by
  have h1 : Work.Spaces.mixed b 1 f z θ
      = Work.Spaces.DzIter b (fun z θ' => Real.sin (2 * θ') * Work.Spaces.pth f z θ') z θ := by
    rfl
  rw [h1, DzIter_const_mul b (fun θ' => Real.sin (2 * θ')) (Work.Spaces.pth f) z θ]
  have h2 : Work.Spaces.pth (Work.Spaces.DzIter b f) z θ
      = Work.Spaces.DzIter b (Work.Spaces.pth f) z θ :=
    Work.FTS.EllipticEst.ThetaU.OpenSliceAux.pth_DzIter_eqOn_of_isOpen
      Work.FTS.EllipticEst.isOpen_Q0 ((Work.FTS.EllipticEst.smoothOpen_iff_forall f).mp hF) b
      (Work.FTS.EllipticEst.mem_Q0.mpr ⟨hz, hθ.1, hθ.2⟩)
  rw [h2]

/-- Over the middle half `[π/8, 3π/8]` of `Iθ`, some point has value at most `(4/π)` times
the integral over `Iθ` (the open-class replacement of `MinLeAvg`, which needs continuity
on the *closed* interval `Iθ`). -/
theorem min_mid_le_avg {φ : ℝ → ℝ}
    (hcont : ContinuousOn φ (Set.Icc (π / 8) (3 * π / 8)))
    (hint : MeasureTheory.IntegrableOn φ Work.Spaces.Iθ)
    (hnn : ∀ θ ∈ Work.Spaces.Iθ, 0 ≤ φ θ) :
    ∃ θ₀ ∈ Set.Icc (π / 8) (3 * π / 8),
      φ θ₀ ≤ (4 / Real.pi) * ∫ θ in Work.Spaces.Iθ, φ θ := by
  have hle : π / 8 ≤ 3 * π / 8 := by linarith [Real.pi_pos]
  obtain ⟨θ₀, hθ₀, hmin⟩ :=
    (isCompact_Icc (a := π / 8) (b := 3 * π / 8)).exists_isMinOn
      ⟨π / 8, by simp only [Set.mem_Icc]; exact ⟨le_rfl, hle⟩⟩ hcont
  refine ⟨θ₀, hθ₀, ?_⟩
  have hsub : Set.Icc (π / 8) (3 * π / 8) ⊆ Work.Spaces.Iθ := by
    intro x hx
    simp only [Work.Spaces.Iθ, Set.mem_Icc]
    exact ⟨by linarith [hx.1, Real.pi_pos], by linarith [hx.2, Real.pi_pos]⟩
  have hmeas : MeasurableSet (Set.Icc (π / 8) (3 * π / 8)) := measurableSet_Icc
  have hIccint : MeasureTheory.IntegrableOn φ (Set.Icc (π / 8) (3 * π / 8)) :=
    hcont.integrableOn_compact isCompact_Icc
  have hconst : MeasureTheory.IntegrableOn (fun _ : ℝ => φ θ₀)
      (Set.Icc (π / 8) (3 * π / 8)) :=
    integrableOn_const (μ := MeasureTheory.volume)
      (isCompact_Icc (a := π / 8) (b := 3 * π / 8)).measure_lt_top.ne (by simp)
  have hmono : ∫ θ in Set.Icc (π / 8) (3 * π / 8), φ θ₀
      ≤ ∫ θ in Set.Icc (π / 8) (3 * π / 8), φ θ :=
    setIntegral_mono_on hconst hIccint hmeas (fun θ hθ => hmin hθ)
  have hval : ∫ θ in Set.Icc (π / 8) (3 * π / 8), φ θ₀ = φ θ₀ * (π / 4) := by
    rw [setIntegral_const, MeasureTheory.Measure.real_def, Real.volume_Icc,
      ENNReal.toReal_ofReal (by linarith [Real.pi_pos] : (0 : ℝ) ≤ 3 * π / 8 - π / 8)]
    ring
  have h2 : (∫ θ in Set.Icc (π / 8) (3 * π / 8), φ θ)
      ≤ ∫ θ in Work.Spaces.Iθ, φ θ := by
    rw [show Work.Spaces.Iθ = Set.Icc (0 : ℝ) (π / 2) from rfl]
    exact MeasureTheory.setIntegral_mono_set hint
      (MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc hnn)
      (Filter.Eventually.of_forall (fun x hx => hsub hx))
  have h3 : φ θ₀ * (π / 4) ≤ ∫ θ in Work.Spaces.Iθ, φ θ := by
    rw [← hval]
    exact hmono.trans h2
  have h4 : φ θ₀ ≤ (∫ θ in Work.Spaces.Iθ, φ θ) / (π / 4) :=
    (le_div_iff₀ (by linarith [Real.pi_pos] : (0 : ℝ) < π / 4)).mpr (by linarith [h3])
  calc φ θ₀ ≤ (∫ θ in Work.Spaces.Iθ, φ θ) / (π / 4) := h4
    _ = (4 / Real.pi) * ∫ θ in Work.Spaces.Iθ, φ θ := by
        rw [div_eq_mul_inv, inv_div]
        ring

/-- `volume.restrict Iθ = volume.restrict (0, π/2)`. -/
theorem restrict_Iθ_eq :
    MeasureTheory.volume.restrict Work.Spaces.Iθ
      = MeasureTheory.volume.restrict (Set.Ioo (0 : ℝ) (π / 2)) := by
  have h : Set.Ioo (0 : ℝ) (π / 2) =ᵐ[MeasureTheory.volume] Work.Spaces.Iθ :=
    MeasureTheory.Ioo_ae_eq_Icc
  exact MeasureTheory.Measure.restrict_congr_set h.symm

/-! ## The target -/

theorem sup_dz_le_hk :
    ∃ C : ℝ, 0 < C ∧ ∀ (α : ℝ) (f : ℝ → ℝ → ℝ), 0 < α → α ≤ 1 →
      Work.FTS.EllipticEst.SmoothOpen f → Work.Spaces.HkMem α 4 f →
      ∀ b : ℕ, b ≤ 2 → ∀ z θ : ℝ, 0 < z → 0 < θ → θ < π / 2 →
        |Work.Spaces.DzIter b f z θ| ≤ C / Real.sqrt (Work.Spaces.gam α - 1)
          * Work.FTS.Nonlin.Xn α f := by
  obtain ⟨CV, hCVpos, hV⟩ := Work.FTS.TransportS.SupDzAux.sup_dz_avg_le
  obtain ⟨CA, hCApos, hA⟩ := Work.FTS.TransportS.SupDzAux.sup_dz_ang_le
  set K : ℝ := 200 * CA + 8 / Real.pi * CV with hKdef
  have hKnn : 0 ≤ K := by rw [hKdef]; positivity
  refine ⟨Real.sqrt K + 1, by positivity, ?_⟩
  intro α f hα hα1 hF hmem b hb z θ hz hθ hθ1
  have hγ1 : 0 < Work.Spaces.gam α - 1 := by rw [Work.Spaces.gam_sub_one]; linarith
  have hγ1le : Work.Spaces.gam α - 1 ≤ 1 := by rw [Work.Spaces.gam_sub_one]; linarith
  have hγ2 : Work.Spaces.gam α < 2 := by rw [Work.Spaces.gam]; linarith
  have hHk : 0 ≤ Work.Spaces.HkSq α 4 f := Work.Spaces.HkSq_nonneg α 4 f
  have hzI : z ∈ Work.Spaces.Iz := hz.le
  have hθI : θ ∈ Work.Spaces.Iθ := ⟨hθ.le, hθ1.le⟩
  have hw1 : 1 ≤ (Work.Spaces.w z) ^ 2 := by
    have := one_le_w hz
    nlinarith
  -- pointwise domination by the `ℋ⁴`-integrand
  have hdom : ∀ σ ∈ Set.Ioo (0 : ℝ) (π / 2),
      (Work.Spaces.DzIter b f z σ) ^ 2 ≤ Work.Spaces.HkIntegrand α 4 f z σ := by
    intro σ hσ
    have hsin : 0 < Real.sin (2 * σ) :=
      Real.sin_pos_of_pos_of_lt_pi (by linarith [hσ.1]) (by linarith [hσ.2, Real.pi_pos])
    have h1 : (Work.Spaces.DzIter b f z σ) ^ 2 * (Work.Spaces.w z) ^ 2
        ≤ Work.Spaces.HkIntegrand α 4 f z σ :=
      Work.FTS.H2.dzIter_sq_w_le_HkIntegrand α f hsin b (by omega)
    have h2 : (Work.Spaces.DzIter b f z σ) ^ 2
        ≤ (Work.Spaces.DzIter b f z σ) ^ 2 * (Work.Spaces.w z) ^ 2 :=
      le_mul_of_one_le_right (sq_nonneg _) hw1
    exact le_trans h2 h1
  -- the angular domination
  have hdomA : ∀ σ ∈ Set.Ioo (0 : ℝ) (π / 2),
      (Work.Spaces.pth (Work.Spaces.DzIter b f) z σ) ^ 2
          * (Real.sin (2 * σ)) ^ (2 - Work.Spaces.gam α)
        ≤ Work.Spaces.HkIntegrand α 4 f z σ := by
    intro σ hσ
    have hsin : 0 < Real.sin (2 * σ) :=
      Real.sin_pos_of_pos_of_lt_pi (by linarith [hσ.1]) (by linarith [hσ.2, Real.pi_pos])
    have hθσ : σ ∈ Work.Spaces.Iθ := ⟨hσ.1.le, hσ.2.le⟩
    have hmix : Work.Spaces.mixed b 1 f z σ
        = Real.sin (2 * σ) * Work.Spaces.pth (Work.Spaces.DzIter b f) z σ :=
      mixed_one_eq_sin_mul_pth hF b hz hσ
    have hsγ : (Real.sin (2 * σ)) ^ (2 - Work.Spaces.gam α)
        = (Real.sin (2 * σ)) ^ 2 * (Real.sin (2 * σ)) ^ (-(Work.Spaces.gam α)) := by
      rw [show 2 - Work.Spaces.gam α = 2 + (-(Work.Spaces.gam α)) by ring,
        Real.rpow_add hsin, Real.rpow_two]
    have hWt : (Work.Spaces.Wt α z σ) ^ 2
        = (Work.Spaces.w z) ^ 2 * (Real.sin (2 * σ)) ^ (-(Work.Spaces.gam α)) :=
      Work.FTS.H2.Wt_sq α hα z σ hθσ
    have hslot : (Work.Spaces.mixed b 1 f z σ * Work.Spaces.Wt α z σ) ^ 2
        ≤ Work.Spaces.HkIntegrand α 4 f z σ :=
      Work.Spaces.sq_le_HkIntegrand_mixed α 4 f z σ 1 b le_rfl (by omega)
    have hnn : 0 ≤ (Real.sin (2 * σ)) ^ (-(Work.Spaces.gam α)) :=
      Real.rpow_nonneg hsin.le _
    calc (Work.Spaces.pth (Work.Spaces.DzIter b f) z σ) ^ 2
          * (Real.sin (2 * σ)) ^ (2 - Work.Spaces.gam α)
        = (Real.sin (2 * σ) * Work.Spaces.pth (Work.Spaces.DzIter b f) z σ) ^ 2
            * (Real.sin (2 * σ)) ^ (-(Work.Spaces.gam α)) := by
          rw [hsγ]
          ring
      _ = (Work.Spaces.mixed b 1 f z σ) ^ 2
            * (Real.sin (2 * σ)) ^ (-(Work.Spaces.gam α)) := by
          rw [← hmix]
      _ ≤ (Work.Spaces.mixed b 1 f z σ * Work.Spaces.Wt α z σ) ^ 2 := by
          have hle : (Real.sin (2 * σ)) ^ (-(Work.Spaces.gam α))
              ≤ (Real.sin (2 * σ)) ^ (-(Work.Spaces.gam α)) * (Work.Spaces.w z) ^ 2 :=
            le_mul_of_one_le_right hnn hw1
          calc (Work.Spaces.mixed b 1 f z σ) ^ 2 * (Real.sin (2 * σ)) ^ (-(Work.Spaces.gam α))
              ≤ (Work.Spaces.mixed b 1 f z σ) ^ 2
                  * ((Real.sin (2 * σ)) ^ (-(Work.Spaces.gam α)) * (Work.Spaces.w z) ^ 2) :=
                mul_le_mul_of_nonneg_left hle (sq_nonneg _)
            _ = (Work.Spaces.mixed b 1 f z σ * Work.Spaces.Wt α z σ) ^ 2 := by
                rw [mul_pow, hWt]
                ring
      _ ≤ Work.Spaces.HkIntegrand α 4 f z σ := hslot
  -- integrability of the two slices at the fixed `z`
  have hintu : MeasureTheory.IntegrableOn
      (fun σ => (Work.Spaces.DzIter b f z σ) ^ 2) Work.Spaces.Iθ := by
    refine MeasureTheory.Integrable.mono' (hmem.1 z hzI) ?_ ?_
    · have hcont2 : ContinuousOn (fun p : ℝ × ℝ => (Work.Spaces.DzIter b f p.1 p.2) ^ 2)
          Work.FTS.EllipticEst.Q0 := (hF.DzIter b).continuousOn.pow 2
      exact Work.Spaces.aesm_slice_of_continuousOn_Qd
        (fun p : ℝ × ℝ => (Work.Spaces.DzIter b f p.1 p.2) ^ 2) hcont2 hz
    · rw [restrict_Iθ_eq]
      refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioo (fun σ hσ => ?_)
      rw [Real.norm_of_nonneg (sq_nonneg _)]
      exact hdom σ hσ
  have hintA : MeasureTheory.IntegrableOn
      (fun σ => (Work.Spaces.pth (Work.Spaces.DzIter b f) z σ) ^ 2
        * (Real.sin (2 * σ)) ^ (2 - Work.Spaces.gam α)) Work.Spaces.Iθ := by
    refine MeasureTheory.Integrable.mono' (hmem.1 z hzI) ?_ ?_
    · have hcont2 : ContinuousOn
          (fun p : ℝ × ℝ => (Work.Spaces.pth (Work.Spaces.DzIter b f) p.1 p.2) ^ 2
            * (Real.sin (2 * p.2)) ^ (2 - Work.Spaces.gam α)) Work.FTS.EllipticEst.Q0 := by
        refine ((hF.DzIter b).pth).continuousOn.pow 2 |>.mul ?_
        refine (Real.continuous_sin.comp_continuousOn
          ((continuous_const.mul continuous_snd).continuousOn)).rpow_const ?_
        intro p _
        exact Or.inr (by linarith : (0 : ℝ) ≤ 2 - Work.Spaces.gam α)
      exact Work.Spaces.aesm_slice_of_continuousOn_Qd
        (fun p : ℝ × ℝ => (Work.Spaces.pth (Work.Spaces.DzIter b f) p.1 p.2) ^ 2
          * (Real.sin (2 * p.2)) ^ (2 - Work.Spaces.gam α)) hcont2 hz
    · rw [restrict_Iθ_eq]
      refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioo (fun σ hσ => ?_)
      have hsin : 0 < Real.sin (2 * σ) :=
        Real.sin_pos_of_pos_of_lt_pi (by linarith [hσ.1]) (by linarith [hσ.2, Real.pi_pos])
      rw [Real.norm_of_nonneg (mul_nonneg (sq_nonneg _) (Real.rpow_nonneg hsin.le _))]
      exact hdomA σ hσ
  -- the minimiser of `(D_z^b f z ·)²` over the middle half
  have hcontmid : ContinuousOn (fun σ => (Work.Spaces.DzIter b f z σ) ^ 2)
      (Set.Icc (π / 8) (3 * π / 8)) := by
    have hc : ContinuousOn (fun σ => Work.Spaces.DzIter b f z σ) (Set.Ioo (0 : ℝ) (π / 2)) :=
      ((hF.DzIter b).curry_θ hz).continuousOn
    refine (hc.mono ?_).pow 2
    intro σ hσ
    exact ⟨by linarith [hσ.1, Real.pi_pos], by linarith [hσ.2, Real.pi_pos]⟩
  obtain ⟨θ₀, hθ₀mem, hθ₀le⟩ :=
    min_mid_le_avg hcontmid hintu (fun σ _ => sq_nonneg _)
  have hθ₀I : θ₀ ∈ Work.Spaces.Iθ :=
    ⟨by linarith [hθ₀mem.1, Real.pi_pos], by linarith [hθ₀mem.2, Real.pi_pos]⟩
  have hsub : Set.uIcc θ θ₀ ⊆ Set.Ioo (0 : ℝ) (π / 2) := by
    intro x hx
    rw [Set.mem_uIcc] at hx
    rcases hx with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact ⟨by linarith [h1], by linarith [h2, hθ₀mem.2, Real.pi_pos]⟩
    · exact ⟨by linarith [hθ₀mem.1, Real.pi_pos, h1], by linarith [h2]⟩
  have hderiv : ∀ x ∈ Set.uIcc θ θ₀,
      HasDerivAt (fun σ => Work.Spaces.DzIter b f z σ)
        (deriv (fun σ => Work.Spaces.DzIter b f z σ) x) x := by
    intro x hx
    have hxI := hsub hx
    have hc := ((hF.DzIter b).curry_θ hz).differentiableOn
      Work.FTS.LocData.smoothOrder_ne_zero
    exact (hc.differentiableAt (isOpen_Ioo.mem_nhds hxI)).hasDerivAt
  have hcontd : ContinuousOn (deriv (fun σ => Work.Spaces.DzIter b f z σ)) (Set.uIcc θ θ₀) := by
    have hc : ContinuousOn (fun σ => Work.Spaces.pth (Work.Spaces.DzIter b f) z σ)
        (Set.Ioo (0 : ℝ) (π / 2)) := ((hF.DzIter b).pth.curry_θ hz).continuousOn
    exact hc.mono hsub
  have hosc := Work.FTS.H2.OscSqLe α hα hα1 (fun σ => Work.Spaces.DzIter b f z σ)
    hθI hθ₀I hderiv hcontd hintA
  -- the two uniform-in-`z` bounds
  set A : ℝ := ∫ σ in Work.Spaces.Iθ, (Work.Spaces.pth (Work.Spaces.DzIter b f) z σ) ^ 2
      * (Real.sin (2 * σ)) ^ (2 - Work.Spaces.gam α) with hAdef
  set V : ℝ := ∫ σ in Work.Spaces.Iθ, (Work.Spaces.DzIter b f z σ) ^ 2 with hVdef
  have hAb : A ≤ CA * Work.Spaces.HkSq α 4 f := by
    rw [hAdef]; exact hA α f b hα hα1 hF hmem hb z hz
  have hVb : V ≤ CV * Work.Spaces.HkSq α 4 f := by
    rw [hVdef]; exact hV α f b hα hα1 hF hmem hb z hz
  have hoscA : (Work.Spaces.DzIter b f z θ - Work.Spaces.DzIter b f z θ₀) ^ 2
      ≤ (100 / (Work.Spaces.gam α - 1)) * A := by
    rw [hAdef]
    simpa only [Work.Spaces.pth] using hosc
  have hminA : (Work.Spaces.DzIter b f z θ₀) ^ 2 ≤ (4 / Real.pi) * V := by
    rw [hVdef]
    exact hθ₀le
  -- the combination
  have key : (Work.Spaces.DzIter b f z θ) ^ 2 ≤ K / (Work.Spaces.gam α - 1)
      * Work.Spaces.HkSq α 4 f := by
    have h1 : (Work.Spaces.DzIter b f z θ) ^ 2
        ≤ 2 * (Work.Spaces.DzIter b f z θ - Work.Spaces.DzIter b f z θ₀) ^ 2
          + 2 * (Work.Spaces.DzIter b f z θ₀) ^ 2 :=
      by nlinarith [sq_nonneg (Work.Spaces.DzIter b f z θ - 2 * Work.Spaces.DzIter b f z θ₀)]
    have h2 : 2 * (Work.Spaces.DzIter b f z θ - Work.Spaces.DzIter b f z θ₀) ^ 2
        ≤ (200 / (Work.Spaces.gam α - 1)) * A := by
      have h3 := mul_le_mul_of_nonneg_left hoscA (by norm_num : (0 : ℝ) ≤ 2)
      have h4 : (200 / (Work.Spaces.gam α - 1)) * A
          = 2 * ((100 / (Work.Spaces.gam α - 1)) * A) := by ring
      linarith [h3, h4.le, h4.ge]
    have h3 : 2 * (Work.Spaces.DzIter b f z θ₀) ^ 2 ≤ (8 / Real.pi) * V := by
      have h4 := mul_le_mul_of_nonneg_left hminA (by norm_num : (0 : ℝ) ≤ 2)
      have h5 : (8 / Real.pi) * V = 2 * ((4 / Real.pi) * V) := by ring
      linarith [h4, h5.le, h5.ge]
    have hA' : (200 / (Work.Spaces.gam α - 1)) * A
        ≤ (200 * CA / (Work.Spaces.gam α - 1)) * Work.Spaces.HkSq α 4 f := by
      calc (200 / (Work.Spaces.gam α - 1)) * A
          ≤ (200 / (Work.Spaces.gam α - 1)) * (CA * Work.Spaces.HkSq α 4 f) :=
            mul_le_mul_of_nonneg_left hAb (by positivity)
        _ = (200 * CA / (Work.Spaces.gam α - 1)) * Work.Spaces.HkSq α 4 f := by ring
    have hV' : (8 / Real.pi) * V
        ≤ ((8 / Real.pi) * CV / (Work.Spaces.gam α - 1)) * Work.Spaces.HkSq α 4 f := by
      have hγinv : (1 : ℝ) ≤ 1 / (Work.Spaces.gam α - 1) := by
        rw [le_div_iff₀ hγ1]
        simpa using hγ1le
      have hcoef : 0 ≤ (8 / Real.pi) * CV * Work.Spaces.HkSq α 4 f := by positivity
      have h5 : (8 / Real.pi) * CV * Work.Spaces.HkSq α 4 f
          ≤ (8 / Real.pi) * CV * (1 / (Work.Spaces.gam α - 1)) * Work.Spaces.HkSq α 4 f := by
        have h6 : (8 / Real.pi) * CV * 1 ≤ (8 / Real.pi) * CV * (1 / (Work.Spaces.gam α - 1)) :=
          mul_le_mul_of_nonneg_left hγinv (by positivity)
        calc (8 / Real.pi) * CV * Work.Spaces.HkSq α 4 f
            = ((8 / Real.pi) * CV * 1) * Work.Spaces.HkSq α 4 f := by ring
          _ ≤ ((8 / Real.pi) * CV * (1 / (Work.Spaces.gam α - 1)))
                * Work.Spaces.HkSq α 4 f := mul_le_mul_of_nonneg_right h6 hHk
          _ = (8 / Real.pi) * CV * (1 / (Work.Spaces.gam α - 1))
                * Work.Spaces.HkSq α 4 f := by ring
      calc (8 / Real.pi) * V
          ≤ (8 / Real.pi) * (CV * Work.Spaces.HkSq α 4 f) :=
            mul_le_mul_of_nonneg_left hVb (by positivity)
        _ = (8 / Real.pi) * CV * Work.Spaces.HkSq α 4 f := by ring
        _ ≤ (8 / Real.pi) * CV * (1 / (Work.Spaces.gam α - 1)) * Work.Spaces.HkSq α 4 f := h5
        _ = ((8 / Real.pi) * CV / (Work.Spaces.gam α - 1)) * Work.Spaces.HkSq α 4 f := by ring
    calc (Work.Spaces.DzIter b f z θ) ^ 2
        ≤ 2 * (Work.Spaces.DzIter b f z θ - Work.Spaces.DzIter b f z θ₀) ^ 2
          + 2 * (Work.Spaces.DzIter b f z θ₀) ^ 2 := h1
      _ ≤ (200 / (Work.Spaces.gam α - 1)) * A + (8 / Real.pi) * V := add_le_add h2 h3
      _ ≤ (200 * CA / (Work.Spaces.gam α - 1)) * Work.Spaces.HkSq α 4 f
            + ((8 / Real.pi) * CV / (Work.Spaces.gam α - 1)) * Work.Spaces.HkSq α 4 f :=
          add_le_add hA' hV'
      _ = K / (Work.Spaces.gam α - 1) * Work.Spaces.HkSq α 4 f := by
          rw [hKdef]; ring
  -- conclude
  have h2sq : Real.sqrt (K / (Work.Spaces.gam α - 1) * Work.Spaces.HkSq α 4 f)
      = Real.sqrt K / Real.sqrt (Work.Spaces.gam α - 1) * Work.Spaces.HkNorm α 4 f := by
    rw [Real.sqrt_mul (by positivity : (0 : ℝ) ≤ K / (Work.Spaces.gam α - 1)),
      Real.sqrt_div hKnn, Work.Spaces.HkNorm]
  have h3 : Real.sqrt K / Real.sqrt (Work.Spaces.gam α - 1) * Work.Spaces.HkNorm α 4 f
      ≤ (Real.sqrt K + 1) / Real.sqrt (Work.Spaces.gam α - 1)
        * Work.Spaces.HkNorm α 4 f := by
    have hγs : 0 < Real.sqrt (Work.Spaces.gam α - 1) := Real.sqrt_pos.mpr hγ1
    have h4 : Real.sqrt K / Real.sqrt (Work.Spaces.gam α - 1)
        ≤ (Real.sqrt K + 1) / Real.sqrt (Work.Spaces.gam α - 1) := by
      rw [div_le_div_iff_of_pos_right hγs]
      linarith
    exact mul_le_mul_of_nonneg_right h4 (Work.Spaces.HkNorm_nonneg α 4 f)
  calc |Work.Spaces.DzIter b f z θ| ≤ Real.sqrt (K / (Work.Spaces.gam α - 1)
        * Work.Spaces.HkSq α 4 f) := Real.abs_le_sqrt key
    _ = Real.sqrt K / Real.sqrt (Work.Spaces.gam α - 1) * Work.Spaces.HkNorm α 4 f := h2sq
    _ ≤ (Real.sqrt K + 1) / Real.sqrt (Work.Spaces.gam α - 1)
          * Work.Spaces.HkNorm α 4 f := h3
    _ = (Real.sqrt K + 1) / Real.sqrt (Work.Spaces.gam α - 1)
          * Work.FTS.Nonlin.Xn α f := rfl

end Work.FTS.TransportS
end
end
