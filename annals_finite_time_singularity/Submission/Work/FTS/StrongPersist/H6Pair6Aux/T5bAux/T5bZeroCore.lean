import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.T5bAux.T5bZeroAux
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.T5bAux.dzSelf1dW
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.T5bAux.dzSelf2dW
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.slotProd
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.intSlotLeHkSq
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.Ip6DzAux
import Submission.Work.Construction.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open MeasureTheory Set Filter
open scoped Real Topology

namespace Work.FTS.StrongPersist.H6Pair6Aux.T5bAux

set_option maxHeartbeats 1600000

noncomputable section

/-- **The `k = 0` top term of the `T5b` row.** -/
theorem T5bZeroTerm_core {α : ℝ} {f : ℝ → ℝ → ℝ} {CL : ℝ} (hCLpos : 0 < CL)
    (hCL : ∀ k ≤ 4, ∀ z : ℝ, 0 < z →
      |Work.Elliptic.DzdIter k (fun z => Work.Construction.L12 f z) z|
        ≤ CL * Work.Spaces.HkNorm α 4 f)
    (hψsm : ContDiffOn ℝ 1 (fun z => Work.Construction.L12 f z) (Set.Ioi 0))
    (a b : ℕ) {σ : ℝ → ℝ}
    (hσcont : ContinuousOn (fun p : ℝ × ℝ => σ p.2)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2) : Set (ℝ × ℝ)))
    (hσnn : ∀ θ ∈ Set.Ioo 0 (π / 2), 0 ≤ σ θ)
    (hσcap : ∀ θ ∈ Set.Ioo 0 (π / 2),
      σ θ ≤ (Real.sin (2 * θ)) ^ (-(if a = 0 then Work.Spaces.eta else Work.Spaces.gam α)))
    (hα : 0 < α) (hsm : Work.FTS.EllipticEst.SmoothOpen f)
    (hm6 : Work.Spaces.HkMem α 6 f) (hm7 : Work.Spaces.HkMem α 7 f)
    (hab : a + b ≤ 6) :
    |∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
        (Work.Spaces.w z) ^ 2 * σ θ * (Work.Construction.c2m θ * Work.Construction.L12 f z)
          * Work.Spaces.mixed (b + 1) a f z θ * Work.Spaces.mixed b a f z θ|
      ≤ 8 * CL * (1 + Work.FTS.Nonlin.Xn α f) ^ 4 * (1 + Work.Spaces.HkSq α 6 f) := by
  set V : ℝ → ℝ → ℝ := fun z θ => Work.Spaces.mixed b a f z θ with hVdef
  set ψ : ℝ → ℝ := fun z => Work.Construction.L12 f z with hψdef
  set θw : ℝ → ℝ := fun θ => σ θ * Work.Construction.c2m θ with hθwdef
  set q : ℝ := (if a = 0 then Work.Spaces.eta else Work.Spaces.gam α) with hqdef
  set Xn : ℝ := Work.Spaces.HkNorm α 4 f with hXndef
  set A : ℝ := CL * Xn with hAdef
  have hXn0 : 0 ≤ Xn := by rw [hXndef]; exact Work.Spaces.HkNorm_nonneg α 4 f
  have hA0 : 0 ≤ A := by rw [hAdef]; positivity
  have hHk0 : 0 ≤ Work.Spaces.HkSq α 6 f := Work.Spaces.HkSq_nonneg α 6 f
  -- ## the ψ-bounds
  have hψA : ∀ z ∈ Set.Ioi (0:ℝ), |ψ z| ≤ A := by
    intro z hz
    have h := hCL 0 (by norm_num) z hz
    simpa using h
  have hψB : ∀ z ∈ Set.Ioi (0:ℝ), |z * deriv ψ z| ≤ A := by
    intro z hz
    have h := hCL 1 (by norm_num) z hz
    have h1 : Work.Elliptic.DzdIter 1 ψ z = z * deriv ψ z := rfl
    rw [h1] at h
    exact h
  have hψsm' : ContDiffOn ℝ 1 ψ (Set.Ioi 0) := by
    rw [hψdef]; exact hψsm
  have hψcOn : ContinuousOn ψ (Set.Ioi 0) := hψsm'.continuousOn
  have h1d : ∀ (Y : ℝ → ℝ), ContDiffOn ℝ 1 Y (Set.Ioi 0) →
      MeasureTheory.IntegrableOn (fun z => (Work.Spaces.w z) ^ 2 * (Y z) ^ 2) (Set.Ioi 0) →
      MeasureTheory.IntegrableOn (fun z => (Work.Spaces.w z) ^ 2 * (z * deriv Y z) ^ 2)
        (Set.Ioi 0) →
      |∫ z in Set.Ioi 0, (Work.Spaces.w z) ^ 2 * ψ z * ((z * deriv Y z) * Y z)|
        ≤ (3 * A + A) * ∫ z in Set.Ioi 0, (Work.Spaces.w z) ^ 2 * (Y z) ^ 2 :=
    fun Y hY hF hD =>
      dzSelf1dW (ψ := ψ) (Y := Y) (A := A) (B := A) hA0 hA0 hψsm' hψA hψB hY hF hD
  -- ## measurability and slices
  have hσθm : AEMeasurable σ (MeasureTheory.volume.restrict Work.Spaces.Iθ) := by
    have hc : ContinuousOn (fun θ : ℝ => σ θ) (Set.Ioo 0 (π / 2)) := by
      have h2 : ContinuousOn (fun θ : ℝ => ((1:ℝ), θ)) (Set.Ioo 0 (π / 2)) :=
        continuousOn_const.prodMk continuousOn_id
      exact (hσcont.comp h2 (fun θ hθ => ⟨by norm_num, hθ⟩)).congr (fun θ _ => rfl)
    rw [MeasureTheory.Measure.restrict_congr_set
      (Work.FTS.StrongPersist.H6Pair6Aux.dzSelf2d_Ith_ae)]
    exact hc.aemeasurable measurableSet_Ioo
  have hθwm : AEMeasurable θw (MeasureTheory.volume.restrict Work.Spaces.Iθ) := by
    have he : θw = fun θ => σ θ * Work.Construction.c2m θ := by rw [hθwdef]
    rw [he]
    exact hσθm.mul aemeasurable_c2m_Iθ
  have hqV : ∀ θ ∈ Set.Ioo (0:ℝ) (π/2), σ θ ≤ (Real.sin (2*θ)) ^ (-q) := by
    intro θ hθ
    rw [hqdef]
    exact hσcap θ hθ
  have hVc : ContinuousOn (Function.uncurry V) (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)) := by
    have h2 : Function.uncurry V = Function.uncurry (Work.Spaces.mixed b a f) := by
      funext p; simp only [Function.uncurry, hVdef]
    rw [h2]
    exact (hsm.mixed b a).continuousOn
  have hWc : ContinuousOn (Function.uncurry (fun z θ => Work.Spaces.mixed (b+1) a f z θ))
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)) := (hsm.mixed (b+1) a).continuousOn
  have hVslice : ∀ θ ∈ Set.Ioo 0 (π / 2), ContDiffOn ℝ 1 (fun z => V z θ) (Set.Ioi 0) := by
    intro θ hθ
    have h := Work.FTS.StrongPersist.H6Pair6Aux.SmoothOpen.slice (hsm.mixed b a) hθ 1
    have he : (fun z : ℝ => Work.Spaces.mixed b a f z θ) = fun z : ℝ => V z θ := by
      funext z; simp only [hVdef]
    rw [he] at h
    exact h
  have hVae : AEMeasurable (Function.uncurry V) Lprod :=
    (Work.Spaces.aesm_of_continuousOn_Qd (Function.uncurry V) hVc).aemeasurable
  -- ## the ae-strongly-measurable factors
  have hwae : AEStronglyMeasurable (fun p : ℝ × ℝ => (Work.Spaces.w p.1)^2) Lprod :=
    Work.Spaces.aesm_of_continuousOn_Qd _
      Work.FTS.StrongPersist.H6Pair6Aux.continuousOn_w_sq_Q0
  have hσae : AEStronglyMeasurable (fun p : ℝ × ℝ => σ p.2) Lprod :=
    Work.Spaces.aesm_of_continuousOn_Qd _ hσcont
  have hc2ae : AEStronglyMeasurable (fun p : ℝ × ℝ => Work.Construction.c2m p.2) Lprod :=
    Work.Spaces.aesm_of_continuousOn_Qd _ continuousOn_c2m_Q0
  have hVae2 : AEStronglyMeasurable (fun p : ℝ × ℝ => (V p.1 p.2)^2) Lprod :=
    Work.Spaces.aesm_of_continuousOn_Qd _ (hVc.pow 2)
  have hWae2 : AEStronglyMeasurable
      (fun p : ℝ × ℝ => (Work.Spaces.mixed (b+1) a f p.1 p.2)^2) Lprod :=
    Work.Spaces.aesm_of_continuousOn_Qd _ (hWc.pow 2)
  have hψae : AEStronglyMeasurable (fun p : ℝ × ℝ => ψ p.1) Lprod := by
    have hcon : ContinuousOn (fun p : ℝ × ℝ => ψ p.1)
        (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2) : Set (ℝ × ℝ)) :=
      (hψcOn.comp continuousOn_fst (fun p hp => hp.1)).congr (fun p _ => rfl)
    exact Work.Spaces.aesm_of_continuousOn_Qd _ hcon
  have hθwae : AEStronglyMeasurable (fun p : ℝ × ℝ => |θw p.2|) Lprod := by
    have hcon : ContinuousOn (fun p : ℝ × ℝ => |θw p.2|)
        (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2) : Set (ℝ × ℝ)) := by
      have he : (fun p : ℝ × ℝ => |θw p.2|)
          = fun p : ℝ × ℝ => |σ p.2 * Work.Construction.c2m p.2| := by
        funext p; rw [hθwdef]
      rw [he]
      exact (hσcont.mul continuousOn_c2m_Q0).abs
    exact Work.Spaces.aesm_of_continuousOn_Qd _ hcon
  have hθw2 : AEStronglyMeasurable (fun p : ℝ × ℝ => θw p.2) Lprod := by
    have he : (fun p : ℝ × ℝ => θw p.2)
        = fun p : ℝ × ℝ => σ p.2 * Work.Construction.c2m p.2 := by
      funext p; rw [hθwdef]
    rw [he]
    exact hσae.mul hc2ae
  -- ## the slot majorants
  have hbigV : MeasureTheory.Integrable (fun p : ℝ × ℝ =>
      (Work.Spaces.w p.1)^2 * (Real.sin (2*p.2)) ^ (-q) * (V p.1 p.2)^2) Lprod := by
    rw [hqdef]
    by_cases ha0 : a = 0
    · subst ha0
      rw [if_pos rfl]
      have h := (Work.FTS.StrongPersist.H6Pair6Aux.slotProd α 6 hsm hm6).1 b (by omega)
      refine h.congr (Filter.Eventually.of_forall fun p => ?_)
      simp only [hVdef, Work.Spaces.mixed_zero_right]
    · rw [if_neg ha0]
      have ha1 : 1 ≤ a := Nat.one_le_iff_ne_zero.mpr ha0
      have h := (Work.FTS.StrongPersist.H6Pair6Aux.slotProd α 6 hsm hm6).2 b a ha1 hab
      refine h.congr (Filter.Eventually.of_forall fun p => ?_)
      simp only [hVdef]
  have hbigW : MeasureTheory.Integrable (fun p : ℝ × ℝ =>
      (Work.Spaces.w p.1)^2 * (Real.sin (2*p.2)) ^ (-q)
        * (Work.Spaces.mixed (b+1) a f p.1 p.2)^2) Lprod := by
    rw [hqdef]
    by_cases ha0 : a = 0
    · subst ha0
      rw [if_pos rfl]
      have h := (Work.FTS.StrongPersist.H6Pair6Aux.slotProd α 7 hsm hm7).1 (b+1) (by omega)
      show MeasureTheory.Integrable (fun p : ℝ × ℝ =>
        (Work.Spaces.w p.1)^2 * (Real.sin (2*p.2)) ^ (-(Work.Spaces.eta))
          * (Work.Spaces.DzIter (b+1) f p.1 p.2)^2)
        ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
          (MeasureTheory.volume.restrict Work.Spaces.Iθ))
      exact h
    · rw [if_neg ha0]
      have ha1 : 1 ≤ a := Nat.one_le_iff_ne_zero.mpr ha0
      exact (Work.FTS.StrongPersist.H6Pair6Aux.slotProd α 7 hsm hm7).2 (b+1) a ha1 (by omega)
  have hσVint : MeasureTheory.Integrable (fun p : ℝ × ℝ =>
      (Work.Spaces.w p.1)^2 * σ p.2 * (V p.1 p.2)^2) Lprod :=
    slot_sigma_integrable (X := V) hσcont hσnn hqV hVc hbigV
  have hσWint : MeasureTheory.Integrable (fun p : ℝ × ℝ =>
      (Work.Spaces.w p.1)^2 * σ p.2 * (Work.Spaces.mixed (b+1) a f p.1 p.2)^2) Lprod :=
    slot_sigma_integrable (X := fun z θ => Work.Spaces.mixed (b+1) a f z θ)
      hσcont hσnn hqV hWc hbigW
  have hZop : ∀ z θ, z * Work.Spaces.pz V z θ = Work.Spaces.mixed (b+1) a f z θ := by
    intro z θ
    simp only [hVdef, Work.Spaces.pz, Work.Spaces.mixed, Work.Spaces.DzIter_succ,
      Work.Spaces.Dz]
  -- ## the three integrability inputs of `dzSelf2dW`
  have hF : MeasureTheory.Integrable (fun p : ℝ × ℝ =>
      (Work.Spaces.w p.1)^2 * |θw p.2| * (V p.1 p.2)^2) Lprod := by
    refine (hσVint.const_mul 2).mono' ?_ ?_
    · have he2 : (fun p : ℝ × ℝ => (Work.Spaces.w p.1)^2 * |θw p.2| * (V p.1 p.2)^2)
          = (fun p : ℝ × ℝ => (Work.Spaces.w p.1)^2) * (fun p : ℝ × ℝ => |θw p.2|)
            * (fun p : ℝ × ℝ => (V p.1 p.2)^2) := by
        funext p; rfl
      rw [he2]
      exact (hwae.mul hθwae).mul hVae2
    · have hpt : ∀ θ ∈ Set.Ioo (0:ℝ) (π/2), ∀ z ∈ Set.Ioi (0:ℝ),
          ‖(Work.Spaces.w z)^2 * |θw θ| * (V z θ)^2‖
            ≤ 2 * ((Work.Spaces.w z)^2 * σ θ * (V z θ)^2) := by
        intro θ hθ z hz
        have hσ0 : 0 ≤ σ θ := hσnn θ hθ
        have hθwa : |θw θ| ≤ 2 * σ θ := by
          rw [hθwdef]; exact thetaW_abs_le σ θ hσ0
        rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (mul_nonneg (sq_nonneg _)
          (abs_nonneg _)) (sq_nonneg _))]
        calc (Work.Spaces.w z)^2 * |θw θ| * (V z θ)^2
            ≤ (Work.Spaces.w z)^2 * (2 * σ θ) * (V z θ)^2 :=
              mul_le_mul_of_nonneg_right
                (mul_le_mul_of_nonneg_left hθwa (sq_nonneg _)) (sq_nonneg _)
          _ = 2 * ((Work.Spaces.w z)^2 * σ θ * (V z θ)^2) := by ring
      exact Work.FTS.StrongPersist.H6Pair6Aux.ae_prod_Ioo hpt
  have hD2 : MeasureTheory.Integrable (fun p : ℝ × ℝ =>
      (Work.Spaces.w p.1)^2 * |θw p.2| * (p.1 * Work.Spaces.pz V p.1 p.2)^2) Lprod := by
    have he0 : (fun p : ℝ × ℝ => (Work.Spaces.w p.1)^2 * |θw p.2|
          * (p.1 * Work.Spaces.pz V p.1 p.2)^2)
        = fun p : ℝ × ℝ => (Work.Spaces.w p.1)^2 * |θw p.2|
          * (Work.Spaces.mixed (b+1) a f p.1 p.2)^2 := by
      funext p; rw [hZop p.1 p.2]
    rw [he0]
    refine (hσWint.const_mul 2).mono' ?_ ?_
    · have he2 : (fun p : ℝ × ℝ => (Work.Spaces.w p.1)^2 * |θw p.2|
            * (Work.Spaces.mixed (b+1) a f p.1 p.2)^2)
          = (fun p : ℝ × ℝ => (Work.Spaces.w p.1)^2) * (fun p : ℝ × ℝ => |θw p.2|)
            * (fun p : ℝ × ℝ => (Work.Spaces.mixed (b+1) a f p.1 p.2)^2) := by
        funext p; rfl
      rw [he2]
      exact (hwae.mul hθwae).mul hWae2
    · have hpt : ∀ θ ∈ Set.Ioo (0:ℝ) (π/2), ∀ z ∈ Set.Ioi (0:ℝ),
          ‖(Work.Spaces.w z)^2 * |θw θ|
              * (Work.Spaces.mixed (b+1) a f z θ)^2‖
            ≤ 2 * ((Work.Spaces.w z)^2 * σ θ * (Work.Spaces.mixed (b+1) a f z θ)^2) := by
        intro θ hθ z hz
        have hσ0 : 0 ≤ σ θ := hσnn θ hθ
        have hθwa : |θw θ| ≤ 2 * σ θ := by
          rw [hθwdef]; exact thetaW_abs_le σ θ hσ0
        rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (mul_nonneg (sq_nonneg _)
          (abs_nonneg _)) (sq_nonneg _))]
        calc (Work.Spaces.w z)^2 * |θw θ| * (Work.Spaces.mixed (b+1) a f z θ)^2
            ≤ (Work.Spaces.w z)^2 * (2 * σ θ) * (Work.Spaces.mixed (b+1) a f z θ)^2 :=
              mul_le_mul_of_nonneg_right
                (mul_le_mul_of_nonneg_left hθwa (sq_nonneg _)) (sq_nonneg _)
          _ = 2 * ((Work.Spaces.w z)^2 * σ θ * (Work.Spaces.mixed (b+1) a f z θ)^2) := by ring
      exact Work.FTS.StrongPersist.H6Pair6Aux.ae_prod_Ioo hpt
  have hcross : MeasureTheory.Integrable (fun p : ℝ × ℝ =>
      (Work.Spaces.w p.1)^2 * θw p.2 * ψ p.1
        * ((p.1 * Work.Spaces.pz V p.1 p.2) * V p.1 p.2)) Lprod := by
    have hmaj : MeasureTheory.Integrable (fun p : ℝ × ℝ => A *
        ((Work.Spaces.w p.1)^2 * σ p.2 * (Work.Spaces.mixed (b+1) a f p.1 p.2)^2
         + (Work.Spaces.w p.1)^2 * σ p.2 * (V p.1 p.2)^2)) Lprod :=
      (hσWint.add hσVint).const_mul A
    refine hmaj.mono' ?_ ?_
    · have hZae : AEStronglyMeasurable
          (fun p : ℝ × ℝ => p.1 * Work.Spaces.pz V p.1 p.2) Lprod := by
        have he : (fun p : ℝ × ℝ => p.1 * Work.Spaces.pz V p.1 p.2)
            = fun p : ℝ × ℝ => Work.Spaces.mixed (b+1) a f p.1 p.2 := by
          funext p; exact hZop p.1 p.2
        rw [he]
        exact Work.Spaces.aesm_of_continuousOn_Qd _ hWc
      have he3 : (fun p : ℝ × ℝ => (Work.Spaces.w p.1)^2 * θw p.2 * ψ p.1
            * ((p.1 * Work.Spaces.pz V p.1 p.2) * V p.1 p.2))
          = (fun p : ℝ × ℝ => (Work.Spaces.w p.1)^2) * (fun p : ℝ × ℝ => θw p.2)
            * (fun p : ℝ × ℝ => ψ p.1)
            * ((fun p : ℝ × ℝ => p.1 * Work.Spaces.pz V p.1 p.2)
              * (fun p : ℝ × ℝ => V p.1 p.2)) := by
        funext p; rfl
      rw [he3]
      exact ((hwae.mul hθw2).mul hψae).mul
        (hZae.mul (Work.Spaces.aesm_of_continuousOn_Qd (Function.uncurry V) hVc))
    · have hpt : ∀ θ ∈ Set.Ioo (0:ℝ) (π/2), ∀ z ∈ Set.Ioi (0:ℝ),
          ‖(Work.Spaces.w z)^2 * θw θ * ψ z * ((z * Work.Spaces.pz V z θ) * V z θ)‖
            ≤ A * ((Work.Spaces.w z)^2 * σ θ * (Work.Spaces.mixed (b+1) a f z θ)^2
              + (Work.Spaces.w z)^2 * σ θ * (V z θ)^2) := by
        intro θ hθ z hz
        have hσ0 : 0 ≤ σ θ := hσnn θ hθ
        have hψa : |ψ z| ≤ A := hψA z hz
        have hw : 0 ≤ (Work.Spaces.w z)^2 := sq_nonneg _
        set Z : ℝ := Work.Spaces.mixed (b+1) a f z θ with hZdef
        have hZe : |z * Work.Spaces.pz V z θ| = |Z| := by rw [hZop z θ, hZdef]
        have habs : ‖(Work.Spaces.w z)^2 * θw θ * ψ z * ((z * Work.Spaces.pz V z θ) * V z θ)‖
            = (Work.Spaces.w z)^2 * |σ θ| * |Work.Construction.c2m θ| * |ψ z|
              * (|Z| * |V z θ|) := by
          have hθwu : θw θ = σ θ * Work.Construction.c2m θ := by rw [hθwdef]
          rw [Real.norm_eq_abs, hθwu]
          simp only [abs_mul, abs_of_nonneg hw, hZe]
          ring
        rw [habs]
        have hAM : 2 * (|Z| * |V z θ|) ≤ Z ^ 2 + (V z θ) ^ 2 := by
          nlinarith [sq_nonneg (|Z| - |V z θ|), sq_abs Z, sq_abs (V z θ)]
        have h1 : (Work.Spaces.w z)^2 * |σ θ| * |Work.Construction.c2m θ| * |ψ z|
            ≤ (Work.Spaces.w z)^2 * σ θ * 2 * A := by
          have hσabs : |σ θ| = σ θ := abs_of_nonneg hσ0
          rw [hσabs]
          calc (Work.Spaces.w z)^2 * σ θ * |Work.Construction.c2m θ| * |ψ z|
              ≤ (Work.Spaces.w z)^2 * σ θ * 2 * |ψ z| :=
                mul_le_mul_of_nonneg_right
                  (mul_le_mul_of_nonneg_left (abs_c2m_le_two θ) (by positivity))
                  (abs_nonneg _)
            _ ≤ (Work.Spaces.w z)^2 * σ θ * 2 * A :=
                mul_le_mul_of_nonneg_left hψa (by positivity)
        calc (Work.Spaces.w z)^2 * |σ θ| * |Work.Construction.c2m θ| * |ψ z|
              * (|Z| * |V z θ|)
            ≤ (Work.Spaces.w z)^2 * σ θ * 2 * A * (|Z| * |V z θ|) :=
              mul_le_mul_of_nonneg_right h1 (mul_nonneg (abs_nonneg _) (abs_nonneg _))
          _ = A * σ θ * ((Work.Spaces.w z)^2 * (2 * (|Z| * |V z θ|))) := by ring
          _ ≤ A * σ θ * ((Work.Spaces.w z)^2 * (Z ^ 2 + (V z θ) ^ 2)) :=
              mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hAM hw) (by positivity)
          _ = A * ((Work.Spaces.w z)^2 * σ θ * Z ^ 2
              + (Work.Spaces.w z)^2 * σ θ * (V z θ)^2) := by ring
      exact Work.FTS.StrongPersist.H6Pair6Aux.ae_prod_Ioo hpt
  -- ## the two-dimensional Hardy input
  have hibp := dzSelf2dW (θw := θw) (ψ := ψ) (V := V) (D := 3 * A + A)
    (by linarith) h1d hθwm hVslice hVae hF hD2 hcross
  -- ## the target integral in the `IBP` form
  have hgoal : (∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
        (Work.Spaces.w z) ^ 2 * σ θ * (Work.Construction.c2m θ * Work.Construction.L12 f z)
          * Work.Spaces.mixed (b + 1) a f z θ * Work.Spaces.mixed b a f z θ)
      = (∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
        (Work.Spaces.w z) ^ 2 * θw θ * ψ z * ((z * Work.Spaces.pz V z θ) * V z θ)) := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun z => integral_congr_ae
      (Filter.Eventually.of_forall fun θ => ?_))
    rw [hθwdef, hψdef, hVdef]
    simp only [Work.Spaces.pz, Work.Spaces.mixed, Work.Spaces.DzIter_succ, Work.Spaces.Dz]
    ring
  -- ## the RHS bound
  have hval : (∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
      (Work.Spaces.w z) ^ 2 * |θw θ| * (V z θ) ^ 2) ≤ 2 * Work.Spaces.HkSq α 6 f := by
    have hcap' : ∀ θ ∈ Set.Ioo (0:ℝ) (π/2), |θw θ| / 2
        ≤ (Real.sin (2*θ)) ^ (-(if a = 0 then Work.Spaces.eta else Work.Spaces.gam α)) := by
      intro θ hθ
      have hσ0 : 0 ≤ σ θ := hσnn θ hθ
      have hθwa : |θw θ| ≤ 2 * σ θ := by
        rw [hθwdef]; exact thetaW_abs_le σ θ hσ0
      linarith [hσcap θ hθ]
    have hnn' : ∀ θ ∈ Set.Ioo (0:ℝ) (π/2), 0 ≤ |θw θ| / 2 :=
      fun θ _ => by positivity
    have hkey : (∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
        (Work.Spaces.w z) ^ 2 * (|θw θ| / 2) * (V z θ) ^ 2)
        ≤ Work.Spaces.HkSq α 6 f := by
      by_cases ha0 : a = 0
      · subst ha0
        have hcap0 : ∀ θ ∈ Set.Ioo (0:ℝ) (π/2),
            |θw θ| / 2 ≤ (Real.sin (2*θ)) ^ (-(Work.Spaces.eta)) :=
          fun θ hθ => by simpa using hcap' θ hθ
        have h := (Work.FTS.StrongPersist.H6Pair6Aux.intSlotLeHkSq α hm6).1 b (by omega)
          (fun θ => |θw θ| / 2) hnn' hcap0
        simpa only [hVdef, Work.Spaces.mixed_zero_right] using h
      · have hcapg : ∀ θ ∈ Set.Ioo (0:ℝ) (π/2),
            |θw θ| / 2 ≤ (Real.sin (2*θ)) ^ (-(Work.Spaces.gam α)) := by
          intro θ hθ
          have h := hcap' θ hθ
          rwa [if_neg ha0] at h
        have ha1 : 1 ≤ a := Nat.one_le_iff_ne_zero.mpr ha0
        exact (Work.FTS.StrongPersist.H6Pair6Aux.intSlotLeHkSq α hm6).2 b a ha1 hab
          (fun θ => |θw θ| / 2) hnn' hcapg
    have hmain : (∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
        2 * ((Work.Spaces.w z) ^ 2 * (|θw θ| / 2) * (V z θ) ^ 2))
        = 2 * (∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
          (Work.Spaces.w z) ^ 2 * (|θw θ| / 2) * (V z θ) ^ 2) := by
      simp only [MeasureTheory.integral_const_mul]
    calc (∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
          (Work.Spaces.w z) ^ 2 * |θw θ| * (V z θ) ^ 2)
        = (∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
          2 * ((Work.Spaces.w z) ^ 2 * (|θw θ| / 2) * (V z θ) ^ 2)) := by
          refine integral_congr_ae (Filter.Eventually.of_forall fun z => integral_congr_ae
            (Filter.Eventually.of_forall fun θ => by ring))
      _ = 2 * (∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
          (Work.Spaces.w z) ^ 2 * (|θw θ| / 2) * (V z θ) ^ 2) := hmain
      _ ≤ 2 * Work.Spaces.HkSq α 6 f := by linarith [hkey]
  -- ## assembly
  have hpow : Xn ≤ (1 + Xn) ^ 4 := by
    have h1 : (1:ℝ) ≤ 1 + Xn := by linarith
    calc Xn ≤ 1 + Xn := by linarith
      _ = (1 + Xn) ^ 1 := by ring
      _ ≤ (1 + Xn) ^ 4 := pow_le_pow_right₀ h1 (by norm_num)
  calc |∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
        (Work.Spaces.w z) ^ 2 * σ θ * (Work.Construction.c2m θ * Work.Construction.L12 f z)
          * Work.Spaces.mixed (b + 1) a f z θ * Work.Spaces.mixed b a f z θ|
      = |∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
          (Work.Spaces.w z) ^ 2 * θw θ * ψ z * ((z * Work.Spaces.pz V z θ) * V z θ)| := by
        rw [hgoal]
    _ ≤ (3 * A + A) * (∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
          (Work.Spaces.w z) ^ 2 * |θw θ| * (V z θ) ^ 2) := hibp
    _ ≤ (3 * A + A) * (2 * Work.Spaces.HkSq α 6 f) :=
        mul_le_mul_of_nonneg_left hval (by linarith)
    _ = 8 * CL * Xn * Work.Spaces.HkSq α 6 f := by rw [hAdef]; ring
    _ ≤ 8 * CL * (1 + Xn) ^ 4 * (1 + Work.Spaces.HkSq α 6 f) := by
        have h8H : 0 ≤ 8 * CL * Work.Spaces.HkSq α 6 f := by positivity
        have h8P : 0 ≤ 8 * CL * (1 + Xn) ^ 4 := by positivity
        have h1 := mul_le_mul_of_nonneg_left hpow h8H
        have h2 := mul_le_mul_of_nonneg_left
          (by linarith : Work.Spaces.HkSq α 6 f ≤ 1 + Work.Spaces.HkSq α 6 f) h8P
        nlinarith [h1, h2]
    _ = 8 * CL * (1 + Work.FTS.Nonlin.Xn α f) ^ 4 * (1 + Work.Spaces.HkSq α 6 f) := by
        rw [hXndef]


end

end Work.FTS.StrongPersist.H6Pair6Aux.T5bAux
