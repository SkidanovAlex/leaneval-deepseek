import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.UniformLimitsDeriv
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.FTS_EllLimOK.ProducerH.BoxAux.Trace
import Submission.Work.FTS_EllLimOK.ProducerH.BoxAux.th2EgRate
import Submission.Work.FTS_EllLimOK.ProducerH.H2.Dev.slice_deriv_bound
import Submission.Work.FTS_EllLimOK.ProducerH.MixedJets.mixed_jets_le_Xn6
import Submission.Work.FTS_EllLimOK.ProducerH.SecondDeriv.second_theta_deriv_le_Xn6
import Submission.Work.FTS_EllLimOK.ProducerH.SecondDerivDz.second_theta_deriv_DzIter_le_Xn6
import Submission.Work.FTS_EllLimOK.ProducerH.slotBd_phiTil
import Submission.Work.FTS_EllLimOK.RulingELF
import Submission.Work.FTS_EllLimOK.SmallAssemblyH
import Submission.Work.GalerkinFix.RegQ.HkMem_mono_Q
import Submission.Work.R1G.DecayInZ_gA
import Submission.Work.Spaces.one_le_mul_w
import Submission.Work.Spaces.sin_two_rpow
import Submission.Work.Stability.mul_rpow_le

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS_EllLimOK.ProducerH.H2

open scoped Real Topology
open MeasureTheory Set Filter

set_option maxHeartbeats 1600000

theorem eg_limits {α Ce : ℝ} (hα : 0 < α) (hα4 : α ≤ 1 / 4)
    {E : Work.FTS.Galerkin.Fn →ₗ[ℝ] Work.FTS.Galerkin.Fn}
    (hE : Work.FTS_EllLimOK.ProducerH.H2.Ctx α Ce E) {a b : ℝ} (ha : 0 < a) (hab : a ≤ b)
    {K β : ℝ} (hK : 0 < K) (hβ : 0 < β)
    (hmod : ∀ g : Work.FTS.Galerkin.Fn, Work.FTS.ClassC.ClassC α g → ∀ z ∈ Set.Icc a b,
      ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
        |deriv (deriv (fun θ' => (E g) z θ')) θ|
          ≤ K * Work.FTS.StrongGlobal.Xn6 α g * (min θ (Real.pi / 2 - θ)) ^ β) :
    ∃ C : ℝ, 0 < C ∧ ∀ g : Work.FTS.Galerkin.Fn, Work.FTS.ClassC.ClassC α g →
      ∃ L0 N0 L1 N1 : ℝ → ℝ,
        (∀ z ∈ Set.Icc a b, Filter.Tendsto (fun θ => Work.Spaces.pth (E g) z θ)
          (nhdsWithin 0 (Set.Ioi 0)) (nhds (L0 z))) ∧
        (∀ z ∈ Set.Icc a b, ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
          |Work.Spaces.pth (E g) z θ - L0 z| ≤ C * Work.FTS.StrongGlobal.Xn6 α g * θ) ∧
        (∀ z ∈ Set.Icc a b, Filter.Tendsto (fun θ => Work.Spaces.pz (Work.Spaces.pth (E g)) z θ)
          (nhdsWithin 0 (Set.Ioi 0)) (nhds (N0 z))) ∧
        (∀ z ∈ Set.Icc a b, ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
          |Work.Spaces.pz (Work.Spaces.pth (E g)) z θ - N0 z| ≤ C * Work.FTS.StrongGlobal.Xn6 α g * θ) ∧
        (∀ z ∈ Set.Icc a b, Filter.Tendsto (fun θ => Work.Spaces.pth (E g) z θ)
          (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds (L1 z))) ∧
        (∀ z ∈ Set.Icc a b, ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
          |Work.Spaces.pth (E g) z θ - L1 z| ≤ C * Work.FTS.StrongGlobal.Xn6 α g * (Real.pi / 2 - θ)) ∧
        (∀ z ∈ Set.Icc a b, Filter.Tendsto (fun θ => Work.Spaces.pz (Work.Spaces.pth (E g)) z θ)
          (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds (N1 z))) ∧
        (∀ z ∈ Set.Icc a b, ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
          |Work.Spaces.pz (Work.Spaces.pth (E g)) z θ - N1 z|
            ≤ C * Work.FTS.StrongGlobal.Xn6 α g * (Real.pi / 2 - θ)) ∧
        ContinuousOn L0 (Set.Icc a b) ∧ ContinuousOn N0 (Set.Icc a b) ∧
        ContinuousOn L1 (Set.Icc a b) ∧ ContinuousOn N1 (Set.Icc a b) ∧
        (∀ z ∈ Set.Icc a b, HasDerivWithinAt L0 (N0 z) (Set.Icc a b) z) ∧
        (∀ z ∈ Set.Icc a b, HasDerivWithinAt L1 (N1 z) (Set.Icc a b) z) := by
  -- ## the two uniform angular bounds of the second derivative on the enlarged box
  obtain ⟨K1, hK1pos, hK1⟩ :=
    Work.FTS_EllLimOK.ProducerH.SecondDeriv.second_theta_deriv_le_Xn6
      (α := α) (Ce := Ce) hα hα4 hE (a := a / 2) (b := b + 1)
      (by linarith) (by linarith)
  obtain ⟨K2, hK2pos, hK2⟩ :=
    Work.FTS_EllLimOK.ProducerH.SecondDerivDz.second_theta_deriv_DzIter_le_Xn6
      (α := α) (Ce := Ce) hα hα4 hE 1 (by norm_num)
      (a₀ := a / 2) (b₀ := b + 1) (by linarith) (by linarith)
  -- ## the (universal in `g`) constant
  refine ⟨max K1 (K2 / (a / 2)) + 1, by positivity, ?_⟩
  have hK1le : K1 ≤ max K1 (K2 / (a / 2)) + 1 := by
    have h := le_max_left K1 (K2 / (a / 2)); linarith
  have hK2le : K2 / (a / 2) ≤ max K1 (K2 / (a / 2)) + 1 := by
    have h := le_max_right K1 (K2 / (a / 2)); linarith
  intro g hg
  -- ## elementary facts about the box
  have hApos : 0 < a / 2 := by linarith
  have hAB : a / 2 < b + 1 := by linarith
  have hX0 : 0 ≤ Work.FTS.StrongGlobal.Xn6 α g := Xn6_nonneg α g
  have hsm : Work.FTS.EllipticEst.SmoothOpen (E g) := (hE g hg).2.2.smooth
  have hAin : ∀ z ∈ Set.Icc a b, z ∈ Set.Icc (a / 2) (b + 1) := by
    intro z hz
    exact ⟨by linarith [hz.1], by linarith [hz.2]⟩
  -- ## the two limit families `∂_θ(E g)` and `∂_z∂_θ(E g)`
  obtain ⟨L0, L1, hL0t, hL0r, hL1t, hL1r, hL0c, hL1c⟩ :=
    eg_limit_family (F := fun θ z => Work.Spaces.pth (E g) z θ)
      (A := a / 2) (B := b + 1) (M := K1 * Work.FTS.StrongGlobal.Xn6 α g)
      hAB (by positivity)
      (fun z hz => ((hsm.pth).curry_θ (by linarith [hz.1])).of_le (by norm_num))
      (fun z hz θ hθ => by
        have h := hK1 g hg z hz θ hθ
        simpa only [Work.Spaces.pth] using h)
      (fun θ hθ => ((hsm.pth).curry_z hθ).continuousOn.mono
        (fun z hz => show (0 : ℝ) < z from by linarith [hz.1]))
  obtain ⟨N0, N1, hN0t, hN0r, hN1t, hN1r, hN0c, hN1c⟩ :=
    eg_limit_family (F := fun θ z => Work.Spaces.pz (Work.Spaces.pth (E g)) z θ)
      (A := a / 2) (B := b + 1) (M := (K2 * Work.FTS.StrongGlobal.Xn6 α g) / (a / 2))
      hAB (by positivity)
      (fun z hz => (((hsm.pth).pz).curry_θ (by linarith [hz.1])).of_le (by norm_num))
      (fun z hz θ hθ =>
        deriv_pz_pth_bound hsm hApos (by positivity)
          (fun z' hz' θ' hθ' => hK2 g hg z' hz' θ' hθ') z hz θ hθ)
      (fun θ hθ => (((hsm.pth).pz).curry_z hθ).continuousOn.mono
        (fun z hz => show (0 : ℝ) < z from by linarith [hz.1]))
  -- ## uniform convergence of `∂_z∂_θ(E g)` at both ends
  have hunif0 : TendstoUniformlyOn (fun n z => Work.Spaces.pz (Work.Spaces.pth (E g)) z n) N0
      (nhdsWithin 0 (Set.Ioi 0)) (Set.Ioo (a / 2) (b + 1)) := by
    rw [Metric.tendstoUniformlyOn_iff]
    intro ε hε
    filter_upwards
      [nhdsWithin_le_nhds (isOpen_Iio.mem_nhds (show (0 : ℝ)
          < ε / ((K2 * Work.FTS.StrongGlobal.Xn6 α g) / (a / 2) + 1) by positivity)),
       Ioo_mem_nhdsGT (show (0 : ℝ) < Real.pi / 2 by linarith [Real.pi_pos])]
      with n hn hnm
    intro z hz
    have hb := hN0r z ⟨le_of_lt hz.1, le_of_lt hz.2⟩ n hnm
    calc dist (N0 z) (Work.Spaces.pz (Work.Spaces.pth (E g)) z n)
        = |N0 z - Work.Spaces.pz (Work.Spaces.pth (E g)) z n| := Real.dist_eq _ _
      _ = |Work.Spaces.pz (Work.Spaces.pth (E g)) z n - N0 z| := abs_sub_comm _ _
      _ ≤ ((K2 * Work.FTS.StrongGlobal.Xn6 α g) / (a / 2)) * n := hb
      _ ≤ (((K2 * Work.FTS.StrongGlobal.Xn6 α g) / (a / 2)) + 1) * n := by
          have h1 : (0 : ℝ) ≤ n := le_of_lt hnm.1
          nlinarith
      _ < (((K2 * Work.FTS.StrongGlobal.Xn6 α g) / (a / 2)) + 1)
            * (ε / (((K2 * Work.FTS.StrongGlobal.Xn6 α g) / (a / 2)) + 1)) :=
          mul_lt_mul_of_pos_left hn (by positivity)
      _ = ε := by field_simp
  have hunif1 : TendstoUniformlyOn (fun n z => Work.Spaces.pz (Work.Spaces.pth (E g)) z n) N1
      (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (Set.Ioo (a / 2) (b + 1)) := by
    rw [Metric.tendstoUniformlyOn_iff]
    intro ε hε
    filter_upwards
      [nhdsWithin_le_nhds (isOpen_Ioi.mem_nhds (show (Real.pi / 2
          - ε / ((K2 * Work.FTS.StrongGlobal.Xn6 α g) / (a / 2) + 1)) < Real.pi / 2 from by
            have h1 : 0 < ε / ((K2 * Work.FTS.StrongGlobal.Xn6 α g) / (a / 2) + 1) := by positivity
            linarith)),
       Ioo_mem_nhdsLT (show (0 : ℝ) < Real.pi / 2 by linarith [Real.pi_pos])]
      with n hn hnm
    intro z hz
    have hb := hN1r z ⟨le_of_lt hz.1, le_of_lt hz.2⟩ n hnm
    have hn' : Real.pi / 2 - ε / ((K2 * Work.FTS.StrongGlobal.Xn6 α g) / (a / 2) + 1) < n := hn
    have hlt : Real.pi / 2 - n < ε / ((K2 * Work.FTS.StrongGlobal.Xn6 α g) / (a / 2) + 1) := by
      linarith [hn']
    have hnn : 0 ≤ Real.pi / 2 - n := by linarith [hnm.2]
    calc dist (N1 z) (Work.Spaces.pz (Work.Spaces.pth (E g)) z n)
        = |N1 z - Work.Spaces.pz (Work.Spaces.pth (E g)) z n| := Real.dist_eq _ _
      _ = |Work.Spaces.pz (Work.Spaces.pth (E g)) z n - N1 z| := abs_sub_comm _ _
      _ ≤ ((K2 * Work.FTS.StrongGlobal.Xn6 α g) / (a / 2)) * (Real.pi / 2 - n) := hb
      _ ≤ (((K2 * Work.FTS.StrongGlobal.Xn6 α g) / (a / 2)) + 1) * (Real.pi / 2 - n) := by
          have h1 : (0 : ℝ) ≤ (K2 * Work.FTS.StrongGlobal.Xn6 α g) / (a / 2) := by positivity
          nlinarith
      _ < (((K2 * Work.FTS.StrongGlobal.Xn6 α g) / (a / 2)) + 1)
            * (ε / (((K2 * Work.FTS.StrongGlobal.Xn6 α g) / (a / 2)) + 1)) :=
          mul_lt_mul_of_pos_left hlt (by positivity)
      _ = ε := by field_simp
  -- ## `L0` and `L1` are differentiable in `z` on the interior of the box
  have hub0 : ∀ x ∈ Set.Ioo (a / 2) (b + 1), HasDerivAt L0 (N0 x) x := by
    intro x hx
    refine hasDerivAt_of_tendstoLocallyUniformlyOn (l := nhdsWithin 0 (Set.Ioi 0))
      (f := fun n z => Work.Spaces.pth (E g) z n) (g := L0)
      (f' := fun n z => Work.Spaces.pz (Work.Spaces.pth (E g)) z n) (g' := N0)
      isOpen_Ioo ?_ ?_ ?_ hx
    · exact hunif0.tendstoLocallyUniformlyOn
    · filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < Real.pi / 2 by linarith [Real.pi_pos])]
        with n hn y hy
      exact (hsm.pth).hasDerivAt_slice hn (by linarith [hy.1])
    · intro y hy
      exact hL0t y ⟨le_of_lt hy.1, le_of_lt hy.2⟩
  have hub1 : ∀ x ∈ Set.Ioo (a / 2) (b + 1), HasDerivAt L1 (N1 x) x := by
    intro x hx
    refine hasDerivAt_of_tendstoLocallyUniformlyOn
      (l := nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2)))
      (f := fun n z => Work.Spaces.pth (E g) z n) (g := L1)
      (f' := fun n z => Work.Spaces.pz (Work.Spaces.pth (E g)) z n) (g' := N1)
      isOpen_Ioo ?_ ?_ ?_ hx
    · exact hunif1.tendstoLocallyUniformlyOn
    · filter_upwards [Ioo_mem_nhdsLT (show (0 : ℝ) < Real.pi / 2 by linarith [Real.pi_pos])]
        with n hn y hy
      exact (hsm.pth).hasDerivAt_slice hn (by linarith [hy.1])
    · intro y hy
      exact hL1t y ⟨le_of_lt hy.1, le_of_lt hy.2⟩
  -- ## the rate constants
  have hrate_L0 : ∀ z ∈ Set.Icc (a / 2) (b + 1), ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      |Work.Spaces.pth (E g) z θ - L0 z|
        ≤ (max K1 (K2 / (a / 2)) + 1) * Work.FTS.StrongGlobal.Xn6 α g * θ := by
    intro z hz θ hθ
    refine le_trans (hL0r z hz θ hθ) ?_
    have hθ0 : 0 ≤ θ := le_of_lt hθ.1
    have h := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hK1le hX0) hθ0
    calc (K1 * Work.FTS.StrongGlobal.Xn6 α g) * θ
        ≤ ((max K1 (K2 / (a / 2)) + 1) * Work.FTS.StrongGlobal.Xn6 α g) * θ := h
      _ = (max K1 (K2 / (a / 2)) + 1) * Work.FTS.StrongGlobal.Xn6 α g * θ := by ring
  have hrate_N0 : ∀ z ∈ Set.Icc (a / 2) (b + 1), ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      |Work.Spaces.pz (Work.Spaces.pth (E g)) z θ - N0 z|
        ≤ (max K1 (K2 / (a / 2)) + 1) * Work.FTS.StrongGlobal.Xn6 α g * θ := by
    intro z hz θ hθ
    refine le_trans (hN0r z hz θ hθ) ?_
    have hθ0 : 0 ≤ θ := le_of_lt hθ.1
    have heq : (K2 * Work.FTS.StrongGlobal.Xn6 α g) / (a / 2)
        = (K2 / (a / 2)) * Work.FTS.StrongGlobal.Xn6 α g := by ring
    rw [heq]
    have h := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hK2le hX0) hθ0
    calc (K2 / (a / 2)) * Work.FTS.StrongGlobal.Xn6 α g * θ
        ≤ ((max K1 (K2 / (a / 2)) + 1) * Work.FTS.StrongGlobal.Xn6 α g) * θ := h
      _ = (max K1 (K2 / (a / 2)) + 1) * Work.FTS.StrongGlobal.Xn6 α g * θ := by ring
  have hrate_L1 : ∀ z ∈ Set.Icc (a / 2) (b + 1), ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      |Work.Spaces.pth (E g) z θ - L1 z|
        ≤ (max K1 (K2 / (a / 2)) + 1) * Work.FTS.StrongGlobal.Xn6 α g
            * (Real.pi / 2 - θ) := by
    intro z hz θ hθ
    refine le_trans (hL1r z hz θ hθ) ?_
    have hθ0 : 0 ≤ Real.pi / 2 - θ := by linarith [hθ.2]
    have h := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hK1le hX0) hθ0
    calc (K1 * Work.FTS.StrongGlobal.Xn6 α g) * (Real.pi / 2 - θ)
        ≤ ((max K1 (K2 / (a / 2)) + 1) * Work.FTS.StrongGlobal.Xn6 α g)
            * (Real.pi / 2 - θ) := h
      _ = (max K1 (K2 / (a / 2)) + 1) * Work.FTS.StrongGlobal.Xn6 α g
            * (Real.pi / 2 - θ) := by ring
  have hrate_N1 : ∀ z ∈ Set.Icc (a / 2) (b + 1), ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      |Work.Spaces.pz (Work.Spaces.pth (E g)) z θ - N1 z|
        ≤ (max K1 (K2 / (a / 2)) + 1) * Work.FTS.StrongGlobal.Xn6 α g
            * (Real.pi / 2 - θ) := by
    intro z hz θ hθ
    refine le_trans (hN1r z hz θ hθ) ?_
    have hθ0 : 0 ≤ Real.pi / 2 - θ := by linarith [hθ.2]
    have heq : (K2 * Work.FTS.StrongGlobal.Xn6 α g) / (a / 2)
        = (K2 / (a / 2)) * Work.FTS.StrongGlobal.Xn6 α g := by ring
    rw [heq]
    have h := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hK2le hX0) hθ0
    calc (K2 / (a / 2)) * Work.FTS.StrongGlobal.Xn6 α g * (Real.pi / 2 - θ)
        ≤ ((max K1 (K2 / (a / 2)) + 1) * Work.FTS.StrongGlobal.Xn6 α g)
            * (Real.pi / 2 - θ) := h
      _ = (max K1 (K2 / (a / 2)) + 1) * Work.FTS.StrongGlobal.Xn6 α g
            * (Real.pi / 2 - θ) := by ring
  -- ## assembly
  refine ⟨L0, N0, L1, N1, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro z hz
    exact hL0t z (hAin z hz)
  · intro z hz θ hθ
    exact hrate_L0 z (hAin z hz) θ hθ
  · intro z hz
    exact hN0t z (hAin z hz)
  · intro z hz θ hθ
    exact hrate_N0 z (hAin z hz) θ hθ
  · intro z hz
    exact hL1t z (hAin z hz)
  · intro z hz θ hθ
    exact hrate_L1 z (hAin z hz) θ hθ
  · intro z hz
    exact hN1t z (hAin z hz)
  · intro z hz θ hθ
    exact hrate_N1 z (hAin z hz) θ hθ
  · exact hL0c.mono (fun z hz => hAin z hz)
  · exact hN0c.mono (fun z hz => hAin z hz)
  · exact hL1c.mono (fun z hz => hAin z hz)
  · exact hN1c.mono (fun z hz => hAin z hz)
  · intro z hz
    exact (hub0 z ⟨by linarith [hz.1], by linarith [hz.2]⟩).hasDerivWithinAt
  · intro z hz
    exact (hub1 z ⟨by linarith [hz.1], by linarith [hz.2]⟩).hasDerivWithinAt

end Work.FTS_EllLimOK.ProducerH.H2
