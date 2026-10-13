import Mathlib.Algebra.Order.Ring.Star
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.T6CoefAux.mismatchAux
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.T6CoefAux.slotAmgm
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.T6CoefAux.slotArith
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.T6CoefAux.cs_sqrt_int
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.T6CoefAux.sigmaDivisibility
import Submission.Work.FTS.StrongPersist.N6.PwOpen6
import Submission.Work.FTS.OpenPkg.Basic
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.zProdIntLe
import Submission.Work.FTS.StrongPersist.N6Trans.Hon.HkProdOpen
import Submission.Work.FTS.TransportS.ip4SlotDomFixed
import Submission.Work.FTS.TransportS.SlotT2.supThetaIntOpen
import Submission.Work.FTS.TransportS.T2SupB2.mixed_slice_z_uniform
import Submission.Work.H2.T1Q.SliceSupOpen
import Submission.Work.Spaces.integrable_prod_of_iterated
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.leafGamPureZ_b1fiveAux
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.T6CoefAux.MismatchHardAux
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.T6CoefAux.MismatchHardB5
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.T6CoefAux.MismatchHardBLe4

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The mismatch coefficient estimate: the case `a = a₁ = 1`, `b₁ = 0`

With these indices the pairing is `∫∫ w²σ^{-γ}·(D_θA)·(D_z^b f)·(D_z^bD_θ f)`, `b ≤ 5`.

* `b ≤ 4`: complete (`mh_hard_b_le_four` in `MismatchHardBLe4`), via `N6.PwAny6` +
  `mixed_slot_le` + `slotAmgm`.
* `b = 5`: complete (`mh_hard_b5` in `MismatchHardB5`), via the σ-divisibility identity
  `leafGam α·D_θA = w²σ^{1-γ}∂_θA`, the radial-uniform slice bound for the `(0,1)`-slot of `A`,
  the slice Agmon bound for `D_z⁵f` (`mh_agmon`), the slice Cauchy–Schwarz at the bounded
  weight `σ^{2-γ}` (`mh_slice_bound`) and the two `z`-marginals of `D_z⁵f`
  (`mh_pureZ_eta_slot_l2`, `T6Coef.zProdIntLe`).
-/
namespace Work.FTS.StrongPersist.H6Pair6Aux.T6CoefAux

open scoped Real Topology
open MeasureTheory Set Filter

noncomputable section

set_option maxHeartbeats 1600000

theorem mismatchCaseHard : ∃ C : ℝ, 0 < C ∧ ∀ α ∈ Set.Ioc (0 : ℝ) 1,
    ∀ (A f : ℝ → ℝ → ℝ) (K0 K4 : ℝ) (a b a₁ b₁ : ℕ),
      Work.FTS.EllipticEst.SmoothOpen A → Work.Spaces.HkMem α 4 A →
      Work.Spaces.HkMem α 6 A →
      (∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 → |A z θ| ≤ K0) →
      Work.FTS.Nonlin.Xn α A ≤ K4 →
      Work.FTS.EllipticEst.SmoothOpen f → Work.Spaces.HkMem α 7 f →
      Work.Spaces.VanishTheta f →
      1 ≤ a₁ → a₁ + b₁ ≤ 2 → a₁ ≤ a → b₁ ≤ b → a + b ≤ 6 →
      a = a₁ → a₁ = 1 → b₁ = 0 →
      MeasureTheory.Integrable (fun p : ℝ × ℝ => Work.FTS.TransportS.leafGam α p.1 p.2
          * Work.Spaces.mixed b₁ a₁ A p.1 p.2
          * Work.Spaces.mixed (b - b₁) (a - a₁) f p.1 p.2
          * Work.Spaces.mixed b a f p.1 p.2)
          ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
            (MeasureTheory.volume.restrict Work.Spaces.Iθ)) ∧
      |∫ p, Work.FTS.TransportS.leafGam α p.1 p.2
            * Work.Spaces.mixed b₁ a₁ A p.1 p.2
            * Work.Spaces.mixed (b - b₁) (a - a₁) f p.1 p.2
            * Work.Spaces.mixed b a f p.1 p.2
          ∂((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
            (MeasureTheory.volume.restrict Work.Spaces.Iθ))|
        ≤ C * α ^ (-(3 : ℝ)) * ((1 + K0 + K4) * (1 + Work.Spaces.HkSq α 6 f)) := by
  obtain ⟨C, hCpos, hC⟩ := mh_hard_b_le_four
  obtain ⟨C', hC'pos, hC'⟩ := mh_hard_b5
  refine ⟨max C C', lt_max_of_lt_left hCpos, ?_⟩
  intro α hα A f K0 K4 a b a₁ b₁ hAsm hA4 hA6 hAbdd hXn hfsm hf7 hfv
    ha₁ hab₁ ha₁a hb₁b hab hae ha₁e hb₁e
  subst hae
  subst ha₁e
  subst hb₁e
  simp only [Nat.sub_zero, Nat.sub_self] at *
  have hf6 : Work.Spaces.HkMem α 6 f :=
    Work.FTS.OpenPkg.HkMem_mono_open (k := 7) hfsm 6 (by norm_num) hf7
  have hK0 : 0 ≤ K0 := by
    have h := hAbdd 1 (Real.pi / 4) one_pos (by linarith [Real.pi_pos])
      (by linarith [Real.pi_pos])
    linarith [abs_nonneg (A 1 (Real.pi / 4))]
  have hK4 : 0 ≤ K4 := le_trans (Work.Spaces.HkNorm_nonneg α 4 A) hXn
  have hHf6 : 0 ≤ Work.Spaces.HkSq α 6 f := Work.Spaces.HkSq_nonneg α 6 f
  by_cases hb : b ≤ 4
  · have h := hC α hα A f K0 K4 b hAsm hA4 hAbdd hXn hfsm hf6 hb
    have hle : C * α ^ (-(3 : ℝ)) * ((1 + K0 + K4) * (1 + Work.Spaces.HkSq α 6 f))
        ≤ max C C' * α ^ (-(3 : ℝ)) * ((1 + K0 + K4) * (1 + Work.Spaces.HkSq α 6 f)) := by
      have h1 : C * (α ^ (-(3 : ℝ)) * ((1 + K0 + K4) * (1 + Work.Spaces.HkSq α 6 f)))
          ≤ max C C' * (α ^ (-(3 : ℝ)) * ((1 + K0 + K4) * (1 + Work.Spaces.HkSq α 6 f))) :=
        mul_le_mul_of_nonneg_right (le_max_left C C')
          (mul_nonneg (Real.rpow_nonneg hα.1.le (-(3 : ℝ)))
            (mul_nonneg (by linarith [hK0, hK4]) (by linarith [hHf6])))
      rw [mul_assoc C, mul_assoc (max C C')]
      exact h1
    exact ⟨by simpa only [Work.FTS.TransportS.leafGam, pm] using h.1,
      le_trans (by simpa only [Work.FTS.TransportS.leafGam, pm] using h.2) hle⟩
  · have hb5 : b = 5 := by omega
    subst hb5
    have h := hC' α hα A f K0 K4 hAsm hA4 hA6 hAbdd hXn hfsm hf6
    have hle : C' * α ^ (-(3 : ℝ)) * ((1 + K0 + K4) * (1 + Work.Spaces.HkSq α 6 f))
        ≤ max C C' * α ^ (-(3 : ℝ)) * ((1 + K0 + K4) * (1 + Work.Spaces.HkSq α 6 f)) := by
      have h1 : C' * (α ^ (-(3 : ℝ)) * ((1 + K0 + K4) * (1 + Work.Spaces.HkSq α 6 f)))
          ≤ max C C' * (α ^ (-(3 : ℝ)) * ((1 + K0 + K4) * (1 + Work.Spaces.HkSq α 6 f))) :=
        mul_le_mul_of_nonneg_right (le_max_right C C')
          (mul_nonneg (Real.rpow_nonneg hα.1.le (-(3 : ℝ)))
            (mul_nonneg (by linarith [hK0, hK4]) (by linarith [hHf6])))
      rw [mul_assoc C', mul_assoc (max C C')]
      exact h1
    exact ⟨by simpa only [Work.FTS.TransportS.leafGam, pm] using h.1,
      le_trans (by simpa only [Work.FTS.TransportS.leafGam, pm] using h.2) hle⟩
end

end Work.FTS.StrongPersist.H6Pair6Aux.T6CoefAux
