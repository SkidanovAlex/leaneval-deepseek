import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.FTS.OpenPkg.ProdOpen.leibniz_open_Dz
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.L12Sup6
import Submission.Work.FTS.StrongPersist.N6.PwOpen6
import Submission.Work.FTS.StrongPersist.StarPkg6OfCore
import Submission.Work.FTS.TransportS.sup_dz_le_hk
import Submission.Work.FTS_EllLimOK.Decay.DecayTools
import Submission.Work.FTS_StreamBdry.Inputs.theta_part_alt_l12fstar
import Submission.Work.GalerkinFix.RegQ.HkMem_mono_Q
import Submission.Work.H2.WPQ.m_term_le_smoothQuad
import Submission.Work.Spaces.HkSq_terms
import Submission.Work.Spaces.sq_mul_div_rpow

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.E4R3.Nblock6.Tools
namespace PtB

open Function Set

noncomputable section

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1600000
/-! ## The Leibniz expansions of the two slot families -/

/-- `D_z^i (D_z f) = D_z^{i+1} f` (formal; no smoothness needed). -/
theorem DzIter_Dz (n : ℕ) (g : ℝ → ℝ → ℝ) :
    Work.Spaces.DzIter n (Work.Spaces.Dz g) = Work.Spaces.DzIter (n + 1) g := by
  induction n with
  | zero => rfl
  | succ n ih =>
      show Work.Spaces.Dz (Work.Spaces.DzIter n (Work.Spaces.Dz g))
        = Work.Spaces.Dz (Work.Spaces.DzIter (n + 1) g)
      rw [ih]

/-- `D_z^j D_θ^i (D_z f) = D_z^{j+1} D_θ^i f` on the open quadrant. -/
theorem mixed_Dz_shift {f : ℝ → ℝ → ℝ} (hF : Work.FTS.EllipticEst.SmoothOpen f)
    (n k : ℕ) {z θ : ℝ} (hz : 0 < z) (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    Work.Spaces.mixed n k (Work.Spaces.Dz f) z θ = Work.Spaces.mixed (n + 1) k f z θ := by
  have hfi := (Work.FTS.EllipticEst.smoothOpen_iff_forall f).mp hF
  have h1 := Work.FTS.EllipticEst.ThetaU.OpenSliceAux.DthIter_DzIter_eqOn_of_isOpen
    Work.FTS.EllipticEst.isOpen_Q0 hfi 1 k
  have h2 := Work.FTS.H2.DzIter_congr_of_isOpen Work.FTS.EllipticEst.isOpen_Q0 h1 n
  have hp : (z, θ) ∈ Work.FTS.EllipticEst.Q0 :=
    Work.FTS.EllipticEst.mem_Q0.mpr ⟨hz, hθ.1, hθ.2⟩
  have h3 := h2 hp
  have h4 : Work.Spaces.DzIter n (Work.Spaces.mixed 1 k f) z θ
      = Work.Spaces.mixed (n + 1) k f z θ := by
    show Work.Spaces.DzIter n (Work.Spaces.DzIter 1 (Work.Spaces.DthIter k f)) z θ
      = Work.Spaces.DzIter (n + 1) (Work.Spaces.DthIter k f) z θ
    rw [Work.Spaces.DzIter_add_right n 1 (Work.Spaces.DthIter k f)]
  exact h3.trans h4

/-! ## The two per-slot bounds -/

/-- **The pure `D_z`-slots.**  Each of the seven `D_z`-slots of `HkIntegrand α 6 (A·D_z f)` is
dominated by the majorant. -/
theorem zslot_le {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) {A f : ℝ → ℝ → ℝ} {MA KA CPw : ℝ}
    (hAO : Work.FTS.EllipticEst.SmoothOpen A) (hfO : Work.FTS.EllipticEst.SmoothOpen f)
    (hMA : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 → |A z θ| ≤ MA)
    (hPwA : SupPw α CPw A) (hPwf : SupPw α CPw f) (hCPw : 0 < CPw) :
    ∀ m : ℕ, m ≤ 6 → ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      (Work.Spaces.DzIter m (fun z θ => A z θ * Work.Spaces.Dz f z θ) z θ * Hv z θ) ^ 2
        ≤ 10 ^ 11 * max CPw 1 * Maj α A f MA KA z θ := by
  intro m hm z θ hz hθ0 hθ1
  have hθ : θ ∈ Set.Ioo 0 (Real.pi / 2) := ⟨hθ0, hθ1⟩
  have hMnn : 0 ≤ Maj α A f MA KA z θ := Maj_nonneg hα A f MA KA z θ
  have hCMnn : 0 ≤ max CPw 1 * Maj α A f MA KA z θ :=
    mul_nonneg (le_trans hCPw.le (le_max_left _ _)) hMnn
  have hleib := Work.FTS.OpenPkg.ProdOpen.leibniz_open_Dz m A (Work.Spaces.Dz f)
    hAO hfO.Dz z θ hz hθ0 hθ1
  have hsum : Work.Spaces.DzIter m (fun z θ => A z θ * Work.Spaces.Dz f z θ) z θ * Hv z θ
      = ∑ b ∈ Finset.range (m + 1),
          ((m.choose b : ℝ)
            * (Work.Spaces.DzIter b A z θ * Work.Spaces.DzIter (m - b + 1) f z θ
              * Hv z θ)) := by
    rw [hleib, Finset.sum_mul]
    refine Finset.sum_congr rfl (fun b hb => ?_)
    rw [DzIter_Dz (m - b) f]
    ring
  have hcard : (((Finset.range (m + 1)).card : ℕ) : ℝ) = (m : ℝ) + 1 := by
    rw [Finset.card_range]; push_cast; ring
  have hterm : ∀ b ∈ Finset.range (m + 1),
      ((m.choose b : ℝ)
        * (Work.Spaces.DzIter b A z θ * Work.Spaces.DzIter (m - b + 1) f z θ * Hv z θ)) ^ 2
        ≤ 4096 * (max CPw 1 * Maj α A f MA KA z θ) := by
    intro b hb
    have hbm : b ≤ m := Nat.lt_succ_iff.mp (Finset.mem_range.mp hb)
    have hcb : (m.choose b : ℝ) ^ 2 ≤ 4096 :=
      Work.FTS.StrongPersist.N6.binom_sq_le_4096 m b hbm hm
    have hcore : (Work.Spaces.DzIter b A z θ * Work.Spaces.DzIter (m - b + 1) f z θ
        * Hv z θ) ^ 2 ≤ max CPw 1 * Maj α A f MA KA z θ := by
      rcases Nat.eq_zero_or_pos b with hb0 | hbpos
      · subst hb0
        have hAz : (A z θ) ^ 2 ≤ MA ^ 2 := by
          have h0 : 0 ≤ MA := le_trans (abs_nonneg _)
            (hMA 1 1 (by norm_num) (by norm_num) (by linarith [Real.pi_gt_three]))
          rw [← sq_abs]
          exact pow_le_pow_left₀ (abs_nonneg _) (hMA z θ hz hθ0 hθ1) 2
        have hY7 : (Work.Spaces.DzIter (m - 0 + 1) f z θ * Hv z θ) ^ 2
            ≤ Work.Spaces.HkIntegrand α 7 f z θ :=
          Work.Spaces.sq_le_HkIntegrand_z α 7 f z θ (m - 0 + 1) (by omega)
        exact close_MA (W := Hv z θ) hα hCPw hAz hY7
      · have hb1 : 1 ≤ b := hbpos
        by_cases hcase : m - b + 1 ≤ 4
        · have hX : (Work.Spaces.DzIter b A z θ * Hv z θ) ^ 2
              ≤ Work.Spaces.HkIntegrand α 6 A z θ :=
            Work.Spaces.sq_le_HkIntegrand_z α 6 A z θ b (by omega)
          have hY : (Work.Spaces.DzIter (m - b + 1) f z θ) ^ 2
              ≤ CPw / (Work.Spaces.gam α - 1) * Work.Spaces.HkSq α 6 f := by
            have h := hPwf (m - b + 1) 0 (by omega) z θ hz hθ
            simpa only [Work.Spaces.mixed_zero_right] using h
          exact close_locA_supf (W := Hv z θ) hα hCPw hX hY
        · have hb4 : b ≤ 4 := by omega
          have hX : (Work.Spaces.DzIter b A z θ) ^ 2
              ≤ CPw / (Work.Spaces.gam α - 1) * Work.Spaces.HkSq α 6 A := by
            have h := hPwA b 0 (by omega) z θ hz hθ
            simpa only [Work.Spaces.mixed_zero_right] using h
          have hY : (Work.Spaces.DzIter (m - b + 1) f z θ * Hv z θ) ^ 2
              ≤ Work.Spaces.HkIntegrand α 6 f z θ :=
            Work.Spaces.sq_le_HkIntegrand_z α 6 f z θ (m - b + 1) (by omega)
          exact close_supA_localf (W := Hv z θ) hα hCPw hX hY
    have hsq : ((m.choose b : ℝ)
        * (Work.Spaces.DzIter b A z θ * Work.Spaces.DzIter (m - b + 1) f z θ * Hv z θ)) ^ 2
        = (m.choose b : ℝ) ^ 2
          * (Work.Spaces.DzIter b A z θ * Work.Spaces.DzIter (m - b + 1) f z θ * Hv z θ) ^ 2 := by
      ring
    rw [hsq]
    exact mul_le_mul hcb hcore (sq_nonneg _) (by norm_num)
  have hsum2 : ∑ b ∈ Finset.range (m + 1),
      ((m.choose b : ℝ)
        * (Work.Spaces.DzIter b A z θ * Work.Spaces.DzIter (m - b + 1) f z θ * Hv z θ)) ^ 2
      ≤ ((m : ℝ) + 1) * (4096 * (max CPw 1 * Maj α A f MA KA z θ)) := by
    refine le_trans (Finset.sum_le_card_nsmul _ _ _ hterm) (le_of_eq ?_)
    rw [Finset.card_range, nsmul_eq_mul]
    congr 1
    push_cast
    ring
  have hfin : ((m : ℝ) + 1) * (((m : ℝ) + 1) * (4096 * (max CPw 1 * Maj α A f MA KA z θ)))
      ≤ 10 ^ 11 * max CPw 1 * Maj α A f MA KA z θ := by
    have hm7 : (m : ℝ) + 1 ≤ 7 := by
      have h6 : (m : ℝ) ≤ 6 := by exact_mod_cast hm
      linarith
    have hcoef : ((m : ℝ) + 1) * ((m : ℝ) + 1) * 4096 ≤ 10 ^ 11 := by nlinarith [hm7]
    have h1 : ((m : ℝ) + 1) * (((m : ℝ) + 1) * (4096 * (max CPw 1 * Maj α A f MA KA z θ)))
        = (((m : ℝ) + 1) * ((m : ℝ) + 1) * 4096)
          * (max CPw 1 * Maj α A f MA KA z θ) := by ring
    rw [h1]
    calc (((m : ℝ) + 1) * ((m : ℝ) + 1) * 4096) * (max CPw 1 * Maj α A f MA KA z θ)
        ≤ 10 ^ 11 * (max CPw 1 * Maj α A f MA KA z θ) :=
          mul_le_mul_of_nonneg_right hcoef hCMnn
      _ = 10 ^ 11 * max CPw 1 * Maj α A f MA KA z θ := by ring
  have hcs := sq_sum_le_card_mul_sum_sq (s := Finset.range (m + 1))
    (f := fun b => (m.choose b : ℝ)
      * (Work.Spaces.DzIter b A z θ * Work.Spaces.DzIter (m - b + 1) f z θ * Hv z θ))
  have hstep1 : (∑ b ∈ Finset.range (m + 1), (m.choose b : ℝ)
        * (Work.Spaces.DzIter b A z θ * Work.Spaces.DzIter (m - b + 1) f z θ * Hv z θ)) ^ 2
      ≤ ((m : ℝ) + 1) * ∑ b ∈ Finset.range (m + 1),
          ((m.choose b : ℝ)
            * (Work.Spaces.DzIter b A z θ * Work.Spaces.DzIter (m - b + 1) f z θ
              * Hv z θ)) ^ 2 := by
    simpa only [hcard] using hcs
  have hstep2 : ((m : ℝ) + 1) * ∑ b ∈ Finset.range (m + 1),
        ((m.choose b : ℝ)
          * (Work.Spaces.DzIter b A z θ * Work.Spaces.DzIter (m - b + 1) f z θ * Hv z θ)) ^ 2
      ≤ ((m : ℝ) + 1) * (((m : ℝ) + 1) * (4096 * (max CPw 1 * Maj α A f MA KA z θ))) :=
    mul_le_mul_of_nonneg_left hsum2 (by positivity)
  rw [hsum]
  exact le_trans hstep1 (le_trans hstep2 hfin)


end

end PtB

end Work.FTS.StrongEps.E4R3.Nblock6.Tools
