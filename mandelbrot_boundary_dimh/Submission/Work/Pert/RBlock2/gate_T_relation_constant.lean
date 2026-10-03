import Mathlib
import Submission.Work.Pert.Basic
import Submission.Work.Pert.Setup
import Submission.Work.Pert.Qm_Qp
import Submission.Work.Pert.RBlock3
import Submission.Work.Interfaces.Fatou
import Submission.Work.Interfaces.FatouNarrow

/-!
# PERT · `Work.Pert.RBlock2.gate_T_relation_constant`

The **constant** of the (A.4.2) relation `Φm ∘ Tt α = Φp + d` between the two gate coordinates,
computed from the two end asymptotics.

`Work.Pert.gate_T_relation` produces the relation with an undetermined constant `d`.  Here the
upper-end expansions `Φp z = z + cp + o(1)` and `Φm z = z + cm + o(1)` (both as `z.im → +∞`,
uniformly in a bounded horizontal window) pin it down: evaluating the relation at the points
`w = i t` (which lie in `Qp Ξ α` for `t` large) and using `Tt α w = w - 1/α ∈ Qm Ξ α`
(`Work.Pert.mem_Qp_add_inv_iff`, both ends being the *upper* end since `im (w - 1/α) = t - im (1/α)`),

  `0 = (Φm (Tt α w) - Tt α w - cm) - (Φp w - w - cp) = d + 1/α + cp - cm`.

The whole content is therefore the geometry `Tt α '' Qp Ξ α = Qm Ξ α` (so that the *same* `t → ∞`
drives both expansions) plus an `ε/2` triangle inequality.
-/

namespace Work.Pert.RBlock2

open MandelDim Complex Set

noncomputable section

/-- Unfolding of `Qreg` at two finite vertices. -/
private lemma mem_Qreg_some_some {z a b : ℂ} :
    z ∈ MandelDim.Qreg (some a) (some b) ↔
      (-|(z - a).im| < (z - a).re ∧ (z - b).re < |(z - b).im|) := by
  simp [MandelDim.Qreg]

/-- Points `i t` with `t` large enough lie in the upper gate `Qp Ξ α`.  (The bound is the naive
one: `Ξ < t` for the first vertex and `Ξ - Re(1/α) < |t - Im(1/α)|` for the second.) -/
private lemma mem_Qp_mul_I {Ξ : ℝ} {α : ℂ} {t : ℝ}
    (ht : Ξ < t) (ht2 : Ξ - (1 / α).re < |t - (1 / α).im|) :
    ((t : ℂ) * Complex.I) ∈ Work.Pert.Qp Ξ α := by
  rw [Work.Pert.Qp, mem_Qreg_some_some]
  constructor
  · have him : ((t : ℂ) * Complex.I - (Ξ : ℂ)).im = t := by
      simp [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im]
    have hre : ((t : ℂ) * Complex.I - (Ξ : ℂ)).re = -Ξ := by
      simp [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im]
    rw [him, hre]
    have h : Ξ < |t| := lt_of_lt_of_le ht (le_abs_self t)
    linarith
  · have hre : ((t : ℂ) * Complex.I - (-(Ξ : ℂ) + 1 / α)).re = Ξ - (1 / α).re := by
      simp [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im]; ring
    have him : ((t : ℂ) * Complex.I - (-(Ξ : ℂ) + 1 / α)).im = t - (1 / α).im := by
      simp [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im]
    rw [hre, him]
    exact ht2

theorem gate_T_relation_constant {Φm Φp : ℂ → ℂ} {α d : ℂ} {Ξ : ℝ} {cm cp : ℂ}
    (hrel : ∀ w ∈ Work.Pert.Qp Ξ α, Φm (Work.Pert.Tt α w) = Φp w + d)
    (hEndm : ∀ x : ℝ, ∀ ε > 0, ∃ Y' : ℝ, ∀ z ∈ Work.Pert.Qm Ξ α, Y' < z.im → |z.re - x| ≤ 2 →
      ‖Φm z - z - cm‖ < ε)
    (hEndp : ∀ x : ℝ, ∀ ε > 0, ∃ Y' : ℝ, ∀ z ∈ Work.Pert.Qp Ξ α, Y' < z.im → |z.re - x| ≤ 2 →
      ‖Φp z - z - cp‖ < ε) :
    d = cm - cp - 1 / α := by
  -- `‖d + 1/α + cp - cm‖` is arbitrarily small, hence zero.
  have key : ∀ ε : ℝ, 0 < ε → ‖d + 1 / α + cp - cm‖ < ε := by
    intro ε hε
    obtain ⟨Yp, hp⟩ := hEndp 0 (ε / 2) (by linarith)
    obtain ⟨Ym, hm⟩ := hEndm (-(1 / α).re) (ε / 2) (by linarith)
    set B : ℝ := max Ξ (max Yp (max (Ym + (1 / α).im) ((1 / α).im + |Ξ - (1 / α).re|)))
      with hB
    set T : ℝ := max B 0 + 1 with hT
    have hBΞ : Ξ ≤ B := by rw [hB]; exact le_max_left _ _
    have hBYp : Yp ≤ B := by
      rw [hB]; exact le_trans (le_max_left _ _) (le_max_right Ξ _)
    have hBYm : Ym + (1 / α).im ≤ B := by
      rw [hB]
      exact le_trans (le_max_left _ _)
        (le_trans (le_max_right Yp _) (le_max_right Ξ _))
    have hBc : (1 / α).im + |Ξ - (1 / α).re| ≤ B := by
      rw [hB]
      exact le_trans (le_max_right _ _)
        (le_trans (le_max_right Yp _) (le_max_right Ξ _))
    have hBT : B ≤ max B 0 := le_max_left _ _
    have hmaxT : max B 0 < T := by rw [hT]; linarith
    have hΞT : Ξ < T := lt_of_le_of_lt (le_trans hBΞ hBT) hmaxT
    have hYpT : Yp < T := lt_of_le_of_lt (le_trans hBYp hBT) hmaxT
    have hYmT : Ym + (1 / α).im < T := lt_of_le_of_lt (le_trans hBYm hBT) hmaxT
    have hcond : Ξ - (1 / α).re < |T - (1 / α).im| := by
      have h0 : |Ξ - (1 / α).re| < T - (1 / α).im := by linarith
      rw [abs_of_nonneg (le_trans (abs_nonneg _) h0.le)]
      linarith [le_abs_self (Ξ - (1 / α).re)]
    have hwQp : ((T : ℂ) * Complex.I) ∈ Work.Pert.Qp Ξ α := mem_Qp_mul_I hΞT hcond
    have hzQm : Work.Pert.Tt α ((T : ℂ) * Complex.I) ∈ Work.Pert.Qm Ξ α := by
      rw [Work.Pert.Tt]
      refine (Work.Pert.mem_Qp_add_inv_iff (ξ := Ξ) (α := α)
        (z := (T : ℂ) * Complex.I - 1 / α)).mp ?_
      have hsum : (T : ℂ) * Complex.I - 1 / α + 1 / α = (T : ℂ) * Complex.I := by ring
      rw [hsum]
      exact hwQp
    have hwim : (((T : ℂ) * Complex.I) : ℂ).im = T := by
      simp [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im]
    have hwre : (((T : ℂ) * Complex.I) : ℂ).re = 0 := by
      simp [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im]
    have hzim : (Work.Pert.Tt α ((T : ℂ) * Complex.I)).im = T - (1 / α).im := by
      rw [Work.Pert.Tt]
      simp [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im]
    have hzre : (Work.Pert.Tt α ((T : ℂ) * Complex.I)).re = -(1 / α).re := by
      rw [Work.Pert.Tt]
      simp [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im]
    have hm' : ‖Φm (Work.Pert.Tt α ((T : ℂ) * Complex.I))
        - Work.Pert.Tt α ((T : ℂ) * Complex.I) - cm‖ < ε / 2 :=
      hm _ hzQm (by rw [hzim]; linarith)
        (by rw [hzre]; simp)
    have hp' : ‖Φp ((T : ℂ) * Complex.I) - ((T : ℂ) * Complex.I) - cp‖ < ε / 2 :=
      hp _ hwQp (by rw [hwim]; exact hYpT)
        (by rw [hwre]; simp)
    have hrelw : Φm (Work.Pert.Tt α ((T : ℂ) * Complex.I)) = Φp ((T : ℂ) * Complex.I) + d :=
      hrel _ hwQp
    have hkey : d + 1 / α + cp - cm
        = (Φm (Work.Pert.Tt α ((T : ℂ) * Complex.I))
            - Work.Pert.Tt α ((T : ℂ) * Complex.I) - cm)
          - (Φp ((T : ℂ) * Complex.I) - ((T : ℂ) * Complex.I) - cp) := by
      rw [hrelw, Work.Pert.Tt]
      ring
    calc ‖d + 1 / α + cp - cm‖
        = ‖(Φm (Work.Pert.Tt α ((T : ℂ) * Complex.I))
              - Work.Pert.Tt α ((T : ℂ) * Complex.I) - cm)
            - (Φp ((T : ℂ) * Complex.I) - ((T : ℂ) * Complex.I) - cp)‖ := by rw [hkey]
      _ ≤ ‖Φm (Work.Pert.Tt α ((T : ℂ) * Complex.I))
              - Work.Pert.Tt α ((T : ℂ) * Complex.I) - cm‖
            + ‖Φp ((T : ℂ) * Complex.I) - ((T : ℂ) * Complex.I) - cp‖ := norm_sub_le _ _
      _ < ε / 2 + ε / 2 := add_lt_add hm' hp'
      _ = ε := by ring
  have hnorm : ‖d + 1 / α + cp - cm‖ = 0 := by
    by_contra hne
    exact lt_irrefl _ (key _ (lt_of_le_of_ne (norm_nonneg _) (Ne.symm hne)))
  have hC : d + 1 / α + cp - cm = 0 := norm_eq_zero.mp hnorm
  have hsub : d - (cm - cp - 1 / α) = 0 := by
    rw [show d - (cm - cp - 1 / α) = d + 1 / α + cp - cm from by ring, hC]
  exact sub_eq_zero.mp hsub

end

end Work.Pert.RBlock2
