import Mathlib
import Submission.Work.Diff.Alg.Pinch.ChatShiftAux
import Submission.Work.Diff.Alg.Pinch.RMA
import Submission.Work.Diff.Alg.Pinch.ric_margin_b
import Submission.Work.Diff.Alg.Pinch.bwCr_lower_window
import Submission.Work.Diff.Alg.Pinch.chat_shift_ric_b
import Submission.Work.Diff.Alg.Pinch.chat_shift_efun_b
import Submission.Work.Diff.Alg.Pinch.chat_shift_ric_a
import Submission.Work.Diff.Alg.Pinch.chat_shift_efun_a

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Uniform shifted strictness for the Brendle–Schoen pinching family

`Work.Diff.Alg.Pinch.chat_shift_strict` is the uniform strictness statement used in
`Work.Diff.Alg.Pinch.pinching_set_exists`: on the family of cones `Ĉ(s)`, `s ≥ ε > 0`, normalised by
`scalAlg X = 1`, there is `ĉ₀ > 0` such that for every `ĉ ∈ (0, ĉ₀]` the shifted reaction direction
`Q (X - ĉ • Iso n)` enjoys the strictness properties `ShiftStrict n s ĉ X` (strict increase of the
Ricci-pinching form at every tight direction, and strict positivity of the isotropic curvature form
at every degenerate direction of the preimage).

## The proof

Write `X = ell (chatAA n s) (chatBB s) S` with `S ∈ Dpic (chatPP n s)` (`Chat n s` is the single
cone `Ccone (chatAA n s) (chatBB s) (chatPP n s)`, `chat_eq_Ccone_param`) and let
`S = chatLinv n s X` be its preimage.  The key expansion (`chatLinv_shift_expand`) reads

`chatLinv n s (Q (X - ĉ • Iso n)) = W₀ + ĉ² μ • Iso n - 2 ĉ • M`,

where `W₀ = linv a b (Q (ell a b S))` is the *unshifted* reaction direction and `M` is the explicit
perturbation `shiftM`.  The two quantitative Böhm–Wilking strictness statements
(`ric_margin_b`/`ric_margin_a_rma` for the Ricci form at tight directions,
`efun_margin_b`/`efun_margin_a` for the isotropic curvature form at degenerate directions) give a
margin of order `(1-p)² (σ/n)² · |v|²` for `W₀`; the perturbation bounds `ricMarg_shiftM_le` and
`norm_shiftM_le`, together with the elementary window bounds
(`one_sub_ccP_ge`, `ccA_lower`, `ccP_lower`, `ccA_ccP_ge`), dominate it by `2ĉ M` as soon as
`ĉ ≤ cShiftB/cShiftA1` (Ricci form) and `ĉ ≤ cB2/cA2` (curvature form).

These four branch estimates are the modules

* `chat_shift_ric_b`, `chat_shift_efun_b` (branch `0 < s ≤ 1/2`),
* `chat_shift_ric_a`, `chat_shift_efun_a` (branch `1/2 < s`),

and the present file is their assembly, with the explicit threshold
`ĉ₀ = min (min (cShiftB n cρ) (cShiftA1 n)) (min (cB2 n ε (Cef+1)) (cA2 n (Cef+1) ce))`, where
`cρ` is a uniform lower bound for `RFAux.bwCρ n ·` on the window `[ε, 1/2]`
(`bwCr_lower_window`), `Cef+1` bounds the isotropic curvature form
(`cm_EF_bound`), and `ce` is the uniform lower bound for `efaPsi n a / A₂`
(`efaPsi_mul_lower`).

The case `n = 2` is vacuous and is handled directly by `chat_shift_strict_two`.
-/

namespace Work.Diff.Alg.Pinch

open Finset Submission.Diff.Alg

variable {n : ℕ}

theorem chat_shift_strict_of_margins (n : ℕ) (hn : 3 ≤ n) (ε : ℝ) (hε : 0 < ε) :
    ∃ ĉ₀ : ℝ, 0 < ĉ₀ ∧ ∀ s : ℝ, ε ≤ s →
      ∀ X : Submission.Diff.Alg.Curv4 n, X ∈ Work.Diff.Alg.Pinch.Chat n s →
        Submission.Diff.Alg.scalAlg X = 1 →
        ∀ ĉ : ℝ, 0 < ĉ → ĉ ≤ ĉ₀ → Work.Diff.Alg.Pinch.ShiftStrict n s ĉ X := by
  have hn2 : 2 ≤ n := by omega
  have hn3R : (3 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hn0R : (0 : ℝ) < (n : ℝ) := by linarith
  have hn2R : (0 : ℝ) < (n : ℝ) + 2 := by linarith
  have hn2m : (0 : ℝ) < (n : ℝ) - 2 := by linarith
  have hε' : 0 < min ε (1 / 4) := lt_min hε (by norm_num)
  have hε'2 : min ε (1 / 4) ≤ 1 / 2 := le_trans (min_le_right _ _) (by norm_num)
  obtain ⟨cρ, hcρ0, hcρb⟩ := bwCr_lower_window n hn2 hε' hε'2
  obtain ⟨Cef, hCef0, hCef⟩ := cm_EF_bound n
  obtain ⟨ce, hce0, hce⟩ := efaPsi_mul_lower n hn
  have hCef1pos : 0 < Cef + 1 := by linarith
  have hCef1 : ∀ D : Curv4 n, IsAlgCurv D → ∀ x y z w : Fin n → ℝ,
      |Q2P.EFun D x y z w| ≤ (Cef + 1) * ‖D‖ * Q2P.EFun (Iso n) x y z w := by
    intro D hD x y z w
    have h1 := hCef D hD x y z w
    have hIso_nn : (0 : ℝ) ≤ Q2P.EFun (Iso n) x y z w := Cone.inPIC2_iso n x y z w
    calc |Q2P.EFun D x y z w| ≤ Cef * ‖D‖ * Q2P.EFun (Iso n) x y z w := h1
      _ ≤ (Cef + 1) * ‖D‖ * Q2P.EFun (Iso n) x y z w := by
          apply mul_le_mul_of_nonneg_right _ hIso_nn
          apply mul_le_mul_of_nonneg_right (by linarith) (norm_nonneg D)
  -- positivity of the four thresholds
  have hcsb : 0 < cShiftB n cρ := by
    rw [cShiftB]
    exact div_pos (mul_pos (by norm_num) hcρ0)
      (mul_pos (mul_pos (pow_pos hn2R 2) (pow_pos hn0R 4)) (cssKP_pos hn2))
  have hcsa : 0 < cShiftA1 n := by
    rw [cShiftA1]
    exact div_pos (phiShiftA_pos hn)
      (mul_pos (mul_pos (by norm_num) (pow_pos hn0R 2)) (cssKP_pos hn2))
  have hcb2 : 0 < cB2 n (min ε (1 / 4)) (Cef + 1) := by
    rw [cB2]
    refine div_pos ?_ (mul_pos hCef1pos (cssKFlux_pos hn))
    exact div_pos
      (mul_pos (mul_pos (by norm_num) hn2m) (pow_pos hε' 3))
      (mul_pos (pow_pos hn2R 2) (pow_pos hn0R 4))
  have hca2 : 0 < cA2 n (Cef + 1) ce := by
    rw [cA2]
    refine div_pos ?_ (mul_pos hCef1pos (cssKFlux_pos hn))
    exact div_pos hce0 (mul_pos (by norm_num) (pow_pos hn0R 2))
  refine ⟨min (min (cShiftB n cρ) (cShiftA1 n))
    (min (cB2 n (min ε (1 / 4)) (Cef + 1)) (cA2 n (Cef + 1) ce)),
    lt_min (lt_min hcsb hcsa) (lt_min hcb2 hca2), ?_⟩
  intro s hsε X hX hscal ĉ hĉ0 hĉle
  have hs0 : 0 < s := lt_of_lt_of_le hε hsε
  have hs0' : (0 : ℝ) ≤ s := le_of_lt hs0
  have hdist : min ε (1 / 4) ≤ s := le_trans (min_le_left _ _) hsε
  have hXc : X ∈ Ccone (n := n) (chatAA n s) (chatBB s) (chatPP n s) := by
    rwa [← chat_eq_Ccone_param]
  obtain ⟨S, hS, hSeq⟩ := hXc
  have hSne : S ≠ 0 := by
    intro h0
    have hX0 : X = 0 := by rw [← hSeq, h0, ell_zero']
    rw [hX0, scalAlg_zero'] at hscal
    exact one_ne_zero hscal.symm
  have hchat : chatLinv n s (ell (chatAA n s) (chatBB s) S) = S := by
    rw [chatLinv_eq_linv n hn2 hs0', linv_ell n (ne_of_gt hn0R) (chatAA_denom n hn2 hs0')
      (chatBB_denom n hn2 hs0') hS.1]
  have hscalA : (1 + 2 * ((n : ℝ) - 1) * chatAA n s) * scalAlg S = 1 := by
    have h := hscal
    rw [← hSeq, scalAlg_ell] at h
    exact h
  refine ⟨?_, ?_⟩
  · intro v hv htight
    rw [← hSeq] at htight ⊢
    rw [hchat] at htight
    by_cases hs1 : s ≤ 1 / 2
    · have ha : chatAA n s = ccA n s := by rw [chatAA_eq, if_pos hs1]; rfl
      have hb : chatBB s = s := by rw [chatBB_eq, if_pos hs1]
      have hp : chatPP n s = ccP n s := by rw [chatPP_eq, if_pos hs1]; rfl
      have hSR : RicPinch (ccP n s) S := by rw [← hp]; exact hS.2.2
      have ht0 : ricMarg S (ccP n s) v = 0 := by
        rw [ricMarg_eq]
        rw [hp] at htight
        linarith
      have hsc : scalAlg (ell (ccA n s) s S) = 1 := by
        rw [scalAlg_ell]
        have h := hscalA
        rw [ha] at h
        exact h
      rw [ha, hb, hp] at ⊢
      have hric := chat_shift_ric_b n hn hε' hcρ0 hcρb hdist hs0 hs1 hĉ0
        (le_trans hĉle (le_trans (min_le_left _ _) (min_le_left _ _)))
        hS.1 hSne hS.2.1 hSR hsc v hv ht0
      rw [ricMarg_eq] at hric
      linarith
    · have hs1' : 1 / 2 < s := not_le.mp hs1
      have ha : chatAA n s = s := by rw [chatAA_eq, if_neg hs1]
      have hb : chatBB s = 1 / 2 := by rw [chatBB_eq, if_neg hs1]
      have hp : chatPP n s = 1 - 4 / ((n : ℝ) - 2 + 8 * s) := by rw [chatPP_eq, if_neg hs1]
      have hSR : RicPinch (1 - 4 / ((n : ℝ) - 2 + 8 * s)) S := by rw [← hp]; exact hS.2.2
      have ht0 : ricMarg S (1 - 4 / ((n : ℝ) - 2 + 8 * s)) v = 0 := by
        rw [ricMarg_eq]
        rw [hp] at htight
        linarith
      have hsc : scalAlg (ell s (1 / 2) S) = 1 := by
        rw [scalAlg_ell]
        have h := hscalA
        rw [ha] at h
        exact h
      rw [ha, hb, hp] at ⊢
      have hric := chat_shift_ric_a n hn (p := 1 - 4 / ((n : ℝ) - 2 + 8 * s)) hs1' rfl hĉ0
        (le_trans hĉle (le_trans (min_le_left _ _) (min_le_right _ _)))
        hS.1 hSne hS.2.1 hSR hsc v hv ht0
      rw [ricMarg_eq] at hric
      linarith
  · intro x y z w hdeg hIso
    rw [← hSeq] at hdeg ⊢
    rw [hchat] at hdeg
    by_cases hs1 : s ≤ 1 / 2
    · have ha : chatAA n s = ccA n s := by rw [chatAA_eq, if_pos hs1]; rfl
      have hb : chatBB s = s := by rw [chatBB_eq, if_pos hs1]
      have hp : chatPP n s = ccP n s := by rw [chatPP_eq, if_pos hs1]; rfl
      have hSR : RicPinch (ccP n s) S := by rw [← hp]; exact hS.2.2
      have hsc : scalAlg (ell (ccA n s) s S) = 1 := by
        rw [scalAlg_ell]
        have h := hscalA
        rw [ha] at h
        exact h
      rw [ha, hb] at ⊢
      exact chat_shift_efun_b n hn hε' hdist hs0 hs1 hĉ0 hCef1pos hCef1
        (le_trans hĉle (le_trans (min_le_right _ _) (min_le_left _ _)))
        hS.1 hSne hS.2.1 hSR hsc x y z w hdeg hIso
    · have hs1' : 1 / 2 < s := not_le.mp hs1
      have ha : chatAA n s = s := by rw [chatAA_eq, if_neg hs1]
      have hb : chatBB s = 1 / 2 := by rw [chatBB_eq, if_neg hs1]
      have hp : chatPP n s = 1 - 4 / ((n : ℝ) - 2 + 8 * s) := by rw [chatPP_eq, if_neg hs1]
      have hSR : RicPinch (1 - 4 / ((n : ℝ) - 2 + 8 * s)) S := by rw [← hp]; exact hS.2.2
      have hsc : scalAlg (ell s (1 / 2) S) = 1 := by
        rw [scalAlg_ell]
        have h := hscalA
        rw [ha] at h
        exact h
      rw [ha, hb] at ⊢
      exact chat_shift_efun_a n hn (p := 1 - 4 / ((n : ℝ) - 2 + 8 * s)) hs1' rfl hĉ0 hCef1pos
        hCef1 hce0 hce
        (le_trans hĉle (le_trans (min_le_right _ _) (min_le_right _ _)))
        hS.1 hSne hS.2.1 hSR hsc x y z w hdeg hIso

theorem chat_shift_strict (n : ℕ) (hn : 2 ≤ n) (ε : ℝ) (hε : 0 < ε) :
    ∃ ĉ₀ : ℝ, 0 < ĉ₀ ∧ ∀ s : ℝ, ε ≤ s →
      ∀ X : Submission.Diff.Alg.Curv4 n, X ∈ Work.Diff.Alg.Pinch.Chat n s →
        Submission.Diff.Alg.scalAlg X = 1 →
        ∀ ĉ : ℝ, 0 < ĉ → ĉ ≤ ĉ₀ → Work.Diff.Alg.Pinch.ShiftStrict n s ĉ X := by
  rcases eq_or_lt_of_le hn with h | h
  · subst h
    exact chat_shift_strict_two ε hε
  · exact chat_shift_strict_of_margins n (by omega) ε hε

end Work.Diff.Alg.Pinch
