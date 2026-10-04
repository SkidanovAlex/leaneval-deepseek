import Mathlib
import Submission.Work.Diff.Alg.Pinch.ChatShiftAux
import Submission.Work.Diff.Alg.Pinch.ric_margin_b
import Submission.Work.Diff.Alg.Pinch.bwCr_lower_window

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Branch `0 < s ≤ 1/2`, isotropic curvature form: uniform shifted strictness

The second branch lemma of `Work.Diff.Alg.Pinch.chat_shift_strict`: for `0 < s ≤ 1/2`, a point
`S ∈ Dpic (ccP n s)` with `scalAlg (ell (ccA n s) s S) = 1`, a *degenerate* direction `(x,y,z,w)`
of the quartic form `Q2P.EFun S` (with `Q2P.EFun (Iso n) x y z w ≠ 0`), the shifted reaction
direction improves the isotropic-curvature form for every `ĉ ≤ cB2 n ε Cef`, where `Cef` is the
constant of `cm_EF_bound` (`|Q2P.EFun D| ≤ Cef ‖D‖ Q2P.EFun (Iso n)`).
-/

namespace Work.Diff.Alg.Pinch

open Finset Submission.Diff.Alg

variable {n : ℕ}

set_option maxHeartbeats 1000000 in
theorem chat_shift_efun_b (n : ℕ) (hn : 3 ≤ n) {ε s ĉ : ℝ} (hε : 0 < ε) (hsε : ε ≤ s)
    (hs : 0 < s) (hs1 : s ≤ 1 / 2) (hĉ0 : 0 < ĉ) {Cef : ℝ} (hCefpos : 0 < Cef)
    (hCef : ∀ D : Curv4 n, IsAlgCurv D → ∀ x y z w : Fin n → ℝ,
      |Q2P.EFun D x y z w| ≤ Cef * ‖D‖ * Q2P.EFun (Iso n) x y z w)
    (hĉle : ĉ ≤ cB2 n ε Cef) {S : Curv4 n} (hSl : IsAlgCurv S) (hS0 : S ≠ 0)
    (hSP : InPIC2 S) (hSR : RicPinch (ccP n s) S)
    (hscal : scalAlg (ell (ccA n s) s S) = 1) :
    ∀ x y z w : Fin n → ℝ, Q2P.EFun S x y z w = 0 → Q2P.EFun (Iso n) x y z w ≠ 0 →
      0 < Q2P.EFun (chatLinv n s (Q (ell (ccA n s) s S - ĉ • Iso n))) x y z w := by
  intro x y z w hdeg hIso
  have hn2 : 2 ≤ n := by omega
  have hn2R : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn2
  have hn0R : (0 : ℝ) < (n : ℝ) := by linarith
  have ha : chatAA n s = ccA n s := by rw [chatAA_eq, if_pos hs1]; rfl
  have hb : chatBB s = s := by rw [chatBB_eq, if_pos hs1]
  have hccAp : 0 < ccA n s := ccA_pos (by omega) hs hs1
  have hccApp : 0 ≤ ccA n s := hccAp.le
  have hccA_half : ccA n s ≤ 1 / 2 := chatA_le_half n hn2 hs1
  have hA2pos : 0 < A2shift n (ccA n s) := by rw [A2shift]; nlinarith
  have hA2le : A2shift n (ccA n s) ≤ (n : ℝ) := by rw [A2shift]; nlinarith
  have hA2one : (1 : ℝ) ≤ A2shift n (ccA n s) := by rw [A2shift]; nlinarith
  have hccP1 : ccP n s ≤ 1 := (ccP_lt_one (by omega) hs hs1).le
  have hccPnn : (0 : ℝ) ≤ ccP n s := ccP_nn (n := n) hn2 (b := s)
  have hccPm1 : -1 ≤ ccP n s := by
    have := ccP_nn (n := n) hn2 (b := s)
    linarith
  have hσ : scalAlg S = 1 / A2shift n (ccA n s) := by
    have h1 : A2shift n (ccA n s) * scalAlg S = 1 := by
      rw [A2shift, ← scalAlg_ell (ccA n s) s S]
      exact hscal
    rw [eq_div_iff (ne_of_gt hA2pos), mul_comm]
    exact h1
  have hσpos : 0 < scalAlg S := by rw [hσ]; positivity
  have hA2eq : A2shift n (ccA n s) * scalAlg S = 1 := by
    rw [hσ, mul_one_div, div_self (ne_of_gt hA2pos)]
  have hIso_pos : 0 < Q2P.EFun (Iso n) x y z w :=
    lt_of_le_of_ne (Cone.inPIC2_iso n x y z w) (Ne.symm hIso)
  have hmargin : 4 * ccA n s * ccP n s * (scalAlg S / (n : ℝ)) ^ 2 * Q2P.EFun (Iso n) x y z w
      ≤ Q2P.EFun (shiftW0 n (ccA n s) s S) x y z w := by
    have h := efun_margin_b n hn2 hs hs1 hSl hS0 hSP hSR x y z w hdeg hIso
    simpa only [shiftW0] using h
  have hMalg : IsAlgCurv (shiftM n (ccA n s) s S) := by
    rw [shiftM]
    exact linv_isAlgCurv (knProd_isAlgCurv
      (fun i j => ric_symm (ell_isAlgCurv n (ccA n s) s hSl) i j) (fun i j => id2_symm i j))
  have hMnorm : ‖shiftM n (ccA n s) s S‖ ≤ cssKFlux n / A2shift n (ccA n s) := by
    have h := norm_shiftM_le n hn hccApp (le_of_lt hs) hs1 hccP1 hσpos hSl hSR rfl hA2eq
    rw [hσ] at h
    have hcssKE : 0 ≤ cssKE n := by
      rw [cssKE]
      have h3 : (0 : ℝ) ≤ Real.sqrt ((n : ℝ) * ((n : ℝ) - 1)) := Real.sqrt_nonneg _
      have h4 : (0 : ℝ) ≤ 10 * (n : ℝ) + 1 := by linarith
      positivity
    have h1 : (1 + ((n : ℝ) - 2) * s) * cssKE n * (1 - ccP n s)
        ≤ (1 + ((n : ℝ) - 2) / 2) * cssKE n := by
      have ha1 : (1 + ((n : ℝ) - 2) * s) ≤ (1 + ((n : ℝ) - 2) / 2) := by nlinarith [hs1]
      have hnn : 0 ≤ (1 + ((n : ℝ) - 2) * s) * cssKE n := by
        apply mul_nonneg _ hcssKE
        have h2 : (0 : ℝ) ≤ (n : ℝ) - 2 := by linarith
        nlinarith [mul_nonneg h2 hs.le]
      calc (1 + ((n : ℝ) - 2) * s) * cssKE n * (1 - ccP n s)
          ≤ (1 + ((n : ℝ) - 2) * s) * cssKE n * 1 :=
            mul_le_mul_of_nonneg_left (by linarith [hccP1]) hnn
        _ = (1 + ((n : ℝ) - 2) * s) * cssKE n := by ring
        _ ≤ (1 + ((n : ℝ) - 2) / 2) * cssKE n := mul_le_mul_of_nonneg_right ha1 hcssKE
    have hL : 2 / ((n : ℝ) * A2shift n (ccA n s))
          + (1 + ((n : ℝ) - 2) * s) * cssKE n * (1 - ccP n s) * (1 / A2shift n (ccA n s))
        = (2 / (n : ℝ) + (1 + ((n : ℝ) - 2) * s) * cssKE n * (1 - ccP n s))
          / A2shift n (ccA n s) := by
      ring_nf
    rw [hL] at h
    have h2 : (2 / (n : ℝ) + (1 + ((n : ℝ) - 2) * s) * cssKE n * (1 - ccP n s))
        ≤ 2 / (n : ℝ) + (1 + ((n : ℝ) - 2) / 2) * cssKE n := by linarith [h1]
    rw [cssKFlux]
    exact le_trans h (div_le_div_of_nonneg_right h2 hA2pos.le)
  have hEF : |Q2P.EFun (shiftM n (ccA n s) s S) x y z w|
      ≤ Cef * (cssKFlux n / A2shift n (ccA n s)) * Q2P.EFun (Iso n) x y z w := by
    have h1 := hCef (shiftM n (ccA n s) s S) hMalg x y z w
    have h2 : (0 : ℝ) ≤ Q2P.EFun (Iso n) x y z w := hIso_pos.le
    calc |Q2P.EFun (shiftM n (ccA n s) s S) x y z w|
        ≤ Cef * ‖shiftM n (ccA n s) s S‖ * Q2P.EFun (Iso n) x y z w := h1
      _ ≤ Cef * (cssKFlux n / A2shift n (ccA n s)) * Q2P.EFun (Iso n) x y z w := by
          apply mul_le_mul_of_nonneg_right _ h2
          exact mul_le_mul_of_nonneg_left hMnorm hCefpos.le
  have hW : chatLinv n s (Q (ell (ccA n s) s S - ĉ • Iso n))
      = shiftW0 n (ccA n s) s S + (ĉ ^ 2 * shiftMu n (A2shift n (ccA n s))) • Iso n
        - (2 * ĉ) • shiftM n (ccA n s) s S := by
    have h := chatLinv_shift_expand (ĉ := ĉ) n hn2 hs (ell_isAlgCurv n (ccA n s) s hSl)
    rw [ha, hb] at h
    simpa only [shiftW0, shiftM, shiftMu, A2shift] using h
  rw [hW]
  have he : shiftW0 n (ccA n s) s S + (ĉ ^ 2 * shiftMu n (A2shift n (ccA n s))) • Iso n
        - (2 * ĉ) • shiftM n (ccA n s) s S
      = shiftW0 n (ccA n s) s S + (ĉ ^ 2 * shiftMu n (A2shift n (ccA n s))) • Iso n
        + (-(2 * ĉ)) • shiftM n (ccA n s) s S := by
    ext i j k l
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    ring
  rw [he, Q2P_EFun_add, Q2P_EFun_add, Q2P_EFun_smul, Q2P_EFun_smul]
  have hIso_nn : 0 ≤ Q2P.EFun (Iso n) x y z w := hIso_pos.le
  have hμ : 0 ≤ (ĉ ^ 2 * shiftMu n (A2shift n (ccA n s))) * Q2P.EFun (Iso n) x y z w := by
    apply mul_nonneg _ hIso_nn
    apply mul_nonneg (sq_nonneg _)
    rw [shiftMu]
    positivity
  have hA2inv : 1 / A2shift n (ccA n s) ≤ 1 := by
    rw [div_le_one hA2pos]
    linarith [hA2one]
  have hlow2 : 64 * ((n : ℝ) - 2) * ε ^ 3 / (((n : ℝ) + 2) ^ 2 * (n : ℝ) ^ 4)
      ≤ 4 * ccA n s * ccP n s * (scalAlg S / (n : ℝ)) ^ 2 := by
    have hcc := ccA_ccP_ge n hn hε hsε hs1
    have hσ1 : 1 / (n : ℝ) ^ 2 ≤ scalAlg S / (n : ℝ) := by
      have he2 : scalAlg S / (n : ℝ) = 1 / (A2shift n (ccA n s) * (n : ℝ)) := by
        rw [hσ, div_div]
      rw [he2]
      rw [div_le_div_iff₀ (by positivity : (0 : ℝ) < (n : ℝ) ^ 2) (mul_pos hA2pos hn0R)]
      simpa only [one_mul, pow_two] using mul_le_mul_of_nonneg_right hA2le hn0R.le
    have h3 : 1 / (n : ℝ) ^ 4 ≤ (scalAlg S / (n : ℝ)) ^ 2 := by
      have h4 : 1 / (n : ℝ) ^ 4 = (1 / (n : ℝ) ^ 2) ^ 2 := by ring
      rw [h4]
      exact pow_le_pow_left₀ (by positivity) hσ1 2
    have hccnn : (0 : ℝ) ≤ ccA n s * ccP n s := mul_nonneg hccApp hccPnn
    calc 64 * ((n : ℝ) - 2) * ε ^ 3 / (((n : ℝ) + 2) ^ 2 * (n : ℝ) ^ 4)
        = 4 * ((16 * ((n : ℝ) - 2) * ε ^ 3 / (((n : ℝ) + 2) ^ 2)) * (1 / (n : ℝ) ^ 4)) := by
          field_simp
          try ring
      _ ≤ 4 * ((ccA n s * ccP n s) * (scalAlg S / (n : ℝ)) ^ 2) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul hcc h3 (by positivity : (0 : ℝ) ≤ 1 / (n : ℝ) ^ 4) hccnn)
            (by norm_num : (0 : ℝ) ≤ 4)
      _ = 4 * ccA n s * ccP n s * (scalAlg S / (n : ℝ)) ^ 2 := by ring
  have hkey : (2 * ĉ) * (Cef * (cssKFlux n / A2shift n (ccA n s)))
        * Q2P.EFun (Iso n) x y z w
      < 4 * ccA n s * ccP n s * (scalAlg S / (n : ℝ)) ^ 2 * Q2P.EFun (Iso n) x y z w := by
    have hnum : (2 * ĉ) * (Cef * cssKFlux n) < 64 * ((n : ℝ) - 2) * ε ^ 3
        / (((n : ℝ) + 2) ^ 2 * (n : ℝ) ^ 4) := by
      have hne : Cef * cssKFlux n ≠ 0 := ne_of_gt (mul_pos hCefpos (cssKFlux_pos hn))
      have h2 : cB2 n ε Cef * (Cef * cssKFlux n)
          = 16 * ((n : ℝ) - 2) * ε ^ 3 / (((n : ℝ) + 2) ^ 2 * (n : ℝ) ^ 4) := by
        rw [cB2, div_mul_cancel₀ _ hne]
      have h1 : ĉ * (Cef * cssKFlux n) ≤ cB2 n ε Cef * (Cef * cssKFlux n) :=
        mul_le_mul_of_nonneg_right hĉle (le_of_lt (mul_pos hCefpos (cssKFlux_pos hn)))
      have hpos : (0 : ℝ) < ((n : ℝ) - 2) * ε ^ 3 / (((n : ℝ) + 2) ^ 2 * (n : ℝ) ^ 4) := by
        apply div_pos _ (by positivity)
        have h2n : (2 : ℝ) < (n : ℝ) := by exact_mod_cast (by omega : 2 < n)
        positivity
      have h3 : 32 * ((n : ℝ) - 2) * ε ^ 3 / (((n : ℝ) + 2) ^ 2 * (n : ℝ) ^ 4)
          < 64 * ((n : ℝ) - 2) * ε ^ 3 / (((n : ℝ) + 2) ^ 2 * (n : ℝ) ^ 4) := by
        have he : 32 * ((n : ℝ) - 2) * ε ^ 3 / (((n : ℝ) + 2) ^ 2 * (n : ℝ) ^ 4)
            = 32 * (((n : ℝ) - 2) * ε ^ 3 / (((n : ℝ) + 2) ^ 2 * (n : ℝ) ^ 4)) := by ring
        have he2 : 64 * ((n : ℝ) - 2) * ε ^ 3 / (((n : ℝ) + 2) ^ 2 * (n : ℝ) ^ 4)
            = 64 * (((n : ℝ) - 2) * ε ^ 3 / (((n : ℝ) + 2) ^ 2 * (n : ℝ) ^ 4)) := by ring
        rw [he, he2]
        linarith [hpos]
      have hA : (2 * ĉ) * (Cef * cssKFlux n) ≤ 2 * (cB2 n ε Cef * (Cef * cssKFlux n)) := by
        linarith [h1]
      rw [h2] at hA
      have hB : 2 * (16 * ((n : ℝ) - 2) * ε ^ 3 / (((n : ℝ) + 2) ^ 2 * (n : ℝ) ^ 4))
          = 32 * ((n : ℝ) - 2) * ε ^ 3 / (((n : ℝ) + 2) ^ 2 * (n : ℝ) ^ 4) := by ring
      rw [hB] at hA
      exact lt_of_le_of_lt hA h3
    have hpert : (2 * ĉ) * (Cef * (cssKFlux n / A2shift n (ccA n s)))
        = (2 * ĉ * (Cef * cssKFlux n)) / A2shift n (ccA n s) := by ring
    have hle : (2 * ĉ * (Cef * cssKFlux n)) / A2shift n (ccA n s) ≤ 2 * ĉ * (Cef * cssKFlux n) := by
      rw [div_le_iff₀ hA2pos]
      have hX : (0 : ℝ) ≤ 2 * ĉ * (Cef * cssKFlux n) :=
        mul_nonneg (by linarith) (mul_nonneg hCefpos.le (cssKFlux_pos hn).le)
      nlinarith [hA2one, hX]
    calc (2 * ĉ) * (Cef * (cssKFlux n / A2shift n (ccA n s))) * Q2P.EFun (Iso n) x y z w
        = ((2 * ĉ * (Cef * cssKFlux n)) / A2shift n (ccA n s)) * Q2P.EFun (Iso n) x y z w := by
          rw [hpert]
      _ ≤ (2 * ĉ * (Cef * cssKFlux n)) * Q2P.EFun (Iso n) x y z w :=
          mul_le_mul_of_nonneg_right hle hIso_pos.le
      _ < (64 * ((n : ℝ) - 2) * ε ^ 3 / (((n : ℝ) + 2) ^ 2 * (n : ℝ) ^ 4))
            * Q2P.EFun (Iso n) x y z w := mul_lt_mul_of_pos_right hnum hIso_pos
      _ ≤ (4 * ccA n s * ccP n s * (scalAlg S / (n : ℝ)) ^ 2) * Q2P.EFun (Iso n) x y z w :=
          mul_le_mul_of_nonneg_right hlow2 hIso_pos.le
      _ = 4 * ccA n s * ccP n s * (scalAlg S / (n : ℝ)) ^ 2 * Q2P.EFun (Iso n) x y z w := rfl
  have hMstep : (2 * ĉ) * Q2P.EFun (shiftM n (ccA n s) s S) x y z w
      ≤ (2 * ĉ) * (Cef * (cssKFlux n / A2shift n (ccA n s))) * Q2P.EFun (Iso n) x y z w := by
    have h1 : Q2P.EFun (shiftM n (ccA n s) s S) x y z w
        ≤ Cef * (cssKFlux n / A2shift n (ccA n s)) * Q2P.EFun (Iso n) x y z w :=
      le_trans (le_abs_self _) hEF
    calc (2 * ĉ) * Q2P.EFun (shiftM n (ccA n s) s S) x y z w
        ≤ (2 * ĉ) * (Cef * (cssKFlux n / A2shift n (ccA n s))
            * Q2P.EFun (Iso n) x y z w) :=
          mul_le_mul_of_nonneg_left h1 (by linarith : (0 : ℝ) ≤ 2 * ĉ)
      _ = (2 * ĉ) * (Cef * (cssKFlux n / A2shift n (ccA n s))) * Q2P.EFun (Iso n) x y z w := by
          ring
  have hfin : (2 * ĉ) * Q2P.EFun (shiftM n (ccA n s) s S) x y z w
      < 4 * ccA n s * ccP n s * (scalAlg S / (n : ℝ)) ^ 2 * Q2P.EFun (Iso n) x y z w :=
    lt_of_le_of_lt hMstep hkey
  have hchain : (2 * ĉ) * Q2P.EFun (shiftM n (ccA n s) s S) x y z w
      < Q2P.EFun (shiftW0 n (ccA n s) s S) x y z w := lt_of_lt_of_le hfin hmargin
  linarith [hchain, hμ]


end Work.Diff.Alg.Pinch
