import Mathlib
import Submission.Work.Diff.Alg.Pinch.ChatShiftAux

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The isotropic-curvature strictness for the shifted family, branch `1/2 < s`

This is the branch `1/2 < a` companion of `chat_shift_efun_b`: it combines the Böhm–Wilking
strictness `efun_margin_a` (for the unshifted direction `linv a (1/2) (Q (ell a (1/2) S))`) with the
quantitative perturbation bounds of `ChatShiftAux` (`norm_shiftM_le`, and the explicit expansion
`chatLinv_shift_expand` of the shifted direction) to get strict positivity of the isotropic
curvature form for the *shifted* direction
`chatLinv n s (Q (ell s (1/2) S - ĉ • Iso n))`, uniformly in `ĉ ≤ cA2 n Cef ce`.
-/

namespace Work.Diff.Alg.Pinch

open Finset Submission.Diff.Alg

variable {n : ℕ}

set_option maxHeartbeats 1000000 in
/-- **Branch `1/2 < s`, isotropic curvature form.** -/
theorem chat_shift_efun_a (n : ℕ) (hn : 3 ≤ n) {s ĉ p : ℝ} (hsh : 1 / 2 < s)
    (hp : p = 1 - 4 / ((n : ℝ) - 2 + 8 * s)) (hĉ0 : 0 < ĉ) {Cef : ℝ} (hCefpos : 0 < Cef)
    (hCef : ∀ D : Curv4 n, IsAlgCurv D → ∀ x y z w : Fin n → ℝ,
      |Q2P.EFun D x y z w| ≤ Cef * ‖D‖ * Q2P.EFun (Iso n) x y z w)
    {ce : ℝ} (hce0 : 0 < ce) (hce : ∀ a : ℝ, 1 / 2 < a →
      ce ≤ efaPsi n a / (1 + 2 * ((n : ℝ) - 1) * a))
    (hĉle : ĉ ≤ cA2 n Cef ce) {S : Curv4 n} (hSl : IsAlgCurv S) (hS0 : S ≠ 0)
    (hSP : InPIC2 S) (hSR : RicPinch p S) (hscal : scalAlg (ell s (1 / 2) S) = 1) :
    ∀ x y z w : Fin n → ℝ, Q2P.EFun S x y z w = 0 → Q2P.EFun (Iso n) x y z w ≠ 0 →
      0 < Q2P.EFun (chatLinv n s (Q (ell s (1 / 2) S - ĉ • Iso n))) x y z w := by
  intro x y z w hdeg hIso
  have hn2 : 2 ≤ n := by omega
  have hn3R : (3 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hn0R : (0 : ℝ) < (n : ℝ) := by linarith
  have hs : 0 < s := by linarith
  have hDpos : (0 : ℝ) < (n : ℝ) - 2 + 8 * s := by linarith
  have hA2pos : 0 < A2shift n s := by
    rw [A2shift]
    have h : 0 < ((n : ℝ) - 1) * s := mul_pos (by linarith) hs
    linarith
  have hA2pos' : (0 : ℝ) < (n : ℝ) ^ 2 * A2shift n s := mul_pos (pow_pos hn0R 2) hA2pos
  have ha : chatAA n s = s := by rw [chatAA_eq, if_neg (not_le.mpr hsh)]
  have hb : chatBB s = 1 / 2 := by rw [chatBB_eq, if_neg (not_le.mpr hsh)]
  have hp1 : p ≤ 1 := by
    rw [hp]
    have h2 : (0 : ℝ) ≤ 4 / ((n : ℝ) - 2 + 8 * s) := le_of_lt (div_pos (by norm_num) hDpos)
    linarith
  have hDiv : 4 / ((n : ℝ) - 2 + 8 * s) ≤ 1 := by
    rw [div_le_one hDpos]
    linarith
  have hp0 : 0 ≤ p := by rw [hp]; linarith
  have hpm1 : -1 ≤ p := by
    rw [hp]
    linarith
  have h1mp : 0 < 1 - p := by
    rw [hp]
    have h2 : (0 : ℝ) < 4 / ((n : ℝ) - 2 + 8 * s) := div_pos (by norm_num) hDpos
    linarith
  have hσ : scalAlg S = 1 / A2shift n s := by
    have h1 : A2shift n s * scalAlg S = 1 := by
      rw [A2shift, ← scalAlg_ell s (1 / 2) S]
      exact hscal
    rw [eq_div_iff (ne_of_gt hA2pos), mul_comm]
    exact h1
  have hσpos : 0 < scalAlg S := by rw [hσ]; positivity
  have hA2eq : A2shift n s * scalAlg S = 1 := by
    rw [hσ, mul_one_div, div_self (ne_of_gt hA2pos)]
  have hIso_pos : 0 < Q2P.EFun (Iso n) x y z w :=
    lt_of_le_of_ne (Cone.inPIC2_iso n x y z w) (Ne.symm hIso)
  -- the unshifted margin
  have hmargin : 2 * efaPsi n s * (scalAlg S / (n : ℝ)) ^ 2 * Q2P.EFun (Iso n) x y z w
      ≤ Q2P.EFun (shiftW0 n s (1 / 2) S) x y z w := by
    have h := efun_margin_a n hn hsh hSl hS0 hSP (by rw [← hp]; exact hSR) x y z w hdeg hIso
    simpa only [shiftW0] using h
  have hcs : ce * A2shift n s ≤ efaPsi n s := by
    have h1 := hce s hsh
    rw [le_div_iff₀ (by positivity : (0 : ℝ) < 1 + 2 * ((n : ℝ) - 1) * s)] at h1
    rw [A2shift]
    linarith [h1]
  -- the perturbing tensor
  have hMalg : IsAlgCurv (shiftM n s (1 / 2) S) := by
    rw [shiftM]
    exact linv_isAlgCurv (knProd_isAlgCurv
      (fun i j => ric_symm (ell_isAlgCurv n s (1 / 2) hSl) i j) (fun i j => id2_symm i j))
  have hMnorm : ‖shiftM n s (1 / 2) S‖ ≤ cssKFlux n / A2shift n s := by
    have h := norm_shiftM_le n hn (a := s) (b := 1 / 2) (p := p) (σ := scalAlg S)
      (by linarith) (by norm_num) (by norm_num) hp1 hσpos hSl hSR rfl hA2eq
    rw [hσ] at h
    have hcssKE : 0 ≤ cssKE n := by
      rw [cssKE]
      have h3 : (0 : ℝ) ≤ Real.sqrt ((n : ℝ) * ((n : ℝ) - 1)) := Real.sqrt_nonneg _
      have h4 : (0 : ℝ) ≤ 10 * (n : ℝ) + 1 := by linarith
      positivity
    have hL : 2 / ((n : ℝ) * A2shift n s)
          + (1 + ((n : ℝ) - 2) * (1 / 2)) * cssKE n * (1 - p) * (1 / A2shift n s)
        = (2 / (n : ℝ) + (1 + ((n : ℝ) - 2) * (1 / 2)) * cssKE n * (1 - p))
          / A2shift n s := by
      ring_nf
    rw [hL] at h
    have h1 : (1 + ((n : ℝ) - 2) * (1 / 2)) * cssKE n * (1 - p)
        ≤ (1 + ((n : ℝ) - 2) / 2) * cssKE n := by
      have hnn : 0 ≤ (1 + ((n : ℝ) - 2) * (1 / 2)) * cssKE n :=
        mul_nonneg (by nlinarith [hn3R]) hcssKE
      have hle1 : (1 - p) ≤ 1 := by linarith [hp0]
      calc (1 + ((n : ℝ) - 2) * (1 / 2)) * cssKE n * (1 - p)
          ≤ (1 + ((n : ℝ) - 2) * (1 / 2)) * cssKE n * 1 :=
            mul_le_mul_of_nonneg_left hle1 hnn
        _ = (1 + ((n : ℝ) - 2) * (1 / 2)) * cssKE n := by ring
        _ ≤ (1 + ((n : ℝ) - 2) / 2) * cssKE n :=
            mul_le_mul_of_nonneg_right (by linarith) hcssKE
    rw [cssKFlux]
    refine le_trans h (div_le_div_of_nonneg_right ?_ hA2pos.le)
    linarith [h1]
  have hEF : |Q2P.EFun (shiftM n s (1 / 2) S) x y z w|
      ≤ Cef * (cssKFlux n / A2shift n s) * Q2P.EFun (Iso n) x y z w := by
    have h1 := hCef (shiftM n s (1 / 2) S) hMalg x y z w
    have h2 : (0 : ℝ) ≤ Q2P.EFun (Iso n) x y z w := hIso_pos.le
    calc |Q2P.EFun (shiftM n s (1 / 2) S) x y z w|
        ≤ Cef * ‖shiftM n s (1 / 2) S‖ * Q2P.EFun (Iso n) x y z w := h1
      _ ≤ Cef * (cssKFlux n / A2shift n s) * Q2P.EFun (Iso n) x y z w := by
          apply mul_le_mul_of_nonneg_right _ h2
          exact mul_le_mul_of_nonneg_left hMnorm hCefpos.le
  -- the shifted direction
  have hW : chatLinv n s (Q (ell s (1 / 2) S - ĉ • Iso n))
      = shiftW0 n s (1 / 2) S + (ĉ ^ 2 * shiftMu n (A2shift n s)) • Iso n
        - (2 * ĉ) • shiftM n s (1 / 2) S := by
    have h := chatLinv_shift_expand (ĉ := ĉ) n hn2 hs (ell_isAlgCurv n s (1 / 2) hSl)
    rw [ha, hb] at h
    simpa only [shiftW0, shiftM, shiftMu, A2shift] using h
  rw [hW]
  have he : shiftW0 n s (1 / 2) S + (ĉ ^ 2 * shiftMu n (A2shift n s)) • Iso n
        - (2 * ĉ) • shiftM n s (1 / 2) S
      = shiftW0 n s (1 / 2) S + (ĉ ^ 2 * shiftMu n (A2shift n s)) • Iso n
        + (-(2 * ĉ)) • shiftM n s (1 / 2) S := by
    ext i j k l
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    ring
  rw [he, Q2P_EFun_add, Q2P_EFun_add, Q2P_EFun_smul, Q2P_EFun_smul]
  have hIso_nn : 0 ≤ Q2P.EFun (Iso n) x y z w := hIso_pos.le
  have hμ : 0 ≤ (ĉ ^ 2 * shiftMu n (A2shift n s)) * Q2P.EFun (Iso n) x y z w := by
    apply mul_nonneg _ hIso_nn
    apply mul_nonneg (sq_nonneg _)
    rw [shiftMu]
    positivity
  -- the arithmetic
  have hcs' : ce ≤ efaPsi n s / A2shift n s := by
    have h1 := hce s hsh
    simpa only [A2shift] using h1
  have hlow2 : 2 * ce / ((n : ℝ) ^ 2 * A2shift n s)
      ≤ 2 * efaPsi n s * (scalAlg S / (n : ℝ)) ^ 2 := by
    have h2 : 2 * ce ≤ 2 * (efaPsi n s / A2shift n s) := by linarith [hcs']
    have h3 : 2 * ce / ((n : ℝ) ^ 2 * A2shift n s)
        ≤ 2 * (efaPsi n s / A2shift n s) / ((n : ℝ) ^ 2 * A2shift n s) :=
      div_le_div_of_nonneg_right h2 hA2pos'.le
    have h4 : 2 * (efaPsi n s / A2shift n s) / ((n : ℝ) ^ 2 * A2shift n s)
        = 2 * efaPsi n s * (scalAlg S / (n : ℝ)) ^ 2 := by
      rw [hσ]
      field_simp
      try ring
    linarith [h3, h4.le, h4.ge]
  have hkey : (2 * ĉ) * (Cef * (cssKFlux n / A2shift n s)) * Q2P.EFun (Iso n) x y z w
      < 2 * efaPsi n s * (scalAlg S / (n : ℝ)) ^ 2 * Q2P.EFun (Iso n) x y z w := by
    have hne : Cef * cssKFlux n ≠ 0 := ne_of_gt (mul_pos hCefpos (cssKFlux_pos hn))
    have h2 : cA2 n Cef ce * (Cef * cssKFlux n) = ce / (2 * (n : ℝ) ^ 2) := by
      rw [cA2, div_mul_cancel₀ _ hne]
    have h1 : ĉ * (Cef * cssKFlux n) ≤ cA2 n Cef ce * (Cef * cssKFlux n) :=
      mul_le_mul_of_nonneg_right hĉle (le_of_lt (mul_pos hCefpos (cssKFlux_pos hn)))
    have h3 : 2 * (n : ℝ) ^ 2 * (ĉ * (Cef * cssKFlux n)) ≤ ce := by
      have h4 : 2 * (n : ℝ) ^ 2 * (ĉ * (Cef * cssKFlux n))
          ≤ 2 * (n : ℝ) ^ 2 * (ce / (2 * (n : ℝ) ^ 2)) := by
        rw [h2] at h1
        exact mul_le_mul_of_nonneg_left h1 (by positivity)
      have h5 : 2 * (n : ℝ) ^ 2 * (ce / (2 * (n : ℝ) ^ 2)) = ce := by
        rw [show (2 : ℝ) * (n : ℝ) ^ 2 * (ce / (2 * (n : ℝ) ^ 2))
            = ce / (2 * (n : ℝ) ^ 2) * (2 * (n : ℝ) ^ 2) from by ring]
        rw [div_mul_cancel₀ _ (by positivity : (2 : ℝ) * (n : ℝ) ^ 2 ≠ 0)]
      linarith [h4, h5.le, h5.ge]
    have hefpos : 0 < efaPsi n s / A2shift n s := lt_of_lt_of_le hce0 hcs'
    have hnum : 2 * (n : ℝ) ^ 2 * (ĉ * (Cef * cssKFlux n)) < 2 * (efaPsi n s / A2shift n s) := by
      linarith
    have hpert : (2 * ĉ) * (Cef * (cssKFlux n / A2shift n s))
        = (2 * (n : ℝ) ^ 2 * (ĉ * (Cef * cssKFlux n))) / ((n : ℝ) ^ 2 * A2shift n s) := by
      rw [eq_div_iff (ne_of_gt hA2pos')]
      field_simp
      try ring
    have hmarg : 2 * efaPsi n s * (scalAlg S / (n : ℝ)) ^ 2
        = (2 * (efaPsi n s / A2shift n s)) / ((n : ℝ) ^ 2 * A2shift n s) := by
      rw [hσ]
      field_simp
      try ring
    rw [hpert, hmarg]
    exact mul_lt_mul_of_pos_right
      (div_lt_div_of_pos_right hnum hA2pos') hIso_pos
  have hMstep : (2 * ĉ) * Q2P.EFun (shiftM n s (1 / 2) S) x y z w
      ≤ (2 * ĉ) * (Cef * (cssKFlux n / A2shift n s)) * Q2P.EFun (Iso n) x y z w := by
    have h1 : Q2P.EFun (shiftM n s (1 / 2) S) x y z w
        ≤ Cef * (cssKFlux n / A2shift n s) * Q2P.EFun (Iso n) x y z w :=
      le_trans (le_abs_self _) hEF
    calc (2 * ĉ) * Q2P.EFun (shiftM n s (1 / 2) S) x y z w
        ≤ (2 * ĉ) * (Cef * (cssKFlux n / A2shift n s) * Q2P.EFun (Iso n) x y z w) :=
          mul_le_mul_of_nonneg_left h1 (by linarith : (0 : ℝ) ≤ 2 * ĉ)
      _ = (2 * ĉ) * (Cef * (cssKFlux n / A2shift n s)) * Q2P.EFun (Iso n) x y z w := by ring
  have hfin : (2 * ĉ) * Q2P.EFun (shiftM n s (1 / 2) S) x y z w
      < 2 * efaPsi n s * (scalAlg S / (n : ℝ)) ^ 2 * Q2P.EFun (Iso n) x y z w :=
    lt_of_le_of_lt hMstep hkey
  have hchain : (2 * ĉ) * Q2P.EFun (shiftM n s (1 / 2) S) x y z w
      < Q2P.EFun (shiftW0 n s (1 / 2) S) x y z w := lt_of_lt_of_le hfin hmargin
  linarith [hchain, hμ]

end Work.Diff.Alg.Pinch
