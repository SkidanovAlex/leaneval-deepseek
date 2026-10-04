import Mathlib
import Submission.Work.Diff.Alg.Pinch.ChatShiftAux
import Submission.Work.Diff.Alg.Pinch.RMA

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Branch `1/2 < s`, Ricci form: uniform shifted strictness

The third branch lemma of `Work.Diff.Alg.Pinch.chat_shift_strict`: for `1/2 < s`, a point
`S ∈ Dpic p` (`p = 1 - 4/((n-2)+8s)`, `a = s`, `b = 1/2`) with `scalAlg (ell s (1/2) S) = 1` and a
*tight* direction `v`, the shifted reaction direction improves the Ricci form for every
`ĉ ≤ cShiftA1 n`.  The margin is the one of `ric_margin_a_rma`,
`2(1-p) (scalAlg S/n)² ((2s-1) + n(1-p)²/(4A₂))`, bounded below with `A₂ φ(n)` via
`phiShiftA_le`; the perturbation is `ricMarg_shiftM_le`.
-/

namespace Work.Diff.Alg.Pinch

open Finset Submission.Diff.Alg

variable {n : ℕ}

theorem chat_shift_ric_a (n : ℕ) (hn : 3 ≤ n) {s ĉ p : ℝ} (hsh : 1 / 2 < s)
    (hp : p = 1 - 4 / ((n : ℝ) - 2 + 8 * s)) (hĉ0 : 0 < ĉ) (hĉle : ĉ ≤ cShiftA1 n)
    {S : Curv4 n} (hSl : IsAlgCurv S) (hS0 : S ≠ 0) (hSP : InPIC2 S)
    (hSR : RicPinch p S) (hscal : scalAlg (ell s (1 / 2) S) = 1) :
    ∀ v : Fin n → ℝ, v ≠ 0 → ricMarg S p v = 0 →
      0 < ricMarg (chatLinv n s (Q (ell s (1 / 2) S - ĉ • Iso n))) p v := by
  intro v hv htight
  have hn2 : 2 ≤ n := by omega
  have hn2R : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn2
  have hn0R : (0 : ℝ) < (n : ℝ) := by linarith
  have hs : 0 < s := by linarith
  have hDpos : (0 : ℝ) < (n : ℝ) - 2 + 8 * s := by nlinarith
  have h1mp : 0 < 1 - p := by
    rw [hp]
    have h2 : (0 : ℝ) < 4 / ((n : ℝ) - 2 + 8 * s) := by positivity
    linarith
  have hp1 : p ≤ 1 := by
    rw [hp]
    have h2 : (0 : ℝ) ≤ 4 / ((n : ℝ) - 2 + 8 * s) := by positivity
    linarith
  have hpm1 : -1 ≤ p := by
    rw [hp]
    have h4 : 4 / ((n : ℝ) - 2 + 8 * s) ≤ 1 := by
      rw [div_le_one hDpos]
      nlinarith
    linarith
  have ha : chatAA n s = s := by rw [chatAA_eq, if_neg (not_le.mpr hsh)]
  have hb : chatBB s = 1 / 2 := by rw [chatBB_eq, if_neg (not_le.mpr hsh)]
  have hA2pos : 0 < A2shift n s := by rw [A2shift]; nlinarith
  have hσ : scalAlg S = 1 / A2shift n s := by
    have h1 : A2shift n s * scalAlg S = 1 := by
      rw [A2shift, ← scalAlg_ell s (1 / 2) S]
      exact hscal
    rw [eq_div_iff (ne_of_gt hA2pos), mul_comm]
    exact h1
  have hσpos : 0 < scalAlg S := by rw [hσ]; positivity
  have hA2eq : A2shift n s * scalAlg S = 1 := by
    rw [hσ, mul_one_div, div_self (ne_of_gt hA2pos)]
  have hSvpos : 0 < ∑ i, v i * v i := by
    obtain ⟨i₀, hi₀⟩ : ∃ i, v i ≠ 0 := by
      by_contra h
      push_neg at h
      exact hv (funext fun i => h i)
    have hnn : ∀ i ∈ (Finset.univ : Finset (Fin n)), 0 ≤ v i * v i :=
      fun i _ => mul_self_nonneg (v i)
    have hle : v i₀ * v i₀ ≤ ∑ i, v i * v i := Finset.single_le_sum hnn (Finset.mem_univ i₀)
    have hlt : 0 < v i₀ * v i₀ := mul_self_pos.mpr hi₀
    linarith
  have hsv : 0 ≤ ∑ i, v i * v i := hSvpos.le
  have ht' : (p * scalAlg S / (n : ℝ)) * (∑ i, v i * v i)
      = ∑ i, ∑ j, ric S i j * v i * v j := by
    rw [ricMarg_eq] at htight
    linarith
  have hmargin : 2 * (1 - p) * phiShiftA n / ((n : ℝ) ^ 2 * A2shift n s) * (∑ i, v i * v i)
      ≤ ricMarg (shiftW0 n s (1 / 2) S) p v := by
    have hric := ric_margin_a_rma n hn2 hsh hSl hS0 hSP (by rw [← hp]; exact hSR) hv
      (by rw [← hp]; exact ht')
    have hw0 : ricMarg (shiftW0 n s (1 / 2) S) p v
        = (∑ i, ∑ j, ric (linv s (1 / 2) (Q (ell s (1 / 2) S))) i j * v i * v j)
          - (p * scalAlg (linv s (1 / 2) (Q (ell s (1 / 2) S))) / (n : ℝ))
            * (∑ i, v i * v i) := by
      rw [shiftW0, ricMarg_eq]
    rw [hw0]
    have hS1 : A2shift n s * phiShiftA n
        ≤ (2 * s - 1) + (n : ℝ) * (4 / ((n : ℝ) - 2 + 8 * s)) ^ 2
            / (4 * (1 + 2 * ((n : ℝ) - 1) * s)) := by
      have h := phiShiftA_le n hn hsh
      rw [A2shift]
      rw [le_div_iff₀ (by positivity : (0 : ℝ) < 1 + 2 * ((n : ℝ) - 1) * s)] at h
      linarith [h]
    have he : 1 - p = 4 / ((n : ℝ) - 2 + 8 * s) := by rw [hp]; ring
    have hfacn : (0 : ℝ) ≤ 2 * (1 - p) * (scalAlg S / (n : ℝ)) ^ 2 :=
      mul_nonneg (mul_nonneg (by norm_num) (le_of_lt h1mp)) (by positivity)
    calc 2 * (1 - p) * phiShiftA n / ((n : ℝ) ^ 2 * A2shift n s) * (∑ i, v i * v i)
        = 2 * (1 - p) * (scalAlg S / (n : ℝ)) ^ 2 * (A2shift n s * phiShiftA n)
            * (∑ i, v i * v i) := by
          rw [hσ]
          field_simp
          try ring
      _ ≤ 2 * (1 - p) * (scalAlg S / (n : ℝ)) ^ 2
            * ((2 * s - 1) + (n : ℝ) * (4 / ((n : ℝ) - 2 + 8 * s)) ^ 2
              / (4 * (1 + 2 * ((n : ℝ) - 1) * s))) * (∑ i, v i * v i) := by
          have hstep : 2 * (1 - p) * (scalAlg S / (n : ℝ)) ^ 2 * (A2shift n s * phiShiftA n)
              ≤ 2 * (1 - p) * (scalAlg S / (n : ℝ)) ^ 2
                * ((2 * s - 1) + (n : ℝ) * (4 / ((n : ℝ) - 2 + 8 * s)) ^ 2
                  / (4 * (1 + 2 * ((n : ℝ) - 1) * s))) :=
            mul_le_mul_of_nonneg_left hS1 hfacn
          calc 2 * (1 - p) * (scalAlg S / (n : ℝ)) ^ 2 * (A2shift n s * phiShiftA n)
                * (∑ i, v i * v i)
              ≤ (2 * (1 - p) * (scalAlg S / (n : ℝ)) ^ 2
                  * ((2 * s - 1) + (n : ℝ) * (4 / ((n : ℝ) - 2 + 8 * s)) ^ 2
                    / (4 * (1 + 2 * ((n : ℝ) - 1) * s)))) * (∑ i, v i * v i) :=
                mul_le_mul_of_nonneg_right hstep hsv
            _ = 2 * (1 - p) * (scalAlg S / (n : ℝ)) ^ 2
                  * ((2 * s - 1) + (n : ℝ) * (4 / ((n : ℝ) - 2 + 8 * s)) ^ 2
                    / (4 * (1 + 2 * ((n : ℝ) - 1) * s))) * (∑ i, v i * v i) := rfl
      _ ≤ _ := by rw [he, hp]; exact hric
  have hMle := ricMarg_shiftM_le n hn (a := s) (b := 1 / 2) (p := p) (σ := scalAlg S)
    (by linarith) (by norm_num) (by norm_num) hp1 hpm1 hσpos hSl hSR rfl hA2eq v
  have hW : chatLinv n s (Q (ell s (1 / 2) S - ĉ • Iso n))
      = shiftW0 n s (1 / 2) S + (ĉ ^ 2 * shiftMu n (A2shift n s)) • Iso n
        - (2 * ĉ) • shiftM n s (1 / 2) S := by
    have h := chatLinv_shift_expand (ĉ := ĉ) n hn2 hs (ell_isAlgCurv n s (1 / 2) hSl)
    rw [ha, hb] at h
    simpa only [shiftW0, shiftM, shiftMu, A2shift] using h
  rw [hW]
  have hlin : ricMarg (shiftW0 n s (1 / 2) S + (ĉ ^ 2 * shiftMu n (A2shift n s)) • Iso n
        - (2 * ĉ) • shiftM n s (1 / 2) S) p v
      = ricMarg (shiftW0 n s (1 / 2) S) p v
        + (ĉ ^ 2 * shiftMu n (A2shift n s)) * ricMarg (Iso n) p v
        - (2 * ĉ) * ricMarg (shiftM n s (1 / 2) S) p v := by
    rw [ricMarg_sub, ricMarg_add, ricMarg_smul, ricMarg_smul]
  rw [hlin]
  have hIso_nn : 0 ≤ ricMarg (Iso n) p v := by
    rw [ricMarg_Iso hn2]
    have h1 : 0 ≤ 1 - p := h1mp.le
    have h2 : 0 ≤ (n : ℝ) - 1 := by linarith
    exact mul_nonneg (mul_nonneg h2 h1) hsv
  have hμ : 0 ≤ (ĉ ^ 2 * shiftMu n (A2shift n s)) * ricMarg (Iso n) p v := by
    apply mul_nonneg _ hIso_nn
    apply mul_nonneg (sq_nonneg _)
    rw [shiftMu]
    positivity
  have hkey : 2 * ĉ * (cssKP n * (1 - p) / A2shift n s * (∑ i, v i * v i))
      < 2 * (1 - p) * phiShiftA n / ((n : ℝ) ^ 2 * A2shift n s) * (∑ i, v i * v i) := by
    have hcssKPpos : 0 < cssKP n := cssKP_pos hn2
    have hnum : 2 * ĉ * cssKP n < 2 * phiShiftA n / (n : ℝ) ^ 2 := by
      have h1 : ĉ * cssKP n ≤ cShiftA1 n * cssKP n :=
        mul_le_mul_of_nonneg_right hĉle hcssKPpos.le
      have h2 : cShiftA1 n * cssKP n = phiShiftA n / (2 * (n : ℝ) ^ 2) := by
        rw [cShiftA1]
        field_simp
        try ring
      have h4 : 2 * (ĉ * cssKP n) ≤ 2 * (phiShiftA n / (2 * (n : ℝ) ^ 2)) :=
        by linarith [h1, h2.le, h2.ge]
      have hB : 2 * (phiShiftA n / (2 * (n : ℝ) ^ 2)) = phiShiftA n / (n : ℝ) ^ 2 := by ring
      rw [hB] at h4
      have h5 : phiShiftA n / (n : ℝ) ^ 2 < 2 * phiShiftA n / (n : ℝ) ^ 2 := by
        have he : 2 * phiShiftA n / (n : ℝ) ^ 2 = 2 * (phiShiftA n / (n : ℝ) ^ 2) := by ring
        rw [he]
        linarith [div_pos (phiShiftA_pos hn) (by positivity : (0 : ℝ) < (n : ℝ) ^ 2)]
      linarith [h4, h5]
    have hfac : 0 < (1 - p) / A2shift n s * (∑ i, v i * v i) :=
      mul_pos (div_pos h1mp hA2pos) hSvpos
    have he1 : 2 * ĉ * (cssKP n * (1 - p) / A2shift n s * (∑ i, v i * v i))
        = (2 * ĉ * cssKP n) * ((1 - p) / A2shift n s * (∑ i, v i * v i)) := by ring
    have he2 : 2 * (1 - p) * phiShiftA n / ((n : ℝ) ^ 2 * A2shift n s) * (∑ i, v i * v i)
        = (2 * phiShiftA n / (n : ℝ) ^ 2) * ((1 - p) / A2shift n s * (∑ i, v i * v i)) := by
      field_simp
      try ring
    rw [he1, he2]
    exact mul_lt_mul_of_pos_right hnum hfac
  have hMstep : (2 * ĉ) * ricMarg (shiftM n s (1 / 2) S) p v
      ≤ (2 * ĉ) * (cssKP n * (1 - p) / A2shift n s * (∑ i, v i * v i)) :=
    mul_le_mul_of_nonneg_left (le_trans (le_abs_self _) hMle) (by linarith)
  have hfin : (2 * ĉ) * ricMarg (shiftM n s (1 / 2) S) p v
      < 2 * (1 - p) * phiShiftA n / ((n : ℝ) ^ 2 * A2shift n s) * (∑ i, v i * v i) :=
    lt_of_le_of_lt hMstep hkey
  have hchain : (2 * ĉ) * ricMarg (shiftM n s (1 / 2) S) p v
      < ricMarg (shiftW0 n s (1 / 2) S) p v := lt_of_lt_of_le hfin hmargin
  linarith [hchain, hμ]



end Work.Diff.Alg.Pinch
