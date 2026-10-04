import Mathlib
import Submission.Work.Diff.Alg.Pinch.ChatShiftAux
import Submission.Work.Diff.Alg.Pinch.ric_margin_b
import Submission.Work.Diff.Alg.Pinch.bwCr_lower_window

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Branch `0 < s ≤ 1/2`, Ricci form: uniform shifted strictness

`chat_shift_ric_b` is the first of the four branch lemmas of
`Work.Diff.Alg.Pinch.chat_shift_strict`: for `0 < s ≤ 1/2`, a point `S ∈ Dpic (ccP n s)` whose
image `X = ell (ccA n s) s S` has `scalAlg X = 1`, and a *tight* direction `v` of the Ricci
pinching of `S`, the shifted reaction direction
`chatLinv n s (Q (X - ĉ • Iso n)) = W₀ + ĉ² (2(n-1)/A₂) • Iso n - 2ĉ • M` improves the Ricci form
for every `ĉ ≤ cShiftB n cρ`, where `cρ` is the uniform lower bound for `RFAux.bwCρ n ·` on the
window `[ε, 1/2]` (`bwCr_lower_window`).

The proof combines `ric_margin_b` (the quantitative Böhm–Wilking strictness, giving the margin
`cρ · |Ric₀ S|² · |v|² ≥ cρ (1-ccP)² (σ/n)² |v|²`) with `ricMarg_shiftM_le` (the perturbation
bound `|ricMarg M p v| ≤ K_P (1-p)/A₂ |v|²`) and `ricMarg_Iso`; the arithmetic is the explicit
comparison of `cρ (4/(n+2))² / n⁴` with `K_P` at `ĉ = cShiftB n cρ`.
-/

namespace Work.Diff.Alg.Pinch

open Finset Submission.Diff.Alg

variable {n : ℕ}

set_option maxHeartbeats 1000000 in
/-- **Branch `0 < s ≤ 1/2`, Ricci form.** -/
theorem chat_shift_ric_b (n : ℕ) (hn : 3 ≤ n) {ε cρ s ĉ : ℝ} (hε : 0 < ε) (hcρ : 0 < cρ)
    (hcρb : ∀ b : ℝ, ε ≤ b → b ≤ 1 / 2 → cρ ≤ RFAux.bwCρ n b)
    (hsε : ε ≤ s) (hs : 0 < s) (hs1 : s ≤ 1 / 2) (hĉ0 : 0 < ĉ)
    (hĉle : ĉ ≤ cShiftB n cρ) {S : Curv4 n} (hSl : IsAlgCurv S) (hS0 : S ≠ 0)
    (hSP : InPIC2 S) (hSR : RicPinch (ccP n s) S)
    (hscal : scalAlg (ell (ccA n s) s S) = 1) :
    ∀ v : Fin n → ℝ, v ≠ 0 → ricMarg S (ccP n s) v = 0 →
      0 < ricMarg (chatLinv n s (Q (ell (ccA n s) s S - ĉ • Iso n))) (ccP n s) v := by
  intro v hv htight
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
  have hccP1 : ccP n s ≤ 1 := (ccP_lt_one (by omega) hs hs1).le
  have hccPnn : (0 : ℝ) ≤ ccP n s := ccP_nn (n := n) hn2 (b := s)
  have h1mp : 0 < 1 - ccP n s := by
    have := ccP_lt_one (n := n) (by omega) hs hs1
    linarith
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
  have ht' : (ccP n s * scalAlg S / (n : ℝ)) * (∑ i, v i * v i)
      = ∑ i, ∑ j, ric S i j * v i * v j := by
    rw [ricMarg_eq] at htight
    linarith
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
  have hmargin : cρ * (4 / ((n : ℝ) + 2)) ^ 2 * (1 / (n : ℝ) ^ 4) * (∑ i, v i * v i)
      ≤ ricMarg (shiftW0 n (ccA n s) s S) (ccP n s) v := by
    have hric := ric_margin_b n hn2 hs hs1 hSl hS0 hSP hSR hv ht'
    have hw0 : ricMarg (shiftW0 n (ccA n s) s S) (ccP n s) v
        = (∑ i, ∑ j, ric (linv (ccA n s) s (Q (ell (ccA n s) s S))) i j * v i * v j)
          - (ccP n s * scalAlg (linv (ccA n s) s (Q (ell (ccA n s) s S))) / (n : ℝ))
            * (∑ i, v i * v i) := by
      rw [shiftW0, ricMarg_eq]
    rw [hw0]
    have hρ : 0 ≤ ric0Frob2 S := by
      rw [ric0Frob2]
      exact Finset.sum_nonneg (fun i _ => Finset.sum_nonneg (fun j _ => mul_self_nonneg _))
    have hbw := hcρb s hsε hs1
    have h6 : cρ * ric0Frob2 S * (∑ i, v i * v i)
        ≤ RFAux.bwCρ n s * ric0Frob2 S * (∑ i, v i * v i) := by
      apply mul_le_mul_of_nonneg_right _ hsv
      exact mul_le_mul_of_nonneg_right hbw hρ
    have hlow := ric0Frob2_tight_lower n (ccP_lt_one (by omega) hs hs1) hSl hSR hv ht'
    have hσ1 : 1 / (n : ℝ) ^ 2 ≤ scalAlg S / (n : ℝ) := by
      have he : scalAlg S / (n : ℝ) = 1 / (A2shift n (ccA n s) * (n : ℝ)) := by
        rw [hσ, div_div]
      rw [he]
      rw [div_le_div_iff₀ (by positivity : (0 : ℝ) < (n : ℝ) ^ 2) (mul_pos hA2pos hn0R)]
      simpa only [one_mul, pow_two] using mul_le_mul_of_nonneg_right hA2le hn0R.le
    have h2 : (4 / ((n : ℝ) + 2)) ^ 2 ≤ (1 - ccP n s) ^ 2 := by
      have h1 := one_sub_ccP_ge n hn2 hs hs1
      exact pow_le_pow_left₀ (by positivity) h1 2
    have h3 : 1 / (n : ℝ) ^ 4 ≤ (scalAlg S / (n : ℝ)) ^ 2 := by
      have h4 : 1 / (n : ℝ) ^ 4 = (1 / (n : ℝ) ^ 2) ^ 2 := by ring
      rw [h4]
      exact pow_le_pow_left₀ (by positivity) hσ1 2
    have h5 : 0 ≤ (1 - ccP n s) ^ 2 := sq_nonneg _
    calc cρ * (4 / ((n : ℝ) + 2)) ^ 2 * (1 / (n : ℝ) ^ 4) * (∑ i, v i * v i)
        = cρ * ((4 / ((n : ℝ) + 2)) ^ 2 * (1 / (n : ℝ) ^ 4)) * (∑ i, v i * v i) := by ring
      _ ≤ cρ * ((1 - ccP n s) ^ 2 * (scalAlg S / (n : ℝ)) ^ 2) * (∑ i, v i * v i) := by
          apply mul_le_mul_of_nonneg_right _ hsv
          apply mul_le_mul_of_nonneg_left _ hcρ.le
          exact mul_le_mul h2 h3 (by positivity) h5
      _ ≤ cρ * ric0Frob2 S * (∑ i, v i * v i) := by
          have h8 := mul_le_mul_of_nonneg_left hlow hcρ.le
          calc cρ * ((1 - ccP n s) ^ 2 * (scalAlg S / (n : ℝ)) ^ 2) * (∑ i, v i * v i)
              = (cρ * ((1 - ccP n s) ^ 2 * (scalAlg S / (n : ℝ)) ^ 2)) * (∑ i, v i * v i) := rfl
            _ ≤ (cρ * ric0Frob2 S) * (∑ i, v i * v i) := mul_le_mul_of_nonneg_right h8 hsv
            _ = cρ * ric0Frob2 S * (∑ i, v i * v i) := rfl
      _ ≤ _ := le_trans h6 hric
  have hMle := ricMarg_shiftM_le n hn (a := ccA n s) (b := s) (p := ccP n s) (σ := scalAlg S)
    hccApp (le_of_lt hs) hs1 hccP1 hccPm1 hσpos hSl hSR rfl hA2eq v
  have hW : chatLinv n s (Q (ell (ccA n s) s S - ĉ • Iso n))
      = shiftW0 n (ccA n s) s S + (ĉ ^ 2 * shiftMu n (A2shift n (ccA n s))) • Iso n
        - (2 * ĉ) • shiftM n (ccA n s) s S := by
    have h := chatLinv_shift_expand (ĉ := ĉ) n hn2 hs (ell_isAlgCurv n (ccA n s) s hSl)
    rw [ha, hb] at h
    simpa only [shiftW0, shiftM, shiftMu, A2shift] using h
  rw [hW]
  have hlin : ricMarg (shiftW0 n (ccA n s) s S
        + (ĉ ^ 2 * shiftMu n (A2shift n (ccA n s))) • Iso n
        - (2 * ĉ) • shiftM n (ccA n s) s S) (ccP n s) v
      = ricMarg (shiftW0 n (ccA n s) s S) (ccP n s) v
        + (ĉ ^ 2 * shiftMu n (A2shift n (ccA n s))) * ricMarg (Iso n) (ccP n s) v
        - (2 * ĉ) * ricMarg (shiftM n (ccA n s) s S) (ccP n s) v := by
    rw [ricMarg_sub, ricMarg_add, ricMarg_smul, ricMarg_smul]
  rw [hlin]
  have hIso_nn : 0 ≤ ricMarg (Iso n) (ccP n s) v := by
    rw [ricMarg_Iso hn2]
    have h1 : 0 ≤ 1 - ccP n s := by linarith
    have h2 : 0 ≤ (n : ℝ) - 1 := by linarith
    exact mul_nonneg (mul_nonneg h2 h1) hsv
  have hμ : 0 ≤ (ĉ ^ 2 * shiftMu n (A2shift n (ccA n s))) * ricMarg (Iso n) (ccP n s) v := by
    apply mul_nonneg _ hIso_nn
    apply mul_nonneg (sq_nonneg _)
    rw [shiftMu]
    positivity
  have hkey : 2 * ĉ * (cssKP n * (1 - ccP n s) / A2shift n (ccA n s) * (∑ i, v i * v i))
      < cρ * (4 / ((n : ℝ) + 2)) ^ 2 * (1 / (n : ℝ) ^ 4) * (∑ i, v i * v i) := by
    have hcssKPpos : 0 < cssKP n := cssKP_pos hn2
    have hfac : (1 - ccP n s) / A2shift n (ccA n s) ≤ 1 := by
      have hA2one : (1 : ℝ) ≤ A2shift n (ccA n s) := by rw [A2shift]; nlinarith
      rw [div_le_one hA2pos]
      linarith [hA2one, hccPnn]
    have hmono : cssKP n * (1 - ccP n s) / A2shift n (ccA n s) * (∑ i, v i * v i)
        ≤ cssKP n * (∑ i, v i * v i) := by
      calc cssKP n * (1 - ccP n s) / A2shift n (ccA n s) * (∑ i, v i * v i)
          = cssKP n * ((1 - ccP n s) / A2shift n (ccA n s)) * (∑ i, v i * v i) := by ring
        _ ≤ cssKP n * 1 * (∑ i, v i * v i) := by
            apply mul_le_mul_of_nonneg_right _ hsv
            exact mul_le_mul_of_nonneg_left hfac hcssKPpos.le
        _ = cssKP n * (∑ i, v i * v i) := by ring
    have hnum : 2 * ĉ * cssKP n < cρ * (4 / ((n : ℝ) + 2)) ^ 2 * (1 / (n : ℝ) ^ 4) := by
      have he : cρ * (4 / ((n : ℝ) + 2)) ^ 2 * (1 / (n : ℝ) ^ 4)
          = 16 * cρ / (((n : ℝ) + 2) ^ 2 * (n : ℝ) ^ 4) := by
        field_simp
        try ring
      rw [he]
      have h1 : ĉ * cssKP n ≤ cShiftB n cρ * cssKP n :=
        mul_le_mul_of_nonneg_right hĉle hcssKPpos.le
      have h2 : cShiftB n cρ * cssKP n = 4 * cρ / (((n : ℝ) + 2) ^ 2 * (n : ℝ) ^ 4) := by
        rw [cShiftB]
        field_simp
        try ring
      have hpos : (0 : ℝ) < cρ / (((n : ℝ) + 2) ^ 2 * (n : ℝ) ^ 4) :=
        div_pos hcρ (by positivity)
      have hA : 2 * ĉ * cssKP n ≤ 2 * (cShiftB n cρ * cssKP n) := by linarith
      have hB : 2 * (cShiftB n cρ * cssKP n) = 8 * (cρ / (((n : ℝ) + 2) ^ 2 * (n : ℝ) ^ 4)) := by
        rw [h2]; ring
      have hC : (8 : ℝ) * (cρ / (((n : ℝ) + 2) ^ 2 * (n : ℝ) ^ 4))
          < 16 * (cρ / (((n : ℝ) + 2) ^ 2 * (n : ℝ) ^ 4)) := by linarith
      have hD : (16 : ℝ) * (cρ / (((n : ℝ) + 2) ^ 2 * (n : ℝ) ^ 4))
          = 16 * cρ / (((n : ℝ) + 2) ^ 2 * (n : ℝ) ^ 4) := by ring
      linarith [hA, hB.le, hB.ge, hC, hD.le, hD.ge]
    calc 2 * ĉ * (cssKP n * (1 - ccP n s) / A2shift n (ccA n s) * (∑ i, v i * v i))
        = (2 * ĉ) * (cssKP n * (1 - ccP n s) / A2shift n (ccA n s) * (∑ i, v i * v i)) := rfl
      _ ≤ (2 * ĉ) * (cssKP n * (∑ i, v i * v i)) := mul_le_mul_of_nonneg_left hmono (by linarith)
      _ = (2 * ĉ * cssKP n) * (∑ i, v i * v i) := by ring
      _ < (cρ * (4 / ((n : ℝ) + 2)) ^ 2 * (1 / (n : ℝ) ^ 4)) * (∑ i, v i * v i) :=
          mul_lt_mul_of_pos_right hnum hSvpos
      _ = cρ * (4 / ((n : ℝ) + 2)) ^ 2 * (1 / (n : ℝ) ^ 4) * (∑ i, v i * v i) := rfl
  have hMstep : (2 * ĉ) * ricMarg (shiftM n (ccA n s) s S) (ccP n s) v
      ≤ (2 * ĉ) * (cssKP n * (1 - ccP n s) / A2shift n (ccA n s) * (∑ i, v i * v i)) :=
    mul_le_mul_of_nonneg_left (le_trans (le_abs_self _) hMle) (by linarith)
  nlinarith [hmargin, hMstep, hμ, hkey]



end Work.Diff.Alg.Pinch
