import Mathlib
import Submission.Work.Diff.Alg.Pinch.Chat_margin
import Submission.Work.Diff.Alg.Pinch.Chat_shift_base
import Submission.Work.Diff.Alg.Pinch.RoomAux.Strict
import Submission.Work.Diff.Alg.Pinch.chat_shift_strict
import Submission.Work.Diff.Alg.Pinch.inPIC2_room
import Submission.Work.Diff.Alg.Pinch.ricPinch_room

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The global room lemma for the Brendle–Schoen family of cones

`Work.Diff.Alg.Pinch.Chat_room_global`, deduced from three helper statements (the uniform shifted
strictness and the two one-step room lemmas); see the docstrings of the individual statements.

The argument below is the *scaling* step: a configuration `(R, c)` with `R + c • Iso n ∈ Ĉ(s)` is
rescaled to the normalized slice `scalAlg X = 1`, where the two room lemmas apply to the preimage
point `S = chatLinv n s X'` and the direction `chatLinv n s (Q (X' - ĉ • Iso n))`; then the
conclusion is scaled back.
-/

namespace Work.Diff.Alg.Pinch

open Finset Submission.Diff.Alg

variable {n : ℕ}

/-- The assembly: the target follows from the shifted strictness and the two room lemmas. -/
lemma Chat_room_global_of_children (n : ℕ) (hn : 2 ≤ n)
    (hcrux : ∀ ε : ℝ, 0 < ε → ∃ ĉ₀ : ℝ, 0 < ĉ₀ ∧ ∀ s : ℝ, ε ≤ s →
      ∀ X : Curv4 n, X ∈ Chat n s → scalAlg X = 1 →
      ∀ ĉ : ℝ, 0 < ĉ → ĉ ≤ ĉ₀ → ShiftStrict n s ĉ X)
    (hroomP : ∀ {S W : Curv4 n}, IsAlgCurv S → IsAlgCurv W → InPIC2 S →
      (∀ x y z w : Fin n → ℝ, Q2P.EFun S x y z w = 0 →
        Q2P.EFun (Iso n) x y z w ≠ 0 → 0 < Q2P.EFun W x y z w) →
      ∃ ε : ℝ, 0 < ε ∧ ∃ ρ : ℝ, 0 < ρ ∧ ∀ τ : ℝ, 0 < τ → τ ≤ ε →
        ∀ Y : Curv4 n, IsAlgCurv Y → ‖Y‖ ≤ ρ → InPIC2 (S + τ • (W + Y)))
    (hroomR : ∀ {p : ℝ} {S W : Curv4 n}, p < 1 → IsAlgCurv S → IsAlgCurv W → RicPinch p S →
      (∀ v : Fin n → ℝ, v ≠ 0 →
        (p * scalAlg S / (n : ℝ)) * (∑ i, v i * v i) = ∑ i, ∑ j, ric S i j * v i * v j →
        (p * scalAlg W / (n : ℝ)) * (∑ i, v i * v i)
          < ∑ i, ∑ j, ric W i j * v i * v j) →
      ∃ ε : ℝ, 0 < ε ∧ ∃ ρ : ℝ, 0 < ρ ∧ ∀ τ : ℝ, 0 < τ → τ ≤ ε →
        ∀ Y : Curv4 n, IsAlgCurv Y → ‖Y‖ ≤ ρ → RicPinch p (S + τ • (W + Y))) :
    ∀ ε : ℝ, 0 < ε → ∃ K : ℝ, 0 < K ∧ ∀ s : ℝ, ε ≤ s →
      ∀ R : Curv4 n, ∀ c : ℝ, 0 < c →
        R + c • Iso n ∈ Chat n s → K * c ≤ scalAlg R →
        ∃ h : ℝ, 0 < h ∧ ∃ ρ : ℝ, 0 < ρ ∧ ∀ t : ℝ, 0 < t → t ≤ h →
          ∀ v : Curv4 n, IsAlgCurv v → ‖v - Q R‖ ≤ ρ →
            R + t • v + c • Iso n ∈ Chat n s := by
  intro ε hε
  obtain ⟨ĉ₀, hĉ₀pos, hcrux'⟩ := hcrux ε hε
  refine ⟨1 / ĉ₀, by positivity, ?_⟩
  intro s hs R c hc hmem hKc
  have hn' : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < (n : ℝ) := by linarith
  have hs0 : 0 < s := lt_of_lt_of_le hε hs
  have hnn : 0 ≤ (n : ℝ) * ((n : ℝ) - 1) := by nlinarith
  set X : Curv4 n := R + c • Iso n with hX
  have hXmem : X ∈ Chat n s := hmem
  have hRalg : IsAlgCurv R := by
    have hXI : IsAlgCurv X := chat_isAlgCurv n hn hs0 hXmem
    have h2 : R = X - c • Iso n := by rw [hX]; abel
    rw [h2]
    exact isAlgCurv_sub hXI (isAlgCurv_smul c (Iso_algCurv n))
  have hμeq : scalAlg X = scalAlg R + c * ((n : ℝ) * ((n : ℝ) - 1)) := by
    rw [hX, scalAlg_add_linv, scalAlg_smul_linv, scalAlg_iso]
  have hμpos : 0 < scalAlg X := by
    have hKpos : 0 < 1 / ĉ₀ := by positivity
    have h2 : c * (1 / ĉ₀) ≤ scalAlg R := by rw [mul_comm]; exact hKc
    nlinarith [h2, hμeq, hc, hnn]
  set μ : ℝ := scalAlg X with hμ
  have hμpos' : 0 < μ := hμpos
  set X' : Curv4 n := μ⁻¹ • X with hX'
  set ĉ : ℝ := c * μ⁻¹ with hĉ
  have hX'mem : X' ∈ Chat n s := chat_smul_mem n hn (by positivity) hXmem
  have hX'scal : scalAlg X' = 1 := by
    rw [hX', scalAlg_smul_linv, hμ, inv_mul_cancel₀ hμpos'.ne']
  have hĉpos : 0 < ĉ := by rw [hĉ]; exact mul_pos hc (inv_pos.mpr hμpos')
  have hĉle : ĉ ≤ ĉ₀ := by
    have hscalR : scalAlg R = μ - c * ((n : ℝ) * ((n : ℝ) - 1)) := by
      have h1 : μ = scalAlg R + c * ((n : ℝ) * ((n : ℝ) - 1)) := by rw [hμ]; exact hμeq
      linarith
    have h2 : c * (1 / ĉ₀) ≤ μ - c * ((n : ℝ) * ((n : ℝ) - 1)) := by
      rw [← hscalR, mul_comm]; exact hKc
    have hden : 0 < 1 / ĉ₀ + (n : ℝ) * ((n : ℝ) - 1) := by
      have : 0 < 1 / ĉ₀ := by positivity
      linarith
    have h3 : c * (1 / ĉ₀ + (n : ℝ) * ((n : ℝ) - 1)) ≤ μ := by
      have h3' : c * (1 / ĉ₀) + c * ((n : ℝ) * ((n : ℝ) - 1)) ≤ μ := by linarith [h2]
      calc c * (1 / ĉ₀ + (n : ℝ) * ((n : ℝ) - 1))
          = c * (1 / ĉ₀) + c * ((n : ℝ) * ((n : ℝ) - 1)) := by ring
        _ ≤ μ := h3'
    have h5 : c / μ ≤ 1 / (1 / ĉ₀ + (n : ℝ) * ((n : ℝ) - 1)) := by
      rw [div_le_div_iff₀ hμpos' hden]
      linarith [h3]
    have h6 : 1 / (1 / ĉ₀ + (n : ℝ) * ((n : ℝ) - 1)) ≤ ĉ₀ := by
      rw [div_le_iff₀ hden]
      have h6' : ĉ₀ * (1 / ĉ₀ + (n : ℝ) * ((n : ℝ) - 1))
          = 1 + ĉ₀ * ((n : ℝ) * ((n : ℝ) - 1)) := by
        field_simp
      nlinarith [hĉ₀pos, hnn]
    rw [hĉ, ← div_eq_mul_inv]
    linarith [h5, h6]
  -- ## the `Dpic` preimage
  obtain ⟨S, hSdpic, hXS⟩ : ∃ S : Curv4 n, S ∈ Dpic (n := n) (chatPP n s) ∧
      ell (chatAA n s) (chatBB s) S = X' := by
    rw [chat_eq_Ccone_param] at hX'mem
    exact hX'mem
  have hSalg : IsAlgCurv S := hSdpic.1
  have hSP : InPIC2 S := hSdpic.2.1
  have hSric : RicPinch (chatPP n s) S := hSdpic.2.2
  have hpp_lt : chatPP n s < 1 := chatPP_lt_one n hn hs0
  -- ## the shifted strictness (the crux)
  have hstrict := hcrux' s hs X' hX'mem hX'scal ĉ hĉpos hĉle
  -- ## identify the preimage
  have hdenA : 1 + 2 * ((n : ℝ) - 1) * chatAA n s ≠ 0 := chatAA_denom n hn hs0.le
  have hdenB : 1 + ((n : ℝ) - 2) * chatBB s ≠ 0 := chatBB_denom n hn hs0.le
  have hlinv_X : chatLinv n s X' = S := by
    rw [chatLinv_eq_linv n hn hs0.le, ← hXS]
    exact linv_ell n (by positivity) hdenA hdenB hSalg
  have hQA : IsAlgCurv (Q (X' - ĉ • Iso n)) :=
    Q_isAlgCurv n (isAlgCurv_sub (chat_isAlgCurv n hn hs0 hX'mem) (isAlgCurv_smul ĉ (Iso_algCurv n)))
  set W : Curv4 n := linv (chatAA n s) (chatBB s) (Q (X' - ĉ • Iso n)) with hW
  have hWalg : IsAlgCurv W := by rw [hW]; exact cm_linv_isAlgCurv hQA
  have hchatW : chatLinv n s (Q (X' - ĉ • Iso n)) = W := by
    rw [chatLinv_eq_linv n hn hs0.le, hW]
  -- ## the two rooms
  obtain ⟨ε₁, hε₁pos, ρ₁, hρ₁pos, hroom₁⟩ :=
    hroomP hSalg hWalg hSP (fun x y z w h0 hne => by
      rw [← hlinv_X] at h0
      have h := hstrict.2 x y z w h0 hne
      rw [hchatW] at h
      exact h)
  obtain ⟨ε₂, hε₂pos, ρ₂, hρ₂pos, hroom₂⟩ :=
    hroomR hpp_lt hSalg hWalg hSric (fun v hv h0 => by
      rw [← hlinv_X] at h0
      have h := hstrict.1 v hv h0
      rw [hchatW] at h
      exact h)
  obtain ⟨M, hMpos, hM⟩ := cm_linv_bound (n := n) (chatAA n s) (chatBB s)
  -- ## conclude
  refine ⟨min ε₁ ε₂ / μ, by positivity, min ρ₁ ρ₂ * μ ^ 2 / M, by positivity, ?_⟩
  intro t htpos hth v hvalg hvρ
  set τ : ℝ := t * μ with hτ
  set Y : Curv4 n := linv (chatAA n s) (chatBB s) (μ⁻¹ • (μ⁻¹ • (v - Q R))) with hY
  have hQRalg : IsAlgCurv (Q R) := Q_isAlgCurv n hRalg
  have hYalg : IsAlgCurv Y := cm_linv_isAlgCurv (isAlgCurv_smul _ (isAlgCurv_smul _
    (isAlgCurv_sub hvalg hQRalg)))
  have hτpos : 0 < τ := by rw [hτ]; exact mul_pos htpos hμpos'
  have hτle : τ ≤ min ε₁ ε₂ := by
    have h2 : t * μ ≤ min ε₁ ε₂ := by
      rw [le_div_iff₀ hμpos'] at hth; linarith [hth]
    rw [hτ]; linarith
  have hYρ : ‖Y‖ ≤ min ρ₁ ρ₂ := by
    have h1 : ‖μ⁻¹ • (μ⁻¹ • (v - Q R))‖ = μ⁻¹ * (μ⁻¹ * ‖v - Q R‖) := by
      rw [norm_smul, norm_smul, Real.norm_of_nonneg (by positivity : (0:ℝ) ≤ μ⁻¹)]
    have h2 := hM (μ⁻¹ • (μ⁻¹ • (v - Q R)))
    rw [hY]
    have h4 : μ⁻¹ * (μ⁻¹ * ‖v - Q R‖) ≤ μ⁻¹ * (μ⁻¹ * (min ρ₁ ρ₂ * μ ^ 2 / M)) := by
      have h3 : ‖v - Q R‖ ≤ min ρ₁ ρ₂ * μ ^ 2 / M := hvρ
      have h5 : μ⁻¹ * ‖v - Q R‖ ≤ μ⁻¹ * (min ρ₁ ρ₂ * μ ^ 2 / M) :=
        mul_le_mul_of_nonneg_left h3 (by positivity)
      exact mul_le_mul_of_nonneg_left h5 (by positivity)
    have h6 : μ⁻¹ * (μ⁻¹ * (min ρ₁ ρ₂ * μ ^ 2 / M)) = min ρ₁ ρ₂ / M := by
      field_simp
      try ring
    rw [h1] at h2
    have h7 : M * (min ρ₁ ρ₂ / M) = min ρ₁ ρ₂ := by
      field_simp
      try ring
    have h8 : M * (μ⁻¹ * (μ⁻¹ * ‖v - Q R‖)) ≤ M * (μ⁻¹ * (μ⁻¹ * (min ρ₁ ρ₂ * μ ^ 2 / M))) :=
      mul_le_mul_of_nonneg_left h4 hMpos.le
    rw [h6, h7] at h8
    linarith [h2, h8]
  have hmem₁ : InPIC2 (S + τ • (W + Y)) :=
    hroom₁ τ hτpos (le_trans hτle (min_le_left _ _)) Y hYalg (le_trans hYρ (min_le_left _ _))
  have hmem₂ : RicPinch (chatPP n s) (S + τ • (W + Y)) :=
    hroom₂ τ hτpos (le_trans hτle (min_le_right _ _)) Y hYalg (le_trans hYρ (min_le_right _ _))
  have hmemD : S + τ • (W + Y) ∈ Dpic (n := n) (chatPP n s) :=
    ⟨isAlgCurv_add hSalg (isAlgCurv_smul _ (isAlgCurv_add hWalg hYalg)), hmem₁, hmem₂⟩
  -- ## the `ell`-image
  have hell1 : ell (chatAA n s) (chatBB s) (S + τ • (W + Y))
      = X' + τ • (Q (X' - ĉ • Iso n) + μ⁻¹ • (μ⁻¹ • (v - Q R))) := by
    rw [ell_add (chatAA n s) (chatBB s) S (τ • (W + Y)), ell_smul (chatAA n s) (chatBB s) τ (W + Y),
      ell_add (chatAA n s) (chatBB s) W Y]
    have h1 : ell (chatAA n s) (chatBB s) S = X' := hXS
    have h2 : ell (chatAA n s) (chatBB s) W = Q (X' - ĉ • Iso n) := by
      rw [hW]; exact ell_linv n hdenA hdenB hQA
    have h3 : ell (chatAA n s) (chatBB s) Y = μ⁻¹ • (μ⁻¹ • (v - Q R)) := by
      rw [hY]
      exact ell_linv n hdenA hdenB (isAlgCurv_smul _ (isAlgCurv_smul _
        (isAlgCurv_sub hvalg hQRalg)))
    rw [h1, h2, h3]
  have hmemX : X' + τ • (Q (X' - ĉ • Iso n) + μ⁻¹ • (μ⁻¹ • (v - Q R))) ∈ Chat n s := by
    rw [← hell1, chat_eq_Ccone_param]
    exact ⟨S + τ • (W + Y), hmemD, rfl⟩
  -- ## the direction simplifies
  have hshift : X' - ĉ • Iso n = μ⁻¹ • R := by
    rw [hX', hĉ, hX]
    simp only [smul_add, smul_smul]
    rw [mul_comm μ⁻¹ c, add_sub_cancel_right]
  have hdir : Q (X' - ĉ • Iso n) + μ⁻¹ • (μ⁻¹ • (v - Q R)) = μ⁻¹ • (μ⁻¹ • v) := by
    rw [hshift, csb_Q_smul]
    module
  rw [hdir] at hmemX
  -- ## scale back
  have hfinal : R + t • v + c • Iso n = μ • (X' + τ • (μ⁻¹ • (μ⁻¹ • v))) := by
    rw [hX', hτ]
    simp only [smul_add, smul_smul]
    have h1 : μ * (t * μ * (μ⁻¹ * μ⁻¹)) = t := by
      rw [show μ * (t * μ * (μ⁻¹ * μ⁻¹)) = t * (μ * μ⁻¹) * (μ * μ⁻¹) from by ring]
      rw [mul_inv_cancel₀ hμpos'.ne', mul_one, mul_one]
    rw [h1, mul_inv_cancel₀ hμpos'.ne', one_smul, hX]
    abel
  rw [hfinal]
  exact chat_smul_mem n hn hμpos'.le hmemX

/-! ## The target -/

theorem Chat_room_global (n : ℕ) (hn : 2 ≤ n) :
    ∀ ε : ℝ, 0 < ε → ∃ K : ℝ, 0 < K ∧ ∀ s : ℝ, ε ≤ s →
      ∀ R : Submission.Diff.Alg.Curv4 n, ∀ c : ℝ, 0 < c →
        R + c • Submission.Diff.Alg.Iso n ∈ Work.Diff.Alg.Pinch.Chat n s →
        K * c ≤ Submission.Diff.Alg.scalAlg R →
        ∃ h : ℝ, 0 < h ∧ ∃ ρ : ℝ, 0 < ρ ∧ ∀ t : ℝ, 0 < t → t ≤ h →
          ∀ v : Submission.Diff.Alg.Curv4 n, Submission.Diff.Alg.IsAlgCurv v →
            ‖v - Submission.Diff.Alg.Q R‖ ≤ ρ →
            R + t • v + c • Submission.Diff.Alg.Iso n ∈ Work.Diff.Alg.Pinch.Chat n s := by
  exact Chat_room_global_of_children n hn
    (fun ε hε => chat_shift_strict n hn ε hε)
    (fun {S W} hS hW hP hst => inPIC2_room n hS hW hP hst)
    (fun {p S W} hp hS hW hric hst => ricPinch_room n (by omega) hp hS hW hric hst)

end Work.Diff.Alg.Pinch
